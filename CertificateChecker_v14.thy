theory CertificateChecker_v14
imports Main HOL.Rat "HOL-Data_Structures.AVL_Map" 
"HOL-Library.Code_Target_Nat" "HOL-Library.Code_Target_Int"
"../verifiedTemporalValidator/Rat_Parsing"
begin

fun rat_of_digits_pair_sgn :: "bool \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> rat" where
"rat_of_digits_pair_sgn pos w f = (if pos then 1 else -1) * (rat_of_digits_pair (w, f))"


datatype calc_rule = 
  Pivot1 "nat" "nat" |
  Pivot2 "nat" "nat" |
  Update "nat" "rat" |
  PivotInBounds "nat" "nat" |
  UpdateInBounds "nat" "rat" |
  Success |
  Failure

(* For now, certificates only certify feasibility (not optimality) *)

type_synonym certificate = "calc_rule list"

(*
Variables are represented as indices from 0 to n - 1
*)

(* 
Configurations need to contain the following information:

B: set of basic variables
T: tableau/matrix
l: list of lower bounds
u: list of upper bounds
alpha: list of assigned values

Necessary data structures:
sets (implemented as a tree, e.g. AVL, red-black)
matrix (implemented using nested trees)
tuples
*)


(* Applies the given function f to every element of the tree *)
fun map_tree :: "('a::linorder * 'b) tree_ht \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 
('a * 'b) tree_ht" where
"map_tree Leaf f = Leaf" |
"map_tree (Node l ((a, b), h) r) f = 
(Node (map_tree l f) ((a, f b), h) (map_tree r f))"

fun unpack_tree :: "('a tree_ht) option \<Rightarrow> 'a tree_ht" where
"unpack_tree None = empty" |
"unpack_tree (Some t) = t"

fun unpack_rat :: "rat option \<Rightarrow> rat" where
"unpack_rat None = (0::rat)" |
"unpack_rat (Some r) = r"

type_synonym nat_set = "nat tree_ht"

(* Important note: When inserting/deleting with nat_set, always use fully qualified function
name (i.e. AVL_Set_Code.insert or AVL_Set_Code.delete) *)

(* Checks whether two nat_sets contain exactly the same elements (disregarding
tree structure). *)
fun nat_sets_equal :: "nat_set \<Rightarrow> nat_set \<Rightarrow> bool" where
"nat_sets_equal s1 s2 = ((inorder s1) = (inorder s2))"

(* Returns a set containing the elements 0, ..., n - 1 given n. *)
fun var_set_n :: "nat \<Rightarrow> nat_set" where
"var_set_n 0 = empty" |
"var_set_n (Suc n) = AVL_Set_Code.insert n (var_set_n n)"

(* Removes all elements of the second set from the first set. *)
fun nat_set_diff :: "nat_set \<Rightarrow> nat_set \<Rightarrow> nat_set" where
"nat_set_diff a Leaf = a" |
"nat_set_diff a (Node l (elt, h) r) =
nat_set_diff (AVL_Set_Code.delete elt (nat_set_diff a l)) r"



(* Matrix *)

type_synonym matrix_row = "((nat * rat) tree_ht)"

(* Adds fac * the first row to the second row and returns the result *)
fun add_mult_row :: "matrix_row \<Rightarrow> rat \<Rightarrow> matrix_row \<Rightarrow> matrix_row" where
"add_mult_row row fac Leaf = Leaf" |
"add_mult_row row fac (Node l ((j, val), h) r) = 
(Node (add_mult_row row fac l) 
((j, val + fac * (unpack_rat (lookup row j))), h) 
(add_mult_row row fac r))"


type_synonym matrix = "((nat * matrix_row) tree_ht)"

(* Alternative *)
(* type_synonym matrix = "((nat * ((nat * rat) tree_ht)) tree_ht)" *)

fun lookup_mat :: "matrix \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rat" where
"lookup_mat m i j = unpack_rat (lookup (unpack_tree (lookup m i)) j)"

(* Pivot operations *)

fun f_pivot_row :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
"f_pivot_row t_ij r = -(r / t_ij)"

(* Takes the contents of row i, i and j as input and returns the updated 
row, which is now row j *)
fun update_row_i :: "matrix_row \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> matrix_row" where
"update_row_i t i j = (let t_ij = unpack_rat (lookup t j) in 
(update i (1 / t_ij)
(map_tree (delete j t) (f_pivot_row t_ij))))"


(* Updates a non-pivot row with the row that was modified as part of the pivot (originally
row i, now row j) *)
fun update_other_row :: "matrix_row \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> matrix_row \<Rightarrow> matrix_row" where
"update_other_row new_row i j row =
(let fac = (unpack_rat (lookup row j)) in
(add_mult_row new_row fac (update i 0 (delete j row))))"

(* Updates the rest of the rows of the matrix *)
fun update_rows :: "matrix \<Rightarrow> matrix_row \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> matrix" where
"update_rows m new_row i j = map_tree m (update_other_row new_row i j)"

(*
Pivot steps:
- precompute new row
- delete old row
- update all new rows using map function
- insert new row
*)

fun pivot_mat :: "matrix \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> matrix" where
"pivot_mat m i j = (let new_row = (update_row_i (unpack_tree (lookup m i)) i j) in
(update j new_row
(update_rows (delete i m) new_row i j)))"

(* -------------------------------------------------------------- *)

(* Variable data *)

type_synonym rat_triple = "(rat * rat * rat)"

type_synonym var_data = "(nat * rat_triple) tree_ht"

fun update_assignment :: "rat_triple \<Rightarrow> rat \<Rightarrow> rat_triple" where
"update_assignment (a, b, c) delta = (a, b + delta, c)"

fun unpack_rat_triple :: "rat_triple option \<Rightarrow> rat_triple" where
"unpack_rat_triple None = (0, 0, 0)" |
"unpack_rat_triple (Some (a, b, c)) = (a, b, c)"

(* Takes the variable data, a variable index and the value by which to update as input *)
fun update_var :: "var_data \<Rightarrow> nat \<Rightarrow> rat \<Rightarrow> var_data" where
"update_var data j delta = 
update j (update_assignment (unpack_rat_triple (lookup data j)) delta) data"

fun update_basic_var :: "matrix \<Rightarrow> nat \<Rightarrow> var_data \<Rightarrow> nat \<Rightarrow> rat \<Rightarrow> var_data" where
"update_basic_var mat j vars i delta = 
update i (update_assignment (unpack_rat_triple (lookup vars i)) 
(delta * (lookup_mat mat i j))) 
vars"

fun update_basic_vars :: "nat_set \<Rightarrow> matrix \<Rightarrow> var_data \<Rightarrow> nat \<Rightarrow> rat \<Rightarrow> var_data" where
"update_basic_vars (Leaf) mat vars j delta = vars" |
"update_basic_vars (Node l (i, h) r) mat vars j delta = 
update_basic_vars r mat (update_basic_vars l mat 
(update_basic_var mat j vars i delta) j delta) j delta"




fun vars_in_bounds :: "var_data \<Rightarrow> bool" where
"vars_in_bounds Leaf = True" |
"vars_in_bounds (Node l ((j, l_j, alpha_j, r_j), h) r) = 
((l_j \<le> alpha_j) \<and> (alpha_j \<le> r_j) \<and>
(vars_in_bounds l) \<and> (vars_in_bounds r))"

(* Returns None if no variables are out of bounds, returns Some (i, t, b) if
variable i is out of bounds. t is the triple containing the lower bound, 
value and upper bound of the variable, and b indicates whether the lower bound is
violated (True) or the upper bound (False). *)
fun var_out_of_bounds :: "var_data \<Rightarrow> (nat * rat_triple * bool) option" where
"var_out_of_bounds Leaf = None" |
"var_out_of_bounds (Node l ((j, l_j, alpha_j, r_j), h) r) = 
(case (var_out_of_bounds l) of 
Some (i, t, b) \<Rightarrow> Some (i, t, b) |
None \<Rightarrow> (if \<not>(l_j \<le> alpha_j) then Some (j, (l_j, alpha_j, r_j), True) else 
(if \<not>(alpha_j \<le> r_j) then Some (j, (l_j, alpha_j, r_j), False) else
(var_out_of_bounds r))))"


(* Conversion functions *)

fun list_to_row :: "(nat * rat) list \<Rightarrow> matrix_row" where
"list_to_row Nil = empty" |
"list_to_row (Cons (n, r) tail) = (update n r (list_to_row tail))"

fun lists_to_mat :: "(nat * ((nat * rat) list)) list \<Rightarrow> matrix" where
"lists_to_mat Nil = empty" |
"lists_to_mat (Cons (n, lst) tail) = update n (list_to_row lst) (lists_to_mat tail)"

fun list_to_set :: "nat list \<Rightarrow> nat_set" where
"list_to_set Nil = empty" |
"list_to_set (Cons n tail) = AVL_Set_Code.insert n (list_to_set tail)"

fun list_to_var_data :: "(nat * rat_triple) list \<Rightarrow> var_data" where
"list_to_var_data Nil = empty" |
"list_to_var_data (Cons (n, triple) tail) = update n triple (list_to_var_data tail)"

(* -------------------------------------------------------------- *)


datatype configuration = Config "nat" "nat_set" "matrix" "var_data"
(*
Configuration contains number of vars, set of basic vars, tableau, var data
*)

(* Checks whether variable j is in slack+(x_i) *)
fun isin_slack_pos :: "matrix \<Rightarrow> var_data \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"isin_slack_pos mat vars i j = 
(let t_ij = (lookup_mat mat i j) in 
(case unpack_rat_triple (lookup vars j) of 
(l_j, alpha_j, u_j) \<Rightarrow> (t_ij > 0 \<and> alpha_j < u_j) \<or> (t_ij < 0 \<and> alpha_j > l_j)))"

(* Checks whether variable j is in slack-(x_i) *)
fun isin_slack_neg :: "matrix \<Rightarrow> var_data \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"isin_slack_neg mat vars i j = 
(let t_ij = (lookup_mat mat i j) in 
(case unpack_rat_triple (lookup vars j) of 
(l_j, alpha_j, u_j) \<Rightarrow> (t_ij < 0 \<and> alpha_j < u_j) \<or> (t_ij > 0 \<and> alpha_j > l_j)))"


(* Checks whether a non-basic variable/key exists in the given var_data tree with the 
property that applying the given function to the variable evaluates to true. *)
fun nb_var_exists_with :: "var_data \<Rightarrow> nat_set \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool" where
"nb_var_exists_with Leaf b_set f = False" |
"nb_var_exists_with (Node l ((j, l_j, alpha_j, u_j), h) r) b_set f = 
(if (\<not>(isin b_set j) \<and> (f j)) then True else
((nb_var_exists_with l b_set f) \<or> (nb_var_exists_with r b_set f)))"

(* Checks whether slack+(x_i) is empty *)
fun slack_pos_empty :: "configuration \<Rightarrow> nat \<Rightarrow> bool" where
"slack_pos_empty (Config n b_set mat vars) i =
(\<not>(nb_var_exists_with vars b_set (isin_slack_pos mat vars i)))"

(* Checks whether slack-(x_i) is empty *)
fun slack_neg_empty :: "configuration \<Rightarrow> nat \<Rightarrow> bool" where
"slack_neg_empty (Config n b_set mat vars) i =
(\<not>(nb_var_exists_with vars b_set (isin_slack_neg mat vars i)))"


(* Checks whether the given basic variable would cause a failure on the given
configuration. *)
fun b_var_fails :: "configuration \<Rightarrow> nat \<Rightarrow> bool" where
"b_var_fails (Config n b_set mat vars) i = 
(case unpack_rat_triple (lookup vars i) of 
(l_i, alpha_i, u_i) \<Rightarrow> 
(let sp = slack_pos_empty (Config n b_set mat vars) i in 
(let sn = slack_neg_empty (Config n b_set mat vars) i in 
((alpha_i < l_i \<and> sp) \<or> (alpha_i > u_i \<and> sn)))))"

fun b_var_fail_exists :: "var_data \<Rightarrow> configuration \<Rightarrow> bool" where
"b_var_fail_exists Leaf (Config n b_set mat vars) = False" |
"b_var_fail_exists (Node l ((i, l_i, alpha_i, u_i), h) r) (Config n b_set mat vars) = 
((b_var_fail_exists l (Config n b_set mat vars)) \<or>
((isin b_set i) \<and> (b_var_fails (Config n b_set mat vars) i)) \<or> 
(b_var_fail_exists r (Config n b_set mat vars)))"

(* -------------------------------------------------------------- *)


(* 
Validity of configurations:

Possible errors:
index out of bounds (index is not between 0 and n - 1, inclusive)

invalid basic indices

invalid non-basic indices

invalid set of variables

invalid bounds


b_set can be invalid (must be subset of {0, ..., n - 1})
- index out of range (not 0 \<le> j \<le> n - 1)

matrix can be invalid
- index out of range (not 0 \<le> j \<le> n - 1)
- row indices must be exactly basic indices, columns exactly non-basic indices

var data can be invalid
- index out of range (var data must contain exactly 0 to n - 1)
- invalid bounds (lower greater than upper)

*)
datatype config_err = 
  InvalidIndex "nat" | (* variable idx *)
  InvalidVarSet "nat list" "nat list" | (* expected set, actual set *)
  InvalidBasicSet "nat list" "nat list" | (* expected set, actual set *)
  InvalidNonBasicSet "nat" "nat list" "nat list" | 
  (* basic variable idx, expected set, actual set *)
  InvalidBounds "nat" "rat" "rat" (* variable idx, lower bound, upper bound *)

datatype config_check_result =
  Valid |
  InvalidBSet "config_err" |
  InvalidMatrix "config_err" |
  InvalidVarData "config_err"


(* Helper functions for checking the validity of a configuration *)

(* Returns the list of keys of the given map, obtained through an inorder traversal. *)
fun keys_inorder_map :: "((nat * 'a) tree_ht) \<Rightarrow> nat list" where
"keys_inorder_map Leaf = Nil" |
"keys_inorder_map (Node l ((j, val), h) r) = 
(keys_inorder_map l) @ (Cons j (keys_inorder_map r))"


fun all_in_bounds :: "nat_set \<Rightarrow> nat \<Rightarrow> config_err option" where
"all_in_bounds Leaf n = None" |
"all_in_bounds (Node l (j, h) r) n = 
(case (all_in_bounds l n) of 
Some err \<Rightarrow> Some err |
None \<Rightarrow> (if \<not>(j < n) then (Some (InvalidIndex j)) else
(all_in_bounds r n)))"


fun all_in_bounds_map :: "nat \<Rightarrow> ((nat * 'a) tree_ht) \<Rightarrow> config_err option" where
"all_in_bounds_map n Leaf = None" |
"all_in_bounds_map n (Node l ((j, val), h) r) = 
(case (all_in_bounds_map n l) of 
Some err \<Rightarrow> Some err |
None \<Rightarrow> (if \<not>(j < n) then (Some (InvalidIndex j)) else
(all_in_bounds_map n r)))"


fun all_rows_in_bounds :: "matrix \<Rightarrow> nat \<Rightarrow> config_err option" where
"all_rows_in_bounds Leaf n = None" |
"all_rows_in_bounds (Node l ((i, row), h) r) n = 
(case (all_rows_in_bounds l n) of
Some err \<Rightarrow> Some err |
None \<Rightarrow> (case (all_in_bounds_map n row) of 
Some err \<Rightarrow> Some err |
None \<Rightarrow> (all_rows_in_bounds r n)))"

fun all_rows_equal :: "matrix \<Rightarrow> nat list \<Rightarrow> config_err option" where
"all_rows_equal Leaf nb_list = None" |
"all_rows_equal (Node l ((i, row), h) r) nb_list = 
(case (all_rows_equal l nb_list) of
Some err \<Rightarrow> Some err |
None \<Rightarrow> (let nb_keys = (keys_inorder_map row) in 
(if \<not>(nb_keys = nb_list) then (Some (InvalidNonBasicSet i nb_list nb_keys)) else
(all_rows_equal r nb_list))))"


fun bounds_valid :: "var_data \<Rightarrow> config_err option" where
"bounds_valid Leaf = None" |
"bounds_valid (Node l ((j, l_j, alpha_j, u_j), h) r) = 
(case (bounds_valid l) of
Some err \<Rightarrow> Some err |
None \<Rightarrow> (if \<not>(l_j \<le> u_j) then (Some (InvalidBounds j l_j u_j)) else 
(bounds_valid r)))"



(* Configuration Checking functions *)

fun check_b_set :: "nat_set \<Rightarrow> nat \<Rightarrow> config_err option" where
"check_b_set b_set n = all_in_bounds b_set n"

fun check_matrix :: "matrix \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> config_err option" where
"check_matrix mat n b_list nb_list = 
(case (all_in_bounds_map n mat) of 
Some err \<Rightarrow> Some err |
None \<Rightarrow> (let b_keys = (keys_inorder_map mat) in 
(if (\<not>(b_keys = b_list)) then (Some (InvalidBasicSet b_list b_keys)) else
(case (all_rows_in_bounds mat n) of
Some err \<Rightarrow> Some err |
None \<Rightarrow> (all_rows_equal mat nb_list)))))"

fun check_var_data :: "var_data \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> config_err option" where
"check_var_data vars n var_list = 
(case (all_in_bounds_map n vars) of
Some err \<Rightarrow> Some err |
None \<Rightarrow> (let keys = (keys_inorder_map vars) in
(if (\<not>(keys = var_list)) then (Some (InvalidVarSet var_list keys)) else
(bounds_valid vars))))"

fun check_config :: "configuration \<Rightarrow> config_check_result" where
"check_config (Config n b_set mat vars) = 
(let var_set = var_set_n n in
(let var_list = (inorder var_set) in 
(let b_list = (inorder b_set) in 
(let nb_list = (inorder (nat_set_diff var_set b_set)) in 
(case (check_b_set b_set n) of 
  Some err \<Rightarrow> InvalidBSet err |
  None \<Rightarrow> 
(case (check_matrix mat n b_list nb_list) of
  Some err \<Rightarrow> InvalidMatrix err |
  None \<Rightarrow> 
(case (check_var_data vars n var_list) of
  Some err \<Rightarrow> InvalidVarData err |
  None \<Rightarrow> Valid)))))))"



(* Always specify values/bounds in the order (lower, value, upper) *)
datatype simplex_err = 
  InvalidIndex "nat" | (* variable idx *)
  Basic "nat" | (* variable idx *)
  NonBasic "nat" | (* variable idx *)
  LowerBoundSat "nat" "rat" "rat" | (* variable idx, lower bound, value *)
  UpperBoundSat "nat" "rat" "rat" | (* variable idx, value, upper bound *)
  LowerBoundUnsat "nat" "rat" "rat" | (* variable idx, lower bound, value *)
  UpperBoundUnsat "nat" "rat" "rat" | (* variable idx, value, upper bound *)
  UpdateLowerBoundUnsat "nat" "rat" "rat" | (* variable idx, lower bound, value *)
  UpdateUpperBoundUnsat "nat" "rat" "rat" | (* variable idx, lower bound, value *)
  BoundsSat "nat" "rat" "rat" "rat" | (* variable idx, lower bound, value, upper bound *)
  NoSlackPos "nat" "nat" | (* variable indices i, j *)
  NoSlackNeg "nat" "nat" | (* variable indices i, j *)
  NoSlack "nat" "nat" | (* variable indices i, j *)
  FailureError
  
(* The invalid values of the checker result datatype include the error which occurred
as well as the length of the tail of the list of rules (those which were not executed) *)

datatype checker_result = 
  Valid |
  InvalidPivot1 "simplex_err" "nat" |
  InvalidPivot2 "simplex_err" "nat" |
  InvalidUpdate "simplex_err" "nat" |
  InvalidPivotInBounds "simplex_err" "nat" |
  InvalidUpdateInBounds "simplex_err" "nat" |
  InvalidSuccess "simplex_err" "nat" |
  InvalidFailure "simplex_err" "nat" |
  InvalidRule "calc_rule" "nat"

(*
The following functions check whether a rule application is valid and return a result
indicating that the preconditions were met or where the rule application failed.

The functions return a value of type simplex_err option, with None indicating a valid
rule application and a value of Some specifying the error.
*)

fun check_pivot1 :: "configuration \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> simplex_err option" where
"check_pivot1 (Config n b_set mat vars) i j = 
(if \<not>(i < n) then (Some (InvalidIndex i)) else
(if \<not>(j < n) then (Some (InvalidIndex j)) else
(case unpack_rat_triple (lookup vars i) of (l_i, alpha_i, u_i) \<Rightarrow> 
(if \<not>(isin b_set i) then Some (NonBasic i) else
(if (isin b_set j) then Some (Basic j) else
(if \<not>(alpha_i < l_i) then Some (LowerBoundSat i l_i alpha_i) else 
(if \<not>(isin_slack_pos mat vars i j) then Some (NoSlackPos i j) else
None)))))))"

fun check_pivot2 :: "configuration \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> simplex_err option" where
"check_pivot2 (Config n b_set mat vars) i j = 
(if \<not>(i < n) then (Some (InvalidIndex i)) else
(if \<not>(j < n) then (Some (InvalidIndex j)) else
(case unpack_rat_triple (lookup vars i) of (l_i, alpha_i, u_i) \<Rightarrow> 
(if \<not>(isin b_set i) then Some (NonBasic i) else
(if (isin b_set j) then Some (Basic j) else
(if \<not>(alpha_i > u_i) then Some (UpperBoundSat i alpha_i u_i) else 
(if \<not>(isin_slack_neg mat vars i j) then Some (NoSlackNeg i j) else
None)))))))"

fun check_pivot_in_bounds :: "configuration \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> simplex_err option" where
"check_pivot_in_bounds (Config n b_set mat vars) i j = 
(if \<not>(i < n) then (Some (InvalidIndex i)) else
(if \<not>(j < n) then (Some (InvalidIndex j)) else
(case unpack_rat_triple (lookup vars i) of (l_i, alpha_i, u_i) \<Rightarrow> 
(if \<not>(isin b_set i) then Some (NonBasic i) else
(if (isin b_set j) then Some (Basic j) else
(if \<not>(l_i \<le> alpha_i) then Some (LowerBoundUnsat i l_i alpha_i) else 
(if \<not>(alpha_i \<le> u_i) then Some (UpperBoundUnsat i alpha_i u_i) else 
(if \<not>((isin_slack_pos mat vars i j) \<or> (isin_slack_neg mat vars i j)) 
then Some (NoSlack i j) else
None))))))))"

fun check_update :: "configuration \<Rightarrow> nat \<Rightarrow> rat \<Rightarrow> simplex_err option" where
"check_update (Config n b_set mat vars) j delta = 
(if \<not>(j < n) then (Some (InvalidIndex j)) else
(case unpack_rat_triple (lookup vars j) of (l_j, alpha_j, u_j) \<Rightarrow> 
let j_new = (alpha_j + delta) in 
(if (isin b_set j) then Some (Basic j) else
(if \<not>((alpha_j < l_j) \<or> (alpha_j > u_j)) then Some (BoundsSat j l_j alpha_j u_j) else
(if \<not>(l_j \<le> j_new) then Some (UpdateLowerBoundUnsat j l_j j_new) else
(if \<not>(j_new \<le> u_j) then Some (UpdateUpperBoundUnsat j j_new u_j) else
None))))))"

fun check_update_in_bounds :: "configuration \<Rightarrow> nat \<Rightarrow> rat \<Rightarrow> simplex_err option" where
"check_update_in_bounds (Config n b_set mat vars) j delta = 
(if \<not>(j < n) then (Some (InvalidIndex j)) else
(case unpack_rat_triple (lookup vars j) of (l_j, alpha_j, u_j) \<Rightarrow> 
let j_new = (alpha_j + delta) in 
(if (isin b_set j) then Some (Basic j) else
(if \<not>(l_j \<le> alpha_j) then Some (LowerBoundUnsat j l_j alpha_j) else 
(if \<not>(alpha_j \<le> u_j) then Some (UpperBoundUnsat j alpha_j u_j) else
(if \<not>(l_j \<le> j_new) then Some (UpdateLowerBoundUnsat j l_j j_new) else
(if \<not>(j_new \<le> u_j) then Some (UpdateUpperBoundUnsat j j_new u_j) else
None)))))))"

fun check_success :: "configuration \<Rightarrow> simplex_err option" where
"check_success (Config n b_set mat vars) = (case (var_out_of_bounds vars) of 
None \<Rightarrow> None |
Some (i, (l, alpha, u), b) \<Rightarrow> 
(if b then Some (LowerBoundUnsat i l alpha) 
else Some (UpperBoundUnsat i alpha u)))"

fun check_failure :: "configuration \<Rightarrow> simplex_err option" where
"check_failure (Config n b_set mat vars) =
(if (b_var_fail_exists vars (Config n b_set mat vars)) then None
else (Some FailureError))"


(* Transformation functions *)

fun pivot_config :: "configuration \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> configuration" where
"pivot_config (Config n b_set mat vars) i j = 
(Config n (AVL_Set_Code.insert j (AVL_Set_Code.delete i b_set)) (pivot_mat mat i j) vars)"

fun update_config :: "configuration \<Rightarrow> nat \<Rightarrow> rat \<Rightarrow> configuration" where
"update_config (Config n b_set mat vars) j delta = 
(Config n b_set mat 
(update_basic_vars b_set mat (update_var vars j delta) j delta))"

(* -------------------------------------------------------------- *)

(* The certificate checker function takes an initial configuration and certificate
as input and returns a value of type checker_result indicating that certificate is
valid or specifying the error.

As soon as the function encounters an invalid rule application, it terminates, i.e.
the result specifies only the first error which was found.
*)

fun check_certificate :: "configuration \<Rightarrow> certificate \<Rightarrow> checker_result" where
"check_certificate config Nil = Valid" |
"check_certificate config (Cons rule rules) = (case rules of 
Nil \<Rightarrow> (case rule of 
  Success \<Rightarrow> (case (check_success config) of 
    None \<Rightarrow> Valid | 
    (Some err) \<Rightarrow> (InvalidSuccess err (length rules))) |
  Failure \<Rightarrow> (case (check_failure config) of 
    None \<Rightarrow> Valid | 
    (Some err) \<Rightarrow> (InvalidFailure err (length rules))) |
  _ \<Rightarrow> InvalidRule rule (length rules)) |
_ \<Rightarrow> (case rule of 
  (Pivot1 i j) \<Rightarrow> (case (check_pivot1 config i j) of 
    None \<Rightarrow> (check_certificate (pivot_config config i j) rules) | 
    (Some err) \<Rightarrow> (InvalidPivot1 err (length rules))) |
  (Pivot2 i j) \<Rightarrow> (case (check_pivot2 config i j) of 
    None \<Rightarrow> (check_certificate (pivot_config config i j) rules) | 
    (Some err) \<Rightarrow> (InvalidPivot2 err (length rules))) |
  (PivotInBounds i j) \<Rightarrow> (case (check_pivot_in_bounds config i j) of 
    None \<Rightarrow> (check_certificate (pivot_config config i j) rules) | 
    (Some err) \<Rightarrow> (InvalidPivotInBounds err (length rules))) |
  (Update j delta) \<Rightarrow> (case (check_update config j delta) of 
    None \<Rightarrow> (check_certificate (update_config config j delta) rules) | 
    (Some err) \<Rightarrow> (InvalidUpdate err (length rules))) |
  (UpdateInBounds j delta) \<Rightarrow> (case (check_update_in_bounds config j delta) of 
    None \<Rightarrow> (check_certificate (update_config config j delta) rules) | 
    (Some err) \<Rightarrow> (InvalidUpdateInBounds err (length rules))) |
  _ \<Rightarrow> InvalidRule rule (length rules)))"

(* Code export to SML *)

(*
export_code 
nat_of_integer
integer_of_nat
rat_of_digits_pair_sgn
lists_to_mat list_to_set list_to_var_data
Config
Pivot1 Pivot2 Update Success Failure
config_check_result.Valid checker_result.Valid
check_config check_certificate
in SML module_name "CertificateChecker"
file "/Users/a3r/macOS12_VM_Shared/certificate_checker_v14.sml"
*)


end