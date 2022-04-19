structure CertificateChecker : sig
  type nat
  val integer_of_nat : nat -> IntInf.int
  type rat
  type 'a tree
  datatype calc_rule = Pivot1 of nat * nat | Pivot2 of nat * nat |
    Update of nat * rat | PivotInBounds of nat * nat |
    UpdateInBounds of nat * rat | Success | Failure
  type config_err
  type simplex_err
  datatype configuration =
    Config of
      nat * (nat * nat) tree * ((nat * ((nat * rat) * nat) tree) * nat) tree *
        ((nat * (rat * (rat * rat))) * nat) tree
  datatype checker_result = Valid | InvalidPivot1 of simplex_err * nat |
    InvalidPivot2 of simplex_err * nat | InvalidUpdate of simplex_err * nat |
    InvalidPivotInBounds of simplex_err * nat |
    InvalidUpdateInBounds of simplex_err * nat |
    InvalidSuccess of simplex_err * nat | InvalidFailure of simplex_err * nat |
    InvalidRule of calc_rule * nat
  datatype config_check_result = Valida | InvalidBSet of config_err |
    InvalidMatrix of config_err | InvalidVarData of config_err
  val nat_of_integer : IntInf.int -> nat
  val list_to_set : nat list -> (nat * nat) tree
  val check_config : configuration -> config_check_result
  val lists_to_mat :
    (nat * (nat * rat) list) list ->
      ((nat * ((nat * rat) * nat) tree) * nat) tree
  val list_to_var_data :
    (nat * (rat * (rat * rat))) list -> ((nat * (rat * (rat * rat))) * nat) tree
  val check_certificate : configuration -> calc_rule list -> checker_result
  val rat_of_digits_pair_sgn : bool -> nat list -> nat list -> rat
end = struct

datatype int = Int_of_integer of IntInf.int;

fun integer_of_int (Int_of_integer k) = k;

fun equal_inta k l = (((integer_of_int k) : IntInf.int) = (integer_of_int l));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_int = {equal = equal_inta} : int equal;

datatype num = One | Bit0 of num | Bit1 of num;

val one_inta : int = Int_of_integer (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_int = {one = one_inta} : int one;

fun times_inta k l =
  Int_of_integer (IntInf.* (integer_of_int k, integer_of_int l));

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

val times_int = {times = times_inta} : int times;

val power_int = {one_power = one_int, times_power = times_int} : int power;

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

val equal_nat = {equal = equal_nata} : nat equal;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_nat = {ord_preorder = ord_nat} : nat preorder;

val order_nat = {preorder_order = preorder_nat} : nat order;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_nat = {order_linorder = order_nat} : nat linorder;

fun eq A_ a b = equal A_ a b;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

datatype rat = Frct of (int * int);

fun quotient_of (Frct x) = x;

fun equal_rata a b =
  equal_proda equal_int equal_int (quotient_of a) (quotient_of b);

val equal_rat = {equal = equal_rata} : rat equal;

datatype 'a tree = Leaf | Node of 'a tree * 'a * 'a tree;

fun equal_treea A_ Leaf (Node (x21, x22, x23)) = false
  | equal_treea A_ (Node (x21, x22, x23)) Leaf = false
  | equal_treea A_ (Node (x21, x22, x23)) (Node (y21, y22, y23)) =
    equal_treea A_ x21 y21 andalso
      (eq A_ x22 y22 andalso equal_treea A_ x23 y23)
  | equal_treea A_ Leaf Leaf = true;

fun equal_tree A_ = {equal = equal_treea A_} : 'a tree equal;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

datatype cmp_val = LT | EQ | GT;

datatype calc_rule = Pivot1 of nat * nat | Pivot2 of nat * nat |
  Update of nat * rat | PivotInBounds of nat * nat | UpdateInBounds of nat * rat
  | Success | Failure;

datatype config_err = InvalidIndex of nat | InvalidVarSet of nat list * nat list
  | InvalidBasicSet of nat list * nat list |
  InvalidNonBasicSet of nat * nat list * nat list |
  InvalidBounds of nat * rat * rat;

datatype simplex_err = InvalidIndexa of nat | Basic of nat | NonBasic of nat |
  LowerBoundSat of nat * rat * rat | UpperBoundSat of nat * rat * rat |
  LowerBoundUnsat of nat * rat * rat | UpperBoundUnsat of nat * rat * rat |
  UpdateLowerBoundUnsat of nat * rat * rat |
  UpdateUpperBoundUnsat of nat * rat * rat | BoundsSat of nat * rat * rat * rat
  | NoSlackPos of nat * nat | NoSlackNeg of nat * nat | NoSlack of nat * nat |
  FailureError;

datatype configuration =
  Config of
    nat * (nat * nat) tree * ((nat * ((nat * rat) * nat) tree) * nat) tree *
      ((nat * (rat * (rat * rat))) * nat) tree;

datatype checker_result = Valid | InvalidPivot1 of simplex_err * nat |
  InvalidPivot2 of simplex_err * nat | InvalidUpdate of simplex_err * nat |
  InvalidPivotInBounds of simplex_err * nat |
  InvalidUpdateInBounds of simplex_err * nat |
  InvalidSuccess of simplex_err * nat | InvalidFailure of simplex_err * nat |
  InvalidRule of calc_rule * nat;

datatype config_check_result = Valida | InvalidBSet of config_err |
  InvalidMatrix of config_err | InvalidVarData of config_err;

fun cmp (A1_, A2_) x y =
  (if less ((ord_preorder o preorder_order o order_linorder) A2_) x y then LT
    else (if eq A1_ x y then EQ else GT));

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

val one_nat : nat = Nat (1 : IntInf.int);

fun suc n = plus_nat n one_nat;

fun apsnd f (x, y) = (x, f y);

fun divmod_integer k l =
  (if ((k : IntInf.int) = (0 : IntInf.int))
    then ((0 : IntInf.int), (0 : IntInf.int))
    else (if IntInf.< ((0 : IntInf.int), l)
           then (if IntInf.< ((0 : IntInf.int), k)
                  then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                  else let
                         val (r, s) =
                           IntInf.divMod (IntInf.abs k, IntInf.abs l);
                       in
                         (if ((s : IntInf.int) = (0 : IntInf.int))
                           then (IntInf.~ r, (0 : IntInf.int))
                           else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                  IntInf.- (l, s)))
                       end)
           else (if ((l : IntInf.int) = (0 : IntInf.int))
                  then ((0 : IntInf.int), k)
                  else apsnd IntInf.~
                         (if IntInf.< (k, (0 : IntInf.int))
                           then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                           else let
                                  val (r, s) =
                                    IntInf.divMod (IntInf.abs k, IntInf.abs l);
                                in
                                  (if ((s : IntInf.int) = (0 : IntInf.int))
                                    then (IntInf.~ r, (0 : IntInf.int))
                                    else (IntInf.- (IntInf.~
              r, (1 : IntInf.int)),
   IntInf.- (IntInf.~ l, s)))
                                end))));

fun fst (x1, x2) = x1;

fun divide_integer k l = fst (divmod_integer k l);

fun divide_int k l =
  Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));

fun uminus_int k = Int_of_integer (IntInf.~ (integer_of_int k));

val zero_int : int = Int_of_integer (0 : IntInf.int);

fun less_int k l = IntInf.< (integer_of_int k, integer_of_int l);

fun snd (x1, x2) = x2;

fun modulo_integer k l = snd (divmod_integer k l);

fun gcd_integer k l =
  IntInf.abs
    (if ((l : IntInf.int) = (0 : IntInf.int)) then k
      else gcd_integer l (modulo_integer (IntInf.abs k) (IntInf.abs l)));

fun gcd_int (Int_of_integer x) (Int_of_integer y) =
  Int_of_integer (gcd_integer x y);

fun normalize p =
  (if less_int zero_int (snd p)
    then let
           val a = gcd_int (fst p) (snd p);
         in
           (divide_int (fst p) a, divide_int (snd p) a)
         end
    else (if equal_inta (snd p) zero_int then (zero_int, one_inta)
           else let
                  val a = uminus_int (gcd_int (fst p) (snd p));
                in
                  (divide_int (fst p) a, divide_int (snd p) a)
                end));

fun fract a b = Frct (normalize (a, b));

fun isin (A1_, A2_) Leaf x = false
  | isin (A1_, A2_) (Node (l, (a, uu), r)) x =
    (case cmp (A1_, A2_) x a of LT => isin (A1_, A2_) l x | EQ => true
      | GT => isin (A1_, A2_) r x);

fun inorder Leaf = []
  | inorder (Node (l, (a, uu), r)) = inorder l @ a :: inorder r;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

val zero_nat : nat = Nat (0 : IntInf.int);

fun ht Leaf = zero_nat
  | ht (Node (l, (a, n), r)) = n;

fun node l a r = Node (l, (a, plus_nat (max ord_nat (ht l) (ht r)) one_nat), r);

fun balL ab ca c =
  (if equal_nata (ht ab) (plus_nat (ht c) (nat_of_integer (2 : IntInf.int)))
    then let
           val Node (a, aa, b) = ab;
           val (aaa, _) = aa;
         in
           (if less_eq_nat (ht b) (ht a) then node a aaa (node b ca c)
             else let
                    val Node (b_1, (ba, _), b_2) = b;
                  in
                    node (node a aaa b_1) ba (node b_2 ca c)
                  end)
         end
    else node ab ca c);

fun split_max A_ (Node (l, (a, uu), r)) =
  (if equal_treea (equal_prod A_ equal_nat) r Leaf then (l, a)
    else let
           val b = split_max A_ r;
           val (ra, ba) = b;
         in
           (balL l a ra, ba)
         end);

fun balR aa a bc =
  (if equal_nata (ht bc) (plus_nat (ht aa) (nat_of_integer (2 : IntInf.int)))
    then let
           val Node (b, (ca, _), c) = bc;
         in
           (if less_eq_nat (ht b) (ht c) then node (node aa a b) ca c
             else let
                    val Node (b_1, (ba, _), b_2) = b;
                  in
                    node (node aa a b_1) ba (node b_2 ca c)
                  end)
         end
    else node aa a bc);

fun delete (A1_, A2_) B_ uu Leaf = Leaf
  | delete (A1_, A2_) B_ x (Node (l, ((a, b), h), r)) =
    (case cmp (A1_, A2_) x a of LT => balR (delete (A1_, A2_) B_ x l) (a, b) r
      | EQ =>
        (if equal_treea (equal_prod (equal_prod A1_ B_) equal_nat) l Leaf then r
          else let
                 val (la, ab) = split_max (equal_prod A1_ B_) l;
               in
                 balR la ab r
               end)
      | GT => balL l (a, b) (delete (A1_, A2_) B_ x r));

fun update (A1_, A2_) x y Leaf = Node (Leaf, ((x, y), one_nat), Leaf)
  | update (A1_, A2_) x y (Node (l, ((a, b), h), r)) =
    (case cmp (A1_, A2_) x a of LT => balL (update (A1_, A2_) x y l) (a, b) r
      | EQ => Node (l, ((x, y), h), r)
      | GT => balR l (a, b) (update (A1_, A2_) x y r));

fun lookup (A1_, A2_) Leaf x = NONE
  | lookup (A1_, A2_) (Node (l, ((a, b), uu), r)) x =
    (case cmp (A1_, A2_) x a of LT => lookup (A1_, A2_) l x | EQ => SOME b
      | GT => lookup (A1_, A2_) r x);

fun gen_length n (x :: xs) = gen_length (suc n) xs
  | gen_length n [] = n;

val empty : ('a * nat) tree = Leaf;

fun deletea (A1_, A2_) uu Leaf = Leaf
  | deletea (A1_, A2_) x (Node (l, (a, n), r)) =
    (case cmp (A1_, A2_) x a of LT => balR (deletea (A1_, A2_) x l) a r
      | EQ =>
        (if equal_treea (equal_prod A1_ equal_nat) l Leaf then r
          else let
                 val aa = split_max A1_ l;
                 val (la, ab) = aa;
               in
                 balR la ab r
               end)
      | GT => balL l a (deletea (A1_, A2_) x r));

fun insert (A1_, A2_) x Leaf = Node (Leaf, (x, one_nat), Leaf)
  | insert (A1_, A2_) x (Node (l, (a, n), r)) =
    (case cmp (A1_, A2_) x a of LT => balL (insert (A1_, A2_) x l) a r
      | EQ => Node (l, (a, n), r) | GT => balR l a (insert (A1_, A2_) x r));

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun power A_ a n =
  (if equal_nata n zero_nat then one (one_power A_)
    else times (times_power A_) a (power A_ a (minus_nat n one_nat)));

val one_rat : rat = Frct (one_inta, one_inta);

fun less_rat p q = let
                     val a = quotient_of p;
                     val (aa, c) = a;
                     val b = quotient_of q;
                     val (ba, d) = b;
                   in
                     less_int (times_inta aa d) (times_inta c ba)
                   end;

fun int_of_nat n = Int_of_integer (integer_of_nat n);

fun plus_int k l =
  Int_of_integer (IntInf.+ (integer_of_int k, integer_of_int l));

fun plus_rat p q =
  Frct let
         val a = quotient_of p;
         val (aa, c) = a;
         val b = quotient_of q;
         val (ba, d) = b;
       in
         normalize
           (plus_int (times_inta aa d) (times_inta ba c), times_inta c d)
       end;

val zero_rat : rat = Frct (zero_int, one_inta);

fun less_eq_int k l = IntInf.<= (integer_of_int k, integer_of_int l);

fun less_eq_rat p q = let
                        val a = quotient_of p;
                        val (aa, c) = a;
                        val b = quotient_of q;
                        val (ba, d) = b;
                      in
                        less_eq_int (times_inta aa d) (times_inta c ba)
                      end;

fun times_rat p q = Frct let
                           val a = quotient_of p;
                           val (aa, c) = a;
                           val b = quotient_of q;
                           val (ba, d) = b;
                         in
                           normalize (times_inta aa ba, times_inta c d)
                         end;

fun size_list x = gen_length zero_nat x;

fun divide_rat p q = Frct let
                            val a = quotient_of p;
                            val (aa, c) = a;
                            val b = quotient_of q;
                            val (ba, d) = b;
                          in
                            normalize (times_inta aa d, times_inta c ba)
                          end;

fun uminus_rat p = Frct let
                          val a = quotient_of p;
                          val (aa, b) = a;
                        in
                          (uminus_int aa, b)
                        end;

fun map_tree A_ Leaf f = Leaf
  | map_tree A_ (Node (l, ((a, b), h), r)) f =
    Node (map_tree A_ l f, ((a, f b), h), map_tree A_ r f);

fun equal_list A_ [] (x21 :: x22) = false
  | equal_list A_ (x21 :: x22) [] = false
  | equal_list A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_list A_ x22 y22
  | equal_list A_ [] [] = true;

fun f_pivot_row t_ij r = uminus_rat (divide_rat r t_ij);

fun unpack_rat NONE = zero_rat
  | unpack_rat (SOME r) = r;

fun update_row_i t i j =
  let
    val t_ij = unpack_rat (lookup (equal_nat, linorder_nat) t j);
  in
    update (equal_nat, linorder_nat) i (divide_rat one_rat t_ij)
      (map_tree linorder_nat (delete (equal_nat, linorder_nat) equal_rat j t)
        (f_pivot_row t_ij))
  end;

fun add_mult_row row fac Leaf = Leaf
  | add_mult_row row fac (Node (l, ((j, vala), h), r)) =
    Node (add_mult_row row fac l,
           ((j, plus_rat vala
                  (times_rat fac
                    (unpack_rat (lookup (equal_nat, linorder_nat) row j)))),
             h),
           add_mult_row row fac r);

fun update_other_row new_row i j row =
  let
    val fac = unpack_rat (lookup (equal_nat, linorder_nat) row j);
  in
    add_mult_row new_row fac
      (update (equal_nat, linorder_nat) i zero_rat
        (delete (equal_nat, linorder_nat) equal_rat j row))
  end;

fun update_rows m new_row i j =
  map_tree linorder_nat m (update_other_row new_row i j);

fun unpack_tree NONE = empty
  | unpack_tree (SOME t) = t;

fun pivot_mat m i j =
  let
    val new_row =
      update_row_i (unpack_tree (lookup (equal_nat, linorder_nat) m i)) i j;
  in
    update (equal_nat, linorder_nat) j new_row
      (update_rows
        (delete (equal_nat, linorder_nat)
          (equal_tree (equal_prod (equal_prod equal_nat equal_rat) equal_nat)) i
          m)
        new_row i j)
  end;

fun var_set_n n =
  (if equal_nata n zero_nat then empty
    else insert (equal_nat, linorder_nat) (minus_nat n one_nat)
           (var_set_n (minus_nat n one_nat)));

fun trim_ld_zs [] = []
  | trim_ld_zs (d :: ds) =
    (if equal_nata d zero_nat then trim_ld_zs ds else d :: ds);

fun trim_tr_zsa [] zs = []
  | trim_tr_zsa (d :: ds) zs =
    (if equal_nata d zero_nat then trim_tr_zsa ds (zero_nat :: zs)
      else zs @ d :: trim_tr_zsa ds []);

fun trim_tr_zs ds = trim_tr_zsa ds [];

fun lookup_mat m i j =
  unpack_rat
    (lookup (equal_nat, linorder_nat)
      (unpack_tree (lookup (equal_nat, linorder_nat) m i)) j);

fun update_assignment (a, (b, c)) delta = (a, (plus_rat b delta, c));

fun unpack_rat_triple NONE = (zero_rat, (zero_rat, zero_rat))
  | unpack_rat_triple (SOME (a, (b, c))) = (a, (b, c));

fun update_var data j delta =
  update (equal_nat, linorder_nat) j
    (update_assignment
      (unpack_rat_triple (lookup (equal_nat, linorder_nat) data j)) delta)
    data;

fun nb_var_exists_with Leaf b_set f = false
  | nb_var_exists_with (Node (l, ((j, (l_j, (alpha_j, u_j))), h), r)) b_set f =
    (if not (isin (equal_nat, linorder_nat) b_set j) andalso f j then true
      else nb_var_exists_with l b_set f orelse nb_var_exists_with r b_set f);

fun isin_slack_pos mat vars i j =
  let
    val t_ij = lookup_mat mat i j;
    val (l_j, (alpha_j, u_j)) =
      unpack_rat_triple (lookup (equal_nat, linorder_nat) vars j);
  in
    less_rat zero_rat t_ij andalso less_rat alpha_j u_j orelse
      less_rat t_ij zero_rat andalso less_rat l_j alpha_j
  end;

fun slack_pos_empty (Config (n, b_set, mat, vars)) i =
  not (nb_var_exists_with vars b_set (isin_slack_pos mat vars i));

fun isin_slack_neg mat vars i j =
  let
    val t_ij = lookup_mat mat i j;
    val (l_j, (alpha_j, u_j)) =
      unpack_rat_triple (lookup (equal_nat, linorder_nat) vars j);
  in
    less_rat t_ij zero_rat andalso less_rat alpha_j u_j orelse
      less_rat zero_rat t_ij andalso less_rat l_j alpha_j
  end;

fun slack_neg_empty (Config (n, b_set, mat, vars)) i =
  not (nb_var_exists_with vars b_set (isin_slack_neg mat vars i));

fun b_var_fails (Config (n, b_set, mat, vars)) i =
  let
    val (l_i, (alpha_i, u_i)) =
      unpack_rat_triple (lookup (equal_nat, linorder_nat) vars i);
    val sp = slack_pos_empty (Config (n, b_set, mat, vars)) i;
    val sn = slack_neg_empty (Config (n, b_set, mat, vars)) i;
  in
    less_rat alpha_i l_i andalso sp orelse less_rat u_i alpha_i andalso sn
  end;

fun all_in_bounds Leaf n = NONE
  | all_in_bounds (Node (l, (j, h), r)) n =
    (case all_in_bounds l n
      of NONE =>
        (if not (less_nat j n) then SOME (InvalidIndex j)
          else all_in_bounds r n)
      | SOME a => SOME a);

fun check_b_set b_set n = all_in_bounds b_set n;

fun list_to_row [] = empty
  | list_to_row ((n, r) :: tail) =
    update (equal_nat, linorder_nat) n r (list_to_row tail);

fun list_to_set [] = empty
  | list_to_set (n :: tail) =
    insert (equal_nat, linorder_nat) n (list_to_set tail);

fun bounds_valid Leaf = NONE
  | bounds_valid (Node (l, ((j, (l_j, (alpha_j, u_j))), h), r)) =
    (case bounds_valid l
      of NONE =>
        (if not (less_eq_rat l_j u_j) then SOME (InvalidBounds (j, l_j, u_j))
          else bounds_valid r)
      | SOME a => SOME a);

fun all_in_bounds_map n Leaf = NONE
  | all_in_bounds_map n (Node (l, ((j, vala), h), r)) =
    (case all_in_bounds_map n l
      of NONE =>
        (if not (less_nat j n) then SOME (InvalidIndex j)
          else all_in_bounds_map n r)
      | SOME a => SOME a);

fun keys_inorder_map Leaf = []
  | keys_inorder_map (Node (l, ((j, vala), h), r)) =
    keys_inorder_map l @ j :: keys_inorder_map r;

fun check_var_data vars n var_list =
  (case all_in_bounds_map n vars
    of NONE =>
      let
        val keys = keys_inorder_map vars;
      in
        (if not (equal_list equal_nat keys var_list)
          then SOME (InvalidVarSet (var_list, keys)) else bounds_valid vars)
      end
    | SOME a => SOME a);

fun nat_set_diff a Leaf = a
  | nat_set_diff a (Node (l, (elt, h), r)) =
    nat_set_diff (deletea (equal_nat, linorder_nat) elt (nat_set_diff a l)) r;

fun all_rows_in_bounds Leaf n = NONE
  | all_rows_in_bounds (Node (l, ((i, row), h), r)) n =
    (case all_rows_in_bounds l n
      of NONE =>
        (case all_in_bounds_map n row of NONE => all_rows_in_bounds r n
          | SOME a => SOME a)
      | SOME a => SOME a);

fun all_rows_equal Leaf nb_list = NONE
  | all_rows_equal (Node (l, ((i, row), h), r)) nb_list =
    (case all_rows_equal l nb_list
      of NONE =>
        let
          val nb_keys = keys_inorder_map row;
        in
          (if not (equal_list equal_nat nb_keys nb_list)
            then SOME (InvalidNonBasicSet (i, nb_list, nb_keys))
            else all_rows_equal r nb_list)
        end
      | SOME a => SOME a);

fun check_matrix mat n b_list nb_list =
  (case all_in_bounds_map n mat
    of NONE =>
      let
        val b_keys = keys_inorder_map mat;
      in
        (if not (equal_list equal_nat b_keys b_list)
          then SOME (InvalidBasicSet (b_list, b_keys))
          else (case all_rows_in_bounds mat n
                 of NONE => all_rows_equal mat nb_list | SOME a => SOME a))
      end
    | SOME a => SOME a);

fun check_config (Config (n, b_set, mat, vars)) =
  let
    val var_set = var_set_n n;
    val var_list = inorder var_set;
    val b_list = inorder b_set;
    val nb_list = inorder (nat_set_diff var_set b_set);
  in
    (case check_b_set b_set n
      of NONE =>
        (case check_matrix mat n b_list nb_list
          of NONE =>
            (case check_var_data vars n var_list of NONE => Valida
              | SOME a => InvalidVarData a)
          | SOME a => InvalidMatrix a)
      | SOME a => InvalidBSet a)
  end;

fun check_pivot1 (Config (n, b_set, mat, vars)) i j =
  (if not (less_nat i n) then SOME (InvalidIndexa i)
    else (if not (less_nat j n) then SOME (InvalidIndexa j)
           else let
                  val (l_i, (alpha_i, _)) =
                    unpack_rat_triple (lookup (equal_nat, linorder_nat) vars i);
                in
                  (if not (isin (equal_nat, linorder_nat) b_set i)
                    then SOME (NonBasic i)
                    else (if isin (equal_nat, linorder_nat) b_set j
                           then SOME (Basic j)
                           else (if not (less_rat alpha_i l_i)
                                  then SOME (LowerBoundSat (i, l_i, alpha_i))
                                  else (if not (isin_slack_pos mat vars i j)
 then SOME (NoSlackPos (i, j)) else NONE))))
                end));

fun check_pivot2 (Config (n, b_set, mat, vars)) i j =
  (if not (less_nat i n) then SOME (InvalidIndexa i)
    else (if not (less_nat j n) then SOME (InvalidIndexa j)
           else let
                  val (_, (alpha_i, u_i)) =
                    unpack_rat_triple (lookup (equal_nat, linorder_nat) vars i);
                in
                  (if not (isin (equal_nat, linorder_nat) b_set i)
                    then SOME (NonBasic i)
                    else (if isin (equal_nat, linorder_nat) b_set j
                           then SOME (Basic j)
                           else (if not (less_rat u_i alpha_i)
                                  then SOME (UpperBoundSat (i, alpha_i, u_i))
                                  else (if not (isin_slack_neg mat vars i j)
 then SOME (NoSlackNeg (i, j)) else NONE))))
                end));

fun check_update (Config (n, b_set, mat, vars)) j delta =
  (if not (less_nat j n) then SOME (InvalidIndexa j)
    else let
           val (l_j, (alpha_j, u_j)) =
             unpack_rat_triple (lookup (equal_nat, linorder_nat) vars j);
           val j_new = plus_rat alpha_j delta;
         in
           (if isin (equal_nat, linorder_nat) b_set j then SOME (Basic j)
             else (if not (less_rat alpha_j l_j orelse less_rat u_j alpha_j)
                    then SOME (BoundsSat (j, l_j, alpha_j, u_j))
                    else (if not (less_eq_rat l_j j_new)
                           then SOME (UpdateLowerBoundUnsat (j, l_j, j_new))
                           else (if not (less_eq_rat j_new u_j)
                                  then SOME
 (UpdateUpperBoundUnsat (j, j_new, u_j))
                                  else NONE))))
         end);

fun lists_to_mat [] = empty
  | lists_to_mat ((n, lst) :: tail) =
    update (equal_nat, linorder_nat) n (list_to_row lst) (lists_to_mat tail);

fun pivot_config (Config (n, b_set, mat, vars)) i j =
  Config
    (n, insert (equal_nat, linorder_nat) j
          (deletea (equal_nat, linorder_nat) i b_set),
      pivot_mat mat i j, vars);

fun int_of_digits [] acc = acc
  | int_of_digits (d :: ds) acc =
    int_of_digits ds
      (plus_int (times_inta acc (Int_of_integer (10 : IntInf.int)))
        (int_of_nat d));

fun b_var_fail_exists Leaf (Config (n, b_set, mat, vars)) = false
  | b_var_fail_exists (Node (l, ((i, (l_i, (alpha_i, u_i))), h), r))
    (Config (n, b_set, mat, vars)) =
    b_var_fail_exists l (Config (n, b_set, mat, vars)) orelse
      (isin (equal_nat, linorder_nat) b_set i andalso
         b_var_fails (Config (n, b_set, mat, vars)) i orelse
        b_var_fail_exists r (Config (n, b_set, mat, vars)));

fun check_failure (Config (n, b_set, mat, vars)) =
  (if b_var_fail_exists vars (Config (n, b_set, mat, vars)) then NONE
    else SOME FailureError);

fun var_out_of_bounds Leaf = NONE
  | var_out_of_bounds (Node (l, ((j, (l_j, (alpha_j, r_j))), h), r)) =
    (case var_out_of_bounds l
      of NONE =>
        (if not (less_eq_rat l_j alpha_j)
          then SOME (j, ((l_j, (alpha_j, r_j)), true))
          else (if not (less_eq_rat alpha_j r_j)
                 then SOME (j, ((l_j, (alpha_j, r_j)), false))
                 else var_out_of_bounds r))
      | SOME (i, (t, b)) => SOME (i, (t, b)));

fun check_success (Config (n, b_set, mat, vars)) =
  (case var_out_of_bounds vars of NONE => NONE
    | SOME (i, ((l, (alpha, _)), true)) => SOME (LowerBoundUnsat (i, l, alpha))
    | SOME (i, ((_, (alpha, u)), false)) =>
      SOME (UpperBoundUnsat (i, alpha, u)));

fun update_basic_var mat j vars i delta =
  update (equal_nat, linorder_nat) i
    (update_assignment
      (unpack_rat_triple (lookup (equal_nat, linorder_nat) vars i))
      (times_rat delta (lookup_mat mat i j)))
    vars;

fun update_basic_vars Leaf mat vars j delta = vars
  | update_basic_vars (Node (l, (i, h), r)) mat vars j delta =
    update_basic_vars r mat
      (update_basic_vars l mat (update_basic_var mat j vars i delta) j delta) j
      delta;

fun update_config (Config (n, b_set, mat, vars)) j delta =
  Config
    (n, b_set, mat,
      update_basic_vars b_set mat (update_var vars j delta) j delta);

fun list_to_var_data [] = empty
  | list_to_var_data ((n, triple) :: tail) =
    update (equal_nat, linorder_nat) n triple (list_to_var_data tail);

fun check_update_in_bounds (Config (n, b_set, mat, vars)) j delta =
  (if not (less_nat j n) then SOME (InvalidIndexa j)
    else let
           val (l_j, (alpha_j, u_j)) =
             unpack_rat_triple (lookup (equal_nat, linorder_nat) vars j);
           val j_new = plus_rat alpha_j delta;
         in
           (if isin (equal_nat, linorder_nat) b_set j then SOME (Basic j)
             else (if not (less_eq_rat l_j alpha_j)
                    then SOME (LowerBoundUnsat (j, l_j, alpha_j))
                    else (if not (less_eq_rat alpha_j u_j)
                           then SOME (UpperBoundUnsat (j, alpha_j, u_j))
                           else (if not (less_eq_rat l_j j_new)
                                  then SOME
 (UpdateLowerBoundUnsat (j, l_j, j_new))
                                  else (if not (less_eq_rat j_new u_j)
 then SOME (UpdateUpperBoundUnsat (j, j_new, u_j)) else NONE)))))
         end);

fun check_pivot_in_bounds (Config (n, b_set, mat, vars)) i j =
  (if not (less_nat i n) then SOME (InvalidIndexa i)
    else (if not (less_nat j n) then SOME (InvalidIndexa j)
           else let
                  val (l_i, (alpha_i, u_i)) =
                    unpack_rat_triple (lookup (equal_nat, linorder_nat) vars i);
                in
                  (if not (isin (equal_nat, linorder_nat) b_set i)
                    then SOME (NonBasic i)
                    else (if isin (equal_nat, linorder_nat) b_set j
                           then SOME (Basic j)
                           else (if not (less_eq_rat l_i alpha_i)
                                  then SOME (LowerBoundUnsat (i, l_i, alpha_i))
                                  else (if not (less_eq_rat alpha_i u_i)
 then SOME (UpperBoundUnsat (i, alpha_i, u_i))
 else (if not (isin_slack_pos mat vars i j orelse isin_slack_neg mat vars i j)
        then SOME (NoSlack (i, j)) else NONE)))))
                end));

fun check_certificate config [] = Valid
  | check_certificate config (rule :: rules) =
    (case rules
      of [] =>
        (case rule of Pivot1 (_, _) => InvalidRule (rule, size_list rules)
          | Pivot2 (_, _) => InvalidRule (rule, size_list rules)
          | Update (_, _) => InvalidRule (rule, size_list rules)
          | PivotInBounds (_, _) => InvalidRule (rule, size_list rules)
          | UpdateInBounds (_, _) => InvalidRule (rule, size_list rules)
          | Success =>
            (case check_success config of NONE => Valid
              | SOME err => InvalidSuccess (err, size_list rules))
          | Failure =>
            (case check_failure config of NONE => Valid
              | SOME err => InvalidFailure (err, size_list rules)))
      | _ :: _ =>
        (case rule
          of Pivot1 (i, j) =>
            (case check_pivot1 config i j
              of NONE => check_certificate (pivot_config config i j) rules
              | SOME err => InvalidPivot1 (err, size_list rules))
          | Pivot2 (i, j) =>
            (case check_pivot2 config i j
              of NONE => check_certificate (pivot_config config i j) rules
              | SOME err => InvalidPivot2 (err, size_list rules))
          | Update (j, delta) =>
            (case check_update config j delta
              of NONE => check_certificate (update_config config j delta) rules
              | SOME err => InvalidUpdate (err, size_list rules))
          | PivotInBounds (i, j) =>
            (case check_pivot_in_bounds config i j
              of NONE => check_certificate (pivot_config config i j) rules
              | SOME err => InvalidPivotInBounds (err, size_list rules))
          | UpdateInBounds (j, delta) =>
            (case check_update_in_bounds config j delta
              of NONE => check_certificate (update_config config j delta) rules
              | SOME err => InvalidUpdateInBounds (err, size_list rules))
          | Success => InvalidRule (rule, size_list rules)
          | Failure => InvalidRule (rule, size_list rules)));

fun rat_of_digits_pair (ds_1, ds_2) =
  let
    val ds_1a = trim_ld_zs ds_1;
    val ds_2a = trim_tr_zs ds_2;
  in
    fract (int_of_digits (ds_1a @ ds_2a) zero_int)
      (power power_int (Int_of_integer (10 : IntInf.int)) (size_list ds_2a))
  end;

fun rat_of_digits_pair_sgn pos w f =
  times_rat (if pos then one_rat else uminus_rat one_rat)
    (rat_of_digits_pair (w, f));

end; (*struct CertificateChecker*)
