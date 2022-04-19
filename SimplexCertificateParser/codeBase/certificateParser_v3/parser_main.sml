
open SimplexCertificate


fun nat_of_int i = CertificateChecker.nat_of_integer (Int.toLarge i)

fun rat_of_decimal (pos, whole_ints, frac_ints) =
  CertificateChecker.rat_of_digits_pair_sgn pos 
    (map nat_of_int whole_ints) (map nat_of_int frac_ints)

fun nat_list_to_isabelle nat_list =
  map nat_of_int nat_list

fun nat_map_list_to_isabelle val_to_isabelle nat_map = 
  map (fn (n, value) => ((nat_of_int n), (val_to_isabelle value))) nat_map

fun nat_rat_map_2d_list_to_isabelle nat_map = 
  nat_map_list_to_isabelle (nat_map_list_to_isabelle rat_of_decimal) nat_map

fun nat_rat_triple_map_list_to_isabelle nat_map =
  nat_map_list_to_isabelle 
  (fn (d1, d2, d3) => (rat_of_decimal d1, (rat_of_decimal d2, rat_of_decimal d3))) nat_map

fun calc_rule_to_isabelle rule = 
  case rule of
    (SimplexCertificate.Pivot1 (i, j)) => 
      (CertificateChecker.Pivot1 (nat_of_int i, nat_of_int j)) |
    (SimplexCertificate.Pivot2 (i, j)) => 
      (CertificateChecker.Pivot2 (nat_of_int i, nat_of_int j)) |
    (SimplexCertificate.Update (j, delta)) => 
      (CertificateChecker.Update (nat_of_int j, rat_of_decimal delta)) | 
    (SimplexCertificate.PivotInBounds (i, j)) => 
      (CertificateChecker.PivotInBounds (nat_of_int i, nat_of_int j)) |
    (SimplexCertificate.UpdateInBounds (j, delta)) => 
      (CertificateChecker.UpdateInBounds (nat_of_int j, rat_of_decimal delta)) | 
    (SimplexCertificate.Success) => 
      CertificateChecker.Success |
    (SimplexCertificate.Failure) => 
      CertificateChecker.Failure

fun calc_rule_list_to_isabelle calc_rule_list = 
  map calc_rule_to_isabelle calc_rule_list

(* ------------------------------------ *)

fun readFile file =
let
    fun next_String input = (TextIO.inputAll input)
    val stream = TextIO.openIn file
in
    next_String stream
end

fun writeFile file content =
    let val fd = TextIO.openOut file
        val _ = TextIO.output (fd, content) handle e => (TextIO.closeOut fd; raise e)
        val _ = TextIO.closeOut fd
    in () end

fun parse_wrapper parser file =
  case (CharParser.parseString parser (readFile file)) of
    Sum.INR x => x
  | Sum.INL err => exit_fail err


(* ------------------------------------ *)

(* Helper functions *)


(* Parsing functions *)

val parse_certificate = parse_wrapper SimplexCertificate.certificate

(* Printing functions *)

val parsed_nat_to_string = Int.toString 

fun parsed_list_to_string sep elt_to_string lst =
  foldr (fn (x, acc) => x ^ sep ^ acc) "" (map elt_to_string lst)

fun parsed_rat_to_string (p, w, f) = 
  (if p then "" else "-") ^ 
  (parsed_list_to_string "" Int.toString w) ^ "." ^ 
  (parsed_list_to_string "" Int.toString f)

fun parsed_nat_triple_to_string sep (n1, n2, n3) = 
  (parsed_nat_to_string n1) ^ sep ^
  (parsed_nat_to_string n2) ^ sep ^
  (parsed_nat_to_string n3)

fun parsed_rat_triple_to_string sep (n1, n2, n3) = 
  (parsed_rat_to_string n1) ^ sep ^
  (parsed_rat_to_string n2) ^ sep ^
  (parsed_rat_to_string n3)

fun parsed_nat_list_map_to_string sep elt_to_string nat_map = 
  foldr (fn (x, acc) => x ^ sep ^ acc) "" 
  (map (fn (n, elt) => (parsed_nat_to_string n) ^ ": " ^ (elt_to_string elt)) nat_map)

fun parsed_config_to_string (header, b_set, matrix, var_data) = (
  "Config:\n" ^ 
  "Header:\n" ^ (parsed_nat_triple_to_string " " header) ^ "\n" ^
  "Basic set:\n" ^ (parsed_list_to_string " " parsed_nat_to_string b_set) ^ "\n" ^
  "Matrix:\n" ^ (parsed_nat_list_map_to_string "\n" 
    (parsed_nat_list_map_to_string " " parsed_rat_to_string) 
    matrix) ^ "\n" ^
  "Variable data:\n" ^ (parsed_nat_list_map_to_string "\n" 
    (parsed_rat_triple_to_string " ") var_data)
)

fun parsed_calc_rule_to_string (Pivot1 (i, j)) = 
    ("Pivot1 " ^ (parsed_nat_to_string i) ^ " " ^ (parsed_nat_to_string j))
  | parsed_calc_rule_to_string (Pivot2 (i, j)) = 
    ("Pivot2 " ^ (parsed_nat_to_string i) ^ " " ^ (parsed_nat_to_string j))
  | parsed_calc_rule_to_string (Update (j, delta)) = 
    ("Update " ^ (parsed_nat_to_string j) ^ " " ^ (parsed_rat_to_string delta))
  | parsed_calc_rule_to_string (PivotInBounds (i, j)) = 
    ("PivotInBounds " ^ (parsed_nat_to_string i) ^ " " ^ (parsed_nat_to_string j))
  | parsed_calc_rule_to_string (UpdateInBounds (j, delta)) = 
    ("UpdateInBounds " ^ (parsed_nat_to_string j) ^ " " ^ (parsed_rat_to_string delta))
  | parsed_calc_rule_to_string (Success) = "Success"
  | parsed_calc_rule_to_string (Failure) = "Failure"

fun parsed_calc_rule_list_to_string calc_rule_list = (
  "Calc rule list:\n" ^ 
  (parsed_list_to_string "\n" parsed_calc_rule_to_string calc_rule_list)
)

fun print_parsed_certificate (config, calc_rule_list) = 
  println ((parsed_config_to_string config) ^ "-----------\n" ^
  (parsed_calc_rule_list_to_string calc_rule_list))

(* ------------------------------------ *)

fun certificate_to_isabelle
  (((n_total, n_basic, n_non_basic), b_set, matrix, var_data), calc_rule_list) =
  let
    val n_total_isabelle = (nat_of_int n_total)
    val b_set_isabelle = 
      CertificateChecker.list_to_set (nat_list_to_isabelle b_set)
    val matrix_isabelle = 
      CertificateChecker.lists_to_mat (nat_rat_map_2d_list_to_isabelle matrix)
    val var_data_isabelle = 
      CertificateChecker.list_to_var_data (nat_rat_triple_map_list_to_isabelle var_data)
    val calc_rule_list_isabelle = (calc_rule_list_to_isabelle calc_rule_list)
  in
    ((CertificateChecker.Config (
      n_total_isabelle,
      b_set_isabelle,
      matrix_isabelle,
      var_data_isabelle)), 
    calc_rule_list_isabelle)
  end

(* TODO expand this with further printing *)
fun print_check_certificate_isabelle config_isabelle calc_rule_list_isabelle =
  case (CertificateChecker.check_config config_isabelle) of
    CertificateChecker.InvalidBSet err =>
      println ("Configuration invalid: Invalid b_set")
  | CertificateChecker.InvalidMatrix err =>
      println ("Configuration invalid: Invalid matrix")
  | CertificateChecker.InvalidVarData err =>
      println ("Configuration invalid: Invalid var_data")
  | CertificateChecker.Valida => 
      let
        val _ = (println "Configuration valid.")
      in
        case (CertificateChecker.check_certificate config_isabelle calc_rule_list_isabelle) of
          CertificateChecker.Valid => (println "Certificate valid.")
        | (CertificateChecker.InvalidPivot1 (err, n)) => 
            (println ("Certificate invalid: Invalid Pivot1 application, " ^ 
              (IntInf.toString (CertificateChecker.integer_of_nat n)) ^ " steps remaining"))
        | (CertificateChecker.InvalidPivot2 (err, n)) => 
            (println ("Certificate invalid: Invalid Pivot2 application, " ^ 
              (IntInf.toString (CertificateChecker.integer_of_nat n)) ^ " steps remaining"))
        | (CertificateChecker.InvalidPivotInBounds (err, n)) => 
            (println ("Certificate invalid: Invalid PivotInBounds application, " ^ 
              (IntInf.toString (CertificateChecker.integer_of_nat n)) ^ " steps remaining"))
        | (CertificateChecker.InvalidUpdate (err, n)) => 
            (println ("Certificate invalid: Invalid Update application, " ^ 
              (IntInf.toString (CertificateChecker.integer_of_nat n)) ^ " steps remaining"))
        | (CertificateChecker.InvalidUpdateInBounds (err, n)) => 
            (println ("Certificate invalid: Invalid UpdateInBounds application, " ^ 
              (IntInf.toString (CertificateChecker.integer_of_nat n)) ^ " steps remaining"))
        | (CertificateChecker.InvalidSuccess (err, n)) => 
            (println ("Certificate invalid: Invalid Success application, " ^ 
              (IntInf.toString (CertificateChecker.integer_of_nat n)) ^ " steps remaining"))
        | (CertificateChecker.InvalidFailure (err, n)) => 
            (println ("Certificate invalid: Invalid Failure application, " ^ 
              (IntInf.toString (CertificateChecker.integer_of_nat n)) ^ " steps remaining"))
        | (CertificateChecker.InvalidRule (rule, n)) => 
            (println ("Certificate invalid: Invalid rule application, " ^ 
              (IntInf.toString (CertificateChecker.integer_of_nat n)) ^ " steps remaining"))
      end



(* ------------------------------------ *)

val args = CommandLine.arguments()

fun print_help () = (
  println("c Usage: " ^ CommandLine.name() ^ " <certificate_file>")
)

(* Method call for printing: (print_parsed_certificate parsed_certificate) *)
val _ = case args of
  [certificate_file] => 
    let
      val _ = println ("Parsing and checking certificate in " ^ certificate_file ^ ":")
    in
      let
        val parsed_certificate = (parse_certificate certificate_file)
      in
        case (certificate_to_isabelle parsed_certificate) of 
          (config_isabelle, calc_rule_list_isabelle) => 
          (print_check_certificate_isabelle config_isabelle calc_rule_list_isabelle)
      end
    end
| _ => (
    println("Invalid command line arguments");
    print_help ();
    exit_fail ""
  )

val _ = OS.Process.exit(OS.Process.success)