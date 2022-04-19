(* This file defines the grammar for parsing simplex certificates. *)

(* Some utility functions. *)
fun println x = print (x ^ "\n")

fun exit_fail msg = (
  println msg;
  OS.Process.exit(OS.Process.failure)
)

structure SimplexCertificate =
(* An implementation that uses token parser. *)
struct

  open ParserCombinators
  open CharParser

  infixr 4 << >>
  infixr 3 &&
  infix  2 -- ##
  infix  2 wth suchthat return guard when
  infixr 1 || <|> ??

  structure CertificateDef :> LANGUAGE_DEF =
  struct

    type scanner = SubstringMonoStreamable.elem CharParser.charParser
    val commentStart   = NONE
    val commentEnd     = NONE
    val commentLine    = SOME ";"
    val nestedComments = false

    val identLetter    = alphaNum <|> oneOf (String.explode "_-,:;=") (*Idents can be separated with " " or \n and can contain [Aa-Zz], [0-9], "-", "_"*)
    val identStart     = identLetter
    val opStart        = fail "Operators not supported" : scanner
    val opLetter       = opStart
    val reservedNames  = []
    val reservedOpNames= []
    val caseSensitive  = false

  end

  val lineComment   =
  let fun comLine _  = newLine <|> done #"\n" <|> (anyChar >> $ comLine)
  in case CertificateDef.commentLine of
         SOME s => string s >> $ comLine return ()
       | NONE   => fail "Single-line comments not supported"
  end
  val mlComment      =
  case (CertificateDef.commentStart, CertificateDef.commentEnd) of
      (SOME st, SOME ed) =>
      let
    fun bcNest _   = try (string st) >> $contNest
    and contNest _ = try (string ed return ())
                                 <|> ($bcNest <|> (anyChar return ())) >> $contNest
    val bcU = try (string st) >> repeat (not (string ed) >> anyChar) >> string ed return ()
      in if CertificateDef.nestedComments then $ bcNest else bcU
      end
    | _ => fail "Multi-line comments not supported"
  val comment        = lineComment <|> mlComment



  fun fold_fn (x_opt, xs_opt) = 
    case xs_opt of 
      NONE => NONE
    | (SOME xs) => case x_opt of 
        NONE => NONE
      | (SOME x) => SOME (x::xs)

  fun char_list_to_int_list_opt chars =
    let
      val min_char = #"0"
      val max_char = #"9"
      val min_char_ord = Char.ord min_char
    in
      let
        val int_opt_list = 
          (map (fn c => if (c >= min_char andalso c <= max_char) 
          then (SOME ((Char.ord c) - min_char_ord)) else NONE) chars)
      in
        foldr (fold_fn) (SOME []) int_opt_list
      end
    end

  fun raw_rat_to_num ((pos, whole), frac) = 
    let
      val whole_opt = char_list_to_int_list_opt whole
      val frac_opt = char_list_to_int_list_opt frac
    in
      case (whole_opt, frac_opt) of 
        (SOME w, SOME f) => SOME (pos, w, f)
      | (SOME w, NONE) => NONE
      | (NONE, SOME f) => NONE
      | (NONE, NONE) => NONE
    end

  
  datatype CALC_RULE = 
    Pivot1 of (int * int)
  | Pivot2 of (int * int)
  | Update of (int * (bool * int list * int list))
  | PivotInBounds of (int * int)
  | UpdateInBounds of (int * (bool * int list * int list))
  | Success
  | Failure
  


  structure RTP = TokenParser (CertificateDef)
  open RTP

  val lparen = (char #"(" ) ?? "lparen"
  val rparen = (char #")" ) ?? "rparen"

  val spaces_comm = repeatSkip (space wth (fn _ => ())|| comment)

  fun in_paren p = spaces_comm >> lparen >> spaces_comm >> p << spaces_comm << rparen << spaces_comm

  (* Certificate grammar definitions *)

  val digits1 = repeat1 digit

  val raw_nat = lexeme digits1

  val num_nat = raw_nat when (fn chars => Int.fromString (String.implode chars))

  val raw_rat = lexeme (((((char #"-") && digits1) wth (fn (x, xs) => (false, xs))) || 
        (digits1 wth (fn xs => (true, xs)))) 
        && ( ((char #".") >> digits1) || ((string "") wth (fn _ => []))))

  val num_rat = raw_rat when raw_rat_to_num

  val nat_triple = (num_nat && num_nat && num_nat) wth (fn (n1, (n2, n3)) => (n1, n2, n3))

  val rat_triple = (num_rat && num_rat && num_rat) wth (fn (n1, (n2, n3)) => (n1, n2, n3))

  val nat_list = repeat num_nat

  fun nat_list_map x = repeat (in_paren ((num_nat << (string ": ")) && x))

  (* Configuration *)

  val config_header = (in_paren nat_triple)

  val config_b_set = (in_paren nat_list)

  val config_matrix = nat_list_map (nat_list_map num_rat)

  val config_var_data = nat_list_map rat_triple

  val lp_config = (config_header && config_b_set && config_matrix && config_var_data) wth
    (fn (h, (b, (m, v))) => (h, b, m, v))

  (* Calculus rules *)

  val operation_rule = (
    ((in_paren ((string "Pivot1 ") >> (num_nat && num_nat)))
      wth (fn (i, j) => Pivot1 (i, j))) ||
    ((in_paren ((string "Pivot2 ") >> (num_nat && num_nat)))
      wth (fn (i, j) => Pivot2 (i, j))) ||
    ((in_paren ((string "Update ") >> (num_nat && num_rat)))
      wth (fn (j, delta) => Update (j, delta))) ||
    ((in_paren ((string "PivotInBounds ") >> (num_nat && num_nat)))
      wth (fn (i, j) => PivotInBounds (i, j))) ||
    ((in_paren ((string "UpdateInBounds ") >> (num_nat && num_rat)))
      wth (fn (j, delta) => UpdateInBounds (j, delta)))
  )

  val final_rule = (
    ((in_paren (string "Success")) 
      wth (fn _ => Success)) ||
    ((in_paren (string "Failure")) 
      wth (fn _ => Failure))
  )

  val calc_rule_list = ((repeat operation_rule) && final_rule) wth 
    (fn (ops, final) => ops @ [final])

  (* Certificate *)

  val certificate = lp_config && calc_rule_list

end