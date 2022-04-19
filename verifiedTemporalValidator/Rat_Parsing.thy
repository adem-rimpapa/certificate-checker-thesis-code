theory Rat_Parsing
  imports TEMPORAL_PDDL_Checker
begin

text \<open>Attempt to prove correctness of @{const rat_of_digits_pair}\<close>

value "rat_of_digits_pair ([1,2,3,4],[1])"
value "rat_of_digits_pair ([1,2,3,4],[])"

text \<open>First I define a function to convert from a rational number to digit sequences.\<close>

(* (nom,denom) \<Rightarrow> (m,e) with: nom / denom = m * 10 ^ -e *)
text \<open>Function to extend the denominator of a fraction to a power of 10.\<close>
fun denom_to_pow10 :: "int \<times> int \<Rightarrow> int \<times> int" where
  "denom_to_pow10 (n,d) =
    (if d = 0 then (0,0)
    else if d = 1 then (n,0)
    else if d mod 10 = 0 then 
      let (m,e) = denom_to_pow10 (n,d div 10) in (m,e+1)
    else if d mod 2 = 0 then 
      let (m,e) = denom_to_pow10 (n,d div 2) in (m*5,e+1)
    else if d mod 5 = 0 then
      let (m,e) = denom_to_pow10 (n,d div 5) in (m*2,e+1)
    else (0,0))"

value "denom_to_pow10 (quotient_of 1.234)"

lemma denom_to_pow10_e_eq_z_iff:
  assumes "denom_to_pow10 (n,d::nat) = (m,e)" 
  shows "e = 0 \<longleftrightarrow> (d = 0 \<or> d = 1 \<or> (d mod 10 \<noteq> 0 \<and> d mod 2 \<noteq> 0 \<and> d mod 5 \<noteq> 0))"
  sorry

lemma denom_to_pow10_crossproduct:
  assumes "denom_to_pow10 (n,d::nat) = (m,e)" and "e \<noteq> 0"
  shows "n * (10^(nat e)) = m * d"
  using assms
  sorry

fun add_zs :: "int \<Rightarrow> digit list \<Rightarrow> digit list" where
  "add_zs i ds = (map (\<lambda>i. 0::nat) [0..<(nat i)]) @ ds"

text \<open>Convert from a rational number to digit sequences.\<close>
definition digits_pair_of_rat :: "rat \<Rightarrow> digit list \<times> digit list" where
  "digits_pair_of_rat r = (
    let (m,e) = denom_to_pow10 (quotient_of r);
      ds = digits_of_int m;
      ds' = add_zs (e - length ds) ds;
      i = nat (length ds' - e)
    in (take i ds', drop i ds')
  )"

(* Tests *)
value "digits_pair_of_rat (rat_of_digits_pair ([1,2,3,4],[0,2,0]))"
value "digits_pair_of_rat (rat_of_digits_pair ([],[0,1]))"
value "digits_pair_of_rat (rat_of_digits_pair ([0,1],[0,1]))"
value "digits_pair_of_rat (rat_of_digits_pair ([1],[]))"

(* A first attempt *)

lemma 
  assumes "wf_digits ds\<^sub>1" and "wf_digits ds\<^sub>2"                             
  shows "digits_pair_of_rat (rat_of_digits_pair' (ds\<^sub>1,ds\<^sub>2)) = (trim_ld_zs ds\<^sub>1, trim_tr_zs ds\<^sub>2)"
proof -
  obtain r where "r = rat_of_digits_pair' (ds\<^sub>1,ds\<^sub>2)"
    by auto
  obtain m e where "m = int_of_digits (ds\<^sub>1 @ ds\<^sub>2) 0" and "e = length ds\<^sub>2"
    by auto
  then have "(10::int) ^ e \<noteq> 0" and "r = Rat.Fract m (10 ^ e)"
    using \<open>r = rat_of_digits_pair' (ds\<^sub>1,ds\<^sub>2)\<close> by auto

  have "\<exists>a b. quotient_of r = (a,int b)"
    by (metis pairself.elims quotient_of_denom_pos zero_less_imp_eq_int)
  then obtain a b where "quotient_of r = (a,int b)"
    by auto
  then have "int b \<noteq> 0" and "(a,b) = Rat.normalize (m,(10 ^ e))"
    using \<open>r = Rat.Fract m (10 ^ e)\<close>
          quotient_of_denom_pos[OF \<open>quotient_of r = (a,int b)\<close>] 
          quotient_of_Fract 
    by auto
  have "Rat.normalize (a,b) = Rat.normalize (m,(10 ^ e))"
    using \<open>(a,b) = Rat.normalize (m,(10 ^ e))\<close>
    by (metis \<open>quotient_of r = (a, int b)\<close> \<open>r = Fract m (10 ^ e)\<close> normalize_eq quotient_of_Fract)
  then have "a * 10 ^ e = b * m"
    using normalize_crossproduct[OF \<open>int b \<noteq> 0\<close> \<open>(10::int) ^ e \<noteq> 0\<close>] by auto


  obtain m' e' where "denom_to_pow10 (a,b) = (m',e')"
    using denom_to_pow10.cases by blast
  have "e' \<noteq> 0"
    sorry
  have "a * (10^(nat e')) = b * m'"
    using denom_to_pow10_crossproduct[OF \<open>denom_to_pow10 (a,b) = (m',e')\<close> \<open>e' \<noteq> 0\<close>] by auto

  have "e = e'" and "m = m'"
    sorry

  have "digits_of_int m' = (trim_ld_zs ds\<^sub>1) @ (trim_tr_zs ds\<^sub>2)"
    sorry
  
  show ?thesis
    sorry
qed (* TODO: proof *)

lemma 
  assumes "wf_digits ds\<^sub>1" and "wf_digits ds\<^sub>2"                             
  shows "digits_pair_of_rat (rat_of_digits_pair (ds\<^sub>1,ds\<^sub>2)) = (trim_ld_zs ds\<^sub>1, trim_tr_zs ds\<^sub>2)"
proof -
  obtain r where "r = rat_of_digits_pair (ds\<^sub>1,ds\<^sub>2)"
    by auto

  obtain ds1' ds2' where "ds1' = trim_ld_zs ds\<^sub>1" and "ds2' = trim_tr_zs (ds\<^sub>2)"
    by auto

  obtain i where "i = int_of_digits (ds1' @ ds2') 0"
    by auto
  then have "r = Rat.Fract i (10 ^ length ds2')"
    using \<open>ds1' = trim_ld_zs ds\<^sub>1\<close> \<open>ds2' = trim_tr_zs (ds\<^sub>2)\<close> by (auto simp: Let_def)
  then have "quotient_of r = Rat.normalize (i,(10 ^ length ds2'))"
    using quotient_of_Fract by auto
  then obtain a b where "Rat.normalize (i,(10 ^ length ds2')) = (a,int b)"
    using denom_to_pow10.cases sorry
  then have "quotient_of r = (a,b)"
    using \<open>quotient_of r = Rat.normalize (i,(10 ^ length ds2'))\<close> by auto

  obtain e m where "denom_to_pow10 (quotient_of r) = (e,m)"
    using denom_to_pow10.cases by blast
  then have "denom_to_pow10 (a,b) = (e,m)"
    using \<open>quotient_of r = (a,b)\<close> by auto
  then have "a * (10^(nat e)) = m * b"
    sorry
  
  then have "denom_to_pow10 (quotient_of r) = (i,length ds2')"
    sorry

  have "wf_digits (ds1' @ ds2')"
    using \<open>ds1' = trim_ld_zs ds\<^sub>1\<close> 
          \<open>ds2' = trim_tr_zs (ds\<^sub>2)\<close> 
          trim_ld_zs_wf[OF \<open>wf_digits ds\<^sub>1\<close>] 
          trim_tr_zs_wf[OF \<open>wf_digits ds\<^sub>2\<close>] 
    by (auto simp: wf_digits_def)
  then have "digits_of_int i = trim_ld_zs (ds1' @ ds2')"
    using \<open>i = int_of_digits (ds1' @ ds2') 0\<close> 
          digits_of_int_int_of_digits 
    by auto
  then have "digits_of_int i = ds1' @ ds2'"
    using \<open>ds1' = trim_ld_zs ds\<^sub>1\<close> trim_ld_zs_idem

    trim_ld_zs_app
    apply (cases "ds1' = []")
    sorry

  have "digits_pair_of_rat r = 
       (take (nat (int (length (add_zs ((length ds2') - int (length (digits_of_int i))) (digits_of_int i))) - (length ds2'))) (add_zs ((length ds2') - int (length (digits_of_int i))) (digits_of_int i)),
        drop (nat (int (length (add_zs ((length ds2') - int (length (digits_of_int i))) (digits_of_int i))) - (length ds2'))) (add_zs ((length ds2') - int (length (digits_of_int i))) (digits_of_int i)))"
    by (metis (no_types, lifting) \<open>denom_to_pow10 (quotient_of r) = (i,length ds2')\<close> case_prod_conv digits_pair_of_rat_def)
  also have "... = (trim_ld_zs ds\<^sub>1, trim_tr_zs (ds\<^sub>2))"
    using \<open>digits_of_int i = ds1' @ ds2'\<close> 
          \<open>ds1' = trim_ld_zs ds\<^sub>1\<close> 
          \<open>ds2' = trim_tr_zs (ds\<^sub>2)\<close>
    by auto
  finally show ?thesis
    using \<open>r = rat_of_digits_pair (ds\<^sub>1,ds\<^sub>2)\<close> by auto
qed (* TODO: proof *)

text \<open>2. Attempt: recursive version of digits_pair_of_rat\<close>

(*fun right_shift_dec_pt :: "digit list \<times> digit list \<Rightarrow> digit list \<times> digit list" where
  "right_shift_dec_pt (ds\<^sub>1,ds\<^sub>2) = 
    (if ds\<^sub>1 = [] then ([], 0 # ds\<^sub>2) else (butlast ds\<^sub>1, last ds\<^sub>1 # ds\<^sub>2))"

value "right_shift_dec_pt ([],[1])"
value "right_shift_dec_pt ([1,2,3,4],[0,1])"

lemma 
  assumes "wf_digits ds\<^sub>1" and "wf_digits ds\<^sub>2"                             
  shows "(rat_of_digits_pair (ds\<^sub>1,ds\<^sub>2)) * (Rat.Fract 1 10) = rat_of_digits_pair (right_shift_dec_pt (ds\<^sub>1,ds\<^sub>2))"
proof -
  obtain r where "r = rat_of_digits_pair (ds\<^sub>1,ds\<^sub>2)"
    by auto

  have "ds\<^sub>1 = [] \<or> ds\<^sub>1 \<noteq> []" 
    by auto
  then show ?thesis
  proof
    assume "ds\<^sub>1 = []"
    then have "right_shift_dec_pt (ds\<^sub>1,ds\<^sub>2) = ([], 0#ds\<^sub>2)" and "trim_ld_zs [] = []"
      by auto

    have "ds\<^sub>2 = [] \<or> ds\<^sub>2 \<noteq> []"
      by auto
    then show ?thesis
    proof
      assume "ds\<^sub>2 = []"
      then have "rat_of_digits_pair (ds\<^sub>1,ds\<^sub>2) = 0" 
        using \<open>ds\<^sub>1 = []\<close> by (auto simp: Zero_rat_def)

      then have "rat_of_digits_pair (right_shift_dec_pt (ds\<^sub>1,ds\<^sub>2)) = 0"
        using \<open>ds\<^sub>1 = []\<close> \<open>ds\<^sub>2 = []\<close> by (auto simp: Let_def Zero_rat_def)
  
      then show ?thesis
        using \<open>rat_of_digits_pair (ds\<^sub>1,ds\<^sub>2) = 0\<close> by auto
    next
      assume "ds\<^sub>2 \<noteq> []"

      obtain ds\<^sub>2' where "ds\<^sub>2' = trim_tr_zs ds\<^sub>2"
        by auto
      then have "trim_tr_zs (0#ds\<^sub>2) = 0#ds\<^sub>2'"
        using \<open>ds\<^sub>2 \<noteq> []\<close> apply auto
        sorry

      have 1: "rat_of_digits_pair (ds\<^sub>1,ds\<^sub>2) = Rat.Fract (int_of_digits ds\<^sub>2' 0) (10 ^ length ds\<^sub>2')"
        using \<open>ds\<^sub>1 = []\<close> \<open>ds\<^sub>2' = trim_tr_zs ds\<^sub>2\<close> by (auto simp: Let_def)
      then have 2: "rat_of_digits_pair (ds\<^sub>1,ds\<^sub>2) * (Rat.Fract 1 10) = r * (Rat.Fract 1 10)"
        using \<open>r = rat_of_digits_pair (ds\<^sub>1,ds\<^sub>2)\<close> by (auto simp: Let_def)

      have 3: "rat_of_digits_pair (right_shift_dec_pt (ds\<^sub>1,ds\<^sub>2)) = r * (Rat.Fract 1 10)"
        using \<open>ds\<^sub>1 = []\<close> \<open>trim_tr_zs (0#ds\<^sub>2) = 0#ds\<^sub>2'\<close> 1 \<open>r = rat_of_digits_pair (ds\<^sub>1,ds\<^sub>2)\<close> 
        by (auto simp: power_commutes)

      show ?thesis
        using 2 3 by auto
    qed
  next
    assume "ds\<^sub>1 \<noteq> []"
    then have "right_shift_dec_pt (ds\<^sub>1,ds\<^sub>2) = (butlast ds\<^sub>1, last ds\<^sub>1 # ds\<^sub>2)"
      by auto

    have "ds\<^sub>2 = [] \<or> ds\<^sub>2 \<noteq> []"
      by auto
    then show ?thesis
    proof
      assume "ds\<^sub>2 = []"
      then show ?thesis
        sorry
    next
      assume "ds\<^sub>2 \<noteq> []"
      then show ?thesis
        sorry
    qed
  qed
qed

fun prim_fac_2_5 :: "nat \<Rightarrow> bool" where
  "prim_fac_2_5 i = (
    if i = 0 \<or> i = 1 then True
    else if i mod 2 = 0 then 
      prim_fac_2_5 (i div 2)
    else if i mod 5 = 0 then 
      prim_fac_2_5 (i div 5)
    else False)"

definition "finite_decimal r \<longleftrightarrow> (let (n,d) = r in prim_fac_2_5 (nat d))"

value "finite_decimal (1::int,8)"
value "finite_decimal (1::int,50)"
value "finite_decimal (1::int,30)"

function digits_pair_of_rat'_aux :: "int \<times> int \<Rightarrow> digit list \<times> digit list" where
  "digits_pair_of_rat'_aux (a,b) = (
    if a < 0 \<or> \<not>finite_decimal (a,b) then undefined
    else if a mod b = 0 then 
      (digits_of_int (a div b),[])
    else if a < b then 
      right_shift_dec_pt (digits_pair_of_rat'_aux (10*a,b))
    else
      let (ds\<^sub>1,ds\<^sub>2) = digits_pair_of_rat'_aux (a mod b,b) 
      in (digits_of_int (a div b) @ ds\<^sub>1,ds\<^sub>2)
  )"
by pat_completeness auto
termination 
  apply (relation "measure (\<lambda>(a,b). nat b div (10 * nat a) * ((nat a mod nat b) div nat b))")
  apply (auto simp: finite_decimal_def split: if_split)
  sorry

definition "digits_pair_of_rat' = digits_pair_of_rat'_aux o quotient_of"

value "digits_pair_of_rat' (1/8)"
value "digits_pair_of_rat' (1/1)"
value "digits_pair_of_rat' (1/2)"

value "digits_pair_of_rat' (rat_of_digits_pair ([1,2,3,4],[0,2,0]))"
value "digits_pair_of_rat' (rat_of_digits_pair ([],[0,1]))"
value "digits_pair_of_rat' (rat_of_digits_pair ([0,1],[0,1]))"
value "digits_pair_of_rat' (rat_of_digits_pair ([1],[]))"

lemma 
  assumes "wf_digits ds\<^sub>1" and "wf_digits ds\<^sub>2"                             
  shows "digits_pair_of_rat' (rat_of_digits_pair (ds\<^sub>1,ds\<^sub>2)) = (trim_ld_zs ds\<^sub>1, trim_tr_zs ds\<^sub>2)"
  unfolding digits_pair_of_rat'_def
  sorry*)




(* new attempt *)

(* rev ds\<^sub>2 *)
(*fun rat_of_digits_pair' :: "digit list \<times> digit list \<Rightarrow> rat" where
  "rat_of_digits_pair' ([],[]) = Rat.Fract 0 1"
| "rat_of_digits_pair' ([],d#ds\<^sub>2) = Rat.Fract d (10 ^ (length ds\<^sub>2 + 1)) + rat_of_digits_pair' ([],ds\<^sub>2)"
| "rat_of_digits_pair' (d#ds\<^sub>1,ds\<^sub>2) = Rat.Fract (d * 10 ^ (length ds\<^sub>1)) 1 + rat_of_digits_pair' (ds\<^sub>1,ds\<^sub>2)"

definition rat_of_digits_pair :: "digit list \<times> digit list \<Rightarrow> rat" where
  "rat_of_digits_pair dd = (case dd of (ds\<^sub>1,ds\<^sub>2) \<Rightarrow> rat_of_digits_pair' (ds\<^sub>1,rev ds\<^sub>2))"

value "rat_of_digits_pair ([],[1])" (* "1 / 10" :: "rat" *)
value "rat_of_digits_pair ([1,2,3,4],[1])" (* "12341 / 10" :: "rat" *)
value "rat_of_digits_pair ([1,2,3,4],[])" (* "1234" :: "rat" *)
value "rat_of_digits_pair ([1,2,3],[4])" (* "617 / 5" :: "rat" *)
value "rat_of_digits_pair ([1,2,3],[4,5,6])" (* "15432 / 125" :: "rat" *)


fun digits_pair_of_rat :: "digit list \<Rightarrow> nat \<Rightarrow> digit list \<times> digit list" where
  "digits_pair_of_rat ds m = (take (length ds - m) ds, drop (length ds - m) ds)"

text \<open>Function to extend the denominator of a fraction to a power of 10.\<close>
fun denom_to_pow10 :: "int \<times> int \<Rightarrow> int \<times> int" where
  "denom_to_pow10 (n,d) =
    (if d = 0 then (0,0)
    else if d = 1 then (n,0)
    else if d mod 10 = 0 then 
      let (m,e) = denom_to_pow10 (n,d div 10) in (m,e+1)
    else if d mod 2 = 0 then 
      let (m,e) = denom_to_pow10 (n,d div 2) in (m*5,e+1)
    else if d mod 5 = 0 then
      let (m,e) = denom_to_pow10 (n,d div 5) in (m*2,e+1)
    else (0,0))"

value "denom_to_pow10 (quotient_of 1.234)"*)

end
