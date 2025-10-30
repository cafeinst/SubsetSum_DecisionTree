theory SubsetSum_DecisionTree
  imports "Complex_Main" "HOL-Real_Asymp.Real_Asymp"
    "Weighted_Arithmetic_Geometric_Mean.Weighted_Arithmetic_Geometric_Mean"
begin

(* ========================================================================= *)
(* PART 1: Bitvectors and Subset-Sum Setup                                  *)
(* ========================================================================= *)

section \<open>0/1 integer vectors and bounded sums\<close>

text \<open>
  We represent selections by 0/1 integer vectors of a fixed length.
  For a list @{term "as :: int list"} and a 0/1 vector @{term "xs :: int list"},
  the subset-sum value is the dot product restricted to a set of indices.
\<close>

(* A bitvector of length k is a list of k elements from {0,1} *)
definition bitvec :: "nat \<Rightarrow> int list set" where
  "bitvec k = {xs. length xs = k \<and> set xs \<subseteq> {0::int, 1}}"

(* Basic lemmas about bitvectors: cardinality, finiteness, etc. *)
lemma bitvec_0[simp]: "bitvec 0 = {[]}"
  unfolding bitvec_def by auto

lemma sum_pow2_int: "(\<Sum> i<k. (2::int)^i) = 2^k - 1"
  by (induction k) simp_all

(* Bitvectors of length n+1 are exactly {0::xs} \<union> {1::xs} where xs has length n *)
lemma bitvec_Suc_partition:
  "bitvec (Suc n) =
     {0 # xs | xs. xs \<in> bitvec n} \<union> {1 # xs | xs. xs \<in> bitvec n}"
proof (rule subset_antisym)
  show "bitvec (Suc n) \<subseteq> {0 # xs | xs. xs \<in> bitvec n} \<union> {1 # xs | xs. xs \<in> bitvec n}"
  proof
    fix x assume x: "x \<in> bitvec (Suc n)"
    then obtain h t where HT: "x = h # t" and len: "length t = n"
      and sub: "set t \<subseteq> {0,1}"
      by (cases x) (auto simp: bitvec_def)
    from x HT have h01: "h = 0 \<or> h = 1"
      by (auto simp: bitvec_def)
    have t_in: "t \<in> bitvec n" using len sub by (simp add: bitvec_def)
    show "x \<in> {0 # xs | xs. xs \<in> bitvec n} \<union> {1 # xs | xs. xs \<in> bitvec n}"
      using HT h01 t_in by auto
  qed
next
  show "{0 # xs | xs. xs \<in> bitvec n} \<union> {1 # xs | xs. xs \<in> bitvec n} \<subseteq> bitvec (Suc n)"
  proof
    fix x assume "x \<in> {0 # xs | xs. xs \<in> bitvec n} \<union> {1 # xs | xs. xs \<in> bitvec n}"
    then show "x \<in> bitvec (Suc n)"
      by (auto simp: bitvec_def)
  qed
qed

(* The two halves of the partition are disjoint *)
lemma bitvec_Suc_disjoint:
  "{0 # xs | xs. xs \<in> bitvec n} \<inter> {1 # xs | xs. xs \<in> bitvec n} = {}"
  by auto

(* There are exactly 2^n bitvectors of length n *)
lemma finite_bitvec[simp]: "finite (bitvec n)"
proof (induction n)
  case 0
  show ?case by (simp add: bitvec_def)
next
  case (Suc n)
  have part: "bitvec (Suc n) =
        {0 # xs | xs. xs \<in> bitvec n} \<union> {1 # xs | xs. xs \<in> bitvec n}"
    by (rule bitvec_Suc_partition)
  have eq0: "{0 # xs | xs. xs \<in> bitvec n} = (\<lambda>xs. 0 # xs) ` bitvec n" by auto
  have eq1: "{1 # xs | xs. xs \<in> bitvec n} = (\<lambda>xs. 1 # xs) ` bitvec n" by auto
  have fin0: "finite {0 # xs | xs. xs \<in> bitvec n}"
    unfolding eq0 by (intro finite_imageI Suc.IH)
  have fin1: "finite {1 # xs | xs. xs \<in> bitvec n}"
    unfolding eq1 by (intro finite_imageI Suc.IH)
  show ?case by (simp add: part fin0 fin1)
qed

lemma card_bitvec: "card (bitvec n) = 2 ^ n"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have part: "bitvec (Suc n) =
        {0 # xs | xs. xs \<in> bitvec n} \<union> {1 # xs | xs. xs \<in> bitvec n}"
    by (rule bitvec_Suc_partition)
  have disj: "{0 # xs | xs. xs \<in> bitvec n} \<inter> {1 # xs | xs. xs \<in> bitvec n} = {}"
    by (rule bitvec_Suc_disjoint)
  have eq0: "{0 # xs | xs. xs \<in> bitvec n} = (\<lambda>xs. 0 # xs) ` bitvec n" by auto
  have eq1: "{1 # xs | xs. xs \<in> bitvec n} = (\<lambda>xs. 1 # xs) ` bitvec n" by auto
  have "card (bitvec (Suc n))
      = card {0 # xs | xs. xs \<in> bitvec n} + card {1 # xs | xs. xs \<in> bitvec n}"
    by (simp add: part disj card_Un_disjoint)
  also have "\<dots> = card ((\<lambda>xs. 0 # xs) ` bitvec n) + card ((\<lambda>xs. 1 # xs) ` bitvec n)"
    by (simp add: eq0 eq1)
  also have "\<dots> = card (bitvec n) + card (bitvec n)"
    by (simp add: card_image)
  also have "\<dots> = 2 ^ n + 2 ^ n" using Suc.IH by simp
  also have "\<dots> = 2 ^ Suc n" by simp
  finally show ?case .
qed

(* ========================================================================= *)
(* PART 2: The Split Function e_k and LHS/RHS Sets                          *)
(* ========================================================================= *)

(* Sum of as[i] * xs[i] over index set I *)
definition sum_as_on :: "int list \<Rightarrow> nat set \<Rightarrow> int list \<Rightarrow> int" where
  "sum_as_on as I xs = (\<Sum> i \<in> I. as ! i * xs ! i)"

(* Left-hand side: sum over first k indices *)
definition lhs_of :: "int list \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int" where
  "lhs_of as k xs = sum_as_on as {0..<k} xs"

(* Right-hand side: target s minus sum over indices k..n *)
definition rhs_of :: "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int" where
  "rhs_of as k s xs = s - sum_as_on as {k..<length as} xs"

(* THE KEY SPLIT FUNCTION:
   e_k maps each bitvector xs to a pair (L, R) where:
   - L is the sum of the first k weights times their selections
   - R is what remains of the target after subtracting the last (n-k) weights
   
   This splits the subset-sum problem into two independent subproblems! *)
definition e_k :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int \<times> int" where
  "e_k as s k xs = (lhs_of as k xs, rhs_of as k s xs)"

(* LHS: the set of all possible left-hand-side values *)
definition LHS :: "(int list \<Rightarrow> int \<times> int) \<Rightarrow> nat \<Rightarrow> int set" where
  "LHS e n = {fst (e xs) | xs. xs \<in> bitvec n}"

(* RHS: the set of all possible right-hand-side values *)
definition RHS :: "(int list \<Rightarrow> int \<times> int) \<Rightarrow> nat \<Rightarrow> int set" where
  "RHS e n = {snd (e xs) | xs. xs \<in> bitvec n}"

(* ========================================================================= *)
(* PART 3: Distinct Subset Sums Property                                    *)
(* ========================================================================= *)

section \<open>Distinct-subset-sums (full length)\<close>

text \<open>
  CRITICAL PROPERTY: A weight list has "distinct subset sums" if different
  0/1 selections always produce different total sums. This is key because
  it makes the split function e_k INJECTIVE on both halves.
\<close>

text \<open>
  Distinct subset sums: different 0/1 n-vectors yield different total sums.
\<close>
definition distinct_subset_sums :: "int list \<Rightarrow> bool" where
  "distinct_subset_sums as \<equiv>
     (\<forall>xs\<in>bitvec (length as). \<forall>ys\<in>bitvec (length as).
        xs \<noteq> ys \<longrightarrow> (\<Sum> i < length as. as ! i * xs ! i) \<noteq> (\<Sum> i < length as. as ! i * ys ! i))"

(* ========================================================================= *)
(* PART 4: Padding Lemmas (Technical Machinery)                             *)
(* ========================================================================= *)

section \<open>Padding lemmas for prefix/suffix reasoning\<close>

(* These lemmas let us extend/restrict bitvectors with zeros while preserving
   the prefix or suffix properties we care about. Used to show that:
   - LHS values come from first k positions (pad with zeros after)
   - RHS values come from last (n-k) positions (pad with zeros before) *)
lemma pad_suffix_zeros_in_bitvec:
  assumes "p \<in> bitvec k" "n \<ge> k"
  shows "p @ replicate (n - k) 0 \<in> bitvec n"
  using assms by (auto simp: bitvec_def)

lemma pad_prefix_zeros_in_bitvec:
  assumes "q \<in> bitvec (n - k)" "k \<le> n"
  shows "(replicate k 0) @ q \<in> bitvec n"
  using assms by (auto simp: bitvec_def)

lemma drop_in_bitvec:
  assumes "xs \<in> bitvec n" "k \<le> n"
  shows   "drop k xs \<in> bitvec (n - k)"
proof -
  have len: "length xs = n" and xs01: "set xs \<subseteq> {0,1}"
    using assms(1) by (auto simp: bitvec_def)
  have "length (drop k xs) = n - k"
    using assms(2) len by simp
  moreover have "set (drop k xs) \<subseteq> {0,1}"
    using xs01 by (auto dest: in_set_dropD)
  ultimately show ?thesis by (simp add: bitvec_def)
qed

lemma sum_as_on_prefix_pad:
  assumes "xs \<in> bitvec n" "k \<le> n"
  shows "sum_as_on as {0..<k} xs =
         sum_as_on as {0..<k} (take k xs @ replicate (n - k) 0)"
  using assms
  by (simp add: sum_as_on_def bitvec_def atLeast0LessThan less_diff_conv nth_append min_def)

lemma sum_reindex_add:
  fixes k n :: nat
  shows "(\<Sum> i \<in> {k..<n}. g i) = (\<Sum> j \<in> {0..<n - k}. g (k + j))"
proof -
  have inj: "inj_on ((+) k) {0..<n - k}" by auto
  have E: "sum g ((+) k ` {0..<n - k}) = sum (g \<circ> ((+) k)) {0..<n - k}"
    by (rule sum.reindex[OF inj])
  have F: "sum (g \<circ> ((+) k)) {0..<n - k} = (\<Sum> j = 0..<n - k. g (k + j))"
    by (simp add: o_def)
  from E F show ?thesis by (metis sum.atLeastLessThan_shift_0)
qed

lemma sum_as_on_suffix_pad_shift:
  assumes lenq: "length q = n - k" and kn: "k \<le> n"
  shows
    "sum_as_on as {k..<n} ((replicate k 0) @ q)
     = (\<Sum> j \<in> {0..<n - k}. as ! (k + j) * q ! j)"
proof -
  have A: "\<And>i. i \<in> {k..<n} \<Longrightarrow> ((replicate k 0) @ q) ! i = q ! (i - k)"
    using lenq by (auto simp: nth_append)

  have "sum_as_on as {k..<n} ((replicate k 0) @ q)
        = (\<Sum> i \<in> {k..<n}. as ! i * ((replicate k 0) @ q) ! i)"
    by (simp add: sum_as_on_def)
  also have "\<dots> = (\<Sum> i \<in> {k..<n}. as ! i * q ! (i - k))"
    by (simp add: A)
  also have "\<dots> = (\<Sum> j \<in> {0..<n - k}. as ! (k + j) * q ! ((k + j) - k))"
    by (subst sum_reindex_add) simp
  also have "\<dots> = (\<Sum> j \<in> {0..<n - k}. as ! (k + j) * q ! j)"
    by simp
  finally show ?thesis .
qed

lemma sum_as_on_suffix_drop_shift:
  assumes xs: "xs \<in> bitvec n" and kn: "k \<le> n"
  shows "sum_as_on as {k..<n} xs
       = (\<Sum> j\<in>{0..<n - k}. as ! (k + j) * (drop k xs) ! j)"
proof -
  have lenxs: "length xs = n" using xs by (simp add: bitvec_def)
  have "sum_as_on as {k..<n} xs = (\<Sum> i\<in>{k..<n}. as ! i * xs ! i)"
    by (simp add: sum_as_on_def)
  also have "\<dots> = (\<Sum> i\<in>{k..<n}. as ! i * (drop k xs) ! (i - k))"
  proof (rule sum.cong[OF refl])
    fix i assume "i \<in> {k..<n}"
    with lenxs kn show "as ! i * xs ! i = as ! i * (drop k xs) ! (i - k)"
      by simp
  qed
  also have "\<dots> = (\<Sum> j\<in>{0..<n - k}. as ! (k + j) * (drop k xs) ! j)"
    by (subst sum_reindex_add) simp
  finally show ?thesis .
qed

lemma take_in_bitvec:
  assumes "xs \<in> bitvec n" "k \<le> n"
  shows   "take k xs \<in> bitvec k"
proof -
  have "length (take k xs) = k" using assms by (simp add: bitvec_def)
  moreover have "set (take k xs) \<subseteq> {0,1}"
    using assms by (auto simp: bitvec_def dest!: in_set_takeD)
  ultimately show ?thesis by (simp add: bitvec_def)
qed

(* padded tail entries are 0 for indices i \<in> {k..<n} *)
lemma padded_tail_zero:
  assumes "length p = k" and "i \<in> {k..<n}"
  shows   "(p @ replicate (n - k) (0::int)) ! i = 0"
proof -
  have ik: "k \<le> i" and in_lt: "i < n" using assms(2) by auto
  have "(p @ replicate (n - k) (0::int)) ! i = (replicate (n - k) (0::int)) ! (i - k)"
    using assms(1) ik by (simp add: nth_append)
  moreover have "i - k < n - k" using in_lt ik by arith
  ultimately show ?thesis by simp
qed

(* ========================================================================= *)
(* PART 5: THE MAIN COUNTING THEOREMS (Lemma 2)                            *)
(* ========================================================================= *)

(* THEOREM: If weights have distinct subset sums, then |LHS| = 2^k *)
lemma card_LHS_e_k:
  fixes as :: "int list" and s :: int and n k :: nat
  assumes n_def: "n = length as" and k_le: "k \<le> n"
      and distinct: "distinct_subset_sums as"
  shows "card (LHS (e_k as s k) n) = 2 ^ k"
proof -
  let ?pref = "bitvec k"
  define f where "f p = sum_as_on as {0..<k} (p @ replicate (n - k) (0::int))" for p

  (* Every LHS value arises from some prefix p. *)
  have LHS_subset: "LHS (e_k as s k) n \<subseteq> f ` ?pref"
  proof
    fix v assume "v \<in> LHS (e_k as s k) n"
    then obtain xs where xs: "xs \<in> bitvec n" and v: "v = fst (e_k as s k xs)"
      by (auto simp: LHS_def)
    define p where "p = take k xs"
    have p_in: "p \<in> ?pref" using xs k_le by (simp add: p_def take_in_bitvec)
    have "v = sum_as_on as {0..<k} xs"
      by (simp add: v e_k_def lhs_of_def sum_as_on_def)
    also have "\<dots> = sum_as_on as {0..<k} (p @ replicate (n - k) (0::int))"
      using xs k_le by (simp add: p_def sum_as_on_prefix_pad n_def)
    finally have "v = f p" by (simp add: f_def)
    thus "v \<in> f ` ?pref" using p_in by blast
  qed

  (* Every prefix p gives a realizable LHS value. *)
  have subset_LHS: "f ` ?pref \<subseteq> LHS (e_k as s k) n"
  proof
    fix v assume "v \<in> f ` ?pref"
    then obtain p where p: "p \<in> ?pref" and v: "v = f p" by blast
    have xs_in: "p @ replicate (n - k) (0::int) \<in> bitvec n"
      using p k_le by (rule pad_suffix_zeros_in_bitvec)
    have "v = sum_as_on as {0..<k} (p @ replicate (n - k) (0::int))"
      by (simp add: v f_def)
    hence "v = fst (e_k as s k (p @ replicate (n - k) (0::int)))"
      by (simp add: e_k_def lhs_of_def)
    thus "v \<in> LHS (e_k as s k) n"
      using xs_in by (auto simp: LHS_def)
  qed

  have LHS_eq_img: "LHS (e_k as s k) n = f ` ?pref"
    using LHS_subset subset_LHS by blast

  (* Injectivity on prefixes by padding with zeros and using distinct sums. *)
  have inj_f: "inj_on f ?pref"
  proof (rule inj_onI)
    fix p1 p2 assume p1: "p1 \<in> ?pref" and p2: "p2 \<in> ?pref" and eq: "f p1 = f p2"
    have lenp1: "length p1 = k" using p1 by (simp add: bitvec_def)
    have lenp2: "length p2 = k" using p2 by (simp add: bitvec_def)

    have pref_eq:
      "sum_as_on as {0..<k} (p1 @ replicate (n - k) (0::int))
       = sum_as_on as {0..<k} (p2 @ replicate (n - k) (0::int))"
      using eq by (simp add: f_def)

    (* --- split the big sums and finish the equality --- *)
    let ?x1 = "p1 @ replicate (n - k) (0::int)"
    let ?x2 = "p2 @ replicate (n - k) (0::int)"
    let ?F1 = "(\<lambda>i. as ! i * ?x1 ! i)"
    let ?F2 = "(\<lambda>i. as ! i * ?x2 ! i)"

    have fin1: "finite ({0..<k}::nat set)" by simp
    have fin2: "finite ({k..<n}::nat set)" by simp
    have disj: "{0..<k} \<inter> {k..<n} = ({}::nat set)" by auto
    have un:   "{0..<k} \<union> {k..<n} = {0..<n}" using k_le by auto

    have split1:
      "(\<Sum>i\<in>{0..<n}. ?F1 i)
      = (\<Sum>i\<in>{0..<k}. ?F1 i) + (\<Sum>i\<in>{k..<n}. ?F1 i)"
      by (subst un[symmetric], rule sum.union_disjoint[OF fin1 fin2], simp_all add: disj)

    have split2:
      "(\<Sum>i\<in>{0..<n}. ?F2 i)
        = (\<Sum>i\<in>{0..<k}. ?F2 i) + (\<Sum>i\<in>{k..<n}. ?F2 i)"
      by (subst un[symmetric], rule sum.union_disjoint[OF fin1 fin2], simp_all add: disj)

(* tails are zero because padded tail entries are 0 *)
    have tail1:
      "(\<Sum>i\<in>{k..<n}. as ! i * (p1 @ replicate (n - k) (0::int)) ! i) = 0"
      by (rule sum.neutral, intro ballI, simp add: padded_tail_zero[OF lenp1])

    have tail2:
      "(\<Sum>i\<in>{k..<n}. as ! i * (p2 @ replicate (n - k) (0::int)) ! i) = 0"
      by (rule sum.neutral, intro ballI, simp add: padded_tail_zero[OF lenp2])

(* prefixes equal via your pref_eq *)
    have pref1: "(\<Sum>i\<in>{0..<k}. ?F1 i) = sum_as_on as {0..<k} ?x1"
      by (simp add: sum_as_on_def)
    have pref2: "(\<Sum>i\<in>{0..<k}. ?F2 i) = sum_as_on as {0..<k} ?x2"
      by (simp add: sum_as_on_def)

    have full_eq_set:
    "(\<Sum>i\<in>{0..<n}. ?F1 i) = (\<Sum>i\<in>{0..<n}. ?F2 i)"
    using pref_eq tail1 tail2 by (simp add: split1 split2 pref1 pref2)

(* if you need the < n binder form *)
    have full_eq:
    "(\<Sum> i < n. as ! i * ?x1 ! i) = (\<Sum> i < n. as ! i * ?x2 ! i)"
    using full_eq_set by (simp add: atLeast0LessThan)

    have xs1: "?x1 \<in> bitvec n" using p1 k_le by (rule pad_suffix_zeros_in_bitvec)
    have xs2: "?x2 \<in> bitvec n" using p2 k_le by (rule pad_suffix_zeros_in_bitvec)

    from full_eq xs1 xs2 distinct n_def
    have "?x1 = ?x2"
      unfolding distinct_subset_sums_def by auto
    thus "p1 = p2" by simp
  qed

  have "card (LHS (e_k as s k) n) = card (f ` ?pref)"
    by (simp add: LHS_eq_img)
  also have "\<dots> = card ?pref" by (rule card_image; use inj_f in auto)
  also have "\<dots> = 2 ^ k" by (rule card_bitvec)
  finally show ?thesis .
qed

(* THEOREM: If weights have distinct subset sums, then |RHS| = 2^(n-k) *)
lemma card_RHS_e_k:
  fixes as :: "int list" and s :: int and n k :: nat
  assumes n_def: "n = length as" and k_le: "k \<le> n"
      and distinct: "distinct_subset_sums as"
  shows "card (RHS (e_k as s k) n) = 2 ^ (n - k)"
proof -
  let ?suf = "bitvec (n - k)"
  define g where "g q = s - sum_as_on as {k..<n} ((replicate k (0::int)) @ q)" for q

  (* Every RHS value arises from some suffix q. *)
  have RHS_subset: "RHS (e_k as s k) n \<subseteq> g ` ?suf"
  proof
    fix v assume "v \<in> RHS (e_k as s k) n"
    then obtain xs where xs: "xs \<in> bitvec n" and vdef: "v = snd (e_k as s k xs)"
      by (auto simp: RHS_def)

    define q where "q = drop k xs"
    have q_in: "q \<in> bitvec (n - k)"
      by (simp add: q_def drop_in_bitvec[OF xs k_le])
    have q_len: "length q = n - k"
      using q_in by (simp add: bitvec_def)

  (* rewrite the xs-tail and the padded-tail to the same shifted sum *)
    have xs_tail:
      "sum_as_on as {k..<n} xs
      = (\<Sum> j\<in>{0..<n - k}. as ! (k + j) * q ! j)"
      by (simp add: q_def sum_as_on_suffix_drop_shift[OF xs k_le])
    have pad_tail:
      "sum_as_on as {k..<n} ((replicate k (0::int)) @ q)
      = (\<Sum> j\<in>{0..<n - k}. as ! (k + j) * q ! j)"
      using sum_as_on_suffix_pad_shift[OF q_len k_le] by simp

    have "v = s - sum_as_on as {k..<n} xs"
      by (simp add: vdef e_k_def rhs_of_def sum_as_on_def n_def)
    also have "... = s - (\<Sum> j\<in>{0..<n - k}. as ! (k + j) * q ! j)"
      by (simp add: xs_tail)
    also have "... = s - sum_as_on as {k..<n} ((replicate k 0) @ q)"
      by (simp add: pad_tail)
    finally have "v = g q" by (simp add: g_def)

    thus "v \<in> g ` ?suf" using q_in by blast
  qed

  (* Every suffix q gives a realizable RHS value. *)
  have subset_RHS: "g ` ?suf \<subseteq> RHS (e_k as s k) n"
  proof
    fix v assume "v \<in> g ` ?suf"
    then obtain q where q: "q \<in> ?suf" and v: "v = g q" by blast
    have xs_in: "(replicate k (0::int)) @ q \<in> bitvec n"
      using q k_le by (rule pad_prefix_zeros_in_bitvec)
    have "v = s - sum_as_on as {k..<n} ((replicate k (0::int)) @ q)"
      by (simp add: v g_def)
    hence "v = snd (e_k as s k ((replicate k (0::int)) @ q))"
      by (simp add: e_k_def rhs_of_def sum_as_on_def n_def)
    thus "v \<in> RHS (e_k as s k) n"
      using xs_in by (auto simp: RHS_def)
  qed

  have RHS_eq_img: "RHS (e_k as s k) n = g ` ?suf"
    using RHS_subset subset_RHS by blast

  (* Injectivity on suffixes by padding with zeros and using distinct sums. *)
  have inj_g: "inj_on g ?suf"
  proof (rule inj_onI)
    fix q1 q2 assume q1: "q1 \<in> ?suf" and q2: "q2 \<in> ?suf" and eq: "g q1 = g q2"
    have xs1: "(replicate k (0::int)) @ q1 \<in> bitvec n"
      using q1 k_le by (rule pad_prefix_zeros_in_bitvec)
    have xs2: "(replicate k (0::int)) @ q2 \<in> bitvec n"
      using q2 k_le by (rule pad_prefix_zeros_in_bitvec)

  (* from g q1 = g q2, tails are equal *)
    from eq have tails_eq:
      "sum_as_on as {k..<n} ((replicate k 0) @ q1)
      = sum_as_on as {k..<n} ((replicate k 0) @ q2)"
      by (simp add: g_def)

  (* --- turn tail equality into full-sum equality --- *)
    let ?x1 = "(replicate k (0::int)) @ q1"
    let ?x2 = "(replicate k (0::int)) @ q2"
    let ?F1 = "(\<lambda>i. as ! i * ?x1 ! i)"
    let ?F2 = "(\<lambda>i. as ! i * ?x2 ! i)"

    have fin1: "finite ({0..<k}::nat set)" by simp
    have fin2: "finite ({k..<n}::nat set)" by simp
    have disj: "{0..<k} \<inter> {k..<n} = ({}::nat set)" by auto
    have un:   "{0..<k} \<union> {k..<n} = {0..<n}" using k_le by auto

    have split1:
      "(\<Sum>i\<in>{0..<n}. ?F1 i)
      = (\<Sum>i\<in>{0..<k}. ?F1 i) + (\<Sum>i\<in>{k..<n}. ?F1 i)"
      by (subst un[symmetric], rule sum.union_disjoint[OF fin1 fin2], simp_all add: disj)
    have split2:
      "(\<Sum>i\<in>{0..<n}. ?F2 i)
      = (\<Sum>i\<in>{0..<k}. ?F2 i) + (\<Sum>i\<in>{k..<n}. ?F2 i)"
      by (subst un[symmetric], rule sum.union_disjoint[OF fin1 fin2], simp_all add: disj)

  (* prefixes are 0: the first k entries are the replicated zeros *)
    have pref1: "(\<Sum>i\<in>{0..<k}. ?F1 i) = 0" by (simp add: nth_append)
    have pref2: "(\<Sum>i\<in>{0..<k}. ?F2 i) = 0" by (simp add: nth_append)

  (* tails equal, rewrite via sum_as_on_def / n_def *)
    have tails_eq_set:
    "(\<Sum>i\<in>{k..<n}. ?F1 i) = (\<Sum>i\<in>{k..<n}. ?F2 i)"
      using tails_eq by (simp add: sum_as_on_def n_def atLeast0LessThan)

    have full_eq_set:
      "(\<Sum>i\<in>{0..<n}. ?F1 i) = (\<Sum>i\<in>{0..<n}. ?F2 i)"
      by (simp add: split1 split2 pref1 pref2 tails_eq_set)

    have full_eq:
      "(\<Sum> i < n. as ! i * ?x1 ! i) = (\<Sum> i < n. as ! i * ?x2 ! i)"
      using full_eq_set by (simp add: atLeast0LessThan)

(* Make the “distinct subset sums” assumption into an injectivity fact *)
    have inj_sum:
      "inj_on (\<lambda>xs. (\<Sum>i < n. as ! i * xs ! i)) (bitvec n)"
      using distinct
      unfolding distinct_subset_sums_def n_def
      by (intro inj_onI) (auto simp: atLeast0LessThan)

(* Apply injectivity to the two padded vectors *)
    have "?x1 = ?x2"
      using inj_sum xs1 xs2 full_eq
      by (force simp: inj_on_def)

(* Cancel the common prefix *)
    then have "q1 = q2" by simp
    thus "q1 = q2" .
  qed

  have "card (RHS (e_k as s k) n) = card (g ` ?suf)"
    by (simp add: RHS_eq_img)
  also have "\<dots> = card ?suf" by (rule card_image; use inj_g in auto)
  also have "\<dots> = 2 ^ (n - k)" by (simp add: card_bitvec)
  finally show ?thesis .
qed

(* COROLLARY: The product |LHS| \<times> |RHS| = 2^n *)
theorem lemma2_split:
  fixes as :: "int list" and s :: int and n k :: nat
  assumes n_def: "n = length as" and k_le: "k \<le> n"
      and distinct: "distinct_subset_sums as"
  shows "card (LHS (e_k as s k) n) * card (RHS (e_k as s k) n) = 2 ^ n"
proof -
  have L: "card (LHS (e_k as s k) n) = 2 ^ k"
    by (rule card_LHS_e_k[OF n_def k_le distinct])
  have R: "card (RHS (e_k as s k) n) = 2 ^ (n - k)"
    by (rule card_RHS_e_k[OF n_def k_le distinct])
  have kn: "k + (n - k) = n" using k_le by simp
  from L R show ?thesis
    by (simp add: power_add[symmetric] kn)
qed

(* ========================================================================= *)
(* PART 6: AM-GM Lower Bound (Lemma 3)                                      *)
(* ========================================================================= *)

(* THEOREM: If A \<times> B \<ge> 2^n, then A + B \<ge> 2\<surd>(2^n) by AM-GM inequality *)
lemma lemma3_AFP:
  fixes A B :: real and n :: nat
  assumes A0: "A \<ge> 0" and B0: "B \<ge> 0"
      and ABge: "A * B \<ge> (2::real) ^ n"
  shows "A + B \<ge> 2 * sqrt ((2::real) ^ n)"
proof -
  (* AM–GM from AFP/Analysis *)
  have amgm: "2 * sqrt (A * B) \<le> A + B"
    using A0 B0 arithmetic_geometric_mean_binary by force
  (* sqrt is monotone on \<real>\<ge>0 *)
  have "sqrt ((2::real) ^ n) \<le> sqrt (A * B)"
    using ABge A0 B0 by simp
  hence "2 * sqrt ((2::real) ^ n) \<le> 2 * sqrt (A * B)" by simp
  with amgm show ?thesis by linarith
qed

(* COROLLARY: For distinct subset sums, |LHS| + |RHS| \<ge> 2\<surd>(2^n) *)
corollary lhs_rhs_sum_lower_bound:
  fixes as :: "int list" and s :: int and n k :: nat
  assumes n_def: "n = length as" and k_le: "k \<le> n" and distinct: "distinct_subset_sums as"
  shows "real (card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n))
         \<ge> 2 * sqrt ((2::real) ^ n)"
proof -
  have prod_eq_nat:
    "card (LHS (e_k as s k) n) * card (RHS (e_k as s k) n) = 2 ^ n"
    by (rule lemma2_split[OF n_def k_le distinct])

(* same product in \<real> *)
  have prod_eq_real:
    "real (card (LHS (e_k as s k) n)) * real (card (RHS (e_k as s k) n))
    = (2::real) ^ n"
    using prod_eq_nat
    by (metis numeral_power_eq_of_nat_cancel_iff of_nat_mult)

  have prod_ge:
    "(2::real) ^ n \<le> real (card (LHS (e_k as s k) n)) * real (card (RHS (e_k as s k) n))"
    by (simp add: prod_eq_real)

  have A0: "0 \<le> real (card (LHS (e_k as s k) n))" by simp
  have B0: "0 \<le> real (card (RHS (e_k as s k) n))" by simp

  from lemma3_AFP[OF A0 B0 prod_ge]
  show "real (card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n))
      \<ge> 2 * sqrt ((2::real) ^ n)"
  by simp
qed

(* ========================================================================= *)
(* PART 7: Decision Tree Model (Lemma 1 Framework)                          *)
(* ========================================================================= *)

section \<open>Decision-tree reader model and coverage (Lemma 1)\<close>

(* A decision tree that can query left-oracle at indices iL and 
   right-oracle at indices iR *)
datatype ('iL,'iR) dtr =
    Leaf bool
  | AskL 'iL "('iL,'iR) dtr" "('iL,'iR) dtr"
  | AskR 'iR "('iL,'iR) dtr" "('iL,'iR) dtr"

(* Run the tree with two oracles oL and oR *)
fun run :: "('iL \<Rightarrow> bool) \<Rightarrow> ('iR \<Rightarrow> bool) \<Rightarrow> ('iL,'iR) dtr \<Rightarrow> bool" where
  "run oL oR (Leaf b) = b"
| "run oL oR (AskL i t0 t1) = run oL oR (if oL i then t1 else t0)"
| "run oL oR (AskR j t0 t1) = run oL oR (if oR j then t1 else t0)"

(* Track which left-indices were queried during the run *)
fun seenL_run :: "('iL \<Rightarrow> bool) \<Rightarrow> ('iR \<Rightarrow> bool) \<Rightarrow> ('iL,'iR) dtr \<Rightarrow> 'iL set" where
  "seenL_run oL oR (Leaf b) = {}"
| "seenL_run oL oR (AskL i t0 t1) =
     insert i (seenL_run oL oR (if oL i then t1 else t0))"
| "seenL_run oL oR (AskR j t0 t1) =
     seenL_run oL oR (if oR j then t1 else t0)"

(* Track which right-indices were queried *)
fun seenR_run :: "('iL \<Rightarrow> bool) \<Rightarrow> ('iR \<Rightarrow> bool) \<Rightarrow> ('iL,'iR) dtr \<Rightarrow> 'iR set" where
  "seenR_run oL oR (Leaf b) = {}"
| "seenR_run oL oR (AskL i t0 t1) =
     seenR_run oL oR (if oL i then t1 else t0)"
| "seenR_run oL oR (AskR j t0 t1) =
     insert j (seenR_run oL oR (if oR j then t1 else t0))"

(* Count the number of queries made *)
fun steps_run :: "('iL \<Rightarrow> bool) \<Rightarrow> ('iR \<Rightarrow> bool) \<Rightarrow> ('iL,'iR) dtr \<Rightarrow> nat" where
  "steps_run oL oR (Leaf b) = 0"
| "steps_run oL oR (AskL i t0 t1) =
     Suc (steps_run oL oR (if oL i then t1 else t0))"
| "steps_run oL oR (AskR j t0 t1) =
     Suc (steps_run oL oR (if oR j then t1 else t0))"

(* Well-formedness: tree only queries from declared index sets *)
text \<open>Well-formedness: the tree only queries declared L/R indices.\<close>
inductive wf_dtr :: "'iL set \<Rightarrow> 'iR set \<Rightarrow> ('iL,'iR) dtr \<Rightarrow> bool" where
  Leaf[intro!]:  "wf_dtr L R (Leaf b)"
| AskL[intro!]:  "i \<in> L \<Longrightarrow> wf_dtr L R t0 \<Longrightarrow> wf_dtr L R t1 \<Longrightarrow> wf_dtr L R (AskL i t0 t1)"
| AskR[intro!]:  "j \<in> R \<Longrightarrow> wf_dtr L R t0 \<Longrightarrow> wf_dtr L R t1 \<Longrightarrow> wf_dtr L R (AskR j t0 t1)"

lemma seenL_subset:
  assumes "wf_dtr L R T" shows "seenL_run oL oR T \<subseteq> L"
  using assms by (induction T) auto

lemma seenR_subset:
  assumes "wf_dtr L R T" shows "seenR_run oL oR T \<subseteq> R"
  using assms by (induction T) auto

(* tiny helpers for the chosen branch *)
lemma seenL_sub_AskL:
  "seenL_run oL oR (if oL i then t1 else t0) \<subseteq> seenL_run oL oR (AskL i t0 t1)"
  by (cases "oL i") auto

lemma seenR_eq_AskL:
  "seenR_run oL oR (if oL i then t1 else t0) = seenR_run oL oR (AskL i t0 t1)"
  by (cases "oL i") auto

lemma seenR_sub_AskR:
  "seenR_run oL oR (if oR j then t1 else t0) \<subseteq> seenR_run oL oR (AskR j t0 t1)"
  by (cases "oR j") auto

lemma seenL_eq_AskR:
  "seenL_run oL oR (if oR j then t1 else t0) = seenL_run oL oR (AskR j t0 t1)"
  by (cases "oR j") auto

(* evaluation/seen simplifiers *)
lemmas run_simps   = run.simps
lemmas seenL_simps = seenL_run.simps
lemmas seenR_simps = seenR_run.simps

lemma run_Leaf[simp]:  "run oL oR (Leaf b) = b" by simp
lemma seenL_Leaf[simp]: "seenL_run oL oR (Leaf b) = {}" by simp
lemma seenR_Leaf[simp]: "seenR_run oL oR (Leaf b) = {}" by simp

lemma run_seen_agree_on_triple:
  assumes L: "\<And>i. i \<in> seenL_run oL oR T \<Longrightarrow> oL' i = oL i"
      and R: "\<And>j. j \<in> seenR_run oL oR T \<Longrightarrow> oR' j = oR j"
  shows "(run oL oR T, seenL_run oL oR T, seenR_run oL oR T)
       = (run oL' oR' T, seenL_run oL' oR' T, seenR_run oL' oR' T)"
  using L R
proof (induction T arbitrary: oL oR oL' oR')
  case (Leaf b)
  show ?case by simp

next
  case (AskL i t0 t1)
  (* agreement on the queried index i *)
  have eq_i: "oL' i = oL i"
    using AskL.prems(1) by simp

  (* IH packaged per subtree, guarded by the actual branch condition *)
  have rec_t1:
    "oL i \<Longrightarrow> (run oL oR t1, seenL_run oL oR t1, seenR_run oL oR t1)
           = (run oL' oR' t1, seenL_run oL' oR' t1, seenR_run oL' oR' t1)"
  proof -
    assume oi: "oL i"
    have Lb: "\<And>x. x \<in> seenL_run oL oR t1 \<Longrightarrow> oL' x = oL x"
      using AskL.prems(1) seenL_sub_AskL by (simp add: oi)
    have Rb: "\<And>x. x \<in> seenR_run oL oR t1 \<Longrightarrow> oR' x = oR x"
      using AskL.prems(2) seenR_eq_AskL by (simp add: oi)
    from AskL.IH(2)[OF Lb Rb] show ?thesis .
  qed

  have rec_t0:
    "\<not> oL i \<Longrightarrow> (run oL oR t0, seenL_run oL oR t0, seenR_run oL oR t0)
            = (run oL' oR' t0, seenL_run oL' oR' t0, seenR_run oL' oR' t0)"
  proof -
    assume noi: "\<not> oL i"
    have Lb: "\<And>x. x \<in> seenL_run oL oR t0 \<Longrightarrow> oL' x = oL x"
      using AskL.prems(1) seenL_sub_AskL by (simp add: noi)
    have Rb: "\<And>x. x \<in> seenR_run oL oR t0 \<Longrightarrow> oR' x = oR x"
      using AskL.prems(2) seenR_eq_AskL by (simp add: noi)
    from AskL.IH(1)[OF Lb Rb] show ?thesis .
  qed

  (* combine the two guarded IHs to get the equality on the chosen branch *)
  have rec_if:
    "(run oL oR (if oL i then t1 else t0),
      seenL_run oL oR (if oL i then t1 else t0),
      seenR_run oL oR (if oL i then t1 else t0))
     =
     (run oL' oR' (if oL i then t1 else t0),
      seenL_run oL' oR' (if oL i then t1 else t0),
      seenR_run oL' oR' (if oL i then t1 else t0))"
    by (cases "oL i") (simp add: rec_t1, simp add: rec_t0)

  (* reduce AskL on both sides and use oL' i = oL i for the condition *)
  have LHS_reduce:
    "(run oL oR (AskL i t0 t1),
      seenL_run oL oR (AskL i t0 t1),
      seenR_run oL oR (AskL i t0 t1))
     =
    (run oL oR (if oL i then t1 else t0),
      insert i (seenL_run oL oR (if oL i then t1 else t0)),
      seenR_run oL oR (if oL i then t1 else t0))" by simp
  have RHS_reduce:
    "(run oL' oR' (AskL i t0 t1),
      seenL_run oL' oR' (AskL i t0 t1),
      seenR_run oL' oR' (AskL i t0 t1))
     =
    (run oL' oR' (if oL i then t1 else t0),
      insert i (seenL_run oL' oR' (if oL i then t1 else t0)),
      seenR_run oL' oR' (if oL i then t1 else t0))"
    by (simp add: eq_i)

  show ?case
    using RHS_reduce rec_if by auto

next
  case (AskR j t0 t1)
  (* agreement on the queried index j *)
  have eq_j: "oR' j = oR j"
    using AskR.prems(2) by simp

  (* IH packaged per subtree, guarded by the actual branch condition *)
  have rec_t1:
    "oR j \<Longrightarrow> (run oL oR t1, seenL_run oL oR t1, seenR_run oL oR t1)
           = (run oL' oR' t1, seenL_run oL' oR' t1, seenR_run oL' oR' t1)"
  proof -
    assume oj: "oR j"
    have Lb: "\<And>x. x \<in> seenL_run oL oR t1 \<Longrightarrow> oL' x = oL x"
      using AskR.prems(1) seenL_eq_AskR by (simp add: oj)
    have Rb: "\<And>x. x \<in> seenR_run oL oR t1 \<Longrightarrow> oR' x = oR x"
      using AskR.prems(2) seenR_sub_AskR by (simp add: oj)
    from AskR.IH(2)[OF Lb Rb] show ?thesis .
  qed

  have rec_t0:
    "\<not> oR j \<Longrightarrow> (run oL oR t0, seenL_run oL oR t0, seenR_run oL oR t0)
            = (run oL' oR' t0, seenL_run oL' oR' t0, seenR_run oL' oR' t0)"
  proof -
    assume noj: "\<not> oR j"
    have Lb: "\<And>x. x \<in> seenL_run oL oR t0 \<Longrightarrow> oL' x = oL x"
      using AskR.prems(1) seenL_eq_AskR by (simp add: noj)
    have Rb: "\<And>x. x \<in> seenR_run oL oR t0 \<Longrightarrow> oR' x = oR x"
      using AskR.prems(2) seenR_sub_AskR by (simp add: noj)
    from AskR.IH(1)[OF Lb Rb] show ?thesis .
  qed

  have rec_if:
    "(run oL oR (if oR j then t1 else t0),
      seenL_run oL oR (if oR j then t1 else t0),
      seenR_run oL oR (if oR j then t1 else t0))
     =
     (run oL' oR' (if oR j then t1 else t0),
      seenL_run oL' oR' (if oR j then t1 else t0),
      seenR_run oL' oR' (if oR j then t1 else t0))"
    by (cases "oR j") (simp add: rec_t1, simp add: rec_t0)

  have LHS_reduce:
    "(run oL oR (AskR j t0 t1),
      seenL_run oL oR (AskR j t0 t1),
      seenR_run oL oR (AskR j t0 t1))
     =
    (run oL oR (if oR j then t1 else t0),
      seenL_run oL oR (if oR j then t1 else t0),
      insert j (seenR_run oL oR (if oR j then t1 else t0)))" by simp
  have RHS_reduce:
    "(run oL' oR' (AskR j t0 t1),
      seenL_run oL' oR' (AskR j t0 t1),
      seenR_run oL' oR' (AskR j t0 t1))
     =
    (run oL' oR' (if oR' j then t1 else t0),
      seenL_run oL' oR' (if oR' j then t1 else t0),
      insert j (seenR_run oL' oR' (if oR' j then t1 else t0)))" by simp
  have cond_swap: "(if oR' j then (X::'a) else Y) = (if oR j then X else Y)" for X Y :: 'a
    by (simp add: eq_j)

  show ?case
    using eq_j rec_if by auto
qed

(* KEY LEMMA: If two oracles agree on all queried indices, they get 
   the same result and query the same indices *)
lemma run_agree_on_seen:
  assumes L: "\<And>i. i \<in> seenL_run oL oR T \<Longrightarrow> oL' i = oL i"
      and R: "\<And>j. j \<in> seenR_run oL oR T \<Longrightarrow> oR' j = oR j"
  shows "run oL oR T = run oL' oR' T"
    and  "seenL_run oL oR T = seenL_run oL' oR' T"
    and  "seenR_run oL oR T = seenR_run oL' oR' T"
proof -
  from run_seen_agree_on_triple[OF L R]
  have "(run oL oR T, seenL_run oL oR T, seenR_run oL oR T)
      = (run oL' oR' T, seenL_run oL' oR' T, seenR_run oL' oR' T)" .
  thus "run oL oR T = run oL' oR' T"
    and "seenL_run oL oR T = seenL_run oL' oR' T"
    and "seenR_run oL oR T = seenR_run oL' oR' T" by auto
qed
 (* This is the "unread-agreement" property! *)

(* single-path seen-sets are finite *)
lemma finite_seenL_run[simp]: "finite (seenL_run oL oR T)"
  by (induction T arbitrary: oL oR) auto
lemma finite_seenR_run[simp]: "finite (seenR_run oL oR T)"
  by (induction T arbitrary: oL oR) auto

(* card(seenL) \<le> steps and symmetrically for R *)
lemma card_seenL_le_steps: "card (seenL_run oL oR T) \<le> steps_run oL oR T"
proof (induction T arbitrary: oL oR)
  case (Leaf b) show ?case by simp
next
  case (AskL i t0 t1)
  let ?S = "seenL_run oL oR (if oL i then t1 else t0)"
  have IH0: "card (seenL_run oL oR t0) \<le> steps_run oL oR t0" by (rule AskL.IH(1))
  have IH1: "card (seenL_run oL oR t1) \<le> steps_run oL oR t1" by (rule AskL.IH(2))
  have br: "card ?S \<le> steps_run oL oR (if oL i then t1 else t0)"
    by (cases "oL i"; simp add: IH0 IH1)
  have fin: "finite ?S"
    by simp
  have "card (seenL_run oL oR (AskL i t0 t1)) = card (insert i ?S)" by simp
  also have "\<dots> \<le> Suc (card ?S)" using fin by (simp add: card_insert_if)
  also have "\<dots> \<le> Suc (steps_run oL oR (if oL i then t1 else t0))"
    using br by simp
  also have "\<dots> = steps_run oL oR (AskL i t0 t1)" by simp
  finally show ?case .
next
  case (AskR j t0 t1)
  have IH0: "card (seenL_run oL oR t0) \<le> steps_run oL oR t0" by (rule AskR.IH(1))
  have IH1: "card (seenL_run oL oR t1) \<le> steps_run oL oR t1" by (rule AskR.IH(2))
  have br: "card (seenL_run oL oR (if oR j then t1 else t0))
            \<le> steps_run oL oR (if oR j then t1 else t0)"
    by (cases "oR j"; simp add: IH0 IH1)
  have "card (seenL_run oL oR (AskR j t0 t1))
        = card (seenL_run oL oR (if oR j then t1 else t0))" by simp
  also have "\<dots> \<le> steps_run oL oR (if oR j then t1 else t0)" using br .
  also have "\<dots> \<le> Suc (steps_run oL oR (if oR j then t1 else t0))"
    by (simp add: le_SucI)
  also have "\<dots> = steps_run oL oR (AskR j t0 t1)" by simp
  finally show ?case .
qed

lemma card_seenR_le_steps: "card (seenR_run oL oR T) \<le> steps_run oL oR T"
proof (induction T arbitrary: oL oR)
  case (Leaf b) show ?case by simp
next
  case (AskL i t0 t1)
  have IH0: "card (seenR_run oL oR t0) \<le> steps_run oL oR t0" by (rule AskL.IH(1))
  have IH1: "card (seenR_run oL oR t1) \<le> steps_run oL oR t1" by (rule AskL.IH(2))
  have br: "card (seenR_run oL oR (if oL i then t1 else t0))
            \<le> steps_run oL oR (if oL i then t1 else t0)"
    by (cases "oL i"; simp add: IH0 IH1)
  have "card (seenR_run oL oR (AskL i t0 t1))
        = card (seenR_run oL oR (if oL i then t1 else t0))" by simp
  also have "\<dots> \<le> steps_run oL oR (if oL i then t1 else t0)" using br .
  also have "\<dots> \<le> Suc (steps_run oL oR (if oL i then t1 else t0))"
    by (simp add: le_SucI)
  also have "\<dots> = steps_run oL oR (AskL i t0 t1)" by simp
  finally show ?case .
next
  case (AskR j t0 t1)
  let ?S = "seenR_run oL oR (if oR j then t1 else t0)"
  have IH0: "card (seenR_run oL oR t0) \<le> steps_run oL oR t0" by (rule AskR.IH(1))
  have IH1: "card (seenR_run oL oR t1) \<le> steps_run oL oR t1" by (rule AskR.IH(2))
  have br: "card ?S \<le> steps_run oL oR (if oR j then t1 else t0)"
    by (cases "oR j"; simp add: IH0 IH1)
  have fin: "finite ?S"
    by simp
  have "card (seenR_run oL oR (AskR j t0 t1)) = card (insert j ?S)" by simp
  also have "\<dots> \<le> Suc (card ?S)" using fin by (simp add: card_insert_if)
  also have "\<dots> \<le> Suc (steps_run oL oR (if oR j then t1 else t0))"
    using br by simp
  also have "\<dots> = steps_run oL oR (AskR j t0 t1)" by simp
  finally show ?case .
qed

(* Number of queries bounds the number of distinct indices seen *)
lemma steps_ge_sum_seen:
  "steps_run oL oR T \<ge> card (seenL_run oL oR T) + card (seenR_run oL oR T)"
  (* Each query step either queries a new index or re-queries an old one *)

(* ========================================================================= *)
(* PART 8: The Coverage Theorem (Lemma 1)                                   *)
(* ========================================================================= *)

text \<open>THE ADVERSARIAL ARGUMENT:
  
  If we have a tree T that computes a boolean function "good(oL, oR)" correctly,
  and flipping ANY unread index would change the answer, then ALL indices must
  have been read.
  
  This is the heart of Lemma 1!
\<close>
proof (induction T arbitrary: oL oR)
  case (Leaf b) show ?case by simp
next
  case (AskL i t0 t1)
  let ?SL = "seenL_run oL oR (if oL i then t1 else t0)"
  let ?SR = "seenR_run oL oR (if oL i then t1 else t0)"
  have IH0: "steps_run oL oR t0 \<ge> card (seenL_run oL oR t0) + card (seenR_run oL oR t0)"
    by (rule AskL.IH(1))
  have IH1: "steps_run oL oR t1 \<ge> card (seenL_run oL oR t1) + card (seenR_run oL oR t1)"
    by (rule AskL.IH(2))
  have br: "steps_run oL oR (if oL i then t1 else t0) \<ge> card ?SL + card ?SR"
    by (cases "oL i") (simp_all add: IH0 IH1)
  have fin: "finite ?SL" "finite ?SR"
    by (cases "oL i"; simp)+
  have "card (seenL_run oL oR (AskL i t0 t1)) + card (seenR_run oL oR (AskL i t0 t1))
        = card (insert i ?SL) + card ?SR" by simp
  also have "\<dots> \<le> Suc (card ?SL) + card ?SR"
    using fin(1) by (simp add: card_insert_if add_mono)
  also have "\<dots> = Suc (card ?SL + card ?SR)" by simp
  also have "\<dots> \<le> steps_run oL oR (AskL i t0 t1)"
    using br by simp
  finally show ?case .
next
  case (AskR j t0 t1)
  let ?SL = "seenL_run oL oR (if oR j then t1 else t0)"
  let ?SR = "seenR_run oL oR (if oR j then t1 else t0)"
  have IH0: "steps_run oL oR t0 \<ge> card (seenL_run oL oR t0) + card (seenR_run oL oR t0)"
    by (rule AskR.IH(1))
  have IH1: "steps_run oL oR t1 \<ge> card (seenL_run oL oR t1) + card (seenR_run oL oR t1)"
    by (rule AskR.IH(2))
  have br: "steps_run oL oR (if oR j then t1 else t0) \<ge> card ?SL + card ?SR"
    by (cases "oR j") (simp_all add: IH0 IH1)
  have fin: "finite ?SL" "finite ?SR"
    by (cases "oR j"; simp)+
  have "card (seenL_run oL oR (AskR j t0 t1)) + card (seenR_run oL oR (AskR j t0 t1))
        = card ?SL + card (insert j ?SR)" by simp
  also have "\<dots> \<le> card ?SL + Suc (card ?SR)"
    using fin(2) by (simp add: card_insert_if add_mono)
  also have "\<dots> = Suc (card ?SL + card ?SR)" by simp
  also have "\<dots> \<le> steps_run oL oR (AskR j t0 t1)"
    using br by simp
  finally show ?case .
qed

(* powers-of-two as ints *)
definition pow2_list :: "nat \<Rightarrow> int list" where
  "pow2_list n = map (\<lambda>i. (2::int)^i) [0..<n]"

text \<open>A generic adversary/coverage locale: this abstracts Lemma 1.\<close>
locale DecisionTree_Coverage =
  fixes Lset :: "'iL set" and Rset :: "'iR set"  (* Index sets *)
  fixes T    :: "('iL,'iR) dtr"                  (* The decision tree *)
  fixes good :: "('iL \<Rightarrow> bool) \<Rightarrow> ('iR \<Rightarrow> bool) \<Rightarrow> bool" (* The spec *)
  assumes wf: "wf_dtr Lset Rset T"
  assumes correct: "\<forall>oL oR. run oL oR T = good oL oR"
(* CRITICAL: Flipping any unread index would change the answer *)
  assumes flipL_pointwise:
    "\<And>i oL oR. i \<in> Lset \<Longrightarrow> \<exists>oL'. (\<forall>j\<noteq>i. oL' j = oL j) \<and> good oL' oR \<noteq> good oL oR"
  assumes flipR_pointwise:
    "\<And>j oL oR. j \<in> Rset \<Longrightarrow> \<exists>oR'. (\<forall>i\<noteq>j. oR' i = oR i) \<and> good oL oR' \<noteq> good oL oR"
begin

(* THEOREM: Every index in Lset and Rset must be queried *)
lemma coverage_for_all_inputs:
  "\<And>oL oR. seenL_run oL oR T = Lset \<and> seenR_run oL oR T = Rset"
proof (intro allI conjI)
  fix oL oR
  have subL: "seenL_run oL oR T \<subseteq> Lset" using wf by (rule seenL_subset)
  have subR: "seenR_run oL oR T \<subseteq> Rset" using wf by (rule seenR_subset)
  have supL: "Lset \<subseteq> seenL_run oL oR T"
  proof
    fix i assume iL: "i \<in> Lset"
    show "i \<in> seenL_run oL oR T"
    proof (rule ccontr)
      assume "i \<notin> seenL_run oL oR T"
      then obtain oL' where A: "\<And>j. j \<noteq> i \<Longrightarrow> oL' j = oL j"
                         and F: "good oL' oR \<noteq> good oL oR"
        using flipL_pointwise[OF iL] by blast
      have "\<And>j. j \<in> seenL_run oL oR T \<Longrightarrow> oL' j = oL j"
        using A \<open>i \<notin> seenL_run oL oR T\<close> by fast
      moreover have "\<And>k. k \<in> seenR_run oL oR T \<Longrightarrow> oR k = oR k" by simp
      ultimately have "run oL oR T = run oL' oR T"
        by (rule run_agree_on_seen)
      hence "good oL oR = good oL' oR"
        using correct by blast
      with F show False by simp
    qed
  qed
  have supR: "Rset \<subseteq> seenR_run oL oR T"
  proof
    fix j assume jR: "j \<in> Rset"
    show "j \<in> seenR_run oL oR T"
    proof (rule ccontr)
      assume "j \<notin> seenR_run oL oR T"
      then obtain oR' where A: "\<And>i. i \<noteq> j \<Longrightarrow> oR' i = oR i"
                         and F: "good oL oR' \<noteq> good oL oR"
        using flipR_pointwise[OF jR] by blast
      have "\<And>k. k \<in> seenR_run oL oR T \<Longrightarrow> oR' k = oR k"
        using A \<open>j \<notin> seenR_run oL oR T\<close> by fast
      moreover have "\<And>i. i \<in> seenL_run oL oR T \<Longrightarrow> oL i = oL i" by simp
      ultimately have "run oL oR T = run oL oR' T"
        using run_agree_on_seen(1) by blast
      hence "good oL oR = good oL oR'"
        using correct by blast
      with F show False by simp
    qed
  qed
  from subL supL subR supR show "seenL_run oL oR T = Lset" "seenR_run oL oR T = Rset" by auto
qed

(* COROLLARY: Number of steps \<ge> |Lset| + |Rset| *)
lemma steps_lower_bound_all:
  "\<And>oL oR. steps_run oL oR T \<ge> card Lset + card Rset"
proof -
  fix oL oR
  from coverage_for_all_inputs have "seenL_run oL oR T = Lset" "seenR_run oL oR T = Rset" by blast+
  moreover have "steps_run oL oR T
       \<ge> card (seenL_run oL oR T) + card (seenR_run oL oR T)"
    by (rule steps_ge_sum_seen)
  ultimately show "steps_run oL oR T \<ge> card Lset + card Rset" by simp
qed

end  (* DecisionTree_Coverage *)

(* ========================================================================= *)
(* PART 9: Ruling Out Polynomial Time                                       *)
(* ========================================================================= *)

(* The rest of the theory shows that if you could solve subset-sum in 
   polynomial time for the distinct-subset-sums family, you'd violate
   the exponential lower bound 2\<surd>(2^n) we just proved. *)

locale SubsetSum_Reader_NoK =
  fixes steps :: "int list \<Rightarrow> int \<Rightarrow> nat"
    and seenL :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int set"
    and seenR :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int set"
  assumes coverage_ex:
    "\<And>as s. distinct_subset_sums as \<Longrightarrow> \<exists>k\<le>length as.
       seenL as s k = LHS (e_k as s k) (length as) \<and>
       seenR as s k = RHS (e_k as s k) (length as)"
  assumes steps_lb:
    "\<And>as s k. steps as s \<ge> card (seenL as s k) + card (seenR as s k)"
begin

lemma lemma1_ex:
  assumes n_def: "n = length as" and distinct: "distinct_subset_sums as"
  shows "\<exists>k\<le>n. card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n) \<le> steps as s"
proof -
  obtain k where k_le: "k \<le> n"
    and covL: "seenL as s k = LHS (e_k as s k) n"
    and covR: "seenR as s k = RHS (e_k as s k) n"
    using coverage_ex[OF distinct] n_def by force
  have "card (seenL as s k) + card (seenR as s k) \<le> steps as s"
    by (rule steps_lb)
  hence "card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n) \<le> steps as s"
    by (simp add: covL covR)
  thus ?thesis using k_le by blast
qed

theorem subset_sum_sqrt_lower_bound:
  fixes as :: "int list" and s :: int and n :: nat
  assumes n_def: "n = length as" and distinct: "distinct_subset_sums as"
  shows "2 * sqrt ((2::real) ^ n) \<le> real (steps as s)"
proof -
  obtain k where k_le: "k \<le> n" and base:
    "card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n) \<le> steps as s"
    using lemma1_ex[OF n_def distinct] by blast
  have "2 * sqrt ((2::real) ^ n)
        \<le> real (card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n))"
    using lhs_rhs_sum_lower_bound[OF n_def k_le distinct] .
  also have "\<dots> \<le> real (steps as s)" using base by simp
  finally show ?thesis .
qed

end  (* SubsetSum_Reader_NoK *)

locale SubsetSum_To_Polytime_NoK =
  SubsetSum_Reader_NoK +
  fixes enc :: "int list \<Rightarrow> int \<Rightarrow> bool list"
assumes enc_len_poly:
  "\<exists>(C::real)>0. \<exists>(D::nat).
      \<forall>as s. distinct_subset_sums as \<longrightarrow>
        real (length (enc as s)) \<le> C * (real (length as)) ^ D"
assumes steps_poly_of_enc:
  "\<exists>(c::real)>0. \<exists>(d::nat).
      \<forall>as s. steps as s \<le> nat (ceiling (c * (real (length (enc as s))) ^ d))"
begin

lemma steps_poly_in_n_on_distinct:
  shows "\<exists>(c'::real)>0. \<exists>(d'::nat).
           \<forall>as s n. n = length as \<longrightarrow> distinct_subset_sums as \<longrightarrow>
                    steps as s \<le> nat (ceiling (c' * (real n) ^ d'))"
proof -
  obtain C :: real and D :: nat
    where Cpos: "C > 0"
      and enc_bd:
        "\<forall>as s. distinct_subset_sums as \<longrightarrow>
           real (length (enc as s)) \<le> C * (real (length as)) ^ D"
    using enc_len_poly by blast
  obtain c :: real and d :: nat
    where cpos: "c > 0"
      and step_bd:
        "\<forall>as s. steps as s \<le> nat (ceiling (c * (real (length (enc as s))) ^ d))"
    using steps_poly_of_enc by blast
  define c' where "c' = c * C ^ d"
  define d' where "d' = D * d"
  have c'pos: "c' > 0" using cpos Cpos by (simp add: c'_def)

  have main:
    "\<forall>as s n. n = length as \<longrightarrow> distinct_subset_sums as \<longrightarrow>
       steps as s \<le> nat (ceiling (c' * (real n) ^ d'))"
  proof (intro allI impI)
    fix as s n assume n_def: "n = length as" and dist: "distinct_subset_sums as"
    have step0: "steps as s \<le> nat (ceiling (c * (real (length (enc as s))) ^ d))"
      using step_bd by blast
    have enc_real: "real (length (enc as s)) \<le> C * (real n) ^ D"
      using enc_bd dist n_def by simp
    have nonneg_x: "0 \<le> real (length (enc as s))" by simp
    have nonneg_y: "0 \<le> C * (real n) ^ D"
      using Cpos by (intro mult_nonneg_nonneg) simp_all
    have pow_mono:
      "(real (length (enc as s))) ^ d \<le> (C * (real n) ^ D) ^ d"
      by (rule power_mono) (use enc_real nonneg_x nonneg_y in auto)
    have mult_mono:
      "c * (real (length (enc as s))) ^ d \<le> c * (C * (real n) ^ D) ^ d"
      using pow_mono cpos by (simp add: mult_left_mono)
    have step1:
      "nat (ceiling (c * (real (length (enc as s))) ^ d))
       \<le> nat (ceiling (c * (C * (real n) ^ D) ^ d))"
      using mult_mono by (intro nat_mono ceiling_mono) simp_all
    from step0 step1
    have "steps as s \<le> nat (ceiling (c * (C * (real n) ^ D) ^ d))" by linarith
    also have "\<dots> = nat (ceiling ((c * C ^ d) * (real n) ^ (D * d)))"
      by (simp add: power_mult_distrib mult_ac power_mult)
    finally show "steps as s \<le> nat (ceiling (c' * (real n) ^ d'))"
      by (simp add: c'_def d'_def)
  qed
  show ?thesis using c'pos main by blast
qed

lemma exp_beats_poly_ceiling_strict:
  fixes c :: real and d :: nat
  assumes cpos: "c > 0"
  shows "\<exists>N::nat. \<forall>n\<ge>N.
           of_int (ceiling (c * (real n) ^ d)) < 2 * sqrt ((2::real) ^ n)"
proof -
  (* Eventually: c * n^d \<le> (\<surd>2)^n *)
  have ev: "eventually (\<lambda>n. c * (real n) ^ d \<le> (sqrt 2) ^ n) at_top"
    by real_asymp
  then obtain N1 where N1: "\<forall>n\<ge>N1. c * (real n) ^ d \<le> (sqrt 2) ^ n"
    by (auto simp: eventually_at_top_linorder)
  define N where "N = max N1 1"

  have ceil_le: "of_int (ceiling y) \<le> y + 1" for y :: real by linarith
  show ?thesis
  proof (rule exI[of _ N], intro allI impI)
    fix n assume nN: "n \<ge> N"
    hence nN1: "n \<ge> N1" and n_ge1: "n \<ge> 1" by (auto simp: N_def)
    from N1 nN1 have bound: "c * (real n) ^ d \<le> (sqrt 2) ^ n" by simp
    have up: "of_int (ceiling (c * (real n) ^ d)) \<le> (sqrt 2) ^ n + 1"
      using ceil_le bound by linarith
    have step: "(sqrt 2) ^ n + 1 < 2 * (sqrt 2) ^ n"
      using n_ge1 by auto
    have "2 * sqrt ((2::real) ^ n) = 2 * (sqrt 2) ^ n"
      by (simp add: real_sqrt_power)
    from up step have L: "of_int (ceiling (c * (real n) ^ d)) < 2 * (sqrt 2) ^ n"
      by linarith
    have "2 * sqrt ((2::real) ^ n) = 2 * (sqrt 2) ^ n"
      by (simp add: real_sqrt_power)
    with L show "of_int (ceiling (c * (real n) ^ d)) < 2 * sqrt ((2::real) ^ n)" by simp
  qed
qed

lemma nth_pow2_list:
  assumes "i < n"
  shows "pow2_list n ! i = (2::int)^i"
  using assms by (simp add: pow2_list_def nth_map_upt)

lemma sum_prefix_pow2_list:
  assumes "k \<le> n"
  shows "(\<Sum> i<k. pow2_list n ! i) = (\<Sum> i<k. (2::int)^i)"
  using assms by (simp add: nth_pow2_list)

lemma pow2_gt_sum_prev_int:
  fixes k :: nat
  shows "(\<Sum> i<k. (2::int)^i) < 2^k"
proof (induction k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have "(\<Sum> i<Suc k. (2::int)^i) = (\<Sum> i<k. 2^i) + 2^k" by simp
  also have "\<dots> < 2^k + 2^k"
    using Suc.IH by (intro add_strict_right_mono)   (* int version *)
  also have "\<dots> = 2^(Suc k)" by simp
  finally show ?case .
qed

(* split a {..<n} sum at index k *)
lemma sum_split_at:
  fixes f :: "nat \<Rightarrow> 'a::comm_monoid_add"
  assumes "k < n"
  shows "sum f {..<n} = sum f {..<k} + f k + sum f {k+1..<n}"
proof -
(* split {..<n} into {..<k} ⪯ {k..<n} *)
  have part: "{..<n} = {..<k} \<union> {k..<n}"
    using \<open>k < n\<close> by auto
  have step1: "sum f {..<n} = sum f {..<k} + sum f {k..<n}"
    by (metis Un_upper1 lessThan_atLeast0 lessThan_subset_iff less_eq_nat.simps(1) 
        part sum.atLeastLessThan_concat)

(* peel k from {k..<n} *)
  have step2set: "{k..<n} = insert k {Suc k..<n}"
    by (metis Suc_leD assms atLeastLessThan_empty atLeastLessThan_empty_iff 
        atLeastLessThan_singleton insert_is_Un ivl_disj_un_two(3) not_less_eq_eq)
  have step2: "sum f {k..<n} = f k + sum f {Suc k..<n}"
    by (subst step2set) simp

(* combine *)
  have "sum f {..<n} = sum f {..<k} + f k + sum f {k+1..<n}"
    using step1 step2 by (metis Suc_eq_plus1 add.assoc)
  show ?thesis
    using \<open>sum f {..<n} = sum f {..<k} + f k + sum f {k + 1..<n}\<close> by blast
qed

(* triangle inequality for sums over {..<k} *)
lemma abs_sum_le_sum_abs_upto:
  shows "abs (\<Sum> i<k. (f i::int)) \<le> (\<Sum> i<k. abs (f i))"
  by (rule sum_abs)

lemma length_pow2_list[simp]: "length (pow2_list n) = n"
  by (simp add: pow2_list_def)

(* handy nth fact over a mapped [0..<n] *)
lemma nth_map_upt:
  assumes "k < n"
  shows "(map f [0..<n]) ! k = f k"
  using assms by simp

lemma pow2_list_nth:
  assumes "k < n"
  shows "pow2_list n ! k = (2::int)^k"
  using assms by (simp add: pow2_list_def nth_map_upt)

(* the superincreasing property you want *)
lemma pow2_superincreasing:
  assumes "k < n"
  shows "pow2_list n ! k > (\<Sum> i<k. pow2_list n ! i)"
proof -
  have A: "pow2_list n ! k = (2::int)^k"
    using assms by (simp add: pow2_list_def nth_map_upt)
  have B: "(\<Sum> i<k. pow2_list n ! i) = (\<Sum> i<k. (2::int)^i)"
    using assms by (simp add: sum_prefix_pow2_list)
  show ?thesis
    by (simp add: A B pow2_gt_sum_prev_int)
qed

lemma diff_of_bits:
  fixes x y :: int
  assumes "x \<in> {0,1}" "y \<in> {0,1}" "x \<noteq> y"
  shows "x - y = 1 \<or> x - y = -1"
  using assms by auto

lemma distinct_subset_sums_pow2:
  fixes n :: nat
  defines "as \<equiv> pow2_list n"
  shows "distinct_subset_sums as"
proof -
  have len: "length as = n" by (simp add: as_def)
  have A: "\<And>xs. xs \<in> bitvec n \<Longrightarrow> set xs \<subseteq> {0,1}" by (simp add: bitvec_def)
  have B: "\<And>xs. xs \<in> bitvec n \<Longrightarrow> length xs = n" by (simp add: bitvec_def)

  have super: "\<And>k. k<n \<Longrightarrow> as ! k > (\<Sum> i<k. as ! i)"
  proof -
    fix k assume "k<n"
    have "as ! k = 2^k"
      using \<open>k<n\<close> len by (simp add: as_def pow2_list_def nth_map_upt)
    moreover have "(\<Sum> i<k. as ! i) = (\<Sum> i<k. 2^i)"
      by (simp add: \<open>k < n\<close> assms less_imp_le_nat sum_prefix_pow2_list)
    ultimately show "as ! k > (\<Sum> i<k. as ! i)"
      using pow2_gt_sum_prev_int by presburger
  qed

  (* superincreasing \<Rightarrow> uniqueness of 0/1-sum representation *)
  have uniq:
    "\<And>xs ys. xs \<in> bitvec n \<Longrightarrow> ys \<in> bitvec n \<Longrightarrow>
             (\<Sum> i<n. as ! i * xs ! i) = (\<Sum> i<n. as ! i * ys ! i) \<Longrightarrow> xs = ys"
  proof -
    fix xs ys assume X: "xs \<in> bitvec n" and Y: "ys \<in> bitvec n"
    and EQ: "(\<Sum> i<n. as ! i * xs ! i) = (\<Sum> i<n. as ! i * ys ! i)"
    show "xs = ys"
    proof (rule ccontr)
      assume "xs \<noteq> ys"
      let ?D = "{i. i<n \<and> xs ! i \<noteq> ys ! i}"
      have fin: "finite ?D" by simp
      have ne: "?D \<noteq> {}"
      proof
        assume "?D = {}"
        hence "\<forall>i<n. xs ! i = ys ! i" by auto
        with B[OF X] B[OF Y] have "xs = ys" by (intro nth_equalityI) auto
        with \<open>xs \<noteq> ys\<close> show False by contradiction
      qed
      define k where "k = Max ?D"
      have kD: "k \<in> ?D" using Max_eq_iff fin k_def ne by blast
      hence kn: "k<n" and diff: "xs ! k \<noteq> ys ! k" by auto

      have zero_above:
        "\<forall>i. k<i \<and> i<n \<longrightarrow> xs ! i = ys ! i"
        using Max_less_iff fin k_def by blast

      have len_xs: "length xs = n"     using X by (auto simp: bitvec_def)
      have xs01_set: "set xs \<subseteq> {0,1}" using X by (auto simp: bitvec_def)

      have len_ys: "length ys = n"     using Y by (auto simp: bitvec_def)
      have ys01_set: "set ys \<subseteq> {0,1}" using Y by (auto simp: bitvec_def)

      have xk01: "xs ! k \<in> {0,1}"
        by (metis kn len_xs nth_mem subsetD xs01_set)
      have yk01: "ys ! k \<in> {0,1}"
        by (metis kn len_ys nth_mem subsetD ys01_set)

(* you must have chosen k so that xs ! k \<noteq> ys ! k *)
      have xy_ne: "xs ! k \<noteq> ys ! k" by (simp add: diff)
  (* e.g. if k is a (max/first) index of difference, or from a premise *)

      have bits: "xs ! k - ys ! k = 1 \<or> xs ! k - ys ! k = -1"
        by (rule diff_of_bits[OF xk01 yk01 xy_ne])

     have tail_bound:
       "abs (\<Sum> i<k. as ! i * (xs ! i - ys ! i)) \<le> (\<Sum> i<k. abs (as ! i))"
     proof -
       have step_i: "\<And>i. i < k \<Longrightarrow> abs (as ! i * (xs ! i - ys ! i)) \<le> abs (as ! i)"
       proof -
         fix i assume ik: "i < k"
         hence in_n: "i < n" using kn by simp
         have xs01i: "xs ! i \<in> {0,1}" by (metis in_n len_xs nth_mem subsetD xs01_set)
         have ys01i: "ys ! i \<in> {0,1}" by (metis in_n len_ys nth_mem subsetD ys01_set)
         have diff_le1: "abs (xs ! i - ys ! i) \<le> (1::int)"
           using xs01i ys01i by fastforce
         have "abs (as ! i * (xs ! i - ys ! i)) = abs (as ! i) * abs (xs ! i - ys ! i)"
           by (simp add: abs_mult)
         also have "\<dots> \<le> abs (as ! i) * 1"
           using diff_le1 by (intro mult_left_mono) simp_all
         finally show "abs (as ! i * (xs ! i - ys ! i)) \<le> abs (as ! i)" by simp
       qed
       have A: "abs (\<Sum> i<k. as ! i * (xs ! i - ys ! i))
           \<le> (\<Sum> i<k. abs (as ! i * (xs ! i - ys ! i)))"
         by simp
       have B: "(\<Sum> i<k. abs (as ! i * (xs ! i - ys ! i))) \<le> (\<Sum> i<k. abs (as ! i))"
         using step_i by (intro sum_mono; simp)
       from A B show ?thesis by linarith
     qed

(* From EQ: the two totals are equal *)
     have diff_sum:
       "0 = (\<Sum> i<n. as ! i * (xs ! i - ys ! i))"
       using EQ by (simp add: sum_subtractf algebra_simps)

(* Split the sum at k *)
     have split_k:
       "(\<Sum> i<n. as ! i * (xs ! i - ys ! i))
        = (\<Sum> i<k. as ! i * (xs ! i - ys ! i))
        + as ! k * (xs ! k - ys ! k)
        + (\<Sum> i\<in>{k+1..<n}. as ! i * (xs ! i - ys ! i))"
     using kn sum_split_at by blast

(* The tail after k is zero because xs and ys agree there *)
     have tail_zero:
       "(\<Sum> i\<in>{k+1..<n}. as ! i * (xs ! i - ys ! i)) = 0"
       by (rule sum.neutral) (auto simp: zero_above)

     from diff_sum split_k tail_zero
     have "0 = as ! k * (xs ! k - ys ! k)
           + (\<Sum> i<k. as ! i * (xs ! i - ys ! i))"
       by simp
     hence "abs (as ! k * (xs ! k - ys ! k))
            = abs (\<Sum> i<k. as ! i * (xs ! i - ys ! i))"
       by simp
(* entries of as are nonnegative (here as = pow2_list n) *)
     have as_nonneg: "\<And>i. i < n \<Longrightarrow> 0 \<le> as ! i"
       by (simp add: as_def pow2_list_def nth_map_upt)

(* turn \<Sum> |as!i| into \<Sum> as!i on {..<k} *)
    have drop_abs_sum:
      "(\<Sum> i<k. abs (as ! i)) = sum ((!) as) {..<k}"
    proof (rule sum.cong[OF refl])
      fix i assume "i \<in> {..<k}"
      then have "i < k" by simp
      with kn have "i < n" by simp
      hence "abs (as ! i) = as ! i"
        by (simp add: as_nonneg)
      thus "abs (as ! i) = (!) as i" by simp
    qed
      have "abs (as ! k * (xs ! k - ys ! k))
            = abs (\<Sum> i<k. as ! i * (xs ! i - ys ! i))"
        using \<open>0 = as ! k * (xs ! k - ys ! k) + (\<Sum> i<k. as ! i * (xs ! i - ys ! i))\<close>
        by simp
      also have "\<dots> \<le> (\<Sum> i<k. abs (as ! i))"
        using tail_bound by simp
      also have "\<dots> = sum ((!) as) {..<k}"
        by (rule drop_abs_sum)
      finally have "abs (as ! k * (xs ! k - ys ! k)) \<le> sum ((!) as) {..<k}" .
      then have "as ! k \<le> (\<Sum> i<k. as ! i)"
        using bits by auto
      with super[OF kn] show False by simp
    qed
  qed
 show ?thesis
    unfolding distinct_subset_sums_def
    using len
    by (intro ballI; clarify) (metis uniq)
qed

lemma exists_hard:
  "\<forall>n. \<exists>as. length as = n \<and> distinct_subset_sums as"
proof
  fix n
  show "\<exists>as. length as = n \<and> distinct_subset_sums as"
    by (intro exI[of _ "pow2_list n"])
       (simp add: distinct_subset_sums_pow2)
qed

theorem no_polytime_decider_on_distinct_family:
  shows "\<not> (\<exists>(c::real)>0. \<exists>(d::nat).
             \<forall>as s. distinct_subset_sums as \<longrightarrow>
               steps as s \<le> nat (ceiling (c * (real (length as)) ^ d)))"
proof
  assume ex: "\<exists>(c::real)>0. \<exists>(d::nat).
                \<forall>as s. distinct_subset_sums as \<longrightarrow>
                  steps as s \<le> nat (ceiling (c * (real (length as)) ^ d))"

  obtain c d where
    cpos: "c > 0" and
    poly_n: "\<forall>as s. distinct_subset_sums as \<longrightarrow>
                  steps as s \<le> nat (ceiling (c * (real (length as)) ^ d))"
    using ex by blast

  obtain N::nat where N:
    "\<forall>n\<ge>N. 2 * sqrt ((2::real) ^ n) > of_int (ceiling (c * (real n) ^ d))"
    using exp_beats_poly_ceiling_strict[OF cpos] by blast

  define n :: nat where "n = N"
  have n_ge: "n \<ge> N" by (simp add: n_def)

  obtain as where nlen: "length as = n" and dist: "distinct_subset_sums as"
    using exists_hard by blast

  have lb: "2 * sqrt ((2::real) ^ n) \<le> real (steps as s)"
    using subset_sum_sqrt_lower_bound[OF nlen[symmetric] dist] .

  have poly_n_as: "\<forall>s. steps as s \<le> nat (ceiling (c * (real (length as)) ^ d))"
    using poly_n dist by blast
  have ub_nat: "steps as s \<le> nat (ceiling (c * (real n) ^ d))"
    using poly_n_as by (simp add: nlen)

  have nonneg: "0 \<le> c * (real n) ^ d" using cpos by simp
  have ceil_ge0: "0 \<le> ceiling (c * (real n) ^ d)" using nonneg by simp
  have conv: "real (nat (ceiling (c * (real n) ^ d))) = of_int (ceiling (c * (real n) ^ d))"
    using ceil_ge0 by simp
  have ub: "real (steps as s) \<le> of_int (ceiling (c * (real n) ^ d))"
    using ub_nat conv by simp

  from N n_ge have strict:
    "2 * sqrt ((2::real) ^ n) > of_int (ceiling (c * (real n) ^ d))" by blast
  from lb ub strict show False by linarith
qed
end

section \<open>Cook–Levin: conclude SUBSET-SUM \<notin> P (conditional on the bridge)\<close>

context SubsetSum_To_Polytime_NoK
begin

context
  fixes E :: "int list \<Rightarrow> int \<Rightarrow> bool list"
  assumes E_len_overhead:
    "\<exists>A B. \<forall>as s. length (E as s) \<le> A * length (enc as s) + B"
begin

definition SUBSET_SUM_CL :: "bool list set" where
  "SUBSET_SUM_CL =
     { E as s | as s.
         (\<exists>xs\<in>bitvec (length as). (\<Sum> i < length as. as ! i * xs ! i) = s) }"

theorem subset_sum_not_in_P_CL:
  shows "SUBSET_SUM_CL \<notin> P"
proof
  assume Pin: "SUBSET_SUM_CL \<in> P"

  (* From membership in P, get a poly bound in the encoding length. *)
  from Pin obtain c d where cpos: "c > 0"
    and enc_steps:
      "\<forall>as s. steps as s \<le> nat (ceiling (c * (real (length (enc as s))) ^ d))"
    using steps_poly_of_enc by blast

  (* Turn “poly in |enc|” into “poly in n = length as” on DISTINCT instances. *)
  from steps_poly_in_n_on_distinct
  obtain c' d' where c'pos: "c' > 0"
    and poly_n:
      "\<forall>as s n. n = length as \<longrightarrow> distinct_subset_sums as \<longrightarrow>
                 steps as s \<le> nat (ceiling (c' * (real n) ^ d'))"
    by blast

  (* Package it in the exact shape that the impossibility theorem forbids. *)
  have ex_cd':
    "\<exists>(c''::real)>0. \<exists>(d''::nat).
        \<forall>as s. distinct_subset_sums as \<longrightarrow>
          steps as s \<le> nat (ceiling (c'' * (real (length as)) ^ d''))"
    using c'pos poly_n by blast

  (* Contradiction with your lower-bound theorem over DISTINCT families. *)
  from no_polytime_decider_on_distinct_family ex_cd' show False by blast
qed

end  (* inner context with E *)
end  (* SubsetSum_To_Polytime_NoK *)

lemma sum_lessThan_split_at:
  fixes f :: "nat \<Rightarrow> 'a::comm_monoid_add"
  assumes "k < n"
  shows "(\<Sum> i<n. f i) =
         (\<Sum> i<k. f i) + f k + (\<Sum> i = Suc k..<n. f i)"
proof -
  have "{..<n} = {..<k} \<union> {k} \<union> {Suc k..<n}"
    using assms by auto
  moreover have "finite ({..<k}::nat set)" and "finite {k}" and "finite {Suc k..<n}" by simp_all
  moreover have "{..<k} \<inter> {k} = {}" and "({..<k} \<union> {k}) \<inter> {Suc k..<n} = {}" by auto
  ultimately show ?thesis
    by (metis Un_insert_right add.commute boolean_algebra.disj_zero_right 
        disjoint_insert(1) finite_UnI sum.insert sum_Un_eq)
qed

lemma distinct_subset_sums_pow2_list:
  fixes n :: nat
  shows "distinct_subset_sums (pow2_list n)"
proof -
  let ?as = "pow2_list n"

  have uniq:
    "\<And>xs ys. xs \<in> bitvec n \<Longrightarrow> ys \<in> bitvec n \<Longrightarrow>
             (\<Sum> i<n. ?as!i * xs!i) = (\<Sum> i<n. ?as!i * ys!i) \<Longrightarrow> xs = ys"
  proof -
    fix xs ys assume xsB: "xs \<in> bitvec n" and ysB: "ys \<in> bitvec n"
      and EQ: "(\<Sum> i<n. ?as!i * xs!i) = (\<Sum> i<n. ?as!i * ys!i)"
    show "xs = ys"
    proof (rule ccontr)
      assume "xs \<noteq> ys"
      let ?D = "{i. i < n \<and> xs!i \<noteq> ys!i}"
      have finD: "finite ?D" by simp

      from xsB have xs_len: "length xs = n" and xs01_set: "set xs \<subseteq> {0,1}"
        by (auto simp: bitvec_def)
      from ysB have ys_len: "length ys = n" and ys01_set: "set ys \<subseteq> {0,1}"
        by (auto simp: bitvec_def)
      have xs01_i: "\<And>i. i < n \<Longrightarrow> xs!i \<in> {0,1}"
        using xs_len xs01_set by (metis in_mono nth_mem)
      have ys01_i: "\<And>i. i < n \<Longrightarrow> ys!i \<in> {0,1}"
        using ys_len ys01_set by (metis in_mono nth_mem)

      have D_ne: "?D \<noteq> {}" 
      proof 
        assume "?D = {}" 
        hence "\<forall>i<n. xs!i = ys!i" 
          by auto with xs_len ys_len 
        have "xs = ys" 
          by (intro nth_equalityI) auto with \<open>xs \<noteq> ys\<close> 
        show False by contradiction 
      qed 
      define k where "k = Max ?D" 
      have k_in: "k \<in> ?D" 
        using D_ne Max_in finD k_def by blast 
      hence k_lt: "k < n" and k_diff: "xs!k \<noteq> ys!k" by auto 
      have agree_after: "\<And>i. k < i \<Longrightarrow> i < n \<Longrightarrow> xs!i = ys!i" 
        using Max_less_iff finD k_def by blast

      (* Tail after k cancels. *)
      have tail0: "(\<Sum> i\<in>{k+1..<n}. ?as!i * (xs!i - ys!i)) = 0"
        by (rule sum.neutral) (use agree_after in auto)

      (* Turn EQ into 0 = sum of differences and split at k. *)
      have zero_sum: "0 = (\<Sum> i<n. ?as!i * (xs!i - ys!i))"
        using EQ by (simp add: sum_subtractf algebra_simps)
      have split_k:
        "(\<Sum> i<n. ?as!i * (xs!i - ys!i)) =
           (\<Sum> i<k. ?as!i * (xs!i - ys!i)) + ?as!k * (xs!k - ys!k)
           + (\<Sum> i = Suc k..<n. ?as!i * (xs!i - ys!i))"
        using k_lt by (rule sum_lessThan_split_at)

      from zero_sum split_k tail0
      have eq_abs:
        "abs (?as!k * (xs!k - ys!k))
         = abs (\<Sum> i<k. ?as!i * (xs!i - ys!i))" by simp

      (* Triangle inequality and |xs!i - ys!i| \<le> 1. *)
      have abs_sum_le:
        "abs (\<Sum> i<k. ?as!i * (xs!i - ys!i)) \<le> (\<Sum> i<k. abs (?as!i))"
      proof -
        have "abs (\<Sum> i<k. ?as!i * (xs!i - ys!i))
              \<le> (\<Sum> i<k. abs (?as!i * (xs!i - ys!i)))" by (rule sum_abs)
        also have "\<dots> \<le> (\<Sum> i<k. abs (?as!i))"
        proof (rule sum_mono, simp)
          fix i assume ik: "i < k"
          with k_lt have in_n: "i < n" by simp
          have "abs (?as!i * (xs!i - ys!i)) = abs (?as!i) * abs (xs!i - ys!i)"
            by (simp add: abs_mult)
          also have "\<dots> \<le> abs (?as!i) * 1"
            using xs01_i[OF in_n] ys01_i[OF in_n] by (intro mult_left_mono) auto
          finally show "abs (?as!i * (xs!i - ys!i)) \<le> abs (?as!i)" by simp
        qed
        finally show ?thesis .
      qed

      (* Drop abs on the prefix because weights are \<ge> 0. *)
      have prefix_nonneg: "\<And>i. i<k \<Longrightarrow> 0 \<le> ?as!i"
        using k_lt by (simp add: pow2_list_def)
      have abs_drop: "(\<Sum> i<k. abs (?as!i)) = (\<Sum> i<k. ?as!i)"
        by (rule sum.cong[OF refl]) (use prefix_nonneg in \<open>simp\<close>)

      (* Also |xs!k - ys!k| = 1 and weights are \<ge> 0. *)
      have abs1: "abs (xs ! k - ys ! k) = 1"
        using xs01_i[OF k_lt] ys01_i[OF k_lt] k_diff by auto
      have nonneg_k: "0 \<le> ?as ! k"
        using k_lt by (simp add: pow2_list_def)
      have abs_prod: "abs (?as!k * (xs ! k - ys ! k)) = ?as!k"
        by (simp add: abs_mult abs1 nonneg_k)

      (* pointwise bound: for every i<k, |a_i * (xs_i - ys_i)| \<le> |a_i| *)
      have term_le:
        "\<And>i. i < k \<Longrightarrow> abs (?as!i * (xs ! i - ys ! i)) \<le> abs (?as!i)"
      proof -
        fix i assume ik: "i < k"
        then have in_n: "i < n" using k_lt by simp
        have diff_le1: "abs (xs ! i - ys ! i) \<le> (1::int)"
          using xs01_i[OF in_n] ys01_i[OF in_n] by auto
        have "abs (?as!i * (xs ! i - ys ! i))
          = abs (?as!i) * abs (xs ! i - ys ! i)" by (simp add: abs_mult)
        also have "\<dots> \<le> abs (?as!i) * 1"
          using diff_le1 by (intro mult_left_mono) simp_all
        finally show "abs (?as!i * (xs ! i - ys ! i)) \<le> abs (?as!i)" by simp
      qed

(* now the chain for main_le goes through *)
      have main_le: "?as!k \<le> (\<Sum> i<k. ?as!i)"
      proof -
        have "?as!k = abs (?as!k * (xs ! k - ys ! k))" by (simp add: abs_prod)
        also have "\<dots> = abs (\<Sum> i<k. ?as!i * (xs ! i - ys ! i))" using eq_abs by simp
        also have "\<dots> \<le> (\<Sum> i<k. abs (?as!i * (xs ! i - ys ! i)))" by (rule sum_abs)
        also have "\<dots> \<le> (\<Sum> i<k. abs (?as!i))"
          by (intro sum_mono term_le) simp
        also have "\<dots> = (\<Sum> i<k. ?as!i)" by (simp add: abs_drop)
        finally show ?thesis .
      qed

      (* Rewrite both sides as powers of 2. *)
      have lhs_pow: "?as!k = (2::int)^k"
        using k_lt by (simp add: pow2_list_def)
      have rhs_pow: "(\<Sum> i<k. ?as!i) = (\<Sum> i<k. (2::int)^i)"
      proof (rule sum.cong[OF refl])
        fix i assume "i \<in> {..<k}"
        with k_lt have "i < n" by auto
        thus "?as!i = (2::int)^i" by (simp add: pow2_list_def)
      qed

      have "(2::int)^k \<le> (\<Sum> i<k. (2::int)^i)"
        using main_le by (simp add: lhs_pow rhs_pow)

      (* Final contradiction via closed form. *)
      hence "(2::int)^k \<le> (2::int)^k - 1"
        by (simp add: sum_pow2_int)
      thus False by linarith
    qed
  qed

(* length of the weight list is n, so the binders match *)
  have len_as[simp]: "length ?as = n" by (simp add: pow2_list_def)

  show ?thesis
    unfolding distinct_subset_sums_def
    by (simp; metis uniq)
qed
end
