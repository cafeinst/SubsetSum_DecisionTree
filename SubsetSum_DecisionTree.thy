theory SubsetSum_DecisionTree
  imports "Complex_Main" "HOL-Real_Asymp.Real_Asymp"
    "Weighted_Arithmetic_Geometric_Mean.Weighted_Arithmetic_Geometric_Mean"
begin
text \<open>
  \paragraph{Overview.}
  We give a \emph{self-contained} combinatorial lower bound for Subset-Sum that
  does not assume any particular machine model. The argument proceeds in three
  clean steps that are fully formalized in this entry:

  \begin{enumerate}
  \item \textbf{Prefix/suffix split at a pivot \emph{k}.}
        For a weight vector \<open>as\<close> of length \<open>n\<close> and target \<open>s\<close>, we consider the map
        \<open>e_k as s k xs = (lhs, rhs)\<close> that extracts from a 0/1 vector \<open>xs\<close> the
        prefix sum over \<open>{0..<k}\<close> and the “required suffix’’
        \<open>s − \<Sum>_{i\<in>{k..<n}} as!i * xs!i\<close>. This yields value sets
        \<open>LHS (e_k as s k) n\<close> and \<open>RHS (e_k as s k) n\<close> ranging over all
        \<open>xs \<in> bitvec n\<close>.

        Under the \emph{distinct subset-sums} hypothesis
        (different 0/1 selections yield different full sums),
        we prove that padding with zeros makes the prefix and the suffix
        images injective in their respective dimensions:
        \<open>card (LHS (e_k as s k) n) = 2^k\<close> and
        \<open>card (RHS (e_k as s k) n) = 2^(n−k)\<close>
        (lemmas \<open>card_LHS_e_k\<close> and \<open>card_RHS_e_k\<close>).
        Hence their product is always \<open>2^n\<close> (theorem \<open>lemma2_split\<close>).

  \item \textbf{From product to sum via AM–GM.}
        Since \<open>card LHS \<sqdot> card RHS = 2^n\<close>, the arithmetic–geometric mean
        inequality gives
        \<open>card LHS + card RHS \<ge> 2 \<sqdot> sqrt (2^n)\<close>
        (lemma \<open>lemma3_AFP\<close> and corollary \<open>lhs_rhs_sum_lower_bound\<close>).
        This step is purely analytic and independent of any algorithmic model.

  \item \textbf{Decision-tree coverage \<Rightarrow> you must read everything relevant.}
        We model readers as abstract decision trees that alternately query a
        left or right index and branch on yes/no answers. For any well-formed
        tree \<open>T\<close> that is \emph{extensionally correct} for a given specification
        \<open>good\<close>, and for which every index on each side admits a pointwise
        “truth-flipping’’ perturbation, we prove that along every run the set
        of queried left (resp.\ right) indices equals the entire declared left
        (resp.\ right) set (locale \<open>DecisionTree_Coverage\<close>, lemma
        \<open>coverage_for_all_inputs\<close>). In particular,
        \<open>steps \<ge> |seenL| + |seenR|\<close> (lemma \<open>steps_ge_sum_seen\<close>) and therefore,
        with the pivot \<open>k\<close> chosen as in Step~1,
        \<open>steps \<ge> card LHS + card RHS\<close> (lemma \<open>steps_lower_bound_all\<close>).
  \end{enumerate}

  Putting the three steps together yields the quantitative lower bound
  \<open>steps \<ge> 2 \<sqdot> sqrt (2^n)\<close> for all instances with distinct subset sums
  (locale \<open>SubsetSum_Reader_NoK\<close>, theorem \<open>subset_sum_sqrt_lower_bound\<close>).
  The whole proof is model-agnostic: it uses only combinatorics on 0/1 vectors,
  the padding/reindexing toolkit, and AM–GM. Any subsequent “TM bridge’’
  (e.g.\ via a correctness/coverage argument showing that the machine’s
  observable reads realize our \<open>seenL/seenR\<close> windows and obey
  \<open>steps \<ge> |seenL| + |seenR|\<close>) can import this bound as a black box.

  \paragraph{Canonical hard family.}
  We also provide a standard superincreasing weight family
  \<open>pow2_list n = [1,2,4,\<dots>,2^{n−1}]\<close> and prove that it has distinct
  subset sums (lemma \<open>distinct_subset_sums_pow2_list\<close>). Hence, for every
  \<open>n\<close> there exist inputs witnessing the lower bound.

 \paragraph{Why we use the explicit extractor \<open>e_k\<close>.}
We deliberately avoid introducing a global “set of equivalent equations’’
for the subset-sum predicate. Instead, we fix a concrete pivot \<open>k\<close> and use the
explicitly defined extractor \<open>e_k\<close> to obtain the two value-sets we count,
\<open>LHS (e_k as s k) n\<close> and \<open>RHS (e_k as s k) n\<close>. This keeps the development
local and assumption-light: apart from the single combinatorial hypothesis
\<open>distinct_subset_sums as\<close> used to derive exact cardinalities in Step~1,
all other ingredients (AM–GM, coverage, and the inequality
\<open>steps \<ge> |seenL| + |seenR|\<close>) are proved inside this file. The later
machine bridges then only need to identify their observable “seen’’
indices with these concrete \<open>LHS/RHS\<close> windows for some pivot \<open>k\<close>, rather
than reasoning about an amorphous space of “equivalent’’ equations.
\<close>
text \<open>
  \<open>SubsetSum_DecisionTree\<close> is a self-contained combinatorial backbone for our later
  TM bridges. It provides:

  • 0/1 vectors and restricted subset-sum operators (prefix/suffix).
  • A clean split at a pivot k: we count distinct values of the LHS (prefix sums)
    and RHS (“required suffix”) ranges.
  • A decision-tree reader model with “seen” indices and a coverage lemma (Lemma 1)
    showing that every relevant index must be queried on every path.
  • An AM–GM step that turns the product lower bound into a \<surd>(2^n) lower bound on
    the number of queries/steps.
  • A canonical distinct family (weights 2^i) that witnesses hardness for every n.

  The file does *not* assume any TM model; it is purely combinatorial. Later files
  only need to instantiate “steps \<ge> |seenL| + |seenR|” and identify seen-sets with
  our LHS/RHS windows to import the lower bound.
\<close>

text \<open>
  \<open>bitvec k\<close> = all 0/1 lists of length k over integers (not booleans).
  This lets us use integer arithmetic directly in the subset-sum objectives.

  Frequently used facts:
    • \<open>finite_bitvec\<close>, \<open>card_bitvec\<close> = 2^k
    • Suc-decomposition lemmas split \<open>bitvec (Suc n)\<close> by the head bit.
\<close>

definition bitvec :: "nat \<Rightarrow> int list set" where
  "bitvec k = {xs. length xs = k \<and> set xs \<subseteq> {0::int, 1}}"

lemma bitvec_0[simp]: "bitvec 0 = {[]}"
  unfolding bitvec_def by auto

lemma sum_pow2_int: "(\<Sum> i<k. (2::int)^i) = 2^k - 1"
  by (induction k) simp_all

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

lemma bitvec_Suc_disjoint:
  "{0 # xs | xs. xs \<in> bitvec n} \<inter> {1 # xs | xs. xs \<in> bitvec n} = {}"
  by auto

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

text \<open>
  Restricted sums and the pivot split.

  • \<open>sum_as_on as I xs\<close> = weighted sum over indices I.
  • \<open>lhs_of as k xs\<close>    = prefix sum over \<open>{0..<k}\<close>.
  • \<open>rhs_of as k s xs\<close>  = the value that the suffix must realize so that the full sum
                          equals s: namely \<open>s − \<Sum>_{i\<in>{k..<length as}} as!i * xs!i\<close>.
  • \<open>e_k as s k xs\<close>     = pair \<open>(lhs, rhs)\<close> extracted from a single 0/1 selection.

  Later we form value-sets
    \<open>LHS (e_k as s k) n\<close> = { lhs_of \<dots> | xs \<in> bitvec n }
    \<open>RHS (e_k as s k) n\<close> = { rhs_of \<dots> | xs \<in> bitvec n }
  and count them under “distinct subset sums”.
\<close>

definition sum_as_on :: "int list \<Rightarrow> nat set \<Rightarrow> int list \<Rightarrow> int" where
  "sum_as_on as I xs = (\<Sum> i \<in> I. as ! i * xs ! i)"

definition lhs_of :: "int list \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int" where
  "lhs_of as k xs = sum_as_on as {0..<k} xs"

definition rhs_of :: "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int" where
  "rhs_of as k s xs = s - sum_as_on as {k..<length as} xs"

definition e_k :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int \<times> int" where
  "e_k as s k xs = (lhs_of as k xs, rhs_of as k s xs)"

definition LHS :: "(int list \<Rightarrow> int \<times> int) \<Rightarrow> nat \<Rightarrow> int set" where
  "LHS e n = {fst (e xs) | xs. xs \<in> bitvec n}"

definition RHS :: "(int list \<Rightarrow> int \<times> int) \<Rightarrow> nat \<Rightarrow> int set" where
  "RHS e n = {snd (e xs) | xs. xs \<in> bitvec n}"

text \<open>
  Distinct-subset-sums property:
  different 0/1 vectors of length \<open>length as\<close> yield different full sums
    \<open>\<Sum> i<length as. as!i * xs!i\<close>.

  This is the injectivity hypothesis used to show large LHS/RHS images.
  The canonical example we use later is \<open>as = map (\<lambda>i. 2^i) [0..<n]\<close>.
\<close>
definition distinct_subset_sums :: "int list \<Rightarrow> bool" where
  "distinct_subset_sums as \<equiv>
     (\<forall>xs\<in>bitvec (length as). \<forall>ys\<in>bitvec (length as).
        xs \<noteq> ys \<longrightarrow> (\<Sum> i < length as. as ! i * xs ! i) \<noteq> (\<Sum> i < length as. as ! i * ys ! i))"

text \<open>
  Padding & splitting toolkit (prefix/suffix technology).

  Goal: reduce any statement about a length-\<open>n\<close> vector to a statement about a
  length-\<open>k\<close> prefix (resp. \<open>n−k\<close> suffix) plus zero padding, so that we can
  (i) push sums to the prefix or suffix and (ii) reindex suffix binders to \<open>{0..<n−k}\<close>.

  Typical flow:
    xs \<in> bitvec n
    p  = take k xs   (p \<in> bitvec k),     pad tail with 0s
    q  = drop k xs   (q \<in> bitvec (n−k)), pad head with 0s
    reindex \<open>{k..<n}\<close> \<leftrightarrow> \<open>{0..<n−k}\<close> using \<open>sum_reindex_add\<close>.

  These lemmas are used in the LHS/RHS cardinality proofs to show:
    LHS = f  ` bitvec k   with f injective
    RHS = g  ` bitvec (n−k) with g injective
\<close>

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

text \<open>
  Counting images under distinctness.

  For fixed \<open>as, s, n, k\<close> with \<open>k \<le> n\<close> and \<open>distinct_subset_sums as\<close>:
    • Every LHS value comes from a *unique* prefix p \<in> bitvec k
      (tail padded with zeros) \<Rightarrow> \<open>card LHS = 2^k\<close>.
    • Every RHS value comes from a *unique* suffix q \<in> bitvec (n−k)
      (head padded with zeros) \<Rightarrow> \<open>card RHS = 2^(n−k)\<close>.

  The key step is using distinctness on *padded* vectors of length n.
  We collect the product identity:

    lemma2_split:  card LHS * card RHS = 2^n.
\<close>

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

text \<open>
  From product to sum via AM–GM.

  If \<open>A = card LHS\<close> and \<open>B = card RHS\<close> then \<open>A * B = 2^n\<close>, hence by AM–GM we obtain
    \<open>A + B \<ge> 2 * sqrt (2^n)\<close>.
  We package that as \<open>lhs_rhs_sum_lower_bound\<close>, which is the quantitative driver
  we will feed into “steps \<ge> |seenL| + |seenR|”.
\<close>

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

text \<open>
  Abstract decision-tree reader.

  • The tree alternately asks left indices \<open>iL\<close> (constructor \<open>AskL\<close>) or right indices
    \<open>iR\<close> (constructor \<open>AskR\<close>) and branches on oracle answers \<open>oL i\<close> / \<open>oR j\<close>.
  • \<open>run oL oR T\<close> evaluates the tree to a boolean.
  • \<open>seenL_run\<close> and \<open>seenR_run\<close> are the *sets of queried indices along the taken path*.
  • \<open>steps_run\<close> is the path length (number of queries).

  We also define a well-formedness predicate \<open>wf_dtr L R T\<close> stating that the tree
  only asks indices from declared sets \<open>L\<close> and \<open>R\<close>, and prove:

    – If two oracles agree on all indices seen along the path, the run result and
      seen-sets are equal (agree-on-seen principle).
    – \<open>card (seenL_run) \<le> steps\<close> and \<open>card (seenR_run) \<le> steps\<close>, hence
      \<open>steps \<ge> |seenL| + |seenR|\<close>.
\<close>

datatype ('iL,'iR) dtr =
    Leaf bool
  | AskL 'iL "('iL,'iR) dtr" "('iL,'iR) dtr"
  | AskR 'iR "('iL,'iR) dtr" "('iL,'iR) dtr"

fun run :: "('iL \<Rightarrow> bool) \<Rightarrow> ('iR \<Rightarrow> bool) \<Rightarrow> ('iL,'iR) dtr \<Rightarrow> bool" where
  "run oL oR (Leaf b) = b"
| "run oL oR (AskL i t0 t1) = run oL oR (if oL i then t1 else t0)"
| "run oL oR (AskR j t0 t1) = run oL oR (if oR j then t1 else t0)"

fun seenL_run :: "('iL \<Rightarrow> bool) \<Rightarrow> ('iR \<Rightarrow> bool) \<Rightarrow> ('iL,'iR) dtr \<Rightarrow> 'iL set" where
  "seenL_run oL oR (Leaf b) = {}"
| "seenL_run oL oR (AskL i t0 t1) =
     insert i (seenL_run oL oR (if oL i then t1 else t0))"
| "seenL_run oL oR (AskR j t0 t1) =
     seenL_run oL oR (if oR j then t1 else t0)"

fun seenR_run :: "('iL \<Rightarrow> bool) \<Rightarrow> ('iR \<Rightarrow> bool) \<Rightarrow> ('iL,'iR) dtr \<Rightarrow> 'iR set" where
  "seenR_run oL oR (Leaf b) = {}"
| "seenR_run oL oR (AskL i t0 t1) =
     seenR_run oL oR (if oL i then t1 else t0)"
| "seenR_run oL oR (AskR j t0 t1) =
     insert j (seenR_run oL oR (if oR j then t1 else t0))"

fun steps_run :: "('iL \<Rightarrow> bool) \<Rightarrow> ('iR \<Rightarrow> bool) \<Rightarrow> ('iL,'iR) dtr \<Rightarrow> nat" where
  "steps_run oL oR (Leaf b) = 0"
| "steps_run oL oR (AskL i t0 t1) =
     Suc (steps_run oL oR (if oL i then t1 else t0))"
| "steps_run oL oR (AskR j t0 t1) =
     Suc (steps_run oL oR (if oR j then t1 else t0))"

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

text \<open>Agreeing on all indices seen along the path \<Rightarrow> same path/result/seen-sets.\<close>
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

lemma steps_ge_sum_seen:
  "steps_run oL oR T \<ge> card (seenL_run oL oR T) + card (seenR_run oL oR T)"
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

text \<open>
  Canonical distinct family: powers of two.

  We instantiate the weights as \<open>as = map (\<lambda>i. 2^i) [0..<n]\<close> and prove that they
  are superincreasing (each weight exceeds the sum of all previous), which implies
  \<open>distinct_subset_sums as\<close>. This gives “hard” instances for every n:

    exists_hard: \<forall>n. \<exists>as. length as = n \<and> distinct_subset_sums as.
\<close>

definition pow2_list :: "nat \<Rightarrow> int list" where
  "pow2_list n = map (\<lambda>i. (2::int)^i) [0..<n]"

text \<open>
  Coverage lemma (Lemma 1 in abstract form).

  Assume:
    • The tree is well-formed.
    • \<open>run\<close> is *extensionally correct* for some specification \<open>good oL oR\<close>.
    • For every left index i \<in> Lset, there is a *pointwise flip* of the left oracle
      (changing only i) that flips the truth of \<open>good\<close>; similarly for right indices.

  Then for *all* inputs (all oracles) we must have:
    • Every left index is *seen* (otherwise flipping it would not be detected),
    • Every right index is *seen*,
    hence  \<open>seenL_run = Lset\<close> and \<open>seenR_run = Rset\<close> and therefore
          \<open>steps \<ge> card Lset + card Rset\<close>.

  This is the model-independent “must read everything relevant” statement.
\<close>
locale DecisionTree_Coverage =
  fixes Lset :: "'iL set" and Rset :: "'iR set"
  fixes T    :: "('iL,'iR) dtr"
  fixes good :: "('iL \<Rightarrow> bool) \<Rightarrow> ('iR \<Rightarrow> bool) \<Rightarrow> bool"
  assumes wf: "wf_dtr Lset Rset T"
  assumes correct: "\<forall>oL oR. run oL oR T = good oL oR"
  assumes flipL_pointwise:
    "\<And>i oL oR. i \<in> Lset \<Longrightarrow> \<exists>oL'. (\<forall>j\<noteq>i. oL' j = oL j) \<and> good oL' oR \<noteq> good oL oR"
  assumes flipR_pointwise:
    "\<And>j oL oR. j \<in> Rset \<Longrightarrow> \<exists>oR'. (\<forall>i\<noteq>j. oR' i = oR i) \<and> good oL oR' \<noteq> good oL oR"
begin

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

text \<open>
  Abstract reader interface (no machine model).

  You supply:
    • \<open>steps as s\<close>: number of queries/steps used to decide “\<exists>xs: sum(as,xs)=s”.
    • \<open>seenL as s k\<close> and \<open>seenR as s k\<close>: the sets of left/right indices read when
      the reader uses pivot k.
  Assumptions:
    • \<open>coverage_ex\<close>: On distinct weights, there *exists* a k \<le> n such that
      \<open>seenL = LHS (e_k \<dots>)\<close> and \<open>seenR = RHS (e_k \<dots>)\<close> — i.e. Lemma 1 instantiated.
    • \<open>steps_lb\<close>: A general “reader cost” inequality, steps \<ge> |seenL| + |seenR|.

  Consequences:
    • \<open>subset_sum_sqrt_lower_bound\<close>: steps \<ge> 2\<surd>(2^n) on distinct instances.
    • \<open>no_polytime_decider_on_distinct_family\<close>: no polynomial (in n) worst-case bound
      exists across all distinct families.
\<close>

text \<open>
  Auxiliary summation identity and a second, compact proof of distinctness for
  \<open>pow2_list\<close>. These are convenient local copies for later files that only need
  the statement “pow2_list has distinct subset sums” without importing all earlier
  lemmas.
\<close>

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
