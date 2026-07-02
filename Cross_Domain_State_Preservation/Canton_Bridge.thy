(*
  Title:      Cross_Domain_State_Preservation/Canton_Bridge.thy
  Author:     Jinwook Kim (Jay) <jay@oraclizer.io>
  Maintainer: Jinwook Kim (Jay) <jay@oraclizer.io>
  License:    BSD

  Cross-Domain State Preservation Functor -- Authenticated Cross-Domain State

  Functor_Laws.thy instantiates the authenticated-data-structure interface of
  Lochbihler and Maric (ADS_Functor.Merkle_Interface) and uses its lemmas in a
  load-bearing way.  This theory develops the authenticated layer further, over
  public components:

    * Composite functor laws.  The authenticated extraction map is a functor
      from the ADS blinding preorder to the cross-domain refinement preorder.
      We prove the category axioms for this composite (identity, composition,
      associativity), and the associativity of the lifted merge/join algebra.

    * Sequence-level authenticity.  The single-step soundness theorems are
      generalised to whole synchronization sequences: a path of blindings, and
      an n-ary fold of merges.

    * Concrete and recursive instantiation.  The authenticated_state structure
      is instantiated on the ADS blindable-position functor
      (ADS_Functor.ADS_Construction), on the top-level commitment of the Canton
      transaction tree, and on a recursive model of that tree built from the
      public rose-tree Merkle machinery of ADS_Functor.Canton_Transaction_Tree.
      The recursive model is structurally faithful with concrete leaf content in
      place of the opaque content types of the public Canton model; this is a
      model-fidelity boundary, not a proof gap, and no axiom relates the opaque
      Canton types to the regulatory model.
*)

theory Canton_Bridge
  imports
    Functor_Laws
    "ADS_Functor.ADS_Construction"
    "ADS_Functor.Canton_Transaction_Tree"
begin

section \<open>Auxiliary list predicate for synchronization sequences\<close>

text \<open>A blinding path: each element of the list is a blinding of its successor.
  As blindings narrow what is revealed, the last element is the most-revealed
  view of the sequence and every earlier element is a partial view of it.\<close>

definition blinding_path :: "('d \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> 'd list \<Rightarrow> bool" where
  "blinding_path bl xs \<longleftrightarrow> (\<forall>i. Suc i < length xs \<longrightarrow> bl (xs ! i) (xs ! Suc i))"


section \<open>Composite functor laws: cross-domain preservation after the ADS Merkle functor\<close>

text \<open>
  Inside @{locale authenticated_state} the ADS layer supplies a thin category:
  objects are authenticated values, and the unique morphism \<open>a \<rightarrow> b\<close> is the
  blinding relation \<^term>\<open>bo a b\<close>, a preorder (reflexive and transitive by the
  Merkle interface).  The cross-domain layer supplies another thin category:
  objects are global states and the morphism \<open>s \<rightarrow> s'\<close> is \<^term>\<open>state_refines s s'\<close>,
  also a preorder.  The extraction map \<^term>\<open>extract_map\<close> is the composite functor
  from the first category to the second: it sends a value to the state it
  extracts to, and a blinding morphism to a refinement morphism.  The next four
  results are the category axioms of this composite functor together with the
  associativity of the lifted merge (join) algebra.
\<close>

context authenticated_state
begin

text \<open>Identity is preserved: the identity (blinding) morphism on \<open>a\<close>, which exists
  by reflexivity of \<^term>\<open>bo\<close>, is sent to the identity (refinement) morphism on the
  extracted state.\<close>

lemma cdsp_ads_id:
  assumes "extract_map a = Some sa"
  shows "bo a a \<and> valid_state sa \<and> state_refines sa sa"
  using mk.reflp extract_preserves_validity[OF assms] state_refines_refl
  by (simp add: reflp_def)

text \<open>The functor's action on a single morphism: a blinding \<open>a \<rightarrow> b\<close> is sent to a
  refinement \<open>extract a \<rightarrow> extract b\<close>, with both extracted states valid.  This is
  @{thm [source] blinded_view_preserves_validity} with the validity hypothesis on
  \<open>b\<close> discharged internally from @{thm [source] extract_preserves_validity}, so the
  morphism map is total on the blinding preorder.\<close>

lemma cdsp_ads_morphism:
  assumes bo: "bo a b" and eb: "extract_map b = Some sb"
  shows "\<exists>sa. extract_map a = Some sa \<and> valid_state sa \<and> valid_state sb \<and> state_refines sa sb"
proof -
  have hab: "h a = h b" using bo_hash_eq[OF bo] .
  obtain sa where ea: "extract_map a = Some sa" and sr: "state_refines sa sb"
    using extract_under_blinding[OF hab bo eb] by blast
  have "valid_state sa" using extract_preserves_validity[OF ea] .
  moreover have "valid_state sb" using extract_preserves_validity[OF eb] .
  ultimately show ?thesis using ea sr by blast
qed

text \<open>Composition is preserved (closed).  Two composable blinding morphisms
  \<open>a \<rightarrow> b\<close> and \<open>b \<rightarrow> c\<close> compose in the source category to \<open>a \<rightarrow> c\<close> (transitivity
  of \<^term>\<open>bo\<close>), and the functor sends the composite to the composite of the images
  \<open>extract a \<rightarrow> extract b \<rightarrow> extract c\<close> (transitivity of \<^term>\<open>state_refines\<close>).  This
  is the cross-domain, authenticated analogue of @{thm [source] preservation_compose}.\<close>

theorem cdsp_ads_compose:
  assumes ab: "bo a b" and bc: "bo b c" and ec: "extract_map c = Some sc"
  shows "bo a c
       \<and> (\<exists>sa sb. extract_map a = Some sa \<and> extract_map b = Some sb
            \<and> valid_state sa \<and> valid_state sb \<and> valid_state sc
            \<and> state_refines sa sb \<and> state_refines sb sc \<and> state_refines sa sc)"
proof -
  have boac: "bo a c" using mk.transp ab bc by (metis transpD)
  obtain sb where eb: "extract_map b = Some sb"
    and srbc: "state_refines sb sc" and vsb: "valid_state sb" and vsc: "valid_state sc"
    using cdsp_ads_morphism[OF bc ec] by blast
  obtain sa where ea: "extract_map a = Some sa"
    and srab: "state_refines sa sb" and vsa: "valid_state sa"
    using cdsp_ads_morphism[OF ab eb] by blast
  have srac: "state_refines sa sc" using state_refines_trans[OF srab srbc] .
  show ?thesis using boac ea eb vsa vsb vsc srab srbc srac by blast
qed

text \<open>Associativity.  Three composable blinding morphisms yield the same composite
  \<open>a \<rightarrow> d\<close> regardless of the bracketing; in this thin category the composite
  morphism is the relation \<^term>\<open>bo a d\<close> (and its image \<^term>\<open>state_refines sa sd\<close>),
  which is bracketing-independent because the relations are propositional.  The
  substantive associativity of the lifted merge appears in the
  merge-associativity result below.\<close>

theorem cdsp_ads_assoc:
  assumes ab: "bo a b" and bc: "bo b c" and cd: "bo c d"
    and ed: "extract_map d = Some sd"
  shows "bo a d \<and> (\<exists>sa. extract_map a = Some sa \<and> valid_state sa \<and> state_refines sa sd)"
proof -
  have "bo b d" using mk.transp bc cd by (metis transpD)
  hence boad: "bo a d" using mk.transp ab by (metis transpD)
  obtain sa where "extract_map a = Some sa" "valid_state sa" "state_refines sa sd"
    using cdsp_ads_morphism[OF boad ed] by blast
  thus ?thesis using boad by blast
qed

text \<open>The functor's action on the merge (join) product: a merge of two views is
  sent to a join of the two extracted states, with the joined state valid and
  refining each input.  This lifts @{thm [source] extract_respects_merging} to a
  theorem carrying validity, and is exactly
  @{thm [source] authenticated_preservation_soundness} read as the product map of
  the composite functor.\<close>

lemma cdsp_ads_merge:
  assumes mab: "m a b = Some ab"
    and ea: "extract_map a = Some sa" and eb: "extract_map b = Some sb"
  shows "\<exists>sab. extract_map ab = Some sab \<and> valid_state sab
            \<and> state_refines sa sab \<and> state_refines sb sab"
  using authenticated_preservation_soundness[OF mab ea eb]
  by blast

text \<open>Associativity of the lifted merge/join algebra.  The ADS merge is associative
  (Merkle-interface axiom @{thm [source] mk.assoc}), so the three-way combination of
  authenticated views is independent of the bracketing: both \<open>(a \<bullet> b) \<bullet> c\<close> and
  \<open>a \<bullet> (b \<bullet> c)\<close> land on the same merged value, hence (the extraction being a
  function) on the same joined state.  This is the substantive ``associativity
  preserved'' of the composite functor.  Commutativity and idempotence of the
  lifted combination descend directly from the interface laws
  (@{thm [source] mk.commute}, @{thm [source] mk.idem}) with the extraction a
  function; associativity is the one law that needs the rearrangement below,
  so it is the law recorded as a theorem.\<close>

theorem cdsp_ads_merge_assoc:
  assumes mab: "m a b = Some ab" and mabc: "m ab c = Some abc"
  shows "\<exists>bc. m b c = Some bc \<and> m a bc = Some abc"
proof -
  have "m b c \<bind> m a = m a b \<bind> m c" by (rule mk.assoc[symmetric])
  also have "m a b \<bind> m c = m c ab" using mab by simp
  also have "m c ab = m ab c" by (rule mk.commute)
  also have "\<dots> = Some abc" using mabc by simp
  finally have "m b c \<bind> m a = Some abc" .
  thus ?thesis by (cases "m b c") auto
qed

end


section \<open>Authenticity preserved along whole synchronization sequences\<close>

text \<open>
  Four authenticity properties are shown to hold not across a single blinding or
  merge step but along the \emph{whole} synchronization sequence:

    \<^enum> \<^bold>\<open>validity\<close> --- every view in the sequence extracts to a valid state,
        along a blinding path (theorem \<open>sequence_authenticity_preservation\<close>)
        and along a merge fold (theorem \<open>sequence_merge_soundness\<close>);
    \<^enum> \<^bold>\<open>need-to-know (refinement)\<close> --- every view is a partial view refining the
        most-revealed endpoint (theorem \<open>sequence_authenticity_preservation\<close>,
        extended to arbitrary blinding-step reachability by corollary
        \<open>reachable_view_authenticity\<close>); dually, every contributor to a merge
        fold refines the combined view (theorem \<open>sequence_merge_soundness\<close>);
    \<^enum> \<^bold>\<open>hash soundness\<close> --- the whole sequence commits to one authenticating root,
        in both the blinding direction (theorem \<open>blinding_path_hash_soundness\<close>)
        and the merge direction (theorem \<open>merge_seq_hash\<close>);
    \<^enum> \<^bold>\<open>inclusion integrity\<close> --- theorem \<open>sequence_inclusion_integrity\<close>.

  \<^bold>\<open>Scope qualifier (read carefully).\<close>  The inclusion result is \<^emph>\<open>state-level\<close>: it
  is about \<^emph>\<open>revealed holdings\<close> --- a holding exhibited by any view in the sequence
  is genuinely present in the endpoint with the same regulatory state, and no view
  fabricates a chain the endpoint does not authenticate.  This is \<^emph>\<open>not\<close> a claim about
  the \<^emph>\<open>concrete Merkle inclusion path\<close> (the witness list authenticating a leaf against
  a root hash); that construction lives in \<open>ADS_Functor.Inclusion_Proof_Construction\<close>
  and belongs to the concrete recursive-tree layer, not to this abstract layer.
\<close>

context authenticated_state
begin

subsection \<open>Need-to-know blinding along a sequence\<close>

text \<open>Along a blinding path, an earlier (more blinded) element blinds any later
  element: the blinding relation is monotone along the path by transitivity.\<close>

lemma blinding_path_mono:
  assumes path: "blinding_path bo xs" and ij: "i \<le> j" and j: "j < length xs"
  shows "bo (xs ! i) (xs ! j)"
proof -
  from ij obtain d where jd: "j = i + d" using le_Suc_ex by blast
  from j jd show ?thesis unfolding jd
  proof (induction d arbitrary: j)
    case 0
    show ?case using mk.reflp by (simp add: reflp_def)
  next
    case (Suc d)
    have lt: "i + d < length xs" using Suc.prems by simp
    have ih: "bo (xs ! i) (xs ! (i + d))" using Suc.IH lt by simp
    have step: "bo (xs ! (i + d)) (xs ! Suc (i + d))"
      using path Suc.prems unfolding blinding_path_def by simp
    show ?case using mk.transp ih step by (metis transpD add_Suc_right)
  qed
qed

text \<open>
  Sequence-level need-to-know preservation.  Given a synchronization sequence
  presented as a blinding path whose most-revealed endpoint (the last element)
  extracts to a valid cross-domain state, \emph{every} intermediate view extracts
  to a valid state that refines the endpoint.  Authenticity (validity together
  with the refinement guarantee of a partial view) is preserved along the whole
  sequence, not merely across one blinding step.  This generalises
  @{thm [source] blinded_view_preserves_validity}.
\<close>

theorem sequence_authenticity_preservation:
  assumes path: "blinding_path bo xs" and ne: "xs \<noteq> []"
    and elast: "extract_map (last xs) = Some s_last"
    and i: "i < length xs"
  shows "\<exists>s\<^sub>i. extract_map (xs ! i) = Some s\<^sub>i \<and> valid_state s\<^sub>i \<and> state_refines s\<^sub>i s_last"
proof -
  have le: "i \<le> length xs - 1" using i by simp
  have lt: "length xs - 1 < length xs" using ne by (cases xs) auto
  have "bo (xs ! i) (xs ! (length xs - 1))"
    using blinding_path_mono[OF path le lt] .
  also have "xs ! (length xs - 1) = last xs" using ne by (simp add: last_conv_nth)
  finally have "bo (xs ! i) (last xs)" .
  from cdsp_ads_morphism[OF this elast] show ?thesis by blast
qed

text \<open>
  Hash soundness along the sequence.  Every view in a blinding path commits to the
  same root hash as the most-revealed endpoint; a blinded view cannot present a
  different root.  This is the sequence-level form of the ADS guarantee
  @{thm [source] bo_hash_eq}: along the whole synchronization sequence there is a
  single authenticating root, so any inclusion claim made anywhere along the
  sequence is checked against the same commitment.
\<close>

theorem blinding_path_hash_soundness:
  assumes path: "blinding_path bo xs" and ne: "xs \<noteq> []" and i: "i < length xs"
  shows "h (xs ! i) = h (last xs)"
proof -
  have le: "i \<le> length xs - 1" using i by simp
  have lt: "length xs - 1 < length xs" using ne by (cases xs) auto
  have "bo (xs ! i) (xs ! (length xs - 1))" using blinding_path_mono[OF path le lt] .
  moreover have "xs ! (length xs - 1) = last xs" using ne by (simp add: last_conv_nth)
  ultimately show ?thesis using bo_hash_eq by simp
qed

text \<open>
  Inclusion-proof integrity along the sequence.  Every holding revealed by any view
  in the sequence is genuinely included in the most-revealed endpoint with the same
  regulatory state, and the revealing chain is connected in the endpoint.  No view
  along the sequence can therefore exhibit a holding that the endpoint does not
  authenticate.  Together with @{thm [source] blinding_path_hash_soundness} (one
  root for the whole sequence) this is the state-level reading of inclusion-proof
  integrity preserved across the synchronization sequence.

  At this abstract layer inclusion reduces to the refinement guarantee
  (@{thm [source] sequence_authenticity_preservation}) read through
  @{thm [source] state_refines_def}: a partial view's revealed leaves are exactly the
  leaves it shares with the endpoint.  The concrete Merkle inclusion-path machinery
  lives one level down in \<open>ADS_Functor.Inclusion_Proof_Construction\<close>.
\<close>

theorem sequence_inclusion_integrity:
  assumes path: "blinding_path bo xs" and ne: "xs \<noteq> []"
    and elast: "extract_map (last xs) = Some s_last"
    and i: "i < length xs" and ei: "extract_map (xs ! i) = Some s\<^sub>i"
    and rev: "get_reg_state s\<^sub>i c aid = Some r"
  shows "get_reg_state s_last c aid = Some r \<and> c \<in> connected_chains s_last aid"
proof -
  obtain s' where es': "extract_map (xs ! i) = Some s'" and sr: "state_refines s' s_last"
    using sequence_authenticity_preservation[OF path ne elast i] by blast
  from es' ei have eq: "s' = s\<^sub>i" by simp
  have conn: "c \<in> connected_chains s\<^sub>i aid"
    using rev unfolding connected_chains_def asset_exists_def
      get_reg_state_def get_asset_state_def by (auto split: option.splits)
  have "c \<in> connected_chains s_last aid
        \<and> get_reg_state s\<^sub>i c aid = get_reg_state s_last c aid"
    using sr eq conn unfolding state_refines_def by metis
  thus ?thesis using rev by simp
qed

text \<open>The same guarantee phrased over the reflexive-transitive closure: any view
  reachable from \<open>b\<close> by any number of blinding steps extracts to a valid state
  refining \<open>b\<close>.  (The closure collapses because \<^term>\<open>bo\<close> is already a preorder,
  which is precisely why arbitrary-length sequences add no new obligation.)\<close>

corollary reachable_view_authenticity:
  assumes reach: "bo\<^sup>*\<^sup>* a b" and eb: "extract_map b = Some sb"
  shows "\<exists>sa. extract_map a = Some sa \<and> valid_state sa \<and> state_refines sa sb"
proof -
  from reach have "bo a b"
  proof (induction rule: rtranclp_induct)
    case base
    show ?case using mk.reflp by (simp add: reflp_def)
  next
    case (step y z)
    show ?case using mk.transp step.IH step.hyps(2) by (metis transpD)
  qed
  from cdsp_ads_morphism[OF this eb] show ?thesis by blast
qed

subsection \<open>Re-revealing merge along a sequence\<close>

text \<open>The n-ary right fold of the (locale) merge along a non-empty sequence of
  authenticated views.  It is defined with the locale merge \<^term>\<open>m\<close> fixed, so its
  induction principle keeps \<^term>\<open>m\<close> in place (a theory-level fold parameterised by
  the merge would generalise it away under induction).\<close>

fun merge_seq :: "'d list \<Rightarrow> 'd option" where
  "merge_seq [] = None"
| "merge_seq [x] = Some x"
| "merge_seq (x # y # ys) =
     (case merge_seq (y # ys) of None \<Rightarrow> None | Some z \<Rightarrow> m x z)"

text \<open>A single merge preserves the common hash, since each input blinds to the
  merge and blinding respects hashes.\<close>

lemma merge_preserves_hash:
  assumes "m a b = Some ab"
  shows "h ab = h a"
proof -
  have "bo a ab" using mk.join assms by blast
  thus ?thesis using bo_hash_eq by simp
qed

text \<open>
  Sequence-level hash preservation for the merge fold.  Combining a whole
  hash-compatible sequence of partial views yields a value with that same common
  hash: re-revealing along the sequence never changes the authenticating root.
  This is the merge-direction companion of
  @{thm [source] blinding_path_hash_soundness} (which covers the blinding
  direction), so along either form of synchronization sequence the root hash is
  preserved.
\<close>

theorem merge_seq_hash:
  assumes "merge_seq xs = Some r" and "xs \<noteq> []"
    and "\<forall>x \<in> set xs. h x = h (hd xs)"
  shows "h r = h (hd xs)"
  using assms
proof (induction xs rule: merge_seq.induct)
  case (3 x y ys)
  obtain z where z: "merge_seq (y # ys) = Some z" and mxz: "m x z = Some r"
    using "3.prems"(1) by (auto split: option.splits)
  have "h r = h x" using merge_preserves_hash[OF mxz] .
  thus ?case by simp
qed simp_all

text \<open>
  Sequence-level merging soundness.  A whole synchronization sequence of partial
  authenticated views over the same committed object (all sharing a hash) folds
  into a single combined view that extracts to a valid cross-domain state
  refining every contributor.  This is the n-ary generalisation of
  @{thm [source] authenticated_preservation_soundness}: re-revealing along the
  entire sequence preserves validity and reconstructs a consistent joint view.
\<close>

theorem sequence_merge_soundness:
  "\<lbrakk> xs \<noteq> []; \<forall>x \<in> set xs. \<exists>s. extract_map x = Some s;
     \<forall>x \<in> set xs. h x = h (hd xs) \<rbrakk>
   \<Longrightarrow> \<exists>ab s. merge_seq xs = Some ab \<and> extract_map ab = Some s \<and> valid_state s
            \<and> (\<forall>x \<in> set xs. \<exists>sx. extract_map x = Some sx \<and> state_refines sx s)"
proof (induction xs rule: merge_seq.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  obtain sx where ex: "extract_map x = Some sx" using "2.prems" by auto
  have "valid_state sx" using extract_preserves_validity[OF ex] .
  thus ?case using ex state_refines_refl by auto
next
  case (3 x y ys)
  have ne_rest: "(y # ys) \<noteq> []" by simp
  have hx: "\<And>w. w \<in> set (y # ys) \<Longrightarrow> h w = h x"
    using "3.prems"(3) by auto
  have hrest: "\<forall>w \<in> set (y # ys). h w = h (hd (y # ys))" using hx by auto
  have erest: "\<forall>w \<in> set (y # ys). \<exists>s. extract_map w = Some s"
    using "3.prems"(2) by auto
  obtain z sz where mz: "merge_seq (y # ys) = Some z"
    and ez: "extract_map z = Some sz" and vz: "valid_state sz"
    and refz: "\<forall>w \<in> set (y # ys). \<exists>sw. extract_map w = Some sw \<and> state_refines sw sz"
    using "3.IH"[OF ne_rest erest hrest] by blast
  obtain sx where ex: "extract_map x = Some sx" using "3.prems"(2) by auto
  have hz: "h z = h x"
  proof -
    have "h z = h (hd (y # ys))" using merge_seq_hash[OF mz ne_rest hrest] .
    thus ?thesis using hx by simp
  qed
  have "\<exists>ab. m x z = Some ab"
    using hz mk.merge_respects_hashes[of x z] by simp
  then obtain xz where mxz: "m x z = Some xz" by blast
  have mseq: "merge_seq (x # y # ys) = Some xz" using mz mxz by simp
  obtain sxz where exz: "extract_map xz = Some sxz" and vxz: "valid_state sxz"
    and rx: "state_refines sx sxz" and rz: "state_refines sz sxz"
    using authenticated_preservation_soundness[OF mxz ex ez] by blast
  have "\<forall>w \<in> set (x # y # ys). \<exists>sw. extract_map w = Some sw \<and> state_refines sw sxz"
  proof
    fix w assume "w \<in> set (x # y # ys)"
    then consider "w = x" | "w \<in> set (y # ys)" by auto
    then show "\<exists>sw. extract_map w = Some sw \<and> state_refines sw sxz"
    proof cases
      case 1
      then show ?thesis using ex rx by blast
    next
      case 2
      then obtain sw where "extract_map w = Some sw" and "state_refines sw sz"
        using refz by blast
      then show ?thesis using state_refines_trans[OF _ rz] by blast
    qed
  qed
  then show ?case using mseq exz vxz by blast
qed

end


section \<open>Instantiation on the ADS blindable-position functor\<close>

text \<open>
  We instantiate @{locale authenticated_state} on a concrete ADS construction:
  the blindable-position functor of @{theory ADS_Functor.ADS_Construction} applied
  to the Oraclizer Merkle interface @{thm [source] merkle_interface_auth}.  The
  carrier is @{typ \<open>(reg_state \<times> chain_id set, reg_state) blindable\<^sub>m\<close>}: an
  authenticated datum is either \<^term>\<open>Unblinded (r, P)\<close> (the fully revealed
  consensus state \<open>r\<close> with revealed-chain set \<open>P\<close>) or \<^term>\<open>Blinded x\<close> (a hash-only
  commitment that reveals nothing).  The blindable hash, blinding order and merge
  are inherited from the ADS construction; the Merkle-interface obligation is
  discharged by @{thm [source] merkle_blindable} from
  @{thm [source] merkle_interface_auth}, so no new interface proof is needed.
\<close>

text \<open>The empty extracted view does not depend on the (unreachable) consensus
  label, so all hash-only commitments extract to the same state.\<close>

lemma auth_state_empty_eq: "auth_state r {} = auth_state r' {}"
  by (simp add: auth_state_def)

text \<open>Extraction: a revealed datum yields its cross-domain state; a hash-only
  commitment yields the empty (no-chains) view, which is valid and refines every
  state.  The commitment must still extract to a state -- a blinding of a value
  must itself be extractable -- so it maps to the empty view rather than to
  \<^term>\<open>None\<close>.\<close>

fun bl_extract :: "(reg_state \<times> chain_id set, reg_state) blindable\<^sub>m \<Rightarrow> global_state option" where
  "bl_extract (Unblinded a) = Some (auth_state (fst a) (snd a))"
| "bl_extract (Blinded _)   = Some (auth_state ACTIVE {})"

interpretation oss_blindable:
  authenticated_state
    "hash_blindable auth_hash"
    "blinding_of_blindable auth_hash auth_bo"
    "merge_blindable auth_hash auth_merge"
    bl_extract
proof (rule authenticated_state.intro)
  show "merkle_interface (hash_blindable auth_hash)
          (blinding_of_blindable auth_hash auth_bo) (merge_blindable auth_hash auth_merge)"
    by (rule merkle_blindable[OF merkle_interface_auth])
next
  show "authenticated_state_axioms (hash_blindable auth_hash)
          (blinding_of_blindable auth_hash auth_bo) (merge_blindable auth_hash auth_merge) bl_extract"
  proof
    \<comment> \<open>extract respects merging\<close>
    fix a b ab sa sb
    assume Hab: "hash_blindable auth_hash a = hash_blindable auth_hash b"
       and Mab: "merge_blindable auth_hash auth_merge a b = Some ab"
       and ea: "bl_extract a = Some sa" and eb: "bl_extract b = Some sb"
    show "\<exists>sab. bl_extract ab = Some sab \<and> state_join sa sb sab"
    proof (cases a)
      case (Unblinded p) note A = this
      show ?thesis
      proof (cases b)
        case (Unblinded q) note B = this
        have fp: "fst p = fst q" using Hab by (simp add: A B auth_hash_def)
        have ab_eq: "ab = Unblinded (fst p, snd p \<union> snd q)"
          using Mab fp by (simp add: A B auth_merge_def)
        have sa_eq: "sa = auth_state (fst p) (snd p)" using ea by (simp add: A)
        have sb_eq: "sb = auth_state (fst p) (snd q)" using eb fp by (simp add: B)
        have "bl_extract ab = Some (auth_state (fst p) (snd p \<union> snd q))" by (simp add: ab_eq)
        moreover have "state_join sa sb (auth_state (fst p) (snd p \<union> snd q))"
          unfolding sa_eq sb_eq by (rule state_join_auth)
        ultimately show ?thesis by blast
      next
        case (Blinded y) note B = this
        have ab_eq: "ab = Unblinded p" using Mab Hab by (simp add: A B auth_hash_def)
        have sa_eq: "sa = auth_state (fst p) (snd p)" using ea by (simp add: A)
        have sb_eq: "sb = auth_state ACTIVE {}" using eb by (simp add: B)
        have "bl_extract ab = Some (auth_state (fst p) (snd p))" by (simp add: ab_eq)
        moreover have "state_join sa sb (auth_state (fst p) (snd p))"
          unfolding sa_eq sb_eq
          using state_join_auth[of "fst p" "snd p" "{}"] auth_state_empty_eq[of ACTIVE "fst p"]
          by simp
        ultimately show ?thesis by blast
      qed
    next
      case (Blinded x) note A = this
      show ?thesis
      proof (cases b)
        case (Unblinded q) note B = this
        have ab_eq: "ab = Unblinded q" using Mab Hab by (simp add: A B auth_hash_def)
        have sa_eq: "sa = auth_state ACTIVE {}" using ea by (simp add: A)
        have sb_eq: "sb = auth_state (fst q) (snd q)" using eb by (simp add: B)
        have "bl_extract ab = Some (auth_state (fst q) (snd q))" by (simp add: ab_eq)
        moreover have "state_join sa sb (auth_state (fst q) (snd q))"
          unfolding sa_eq sb_eq
          using state_join_auth[of "fst q" "{}" "snd q"] auth_state_empty_eq[of ACTIVE "fst q"]
          by simp
        ultimately show ?thesis by blast
      next
        case (Blinded y) note B = this
        have ab_eq: "ab = Blinded y" using Mab Hab by (simp add: A B)
        have sa_eq: "sa = auth_state ACTIVE {}" using ea by (simp add: A)
        have sb_eq: "sb = auth_state ACTIVE {}" using eb by (simp add: B)
        have "bl_extract ab = Some (auth_state ACTIVE {})" by (simp add: ab_eq)
        moreover have "state_join sa sb (auth_state ACTIVE {})"
          unfolding sa_eq sb_eq using state_join_auth[of ACTIVE "{}" "{}"] by simp
        ultimately show ?thesis by blast
      qed
    qed
  next
    \<comment> \<open>extract under blinding\<close>
    fix a b sb
    assume Hab: "hash_blindable auth_hash a = hash_blindable auth_hash b"
       and BOab: "blinding_of_blindable auth_hash auth_bo a b"
       and eb: "bl_extract b = Some sb"
    show "\<exists>sa. bl_extract a = Some sa \<and> state_refines sa sb"
    proof (cases b)
      case (Unblinded q) note B = this
      show ?thesis
      proof (cases a)
        case (Unblinded p) note A = this
        have bo: "auth_bo p q" using BOab by (simp add: A B)
        have rfst: "fst p = fst q" and sub: "snd p \<subseteq> snd q"
          using bo by (simp_all add: auth_bo_def)
        have sr: "state_refines (auth_state (fst p) (snd p)) (auth_state (fst p) (snd q))"
          using sub by (rule state_refines_auth)
        have "bl_extract a = Some (auth_state (fst p) (snd p))" by (simp add: A)
        moreover have "state_refines (auth_state (fst p) (snd p)) sb"
          using sr rfst eb by (simp add: B)
        ultimately show ?thesis by blast
      next
        case (Blinded x) note A = this
        have sr: "state_refines (auth_state (fst q) {}) (auth_state (fst q) (snd q))"
          using empty_subsetI by (rule state_refines_auth)
        have "bl_extract a = Some (auth_state (fst q) {})"
          by (simp add: A auth_state_empty_eq[of ACTIVE "fst q"])
        moreover have "state_refines (auth_state (fst q) {}) sb"
          using sr eb by (simp add: B)
        ultimately show ?thesis by blast
      qed
    next
      case (Blinded y) note B = this
      \<comment> \<open>Only a blinded value can blind to a blinded value, and then they are equal.\<close>
      have "a = Blinded y" using BOab by (cases a) (simp_all add: B)
      then have "bl_extract a = Some (auth_state ACTIVE {})" by simp
      moreover have "sb = auth_state ACTIVE {}" using eb by (simp add: B)
      ultimately show ?thesis using state_refines_refl by auto
    qed
  next
    \<comment> \<open>extract preserves validity\<close>
    fix a s
    assume "bl_extract a = Some s"
    then show "valid_state s"
      by (cases a) (auto simp: auth_state_valid)
  qed
qed

text \<open>Non-degeneracy of the blindable instance: revealed two-chain views merge
  to their union, and a hash-only commitment merges back to the revealed view.\<close>

lemma oss_blindable_nontrivial:
  "merge_blindable auth_hash auth_merge (Unblinded (ACTIVE, {0})) (Unblinded (ACTIVE, {Suc 0}))
     = Some (Unblinded (ACTIVE, {0, Suc 0}))"
  "bl_extract (Unblinded (ACTIVE, {0, Suc 0})) = Some (auth_state ACTIVE {0, Suc 0})"
  "merge_blindable auth_hash auth_merge (Blinded (Content ACTIVE)) (Unblinded (ACTIVE, {0}))
     = Some (Unblinded (ACTIVE, {0}))"
  by (simp_all add: auth_merge_def auth_hash_def insert_commute)

text \<open>
  Regression witness exhibiting a non-vacuous instance for the sequence-level
  results above.  The generalised predicate @{const blinding_path} is satisfied by a genuinely
  increasing need-to-know sequence at this instance: a hash-only commitment, then a
  one-chain revealed view, then a two-chain revealed view, each blinding its
  successor.  The most-revealed endpoint extracts to a non-degenerate two-chain
  state.  This pins @{thm [source] authenticated_state.sequence_authenticity_preservation},
  @{thm [source] authenticated_state.blinding_path_hash_soundness} and
  @{thm [source] authenticated_state.sequence_inclusion_integrity} to a non-vacuous
  instance.
\<close>

lemma blinding_path_witness:
  "blinding_path (blinding_of_blindable auth_hash auth_bo)
     [Blinded (Content ACTIVE),
      Unblinded (ACTIVE, {0::nat}),
      Unblinded (ACTIVE, {0::nat, Suc 0})]"
  unfolding blinding_path_def
  by (auto simp: nth_Cons' auth_hash_def auth_bo_def)

lemma blinding_path_witness_endpoint:
  "bl_extract (Unblinded (ACTIVE, {0::nat, Suc 0})) = Some (auth_state ACTIVE {0, Suc 0})"
  "connected_chains (auth_state ACTIVE {0::nat, Suc 0}) (0::nat) = {0, Suc 0}"
  by (simp_all add: auth_state_connected)


section \<open>Instantiation on the top-level Canton transaction commitment\<close>

text \<open>
  Theory @{theory ADS_Functor.Canton_Transaction_Tree} formalises the production
  Canton transaction tree as an authenticated data structure, but over abstract
  content: @{typ view_data}, @{typ view_metadata}, @{typ common_metadata} and
  @{typ participant_metadata} are introduced by @{command typedecl} and carry no
  regulatory meaning, so a cross-domain state cannot be read out of @{typ transaction\<^sub>m}
  without an inadmissible axiom relating those opaque types to the regulatory model.
  We therefore model the same public structure with concrete content.  A Canton
  transaction is @{term Transaction\<^sub>m} applied to one top-level blindable position over
  a payload of metadata and a view list; we mirror exactly this
  one-constructor-over-a-blindable shape, taking the payload to be the cross-domain
  regulatory datum --- the consensus regulatory state (in the role of the common
  metadata) together with the set of chains whose views attest it (the per-participant
  view list, abstracted to its attesting-chain set).  Hash, blinding and merge are the
  ADS blindable-position operations on the payload: precisely the top-level
  authenticated operation Canton performs, since @{term Transaction\<^sub>m} wraps a single
  @{type blindable\<^sub>m}.  The Merkle interface and the three coherence obligations are
  transported from the blindable instance @{term oss_blindable} through the
  constructor bijection, so no new axiom and no residual proof obligation arise.  The
  one open item is model fidelity: whether this payload faithfully abstracts Canton's
  metadata-and-view-list datatype.  That is a sanity check of the model against the
  Canton specification, not a proof gap.
\<close>

datatype reg_transaction =
  RegTransaction (the_reg_tx: "(reg_state \<times> chain_id set, reg_state) blindable\<^sub>m")

definition rtx_hash :: "reg_transaction \<Rightarrow> reg_state blindable\<^sub>h" where
  "rtx_hash t = hash_blindable auth_hash (the_reg_tx t)"

definition rtx_bo :: "reg_transaction \<Rightarrow> reg_transaction \<Rightarrow> bool" where
  "rtx_bo s t = blinding_of_blindable auth_hash auth_bo (the_reg_tx s) (the_reg_tx t)"

definition rtx_merge :: "reg_transaction \<Rightarrow> reg_transaction \<Rightarrow> reg_transaction option" where
  "rtx_merge s t =
     map_option RegTransaction
       (merge_blindable auth_hash auth_merge (the_reg_tx s) (the_reg_tx t))"

definition rtx_extract :: "reg_transaction \<Rightarrow> global_state option" where
  "rtx_extract t = bl_extract (the_reg_tx t)"

text \<open>The single constructor is a bijection, so the Merkle interface of the payload
  blindable transports to the transaction wrapper.\<close>

lemma merkle_reg_transaction: "merkle_interface rtx_hash rtx_bo rtx_merge"
proof -
  have bind_simp: "rtx_merge a b \<bind> rtx_merge c
        = map_option RegTransaction
            (merge_blindable auth_hash auth_merge (the_reg_tx a) (the_reg_tx b)
               \<bind> merge_blindable auth_hash auth_merge (the_reg_tx c))" for a b c
    by (cases "merge_blindable auth_hash auth_merge (the_reg_tx a) (the_reg_tx b)")
       (simp_all add: rtx_merge_def)
  have mrh: "(rtx_hash a = rtx_hash b) = (\<exists>ab. rtx_merge a b = Some ab)" for a b
    by (cases "merge_blindable auth_hash auth_merge (the_reg_tx a) (the_reg_tx b)")
       (auto simp: rtx_hash_def rtx_merge_def oss_blindable.mk.merge_respects_hashes)
  have midem: "rtx_merge a a = Some a" for a
    by (simp add: rtx_merge_def oss_blindable.mk.idem)
  have mcomm: "rtx_merge a b = rtx_merge b a" for a b
    by (simp add: rtx_merge_def oss_blindable.mk.commute)
  have massoc: "rtx_merge a b \<bind> rtx_merge c = rtx_merge b c \<bind> rtx_merge a" for a b c
    using bind_simp[of a b c] bind_simp[of b c a]
          oss_blindable.mk.assoc[of "the_reg_tx a" "the_reg_tx b" "the_reg_tx c"] by simp
  have mbod: "rtx_bo a b = (rtx_merge a b = Some b)" for a b
    by (cases "merge_blindable auth_hash auth_merge (the_reg_tx a) (the_reg_tx b)")
       (auto simp: rtx_bo_def rtx_merge_def oss_blindable.mk.bo_def reg_transaction.expand)
  show ?thesis
    by (rule merkle_interface.intro[OF mrh midem mcomm massoc mbod])
qed

text \<open>Extraction reads the revealed cross-domain datum out of the transaction's
  top-level commitment; the three coherence obligations transport from the blindable
  instance @{term oss_blindable}.\<close>

interpretation canton_authenticated:
  authenticated_state rtx_hash rtx_bo rtx_merge rtx_extract
proof (rule authenticated_state.intro)
  show "merkle_interface rtx_hash rtx_bo rtx_merge" by (rule merkle_reg_transaction)
next
  show "authenticated_state_axioms rtx_hash rtx_bo rtx_merge rtx_extract"
  proof
    \<comment> \<open>extract respects merging, transported through the constructor\<close>
    fix a b ab sa sb
    assume H: "rtx_hash a = rtx_hash b" and M: "rtx_merge a b = Some ab"
       and ea: "rtx_extract a = Some sa" and eb: "rtx_extract b = Some sb"
    have h': "hash_blindable auth_hash (the_reg_tx a) = hash_blindable auth_hash (the_reg_tx b)"
      using H by (simp add: rtx_hash_def)
    have m': "merge_blindable auth_hash auth_merge (the_reg_tx a) (the_reg_tx b)
                = Some (the_reg_tx ab)"
      using M by (auto simp: rtx_merge_def split: option.splits)
    have ea': "bl_extract (the_reg_tx a) = Some sa" using ea by (simp add: rtx_extract_def)
    have eb': "bl_extract (the_reg_tx b) = Some sb" using eb by (simp add: rtx_extract_def)
    obtain sab where "bl_extract (the_reg_tx ab) = Some sab" "state_join sa sb sab"
      using oss_blindable.extract_respects_merging[OF h' m' ea' eb'] by blast
    then show "\<exists>sab. rtx_extract ab = Some sab \<and> state_join sa sb sab"
      by (auto simp: rtx_extract_def)
  next
    \<comment> \<open>extract under blinding, transported through the constructor\<close>
    fix a b sb
    assume H: "rtx_hash a = rtx_hash b" and BO: "rtx_bo a b"
       and eb: "rtx_extract b = Some sb"
    have h': "hash_blindable auth_hash (the_reg_tx a) = hash_blindable auth_hash (the_reg_tx b)"
      using H by (simp add: rtx_hash_def)
    have bo': "blinding_of_blindable auth_hash auth_bo (the_reg_tx a) (the_reg_tx b)"
      using BO by (simp add: rtx_bo_def)
    have eb': "bl_extract (the_reg_tx b) = Some sb" using eb by (simp add: rtx_extract_def)
    obtain sa where "bl_extract (the_reg_tx a) = Some sa" "state_refines sa sb"
      using oss_blindable.extract_under_blinding[OF h' bo' eb'] by blast
    then show "\<exists>sa. rtx_extract a = Some sa \<and> state_refines sa sb"
      by (auto simp: rtx_extract_def)
  next
    \<comment> \<open>extract preserves validity\<close>
    fix a s
    assume "rtx_extract a = Some s"
    then have "bl_extract (the_reg_tx a) = Some s" by (simp add: rtx_extract_def)
    then show "valid_state s" using oss_blindable.extract_preserves_validity by blast
  qed
qed

text \<open>Non-degeneracy: a revealed two-chain transaction joins with a hash-only
  commitment to the same chains, re-revealing the cross-domain view.\<close>

lemma canton_authenticated_nontrivial:
  "rtx_merge (RegTransaction (Unblinded (ACTIVE, {0})))
             (RegTransaction (Unblinded (ACTIVE, {Suc 0})))
     = Some (RegTransaction (Unblinded (ACTIVE, {0, Suc 0})))"
  "rtx_extract (RegTransaction (Unblinded (ACTIVE, {0, Suc 0})))
     = Some (auth_state ACTIVE {0, Suc 0})"
  "rtx_merge (RegTransaction (Blinded (Content ACTIVE)))
             (RegTransaction (Unblinded (ACTIVE, {0})))
     = Some (RegTransaction (Unblinded (ACTIVE, {0})))"
  by (simp_all add: rtx_merge_def rtx_extract_def auth_merge_def auth_hash_def insert_commute)


section \<open>Recursive instantiation on the Canton transaction tree\<close>

text \<open>
  The coarse instance @{term canton_authenticated} above models a Canton transaction
  as one top-level blindable over an abstract payload.  Here we keep the public
  \<^emph>\<open>recursive\<close> shape: a view is the rose tree @{type rose_tree\<^sub>m} of
  @{theory ADS_Functor.ADS_Construction} --- the very datatype the public Canton
  formalisation uses to build \<open>view\<^sub>m\<close> (\<open>view\<^sub>m \<cong> view_content rose_tree\<^sub>m\<close>, with
  \<open>merge_view = merge_tree \<dots>\<close>).  We instantiate that content-agnostic machine with
  concrete regulatory content: each node carries the \<^typ>\<open>chain_id\<close> it attests, and
  the children are its subviews.  No new datatype, no new Merkle proof: the interface
  is inherited from @{thm [source] merkle_tree}.
\<close>

type_synonym reg_view = "(chain_id, chain_id) rose_tree\<^sub>m"

abbreviation rv_hash :: "(reg_view, chain_id rose_tree\<^sub>h) hash" where
  "rv_hash \<equiv> hash_tree (hash_discrete :: chain_id \<Rightarrow> chain_id)"
abbreviation rv_bo :: "reg_view blinding_of" where
  "rv_bo \<equiv> blinding_of_tree hash_discrete (blinding_of_discrete :: chain_id blinding_of)"
abbreviation rv_merge :: "reg_view merge" where
  "rv_merge \<equiv> merge_tree hash_discrete (merge_discrete :: chain_id merge)"

lemma merkle_reg_view: "merkle_interface rv_hash rv_bo rv_merge"
  by (rule merkle_tree[OF merkle_discrete])

text \<open>Extraction collects the attested chains from every revealed node, recursing
  into subviews; a blinded node contributes nothing.  By the Merkle property a
  subview is reachable only through its (revealed) parent.  Lemma
  \<open>reg_chains_blinding\<close> below makes this monotone: blinding a node can only shrink
  the attested-chain set.\<close>

fun reg_chains :: "reg_view \<Rightarrow> chain_id set" where
  "reg_chains (Tree\<^sub>m (Unblinded (c, kids))) = insert c (\<Union>x\<in>set kids. reg_chains x)"
| "reg_chains (Tree\<^sub>m (Blinded _)) = {}"

subsection \<open>Extraction commutes with blinding and merge\<close>

text \<open>A pointwise containment along a list lifts to the union of the collected
  chains.\<close>

lemma UN_reg_chains_mono:
  assumes "list_all2 (\<lambda>x y. reg_chains x \<subseteq> reg_chains y) xs ys"
  shows "(\<Union>x\<in>set xs. reg_chains x) \<subseteq> (\<Union>y\<in>set ys. reg_chains y)"
  using assms by (induction xs ys rule: list_all2_induct) auto

text \<open>Positional characterisation of the ADS list merge (used for the children
  lists of a rose-tree node).  The length alignment is \emph{derived}, not assumed:
  the lemmas \<open>merge_list_NC\<close> / \<open>merge_list_CN\<close> below reject lists of different
  length, exactly because the list hash (@{term \<open>map\<close>}) commits to the length.\<close>

context begin
interpretation list_R1 .

lemma merge_list_Cons:
  "merge_list m (x # xs) (y # ys) =
     (case m x y of None \<Rightarrow> None | Some z \<Rightarrow> map_option ((#) z) (merge_list m xs ys))"
  by (simp add: merge_list_def merge_F_def merge_R1.simps
                list_to_list_R1.simps list_R1_to_list_simps merge_sum.simps merge_prod.simps
                merge_discrete_def option.map_comp o_def split: option.splits)

lemma merge_list_NN [simp]: "merge_list m [] [] = Some []"
  by (simp add: merge_list_def merge_F_def merge_R1.simps
                list_to_list_R1.simps list_R1_to_list_simps merge_sum.simps merge_discrete_def)

lemma merge_list_CN [simp]: "merge_list m (x # xs) [] = None"
  by (simp add: merge_list_def merge_F_def merge_R1.simps list_to_list_R1.simps merge_sum.simps)

lemma merge_list_NC [simp]: "merge_list m [] (y # ys) = None"
  by (simp add: merge_list_def merge_F_def merge_R1.simps list_to_list_R1.simps merge_sum.simps)

end

text \<open>The collected chains of a list-merge are the union of the contributors'
  chains, given that the elementwise merge has that property.\<close>

lemma reg_chains_merge_list:
  assumes "merge_list m k1 k2 = Some k"
    and "\<And>s t u. s \<in> set k1 \<Longrightarrow> m s t = Some u \<Longrightarrow> reg_chains u = reg_chains s \<union> reg_chains t"
  shows "(\<Union>s\<in>set k. reg_chains s) = (\<Union>s\<in>set k1. reg_chains s) \<union> (\<Union>t\<in>set k2. reg_chains t)"
  using assms
proof (induction k1 arbitrary: k2 k)
  case Nil
  then show ?case by (cases k2) auto
next
  case (Cons x xs)
  show ?case
  proof (cases k2)
    case Nil then show ?thesis using Cons.prems(1) by simp
  next
    case (Cons y ys)
    from Cons.prems(1) obtain z k' where z: "m x y = Some z"
      and k': "merge_list m xs ys = Some k'" and keq: "k = z # k'"
      by (auto simp: Cons merge_list_Cons split: option.splits)
    have hz: "reg_chains z = reg_chains x \<union> reg_chains y"
      using Cons.prems(2)[of x y z] z by simp
    have ih: "(\<Union>s\<in>set k'. reg_chains s) = (\<Union>s\<in>set xs. reg_chains s) \<union> (\<Union>t\<in>set ys. reg_chains t)"
      using k' by (intro Cons.IH) (use Cons.prems(2) in auto)
    show ?thesis using keq hz ih by (simp add: Cons) blast
  qed
qed

text \<open>Blinding shrinks the revealed chains, recursively through subviews: a
  blinded view's chains are contained in those of the view it blinds.\<close>

lemma reg_chains_blinding:
  "rv_bo a b \<Longrightarrow> reg_chains a \<subseteq> reg_chains b"
proof (induction a arbitrary: b rule: rose_tree\<^sub>m.induct)
  case (Tree\<^sub>m x b)
  obtain t2 where bt2: "b = Tree\<^sub>m t2" by (cases b)
  note rt = Tree\<^sub>m.prems[unfolded bt2 blinding_of_tree_simps]
  show ?case
  proof (cases x)
    case (Blinded h) then show ?thesis by simp
  next
    case (Unblinded p)
    obtain c kids1 where p: "p = (c, kids1)" by (cases p)
    from rt obtain kids2 where t2eq: "t2 = Unblinded (c, kids2)" and
      la: "list_all2 rv_bo kids1 kids2"
      by (auto simp: Unblinded p rel_prod_inject)
    have la2: "list_all2 (\<lambda>s t. reg_chains s \<subseteq> reg_chains t) kids1 kids2"
    proof (rule list_all2_all_nthI)
      show "length kids1 = length kids2" using la list_all2_lengthD by blast
      fix n assume n: "n < length kids1"
      have m1: "(c, kids1) \<in> set1_blindable\<^sub>m x" by (simp add: Unblinded p)
      have sm: "kids1 \<in> snds (c, kids1)" by (simp add: prod_set_simps)
      have memn: "kids1 ! n \<in> set kids1" using n by simp
      have rvn: "rv_bo (kids1 ! n) (kids2 ! n)" using la n list_all2_nthD by blast
      show "reg_chains (kids1 ! n) \<subseteq> reg_chains (kids2 ! n)"
        using Tree\<^sub>m.IH[OF m1 sm memn rvn] .
    qed
    from UN_reg_chains_mono[OF la2] show ?thesis
      by (auto simp: Unblinded p bt2 t2eq)
  qed
qed

text \<open>Merging re-reveals exactly the union of the two contributors' chains,
  recursively through subviews.\<close>

lemma reg_chains_merge:
  "rv_merge a b = Some ab \<Longrightarrow> reg_chains ab = reg_chains a \<union> reg_chains b"
proof (induction a arbitrary: b ab rule: rose_tree\<^sub>m.induct)
  case (Tree\<^sub>m x b ab)
  obtain y where bY: "b = Tree\<^sub>m y" by (cases b)
  obtain z where abz: "ab = Tree\<^sub>m z" by (cases ab)
  from Tree\<^sub>m.prems[unfolded bY abz merge_tree.simps]
  have mz: "merge_rt_F\<^sub>m hash_discrete merge_discrete (hash_tree hash_discrete) rv_merge x y = Some z"
    by (auto split: option.splits)
  note mb = mz[unfolded merge_rt_F\<^sub>m_def]
  show ?case
  proof (cases x)
    case (Blinded hx)
    from mb have "z = y \<or> (\<exists>q. y = Unblinded q \<and> z = Unblinded q)"
      by (cases y) (auto simp: Blinded split: if_splits)
    then show ?thesis using bY abz Blinded by auto
  next
    case (Unblinded px)
    obtain c1 k1 where px: "px = (c1, k1)" by (cases px)
    show ?thesis
    proof (cases y)
      case (Blinded hy)
      from mb have "z = Unblinded (c1, k1)"
        by (auto simp: Unblinded px Blinded split: if_splits)
      then show ?thesis using bY abz Unblinded px Blinded by simp
    next
      case (Unblinded py)
      obtain c2 k2 where py: "py = (c2, k2)" by (cases py)
      from mb obtain k where c12: "c1 = c2" and kk: "merge_list rv_merge k1 k2 = Some k"
        and zk: "z = Unblinded (c1, k)"
        by (auto simp: \<open>x = Unblinded px\<close> px Unblinded py merge_discrete_def
                 split: option.splits if_splits)
      have IHc: "\<And>s t u. s \<in> set k1 \<Longrightarrow> rv_merge s t = Some u
                   \<Longrightarrow> reg_chains u = reg_chains s \<union> reg_chains t"
      proof -
        fix s t u assume sset: "s \<in> set k1" and st: "rv_merge s t = Some u"
        have m1: "(c1, k1) \<in> set1_blindable\<^sub>m x" by (simp add: \<open>x = Unblinded px\<close> px)
        have sm: "k1 \<in> snds (c1, k1)" by (simp add: prod_set_simps)
        show "reg_chains u = reg_chains s \<union> reg_chains t"
          using Tree\<^sub>m.IH[OF m1 sm sset st] .
      qed
      have "(\<Union>s\<in>set k. reg_chains s) = (\<Union>s\<in>set k1. reg_chains s) \<union> (\<Union>t\<in>set k2. reg_chains t)"
        using reg_chains_merge_list[OF kk IHc] .
      then show ?thesis
        using bY abz zk c12 by (simp add: \<open>x = Unblinded px\<close> px Unblinded py)
    qed
  qed
qed

text \<open>
  Regression witnesses for the recursive structure.  First, deep-nested chains are
  not dropped: extraction genuinely recurses into subviews.  Second, list-merge
  length alignment is enforced (mismatched lengths are rejected), so it is derived
  from the hash rather than assumed.  Third, a blinded node contributes nothing.
  The single-consensus invariant (load-bearing, requiring the extraction map) is
  exhibited with the interpretation below.
\<close>

lemma reg_chains_deep_nesting:
  "reg_chains (Tree\<^sub>m (Unblinded (0::chain_id, [Tree\<^sub>m (Unblinded (Suc 0, []))]))) = {0, Suc 0}"
  by simp

lemma reg_chains_blinded_contributes_nothing:
  "reg_chains (Tree\<^sub>m (Blinded h)) = {}"
  by simp

lemma merge_list_length_aligned:
  "merge_list rv_merge [t] [] = None"
  "merge_list rv_merge [] [t] = None"
  by simp_all


subsection \<open>The recursive transaction-tree instance\<close>

text \<open>
  A Canton transaction wraps its consensus metadata and its view list in one
  top-level blindable (\<open>transaction\<^sub>m = Transaction\<^sub>m (blindable\<^sub>m \<dots>)\<close>).  We mirror
  that exactly: the carrier is a top-level blindable over a payload
  @{typ \<open>reg_state \<times> reg_view list\<close>} --- the consensus regulatory state together with
  the list of recursive view trees.  Hash, blinding and merge come from the public
  product/list/blindable building blocks, so the Merkle interface is inherited
  (lemma \<open>merkle_reg_tx\<close> below).

  \<^bold>\<open>Honesty (model-fidelity boundary, read carefully).\<close>  The recursive view structure
  is now \<^emph>\<open>faithful\<close>: subviews nest as in Canton, and subview-level blinding is alive
  (the witnesses below).  Two points remain modelling choices, \<^emph>\<open>not\<close> a 1:1 match with
  Canton's datatype.  First, leaf content is concrete \<^typ>\<open>chain_id\<close>/\<^typ>\<open>reg_state\<close>,
  whereas Canton's leaves are the opaque @{typ view_data}/@{typ view_metadata}: this
  is \<^emph>\<open>recursive-faithful, content-abstracted\<close>.  Second, the consensus \<^term>\<open>reg_state\<close>
  is modelled as a \<^emph>\<open>bare, non-independently-blindable\<close> field of the payload, while
  Canton's \<open>common_metadata\<^sub>m\<close> is itself an independently blindable position.  This is
  what structurally forces the single-consensus invariant (a view is reachable only
  by revealing the whole transaction, hence its consensus), which in turn gives
  validity with no assumption.  The price is a scope limit: the case ``a view is
  revealed while the consensus is blinded'' is \<^emph>\<open>out of this model's scope\<close>.  Lifting
  it would require an independently-blindable consensus and a fresh consistency
  argument; that is recorded as future work and as the residual fidelity check for
  the Canton authors, not closed here.
\<close>

type_synonym reg_transaction_tree =
  "(reg_state \<times> reg_view list, reg_state \<times> chain_id rose_tree\<^sub>h list) blindable\<^sub>m"

abbreviation rtt_chash :: "(reg_state \<times> reg_view list, reg_state \<times> chain_id rose_tree\<^sub>h list) hash"
  where "rtt_chash \<equiv> hash_prod hash_discrete (hash_list rv_hash)"
abbreviation rtt_cbo :: "(reg_state \<times> reg_view list) blinding_of"
  where "rtt_cbo \<equiv> blinding_of_prod blinding_of_discrete (blinding_of_list rv_bo)"
abbreviation rtt_cmerge :: "(reg_state \<times> reg_view list) merge"
  where "rtt_cmerge \<equiv> merge_prod merge_discrete (merge_list rv_merge)"
abbreviation rtt_hash :: "(reg_transaction_tree, (reg_state \<times> chain_id rose_tree\<^sub>h list) blindable\<^sub>h) hash"
  where "rtt_hash \<equiv> hash_blindable rtt_chash"
abbreviation rtt_bo :: "reg_transaction_tree blinding_of"
  where "rtt_bo \<equiv> blinding_of_blindable rtt_chash rtt_cbo"
abbreviation rtt_merge :: "reg_transaction_tree merge"
  where "rtt_merge \<equiv> merge_blindable rtt_chash rtt_cmerge"

lemma merkle_reg_tx_content: "merkle_interface rtt_chash rtt_cbo rtt_cmerge"
  by (rule merkle_product[OF merkle_discrete merkle_list[OF merkle_reg_view]])

lemma merkle_reg_tx: "merkle_interface rtt_hash rtt_bo rtt_merge"
  by (rule merkle_blindable[OF merkle_reg_tx_content])

text \<open>The two list-level corollaries of the recursive lemmas above, lifted over the
  view list of a transaction.\<close>

lemma reg_chains_views_blinding:
  assumes "list_all2 rv_bo va vb"
  shows "(\<Union>v\<in>set va. reg_chains v) \<subseteq> (\<Union>w\<in>set vb. reg_chains w)"
proof (rule UN_reg_chains_mono)
  show "list_all2 (\<lambda>x y. reg_chains x \<subseteq> reg_chains y) va vb"
    using assms by (auto elim!: list_all2_mono reg_chains_blinding)
qed

lemma reg_chains_views_merge:
  assumes "merge_list rv_merge va vb = Some v"
  shows "(\<Union>x\<in>set v. reg_chains x) = (\<Union>x\<in>set va. reg_chains x) \<union> (\<Union>y\<in>set vb. reg_chains y)"
proof (rule reg_chains_merge_list[OF assms])
  fix s t u assume "rv_merge s t = Some u"
  then show "reg_chains u = reg_chains s \<union> reg_chains t" by (rule reg_chains_merge)
qed

text \<open>Extraction: a revealed transaction yields the cross-domain state in which every
  attested chain (collected recursively from the revealed views) holds the asset in
  the consensus state; a fully blinded transaction yields the empty view.\<close>

fun rtt_extract :: "reg_transaction_tree \<Rightarrow> global_state option" where
  "rtt_extract (Unblinded (r, tvs)) = Some (auth_state r (\<Union>v\<in>set tvs. reg_chains v))"
| "rtt_extract (Blinded _) = Some (auth_state ACTIVE {})"

interpretation reg_tx_authenticated:
  authenticated_state rtt_hash rtt_bo rtt_merge rtt_extract
proof (rule authenticated_state.intro)
  show "merkle_interface rtt_hash rtt_bo rtt_merge" by (rule merkle_reg_tx)
next
  note mlist = merkle_list[OF merkle_reg_view]
  show "authenticated_state_axioms rtt_hash rtt_bo rtt_merge rtt_extract"
  proof
    \<comment> \<open>extract respects merging\<close>
    fix a b ab sa sb
    assume Hab: "rtt_hash a = rtt_hash b" and Mab: "rtt_merge a b = Some ab"
       and ea: "rtt_extract a = Some sa" and eb: "rtt_extract b = Some sb"
    show "\<exists>sab. rtt_extract ab = Some sab \<and> state_join sa sb sab"
    proof (cases a)
      case (Unblinded pa) note A = this
      obtain ra va where pa: "pa = (ra, va)" by (cases pa)
      show ?thesis
      proof (cases b)
        case (Unblinded pb) note B = this
        obtain rb vb where pb: "pb = (rb, vb)" by (cases pb)
        have hh: "ra = rb \<and> map rv_hash va = map rv_hash vb"
          using Hab by (simp add: A B pa pb)
        then have req: "ra = rb" and meq: "hash_list rv_hash va = hash_list rv_hash vb" by simp_all
        from meq obtain v where mlv: "merge_list rv_merge va vb = Some v"
          using merkle_interface.merge_respects_hashes[OF mlist] by blast
        have ab_eq: "ab = Unblinded (ra, v)"
          using Mab req mlv by (simp add: A B pa pb merge_discrete_def)
        have sa_eq: "sa = auth_state ra (\<Union>x\<in>set va. reg_chains x)" using ea by (simp add: A pa)
        have sb_eq: "sb = auth_state ra (\<Union>y\<in>set vb. reg_chains y)" using eb req by (simp add: B pb)
        have uv: "(\<Union>x\<in>set v. reg_chains x)
                  = (\<Union>x\<in>set va. reg_chains x) \<union> (\<Union>y\<in>set vb. reg_chains y)"
          using reg_chains_views_merge[OF mlv] .
        have "rtt_extract ab = Some (auth_state ra ((\<Union>x\<in>set va. reg_chains x)
                                                     \<union> (\<Union>y\<in>set vb. reg_chains y)))"
          by (simp add: ab_eq uv)
        moreover have "state_join sa sb (auth_state ra ((\<Union>x\<in>set va. reg_chains x)
                                                         \<union> (\<Union>y\<in>set vb. reg_chains y)))"
          unfolding sa_eq sb_eq by (rule state_join_auth)
        ultimately show ?thesis by blast
      next
        case (Blinded hb) note B = this
        have ab_eq: "ab = Unblinded (ra, va)" using Mab Hab by (simp add: A B pa)
        have sa_eq: "sa = auth_state ra (\<Union>x\<in>set va. reg_chains x)" using ea by (simp add: A pa)
        have sb_eq: "sb = auth_state ACTIVE {}" using eb by (simp add: B)
        have "rtt_extract ab = Some (auth_state ra (\<Union>x\<in>set va. reg_chains x))"
          by (simp add: ab_eq)
        moreover have "state_join sa sb (auth_state ra (\<Union>x\<in>set va. reg_chains x))"
          unfolding sa_eq sb_eq
          using state_join_auth[of ra "\<Union>x\<in>set va. reg_chains x" "{}"]
                auth_state_empty_eq[of ACTIVE ra] by simp
        ultimately show ?thesis by blast
      qed
    next
      case (Blinded ha) note A = this
      show ?thesis
      proof (cases b)
        case (Unblinded pb) note B = this
        obtain rb vb where pb: "pb = (rb, vb)" by (cases pb)
        have ab_eq: "ab = Unblinded (rb, vb)" using Mab Hab by (simp add: A B pb)
        have sa_eq: "sa = auth_state ACTIVE {}" using ea by (simp add: A)
        have sb_eq: "sb = auth_state rb (\<Union>y\<in>set vb. reg_chains y)" using eb by (simp add: B pb)
        have "rtt_extract ab = Some (auth_state rb (\<Union>y\<in>set vb. reg_chains y))"
          by (simp add: ab_eq)
        moreover have "state_join sa sb (auth_state rb (\<Union>y\<in>set vb. reg_chains y))"
          unfolding sa_eq sb_eq
          using state_join_auth[of rb "{}" "\<Union>y\<in>set vb. reg_chains y"]
                auth_state_empty_eq[of ACTIVE rb] by simp
        ultimately show ?thesis by blast
      next
        case (Blinded hb) note B = this
        have ab_eq: "ab = Blinded hb" using Mab Hab by (simp add: A B)
        have sa_eq: "sa = auth_state ACTIVE {}" using ea by (simp add: A)
        have sb_eq: "sb = auth_state ACTIVE {}" using eb by (simp add: B)
        have "rtt_extract ab = Some (auth_state ACTIVE {})" by (simp add: ab_eq)
        moreover have "state_join sa sb (auth_state ACTIVE {})"
          unfolding sa_eq sb_eq using state_join_auth[of ACTIVE "{}" "{}"] by simp
        ultimately show ?thesis by blast
      qed
    qed
  next
    \<comment> \<open>extract under blinding\<close>
    fix a b sb
    assume Hab: "rtt_hash a = rtt_hash b" and BOab: "rtt_bo a b"
       and eb: "rtt_extract b = Some sb"
    show "\<exists>sa. rtt_extract a = Some sa \<and> state_refines sa sb"
    proof (cases b)
      case (Unblinded pb) note B = this
      obtain rb vb where pb: "pb = (rb, vb)" by (cases pb)
      show ?thesis
      proof (cases a)
        case (Unblinded pa) note A = this
        obtain ra va where pa: "pa = (ra, va)" by (cases pa)
        have bo: "rtt_cbo (ra, va) (rb, vb)" using BOab by (simp add: A B pa pb)
        then have req: "ra = rb" and la: "list_all2 rv_bo va vb"
          by (simp_all add: rel_prod_inject)
        have sr: "(\<Union>x\<in>set va. reg_chains x) \<subseteq> (\<Union>y\<in>set vb. reg_chains y)"
          using reg_chains_views_blinding[OF la] .
        have srf: "state_refines (auth_state ra (\<Union>x\<in>set va. reg_chains x))
                                 (auth_state ra (\<Union>y\<in>set vb. reg_chains y))"
          using sr by (rule state_refines_auth)
        have "rtt_extract a = Some (auth_state ra (\<Union>x\<in>set va. reg_chains x))"
          by (simp add: A pa)
        moreover have "state_refines (auth_state ra (\<Union>x\<in>set va. reg_chains x)) sb"
          using srf req eb by (simp add: B pb)
        ultimately show ?thesis by blast
      next
        case (Blinded ha) note A = this
        have sr: "state_refines (auth_state rb {}) (auth_state rb (\<Union>y\<in>set vb. reg_chains y))"
          using empty_subsetI by (rule state_refines_auth)
        have "rtt_extract a = Some (auth_state rb {})"
          by (simp add: A auth_state_empty_eq[of ACTIVE rb])
        moreover have "state_refines (auth_state rb {}) sb"
          using sr eb by (simp add: B pb)
        ultimately show ?thesis by blast
      qed
    next
      case (Blinded hb) note B = this
      have "a = Blinded hb" using BOab by (cases a) (simp_all add: B)
      then have "rtt_extract a = Some (auth_state ACTIVE {})" by simp
      moreover have "sb = auth_state ACTIVE {}" using eb by (simp add: B)
      ultimately show ?thesis using state_refines_refl by auto
    qed
  next
    \<comment> \<open>extract preserves validity: single consensus per transaction, hence consistent\<close>
    fix a s
    assume "rtt_extract a = Some s"
    then show "valid_state s"
      by (cases a) (auto simp: auth_state_valid)
  qed
qed

text \<open>
  \<^bold>\<open>Multi-level (subview) non-degeneracy witness.\<close>  A transaction with one view that
  has two subviews (chains \<open>1\<close> and \<open>2\<close> nested under chain \<open>0\<close>).  Revealing everything
  attests all three chains; blinding \<^emph>\<open>only the chain-2 subview\<close> --- a subview-level,
  not top-level, blinding --- drops exactly chain \<open>2\<close>, leaving chains \<open>0\<close> and \<open>1\<close>
  attested.  Selective disclosure is alive below the root.
\<close>

definition demo_subview1 :: reg_view where
  "demo_subview1 = Tree\<^sub>m (Unblinded (Suc 0, []))"
definition demo_subview2 :: reg_view where
  "demo_subview2 = Tree\<^sub>m (Unblinded (Suc (Suc 0), []))"
definition demo_view :: reg_view where
  "demo_view = Tree\<^sub>m (Unblinded (0, [demo_subview1, demo_subview2]))"
definition demo_view_sv2blinded :: reg_view where
  "demo_view_sv2blinded = Tree\<^sub>m (Unblinded (0, [demo_subview1, Tree\<^sub>m (Blinded (Garbage 0))]))"

lemma demo_subview_disclosure:
  "reg_chains demo_view = {0, Suc 0, Suc (Suc 0)}"
  "reg_chains demo_view_sv2blinded = {0, Suc 0}"
  by (auto simp: demo_view_def demo_view_sv2blinded_def demo_subview1_def demo_subview2_def)

lemma demo_multilevel_extract:
  "rtt_extract (Unblinded (ACTIVE, [demo_view]))
     = Some (auth_state ACTIVE {0, Suc 0, Suc (Suc 0)})"
  "rtt_extract (Unblinded (ACTIVE, [demo_view_sv2blinded]))
     = Some (auth_state ACTIVE {0, Suc 0})"
  by (simp_all add: demo_subview_disclosure)

text \<open>
  \<^bold>\<open>The single-consensus invariant is load-bearing.\<close>  If a model allowed
  a chain to be attested in a regulatory state different from another chain's (which
  a per-node \<^term>\<open>reg_state\<close> would permit), validity would collapse: the state below
  pins chain \<open>0\<close> to \<^const>\<open>ACTIVE\<close> and chain \<^term>\<open>Suc 0\<close> to \<^const>\<open>FROZEN\<close> on the same
  asset, and is \<^emph>\<open>not\<close> valid.  The recursive extraction @{const rtt_extract} never
  produces such a state, because every attested chain shares the \<^emph>\<open>one\<close> consensus
  \<^term>\<open>reg_state\<close> of its transaction --- exactly the structural reason validity holds
  with no assumption.\<close>

definition rogue_inconsistent_state :: global_state where
  "rogue_inconsistent_state =
     \<lparr> gs_chains = (\<lambda>c a.
          if a = 0 \<and> c = 0
            then Some \<lparr> as_reg_state = ACTIVE \<rparr>
          else if a = 0 \<and> c = Suc 0
            then Some \<lparr> as_reg_state = FROZEN \<rparr>
          else None),
       gs_locks = (\<lambda>_. False) \<rparr>"

lemma single_consensus_load_bearing:
  "\<not> valid_state rogue_inconsistent_state"
  by (auto simp: rogue_inconsistent_state_def valid_state_def consistent_state_def
                 get_reg_state_def get_asset_state_def)

text \<open>Non-degeneracy of the recursive transaction instance: a single-chain
  transaction extracts to a genuine one-chain cross-domain state, and a transaction
  with a non-empty view list genuinely merges at the transaction-tree level (the
  \<open>extract_respects_merging\<close> path is exercised directly, not only through
  @{thm [source] reg_chains_merge}).\<close>

lemma reg_tx_authenticated_nontrivial:
  "rtt_extract (Unblinded (ACTIVE, [Tree\<^sub>m (Unblinded (0, []))]))
     = Some (auth_state ACTIVE {0})"
  "rtt_merge (Unblinded (ACTIVE, [Tree\<^sub>m (Unblinded (0, []))]))
             (Unblinded (ACTIVE, [Tree\<^sub>m (Unblinded (0, []))]))
     = Some (Unblinded (ACTIVE, [Tree\<^sub>m (Unblinded (0, []))]))"
  by (simp_all add: merge_discrete_def merge_list_Cons merge_tree.simps merge_rt_F\<^sub>m_def)


section \<open>Path-level Merkle inclusion for the recursive view tree\<close>

text \<open>
  The sequence-level result @{thm [source] authenticated_state.sequence_inclusion_integrity}
  is stated at the level of revealed holdings.  Here we sharpen it to the concrete Merkle
  \<^emph>\<open>inclusion path\<close>.  The recursive view @{typ reg_view} is exactly an instance of the
  generic rose-tree inclusion-proof machinery of
  @{theory ADS_Functor.Inclusion_Proof_Construction}: we take the source-content embedding
  to be the identity on @{typ chain_id} (\<open>rv_embed\<close>) and the content hash to be
  @{term hash_discrete}.  An inclusion proof is a zipper in which the target subview is
  revealed while every node on the path to the root and all off-path siblings are blinded
  (\<open>blind_path\<close>).  Because the discrete content already satisfies the blinding-order locale
  (@{thm [source] blinding_of_on_discrete}), the two soundness results transfer with no new
  assumption.  This is the same construction the public Canton formalisation applies to its
  own view tree; it operates on the view rose tree, so the consensus scope limit of the
  preceding section is untouched.
\<close>

abbreviation rv_embed :: "chain_id \<Rightarrow> chain_id" where
  "rv_embed \<equiv> id"

abbreviation zippers_reg_view :: "chain_id zipper \<Rightarrow> (chain_id, chain_id) zipper\<^sub>m list" where
  "zippers_reg_view \<equiv> zippers_rose_tree rv_embed hash_discrete"

abbreviation blind_reg_path :: "chain_id path \<Rightarrow> (chain_id, chain_id) path\<^sub>m" where
  "blind_reg_path \<equiv> blind_path rv_embed hash_discrete"

abbreviation embed_reg_path :: "chain_id path \<Rightarrow> (chain_id, chain_id) path\<^sub>m" where
  "embed_reg_path \<equiv> embed_path rv_embed"

text \<open>Inclusion soundness: every enumerated inclusion proof commits to the same
  authenticating root hash as the fully revealed view tree, so no inclusion proof can
  fabricate a tree the root does not authenticate.\<close>

theorem reg_view_inclusion_same_hash:
  assumes "z \<in> set (zippers_reg_view (p, t))"
  shows "rv_hash (tree_of_zipper\<^sub>m z)
       = rv_hash (tree_of_zipper\<^sub>m (embed_reg_path p, embed_source_tree rv_embed t))"
  using assms by (rule zippers_rose_tree_same_hash')

text \<open>Each inclusion proof is a blinding of the canonical inclusion-path tree, which
  carries the same root hash as the fully revealed tree: a partial, need-to-know view that
  refines the whole.  The single content premise is discharged from the discrete building
  block, so no assumption is added.\<close>

theorem reg_view_inclusion_blinding_of:
  assumes "z \<in> set (zippers_reg_view (p, t))"
  shows "rv_bo (tree_of_zipper\<^sub>m z)
              (tree_of_zipper\<^sub>m (blind_reg_path p, embed_source_tree rv_embed t))"
  by (rule zippers_rose_tree_blinding_of[OF blinding_of_on_discrete assms])

text \<open>The attested chains carried by an inclusion proof are contained in those of the
  fully revealed tree: a path-level reading of need-to-know, from
  @{thm [source] reg_chains_blinding}.\<close>

corollary reg_view_inclusion_chains_sound:
  assumes "z \<in> set (zippers_reg_view (p, t))"
  shows "reg_chains (tree_of_zipper\<^sub>m z)
       \<subseteq> reg_chains (tree_of_zipper\<^sub>m (blind_reg_path p, embed_source_tree rv_embed t))"
  using reg_chains_blinding[OF reg_view_inclusion_blinding_of[OF assms]] .

text \<open>Non-degeneracy.  Over a genuine two-level view tree the canonical inclusion endpoint
  reveals all three attested chains, and a selective inclusion proof in the enumeration
  exposes its target subview (chains \<^term>\<open>0::chain_id\<close> and \<^term>\<open>Suc 0\<close>) while the unrelated
  sibling (chain \<^term>\<open>Suc (Suc 0)\<close>) stays blinded.  Selective disclosure is alive at the
  path level.\<close>

definition demo_src :: "chain_id rose_tree" where
  "demo_src = Tree (0, [Tree (Suc 0, []), Tree (Suc (Suc 0), [])])"

lemma reg_view_inclusion_nonvacuous_endpoint:
  "reg_chains (tree_of_zipper\<^sub>m (embed_reg_path [], embed_source_tree rv_embed demo_src))
     = {0, Suc 0, Suc (Suc 0)}"
  by (auto simp: demo_src_def embed_path_def)

lemma reg_view_inclusion_nonvacuous_selective:
  "\<exists>z \<in> set (zippers_reg_view ([], demo_src)). reg_chains (tree_of_zipper\<^sub>m z) = {0, Suc 0}"
  by (force simp: demo_src_def zippers_rose_tree.simps zipper_children.simps
                  blind_path_def embed_path_def)

text \<open>Load-bearing regression witness.  A forged zipper that fabricates a different chain
  is neither in the legitimate enumeration nor matched by the same-hash guarantee, so the
  membership premise of @{thm [source] reg_view_inclusion_same_hash} is load-bearing:
  dropping it makes the theorem false.\<close>

lemma reg_view_inclusion_forgery_excluded:
  "([], embed_source_tree rv_embed (Tree (Suc 0, [])))
       \<notin> set (zippers_reg_view ([], Tree (0::chain_id, [])))
   \<and> rv_hash (tree_of_zipper\<^sub>m ([], embed_source_tree rv_embed (Tree (Suc 0, []))))
      \<noteq> rv_hash (tree_of_zipper\<^sub>m (embed_reg_path [], embed_source_tree rv_embed (Tree (0::chain_id, []))))"
  by (simp add: zippers_rose_tree.simps zipper_children.simps embed_path_def hash_rt_F\<^sub>m_alt_def)

end
