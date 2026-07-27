import FormalConjecturesUtil
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

/-!
# Written on the Wall II — Graph Conjecture 2

Local project version.  It uses the minimal `FormalConjecturesUtil`
compatibility module and is independent of the Lean4Web source file.
-/

namespace WrittenOnTheWallII.GraphConjecture2

open Classical SimpleGraph
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

def edgeDegreeSum (d : α → ℝ) : Sym2 α → ℝ :=
  Sym2.lift ⟨fun u v => d u + d v, fun _ _ => add_comm _ _⟩

omit [Fintype α] [DecidableEq α] in
@[simp]
lemma edgeDegreeSum_mk (d : α → ℝ) (u v : α) :
    edgeDegreeSum d s(u, v) = d u + d v :=
  rfl

lemma sum_edgeDegreeSum (G : SimpleGraph α) [DecidableRel G.Adj] :
    ∑ e ∈ G.edgeFinset, edgeDegreeSum (fun x => (G.degree x : ℝ)) e =
      ∑ v, (G.degree v : ℝ) ^ 2 := by
  classical
  calc
    _ = ∑ e ∈ G.edgeFinset, ∑ v ∈ Finset.univ with v ∈ e, (G.degree v : ℝ) := by
      apply Finset.sum_congr rfl
      intro e he
      induction e using Sym2.inductionOn with
      | _ u v =>
          rw [SimpleGraph.mem_edgeFinset] at he
          rw [SimpleGraph.mem_edgeSet] at he
          have hs : {x ∈ (Finset.univ : Finset α) | x = u ∨ x = v} = {u, v} := by
            ext x
            simp [eq_comm]
          simp only [edgeDegreeSum_mk, Sym2.mem_iff]
          rw [hs]
          simp [he.ne]
    _ = ∑ v ∈ Finset.univ, ∑ e ∈ G.edgeFinset with v ∈ e, (G.degree v : ℝ) := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = ∑ v, (G.degree v : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [← G.incidenceFinset_eq_filter]
      simp [pow_two]

lemma exists_edge_degreeSum_ge_twice_average
    [Nonempty α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hE : G.edgeFinset.Nonempty) :
    ∃ u v, G.Adj u v ∧
      2 * ((∑ x, (G.degree x : ℝ)) / (Fintype.card α : ℝ))
        ≤ (G.degree u : ℝ) + G.degree v := by
  classical
  let b : ℝ := 2 * ((∑ x, (G.degree x : ℝ)) / (Fintype.card α : ℝ))
  have hn : 0 < (Fintype.card α : ℝ) := by positivity
  have hhand :
      (∑ x, (G.degree x : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hc :
      (∑ x, (G.degree x : ℝ)) ^ 2 ≤
        (Fintype.card α : ℝ) * ∑ x, (G.degree x : ℝ) ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset α)) (f := fun x => (G.degree x : ℝ)))
  have havg :
      (G.edgeFinset.card : ℝ) * b ≤
        ∑ e ∈ G.edgeFinset, edgeDegreeSum (fun x => (G.degree x : ℝ)) e := by
    rw [sum_edgeDegreeSum]
    calc
      (G.edgeFinset.card : ℝ) * b =
          (4 * (G.edgeFinset.card : ℝ) ^ 2) / (Fintype.card α : ℝ) := by
            dsimp [b]
            rw [hhand]
            ring
      _ ≤ ∑ x, (G.degree x : ℝ) ^ 2 := by
        rw [div_le_iff₀ hn]
        rw [hhand] at hc
        nlinarith
  have hedge :
      ∃ e ∈ G.edgeFinset, b ≤ edgeDegreeSum (fun x => (G.degree x : ℝ)) e := by
    by_contra hex
    push Not at hex
    have hlt :
        (∑ e ∈ G.edgeFinset, edgeDegreeSum (fun x => (G.degree x : ℝ)) e) <
          ∑ _e ∈ G.edgeFinset, b :=
      Finset.sum_lt_sum_of_nonempty hE fun e he => hex e he
    have hconst :
        (∑ _e ∈ G.edgeFinset, b) = (G.edgeFinset.card : ℝ) * b := by
      simp
    rw [hconst] at hlt
    exact (not_lt_of_ge havg) hlt
  obtain ⟨e, he, hbe⟩ := hedge
  induction e using Sym2.inductionOn with
  | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      exact ⟨u, v, he, by simpa [b] using hbe⟩

def starAt (v : α) (I : Finset α) : SimpleGraph α :=
  SimpleGraph.fromRel (fun a b => a = v ∧ b ∈ I)

omit [Fintype α] [DecidableEq α] in
@[simp]
lemma starAt_adj (v : α) (I : Finset α) (a b : α) :
    (starAt v I).Adj a b ↔
      a ≠ b ∧ ((a = v ∧ b ∈ I) ∨ (b = v ∧ a ∈ I)) := by
  simp [starAt, SimpleGraph.fromRel_adj]

omit [DecidableEq α] in
lemma starAt_edge_contains_center {v : α} {I : Finset α} {e : Sym2 α}
    (he : e ∈ (starAt v I).edgeFinset) : v ∈ e := by
  induction e using Sym2.inductionOn with
  | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      rw [Sym2.mem_iff]
      rw [starAt_adj] at he
      rcases he.2 with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl h.symm
      · exact Or.inr h.symm

lemma starAt_neighborFinset_center {v : α} {I : Finset α} (hv : v ∉ I) :
    (starAt v I).neighborFinset v = I := by
  ext x
  rw [SimpleGraph.mem_neighborFinset]
  by_cases hx : x ∈ I
  · have hne : v ≠ x := by
      intro h
      subst x
      exact hv hx
    exact ⟨fun _ => hx, fun _ => starAt_adj v I v x |>.2 ⟨hne, Or.inl ⟨rfl, hx⟩⟩⟩
  · constructor
    · intro hadj
      rw [starAt_adj] at hadj
      rcases hadj.2 with ⟨_, hxI⟩ | ⟨_, hvI⟩
      · exact (hx hxI).elim
      · exact (hv hvI).elim
    · exact fun h => (hx h).elim

lemma starAt_degree_center {v : α} {I : Finset α} (hv : v ∉ I) :
    (starAt v I).degree v = I.card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, starAt_neighborFinset_center hv]

lemma starAt_card_edgeFinset {v : α} {I : Finset α} (hv : v ∉ I) :
    (starAt v I).edgeFinset.card = I.card := by
  have hi :
      (starAt v I).incidenceFinset v = (starAt v I).edgeFinset := by
    rw [SimpleGraph.incidenceFinset_eq_filter]
    exact Finset.filter_eq_self.2 fun e he => starAt_edge_contains_center he
  rw [← starAt_degree_center hv, ← SimpleGraph.card_incidenceFinset_eq_degree, hi]

def replaceAt (H : SimpleGraph α) (v : α) (I : Finset α) : SimpleGraph α :=
  H.deleteIncidenceSet v ⊔ starAt v I

omit [Fintype α] [DecidableEq α] in
@[simp]
lemma replaceAt_adj (H : SimpleGraph α) [DecidableRel H.Adj]
    (v : α) (I : Finset α) (a b : α) :
    (replaceAt H v I).Adj a b ↔
      (H.Adj a b ∧ a ≠ v ∧ b ≠ v) ∨
        (a ≠ b ∧ ((a = v ∧ b ∈ I) ∨ (b = v ∧ a ∈ I))) := by
  rw [replaceAt, SimpleGraph.sup_adj, SimpleGraph.deleteIncidenceSet_adj, starAt_adj]

omit [Fintype α] [DecidableEq α] in
lemma replaceAt_center_adj_iff (H : SimpleGraph α) [DecidableRel H.Adj]
    (v : α) (I : Finset α) (x : α) :
    (replaceAt H v I).Adj v x ↔ v ≠ x ∧ x ∈ I := by
  rw [replaceAt_adj]
  constructor
  · rintro (h | h)
    · exact (h.2.1 rfl).elim
    · rcases h.2 with ⟨_, hx⟩ | ⟨hxv, _⟩
      · exact ⟨h.1, hx⟩
      · exact (h.1 hxv.symm).elim
  · rintro ⟨hvx, hx⟩
    exact Or.inr ⟨hvx, Or.inl ⟨rfl, hx⟩⟩

omit [Fintype α] [DecidableEq α] in
lemma replaceAt_adj_center_iff (H : SimpleGraph α) [DecidableRel H.Adj]
    (v : α) (I : Finset α) (x : α) :
    (replaceAt H v I).Adj x v ↔ x ≠ v ∧ x ∈ I := by
  rw [SimpleGraph.adj_comm, replaceAt_center_adj_iff]
  exact and_congr ne_comm Iff.rfl

omit [Fintype α] [DecidableEq α] in
lemma replaceAt_le {G H : SimpleGraph α} [DecidableRel H.Adj]
    {v : α} {I : Finset α} (hHG : H ≤ G)
    (hIG : ∀ x ∈ I, G.Adj v x) : replaceAt H v I ≤ G := by
  intro a b hab
  rw [replaceAt_adj] at hab
  rcases hab with hdel | hstar
  · exact hHG hdel.1
  ·
    rcases hstar.2 with ⟨rfl, hb⟩ | ⟨rfl, ha⟩
    · exact hIG b hb
    · exact (hIG a ha).symm

lemma replaceAt_card_edgeFinset (H : SimpleGraph α) [DecidableRel H.Adj]
    {v : α} {I : Finset α} (hv : v ∉ I) :
    (replaceAt H v I).edgeFinset.card =
      H.edgeFinset.card - H.degree v + I.card := by
  have hd :
      Disjoint (H.deleteIncidenceSet v).edgeFinset (starAt v I).edgeFinset := by
    rw [Finset.disjoint_left]
    intro e hedel hestar
    rw [SimpleGraph.edgeFinset_deleteIncidenceSet_eq_filter] at hedel
    exact (Finset.mem_filter.mp hedel).2 (starAt_edge_contains_center hestar)
  have hs :
      (replaceAt H v I).edgeFinset =
        (H.deleteIncidenceSet v).edgeFinset ∪ (starAt v I).edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | _ a b =>
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          Finset.mem_union]
        change (H.deleteIncidenceSet v ⊔ starAt v I).Adj a b ↔
          (H.deleteIncidenceSet v).Adj a b ∨ (starAt v I).Adj a b
        exact SimpleGraph.sup_adj (H.deleteIncidenceSet v) (starAt v I) a b
  rw [hs, Finset.card_union_of_disjoint hd,
    H.card_edgeFinset_deleteIncidenceSet, starAt_card_edgeFinset hv]

omit [Fintype α] in
lemma replaceAt_cliqueFree_three {G H : SimpleGraph α} [DecidableRel H.Adj]
    {v : α} {I : Finset α} (hHG : H ≤ G) (hH : H.CliqueFree 3)
    (hI : G.IsIndepSet (I : Set α)) :
    (replaceAt H v I).CliqueFree 3 := by
  intro t ht
  rw [SimpleGraph.is3Clique_iff] at ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht
  by_cases ha : a = v
  · subst a
    have hbv : b ≠ v := hab.ne.symm
    have hcv : c ≠ v := hac.ne.symm
    have hbI : b ∈ I := (replaceAt_center_adj_iff H v I b).mp hab |>.2
    have hcI : c ∈ I := (replaceAt_center_adj_iff H v I c).mp hac |>.2
    have hHbc : H.Adj b c := by
      simpa [replaceAt_adj, hbv, hcv] using hbc
    exact (hI hbI hcI hHbc.ne) (hHG hHbc)
  · by_cases hb : b = v
    · subst b
      have hav : a ≠ v := ha
      have hcv : c ≠ v := hbc.ne.symm
      have haI : a ∈ I := (replaceAt_adj_center_iff H v I a).mp hab |>.2
      have hcI : c ∈ I := (replaceAt_center_adj_iff H v I c).mp hbc |>.2
      have hHac : H.Adj a c := by
        simpa [replaceAt_adj, hav, hcv] using hac
      exact (hI haI hcI hHac.ne) (hHG hHac)
    · by_cases hc : c = v
      · subst c
        have hav : a ≠ v := ha
        have hbv : b ≠ v := hb
        have haI : a ∈ I := (replaceAt_adj_center_iff H v I a).mp hac |>.2
        have hbI : b ∈ I := (replaceAt_adj_center_iff H v I b).mp hbc |>.2
        have hHab : H.Adj a b := by
          simpa [replaceAt_adj, hav, hbv] using hab
        exact (hI haI hbI hHab.ne) (hHG hHab)
      · have hHab : H.Adj a b := by
          simpa [replaceAt_adj, ha, hb] using hab
        have hHac : H.Adj a c := by
          simpa [replaceAt_adj, ha, hc] using hac
        have hHbc : H.Adj b c := by
          simpa [replaceAt_adj, hb, hc] using hbc
        exact hH {a, b, c} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hHab, hHac, hHbc⟩)

lemma exists_triangleFree_subgraph_degree_ge_indepNeighbors (G : SimpleGraph α) :
    ∃ H : SimpleGraph α, ∃ _inst : DecidableRel H.Adj,
      H ≤ G ∧ H.CliqueFree 3 ∧ ∀ v, G.indepNeighborsCard v ≤ H.degree v := by
  classical
  let p : SimpleGraph α → Prop := fun H => H ≤ G ∧ H.CliqueFree 3
  have hp : ∃ H : SimpleGraph α, p H := by
    refine ⟨⊥, bot_le, ?_⟩
    exact SimpleGraph.cliqueFree_bot (by omega)
  obtain ⟨H, instH, hExt⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists p).mpr hp
  refine ⟨H, instH, hExt.1.1, hExt.1.2, ?_⟩
  intro v
  obtain ⟨J, hJ⟩ :=
    SimpleGraph.exists_isNIndepSet_indepNum
      (G := G.induce (G.neighborSet v))
  let I : Finset α := J.map ⟨Subtype.val, Subtype.val_injective⟩
  have hIcard : I.card = G.indepNeighborsCard v := by
    simp [I, SimpleGraph.indepNeighborsCard, hJ.card_eq]
  have hIG : ∀ x ∈ I, G.Adj v x := by
    intro x hx
    simp only [I, Finset.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact y.property
  have hvI : v ∉ I := fun hv => G.loopless v (hIG v hv)
  have hIind : G.IsIndepSet (I : Set α) := by
    have hcoe :
        (I : Set α) = Subtype.val '' (J : Set (G.neighborSet v)) := by
      ext x
      simp [I]
    rw [hcoe]
    rw [← G.isIndepSet_induce]
    rw [← SimpleGraph.induce_eq_coe_induce_top]
    exact hJ.isIndepSet
  by_contra hdeg
  have hlt : H.degree v < G.indepNeighborsCard v := Nat.lt_of_not_ge hdeg
  let H' := replaceAt H v I
  have hH'le : H' ≤ G := replaceAt_le hExt.1.1 hIG
  have hH'free : H'.CliqueFree 3 :=
    replaceAt_cliqueFree_three hExt.1.1 hExt.1.2 hIind
  have hmax : H'.edgeFinset.card ≤ H.edgeFinset.card :=
    hExt.2 ⟨hH'le, hH'free⟩
  have hcard :
      H'.edgeFinset.card = H.edgeFinset.card - H.degree v + I.card :=
    replaceAt_card_edgeFinset H hvI
  omega

def leafCount (T : SimpleGraph α) [DecidableRel T.Adj] : ℕ :=
  (Finset.univ.filter fun v => T.degree v = 1).card

omit [DecidableEq α] in
lemma leafCount_eq_two_add_sum_degree_sub_two
    [Nontrivial α] (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) :
    leafCount T = 2 + ∑ v, (T.degree v - 2) := by
  have hpos : ∀ v, 0 < T.degree v := by
    intro v
    rw [T.degree_pos_iff_exists_adj]
    exact hT.isConnected.preconnected.exists_adj_of_nontrivial v
  have hpoint : ∀ v,
      (T.degree v : ℤ) =
        2 + ((T.degree v - 2 : ℕ) : ℤ) -
          if T.degree v = 1 then 1 else 0 := by
    intro v
    split_ifs with hv
    · omega
    · have hp := hpos v
      have htwo : 2 ≤ T.degree v := by omega
      rw [Nat.cast_sub htwo]
      norm_num
  have hsum :
      (∑ v, (T.degree v : ℤ)) =
        2 * (Fintype.card α : ℤ) +
          (∑ v, ((T.degree v - 2 : ℕ) : ℤ)) - (leafCount T : ℤ) := by
    calc
      _ = ∑ v, (2 + ((T.degree v - 2 : ℕ) : ℤ) -
          if T.degree v = 1 then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro v _
            exact hpoint v
      _ = _ := by
        simp [leafCount, Finset.sum_sub_distrib, Finset.sum_add_distrib]
        ring
  have hhand :
      (∑ v, (T.degree v : ℤ)) = 2 * (T.edgeFinset.card : ℤ) := by
    exact_mod_cast T.sum_degrees_eq_twice_card_edges
  have hedge :
      (T.edgeFinset.card : ℤ) + 1 = (Fintype.card α : ℤ) := by
    exact_mod_cast hT.card_edgeFinset
  have hcast :
      ((∑ v, (T.degree v - 2) : ℕ) : ℤ) =
        ∑ v, ((T.degree v - 2 : ℕ) : ℤ) := by
    simp
  exact_mod_cast (show (leafCount T : ℤ) =
      2 + ((∑ v, (T.degree v - 2) : ℕ) : ℤ) by
        rw [hcast]
        nlinarith [hsum, hhand, hedge])

lemma leafCount_ge_degree_add_degree_sub_two
    [Nontrivial α] (T : SimpleGraph α) [DecidableRel T.Adj]
    (hT : T.IsTree) {u v : α} (huv : T.Adj u v) :
    T.degree u + T.degree v - 2 ≤ leafCount T := by
  have hpair :
      (T.degree u - 2) + (T.degree v - 2) ≤ ∑ x, (T.degree x - 2) := by
    calc
      _ = ∑ x ∈ ({u, v} : Finset α), (T.degree x - 2) := by
        rw [Finset.sum_pair huv.ne]
      _ ≤ ∑ x ∈ (Finset.univ : Finset α), (T.degree x - 2) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (by simp) (by simp)
      _ = _ := by simp
  rw [leafCount_eq_two_add_sum_degree_sub_two T hT]
  omega

omit [Fintype α] [DecidableEq α] in
lemma not_mem_support_starAt {v x : α} {I : Finset α}
    (hxv : x ≠ v) (hxI : x ∉ I) : x ∉ (starAt v I).support := by
  rw [SimpleGraph.mem_support]
  push Not
  intro y
  rw [starAt_adj]
  aesop

omit [Fintype α] in
lemma isAcyclic_sup_starAt (F : SimpleGraph α) [DecidableRel F.Adj]
    {v : α} {I : Finset α} (hF : F.IsAcyclic) (hvI : v ∉ I)
    (hdis : ∀ x ∈ I, x ∉ F.support) :
    (F ⊔ starAt v I).IsAcyclic := by
  induction I using Finset.induction_on with
  | empty =>
      have hz : starAt v ∅ = (⊥ : SimpleGraph α) := by
        ext a b
        simp [starAt_adj]
      simpa [hz] using hF
  | @insert x I hx ih =>
      have hvx : v ≠ x := by
        intro h
        subst x
        exact hvI (by simp)
      have hvI' : v ∉ I := fun h => hvI (Finset.mem_insert_of_mem h)
      have hdis' : ∀ y ∈ I, y ∉ F.support :=
        fun y hy => hdis y (Finset.mem_insert_of_mem hy)
      have hprev : (F ⊔ starAt v I).IsAcyclic := ih hvI' hdis'
      have hxF : x ∉ F.support := hdis x (by simp)
      have hxStar : x ∉ (starAt v I).support :=
        not_mem_support_starAt hvx.symm hx
      have hxPrev : x ∉ (F ⊔ starAt v I).support := by
        rw [SimpleGraph.mem_support]
        push Not
        intro y
        rw [SimpleGraph.sup_adj]
        exact fun h => h.elim
          (fun hxy => hxF ((SimpleGraph.mem_support _).mpr ⟨y, hxy⟩))
          (fun hxy => hxStar ((SimpleGraph.mem_support _).mpr ⟨y, hxy⟩))
      have hreach : ¬(F ⊔ starAt v I).Reachable v x := by
        intro h
        exact hxPrev (SimpleGraph.mem_support_of_reachable hvx.symm h.symm)
      have hadd :
          ((F ⊔ starAt v I) ⊔ SimpleGraph.fromEdgeSet {s(v, x)}).IsAcyclic :=
        ((F ⊔ starAt v I).isAcyclic_add_edge_iff_of_not_reachable v x hreach).2 hprev
      have heq :
          F ⊔ starAt v (insert x I) =
            (F ⊔ starAt v I) ⊔ SimpleGraph.fromEdgeSet {s(v, x)} := by
        ext a b
        simp only [SimpleGraph.sup_adj, starAt_adj, SimpleGraph.fromEdgeSet_adj,
          Set.mem_singleton_iff, Sym2.eq_iff, Finset.mem_insert]
        aesop
      rwa [heq]

def doubleStar (H : SimpleGraph α) [DecidableRel H.Adj] (u v : α) : SimpleGraph α :=
  (starAt u (H.neighborFinset u \ {v}) ⊔ SimpleGraph.edge u v) ⊔
    starAt v (H.neighborFinset v \ {u})

omit [DecidableEq α] in
lemma starAt_le_of_mem_neighbor {H : SimpleGraph α} [DecidableRel H.Adj]
    {v : α} {I : Finset α} (hI : I ⊆ H.neighborFinset v) :
    starAt v I ≤ H := by
  intro a b hab
  rw [starAt_adj] at hab
  rcases hab.2 with ⟨rfl, hb⟩ | ⟨rfl, ha⟩
  · rw [← H.mem_neighborFinset]
    exact hI hb
  · rw [SimpleGraph.adj_comm, ← H.mem_neighborFinset]
    exact hI ha

lemma doubleStar_le {G H : SimpleGraph α} [DecidableRel H.Adj]
    {u v : α} (hHG : H ≤ G) (huv : H.Adj u v) :
    doubleStar H u v ≤ G := by
  apply sup_le
  · apply sup_le
    · exact (starAt_le_of_mem_neighbor Finset.sdiff_subset).trans hHG
    · have he : SimpleGraph.edge u v ≤ H :=
        (SimpleGraph.edge_le_iff H).2 (Or.inr huv)
      exact he.trans hHG
  · exact (starAt_le_of_mem_neighbor Finset.sdiff_subset).trans hHG

lemma doubleStar_degree_left (H : SimpleGraph α) [DecidableRel H.Adj]
    {u v : α} (huv : H.Adj u v) :
    H.degree u ≤ (doubleStar H u v).degree u := by
  rw [← H.card_neighborFinset_eq_degree,
    ← (doubleStar H u v).card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro x hx
  rw [H.mem_neighborFinset] at hx
  rw [(doubleStar H u v).mem_neighborFinset]
  by_cases hxv : x = v
  · subst x
    rw [doubleStar, SimpleGraph.sup_adj, SimpleGraph.sup_adj]
    exact Or.inl (Or.inr (by simp [SimpleGraph.edge_adj, huv.ne]))
  · rw [doubleStar, SimpleGraph.sup_adj, SimpleGraph.sup_adj]
    apply Or.inl
    apply Or.inl
    rw [starAt_adj]
    exact ⟨hx.ne, Or.inl ⟨rfl, by simp [hx, hxv]⟩⟩

lemma doubleStar_degree_right (H : SimpleGraph α) [DecidableRel H.Adj]
    {u v : α} (huv : H.Adj u v) :
    H.degree v ≤ (doubleStar H u v).degree v := by
  rw [← H.card_neighborFinset_eq_degree,
    ← (doubleStar H u v).card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro x hx
  rw [H.mem_neighborFinset] at hx
  rw [(doubleStar H u v).mem_neighborFinset]
  by_cases hxu : x = u
  · subst x
    rw [doubleStar, SimpleGraph.sup_adj, SimpleGraph.sup_adj]
    exact Or.inl (Or.inr (by simpa [SimpleGraph.edge_adj] using huv.ne.symm))
  · rw [doubleStar, SimpleGraph.sup_adj]
    apply Or.inr
    rw [starAt_adj]
    exact ⟨hx.ne, Or.inl ⟨rfl, by simp [hx, hxu]⟩⟩

lemma doubleStar_isAcyclic (H : SimpleGraph α) [DecidableRel H.Adj]
    (hfree : H.CliqueFree 3) {u v : α} (huv : H.Adj u v) :
    (doubleStar H u v).IsAcyclic := by
  let Iu := H.neighborFinset u \ {v}
  let Iv := H.neighborFinset v \ {u}
  have huIu : u ∉ Iu := by
    simp [Iu]
  have hstar : (starAt u Iu).IsAcyclic := by
    simpa using isAcyclic_sup_starAt (F := (⊥ : SimpleGraph α))
      SimpleGraph.isAcyclic_bot huIu (by simp)
  have hvSupport : v ∉ (starAt u Iu).support := by
    apply not_mem_support_starAt huv.ne.symm
    simp [Iu]
  have hreach : ¬(starAt u Iu).Reachable u v := by
    intro h
    exact hvSupport (SimpleGraph.mem_support_of_reachable huv.ne.symm h.symm)
  have hbase :
      (starAt u Iu ⊔ SimpleGraph.edge u v).IsAcyclic := by
    exact ((starAt u Iu).isAcyclic_add_edge_iff_of_not_reachable u v hreach).2 hstar
  have hvIv : v ∉ Iv := by simp [Iv]
  have hdis :
      ∀ x ∈ Iv, x ∉ (starAt u Iu ⊔ SimpleGraph.edge u v).support := by
    intro x hx
    have hxHv : H.Adj v x := by
      have := (Finset.mem_sdiff.mp hx).1
      rwa [H.mem_neighborFinset] at this
    have hxu : x ≠ u := by simpa [Iv] using (Finset.mem_sdiff.mp hx).2
    have hxv : x ≠ v := hxHv.ne.symm
    have hxIu : x ∉ Iu := by
      intro hxIu
      have hxHu : H.Adj u x := by
        have := (Finset.mem_sdiff.mp hxIu).1
        rwa [H.mem_neighborFinset] at this
      exact hfree {u, v, x}
        (SimpleGraph.is3Clique_triple_iff.mpr ⟨huv, hxHu, hxHv⟩)
    rw [SimpleGraph.mem_support]
    push Not
    intro y
    rw [SimpleGraph.sup_adj]
    rintro (hxy | hxy)
    · exact not_mem_support_starAt hxu hxIu ((SimpleGraph.mem_support _).mpr ⟨y, hxy⟩)
    · rw [SimpleGraph.edge_adj] at hxy
      rcases hxy.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxu rfl
      · exact hxv rfl
  simpa [doubleStar, Iu, Iv] using
    isAcyclic_sup_starAt
      (F := starAt u Iu ⊔ SimpleGraph.edge u v) hbase hvIv hdis

lemma exists_spanningTree_leafCount_ge_degree_sum
    [Nontrivial α] {G H : SimpleGraph α} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : G.Connected) (hHG : H ≤ G) (hfree : H.CliqueFree 3)
    {u v : α} (huv : H.Adj u v) :
    ∃ T : SimpleGraph α, ∃ _inst : DecidableRel T.Adj,
      T ≤ G ∧ T.IsTree ∧ H.degree u + H.degree v - 2 ≤ leafCount T := by
  let D := doubleStar H u v
  have hDG : D ≤ G := doubleStar_le hHG huv
  have hDacyc : D.IsAcyclic := doubleStar_isAcyclic H hfree huv
  obtain ⟨T, hDT, hmax⟩ :=
    G.exists_maximal_isAcyclic_of_le_isAcyclic hDG hDacyc
  let instT : DecidableRel T.Adj := Classical.decRel _
  letI : DecidableRel T.Adj := instT
  have hTG : T ≤ G := hmax.prop.1
  have hT : T.IsTree :=
    (hG.maximal_le_isAcyclic_iff_isTree hTG).mp hmax
  have hdu : H.degree u ≤ T.degree u :=
    (doubleStar_degree_left H huv).trans (SimpleGraph.degree_le_of_le hDT)
  have hdv : H.degree v ≤ T.degree v :=
    (doubleStar_degree_right H huv).trans (SimpleGraph.degree_le_of_le hDT)
  have hTuv : T.Adj u v := hDT (by
    dsimp [D]
    rw [doubleStar, SimpleGraph.sup_adj, SimpleGraph.sup_adj]
    exact Or.inl (Or.inr (by simpa [SimpleGraph.edge_adj] using huv.ne)))
  refine ⟨T, instT, hTG, hT, ?_⟩
  have hleaf := leafCount_ge_degree_add_degree_sub_two T hT hTuv
  omega

omit [DecidableEq α] in
lemma leafCount_le_Ls {G T : SimpleGraph α}
    [DecidableRel G.Adj] [DecidableRel T.Adj]
    (hTG : T ≤ G) (hT : T.IsTree) :
    (leafCount T : ℝ) ≤ G.Ls := by
  let S : G.Subgraph := G.toSubgraph T hTG
  have hspan : S.IsSpanning := SimpleGraph.toSubgraph.isSpanning T hTG
  have hSTree : S.coe.IsTree := by
    apply (S.spanningCoeEquivCoeOfSpanning hspan).isTree_iff.mp
    simpa [S] using hT
  have hleaves :
      S.verts.toFinset.filter (fun x => S.degree x = 1) =
        Finset.univ.filter (fun x => T.degree x = 1) := by
    ext x
    simp [S]
  have hbdd :
      BddAbove (Set.image
        (fun R : G.Subgraph =>
          ((R.verts.toFinset.filter fun x => R.degree x = 1).card : ℝ))
        {R : G.Subgraph | R.IsSpanning ∧ R.coe.IsTree}) := by
    refine ⟨(Fintype.card α : ℝ), ?_⟩
    rintro z ⟨R, -, rfl⟩
    change ((R.verts.toFinset.filter (fun x => R.degree x = 1)).card : ℝ) ≤
      (Fintype.card α : ℝ)
    exact_mod_cast (R.verts.toFinset.filter (fun x => R.degree x = 1)).card_le_univ
  unfold SimpleGraph.Ls
  apply le_csSup hbdd
  refine ⟨S, ⟨hspan, hSTree⟩, ?_⟩
  change ((S.verts.toFinset.filter (fun x => S.degree x = 1)).card : ℝ) =
    (leafCount T : ℝ)
  rw [leafCount, hleaves]

theorem conjecture2_of_nontrivial [Nontrivial α]
    (G : SimpleGraph α) (hG : G.Connected) :
    2 * (G.averageIndepNeighbors - 1) ≤ G.Ls := by
  classical
  obtain ⟨H, instH, hHG, hfree, hdeg⟩ :=
    exists_triangleFree_subgraph_degree_ge_indepNeighbors G
  letI : DecidableRel H.Adj := instH
  have hE : H.edgeFinset.Nonempty := by
    let a : α := Classical.choice (inferInstance : Nonempty α)
    obtain ⟨b, hab⟩ := hG.preconnected.exists_adj_of_nontrivial a
    let b' : G.neighborSet a := ⟨b, hab⟩
    have hs :
        (G.induce (G.neighborSet a)).IsIndepSet ({b'} : Finset (G.neighborSet a)) := by
      simp
    have hmu : 1 ≤ G.indepNeighborsCard a := by
      have hle := hs.card_le_indepNum
      simpa [SimpleGraph.indepNeighborsCard] using hle
    have hHa : 1 ≤ H.degree a := hmu.trans (hdeg a)
    obtain ⟨c, hac⟩ := (H.degree_pos_iff_exists_adj a).mp (by omega)
    refine ⟨s(a, c), ?_⟩
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hac
  obtain ⟨u, v, huv, hsumdeg⟩ :=
    exists_edge_degreeSum_ge_twice_average H hE
  obtain ⟨T, instT, hTG, hT, hleafNat⟩ :=
    exists_spanningTree_leafCount_ge_degree_sum hG hHG hfree huv
  letI : DecidableRel T.Adj := instT
  have hLs : (leafCount T : ℝ) ≤ G.Ls := leafCount_le_Ls hTG hT
  have havg :
      G.averageIndepNeighbors ≤
        (∑ x, (H.degree x : ℝ)) / (Fintype.card α : ℝ) := by
    unfold SimpleGraph.averageIndepNeighbors SimpleGraph.indepNeighbors
    gcongr with x
    exact_mod_cast hdeg x
  have hu1 : 1 ≤ H.degree u :=
    (H.degree_pos_iff_exists_adj u).mpr ⟨v, huv⟩
  have hv1 : 1 ≤ H.degree v :=
    (H.degree_pos_iff_exists_adj v).mpr ⟨u, huv.symm⟩
  have htwo : 2 ≤ H.degree u + H.degree v := by omega
  have hleafReal :
      (H.degree u : ℝ) + H.degree v - 2 ≤ (leafCount T : ℝ) := by
    calc
      _ = ((H.degree u + H.degree v - 2 : ℕ) : ℝ) := by
        rw [Nat.cast_sub htwo, Nat.cast_add]
        norm_num
      _ ≤ (leafCount T : ℝ) := by exact_mod_cast hleafNat
  calc
    2 * (G.averageIndepNeighbors - 1) =
        2 * G.averageIndepNeighbors - 2 := by ring
    _ ≤ (H.degree u : ℝ) + H.degree v - 2 := by
      nlinarith [havg, hsumdeg]
    _ ≤ (leafCount T : ℝ) := hleafReal
    _ ≤ G.Ls := hLs

theorem conjecture2 (G : SimpleGraph α) (h : G.Connected) :
    2 * (averageIndepNeighbors G - 1) ≤ Ls G := by
  classical
  rcases subsingleton_or_nontrivial α with hα | hα
  · letI : Subsingleton α := hα
    haveI : Nonempty α := h.nonempty
    have hGbot : G = ⊥ := by
      ext v w
      simp only [SimpleGraph.bot_adj, iff_false]
      intro hvw
      exact hvw.ne (Subsingleton.elim v w)
    subst G
    have hindep (x : α) :
        ((⊥ : SimpleGraph α).induce ((⊥ : SimpleGraph α).neighborSet x)).indepNum = 0 := by
      letI : IsEmpty ((⊥ : SimpleGraph α).neighborSet x) :=
        ⟨fun y => (SimpleGraph.bot_adj x y).mp y.property⟩
      obtain ⟨s, hs⟩ :=
        SimpleGraph.exists_isNIndepSet_indepNum
          (G := (⊥ : SimpleGraph α).induce ((⊥ : SimpleGraph α).neighborSet x))
      have hs0 : s = ∅ := Finset.eq_empty_of_forall_notMem isEmptyElim
      simpa [hs0] using hs.card_eq.symm
    have havg : (⊥ : SimpleGraph α).averageIndepNeighbors = 0 := by
      unfold SimpleGraph.averageIndepNeighbors SimpleGraph.indepNeighbors
        SimpleGraph.indepNeighborsCard
      simp_rw [hindep]
      simp
    have hLs : (0 : ℝ) ≤ (⊥ : SimpleGraph α).Ls := by
      have htree : (⊥ : SimpleGraph α).IsTree :=
        SimpleGraph.IsTree.of_subsingleton
      simpa [leafCount] using
        (leafCount_le_Ls (G := (⊥ : SimpleGraph α)) (T := (⊥ : SimpleGraph α))
          le_rfl htree)
    rw [havg]
    exact (by norm_num : (2 : ℝ) * (0 - 1) ≤ 0).trans hLs
  · letI : Nontrivial α := hα
    exact conjecture2_of_nontrivial G h

#check conjecture2
#print axioms conjecture2

end WrittenOnTheWallII.GraphConjecture2
