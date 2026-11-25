import PEqualNP.Outside.L_meta_3519

-- In the star circuit for a nonempty bipartite graph, each spoke costs one gate,
-- and combining the stars costs one fewer gate than the number of centers.
-- The upper bound uses the project's checked construction in L-meta-3519.

namespace PEqualNP.MetaComplexity.StarCoverCost

abbrev Star := ℕ × List ℕ

def cost (stars : List Star) : ℕ :=
  (stars.map fun s => s.2.length).sum + stars.length - 1

def Covers {a b : ℕ} (edges : Finset (Fin a × Fin b)) (stars : List Star) : Prop :=
  (∀ s ∈ stars, s.2 ≠ [] ∧
    ((s.1 < a ∧ ∀ t ∈ s.2, a ≤ t ∧ t < a + b) ∨
     (a ≤ s.1 ∧ s.1 < a + b ∧ ∀ t ∈ s.2, t < a))) ∧
  ∀ (p : Fin a) (l : Fin b), (p, l) ∈ edges ↔ ∃ s ∈ stars,
    (s.1 = p.val ∧ a + l.val ∈ s.2) ∨ (s.1 = a + l.val ∧ p.val ∈ s.2)

private def expand (s : Star) : List (ℕ × ℕ) :=
  s.2.map fun t => (min s.1 t, max s.1 t)

private lemma expand_length (stars : List Star) :
    (stars.flatMap expand).length = (stars.map fun s => s.2.length).sum := by
  induction stars with
  | nil => rfl
  | cons s t ih => simp [expand, List.flatMap_cons, ih]

private def encode (a b : ℕ) : Fin a × Fin b ↪ ℕ × ℕ where
  toFun e := (e.1.val, a + e.2.val)
  inj' := by
    intro x y h
    exact Prod.ext (Fin.ext (congrArg Prod.fst h))
      (Fin.ext (Nat.add_left_cancel (congrArg Prod.snd h)))

private lemma edge_count {a b : ℕ} {edges : Finset (Fin a × Fin b)}
    {stars : List Star} (h : Covers edges stars) :
    edges.card ≤ (stars.map fun s => s.2.length).sum := by
  classical
  have sub : edges.map (encode a b) ⊆ (stars.flatMap expand).toFinset := by
    intro code hc
    obtain ⟨⟨p, l⟩, he, rfl⟩ := Finset.mem_map.mp hc
    obtain ⟨s, hs, own⟩ := (h.2 p l).mp he
    have hle : p.val ≤ a + l.val := by have := p.isLt; omega
    apply List.mem_toFinset.mpr
    refine List.mem_flatMap.mpr ⟨s, hs, ?_⟩
    change (p.val, a + l.val) ∈ s.2.map _
    rcases own with ⟨center, leaf⟩ | ⟨center, leaf⟩
    · exact List.mem_map.mpr ⟨a + l.val, leaf, by simp [center, min_eq_left hle, max_eq_right hle]⟩
    · exact List.mem_map.mpr ⟨p.val, leaf, by simp [center, min_eq_right hle, max_eq_left hle]⟩
  have count := (Finset.card_le_card sub).trans (List.toFinset_card_le _)
  simpa only [Finset.card_map, expand_length] using count

-- A star cover meets a budget exactly when a vertex cover meets the corresponding budget.
theorem budget_iff {a b : ℕ} (edges : Finset (Fin a × Fin b)) (k : ℕ) :
    (∃ stars, Covers edges stars ∧ cost stars ≤ k) ↔
    ∃ (points : Finset (Fin a)) (lines : Finset (Fin b)),
      (∀ e ∈ edges, e.1 ∈ points ∨ e.2 ∈ lines) ∧
      edges.card + points.card + lines.card - 1 ≤ k := by
  classical
  constructor
  · rintro ⟨stars, hs, hk⟩
    let centers := (stars.map Prod.fst).toFinset
    let points := Finset.univ.filter fun p : Fin a => p.val ∈ centers
    let lines := Finset.univ.filter fun l : Fin b => a + l.val ∈ centers
    refine ⟨points, lines, ?_, ?_⟩
    · rintro ⟨p,l⟩ he
      obtain ⟨s, hmem, hor⟩ := (hs.2 p l).mp he
      have hc : s.1 ∈ centers := List.mem_toFinset.mpr (List.mem_map.mpr ⟨s, hmem, rfl⟩)
      rcases hor with ⟨eq, _⟩ | ⟨eq, _⟩
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, eq ▸ hc⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, eq ▸ hc⟩)
    · let leftCodes := points.image Fin.val
      let rightCodes := lines.image fun l => a + l.val
      have dis : Disjoint leftCodes rightCodes := by
        apply Finset.disjoint_left.mpr
        intro v hv hw
        obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨l, _, eq⟩ := Finset.mem_image.mp hw
        have := p.isLt
        omega
      have sub : leftCodes ∪ rightCodes ⊆ centers := by
        intro v hv
        rcases Finset.mem_union.mp hv with hp | hl
        · obtain ⟨p, hmem, rfl⟩ := Finset.mem_image.mp hp
          exact (Finset.mem_filter.mp hmem).2
        · obtain ⟨l, hmem, rfl⟩ := Finset.mem_image.mp hl
          exact (Finset.mem_filter.mp hmem).2
      have hleft : leftCodes.card = points.card := Finset.card_image_of_injective _ Fin.val_injective
      have hright : rightCodes.card = lines.card := Finset.card_image_of_injective _
        (fun _ _ h => Fin.ext (Nat.add_left_cancel h))
      have hc := (Finset.card_le_card sub).trans (List.toFinset_card_le _)
      rw [Finset.card_union_of_disjoint dis, hleft, hright, List.length_map] at hc
      have he := edge_count hs
      unfold cost at hk
      omega
  · rintro ⟨points, lines, hcov, hk⟩
    obtain ⟨stars, hshape, hedges, hcost⟩ :=
      PEqualNP.Outside.L_meta_3519 a b edges points lines hcov
    exact ⟨stars, ⟨hshape, hedges⟩, hcost.trans hk⟩

private theorem vertex_cover_exists {a b : ℕ} (edges : Finset (Fin a × Fin b)) :
    ∃ t : ℕ, ∃ (points : Finset (Fin a)) (lines : Finset (Fin b)),
      (∀ e ∈ edges, e.1 ∈ points ∨ e.2 ∈ lines) ∧ points.card + lines.card = t := by
  refine ⟨_, Finset.univ, ∅, ?_, rfl⟩
  exact fun _ _ => Or.inl (Finset.mem_univ _)

noncomputable def vertexCoverNumber {a b : ℕ} (edges : Finset (Fin a × Fin b)) : ℕ := by
  classical
  exact Nat.find (vertex_cover_exists edges)

-- The truncated subtraction also gives the empty graph cost zero.
theorem cost_iff {a b : ℕ} (edges : Finset (Fin a × Fin b)) (k : ℕ) :
    (∃ stars, Covers edges stars ∧ cost stars ≤ k) ↔
      edges.card + vertexCoverNumber edges - 1 ≤ k := by
  classical
  rw [budget_iff]
  constructor
  · rintro ⟨points, lines, hcover, hk⟩
    have hmin : vertexCoverNumber edges ≤ points.card + lines.card :=
      Nat.find_min' (vertex_cover_exists edges) ⟨points, lines, hcover, rfl⟩
    omega
  · intro hk
    obtain ⟨points, lines, hcover, hmin⟩ := Nat.find_spec (vertex_cover_exists edges)
    change points.card + lines.card = vertexCoverNumber edges at hmin
    exact ⟨points, lines, hcover, by omega⟩

end PEqualNP.MetaComplexity.StarCoverCost
