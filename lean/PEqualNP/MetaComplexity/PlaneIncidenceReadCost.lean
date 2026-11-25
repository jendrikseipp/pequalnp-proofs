import PEqualNP.Outside.L_meta_7684
import PEqualNP.Outside.L_meta_7639
import PEqualNP.Outside.L_meta_3716
import Mathlib.Combinatorics.Enumerative.DoubleCounting

-- For each incidence, a read-one proof tree uses its point and line once.
-- A perfect matching gives the lower bound, and the star construction attains it.
-- The construction and matching bound are the checked lemmas L-meta-7684 and L-meta-7639.

namespace PEqualNP.MetaComplexity.PlaneIncidenceReadCost

namespace Bounds


open PEqualNP.ReadK PEqualNP.CircuitLowerBounds

private def clip (k : ℕ) (v : List ℕ) := v.map fun x => min x (k + 1)
private def Related (k : ℕ) (A B : List (List ℕ)) : Prop :=
  ∀ v ∈ A, ∃ w ∈ B, v = clip k w

private lemma empty_related (k : ℕ) : Related k [] [] := by simp [Related]

private lemma insert_mem (A : List (List ℕ)) (v w : List ℕ) :
    w ∈ insertNew A v ↔ w ∈ A ∨ w = v := by
  unfold insertNew
  split_ifs with h <;> simp_all

private lemma fold_mem (A B : List (List ℕ)) (w : List ℕ) :
    w ∈ B.foldl insertNew A ↔ w ∈ A ∨ w ∈ B := by
  induction B generalizing A with
  | nil => simp
  | cons v vs ih => simp only [List.foldl_cons, ih, insert_mem, List.mem_cons]; tauto

private lemma add_clip {k l : ℕ} (hkl : k ≤ l) (u v : List ℕ) :
    capAdd k (clip k u) (clip k v) = clip k (capAdd l u v) := by
  induction u generalizing v with
  | nil => simp [clip, capAdd]
  | cons a t ih =>
    cases v with
    | nil => simp [clip, capAdd]
    | cons b s =>
      change (min (min a (k+1) + min b (k+1)) (k+1)) :: capAdd k (clip k t) (clip k s) =
        min (min (a+b) (l+1)) (k+1) :: clip k (capAdd l t s)
      rw [ih]
      congr 1
      omega

private lemma combine {k l : ℕ} (hkl : k ≤ l) {A A' B B' : List (List ℕ)}
    (ha : Related k A A') (hb : Related k B B') : Related k (andStep k A B) (andStep l A' B') := by
  intro v hv
  simp only [andStep, fold_mem, List.not_mem_nil, false_or, List.mem_flatMap,
    List.mem_map] at hv ⊢
  obtain ⟨u,hu,t,ht,rfl⟩ := hv
  obtain ⟨u',hu',rfl⟩ := ha u hu
  obtain ⟨t',ht',rfl⟩ := hb t ht
  exact ⟨capAdd l u' t', ⟨u',hu',t',ht',rfl⟩, add_clip hkl u' t'⟩

private lemma union_related {k : ℕ} {A A' B B' : List (List ℕ)}
    (ha : Related k A A') (hb : Related k B B') :
    Related k (B.foldl insertNew A) (B'.foldl insertNew A') := by
  intro v hv
  rcases (fold_mem A B v).mp hv with h | h
  · obtain ⟨w,hw,eq⟩ := ha v h; exact ⟨w, (fold_mem _ _ _).mpr (.inl hw),eq⟩
  · obtain ⟨w,hw,eq⟩ := hb v h; exact ⟨w, (fold_mem _ _ _).mpr (.inr hw),eq⟩

private lemma fold_related {α β γ δ : Type} (r : α → β → Prop) (s : γ → δ → Prop)
    (f : γ → α → γ) (g : δ → β → δ)
    (step : ∀ a b c d, r a b → s c d → s (f c a) (g d b))
    {x y} (h : List.Forall₂ r x y) {c d} (hc : s c d) :
    s (x.foldl f c) (y.foldl g d) := by
  induction h generalizing c d with
  | nil => exact hc
  | cons hx _ ih => exact ih (step _ _ _ _ hx hc)

private lemma get_related {k} {A B : List (List (List ℕ))}
    (h : List.Forall₂ (Related k) A B) (i : ℕ) : Related k (A.getD i []) (B.getD i []) := by
  induction h generalizing i with
  | nil => simpa using empty_related k
  | cons hx _ ih => cases i with
    | zero => exact hx
    | succ i => exact ih i

private lemma leaf_related {k l : ℕ} (S : List ℕ) (i : ℕ) :
    Related k (leafVectors S k i) (leafVectors S l i) := by
  by_cases hi : i ∈ S
  · intro v hv
    simp only [leafVectors, ite_eq_left hi, List.mem_singleton] at hv
    subst v
    refine ⟨S.map (fun j => if j = i then min 1 (l+1) else 0), ?_, ?_⟩
    · simp [leafVectors, hi]
    · unfold clip
      rw [List.map_map]
      apply List.map_congr_left
      intro j _
      by_cases hj : j = i <;> simp [hj]
  · simpa only [leafVectors, ite_eq_right hi] using empty_related k

private def step (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) :=
  let ins := g.inputs.map fun i => R.getD i []
  R ++ [match g.op with
    | .or => ins.foldl (fun acc A => A.foldl insertNew acc) []
    | .and => ins.foldl (andStep k) [S.map fun _ => 0]
    | _ => []]

private lemma read_related {k l : ℕ} (hkl : k ≤ l) (n : ℕ) (C : Circuit) (S : List ℕ) :
    List.Forall₂ (Related k) (readVectors C n S k) (readVectors C n S l) := by
  change List.Forall₂ _ (C.gates.foldl (step S k) _) (C.gates.foldl (step S l) _)
  apply fold_related Eq (List.Forall₂ (Related k)) (step S k) (step S l)
  · rintro g _ A B rfl h
    have ins : List.Forall₂ (Related k) (g.inputs.map fun i => A.getD i []) (g.inputs.map fun i => B.getD i []) := by
      induction g.inputs with
      | nil => exact .nil
      | cons i is ih => exact .cons (get_related h i) ih
    apply List.rel_append h
    apply List.Forall₂.cons _ List.Forall₂.nil
    cases g.op with
    | or =>
      exact fold_related (Related k) (Related k)
        (fun acc A => A.foldl insertNew acc) (fun acc A => A.foldl insertNew acc)
        (fun _ _ _ _ hb ha => union_related ha hb) ins (empty_related k)
    | and =>
      apply fold_related (Related k) (Related k) (andStep k) (andStep l) (fun _ _ _ _ hb ha => combine hkl ha hb) ins
      simp [Related, clip]
    | _ => exact empty_related k
  · induction C.gates with
    | nil => exact .nil
    | cons _ _ ih => exact .cons rfl ih
  · induction List.range n with
    | nil => exact .nil
    | cons i _ ih => exact .cons (leaf_related S i) ih

theorem monotone (n : ℕ) (C : Circuit) {k l : ℕ} (hkl : k ≤ l) (h : IsReadK n C k) :
    IsReadK n C l := by
  intro S hS
  have hw := h S hS
  simp only [readsAtMost, List.any_eq_true, List.all_eq_true, decide_eq_true_eq] at hw ⊢
  obtain ⟨v,hv,small⟩ := hw
  obtain ⟨w,hw,rfl⟩ := get_related (read_related hkl n C (setList S)) C.output v hv
  refine ⟨w, hw, ?_⟩
  intro x hx
  have hc := small (min x (k+1)) (List.mem_map.mpr ⟨x,hx,rfl⟩)
  omega

end Bounds


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK PEqualNP.TopForm

variable {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]

def flags : Finset (Fin N × Fin N) := Finset.univ.filter (fun e => I e.1 e.2)

def computes (C : Circuit) : Prop := ∀ z : Fin (N + N) → Bool,
  circuitFun (N+N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)

lemma count_flags (q : ℕ) (columns : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q+1) :
    (flags I).card = N*(q+1) := by
  classical
  have fiber (l : Fin N) : ((flags I).filter fun e => e.2 = l).card = q+1 := by
    rw [← columns l]
    apply Finset.card_bij (fun e _ => e.1)
    · intro e he
      obtain ⟨h,hl⟩ := Finset.mem_filter.mp he
      simpa only [flags, Finset.mem_filter, Finset.mem_univ, true_and, hl] using h
    · intro e he f hf eq
      exact Prod.ext eq ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)
    · intro p hp
      exact ⟨(p,l), by simpa [flags] using hp, rfl⟩
  calc
    (flags I).card = ∑ l : Fin N, ((flags I).filter (fun e => e.2 = l)).card :=
      Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (fun _ _ => Finset.mem_univ _)
    _ = N*(q+1) := by simp_rw [fiber]; simp

lemma matching (q : ℕ)
    (rows : ∀ p, (Finset.univ.filter (fun l => I p l)).card = q+1)
    (cols : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q+1) :
    ∃ perm : Equiv.Perm (Fin N), ∀ p, I p (perm p) := by
  classical
  let adj (p : Fin N) := Finset.univ.filter (fun l => I p l)
  have hall (S : Finset (Fin N)) : S.card ≤ (S.biUnion adj).card := by
    let T := S.biUnion adj
    have at_row (p : Fin N) (hp : p ∈ S) : (T.bipartiteAbove I p).card = q+1 := by
      have eq : T.bipartiteAbove I p = adj p := by
        ext l
        simp only [Finset.mem_bipartiteAbove, adj, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨And.right, fun h => ⟨Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩,h⟩⟩
      rw [eq];exact rows p
    have at_col (l : Fin N) (_ : l ∈ T) : (S.bipartiteBelow I l).card ≤ q+1 := by
      rw [← cols l]
      exact Finset.card_le_card (fun p h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩)
    have cnt := Finset.card_mul_le_card_mul I (fun p hp => (at_row p hp).ge) at_col
    exact Nat.le_of_mul_le_mul_right cnt (by omega)
  obtain ⟨f,hf,incident⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' adj).mp hall
  let perm := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  exact ⟨perm, fun p => (Finset.mem_filter.mp (incident p)).2⟩

lemma read_one_upper (q : ℕ) (cols : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q+1) :
    ∃ C : Circuit, IsAO2 (N+N) C ∧ computes I C ∧ IsReadK (N+N) C 1 ∧ C.size ≤ N*(q+2)-1 := by
  classical
  obtain ⟨C,ao,hsize,hfun,read⟩ := PEqualNP.Outside.L_meta_7684 N N (flags I) Finset.univ ∅ (fun _ _ => Or.inl (Finset.mem_univ _))
  refine ⟨C,ao,?_,read,?_⟩
  · intro x
    simpa [flags] using hfun x
  · rw [count_flags I q cols] at hsize
    simp only [Finset.card_univ,Fintype.card_fin,Finset.card_empty,Nat.add_zero] at hsize
    have h : N*(q+2) = N*(q+1)+N := by ring
    rwa [h]

lemma read_one_lower (q : ℕ) (C : Circuit)
    (rows : ∀ p, (Finset.univ.filter (fun l => I p l)).card = q+1)
    (cols : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (ao : IsAO2 (N+N) C) (hc : computes I C) (read : IsReadK (N+N) C 1) :
    N*(q+2) ≤ C.size + 1 := by
  classical
  obtain ⟨perm, inc⟩ := matching I q rows cols
  have rect : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ ((p,l) ∈ flags I ∧ (p,l') ∈ flags I ∧ (p',l) ∈ flags I ∧ (p',l') ∈ flags I) := by
    intro p p' l l' hpp hll h
    simp only [flags, Finset.mem_filter, Finset.mem_univ, true_and] at h
    obtain ⟨line,_,only⟩ := unique p p' hpp
    exact hll ((only l ⟨h.1,h.2.2.1⟩).trans (only l' ⟨h.2.1,h.2.2.2⟩).symm)
  have bound := PEqualNP.Outside.L_meta_7639 N (flags I) perm C rect
    (fun p => by simpa [flags] using inc p) ao (fun x => by simpa [flags] using hc x) read
  rw [count_flags I q cols] at bound
  have h : N*(q+2) = N*(q+1)+N := by ring
  rwa [h]

theorem sharp_read_one_budget (q k : ℕ) (hq : 2 ≤ q) (order : N = q^2 + q + 1)
    (columns : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    (∃ D : Circuit, IsAO2 (N+N) D ∧ computes I D ∧ D.size ≤ k ∧ IsReadK (N+N) D 1) ↔
      N*(q+2) ≤ k+1 := by
  constructor
  · rintro ⟨D, ao, correct, hs, hr⟩
    have rows := PEqualNP.Outside.L_meta_3716.point_deg q N I hq order columns unique
    have bound := read_one_lower I q D rows columns unique ao correct hr
    omega
  · intro hk
    obtain ⟨D,ao,correct,hr,hs⟩ := read_one_upper I q columns
    exact ⟨D,ao,correct,by omega,hr⟩


-- Every size budget attaining the read-one optimum also admits a read-two circuit.
theorem read_two_of_budget (q k : ℕ)
    (columns : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hk : N * (q + 2) ≤ k + 1) :
    ∃ D : Circuit, IsAO2 (N + N) D ∧ computes I D ∧ D.size ≤ k ∧ IsReadK (N + N) D 2 := by
  obtain ⟨D, ao, correct, read, hs⟩ := read_one_upper I q columns
  exact ⟨D, ao, correct, by omega, Bounds.monotone _ _ (by decide : 1 ≤ 2) read⟩

end PEqualNP.MetaComplexity.PlaneIncidenceReadCost
