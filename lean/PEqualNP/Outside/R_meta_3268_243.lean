import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Remove the eighth gate and keep at most five old observations. One binary
-- test on the earlier wires accounts for the remaining observation. Index 16 of
-- the seven-gate circuit reads false and represents any missing input wire.
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_3268_243
    (andTest :
      let edge := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun k => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
      ∀ D : Circuit, Monotone2 D → D.size = 7 →
        let read := fun (x : Fin 9 → Bool) (i : ℕ) => (D.wires (List.ofFn x)).getD i false
        (∀ x, read x 9 = (x 0 || x 2)) → ∀ T : Finset ℕ, T ⊆ Finset.range 16 → T.card ≤ 5 →
        ∀ a b : Fin 17, ∃ x y : Fin 9 → Bool, (∀ i ∈ T, read x i = read y i) ∧
          (read x a && read x b) = (read y a && read y b) ∧ edge x ≠ edge y)
    (orTest :
      let edge := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun k => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
      ∀ D : Circuit, Monotone2 D → D.size = 7 →
        let read := fun (x : Fin 9 → Bool) (i : ℕ) => (D.wires (List.ofFn x)).getD i false
        (∀ x, read x 9 = (x 0 || x 2)) → ∀ T : Finset ℕ, T ⊆ Finset.range 16 → T.card ≤ 5 →
        ∀ a b : Fin 17, ∃ x y : Fin 9 → Bool, (∀ i ∈ T, read x i = read y i) ∧
          (read x a || read x b) = (read y a || read y b) ∧ edge x ≠ edge y) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size = (8 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) → ∀ (x6 : Finset ℕ), x6.card ≤ (6 : ℕ) → ∃ (x8 : Fin (9 : ℕ) → Bool) (x9 : Fin (9 : ℕ) → Bool), (∀ x10 ∈ x6, (x2.wires (List.ofFn x8)).getD x10 Bool.false = (x2.wires (List.ofFn x9)).getD x10 Bool.false) ∧ x1 x8 ≠ x1 x9 := by
  intro edge C mono size first S budget
  have split : ∃ gs g, C.gates = gs ++ [g] := by
    cases h : C.gates.reverse with
    | nil =>
      have he := congrArg List.reverse h
      simp only [List.reverse_reverse, List.reverse_nil] at he
      change C.gates.length = 8 at size
      simp [he] at size
    | cons g rest =>
      refine ⟨rest.reverse, g, ?_⟩
      simpa using congrArg List.reverse h
  obtain ⟨gs, g, hgs⟩ := split
  let D : Circuit := ⟨gs, 0⟩
  have ds : D.size = 7 := by
    change C.gates.length = 8 at size
    rw [hgs, List.length_append] at size
    change gs.length = 7
    simpa using size
  have dm : Monotone2 D := by
    intro h hh
    exact mono h (by rw [hgs]; exact List.mem_append_left _ hh)
  have hg := mono g (by rw [hgs]; simp)
  let wires := fun x : Fin 9 → Bool => D.wires (List.ofFn x)
  let read := fun (x : Fin 9 → Bool) (i : ℕ) => (wires x).getD i false
  let last := fun x : Fin 9 → Bool => g.op.eval (g.inputs.map (read x))
  have extend (x : Fin 9 → Bool) : C.wires (List.ofFn x) = wires x ++ [last x] := by
    change C.gates.foldl (fun w h => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]) (List.ofFn x) = _
    rw [hgs, List.foldl_append]
    rfl
  have length (x : Fin 9 → Bool) : (wires x).length = 16 := by
    let step := fun (w : List Bool) (h : Gate) => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]
    have run (hs : List Gate) (w : List Bool) : (hs.foldl step w).length = w.length + hs.length := by
      induction hs generalizing w with
      | nil => simp
      | cons h hs ih => rw [List.foldl_cons, ih]; simp [step]; omega
    change (gs.foldl step (List.ofFn x)).length = 16
    change gs.length = 7 at ds
    rw [run, List.length_ofFn, ds]
  have old (x : Fin 9 → Bool) (i : ℕ) (hi : i < 16) :
      (C.wires (List.ofFn x)).getD i false = read x i := by
    rw [extend]
    exact List.getD_append _ _ _ _ (by simpa only [length] using hi)
  have finalWire (x : Fin 9 → Bool) : (C.wires (List.ofFn x)).getD 16 false = last x := by
    rw [extend, ← length x]
    simp [List.getD_eq_getElem?_getD]
  have out (x : Fin 9 → Bool) (i : ℕ) (hi : 16 < i) : (C.wires (List.ofFn x)).getD i false = false := by
    apply List.getD_eq_default
    rw [extend, List.length_append, length]
    change 16 + 1 ≤ i
    omega
  have firstD (x : Fin 9 → Bool) : read x 9 = (x 0 || x 2) := by
    rw [← old x 9 (by decide)]
    exact first x
  by_cases empty : S = ∅
  · subst S
    exact ⟨fun _ => false, fun _ => true, by simp, by decide⟩
  have nonempty := Finset.nonempty_iff_ne_empty.mpr empty
  obtain ⟨k, hk, priority⟩ : ∃ k ∈ S, 16 ∈ S → k = 16 := by
    by_cases h : 16 ∈ S
    · exact ⟨16, h, fun _ => rfl⟩
    · obtain ⟨k, hk⟩ := nonempty
      exact ⟨k, hk, fun h' => (h h').elim⟩
  let T := (S.erase k).filter (fun i => i < 16)
  have small : T ⊆ Finset.range 16 := fun i hi => Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  have count : T.card ≤ 5 := by
    have h := Finset.card_filter_le (S.erase k) (fun i => i < 16)
    have h' := Finset.card_erase_add_one hk
    change ((S.erase k).filter _).card ≤ 5
    omega
  let clamp (i : ℕ) : Fin 17 := ⟨min i 16, by omega⟩
  have clipped (x : Fin 9 → Bool) (i : ℕ) : read x (clamp i) = read x i := by
    by_cases h : i ≤ 16
    · change read x (min i 16) = read x i
      rw [min_eq_left h]
    · change (wires x).getD (min i 16) false = (wires x).getD i false
      rw [min_eq_right (by omega), List.getD_eq_default _ _ (by rw [length]),
        List.getD_eq_default _ _ (by rw [length]; omega)]
  have liftPair (x y : Fin 9 → Bool) (agree : ∀ i ∈ T, read x i = read y i)
      (special : (C.wires (List.ofFn x)).getD k false = (C.wires (List.ofFn y)).getD k false)
      (diff : edge x ≠ edge y) : ∃ x y : Fin 9 → Bool,
        (∀ i ∈ S, (C.wires (List.ofFn x)).getD i false = (C.wires (List.ofFn y)).getD i false) ∧
        edge x ≠ edge y := by
    refine ⟨x, y, ?_, diff⟩
    intro i hi
    by_cases eq : i = k
    · simpa [eq] using special
    have ne : i ≠ 16 := by
      rintro rfl
      exact eq (priority hi).symm
    rcases lt_or_gt_of_ne ne with h | h
    · rw [old _ _ h, old _ _ h]
      exact agree i (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨eq, hi⟩, h⟩)
    · rw [out _ _ h, out _ _ h]
  have conj := andTest D dm ds firstD T small count
  have disj := orTest D dm ds firstD T small count
  change ∀ a b : Fin 17, ∃ x y, (∀ i ∈ T, read x i = read y i) ∧
    (read x a && read x b) = (read y a && read y b) ∧ edge x ≠ edge y at conj
  change ∀ a b : Fin 17, ∃ x y, (∀ i ∈ T, read x i = read y i) ∧
    (read x a || read x b) = (read y a || read y b) ∧ edge x ≠ edge y at disj
  by_cases final : k = 16
  · subst k
    have solveLast (x y : Fin 9 → Bool) (same : ∀ i ∈ T, read x i = read y i)
        (equal : last x = last y) (different : edge x ≠ edge y) :=
      liftPair x y same (by simpa only [finalWire] using equal) different
    rcases g with ⟨op, ins⟩
    rcases hg with ⟨hop, hlen⟩
    change op = GateOp.and ∨ op = GateOp.or at hop
    change ins.length ≤ 2 at hlen
    cases ins with
    | nil =>
      obtain ⟨x, y, same, _, different⟩ := disj 0 0
      exact solveLast x y same rfl different
    | cons a more =>
      cases more with
      | nil =>
        obtain ⟨x, y, same, equal, different⟩ := disj (clamp a) (clamp a)
        simp only [Bool.or_self, clipped] at equal
        apply solveLast x y same _ different
        change op.eval ([read x a]) = op.eval ([read y a])
        rw [equal]
      | cons b rest =>
        cases rest with
        | cons c rest => simp at hlen
        | nil =>
          rcases hop with rfl | rfl
          · obtain ⟨x, y, same, equal, different⟩ := conj (clamp a) (clamp b)
            apply solveLast x y same _ different
            change (read x a && (read x b && true)) = (read y a && (read y b && true))
            simpa only [Bool.and_true, clipped] using equal
          · obtain ⟨x, y, same, equal, different⟩ := disj (clamp a) (clamp b)
            apply solveLast x y same _ different
            change (read x a || (read x b || false)) = (read y a || (read y b || false))
            simpa only [Bool.or_false, clipped] using equal
  · obtain ⟨x, y, same, equal, different⟩ := disj (clamp k) (clamp k)
    apply liftPair x y same _ different
    rcases lt_or_gt_of_ne final with h | h
    · simpa only [old _ _ h, Bool.or_self, clipped] using equal
    · rw [out _ _ h, out _ _ h]
