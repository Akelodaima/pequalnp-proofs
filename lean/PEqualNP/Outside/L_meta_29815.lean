import Mathlib

def pnpStep (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- Input `[a, p, q, true, false, false, false]` as a function on `Fin 7`. -/
def pnpInp (a p q : Bool) : Fin 7 → Bool :=
  fun i => [a, p, q, true, false, false, false].getD i.val false

theorem pnp_ofFn_inp (a p q : Bool) :
    List.ofFn (pnpInp a p q) = [a, p, q, true, false, false, false] := by
  cases a <;> cases p <;> cases q <;>
    first | decide | rfl | simp [pnpInp, List.ofFn_succ]

/-- A gate step keeps two wire lists equal except in position 0. -/
theorem pnp_step (g : PEqualNP.CircuitLowerBounds.Gate) (a b p q : Bool) (r : List Bool)
    (hg : 0 ∉ g.inputs ∨
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 3 ∈ g.inputs)) :
    ∃ x : Bool,
      pnpStep (a :: p :: q :: true :: r) g = a :: p :: q :: true :: (r ++ [x]) ∧
      pnpStep (b :: p :: q :: true :: r) g = b :: p :: q :: true :: (r ++ [x]) := by
  have key : g.op.eval (g.inputs.map fun i => (a :: p :: q :: true :: r).getD i false)
      = g.op.eval (g.inputs.map fun i => (b :: p :: q :: true :: r).getD i false) := by
    rcases hg with h0 | ⟨hop, h3⟩
    · congr 1
      apply List.map_congr_left
      intro i hi
      have hi0 : i ≠ 0 := fun h => h0 (by subst h; exact hi)
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
      simp
    · have hv : ∀ c : Bool,
          g.op.eval (g.inputs.map fun i => (c :: p :: q :: true :: r).getD i false)
            = true := by
        intro c
        rw [hop]
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_eq_true]
        exact ⟨true, List.mem_map.mpr ⟨3, h3, by simp⟩, rfl⟩
      rw [hv a, hv b]
  refine ⟨g.op.eval (g.inputs.map fun i => (a :: p :: q :: true :: r).getD i false),
    ?_, ?_⟩
  · first | rfl | simp [pnpStep]
  · unfold pnpStep
    rw [← key]
    first | rfl | simp

theorem pnp_fold (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hgs : ∀ g ∈ gs, 0 ∉ g.inputs ∨
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 3 ∈ g.inputs)) :
    ∀ (a b p q : Bool) (r : List Bool), ∃ r' : List Bool,
      gs.foldl pnpStep (a :: p :: q :: true :: r) = a :: p :: q :: true :: r' ∧
      gs.foldl pnpStep (b :: p :: q :: true :: r) = b :: p :: q :: true :: r' := by
  induction gs with
  | nil =>
    intro a b p q r
    exact ⟨r, rfl, rfl⟩
  | cons g gs ih =>
    intro a b p q r
    obtain ⟨x, h1, h2⟩ := pnp_step g a b p q r
      (hgs g (List.mem_cons.mpr (Or.inl rfl)))
    obtain ⟨r', e1, e2⟩ := ih
      (fun g' hg' => hgs g' (List.mem_cons.mpr (Or.inr hg'))) a b p q (r ++ [x])
    refine ⟨r', ?_, ?_⟩
    · rw [List.foldl_cons, h1]; exact e1
    · rw [List.foldl_cons, h2]; exact e2

theorem pnp_unit_false :
    ¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length),
      i.val = 3 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧
      (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧
      0 ∈ (C.gates.get i).inputs ∧
      (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧
      (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧
      3 ∈ (C.gates.get i).inputs ∧ 3 ≠ 0 ∧ 3 < 7 + i.val ∧
      ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧
        (C.wires (List.ofFn x)).getD 3 false = true) := by
  rintro ⟨C, i, k, -, -, -, hf, -, huniq, hor, -, -, -, h3, -, -, -⟩
  -- every gate either avoids wire 0, or is gate i (an OR reading wire 3)
  have hgs : ∀ g ∈ C.gates, 0 ∉ g.inputs ∨
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 3 ∈ g.inputs) := by
    intro g hg
    by_cases h : 0 ∈ g.inputs
    · right
      obtain ⟨j, hj⟩ : ∃ j : Fin C.gates.length, C.gates.get j = g := by
        first
          | exact List.get_of_mem hg
          | exact List.mem_iff_get.mp hg
          | (obtain ⟨n, hn, e⟩ := List.getElem_of_mem hg; exact ⟨⟨n, hn⟩, e⟩)
      have hji : j = i := huniq j (by rw [hj]; exact h)
      rw [hji] at hj
      subst hj
      exact ⟨hor, h3⟩
    · left
      exact h
  have hev : ∀ a b p q : Bool, ∃ r' : List Bool,
      C.wires [a, p, q, true, false, false, false] = a :: p :: q :: true :: r' ∧
      C.wires [b, p, q, true, false, false, false] = b :: p :: q :: true :: r' :=
    fun a b p q => pnp_fold C.gates hgs a b p q [false, false, false]
  by_cases hout : C.output = 0
  · -- the output is wire 0 itself, which is just x0
    have f1 : C.eval [false, true, true, true, false, false, false] = true := by
      have h := hf (pnpInp false true true)
      rw [pnp_ofFn_inp] at h
      exact h.trans (by first | decide | simp [pnpInp])
    obtain ⟨r', e1, -⟩ := hev false false true true
    have s1 : C.eval [false, true, true, true, false, false, false]
        = (C.wires [false, true, true, true, false, false, false]).getD C.output false :=
      rfl
    have g1 : C.eval [false, true, true, true, false, false, false] = false := by
      rw [s1, e1, hout] <;> simp
    have := f1.symm.trans g1
    simp at this
  · -- the output ignores x0 when x3 = true, yet the target function does not
    have f2 : C.eval [false, true, false, true, false, false, false] = false := by
      have h := hf (pnpInp false true false)
      rw [pnp_ofFn_inp] at h
      exact h.trans (by first | decide | simp [pnpInp])
    have f3 : C.eval [true, true, false, true, false, false, false] = true := by
      have h := hf (pnpInp true true false)
      rw [pnp_ofFn_inp] at h
      exact h.trans (by first | decide | simp [pnpInp])
    obtain ⟨r', e2, e3⟩ := hev false true true false
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hout
    have s2 : C.eval [false, true, false, true, false, false, false]
        = (C.wires [false, true, false, true, false, false, false]).getD C.output false :=
      rfl
    have s3 : C.eval [true, true, false, true, false, false, false]
        = (C.wires [true, true, false, true, false, false, false]).getD C.output false :=
      rfl
    have heq : C.eval [false, true, false, true, false, false, false]
        = C.eval [true, true, false, true, false, false, false] := by
      rw [s2, s3, e2, e3, hm] <;> simp
    rw [f2, f3] at heq
    simp at heq
