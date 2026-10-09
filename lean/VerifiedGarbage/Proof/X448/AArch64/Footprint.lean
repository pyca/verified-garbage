import VerifiedGarbage.Proof.Framework.AArch64.Interleave

/-!
# AArch64: footprints bounded once for any slots

Untrusted: everything here is checked by Lean. Two interleaved blocks are
independent if their footprints are (`indeps_of_check`), which the kernel
checks by building the code of each block and its footprint. For code built
by a generator from slots (`[o] := [a] * [b]` and the like), the footprint is
the same for every choice of slots, but for where it reads and writes memory:
a bound (`Bnd`) with windows of bytes for memory, checked once for the code
at probe slots (`fpIn`), holds for the code at any slots, with its windows
moved to them (`fpIn_reloc`), as the code at any slots is the code at the
probe slots with its offsets moved (`relocI`, checked once by the kernel for
any slots). Independence then needs only the bounds' (`indeps_of_bnd`).
-/

namespace VG.AArch64.Interleave

/-- A bound on footprints: register masks, the flags, and the windows
`(base, len)` of the bytes (at offsets from `x3`) read and written. -/
structure Bnd where
  gr : Nat
  gw : Nat
  vr : Nat
  vw : Nat
  cr : Bool
  cw : Bool
  rd : List (Nat × Nat)
  wr : List (Nat × Nat)

/-- The bytes of windows. -/
def winMask : List (Nat × Nat) → Nat
  | [] => 0
  | (b, l) :: ws => range b l ||| winMask ws

def Bnd.toFp (U : Bnd) : Fp := ⟨U.gr, U.gw, U.vr, U.vw, U.cr, U.cw, winMask U.rd, winMask U.wr⟩

def Bnd.union (U V : Bnd) : Bnd :=
  ⟨U.gr ||| V.gr, U.gw ||| V.gw, U.vr ||| V.vr, U.vw ||| V.vw, U.cr || V.cr, U.cw || V.cw,
    U.rd ++ V.rd, U.wr ++ V.wr⟩

/-- `[off, off + n)` lies in a window. -/
def inWin (off n : Nat) : List (Nat × Nat) → Bool
  | [] => false
  | (b, l) :: ws => (Nat.ble b off && Nat.ble (off + n) (b + l)) || inWin off n ws

/-- Every bit of `a` is one of `b`. -/
def subM (a b : Nat) : Bool := a &&& b == a

/-- The bytes an instruction reads or writes lie in the bound's windows. -/
def memIn (U : Bnd) : Instr → Bool
  | .ldr sz _ _ off => inWin off sz.bytes U.rd
  | .str sz _ _ off => inWin off sz.bytes U.wr
  | .ldrq _ _ off => inWin off 16 U.rd
  | .strq _ _ off => inWin off 16 U.wr
  | _ => true

/-- The instruction has a footprint, within the bound. -/
def fpIn (U : Bnd) (i : Instr) : Bool :=
  match fp i with
  | none => false
  | some F => subM F.gr U.gr && subM F.gw U.gw && subM F.vr U.vr && subM F.vw U.vw &&
      (!F.cr || U.cr) && (!F.cw || U.cw) && memIn U i

/-! ## Soundness -/

theorem subM_bit {a b : Nat} (h : subM a b = true) {i : Nat} (hi : a.testBit i = true) : b.testBit i = true := by
  have h : a &&& b = a := by simpa [subM] using h
  have := congrArg (Nat.testBit · i) h
  simp only [Nat.testBit_and, hi, Bool.true_and] at this
  exact this

theorem winMask_bit {off n : Nat} : ∀ {ws : List (Nat × Nat)}, inWin off n ws = true →
    ∀ k, (range off n).testBit k = true → (winMask ws).testBit k = true
  | [], h, _, _ => by cases h
  | (b, l) :: ws, h, k, hk => by
    simp only [inWin, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq] at h
    simp only [winMask, Nat.testBit_or, Bool.or_eq_true]
    rcases h with ⟨h1, h2⟩ | h
    · left
      simp only [testBit_range, decide_eq_true_eq] at hk ⊢
      omega
    · exact .inr (winMask_bit h k hk)

theorem fp_mem {i : Instr} {F : Fp} (hf : fp i = some F) {U : Bnd} (hm : memIn U i = true) :
    (∀ k, F.mr.testBit k = true → (winMask U.rd).testBit k = true) ∧
    (∀ k, F.mw.testBit k = true → (winMask U.wr).testBit k = true) := by
  cases i with
  | ldr sz t n off =>
    simp only [fp] at hf
    split at hf
    · cases hf
      exact ⟨winMask_bit hm, fun k hk => by simp at hk⟩
    · cases hf
  | str sz t n off =>
    simp only [fp] at hf
    split at hf
    · cases hf
      exact ⟨fun k hk => by simp at hk, winMask_bit hm⟩
    · cases hf
  | ldrq t n off =>
    simp only [fp] at hf
    split at hf
    · cases hf
      exact ⟨winMask_bit hm, fun k hk => by simp at hk⟩
    · cases hf
  | strq t n off =>
    simp only [fp] at hf
    split at hf
    · cases hf
      exact ⟨fun k hk => by simp at hk, winMask_bit hm⟩
    · cases hf
  | vop op =>
    simp only [fp] at hf
    have := VOp.fp_shape hf
    refine ⟨fun k hk => ?_, fun k hk => by simp [this.2.2] at hk⟩
    cases op <;> simp only [VOp.fp, Option.some.injEq, reduceCtorEq] at hf <;> subst hf <;>
      simp [vecFp] at hk
  | _ =>
    simp only [fp, regFp, Option.some.injEq, reduceCtorEq] at hf
    all_goals (subst hf; exact ⟨fun k hk => by simp at hk, fun k hk => by simp at hk⟩)

theorem fpIn_sub {U : Bnd} {i : Instr} (h : fpIn U i = true) : ∃ F, fp i = some F ∧ Sub F U.toFp := by
  unfold fpIn at h
  cases hf : fp i with
  | none => rw [hf] at h; cases h
  | some F =>
    rw [hf] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
    obtain ⟨m1, m2⟩ := fp_mem hf h7
    refine ⟨F, rfl, ⟨fun _ => subM_bit h1, fun _ => subM_bit h2, fun _ => subM_bit h3,
      fun _ => subM_bit h4, fun hc => ?_, fun hc => ?_, m1, m2⟩⟩
    · rcases h5 with h5 | h5
      · rw [hc] at h5; cases h5
      · exact h5
    · rcases h6 with h6 | h6
      · rw [hc] at h6; cases h6
      · exact h6

/-- Blocks within bounds that are independent are independent. -/
theorem indeps_of_bnd {a b : List Instr} {A B : Bnd} (ha : ∀ x ∈ a, fpIn A x = true)
    (hb : ∀ y ∈ b, fpIn B y = true) (h : A.toFp.indep B.toFp = true) : Indeps a b := by
  intro x hx y hy
  obtain ⟨F, hx', hF⟩ := fpIn_sub (ha x hx)
  obtain ⟨G, hy', hG⟩ := fpIn_sub (hb y hy)
  exact ⟨F, G, hx', hy', (Indep.of h).mono hF hG⟩

/-! ## Moving the slots -/

/-- The size of a probe slot's window. -/
def W : Nat := 4096

/-- An offset in the window `[p, p + W)` of a pair `(p, q)` moves to `q + (off - p)`. -/
def relocOff : List (Nat × Nat) → Nat → Nat
  | [], off => off
  | (p, q) :: ws, off => bif Nat.ble p off && Nat.blt off (p + W) then q + (off - p) else relocOff ws off

/-- The instruction with its offsets moved. -/
def relocI (ws : List (Nat × Nat)) : Instr → Instr
  | .ldr sz t n off => .ldr sz t n (relocOff ws off)
  | .str sz t n off => .str sz t n (relocOff ws off)
  | .ldrq t n off => .ldrq t n (relocOff ws off)
  | .strq t n off => .strq t n (relocOff ws off)
  | i => i

def Bnd.reloc (ws : List (Nat × Nat)) (U : Bnd) : Bnd :=
  { U with rd := U.rd.map fun w => (relocOff ws w.1, w.2), wr := U.wr.map fun w => (relocOff ws w.1, w.2) }

/-- The probes' windows are disjoint. -/
def sepB : List Nat → Bool
  | [] => true
  | p :: ps => ps.all (fun p' => Nat.ble (p + W) p' || Nat.ble (p' + W) p) && sepB ps

/-- A window lies in a probe's window, or outside all of them. -/
def alignedB (ps : List Nat) (w : Nat × Nat) : Bool :=
  ps.any (fun p => Nat.ble p w.1 && Nat.ble (w.1 + w.2) (p + W)) ||
    ps.all (fun p => Nat.ble (w.1 + w.2) p || Nat.ble (p + W) w.1)

theorem win_true {p off : Nat} (h1 : p ≤ off) (h2 : off < p + W) :
    (Nat.ble p off && Nat.blt off (p + W)) = true := by
  simp [h1, h2]

theorem win_false {p off : Nat} (h : ¬ (p ≤ off ∧ off < p + W)) :
    (Nat.ble p off && Nat.blt off (p + W)) = false := by
  rw [Bool.eq_false_iff]
  intro hc
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hc
  exact h hc

theorem reloc_out {off : Nat} : ∀ {ws : List (Nat × Nat)}, (∀ w ∈ ws, ¬ (w.1 ≤ off ∧ off < w.1 + W)) →
    relocOff ws off = off
  | [], _ => rfl
  | (p, q) :: ws, h => by
    simp only [relocOff, win_false (h (p, q) List.mem_cons_self), Bool.cond_false]
    exact reloc_out fun w hw => h w (List.mem_cons_of_mem _ hw)

theorem reloc_in {off p q : Nat} (hp : p ≤ off) (hw : off < p + W) :
    ∀ {ws : List (Nat × Nat)}, sepB (ws.map Prod.fst) = true → (p, q) ∈ ws → relocOff ws off = q + (off - p)
  | [], _, h => by cases h
  | (p', q') :: ws, hs, h => by
    simp only [List.map_cons, sepB, Bool.and_eq_true, List.all_eq_true, List.mem_map, Bool.or_eq_true,
      Nat.ble_eq] at hs
    rcases List.mem_cons.mp h with h | h
    · cases h
      simp only [relocOff, win_true hp hw, Bool.cond_true]
    · have hd := hs.1 p ⟨(p, q), h, rfl⟩
      simp only [relocOff, win_false (show ¬ (p' ≤ off ∧ off < p' + W) by omega), Bool.cond_false]
      exact reloc_in hp hw hs.2 h

theorem inWin_reloc {off n : Nat} (hn : 0 < n) {ws : List (Nat × Nat)} (hs : sepB (ws.map Prod.fst) = true) :
    ∀ {wins : List (Nat × Nat)}, (∀ w ∈ wins, alignedB (ws.map Prod.fst) w = true) → inWin off n wins = true →
      inWin (relocOff ws off) n (wins.map fun w => (relocOff ws w.1, w.2)) = true
  | [], _, h => by cases h
  | (b, l) :: wins, ha, h => by
    simp only [inWin, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, List.map_cons] at h ⊢
    rcases h with ⟨h1, h2⟩ | h
    · left
      have hal := ha (b, l) List.mem_cons_self
      simp only [alignedB, Bool.or_eq_true, List.any_eq_true, List.all_eq_true, List.mem_map,
        Bool.and_eq_true, Nat.ble_eq] at hal
      rcases hal with ⟨_, ⟨⟨p, q⟩, hpq, rfl⟩, hp1, hp2⟩ | hal
      · have hW : W = 4096 := rfl
        rw [reloc_in (by omega) (by omega) hs hpq, reloc_in (by omega) (by omega) hs hpq]
        omega
      · have hout : ∀ x, b ≤ x → x < b + l → ∀ w ∈ ws, ¬ (w.1 ≤ x ∧ x < w.1 + W) := fun x hx1 hx2 w hw hc => by
          have := hal w.1 ⟨w, hw, rfl⟩
          rcases this with h | h <;> omega
        rw [reloc_out (hout off h1 (by omega)), reloc_out (hout b (Nat.le_refl _) (by omega))]
        omega
    · exact .inr (inWin_reloc hn hs (fun w hw => ha w (List.mem_cons_of_mem _ hw)) h)

theorem fpIn_reloc {ws : List (Nat × Nat)} (hs : sepB (ws.map Prod.fst) = true) {U : Bnd}
    (ha : ∀ w ∈ U.rd ++ U.wr, alignedB (ws.map Prod.fst) w = true) {i : Instr} (h : fpIn U i = true) :
    fpIn (U.reloc ws) (relocI ws i) = true := by
  have hr : ∀ w ∈ U.rd, alignedB (ws.map Prod.fst) w = true := fun w hw => ha w (List.mem_append_left _ hw)
  have hw : ∀ w ∈ U.wr, alignedB (ws.map Prod.fst) w = true := fun w hw => ha w (List.mem_append_right _ hw)
  cases i with
  | ldr sz t n off =>
    show fpIn (U.reloc ws) (.ldr sz t n (relocOff ws off)) = true
    by_cases hn : n = .x3
    · subst hn
      unfold fpIn at h ⊢
      simp only [fp, ite_true, memIn, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, inWin_reloc (by cases sz <;> decide) hs hr h.2⟩
    · unfold fpIn at h
      simp only [fp, hn, ite_false] at h
      cases h
  | str sz t n off =>
    show fpIn (U.reloc ws) (.str sz t n (relocOff ws off)) = true
    by_cases hn : n = .x3
    · subst hn
      unfold fpIn at h ⊢
      simp only [fp, ite_true, memIn, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, inWin_reloc (by cases sz <;> decide) hs hw h.2⟩
    · unfold fpIn at h
      simp only [fp, hn, ite_false] at h
      cases h
  | ldrq t n off =>
    show fpIn (U.reloc ws) (.ldrq t n (relocOff ws off)) = true
    by_cases hn : n = .x3
    · subst hn
      unfold fpIn at h ⊢
      simp only [fp, ite_true, memIn, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, inWin_reloc (by decide) hs hr h.2⟩
    · unfold fpIn at h
      simp only [fp, hn, ite_false] at h
      cases h
  | strq t n off =>
    show fpIn (U.reloc ws) (.strq t n (relocOff ws off)) = true
    by_cases hn : n = .x3
    · subst hn
      unfold fpIn at h ⊢
      simp only [fp, ite_true, memIn, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, inWin_reloc (by decide) hs hw h.2⟩
    · unfold fpIn at h
      simp only [fp, hn, ite_false] at h
      cases h
  | _ => exact h

/-- Code at any slots, as code at the probe slots with its offsets moved, is within the bound
checked at the probe slots, moved. -/
theorem fpIn_relocs {ws : List (Nat × Nat)} {ps : List Nat} {c c' : List Instr} {U : Bnd}
    (he : c' = c.map (relocI ws)) (hc : c.all (fpIn U) = true) (hps : ws.map Prod.fst = ps)
    (hs : sepB ps = true) (ha : (U.rd ++ U.wr).all (alignedB ps) = true) :
    ∀ x ∈ c', fpIn (U.reloc ws) x = true := by
  subst he hps
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact fpIn_reloc hs (List.all_eq_true.mp ha) (List.all_eq_true.mp hc y hy)

/-! ## Unions -/

theorem subM_union_left {a b c : Nat} (h : subM a b = true) : subM a (b ||| c) = true := by
  simp only [subM, beq_iff_eq] at h ⊢
  apply Nat.eq_of_testBit_eq; intro i
  have := congrArg (Nat.testBit · i) h
  simp only [Nat.testBit_and, Nat.testBit_or] at this ⊢
  cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

theorem subM_union_right {a b c : Nat} (h : subM a c = true) : subM a (b ||| c) = true := by
  simp only [subM, beq_iff_eq] at h ⊢
  apply Nat.eq_of_testBit_eq; intro i
  have := congrArg (Nat.testBit · i) h
  simp only [Nat.testBit_and, Nat.testBit_or] at this ⊢
  cases ha : a.testBit i <;> cases hb : c.testBit i <;> simp_all

theorem inWin_append_left {off n : Nat} {a b : List (Nat × Nat)} (h : inWin off n a = true) :
    inWin off n (a ++ b) = true := by
  induction a with
  | nil => cases h
  | cons w a ih =>
    simp only [inWin, List.cons_append, Bool.or_eq_true] at h ⊢
    exact h.imp id ih

theorem inWin_append_right {off n : Nat} {a b : List (Nat × Nat)} (h : inWin off n b = true) :
    inWin off n (a ++ b) = true := by
  induction a with
  | nil => exact h
  | cons w a ih => simp only [inWin, List.cons_append, Bool.or_eq_true]; exact .inr ih

theorem fpIn_union_left {U V : Bnd} {i : Instr} (h : fpIn U i = true) : fpIn (U.union V) i = true := by
  unfold fpIn at h ⊢
  cases hf : fp i with
  | none => rw [hf] at h; cases h
  | some F =>
    rw [hf] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h ⊢
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
    refine ⟨⟨⟨⟨⟨⟨subM_union_left h1, subM_union_left h2⟩, subM_union_left h3⟩, subM_union_left h4⟩, ?_⟩, ?_⟩, ?_⟩
    · rcases h5 with h5 | h5
      · exact .inl h5
      · exact .inr (by simp [Bnd.union, h5])
    · rcases h6 with h6 | h6
      · exact .inl h6
      · exact .inr (by simp [Bnd.union, h6])
    · cases i <;> simp only [memIn, Bnd.union] at h7 ⊢ <;> first | rfl | exact inWin_append_left h7

theorem fpIn_union_right {U V : Bnd} {i : Instr} (h : fpIn V i = true) : fpIn (U.union V) i = true := by
  unfold fpIn at h ⊢
  cases hf : fp i with
  | none => rw [hf] at h; cases h
  | some F =>
    rw [hf] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h ⊢
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
    refine ⟨⟨⟨⟨⟨⟨subM_union_right h1, subM_union_right h2⟩, subM_union_right h3⟩, subM_union_right h4⟩, ?_⟩, ?_⟩, ?_⟩
    · rcases h5 with h5 | h5
      · exact .inl h5
      · exact .inr (by simp [Bnd.union, h5])
    · rcases h6 with h6 | h6
      · exact .inl h6
      · exact .inr (by simp [Bnd.union, h6])
    · cases i <;> simp only [memIn, Bnd.union] at h7 ⊢ <;> first | rfl | exact inWin_append_right h7

end VG.AArch64.Interleave
