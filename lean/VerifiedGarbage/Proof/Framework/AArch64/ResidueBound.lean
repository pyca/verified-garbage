module

public import VerifiedGarbage.Proof.Framework.AArch64.ResidueCT
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.Semantics

/-!
# How many bits a function's result has (AArch64)

`rtaintB` is `rtaintCT` (`ResidueCT.lean`) that also keeps upper bounds of
registers, as widths (`Bound`): a value that fits in `k` bits in each run
agrees with the other run's above bit `k`, both being zero there. A status
that code computes as `and x0, x3, x1` after `movz x1, #1`, from a mask the
analysis cannot show is public, then differs at most in its low bit, which
is all `Outside` lets the result differ in. The bounds are of each run on
its own: `movz` gives the width of its immediate, `and` the smaller of its
operands', and an instruction that writes a register forgets its bound.

`noResidue_of_verified`: `RTaintCT.noResidue_of_verified`, with the result
public above bit `r` either because the analysis says so or because it fits
in `r` bits (`doneB`).
-/

@[expose] public section

namespace VG.AArch64.RTaintB

open VG.AArch64

/-- Registers and widths: each one's value fits in its width. -/
abbrev W := List (Reg × Nat)

/-- Every register of `w` fits in its width in `s`. -/
def Bound (w : W) (s : State) : Prop := ∀ e ∈ w, (s.gpr e.1).toNat < 2 ^ e.2

/-- The width `w` gives `r` (64, every register's, if none). -/
def wget (w : W) (r : Reg) : Nat := ((w.find? (·.1 == r)).map (·.2)).getD 64

theorem wget_bound {w : W} {s : State} (h : Bound w s) (r : Reg) :
    (s.gpr r).toNat < 2 ^ wget w r := by
  unfold wget
  cases hf : w.find? (·.1 == r) with
  | none => exact (s.gpr r).isLt
  | some e =>
    have he := List.mem_of_find?_eq_some hf
    have hr : e.1 = r := by simpa using List.find?_some hf
    simp only [Option.map_some, Option.getD_some]
    rw [← hr]; exact h e he

/-- A width of a 16-bit immediate. -/
def bitsOf (n : Nat) : Nat := if n < 2 then 1 else if n < 256 then 8 else 16

theorem lt_bitsOf {n : Nat} (h : n < 2 ^ 16) : n < 2 ^ bitsOf n := by
  unfold bitsOf
  split
  · omega
  · split
    · omega
    · exact h

/-- The widths after `i`. -/
def wstep (w : W) (i : Instr) : W :=
  let kept := w.filter (fun e => !clobbers i e.1)
  match i with
  | .movz .x d imm 0 => (d, bitsOf imm.toNat) :: kept
  | .logic .and .x d n m => (d, min (wget w n) (wget w m)) :: kept
  | _ => kept

theorem bound_kept {w : W} {i : Instr} {s s' : State} (h : Bound w s) (e : exec i s = some s') :
    Bound (w.filter (fun e => !clobbers i e.1)) s' := by
  intro x hx
  rw [List.mem_filter, Bool.not_eq_true'] at hx
  rw [exec_gpr hx.2 e]
  exact h x hx.1

theorem bound_step {w : W} {i : Instr} {s s' : State} (h : Bound w s) (e : exec i s = some s') :
    Bound (wstep w i) s' := by
  have hk := bound_kept h e
  unfold wstep
  split
  · rename_i d imm
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simp only [reduceExec, show 16 * 0 < Size.bits .x by decide, ↓reduceIte,
        Option.some.injEq] at e
      subst e
      simp only [RegUpd.gpr_write_self, Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.toNat_setWidth]
      exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.mod_le _ _) (Nat.mod_le _ _)) (lt_bitsOf imm.isLt)
    · exact hk x hx
  · rename_i d n m
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simp only [reduceExec, Option.some.injEq] at e
      subst e
      simp only [RegUpd.gpr_write_self, Size.bits, BitVec.setWidth_eq, State.read,
        BitVec.toNat_and]
      by_cases hle : wget w n ≤ wget w m
      · rw [Nat.min_eq_left hle]
        exact Nat.lt_of_le_of_lt Nat.and_le_left (wget_bound h n)
      · rw [Nat.min_eq_right (by omega)]
        exact Nat.lt_of_le_of_lt Nat.and_le_right (wget_bound h m)
    · exact hk x hx
  · exact hk

/-- The widths of both `w` and `v`, the larger of the two. -/
def wmeet (w v : W) : W :=
  w.filterMap fun e => (v.find? (·.1 == e.1)).map fun f => (e.1, max e.2 f.2)

theorem bound_meet_left {w v : W} {s : State} (h : Bound w s) : Bound (wmeet w v) s := by
  intro x hx
  obtain ⟨e, he, hm⟩ := List.mem_filterMap.mp hx
  obtain ⟨f, -, rfl⟩ := Option.map_eq_some_iff.mp hm
  exact Nat.lt_of_lt_of_le (h e he) (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))

theorem bound_meet_right {w v : W} {s : State} (h : Bound v s) : Bound (wmeet w v) s := by
  intro x hx
  obtain ⟨e, -, hm⟩ := List.mem_filterMap.mp hx
  obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hm
  have hr : f.1 = e.1 := by simpa using List.find?_some hf
  have := h f (List.mem_of_find?_eq_some hf)
  rw [hr] at this
  exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))

/-- Every bound of `w` follows from `v`'s. -/
def wle (w v : W) : Bool := w.all fun e => Nat.ble (wget v e.1) e.2

theorem bound_le {w v : W} {s : State} (hl : wle w v = true) (h : Bound v s) : Bound w s := by
  intro x hx
  have := Nat.le_of_ble_eq_true (List.all_eq_true.mp hl x hx)
  exact Nat.lt_of_lt_of_le (wget_bound h x.1) (Nat.pow_le_pow_right (by decide) this)

abbrev T := RTaintL.T × W

def Agree (τ : T) (s₁ s₂ : State) : Prop :=
  RTaintL.Agree τ.1 s₁ s₂ ∧ Bound τ.2 s₁ ∧ Bound τ.2 s₂

def step (τ : T) (i : Instr) : Option T := (RTaintCT.step τ.1 i).map (·, wstep τ.2 i)

theorem step_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : step τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂')
    (hadr : addrs i s₁ = addrs i s₂) : Agree τ' s₁' s₂' := by
  obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.mp hs
  exact ⟨RTaintCT.step_sound ha.1 hσ e₁ e₂ hadr, bound_step ha.2.1 e₁, bound_step ha.2.2 e₂⟩

/-! ## The step with its cases closed

As `RTaintCT.stepK`: `stepK` is `step` (`stepK_eq`) as one `casesOn` of the
instruction whose minor premises are closed (`inline_match%`), made from
`stepC`, which is `step` with `RTaintCT.clobbersI` for `clobbers`. -/

/-- `wstep`, with `RTaintCT.clobbersI`. -/
def wstepC (w : W) (i : Instr) : W :=
  let kept := w.filter (fun e => !RTaintCT.clobbersI e.1 i)
  match i with
  | .movz .x d imm 0 => (d, bitsOf imm.toNat) :: kept
  | .logic .and .x d n m => (d, min (wget w n) (wget w m)) :: kept
  | _ => kept

theorem wstepC_eq (w : W) (i : Instr) : wstepC w i = wstep w i := by
  have h : (fun e : Reg × Nat => !RTaintCT.clobbersI e.1 i) = fun e => !clobbers i e.1 :=
    funext fun e => by rw [RTaintCT.clobbersI_eq]
  unfold wstepC wstep
  rw [h]

/-- `step`, with `RTaintCT.stepC` and `wstepC`. -/
def stepC (τ : T) (i : Instr) : Option T := (RTaintCT.stepC τ.1 i).map (·, wstepC τ.2 i)

theorem stepC_eq (τ : T) (i : Instr) : stepC τ i = step τ i := by
  simp only [stepC, step, RTaintCT.stepC_eq, wstepC_eq]

/-- `stepC`, as a function of the instruction first. -/
def stepFn (i : Instr) : T → Option T := fun τ => stepC τ i

/-- `stepFn`, with its cases closed (`inline_match%`). -/
def stepFnK : Instr → T → Option T :=
  inline_match% stepFn stepC wstepC RTaintCT.stepC RTaintCT.stepLC RTaintCT.stepRC RTaintCT.hstepC
    RTaintCT.clobbersI dstOf RTaintCT.pubBase RTaintCT.base RTaintL.lstep RTaintL.insD2 RTaint.vstep
    RTaint.vopStep RTaint.fstep RTaint.setsFlags vdstOf VectorTaint.step Taint.step Taint.stepFn

theorem stepFnK_eq (i : Instr) : stepFnK i = stepFn i := by cases i <;> rfl

/-- `step`, with its cases closed. -/
def stepK (τ : T) (i : Instr) : Option T := stepFnK i τ

theorem stepK_eq (τ : T) (i : Instr) : stepK τ i = step τ i := by
  rw [stepK, stepFnK_eq]
  exact stepC_eq τ i

end RTaintB

/-- `rtaintCT` with the widths of registers (see `RTaintB`). -/
def rtaintB : VG.TaintCT isa where
  T := RTaintB.T
  Agree := RTaintB.Agree
  step := RTaintB.stepK
  step_sound ha hs e₁ e₂ hadr := RTaintB.step_sound ha ((RTaintB.stepK_eq _ _).symm.trans hs) e₁ e₂ hadr
  addrs_length := RTaintCT.addrs_length
  meet τ σ := (rtaintCT.meet τ.1 σ.1, RTaintB.wmeet τ.2 σ.2)
  meet_left h := ⟨rtaintCT.meet_left h.1, RTaintB.bound_meet_left h.2.1,
    RTaintB.bound_meet_left h.2.2⟩
  meet_right h := ⟨rtaintCT.meet_right h.1, RTaintB.bound_meet_right h.2.1,
    RTaintB.bound_meet_right h.2.2⟩
  le τ σ := rtaintCT.le τ.1 σ.1 && RTaintB.wle τ.2 σ.2
  le_sound hl h := by
    simp only [Bool.and_eq_true] at hl
    exact ⟨rtaintCT.le_sound hl.1 h.1, RTaintB.bound_le hl.2 h.2.1, RTaintB.bound_le hl.2 h.2.2⟩
  call _ := none
  call_sound _ hs := nomatch hs
  callAddrs_length _ _ := rfl
  ret _ := none
  ret_sound _ hs := nomatch hs
  retAddrs_length _ _ := rfl
  push _ _ := none
  push_sound _ hs := nomatch hs
  pop _ _ := none
  pop_sound _ hs := nomatch hs

namespace RTaintB

def init : T := (RTaintL.init, [])

/-- `RTaintCT.donePres r`, with the result public above bit `r` because the
analysis says so or because it fits in `r` bits. -/
def doneB (r : Nat) (τ : T) : Bool :=
  RTaintCT.donePres 64 τ.1 && (Nat.ble τ.1.1.2.2 r || Nat.ble (wget τ.2 .x0) r)

theorem shr_eq_zero {x : BitVec 64} {k r : Nat} (h : x.toNat < 2 ^ k) (hk : k ≤ r) : x >>> r = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hk))]
  rfl

/-- Code verified against its contract, whose analysis (`rtaintB`) from
everything public ends in `doneB r`, returns without secret residue, with
an `r`-bit result. -/
theorem noResidue_of_verified {c : Prog isa} {k : Contract isa} {r : Nat}
    (hv : Verified target c k)
    (h : ∃ hc, (rtaintB.check init c hc).any (doneB r) = true) :
    NoResidue c k r := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp ho hu e₁ e₂
  obtain ⟨hc, h⟩ := h
  cases hτ : rtaintB.check init c hc with
  | none => rw [hτ] at h; cases h
  | some τ' =>
    rw [hτ] at h
    have h' : doneB r τ' = true := h
    simp only [doneB, Bool.and_eq_true, Bool.or_eq_true] at h'
    obtain ⟨hd, hx⟩ := h'
    obtain ⟨_, u₁, f₁, hp₁, -⟩ := hv.1 s₁ h₁
    obtain ⟨_, u₂, f₂, hp₂, -⟩ := hv.1 s₂ h₂
    obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
    obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
    have ha := TaintCT.agree_of_check hv.2.1 hτ h₁ h₂ hp
      (show Agree init s₁ s₂ from
        ⟨RTaintL.agree_init ho hu, (fun _ h => nomatch h), (fun _ h => nomatch h)⟩) e₁ e₂
    have o := RTaintCT.outside_of_donePres ha.1 hd ho hp₁ hp₂
    have hx0 : s₁'.gpr .x0 >>> r = s₂'.gpr .x0 >>> r := by
      rcases hx with hx | hx
      · exact RTaint.shr_mono ha.1.1.2.2.1 (Nat.le_of_ble_eq_true hx)
      · rw [shr_eq_zero (wget_bound ha.2.1 .x0) (Nat.le_of_ble_eq_true hx),
          shr_eq_zero (wget_bound ha.2.2 .x0) (Nat.le_of_ble_eq_true hx)]
    exact ⟨o.1, o.2.1, o.2.2.1, hx0, o.2.2.2.2⟩

end RTaintB

end VG.AArch64
