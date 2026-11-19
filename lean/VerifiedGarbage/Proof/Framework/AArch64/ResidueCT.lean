module

public import VerifiedGarbage.Proof.Framework.AArch64.ResidueTaint
public import VerifiedGarbage.Proof.Framework.TaintCT
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Semantics

/-!
# What constant-time code leaves in its registers (AArch64)

`rtaintCT` is `rtaintL` (`ResidueTaint.lean`) for two runs that leak the
same (`TaintCT`): a load or a store accesses the same address in both, so
its base register, whose sum with the offset that address is, holds the
same value in both, and is public from then on (`pubBase`). The step of
`rtaintL` itself needs that register public, and fails otherwise: the
address of a table of constants (`adrSym`), which the two runs need not
share (`State.syms`), or a pointer loaded from memory the analysis does not
follow, is then public after its first use. Branches need not be on public
conditions either.

`noResidue_of_check`: code proven constant time under its contract, whose
analysis from everything public ends in `RTaintL.done r`, returns without
secret residue with an `r`-bit result. The two runs `NoResidue` compares
satisfy the precondition and agree on what the contract's `pub` says, so
their traces are equal (`TaintCT.agree_of_check`).

`noResidue_of_verified`: code verified against its contract needs no more
than that of the registers the calling convention preserves (`x19`–`x28`,
`x30`, and the low halves of `v8`–`v15`), which it leaves as they were on
entry, where the two runs agree (`donePres`): the analysis need not follow
a value saved and restored through memory it does not know.
-/

@[expose] public section

namespace VG.AArch64.RTaintCT

open VG.AArch64

/-- The base register and offset of the first address of a load or a store
through a general-purpose register. -/
def base : Instr → Option (Reg × Nat)
  | .ldr _ _ n off | .str _ _ n off | .ldrb _ n off | .strb _ n off | .ldp _ _ n off
  | .stp _ _ n off | .ldrq _ n off | .strq _ n off => some (n, off)
  | _ => none

theorem addrs_of_base {i : Instr} {n : Reg} {off : Nat} (h : base i = some (n, off)) (s : State) :
    (addrs i s).head? = some (s.gpr n + BitVec.ofNat 64 off) := by
  cases i <;> simp only [base, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h <;>
    (obtain ⟨rfl, rfl⟩ := h; rfl)

/-- `τ`, with `n` public. -/
def withPub (τ : RTaintL.T) (n : Reg) : RTaintL.T :=
  (((τ.1.1.1.insert n, τ.1.1.2), τ.1.2), τ.2)

theorem agree_withPub {τ : RTaintL.T} {n : Reg} {s₁ s₂ : State} (h : RTaintL.Agree τ s₁ s₂)
    (hn : s₁.gpr n = s₂.gpr n) : RTaintL.Agree (withPub τ n) s₁ s₂ := by
  obtain ⟨⟨⟨⟨hsp, hg⟩, hv⟩, hr⟩, hq⟩ := h
  refine ⟨⟨⟨⟨hsp, fun r hr' => ?_⟩, hv⟩, hr⟩, hq⟩
  rcases RegSet.mem_insert.mp hr' with rfl | hr'
  · exact hn
  · exact hg r hr'

/-- `τ`, with the base register of `i` public. -/
def pubBase (τ : RTaintL.T) (i : Instr) : RTaintL.T :=
  match base i with
  | some (n, _) => withPub τ n
  | none => τ

theorem agree_pubBase {τ : RTaintL.T} {i : Instr} {s₁ s₂ : State} (h : RTaintL.Agree τ s₁ s₂)
    (ha : addrs i s₁ = addrs i s₂) : RTaintL.Agree (pubBase τ i) s₁ s₂ := by
  unfold pubBase
  split
  · rename_i n off hb
    have e := addrs_of_base hb s₁
    rw [ha, addrs_of_base hb s₂, Option.some.injEq] at e
    have e' := congrArg (· - BitVec.ofNat 64 off) e.symm
    simp only [BitVec.add_sub_cancel] at e'
    exact agree_withPub h e'
  · exact h

def step (τ : RTaintL.T) (i : Instr) : Option RTaintL.T := RTaintL.step (pubBase τ i) i

theorem step_sound {τ τ' : RTaintL.T} {i : Instr} {s₁ s₂ s₁' s₂' : State}
    (ha : RTaintL.Agree τ s₁ s₂) (hs : step τ i = some τ') (e₁ : exec i s₁ = some s₁')
    (e₂ : exec i s₂ = some s₂') (hadr : addrs i s₁ = addrs i s₂) : RTaintL.Agree τ' s₁' s₂' :=
  (RTaintL.step_sound (agree_pubBase ha hadr) hs e₁ e₂).2

theorem addrs_length (i : Instr) (s₁ s₂ : State) : (addrs i s₁).length = (addrs i s₂).length := by
  cases i <;> rfl

/-! ## The step with its cases closed

`step` is `RTaintL.step`, `RTaint.step`, `RTaint.vstep` and `VectorTaint.step`
one in the other, with `pubBase`, `RTaintL.lstep`, `RTaint.fstep` and
`RTaint.hstep`: nine matches on the instruction, each of which the kernel
unfolds, building a term of every case of the match to keep one (see "The
match on the instruction, with its cases closed" in
`Proof/Framework/Taint.lean`). `stepK` is `step` (`stepK_eq`) as one `casesOn`
of the instruction whose minor premises are closed (`inline_match%`), which
`rtaintCT` takes for its step; the soundness proofs stay about `step`. It is
made from `stepC`, which is `step` with `clobbersI` for `clobbers`: a function
of the instruction last, which `inline_match%` then resolves too, where
`clobbers i r` is left to the kernel, a match on the instruction at each
instruction. -/

/-- `clobbers i r`, as a function of the instruction last. -/
def clobbersI (r : Reg) : Instr → Bool
  | .ldp t1 t2 _ _ => r == t1 || r == t2
  | i => dstOf i == some r

theorem clobbersI_eq (r : Reg) (i : Instr) : clobbersI r i = clobbers i r := by
  cases i <;> rfl

/-- `RTaint.hstep`, with `clobbersI`. -/
def hstepC (g' : Taint.T) (h : Nat) (i : Instr) : Nat :=
  if Taint.pub g' .x0 then 0
  else if !clobbersI .x0 i then h
  else match i with
    | .lsr .x .x0 _ sh => 64 - sh
    | .movz .w .x0 _ _ | .lsr .w .x0 _ _ | .logic _ .w .x0 _ _ | .add .w .x0 _ _
    | .sub .w .x0 _ _ | .addImm .w .x0 _ _ | .subImm .w .x0 _ _ => 32
    | _ => 64

theorem hstepC_eq (g' : Taint.T) (h : Nat) (i : Instr) : hstepC g' h i = RTaint.hstep g' h i := by
  unfold hstepC RTaint.hstep
  rw [clobbersI_eq]
  rfl

/-- `RTaint.step`, with `hstepC`. -/
def stepRC (τ : RTaint.T) (i : Instr) : Option RTaint.T :=
  (RTaint.vstep τ.1 i).map fun v => (v, RTaint.fstep τ.1.1 τ.2.1 i, hstepC v.1 τ.2.2 i)

theorem stepRC_eq (τ : RTaint.T) (i : Instr) : stepRC τ i = RTaint.step τ i := by
  simp only [stepRC, RTaint.step, hstepC_eq]

/-- `RTaintL.step`, with `stepRC`. -/
def stepLC (τ : RTaintL.T) (i : Instr) : Option RTaintL.T :=
  (stepRC τ.1 i).map fun τ' => (τ', RTaintL.lstep τ.1 τ.2 i)

theorem stepLC_eq (τ : RTaintL.T) (i : Instr) : stepLC τ i = RTaintL.step τ i := by
  simp only [stepLC, RTaintL.step, stepRC_eq]

/-- `step`, with `stepLC`. -/
def stepC (τ : RTaintL.T) (i : Instr) : Option RTaintL.T := stepLC (pubBase τ i) i

theorem stepC_eq (τ : RTaintL.T) (i : Instr) : stepC τ i = step τ i := stepLC_eq _ i

/-- `stepC`, as a function of the instruction first. -/
def stepFn (i : Instr) : RTaintL.T → Option RTaintL.T := fun τ => stepC τ i

/-- `stepFn`, with its cases closed (`inline_match%`). -/
def stepFnK : Instr → RTaintL.T → Option RTaintL.T :=
  inline_match% stepFn stepC stepLC stepRC hstepC clobbersI dstOf pubBase base RTaintL.lstep
    RTaintL.insD2 RTaint.vstep RTaint.vopStep RTaint.fstep RTaint.setsFlags vdstOf VectorTaint.step
    Taint.step Taint.stepFn

theorem stepFnK_eq (i : Instr) : stepFnK i = stepFn i := by cases i <;> rfl

/-- `step`, with its cases closed. -/
def stepK (τ : RTaintL.T) (i : Instr) : Option RTaintL.T := stepFnK i τ

theorem stepK_eq (τ : RTaintL.T) (i : Instr) : stepK τ i = step τ i := by
  rw [stepK, stepFnK_eq]
  exact stepC_eq τ i

end RTaintCT

open RTaintCT in
/-- `rtaintL` for two runs that leak the same (see `RTaintCT`). -/
def rtaintCT : VG.TaintCT isa where
  T := RTaintL.T
  Agree := RTaintL.Agree
  step := RTaintCT.stepK
  step_sound ha hs e₁ e₂ hadr := RTaintCT.step_sound ha ((RTaintCT.stepK_eq _ _).symm.trans hs) e₁ e₂ hadr
  addrs_length := RTaintCT.addrs_length
  meet := rtaintL.meet
  meet_left := rtaintL.meet_left
  meet_right := rtaintL.meet_right
  le := rtaintL.le
  le_sound := rtaintL.le_sound
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

namespace RTaintCT

/-- Code proven constant time under its contract, whose analysis
(`rtaintCT`) from everything public ends in `RTaintL.done r`, returns without
secret residue, with an `r`-bit result. -/
theorem noResidue_of_check {c : Prog isa} {k : Contract isa} {r : Nat}
    (hct : ConstantTime isa k.pre k.pub c)
    (h : ∃ hc, (rtaintCT.check RTaintL.init c hc).any (RTaintL.done r) = true) :
    NoResidue c k r := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp ho hu e₁ e₂
  obtain ⟨hc, h⟩ := h
  cases hτ : rtaintCT.check RTaintL.init c hc with
  | none => rw [hτ] at h; cases h
  | some τ' =>
    rw [hτ] at h
    exact RTaintL.outside_of_done
      (TaintCT.agree_of_check hct hτ h₁ h₂ hp (RTaintL.agree_init ho hu) e₁ e₂) h

/-- The registers the calling convention does not preserve, but `x0`. -/
def scratchRegs : List Reg :=
  [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

theorem mem_scratch_or {q : Reg} (hq : q ≠ .x0) : q ∈ scratchRegs ∨ q ∈ preserved := by
  cases q <;> simp_all [scratchRegs, preserved]

/-- `RTaintL.done r`, but for what the calling convention preserves: a
vector register that it preserves the low half of needs only its high half
public. -/
def donePres (r : Nat) (τ : RTaintL.T) : Bool :=
  scratchRegs.all (fun q => τ.1.1.1.mem q) &&
    RTaintL.vregs.all (fun v => if preservedV.contains v then τ.1.1.2.mem v || τ.2.2.mem v
      else RTaintL.vpub τ v) &&
    τ.1.2.1 && Nat.ble τ.1.2.2 r

theorem outside_of_donePres {τ : RTaintL.T} {r : Nat} {s₁ s₂ s₁' s₂' : State}
    (h : RTaintL.Agree τ s₁' s₂') (hd : donePres r τ = true) (ho : Outside 0 s₁ s₂)
    (hp₁ : abiPreserved s₁ s₁') (hp₂ : abiPreserved s₂ s₂') : Outside r s₁' s₂' := by
  simp only [donePres, Bool.and_eq_true, List.all_eq_true] at hd
  obtain ⟨⟨⟨hg, hv⟩, hf⟩, hr⟩ := hd
  obtain ⟨⟨⟨⟨hsp, hgr⟩, hvr⟩, hfl, hx0, hrd, hwr, hdit, -, hm⟩, hq⟩ := h
  obtain ⟨hc, hn, hz, hvf⟩ := hfl hf
  refine ⟨hrd, hwr, fun q hq' => ?_, RTaint.shr_mono hx0 (Nat.le_of_ble_eq_true hr), hsp, hc, hn,
    hz, hvf, hdit, funext fun v => ?_, hm⟩
  · rcases mem_scratch_or hq' with hs | hs
    · exact hgr q (Taint.pub_iff.mp (hg q hs))
    · rw [hp₁.1 q hs, hp₂.1 q hs]; exact ho.2.2.1 q hq'
  · have hp := hv v (RTaintL.mem_vregs v)
    by_cases hpv : v ∈ preservedV
    · simp only [List.contains_iff_mem.mpr hpv, ite_true, Bool.or_eq_true] at hp
      rcases hp with hp | hp
      · exact hvr v hp
      · refine RTaintL.eq_of_halves ?_ (hq true v hp)
        rw [hp₁.2.2 v hpv, hp₂.2.2 v hpv, ho.2.2.2.2.2.2.2.2.2.2.1]
    · have : preservedV.contains v = false := by simpa using hpv
      simp only [this, Bool.false_eq_true, ite_false, RTaintL.vpub, Bool.or_eq_true,
        Bool.and_eq_true] at hp
      rcases hp with hp | ⟨h₀, h₁⟩
      · exact hvr v hp
      · exact RTaintL.eq_of_halves (hq false v h₀) (hq true v h₁)

/-- Code verified against its contract, whose analysis (`rtaintCT`) from
everything public ends in `donePres r`, returns without secret residue,
with an `r`-bit result. -/
theorem noResidue_of_verified {c : Prog isa} {k : Contract isa} {r : Nat}
    (hv : Verified target c k)
    (h : ∃ hc, (rtaintCT.check RTaintL.init c hc).any (donePres r) = true) :
    NoResidue c k r := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp ho hu e₁ e₂
  obtain ⟨hc, h⟩ := h
  cases hτ : rtaintCT.check RTaintL.init c hc with
  | none => rw [hτ] at h; cases h
  | some τ' =>
    rw [hτ] at h
    obtain ⟨_, u₁, f₁, hp₁, -⟩ := hv.1 s₁ h₁
    obtain ⟨_, u₂, f₂, hp₂, -⟩ := hv.1 s₂ h₂
    obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
    obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
    exact outside_of_donePres
      (TaintCT.agree_of_check hv.2.1 hτ h₁ h₂ hp (RTaintL.agree_init ho hu) e₁ e₂) h ho hp₁ hp₂

end RTaintCT

end VG.AArch64
