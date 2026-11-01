module

public import VerifiedGarbage.Proof.Sm4.AArch64.Ecb
public import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Sm4.AArch64.CryptSum
import VerifiedGarbage.Proof.Sm4.AArch64.Lit
import VerifiedGarbage.Proof.Sm4.AArch64.LayersLit
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm4.AArch64.Ecb
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Sm4.AArch64.CryptSum
meta import VerifiedGarbage.Proof.Sm4.AArch64.Lit
meta import VerifiedGarbage.Proof.Sm4.AArch64.LayersLit
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Proof.Sm4.Contract

/-!
# SM4 ECB on AArch64 meets its contracts

`ecb_verified`: `ecb dir` is correct (`ecb_wp`) and constant time, by the
taint analysis: the pointers, `n` and the stack pointer are public, and so
is everything the code computes from them, which it keeps in registers
(`x0`–`x5`, the copies' pointers and counts and the loop tests).
`ecb_framed` runs it with its working space on the stack, zeroed on
return: 3168 bytes, the 396 words of the scratch buffer.
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64

open VG VG.AArch64 VG.Impl.Sm4.AArch64
open VG.Proof.Sm4 (specDirA ecbAArch64)

theorem ecbTaint_agree (dir : Dir) (s₁ s₂ : State) (_ : (ecbAArch64 dir).pre s₁) (_ : (ecbAArch64 dir).pre s₂)
    (hp : (ecbAArch64 dir).pub s₁ s₂) : VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem ecb_ct (dir : Dir) : ConstantTime isa (ecbAArch64 dir).pre (ecbAArch64 dir).pub (ecb dir) := by
  cases dir
  · exact VG.Taint.constantTime_of_exists (A := VectorTaint.taint)
        (VectorTaint.ofRegs [.x0, .x1, .x2, .x3]) (fun s₁ s₂ h₁ h₂ hp =>
      ⟨ecbTaint_agree .encrypt s₁ s₂ h₁ h₂ hp, fun v hv => by simp [VectorTaint.ofRegs, RegSet.mem_ofList] at hv⟩)
      (by taint_decide_sum [cryptSum])
  · exact VG.Taint.constantTime_of_exists (A := VectorTaint.taint)
        (VectorTaint.ofRegs [.x0, .x1, .x2, .x3]) (fun s₁ s₂ h₁ h₂ hp =>
      ⟨ecbTaint_agree .decrypt s₁ s₂ h₁ h₂ hp, fun v hv => by simp [VectorTaint.ofRegs, RegSet.mem_ofList] at hv⟩)
      (by taint_decide_sum [cryptSum])

theorem ecb_correct (dir : Dir) (s : State) (hs : (ecbAArch64 dir).pre s) :
    ∃ t s', Exec isa (ecb dir) s t s' ∧ abiPreserved s s' ∧ (ecbAArch64 dir).post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (ecb_wp dir hs)
    (by cases dir <;> lit_decide) (by cases dir <;> lit_decide)
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he (by cases dir <;> lit_decide)⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega)
  · exact h₁ 1 (by omega)
  · exact h₁ 2 (by omega)
  · exact h₁ 3 (by omega)
  · exact h₁ 4 (by omega)
  · exact h₁ 5 (by omega)
  · exact h₁ 6 (by omega)
  · exact h₁ 7 (by omega)
  · exact h₁ 8 (by omega)
  · exact h₁ 9 (by omega)
  · exact h₃ _ (by simp)

/-- A state satisfying the precondition (one block). -/
def ecbSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 1 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 8 * 396⟩]

theorem ecb_verified (dir : Dir) :
    Verified AArch64.target (ecb dir) (Proof.Sm4.ecbScratchContract AArch64.abi (specDirA dir) slots) :=
  Verified.of_correct (ecb_correct dir) (ecb_ct dir) (by
    cases dir <;>
    sig_implies [Proof.Sm4.ecbScratchContract, Proof.Sm4.ecbScratchSig, Spec.Sm4.ecbPost, ecbAArch64, specDirA,
      AArch64.abi, AArch64.argRegs, slots, savedSlot, tableEnd, tableSlot] [ecbSat] using ecbSat)

/-- A state satisfying the ECB functions' precondition: the schedule at
`0x1000`, one block at `0x3000`. -/
def ecbFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩]

theorem ecbFrameSat_pre (d : Spec.Sm4.Direction) :
    ∃ s, (Spec.Sm4.ecbContract AArch64.abi d 3168).pre s := by
  implies_sat [Spec.Sm4.ecbContract, Spec.Sm4.ecbSig, Spec.Sm4.ecbPost, AArch64.abi, AArch64.argRegs]
    [ecbFrameSat] using ecbFrameSat

/-- ECB in the direction `dir`, with its working space on the stack. -/
theorem ecb_framed (dir : Dir) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 3168 .x3 396 (ecb dir))
      (Spec.Sm4.ecbContract AArch64.abi (specDirA dir) 3168) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Sm4.ecbSig) (nm := "scratch") (e := .u64)
    (n := 396) (post := Spec.Sm4.ecbPost (specDirA dir) AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3168) (ecb_verified dir)
    (by decide) (by decide) (by decide) (Proof.Sm4.ecbPostOut_local _ _) (ecbFrameSat_pre _)

/-! ## Either direction -/

theorem ecbAnyTaint_agree (s₁ s₂ : State) (_ : ecbAnyAArch64.pre s₁) (_ : ecbAnyAArch64.pre s₂)
    (hp : ecbAnyAArch64.pub s₁ s₂) :
    VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem ecbAny_ct : ConstantTime isa ecbAnyAArch64.pre ecbAnyAArch64.pub ecbAny :=
  VG.Taint.constantTime_of_exists (A := VectorTaint.taint)
    (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4]) (fun s₁ s₂ h₁ h₂ hp =>
    ⟨ecbAnyTaint_agree s₁ s₂ h₁ h₂ hp, fun v hv => by simp [VectorTaint.ofRegs, RegSet.mem_ofList] at hv⟩)
    (by taint_decide_sum [cryptSum])

theorem ecbAny_correct (s : State) (hs : ecbAnyAArch64.pre s) :
    ∃ t s', Exec isa ecbAny s t s' ∧ abiPreserved s s' ∧ ecbAnyAArch64.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (ecbAny_wp hs) (by lit_decide) (by lit_decide)
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega)
  · exact h₁ 1 (by omega)
  · exact h₁ 2 (by omega)
  · exact h₁ 3 (by omega)
  · exact h₁ 4 (by omega)
  · exact h₁ 5 (by omega)
  · exact h₁ 6 (by omega)
  · exact h₁ 7 (by omega)
  · exact h₁ 8 (by omega)
  · exact h₁ 9 (by omega)
  · exact h₃ _ (by simp)

/-- A state satisfying `vg_sm4_ecb`'s precondition with its working space as
an argument (one block, encryption). -/
def ecbAnySat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 1 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 8 * 396⟩]

theorem ecbAny_verified :
    Verified AArch64.target ecbAny (Proof.Sm4.ecbDirScratchContract AArch64.abi slots) :=
  Verified.of_correct ecbAny_correct ecbAny_ct (by
    sig_implies [Proof.Sm4.ecbDirScratchContract, Proof.Sm4.ecbDirScratchSig, Proof.Sm4.ecbDirPre,
      Proof.Sm4.ecbDirPost, ecbAnyAArch64, AArch64.abi, AArch64.argRegs, slots, savedSlot, tableEnd,
      tableSlot] [ecbAnySat] using ecbAnySat)

/-- A state satisfying `vg_sm4_ecb`'s precondition: the schedule at
`0x1000`, one block at `0x3000`, encryption. -/
def ecbDirFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩]

theorem ecbDirFrameSat_pre : ∃ s, (Proof.Sm4.ecbDirContract AArch64.abi 3168).pre s := by
  implies_sat [Proof.Sm4.ecbDirContract, Proof.Sm4.ecbDirSig, Spec.Sm4.ecbSig, AArch64.abi, AArch64.argRegs]
    [ecbDirFrameSat] using ecbDirFrameSat

/-- `vg_sm4_ecb`: ECB in the direction `decrypt` selects, with its working
space on the stack. -/
theorem ecbAny_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 3168 .x4 396 ecbAny)
      (Proof.Sm4.ecbDirContract AArch64.abi 3168) :=
  AArch64.Verified.stackScratchWiped (sig := Proof.Sm4.ecbDirSig) (nm := "scratch") (e := .u64)
    (n := 396) (pre := Proof.Sm4.ecbDirPre AArch64.abi.ptrBits) (post := Proof.Sm4.ecbDirPost AArch64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 3168) ecbAny_verified
    (by decide) (by decide) (by decide) (Proof.Sm4.ecbDirPostOut_local _) ecbDirFrameSat_pre

end VG.Proof.Sm4.AArch64
