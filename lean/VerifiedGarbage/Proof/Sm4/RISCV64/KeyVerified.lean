module

public import VerifiedGarbage.Proof.Sm4.RISCV64.KeyEk
public import VerifiedGarbage.Proof.Sm4.Scratch
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Sm4.RISCV64.Lit
import VerifiedGarbage.Proof.Sm4.RISCV64.Prologue
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm4.RISCV64.KeyEk
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Impl.StackScratch.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Sm4.RISCV64.Lit
meta import VerifiedGarbage.Proof.Sm4.RISCV64.Prologue
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# SM4 key expansion on RISCV64 meets its contracts

`expandKey_verified`: `expandKey` is correct (`expandKey_wp`) and constant
time, by the taint analysis with the pointers and the stack pointer public.
`expandKey_framed` runs it with its working space on the stack, zeroed on
return, as `ecb_framed` does. As on PPC64LE
(`Proof/Sm4/PPC64LE/KeyVerified.lean`).
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4.RISCV64
open VG.Proof.Sm4 (expandKeyRISCV64)

theorem expandKeyTaint_agree (s₁ s₂ : State) (_ : expandKeyRISCV64.pre s₁) (_ : expandKeyRISCV64.pre s₂)
    (hp : expandKeyRISCV64.pub s₁ s₂) : taint.Agree (Taint.ofRegs [.a0, .a1, .a2]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [h1, h2, h3]

theorem expandKey_ct : ConstantTime isa expandKeyRISCV64.pre expandKeyRISCV64.pub expandKey :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) expandKeyTaint_agree (by taint_decide)

theorem expandKey_correct (s : State) (hs : expandKeyRISCV64.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandKeyRISCV64.post s s' := by
  obtain ⟨t, s', he, h₁, hra, h₂⟩ := expandKey_wp hs
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, hra⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact h₁ 10 (by omega)
  · exact h₁ 11 (by omega)

/-- A state satisfying the precondition. -/
def expandKeySat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 8 * 397⟩]

theorem expandKey_verified :
    Verified target expandKey (Proof.Sm4.expandKeyScratchContract abi slots) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Proof.Sm4.expandKeyScratchContract, Proof.Sm4.expandKeyScratchSig, Proof.Sm4.expandKeyPost,
      expandKeyRISCV64, abi, argRegs, slots, savedSlot, tableEnd, tableSlot]
      [expandKeySat] using expandKeySat)

/-- A state satisfying the key schedule's precondition: the key at
`0x1000`, the schedule at `0x2000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Sm4.expandKeyContract abi 3184).pre s := by
  implies_sat [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, abi, argRegs]
    [expandKeyFrameSat] using expandKeyFrameSat

/-- Key expansion, with its working space on the stack. -/
theorem expandKey_framed :
    Verified target (Impl.StackScratch.RISCV64.withStackScratchWiped 3184 .a2 397 expandKey)
      (Spec.Sm4.expandKeyContract abi 3184) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.Sm4.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 397) (post := Proof.Sm4.expandKeyPost abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 3184) (words := 397) expandKey_verified (by decide) (by decide) (by decide)
    (Proof.Sm4.expandKeyPostOut_local _) expandKeyFrameSat_pre

end VG.Proof.Sm4.RISCV64
