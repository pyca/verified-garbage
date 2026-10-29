module

public import VerifiedGarbage.Proof.Sm4.RISCV64.Ecb
public import VerifiedGarbage.Proof.Sm4.Scratch
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Sm4.RISCV64.Lit
import VerifiedGarbage.Proof.Sm4.RISCV64.Prologue
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm4.RISCV64.Ecb
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Impl.StackScratch.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Sm4.RISCV64.Lit
meta import VerifiedGarbage.Proof.Sm4.RISCV64.Prologue
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# SM4 ECB on RISCV64 meets its contracts

`ecb_verified`: `ecb dir` is correct (`ecb_wp`) and constant time, by the
taint analysis: the pointers, `n` and the stack pointer are public, and so
is everything the code computes from them, which it keeps in registers
(`a0`–`a4`, the copies' pointers and counts and the loop tests).
`ecb_framed` runs it with its working space on the stack, zeroed on return:
3184 bytes, for the 397 words of the scratch buffer. As on PPC64LE
(`Proof/Sm4/PPC64LE/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4.RISCV64
open VG.Proof.Sm4 (specDirA ecbRISCV64)

theorem ecbTaint_agree (dir : Dir) (s₁ s₂ : State) (_ : (ecbRISCV64 dir).pre s₁) (_ : (ecbRISCV64 dir).pre s₂)
    (hp : (ecbRISCV64 dir).pub s₁ s₂) : taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h1, h2, h3, h4]

theorem ecb_ct (dir : Dir) : ConstantTime isa (ecbRISCV64 dir).pre (ecbRISCV64 dir).pub (ecb dir) := by
  cases dir
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
      (ecbTaint_agree .encrypt) (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
      (ecbTaint_agree .decrypt) (by taint_decide)

theorem ecb_correct (dir : Dir) (s : State) (hs : (ecbRISCV64 dir).pre s) :
    ∃ t s', Exec isa (ecb dir) s t s' ∧ abiPreserved s s' ∧ (ecbRISCV64 dir).post s s' := by
  obtain ⟨t, s', he, h₁, hra, h₂⟩ := ecb_wp dir hs
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

/-- A state satisfying the precondition (one block). -/
def ecbSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | .a2 => 1 | .a3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 8 * 397⟩]

theorem ecb_verified (dir : Dir) :
    Verified target (ecb dir) (Proof.Sm4.ecbScratchContract abi (specDirA dir) slots) :=
  Verified.of_correct (ecb_correct dir) (ecb_ct dir) (by
    cases dir <;>
    sig_implies [Proof.Sm4.ecbScratchContract, Proof.Sm4.ecbScratchSig, Spec.Sm4.ecbPost, ecbRISCV64, specDirA,
      abi, argRegs, slots, savedSlot, tableEnd, tableSlot] [ecbSat] using ecbSat)

/-- A state satisfying the ECB functions' precondition: the schedule at
`0x1000`, one block at `0x3000`. -/
def ecbFrameSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | .a2 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩]

theorem ecbFrameSat_pre (d : Spec.Sm4.Direction) :
    ∃ s, (Spec.Sm4.ecbContract abi d 3184).pre s := by
  implies_sat [Spec.Sm4.ecbContract, Spec.Sm4.ecbSig, Spec.Sm4.ecbPost, abi, argRegs]
    [ecbFrameSat] using ecbFrameSat

/-- ECB in the direction `dir`, with its working space on the stack. -/
theorem ecb_framed (dir : Dir) :
    Verified target (Impl.StackScratch.RISCV64.withStackScratchWiped 3184 .a3 397 (ecb dir))
      (Spec.Sm4.ecbContract abi (specDirA dir) 3184) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.Sm4.ecbSig) (nm := "scratch") (e := .u64)
    (n := 397) (post := Spec.Sm4.ecbPost (specDirA dir) abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3184) (words := 397) (ecb_verified dir) (by decide) (by decide) (by decide)
    (Proof.Sm4.ecbPostOut_local _ _) (ecbFrameSat_pre _)

end VG.Proof.Sm4.RISCV64
