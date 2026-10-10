import VerifiedGarbage.Proof.Sm4.AArch64.Ecb
import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract

/-!
# SM4 ECB on AArch64 meets its contracts

`ecb_verified`: `ecb dir` is correct (`ecb_wp`) and constant time, by the
taint analysis: the pointers, `n` and the stack pointer are public, and so
is everything the code computes from them, which it keeps in registers
(`x0`–`x5`, the copies' pointers and counts and the loop tests).
`ecb_framed` runs it with its working space on the stack, zeroed on
return: 3152 bytes, the 394 words of the scratch buffer.
-/

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
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) (ecbTaint_agree .encrypt)
      (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) (ecbTaint_agree .decrypt)
      (by taint_decide)

theorem ecb_correct (dir : Dir) (s : State) (hs : (ecbAArch64 dir).pre s) :
    ∃ t s', Exec isa (ecb dir) s t s' ∧ abiPreserved s s' ∧ (ecbAArch64 dir).post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (ecb_wp dir hs)
    (by cases dir <;> decide +kernel) (by cases dir <;> decide +kernel)
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he (by cases dir <;> decide +kernel)⟩, h₂⟩
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
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 8 * 394⟩]

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
    ∃ s, (Spec.Sm4.ecbContract AArch64.abi d 3152).pre s := by
  implies_sat [Spec.Sm4.ecbContract, Spec.Sm4.ecbSig, Spec.Sm4.ecbPost, AArch64.abi, AArch64.argRegs]
    [ecbFrameSat] using ecbFrameSat

/-- ECB in the direction `dir`, with its working space on the stack. -/
theorem ecb_framed (dir : Dir) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 3152 .x3 394 (ecb dir))
      (Spec.Sm4.ecbContract AArch64.abi (specDirA dir) 3152) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Sm4.ecbSig) (nm := "scratch") (e := .u64)
    (n := 394) (post := Spec.Sm4.ecbPost (specDirA dir) AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3152) (ecb_verified dir)
    (by decide) (by decide) (by decide) (Proof.Sm4.ecbPostOut_local _ _) (ecbFrameSat_pre _)

end VG.Proof.Sm4.AArch64
