module

public import VerifiedGarbage.Proof.Sm4.PPC64LE.KeyEk
public import VerifiedGarbage.Proof.Sm4.Scratch
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.KeyEk
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Impl.StackScratch.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# SM4 key expansion on PPC64LE meets its contracts

`expandKey_verified`: `expandKey` is correct (`expandKey_wp`) and constant
time, by the taint analysis with the pointers and the stack pointer public.
`expandKey_framed` runs it with its working space on the stack, zeroed on
return, as `ecb_framed` does.
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4.PPC64LE
open VG.Proof.Sm4 (expandKeyPPC64LE)

theorem expandKeyTaint_agree (s₁ s₂ : State) (_ : expandKeyPPC64LE.pre s₁) (_ : expandKeyPPC64LE.pre s₂)
    (hp : expandKeyPPC64LE.pub s₁ s₂) : taint.Agree (Taint.ofRegs [.r3, .r4, .r5]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> with_reducible assumption

theorem expandKey_ct : ConstantTime isa expandKeyPPC64LE.pre expandKeyPPC64LE.pub expandKey :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5]) expandKeyTaint_agree (by taint_decide)

/-- The registers key expansion writes. -/
def expandKeyWrites : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20,
   .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

theorem expandKey_correct (s : State) (hs : expandKeyPPC64LE.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandKeyPPC64LE.post s s' := by
  have hn : expandKey.noCalls = true := by lit_decide
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, hk⟩ := WP.keep expandKeyWrites (expandKey_wp hs) (by lit_decide) hn
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.lr he hn (by lit_decide)⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact hk.gpr (by decide)
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
  · exact h₁ 12 (by omega)
  · exact h₁ 13 (by omega)
  · exact h₁ 14 (by omega)
  · exact h₁ 15 (by omega)
  · exact h₁ 16 (by omega)
  · exact h₁ 17 (by omega)

/-- A state satisfying the precondition. -/
def expandKeySat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 8 * 402⟩]

theorem expandKey_verified :
    Verified target expandKey (Proof.Sm4.expandKeyScratchContract abi slots) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Proof.Sm4.expandKeyScratchContract, Proof.Sm4.expandKeyScratchSig, Proof.Sm4.expandKeyPost,
      expandKeyPPC64LE, abi, argRegs, slots, savedSlot, tableEnd, tableSlot]
      [expandKeySat] using expandKeySat)

/-- A state satisfying the key schedule's precondition: the key at
`0x1000`, the schedule at `0x2000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Sm4.expandKeyContract abi 3248).pre s := by
  implies_sat [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, abi, argRegs]
    [expandKeyFrameSat] using expandKeyFrameSat

/-- Key expansion, with its working space on the stack. -/
theorem expandKey_framed :
    Verified target (Impl.StackScratch.PPC64LE.withStackScratchWiped 3248 .r5 402 expandKey)
      (Spec.Sm4.expandKeyContract abi 3248) :=
  Verified.stackScratchWiped (sig := Spec.Sm4.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 402) (post := Proof.Sm4.expandKeyPost abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 3248) (words := 402) expandKey_verified (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm4.expandKeyPost_local _)
    (Proof.Sm4.expandKeyPostOut_local _) expandKeyFrameSat_pre

end VG.Proof.Sm4.PPC64LE
