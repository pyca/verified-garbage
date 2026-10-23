module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.Ecb
public import VerifiedGarbage.Proof.Camellia.Scratch
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Camellia.PPC64LE.Ecb
meta import VerifiedGarbage.Proof.Camellia.Scratch
meta import VerifiedGarbage.Impl.StackScratch.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# Camellia ECB on PPC64LE meets its contracts

`ecb_verified`: `ecb dir` is correct (`ecb_wp`) and constant time, by the
taint analysis: the pointers, `rounds`, `n` and the stack pointer are public, and so
is everything the code computes from them, which it keeps in registers
(`r3`–`r12`, the copies' pointers and counts and the loop
tests). `ecb_framed` runs it with its working space on the stack, zeroed on
return: 3344 bytes, for the 414 words of the scratch buffer.
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE

open VG VG.PPC64LE VG.Impl.Camellia.PPC64LE

theorem ecbTaint_agree (dir : Dir) (s₁ s₂ : State) (_ : (ecbPPC64LE dir).pre s₁) (_ : (ecbPPC64LE dir).pre s₂)
    (hp : (ecbPPC64LE dir).pub s₁ s₂) : taint.Agree (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem ecb_ct (dir : Dir) : ConstantTime isa (ecbPPC64LE dir).pre (ecbPPC64LE dir).pub (ecb dir) := by
  cases dir
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
      (ecbTaint_agree .encrypt) (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
      (ecbTaint_agree .decrypt) (by taint_decide)

/-- The registers ECB writes. -/
def ecbWrites : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20,
   .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

theorem ecb_correct (dir : Dir) (s : State) (hs : (ecbPPC64LE dir).pre s) :
    ∃ t s', Exec isa (ecb dir) s t s' ∧ abiPreserved s s' ∧ (ecbPPC64LE dir).post s s' := by
  have hn : (ecb dir).noCalls = true := by cases dir <;> lit_decide
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, hk⟩ := WP.keep ecbWrites (ecb_wp dir hs) (by cases dir <;> lit_decide) hn
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.lr he hn (by cases dir <;> lit_decide)⟩, h₂⟩
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

/-- A state satisfying the precondition (one block). -/
def ecbSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 18 | .r5 => 0x3000 | .r6 => 1 | .r7 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 8 * 414⟩]

theorem ecb_verified (dir : Dir) :
    Verified target (ecb dir) (Proof.Camellia.ecbScratchContract abi (specDir dir) slots) :=
  Verified.of_correct (ecb_correct dir) (ecb_ct dir) (by
    cases dir <;>
    sig_implies [Proof.Camellia.ecbScratchContract, Proof.Camellia.ecbScratchSig, Spec.Camellia.ecbSig,
      Spec.Camellia.ecbPre, Spec.Camellia.ecbPost, ecbPPC64LE, specDir, abi, argRegs, slots, tailSlot, savedSlot,
      endSlot, keySlot] [ecbSat] using ecbSat)

/-- A state satisfying the ECB functions' precondition: the schedule at
`0x1000`, one block at `0x3000`, 18 rounds. -/
def ecbFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 18 | .r5 => 0x3000 | .r6 => 1 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x3000, 16⟩]

theorem ecbFrameSat_pre (d : Spec.Camellia.Direction) :
    ∃ s, (Spec.Camellia.ecbContract abi d 3344).pre s := by
  implies_sat [Spec.Camellia.ecbContract, Spec.Camellia.ecbSig, Spec.Camellia.ecbPre, Spec.Camellia.ecbPost, abi,
    argRegs] [ecbFrameSat] using ecbFrameSat

/-- ECB in the direction `dir`, with its working space on the stack. -/
theorem ecb_framed (dir : Dir) :
    Verified target (Impl.StackScratch.PPC64LE.withStackScratchWiped 3344 .r7 414 (ecb dir))
      (Spec.Camellia.ecbContract abi (specDir dir) 3344) :=
  Verified.stackScratchWiped (sig := Spec.Camellia.ecbSig) (nm := "scratch") (e := .u64)
    (n := 414) (pre := Spec.Camellia.ecbPre abi.ptrBits)
    (post := Spec.Camellia.ecbPost (specDir dir) abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 3344) (words := 414) (by rw [← Proof.Camellia.ecbScratchContract_eq]; exact ecb_verified dir)
    (by decide) (by decide) (by decide) (Proof.Camellia.ecbPre_local _) (Proof.Camellia.ecbPost_local _ _)
    (Proof.Camellia.ecbPostOut_local _ _) (ecbFrameSat_pre _)

end VG.Proof.Camellia.PPC64LE
