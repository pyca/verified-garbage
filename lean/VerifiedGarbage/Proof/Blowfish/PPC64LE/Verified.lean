module

public import VerifiedGarbage.Proof.Blowfish.PPC64LE.EcbVerified
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.KeyMain
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Blowfish.PPC64LE.EcbVerified
meta import VerifiedGarbage.Proof.Blowfish.PPC64LE.KeyMain
meta import VerifiedGarbage.Impl.StackScratch.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Blowfish on PPC64LE meets its contracts

Key expansion meets `expandKeyScratchContract` (`expandKey_verified`), the
contract with the working space as an argument, as ECB does
`ecbScratchContract` (`EcbVerified.lean`). Each runs in a frame that
allocates its working space and zeroes the 32 bytes the code uses after it
(`Verified.stackScratchWiped`): they hold our caller's `r14`–`r17`. The
code uses no other stack.
-/

@[expose] public section

namespace VG.Proof.Blowfish.PPC64LE

open VG VG.PPC64LE VG.Impl.Blowfish.PPC64LE VG.Spec.Blowfish VG.Proof.Blowfish

/-- The key expansion contract as the code sees it. -/
def keyC : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let sch : Region := ⟨s.gpr .r5, 4168⟩
    let buf : Region := ⟨s.gpr .r6, 32⟩
    s.rd = [key] ∧ s.wr = [sch, buf] ∧ key.Disjoint sch ∧ key.Disjoint buf ∧ sch.Disjoint buf ∧
      validKey (s.gpr .r4).toNat
  post s s' := scheduleAt s'.mem (s.gpr .r5) = expandKey (bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

/-- The registers key expansion writes. -/
def keyRegs : List Reg := [.r0, .r3, .r4, .r5, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17]

theorem expandKey_ok (s : State) (hs : keyC.pre s) :
    ∃ t s', Exec isa Impl.Blowfish.PPC64LE.expandKey s t s' ∧ abiPreserved s s' ∧ keyC.post s s' := by
  obtain ⟨rd, wr, kS, kB, SB, valid⟩ := hs
  have hn : Impl.Blowfish.PPC64LE.expandKey.noCalls = true := by decide +kernel
  obtain ⟨t, s', he, hp, hk⟩ := WP.keep keyRegs (expandKey_wp ⟨valid, rd, wr, kS, kB, SB⟩)
    (by decide +kernel) hn
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.lr he hn (by rw [← Code.allInstrs_eq]; decide +kernel)⟩,
    hp.sched⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    first
    | exact hp.saved _ (by decide)
    | exact hk.gpr (by decide)

theorem key_agree : ∀ s₁ s₂, keyC.pre s₁ → keyC.pre s₂ → keyC.pub s₁ s₂ →
    taint.Agree (Taint.ofRegs [.r3, .r4, .r5, .r6]) s₁ s₂ := by
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1

theorem expandKey_ct : ConstantTime isa keyC.pre keyC.pub Impl.Blowfish.PPC64LE.expandKey :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) key_agree (by taint_decide)

def keySat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 16 | .r5 => 0x2000 | .r6 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 4168⟩, ⟨0x4000, 32⟩]

theorem expandKey_verified :
    Verified target Impl.Blowfish.PPC64LE.expandKey (Proof.Blowfish.expandKeyScratchContract abi) := by
  refine Verified.of_correct (k := keyC) expandKey_ok expandKey_ct ?_
  sig_implies [Proof.Blowfish.expandKeyScratchContract, Proof.Blowfish.expandKeyScratchSig,
    Spec.Blowfish.expandKeyPre, Spec.Blowfish.expandKeyPost, Spec.Blowfish.validKey, abi, argRegs, keyC]
    [keySat] using keySat

/-! ## In their frames -/

/-- A state satisfying `vg_blowfish_expand_key`'s precondition: a 16-byte key
at `0x1000` and the schedule at `0x2000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 16 | .r5 => 0x2000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 4168⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Blowfish.expandKeyContract abi 64).pre s := by
  implies_sat [Spec.Blowfish.expandKeyContract, Spec.Blowfish.expandKeySig, Spec.Blowfish.expandKeyPre,
    Spec.Blowfish.expandKeyPost, Spec.Blowfish.validKey, abi, argRegs] [expandKeyFrameSat]
    using expandKeyFrameSat

theorem expandKey_framed :
    Verified target
      (Impl.StackScratch.PPC64LE.withStackScratchWiped 64 .r6 4 Impl.Blowfish.PPC64LE.expandKey)
      (Spec.Blowfish.expandKeyContract abi 64) :=
  Verified.stackScratchWiped (sig := Spec.Blowfish.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 4) (pre := Spec.Blowfish.expandKeyPre abi.ptrBits)
    (post := Spec.Blowfish.expandKeyPost abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 64) expandKey_verified (by decide) (by decide) (by decide)
    (Proof.Blowfish.expandKeyPre_local _) (Proof.Blowfish.expandKeyPost_local _)
    (Proof.Blowfish.expandKeyPostOut_local _) expandKeyFrameSat_pre

/-- ECB in the direction `d`, proved with its working space as an argument
and no stack, in its frame. -/
theorem ecb_framed {c : Prog isa} {d : Spec.Blowfish.Direction}
    (h : Verified target c (Proof.Blowfish.ecbScratchContract abi d 0)) :
    Verified target (Impl.StackScratch.PPC64LE.withStackScratchWiped 288 .r6 4 c)
      (Spec.Blowfish.ecbContract abi d 288) :=
  Verified.stackScratchWiped (sig := Spec.Blowfish.ecbSig) (nm := "scratch") (e := .u64)
    (n := 32) (post := Spec.Blowfish.ecbPost d abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 288) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Blowfish.ecbPost_local _ d)
    (Proof.Blowfish.ecbPostOut_local _ d)
    (sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Blowfish.PPC64LE
