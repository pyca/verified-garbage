module

public import VerifiedGarbage.Proof.Camellia.Arm.ExpandKey
meta import VerifiedGarbage.Proof.Camellia.Arm.ExpandKey
public import VerifiedGarbage.Proof.Framework.Arm.TaintMono
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Proof.Camellia.Arm.Lit
public import VerifiedGarbage.Proof.Camellia.Scratch
public import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.TaintMono
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Arm.RegScratchWipe
meta import VerifiedGarbage.Proof.Framework.Arm.RegScratchWipe
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Impl.Aes.Arm.Alloc
import VerifiedGarbage.Proof.Camellia.Arm.Copy
import VerifiedGarbage.Proof.Camellia.Arm.Crypt8
import VerifiedGarbage.Proof.Camellia.Arm.Fl
import VerifiedGarbage.Proof.Camellia.Arm.KaKb
import VerifiedGarbage.Proof.Camellia.Arm.KeyInit
import VerifiedGarbage.Proof.Camellia.Arm.KeyLoad
import VerifiedGarbage.Proof.Camellia.Arm.Verified
import VerifiedGarbage.Proof.Camellia.Planes32
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Aes.Arm.Alloc
meta import VerifiedGarbage.Proof.Camellia.Arm.Copy
meta import VerifiedGarbage.Proof.Camellia.Arm.Crypt8
meta import VerifiedGarbage.Proof.Camellia.Arm.Fl
meta import VerifiedGarbage.Proof.Camellia.Arm.KaKb
meta import VerifiedGarbage.Proof.Camellia.Arm.KeyInit
meta import VerifiedGarbage.Proof.Camellia.Arm.KeyLoad
meta import VerifiedGarbage.Proof.Camellia.Arm.Verified
meta import VerifiedGarbage.Proof.Camellia.Planes32
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.CallF
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# The Camellia key schedule on ARMv7 meets its contracts

`expandKey_verified`: `expandKey` is correct (`expandKey_wp`) and constant
time, by the taint analysis: the pointers and the key's length are public,
and so are the schedule's pointer, the length and the count of pairs the
code keeps in slots of the scratch buffer (stored through `sb`, the
buffer's base). `expandKey_framed` runs it with its working space on the
stack, zeroed on return, as `ecb_framed` does.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Impl.Camellia.Arm

/-- The initial taint: the arguments are public; `r3` points at the scratch
buffer, the second writable region. -/
def expandKeyTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [272, 4 * slots], bases := [(.r3, 1)] }

theorem expandKeyTaint_wf {s : State} (h : expandKeyArm.pre s) : VG.Arm.Taint.Wf expandKeyTaint s := by
  obtain ⟨-, hwr, -, -, dSB, -, fitS, fitB, -⟩ := h
  refine ⟨fun _ => ⟨by simp [hwr, expandKeyTaint], ?_, ?_⟩, fun p hp => ?_, fun h => by simp [expandKeyTaint] at h,
    fun p hp => by simp [expandKeyTaint] at hp⟩
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil]
    exact ⟨dSB, fun _ h => h.elim, trivial⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · simp only [expandKeyTaint, List.mem_singleton] at hp; subst hp
    simp [VG.Arm.Taint.region, hwr]

theorem expandKeyTaint_agree (s₁ s₂ : State) (h₁ : expandKeyArm.pre s₁) (h₂ : expandKeyArm.pre s₂)
    (hp : expandKeyArm.pub s₁ s₂) : VG.Arm.Taint.Agree expandKeyTaint s₁ s₂ := by
  obtain ⟨p0, p1, p2, p3, -⟩ := hp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, expandKeyTaint_wf h₁, expandKeyTaint_wf h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => by simp [expandKeyTaint] at h, fun k hk => by simp [expandKeyTaint] at hk⟩
  · simp only [expandKeyTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.2.1, h₂.2.1, p2, p3]

/-- What `KA` and `KB` need public: the arguments, the scratch buffer's and
the table's pointers, and the schedule's address and the key's length in
their slots. Not the sigma constants, which the prologue stores in the
table: each is a public slot of its own, which the analysis of every later
instruction would look through. -/
def kaKbTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3, .r8, .r9], flags := false, lens := [272, 4 * slots],
    bases := [(.r3, 1), (.r8, 1)], slots := [(1, 4 * nSlot, 4), (1, 4 * dSlot, 4)] }

taint_summary kaKbSum : taintS kaKbTaint kaKb

theorem expandKey_ct : ConstantTime isa expandKeyArm.pre expandKeyArm.pub expandKey :=
  let ⟨_, h⟩ := (by taint_decide_sum [kaKbSum] : ∃ h, (taintS.check expandKeyTaint expandKey h).isSome = true)
  VG.Taint.constantTime (A := taintS) expandKeyTaint expandKeyTaint_agree h

theorem expandKey_correct (s : State) (hs : expandKeyArm.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandKeyArm.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := expandKey_wp hs
  refine ⟨t, s', he, ⟨fun r hr => ?_, VG.Arm.Exec.sp he⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega)
  · exact h₁ 1 (by omega)
  · exact h₁ 2 (by omega)
  · exact h₁ 3 (by omega)
  · exact h₁ 4 (by omega)
  · exact h₁ 5 (by omega)
  · exact h₁ 6 (by omega)
  · exact h₁ 7 (by omega)
  · exact h₁ 8 (by omega)

/-- A state satisfying the precondition: a key of 16 bytes at `0x1000`. -/
def expandKeySat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 16 | .r2 => 0x2000 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 272⟩, ⟨0x4000, 4 * 680⟩]

theorem expandKey_verified :
    Verified Arm.target expandKey (Proof.Camellia.expandKeyScratchContract Arm.abi 340) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Proof.Camellia.expandKeyScratchContract, Proof.Camellia.expandKeyScratchSig,
      Spec.Camellia.expandKeySig, Spec.Camellia.expandKeyPre, Spec.Camellia.expandKeyPost, expandKeyArm,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr, slots, tailSlot, savedSlot, endSlot,
      grpSlot, keySlot]
      [expandKeySat] using expandKeySat)

/-- A state satisfying the key schedule's precondition, without the working space. -/
def expandKeyFrameSat : State := { expandKeySat with wr := [⟨0x2000, 272⟩] }

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Camellia.expandKeyContract Arm.abi 2720).pre s := by
  implies_sat [Spec.Camellia.expandKeyContract, Spec.Camellia.expandKeySig, Spec.Camellia.expandKeyPre,
    Spec.Camellia.expandKeyPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [expandKeyFrameSat, expandKeySat] using expandKeyFrameSat

/-- Key expansion, with its working space on the stack. -/
theorem expandKey_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withRegScratchWiped 2720 .r3 680 expandKey)
      (Spec.Camellia.expandKeyContract Arm.abi 2720) :=
  Arm.Verified.regScratchWiped (sig := Spec.Camellia.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 340) (pre := Spec.Camellia.expandKeyPre Arm.abi.ptrBits)
    (post := Spec.Camellia.expandKeyPost Arm.abi.ptrBits) (wa := false) (stack := 0)
    (by rw [← Proof.Camellia.expandKeyScratchContract_eq]; exact expandKey_verified)
    (by decide) (by decide) (by decide) (by decide)
    (Proof.Camellia.expandKeyPostOut_local _) expandKeyFrameSat_pre

end VG.Proof.Camellia.Arm
