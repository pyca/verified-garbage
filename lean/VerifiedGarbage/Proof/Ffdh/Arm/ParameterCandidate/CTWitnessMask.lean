module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTWitnessMaskStore
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessMaskHead
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessMaskBits
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase

/-! Masking a sampled witness reveals only the public phase bit width. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch

structure WitnessMaskData where
  base : BitVec 32
  capacity : Nat
  words : Nat
  bits : Nat

structure WitnessMaskStart (p : WitnessMaskData) (s : State) : Prop where
  ready : ArithmeticReady p.base p.capacity p.words s
  stack : Workspace s s.sp 72
  positive : 0 < p.bits
  bound : p.bits ≤ 8192
  saved : s.mem.readW (State.addr (s.sp + 44#32)) 32 = BitVec.ofNat 32 p.bits

private def WitnessMaskHead (p : WitnessMaskData) (s : State) : Prop :=
  ArithmeticReady p.base p.capacity p.words s ∧
  s.gpr .r5 = BitVec.ofNat 32 ((p.bits - 1) / 32) ∧
  s.gpr .r6 = BitVec.ofNat 32 ((p.bits - 1) % 32 + 1)

private theorem maskHead_ok (p : WitnessMaskData) (s : State) (h : WitnessMaskStart p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskHead) s (WitnessMaskHead p) := by
  refine WP.mono (witnessMaskHead_ok h.stack h.positive h.bound h.saved) ?_
  rintro t ⟨⟨index, count, mem⟩, rest⟩
  exact ⟨h.ready.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ready.ptr), index, count⟩

private def maskStoreData (p : WitnessMaskData) : MaskStoreData :=
  ⟨p.base, p.capacity, p.words, (p.bits - 1) / 32⟩

private theorem maskBits_ok (p : WitnessMaskData) (s : State) (h : WitnessMaskHead p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskBits s (MaskStoreStart (maskStoreData p)) := by
  refine WP.mono (witnessMaskBits_ok (by omega : (p.bits - 1) % 32 + 1 ≤ 32) h.2.2) ?_
  rintro t ⟨_, mem, rest⟩
  exact ⟨h.1.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.1.ptr), (rest.gpr .r5 (by simp)).trans h.2.1⟩

theorem witnessMask_ct : RelCT isa (Two WitnessMaskStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMask (fun _ _ => True) := by
  have head : RelCT isa (Two WitnessMaskStart)
      (.block VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskHead) (Two WitnessMaskHead) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) maskHead_ok
  have bitsTrace : RelCT isa (fun s t => s.sp = t.sp)
      VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskBits (fun s t => s.sp = t.sp) :=
    (stackOnly_ct _ rfl).seq ((stackOnly_ct _ rfl).seq (stackOnly_ct _ rfl))
  have bits : RelCT isa (Two WitnessMaskHead) VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskBits
      (Two MaskStoreStart) :=
    (two_post (bitsTrace.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) maskBits_ok).mono
      (fun _ _ h => h) (fun _ _ ⟨p, left, right, sp⟩ => ⟨maskStoreData p, left, right, sp⟩)
  exact head.seq (bits.seq (witnessMaskStore_ct.seq (RelCT.block_nil (fun _ _ _ => trivial))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
