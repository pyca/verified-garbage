module
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Impl.Dsa.AArch64.Random

import VerifiedGarbage.Proof.Dsa.AArch64.RandomFrame
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Impl.Dsa.AArch64.Random
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomFrame
meta import Mathlib.Tactic.Push
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! The range check leaks its public pointers and width only. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

structure RandomRangePublic where
  B : Addr
  Q : Addr
  qLen : Nat
  width : Nat

def RandomRangePre (p : RandomRangePublic) (s : State) : Prop :=
  Scr s p.B Random.frameBytes ∧ s.sp = p.B ∧
  word s.mem p.B Random.oQLen = BitVec.ofNat 64 p.qLen ∧
  word s.mem p.B Random.oWidth = BitVec.ofNat 64 p.width ∧
  word s.mem p.B Random.oQ = p.Q

def RandomRangeRegs (p : RandomRangePublic) (s : State) : Prop :=
  s.gpr .x2 = off p.B (Random.oNonce + p.qLen) ∧
  s.gpr .x12 = p.Q + BitVec.ofNat 64 p.width ∧ s.gpr .x9 = BitVec.ofNat 64 p.width

theorem random_inRange_ct : RelCT isa (Two RandomRangePre) Random.inRange (fun _ _ => True) := by
  unfold Random.inRange
  refine RelCT.seq (two_piece (Ψ := RandomRangeRegs) [] ?_ (by taint_decide) ?_) ?_
  · intro _ _ _ _ _ _ hr; cases hr
  · intro p s ⟨hs, hsp, hl, hn, hq⟩
    exact WP.mono (random_rangeInit_ok hs hsp hl hn hq) fun _ ⟨hd, h10, h11, _, _, _, _⟩ => ⟨hd, h10, h11⟩
  · apply two_taint [.x12, .x2, .x9] ?_ (by taint_decide)
    intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.2.1.trans ht.2.1.symm
    · exact hs.1.trans ht.1.symm
    · exact hs.2.2.trans ht.2.2.symm

end VG.Proof.Dsa.AArch64
