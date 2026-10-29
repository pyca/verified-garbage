module
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Impl.Dsa.X86_64.Random

import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Impl.Dsa.X86_64.Random
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! The range check leaks its public pointers and width only. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

structure RandomRangePublic where
  B : Addr
  Q : Addr
  qLen : Nat
  width : Nat

def RandomRangePre (p : RandomRangePublic) (s : State) : Prop :=
  Scr s p.B Random.frameBytes ∧ s.gpr .rsp = p.B ∧
  word s.mem p.B Random.oQLen = BitVec.ofNat 64 p.qLen ∧
  word s.mem p.B Random.oWidth = BitVec.ofNat 64 p.width ∧
  word s.mem p.B Random.oQ = p.Q

def RandomRangeRegs (p : RandomRangePublic) (s : State) : Prop :=
  s.gpr .rdx = off p.B (Random.oNonce + p.qLen) ∧
  s.gpr .r10 = p.Q + BitVec.ofNat 64 p.width ∧ s.gpr .r11 = BitVec.ofNat 64 p.width

theorem random_inRange_ct : RelCT isa (Two RandomRangePre) Random.inRange (fun _ _ => True) := by
  unfold Random.inRange
  refine RelCT.seq (two_piece (Ψ := RandomRangeRegs) [.rsp] ?_ (by taint_decide) ?_) ?_
  · intro p s t hs ht r hr
    rw [List.mem_singleton] at hr
    subst r
    exact hs.2.1.trans ht.2.1.symm
  · intro p s ⟨hs, hsp, hl, hn, hq⟩
    exact WP.mono (random_rangeInit_ok hs hsp hl hn hq) fun _ ⟨hd, h10, h11, _, _, _, _⟩ => ⟨hd, h10, h11⟩
  · apply two_taint [.r10, .rdx, .r11] ?_ (by taint_decide)
    intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.2.1.trans ht.2.1.symm
    · exact hs.1.trans ht.1.symm
    · exact hs.2.2.trans ht.2.2.symm

end VG.Proof.Dsa.X86_64
