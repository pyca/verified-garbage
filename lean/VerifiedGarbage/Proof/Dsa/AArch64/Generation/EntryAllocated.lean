module
public import VerifiedGarbage.Proof.Framework.AArch64.Call

import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # Allocating and freeing a frame of the native search -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64


def allocState (bytes : Nat) (s : State) : State :=
  { s with sp := s.sp - BitVec.ofNat 64 bytes, wr := ⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr }

def freeState (bytes : Nat) (s : State) : State :=
  { s with sp := s.sp + BitVec.ofNat 64 bytes, wr := s.wr.tail }

theorem alloc_frame_ok {bytes : Nat} (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0)
    {s : State} (hl : bytes ≤ s.sp.toNat) {body : Prog isa} {Q : State → Prop}
    (run : WP isa body (allocState bytes s) fun t =>
      t.sp = (allocState bytes s).sp ∧ t.wr = (allocState bytes s).wr ∧ Q (freeState bytes t)) :
    WP isa (.frame (.alloc bytes) body (.free bytes)) s Q := by
  obtain ⟨trace, t, he, hsp, hwr, hq⟩ := run
  have ha : isa.push (.alloc bytes) s = some (allocState bytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨hb.1, hb.2.1, hb.2.2, hl⟩
  have hf : isa.pop (.free bytes) (allocState bytes s) t = some (freeState bytes t) := by
    simp only [isa, pop]
    exact ite_eq_left ⟨hb.1, hb.2.1, hb.2.2, hsp, hwr, rfl⟩
  exact ⟨_, _, Exec.frame ha he hf, hq⟩

end VG.Proof.Dsa.AArch64.Generation
