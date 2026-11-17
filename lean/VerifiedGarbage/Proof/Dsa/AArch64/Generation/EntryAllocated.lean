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
      ∀ m u, Frame [⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩] t.mem m →
        Q { freeState bytes t with mem := m, unknowns := u }) :
    WP isa (.frame (.alloc bytes) body (.free bytes)) s Q :=
  WP.alloc hb hl run

end VG.Proof.Dsa.AArch64.Generation
