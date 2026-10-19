module

public import VerifiedGarbage.Impl.MillerRabin.AArch64.Round
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Spec.RsaKeyGen

/-! # Release the round's Boolean result without a secret branch -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

private theorem mask_and_one (p : Bool) : mask p &&& (BitVec.setWidth 64 1#16) = BitVec.ofNat 64 p.toNat := by
  cases p <;> decide

theorem returnFlag_ok {s : State} {B : Addr} {Z w : Nat} {p : Bool}
    (h : Ws s B Z w) (hp : word s.mem B (8 * kFlag) = mask p) :
    WP isa (.block returnFlag) s fun t =>
      t.mem = s.mem ∧ t.gpr .x0 = BitVec.ofNat 64 p.toNat ∧ Keep [.x0, .x3, .x4] s t := by
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * kFlag)) 8 :=
    h.scr.ld (by have := h.h256; simp only [kFlag, kPlen, sFn]; omega_arith)
  refine WP.mono (WP.keep [.x0, .x3, .x4]
    (Q := fun t => t.mem = s.mem ∧ t.gpr .x0 = BitVec.ofNat 64 p.toNat) ?_
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨hm, hr⟩, hk⟩ => ⟨hm, hr, hk⟩
  unfold returnFlag
  brun [h.x0, hdr_enc (show kFlag < 32 by decide), hl, hp, mask_and_one]

end VG.Proof.MillerRabin.AArch64
