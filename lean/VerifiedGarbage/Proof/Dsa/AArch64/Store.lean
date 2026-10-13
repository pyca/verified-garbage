module

public import VerifiedGarbage.Impl.Dsa.AArch64.Arithmetic
public import VerifiedGarbage.Proof.Dsa.Digest
public import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtFrame
public import VerifiedGarbage.Proof.Bignum.AArch64.Store
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Encoding a DSA arithmetic result into its separate output buffer -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- Store the full allocated width, including any leading zero padding.
The frame is stated bytewise so it also covers the caller's scratch suffix. -/
theorem store_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) {a sp sl k : Nat} {out : Addr}
    (ha : a < 8) (hsp : sp < 32) (hsl : sl < 32)
    (hp : word s.mem B (8 * sp) = out)
    (hl : word s.mem B (8 * sl) = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (out + BitVec.ofNat 64 j) 1)
    (hsep : ∀ j < k, slot wx 8 ≤ ofs (off B o) (out + BitVec.ofNat 64 j)) :
    WP isa (Arithmetic.store a sp sl) s fun t =>
      Spec.Rsa.bytesAt t.mem out k = Spec.Dsa.encodeBE k (wv s.mem (off B o) (slot wx a) wx) ∧
      (∀ x, (∀ j < k, x ≠ out + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧
      Keep mmRegs s t := by
  have hg := hc.good
  have hlo := hc.lo
  have hhi := hc.hi
  have h256 : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega
  unfold Arithmetic.store
  refine WP.seq (WP.mono (WP.keep [.x1, .x5, .x7, .x8, .x9, .x15]
    (Q := fun u => u.gpr .x1 = out + BitVec.ofNat 64 k ∧ u.gpr .x9 = BitVec.ofNat 64 k ∧
      u.gpr .x8 = off (off B o) (slot wx a) ∧ u.gpr .x15 = mask true ∧ u.mem = s.mem) ?_ rfl rfl rfl)
    fun u ⟨⟨huout, huk, hua, humask, hum⟩, hku⟩ => ?_)
  · brun [Crt.ldw, hc.x0, hdr_enc (show Crt.sLink < 32 by decide), hdr_enc hsp, hdr_enc hsl,
      hdr_enc (sArr_lt ha), hc.ld' (show Crt.sLink < 32 by decide), hc.link', hc.ldn hsp, hp,
      hc.ldn hsl, hl, hc.ld' (sArr_lt ha), hc.harr' ha, off_off]
  refine WP.mono (storeBE_ok (hg.scr.congr hku.wr) hua huout huk humask hk1 hk' hkw
    (by have := slot_le (w := wx) ha; omega)
    (fun j hj => by rw [hku.wr]; exact hout j hj) hsep) fun t ⟨hv, hf, _, _, hk⟩ => ?_
  refine ⟨?_, ?_, (hku.trans hk).mono (by decide)⟩
  · rw [encodeBE_i2osp]
    rw [hum] at hv
    exact hv
  · intro x hx
    rw [hf x hx, hum]

end VG.Proof.Dsa.AArch64
