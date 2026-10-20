module

public import VerifiedGarbage.Impl.Dsa.X86_64.Arithmetic
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrame
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Encoding a DSA arithmetic result into its separate output buffer -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

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
  have hsmall : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off B o) (8 * i)) 8 :=
    fun i hi => hg.scr.ld (by have := hdr_lt_slot wx 8 hi; omega)
  have hlarge : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 :=
    fun i hi => hc.scr.ld (by omega)
  unfold Arithmetic.store seqs
  refine WP.seq (WP.mono (WP.keep [.rax, .rsi, .rcx, .rbx, .r15]
    (Q := fun u => u.gpr .rsi = out ∧ u.gpr .rcx = BitVec.ofNat 64 k ∧
      u.gpr .rbx = off (off B o) (slot wx a) ∧ u.gpr .r15 = mask true ∧ u.mem = s.mem) ?_ rfl)
    fun u ⟨⟨huout, huk, hua, humask, hum⟩, hku⟩ => ?_)
  · xrun [State.ea, hdr, Crt.ws, hc.rdi, hdrOff, hsmall Crt.sLink (by decide), hc.link,
      hlarge sp hsp, hp, hlarge sl hsl, hl,
      hsmall (sArr a) (by unfold sArr; omega), hc.hdr.harr a ha]
  refine WP.mono (storeBE_ok (hg.scr.congr hku.2.2) hua huout huk humask hk1 hk' hkw
    (by have := slot_le (w := wx) ha; omega)
    (fun j hj => by rw [hku.2.2]; exact hout j hj) hsep) fun t ⟨hv, hf, _, _, hk⟩ => ?_
  refine ⟨?_, ?_, (hku.trans hk).mono (by decide)⟩
  · rw [encodeBE_i2osp]
    rw [hum] at hv
    exact hv
  · intro x hx
    rw [hf x hx, hum]

end VG.Proof.Dsa.X86_64
