module

public import VerifiedGarbage.Impl.Dsa.AArch64.Arithmetic
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtFrame
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Dsa.AArch64.Store`, which only this module used -/

section

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
  have h256 : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_using []
  have hsmall : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off B o) (8 * i)) 8 :=
    fun i hi => hg.scr.ld (by have := hdr_lt_slot wx 8 hi; omega_using [this])
  have hlarge : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 :=
    fun i hi => hc.scr.ld (by omega_using [hlo, hhi, h256, hi])
  unfold Arithmetic.store seqs
  refine WP.seq (WP.mono (WP.keep [.x5, .x1, .x9, .x8, .x15]
    (Q := fun u => u.gpr .x1 = out + BitVec.ofNat 64 k ∧ u.gpr .x9 = BitVec.ofNat 64 k ∧
      u.gpr .x8 = off (off B o) (slot wx a) ∧ u.gpr .x15 = mask true ∧ u.mem = s.mem) ?_ rfl rfl rfl)
    fun u ⟨⟨huout, huk, hua, humask, hum⟩, hku⟩ => ?_)
  · drun [Crt.ldw, hc.x0, hdr_enc hsp, hdr_enc hsl, hdr_enc (show Crt.sLink < 32 by decide),
      hdr_enc (show sArr a < 32 by unfold sArr; omega_using [ha]), hsmall Crt.sLink (by decide), hc.link,
      hlarge sp hsp, hp, hlarge sl hsl, hl,
      hsmall (sArr a) (by unfold sArr; omega_using [ha]), hc.hdr.harr a ha]
    rfl
  refine WP.mono (storeBE_ok (hg.scr.congr hku.wr) hua huout huk humask hk1 hk' hkw
    (by have := slot_le (w := wx) ha; omega_using [this])
    (fun j hj => by rw [hku.wr]; exact hout j hj) hsep) fun t ⟨hv, hf, _, _, hk⟩ => ?_
  refine ⟨?_, ?_, (hku.trans hk).mono (by decide)⟩
  · rw [encodeBE_i2osp]
    rw [hum] at hv
    exact hv
  · intro x hx
    rw [hf x hx, hum]

end VG.Proof.Dsa.AArch64

end

end

/-! # Writing arithmetic results beyond DSA's active workspace prefix -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- A bytewise output frame preserves every word in the active prefix. -/
theorem suffix_word {mem mem' : Mem} {B out : Addr} {Z k d : Nat}
    (hf : ∀ x, (∀ j < k, x ≠ out + BitVec.ofNat 64 j) → mem' x = mem x)
    (hout : ∀ j < k, Z ≤ ofs B (out + BitVec.ofNat 64 j))
    (hZ : Z ≤ 2 ^ 64) (hd : d + 8 ≤ Z) : word mem' B d = word mem B d := by
  apply Mem.readW_congr
  intro i hi
  apply hf
  intro j hj heq
  have hs := hout j hj
  rw [← heq, ofs_off B (by omega_using [hZ, hd, hi])] at hs
  omega_using [hd, hi, hs]

/-- Storing in the scratch suffix preserves both the parent and child
headers, every arithmetic array and the linked child context. -/
theorem storeSuffix_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) {a sp sl k : Nat} {out : Addr}
    (ha : a < 8) (hsp : sp < 32) (hsl : sl < 32)
    (hp : word s.mem B (8 * sp) = out)
    (hl : word s.mem B (8 * sl) = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (out + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (out + BitVec.ofNat 64 j)) :
    WP isa (Arithmetic.store a sp sl) s fun t =>
      SubCtx t B Z o w wx minv ∧
      Spec.Rsa.bytesAt t.mem out k = Spec.Dsa.encodeBE k (wv s.mem (off B o) (slot wx a) wx) ∧
      (∀ d, d + 8 ≤ Z → word t.mem B d = word s.mem B d) ∧
      (∀ j < 8, wv t.mem (off B o) (slot wx j) wx = wv s.mem (off B o) (slot wx j) wx) ∧
      (∀ x, (∀ j < k, x ≠ out + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧ Keep mmRegs s t := by
  have hn := hc.scr.nowrap
  have hhi := hc.hi
  have hlo := hc.lo
  have hroot : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_using []
  have hchild : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  have hsep : ∀ j < k, slot wx 8 ≤ ofs (off B o) (out + BitVec.ofNat 64 j) := by
    intro j hj
    have hp := hprefix j hj
    rcases ofs_rebase B (out + BitVec.ofNat 64 j) (o := o) (by omega_using [hn, hhi, hchild]) with ⟨_, h2⟩ | ⟨h1, _⟩ <;> omega_arith
  refine WP.mono (store_ok hc ha hsp hsl hp hl hk1 hk' hkw hout hsep)
    fun t ⟨hv, hf, hk⟩ => ?_
  have hwrd : ∀ d, d + 8 ≤ Z → word t.mem B d = word s.mem B d :=
    fun d hd => suffix_word hf hprefix (by omega_using [hn]) hd
  have hcword : ∀ i < 17, word t.mem (off B o) (8 * i) = word s.mem (off B o) (8 * i) := by
    intro i hi
    rw [word_off, word_off]
    exact hwrd _ (by omega_using [hhi, hchild, hi])
  have hctx : SubCtx t B Z o w wx minv :=
    ⟨hc.scr.congr hk.wr, (hk.gpr .x0 (by decide)).trans hc.x0,
      ⟨(hcword _ (by decide)).trans hc.hdr.hw, (hcword _ (by decide)).trans hc.hdr.hminv,
        fun j hj => (hcword _ (by unfold sArr; omega_using [hj])).trans (hc.hdr.harr j hj)⟩,
      (hcword _ (by decide)).trans hc.link,
      (hwrd _ (by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega_using [hhi, hlo, this])).trans hc.nw,
      fun j hj => (hwrd _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega_using [hj]); omega_using [hhi, hlo, this])).trans (hc.narr j hj),
      hlo, hhi⟩
  refine ⟨hctx, hv, hwrd, ?_, hf, hk⟩
  intro j hj
  apply wv_congr
  intro i hi
  rw [word_off, word_off]
  exact hwrd _ (by have := slot_le (w := wx) hj; omega_using [hhi, hi, this])

end VG.Proof.Dsa.AArch64
