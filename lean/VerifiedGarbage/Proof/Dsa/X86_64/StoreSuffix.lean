module
public import VerifiedGarbage.Impl.Dsa.X86_64.Arithmetic
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrame
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Dsa.X86_64.Store
import Mathlib.Tactic.Finiteness.Attr
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Writing arithmetic results beyond DSA's active workspace prefix -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

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
  rw [← heq, ofs_off B (by omega)] at hs
  omega

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
  have hroot : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega
  have hchild : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have hsep : ∀ j < k, slot wx 8 ≤ ofs (off B o) (out + BitVec.ofNat 64 j) := by
    intro j hj
    have hp := hprefix j hj
    rcases ofs_rebase B (out + BitVec.ofNat 64 j) (o := o) (by omega) with ⟨_, h2⟩ | ⟨h1, _⟩ <;> omega
  refine WP.mono (store_ok hc ha hsp hsl hp hl hk1 hk' hkw hout hsep)
    fun t ⟨hv, hf, hk⟩ => ?_
  have hwrd : ∀ d, d + 8 ≤ Z → word t.mem B d = word s.mem B d :=
    fun d hd => suffix_word hf hprefix (by omega) hd
  have hcword : ∀ i < 17, word t.mem (off B o) (8 * i) = word s.mem (off B o) (8 * i) := by
    intro i hi
    rw [word_off, word_off]
    exact hwrd _ (by omega)
  have hctx : SubCtx t B Z o w wx minv :=
    ⟨hc.scr.congr hk.2.2, (hk.gpr (by decide)).trans hc.rdi,
      ⟨(hcword _ (by decide)).trans hc.hdr.hw, (hcword _ (by decide)).trans hc.hdr.hminv,
        fun j hj => (hcword _ (by unfold sArr; omega)).trans (hc.hdr.harr j hj)⟩,
      (hcword _ (by decide)).trans hc.link,
      (hwrd _ (by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega)).trans hc.nw,
      fun j hj => (hwrd _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega); omega)).trans (hc.narr j hj),
      hlo, hhi⟩
  refine ⟨hctx, hv, hwrd, ?_, hf, hk⟩
  intro j hj
  apply wv_congr
  intro i hi
  rw [word_off, word_off]
  exact hwrd _ (by have := slot_le (w := wx) hj; omega)

end VG.Proof.Dsa.X86_64
