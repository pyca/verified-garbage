module

public import VerifiedGarbage.Proof.Dsa.AArch64.Finish
public import VerifiedGarbage.Proof.Dsa.AArch64.Frame
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! # Composing DSA arithmetic with result encoding and workspace return -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- A result call changes the selected child and the designated output bytes. -/
def ResultFrame (B : Addr) (o wx : Nat) (out : Addr) (k : Nat) (mem mem' : Mem) : Prop :=
  ∀ x, (∀ r ∈ workRanges wx, ofs (off B o) x < r.1 ∨ r.1 + r.2 ≤ ofs (off B o) x) →
    (∀ j < k, x ≠ out + BitVec.ofNat 64 j) → mem' x = mem x

/-- The parent can call a child again with the same modulus and inverse. -/
structure ChildReady (mem : Mem) (B : Addr) (o wx m : Nat) (minv : BitVec 64) : Prop where
  header : WsAt mem B o wx minv
  modulus : wv mem (off B o) (slot wx aN) wx = m
  inverse : ((word mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0

/-- Any verified arithmetic body can return an encoded result while keeping
its modulus and every parent-header word available for the next call. -/
theorem returnAfter_ok {s : State} {B out : Addr} {Z o w wx m value k : Nat}
    {minv parentMinv : BitVec 64} {body : Prog isa}
    (hc : SubCtx s B Z o w wx minv)
    (run : WP isa body s fun u => SubCtx u B Z o w wx minv ∧
      ModCtx u (off B o) (slot wx 8) wx minv m ∧
      wv u.mem (off B o) (slot wx aY) wx = value ∧
      Frm (off B o) (workRanges wx) s.mem u.mem ∧ Keep mmRegs s u)
    (hpm : word s.mem B (8 * sMinv) = parentMinv)
    (hp : word s.mem B (8 * result) = out)
    (hl : word s.mem B (8 * resultLen) = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (out + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (out + BitVec.ofNat 64 j)) :
    WP isa (.seq body (seqs Core.finish)) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      Spec.Rsa.bytesAt t.mem out k = Spec.Dsa.encodeBE k value ∧
      (∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i)) ∧
      ResultFrame B o wx out k s.mem t.mem ∧ Keep coreRegs s t := by
  have hlo := hc.lo
  have hhi := hc.hi
  have hroot : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega
  have hchild : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  refine WP.seq (WP.mono run fun u ⟨hcu, hmu, huv, hfu, hku⟩ => ?_)
  refine WP.mono (finish_ok hcu ((work_parent hc hfu (by decide)).trans hpm)
    ((work_parent hc hfu (by decide)).trans hp) ((work_parent hc hfu (by decide)).trans hl)
    hk1 hk' hkw (fun j hj => by rw [hku.wr]; exact hout j hj) hprefix)
    fun t ⟨hgt, htout, htword, hft, hkt⟩ => ?_
  have hcword : ∀ d, o + d + 8 ≤ Z → word t.mem (off B o) d = word u.mem (off B o) d := by
    intro d hd
    rw [word_off, word_off]
    exact htword _ hd
  have hhdr : WsAt t.mem B o wx minv :=
    (show WsAt u.mem B o wx minv from ⟨hcu.hdr, hcu.link⟩).of_words
      (fun i hi => hcword _ (by omega))
  have hn : wv t.mem (off B o) (slot wx aN) wx = m := by
    rw [wv_congr (fun i hi => hcword _ (by have := slot_le (w := wx) (show aN < 8 by decide); omega))]
    exact hmu.modulus
  have hinv : ((word t.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hcword _ (by have := slot_le (w := wx) (show aN < 8 by decide); omega)]
    exact hmu.inverse
  rw [huv] at htout
  exact ⟨hgt, ⟨hhdr, hn, hinv⟩, htout,
    fun i hi => (htword _ (by omega)).trans (work_parent hc hfu hi),
    fun x hx ho => (hft x ho).trans (hfu x hx), (hku.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
