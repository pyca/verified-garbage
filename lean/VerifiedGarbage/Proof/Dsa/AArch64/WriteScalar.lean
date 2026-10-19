module
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract

import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalarHead
import VerifiedGarbage.Proof.Dsa.AArch64.CopyMasked
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest

/-! # Masked copying of each DSA signature scalar to the caller -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem writeScalar_ok {s : State} {B out : Addr} {Z offset q : Nat} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z) (ho : offset < 2 ^ 16)
    (hout : word s.mem B Field.out.offset = out) (hq : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q)
    (hm : word s.mem B Field.mask.offset = mask valid) (second : Bool)
    (h1 : 0 < q) (h64 : q < 2 ^ 64) (hsrc : offset + q ≤ Z)
    (hw : ∀ i < q, InRegions s.wr ((if second then out + BitVec.ofNat 64 q else out) + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < q, Z ≤ ofs B ((if second then out + BitVec.ofNat 64 q else out) + BitVec.ofNat 64 i)) :
    WP isa (SignVerify.writeScalar offset second) s fun t =>
      (∀ i < q, t.mem ((if second then out + BitVec.ofNat 64 q else out) + BitVec.ofNat 64 i) =
        if valid then s.mem (off B offset + BitVec.ofNat 64 i) else 0) ∧
      (∀ x, (∀ i < q, x ≠ (if second then out + BitVec.ofNat 64 q else out) + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep [.x3, .x1, .x2, .x9, .x8] s t := by
  unfold SignVerify.writeScalar seqs
  refine WP.seq (WP.mono (scalarHead_ok hs hdi hZ ho hout hq hm second)
    fun u ⟨husi, hudx, hucx, hu8, hum, hku⟩ => ?_)
  have hr : ∀ i < q, InRegions (u.rd ++ u.wr) (off B offset + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [hku.rd, hku.wr, show off B offset + BitVec.ofNat 64 i = off B (offset + i) by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
    obtain ⟨r, hr, hc⟩ := hs.region (d := offset + i) (by omega) (show 0 < 1 by decide)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hsep' : ∀ i < q, ∀ j < q, off B offset + BitVec.ofNat 64 i ≠
      (if second then out + BitVec.ofNat 64 q else out) + BitVec.ofNat 64 j := by
    intro i hi j hj
    exact scr_ne_out hsep (d := offset) (i := i) (by omega) (by have := hs.nowrap; omega) j hj
  refine WP.mono (copyMasked_ok husi hudx hucx hu8 h1 h64 hr
    (fun i hi => by rw [hku.wr]; exact hw i hi) hsep') fun t ⟨htb, htf, hkt⟩ => ?_
  exact ⟨by rw [hum] at htb; exact htb, fun x hx => (htf x hx).trans (congrFun hum x),
    (hku.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
