module
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Pack
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PackPart
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Pack a component into a bounded domain buffer, preserving all sources -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem packInto_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {src d total : Nat} {bs : List Byte}
    (hs : src < 2 ^ 16) (hl : 2 ≤ bs.length ∧ bs.length ≤ 1024)
    (ht : total ≤ 1024) (hroom : d + bs.length ≤ total)
    (source : Src s (VG.Proof.Bignum.off (W 5) packed) total (VG.Proof.Bignum.off (W 5) src) bs)
    (hwr : ∀ i < total, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) packed) i) 1)
    (hF : (⟨F, frameBytes⟩ : Region).Disjoint ⟨VG.Proof.Bignum.off (W 5) packed, total⟩)
    (hS : (⟨S, oRsa⟩ : Region).Disjoint ⟨VG.Proof.Bignum.off (W 5) packed, total⟩) :
    WP isa (Impl.Dsa.AArch64.Generation.packPart src (packed + d) bs.length) s fun t =>
      Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) packed) d) bs.length = bs ∧
      Lay t F S ∧ Rep t.mem F S V W ∧
      Frame [⟨VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) packed) d, bs.length⟩] s.mem t.mem ∧
      InScr (VG.Proof.Bignum.off (W 5) packed) total s.mem t.mem ∧ Keep (.x0 :: mmRegs) s t := by
  have hd : packed + d < 2 ^ 16 := by unfold packed; omega
  have sub : Region.Sub ⟨VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) packed) d, bs.length⟩ ⟨VG.Proof.Bignum.off (W 5) packed, total⟩ :=
    Offset.sub_base _ hroom
  refine WP.mono (packPart_ok L R hs hd hl source.rd
    (fun i hi => by rw [← VG.Proof.Bignum.off_off, VG.Proof.Bignum.off_off]; exact hwr (d + i) (by omega))
    (fun i hi => by simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] using source.val i hi)
    (by
      intro i hi j hj he
      have hout := source.out i hi
      change total ≤ ofs (VG.Proof.Bignum.off (W 5) packed) (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) src) i) at hout
      rw [he, ← VG.Proof.Bignum.off_off, VG.Proof.Bignum.off_off] at hout
      simp only [ofs, VG.Proof.Bignum.off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : d + j < 2 ^ 64)] at hout
      omega)
    (by rw [← VG.Proof.Bignum.off_off]; exact hF.sub_right sub)
    (by rw [← VG.Proof.Bignum.off_off]; exact hS.sub_right sub)) fun t ⟨result, Lt, Rt, ft, kt⟩ => ?_
  have frame : Frame [⟨VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) packed) d, bs.length⟩] s.mem t.mem := by
    simpa only [VG.Proof.Bignum.off_off] using ft
  refine ⟨by simpa only [VG.Proof.Bignum.off_off] using result, Lt, Rt, frame, ?_, kt⟩
  intro a ha
  apply frame a
  intro r hr hc
  rcases List.mem_singleton.mp hr with rfl
  have inside := sub a hc
  change ofs (VG.Proof.Bignum.off (W 5) packed) a + 1 ≤ total at inside
  omega

end VG.Proof.Dsa.AArch64.Generation
