module
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Pack
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PackPart
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Pack a component into a bounded domain buffer, preserving all sources -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem packInto_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {src d total : Nat} {bs : List Byte}
    (hs : src < 2 ^ 31) (hl : 2 ≤ bs.length ∧ bs.length ≤ 1024)
    (ht : total ≤ 1024) (hroom : d + bs.length ≤ total)
    (source : Src s (off (W 5) packed) total (off (W 5) src) bs)
    (hwr : ∀ i < total, InRegions s.wr (off (off (W 5) packed) i) 1)
    (hF : (⟨F, frameBytes⟩ : Region).Disjoint ⟨off (W 5) packed, total⟩)
    (hS : (⟨S, oRsa⟩ : Region).Disjoint ⟨off (W 5) packed, total⟩) :
    WP isa (Impl.Dsa.X86_64.Generation.packPart src (packed + d) bs.length) s fun t =>
      Spec.Rsa.bytesAt t.mem (off (off (W 5) packed) d) bs.length = bs ∧
      Lay t F S ∧ Rep t.mem F S V W ∧
      Frame [⟨off (off (W 5) packed) d, bs.length⟩] s.mem t.mem ∧
      InScr (off (W 5) packed) total s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  have hd : packed + d < 2 ^ 31 := by unfold packed; omega
  have sub : Region.Sub ⟨off (off (W 5) packed) d, bs.length⟩ ⟨off (W 5) packed, total⟩ :=
    Offset.sub_base _ hroom
  refine WP.mono (packPart_ok L R hs hd hl source.rd
    (fun i hi => by rw [← off_off, off_off]; exact hwr (d + i) (by omega))
    (fun i hi => by simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] using source.val i hi)
    (by
      intro i hi j hj he
      have hout := source.out i hi
      change total ≤ ofs (off (W 5) packed) (off (off (W 5) src) i) at hout
      rw [he, ← off_off, off_off] at hout
      simp only [ofs, off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : d + j < 2 ^ 64)] at hout
      omega)
    (by rw [← off_off]; exact hF.sub_right sub)
    (by rw [← off_off]; exact hS.sub_right sub)) fun t ⟨result, Lt, Rt, ft, kt⟩ => ?_
  have frame : Frame [⟨off (off (W 5) packed) d, bs.length⟩] s.mem t.mem := by
    simpa only [off_off] using ft
  refine ⟨by simpa only [off_off] using result, Lt, Rt, frame, ?_, kt⟩
  intro a ha
  apply frame a
  intro r hr hc
  rcases List.mem_singleton.mp hr with rfl
  have inside := sub a hc
  change ofs (off (W 5) packed) a + 1 ≤ total at inside
  omega

end VG.Proof.Dsa.X86_64.Generation
