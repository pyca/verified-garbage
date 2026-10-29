module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Pack
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic

import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PackPart
import VerifiedGarbage.Proof.Framework.AddrArith
/-! # Pack all three generated parameters into p || q || g -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/PackInto.lean`, which only this module imported.
section

/-! # Pack a component into a bounded domain buffer, preserving all sources -/

section
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
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem pack_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    {pb qb gb : List Byte} {pLen qLen : Nat}
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (hp : pb.length = pLen) (hq : qb.length = qLen) (hg : gb.length = pLen)
    (hl : 2 ≤ pLen ∧ 2 ≤ qLen ∧ 2 * pLen + qLen ≤ 1024)
    (sp : Src s (off (W 5) packed) (2 * pLen + qLen) (off (W 5) Impl.Dsa.Generation.Layout.p) pb)
    (sq : Src s (off (W 5) packed) (2 * pLen + qLen) (off (W 5) q) qb)
    (sg : Src s (off (W 5) packed) (2 * pLen + qLen) (off (W 5) g) gb)
    (hwr : ∀ i < 2 * pLen + qLen, InRegions s.wr (off (off (W 5) packed) i) 1)
    (hF : (⟨F, frameBytes⟩ : Region).Disjoint ⟨off (W 5) packed, 2 * pLen + qLen⟩)
    (hS : (⟨S, oRsa⟩ : Region).Disjoint ⟨off (W 5) packed, 2 * pLen + qLen⟩) :
    WP isa (Impl.Dsa.X86_64.Generation.pack pLen qLen) s fun t =>
      Spec.Rsa.bytesAt t.mem (off (W 5) packed) (2 * pLen + qLen) = pb ++ qb ++ gb ∧
      Lay t F S ∧ Rep t.mem F S V W ∧
      Frame [⟨off (W 5) packed, 2 * pLen + qLen⟩] s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  unfold Impl.Dsa.X86_64.Generation.pack
  change WP isa (.seq _ (.seq _ _)) s _
  have first := packInto_ok (d := 0) L R (by decide : Impl.Dsa.Generation.Layout.p < 2 ^ 31)
    (by omega) hl.2.2 (by omega) sp hwr hF hS
  simp only [Nat.add_zero, hp] at first
  refine WP.seq (WP.mono first fun u ⟨bu, Lu, Ru, _, fu, ku⟩ => ?_)
  have second := packInto_ok (d := pLen) Lu Ru (by decide : q < 2 ^ 31)
    (by omega) hl.2.2 (by omega) (sq.congrK fu ku)
    (fun i hi => by rw [ku.2.2]; exact hwr i hi) hF hS
  simp only [hq] at second
  refine WP.seq (WP.mono second fun v ⟨bv, Lv, Rv, fv, iv, kv⟩ => ?_)
  have third := packInto_ok (d := pLen + qLen) Lv Rv (by decide : g < 2 ^ 31)
    (by omega) hl.2.2 (by omega) (sg.congrK (fu.trans iv) (ku.trans kv))
    (fun i hi => by rw [kv.2.2, ku.2.2]; exact hwr i hi) hF hS
  simp only [hg] at third
  simp only [Impl.Bignum.X86_64.seqs, Nat.add_assoc]
  refine WP.mono third fun t ⟨bt, Lt, Rt, ft, it, kt⟩ => ?_
  have keep := (ku.trans kv).trans kt
  have inside := (fu.trans iv).trans it
  refine ⟨?_, Lt, Rt, ?_, keep.mono (by decide)⟩
  · have preserveP : Spec.Rsa.bytesAt t.mem (off (W 5) packed) pLen = pb := by
      rw [VG.Proof.Dsa.Generation.frame_bytesAt ft (by
        intro r hr; rcases List.mem_singleton.mp hr with rfl
        exact Offset.base_disjoint _ (by omega) (by omega)) (by omega),
        VG.Proof.Dsa.Generation.frame_bytesAt fv (by
          intro r hr; rcases List.mem_singleton.mp hr with rfl
          exact Offset.base_disjoint _ (by omega) (by omega)) (by omega)]
      simpa [off] using bu
    have preserveQ : Spec.Rsa.bytesAt t.mem (off (off (W 5) packed) pLen) qLen = qb := by
      rw [VG.Proof.Dsa.Generation.frame_bytesAt ft (by
        intro r hr; rcases List.mem_singleton.mp hr with rfl
        exact Offset.disjoint _ (Or.inl (by omega)) (by omega) (by omega)) (by omega)]
      exact bv
    rw [show 2 * pLen + qLen = (pLen + qLen) + pLen by omega,
      VG.Proof.Dsa.Generation.bytesAt_append, VG.Proof.Dsa.Generation.bytesAt_append,
      preserveP, preserveQ, bt]
  · intro a ha
    apply inside a
    have hn := ha ⟨off (W 5) packed, 2 * pLen + qLen⟩ (by simp)
    change ¬ ofs (off (W 5) packed) a < 2 * pLen + qLen at hn
    omega

end VG.Proof.Dsa.X86_64.Generation
