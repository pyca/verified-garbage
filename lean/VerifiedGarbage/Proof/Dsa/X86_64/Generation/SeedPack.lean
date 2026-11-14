module
import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Pack
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ArenaSource
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PackPart
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork

/-! ### `Dsa.X86_64.Generation.Pack`, which only this module used -/

section

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
    (by omega_using [hp, hl]) hl.2.2 (by omega_using [hp]) sp hwr hF hS
  simp only [Nat.add_zero, hp] at first
  refine WP.seq (WP.mono first fun u ⟨bu, Lu, Ru, _, fu, ku⟩ => ?_)
  have second := packInto_ok (d := pLen) Lu Ru (by decide : q < 2 ^ 31)
    (by omega_using [hq, hl]) hl.2.2 (by omega_using [hq]) (sq.congrK fu ku)
    (fun i hi => by rw [ku.2.2]; exact hwr i hi) hF hS
  simp only [hq] at second
  refine WP.seq (WP.mono second fun v ⟨bv, Lv, Rv, fv, iv, kv⟩ => ?_)
  have third := packInto_ok (d := pLen + qLen) Lv Rv (by decide : g < 2 ^ 31)
    (by omega_using [hg, hl]) hl.2.2 (by omega_using [hg]) (sg.congrK (fu.trans iv) (ku.trans kv))
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
        exact Offset.base_disjoint _ (by omega_using []) (by omega_using [hl])) (by omega_using [hl]),
        VG.Proof.Dsa.Generation.frame_bytesAt fv (by
          intro r hr; rcases List.mem_singleton.mp hr with rfl
          exact Offset.base_disjoint _ (by omega_using []) (by omega_using [hl])) (by omega_using [hl])]
      simpa [off] using bu
    have preserveQ : Spec.Rsa.bytesAt t.mem (off (off (W 5) packed) pLen) qLen = qb := by
      rw [VG.Proof.Dsa.Generation.frame_bytesAt ft (by
        intro r hr; rcases List.mem_singleton.mp hr with rfl
        exact Offset.disjoint _ (Or.inl (by omega_using [])) (by omega_using [hl]) (by omega_using [hl])) (by omega_using [hl])]
      exact bv
    rw [show 2 * pLen + qLen = (pLen + qLen) + pLen by omega_using [],
      VG.Proof.Dsa.Generation.bytesAt_append, VG.Proof.Dsa.Generation.bytesAt_append,
      preserveP, preserveQ, bt]
  · intro a ha
    apply inside a
    have hn := ha ⟨off (W 5) packed, 2 * pLen + qLen⟩ (by simp)
    change ¬ ofs (off (W 5) packed) a < 2 * pLen + qLen at hn
    omega_using [hn]

end VG.Proof.Dsa.X86_64.Generation

end

end


/-! # Pack the accepted native buffers while preserving the seed-search state -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem seedPack_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (pb qb gb : List Byte)
    (hp : pb.length = p.geo.pLen) (hq : qb.length = p.geo.qLen) (hg : gb.length = p.geo.pLen)
    (bp : Spec.Rsa.bytesAt s.mem (off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = pb)
    (bq : Spec.Rsa.bytesAt s.mem (off p.geo.B q) p.geo.qLen = qb)
    (bg : Spec.Rsa.bytesAt s.mem (off p.geo.B g) p.geo.pLen = gb) :
    WP isa (Impl.Dsa.X86_64.Generation.pack p.geo.pLen p.geo.qLen) s fun t =>
      GenerationMemory p W t ∧
      Spec.Rsa.bytesAt t.mem (off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) = pb ++ qb ++ gb ∧
      Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have pn : 2 ≤ p.geo.pLen ∧ p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega_using [hh]
  have qn : 2 ≤ p.geo.qLen ∧ p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega_using [hh]
  have h5 := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
  have packedBound := p.geo.small_bound (d := packed) (n := 2 * p.geo.pLen + p.geo.qLen)
    (by decide) (by unfold arithmeticBytes; omega_using [pn, qn])
  have hh := p.geo.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  have src (d : Nat) (bs : List Byte) (hd : d + bs.length ≤ packed)
      (bytes : Spec.Rsa.bytesAt s.mem (off p.geo.B d) bs.length = bs) :
      Src s (off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) (off p.geo.B d) bs := by
    have bound : d + bs.length ≤ usedBytes p.geo.pLen := by omega_using [packedBound, hd]
    apply arena_source h.scratch bound (by unfold packed at hd; omega_using [hd]) bytes
    exact p.geo.parts_disjoint bound packedBound (Or.inl hd)
  obtain ⟨V, R⟩ := h.rep
  have call := pack_ok h.layout R hp hq hg ⟨pn.1, qn.1, by omega_using [pn, qn]⟩
  rw [h5] at call
  refine WP.mono (call
    (src VG.Impl.Dsa.Generation.Layout.p pb (by rw [hp]; unfold VG.Impl.Dsa.Generation.Layout.p packed; omega_using [pn]) (by simpa only [hp] using bp))
    (src q qb (by rw [hq]; unfold q packed; omega_using [qn]) (by simpa only [hq] using bq))
    (src g gb (by rw [hg]; unfold g packed; omega_using [pn]) (by simpa only [hg] using bg))
    (by intro i hi; rw [off_off]; exact h.scratch.region (by omega_using [packedBound, hi]) (by decide))
    (p.geo.frame_part packedBound) (p.geo.parts_disjoint hh packedBound (Or.inl (by decide))))
    fun t ⟨bytes, Lt, Rt, ft, kt⟩ => ?_
  have ff : Frame p.changed s.mem t.mem := by
    apply GenerationContext.frame_parts ft
    intro r hr
    rcases List.mem_singleton.mp hr with rfl
    exact ⟨⟨p.geo.B, usedBytes p.geo.pLen⟩, by simp [GenerationContext.changed], p.geo.part_sub packedBound⟩
  exact ⟨h.frame Lt ⟨V, Rt⟩ (fun _ _ => rfl) ff kt.2.1 kt.2.2, bytes, ff, kt.2.1, kt.2.2⟩

end VG.Proof.Dsa.X86_64.Generation
