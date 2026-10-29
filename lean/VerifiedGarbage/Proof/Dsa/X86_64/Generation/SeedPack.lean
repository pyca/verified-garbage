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
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Pack
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork

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
  have pn : 2 ≤ p.geo.pLen ∧ p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega
  have qn : 2 ≤ p.geo.qLen ∧ p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega
  have h5 := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
  have packedBound := p.geo.small_bound (d := packed) (n := 2 * p.geo.pLen + p.geo.qLen)
    (by decide) (by unfold arithmeticBytes; omega)
  have hh := p.geo.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  have src (d : Nat) (bs : List Byte) (hd : d + bs.length ≤ packed)
      (bytes : Spec.Rsa.bytesAt s.mem (off p.geo.B d) bs.length = bs) :
      Src s (off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) (off p.geo.B d) bs := by
    have bound : d + bs.length ≤ usedBytes p.geo.pLen := by omega
    apply arena_source h.scratch bound (by unfold packed at hd; omega) bytes
    exact p.geo.parts_disjoint bound packedBound (Or.inl hd)
  obtain ⟨V, R⟩ := h.rep
  have call := pack_ok h.layout R hp hq hg ⟨pn.1, qn.1, by omega⟩
  rw [h5] at call
  refine WP.mono (call
    (src VG.Impl.Dsa.Generation.Layout.p pb (by rw [hp]; unfold VG.Impl.Dsa.Generation.Layout.p packed; omega) (by simpa only [hp] using bp))
    (src q qb (by rw [hq]; unfold q packed; omega) (by simpa only [hq] using bq))
    (src g gb (by rw [hg]; unfold g packed; omega) (by simpa only [hg] using bg))
    (by intro i hi; rw [off_off]; exact h.scratch.region (by omega) (by decide))
    (p.geo.frame_part packedBound) (p.geo.parts_disjoint hh packedBound (Or.inl (by decide))))
    fun t ⟨bytes, Lt, Rt, ft, kt⟩ => ?_
  have ff : Frame p.changed s.mem t.mem := by
    apply GenerationContext.frame_parts ft
    intro r hr
    rcases List.mem_singleton.mp hr with rfl
    exact ⟨⟨p.geo.B, usedBytes p.geo.pLen⟩, by simp [GenerationContext.changed], p.geo.part_sub packedBound⟩
  exact ⟨h.frame Lt ⟨V, Rt⟩ (fun _ _ => rfl) ff kt.2.1 kt.2.2, bytes, ff, kt.2.1, kt.2.2⟩

end VG.Proof.Dsa.X86_64.Generation
