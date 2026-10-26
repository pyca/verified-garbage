module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PackPartCT
import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
public import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PackPart
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArenaSource
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryWork
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Component packing preserves the native generation context -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def GenerationMemoryBefore (p : GenerationContext) (s : State) : Prop := ∃ W, GenerationMemory p W s

def GenerationContext.packPublic (p : GenerationContext) : PackPublic := ⟨p.geo.B, p.geo.F, p.geo.hash⟩

theorem generationMemory_pack {p : GenerationContext} {s : State} (h : GenerationMemoryBefore p s) :
    PackBefore p.packPublic s := by
  obtain ⟨W, h⟩ := h
  obtain ⟨V, R⟩ := h.rep
  exact ⟨h.layout, V, W, R, (h.slots 5 (by simp [generationSlots])).trans p.baseSlot⟩

theorem packPart_memory {p : GenerationContext} {s : State} (h : GenerationMemoryBefore p s)
    (src dst len : Nat) (hsrc : src + len ≤ packed) (hdst : packed ≤ dst)
    (hend : dst + len ≤ packed + 800) (hlen : 2 ≤ len ∧ len ≤ 384) :
    WP isa (Impl.Dsa.AArch64.Generation.packPart src dst len) s (GenerationMemoryBefore p) := by
  obtain ⟨W, h⟩ := h
  obtain ⟨V, R⟩ := h.rep
  have hb := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
  have srcBound := p.geo.small_bound (d := src) (n := len)
    (by change src ≤ 40960; unfold packed at hsrc; omega) (by change len ≤ 12288; omega)
  have dstBound := p.geo.small_bound (d := dst) (n := len)
    (by change dst ≤ 40960; unfold packed at hend; omega) (by change len ≤ 12288; omega)
  have hashBound := p.geo.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  let bs := Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B src) len
  have bl : bs.length = len := by simp [bs, Spec.Rsa.bytesAt]
  have source : Src s (VG.Proof.Bignum.off p.geo.B dst) len (VG.Proof.Bignum.off p.geo.B src) bs := by
    apply arena_source h.scratch
    · rw [bl]; exact srcBound
    · rw [bl]; omega
    · rw [bl]
    · simpa only [bl, GenerationGeometry.part] using
        p.geo.parts_disjoint srcBound dstBound (Or.inl (by omega))
  have call := packPart_ok (src := src) (dst := dst) (bs := bs) h.layout R
    (by unfold packed at hsrc; omega) (by unfold packed at hend; omega)
    (by rw [bl]; omega)
  rw [hb] at call
  have run := call source.rd (fun i hi => by
    rw [VG.Proof.Bignum.off_off]; exact h.scratch.region (by rw [bl] at hi; omega) (by decide))
    (fun i hi => by simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] using source.val i hi)
    (fun i hi j hj heq => by
      have outside := source.out i hi
      change len ≤ ofs (VG.Proof.Bignum.off p.geo.B dst) (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.geo.B src) i) at outside
      rw [heq] at outside
      rw [bl] at hj
      simp only [ofs, VG.Proof.Bignum.off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : j < 2 ^ 64)] at outside
      omega)
    (by simpa only [bl, GenerationGeometry.part] using p.geo.frame_part dstBound)
    (by simpa only [bl, GenerationGeometry.part, GenerationGeometry.hash] using
      p.geo.parts_disjoint hashBound dstBound (Or.inl (by unfold VG.Impl.Dsa.Generation.Layout.hash oRsa packed at *; omega)))
  rw [bl] at run
  refine WP.mono run fun t ⟨_, Lt, Rt, ft, kt⟩ => ?_
  have ff : Frame p.changed s.mem t.mem := by
    apply GenerationContext.frame_parts ft
    intro r hr
    rcases List.mem_singleton.mp hr with rfl
    exact ⟨⟨p.geo.B, usedBytes p.geo.pLen⟩, by simp [GenerationContext.changed], p.geo.part_sub dstBound⟩
  exact ⟨W, h.frame Lt ⟨V, Rt⟩ (fun _ _ => rfl) ff kt.rd kt.wr⟩

end VG.Proof.Dsa.AArch64.Generation
