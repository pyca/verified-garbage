module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext

/-! # Ordinary disjoint input and output buffers establish native import access -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Import
open VG VG.X86 VG.Proof.Mont

theorem contains_offset {r : Region} {a : Addr} {length offset bytes : Nat}
    (H : r.Contains a length) (fit : offset + bytes ≤ length) :
    r.Contains (off a offset) bytes := by
  change (a - r.base).toNat + length ≤ r.len at H
  change (a + BitVec.ofNat 64 offset - r.base).toNat + bytes ≤ r.len
  have rearrange : a + BitVec.ofNat 64 offset - r.base = (a - r.base) + BitVec.ofNat 64 offset := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.add_comm (BitVec.ofNat 64 offset) (-r.base), ← BitVec.add_assoc]
  rw [rearrange, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := Nat.mod_le ((a - r.base).toNat + offset % 2 ^ 64) (2 ^ 64)
  have := Nat.mod_le offset (2 ^ 64)
  omega

theorem context_of_regions {g : Geometry} {s : State} (positive : 0 < g.count)
    (sourceFit : g.src.toNat + 4 * g.count ≤ 2 ^ 32) (destFit : g.dst.toNat + 4 * g.count ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (g.src.setWidth 64) (4 * g.count))
    (writable : InRegions s.wr (g.dst.setWidth 64) (4 * g.count))
    (separate : g.sourceRegion.Disjoint g.destRegion) : Context g s := by
  refine ⟨positive, sourceFit, destFit, ?_, ?_, separate⟩
  · intro i index
    obtain ⟨r, mem, access⟩ := readable
    exact ⟨r, mem, contains_offset access (by omega)⟩
  · intro i index
    obtain ⟨r, mem, access⟩ := writable
    exact ⟨r, mem, contains_offset access (by omega)⟩

end VG.Proof.RsaKeyGen.X86.Import
