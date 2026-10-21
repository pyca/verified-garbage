module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportRegions
import VerifiedGarbage.Proof.Framework.Offset

/-! # Any native workspace array can import one disjoint public source region -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Import
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem context_workspace {s : State} {base : Addr} {size out n : Nat} {src : BitVec 32}
    (S : Scr s base size) (positive : 0 < n) (space : out + 4 * n ≤ size)
    (sourceFit : src.toNat + 4 * n ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (src.setWidth 64) (4 * n))
    (separate : (⟨src.setWidth 64, 4 * n⟩ : Region).Disjoint ⟨base, size⟩) :
    Context ⟨src, s.gpr .edi + BitVec.ofNat 32 out, n⟩ s := by
  have outBound : out < 2 ^ 32 := by have := S.nowrap; omega
  have destAddress : (s.gpr .edi + BitVec.ofNat 32 out).setWidth 64 = off base out := S.ea (by omega)
  refine context_of_regions positive sourceFit ?_ readable ?_ ?_
  · change (s.gpr .edi + BitVec.ofNat 32 out).toNat + 4 * n ≤ 2 ^ 32
    rw [BitVec.toNat_add, S.edi_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt outBound,
      Nat.mod_eq_of_lt (by have := S.nowrap; omega)]
    have := S.nowrap
    omega
  · change InRegions s.wr ((s.gpr .edi + BitVec.ofNat 32 out).setWidth 64) (4 * n)
    rw [destAddress]
    exact S.write space
  · change (⟨src.setWidth 64, 4 * n⟩ : Region).Disjoint
      ⟨(s.gpr .edi + BitVec.ofNat 32 out).setWidth 64, 4 * n⟩
    rw [destAddress]
    exact separate.sub_right (Offset.sub_base base space)

end VG.Proof.RsaKeyGen.X86.Import
