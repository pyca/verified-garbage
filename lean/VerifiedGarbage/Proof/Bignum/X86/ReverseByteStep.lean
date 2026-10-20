module

public import VerifiedGarbage.Impl.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Bignum.X86.ByteOps
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Exact memory and register effects of one endian-conversion step -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem reverseByteStep_ok (s : State) (src dst : Addr)
    (ps : s.ea ⟨.esi, 0⟩ = src) (pd : s.ea ⟨.ebx, 0⟩ = dst)
    (hr : InRegions (s.rd ++ s.wr) src 1) (hw : InRegions s.wr dst 1) :
    WP isa (.block reverseByteStep) s fun t =>
      t.mem = s.mem.writeW dst (s.mem src) ∧
      t.gpr .ebx = s.gpr .ebx + 1 ∧ t.gpr .esi = s.gpr .esi - 1 ∧
      t.gpr .ecx = s.gpr .ecx - 1 ∧ t.zf = some (s.gpr .ecx - 1 == 0) ∧
      Keeps [.eax, .ebx, .esi, .ecx] s t := by
  unfold reverseByteStep
  refine wp_loadByte ps hr fun s₁ u₁ => ?_
  refine wp_storeByte (a := dst)
    (by change (s₁.gpr .ebx + BitVec.ofNat 32 0).setWidth 64 = dst
        rw [u₁.other .ebx (by decide)]; exact pd)
    (by rw [u₁.wr]; exact hw) fun s₂ u₂ => ?_
  refine wp_addS rfl fun s₃ u₃ _ => ?_
  refine wp_subS rfl fun s₄ u₄ _ => ?_
  refine wp_subS rfl fun s₅ u₅ _ => ?_
  refine wp_cmpS rfl fun t ft zt => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ft.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    change s.mem.writeW dst ((s₁.gpr .eax).setWidth 8) = _
    rw [u₁.gpr, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq]
  · rw [ft.gpr, u₅.other .ebx (by decide), u₄.other .ebx (by decide), u₃.gpr,
      u₂.gpr, u₁.other .ebx (by decide)]
  · rw [ft.gpr, u₅.other .esi (by decide), u₄.gpr, u₃.other .esi (by decide),
      u₂.gpr, u₁.other .esi (by decide)]
  · rw [ft.gpr, u₅.gpr, u₄.other .ecx (by decide), u₃.other .ecx (by decide),
      u₂.gpr, u₁.other .ecx (by decide)]
  · rw [zt, u₅.gpr, u₄.other .ecx (by decide), u₃.other .ecx (by decide),
      u₂.gpr, u₁.other .ecx (by decide)]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero]
  · exact (((((u₁.keeps.mono (by decide)).trans (u₂.keeps _)).widen u₃.keeps).widen
      u₄.keeps).widen u₅.keeps).trans (ft.keeps _)

end VG.Proof.Bignum.X86
