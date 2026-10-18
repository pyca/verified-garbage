module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodePadding
public import VerifiedGarbage.Proof.RsaPkcs1Sig.ByteMath
public import VerifiedGarbage.Proof.Bignum.X86.ByteOps
import all Init.Data.Nat.Bitwise.Basic

/-! # Exact memory and register effects of one byte-copy step -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86
open VG VG.X86 VG.X86.Wp VG.Impl.RsaPkcs1Sig.X86 VG.Proof.Mont.X86 VG.Proof.Bignum.X86

theorem copyStep_ok (s : State) (src dst : Addr)
    (ps : s.ea ⟨.esi, 0⟩ = src) (pd : s.ea ⟨.edi, 0⟩ = dst)
    (hr : InRegions (s.rd ++ s.wr) src 1) (hw : InRegions s.wr dst 1) :
    WP isa (.block copyStep) s fun t =>
      t.mem = s.mem.writeW dst (s.mem src) ∧
      t.gpr .edi = s.gpr .edi + 1 ∧ t.gpr .esi = s.gpr .esi + 1 ∧
      t.gpr .ebp = s.gpr .ebp - 1 ∧ t.zf = some (s.gpr .ebp - 1 == 0) ∧
      Keeps [.eax, .edi, .esi, .ebp] s t := by
  unfold copyStep
  refine wp_loadByte ps hr fun s₁ u₁ => ?_
  refine wp_storeByte (a := dst)
    (by change (s₁.gpr .edi + BitVec.ofNat 32 0).setWidth 64 = dst
        rw [u₁.other .edi (by decide)]; exact pd)
    (by rw [u₁.wr]; exact hw) fun s₂ u₂ => ?_
  refine wp_addS rfl fun s₃ u₃ _ => ?_
  refine wp_addS rfl fun s₄ u₄ _ => ?_
  refine wp_subi fun t u₅ _ zt => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    change s.mem.writeW dst ((s₁.gpr .eax).setWidth 8) = _
    rw [u₁.gpr, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq]
  · rw [u₅.other .edi (by decide), u₄.gpr, u₃.other .edi (by decide),
      u₂.gpr, u₁.other .edi (by decide)]
  · rw [u₅.other .esi (by decide), u₄.other .esi (by decide), u₃.gpr,
      u₂.gpr, u₁.other .esi (by decide)]
  · rw [u₅.gpr, u₄.other .ebp (by decide), u₃.other .ebp (by decide),
      u₂.gpr, u₁.other .ebp (by decide)]
  · rw [zt, u₄.other .ebp (by decide), u₃.other .ebp (by decide),
      u₂.gpr, u₁.other .ebp (by decide)]
  · exact ((((u₁.keeps.mono (by decide)).trans (u₂.keeps _)).widen u₃.keeps).widen
      u₄.keeps).widen u₅.keeps


end VG.Proof.RsaPkcs1Sig.X86
