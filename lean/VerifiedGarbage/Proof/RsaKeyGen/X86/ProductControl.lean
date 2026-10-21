module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Product
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.Loop

/-! # Public control of the native RSA multiplication rows -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Product
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86

theorem advance_ok {s : State} {i left : Nat}
    (pointer : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (index : i < left) (bound : 4 * left < 2 ^ 32) :
    WP isa (.block (Impl.RsaKeyGen.X86.Product.advance left)) s fun t =>
      t.mem = s.mem ∧
      t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * (i + 1)) ∧
      t.zf = some (decide (i + 1 = left)) ∧
      Keeps [.ebp, .edx] s t := by
  unfold Impl.RsaKeyGen.X86.Product.advance
  refine wp_addS rfl fun u U _ => wp_movS rfl fun v V _ =>
    wp_addS rfl fun w W _ => wp_cmpS rfl fun t T z => WP.block_nil ?_
  have K : Keeps [.ebp, .edx] s t :=
    ((U.keeps.mono (by decide)).widen V.keeps).trans ((W.keeps.mono (by decide)).widen (T.keeps []))
  have P : t.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i) + 4 := by
    rw [T.gpr, W.other _ (by decide), V.other _ (by decide), U.gpr, pointer]
  have D : w.gpr .edx = s.gpr .edi + BitVec.ofNat 32 (4 * left) := by
    rw [W.gpr, V.gpr, U.other _ (by decide)]
  refine ⟨by rw [T.mem, W.mem, V.mem, U.mem], ?_, ?_, K⟩
  · rw [P, K.1 _ (by decide), row_ebp]
  · rw [z, W.other _ (by decide), V.other _ (by decide), U.gpr, pointer, D,
      row_zf _ index bound]

end VG.Proof.RsaKeyGen.X86.Product
