module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Output
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Generation.OutputZeroLoop

/-! # Clear every output byte on failure and return zero -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem outputZero_ok {s : State} {base : Addr} {W : Nat → BitVec 32} {len : Nat}
    (F : SearchFrame s base) (R : FrameWords s.mem base W)
    (positive : 0 < len) (small : len < 2 ^ 32) (length : W 7 = BitVec.ofNat 32 len)
    (room : (W 6).toNat + len ≤ 2 ^ 32)
    (write : ∀ i, i < len → InRegions s.wr (off ((W 6).setWidth 64) i) 1) :
    WP isa outputZero s fun t => t.gpr .eax = 0 ∧ Frame [⟨(W 6).setWidth 64, len⟩] s.mem t.mem ∧
      Spec.Rsa.bytesAt t.mem ((W 6).setWidth 64) len = List.replicate len 0 ∧ Keeps [.eax, .ecx, .esi] s t := by
  unfold outputZero
  refine WP.seq (wp_movS (F.readWord R (by decide : 6 < 37)) fun a sa _ => ?_)
  have Fa := F.keeps sa.keeps (by decide)
  have Ra : FrameWords a.mem base W := by rw [sa.mem]; exact R
  refine wp_movS (Fa.readWord Ra (by decide : 7 < 37)) fun b ab _ =>
    wp_movS rfl fun c bc _ => WP.block_nil ?_
  have K : Keeps [.eax, .ecx, .esi] s c :=
    (sa.keeps.mono (by decide)).trans ((ab.keeps.mono (by decide)).trans (bc.keeps.mono (by decide)))
  have mem : c.mem = s.mem := bc.mem.trans (ab.mem.trans sa.mem)
  apply outputZeroLoop_ok positive small room write
  exact ⟨by rw [bc.other _ (by decide), ab.other _ (by decide), sa.gpr, BitVec.add_zero],
    by rw [bc.other _ (by decide), ab.gpr, length, Nat.sub_zero], bc.gpr,
    by rw [mem]; exact Frame.refl _ _, by intro i hi; omega, K⟩
end VG.Proof.Dsa.X86.Generation
