module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Entry
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Generation.OutputZeroLoop

/-! # Initialize the complete working arena before using search temporaries -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86.Generation
open VG.Impl.Dsa.Generation.Layout

theorem clearScratch_ok {s : State} {base : Addr} {W : Nat → BitVec 32} {plen : Nat}
    (F : SearchFrame s base) (R : FrameWords s.mem base W)
    (small : usedBytes plen < 2 ^ 32) (room : (W 5).toNat + usedBytes plen ≤ 2 ^ 32)
    (write : ∀ i, i < usedBytes plen → InRegions s.wr (off ((W 5).setWidth 64) i) 1) :
    WP isa (clearScratch plen) s fun t =>
      Frame [⟨(W 5).setWidth 64, usedBytes plen⟩] s.mem t.mem ∧
      Spec.Rsa.bytesAt t.mem ((W 5).setWidth 64) (usedBytes plen) = List.replicate (usedBytes plen) 0 ∧
      Keeps [.eax, .ecx, .esi] s t := by
  have positive : 0 < usedBytes plen := by unfold usedBytes domainCheck; omega
  unfold clearScratch
  refine WP.seq (wp_movS (F.readWord R (by decide : 5 < 37)) fun a sa _ =>
    wp_movS rfl fun b ab _ => wp_movS rfl fun c bc _ => WP.block_nil ?_)
  have K : Keeps [.eax, .ecx, .esi] s c :=
    (sa.keeps.mono (by decide)).trans ((ab.keeps.mono (by decide)).trans (bc.keeps.mono (by decide)))
  have mem : c.mem = s.mem := bc.mem.trans (ab.mem.trans sa.mem)
  refine WP.mono (outputZeroLoop_ok positive small room write ?_) fun _ ⟨_, O, bytes, Kt⟩ => ⟨O, bytes, Kt⟩
  exact ⟨by rw [bc.other _ (by decide), ab.other _ (by decide), sa.gpr, BitVec.add_zero],
    by rw [bc.other _ (by decide), ab.gpr, Nat.sub_zero], bc.gpr,
    by rw [mem]; exact Frame.refl _ _, by intro i hi; omega, K⟩
end VG.Proof.Dsa.X86.Generation
