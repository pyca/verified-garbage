module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext
import VerifiedGarbage.Proof.Dsa.X86.KeyCopy
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Output
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers
import VerifiedGarbage.Proof.Dsa.X86.Generation.OutputArguments

/-! # Copy the accepted serialized domain to the caller -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.X86.Generation

theorem outputCopy_ok {P : SearchContextPlan} {W : Nat → BitVec 32} {s : State} {len : Nat}
    (R : SearchContext P W s) (positive : 0 < len) (small : len < 2 ^ 32)
    (length : W 7 = BitVec.ofNat 32 len) (sourceRoom : packed + len ≤ usedBytes P.geometry.pLen)
    (outRoom : (W 6).toNat + len ≤ 2 ^ 32)
    (apart : (P.geometry.part packed len).Disjoint ⟨(W 6).setWidth 64, len⟩)
    (write : ∀ i, i < len → InRegions s.wr (off ((W 6).setWidth 64) i) 1) :
    WP isa outputCopy s fun t => t.gpr .eax = 1 ∧
      Spec.Rsa.bytesAt t.mem ((W 6).setWidth 64) len = Spec.Rsa.bytesAt s.mem (off P.geometry.base packed) len ∧
      Frame [⟨(W 6).setWidth 64, len⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := by
  have ss : packed < usedBytes P.geometry.pLen := by omega
  have parent := (R.fixed 5 (by decide) (by decide)).trans P.parent
  unfold outputCopy
  refine WP.seq (WP.mono (outputArgs_ok R.arena.frame R.representation) fun a ⟨si, dx, cx, bx, mem, Ka⟩ => ?_)
  rw [parent] at si
  have Ra := R.congr mem Ka (by decide)
  refine WP.seq (WP.mono (keyCopy_ok positive small (P.geometry.pointer_fit ss sourceRoom) outRoom
    (by rw [P.geometry.pointer_addr ss]; exact apart) si dx (cx.trans length) bx
    (by intro i hi; exact Ra.arena.readPointer ss sourceRoom i 1 (by omega))
    (by intro i hi; rw [Ka.2.2]; exact write i hi)) fun b I => ?_)
  refine wp_movS rfl fun t bt _ => WP.block_nil ?_
  have bytes := copied_unmasked I
  rw [P.geometry.pointer_addr ss, mem] at bytes
  have O := copyOutside_frame I.mem
  rw [mem] at O
  exact ⟨bt.gpr, by rw [bt.mem]; exact bytes, by rw [bt.mem]; exact O,
    (Ka.mono (by decide)).trans ((I.keeps.mono (by decide)).trans (bt.keeps.mono (by decide)))⟩
end VG.Proof.Dsa.X86.Generation
