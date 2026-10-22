module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.WitnessContext
public import VerifiedGarbage.Proof.Dsa.X86.CoreLoad
import VerifiedGarbage.Proof.Dsa.X86.LocalOperand
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! Load a truncated witness through the existing padded big-endian loader. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

private theorem witness_buffer_bound {n len : Nat} (upper : n ≤ 48) (hlen : len ≤ 8 * n) :
    Layout.witness + len ≤ 40960 ∧ contextBytes n ≤ Layout.witness := by
  simp only [Layout.witness, contextBytes, slot, stride]
  omega

theorem load_witness {s : State} {base : Addr} {bytes n len candidate : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (C : WitnessContext base n candidate s)
    (upper : n ≤ 48) (lower : 4 ≤ len) (length : len ≤ 8 * n) (aligned : len % 4 = 0) :
    WP isa (loadWitness n len) s fun t =>
      WitnessContext base n candidate t ∧
      wordsVal t.mem base (slot n 5) n =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off base Layout.witness) len) ∧
      Outside base (slot n 5) (8 * n) s.mem t.mem ∧ Keeps loadClob s t := by
  have buffers := witness_buffer_bound upper length
  have source := VG.Proof.Dsa.X86.localReady scr (by omega)
    (Nat.le_trans buffers.1 capacity) buffers.2
  have destination := slot_bound (n := n) (i := 5) (by decide)
  have fit : slot n 5 + 8 * n ≤ bytes := by
    have size := C.parent.size_le
    have cap : montgomeryBytes ≤ bytes := by unfold montgomeryBytes; omega
    unfold stride at destination
    omega
  refine WP.mono (VG.Proof.Dsa.X86.coreLoad_ok scr (by
    unfold VG.Impl.Dsa.X86.Layout.saved; omega) fit lower length aligned source.toReadableComponent
    (source.apart.sub_right (Offset.sub_base base (by unfold stride at destination; omega))))
    fun t ⟨value, K, F⟩ => ?_
  rw [VG.Proof.Dsa.X86.local_pointer scr (by omega) (Nat.le_trans buffers.1 capacity),
    VG.Proof.Dsa.decodeBE_os2ip] at value
  have s05 := slot_le (n := n) (i := 0) (j := 5) (by decide)
  have parent := C.parent.outside_keep K (by decide) (by decide) F
    (.inl (by unfold stride at s05; omega)) (by have := slot_header n 5; omega)
  have same : ∀ j, j = 1 ∨ j = 3 ∨ j = 4 →
      wordsVal t.mem base (slot n j) n = wordsVal s.mem base (slot n j) n := by
    intro j hj
    have apart := slot_le (n := n) (i := j) (j := 5) (by omega)
    have bound := slot_bound (n := n) (i := j) (by omega)
    have size := C.parent.size_le
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact F.val32 (.inl (by unfold stride at apart; omega)) (by
      unfold stride at bound; unfold montgomeryBytes at size; omega)
  exact ⟨⟨parent, (same 3 (.inr (.inl rfl))).trans C.ordinary,
    (same 4 (.inr (.inr rfl))).trans C.square, (same 1 (.inl rfl)).trans C.ceiling⟩, value, F, K⟩

end VG.Proof.Dsa.X86.Generation
