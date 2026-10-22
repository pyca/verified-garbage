module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.HalvingState
public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! RSA's word-copy and halving operations prepare the masked update. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Keep num slot)
open VG.Impl.Rsa.X86.KeyRt (Lay)

theorem halving_temp {L : Lay} {s : State} {base : Addr} {bytes len count value twos remaining : Nat}
    (h : HalvingState L base bytes len count value twos remaining s) (arrays : 2 ≤ count) :
    WP isa (.seq (Impl.Rsa.X86.KeyRt.copy L 1 0)
      (.seq (.block [.mov .ebx (.imm 0)]) (Impl.Rsa.X86.KeyRt.half L 1))) s fun t =>
      HalvingTemp L base bytes len count value twos remaining t ∧
      Keep base (kw len) [1] [] s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.seq (WP.mono (copy_ok h.workspace (by omega : 1 < count) (by omega : 0 < count) (by decide)) ?_)
  rintro u ⟨hu, F, copied, K, _⟩
  rw [h.value] at copied
  refine WP.seq (wp_movS rfl fun v V _ => WP.block_nil ?_)
  have hv := hu.keep V.keeps (by decide) (by decide) (by rw [V.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (half_ok hv (j := 1) (by omega) (by rw [V.gpr]; decide)) ?_
  rintro t ⟨ht, F', half, K'⟩
  rw [V.mem, copied, V.gpr] at half
  change num t.mem base (kw len) 1 = (value + 2 ^ (32 * kw len) * 0) / 2 at half
  rw [Nat.mul_zero, Nat.add_zero] at half
  rw [V.mem] at F'
  have frame : Keep base (kw len) [1] [] s.mem t.mem := F.trans F'
  refine ⟨⟨⟨ht, ?_, ?_, ?_⟩, half⟩, frame,
    ((K.mono (by decide)).trans (V.keeps.mono (by decide))).trans (K'.mono (by decide))⟩
  · exact (frame.num (by simp) (by simp) (h.workspace.ws.fit64 (by omega : 0 < count))).trans h.value
  · exact (frame.slot (by decide) (by simp)).trans h.twos
  · exact (frame.slot (by decide) (by simp)).trans h.remaining

end VG.Proof.Dsa.X86.Generation
