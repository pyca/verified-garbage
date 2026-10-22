module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ExponentScalar
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Half
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops

/-! Restore the candidate and prepare the first exponent halving. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Keep num slot)
open VG.Impl.Rsa.X86.KeyRt (Lay)
open VG.Proof.RsaKeyGen (mrA mrSig)

theorem exponent_start {L : Lay} {s : State} {base : Addr} {bytes len count candidate : Nat}
    (h : RtWs L s base bytes len count) (arrays : 3 ≤ count)
    (current : num s.mem base (kw len) 2 = candidate) (factors : slot s.mem base 20 = mrA candidate) :
    WP isa (Impl.Dsa.X86.Generation.exponentStart L) s fun t =>
      RtWs L t base bytes len count ∧ Keep base (kw len) [0] [32] s.mem t.mem ∧
      num t.mem base (kw len) 0 = candidate / 2 ∧ slot t.mem base 32 = mrSig candidate ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold Impl.Dsa.X86.Generation.exponentStart
  refine WP.seq (WP.mono (exponent_sigma h) ?_)
  rintro a ⟨ha, F, sigma, K⟩
  rw [factors] at sigma
  change slot a.mem base 32 = mrSig candidate at sigma
  have ca := (F.num (j := 2) (by simp) (by decide) (h.ws.fit64 (by omega))).trans current
  refine WP.seq (WP.mono (copy_ok ha (o := 0) (a := 2) (by omega) (by omega) (by decide)) ?_)
  rintro b ⟨hb, F', copied, K', _⟩
  rw [ca] at copied
  refine WP.seq (wp_movS rfl fun c C _ => WP.block_nil ?_)
  have hc := hb.keep C.keeps (by decide) (by decide) (by rw [C.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (half_ok hc (j := 0) (by omega) (by rw [C.gpr]; decide)) ?_
  rintro t ⟨H, F'', half, K''⟩
  rw [C.mem, copied, C.gpr] at half
  change num t.mem base (kw len) 0 = (candidate + 2 ^ (32 * kw len) * 0) / 2 at half
  rw [Nat.mul_zero, Nat.add_zero] at half
  rw [C.mem] at F''
  have frame : Keep base (kw len) [0] [32] s.mem t.mem :=
    (F.join F' (js := [0]) (ds := [32])).join F''
  have shift := (F''.slot (e := 32) (by decide) (by simp)).trans
    ((F'.slot (e := 32) (by decide) (by simp)).trans sigma)
  exact ⟨H, frame, half, shift,
    (((K.mono (by decide)).trans K').trans (C.keeps.mono (by decide))).trans (K''.mono (by decide))⟩

end VG.Proof.Dsa.X86.Generation
