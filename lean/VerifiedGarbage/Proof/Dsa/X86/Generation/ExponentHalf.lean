module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ExponentScalar
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HalvingTemp

/-! Each extra exponent halving reuses RSA's existing masked array selection. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Keep num slot)
open VG.Impl.Rsa.X86.KeyRt (Lay)

theorem exponent_half {L : Lay} {s : State} {base : Addr} {bytes len count value sigma threshold : Nat}
    (h : RtWs L s base bytes len count) (arrays : 2 ≤ count)
    (current : num s.mem base (kw len) 0 = value) (shift : slot s.mem base 32 = sigma)
    (hs : 1 ≤ sigma ∧ sigma ≤ 4) (ht : 1 ≤ threshold ∧ threshold ≤ 3) :
    WP isa (Impl.Dsa.X86.Generation.exponentHalf L threshold) s fun t =>
      RtWs L t base bytes len count ∧ Keep base (kw len) [0, 1] [28] s.mem t.mem ∧
      num t.mem base (kw len) 0 = (if threshold < sigma then value / 2 else value) ∧
      slot t.mem base 32 = sigma ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold Impl.Dsa.X86.Generation.exponentHalf
  refine WP.seq (WP.mono (exponent_mask h shift hs ht) ?_)
  rintro u ⟨hu, F, bit, K⟩
  have currentu := (F.num (j := 0) (by simp) (by decide) (h.ws.fit64 (by omega))).trans current
  have state : HalvingState L base bytes len count value (slot u.mem base 20) (slot u.mem base 56) u :=
    ⟨hu, currentu, rfl, rfl⟩
  refine WP.seq (WP.mono (halving_temp state arrays) ?_)
  rintro v ⟨hv, F', K'⟩
  have bitv := (F'.slot (e := 28) (by decide) (by simp)).trans bit
  refine WP.mono (sel_ok hv.workspace (o := 0) (a := 0) (b := 1) (sl := 28)
    (by omega) (by omega) (by omega) (by decide) (by rw [bitv]; exact Bool.toNat_le _) (Or.inr (by decide))) ?_
  rintro t ⟨H, F'', selected, K''⟩
  rw [bitv, hv.value, hv.temp] at selected
  have final : num t.mem base (kw len) 0 = if threshold < sigma then value / 2 else value := by
    by_cases more : threshold < sigma
    · simpa only [more, decide_true, Bool.toNat_true, show ¬ (1 : Nat) = 0 by decide, ite_false, ite_true] using selected
    · simpa only [more, decide_false, Bool.toNat_false, ite_true, ite_false] using selected
  have frame : Keep base (kw len) [0, 1] [28] s.mem t.mem := (F.join F' (js := [0, 1]) (ds := [28])).join F''
  exact ⟨H, frame, final, (frame.slot (by decide) (by simp)).trans shift,
    ((K.mono (by decide)).trans K').trans K''⟩

end VG.Proof.Dsa.X86.Generation
