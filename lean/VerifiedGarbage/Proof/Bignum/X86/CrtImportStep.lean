module

public import VerifiedGarbage.Proof.Bignum.X86.CrtInputs
public import VerifiedGarbage.Proof.Bignum.X86.CrtImportComponent
public import VerifiedGarbage.Proof.Bignum.X86.CrtSlotFrame

/-! # An imported private component preserves the complete call resources -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Bignum.X86.Crt

theorem importStep_ok {s : State} {base : Addr} {bytes len i dst k : Nat} {args : Nat → BitVec 32}
    (h : Inputs base bytes len args s) (hi : i ∈ componentArguments)
    (hd : dst < 20) (hk : Spec.Rsa.modulusWords len ≤ k) (hk' : k ≤ 2 * Spec.Rsa.modulusWords len) :
    WP isa (importComponent k i (slot (Spec.Rsa.modulusWords len) dst)) s fun t =>
      wordsVal t.mem base (slot (Spec.Rsa.modulusWords len) dst) k =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args i)) (args (i + 1)).toNat) ∧
      Outside base (slot (Spec.Rsa.modulusWords len) dst) (8 * k) s.mem t.mem ∧
      Inputs base bytes len args t ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have dims := h.dimensions
  have bound := slot_bound (n := Spec.Rsa.modulusWords len) hd
  have space := h.space
  have islot : i + 1 < 18 := by
    simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have outputBound : slot (Spec.Rsa.modulusWords len) dst + 8 * k ≤ bytes := by
    unfold stride at bound; omega
  refine WP.mono (importComponent_ok h.scratch (by omega) outputBound (h.positive i hi)
    (by have := h.bounded i hi; omega) (h.stack i (by omega))
    (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h.stack (i + 1) islot)
    (h.fits i hi) (h.readable i hi) (h.apart i hi)) fun t ⟨V, O, K⟩ => ?_
  exact ⟨V, O, h.keep K (by decide) (by decide) (O.mono (by omega) (by omega)), K⟩

end VG.Proof.Bignum.X86.Crt
