module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Exponent
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ExponentMath
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! Store the reviewed window shift and the masks for its three extra halvings. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Keep slot)
open VG.Impl.Rsa.X86.KeyRt (Lay)

theorem exponent_sigma {L : Lay} {s : State} {base : Addr} {bytes len count : Nat}
    (h : RtWs L s base bytes len count) :
    WP isa (.block Impl.Dsa.X86.Generation.exponentSigma) s fun t =>
      RtWs L t base bytes len count ∧ Keep base (kw len) [] [32] s.mem t.mem ∧
      slot t.mem base 32 = VG.Proof.RsaKeyGen.sigOf (slot s.mem base 20) ∧ Keeps [.eax] s t := by
  have head : 160 ≤ bytes := h.ws.hdr_le
  unfold Impl.Dsa.X86.Generation.exponentSigma
  refine wp_movS (readSrc_sc h.ws.workspace (d := 20) (by omega)) fun a A _ =>
    wp_subS rfl fun b B _ => wp_logicS (Or.inl rfl) rfl fun c C => wp_addS rfl fun d D _ => ?_
  have value : d.gpr .eax = sigmaWord (s.mem.readW (off base 20) 32) := by
    rw [D.gpr, C.gpr, B.gpr, A.gpr]
    rfl
  have K : Keeps [.eax] s d := ((A.keeps.trans B.keeps).trans C.keeps).trans D.keeps
  have mem : d.mem = s.mem := D.mem.trans (C.mem.trans (B.mem.trans A.mem))
  have hd := h.keep K (by decide) (by decide) (by rw [mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (storeSlot_ok hd (d := 32) (by decide) .eax) ?_
  rintro t ⟨ht, F, sigma, K'⟩
  rw [mem] at F
  rw [value, sigma_word_value] at sigma
  exact ⟨ht, F, sigma, K.trans (K'.mono (by simp))⟩

theorem exponent_mask {L : Lay} {s : State} {base : Addr} {bytes len count sigma threshold : Nat}
    (h : RtWs L s base bytes len count) (value : slot s.mem base 32 = sigma)
    (hs : 1 ≤ sigma ∧ sigma ≤ 4) (ht : 1 ≤ threshold ∧ threshold ≤ 3) :
    WP isa (.block (Impl.Dsa.X86.Generation.exponentMask threshold)) s fun t =>
      RtWs L t base bytes len count ∧ Keep base (kw len) [] [28] s.mem t.mem ∧
      slot t.mem base 28 = (decide (threshold < sigma)).toNat ∧ Keeps [.eax] s t := by
  have head : 160 ≤ bytes := h.ws.hdr_le
  have input : s.mem.readW (off base 32) 32 = BitVec.ofNat 32 sigma := by
    apply BitVec.eq_of_toNat_eq
    change slot s.mem base 32 = _
    rw [value, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold Impl.Dsa.X86.Generation.exponentMask
  refine wp_movS (readSrc_sc h.ws.workspace (d := 32) (by omega)) fun a A _ =>
    wp_subS rfl fun b B _ => wp_shr (by decide) fun c C _ => wp_logicS (Or.inr rfl) rfl fun d D => ?_
  have word : d.gpr .eax = BitVec.ofNat 32 (decide (threshold < sigma)).toNat := by
    rw [D.gpr, C.gpr, B.gpr, A.gpr, input]
    change greaterWord (BitVec.ofNat 32 sigma) threshold = _
    exact greater_word_value hs ht
  have K : Keeps [.eax] s d := ((A.keeps.trans B.keeps).trans C.keeps).trans D.keeps
  have mem : d.mem = s.mem := D.mem.trans (C.mem.trans (B.mem.trans A.mem))
  have hd := h.keep K (by decide) (by decide) (by rw [mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (storeSlot_ok hd (d := 28) (by decide) .eax) ?_
  rintro t ⟨H, F, bit, K'⟩
  rw [mem] at F
  rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Bool.toNat_le (decide (threshold < sigma)); omega)] at bit
  exact ⟨H, F, bit, K.trans (K'.mono (by simp))⟩

end VG.Proof.Dsa.X86.Generation
