import VerifiedGarbage.Proof.Bignum.X86_64.PcVerified
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnBase
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost

/-!
# `vg_rsa_public_precompute` on x86-64, by calls of `vg_rsa_mont_mul`
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Bignum.X86_64.MontFn

theorem precompute_implies8 : pcContract.Implies (Spec.Rsa.publicPrecomputeContract abi 8) where
  pre := by
    intro s h
    sig_pre [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, pcContract, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, pcContract, List.append_eq]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, pcContract, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, pcContract, List.append_eq] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9⟩ := h
    refine ⟨?_, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, pcContract, List.append_eq] [pcSatState] using pcSatState

theorem pc_hpost (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : (Spec.Rsa.publicPrecomputeContract abi 8).pre s)
    (hp : pcContract.post s b) : pcContract.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  have hc := Sig.clear_of_pre hs
  obtain ⟨-, hwr, -, -, -, -, -, -, hn, -⟩ := precompute_implies8.pre s hs
  have hr : (⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have hm : ∀ i < 8 * (s.gpr .rsi).toNat, ¬ (hole (s.gpr .rsp)).Contains (s.gpr .rdi + BitVec.ofNat 64 i) 1 :=
    fun i hi => Clear.wr_miss hc hr (by have := (s.gpr .rdi).isLt; omega) (by omega)
  simp only [pcContract, State.patch_gpr] at hp ⊢
  rw [show (b.patch (hole (s.gpr .rsp)) hv u).mem = overlay (hole (s.gpr .rsp)) hv b.mem from rfl,
    wordsAt_overlay hm]
  exact hp

/-- `vg_rsa_public_precompute` by calls of `vg_rsa_mont_mul`. -/
theorem precompute_fn_verified :
    Verified target (Precompute.code (call "vg_rsa_mont_mul" mulBase)) (Spec.Rsa.publicPrecomputeContract abi 8) :=
  Verified.of_inline (by decide +kernel) (pcCode_correct Mont.fnBase (by decide +kernel))
    (pcCode_constantTime Mont.fnBase) precompute_implies8 (fun _ h => Sig.clear_of_pre h) pc_hpost
    (fun _ _ _ _ h => Sig.rsp_of_pub h)

end VG.Proof.Bignum.X86_64
