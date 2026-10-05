import VerifiedGarbage.Proof.RsaPss.X86_64.SignCorrect

/-!
# RSASSA-PSS signing on x86-64: the calling convention

`sign_correct`: `sign` meets `signK` and keeps the callee-saved registers,
its return address (which only its frame and calls are below) and MXCSR's
control bits (no instruction loads MXCSR).
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.Rsa.X86_64 (chkContract)

variable {H : Impl.Pbkdf2.Md.X86_64.Hash} (hH : Pbkdf2.Md.X86_64.HashOK H) (K : Pbkdf2.Md.X86_64.Callees H)

include hH K in
theorem sign_spAll {privN : String} {privC : Prog isa} (hC : SpSafe privC) :
    (sign H privN privC).allInstrs (fun i => !isa.writesSp i) = true := by
  have he := signEnc_safe hH K
  rw [safeI_eq, allInstrs_and, Bool.and_eq_true] at he
  have hC' : privC.allInstrs (fun i => !isa.writesSp i) = true := by
    rw [Code.allInstrs_eq]; exact List.all_eq_true.mpr fun i hi => by rw [hC i hi]; rfl
  simp only [sign, signBody, seqs, signMain, Code.allInstrs, he.1, hC', rec_all, List.all_append,
    signFail, emLen, byteLoop, step, Bool.and_true, Bool.true_and]
  rfl

include hH K in
theorem sign_sp {privN : String} {privC : Prog isa} (hC : SpSafe privC) :
    SpSafe (sign H privN privC) := by
  have h := sign_spAll hH K (privN := privN) hC
  rw [Code.allInstrs_eq] at h
  intro i hi
  simpa using List.all_eq_true.mp h i hi

include K in
theorem sign_xd {privN : String} {privC : Prog isa} (hd : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes) :
    (sign H privN privC).x86_64Depth ≤ signStack := by
  simp only [sign, signBody, seqs, signMain, Code.x86_64Depth, signEnc_xd K, signFail, emLen, byteLoop,
    X86_64.Instr.frameBytes, Nat.zero_max, Nat.max_zero]
  have h8 : max 8 (privC.x86_64Depth + 8) ≤ privC.x86_64Depth + 8 :=
    Nat.max_le.mpr ⟨Nat.le_add_left 8 _, Nat.le_refl _⟩
  unfold signStack Rsa.X86_64.stackBytes frameBytes at *
  omega

include hH K in
theorem sign_correct (lk : Pbkdf2.Md.X86_64.MgfLink H hH) {privN : String} {privC : Prog isa}
    (hv : ∀ s, chkContract.pre s → ∃ t s', Exec isa privC s t s' ∧ abiPreserved s s' ∧ chkContract.post s s')
    (hC : SpSafe privC) (hdC : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes)
    (s : State) (h : (signK lk.G).pre s) :
    ∃ t s', Exec isa (sign H privN privC) s t s' ∧ abiPreserved s s' ∧ (signK lk.G).post s s' := by
  have hp := SPre.of lk.G h
  have hW := X86_64.WP.stackFrame (sign_sp hH K (privN := privN) hC) (by have := sign_xd K (privN := privN) hdC; unfold signStack Rsa.X86_64.stackBytes at this; omega)
    (sign_ok hH K lk hv hC hdC h)
  obtain ⟨t, s', he, ⟨hcs, hpost, hmx⟩, hf⟩ := hW
  refine ⟨t, s', he, ⟨hcs, ?_, hmx⟩, hpost⟩
  -- The return address.
  have hd := sign_xd K (privN := privN) hdC
  refine Mem.readW_congr fun i hi => hf _ fun r hr hc => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [hp.hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dRo _ (Offset.contains_base _ (by omega) (by omega)) hc
    · exact hp.dRs _ (Offset.contains_base _ (by omega) (by omega)) hc
  · simp only [List.mem_singleton] at hr; subst hr
    have := hp.sp1; have := hp.sp2
    exact Offset.base_disjoint_below (s.gpr .rsp) (n := (sign H privN privC).x86_64Depth) (k := 8)
      (by unfold signStack at *; omega) _ (Offset.contains_base _ (by omega) (by omega)) hc

end VG.Proof.RsaPss.X86_64
