import VerifiedGarbage.Proof.MlKem.X86_64.DecMul
import VerifiedGarbage.Proof.MlKem.X86_64.Lit

/-!
# ML-KEM on x86-64: `vg_mlkem768_decrypt_mul` and `vg_mlkem1024_decrypt_mul`, verified

The proof of `DecMul.lean` for each backend and rank, its constant time,
and its contract implying the shared one of `Spec/MlKem/KpkeMul.lean`.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem decMul_correct {B : Bodies} (hB : BodiesOk B) {k : Nat} (hk : k ≤ 4) (hk0 : 0 < k)
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14] (DecMul.inner B) = true)
    (hctl : ctlOk (decryptMul B k) = true) (s : State) (hs : (decMulK k).pre s) :
    ∃ t s', Exec isa (decryptMul B k) s t s' ∧ abiPreserved s s' ∧ (decMulK k).post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := DecMul.wp_all hs hk hB hk0 hwo
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hg, hpost⟩

theorem decMul_agree {k : Nat} (s₁ s₂ : State) (_ : (decMulK k).pre s₁) (_ : (decMulK k).pre s₂)
    (hp : (decMulK k).pub s₁ s₂) : X86_64.Taint.Agree (X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) s₁ s₂ :=
  X86_64.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2]

theorem vecReduced_zero (p : Addr) (l : Nat) : VecReduced (fun _ => 0) p l := fun _ _ => reduced_zero _

/-- A state satisfying the precondition, for `k ≤ 4`. -/
def decMulSat (k : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x7000 | .rcx => 0xC000 | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 1024 * k⟩, ⟨0x7000, 1024 * k⟩]
  wr := [⟨0x1000, 1024⟩, ⟨0xC000, 4096⟩]

section
variable (B : Bodies)

theorem decMul3_verified (hB : BodiesOk B)
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14] (DecMul.inner B) = true)
    (hctl : ctlOk (decryptMul B 3) = true)
    (hct : ConstantTime isa (decMulK 3).pre (decMulK 3).pub (decryptMul B 3)) :
    Verified X86_64.target (decryptMul B 3) (Spec.MlKem.decryptMulContract 3 X86_64.abi) :=
  Verified.of_correct (decMul_correct hB (by decide) (by decide) hwo hctl) hct
    { pre := by sig_implies_pre [Spec.MlKem.decryptMulContract, Spec.MlKem.decryptMulSig, decMulK, X86_64.abi,
        X86_64.argRegs]
      post := by sig_implies_post [Spec.MlKem.decryptMulContract, Spec.MlKem.decryptMulSig, decMulK, X86_64.abi,
        X86_64.argRegs]
      pub := by sig_implies_pub [Spec.MlKem.decryptMulContract, Spec.MlKem.decryptMulSig, decMulK, X86_64.abi,
        X86_64.argRegs]
      sat := by
        refine ⟨decMulSat 3, ?_⟩
        sig_pre [Spec.MlKem.decryptMulContract, Spec.MlKem.decryptMulSig, decMulK, X86_64.abi, X86_64.argRegs]
        and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact vecReduced_zero _ _
          | (intro a h₁ h₂
             simp only [Region.Contains] at h₁ h₂
             bv_omega) }


theorem decMul4_verified (hB : BodiesOk B)
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14] (DecMul.inner B) = true)
    (hctl : ctlOk (decryptMul B 4) = true)
    (hct : ConstantTime isa (decMulK 4).pre (decMulK 4).pub (decryptMul B 4)) :
    Verified X86_64.target (decryptMul B 4) (Spec.MlKem.decryptMulContract 4 X86_64.abi) :=
  Verified.of_correct (decMul_correct hB (by decide) (by decide) hwo hctl) hct
    { pre := by sig_implies_pre [Spec.MlKem.decryptMulContract, Spec.MlKem.decryptMulSig, decMulK, X86_64.abi,
        X86_64.argRegs]
      post := by sig_implies_post [Spec.MlKem.decryptMulContract, Spec.MlKem.decryptMulSig, decMulK, X86_64.abi,
        X86_64.argRegs]
      pub := by sig_implies_pub [Spec.MlKem.decryptMulContract, Spec.MlKem.decryptMulSig, decMulK, X86_64.abi,
        X86_64.argRegs]
      sat := by
        refine ⟨decMulSat 4, ?_⟩
        sig_pre [Spec.MlKem.decryptMulContract, Spec.MlKem.decryptMulSig, decMulK, X86_64.abi, X86_64.argRegs]
        and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact vecReduced_zero _ _
          | (intro a h₁ h₂
             simp only [Region.Contains] at h₁ h₂
             bv_omega) }

end

theorem decMulSse3_ct : ConstantTime isa (decMulK 3).pre (decMulK 3).pub (decryptMul .sse 3) :=
  VG.Taint.constantTime (A := taint) _ decMul_agree (by taint_decide)

theorem decMulSse4_ct : ConstantTime isa (decMulK 4).pre (decMulK 4).pub (decryptMul .sse 4) :=
  VG.Taint.constantTime (A := taint) _ decMul_agree (by taint_decide)

theorem decMulAvx3_ct : ConstantTime isa (decMulK 3).pre (decMulK 3).pub (decryptMul .avx2 3) :=
  VG.Taint.constantTime (A := taint) _ decMul_agree (by taint_decide)

theorem decMulAvx4_ct : ConstantTime isa (decMulK 4).pre (decMulK 4).pub (decryptMul .avx2 4) :=
  VG.Taint.constantTime (A := taint) _ decMul_agree (by taint_decide)

/-! The checks of each backend's code, each evaluated once: with `Elab.async`
the theorems below are elaborated in parallel, and the kernel would evaluate
a check stated in two of them twice. -/

theorem decMulWoSse : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14]
    (DecMul.inner .sse) = true := by lit_decide
theorem decMulWoAvx : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14]
    (DecMul.inner .avx2) = true := by lit_decide
theorem decMulCtlSse3 : ctlOk (decryptMul .sse 3) = true := by lit_decide
theorem decMulCtlSse4 : ctlOk (decryptMul .sse 4) = true := by lit_decide
theorem decMulCtlAvx3 : ctlOk (decryptMul .avx2 3) = true := by lit_decide
theorem decMulCtlAvx4 : ctlOk (decryptMul .avx2 4) = true := by lit_decide

theorem decMulSse3_correct : ∀ s, (decMulK 3).pre s →
    ∃ t s', Exec isa (decryptMul .sse 3) s t s' ∧ abiPreserved s s' ∧ (decMulK 3).post s s' :=
  decMul_correct BodiesOk.sse (by decide) (by decide) decMulWoSse decMulCtlSse3

theorem decMulSse4_correct : ∀ s, (decMulK 4).pre s →
    ∃ t s', Exec isa (decryptMul .sse 4) s t s' ∧ abiPreserved s s' ∧ (decMulK 4).post s s' :=
  decMul_correct BodiesOk.sse (by decide) (by decide) decMulWoSse decMulCtlSse4

theorem decMulAvx3_correct : ∀ s, (decMulK 3).pre s →
    ∃ t s', Exec isa (decryptMul .avx2 3) s t s' ∧ abiPreserved s s' ∧ (decMulK 3).post s s' :=
  decMul_correct BodiesOk.avx2 (by decide) (by decide) decMulWoAvx decMulCtlAvx3

theorem decMulAvx4_correct : ∀ s, (decMulK 4).pre s →
    ∃ t s', Exec isa (decryptMul .avx2 4) s t s' ∧ abiPreserved s s' ∧ (decMulK 4).post s s' :=
  decMul_correct BodiesOk.avx2 (by decide) (by decide) decMulWoAvx decMulCtlAvx4

theorem decMulSse3_verified : Verified X86_64.target (decryptMul .sse 3) (Spec.MlKem.decryptMulContract 3 X86_64.abi) :=
  decMul3_verified _ BodiesOk.sse decMulWoSse decMulCtlSse3 decMulSse3_ct

theorem decMulSse4_verified : Verified X86_64.target (decryptMul .sse 4) (Spec.MlKem.decryptMulContract 4 X86_64.abi) :=
  decMul4_verified _ BodiesOk.sse decMulWoSse decMulCtlSse4 decMulSse4_ct

theorem decMulAvx3_verified :
    Verified X86_64.target (decryptMul .avx2 3) (Spec.MlKem.decryptMulContract 3 X86_64.abi) :=
  decMul3_verified _ BodiesOk.avx2 decMulWoAvx decMulCtlAvx3 decMulAvx3_ct

theorem decMulAvx4_verified :
    Verified X86_64.target (decryptMul .avx2 4) (Spec.MlKem.decryptMulContract 4 X86_64.abi) :=
  decMul4_verified _ BodiesOk.avx2 decMulWoAvx decMulCtlAvx4 decMulAvx4_ct

end VG.Proof.MlKem.X86_64
