import VerifiedGarbage.Proof.MlKem.X86_64.EncMul
import VerifiedGarbage.Proof.MlKem.X86_64.Lit
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly

/-!
# ML-KEM on x86-64: `vg_mlkem768_encrypt_mul` and `vg_mlkem1024_encrypt_mul`, verified

The proof of `EncMul.lean` for each backend and rank, its constant time,
and its contract implying the shared one of `Spec/MlKem/KpkeMul.lean`.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem encMul_correct {B : Bodies} (hB : BodiesOk B) {k : Nat} (hk : k ≤ 4) (hk0 : 0 < k)
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp]
      (EncMul.innerE B k) = true)
    (hctl : ctlOk (encryptMul B k) = true) (s : State) (hs : (encMulK k).pre s) :
    ∃ t s', Exec isa (encryptMul B k) s t s' ∧ abiPreserved s s' ∧ (encMulK k).post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := EncMul.wp_all hs hk hB hk0 hwo
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hg, hpost⟩

theorem encMul_agree {k : Nat} (s₁ s₂ : State) (_ : (encMulK k).pre s₁) (_ : (encMulK k).pre s₂)
    (hp : (encMulK k).pub s₁ s₂) :
    X86_64.Taint.Agree (X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) s₁ s₂ :=
  X86_64.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2]

/-- A state satisfying the precondition, for `k ≤ 4`. -/
def encMulSat (k : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x8000 | .rdx => 0x20000 | .rcx => 0x28000 | .r8 => 0x30000
    | .rsp => 0x40000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x8000, 1024 * (k * k)⟩, ⟨0x20000, 1024 * k⟩, ⟨0x28000, 1024 * k⟩]
  wr := [⟨0x1000, 1024 * (k + 1)⟩, ⟨0x30000, 4096⟩]

section
variable (B : Bodies)

theorem encMul3_verified (hB : BodiesOk B)
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp]
      (EncMul.innerE B 3) = true)
    (hctl : ctlOk (encryptMul B 3) = true)
    (hct : ConstantTime isa (encMulK 3).pre (encMulK 3).pub (encryptMul B 3)) :
    Verified X86_64.target (encryptMul B 3) (Spec.MlKem.encryptMulContract 3 X86_64.abi) :=
  Verified.of_correct (encMul_correct hB (by decide) (by decide) hwo hctl) hct
    { pre := by sig_implies_pre [Spec.MlKem.encryptMulContract, Spec.MlKem.encryptMulSig, encMulK, X86_64.abi,
        X86_64.argRegs]
      post := by sig_implies_post [Spec.MlKem.encryptMulContract, Spec.MlKem.encryptMulSig, encMulK, X86_64.abi,
        X86_64.argRegs]
      pub := by sig_implies_pub [Spec.MlKem.encryptMulContract, Spec.MlKem.encryptMulSig, encMulK, X86_64.abi,
        X86_64.argRegs]
      sat := by
        refine ⟨encMulSat 3, ?_⟩
        sig_pre [Spec.MlKem.encryptMulContract, Spec.MlKem.encryptMulSig, encMulK, X86_64.abi, X86_64.argRegs]
        and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact vecReduced_zero _ _
          | (intro a h₁ h₂
             simp only [Region.Contains] at h₁ h₂
             bv_omega) }


theorem encMul4_verified (hB : BodiesOk B)
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp]
      (EncMul.innerE B 4) = true)
    (hctl : ctlOk (encryptMul B 4) = true)
    (hct : ConstantTime isa (encMulK 4).pre (encMulK 4).pub (encryptMul B 4)) :
    Verified X86_64.target (encryptMul B 4) (Spec.MlKem.encryptMulContract 4 X86_64.abi) :=
  Verified.of_correct (encMul_correct hB (by decide) (by decide) hwo hctl) hct
    { pre := by sig_implies_pre [Spec.MlKem.encryptMulContract, Spec.MlKem.encryptMulSig, encMulK, X86_64.abi,
        X86_64.argRegs]
      post := by sig_implies_post [Spec.MlKem.encryptMulContract, Spec.MlKem.encryptMulSig, encMulK, X86_64.abi,
        X86_64.argRegs]
      pub := by sig_implies_pub [Spec.MlKem.encryptMulContract, Spec.MlKem.encryptMulSig, encMulK, X86_64.abi,
        X86_64.argRegs]
      sat := by
        refine ⟨encMulSat 4, ?_⟩
        sig_pre [Spec.MlKem.encryptMulContract, Spec.MlKem.encryptMulSig, encMulK, X86_64.abi, X86_64.argRegs]
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

/-! The facts about the code, each checked once (on the literals of `Lit.lean`). -/

theorem encMulSse3_wo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp]
    (EncMul.innerE .sse 3) = true :=
  writesOnly_of (by lit_decide)

theorem encMulSse3_ctl : ctlOk (encryptMul .sse 3) = true := by lit_decide

theorem encMulSse4_wo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp]
    (EncMul.innerE .sse 4) = true :=
  writesOnly_of (by lit_decide)

theorem encMulSse4_ctl : ctlOk (encryptMul .sse 4) = true := by lit_decide

theorem encMulAvx3_wo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp]
    (EncMul.innerE .avx2 3) = true :=
  writesOnly_of (by lit_decide)

theorem encMulAvx3_ctl : ctlOk (encryptMul .avx2 3) = true := by lit_decide

theorem encMulAvx4_wo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp]
    (EncMul.innerE .avx2 4) = true :=
  writesOnly_of (by lit_decide)

theorem encMulAvx4_ctl : ctlOk (encryptMul .avx2 4) = true := by lit_decide

theorem encMulSse3_ct : ConstantTime isa (encMulK 3).pre (encMulK 3).pub (encryptMul .sse 3) :=
  VG.Taint.constantTime (A := taint) _ encMul_agree (by taint_decide)

theorem encMulSse3_correct : ∀ s, (encMulK 3).pre s →
    ∃ t s', Exec isa (encryptMul .sse 3) s t s' ∧ abiPreserved s s' ∧ (encMulK 3).post s s' :=
  encMul_correct BodiesOk.sse (by decide) (by decide) encMulSse3_wo encMulSse3_ctl

theorem encMulSse3_verified :
    Verified X86_64.target (encryptMul .sse 3) (Spec.MlKem.encryptMulContract 3 X86_64.abi) :=
  encMul3_verified _ BodiesOk.sse encMulSse3_wo encMulSse3_ctl encMulSse3_ct

theorem encMulSse4_ct : ConstantTime isa (encMulK 4).pre (encMulK 4).pub (encryptMul .sse 4) :=
  VG.Taint.constantTime (A := taint) _ encMul_agree (by taint_decide)

theorem encMulSse4_correct : ∀ s, (encMulK 4).pre s →
    ∃ t s', Exec isa (encryptMul .sse 4) s t s' ∧ abiPreserved s s' ∧ (encMulK 4).post s s' :=
  encMul_correct BodiesOk.sse (by decide) (by decide) encMulSse4_wo encMulSse4_ctl

theorem encMulSse4_verified :
    Verified X86_64.target (encryptMul .sse 4) (Spec.MlKem.encryptMulContract 4 X86_64.abi) :=
  encMul4_verified _ BodiesOk.sse encMulSse4_wo encMulSse4_ctl encMulSse4_ct

theorem encMulAvx3_ct : ConstantTime isa (encMulK 3).pre (encMulK 3).pub (encryptMul .avx2 3) :=
  VG.Taint.constantTime (A := taint) _ encMul_agree (by taint_decide)

theorem encMulAvx3_correct : ∀ s, (encMulK 3).pre s →
    ∃ t s', Exec isa (encryptMul .avx2 3) s t s' ∧ abiPreserved s s' ∧ (encMulK 3).post s s' :=
  encMul_correct BodiesOk.avx2 (by decide) (by decide) encMulAvx3_wo encMulAvx3_ctl

theorem encMulAvx3_verified :
    Verified X86_64.target (encryptMul .avx2 3) (Spec.MlKem.encryptMulContract 3 X86_64.abi) :=
  encMul3_verified _ BodiesOk.avx2 encMulAvx3_wo encMulAvx3_ctl encMulAvx3_ct

theorem encMulAvx4_ct : ConstantTime isa (encMulK 4).pre (encMulK 4).pub (encryptMul .avx2 4) :=
  VG.Taint.constantTime (A := taint) _ encMul_agree (by taint_decide)

theorem encMulAvx4_correct : ∀ s, (encMulK 4).pre s →
    ∃ t s', Exec isa (encryptMul .avx2 4) s t s' ∧ abiPreserved s s' ∧ (encMulK 4).post s s' :=
  encMul_correct BodiesOk.avx2 (by decide) (by decide) encMulAvx4_wo encMulAvx4_ctl

theorem encMulAvx4_verified :
    Verified X86_64.target (encryptMul .avx2 4) (Spec.MlKem.encryptMulContract 4 X86_64.abi) :=
  encMul4_verified _ BodiesOk.avx2 encMulAvx4_wo encMulAvx4_ctl encMulAvx4_ct

end VG.Proof.MlKem.X86_64
