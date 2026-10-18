module

public import VerifiedGarbage.Proof.MlKem.X86_64.DecMulY
meta import VerifiedGarbage.Proof.MlKem.X86_64.DecMulY
public import VerifiedGarbage.Proof.MlKem.X86_64.EncMulY
meta import VerifiedGarbage.Proof.MlKem.X86_64.EncMulY
public import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
import VerifiedGarbage.Proof.MlKem.X86_64.Lit
meta import VerifiedGarbage.Proof.MlKem.X86_64.Lit
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
meta import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
meta import VerifiedGarbage.Proof.MlKem.X86_64.YLanes

/-!
# ML-KEM on x86-64: `vg_mlkem*_{en,de}crypt_mul_avx2`, verified

The proofs of `DecMulY.lean` and `EncMulY.lean` for each rank, their
constant time, and their contracts implying the shared ones of
`Spec/MlKem/KpkeMul.lean`, as `DecMulV.lean` and `EncMulV.lean` do for
`decryptMul` and `encryptMul`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! The facts about the code, each checked once (on the literals of `Lit.lean`). -/

theorem decMulY3_wo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14]
    (DecMulY.innerY 3) = true := writesOnly_of (by lit_decide)

theorem decMulY4_wo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14]
    (DecMulY.innerY 4) = true := writesOnly_of (by lit_decide)

theorem encMulY3_wo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp]
    (EncMulY.innerY 3) = true := writesOnly_of (by lit_decide)

theorem encMulY4_wo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp]
    (EncMulY.innerY 4) = true := writesOnly_of (by lit_decide)

theorem decMulY3_ctl : ctlOk (decryptMulY 3) = true := by lit_decide
theorem decMulY4_ctl : ctlOk (decryptMulY 4) = true := by lit_decide
theorem encMulY3_ctl : ctlOk (encryptMulY 3) = true := by lit_decide
theorem encMulY4_ctl : ctlOk (encryptMulY 4) = true := by lit_decide

/-! ## `decrypt_mul` -/

theorem decMulY_correct {k : Nat} (hk : k = 3 ∨ k = 4)
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14] (DecMulY.innerY k) = true)
    (hctl : ctlOk (decryptMulY k) = true) (s : State) (hs : (decMulK k).pre s) :
    ∃ t s', Exec isa (decryptMulY k) s t s' ∧ abiPreserved s s' ∧ (decMulK k).post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := DecMulY.wp_all hs (by omega) (by omega) hwo (rowEY_wo hk (.inl rfl))
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hg, hpost⟩

theorem decMulY3_ct : ConstantTime isa (decMulK 3).pre (decMulK 3).pub (decryptMulY 3) :=
  VG.Taint.constantTime (A := taint) _ decMul_agree (by taint_decide)

theorem decMulY4_ct : ConstantTime isa (decMulK 4).pre (decMulK 4).pub (decryptMulY 4) :=
  VG.Taint.constantTime (A := taint) _ decMul_agree (by taint_decide)

theorem decMulY3_correct : ∀ s, (decMulK 3).pre s →
    ∃ t s', Exec isa (decryptMulY 3) s t s' ∧ abiPreserved s s' ∧ (decMulK 3).post s s' :=
  decMulY_correct (.inl rfl) decMulY3_wo decMulY3_ctl

theorem decMulY4_correct : ∀ s, (decMulK 4).pre s →
    ∃ t s', Exec isa (decryptMulY 4) s t s' ∧ abiPreserved s s' ∧ (decMulK 4).post s s' :=
  decMulY_correct (.inr rfl) decMulY4_wo decMulY4_ctl

/-! ## `encrypt_mul` -/

theorem encMulY_correct {k : Nat} (hk : k = 3 ∨ k = 4)
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp]
      (EncMulY.innerY k) = true)
    (hctl : ctlOk (encryptMulY k) = true) (s : State) (hs : (encMulK k).pre s) :
    ∃ t s', Exec isa (encryptMulY k) s t s' ∧ abiPreserved s s' ∧ (encMulK k).post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := EncMulY.wp_all hs (by omega) hk hwo
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hg, hpost⟩

theorem encMulY3_ct : ConstantTime isa (encMulK 3).pre (encMulK 3).pub (encryptMulY 3) :=
  VG.Taint.constantTime (A := taint) _ encMul_agree (by taint_decide)

theorem encMulY4_ct : ConstantTime isa (encMulK 4).pre (encMulK 4).pub (encryptMulY 4) :=
  VG.Taint.constantTime (A := taint) _ encMul_agree (by taint_decide)

theorem encMulY3_correct : ∀ s, (encMulK 3).pre s →
    ∃ t s', Exec isa (encryptMulY 3) s t s' ∧ abiPreserved s s' ∧ (encMulK 3).post s s' :=
  encMulY_correct (.inl rfl) encMulY3_wo encMulY3_ctl

theorem encMulY4_correct : ∀ s, (encMulK 4).pre s →
    ∃ t s', Exec isa (encryptMulY 4) s t s' ∧ abiPreserved s s' ∧ (encMulK 4).post s s' :=
  encMulY_correct (.inr rfl) encMulY4_wo encMulY4_ctl

theorem encMulY3_verified : Verified X86_64.target (encryptMulY 3) (Spec.MlKem.encryptMulContract 3 X86_64.abi) :=
  Verified.of_correct encMulY3_correct encMulY3_ct
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

theorem encMulY4_verified : Verified X86_64.target (encryptMulY 4) (Spec.MlKem.encryptMulContract 4 X86_64.abi) :=
  Verified.of_correct encMulY4_correct encMulY4_ct
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

end VG.Proof.MlKem.X86_64
