module

import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit

public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeEnc
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDecV
import VerifiedGarbage.Proof.MlKem.X86_64.Mul16V
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.X86_64.KpkeEnc
meta import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDecV
meta import VerifiedGarbage.Proof.MlKem.X86_64.Mul16V
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: `vg_mlkem768_kpke_encrypt`, verified

The proof of `KpkeEnc.lean` with AVX2, its constant time, and its contract
implying the shared one of `Proof/MlKem/Kpke16Contract.lean`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Kpke16
open VG.Spec.MlKem

theorem kpkeEnc_agree (L : Kem) (s₁ s₂ : State) (_ : (kpkeEncK L).pre s₁) (_ : (kpkeEncK L).pre s₂)
    (hp : (kpkeEncK L).pub s₁ s₂) :
    X86_64.Taint.Agree (X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) s₁ s₂ :=
  X86_64.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2]

theorem vecReducedW16_zero (p : Addr) (l : Nat) : VecReducedW 16 (fun _ => 0) p l := fun _ _ _ _ => by
  simp only [coeffAtW, Mem.readW, read_zero]
  decide

theorem keWf768 : KpkeEnc.KeWf kem768 := ⟨.inl rfl, by decide, by decide, by decide⟩

/-- The pointers that `kpkeEncPost` uses agree after `kpkeEncPre`: they are those of
the entry (`KpkeEnc.KT`), whose pointers agree. -/
theorem kpkeEnc_mid {L : Kem} {s₁ s₂ σ₁ σ₂ : State} (hp : (kpkeEncK L).pub σ₁ σ₂)
    (e₁ : KpkeEnc.EU L σ₁ 0 s₁) (e₂ : KpkeEnc.EU L σ₂ 0 s₂) :
    ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [e₁.kt.rbx, e₂.kt.rbx, hp.2.2.2.2.2.1]
  · rw [e₁.kt.rbp, e₂.kt.rbp, hp.2.1]
  · rw [e₁.kt.r12, e₂.kt.r12, hp.2.2.1]
  · rw [e₁.kt.r13, e₂.kt.r13, hp.2.2.2.1]
  · rw [e₁.kt.r14, e₂.kt.r14, hp.2.2.2.2.1]
  · rw [e₁.kt.r15, e₂.kt.r15, hp.1]
  · rw [e₁.kt.rsp, e₂.kt.rsp, hp.2.2.2.2.2.2]

theorem kpkeEnc768Y_ct :
    ConstantTime isa (kpkeEncK kem768).pre (kpkeEncK kem768).pub (kpkeEnc kem768 .avx2 encryptMul16Y) := by
  unfold kpkeEnc
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.seq
    (R := fun (s₁ s₂ : State) => ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], s₁.gpr r = s₂.gpr r) ?_ ?_)
  · refine ((RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
      (fun x y h => kpkeEnc_agree kem768 x y h.1 h.2.1 h.2.2) [] (by taint_decide)).wpDep
      (F := fun σ s => KpkeEnc.EU kem768 σ 0 s) fun s₁ s₂ h =>
        ⟨KpkeEnc.pre_wp PrimsOk.avx2 keWf768 encMul16Y3_correct (by lit_decide) (by lit_decide) h.1,
          KpkeEnc.pre_wp PrimsOk.avx2 keWf768 encMul16Y3_correct (by lit_decide) (by lit_decide) h.2.1⟩).mono
      (fun _ _ h => h) fun s₁ s₂ ⟨_, σ₁, σ₂, ⟨_, _, hp⟩, e₁, e₂⟩ => kpkeEnc_mid hp e₁ e₂
  · exact RelCT.mono (RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (fun x y h => X86_64.Taint.agree_ofRegs h) [] (by taint_decide)) (fun _ _ h => h) fun _ _ _ => trivial

theorem kpkeEnc768Y_correct : ∀ s, (kpkeEncK kem768).pre s →
    ∃ t s', Exec isa (kpkeEnc kem768 .avx2 encryptMul16Y) s t s' ∧ abiPreserved s s' ∧ (kpkeEncK kem768).post s s' :=
  KpkeEnc.kpkeEnc_correct PrimsOk.avx2 kdCalls768 keWf768 encMul16Y3_correct (by lit_decide) (by lit_decide)
    (by lit_decide) (by lit_decide) (by lit_decide) (by lit_decide)

/-- A state the contract permits. -/
def kpkeEncSat (L : Kem) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x5000 | .rcx => 0x6000 | .r8 => 0x8000 | .r9 => 0x10000
    | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 512 * (L.k * L.k)⟩, ⟨0x5000, 384 * L.k⟩, ⟨0x8000, 32⟩]
  wr := [⟨0x1000, L.ctLen⟩, ⟨0x6000, 512 * (2 * L.k + 1)⟩, ⟨0x10000, 20480⟩]

theorem kpkeEnc768_of {c : Prog isa}
    (hc : ∀ s, (kpkeEncK kem768).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (kpkeEncK kem768).post s s')
    (hct : ConstantTime isa (kpkeEncK kem768).pre (kpkeEncK kem768).pub c) :
    Verified X86_64.target c (Proof.MlKem.Params.kpkeEncryptContract Spec.MlKem.mlKem768 X86_64.abi) :=
  Verified.of_correct hc hct
    { pre := by sig_implies_pre [Params.kpkeEncryptContract, Params.kpkeEncryptSig, kpkeEncK, X86_64.abi,
        X86_64.argRegs, kScrE, Kem.k, Kem.ctLen, kem768, retR, Params.ctLen, mlKem768]
      post := by sig_implies_post [Params.kpkeEncryptContract, Params.kpkeEncryptSig, kpkeEncK, encCt, X86_64.abi,
        X86_64.argRegs, kScrE, Kem.k, Kem.du, Kem.dv, Kem.ctLen, kem768, retR, Params.ctLen, mlKem768]
      pub := by sig_implies_pub [Params.kpkeEncryptContract, Params.kpkeEncryptSig, kpkeEncK, X86_64.abi,
        X86_64.argRegs, kScrE, Kem.k, Kem.ctLen, kem768, retR, Params.ctLen, mlKem768]
      sat := by
        refine ⟨kpkeEncSat kem768, ?_⟩
        sig_pre [Params.kpkeEncryptContract, Params.kpkeEncryptSig, kpkeEncK, X86_64.abi, X86_64.argRegs]
        and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact vecReducedW16_zero _ _
          | (intro a h₁ h₂
             simp only [Region.Contains] at h₁ h₂
             bv_omega) }

theorem kpkeEnc768Y_verified :
    Verified X86_64.target (kpkeEnc kem768 .avx2 encryptMul16Y) (Proof.MlKem.Params.kpkeEncryptContract mlKem768 X86_64.abi) :=
  kpkeEnc768_of kpkeEnc768Y_correct kpkeEnc768Y_ct

end VG.Proof.MlKem.X86_64
