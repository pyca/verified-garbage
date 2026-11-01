module

public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDec
public import VerifiedGarbage.Proof.MlKem.X86_64.DecMulY
import VerifiedGarbage.Proof.MlKem.X86_64.RowEY
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDec
meta import VerifiedGarbage.Proof.MlKem.X86_64.DecMulY
meta import VerifiedGarbage.Proof.MlKem.X86_64.RowEY
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: `vg_mlkem768_kpke_decrypt`, verified

The proof of `KpkeDec.lean` for each backend, its constant time, and its
contract implying the shared one of `Proof/MlKem/Kpke16Contract.lean`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Kpke16
open VG.Spec.MlKem

theorem decMulY3_wo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14]
    (DecMulY.innerY 3) = true := writesOnly_of (by lit_decide)

theorem decMulY4_wo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14]
    (DecMulY.innerY 4) = true := writesOnly_of (by lit_decide)

/-- The products of `ŝᵀ ∘ NTT(u)` with AVX2, inline. -/
theorem dmOkY : KpkeDec.DmOk dmInnerY where
  ok k hk s₀ hs := by
    rcases hk with rfl | rfl
    · exact DecMulY.body_ok hs (by decide) (by decide) decMulY3_wo (rowEY_wo (.inl rfl) (.inl rfl))
    · exact DecMulY.body_ok hs (by decide) (by decide) decMulY4_wo (rowEY_wo (.inr rfl) (.inl rfl))
  nc k hk := by rcases hk with rfl | rfl <;> lit_decide
  r15 k hk := by rcases hk with rfl | rfl <;> lit_decide

theorem kpkeDec_agree (L : Kem) (s₁ s₂ : State) (_ : (kpkeDecK L).pre s₁) (_ : (kpkeDecK L).pre s₂)
    (hp : (kpkeDecK L).pub s₁ s₂) :
    X86_64.Taint.Agree (X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) s₁ s₂ :=
  X86_64.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2]

theorem kdWf768 : KpkeDec.KdWf kem768 := ⟨.inl rfl, by decide, by decide, by decide⟩

theorem kdCalls768 : KemCalls kem768 compressWidths compressWidths := ⟨Codecs.ceI, Codecs.ddI, by decide, by decide⟩

theorem kpkeDec768Y_ct :
    ConstantTime isa (kpkeDecK kem768).pre (kpkeDecK kem768).pub (kpkeDec kem768 .avx2 dmInnerY) :=
  VG.Taint.constantTime (A := taint) _ (kpkeDec_agree kem768) (by taint_decide)

theorem kpkeDec768Y_correct : ∀ s, (kpkeDecK kem768).pre s →
    ∃ t s', Exec isa (kpkeDec kem768 .avx2 dmInnerY) s t s' ∧ abiPreserved s s' ∧ (kpkeDecK kem768).post s s' :=
  KpkeDec.kpkeDec_correct PrimsOk.avx2 kdCalls768 kdWf768 dmOkY (by lit_decide) (by lit_decide) (by lit_decide)
    (by lit_decide) (by lit_decide)

/-- A state the contract permits. -/
def kpkeDecSat (L : Kem) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x10000 | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 384 * L.k⟩, ⟨0x3000, L.ctLen⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x10000, 16384⟩]

theorem kpkeDec768_of {c : Prog isa}
    (hc : ∀ s, (kpkeDecK kem768).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (kpkeDecK kem768).post s s')
    (hct : ConstantTime isa (kpkeDecK kem768).pre (kpkeDecK kem768).pub c) :
    Verified X86_64.target c (Proof.MlKem.Params.kpkeDecryptContract Spec.MlKem.mlKem768 X86_64.abi) :=
  Verified.of_correct hc hct
    { pre := by sig_implies_pre [Params.kpkeDecryptContract, Params.kpkeDecryptSig, kpkeDecK, X86_64.abi, X86_64.argRegs, kScr, Kem.k,
        Kem.ctLen, kem768, retR, Params.ctLen, mlKem768]
      post := by sig_implies_post [Params.kpkeDecryptContract, Params.kpkeDecryptSig, kpkeDecK, X86_64.abi, X86_64.argRegs, kScr, Kem.k,
        Kem.ctLen, kem768, retR, Params.ctLen, mlKem768]
      pub := by sig_implies_pub [Params.kpkeDecryptContract, Params.kpkeDecryptSig, kpkeDecK, X86_64.abi, X86_64.argRegs, kScr, Kem.k,
        Kem.ctLen, kem768, retR, Params.ctLen, mlKem768]
      sat := by
        refine ⟨kpkeDecSat kem768, ?_⟩
        sig_pre [Params.kpkeDecryptContract, Params.kpkeDecryptSig, kpkeDecK, X86_64.abi,
          X86_64.argRegs]
        and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | (intro a h₁ h₂
             simp only [Region.Contains] at h₁ h₂
             bv_omega) }

theorem kpkeDec768Y_verified :
    Verified X86_64.target (kpkeDec kem768 .avx2 dmInnerY) (Proof.MlKem.Params.kpkeDecryptContract mlKem768 X86_64.abi) :=
  kpkeDec768_of kpkeDec768Y_correct kpkeDec768Y_ct

end VG.Proof.MlKem.X86_64
