module

public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDec
meta import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDec
public import VerifiedGarbage.Proof.MlKem.X86_64.DecMulY
meta import VerifiedGarbage.Proof.MlKem.X86_64.DecMulY
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import VerifiedGarbage.Proof.MlKem.X86_64.RowEY
meta import VerifiedGarbage.Proof.MlKem.X86_64.RowEY
import VerifiedGarbage.Proof.MlKem.X86_64.Lit
meta import VerifiedGarbage.Proof.MlKem.X86_64.Lit
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.MlKem.PolyW
import VerifiedGarbage.Proof.MlKem.X86_64.AccInvY
import VerifiedGarbage.Proof.MlKem.X86_64.Cbd16Avx2
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
import VerifiedGarbage.Proof.MlKem.X86_64.FragC
import VerifiedGarbage.Proof.MlKem.X86_64.FragDM
import VerifiedGarbage.Proof.MlKem.X86_64.FragEM
import VerifiedGarbage.Proof.MlKem.X86_64.FragL
import VerifiedGarbage.Proof.MlKem.X86_64.KgCT
import VerifiedGarbage.Proof.MlKem.X86_64.KgMulV
import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Model
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Step
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Top
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.TopAcc
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.TopAcc16
import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
import VerifiedGarbage.Proof.MlKem.X86_64.S4Verified
import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay42
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Word
import VerifiedGarbage.Proof.Sha3.X86_64.X4R.Loop
meta import VerifiedGarbage.Proof.Bignum.Layout
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.Words
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.Words
meta import VerifiedGarbage.Proof.MlKem.PolyW
meta import VerifiedGarbage.Proof.MlKem.X86_64.AccInvY
meta import VerifiedGarbage.Proof.MlKem.X86_64.Cbd16Avx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
meta import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragC
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragDM
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragEM
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragL
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgCT
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Model
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Step
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Top
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.TopAcc
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.TopAcc16
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Verified
meta import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
meta import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
meta import VerifiedGarbage.Proof.MlKem.X86_64.VPack
meta import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay42
meta import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Word
meta import VerifiedGarbage.Proof.Sha3.X86_64.X4R.Loop

/-!
# ML-KEM on x86-64: `vg_mlkem768_kpke_decrypt`, verified

The proof of `KpkeDec.lean` for each backend, its constant time, and its
contract implying the shared one of `Spec/MlKem/Kpke16.lean`.
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
    Verified X86_64.target c (Spec.MlKem.mlKem768.kpkeDecryptContract X86_64.abi) :=
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
    Verified X86_64.target (kpkeDec kem768 .avx2 dmInnerY) (mlKem768.kpkeDecryptContract X86_64.abi) :=
  kpkeDec768_of kpkeDec768Y_correct kpkeDec768Y_ct

end VG.Proof.MlKem.X86_64
