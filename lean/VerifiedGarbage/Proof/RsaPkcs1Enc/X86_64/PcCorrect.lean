module
public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86_64.Precomputed
public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCall
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Precomputed

import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.PcCall
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCorrect
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Rsa.X86_64.PrivFrame

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86-64: correctness

`EM` as `vg_rsa_pkcs1_encrypt` builds it (`em_ok`), the call with `pre`
(`callArgs_ok`, `call_ok`) and the mask (`tail_ok`): if `pre` holds the
values for `n`, `encK`'s postcondition (`code_correct`), and the frame and
the registers the ABI keeps whatever `pre` holds.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Pc

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Encrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa.X86_64 (PublicImpl)

/-- `encK`'s postcondition, if `pre` holds the values for `n`. -/
def post (s u : State) : Prop :=
  Spec.Rsa.publicPrecompute (nB s) = some (Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat) →
    encK.post s u

theorem body_eq (pubName : String) (pub : Prog isa) :
    Impl.RsaPkcs1Enc.X86_64.Precomputed.body pubName pub = .seq (.block setup) (.seq psLoop (.seq (.block sep)
      (.seq msgCopy (.seq (.block Impl.RsaPkcs1Enc.X86_64.Precomputed.callArgs) (.seq (.call pubName pub)
        (.seq (.block maskArgs) (.seq maskLoop (.block [.mov .rax (.reg .r11)])))))))) :=
  rfl

theorem code_correct (v : PublicImpl) (s : State)
    (h : (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi encStack).pre s) :
    ∃ t s', Exec isa (Impl.RsaPkcs1Enc.X86_64.Precomputed.code v.name v.code) s t s' ∧ abiPreserved s s' ∧
      post s s' := by
  have hp := pre_of h
  suffices hw : WP isa (Impl.RsaPkcs1Enc.X86_64.Precomputed.code v.name v.code) s fun s' =>
      abiPreserved s s' ∧ post s s' by
    obtain ⟨t, s', he, hq⟩ := hw
    exact ⟨t, s', he, hq⟩
  refine wp_alloc (by decide) (by decide) (by decide) (by have := hp.sp1; unfold encStack at this; omega) ?_
  rw [body_eq]
  refine wp_seq4 (WP.mono_mx (by decide +kernel)
    (WP.keep [.rax, .rcx, .rdx, .rsi, .rdi, .r10, .r11] (em_ok hp.toEPre) (by decide +kernel))
    fun t ⟨hpc, k⟩ hmx => (⟨hpc, k, hmx⟩ : PreCall s t ∧ Keep _ (allocState frameBytes s) t ∧ _)) ?_
  intro t₁ ⟨hpc, k₁, hmx₁⟩
  refine WP.seq (WP.mono_mx (by decide +kernel) (callArgs_ok hp hpc) fun t₂ ⟨hj, k₂⟩ hmx₂ => ?_)
  refine WP.seq (WP.mono (call_ok v hp hj) fun t₃ ⟨hpost, hcs₃, hmx₃⟩ => ?_)
  refine WP.mono_mx (by decide +kernel) (tail_ok hp.toEPre hpost.toAfterCall) fun t₄ ht hmx₄ => ?_
  refine ⟨ht.rsp, by rw [ht.wr]; rfl, ⟨fun r hr => ?_, ret_frame hp.toEPre ht.mem, ?_⟩, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'
      show t₄.gpr .rsp + BitVec.ofNat 64 frameBytes = s.gpr .rsp
      rw [ht.rsp, BitVec.sub_add_cancel]
    · show (if r = .rsp then _ else t₄.gpr r) = s.gpr r
      have hnr : r ∉ [Reg.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp only [hr', ↓reduceIte]
      rw [ht.keep.gpr (not_mem_of hnr (by decide)), hcs₃ r hr, k₂.gpr (not_mem_of hnr (by decide)),
        k₁.gpr (not_mem_of hnr (by decide))]
      simp only [allocState_gpr, hr', ↓reduceIte]
  · show t₄.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
    rw [hmx₄, hmx₃, hmx₂, hmx₁]; rfl
  · intro hq
    have := result_ok hp.toEPre ⟨hpost.toAfterCall, hpost.res hq⟩ ht
    simp only [encK] at this ⊢
    rw [freed_mem, freed_rax]; exact this

end VG.Proof.RsaPkcs1Enc.X86_64.Pc
