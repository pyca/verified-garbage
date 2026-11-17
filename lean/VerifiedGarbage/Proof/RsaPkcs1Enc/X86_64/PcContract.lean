module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86_64.Precomputed
public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCall
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Contract
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.PcCall
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCorrect
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified

/-! ### `RsaPkcs1Enc.X86_64.PcCorrect`, which only this module used -/

section

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
    (h : (Proof.RsaPkcs1Enc.encryptPrecomputedContract abi encStack).pre s) :
    ∃ t s', Exec isa (Impl.RsaPkcs1Enc.X86_64.Precomputed.code v.name v.code) s t s' ∧ abiPreserved s s' ∧
      post s s' := by
  have hp := pre_of h
  suffices hw : WP isa (Impl.RsaPkcs1Enc.X86_64.Precomputed.code v.name v.code) s fun s' =>
      abiPreserved s s' ∧ post s s' by
    obtain ⟨t, s', he, hq⟩ := hw
    exact ⟨t, s', he, hq⟩
  refine wp_alloc (by decide) (by decide) (by decide) (by have := hp.sp1; unfold encStack at this; omega_using [this]) ?_
  rw [body_eq]
  refine wp_seq4 (WP.mono_mx (by decide +kernel)
    (WP.keep [.rax, .rcx, .rdx, .rsi, .rdi, .r10, .r11] (em_ok hp.toEPre) (by decide +kernel))
    fun t ⟨hpc, k⟩ hmx => (⟨hpc, k, hmx⟩ : PreCall s t ∧ Keep _ (allocState frameBytes s) t ∧ _)) ?_
  intro t₁ ⟨hpc, k₁, hmx₁⟩
  refine WP.seq (WP.mono_mx (by decide +kernel) (callArgs_ok hp hpc) fun t₂ ⟨hj, k₂⟩ hmx₂ => ?_)
  refine WP.seq (WP.mono (call_ok v hp hj) fun t₃ ⟨hpost, hcs₃, hmx₃⟩ => ?_)
  refine WP.mono_mx (by decide +kernel) (tail_ok hp.toEPre hpost.toAfterCall) fun t₄ ht hmx₄ => ?_
  refine ⟨ht.rsp, by rw [ht.wr]; rfl, fun m u fm => ?_⟩
  have hs := VG.Proof.RsaPkcs1Enc.X86_64.frame_sub s (d := 0) (n := frameBytes) (by omega_using [])
  simp only [off, BitVec.add_zero] at hs
  refine ⟨⟨fun r hr => ?_, ret_frame hp.toEPre (ht.mem.trans (fm.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., hs⟩)), ?_⟩, ?_⟩
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
    have hsi := hp.toEPre.hsi
    exact Proof.Rsa.written_frame fm (s.gpr .rcx).isLt (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      have := (hp.toEPre.dKo.sub_left hs).symm
      rwa [hsi] at this) this

end VG.Proof.RsaPkcs1Enc.X86_64.Pc

end

end


/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86-64: the contract

`contract` is the shared contract's precondition, `post`, and `encK`'s public
data with `pre` and its words; it implies the shared contract (`implies`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

def contract : Contract isa where
  pre := (Proof.RsaPkcs1Enc.encryptPrecomputedContract abi encStack).pre
  post := post
  pub a s := encK.pub a s ∧ stackArg a 6 = stackArg s 6 ∧ stackArg a 7 = stackArg s 7 ∧
    Spec.Rsa.wordsAt a.mem (stackArg a 6) (stackArg a 7).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat

/-- `encSatState`, with 16 words of `pre` at `0x5000`. -/
def satState : State := { encSatState with
  mem := fun a => if a = 0x10039 then 0x50 else if a = 0x10040 then 16 else encSatState.mem a
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0x4100, 61⟩, ⟨0x5000, 128⟩, ⟨0x10008, 64⟩] }

theorem implies : contract.Implies (Proof.RsaPkcs1Enc.encryptPrecomputedContract abi encStack) where
  pre := fun _ h => h
  post := by sig_implies_post [Proof.RsaPkcs1Enc.encryptPrecomputedContract,
    Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi, argRegs, contract, post, encK, encStack,
    Impl.RsaPkcs1Enc.X86_64.Encrypt.frameBytes, stackArgs_eight, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig,
      abi, argRegs, contract, encStack, Impl.RsaPkcs1Enc.X86_64.Encrypt.frameBytes, stackArgs_eight,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
    obtain ⟨hb, hq⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, hcx, h9])
    have hq' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hq
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hb
    refine ⟨⟨?_, by simp only [stackArgs_six, a0, a1, a2, a3, a4, a5], hn, he⟩, a6, a7, hq'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Proof.RsaPkcs1Enc.encryptPrecomputedContract,
    Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi, argRegs, contract, encStack,
    Impl.RsaPkcs1Enc.X86_64.Encrypt.frameBytes, stackArgs_eight, List.append_eq]
    [satState, encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

end VG.Proof.RsaPkcs1Enc.X86_64.Pc
