module
public import VerifiedGarbage.Proof.MlKem.X86_64.S4CT

import VerifiedGarbage.Proof.MlKem.X86_64.S4Verified
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Verified
import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
import VerifiedGarbage.Proof.MlKem.Bits
meta import VerifiedGarbage.Proof.MlKem.Bits
import VerifiedGarbage.Impl.MlKem.X86_64.Frag
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlKem.X86_64.FragCall
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
meta import VerifiedGarbage.Impl.MlKem.X86_64.Frag
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
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
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragCall
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4CT
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
meta import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.X86_64.X4R.Loop

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4`, verified

The baseline implementation of `vg_mlkem_sample_ntt4` calls
`vg_mlkem_sample_ntt` on each seed, between the prologue and the epilogue of
the one for AVX2; its proofs are the pieces of that one's for the calls
(`S4Parse.lean`, `S4CT.lean`), with nothing to keep of the memory but the
polynomials already sampled.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.S4

variable {w16 : Bool}

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Spec.MlKem

/-- Nothing of the memory. -/
abbrev NoX (_ : Mem) : Prop := True

section
variable {σ : State} (hp : PreW w16 σ)
include hp

theorem callK_ok' {K : Nat} (hK : K < 4) {s : State} (h : PCW w16 NoX σ K s) : WP isa (callK K w16) s (PCW w16 NoX σ (K + 1)) :=
  WP.seq (WP.mono (argsK_ok hK h) fun _ h₂ => WP.seq (WP.mono (callK_ok hp hK (fun _ _ _ _ => trivial) h₂)
    fun _ h₃ => andK_ok h₃))

theorem scalar_body_ok {s : State} (h : I0W w16 σ s) :
    WP isa (.seq (callK 0 w16) (.seq (callK 1 w16) (.seq (callK 2 w16) (.seq (callK 3 w16) (.block epi))))) s fun s' =>
      (sample4KW w16).post σ s' ∧ gprPreserved σ s' := by
  have p₀ : PCW w16 NoX σ 0 s := ⟨h.env, trivial, by rw [h.r14]; rfl, fun _ h _ _ => absurd h (by omega)⟩
  exact WP.seq (WP.mono (callK_ok' hp (by decide) p₀) fun _ p₁ => WP.seq (WP.mono (callK_ok' hp (by decide) p₁)
    fun _ p₂ => WP.seq (WP.mono (callK_ok' hp (by decide) p₂) fun _ p₃ =>
      WP.seq (WP.mono (callK_ok' hp (by decide) p₃) fun _ p₄ => end_ok hp p₄))))

end

theorem correct_scalar (σ : State) (hs : (sample4KW w16).pre σ) :
    ∃ t s', Exec isa (Impl.MlKem.X86_64.Sample4.sampleNTT4 w16) σ t s' ∧ abiPreserved σ s' ∧
      (sample4KW w16).post σ s' := by
  have hp := preW_of hs
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok hp) fun _ h => scalar_body_ok hp h)
  exact ⟨t, s', he, abiPreserved_of_exec (by cases w16 <;> decide +kernel) he hF.2, hF.1⟩

/-- The taint analysis of the arguments of the call on seed `K`, of either width. -/
theorem args_taint {K : Nat} (hK : K < 4) (w16 : Bool) : ∃ hc : VG.Taint.Hint X86_64.Taint.T,
    (taint.check (X86_64.Taint.ofRegs [.r12, .r13, .rbx])
      (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * K))),
        .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (pBytes w16 * K))), .mov .rdx (.reg .rbx),
        .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))]) hc).isSome = true := by
  rcases (by omega : K = 0 ∨ K = 1 ∨ K = 2 ∨ K = 3) with rfl | rfl | rfl | rfl <;> cases w16 <;>
    exact ⟨_, by taint_decide⟩

/-- The call on seed `K`. -/
theorem callK_ct {K : Nat} (hK : K < 4) :
    RelCT isa (R4W w16 fun σ s => PCW w16 NoX σ K s) (callK K w16) (R4W w16 fun σ s => PCW w16 NoX σ (K + 1) s) := by
  obtain ⟨_, c⟩ := args_taint hK w16
  exact RelCT.seq (args_ct (X := fun _ => NoX) hK c) (RelCT.seq (call_ct hK fun _ _ _ _ _ _ => trivial) and_ct)

theorem ct_scalar : ConstantTime isa (sample4KW w16).pre (sample4KW w16).pub (Impl.MlKem.X86_64.Sample4.sampleNTT4 w16) := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq (RelCT.mono (relInv (I' := fun σ s => PCW w16 NoX σ 0 s)
    (fun σ s hp h => by
      subst h
      exact WP.mono (pro_ok (preW_of hp)) fun _ h => ⟨h.env, trivial, by rw [h.r14]; rfl, fun _ h _ _ => absurd h (by omega)⟩)
    (taintRel [.rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hq.1, hq.2.1, hq.2.2.1]) (by taint_decide))) (fun _ _ h => h) fun _ _ h => h) ?_)
  refine RelCT.seq (callK_ct (K := 0) (by decide)) (RelCT.seq (callK_ct (K := 1) (by decide))
    (RelCT.seq (callK_ct (K := 2) (by decide)) (RelCT.seq (callK_ct (K := 3) (by decide)) ?_)))
  exact taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide)

end VG.Proof.MlKem.X86_64.S4

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

theorem sample4_scalar_correct (σ : State) (hs : sample4K.pre σ) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.Sample4.sampleNTT4 σ t s' ∧ abiPreserved σ s' ∧ sample4K.post σ s' := by
  rw [sample4K_eq] at hs ⊢; exact S4.correct_scalar (w16 := false) σ hs

theorem sample4_scalar_ct : ConstantTime isa sample4K.pre sample4K.pub Impl.MlKem.X86_64.Sample4.sampleNTT4 := by
  rw [sample4K_eq]; exact S4.ct_scalar (w16 := false)

theorem sample4_scalar_verified : Verified X86_64.target Impl.MlKem.X86_64.Sample4.sampleNTT4
    (Proof.MlKem.sampleNTT4Contract X86_64.abi 24) :=
  Verified.of_correct sample4_scalar_correct sample4_scalar_ct
    { pre := by sig_implies_pre [Proof.MlKem.sampleNTT4Contract, Proof.MlKem.sampleNTT4Sig, sample4K, X86_64.abi,
        X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Proof.MlKem.sampleNTT4Contract, Proof.MlKem.sampleNTT4Sig, sample4K, X86_64.abi, X86_64.argRegs]
        exact sample4_post h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.MlKem.sampleNTT4Contract, Proof.MlKem.sampleNTT4Sig, sample4K, X86_64.abi, X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.MlKem.sampleNTT4Contract, Proof.MlKem.sampleNTT4Sig, sample4K, X86_64.abi, X86_64.argRegs]
        sig_simp [Proof.MlKem.sampleNTT4Contract, Proof.MlKem.sampleNTT4Sig, sample4K, X86_64.abi, X86_64.argRegs]
          [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals first | with_reducible assumption | exact map_toNat_inj ‹_›
      sat := by
        sig_implies_sat [Proof.MlKem.sampleNTT4Contract, Proof.MlKem.sampleNTT4Sig, sample4K, X86_64.abi,
          X86_64.argRegs] [sample4Sat] using sample4Sat }

end VG.Proof.MlKem.X86_64
