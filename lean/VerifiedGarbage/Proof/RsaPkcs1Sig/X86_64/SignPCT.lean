module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignCT
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignPCall
import VerifiedGarbage.Proof.Rsa.X86_64.PrivPCT
import VerifiedGarbage.Proof.Rsa.PreWords
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCT
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignCT
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignPCall
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivPCT
meta import VerifiedGarbage.Proof.Rsa.PreWords
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCT

/-!
# `vg_rsa_pkcs1_sign_precomputed` on x86-64: constant time

`Sign.codeP` leaks what `Sign.code` leaks, and, in its call of
`vg_rsa_private_checked_precomputed`, `pre`'s address and length and the
modulus' values in it, which its contract (`sigContractP`) makes public: the
pieces of `SignCT.lean`, with entry states that also agree on those
(`XP`), and the call's (`callP_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.Sgn

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Sign
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (sp lea test0)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64
open VG.Proof.Rsa.X86_64 (CrtImpl chkContract chkContractP codeP_correct codeP_spSafe)
open VG.Proof.RsaPkcs1Sig.X86_64.Ver (regs_eq)

/-- `vg_rsa_pkcs1_sign_precomputed`'s contract, with `sigContract`'s
postcondition and its public data, with `pre`, `pre_len` and the modulus'
values in `pre`. -/
def sigContractP : Contract isa where
  pre := (Spec.RsaPkcs1Sig.signPrecomputedContract abi sigStack).pre
  post := sigContract.post
  pub s₁ s₂ := sigContract.pub s₁ s₂ ∧ stackArg s₁ 15 = stackArg s₂ 15 ∧ stackArg s₁ 16 = stackArg s₂ 16 ∧
    Spec.Rsa.privatePrecomputedLeak s₁.mem (stackArg s₁ 15) (s₁.gpr .rcx).toNat =
      Spec.Rsa.privatePrecomputedLeak s₂.mem (stackArg s₂ 15) (s₂.gpr .rcx).toNat

/-- What entry states agree on with `a` besides `sigContract.pub`. -/
def XP (a s : State) : Prop :=
  PreP s ∧ stackArg s 15 = stackArg a 15 ∧ stackArg s 16 = stackArg a 16 ∧
    Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 15) (s.gpr .rcx).toNat =
      Spec.Rsa.privatePrecomputedLeak a.mem (stackArg a 15) (a.gpr .rcx).toNat

/-! ## The call -/

def J4P (s t : State) : Prop :=
  EnvC s t ∧ (∀ i < 16, word t.mem (fb s) (8 * i) = callArgP s i) ∧
    t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rsi ∧ t.gpr .rdx = s.gpr .rdx ∧
    t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = s.gpr .r9

theorem callArgsP_two :
    RelCT isa (Two fun a t => At XP J3 a t ∧ isa.eval .e t = some false) (.block callArgsP) (Two (At XP J4P)) :=
  two_and (two_piece [.rsp] (pins_rsp fun _ _ _ h => J3_rsp h.1) (by taint_decide)
    fun _ t ⟨s, S, j, _⟩ => WP.mono (callArgsP_ok S.1.1 S.2.1 (J3_env S.1.1 j))
      fun _ ⟨he, hw, hdi, hsi, hdx, hcx, h8, h9, _, _⟩ => ⟨s, S, he, hw, hdi, hsi, hdx, hcx, h8, h9⟩)

/-- The modulus' values in `pre`, at the call. -/
theorem leak_entry {s t : State} (hq : PreP s) (he : EnvC s t) (rd wr : List Region) :
    Spec.Rsa.privatePrecomputedLeak (t.callEntry.withRegions rd wr).mem (stackArg s 15) (s.gpr .rcx).toNat =
      Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 15) (s.gpr .rcx).toNat := by
  have hfE : Frame [stkR s, outR s, scrR s] s.mem t.callEntry.mem :=
    frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr, below_kb]; exact .inl (Region.sub_prefix (by decide))
  have hle : Spec.Rsa.precomputedWords (s.gpr .rcx).toNat ≤ (stackArg s 16).toNat := by
    rw [hq.hpl]; unfold Spec.Rsa.privatePrecomputedWords; omega
  simp only [Spec.Rsa.privatePrecomputedLeak, State.withRegions_mem]
  rw [← VG.Proof.Rsa.wordsAt_take _ _ hle, ← VG.Proof.Rsa.wordsAt_take _ _ hle, wordsP_of_frame hq hfE]

theorem callP_ct (v : CrtImpl) :
    RelCT isa (Two (At XP J4P)) (.call (privNameP v) (privCodeP v)) fun _ _ => True := by
  refine RelCT.callEx (k := chkContractP) (codeP_correct v (pdName v))
    (Rsa.X86_64.codeP_constantTime v _)
    fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨he₁, hw₁, hdi₁, hsi₁, hdx₁, hcx₁, h8₁, h9₁⟩ := j₁
  obtain ⟨he₂, hw₂, hdi₂, hsi₂, hdx₂, hcx₂, h8₂, h9₂⟩ := j₂
  have hw14 : ∀ {s t : State}, (∀ i < 16, word t.mem (fb s) (8 * i) = callArgP s i) →
      ∀ i < 14, word t.mem (fb s) (8 * i) = callArg s i := fun hw i hi => by
    rw [hw i (by omega)]; simp only [callArgP, hi, ↓reduceIte]
  obtain ⟨r₁, g₁, n₁, e₁⟩ := privView_of (rds := privRdP s₁) S₁ he₁ (hw14 hw₁) hdi₁ hsi₁ hdx₁ hcx₁ h8₁ h9₁
  obtain ⟨r₂, g₂, n₂, e₂⟩ := privView_of (rds := privRdP s₂) S₂ he₂ (hw14 hw₂) hdi₂ hsi₂ hdx₂ hcx₂ h8₂ h9₂
  obtain ⟨c₁, w₁⟩ := privP_covers S₁.1.1 S₁.2.1 he₁
  obtain ⟨c₂, w₂⟩ := privP_covers S₂.1.1 S₂.2.1 he₂
  have a14 : ∀ {s t : State} (he : EnvC s t) (hw : ∀ i < 16, word t.mem (fb s) (8 * i) = callArgP s i),
      stackArg (t.callEntry.withRegions (privRdP s) (privWr s)) 14 = stackArg s 15 := fun he hw =>
    (stackArg_entry he.rsp _ _ (by decide)).trans (hw 14 (by decide))
  have a15 : ∀ {s t : State} (he : EnvC s t) (hw : ∀ i < 16, word t.mem (fb s) (8 * i) = callArgP s i),
      stackArg (t.callEntry.withRegions (privRdP s) (privWr s)) 15 = stackArg s 16 := fun he hw =>
    (stackArg_entry he.rsp _ _ (by decide)).trans (hw 15 (by decide))
  have kx : ∀ {s t : State}, t.gpr .rcx = s.gpr .rcx →
      ((t.callEntry.withRegions (privRdP s) (privWr s)).gpr .rcx) = s.gpr .rcx := fun h => by
    simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), h]
  exact ⟨privRdP s₁, privWr s₁, privRdP s₂, privWr s₂,
    privP_pre S₁.1.1 S₁.2.1 he₁ hw₁ hdi₁ hsi₁ hdx₁ hcx₁ h8₁ h9₁,
    privP_pre S₂.1.1 S₂.2.1 he₂ hw₂ hdi₂ hsi₂ hdx₂ hcx₂ h8₂ h9₂,
    ⟨⟨regs_eq (r₁.trans r₂.symm), g₁.trans g₂.symm, n₁.trans n₂.symm, e₁.trans e₂.symm⟩,
      by rw [a14 he₁ hw₁, a14 he₂ hw₂, S₁.2.2.1, S₂.2.2.1],
      by rw [a15 he₁ hw₁, a15 he₂ hw₂, S₁.2.2.2.1, S₂.2.2.2.1],
      by rw [a14 he₁ hw₁, a14 he₂ hw₂, kx hcx₁, kx hcx₂, leak_entry S₁.2.1 he₁,
        leak_entry S₂.2.1 he₂, S₁.2.2.2.2, S₂.2.2.2.2]⟩,
    c₁, w₁, c₂, w₂, by rw [he₁.rsp, he₂.rsp, S₁.fb, S₂.fb]⟩

theorem callP_two (v : CrtImpl) :
    RelCT isa (Two (At XP J4P)) (.call (privNameP v) (privCodeP v)) (Two (At XP J5)) :=
  two_post (callP_ct v) fun _ _ ⟨s, S, he, hw, hdi, hsi, hdx, hcx, h8, h9⟩ =>
    WP.mono (privP_call v S.1.1 S.2.1 he hw hdi hsi hdx hcx h8 h9) fun _ h => ⟨s, S, h.1⟩

/-! ## The composition -/

theorem afterEncP_ct (v : CrtImpl) :
    RelCT isa (Two (At XP J2)) (afterEncWith callArgsP (privNameP v) (privCodeP v)) fun _ _ => True := by
  unfold afterEncWith
  refine RelCT.seq test0_two (two_ite ?_ (two_and (zeroSlots_ct fun _ _ hs h => J3_env hs h.1))
    (RelCT.seq callArgsP_two (RelCT.seq (callP_two v) wipe_ct)))
  refine pinEval (fun s => some !(encOut s).isSome) (fun s t h => by
    obtain ⟨_, _, _, hz⟩ := h
    simp only [eval, hz]) ?_
  intro a s S
  rw [encOut_sib S]

theorem bodyP_ct (v : CrtImpl) :
    RelCT isa (Two (At XP JA)) (bodyP (privNameP v) (privCodeP v)) fun _ _ => True :=
  RelCT.seq head_two (RelCT.seq encode_two (afterEncP_ct v))

theorem codeP_ct (v : CrtImpl) :
    RelCT isa (Two (At XP J0)) (codeP (privNameP v) (privCodeP v)) fun _ _ => True := by
  unfold codeP
  refine relCT_alloc ((bodyP_ct v).mono ?_ fun _ _ h => h)
  rintro _ _ ⟨t₁, t₂, ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩, rfl, rfl⟩
  exact ⟨a, ⟨s₁, S₁, by rw [show t₁ = s₁ from j₁]; rfl⟩, ⟨s₂, S₂, by rw [show t₂ = s₂ from j₂]; rfl⟩⟩

/-- `vg_rsa_pkcs1_sign_precomputed` is constant time but for its public
data. -/
theorem codeP_constantTime (v : CrtImpl) :
    ConstantTime isa sigContractP.pre sigContractP.pub (codeP (privNameP v) (privCodeP v)) :=
  RelCT.constantTime ((codeP_ct v).mono
    (fun s₁ s₂ ⟨h₁, h₂, hpub, h15, h16, hl⟩ =>
      ⟨s₁, ⟨s₁, ⟨⟨(preSP_of h₁).1, pub_refl s₁⟩, (preSP_of h₁).2, rfl, rfl, rfl⟩, rfl⟩,
        ⟨s₂, ⟨⟨(preSP_of h₂).1, hpub⟩, (preSP_of h₂).2, h15.symm, h16.symm, hl.symm⟩, rfl⟩⟩) fun _ _ h => h)

/-! ## Correctness and the stack pointer -/

theorem codeP_correct' (v : CrtImpl) (s : State) (h : sigContractP.pre s) :
    ∃ t s', Exec isa (codeP (privNameP v) (privCodeP v)) s t s' ∧ abiPreserved s s' ∧ sigContractP.post s s' :=
  let ⟨hp, hq⟩ := preSP_of h
  let ⟨t, s', he, hq'⟩ := codeP_ok v hp hq
  ⟨t, s', he, hq'⟩

/-- It writes `rsp` only in its frame's push and pop, and its callee in its
own. -/
theorem codeP_spSafe (v : CrtImpl) :
    (codeP (privNameP v) (privCodeP v)).all (fun i => !isa.writesSp i) = true := by
  have h := Rsa.X86_64.codeP_spSafe v (pdName v)
  simp only [codeP, bodyP, afterEncWith, Code.all, privCodeP, h, Bool.true_and]
  decide +kernel

end VG.Proof.RsaPkcs1Sig.X86_64.Sgn
