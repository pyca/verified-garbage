module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCT5
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecPCall
import VerifiedGarbage.Proof.Rsa.X86_64.PrivPCT
import VerifiedGarbage.Proof.Rsa.PreWords
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Alloc
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCT5
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecPCall
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivPCT
meta import VerifiedGarbage.Proof.Rsa.PreWords
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Alloc
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# `vg_rsa_pkcs1_decrypt_precomputed` on x86-64: constant time

`Decrypt.codeP` leaks what `Decrypt.code` leaks, and, in its call of
`vg_rsa_private_checked_precomputed`, `pre`'s address and length and the
modulus' values in it, which its contract (`decKP`) makes public: `stash`
and `restore` address only the frame and the stack arguments, the call is
constant time for its contract (`privP_ct`), and the rest is `code`'s
(`DecCT1.lean` … `DecCT5.lean`), with entry states that also agree on `pre`
(`XPd`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64
open VG.Proof.Rsa.X86_64 (CrtImpl chkContract chkContractP codeP_correct)
open VG.Proof.Sha256.X86_64 (Compress)

/-- `vg_rsa_pkcs1_decrypt_precomputed`'s contract, with `decK`'s
postcondition and its public data, with `pre`, `pre_len` and the modulus'
values in `pre`. -/
def decKP : Contract isa where
  pre := (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi decStack).pre
  post := decK.post
  pub s₁ s₂ := decK.pub s₁ s₂ ∧ stackArg s₁ 17 = stackArg s₂ 17 ∧ stackArg s₁ 18 = stackArg s₂ 18 ∧
    Spec.Rsa.privatePrecomputedLeak s₁.mem (stackArg s₁ 17) (s₁.gpr .r8).toNat =
      Spec.Rsa.privatePrecomputedLeak s₂.mem (stackArg s₂ 17) (s₂.gpr .r8).toNat

/-- What entry states agree on with `a` besides `decK.pub`. -/
def XPd (a s : State) : Prop :=
  DPreP s ∧ stackArg s 17 = stackArg a 17 ∧ stackArg s 18 = stackArg a 18 ∧
    Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 17) (s.gpr .r8).toNat =
      Spec.Rsa.privatePrecomputedLeak a.mem (stackArg a 17) (a.gpr .r8).toNat

def J0P (s t : State) : Prop := J0 s t ∧ DPreP s
def JSP (s t : State) : Prop := (SetupP s t ∧ CS s t) ∧ DPreP s
def JPC (s t : State) : Prop := ∃ t₀, SetupP s t₀ ∧ PostCall s t₀ t ∧ CS s t

theorem setupP_two : RelCT isa (Two (At XPd J0P)) (.block (setup ++ stash)) (Two (At XPd JSP)) :=
  two_blk [.rsp] (pins (J := J0P) [(.rsp, fb)] (by
      simp only [List.mem_singleton]; rintro p rfl s t ⟨h, -⟩; rw [h]; rfl)
    (by simp only [List.mem_singleton]; rintro p rfl; exact fb_pin)) (by taint_decide)
    fun s t hp ⟨h, hq⟩ => by
      subst h
      rw [WP.block_append_iff]
      exact WP.mono (WP.keep [.rax, .rsi, .rdx, .rcx, .r8, .r9] (setup_run hp) (by decide +kernel))
        fun t₁ ⟨h₁, k₁⟩ => WP.mono (stash_ok hp hq h₁) fun t' ⟨h', k'⟩ => ⟨⟨h', fun r hr hr' => by
          rw [k'.cs (by decide) r hr, k₁.cs (by decide) r hr]; simp only [allocState_gpr, hr', ↓reduceIte]⟩, hq⟩

/-- The modulus' values in `pre`, at the call. -/
theorem leakP_entry {s t : State} (hq : DPreP s) (h : CallAt s t) (rd wr : List Region) :
    Spec.Rsa.privatePrecomputedLeak (t.callEntry.withRegions rd wr).mem (stackArg s 17) (s.gpr .r8).toNat =
      Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 17) (s.gpr .r8).toNat := by
  have hfE : Frame (wrs s) s.mem t.callEntry.mem :=
    frame_call (frame_of_outside h.out) (callEntry_frame h.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨stkR s, List.mem_cons_self .., below_sub s (by decide)⟩
  have hle : Spec.Rsa.precomputedWords (s.gpr .r8).toNat ≤ (stackArg s 18).toNat := by
    rw [hq.hpl]; unfold Spec.Rsa.privatePrecomputedWords; omega
  simp only [Spec.Rsa.privatePrecomputedLeak, State.withRegions_mem]
  rw [← VG.Proof.Rsa.wordsAt_take _ _ hle, ← VG.Proof.Rsa.wordsAt_take _ _ hle, wordsP_of_frame hq hfE]

theorem privP_ct (c : CrtImpl) :
    RelCT isa (Two (At XPd JSP)) (.call (privNameP c) (privCodeP c)) fun _ _ => True := by
  refine RelCT.callEx (k := chkContractP) (codeP_correct c _) (Rsa.X86_64.codeP_constantTime c _)
    fun t₁ t₂ ⟨a, ⟨s₁, S₁, ⟨j₁, _⟩, hq₁⟩, ⟨s₂, S₂, ⟨j₂, _⟩, hq₂⟩⟩ => ?_
  obtain ⟨r₁, a₁, n₁, e₁⟩ := priv_view (rds := privRdP s₁) S₁ j₁.call
  obtain ⟨r₂, a₂, n₂, e₂⟩ := priv_view (rds := privRdP s₂) S₂ j₂.call
  obtain ⟨c₁, w₁⟩ := privP_covers S₁.p hq₁ j₁.call
  obtain ⟨c₂, w₂⟩ := privP_covers S₂.p hq₂ j₂.call
  have a14 : ∀ {s t : State}, SetupP s t → stackArg (t.callEntry.withRegions (privRdP s) (privWr s)) 14 =
      stackArg s 17 := fun h => (stackArg_entry h.call.rsp _ _ (by decide)).trans h.a14
  have a15 : ∀ {s t : State}, SetupP s t → stackArg (t.callEntry.withRegions (privRdP s) (privWr s)) 15 =
      stackArg s 18 := fun h => (stackArg_entry h.call.rsp _ _ (by decide)).trans h.a15
  have kx : ∀ {s t : State}, SetupP s t →
      (t.callEntry.withRegions (privRdP s) (privWr s)).gpr .rcx = s.gpr .r8 := fun h => by
    simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), h.call.rcx]
  exact ⟨privRdP s₁, privWr s₁, privRdP s₂, privWr s₂, privP_pre S₁.p hq₁ j₁, privP_pre S₂.p hq₂ j₂,
    ⟨⟨List.map_inj_left.mp (r₁.trans r₂.symm), a₁.trans a₂.symm, n₁.trans n₂.symm, e₁.trans e₂.symm⟩,
      by rw [a14 j₁, a14 j₂, S₁.2.2.1, S₂.2.2.1], by rw [a15 j₁, a15 j₂, S₁.2.2.2.1, S₂.2.2.2.1],
      by rw [a14 j₁, a14 j₂, kx j₁, kx j₂, leakP_entry hq₁ j₁.call, leakP_entry hq₂ j₂.call, S₁.2.2.2.2,
        S₂.2.2.2.2]⟩,
    c₁, w₁, c₂, w₂, by rw [j₁.call.rsp, j₂.call.rsp, S₁.fb, S₂.fb]⟩

theorem privP_two (c : CrtImpl) :
    RelCT isa (Two (At XPd JSP)) (.call (privNameP c) (privCodeP c)) (Two (At XPd JPC)) :=
  two_then (privP_ct c) fun _ t hp ⟨⟨h, hcs⟩, hq⟩ => WP.mono (privP_call c hp hq h) fun _ ⟨pc, hcs', _⟩ =>
    ⟨t, h, pc, fun r hr hr' => (hcs' r hr).trans (hcs r hr hr')⟩

theorem restore_two : RelCT isa (Two (At XPd JPC)) (.block restore) (Two (At XPd JP)) :=
  two_blk [.rsp] (pins (J := JPC) [(.rsp, fb)] (by
      simp only [List.mem_singleton]; rintro p rfl s t ⟨_, _, pc, _⟩; exact pc.rsp)
    (by simp only [List.mem_singleton]; rintro p rfl; exact fb_pin)) (by taint_decide)
    fun s t hp ⟨t₀, h, pc, hcs⟩ => WP.mono (restore_ok hp h pc) fun _ ⟨hpp, k⟩ =>
      ⟨hpp, fun r hr hr' => (k.cs (by decide) r hr).trans (hcs r hr hr')⟩

/-! ## The function -/

theorem bodyP_ct (v : Compress) (c : CrtImpl) :
    RelCT isa (Two (At XPd J0P)) (bodyP (HH v) (privNameP c) (privCodeP c)) fun _ _ => True :=
  RelCT.seq setupP_two (RelCT.seq (RelCT.seq (privP_two c) restore_two) (RelCT.seq dBuild_two (RelCT.seq hashD_two
    (RelCT.seq kdkMac_two (RelCT.seq clLoop_two (RelCT.seq amLoop_two (RelCT.seq maskPart_two
    (RelCT.seq alPart_two (RelCT.seq scanPart_two selPart_ct)))))))))

/-- `vg_rsa_pkcs1_decrypt_precomputed` is constant time but for its public
data. -/
theorem decP_constantTime (v : Compress) (c : CrtImpl) :
    ConstantTime isa decKP.pre decKP.pub (codeP (HH v) (privNameP c) (privCodeP c)) :=
  RelCT.constantTime (relCT_alloc ((bodyP_ct v c).mono
    (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub, h17, h18, hl⟩, e₁, e₂⟩ =>
      ⟨s₁, ⟨s₁, ⟨⟨(dPreP_of h₁).1, pub_refl s₁⟩, (dPreP_of h₁).2, rfl, rfl, rfl⟩, e₁, (dPreP_of h₁).2⟩,
        ⟨s₂, ⟨⟨(dPreP_of h₂).1, hpub⟩, (dPreP_of h₂).2, h17.symm, h18.symm, hl.symm⟩, e₂, (dPreP_of h₂).2⟩⟩)
    fun _ _ h => h))

theorem decP_correct (v : Compress) (c : CrtImpl) (s : State) (h : decKP.pre s) :
    ∃ t s', Exec isa (codeP (HH v) (privNameP c) (privCodeP c)) s t s' ∧ abiPreserved s s' ∧ decKP.post s s' :=
  let ⟨hp, hq⟩ := dPreP_of h
  let ⟨t, s', he, hq'⟩ := decP_ok v c hp hq
  ⟨t, s', he, hq'⟩

/-- It writes `rsp` only in its frame's push and pop, and its callees' own. -/
theorem decP_spSafe (v : Compress) (c : CrtImpl) :
    (codeP (HH v) (privNameP c) (privCodeP c)).all (fun i => !isa.writesSp i) = true := by
  have h := afterPriv_spSafe v
  have h2 := Rsa.X86_64.codeP_spSafe c c.pubOp.name
  simp only at h h2
  simp only [codeP, bodyP, privCodeP, Code.all, h, h2, Bool.and_true]
  decide +kernel

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
