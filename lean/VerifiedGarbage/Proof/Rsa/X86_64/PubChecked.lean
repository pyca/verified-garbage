import VerifiedGarbage.Proof.Rsa.X86_64.Guarded
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
import VerifiedGarbage.Proof.Bignum.X86_64.PdVerified

/-!
# `vg_rsa_public_checked` and `vg_rsa_public_precomputed_checked` on x86-64

Each is `vg_rsa_public`'s or `vg_rsa_public_precomputed`'s code guarded by
the check of `e` (`guarded`), against the contracts on the registers of
those functions with the checked postcondition (`pubChkContract`,
`pdChkContract`), and from there against the shared contracts
(`publicChecked_verified`, `precomputedChecked_verified`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Checked
open VG.Proof.Bignum.X86_64

/-! ## The contracts on the registers -/

/-- `pubContract`, with BoringSSL's limits on `e` (`publicOpChecked`). -/
def pubChkContract : Contract isa where
  pre := pubContract.pre
  pub := pubContract.pub
  post s s' := Spec.Rsa.written s'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((s'.gpr .rax).setWidth 32)
      (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat))

/-- `pdContract`, with BoringSSL's limits on `e` (`publicOpChecked`). -/
def pdChkContract : Contract isa where
  pre := pdContract.pre
  pub := pdContract.pub
  post s s' := ∀ nB : List Byte, nB.length = (s.gpr .rsi).toNat →
      Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) →
      Spec.Rsa.written s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat ((s'.gpr .rax).setWidth 32)
        (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat))

/-! ## What the contracts read of a state -/

theorem stackArg_same {s t : State} (h : Same s t) (i : Nat) : stackArg t i = stackArg s i := by
  simp only [stackArg, stackArgAddr, h.rsp, h.mem]

theorem pubPre_same {s t : State} (h : Same s t) : pubContract.pre t = pubContract.pre s := by
  simp only [pubContract, stackArg_same h, stackArgAddr, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.rsp,
    h.rd, h.wr]

theorem pdPre_same {s t : State} (h : Same s t) : pdContract.pre t = pdContract.pre s := by
  simp only [pdContract, stackArg_same h, stackArgAddr, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.rsp,
    h.rd, h.wr]

theorem pubPub_same {s₁ s₂ t₁ t₂ : State} (h₁ : Same s₁ t₁) (h₂ : Same s₂ t₂) (h : pubContract.pub s₁ s₂) :
    pubContract.pub t₁ t₂ := by
  simp only [pubContract, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    stackArg_same h₁, stackArg_same h₂, h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₁.rsp, h₁.mem,
    h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9, h₂.rsp, h₂.mem] at h ⊢
  exact h

theorem pdPub_same {s₁ s₂ t₁ t₂ : State} (h₁ : Same s₁ t₁) (h₂ : Same s₂ t₂) (h : pdContract.pub s₁ s₂) :
    pdContract.pub t₁ t₂ := by
  simp only [pdContract, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    stackArg_same h₁, stackArg_same h₂, h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₁.rsp, h₁.mem,
    h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9, h₂.rsp, h₂.mem] at h ⊢
  exact h

theorem pub_rsi {s : State} (h : pubContract.pre s) : (s.gpr .rsi).toNat = (s.gpr .rcx).toNat := by
  simp only [pubContract] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hol, -⟩ := h
  exact hol

theorem pubGeom {s : State} (h : pubContract.pre s) : Geom s := by
  have c := codeCtx_of h
  have hsi := pub_rsi h
  have hk2 := c.hk2
  have hL2 := c.hL2
  refine ⟨by have := c.hk1; omega, by omega, fun j hj => c.hout j (by omega),
    fun b hb j hj => (c.hret b hb).2 j (by omega), c.hL1, by omega, fun i hi => c.heb.rd i (by
      rw [bytesAt_length]; exact hi)⟩

theorem pdGeom {s : State} (h : pdContract.pre s) : Geom s := by
  have c := pdCtx_of h
  have hk2 := c.hk2
  have hL2 := c.hL2
  exact ⟨by have := c.hk1; omega, by omega, c.hout, fun b hb j hj => (c.hret b hb).2 j hj, c.hL1, by omega,
    fun i hi => c.heb.rd i (by rw [bytesAt_length]; exact hi)⟩

/-! ## `vg_rsa_public_checked` -/

theorem publicChecked_correct (s : State) (h : pubContract.pre s) :
    ∃ t s', Exec isa publicChecked s t s' ∧ abiPreserved s s' ∧ pubChkContract.post s s' := by
  refine guarded_correct code_correct (fun _ h => pubGeom h) (fun s t hs h => (pubPre_same hs).symm ▸ h) ?_ ?_ s h
  · intro s t s' _ hs hv hp
    simp only [pubContract, stackArg_same hs, hs.rdi, hs.rdx, hs.rcx, hs.r8, hs.r9, hs.mem] at hp
    simp only [pubChkContract, Spec.Rsa.publicOpChecked]
    simp only [eValid, eBytes] at hv
    simp only [hv, ↓reduceIte]; exact hp
  · intro s s' h hv hb hax
    have hsi := pub_rsi h
    simp only [eValid, eBytes] at hv
    simp only [pubChkContract, Spec.Rsa.publicOpChecked, hv, Bool.false_eq_true, ite_false, Spec.Rsa.written, hax]
    exact ⟨rfl, by rw [← hsi]; exact hb⟩

theorem publicChecked_constantTime : ConstantTime isa pubContract.pre pubContract.pub publicChecked :=
  guarded_ct code_constantTime (fun _ h => pubGeom h) (fun s t hs h => (pubPre_same hs).symm ▸ h)
    (fun _ _ _ _ hp => ⟨fun r hr => hp.1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp), hp.2.2.2.2.2.2⟩)
    fun _ _ _ _ h₁ h₂ hp => pubPub_same h₁ h₂ hp

theorem publicChecked_implies : pubChkContract.Implies (Spec.Rsa.publicCheckedContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argRegs, pubChkContract, pubContract, stackArgs_four, List.append_eq] at h
    sig_pre [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argRegs, pubChkContract, pubContract, stackArgs_four, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argRegs, pubChkContract, pubContract, stackArgs_four, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argRegs, pubChkContract, pubContract, stackArgs_four, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argRegs, pubChkContract, pubContract, stackArgs_four, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3⟩ := h
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hl
    refine ⟨?_, a0, a1, a2, a3, hn, he⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argRegs, pubChkContract, pubContract, stackArgs_four, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

theorem publicChecked_verified : Verified target publicChecked (Spec.Rsa.publicCheckedContract abi) :=
  have hct : ConstantTime isa pubChkContract.pre pubChkContract.pub publicChecked := publicChecked_constantTime
  Verified.of_correct (k := pubChkContract) publicChecked_correct hct publicChecked_implies

/-! ## `vg_rsa_public_precomputed_checked` -/

theorem precomputedChecked_correct (M : Mont)
    (hmx : (Precomputed.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true) (s : State) (h : pdContract.pre s) :
    ∃ t s', Exec isa (precomputedChecked M.mm) s t s' ∧ abiPreserved s s' ∧ pdChkContract.post s s' := by
  refine guarded_correct (pdCode_correct M hmx) (fun _ h => pdGeom h) (fun s t hs h => (pdPre_same hs).symm ▸ h)
    ?_ ?_ s h
  · intro s t s' _ hs hv hp nB hl hpre
    simp only [pdContract, stackArg_same hs, hs.rdi, hs.rsi, hs.rdx, hs.rcx, hs.r8, hs.r9, hs.mem] at hp
    simp only [eValid, eBytes] at hv
    simp only [Spec.Rsa.publicOpChecked, hv, ↓reduceIte]
    exact hp nB hl hpre
  · intro s s' h hv hb hax nB _ _
    simp only [eValid, eBytes] at hv
    simp only [Spec.Rsa.publicOpChecked, hv, Bool.false_eq_true, ite_false, Spec.Rsa.written, hax]
    exact ⟨rfl, hb⟩

theorem precomputedChecked_constantTime (M : Mont) :
    ConstantTime isa pdContract.pre pdContract.pub (precomputedChecked M.mm) :=
  guarded_ct (pdCode_constantTime (M := M)) (fun _ h => pdGeom h) (fun s t hs h => (pdPre_same hs).symm ▸ h)
    (fun _ _ _ _ hp => ⟨fun r hr => hp.1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp), hp.2.2.2.2.2.2⟩)
    fun _ _ _ _ h₁ h₂ hp => pdPub_same h₁ h₂ hp

theorem precomputedChecked_implies :
    pdChkContract.Implies (Spec.Rsa.publicPrecomputedCheckedContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, pdChkContract, pdContract, stackArgs_four, List.append_eq] at h
    sig_pre [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, pdChkContract, pdContract, stackArgs_four, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, pdChkContract, pdContract, stackArgs_four, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, pdChkContract, pdContract, stackArgs_four, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, pdChkContract, pdContract, stackArgs_four, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3⟩ := h
    obtain ⟨hw, he⟩ := leak_eq2 (by simp [Spec.Rsa.wordsAt, hcx]) hl
    refine ⟨?_, a0, a1, a2, a3, hw, he⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, pdChkContract, pdContract, stackArgs_four, List.append_eq] [pdSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using pdSatState

/-- `vg_rsa_public_precomputed_checked` with Montgomery multiplication `M`,
given that its code never loads MXCSR (which the registration file
evaluates). -/
theorem precomputedChecked_verified (M : Mont)
    (hmx : (Precomputed.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (precomputedChecked M.mm) (Spec.Rsa.publicPrecomputedCheckedContract abi) :=
  have hct : ConstantTime isa pdChkContract.pre pdChkContract.pub (precomputedChecked M.mm) :=
    precomputedChecked_constantTime M
  Verified.of_correct (k := pdChkContract) (precomputedChecked_correct M hmx) hct precomputedChecked_implies

end VG.Proof.Rsa.X86_64
