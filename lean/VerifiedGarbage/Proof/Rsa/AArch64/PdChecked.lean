import VerifiedGarbage.Proof.Rsa.AArch64.Guarded
import VerifiedGarbage.Proof.Bignum.AArch64.PdCT
import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_public_precomputed_checked` on AArch64

`vg_rsa_public_precomputed`'s code guarded by the check of `e` (`guarded`),
against the contract on the registers with the checked postcondition
(`pdChkContract`), and from there against the shared contract
(`precomputedChecked_verified`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Checked
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

/-- `pdContract`, with BoringSSL's limits on `e` (`publicOpChecked`). -/
def pdChkContract : Contract isa where
  pre := pdContract.pre
  pub := pdContract.pub
  post s s' := ∀ nB : List Byte, nB.length = (s.gpr .x1).toNat →
      Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) →
      Spec.Rsa.written s'.mem (s.gpr .x0) (s.gpr .x1).toNat ((s'.gpr .x0).setWidth 32)
        (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x1).toNat))

/-! ## What the contract reads of a state -/

theorem stackArg_same {s t : State} (h : Same s t) (i : Nat) : stackArg t i = stackArg s i := by
  simp only [stackArg, stackArgAddr, h.sp, h.mem]

theorem pdPre_same {s t : State} (h : Same s t) : pdContract.pre t = pdContract.pre s := by
  simp only [pdContract, pdArgs, stackArg_same h, stackArgAddr, h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, h.x6, h.x7, h.sp,
    h.rd, h.wr]

theorem pdPub_same {s₁ s₂ t₁ t₂ : State} (h₁ : Same s₁ t₁) (h₂ : Same s₂ t₂) (h : pdContract.pub s₁ s₂) :
    pdContract.pub t₁ t₂ := by
  simp only [pdContract, stackArg_same h₁, stackArg_same h₂, h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₁.x4, h₁.x5, h₁.x6,
    h₁.x7, h₁.sp, h₁.mem, h₂.x0, h₂.x1, h₂.x2, h₂.x3, h₂.x4, h₂.x5, h₂.x6, h₂.x7, h₂.sp, h₂.mem] at h ⊢
  exact h

theorem pdGeom {s : State} (h : pdContract.pre s) : Geom s := by
  have c := pdCtx_of h
  have hk2 := c.hk2
  have hL2 := c.hL2
  exact ⟨by have := c.hk1; omega, by omega, c.hout, c.hL1, by omega,
    fun i hi => c.heb.rd i (by rw [bytesAt_length]; exact hi)⟩

/-! ## `vg_rsa_public_precomputed_checked` -/

theorem precomputedChecked_correct (M : Mont) (s : State) (h : pdContract.pre s) :
    ∃ t s', Exec isa (precomputedChecked M.mm) s t s' ∧ abiPreserved s s' ∧ pdChkContract.post s s' := by
  refine guarded_correct (pdCode_correct M) (fun _ h => pdGeom h) (fun s t hs h => (pdPre_same hs).symm ▸ h)
    ?_ ?_ s h
  · intro s t s' _ hs hv hp nB hl hpre
    simp only [pdContract, hs.x0, hs.x1, hs.x2, hs.x3, hs.x4, hs.x5, hs.x6, hs.mem] at hp
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
    (fun _ _ _ _ hp => ⟨hp.1, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.2.1
      · exact hp.2.2.1
      · exact hp.2.2.2.2.2.1
      · exact hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2⟩)
    fun _ _ _ _ h₁ h₂ hp => pdPub_same h₁ h₂ hp

/-- A state meeting `pdContract.pre`: a 512-bit modulus, a one-byte
exponent, and the stack arguments at `0x6000`. -/
def pdSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 16 | .x4 => 0x3000 | .x5 => 1 | .x6 => 0x4000
    | .x7 => 64 | _ => 0
  sp := 0x6000
  mem a := if a = 0x6001 then 0x80 else if a = 0x6009 then 0x04 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 1⟩, ⟨0x4000, 64⟩, ⟨0x6000, 16⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩]

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

theorem precomputedChecked_implies :
    pdChkContract.Implies (Spec.Rsa.publicPrecomputedCheckedContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, pdChkContract,
      pdContract, pdArgs, stackArgs_two, List.append_eq] at h
    sig_pre [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, pdChkContract,
      pdContract, pdArgs, stackArgs_two, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs,
      pdChkContract, pdContract, pdArgs, stackArgs_two, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs,
    pdChkContract, pdContract, pdArgs, stackArgs_two, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, pdChkContract,
      pdContract, pdArgs, stackArgs_two, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, a0, a1, a2, a3, a4, a5, a6, a7, s0, s1⟩ := h
    obtain ⟨hw, he⟩ := leak_eq2 (by simp [Spec.Rsa.wordsAt, a3]) hl
    exact ⟨hsp, a0, a1, a2, a3, a4, a5, a6, a7, s0, s1, hw, he⟩
  sat := by sig_implies_sat [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs,
    pdChkContract, pdContract, pdArgs, stackArgs_two, List.append_eq] [pdSatState, stackArg, stackArgAddr, Mem.readW,
    Mem.read] using pdSatState

/-- `vg_rsa_public_precomputed_checked` with Montgomery multiplication `M`. -/
theorem precomputedChecked_verified (M : Mont) :
    Verified target (precomputedChecked M.mm) (Spec.Rsa.publicPrecomputedCheckedContract abi) :=
  have hct : ConstantTime isa pdChkContract.pre pdChkContract.pub (precomputedChecked M.mm) :=
    precomputedChecked_constantTime M
  Verified.of_correct (k := pdChkContract) (precomputedChecked_correct M) hct precomputedChecked_implies

end VG.Proof.Rsa.AArch64
