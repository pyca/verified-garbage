module

public import VerifiedGarbage.Proof.AesOcb.PPC64LE.CTBase
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Seal
import VerifiedGarbage.Proof.AesOcb.PPC64LE.FrontCT
meta import VerifiedGarbage.Proof.AesOcb.PPC64LE.CTBase
meta import VerifiedGarbage.Proof.AesOcb.PPC64LE.FrontCT
meta import VerifiedGarbage.Proof.AesOcb.PPC64LE.Seal
meta import VerifiedGarbage.Impl.AesOcb.PPC64LE
meta import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# AES-OCB on PPC64LE: `vg_aes_ocb_seal` and `vg_aes_ocb_open` are constant time

Untrusted: everything here is checked by Lean. Two runs with the same public
arguments (`onePub`) have the same arguments of `front_rel` (`FnArgs`, with
the values of the first run). After `front`, `seal` copies the tag out and
restores our caller's registers; `open` copies the received tag, compares
it with the one it computed and masks the data without a branch, and
restores them: code without calls, which the taint analysis checks from the
public registers. `open` leaks nothing more than `seal`, in particular not
whether the tag is right.
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE

/-- `FnArgs` in two runs with the same public arguments, with the values of
the first. -/
theorem args₂_of {σ₁ σ₂ : State} (hq : onePub σ₁ σ₂)
    (A₂ : FnArgs σ₂ (σ₂.gpr .r3) (stackArg σ₂ 2) (σ₂.gpr .r5) (σ₂.gpr .r7) (σ₂.gpr .r9) (σ₂.gpr .r4).toNat
      (σ₂.gpr .r6).toNat (σ₂.gpr .r8).toNat (σ₂.gpr .r10).toNat (stackArg σ₂ 1).toNat (stackArg σ₂ 0)) :
    FnArgs σ₂ (σ₁.gpr .r3) (stackArg σ₁ 2) (σ₁.gpr .r5) (σ₁.gpr .r7) (σ₁.gpr .r9) (σ₁.gpr .r4).toNat
      (σ₁.gpr .r6).toNat (σ₁.gpr .r8).toNat (σ₁.gpr .r10).toNat (stackArg σ₁ 1).toNat (stackArg σ₁ 0) := by
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, -, qa⟩ := hq
  rw [← q3, ← q4, ← q5, ← q6, ← q7, ← q8, ← q9, ← q10, ← qa 0 (by decide), ← qa 1 (by decide),
    ← qa 2 (by decide)] at A₂
  exact A₂

/-- `front enc d; k` in two runs with the same public arguments. -/
theorem front_relq (enc : Bool) {d : Nat} (hd : d = tagO ∨ d = t2O) {k : Prog isa}
    (hk : ∃ h, (VG.Taint.check taint (Taint.ofRegs ([] ++ pubR)) k h).isSome = true) {σ₁ σ₂ : State}
    (A₁ : FnArgs σ₁ (σ₁.gpr .r3) (stackArg σ₁ 2) (σ₁.gpr .r5) (σ₁.gpr .r7) (σ₁.gpr .r9) (σ₁.gpr .r4).toNat
      (σ₁.gpr .r6).toNat (σ₁.gpr .r8).toNat (σ₁.gpr .r10).toNat (stackArg σ₁ 1).toNat (stackArg σ₁ 0))
    (A₂ : FnArgs σ₂ (σ₂.gpr .r3) (stackArg σ₂ 2) (σ₂.gpr .r5) (σ₂.gpr .r7) (σ₂.gpr .r9) (σ₂.gpr .r4).toNat
      (σ₂.gpr .r6).toNat (σ₂.gpr .r8).toNat (σ₂.gpr .r10).toNat (stackArg σ₂ 1).toNat (stackArg σ₂ 0))
    (hq : onePub σ₁ σ₂) : RelCT isa (Eq2 σ₁ σ₂) (.seq (front enc d) k) TT := by
  have A₂' := args₂_of hq A₂
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, qa⟩ := hq
  have o : ∀ x : BitVec 64, x = BitVec.ofNat 64 x.toNat := fun x => (ofNat_toNat64 x).symm
  have o' : ∀ {x y : BitVec 64}, x = y → y = BitVec.ofNat 64 x.toNat := fun h => by rw [h]; exact o _
  exact front_rel enc hd hk A₁ A₂' rfl rfl (o _) rfl (o _) rfl (o _) rfl (o _) rfl (o _)
    (qa 2 (by decide)).symm (qa 0 (by decide)).symm (o' (qa 1 (by decide))) q3.symm (o' q4) q5.symm (o' q6)
    q7.symm (o' q8) q9.symm (o' q10) qsp

theorem seal_ct : ConstantTime isa sealPPC64LE.pre sealPPC64LE.pub «seal» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  unfold «seal»
  refine front_relq true (.inl rfl) ?_ (sealArgs_of h₁) (sealArgs_of h₂) hq
  exact ⟨_, by taint_decide⟩

theorem open_ct : ConstantTime isa openPPC64LE.pre openPPC64LE.pub «open» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  unfold «open»
  refine front_relq false (.inr rfl) ?_ (openArgs_of h₁) (openArgs_of h₂) hq.1
  exact ⟨_, by taint_decide⟩

end VG.Proof.AesOcb.PPC64LE
