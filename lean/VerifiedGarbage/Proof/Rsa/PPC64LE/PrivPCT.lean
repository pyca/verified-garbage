module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCT
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPreCopy
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Rsa.Contract

/-!
# `vg_rsa_private_checked_precomputed` on PPC64LE: constant time, and the contract on the registers

Its public data (`dataOfP`) adds `pre` and `pre_len` and the modulus' values
in `pre` to `vg_rsa_private_checked`'s; the chain is `vg_rsa_private_checked`'s
(`codeG_rel`), with `n`'s values copied from `pre` (`step_rel_true`).
`fnContractP` states the contract on the registers and the stack.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Two)

/-- The public data. -/
def dataOfP (s : State) : Data :=
  (argRegs.map s.gpr, (List.range 14).map (stackArg s),
    (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat ++ Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat).map
      (·.toNat) ++ Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 12) (s.gpr .r6).toNat, s.sp)

theorem pub_dataP {s₁ s₂ : State} (h : (Proof.Rsa.privateCheckedPrecomputedContract abi frameBytes).pub s₁ s₂) :
    dataOfP s₁ = dataOfP s₂ := by
  have e : frameBytes = 3327 + 1 := rfl
  rw [e] at h
  sig_pub [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, abi, argRegs, stackArgs_fourteen, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := h
  unfold dataOfP
  rw [hl]
  simp only [argRegs, List.map_cons, List.map_nil, stackArgs_fourteen, h3, h4, h5, h6, h7, h8, h9, h10, a0,
    a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, hsp]

/-- The public data, from its facts. -/
theorem pub_ofP {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp) (hr : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r)
    (ha : ∀ i < 14, stackArg s₁ i = stackArg s₂ i)
    (hn : Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r5) (s₁.gpr .r6).toNat = Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r5) (s₂.gpr .r6).toNat)
    (he : Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r7) (s₁.gpr .r8).toNat = Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r7) (s₂.gpr .r8).toNat)
    (hp : Spec.Rsa.privatePrecomputedLeak s₁.mem (stackArg s₁ 12) (s₁.gpr .r6).toNat =
      Spec.Rsa.privatePrecomputedLeak s₂.mem (stackArg s₂ 12) (s₂.gpr .r6).toNat) :
    (Proof.Rsa.privateCheckedPrecomputedContract abi frameBytes).pub s₁ s₂ := by
  have e : frameBytes = 3327 + 1 := rfl
  rw [e]
  sig_pub [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, abi, argRegs, stackArgs_fourteen, List.append_eq]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  exact ⟨hsp, by rw [hn, he, hp], hr .r3 (by decide), hr .r4 (by decide), hr .r5 (by decide), hr .r6 (by decide),
    hr .r7 (by decide), hr .r8 (by decide), hr .r9 (by decide), hr .r10 (by decide), ha 0 (by decide),
    ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide), ha 5 (by decide), ha 6 (by decide),
    ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide), ha 11 (by decide), ha 12 (by decide),
    ha 13 (by decide)⟩

theorem same_ofP {s₁ s₂ : State} (h : dataOfP s₁ = dataOfP s₂) : Same true s₁ s₂ := by
  simp only [dataOfP, Prod.mk.injEq] at h
  obtain ⟨hr, ha, hb, hsp⟩ := h
  have gr : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r := List.map_inj_left.mp hr
  have ga : ∀ i < 14, stackArg s₁ i = stackArg s₂ i := fun i hi => List.map_inj_left.mp ha i (List.mem_range.mpr hi)
  have h6 : s₁.gpr .r6 = s₂.gpr .r6 := gr _ (by decide)
  have h8 : s₁.gpr .r8 = s₂.gpr .r8 := gr _ (by decide)
  obtain ⟨hne, hpre⟩ := List.append_inj hb (by simp [Proof.Rsa.bytesAt_length', h6, h8])
  rw [List.map_append, List.map_append] at hne
  obtain ⟨hn, he⟩ := List.append_inj hne (by simp [Proof.Rsa.bytesAt_length', h6])
  refine ⟨gr, fun i hi => ga i (by omega), hsp, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hn,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 he, fun _ => ga 12 (by decide), ?_⟩
  simp only [preVal, ↓reduceIte]
  simp only [Spec.Rsa.privatePrecomputedLeak] at hpre
  rw [← h6, ← ga 12 (by decide)] at hpre ⊢
  exact (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hpre

/-- On entry, with the public data `d`. -/
def Φ0P (d : Data) (s : State) : Prop :=
  (Proof.Rsa.privateCheckedPrecomputedContract abi frameBytes).pre s ∧ dataOfP s = d

theorem entry_okP : EntryOk true Φ0P :=
  ⟨fun _ _ φ => (preP_ofP φ.1).1, fun _ _ _ φ₁ φ₂ => same_ofP (φ₁.2.trans φ₂.2.symm)⟩

theorem codeP_ct : ConstantTime isa (Proof.Rsa.privateCheckedPrecomputedContract abi frameBytes).pre
    (Proof.Rsa.privateCheckedPrecomputedContract abi frameBytes).pub codeP :=
  RelCT.constantTime ((codeG_rel entry_okP (step_rel_true entry_okP fun _ _ φ => (preP_ofP φ.1).2)).mono
    (fun s _ ⟨hs, ht, hp⟩ => ⟨dataOfP s, ⟨hs, rfl⟩, ⟨ht, (pub_dataP hp).symm⟩, (same_ofP (pub_dataP hp)).sp⟩)
    fun _ _ h => h)

/-- The contract, its postcondition on the registers and the stack. -/
def fnContractP : Contract isa where
  pre := (Proof.Rsa.privateCheckedPrecomputedContract abi frameBytes).pre
  post := fnPost
  pub := (Proof.Rsa.privateCheckedPrecomputedContract abi frameBytes).pub

end VG.Proof.Rsa.PPC64LE.Priv
