module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCT
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPreCopy
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Rsa.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivTaint
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCT
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCorrect
import VerifiedGarbage.Proof.Framework.Offset

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
open VG.Proof.Bignum.PPC64LE (Two Keep two_post)

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
  refine ⟨gr, fun i hi => ga i (by omega_using [hi]), hsp, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hn,
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

/-- What `crtPtr` leaves: from the state `t` at the call of the CRT, `u`. -/
def PtrAt (s t u : State) : Prop :=
  AtCrt s t ∧ Keep [.r0, .r12, .r31] t u ∧ u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oR31) (s.gpr .r31) ∧
    u.sp = t.sp ∧ u.gpr .r31 = stackArg s 12 + BitVec.ofNat 64 (8 * Spec.Rsa.precomputedWords (s.gpr .r6).toNat)

theorem crt_pubP {s₁ s₂ t₁ t₂ u₁ u₂ : State} (h₁ : PreP true s₁) (h₂ : PreP true s₂) (S : Same true s₁ s₂)
    (P₁ : PtrAt s₁ t₁ u₁) (P₂ : PtrAt s₂ t₂ u₂) :
    Proof.Bignum.PPC64LE.Crt.fnContractP.pub (crtEntryG s₁ u₁ [r2Rs s₁]) (crtEntryG s₂ u₂ [r2Rs s₂]) := by
  have hpsa : ∀ {s t u : State}, PtrAt s t u →
      ∀ i < 10, u.mem.readW (fb s + BitVec.ofNat 64 (96 + 8 * i)) 64 = stackArg s (2 + i) :=
    fun ⟨A, _, hm, _, _⟩ i hi => by
      rw [hm, Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oR31; omega_using [hi]))
        (by omega_using [hi]) (by unfold oR31; omega_using [])) (by decide)]
      exact A.psa i hi
  have g : ∀ {s t u : State}, PtrAt s t u → ∀ r, r ∉ linkRegs → r ∉ [Reg.r0, .r12, .r31] →
      (crtEntryG s u [r2Rs s]).gpr r = t.gpr r := fun ⟨_, k, _⟩ r h1 h2 =>
    (State.callEntry_gpr _ h1).trans (k.gpr _ h2)
  have hn : ∀ {s t u : State}, PreP true s → PtrAt s t u →
      Spec.Rsa.bytesAt u.mem (s.gpr .r5) (s.gpr .r6).toNat = Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat :=
    fun {s t u} h P => by
      obtain ⟨A, _, hm, _, _⟩ := P
      have hk := h.k2
      have hfu : Frame [kR s] s.mem u.mem := by
        rw [hm]
        exact A.mem.writeW (List.mem_singleton_self _) _ (frame_contains _ (by unfold oR31 frameBytes; omega_using []))
      exact bytes_of_frame hfu (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.kn.symm)
        (by have := h.wn; omega_using [])
  have hl : ∀ {s t u : State}, PtrAt s t u →
      (List.range 10).map (stackArg (crtEntryG s u [r2Rs s])) = (List.range 10).map fun i => stackArg s (2 + i) :=
    fun P => List.map_congr_left fun i hi => crtEntryG_stackArg P.1 (hpsa P) P.2.2.2.1 (List.mem_range.mp hi)
  have sp : ∀ {s t u : State}, PtrAt s t u → (crtEntryG s u [r2Rs s]).sp = fb s := fun P => P.2.2.2.1.trans P.1.sp
  refine ⟨⟨fun r hr => ?_, by rw [sp P₁, sp P₂, fb_same S], ?_, ?_⟩, ?_⟩
  · rw [g P₁ r (fun h => by revert r; decide) (fun h => by revert r; decide),
      g P₂ r (fun h => by revert r; decide) (fun h => by revert r; decide)]
    obtain ⟨A₁, -⟩ := P₁
    obtain ⟨A₂, -⟩ := P₂
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [A₁.r3, A₂.r3, fb_same S]
    · rw [A₁.r4, A₂.r4, r_same S]
    · rw [A₁.r5, A₂.r5, r_same S]
    · rw [A₁.r6, A₂.r6, r_same S]
    · rw [A₁.r7, A₂.r7, r_same S]
    · rw [A₁.r8, A₂.r8, r_same S]
    · rw [A₁.r9, A₂.r9, S.arg 0 (by decide)]
    · rw [A₁.r10, A₂.r10, S.arg 1 (by decide)]
  · rw [hl P₁, hl P₂]
    exact List.map_congr_left fun i hi => S.arg (2 + i) (by have := List.mem_range.mp hi; omega_using [this])
  · have A₁ := P₁.1
    have A₂ := P₂.1
    simp only [State.withRegions_mem, State.callEntry_mem, g P₁ .r5 (by decide) (by decide),
      g P₁ .r6 (by decide) (by decide), g P₂ .r5 (by decide) (by decide), g P₂ .r6 (by decide) (by decide)]
    rw [A₁.r5, A₁.r6, A₂.r5, A₂.r6, hn h₁ P₁, hn h₂ P₂]
    exact S.n
  · have e1 : (crtEntryG s₁ u₁ [r2Rs s₁]).gpr .r31 = _ := (State.callEntry_gpr u₁ (by decide)).trans P₁.2.2.2.2
    have e2 : (crtEntryG s₂ u₂ [r2Rs s₂]).gpr .r31 = _ := (State.callEntry_gpr u₂ (by decide)).trans P₂.2.2.2.2
    rw [e1, e2, S.arg12 rfl, r_same S (r := .r6)]

section

variable {D : Type} {E : D → State → Prop}

def ΨP (E : D → State → Prop) (d : D) (u : State) : Prop := ∃ s t, E d s ∧ PtrAt s t u
def ΨA (E : D → State → Prop) (d : D) (v : State) : Prop := ∃ s, E d s ∧ AfterP s v

theorem callP_rel (hE : EntryOk true E) (hX : ∀ d s, E d s → PreX s) :
    RelCT isa (Two (ΨP E)) crtCallP fun _ _ => True := by
  unfold crtCallP
  refine RelCT.callEx Proof.Bignum.PPC64LE.Crt.fn_correctP Proof.Bignum.PPC64LE.Crt.fn_ctP
    fun u₁ u₂ ⟨_, ⟨s₁, t₁, φ₁, P₁⟩, ⟨s₂, t₂, φ₂, P₂⟩, _⟩ => ?_
  have h₁ := hE.pre _ _ φ₁
  have h₂ := hE.pre _ _ φ₂
  obtain ⟨A₁, k₁, m₁, sp₁, r₁⟩ := P₁
  obtain ⟨A₂, k₂, m₂, sp₂, r₂⟩ := P₂
  exact ⟨crtRd s₁ ++ [r2Rs s₁], crtWr s₁, crtRd s₂ ++ [r2Rs s₂], crtWr s₂,
    crt_preP h₁ (hX _ _ φ₁) A₁ k₁ m₁ sp₁ r₁, crt_preP h₂ (hX _ _ φ₂) A₂ k₂ m₂ sp₂ r₂,
    crt_pubP h₁ h₂ (hE.same _ _ _ φ₁ φ₂) ⟨A₁, k₁, m₁, sp₁, r₁⟩ ⟨A₂, k₂, m₂, sp₂, r₂⟩,
    (coversP h₁ (hX _ _ φ₁) A₁ k₁).1, (coversP h₁ (hX _ _ φ₁) A₁ k₁).2,
    (coversP h₂ (hX _ _ φ₂) A₂ k₂).1, (coversP h₂ (hX _ _ φ₂) A₂ k₂).2⟩

/-- `vg_rsa_private_crt_precomputed`, given the primes' values in `r31`. -/
theorem crt_step_rel_true (hE : EntryOk true E) (hX : ∀ d s, E d s → PreX s) :
    RelCT isa (Two (Ψ1 E)) (crtStep true) (Two (Ψ2 E)) := by
  show RelCT isa _ (.seq (.block crtPtr) (.seq crtCallP (.block crtRestore))) _
  exact RelCT.seq (two_post (Ψ := ΨP E) (crtPtr_taint (Ψ1 E)) fun _ _ ⟨s, φ, A⟩ =>
      WP.mono (crtPtr_ok (hE.pre _ _ φ) A) fun _ ⟨⟨h31, hm, hsp⟩, k⟩ => ⟨s, _, φ, A, k, hm, hsp, h31⟩)
    (RelCT.seq (two_post (Ψ := ΨA E) (callP_rel hE hX) fun _ _ ⟨s, _, φ, A, k, hm, hsp, h31⟩ =>
        WP.mono (callP_ok (hE.pre _ _ φ) (hX _ _ φ) A k hm hsp h31) fun _ hv => ⟨s, φ, hv⟩)
      (two_post (crtRestore_taint (ΨA E)) fun _ _ ⟨s, φ, hv⟩ =>
        WP.mono (restoreP_ok (hE.pre _ _ φ) hv) fun _ ⟨M, C⟩ => ⟨s, φ, M, C⟩))

end

theorem codeP_ct : ConstantTime isa (Proof.Rsa.privateCheckedPrecomputedContract abi frameBytes).pre
    (Proof.Rsa.privateCheckedPrecomputedContract abi frameBytes).pub codeP :=
  RelCT.constantTime ((codeG_rel entry_okP (crt_step_rel_true entry_okP fun _ _ φ => (preP_ofP φ.1).2)
      (step_rel_true entry_okP fun _ _ φ => (preP_ofP φ.1).2)).mono
    (fun s _ ⟨hs, ht, hp⟩ => ⟨dataOfP s, ⟨hs, rfl⟩, ⟨ht, (pub_dataP hp).symm⟩, (same_ofP (pub_dataP hp)).sp⟩)
    fun _ _ h => h)

/-- The contract, its postcondition on the registers and the stack. -/
def fnContractP : Contract isa where
  pre := (Proof.Rsa.privateCheckedPrecomputedContract abi frameBytes).pre
  post := fnPost
  pub := (Proof.Rsa.privateCheckedPrecomputedContract abi frameBytes).pub

end VG.Proof.Rsa.PPC64LE.Priv
