module

import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCorrect
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPreCopy
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivTaint
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCT
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCT
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCT
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCorrect
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPubCall
public import VerifiedGarbage.Proof.Rsa.PrivCheck
public import VerifiedGarbage.Proof.Rsa.Contract
meta import VerifiedGarbage.Proof.Rsa.Contract

/-!
# `vg_rsa_private_checked` on PPC64LE: constant time

Two runs are related by `Two` (`MontCT.lean`) at each step, both satisfying
the same predicate for the same public data (`dataOf`): the blocks between
the calls by the taint analysis (`PrivTaint.lean`), and the calls by the
callees' constant time (`RelCT.callEx`), whose public data at the call the
correctness facts fix (`crt_pub`, `pre_pub`, `pub_pub`); what each run
satisfies after each step follows from correctness (`two_post`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Two Pins two_post)

/-- The public data. -/
def dataOf (s : State) : List (BitVec 64) × List (BitVec 64) × List Nat × Addr :=
  (argRegs.map s.gpr, (List.range 12).map (stackArg s),
    (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat ++ Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat).map
      (·.toNat), s.sp)

theorem pub_data {s₁ s₂ : State} (h : (Proof.Rsa.privateCheckedContract abi frameBytes).pub s₁ s₂) :
    dataOf s₁ = dataOf s₂ := by
  have e : frameBytes = 3327 + 1 := rfl
  rw [e] at h
  sig_pub [Proof.Rsa.privateCheckedContract, Proof.Rsa.privateCheckedSig, abi, argRegs, stackArgs_twelve,
    List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
  unfold dataOf
  rw [hl]
  simp only [argRegs, List.map_cons, List.map_nil, stackArgs_twelve, h3, h4, h5, h6, h7, h8, h9, h10, a0,
    a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, hsp]

/-- The public data's facts, of `vg_rsa_private_checked` or, with `pc`, of
`vg_rsa_private_checked_precomputed`. -/
structure Same (pc : Bool) (s₁ s₂ : State) : Prop where
  gpr : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r
  arg : ∀ i < 12, stackArg s₁ i = stackArg s₂ i
  sp : s₁.sp = s₂.sp
  n : Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r5) (s₁.gpr .r6).toNat = Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r5) (s₂.gpr .r6).toNat
  e : Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r7) (s₁.gpr .r8).toNat = Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r7) (s₂.gpr .r8).toNat
  arg12 : pc = true → stackArg s₁ 12 = stackArg s₂ 12
  pv : preVal pc s₁ = preVal pc s₂

theorem same_of {s₁ s₂ : State} (h : dataOf s₁ = dataOf s₂) : Same false s₁ s₂ := by
  simp only [dataOf, Prod.mk.injEq] at h
  obtain ⟨hr, ha, hb, hsp⟩ := h
  have gr : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r := List.map_inj_left.mp hr
  have h6 : s₁.gpr .r6 = s₂.gpr .r6 := gr _ (by decide)
  have h8 : s₁.gpr .r8 = s₂.gpr .r8 := gr _ (by decide)
  rw [List.map_append, List.map_append] at hb
  obtain ⟨hn, he⟩ := List.append_inj hb (by simp [Proof.Rsa.bytesAt_length', h6])
  have hn' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hn
  exact ⟨gr, fun i hi => List.map_inj_left.mp ha i (List.mem_range.mpr hi), hsp, hn',
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 he, (fun h => nomatch h),
    by simp only [preVal, Bool.false_eq_true, ↓reduceIte]; rw [hn', h6]⟩

/-- On entry, with the public data `d`. -/
def Φ0 (d : List (BitVec 64) × List (BitVec 64) × List Nat × Addr) (s : State) : Prop :=
  (Proof.Rsa.privateCheckedContract abi frameBytes).pre s ∧ dataOf s = d

/-- Two states for the same public data. -/
theorem same {d} {s₁ s₂ : State} (h₁ : Φ0 d s₁) (h₂ : Φ0 d s₂) : Same false s₁ s₂ := same_of (h₁.2.trans h₂.2.symm)

theorem fb_same {pc : Bool} {s₁ s₂ : State} (S : Same pc s₁ s₂) : fb s₁ = fb s₂ := by simp only [fb, S.sp]

theorem r_same {pc : Bool} {s₁ s₂ : State} (S : Same pc s₁ s₂) {r : Reg} (hr : r ∈ argRegs := by decide) :
    s₁.gpr r = s₂.gpr r := S.gpr r hr

/-- The public data, from its facts. -/
theorem pub_of {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp) (hr : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r)
    (ha : ∀ i < 12, stackArg s₁ i = stackArg s₂ i)
    (hn : Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r5) (s₁.gpr .r6).toNat = Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r5) (s₂.gpr .r6).toNat)
    (he : Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r7) (s₁.gpr .r8).toNat = Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r7) (s₂.gpr .r8).toNat) :
    (Proof.Rsa.privateCheckedContract abi frameBytes).pub s₁ s₂ := by
  have e : frameBytes = 3327 + 1 := rfl
  rw [e]
  sig_pub [Proof.Rsa.privateCheckedContract, Proof.Rsa.privateCheckedSig, abi, argRegs, stackArgs_twelve,
    List.append_eq]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  exact ⟨hsp, by rw [hn, he], hr .r3 (by decide), hr .r4 (by decide), hr .r5 (by decide), hr .r6 (by decide),
    hr .r7 (by decide), hr .r8 (by decide), hr .r9 (by decide), hr .r10 (by decide), ha 0 (by decide),
    ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide), ha 5 (by decide), ha 6 (by decide),
    ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide), ha 11 (by decide)⟩

/-! ## The calls -/

theorem crt_pub {pc : Bool} {s₁ s₂ t₁ t₂ : State} (h₁ : PreP pc s₁) (h₂ : PreP pc s₂) (S : Same pc s₁ s₂) (A₁ : AtCrt s₁ t₁)
    (A₂ : AtCrt s₂ t₂) : Proof.Bignum.PPC64LE.Crt.fnContract.pub (crtEntry s₁ t₁) (crtEntry s₂ t₂) := by
  have g : ∀ {s t : State}, ∀ r, r ∉ linkRegs → (crtEntry s t).gpr r = t.gpr r :=
    fun r hr => State.callEntry_gpr _ hr
  have hn : ∀ {s t : State}, PreP pc s → AtCrt s t →
      Spec.Rsa.bytesAt t.mem (s.gpr .r5) (s.gpr .r6).toNat = Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat :=
    fun h A => bytes_of_frame A.mem (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.kn.symm)
      (by have := h.wn; omega)
  have hl : ∀ {s t : State}, AtCrt s t →
      (List.range 10).map (stackArg (crtEntry s t)) = (List.range 10).map fun i => stackArg s (2 + i) :=
    fun A => List.map_congr_left fun i hi => crtEntry_stackArg A (List.mem_range.mp hi)
  refine ⟨fun r hr => ?_, by rw [show (crtEntry s₁ t₁).sp = fb s₁ from A₁.sp,
      show (crtEntry s₂ t₂).sp = fb s₂ from A₂.sp, fb_same S], ?_, ?_⟩
  · rw [g r (fun h => by revert r; decide), g r (fun h => by revert r; decide)]
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
  · rw [hl A₁, hl A₂]
    exact List.map_congr_left fun i hi => S.arg _ (by have := List.mem_range.mp hi; omega)
  · show Spec.Rsa.bytesAt t₁.mem ((crtEntry s₁ t₁).gpr .r5) ((crtEntry s₁ t₁).gpr .r6).toNat =
      Spec.Rsa.bytesAt t₂.mem ((crtEntry s₂ t₂).gpr .r5) ((crtEntry s₂ t₂).gpr .r6).toNat
    rw [g .r5 (by decide), g .r6 (by decide), g .r5 (by decide), g .r6 (by decide), A₁.r5, A₁.r6, A₂.r5,
      A₂.r6, hn h₁ A₁, hn h₂ A₂, S.n]

theorem pre_pub {s₁ s₂ t₁ t₂ : State} (h₁ : PreP false s₁) (h₂ : PreP false s₂) (S : Same false s₁ s₂) (A₁ : AtPre s₁ t₁)
    (A₂ : AtPre s₂ t₂) : Proof.Bignum.PPC64LE.Pre.fnContract.pub (t₁.callEntry.withRegions [nR s₁] (preWr s₁))
      (t₂.callEntry.withRegions [nR s₂] (preWr s₂)) := by
  have g : ∀ {s t : State}, ∀ r, r ∉ linkRegs → (t.callEntry.withRegions [nR s] (preWr s)).gpr r = t.gpr r :=
    fun r hr => State.callEntry_gpr _ hr
  have hn : ∀ {s t : State}, PreP false s → AtPre s t →
      Spec.Rsa.bytesAt t.mem (s.gpr .r5) (s.gpr .r6).toNat = Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat :=
    fun h A => bytes_of_frame A.mem (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.kn.symm
      · exact h.ns) (by have := h.wn; omega)
  simp only [Proof.Bignum.PPC64LE.Pre.fnContract, g .r3 (by decide), g .r4 (by decide), g .r5 (by decide),
    g .r6 (by decide), g .r7 (by decide), g .r8 (by decide), A₁.r3, A₁.r4, A₁.r5, A₁.r6, A₁.r7, A₁.r8, A₂.r3,
    A₂.r4, A₂.r5, A₂.r6, A₂.r7, A₂.r8, State.withRegions_mem, State.callEntry_mem, State.withRegions_sp,
    State.callEntry_sp, A₁.sp, A₂.sp]
  rw [hn h₁ A₁, hn h₂ A₂, S.n, fb_same S, r_same S (r := .r5), r_same S (r := .r6), S.arg 10 (by decide),
    S.arg 11 (by decide)]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem pub_pub {pc : Bool} {s₁ s₂ t₁ t₂ : State} (h₁ : PreP pc s₁) (h₂ : PreP pc s₂) (S : Same pc s₁ s₂)
    (A₁ : AtPubC pc s₁ t₁) (A₂ : AtPubC pc s₂ t₂) : Proof.Bignum.PPC64LE.Pub.fnContract.pub (pubEntry s₁ t₁) (pubEntry s₂ t₂) := by
  have g : ∀ {s t : State}, ∀ r, r ∉ linkRegs → (pubEntry s t).gpr r = t.gpr r :=
    fun r hr => State.callEntry_gpr _ hr
  have he : ∀ {s t : State}, PreP pc s → AtPubC pc s t →
      Spec.Rsa.bytesAt t.mem (s.gpr .r7) (s.gpr .r8).toNat = Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat :=
    fun h A => bytes_of_frame A.mem (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.ke.symm
      · exact h.es) (by have := h.we; omega)
  obtain ⟨a₁, b₁⟩ := pubEntry_sa A₁
  obtain ⟨a₂, b₂⟩ := pubEntry_sa A₂
  simp only [Proof.Bignum.PPC64LE.Pub.fnContract, g .r3 (by decide), g .r4 (by decide), g .r5 (by decide),
    g .r6 (by decide), g .r7 (by decide), g .r8 (by decide), g .r9 (by decide), g .r10 (by decide), A₁.r3, A₁.r4,
    A₁.r5, A₁.r6, A₁.r7, A₁.r8, A₁.r9, A₁.r10, A₂.r3, A₂.r4, A₂.r5, A₂.r6, A₂.r7, A₂.r8, A₂.r9, A₂.r10, a₁, b₁, a₂,
    b₂, State.withRegions_mem, State.callEntry_mem, State.withRegions_sp, State.callEntry_sp, A₁.sp, A₂.sp,
    pre_toNat h₁, pre_toNat h₂]
  rw [A₁.pre, A₂.pre, he h₁ A₁, he h₂ A₂, S.pv, S.e, fb_same S, r_same S (r := .r3), r_same S (r := .r6),
    r_same S (r := .r7), r_same S (r := .r8), S.arg 10 (by decide), S.arg 11 (by decide)]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The chain -/

/-- The public data. -/
abbrev Data := List (BitVec 64) × List (BitVec 64) × List Nat × Addr

/-- What the chain needs of the entry states `E d s` for the public data `d`. -/
structure EntryOk {D : Type} (pc : Bool) (E : D → State → Prop) : Prop where
  pre : ∀ d s, E d s → PreP pc s
  same : ∀ d s₁ s₂, E d s₁ → E d s₂ → Same pc s₁ s₂

section

variable {D : Type} (E : D → State → Prop)

def Φ1 (d : D) (u : State) : Prop := ∃ s, E d s ∧ u = allocated frameBytes s
def Ψ1 (d : D) (u : State) : Prop := ∃ s, E d s ∧ AtCrt s u
def Ψ2 (d : D) (u : State) : Prop := ∃ s, E d s ∧ Mid s u ∧ crtOut s u
def Ψ3 (d : D) (u : State) : Prop := ∃ s, E d s ∧ AtPre s u
def ΨC (d : D) (u : State) : Prop := ∃ s, E d s ∧ AtCopy s u
def Ψ4 (pc : Bool) (d : D) (u : State) : Prop := ∃ s, E d s ∧ AtPub pc s u
def Ψ5 (pc : Bool) (d : D) (u : State) : Prop := ∃ s, E d s ∧ AtPubC pc s u
def Ψ6 (pc : Bool) (d : D) (u : State) : Prop := ∃ s, E d s ∧ AtCmp pc s u

variable {E} {pc : Bool}

theorem crt_rel (hE : EntryOk pc E) : RelCT isa (Two (Ψ1 E)) crtCall fun _ _ => True := by
  unfold crtCall
  refine RelCT.callEx Proof.Bignum.PPC64LE.Crt.fn_correct Proof.Bignum.PPC64LE.Crt.fn_ct
    fun u₁ u₂ ⟨_, ⟨s₁, φ₁, A₁⟩, ⟨s₂, φ₂, A₂⟩, _⟩ => ?_
  have h₁ := hE.pre _ _ φ₁
  have h₂ := hE.pre _ _ φ₂
  exact ⟨crtRd s₁, crtWr s₁, crtRd s₂, crtWr s₂, crt_pre h₁ A₁, crt_pre h₂ A₂,
    crt_pub h₁ h₂ (hE.same _ _ _ φ₁ φ₂) A₁ A₂, (crt_covers h₁ A₁).1, (crt_covers h₁ A₁).2, (crt_covers h₂ A₂).1,
    (crt_covers h₂ A₂).2⟩

theorem pre_rel (hE : EntryOk false E) : RelCT isa (Two (Ψ3 E)) preCall fun _ _ => True := by
  unfold preCall
  refine RelCT.callEx Proof.Bignum.PPC64LE.Pre.fn_correct Proof.Bignum.PPC64LE.Pre.fn_ct
    fun u₁ u₂ ⟨_, ⟨s₁, φ₁, A₁⟩, ⟨s₂, φ₂, A₂⟩, _⟩ => ?_
  have h₁ := hE.pre _ _ φ₁
  have h₂ := hE.pre _ _ φ₂
  exact ⟨[nR s₁], preWr s₁, [nR s₂], preWr s₂, pre_pre h₁ A₁, pre_pre h₂ A₂,
    pre_pub h₁ h₂ (hE.same _ _ _ φ₁ φ₂) A₁ A₂, (pre_covers h₁ A₁).1, (pre_covers h₁ A₁).2, (pre_covers h₂ A₂).1,
    (pre_covers h₂ A₂).2⟩

theorem pub_rel (hE : EntryOk pc E) : RelCT isa (Two (Ψ5 E pc)) pubCall fun _ _ => True := by
  unfold pubCall
  refine RelCT.callEx Proof.Bignum.PPC64LE.Pub.fn_correct Proof.Bignum.PPC64LE.Pub.fn_ct
    fun u₁ u₂ ⟨_, ⟨s₁, φ₁, A₁⟩, ⟨s₂, φ₂, A₂⟩, _⟩ => ?_
  have h₁ := hE.pre _ _ φ₁
  have h₂ := hE.pre _ _ φ₂
  obtain ⟨p₁, c₁, w₁⟩ := pub_pre h₁ A₁
  obtain ⟨p₂, c₂, w₂⟩ := pub_pre h₂ A₂
  exact ⟨pubRd s₁, pubWr s₁, pubRd s₂, pubWr s₂, p₁, p₂, pub_pub h₁ h₂ (hE.same _ _ _ φ₁ φ₂) A₁ A₂, c₁, w₁, c₂,
    w₂⟩

theorem pins_Ψ6 (hE : EntryOk pc E) : Pins (Ψ6 E pc) [.r24, .r26, .r29] := by
  rintro d u₁ u₂ ⟨s₁, φ₁, A₁⟩ ⟨s₂, φ₂, A₂⟩ r hr
  have S := hE.same _ _ _ φ₁ φ₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [A₁.r24, A₂.r24, r_same S]
  · rw [A₁.r26, A₂.r26, r_same S]
  · rw [A₁.r29, A₂.r29, r_same S]

theorem pins_ΨC (hE : EntryOk true E) : Pins (ΨC E) [.r3, .r4, .r5] := by
  rintro d u₁ u₂ ⟨s₁, φ₁, A₁⟩ ⟨s₂, φ₂, A₂⟩ r hr
  have S := hE.same _ _ _ φ₁ φ₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [A₁.r3, A₂.r3, S.arg12 rfl]
  · rw [A₁.r4, A₂.r4, fb_same S]
  · rw [A₁.r5, A₂.r5, r_same S]

/-- `n`'s values computed. -/
theorem step_rel_false (hE : EntryOk false E) : RelCT isa (Two (Ψ2 E)) (preStep false) (Two (Ψ4 E false)) :=
  RelCT.seq (two_post (Ψ := Ψ3 E) (preArgs_taint (Ψ2 E)) fun _ _ ⟨s, φ, M, C⟩ =>
    WP.mono (preArgs_ok (hE.pre _ _ φ) M C) fun _ A => ⟨s, φ, A⟩)
    (two_post (pre_rel hE) fun _ _ ⟨s, φ, A⟩ => preCall_ok (hE.pre _ _ φ) A fun _ B => ⟨s, φ, B⟩)

/-- `n`'s values copied from `pre`. -/
theorem step_rel_true (hE : EntryOk true E) (hX : ∀ d s, E d s → PreX s) :
    RelCT isa (Two (Ψ2 E)) (preStep true) (Two (Ψ4 E true)) :=
  RelCT.seq (two_post (Ψ := ΨC E) (preArgsP_taint (Ψ2 E)) fun _ _ ⟨s, φ, M, C⟩ =>
    WP.mono (preArgsP_ok (hE.pre _ _ φ) M C) fun _ A => ⟨s, φ, A⟩)
    (two_post (preCopy_taint (pins_ΨC hE)) fun _ _ ⟨s, φ, A⟩ =>
      WP.mono (preCopy_ok (hE.pre _ _ φ) (hX _ _ φ) A) fun _ B => ⟨s, φ, B⟩)

/-- `vg_rsa_private_crt`. -/
theorem crt_step_rel_false (hE : EntryOk false E) : RelCT isa (Two (Ψ1 E)) (crtStep false) (Two (Ψ2 E)) :=
  two_post (crt_rel hE) fun _ _ ⟨s, φ, A⟩ => crtCall_ok (hE.pre _ _ φ) A fun _ M C => ⟨s, φ, M, C⟩

theorem body_rel (hE : EntryOk pc E) (hcrt : RelCT isa (Two (Ψ1 E)) (crtStep pc) (Two (Ψ2 E)))
    (hstep : RelCT isa (Two (Ψ2 E)) (preStep pc) (Two (Ψ4 E pc))) :
    RelCT isa (Two (Φ1 E)) (bodyG pc) fun _ _ => True := by
  unfold bodyG
  refine RelCT.seq (two_post (Ψ := Ψ1 E) (setup_taint (Φ1 E)) fun d u ⟨s, φ, e⟩ =>
    e ▸ WP.mono (setup_ok (hE.pre _ _ φ)) fun v A => ⟨s, φ, A⟩) ?_
  refine RelCT.seq hcrt ?_
  refine RelCT.seq hstep ?_
  refine RelCT.seq (two_post (Ψ := Ψ5 E pc) (pubArgs_taint (Ψ4 E pc)) fun d u ⟨s, φ, A⟩ =>
    WP.mono (pubArgs_ok (hE.pre _ _ φ) A) fun v B => ⟨s, φ, B⟩) ?_
  refine RelCT.seq (two_post (Ψ := Ψ6 E pc) (pub_rel hE) fun d u ⟨s, φ, A⟩ =>
    pubCall_ok (hE.pre _ _ φ) A fun v B => ⟨s, φ, B⟩) ?_
  exact tail_taint (pins_Ψ6 hE)

theorem codeG_rel (hE : EntryOk pc E) (hcrt : RelCT isa (Two (Ψ1 E)) (crtStep pc) (Two (Ψ2 E)))
    (hstep : RelCT isa (Two (Ψ2 E)) (preStep pc) (Two (Ψ4 E pc))) :
    RelCT isa (Two E) (.frame (.alloc frameBytes) (bodyG pc) (.free frameBytes)) fun _ _ => True :=
  RelCT.alloc (fun _ _ ⟨_, _, _, hsp⟩ => hsp) ((body_rel hE hcrt hstep).mono
    (fun a b ⟨s, t, ⟨d, φs, φt, hsp⟩, ea, eb⟩ =>
      ⟨d, ⟨s, φs, ea⟩, ⟨t, φt, eb⟩, by rw [ea, eb]; simp only [allocated, hsp]⟩) fun _ _ h => h)

end

theorem entry_ok : EntryOk false Φ0 := ⟨fun _ _ φ => preP_of φ.1, fun _ _ _ φ₁ φ₂ => same φ₁ φ₂⟩

theorem code_rel : RelCT isa (Two Φ0) code fun _ _ => True :=
  codeG_rel entry_ok (crt_step_rel_false entry_ok) (step_rel_false entry_ok)

theorem code_ct : ConstantTime isa (Proof.Rsa.privateCheckedContract abi frameBytes).pre
    (Proof.Rsa.privateCheckedContract abi frameBytes).pub code :=
  RelCT.constantTime (code_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨dataOf s, ⟨hs, rfl⟩, ⟨ht, (pub_data hp).symm⟩, (same_of (pub_data hp)).sp⟩) fun _ _ h => h)

end VG.Proof.Rsa.PPC64LE.Priv
