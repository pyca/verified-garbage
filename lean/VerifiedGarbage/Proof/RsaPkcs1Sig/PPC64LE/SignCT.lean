module

import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.SignCorrect
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.SignTaint
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCT
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPubCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.SignCall
public import VerifiedGarbage.Proof.Rsa.Contract
meta import VerifiedGarbage.Proof.Rsa.Contract

/-!
# `vg_rsa_pkcs1_sign` on PPC64LE: constant time

Two runs are related by `Two` (`MontCT.lean`) at each step, both satisfying
the same predicate for the same public data (`dataOf`): the blocks by the
taint analysis (`SignTaint.lean`), the branch on the encoding's result,
which only the lengths and `hash` decide (`r3_same`), and the call by
`vg_rsa_private_checked`'s (or with `pc` `vg_rsa_private_checked_precomputed`'s)
constant time (`RelCT.callEx`), whose public data at the call the correctness
facts fix (`priv_facts`, `pre_leak`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.Sign
open VG.Proof.Bignum.PPC64LE (Two Pins two_post)

variable {pc : Bool}

/-- The argument registers whose whole value is public: all but `hash`'s,
whose low word is. -/
def pubRegs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r10]

/-- Our stack arguments: thirteen, or with `pc` fifteen. -/
abbrev nArgs (pc : Bool) : Nat := if pc then 15 else 13

/-- The public data. -/
abbrev Data := List (BitVec 64) × BitVec 32 × List (BitVec 64) × List Nat × List Nat × Addr

def dataOf (pc : Bool) (s : State) : Data :=
  (pubRegs.map s.gpr, (s.gpr .r9).setWidth 32, (List.range (nArgs pc)).map (stackArg s),
    (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat ++ Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat).map
      (·.toNat),
    (if pc then Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 13) (s.gpr .r6).toNat else []), s.sp)

theorem pub_data {s₁ s₂ : State} (h : (Spec.RsaPkcs1Sig.signContract abi stackBytes).pub s₁ s₂) :
    dataOf false s₁ = dataOf false s₂ := by
  have e : stackBytes = 4607 + 1 := rfl
  rw [e] at h
  sig_pub [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, abi, argRegs, stackArgs_thirteen,
    List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  unfold dataOf
  rw [hl]
  simp only [pubRegs, nArgs, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, stackArgs_thirteen, h3,
    h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, hsp]

/-- The public data's facts. -/
structure Same (pc : Bool) (s₁ s₂ : State) : Prop where
  gpr : ∀ r ∈ pubRegs, s₁.gpr r = s₂.gpr r
  hash : (s₁.gpr .r9).setWidth 32 = (s₂.gpr .r9).setWidth 32
  arg : ∀ i < nArgs pc, stackArg s₁ i = stackArg s₂ i
  sp : s₁.sp = s₂.sp
  n : Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r5) (s₁.gpr .r6).toNat = Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r5) (s₂.gpr .r6).toNat
  e : Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r7) (s₁.gpr .r8).toNat = Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r7) (s₂.gpr .r8).toNat
  leak : pc = true → Spec.Rsa.privatePrecomputedLeak s₁.mem (stackArg s₁ 13) (s₁.gpr .r6).toNat =
    Spec.Rsa.privatePrecomputedLeak s₂.mem (stackArg s₂ 13) (s₂.gpr .r6).toNat

theorem Same.a {s₁ s₂ : State} (S : Same pc s₁ s₂) {i : Nat} (hi : i < 13) : stackArg s₁ i = stackArg s₂ i :=
  S.arg i (lt_args hi)

theorem same_of {s₁ s₂ : State} (h : dataOf pc s₁ = dataOf pc s₂) : Same pc s₁ s₂ := by
  simp only [dataOf, Prod.mk.injEq] at h
  obtain ⟨hr, hh, ha, hb, hl, hsp⟩ := h
  have gr : ∀ r ∈ pubRegs, s₁.gpr r = s₂.gpr r := List.map_inj_left.mp hr
  have h6 : s₁.gpr .r6 = s₂.gpr .r6 := gr _ (by decide)
  rw [List.map_append, List.map_append] at hb
  obtain ⟨hn, he⟩ := List.append_inj hb (by simp [Proof.RsaPkcs1Sig.bytesAt_length, h6])
  exact ⟨gr, hh, fun i hi => List.map_inj_left.mp ha i (List.mem_range.mpr hi), hsp,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hn,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 he,
    fun hp => by subst hp; simpa only [↓reduceIte] using hl⟩

/-- What a run's entry state gives: `SPre`, and with `pc` `PreX`. -/
abbrev En (pc : Bool) (s : State) : Prop := SPre pc s ∧ (pc = true → PreX s)

/-- On entry, with the public data `d`. -/
def Φ0 (pc : Bool) (d : Data) (s : State) : Prop := En pc s ∧ dataOf pc s = d

theorem same {d : Data} {s₁ s₂ : State} (h₁ : Φ0 pc d s₁) (h₂ : Φ0 pc d s₂) : Same pc s₁ s₂ :=
  same_of (h₁.2.trans h₂.2.symm)

theorem fb_same {s₁ s₂ : State} (S : Same pc s₁ s₂) : fb s₁ = fb s₂ := by simp only [fb, S.sp]

theorem r_same {s₁ s₂ : State} (S : Same pc s₁ s₂) {r : Reg} (hr : r ∈ pubRegs := by decide) :
    s₁.gpr r = s₂.gpr r := S.gpr r hr

/-- Whether the encoding succeeds depends only on `hash`, the lengths of the
hash value and `k`. -/
theorem isSome_same {s₁ s₂ : State} (S : Same pc s₁ s₂) : (encOut s₁).isSome = (encOut s₂).isSome := by
  unfold encOut RsaPkcs1Sig.PPC64LE.encodeId
  rw [S.hash, r_same S (r := .r6)]
  cases Spec.RsaPkcs1Sig.Hash.ofId ((s₂.gpr .r9).setWidth 32).toNat with
  | none => rfl
  | some h =>
    simp only [Spec.RsaPkcs1Sig.encode, Spec.RsaPkcs1Sig.digestInfo, List.length_append, hashOf,
      Proof.RsaPkcs1Sig.bytesAt_length, S.a (i := 0) (by decide)]
    split <;> rfl

theorem AtAft.r3_eq {s u : State} (B : AtAft s u) : u.gpr .r3 = if (encOut s).isSome then 1 else 0 := by
  have := B.enc
  revert this
  cases encOut s with
  | none => intro h; exact h
  | some _ => intro h; exact h.1

/-! ## The call -/

/-- What two runs share at the call. -/
theorem priv_facts {s₁ s₂ t₁ t₂ : State} {em₁ em₂ : List Byte} (h₁ : SPre pc s₁) (h₂ : SPre pc s₂)
    (S : Same pc s₁ s₂) (A₁ : AtCall pc s₁ t₁ em₁) (A₂ : AtCall pc s₂ t₂ em₂) :
    (callE pc s₁ t₁).sp = (callE pc s₂ t₂).sp ∧
      (∀ r ∈ argRegs, (callE pc s₁ t₁).gpr r = (callE pc s₂ t₂).gpr r) ∧
      (∀ i < nCallArgs pc, stackArg (callE pc s₁ t₁) i = stackArg (callE pc s₂ t₂) i) ∧
      Spec.Rsa.bytesAt (callE pc s₁ t₁).mem ((callE pc s₁ t₁).gpr .r5) ((callE pc s₁ t₁).gpr .r6).toNat =
        Spec.Rsa.bytesAt (callE pc s₂ t₂).mem ((callE pc s₂ t₂).gpr .r5) ((callE pc s₂ t₂).gpr .r6).toNat ∧
      Spec.Rsa.bytesAt (callE pc s₁ t₁).mem ((callE pc s₁ t₁).gpr .r7) ((callE pc s₁ t₁).gpr .r8).toNat =
        Spec.Rsa.bytesAt (callE pc s₂ t₂).mem ((callE pc s₂ t₂).gpr .r7) ((callE pc s₂ t₂).gpr .r8).toNat := by
  have hn : ∀ {s t : State} {em : List Byte}, SPre pc s → AtCall pc s t em →
      Spec.Rsa.bytesAt (callE pc s t).mem ((callE pc s t).gpr .r5) ((callE pc s t).gpr .r6).toNat =
        Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat := fun h A => by
    rw [callE_gpr, callE_gpr, A.r5, A.r6]
    exact bytes_of_frame A.mem (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.kn.symm)
      (by have := h.wn; omega_using [])
  have he : ∀ {s t : State} {em : List Byte}, SPre pc s → AtCall pc s t em →
      Spec.Rsa.bytesAt (callE pc s t).mem ((callE pc s t).gpr .r7) ((callE pc s t).gpr .r8).toNat =
        Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat := fun h A => by
    rw [callE_gpr, callE_gpr, A.r7, A.r8]
    exact bytes_of_frame A.mem (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.ke.symm)
      (by have := h.we; omega_using [])
  refine ⟨by rw [show (callE pc s₁ t₁).sp = fb s₁ from A₁.sp, show (callE pc s₂ t₂).sp = fb s₂ from A₂.sp,
      fb_same S], fun r hr => ?_, fun i hi => ?_, by rw [hn h₁ A₁, hn h₂ A₂, S.n], by rw [he h₁ A₁, he h₂ A₂, S.e]⟩
  · rw [callE_gpr s₁ t₁ (fun h => by revert r; decide), callE_gpr s₂ t₂ (fun h => by revert r; decide)]
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [A₁.r3, A₂.r3, r_same S]
    · rw [A₁.r4, A₂.r4, r_same S]
    · rw [A₁.r5, A₂.r5, r_same S]
    · rw [A₁.r6, A₂.r6, r_same S]
    · rw [A₁.r7, A₂.r7, r_same S]
    · rw [A₁.r8, A₂.r8, r_same S]
    · rw [A₁.r9, A₂.r9, fb_same S]
    · rw [A₁.r10, A₂.r10, r_same S]
  · rw [callE_stackArg A₁ hi, callE_stackArg A₂ hi, S.arg _ (nCall_lt hi).2]

/-- With `pc`, what the call may leak of `pre`, as on entry. -/
theorem pre_leak {s t : State} {em : List Byte} (X : PreX s) (A : AtCall true s t em) :
    Spec.Rsa.privatePrecomputedLeak (callE true s t).mem (stackArg (callE true s t) 12)
        ((callE true s t).gpr .r6).toNat =
      Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 13) (s.gpr .r6).toNat := by
  have pwl : Spec.Rsa.precomputedWords (s.gpr .r6).toNat ≤ (stackArg s 14).toNat := by
    rw [X.pl]; unfold Spec.Rsa.privatePrecomputedWords; omega_using []
  simp only [Spec.Rsa.privatePrecomputedLeak, callE_stackArg A (i := 12) (by decide), callE_gpr (pc := true) s t (r := .r6),
    A.r6]
  congr 1
  have subPre : Region.Sub ⟨stackArg s 13, 8 * Spec.Rsa.precomputedWords (s.gpr .r6).toNat⟩ (preR s) :=
    fun _ hx => by simp only [Region.Contains] at hx ⊢; omega_using [pwl, hx]
  exact VG.Proof.Rsa.PPC64LE.Priv.words_of_frame A.mem (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact X.kP.symm.sub_left subPre) (by have := X.wP; omega_using [pwl, this])

/-! ## The chain -/

def Φ1 (pc : Bool) (d : Data) (u : State) : Prop := ∃ s, Φ0 pc d s ∧ u = allocated frameBytes s
def Ψ1 (pc : Bool) (d : Data) (u : State) : Prop := ∃ s, Φ0 pc d s ∧ AtEnc s u
def Ψ2 (pc : Bool) (d : Data) (u : State) : Prop := ∃ s, Φ0 pc d s ∧ AtAft s u
def Ψ2s (pc : Bool) (d : Data) (u : State) : Prop := ∃ s, Φ0 pc d s ∧ AtAft s u ∧ (encOut s).isSome
def Ψ5 (pc : Bool) (d : Data) (u : State) : Prop := ∃ s em, Φ0 pc d s ∧ AtCall pc s u em
def Ψ6 (pc : Bool) (d : Data) (u : State) : Prop := ∃ s em, Φ0 pc d s ∧ AtRet s u em
def Ψ8 (pc : Bool) (d : Data) (u : State) : Prop := ∃ s, Φ0 pc d s ∧ Fr2 s u

theorem pins_nil {α : Type} (Φ : α → State → Prop) : Pins Φ [] := fun _ _ _ _ _ _ h => nomatch h

theorem pins_Ψ1 : Pins (Ψ1 pc) [.r4, .r5, .r6, .r7, .r8] := by
  rintro d u₁ u₂ ⟨s₁, φ₁, A₁⟩ ⟨s₂, φ₂, A₂⟩ r hr
  have S := same φ₁ φ₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [A₁.r4, A₂.r4, fb_same S]
  · rw [A₁.r5, A₂.r5, r_same S]
  · rw [A₁.r6, A₂.r6, S.hash]
  · rw [A₁.r7, A₂.r7, r_same S]
  · rw [A₁.r8, A₂.r8, S.a (i := 0) (by decide)]

theorem pins_Ψ2 : Pins (Ψ2 pc) [.r26, .r28] := by
  rintro d u₁ u₂ ⟨s₁, φ₁, A₁⟩ ⟨s₂, φ₂, A₂⟩ r hr
  have S := same φ₁ φ₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [A₁.r26, A₂.r26, r_same S]
  · rw [A₁.r28, A₂.r28, r_same S]

theorem pins_Ψ6 : Pins (Ψ6 pc) [.r28] := by
  rintro d u₁ u₂ ⟨s₁, _, φ₁, A₁⟩ ⟨s₂, _, φ₂, A₂⟩ r hr
  rw [List.mem_singleton.mp hr, A₁.r28, A₂.r28, r_same (same φ₁ φ₂)]

theorem priv_rel : RelCT isa (Two (Ψ5 pc)) (privCall pc) fun _ _ => True := by
  cases pc with
  | false =>
    refine RelCT.callEx (k := Rsa.PPC64LE.Priv.fnContract) Rsa.PPC64LE.Priv.code_correct
      Rsa.PPC64LE.Priv.code_ct fun u₁ u₂ ⟨_, ⟨s₁, _, φ₁, A₁⟩, ⟨s₂, _, φ₂, A₂⟩, _⟩ => ?_
    have h₁ := φ₁.1.1
    have h₂ := φ₂.1.1
    obtain ⟨hsp, hr, ha, hn, he⟩ := priv_facts h₁ h₂ (same φ₁ φ₂) A₁ A₂
    exact ⟨callRd false s₁, callWr s₁, callRd false s₂, callWr s₂, Rsa.PPC64LE.Priv.pre_of_preP (preP_entry h₁ A₁),
      Rsa.PPC64LE.Priv.pre_of_preP (preP_entry h₂ A₂), Rsa.PPC64LE.Priv.pub_of hsp hr ha hn he,
      (call_covers h₁ A₁).1, (call_covers h₁ A₁).2, (call_covers h₂ A₂).1, (call_covers h₂ A₂).2⟩
  | true =>
    refine RelCT.callEx (k := Rsa.PPC64LE.Priv.fnContractP) Rsa.PPC64LE.Priv.codeP_correct
      Rsa.PPC64LE.Priv.codeP_ct fun u₁ u₂ ⟨_, ⟨s₁, _, φ₁, A₁⟩, ⟨s₂, _, φ₂, A₂⟩, _⟩ => ?_
    have h₁ := φ₁.1.1
    have h₂ := φ₂.1.1
    have X₁ := φ₁.1.2 rfl
    have X₂ := φ₂.1.2 rfl
    obtain ⟨hsp, hr, ha, hn, he⟩ := priv_facts h₁ h₂ (same φ₁ φ₂) A₁ A₂
    exact ⟨callRd true s₁, callWr s₁, callRd true s₂, callWr s₂,
      Rsa.PPC64LE.Priv.pre_of_prePX (preP_entry h₁ A₁) (preX_entry h₁ X₁ A₁),
      Rsa.PPC64LE.Priv.pre_of_prePX (preP_entry h₂ A₂) (preX_entry h₂ X₂ A₂),
      Rsa.PPC64LE.Priv.pub_ofP hsp hr ha hn he
        (by rw [pre_leak X₁ A₁, pre_leak X₂ A₂]; exact (same φ₁ φ₂).leak rfl),
      (call_covers h₁ A₁).1, (call_covers h₁ A₁).2, (call_covers h₂ A₂).1, (call_covers h₂ A₂).2⟩

theorem sign_rel : RelCT isa (Two (Ψ2s pc)) (.seq (.block (callArgs pc)) (.seq (privCall pc) wipe))
    fun _ _ => True := by
  refine RelCT.seq (two_post (Ψ := Ψ5 pc) (callArgs_taint pc (pins_nil _)) fun d u ⟨s, φ, B, hs⟩ => ?_) ?_
  · have h := φ.1.1
    have he := B.enc
    revert he
    cases hc : encOut s with
    | none => rw [hc] at hs; cases hs
    | some em => intro ⟨_, hb⟩; exact WP.mono (callArgs_ok h B hb) fun v C => ⟨s, em, φ, C⟩
  refine RelCT.seq (two_post (Ψ := Ψ6 pc) priv_rel fun d u ⟨s, em, φ, C⟩ =>
    call_ok φ.1.1 φ.1.2 C fun v R => ⟨s, em, φ, R⟩) ?_
  exact wipe_taint pins_Ψ6

theorem aft_rel : RelCT isa (Two (Ψ2 pc)) (afterEnc pc) fun _ _ => True := by
  have hr3 : ∀ u₁ u₂, Two (Ψ2 pc) u₁ u₂ → u₁.gpr .r3 = u₂.gpr .r3 := by
    rintro u₁ u₂ ⟨d, ⟨s₁, φ₁, B₁⟩, ⟨s₂, φ₂, B₂⟩, _⟩
    rw [B₁.r3_eq, B₂.r3_eq, isSome_same (same φ₁ φ₂)]
  refine RelCT.ite (fun u₁ u₂ h => by rw [eval_zero, eval_zero, hr3 u₁ u₂ h])
    ((zeroOut_taint pins_Ψ2).mono (fun _ _ h => h.1) fun _ _ h => h) (sign_rel.mono ?_ fun _ _ h => h)
  rintro u₁ u₂ ⟨⟨d, ⟨s₁, φ₁, B₁⟩, ⟨s₂, φ₂, B₂⟩, hsp⟩, hc⟩
  have hs₁ : (encOut s₁).isSome = true := by
    rw [eval_zero, B₁.r3_eq] at hc
    cases h : (encOut s₁).isSome
    · rw [h] at hc; simp at hc
    · rfl
  exact ⟨d, ⟨s₁, φ₁, B₁, hs₁⟩, ⟨s₂, φ₂, B₂, (isSome_same (same φ₁ φ₂)).symm.trans hs₁⟩, hsp⟩

theorem body_rel : RelCT isa (Two (Φ1 pc)) (body pc) fun _ _ => True := by
  unfold body
  refine RelCT.seq (two_post (Ψ := Ψ1 pc) (setup_taint (pins_nil _)) fun d u ⟨s, φ, e⟩ =>
    e ▸ WP.mono (setup_ok φ.1.1) fun v A => ⟨s, φ, A⟩) ?_
  refine RelCT.seq (two_post (Ψ := Ψ2 pc) (encode_taint pins_Ψ1) fun d u ⟨s, φ, A⟩ =>
    WP.mono (enc_ok φ.1.1 A) fun v B => ⟨s, φ, B⟩) ?_
  refine RelCT.seq (two_post (Ψ := Ψ8 pc) aft_rel fun d u ⟨s, φ, B⟩ =>
    WP.mono (afterEnc_ok φ.1.1 φ.1.2 B) fun v ⟨F, _⟩ => ⟨s, φ, F⟩) ?_
  exact restore_taint (pins_nil _)

theorem codeG_rel : RelCT isa (Two (Φ0 pc)) (codeG pc) fun _ _ => True :=
  RelCT.alloc (fun _ _ ⟨_, _, _, hsp⟩ => hsp) (body_rel.mono (fun a b ⟨s, t, ⟨d, φs, φt, hsp⟩, ea, eb⟩ =>
    ⟨d, ⟨s, φs, ea⟩, ⟨t, φt, eb⟩, by rw [ea, eb]; simp only [allocated, hsp]⟩) fun _ _ h => h)

theorem code_ct : ConstantTime isa (Spec.RsaPkcs1Sig.signContract abi stackBytes).pre
    (Spec.RsaPkcs1Sig.signContract abi stackBytes).pub code :=
  RelCT.constantTime (codeG_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨dataOf false s, ⟨⟨sPre_of hs, nofun⟩, rfl⟩, ⟨⟨sPre_of ht, nofun⟩, (pub_data hp).symm⟩,
      (same_of (pub_data hp)).sp⟩) fun _ _ h => h)

end VG.Proof.RsaPkcs1Sig.PPC64LE.Sign
