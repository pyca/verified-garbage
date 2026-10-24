module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.SignCorrect
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.SignTaint
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc

/-!
# `vg_rsa_pkcs1_sign` on PPC64LE: constant time

Two runs are related by `Two` (`MontCT.lean`) at each step, both satisfying
the same predicate for the same public data (`dataOf`): the blocks by the
taint analysis (`SignTaint.lean`), the branch on the encoding's result,
which only the lengths and `hash` decide (`r3_same`), and the call by
`vg_rsa_private_checked`'s constant time (`RelCT.callEx`), whose public data
at the call the correctness facts fix (`priv_pub`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.Sign
open VG.Proof.Bignum.PPC64LE (Two Pins two_post)

/-- The argument registers whose whole value is public: all but `hash`'s,
whose low word is. -/
def pubRegs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r10]

/-- The public data. -/
abbrev Data := List (BitVec 64) × BitVec 32 × List (BitVec 64) × List Nat × Addr

def dataOf (s : State) : Data :=
  (pubRegs.map s.gpr, (s.gpr .r9).setWidth 32, (List.range 13).map (stackArg s),
    (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat ++ Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat).map
      (·.toNat), s.sp)

theorem pub_data {s₁ s₂ : State} (h : (Spec.RsaPkcs1Sig.signContract abi stackBytes).pub s₁ s₂) :
    dataOf s₁ = dataOf s₂ := by
  have e : stackBytes = 4591 + 1 := rfl
  rw [e] at h
  sig_pub [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, abi, argRegs, stackArgs_thirteen,
    List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  unfold dataOf
  rw [hl]
  simp only [pubRegs, List.map_cons, List.map_nil, stackArgs_thirteen, h3, h4, h5, h6, h7, h8, h9, h10, a0,
    a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, hsp]

/-- The public data's facts. -/
structure Same (s₁ s₂ : State) : Prop where
  gpr : ∀ r ∈ pubRegs, s₁.gpr r = s₂.gpr r
  hash : (s₁.gpr .r9).setWidth 32 = (s₂.gpr .r9).setWidth 32
  arg : ∀ i < 13, stackArg s₁ i = stackArg s₂ i
  sp : s₁.sp = s₂.sp
  n : Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r5) (s₁.gpr .r6).toNat = Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r5) (s₂.gpr .r6).toNat
  e : Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r7) (s₁.gpr .r8).toNat = Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r7) (s₂.gpr .r8).toNat

theorem same_of {s₁ s₂ : State} (h : dataOf s₁ = dataOf s₂) : Same s₁ s₂ := by
  simp only [dataOf, Prod.mk.injEq] at h
  obtain ⟨hr, hh, ha, hb, hsp⟩ := h
  have gr : ∀ r ∈ pubRegs, s₁.gpr r = s₂.gpr r := List.map_inj_left.mp hr
  have h6 : s₁.gpr .r6 = s₂.gpr .r6 := gr _ (by decide)
  rw [List.map_append, List.map_append] at hb
  obtain ⟨hn, he⟩ := List.append_inj hb (by simp [Proof.RsaPkcs1Sig.bytesAt_length, h6])
  exact ⟨gr, hh, fun i hi => List.map_inj_left.mp ha i (List.mem_range.mpr hi), hsp,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hn,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 he⟩

/-- On entry, with the public data `d`. -/
def Φ0 (d : Data) (s : State) : Prop := (Spec.RsaPkcs1Sig.signContract abi stackBytes).pre s ∧ dataOf s = d

theorem same {d : Data} {s₁ s₂ : State} (h₁ : Φ0 d s₁) (h₂ : Φ0 d s₂) : Same s₁ s₂ :=
  same_of (h₁.2.trans h₂.2.symm)

theorem fb_same {s₁ s₂ : State} (S : Same s₁ s₂) : fb s₁ = fb s₂ := by simp only [fb, S.sp]

theorem r_same {s₁ s₂ : State} (S : Same s₁ s₂) {r : Reg} (hr : r ∈ pubRegs := by decide) :
    s₁.gpr r = s₂.gpr r := S.gpr r hr

/-- Whether the encoding succeeds depends only on `hash`, the lengths of the
hash value and `k`. -/
theorem isSome_same {s₁ s₂ : State} (S : Same s₁ s₂) : (encOut s₁).isSome = (encOut s₂).isSome := by
  unfold encOut RsaPkcs1Sig.PPC64LE.encodeId
  rw [S.hash, r_same S (r := .r6)]
  cases Spec.RsaPkcs1Sig.Hash.ofId ((s₂.gpr .r9).setWidth 32).toNat with
  | none => rfl
  | some h =>
    simp only [Spec.RsaPkcs1Sig.encode, Spec.RsaPkcs1Sig.digestInfo, List.length_append, hashOf,
      Proof.RsaPkcs1Sig.bytesAt_length, S.arg 0 (by decide)]
    split <;> rfl

theorem AtAft.r3_eq {s u : State} (B : AtAft s u) : u.gpr .r3 = if (encOut s).isSome then 1 else 0 := by
  have := B.enc
  revert this
  cases encOut s with
  | none => intro h; exact h
  | some _ => intro h; exact h.1

/-! ## The call -/

theorem priv_pub {s₁ s₂ t₁ t₂ : State} {em₁ em₂ : List Byte} (h₁ : SPre s₁) (h₂ : SPre s₂) (S : Same s₁ s₂)
    (A₁ : AtCall s₁ t₁ em₁) (A₂ : AtCall s₂ t₂ em₂) :
    (Spec.Rsa.privateCheckedContract abi Impl.Rsa.PPC64LE.Priv.frameBytes).pub (callE s₁ t₁) (callE s₂ t₂) := by
  have hn : ∀ {s t : State} {em : List Byte}, SPre s → AtCall s t em →
      Spec.Rsa.bytesAt (callE s t).mem ((callE s t).gpr .r5) ((callE s t).gpr .r6).toNat =
        Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat := fun h A => by
    rw [callE_gpr, callE_gpr, A.r5, A.r6]
    exact bytes_of_frame A.mem (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.kn.symm)
      (by have := h.wn; omega)
  have he : ∀ {s t : State} {em : List Byte}, SPre s → AtCall s t em →
      Spec.Rsa.bytesAt (callE s t).mem ((callE s t).gpr .r7) ((callE s t).gpr .r8).toNat =
        Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat := fun h A => by
    rw [callE_gpr, callE_gpr, A.r7, A.r8]
    exact bytes_of_frame A.mem (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.ke.symm)
      (by have := h.we; omega)
  refine Rsa.PPC64LE.Priv.pub_of (by rw [show (callE s₁ t₁).sp = fb s₁ from A₁.sp,
      show (callE s₂ t₂).sp = fb s₂ from A₂.sp, fb_same S]) (fun r hr => ?_) (fun i hi => ?_)
    (by rw [hn h₁ A₁, hn h₂ A₂, S.n]) (by rw [he h₁ A₁, he h₂ A₂, S.e])
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
  · rw [callE_stackArg A₁ hi, callE_stackArg A₂ hi, S.arg _ (by omega)]

/-! ## The chain -/

def Φ1 (d : Data) (u : State) : Prop := ∃ s, Φ0 d s ∧ u = allocated frameBytes s
def Ψ1 (d : Data) (u : State) : Prop := ∃ s, Φ0 d s ∧ AtEnc s u
def Ψ2 (d : Data) (u : State) : Prop := ∃ s, Φ0 d s ∧ AtAft s u
def Ψ2s (d : Data) (u : State) : Prop := ∃ s, Φ0 d s ∧ AtAft s u ∧ (encOut s).isSome
def Ψ5 (d : Data) (u : State) : Prop := ∃ s em, Φ0 d s ∧ AtCall s u em
def Ψ6 (d : Data) (u : State) : Prop := ∃ s em, Φ0 d s ∧ AtRet s u em
def Ψ8 (d : Data) (u : State) : Prop := ∃ s, Φ0 d s ∧ Fr2 s u

theorem pins_nil {α : Type} (Φ : α → State → Prop) : Pins Φ [] := fun _ _ _ _ _ _ h => nomatch h

theorem pins_Ψ1 : Pins Ψ1 [.r4, .r5, .r6, .r7, .r8] := by
  rintro d u₁ u₂ ⟨s₁, φ₁, A₁⟩ ⟨s₂, φ₂, A₂⟩ r hr
  have S := same φ₁ φ₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [A₁.r4, A₂.r4, fb_same S]
  · rw [A₁.r5, A₂.r5, r_same S]
  · rw [A₁.r6, A₂.r6, S.hash]
  · rw [A₁.r7, A₂.r7, r_same S]
  · rw [A₁.r8, A₂.r8, S.arg 0 (by decide)]

theorem pins_Ψ2 : Pins Ψ2 [.r26, .r28] := by
  rintro d u₁ u₂ ⟨s₁, φ₁, A₁⟩ ⟨s₂, φ₂, A₂⟩ r hr
  have S := same φ₁ φ₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [A₁.r26, A₂.r26, r_same S]
  · rw [A₁.r28, A₂.r28, r_same S]

theorem pins_Ψ6 : Pins Ψ6 [.r28] := by
  rintro d u₁ u₂ ⟨s₁, _, φ₁, A₁⟩ ⟨s₂, _, φ₂, A₂⟩ r hr
  rw [List.mem_singleton.mp hr, A₁.r28, A₂.r28, r_same (same φ₁ φ₂)]

theorem priv_rel : RelCT isa (Two Ψ5) privCall fun _ _ => True := by
  unfold privCall
  refine RelCT.callEx (k := Rsa.PPC64LE.Priv.fnContract) Rsa.PPC64LE.Priv.code_correct
    Rsa.PPC64LE.Priv.code_ct fun u₁ u₂ ⟨_, ⟨s₁, _, φ₁, A₁⟩, ⟨s₂, _, φ₂, A₂⟩, _⟩ => ?_
  have h₁ := sPre_of φ₁.1
  have h₂ := sPre_of φ₂.1
  exact ⟨callRd s₁, callWr s₁, callRd s₂, callWr s₂, Rsa.PPC64LE.Priv.pre_of_preP (preP_entry h₁ A₁),
    Rsa.PPC64LE.Priv.pre_of_preP (preP_entry h₂ A₂), priv_pub h₁ h₂ (same φ₁ φ₂) A₁ A₂,
    (call_covers h₁ A₁).1, (call_covers h₁ A₁).2, (call_covers h₂ A₂).1, (call_covers h₂ A₂).2⟩

theorem sign_rel : RelCT isa (Two Ψ2s) (.seq (.block callArgs) (.seq privCall wipe)) fun _ _ => True := by
  refine RelCT.seq (two_post (Ψ := Ψ5) (callArgs_taint (pins_nil _)) fun d u ⟨s, φ, B, hs⟩ => ?_) ?_
  · have h := sPre_of φ.1
    have he := B.enc
    revert he
    cases hc : encOut s with
    | none => rw [hc] at hs; cases hs
    | some em => intro ⟨_, hb⟩; exact WP.mono (callArgs_ok h B hb) fun v C => ⟨s, em, φ, C⟩
  refine RelCT.seq (two_post (Ψ := Ψ6) priv_rel fun d u ⟨s, em, φ, C⟩ =>
    call_ok (sPre_of φ.1) C fun v R => ⟨s, em, φ, R⟩) ?_
  exact wipe_taint pins_Ψ6

theorem aft_rel : RelCT isa (Two Ψ2) afterEnc fun _ _ => True := by
  have hr3 : ∀ u₁ u₂, Two Ψ2 u₁ u₂ → u₁.gpr .r3 = u₂.gpr .r3 := by
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

theorem body_rel : RelCT isa (Two Φ1) body fun _ _ => True := by
  unfold body
  refine RelCT.seq (two_post (Ψ := Ψ1) (setup_taint (pins_nil _)) fun d u ⟨s, φ, e⟩ =>
    e ▸ WP.mono (setup_ok (sPre_of φ.1)) fun v A => ⟨s, φ, A⟩) ?_
  refine RelCT.seq (two_post (Ψ := Ψ2) (encode_taint pins_Ψ1) fun d u ⟨s, φ, A⟩ =>
    WP.mono (enc_ok (sPre_of φ.1) A) fun v B => ⟨s, φ, B⟩) ?_
  refine RelCT.seq (two_post (Ψ := Ψ8) aft_rel fun d u ⟨s, φ, B⟩ =>
    WP.mono (afterEnc_ok (sPre_of φ.1) B) fun v ⟨F, _⟩ => ⟨s, φ, F⟩) ?_
  exact restore_taint (pins_nil _)

theorem code_rel : RelCT isa (Two Φ0) code fun _ _ => True :=
  RelCT.alloc (fun _ _ ⟨_, _, _, hsp⟩ => hsp) (body_rel.mono (fun a b ⟨s, t, ⟨d, φs, φt, hsp⟩, ea, eb⟩ =>
    ⟨d, ⟨s, φs, ea⟩, ⟨t, φt, eb⟩, by rw [ea, eb]; simp only [allocated, hsp]⟩) fun _ _ h => h)

theorem code_ct : ConstantTime isa (Spec.RsaPkcs1Sig.signContract abi stackBytes).pre
    (Spec.RsaPkcs1Sig.signContract abi stackBytes).pub code :=
  RelCT.constantTime (code_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨dataOf s, ⟨hs, rfl⟩, ⟨ht, (pub_data hp).symm⟩, (same_of (pub_data hp)).sp⟩) fun _ _ h => h)

end VG.Proof.RsaPkcs1Sig.PPC64LE.Sign
