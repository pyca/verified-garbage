module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignContractInput
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignP.Pre
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignRegions
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Contract

/-! # `vg_rsa_pkcs1_sign_precomputed` on i686: its precondition

`signPrecomputedContract`'s precondition gives `vg_rsa_pkcs1_sign`'s
(`SignABI`) and `pre`'s facts (`SPreABI`, `signABIP_of`), and so the wrapper's
inputs and `SPreCtx` where its body starts (`sign_contractP_pre`).
-/

-- separate module: the precondition builds in parallel with the body's proof (`SignP.Fn`).

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (argumentPointer)

/-- What `vg_rsa_pkcs1_sign_precomputed`'s precondition adds to `SignABI`: its arguments 21
and 22, `pre` and `pre_len`. -/
structure SPreABI (s : State) : Prop where
  high : (s.gpr .esp).toNat + 96 ≤ 2 ^ 32
  preR : (⟨argumentPointer s 21, (arg s 22).toNat * 8⟩ : Region) ∈ s.rd
  argsW : (⟨argAddr s 0, 92⟩ : Region) ∈ s.wr
  outPre : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 21, (arg s 22).toNat * 8⟩
  wsPre : (⟨argumentPointer s 19, (arg s 20).toNat * 8⟩ : Region).Disjoint
    ⟨argumentPointer s 21, (arg s 22).toNat * 8⟩
  outArgs : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 92⟩
  wsArgs : (⟨argumentPointer s 19, (arg s 20).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 92⟩
  stackPre : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint
    ⟨argumentPointer s 21, (arg s 22).toNat * 8⟩
  stackArgs : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint
    ⟨argAddr s 0, 92⟩
  preFit : (arg s 21).toNat + (arg s 22).toNat * 8 ≤ 2 ^ 32
  preLen : (arg s 22).toNat =
    Spec.Rsa.privatePrecomputedWords (arg s 3).toNat (arg s 10).toNat (arg s 12).toNat
  key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 9) (arg s 10).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 11) (arg s 12).toNat) =
    some (Spec.Rsa.wordsAt s.mem (argumentPointer s 21) (arg s 22).toNat)

theorem signABIP_of {s : State}
    (h : (Spec.RsaPkcs1Sig.signPrecomputedContract abi sigStack).pre s) : SignABI s ∧ SPreABI s := by
  sig_pre [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
    Spec.RsaPkcs1Sig.signSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  simp only [sigStack] at *
  have sub84 : Region.Sub ⟨argAddr s 0, 84⟩ ⟨argAddr s 0, 92⟩ := Region.sub_of_ble rfl
  refine ⟨?_, ?_⟩ <;> constructor <;> try simp only [sigStack]
  all_goals first
    | with_reducible assumption
    | (apply Region.Disjoint.sub_right (r₂ := ⟨argAddr s 0, 92⟩) _ sub84; with_reducible assumption)
    | (intro r hr; rw [‹s.rd = _›]; exact List.mem_append_left [_] hr)
    | (rw [‹s.rd = _›]; simp)
    | (rw [‹s.wr = _›]; simp)
    | (rw [‹s.wr = _›]
       exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
         by simp [Region.Contains]⟩)
    | omega_arith

section
variable {s : State}

theorem argument_addrS (A : SignABI s) {d : Nat} :
    byteAddr (signGeometry s).stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + d) =
      argAddr s 0 + BitVec.ofNat 64 d := by
  rw [← Offset.add_add]
  change (signGeometry s).argumentsRegion.base + _ = _
  rw [signGeometry_arguments s A.stackLow A.stackBound]

theorem argAddr_highS (B : SPreABI s) {j : Nat} (hj : j < 23) :
    argAddr s j = argAddr s 0 + BitVec.ofNat 64 (4 * j) := by
  have first := byteAddr_add (by have := B.high; omega_using [this] : (s.gpr .esp).toNat + 4 < 2 ^ 32)
  have last := byteAddr_add (by have := B.high; omega_using [hj, this] : (s.gpr .esp).toNat + (4 + 4 * j) < 2 ^ 32)
  change byteAddr (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * j)) =
    byteAddr (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)) + _
  rw [last, Nat.mul_zero, Nat.add_zero, first, Offset.add_add]

theorem bodyWrites_apartS (A : SignABI s) (E : EntryInput (signGeometry s) (signBytes s) s) {x : Region}
    (hs : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint x)
    (ho : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint x)
    (hw : (⟨argumentPointer s 19, (arg s 20).toNat * 8⟩ : Region).Disjoint x) :
    ∀ r ∈ bodyWrites (signGeometry s), x.Disjoint r := by
  rw [← signGeometry_wholeStack s A.stackLow] at hs
  rw [A.outLen] at ho
  rw [show (arg s 20).toNat * 8 = 8 * (arg s 20).toNat from Nat.mul_comm _ _] at hw
  intro r hr
  simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hs.sub_left E.valid.innerSub).symm
  · exact (hs.sub_left E.valid.calleeSub).symm
  · exact ho.symm
  · exact hw.symm

/-- The precomputed contract's precondition: the wrapper's inputs, and `SPreCtx` where its body
starts. -/
theorem sign_contractP_pre (h : (Spec.RsaPkcs1Sig.signPrecomputedContract abi sigStack).pre s) :
    FnInput (signGeometry s) (signBytes s) s ∧
      SPreCtx (signGeometry s) (signBytes s) (arg s 21) (arg s 22).toNat (entered s) := by
  obtain ⟨A, B⟩ := signABIP_of h
  have E := sign_abi_entry s A
  refine ⟨E.ready, ?_⟩
  have savedSep : ∀ {x : Region},
      (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint x →
      ∀ r ∈ [(signGeometry s).savedRegion], x.Disjoint r := by
    intro x hs r hr
    obtain rfl := List.mem_singleton.mp hr
    rw [← signGeometry_wholeStack s A.stackLow] at hs
    exact (hs.sub_left E.valid.savedSub).symm
  have word : ∀ d, d + 4 ≤ 8 → (entered s).mem.readW (byteAddr (signGeometry s).stack +
      BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + (84 + d))) 32 =
      s.mem.readW (argAddr s 0 + BitVec.ofNat 64 (84 + d)) 32 := by
    intro d hd
    rw [argument_addrS A]
    exact E.enteredFrame.readW (Offset.contains_base _ (by omega_using [hd] : 84 + d + 32 / 8 ≤ 92) (by omega_using [hd]))
      (savedSep B.stackArgs) (by decide)
  have args8 : Region.Sub ⟨argAddr s 0 + BitVec.ofNat 64 84, 8⟩ ⟨argAddr s 0, 92⟩ :=
    Offset.sub_base _ (by decide)
  have pre8 : (⟨argumentPointer s 21, (arg s 22).toNat * 8⟩ : Region) =
      ⟨byteAddr (arg s 21), 8 * (arg s 22).toNat⟩ := by
    rw [Nat.mul_comm]; rfl
  have e88 : VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + 88 =
      VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + (84 + 4) := rfl
  have e84 : VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + 84 =
      VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + (84 + 0) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [signGeometry_stackNat s A.stackLow]
    have := A.stackLow; have := B.high
    simp only [sigStack, VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes] at *; omega_using [this]
  · have w := word 0 (by decide)
    rw [← argAddr_highS B (by decide : 21 < 23)] at w
    rw [e84]; exact w
  · have w := word 4 (by decide)
    rw [← argAddr_highS B (by decide : 22 < 23)] at w
    rw [e88, w]
    exact ((BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)).symm
  · rw [argument_addrS A]
    exact entered_read ⟨_, List.mem_append_right _ B.argsW, Offset.contains_base _ (by decide) (by decide)⟩
  · intro r hr
    rw [argument_addrS A]
    exact bodyWrites_apartS A E (B.stackArgs.sub_right args8) (B.outArgs.sub_right args8)
      (B.wsArgs.sub_right args8) r hr
  · refine entered_read ⟨_, List.mem_append_left _ B.preR, ?_⟩
    rw [pre8]; exact Region.contains_self _ _
  · have := B.preFit; omega_using [this]
  · rw [← pre8]
    exact bodyWrites_apartS A E B.stackPre B.outPre B.wsPre
  · rw [B.preLen]; rfl
  · rw [VG.Proof.Rsa.wordsAt_frame E.enteredFrame (by have := B.preFit; omega_using [])
      (savedSep (by rw [← pre8]; exact B.stackPre))]
    exact B.key
end
end VG.Proof.RsaPkcs1Sig.X86.Sgn
