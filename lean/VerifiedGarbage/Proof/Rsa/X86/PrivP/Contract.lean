module

public import VerifiedGarbage.Proof.Rsa.X86.PrivContractInput
public import VerifiedGarbage.Proof.Rsa.X86.PrivP.Pre
import VerifiedGarbage.Proof.Rsa.X86.PrivRegions
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Rsa.Contract

/-! # `vg_rsa_private_checked_precomputed` on x86: its precondition

`privateCheckedPrecomputedContract`'s precondition gives `vg_rsa_private_checked`'s
(`PrivABI`) and `pre`'s facts (`PreABI`, `privateABIP_of`), and so the
wrapper's inputs and `PreCtx` where its body starts (`private_contractP_pre`).
-/

-- separate module: the precondition builds in parallel with the body's proof (`PrivP.Fn`).

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (argumentPointer)

/-- What `vg_rsa_private_checked_precomputed`'s precondition adds to `PrivABI`: its arguments 20
and 21, `pre` and `pre_len`. -/
structure PreABI (s : State) : Prop where
  high : (s.gpr .esp).toNat + 92 ≤ 2 ^ 32
  preR : (⟨argumentPointer s 20, (arg s 21).toNat * 8⟩ : Region) ∈ s.rd
  argsW : (⟨argAddr s 0, 88⟩ : Region) ∈ s.wr
  outPre : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 20, (arg s 21).toNat * 8⟩
  wsPre : (⟨argumentPointer s 18, (arg s 19).toNat * 8⟩ : Region).Disjoint
    ⟨argumentPointer s 20, (arg s 21).toNat * 8⟩
  outArgs : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 88⟩
  wsArgs : (⟨argumentPointer s 18, (arg s 19).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 88⟩
  stackPre : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint
    ⟨argumentPointer s 20, (arg s 21).toNat * 8⟩
  stackArgs : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint
    ⟨argAddr s 0, 88⟩
  preFit : (arg s 20).toNat + (arg s 21).toNat * 8 ≤ 2 ^ 32
  preLen : (arg s 21).toNat =
    Spec.Rsa.privatePrecomputedWords (arg s 3).toNat (arg s 9).toNat (arg s 11).toNat
  key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 8) (arg s 9).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 10) (arg s 11).toNat) =
    some (Spec.Rsa.wordsAt s.mem (argumentPointer s 20) (arg s 21).toNat)

theorem privateABIP_of {s : State}
    (h : (Proof.Rsa.privateCheckedPrecomputedContract abi stackBytes).pre s) : PrivABI s ∧ PreABI s := by
  sig_pre [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  simp only [stackBytes] at *
  have sub80 : Region.Sub ⟨argAddr s 0, 80⟩ ⟨argAddr s 0, 88⟩ := Region.sub_of_ble rfl
  refine ⟨?_, ?_⟩ <;> constructor <;> try simp only [stackBytes]
  all_goals first
    | with_reducible assumption
    | (apply Region.Disjoint.sub_right (r₂ := ⟨argAddr s 0, 88⟩) _ sub80; with_reducible assumption)
    | (intro r hr; rw [‹s.rd = _›]; exact List.mem_append_left [_] hr)
    | (rw [‹s.rd = _›]; simp)
    | (rw [‹s.wr = _›]; simp)
    | (rw [‹s.wr = _›]
       exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
         by simp [Region.Contains]⟩)
    | omega_arith

section
variable {s : State}

/-- The wrapper's frame and arguments from `esp`: argument `j` at `frameBytes + 20 + 4 j`. -/
theorem argument_addr (A : PrivABI s) {d : Nat} :
    byteAddr (privateGeometry s).stack + BitVec.ofNat 64 (VG.Impl.Rsa.X86.PrivChecked.frameBytes + 20 + d) =
      argAddr s 0 + BitVec.ofNat 64 d := by
  rw [← Offset.add_add]
  change (privateGeometry s).argumentsRegion.base + _ = _
  rw [privateGeometry_arguments s A.stackLow A.stackBound]

theorem argAddr_high (B : PreABI s) {j : Nat} (hj : j < 22) :
    argAddr s j = argAddr s 0 + BitVec.ofNat 64 (4 * j) := by
  have first := byteAddr_add (by have := B.high; omega_using [this] : (s.gpr .esp).toNat + 4 < 2 ^ 32)
  have last := byteAddr_add (by have := B.high; omega_using [hj, this] : (s.gpr .esp).toNat + (4 + 4 * j) < 2 ^ 32)
  change byteAddr (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * j)) =
    byteAddr (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)) + _
  rw [last, Nat.mul_zero, Nat.add_zero, first, Offset.add_add]

/-- What the body writes, apart from a region apart from the stack, the output and the
workspace. -/
theorem bodyWrites_apart (A : PrivABI s) (E : PrivEntryInput (privateGeometry s) (privateBytes s) s)
    {x : Region}
    (hs : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint x)
    (ho : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint x)
    (hw : (⟨argumentPointer s 18, (arg s 19).toNat * 8⟩ : Region).Disjoint x) :
    ∀ r ∈ bodyWrites (privateGeometry s), x.Disjoint r := by
  rw [← privateGeometry_wholeStack s A.stackLow] at hs
  rw [A.outLen] at ho
  rw [show (arg s 19).toNat * 8 = 8 * (arg s 19).toNat from Nat.mul_comm _ _] at hw
  intro r hr
  simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hs.sub_left E.valid.innerSub).symm
  · exact (hs.sub_left E.valid.calleeSub).symm
  · exact ho.symm
  · exact hw.symm

/-- The precomputed contract's precondition: the wrapper's inputs, and `PreCtx` where its body
starts. -/
theorem private_contractP_pre (h : (Proof.Rsa.privateCheckedPrecomputedContract abi stackBytes).pre s) :
    PrivFnInput (privateGeometry s) (privateBytes s) s ∧
      PreCtx (privateGeometry s) (privateBytes s) (arg s 20) (arg s 21).toNat (entered s) := by
  obtain ⟨A, B⟩ := privateABIP_of h
  have E := private_abi_entry s A
  refine ⟨E.ready, ?_⟩
  have savedSep : ∀ {x : Region},
      (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint x →
      ∀ r ∈ [(privateGeometry s).savedRegion], x.Disjoint r := by
    intro x hs r hr
    obtain rfl := List.mem_singleton.mp hr
    rw [← privateGeometry_wholeStack s A.stackLow] at hs
    exact (hs.sub_left E.valid.savedSub).symm
  have word : ∀ d, d + 4 ≤ 8 → (entered s).mem.readW (byteAddr (privateGeometry s).stack +
      BitVec.ofNat 64 (VG.Impl.Rsa.X86.PrivChecked.frameBytes + 20 + (80 + d))) 32 =
      s.mem.readW (argAddr s 0 + BitVec.ofNat 64 (80 + d)) 32 := by
    intro d hd
    rw [argument_addr A]
    exact E.enteredFrame.readW (Offset.contains_base _ (by omega_using [hd] : 80 + d + 32 / 8 ≤ 88) (by omega_using [hd]))
      (savedSep B.stackArgs) (by decide)
  have args8 : Region.Sub ⟨argAddr s 0 + BitVec.ofNat 64 80, 8⟩ ⟨argAddr s 0, 88⟩ :=
    Offset.sub_base _ (by decide)
  have pre8 : (⟨argumentPointer s 20, (arg s 21).toNat * 8⟩ : Region) =
      ⟨byteAddr (arg s 20), 8 * (arg s 21).toNat⟩ := by
    rw [Nat.mul_comm]; rfl
  have hundred : VG.Impl.Rsa.X86.PrivChecked.frameBytes + 100 = VG.Impl.Rsa.X86.PrivChecked.frameBytes + 20 + 80 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [privateGeometry_stackNat s A.stackLow]
    have := A.stackLow; have := B.high
    simp only [stackBytes, VG.Impl.Rsa.X86.PrivChecked.frameBytes] at *; omega_using [this]
  · have w := word 0 (by decide)
    rw [← argAddr_high B (by decide : 20 < 22)] at w
    exact w
  · have w := word 4 (by decide)
    rw [← argAddr_high B (by decide : 21 < 22)] at w
    rw [w]
    exact ((BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)).symm
  · rw [hundred, argument_addr A]
    exact entered_read ⟨_, List.mem_append_right _ B.argsW, Offset.contains_base _ (by decide) (by decide)⟩
  · intro r hr
    rw [hundred, argument_addr A]
    exact bodyWrites_apart A E (B.stackArgs.sub_right args8) (B.outArgs.sub_right args8)
      (B.wsArgs.sub_right args8) r hr
  · refine entered_read ⟨_, List.mem_append_left _ B.preR, ?_⟩
    rw [pre8]; exact Region.contains_self _ _
  · have := B.preFit; omega_using [this]
  · rw [← pre8]
    exact bodyWrites_apart A E B.stackPre B.outPre B.wsPre
  · rw [B.preLen]; rfl
  · rw [VG.Proof.Rsa.wordsAt_frame E.enteredFrame (by have := B.preFit; omega_using [])
      (savedSep (by rw [← pre8]; exact B.stackPre))]
    exact B.key
end
end VG.Proof.Rsa.X86.PrivChecked
