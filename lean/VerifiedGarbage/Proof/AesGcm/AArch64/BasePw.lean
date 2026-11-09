module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Verified
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenVerified
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenTo
public import VerifiedGarbage.Proof.Framework.AArch64.TrailingRo
public import VerifiedGarbage.Spec.Gcm.Powers8
import VerifiedGarbage.Proof.AesGcm.Rounds
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.SealPw
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenPw
import VerifiedGarbage.Proof.AesGcm.ScratchPowers8
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Verified
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenVerified
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenTo
meta import VerifiedGarbage.Proof.Framework.AArch64.TrailingRo
meta import VerifiedGarbage.Spec.Gcm.Powers8
meta import VerifiedGarbage.Proof.AesGcm.Rounds
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.SealPw
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenPw
meta import VerifiedGarbage.Proof.AesGcm.ScratchPowers8
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_aes_gcm_{seal,open,open_to}_with_powers` from `vg_aes_gcm_{seal,open,open_to}` (AArch64)

For implementations without code that reads the powers, `seal_with_powers`,
`open_with_powers` and `open_to_with_powers` are `seal`, `open` and
`open_to`: the same code, which never
reads the powers' buffer, its address the stack argument after theirs.
`AArch64.Verified.dropTrailingRo` moves their proofs to the contracts with
the buffer, whose preconditions add the powers to theirs and whose
postconditions and leaks are theirs (`Spec.Gcm.sealWithPowersContract`,
`Spec.Gcm.openWithPowersContract`, `Spec.Gcm.openToWithPowersContract`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64

open VG.AArch64

/-! ## The contracts with the buffer, from those without -/

/-- `sealWithPowersPre` gives `sealPre`, of the arguments but the buffer. -/
theorem sealWithPowersPre_imp : ∀ (vs : List (BitVec 64)) (x : BitVec 64) (m : Mem),
    vs.length = (Spec.Gcm.sealSig.words abi.ptrBits).length →
    Curry.apply _ (Spec.Gcm.sealWithPowersPre abi.ptrBits) (vs ++ [x]) m →
      Curry.apply _ (Spec.Gcm.sealPre abi.ptrBits) vs m := by
  intro vs x m hl h
  rcases vs with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8,
    _ | ⟨a9, _ | ⟨a10, vs⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp [Spec.Gcm.sealSig, Sig.words, Param.words] at hl
  exact h.1

/-- `sealPost` gives `sealWithPowersPost`, which ignores the buffer. -/
theorem sealWithPowersPost_of : ∀ (vs : List (BitVec 64)) (x : BitVec 64) (m m' : Mem) r,
    vs.length = (Spec.Gcm.sealSig.words abi.ptrBits).length →
    Curry.apply _ (Spec.Gcm.sealPost abi.ptrBits) vs m m' r →
      Curry.apply ((Spec.Gcm.sealSig.withRo "pw" .u64 16).words abi.ptrBits)
        (Spec.Gcm.sealWithPowersPost abi.ptrBits) (vs ++ [x]) m m' r := by
  intro vs x m m' r hl h
  rcases vs with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8,
    _ | ⟨a9, _ | ⟨a10, vs⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp [Spec.Gcm.sealSig, Sig.words, Param.words] at hl
  exact h

/-- `openWithPowersPre` gives `openPre`, of the arguments but the buffer. -/
theorem openWithPowersPre_imp : ∀ (vs : List (BitVec 64)) (x : BitVec 64) (m : Mem),
    vs.length = (Spec.Gcm.openSig.words abi.ptrBits).length →
    Curry.apply _ (Spec.Gcm.openWithPowersPre abi.ptrBits) (vs ++ [x]) m →
      Curry.apply _ (Spec.Gcm.openPre abi.ptrBits) vs m := by
  intro vs x m hl h
  rcases vs with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8,
    _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, vs⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp [Spec.Gcm.openSig, Sig.words, Param.words] at hl
  exact h.1

/-- `openPost` gives `openWithPowersPost`, which ignores the buffer. -/
theorem openWithPowersPost_of : ∀ (vs : List (BitVec 64)) (x : BitVec 64) (m m' : Mem) r,
    vs.length = (Spec.Gcm.openSig.words abi.ptrBits).length →
    Curry.apply _ (Spec.Gcm.openPost abi.ptrBits) vs m m' r →
      Curry.apply ((Spec.Gcm.openSig.withRo "pw" .u64 16).words abi.ptrBits)
        (Spec.Gcm.openWithPowersPost abi.ptrBits) (vs ++ [x]) m m' r := by
  intro vs x m m' r hl h
  rcases vs with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8,
    _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, vs⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp [Spec.Gcm.openSig, Sig.words, Param.words] at hl
  exact h

/-- `openWithPowersLeak` is `openLeak`, which ignores the buffer. -/
theorem openWithPowersLeak_agree : ∀ (vs₁ : List (BitVec 64)) (x₁ : BitVec 64) (m₁ : Mem)
    (vs₂ : List (BitVec 64)) (x₂ : BitVec 64) (m₂ : Mem),
    vs₁.length = (Spec.Gcm.openSig.words abi.ptrBits).length →
    vs₂.length = (Spec.Gcm.openSig.words abi.ptrBits).length →
    leakAgree (ws := (Spec.Gcm.openSig.withRo "pw" .u64 16).words abi.ptrBits)
        (some (Spec.Gcm.openWithPowersLeak abi.ptrBits)) (vs₁ ++ [x₁]) m₁ (vs₂ ++ [x₂]) m₂ →
      leakAgree (some (Spec.Gcm.openLeak abi.ptrBits)) vs₁ m₁ vs₂ m₂ := by
  intro vs₁ x₁ m₁ vs₂ x₂ m₂ hl₁ hl₂ h
  rcases vs₁ with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8,
    _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, vs₁⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp [Spec.Gcm.openSig, Sig.words, Param.words] at hl₁
  rcases vs₂ with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | ⟨b8,
    _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, vs₂⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp [Spec.Gcm.openSig, Sig.words, Param.words] at hl₂
  exact h

/-- `openToWithPowersPre` gives `openToPre`, of the arguments but the buffer. -/
theorem openToWithPowersPre_imp : ∀ (vs : List (BitVec 64)) (x : BitVec 64) (m : Mem),
    vs.length = (Spec.Gcm.openToSig.words abi.ptrBits).length →
    Curry.apply _ (Spec.Gcm.openToWithPowersPre abi.ptrBits) (vs ++ [x]) m →
      Curry.apply _ (Spec.Gcm.openToPre abi.ptrBits) vs m := by
  intro vs x m hl h
  rcases vs with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8,
    _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | ⟨a13, vs⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp [Spec.Gcm.openToSig, Sig.words, Param.words] at hl
  exact h.1

/-- `openToRoundsPost` gives `openToWithPowersRoundsPost`, which ignores the
buffer. -/
theorem openToWithPowersPost_of : ∀ (vs : List (BitVec 64)) (x : BitVec 64) (m m' : Mem) r,
    vs.length = (Spec.Gcm.openToSig.words abi.ptrBits).length →
    Curry.apply _ (Proof.AesGcm.openToRoundsPost abi.ptrBits) vs m m' r →
      Curry.apply ((Spec.Gcm.openToSig.withRo "pw" .u64 16).words abi.ptrBits)
        (Proof.AesGcm.openToWithPowersRoundsPost abi.ptrBits) (vs ++ [x]) m m' r := by
  intro vs x m m' r hl h
  rcases vs with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8,
    _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | ⟨a13, vs⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp [Spec.Gcm.openToSig, Sig.words, Param.words] at hl
  exact h

/-- `openToWithPowersLeak` is `openToLeak`, which ignores the buffer. -/
theorem openToWithPowersLeak_agree : ∀ (vs₁ : List (BitVec 64)) (x₁ : BitVec 64) (m₁ : Mem)
    (vs₂ : List (BitVec 64)) (x₂ : BitVec 64) (m₂ : Mem),
    vs₁.length = (Spec.Gcm.openToSig.words abi.ptrBits).length →
    vs₂.length = (Spec.Gcm.openToSig.words abi.ptrBits).length →
    leakAgree (ws := (Spec.Gcm.openToSig.withRo "pw" .u64 16).words abi.ptrBits)
        (some (Spec.Gcm.openToWithPowersLeak abi.ptrBits)) (vs₁ ++ [x₁]) m₁ (vs₂ ++ [x₂]) m₂ →
      leakAgree (some (Spec.Gcm.openToLeak abi.ptrBits)) vs₁ m₁ vs₂ m₂ := by
  intro vs₁ x₁ m₁ vs₂ x₂ m₂ hl₁ hl₂ h
  rcases vs₁ with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8,
    _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | ⟨a13, vs₁⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp [Spec.Gcm.openToSig, Sig.words, Param.words] at hl₁
  rcases vs₂ with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | ⟨b8,
    _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, vs₂⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp [Spec.Gcm.openToSig, Sig.words, Param.words] at hl₂
  exact h

/-! ## Satisfiable -/

theorem sealBasePwSat_pre : ∃ s, (Spec.Gcm.sealWithPowersContract AArch64.abi 2576).pre s := by
  refine ⟨Fast.sealFrameSatPw, ?_⟩
  sig_pre [Spec.Gcm.sealWithPowersContract, Spec.Gcm.sealWithPowersSig, Spec.Gcm.sealSig,
    Spec.Gcm.withPowersParam, Spec.Gcm.sealWithPowersPre, Spec.Gcm.sealPre,
    Spec.Gcm.sealWithPowersPost, Spec.Gcm.sealPost, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
    AArch64.stackArgAddr, List.getD, List.range, List.range.loop, List.cons_append, List.nil_append,
    Fast.sealFrameSatPw, Fast.sealSatPw, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.powers8Repr_of_zeroMem (by decide) Fast.sealSatPw_zero

theorem openBasePwSat_pre : ∃ s, (Spec.Gcm.openWithPowersContract AArch64.abi 2592).pre s := by
  refine ⟨Fast.openFrameSatPw, ?_⟩
  sig_pre [Spec.Gcm.openWithPowersContract, Spec.Gcm.openWithPowersSig, Spec.Gcm.openSig,
    Spec.Gcm.withPowersParam, Spec.Gcm.openWithPowersPre, Spec.Gcm.openPre,
    Spec.Gcm.openWithPowersPost, Spec.Gcm.openPost, Spec.Gcm.openWithPowersLeak, Spec.Gcm.openLeak,
    AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
    List.range.loop, List.cons_append, List.nil_append, Fast.openFrameSatPw, Fast.openSatPw, openSat,
    stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.powers8Repr_of_zeroMem (by decide) Fast.openSatPw_zero

/-! ## The functions -/

/-- `vg_aes_gcm_seal_with_powers` of the implementations `v`: their `seal`. -/
theorem sealBasePw_verified (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 2576 1 (sealCode v))
      (Spec.Gcm.sealWithPowersContract AArch64.abi 2576) :=
  Verified.dropTrailingRo (sig := Spec.Gcm.sealSig) (nm := "pw") (e := .u64) (n := 16)
    (Proof.AesGcm.seal_keyed (sealCode_framed v hMK)) (by decide) sealWithPowersPre_imp
    sealWithPowersPost_of (fun _ _ _ _ _ _ _ _ _ => trivial) sealBasePwSat_pre

/-- `vg_aes_gcm_open_with_powers` of the implementations `v`: their `open`. -/
theorem openBasePw_verified (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (openCode v))
      (Spec.Gcm.openWithPowersContract AArch64.abi 2592) :=
  Verified.dropTrailingRo (sig := Spec.Gcm.openSig) (nm := "pw") (e := .u64) (n := 16)
    (Proof.AesGcm.open_keyed (openCode_framed v hMK)) (by decide) openWithPowersPre_imp
    openWithPowersPost_of openWithPowersLeak_agree openBasePwSat_pre

/-- `vg_aes_gcm_open_to_with_powers` of the implementations `v`: their
`open_to`. -/
theorem openToBasePw_verified (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 2608 4 (openToCode v))
      (Spec.Gcm.openToWithPowersContract AArch64.abi 2608) :=
  Proof.AesGcm.openToWithPowers_keyed <|
    Verified.dropTrailingRo (sig := Spec.Gcm.openToSig) (nm := "pw") (e := .u64) (n := 16)
      (openToCode_framed v hMK) (by decide) openToWithPowersPre_imp
      openToWithPowersPost_of openToWithPowersLeak_agree Fast.openToFrameSatPw_pre

end VG.Proof.AesGcm.AArch64
