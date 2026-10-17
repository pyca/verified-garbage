module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.Arm.Decrypt
public import VerifiedGarbage.Proof.Sha256.Arm.Shared
public import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Frame
public import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Sha256
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha256
public import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Sha256
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RSAES-PKCS1-v1_5 decryption on ARMv7: the SHA-256 and HMAC-SHA-256 functions it calls

`decFns`: SHA-256's `init`, `update` and `finalize` and HMAC-SHA-256's
`init` and `finalize`, the ARMv7 artifacts (`Artifacts/Sha256/Arm.lean`,
`Artifacts/HmacSha256/Arm.lean`), each with the working space in its own
frame; their proofs, and the stack they use.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm

open VG VG.Arm

/-- The functions decryption calls. -/
def decFns : Impl.RsaPkcs1Enc.Arm.Decrypt.Fns where
  initN := Spec.Sha256.initApi.name
  initC := Impl.Sha256.Arm.Stream.init
  updN := Spec.Sha256.updateApi.name
  updC := Impl.StackScratch.Arm.withStackScratch 624 2 Impl.Sha256.Arm.Stream.update
  finN := Spec.Sha256.finalizeApi.name
  finC := Impl.StackScratch.Arm.withStackScratch 624 1 Impl.Sha256.Arm.Stream.finalize
  hiN := Spec.Hmac.sha256I.initApi.name
  hiC := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha256I) 0
    Proof.Pbkdf2.Md.Arm.sha256Md.hmacInit
  hfN := Spec.Hmac.sha256I.finalizeApi.name
  hfC := Impl.StackScratch.Arm.withStackScratch (Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha256I) 1
    Proof.Pbkdf2.Md.Arm.sha256Md.hmacFin

theorem frame_eq : 16 + Proof.Pbkdf2.Md.Arm.frame Spec.Hmac.sha256I = 880 := by decide

theorem initV : Verified target decFns.initC (Spec.Sha256.initContract abi) := Proof.Sha256.Arm.Shared.init
theorem updV : Verified target decFns.updC (Spec.Sha256.updateContract abi 624) := Proof.Sha256.Arm.Shared.update
theorem finV : Verified target decFns.finC (Spec.Sha256.finalizeContract abi 624) :=
  Proof.Sha256.Arm.Shared.finalize

theorem hiV : Verified target decFns.hiC (Spec.Hmac.sha256I.initContract abi 880) := by
  have h := Proof.Pbkdf2.Md.Arm.initFramed Proof.Pbkdf2.Md.Arm.Instances.sha256_init
    Proof.Pbkdf2.Md.Arm.sha256_initFrameSat
  rw [frame_eq] at h
  exact h

theorem hfV : Verified target decFns.hfC (Spec.Hmac.sha256I.finalizeContract abi 880) := by
  have h := Proof.Pbkdf2.Md.Arm.finFramed Proof.Pbkdf2.Md.Arm.Instances.sha256_finalize
    Proof.Hmac.sha256_local Proof.Pbkdf2.Md.Arm.sha256_finFrameSat
  rw [frame_eq] at h
  exact h

theorem armStack_zero {c : Prog isa} (h : c.noFrames = true) : FrameStack.armStack c = 0 := by
  induction c <;> simp_all [Code.noFrames, FrameStack.armStack]

theorem initS : FrameStack.armStack decFns.initC ≤ 0 :=
  Nat.le_of_eq (armStack_zero Proof.Pbkdf2.Stream.Arm.sha256OK.initNF)

theorem updS : FrameStack.armStack decFns.updC ≤ 624 := by
  have := armStack_zero Proof.Pbkdf2.Stream.Arm.sha256OK.updNF
  simp only [decFns, Impl.StackScratch.Arm.withStackScratch, FrameStack.armStack] at this ⊢
  simp only [Proof.Pbkdf2.Stream.Arm.sha256H] at this
  omega

theorem finS : FrameStack.armStack decFns.finC ≤ 624 := by
  have := armStack_zero Proof.Pbkdf2.Stream.Arm.sha256OK.finNF
  simp only [decFns, Impl.StackScratch.Arm.withStackScratch, FrameStack.armStack] at this ⊢
  simp only [Proof.Pbkdf2.Stream.Arm.sha256H] at this
  omega

theorem hiS : FrameStack.armStack decFns.hiC ≤ 880 := by
  have := Proof.Pbkdf2.Whole.Arm.sha256OKF.hiSt
  have e := frame_eq
  simp only [decFns, Impl.StackScratch.Arm.withStackScratch, FrameStack.armStack] at this ⊢
  simp only [Proof.Pbkdf2.Whole.Arm.sha256F, Proof.Pbkdf2.Whole.Arm.fnsOf] at this
  omega

theorem hfS : FrameStack.armStack decFns.hfC ≤ 880 := by
  have := Proof.Pbkdf2.Whole.Arm.sha256OKF.hfSt
  have e := frame_eq
  simp only [decFns, Impl.StackScratch.Arm.withStackScratch, FrameStack.armStack] at this ⊢
  simp only [Proof.Pbkdf2.Whole.Arm.sha256F, Proof.Pbkdf2.Whole.Arm.fnsOf] at this
  omega

end VG.Proof.RsaPkcs1Enc.Arm
