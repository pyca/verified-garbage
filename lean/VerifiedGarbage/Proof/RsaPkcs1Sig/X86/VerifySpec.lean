module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyAfter
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Weierstrass.PointContract

/-! # The byte comparison is the RFC verification procedure -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Proof.Bignum.X86

def verifiedResult (g : Geometry) (bs : Fin 5 → List Byte) : BitVec 32 :=
  if Spec.RsaPkcs1Sig.verifyId (bs 0) (bs 1) g.hash.toNat (bs 2) (bs 3) then 1 else 0

theorem verifiedResult_eq {g : Geometry} {bs : Fin 5 → List Byte}
    (nlen : (bs 0).length = g.length) (siglen : (bs 3).length = g.length) :
    verifiedResult g bs = match Spec.Rsa.publicOpChecked (bs 0) (bs 1) (bs 3), encodeId g.hash (bs 2) g.length with
      | some x, some y => BitVec.ofNat 32 (decide (x = y)).toNat
      | _, _ => 0 := by
  unfold verifiedResult Spec.RsaPkcs1Sig.verifyId encodeId
  cases id : Spec.RsaPkcs1Sig.Hash.ofId g.hash.toNat with
  | none =>
    simp only [Bool.false_eq_true, ite_false, Option.bind_none]
    cases Spec.Rsa.publicOpChecked (bs 0) (bs 1) (bs 3) <;> rfl
  | some h =>
    dsimp only
    simp only [VG.Proof.RsaPkcs1Sig.verify_eq_verifyRfc]
    unfold Spec.RsaPkcs1Sig.verifyRfc
    rw [nlen, ite_eq_left siglen]
    simp only [Option.bind_some]
    cases Spec.Rsa.publicOpChecked (bs 0) (bs 1) (bs 3) with
    | none => cases Spec.RsaPkcs1Sig.encode h (bs 2) g.length <;> rfl
    | some x =>
      cases Spec.RsaPkcs1Sig.encode h (bs 2) g.length with
      | none => rfl
      | some y =>
        by_cases eq : x = y
        · simp only [eq, beq_self_eq_true, ite_true, decide_true]; rfl
        · simp only [beq_eq_false_iff_ne.mpr eq, Bool.false_eq_true, ite_false, decide_eq_false eq]; rfl

theorem checkedResult_eq {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (nlen : (bs 0).length = g.length) (siglen : (bs 3).length = g.length)
    (post : Spec.Rsa.written s.mem (byteAddr g.em1) g.length (s.gpr .eax)
      (Spec.Rsa.publicOpChecked (bs 0) (bs 1) (bs 3))) :
    checkedResult g bs s = verifiedResult g bs := by
  rw [verifiedResult_eq nlen siglen]
  cases op : Spec.Rsa.publicOpChecked (bs 0) (bs 1) (bs 3) with
  | none =>
    rw [op] at post
    unfold checkedResult
    cases encodeId g.hash (bs 2) g.length <;> dsimp only <;>
      simp only [post.1, show (0 : BitVec 32) = 0#32 from rfl, BitVec.and_zero]
  | some em =>
    rw [op] at post
    unfold checkedResult
    cases enc : encodeId g.hash (bs 2) g.length with
    | none => rfl
    | some expected =>
      dsimp only
      rw [post.1, post.2]
      cases eq : decide (em = expected) <;> rfl

end VG.Proof.RsaPkcs1Sig.X86.Ver
