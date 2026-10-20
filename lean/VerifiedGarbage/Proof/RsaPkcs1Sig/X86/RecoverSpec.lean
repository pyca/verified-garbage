module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverAfter
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.RsaPkcs1Sig.Recover
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem

/-! # Re-encoding the trailing digest implements the shared recovery specification -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86

def recovered (g : Geometry) (bs : Fin 4 → List Byte) : Option (List Byte) :=
  (Spec.RsaPkcs1Sig.Hash.ofId g.hash.toNat).bind fun h => Spec.RsaPkcs1Sig.recover (bs 0) (bs 1) h (bs 2)

theorem digestBytes_drop {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    digestBytes g s = (Spec.Rsa.bytesAt s.mem (byteAddr g.em1) g.length).drop (g.length - g.outputLength) := by
  unfold digestBytes
  rw [h.valid.digestAddr, ← VG.Proof.RsaPkcs1Sig.bytesAt_drop]
  rw [Nat.sub_add_cancel h.valid.outputFits]

theorem checkedPublicRecovery_eq {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) (siglen : g.signatureLength = g.length)
    (post : Spec.Rsa.written s.mem (byteAddr g.em1) g.length (s.gpr .eax)
      (Spec.Rsa.publicOpChecked (bs 0) (bs 1) (bs 2))) :
    checkedPublicRecovery g s = recovered g bs := by
  obtain ⟨hash, id, outlen⟩ := h.valid.hashValid
  have nlen : (bs 0).length = g.length := (h.sources 0).length
  have slen : (bs 2).length = g.length := (h.sources 2).length.trans siglen
  unfold recovered
  rw [id, Option.bind_some, VG.Proof.RsaPkcs1Sig.recover_eq_recoverEnc]
  unfold VG.Proof.RsaPkcs1Sig.recoverEnc
  rw [nlen, ite_eq_left slen]
  cases op : Spec.Rsa.publicOpChecked (bs 0) (bs 1) (bs 2) with
  | none =>
    rw [op] at post
    unfold checkedPublicRecovery
    cases encodeId g.hash (digestBytes g s) g.length with
    | none => rfl
    | some expected =>
      dsimp only
      rw [post.1]
      simp only [show ((0 : BitVec 32).getLsbD 0) = false from rfl, Bool.and_false, Bool.false_eq_true, ite_false]
  | some em =>
    rw [op] at post
    have digest : digestBytes g s = em.drop (g.length - hash.len) := by
      rw [digestBytes_drop h, post.2, outlen]
    unfold checkedPublicRecovery encodeId
    rw [id, Option.bind_some, digest, post.1, post.2]
    simp only [show ((1 : BitVec 32).getLsbD 0) = true from rfl, Bool.and_true]
    cases encoding : Spec.RsaPkcs1Sig.encode hash (em.drop (g.length - hash.len)) g.length with
    | none => simp
    | some expected =>
      by_cases eq : em = expected
      · subst expected
        simp only [decide_true, ite_true]
      · simp only [decide_eq_false eq, Bool.false_eq_true, ite_false,
          Option.some.injEq, Ne.symm eq]

end VG.Proof.RsaPkcs1Sig.X86.Rcv
