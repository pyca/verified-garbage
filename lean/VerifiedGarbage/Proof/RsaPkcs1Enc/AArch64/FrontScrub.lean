module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Front
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Callees
public import VerifiedGarbage.Proof.Framework.AArch64.SideFill
public import VerifiedGarbage.Proof.Framework.QualifiedName
public import VerifiedGarbage.Proof.Rsa.AArch64.Scrub
public import VerifiedGarbage.Impl.Scrypt.AArch64.Scrypt
import VerifiedGarbage.Proof.Ffdh.AArch64.Scrub
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# `vg_rsa_pkcs1_decrypt_precomputed_front` on AArch64, without secret residue

The function as emitted (`Impl.RsaPkcs1Enc.AArch64.Fn.decryptPrecomputedFront`)
over any implementation of SHA-256's compression function and of the private
CRT operation: `Front.code`, calling `vg_rsa_pkcs1_decrypt_precomputed`'s
code before its cleanup as an internal function of its own (`bodyName`), then
the cleanup of the 3776 bytes of stack its frames (288) and the callee (3488)
use, and of the registers the code may write (`scrubOf`). What the cleanup
needs of the code is its own instructions', evaluated once with nothing in
the place of the functions decryption calls (as `Scrub.lean` does for
decryption), and the implementations' (their records').
-/

-- separate module: the kernel's evaluation of the cleanup's side condition, which a registration file may not hold

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Front

open VG VG.AArch64 VG.AArch64.Scrub
open VG.Proof.RsaPkcs1Sig.AArch64 (privP_side privP_depth)
open VG.Proof.Ffdh.AArch64.Scrub (bytesAt_of wordsAt_of toNat_sw)

/-- The name of `vg_rsa_pkcs1_decrypt_precomputed`'s code before its
cleanup, calling `h` and `c`, an internal function. -/
def bodyName (h : Proof.Sha256.AArch64.Compress) (c : Proof.Rsa.AArch64.CrtImpl) : String :=
  "vg_rsa_pkcs1_decrypt_precomputed_body" ++ qualifiedName "" [("sha256", h.suffix), ("crt", c.suffix)]

/-- `vg_rsa_pkcs1_decrypt_precomputed`'s code before its cleanup, over `h`
and `c`. -/
abbrev decCode (h : Proof.Sha256.AArch64.Compress) (c : Proof.Rsa.AArch64.CrtImpl) : Prog isa :=
  Impl.RsaPkcs1Enc.AArch64.Decrypt.codeP (Impl.Scrypt.AArch64.sha256 h.name h.suffix h.code) c.toCrt.privPName
    c.toCrt.privP

/-- A state meeting the precondition: decryption's, with more stack. -/
theorem satF : ∃ s, (FK 3776).pre s := Dec.decP_sat 3536 (by decide)

theorem writtenMsgFront_of {m₁ m₂ : Mem} {o l : Addr} {n : Nat} {r : BitVec 32} {v : Spec.Rsa.Outcome}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (el : Spec.Rsa.wordsAt m₂ l 1 = Spec.Rsa.wordsAt m₁ l 1)
    (h : Spec.RsaPkcs1Enc.writtenMsgFront m₁ o l n r v) : Spec.RsaPkcs1Enc.writtenMsgFront m₂ o l n r v := by
  cases v <;> simpa only [Spec.RsaPkcs1Enc.writtenMsgFront, e, el] using h

/-- The postcondition reads the memory on return only in `out` and
`msg_len`. -/
theorem frontOk (stack : Nat) :
    ScrubAllOk (Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract abi stack) stack
      (Spec.RsaPkcs1Enc.decryptPrecomputedSig.retBits abi.ptrBits) :=
  scrubAllOk_args_pre_any (sig := Spec.RsaPkcs1Enc.decryptPrecomputedSig) fun
    | [out, outLen, ml, _, nLen, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaPkcs1Enc.decryptPrecomputedSig, Spec.RsaPkcs1Enc.decryptSig, List.cons_append,
        List.nil_append, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec (Spec.RsaPkcs1Enc.decryptPrecomputedSig.retBits abi.ptrBits) → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.RsaPkcs1Enc.decryptPrecomputedSig.retBits abi.ptrBits) → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      have hol := hp.2.1
      rw [toNat_sw, toNat_sw] at hol
      exact writtenMsgFront_of (e _ (by rw [toNat_sw]; exact hol.symm)) (wordsAt_of hb.2.1) h

theorem dec_verified (h : Proof.Sha256.AArch64.Compress) (c : Proof.Rsa.AArch64.CrtImpl) :
    Verified AArch64.target (decCode h c) (DK 3488) :=
  Dec.decP_verified h (privPOf c) (decP_sat' c)

/-- `Spec.RsaPkcs1Enc.decryptPrecomputedFrontApi`'s function as emitted over
`h` and `c` meets its contract in constant time and returns without secret
residue. -/
theorem front_scrubbed (h : Proof.Sha256.AArch64.Compress) (c : Proof.Rsa.AArch64.CrtImpl) :
    VerifiedScrubbed target (Impl.RsaPkcs1Enc.AArch64.Fn.decryptPrecomputedFront (bodyName h c) (decCode h c))
      (Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract abi 3776) 32 := by
  obtain ⟨hs, hd⟩ := side_depth_of_fill2
    (c := Impl.RsaPkcs1Enc.AArch64.Front.code (bodyName h c) (decCode h c))
    (a := .call c.toCrt.privPName c.toCrt.privP) (b := .call h.name h.code) (da := 203) (db := 0) (d := 236)
    (e := Impl.RsaPkcs1Enc.AArch64.Front.code (bodyName h c) (Impl.RsaPkcs1Enc.AArch64.Decrypt.codeP
      (Impl.Scrypt.AArch64.sha256 "" h.suffix (.seq (.block []) (.block []))) "" (.block [])))
    (by kernel_rfl) (privP_side c) (privP_depth c) h.side
    (Nat.le_of_eq (Proof.Pbkdf2.Md.AArch64.fdepth_of_noFrames h.noFrames)) (by kernel_rfl)
    (Nat.le_of_ble_eq_true (by kernel_rfl))
  have hdd : 16 * (decCode h c).aarch64Depth ≤ 3488 := by
    rw [front_depth] at hd; omega_arith
  exact verifiedScrubbedOf (W := 3776) (front_verified (dec_verified h c) hdd satF) (frontOk _) (by decide)
    (Nat.le_trans (Nat.mul_le_mul_left 16 hd) (by decide)) hs (.inr (.inl rfl))

end VG.Proof.RsaPkcs1Enc.AArch64.Front
