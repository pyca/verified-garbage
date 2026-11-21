module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86_64.Fn
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecPrecomputed
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecHash
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.RndCT
public import VerifiedGarbage.Proof.Rsa.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
import VerifiedGarbage.Proof.Sha256.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# RSAES-PKCS1-v1_5 on x86-64, without secret residue

Each function as emitted (`Impl.RsaPkcs1Enc.X86_64.Fn`), over any
implementation of SHA-256's compression function (`Compress`) and of the
private CRT operation (`CrtImpl`), or of the public operation
(`PublicImpl`), its whole stack wiped by its cleanup at the higher of its own
level and theirs. Its code is its code over a stub, with the
implementations' code where it calls them (`fill_calls`): the kernel
evaluates what the cleanup needs of the stub once (for decryption, once for
each size of the compression function's scratch space, which moves offsets
in the hash functions' code), and each implementation proves what it needs
of its own code where it is defined (`Compress.side`, `CrtImpl.sideP`,
`PublicImpl.side`).
-/

-- separate module: the kernel's evaluation of the cleanup's side conditions, which a registration file may not hold

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64 VG.Impl.Pbkdf2.Md.X86_64 VG.Proof.Rsa.X86_64

/-- SHA-256's functions as decryption calls them, over a stub of the
compression function with `so` bytes of scratch space, and of `init`. -/
def stubHash (so : Nat) : Hash :=
  { P := Proof.Sha256.X86_64.Stream.paramsS so, D := 32, W := Hash.wOf (Proof.Sha256.X86_64.Stream.paramsS so),
    compN := "", compC := .block [], initN := "", initC := .block [], updN := "", finN := "",
    hmacInitN := "", hmacFinN := "", iterN := "" }

/-- Decryption's code over stubs of the hash functions (with `so` bytes of
scratch space) and of the CRT and public operations. -/
def decStub (so : Nat) : Prog isa :=
  Impl.RsaPkcs1Enc.X86_64.Decrypt.codeP (stubHash so) "priv"
    (Impl.Rsa.X86_64.PrivChecked.codeP "crt" (.block []) "pub" (.block []))

/-- The stack the implementations decryption calls need: the CRT
operation's 8 bytes, the others none. -/
def decStack : String → Nat := fun s => if s = "crt" then 8 else 0

theorem init_side : calleeSide Impl.Sha256.X86_64.Stream.init VecLevel.sse.level 0 = true := by lit_decide

/-- The level of decryption's cleanup over `h` and `c`. -/
def decLevel (h : Proof.Sha256.X86_64.Compress) (c : CrtImpl) : VecLevel :=
  h.level.join (c.level.join c.pubOp.level)

theorem dec_fill (h : Proof.Sha256.X86_64.Compress) (c : CrtImpl) {k so : Nat} (hso : h.callee.so = so)
    (hh : calleeSide h.callee.code k 0 = true) (hi : calleeSide Impl.Sha256.X86_64.Stream.init k 0 = true)
    (hc : calleeSide c.codeP k 8 = true) (hp : calleeSide c.pubOp.code k 0 = true) :
    Fill k decStack (decStub so)
      (Impl.RsaPkcs1Enc.X86_64.Decrypt.codeP (Dec.HH h) (Dec.privNameP c) (Dec.privCodeP c)) := by
  unfold decStub Dec.privCodeP Dec.HH
  have : Proof.Pbkdf2.Md.X86_64.Sha256.hash h =
      { P := Proof.Sha256.X86_64.Stream.paramsS so, D := 32, W := Hash.wOf (Proof.Sha256.X86_64.Stream.paramsS so),
        compN := h.callee.name, compC := h.callee.code, initN := "vg_sha256_init_core",
        initC := Impl.Sha256.X86_64.Stream.init, updN := "vg_sha256_update_scratch" ++ h.suffix,
        finN := "vg_sha256_finalize_scratch" ++ h.suffix, hmacInitN := "vg_hmac_sha256_init_scratch" ++ h.suffix,
        hmacFinN := "vg_hmac_sha256_finalize_scratch" ++ h.suffix,
        iterN := "vg_pbkdf2_hmac_sha256_iterate" ++ h.suffix } := by
    simp only [Proof.Pbkdf2.Md.X86_64.Sha256.hash, hso]
  rw [this]
  fill_calls

theorem dec_stub0 : stubSide (decStub 0) VecLevel.sse.level decStack 3480 [] = true := by lit_decide
theorem dec_stub112 : stubSide (decStub 112) VecLevel.sse.level decStack 3480 [] = true := by lit_decide
theorem dec_stub560 : stubSide (decStub 560) VecLevel.sse.level decStack 3480 [] = true := by lit_decide

/-- Decryption over `h` and `c`, before its cleanup. -/
def decPlain (h : Proof.Sha256.X86_64.Compress) (c : CrtImpl) :
    Unscrubbed Spec.RsaPkcs1Enc.decryptPrecomputedApi target where
  code := Impl.RsaPkcs1Enc.X86_64.Decrypt.codeP (Dec.HH h) (Dec.privNameP c) (Dec.privCodeP c)
  verified := Dec.decryptPrecomputed_verified h c
  spSafe := Dec.decP_spSafe h c

/-- `Spec.RsaPkcs1Enc.decryptPrecomputedApi`'s function as emitted over `h`
and `c` meets its contract in constant time and returns without secret
residue. -/
theorem dec_scrubbed (h : Proof.Sha256.X86_64.Compress) (c : CrtImpl) :
    VerifiedScrubbed target
      (Impl.RsaPkcs1Enc.X86_64.Fn.decryptPrecomputed (decLevel h c) (Dec.HH h) (Dec.privNameP c) (Dec.privCodeP c))
      (Spec.RsaPkcs1Enc.decryptPrecomputedApi.contract X86_64.abi 3480) 32 := by
  have hk₁ := level_join_left h.level (c.level.join c.pubOp.level)
  have hk₂ := level_join_right h.level (c.level.join c.pubOp.level)
  have hh := calleeSide_mono hk₁ (Nat.le_refl _) h.side
  have hc := calleeSide_mono (Nat.le_trans (level_join_left _ _) hk₂) (Nat.le_refl _) c.sideP
  have hp := calleeSide_mono (Nat.le_trans (level_join_right _ _) hk₂) (Nat.le_refl _) c.pubOp.side
  have hi : calleeSide Impl.Sha256.X86_64.Stream.init (decLevel h c).level 0 = true :=
    calleeSide_mono (Nat.zero_le _) (Nat.le_refl _) init_side
  rcases h.hso with e | e | e
  · exact verifiedScrubbedAllFill (decPlain h c) _ (Dec.decryptPrecomputed_postOut _)
      (dec_fill h c e hh hi hc hp) (Nat.zero_le _) (Nat.le_refl _) (ha := dec_stub0)
  · exact verifiedScrubbedAllFill (decPlain h c) _ (Dec.decryptPrecomputed_postOut _)
      (dec_fill h c e hh hi hc hp) (Nat.zero_le _) (Nat.le_refl _) (ha := dec_stub112)
  · exact verifiedScrubbedAllFill (decPlain h c) _ (Dec.decryptPrecomputed_postOut _)
      (dec_fill h c e hh hi hc hp) (Nat.zero_le _) (Nat.le_refl _) (ha := dec_stub560)

theorem dec_spSafe (h : Proof.Sha256.X86_64.Compress) (c : CrtImpl) :
    (Impl.RsaPkcs1Enc.X86_64.Fn.decryptPrecomputed (decLevel h c) (Dec.HH h) (Dec.privNameP c)
      (Dec.privCodeP c)).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Dec.decP_spSafe h c)

/-- The stack the public operation needs: none. -/
def pubStack : String → Nat := fun _ => 0

theorem rnd_stub :
    stubSide (Impl.RsaPkcs1Enc.X86_64.Random.code "enc" (Impl.RsaPkcs1Enc.X86_64.Precomputed.code "pub" (.block [])))
      VecLevel.sse.level pubStack 2288 [] = true := by lit_decide

/-- `Spec.RsaPkcs1Enc.encryptRandomApi`'s function as emitted over `v` meets
its contract in constant time and returns without secret residue. -/
theorem rnd_scrubbed (v : PublicImpl) :
    VerifiedScrubbed target (Impl.RsaPkcs1Enc.X86_64.Fn.encryptRandom v.level (Rnd.encName v) (Rnd.encCode v))
      (Spec.RsaPkcs1Enc.encryptRandomApi.contract X86_64.abi 2288) 32 :=
  verifiedScrubbedAllFill (api := Spec.RsaPkcs1Enc.encryptRandomApi)
    { code := Impl.RsaPkcs1Enc.X86_64.Random.code (Rnd.encName v) (Rnd.encCode v)
      verified := Rnd.code_verified v
      spSafe := Rnd.code_spSafe v } _ (Proof.Rsa.X86_64.Scrub.pkcs1EncryptRandomOut _)
    (by have := v.side; unfold Rnd.encCode; fill_calls)
    (Nat.zero_le _) (Nat.le_refl _) (ha := rnd_stub)

theorem rnd_spSafe (v : PublicImpl) :
    (Impl.RsaPkcs1Enc.X86_64.Fn.encryptRandom v.level (Rnd.encName v) (Rnd.encCode v)).all
      (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Rnd.code_spSafe v)

end VG.Proof.RsaPkcs1Enc.X86_64.Scrub
