module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RandomPublic
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

Each function as emitted (`Impl.RsaPkcs1Enc.X86_64.Fn`, and
`vg_rsa_pkcs1_decrypt_precomputed` in `FrontScrub.lean`, which calls
decryption's code here), over any implementation of SHA-256's compression
function (`Compress`) and of the private CRT operation (`CrtImpl`), or of
the public operation (`PublicImpl`), its whole stack wiped by its cleanup at
the higher of its own level and theirs. Its code is its code over a stub, with the
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
        iterN := "vg_pbkdf2_hmac_sha256_iterate" ++ h.suffix,
        hmacInitAnyN := "vg_hmac_sha256_init_any_scratch" ++ h.suffix } := by
    simp only [Proof.Pbkdf2.Md.X86_64.Sha256.hash, hso]
  rw [this]
  fill_calls

theorem dec_stub0 : stubSide (decStub 0) VecLevel.sse.level decStack 3480 [] = true := by lit_decide
theorem dec_stub112 : stubSide (decStub 112) VecLevel.sse.level decStack 3480 [] = true := by lit_decide
theorem dec_stub560 : stubSide (decStub 560) VecLevel.sse.level decStack 3480 [] = true := by lit_decide

/-- The stack the public operation needs: none. -/
def pubStack : String → Nat := fun _ => 0

theorem rnd_stub :
    stubSide (Impl.RsaPkcs1Enc.X86_64.Random.code "enc" (Impl.RsaPkcs1Enc.X86_64.Precomputed.code "pub" (.block [])))
      VecLevel.sse.level pubStack 2288 [] = true := by lit_decide

/-- `vg_rsa_pkcs1_encrypt_random` as emitted over `v` meets
`encryptRandomAskedContract` in constant time and returns without secret residue. -/
theorem rnd_asked (v : PublicImpl) :
    VerifiedScrubbed target (Impl.RsaPkcs1Enc.X86_64.Fn.encryptRandom v.level (Rnd.encName v) (Rnd.encCode v))
      (Proof.RsaPkcs1Enc.encryptRandomAskedContract X86_64.abi 2288) 32 :=
  verifiedScrubbedAllFill (api := Proof.RsaPkcs1Enc.encryptRandomAskedApi)
    { code := Impl.RsaPkcs1Enc.X86_64.Random.code (Rnd.encName v) (Rnd.encCode v)
      verified := Rnd.code_verified v
      spSafe := Rnd.code_spSafe v } _ (Proof.Rsa.X86_64.Scrub.pkcs1EncryptRandomOut _)
    (by have := v.side; unfold Rnd.encCode; fill_calls)
    (Nat.zero_le _) (Nat.le_refl _) (ha := rnd_stub)

theorem rnd_scrubbed (v : PublicImpl) :
    VerifiedScrubbed target
      (Impl.RsaPkcs1Enc.X86_64.Fn.encryptRandom v.level (Rnd.encName v) (Rnd.encCode v))
      (Spec.RsaPkcs1Enc.encryptRandomContract X86_64.abi 2288) 32 :=
  encryptRandom_imp (rnd_asked v) id

theorem rnd_public (v : PublicImpl) :
    Spec.RsaPkcs1Enc.encryptRandomOut.Of X86_64.abi
      (Impl.RsaPkcs1Enc.X86_64.Fn.encryptRandom v.level (Rnd.encName v) (Rnd.encCode v))
      (Spec.RsaPkcs1Enc.encryptRandomContract X86_64.abi 2288) :=
  Proof.RsaPkcs1Enc.encryptRandom_public (rnd_asked v)

theorem rnd_spSafe (v : PublicImpl) :
    (Impl.RsaPkcs1Enc.X86_64.Fn.encryptRandom v.level (Rnd.encName v) (Rnd.encCode v)).all
      (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Rnd.code_spSafe v)

end VG.Proof.RsaPkcs1Enc.X86_64.Scrub
