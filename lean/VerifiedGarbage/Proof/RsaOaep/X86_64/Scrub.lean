module

public import VerifiedGarbage.Impl.RsaOaep.X86_64.Fn
public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecPrecomputed
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Verified
public import VerifiedGarbage.Proof.RsaOaep.X86_64.PcSp
public import VerifiedGarbage.Proof.Rsa.X86_64.Scrub
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivScrub
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64
public import VerifiedGarbage.Proof.MdHashTable.X86_64.Up
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# RSAES-OAEP on x86-64, without secret residue

Each function as emitted (`Impl.RsaOaep.X86_64.Fn`), over the hash
functions of the interface `MdHash` (as tables) and any implementation of the
private CRT operation (`CrtImpl`), or of the public operation (`PublicImpl`),
its whole stack wiped by its cleanup. Its code is its code over a stub, with
the implementation's code where it calls it (`fillCallsG`): the kernel
evaluates what the cleanup needs of the stub once (with stubs of the hash
functions too, `MdHashTable/X86_64/Up.lean`), and each implementation
proves what it needs of its own code where it is defined. At the level `sse`
(an implementation without vector instructions) the cleanup clears only the
SSE registers, since the hash functions the tables hold leave the upper
halves of the vector registers clear (`verifiedScrubbedOrUpFill`).
-/

-- separate module: the kernel's evaluation of the cleanup's side conditions, which a registration file may not hold

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.Rsa.X86_64.PrivScrub (callSigma callStack callSigma_up callSigma_side)
open VG.Proof.Rsa.X86_64.PubScrub (pubSigma pubStack pubSigma_up pubSigma_side)
open VG.Proof.MdHashTable.X86_64 (tables)
open VG.Proof.HashTable.X86_64 (fnsOf names stubFns fns_up mem_tableFns)
open VG.Proof.MdHashTable.X86_64 (MdUp variants_mdUp)
open VG.Proof.RsaPkcs1Enc.X86_64 (privNameP privCodeP)

/-- The hash functions the registrations take. -/
abbrev vs : List Proof.Pbkdf2.Md.X86_64.MdHash := VG.Proof.Variants.MdHash.X86_64.variants

/-- The tables the functions take. -/
abbrev ts : List (String × List FnTable) := [("hash", tables vs), ("mgf1", tables vs)]

/-- Decryption's code over stubs of the tables' functions and of the checked
private operation. -/
def decStub : Prog isa := Impl.RsaOaep.X86_64.decryptP stubFns "priv" (.block [])

theorem dec_eq (c : CrtImpl) :
    Impl.RsaOaep.X86_64.decryptP stubFns (privNameP c) (privCodeP c) = fillCallsG (callSigma c) decStub := by
  unfold decStub; kernel_rfl

theorem dec_tfill {vs : List Proof.Pbkdf2.Md.X86_64.MdHash} (hv : ∀ w ∈ vs, MdUp w) (c : CrtImpl) :
    TFill 8 (names vs) (fillCallsG (callSigma c) decStub)
      (Impl.RsaOaep.X86_64.decryptP (fnsOf vs) (privNameP c) (privCodeP c)) := by
  rw [← dec_eq]
  obtain ⟨h1, h2, h3⟩ := fns_up hv
  have hc := sigma_inames (fun hl => callSigma_up c hl) (fun hl => callSigma_side c hl) "priv" _ _ rfl
  unfold Impl.RsaOaep.X86_64.decryptP
  tfill_calls

/-- Decryption over `c`, before its cleanup. -/
def decPlain (h : OK vs) (c : CrtImpl) : Unscrubbed Spec.RsaOaep.decryptPrecomputedMdTablesApi target where
  tables := ts
  code := Impl.RsaOaep.X86_64.decryptP (fnsOf vs) (privNameP c) (privCodeP c)
  verified := decPrecomputed_ok vs h c
  spSafe := decP_spSafe vs c

/-- `Spec.RsaOaep.decryptPrecomputedMdTablesApi`'s function as emitted over
`c` meets its contract in constant time and returns without secret residue. -/
theorem dec_scrubbed (h : OK vs) (c : CrtImpl) :
    VerifiedScrubbed target
      (Impl.RsaOaep.X86_64.Fn.decryptPrecomputed (PrivScrub.level c) (fnsOf vs) (privNameP c) (privCodeP c))
      (pdspec (tables vs)) 32 :=
  verifiedScrubbedOrUpFill (decPlain h c) (PrivScrub.level c) (decPrecomputed_postOut _) (dec_tfill variants_mdUp c)
    (fun _ h => mem_tableFns h) (fun hl => callSigma_up c hl) (fun hl => callSigma_side c hl)

theorem dec_spSafe (c : CrtImpl) :
    (Impl.RsaOaep.X86_64.Fn.decryptPrecomputed (PrivScrub.level c) (fnsOf vs) (privNameP c)
      (privCodeP c)).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (decP_spSafe vs c)

/-- Encryption's code over stubs of the tables' functions and of the public
operation. -/
def encStub : Prog isa := Impl.RsaOaep.X86_64.Precomputed.encrypt stubFns "pub" (.block [])

theorem enc_eq (c : PublicImpl) :
    Impl.RsaOaep.X86_64.Precomputed.encrypt stubFns c.name c.code = fillCallsG (pubSigma c) encStub := by
  unfold encStub; kernel_rfl

theorem enc_tfill {vs : List Proof.Pbkdf2.Md.X86_64.MdHash} (hv : ∀ w ∈ vs, MdUp w) (c : PublicImpl) :
    TFill 8 (names vs) (fillCallsG (pubSigma c) encStub)
      (Impl.RsaOaep.X86_64.Precomputed.encrypt (fnsOf vs) c.name c.code) := by
  rw [← enc_eq]
  obtain ⟨h1, h2, h3⟩ := fns_up hv
  have hc := sigma_inames (fun hl => pubSigma_up c hl) (fun hl => pubSigma_side c hl) "pub" _ _ rfl
  unfold Impl.RsaOaep.X86_64.Precomputed.encrypt
  tfill_calls

/-- Encryption over `c`, before its cleanup. -/
def encPlain (h : OK vs) (c : PublicImpl) : Unscrubbed Spec.RsaOaep.encryptMdTablesApi target where
  tables := ts
  code := Impl.RsaOaep.X86_64.Precomputed.encrypt (fnsOf vs) c.name c.code
  verified := enc_ok vs h c
  spSafe := Pc.code_spSafe vs c

/-- `Spec.RsaOaep.encryptMdTablesApi`'s function as emitted over `c` meets
its contract in constant time and returns without secret residue. -/
theorem enc_scrubbed (h : OK vs) (c : PublicImpl) :
    VerifiedScrubbed target (Impl.RsaOaep.X86_64.Fn.encrypt c.level (fnsOf vs) c.name c.code)
      (Pc.encC (tables vs)) 32 :=
  verifiedScrubbedOrUpFill (encPlain h c) c.level (Proof.Rsa.X86_64.Scrub.oaepEncryptOut _ _) (enc_tfill variants_mdUp c)
    (fun _ h => mem_tableFns h) (fun hl => pubSigma_up c hl) (fun hl => pubSigma_side c hl)

theorem enc_spSafe (c : PublicImpl) :
    (Impl.RsaOaep.X86_64.Fn.encrypt c.level (fnsOf vs) c.name c.code).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Pc.code_spSafe vs c)

end VG.Proof.RsaOaep.X86_64.Scrub
