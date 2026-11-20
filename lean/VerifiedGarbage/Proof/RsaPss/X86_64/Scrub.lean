module

public import VerifiedGarbage.Impl.RsaPss.X86_64.Fn
public import VerifiedGarbage.Proof.RsaPss.X86_64.Sat
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignPrecomputed
public import VerifiedGarbage.Proof.Rsa.X86_64.Scrub
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivScrub
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# RSASSA-PSS on x86-64, without secret residue

Each function as emitted (`Impl.RsaPss.X86_64.Fn`), over the hash functions
of the interface `MdHash` (as tables) and any implementation of the private
CRT operation (`CrtImpl`), or of the public operation (`PublicImpl`), its
whole stack wiped by its cleanup, as RSAES-OAEP's
(`Proof/RsaOaep/X86_64/Scrub.lean`).
-/

-- separate module: the kernel's evaluation of the cleanup's side conditions, which a registration file may not hold

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.Rsa.X86_64.PrivScrub (callSigma callStack callSigma_up callSigma_side)
open VG.Proof.Rsa.X86_64.PubScrub (pubSigma pubStack pubSigma_up pubSigma_side)
open VG.Proof.RsaPkcs1Enc.X86_64 (privNameP privCodeP privCodeP_spSafe)
open VG.Proof.RsaPss.X86_64 (signPrecomputed_ok signCP_spAll enc_safe verify_ok chk_safe OK)

/-- The hash functions the registrations take. -/
abbrev vs : List Proof.Pbkdf2.Md.X86_64.MdHash := VG.Proof.Variants.MdHash.X86_64.variants

/-- The tables the functions take. -/
abbrev ts : List (String × List FnTable) :=
  [("hash", Proof.MdHashTable.X86_64.tables vs), ("mgf1", Proof.MdHashTable.X86_64.tables vs)]

/-- The hash functions' tables as signing and verification call them. -/
abbrev F : Impl.RsaPss.X86_64.MdFns := Proof.MdHashTable.X86_64.fnsOf vs
abbrev G : Impl.Mgf1.X86_64.Table.Fns := Proof.HashTable.X86_64.fnsOf vs

/-- Signing's code over a stub of the checked private operation. -/
def signStub : Prog isa := Impl.RsaPss.X86_64.signCP F G "priv" (.block [])

theorem sign_eq (c : CrtImpl) :
    Impl.RsaPss.X86_64.signCP F G (privNameP c) (privCodeP c) = fillCallsG (callSigma c) signStub := by
  unfold signStub; kernel_rfl

theorem sign_spSafe' (h : OK vs) (c : CrtImpl) :
    (Impl.RsaPss.X86_64.signCP F G (privNameP c) (privCodeP c)).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (signCP_spAll (fun i hi => (enc_safe h i hi).1) (fun i hi => (enc_safe h i hi).2)
    (X86_64.SpSafe.of_all (privCodeP_spSafe c)))

/-- Signing over `c`, before its cleanup. -/
def signPlain (h : OK vs) (c : CrtImpl) : Unscrubbed Spec.RsaPss.signPrecomputedMdTableApi target where
  tables := ts
  code := Impl.RsaPss.X86_64.signCP F G (privNameP c) (privCodeP c)
  verified := signPrecomputed_ok h c
  spSafe := sign_spSafe' h c

/-- `Spec.RsaPss.signPrecomputedMdTableApi`'s function as emitted over `c`
meets its contract in constant time and returns without secret residue. -/
theorem sign_scrubbed (h : OK vs) (c : CrtImpl) :
    VerifiedScrubbed target (Impl.RsaPss.X86_64.Fn.signPrecomputed (PrivScrub.level c) F G (privNameP c) (privCodeP c))
      (Proof.RsaPss.X86_64.pspec (Proof.MdHashTable.X86_64.tables vs) (Proof.MdHashTable.X86_64.tables vs)) 32 :=
  verifiedScrubbedOrUp (signPlain h c) (PrivScrub.level c) ts (Proof.RsaPss.X86_64.signPrecomputed_postOut _ _)
    (sign_eq c) (fun hl => callSigma_up c hl) (fun hl => callSigma_side c hl)

theorem sign_spSafe (h : OK vs) (c : CrtImpl) :
    (Impl.RsaPss.X86_64.Fn.signPrecomputed (PrivScrub.level c) F G (privNameP c) (privCodeP c)).all
      (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (sign_spSafe' h c)

/-- Verification's code over a stub of the public operation. -/
def verifyStub : Prog isa := Impl.RsaPss.X86_64.verifyC F G "pub" (.block [])

theorem verify_eq (c : PublicImpl) :
    Impl.RsaPss.X86_64.verifyC F G c.name c.code = fillCallsG (pubSigma c) verifyStub := by
  unfold verifyStub; kernel_rfl

theorem verify_spSafe' (h : OK vs) (c : PublicImpl) :
    (Impl.RsaPss.X86_64.verifyC F G c.name c.code).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (Proof.RsaPss.X86_64.Pc.codeC_spAll (fun i hi => (chk_safe h i hi).1)
    (fun i hi => (chk_safe h i hi).2) c)

/-- Verification over `c`, before its cleanup. -/
def verifyPlain (h : OK vs) (c : PublicImpl) : Unscrubbed Spec.RsaPss.verifyPrecomputedMdTableApi target where
  tables := ts
  code := Impl.RsaPss.X86_64.verifyC F G c.name c.code
  verified := verify_ok h c
  spSafe := verify_spSafe' h c

/-- `Spec.RsaPss.verifyPrecomputedMdTableApi`'s function as emitted over `c`
meets its contract in constant time and returns without secret residue. -/
theorem verify_scrubbed (h : OK vs) (c : PublicImpl) :
    VerifiedScrubbed target (Impl.RsaPss.X86_64.Fn.verifyPrecomputed c.level F G c.name c.code)
      (Proof.RsaPss.X86_64.verifyC (Proof.MdHashTable.X86_64.tables vs) (Proof.MdHashTable.X86_64.tables vs)) 32 :=
  verifiedScrubbedOrUp (verifyPlain h c) c.level ts (Proof.Rsa.X86_64.Scrub.pssVerifyOut _ _ _) (verify_eq c)
    (fun hl => pubSigma_up c hl) (fun hl => pubSigma_side c hl)

theorem verify_spSafe (h : OK vs) (c : PublicImpl) :
    (Impl.RsaPss.X86_64.Fn.verifyPrecomputed c.level F G c.name c.code).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (verify_spSafe' h c)

end VG.Proof.RsaPss.X86_64.Scrub
