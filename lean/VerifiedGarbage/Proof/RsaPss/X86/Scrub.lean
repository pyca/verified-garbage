module

public import VerifiedGarbage.Spec.RsaPss.MdTable
public import VerifiedGarbage.Proof.RsaPss.X86.Inst
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Variants.Sha256.X86
public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Rsa.X86.ScrubOut
public import VerifiedGarbage.Proof.RsaPss.X86.SgPVerified
public import VerifiedGarbage.Impl.RsaPss.X86.Fn
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Sha1.X86.Lit
import VerifiedGarbage.Proof.Sha1.X86.ShaNi.Lit
import VerifiedGarbage.Proof.Sha256.X86.Lit
import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Lit
import VerifiedGarbage.Proof.Sha512.X86.Lit
import VerifiedGarbage.Proof.Md5.X86.Lit
meta import VerifiedGarbage.Proof.RsaPss.X86.Inst
meta import VerifiedGarbage.Proof.Variants.Sha1.X86
meta import VerifiedGarbage.Proof.Variants.Sha256.X86
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Proof.Rsa.X86.ScrubOut
meta import VerifiedGarbage.Proof.RsaPss.X86.SgPVerified
meta import VerifiedGarbage.Impl.RsaPss.X86.Fn
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Sha1.X86.Lit
meta import VerifiedGarbage.Proof.Sha1.X86.ShaNi.Lit
meta import VerifiedGarbage.Proof.Sha256.X86.Lit
meta import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Lit
meta import VerifiedGarbage.Proof.Sha512.X86.Lit
meta import VerifiedGarbage.Proof.Md5.X86.Lit

/-!
# RSASSA-PSS on x86 (32-bit), without secret residue

`vg_rsa_pss_verify_precomputed`, with the tables of every hash function
(`Proof.Variants.Sha1.X86.variants`, `Proof.Variants.Sha256.X86.variants`),
which it calls indirectly, emitted with the zeroing of the stack its
contract reserves and the tail that clears the registers
(`Impl.RsaPss.X86.Fn.verifyPrecomputed`), returns without secret residue
(`verify_scrubbed`): the functions it calls indirectly are its tables'
(`X86.Scrub.tablesCall`). Its postcondition reads no memory on return
(`X86.Scrub.PostOut`).

`vg_rsa_pss_sign_precomputed`, also generic over the implementation of the
private-key operation (`CrtImpl`), is emitted with its cleanup
(`Impl.RsaPss.X86.Fn.signPrecomputed`), which returns without secret residue
whatever the implementation (`sign_scrubbed`). What its cleanup needs of its
code holds of it with every implementation (`sign_scrub`): its code with the
implementation's public precomputation and check holes of the 96 bytes they
may use (`holeStub 96`), which the kernel evaluates once (`sign_side`), and
`FillB` (`sign_fill`). Its postcondition reads the memory on return only
within `out`, given that `out` holds `n_len` bytes.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Scrub

open VG.X86 VG.X86.Scrub
open VG.Proof.RsaPss.X86 (verify_ok)
open VG.Proof.MdHashTable.X86 (mvars)
open VG.Proof.HashTable.X86 (vars)

/-! ## Postconditions -/

theorem verifyOut (tsH tsG : List FnTable) (stack : Nat) :
    PostOut (Spec.RsaPss.verifyPrecomputedMdTableContract
        (abi.withTables Spec.RsaPss.verifyPrecomputedMdTableSig [("hash", tsH), ("mgf1", tsG)]) stack)
      (Spec.RsaPss.verifyPrecomputedMdTableSig.retBits 32) :=
  postOut_of_local (leak := some _) (ScrubAbi.plain.tables _ _) fun
    | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, _, _, _, _, _, h => h

/-! ## The verification, with its cleanup -/

/-- The hash functions of the tables, as PSS's hash. -/
abbrev allMVars : List Proof.MdHashTable.X86.MVar :=
  mvars Proof.Variants.Sha1.X86.variants Proof.Variants.Sha256.X86.variants

/-- The hash functions of the tables, as MGF1's. -/
abbrev allVars : List Proof.HashTable.X86.TVar :=
  vars Proof.Variants.Sha1.X86.variants Proof.Variants.Sha256.X86.variants

/-- `vg_rsa_pss_verify_precomputed`, with the tables of every hash function,
the baseline public-key operation and its cleanup, returns without secret
residue. -/
theorem verify_scrubbed (h : Proof.RsaPss.X86.Sg.OK allMVars allVars) :
    VerifiedScrubbed target
      (Impl.RsaPss.X86.Fn.verifyPrecomputed (Proof.MdHashTable.X86.fnsOf allMVars) (Proof.HashTable.X86.fnsOf allVars)
        Proof.RsaPkcs1Sig.X86.Ver.baseline.name Proof.RsaPkcs1Sig.X86.Ver.baseline.code)
      (Proof.RsaPss.X86.Vf.vspec allMVars allVars) 32 :=
  verifiedScrubbedAll (api := Spec.RsaPss.verifyPrecomputedMdTableApi) {
      tables := [("hash", Proof.MdHashTable.X86.tables allMVars), ("mgf1", Proof.HashTable.X86.tables allVars)]
      code := Proof.RsaPss.X86.Vf.verifyCode allMVars allVars Proof.RsaPkcs1Sig.X86.Ver.baseline
      verified := verify_ok _ _ h Proof.RsaPkcs1Sig.X86.Ver.baseline
      spSafe := Proof.RsaPss.X86.Vf.code_sp h Proof.RsaPkcs1Sig.X86.Ver.baseline }
    (verifyOut _ _ _)

/-! ## Signing, whatever the implementation of the private-key operation -/

open VG.Proof.Rsa.X86.Scrub (bytesAt_of toNat_sw_le writtenOutcome_of)
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl privCodeP crtPBaseline)

theorem signOut (tsH tsG : List FnTable) (stack : Nat) :
    PostOut (Spec.RsaPss.signPrecomputedMdTableContract
        (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig [("hash", tsH), ("mgf1", tsG)]) stack)
      (Spec.RsaPss.signPrecomputedMdTableSig.retBits 32) :=
  postOut_of_local_pre (leak := some _) (ScrubAbi.plain.tables _ _) fun
    | [out, outLen, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _],
        m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaPss.signPrecomputedMdTableSig, Sig.bufs, List.mem_cons, forall_eq_or_imp,
        Elem.size] at hb
      change @Curry.apply (Mem → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e' := bytesAt_of hb.1 (hp.2.1 ▸ toNat_sw_le _ (ScrubAbi.plain.tables _ _) outLen)
      exact fun H G h1 h2 => writtenOutcome_of e' (h H G h1 h2)

/-- `vg_rsa_pss_sign_precomputed`, with the tables of every hash function and
the private-key operation's public precomputation and check holes of 96
bytes. -/
def signStub : Prog isa :=
  Impl.RsaPss.X86.sign (Proof.MdHashTable.X86.fnsOf allMVars) (Proof.HashTable.X86.fnsOf allVars) ""
    (Impl.Rsa.X86.PrivChecked.codeP crtPBaseline.name crtPBaseline.code "" (holeStub 96) "" (holeStub 96))
    Impl.RsaPss.X86.privArgsP

-- The stub as a literal, for the kernel's evaluation.
materialize_code signStub

theorem sign_side :
    scrubFSide signStub [("hash", Proof.MdHashTable.X86.tables allMVars),
      ("mgf1", Proof.HashTable.X86.tables allVars)] 3608 = true := by
  lit_decide

theorem sign_fill (c : CrtImpl) (hc : calleeSide c.pc 96 = true) (hd : calleeSide c.pd 96 = true) :
    FillB signStub (Proof.RsaPss.X86.Sg.signCodeP allMVars allVars c crtPBaseline) := by
  unfold signStub
  fillB_calls

/-- `scrubFSide` of `vg_rsa_pss_sign_precomputed`, whatever the
implementation of the private-key operation. -/
theorem sign_scrub (c : CrtImpl) :
    scrubFSide (Proof.RsaPss.X86.Sg.signCodeP allMVars allVars c crtPBaseline)
      [("hash", Proof.MdHashTable.X86.tables allMVars), ("mgf1", Proof.HashTable.X86.tables allVars)] 3608 = true :=
  scrubFSide_of_fillB (sign_fill c (calleeSide_of_le c.pcStack c.pcScrub)
    (calleeSide_of_le c.pdStack c.pdScrub)) sign_side

/-- `vg_rsa_pss_sign_precomputed`, with its cleanup, returns without secret
residue, whatever the implementation `c` of the private-key operation. -/
theorem sign_scrubbed (h : Proof.RsaPss.X86.Sg.OK allMVars allVars) (c : CrtImpl) :
    VerifiedScrubbed target
      (Impl.RsaPss.X86.Fn.signPrecomputed (Proof.MdHashTable.X86.fnsOf allMVars) (Proof.HashTable.X86.fnsOf allVars)
        (Proof.RsaPss.X86.Sg.privNameP c) (privCodeP c crtPBaseline))
      (Proof.RsaPss.X86.Sg.sspecP allMVars allVars) 32 :=
  verifiedScrubbedAll (api := Spec.RsaPss.signPrecomputedMdTableApi)
    { tables := [("hash", Proof.MdHashTable.X86.tables allMVars), ("mgf1", Proof.HashTable.X86.tables allVars)]
      code := Proof.RsaPss.X86.Sg.signCodeP allMVars allVars c crtPBaseline
      verified := Proof.RsaPss.X86.signP_ok _ _ h c crtPBaseline
      spSafe := Proof.RsaPss.X86.Sg.code_spP h c crtPBaseline }
    (signOut _ _ _) (hs := sign_scrub c)

/-- `vg_rsa_pss_sign_precomputed`, with its cleanup, writes `esp` only by its frames. -/
theorem sign_spSafe (h : Proof.RsaPss.X86.Sg.OK allMVars allVars) (c : CrtImpl) :
    (Impl.RsaPss.X86.Fn.signPrecomputed (Proof.MdHashTable.X86.fnsOf allMVars) (Proof.HashTable.X86.fnsOf allVars)
      (Proof.RsaPss.X86.Sg.privNameP c) (privCodeP c crtPBaseline)).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (Proof.RsaPss.X86.Sg.code_spP h c crtPBaseline)

end VG.Proof.RsaPss.X86.Scrub
