module

public import VerifiedGarbage.Proof.Rsa.X86.ScrubOut
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.RsaOaep.X86.Fn
public import VerifiedGarbage.Spec.RsaOaep.MdTables
public import VerifiedGarbage.Proof.RsaOaep.X86.Inst
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Variants.Sha256.X86
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Sha1.X86.Lit
import VerifiedGarbage.Proof.Sha1.X86.ShaNi.Lit
import VerifiedGarbage.Proof.Sha256.X86.Lit
import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Lit
import VerifiedGarbage.Proof.Sha512.X86.Lit
import VerifiedGarbage.Proof.Md5.X86.Lit
meta import VerifiedGarbage.Proof.Rsa.X86.ScrubOut
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Impl.RsaOaep.X86.Fn
meta import VerifiedGarbage.Proof.RsaOaep.X86.Inst
meta import VerifiedGarbage.Proof.Variants.Sha1.X86
meta import VerifiedGarbage.Proof.Variants.Sha256.X86
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Sha1.X86.Lit
meta import VerifiedGarbage.Proof.Sha1.X86.ShaNi.Lit
meta import VerifiedGarbage.Proof.Sha256.X86.Lit
meta import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Lit
meta import VerifiedGarbage.Proof.Sha512.X86.Lit
meta import VerifiedGarbage.Proof.Md5.X86.Lit

/-!
# RSAES-OAEP on x86 (32-bit), without secret residue

`vg_rsa_oaep_encrypt_precomputed`, with the tables of every hash function
(`Proof.Variants.Sha1.X86.variants`, `Proof.Variants.Sha256.X86.variants`),
which it calls indirectly, emitted with the zeroing of the stack its
contract reserves and the tail that clears the registers
(`Impl.RsaOaep.X86.Fn.encryptPrecomputed`), returns without secret residue
(`encrypt_scrubbed`): the functions it calls indirectly are its tables'
(`X86.Scrub.tablesCall`). Its postcondition reads the memory on return only
within `out`, given that `out` holds `n_len` bytes (`X86.Scrub.PostOut`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.Rsa.X86.Scrub
open VG.Proof.RsaOaep.X86 (OK enc_ok)
open VG.Proof.HashTable.X86 (vars tables)

/-! ## Postconditions -/

theorem encryptOut (ts : List FnTable) (stack : Nat) :
    PostOut (Spec.RsaOaep.encryptMdTablesContract
        (abi.withTables Spec.RsaOaep.encryptMdTablesSig [("hash", ts), ("mgf1", ts)]) stack)
      (Spec.RsaOaep.encryptMdTablesSig.retBits 32) :=
  postOut_of_local_pre (leak := some _) (ScrubAbi.plain.tables _ _) fun
    | [out, outLen, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaOaep.encryptMdTablesSig, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e' := bytesAt_of hb.1 (hp.2.1 ▸ toNat_sw_le _ (ScrubAbi.plain.tables _ _) outLen)
      exact fun H G h1 h2 h3 => written_of e' (h H G h1 h2 h3)

/-! ## The function, with its cleanup -/

/-- The tables of every hash function on x86. -/
abbrev allVars : List Proof.HashTable.X86.TVar :=
  vars Proof.Variants.Sha1.X86.variants Proof.Variants.Sha256.X86.variants

/-- `vg_rsa_oaep_encrypt_precomputed`, with the tables of every hash function,
the baseline public-key operation and its cleanup, returns without secret
residue. -/
theorem encrypt_scrubbed (h : OK allVars) :
    VerifiedScrubbed target
      (Impl.RsaOaep.X86.Fn.encryptPrecomputed (Proof.HashTable.X86.fnsOf allVars)
        Proof.RsaPkcs1Sig.X86.Ver.baseline.name Proof.RsaPkcs1Sig.X86.Ver.baseline.code)
      (Proof.RsaOaep.X86.Enc.espec allVars) 32 :=
  verifiedScrubbedF (api := Spec.RsaOaep.encryptMdTablesApi) {
      tables := [("hash", tables allVars), ("mgf1", tables allVars)]
      code := Proof.RsaOaep.X86.Enc.encryptCode allVars Proof.RsaPkcs1Sig.X86.Ver.baseline
      verified := enc_ok _ h
      spSafe := Proof.RsaOaep.X86.Enc.code_sp (vs := allVars) Proof.RsaPkcs1Sig.X86.Ver.baseline }
    (encryptOut _ _)

end VG.Proof.RsaOaep.X86.Scrub
