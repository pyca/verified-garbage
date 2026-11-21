module

public import VerifiedGarbage.Proof.Rsa.X86.ScrubOut
public import VerifiedGarbage.Spec.RsaOaep.MdTables
public import VerifiedGarbage.Proof.RsaOaep.X86.Inst
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Variants.Sha256.X86
public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.PVerified
public import VerifiedGarbage.Impl.RsaOaep.X86.Fn
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Sha1.X86.Lit
import VerifiedGarbage.Proof.Sha1.X86.ShaNi.Lit
import VerifiedGarbage.Proof.Sha256.X86.Lit
import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Lit
import VerifiedGarbage.Proof.Sha512.X86.Lit
import VerifiedGarbage.Proof.Md5.X86.Lit
meta import VerifiedGarbage.Proof.Rsa.X86.ScrubOut
meta import VerifiedGarbage.Proof.RsaOaep.X86.Inst
meta import VerifiedGarbage.Proof.Variants.Sha1.X86
meta import VerifiedGarbage.Proof.Variants.Sha256.X86
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Proof.RsaOaep.X86.Dec.PVerified
meta import VerifiedGarbage.Impl.RsaOaep.X86.Fn
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

`vg_rsa_oaep_decrypt_precomputed`, also generic over the implementation of
the private-key operation (`CrtImpl`), is emitted with its cleanup
(`Impl.RsaOaep.X86.Fn.decryptPrecomputed`), which returns without secret
residue whatever the implementation (`decrypt_scrubbed`). What its cleanup
needs of its code holds of it with every implementation (`decrypt_scrub`):
its code with the implementation's public precomputation and check holes of
the 96 bytes they may use (`holeStub 96`), which the kernel evaluates once
(`decrypt_side`), and `FillB` (`decrypt_fill`). Its postcondition reads the
memory on return only within `out` and `msg_len`.
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

theorem writtenDecrypt_of {m₁ m₂ : Mem} {o l : Addr} {n : Nat} {r : BitVec 32} {v : Spec.Rsa.Outcome}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (el : m₂.readW l 64 = m₁.readW l 64)
    (h : Spec.RsaOaep.writtenDecrypt m₁ o l n r v) : Spec.RsaOaep.writtenDecrypt m₂ o l n r v := by
  cases v <;> simpa only [Spec.RsaOaep.writtenDecrypt, e, el] using h

theorem decryptOut (ts : List FnTable) (stack : Nat) :
    PostOut (Spec.RsaOaep.decryptPrecomputedMdTablesContract
        (abi.withTables Spec.RsaOaep.decryptPrecomputedMdTablesSig [("hash", ts), ("mgf1", ts)]) stack)
      (Spec.RsaOaep.decryptPrecomputedMdTablesSig.retBits 32) :=
  postOut_of_local_pre (leak := some _) (ScrubAbi.plain.tables _ _) fun
    | [out, outLen, ml, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _],
        m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaOaep.decryptPrecomputedMdTablesSig, Spec.RsaOaep.decryptSig, List.cons_append,
        List.nil_append, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size] at hb
      change @Curry.apply (Mem → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e' := bytesAt_of hb.1 (hp.2.1 ▸ toNat_sw_le _ (ScrubAbi.plain.tables _ _) outLen)
      have el : m₂.readW ml 64 = m₁.readW ml 64 := Mem.readW_congr fun t ht => by
        have := hb.2.1 (ml + BitVec.ofNat 64 t) (contains_of (by simp only [Nat.reduceDiv] at ht; omega))
        exact this.symm
      exact fun H G h1 h2 => writtenDecrypt_of e' el (h H G h1 h2)

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
  verifiedScrubbedAll (api := Spec.RsaOaep.encryptMdTablesApi) {
      tables := [("hash", tables allVars), ("mgf1", tables allVars)]
      code := Proof.RsaOaep.X86.Enc.encryptCode allVars Proof.RsaPkcs1Sig.X86.Ver.baseline
      verified := enc_ok _ h
      spSafe := Proof.RsaOaep.X86.Enc.code_sp (vs := allVars) Proof.RsaPkcs1Sig.X86.Ver.baseline }
    (encryptOut _ _)

/-! ## Decryption, whatever the implementation of the private-key operation -/

open VG.Proof.Rsa.X86.PrivChecked (CrtImpl privCodeP crtPBaseline)

/-- `vg_rsa_oaep_decrypt_precomputed`, with the tables of every hash function
and the private-key operation's public precomputation and check holes of 96
bytes. -/
def decryptStub : Prog isa :=
  Impl.RsaOaep.X86.decrypt (Proof.HashTable.X86.fnsOf allVars) ""
    (Impl.Rsa.X86.PrivChecked.codeP crtPBaseline.name crtPBaseline.code "" (holeStub 96) "" (holeStub 96))
    Impl.RsaOaep.X86.privArgsP

-- The stub as a literal, for the kernel's evaluation.
materialize_code decryptStub

theorem decrypt_side :
    scrubFSide decryptStub [("hash", tables allVars), ("mgf1", tables allVars)] 3608 = true := by
  lit_decide

theorem decrypt_fill (c : CrtImpl) (hc : calleeSide c.pc 96 = true) (hd : calleeSide c.pd 96 = true) :
    FillB decryptStub (Proof.RsaOaep.X86.Dec.decCodeP allVars c crtPBaseline) := by
  unfold decryptStub
  fillB_calls

/-- `scrubFSide` of `vg_rsa_oaep_decrypt_precomputed`, whatever the
implementation of the private-key operation. -/
theorem decrypt_scrub (c : CrtImpl) :
    scrubFSide (Proof.RsaOaep.X86.Dec.decCodeP allVars c crtPBaseline)
      [("hash", tables allVars), ("mgf1", tables allVars)] 3608 = true :=
  scrubFSide_of_fillB (decrypt_fill c (calleeSide_of_le c.pcStack c.pcScrub)
    (calleeSide_of_le c.pdStack c.pdScrub)) decrypt_side

/-- `vg_rsa_oaep_decrypt_precomputed`, with its cleanup, returns without
secret residue, whatever the implementation `c` of the private-key
operation. -/
theorem decrypt_scrubbed (h : OK allVars) (c : CrtImpl) :
    VerifiedScrubbed target
      (Impl.RsaOaep.X86.Fn.decryptPrecomputed (Proof.HashTable.X86.fnsOf allVars)
        (Proof.RsaOaep.X86.Dec.privNameP c) (privCodeP c crtPBaseline))
      (Proof.RsaOaep.X86.Dec.dspecP allVars) 32 :=
  verifiedScrubbedAll (api := Spec.RsaOaep.decryptPrecomputedMdTablesApi)
    { tables := [("hash", tables allVars), ("mgf1", tables allVars)]
      code := Proof.RsaOaep.X86.Dec.decCodeP allVars c crtPBaseline
      verified := Proof.RsaOaep.X86.decP_ok _ h c crtPBaseline
      spSafe := Proof.RsaOaep.X86.Dec.code_spP c crtPBaseline }
    (decryptOut _ _) (hs := decrypt_scrub c)

/-- `vg_rsa_oaep_decrypt_precomputed`, with its cleanup, writes `esp` only by its frames. -/
theorem decrypt_spSafe (c : CrtImpl) :
    (Impl.RsaOaep.X86.Fn.decryptPrecomputed (Proof.HashTable.X86.fnsOf allVars)
      (Proof.RsaOaep.X86.Dec.privNameP c) (privCodeP c crtPBaseline)).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (Proof.RsaOaep.X86.Dec.code_spP c crtPBaseline)

end VG.Proof.RsaOaep.X86.Scrub
