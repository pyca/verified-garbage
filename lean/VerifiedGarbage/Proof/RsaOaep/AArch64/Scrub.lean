module

public import VerifiedGarbage.Spec.RsaOaep.MdTables
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Inst
public import VerifiedGarbage.Proof.HashTable.AArch64
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.AArch64
public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.AArch64
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MdHashTable.AArch64.Tables
import VerifiedGarbage.Proof.Ffdh.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.Mem

/-!
# RSAES-OAEP on AArch64, without secret residue

The postconditions of `vg_rsa_oaep_encrypt_precomputed` and
`vg_rsa_oaep_decrypt_precomputed` read the memory on return only within
`out` (and decryption's `msg_len`), given that `out` holds `n_len` bytes
(`ScrubAll.ScrubAllOk`, as x86-64's `Proof/RsaOaep/X86_64/Scrub.lean` proves
them): each implementation, generic over the hash functions its tables hold,
which it calls indirectly, returns with every register it may leave secret
cleared and its whole stack zeroed (`ScrubAll.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll VG.Proof.Ffdh.AArch64.Scrub
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.MdHashTable.AArch64 (tables)

theorem writtenDecrypt_of {m₁ m₂ : Mem} {o l : Addr} {n : Nat} {r : BitVec 32} {v : Spec.Rsa.Outcome}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (el : m₂.readW l 64 = m₁.readW l 64)
    (h : Spec.RsaOaep.writtenDecrypt m₁ o l n r v) : Spec.RsaOaep.writtenDecrypt m₂ o l n r v := by
  cases v <;> simpa only [Spec.RsaOaep.writtenDecrypt, e, el] using h

theorem encryptOk (vs : List MdHash) (stack : Nat) :
    ScrubAllOk (Spec.RsaOaep.encryptMdTablesContract
        (abi.withTables Spec.RsaOaep.encryptMdTablesSig [("hash", tables vs), ("mgf1", tables vs)]) stack)
      stack (Spec.RsaOaep.encryptMdTablesSig.retBits abi.ptrBits) :=
  scrubAllOk_tables (scrubAllOk_args_pre_any (sig := Spec.RsaOaep.encryptMdTablesSig) fun
    | [out, outLen, _, nLen, _, _, _, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaOaep.encryptMdTablesSig, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec (Spec.RsaOaep.encryptMdTablesSig.retBits abi.ptrBits) → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.RsaOaep.encryptMdTablesSig.retBits abi.ptrBits) → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      have hol : (outLen.setWidth 64).toNat = (nLen.setWidth 64).toNat := hp.2.1
      rw [BitVec.setWidth_eq, BitVec.setWidth_eq] at hol
      have e' : Spec.Rsa.bytesAt m₂ out (nLen.setWidth 64).toNat = Spec.Rsa.bytesAt m₁ out (nLen.setWidth 64).toNat :=
        e _ (by rw [BitVec.setWidth_eq]; exact hol.symm)
      exact fun H G h1 h2 h3 => written_of e' (h H G h1 h2 h3))

theorem decryptOk (vs : List MdHash) (stack : Nat) :
    ScrubAllOk (Spec.RsaOaep.decryptPrecomputedMdTablesContract
        (abi.withTables Spec.RsaOaep.decryptPrecomputedMdTablesSig [("hash", tables vs), ("mgf1", tables vs)]) stack)
      stack (Spec.RsaOaep.decryptPrecomputedMdTablesSig.retBits abi.ptrBits) :=
  scrubAllOk_tables (scrubAllOk_args_pre_any (sig := Spec.RsaOaep.decryptPrecomputedMdTablesSig) fun
    | [out, outLen, ml, _, nLen, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaOaep.decryptPrecomputedMdTablesSig, Spec.RsaOaep.decryptSig, List.cons_append,
        List.nil_append, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec (Spec.RsaOaep.decryptPrecomputedMdTablesSig.retBits abi.ptrBits) → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.RsaOaep.decryptPrecomputedMdTablesSig.retBits abi.ptrBits) → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      have hol : (outLen.setWidth 64).toNat = (nLen.setWidth 64).toNat := hp.2.1
      rw [BitVec.setWidth_eq, BitVec.setWidth_eq] at hol
      have e' : Spec.Rsa.bytesAt m₂ out (nLen.setWidth 64).toNat = Spec.Rsa.bytesAt m₁ out (nLen.setWidth 64).toNat :=
        e _ (by rw [BitVec.setWidth_eq]; exact hol.symm)
      have el : m₂.readW ml 64 = m₁.readW ml 64 := Mem.readW_congr fun t ht => by
        have := hb.2.1 (ml + BitVec.ofNat 64 t) (contains_of (by simp only [Nat.reduceDiv] at ht; omega))
        exact this.symm
      exact fun H G h1 h2 => writtenDecrypt_of e' el (h H G h1 h2))

open VG.Proof.RsaPkcs1Sig.AArch64 (privPOf pdOf) in
open VG.Proof.HashTable.AArch64 (fnsOf) in
/-- The registers the tails of encryption and decryption clear: those they
may write, with every implementation of RSA and of the hash functions
(`decryptSide`, `encryptSide`). -/
def clear : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
    .v26, .v27, .v28, .v29, .v30, .v31], []⟩

open VG.Proof.RsaPkcs1Sig.AArch64 (privPOf) in
open VG.Proof.HashTable.AArch64 (fnsOf) in
/-- What `scrubAllOf` needs of decryption with each implementation of the
private-key operation and the hash functions' tables: evaluated here. -/
theorem decryptSide (c : Proof.Rsa.AArch64.CrtImpl) (hc : c ∈ Proof.Variants.RsaPrivateCrt.AArch64.variants) :
    scrubSide (Impl.RsaOaep.AArch64.decryptP (fnsOf Proof.Variants.MdHash.AArch64.variants) (privPOf c).name
        (privPOf c).code) ((privPOf c).stack + 288) (Spec.RsaOaep.decryptPrecomputedMdTablesSig.retBits abi.ptrBits)
      clear [("hash", tables Proof.Variants.MdHash.AArch64.variants),
        ("mgf1", tables Proof.Variants.MdHash.AArch64.variants)] = true := by
  have h : (Proof.Variants.RsaPrivateCrt.AArch64.variants.all fun c =>
      scrubSide (Impl.RsaOaep.AArch64.decryptP (fnsOf Proof.Variants.MdHash.AArch64.variants) (privPOf c).name
        (privPOf c).code) ((privPOf c).stack + 288) (Spec.RsaOaep.decryptPrecomputedMdTablesSig.retBits abi.ptrBits)
      clear [("hash", tables Proof.Variants.MdHash.AArch64.variants),
        ("mgf1", tables Proof.Variants.MdHash.AArch64.variants)]) = true := by lit_decide
  exact List.all_eq_true.mp h c hc

open VG.Proof.RsaPkcs1Sig.AArch64 (pdOf) in
open VG.Proof.HashTable.AArch64 (fnsOf) in
/-- `decryptSide`, for encryption with each implementation of the public-key
operation. -/
theorem encryptSide (c : Proof.Rsa.AArch64.PublicImpl)
    (hc : c ∈ Proof.Variants.RsaPublicPrecomputed.AArch64.variants) :
    scrubSide (Impl.RsaOaep.AArch64.Precomputed.encrypt (fnsOf Proof.Variants.MdHash.AArch64.variants) (pdOf c).name
        (pdOf c).code) (Proof.RsaOaep.AArch64.Enc.encStack (pdOf c))
      (Spec.RsaOaep.encryptMdTablesSig.retBits abi.ptrBits)
      clear [("hash", tables Proof.Variants.MdHash.AArch64.variants),
        ("mgf1", tables Proof.Variants.MdHash.AArch64.variants)] = true := by
  have h : (Proof.Variants.RsaPublicPrecomputed.AArch64.variants.all fun c =>
      scrubSide (Impl.RsaOaep.AArch64.Precomputed.encrypt (fnsOf Proof.Variants.MdHash.AArch64.variants) (pdOf c).name
        (pdOf c).code) (Proof.RsaOaep.AArch64.Enc.encStack (pdOf c))
      (Spec.RsaOaep.encryptMdTablesSig.retBits abi.ptrBits)
      clear [("hash", tables Proof.Variants.MdHash.AArch64.variants),
        ("mgf1", tables Proof.Variants.MdHash.AArch64.variants)]) = true := by lit_decide
  exact List.all_eq_true.mp h c hc

end VG.Proof.RsaOaep.AArch64.Scrub
