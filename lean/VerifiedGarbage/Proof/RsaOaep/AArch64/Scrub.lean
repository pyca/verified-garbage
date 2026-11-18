module

public import VerifiedGarbage.Spec.RsaOaep.MdTables
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
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

end VG.Proof.RsaOaep.AArch64.Scrub
