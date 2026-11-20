module

public import VerifiedGarbage.Spec.RsaOaep.MdTables
public import VerifiedGarbage.Proof.Framework.AArch64.SideFillT
public import VerifiedGarbage.Impl.RsaOaep.AArch64.Fn
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
import VerifiedGarbage.Proof.Framework.KernelRfl
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
them). Each function as emitted (`Impl.RsaOaep.AArch64.Fn`), with the tables
of the hash functions, which it calls indirectly, and any implementation of
the RSA operation, returns with every register it may write cleared and its
whole stack zeroed (`decryptP_scrubbed`, `encrypt_scrubbed`).
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

/-! ## The functions, as emitted

`vg_rsa_oaep_decrypt_precomputed` and `vg_rsa_oaep_encrypt_precomputed` with
their cleanup (`Impl.RsaOaep.AArch64.Fn`), with the tables of every hash
function and any implementation of the RSA operation they call. What the
cleanup needs of the code is evaluated once, with nothing in the place of
the RSA operation, and the implementation's is its record's. -/

open VG.Proof.Variants.MdHash.AArch64 (variants hashes)
open VG.Proof.RsaPkcs1Sig.AArch64 (privP_side privP_depth)

/-- The hash functions the registrations give meet what the functions need
of them. -/
theorem variants_ok : OK variants := of_decide_eq_true (by kernel_rfl)

theorem fnsOf_hashes : Proof.HashTable.AArch64.fnsOf variants = Impl.RsaOaep.AArch64.Fn.fnsOf hashes := by
  kernel_rfl

/-- `vg_rsa_oaep_decrypt_precomputed` as emitted, cleanup included. -/
theorem decryptP_scrubbed (c : Proof.Rsa.AArch64.CrtImpl) :
    VerifiedScrubbed target (Impl.RsaOaep.AArch64.Fn.decryptP hashes c.toCrt)
      (Spec.RsaOaep.decryptPrecomputedMdTablesContract
        (abi.withTables Spec.RsaOaep.decryptPrecomputedMdTablesSig [("hash", tables variants), ("mgf1", tables variants)])
        3536) 32 := by
  obtain ⟨hdit, ht, hd⟩ := table_depth_of_fill2
    (c := Impl.RsaOaep.AArch64.decryptP (Impl.RsaOaep.AArch64.Fn.fnsOf hashes) c.privPName c.privP)
    (ts := [("hash", tables variants), ("mgf1", tables variants)])
    (a := .call c.privPName c.privP) (b := .block []) (da := 203) (db := 0) (d := 221)
    (e := Impl.RsaOaep.AArch64.decryptP (Impl.RsaOaep.AArch64.Fn.fnsOf hashes) "" (.block [])) (by kernel_rfl)
    (privP_side c) (privP_depth c) (by kernel_rfl) (Nat.le_refl _) (by kernel_rfl) (by kernel_rfl)
    (Nat.le_of_ble_eq_true (by kernel_rfl))
  have hv := decP_ok variants variants_ok c
  rw [fnsOf_hashes] at hv
  exact verifiedScrubbedOfT (W := 3536) hv (decryptOk _ _) (by decide)
    (Nat.le_trans (Nat.mul_le_mul_left 16 hd) (by decide)) hdit (fun _ _ h => contract_pub h) ht (.inr (.inl rfl))

/-- `vg_rsa_oaep_encrypt_precomputed` as emitted, cleanup included. -/
theorem encrypt_scrubbed (c : Proof.Rsa.AArch64.PublicImpl) :
    VerifiedScrubbed target (Impl.RsaOaep.AArch64.Fn.encrypt hashes c.name c.code)
      (Spec.RsaOaep.encryptMdTablesContract
        (abi.withTables Spec.RsaOaep.encryptMdTablesSig [("hash", tables variants), ("mgf1", tables variants)]) 304)
      32 := by
  obtain ⟨hdit, ht, hd⟩ := table_depth_of_fill2
    (c := Impl.RsaOaep.AArch64.Precomputed.encrypt (Impl.RsaOaep.AArch64.Fn.fnsOf hashes) c.name c.code)
    (ts := [("hash", tables variants), ("mgf1", tables variants)])
    (a := .call c.name c.code) (b := .block []) (da := 0) (db := 0) (d := 19)
    (e := Impl.RsaOaep.AArch64.Precomputed.encrypt (Impl.RsaOaep.AArch64.Fn.fnsOf hashes) "" (.block []))
    (by kernel_rfl) c.side (Nat.le_of_eq c.depth) (by kernel_rfl) (Nat.le_refl _) (by kernel_rfl) (by kernel_rfl)
    (Nat.le_of_ble_eq_true (by kernel_rfl))
  have hv := enc_ok variants variants_ok c
  rw [fnsOf_hashes] at hv
  exact verifiedScrubbedOfT (W := 304) hv (encryptOk _ _) (by decide)
    (Nat.le_trans (Nat.mul_le_mul_left 16 hd) (by decide)) hdit (fun _ _ h => contract_pub h) ht (.inr (.inl rfl))

end VG.Proof.RsaOaep.AArch64.Scrub
