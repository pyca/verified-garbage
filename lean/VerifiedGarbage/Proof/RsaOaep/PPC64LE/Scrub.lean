module

public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE.Fn
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Rsa.PPC64LE.Scrub
public import VerifiedGarbage.Spec.RsaOaep.MdTables
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Inst
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Verified
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Lit

/-!
# RSAES-OAEP on PPC64LE, without secret residue

`vg_rsa_oaep_encrypt_precomputed` and `vg_rsa_oaep_decrypt_precomputed`,
each as emitted (`Impl/RsaOaep/PPC64LE/Fn.lean`), followed by its cleanup
(`Impl.Scrub.PPC64LE.scrubAll`, `PPC64LE.Scrub.verifiedScrubbedAll`), which clears
the volatile registers each may write and zeroes the stack their frames used. Each is generic over the hash functions its tables hold,
which it calls indirectly: those are the tables' functions, whose addresses
two runs agree on (`PPC64LE.Scrub.tablesCall`). Their postconditions read
the memory on return only within `out` (and decryption's `msg_len`), given
that `out` holds `n_len` bytes, as on AArch64
(`Proof/RsaOaep/AArch64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub VG.Proof.Rsa.PPC64LE.Scrub
open VG.Proof.MdHashTable.PPC64LE (mvars tables fns3)
open VG.Proof.RsaOaep.PPC64LE (OK enc_ok decP_ok)

/-! ## Postconditions -/

theorem writtenDecrypt_of {m₁ m₂ : Mem} {o l : Addr} {n : Nat} {r : BitVec 32} {v : Spec.Rsa.Outcome}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (el : m₂.readW l 64 = m₁.readW l 64)
    (h : Spec.RsaOaep.writtenDecrypt m₁ o l n r v) : Spec.RsaOaep.writtenDecrypt m₂ o l n r v := by
  cases v <;> simpa only [Spec.RsaOaep.writtenDecrypt, e, el] using h

theorem encryptOut (ts : List FnTable) (stack : Nat) :
    PostOut (Spec.RsaOaep.encryptMdTablesContract
        (abi.withTables Spec.RsaOaep.encryptMdTablesSig [("hash", ts), ("mgf1", ts)]) stack)
      (Spec.RsaOaep.encryptMdTablesSig.retBits 64) :=
  postOut_of_local_pre (leak := some _) (ScrubAbi.plain.tables _ _) fun
    | [out, outLen, _, nLen, _, _, _, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaOaep.encryptMdTablesSig, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      have hol : (outLen.setWidth 64).toNat = (nLen.setWidth 64).toNat := hp.2.1
      rw [BitVec.setWidth_eq, BitVec.setWidth_eq] at hol
      have e' : Spec.Rsa.bytesAt m₂ out (nLen.setWidth 64).toNat =
          Spec.Rsa.bytesAt m₁ out (nLen.setWidth 64).toNat :=
        e _ (by rw [BitVec.setWidth_eq]; exact hol.symm)
      exact fun H G h1 h2 h3 => written_of e' (h H G h1 h2 h3)

theorem decryptOut (ts : List FnTable) (stack : Nat) :
    PostOut (Spec.RsaOaep.decryptPrecomputedMdTablesContract
        (abi.withTables Spec.RsaOaep.decryptPrecomputedMdTablesSig [("hash", ts), ("mgf1", ts)]) stack)
      (Spec.RsaOaep.decryptPrecomputedMdTablesSig.retBits 64) :=
  postOut_of_local_pre (leak := some _) (ScrubAbi.plain.tables _ _) fun
    | [out, outLen, ml, _, nLen, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _],
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
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      have hol : (outLen.setWidth 64).toNat = (nLen.setWidth 64).toNat := hp.2.1
      rw [BitVec.setWidth_eq, BitVec.setWidth_eq] at hol
      have e' : Spec.Rsa.bytesAt m₂ out (nLen.setWidth 64).toNat =
          Spec.Rsa.bytesAt m₁ out (nLen.setWidth 64).toNat :=
        e _ (by rw [BitVec.setWidth_eq]; exact hol.symm)
      have el : m₂.readW ml 64 = m₁.readW ml 64 := Mem.readW_congr fun t ht => by
        have := hb.2.1 (ml + BitVec.ofNat 64 t) (contains_of (by simp only [Nat.reduceDiv] at ht; omega))
        exact this.symm
      exact fun H G h1 h2 => writtenDecrypt_of e' el (h H G h1 h2)

/-! ## The functions as emitted -/

/-- The hash functions whose tables the functions take are coherent: their
functions of the same name have the same code, there is one, and not too many
names. -/
theorem mvars_ok : OK mvars := of_decide_eq_true (by kernel_rfl)

/-- `vg_rsa_oaep_decrypt_precomputed` as emitted (`Impl.RsaOaep.PPC64LE.Fn.decryptP`),
with the tables of every hash function, meets its contract in constant time
and returns without secret residue. -/
theorem decryptP_scrubbed :
    VerifiedScrubbed PPC64LE.target (Impl.RsaOaep.PPC64LE.Fn.decryptP (fns3 mvars))
      (Spec.RsaOaep.decryptPrecomputedMdTablesContract
        (abi.withTables Spec.RsaOaep.decryptPrecomputedMdTablesSig [("hash", tables mvars), ("mgf1", tables mvars)])
        Proof.RsaOaep.PPC64LE.Dec.stackBytes) 32 :=
  verifiedScrubbedAll (api := Spec.RsaOaep.decryptPrecomputedMdTablesApi) {
      tables := [("hash", tables mvars), ("mgf1", tables mvars)]
      code := Impl.RsaOaep.PPC64LE.Dec.decryptP (fns3 mvars)
      verified := decP_ok mvars mvars_ok }
    3792 .all
    (decryptOut _ _)
    (by dsimp only; lit_decide)

/-- `vg_rsa_oaep_encrypt_precomputed` as emitted (`Impl.RsaOaep.PPC64LE.Fn.encrypt`),
with the tables of every hash function, meets its contract in constant time
and returns without secret residue. -/
theorem encrypt_scrubbed :
    VerifiedScrubbed PPC64LE.target (Impl.RsaOaep.PPC64LE.Fn.encrypt (fns3 mvars))
      (Spec.RsaOaep.encryptMdTablesContract
        (abi.withTables Spec.RsaOaep.encryptMdTablesSig [("hash", tables mvars), ("mgf1", tables mvars)]) 304) 32 :=
  verifiedScrubbedAll (api := Spec.RsaOaep.encryptMdTablesApi) {
      tables := [("hash", tables mvars), ("mgf1", tables mvars)]
      code := Impl.RsaOaep.PPC64LE.encrypt (fns3 mvars)
      verified := enc_ok mvars mvars_ok }
    304 .all
    (encryptOut _ _)
    (by dsimp only; lit_decide)

end VG.Proof.RsaOaep.PPC64LE.Scrub
