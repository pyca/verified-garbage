module

public import VerifiedGarbage.Spec.RsaPss.MdTable
public import VerifiedGarbage.Proof.Framework.AArch64.SideFillT
public import VerifiedGarbage.Impl.RsaPss.AArch64.Fn
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.RsaPss.AArch64.Sat
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.AArch64
public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.AArch64
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Ffdh.AArch64.Scrub

/-!
# RSASSA-PSS on AArch64, without secret residue

The postcondition of `vg_rsa_pss_sign_precomputed` reads the memory on
return only within `out`, given that `out` holds `n_len` bytes, and that of
`vg_rsa_pss_verify_precomputed` not at all (`Scrub.ScrubAllOk`, as
x86-64's `Proof/RsaPss/X86_64/Scrub.lean` proves them). Each function as
emitted (`Impl.RsaPss.AArch64.Fn`), with the tables of the hash functions,
which it calls indirectly, and any implementation of the RSA operation,
returns with every register it may write cleared and its whole stack zeroed
(`signCP_scrubbed`, `verifyC_scrubbed`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Scrub

open VG.AArch64 VG.AArch64.Scrub VG.Proof.Ffdh.AArch64.Scrub

theorem writtenOutcome_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} {r : BitVec 32} {v : Spec.Rsa.Outcome}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (h : Spec.Rsa.writtenOutcome m₁ o n r v) :
    Spec.Rsa.writtenOutcome m₂ o n r v := by
  cases v <;> simpa only [Spec.Rsa.writtenOutcome, e] using h

theorem signOk (tsH tsG : List FnTable) (stack : Nat) :
    ScrubAllOk (Spec.RsaPss.signPrecomputedMdTableContract
        (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig [("hash", tsH), ("mgf1", tsG)]) stack)
      stack (Spec.RsaPss.signPrecomputedMdTableSig.retBits abi.ptrBits) :=
  scrubAllOk_tables (scrubAllOk_args_pre_any (sig := Spec.RsaPss.signPrecomputedMdTableSig) fun
    | [out, outLen, _, nLen, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaPss.signPrecomputedMdTableSig, Sig.bufs, List.mem_cons, forall_eq_or_imp,
        Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec (Spec.RsaPss.signPrecomputedMdTableSig.retBits abi.ptrBits) → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.RsaPss.signPrecomputedMdTableSig.retBits abi.ptrBits) → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      have hol : (outLen.setWidth 64).toNat = (nLen.setWidth 64).toNat := hp.2.1
      rw [BitVec.setWidth_eq, BitVec.setWidth_eq] at hol
      have e' : Spec.Rsa.bytesAt m₂ out (nLen.setWidth 64).toNat = Spec.Rsa.bytesAt m₁ out (nLen.setWidth 64).toNat :=
        e _ (by rw [BitVec.setWidth_eq]; exact hol.symm)
      exact fun H G h1 h2 => writtenOutcome_of e' (h H G h1 h2))

theorem verifyOk (tsH tsG : List FnTable) (stack : Nat) :
    ScrubAllOk (Spec.RsaPss.verifyPrecomputedMdTableContract
        (abi.withTables Spec.RsaPss.verifyPrecomputedMdTableSig [("hash", tsH), ("mgf1", tsG)]) stack)
      stack (Spec.RsaPss.verifyPrecomputedMdTableSig.retBits abi.ptrBits) :=
  scrubAllOk_tables (scrubAllOk_args_any (sig := Spec.RsaPss.verifyPrecomputedMdTableSig) fun
    | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, _, _, _, _, _, h => h)

/-! ## The functions, as emitted

`vg_rsa_pss_sign_precomputed` and `vg_rsa_pss_verify_precomputed` with their
cleanup (`Impl.RsaPss.AArch64.Fn`), with the tables of every hash function
and any implementation of the RSA operation they call. What the cleanup
needs of the code is evaluated once, with nothing in the place of the RSA
operation, and the implementation's is its record's. -/

open VG.Proof.Variants.MdHash.AArch64 (variants hashes)
open VG.Proof.RsaPkcs1Sig.AArch64 (privP_side privP_depth)
open VG.Proof.MdHashTable.AArch64 (tables fnsOf)

/-- The hash functions the registrations give meet what the functions need
of them. -/
theorem variants_ok : Proof.RsaPss.AArch64.OK variants := of_decide_eq_true (by kernel_rfl)

theorem fnsOf_hashes : Proof.HashTable.AArch64.fnsOf variants = Impl.RsaOaep.AArch64.Fn.fnsOf hashes := by
  kernel_rfl

/-- The functions of the message's hash functions, as the proofs name them,
are those `Impl/` states of `hashes`. -/
theorem mdFns_hashes : fnsOf variants = Impl.RsaPss.AArch64.Fn.mdFns hashes := by
  kernel_rfl

/-- `vg_rsa_pss_sign_precomputed` as emitted, cleanup included. -/
theorem signCP_scrubbed (c : Proof.Rsa.AArch64.CrtImpl) :
    VerifiedScrubbed target (Impl.RsaPss.AArch64.Fn.signCP hashes c.toCrt)
      (Spec.RsaPss.signPrecomputedMdTableContract
        (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig [("hash", tables variants), ("mgf1", tables variants)])
        3584) 32 := by
  obtain ⟨hdit, ht, hd⟩ := table_depth_of_fill2
    (c := Impl.RsaPss.AArch64.signCP (Impl.RsaPss.AArch64.Fn.mdFns hashes)
      (Impl.RsaOaep.AArch64.Fn.fnsOf hashes) c.privPName c.privP)
    (ts := [("hash", tables variants), ("mgf1", tables variants)])
    (a := .call c.privPName c.privP) (b := .block []) (da := 203) (db := 0) (d := 224)
    (e := Impl.RsaPss.AArch64.signCP (Impl.RsaPss.AArch64.Fn.mdFns hashes)
      (Impl.RsaOaep.AArch64.Fn.fnsOf hashes) "" (.block []))
    (by kernel_rfl) (privP_side c) (privP_depth c) (by kernel_rfl) (Nat.le_refl _) (by kernel_rfl) (by kernel_rfl)
    (Nat.le_of_ble_eq_true (by kernel_rfl))
  have hv := Proof.RsaPss.AArch64.signP_ok variants_ok c
  rw [fnsOf_hashes, mdFns_hashes] at hv
  exact verifiedScrubbedOfT (W := 3584) hv (signOk _ _ _) (by decide)
    (Nat.le_trans (Nat.mul_le_mul_left 16 hd) (by decide)) hdit (fun _ _ h => contract_pub h) ht (.inr (.inl rfl))

/-- `vg_rsa_pss_verify_precomputed` as emitted, cleanup included. -/
theorem verifyC_scrubbed (c : Proof.Rsa.AArch64.PublicImpl) :
    VerifiedScrubbed target (Impl.RsaPss.AArch64.Fn.verifyC hashes c.name c.code)
      (Spec.RsaPss.verifyPrecomputedMdTableContract
        (abi.withTables Spec.RsaPss.verifyPrecomputedMdTableSig [("hash", tables variants), ("mgf1", tables variants)])
        960) 32 := by
  obtain ⟨hdit, ht, hd⟩ := table_depth_of_fill2
    (c := Impl.RsaPss.AArch64.verifyC (Impl.RsaPss.AArch64.Fn.mdFns hashes)
      (Impl.RsaOaep.AArch64.Fn.fnsOf hashes) c.name c.code)
    (ts := [("hash", tables variants), ("mgf1", tables variants)])
    (a := .call c.name c.code) (b := .block []) (da := 0) (db := 0) (d := 60)
    (e := Impl.RsaPss.AArch64.verifyC (Impl.RsaPss.AArch64.Fn.mdFns hashes)
      (Impl.RsaOaep.AArch64.Fn.fnsOf hashes) "" (.block []))
    (by kernel_rfl) c.side (Nat.le_of_eq c.depth) (by kernel_rfl) (Nat.le_refl _) (by kernel_rfl) (by kernel_rfl)
    (Nat.le_of_ble_eq_true (by kernel_rfl))
  have hv := Proof.RsaPss.AArch64.verify_ok variants_ok c
  rw [fnsOf_hashes, mdFns_hashes] at hv
  exact verifiedScrubbedOfT (W := 960) hv (verifyOk _ _ _) (by decide)
    (Nat.le_trans (Nat.mul_le_mul_left 16 hd) (by decide)) hdit (fun _ _ h => contract_pub h) ht (.inr (.inl rfl))

end VG.Proof.RsaPss.AArch64.Scrub
