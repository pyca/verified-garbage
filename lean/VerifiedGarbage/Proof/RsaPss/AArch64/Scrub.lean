module

public import VerifiedGarbage.Spec.RsaPss.MdTable
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
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
`vg_rsa_pss_verify_precomputed` not at all (`ScrubAll.ScrubAllOk`, as
x86-64's `Proof/RsaPss/X86_64/Scrub.lean` proves them): each implementation,
generic over the hash functions its tables hold, which it calls indirectly,
returns with every register it may leave secret cleared and its whole stack
zeroed (`ScrubAll.scrubAllOf`, with `clear`, `signSide` and `verifySide`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll VG.Proof.Ffdh.AArch64.Scrub

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

open VG.Proof.RsaPkcs1Sig.AArch64 (privPOf pdOf) in
/-- The registers the tails of signing and verification clear: those they
may write, with every implementation of RSA and of the hash functions
(`signSide`, `verifySide`). -/
def clear : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
    .v26, .v27, .v28, .v29, .v30, .v31], []⟩

open VG.Proof.RsaPkcs1Sig.AArch64 (privPOf) in
/-- What `scrubAllOf` needs of signing with each implementation of the
private-key operation and the hash functions' tables: evaluated here. -/
theorem signSide (c : Proof.Rsa.AArch64.CrtImpl) (hc : c ∈ Proof.Variants.RsaPrivateCrt.AArch64.variants) :
    scrubSide (Impl.RsaPss.AArch64.signCP (Proof.MdHashTable.AArch64.fnsOf Proof.Variants.MdHash.AArch64.variants)
        (Proof.HashTable.AArch64.fnsOf Proof.Variants.MdHash.AArch64.variants) (privPOf c).name (privPOf c).code)
      (Proof.RsaPss.AArch64.Sgn.stk (privPOf c).stack)
      (Spec.RsaPss.signPrecomputedMdTableSig.retBits abi.ptrBits) clear
      [("hash", Proof.MdHashTable.AArch64.tables Proof.Variants.MdHash.AArch64.variants),
        ("mgf1", Proof.MdHashTable.AArch64.tables Proof.Variants.MdHash.AArch64.variants)] = true := by
  have h : (Proof.Variants.RsaPrivateCrt.AArch64.variants.all fun c =>
      scrubSide (Impl.RsaPss.AArch64.signCP (Proof.MdHashTable.AArch64.fnsOf Proof.Variants.MdHash.AArch64.variants)
        (Proof.HashTable.AArch64.fnsOf Proof.Variants.MdHash.AArch64.variants) (privPOf c).name (privPOf c).code)
      (Proof.RsaPss.AArch64.Sgn.stk (privPOf c).stack)
      (Spec.RsaPss.signPrecomputedMdTableSig.retBits abi.ptrBits) clear
      [("hash", Proof.MdHashTable.AArch64.tables Proof.Variants.MdHash.AArch64.variants),
        ("mgf1", Proof.MdHashTable.AArch64.tables Proof.Variants.MdHash.AArch64.variants)]) = true := by lit_decide
  exact List.all_eq_true.mp h c hc

open VG.Proof.RsaPkcs1Sig.AArch64 (pdOf) in
/-- `signSide`, for verification with each implementation of the public-key
operation. -/
theorem verifySide (c : Proof.Rsa.AArch64.PublicImpl)
    (hc : c ∈ Proof.Variants.RsaPublicPrecomputed.AArch64.variants) :
    scrubSide (Impl.RsaPss.AArch64.verifyC (Proof.MdHashTable.AArch64.fnsOf Proof.Variants.MdHash.AArch64.variants)
        (Proof.HashTable.AArch64.fnsOf Proof.Variants.MdHash.AArch64.variants) (pdOf c).name (pdOf c).code)
      (Proof.RsaPss.AArch64.Sgn.stk 624)
      (Spec.RsaPss.verifyPrecomputedMdTableSig.retBits abi.ptrBits) clear
      [("hash", Proof.MdHashTable.AArch64.tables Proof.Variants.MdHash.AArch64.variants),
        ("mgf1", Proof.MdHashTable.AArch64.tables Proof.Variants.MdHash.AArch64.variants)] = true := by
  have h : (Proof.Variants.RsaPublicPrecomputed.AArch64.variants.all fun c =>
      scrubSide (Impl.RsaPss.AArch64.verifyC (Proof.MdHashTable.AArch64.fnsOf Proof.Variants.MdHash.AArch64.variants)
        (Proof.HashTable.AArch64.fnsOf Proof.Variants.MdHash.AArch64.variants) (pdOf c).name (pdOf c).code)
      (Proof.RsaPss.AArch64.Sgn.stk 624)
      (Spec.RsaPss.verifyPrecomputedMdTableSig.retBits abi.ptrBits) clear
      [("hash", Proof.MdHashTable.AArch64.tables Proof.Variants.MdHash.AArch64.variants),
        ("mgf1", Proof.MdHashTable.AArch64.tables Proof.Variants.MdHash.AArch64.variants)]) = true := by lit_decide
  exact List.all_eq_true.mp h c hc

end VG.Proof.RsaPss.AArch64.Scrub
