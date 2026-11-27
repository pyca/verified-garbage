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
public import VerifiedGarbage.Proof.MdHashTable.AArch64.Up
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Ffdh.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.ForallLength
import VerifiedGarbage.Proof.HashTable.First

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
  scrubAllOk_tables (scrubAllOk_args_pre_any (sig := Spec.RsaPss.signPrecomputedMdTableSig) fun vs m m₁ m₂ r hl => by
      revert vs; refine forall_length (n := 26) ?_
      intro out outLen _ nLen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp hb h
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
      obtain ⟨H, G, hH, hG, outcome⟩ := h
      exact ⟨H, G, hH, hG, writtenOutcome_of e' outcome⟩)

theorem verifyOk (tsH tsG : List FnTable) (stack : Nat) :
    ScrubAllOk (Spec.RsaPss.verifyPrecomputedMdTableContract
        (abi.withTables Spec.RsaPss.verifyPrecomputedMdTableSig [("hash", tsH), ("mgf1", tsG)]) stack)
      stack (Spec.RsaPss.verifyPrecomputedMdTableSig.retBits abi.ptrBits) :=
  scrubAllOk_tables (scrubAllOk_args_any (sig := Spec.RsaPss.verifyPrecomputedMdTableSig) fun vs _ _ _ _ hl => by
      revert vs; refine forall_length (n := 16) ?_
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; exact h)

/-! ## The functions, as emitted

`vg_rsa_pss_sign_precomputed` and `vg_rsa_pss_verify_precomputed` with their
cleanup (`Impl.RsaPss.AArch64.Fn`), with the tables of every hash function
and any implementation of the RSA operation they call. What the cleanup
needs of the code is evaluated once, with nothing in the place of the RSA
operation, and the implementation's is its record's. -/

open VG.Proof.Variants.MdHash.AArch64 (variants hashes)
open VG.Proof.RsaPkcs1Sig.AArch64 (privP_side privP_depth)
open VG.Proof.MdHashTable.AArch64 (tables fnsOf)

/-- The registrations' hash functions of the same name have the same code. -/
theorem variants_mdCoh : MdHashTable.AArch64.Coh variants := fun w hw w' hw' =>
  ⟨Proof.HashTable.coh_of_first variants (·.H.initN) (·.H.initC) (by kernel_rfl) w hw w' hw',
    Proof.HashTable.coh_of_first variants (·.H.compN) (·.H.compC) (by kernel_rfl) w hw w' hw',
    Proof.HashTable.coh_of_first variants MdHashTable.AArch64.digName
      (Impl.MdHashTable.AArch64.digest ·.H.P) (by kernel_rfl) w hw w' hw'⟩

/-- The registrations' hash functions of the same name have the same code. -/
theorem variants_coh : HashTable.AArch64.Coh variants := fun w hw w' hw' =>
  ⟨Proof.HashTable.coh_of_first variants (·.H.initN) (·.H.initC) (by kernel_rfl) w hw w' hw',
    Proof.HashTable.coh_of_first variants (·.H.updN) (·.H.updC) (by kernel_rfl) w hw w' hw',
    Proof.HashTable.coh_of_first variants (·.H.finN) (·.H.finC) (by kernel_rfl) w hw w' hw'⟩

/-- The hash functions the registrations give meet what the functions need
of them. -/
theorem variants_ok : Proof.RsaPss.AArch64.OK variants := by
  refine ⟨variants_mdCoh, variants_coh, ?_⟩
  unfold DepthOK
  exact of_decide_eq_true (by kernel_rfl)

theorem fnsOf_hashes : Proof.HashTable.AArch64.fnsOf variants = Impl.RsaOaep.AArch64.Fn.fnsOf hashes := by
  kernel_rfl

/-- The functions of the message's hash functions, as the proofs name them,
are those `Impl/` states of `hashes`. -/
theorem mdFns_hashes : fnsOf variants = Impl.RsaPss.AArch64.Fn.mdFns hashes := by
  kernel_rfl

open Proof.MdHashTable.AArch64 (names MdUp variants_mdUp mdFns_up)
open Proof.HashTable.AArch64 (stubFns fns_up mem_tableFns)
open Proof.Pbkdf2.Md.AArch64 (MdHash)

/-- A stub in the place of each of the functions PSS calls through a table. -/
def mdStubFns : Impl.RsaPss.AArch64.MdFns := ⟨[("t", tableStub 1)], [("t", tableStub 1)], [("t", tableStub 1)]⟩

/-- Signing's code is its code over stubs, with the tables' functions and the
RSA operation's code in their places. -/
theorem sign_tfill {vs : List MdHash} (hv : ∀ w ∈ vs, MdUp w) (c : Proof.Rsa.AArch64.CrtImpl) :
    TFill 1 (names vs) (Code.fill2 (.call c.privPName c.privP) (.block [])
        (Impl.RsaPss.AArch64.signCP mdStubFns stubFns "" (.block [])))
      (Impl.RsaPss.AArch64.signCP (fnsOf vs) (Proof.HashTable.AArch64.fnsOf vs) c.privPName c.privP) := by
  rw [show Code.fill2 (.call c.privPName c.privP) (.block [])
      (Impl.RsaPss.AArch64.signCP mdStubFns stubFns "" (.block [])) =
    Impl.RsaPss.AArch64.signCP mdStubFns stubFns c.privPName c.privP from by kernel_rfl]
  obtain ⟨hf1, hf2, hf3⟩ := mdFns_up hv
  obtain ⟨hg1, hg2, hg3⟩ := fns_up hv
  have hc : inames c.privP = [] := inames_of_noIcall (noIcall_of_sideAll (privP_side c))
  unfold Impl.RsaPss.AArch64.signCP
  tfill_calls

theorem verify_tfill {vs : List MdHash} (hv : ∀ w ∈ vs, MdUp w) (c : Proof.Rsa.AArch64.PublicImpl) :
    TFill 1 (names vs) (Code.fill2 (.call c.name c.code) (.block [])
        (Impl.RsaPss.AArch64.verifyC mdStubFns stubFns "" (.block [])))
      (Impl.RsaPss.AArch64.verifyC (fnsOf vs) (Proof.HashTable.AArch64.fnsOf vs) c.name c.code) := by
  rw [show Code.fill2 (.call c.name c.code) (.block [])
      (Impl.RsaPss.AArch64.verifyC mdStubFns stubFns "" (.block [])) =
    Impl.RsaPss.AArch64.verifyC mdStubFns stubFns c.name c.code from by kernel_rfl]
  obtain ⟨hf1, hf2, hf3⟩ := mdFns_up hv
  obtain ⟨hg1, hg2, hg3⟩ := fns_up hv
  have hc : inames c.code = [] := inames_of_noIcall (noIcall_of_sideAll c.side)
  unfold Impl.RsaPss.AArch64.verifyC
  tfill_calls

/-- `vg_rsa_pss_sign_precomputed` as emitted, cleanup included. -/
theorem signCP_scrubbed (c : Proof.Rsa.AArch64.CrtImpl) :
    VerifiedScrubbed target (Impl.RsaPss.AArch64.Fn.signCP hashes c.toCrt)
      (Spec.RsaPss.signPrecomputedMdTableContract
        (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig [("hash", tables variants), ("mgf1", tables variants)])
        3584) 32 := by
  have hf := sign_tfill variants_mdUp c
  rw [fnsOf_hashes, mdFns_hashes] at hf
  obtain ⟨hdit, ht, hd⟩ := table_depth_of_tfill (d := 224) hf (fun _ h => mem_tableFns h) (privP_side c) (privP_depth c)
    (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
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
  have hf := verify_tfill variants_mdUp c
  rw [fnsOf_hashes, mdFns_hashes] at hf
  obtain ⟨hdit, ht, hd⟩ := table_depth_of_tfill (a := .call c.name c.code) (da := 0) (d := 60) hf
    (fun _ h => mem_tableFns h) c.side (Nat.le_of_eq c.depth) (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))
  have hv := Proof.RsaPss.AArch64.verify_ok variants_ok c
  rw [fnsOf_hashes, mdFns_hashes] at hv
  exact verifiedScrubbedOfT (W := 960) hv (verifyOk _ _ _) (by decide)
    (Nat.le_trans (Nat.mul_le_mul_left 16 hd) (by decide)) hdit (fun _ _ h => contract_pub h) ht (.inr (.inl rfl))

end VG.Proof.RsaPss.AArch64.Scrub
