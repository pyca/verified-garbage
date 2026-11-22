module

public import VerifiedGarbage.Proof.Hkdf.AArch64.Table
public import VerifiedGarbage.Proof.Hkdf.Common
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
public import VerifiedGarbage.Proof.Framework.AArch64.SideFillT
public import VerifiedGarbage.Impl.Hkdf.AArch64.Fn
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# HKDF on AArch64, without secret residue

Each function, generic over the HMAC implementations its table holds, which
it calls indirectly, followed by its cleanup (`Impl.Hkdf.AArch64.Fn`),
returns with every register it may leave secret cleared and the stack its
contract gives it zeroed (`verifiedScrubbedOfTA`): its postcondition reads
the memory on return only within the buffers it writes (`keyLocal`):
`key`'s, through the streaming states' `Repr`, which depends on their bytes
alone (`Proof.Hkdf.streamingOf_local`). What the cleanup needs of the code,
the functions it calls included, is evaluated once, for the registrations'
variants (`key_scrubbedV`).
-/

@[expose] public section

namespace VG.Proof.Hkdf.AArch64.Scrub

open VG.AArch64 VG.AArch64.Scrub
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.HmacTable.AArch64 (tables fnsOf)
open VG.Impl.Hkdf.AArch64 (kFr xFr eFr)

/-! ## `vg_hkdf_key` -/

/-- `key`'s postcondition reads the memory on return only within `key`. -/
theorem keyLocal {A : Abi isa} :
    ∀ vs m m₁ m₂ r, vs.length = (Spec.Hkdf.keySig.words A.ptrBits).length →
      (∀ b ∈ Sig.bufs Spec.Hkdf.keySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (Spec.Hkdf.keySig.words A.ptrBits) (Spec.Hkdf.keyPost A.ptrBits) vs m m₁ r →
      Curry.apply (Spec.Hkdf.keySig.words A.ptrBits) (Spec.Hkdf.keyPost A.ptrBits) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [prk, pl, key, hm], _ =>
    simp only [Spec.Hkdf.keySig, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size, Nat.mul_one] at hb
    intro H S hH hSt
    have hl : Proof.Hmac.ReprLocal S := Proof.Hkdf.streamingOf_local hSt
    have hS := Spec.Hkdf.streamingOf_stateBytes H S hSt
    obtain ⟨hi, ho⟩ := h H S hH hSt
    have keep : ∀ o, o + S.stateBytes ≤ 384 → ∀ i < S.stateBytes,
        m₂ (key + BitVec.ofNat 64 o + BitVec.ofNat 64 i) = m₁ (key + BitVec.ofNat 64 o + BitVec.ofNat 64 i) :=
      fun o ho i hi => (hb.2.1 _ (by
        rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
        exact Offset.contains_base _ (by omega_using [ho, hi]) (by omega_using [ho, hi]))).symm
    have k0 := keep 0 (by omega_using [hS])
    rw [BitVec.add_zero] at k0
    exact ⟨hl k0 hi, hl (keep 192 (by omega_using [hS])) ho⟩

theorem keyOk (vs : List MdHash) :
    ScrubAllOk (Proof.Hkdf.AArch64.specKey vs) (kFr + 32)
      (Spec.Hkdf.keySig.retBits ((abi.withTables Spec.Hkdf.keySig [("hmac", tables vs)]).ptrBits)) :=
  scrubAllOk_tables (scrubAllOk_regs (sig := Spec.Hkdf.keySig) (Nat.le_of_ble_eq_true rfl) (by decide)
    (Nat.le_refl _) keyLocal)

/-- `vg_hkdf_key` as emitted, cleanup included (`Impl.Hkdf.AArch64.Fn.key`),
with the tables of `vs`: it meets its contract in constant time and returns
without secret residue, given what the cleanup needs of the code, which
the registration's variants' evaluate. -/
theorem key_scrubbed {vs : List MdHash} (hO : Proof.Hkdf.AArch64.OK vs) (hS : Proof.Hkdf.AArch64.Streams vs)
    (hdit : (Impl.Hkdf.AArch64.key (fnsOf vs)).all (fun i => !i.writesDit) = true)
    (ht : tablesCall (Impl.Hkdf.AArch64.key (fnsOf vs)) [("hmac", tables vs)] = true)
    (hd : 16 * (Impl.Hkdf.AArch64.key (fnsOf vs)).aarch64Depth ≤ kFr + 32) :
    VerifiedScrubbed target (Impl.Hkdf.AArch64.Fn.key (fnsOf vs)) (Proof.Hkdf.AArch64.specKey vs) 0 :=
  verifiedScrubbedOfTA (Proof.Hkdf.AArch64.key_spec hO hS) (keyOk vs) (by decide) hd hdit
    (fun _ _ h => contract_pub h) ht (.inl rfl)

/-! ## `vg_hkdf_extract` -/

/-- `extract`'s postcondition reads the memory on return only within `prk`
(of `prk_len` bytes, the digest length, by the precondition). -/
theorem extractLocal :
    ∀ vs m m₁ m₂ r, vs.length = (Spec.Hkdf.extractSig.words abi.ptrBits).length →
      Curry.apply (Spec.Hkdf.extractSig.words abi.ptrBits) (Spec.Hkdf.extractPre abi.ptrBits) vs m →
      (∀ b ∈ Sig.bufs Spec.Hkdf.extractSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (Spec.Hkdf.extractSig.words abi.ptrBits) (Spec.Hkdf.extractPost abi.ptrBits) vs m m₁ r →
      Curry.apply (Spec.Hkdf.extractSig.words abi.ptrBits) (Spec.Hkdf.extractPost abi.ptrBits) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hpre hb h
  match vs, hlen with
  | [salt, sl, ikm, il, prk, pl, hm], _ =>
    simp only [Spec.Hkdf.extractSig, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size, Nat.mul_one] at hb
    intro H F hH hF
    obtain ⟨hpl, -⟩ := hpre H hH
    have := h H F hH hF
    refine (Proof.Sha256.Stream.bytesAt_congr fun i hi => (hb.2.2.1 _ ?_).symm).trans this
    have hpl' : pl.toNat = H.len := hpl
    exact Offset.contains_base _ (by omega_using [hpl', hi]) (by
      have := pl.isLt; omega_using [hpl', hi, this])

theorem extractOk (vs : List MdHash) :
    ScrubAllOk (Proof.Hkdf.AArch64.specExtract vs) (xFr + 32)
      (Spec.Hkdf.extractSig.retBits ((abi.withTables Spec.Hkdf.extractSig [("hmac", tables vs)]).ptrBits)) :=
  scrubAllOk_tables (scrubAllOk_regs_pre (sig := Spec.Hkdf.extractSig) (Nat.le_of_ble_eq_true rfl) (by decide)
    (Nat.le_refl _) extractLocal)

/-- `vg_hkdf_extract` as emitted, cleanup included
(`Impl.Hkdf.AArch64.Fn.extract`), with the tables of `vs`. -/
theorem extract_scrubbed {vs : List MdHash} (hO : Proof.Hkdf.AArch64.OK vs) (hS : Proof.Hkdf.AArch64.Streams vs)
    (hdit : (Impl.Hkdf.AArch64.extract (fnsOf vs)).all (fun i => !i.writesDit) = true)
    (ht : tablesCall (Impl.Hkdf.AArch64.extract (fnsOf vs)) [("hmac", tables vs)] = true)
    (hd : 16 * (Impl.Hkdf.AArch64.extract (fnsOf vs)).aarch64Depth ≤ xFr + 32) :
    VerifiedScrubbed target (Impl.Hkdf.AArch64.Fn.extract (fnsOf vs)) (Proof.Hkdf.AArch64.specExtract vs) 0 :=
  verifiedScrubbedOfTA (Proof.Hkdf.AArch64.extract_spec hO hS) (extractOk vs) (by decide) hd hdit
    (fun _ _ h => contract_pub h) ht (.inl rfl)

/-! ## `vg_hkdf_expand` -/

/-- `expand`'s postcondition reads the memory on return only within `out`. -/
theorem expandLocal :
    ∀ vs m m₁ m₂ r, vs.length = (Spec.Hkdf.expandSig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs Spec.Hkdf.expandSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (Spec.Hkdf.expandSig.words abi.ptrBits) (Spec.Hkdf.expandPost abi.ptrBits) vs m m₁ r →
      Curry.apply (Spec.Hkdf.expandSig.words abi.ptrBits) (Spec.Hkdf.expandPost abi.ptrBits) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [key, info, il, out, ol, hm], _ =>
    simp only [Spec.Hkdf.expandSig, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size, Nat.mul_one] at hb
    intro H S prk hH hSt hK
    rw [h H S prk hH hSt hK]
    exact congrArg some (Proof.Sha256.Stream.bytesAt_congr fun i hi => by
      have hi' : i < ol.toNat := hi
      exact hb.2.2.1 _ (Offset.contains_base _ (by omega_using [hi']) (by have := ol.isLt; omega_using [hi', this])))

theorem expandOk (vs : List MdHash) :
    ScrubAllOk (Proof.Hkdf.AArch64.specExpand vs) (eFr + 32)
      (Spec.Hkdf.expandSig.retBits ((abi.withTables Spec.Hkdf.expandSig [("hmac", tables vs)]).ptrBits)) :=
  scrubAllOk_tables (scrubAllOk_regs (sig := Spec.Hkdf.expandSig) (Nat.le_of_ble_eq_true rfl) (by decide)
    (Nat.le_refl _) expandLocal)

/-- `vg_hkdf_expand` as emitted, cleanup included
(`Impl.Hkdf.AArch64.Fn.expand`), with the tables of `vs`. -/
theorem expand_scrubbed {vs : List MdHash} (hO : Proof.Hkdf.AArch64.OK vs) (hS : Proof.Hkdf.AArch64.Streams vs)
    (hdit : (Impl.Hkdf.AArch64.expand (fnsOf vs)).all (fun i => !i.writesDit) = true)
    (ht : tablesCall (Impl.Hkdf.AArch64.expand (fnsOf vs)) [("hmac", tables vs)] = true)
    (hd : 16 * (Impl.Hkdf.AArch64.expand (fnsOf vs)).aarch64Depth ≤ eFr + 32) :
    VerifiedScrubbed target (Impl.Hkdf.AArch64.Fn.expand (fnsOf vs)) (Proof.Hkdf.AArch64.specExpand vs) 0 :=
  verifiedScrubbedOfTA (Proof.Hkdf.AArch64.expand_spec hO hS) (expandOk vs) (by decide) hd hdit
    (fun _ _ h => contract_pub h) ht (.inl rfl)

/-! ## The registrations' variants -/

open VG.Proof.Variants.MdHash.AArch64 (variants)

/-- The hash functions the registrations give meet what the functions need
of them. -/
theorem variants_ok : Proof.Hkdf.AArch64.OK variants := of_decide_eq_true (by kernel_rfl)

/-- Each variant's streaming states are the specification's. -/
theorem variants_streams : Proof.Hkdf.AArch64.Streams variants := by
  intro w hw
  simp only [variants, Proof.Variants.MdHash.AArch64.md5Variants, Proof.Variants.MdHash.AArch64.sha1Variants,
    Proof.Variants.MdHash.AArch64.sha224Variants, Proof.Variants.MdHash.AArch64.sha256Variants,
    Proof.Variants.MdHash.AArch64.sha384Variants, Proof.Variants.MdHash.AArch64.sha512Variants,
    Proof.Variants.MdHash.AArch64.sha512_224Variants, Proof.Variants.MdHash.AArch64.sha512_256Variants,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  repeat' (rcases hw with rfl | hw)
  all_goals rfl

/-- `vg_hkdf_key` as emitted, with the tables of the registrations' variants. -/
theorem key_scrubbedV :
    VerifiedScrubbed target (Impl.Hkdf.AArch64.Fn.key (fnsOf variants)) (Proof.Hkdf.AArch64.specKey variants) 0 :=
  key_scrubbed variants_ok variants_streams (by kernel_rfl) (by kernel_rfl) (Nat.le_of_ble_eq_true (by kernel_rfl))

/-- `vg_hkdf_extract` as emitted, with the tables of the registrations'
variants. -/
theorem extract_scrubbedV :
    VerifiedScrubbed target (Impl.Hkdf.AArch64.Fn.extract (fnsOf variants))
      (Proof.Hkdf.AArch64.specExtract variants) 0 :=
  extract_scrubbed variants_ok variants_streams (by kernel_rfl) (by kernel_rfl)
    (Nat.le_of_ble_eq_true (by kernel_rfl))

/-- `vg_hkdf_expand` as emitted, with the tables of the registrations'
variants. -/
theorem expand_scrubbedV :
    VerifiedScrubbed target (Impl.Hkdf.AArch64.Fn.expand (fnsOf variants))
      (Proof.Hkdf.AArch64.specExpand variants) 0 :=
  expand_scrubbed variants_ok variants_streams (by kernel_rfl) (by kernel_rfl)
    (Nat.le_of_ble_eq_true (by kernel_rfl))

end VG.Proof.Hkdf.AArch64.Scrub
