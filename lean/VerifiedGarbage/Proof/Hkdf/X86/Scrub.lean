module

public import VerifiedGarbage.Proof.Hkdf.X86.Key
public import VerifiedGarbage.Proof.Hkdf.X86.Extract
public import VerifiedGarbage.Proof.Hkdf.X86.Expand
public import VerifiedGarbage.Proof.Hkdf.X86.Table
public import VerifiedGarbage.Proof.Hkdf.Common
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Hkdf.X86.Fn
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Variants.Sha256.X86
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Lit
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Lit
import VerifiedGarbage.Proof.Md5.X86.Lit
import VerifiedGarbage.Proof.Sha1.X86.Lit
import VerifiedGarbage.Proof.Sha1.X86.ShaNi.Lit
import VerifiedGarbage.Proof.Sha256.X86.Lit
import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Lit
import VerifiedGarbage.Proof.Sha512.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# HKDF on x86 (32-bit), without secret residue

Each function, generic over the HMAC implementations its table holds, which
it calls indirectly, followed by its cleanup (`Impl.Hkdf.X86.Fn`): the
zeroing of the stack its frames and calls use and `Impl.Scrub.X86.tail`, as
emitted (`X86.Scrub.verifiedScrubbedAll`), as for ECDSA's signing on x86
(`Proof/Ecdsa/X86/P256/Scrub.lean`). The postconditions read the memory on
return only within the buffers they write (`keyOut`): `key`'s, through the
streaming states' `Repr`, which depends on their bytes alone
(`Proof.Hkdf.streamingOf_local`). What the cleanup needs of each function's
code, with the HMAC implementations of SHA-1's and SHA-256's variants
(`Proof/Variants/Sha1/X86.lean`, `Proof/Variants/Sha256/X86.lean`) in its
table, is evaluated once, with their literals (`keySide`).
-/

@[expose] public section

namespace VG.Proof.Hkdf.X86.Scrub

open VG.X86 VG.X86.Scrub
open VG.Proof.HmacTable.X86 (HVar tables fnsOf vars)

/-! ## The postconditions read only the buffers they write -/

/-- A length, which the contract reads as its low 32 bits, spans at most the
bytes of the buffer `Sig.bufs` gives it. -/
theorem len_le (x : BitVec 64) (A : Abi isa) (hA : A.ptrBits = 32) : ((ArgWord.int A.ptrBits).ofRaw x).toNat ≤ x.toNat := by
  rw [hA]
  show (x.setWidth 32).toNat ≤ x.toNat
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_le _ _

/-- `key`'s postcondition reads the memory on return only within `key`. -/
theorem keyOut (vs : List HVar) : PostOut (specKey vs) (Spec.Hkdf.keySig.retBits 32) :=
  postOut_of_local (ScrubAbi.plain.tables _ _) fun vs m m₁ m₂ r hlen hb h => by
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

/-- `extract`'s postcondition reads the memory on return only within `prk`
(of `prk_len` bytes, the digest length, by the precondition). -/
theorem extractOut (vs : List HVar) : PostOut (specExtract vs) (Spec.Hkdf.extractSig.retBits 32) :=
  postOut_of_local_pre (ScrubAbi.plain.tables _ _) fun ws m m₁ m₂ r hlen hpre hb h => by
    match ws, hlen with
    | [salt, sl, ikm, il, prk, pl, hm], _ =>
      simp only [Spec.Hkdf.extractSig, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size, Nat.mul_one] at hb
      intro H F hH hF
      obtain ⟨hpl, -⟩ := hpre H hH
      have := h H F hH hF
      refine (Proof.Sha256.Stream.bytesAt_congr fun i hi => (hb.2.2.1 _ ?_).symm).trans this
      have hle := len_le pl (abi.withTables Spec.Hkdf.extractSig [("hmac", tables vs)]) rfl
      exact Offset.contains_base _ (by omega_using [hpl, hi, hle]) (by
        have := pl.isLt; omega_using [hpl, hi, this, hle])

/-- `expand`'s postcondition reads the memory on return only within `out`. -/
theorem expandOut (vs : List HVar) : PostOut (specExpand vs) (Spec.Hkdf.expandSig.retBits 32) :=
  postOut_of_local (ScrubAbi.plain.tables _ _) fun ws m m₁ m₂ r hlen hb h => by
    match ws, hlen with
    | [key, info, il, out, ol, hm], _ =>
      simp only [Spec.Hkdf.expandSig, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size, Nat.mul_one] at hb
      intro H S prk hH hSt hK
      rw [h H S prk hH hSt hK]
      exact congrArg some (Proof.Sha256.Stream.bytesAt_congr fun i hi => by
        have hle := len_le ol (abi.withTables Spec.Hkdf.expandSig [("hmac", tables vs)]) rfl
        exact hb.2.2.1 _ (Offset.contains_base _ (by omega_using [hi, hle]) (by
          have := ol.isLt; omega_using [hi, this, hle])))

/-! ## The functions as emitted -/

section
variable {vs : List HVar}

/-- `vg_hkdf_key` as emitted, cleanup included (`Impl.Hkdf.X86.Fn.key`),
with the tables of `vs`: it meets its contract in constant time and returns
without secret residue, given what the cleanup needs of its code. -/
theorem key_scrubbed (hO : OK vs) (hS : Streams vs)
    (hs : scrubFSide (Impl.Hkdf.X86.key (fnsOf vs)) [("hmac", tables vs)] kStack = true) :
    VerifiedScrubbed target (Impl.Hkdf.X86.Fn.key (fnsOf vs)) (specKey vs) 0 :=
  verifiedScrubbedAll (api := Spec.Hkdf.keyApi)
    { tables := [("hmac", tables vs)]
      code := Impl.Hkdf.X86.key (fnsOf vs)
      contract := specKey vs
      verified := key_spec hO hS
      spSafe := frame_sp (keyBody_okP vs) }
    (keyOut vs) (hs := hs)

/-- `vg_hkdf_extract` as emitted, cleanup included (`Impl.Hkdf.X86.Fn.extract`). -/
theorem extract_scrubbed (hO : OK vs)
    (hs : scrubFSide (Impl.Hkdf.X86.extract (fnsOf vs)) [("hmac", tables vs)] xStack = true) :
    VerifiedScrubbed target (Impl.Hkdf.X86.Fn.extract (fnsOf vs)) (specExtract vs) 0 :=
  verifiedScrubbedAll (api := Spec.Hkdf.extractApi)
    { tables := [("hmac", tables vs)]
      code := Impl.Hkdf.X86.extract (fnsOf vs)
      contract := specExtract vs
      verified := extract_spec hO
      spSafe := frame_sp (extractBody_okP vs) }
    (extractOut vs) (hs := hs)

/-- `vg_hkdf_expand` as emitted, cleanup included (`Impl.Hkdf.X86.Fn.expand`). -/
theorem expand_scrubbed (hO : OK vs) (hS : Streams vs)
    (hs : scrubFSide (Impl.Hkdf.X86.expand (fnsOf vs)) [("hmac", tables vs)] eStack = true) :
    VerifiedScrubbed target (Impl.Hkdf.X86.Fn.expand (fnsOf vs)) (specExpand vs) 0 :=
  verifiedScrubbedAll (api := Spec.Hkdf.expandApi)
    { tables := [("hmac", tables vs)]
      code := Impl.Hkdf.X86.expand (fnsOf vs)
      contract := specExpand vs
      verified := expand_spec hO hS
      spSafe := frame_sp (expandBody_okP vs) }
    (expandOut vs) (hs := hs)

end

/-! ## The registrations' variants -/

/-- The HMAC implementations of the table: SHA-1's and SHA-256's variants. -/
abbrev vs : List HVar := vars VG.Proof.Variants.Sha1.X86.variants VG.Proof.Variants.Sha256.X86.variants

/-- Each variant's streaming states are the specification's. -/
theorem vars_streams (vs1 : List Proof.Sha1.X86.Variants.Backend) (vs256 : List Proof.Sha256.X86.Variants.Backend) :
    Streams (vars vs1 vs256) := by
  intro w hw
  simp only [vars, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
    or_false] at hw
  rcases hw with rfl | ((⟨b, -, rfl⟩ | ⟨b, -, rfl⟩) | ⟨b, -, rfl⟩) | rfl | rfl | rfl | rfl <;> rfl

/-- What the cleanup needs of `vg_hkdf_key`'s code, evaluated once. -/
theorem keySide : scrubFSide (Impl.Hkdf.X86.key (fnsOf vs)) [("hmac", tables vs)] kStack = true := by
  lit_decide

/-- What the cleanup needs of `vg_hkdf_extract`'s code, evaluated once. -/
theorem extractSide : scrubFSide (Impl.Hkdf.X86.extract (fnsOf vs)) [("hmac", tables vs)] xStack = true := by
  lit_decide

/-- What the cleanup needs of `vg_hkdf_expand`'s code, evaluated once. -/
theorem expandSide : scrubFSide (Impl.Hkdf.X86.expand (fnsOf vs)) [("hmac", tables vs)] eStack = true := by
  lit_decide

/-- `vg_hkdf_key` as emitted, with the tables of the registrations' variants,
given what the registration checks of them (`OK`). -/
theorem key_scrubbedV (hO : OK vs) :
    VerifiedScrubbed target (Impl.Hkdf.X86.Fn.key (fnsOf vs)) (specKey vs) 0 :=
  key_scrubbed hO (vars_streams _ _) keySide

/-- `vg_hkdf_extract` as emitted, with the tables of the registrations' variants. -/
theorem extract_scrubbedV (hO : OK vs) :
    VerifiedScrubbed target (Impl.Hkdf.X86.Fn.extract (fnsOf vs)) (specExtract vs) 0 :=
  extract_scrubbed hO extractSide

/-- `vg_hkdf_expand` as emitted, with the tables of the registrations' variants. -/
theorem expand_scrubbedV (hO : OK vs) :
    VerifiedScrubbed target (Impl.Hkdf.X86.Fn.expand (fnsOf vs)) (specExpand vs) 0 :=
  expand_scrubbed hO (vars_streams _ _) expandSide

/-- No instruction of the functions as emitted writes `esp` but their frames'. -/
theorem key_spSafe (vs : List HVar) :
    (Impl.Hkdf.X86.Fn.key (fnsOf vs)).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (frame_sp (keyBody_okP vs))

theorem extract_spSafe (vs : List HVar) :
    (Impl.Hkdf.X86.Fn.extract (fnsOf vs)).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (frame_sp (extractBody_okP vs))

theorem expand_spSafe (vs : List HVar) :
    (Impl.Hkdf.X86.Fn.expand (fnsOf vs)).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (frame_sp (expandBody_okP vs))

end VG.Proof.Hkdf.X86.Scrub
