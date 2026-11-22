module

public import VerifiedGarbage.Proof.Hkdf.PPC64LE.Table
public import VerifiedGarbage.Proof.Hkdf.Common
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Hkdf.PPC64LE.Fn
public import VerifiedGarbage.Proof.HmacTable.PPC64LE.Vars
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Lit

/-!
# HKDF on PPC64LE, without secret residue

Each function as emitted (`Impl.Hkdf.PPC64LE.Fn`), generic over the HMAC
implementations its table holds, which it calls indirectly: its code, then
`Impl.Scrub.PPC64LE.scrubAll` (`PPC64LE.Scrub.verifiedScrubbedAll`), which
clears the volatile registers and zeroes the stack its frame and HMAC's
functions use. It calls indirectly only the functions of its table
(`PPC64LE.Scrub.tablesCall`), which the side condition, evaluated on the
code with the functions of `HmacTable.PPC64LE.vars`, checks, as ECDSA's does
(`Proof/Ecdsa/Rfc6979/PPC64LE/Scrub.lean`). The postconditions read the
memory on return only within the buffers they write (`keyOut`), as on
RISC-V (`Proof/Hkdf/RISCV64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Hkdf.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub
open VG.Proof.HmacTable.PPC64LE (HVar tables fnsOf vars)
open VG.Impl.Hkdf.PPC64LE (kFr xFr eFr)

/-! ## The postconditions -/

/-- `postOut_of_local`, for a postcondition that reads the memory on return
only within the buffers when the precondition holds (as RISC-V's
`RISCV64.Scrub.postOut_of_local_pre`). -/
theorem postOut_of_local_pre {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    (hl : ∀ vs m m₁ m₂ r, vs.length = (sig.words A.ptrBits).length →
      Curry.apply (sig.words A.ptrBits) pre vs m →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words A.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words A.ptrBits) post vs m m₂ r) :
    PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  intro s u u' hs hp hm hr
  simp only [Sig.contract] at hs hp ⊢
  revert hs hp
  cases hargs : A.args ((sig.words A.ptrBits).map (·.bits A.ptrBits)) with
  | none => intro hs; exact hs.elim
  | some vals =>
    intro hs hp
    simp only at hs hp ⊢
    obtain ⟨-, hrd, hwr, -, -, -, hpre⟩ := hs
    have hpre' : Curry.apply (sig.words A.ptrBits) pre (vals s) (A.mem s) := by
      cases hal : A.alignsBufs
      · rw [hal] at hpre; exact hpre
      · rw [hal] at hpre; exact hpre.1
    rw [hA.ret, hA.mem, hA.mem] at hp ⊢
    rw [hA.mem] at hpre'
    rw [hr]
    refine hl (vals s) _ _ _ _ (by rw [hA.argsLen _ _ hargs s, List.length_map]) hpre' (fun b hb a ha => ?_) hp
    have hin : b.1 ∈ s.rd ++ s.wr := by
      cases hw : b.2
      · apply List.mem_append_left; apply hA.rdSub; rw [hrd]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          by simp [hw]⟩, rfl⟩
      · apply List.mem_append_right; rw [← hA.wr, hwr]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          hw⟩, rfl⟩
    exact (hm a ⟨b.1, hin, ha⟩).symm

/-- `key`'s postcondition reads the memory on return only within `key`. -/
theorem keyOut (vs : List HVar) :
    PostOut (specKey vs) (Spec.Hkdf.keySig.retBits 64) :=
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
theorem extractOut (vs : List HVar) :
    PostOut (specExtract vs) (Spec.Hkdf.extractSig.retBits 64) :=
  postOut_of_local_pre (ScrubAbi.plain.tables _ _) fun vs m m₁ m₂ r hlen hpre hb h => by
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

/-- `expand`'s postcondition reads the memory on return only within `out`. -/
theorem expandOut (vs : List HVar) :
    PostOut (specExpand vs) (Spec.Hkdf.expandSig.retBits 64) :=
  postOut_of_local (ScrubAbi.plain.tables _ _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [key, info, il, out, ol, hm], _ =>
      simp only [Spec.Hkdf.expandSig, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size, Nat.mul_one] at hb
      intro H S prk hH hSt hK
      rw [h H S prk hH hSt hK]
      exact congrArg some (Proof.Sha256.Stream.bytesAt_congr fun i hi => by
        have hi' : i < ol.toNat := hi
        exact hb.2.2.1 _ (Offset.contains_base _ (by omega_using [hi']) (by have := ol.isLt; omega_using [hi', this])))

/-! ## The hash functions the registrations give -/

/-- Each hash function's streaming states are the specification's. -/
theorem vars_streams : Streams vars := by
  intro w hw
  simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ## The functions -/

/-- `vg_hkdf_key` as emitted (`Impl.Hkdf.PPC64LE.Fn.key`), with the HMAC
implementations of `HmacTable.PPC64LE.vars`, meets its contract in constant
time and returns without secret residue. -/
theorem key_scrubbed (hO : OK vars) :
    VerifiedScrubbed PPC64LE.target (Impl.Hkdf.PPC64LE.Fn.key (fnsOf vars)) (specKey vars) 0 :=
  verifiedScrubbedAll (api := Spec.Hkdf.keyApi) {
      tables := [("hmac", tables vars)]
      code := Impl.Hkdf.PPC64LE.key (fnsOf vars)
      contract := specKey vars
      verified := key_spec hO vars_streams }
    (kFr + 144) .all (keyOut vars) (by dsimp only; lit_decide)

/-- `vg_hkdf_extract` as emitted (`Impl.Hkdf.PPC64LE.Fn.extract`), with the
HMAC implementations of `HmacTable.PPC64LE.vars`. -/
theorem extract_scrubbed (hO : OK vars) :
    VerifiedScrubbed PPC64LE.target (Impl.Hkdf.PPC64LE.Fn.extract (fnsOf vars)) (specExtract vars) 0 :=
  verifiedScrubbedAll (api := Spec.Hkdf.extractApi) {
      tables := [("hmac", tables vars)]
      code := Impl.Hkdf.PPC64LE.extract (fnsOf vars)
      contract := specExtract vars
      verified := extract_spec hO vars_streams }
    (xFr + 144) .all (extractOut vars) (by dsimp only; lit_decide)

/-- `vg_hkdf_expand` as emitted (`Impl.Hkdf.PPC64LE.Fn.expand`), with the
HMAC implementations of `HmacTable.PPC64LE.vars`. -/
theorem expand_scrubbed (hO : OK vars) :
    VerifiedScrubbed PPC64LE.target (Impl.Hkdf.PPC64LE.Fn.expand (fnsOf vars)) (specExpand vars) 0 :=
  verifiedScrubbedAll (api := Spec.Hkdf.expandApi) {
      tables := [("hmac", tables vars)]
      code := Impl.Hkdf.PPC64LE.expand (fnsOf vars)
      contract := specExpand vars
      verified := expand_spec hO vars_streams }
    (eFr + 96) .all (expandOut vars) (by dsimp only; lit_decide)

end VG.Proof.Hkdf.PPC64LE.Scrub
