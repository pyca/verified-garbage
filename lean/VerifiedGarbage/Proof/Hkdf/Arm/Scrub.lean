module

public import VerifiedGarbage.Proof.Hkdf.Arm.Table
public import VerifiedGarbage.Proof.Hkdf.Common
public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Rsa.Arm.ScrubTab
public import VerifiedGarbage.Impl.Hkdf.Arm.Fn
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# HKDF on 32-bit ARM, without secret residue

As for deterministic ECDSA's signing (`Proof/Ecdsa/Rfc6979/Arm/Scrub.lean`):
each function, generic over the HMAC implementations its table holds, which
it calls indirectly, is emitted followed by a wipe of the stack its contract
reserves and instructions that set the registers a callee may change and the
flags to constants (`Impl.Hkdf.Arm.Fn`), and proven so by
`Arm.Scrub.verifiedScrubbedAll`. Its postcondition reads the memory on return
only within the buffers it writes (`keyOut`, `extractOut`, `expandOut`):
`key`'s through the streaming states' `Repr`, which depends on their bytes
alone (`Proof.Hkdf.streamingOf_local`), and `extract`'s `PRK` of the digest's
length, `prk_len` by the precondition. What the cleanup needs of the code
(`Arm.Scrub.scrubSideF`: its frames within the stack its contract reserves,
and indirect calls only of functions of its table) follows from the code's
shape (`CodeOkT`) and from what each HMAC implementation of the table states
of its own (`HVar.scrub`, `fnsOf_init`): no HMAC function's code is
evaluated.
-/

@[expose] public section

namespace VG.Proof.Hkdf.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub
open VG.Impl.Hkdf.Arm
open VG.Impl.Ecdsa.Rfc6979.Arm (Fns)
open VG.Proof.HmacTable.Arm (HVar vars tables fnsOf CodeOkT.icallsK fnsOf_init fnsOf_upd fnsOf_fin)
open VG.Proof.Rsa.Arm.Scrub (CodeOkT CodeOkT.block CodeOkT.seq CodeOkT.ite CodeOkT.loop CodeOkT.alloc
  CodeOkT.push scrubSideF_ofT)
open VG.Proof.Hkdf.Arm (OK Streams specKey specExtract specExpand tableRegion_eq names_eq argAddr0)

/-! ## The postconditions read only the buffers -/

/-- `key`'s postcondition reads the memory on return only within `key`. -/
theorem keyOut (vs : List HVar) : PostOut (specKey vs) 0 :=
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

/-- `extract`'s postcondition reads the memory on return only within `prk`,
of `prk_len` bytes, the digest's length by the precondition. -/
theorem extractOut (vs : List HVar) : PostOut (specExtract vs) 0 := by
  intro s u u' hs hp hm _
  sig_pre [Spec.Hkdf.extractContract, Spec.Hkdf.extractSig, Spec.Hkdf.extractPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, stackBelow, Extract.xStack, String.reduceEq,
    Option.map_some, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, tableRegion_eq, names_eq, argAddr0] at hs
  obtain ⟨-, -, -, -, -, hwr, -, -, -, -, -, -, -, -, -, -, -, n3, -, hP⟩ := hs
  sig_post [Spec.Hkdf.extractContract, Spec.Hkdf.extractSig, Spec.Hkdf.extractPost,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, stackBelow, Extract.xStack, String.reduceEq,
    Option.map_some, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, tableRegion_eq, names_eq, argAddr0] at hp ⊢
  intro H F hH hF
  rw [← hp H F hH hF]
  have hl := (hP H hH).1
  refine Proof.Sha256.Stream.bytesAt_congr fun i hi => hm _ ⟨_, List.mem_append_right _ (by
    rw [hwr]; exact List.mem_singleton_self _), Offset.contains_base _ (by omega_using [hl, hi]) (by
      have := (stackArg s 0).isLt; omega_using [n3, hl, hi, this])⟩

/-- `expand`'s postcondition reads the memory on return only within `out`. -/
theorem expandOut (vs : List HVar) : PostOut (specExpand vs) 0 :=
  postOut_of_local (ScrubAbi.plain.tables _ _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [key, info, il, out, ol, hm], _ =>
      simp only [Spec.Hkdf.expandSig, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size, Nat.mul_one] at hb
      intro H S prk hH hSt hK
      rw [h H S prk hH hSt hK]
      exact congrArg some (Proof.Sha256.Stream.bytesAt_congr fun i hi => by
        have hi' : i < (ol.setWidth 32).toNat := hi
        have hw : (ol.setWidth 32).toNat ≤ ol.toNat := by rw [BitVec.toNat_setWidth]; exact Nat.mod_le _ _
        exact hb.2.2.1 _ (Offset.contains_base _ (by omega_using [hi', hw])
          (by have := (ol.setWidth 32).isLt; omega_using [hi', this])))

/-! ## What the cleanup needs of the code -/

section
variable {T : List String}

/-- A call through the table, whose frame leaves 16 bytes for the function
it calls. -/
theorem tcall_okT {t : Reg} {j : Nat} {ts : List (String × Prog isa)} {rs : List Reg} {r : Reg} {k n : Nat}
    (hk : 4 * rs.length ≤ n) (h16 : 16 ≤ n - 4 * rs.length) (h : ∀ p ∈ ts, CodeOk p.2 16 ∧ p.1 ∈ T) :
    CodeOkT (tcall t j ts rs r k) n T :=
  CodeOkT.seq CodeOkT.block (CodeOkT.push hk (CodeOkT.icallsK h16 h))

theorem key_okT {f : Fns} (hi : ∀ p ∈ f.init, CodeOk p.2 16 ∧ p.1 ∈ T) : CodeOkT (key f) (kFr + 32) T :=
  CodeOkT.alloc (by decide) (CodeOkT.seq CodeOkT.block
    (CodeOkT.seq (CodeOkT.push (by decide) (CodeOkT.icallsK (by decide) hi)) CodeOkT.block))

theorem extract_okT {f : Fns} (hi : ∀ p ∈ f.init, CodeOk p.2 16 ∧ p.1 ∈ T)
    (hu : ∀ p ∈ f.upd, CodeOk p.2 16 ∧ p.1 ∈ T) (hf : ∀ p ∈ f.fin, CodeOk p.2 16 ∧ p.1 ∈ T) :
    CodeOkT (extract f) (xFr + 32) T :=
  CodeOkT.alloc (by decide) (CodeOkT.seq CodeOkT.block
    (CodeOkT.seq (tcall_okT (by decide) (by decide) hi) (CodeOkT.seq CodeOkT.block
    (CodeOkT.seq (tcall_okT (by decide) (by decide) hu) (CodeOkT.seq CodeOkT.block
    (CodeOkT.seq (tcall_okT (by decide) (by decide) hf) CodeOkT.block))))))

theorem block_okT {f : Fns} (hu : ∀ p ∈ f.upd, CodeOk p.2 16 ∧ p.1 ∈ T)
    (hf : ∀ p ∈ f.fin, CodeOk p.2 16 ∧ p.1 ∈ T) : CodeOkT (block f) 32 T :=
  CodeOkT.seq CodeOkT.block (CodeOkT.seq (CodeOkT.loop CodeOkT.block)
  (CodeOkT.seq CodeOkT.block (CodeOkT.seq (tcall_okT (by decide) (by decide) hu)
  (CodeOkT.seq CodeOkT.block (CodeOkT.seq (tcall_okT (by decide) (by decide) hu)
  (CodeOkT.seq CodeOkT.block (CodeOkT.seq (tcall_okT (by decide) (by decide) hu)
  (CodeOkT.seq CodeOkT.block (CodeOkT.seq (tcall_okT (by decide) (by decide) hf)
  (CodeOkT.seq CodeOkT.block (CodeOkT.seq (CodeOkT.loop CodeOkT.block) CodeOkT.block)))))))))))

theorem expand_okT {f : Fns} (hu : ∀ p ∈ f.upd, CodeOk p.2 16 ∧ p.1 ∈ T)
    (hf : ∀ p ∈ f.fin, CodeOk p.2 16 ∧ p.1 ∈ T) : CodeOkT (expand f) (eFr + 32) T :=
  CodeOkT.alloc (by decide) (CodeOkT.seq CodeOkT.block
    (CodeOkT.seq (CodeOkT.ite CodeOkT.block (CodeOkT.loop (block_okT hu hf))) CodeOkT.block))

end

/-! ## The registrations' variants -/

/-- The hash functions the registrations give meet what the functions need
of them. -/
theorem vars_ok : OK vars := by
  refine ⟨HmacTable.Arm.vars_coh, by decide, List.cons_ne_nil _ _, fun w hw => ?_⟩
  have hl := HmacTable.Arm.vars_macLen w hw
  simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
    Nat.le_of_ble_eq_true rfl, hl⟩

/-- Each variant's streaming states are the specification's. -/
theorem vars_streams : Streams vars := by
  intro w hw
  simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

/-- `vg_hkdf_key` as emitted, cleanup included (`Impl.Hkdf.Arm.Fn.key`),
with the tables of the registrations' variants: it meets its contract in
constant time and returns without secret residue. -/
theorem key_scrubbedV :
    VerifiedScrubbed target (Impl.Hkdf.Arm.Fn.key (fnsOf vars)) (specKey vars) 0 :=
  verifiedScrubbedAll (api := Spec.Hkdf.keyApi)
    { tables := [("hmac", tables vars)]
      code := key (fnsOf vars)
      verified := Proof.Hkdf.Arm.key_spec vars_ok vars_streams }
    (keyOut vars) (scrubSideF_ofT (key_okT (fnsOf_init vars)) (by decide))

/-- `vg_hkdf_extract` as emitted, with the tables of the registrations'
variants. -/
theorem extract_scrubbedV :
    VerifiedScrubbed target (Impl.Hkdf.Arm.Fn.extract (fnsOf vars)) (specExtract vars) 0 :=
  verifiedScrubbedAll (api := Spec.Hkdf.extractApi)
    { tables := [("hmac", tables vars)]
      code := extract (fnsOf vars)
      verified := Proof.Hkdf.Arm.extract_spec vars_ok }
    (extractOut vars)
    (scrubSideF_ofT (extract_okT (fnsOf_init vars) (fnsOf_upd vars) (fnsOf_fin vars)) (by decide))

/-- `vg_hkdf_expand` as emitted, with the tables of the registrations'
variants. -/
theorem expand_scrubbedV :
    VerifiedScrubbed target (Impl.Hkdf.Arm.Fn.expand (fnsOf vars)) (specExpand vars) 0 :=
  verifiedScrubbedAll (api := Spec.Hkdf.expandApi)
    { tables := [("hmac", tables vars)]
      code := expand (fnsOf vars)
      verified := Proof.Hkdf.Arm.expand_spec vars_ok vars_streams }
    (expandOut vars) (scrubSideF_ofT (expand_okT (fnsOf_upd vars) (fnsOf_fin vars)) (by decide))

end VG.Proof.Hkdf.Arm.Scrub
