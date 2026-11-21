module

public import VerifiedGarbage.Proof.Hkdf.RISCV64.Table
public import VerifiedGarbage.Proof.Hkdf.Common
public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubCall
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Hkdf.RISCV64.Fn
public import VerifiedGarbage.Proof.Variants.MdHash.RISCV64
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Hkdf.RISCV64.Fn

/-!
# HKDF on RISC-V, without secret residue

Each function, generic over the HMAC implementations its table holds, which
it calls indirectly, followed by its cleanup, returns with the caller-saved
registers cleared and its whole stack zeroed (`Impl.Hkdf.RISCV64.Fn`). What
the cleanup needs of the code (`RISCV64.Scrub.scrubSide`) is evaluated once,
with nothing in the place of HMAC's functions (`stubFns`); the code with
the functions of every hash function in their place is that code filled
(`key_fill`), from what each hash function states of its own code where it
is defined (`HVar.scrub`). The postconditions read the memory on return
only within the buffers they write (`keyOut`): `key`'s, through the
streaming states' `Repr`, which depends on their bytes alone
(`Proof.Hkdf.streamingOf_local`).
-/

@[expose] public section

namespace VG.Proof.Hkdf.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub
open VG.Impl.Ecdsa.Rfc6979.RISCV64 (Fns)
open VG.Proof.HmacTable.RISCV64 (HVar tables fnsOf names mem_names)

/-- Nothing in the place of HMAC's functions: the code with it calls nothing
indirectly. -/
def stubFns : Fns := ⟨[], [], []⟩

/-- Each function an indirect call of a slot of the tables of `vs` reaches
is named in them, uses at most 512 bytes of stack and calls nothing
indirectly: what each hash function states of its own code. -/
theorem fnsOf_side (vs : List HVar) :
    (∀ e ∈ (fnsOf vs).init, e.1 ∈ names vs ∧ calleeSide e.2 512 = true) ∧
      (∀ e ∈ (fnsOf vs).upd, e.1 ∈ names vs ∧ calleeSide e.2 512 = true) ∧
      (∀ e ∈ (fnsOf vs).fin, e.1 ∈ names vs ∧ calleeSide e.2 512 = true) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro e he <;> simp only [fnsOf, List.mem_map] at he <;>
    obtain ⟨w, hw, rfl⟩ := he <;> have h := w.scrub <;> simp only [Bool.and_eq_true] at h
  · exact ⟨(mem_names hw).1, h.1.1⟩
  · exact ⟨(mem_names hw).2.1, h.1.2⟩
  · exact ⟨(mem_names hw).2.2, h.2⟩

theorem mem_tableFns {vs : List HVar} {f : String} (h : f ∈ names vs) :
    f ∈ tableFns [("hmac", tables vs)] := by
  simp only [tableFns, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_flatMap]
  simp only [names, List.mem_flatten, List.mem_map] at h
  obtain ⟨_, ⟨t, ht, rfl⟩, hf⟩ := h
  exact ⟨t, ht, hf⟩

/-! ## `vg_hkdf_key` -/

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

/-- `vg_hkdf_key` with the functions `f` is its code with nothing in their
place (`stubFns`), filled with them. -/
theorem key_fill {f : Fns} {N : List String} (hi : ∀ e ∈ f.init, e.1 ∈ N ∧ calleeSide e.2 512 = true) :
    Fill 512 N (Impl.Hkdf.RISCV64.key stubFns) (Impl.Hkdf.RISCV64.key f) := by
  fill_calls

theorem key_side : scrubSide (Impl.Hkdf.RISCV64.key stubFns) 16 0 [] = true := by lit_decide

/-- `vg_hkdf_key` as emitted, cleanup included (`Impl.Hkdf.RISCV64.Fn.key`),
with the tables of `vs`: it meets its contract in constant time and returns
without secret residue. -/
theorem key_scrubbed {vs : List HVar} (hO : OK vs) (hS : Streams vs) :
    VerifiedScrubbed target (Impl.Hkdf.RISCV64.Fn.key (fnsOf vs)) (specKey vs) 0 := by
  have hfill := key_fill (f := fnsOf vs) (fnsOf_side vs).1
  have h := scrubSide_of_fill (W := 528) hfill key_side (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => mem_tableFns h)
  exact verifiedScrubbedAll (api := Spec.Hkdf.keyApi)
    { tables := [("hmac", tables vs)]
      code := Impl.Hkdf.RISCV64.key (fnsOf vs)
      contract := specKey vs
      verified := key_spec hO hS }
    (keyOut vs) h

/-! ## `vg_hkdf_extract` -/

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

/-- `vg_hkdf_extract` with the functions `f` is its code with nothing in
their place, filled with them. -/
theorem extract_fill {f : Fns} {N : List String} (hi : ∀ e ∈ f.init, e.1 ∈ N ∧ calleeSide e.2 512 = true)
    (hu : ∀ e ∈ f.upd, e.1 ∈ N ∧ calleeSide e.2 512 = true)
    (hf : ∀ e ∈ f.fin, e.1 ∈ N ∧ calleeSide e.2 512 = true) :
    Fill 512 N (Impl.Hkdf.RISCV64.extract stubFns) (Impl.Hkdf.RISCV64.extract f) := by
  fill_calls

theorem extract_side : scrubSide (Impl.Hkdf.RISCV64.extract stubFns) 480 0 [] = true := by lit_decide

theorem extract_scrubbed {vs : List HVar} (hO : OK vs) :
    VerifiedScrubbed target (Impl.Hkdf.RISCV64.Fn.extract (fnsOf vs)) (specExtract vs) 0 := by
  have hs := fnsOf_side vs
  have hfill := extract_fill (f := fnsOf vs) hs.1 hs.2.1 hs.2.2
  have h := scrubSide_of_fill (W := 992) hfill extract_side (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => mem_tableFns h)
  exact verifiedScrubbedAll (api := Spec.Hkdf.extractApi)
    { tables := [("hmac", tables vs)]
      code := Impl.Hkdf.RISCV64.extract (fnsOf vs)
      contract := specExtract vs
      verified := extract_spec hO }
    (extractOut vs) h

/-! ## `vg_hkdf_expand` -/

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

/-- `vg_hkdf_expand` with the functions `f` is its code with nothing in
their place, filled with them. -/
theorem expand_fill {f : Fns} {N : List String} (hu : ∀ e ∈ f.upd, e.1 ∈ N ∧ calleeSide e.2 512 = true)
    (hf : ∀ e ∈ f.fin, e.1 ∈ N ∧ calleeSide e.2 512 = true) :
    Fill 512 N (Impl.Hkdf.RISCV64.expand stubFns) (Impl.Hkdf.RISCV64.expand f) := by
  fill_calls

theorem expand_side : scrubSide (Impl.Hkdf.RISCV64.expand stubFns) 368 0 [] = true := by lit_decide

theorem expand_scrubbed {vs : List HVar} (hO : OK vs) (hS : Streams vs) :
    VerifiedScrubbed target (Impl.Hkdf.RISCV64.Fn.expand (fnsOf vs)) (specExpand vs) 0 := by
  have hs := fnsOf_side vs
  have hfill := expand_fill (f := fnsOf vs) hs.2.1 hs.2.2
  have h := scrubSide_of_fill (W := 880) hfill expand_side (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => mem_tableFns h)
  exact verifiedScrubbedAll (api := Spec.Hkdf.expandApi)
    { tables := [("hmac", tables vs)]
      code := Impl.Hkdf.RISCV64.expand (fnsOf vs)
      contract := specExpand vs
      verified := expand_spec hO hS }
    (expandOut vs) h

/-! ## The hash functions the registrations give -/

open VG.Proof.Variants.MdHash.RISCV64 (variants fns)

theorem eq_of_map_nodup {α β : Type} {f : α → β} :
    ∀ {l : List α} {x y : α}, (l.map f).Nodup → x ∈ l → y ∈ l → f x = f y → x = y
  | a :: l, x, y, h, hx, hy, e => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact absurd (show f x ∈ l.map f by rw [e]; exact List.mem_map_of_mem hy') h.1
    · exact absurd (show f y ∈ l.map f by rw [← e]; exact List.mem_map_of_mem hx') h.1
    · exact eq_of_map_nodup h.2 hx' hy' e

/-- Each hash function's streaming `update` is the code of the first of
`variants` its name finds: several share one (SHA-224 SHA-256's, SHA-384 and
SHA-512/t SHA-512's), by the same constant. -/
theorem upd_first : ∀ w ∈ variants,
    some w.H.updC = (variants.find? (·.H.updN == w.H.updN)).map (·.H.updC) := by
  intro w hw
  simp only [variants, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> kernel_rfl

theorem upd_coh {w w' : HVar} (hw : w ∈ variants) (hw' : w' ∈ variants) (e : w.H.updN = w'.H.updN) :
    w.H.updC = w'.H.updC :=
  Option.some.inj ((upd_first w hw).trans (e ▸ (upd_first w' hw').symm))

/-- The hash functions the registrations give meet what the functions need
of their tables: HMAC's `init` and `finalize` have distinct names, and the
streaming `update`s of the same name are the same code. -/
theorem variants_ok : OK variants := by
  obtain ⟨hi, hf⟩ : (variants.map (·.hiN)).Nodup ∧ (variants.map (·.hfN)).Nodup :=
    of_decide_eq_true (by kernel_rfl)
  refine ⟨fun w hw w' hw' => ⟨fun e => ?_, upd_coh hw hw', fun e => ?_⟩,
    of_decide_eq_true (by kernel_rfl), nofun⟩
  · rw [eq_of_map_nodup hi hw hw' e]
  · rw [eq_of_map_nodup hf hw hw' e]

/-- Each hash function's streaming states are the specification's. -/
theorem variants_streams : Streams variants := by
  intro w hw
  simp only [variants, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `vg_hkdf_key` as emitted, with the tables of the registrations' hash
functions. -/
theorem key_scrubbedV : VerifiedScrubbed target (Impl.Hkdf.RISCV64.Fn.key fns) (specKey variants) 0 :=
  key_scrubbed variants_ok variants_streams

/-- `vg_hkdf_extract` as emitted, with the tables of the registrations' hash
functions. -/
theorem extract_scrubbedV :
    VerifiedScrubbed target (Impl.Hkdf.RISCV64.Fn.extract fns) (specExtract variants) 0 :=
  extract_scrubbed variants_ok

/-- `vg_hkdf_expand` as emitted, with the tables of the registrations' hash
functions. -/
theorem expand_scrubbedV :
    VerifiedScrubbed target (Impl.Hkdf.RISCV64.Fn.expand fns) (specExpand variants) 0 :=
  expand_scrubbed variants_ok variants_streams

end VG.Proof.Hkdf.RISCV64.Scrub
