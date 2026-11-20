module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.TableSat
public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubCall
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.RISCV64.Fn
public import VerifiedGarbage.Proof.Variants.MdHash.RISCV64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# Deterministic ECDSA on RISC-V, without secret residue

The postcondition of `vg_ecdsa_<curve>_sign` reads the memory on return only
within `out` (`RISCV64.Scrub.PostOut`), as on AArch64
(`Proof/Ecdsa/Rfc6979/AArch64/Scrub.lean`): each implementation, generic
over the HMAC implementations its table holds, which it calls indirectly,
followed by its cleanup, returns with the caller-saved registers cleared and
its whole stack zeroed: the function as emitted is
`Impl.Ecdsa.Rfc6979.RISCV64.Fn.sign`, and `sign_scrubbed` is what a curve's
theorem comes from.

What the cleanup needs of the code (`RISCV64.Scrub.scrubSide`) is the
curve's to evaluate, once, with nothing in the place of HMAC's functions
(`stubFns`). The code with the functions of every hash function in their
place is that code filled (`sign_fill`, once for every curve), from what each
hash function states of its own code where it is defined (`HVar.scrub`):
nothing evaluates a hash function's code for its callers.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub
open VG.Proof.HmacTable.RISCV64 (HVar tables)

/-- The `n` bytes at `q` read the memory only within a region at `q` of at
least `n` bytes. -/
theorem bytesAt_of {m₁ m₂ : Mem} {q : Addr} {N n : Nat} (hn : n ≤ N)
    (h : ∀ a, Region.Contains ⟨q, N⟩ a 1 → m₁ a = m₂ a) :
    Spec.Sha3.bytesAt m₂ q n = Spec.Sha3.bytesAt m₁ q n := by
  simp only [Spec.Sha3.bytesAt]
  refine List.map_congr_left fun i hi => (h _ ?_).symm
  have hi := List.mem_range.mp hi
  simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have := Nat.mod_le i (2 ^ 64)
  omega_using [hn, hi]

/-- The postcondition reads the memory on return only within `out`. -/
theorem signOut (T : Spec.Ecdsa.Rfc6979.TableInstance) (cs : List (String × List (BitVec 64)))
    (vs : List HVar) :
    PostOut (specK T cs vs) (T.signSig.retBits 64) :=
  postOut_of_local ((ScrubAbi.consts cs).tables _ _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [out, d, dg, dl, sc, hm], _ =>
      simp only [Spec.Ecdsa.Rfc6979.TableInstance.signSig, Sig.bufs, List.mem_cons,
        forall_eq_or_imp, Elem.size, Nat.mul_one] at hb
      have e := bytesAt_of (n := 2 * T.ecdsa.curve.len) (Nat.le_refl _) hb.1
      intro H F h1 h2
      have h' := h H F h1 h2
      revert h'
      split
      · exact fun h' => ⟨h'.1, e.trans h'.2⟩
      · exact fun h' => ⟨h'.1, e.trans h'.2⟩

/-! ## The function, as emitted -/

open VG.Impl.Ecdsa.Rfc6979.RISCV64 (Cfg Fns)
open VG.Proof.HmacTable.RISCV64 (fnsOf names Coh mem_names)
open VG.Proof.Variants.MdHash.RISCV64 (variants fns)

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

/-- `vg_ecdsa_<curve>_sign` with the functions `f` is its code with nothing
in their place (`stubFns`), filled with them: whatever the curve. -/
theorem sign_fill (c : Cfg) {f : Fns} {N : List String}
    (hi : ∀ e ∈ f.init, e.1 ∈ N ∧ calleeSide e.2 512 = true)
    (hu : ∀ e ∈ f.upd, e.1 ∈ N ∧ calleeSide e.2 512 = true)
    (hf : ∀ e ∈ f.fin, e.1 ∈ N ∧ calleeSide e.2 512 = true) :
    Fill 512 N { c with f := stubFns }.sign { c with f := f }.sign := by
  fill_calls

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

/-- The streaming `update`s of the same name are the same code. -/
theorem upd_coh {w w' : HVar} (hw : w ∈ variants) (hw' : w' ∈ variants) (e : w.H.updN = w'.H.updN) :
    w.H.updC = w'.H.updC :=
  Option.some.inj ((upd_first w hw).trans (e ▸ (upd_first w' hw').symm))

/-- The hash functions the registrations give meet what the function needs
of their tables: HMAC's `init` and `finalize` have distinct names, and the
streaming `update`s of the same name are the same code. -/
theorem variants_ok : OK variants := by
  obtain ⟨hi, hf⟩ : (variants.map (·.hiN)).Nodup ∧ (variants.map (·.hfN)).Nodup :=
    of_decide_eq_true (by kernel_rfl)
  refine ⟨fun w hw w' hw' => ⟨fun e => ?_, upd_coh hw hw', fun e => ?_⟩,
    of_decide_eq_true (by kernel_rfl), nofun⟩
  · rw [eq_of_map_nodup hi hw hw' e]
  · rw [eq_of_map_nodup hf hw hw' e]

theorem mem_tableFns {vs : List HVar} {f : String} (h : f ∈ names vs) :
    f ∈ tableFns [("hmac", Proof.HmacTable.RISCV64.tables vs)] := by
  simp only [tableFns, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_flatMap]
  simp only [names, List.mem_flatten, List.mem_map] at h
  obtain ⟨_, ⟨t, ht, rfl⟩, hf⟩ := h
  exact ⟨t, ht, hf⟩

/-- `vg_ecdsa_<curve>_sign` as emitted, cleanup included
(`Impl.Ecdsa.Rfc6979.RISCV64.Fn.sign`), with the configuration `c fns` and
the tables of every hash function: it meets its contract in constant time
and returns without secret residue. What the cleanup needs of the code is
the curve's to evaluate, once, with nothing in the place of HMAC's functions
(`hs`), filled with every hash function's (`sign_fill`, of `c`, a curve's
configuration of the functions it calls through its table: `hcf`); `hv` is
its verification, of the code `hc` says it is. -/
theorem sign_scrubbed {R : CurveT} {T : Spec.Ecdsa.Rfc6979.TableInstance}
    {cs : List (String × List (BitVec 64))} (c : Fns → Cfg)
    (hv : Verified target (signCodeT R T.tries variants) (specK T cs variants))
    (hc : signCodeT R T.tries variants = (c fns).sign)
    (hs : scrubSide (c stubFns).sign 512 32 [] = true)
    (hcf : ∀ f, c f = { c stubFns with f := f } := by intro; rfl):
    VerifiedScrubbed target (Impl.Ecdsa.Rfc6979.RISCV64.Fn.sign (c fns)) (specK T cs variants) 32 := by
  have hfill : Fill 512 (names variants) (c stubFns).sign (c fns).sign := by
    have hside := fnsOf_side variants
    have h := sign_fill (c stubFns) (f := fns) hside.1 hside.2.1 hside.2.2
    rwa [← hcf fns, ← hcf stubFns] at h
  have h := scrubSide_of_fill (W := 1024) hfill hs (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => mem_tableFns h)
  rw [hc] at hv
  exact verifiedScrubbed (api := T.signApi)
    { tables := [("hmac", Proof.HmacTable.RISCV64.tables variants)]
      code := (c fns).sign
      contract := specK T cs variants
      verified := hv }
    (signOut T cs variants) h

end VG.Proof.Ecdsa.Rfc6979.RISCV64.Scrub
