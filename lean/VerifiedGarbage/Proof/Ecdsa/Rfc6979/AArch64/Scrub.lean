module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSpec
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Deterministic ECDSA on AArch64, without secret residue

The postcondition of `vg_ecdsa_<curve>_sign` reads the memory on return only
within `out` (`ScrubAll.ScrubAllOk`, as x86-64's
`Proof/Ecdsa/Rfc6979/X86_64/Scrub.lean` proves it): each implementation,
generic over the HMAC implementations its table holds, which it calls
indirectly, returns with every register it may leave secret cleared and its
whole stack zeroed (`ScrubAll.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.HmacTable.AArch64 (tables)

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
theorem post_local (T : Spec.Ecdsa.Rfc6979.TableInstance) {A : Abi isa} :
    ∀ vs m m₁ m₂ r, vs.length = (T.signSig.words A.ptrBits).length →
      (∀ b ∈ Sig.bufs T.signSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (T.signSig.words A.ptrBits) (fun out d digest _digestLen _scratch hmac m m' r =>
        ∀ H F, Spec.HmacTable.hashAt A.ptrBits m hmac = some H → Spec.HmacTable.hmacOf H = some F →
          match (T.result H F m d digest).1 with
          | some rs => r = 1 ∧ Spec.Sha3.bytesAt m' out (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
          | none => r = 0 ∧ Spec.Sha3.bytesAt m' out (2 * T.ecdsa.curve.len) =
              List.replicate (2 * T.ecdsa.curve.len) 0 : T.signSig.Post A.ptrBits) vs m m₁ r →
      Curry.apply (T.signSig.words A.ptrBits) (fun out d digest _digestLen _scratch hmac m m' r =>
        ∀ H F, Spec.HmacTable.hashAt A.ptrBits m hmac = some H → Spec.HmacTable.hmacOf H = some F →
          match (T.result H F m d digest).1 with
          | some rs => r = 1 ∧ Spec.Sha3.bytesAt m' out (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
          | none => r = 0 ∧ Spec.Sha3.bytesAt m' out (2 * T.ecdsa.curve.len) =
              List.replicate (2 * T.ecdsa.curve.len) 0 : T.signSig.Post A.ptrBits) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
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

theorem signOk (T : Spec.Ecdsa.Rfc6979.TableInstance) (cs : List (String × List (BitVec 64)))
    (vs : List MdHash) :
    ScrubAllOk (specK T cs vs) stackT
      (T.signSig.retBits ((abi.withConsts cs).withTables T.signSig [("hmac", tables vs)]).ptrBits) := by
  cases cs with
  | nil =>
    exact scrubAllOk_tables (scrubAllOk_regs (sig := T.signSig) (Nat.le_of_ble_eq_true rfl) (by decide)
      (Nat.le_refl _) (post_local T))
  | cons c₀ cs =>
    exact scrubAllOk_tables (scrubAllOk_consts (sig := T.signSig) (Nat.le_of_ble_eq_true rfl) (by decide)
      (Nat.le_refl _) (post_local T))

end VG.Proof.Ecdsa.Rfc6979.AArch64.Scrub
