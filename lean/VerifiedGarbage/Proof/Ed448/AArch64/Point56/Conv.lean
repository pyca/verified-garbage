import VerifiedGarbage.Proof.X448.AArch64.Fast.Env
import VerifiedGarbage.Proof.Framework.AArch64.StoreFrame
import VerifiedGarbage.Spec.Ed448.Point56

/-!
# Ed448 on AArch64: the specification's elements and the proofs'

Untrusted: everything here is checked by Lean. `Spec/X448/Field56.lean`
states the elements as the register-resident arithmetic's proofs keep them:
the same limbs (`limbAt_eq`), values (`elemAt_eq`) and bounds (`bounded_iff`,
`res_iff`). The bytes a function keeps (`Field56.Keeps`) follow from its stores
(`keeps_of_unstored`, from `Exec.storeFrame`).
-/

namespace VG.Proof.Ed448.AArch64.Point56

open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot)
open VG.Proof.X448.AArch64 (limbs)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Spec.X448.Field56 (limbAt valAt elemAt Bounded Res slotAt)

theorem limbAt_eq (m : Mem) (ws : Addr) (o i : Nat) : limbAt m ws o i = limbs m ws o i := rfl

theorem slotAt_eq (n : Nat) : slotAt n = slot n := rfl

theorem valN_eq (m : Mem) (ws : Addr) (o : Nat) :
    ∀ n, Spec.X448.Field56.valN m ws o n = VG.Proof.X448.Wide.valN (limbs m ws o) n
  | 0 => rfl
  | n + 1 => by
    rw [Spec.X448.Field56.valN, VG.Proof.X448.Wide.valN, valN_eq m ws o n, limbAt_eq,
      VG.Proof.X448.Wide.radix, ← Nat.pow_mul]

theorem elemAt_eq (m : Mem) (ws : Addr) (i : Index) :
    elemAt m ws (slotAt i.val) = VG.Proof.X448.AArch64.Weak.E m ws i := by
  simp only [elemAt, valAt, Spec.X448.Field56.limbs, valN_eq, slotAt_eq]
  rfl

theorem bounded_iff (m : Mem) (ws : Addr) : Bounded m ws ↔ BEnv m ws := by
  constructor
  · intro h i j hj
    exact h i.val i.isLt j hj
  · intro h n hn j hj
    exact h ⟨n, hn⟩ j hj

theorem res_iff (m : Mem) (ws : Addr) (n : Nat) : Res m ws n ↔ Bnd Mb m ws (slot n) := Iff.rfl

/-- The bytes outside the ranges `rs` are in no store at an offset `ok` accepts, if each such
store lies in one of the ranges. -/
theorem unstored_of {ok : Nat → Bool} {rs : List (Nat × Nat)} (hok : ∀ d, ok d = true →
      d + 8 ≤ 8192 ∧ ∃ r ∈ rs, r.1 ≤ d ∧ d + 8 ≤ r.2)
    (ws : Addr) {i : Nat} (hi : i < 8192) (hr : ∀ r ∈ rs, i < r.1 ∨ r.2 ≤ i) :
    Unstored ok ws (ws + BitVec.ofNat 64 i) := by
  intro d hd
  obtain ⟨hd8, r, hrs, h1, h2⟩ := hok d hd
  have := hr r hrs
  rw [Offset.add_sub_add_left, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- `Field56.Keeps` from the stores. -/
theorem keeps_of_unstored {ok : Nat → Bool} {rs : List (Nat × Nat)} (hok : ∀ d, ok d = true →
      d + 8 ≤ 8192 ∧ ∃ r ∈ rs, r.1 ≤ d ∧ d + 8 ≤ r.2)
    {ws : Addr} {m m' : Mem} (h : ∀ a, Unstored ok ws a → m' a = m a) :
    Spec.X448.Field56.Keeps ws rs m m' := fun _ hi hr => h _ (unstored_of hok ws hi hr)

end VG.Proof.Ed448.AArch64.Point56
