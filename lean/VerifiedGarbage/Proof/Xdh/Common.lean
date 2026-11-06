module

public import VerifiedGarbage.Spec.X25519.Contract
public import VerifiedGarbage.Spec.X448.Contract

/-!
# X25519 and X448 exchange: the check, on any target

Untrusted: everything here is checked by Lean. The OR of the `n` bytes at
`a` (`orAll`) is zero exactly when they are all zero (`orAll_eq_zero`), the
check RFC 7748 §6.1 and §6.2 allow of the shared secret, which each
target's exchange function computes from the bytes the unchecked function
wrote.
-/

@[expose] public section

namespace VG.Proof.Xdh

open VG

/-- The OR of the first `n` bytes at `a`. -/
def orAll (m : Mem) (a : Addr) : Nat → Byte
  | 0 => 0
  | n + 1 => orAll m a n ||| m (a + BitVec.ofNat 64 n)

/-- X448's `bytesAt` is X25519's. -/
theorem x448_bytesAt (m : Mem) (p : Addr) (n : Nat) :
    Spec.X448.bytesAt m p n = Spec.X25519.bytesAt m p n := rfl

theorem orAll_eq_zero (m : Mem) (a : Addr) (n : Nat) :
    orAll m a n = 0 ↔ Spec.X25519.bytesAt m a n = List.replicate n 0 := by
  induction n with
  | zero => simp [orAll, Spec.X25519.bytesAt]
  | succ n ih =>
    have e : Spec.X25519.bytesAt m a (n + 1) = Spec.X25519.bytesAt m a n ++ [m (a + BitVec.ofNat 64 n)] := by
      simp only [Spec.X25519.bytesAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    have hl : (Spec.X25519.bytesAt m a n).length = (List.replicate n (0 : Byte)).length := by
      simp [Spec.X25519.bytesAt]
    have hor : ∀ x y : Byte, (x ||| y = 0) ↔ (x = 0 ∧ y = 0) := fun _ _ => BitVec.or_eq_zero_iff
    rw [orAll, hor, ih, e, List.replicate_succ']
    constructor
    · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]
    · intro h
      obtain ⟨h₁, h₂⟩ := List.append_inj h hl
      exact ⟨h₁, List.cons.inj h₂ |>.1⟩

/-- The check's result, from the OR zero-extended to 64 bits, as `sltu` (`0 < x`) gives it. -/
theorem result_lt (d : Byte) :
    ((if (0 : BitVec 64) < d.setWidth 64 then (1 : BitVec 64) else 0).setWidth 32) =
      if d = 0 then 0 else 1 := by
  have h : ∀ d : Byte, ((if (0 : BitVec 64) < d.setWidth 64 then (1 : BitVec 64) else 0).setWidth 32) =
      if d = 0 then 0 else 1 := by decide +kernel
  exact h d

/-- The check's result, as `((acc - 1) >> 63) ^ 1` gives it from the OR `acc` zero-extended to 64
bits. -/
theorem result_shr (d : Byte) :
    ((((d.setWidth 64 - 1) >>> 63) ^^^ (1 : BitVec 64)).setWidth 32) = if d = 0 then 0 else 1 := by
  have h : ∀ d : Byte, ((((d.setWidth 64 - 1) >>> 63) ^^^ (1 : BitVec 64)).setWidth 32) =
      if d = 0 then 0 else 1 := by decide +kernel
  exact h d

/-- The check's result on a 32-bit target: `((acc - 1) >> 31) ^ 1` of the OR `acc` zero-extended
to 32 bits. -/
theorem result_shr32 (d : Byte) :
    (((d.setWidth 32 - 1) >>> 31) ^^^ (1 : BitVec 32)) = if d = 0 then 0 else 1 := by
  have h : ∀ d : Byte, (((d.setWidth 32 - 1) >>> 31) ^^^ (1 : BitVec 32)) = if d = 0 then 0 else 1 := by
    decide +kernel
  exact h d

/-- The check's result, as the contracts state it. -/
theorem result_spec (m : Mem) (a : Addr) (n : Nat) (z : List Byte)
    (hz : Spec.X25519.bytesAt m a n = z) :
    (if orAll m a n = 0 then (0 : BitVec 32) else 1) = if z = List.replicate n 0 then 0 else 1 := by
  subst hz
  have h := orAll_eq_zero m a n
  by_cases h' : orAll m a n = 0
  · simp only [h', h.mp h', ↓reduceIte]
  · have h'' : ¬ Spec.X25519.bytesAt m a n = List.replicate n 0 := fun e => h' (h.mpr e)
    simp only [h', h'', ↓reduceIte]

end VG.Proof.Xdh
