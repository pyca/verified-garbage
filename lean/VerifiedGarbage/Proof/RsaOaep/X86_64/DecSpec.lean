import VerifiedGarbage.Proof.RsaOaep.X86_64.DecLoops

/-!
# RSAES-OAEP decryption on x86-64: the masks and the decoding

The comparison of `lHash'` with `lHash` the code accumulates without
branches is zero iff they are equal and `EM[0]` is zero (`accL_eq_zero`).
The scan's masks are `Proof/RsaOaep/Scan.lean`'s (`scanS`): `rdx`, `rsi` and
`rcx` after the scan of `T`.
-/

namespace VG.Proof.RsaOaep.X86_64

open VG VG.Impl.RsaOaep.X86_64
open VG.Proof.MlKem.X86_64 (ifp ifn)

/-! ## Masks -/

/-- `EM[0] ∨ ⋁ (lHash ⊕ lHash')` is zero iff `EM[0]` is zero and they agree. -/
theorem accL_eq_zero (V : Nat → Byte) (D : Nat) :
    ∀ j, accL V D j = 0 ↔ V oEm = 0 ∧ ∀ i < j, V (oLh + i) = V (oEm + 1 + D + i)
  | 0 => by simp only [accL, zx_eq_zero]; exact ⟨fun h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun h => h.1⟩
  | j + 1 => by
    rw [accL, or_eq_zero, accL_eq_zero V D j, xor_eq_zero, zx_inj]
    constructor
    · rintro ⟨⟨h0, h⟩, h'⟩
      exact ⟨h0, fun i hi => if hij : i < j then h i hij else by rw [show i = j by omega]; exact h'⟩
    · rintro ⟨h0, h⟩
      exact ⟨⟨h0, fun i hi => h i (by omega)⟩, h j (by omega)⟩

end VG.Proof.RsaOaep.X86_64
