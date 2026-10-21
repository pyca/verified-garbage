module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Omega

/-! # Enlarging the writable ranges of an array operation -/

@[expose] public section
namespace VG.Proof.Rsa
open VG VG.Proof.Mont

theorem outs_cover {base : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem}
    (h : Outs base rs m m')
    (cover : ∀ r ∈ rs, ∃ t ∈ rs', t.1 ≤ r.1 ∧ r.1 + r.2 ≤ t.1 + t.2) : Outs base rs' m m' := by
  intro x hx
  apply h x
  intro r hr
  obtain ⟨t, ht, lo, hi⟩ := cover r hr
  have := hx t ht
  omega
end VG.Proof.Rsa
