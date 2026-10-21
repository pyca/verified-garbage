module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Mem

/-! # Compose verified scratch writes under containing ranges -/

@[expose] public section
namespace VG.Proof.Mont
open VG

theorem Outs.cover {base : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem}
    (h : Outs base rs m m')
    (covered : ∀ r ∈ rs, ∃ R ∈ rs', R.1 ≤ r.1 ∧ r.1 + r.2 ≤ R.1 + R.2) : Outs base rs' m m' := by
  intro x outside
  apply h x
  intro r mem
  obtain ⟨R, member, lo, hi⟩ := covered r mem
  have := outside R member
  omega

theorem Outs.word {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m')
    {d : Nat} (apart : ∀ r ∈ rs, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d) (fit : d + 8 ≤ 2 ^ 64) :
    word m' base d = word m base d := by
  apply Mem.readW_congr
  intro i hi
  apply h
  intro r mem
  have := apart r mem
  rw [ofs_off base (by omega)]
  omega

end VG.Proof.Mont
