module

public import VerifiedGarbage.Proof.Bignum.X86.SparseStep
public import VerifiedGarbage.Proof.Mont.X86.ContextMath

/-! # The exponentiation loop that ends after the exponent's top bit -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86.PublicContext

/-- After some iterations from `s`: the result `y` and the base `b` in
Montgomery form, with `y * b ^ e`, for what is left `e` of the exponent,
still the target. -/
structure SparseInv (n bytes m target : Nat) (base : Addr) (s t : State) : Prop where
  context : Context n m base bytes t
  value : ∃ y b,
    wordsVal t.mem base (slot n 7) n = y * 2 ^ (64 * n) % m ∧
    wordsVal t.mem base (slot n 6) n = b * 2 ^ (64 * n) % m ∧
    (y * b ^ val32 t.mem base 128 2) % m = target
  mem : Outs base (exponentRanges n) s.mem t.mem
  keeps : Keeps clob s t

theorem sparseLoop_ok {n bytes m a y : Nat} {base : Addr} {s : State}
    (h : Context n m base bytes s)
    (hy : wordsVal s.mem base (slot n 7) n = y * 2 ^ (64 * n) % m)
    (hb : wordsVal s.mem base (slot n 6) n = a * 2 ^ (64 * n) % m) :
    WP isa (.loop (sparseRound n) .ne) s fun t =>
      SparseInv n bytes m (y * a ^ val32 s.mem base 128 2 % m) base s t ∧
        val32 t.mem base 128 2 = 0 := by
  let target := y * a ^ val32 s.mem base 128 2 % m
  refine WP.loop (M := isa)
    (fun k t => val32 t.mem base 128 2 = k ∧ SparseInv n bytes m target base s t) ?_
    (val32 s.mem base 128 2) s ⟨rfl, h, ⟨y, a, hy, hb, rfl⟩, Outs.refl _ _ _, Keeps.refl _ _⟩
  rintro k t ⟨rfl, I⟩
  obtain ⟨y', b, Y, B, V⟩ := I.value
  refine WP.mono (sparseRound_ok I.context Y B) fun u ⟨C, Y', B', E', Z, O, K⟩ => ?_
  have next : SparseInv n bytes m target base s u := by
    refine ⟨C, ⟨_, _, Y', B', ?_⟩, I.mem.trans O, I.keeps.trans K⟩
    rw [E', exponent_step_value]
    exact V
  by_cases done : val32 t.mem base 128 2 / 2 = 0
  · refine .inl ⟨?_, next, by rw [E', done]⟩
    simp only [eval, Z, done, decide_true, Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, val32 u.mem base 128 2, by rw [E']; omega, rfl, next⟩
    simp only [eval, Z, decide_eq_false done, Option.map_some, Bool.not_false]

theorem SparseInv.finished {n bytes m target : Nat} {base : Addr} {s t : State}
    (I : SparseInv n bytes m target base s t) (hz : val32 t.mem base 128 2 = 0) :
    wordsVal t.mem base (slot n 7) n = target * 2 ^ (64 * n) % m := by
  obtain ⟨y, b, Y, _, V⟩ := I.value
  rw [hz, Nat.pow_zero, Nat.mul_one] at V
  rw [Y, Nat.mul_mod y, V, Nat.mul_mod_mod]

end VG.Proof.Bignum.X86.PublicContext
