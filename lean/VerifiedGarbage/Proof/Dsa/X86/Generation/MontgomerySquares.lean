module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.MontgomerySetup
public import VerifiedGarbage.Proof.Dsa.X86.Generation.MontgomeryFrame
import VerifiedGarbage.Proof.Bignum.Math

/-! Repeated calls use the optimized symmetric square and retain the context. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem montgomery_squares {s : State} {base : Addr} {n m E : Nat} (count : Nat)
    (C : Context n m base montgomeryBytes s)
    (room : CallRoom (s.gpr .esp) base montgomeryBytes)
    (hn : 0 < n) (hn' : n ≤ 48) (coprime : Nat.Coprime (2 ^ (64 * n)) m)
    (lt : val32 s.mem base (slot n 4) (2 * n) < m)
    (residue : val32 s.mem base (slot n 4) (2 * n) % m = 2 ^ E * 2 ^ (64 * n) % m) :
    WP isa (montgomerySquares n count) s fun t =>
      Context n m base montgomeryBytes t ∧
      val32 t.mem base (slot n 4) (2 * n) < m ∧
      val32 t.mem base (slot n 4) (2 * n) % m =
        2 ^ (2 ^ count * E) * 2 ^ (64 * n) % m ∧
      MontgomeryFrame base (s.gpr .esp) n 4 s t ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  induction count generalizing s E with
  | zero =>
    exact WP.block_nil ⟨C, lt, by simpa only [Nat.pow_zero, Nat.one_mul] using residue,
      Frame.refl _ _, fun _ _ => rfl, rfl, rfl⟩
  | succ count ih =>
    have modulus : val32 s.mem base (slot n 0) (2 * n) = m := by
      rw [← wordsVal_eq_val32]; exact C.modulus.val
    refine WP.seq (WP.mono (montgomery_ok C.scr room hn hn' (by decide) (by decide)
      (by decide) (by decide) (by rw [modulus]; exact C.inverse) (by rw [modulus]; exact lt))
      fun u ⟨cs, rd, wr, F, bound, value⟩ => ?_)
    rw [modulus] at bound value
    have Cu := montgomery_context_keep C room hn hn' (by decide) (by decide) cs rd wr F
    have roomU : CallRoom (u.gpr .esp) base montgomeryBytes := by
      rw [cs .esp (by decide)]; exact room
    have residueU := VG.Proof.Bignum.mont_sq coprime residue value
    refine WP.mono (ih Cu roomU bound residueU) fun t ⟨Ct, bt, rt, Ft, cst, rdt, wrt⟩ =>
      ⟨Ct, bt, ?_, ?_, fun r hr => (cst r hr).trans (cs r hr), rdt.trans rd, wrt.trans wr⟩
    · rw [rt, show 2 ^ count * (2 * E) = 2 ^ (count + 1) * E by
        rw [Nat.pow_succ]; ac_rfl]
    · rw [cs .esp (by decide)] at Ft
      exact F.trans Ft

end VG.Proof.Dsa.X86.Generation
