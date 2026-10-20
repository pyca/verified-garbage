module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.MillerRabinMath
public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundEffects
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundStep

/-! # The squaring loop consumes its bounded count and returns the specified result -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation
open VG.Proof.Ecdsa.X86

structure RoundLoopInv (s : State) (base : Addr) (n m size k left : Nat) (t : State) : Prop where
  ready : RoundReady base n m size t
  positive : 0 < left
  bound : left < 2 ^ 32
  count : t.mem.readW (off base roundCount) 32 = BitVec.ofNat 32 left
  result : publicMrSquares m k (wordsVal s.mem base (slot n 6) n) =
    publicMrSquares m left (wordsVal t.mem base (slot n 6) n)
  mem : Outs base (roundWrites n) s.mem t.mem
  keeps : Keeps clob s t

theorem roundLoop_ok {base : Addr} {n m size k : Nat} {s : State} (R : RoundReady base n m size s)
    (hk : 1 ≤ k) (bound : k < 2 ^ 32) (count : s.mem.readW (off base roundCount) 32 = BitVec.ofNat 32 k) :
    WP isa (.loop (roundStep n) .ne) s fun t => RoundReady base n m size t ∧
      t.mem.readW (off base roundStatus) 32 = mask32 (publicMrSquares m k (wordsVal s.mem base (slot n 6) n) = true) ∧
      Outs base (roundWrites n) s.mem t.mem ∧ Keeps clob s t := by
  refine WP.loop (M := isa) (RoundLoopInv s base n m size k) ?_ k s
    ⟨R, hk, bound, count, rfl, Outs.refl _ _ _, Keeps.refl _ _⟩
  intro left t I
  refine WP.mono (roundStep_ok I.ready I.positive I.bound I.count) fun u ⟨_, _, Ru, Ou, Ku, step⟩ => ?_
  rcases step with ⟨zf, status⟩ | ⟨zf, more, count, result⟩
  · exact .inl ⟨by simp only [eval, zf, Option.map_some, Bool.not_true],
      Ru, by rw [I.result]; exact status, I.mem.trans Ou, I.keeps.trans Ku⟩
  · exact .inr ⟨by simp only [eval, zf, Option.map_some, Bool.not_false], left - 1, by omega,
      Ru, by omega, by have := I.bound; omega, count, I.result.trans result, I.mem.trans Ou, I.keeps.trans Ku⟩
end VG.Proof.Dsa.X86.Generation
