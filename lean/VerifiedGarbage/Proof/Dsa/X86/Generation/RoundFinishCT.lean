module
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundMinus
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundCTState
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundArithmeticCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundTestsCT

/-! # Rebuilding minus one preserves the round's public residue and count -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

structure RoundBaseAt (n : Nat) (p : RoundPublic) (s : State) : Prop where
  context : Context n p.modulus p.base p.size s
  width : n ≤ 48
  room : roundStatus + 4 ≤ p.size
  one : wordsVal s.mem p.base (slot n 3) n = 1
  r2 : wordsVal s.mem p.base (slot n 4) n = 2 ^ (128 * n) % p.modulus
  count : s.mem.readW (off p.base roundCount) 32 = BitVec.ofNat 32 p.count
  bound : p.count < 2 ^ 32

def RoundFinishAt (n : Nat) (p : RoundPublic) (s : State) : Prop :=
  RoundBaseAt n p s ∧ wordsVal s.mem p.base (slot n 6) n = p.value

theorem roundMinusOne_phase_ok {n : Nat} {p : RoundPublic} {s : State} (R : RoundFinishAt n p s) :
    WP isa (roundMinusOne n) s (RoundAt n p) := by
  refine WP.mono (roundMinusOne_ok R.1.context R.1.one) fun t ⟨C, minus, O, _⟩ => ?_
  have val (j : Nat) (hj : j < 8) : wordsVal t.mem p.base (slot n j) n = wordsVal s.mem p.base (slot n j) n := by
    have sep := slot_sep (n := n) (i := j) (j := 8) (by omega)
    have before := slot_bound (n := n) (by omega : j < 9)
    have upto : slot n j ≤ slot n 8 := by unfold slot; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
    have fit := R.1.context.size_le
    have nw := R.1.context.scr.nowrap
    simp only [stride] at sep before
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact O.val32 (by omega) (by omega)
  have count : t.mem.readW (off p.base roundCount) 32 = s.mem.readW (off p.base roundCount) 32 := by
    apply BitVec.eq_of_toNat_eq
    exact O.w32 (by have := R.1.width; simp only [slot, stride, roundCount]; omega) (by decide)
  exact ⟨⟨C, R.1.width, R.1.room, (val 3 (by decide)).trans R.1.one,
    (val 4 (by decide)).trans R.1.r2, minus⟩, (val 6 (by decide)).trans R.2, count.trans R.1.count, R.1.bound⟩

theorem roundFinish_ct (n : Nat) :
    RelCT isa (Two (RoundFinishAt n)) (roundFinish n) (fun _ _ => True) := by
  refine RelCT.seq (two_post ((roundMinusOne_ct n).mono ?_ (fun _ _ h => h))
    (fun _ _ R => roundMinusOne_phase_ok R)) (roundTests_ct n)
  rintro s t ⟨p, hs, ht⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  exact BitVec.eq_of_toNat_eq (hs.1.context.scr.edi_toNat.trans ht.1.context.scr.edi_toNat.symm)
end VG.Proof.Dsa.X86.Generation
