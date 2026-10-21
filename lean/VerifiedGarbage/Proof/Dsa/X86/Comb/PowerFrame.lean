module


import VerifiedGarbage.Proof.Dsa.X86.Comb.SelectTable
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
public import VerifiedGarbage.Proof.Mont.X86.CombTableState

/-! The comb loop writes only its digit, masks, accumulator and exponent. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

def rows (e : Nat) : Nat := Spec.Rsa.FixedBaseComb.rows (32*e)
def expWords (e : Nat) : Nat := (5*rows e+31)/32

def powerRanges (n e : Nat) : List (Nat × Nat) :=
  [(4,4),(slot n 1,128),(slot n 1,8*n),(slot n 2,16*n+4),
   (slot n 6,8*n),(slot n 7,8*n),(slot n 8,4*expWords e)]

theorem power_bounds {n e : Nat} (h : Supported n e) :
    0<rows e ∧ rows e<2^32 ∧ 0<expWords e ∧ expWords e≤2*n ∧
    5*rows e≤32*expWords e ∧ slot n 8+4*expWords e≤(layout n e).size ∧
    8≤(layout n e).size := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide

theorem power_preserves_one {n e : Nat} {base : Addr} {s t : Mem} (h : Supported n e)
    (O : Outs base (powerRanges n e) s t) :
    wordsVal t base (slot n 3) n=wordsVal s base (slot n 3) n := by
  rw [wordsVal_eq_val32,wordsVal_eq_val32]
  apply O.val32
  · intro r hr
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    all_goals revert r; decide
  · rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide

theorem power_preserves_table {n e m g : Nat} {base : Addr} {s t : State} (h : Supported n e)
    (hs : Scr s base (layout n e).size)
    (T : VG.Proof.Mont.X86.Comb.TableAt n (context n) m g (32*e) base (fun _ => True) s.mem)
    (O : Outs base (powerRanges n e) s.mem t.mem) :
    VG.Proof.Mont.X86.Comb.TableAt n (context n) m g (32*e) base (fun _ => True) t.mem := by
  apply T.outs (table_layout h) hs O
  intro r hr
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  all_goals revert r; decide

theorem power_context {n e m : Nat} {base : Addr} {s t : State} (h : Supported n e)
    (C : Context n m base (layout n e).size s) (O : Outs base (powerRanges n e) s.mem t.mem)
    (K : Keeps powerClob s t) : Context n m base (layout n e).size t := by
  apply C.outs_keep K (by decide) (by decide) O
  all_goals
    intro r hr
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> revert r <;> decide

end VG.Proof.Dsa.X86.Comb
