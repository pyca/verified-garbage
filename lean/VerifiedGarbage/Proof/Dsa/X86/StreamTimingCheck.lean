module

public import VerifiedGarbage.Impl.Dsa.X86.Stream
public import VerifiedGarbage.Proof.Mont.X86.PowerTiming

/-! # Timing certificates for DSA's two subgroup workspace widths -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.X86 VG.Proof.Mont.X86.Dynamic

/-- Only the source pointer and byte counter are public; all integer buffers
and the modulus remain secret to the checker. The DSA scalar workspace is
1408 bytes and is region zero for this internal routine. -/
def streamTaint : VG.X86.Taint.T :=
  { regs := .ofList [.edi, .esi], flags := false, lens := [1408],
    bases := [(.edi, 0, 0)], slots := [(0, sourcePointer, 4)] }

def streamFetchedTaint : VG.X86.Taint.T :=
  { streamTaint with regs := .ofList [.edi, .esi, .ebp] }

def streamFetchEnd : VG.X86.Taint.T := { streamFetchedTaint with flags := true }

theorem scalarFetch (n : Nat) (hn : n = 3 ∨ n = 4) :
    taint.checkBlock streamTaint (fetchByte n) = some streamFetchEnd := by
  rcases hn with rfl | rfl <;> rfl

theorem scalarCsub (n : Nat) (hn : n = 3 ∨ n = 4) :
    taint.checkBlock streamFetchedTaint
      (VG.Impl.Mont.X86.csub (VG.Impl.Mont.X86.Dynamic.contextMod n)
        (VG.Impl.Mont.X86.Dynamic.slot n 2) (VG.Impl.Mont.X86.Dynamic.slot n 6)) = some streamFetchedTaint := by
  open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic in
  have df : taint.checkBlock streamFetchedTaint (diffs (contextMod n) (slot n 2)) = some streamFetchedTaint := by
    rcases hn with rfl | rfl <;> rfl
  open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic in
  have mask : taint.checkBlock streamFetchedTaint
      [.mov .eax (.mem (sc (slot n 2 + 4 * words (contextMod n)))), .alu .sbb .eax (.imm 0),
        .alu .sbb .eax (.reg .eax), .alu .xor .eax (.imm (-1))] = some streamFetchedTaint := by
    rcases hn with rfl | rfl <;> rfl
  open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic in
  have sl : taint.checkBlock streamFetchedTaint (selects (contextMod n) (slot n 2) (slot n 6)) = some streamFetchedTaint := by
    rcases hn with rfl | rfl <;> rfl
  unfold VG.Impl.Mont.X86.csub
  rw [List.append_assoc, exponent_check_append taint streamFetchedTaint, df]
  dsimp only [Option.bind]
  rw [exponent_check_append taint streamFetchedTaint, mask]
  exact sl

theorem scalarAdd (n b : Nat) (hn : n = 3 ∨ n = 4) (hb : b = 6 ∨ b = 7) (flags : Bool) :
    taint.checkBlock { streamFetchedTaint with flags := flags }
      (VG.Impl.Mont.X86.add (VG.Impl.Mont.X86.Dynamic.contextMod n)
        (VG.Impl.Mont.X86.Dynamic.slot n 2) (VG.Impl.Mont.X86.Dynamic.slot n 6)
        (VG.Impl.Mont.X86.Dynamic.slot n 6) (VG.Impl.Mont.X86.Dynamic.slot n b)) = some streamFetchedTaint := by
  open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic in
  have ch : taint.checkBlock { streamFetchedTaint with flags := flags }
      (chain (contextMod n) .add .adc (slot n 2) (slot n 6) (slot n b)) = some streamFetchedTaint := by
    rcases hn with rfl | rfl <;> rcases hb with rfl | rfl <;> cases flags <;> rfl
  open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic in
  have top : taint.checkBlock streamFetchedTaint
      [.mov .eax (.imm 0), .alu .adc .eax (.imm 0), .store (sc (slot n 2 + 4 * words (contextMod n))) .eax] =
      some streamFetchedTaint := by
    rcases hn with rfl | rfl <;> rfl
  unfold VG.Impl.Mont.X86.add
  rw [List.append_assoc, exponent_check_append taint { streamFetchedTaint with flags := flags }, ch]
  dsimp only [Option.bind]
  rw [exponent_check_append taint streamFetchedTaint, top]
  exact scalarCsub n hn

open VG.Impl.Mont.X86.Dynamic in
theorem scalarDoubles (n : Nat) (hn : n = 3 ∨ n = 4) (k : Nat) :
    taint.checkBlock streamFetchEnd (doubles n (slot n 6) (k + 1)) = some streamFetchedTaint := by
  induction k with
  | zero => exact scalarAdd n 6 hn (.inl rfl) true
  | succ k ih =>
    rw [doubles, exponent_check_append taint streamFetchEnd, ih]
    exact scalarAdd n 6 hn (.inl rfl) false

theorem scalarStreamCore (n : Nat) (hn : n = 3 ∨ n = 4) :
    taint.checkBlock streamTaint (fetchByte n ++ reduceStep n) = some streamFetchedTaint := by
  rw [exponent_check_append taint streamTaint, scalarFetch n hn]
  dsimp only [Option.bind]
  rw [reduceStep, exponent_check_append taint streamFetchEnd, scalarDoubles n hn 7]
  exact scalarAdd n 7 hn (.inr rfl) false

end VG.Proof.Dsa.X86
