module

public import VerifiedGarbage.Proof.Dsa.X86.StreamTimingCheck

/-! # Secret-independent byte reduction for both DSA scalar widths -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Mont.X86.Dynamic

def streamEntryTaint : VG.X86.Taint.T := { streamTaint with regs := .ofList [.edi] }

def streamInitTaint (n : Nat) : VG.X86.Taint.T :=
  { streamTaint with regs := .ofList [.edi, .esi, .eax], slots := [(0, sourcePointer, 4), (0, slot n 6, 8 * n), (0, slot n 7, 8 * n)] }

theorem scalarStreamInit_check (n : Nat) (hn : n = 3 ∨ n = 4) :
    taint.checkBlock streamEntryTaint
      (zeros (slot n 6) (2 * n) ++ zeros (slot n 7) (2 * n) ++ ([.mov .esi (.imm 0)] : List Instr)) =
      some (streamInitTaint n) := by
  rcases hn with rfl | rfl <;> rfl

theorem scalarStreamStep_check (n len : Nat) (hn : n = 3 ∨ n = 4) :
    taint.checkBlock streamTaint (streamStep n len) = some streamFetchEnd := by
  unfold streamStep
  rw [exponent_check_append taint streamTaint, scalarStreamCore n hn]
  rfl

theorem reduceStream_constantTime (n len : Nat) (hn : n = 3 ∨ n = 4) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree streamEntryTaint) (reduceStream n len) := by
  by_cases hz : len = 0
  · refine VG.Taint.constantTime (A := taint) streamEntryTaint (fun _ _ _ _ h => h)
      (hc := .seq streamTaint (.block []) (.block [])) ?_
    unfold reduceStream
    rw [ite_eq_left hz]
    simp only [VG.Taint.check, VG.Taint.checkChunks]
    rw [scalarStreamInit_check n hn]
    rcases hn with rfl | rfl <;> rfl
  · refine VG.Taint.constantTime (A := taint) streamEntryTaint (fun _ _ _ _ h => h)
      (hc := .seq streamTaint (.block []) (.loop streamTaint (.block []))) ?_
    unfold reduceStream
    rw [ite_eq_right hz]
    have loop : VG.Taint.check taint streamTaint (.loop (.block (streamStep n len)) .ne)
        (.loop streamTaint (.block [])) = some streamFetchEnd := by
      change (if taint.le streamTaint streamTaint then
        (taint.checkBlock streamTaint (streamStep n len)).bind
          (fun t => if taint.le streamTaint t && taint.condPub t .ne then some t else none) else none) = _
      rw [scalarStreamStep_check n len hn]
      rfl
    have initLe : taint.le streamTaint (streamInitTaint n) = true := by rcases hn with rfl | rfl <;> rfl
    have check : VG.Taint.check taint streamEntryTaint
        (.seq (.block (zeros (slot n 6) (2 * n) ++ zeros (slot n 7) (2 * n) ++ [.mov .esi (.imm 0)]))
          (.loop (.block (streamStep n len)) .ne))
        (.seq streamTaint (.block []) (.loop streamTaint (.block []))) = some streamFetchEnd :=
      exponent_check_seq taint (scalarStreamInit_check n hn) initLe loop
    rw [check]
    rfl

end VG.Proof.Dsa.X86
