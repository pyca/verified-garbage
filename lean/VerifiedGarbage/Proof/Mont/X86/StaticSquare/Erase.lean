module

public import VerifiedGarbage.Impl.Mont.X86.StaticSquare
public import VerifiedGarbage.Proof.Framework.X86.TaintErase

/-! # Erasing the fixed square before constructing its product instructions -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare.Erase

open VG VG.X86 VG.Impl.Mont.X86.Rt

def aprod : List Instr := KList.map Instr.erase (VG.Impl.Mont.X86.Rt.StaticSquare.aprod 0 0)
def qprod : List Instr := KList.map Instr.erase (VG.Impl.Mont.X86.Rt.StaticSquare.qprod 0 0)

theorem erase_aprod (i j : Nat) : KList.map Instr.erase (VG.Impl.Mont.X86.Rt.StaticSquare.aprod i j) = aprod := by rfl
theorem erase_qprod (i j : Nat) : KList.map Instr.erase (VG.Impl.Mont.X86.Rt.StaticSquare.qprod i j) = qprod := by rfl

def inputTerm (N k i : Nat) : List Instr :=
  bif Nat.ble i k && (Nat.blt (k - i) N && Nat.blt i (k - i)) then aprod else []
def reductionTerm (N k j : Nat) : List Instr :=
  bif Nat.blt j k && Nat.blt (k - j) N then qprod else []
/-- A direct recursor avoids the library flat-map evaluator in the kernel. -/
def products (f : Nat → List Instr) (xs : List Nat) : List Instr :=
  List.rec [] (fun i _ rest => KList.append (f i) rest) xs

theorem products_eq (f : Nat → List Instr) (xs : List Nat) : products f xs = xs.flatMap f := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    change KList.append (f i) (products f xs) = f i ++ xs.flatMap f
    rw [KList.append_eq, ih]

def inputProducts (N k count : Nat) : List Instr :=
  products (inputTerm N k) (List.range count)
def reductionProducts (N k count : Nat) : List Instr :=
  products (reductionTerm N k) (List.range count)

theorem erase_inputTerm (N k i : Nat) :
    KList.map Instr.erase (VG.Impl.Mont.X86.Rt.StaticSquare.inputTerm N k i) = inputTerm N k i := by
  unfold VG.Impl.Mont.X86.Rt.StaticSquare.inputTerm inputTerm
  simp only [Bool.cond_eq_ite, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]
  split
  · exact erase_aprod _ _
  · rfl

theorem erase_reductionTerm (N k j : Nat) :
    KList.map Instr.erase (VG.Impl.Mont.X86.Rt.StaticSquare.reductionTerm N k j) = reductionTerm N k j := by
  unfold VG.Impl.Mont.X86.Rt.StaticSquare.reductionTerm reductionTerm
  simp only [Bool.cond_eq_ite, Bool.and_eq_true, Nat.blt_eq]
  split
  · exact erase_qprod _ _
  · rfl

theorem erase_inputProducts (N k count : Nat) :
    KList.map Instr.erase (VG.Impl.Mont.X86.Rt.StaticSquare.inputProducts N k count) = inputProducts N k count := by
  simp only [VG.Impl.Mont.X86.Rt.StaticSquare.inputProducts, inputProducts, products_eq, KList.map_eq, List.map_flatMap]
  congr 1
  funext i
  exact (KList.map_eq _ _).symm.trans (erase_inputTerm N k i)

theorem erase_reductionProducts (N k count : Nat) :
    KList.map Instr.erase (VG.Impl.Mont.X86.Rt.StaticSquare.reductionProducts N k count) = reductionProducts N k count := by
  simp only [VG.Impl.Mont.X86.Rt.StaticSquare.reductionProducts, reductionProducts, products_eq, KList.map_eq, List.map_flatMap]
  congr 1
  funext j
  exact (KList.map_eq _ _).symm.trans (erase_reductionTerm N k j)

/-- Right-nested `KList.append`s, which the kernel evaluates faster than `++`. -/
def input (N k : Nat) : List Instr :=
  bif Nat.blt k (2 * N - 1) then
    KList.append (KList.map Instr.erase (ptr .edi argA .eax)) (KList.append (inputProducts N k N)
      (KList.append (KList.map Instr.erase VG.Impl.Mont.X86.Rt.StaticSquare.double)
        (bif Nat.beq (k % 2) 0 then aprod else [])))
  else []

theorem erase_input (N k : Nat) : KList.map Instr.erase (VG.Impl.Mont.X86.Rt.StaticSquare.input N k) = input N k := by
  unfold VG.Impl.Mont.X86.Rt.StaticSquare.input input
  simp only [Bool.cond_eq_ite, Nat.blt_eq, Nat.beq_eq]
  split
  · simp only [KList.map_eq, KList.append_eq, List.map_append, List.append_assoc]
    rw [← KList.map_eq Instr.erase (VG.Impl.Mont.X86.Rt.StaticSquare.inputProducts N k N),
      erase_inputProducts]
    split
    · simp only [← KList.map_eq, erase_aprod]
    · rfl
  · rfl

def digit (N k : Nat) : List Instr :=
  bif Nat.blt k N then KList.map Instr.erase (VG.Impl.Mont.X86.Rt.StaticSquare.digit 1 0)
  else KList.map Instr.erase (VG.Impl.Mont.X86.Rt.StaticSquare.digit 0 0)

theorem erase_digit (N k : Nat) : KList.map Instr.erase (VG.Impl.Mont.X86.Rt.StaticSquare.digit N k) = digit N k := by
  unfold VG.Impl.Mont.X86.Rt.StaticSquare.digit digit
  simp only [Bool.cond_eq_ite, Nat.blt_eq]
  split <;> rfl

theorem erase_finish (N : Nat) :
    KList.map Instr.erase (VG.Impl.Mont.X86.Rt.StaticSquare.finish N) = KList.map Instr.erase (VG.Impl.Mont.X86.Rt.StaticSquare.finish 0) := by rfl

def column (N k : Nat) : Prog isa := VG.Impl.Mont.X86.Rt.StaticSquare.seqs [
  .block (KList.map Instr.erase VG.Impl.Mont.X86.Rt.StaticSquare.clear), .block (input N k),
  .block (KList.map Instr.erase (ptr .edi argS .eax ++ ptr .ebp argM .eax)),
  .block (KList.map Instr.erase VG.Impl.Mont.X86.Rt.StaticSquare.carryIn), .block (reductionProducts N k N),
  .block (digit N k), .block (KList.map Instr.erase VG.Impl.Mont.X86.Rt.StaticSquare.carryOut)]

theorem erase_column (N k : Nat) : Code.erase (VG.Impl.Mont.X86.Rt.StaticSquare.column N k) = column N k := by
  simp only [VG.Impl.Mont.X86.Rt.StaticSquare.column, column, VG.Impl.Mont.X86.Rt.StaticSquare.seqs, VG.Impl.Mont.X86.Rt.Square.seqs, Code.erase,
    erase_input, erase_reductionProducts, erase_digit]

def columns (N : Nat) : Nat → Nat → Prog isa
  | _, 0 => .block []
  | k, count + 1 => .seq (column N k) (columns N (k + 1) count)

theorem erase_columns (N k count : Nat) : Code.erase (VG.Impl.Mont.X86.Rt.StaticSquare.columns N k count) = columns N k count := by
  induction count generalizing k with
  | zero => rfl
  | succ count ih =>
    simp only [VG.Impl.Mont.X86.Rt.StaticSquare.columns, columns, Code.erase, erase_column, ih]

def front (N : Nat) : Prog isa := VG.Impl.Mont.X86.Rt.StaticSquare.seqs [
  .block (KList.map Instr.erase VG.Impl.Mont.X86.Rt.StaticSquare.init), columns N 0 (2 * N),
  .block (KList.map Instr.erase (VG.Impl.Mont.X86.Rt.StaticSquare.finish 0))]

theorem erase_front (N : Nat) : Code.erase (VG.Impl.Mont.X86.Rt.StaticSquare.front N) = front N := by
  simp only [VG.Impl.Mont.X86.Rt.StaticSquare.front, front, VG.Impl.Mont.X86.Rt.StaticSquare.seqs, VG.Impl.Mont.X86.Rt.Square.seqs, Code.erase,
    erase_columns, erase_finish]

/-- The same erased square, constructed from shared erased products. -/
def square (N : Nat) : Prog isa := VG.Impl.Mont.X86.Rt.StaticSquare.seqs [front N, Code.erase subM,
  .block (KList.map Instr.erase mask), Code.erase select, .block (KList.map Instr.erase restoreRegs)]

theorem erase_square (N : Nat) : Code.erase (VG.Impl.Mont.X86.Rt.StaticSquare.square N) = square N := by
  simp only [VG.Impl.Mont.X86.Rt.StaticSquare.square, square, VG.Impl.Mont.X86.Rt.StaticSquare.seqs, VG.Impl.Mont.X86.Rt.Square.seqs, Code.erase, erase_front]

end VG.Proof.Mont.X86.StaticSquare.Erase
