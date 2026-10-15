module

public import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Proof.Framework.NativeHintOps
public import VerifiedGarbage.TCB.Arm.Target

/-! Executable ARMv7 taint operations for the native hint search, separated
from their soundness proofs (`Arm/Taint.lean`, `Arm/TaintMono.lean`). Each
function computes exactly what its counterpart in the checked domain
computes (`Taint.stepKD`, `Taint.meet`, `Taint.leK`, `Taint.leS`,
`Taint.callStep`), so a hint found here is the one the interpreted search
(`Taint.hintOfSize`) finds; nothing here needs to be sound, since the kernel
still checks the hint with the checked domain. -/

@[expose] public section

namespace VG.NativeHints.Arm
open VG.Arm

deriving instance Lean.ToExpr for Reg

instance : RegIdx Reg := ⟨Reg.ctorIdx, fun {a b} h => by rw [← Reg.ofNat_ctorIdx a, h, Reg.ofNat_ctorIdx]⟩

/-- `VG.Arm.Taint.T`, field for field. -/
structure T where
  regs : RegSet Reg
  flags : Bool
  lens : List Nat := []
  bases : List (Reg × Nat) := []
  slots : List (Nat × Nat × Nat) := []
  argLen : Nat := 0
  argBases : List (Nat × Nat) := []
  deriving Lean.ToExpr

def pub (τ : T) (r : Reg) : Bool := τ.regs.mem r

def regEq (a b : Reg) : Bool := Nat.beq a.ctorIdx b.ctorIdx

def setK (τ : T) (r : Reg) (p : Bool) : RegSet Reg := bif p then τ.regs.insert r else τ.regs.erase r

def killK (τ : T) (d : Reg) : List (Reg × Nat) := τ.bases.filter fun p => !regEq p.1 d

def op2Pub (τ : T) : Op2 → Bool
  | .imm _ => true
  | .reg r | .shifted r _ _ => pub τ r

def addrOfK (τ : T) (n : Reg) (off : Nat) : Option (Nat × Nat) :=
  (τ.bases.find? fun p => regEq p.1 n).map fun p => (p.2, off)

def slotPubK (τ : T) (n : Reg) (off w : Nat) : Bool :=
  match addrOfK τ n off with
  | some (i, d) =>
    τ.slots.any fun sl => Nat.beq sl.1 i && Nat.ble sl.2.1 d && Nat.ble (d + w) (sl.2.1 + sl.2.2)
  | none => false

def movBasesK (τ : T) (d : Reg) : Op2 → List (Reg × Nat)
  | .reg r => killK τ d ++ ((τ.bases.filter fun p => regEq p.1 r).map fun p => (d, p.2))
  | _ => killK τ d

def mem3 (a : Nat × Nat × Nat) (l : List (Nat × Nat × Nat)) : Bool :=
  l.any fun b => Nat.beq a.1 b.1 && Nat.beq a.2.1 b.2.1 && Nat.beq a.2.2 b.2.2

def storeSlotsKD (τ : T) (n : Reg) (off w : Nat) (p : Bool) : List (Nat × Nat × Nat) :=
  match addrOfK τ n off with
  | some (i, d) =>
    bif Nat.ble (d + w) (τ.lens.getD i 0) then
      bif p then (bif mem3 (i, d, w) τ.slots then τ.slots else (i, d, w) :: τ.slots)
      else τ.slots.filter (fun sl => p || !Nat.beq sl.1 i || Nat.ble (d + w) sl.2.1 ||
        Nat.ble (sl.2.1 + sl.2.2) d)
    else bif p then τ.slots else []
  | none => bif p then τ.slots else []

def storeStepKD (τ : T) (n : Reg) (off w : Nat) (p : Bool) : Option T :=
  bif pub τ n then some { τ with slots := storeSlotsKD τ n off w p } else none

def spBasesK (τ : T) (t : Reg) (off : Nat) : List (Reg × Nat) :=
  killK τ t ++ ((τ.argBases.filter fun p => Nat.beq p.1 off).map fun p => (t, p.2))

/-- `Taint.stepKD`. -/
def step (τ : T) : Instr → Option T
  | .mov d op2 => some { τ with regs := setK τ d (op2Pub τ op2), bases := movBasesK τ d op2 }
  | .dp _ d n op2 => some { τ with regs := setK τ d (pub τ n && op2Pub τ op2), bases := killK τ d }
  | .adds d n op2 | .subs d n op2 =>
    let p := pub τ n && op2Pub τ op2
    some { τ with regs := setK τ d p, flags := p, bases := killK τ d }
  | .adc d n op2 =>
    some { τ with regs := setK τ d (pub τ n && op2Pub τ op2 && τ.flags), bases := killK τ d }
  | .cmp n op2 => some { τ with flags := pub τ n && op2Pub τ op2 }
  | .movw d _ => some { τ with regs := setK τ d true, bases := killK τ d }
  | .adrSym d _ => some { τ with regs := setK τ d false, bases := killK τ d }
  | .addSp d _ => some { τ with regs := setK τ d (decide (0 < τ.argLen)), bases := killK τ d }
  | .movt d _ => some { τ with regs := setK τ d (pub τ d), bases := killK τ d }
  | .rev d m => some { τ with regs := setK τ d (pub τ m), bases := killK τ d }
  | .mul d n m => some { τ with regs := setK τ d (pub τ n && pub τ m), bases := killK τ d }
  | .ldr t n off =>
    bif pub τ n then some { τ with regs := setK τ t (slotPubK τ n off 4), bases := killK τ t } else none
  | .str t n off => storeStepKD τ n off 4 (pub τ t)
  | .ldrb t n _ => bif pub τ n then some { τ with regs := setK τ t false, bases := killK τ t } else none
  | .strb t n off => storeStepKD τ n off 1 (pub τ t)
  | .ldrSp t off =>
    bif Nat.ble (off + 4) τ.argLen then some { τ with regs := setK τ t true, bases := spBasesK τ t off }
    else none
  | .push _ | .pop .. | .alloc _ | .free _ => none

/-- `Taint.meet`. -/
def meet (τ₁ τ₂ : T) : T where
  regs := τ₁.regs.inter τ₂.regs
  flags := τ₁.flags && τ₂.flags
  lens := if τ₁.lens = τ₂.lens then τ₁.lens else []
  bases := τ₁.bases.filter (τ₂.bases.contains ·)
  slots := if τ₁.lens = τ₂.lens then τ₁.slots.filter (τ₂.slots.contains ·) else []
  argLen := if τ₁.argLen = τ₂.argLen then τ₁.argLen else 0
  argBases := if τ₁.argLen = τ₂.argLen then τ₁.argBases.filter (τ₂.argBases.contains ·) else []

def memB (a : Reg × Nat) (l : List (Reg × Nat)) : Bool := l.any fun b => regEq a.1 b.1 && Nat.beq a.2 b.2

def mem2 (a : Nat × Nat) (l : List (Nat × Nat)) : Bool := l.any fun b => Nat.beq a.1 b.1 && Nat.beq a.2 b.2

/-- `Taint.leK`, the order of `VG.Arm.taint`. -/
def leK (τ σ : T) : Bool :=
  τ.regs.subset σ.regs && (!τ.flags || σ.flags) && τ.lens == σ.lens &&
    τ.bases.all (memB · σ.bases) && τ.slots.all (mem3 · σ.slots) && Nat.beq τ.argLen σ.argLen &&
    τ.argBases.all (mem2 · σ.argBases)

def fnK (l : List (Reg × Nat)) : Bool :=
  l.all fun p => l.all fun q => !regEq p.1 q.1 || Nat.beq p.2 q.2

def fnAK (l : List (Nat × Nat)) : Bool :=
  l.all fun p => l.all fun q => !Nat.beq p.1 q.1 || Nat.beq p.2 q.2

/-- `Taint.leS`, the order of `VG.Arm.taintS`. -/
def leS (τ σ : T) : Bool :=
  τ.regs.subset σ.regs && (!τ.flags || σ.flags) && (τ.lens == σ.lens || (τ.lens.isEmpty && τ.slots.isEmpty)) &&
    τ.bases.all (memB · σ.bases) && τ.slots.all (mem3 · σ.slots) &&
    (Nat.beq τ.argLen σ.argLen || (Nat.beq τ.argLen 0 && τ.argBases.isEmpty)) &&
    τ.argBases.all (mem2 · σ.argBases) && fnK σ.bases && fnAK σ.argBases

def callKeeps (r : Reg) : Bool := r != .lr && r != .r12

/-- `Taint.callStep`. -/
def callStep (τ : T) : T :=
  { τ with
    regs := (τ.regs.erase .lr).erase .r12
    flags := false
    bases := τ.bases.filter (callKeeps ·.1) }

/-- The operations of `VG.Arm.taint` (`le := leK`) or `VG.Arm.taintS` (`le := leS`). -/
def hintOps (le : T → T → Bool) : VG.NativeHintOps isa where
  T := T
  step := step
  condPub τ _ := τ.flags
  meet := meet
  le := le
  call τ := some (callStep τ)
  ret τ := some τ
  push _ _ := none
  pop _ _ := none

end VG.NativeHints.Arm

namespace VG.NativeHints.Arm.provider
/-- Untrusted native hints for `VG.Arm.taint`; `Taint.check` still checks them. -/
def hintOfSize := VG.NativeHintOps.hintOfSize (VG.NativeHints.Arm.hintOps VG.NativeHints.Arm.leK)
def hintWeakOfSize := VG.NativeHintOps.hintWeakOfSize (VG.NativeHints.Arm.hintOps VG.NativeHints.Arm.leK)
/-- The same, for `VG.Arm.taintS`. -/
def hintOfSizeS := VG.NativeHintOps.hintOfSize (VG.NativeHints.Arm.hintOps VG.NativeHints.Arm.leS)
def hintWeakOfSizeS := VG.NativeHintOps.hintWeakOfSize (VG.NativeHints.Arm.hintOps VG.NativeHints.Arm.leS)
end VG.NativeHints.Arm.provider
