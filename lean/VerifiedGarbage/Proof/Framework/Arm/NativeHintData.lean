module

public import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Proof.Framework.NativeHintOps
public import VerifiedGarbage.TCB.Arm.Isa
meta import VerifiedGarbage.Proof.Framework.RegSet
meta import VerifiedGarbage.Proof.Framework.NativeHintOps
meta import VerifiedGarbage.TCB.Arm.Isa

/-! Executable ARMv7 taint operations for the compiled hint search
(`native_taint_decide`), separated from their soundness proofs: a copy of
`Arm.taint` (`Proof/Framework/Arm/Taint.lean`), field for field, whose hints
are renamed to the checked domain's constructors and checked by the kernel
like any other (`Taint.check`). A difference from `Arm.taint` can only make
the check fail. -/

@[expose] public section

namespace VG.NativeHints.Arm
open VG.Arm

deriving instance Lean.ToExpr for Reg

instance : RegIdx Reg := ⟨Reg.ctorIdx, fun {a b} h => by rw [← Reg.ofNat_ctorIdx a, h, Reg.ofNat_ctorIdx]⟩

/-- `Arm.Taint.T`, field for field. -/
structure T where
  regs : RegSet Reg
  flags : Bool
  lens : List Nat := []
  bases : List (Reg × Nat) := []
  slots : List (Nat × Nat × Nat) := []
  argLen : Nat := 0
  argBases : List (Nat × Nat) := []
  deriving DecidableEq, Lean.ToExpr

def pub (τ : T) (r : Reg) : Bool := τ.regs.mem r

def set (τ : T) (r : Reg) (p : Bool) : RegSet Reg :=
  if p then τ.regs.insert r else τ.regs.erase r

def kill (τ : T) (d : Reg) : List (Reg × Nat) := τ.bases.filter (·.1 != d)

def op2Pub (τ : T) : Op2 → Bool
  | .imm _ => true
  | .reg r | .shifted r _ _ => pub τ r

def addrOf (τ : T) (n : Reg) (off : Nat) : Option (Nat × Nat) :=
  (τ.bases.find? (·.1 == n)).map fun p => (p.2, off)

def slotPub (τ : T) (n : Reg) (off w : Nat) : Bool :=
  match addrOf τ n off with
  | some (i, d) => τ.slots.any fun sl => sl.1 == i && sl.2.1 ≤ d && d + w ≤ sl.2.1 + sl.2.2
  | none => false

def movBases (τ : T) (d : Reg) : Op2 → List (Reg × Nat)
  | .reg r => kill τ d ++ (τ.bases.filter (·.1 == r)).map fun p => (d, p.2)
  | _ => kill τ d

/-- `Arm.Taint.touches`. -/
def touches (s x : Nat × Nat × Nat) : Bool :=
  s.1 == x.1 && s.2.1 ≤ x.2.1 + x.2.2 && x.2.1 ≤ s.2.1 + s.2.2

/-- `Arm.Taint.joinSlot`. -/
def joinSlot (s x : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (s.1, min s.2.1 x.2.1, max (s.2.1 + s.2.2) (x.2.1 + x.2.2) - min s.2.1 x.2.1)

/-- `Arm.Taint.mergeSlot`: the slots with `x`, merged with those it touches. -/
def mergeSlot (x : Nat × Nat × Nat) : List (Nat × Nat × Nat) → List (Nat × Nat × Nat)
  | [] => [x]
  | s :: l => if touches s x then mergeSlot (joinSlot s x) l else s :: mergeSlot x l

/-- `Arm.Taint.containsSlot`. -/
def containsSlot (s x : Nat × Nat × Nat) : Bool :=
  s.1 == x.1 && s.2.1 ≤ x.2.1 && x.2.1 + x.2.2 ≤ s.2.1 + s.2.2

/-- `Arm.Taint.cutSlot`: the parts of `sl` outside the bytes `d` to `d + w` of region `i`. -/
def cutSlot (i d w : Nat) (sl : Nat × Nat × Nat) : List (Nat × Nat × Nat) :=
  if sl.1 != i || d + w ≤ sl.2.1 || sl.2.1 + sl.2.2 ≤ d then [sl]
  else (if sl.2.1 < d then [(i, sl.2.1, d - sl.2.1)] else []) ++
    (if d + w < sl.2.1 + sl.2.2 then [(i, d + w, sl.2.1 + sl.2.2 - (d + w))] else [])

/-- `Arm.Taint.cutSlots`. -/
def cutSlots (i d w : Nat) : List (Nat × Nat × Nat) → List (Nat × Nat × Nat)
  | [] => []
  | sl :: l => cutSlot i d w sl ++ cutSlots i d w l

/-- `Arm.Taint.interSlot`: the bytes of both slots, if any. -/
def interSlot (x z : Nat × Nat × Nat) : List (Nat × Nat × Nat) :=
  if x.1 == z.1 && max x.2.1 z.2.1 < min (x.2.1 + x.2.2) (z.2.1 + z.2.2) then
    [(x.1, max x.2.1 z.2.1, min (x.2.1 + x.2.2) (z.2.1 + z.2.2) - max x.2.1 z.2.1)]
  else []

/-- `Arm.Taint.interAll`. -/
def interAll (x : Nat × Nat × Nat) : List (Nat × Nat × Nat) → List (Nat × Nat × Nat)
  | [] => []
  | z :: l => interSlot x z ++ interAll x l

/-- `Arm.Taint.interSlots`. -/
def interSlots : List (Nat × Nat × Nat) → List (Nat × Nat × Nat) → List (Nat × Nat × Nat)
  | [], _ => []
  | x :: l, l₂ => interAll x l₂ ++ interSlots l l₂

/-- `Arm.Taint.storeSlotsKM`: the slots after a store, the public bytes merged into their runs. -/
def storeSlots (τ : T) (n : Reg) (off w : Nat) (p : Bool) : List (Nat × Nat × Nat) :=
  match addrOf τ n off with
  | some (i, d) =>
    if d + w ≤ τ.lens.getD i 0 then
      if p then mergeSlot (i, d, w) τ.slots
      else cutSlots i d w τ.slots
    else if p then τ.slots else []
  | none => if p then τ.slots else []

def spBases (τ : T) (t : Reg) (off : Nat) : List (Reg × Nat) :=
  kill τ t ++ (τ.argBases.filter fun p => p.1 == off).map fun p => (t, p.2)

def storeStep (τ : T) (n : Reg) (off w : Nat) (p : Bool) : Option T :=
  if pub τ n then some { τ with slots := storeSlots τ n off w p } else none

/-- `Arm.Taint.stepKM`. -/
def step (τ : T) : Instr → Option T
  | .mov d op2 => some { τ with regs := set τ d (op2Pub τ op2), bases := movBases τ d op2 }
  | .dp _ d n op2 => some { τ with regs := set τ d (pub τ n && op2Pub τ op2), bases := kill τ d }
  | .adds d n op2 | .subs d n op2 =>
    let p := pub τ n && op2Pub τ op2
    some { τ with regs := set τ d p, flags := p, bases := kill τ d }
  | .adc d n op2 =>
    some { τ with regs := set τ d (pub τ n && op2Pub τ op2 && τ.flags), bases := kill τ d }
  | .cmp n op2 => some { τ with flags := pub τ n && op2Pub τ op2 }
  | .movw d _ => some { τ with regs := set τ d true, bases := kill τ d }
  | .adrSym d _ => some { τ with regs := set τ d false, bases := kill τ d }
  | .addSp d _ => some { τ with regs := set τ d (decide (0 < τ.argLen)), bases := kill τ d }
  | .movt d _ => some { τ with regs := set τ d (pub τ d), bases := kill τ d }
  | .rev d m => some { τ with regs := set τ d (pub τ m), bases := kill τ d }
  | .mul d n m => some { τ with regs := set τ d (pub τ n && pub τ m), bases := kill τ d }
  | .mla d n m a => some { τ with regs := set τ d (pub τ n && pub τ m && pub τ a), bases := kill τ d }
  | .umaal .. => none
  | .ldr t n off =>
    if pub τ n then some { τ with regs := set τ t (slotPub τ n off 4), bases := kill τ t } else none
  | .str t n off => storeStep τ n off 4 (pub τ t)
  | .ldrb t n _ => if pub τ n then some { τ with regs := set τ t false, bases := kill τ t } else none
  | .strb t n off => storeStep τ n off 1 (pub τ t)
  | .ldrSp t off =>
    if off + 4 ≤ τ.argLen then some { τ with regs := set τ t true, bases := spBases τ t off } else none
  | .push _ | .pop .. | .alloc _ | .free _ => none

def meet (τ₁ τ₂ : T) : T where
  regs := τ₁.regs.inter τ₂.regs
  flags := τ₁.flags && τ₂.flags
  lens := if τ₁.lens = τ₂.lens then τ₁.lens else []
  bases := τ₁.bases.filter (τ₂.bases.contains ·)
  slots := if τ₁.lens = τ₂.lens then interSlots τ₁.slots τ₂.slots else []
  argLen := if τ₁.argLen = τ₂.argLen then τ₁.argLen else 0
  argBases := if τ₁.argLen = τ₂.argLen then τ₁.argBases.filter (τ₂.argBases.contains ·) else []

def le (τ σ : T) : Bool :=
  τ.regs.subset σ.regs && (!τ.flags || σ.flags) && τ.lens == σ.lens &&
    τ.bases.all (σ.bases.contains ·) && τ.slots.all (fun x => σ.slots.any (containsSlot · x)) &&
    τ.argLen == σ.argLen && τ.argBases.all (σ.argBases.contains ·)

/-- `Arm.Taint.callStep`: a call leaves unknown values in `lr`, `r12` and the flags. -/
def callStep (τ : T) : T :=
  { τ with
    regs := (τ.regs.erase .lr).erase .r12
    flags := false
    bases := τ.bases.filter fun p => p.1 != .lr && p.1 != .r12 }

def hintOps : VG.NativeHintOps isa where
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
/-- An untrusted native hint; `Taint.check` still checks every interval. -/
def hintOfSize := VG.NativeHintOps.hintOfSize VG.NativeHints.Arm.hintOps
def hintWeakOfSize := VG.NativeHintOps.hintWeakOfSize VG.NativeHints.Arm.hintOps
end VG.NativeHints.Arm.provider
