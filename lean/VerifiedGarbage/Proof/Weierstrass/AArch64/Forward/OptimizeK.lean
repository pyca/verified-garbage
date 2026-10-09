import VerifiedGarbage.Impl.Weierstrass.AArch64.Forward

/-! A twin of the untrusted scheduler's forwarding pass for the kernel. Proofs
need `optimize`'s output as a literal, which the kernel checks by evaluating
`optimize`. Its `forward` pass (a `for` loop in `Id` over association lists
compared through `BEq` instances) costs the kernel several times as much as
the same steps written with recursors and `Nat.beq`; `optimize_eq` rewrites
`optimize` to that twin, which is proved equal to it for every input. -/

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.Forward

/-- The state of `forward`'s loop: registers' and words' values, the output in
reverse, and the last fresh value. -/
abbrev FState := List (Reg×Nat) × List (Nat×Nat) × List Instr × Nat

private theorem forIn_id_of_yield {α β : Type} (l : List α) (init : β) (g : α → β → Id (ForInStep β))
    (f : α → β → β) (h : ∀ a b,g a b=.yield (f a b)) :
    forIn l init g=l.foldl (fun b a => f a b) init := by
  have : g=fun a b => pure (ForInStep.yield (f a b)) := by funext a b; exact h a b
  subst this
  exact List.forIn_pure_yield_eq_foldl _ _

private theorem reg_beq (a b : Reg) : Nat.beq a.ctorIdx b.ctorIdx=(a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact ⟨fun he => by rw [← Reg.ofNat_ctorIdx a,he,Reg.ofNat_ctorIdx],fun he => he ▸ rfl⟩

private theorem nat_beq (a b : Nat) : Nat.beq a b=(a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]

/-- `List.lookup` of a register, by `List.rec`. -/
noncomputable def lookupRegK (d : Reg) (regs : List (Reg×Nat)) : Option Nat :=
  List.rec none (fun p _ r => Bool.rec r (some p.2) (Nat.beq d.ctorIdx p.1.ctorIdx)) regs

theorem lookupRegK_eq (d : Reg) (regs : List (Reg×Nat)) : lookupRegK d regs=regs.lookup d := by
  induction regs with
  | nil => rfl
  | cons p regs ih =>
    rw [List.lookup,← ih]
    change Bool.rec (motive := fun _ => Option Nat) (lookupRegK d regs) (some p.2)
      (Nat.beq d.ctorIdx p.1.ctorIdx)=_
    rw [reg_beq]
    cases d==p.1 <;> rfl

/-- `put`'s filter of a register, by `List.rec`. -/
noncomputable def dropRegK (d : Reg) (regs : List (Reg×Nat)) : List (Reg×Nat) :=
  List.rec [] (fun p _ r => Bool.rec (p :: r) r (Nat.beq p.1.ctorIdx d.ctorIdx)) regs

theorem dropRegK_eq (d : Reg) (v : Nat) (regs : List (Reg×Nat)) :
    (d,v) :: dropRegK d regs=put d v regs := by
  unfold put
  congr 1
  induction regs with
  | nil => rfl
  | cons p regs ih =>
    rw [List.filter_cons,← ih]
    change Bool.rec (motive := fun _ => List (Reg×Nat)) (p :: dropRegK d regs) (dropRegK d regs)
      (Nat.beq p.1.ctorIdx d.ctorIdx)=_
    rw [reg_beq]
    cases h : p.1==d <;> simp_all

/-- The register holding `value` first, by `List.rec`. -/
noncomputable def findRegK (value : Nat) (regs : List (Reg×Nat)) : Option Reg :=
  List.rec none (fun p _ r => Bool.rec r (some p.1) (Nat.beq p.2 value)) regs

theorem findRegK_eq (value : Nat) (regs : List (Reg×Nat)) :
    findRegK value regs=(regs.find? (fun p => p.2==value)).map Prod.fst := by
  induction regs with
  | nil => rfl
  | cons p regs ih =>
    change Bool.rec (motive := fun _ => Option Reg) (findRegK value regs) (some p.1)
      (Nat.beq p.2 value)=_
    rw [nat_beq,ih,List.find?_cons]
    cases p.2==value <;> rfl

/-- `List.lookup` of a word, by `List.rec`. -/
noncomputable def lookupWordK (off : Nat) (mem : List (Nat×Nat)) : Option Nat :=
  List.rec none (fun p _ r => Bool.rec r (some p.2) (Nat.beq off p.1)) mem

theorem lookupWordK_eq (off : Nat) (mem : List (Nat×Nat)) : lookupWordK off mem=mem.lookup off := by
  induction mem with
  | nil => rfl
  | cons p mem ih =>
    rw [List.lookup,← ih]
    change Bool.rec (motive := fun _ => Option Nat) (lookupWordK off mem) (some p.2)
      (Nat.beq off p.1)=_
    rw [nat_beq]
    cases off==p.1 <;> rfl

/-- `put`'s filter of a word, by `List.rec`. -/
noncomputable def dropWordK (off : Nat) (mem : List (Nat×Nat)) : List (Nat×Nat) :=
  List.rec [] (fun p _ r => Bool.rec (p :: r) r (Nat.beq p.1 off)) mem

theorem dropWordK_eq (off v : Nat) (mem : List (Nat×Nat)) :
    (off,v) :: dropWordK off mem=put off v mem := by
  unfold put
  congr 1
  induction mem with
  | nil => rfl
  | cons p mem ih =>
    rw [List.filter_cons,← ih]
    change Bool.rec (motive := fun _ => List (Nat×Nat)) (p :: dropWordK off mem) (dropWordK off mem)
      (Nat.beq p.1 off)=_
    rw [nat_beq]
    cases h : p.1==off <;> simp_all

/-- The body of `forward`'s loop, by recursors and `Nat.beq`. -/
noncomputable def forwardStepK (i : Instr) (s : FState) : FState :=
  let regs := s.1
  let mem := s.2.1
  let out := s.2.2.1
  let fresh := s.2.2.2+1
  match i with
  | .ldr .x d .x0 off =>
    let value := Option.rec fresh (fun v => v) (lookupWordK off mem)
    let src := Bool.rec (findRegK value regs) (some d)
      (Option.rec false (fun v => Nat.beq v value) (lookupRegK d regs))
    let out := Option.rec (i :: out)
      (fun r => Bool.rec (.logic .orr .x d r r :: out) out (Nat.beq r.ctorIdx d.ctorIdx)) src
    ((d,value) :: dropRegK d regs,(off,value) :: dropWordK off mem,out,fresh)
  | .str .x r .x0 off =>
    let value := Option.rec fresh (fun v => v) (lookupRegK r regs)
    ((r,value) :: dropRegK r regs,(off,value) :: dropWordK off mem,i :: out,fresh)
  | .movz .x r 0 _ =>
    ((r,0) :: dropRegK r regs,mem,
      Bool.rec out (i :: out) (Option.rec true (fun v => !Nat.beq v 0) (lookupRegK r regs)),fresh)
  | _ =>
    match writeReg i with
    | some d => ((d,fresh) :: dropRegK d regs,mem,i :: out,fresh)
    | none => ([],[],i :: out,fresh)

private theorem getD_rec (x : Option Nat) (d : Nat) : Option.rec d (fun v => v) x=x.getD d := by
  cases x <;> rfl

private theorem beq_rec (x : Option Nat) (v : Nat) :
    Option.rec false (fun w => Nat.beq w v) x=(x==some v) := by
  cases x <;> simp [nat_beq]

private theorem bne_rec (x : Option Nat) (v : Nat) :
    Option.rec true (fun w => !Nat.beq w v) x=(x != some v) := by
  cases x with
  | none => rfl
  | some w =>
    change (!Nat.beq w v)=(some w != some v)
    by_cases h : w=v
    · subst h; simp
    · have : Nat.beq w v=false := Bool.eq_false_iff.mpr (by rw [Ne,Nat.beq_eq]; exact h)
      rw [this]; simp [h]

private theorem bool_rec {β : Type} (x y : β) (b : Bool) :
    Bool.rec (motive := fun _ => β) x y b=if b=true then y else x := by cases b <;> rfl

theorem forward_eq (is : List Instr) :
    forward is=(is.foldl (fun s i => forwardStepK i s) ([],[],[],1)).2.2.1.reverse := by
  unfold forward
  simp only [Id.run]
  rw [forIn_id_of_yield _ _ _ forwardStepK]
  · rfl
  · intro i s
    simp only [forwardStepK,getD_rec,beq_rec,bne_rec,bool_rec,lookupWordK_eq,lookupRegK_eq,findRegK_eq,
      dropRegK_eq,dropWordK_eq,reg_beq]
    split <;> (try split) <;> (try split) <;> simp_all <;> rfl

/-- One step, then the rest (`k`). Taking the step's result apart makes the
kernel evaluate it before the next, rather than build a chain of steps. -/
noncomputable def forwardThen (i : Instr) (s : FState) (k : FState → FState) : FState :=
  Prod.casesOn (motive := fun _ => FState) (forwardStepK i s) fun a b => k (a,b)

/-- `forward`'s loop, by `List.rec`. -/
noncomputable def forwardK (is : List Instr) (s : FState) : FState :=
  List.rec (motive := fun _ => FState → FState) (fun s => s) (fun i _ ih s => forwardThen i s ih) is s

theorem forwardK_eq (is : List Instr) (s : FState) :
    forwardK is s=is.foldl (fun s i => forwardStepK i s) s := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    change Prod.casesOn (motive := fun _ => FState) (forwardStepK i s) (fun a b => forwardK is (a,b))=_
    rw [List.foldl_cons,← ih]

/-- The body of `deadStores`'s loop (the words read before written again,
and the output), by recursors and `Nat.beq`. -/
noncomputable def deadStepK (i : Instr) (s : List Nat × List Instr) : List Nat × List Instr :=
  let later := s.1
  let out := s.2
  match i with
  | .str .x _ .x0 off =>
    (off :: later,Bool.rec (i :: out) out (List.rec false (fun o _ r => Nat.beq o off || r) later))
  | .ldr .x _ .x0 off =>
    (List.rec [] (fun o _ r => Bool.rec (o :: r) r (Nat.beq o off)) later,i :: out)
  | _ =>
    (Option.rec [] (fun _ => later) (writeReg i),i :: out)

private theorem contains_rec (later : List Nat) (off : Nat) :
    List.rec (motive := fun _ => Bool) false (fun o _ r => Nat.beq o off || r) later=later.contains off := by
  induction later with
  | nil => rfl
  | cons o later ih =>
    change (Nat.beq o off || List.rec (motive := fun _ => Bool) false
      (fun o _ r => Nat.beq o off || r) later)=_
    rw [ih,nat_beq]
    by_cases h : o=off <;> simp [h,Ne.symm]

private theorem filter_rec (later : List Nat) (off : Nat) :
    List.rec (motive := fun _ => List Nat) [] (fun o _ r => Bool.rec (o :: r) r (Nat.beq o off)) later=
      later.filter (· != off) := by
  induction later with
  | nil => rfl
  | cons o later ih =>
    change Bool.rec (motive := fun _ => List Nat) (o :: List.rec (motive := fun _ => List Nat) []
      (fun o _ r => Bool.rec (o :: r) r (Nat.beq o off)) later) (List.rec (motive := fun _ => List Nat) []
      (fun o _ r => Bool.rec (o :: r) r (Nat.beq o off)) later) (Nat.beq o off)=_
    rw [ih,nat_beq,List.filter_cons]
    by_cases h : o=off
    · simp [h]
    · rw [beq_false_of_ne h]; simp [h]

private theorem write_rec (w : Option Reg) (l : List Nat) :
    Option.rec (motive := fun _ => List Nat) [] (fun _ => l) w=if (w==none)=true then [] else l := by
  cases w <;> rfl

theorem deadStores_eq (is : List Instr) :
    deadStores is=(is.reverse.foldl (fun s i => deadStepK i s) ([],[])).2 := by
  unfold deadStores
  simp only [Id.run]
  rw [forIn_id_of_yield _ _ _ deadStepK]
  · rfl
  · intro i s
    simp only [deadStepK,contains_rec,filter_rec,write_rec]
    split <;> (try split) <;> (try split) <;> simp_all <;> rfl

noncomputable def deadThen (i : Instr) (s : List Nat × List Instr)
    (k : List Nat × List Instr → List Nat × List Instr) : List Nat × List Instr :=
  Prod.casesOn (motive := fun _ => List Nat × List Instr) (deadStepK i s) fun a b => k (a,b)

/-- `deadStores`'s loop, by `List.rec`. -/
noncomputable def deadK (is : List Instr) (s : List Nat × List Instr) : List Nat × List Instr :=
  List.rec (motive := fun _ => List Nat × List Instr → List Nat × List Instr) (fun s => s)
    (fun i _ ih s => deadThen i s ih) is s

theorem deadK_eq (is : List Instr) (s : List Nat × List Instr) :
    deadK is s=is.foldl (fun s i => deadStepK i s) s := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    change Prod.casesOn (motive := fun _ => List Nat × List Instr) (deadStepK i s)
      (fun a b => deadK is (a,b))=_
    rw [List.foldl_cons,← ih]

/-- `optimize`, by the twins of its passes. -/
noncomputable def optimizeK (is : List Instr) : List Instr :=
  (deadK (foldMoves (forwardK is ([],[],[],1)).2.2.1.reverse).reverse ([],[])).2

theorem optimize_eq (is : List Instr) : optimize is=optimizeK is := by
  rw [optimize,forward_eq,deadStores_eq,optimizeK,deadK_eq,forwardK_eq]

/-- `optimize is` is `r`, by the kernel's evaluation of the twin on `is`'s literal `l`. -/
theorem optimize_of_lit {is l r : List Instr} (hl : is=l) (h : optimizeK l=r) : optimize is=r := by
  rw [optimize_eq,hl,h]

end VG.Proof.Weierstrass.AArch64.Forward
