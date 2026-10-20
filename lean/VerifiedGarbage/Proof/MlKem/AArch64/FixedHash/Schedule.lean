module
public import VerifiedGarbage.Impl.MlKem.AArch64.Top


/-! A checked straight-line absorb schedule. The checker validates every
source byte, destination position, and permutation boundary. -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64

structure Action where
  base : Reg
  off : Nat
  pos : Nat
  word : Bool
  deriving DecidableEq

def width (w : Bool) : Nat := if w then 8 else 1

def action (p : Piece) (i pos : Nat) (w : Bool) : Action :=
  ⟨p.base,p.off+i,pos,w⟩

def nextPos (rate pos : Nat) (w : Bool) : Nat :=
  if pos+width w=rate then 0 else pos+width w

inductive Valid (rate : Nat) : List Piece → Nat → Nat → List Action → Nat → Prop where
  | done (pos : Nat) : Valid rate [] 0 pos [] pos
  | skip {p ps pos acts last} : Valid rate ps 0 pos acts last →
      Valid rate (p::ps) p.len pos acts last
  | step {p ps i pos w acts last}
      (hi : i+width w≤p.len) (hp : pos+width w≤rate)
      (hw : w=true → i%8=0 ∧ pos%8=0)
      (tail : Valid rate (p::ps) (i+width w) (nextPos rate pos w) acts last) :
      Valid rate (p::ps) i pos (action p i pos w::acts) last

def check (rate : Nat) : Nat → List Piece → Nat → Nat → List Action → Nat → Bool
  | 0,_,_,_,_,_ => false
  | _+1,[],i,pos,acts,last => i==0 && acts.isEmpty && last==pos
  | fuel+1,p::ps,i,pos,acts,last =>
    if i=p.len then check rate fuel ps 0 pos acts last
    else match acts with
    | [] => false
    | a::rest =>
      decide (a=action p i pos a.word) &&
      decide (i+width a.word≤p.len) && decide (pos+width a.word≤rate) &&
      decide (a.word=true → i%8=0 ∧ pos%8=0) &&
      check rate fuel (p::ps) (i+width a.word) (nextPos rate pos a.word) rest last

theorem check_sound {rate fuel ps i pos acts last}
    (h : check rate fuel ps i pos acts last=true) : Valid rate ps i pos acts last := by
  induction fuel generalizing ps i pos acts last with
  | zero => simp [check] at h
  | succ fuel ih =>
    cases ps with
    | nil =>
      simp only [check,Bool.and_eq_true,beq_iff_eq,List.isEmpty_iff] at h
      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := h
      exact .done _
    | cons p ps =>
      simp only [check] at h
      split at h
      · subst i; exact .skip (ih h)
      · cases acts with
        | nil => simp at h
        | cons a rest =>
          simp only [Bool.and_eq_true,decide_eq_true_eq] at h
          obtain ⟨⟨⟨⟨ha,hi⟩,hp⟩,hw⟩,ht⟩ := h
          have tail := ih ht
          rw [ha]
          exact .step hi hp hw tail

/-- Produce a candidate schedule; `check_sound` is the separate certificate. -/
def generate (rate : Nat) : Nat → List Piece → Nat → Nat → List Action × Nat
  | 0,_,_,pos => ([],pos)
  | _+1,[],_,pos => ([],pos)
  | fuel+1,p::ps,i,pos =>
    if i=p.len then generate rate fuel ps 0 pos
    else
      let w := i%8==0 && pos%8==0 && p.len-i≥8
      let tail := generate rate fuel (p::ps) (i+width w) (nextPos rate pos w)
      (action p i pos w::tail.1,tail.2)

def fuelFor (ps : List Piece) : Nat := (ps.map (·.len)).sum+ps.length+1

def schedule (rate : Nat) (ps : List Piece) : List Action × Nat :=
  generate rate (fuelFor ps) ps 0 0

def certified (rate : Nat) (ps : List Piece) : Bool :=
  check rate (fuelFor ps) ps 0 0 (schedule rate ps).1 (schedule rate ps).2

theorem certified_sound {rate ps} (h : certified rate ps=true) :
    Valid rate ps 0 0 (schedule rate ps).1 (schedule rate ps).2 := check_sound h

def actionCode (sc : Reg) (st : Nat) (a : Action) : List Instr :=
  ptrTo .x2 a.base a.off ++
  if a.word then
    [.ldr .x .x9 .x2 0,.ldr .x .x10 sc (st+a.pos),
     .logic .eor .x .x9 .x9 .x10,.str .x .x9 sc (st+a.pos)]
  else
    [.ldrb .x9 .x2 0,.ldrb .x10 sc (st+a.pos),
     .logic .eor .x .x9 .x9 .x10,.strb .x9 sc (st+a.pos)]

def permute (c : Impl.Sha3.AArch64.Callee) (sc : Reg) (st wk : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 sc st ++ ptrTo .x1 sc wk)) (.call c.name c.code)

def compile (c : Impl.Sha3.AArch64.Callee) (sc : Reg) (st wk rate : Nat) : List Action → Prog isa
  | [] => .block []
  | a::as => .seq (.block (actionCode sc st a))
      (if a.pos+width a.word=rate then .seq (permute c sc st wk) (compile c sc st wk rate as)
       else compile c sc st wk rate as)

end VG.Proof.MlKem.AArch64.FixedHash
