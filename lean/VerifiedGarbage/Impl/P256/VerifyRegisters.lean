import VerifiedGarbage.Impl.Weierstrass.AArch64.Forward

/-! Register allocation for the fixed, public P-256 verification blocks.

The optimizer is not trusted. Each selected output is checked against its
arithmetic specification by the verification artifact's proofs. It forwards
scratch words in SSA form, schedules dependencies (including carry flags),
and allocates scalar registers with bounded scratch spills.
-/
namespace VG.Impl.P256.VerifyRegisters
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64

private instance : Inhabited Instr := ⟨.movz .x .x7 0 0⟩

structure Item where
  instr : Instr
  reads : List (Reg × Nat)
  dest : Option (Reg × Nat)
  implicit : Option Nat := none
  deriving Inhabited

def Item.inputs (i : Item) : List Nat :=
  ((i.reads.map Prod.snd).filter (· != 0)).eraseDups

def get {α β : Type} [BEq α] (k : α) (xs : List (α × β)) := xs.lookup k
def put {α β : Type} [BEq α] (k : α) (v : β) (xs : List (α × β)) := Forward.put k v xs

def loadOffset : Instr → Option Nat
  | .ldr .x _ .x0 off => some off
  | _ => none
def storeOffset : Instr → Option Nat
  | .str .x _ .x0 off => some off
  | _ => none
def readsCarry : Instr → Bool
  | .adcs .. | .sbcs .. | .adc .. | .sbc .. | .csel .. => true
  | _ => false
def writesCarry : Instr → Bool
  | .adds .. | .subs .. | .adcs .. | .sbcs .. => true
  | _ => false

/-- Value zero denotes the unchanged scratch pointer, not a numeric zero. -/
def ssa (initial : List Reg) (code : List Instr) : Option (List Item × Nat) := do
  let mut regs := (Reg.x0,0) :: (initial.zipIdx.map fun (r,i) => (r,i+1))
  let mut memory : List (Nat × Nat) := []
  let mut constants : List (Instr × Nat) := []
  let mut fresh := initial.length
  let mut out := []
  for i in code do
    let reads ← (Forward.readRegs i).mapM fun r => do
      let v ← get r regs
      pure (r,v)
    let dst := Forward.writeReg i
    if dst == some .x0 then none
    match i with
    | .ldr .x d .x0 off =>
      if let some v := get off memory then
        regs := put d v regs
        continue
    | .logic .orr .x d a b =>
      if a == b then
        let v ← get a regs
        regs := put d v regs
        continue
    | .movz z d v k =>
      if let some value := get (.movz z .x0 v k) constants then
        regs := put d value regs
        continue
    | _ => pure ()
    let mut dest := none
    if let some d := dst then
      fresh := fresh+1
      dest := some (d,fresh)
      regs := put d fresh regs
    else if (storeOffset i).isNone then none
    let implicit ← match i with
      | .movk _ d _ _ => some <$> get d reads
      | _ => pure none
    out := {instr := i, reads := reads, dest := dest, implicit := implicit} :: out
    match i with
    | .ldr .x _ .x0 off => memory := put off fresh memory
    | .str .x r .x0 off =>
      let v ← get r reads
      memory := put off v memory
    | .movz z _ v k => constants := put (.movz z .x0 v k) fresh constants
    | _ => pure ()
  return (out.reverse,fresh+1)

/-- Retain the final stores required by this block's point or inversion contract. -/
def stores (keep : Nat → Bool) (items : List Item) : List Item := Id.run do
  let mut seen := []
  let mut out := []
  for i in items.reverse do
    if let some off := storeOffset i.instr then
      if keep off && !seen.contains off then out := i :: out
      seen := off :: seen
    else out := i :: out
  return out

def dependencies (items : Array Item) : Array (List Nat) := Id.run do
  let mut defs : List (Nat × Nat) := []
  let mut flag : Option Nat := none
  let mut flagReads : List Nat := []
  let mut written : List (Nat × Nat) := []
  let mut loaded : List (Nat × List Nat) := []
  let mut out := #[]
  for idx in [:items.size] do
    let i := items[idx]!
    let mut ds := i.inputs.filterMap fun v => get v defs
    if let some (_,v) := i.dest then defs := put v idx defs
    if readsCarry i.instr then
      if let some f := flag then ds := f :: ds
      flagReads := idx :: flagReads
    if writesCarry i.instr then
      if let some f := flag then ds := f :: ds
      ds := flagReads.filter (· != idx) ++ ds
      flagReads := []
      flag := some idx
    if let some off := (loadOffset i.instr).or (storeOffset i.instr) then
      if let some w := get off written then ds := w :: ds
      if (storeOffset i.instr).isSome then
        ds := (get off loaded).getD [] ++ ds
        loaded := put off [] loaded
        written := put off idx written
      else loaded := put off (idx :: (get off loaded).getD []) loaded
    out := out.push ds.eraseDups
  return out

def latency : Instr → Nat
  | .ldr .. | .mul .. | .umulh .. | .madd .. => 4
  | _ => 1

def schedule (items : List Item) (values : Nat) : List Item := Id.run do
  let xs := items.toArray
  let deps := dependencies xs
  let mut successors := Array.replicate xs.size ([] : List Nat)
  for i in [:xs.size] do
    for d in deps[i]! do successors := successors.set! d (i :: successors[d]!)
  let mut scores := Array.replicate xs.size 0
  for i in (List.range xs.size).reverse do
    scores := scores.set! i (latency xs[i]!.instr +
      (successors[i]!).foldl (fun n j => max n scores[j]!) 0)
  let mut counts := deps.map List.length
  let mut left := Array.replicate values 0
  for i in xs do
    for v in i.inputs do left := left.set! v (left[v]!+1)
  let mut live := Array.replicate values false
  let mut liveCount := 0
  let mut done := Array.replicate xs.size false
  let mut out := []
  for _ in [:xs.size] do
    let mut chosen := xs.size
    let mut best : Int := 0
    for j in [:xs.size] do
      if !done[j]! && counts[j]! == 0 then
        let i := xs[j]!
        let up := if i.dest.any (fun p => left[p.2]! > 0) then 1 else 0
        let down := (i.inputs.filter (fun v => left[v]! == 1)).length
        let pressure := (liveCount+up : Nat) - (down+27)
        let score : Int := Int.ofNat scores[j]! - Int.ofNat (1000*pressure)
        if chosen == xs.size || score > best then
          chosen := j
          best := score
    if chosen < xs.size then
      let i := xs[chosen]!
      out := i :: out
      done := done.set! chosen true
      for v in i.inputs do
        left := left.set! v (left[v]!-1)
        if left[v]! == 0 && live[v]! then
          live := live.set! v false
          liveCount := liveCount-1
      if let some (_,v) := i.dest then
        if left[v]! > 0 then
          live := live.set! v true
          liveCount := liveCount+1
      for j in successors[chosen]! do counts := counts.set! j (counts[j]!-1)
  return out.reverse

def rename (rd wr : Reg → Reg) : Instr → Instr
  | .add z d a b => .add z (wr d) (rd a) (rd b)
  | .sub z d a b => .sub z (wr d) (rd a) (rd b)
  | .adds z d a b => .adds z (wr d) (rd a) (rd b)
  | .subs z d a b => .subs z (wr d) (rd a) (rd b)
  | .adcs z d a b => .adcs z (wr d) (rd a) (rd b)
  | .sbcs z d a b => .sbcs z (wr d) (rd a) (rd b)
  | .adc z d a b => .adc z (wr d) (rd a) (rd b)
  | .sbc z d a b => .sbc z (wr d) (rd a) (rd b)
  | .csel z d a b => .csel z (wr d) (rd a) (rd b)
  | .logic op z d a b => .logic op z (wr d) (rd a) (rd b)
  | .mul z d a b => .mul z (wr d) (rd a) (rd b)
  | .umulh d a b => .umulh (wr d) (rd a) (rd b)
  | .madd z d a b c => .madd z (wr d) (rd a) (rd b) (rd c)
  | .lsl z d a n => .lsl z (wr d) (rd a) n
  | .lsr z d a n => .lsr z (wr d) (rd a) n
  | .extr z d a b n => .extr z (wr d) (rd a) (rd b) n
  | .movz z d v n => .movz z (wr d) v n
  | .movk z d v n => .movk z (wr d) v n
  | .ldr z d a n => .ldr z (wr d) (rd a) n
  | .str z a b n => .str z (rd a) (rd b) n
  | i => i

def pool : List Reg :=
  [.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,
   .x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x30]

structure Alloc where
  physical : List (Reg × Nat) := []
  backing : List (Nat × Nat) := []
  reversed : List Instr := []

def nextUse (uses : Array (List Nat)) (v idx : Nat) : Nat :=
  ((uses[v]!).find? (· >= idx)).getD 999999

def available (regs : List Reg) (uses : Array (List Nat)) (idx : Nat)
    (held : List Nat) (s : Alloc) : Option (Reg × Alloc) := do
  if let some r := regs.find? (fun r => (get r s.physical).isNone) then return (r,s)
  let choices := regs.filter (fun r => !(get r s.physical).any held.contains)
  let first ← choices.head?
  let chosen := choices.foldl (fun a r =>
    if nextUse uses ((get r s.physical).getD 0) idx >
       nextUse uses ((get a s.physical).getD 0) idx then r else a) first
  let value ← get chosen s.physical
  let mut s := {s with physical := s.physical.filter (fun p => p.1 != chosen)}
  if nextUse uses value idx != 999999 && (get value s.backing).isNone then
    let used := (s.backing.filter (fun p => nextUse uses p.1 idx != 999999)).map Prod.snd
    let off ← ((List.range 72).map (fun i => 7104+8*i)).find? (fun off => !used.contains off)
    s := {s with backing := put value off s.backing, reversed := .str .x chosen .x0 off :: s.reversed}
  return (chosen,s)

def allocate (initial regs : List Reg) (items : List Item) (values : Nat) : Option (List Instr) := do
  let xs := items.toArray
  let mut uses := Array.replicate values ([] : List Nat)
  for idx in (List.range xs.size).reverse do
    for v in xs[idx]!.inputs do uses := uses.set! v (idx :: uses[v]!)
  let mut s : Alloc := {physical := initial.zipIdx.map (fun (r,i) => (r,i+1))}
  for idx in [:xs.size] do
    let i := xs[idx]!
    let held := i.inputs
    for v in held do
      if !(s.physical.any (fun p => p.2 == v)) then
        let off ← get v s.backing
        let (r,t) ← available regs uses idx held s
        s := {t with physical := put r v t.physical, reversed := .ldr .x r .x0 off :: t.reversed}
    let old := (0,Reg.x0) :: s.physical.map (fun (r,v) => (v,r))
    let mut dst := none
    if let some (_,v) := i.dest then
      let mut r := Reg.x0
      if let some source := i.implicit then
        let src ← get source old
        if nextUse uses source (idx+1) == 999999 then r := src
        else
          let (chosen,t) ← available regs uses idx held s
          r := chosen
          s := {t with reversed := .logic .orr .x r src src :: t.reversed}
      else
        let dead := regs.find? fun r => match get r s.physical with
          | none => true
          | some v => nextUse uses v (idx+1) == 999999
        if let some chosen := dead then r := chosen
        else
          let (chosen,t) ← available regs uses idx held s
          r := chosen
          s := t
      dst := some r
      s := {s with physical := put r v s.physical}
    let reads ← i.reads.mapM fun (r,v) => do
      let p ← get v old
      pure (r,p)
    let emitted := rename (fun r => (get r reads).getD r) (fun r => dst.getD r) i.instr
    s := {s with reversed := emitted :: s.reversed}
  return s.reversed.reverse

def optimize (initial regs : List Reg) (keep : Nat → Bool) (code : List Instr) : List Instr :=
  ((do
    let (items,values) ← ssa initial code
    allocate initial regs (schedule (stores keep items) values) values) : Option (List Instr)).getD code

end VG.Impl.P256.VerifyRegisters
