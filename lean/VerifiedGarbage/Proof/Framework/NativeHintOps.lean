module

public import Lean.Util.ReplaceExpr
public import VerifiedGarbage.TCB.Code
public import Lean.ToExpr

@[expose] public section

namespace VG
namespace NativeHints
inductive Hint (T : Type) where
  | block (mids : List T) (chunkSize : Nat := 256)
  | seq (mid : T) (h₁ h₂ : Hint T)
  | ite (h₁ h₂ : Hint T)
  | loop (inv : T) (h : Hint T)
  | call (h : Hint T)
  | frame (h : Hint T)
  deriving Lean.ToExpr

end NativeHints

/-- Operations for untrusted hint search. Only the separate sound checker
can turn a generated hint into a constant-time proof. -/
structure NativeHintOps (M : ISA) where
  T : Type
  step : T → M.Instr → Option T
  condPub : T → M.Cond → Bool
  meet : T → T → T
  le : T → T → Bool
  call : T → Option T
  ret : T → Option T
  push : T → M.Instr → Option T
  pop : T → M.Instr → Option T

namespace NativeHintOps
open NativeHints
variable {M : ISA} (A : NativeHintOps M)

def checkBlock (τ : A.T) (is : List M.Instr) : Option A.T :=
  is.foldlM (fun τ i => A.step τ i) τ

def chunk : Nat := 256

def chunkHints (chunkSize : Nat) : A.T → List M.Instr → Nat → List A.T
  | _, _, 0 => []
  | τ, is, n + 1 =>
    if is.length ≤ chunkSize then [] else
    match A.checkBlock τ (is.take chunkSize) with
    | some τ' => τ' :: chunkHints chunkSize τ' (is.drop chunkSize) n
    | none => []

/-- How many times the search for a loop invariant weakens its candidate. -/
def loopFuel : Nat := 4

/-- The analysis of structured code, with its hint. A loop's invariant is
found by starting from the taint on entry and, while the body does not keep
public everything the candidate says is public (or leaves the loop condition
secret), weakening the candidate to what is public both before and after the
body. -/
def hint (chunkSize : Nat) : A.T → Prog M → Option (A.T × Hint A.T)
  | τ, .block is => (A.checkBlock τ is).map fun τ' => (τ', .block (chunkHints A chunkSize τ is is.length) chunkSize)
  | τ, .seq c₁ c₂ =>
    (hint chunkSize τ c₁).bind fun (τ₁, h₁) => (hint chunkSize τ₁ c₂).map fun (τ₂, h₂) => (τ₂, .seq τ₁ h₁ h₂)
  | τ, .ite _ t e =>
    (hint chunkSize τ t).bind fun (τ₁, h₁) => (hint chunkSize τ e).map fun (τ₂, h₂) => (A.meet τ₁ τ₂, .ite h₁ h₂)
  | τ, .loop body c => go c (hint chunkSize · body) loopFuel τ
  | τ, .call _ body =>
    (A.call τ).bind fun τ₁ => (hint chunkSize τ₁ body).bind fun (τ₂, h) => (A.ret τ₂).map (·, .call h)
  | τ, .frame i body j =>
    (A.push τ i).bind fun τ₁ => (hint chunkSize τ₁ body).bind fun (τ₂, h) => (A.pop τ₂ j).map (·, .frame h)
  -- The taint analysis does not handle indirect calls.
  | _, .icall .. => none
where
  go (c : M.Cond) (body : A.T → Option (A.T × Hint A.T)) :
      Nat → A.T → Option (A.T × Hint A.T)
    | 0, _ => none
    | n + 1, σ => (body σ).bind fun (σ', h) =>
      if A.le σ σ' && A.condPub σ' c then some (σ', .loop σ h) else go c body n (A.meet σ σ')

/-- The hint for `c` from `τ` (any hint, if the analysis fails). -/
def hintOfSize (chunkSize : Nat) (τ : A.T) (c : Prog M) : Hint A.T :=
  ((hint A chunkSize τ c).map (·.2)).getD (.block [] chunkSize)

/-- A hint using the fallback interval, for summary and batch callers. -/
def hintOf (τ : A.T) (c : Prog M) : Hint A.T := hintOfSize A chunk τ c

/-- Compute a block's output and its intermediate weakened taints in one pass.
The checker still validates every interval; this only constructs its hint. -/
def blockHintWeak (chunkSize : Nat) (w : A.T → A.T) :
    A.T → List M.Instr → Nat → Option (A.T × List A.T)
  | τ, is, 0 => (A.checkBlock τ is).map (·, [])
  | τ, is, n + 1 =>
    if is.length ≤ chunkSize then (A.checkBlock τ is).map (·, []) else
    (A.checkBlock τ (is.take chunkSize)).bind fun τ' =>
      let mid := w τ'
      (blockHintWeak chunkSize w mid (is.drop chunkSize) n).map fun (out, ms) =>
        (out, mid :: ms)

/-- Search from the weakened intermediate states that the checker will use.
Unlike computing a full hint and mapping `w` over it afterward, the following
search never carries facts discarded at an earlier hint boundary. -/
def hintWeak (chunkSize : Nat) (w : A.T → A.T) : A.T → Prog M → Option (A.T × Hint A.T)
  | τ, .block is => (blockHintWeak A chunkSize w τ is is.length).map fun (out, ms) =>
      (out, .block ms chunkSize)
  | τ, .seq c₁ c₂ =>
    (hintWeak chunkSize w τ c₁).bind fun (τ₁, h₁) =>
      let mid := w τ₁
      (hintWeak chunkSize w mid c₂).map fun (τ₂, h₂) => (τ₂, .seq mid h₁ h₂)
  | τ, .ite _ t e =>
    (hintWeak chunkSize w τ t).bind fun (τ₁, h₁) =>
      (hintWeak chunkSize w τ e).map fun (τ₂, h₂) => (A.meet τ₁ τ₂, .ite h₁ h₂)
  | τ, .loop body c => go c (hintWeak chunkSize w · body) loopFuel (w τ)
  | τ, .call _ body =>
    (A.call τ).bind fun τ₁ => (hintWeak chunkSize w τ₁ body).bind fun (τ₂, h) =>
      (A.ret τ₂).map (·, .call h)
  | τ, .frame i body j =>
    (A.push τ i).bind fun τ₁ => (hintWeak chunkSize w τ₁ body).bind fun (τ₂, h) =>
      (A.pop τ₂ j).map (·, .frame h)
  | _, .icall .. => none
where
  go (c : M.Cond) (body : A.T → Option (A.T × Hint A.T)) :
      Nat → A.T → Option (A.T × Hint A.T)
    | 0, _ => none
    | n + 1, σ => (body σ).bind fun (σ', h) =>
      if A.le σ σ' && A.condPub σ' c then some (σ', .loop σ h)
      else go c body n (w (A.meet σ σ'))

/-- A weakened hint, or an arbitrary hint if the untrusted search fails. -/
def hintWeakOfSize (chunkSize : Nat) (w : A.T → A.T) (τ : A.T) (c : Prog M) : Hint A.T :=
  ((hintWeak A chunkSize w τ c).map (·.2)).getD (.block [] chunkSize)


end NativeHintOps

namespace NativeHints

/-- `Taint.SHint`, constructor for constructor: a hint with summaries. -/
inductive SHint (T : Type) where
  | block (mids : List T)
  | seq (mid : T) (h₁ h₂ : SHint T)
  | ite (h₁ h₂ : SHint T)
  | loop (inv : T) (h : SHint T)
  | call (h : SHint T)
  | frame (h : SHint T)
  | sum (k : Nat)
  deriving Lean.ToExpr

/-- `Taint.codeBeq`. -/
def codeBeq {I C : Type} [BEq I] [BEq C] : Code I C → Code I C → Bool
  | .block a, .block b => a == b
  | .seq a b, .seq c d => codeBeq a c && codeBeq b d
  | .ite x a b, .ite y c d => x == y && codeBeq a c && codeBeq b d
  | .loop a x, .loop b y => x == y && codeBeq a b
  | .call n a, .call m b => n == m && codeBeq a b
  | .frame i a j, .frame k b l => i == k && j == l && codeBeq a b
  | _, _ => false

end NativeHints

/-- `NativeHintOps` with the operations of a domain's frames (`Taint.Frame`):
untrusted, for the hint search of `taint_decide_sum`, whose hints the kernel
checks (`Taint.checkSum`). -/
structure NativeFrameOps (M : ISA) extends NativeHintOps M where
  R : T → T → Bool
  join : T → T → T
  frameOf : T → T → T

namespace NativeFrameOps
open NativeHints
variable {M : ISA} (A : NativeFrameOps M)

/-- A summary: code, `pre`, `post` and frame (`Taint.Summary`). -/
abbrev Summary := Prog M × A.T × A.T × A.T

/-! The hint search of `Taint.hintReport` (`Proof/Framework/TaintSum.lean`), in
compiled code: the same functions, on the domain's copy. -/

def findSum (n : String) (τ : A.T) : List A.Summary → Nat → Option (Nat × A.T)
  | [], _ => none
  | (c, pre, post, F) :: S, k => match c with
    | .call n' _ =>
      if n' == n && A.R pre τ then some (k, A.join post (A.frameOf τ F))
      else findSum n τ S (k + 1)
    | _ => findSum n τ S (k + 1)

def findSumCode (same : Prog M → Prog M → Bool) (c : Prog M) (τ : A.T) :
    List A.Summary → Nat → Option (Nat × A.T)
  | [], _ => none
  | (c', pre, post, F) :: S, k =>
    if same c' c && A.R pre τ then some (k, A.join post (A.frameOf τ F))
    else findSumCode same c τ S (k + 1)

def entryCall : Prog M → Option String
  | .call n _ => some n
  | .seq c _ => entryCall c
  | .frame _ c _ => entryCall c
  | _ => none

def leadsWithSum {T : Type} : SHint T → Bool
  | .sum _ => true
  | .seq _ h _ => leadsWithSum h
  | .frame h => leadsWithSum h
  | _ => false

def hasCallSum (S : List A.Summary) (n : String) : Bool :=
  S.any fun (c, _) => match c with
    | .call n' _ => n' == n
    | _ => false

def sumOr {T : Type} (o : Option (Nat × T)) (k : Unit → Option (T × SHint T)) :
    Option (T × SHint T) :=
  match o with
  | some (k, post) => some (post, .sum k)
  | none => k ()

/-- `Taint.chunk`: the interval of the hints of `Taint.checkSum`'s blocks. -/
def chunk : Nat := 256

def hintSumA (S : List A.Summary) (same : Prog M → Prog M → Bool) :
    List A.T → A.T → Prog M → Option (A.T × SHint A.T)
  | _, τ, .block is => sumOr (findSumCode A same (.block is) τ S 0) fun _ =>
    (A.checkBlock τ is).map fun τ' => (τ', .block (A.chunkHints chunk τ is is.length))
  | anc, τ, .seq c₁ c₂ => sumOr (findSumCode A same (.seq c₁ c₂) τ S 0) fun _ =>
    (hintSumA S same anc τ c₁).bind fun (τ₁, h₁) =>
      let anc' := τ :: anc
      let plain := (hintSumA S same anc' τ₁ c₂).map fun (τ₂, h₂) => (τ₂, .seq τ₁ h₁ h₂)
      match entryCall c₂ with
      | some n =>
        if hasCallSum A S n && !(plain.any fun (_, h) => match h with
            | .seq _ _ h₂ => leadsWithSum h₂
            | _ => false) then
          (anc'.findSome? fun a =>
            let m := A.join a (A.frameOf τ₁ τ₁)
            if A.le m τ₁ then
              (hintSumA S same anc' m c₂).bind fun (τ₂, h₂) =>
                if leadsWithSum h₂ then some (τ₂, .seq m h₁ h₂) else none
            else none) <|> plain
        else plain
      | none => plain
  | anc, τ, .ite cd t e => sumOr (findSumCode A same (.ite cd t e) τ S 0) fun _ =>
    (hintSumA S same anc τ t).bind fun (τ₁, h₁) => (hintSumA S same anc τ e).map fun (τ₂, h₂) =>
      (A.meet τ₁ τ₂, .ite h₁ h₂)
  | anc, τ, .loop body c => sumOr (findSumCode A same (.loop body c) τ S 0) fun _ =>
    go c (hintSumA S same anc · body) NativeHintOps.loopFuel τ
  | _, τ, .call n body => match findSum A n τ S 0 with
    | some (k, post) => some (post, .sum k)
    | none => (A.call τ).bind fun τ₁ => (hintSumA S same [] τ₁ body).bind fun (τ₂, h) =>
      (A.ret τ₂).map (·, .call h)
  | _, τ, .frame i body j => sumOr (findSumCode A same (.frame i body j) τ S 0) fun _ =>
    (A.push τ i).bind fun τ₁ => (hintSumA S same [] τ₁ body).bind fun (τ₂, h) =>
      (A.pop τ₂ j).map (·, .frame h)
  | _, _, .icall .. => none
where
  go (c : M.Cond) (body : A.T → Option (A.T × SHint A.T)) :
      Nat → A.T → Option (A.T × SHint A.T)
    | 0, _ => none
    | n + 1, σ => (body σ).bind fun (σ', h) =>
      if A.le σ σ' && A.condPub σ' c then some (σ', .loop σ h) else go c body n (A.meet σ σ')

/-- `Taint.sumsOfCall`. -/
def sumsOfCall (S : List A.Summary) (body : Prog M → Prog M → Bool) (n : String) (b : Prog M) :
    List Nat :=
  go S 0
where
  go : List A.Summary → Nat → List Nat
    | [], _ => []
    | s :: S, k =>
      let hit := match s.1 with
        | .call n' b' => n' == n || body b' b
        | c' => body c' b
      if hit then k :: go S (k + 1) else go S (k + 1)

def missedCalls (S : List A.Summary) (body : Prog M → Prog M → Bool) :
    Prog M → SHint A.T → List (String × Nat)
  | .seq c₁ c₂, .seq _ h₁ h₂ => missedCalls S body c₁ h₁ ++ missedCalls S body c₂ h₂
  | .ite _ t e, .ite h₁ h₂ => missedCalls S body t h₁ ++ missedCalls S body e h₂
  | .loop b _, .loop _ h => missedCalls S body b h
  | .frame _ b _, .frame h => missedCalls S body b h
  | .call n b, .call h =>
    let applied := match h with
      | .sum _ => true
      | _ => false
    (if applied then [] else (sumsOfCall A S body n b).map (n, ·)) ++ missedCalls S body b h
  | _, _ => []

/-- `Taint.hintReport`: the taint at the end and the hint (`τ` and any hint, if
the analysis fails), and the calls the hint analyses in full although a
summary is of the same function. -/
def hintReport (S : List A.Summary) (same body : Prog M → Prog M → Bool) (τ : A.T) (c : Prog M) :
    (A.T × SHint A.T) × List (String × Nat) :=
  let ph := (hintSumA A S same [] τ c).getD (τ, .block [])
  (ph, missedCalls A S body c ph.2)

end NativeFrameOps
end VG

namespace VG.NativeHints
open Lean
def renamePrefix (old new : Name) (n : Name) : Name :=
  if n == old then new else match n with
  | .str p s => .str (renamePrefix old new p) s
  | .num p i => .num (renamePrefix old new p) i
  | .anonymous => .anonymous

/-- Reify the native hint into the checked domain's constructors. The caller
must still establish the checker equation in the kernel. -/
def checkedHintExpr (src dst : Name) (e : Expr) : Expr := e.replace fun t => match t with
  | .const n us =>
    let n' := renamePrefix `VG.NativeHints.Hint `VG.Taint.Hint n
    let n' := renamePrefix src dst n'
    if n' == n then none else some (.const n' us)
  | _ => none
end VG.NativeHints
