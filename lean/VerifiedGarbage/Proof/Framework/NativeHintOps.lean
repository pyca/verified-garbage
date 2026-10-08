import Lean.Util.ReplaceExpr
import VerifiedGarbage.TCB.Code
import Lean.ToExpr

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
end VG

namespace VG.NativeHints
open Lean
private def renamePrefix (old new : Name) (n : Name) : Name :=
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
