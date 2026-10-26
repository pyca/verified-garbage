module

public import VerifiedGarbage.TCB.Code

/-!
# Speculative constant time (Spectre v1 and v1.1), prototype

**Prototype, untrusted.** `Spectre`, `SBlock`, `SExec` and
`SpecConstantTime` are definitions a reviewer has to trust; they would move
to `TCB/` in a PR of their own. They are those of
[#769](https://github.com/pyca/verified-garbage/pull/769).

The speculative semantics follows the directive-based definition of
Shivakumar et al., "Typing High-Speed Cryptography against Spectre v1"
(S&P 2023), as restated in Baumann et al., "FSLH" (arXiv 2502.03203,
Definitions 2 and 3): a misspeculation flag, attacker directives, every
prefix of a run observed, and no rollback, so an unbounded speculation
window.

* At every conditional (`ite`, and each evaluation of a `loop` condition)
  the attacker's next directive (`D`, a list of `Bool`) chooses the
  direction taken, whatever the condition evaluates to. A direction other
  than the condition's value sets the misspeculation flag `ms` (as does a
  condition on an undefined flag, `none`), which stays set: nested
  mispredictions are allowed and nothing is rolled back. The value of the
  condition leaks, as the observation `cond v`; it leaks too when no
  directive is left, and the run stops there.
* A run stops after `n` instructions (the fuel), wherever the attacker
  chooses, so every prefix of a non-terminating or faulting transient
  execution is observed.
* While `ms` is clear, instructions run with the sequential semantics
  (`M.exec`, `M.addrs`). While it is set, they run with the speculative
  semantics `S.sexec` and leak `S.saddrs`, and a speculation barrier
  (`S.fence`) stops the run, as the transient execution ends when the
  misprediction resolves.
* A return goes back to its call site: while `ms` is set as the return stack
  buffer predicts (`S.sret`), while it is clear as sequentially (`M.ret`).

`SpecConstantTime`: for every directive list and fuel, two runs that start
before any misspeculation, from states that agree on public data, leak the
same trace.
-/

@[expose] public section

namespace VG

/-- An observation of the speculative attacker. -/
inductive SLeak where
  | addr (a : Addr)
  /-- The value of a branch condition (`none`: it reads an undefined flag). -/
  | cond (v : Option Bool)
  deriving DecidableEq

/-- The speculative semantics: what an instruction does, and the addresses
it accesses, when executed transiently; the transient return of a called
function; and which instructions are speculation barriers. -/
structure Spectre (M : ISA) where
  sexec : M.Instr → M.State → Option M.State
  saddrs : M.Instr → M.State → List Addr
  sret : M.State → M.State → Option M.State
  fence : M.Instr → Bool

variable {M : ISA} (S : Spectre M)

/-- An instruction, transiently if `ms`. -/
def Spectre.run (ms : Bool) (i : M.Instr) (s : M.State) : Option M.State :=
  if ms then S.sexec i s else M.exec i s

/-- The addresses an instruction accesses, transiently if `ms`. -/
def Spectre.leaks (ms : Bool) (i : M.Instr) (s : M.State) : List Addr :=
  if ms then S.saddrs i s else M.addrs i s

/-- A return, transiently if `ms`. -/
def Spectre.ret (ms : Bool) (s₁ s₂ : M.State) : Option M.State :=
  if ms then S.sret s₁ s₂ else M.ret s₁ s₂

/-- The misspeculation flag after following direction `b` at a condition of
value `v`. -/
def Spectre.mis (ms : Bool) (v : Option Bool) (b : Bool) : Bool := ms || v != some b

/-- How a speculative run ends: stopped, or done with the misspeculation
flag and the remaining directives and fuel. -/
inductive SOut (M : ISA) where
  | halt
  | done (s : M.State) (ms : Bool) (D : List Bool) (n : Nat)

/-- Speculative run of a straight-line block, with misspeculation flag `ms`
and fuel `n`: `none` if it stopped. -/
inductive SBlock : List M.Instr → M.State → Bool → Nat → List SLeak → Option (M.State × Nat) → Prop
  | nil {s ms n} : SBlock [] s ms n [] (some (s, n))
  | stop {i is s ms} : SBlock (i :: is) s ms 0 [] none
  /-- A speculation barrier ends a transient run. -/
  | fence {i is s n} : S.fence i = true → SBlock (i :: is) s true (n + 1) [] none
  | cons {i is s s₁ ms n t r} : (ms && S.fence i) = false → S.run ms i s = some s₁ →
      SBlock is s₁ ms n t r →
      SBlock (i :: is) s ms (n + 1) ((S.leaks ms i s).map .addr ++ t) r

/-- Speculative big-step semantics, with misspeculation flag `ms`,
directives `D` and fuel `n`. -/
inductive SExec : Prog M → M.State → Bool → List Bool → Nat → List SLeak → SOut M → Prop
  | blockDone {is s s' ms D n n' t} : SBlock S is s ms n t (some (s', n')) →
      SExec (.block is) s ms D n t (.done s' ms D n')
  | blockHalt {is s ms D n t} : SBlock S is s ms n t none → SExec (.block is) s ms D n t .halt
  | seq {c₁ c₂ s s₁ ms ms₁ D D₁ n n₁ t₁ t₂ o} : SExec c₁ s ms D n t₁ (.done s₁ ms₁ D₁ n₁) →
      SExec c₂ s₁ ms₁ D₁ n₁ t₂ o → SExec (.seq c₁ c₂) s ms D n (t₁ ++ t₂) o
  | seqHalt {c₁ c₂ s ms D n t} : SExec c₁ s ms D n t .halt → SExec (.seq c₁ c₂) s ms D n t .halt
  | iteEnd {c th el s ms n} : SExec (.ite c th el) s ms [] n [.cond (M.eval c s)] .halt
  | iteT {c th el s ms D n t o} : SExec th s (Spectre.mis ms (M.eval c s) true) D n t o →
      SExec (.ite c th el) s ms (true :: D) n (.cond (M.eval c s) :: t) o
  | iteF {c th el s ms D n t o} : SExec el s (Spectre.mis ms (M.eval c s) false) D n t o →
      SExec (.ite c th el) s ms (false :: D) n (.cond (M.eval c s) :: t) o
  | loopHalt {body c s ms D n t} : SExec body s ms D n t .halt → SExec (.loop body c) s ms D n t .halt
  | loopEnd {body c s s' ms ms' D n n' t} : SExec body s ms D n t (.done s' ms' [] n') →
      SExec (.loop body c) s ms D n (t ++ [.cond (M.eval c s')]) .halt
  | loopExit {body c s s' ms ms' D D' n n' t} : SExec body s ms D n t (.done s' ms' (false :: D') n') →
      SExec (.loop body c) s ms D n (t ++ [.cond (M.eval c s')])
        (.done s' (Spectre.mis ms' (M.eval c s') false) D' n')
  | loopNext {body c s s' ms ms' D D' n n' t t' o} :
      SExec body s ms D n t (.done s' ms' (true :: D') n') →
      SExec (.loop body c) s' (Spectre.mis ms' (M.eval c s') true) D' n' t' o →
      SExec (.loop body c) s ms D n (t ++ .cond (M.eval c s') :: t') o
  | callHalt {name body s s₁ ms D n t} : M.call s = some s₁ → SExec body s₁ ms D n t .halt →
      SExec (.call name body) s ms D n ((M.callAddrs s).map .addr ++ t) .halt
  | call {name body s s₁ s₂ s' ms ms' D D' n n' t} : M.call s = some s₁ →
      SExec body s₁ ms D n t (.done s₂ ms' D' n') → S.ret ms' s₁ s₂ = some s' →
      SExec (.call name body) s ms D n
        ((M.callAddrs s).map .addr ++ t ++ (M.retAddrs s₂).map .addr) (.done s' ms' D' n')
  | frameHalt {i j body s s₁ ms D n t} : M.push i s = some s₁ → SExec body s₁ ms D n t .halt →
      SExec (.frame i body j) s ms D n ((M.addrs i s).map .addr ++ t) .halt
  | frame {i j body s s₁ s₂ s' ms ms' D D' n n' t} : M.push i s = some s₁ →
      SExec body s₁ ms D n t (.done s₂ ms' D' n') → M.pop j s₁ s₂ = some s' →
      SExec (.frame i body j) s ms D n
        ((M.addrs i s).map .addr ++ t ++ (M.addrs j s₂).map .addr) (.done s' ms' D' n')

/-- Speculative constant time: under any directives and fuel, two runs from
states agreeing on public data, starting before any misspeculation, leak
the same trace. -/
def SpecConstantTime (Pre : M.State → Prop) (Pub : M.State → M.State → Prop) (c : Prog M) : Prop :=
  ∀ s₁ s₂ D n t₁ t₂ o₁ o₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ →
    SExec S c s₁ false D n t₁ o₁ → SExec S c s₂ false D n t₂ o₂ → t₁ = t₂

end VG
