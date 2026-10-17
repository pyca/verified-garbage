module

public import VerifiedGarbage.Proof.Hmac.Generic.Implies
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Calls
public import VerifiedGarbage.Spec.Hmac.Any
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# HMAC and streaming `update` with the hash function as an argument on x86-64: the contracts

`initA`, `updA` and `finA` are the contracts the proofs are written against:
`Spec.Hmac.Any`'s with their facts spelt out in registers, as HMAC's
`initG` and `finG` and the streaming `updK` (`Proof/Pbkdf2/Md/X86_64/Calls.lean`)
are for one hash function, with `hash` in `r9`. They imply the shared
contracts (`initImp`, `updImp`, `finImp`), which `initSat`, `updSat` and
`finSat` satisfy.
-/

@[expose] public section

namespace VG.Proof.Hmac.Any.X86_64

open VG.X86_64
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Hmac.Any (inst hashIds)
open Spec.Sha256 (bytesAt)

/-- `init(inner, outer, key, key_len, scratch, hash)`: `Spec.Hmac.Any.initContract`
with 24 bytes of stack. -/
def initA : Contract isa where
  pre s :=
    let inner : Region := ⟨s.gpr .rdi, 192⟩
    let outer : Region := ⟨s.gpr .rsi, 192⟩
    let key : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * 234⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 24, 24⟩
    ((s.gpr .r9).toNat ∈ hashIds ∧
      ∀ I, inst (s.gpr .r9).toNat = some I → (s.gpr .rcx).toNat ≤ I.S.H.blockSize) ∧
    s.rd = [key] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint key ∧ stack.Disjoint scratch ∧
    (s.gpr .r8).toNat + 8 * 234 ≤ 2 ^ 64
  post s s' := ∀ I, inst (s.gpr .r9).toNat = some I →
    let k0 := blockKey I.S.H (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    I.S.Repr s'.mem (s.gpr .rdi) (xorPad k0 ipad) ∧ I.S.Repr s'.mem (s.gpr .rsi) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp

/-- `update(state, count, data, len, scratch, hash)`: `Spec.Hmac.Any.updateContract`
with 16 bytes of stack. -/
def updA : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 192⟩
    let data : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * 234⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 16, 16⟩
    (s.gpr .r9).toNat ∈ hashIds ∧ s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch
  post s s' := ∀ I, inst (s.gpr .r9).toNat = some I →
    Spec.Hmac.Any.updatePost I.S (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) s.mem s'.mem
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp

/-- `finalize(inner, outer, count, out, scratch, hash)`:
`Spec.Hmac.Any.finalizeContract` with 24 bytes of stack. -/
def finA : Contract isa where
  pre s :=
    let inner : Region := ⟨s.gpr .rdi, 192⟩
    let outer : Region := ⟨s.gpr .rsi, 192⟩
    let out : Region := ⟨s.gpr .rcx, 64⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * 234⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 24, 24⟩
    (s.gpr .r9).toNat ∈ hashIds ∧ s.rd = [outer] ∧ s.wr = [inner, out, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint out ∧ inner.Disjoint scratch ∧
    outer.Disjoint out ∧ outer.Disjoint scratch ∧ out.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (s.gpr .r8).toNat + 8 * 234 ≤ 2 ^ 64
  post s s' := ∀ I, inst (s.gpr .r9).toNat = some I →
    ∀ k0 text, k0.length = I.S.H.blockSize → k0.length + text.length < 2 ^ 64 →
      I.S.Repr s.mem (s.gpr .rdi) (xorPad k0 ipad ++ text) →
      s.gpr .rdx = BitVec.ofNat 64 (I.S.H.blockSize + text.length) →
      I.S.Repr s.mem (s.gpr .rsi) (xorPad k0 opad) →
      bytesAt s'.mem (s.gpr .rcx) I.S.digestBytes = hmacBlockKey I.S.H k0 text
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp

/-! ## The shared contracts -/

/-- A state satisfying `init`'s precondition (SHA-1, a one-byte key). -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rsi => 0x20000 | .rdx => 0x30000 | .rcx => 1 | .r8 => 0x40000
    | .r9 => 1 | .rsp => 0x90000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x30000, 1⟩]
  wr := [⟨0x10000, 192⟩, ⟨0x20000, 192⟩, ⟨0x40000, 1872⟩]

/-- A state satisfying `update`'s precondition (SHA-1, no data). -/
def updSat : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rdx => 0x30000 | .r8 => 0x40000 | .r9 => 1 | .rsp => 0x90000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x30000, 0⟩]
  wr := [⟨0x10000, 192⟩, ⟨0x40000, 1872⟩]

/-- A state satisfying `finalize`'s precondition (SHA-1). -/
def finSat : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rsi => 0x20000 | .rcx => 0x30000 | .r8 => 0x40000
    | .r9 => 1 | .rsp => 0x90000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x20000, 192⟩]
  wr := [⟨0x10000, 192⟩, ⟨0x30000, 64⟩, ⟨0x40000, 1872⟩]

theorem initSat_ok : ∃ s, (Spec.Hmac.Any.initContract X86_64.abi 24).pre s := by
  inst_sat [Spec.Hmac.Any.initContract, Spec.Hmac.Any.initSig, Spec.Hmac.Any.hashIds,
    Spec.Hmac.Any.inst, Spec.Hmac.Any.stateBytes, Spec.Hmac.Any.scratchWords, X86_64.abi, X86_64.argRegs,
    initSat] using initSat

theorem updSat_ok : ∃ s, (Spec.Hmac.Any.updateContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Any.updateContract, Spec.Hmac.Any.updateSig, Spec.Hmac.Any.hashIds,
    Spec.Hmac.Any.stateBytes, Spec.Hmac.Any.scratchWords, X86_64.abi, X86_64.argRegs, updSat] using updSat

theorem finSat_ok : ∃ s, (Spec.Hmac.Any.finalizeContract X86_64.abi 24).pre s := by
  inst_sat [Spec.Hmac.Any.finalizeContract, Spec.Hmac.Any.finalizeSig, Spec.Hmac.Any.hashIds,
    Spec.Hmac.Any.stateBytes, Spec.Hmac.Any.digestBytes, Spec.Hmac.Any.scratchWords, X86_64.abi,
    X86_64.argRegs, finSat] using finSat

theorem initImp : initA.Implies (Spec.Hmac.Any.initContract X86_64.abi 24) := by
  generic_implies [Spec.Hmac.Any.initContract, Spec.Hmac.Any.initSig, Spec.Hmac.initPost,
    Spec.Hmac.Any.stateBytes, Spec.Hmac.Any.scratchWords, initA, X86_64.abi, X86_64.argRegs] using initSat_ok

theorem updImp : updA.Implies (Spec.Hmac.Any.updateContract X86_64.abi 16) := by
  generic_implies [Spec.Hmac.Any.updateContract, Spec.Hmac.Any.updateSig,
    Spec.Hmac.Any.stateBytes, Spec.Hmac.Any.scratchWords, updA, X86_64.abi, X86_64.argRegs] using updSat_ok

theorem finImp : finA.Implies (Spec.Hmac.Any.finalizeContract X86_64.abi 24) := by
  generic_implies [Spec.Hmac.Any.finalizeContract, Spec.Hmac.Any.finalizeSig, Spec.Hmac.finalizePost,
    Spec.Hmac.Any.stateBytes, Spec.Hmac.Any.digestBytes, Spec.Hmac.Any.scratchWords, finA, X86_64.abi,
    X86_64.argRegs] using finSat_ok

end VG.Proof.Hmac.Any.X86_64
