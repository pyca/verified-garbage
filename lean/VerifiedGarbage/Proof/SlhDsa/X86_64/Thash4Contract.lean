module

public import VerifiedGarbage.Spec.Sha3
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# SLH-DSA on x86-64: the contract of `thash4`

`thash4(in = rdi, stride = rsi, len = rdx, out = rcx, work = r8)` writes
`SHAKE256(Mₖ, 8n)`, for `Mₖ` the `len` bytes at `in + k·stride`, to the `n`
bytes at `out + k·stride`, for `k` from 0 to 3 (`Impl/SlhDsa/X86_64/Thash4.lean`).
Every implementation of it (the four hashes one after the other, or at once
in vector registers) is proven against this contract, and the code above it
against any of them.

The four lanes are one writable region of `4·stride` bytes from `in`, each
lane `PK.seed ‖ ADRS ‖ M` with its output over the start of `M`:
`out = in + n + 32`, and `n + 32 + n ≤ stride`; each message lies within its
lane (`len ≤ stride`). `work` is a writable region of
`workLen` bytes whose bytes 1600 to 2367 hold the table of the round
constants of the four-way permutation (`rcTable`), which the function only
reads: it may change the rest of `work`, and of the lanes only the outputs.
Its calls take at most `stack` bytes below the stack pointer. The pointers,
`stride` and `len` are public; the messages are not.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64

open VG VG.X86_64
open VG.Spec.Sha3 (bytesAt RC shake256)

/-- The size of `work`. -/
def workLen : Nat := 2400

/-- The table of the round constants in `work`: round constant `r` in each of
the four quadwords at `work + 1600 + 32 r`. -/
def RcTable (m : Mem) (work : Addr) : Prop :=
  ∀ r < 24, ∀ k < 4, m.readW (work + BitVec.ofNat 64 (1600 + 32 * r + 8 * k)) 64 = RC r

/-- The return address's region. -/
abbrev retR (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-- The arguments of `thash4`, for outputs of `n` bytes, at the entry state
`s`, with `stack` bytes below the stack pointer for its calls. -/
structure Thash4Pre (n stack : Nat) (s : State) : Prop where
  rd : s.rd = []
  wr : s.wr = [⟨s.gpr .rdi, 4 * (s.gpr .rsi).toNat⟩, ⟨s.gpr .r8, workLen⟩]
  lanes_work : Region.Disjoint ⟨s.gpr .rdi, 4 * (s.gpr .rsi).toNat⟩ ⟨s.gpr .r8, workLen⟩
  ret_lanes : (retR s).Disjoint ⟨s.gpr .rdi, 4 * (s.gpr .rsi).toNat⟩
  ret_work : (retR s).Disjoint ⟨s.gpr .r8, workLen⟩
  stk_lanes : (below (s.gpr .rsp) stack).Disjoint ⟨s.gpr .rdi, 4 * (s.gpr .rsi).toNat⟩
  stk_work : (below (s.gpr .rsp) stack).Disjoint ⟨s.gpr .r8, workLen⟩
  lanes_fit : (s.gpr .rdi).toNat + 4 * (s.gpr .rsi).toNat ≤ 2 ^ 64
  work_fit : (s.gpr .r8).toNat + workLen ≤ 2 ^ 64
  len_pos : 0 < (s.gpr .rdx).toNat
  len_mod : (s.gpr .rdx).toNat % 8 = 0
  len_le : (s.gpr .rdx).toNat ≤ (s.gpr .rsi).toNat
  out_eq : s.gpr .rcx = s.gpr .rdi + BitVec.ofNat 64 (n + 32)
  out_fit : n + 32 + n ≤ (s.gpr .rsi).toNat
  rc : RcTable s.mem (s.gpr .r8)

/-- Message `k` at the entry state `s`. -/
def msg (s : State) (k : Nat) : List Byte :=
  bytesAt s.mem (s.gpr .rdi + BitVec.ofNat 64 (k * (s.gpr .rsi).toNat)) (s.gpr .rdx).toNat

/-- Where output `k` goes, at the entry state `s`. -/
def outAt (s : State) (k : Nat) : Addr := s.gpr .rcx + BitVec.ofNat 64 (k * (s.gpr .rsi).toNat)

/-- The regions `thash4` may change: the outputs, `work` but its table of
round constants, and the `stack` bytes below the stack pointer its calls
use. -/
def thash4Changes (n stack : Nat) (s : State) : List Region :=
  (List.range 4).map (fun k => ⟨outAt s k, n⟩) ++
    [⟨s.gpr .r8, 1600⟩, ⟨s.gpr .r8 + BitVec.ofNat 64 2368, workLen - 2368⟩, below (s.gpr .rsp) stack]

/-- The contract of `thash4` for outputs of `n` bytes, whose calls take at
most `stack` bytes below the stack pointer. -/
def thash4Contract (n stack : Nat) : Contract isa where
  pre := Thash4Pre n stack
  post s s' :=
    (∀ k < 4, bytesAt s'.mem (outAt s k) n = shake256 (msg s k) n) ∧
      Frame (thash4Changes n stack s) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.SlhDsa.X86_64
