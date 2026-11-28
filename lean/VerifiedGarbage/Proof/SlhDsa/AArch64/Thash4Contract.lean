module

public import VerifiedGarbage.Spec.Sha3
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Mem

/-!
# SLH-DSA on AArch64: the contract of `thash4`

`thash4(in = x0, stride = x1, len = x2, out = x3, work = x4)` writes
`SHAKE256(Mₖ, 8n)`, for `Mₖ` the `len` bytes at `in + k·stride`, to the `n`
bytes at `out + k·stride`, for `k` from 0 to 3 (`Impl/SlhDsa/AArch64/Thash4.lean`),
as x86-64's (`Proof/SlhDsa/X86_64/Thash4Contract.lean`). Every implementation
of it (over each two-way Keccak-f[1600], `Proof/Variants/KeccakX2/AArch64.lean`)
is proven against this contract, and the code above it against any of them.

The four lanes are one writable region of `4·stride` bytes from `in`, each
lane `PK.seed ‖ ADRS ‖ M` with its output over the start of `M`:
`out = in + n + 32`, and `n + 32 + n ≤ stride`; each message lies within its
lane (`len ≤ stride`). `work` is a writable region of `workLen` bytes, of
which the function writes the first `workUsed` (the four states, the
permutation's working space and return address, and the callee-saved
registers it saves): it may change those, and of the lanes only the outputs.
There is no table of round constants (the permutation reads its own), and
no stack: its calls (`bl`) store nothing there. The pointers, `stride` and
`len` are public; the messages are not.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64

open VG VG.AArch64
open VG.Spec.Sha3 (bytesAt shake256)

/-- The size of `work`. -/
def workLen : Nat := 1024

/-- The bytes of `work` that `thash4` writes: the states (800), the
permutation's working space and the return address it keeps after it (136),
and the nine callee-saved registers it saves (72). -/
def workUsed : Nat := 1008

/-- The arguments of `thash4`, for outputs of `n` bytes, at the entry state
`s`. -/
structure Thash4Pre (n : Nat) (s : State) : Prop where
  rd : s.rd = []
  wr : s.wr = [⟨s.gpr .x0, 4 * (s.gpr .x1).toNat⟩, ⟨s.gpr .x4, workLen⟩]
  lanes_work : Region.Disjoint ⟨s.gpr .x0, 4 * (s.gpr .x1).toNat⟩ ⟨s.gpr .x4, workLen⟩
  lanes_fit : (s.gpr .x0).toNat + 4 * (s.gpr .x1).toNat ≤ 2 ^ 64
  work_fit : (s.gpr .x4).toNat + workLen ≤ 2 ^ 64
  len_pos : 0 < (s.gpr .x2).toNat
  len_mod : (s.gpr .x2).toNat % 8 = 0
  len_le : (s.gpr .x2).toNat ≤ (s.gpr .x1).toNat
  out_eq : s.gpr .x3 = s.gpr .x0 + BitVec.ofNat 64 (n + 32)
  out_fit : n + 32 + n ≤ (s.gpr .x1).toNat

/-- Message `k` at the entry state `s`. -/
def msg (s : State) (k : Nat) : List Byte :=
  bytesAt s.mem (s.gpr .x0 + BitVec.ofNat 64 (k * (s.gpr .x1).toNat)) (s.gpr .x2).toNat

/-- Where output `k` goes, at the entry state `s`. -/
def outAt (s : State) (k : Nat) : Addr := s.gpr .x3 + BitVec.ofNat 64 (k * (s.gpr .x1).toNat)

/-- The regions `thash4` may change: the outputs, and the first `workUsed`
bytes of `work`. -/
def thash4Changes (n : Nat) (s : State) : List Region :=
  (List.range 4).map (fun k => ⟨outAt s k, n⟩) ++ [⟨s.gpr .x4, workUsed⟩]

/-- The contract of `thash4` for outputs of `n` bytes. -/
def thash4Contract (n : Nat) : Contract isa where
  pre := Thash4Pre n
  post s s' :=
    (∀ k < 4, bytesAt s'.mem (outAt s k) n = shake256 (msg s k) n) ∧
      Frame (thash4Changes n s) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

end VG.Proof.SlhDsa.AArch64
