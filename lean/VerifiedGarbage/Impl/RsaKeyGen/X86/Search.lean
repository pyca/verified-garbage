module

public import VerifiedGarbage.Impl.Mont.X86.Compact
public import VerifiedGarbage.Impl.Bignum.X86.PublicRt

/-! # The RSA prime search on i686

`vg_rsa_prime_search`, as on AArch64 (`Impl/RsaKeyGen/AArch64/Search.lean`):
calls `vg_rsa_keygen_candidate` on the tape's successive candidates until one
is accepted, the budget of counted candidates or the tape's entropy runs
out, or the tape ends inside a candidate (`VG.Spec.RsaKeyGen.primeSearch`).

Its working state is in the callee-saved registers, which the candidate
keeps: the octets consumed in `esi`, the counted candidates left in `edi`,
the next tape's length in `ebp` and the status in `ebx` (4 while the search
goes on). It saves them in a frame of 16 bytes; the pointers and lengths it
reads from its own stack arguments each time, and passes the candidate's in
a frame of 44 bytes. The state's `u64` words, which are all below `2 ^ 32`,
are read and written as their halves.

`vg_rsa_prime_search(out, out_len, used, e, e_len, p, p_len, rand, rand_len,
scratch, scratch_len, state)`, all on the stack.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.X86.Search

open VG VG.X86
open VG.Impl.Mont.X86 (at_)
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- The words the search pushes. -/
def pushWords : Nat := 4

/-- The words of the candidate's arguments. -/
def callWords : Nat := 11

/-- The search's argument `i` (`out, out_len, used, e, e_len, p, p_len,
rand, rand_len, scratch, scratch_len, state`), below `extra` more words of
frame than its own. -/
def param (extra i : Nat) : MemOp := argAt (pushWords + extra) i

/-- The counted candidates left, the low half of the state's first word;
nothing consumed, no request, and the search goes on. -/
def entry : List Instr :=
  [.mov .eax (.mem (param 0 11)), .mov .edi (.mem (at_ .eax 0)), .mov .esi (.imm 0), .mov .ebp (.imm 0),
    .mov .ebx (.imm 4)]

/-- The search's argument `i` to the candidate's argument `i`, `adjust`ed. -/
def pass (i : Nat) (adjust : List Instr) : List Instr :=
  .mov .eax (.mem (param callWords i)) :: adjust ++ [.store (at_ .esp (4 * i)) .eax]

/-- The candidate's arguments, for the rest of the tape. -/
def arguments : List Instr :=
  pass 0 [] ++ pass 1 [] ++ pass 2 [] ++ pass 3 [] ++ pass 4 [] ++ pass 5 [] ++ pass 6 [] ++
    pass 7 [.alu .add .eax (.reg .esi)] ++ pass 8 [.alu .sub .eax (.reg .esi)] ++ pass 9 [] ++ pass 10 []

/-- No more candidates and no request, with `status`. -/
def terminal (status : Nat) : List Instr :=
  [.mov .edi (.imm 0), .mov .ebp (.imm 0), .mov .ebx (.imm (BitVec.ofNat 32 status))]

/-- `out_len` zeros at `out`. -/
def zeroOut : Prog isa :=
  .seq (.block [.mov .edx (.mem (param 0 0)), .mov .ecx (.mem (param 0 1)), .mov .eax (.imm 0)])
    (.loop (.block [.store8 (at_ .edx 0) .al, .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]) .ne)

/-- Exhausted: zeros at `out`, which no candidate may have written. -/
def exhausted : Prog isa := .seq (.block (terminal 3)) zeroOut

/-- The prime: its candidate's octets (`ecx`) consumed. -/
def accept : List Instr := .alu .add .esi (.reg .ecx) :: terminal 1

/-- The next tape's length, `VG.Proof.RsaKeyGen.primeRequest`: twice the larger of the octets
left (`eax`) and 16 per octet of the prime, at most the entropy budget
(`ebp`); the search stops, asking for it. The larger and the smaller come
from masks of the borrows: every value is public. -/
def request : List Instr :=
  [.mov .ecx (.mem (param 0 1)), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx),
    .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx),
    -- `eax := max(eax, ecx)`: `edx` all ones when `eax < ecx`.
    .alu .cmp .eax (.reg .ecx), .alu .sbb .edx (.reg .edx),
    .alu .xor .ecx (.reg .eax), .alu .and .ecx (.reg .edx), .alu .xor .eax (.reg .ecx),
    .alu .add .eax (.reg .eax),
    -- `eax := min(eax, ebp)`: `edx` all ones when `ebp < eax`.
    .alu .cmp .ebp (.reg .eax), .alu .sbb .edx (.reg .edx),
    .alu .xor .ebp (.reg .eax), .alu .and .ebp (.reg .edx), .alu .xor .eax (.reg .ebp),
    .mov .ebp (.reg .eax), .mov .ebx (.imm 0)]

/-- The tape ended inside a candidate: ask for more, unless the candidate
already had the whole budget, `32769 out_len` (in `ebp`). The candidate
wrote zeros at `out`. -/
def short : Prog isa := .seq
  (.block [.mov .ecx (.mem (param 0 1)), .mov .eax (.imm 32769), .mul .ecx, .mov .ebp (.reg .eax),
    .mov .eax (.mem (param 0 8)), .alu .sub .eax (.reg .esi), .alu .cmp .eax (.reg .ebp)])
  (.ite .e exhausted (.block request))

/-- A candidate rejected, too close (2) or otherwise (3), after `ecx`
octets: they are consumed, and a counted rejection is one candidate fewer;
one that consumed nothing (which no valid width allows) exhausts the search,
as the specification's progress check does. -/
def reject : Prog isa := .seq (.block [.alu .cmp .ecx (.imm 0)]) (.ite .e exhausted
  (.seq (.block [.alu .add .esi (.reg .ecx), .alu .cmp .eax (.imm 3)])
    (.ite .e (.block [.alu .sub .edi (.imm 1)]) (.block []))))

/-- The candidate's status in `eax`, the octets it consumed (the low half of
`used`) in `ecx`. -/
def classify : Prog isa :=
  .seq (.block [.mov .edx (.mem (param 0 2)), .mov .ecx (.mem (at_ .edx 0)), .alu .cmp .eax (.imm 1)])
    (.ite .e (.block accept) (.seq (.block [.alu .cmp .eax (.imm 0)]) (.ite .e short reject)))

variable (candidate : Prog isa)

/-- The candidate, a call of `vg_rsa_keygen_candidate`, in a frame of its
arguments. -/
def candidateRun : Prog isa :=
  .frame (.alloc (4 * callWords)) (.seq (.block arguments) candidate) (.free (4 * callWords))

/-- The candidate, unless fewer than `out_len` octets are left, which no
candidate fits in: then the tape ended inside one (status 0, as the
candidate would return), with zeros at `out`, and the candidate is not
called, which keeps the tape's pointer within it. -/
def candidateStep : Prog isa := .seq
  (.block [.mov .eax (.mem (param 0 8)), .alu .sub .eax (.reg .esi), .alu .cmp .eax (.mem (param 0 1))])
  (.ite .b (.seq zeroOut short) (.seq (candidateRun candidate) classify))

/-- The loop goes on while the status is 4. -/
def iteration : Prog isa :=
  .seq (.block [.alu .cmp .edi (.imm 0)]) (.seq (.ite .e exhausted (candidateStep candidate))
    (.block [.alu .cmp .ebx (.imm 4)]))

/-- The state's words (the counted candidates left, `out_len`, the budget
`32769 out_len` and the request, high halves zero), the octets consumed to
`used`, and the status returned. -/
def results : List Instr :=
  [.mov .ecx (.mem (param 0 1)), .mov .eax (.imm 32769), .mul .ecx, .mov .edx (.mem (param 0 11)),
    .store (at_ .edx 0) .edi, .store (at_ .edx 8) .ecx, .store (at_ .edx 16) .eax, .store (at_ .edx 24) .ebp,
    .mov .eax (.imm 0), .store (at_ .edx 4) .eax, .store (at_ .edx 12) .eax, .store (at_ .edx 20) .eax,
    .store (at_ .edx 28) .eax, .mov .edx (.mem (param 0 2)), .store (at_ .edx 0) .esi,
    .store (at_ .edx 4) .eax, .mov .eax (.reg .ebx)]

/-- The results, then the callee-saved registers but `ebx`, which the
frame's pop restores. -/
def finish : List Instr := results ++ Impl.Mont.X86.Compact.restoreRegs

def body : Prog isa := .seq (.block entry) (.seq (.loop (iteration candidate) .e) (.block finish))

def code : Prog isa :=
  .frame (.push [.ebx, .ebp, .esi, .edi]) (body candidate) (.pop .ebx pushWords)

end VG.Impl.RsaKeyGen.X86.Search
