module

public import VerifiedGarbage.Impl.Ffdh.X86.Domain
public import VerifiedGarbage.Spec.Ffdh.Contract

/-!
# FFDH on i686: key generation

`vg_ffdh_generate_key`, on the operations of `Domain.lean`: p checked as a
modulus (RSA's check of its bytes, as `vg_ffdh_check_domain` does), else 0
returned; the bound's octets (q's, or p's, whose first nonzero octet is
`p − 1`'s for an odd p above one) scanned for the first nonzero one, `ld`,
and the mask `t` of its bits, without a branch; `rand`'s `p_len` octets cut
there to `x` (zeros before octet `ld`, octet `ld` and'ed with `t`, the rest
kept), without a branch; x checked as a scalar as `vg_ffdh_check_private`
checks it (2 returned and zeros written otherwise, the one branch on x);
then `y = g^x mod p`, its range and, with q, `y^q mod p = 1` as the
acceptance mask, x and y written (zeros unless accepted) and `3 − 2 flag`
returned, without a branch.

The header words: `t`'s octet (16), the scan's flag (20), `ld` (24) and the
mask `t` (28).
-/

@[expose] public section
namespace VG.Impl.Ffdh.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- Wide slot `j`. -/
local notation:max "sl " j:max => Loc.slot Ctx.wide j
/-- A number of the wide context. -/
local notation "n1" => one Ctx.wide

/-- The header words of the scan and the cut. -/
def tbOff : Nat := 16
def foundOff : Nat := 20
def ldOff : Nat := 24
def tOff : Nat := 28

/-- The result, masked by the acceptance word, written to synthetic argument `p` (`l` bytes, at the
synthetic argument `l`), and the acceptance's low bit in `eax`: `exportResult` for `p = 0`, `l = 1`. -/
def exportTo (p l : Nat) : Prog isa :=
  .seq (.block (ptrTo (.slot .wide 19) .ebp .edx ++ cntTo (one .wide) .edx ++ [.mov .ecx (.mem (sc accOff))])) <|
  .seq maskLoop <|
  .seq (.block ([.mov .ebx (.mem (argAt 0 p)), .mov .ecx (.mem (argAt 0 l))] ++ ptrTo (.slot .wide 19) .esi .edx ++
    [.alu .add .esi (.reg .ecx), .alu .sub .esi (.imm 1)]))
    (.seq reverseBytes (.block [.mov .eax (.mem (sc accOff)), .alu .and .eax (.imm 1)]))

namespace GenerateKey

/-- `(x, x_len, y, y_len, domain, domain_len, p_len, rand, rand_len, scratch, scratch_len)`: x the output
(synthetic argument 0), y's output as synthetic argument 8, `rand` as 10. -/
def args : Args := { out := some 0, dom := 4, dlen := 5, plen := 6, y := some 2, x := some 7, ws := 9 }

/-- `esi` the bound's octets: the domain's third component with q, else its first. -/
def boundPtr : List Instr :=
  [.mov .eax (.mem (argAt 0 12)), .mov .ecx (.mem (argAt 0 3)), .alu .sub .eax (.reg .ecx),
    .alu .sub .eax (.reg .ecx), .mov .esi (.mem (argAt 0 2)), .alu .add .esi (.reg .eax), .alu .add .esi (.reg .eax)]

/-- The scan's start: `ld = p_len − 1` (`ebx`), `i = 0` (`ecx`), no octet nor flag. -/
def scanInit : List Instr :=
  [.mov .ebx (.mem (argAt 0 3)), .alu .sub .ebx (.imm 1), .mov .ecx (.imm 0), .mov .eax (.imm 0),
    .store (sc tbOff) .eax, .store (sc foundOff) .eax]

/-- Octet `i` of the bound (at `esi`): if it is the first nonzero one, `ld := i` and its octet kept. -/
def scanStep : List Instr :=
  [.movzx8 .eax ⟨.esi, 0⟩, .mov .edx (.reg .eax), .alu .add .edx (.imm 0xFFFFFFFF), .alu .sbb .edx (.reg .edx),
    .mov .ebp (.mem (sc foundOff)), .alu .xor .ebp (.imm 0xFFFFFFFF), .alu .and .ebp (.reg .edx),
    .alu .or .edx (.mem (sc foundOff)), .store (sc foundOff) .edx,
    .mov .edx (.reg .ebx), .alu .xor .edx (.reg .ecx), .alu .and .edx (.reg .ebp), .alu .xor .ebx (.reg .edx),
    .mov .edx (.mem (sc tbOff)), .alu .xor .eax (.reg .edx), .alu .and .eax (.reg .ebp), .alu .xor .edx (.reg .eax),
    .store (sc tbOff) .edx,
    .alu .add .esi (.imm 1), .alu .add .ecx (.imm 1), .mov .edx (.mem (argAt 0 3)), .alu .cmp .ecx (.reg .edx)]

/-- `ld` and the mask `t` of the octet's bits to the header. -/
def scanEnd : List Instr :=
  [.store (sc ldOff) .ebx, .mov .eax (.mem (sc tbOff)),
    .mov .edx (.reg .eax), .shift .shr .edx 1, .alu .or .eax (.reg .edx),
    .mov .edx (.reg .eax), .shift .shr .edx 2, .alu .or .eax (.reg .edx),
    .mov .edx (.reg .eax), .shift .shr .edx 4, .alu .or .eax (.reg .edx), .store (sc tOff) .eax]

def scan : Prog isa := .seq (.block (boundPtr ++ scanInit)) (.seq (.loop (.block scanStep) .ne) (.block scanEnd))

/-- The cut's start: `rand` (`esi`), `x` (`ebx`), `i = 0`. -/
def cutInit : List Instr :=
  [.mov .esi (.mem (argAt 0 10)), .mov .ebx (.mem (argAt 0 0)), .mov .ecx (.imm 0)]

/-- Octet `i` of `rand` to `x`: zero before `ld`, and'ed with `t` at it, kept after it. -/
def cutStep : List Instr :=
  [.mov .eax (.reg .ecx), .alu .cmp .eax (.mem (sc ldOff)), .alu .sbb .edx (.reg .edx),
    .alu .xor .eax (.mem (sc ldOff)), .alu .add .eax (.imm 0xFFFFFFFF), .alu .sbb .ebp (.reg .ebp),
    .mov .eax (.mem (sc tOff)), .alu .xor .eax (.imm 0xFF), .alu .and .eax (.reg .ebp), .alu .xor .eax (.mem (sc tOff)),
    .alu .xor .edx (.imm 0xFFFFFFFF), .alu .and .eax (.reg .edx),
    .movzx8 .edx ⟨.esi, 0⟩, .alu .and .edx (.reg .eax), .store8 ⟨.ebx, 0⟩ .dl,
    .alu .add .esi (.imm 1), .alu .add .ebx (.imm 1), .alu .add .ecx (.imm 1), .mov .eax (.mem (argAt 0 3)),
    .alu .cmp .ecx (.reg .eax)]

def cut : Prog isa := .seq (.block cutInit) (.loop (.block cutStep) .ne)

/-- x and y (the wide slots 13 and 12) written, masked by the acceptance word; its low bit in `eax`. -/
def outputs : Prog isa :=
  .seq (copy (sl 13) (sl 19) n1) <| .seq (exportTo 0 1) <| .seq (copy (sl 12) (sl 19) n1) (exportTo 8 9)

/-- Zeros written for x and y, and 2 returned. -/
def fail : Prog isa :=
  .seq (.block [.mov .ecx (.imm 0), .store (sc accOff) .ecx]) (.seq outputs (ret 2))

/-- `y = g^x mod p` (slot 12), its range and, with q, `y^q mod p = 1` as the acceptance; x and y
written, and `3 − 2 flag` returned. -/
def tail : Prog isa :=
  .seq (powP 10 13) <| .seq (copy (sl 6) (sl 12) n1) <| .seq (rangeMask 12) <|
  .seq (.block [.store (sc accOff) .ecx]) <|
  .seq (.block qTest) <|
  .seq (.ite .e (.block []) (.seq (powP 12 16) (.seq (equal (sl 6) (sl 3) n1)
    (.block [.alu .and .ecx (.mem (sc accOff)), .store (sc accOff) .ecx])))) <|
  .seq outputs
    (.block [.alu .add .eax (.reg .eax), .mov .ecx (.imm 3), .alu .sub .ecx (.reg .eax), .mov .eax (.reg .ecx)])

/-- With p a valid modulus: p's setup, g, the scalar cut from `rand` and checked, then `tail`. -/
def main : Prog isa :=
  .seq pSetup <| .seq (load (sl 10) n1 4 5) <| .seq scan <| .seq cut <| .seq (load (sl 13) n1 0 1) <|
  .seq CheckPrivate.bound <| .seq CheckPrivate.scalarMask <| .seq testMask (.ite .e fail tail)

def body : Prog isa :=
  .seq (.block PublicFn.modulusArgs) (.seq (.block modulusCheck) (.ite .e main (ret 0)))

def code : Prog isa := wrap args body

end GenerateKey

/-! ## `vg_ffdh_key_generation_init` -/

namespace KeyInit

/-- `(state, p_len)`: `edx := 1` exactly when `64 ≤ p_len ≤ 1024`, by the borrows of two comparisons
(`edx` cleared first, so that the mask is public). -/
def validate : List Instr :=
  [.mov .ecx (.mem (PublicFn.argument 0)), .mov .eax (.mem (PublicFn.argument 1)), .mov .edx (.imm 0),
    .alu .cmp .eax (.imm 64), .alu .sbb .edx (.reg .edx), .alu .xor .edx (.imm 0xFFFFFFFF),
    .alu .cmp .eax (.imm 1025), .alu .sbb .eax (.reg .eax), .alu .and .edx (.reg .eax), .alu .and .edx (.imm 1)]

/-- The four public words, 64 bits each: `k`, `s`, `w` and `r` (registers or zero). -/
def words (k s w r : Src) : List Instr :=
  [.mov .eax k, .store (at_ .ecx 0) .eax, .mov .eax s, .store (at_ .ecx 8) .eax,
    .mov .eax w, .store (at_ .ecx 16) .eax, .mov .eax r, .store (at_ .ecx 24) .eax,
    .mov .eax (.imm 0), .store (at_ .ecx 4) .eax, .store (at_ .ecx 12) .eax, .store (at_ .ecx 20) .eax,
    .store (at_ .ecx 28) .eax]

def code : Prog isa :=
  .seq (.block (validate ++ [.alu .test .edx (.reg .edx)]))
    (.ite .e (.block (words (.imm 0) (.imm 0) (.imm 0) (.imm 0) ++ [.mov .eax (.imm 0)]))
      (.block ([.mov .edx (.mem (PublicFn.argument 1))] ++
        words (.imm 128) (.imm 128) (.reg .edx) (.reg .edx) ++ [.mov .eax (.imm 1)])))

end KeyInit

/-! ## `vg_ffdh_generate_key_search` -/

namespace KeySearch

/-- `(x, x_len, y, y_len, used, domain, domain_len, p_len, rand, rand_len, scratch, scratch_len, state)`:
argument `i`, from `esp`'s distance `k` below the entry's. -/
def argK (k i : Nat) : MemOp := argAt k i

/-- The state's private words: the caller's `esi`, the tape's pointer and length, the octets
consumed, the status. -/
def savedOff : Nat := 32
def randOff : Nat := 40
def leftOff : Nat := 44
def usedOff : Nat := 48
def statusOff : Nat := 52

/-- A state word, at `esi`. -/
def st (d : Nat) : MemOp := at_ .esi d

/-- `esi` the state, the caller's `esi` saved in it; the tape; nothing consumed. -/
def entry : List Instr :=
  [.mov .eax (.mem (argK 0 12)), .store (at_ .eax savedOff) .esi, .mov .esi (.reg .eax),
    .mov .eax (.mem (argK 0 8)), .store (st randOff) .eax, .mov .eax (.mem (argK 0 9)), .store (st leftOff) .eax,
    .mov .eax (.imm 0), .store (st usedOff) .eax]

/-- `p_len` zeros at the argument `i`. -/
def zeroOut (i : Nat) : Prog isa :=
  .seq (.block [.mov .ebx (.mem (argK 0 i)), .mov .ecx (.mem (argK 0 7)), .mov .eax (.imm 0)])
    (.loop (.block [.store8 ⟨.ebx, 0⟩ .al, .alu .add .ebx (.imm 1), .alu .sub .ecx (.imm 1)]) .ne)

/-- Zeros at `x` and `y`. -/
def zeroOutputs : Prog isa := .seq (zeroOut 0) (zeroOut 2)

/-- The budgets and the request zero, and `status`. -/
def terminal (status : Nat) : List Instr :=
  [.mov .eax (.imm 0), .store (st 0) .eax, .store (st 8) .eax, .store (st 24) .eax, .store (st 28) .eax,
    .mov .eax (.imm (BitVec.ofNat 32 status)), .store (st statusOff) .eax]

def exhausted : Prog isa := .seq (.block (terminal 3)) zeroOutputs

/-- Ask for `p_len` octets: the tape holds less than an attempt. -/
def request : Prog isa :=
  .seq (.block [.mov .eax (.mem (argK 0 7)), .store (st 24) .eax, .mov .eax (.imm 0), .store (st 28) .eax,
    .store (st statusOff) .eax]) zeroOutputs

/-- `vg_ffdh_generate_key`'s arguments, for `p_len` octets at the tape's pointer, in the frame of 44
bytes. -/
def arguments : List Instr :=
  [.mov .eax (.mem (argK 11 0)), .store (at_ .esp 0) .eax, .mov .eax (.mem (argK 11 7)), .store (at_ .esp 4) .eax,
    .mov .eax (.mem (argK 11 2)), .store (at_ .esp 8) .eax, .mov .eax (.mem (argK 11 7)), .store (at_ .esp 12) .eax,
    .mov .eax (.mem (argK 11 5)), .store (at_ .esp 16) .eax, .mov .eax (.mem (argK 11 6)), .store (at_ .esp 20) .eax,
    .mov .eax (.mem (argK 11 7)), .store (at_ .esp 24) .eax, .mov .eax (.mem (st randOff)), .store (at_ .esp 28) .eax,
    .mov .eax (.mem (argK 11 7)), .store (at_ .esp 32) .eax, .mov .eax (.mem (argK 11 10)), .store (at_ .esp 36) .eax,
    .mov .eax (.mem (argK 11 11)), .store (at_ .esp 40) .eax]

/-- The attempt, a call of `vg_ffdh_generate_key`, in a frame of its arguments. -/
def attempt : Prog isa :=
  .frame (.alloc 44) (.seq (.block arguments) (.call Spec.Ffdh.generateKeyApi.name GenerateKey.code)) (.free 44)

/-- The attempt's `p_len` octets consumed; the status in `edx`. -/
def advance : List Instr :=
  [.mov .edx (.reg .eax), .mov .ecx (.mem (argK 0 7)),
    .mov .eax (.mem (st randOff)), .alu .add .eax (.reg .ecx), .store (st randOff) .eax,
    .mov .eax (.mem (st leftOff)), .alu .sub .eax (.reg .ecx), .store (st leftOff) .eax,
    .mov .eax (.mem (st usedOff)), .alu .add .eax (.reg .ecx), .store (st usedOff) .eax]

/-- A scalar out of range: one fewer scalar left. -/
def rejectedScalar : List Instr :=
  [.mov .eax (.mem (st 8)), .alu .sub .eax (.imm 1), .store (st 8) .eax, .mov .eax (.imm 4), .store (st statusOff) .eax]

/-- A degenerate public value: one fewer key left, and the scalar budget again. -/
def rejectedPublic : List Instr :=
  [.mov .eax (.mem (st 0)), .alu .sub .eax (.imm 1), .store (st 0) .eax, .mov .eax (.imm 128), .store (st 8) .eax,
    .mov .eax (.imm 4), .store (st statusOff) .eax]

/-- ZF set when the status `edx` is `k`. -/
def test (k : Nat) : List Instr := [.mov .eax (.reg .edx), .alu .cmp .eax (.imm (BitVec.ofNat 32 k))]

def classify : Prog isa := .seq (.block (advance ++ test 1))
  (.ite .e (.block (terminal 1))
    (.seq (.block (test 2))
      (.ite .e (.block rejectedScalar)
        (.seq (.block (test 3)) (.ite .e (.block rejectedPublic) exhausted)))))

/-- ZF clear when the tape holds an attempt: `left < p_len` sets the borrow. -/
def room : List Instr := [.mov .eax (.mem (st leftOff)), .alu .cmp .eax (.mem (argK 0 7))]

def attemptOrRequest : Prog isa := .seq (.block room) (.ite .b request (.seq attempt classify))

def branch : Prog isa :=
  .seq (.block [.mov .eax (.mem (st 0)), .alu .test .eax (.reg .eax)])
    (.ite .e exhausted (.seq (.block [.mov .eax (.mem (st 8)), .alu .test .eax (.reg .eax)])
      (.ite .e exhausted attemptOrRequest)))

/-- The loop goes on while the status is 4, a rejection. -/
def iteration : Prog isa :=
  .seq branch (.block [.mov .eax (.mem (st statusOff)), .alu .cmp .eax (.imm 4)])

/-- `used` written (64 bits), the status returned and the caller's `esi` restored. -/
def finish : List Instr :=
  [.mov .ecx (.mem (argK 0 4)), .mov .eax (.mem (st usedOff)), .store (at_ .ecx 0) .eax, .mov .eax (.imm 0),
    .store (at_ .ecx 4) .eax, .mov .eax (.mem (st statusOff)), .mov .esi (.mem (st savedOff))]

def code : Prog isa := .seq (.block entry) (.seq (.loop iteration .e) (.block finish))

end KeySearch

end VG.Impl.Ffdh.X86
