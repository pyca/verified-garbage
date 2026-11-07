module

public import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma
public import VerifiedGarbage.Impl.Rsa.X86_64.PubIfma

/-!
# FFDH's exponentiation with AVX512_IFMA on x86-64

`code mul sp sl`: in a prime's workspace (`rdi`, as `Crt.expLoop`
takes it, `Y = R_X mod X` and `x R_X mod X` in `aXc`), `Y := x^e R_X mod X`
for the exponent of `sl` bytes at the pointer in `n`'s slot `sp`. For a
modulus of 32, 48 or 64 words (2048-, 3072- and 4096-bit groups) and an
exponent of at most `8 W` bytes, one lane of `CrtIfma`'s exponentiation, in
radix `2⁵²` with the multiplication of `PubIfma`'s layouts (`pay2048`,
`pay3072`, `pay4096`, windows of 4 bits): `CrtIfma.region` for the prime
`p` (whose last multiplier, `R_X mod X`, leaves the result in Montgomery
form for `R_X`), the vector code from the exponent's first digit, and
`CrtIfma.result`. Otherwise `Crt.expLoop`.

The area is the room after the workspace's arrays, which `Crt.expLoop` takes
for its table. Intel's MXCSR prologue and epilogue (see "MCDT" in
`TCB/X86_64/Isa.lean`) keep the caller's MXCSR in `r14`, which the vector
code does not write, so that every run restores it.
-/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
  VG.Impl.Rsa.X86_64.Crt VG.Impl.Rsa.X86_64.CrtIfma

variable (l : Lay)

/-- The area's offset in the workspace: after its eight arrays. -/
def oArea : Nat := hdrBytes + 8 * (8 * (l.W + 2))

/-- The first digit of the exponent's windows, after the MXCSR slots. -/
def oSt : Nat := l.oMx + 8

/-- The workspace's `sCtr` while `k1` counts in it. -/
def oSv : Nat := l.oMx + 16

/-- Intel's MXCSR prologue and epilogue around `c`, the caller's MXCSR
(bits 15:0) kept in `r14`, which `c` never writes: the shape of a save and
restore that the proofs check (`ctlOk`). -/
def withMx (c : Prog isa) : Prog isa :=
  .seq (.seq (.block [.stmxcsr (at_ .rbx l.oMx), .mov32 .r14 (.mem (at_ .rbx l.oMx)), .alu32 .and .r14 (.imm 0xFFFF)])
      (.seq (.seq (.block [.mov32 .rax (.imm 0x1FBF), .store32 (at_ .rbx (l.oMx + 4)) .rax,
          .ldmxcsr (at_ .rbx (l.oMx + 4)), .lfence]) (.seq c (.block [.lfence])))
        (.block [.store32 (at_ .rbx l.oMx) .r14, .ldmxcsr (at_ .rbx l.oMx)])))
    (.block [.vop .vzeroupper])

/-- The vector code: `CrtIfma.expLoop` for one lane, from the digit at `oSt`. -/
def vec : Prog isa := withMx l (seqs (expLoop l [.mov .r13 (.mem (at_ .rbx (oSt l)))]))

/-- The area's base into `sIfma`, the first digit with a bit of the
exponent, `2 (P - len)`, at `oSt`, and `sCtr` at `oSv`. -/
def head (sl : Nat) : List Instr :=
  [.mov .r8 (.mem (hdr sCtr)), .mov .rdx (.mem (hdr sLink)), .mov .rcx (.mem (ws .rdx sl)),
    .alu .add .rcx (.reg .rcx), .mov32 .rdx (.imm (BitVec.ofNat 32 (2 * l.P))), .alu .sub .rdx (.reg .rcx),
    .mov .rax (.reg .rdi), .alu .add .rax (.imm (BitVec.ofNat 32 (oArea l))), .store (hdr sIfma) .rax,
    .store (at_ .rax (oSt l)) .rdx, .store (at_ .rax (oSv l)) .r8]

/-- `sCtr` back from `oSv`. -/
def tail : List Instr :=
  [.mov .rax (.mem (hdr sIfma)), .mov .rcx (.mem (at_ .rax (oSv l))), .store (hdr sCtr) .rcx]

/-- The exponentiation of a layout: the region, the vector code, the result. -/
def exp (sp sl : Nat) : List (Prog isa) :=
  [.block (head l sl)] ++ region l 0 sp sl ++ [.block [.mov .rbx (.mem (hdr sIfma))], vec l] ++ result l 0 ++
    [.block (tail l)]

/-- ZF: whether the workspace has `W` words and the exponent at most `8 W` bytes. -/
def fits (sl : Nat) : List Instr :=
  [.mov .rax (.mem (hdr sW)), .alu .xor .rax (.imm (BitVec.ofNat 32 l.W)), .mov .rdx (.mem (hdr sLink)),
    .mov .rdx (.mem (ws .rdx sl)), .alu .cmp .rdx (.imm (BitVec.ofNat 32 (8 * l.W + 1))), .alu .sbb .rcx (.reg .rcx),
    .alu .add .rcx (.imm 1), .alu .or .rax (.reg .rcx)]

/-- The vector code of the first layout that fits, else `Crt.expLoop`. -/
def code (mul : Nat → Nat → Nat → Prog isa) (sp sl : Nat) : List (Prog isa) :=
  [.seq (.block (fits PubIfma.pay2048 sl)) (.ite .e (seqs (exp PubIfma.pay2048 sp sl))
    (.seq (.block (fits PubIfma.pay3072 sl)) (.ite .e (seqs (exp PubIfma.pay3072 sp sl))
      (.seq (.block (fits PubIfma.pay4096 sl)) (.ite .e (seqs (exp PubIfma.pay4096 sp sl))
        (seqs (Crt.expLoop mul tabSelect sp sl)))))))]

end VG.Impl.Ffdh.X86_64.Ifma
