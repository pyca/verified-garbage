module
public import VerifiedGarbage.Impl.Bignum.X86_64
public import VerifiedGarbage.Impl.Rsa.X86_64.Crt
public import VerifiedGarbage.Impl.Rsa.X86_64


/-! # Workspace representation shared by RSA and FFDH Miller–Rabin -/

@[expose] public section

namespace VG.Impl.RsaKeyGen.X86_64.Candidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64

/-! ## Header slots -/

def kOut : Nat := sFn 0
def kLen : Nat := sFn 1
def kUsedP : Nat := sFn 2
def kE : Nat := sFn 3
def kElen : Nat := sFn 4
def kP : Nat := sFn 5
def kPlen : Nat := sFn 6
def kRand : Nat := sFn 7
def kRandLen : Nat := sFn 8
/-- The octets of `rand` read so far. -/
def kUsed : Nat := sFn 9
/-- Three slots for each phase's counters. -/
def kT0 : Nat := sFn 10
def kT1 : Nat := sFn 11
def kT2 : Nat := sFn 12
/-- Miller–Rabin's state: what became of the last witness. -/
def kStat : Nat := sFn 13
/-- The mask of the witness being uniform. -/
def kU : Nat := sFn 14
/-- `gcd(c − 1, e)`. -/
def kG : Nat := sFn 15

/-- Miller–Rabin's slots, once `e` and `p` are no longer needed: the uniform
witnesses it needs, the witnesses so far plus one, the uniform ones, the
flag, the word of `c` being scanned, the words left and the bits left. -/
def kChecks : Nat := kE
def kI : Nat := kElen
def kUni : Nat := kP
def kFlag : Nat := kPlen
def kV : Nat := kT0
def kWords : Nat := kT1
def kBits : Nat := kT2

/-! ## Arrays

Besides `vg_rsa_public`'s eight: Miller–Rabin's table of the powers
`T_j = b^j R mod c` (`j < 16`, entry `j` the array `aT0 + j`, so `aB`, the
witness in Montgomery form, is `T_1`), the exponent `(c − 1) / 2^σ`
(`aE`, with the lowest set bit of `c − 1`'s lowest nonzero word after its
`w` words), `R mod c` (`aR1`) and `c − R mod c` (`aRm1`); the table of
small primes (`aTab`) overlaps Miller–Rabin's table, which is written only
after trial division. `aX` holds `p`, then `c − 1`, then the witness. -/

def aT0 : Nat := 8
def aB : Nat := 9
def aE : Nat := 24
def aR1 : Nat := 25
def aRm1 : Nat := 26
def aTab : Nat := 11

/-- The base of array `j ≥ 7` into `r`: array 7's plus `j − 7` arrays of
`8 (w + 2)` bytes. Clobbers `rax`. -/
def extBase (j : Nat) (r : Reg) : List Instr :=
  ([.mov .rax (.mem (hdr sW)), .alu .add .rax (.imm 2), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .mov r (.mem (hdr (sArr aOne)))] : List Instr) ++
      List.replicate (j - 7) (.alu .add r (.reg .rax))

end VG.Impl.RsaKeyGen.X86_64.Candidate
