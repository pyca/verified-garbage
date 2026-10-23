module

public import VerifiedGarbage.Impl.Bignum.Arm.FiosPipelined

/-! Public word counts select fixed scans at the common primality-test and RSA widths. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.FiosFast
open VG VG.Arm VG.Impl.Bignum.Arm

/-- The word counts with a fixed scan: the primes, and the halves of the
moduli in the CRT, of RSA keys of 1024, 2048, 3072, 4096 and 8192 bits. -/
def widths : List Nat := [16, 32, 48, 64, 128]

def choose (n : BitVec 32) : List Instr := [.cmp .lr (.imm n)]

/-- The fixed scan of the first of `ws` that is the count, else the general one. -/
def select : List Nat → Prog isa
  | [] => Fios.code
  | k :: ks => .seq (.block (choose (BitVec.ofNat 32 k))) (.ite .eq (FiosPipelined.code k) (select ks))

def code : Prog isa := select widths
def round : Prog isa := .seq (.block Fios.args) (.seq code (.block roundFinish))

end VG.Impl.Bignum.Arm.FiosFast
