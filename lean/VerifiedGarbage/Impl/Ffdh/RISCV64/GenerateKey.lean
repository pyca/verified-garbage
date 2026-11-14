module

public import VerifiedGarbage.Impl.Ffdh.RISCV64.Derive

/-!
# Finite-field Diffie–Hellman on RISC-V: one key-generation attempt

`vg_ffdh_generate_key(x = a0, x_len = a1, y = a2, y_len = a3, domain = a4,
domain_len = a5, p_len = a6, rand = a7, rand_len, scratch, scratch_len)`
(`Spec/Ffdh/Contract.lean`), the last three on the stack, in the working
space of `vg_ffdh_derive_public` (`Derive.lean`), with `y` as its `y`, x as
its x (`p_len` octets) and the arguments moved to its registers; `rand`'s
address is kept in `t1`:

* p is loaded into array 0 and checked as `vg_ffdh_derive_public` checks it;
  otherwise the result is 0;
* the bound's octets (q's at `domain + 2 p_len`, or p's without q, whose
  first nonzero octet is `p − 1`'s) are scanned without a branch for the
  first nonzero one and its index (`scanBody`), its bits below the highest
  set (`smear`), and `rand`'s `p_len` octets are cut there into `x`: zeros
  before it, and'ed with the smeared octet at it, kept after it (`cutBody`),
  so that x is `scalarOfOctets` of `rand`;
* then as `vg_ffdh_derive_public` (`Derive.dpBody`): the status 2 and zeros
  at `y` for x out of range, else `y = g^x mod p` or zeros and the status 1
  or 3;
* x's octets masked by the status being 1 (`maskX`): zeros but for 1.

The code branches on p's validity, whether there is q and x's range, which
the domain and the status reveal; the scan, the cut and the mask run over
every octet without a branch.
-/

@[expose] public section

namespace VG.Impl.Ffdh.RISCV64.GenerateKey

open VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Ffdh.RISCV64 VG.Impl.Ffdh.RISCV64.Derive
open VG.Impl.Bignum.RISCV64.PublicChecked (base saveRegs restore setup)

/-- `y`, x, `p_len` (x's length) and g's address into the header's words
0–3; `rand` into `t1`, and the arguments moved to `vg_ffdh_derive_public`'s
registers: `y` in `a0`, the domain in `a2` and `s7`, its length in `a3`,
`p_len` in `a1`, `a4`, `a6` and `s8`, x in `a5`. -/
def gkHdr : List Instr :=
  [.store .d .a2 .s6 0, .store .d .a0 .s6 8, .store .d .a6 .s6 16, .add .t2 .a4 .a6, .store .d .t2 .s6 24,
    .addi .t1 .a7 0, .addi .a3 .a5 0, .addi .a5 .a0 0, .addi .a0 .a2 0, .addi .a2 .a4 0, .addi .a4 .a6 0,
    .addi .s7 .a2 0, .addi .s8 .a4 0, .addi .a1 .a4 0]

/-- The working space (the second argument on the stack) into `t0`, the
registers saved there, the header, and `setup`. -/
def gkFront : List Instr := [.addSp .t0 8, .load .d .t0 .t0 0] ++ saveRegs ++ gkHdr ++ setup

/-- `t2 := 0` exactly when `domain_len = 3 p_len`: there is q. -/
def hasQ : List Instr := [.add .t2 .a4 .a4, .add .t2 .t2 .a4, .sub .t2 .a3 .t2]

/-- `t3 :=` the bound's octets: q's (`domain + 2 p_len`), or p's without q. -/
def boundPtr : Prog isa :=
  .seq (.block hasQ) (.ite (.zero .t2) (.block [.add .t3 .a4 .a4, .add .t3 .t3 .a2]) (.block [.addi .t3 .a2 0]))

/-- The scan's start: `p_len` octets (`t5`) from index 0 (`t4`); the index
`p_len − 1` (`s1`), the octet 0 (`s2`) and nothing found (`s3`). -/
def scanSetup : List Instr := [.addi .t5 .a4 0, .li .t4 0, .addi .s1 .a4 (-1), .li .s2 0, .li .s3 0]

/-- One octet `b` of the scan: if it is the first nonzero one (`s4`, all
ones, else 0), its index and itself are kept. -/
def scanBody : List Instr :=
  [.load .b .t6 .t3 0, .li .t2 0, .sub .s4 .t2 .t6, .logic .or .s4 .s4 .t6, .shift .srl .d .s4 .s4 63,
    .sub .s4 .t2 .s4, .logic .or .s4 .s4 .s3, .logic .xor .s4 .s4 .s3,
    .logic .xor .s0 .s1 .t4, .logic .and .s0 .s0 .s4, .logic .xor .s1 .s1 .s0,
    .logic .xor .s0 .s2 .t6, .logic .and .s0 .s0 .s4, .logic .xor .s2 .s2 .s0,
    .logic .or .s3 .s3 .s4, .addi .t3 .t3 1, .addi .t4 .t4 1]

/-- The bits of the octet `s2` below its highest set one, that one too. -/
def smear : List Instr :=
  [.shift .srl .d .t6 .s2 1, .logic .or .s2 .s2 .t6, .shift .srl .d .t6 .s2 2, .logic .or .s2 .s2 .t6,
    .shift .srl .d .t6 .s2 4, .logic .or .s2 .s2 .t6]

/-- The cut's start: `p_len` octets (`t5`) from index 0 (`t4`), x (`a5`) into
`a0`. -/
def cutSetup : List Instr := [.addi .t5 .a4 0, .li .t4 0, .addi .a0 .a5 0]

/-- One octet of `rand` (`t1`) to x (`a0`): and'ed with 0 before the index
`s1`, with the smeared octet `s2` at it, and with 255 after it. -/
def cutBody : List Instr :=
  [.load .b .t6 .t1 0, .li .t2 0, .sub .s4 .t4 .s1, .shift .srl .d .s4 .s4 63, .sub .s4 .t2 .s4,
    .logic .xor .s0 .t4 .s1, .addi .s0 .s0 (-1), .shift .srl .d .s0 .s0 63, .sub .s0 .t2 .s0,
    .li .s3 255, .logic .xor .a1 .s3 .s2, .logic .and .a1 .a1 .s0, .logic .xor .a1 .a1 .s3,
    .logic .or .a1 .a1 .s4, .logic .xor .a1 .a1 .s4, .logic .and .t6 .t6 .a1, .store .b .t6 .a0 0,
    .addi .t1 .t1 1, .addi .a0 .a0 1, .addi .t4 .t4 1]

/-- x := `rand`'s `p_len` octets cut to the bound's bit length, then
`s0 := 0`. -/
def scalar : Prog isa :=
  .seq boundPtr (.seq (.block scanSetup) (.seq (countLoop .t5 scanBody)
    (.seq (.block (smear ++ cutSetup)) (.seq (countLoop .t5 cutBody) (.block [.li .s0 0])))))

/-- `s4 :=` all ones if the status `a0` is 1, else 0, without a branch; x's
address and length (`p_len`) from the header's words 1 and 2 into `a1` and
`t5`. -/
def maskPre : List Instr :=
  [.addi .t2 .a0 (-1), .li .t3 0, .sub .s4 .t3 .t2, .logic .or .s4 .s4 .t2, .shift .srl .d .s4 .s4 63,
    .addi .s4 .s4 (-1), .load .d .a1 .s6 8, .load .d .t5 .s6 16]

/-- x's `p_len` octets (at `a1`) and'ed with the mask `s4`. -/
def maskLoop : Prog isa :=
  countLoop .t5 [.load .b .t6 .a1 0, .logic .and .t6 .t6 .s4, .store .b .t6 .a1 0, .addi .a1 .a1 1]

/-- x's octets and'ed with the mask of the status 1: kept for 1, zeros
otherwise. -/
def maskX : Prog isa := .seq (.block maskPre) maskLoop

/-- After p's check: x, then `vg_ffdh_derive_public`'s body, then zeros at
x but for the status 1. -/
def gkBody : Prog isa := .seq scalar (.seq dpBody maskX)

/-- `vg_ffdh_generate_key`. -/
def generateKey : Prog isa :=
  .seq (.block gkFront) (.seq loadP
    (.seq (.ite (.zero .s0) gkBody (.block [.li .a0 0])) (.block restore)))

end VG.Impl.Ffdh.RISCV64.GenerateKey
