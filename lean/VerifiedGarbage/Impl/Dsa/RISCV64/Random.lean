module

public import VerifiedGarbage.Impl.Dsa.RISCV64.Common

/-!
# DSA on RISC-V: the frame of the randomized functions, and rejection sampling

As on PPC64LE (`Impl/Dsa/PPC64LE/Random.lean`), `vg_dsa_sign_random` and
`vg_dsa_generate_key` run in a frame of `frameBytes` bytes on the stack,
which holds:

* at `sp`, the arguments on the stack of the function they call
  (`vg_dsa_sign`'s `digest_len`, `scratch` and `scratch_len`, or
  `vg_dsa_derive_key`'s `scratch_len`), written once on entry;
* at `sp + oNonce`, the 32 octets of the nonce (or of x), the sampled
  scalar's `q_len` octets, big-endian, zeroed on entry and on exit;
* at `sp + oOut`, `sp + oUsed` and `sp + oDig`, `out`, `used` and the
  digest's address, which only the call and the exit read;
* at `sp + oSave`, our caller's `s0`–`s11` and our return address.

The state lives in the callee-saved registers, which the calls keep: `s1`
the key (or the domain p||q||g), `s2` the lengths `p_len | q_len << 16`,
`s3` `rand`, `s4` `rand_len`, `s5` the octets of `rand` consumed, `s6` the
attempts left, `s7` the address of q's first significant octet, `s8` their
count (the width of a draw), `s9` the mask of its significant bits, `s10`
the status (4 while sampling or signing goes on), `s11` the draws left.

`prepare` scans q (public): its significant octets (`sigLen`), the address
of the first, the mask of its bits (smeared right) and `a0 ≠ 0` exactly
when `q > 1`. `sample` draws up to 128 candidates of `s8` octets from
`rand + s5`: each is copied, its first octet masked, to the nonce's last
`s8` octets (the others stay zero), and compared with q (a borrow chain
and an or of the octets, without a branch); it leaves the status 1
(accepted), 2 (short tape) or 0 (128 rejections). Only the tape's length,
the count of draws and each candidate's acceptance reach a branch or an
address, as the contracts allow.
-/

@[expose] public section

namespace VG.Impl.Dsa.RISCV64.Random

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64

/-! ## The frame -/

/-- The size of the frame. -/
def frameBytes : Nat := 192

/-- The nonce's 32 octets. -/
def oNonce : Nat := 32

/-- `out`, `used` and the digest's address. -/
def oOut : Nat := 64
def oUsed : Nat := 72
def oDig : Nat := 80

/-- Our caller's `s0`–`s11`, then our return address. -/
def oSave : Nat := 88

/-- The callee-saved registers saved. -/
def cs (i : Nat) : Reg :=
  [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11].getD i .s0

/-- Save `s0`–`s11` and the return address, through `t0 = sp`. -/
def saveRegs : List Instr :=
  [.addSp .t0 0] ++ (List.range 12).flatMap (fun i => [.store .d (cs i) .t0 (oSave + 8 * i)]) ++
    [.store .d .ra .t0 (oSave + 96)]

/-- Zero the nonce's 32 octets, through `t0 = sp`. -/
def clearNonce : List Instr :=
  [.addSp .t0 0, .li .t1 0, .store .d .t1 .t0 oNonce, .store .d .t1 .t0 (oNonce + 8),
    .store .d .t1 .t0 (oNonce + 16), .store .d .t1 .t0 (oNonce + 24)]

/-- Restore the return address and `s0`–`s11`. -/
def restoreRegs : List Instr :=
  [.addSp .t0 0, .load .d .ra .t0 (oSave + 96)] ++
    (List.range 12).flatMap (fun i => [.load .d (cs i) .t0 (oSave + 8 * i)])

/-- `rd := p_len`. -/
def lenP (rd : Reg) : List Instr := [.shift .sll .d rd .s2 48, .shift .srl .d rd rd 48]

/-- `rd := q_len`. -/
def lenQ (rd : Reg) : List Instr := [.shift .srl .d rd .s2 16]

/-! ## The scan of q -/

/-- With q's `q_len` octets at `s7` (`s8 = q_len`): `s8 :=` its significant
octets, `s7 :=` the address of the first, `s9 :=` the mask of its
significant bits, and `a0 ≠ 0` exactly when `q > 1` (two significant
octets, or a first one of at least 2). -/
def prepare : Prog isa :=
  .seq sigLen (.block [.add .t3 .s7 .s8, .sub .s7 .t3 .a1, .addi .s8 .a1 0, .load .b .t4 .s7 0,
    .shift .srl .d .t5 .t4 1, .logic .or .s9 .t4 .t5, .shift .srl .d .t5 .s9 2, .logic .or .s9 .s9 .t5,
    .shift .srl .d .t5 .s9 4, .logic .or .s9 .s9 .t5,
    .shift .srl .d .t5 .a1 1, .shift .srl .d .a2 .t4 1, .logic .or .t5 .t5 .a2, .li .a2 0, .sub .t5 .a2 .t5,
    .shift .srl .d .t5 .t5 63, .sub .a2 .a2 .a1, .shift .srl .d .a2 .a2 63, .logic .and .a0 .t5 .a2])

/-- The scan of q at `s1 + p_len` (`q_len` octets). -/
def prepareQ : Prog isa := .seq (.block (lenP .t3 ++ [.add .s7 .s1 .t3] ++ lenQ .s8)) prepare

/-! ## A draw -/

/-- `a0 := 1` exactly when the tape has fewer than `s8` octets left:
`rand_len − used < width`, by the sign of the difference unless the
octets left are `2⁶³` or more. -/
def shortTest : List Instr :=
  [.sub .a0 .s4 .s5, .sub .a1 .a0 .s8, .shift .srl .d .a1 .a1 63, .shift .srl .d .a0 .a0 63,
    .logicImm .xor .a0 .a0 1, .logic .and .a0 .a0 .a1]

/-- The draw's place: the tape at `rand + used` (`t3`), the nonce's last
`s8` octets (`t4`), the count (`t5`) and the first octet's mask (`t2`). -/
def copyInit : List Instr :=
  [.add .t3 .s3 .s5, .addSp .t4 oNonce] ++ lenQ .a2 ++ [.add .t4 .t4 .a2, .sub .t4 .t4 .s8, .addi .t5 .s8 0,
    .addi .t2 .s9 0]

/-- An octet of the draw, masked by `t2`, which is all ones after the first. -/
def copyByte : List Instr :=
  [.load .b .a0 .t3 0, .logic .and .a0 .a0 .t2, .store .b .a0 .t4 0, .li .t2 255, .addi .t3 .t3 1,
    .addi .t4 .t4 1]

/-- The draw into the nonce, and the octets consumed. -/
def copy : Prog isa :=
  .seq (.block copyInit) (.seq (countLoop .t5 copyByte) (.block [.add .s5 .s5 .s8]))

/-- The comparison from the ends: the nonce (`t3`) and q (`t4`), `s8`
octets; `a3` the borrow, `a4` the or of the nonce's octets. -/
def rangeInit : List Instr :=
  [.addSp .t3 oNonce] ++ lenQ .a2 ++ [.add .t3 .t3 .a2, .add .t4 .s7 .s8, .addi .t5 .s8 0, .li .a3 0,
    .li .a4 0]

/-- An octet of the comparison, from the least significant. -/
def rangeByte : List Instr :=
  [.addi .t3 .t3 (-1), .addi .t4 .t4 (-1), .load .b .a0 .t3 0, .logic .or .a4 .a4 .a0, .load .b .a5 .t4 0,
    .add .a5 .a5 .a3, .sub .a0 .a0 .a5, .shift .srl .d .a3 .a0 63]

/-- `a3 := 1` exactly when the candidate is below q and not zero. -/
def rangeFinish : List Instr :=
  [.li .a0 0, .sub .a0 .a0 .a4, .shift .srl .d .a0 .a0 63, .logic .and .a3 .a3 .a0]

/-- Whether the candidate is accepted, into `a3`. -/
def inRange : Prog isa :=
  .seq (.block rangeInit) (.seq (countLoop .t5 rangeByte) (.block rangeFinish))

/-- Accepted: status 1; otherwise a draw of the budget (`s11`) is spent,
and the status is 0 once none is left. -/
def drawFinish : Prog isa :=
  .ite (.nonzero .a3) (.block [.li .s10 1])
    (.seq (.block [.addi .s11 .s11 (-1)]) (.ite (.zero .s11) (.block [.li .s10 0]) (.block [])))

/-- One draw: a short tape (status 2), or a candidate. -/
def draw : Prog isa :=
  .seq (.block shortTest) (.ite (.nonzero .a0) (.block [.li .s10 2]) (.seq (.seq copy inRange) drawFinish))

/-- Up to 128 draws, while the status is 4. -/
def sample : Prog isa :=
  .seq (.block [.li .s11 128, .li .s10 4]) (.loop (.seq draw (.block [.addi .a0 .s10 (-4)])) (.zero .a0))

/-! ## The exit -/

/-- `out`'s `t5` octets := 0 (`t5 > 0`; `len` computes it). -/
def zeroOut (len : List Instr) : Prog isa :=
  .seq (.block ([.addSp .t3 0, .load .d .t4 .t3 oOut] ++ len ++ [.li .a0 0]))
    (countLoop .t5 [.store .b .a0 .t4 0, .addi .t4 .t4 1])

/-- Unless the status is 1, `out` (`len` computes its length into `t5`) is
zeroed; then the nonce, the octets consumed to `used`, the status, and the
registers. -/
def finish (len : List Instr) : Prog isa :=
  .seq (.block [.addi .a0 .s10 (-1)]) (.seq (.ite (.zero .a0) (.block []) (zeroOut len))
    (.block (clearNonce ++ [.load .d .t4 .t0 oUsed, .store .d .s5 .t4 0, .addi .a0 .s10 0] ++ restoreRegs)))

end VG.Impl.Dsa.RISCV64.Random
