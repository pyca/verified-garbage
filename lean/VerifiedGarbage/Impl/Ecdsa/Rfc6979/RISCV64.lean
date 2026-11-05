module

public import VerifiedGarbage.Impl.Hmac.Stream.RISCV64
public import VerifiedGarbage.Impl.Ecdh.RISCV64
public import VerifiedGarbage.Impl.Ecdh.RISCV64.Num4
public import VerifiedGarbage.Impl.Ecdh.RISCV64.Num0
public import VerifiedGarbage.Impl.Words.RISCV64.Bytes
public import VerifiedGarbage.Impl.Words.RISCV64.Loops
public import VerifiedGarbage.Impl.ICall

/-!
# Deterministic ECDSA (RFC 6979) on RISC-V, with HMAC through a table

`vg_ecdsa_<curve>_sign(out = a0, d = a1, digest = a2, digest_len = a3,
scratch = a4, hmac = a5) -> a0` (`sign`), for a curve of `Q`-byte scalars in
`nw` 64-bit words (`Q = 8 nw`; `8 nw - 4`, a top word of four bytes; `8 nw -
8`, a top word of zero; or P-521's 66 in nine): RFC 6979 §3.2 with HMAC over
the hash function of the table `hmac` of the interface `Hmac`
(`Spec/HmacTable.lean`), whose functions it calls indirectly (`tcall`: the
table's word `j` into `t1`, then `jalr ra, 0(t1)`): HMAC's `init` (word 0),
which keys the inner and outer streaming states, the streaming `update`
(word 1), on the inner state, and HMAC's `finalize` (word 2), which writes
the MAC; and each candidate tried by calling `core`, the signature with a
given `k` (`vg_ecdsa_<curve>_sign_k`), which reads `G` bytes of the digest
(`Q`, or 64 for P-521) and `Q` bytes of `k`, of which it takes the leftmost
`qlen` bits.

One body serves every hash function: the digest length `D` and HMAC's block
size `B` are the table's words of data 4 and 5, which the prologue loads into
`s7` and `s8`, and the code computes the lengths and counts it passes from
them (all public). Nothing in the code depends on the hash function but
those two words and the table's functions.

It runs in a frame of `frB` bytes (`alloc`): our caller's `ra` and
`s0`–`s9`, then `K` and `V` (64 bytes each, of which the first `D` are used,
and the byte after `V` the separator of steps d, f and h.3), `X` (72 bytes),
`h` (64 bytes, unless `big`) and the candidate `T` (136 bytes). Our
variables live in `s0`–`s9`, which the functions we call save and restore:
`s0` = `scratch`, `s1` = the frame, `s2` = `out`, `s3` = `d`, `s4` =
`digest`, `s5` = the candidates left, `s6` = the table, `s7` = `D`, `s8` =
`B` and `s9` = the length of `T`. In `scratch`: HMAC's inner and outer
states (at 0 and 192), which `core` then overwrites. The functions we call
use the stack below the frame.

1. `X`: `Q - min(D, Q)` zero bytes, then the digest's leftmost `min(D, Q)`
   bytes (`prepX`, by a byte loop, `copyLoop`; the minimum by a branch-free
   select from the sign of `D - Q`), a `Q`-byte number: the digest's
   `bits2int`, as `core` reads it (at `fDg`, from `X`'s byte `Q - G`).
2. `h = bits2octets(digest)`: unless `big`, `X` read into `scratch`
   (`loadQ`) and reduced modulo `n` by a call of the order's addition with
   zero (it is below `2^(8 Q) < 2n`), written big-endian to `h`
   (`reduce`); if `big` (P-521, whose scalars are longer than every digest),
   `X` itself, whose number is below `n`.
3. Steps b to g: `V = 0x01…`, `K = 0x00…` (64 bytes each),
   `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`, `V = HMAC_K(V)`,
   `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`, each message absorbed in
   parts from where they are (`V` and the separator, `d`, `h`).
4. At most `tries` times: the candidate `T`, the `V`s of successive
   `V = HMAC_K(V)` while it is shorter than `Q` bytes (`cand`, a loop whose
   count is public, each `V` appended to `T` by `copyLoop`), and
   `core(out, d, X, T, scratch)`; if it failed and candidates are left,
   `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)` and again. Whether to go on, in
   `t6`, is computed without branches from the low bit of `core`'s result,
   so that the code branches only on it: the number of candidates tried is
   all it reveals.

`core` writes the signature or zeros to `out`, and its result is ours. `K`,
`V`, `X`, `h` and `T` are cleared before the frame is freed. Every address
depends only on the pointers and `D`.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Rfc6979.RISCV64

open VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (mov)

/-! Where things are in the frame. -/
def fK : Nat := 96
def fV : Nat := 160
/-- `X` (72 bytes): `h` if `big`. -/
def fX : Nat := 232
/-- `h` (64 bytes), unless `big`. -/
def fH : Nat := 304
/-- The candidate `T` (136 bytes). -/
def fT : Nat := 368
/-- The frame's size. -/
def frB : Nat := 512

/-! Where things are in `scratch`: HMAC's states, and the first number of
`bits2octets`. -/
def sIn : Nat := 0
def sOut : Nat := 192
def sX : Nat := 0

/-- The functions an indirect call of each of a table's functions may
reach: for each of HMAC's `init`, the streaming `update` and HMAC's
`finalize`, that function of every table of the interface, by name. -/
structure Fns where
  init : List (String × Prog isa)
  upd : List (String × Prog isa)
  fin : List (String × Prog isa)

/-- What the code needs of a curve: the functions a table's may be, the
arithmetic modulo the order `n` (`FN`, whose addition `bits2octets` calls),
the signature with a given `k` and its name, the most candidates to try, the
scalars' 64-bit words and their bytes, whether they are longer than every
digest (`big`), and the digest's bytes `core` reads. -/
structure Cfg where
  f : Fns
  FN : Weierstrass.RISCV64.Field
  coreN : String
  coreC : Prog isa
  tries : Nat
  nw : Nat
  Q : Nat := 8 * nw
  big : Bool := false
  G : Nat := Q

/-- Our caller's registers we save, and where, at the start of the frame. -/
def saved : List (Reg × Nat) :=
  [(.ra, 0), (.s0, 8), (.s1, 16), (.s2, 24), (.s3, 32), (.s4, 40), (.s5, 48), (.s6, 56), (.s7, 64),
    (.s8, 72), (.s9, 80)]

/-- Where we restore them from, in order (`s1`, the base, last). -/
def restList : List (Reg × Nat) :=
  [(.ra, 0), (.s0, 8), (.s2, 24), (.s3, 32), (.s4, 40), (.s5, 48), (.s6, 56), (.s7, 64), (.s8, 72),
    (.s9, 80), (.s1, 16)]

/-- A length: `D` (if the flag is set) plus a constant. -/
abbrev Len := Bool × Nat

/-- A part of a message: `len` bytes at `off(base)`. -/
abbrev Part := Reg × Nat × Len

/-- The length of the parts, if at most the first holds `D`. -/
def total : List Part → Len
  | [] => (false, 0)
  | p :: ps => (p.2.2.1 || (total ps).1, p.2.2.2 + (total ps).2)

/-- `d ← B + l` (`B` in `s8`, `D` in `s7`). -/
def cntTo (d : Reg) (l : Len) : List Instr :=
  if l.1 then [.add d .s8 .s7, .addi d d l.2] else [.addi d .s8 l.2]

/-- `d ← l`. -/
def lenTo (d : Reg) (l : Len) : List Instr :=
  if l.1 then [.addi d .s7 l.2] else [.li d l.2]

/-- The call of the table's function `j` (the table in `s6`), among `ts`:
its address into `t1`, then `jalr ra, 0(t1)`. -/
def tcall (j : Nat) (ts : List (String × Prog isa)) : Prog isa :=
  .seq (.block [.load .d .t1 .s6 (8 * j)]) (Code.icalls (.jalr .t1) ts)

namespace Cfg

variable (c : Cfg)

/-- Where `h` is in the frame: `X` itself if `big`. -/
def fHo : Nat := if c.big then fX else fH

/-- Where `core` reads its digest in the frame: `X`'s last `G` bytes. -/
def fDg : Nat := fX + (c.Q - c.G)

/-! The other numbers of `bits2octets` in `scratch`, after `sX`'s. -/
def sZ : Nat := 8 * c.nw
def sY : Nat := 2 * (8 * c.nw)

/-- The `Q`-byte number at `p + off` big-endian to `[o]`. -/
def loadQ (o : Nat) (p : Reg) (off : Nat) : List Instr :=
  if c.Q = 8 * c.nw then Ecdh.RISCV64.loadNum c.nw o p off
  else if c.Q + 4 = 8 * c.nw then Ecdh.RISCV64.loadNum4 (c.nw - 1) o p off
  else Ecdh.RISCV64.loadNum0 (c.nw - 1) o p off

/-- The number at `[a]` under the mask `a7`, to `q + off` big-endian in `Q`
bytes (for a top word of zero, its low `nw - 1` words). -/
def storeQ (a : Nat) (q : Reg) (off : Nat) : List Instr :=
  if c.Q = 8 * c.nw then Ecdh.RISCV64.storeNum c.nw a q off
  else if c.Q + 4 = 8 * c.nw then Ecdh.RISCV64.storeNum4 (c.nw - 1) a q off
  else Ecdh.RISCV64.storeNum (c.nw - 1) a q off

/-- Our caller's registers into the frame, which `s1` then holds; the
arguments into the registers that keep them, and `D` and `B`, the table's
words of data 4 and 5, into `s7` and `s8`. -/
def prologue : List Instr :=
  .addSp .t0 0 :: saved.map (fun (r, d) => .store .d r .t0 d) ++
    [mov .s1 .t0, mov .s2 .a0, mov .s3 .a1, mov .s4 .a2, mov .s0 .a4, mov .s6 .a5, .load .d .s7 .a5 32,
      .load .d .s8 .a5 40]

/-- The arguments of `X`'s copy: `X` cleared; then `a6 = min(D, Q)`
(`Q + ((D - Q) & -(D < Q))`, the comparison the sign of `D - Q`), the digest
in `a4` and `X + Q - a6` in `a5`. -/
def xArgs : List Instr :=
  .li .t0 0 :: (List.range 9).map (fun j => .store .d .t0 .s1 (fX + 8 * j)) ++
    [.li .t1 c.Q, .sub .t2 .s7 .t1, .shift .srl .d .t3 .t2 63, .li .t4 0, .sub .t3 .t4 .t3,
      .logic .and .t2 .t2 .t3, .add .a6 .t1 .t2, mov .a4 .s4, .addi .a5 .s1 (fX + c.Q), .sub .a5 .a5 .a6]

/-- `X`: `Q - min(D, Q)` zero bytes, then the digest's leftmost `min(D, Q)`. -/
def prepX : Prog isa := .seq (.block c.xArgs) (Words.RISCV64.copyLoop .t1 .a4 .a5 .a6)

/-- `h = bits2octets(digest)`, unless `big`: `X` to `scratch`'s `sX`, zero
to `sZ`, their sum modulo `n` to `sY`, and that to `h`. -/
def reduce : Prog isa :=
  .seq (.block (c.loadQ sX .s1 fX ++ Ecdh.RISCV64.setConst c.nw c.sZ 0))
    (.seq (Weierstrass.RISCV64.addCall c.FN c.sY sX c.sZ)
      (.block ([.li .a7 (-1)] ++ c.storeQ c.sY .s1 fH)))

/-- `h`: `reduce`, or, if `big`, `X` itself. -/
def prepH : Prog isa := if c.big then .block [] else c.reduce

/-- `V = 0x01…` and `K = 0x00…`, all 64 bytes of each, a doubleword at a
time (`0x0101…01` built in `t0`, zero in `t1`). -/
def initKV : List Instr :=
  [.li .t0 0x101, .shift .sll .d .t1 .t0 16, .logic .or .t0 .t0 .t1, .shift .sll .d .t1 .t0 32,
    .logic .or .t0 .t0 .t1, .li .t1 0] ++
    (List.range 8).flatMap fun j => [.store .d .t1 .s1 (fK + 8 * j), .store .d .t0 .s1 (fV + 8 * j)]

/-! ## HMAC through the table -/

/-- HMAC's `init`'s arguments: the states, the key `K` of `D` bytes. -/
def initArgs : List Instr := [.addi .a0 .s0 sIn, .addi .a1 .s0 sOut, .addi .a2 .s1 fK, mov .a3 .s7]

/-- The streaming `update`'s arguments for a part, the inner state holding
`B + cnt` bytes. -/
def updArgs (cnt : Len) (p : Part) : List Instr :=
  [.addi .a0 .s0 sIn] ++ cntTo .a1 cnt ++ [.addi .a2 p.1 p.2.1] ++ lenTo .a3 p.2.2

/-- The parts absorbed into the inner state, which holds `B + cnt` bytes. -/
def upds : Len → List Part → Prog isa
  | _, [] => .block []
  | cnt, p :: ps =>
    .seq (.seq (.block (updArgs cnt p)) (tcall 1 c.f.upd))
      (upds (cnt.1 || p.2.2.1, cnt.2 + p.2.2.2) ps)

/-- HMAC's `finalize`'s arguments: the states, the `B + len` bytes the inner
one holds, the MAC's place in the frame. -/
def finArgs (len : Len) (dst : Nat) : List Instr :=
  [.addi .a0 .s0 sIn, .addi .a1 .s0 sOut] ++ cntTo .a2 len ++ [.addi .a3 .s1 dst]

/-- `HMAC_K(parts)` into the frame at `dst`: HMAC's `init` with the key `K`,
`update` with each part, and `finalize`, through the table. -/
def hmac (ps : List Part) (dst : Nat) : Prog isa :=
  .seq (.block initArgs)
  (.seq (tcall 0 c.f.init)
  (.seq (c.upds (false, 0) ps)
  (.seq (.block (finArgs (total ps) dst))
    (tcall 2 c.f.fin))))

/-- `V = HMAC_K(V)`. -/
def hmacV : Prog isa := c.hmac [(.s1, fV, (true, 0))] fV

/-- The separator `b` after `V`, at `V + D`. -/
def sep (b : Nat) : List Instr := [.add .t0 .s1 .s7, .li .t1 b, .store .b .t1 .t0 fV]

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block (sep b))
    (.seq (c.hmac [(.s1, fV, (true, 1)), (.s3, 0, (false, c.Q)), (.s1, c.fHo, (false, c.Q))] fK) c.hmacV)

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block (sep 0)) (.seq (c.hmac [(.s1, fV, (true, 1))] fK) c.hmacV)

/-- The candidates left. -/
def initCnt : List Instr := [.li .s5 c.tries]

/-! ## The candidates -/

/-- `T` empty. -/
def tInit : List Instr := [.li .s9 0]

/-- The arguments of `V`'s copy to the end of `T`: `V` in `a4`, `T + |T|`
in `a5` and `D` in `a6`. -/
def keepArgs : List Instr := [.addi .a4 .s1 fV, .addi .a5 .s1 fT, .add .a5 .a5 .s9, mov .a6 .s7]

/-- `T` longer by `D` bytes, and `t6 ≠ 0` iff it is still shorter than `Q`. -/
def tStep : List Instr := [.add .s9 .s9 .s7, .li .t0 c.Q, .sltu .t6 .s9 .t0]

/-- One `V` of the candidate: `V = HMAC_K(V)`, appended to `T`. -/
def candStep : Prog isa :=
  .seq c.hmacV (.seq (.block keepArgs) (.seq (Words.RISCV64.copyLoop .t1 .a4 .a5 .a6) (.block c.tStep)))

/-- The candidate: `T`, the `V`s of successive `V = HMAC_K(V)` while it is
shorter than `Q` bytes. -/
def cand : Prog isa := .seq (.block tInit) (.loop c.candStep (.nonzero .t6))

/-- `core(out, d, X, k = T, scratch)`. -/
def coreArgs : List Instr := [mov .a0 .s2, mov .a1 .s3, .addi .a2 .s1 c.fDg, .addi .a3 .s1 fT, mov .a4 .s0]

/-- One candidate fewer, and `t6 ≠ 0` iff the signature failed (the low bit
of `a0` is 0) and candidates are left: `t6 = ((a0 & 1) - 1) & s5`. -/
def goOn : List Instr :=
  [.addi .s5 .s5 (-1), .logicImm .and .t0 .a0 1, .addi .t0 .t0 (-1), .logic .and .t6 .t0 .s5]

/-- Go on. -/
def again : List Instr := [.li .t6 1]

/-- Stop. -/
def stop : List Instr := [.li .t6 0]

/-- One candidate: `cand`, `core` with it, then, if it failed and
candidates are left, step h.3. -/
def tryOne : Prog isa :=
  .seq c.cand
  (.seq (.block c.coreArgs)
  (.seq (.call c.coreN c.coreC)
  (.seq (.block goOn)
    (.ite (.nonzero .t6) (.seq c.rekey (.block again)) (.block stop)))))

/-- `K`, `V`, `X`, `h` and `T` cleared. -/
def wipe : List Instr :=
  .li .t0 0 :: (List.range ((fT + 136 - fK) / 8)).map fun j => .store .d .t0 .s1 (fK + 8 * j)

/-- Restore our caller's registers. -/
def restore : List Instr := restList.map fun (r, d) => .load .d r .s1 d

/-- The frame's body. -/
def main : Prog isa :=
  .seq (.block prologue)
  (.seq c.prepX
  (.seq c.prepH
  (.seq (.block initKV)
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne (.nonzero .t6))
    (.block (wipe ++ restore)))))))))

/-- `vg_ecdsa_<curve>_sign`. -/
def sign : Prog isa := .frame (.alloc frB) c.main (.free frB)

end Cfg

end VG.Impl.Ecdsa.Rfc6979.RISCV64
