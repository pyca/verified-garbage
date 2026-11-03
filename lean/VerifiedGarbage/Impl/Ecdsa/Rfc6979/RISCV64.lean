module

public import VerifiedGarbage.Impl.Hmac.Stream.RISCV64
public import VerifiedGarbage.Impl.Ecdh.RISCV64
public import VerifiedGarbage.Impl.Ecdh.RISCV64.Num4
public import VerifiedGarbage.Impl.Ecdh.RISCV64.Num0
public import VerifiedGarbage.Impl.Words.RISCV64.Bytes

/-!
# Deterministic ECDSA (RFC 6979) on RISC-V

`sign(out = a0, d = a1, digest = a2, scratch = a3) -> a0`: RFC 6979 §3.2
for a curve of scalars of `Q` bytes in `nw` 64-bit words (`Q = 8 nw`;
`8 nw - 4`, a top word of four bytes; or `8 nw - 8`, a top word of zero:
P-256's 32, P-384's 48, P-224's 28, P-192's 24) whose order `n` has `8 Q`
bits, and a
Merkle–Damgård hash function `H` whose output is `D ≥ Q` bytes, with HMAC
computed by calling `H`'s HMAC `init` and `finalize` and its streaming
`update` (`Impl/Hmac/Stream/RISCV64.lean`), and each candidate tried by
calling `core`, the signature with a given `k` (`vg_ecdsa_<curve>_sign`),
which reads `Q` bytes of the digest and of `k`. One `V` makes a candidate,
its leftmost `Q` bytes, so `core` reads the digest and `V` in place.

It runs in a frame of `fH + 8 nw` bytes rounded up to 16 (`alloc`): our
caller's `ra` and `s0`–`s5`, then `K` and `V` (64 bytes each, of which the
first `D` are used, and the byte after `V` the separator of steps d, f and
h.3) and `h` (`Q` bytes, in `8 nw`) at `fH`: 192, or 208 when `D` is 64 and
the separator is byte 192. Our
variables live in `s0`–`s5`, which the functions we call save and restore:
`s0` = `scratch`, `s1` = the frame, `s2` = `out`, `s3` = `d`, `s4` =
`digest` and `s5` = the candidates left. In `scratch`: HMAC's inner and
outer states (at 0 and 192), which `core` then overwrites. The functions we
call use the stack below the frame.

1. `h = bits2octets(digest)`: the leftmost `Q` bytes, big-endian, read into
   `scratch` (`loadNum`, `loadNum4` for a top word of four bytes, or
   `loadNum0` for a top word of zero) and reduced modulo `n` by a call of the order's addition with
   zero (they are below `2^(8 Q) < 2n`), then written big-endian to `h`.
2. Steps b to g: `V = 0x01…`, `K = 0x00…`, `K = HMAC_K(V ‖ 0x00 ‖ d ‖ h)`,
   `V = HMAC_K(V)`, `K = HMAC_K(V ‖ 0x01 ‖ d ‖ h)`, `V = HMAC_K(V)`, each
   message absorbed in parts from where they are (`V` and the separator, `d`,
   `h`).
3. At most `tries` times: `V = HMAC_K(V)`, which is `k`, and
   `core(out, d, digest, k, scratch)`; if it failed and candidates are left,
   `K = HMAC_K(V ‖ 0x00)`, `V = HMAC_K(V)` and again. Whether to go on, in
   `t6`, is computed without branches from the low bit of `core`'s result
   (the bits its contract determines), so that the code branches only on it:
   the number of candidates tried is all it reveals.

`core` writes the signature or zeros to `out`, and its result is ours. `K`,
`V` and `h` are cleared before the frame is freed. Every address depends
only on the pointers.

If the scalars are longer than the hash's output (`wide`: P-521's 66 bytes
with SHA-512's 64), `core` reads the digest's `D` bytes and the candidate's
leftmost `Q` bytes, and takes the leftmost bits of each as `e` and `k`, as
the specification's `bits2int` does; the frame has the candidate's `Q`
bytes after `h`, at `fT`:

1. `h` is the digest after `Q - D` zero bytes: its number is below
   `2^(8 D) < n`, which `bits2octets` keeps.
2. A candidate is `T = V₁ ‖ V₂`, two `V = HMAC_K(V)`: `V₁` to `fT`, `V₂`
   from it to `V`'s place, and the first `Q - D` bytes of `V₂` after `V₁`.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Rfc6979.RISCV64

open VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)

/-! Where things are in the frame. -/
def fK : Nat := 64
def fV : Nat := 128

/-! Where things are in `scratch`: HMAC's states, and the first number of
`bits2octets`. -/
def sIn : Nat := 0
def sOut : Nat := 192
def sX : Nat := 0

/-- What the code needs: the hash function's streaming functions with
HMAC's `init` and `finalize` over them (`H`) and their names, the arithmetic
modulo the order `n` (`FN`, whose addition `bits2octets` calls), the
signature with a given `k` and its name, the most candidates to try, the
scalars' 64-bit words and their bytes. -/
structure Cfg where
  H : Hash
  hiN : String
  hfN : String
  FN : Weierstrass.RISCV64.Field
  coreN : String
  coreC : Prog isa
  tries : Nat
  nw : Nat
  Q : Nat := 8 * nw

/-- Our caller's registers we save, and where, at the start of the frame. -/
def saved : List (Reg × Nat) :=
  [(.ra, 0), (.s0, 8), (.s1, 16), (.s2, 24), (.s3, 32), (.s4, 40), (.s5, 48)]

/-- Where we restore them from, in order (`s1`, the base, last). -/
def restList : List (Reg × Nat) :=
  [(.ra, 0), (.s0, 8), (.s2, 24), (.s3, 32), (.s4, 40), (.s5, 48), (.s1, 16)]

/-- A part of a message: `len` bytes at `off(base)`. -/
abbrev Part := Reg × Nat × Nat

/-- The bytes of the parts. -/
def total : List Part → Nat
  | [] => 0
  | p :: ps => p.2.2 + total ps

namespace Cfg

variable (c : Cfg)

/-- Where `h` is in the frame: after `V` and its separator. -/
def fH : Nat := if c.H.D < 64 then 192 else 208

/-- Whether the scalars are longer than the hash's output. -/
def wide : Bool := decide (c.H.D < c.Q)

/-- If `wide`: the candidate, after `h`. -/
def fT : Nat := c.fH + 8 * c.nw

/-- The numbers in the frame from `fH` on: `h`, and if `wide` the
candidate. -/
def nums : Nat := if c.wide then 2 else 1

/-- The frame's size: the numbers' words after `fH`, rounded up to a
multiple of 16. -/
def frB : Nat := (c.fH + 8 * c.nw * c.nums + 15) / 16 * 16

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
arguments into the registers that keep them. -/
def prologue : List Instr :=
  .addSp .t0 0 :: saved.map (fun (r, d) => .store .d r .t0 d) ++
    [mov .s1 .t0, mov .s2 .a0, mov .s3 .a1, mov .s4 .a2, mov .s0 .a3]

/-- If `wide`: `h`, the digest after `Q - D` zero bytes. -/
def reduceW : List Instr :=
  Words.RISCV64.storeBytes .t0 .s1 c.fH (List.replicate (c.Q - c.H.D) 0) ++
    Words.RISCV64.copyBytes .t0 .s4 .s1 0 (c.fH + (c.Q - c.H.D)) c.H.D

/-- `h = bits2octets(digest)`: the digest's leftmost `Q` bytes to `scratch`'s
`sX`, zero to `sZ`, their sum modulo `n` to `sY`, and that to `h`; or, if
`wide`, `reduceW`. -/
def reduce : Prog isa :=
  if c.wide then .block c.reduceW else
  .seq (.block (c.loadQ sX .s4 0 ++ Ecdh.RISCV64.setConst c.nw c.sZ 0))
    (.seq (Weierstrass.RISCV64.addCall c.FN c.sY sX c.sZ)
      (.block ([.li .a7 (-1)] ++ c.storeQ c.sY .s1 c.fH)))

/-- `K = 0x00…`, `V = 0x01…`, `D` bytes each. -/
def initKV : List Instr :=
  Words.RISCV64.storeBytes .t0 .s1 fK (List.replicate c.H.D 0) ++
    Words.RISCV64.storeBytes .t0 .s1 fV (List.replicate c.H.D 1)

/-- HMAC's `init`'s arguments: the states, the key `K`. -/
def initArgs : List Instr := [.addi .a0 .s0 sIn, .addi .a1 .s0 sOut, .addi .a2 .s1 fK, .li .a3 c.H.D]

/-- The streaming `update`'s arguments for a part, the inner state holding
`B + cnt` bytes. -/
def updArgs (cnt : Nat) (p : Part) : List Instr :=
  [.addi .a0 .s0 sIn, .li .a1 (c.H.B + cnt), .addi .a2 p.1 p.2.1, .li .a3 p.2.2]

/-- The parts absorbed into the inner state, which holds `B + cnt` bytes. -/
def upds : Nat → List Part → Prog isa
  | _, [] => .block []
  | cnt, p :: ps => .seq (.seq (.block (c.updArgs cnt p)) c.H.callUpd) (upds (cnt + p.2.2) ps)

/-- HMAC's `finalize`'s arguments: the states, the bytes the inner one holds,
the MAC's place in the frame. -/
def finArgs (len dst : Nat) : List Instr :=
  [.addi .a0 .s0 sIn, .addi .a1 .s0 sOut, .li .a2 (c.H.B + len), .addi .a3 .s1 dst]

/-- `HMAC_K(parts)` into the frame at `dst`: HMAC's `init` with the key `K`,
`update` with each part, and `finalize`. -/
def hmac (ps : List Part) (dst : Nat) : Prog isa :=
  .seq (.block c.initArgs)
  (.seq (.call c.hiN c.H.init)
  (.seq (c.upds 0 ps)
  (.seq (.block (c.finArgs (total ps) dst))
    (.call c.hfN c.H.finalize))))

/-- `V = HMAC_K(V)`. -/
def hmacV : Prog isa := c.hmac [(.s1, fV, c.H.D)] fV

/-- The separator `b` after `V`. -/
def sep (b : Nat) : List Instr := Words.RISCV64.storeBytes .t0 .s1 (fV + c.H.D) [b]

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block (c.sep b))
    (.seq (c.hmac [(.s1, fV, c.H.D + 1), (.s3, 0, c.Q), (.s1, c.fH, c.Q)] fK) c.hmacV)

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block (c.sep 0)) (.seq (c.hmac [(.s1, fV, c.H.D + 1)] fK) c.hmacV)

/-- The candidates left. -/
def initCnt : List Instr := [.li .s5 c.tries]

/-- `core(out, d, digest, k = V, scratch)`. -/
def coreArgs : List Instr := [mov .a0 .s2, mov .a1 .s3, mov .a2 .s4, .addi .a3 .s1 fV, mov .a4 .s0]

/-- If `wide`: `core(out, d, digest, k = fT, scratch)`. -/
def coreArgsW : List Instr := [mov .a0 .s2, mov .a1 .s3, mov .a2 .s4, .addi .a3 .s1 c.fT, mov .a4 .s0]

/-- If `wide`, the candidate: `V₁ = HMAC_K(V)` to `fT`, `V₂ = HMAC_K(V₁)` to
`V`'s place, and `V₂`'s first `Q - D` bytes after `V₁`. -/
def candW : Prog isa :=
  .seq (c.hmac [(.s1, fV, c.H.D)] c.fT)
  (.seq (c.hmac [(.s1, c.fT, c.H.D)] fV)
    (.block (Words.RISCV64.copyBytes .t0 .s1 .s1 fV (c.fT + c.H.D) (c.Q - c.H.D))))

/-- One candidate fewer, and `t6 ≠ 0` iff the signature failed (the low bit
of `a0` is 0) and candidates are left: `t6 = ((a0 & 1) - 1) & s5`. -/
def goOn : List Instr :=
  [.addi .s5 .s5 (-1), .logicImm .and .t0 .a0 1, .addi .t0 .t0 (-1), .logic .and .t6 .t0 .s5]

/-- Go on. -/
def again : List Instr := [.li .t6 1]

/-- Stop. -/
def stop : List Instr := [.li .t6 0]

/-- One candidate: `V = HMAC_K(V)` (or, if `wide`, `candW`), `core` with
it, then, if it failed and candidates are left, step h.3. -/
def tryOne : Prog isa :=
  .seq (if c.wide then c.candW else c.hmacV)
  (.seq (.block (if c.wide then c.coreArgsW else coreArgs))
  (.seq (.call c.coreN c.coreC)
  (.seq (.block goOn)
    (.ite (.nonzero .t6) (.seq c.rekey (.block again)) (.block stop)))))

/-- `K`, `V` and the numbers cleared. -/
def wipe : List Instr :=
  .li .t0 0 :: (List.range ((c.fH - fK) / 8 + c.nw * c.nums)).map fun j => .store .d .t0 .s1 (fK + 8 * j)

/-- Restore our caller's registers. -/
def restore : List Instr := restList.map fun (r, d) => .load .d r .s1 d

/-- The frame's body. -/
def main : Prog isa :=
  .seq (.block prologue)
  (.seq c.reduce
  (.seq (.block c.initKV)
  (.seq (c.rekeyFull 0)
  (.seq (c.rekeyFull 1)
  (.seq (.block c.initCnt)
  (.seq (.loop c.tryOne (.nonzero .t6))
    (.block (c.wipe ++ restore))))))))

/-- `vg_ecdsa_<curve>_<hash>_sign`. -/
def sign : Prog isa := .frame (.alloc c.frB) c.main (.free c.frB)

end Cfg

end VG.Impl.Ecdsa.Rfc6979.RISCV64
