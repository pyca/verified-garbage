module

public import VerifiedGarbage.Impl.Hmac.Stream.RISCV64
public import VerifiedGarbage.Impl.Ecdh.RISCV64
public import VerifiedGarbage.Impl.Words.RISCV64.Bytes

/-!
# Deterministic ECDSA (RFC 6979) on RISC-V

`sign(out = a0, d = a1, digest = a2, scratch = a3) -> a0`: RFC 6979 §3.2
for a curve of 32-byte scalars whose order `n` has 256 bits (P-256), and a
Merkle–Damgård hash function `H` whose output is `D ≥ 32` bytes, with HMAC
computed by calling `H`'s HMAC `init` and `finalize` and its streaming
`update` (`Impl/Hmac/Stream/RISCV64.lean`), and each candidate tried by
calling `core`, the signature with a given `k` (`vg_ecdsa_<curve>_sign`),
which reads 32 bytes of the digest and of `k`. One `V` makes a candidate,
its leftmost 32 bytes, so `core` reads the digest and `V` in place.

It runs in a frame of 224 bytes (`alloc`): our caller's `ra` and `s0`–`s5`,
then `K` and `V` (64 bytes each, of which the first `D` are used, and the
byte after `V` the separator of steps d, f and h.3) and `h` (32 bytes). Our
variables live in `s0`–`s5`, which the functions we call save and restore:
`s0` = `scratch`, `s1` = the frame, `s2` = `out`, `s3` = `d`, `s4` =
`digest` and `s5` = the candidates left. In `scratch`: HMAC's inner and
outer states (at 0 and 192), which `core` then overwrites. The functions we
call use the stack below the frame.

1. `h = bits2octets(digest)`: the leftmost 32 bytes, big-endian, read into
   `scratch` and reduced modulo `n` by a call of the order's addition with
   zero (they are below `2^256 < 2n`), then written big-endian to `h`.
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
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Rfc6979.RISCV64

open VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)

/-! Where things are in the frame. -/
def fK : Nat := 64
def fV : Nat := 128
def fH : Nat := 192
/-- The frame's size, a multiple of 16. -/
def frB : Nat := 224

/-! Where things are in `scratch`: HMAC's states, and the numbers of
`bits2octets`. -/
def sIn : Nat := 0
def sOut : Nat := 192
def sX : Nat := 0
def sZ : Nat := 32
def sY : Nat := 64

/-- What the code needs: the hash function's streaming functions with
HMAC's `init` and `finalize` over them (`H`) and their names, the arithmetic
modulo the order `n` (`FN`, whose addition `bits2octets` calls), the
signature with a given `k` and its name, and the most candidates to try. -/
structure Cfg where
  H : Hash
  hiN : String
  hfN : String
  FN : Weierstrass.RISCV64.Field
  coreN : String
  coreC : Prog isa
  tries : Nat

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

/-- Our caller's registers into the frame, which `s1` then holds; the
arguments into the registers that keep them. -/
def prologue : List Instr :=
  .addSp .t0 0 :: saved.map (fun (r, d) => .store .d r .t0 d) ++
    [mov .s1 .t0, mov .s2 .a0, mov .s3 .a1, mov .s4 .a2, mov .s0 .a3]

/-- `h = bits2octets(digest)`: the digest's leftmost 32 bytes to `scratch`'s
`sX`, zero to `sZ`, their sum modulo `n` to `sY`, and that to `h`. -/
def reduce : Prog isa :=
  .seq (.block (Ecdh.RISCV64.loadNum 4 sX .s4 0 ++ Ecdh.RISCV64.setConst 4 sZ 0))
    (.seq (Weierstrass.RISCV64.addCall c.FN sY sX sZ)
      (.block ([.li .a7 (-1)] ++ Ecdh.RISCV64.storeNum 4 sY .s1 fH)))

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
    (.seq (c.hmac [(.s1, fV, c.H.D + 1), (.s3, 0, 32), (.s1, fH, 32)] fK) c.hmacV)

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block (c.sep 0)) (.seq (c.hmac [(.s1, fV, c.H.D + 1)] fK) c.hmacV)

/-- The candidates left. -/
def initCnt : List Instr := [.li .s5 c.tries]

/-- `core(out, d, digest, k = V, scratch)`. -/
def coreArgs : List Instr := [mov .a0 .s2, mov .a1 .s3, mov .a2 .s4, .addi .a3 .s1 fV, mov .a4 .s0]

/-- One candidate fewer, and `t6 ≠ 0` iff the signature failed (the low bit
of `a0` is 0) and candidates are left: `t6 = ((a0 & 1) - 1) & s5`. -/
def goOn : List Instr :=
  [.addi .s5 .s5 (-1), .logicImm .and .t0 .a0 1, .addi .t0 .t0 (-1), .logic .and .t6 .t0 .s5]

/-- Go on. -/
def again : List Instr := [.li .t6 1]

/-- Stop. -/
def stop : List Instr := [.li .t6 0]

/-- One candidate: `V = HMAC_K(V)`, `core` with it, then, if it failed and
candidates are left, step h.3. -/
def tryOne : Prog isa :=
  .seq c.hmacV
  (.seq (.block coreArgs)
  (.seq (.call c.coreN c.coreC)
  (.seq (.block goOn)
    (.ite (.nonzero .t6) (.seq c.rekey (.block again)) (.block stop)))))

/-- `K`, `V` and `h` cleared. -/
def wipe : List Instr := .li .t0 0 :: (List.range 20).map fun j => .store .d .t0 .s1 (fK + 8 * j)

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
    (.block (wipe ++ restore))))))))

/-- `vg_ecdsa_<curve>_<hash>_sign`. -/
def sign : Prog isa := .frame (.alloc frB) c.main (.free frB)

end Cfg

end VG.Impl.Ecdsa.Rfc6979.RISCV64
