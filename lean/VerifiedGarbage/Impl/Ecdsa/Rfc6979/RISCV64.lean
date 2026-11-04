module

public import VerifiedGarbage.Impl.Hmac.Stream.RISCV64
public import VerifiedGarbage.Impl.RsaOaep.RISCV64
public import VerifiedGarbage.Impl.ICall
public import VerifiedGarbage.Impl.Ecdh.RISCV64
public import VerifiedGarbage.Impl.Ecdh.RISCV64.Num4
public import VerifiedGarbage.Impl.Ecdh.RISCV64.Num0
public import VerifiedGarbage.Impl.Words.RISCV64.Bytes

/-!
# Deterministic ECDSA (RFC 6979) on RISC-V, with the hash function of a table

`vg_ecdsa_<curve>_sign(out = a0, d = a1, digest = a2, digest_len = a3,
scratch = a4, hash = a5) -> a0` (`signT`): RFC 6979 §3.2 for a curve of
scalars of `Q` bytes in `nw` 64-bit words (`Q = 8 nw`; `8 nw - 4`, a top
word of four bytes; or `8 nw - 8`, a top word of zero: P-256's 32, P-384's
48, P-224's 28, P-192's 24) whose order `n` has `8 Q` bits, with HMAC over
the hash function of the table `hash` of the interface `Hash`
(`Spec/HashTable.lean`), whose streaming `init`, `update` and `finalize`
(its words 0 to 2) it calls indirectly (`tcall`: the word into `t1`, then
`jalr ra, 0(t1)`, of whichever of the functions `Fns` lists is at that
address), and each candidate tried by calling `core`, the signature with a
given `k` (`vg_ecdsa_<curve>_sign_k`), which reads `Q` bytes of the digest
and of `k`.

Which table `hash` is, is public (`Abi.withTables`), and so is the hash
function's index in `Mgf1.hashes`, its word 3: `signT` chooses by it
(`byIdx`, comparisons with each index of `idxs`) the code for that hash
function's digest length `D` and block size `B` (`shapeOf`), `sign` of a
`Cfg`, in which both are constants. Everything below is that code.

HMAC (`hmac`) is computed from the table's streaming functions: the key `K`
(`D` bytes, in the frame) padded to a block and XORed with `ipad` (`padBlk`,
a 32-bit word at a time, into `scratch + sPad`), the inner state set by
`init` and updated with it, the same with `opad` for the outer state
(`hinit`); the inner state updated with each part of the data (`upds`);
then the inner state finalized into `scratch + sTmp`, and the outer one
updated with that digest and finalized into the MAC's place in the frame
(`hfin`).

It runs in a frame of `fH + 8 nw` bytes rounded up to 16 (`alloc`): our
caller's `ra` and `s0`–`s6`, then `K` and `V` (64 bytes each, of which the
first `D` are used, and the byte after `V` the separator of steps d, f and
h.3) and `h` (`Q` bytes, in `8 nw`) at `fH`: 192, or 208 when `D` is 64 and
the separator is byte 192. Our variables live in `s0`–`s6`, which the
functions we call save and restore: `s0` = `scratch`, `s1` = the frame,
`s2` = `out`, `s3` = `d`, `s4` = `digest`, `s5` = the candidates left and
`s6` = the table. In `scratch`: HMAC's inner and outer streaming states (at
0 and 192), the padded key (at 384) and the inner digest (at 512), which
`core` then overwrites. The functions we call use the stack below the frame.

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
open VG.Impl.Hmac.Stream.RISCV64 (mov)
open VG.Impl.RsaOaep.RISCV64 (Fns)

/-! Where things are in the frame. -/
def fK : Nat := 64
def fV : Nat := 128

/-! Where things are in `scratch`: HMAC's states, the padded key, the inner
digest, and the first number of `bits2octets`. -/
def sIn : Nat := 0
def sOut : Nat := 192
def sPad : Nat := 384
def sTmp : Nat := 512
def sX : Nat := 0

/-- What the code needs: the hash function's digest length and block size,
the functions an indirect call of a table's functions may reach, the
arithmetic modulo the order `n` (`FN`, whose addition `bits2octets` calls),
the signature with a given `k` and its name, the most candidates to try,
the scalars' 64-bit words and their bytes. -/
structure Cfg where
  D : Nat
  B : Nat
  f : Fns
  FN : Weierstrass.RISCV64.Field
  coreN : String
  coreC : Prog isa
  tries : Nat
  nw : Nat
  Q : Nat := 8 * nw

/-- Our caller's registers we save, and where, at the start of the frame. -/
def saved : List (Reg × Nat) :=
  [(.ra, 0), (.s0, 8), (.s1, 16), (.s2, 24), (.s3, 32), (.s4, 40), (.s5, 48), (.s6, 56)]

/-- Where we restore them from, in order (`s1`, the base, last). -/
def restList : List (Reg × Nat) :=
  [(.ra, 0), (.s0, 8), (.s2, 24), (.s3, 32), (.s4, 40), (.s5, 48), (.s6, 56), (.s1, 16)]

/-- A part of a message: `len` bytes at `off(base)`. -/
abbrev Part := Reg × Nat × Nat

/-- The bytes of the parts. -/
def total : List Part → Nat
  | [] => 0
  | p :: ps => p.2.2 + total ps

/-- The table's word `k` (the table in `s6`) into `t1`. -/
def tword (k : Nat) : List Instr := [.load .d .t1 .s6 (8 * k)]

/-- The call of the table's function `k`, among `ts`: its address into
`t1`, then `jalr ra, 0(t1)`. -/
def tcall (k : Nat) (ts : List (String × Prog isa)) : Prog isa :=
  .seq (.block (tword k)) (Code.icalls (.jalr .t1) ts)

/-- The byte `b` in each byte of the low word of `t5` (through `t4`). -/
def padWord (b : Nat) : List Instr :=
  [.li .t5 b, .shift .sll .d .t4 .t5 8, .logic .or .t5 .t5 .t4, .shift .sll .d .t4 .t5 16, .logic .or .t5 .t5 .t4]

/-- `ipad` and `opad` (RFC 2104). -/
def ipadW : List Instr := padWord 0x36
def opadW : List Instr := padWord 0x5c

namespace Cfg

variable (c : Cfg)

/-- Where `h` is in the frame: after `V` and its separator. -/
def fH : Nat := if c.D < 64 then 192 else 208

/-- Whether the scalars are longer than the hash's output. -/
def wide : Bool := decide (c.D < c.Q)

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
    [mov .s1 .t0, mov .s2 .a0, mov .s3 .a1, mov .s4 .a2, mov .s0 .a4, mov .s6 .a5]

/-- If `wide`: `h`, the digest after `Q - D` zero bytes. -/
def reduceW : List Instr :=
  Words.RISCV64.storeBytes .t0 .s1 c.fH (List.replicate (c.Q - c.D) 0) ++
    Words.RISCV64.copyBytes .t0 .s4 .s1 0 (c.fH + (c.Q - c.D)) c.D

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
  Words.RISCV64.storeBytes .t0 .s1 fK (List.replicate c.D 0) ++
    Words.RISCV64.storeBytes .t0 .s1 fV (List.replicate c.D 1)

/-! ## HMAC through the table -/

/-- The streaming `init` of the state at `scratch + o`. -/
def initCall (o : Nat) : Prog isa := .seq (.block [.addi .a0 .s0 o]) (tcall 0 c.f.init)

/-- The streaming `update`'s arguments: the state at `scratch + o`, which
holds `cnt` bytes, and the `len` bytes at `off(base)`. -/
def updArgs (o cnt : Nat) (base : Reg) (off len : Nat) : List Instr :=
  [.addi .a0 .s0 o, .li .a1 cnt, .addi .a2 base off, .li .a3 len]

def updCall (o cnt : Nat) (base : Reg) (off len : Nat) : Prog isa :=
  .seq (.block (updArgs o cnt base off len)) (tcall 1 c.f.upd)

/-- The streaming `finalize`'s arguments: the state at `scratch + o`, which
holds `cnt` bytes, and the digest to `off(base)`. -/
def finArgs (o cnt : Nat) (base : Reg) (off : Nat) : List Instr :=
  [.addi .a0 .s0 o, .li .a1 cnt, .addi .a2 base off]

def finCall (o cnt : Nat) (base : Reg) (off : Nat) : Prog isa :=
  .seq (.block (finArgs o cnt base off)) (tcall 2 c.f.fin)

/-- Word `k` of the key `K` (the frame's first `D` bytes) padded to `B`
bytes, XORed with the pad in `t5`, to `scratch + sPad`. -/
def padW (k : Nat) : List Instr :=
  if k < c.D / 4 then
    [.load .w .t1 .s1 (fK + 4 * k), .logic .xor .t1 .t1 .t5, .store .w .t1 .s0 (sPad + 4 * k)]
  else [.store .w .t5 .s0 (sPad + 4 * k)]

/-- `K₀ ⊕ pad` (a block) at `scratch + sPad`, the pad's word set by `pw`. -/
def padBlk (pw : List Instr) : List Instr := pw ++ (List.range (c.B / 4)).flatMap c.padW

/-- HMAC's states for the key `K`: each set by `init`, then updated with
the padded key. -/
def hinit : Prog isa :=
  .seq (c.initCall sIn) (.seq (c.initCall sOut)
  (.seq (.block (c.padBlk ipadW)) (.seq (c.updCall sIn 0 .s0 sPad c.B)
  (.seq (.block (c.padBlk opadW)) (c.updCall sOut 0 .s0 sPad c.B)))))

/-- The parts absorbed into the inner state, which holds `B + cnt` bytes. -/
def upds : Nat → List Part → Prog isa
  | _, [] => .block []
  | cnt, p :: ps => .seq (c.updCall sIn (c.B + cnt) p.1 p.2.1 p.2.2) (upds (cnt + p.2.2) ps)

/-- The MAC, for `len` bytes of data, to the frame at `dst`: the inner state
finalized into `scratch + sTmp`, the outer one updated with that digest and
finalized to `dst`. -/
def hfin (len dst : Nat) : Prog isa :=
  .seq (c.finCall sIn (c.B + len) .s0 sTmp) (.seq (c.updCall sOut c.B .s0 sTmp c.D)
    (c.finCall sOut (c.B + c.D) .s1 dst))

/-- `HMAC_K(parts)` into the frame at `dst`. -/
def hmac (ps : List Part) (dst : Nat) : Prog isa :=
  .seq c.hinit (.seq (c.upds 0 ps) (c.hfin (total ps) dst))

/-- `V = HMAC_K(V)`. -/
def hmacV : Prog isa := c.hmac [(.s1, fV, c.D)] fV

/-- The separator `b` after `V`. -/
def sep (b : Nat) : List Instr := Words.RISCV64.storeBytes .t0 .s1 (fV + c.D) [b]

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
def rekeyFull (b : Nat) : Prog isa :=
  .seq (.block (c.sep b))
    (.seq (c.hmac [(.s1, fV, c.D + 1), (.s3, 0, c.Q), (.s1, c.fH, c.Q)] fK) c.hmacV)

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
def rekey : Prog isa :=
  .seq (.block (c.sep 0)) (.seq (c.hmac [(.s1, fV, c.D + 1)] fK) c.hmacV)

/-- The candidates left. -/
def initCnt : List Instr := [.li .s5 c.tries]

/-- `core(out, d, digest, k = V, scratch)`. -/
def coreArgs : List Instr := [mov .a0 .s2, mov .a1 .s3, mov .a2 .s4, .addi .a3 .s1 fV, mov .a4 .s0]

/-- If `wide`: `core(out, d, digest, k = fT, scratch)`. -/
def coreArgsW : List Instr := [mov .a0 .s2, mov .a1 .s3, mov .a2 .s4, .addi .a3 .s1 c.fT, mov .a4 .s0]

/-- If `wide`, the candidate: `V₁ = HMAC_K(V)` to `fT`, `V₂ = HMAC_K(V₁)` to
`V`'s place, and `V₂`'s first `Q - D` bytes after `V₁`. -/
def candW : Prog isa :=
  .seq (c.hmac [(.s1, fV, c.D)] c.fT)
  (.seq (c.hmac [(.s1, c.fT, c.D)] fV)
    (.block (Words.RISCV64.copyBytes .t0 .s1 .s1 fV (c.fT + c.D) (c.Q - c.D))))

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

/-- The signature for the hash function of this size, with the table in
`a5`. -/
def sign : Prog isa := .frame (.alloc c.frB) c.main (.free c.frB)

end Cfg

/-! ## The choice by the hash function -/

/-- The indices in `Mgf1.hashes` of the hash functions with HMAC
(`Spec.Ecdsa.Rfc6979.hmacOf`): MD5, SHA-1, SHA-224, SHA-256, SHA-384,
SHA-512, SHA-512/224 and SHA-512/256. -/
def idxs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]

/-- The digest length and block size of the hash function of index `i`. -/
def shapeOf : Nat → Nat × Nat
  | 0 => (16, 64)
  | 1 => (20, 64)
  | 2 => (28, 64)
  | 3 => (32, 64)
  | 4 => (48, 128)
  | 5 => (64, 128)
  | 6 => (28, 128)
  | _ => (32, 128)

/-- `b i` for the index `i` in `t2`, by comparisons with each of `is`
(`t3 = t2 - i`): the last is taken for every other value. -/
def byIdx (b : Nat → Prog isa) : List Nat → Prog isa
  | [] => .block []
  | [i] => b i
  | i :: is => .seq (.block [.addi .t3 .t2 (-(i : Int))]) (.ite (.zero .t3) (b i) (byIdx b is))

/-- The hash function's index (the table's word 3) to `t2`. -/
def entry : List Instr := [.load .d .t2 .a5 24]

/-- `vg_ecdsa_<curve>_sign`: the signature with the code `cfg i` for the
hash function of index `i` of the table `hash`. -/
def signT (cfg : Nat → Cfg) : Prog isa :=
  .seq (.block entry) (byIdx (fun i => (cfg i).sign) idxs)

end VG.Impl.Ecdsa.Rfc6979.RISCV64
