module

public import VerifiedGarbage.Spec.Sha1
public import VerifiedGarbage.Impl.Words.RISCV64

/-!
# PBKDF2-HMAC-SHA-1's iteration: RISC-V implementation

`iterate(key = a0, u = a1, n = a2, t = a3, scratch = a4)` runs `n` steps
`U ← HMAC (K₀, U)`, `T ← T ⊕ U` (`VG.Spec.Pbkdf2.iterate`), for the key
whose inner and outer SHA-1 streaming states are at `key` and `key + 84`,
with the iteration's contract of every Merkle–Damgård hash function
(`Impl/Pbkdf2/RISCV64.lean`), but with its own compressions rather than
calls of `vg_sha1_compress`.

HMAC of a 20-byte `U` is two compressions, of the inner and then the outer
hash value, each of a block that is a digest followed by the padding of an
84-byte message. SHA-1's digest is its hash value's words, big-endian, so
that block is the five words of the hash value the previous compression
left, `0x80000000`, nine zero words and the bit count `672`. So the
iteration runs on words: `U` lives in five registers between the steps,
`T`, the inner and the outer hash value are words in `scratch`, and only
the prologue and the epilogue convert `U` and `T` from and to bytes.

Each compression (`cmp`) keeps the whole message schedule window in
registers (`w`, `Wₜ` in `w[t mod 16]`), the working variables in five more
(`vs`, renamed each round as in `Impl/Sha1/RISCV64.lean`), and `Kₜ` in `KR`.
The inner compression's window starts with `U`'s registers (`A`) and leaves
its result in its working variables' (`V`); the outer one's starts with
`V` and leaves its result in `A`, which is the next step's `U`. The padding
words are loaded into the rest of the window (`P`) by each compression.
With one temporary (`T1`), the rounds add `ROTL⁵(a)` as its two halves,
which do not overlap, and `Maj(b, c, d)` as `(b ∧ c) + (d ∧ (b ⊕ c))`.

`scratch` is rounded up to a multiple of 8 (it has room to spare): our
caller's `ra` and `s0`–`s11` at `[0, 104)`, the inner hash value at `104`,
the outer at `124` and `T` at `144`, as words. Every register but `a2` (the
steps left), `a3` (`t`) and `a4` (`scratch`) is used, so all the
callee-saved ones are saved there and the function uses no stack. The key,
`U` and `T` are argument buffers, whose alignment the contract does not
state, so they are accessed a byte at a time. Every address and branch
depends only on the pointers and `n`.

`n` is a 32-bit argument, which the calling convention sign-extends: the
entry block zero-extends it, in place, before anything else depends on it.
-/

@[expose] public section

namespace VG.Impl.Pbkdf2.Sha1.RISCV64

open VG.RISCV64
open VG.Impl.Words.RISCV64 (li32 loadBE32 loadLE32 storeBE)

/-- The registers the loop keeps: the frame, the steps left and `t`. -/
def B : Reg := .a4
def N : Reg := .a2
def TP : Reg := .a3

/-- `Kₜ`, and the temporary. -/
def KR : Reg := .a5
def T1 : Reg := .a6

/-- `U`'s words (the inner window's first five, and the outer working
variables), the inner working variables (and the outer window's first five),
and the rest of the window. -/
def A : List Reg := [.s1, .s2, .s3, .s4, .s5]
def V : List Reg := [.s6, .s7, .s8, .s9, .s10]
def P : List Reg := [.s11, .s0, .ra, .t0, .t1, .t2, .t3, .t4, .t5, .t6, .a7]

/-- Where the inner and the outer hash value and `T` are in the frame. -/
def hiO : Nat := 104
def hoO : Nat := 124
def tO : Nat := 144

/-- The registers of one compression: its window, its working variables and
where its hash value is. -/
structure Lay where
  w : List Reg
  vs : List Reg
  hO : Nat

/-- The inner and the outer compression. -/
def inner : Lay := ⟨A ++ P, V, hiO⟩
def outer : Lay := ⟨V ++ P, A, hoO⟩

namespace Lay

variable (L : Lay)

/-- The register holding working variable `k` (`a = 0, …, e = 4`) at the start of round `t`. -/
def var (t k : Nat) : Reg := L.vs.getD ((k + 5 - t % 5) % 5) .t0

/-- The register holding `Wⱼ` (and `Wⱼ₊₁₆`, …). -/
def wr (j : Nat) : Reg := L.w.getD (j % 16) .t0

end Lay

/-- `d := ROTLⁿ(x)` for a word `x`, through `T1` (`0 < n < 32`; `d` may be `x`). -/
def rotl (d x : Reg) (n : Nat) : List Instr :=
  [.shift .sll .w T1 x n, .shift .srl .w d x (32 - n), .logic .or d d T1]

/-- The logical functions of §4.1.1. -/
inductive Fn | ch | parity | maj
  deriving DecidableEq

/-- The function `fₜ` of round `t`. -/
def fn (t : Nat) : Fn :=
  if t < 20 then .ch else if t < 40 then .parity else if t < 60 then .maj else .parity

/-- `e += f(b, c, d)`, through `T1`: `Ch` as `((c ⊕ d) ∧ b) ⊕ d`, and `Maj` as
`(b ∧ c) + (d ∧ (b ⊕ c))`, whose terms have no bit in common. -/
def fadd (f : Fn) (b c d e : Reg) : List Instr :=
  match f with
  | .ch => [.logic .xor T1 c d, .logic .and T1 T1 b, .logic .xor T1 T1 d, .add e e T1]
  | .parity => [.logic .xor T1 b c, .logic .xor T1 T1 d, .add e e T1]
  | .maj => [.logic .and T1 b c, .add e e T1, .logic .xor T1 b c, .logic .and T1 T1 d, .add e e T1]

/-- Round `t`: `T = ROTL⁵(a) + f + e + Kₜ + Wₜ` is added up in `e`'s register
(the new `a`), as `e + Wₜ + f + Kₜ + (a << 5) + (a >> 27)`, and `b` becomes
`ROTL³⁰(b)`. -/
def round (L : Lay) (t : Nat) : List Instr :=
  let a := L.var t 0; let b := L.var t 1; let c := L.var t 2; let d := L.var t 3; let e := L.var t 4
  ([.add e e (L.wr t)] : List Instr) ++ fadd (fn t) b c d e ++
  ([.add e e KR, .shift .sll .w T1 a 5, .add e e T1, .shift .srl .w T1 a 27, .add e e T1] : List Instr) ++
  rotl b b 30

/-- `Wₜ = ROTL¹(Wₜ₋₁₆ ⊕ Wₜ₋₁₄ ⊕ Wₜ₋₈ ⊕ Wₜ₋₃)`, in place of `Wₜ₋₁₆` (`16 ≤ t`). -/
def sched (L : Lay) (t : Nat) : List Instr :=
  let d := L.wr t
  ([.logic .xor d d (L.wr (t + 2)), .logic .xor d d (L.wr (t + 8)), .logic .xor d d (L.wr (t + 13))] :
    List Instr) ++ rotl d d 1

/-- `KR := Kₜ` where it changes. -/
def kload (t : Nat) : List Instr := if t % 20 = 0 then li32 KR (Spec.Sha1.K t) else []

/-- Round `t`, with the schedule and the constant it needs. -/
def step (L : Lay) (t : Nat) : List Instr := (if 16 ≤ t then sched L t else []) ++ kload t ++ round L t

/-- The working variables from the hash value. -/
def load (L : Lay) : List Instr := (List.range 5).flatMap fun k => [.load .w (L.var 0 k) B (L.hO + 4 * k)]

/-- The padding words of the block. -/
def consts (L : Lay) : List Instr :=
  li32 (L.wr 5) 0x80000000 ++ (List.range 9).flatMap (fun i => [.li (L.wr (6 + i)) 0]) ++ [.li (L.wr 15) 672]

/-- The hash value added into the working variables. -/
def addH (L : Lay) : List Instr :=
  (List.range 5).flatMap fun k => [.load .w T1 B (L.hO + 4 * k), .add (L.var 0 k) (L.var 0 k) T1]

/-- One compression: the hash value at `hO` and the block of the digest in
`w[0..5)` and the padding, into `vs` (`80 % 5 = 0`, so the variables are
in the same registers after the 80 rounds). -/
def cmp (L : Lay) : List Instr :=
  load L ++ consts L ++ (List.range 80).flatMap (step L) ++ addH L

/-- `T ← T ⊕ U`, with `U` in `A`. -/
def xorT : List Instr :=
  (List.range 5).flatMap fun k =>
    [.load .w T1 B (tO + 4 * k), .logic .xor T1 T1 (A.getD k .t0), .store .w T1 B (tO + 4 * k)]

/-- One step: the inner hash, then the outer one, then `T ← T ⊕ U`. -/
def body : List Instr := cmp inner ++ cmp outer ++ xorT ++ [.addi N N (-1)]

/-- Our caller's registers, and where we save them in the frame. -/
def saved : List (Reg × Nat) :=
  [(.ra, 0), (.s0, 8), (.s1, 16), (.s2, 24), (.s3, 32), (.s4, 40), (.s5, 48), (.s6, 56), (.s7, 64), (.s8, 72),
    (.s9, 80), (.s10, 88), (.s11, 96)]

/-- Align `scratch` and save our caller's registers. -/
def save : List Instr :=
  [.addi B B 7, .logicImm .and B B (-8)] ++ saved.map fun (r, d) => .store .d r B d

/-- The hash value at `so(key)` to the frame at `fo`, as words. -/
def cpLE (so fo : Nat) : List Instr :=
  (List.range 5).flatMap fun k => loadLE32 T1 KR .a0 (so + 4 * k) ++ [.store .w T1 B (fo + 4 * k)]

/-- `T`'s words to the frame. -/
def cpT : List Instr := (List.range 5).flatMap fun k => loadBE32 T1 KR TP (4 * k) ++ [.store .w T1 B (tO + 4 * k)]

/-- `U`'s words to `A`. -/
def ldU : List Instr := (List.range 5).flatMap fun k => loadBE32 (A.getD k .t0) KR .a1 (4 * k)

/-- The hash values, `T` and `U` as words. -/
def setup : List Instr := cpLE 0 hiO ++ cpLE 84 hoO ++ cpT ++ ldU

/-- `T`'s words to `t`, big-endian, and our caller's registers restored. -/
def finish : List Instr :=
  (List.range 5).flatMap (fun k => [.load .w T1 B (tO + 4 * k)] ++ storeBE 4 T1 KR TP (4 * k)) ++
  saved.map fun (r, d) => .load .d r B d

/-- `n` zero-extended. -/
def entry : List Instr := [.shift .sll .d N N 32, .shift .srl .d N N 32]

def main : Prog isa :=
  .seq (.block (save ++ setup))
  (.seq (.ite (.zero N) (.block []) (.loop (.block body) (.nonzero N)))
    (.block finish))

def iterate : Prog isa := .seq (.block entry) main

end VG.Impl.Pbkdf2.Sha1.RISCV64
