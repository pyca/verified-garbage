import VerifiedGarbage.TCB.X86_64.Print

/-!
# Semantics tests for the x86-64 `imul r64, r64, imm32`, `shld r64, r64, imm8` and `btr r64, imm8`

Each expected value was computed on an x86-64 CPU (an Intel Xeon), by the
same instruction in inline assembly (`imul rax, rcx, imm`, `shld rax, rcx,
n` and `btr rax, n`, reading RFLAGS with `pushfq` after it), and is compared
with the model's result on the same inputs. This tests the transcription of
the SDM's pseudocode, which review of the TCB would otherwise have to catch
by eye: the low half of the product, and CF and OF set when the signed
product does not fit (SF and ZF undefined); the shifted-in bits, CF (the last
bit shifted out), SF and ZF from the result, and OF for a 1-bit shift (its
sign change; undefined for other counts); and CF (the selected bit), the
cleared bit and ZF kept (OF and SF undefined).
-/

namespace VG.Test.X86_64ShldBtrImul3

open X86_64

/-- A state with `a` in `rax`, `b` in `rcx` and `z` in ZF, and every flag defined. -/
def s (a b : BitVec 64) (z : Bool := true) : State where
  gpr r := if r = .rax then a else if r = .rcx then b else 7
  cf := some false
  zf := some z
  sf := some true
  of := some false
  mem _ := 0
  rd := []
  wr := []

/-- `imul rax, rcx, v` with `a` in `rcx`: the expected product and CF (= OF),
with SF and ZF undefined. -/
def imul3 (a : BitVec 64) (v : Int) (p : BitVec 64) (c : Bool) : Bool :=
  (exec (.imul3 .rax .rcx (BitVec.ofInt 32 v)) (s 7 a)).map
      (fun t => (t.gpr .rax, t.cf, t.of, t.sf.isNone && t.zf.isNone)) ==
    some (p, some c, some c, true)

/-- `shld rax, rcx, 1` with `a` in `rax` and `b` in `rcx`: the expected
result, CF, ZF, SF and OF. -/
def shld1 (a b r : BitVec 64) (cf zf sf o : Bool) : Bool :=
  (exec (.shld .rax .rcx 1) (s a b)).map (fun t => (t.gpr .rax, t.cf, t.zf, t.sf, t.of)) ==
    some (r, some cf, some zf, some sf, some o)

/-- `shld rax, rcx, n` for `n > 1`: the expected result, CF, ZF and SF, with
OF undefined. -/
def shld (n : Nat) (a b r : BitVec 64) (cf zf sf : Bool) : Bool :=
  (exec (.shld .rax .rcx n) (s a b)).map (fun t => (t.gpr .rax, t.cf, t.zf, t.sf, t.of.isNone)) ==
    some (r, some cf, some zf, some sf, true)

/-- `btr rax, n` with `a` in `rax` and `z` in ZF: the expected result, CF
and ZF, with OF and SF undefined. -/
def btr (n : Nat) (z : Bool) (a r : BitVec 64) (cf zf : Bool) : Bool :=
  (exec (.btr .rax n) (s a 0 z)).map (fun t => (t.gpr .rax, t.cf, t.zf, t.of.isNone && t.sf.isNone)) ==
    some (r, some cf, some zf, true)

/-! ## `imul rax, rcx, imm32` -/

#guard imul3 0x0 (19) 0x0 false
#guard imul3 0x1 (19) 0x13 false
#guard imul3 0x2 (19) 0x26 false
#guard imul3 0x3 (19) 0x39 false
#guard imul3 0x7fffffffffffffff (19) 0x7fffffffffffffed true
#guard imul3 0x8000000000000000 (19) 0x8000000000000000 true
#guard imul3 0xffffffffffffffff (19) 0xffffffffffffffed false
#guard imul3 0x123456789abcdef (19) 0x159e26af37c048bd false
#guard imul3 0xdeadbeefcafebabe (19) 0x86e52bcc10e7dc1a true
#guard imul3 0x6bca1af286bca1b (19) 0x8000000000000001 true
#guard imul3 0x8000000000000001 (19) 0x8000000000000013 true
#guard imul3 0x4000000000000000 (19) 0xc000000000000000 true
#guard imul3 0x0 (38) 0x0 false
#guard imul3 0x1 (38) 0x26 false
#guard imul3 0x2 (38) 0x4c false
#guard imul3 0x3 (38) 0x72 false
#guard imul3 0x7fffffffffffffff (38) 0xffffffffffffffda true
#guard imul3 0x8000000000000000 (38) 0x0 true
#guard imul3 0xffffffffffffffff (38) 0xffffffffffffffda false
#guard imul3 0x123456789abcdef (38) 0x2b3c4d5e6f80917a false
#guard imul3 0xdeadbeefcafebabe (38) 0xdca579821cfb834 true
#guard imul3 0x6bca1af286bca1b (38) 0x2 true
#guard imul3 0x8000000000000001 (38) 0x26 true
#guard imul3 0x4000000000000000 (38) 0x8000000000000000 true
#guard imul3 0x0 (-1) 0x0 false
#guard imul3 0x1 (-1) 0xffffffffffffffff false
#guard imul3 0x2 (-1) 0xfffffffffffffffe false
#guard imul3 0x3 (-1) 0xfffffffffffffffd false
#guard imul3 0x7fffffffffffffff (-1) 0x8000000000000001 false
#guard imul3 0x8000000000000000 (-1) 0x8000000000000000 true
#guard imul3 0xffffffffffffffff (-1) 0x1 false
#guard imul3 0x123456789abcdef (-1) 0xfedcba9876543211 false
#guard imul3 0xdeadbeefcafebabe (-1) 0x2152411035014542 false
#guard imul3 0x6bca1af286bca1b (-1) 0xf9435e50d79435e5 false
#guard imul3 0x8000000000000001 (-1) 0x7fffffffffffffff false
#guard imul3 0x4000000000000000 (-1) 0xc000000000000000 false
#guard imul3 0x0 (2147483647) 0x0 false
#guard imul3 0x1 (2147483647) 0x7fffffff false
#guard imul3 0x2 (2147483647) 0xfffffffe false
#guard imul3 0x3 (2147483647) 0x17ffffffd false
#guard imul3 0x7fffffffffffffff (2147483647) 0x7fffffff80000001 true
#guard imul3 0x8000000000000000 (2147483647) 0x8000000000000000 true
#guard imul3 0xffffffffffffffff (2147483647) 0xffffffff80000001 false
#guard imul3 0x123456789abcdef (2147483647) 0xc3b2a18ff6543211 true
#guard imul3 0xdeadbeefcafebabe (2147483647) 0x6d19e6f35014542 true
#guard imul3 0x6bca1af286bca1b (2147483647) 0x8d79435e579435e5 true
#guard imul3 0x8000000000000001 (2147483647) 0x800000007fffffff true
#guard imul3 0x4000000000000000 (2147483647) 0xc000000000000000 true
#guard imul3 0x0 (-2147483648) 0x0 false
#guard imul3 0x1 (-2147483648) 0xffffffff80000000 false
#guard imul3 0x2 (-2147483648) 0xffffffff00000000 false
#guard imul3 0x3 (-2147483648) 0xfffffffe80000000 false
#guard imul3 0x7fffffffffffffff (-2147483648) 0x80000000 true
#guard imul3 0x8000000000000000 (-2147483648) 0x0 true
#guard imul3 0xffffffffffffffff (-2147483648) 0x80000000 false
#guard imul3 0x123456789abcdef (-2147483648) 0x3b2a190880000000 true
#guard imul3 0xdeadbeefcafebabe (-2147483648) 0x1a80a2a100000000 true
#guard imul3 0x6bca1af286bca1b (-2147483648) 0x6bca1af280000000 true
#guard imul3 0x8000000000000001 (-2147483648) 0xffffffff80000000 true
#guard imul3 0x4000000000000000 (-2147483648) 0x0 true

/-! ## `shld rax, rcx, 1` -/

#guard shld1 0x0 0x0 0x0 false true false false
#guard shld1 0x0 0x3 0x0 false true false false
#guard shld1 0x0 0xffffffffffffffff 0x1 false false false false
#guard shld1 0x0 0x6bca1af286bca1b 0x0 false true false false
#guard shld1 0x1 0x0 0x2 false false false false
#guard shld1 0x1 0x3 0x2 false false false false
#guard shld1 0x1 0xffffffffffffffff 0x3 false false false false
#guard shld1 0x1 0x6bca1af286bca1b 0x2 false false false false
#guard shld1 0x2 0x0 0x4 false false false false
#guard shld1 0x2 0x3 0x4 false false false false
#guard shld1 0x2 0xffffffffffffffff 0x5 false false false false
#guard shld1 0x2 0x6bca1af286bca1b 0x4 false false false false
#guard shld1 0x3 0x0 0x6 false false false false
#guard shld1 0x3 0x3 0x6 false false false false
#guard shld1 0x3 0xffffffffffffffff 0x7 false false false false
#guard shld1 0x3 0x6bca1af286bca1b 0x6 false false false false
#guard shld1 0x7fffffffffffffff 0x0 0xfffffffffffffffe false false true true
#guard shld1 0x7fffffffffffffff 0x3 0xfffffffffffffffe false false true true
#guard shld1 0x7fffffffffffffff 0xffffffffffffffff 0xffffffffffffffff false false true true
#guard shld1 0x7fffffffffffffff 0x6bca1af286bca1b 0xfffffffffffffffe false false true true
#guard shld1 0x8000000000000000 0x0 0x0 true true false true
#guard shld1 0x8000000000000000 0x3 0x0 true true false true
#guard shld1 0x8000000000000000 0xffffffffffffffff 0x1 true false false true
#guard shld1 0x8000000000000000 0x6bca1af286bca1b 0x0 true true false true
#guard shld1 0xffffffffffffffff 0x0 0xfffffffffffffffe true false true false
#guard shld1 0xffffffffffffffff 0x3 0xfffffffffffffffe true false true false
#guard shld1 0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff true false true false
#guard shld1 0xffffffffffffffff 0x6bca1af286bca1b 0xfffffffffffffffe true false true false
#guard shld1 0x123456789abcdef 0x0 0x2468acf13579bde false false false false
#guard shld1 0x123456789abcdef 0x3 0x2468acf13579bde false false false false
#guard shld1 0x123456789abcdef 0xffffffffffffffff 0x2468acf13579bdf false false false false
#guard shld1 0x123456789abcdef 0x6bca1af286bca1b 0x2468acf13579bde false false false false
#guard shld1 0xdeadbeefcafebabe 0x0 0xbd5b7ddf95fd757c true false true false
#guard shld1 0xdeadbeefcafebabe 0x3 0xbd5b7ddf95fd757c true false true false
#guard shld1 0xdeadbeefcafebabe 0xffffffffffffffff 0xbd5b7ddf95fd757d true false true false
#guard shld1 0xdeadbeefcafebabe 0x6bca1af286bca1b 0xbd5b7ddf95fd757c true false true false
#guard shld1 0x6bca1af286bca1b 0x0 0xd79435e50d79436 false false false false
#guard shld1 0x6bca1af286bca1b 0x3 0xd79435e50d79436 false false false false
#guard shld1 0x6bca1af286bca1b 0xffffffffffffffff 0xd79435e50d79437 false false false false
#guard shld1 0x6bca1af286bca1b 0x6bca1af286bca1b 0xd79435e50d79436 false false false false
#guard shld1 0x8000000000000001 0x0 0x2 true false false true
#guard shld1 0x8000000000000001 0x3 0x2 true false false true
#guard shld1 0x8000000000000001 0xffffffffffffffff 0x3 true false false true
#guard shld1 0x8000000000000001 0x6bca1af286bca1b 0x2 true false false true
#guard shld1 0x4000000000000000 0x0 0x8000000000000000 false false true true
#guard shld1 0x4000000000000000 0x3 0x8000000000000000 false false true true
#guard shld1 0x4000000000000000 0xffffffffffffffff 0x8000000000000001 false false true true
#guard shld1 0x4000000000000000 0x6bca1af286bca1b 0x8000000000000000 false false true true

/-! ## `shld rax, rcx, n`, `n > 1` -/

#guard shld 4 0x0 0x0 0x0 false true false
#guard shld 4 0x0 0x3 0x0 false true false
#guard shld 4 0x0 0xffffffffffffffff 0xf false false false
#guard shld 4 0x0 0x6bca1af286bca1b 0x0 false true false
#guard shld 4 0x1 0x0 0x10 false false false
#guard shld 4 0x1 0x3 0x10 false false false
#guard shld 4 0x1 0xffffffffffffffff 0x1f false false false
#guard shld 4 0x1 0x6bca1af286bca1b 0x10 false false false
#guard shld 4 0x2 0x0 0x20 false false false
#guard shld 4 0x2 0x3 0x20 false false false
#guard shld 4 0x2 0xffffffffffffffff 0x2f false false false
#guard shld 4 0x2 0x6bca1af286bca1b 0x20 false false false
#guard shld 4 0x3 0x0 0x30 false false false
#guard shld 4 0x3 0x3 0x30 false false false
#guard shld 4 0x3 0xffffffffffffffff 0x3f false false false
#guard shld 4 0x3 0x6bca1af286bca1b 0x30 false false false
#guard shld 4 0x7fffffffffffffff 0x0 0xfffffffffffffff0 true false true
#guard shld 4 0x7fffffffffffffff 0x3 0xfffffffffffffff0 true false true
#guard shld 4 0x7fffffffffffffff 0xffffffffffffffff 0xffffffffffffffff true false true
#guard shld 4 0x7fffffffffffffff 0x6bca1af286bca1b 0xfffffffffffffff0 true false true
#guard shld 4 0x8000000000000000 0x0 0x0 false true false
#guard shld 4 0x8000000000000000 0x3 0x0 false true false
#guard shld 4 0x8000000000000000 0xffffffffffffffff 0xf false false false
#guard shld 4 0x8000000000000000 0x6bca1af286bca1b 0x0 false true false
#guard shld 4 0xffffffffffffffff 0x0 0xfffffffffffffff0 true false true
#guard shld 4 0xffffffffffffffff 0x3 0xfffffffffffffff0 true false true
#guard shld 4 0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff true false true
#guard shld 4 0xffffffffffffffff 0x6bca1af286bca1b 0xfffffffffffffff0 true false true
#guard shld 4 0x123456789abcdef 0x0 0x123456789abcdef0 false false false
#guard shld 4 0x123456789abcdef 0x3 0x123456789abcdef0 false false false
#guard shld 4 0x123456789abcdef 0xffffffffffffffff 0x123456789abcdeff false false false
#guard shld 4 0x123456789abcdef 0x6bca1af286bca1b 0x123456789abcdef0 false false false
#guard shld 4 0xdeadbeefcafebabe 0x0 0xeadbeefcafebabe0 true false true
#guard shld 4 0xdeadbeefcafebabe 0x3 0xeadbeefcafebabe0 true false true
#guard shld 4 0xdeadbeefcafebabe 0xffffffffffffffff 0xeadbeefcafebabef true false true
#guard shld 4 0xdeadbeefcafebabe 0x6bca1af286bca1b 0xeadbeefcafebabe0 true false true
#guard shld 4 0x6bca1af286bca1b 0x0 0x6bca1af286bca1b0 false false false
#guard shld 4 0x6bca1af286bca1b 0x3 0x6bca1af286bca1b0 false false false
#guard shld 4 0x6bca1af286bca1b 0xffffffffffffffff 0x6bca1af286bca1bf false false false
#guard shld 4 0x6bca1af286bca1b 0x6bca1af286bca1b 0x6bca1af286bca1b0 false false false
#guard shld 4 0x8000000000000001 0x0 0x10 false false false
#guard shld 4 0x8000000000000001 0x3 0x10 false false false
#guard shld 4 0x8000000000000001 0xffffffffffffffff 0x1f false false false
#guard shld 4 0x8000000000000001 0x6bca1af286bca1b 0x10 false false false
#guard shld 4 0x4000000000000000 0x0 0x0 false true false
#guard shld 4 0x4000000000000000 0x3 0x0 false true false
#guard shld 4 0x4000000000000000 0xffffffffffffffff 0xf false false false
#guard shld 4 0x4000000000000000 0x6bca1af286bca1b 0x0 false true false
#guard shld 32 0x0 0x0 0x0 false true false
#guard shld 32 0x0 0x3 0x0 false true false
#guard shld 32 0x0 0xffffffffffffffff 0xffffffff false false false
#guard shld 32 0x0 0x6bca1af286bca1b 0x6bca1af false false false
#guard shld 32 0x1 0x0 0x100000000 false false false
#guard shld 32 0x1 0x3 0x100000000 false false false
#guard shld 32 0x1 0xffffffffffffffff 0x1ffffffff false false false
#guard shld 32 0x1 0x6bca1af286bca1b 0x106bca1af false false false
#guard shld 32 0x2 0x0 0x200000000 false false false
#guard shld 32 0x2 0x3 0x200000000 false false false
#guard shld 32 0x2 0xffffffffffffffff 0x2ffffffff false false false
#guard shld 32 0x2 0x6bca1af286bca1b 0x206bca1af false false false
#guard shld 32 0x3 0x0 0x300000000 false false false
#guard shld 32 0x3 0x3 0x300000000 false false false
#guard shld 32 0x3 0xffffffffffffffff 0x3ffffffff false false false
#guard shld 32 0x3 0x6bca1af286bca1b 0x306bca1af false false false
#guard shld 32 0x7fffffffffffffff 0x0 0xffffffff00000000 true false true
#guard shld 32 0x7fffffffffffffff 0x3 0xffffffff00000000 true false true
#guard shld 32 0x7fffffffffffffff 0xffffffffffffffff 0xffffffffffffffff true false true
#guard shld 32 0x7fffffffffffffff 0x6bca1af286bca1b 0xffffffff06bca1af true false true
#guard shld 32 0x8000000000000000 0x0 0x0 false true false
#guard shld 32 0x8000000000000000 0x3 0x0 false true false
#guard shld 32 0x8000000000000000 0xffffffffffffffff 0xffffffff false false false
#guard shld 32 0x8000000000000000 0x6bca1af286bca1b 0x6bca1af false false false
#guard shld 32 0xffffffffffffffff 0x0 0xffffffff00000000 true false true
#guard shld 32 0xffffffffffffffff 0x3 0xffffffff00000000 true false true
#guard shld 32 0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff true false true
#guard shld 32 0xffffffffffffffff 0x6bca1af286bca1b 0xffffffff06bca1af true false true
#guard shld 32 0x123456789abcdef 0x0 0x89abcdef00000000 true false true
#guard shld 32 0x123456789abcdef 0x3 0x89abcdef00000000 true false true
#guard shld 32 0x123456789abcdef 0xffffffffffffffff 0x89abcdefffffffff true false true
#guard shld 32 0x123456789abcdef 0x6bca1af286bca1b 0x89abcdef06bca1af true false true
#guard shld 32 0xdeadbeefcafebabe 0x0 0xcafebabe00000000 true false true
#guard shld 32 0xdeadbeefcafebabe 0x3 0xcafebabe00000000 true false true
#guard shld 32 0xdeadbeefcafebabe 0xffffffffffffffff 0xcafebabeffffffff true false true
#guard shld 32 0xdeadbeefcafebabe 0x6bca1af286bca1b 0xcafebabe06bca1af true false true
#guard shld 32 0x6bca1af286bca1b 0x0 0x286bca1b00000000 true false false
#guard shld 32 0x6bca1af286bca1b 0x3 0x286bca1b00000000 true false false
#guard shld 32 0x6bca1af286bca1b 0xffffffffffffffff 0x286bca1bffffffff true false false
#guard shld 32 0x6bca1af286bca1b 0x6bca1af286bca1b 0x286bca1b06bca1af true false false
#guard shld 32 0x8000000000000001 0x0 0x100000000 false false false
#guard shld 32 0x8000000000000001 0x3 0x100000000 false false false
#guard shld 32 0x8000000000000001 0xffffffffffffffff 0x1ffffffff false false false
#guard shld 32 0x8000000000000001 0x6bca1af286bca1b 0x106bca1af false false false
#guard shld 32 0x4000000000000000 0x0 0x0 false true false
#guard shld 32 0x4000000000000000 0x3 0x0 false true false
#guard shld 32 0x4000000000000000 0xffffffffffffffff 0xffffffff false false false
#guard shld 32 0x4000000000000000 0x6bca1af286bca1b 0x6bca1af false false false
#guard shld 63 0x0 0x0 0x0 false true false
#guard shld 63 0x0 0x3 0x1 false false false
#guard shld 63 0x0 0xffffffffffffffff 0x7fffffffffffffff false false false
#guard shld 63 0x0 0x6bca1af286bca1b 0x35e50d79435e50d false false false
#guard shld 63 0x1 0x0 0x8000000000000000 false false true
#guard shld 63 0x1 0x3 0x8000000000000001 false false true
#guard shld 63 0x1 0xffffffffffffffff 0xffffffffffffffff false false true
#guard shld 63 0x1 0x6bca1af286bca1b 0x835e50d79435e50d false false true
#guard shld 63 0x2 0x0 0x0 true true false
#guard shld 63 0x2 0x3 0x1 true false false
#guard shld 63 0x2 0xffffffffffffffff 0x7fffffffffffffff true false false
#guard shld 63 0x2 0x6bca1af286bca1b 0x35e50d79435e50d true false false
#guard shld 63 0x3 0x0 0x8000000000000000 true false true
#guard shld 63 0x3 0x3 0x8000000000000001 true false true
#guard shld 63 0x3 0xffffffffffffffff 0xffffffffffffffff true false true
#guard shld 63 0x3 0x6bca1af286bca1b 0x835e50d79435e50d true false true
#guard shld 63 0x7fffffffffffffff 0x0 0x8000000000000000 true false true
#guard shld 63 0x7fffffffffffffff 0x3 0x8000000000000001 true false true
#guard shld 63 0x7fffffffffffffff 0xffffffffffffffff 0xffffffffffffffff true false true
#guard shld 63 0x7fffffffffffffff 0x6bca1af286bca1b 0x835e50d79435e50d true false true
#guard shld 63 0x8000000000000000 0x0 0x0 false true false
#guard shld 63 0x8000000000000000 0x3 0x1 false false false
#guard shld 63 0x8000000000000000 0xffffffffffffffff 0x7fffffffffffffff false false false
#guard shld 63 0x8000000000000000 0x6bca1af286bca1b 0x35e50d79435e50d false false false
#guard shld 63 0xffffffffffffffff 0x0 0x8000000000000000 true false true
#guard shld 63 0xffffffffffffffff 0x3 0x8000000000000001 true false true
#guard shld 63 0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff true false true
#guard shld 63 0xffffffffffffffff 0x6bca1af286bca1b 0x835e50d79435e50d true false true
#guard shld 63 0x123456789abcdef 0x0 0x8000000000000000 true false true
#guard shld 63 0x123456789abcdef 0x3 0x8000000000000001 true false true
#guard shld 63 0x123456789abcdef 0xffffffffffffffff 0xffffffffffffffff true false true
#guard shld 63 0x123456789abcdef 0x6bca1af286bca1b 0x835e50d79435e50d true false true
#guard shld 63 0xdeadbeefcafebabe 0x0 0x0 true true false
#guard shld 63 0xdeadbeefcafebabe 0x3 0x1 true false false
#guard shld 63 0xdeadbeefcafebabe 0xffffffffffffffff 0x7fffffffffffffff true false false
#guard shld 63 0xdeadbeefcafebabe 0x6bca1af286bca1b 0x35e50d79435e50d true false false
#guard shld 63 0x6bca1af286bca1b 0x0 0x8000000000000000 true false true
#guard shld 63 0x6bca1af286bca1b 0x3 0x8000000000000001 true false true
#guard shld 63 0x6bca1af286bca1b 0xffffffffffffffff 0xffffffffffffffff true false true
#guard shld 63 0x6bca1af286bca1b 0x6bca1af286bca1b 0x835e50d79435e50d true false true
#guard shld 63 0x8000000000000001 0x0 0x8000000000000000 false false true
#guard shld 63 0x8000000000000001 0x3 0x8000000000000001 false false true
#guard shld 63 0x8000000000000001 0xffffffffffffffff 0xffffffffffffffff false false true
#guard shld 63 0x8000000000000001 0x6bca1af286bca1b 0x835e50d79435e50d false false true
#guard shld 63 0x4000000000000000 0x0 0x0 false true false
#guard shld 63 0x4000000000000000 0x3 0x1 false false false
#guard shld 63 0x4000000000000000 0xffffffffffffffff 0x7fffffffffffffff false false false
#guard shld 63 0x4000000000000000 0x6bca1af286bca1b 0x35e50d79435e50d false false false

/-! ## `btr rax, n` -/

#guard btr 0 false 0x0 0x0 false false
#guard btr 0 true 0x0 0x0 false true
#guard btr 0 false 0x1 0x0 true false
#guard btr 0 true 0x1 0x0 true true
#guard btr 0 false 0x2 0x2 false false
#guard btr 0 true 0x2 0x2 false true
#guard btr 0 false 0x3 0x2 true false
#guard btr 0 true 0x3 0x2 true true
#guard btr 0 false 0x7fffffffffffffff 0x7ffffffffffffffe true false
#guard btr 0 true 0x7fffffffffffffff 0x7ffffffffffffffe true true
#guard btr 0 false 0x8000000000000000 0x8000000000000000 false false
#guard btr 0 true 0x8000000000000000 0x8000000000000000 false true
#guard btr 0 false 0xffffffffffffffff 0xfffffffffffffffe true false
#guard btr 0 true 0xffffffffffffffff 0xfffffffffffffffe true true
#guard btr 0 false 0x123456789abcdef 0x123456789abcdee true false
#guard btr 0 true 0x123456789abcdef 0x123456789abcdee true true
#guard btr 0 false 0xdeadbeefcafebabe 0xdeadbeefcafebabe false false
#guard btr 0 true 0xdeadbeefcafebabe 0xdeadbeefcafebabe false true
#guard btr 0 false 0x6bca1af286bca1b 0x6bca1af286bca1a true false
#guard btr 0 true 0x6bca1af286bca1b 0x6bca1af286bca1a true true
#guard btr 0 false 0x8000000000000001 0x8000000000000000 true false
#guard btr 0 true 0x8000000000000001 0x8000000000000000 true true
#guard btr 0 false 0x4000000000000000 0x4000000000000000 false false
#guard btr 0 true 0x4000000000000000 0x4000000000000000 false true
#guard btr 5 false 0x0 0x0 false false
#guard btr 5 true 0x0 0x0 false true
#guard btr 5 false 0x1 0x1 false false
#guard btr 5 true 0x1 0x1 false true
#guard btr 5 false 0x2 0x2 false false
#guard btr 5 true 0x2 0x2 false true
#guard btr 5 false 0x3 0x3 false false
#guard btr 5 true 0x3 0x3 false true
#guard btr 5 false 0x7fffffffffffffff 0x7fffffffffffffdf true false
#guard btr 5 true 0x7fffffffffffffff 0x7fffffffffffffdf true true
#guard btr 5 false 0x8000000000000000 0x8000000000000000 false false
#guard btr 5 true 0x8000000000000000 0x8000000000000000 false true
#guard btr 5 false 0xffffffffffffffff 0xffffffffffffffdf true false
#guard btr 5 true 0xffffffffffffffff 0xffffffffffffffdf true true
#guard btr 5 false 0x123456789abcdef 0x123456789abcdcf true false
#guard btr 5 true 0x123456789abcdef 0x123456789abcdcf true true
#guard btr 5 false 0xdeadbeefcafebabe 0xdeadbeefcafeba9e true false
#guard btr 5 true 0xdeadbeefcafebabe 0xdeadbeefcafeba9e true true
#guard btr 5 false 0x6bca1af286bca1b 0x6bca1af286bca1b false false
#guard btr 5 true 0x6bca1af286bca1b 0x6bca1af286bca1b false true
#guard btr 5 false 0x8000000000000001 0x8000000000000001 false false
#guard btr 5 true 0x8000000000000001 0x8000000000000001 false true
#guard btr 5 false 0x4000000000000000 0x4000000000000000 false false
#guard btr 5 true 0x4000000000000000 0x4000000000000000 false true
#guard btr 32 false 0x0 0x0 false false
#guard btr 32 true 0x0 0x0 false true
#guard btr 32 false 0x1 0x1 false false
#guard btr 32 true 0x1 0x1 false true
#guard btr 32 false 0x2 0x2 false false
#guard btr 32 true 0x2 0x2 false true
#guard btr 32 false 0x3 0x3 false false
#guard btr 32 true 0x3 0x3 false true
#guard btr 32 false 0x7fffffffffffffff 0x7ffffffeffffffff true false
#guard btr 32 true 0x7fffffffffffffff 0x7ffffffeffffffff true true
#guard btr 32 false 0x8000000000000000 0x8000000000000000 false false
#guard btr 32 true 0x8000000000000000 0x8000000000000000 false true
#guard btr 32 false 0xffffffffffffffff 0xfffffffeffffffff true false
#guard btr 32 true 0xffffffffffffffff 0xfffffffeffffffff true true
#guard btr 32 false 0x123456789abcdef 0x123456689abcdef true false
#guard btr 32 true 0x123456789abcdef 0x123456689abcdef true true
#guard btr 32 false 0xdeadbeefcafebabe 0xdeadbeeecafebabe true false
#guard btr 32 true 0xdeadbeefcafebabe 0xdeadbeeecafebabe true true
#guard btr 32 false 0x6bca1af286bca1b 0x6bca1ae286bca1b true false
#guard btr 32 true 0x6bca1af286bca1b 0x6bca1ae286bca1b true true
#guard btr 32 false 0x8000000000000001 0x8000000000000001 false false
#guard btr 32 true 0x8000000000000001 0x8000000000000001 false true
#guard btr 32 false 0x4000000000000000 0x4000000000000000 false false
#guard btr 32 true 0x4000000000000000 0x4000000000000000 false true
#guard btr 63 false 0x0 0x0 false false
#guard btr 63 true 0x0 0x0 false true
#guard btr 63 false 0x1 0x1 false false
#guard btr 63 true 0x1 0x1 false true
#guard btr 63 false 0x2 0x2 false false
#guard btr 63 true 0x2 0x2 false true
#guard btr 63 false 0x3 0x3 false false
#guard btr 63 true 0x3 0x3 false true
#guard btr 63 false 0x7fffffffffffffff 0x7fffffffffffffff false false
#guard btr 63 true 0x7fffffffffffffff 0x7fffffffffffffff false true
#guard btr 63 false 0x8000000000000000 0x0 true false
#guard btr 63 true 0x8000000000000000 0x0 true true
#guard btr 63 false 0xffffffffffffffff 0x7fffffffffffffff true false
#guard btr 63 true 0xffffffffffffffff 0x7fffffffffffffff true true
#guard btr 63 false 0x123456789abcdef 0x123456789abcdef false false
#guard btr 63 true 0x123456789abcdef 0x123456789abcdef false true
#guard btr 63 false 0xdeadbeefcafebabe 0x5eadbeefcafebabe true false
#guard btr 63 true 0xdeadbeefcafebabe 0x5eadbeefcafebabe true true
#guard btr 63 false 0x6bca1af286bca1b 0x6bca1af286bca1b false false
#guard btr 63 true 0x6bca1af286bca1b 0x6bca1af286bca1b false true
#guard btr 63 false 0x8000000000000001 0x1 true false
#guard btr 63 true 0x8000000000000001 0x1 true true
#guard btr 63 false 0x4000000000000000 0x4000000000000000 false false
#guard btr 63 true 0x4000000000000000 0x4000000000000000 false true

/-! ## Counts the model does not cover

`shld` by 0 (which changes nothing) or by 64 or more (masked to 6 bits), and
`btr` of a bit offset of 64 or more (taken modulo 64), are not modelled: they
fault. -/

#guard (exec (.shld .rax .rcx 0) (s 1 2)).isNone
#guard (exec (.shld .rax .rcx 64) (s 1 2)).isNone
#guard (exec (.btr .rax 64) (s 1 2)).isNone

-- Only the destination and the flags change.
#guard (exec (.imul3 .rax .rcx 19) (s 3 5)).map (fun t => (t.gpr .rcx, t.gpr .rdx, t.gpr .r15)) == some (5, 7, 7)
#guard (exec (.shld .rax .rcx 1) (s 3 5)).map (fun t => (t.gpr .rcx, t.gpr .rdx, t.gpr .r15)) == some (5, 7, 7)
#guard (exec (.btr .rax 1) (s 3 5)).map (fun t => (t.gpr .rcx, t.gpr .rdx, t.gpr .r15)) == some (5, 7, 7)

/-! ## Printing -/

#guard Instr.asm (.imul3 .rax .r12 19) == ["imul rax, r12, 19"]
#guard Instr.asm (.imul3 .rax .r12 (BitVec.ofInt 32 (-1))) == ["imul rax, r12, -1"]
#guard Instr.asm (.shld .r12 .r11 1) == ["shld r12, r11, 1"]
#guard Instr.asm (.btr .r11 63) == ["btr r11, 63"]

-- All three are in the x86-64 baseline, and write `rsp` only as their destination.
#guard isa.requires (.imul3 .rax .rcx 19) == []
#guard isa.requires (.shld .rax .rcx 1) == []
#guard isa.requires (.btr .rax 63) == []
#guard isa.writesSp (.imul3 .rsp .rax 19)
#guard !isa.writesSp (.imul3 .rax .rsp 19)
#guard isa.writesSp (.shld .rsp .rax 1)
#guard !isa.writesSp (.shld .rax .rsp 1)
#guard isa.writesSp (.btr .rsp 3)

end VG.Test.X86_64ShldBtrImul3
