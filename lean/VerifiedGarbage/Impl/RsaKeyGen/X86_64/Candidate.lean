module

public import VerifiedGarbage.Impl.Rsa.X86_64
public import VerifiedGarbage.Impl.Rsa.X86_64.Crt
public import VerifiedGarbage.Impl.RsaKeyGen.Primes

/-!
# A candidate for a prime of an RSA key on x86-64

`vg_rsa_keygen_candidate(out, out_len, used, e, e_len, p, p_len, rand,
rand_len, scratch, scratch_len)`: the first six arguments in registers, the
others on the stack. The working space is a header and arrays as
`vg_rsa_public`'s (`Impl/Bignum/X86_64.lean`), for `w = out_len / 8` words,
with more arrays after the eight: Miller–Rabin's table of 16 entries, its
exponent, `R mod c` and `c − R mod c` (see "Arrays" below), and before
Miller–Rabin the table of small primes (256 words). The candidate `c` is in
`aN`, where Montgomery multiplication `mul` (the baseline `mm`, or one for
other CPU features) takes its modulus.

1. `out` is zeroed; if `rand` is shorter than `out_len`, the result is 0.
2. `c`: the first `out_len` octets of `rand`, its two top bits and its low
   bit set.
3. If `p` is given: `|c − p|` (a subtraction, then a negation under the mask
   of its borrow) compared with `2^(8 out_len − 100)`; the result is 2 if it
   is not above.
4. Trial division by the primes 3 to 8161 (3 to 3671 for `w ≤ 16`), from a
   table of four 16-bit primes a word: for each prime `s`, `c 2^(−64 w) mod s`
   by Montgomery reduction of `c`'s 32-bit halves, from the least
   significant (`acc := (acc + h) 2^(−32) mod s`, kept below `2 s`), with
   `−s⁻¹ mod 2^64` by Newton's iteration; `s` divides `c` iff `acc` is 0 or
   `s`. The masks of all primes are or'ed, and the result is 3 if one is
   set. The table's last prime of each half is 3 again, which changes
   nothing.
5. `gcd(c − 1, e)`: 3 if `e` is even; for `e = 1` nothing; otherwise
   `(c − 1) mod e` bit by bit, then 128 steps of a binary gcd on words with
   masks (`Proof/RsaKeyGen/Gcd.lean`); 3 unless it is 1.
6. `-c⁻¹`, `R² mod c` as `vg_rsa_public` computes it (here `c`'s top bit is
   set), `R mod c` (`aR1`) and `c − R mod c` (`aRm1`): 1 and `−1` in
   Montgomery form. Then Miller–Rabin's exponent: for `c − 1 = m 2^a`
   (`m` odd), `E = (c − 1) / 2^σ` with `σ ∈ [1, 4]` and `σ ≡ a (mod 4)`, so
   that `E = m 16^v`: `c / 2`, halved again under the masks of `σ > 1`,
   `σ > 2` and `σ > 3`, which come from the lowest set bit of `c − 1`'s
   lowest nonzero word (found by masks over its words).
7. Miller–Rabin, one witness an iteration: 0 if `rand` has fewer than
   `out_len` octets left; else the witness `x`, the next `out_len` octets,
   uniform if `2 ≤ x < c − 1`, otherwise bit 1 set and the top bit cleared;
   its Montgomery form, the table of its powers `T_j = x^j R mod c`
   (`j < 16`); then `E`'s windows of 4 bits from the top
   (`Proof/RsaKeyGen/MrWindow.lean`): four squarings `y := y²`, each or'ing
   the flag with `y = −1`, then `y := y T_d` for the window's digit `d`, the
   entry read from all 16 by masks (two passes of the CRT's gathering), and
   if `d ≠ 0` the flag `y = 1 ∨ y = −1`; then three more squarings, or'ing
   the flag with `y = −1` under the masks of `σ > 1`, `σ > 2`, `σ > 3`. The
   flag is `mrIteration`'s result: the windows end at `b^m`'s lowest set
   bit, and the squarings after it look at `b^m` squared up to `a − 1`
   times. A clear flag ends with 3; otherwise the witness counts, and the
   loop goes on while fewer than 16 witnesses or fewer than
   `BN_prime_checks_for_size` uniform ones have passed; then the result is
   1 and `c` is written to `out`.

`used` is written at the end: the octets read (`out_len` per number), or 0
for the result 0.

Header words that address memory or decide a branch are loaded into a
register before they are compared or added, and before anything secret is
stored into the arrays, so the taint analysis knows them public.
-/

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

/-! ## The table of small primes (`Impl/RsaKeyGen/Primes.lean`) -/

/-- Store word `i` of the table at `[rbx + 8 i]`. -/
def tabStore (i : Nat) : List Instr :=
  [.movImm64 .rax (BitVec.ofNat 64 (tabWord i)), .store { base := .rbx, disp := 8 * i } .rax]

/-- The table, at `rbx`. -/
def tabWrite : List Instr := (List.range 256).flatMap tabStore

/-! ## Entry and exit -/

/-- The stack argument `i` (from 1). -/
def kStk (i : Nat) : MemOp := { base := .rsp, disp := 8 * i }

/-- Save the callee-saved registers and the arguments in the header at
`scratch`, with its base in `rdi`. -/
def kEntry : List Instr :=
  ([.mov .r11 (.mem (kStk 4))] : List Instr) ++
  (saved.zipIdx.map fun (r, i) => .store { base := .r11, disp := 8 * i } r) ++
  ([.store { base := .r11, disp := 8 * kOut } .rdi, .store { base := .r11, disp := 8 * kLen } .rsi,
    .store { base := .r11, disp := 8 * kUsedP } .rdx, .store { base := .r11, disp := 8 * kE } .rcx,
    .store { base := .r11, disp := 8 * kElen } .r8, .store { base := .r11, disp := 8 * kP } .r9,
    .mov .rax (.mem (kStk 1)), .store { base := .r11, disp := 8 * kPlen } .rax,
    .mov .rax (.mem (kStk 2)), .store { base := .r11, disp := 8 * kRand } .rax,
    .mov .rax (.mem (kStk 3)), .store { base := .r11, disp := 8 * kRandLen } .rax,
        .mov .rdi (.reg .r11)] : List Instr)

/-- Zeros to the `out_len` bytes of `out`. -/
def zeroOut : Prog isa :=
  .seq (.block [.mov .rsi (.mem (hdr kOut)), .mov .rcx (.mem (hdr kLen)), .mov32 .rax (.imm 0)])
    (.loop (.block [.store8 (at0 .rsi) .rax, .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) .ne)

/-- `rax` to `used`, the status `st` returned, the callee-saved registers
restored. -/
def finish (st : Nat) : List Instr :=
  ([.mov .rdx (.mem (hdr kUsedP)), .store (at0 .rdx) .rax, .mov32 .rax (.imm (BitVec.ofNat 32 st))] : List Instr) ++
    exit

/-- Status 0: `used` is 0. -/
def finNone : Prog isa := .block (([.mov32 .rax (.imm 0)] : List Instr) ++ finish 0)

/-- Status `st` (2 or 3): `used` is the octets read. -/
def finUsed (st : Nat) : Prog isa := .block (([.mov .rax (.mem (hdr kUsed))] : List Instr) ++ finish st)

/-- Status 1: `used` the octets read, and `c` to `out` (the bases and the
length loaded first, so that none is read from the header once memory
outside it has been written). -/
def finPrime : Prog isa :=
  .seq (.block [.mov .rbx (.mem (hdr (sArr aN))), .mov .rsi (.mem (hdr kOut)), .mov .rcx (.mem (hdr kLen)),
      .mov .r15 (.imm (BitVec.ofInt 32 (-1))), .mov .rax (.mem (hdr kUsed)), .mov .rdx (.mem (hdr kUsedP)),
      .store (at0 .rdx) .rax])
    (.seq storeBE (.block (([.mov32 .rax (.imm 1)] : List Instr) ++ exit)))

/-! ## The candidate -/

/-- `w := out_len / 8` (in `r12` and its slot), the arrays' bases, `c` from
the first `out_len` octets of `rand` with its two top bits and its low bit
set, and `used := out_len`. -/
def loadC : List (Prog isa) := [
  .block (([.mov .rcx (.mem (hdr kLen)), .mov .r12 (.reg .rcx), .shift .shr .r12 3,
      .store (hdr sW) .r12] : List Instr) ++
    setBases ++ ([.mov .rsi (.mem (hdr kRand)), .mov .rbx (.mem (hdr (sArr aN)))] : List Instr)),
  loadBE,
  .block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aN))),
    .movImm64 .rdx (BitVec.ofNat 64 (3 * 2 ^ 62)), .alu .or .rdx (.mem (ix .rbx .r12 (-8))),
    .store (ix .rbx .r12 (-8)) .rdx, .mov .rdx (.mem (at0 .rbx)), .alu .or .rdx (.imm 1), .store (at0 .rbx) .rdx,
    .mov .rax (.mem (hdr kLen)), .store (hdr kUsed) .rax]]

/-! ## Too close to `p` -/

/-- `[aAcc] := c − p` over `w` words, `rbp` the mask of its borrow. -/
def diffLoop : List (Prog isa) := [
  .block [.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aN))), .mov .r10 (.mem (hdr (sArr aX))),
    .mov .rsi (.mem (hdr (sArr aAcc))), .mov32 .rbp (.imm 0)],
  wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .r8 .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)),
    .store (ix .rsi .r14) .rax, cfToRbp]]

/-- `[aAcc] := ([aAcc] ⊕ m) + (m & 1)` for the mask `m` (`rbp`, kept in `r15`):
negated if `m` is all ones, so `|c − p|`. The carry, starting as `m`, is
kept in `rbp` as a mask. -/
def negLoop : List (Prog isa) := [
  .block [.mov .r15 (.reg .rbp), .mov .rsi (.mem (hdr (sArr aAcc)))],
  wordLoop 0 [.mov .rax (.mem (ix .rsi .r14)), .alu .xor .rax (.reg .r15), cfFromRbp, .alu .adc .rax (.imm 0),
    .store (ix .rsi .r14) .rax, cfToRbp]]

/-- `rbp` the mask of `|c − p| ≤ 2^(64 w − 100)`, or 0 without `p`: the
bound in `aTmp` (word `w − 2` is `2^28`), then the mask of
`bound < |c − p|`, inverted. -/
def closeCheck : List (Prog isa) :=
  [.block [.mov .rax (.mem (hdr kPlen)), .alu .test .rax (.reg .rax), .mov32 .rbp (.imm 0)],
   .ite .ne (seqs (([
      .block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr kP)), .mov .rcx (.mem (hdr kLen)),
        .mov .rbx (.mem (hdr (sArr aX)))],
      loadBE] : List (Prog isa)) ++ diffLoop ++ negLoop ++ ([
      .block [.mov .r12 (.mem (hdr sW)), .mov .rcx (.reg .r12), .alu .sub .rcx (.imm 2),
        .mov32 .rdx (.imm (BitVec.ofNat 32 (2 ^ 28)))],
      setWord aTmp .rcx,
      .block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aTmp))), .mov .r10 (.mem (hdr (sArr aAcc))),
        .mov32 .rbp (.imm 0)],
      wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp],
      .block [.alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))]] : List (Prog isa))))
    (.block []),
   .block [.alu .test .rbp (.reg .rbp)]]

/-! ## Trial division -/

/-- `acc := (acc + h) 2^(−32) mod s` (below `2 s`) for the 32-bit `h` in
`rax`, `acc` in `rbp`, `s` in `rbx` and `−s⁻¹ mod 2^64` in `r15`:
Montgomery reduction of `x = acc + h < s 2^32`. -/
def redc32 : List Instr :=
  [.alu .add .rax (.reg .rbp), .mov .rcx (.reg .rax), .mul .r15, .mov32 .rax (.reg .rax), .mul .rbx,
    .alu .add .rax (.reg .rcx), .shift .shr .rax 32, .mov .rbp (.reg .rax)]

/-- For entry `j` of the table word in `kT1`: `s` into `rbx`, `−s⁻¹` into
`r15`, `acc` over `c`'s halves, and the mask of `acc ∈ {0, s}` or'ed into
`kT2`. -/
def trialEntry (j : Nat) : List (Prog isa) := [
  .block (([.mov .rbx (.mem (hdr kT1))] : List Instr) ++ (if j = 0 then [] else [.shift .shr .rbx (16 * j)]) ++
    ([.alu .and .rbx (.imm 0xFFFF)] : List Instr) ++ minv ++
    ([.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aN))), .mov32 .rbp (.imm 0)] : List Instr)),
  wordLoop 0 (([.mov .rsi (.mem (ix .r8 .r14)), .mov32 .rax (.reg .rsi)] : List Instr) ++ redc32 ++
    ([.mov .rax (.reg .rsi), .shift .shr .rax 32] : List Instr) ++ redc32),
  .block [.mov .rax (.reg .rbp), .alu .cmp .rax (.imm 1), .alu .sbb .rdx (.reg .rdx), .alu .xor .rax (.reg .rbx),
    .alu .cmp .rax (.imm 1), .alu .sbb .rcx (.reg .rcx), .alu .or .rdx (.reg .rcx), .alu .or .rdx (.mem (hdr kT2)),
    .store (hdr kT2) .rdx]]

/-- The table at `aTab`, then for each of its first `128` words (`256` for
`w > 16`, in `kT0`) its four entries; ZF clear if one divides `c`. -/
def trial : List (Prog isa) := [
  .block (extBase aTab .rbx ++ tabWrite ++
    ([.mov32 .rax (.imm 128), .mov .rcx (.mem (hdr sW)), .alu .cmp .rcx (.imm 17)] : List Instr)),
  .ite .b (.block []) (.block [.mov32 .rax (.imm 256)]),
  .block [.store (hdr kT0) .rax, .mov32 .rax (.imm 0), .store (hdr kT2) .rax, .mov32 .r13 (.imm 0)],
  .loop (seqs (([.block (extBase aTab .rbx ++ ([.mov .rax (.mem (ix .rbx .r13)),
      .store (hdr kT1) .rax] : List Instr))] : List (Prog isa)) ++
      trialEntry 0 ++ trialEntry 1 ++ trialEntry 2 ++ trialEntry 3 ++
      ([.block [.alu .add .r13 (.imm 1), .mov .rax (.mem (hdr kT0)),
          .alu .cmp .r13 (.reg .rax)]] : List (Prog isa)))) .ne,
  .block [.mov .rax (.mem (hdr kT2)), .alu .test .rax (.reg .rax)]]

/-! ## `gcd(c − 1, e)` -/

/-- `e` (`e_len` octets, most significant first) into `rbx`. -/
def loadE : List (Prog isa) := [
  .block [.mov .rsi (.mem (hdr kE)), .mov .rcx (.mem (hdr kElen)), .mov32 .rbx (.imm 0)],
  .loop (.block [.shift .ror .rbx 56, .movzx8 .rax (at0 .rsi), .alu .add .rbx (.reg .rax), .alu .add .rsi (.imm 1),
    .alu .sub .rcx (.imm 1)]) .ne]

/-- One bit of `(c − 1) mod e`: the top bit of `rdx` shifted out into
`r = rsi` (`r := 2 r + bit`, its carry in `rcx`), then `r − e` (`rbx`)
kept if that carried or did not borrow. -/
def modBit : List Instr :=
  [.alu .add .rdx (.reg .rdx), .alu .adc .rsi (.reg .rsi), .alu .sbb .rcx (.reg .rcx), .mov .rax (.reg .rsi),
    .alu .sub .rax (.reg .rbx), .alu .sbb .rbp (.reg .rbp), .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1))),
    .alu .or .rcx (.reg .rbp), .alu .xor .rax (.reg .rsi), .alu .and .rax (.reg .rcx), .alu .xor .rsi (.reg .rax)]

/-- `modE`'s word loop, with the bit loop: its body for word `w − 1 − r14`. -/
def modWord : Prog isa :=
  .seq (.block [.mov .rax (.reg .r12), .alu .sub .rax (.imm 1), .alu .sub .rax (.reg .r14),
      .mov .rdx (.mem (ix .r8 .rax)), .mov32 .r13 (.imm 64)])
    (.loop (.block (modBit ++ ([.alu .sub .r13 (.imm 1)] : List Instr))) .ne)

/-- `rsi := (c − 1) mod e` for `e` in `kG` and `rbx`. -/
def modLoop : List (Prog isa) := [
  .block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aN))), .mov .rbx (.mem (hdr (sArr aX)))],
  copyWords,
  .block [.mov .r8 (.reg .rbx), .mov .rax (.mem (at0 .rbx)), .alu .and .rax (.imm (BitVec.ofInt 32 (-2))),
    .store (at0 .rbx) .rax, .mov .rbx (.mem (hdr kG)), .mov32 .rsi (.imm 0), .mov32 .r14 (.imm 0)],
  .loop (.seq modWord (.block [.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)])) .ne]

/-- One step of the binary gcd on `u = rsi` and the odd `v = rbx`: if `u`
is odd, `(|u − v|, min u v)`; then `u / 2`. -/
def bgcdStep : List Instr :=
  [.mov .rax (.reg .rsi), .alu .and .rax (.imm 1), .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rax),
    .mov .rax (.reg .rsi), .alu .sub .rax (.reg .rbx), .alu .sbb .rdx (.reg .rdx),
    .alu .xor .rax (.reg .rdx), .alu .sub .rax (.reg .rdx),
    .mov .rbp (.reg .rsi), .alu .xor .rbp (.reg .rbx), .alu .and .rbp (.reg .rdx), .alu .xor .rbp (.reg .rbx),
    .alu .xor .rax (.reg .rsi), .alu .and .rax (.reg .rcx), .alu .xor .rsi (.reg .rax),
    .alu .xor .rbp (.reg .rbx), .alu .and .rbp (.reg .rcx), .alu .xor .rbx (.reg .rbp),
    .shift .shr .rsi 1]

/-- `kG := gcd(c − 1, e)` for the odd `e > 1` in `rbx`: `(c − 1) mod e`, then
128 steps. -/
def gcdE : List (Prog isa) :=
  ([.block [.store (hdr kG) .rbx]] : List (Prog isa)) ++ modLoop ++
  ([.block [.mov .rbx (.mem (hdr kG)), .mov32 .r13 (.imm 128)],
   .loop (.block (bgcdStep ++ ([.alu .sub .r13 (.imm 1)] : List Instr))) .ne,
   .block [.store (hdr kG) .rbx]] : List (Prog isa))

/-- `gcd(c − 1, e)` into `kG`, or an even number for an even `e`; then ZF
clear unless it is 1. -/
def gcdCheck : List (Prog isa) :=
  loadE ++ ([
  .block [.store (hdr kG) .rbx, .mov .rax (.reg .rbx), .alu .and .rax (.imm 1)],
  .ite .e (.block [])
    (seqs [.block [.alu .cmp .rbx (.imm 1)], .ite .e (.block []) (seqs gcdE)]),
  .block [.mov .rax (.mem (hdr kG)), .alu .cmp .rax (.imm 1)]] : List (Prog isa))

/-! ## Montgomery arithmetic modulo `c` -/

/-- `-c⁻¹`, the number 1, `R² mod c`, `R mod c` into `aR1` and `c − R mod c`
into `aRm1`, and the number of uniform witnesses needed. -/
def montSetup (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  .block (([.mov .r10 (.mem (hdr (sArr aN))), .mov .r12 (.mem (hdr sW)),
      .mov .rbx (.mem (at0 .r10))] : List Instr) ++ minv ++
    ([.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)] : List Instr)),
  setWord aOne .rcx,
  .block [.movImm64 .rdx (BitVec.ofNat 64 (2 ^ 63)), .mov .rcx (.reg .r12), .alu .sub .rcx (.imm 1)],
  setWord aR2 .rcx,
  .block [.mov .rcx (.mem (hdr sW)), .alu .add .rcx (.imm 1)],
  doubles aN aAcc aTmp aR2 kT0,
  mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2,
  mul aY aR2 aOne,
  .block (([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aY)))] : List Instr) ++ extBase aR1 .rbx),
  copyWords,
  .block (([.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aN)))] : List Instr) ++ extBase aR1 .r10 ++
    extBase aRm1 .rsi ++
    ([.mov32 .rbp (.imm 0)] : List Instr)),
  wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .r8 .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)),
    .store (ix .rsi .r14) .rax, cfToRbp],
  .block [.mov .rcx (.mem (hdr sW)), .mov32 .rax (.imm 27), .alu .cmp .rcx (.imm 5)],
  .ite .b (.block []) (seqs [
    .block [.mov32 .rax (.imm 8), .alu .cmp .rcx (.imm 6)],
    .ite .b (.block []) (seqs [
      .block [.mov32 .rax (.imm 7), .alu .cmp .rcx (.imm 7)],
      .ite .b (.block []) (seqs [
        .block [.mov32 .rax (.imm 6), .alu .cmp .rcx (.imm 8)],
        .ite .b (.block []) (seqs [
          .block [.mov32 .rax (.imm 5), .alu .cmp .rcx (.imm 22)],
          .ite .b (.block []) (seqs [
            .block [.mov32 .rax (.imm 4), .alu .cmp .rcx (.imm 59)],
            .ite .b (.block []) (.block [.mov32 .rax (.imm 3)])])])])])]),
  .block [.store (hdr kChecks) .rax]]

/-! ## Miller–Rabin's exponent

For `c − 1 = m 2^a` (`m` odd), the exponentiation is by `E = (c − 1) / 2^σ`
for `σ ∈ [1, 4]`, `σ ≡ a (mod 4)`: `E = m 2^(a − σ)` has its lowest set bit
at a multiple of 4, where a window of 4 bits ends. `σ` is secret: `E` is
`c / 2` halved under the masks of `σ > 1`, `σ > 2` and `σ > 3`, which
come from the lowest set bit `l = 2^(a mod 64)` of the lowest nonzero word
of `c − 1` (`l & K ≠ 0` for the constants `K` of `sigK`). -/

/-- `rbp := ` the lowest nonzero word of `c − 1` (`c`'s words, bit 0 of the
first cleared): `rbp |= word & mask (rbp = 0)` from the bottom. -/
def lowWord : List (Prog isa) := [
  .block [.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aN))), .mov .rbp (.mem (at0 .r8)),
    .alu .and .rbp (.imm (BitVec.ofInt 32 (-2)))],
  wordLoop 1 [.mov .rax (.mem (ix .r8 .r14)), .alu .cmp .rbp (.imm 1), .alu .sbb .rdx (.reg .rdx),
    .alu .and .rax (.reg .rdx), .alu .or .rbp (.reg .rax)]]

/-- The masks of `σ > j` (`j = 1, 2, 3`) are those of `l & sigK j ≠ 0`: the
bits whose position mod 4 is 0, 2 or 3; 0 or 3; 0. -/
def sigK : Nat → BitVec 64
  | 1 => 0xDDDDDDDDDDDDDDDD
  | 2 => 0x9999999999999999
  | _ => 0x1111111111111111

/-- `[rbx] := r15 ? [rsi] / 2 : [rsi]` over `w` words (`r12`), in place
when `rbx = rsi`: the word below is written once the next is read, the word
in `rbp`. -/
def halfPass : List (Prog isa) := [
  .block [.mov .rbp (.mem (at0 .rsi))],
  wordLoop 1 [.mov .rax (.mem (ix .rsi .r14)), .mov .rdx (.reg .rax), .shift .shl .rdx 63, .mov .rcx (.reg .rbp),
    .shift .shr .rcx 1, .alu .or .rcx (.reg .rdx), .alu .xor .rcx (.reg .rbp), .alu .and .rcx (.reg .r15),
    .alu .xor .rcx (.reg .rbp), .store (ix .rbx .r14 (-8)) .rcx, .mov .rbp (.reg .rax)],
  .block [.mov .rcx (.reg .rbp), .shift .shr .rcx 1, .alu .xor .rcx (.reg .rbp), .alu .and .rcx (.reg .r15),
    .alu .xor .rcx (.reg .rbp), .store (ix .rbx .r12 (-8)) .rcx]]

/-- `[aE] := [aE] / 2` under the mask of `σ > j`, `aE`'s base in `rbx` and `w`
in `r12`. -/
def halfCond (j : Nat) : List (Prog isa) :=
  .block [.mov .rsi (.reg .rbx), .movImm64 .r15 (sigK j), .alu .and .r15 (.mem (ix .rbx .r12)),
    .alu .cmp .r15 (.imm 1), .alu .sbb .r15 (.reg .r15), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))] :: halfPass

/-- `l` after the `w` words of `aE`, then `[aE] := E`. The header is read
before anything is stored: the halvings keep `aE`'s base in `rbx` and `w` in
`r12`. -/
def expSetup : List (Prog isa) :=
  lowWord ++ [
  .block (extBase aE .rbx ++ ([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aN))),
    .mov .r15 (.imm (BitVec.ofInt 32 (-1))), .mov32 .rax (.imm 0), .alu .sub .rax (.reg .rbp),
    .alu .and .rax (.reg .rbp), .store (ix .rbx .r12) .rax] : List Instr))] ++
  halfPass ++ halfCond 1 ++ halfCond 2 ++ halfCond 3

/-! ## Miller–Rabin -/

/-- The mask of `[aY] = [j]` over `w` words into `rbp` (`j` an extra array,
its base into `r10`). -/
def eqMask (j : Nat) : List (Prog isa) := [
  .block (([.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aY)))] : List Instr) ++ extBase j .r10 ++
    ([.mov32 .rbp (.imm 0)] : List Instr)),
  wordLoop 0 [.mov .rax (.mem (ix .rbx .r14)), .alu .xor .rax (.mem (ix .r10 .r14)), .alu .or .rbp (.reg .rax)],
  .block [.alu .cmp .rbp (.imm 1), .alu .sbb .rbp (.reg .rbp)]]

/-- `y := y²`, the flag or'ed with `y = −1`. -/
def mrSq (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  [mul aY aY aY] ++ eqMask aRm1 ++
  [.block [.mov .rax (.mem (hdr kFlag)), .alu .or .rax (.reg .rbp), .store (hdr kFlag) .rax]]

/-- The first selection pass's registers (`Impl/Rsa/X86_64/Crt.lean`):
`r15 = 0`, `r11 = 8 (w + 2)`, `r13 = 2 ⌈w / 2⌉`, `rbx = aXm` and `rcx` the
entry 0. -/
def selRegs : List Instr :=
  ([.mov32 .r15 (.imm 0), .mov .r12 (.mem (hdr sW)), .mov .r11 (.reg .r12),
    .alu .add .r11 (.imm 2), .alu .add .r11 (.reg .r11), .alu .add .r11 (.reg .r11), .alu .add .r11 (.reg .r11),
    .mov .r13 (.reg .r12), .alu .add .r13 (.imm 1), .shift .shr .r13 1, .alu .add .r13 (.reg .r13),
    .mov .rbx (.mem (hdr (sArr aXm)))] : List Instr) ++ extBase aT0 .rcx

/-- The second pass's: `r15 = 8` and `rcx` the entry 8, from the first's;
the header is not read again once `aXm` has been written. -/
def selNext : List Instr :=
  [.mov32 .r15 (.imm 8), .mov .rax (.reg .r11), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .alu .add .rcx (.reg .rax)]

/-- A pass's masks of `r15 + j = d` (`d` in `kG`) in `xmm(8 + j)`, that of
`r15 = 8` in `xmm7`, and the bases of its eight entries. -/
def selMasks : List (Prog isa) :=
  [.block (Crt.selMask 0 (.mem (hdr kG)) .xmm8), .block (Crt.selMask 1 (.mem (hdr kG)) .xmm9),
    .block (Crt.selMask 2 (.mem (hdr kG)) .xmm10), .block (Crt.selMask 3 (.mem (hdr kG)) .xmm11),
    .block (Crt.selMask 4 (.mem (hdr kG)) .xmm12), .block (Crt.selMask 5 (.mem (hdr kG)) .xmm13),
    .block (Crt.selMask 6 (.mem (hdr kG)) .xmm14), .block (Crt.selMask 7 (.mem (hdr kG)) .xmm15),
    .block (Crt.selMask 0 (.imm 8) .xmm7),
    .block Crt.gatherBases]

/-- The selection of `T_d` (`d` in `kG`) into `aXm` in two passes, over the
entries 0 to 7 and 8 to 15, as `Crt.gatherPass`: each pair of words of
`aXm` becomes `(aXm & xmm7) | OR_j (T_(8p+j) & xmm(8+j))`. -/
def mrSel : List (Prog isa) :=
  [seqs (.block selRegs :: selMasks), .loop (seqs Crt.gatherBody) .ne,
    seqs (.block selNext :: selMasks), .loop (seqs Crt.gatherBody) .ne]

/-- One window, the digit `d` at the top of `kV`: four squarings, `T_d` into
`aXm` by masks, `y := y T_d`; the flag `P := d ≠ 0 ? (y = 1 ∨ y = −1) : P`;
then `kV := kV << 4` and `kBits := kBits − 1` (ZF set when it is 0). -/
def mrWin (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  mrSq mul ++ mrSq mul ++ mrSq mul ++ mrSq mul ++
  [.block [.mov .rax (.mem (hdr kV)), .shift .shr .rax 60, .store (hdr kG) .rax]] ++ mrSel ++
  [mul aY aY aXm] ++ eqMask aRm1 ++ [.block [.store (hdr kG) .rbp]] ++ eqMask aR1 ++
  [.block [.mov .rax (.mem (hdr kV)), .shift .shr .rax 60, .alu .cmp .rax (.imm 1), .alu .sbb .r15 (.reg .r15),
    .mov .rdx (.mem (hdr kG)), .alu .or .rbp (.reg .rdx), .mov .rax (.mem (hdr kFlag)), .alu .and .rax (.reg .r15),
    .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1))), .alu .and .rbp (.reg .r15), .alu .or .rax (.reg .rbp),
    .store (hdr kFlag) .rax,
    .mov .rax (.mem (hdr kV)), .shift .shl .rax 4, .store (hdr kV) .rax,
    .mov .rax (.mem (hdr kBits)), .alu .sub .rax (.imm 1), .store (hdr kBits) .rax]]

/-- A squaring after the windows: `y := y²`, the flag or'ed with `y = −1`
under the mask of `σ > j` (from `l`). -/
def mrLast (mul : Nat → Nat → Nat → Prog isa) (j : Nat) : List (Prog isa) :=
  [mul aY aY aY] ++ eqMask aRm1 ++
  [.block (extBase aE .rbx ++ ([.mov .r12 (.mem (hdr sW)), .movImm64 .rdx (sigK j),
    .alu .and .rdx (.mem (ix .rbx .r12)), .alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx),
    .alu .xor .rdx (.imm (BitVec.ofInt 32 (-1))), .alu .and .rbp (.reg .rdx), .mov .rax (.mem (hdr kFlag)),
    .alu .or .rax (.reg .rbp), .store (hdr kFlag) .rax] : List Instr))]

/-- The flag over the windows of `E`, its words from the top, 16 windows
each, then three more squarings: `mrIteration`'s result. -/
def mrExpLoop (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  .block [.mov .rax (.mem (hdr sW)), .store (hdr kWords) .rax, .mov32 .rax (.imm 0), .store (hdr kFlag) .rax],
  .loop (seqs [
    .block (([.mov .rax (.mem (hdr kWords)), .alu .sub .rax (.imm 1), .store (hdr kWords) .rax] : List Instr) ++
      extBase aE .rdx ++ ([.mov .rax (.mem (hdr kWords)), .mov .rcx (.mem (ix .rdx .rax)), .store (hdr kV) .rcx,
      .mov32 .rcx (.imm 16), .store (hdr kBits) .rcx] : List Instr)),
    .loop (seqs (mrWin mul)) .ne,
    .block [.mov .rax (.mem (hdr kWords)), .alu .test .rax (.reg .rax)]]) .ne] ++
  mrLast mul 1 ++ mrLast mul 2 ++ mrLast mul 3

/-- The witness in `aX` from the next `out_len` octets of `rand`, `used`
advanced; the mask of `2 ≤ x < c − 1` (`(x | 1) < c`) into `kU`; if it is
clear, bit 1 set and the top bit cleared. -/
def mrWitness : List (Prog isa) := [
  .block [.mov .rsi (.mem (hdr kRand)), .mov .rax (.mem (hdr kUsed)), .alu .add .rsi (.reg .rax),
    .mov .rcx (.mem (hdr kLen)), .mov .rbx (.mem (hdr (sArr aX))), .alu .add .rax (.reg .rcx),
    .store (hdr kUsed) .rax],
  loadBE,
  -- `rbp := (x & ~1) | x_1 | … | x_(w−1)`.
  .block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aX))), .mov .rbp (.mem (at0 .rbx)),
    .alu .and .rbp (.imm (BitVec.ofInt 32 (-2)))],
  wordLoop 1 [.mov .rax (.mem (ix .rbx .r14)), .alu .or .rbp (.reg .rax)],
  -- `r15 := ` the mask of `x ≥ 2`; `rbp := ` the borrow of `(x | 1) − c`.
  .block [.alu .cmp .rbp (.imm 1), .alu .sbb .r15 (.reg .r15), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1))),
    .mov .r10 (.mem (hdr (sArr aN))), .mov .rax (.mem (at0 .rbx)), .alu .or .rax (.imm 1),
    .alu .sub .rax (.mem (at0 .r10)), cfToRbp],
  wordLoop 1 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp],
  .block [.alu .and .r15 (.reg .rbp), .store (hdr kU) .r15, .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1))),
    .mov .rax (.reg .r15), .alu .and .rax (.imm 2), .alu .or .rax (.mem (at0 .rbx)), .store (at0 .rbx) .rax,
    .movImm64 .rax (BitVec.ofNat 64 (2 ^ 63)), .alu .and .rax (.reg .r15),
        .alu .xor .rax (.imm (BitVec.ofInt 32 (-1))),
    .alu .and .rax (.mem (ix .rbx .r12 (-8))), .store (ix .rbx .r12 (-8)) .rax]]

/-- The table's start: the bases, read from the header before anything is
stored (`aXm` in `r8`, `aB` in `r9`, `aY` in `r10`, `aR1` in `r11`, `aT0` in
`r13`), the base of entry 2 into `kV` and the count 14 into `kBits`; then
`T_1 := b R mod c` (from `aXm`), `y := T_1` and `T_0 := R mod c`. -/
def tabHead : List (Prog isa) := [
  .block (([.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aXm))), .mov .r10 (.mem (hdr (sArr aY)))] :
    List Instr) ++ extBase aB .r9 ++ extBase aR1 .r11 ++ extBase aT0 .r13 ++ extBase (aT0 + 2) .rcx ++
    ([.store (hdr kV) .rcx, .mov32 .rax (.imm 14), .store (hdr kBits) .rax] : List Instr)),
  seqs [.block [.mov .rsi (.reg .r8), .mov .rbx (.reg .r9)], copyWords],
  seqs [.block [.mov .rsi (.reg .r8), .mov .rbx (.reg .r10)], copyWords],
  seqs [.block [.mov .rsi (.reg .r11), .mov .rbx (.reg .r13)], copyWords]]

/-- The table, from `b R mod c` in `aXm`: `tabHead`, then `y := y T_1` into
each entry from 2 to 15 (the entry's base in `kV`, the count in `kBits`);
then `y := 1`. -/
def tabBuild (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  seqs tabHead,
  .loop (seqs [mul aY aY aXm,
    .block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aY))), .mov .rbx (.mem (hdr kV))], copyWords,
    .block [.mov .rax (.mem (hdr kV)), .mov .rdx (.mem (hdr sW)), .alu .add .rdx (.imm 2), .alu .add .rdx (.reg .rdx),
      .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rax (.reg .rdx), .store (hdr kV) .rax,
      .mov .rax (.mem (hdr kBits)), .alu .sub .rax (.imm 1), .store (hdr kBits) .rax]]) .ne,
  .block (([.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aY)))] : List Instr) ++ extBase aR1 .rsi), copyWords]

/-- One witness: its Montgomery form into `aXm`, the table, `y := 1`, the
flag; `kStat := 3` if it is clear; otherwise the witness counts, and
`kStat := 4` to go on (fewer than 16 witnesses, or fewer uniform ones than
needed) or 1. -/
def mrRound (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  mrWitness ++ [mul aXm aX aR2] ++ tabBuild mul ++
  mrExpLoop mul ++ ([
  .block [.mov32 .rcx (.imm 3), .mov .rax (.mem (hdr kFlag)), .alu .test .rax (.reg .rax)],
  .ite .e (.block [])
    (.block [.mov .rax (.mem (hdr kI)), .alu .add .rax (.imm 1), .store (hdr kI) .rax,
      .mov .rdx (.mem (hdr kU)), .alu .and .rdx (.imm 1), .alu .add .rdx (.mem (hdr kUni)), .store (hdr kUni) .rdx,
      -- `rcx := 4` if `i ≤ 16` or `uniform < checks`, else 1.
      .alu .cmp .rax (.imm 17), .alu .sbb .rcx (.reg .rcx), .alu .cmp .rdx (.mem (hdr kChecks)),
      .alu .sbb .rax (.reg .rax), .alu .or .rcx (.reg .rax), .alu .and .rcx (.imm 3), .alu .add .rcx (.imm 1)]),
  .block [.store (hdr kStat) .rcx]] : List (Prog isa))

/-- Miller–Rabin: witnesses while `kStat = 4`; 0 when fewer than `out_len`
octets of `rand` are left (`rand_len − used`, which does not wrap). -/
def millerRabin (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  .block [.mov32 .rax (.imm 1), .store (hdr kI) .rax, .mov32 .rax (.imm 0), .store (hdr kUni) .rax],
  .loop (seqs [
    .block [.mov .rcx (.mem (hdr kRandLen)), .mov .rax (.mem (hdr kUsed)), .alu .sub .rcx (.reg .rax),
      .mov .rax (.mem (hdr kLen)), .alu .cmp .rcx (.reg .rax)],
    .ite .b (.block [.mov32 .rax (.imm 0), .store (hdr kStat) .rax]) (seqs (mrRound mul)),
    .block [.mov .rax (.mem (hdr kStat)), .alu .cmp .rax (.imm 4)]]) .e]

/-! ## `vg_rsa_keygen_candidate` -/

/-- The result of Miller–Rabin, from `kStat`. -/
def mrResult : Prog isa :=
  .seq (.block [.mov .rax (.mem (hdr kStat)), .alu .test .rax (.reg .rax)])
    (.ite .e finNone (.seq (.block [.alu .cmp .rax (.imm 1)]) (.ite .e finPrime (finUsed 3))))

/-- Once `rand` has the candidate's octets. -/
def kMain (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  seqs (loadC ++ closeCheck ++ ([.ite .ne (finUsed 2) (seqs (trial ++
    ([.ite .ne (finUsed 3) (seqs (gcdCheck ++
      ([.ite .ne (finUsed 3) (seqs (montSetup mul ++ expSetup ++ millerRabin mul ++
        [mrResult]))] : List (Prog isa))))] : List (Prog isa))))] : List (Prog isa)))

/-- `vg_rsa_keygen_candidate`. -/
def code (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  seqs [.block kEntry, zeroOut,
    .block [.mov .rax (.mem (hdr kRandLen)), .mov .rcx (.mem (hdr kLen)), .alu .cmp .rax (.reg .rcx)],
    .ite .b finNone (kMain mul)]

end VG.Impl.RsaKeyGen.X86_64.Candidate
