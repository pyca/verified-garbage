import VerifiedGarbage.Impl.Rsa.X86_64
import VerifiedGarbage.Impl.RsaKeyGen.Primes

/-!
# A candidate for a prime of an RSA key on x86-64

`vg_rsa_keygen_candidate(out, out_len, used, e, e_len, p, p_len, rand,
rand_len, scratch, scratch_len)`: the first six arguments in registers, the
others on the stack. The working space is a header and arrays as
`vg_rsa_public`'s (`Impl/Bignum/X86_64.lean`), for `w = out_len / 8` words,
with three more arrays after the eight (`aB`, `aR1`, `aRm1`) and then the
table of small primes (256 words). The candidate `c` is in `aN`, where
Montgomery multiplication `mul` (the baseline `mm`, or one for other CPU
features) takes its modulus.

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
   Montgomery form.
7. Miller–Rabin, one witness an iteration: 0 if `rand` has fewer than
   `out_len` octets left; else the witness `x`, the next `out_len` octets,
   uniform if `2 ≤ x < c − 1`, otherwise bit 1 set and the top bit cleared;
   its Montgomery form (`aB`); then over the bits of `c − 1` from the top
   down to bit 1 (bit 0 is not needed), `y := y² b^bit` (the factor chosen
   between `aB` and `aR1` by the bit's mask) and the flag of
   `Proof/RsaKeyGen/MillerRabin.lean`: at a set bit `y = ±1`, at a clear one
   the flag or `y = −1`. A clear flag ends with 3; otherwise the witness
   counts, and the loop goes on while fewer than 16 witnesses or fewer than
   `BN_prime_checks_for_size` uniform ones have passed; then the result is
   1 and `c` is written to `out`.

`used` is written at the end: the octets read (`out_len` per number), or 0
for the result 0.

Header words that address memory or decide a branch are loaded into a
register before they are compared or added, and before anything secret is
stored into the arrays, so the taint analysis knows them public.
-/

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

Besides `vg_rsa_public`'s eight: `b R mod c` (`aB`), `R mod c` (`aR1`),
`c − R mod c` (`aRm1`), then the table (`aTab`). `aX` holds `p`, then
`c − 1`, then the witness. -/

def aB : Nat := 8
def aR1 : Nat := 9
def aRm1 : Nat := 10
def aTab : Nat := 11

/-- The base of array `j ≥ 7` into `r`: array 7's plus `j − 7` arrays of
`8 (w + 2)` bytes. Clobbers `rax`. -/
def extBase (j : Nat) (r : Reg) : List Instr :=
  [.mov .rax (.mem (hdr sW)), .alu .add .rax (.imm 2), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .mov r (.mem (hdr (sArr aOne)))] ++ List.replicate (j - 7) (.alu .add r (.reg .rax))

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
  [.mov .r11 (.mem (kStk 4))] ++
  (saved.zipIdx.map fun (r, i) => .store { base := .r11, disp := 8 * i } r) ++
  [.store { base := .r11, disp := 8 * kOut } .rdi, .store { base := .r11, disp := 8 * kLen } .rsi,
    .store { base := .r11, disp := 8 * kUsedP } .rdx, .store { base := .r11, disp := 8 * kE } .rcx,
    .store { base := .r11, disp := 8 * kElen } .r8, .store { base := .r11, disp := 8 * kP } .r9,
    .mov .rax (.mem (kStk 1)), .store { base := .r11, disp := 8 * kPlen } .rax,
    .mov .rax (.mem (kStk 2)), .store { base := .r11, disp := 8 * kRand } .rax,
    .mov .rax (.mem (kStk 3)), .store { base := .r11, disp := 8 * kRandLen } .rax, .mov .rdi (.reg .r11)]

/-- Zeros to the `out_len` bytes of `out`. -/
def zeroOut : Prog isa :=
  .seq (.block [.mov .rsi (.mem (hdr kOut)), .mov .rcx (.mem (hdr kLen)), .mov32 .rax (.imm 0)])
    (.loop (.block [.store8 (at0 .rsi) .rax, .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) .ne)

/-- `rax` to `used`, the status `st` returned, the callee-saved registers
restored. -/
def finish (st : Nat) : List Instr :=
  [.mov .rdx (.mem (hdr kUsedP)), .store (at0 .rdx) .rax, .mov32 .rax (.imm (BitVec.ofNat 32 st))] ++ exit

/-- Status 0: `used` is 0. -/
def finNone : Prog isa := .block ([.mov32 .rax (.imm 0)] ++ finish 0)

/-- Status `st` (2 or 3): `used` is the octets read. -/
def finUsed (st : Nat) : Prog isa := .block ([.mov .rax (.mem (hdr kUsed))] ++ finish st)

/-- Status 1: `used` the octets read, and `c` to `out` (the bases and the
length loaded first, so that none is read from the header once memory
outside it has been written). -/
def finPrime : Prog isa :=
  .seq (.block [.mov .rbx (.mem (hdr (sArr aN))), .mov .rsi (.mem (hdr kOut)), .mov .rcx (.mem (hdr kLen)),
      .mov .r15 (.imm (BitVec.ofInt 32 (-1))), .mov .rax (.mem (hdr kUsed)), .mov .rdx (.mem (hdr kUsedP)),
      .store (at0 .rdx) .rax])
    (.seq storeBE (.block ([.mov32 .rax (.imm 1)] ++ exit)))

/-! ## The candidate -/

/-- `w := out_len / 8` (in `r12` and its slot), the arrays' bases, `c` from
the first `out_len` octets of `rand` with its two top bits and its low bit
set, and `used := out_len`. -/
def loadC : List (Prog isa) := [
  .block ([.mov .rcx (.mem (hdr kLen)), .mov .r12 (.reg .rcx), .shift .shr .r12 3, .store (hdr sW) .r12] ++
    setBases ++ [.mov .rsi (.mem (hdr kRand)), .mov .rbx (.mem (hdr (sArr aN)))]),
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
   .ite .ne (seqs ([
      .block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr kP)), .mov .rcx (.mem (hdr kLen)),
        .mov .rbx (.mem (hdr (sArr aX)))],
      loadBE] ++ diffLoop ++ negLoop ++ [
      .block [.mov .r12 (.mem (hdr sW)), .mov .rcx (.reg .r12), .alu .sub .rcx (.imm 2),
        .mov32 .rdx (.imm (BitVec.ofNat 32 (2 ^ 28)))],
      setWord aTmp .rcx,
      .block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aTmp))), .mov .r10 (.mem (hdr (sArr aAcc))),
        .mov32 .rbp (.imm 0)],
      wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp],
      .block [.alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))]]))
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
  .block ([.mov .rbx (.mem (hdr kT1))] ++ (if j = 0 then [] else [.shift .shr .rbx (16 * j)]) ++
    [.alu .and .rbx (.imm 0xFFFF)] ++ minv ++
    [.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aN))), .mov32 .rbp (.imm 0)]),
  wordLoop 0 ([.mov .rsi (.mem (ix .r8 .r14)), .mov32 .rax (.reg .rsi)] ++ redc32 ++
    [.mov .rax (.reg .rsi), .shift .shr .rax 32] ++ redc32),
  .block [.mov .rax (.reg .rbp), .alu .cmp .rax (.imm 1), .alu .sbb .rdx (.reg .rdx), .alu .xor .rax (.reg .rbx),
    .alu .cmp .rax (.imm 1), .alu .sbb .rcx (.reg .rcx), .alu .or .rdx (.reg .rcx), .alu .or .rdx (.mem (hdr kT2)),
    .store (hdr kT2) .rdx]]

/-- The table at `aTab`, then for each of its first `128` words (`256` for
`w > 16`, in `kT0`) its four entries; ZF clear if one divides `c`. -/
def trial : List (Prog isa) := [
  .block (extBase aTab .rbx ++ tabWrite ++
    [.mov32 .rax (.imm 128), .mov .rcx (.mem (hdr sW)), .alu .cmp .rcx (.imm 17)]),
  .ite .b (.block []) (.block [.mov32 .rax (.imm 256)]),
  .block [.store (hdr kT0) .rax, .mov32 .rax (.imm 0), .store (hdr kT2) .rax, .mov32 .r13 (.imm 0)],
  .loop (seqs ([.block (extBase aTab .rbx ++ [.mov .rax (.mem (ix .rbx .r13)), .store (hdr kT1) .rax])] ++
      trialEntry 0 ++ trialEntry 1 ++ trialEntry 2 ++ trialEntry 3 ++
      [.block [.alu .add .r13 (.imm 1), .mov .rax (.mem (hdr kT0)), .alu .cmp .r13 (.reg .rax)]])) .ne,
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
    (.loop (.block (modBit ++ [.alu .sub .r13 (.imm 1)])) .ne)

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
  [.block [.store (hdr kG) .rbx]] ++ modLoop ++
  [.block [.mov .rbx (.mem (hdr kG)), .mov32 .r13 (.imm 128)],
   .loop (.block (bgcdStep ++ [.alu .sub .r13 (.imm 1)])) .ne,
   .block [.store (hdr kG) .rbx]]

/-- `gcd(c − 1, e)` into `kG`, or an even number for an even `e`; then ZF
clear unless it is 1. -/
def gcdCheck : List (Prog isa) :=
  loadE ++ [
  .block [.store (hdr kG) .rbx, .mov .rax (.reg .rbx), .alu .and .rax (.imm 1)],
  .ite .e (.block [])
    (seqs [.block [.alu .cmp .rbx (.imm 1)], .ite .e (.block []) (seqs gcdE)]),
  .block [.mov .rax (.mem (hdr kG)), .alu .cmp .rax (.imm 1)]]

/-! ## Montgomery arithmetic modulo `c` -/

/-- `-c⁻¹`, the number 1, `R² mod c`, `R mod c` into `aR1` and `c − R mod c`
into `aRm1`, and the number of uniform witnesses needed. -/
def montSetup (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  .block ([.mov .r10 (.mem (hdr (sArr aN))), .mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (at0 .r10))] ++ minv ++
    [.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)]),
  setWord aOne .rcx,
  .block [.movImm64 .rdx (BitVec.ofNat 64 (2 ^ 63)), .mov .rcx (.reg .r12), .alu .sub .rcx (.imm 1)],
  setWord aR2 .rcx,
  .block [.mov .rcx (.mem (hdr sW)), .alu .add .rcx (.imm 1)],
  doubles aN aAcc aTmp aR2 kT0,
  mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2,
  mul aY aR2 aOne,
  .block ([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aY)))] ++ extBase aR1 .rbx),
  copyWords,
  .block ([.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aN)))] ++ extBase aR1 .r10 ++ extBase aRm1 .rsi ++
    [.mov32 .rbp (.imm 0)]),
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

/-! ## Miller–Rabin -/

/-- The mask of `[aY] = [j]` over `w` words into `rbp` (`j` an extra array,
its base into `r10`). -/
def eqMask (j : Nat) : List (Prog isa) := [
  .block ([.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aY)))] ++ extBase j .r10 ++ [.mov32 .rbp (.imm 0)]),
  wordLoop 0 [.mov .rax (.mem (ix .rbx .r14)), .alu .xor .rax (.mem (ix .r10 .r14)), .alu .or .rbp (.reg .rax)],
  .block [.alu .cmp .rbp (.imm 1), .alu .sbb .rbp (.reg .rbp)]]

/-- One bit of `c`, at the top of `kV`: `y := y²`; `[aXm] := bit ? [aB] : [aR1]`;
`y := y [aXm]`; the flag `P := bit ? (y = 1 ∨ y = −1) : (P ∨ y = −1)`; then
`kV := 2 kV` and `kBits := kBits − 1` (ZF set when it is 0). -/
def mrExpBit (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  mul aY aY aY,
  .block ([.mov .rax (.mem (hdr kV)), .shift .shr .rax 63, .mov32 .r15 (.imm 0), .alu .sub .r15 (.reg .rax),
    .mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aXm)))] ++ extBase aB .r8 ++ extBase aR1 .rsi),
  wordLoop 0 [.mov .rax (.mem (ix .r8 .r14)), .mov .rdx (.mem (ix .rsi .r14)), .alu .xor .rax (.reg .rdx),
    .alu .and .rax (.reg .r15), .alu .xor .rax (.reg .rdx), .store (ix .rbx .r14) .rax],
  mul aY aY aXm] ++
  eqMask aRm1 ++ [.block [.store (hdr kG) .rbp]] ++ eqMask aR1 ++ [
  .block [.mov .rax (.mem (hdr kV)), .shift .shr .rax 63, .mov32 .r15 (.imm 0), .alu .sub .r15 (.reg .rax),
    .mov .rdx (.mem (hdr kG)), .alu .or .rbp (.reg .rdx), .alu .and .rbp (.reg .r15),
    .mov .rax (.mem (hdr kFlag)), .alu .or .rax (.reg .rdx), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1))),
    .alu .and .rax (.reg .r15), .alu .or .rax (.reg .rbp), .store (hdr kFlag) .rax,
    .mov .rax (.mem (hdr kV)), .alu .add .rax (.reg .rax), .store (hdr kV) .rax,
    .mov .rax (.mem (hdr kBits)), .alu .sub .rax (.imm 1), .store (hdr kBits) .rax]]

/-- The flag over the bits of `c` from the top down to bit 1: its words from
the top, 64 bits each but 63 of the last. -/
def mrExpLoop (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  .block [.mov .rax (.mem (hdr sW)), .store (hdr kWords) .rax, .mov32 .rax (.imm 0), .store (hdr kFlag) .rax],
  .loop (seqs [
    .block [.mov .rax (.mem (hdr kWords)), .alu .sub .rax (.imm 1), .store (hdr kWords) .rax,
      .mov .rdx (.mem (hdr (sArr aN))), .mov .rcx (.mem (ix .rdx .rax)), .store (hdr kV) .rcx,
      .mov32 .rcx (.imm 64), .alu .cmp .rax (.imm 1), .alu .sbb .rcx (.imm 0), .store (hdr kBits) .rcx],
    .loop (seqs (mrExpBit mul)) .ne,
    .block [.mov .rax (.mem (hdr kWords)), .alu .test .rax (.reg .rax)]]) .ne]

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
    .movImm64 .rax (BitVec.ofNat 64 (2 ^ 63)), .alu .and .rax (.reg .r15), .alu .xor .rax (.imm (BitVec.ofInt 32 (-1))),
    .alu .and .rax (.mem (ix .rbx .r12 (-8))), .store (ix .rbx .r12 (-8)) .rax]]

/-- One witness: its Montgomery form into `aXm` and `aB`, `y := 1`, the flag;
`kStat := 3` if it is clear; otherwise the witness counts, and `kStat := 4`
to go on (fewer than 16 witnesses, or fewer uniform ones than needed) or 1. -/
def mrRound (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  mrWitness ++ [
  mul aXm aX aR2,
  .block ([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aXm)))] ++ extBase aB .rbx),
  copyWords,
  .block ([.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aY)))] ++ extBase aR1 .rsi),
  copyWords] ++
  mrExpLoop mul ++ [
  .block [.mov32 .rcx (.imm 3), .mov .rax (.mem (hdr kFlag)), .alu .test .rax (.reg .rax)],
  .ite .e (.block [])
    (.block [.mov .rax (.mem (hdr kI)), .alu .add .rax (.imm 1), .store (hdr kI) .rax,
      .mov .rdx (.mem (hdr kU)), .alu .and .rdx (.imm 1), .alu .add .rdx (.mem (hdr kUni)), .store (hdr kUni) .rdx,
      -- `rcx := 4` if `i ≤ 16` or `uniform < checks`, else 1.
      .alu .cmp .rax (.imm 17), .alu .sbb .rcx (.reg .rcx), .alu .cmp .rdx (.mem (hdr kChecks)),
      .alu .sbb .rax (.reg .rax), .alu .or .rcx (.reg .rax), .alu .and .rcx (.imm 3), .alu .add .rcx (.imm 1)]),
  .block [.store (hdr kStat) .rcx]]

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
  seqs (loadC ++ closeCheck ++ [.ite .ne (finUsed 2) (seqs (trial ++
    [.ite .ne (finUsed 3) (seqs (gcdCheck ++
      [.ite .ne (finUsed 3) (seqs (montSetup mul ++ millerRabin mul ++ [mrResult]))]))]))])

/-- `vg_rsa_keygen_candidate`. -/
def code (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  seqs [.block kEntry, zeroOut,
    .block [.mov .rax (.mem (hdr kRandLen)), .mov .rcx (.mem (hdr kLen)), .alu .cmp .rax (.reg .rcx)],
    .ite .b finNone (kMain mul)]

end VG.Impl.RsaKeyGen.X86_64.Candidate
