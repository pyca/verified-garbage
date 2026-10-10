import VerifiedGarbage.Impl.Rsa.AArch64.Keys
import VerifiedGarbage.Impl.RsaKeyGen.Primes

/-!
# A candidate for a prime of an RSA key on AArch64

`vg_rsa_keygen_candidate(out, out_len, used, e, e_len, p, p_len, rand,
rand_len, scratch, scratch_len)`: the first eight arguments in `x0`–`x7`,
the others on the stack. x86-64's computation
(`Impl/RsaKeyGen/X86_64/Candidate.lean`) in the layout of the RSA key
routines (`Impl/Rsa/AArch64/Keys.lean`): a header of 32 words, then arrays
of `w + 2` words for `w = out_len / 8`, array `j` at
`256 + 8 (w + 2) j`, its base computed from `x0` and the stride. Besides
`vg_rsa_public`'s eight arrays: `b R mod c` (`aB`), `R mod c` (`aR1`),
`c − R mod c` (`aRm1`), then the table of small primes (`aTab`, 256 words).
The candidate `c` is in `aN`, where Montgomery multiplication `mul` (the
baseline `mm`, or one for other CPU features) takes its modulus.

1. `out` is zeroed; if `rand` is shorter than `out_len`, the result is 0.
2. `c`: the first `out_len` octets of `rand`, its two top bits and its low
   bit set.
3. If `p` is given: `c − p` and `p − c` (subtractions), the one that does
   not borrow selected under the mask of the first's borrow, compared with
   `2^(8 out_len − 100)`; the result is 2 if it is not above.
4. Trial division by the primes 3 to 8161 (3 to 3671 for `w ≤ 16`), from
   the table of four 16-bit primes a word (`Impl/RsaKeyGen/Primes.lean`):
   for each prime `s`, `c 2^(−64 w) mod s` by Montgomery reduction of `c`'s
   32-bit halves, from the least significant
   (`acc := (acc + h) 2^(−32) mod s`, kept below `2 s`), with
   `−s⁻¹ mod 2^64` by Newton's iteration; `s` divides `c` iff `acc` is 0 or
   `s`. The masks of all primes are or'ed, and the result is 3 if one is
   set.
5. `gcd(c − 1, e)`: 3 if `e` is even; for `e = 1` nothing; otherwise
   `(c − 1) mod e` bit by bit, then 128 steps of a binary gcd on words with
   masks (`Proof/RsaKeyGen/Gcd.lean`); 3 unless it is 1.
6. `-c⁻¹`, `R² mod c` as `vg_rsa_public_precompute` computes it (`r2Steps`),
   `R mod c` (`aR1`) and `c − R mod c` (`aRm1`): 1 and `−1` in Montgomery
   form; and the number of uniform witnesses needed.
7. Miller–Rabin, one witness an iteration: 0 if `rand` has fewer than
   `out_len` octets left; else the witness `x`, the next `out_len` octets,
   uniform if `2 ≤ x < c − 1`, otherwise bit 1 set and the top bit cleared;
   its Montgomery form (`aB`); then over the bits of `c − 1` from the top
   down to bit 1 (bit 0 is not needed), `y := y² b^bit` (the factor
   selected between `aB` and `aR1` under the bit's mask) and the flag of
   `Proof/RsaKeyGen/MillerRabin.lean`: at a set bit `y = ±1`, at a clear
   one the flag or `y = −1`. A clear flag ends with 3; otherwise the witness
   counts, and the loop goes on while fewer than 16 witnesses or fewer than
   `BN_prime_checks_for_size` uniform ones have passed; then the result is
   1 and `c` is written to `out`.

`used` is written at the end: the octets read (`out_len` per number), or 0
for the result 0.

Every branch is a `cbz`/`cbnz` on a register, and every flag a comparison's
carry made a mask or a value by `csel`. The code branches only on what the
leak allows: the lengths, `e`, the result of each check, and whether each
witness passed. No callee-saved register is written.
-/

namespace VG.Impl.RsaKeyGen.AArch64.Candidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen

/-! ## Header slots

`out_len` is in `vg_rsa_public`'s `sK`, from which `Keys.head` computes
`w`; `Keys.head` also sets the stride (`sStride`) and the mask `sMask` all
ones, which `finPrime` stores `c` under; `r2Steps` counts its doublings in
`sCnt`, which is otherwise a temporary (`kT0`). -/

def kOut : Nat := sFn 0
def kUsedP : Nat := sFn 1
def kLen : Nat := sK
def kE : Nat := sFn 3
def kElen : Nat := sFn 4
def kP : Nat := sFn 5
def kPlen : Nat := sFn 7
def kRand : Nat := sFn 8
def kRandLen : Nat := sFn 9
/-- The octets of `rand` read so far. -/
def kUsed : Nat := sFn 11
/-- Temporaries. -/
def kT0 : Nat := sCnt
def kT1 : Nat := sFn 13
def kT2 : Nat := sFn 14
/-- Miller–Rabin's state: what became of the last witness. -/
def kStat : Nat := sFn 15
/-- The mask of the witness being uniform (header slot 0, which no register
is saved in). -/
def kU : Nat := 0
/-- `gcd(c − 1, e)`, and Miller–Rabin's mask of `y = −1` (slot 1). -/
def kG : Nat := 1

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
`c − R mod c` (`aRm1`), then the table (`aTab`, 256 words). `aX` holds `p`,
then `c − 1`, then the witness. -/

def aB : Nat := 8
def aR1 : Nat := 9
def aRm1 : Nat := 10
def aTab : Nat := 11

/-! ## Entry and exit -/

/-- The arguments in the header at `scratch` (the second stack argument),
whose base goes in `x0`. -/
def kEntry : List Instr :=
  [.ldrSp .x8 8, .str .x .x0 .x8 (8 * kOut), .str .x .x1 .x8 (8 * kLen), .str .x .x2 .x8 (8 * kUsedP),
    .str .x .x3 .x8 (8 * kE), .str .x .x4 .x8 (8 * kElen), .str .x .x5 .x8 (8 * kP), .str .x .x6 .x8 (8 * kPlen),
    .str .x .x7 .x8 (8 * kRand), .ldrSp .x9 0, .str .x .x9 .x8 (8 * kRandLen), mov .x0 .x8]

/-- `x3` to `used`, and the status `r` returned. -/
def finish (r : Nat) : List Instr := [ldh .x2 kUsedP, st .x3 .x2, movi .x0 r]

/-- Status 0: `used` is 0. -/
def finNone : Prog isa := .block ([movi .x3 0] ++ finish 0)

/-- Status `r` (2 or 3): `used` is the octets read. -/
def finUsed (r : Nat) : Prog isa := .block ([ldh .x3 kUsed] ++ finish r)

/-- Status 1: `used` the octets read, and `c` to `out` under the mask
`sMask`, all ones. -/
def finPrime : Prog isa :=
  seqs (([.block [ldh .x3 kUsed, ldh .x2 kUsedP, st .x3 .x2]] : List (Prog isa)) ++ storeA aN kOut kLen sMask ++
    ([.block [movi .x0 1]] : List (Prog isa)))

/-- `x5 := 1` if `[x3] − [x4]` does not borrow, else 0 (`x7 := 0`). -/
def geFlag : List Instr := [.subs .x .x3 .x3 .x4, movi .x7 0, movi .x4 1, .csel .x .x5 .x4 .x7]

/-! ## The candidate -/

/-- `w := out_len / 8`, the arrays' bases, the stride and the mask; `c` from
the first `out_len` octets of `rand` with its two top bits and its low bit
set; and `used := out_len`. -/
def loadC : List (Prog isa) :=
  ([.block Keys.head] : List (Prog isa)) ++ loadA aN kRand kLen ++
  ([.block (ws ++ base aN .x16 ++ [ld .x3 .x16, movi .x4 1, .logic .orr .x .x3 .x3 .x4, st .x3 .x16,
    .lsl .x .x5 .x12 3, .add .x .x5 .x16 .x5, .subImm .x .x5 .x5 8, ld .x3 .x5, .movz .x .x4 0xC000 3,
    .logic .orr .x .x3 .x3 .x4, st .x3 .x5, ldh .x3 kLen, sth .x3 kUsed])] : List (Prog isa))

/-! ## Too close to `p` -/

/-- `[o] := [a] − [b]` over `w` words, the carry flag clear on a borrow:
`subMBody` under the mask all ones. -/
def subA (o a b : Nat) : List (Prog isa) := [
  .block (ws ++ [movi .x7 0, .subImm .x .x15 .x7 1, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++ base a .x16 ++
    base b .x17 ++ base o .x8),
  countLoop .x14 subMBody]

/-- `x15` the mask of `|c − p| ≤ 2^(64 w − 100)`, or 0 without `p`: `c − p`
into `aAcc` and `p − c` into `aTmp`, the latter selected into `aAcc` under
the mask of the former's borrow (kept in `kT0`); the bound in `aY` (word
`w − 2` is `2^28`), then the mask of `bound < |c − p|`'s complement. -/
def closeCheck : List (Prog isa) :=
  [.block [ldh .x3 kPlen, movi .x15 0],
   .ite (.zero .x .x3) (.block []) (seqs (loadA aX kP kPlen ++ subA aAcc aN aX ++
      ([.block (borrowMask ++ [sth .x15 kT0])] : List (Prog isa)) ++ subA aTmp aX aN ++ ([
      .block (ws ++ [ldh .x15 kT0, mov .x14 .x12] ++ base aTmp .x16 ++ base aAcc .x17),
      Crt.selLoop,
      .block [ldh .x12 sW, .movz .x .x9 0x1000 1, .subImm .x .x13 .x12 2],
      setWord aY,
      .block (ws ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++ base aY .x16 ++ base aAcc .x17),
      cmpLoop,
      .block carryMask] : List (Prog isa))))]

/-! ## Trial division -/

/-- `acc := (acc + h) 2^(−32) mod s` (below `2 s`) for the 32-bit `h` in
`x4`, `acc` in `x2`, `s` in `x13` and `−s⁻¹ mod 2^64` in `x15`: Montgomery
reduction of `x = acc + h < s 2^32`, with `q = x (−s⁻¹) mod 2^32` by a
32-bit multiplication. -/
def redc32 : List Instr :=
  [.add .x .x4 .x4 .x2, .mul .w .x6 .x4 .x15, .mul .x .x6 .x6 .x13, .add .x .x6 .x6 .x4, .lsr .x .x2 .x6 32]

/-- For entry `j` of the table word in `x17`: `s` into `x3` and `x13`,
`−s⁻¹` into `x15`, `acc` over `c`'s halves, and the mask of `acc ∈ {0, s}`
or'ed into `x1` (`x7 = 0`, `x8` all ones). -/
def trialEntry (j : Nat) : List (Prog isa) := [
  .block ((if j = 0 then [mov .x3 .x17] else [.lsr .x .x3 .x17 (16 * j)]) ++
    ([.movz .x .x4 0xFFFF 0, .logic .and .x .x3 .x3 .x4] : List Instr) ++ minv ++ [mov .x13 .x3] ++ ws ++
      base aN .x16 ++
    [mov .x14 .x12, movi .x2 0]),
  countLoop .x14 ([ld .x5 .x16, .addImm .w .x4 .x5 0] ++ redc32 ++ ([.lsr .x .x4 .x5 32] : List Instr) ++ redc32 ++
    [next .x16]),
  .block [movi .x4 1, .subs .x .x3 .x2 .x4, .csel .x .x5 .x7 .x8, .logic .eor .x .x3 .x2 .x13,
    .subs .x .x3 .x3 .x4, .csel .x .x6 .x7 .x8, .logic .orr .x .x5 .x5 .x6, .logic .orr .x .x1 .x1 .x5]]

/-- Store word `i` of the table at `[x9 + 8 i]`. -/
def tabStore (i : Nat) : List Instr :=
  [.movz .x .x3 (BitVec.ofNat 16 (tabWord i)) 0, .movk .x .x3 (BitVec.ofNat 16 (tabWord i / 2 ^ 16)) 1,
    .movk .x .x3 (BitVec.ofNat 16 (tabWord i / 2 ^ 32)) 2, .movk .x .x3 (BitVec.ofNat 16 (tabWord i / 2 ^ 48)) 3,
    st .x3 .x9 (8 * i)]

/-- The table, at `x9`. -/
def tabWrite : List Instr := (List.range 256).flatMap tabStore

/-- The table at `aTab`, then for each of its first `128` words (`256` for
`w > 16`, counted in `x10`, read through `x9`) its four entries; `x1` not
zero if one divides `c`. -/
def trial : List (Prog isa) := [
  .block (ws ++ base aTab .x9 ++ tabWrite ++
    [movi .x3 128, movi .x4 256, movi .x5 17, .subs .x .x6 .x12 .x5, .csel .x .x10 .x4 .x3, movi .x1 0,
      movi .x7 0, .subImm .x .x8 .x7 1]),
  .loop (seqs (([.block [ld .x17 .x9, next .x9]] : List (Prog isa)) ++ trialEntry 0 ++ trialEntry 1 ++ trialEntry 2 ++
      trialEntry 3 ++ ([.block [.subImm .x .x10 .x10 1]] : List (Prog isa)))) (.nonzero .x .x10)]

/-! ## `gcd(c − 1, e)` -/

/-- `e` (`e_len` octets, most significant first) into `x3`. -/
def loadE : List (Prog isa) := [
  .block [ldh .x1 kE, ldh .x2 kElen, movi .x3 0],
  countLoop .x2 [.lsl .x .x3 .x3 8, .ldrb .x4 .x1 0, .add .x .x3 .x3 .x4, .addImm .x .x1 .x1 1]]

/-- One bit of `(c − 1) mod e`: the top bit of `x2` shifted out into
`r = x3` (`r := 2 r + bit`, its carry into `x4`), then `r − e` (`x13`) kept
if that carried or did not borrow (`x7 = 0`, `x8` all ones). -/
def modBit : List Instr :=
  [.adds .x .x2 .x2 .x2, .adcs .x .x3 .x3 .x3, .adc .x .x4 .x7 .x7, .subs .x .x5 .x3 .x13, .csel .x .x6 .x8 .x7,
    .sub .x .x4 .x7 .x4, .logic .orr .x .x6 .x6 .x4, .logic .eor .x .x5 .x5 .x3, .logic .and .x .x5 .x5 .x6,
    .logic .eor .x .x3 .x3 .x5]

/-- `x3 := (c − 1) mod e` for `e` in `kG`: `c` copied to `aX`, its low bit
cleared, then its words from the top (`x10` walking down, `x14` counting),
64 bits each (`x9` counting). -/
def modLoop : List (Prog isa) := [
  copyA aX aN,
  .block (ws ++ base aX .x16 ++ [ld .x3 .x16, movi .x4 1, .logic .eor .x .x3 .x3 .x4, st .x3 .x16,
    .lsl .x .x5 .x12 3, .add .x .x10 .x16 .x5, mov .x14 .x12, ldh .x13 kG, movi .x3 0, movi .x7 0,
    .subImm .x .x8 .x7 1]),
  .loop (seqs [.block [.subImm .x .x10 .x10 8, ld .x2 .x10, movi .x9 64], countLoop .x9 modBit,
    .block [.subImm .x .x14 .x14 1]]) (.nonzero .x .x14)]

/-- One step of the binary gcd on `u = x3` and the odd `v = x13`
(`x7 = 0`, `x8` all ones): if `u` is odd, `(|u − v|, min u v)`; then
`u / 2`. -/
def bgcdStep : List Instr :=
  [movi .x4 1, .logic .and .x .x4 .x3 .x4, .sub .x .x4 .x7 .x4,
    .subs .x .x5 .x3 .x13, .csel .x .x6 .x7 .x8, .logic .eor .x .x5 .x5 .x6, .sub .x .x5 .x5 .x6,
    .logic .eor .x .x10 .x3 .x13, .logic .and .x .x10 .x10 .x6, .logic .eor .x .x10 .x10 .x13,
    .logic .eor .x .x5 .x5 .x3, .logic .and .x .x5 .x5 .x4, .logic .eor .x .x3 .x3 .x5,
    .logic .eor .x .x10 .x10 .x13, .logic .and .x .x10 .x10 .x4, .logic .eor .x .x13 .x13 .x10,
    .lsr .x .x3 .x3 1]

/-- `kG := gcd(c − 1, e)` for the odd `e > 1` in `kG`: `(c − 1) mod e`, then
128 steps. -/
def gcdE : List (Prog isa) :=
  modLoop ++ ([.block [movi .x9 128], countLoop .x9 bgcdStep, .block [sth .x13 kG]] : List (Prog isa))

/-- `gcd(c − 1, e)` into `kG`, or `e` for an even `e`; then `x3 = 0` iff it
is 1. -/
def gcdCheck : List (Prog isa) :=
  loadE ++ ([
  .block [sth .x3 kG, movi .x4 1, .logic .and .x .x5 .x3 .x4],
  .ite (.zero .x .x5) (.block [])
    (.seq (.block [.subImm .x .x5 .x3 1]) (.ite (.zero .x .x5) (.block []) (seqs gcdE))),
  .block [ldh .x3 kG, .subImm .x .x3 .x3 1]] : List (Prog isa))

/-! ## Montgomery arithmetic modulo `c` -/

/-- `x5 := v` if `w ≥ k`. -/
def checksIf (k v : Nat) : List Instr := [movi .x4 k, .subs .x .x3 .x12 .x4, movi .x6 v, .csel .x .x5 .x6 .x5]

/-- `-c⁻¹`, the number 1, `R² mod c`, `R mod c` into `aR1` and `c − R mod c`
into `aRm1`, and the number of uniform witnesses needed (`checksW w`). -/
def montSetup (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  ([.block ([ldh .x8 (sArr aN), ld .x3 .x8] ++ minv ++ [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0]),
    setWord aOne] : List (Prog isa)) ++
  r2Steps mul ++
  [mul aY aR2 aOne, copyA aR1 aY] ++ subA aRm1 aN aR1 ++
  ([.block ([ldh .x12 sW, movi .x5 27] ++ checksIf 5 8 ++ checksIf 6 7 ++ checksIf 7 6 ++ checksIf 8 5 ++
    checksIf 22 4 ++ checksIf 59 3 ++ [sth .x5 kChecks])] : List (Prog isa))

/-! ## Miller–Rabin -/

/-- `x15 :=` the mask of `[aY] = [j]`. -/
def eqMask (j : Nat) : List (Prog isa) :=
  eqA aY j ++ ([.block ([movi .x7 0, movi .x4 1, .subs .x .x3 .x9 .x4] ++ borrowMask)] : List (Prog isa))

/-- `x15 := ` the mask of the top bit of `kV` (`x7 := 0`). -/
def bitMask : List Instr := [ldh .x3 kV, .lsr .x .x3 .x3 63, movi .x7 0, .sub .x .x15 .x7 .x3]

/-- One bit of `c`, at the top of `kV`: `y := y²`; `[aXm] := bit ? [aB] : [aR1]`;
`y := y [aXm]`; the flag `P := bit ? (y = 1 ∨ y = −1) : (P ∨ y = −1)`; then
`kV := 2 kV` and `x3 := kBits := kBits − 1`. -/
def mrExpBit (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  mul aY aY aY,
  copyA aXm aR1,
  .block (bitMask ++ ws ++ base aB .x16 ++ base aXm .x17 ++ [mov .x14 .x12]),
  Crt.selLoop,
  mul aY aY aXm] ++
  eqMask aRm1 ++ ([.block [sth .x15 kG]] : List (Prog isa)) ++ eqMask aR1 ++ ([
  .block [mov .x9 .x15, ldh .x3 kV, .lsr .x .x3 .x3 63, movi .x7 0, .sub .x .x6 .x7 .x3, ldh .x5 kG,
    .logic .orr .x .x9 .x9 .x5, .logic .and .x .x9 .x9 .x6, ldh .x4 kFlag, .logic .orr .x .x4 .x4 .x5,
    .subImm .x .x8 .x7 1, .logic .eor .x .x6 .x6 .x8, .logic .and .x .x4 .x4 .x6, .logic .orr .x .x4 .x4 .x9,
    sth .x4 kFlag, ldh .x3 kV, .lsl .x .x3 .x3 1, sth .x3 kV, ldh .x3 kBits, .subImm .x .x3 .x3 1,
        sth .x3 kBits]] : List (Prog isa))

/-- The flag over the bits of `c` from the top down to bit 1: its words from
the top, 64 bits each but 63 of the last. -/
def mrExpLoop (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  .block [ldh .x3 sW, sth .x3 kWords, movi .x3 0, sth .x3 kFlag],
  .loop (seqs [
    .block [ldh .x3 kWords, .subImm .x .x3 .x3 1, sth .x3 kWords, ldh .x4 (sArr aN), .lsl .x .x5 .x3 3,
      .add .x .x4 .x4 .x5, ld .x5 .x4, sth .x5 kV, movi .x6 64, movi .x7 63, movi .x4 1, .subs .x .x8 .x3 .x4,
      .csel .x .x6 .x6 .x7, sth .x6 kBits],
    .loop (seqs (mrExpBit mul)) (.nonzero .x .x3),
    .block [ldh .x3 kWords]]) (.nonzero .x .x3)]

/-- The witness in `aX` from the next `out_len` octets of `rand`, `used`
advanced; the mask of `2 ≤ x < c − 1` (`x ≥ 2` and `(x | 1) < c`) into
`kU`; if it is clear, bit 1 set and the top bit cleared. -/
def mrWitness : List (Prog isa) := [
  zeroA aX,
  .block (ws ++ base aX .x8 ++ [ldh .x1 kRand, ldh .x3 kUsed, .add .x .x1 .x1 .x3, ldh .x2 kLen,
    .add .x .x3 .x3 .x2, sth .x3 kUsed]),
  loadBE,
  -- `x5 := (x_0 >> 1) | x_1 | … | x_(w−1)`, zero iff `x < 2`.
  .block (ws ++ base aX .x16 ++ [ld .x5 .x16, .lsr .x .x5 .x5 1, next .x16, .subImm .x .x14 .x12 1]),
  countLoop .x14 [ld .x3 .x16, .logic .orr .x .x5 .x5 .x3, next .x16],
  -- `x9 := ` the mask of `x ≥ 2`; the carry of `(x | 1) − c`.
  .block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4, .csel .x .x9 .x8 .x7] ++ ws ++
    base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4, ld .x4 .x17, .subs .x .x3 .x3 .x4,
    next .x16, next .x17, .subImm .x .x14 .x12 1]),
  cmpLoop,
  .block (([.csel .x .x15 .x7 .x8, .logic .and .x .x9 .x9 .x15, sth .x9 kU,
      .logic .eor .x .x9 .x9 .x8] : List Instr) ++
    base aX .x16 ++ [movi .x4 2, .logic .and .x .x4 .x4 .x9, ld .x3 .x16, .logic .orr .x .x3 .x3 .x4, st .x3 .x16,
    .lsl .x .x5 .x12 3, .add .x .x16 .x16 .x5, .subImm .x .x16 .x16 8, .movz .x .x4 0x8000 3,
    .logic .and .x .x4 .x4 .x9, .logic .eor .x .x4 .x4 .x8, ld .x3 .x16, .logic .and .x .x3 .x3 .x4, st .x3 .x16])]

/-- One witness: its Montgomery form into `aXm` and `aB`, `y := 1`, the flag;
`kStat := 3` if it is clear; otherwise the witness counts, and `kStat := 4`
to go on (fewer than 16 witnesses, or fewer uniform ones than needed) or 1. -/
def mrRound (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  mrWitness ++ [mul aXm aX aR2, copyA aB aXm, copyA aY aR1] ++ mrExpLoop mul ++ ([
  .block [ldh .x3 kFlag],
  .ite (.zero .x .x3) (.block [movi .x3 3, sth .x3 kStat])
    (.block [ldh .x3 kI, .addImm .x .x3 .x3 1, sth .x3 kI, ldh .x4 kU, movi .x5 1, .logic .and .x .x4 .x4 .x5,
      ldh .x5 kUni, .add .x .x4 .x4 .x5, sth .x4 kUni,
      -- `x13 := 4` if `i ≤ 16` or `uniform < checks`, else 1.
      movi .x9 4, movi .x10 1, movi .x5 17, .subs .x .x6 .x3 .x5, .csel .x .x13 .x10 .x9, ldh .x5 kChecks,
      .subs .x .x6 .x4 .x5, .csel .x .x13 .x13 .x9, sth .x13 kStat])] : List (Prog isa))

/-- Miller–Rabin: witnesses while `kStat = 4`; 0 when fewer than `out_len`
octets of `rand` are left (`rand_len − used`, which does not wrap). -/
def millerRabin (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  .block [movi .x3 1, sth .x3 kI, movi .x3 0, sth .x3 kUni],
  .loop (seqs [
    .block ([ldh .x3 kRandLen, ldh .x4 kUsed, .sub .x .x3 .x3 .x4, ldh .x4 kLen] ++ geFlag),
    .ite (.zero .x .x5) (.block [movi .x3 0, sth .x3 kStat]) (seqs (mrRound mul)),
    .block [ldh .x3 kStat, .subImm .x .x3 .x3 4]]) (.zero .x .x3)]

/-! ## `vg_rsa_keygen_candidate` -/

/-- The result of Miller–Rabin, from `kStat`. -/
def mrResult : Prog isa :=
  .seq (.block [ldh .x3 kStat])
    (.ite (.zero .x .x3) finNone (.seq (.block [.subImm .x .x3 .x3 1]) (.ite (.zero .x .x3) finPrime (finUsed 3))))

/-- Once `rand` has the candidate's octets. -/
def kMain (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  seqs (loadC ++ closeCheck ++ ([.ite (.nonzero .x .x15) (finUsed 2) (seqs (trial ++
    ([.ite (.nonzero .x .x1) (finUsed 3) (seqs (gcdCheck ++
      ([.ite (.nonzero .x .x3) (finUsed 3) (seqs (montSetup mul ++ millerRabin mul ++
        [mrResult]))] : List (Prog isa))))] : List (Prog isa))))] : List (Prog isa)))

/-- `vg_rsa_keygen_candidate`. -/
def code (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  seqs [.block kEntry, zeroOut kOut kLen, .block ([ldh .x3 kRandLen, ldh .x4 kLen] ++ geFlag),
    .ite (.zero .x .x5) finNone (kMain mul)]

end VG.Impl.RsaKeyGen.AArch64.Candidate
