module

public import VerifiedGarbage.Impl.MlKem.AArch64.FixedHashCallers
public import VerifiedGarbage.Impl.Sha3.AArch64.Hybrid.X3
public import VerifiedGarbage.Impl.MlKem.AArch64.Paired

/-! # ML-KEM encapsulation hashing `ek` inside the paired matrix sampling

The hardware-SHA3 encapsulation computes `H(ek) = SHA3-256(ek)` in the third
state of `vg_keccak_f1600_x3_sha3`, while the paired SHAKE128 streams of the
matrix run in its vector state, instead of with separate permutations before
the matrix:

1. the prologue, `m` and `ρ`, and the all-zero third state at `ST` of
   `scratch` (`startH`);
2. the matrix (`matrixH`), whose first `hashPairs` pairs each make their
   three main squeezes with `x3` calls (`pair3`), each after XORing the next
   136-byte block of `ek` into the third state (`absorbBlock`; the last block
   is partial, and carries SHA3-256's padding `0x06 … 0x80`); the other pairs,
   the singleton and every additional squeeze keep `vg_keccak_f1600_x2_sha3`;
3. `H(ek)`, the first 32 bytes of the third state, into `HB`, and
   `G(m ‖ H(ek))` (`tailH`);
4. noise, `u`, `v` and the epilogue, as before.

Only the public lengths decide which blocks are absorbed when; the third
state's pointer is `scratch`'s.
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Hybrid
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM

/-- The number of 136-byte blocks of `pad(ek)`. -/
def blocks (L : KemLay) : Nat := L.ekLen / 136 + 1

/-- The pairs of the matrix whose main squeezes absorb `ek`: three blocks each. -/
def hashPairs (L : KemLay) : Nat := blocks L / 3

/-- XOR the `n` words of `ek` at `eo` into the first `n` lanes of the third state
(at `scratch + ST`, `ST = 0`). -/
def absorbWords (eo n : Nat) : List Instr :=
  (List.range n).flatMap fun w =>
    [.ldr .x .x9 .x25 (eo + 8 * w), .ldr .x .x10 .x28 (8 * w), .logic .eor .x .x9 .x9 .x10,
      .str .x .x9 .x28 (8 * w)]

/-- XOR the byte `value` into byte `off` of `scratch`. -/
def xorByte (off value : Nat) : List Instr :=
  [.ldrb .x9 .x28 off, .movz .x .x10 (BitVec.ofNat 16 value) 0, .logic .eor .x .x9 .x9 .x10, .strb .x9 .x28 off]

/-- Block `b` of `pad(ek)` (rate 136, SHA3's suffix `0x06`) into the third state. -/
def absorbBlock (L : KemLay) (b : Nat) : List Instr :=
  if 136 * b + 136 ≤ L.ekLen then absorbWords (136 * b) 17
  else absorbWords (136 * b) ((L.ekLen - 136 * b) / 8) ++
    xorByte (L.ekLen - 136 * b) 6 ++ xorByte 135 128

/-- `vg_keccak_f1600_x3_sha3` on the pair at `x19`, the third state at `scratch`
(`ST = 0`) and its working space at `x19 + 1536`, keeping `x30` after it. -/
def x3call : Prog isa :=
  .seq (.block [.addImm .x .x2 .x19 1536, .str .x .x30 .x2 128, .addImm .x .x0 .x19 0,
      .addImm .x .x1 .x28 0])
    (.seq (.call Impl.Sha3.AArch64.Hybrid.X3.name Impl.Sha3.AArch64.Hybrid.X3.code)
      (.block [.ldr .x .x30 .x19 1664]))

/-- The squeeze's tail: both states' first 21 words, and the next blocks. -/
def squeezeTail : List Instr :=
  Impl.Sha3.AArch64.Neon.X2.squeeze 21 .x19 .x20 .x21 ++ [.addImm .x .x20 .x20 168, .addImm .x .x21 .x21 168]

/-- One main squeeze absorbing block `b`. -/
def step3 (L : KemLay) (b : Nat) : Prog isa :=
  .seq (.block (absorbBlock L b)) (.seq x3call (.block squeezeTail))

/-- The three main squeezes of pair `i`, absorbing blocks `3i`, `3i + 1`, `3i + 2`. -/
def squeeze3 (L : KemLay) (i : Nat) : Prog isa :=
  .seq (step3 L (3 * i)) (.seq (step3 L (3 * i + 1)) (step3 L (3 * i + 2)))

/-- `Paired.pair` (encapsulation) with `squeeze3` for the three main squeezes. -/
def pair3 (L : KemLay) (a i : Nat) (w16 : Bool := false) : Prog isa :=
  seqs [.block (Paired.init SB SS a (a+1) L.k), squeeze3 L i, .block Rej8.rejConsts,
    Paired.reject 400 (AH+1024*a) .x22 w16,
    .block [.str .x .x3 .x19 1680,.str .x .x4 .x19 1688],
    Paired.reject 904 (AH+1024*(a+1)) .x23 w16,
    .block [.str .x .x3 .x19 1696,.str .x .x4 .x19 1704,.logic .and .x .x6 .x22 .x23],
    .ite (.zero .x .x6) (Paired.extraPair w16) (.block []),
    .block ((Paired.saved.zipIdx.reverse.map fun (r,i) => .ldr .x r .x19 (1800+8*i)))]

/-- The encapsulation matrix: the first `hashPairs` pairs absorb `ek`. -/
def matrixH (L : KemLay) (w16 : Bool := false) : Prog isa :=
  seqs (((List.range (L.k*L.k/2)).map fun i =>
      if i < hashPairs L then pair3 L (2*i) i w16 else Paired.pair L false (2*i) w16) ++
    (if L.k*L.k%2=1 then [Paired.lastSample L false w16] else []))

/-- The prologue, `m`, the all-zero third state and `ρ`. -/
def startH (L : KemLay) : Prog isa :=
  .block (L.kemPrologue 4 [0,2,3,4] ++ copy32 .x1 0 .x28 MB ++ zeroState .x28 KEM.ST ++
    copy32 .x25 (384*L.k) .x28 SB)

/-- `H(ek)` into `HB`, and `G(m ‖ H(ek))` into `key` and `RB`. -/
def tailH (hash : FixedHashCallers.HashFn) : Prog isa :=
  .seq (.block (copy32 .x28 KEM.ST .x28 HB))
    (hash .x28 KEM.ST WK 72 6 [⟨.x28,MB,32⟩,⟨.x28,HB,32⟩] [⟨.x26,0,32⟩,⟨.x28,RB,32⟩])

end VG.Impl.MlKem.AArch64.Hybrid
