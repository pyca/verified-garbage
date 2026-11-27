module

public import VerifiedGarbage.Impl.Camellia.X86.Sse
public import VerifiedGarbage.Impl.Camellia.X86.ExpandKey
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86.Sel

/-!
# The Camellia key schedule on x86 (32-bit) in XMM registers

The key schedule (`ExpandKey.lean`) whose `KA` and `KB` take the three pairs
of rounds by the core's (`Sse.lean`), all sixteen of its blocks the one
value: a plane is then a bit of each byte, copied through its lane. Its
slots start 384 bytes into the scratch buffer, after the values and the
saved registers; `edi` is moved there and back. The constants, as subkeys
(`copyIn`), and the values are in the slots of the core's subkeys and
blocks. Each pair takes the value (`vS`) to its planes (`spreadV`), and back
to bytes (`packV`): the bit of each byte that its plane has, XORed together.
-/

@[expose] public section

namespace VG.Impl.Camellia.X86.SseKey

open VG.X86
open VG.Impl.Modes.X86 (sb)
open VG.Impl.Camellia.X86.Sse

/-- Where the core's slots start in the scratch buffer. -/
def off : Nat := 384

/-- The values' slots: the running value, `KL`, `KR`, `KA` and `KB`. -/
def vS : Nat := 44
def klS : Nat := 45
def krS : Nat := 46
def kaS : Nat := 47
def kbS : Nat := 48

/-- The constants and `KL` and `KR` to the core's slots, from `edi` not yet moved. -/
def copyIn : List Instr :=
  (List.range 6).flatMap (fun i => [tb .xmm0 (144 + 16 * i), stx sb (off + 16 * (62 + i)) .xmm0]) ++
  [ld .xmm0 sb (4 * klSlot), stx sb (off + 16 * klS) .xmm0, ld .xmm0 sb (4 * krSlot), stx sb (off + 16 * krS) .xmm0]

/-- The values `a` and `b`, XORed, to the running value. -/
def xorV (a b : Nat) : List Instr := [ldS .xmm0 a, ldS .xmm1 b, x .pxor .xmm0 .xmm1, stS vS .xmm0]

/-- The planes at `d` of the bytes in the lanes of `r`. -/
def planes (d : Nat) (r : XReg) : List Instr :=
  (List.range 8).flatMap fun j => kPlane .xmm6 r j ++ [stS (d + j) .xmm6]

/-- The running value to the planes of its halves. -/
def spreadV : List Instr :=
  [tb .xmm7 0, ldS .xmm0 vS, mv .xmm1 .xmm0, x .pand .xmm0 .xmm7, sh .psrld .xmm1 8, x .pand .xmm1 .xmm7, mv .xmm2 .xmm0,
   x .punpcklwd .xmm0 .xmm1, x .punpckhwd .xmm2 .xmm1] ++ planes d1 .xmm0 ++ planes d2 .xmm2

/-- The bytes of the planes at `d`, one in each lane, then in the low half of `r`. -/
def gather (d : Nat) (r : XReg) : List Instr :=
  [tb .xmm7 240, ldS r d, x .pand r .xmm7] ++
  (List.range 7).flatMap (fun j => [sh .pslld .xmm7 1, ldS .xmm1 (d + (j + 1)), x .pand .xmm1 .xmm7, x .pxor r .xmm1]) ++
  [mv .xmm1 r, sh .psrld .xmm1 8, x .pxor r .xmm1, .xop (.pshuflw r r 0xD8), .xop (.pshufhw r r 0xD8),
   .xop (.pshufd r r 0xD8)]

/-- The planes of the halves to the value at slot `dst`. -/
def packV (dst : Nat) : List Instr :=
  gather d1 .xmm0 ++ gather d2 .xmm2 ++ [x .punpcklqdq .xmm0 .xmm2, stS dst .xmm0]

/-- A pair of rounds on the running value, to slot `dst`. -/
def pairV (dst : Nat) : List Instr := spreadV ++ round 32 d1 d2 ++ round 48 d2 d1 ++ packV dst

/-- On to the next pair's subkeys. -/
def next : Instr := .alu .add kr (.imm 32)

/-- `KA` and `KB`, from `KL` and `KR`. -/
def kaKb : List Instr :=
  xorV klS krS ++ (pairV vS ++ (xorV vS klS ++ (next :: (pairV kaS ++ (xorV kaS krS ++ (next :: pairV kbS))))))

/-- `KA` and `KB` to the values' slots of the key schedule, `edi` moved back. -/
def copyOut : List Instr :=
  [ld .xmm0 sb (off + 16 * kaS), stx sb (4 * kaSlot) .xmm0, ld .xmm0 sb (off + 16 * kbS), stx sb (4 * kbSlot) .xmm0]

/-- The block of the key schedule's code for `KA` and `KB`. -/
def mid : List Instr :=
  .mov tbr (.reg .edx) :: (copyIn ++ (.alu .add sb (.imm 384) :: .mov kr (.reg sb) :: .alu .add kr (.imm 960) ::
    (kaKb ++ (.alu .sub sb (.imm 384) :: copyOut))))

/-- `vg_camellia_expand_key`, with its scratch buffer as the fourth argument. -/
def expandKey : Prog isa := X86.expandKey tableName mid

/-- The scratch buffer's slots, of 4 bytes. -/
def slots : Nat := 368

namespace Fn

/-- The doublewords of the 1508 bytes of stack below `esp` that the residue
analysis finds the function may leave different in two runs: the header of
its working space's frame, and the frame's last three doublewords, which
nothing writes. -/
def words : List Nat := [1, 2, 3, 4, 5, 374, 375, 376]

/-- `Spec.Camellia.expandKeyApi`'s function as emitted. -/
def expandKey : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1508 words
    (Impl.StackScratch.X86.withStackScratchWiped 1504 3 368 SseKey.expandKey)

end Fn

end VG.Impl.Camellia.X86.SseKey
