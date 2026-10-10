import VerifiedGarbage.Impl.Ed448.X86_64.ScalarBase

/-!
# Ed448 verification's equation on x86-64

`vg_ed448_verify_equation(pk = rdi, signature = rsi, challenge = rdx,
scratch = rcx) -> eax`: 1 if the public key and `R` (the signature's first 57
bytes) decode, `S` (its last 57) is below `L`, and `[4][S]B = [4]R + [4][k]A`
for the 456-bit challenge `k`; 0 otherwise.

Everything is computed whatever the inputs, and the checks are accumulated
in the word `BAD` of the working space, which stays 0 exactly when every one
passes: each check ORs into it a word that is 0 if and only if it passes.

* `S < L`: its byte 56 is 0 and its low 448 bits plus `2^448 - L` do not carry.
* Decoding a point (RFC 8032 §5.2.3) at `rsi` into the slots `xo` and `yo`:
  the seven words of `y`, which must be below `p` (they are equal to their
  full reduction) with bits 448–454 of the encoding 0; `u = y² - 1`,
  `v = d y² - 1`, the candidate root `x = u³v (u⁵v³)^((p-3)/4)` (by
  `root`, X448's addition chain until `2^223 - 1`, then 223 squarings), the
  check `v x² = u`, the check that `x = 0` comes with the sign bit 0, and `x`
  negated (swapped with `-x` by a mask) if its low bit is not the sign bit.
* `R` and then `A` are decoded into slots 6–7 by one loop (`vdecode`), `R`
  kept at `RX` and `RY` (`Z = 1` in slot 10). `A` is negated, and
  `Q = [S]B + [k](-A)` computed from the top bit down, as `[s]B` is: `Q`
  doubled, `B` added and swapped into `Q` by bit `t` of `S`, then `-A` added
  and swapped in by bit `t` of `k`. The doublings and additions are calls of
  `vg_ed448_r64_point_double` and `vg_ed448_r64_point_add_affine`
  (`Point64.lean`), which add the point in slots 8–9 with `Z = 1`: `-A` is
  copied there for its addition, and `B` written back after it.
* `Q` is doubled twice and copied into slots 3–5, `R` into slots 0–2 (with
  `Z = 1`) and doubled twice, and they are compared: `X_Q Z_R = X_R Z_Q` and
  `Y_Q Z_R = Y_R Z_Q`, fully reduced.

The result is 1 if `BAD` is 0. Every address and branch depends only on the
pointers.
-/

namespace VG.Impl.Ed448.X86_64

open VG.X86_64
open VG.Impl.X448.X86_64 (at_ sc W w loads stores slot Field add sub cswap freeze sqn BITS chain chain223 pow223Keep copyOut)

/-! ## The working space -/

/-- The pointers to the public key and the signature. -/
def PPK : Nat := 1664
def PSIG : Nat := 1672
/-- The accumulated checks: 0 if they all pass. -/
def BAD : Nat := 1688
/-- The sign bit of the point being decoded. -/
def SIGN : Nat := 1696
/-- The mask of `x`'s negation. -/
def NEG : Nat := 1704
/-- A fully reduced field element, to compare another with. -/
def CAN : Nat := 1712
/-- The bits of `k` (those of `S` are at X448's `BITS`). -/
def KBITS : Nat := 2560
/-- `R`, decoded first, kept while `A` is decoded and `Q` computed: its `X` and `Y`, above
`BAD`'s area, where no field operation writes. -/
def RX : Nat := 1768
def RY : Nat := 1824
/-- The pointer to the point the decoding loop decodes next, and the decodings left. -/
def PCUR : Nat := 1880
def CNT : Nat := 1888

/-! ## Checks -/

/-- `BAD |= rdx`. -/
def orBad : List Instr :=
  [.mov .rax (.mem (sc BAD)), .alu .or .rax (.reg .rdx), .store (sc BAD) .rax]

/-- `rdx = (rdx == 0)`. -/
def isZero : List Instr :=
  [.alu .cmp .rdx (.imm 1), .mov32 .rdx (.imm 0), .alu .adc .rdx (.imm 0)]

/-- `rdx = ⋁ (r8–r14 ⊕ [o + 8i])`: 0 exactly when `r8–r14` are the seven
words at `o`. -/
def diffWords (o : Nat) : List Instr :=
  [.mov32 .rdx (.imm 0)] ++ (List.range 7).flatMap fun i =>
    [.mov .rax (.mem (sc (o + 8 * i))), .alu .xor .rax (.reg (w i)), .alu .or .rdx (.reg .rax)]

/-- `BAD |= 0` exactly when slots `a` and `b` hold the same field element. -/
def eqSlots (a b : Nat) : List Instr :=
  freeze (slot a) ++ (stores CAN W ++ (freeze (slot b) ++ (diffWords CAN ++ orBad)))

/-- `BAD |= 0` exactly when the 57 bytes at `rsi` are below `L`: byte 56 is
0, and the seven words below it plus `2^448 - L` (stored at `KC`, in slot 1,
which is not yet in use) do not carry. -/
def sCheck : List Instr :=
  storeK ++ (((List.range 7).map fun i => .mov (w i) (.mem (at_ .rsi (8 * i)))) ++
  (chain .add .adc W ((List.range 7).map fun i => .mem (sc (KC + 8 * i))) ++
  ([.mov32 .rdx (.imm 0), .alu .adc .rdx (.imm 0), .movzx8 .rax (at_ .rsi 56),
    .alu .or .rdx (.reg .rax)] ++ orBad)))

/-! ## Decoding a point -/

/-- `[T7] = [z]^((p-3)/4)` from `chain223` of `z`: `(z^(2^223 - 1))^(2^223) · z^(2^222 - 1)`. -/
def rootTail (F : Field) : Prog isa :=
  .seq (sqn F (slot 21) (slot 21) 223) (.block (F.mul (slot 21) (slot 21) (slot 20)))

/-- `[T7] = [z]^((p-3)/4)`: X448's addition chain (`invert`) as far as
`z^(2^223 - 1)` in `T7` and `z^(2^222 - 1)` in `T6` (`chain223`), then
`rootTail`. -/
def root (F : Field) (z : Nat) : Prog isa := .seq (chain223 F (slot z)) (rootTail F)

/-- `root F 12`, the chain by a call of `vg_gf448_r64_pow223`, keeping the decoding loop's
public words, `PPK` and `CNT`. -/
def rootCall (F : Field) : Prog isa := .seq (pow223Keep [PPK, CNT]) (rootTail F)

/-- The 57 bytes at `rsi`: `y`'s seven words into slot `yo`, the sign bit
into `SIGN`, and `BAD |= 0` exactly when bits 448–454 are 0 and `y < p`. -/
def decodeY (yo : Nat) : List Instr :=
  ((List.range 7).map fun i => .mov (w i) (.mem (at_ .rsi (8 * i)))) ++ (stores (slot yo) W ++
  ([.movzx8 .rdx (at_ .rsi 56), .mov .rax (.reg .rdx), .shift .shr .rax 7, .store (sc SIGN) .rax,
    .alu .and .rdx (.imm 0x7f)] ++ (orBad ++
  (freeze (slot yo) ++ (diffWords (slot yo) ++ orBad)))))

/-- `x` in slot `xo`, from `u³v` there and the root in slot 21, and the
check `v x² = u`. -/
def decodeX (F : Field) (xo : Nat) : List Instr :=
  fieldCode F [.mul xo xo 21, .sqr 12 xo, .mul 12 3 12] ++ eqSlots 12 13

/-- The sign: `x` fully reduced; `BAD |= 0` exactly when `x ≠ 0` or the
sign bit is 0; `NEG` the mask of `x`'s low bit differing from the sign bit;
then `x` swapped with `-x` (from slot 12) by that mask. -/
def decodeSign (F : Field) (xo : Nat) : List Instr :=
  freeze (slot xo) ++ ([.mov .rcx (.reg .r8), .alu .and .rcx (.imm 1), .mov .rax (.mem (sc SIGN)),
    .alu .xor .rcx (.reg .rax), .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rcx), .store (sc NEG) .rdx,
    .mov .rdx (.reg .r8)] ++ ((List.range 6).map (fun i => .alu .or .rdx (.reg (w (i + 1)))) ++
  (isZero ++ ([.alu .and .rdx (.reg .rax)] ++ (orBad ++
  (fieldCode F [.sub 12 xo xo, .sub 12 12 xo] ++ ([.mov .rcx (.mem (sc NEG))] ++
    cswap (slot xo) (slot 12))))))))

/-- Decode the 57 bytes at `rsi` into slots `xo` and `yo`, with the square root's power
`rt` (`root F 12`, or `rootCall F`). -/
def decode (F : Field) (xo yo : Nat) (rt : Prog isa := root F 12) : Prog isa :=
  .seq (.block (decodeY yo ++ fieldCode F (decodeUV yo xo))) <| .seq rt <|
    .block (decodeX F xo ++ decodeSign F xo)

/-! ## `[S]B + [k](-A)` -/

/-- `rcx = -[rdi + o + rbx]`: the mask of bit `rbx` of the bits at `o`. -/
def maskAt (o : Nat) : List Instr :=
  [.movzx8 .rdx { base := .rdi, index := some .rbx, disp := (o : Int) }, .mov32 .rcx (.imm 0),
    .alu .sub .rcx (.reg .rdx)]

/-- `T` swapped into `R` by the mask `rcx`. -/
def swapT : List Instr := cswap (slot 0) (slot 3) ++ cswap (slot 1) (slot 4) ++ cswap (slot 2) (slot 5)

/-- `-A` (slots 6–7) into slots 8–9, where the affine addition reads its second point. -/
def stageA : List Instr := copyOut (slot 8) (slot 6) ++ copyOut (slot 9) (slot 7)

/-- `B` back into slots 8–9. -/
def restoreB : List Instr :=
  constSlot 8 Spec.Ed448.basePoint.X ++ constSlot 9 Spec.Ed448.basePoint.Y

/-- One bit `t = rbx - 1`, from the top, with the point operations `P`: `Q` doubled, `B` (in
slots 8–9) added and swapped in by bit `t` of `S`, `-A` (copied into slots 8–9) added and
swapped in by bit `t` of `k`, and `B` restored. -/
def vstep (P : Point64.Ops) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <| .seq P.dbl <| .seq P.add <|
  .seq (.block (maskAt BITS ++ (swapT ++ stageA))) <| .seq P.add <|
    .block (maskAt KBITS ++ (swapT ++ (restoreB ++ [.alu .test .rbx (.reg .rbx)])))

/-- The 456 bits, from 455 down to 0. -/
def vloop (P : Point64.Ops) : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 456)]) (.loop (vstep P) .ne)

/-! ## The function -/

/-- The bits of the 57 bytes at `rsi` at `o`: byte `t` is bit `t`. -/
def bitsBodyAt (o : Nat) : List Instr :=
  [.movzx8 .rax { base := .rsi, index := some .rbx }] ++
    ((List.range 8).flatMap fun j =>
      [.mov .rdx (.reg .rax)] ++ (if j = 0 then [] else [.shift .shr .rdx j]) ++
      [.alu .and .rdx (.imm 1),
        .store8 { base := .rdi, index := some .rbx, scale := 8, disp := ((o + j : Nat) : Int) } .rdx]) ++
    [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 57)]

def bitsAt (o : Nat) : Prog isa := .seq (.block [.mov32 .rbx (.imm 0)]) (.loop (.block (bitsBodyAt o)) .ne)

/-- The callee-saved registers saved at the working space `rcx`, the
pointers to `A` and the signature kept in `r8` and `r9`, the working space
into `rdi`, and the challenge's into `rsi`. -/
def ventry : List Instr :=
  saveAt .rcx ++ [.mov .r8 (.reg .rdi), .mov .r9 (.reg .rsi), .mov .rdi (.reg .rcx), .mov .rsi (.reg .rdx)]

/-- The bits of `k` and `S`, before anything is stored that is read back as
an address: their stores are at a counter's offset. -/
def vbits : Prog isa :=
  .seq (bitsAt KBITS) <| .seq (.block [.mov .rsi (.reg .r9), .alu .add .rsi (.imm 57)]) (bitsAt BITS)

/-- The pointers to `A` and the signature saved, `BAD = 0`, and the check of
`S` (at `rsi`). -/
def vstart : List Instr :=
  [.store (sc PPK) .r8, .store (sc PSIG) .r9, .mov32 .rax (.imm 0), .store (sc BAD) .rax] ++ sCheck

/-- One decoding: slots 6–7 kept at `RX` and `RY`, the constants, and the point at `PCUR`
decoded into slots 6–7; then `PCUR` at `A`, and `CNT` moved down (ZF set at 0). -/
def vdecodeBody (F : Field) (rt : Prog isa := root F 12) : Prog isa :=
  .seq (.block (copyOut RX (slot 6) ++ copyOut RY (slot 7) ++ consts ++ [.mov .rsi (.mem (sc PCUR))])) <|
  .seq (decode F 6 7 rt) <|
    .block [.mov .rsi (.mem (sc PPK)), .store (sc PCUR) .rsi, .mov .rbx (.mem (sc CNT)),
      .alu .sub .rbx (.imm 1), .store (sc CNT) .rbx]

/-- `R` (the signature's first half) decoded, then `A`: a loop of two iterations, counted by
`CNT`. `A` ends in slots 6–7 and `R` at `RX` and `RY`. -/
def vdecode (F : Field) (rt : Prog isa := root F 12) : Prog isa :=
  .seq (.block [.mov .rsi (.mem (sc PSIG)), .store (sc PCUR) .rsi, .mov32 .rbx (.imm 2),
    .store (sc CNT) .rbx]) (.loop (vdecodeBody F rt) .ne)

/-- `A` negated, with the constants. -/
def vnegA (F : Field) : List Instr := consts ++ fieldCode F [.sub 6 0 6]

/-- `[4]Q` into slots 3–5, and `R` (`Z = 1`) into slots 0–2. -/
def vR : List Instr :=
  copyOut (slot 3) (slot 0) ++ (copyOut (slot 4) (slot 1) ++ (copyOut (slot 5) (slot 2) ++
    (copyOut (slot 0) RX ++ (copyOut (slot 1) RY ++ constSlot 2 1))))

/-- The point in slots 0–2 doubled twice: a loop of two iterations, counted by `rbx`. -/
def vdouble (P : Point64.Ops) : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 2)]) (.loop (.seq P.dbl (.block [.alu .sub .rbx (.imm 1)])) .ne)

/-- `[4]Q` and `[4]R` compared (`BAD |= 0` exactly when they are the same
point), the result `eax = (BAD == 0)`, and the callee-saved registers
restored. -/
def vfinish (F : Field) (P : Point64.Ops) : Prog isa :=
  .seq (vdouble P) <| .seq (.block vR) <| .seq (vdouble P) <|
  .block (fieldCode F [.mul 12 3 2, .mul 13 0 5] ++ (eqSlots 12 13 ++
    (fieldCode F [.mul 12 4 2, .mul 13 1 5] ++ (eqSlots 12 13 ++
    ([.mov .rdx (.mem (sc BAD))] ++ (isZero ++ ([.mov .rax (.reg .rdx)] ++
      Impl.X448.X86_64.restore)))))))

/-- `vg_ed448_verify_equation` with the field multiplications `F`, the point operations `P`
and the square root's power `rt`. -/
def verifyEquationWith (F : Field) (P : Point64.Ops) (rt : Prog isa := root F 12) : Prog isa :=
  .seq (.block ventry) <| .seq vbits <| .seq (.block vstart) <| .seq (vdecode F rt) <|
    .seq (.block (vnegA F)) <| .seq (vloop P) (vfinish F P)

def verifyEquation : Prog isa :=
  verifyEquationWith Impl.X448.X86_64.baseline Point64.calls (rootCall Impl.X448.X86_64.baseline)

end VG.Impl.Ed448.X86_64
