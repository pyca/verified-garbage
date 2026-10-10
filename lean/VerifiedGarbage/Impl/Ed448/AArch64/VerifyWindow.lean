import VerifiedGarbage.Impl.Ed448.AArch64.VerifyEquation

/-!
# Ed448 verification's equation on AArch64, by a comb and 4-bit windows

`vg_ed448_verify_equation(pk = x0, signature = x1, challenge = x2,
scratch = x3) -> w0`: the checks of `S` and of the encodings of `A` and `R`
are `VerifyEquation.lean`'s (with X448's memory-resident arithmetic), as is the
comparison of `[4]Q` with `[4]R`; but `Q = [S]B + [k](-A)` is computed with the
register-resident arithmetic (`Impl/Curve448/AArch64/Fast.lean`):

* `[S]B` by `vg_ed448_scalar_base`'s comb of 57 tables (`Point56.combLoop 57`, `Point56.combineCall`),
  from the bits of `S` at `BITS`.
* `[k](-A)` by 4-bit windows from the top, each four doublings and the
  addition of `[n](-A)` for the window's digit `n`, selected in constant time
  with a mask for each of the 16 entries of a table of `[n](-A)` built at run
  time (`TAB`, entry `n` at `TAB + 192 n`: `X`, `Y` and `Z`, eight words each).
  Entry 0 is the neutral point, so every window adds one.

The additions and doublings of the table, the windows and the comparison are
calls of `vg_ed448_r56_point_add` and `vg_ed448_r56_point_double`
(`Point56.lean`), on slots 3–5 and 6–8. The challenge's bytes are copied to
the working space (`KB`) at the entry, since the field operations use every
register that could keep its pointer; `R`, once decoded, is kept at `RX` and
`RY`. The function saves `x19`–`x28`, its return address and `v8`–`v15` in
the working space and restores them. Every address and branch depends only on
the pointers and counters.
-/

namespace VG.Impl.Ed448.AArch64

open VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot BITS)
open VG.Impl.X448.AArch64.Fast (codeOf)
open VG.Impl.X448.AArch64.Base (constSlot)

/-! ## The working space -/

/-- The challenge's 57 bytes, copied at the entry: the windows read them from the working
space, at addresses from public registers. -/
def KB : Nat := 2944
/-- The table of `[n](-A)`, `n < 16`: 192 bytes each. -/
def TAB : Nat := 4992
/-- `R`'s `x` and `y`: after the table, and at `CAN`, which nothing uses between the decoding of
`R` and its comparison. -/
def RX : Nat := 8064
def RY : Nat := CAN

/-! ## Entry -/

/-- The challenge's bytes copied to `KB`, and `x21`–`x28` and `v8`–`v15` saved. -/
def wsave : List Instr :=
  (List.range 57).flatMap (fun i => [.ldrb .x4 .x2 i, .strb .x4 .x3 (KB + i)]) ++
    Impl.X448.AArch64.Fast.save ++ Impl.X448.AArch64.Fast.vsave

/-! ## The table of `[n](-A)` -/

/-- Slots 3–5 to entry `x19` of the table. -/
def tabStore : List Instr :=
  [.lsl .x .x8 .x19 7, .lsl .x .x9 .x19 6, .add .x .x8 .x8 .x9, .add .x .x8 .x8 .x3] ++
  (List.range 24).flatMap fun w =>
    [ld .x4 (slot (3 + w / 8) + 8 * (w % 8)), .str .x .x4 .x8 (TAB + 8 * w)]

/-- `R` (slots 8–9) to `RX` and `RY`; zero in slot 19 and 1 in slot 20; entry 0 the neutral
point; `-A` (`(x, y, 1)`, from slots 6–7) in slots 3–5 and 6–8 and as entry 1; and the
counter at 2. -/
def tabInit : List Instr :=
  Curve448.AArch64.copy RX (slot 8) ++ Curve448.AArch64.copy RY (slot 9) ++
  constSlot (slot 19) 0 ++ constSlot (slot 20) 1 ++
  constSlot TAB 0 ++ constSlot (TAB + 64) 1 ++ constSlot (TAB + 128) 1 ++
  Curve448.AArch64.copy (slot 3) (slot 6) ++ Curve448.AArch64.copy (slot 4) (slot 7) ++ constSlot (slot 5) 1 ++
  constSlot (slot 8) 1 ++ [.movz .x .x19 1 0] ++ tabStore ++ [.movz .x .x19 2 0]

/-- Entry `x19` = entry `x19 - 1` (slots 3–5) plus `-A` (slots 6–8); `x9` is nonzero
while another entry follows. -/
def tabBody : Prog isa :=
  .seq Point56.addCall (.block (tabStore ++ [.addImm .x .x19 .x19 1, .subImm .x .x9 .x19 16]))

def table : Prog isa := .seq (.block tabInit) (.loop tabBody (.nonzero .x .x9))

/-! ## `[S]B` -/

/-- Both accumulators at `[G] B`, the comb's steps over the bits of `S` (at `BITS`), and
`16 A + B`: `[S]B` in slots 0–2. -/
def sBase : Prog isa :=
  .seq (.block (Impl.X448.AArch64.Base.accs Impl.X448.baseG57)) <|
  .seq (Point56.combLoop 57) Point56.combineCall

/-! ## `[k](-A)` -/

/-- The registers holding the masks of the digits `0 … 15`. -/
def maskRegs : List Reg :=
  [.x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x0, .x1, .x2, .x4, .x5, .x6, .x7, .x8]

def maskReg (m : Nat) : Reg := maskRegs.getD m .x21

/-- `maskReg m` = all ones exactly if the digit `n` in `x11` is `m`: `[n < m] - [n < m + 1]`,
the top bits of `n - (m + 1)` and `n - m`, negated. -/
def digitMask (m : Nat) : List Instr :=
  [.subImm .x (maskReg m) .x11 (m + 1), .lsr .x (maskReg m) (maskReg m) 63,
    .subImm .x .x10 .x11 m, .lsr .x .x10 .x10 63, .sub .x (maskReg m) .x10 (maskReg m)]

def digitMasks : List Instr := (List.range 16).flatMap digitMask

/-- Word `w` of the selected entry (`X`, `Y`, `Z`: eight words each) to slots 6–8. -/
def selectEntryWord (w : Nat) : List Instr :=
  [ld .x9 (TAB + 8 * w), .logic .and .x .x9 .x9 (maskReg 0)] ++
  (List.range 15).flatMap (fun m =>
    [ld .x10 (TAB + 192 * (m + 1) + 8 * w), .logic .and .x .x10 .x10 (maskReg (m + 1)),
      .logic .orr .x .x9 .x9 .x10]) ++
  [st .x9 (slot (6 + w / 8) + 8 * (w % 8))]

/-- The entry for the digit in `x11` to slots 6–8. -/
def selectEntry : List Instr := digitMasks ++ (List.range 24).flatMap selectEntryWord

/-- `x11` = byte `x19` of `k` (from `KB`), shifted right by `sh` and masked to 4 bits. -/
def digitOf (sh : Nat) : List Instr :=
  [.add .x .x2 .x3 .x19, .ldrb .x11 .x2 KB, .movz .x .x10 15 0] ++
  (if sh = 0 then [] else [.lsr .x .x11 .x11 sh]) ++ [.logic .and .x .x11 .x11 .x10]

/-- `Q` (slots 3–5) doubled four times: a loop counted by `x1`, which the doubling keeps. -/
def dbl4Loop : Prog isa :=
  .seq (.block [.movz .w .x1 4 0])
    (.loop (.seq Point56.doubleCall (.block [.subImm .x .x1 .x1 1])) (.nonzero .x .x1))

/-- A window: `Q` (slots 3–5) doubled four times, and the entry of the digit
(`digitOf sh`) added. -/
def window (sh : Nat) : Prog isa :=
  .seq dbl4Loop (.seq (.block (digitOf sh ++ selectEntry)) Point56.addCall)

/-- Byte `x19 - 1` of `k` (`x19` counts down to it): its high and its low digit. -/
def kByte : Prog isa := .seq (.block [.subImm .x .x19 .x19 1]) (.seq (window 4) (window 0))

/-- `Q` the neutral point, 1 in slot 20 (for `dblOps`), and the counter at 57. -/
def kInit : List Instr :=
  constSlot (slot 3) 0 ++ constSlot (slot 4) 1 ++ constSlot (slot 5) 1 ++ constSlot (slot 20) 1 ++
    [.movz .x .x19 57 0]

/-- `kInit`, then the 57 bytes of `k`, from the top. -/
def kWindows : Prog isa := .seq (.block kInit) (.loop kByte (.nonzero .x .x19))

/-! ## The comparison -/

/-- `Q = [k](-A) + [S]B` in slots 3–5 (`[S]B` copied from slots 0–2 to 6–8), doubled twice and
copied to slots 0–2; `R` from `RX` and `RY` into slots 3–5 (`Z = 1`), doubled twice; and the
products `X_Q Z_R`, `X_R Z_Q`, `Y_Q Z_R`, `Y_R Z_Q` in slots 12–15. -/
def wcross : Prog isa :=
  .seq (.block (Curve448.AArch64.copy (slot 6) (slot 0) ++ Curve448.AArch64.copy (slot 7) (slot 1) ++
    Curve448.AArch64.copy (slot 8) (slot 2))) <|
  .seq Point56.addCall <| .seq Point56.doubleCall <| .seq Point56.doubleCall <|
  .seq (.block (Curve448.AArch64.copy (slot 0) (slot 3) ++ Curve448.AArch64.copy (slot 1) (slot 4) ++
    Curve448.AArch64.copy (slot 2) (slot 5) ++ Curve448.AArch64.copy (slot 3) RX ++
    Curve448.AArch64.copy (slot 4) RY ++ constSlot (slot 5) 1)) <|
  .seq Point56.doubleCall <| .seq Point56.doubleCall <|
  .block (codeOf [.mul (slot 12) (slot 0) (slot 5), .mul (slot 13) (slot 3) (slot 2),
     .mul (slot 14) (slot 1) (slot 5), .mul (slot 15) (slot 4) (slot 2)])

/-- The comparisons, the result `x0 = (x20 == 0)`, and the registers restored. -/
def wfinish : List Instr :=
  eqSlots 12 13 ++ eqSlots 14 15 ++ [.addImm .x .x5 .x20 0] ++ isZero ++
  [.addImm .x .x0 .x5 0, ld .x19 0, ld .x20 8, ld .x30 LRS] ++ Impl.X448.AArch64.Fast.restore ++
  Impl.X448.AArch64.Fast.vrestore

/-- The entry, the bits of `S`, its check, and the decodings of `A` (negated, into slots 6–7) and
`R` (into slots 8–9). -/
def wfront : Prog isa :=
  .seq (.block (ventry ++ wsave)) <| .seq (bitsAt .x1 57 0 BITS) <| .seq (.block sCheck) <|
  .seq vdecodeA (decode .x1 8 9)

def verifyEquation : Prog isa :=
  .seq wfront <| .seq table <| .seq sBase <| .seq kWindows <| .seq wcross (.block wfinish)

end VG.Impl.Ed448.AArch64
