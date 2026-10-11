/-!
# Block cipher modes, one step at a time, for any target

A mode of operation here processes its data one *step* at a time (a block,
or a byte for CFB8), in three *areas*: the step's data (`dat`), the mode's
chaining value or input block (`chn`), and the first block of the block
cipher's buffer (`buf`). A step is `pre`, the block cipher on `buf`, and
`post`, where `pre` and `post` are lists of operations (`Op`): copies and
XORs among the areas, of 4-byte words or bytes. Each target compiles the
operations and runs the steps (`Impl/Modes/X86/Seq.lean`); the modes'
correctness is proven of the operations, for any target
(`Proof/Modes/Ops.lean`, `Proof/Modes/Steps.lean`).
-/

namespace VG.Impl.Modes

/-- The areas of a step. -/
inductive Loc | dat | chn | buf
  deriving DecidableEq, Repr

/-- `dst := src` or `dst := src ⊕ xr`, on a word (`wide`) or a byte, at
byte offsets into the areas. -/
structure Op where
  wide : Bool
  dst : Loc
  dOff : Nat
  src : Loc
  sOff : Nat
  xr : Option (Loc × Nat) := none
  deriving DecidableEq, Repr

/-- A mode, one step at a time: the operations before and after the core,
the bytes of data a step consumes, and whether the chaining value goes back
to the IV at the end. -/
structure Mode where
  pre : List Op
  post : List Op
  step : Nat
  ivOut : Bool

/-- `dst := src` on a block of `bw` words. -/
def copyBlk (bw : Nat) (dst src : Loc) : List Op :=
  (List.range bw).map fun w => { wide := true, dst, dOff := 4 * w, src, sOff := 4 * w }

/-- `dst := a ⊕ b` on a block of `bw` words. -/
def xorBlk (bw : Nat) (dst a b : Loc) : List Op :=
  (List.range bw).map fun w => { wide := true, dst, dOff := 4 * w, src := a, sOff := 4 * w, xr := some (b, 4 * w) }

/-! ## The modes, for blocks of `bw` words -/

namespace Mode

variable (bw : Nat)

/-- CBC encryption (SP 800-38A §6.2): `buf := Pⱼ ⊕ Cⱼ₋₁`, and
`Cⱼ = CIPH_K(buf)` to the chaining value and the data. -/
def cbcEnc : Mode where
  pre := xorBlk bw .buf .dat .chn
  post := copyBlk bw .chn .buf ++ copyBlk bw .dat .buf
  step := 4 * bw
  ivOut := false

/-- CBC decryption (§6.2): `buf := Cⱼ`, and `Pⱼ = CIPH⁻¹_K(buf) ⊕ Cⱼ₋₁` to
the data, `Cⱼ` (in `buf` meanwhile) to the chaining value. -/
def cbcDec : Mode where
  pre := copyBlk bw .buf .dat
  post := xorBlk bw .buf .buf .chn ++ copyBlk bw .chn .dat ++ copyBlk bw .dat .buf
  step := 4 * bw
  ivOut := false

/-- OFB (§6.4): `buf := Oⱼ₋₁`, and `Oⱼ = CIPH_K(buf)` to the chaining value
and XORed into the data. -/
def ofb : Mode where
  pre := copyBlk bw .buf .chn
  post := copyBlk bw .chn .buf ++ xorBlk bw .dat .dat .buf
  step := 4 * bw
  ivOut := true

/-- CFB encryption, with segments of a block (§6.3): `buf := Cⱼ₋₁`, and
`Cⱼ = Pⱼ ⊕ CIPH_K(buf)` to the data and the chaining value. -/
def cfbEnc : Mode where
  pre := copyBlk bw .buf .chn
  post := xorBlk bw .dat .dat .buf ++ copyBlk bw .chn .dat
  step := 4 * bw
  ivOut := true

/-- CFB decryption (§6.3): `buf := Cⱼ₋₁`, `Cⱼ` to the chaining value, and
`Pⱼ = Cⱼ ⊕ CIPH_K(buf)` to the data. -/
def cfbDec : Mode where
  pre := copyBlk bw .buf .chn
  post := copyBlk bw .chn .dat ++ xorBlk bw .dat .dat .buf
  step := 4 * bw
  ivOut := true

/-- The input block shifted left by a byte, the data byte shifted in. -/
def shiftIn : List Op :=
  (List.range (4 * bw - 1)).map (fun i => { wide := false, dst := .chn, dOff := i, src := .chn, sOff := i + 1 }) ++
    [{ wide := false, dst := .chn, dOff := 4 * bw - 1, src := .dat, sOff := 0 }]

/-- CFB8 encryption (§6.3, 8-bit segments): `buf := Iⱼ`, `C#ⱼ = P#ⱼ ⊕
MSB₈(CIPH_K(buf))` to the data byte, and `Iⱼ₊₁` (`Iⱼ` without its first
byte, followed by `C#ⱼ`) to the input block. -/
def cfb8Enc : Mode where
  pre := copyBlk bw .buf .chn
  post := { wide := false, dst := .dat, dOff := 0, src := .dat, sOff := 0, xr := some (.buf, 0) } :: shiftIn bw
  step := 1
  ivOut := true

/-- CFB8 decryption: `buf := Iⱼ`, `Iⱼ₊₁` (with the ciphertext byte `C#ⱼ`)
to the input block, and `P#ⱼ = C#ⱼ ⊕ MSB₈(CIPH_K(buf))` to the data byte. -/
def cfb8Dec : Mode where
  pre := copyBlk bw .buf .chn
  post := shiftIn bw ++ [{ wide := false, dst := .dat, dOff := 0, src := .dat, sOff := 0, xr := some (.buf, 0) }]
  step := 1
  ivOut := true

end Mode

end VG.Impl.Modes
