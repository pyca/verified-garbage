import VerifiedGarbage.Impl.Bignum.X86_64.AdxSquare

/-!
# Montgomery reduction by rows of eight-word blocks (x86-64, BMI2 and ADX)

`redc` reduces the `2 w` words at `aAcc + 16` (`w` a positive multiple of
8) as `AdxSquare.redc` does, a row per word of the result: the head computes
the row's multiplier `u = t_i · (-m⁻¹)`, the row adds `u m` to the window at
word `i` and the tail adds its carry and the previous row's to word `i + w`.
Only the row differs: it adds `u m` by blocks of eight words, each word a
`mulx` of the modulus, an `adcx` of the window's word and an `adox` of the
previous word's high half, both chains closed into the block's high half
(`rcx`) at its end. The window and the modulus are addressed through pointers
(`r13`, `r15`) that advance by a block, with displacements only: an indexed
address keeps the store and the memory operands of `adcx` and `mulx` from
staying micro-fused on Intel's cores, which made `AdxSquareWide.row` slower.
The rows' memory traffic, unlike `AdxRotate8.redc`'s register tiles, leaves
each row's multiply-adds independent of the next row's multiplier, which
out-of-order execution overlaps.
-/

namespace VG.Impl.Bignum.X86_64.AdxRowRedc

open VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

/-- Word `k` of a block: `hi:r11 := rdx · m_k`, `r11 += t_k` (CF),
`r11 += prev` (OF), `t_k := r11`. -/
def word (k : Nat) (hi prev : Reg) : List Instr :=
  [.mulx hi .r11 (.mem (at_ .r15 (8 * k))), .adcx .r11 (.mem (at_ .r13 (8 * k))), .adox .r11 (.reg prev),
    .store (at_ .r13 (8 * k)) .r11]

/-- Two words, returning the high half to `rcx`. -/
def pair (k : Nat) : List Instr := word k .rax .rcx ++ word (k + 1) .rcx .rax

/-- `n` pairs from word `k`. -/
def chain : Nat → Nat → List Instr
  | 0, _ => []
  | n + 1, k => pair k ++ chain n (k + 2)

/-- A block of eight words, both chains closed into `rcx`; then the pointers
advance a block and the count `r14` eight words, compared with `w` in `rbx`. -/
def block : List Instr :=
  ([.alu32 .xor .rsi (.reg .rsi)] : List Instr) ++ chain 4 0 ++ Adx.close .rcx ++
    ([.alu .add .r13 (.imm 64), .alu .add .r15 (.imm 64), .alu .add .r14 (.imm 8),
      .alu .cmp .r14 (.reg .rbx)] : List Instr)

/-- The row's pointers, its count and its zero carry. -/
def rowInit : List Instr :=
  [.mov .rbx (.reg .rbp), .mov32 .rcx (.imm 0), .mov32 .r14 (.imm 0), .mov .r13 (.reg .r8),
    .mov .r15 (.reg .r9)]

/-- `u m` into the `w` words at `r8`, `u` in `rdx`, `m` at `r9`, `w` in
`rbp`; the carry into word `w` in `rcx`, and `r14 = w`. -/
def row : Prog isa := .seq (.block rowInit) (.loop (.block block) .ne)

/-- One row of the reduction. -/
def redcRow : Prog isa :=
  .seq (.block AdxSquare.redcHead) (.seq row (.seq (.block AdxSquare.redcTail) (.block Adx.rowEnd)))

/-- Montgomery reduction of the `2 w` words at `aAcc + 16`, for `w` a
positive multiple of 8. -/
def redc : Prog isa :=
  .seq (.block AdxSquare.redcSetup) (.seq (.loop redcRow .ne) (.block AdxSquare.redcFinish))

end VG.Impl.Bignum.X86_64.AdxRowRedc
