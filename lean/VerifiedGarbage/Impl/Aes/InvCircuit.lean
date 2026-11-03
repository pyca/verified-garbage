module

-- separate module: the other targets' AES proofs import `Circuit.lean`, and a circuit only RISC-V uses need not rebuild them

public import VerifiedGarbage.Impl.Aes.Circuit

/-!
# The AES inverse S-box as a Boolean circuit

The inverse S-box is `inv ∘ aff⁻¹`, and `Circuit.sbox` is `aff ∘ inv`
with `inv` in its non-linear section (`middle`), so `aff⁻¹` folds into the
circuit's two linear sections, with no gate of its own:

* `invTop` computes the signals `y₁ … y₂₁` (and `y₀`, which `invMiddle`
  reads where `middle` reads `x₇`) that `top` computes from
  `aff⁻¹(x)`, from `x`; its XNORs add `aff⁻¹`'s constant.
* `invBottom` computes `aff⁻¹` of `bottom`'s output from `z₀ … z₁₇`;
  `bottom`'s constant and `aff⁻¹`'s cancel (`aff⁻¹({63}) = 0`).

Both are straight-line programs found by Boyar and Peralta's heuristic
(SEA 2010, as cited in `Circuit.lean`) for the linear maps: 23 gates
(4 XNORs) and 30, where `aff⁻¹ ∘ sbox ∘ aff⁻¹` takes 23 and 30 (4 XNORs)
and the two `aff⁻¹` on every byte. Each target's proof checks the code
made from it on all 256 inputs (e.g. `Proof/Aes/RISCV64/Decrypt.lean`);
nothing here needs to be trusted.
-/

@[expose] public section

namespace VG.Impl.Aes.Circuit

/-- Variables of the linear sections' other signals. -/
def w (i : Nat) : Nat := 124 + i

/-- The top linear transformation of `aff⁻¹`'s output, from its input. -/
def invTop : List Gate := [
  xor (y 3) (x 0) (x 3), xnor (y 6) (x 1) (y 3), xor (y 9) (x 3) (x 4), xnor (y 18) (x 2) (y 9),
  xor (y 8) (x 3) (y 6), xor (y 14) (x 4) (y 6), xor (y 5) (y 3) (y 8), xnor (y 19) (x 4) (x 7),
  xor (y 10) (y 8) (y 19), xor (y 1) (x 3) (y 19), xnor (y 13) (x 6) (y 1),
  xor (y 12) (y 14) (y 13), xor (y 4) (y 3) (y 12), xor (y 2) (y 5) (y 13), xor (y 7) (y 18) (y 2),
  xor (y 16) (y 1) (y 7), xor (y 21) (y 13) (y 16), xor (w 0) (x 0) (x 5), xor (y 11) (y 4) (w 0),
  xor (y 20) (y 9) (y 11), xor (y 0) (y 7) (y 11), xor (y 17) (y 10) (y 11),
  xor (y 15) (y 16) (y 17)]

/-- `middle`, reading `y₀` for `x₇`. -/
def invMiddle : List Gate :=
  middle.map fun g => { g with
    a := if g.a = x 7 then y 0 else g.a, b := if g.b = x 7 then y 0 else g.b }

/-- `aff⁻¹` of the bottom linear transformation. -/
def invBottom : List Gate := [
  xor (w 1) (z 6) (z 15), xor (w 2) (z 12) (w 1), xor (w 3) (z 13) (w 2), xor (w 4) (z 16) (w 3),
  xor (w 5) (z 8) (w 4), xor (w 6) (z 3) (w 5), xor (s 0) (z 5) (w 6), xor (w 7) (z 4) (w 6),
  xor (w 8) (z 1) (w 7), xor (w 9) (z 2) (z 10), xor (w 10) (z 0) (w 5), xor (s 3) (z 2) (w 10),
  xor (w 11) (z 9) (z 17), xor (w 12) (w 8) (w 9), xor (w 13) (z 14) (w 12),
  xor (w 14) (z 7) (w 7), xor (s 6) (z 8) (w 14), xor (w 15) (s 0) (w 10), xor (s 5) (w 8) (w 15),
  xor (w 16) (z 11) (w 11), xor (s 7) (z 15) (w 16), xor (w 17) (z 11) (w 13),
  xor (s 2) (z 13) (w 17), xor (w 18) (z 16) (w 16), xor (w 19) (z 12) (w 17),
  xor (s 1) (w 18) (w 19), xor (w 20) (z 9) (w 9), xor (w 21) (s 6) (w 18),
  xor (w 22) (w 15) (w 21), xor (s 4) (w 20) (w 22)]

def invSbox : List Gate := invTop ++ invMiddle ++ invBottom

end VG.Impl.Aes.Circuit
