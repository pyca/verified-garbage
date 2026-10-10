import VerifiedGarbage.Proof.Framework.Bitslice.Lanes

/-!
# Input words of atoms, as one shifted diagonal

The lane domain's input word `i` of `w` bits has atom `w i + t` at bit `t`
(`mk w (fun t => [w * i + t]) w`). Built that way, the kernel evaluates `w`
XORs of numbers as large as the result for every word. `inWordW` is word
`0`'s lanes (`diagW w w`, computed once) shifted to word `i`'s, and
`inWordW_eq_mk` says it is the same number. `Atoms.lean` and the ISAs'
own words of atoms (`Framework/Arm/Linear.lean`) use it.
-/

namespace VG.Bitslice

/-- The lanes of atoms `0 … n - 1` of word `0`, atom `t` at position `t`:
bits `(w + 1) t`. -/
def diagW (w : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => diagW w n ^^^ (2 ^ ((w + 1) * n))

/-- Input word `i` of `w` bits: bit `t` is atom `w i + t`. Word `0`'s lanes
shifted to word `i`'s, so the kernel evaluates one shift of a `w (w + 1)`-bit
number rather than `w` XORs of numbers as large as the result
(`inWordW_eq_mk`). -/
def inWordW (w i : Nat) : Nat × Nat := (0, diagW w w <<< (w * w * i))

theorem diagW_shift (w i : Nat) : ∀ n, diagW w n <<< (w * w * i) = mk w (fun t => [w * i + t]) n
  | 0 => by simp [diagW, mk]
  | n + 1 => by
    rw [diagW, mk, Nat.shiftLeft_xor_distrib, diagW_shift w i n, atomsAt, atomsAt, Nat.xor_zero,
      Nat.shiftLeft_eq, ← Nat.pow_add]
    have e : (w + 1) * n + w * w * i = w * (w * i + n) + n := by
      rw [Nat.mul_add w, ← Nat.mul_assoc, Nat.succ_mul]; omega
    rw [e]

theorem inWordW_eq_mk (w i : Nat) : inWordW w i = (0, mk w (fun t => [w * i + t]) w) := by
  rw [inWordW, diagW_shift]

end VG.Bitslice
