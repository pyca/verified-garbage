module

/-!
# The layouts of DSA's internal functions

The offsets in a working space at which DSA's internal functions (the
exponentiation `vg_dsa_pow_{n}_{e}`, the reduction and product
`vg_dsa_reduce_{n}` and `vg_dsa_mulmod_{n}`, the Montgomery context
`vg_dsa_context_{n}`, the probable-prime test `vg_dsa_probable_prime_{bits}`,
the public-key checks `vg_dsa_public_validate_{p}_{q}`, the generator stage
`vg_dsa_generator_{bits}` and the fixed-base comb) find their numbers, which
each target's code fixes, and their contracts, `Proof/Dsa/*Contract.lean`, take.
-/

@[expose] public section

namespace VG.Impl.Dsa.ModPow

/-- The widths and byte offsets of an exponentiation in its working space. -/
structure Layout where
  /-- The 64-bit words of the modulus, the base and the result. -/
  n : Nat
  /-- The 32-bit words of the exponent. -/
  e : Nat
  /-- Byte offsets in the working space. -/
  modulus : Nat
  base : Nat
  exponent : Nat
  result : Nat
  /-- The ranges `(offset, bytes)` of the working space that the function
  may change, the result's among them. -/
  scratch : List (Nat × Nat)
  /-- The bytes of the working space that the function uses. -/
  size : Nat

end VG.Impl.Dsa.ModPow

namespace VG.Impl.Dsa.ModArith

/-- The width and byte offsets of a reduction in its working space. -/
structure ReduceLayout where
  /-- The 64-bit words of the modulus and the result. -/
  n : Nat
  /-- Byte offsets in the working space. -/
  modulus : Nat
  result : Nat
  /-- The ranges `(offset, bytes)` of the working space that the function
  may change, the result's among them. -/
  scratch : List (Nat × Nat)
  /-- The bytes of the working space that the function uses. -/
  size : Nat

/-- The width and byte offsets of a product in its working space. -/
structure MulLayout where
  /-- The 64-bit words of the modulus, the operands and the result. -/
  n : Nat
  /-- Byte offsets in the working space. -/
  modulus : Nat
  a : Nat
  b : Nat
  result : Nat
  /-- The ranges `(offset, bytes)` of the working space that the function
  may change, the result's among them. -/
  scratch : List (Nat × Nat)
  /-- The bytes of the working space that the function uses. -/
  size : Nat

end VG.Impl.Dsa.ModArith

namespace VG.Impl.Dsa.MontContext

structure Layout where
  /-- The modulus's width in 64-bit words. -/
  n : Nat
  modulus : Nat
  inverse : Nat
  one : Nat
  rSquared : Nat
  /-- Output ranges and other bytes the function may change. -/
  scratch : List (Nat × Nat)
  size : Nat

end VG.Impl.Dsa.MontContext

namespace VG.Impl.Dsa.ProbablePrime

/-- The width and byte offsets of a test in its working space. -/
structure Layout where
  /-- The candidate's exact bit length, a multiple of 8. -/
  bits : Nat
  /-- The byte offset of the candidate's `bits / 8` big-endian bytes in the
  working space. -/
  candidate : Nat
  /-- The ranges `(offset, bytes)` of the working space that the function
  may change. -/
  scratch : List (Nat × Nat)
  /-- The bytes of the working space that the function uses. -/
  size : Nat

end VG.Impl.Dsa.ProbablePrime

namespace VG.Impl.Dsa.PublicValidation

structure Layout where
  /-- Widths of the packed big-endian components, in bytes. -/
  pLen : Nat
  qLen : Nat
  /-- Workspace offsets of native-width little-endian pointers. -/
  pPointer : Nat
  qPointer : Nat
  gPointer : Nat
  yPointer : Nat
  /-- Workspace offsets of the 32-bit mask and big-endian `q - 2`. -/
  mask : Nat
  qMinusTwo : Nat
  /-- Allowed write ranges, and minimum workspace capacity in bytes. -/
  scratch : List (Nat × Nat)
  size : Nat

end VG.Impl.Dsa.PublicValidation

namespace VG.Impl.Dsa.GeneratorStage

/-- The sizes and byte offsets of the stage in its working space. -/
structure Layout where
  /-- The bytes of p and g. -/
  pLen : Nat
  /-- The bytes of q. -/
  qLen : Nat
  /-- The offset of p's `pLen` big-endian bytes. -/
  p : Nat
  /-- The offset of q's `qLen` big-endian bytes. -/
  q : Nat
  /-- The offset of the exponent (p − 1) / q's `pLen` big-endian bytes. -/
  exponent : Nat
  /-- The offset of the `2 * pLen + qLen` bytes p ‖ q ‖ g written on success. -/
  packed : Nat
  /-- The ranges `(offset, bytes)` of the working space that the function
  may change. -/
  scratch : List (Nat × Nat)
  /-- The bytes of the working space that the function uses. -/
  size : Nat

end VG.Impl.Dsa.GeneratorStage

namespace VG.Impl.Dsa.FixedBaseComb

/-- Arithmetic offsets and scratch ranges use the existing DSA power layout.
The context is a separate range in the same working space. -/
structure Layout extends VG.Impl.Dsa.ModPow.Layout where
  context : Nat

end VG.Impl.Dsa.FixedBaseComb
