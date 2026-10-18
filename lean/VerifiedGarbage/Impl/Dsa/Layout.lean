module

/-!
# DSA's internal working-space layout

The outer workspace has 48 limbs, matching RSA's exponentiation context.
Its arrays are used only for the DSA call's saved arguments; the arithmetic
runs in the p and q child workspaces. Both child workspaces include a
sixteen-entry exponentiation table. Computed scalars and exponents are in
the suffix, outside the active arithmetic prefix.

The layout fits in 16384 bytes, the minimum scratch allocation permitted
by the DSA contracts, including when the caller supplies padded parameters.
-/

@[expose] public section

namespace VG.Impl.Dsa.Layout

def outerWords : Nat := 48
def pWorkspace : Nat := 3456
def qWorkspace : Nat := 13312
def activeBytes : Nat := 14720

def r : Nat := 14720
def s : Nat := 14752
def inverse : Nat := 14784
def u : Nat := 14816
def v : Nat := 14848
def z : Nat := 14880
def qMinusTwo : Nat := 14912
def t : Nat := 14944
def t2 : Nat := 15328
def usedBytes : Nat := 15712

/-- Key derivation's public value, just past the signer's layout: its
checks read y as they read a caller's input, which lies outside it. It
ends by 16384 bytes for p_len = 128, and the minimum scratch grows with p. -/
def derivedY : Nat := usedBytes

/-- Slots of the outer header used to call an arithmetic routine. -/
def arg : Nat := 16
def argLen : Nat := 17
def arg2 : Nat := 18
def arg2Len : Nat := 19
def result : Nat := 20
def resultLen : Nat := 21

/-- Byte offsets of saved arguments, within the unused outer arrays. -/
inductive Field where
  | p | q | g | y | x | signature | nonce | digest | out
  | pLen | qLen | digestLen | digestPrefixLen | mask
  deriving DecidableEq, Repr

def Field.offset : Field → Nat
  | .p => 256 | .q => 264 | .g => 272 | .y => 280 | .x => 288
  | .signature => 296 | .nonce => 304 | .digest => 312 | .out => 320
  | .pLen => 328 | .qLen => 336 | .digestLen => 344 | .digestPrefixLen => 352 | .mask => 360

/-- An arithmetic operand, either caller bytes or a computed scratch value. -/
inductive Pointer where
  | input (field : Field)
  | local (offset : Nat)
  | signatureS
  deriving DecidableEq, Repr

structure Operand where
  pointer : Pointer
  length : Field
  deriving DecidableEq, Repr

end VG.Impl.Dsa.Layout
