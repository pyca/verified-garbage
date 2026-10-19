module

public import VerifiedGarbage.Spec.Dsa.ModPow
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract

/-!
# The algebraic public-key checks shared by DSA signing and verification

**Trusted.** A helper checks the ranges and subgroup equations of a packed
public key after shape validation. It accumulates the result into an existing
32-bit mask and prepares the big-endian exponent `q - 2`. It neither tests
primality nor replaces the caller's shape checks.

The workspace already contains pointers into the packed key. Their offsets,
the mask and exponent offsets, and the allowed writes belong to the layout.
The helper preserves every other workspace byte. Addresses and lengths are
public; the key values and incoming mask do not affect the leakage trace.
-/

@[expose] public section
namespace VG.Spec.Dsa.PublicValidation
open VG.Spec.Rsa (bytesAt)
open VG.Spec.Dsa.ModPow (numAt Keeps rangesDoc)

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

/-- One component of the packed public key. -/
def component (m : Mem) (key : Addr) (offset len : Nat) : Nat :=
  decodeBE (bytesAt m (key + BitVec.ofNat 64 offset) len)

/-- Algebraic checks only; shape validation and domain assurance are separate. -/
def valid (p q g y : Nat) : Prop :=
  ((1 < g ∧ g < p) ∧ (1 < y ∧ y < p)) ∧ (p - 1) % q = 0 ∧
    g ^ q % p = 1 ∧ y ^ q % p = 1

instance (p q g y : Nat) : Decidable (valid p q g y) := by
  unfold valid
  infer_instance

/-- Writable workspace and a packed public key (trailing bytes are ignored). -/
def sig : Sig where
  params := [("ws", .slice true .u64 "ws_len"), ("key", .slice false .u8 "key_len")]

/-- Workspace capacity, installed pointers, and the domain assumptions. -/
def pre (L : Layout) (pointerBytes : Nat) (ws : Addr) (wsLen : Nat)
    (key : Addr) (keyLen : Nat) (m : Mem) : Prop :=
  let p := component m key 0 L.pLen
  let q := component m key L.pLen L.qLen
  L.size ≤ 8 * wsLen ∧ 3 * L.pLen + L.qLen ≤ keyLen ∧
  numAt m ws L.pPointer pointerBytes = key.toNat ∧
  numAt m ws L.qPointer pointerBytes = (key + BitVec.ofNat 64 L.pLen).toNat ∧
  numAt m ws L.gPointer pointerBytes = (key + BitVec.ofNat 64 (L.pLen + L.qLen)).toNat ∧
  numAt m ws L.yPointer pointerBytes = (key + BitVec.ofNat 64 (2 * L.pLen + L.qLen)).toNat ∧
  1 < p ∧ p % 2 = 1 ∧ 255 < q ∧ q % 2 = 1

/-- Accumulate the checks, prepare the inverse exponent, and preserve the frame. -/
def post (L : Layout) (ws : Addr) (wsLen : Nat) (key : Addr) (m m' : Mem) : Prop :=
  let p := component m key 0 L.pLen
  let q := component m key L.pLen L.qLen
  let g := component m key (L.pLen + L.qLen) L.pLen
  let y := component m key (2 * L.pLen + L.qLen) L.pLen
  numAt m' ws L.mask 4 = (if valid p q g y then numAt m ws L.mask 4 else 0) ∧
  component m' ws L.qMinusTwo L.qLen = q - 2 ∧
  Keeps ws wsLen L.scratch m m'

/-- Check the public components after shape validation, without assuming primality. -/
def contract {I : ISA} (L : Layout) (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws wsLen key keyLen m => pre L (A.ptrBits / 8) ws wsLen.toNat key keyLen.toNat m)
    (post := fun ws wsLen key _ m m' _ => post L ws wsLen.toNat key m m')
    (stack := stack)

def api (L : Layout) : Api where
  module := "dsa"
  name := s!"vg_dsa_public_validate_{L.pLen}_{L.qLen}"
  sig := sig
  contracts := some fun A stack => contract L A stack
  summary := s!"Checks the algebraic consistency of packed DSA public components of widths \
    {L.pLen}/{L.qLen} bytes. Keeps the 32-bit mask at workspace byte {L.mask} when all checks \
    pass, otherwise clears it; writes q-2 as {L.qLen} big-endian bytes at byte {L.qMinusTwo}. \
    Only workspace ranges {rangesDoc L.scratch} may change. This does not check primality \
    or supported bit lengths. Constant time with respect to key values and the incoming mask.\n\n\
    Contract: `VG.Spec.Dsa.PublicValidation.contract`."
  safety := [s!"The workspace must contain at least {L.size} bytes and the key at least \
      {3 * L.pLen + L.qLen} bytes, packed as p, q, g, y, big-endian.",
    s!"Native-width pointers at workspace offsets {L.pPointer}, {L.qPointer}, {L.gPointer}, \
      {L.yPointer} must address those four components respectively.",
    "p must be odd and above 1; q must be odd and above 255.",
    s!"Scratch ranges {rangesDoc L.scratch} may hold intermediate values after return."]

end VG.Spec.Dsa.PublicValidation
