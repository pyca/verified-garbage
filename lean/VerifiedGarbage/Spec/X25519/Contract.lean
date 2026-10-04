import VerifiedGarbage.Spec.X25519
import VerifiedGarbage.TCB.Artifact

/-!
# X25519: the contract, on every target

**Trusted** (as every file in `Spec/`). The contract of `vg_x25519`, in
terms of `Spec/X25519.lean`, for any target: `A` is the target's calling
convention. The signature fixes where the arguments are, the memory the
function may access, disjointness, and that the pointers are public (see
`TCB/Sig.lean`); the contract adds the rest. The scalar and the
u-coordinate are secret (the u-coordinate is usually a public key, but the
function does not rely on it).

The function takes 4 KiB of working space (`scratch`), which it leaves
unspecified, since the ladder's variables do not fit in the registers of any
target.

`vg_x25519_base` computes the same function for the base point `u = 9`
alone (`basePoint`), which RFC 7748 §6.1 uses to derive public keys; it
takes no u-coordinate, so an implementation may use another algorithm for
it (for example a fixed-base multiplication on the birationally equivalent
Edwards curve), and 8 KiB of working space.

The contract takes the number of bytes of stack below the stack pointer that
an implementation's calls and frames use (`stack`, see `Sig.contract`), 0
for one that uses none.
-/

namespace VG.Spec.X25519

/-- The `n` bytes at `p`. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-- `vg_x25519(out: *mut [u8; 32], scalar: *const [u8; 32], point: *const [u8; 32], scratch: *mut [u64; 512])`.
`scratch` is working space. -/
def x25519Sig : Sig where
  params := [("out", .array true .u8 32), ("scalar", .array false .u8 32),
    ("point", .array false .u8 32), ("scratch", .array true .u64 512)]

/-- Writes `X25519(k, u)` to `out`, for the 32-byte scalar `k` at `scalar`
and the 32-byte u-coordinate `u` at `point`. -/
def x25519Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  x25519Sig.contract A (post := fun out scalar point _scratch m m' _ =>
    bytesAt m' out 32 = x25519 (bytesAt m scalar 32) (bytesAt m point 32))
    (stack := stack)

/-- `vg_x25519` on every target. -/
def x25519Api : Api where
  module := "x25519"
  name := "vg_x25519"
  sig := x25519Sig
  contracts := some fun A stack => x25519Contract A stack
  summary := "Computes X25519 (RFC 7748 §5): writes `X25519(k, u)` to `*out`, for the 32-byte \
    scalar `k` at `scalar` and the 32-byte u-coordinate `u` at `point`. The scalar is decoded \
    (clamped) and the most significant bit of `u` masked as RFC 7748 specifies; the result may \
    be all zero (for a `u` of small order), which the caller must check for if its protocol \
    requires it (RFC 7748 §6.1).\n\n\
    Contract: `VG.Spec.X25519.x25519Contract`. Constant time: only the pointers may affect \
    timing, not the scalar or the u-coordinate."
  safety := ["The contents of `scratch` on return are unspecified."]

/-- `vg_x25519_base(out: *mut [u8; 32], scalar: *const [u8; 32], scratch: *mut [u64; 1024])`.
`scratch` is working space. -/
def x25519BaseSig : Sig where
  params := [("out", .array true .u8 32), ("scalar", .array false .u8 32),
    ("scratch", .array true .u64 1024)]

/-- Writes `X25519(k, 9)` to `out`, for the 32-byte scalar `k` at `scalar`. -/
def x25519BaseContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  x25519BaseSig.contract A (post := fun out scalar _scratch m m' _ =>
    bytesAt m' out 32 = x25519 (bytesAt m scalar 32) basePoint)
    (stack := stack)

/-- `vg_x25519_base` on every target. -/
def x25519BaseApi : Api where
  module := "x25519"
  name := "vg_x25519_base"
  sig := x25519BaseSig
  contracts := some fun A stack => x25519BaseContract A stack
  summary := "Computes X25519 (RFC 7748 §5) of the base point: writes `X25519(k, 9)`, the \
    public key of RFC 7748 §6.1, to `*out`, for the 32-byte scalar `k` at `scalar`, which is \
    decoded (clamped) as RFC 7748 specifies.\n\n\
    Contract: `VG.Spec.X25519.x25519BaseContract`. Constant time: only the pointers may affect \
    timing, not the scalar."
  safety := ["The contents of `scratch` on return are unspecified and may contain secrets; the \
    caller must destroy them after use."]

end VG.Spec.X25519
