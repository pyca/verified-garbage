module

public import VerifiedGarbage.TCB.Artifact

/-! # X25519 byte access and ABI signatures

**Trusted.** Shared by the public contracts and the internal implementation
proofs; independent of the cryptographic specification.
-/

@[expose] public section

namespace VG.Spec.X25519

/-- The `n` bytes at `p`. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-- `vg_x25519_base(out: *mut [u8; 32], scalar: *const [u8; 32], scratch: *mut [u64; 1024])`.
`scratch` is working space. -/
def x25519BaseSig : Sig where
  params := [("out", .array true .u8 32), ("scalar", .array false .u8 32),
    ("scratch", .array true .u64 1024)]

/-- `vg_x25519_exchange(out: *mut [u8; 32], scalar: *const [u8; 32], point: *const [u8; 32], scratch: *mut [u64; 512]) -> u32`.
`scratch` is working space. -/
def exchangeSig : Sig where
  params := [("out", .array true .u8 32), ("scalar", .array false .u8 32),
    ("point", .array false .u8 32), ("scratch", .array true .u64 512)]
  ret := some .u32

end VG.Spec.X25519
