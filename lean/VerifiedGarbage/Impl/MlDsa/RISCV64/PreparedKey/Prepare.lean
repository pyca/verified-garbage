module

public import VerifiedGarbage.Impl.MlDsa.RISCV64.CacheCopy
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Arith
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Pack.Encode
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Whole
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on RISC-V: preparing keys

`vg_mldsa*_prepare_verifying_key(pk = a0, prepared = a1, scratch = a2)` and
`vg_mldsa*_prepare_signing_key(sk = a0, prepared = a1, scratch = a2)` copy the
encoded key to `prepared`, then for each of the key's polynomials (`t₁[i]`
for a public key; `s₁`, `s₂` and `t₀` for a private key, as `Sign/Sign.lean`
decodes them) decode it into a buffer, transform it with `vg_mldsa_ntt` (whose
working space is `scratch`) and copy it after the key, a byte at a time, since
`prepared` (bytes) need not be aligned.

The buffer is a frame of 1072 bytes on the stack (`withStackScratchWiped`,
which passes it in `a3` and zeroes it after the code): the polynomial at 0, and
our caller's `s8`–`s11` and the return address at 1024 (`oSV`). The code keeps
`scratch` in `s8`, `prepared` in `s9`, the key in `s10` and the buffer in
`s11`. Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlDsa.RISCV64.PreparedKey

open VG.RISCV64
open VG.Impl.MlDsa.RISCV64.KeyGen (Ptr Arg callAt seqR)
open VG.Impl.MlDsa.RISCV64.CacheCopy (copyN)
open VG.Impl.Ed25519.RISCV64.Whole (saveRegs restoreRegs)
open VG.Impl.Sha3.RISCV64.Stream (mov)
open VG.Spec.MlDsa (Params bitlen)

/-- Where our caller's registers are saved in the buffer. -/
def oSV : Nat := 1024

/-- The registers the code keeps, the buffer's last. -/
def keptRegs : List Reg := [.s8, .s9, .s10, .s11]

/-- The bytes of the buffer, and its doublewords. -/
def bufBytes : Nat := 1072
def bufWords : Nat := 134

/-- Our caller's registers saved, and the arguments moved to theirs. -/
def prepEnter : List Instr :=
  saveRegs .a3 oSV keptRegs ++ [mov .s8 .a2, mov .s9 .a1, mov .s10 .a0, mov .s11 .a3]

/-- The buffer's polynomial transformed, and copied to `off` of `prepared`. -/
def nttOut (off : Nat) : Prog isa :=
  .seq (callAt "vg_mldsa_ntt" Arith.ntt [(.a0, .ptr (.s11, 0)), (.a1, .ptr (.s8, 0))])
    (copyN (.s11, 0) (.s9, off) 1024)

/-- `NTT(t₁[i] · 2ᵈ)` after the public key. -/
def publicPoly (p : Params) (i : Nat) : Prog isa :=
  .seq (callAt "vg_mldsa_unpack_t1" Pack.unpackT1 [(.a0, .ptr (.s10, 32 + 320 * i)), (.a1, .ptr (.s11, 0))])
    (nttOut (p.pkLen + 1024 * i))

/-- The length of a polynomial of `s₁` or `s₂` in a private key. -/
def secretLen (p : Params) : Nat := 32 * bitlen (2 * p.η)

/-- The offset, length and bounds of polynomial `i` of `s₁ ‖ s₂ ‖ t₀` in a
private key. -/
def secretPiece (p : Params) (i : Nat) : Nat × Nat × Nat × Nat :=
  if i < p.ℓ + p.k then (128 + secretLen p * i, secretLen p, p.η, p.η)
  else (128 + secretLen p * (p.ℓ + p.k) + 416 * (i - p.ℓ - p.k), 416, 4095, 4096)

/-- `NTT` of polynomial `i` of `s₁ ‖ s₂ ‖ t₀` after the private key. -/
def secretPoly (p : Params) (i : Nat) : Prog isa :=
  .seq (callAt "vg_mldsa_bit_unpack" Pack.bitUnpack
      [(.a0, .ptr (.s10, (secretPiece p i).1)), (.a1, .imm (secretPiece p i).2.1),
        (.a2, .imm (secretPiece p i).2.2.1), (.a3, .imm (secretPiece p i).2.2.2), (.a4, .ptr (.s11, 0))])
    (nttOut (p.skLen + 1024 * i))

/-- The key's `len` bytes copied, its `n` polynomials `poly i`, and our
caller's registers restored. -/
def prepBody (len n : Nat) (poly : Nat → Prog isa) : Prog isa :=
  .seq (.block prepEnter) (.seq (copyN (.s10, 0) (.s9, 0) len)
    (.seq (seqR poly 0 n) (.block (restoreRegs .s11 oSV keptRegs))))

/-- `vg_mldsa*_prepare_verifying_key`. -/
def preparePublic (p : Params) : Prog isa :=
  Impl.StackScratch.RISCV64.withStackScratchWiped bufBytes .a3 bufWords (prepBody p.pkLen p.k (publicPoly p))

/-- `vg_mldsa*_prepare_signing_key`. -/
def prepareSecret (p : Params) : Prog isa :=
  Impl.StackScratch.RISCV64.withStackScratchWiped bufBytes .a3 bufWords
    (prepBody p.skLen (p.ℓ + 2 * p.k) (secretPoly p))

end VG.Impl.MlDsa.RISCV64.PreparedKey
