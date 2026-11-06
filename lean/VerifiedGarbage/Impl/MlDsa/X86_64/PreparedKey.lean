module

public import VerifiedGarbage.Impl.MlDsa.X86_64.Verify.Frag
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sign.Frag
public import VerifiedGarbage.Spec.MlDsa.PreparedKey

/-!
# ML-DSA on x86-64: `vg_mldsa*_prepare_verifying_key`, `vg_mldsa*_prepare_signing_key`

`prepare(key = rdi, prepared = rsi, scratch = rdx)`: the encoded key (`len`
bytes) and, after it, the NTTs of its `m` polynomials, each decoded from the
key by `unpack i` to its slot and transformed in place. The function saves its
caller's callee-saved registers in `scratch` at 840, and keeps `prepared` in
`rbx`, `key` in `rbp` and `scratch` in `r12`. The NTT's working space is the
first KiB of `prepared`, which the copy of the encoded key, last, overwrites.
Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlDsa.X86_64.PreparedKey

open VG.X86_64
open VG.Impl.MlKem.X86_64 (at_)
open VG.Impl.MlDsa.X86_64.Verify (Ptr Prims callAt unpackT1At bitUnpackAt savedRegs oSV)
open VG.Spec.MlDsa

/-- Save the callee-saved registers in `scratch` at 840; `rbx = prepared`,
`rbp = key`, `r12 = r13 = scratch`. -/
def pro : List Instr :=
  (List.range 6).map (fun k => .store (at_ .rdx (oSV + 8 * k)) (savedRegs.getD k .rbx)) ++
    ([.mov .rbx (.reg .rsi), .mov .rbp (.reg .rdi), .mov .r12 (.reg .rdx), .mov .r13 (.reg .rdx)] : List Instr)

/-- Restore the callee-saved registers (`r12` last). -/
def epi : List Instr :=
  [.mov .rbx (.mem (at_ .r12 oSV)), .mov .rbp (.mem (at_ .r12 (oSV + 8))), .mov .r13 (.mem (at_ .r12 (oSV + 24))),
    .mov .r14 (.mem (at_ .r12 (oSV + 32))), .mov .r15 (.mem (at_ .r12 (oSV + 40))),
    .mov .r12 (.mem (at_ .r12 (oSV + 16)))]

/-- The slot of polynomial `i`, after the `len` bytes of the encoded key. -/
abbrev slot (len i : Nat) : Ptr := (.rbx, len + 1024 * i)

/-- The NTT of the polynomial at `f`, with the first KiB of `prepared` as working space. -/
def nttAt (P : Prims) (f : Ptr) : Prog isa :=
  callAt ("vg_mldsa_ntt" ++ P.sfx) P.ntt [(.rdi, .ptr f), (.rsi, .ptr (.rbx, 0))]

/-- The key of `len` bytes and the NTTs of its `m` polynomials. -/
def prepare (P : Prims) (len m : Nat) (unpack : Nat → Prog isa) : Prog isa :=
  .seq (.block pro) (.seq (Verify.seqR (fun i => .seq (unpack i) (nttAt P (slot len i))) 0 m)
    (.seq (Impl.MlDsa.X86_64.Sign.copy (.rbx, 0) (.rbp, 0) len) (.block epi)))

/-- `t₁[i] · 2ᵈ`, from its 320 bytes in the public key. -/
def publicUnpack (P : Prims) (p : Params) (i : Nat) : Prog isa := unpackT1At P (.rbp, 32 + 320 * i) (slot p.pkLen i)

/-- The length of a packed polynomial of `s₁` or `s₂`. -/
def secretLen (p : Params) : Nat := 32 * bitlen (2 * p.η)

/-- Where polynomial `i` of `s₁ ‖ s₂ ‖ t₀` is in the private key, its length, and the bounds of its coefficients. -/
def secretPiece (p : Params) (i : Nat) : Nat × Nat × Nat × Nat :=
  if i < p.ℓ + p.k then (128 + secretLen p * i, secretLen p, p.η, p.η)
  else (128 + secretLen p * (p.ℓ + p.k) + 416 * (i - p.ℓ - p.k), 416, 4095, 4096)

/-- Polynomial `i` of `s₁ ‖ s₂ ‖ t₀`, from the private key. -/
def secretUnpack (P : Prims) (p : Params) (i : Nat) : Prog isa :=
  bitUnpackAt P (.rbp, (secretPiece p i).1) (secretPiece p i).2.1 (secretPiece p i).2.2.1 (secretPiece p i).2.2.2
    (slot p.skLen i)

/-- `vg_mldsa*_prepare_verifying_key`. -/
def preparePublic (P : Prims) (p : Params) : Prog isa := prepare P p.pkLen p.k (publicUnpack P p)

/-- `vg_mldsa*_prepare_signing_key`. -/
def prepareSecret (P : Prims) (p : Params) : Prog isa := prepare P p.skLen (p.ℓ + 2 * p.k) (secretUnpack P p)

end VG.Impl.MlDsa.X86_64.PreparedKey
