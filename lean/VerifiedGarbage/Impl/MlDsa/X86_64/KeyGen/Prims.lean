module
public import VerifiedGarbage.TCB.X86_64.Isa


/-!
# ML-DSA on x86-64: the primitives key generation calls

`vg_mldsa*_keygen` is a sequence of calls of ML-DSA's polynomial
primitives (`Proof/MlDsa/Contract.lean`) and of the SHA-3 sponge functions. Its
code is written for any implementations of the primitives, given as a
`Prims`: the code of each primitive it calls, which it calls by the name of
the artifact that has that code.
-/

@[expose] public section

namespace VG.Impl.MlDsa.X86_64.KeyGen

open VG.X86_64

/-- The code of the primitives key generation calls. -/
structure Prims where
  /-- `vg_mldsa_ntt` -/
  ntt : Prog isa
  /-- `vg_mldsa_add` -/
  add : Prog isa
  /-- `vg_mldsa_rej_ntt_poly` -/
  rejNtt : Prog isa
  /-- `vg_mldsa_rej_bounded_poly` -/
  rejBounded : Prog isa
  /-- `vg_mldsa_power2round` -/
  power2Round : Prog isa
  /-- `vg_mldsa_simple_bit_pack` -/
  simpleBitPack : Prog isa
  /-- `vg_mldsa_bit_pack` -/
  bitPack : Prog isa
  /-- `vg_mldsa_rej_ntt_poly4` -/
  rej4 : Prog isa
  /-- `vg_mldsa_dot_inverse4`, `5` and `7`: `NTT⁻¹` of a row's sum of products -/
  dotInv4 : Prog isa
  dotInv5 : Prog isa
  dotInv7 : Prog isa
  /-- What the names of the polynomial arithmetic's functions end with (`Arith.Backend`). -/
  sfx : String := ""

/-- `vg_mldsa_dot_inverse{c}`, for `c` of 4, 5 and 7. -/
abbrev Prims.dotInv (P : Prims) (c : Nat) : Prog isa :=
  if c = 4 then P.dotInv4 else if c = 5 then P.dotInv5 else P.dotInv7

end VG.Impl.MlDsa.X86_64.KeyGen
