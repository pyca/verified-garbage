module

public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Ntt
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Mul
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Dot
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.AddSub
public import VerifiedGarbage.Impl.MlDsa.X86_64.Round.Round
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejNtt4
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.ExpandMask4

/-!
# ML-DSA on x86-64: implementations of the polynomial arithmetic

Key generation, signing and verification call the polynomial arithmetic of
one implementation, a `Backend`: the code of `vg_mldsa_ntt`,
`vg_mldsa_inv_ntt`, `vg_mldsa_multiply_ntt`, `vg_mldsa_multiply_add_ntt`,
`vg_mldsa_add` and `vg_mldsa_sub`, of `vg_mldsa_high_bits`, `vg_mldsa_low_bits`,
`vg_mldsa_norm_lt`, `vg_mldsa_make_hint` and `vg_mldsa_use_hint`, and of `vg_mldsa_rej_ntt_poly4` and
`vg_mldsa_expand_mask_poly4` (which sample four polynomials at once), whose names end with `sfx` (e.g.
`_avx2`; nothing for the SSE2 code, `sse2`). Each is a variant of the
interface `MlDsaArith` on x86-64 (`Variants/MlDsaArith/X86_64/`), and the
functions that call them are emitted once for each
(`Generic/MlDsaArith/X86_64/`).
-/

@[expose] public section

namespace VG.Impl.MlDsa.X86_64.Arith

open VG.X86_64

/-- An implementation of the polynomial arithmetic. -/
structure Backend where
  ntt : Prog isa
  invNtt : Prog isa
  mul : Prog isa
  mulAdd : Prog isa
  add : Prog isa
  sub : Prog isa
  highBits : Prog isa
  lowBits : Prog isa
  normLt : Prog isa
  makeHint : Prog isa
  useHint : Prog isa
  rej4 : Prog isa
  expandMask4 : Prog isa
  /-- What the names of its functions, and of those calling them, end with. -/
  sfx : String
  /-- Whether products and the inverse transform use Montgomery scaling. -/
  montgomery : Bool := false
  /-- `vg_mldsa_dot_inverse4`, `5` and `7`: the inverse NTT of a row's sum of products. -/
  dotInv4 : Prog isa
  dotInv5 : Prog isa
  dotInv7 : Prog isa

/-- The SSE2 code. -/
def Backend.sse2 : Backend :=
  ⟨Arith.ntt, Arith.nttInv, Arith.mul, Arith.mulAdd, Arith.add, Arith.sub, Round.highBits,
    Round.lowBits, Round.normLt, Round.makeHint, Round.useHint, Sample.Rej4.rejNTT4,
    Sample.Mask4.expandMask4, "", false, dotInvSse2 4, dotInvSse2 5,
    dotInvSse2 7⟩

/-- `vg_mldsa_dot_inverse{c}`, for `c` of 4, 5 and 7. -/
abbrev Backend.dotInv (B : Backend) (c : Nat) : Prog isa :=
  if c = 4 then B.dotInv4 else if c = 5 then B.dotInv5 else B.dotInv7

/-- Every function empty, which the proofs that the functions calling a
backend never write `rsp` (and load MXCSR only to restore it) evaluate in
its place. -/
def Backend.empty : Backend :=
  ⟨.block [], .block [], .block [], .block [], .block [], .block [], .block [], .block [], .block [],
    .block [], .block [], .block [], .block [], "", false, .block [], .block [], .block []⟩

end VG.Impl.MlDsa.X86_64.Arith
