module

public import VerifiedGarbage.Impl.MlKem.X86_64.Kpke16
public import VerifiedGarbage.Impl.MlKem.X86_64.KeyGen
public import VerifiedGarbage.Impl.MlKem.X86_64.Encaps
public import VerifiedGarbage.Impl.MlKem.X86_64.Decaps
public import VerifiedGarbage.Impl.MlKem.X86_64.Frag16

/-!
# ML-KEM on x86-64: the layout of the top-level functions with 16-bit polynomials

With AVX2, key generation, encapsulation and decapsulation keep their
polynomials as `u16`s and run K-PKE in one call (`Kpke16.lean`). They keep
the layout of the first 4096 bytes of `scratch` (`Frag.lean`), and beyond
it (`Kem16`): the `k²` polynomials of `Â` from `oA` (512 bytes each), those
sampled with `SamplePolyCBD` (`s ‖ e`, or `y ‖ e₁ ‖ e₂`) from `oR`, and the
working space of the K-PKE function from `oZ`. While `Â` and the others are
sampled, the same bytes from `oZ` hold the working space of the samplers and
of `prfs` (from `oW`) and the outputs of `PRF₂` (from `oPR`).
Decapsulation's re-encryption writes `c'` to the working space of the
primitives (`oCT16`), which these functions do not call.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- Where the top-level functions with 16-bit polynomials keep them. -/
structure Kem16 where
  L : Kem
  oA : Nat
  oR : Nat
  oZ : Nat
  oW : Nat
  oPR : Nat

/-- `c'` of decapsulation's re-encryption. -/
def oCT16 : Nat := oSS

namespace Top16

variable (K : Kem16)

/-- Entry `e` of `Â`. -/
abbrev aP (e : Nat) : Ptr := sc (K.oA + 512 * e)
/-- `PRF₂(σ, N)`, and polynomial `N` of `s ‖ e` (or `y ‖ e₁ ‖ e₂`). -/
abbrev prfO (N : Nat) : Ptr := sc (K.oPR + 128 * N)
abbrev rP (N : Nat) : Ptr := sc (K.oR + 512 * N)

/-- The `k²` entries of `Â`, with the samplers `p` (an implementation's `Callee4.s16`). -/
def mat (p : String × Prog isa) : Prog isa := samples16 p K.L.k K.oA (sc K.oW)

/-- `SamplePolyCBD₂(PRF₂(σ, N))` to polynomial `N`. -/
def cbdN (A : Arith) (N : Nat) : Prog isa := cbd2_16At A (prfO K N) (rP K N)

/-- The `n` outputs of `PRF₂` and the polynomials sampled from them. -/
def noise (c : Callee4) (n : Nat) : Prog isa :=
  .seq (c.prfs 0 n K.oPR (K.oW / 32)) (seqR (cbdN K c.arith) 0 n)

/-- `ŝ`, `t̂` encoded to the keys, and the keys' last pieces. -/
def kgTail : Prog isa :=
  .seq (K.L.kpkeKgAt (.r12, 0) (.r13, 0) (sc K.oA) (sc K.oR) (sc K.oZ)) (KeyGen.fin K.L)

/-- Key generation after `Â`, if every `SampleNTT` succeeded. -/
def kgRest (c : Callee4) : Prog isa := .seq (noise K c (2 * K.L.k)) (kgTail K)

end Top16

open KeyGen Top16 in
/-- The key generation of the parameter set of `K`, with 16-bit polynomials,
with the samplers `p` and the rest of the implementation `c`. -/
def kemKeyGen16 (K : Kem16) (c : Callee4) (p : String × Prog isa) : Prog isa :=
  .seq (.block pro) (.seq (gRho K.L) (.seq (mat K p) (.seq (ifOk (kgRest K c)) (.block topEpi))))

/-- ML-KEM-768's layout: `Â` 4608 bytes from 4096, the others (at most
3584 bytes) from 8704, and the K-PKE functions' working space (20480 bytes)
from 12288, the end of `scratch`. -/
def kem768w : Kem16 where
  L := kem768
  oA := 4096
  oR := 8704
  oZ := 12288
  oW := 12288
  oPR := 20480

end VG.Impl.MlKem.X86_64
