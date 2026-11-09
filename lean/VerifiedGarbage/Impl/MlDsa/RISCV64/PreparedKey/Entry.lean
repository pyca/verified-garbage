module

public import VerifiedGarbage.Impl.MlDsa.RISCV64.KeyGen.Frag
public import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on RISC-V: the entries of the kernels with a cache

Signing and verification of `μ` are one kernel each per parameter set
(`vg_mldsa*_sign_with_cache`, `vg_mldsa*_verify_with_cache`, `Sign/Sign.lean`,
`Verify/Verify.lean`), which take a cache of the key's polynomials after their
arguments, a pointer in `cp` and its length in `cl`. The entries
(`vg_mldsa*_sign`, `vg_mldsa*_verify` and, for a prepared key,
`vg_mldsa*_sign_prepared`, `vg_mldsa*_verify_prepared`) call them with their
own arguments: with an empty cache (`cp ← a0`, `cl ← 0`), or with the
`len` bytes at `off` of the prepared key in `a0` (`cp ← a0 + off`,
`cl ← len`). The call overwrites our return address, so a frame of 16 bytes
keeps it.
-/

@[expose] public section

namespace VG.Impl.MlDsa.RISCV64.PreparedKey

open VG.RISCV64
open VG.Impl.MlDsa.RISCV64.KeyGen (Arg)
open VG.Impl.Sha3.RISCV64.Stream (mov)

/-- The cache's pointer into `cp` and its length into `cl`. -/
def cacheArgs (cp cl : Reg) (off len : Nat) : Bool → List Instr
  | true => Arg.instrs cp (.ptr (.a0, off)) ++ Arith.loadImm cl len
  | false => [mov cp .a0, .li cl 0]

/-- The call of the kernel `kernel`, named `name`, with the cache's arguments. -/
def entry (name : String) (kernel : Prog isa) (cp cl : Reg) (off len : Nat) (prepared : Bool) : Prog isa :=
  .frame (.push .ra) (.seq (.block (cacheArgs cp cl off len prepared)) (.call name kernel)) (.pop .ra)

/-- The length of a private key's cache: `ℓ + 2k` polynomials. -/
abbrev sCacheBytes (p : Spec.MlDsa.Params) : Nat := 1024 * (p.ℓ + 2 * p.k)

/-- The length of a public key's cache: `k` polynomials. -/
abbrev vCacheBytes (p : Spec.MlDsa.Params) : Nat := 1024 * p.k

/-- `vg_mldsa*_sign` (`q` false) and `vg_mldsa*_sign_prepared` (`q` true):
`sign(sk = a0, mu = a1, rnd = a2, sig = a3, scratch = a4)` calls the kernel
with the cache in `a5` and `a6`. -/
def signEntry (p : Spec.MlDsa.Params) (name : String) (kernel : Prog isa) (q : Bool) : Prog isa :=
  entry name kernel .a5 .a6 p.skLen (sCacheBytes p) q

/-- `vg_mldsa*_verify` (`q` false) and `vg_mldsa*_verify_prepared` (`q`
true): `verify(pk = a0, mu = a1, sig = a2, scratch = a3)` calls the kernel
with the cache in `a4` and `a5`. -/
def verifyEntry (p : Spec.MlDsa.Params) (name : String) (kernel : Prog isa) (q : Bool) : Prog isa :=
  entry name kernel .a4 .a5 p.pkLen (vCacheBytes p) q

end VG.Impl.MlDsa.RISCV64.PreparedKey
