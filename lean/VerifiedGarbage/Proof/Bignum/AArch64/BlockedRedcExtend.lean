module

public import Mathlib.Tactic.SplitIfs
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64

/-- A row touches only its low k+1 blocks. The unvisited high product blocks
can be reattached to its exact arithmetic relation. -/
theorem extend_row_value {m m' : Mem} {B : Addr} {e k n q modulus p p' : Nat}
    (hk : k + 1 ≤ n) (hn : e + 64 * n ≤ 2 ^ 64)
    (ho : Outside B e (64 * (k + 1)) m m')
    (hv : (2 ^ 64) ^ 8 * (wv m' B (e + 64) (8 * k) + 2 ^ (64 * (8 * k)) * p') =
      wv m B e (8 * (k + 1)) + q * modulus + 2 ^ (64 * (8 * k)) * p) :
    (2 ^ 64) ^ 8 * (wv m' B (e + 64) (8 * (n - 1)) + 2 ^ (64 * (8 * k)) * p') =
      wv m B e (8 * n) + q * modulus + 2 ^ (64 * (8 * k)) * p := by
  have htail := ho.wv (d := e + 64 * (k + 1)) (k := 8 * (n - (k + 1)))
    (by omega) (by omega)
  have hOld := wv_add m B e (8 * (k + 1)) (8 * (n - (k + 1)))
  rewrite [show 8 * (k + 1) + 8 * (n - (k + 1)) = 8 * n by omega,
    show e + 8 * (8 * (k + 1)) = e + 64 * (k + 1) by omega,
    pow_blocks_succ] at hOld
  have hNew := wv_add m' B (e + 64) (8 * k) (8 * (n - (k + 1)))
  rewrite [show 8 * k + 8 * (n - (k + 1)) = 8 * (n - 1) by omega,
    show e + 64 + 8 * (8 * k) = e + 64 * (k + 1) by omega, htail] at hNew
  rewrite [hOld, hNew]
  exact row_extend hv

end VG.Proof.Bignum.AArch64.BlockedRedc
