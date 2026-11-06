module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.MlDsa.Round.Decompose
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
meta import VerifiedGarbage.Proof.MlDsa.Round.Decompose
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# ML-DSA on AArch64: `vg_mldsa_power2round`
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Round

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Round VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Arith (Qv toNat_setWidth64 q32 movW_ok)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa

/-- A value `v` plus `q` if it is negative (as a 64-bit number). -/
abbrev addQ (v : BitVec 64) : BitVec 64 := v + (v >>> 63) * Qv

/-- `a + 4095`, in 64 bits. -/
abbrev p2rX (x : BitVec 32) : BitVec 64 := x.setWidth 64 + BitVec.ofNat 64 4095

/-- The `t1` the body stores. -/
def t1V (x : BitVec 32) : BitVec 32 := (p2rX x >>> 13).setWidth 32

/-- The `t0` the body stores. -/
def t0V (x : BitVec 32) : BitVec 32 :=
  (addQ (p2rX x - (p2rX x >>> 13) <<< 13 - BitVec.ofNat 64 4095)).setWidth 32

theorem p2rX_toNat {x : BitVec 32} (_hx : x.toNat < q) : (p2rX x).toNat = x.toNat + 4095 := by
  have hq : q = 8380417 := rfl
  rw [BitVec.toNat_add, toNat_setWidth64, BitVec.toNat_ofNat]
  omega_arith

theorem t1V_toNat {x : BitVec 32} (hx : x.toNat < q) : (t1V x).toNat = (x.toNat + 4095) / 8192 := by
  have hq : q = 8380417 := rfl
  have e : (p2rX x >>> 13).toNat = (x.toNat + 4095) / 8192 := by
    rw [BitVec.toNat_ushiftRight, p2rX_toNat hx, Nat.shiftRight_eq_div_pow]
  rw [t1V, BitVec.toNat_setWidth, e]
  omega_arith

/-- `v - k` plus `q` if negative, for `v < 2³²` and `k ≤ q`: `v + q - k` if
`v < k`, else `v - k`. -/
theorem addQ_sub_toNat {v k : BitVec 64} (hv : v.toNat < 2 ^ 32) (hk : k.toNat ≤ q) :
    (addQ (v - k)).toNat = if v.toNat < k.toNat then v.toNat + q - k.toNat else v.toNat - k.toNat := by
  have hq : q = 8380417 := rfl
  have hQ : Qv.toNat = 8380417 := rfl
  have hsub : (v - k).toNat = if v.toNat < k.toNat then 2 ^ 64 - k.toNat + v.toNat else v.toNat - k.toNat := by
    rw [BitVec.toNat_sub]
    split <;> omega_arith
  have hsh : ((v - k) >>> 63).toNat = if v.toNat < k.toNat then 1 else 0 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hsub]
    split <;> omega_arith
  rw [addQ, BitVec.toNat_add, BitVec.toNat_mul, hsh, hsub, hQ]
  split <;> omega_arith

theorem t0V_toNat {x : BitVec 32} (hx : x.toNat < q) :
    (t0V x).toNat = if (x.toNat + 4095) % 8192 < 4095 then (x.toNat + 4095) % 8192 + q - 4095
      else (x.toNat + 4095) % 8192 - 4095 := by
  have hq : q = 8380417 := rfl
  have e1 : (p2rX x - (p2rX x >>> 13) <<< 13).toNat = (x.toNat + 4095) % 8192 := by
    have h2 : ((p2rX x >>> 13) <<< 13).toNat = (x.toNat + 4095) / 8192 * 8192 := by
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, p2rX_toNat hx, Nat.shiftRight_eq_div_pow,
        Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_arith)]
    rw [BitVec.toNat_sub, h2, p2rX_toNat hx]
    omega_arith
  have hr := Nat.mod_lt (x.toNat + 4095) (show 8192 > 0 by decide)
  have h4095 : (BitVec.ofNat 64 4095).toNat = 4095 := rfl
  rw [t0V, BitVec.toNat_setWidth, addQ_sub_toNat (by rw [e1]; omega_arith) (by rw [h4095, hq]; omega_arith), e1, h4095]
  split <;> omega_arith

/-- A state satisfying the precondition. -/
def p2rSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]

end VG.Proof.MlDsa.AArch64.Round
