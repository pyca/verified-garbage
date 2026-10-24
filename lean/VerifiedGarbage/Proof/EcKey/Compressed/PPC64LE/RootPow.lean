module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
public import VerifiedGarbage.Impl.EcKey.Compressed.PPC64LE.Decompress
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Bits
import VerifiedGarbage.Proof.Mont.PPC64LE.Const
import VerifiedGarbage.Proof.Mont.Words32

/-!
# SEC 1 point decompression on PPC64LE: powers of the right-hand side

`rootPower_ok`: `rootPower e j` writes `e` to `EXPP`, its bits to table `j`,
and `W2^e` (in Montgomery form) to `ACC`, by the signature's power
(`pow_ok`); `rootThree_ok`: the candidate `rhs^((p+1)/4)` for `p ≡ 3 mod 4`.
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Spec.Weierstrass
open VG.Impl.Ecdh.PPC64LE (W2)
open VG.Impl.EcKey.Compressed.PPC64LE (rootPow rootPower)

variable {c : Cfg}

theorem rootPowLay (hc : CfgOk c) {j : Nat} (hj : j < 3) : PowLayP (rootPow c j) c.n where
  acc := sl_below_own c hc.n10 (by decide)
  tmp := sl_below_own c hc.n10 (by decide)
  base := sl_below_own c hc.n10 (by decide)
  one := sl_below_own c hc.n10 (by decide)
  own := own_below_bits c hc.n10 j
  bits := bitsAt_le c hc.n10 hj
  nbits := by show 1 ≤ 64 * c.n ∧ 64 * c.n < 2 ^ 15; have := hc.n0; have := hc.n10; omega
  acc_tmp := sl_apart c (by decide)
  acc_one := sl_apart c (by decide)
  base_acc := sl_apart c (by decide)
  base_tmp := sl_apart c (by decide)
  acc4 := sl_al c _
  tmp4 := sl_al c _
  one4 := sl_al c _

/-- What `rootPower e j` writes. -/
abbrev rootPowerW (c : Cfg) (j : Nat) : List (Nat × Nat) :=
  [(c.sl EXPP, 8 * c.n), (bitsAt c.n j, 64 * c.n), (c.sl ACC, 8 * c.n), (c.sl PT, 8 * c.n),
    (own c.n, 64 * c.n)]

/-- `ACC = W2^e`, in Montgomery form. -/
theorem rootPower_ok (hc : CfgOk c) {e j : Nat} (hj : j < 3) (he : e < 2 ^ (64 * c.n)) {base : Addr}
    {s : State} (hw : WsReg s base) (hB : sv c base s W2 < c.C.p)
    (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (rootPower c e j) s fun s' =>
      WsReg s' base ∧ Rk powClob s s' ∧ Unch base (rootPowerW c j) s.mem s'.mem ∧
      sv c base s' ACC < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) = toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ e := by
  have h7 := hc.n10
  have hn := hw.nowrap
  have hE := sl_le c h7 (i := EXPP) (by decide)
  have hsz : size = 8192 := rfl
  change WP isa (.seq (.block (VG.Impl.Mont.PPC64LE.setConst c.n (c.sl EXPP) e))
    (.seq (bits (c.sl EXPP) (bitsAt c.n j) (8 * c.n)) (pow (rootPow c j) c.SP))) s _
  refine WP.seq (WP.mono (setConst_ok hw.ws hw.at3 (o := c.sl EXPP) (by omega) he) fun s₁ ⟨O₁, v₁, k₁⟩ => ?_)
  rw [← wordsVal_eq_val32] at v₁
  have hw₁ := hw.of_kp k₁
  refine WP.seq (WP.mono (tbl_bits_ok hc hw₁ (i := EXPP) (j := j) (by decide) hj) fun s₂ ⟨b₂, k₂, O₂⟩ => ?_)
  rw [v₁] at b₂
  have hw₂ := hw₁.of_kp k₂
  have keep₂ : ∀ {i}, i < 45 → i ≠ EXPP → sv c base s₂ i = sv c base s i := fun hi hiE =>
    (sv_unch O₂.unch h7 hn hi (apart_tbl h7 hi j)).trans
      (sv_unch O₁.unch h7 hn hi (fun w hw' => by
        rw [List.mem_singleton.mp hw']; have := sl_apart c hiE; dsimp only; omega))
  refine WP.mono (pow_ok hc.fpk hc.fpm (modP hc) rfl (rootPowLay hc hj) (unitMod_pow_two hc.p_odd _) hw₂
    (by show sv c base s₂ W2 < _; rw [keep₂ (by decide) (by decide)]; exact hB)
    (by show sv c base s₂ ONEP = _; rw [keep₂ (by decide) (by decide)]; exact hO) b₂ he)
    fun s₃ ⟨k₃, U₃, lt₃, v₃⟩ => ⟨hw₂.of_rk k₃, ((k₁.rk (rs' := powClob)).trans (k₂.rk (rs' := powClob))).trans k₃,
      (O₁.unch.trans O₂.unch).trans U₃, lt₃, ?_⟩
  change toM c.C.p (2 ^ (64 * c.n)) (sv c base s₃ ACC) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ W2) ^ e at v₃
  rw [v₃, keep₂ (by decide) (by decide)]

/-- The candidate `rhs^((p+1)/4)`, for `p ≡ 3 mod 4`. -/
theorem rootThree_ok (hc : CfgOk c) (hp : c.C.p % 4 = 3) {base : Addr} {s : State} (hw : WsReg s base)
    (hB : sv c base s W2 < c.C.p) (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.PPC64LE.rootCandidate c) s fun s' =>
      WsReg s' base ∧ Rk powClob s s' ∧ Unch base (rootPowerW c 2) s.mem s'.mem ∧
      sv c base s' ACC < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ ((c.C.p + 1) / 4) := by
  simp only [Impl.EcKey.Compressed.PPC64LE.rootCandidate, hp, ↓reduceIte]
  exact rootPower_ok hc (by decide) (by have := hc.p_lt; have := hc.p_ge; omega) hw hB hO

end VG.Proof.EcKey.Compressed.PPC64LE
