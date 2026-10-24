module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
public import VerifiedGarbage.Impl.EcKey.Compressed.PPC64LE.Decompress
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointFprog
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.SlotOps
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.Unch

/-!
# SEC 1 point decompression on PPC64LE: the field programs

`ops_core`: a field program on the signature's slots (`fprog` of named
slots), from a state holding its inputs below `m`, as ECDH's `curve_core`
(`Proof/Ecdh/PPC64LE/Validate.lean`) for any program. `rhs_ok`: `rhsOps`
computes `x³ + a x + b` to `W2`, in Montgomery form; `checkPoly_ok`:
`checkRootOps` computes `y² - rhs` to `W3`.
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Spec.Weierstrass
open VG.Impl.Ecdh.PPC64LE (R2P BP QXM QYM QY W0 W1 W2 W3)

variable {c : Cfg}

/-- The signature's slots written by a program are apart from every other. -/
theorem slLay (h7 : c.n < 10) (W : List Nat) : Point.LayR c.n 45 W c.sl where
  le := fun _ hx => sl_below_own c h7 hx
  apart := fun _ _ _ _ hxw => sl_apart c hxw

/-- A field program on the signature's slots, modulo `p`. -/
theorem ops_core (hc : CfgOk c) {ops : List FOp} {V W : List Nat} {base : Addr} {s : State}
    (hw : WsReg s base) (hids : ∀ op ∈ ops, op.out ∈ W ∧ ∀ x ∈ op.out :: op.ins, x < 45)
    (hV : ∀ x ∈ V, x < 45) (hlt : ∀ x ∈ V, sv c base s x < c.C.p) (hR : readsOk ops V = true) :
    WP isa (Point.fprogR c.sl c.SP ops) s fun s' =>
      Point.KeepR c.n c.sl base (ops.map FOp.out) s s' ∧
      Point.InvR c.n 45 c.sl base c.C.p (validAfter ops V)
        (runOps ops fun x => toM c.C.p (2 ^ (64 * c.n)) (sv c base s x)) s' := by
  have h7 := hc.n10
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hM : ModOk c.n c.C.p := by have := hc.fp; rw [hc.fpk, hc.fpm] at this; exact this
  have hkS := hc.fpk
  have hmS := hc.fpm
  obtain ⟨n, C, SP, SN⟩ := c
  obtain ⟨cv, w, m', k', d⟩ := SP
  dsimp only at hkS hmS
  subst hkS hmS
  exact Point.fprogR_ok (S := ⟨cv, w, _, _, d⟩) hM rfl (slLay h7 W) hpR ops
    ⟨hw, hV, hlt, fun _ _ => rfl⟩ hids hR

/-- What a field program keeps, as `Rk` and `Unch`. -/
theorem keepR_unch {ops : List FOp} {base : Addr} {s s' : State}
    (K : Point.KeepR c.n c.sl base (ops.map FOp.out) s s') :
    Rk fnClob s s' ∧ Unch base ((ops.map FOp.out).map (fun w => (c.sl w, 8 * c.n)) ++ [(own c.n, 64 * c.n)])
      s.mem s'.mem :=
  ⟨⟨K.gpr, K.rd, K.wr, K.sp⟩, K.mem⟩

/-- `x R⁻¹ · (R² mod p) R⁻¹ = x`. -/
theorem raw_r2_mul (hc : CfgOk c) (a : Nat) :
    toM c.C.p (2 ^ (64 * c.n)) a * toM c.C.p (2 ^ (64 * c.n)) (c.R * c.R % c.C.p) = Fin.ofNat c.C.p a := by
  change toM c.C.p (2 ^ (64 * c.n)) a * toM c.C.p (2 ^ (64 * c.n)) (c.mont c.R) = _
  rw [toM_cmont hc]
  unfold toM
  have hu := mul_rinv (unitMod_pow_two hc.p_odd (64 * c.n))
  change Fin.ofNat c.C.p c.R * rinv c.C.p (2 ^ (64 * c.n)) = 1 at hu
  grind

/-! ## `x³ + a x + b` -/

/-- `rhsOps` past its first multiplication, on slot numbers. -/
def rhsN : List FOp :=
  [.mul W1 QXM QXM, .mul W2 W1 QXM, .mul W1 AP QXM, .add W3 W2 W1, .add W2 W3 BP]

theorem rhsOps_eq (c : Cfg) : fprog c.SP (Impl.EcKey.Compressed.PPC64LE.rhsOps c) =
    .seq (mulCall c.SP (c.sl QXM) (c.sl E) (c.sl R2P)) (Point.fprogR c.sl c.SP rhsN) := rfl

theorem rhsN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps rhsN e W2 = e QXM * e QXM * e QXM + e AP * e QXM + e BP := by
  simp only [rhsN, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [W1, W2, W3, QXM, AP, BP, TT, SM, RM, XM, EM, Nat.reduceEqDiff, ↓reduceIte]

theorem rhsN_reads : readsOk rhsN [QXM, AP, BP] = true := by decide

theorem rhsN_ids : ∀ op ∈ rhsN, op.out ∈ [W1, W2, W3] ∧ ∀ x ∈ op.out :: op.ins, x < 45 := by decide

/-- What `rhsOps` writes. -/
abbrev rhsW (c : Cfg) : List (Nat × Nat) := slW c [QXM, W1, W2, W3] ++ [(own c.n, 64 * c.n)]

/-- `x³ + a x + b`, in Montgomery form, to `W2`, for any `x` below `2^(64 n)`
(reduced modulo `p`). -/
theorem rhs_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    (hap : sv c base s AP = c.mont c.C.a) (hbp : sv c base s BP = c.mont c.C.b) :
    WP isa (fprog c.SP (Impl.EcKey.Compressed.PPC64LE.rhsOps c)) s fun s' =>
      WsReg s' base ∧ Rk fnClob s s' ∧ Unch base (rhsW c) s.mem s'.mem ∧ sv c base s' W2 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' W2) =
        (let x := Fin.ofNat c.C.p (sv c base s E)
         x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b) := by
  have h7 := hc.n10
  have hn := hw.nowrap
  have hp3 := hc.p_ge
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have hr2' : sv c base s R2P = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.p := hr2
  rw [rhsOps_eq]
  refine WP.seq (WP.mono (slMul_ok hc.fp hc.fpk hc.fpm h7 hw (o := QXM) (a := E) (b := R2P) (by decide)
    (by decide) (by decide) (by rw [hr2']; exact Nat.mod_lt _ (by omega))) fun s₁ ⟨k₁, U₁, lt₁, e₁⟩ => ?_)
  have hw₁ := hw.of_rk k₁
  have v₁ : ∀ {i}, i < 45 → i ≠ QXM → sv c base s₁ i = sv c base s i := fun hi h₁ =>
    sv_unch U₁ h7 hn hi (apart_callW h7 hi h₁)
  have x₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ QXM) = Fin.ofNat c.C.p (sv c base s E) :=
    toM_r2 hpR (by rw [e₁, hr2'])
  have a₁ : sv c base s₁ AP = c.mont c.C.a := (v₁ (by decide) (by decide)).trans hap
  have b₁ : sv c base s₁ BP = c.mont c.C.b := (v₁ (by decide) (by decide)).trans hbp
  refine WP.mono (ops_core hc hw₁ rhsN_ids (by decide) (fun x hx' => ?_) rhsN_reads) fun s' ⟨K, I⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
    rcases hx' with rfl | rfl | rfl
    · exact lt₁
    · rw [a₁]; exact hmont _
    · rw [b₁]; exact hmont _
  have hW2 : W2 ∈ validAfter rhsN [QXM, AP, BP] := by decide
  have v := I.val W2 hW2
  rw [rhsN_run, a₁, b₁, toM_cmont hc, toM_cmont hc, x₁] at v
  obtain ⟨R, U⟩ := keepR_unch K
  exact ⟨I.ws, k₁.trans R, (U₁.trans U).mono fun w hw' => by
    simp only [rhsN, callW, List.map_cons, List.map_nil, FOp.out, slW, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hw' ⊢
    grind, I.lt W2 hW2, v⟩

/-! ## `y² - rhs` -/

/-- `checkRootOps` on slot numbers. -/
def checkN : List FOp := [.mul QYM QY R2P, .mul W1 QYM QYM, .sub W3 W1 W2]

theorem checkOps_eq (c : Cfg) :
    fprog c.SP (Impl.EcKey.Compressed.PPC64LE.checkRootOps c) = Point.fprogR c.sl c.SP checkN := rfl

theorem checkN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps checkN e W3 = (e QY * e R2P) * (e QY * e R2P) - e W2 := by
  simp only [checkN, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [QYM, QY, R2P, W1, W2, X, RR, DM, TT, SM, Nat.reduceEqDiff, ↓reduceIte]

theorem checkN_reads : readsOk checkN [QY, R2P, W2] = true := by decide

theorem checkN_ids : ∀ op ∈ checkN, op.out ∈ [QYM, W1, W3] ∧ ∀ x ∈ op.out :: op.ins, x < 45 := by decide

/-- What `checkRootOps` writes. -/
abbrev checkW (c : Cfg) : List (Nat × Nat) := slW c [QYM, W1, W3] ++ [(own c.n, 64 * c.n)]

/-- `y² - rhs`, in Montgomery form, to `W3`. -/
theorem checkPoly_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base)
    (hy : sv c base s QY < c.C.p) (hr : sv c base s W2 < c.C.p) (hr2 : sv c base s R2P = c.R * c.R % c.C.p) :
    WP isa (fprog c.SP (Impl.EcKey.Compressed.PPC64LE.checkRootOps c)) s fun s' =>
      WsReg s' base ∧ Rk fnClob s s' ∧ Unch base (checkW c) s.mem s'.mem ∧ sv c base s' W3 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' W3) =
        Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) -
          toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) := by
  have hp3 := hc.p_ge
  rw [checkOps_eq]
  refine WP.mono (ops_core hc hw checkN_ids (by decide) (fun x hx' => ?_) checkN_reads) fun s' ⟨K, I⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
    rcases hx' with rfl | rfl | rfl
    · exact hy
    · rw [hr2]; exact Nat.mod_lt _ (by omega)
    · exact hr
  have hW3 : W3 ∈ validAfter checkN [QY, R2P, W2] := by decide
  have v := I.val W3 hW3
  rw [checkN_run, hr2, raw_r2_mul hc] at v
  obtain ⟨R, U⟩ := keepR_unch K
  exact ⟨I.ws, R, U.mono fun w hw' => by
    simp only [checkN, List.map_cons, List.map_nil, FOp.out, slW, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hw' ⊢
    grind, I.lt W3 hW3, v⟩

end VG.Proof.EcKey.Compressed.PPC64LE
