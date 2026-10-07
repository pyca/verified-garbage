import VerifiedGarbage.Proof.Weierstrass.X86.PowerSquares

/-! # Composing fixed exponentiation chains -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

def powerExponents : PowerOp → Nat × Nat → Nat × Nat
  | .save, (a, _) => (a, a)
  | .squares n, (a, t) => (a * 2 ^ n, t)
  | .mulBase, (a, t) => (a + 1, t)
  | .mulSaved, (a, t) => (a + t, t)

def chainExponents : List PowerOp → Nat × Nat → Nat × Nat
  | [], v => v
  | op :: ops, v => chainExponents ops (powerExponents op v)

def powerOpBound : PowerOp → Prop
  | .squares n => n < 2 ^ 32
  | _ => True

theorem powerOp_ok {P : PowCfg} {base : Addr} {size wk m a t : Nat} [NeZero m]
    {B : Fin m} {s : State} (I : PowerState P base size m B a t s)
    (hL : PowLay P size) (hW : PowWk P size wk) (hm : UnitMod m (2 ^ (64 * P.M.n)))
    (op : PowerOp) (h : powerOpBound op) :
    WP isa (powerOp P wk op) s fun u =>
      PowerState P base size m B (powerExponents op (a, t)).1 (powerExponents op (a, t)).2 u ∧
      Keeps powClob s u ∧ Unch base (powWx P wk) s.mem u.mem := by
  cases op with
  | save => exact WP.mono (powerSave_ok I hL hW) fun u ⟨Iu, K, U⟩ => ⟨Iu, K.mono (by decide), U⟩
  | squares n => exact squareRun_ok I hL hW hm n h
  | mulBase =>
    exact WP.mono (powerMul_ok I hL hW hm hL.base hW.base I.base_lt
      (show toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n) = B ^ 1 by
        rw [Lean.Grind.Semiring.pow_one]; exact I.base_val))
      fun u ⟨Iu, K, U⟩ => ⟨Iu, K.mono (by decide), U⟩
  | mulSaved =>
    exact WP.mono (powerMul_ok I hL hW hm hL.tmp hW.tmp I.tmp_lt I.tmp_val)
      fun u ⟨Iu, K, U⟩ => ⟨Iu, K.mono (by decide), U⟩

theorem powerChain_ok {P : PowCfg} {base : Addr} {size wk m : Nat} [NeZero m]
    (hL : PowLay P size) (hW : PowWk P size wk) (hm : UnitMod m (2 ^ (64 * P.M.n)))
    (ops : List PowerOp) (h : ∀ op ∈ ops, powerOpBound op) {B : Fin m} {s : State} {v : Nat × Nat}
    (I : PowerState P base size m B v.1 v.2 s) :
    WP isa (powerChain P wk ops) s fun u =>
      PowerState P base size m B (chainExponents ops v).1 (chainExponents ops v).2 u ∧
      Keeps powClob s u ∧ Unch base (powWx P wk) s.mem u.mem := by
  induction ops generalizing s v with
  | nil => exact WP.block_nil ⟨I, Keeps.refl .., Unch.refl base (powWx P wk) s.mem⟩
  | cons op ops ih =>
    refine WP.seq (WP.mono (powerOp_ok I hL hW hm op (h op (List.mem_cons_self ..))) fun u ⟨Iu, Ku, Uu⟩ => ?_)
    refine WP.mono (ih (fun op ho => h op (List.mem_cons_of_mem _ ho)) Iu) fun t ⟨It, Kt, Ut⟩ =>
      ⟨It, Ku.trans Kt, fun x hx => (Ut x hx).trans (Uu x hx)⟩

end VG.Proof.Weierstrass.X86
