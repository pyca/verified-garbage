import VerifiedGarbage.Proof.Weierstrass.X86.Pow
import VerifiedGarbage.Impl.Weierstrass.X86.PowChain

/-! ## `PowerState` -/

section

/-! # State and frames for fixed exponentiation chains -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

structure PowerState (P : PowCfg) (base : Addr) (size m : Nat) [NeZero m]
    (B : Fin m) (a t : Nat) (s : State) : Prop where
  scr : Scr s base size
  mod : ModOkW P.M size m s.mem base
  base_lt : wordsVal s.mem base P.base P.M.n < m
  base_val : toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n) = B
  acc_lt : wordsVal s.mem base P.acc P.M.n < m
  acc_val : toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.acc P.M.n) = B ^ a
  tmp_lt : wordsVal s.mem base P.tmp P.M.n < m
  tmp_val : toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.tmp P.M.n) = B ^ t

theorem powWx_mo {P : PowCfg} {F : Spec.Weierstrass.Mont.Modulus} {m size wk : Nat} (hL : PowLay P size)
    (hW : PowWk P F m size wk) :
    ∀ w ∈ powWx P wk, P.M.mo + 8 * P.M.n ≤ w.1 ∨ w.1 + w.2 ≤ P.M.mo := by
  intro w hw
  simp only [powWx, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with hw | rfl | rfl
  · exact hL.mo_w w hw
  · exact .inl hW.mo
  · have := hW.mo; have := hW.toCallCfg.own_le
    exact .inl (by simp only; omega)

theorem powWx_base {P : PowCfg} {F : Spec.Weierstrass.Mont.Modulus} {m size wk : Nat} (hL : PowLay P size)
    (hW : PowWk P F m size wk) :
    ∀ w ∈ powWx P wk, P.base + 8 * P.M.n ≤ w.1 ∨ w.1 + w.2 ≤ P.base := by
  intro w hw
  simp only [powWx, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with hw | rfl | rfl
  · exact hL.base_w w hw
  · exact .inl hW.base
  · have := hW.base; have := hW.toCallCfg.own_le
    exact .inl (by simp only; omega)

theorem PowerState.rebuild {P : PowCfg} {F : Spec.Weierstrass.Mont.Modulus} {base : Addr}
    {size wk m a t a' t' : Nat} [NeZero m]
    {B : Fin m} {s u : State} (I : PowerState P base size m B a t s)
    (hL : PowLay P size) (hW : PowWk P F m size wk)
    (hs : Scr u base size) (U : Unch base (powWx P wk) s.mem u.mem)
    (ha : wordsVal u.mem base P.acc P.M.n < m)
    (va : toM m (2 ^ (64 * P.M.n)) (wordsVal u.mem base P.acc P.M.n) = B ^ a')
    (ht : wordsVal u.mem base P.tmp P.M.n < m)
    (vt : toM m (2 ^ (64 * P.M.n)) (wordsVal u.mem base P.tmp P.M.n) = B ^ t') :
    PowerState P base size m B a' t' u := by
  have hn := I.scr.nowrap
  have hmo := I.mod.mo
  have hbase := hL.base
  have em := U.wordsVal (powWx_mo hL hW) (by omega)
  have eb := U.wordsVal (powWx_base hL hW) (by omega)
  exact ⟨hs, ⟨I.mod.n0, I.mod.mo, I.mod.tmp, I.mod.sep, em.trans I.mod.val, I.mod.inv, I.mod.red⟩,
    eb ▸ I.base_lt, by rw [eb]; exact I.base_val, ha, va, ht, vt⟩

theorem PowerState.regs {P : PowCfg} {base : Addr} {size m a t : Nat} [NeZero m]
    {B : Fin m} {s u : State} (I : PowerState P base size m B a t s)
    {rs : List Reg} (K : Keeps rs s u) (he : Reg.edi ∉ rs) (hm : u.mem = s.mem)
    (hsp : Reg.esp ∉ rs := by decide) :
    PowerState P base size m B a t u := by
  refine ⟨I.scr.of_keeps K he hsp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hm]
  · exact I.mod
  · exact I.base_lt
  · exact I.base_val
  · exact I.acc_lt
  · exact I.acc_val
  · exact I.tmp_lt
  · exact I.tmp_val

end VG.Proof.Weierstrass.X86

end

/-! ## `PowerStep` -/

section

/-! # Multiplication and saved powers in fixed exponentiation chains -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

theorem powerMul_ok {P : PowCfg} {F : Spec.Weierstrass.Mont.Modulus} {base : Addr} {size wk m a t b e : Nat}
    [NeZero m] {B : Fin m} {s : State} (I : PowerState P base size m B a t s)
    (hL : PowLay P size) (hW : PowWk P F m size wk) (hm : UnitMod m (2 ^ (64 * P.M.n)))
    (hbw : b + 8 * P.M.n ≤ wk)
    (hblt : wordsVal s.mem base b P.M.n < m)
    (hbval : toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base b P.M.n) = B ^ e) :
    WP isa (Mont.mulCall F P.acc P.acc b) s fun u =>
      PowerState P base size m B (a + e) t u ∧ Keeps clob s u ∧
      Unch base (powWx P wk) s.mem u.mem := by
  have hn := I.scr.nowrap
  have htmp := hL.tmp
  refine WP.mono (mulC_ok hW.toCallCfg I.scr hW.acc hW.acc hbw hblt) fun u ⟨K, L, V⟩ => ?_
  have U : Unch base (powWx P wk) s.mem u.mem := K.unch.mono fun w hw => by
    simp only [powWx, powW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    grind
  have et : wordsVal u.mem base P.tmp P.M.n = wordsVal s.mem base P.tmp P.M.n :=
    K.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact hL.acc_tmp.symm
      · exact hL.tmp_mtmp
      · exact .inl hW.tmp
      · have := hW.tmp; have := hW.toCallCfg.own_le
        exact .inl (by simp only; omega)) (by omega)
  refine ⟨I.rebuild hL hW (K.scr I.scr) U L ?_ (et ▸ I.tmp_lt) ?_, ⟨K.gpr, K.rd, K.wr⟩, U⟩
  · rw [toM_mul hm V, I.acc_val, hbval, Lean.Grind.Semiring.pow_add]
  · rw [et]; exact I.tmp_val

theorem powerSave_ok {P : PowCfg} {F : Spec.Weierstrass.Mont.Modulus} {base : Addr} {size wk m a t : Nat}
    [NeZero m] {B : Fin m} {s : State} (I : PowerState P base size m B a t s)
    (hL : PowLay P size) (hW : PowWk P F m size wk) :
    WP isa (.block (copy (2 * P.M.n) P.tmp P.acc)) s fun u =>
      PowerState P base size m B a a u ∧ Keeps [.eax] s u ∧ Unch base (powWx P wk) s.mem u.mem := by
  have hn := I.scr.nowrap
  have ha := hL.acc
  have ht := hL.tmp
  have hap := hL.acc_tmp
  refine WP.mono (copy_ok (2 * P.M.n) I.scr (o := P.tmp) (a := P.acc) (by omega) (by omega) (by omega))
    fun u ⟨V, K, O⟩ => ?_
  rw [show 4 * (2 * P.M.n) = 8 * P.M.n by omega] at O
  have U : Unch base (powWx P wk) s.mem u.mem := O.unch.mono fun w hw => by
    simp only [List.mem_singleton] at hw
    simp [hw, powWx, powW]
  have et : wordsVal u.mem base P.tmp P.M.n = wordsVal s.mem base P.acc P.M.n := by
    rw [wordsVal_eq_val32, V, ← wordsVal_eq_val32]
  have ea : wordsVal u.mem base P.acc P.M.n = wordsVal s.mem base P.acc P.M.n :=
    O.wordsVal hap (by omega)
  refine ⟨I.rebuild hL hW (I.scr.of_keeps K (by decide)) U (ea ▸ I.acc_lt) ?_ (et ▸ I.acc_lt) ?_, K, U⟩
  · rw [ea]; exact I.acc_val
  · rw [et]; exact I.acc_val

end VG.Proof.Weierstrass.X86

end

/-! ## `PowerSquares` -/

section

/-! # Public-count repeated squaring in a fixed exponentiation chain -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

theorem squareRun_ok {P : PowCfg} {F : Spec.Weierstrass.Mont.Modulus} {base : Addr} {size wk m a t : Nat} [NeZero m]
    {B : Fin m} {s : State} (I : PowerState P base size m B a t s)
    (hL : PowLay P size) (hW : PowWk P F m size wk) (hm : UnitMod m (2 ^ (64 * P.M.n))) :
    ∀ n, n < 2 ^ 32 → WP isa (squareRun P F n) s fun u =>
      PowerState P base size m B (a * 2 ^ n) t u ∧ Keeps powClob s u ∧
      Unch base (powWx P wk) s.mem u.mem
  | 0, _ => by
    simp only [squareRun, Nat.pow_zero, Nat.mul_one]
    exact WP.block_nil ⟨I, Keeps.refl .., Unch.refl base (powWx P wk) s.mem⟩
  | n + 1, hn => by
    unfold squareRun
    refine WP.seq (wp_movS rfl fun s₁ u₁ _ => WP.block_nil ?_)
    let Inv := fun j u => PowerState P base size m B (a * 2 ^ (n + 1 - j)) t u ∧
      u.gpr .esi = BitVec.ofNat 32 j ∧ Keeps powClob s u ∧ Unch base (powWx P wk) s.mem u.mem
    refine countLoop_ok (Inv := Inv) (n := n + 1) ?_ ?_ (by omega) ?_
    · intro j v hj hjn hI
      obtain ⟨Iv, ev, Kv, Uv⟩ := hI
      refine WP.seq (wp_decCounter hj ev fun v₁ e₁ K₁ mem₁ => WP.block_nil ?_)
      have I₁ := Iv.regs K₁ (by decide) mem₁
      refine WP.seq (WP.mono (powerMul_ok I₁ hL hW hm hW.acc I₁.acc_lt I₁.acc_val)
        fun v₂ ⟨I₂, K₂, U₂⟩ => ?_)
      have ee : a * 2 ^ (n + 1 - j) + a * 2 ^ (n + 1 - j) = a * 2 ^ (n + 1 - (j - 1)) := by
        rw [show n + 1 - (j - 1) = (n + 1 - j) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc]
        omega
      rw [ee] at I₂
      have e₂ : v₂.gpr .esi = BitVec.ofNat 32 (j - 1) := by rw [K₂.1 _ esi_not_clob, e₁]
      refine wp_testCounter (by omega) e₂ fun u F hz => WP.block_nil ⟨?_, hz⟩
      refine ⟨I₂.regs (F.keeps []) (by decide) F.mem, by rw [F.gpr]; exact e₂,
        ((Kv.trans (K₁.mono (by decide))).trans (K₂.mono (by decide))).trans (F.keeps _), ?_⟩
      intro x hx
      rw [F.mem, U₂ x hx, mem₁]
      exact Uv x hx
    · intro u ⟨Iu, _, Ku, Uu⟩
      simp only [Nat.sub_zero] at Iu
      exact ⟨Iu, Ku, Uu⟩
    · refine ⟨?_, u₁.gpr, u₁.keeps.mono (by decide), ?_⟩
      · simp only [Nat.sub_self, Nat.pow_zero, Nat.mul_one]
        exact I.regs u₁.keeps (by decide) u₁.mem
      · rw [u₁.mem]; exact Unch.refl base (powWx P wk) s.mem

end VG.Proof.Weierstrass.X86

end

/-! ## `PowerChain` -/

section

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

theorem powerOp_ok {P : PowCfg} {F : Spec.Weierstrass.Mont.Modulus} {base : Addr} {size wk m a t : Nat} [NeZero m]
    {B : Fin m} {s : State} (I : PowerState P base size m B a t s)
    (hL : PowLay P size) (hW : PowWk P F m size wk) (hm : UnitMod m (2 ^ (64 * P.M.n)))
    (op : PowerOp) (h : powerOpBound op) :
    WP isa (powerOp P F op) s fun u =>
      PowerState P base size m B (powerExponents op (a, t)).1 (powerExponents op (a, t)).2 u ∧
      Keeps powClob s u ∧ Unch base (powWx P wk) s.mem u.mem := by
  cases op with
  | save => exact WP.mono (powerSave_ok I hL hW) fun u ⟨Iu, K, U⟩ => ⟨Iu, K.mono (by decide), U⟩
  | squares n => exact squareRun_ok I hL hW hm n h
  | mulBase =>
    exact WP.mono (powerMul_ok I hL hW hm hW.base I.base_lt
      (show toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n) = B ^ 1 by
        rw [Lean.Grind.Semiring.pow_one]; exact I.base_val))
      fun u ⟨Iu, K, U⟩ => ⟨Iu, K.mono (by decide), U⟩
  | mulSaved =>
    exact WP.mono (powerMul_ok I hL hW hm hW.tmp I.tmp_lt I.tmp_val)
      fun u ⟨Iu, K, U⟩ => ⟨Iu, K.mono (by decide), U⟩

theorem powerChain_ok {P : PowCfg} {F : Spec.Weierstrass.Mont.Modulus} {base : Addr} {size wk m : Nat} [NeZero m]
    (hL : PowLay P size) (hW : PowWk P F m size wk) (hm : UnitMod m (2 ^ (64 * P.M.n)))
    (ops : List PowerOp) (h : ∀ op ∈ ops, powerOpBound op) {B : Fin m} {s : State} {v : Nat × Nat}
    (I : PowerState P base size m B v.1 v.2 s) :
    WP isa (powerChain P F ops) s fun u =>
      PowerState P base size m B (chainExponents ops v).1 (chainExponents ops v).2 u ∧
      Keeps powClob s u ∧ Unch base (powWx P wk) s.mem u.mem := by
  induction ops generalizing s v with
  | nil => exact WP.block_nil ⟨I, Keeps.refl .., Unch.refl base (powWx P wk) s.mem⟩
  | cons op ops ih =>
    refine WP.seq (WP.mono (powerOp_ok I hL hW hm op (h op (List.mem_cons_self ..))) fun u ⟨Iu, Ku, Uu⟩ => ?_)
    refine WP.mono (ih (fun op ho => h op (List.mem_cons_of_mem _ ho)) Iu) fun t ⟨It, Kt, Ut⟩ =>
      ⟨It, Ku.trans Kt, fun x hx => (Ut x hx).trans (Uu x hx)⟩

end VG.Proof.Weierstrass.X86

end
