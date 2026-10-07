import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacBuild

/-!
# The Jacobian window method on x86-64: `R = 32 R`

Five doublings of `R` in place by the doubling given (`DblOk`), counted in the
bits of `rbx` above the window index (below 4096): `rbx` gets `5 · 4096`
added, and each doubling takes `4096` off and compares with `4096`, whose
carry ends the loop with the window index left (`dblCount_ok`, `aeLoop_ok`,
`dbls_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-- Consume one doubling, setting carry when only the window index remains. -/
theorem dblCount_ok (s : State) {i j : Nat} (hi : i < 4096) (hj : 1 ≤ j) (hj' : j ≤ 5)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (i + 4096 * j)) :
    WP isa (.block [.alu .sub .rbx (.imm 4096), .alu .cmp .rbx (.imm 4096)]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 (i + 4096 * (j - 1)) ∧
      s'.cf = some (decide (j - 1 = 0)) ∧ Keeps [.rbx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, ite_true,
    Option.some.injEq, exists_eq_left', hb]
  have e : (4096 : BitVec 32).signExtend 64 = BitVec.ofNat 64 4096 := by decide
  have sub : BitVec.ofNat 64 (i + 4096 * j) - (4096 : BitVec 32).signExtend 64 =
      BitVec.ofNat 64 (i + 4096 * (j - 1)) := by
    rw [e]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  refine ⟨sub, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [sub, e]
    congr 1
    simp only [BitVec.toNat_ofNat]
    apply propext
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- A loop of `n ≥ 1` iterations, branching while the count left is nonzero. -/
theorem aeLoop_ok {body : Prog isa} {Inv : Nat → State → Prop} {Q : State → Prop} {n : Nat}
    (hstep : ∀ j s, 1 ≤ j → j ≤ n → Inv j s →
      WP isa body s fun s' => Inv (j - 1) s' ∧ s'.cf = some (decide (j - 1 = 0)))
    (hQ : ∀ s, Inv 0 s → Q s) (hn : 1 ≤ n) {s : State} (hs : Inv n s) :
    WP isa (.loop body .ae) s Q := by
  refine WP.loop (M := isa) (fun j s => 1 ≤ j ∧ j ≤ n ∧ Inv j s) (fun j s ⟨h1, h2, hi⟩ => ?_) n s
    ⟨hn, Nat.le_refl _, hs⟩
  refine WP.mono (hstep j s h1 h2 hi) fun s' ⟨hi', hc⟩ => ?_
  by_cases hj : j - 1 = 0
  · refine Or.inl ⟨?_, hQ s' (by rw [hj] at hi'; exact hi')⟩
    show s'.cf.map (!·) = some false
    rw [hc, hj]; rfl
  · refine Or.inr ⟨?_, j - 1, by omega, by omega, by omega, hi'⟩
    show s'.cf.map (!·) = some true
    rw [hc]; simp [hj]

/-- The slots a doubling of `R` writes are distinct. -/
theorem JacWinLay.rcbW_R (hL : JacWinLay K size) : (rcbW K.S K.R).Nodup := by
  have o := fun i j hi hj h => hL.oth_ne (K := K) (i := i) (j := j) hi hj h
  simp only [rcbW, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true]
  refine ⟨⟨o 7 8 (by decide) (by decide) (by decide), o 7 9 (by decide) (by decide) (by decide),
    o 7 10 (by decide) (by decide) (by decide), o 7 11 (by decide) (by decide) (by decide),
    o 7 12 (by decide) (by decide) (by decide), o 7 0 (by decide) (by decide) (by decide),
    o 7 1 (by decide) (by decide) (by decide), o 7 2 (by decide) (by decide) (by decide)⟩,
    ⟨o 8 9 (by decide) (by decide) (by decide), o 8 10 (by decide) (by decide) (by decide),
    o 8 11 (by decide) (by decide) (by decide), o 8 12 (by decide) (by decide) (by decide),
    o 8 0 (by decide) (by decide) (by decide), o 8 1 (by decide) (by decide) (by decide),
    o 8 2 (by decide) (by decide) (by decide)⟩,
    ⟨o 9 10 (by decide) (by decide) (by decide), o 9 11 (by decide) (by decide) (by decide),
    o 9 12 (by decide) (by decide) (by decide), o 9 0 (by decide) (by decide) (by decide),
    o 9 1 (by decide) (by decide) (by decide), o 9 2 (by decide) (by decide) (by decide)⟩,
    ⟨o 10 11 (by decide) (by decide) (by decide), o 10 12 (by decide) (by decide) (by decide),
    o 10 0 (by decide) (by decide) (by decide), o 10 1 (by decide) (by decide) (by decide),
    o 10 2 (by decide) (by decide) (by decide)⟩,
    ⟨o 11 12 (by decide) (by decide) (by decide), o 11 0 (by decide) (by decide) (by decide),
    o 11 1 (by decide) (by decide) (by decide), o 11 2 (by decide) (by decide) (by decide)⟩,
    ⟨o 12 0 (by decide) (by decide) (by decide), o 12 1 (by decide) (by decide) (by decide),
    o 12 2 (by decide) (by decide) (by decide)⟩,
    ⟨o 0 1 (by decide) (by decide) (by decide), o 0 2 (by decide) (by decide) (by decide)⟩,
    o 1 2 (by decide) (by decide) (by decide), not_false⟩

/-- What holds between doublings: the frame, the table, and `R` a Jacobian
triple of `Q`. -/
structure RSt (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (Q : Point C) (s : State) : Prop where
  fr : JFrame K C base size s₀ s
  tbl : TblOk K C base P 16 s
  lt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p
  rep : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z) Q

theorem RSt.rbxKeeps (hL : JacWinLay K size) {base : Addr} {P Q : Point C} {s₀ s s' : State}
    (h : RSt K C base size P s₀ Q s) (hk : Keeps [.rbx] s s') : RSt K C base size P s₀ Q s' := by
  have m : s'.mem = s.mem := hk.2.1
  have e : ∀ x, tmv C K.M.n base s' x = tmv C K.M.n base s x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [m]
  refine ⟨h.fr.next hL (h.fr.scr.of_keeps hk (by decide)) ((Keeps.regs hk).mono (sub_powClob (by decide)))
    (W := []) (by rw [m]; exact Unch.refl _ _ _) (by simp), fun j h1 hj => (h.tbl j h1 hj).congr
    fun c _ => by rw [m], fun x hx => by rw [m]; exact h.lt x hx, by rw [e, e, e]; exact h.rep⟩

/-- One doubling of `R`. -/
theorem dblR_ok (hL : JacWinLay K size) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl)
    {base : Addr} {P Q : Point C} (hQ : onCurve C Q = true) {s₀ s : State}
    (h : RSt K C base size P s₀ Q s) :
    WP isa (dbl K.R) s fun t => RSt K C base size P s₀ (Spec.Weierstrass.add Q Q) t ∧
      t.gpr .rbx = s.gpr .rbx := by
  have hs := h.fr.scr
  have hn := hs.nowrap
  have hRo : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ jwOther K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jw_mem
  have I0 : Inv K.M base size C.p (· ∈ jwSlots K) [K.R.x, K.R.y, K.R.z] (tmv C K.M.n base s) s :=
    ⟨hs, h.fr.mod, fun x hx => other_mem (hRo x hx), h.lt, fun _ _ => rfl⟩
  have hsl : ∀ x ∈ rcbW K.S K.R, x ∈ jwSlots K := by
    intro x hx
    simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> jw_mem
  refine WP.mono (hD hL.lay hL.rcbW_R hsl I0 hQ h.rep) fun t ⟨k, E, I, J⟩ => ?_
  have U : Unch base (jwLoopW K) s.mem t.mem :=
    k.loopW (rcbW_loopW fun x hx => other_loopW (hRo x hx))
  refine ⟨⟨h.fr.next hL (k.scr hs) k.regs U (jwLoopW_sub K), h.tbl.loopW hL U hn (by decide),
    fun x hx => I.lt x hx, ?_⟩, k.gpr _ (rbx_not_clob _)⟩
  have e : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base t x = E x := fun x hx => I.val x hx
  rw [e _ (by simp), e _ (by simp), e _ (by simp)]
  exact J

/-- `R = 32 R`, `rbx` the window index `j < 4096` before and after. -/
theorem dbls_ok (hL : JacWinLay K size) (hC : Law C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl)
    {base : Addr} {P : Point C} (hP : onCurve C P = true) {s₀ s : State} {e j : Nat} (hj : j < 4096)
    (hb : s.gpr .rbx = BitVec.ofNat 64 j) (h : RSt K C base size P s₀ (mul e P) s) :
    WP isa (K.dbls dbl) s fun t => RSt K C base size P s₀ (mul (32 * e) P) t ∧
      t.gpr .rbx = BitVec.ofNat 64 j := by
  rw [JacWinCfg.dbls]
  refine WP.seq (WP.mono (addRbx_ok s (c := 5 * 4096) (by decide) hb) fun s₁ ⟨b₁, k₁⟩ => ?_)
  refine aeLoop_ok (n := 5) (Inv := fun i t => RSt K C base size P s₀ (mul (2 ^ (5 - i) * e) P) t ∧
      t.gpr .rbx = BitVec.ofNat 64 (j + 4096 * i))
    (fun i t h1 h5 ⟨R, b⟩ => ?_) (fun t ⟨R, b⟩ => ⟨by simpa using R, by simpa using b⟩) (by decide)
    ⟨by simpa using h.rbxKeeps hL k₁, by rw [b₁]⟩
  rw [JacWinCfg.dblStep]
  refine WP.seq (WP.mono (dblR_ok hL hD (hC.onCurve_mul hP _) R) fun t₁ ⟨R₁, b₁'⟩ => ?_)
  refine WP.mono (dblCount_ok t₁ hj h1 h5 (by rw [b₁', b])) fun t₂ ⟨b₂, c₂, k₂⟩ => ⟨⟨?_, b₂⟩, c₂⟩
  have := R₁.rbxKeeps hL k₂
  rwa [hC.add_mul_mul hP, show 2 ^ (5 - i) * e + 2 ^ (5 - i) * e = 2 ^ (5 - (i - 1)) * e by
    rw [show 5 - (i - 1) = 5 - i + 1 by omega, Nat.pow_succ]; grind] at this

end VG.Proof.Weierstrass.X86_64
