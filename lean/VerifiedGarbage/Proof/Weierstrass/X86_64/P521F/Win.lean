module
-- separate module: the P-521 fast window's proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Weierstrass.X86_64.P521F.Madd
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinQuad
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJStep
import VerifiedGarbage.Proof.Weierstrass.X86_64.QuadCounter
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJLoop
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinLoop
import VerifiedGarbage.Proof.Weierstrass.WindowJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJNorm
public import VerifiedGarbage.Proof.Weierstrass.Booth
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJBuild
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# P-521's windows on x86-64 by the fast steps: an iteration

`R = 16 R` by four doublings in place (`quadF_ok`), and the mixed addition
(`sumF_ok`), as `quadJ_ok` and `sumJ_ok`, for a configuration whose slots
and code satisfy `FastCfg` (checked on the concrete one).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.P521F

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64.P521F
open VG.Impl.Weierstrass.X86_64.Mont (fnTmp)
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Proof.Weierstrass
  VG.Proof.Weierstrass.X86_64 Spec.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- What the fast doubling and addition need of a window configuration. -/
structure FastCfg (K : WinCfg) (C : Curve) (size : Nat) : Prop where
  ctx : StepCtx K.M size C.p (· ∈ winSlots K)
  dnd : (rcbW K.S K.R).Nodup
  dsl : ∀ x ∈ rcbW K.S K.R, x ∈ winSlots K
  dW : ∀ x ∈ rcbW K.S K.R, x ∈ winOther K
  dlow : ∀ x ∈ rcbW K.S K.R, x + 72 ≤ 3520
  dv0 : ∀ x ∈ [K.S.a, K.S.b3, K.zero], x ∉ rcbW K.S K.R
  dkb : KeepReg.keeps .rbx (dbl K.S K.R).inline = true
  dks : KeepReg.keeps .rsi (dbl K.S K.R).inline = true
  msl : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.E, x + 72 ≤ 3520 ∧ x ≠ 1
  mkb : KeepReg.keeps .rbx (madd K.S K.R K.E K.D).inline = true
  mks : KeepReg.keeps .rsi (madd K.S K.R K.E K.D).inline = true

/-! ## The count of four doublings -/

theorem quadStart4_ok (s : State) {i : Nat} (hb : s.gpr .rbx = BitVec.ofNat 64 i) :
    WP isa (.block [.alu .add .rbx (.imm 16384)]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 (i + 4096 * 4) ∧ Keeps [.rbx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left', hb]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e : (16384 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16384 := by decide
    rw [e, ← BitVec.ofNat_add]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem quadCount4_ok (s : State) {i j : Nat} (hi : i < 4096) (hj : 1 ≤ j) (hj' : j ≤ 4)
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
  · rw [sub]
    rw [e]
    congr 1
    simp only [BitVec.toNat_ofNat]
    apply propext
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem quadLoop4_ok {body : Prog isa} {Inv : Nat → State → Prop} {Q : State → Prop}
    (hstep : ∀ j s, 1 ≤ j → j ≤ 4 → Inv j s →
      WP isa body s fun s' => Inv (j - 1) s' ∧ s'.cf = some (decide (j - 1 = 0)))
    (hQ : ∀ s, Inv 0 s → Q s) {s : State} (hs : Inv 4 s) :
    WP isa (.loop body .ae) s Q := by
  refine WP.loop (M := isa) (fun j s => 1 ≤ j ∧ j ≤ 4 ∧ Inv j s) (fun j s ⟨h1, h2, hi⟩ => ?_) 4 s
    ⟨by decide, by decide, hs⟩
  refine WP.mono (hstep j s h1 h2 hi) fun s' ⟨hi', hc⟩ => ?_
  by_cases hj : j - 1 = 0
  · refine Or.inl ⟨?_, hQ s' (by rw [hj] at hi'; exact hi')⟩
    show s'.cf.map (!·) = some false
    rw [hc, hj]; rfl
  · refine Or.inr ⟨?_, j - 1, by omega, by omega, by omega, hi'⟩
    show s'.cf.map (!·) = some true
    rw [hc]; simp [hj]

/-! ## `R = 16 R` -/

/-- A `ProgKeep` of writes to `R` and the temporaries keeps the window's other slots. -/
theorem unchR {K : WinCfg} {C : Curve} {size : Nat} (hFC : FastCfg K C size) {base : Addr} {s t : State}
    (h : ProgKeep K.M base (rcbW K.S K.R) s t) : Unch base (loopW K) s.mem t.mem :=
  h.unch.mono fun w hw => by
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · exact Or.inl ⟨y, hFC.dW y hy, rfl⟩
    · exact Or.inr rfl

/-- `R = 16 R` in Jacobian coordinates, in place, by four doublings: as `quadJ_ok`. -/
theorem quadF_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hFC : FastCfg K C size) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) {Rp : Fe C → Fe C → Fe C → Point C → Prop} {s₀ s : State}
    (hF : WinFixed K C base s₀ P k) (hS : WinStR K C base size Rp P s₀ s) {i : Nat} (hi : i < 4096)
    (hb : s.gpr .rbx = BitVec.ofNat 64 i) {e : Nat}
    (hlt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
      (mul e P)) :
    WP isa (Win.quadF K).inline s fun s' =>
      WinStR K C base size Rp P s₀ s' ∧ s'.gpr .rbx = s.gpr .rbx ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      InvJ C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (mul (16 * e) P) := by
  obtain ⟨-, -, ro_lt, -⟩ := hS.ro_tmv hL hF
  have oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  let V := [K.R.x, K.R.y, K.R.z, K.S.a, K.S.b3, K.zero]
  have V0 : ∀ x ∈ V, x ∈ winSlots K ∧ wordsVal s.mem base x K.M.n < C.p := by
    intro x hx
    simp only [V, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨winOther_mem (oR _ (by simp)), hlt _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hlt _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hlt _ (by simp)⟩
    all_goals exact ⟨by win_mem, ro_lt _ (by simp [winRo])⟩
  have I₀ : Inv K.M base size C.p (· ∈ winSlots K) V (tmv C K.M.n base s) s :=
    ⟨hS.scr, hS.mod, fun x hx => (V0 x hx).1, fun x hx => (V0 x hx).2, fun _ _ => rfl⟩
  have hQ := fun (a : Nat) => hC.onCurve_mul hP a
  rw [Win.quadF]
  simp only [Code.inline]
  refine WP.seq (WP.mono (quadStart4_ok s hb) fun s₂ ⟨b₂, kc₂⟩ => ?_)
  let LI := fun j st => WinStR K C base size Rp P s₀ st ∧
    st.gpr .rbx = BitVec.ofNat 64 (i + 4096 * j) ∧ ∃ E : Nat → Fe C,
    Inv K.M base size C.p (· ∈ winSlots K) V E st ∧
    InvJ C (E K.R.x) (E K.R.y) (E K.R.z) (mul (2 ^ (4 - j) * e) P)
  have start : LI 4 s₂ := ⟨hS.rbxKeeps hL kc₂, b₂, _, I₀.rbxKeeps kc₂, by simpa using hR⟩
  have body : ∀ j st, 1 ≤ j → j ≤ 4 → LI j st →
      WP isa (Code.seq (dbl K.S K.R).inline (.block [.alu .sub .rbx (.imm 4096), .alu .cmp .rbx (.imm 4096)])) st
        fun st' => LI (j - 1) st' ∧ st'.cf = some (decide (j - 1 = 0)) := by
    intro j st hj hj' ⟨S, b, E, I, J⟩
    refine WP.seq (WP.mono (dblF_ok hFC.ctx hC hM3 hFC.dnd hFC.dsl hFC.dlow hFC.dv0 hFC.dkb hFC.dks
      (V0 := [K.S.a, K.S.b3, K.zero]) I (hQ _) J) fun st₁ ⟨k₁, kw₁, E₁, I₁, _, J₁⟩ => ?_)
    have pk₁ := progKeep_of hFC.ctx k₁ kw₁
    have S₁ := S.next hL I₁.scr ((by rw [← hFC.ctx.n9] at k₁; exact k₁ : KeepRegs (clob K.M.n) st st₁).mono
      clob_powClob) (unchR hFC pk₁)
    rw [hC.double hP] at J₁
    have ar : 2 * (2 ^ (4 - j) * e) = 2 ^ (4 - (j - 1)) * e := by
      have hj4 : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
      rcases hj4 with rfl | rfl | rfl | rfl <;> simp <;> omega
    rw [ar] at J₁
    have b' : st₁.gpr .rbx = BitVec.ofNat 64 (i + 4096 * j) := by
      rw [k₁.gpr _ (by decide), b]
    refine WP.mono (quadCount4_ok st₁ hi hj hj' b') fun st₃ ⟨b₃, c₃, kc₃⟩ => ?_
    exact ⟨⟨S₁.rbxKeeps hL kc₃, b₃, E₁, I₁.rbxKeeps kc₃, J₁⟩, c₃⟩
  refine WP.mono (quadLoop4_ok body (fun _ h => h) start) fun s₅ ⟨S₅, b₅, E₅, I₅, J₅⟩ => ?_
  have rb₅ : s₅.gpr .rbx = s.gpr .rbx := by simpa only [Nat.mul_zero, Nat.add_zero, hb] using b₅
  have J₅ : InvJ C (E₅ K.R.x) (E₅ K.R.y) (E₅ K.R.z) (mul (16 * e) P) := by simpa using J₅
  have hRV : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ V := by
    intro x hx; simp only [V, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with h | h | h <;> simp [h]
  refine ⟨S₅, rb₅, fun x hx => I₅.lt x (hRV x hx), ?_⟩
  show InvJ C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
  rw [I₅.val _ (hRV _ (by simp)), I₅.val _ (hRV _ (by simp)), I₅.val _ (hRV _ (by simp))]
  exact J₅

/-! ## The mixed addition -/

/-- `R = R + E` as `sumJ_ok`, by `madd`. -/
theorem sumF_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hFC : FastCfg K C size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    {Rp : Fe C → Fe C → Fe C → Point C → Prop} {s₀ s : State} (hF : WinFixed K C base s₀ P k)
    (hS : WinStR K C base size Rp P s₀ s) {QR QE : Point C} (hQR : onCurve C QR = true)
    (hQE : onCurve C QE = true)
    (hltR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hltE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z) QR)
    (hE : RepA C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) QE)
    (hsep : QR ≠ .infinity → QE ≠ .infinity → QR ≠ QE) :
    WP isa (Code.seq (madd K.S K.R K.E K.D) (.block (WinCfg.selSum K))).inline s fun s' =>
      WinStR K C base size Rp P s₀ s' ∧ s'.gpr .rbx = s.gpr .rbx ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      InvJ C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (Spec.Weierstrass.add QR QE) := by
  obtain ⟨-, -, ro_lt, -⟩ := hS.ro_tmv hL hF
  have oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  have oE := pt_other (K := K) (p := K.E) (Or.inr (Or.inl rfl))
  have oD := pt_other (K := K) (p := K.D) (Or.inr (Or.inr rfl))
  have sl := fun (P : Pt) (h : ∀ x ∈ [P.x, P.y, P.z], x ∈ winOther K) x (hx : x ∈ [P.x, P.y, P.z]) =>
    winOther_mem (h x hx)
  have w1 := winJ_sl oD (sl _ oR) (sl _ oE)
  have V0 : ∀ x ∈ rcbR K.S K.R K.E, x ∈ winSlots K ∧ wordsVal s.mem base x K.M.n < C.p := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by win_mem, ro_lt _ (by simp [winRo])⟩
    · exact ⟨by win_mem, ro_lt _ (by simp [winRo])⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hltR _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hltR _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hltR _ (by simp)⟩
    · exact ⟨winOther_mem (oE _ (by simp)), hltE _ (by simp)⟩
    · exact ⟨winOther_mem (oE _ (by simp)), hltE _ (by simp)⟩
    · exact ⟨winOther_mem (oE _ (by simp)), hltE _ (by simp)⟩
  have I₀ : Inv K.M base size C.p (· ∈ winSlots K) (rcbR K.S K.R K.E) (tmv C K.M.n base s) s :=
    ⟨hS.scr, hS.mod, fun x hx => (V0 x hx).1, fun x hx => (V0 x hx).2, fun _ _ => rfl⟩
  show WP isa (Code.seq (madd K.S K.R K.E K.D).inline (.block (WinCfg.selSum K))) s _
  have hSlF : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.E, x ∈ winSlots K ∧ x + 72 ≤ 3520 ∧ x ≠ 1 :=
    fun x hx => ⟨w1.1 x hx, hFC.msl x hx⟩
  refine WP.seq (WP.mono (maddF_ok hFC.ctx (hL.rcbApart_D (Or.inr rfl)) hSlF I₀ (fun x hx => hx) hFC.mkb hFC.mks)
    fun s₁ ⟨pk₁, I₁, v₁⟩ => ?_)
  have k₁ : KeepRegs (clob K.M.n) s s₁ := ⟨pk₁.gpr, pk₁.rd, pk₁.wr⟩
  have U₁ : Unch base (loopW K) s.mem s₁.mem := pk₁.unch.mono fun w hw => by
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · exact Or.inl ⟨y, w1.2 y hy, rfl⟩
    · exact Or.inr rfl
  have o₁ : ∀ x, x ∉ rcbW K.S K.D → runOps (maddJ K.S K.R K.E K.D) (tmv C K.M.n base s) x =
      tmv C K.M.n base s x := fun x hx =>
    runOps_of_not_out _ _ fun op hop h => hx (h ▸ ofN_out maddJN_ok op (by rw [← maddJ_eq]; exact hop))
  set E₁ := runOps (maddJ K.S K.R K.E K.D) (tmv C K.M.n base s)
  have S₁ := hS.next hL I₁.scr (k₁.mono clob_powClob) U₁
  -- `R` and `E` kept, `D` the sum.
  obtain ⟨-, -, -, hRo, -, -, -, hEo, -, -⟩ := hL.other_ne
  have nD : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z], x ∉ rcbW K.S K.D := by
    intro x hx h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    have h1 : ∀ y ∈ [K.R.x, K.R.y, K.R.z], y ∉ rcbW K.S K.D := fun y hy h =>
      hRo y hy (List.mem_append_right _ h)
    have h2 : ∀ y ∈ [K.E.x, K.E.y, K.E.z], y ∉ rcbW K.S K.D := fun y hy h =>
      hEo y hy (List.mem_cons_of_mem _ h)
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1 _ (by simp) h
    · exact h1 _ (by simp) h
    · exact h1 _ (by simp) h
    · exact h2 _ (by simp) h
    · exact h2 _ (by simp) h
    · exact h2 _ (by simp) h
  have inV : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z],
      x ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.R K.E := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append] at hx ⊢
    rcases hx with h | h | h | h | h | h | h | h | h <;> simp [h]
  have v₁' : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z],
      toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₁.mem base x K.M.n) = tmv C K.M.n base s x := fun x hx => by
    rw [I₁.val x (inV x (by sub_mem hx)), o₁ x (nD x hx)]
  have lt₁ : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z],
      wordsVal s₁.mem base x K.M.n < C.p := fun x hx => I₁.lt x (inV x hx)
  have vD : (toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₁.mem base K.D.x K.M.n),
      toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₁.mem base K.D.y K.M.n),
      toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₁.mem base K.D.z K.M.n)) =
      maddJF (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
        (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) := by
    refine Eq.trans ?_ (v₁.trans (maddJN_run _))
    rw [I₁.val _ (inV _ (by simp)), I₁.val _ (inV _ (by simp)), I₁.val _ (inV _ (by simp))]
  have jx := congrArg Prod.fst vD
  have jy := congrArg (fun t => t.2.1) vD
  have jz := congrArg (fun t => t.2.2) vD
  dsimp only at jx jy jz
  refine WP.mono (selSum_ok hL I₁.scr) fun s₂ ⟨r2x, r2y, r2z, k₂, U₂⟩ => ?_
  have c : ∀ r ∈ [Reg.rax, .rcx, .rdx], r ∈ powClob K.M.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [powClob, clob]
  have S₂ := S₁.next hL (I₁.scr.of_keepRegs k₂ (by decide)) (k₂.mono c) U₂
  have tz1 := v₁' K.R.z (by simp)
  have tz2 := v₁' K.E.z (by simp)
  have l1 := lt₁ K.R.z (by simp)
  have l2 := lt₁ K.E.z (by simp)
  refine ⟨S₂, by rw [k₂.gpr _ (by decide), k₁.gpr _ (rbx_not_clob _)], fun x hx => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [r2x, selVal]; split
      · exact lt₁ _ (by simp)
      · split <;> exact lt₁ _ (by simp)
    · rw [r2y, selVal]; split
      · exact lt₁ _ (by simp)
      · split <;> exact lt₁ _ (by simp)
    · rw [r2z, selVal]; split
      · exact lt₁ _ (by simp)
      · split <;> exact lt₁ _ (by simp)
  · show InvJ C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [r2x, r2y, r2z, toM_selVal hp tz1 l1 tz2 l2 (v₁' _ (by simp)) (v₁' _ (by simp)) jx,
      toM_selVal hp tz1 l1 tz2 l2 (v₁' _ (by simp)) (v₁' _ (by simp)) jy,
      toM_selVal hp tz1 l1 tz2 l2 (v₁' _ (by simp)) (v₁' _ (by simp)) jz]
    exact InvJ.sumSelM hC hM3 hQR hQE hR hE hsep


/-! ## An iteration -/

/-- An iteration but the last, `rbx = j ≥ 2` to `j - 1`: adds digit `j - 1`. -/
theorem winStepF_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hFC : FastCfg K C size)
    (hX : WinX K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true) (hP0 : P ≠ .infinity)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s₀ : State} (hF : WinFixed K C base s₀ P k)
    (hk8 : 8 * geom K.J ≤ k) {j : Nat} (hj : 2 ≤ j) (hjn : j ≤ K.J)
    (hb : 16 * winE k K.J j + 8 < C.n) {s : State} (hI : WinInvJ K C base size k P s₀ s j) :
    WP isa (Win.stepF K).inline s fun s' =>
      WinInvJ K C base size k P s₀ s' (j - 1) ∧ s'.zf = some (decide (j - 1 = 1)) := by
  have hJ := hL.J
  rw [Win.stepF]
  simp only [Code.inline]
  refine WP.seq (WP.mono (decRbx_ok s (by omega_using [hj]) (by omega_using [hjn, hJ]) hI.rbx) fun s₁ ⟨b₁, k₁⟩ => ?_)
  have hS₁ := hI.st.rbxKeeps hL k₁
  have lt₁ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₁.mem base x K.M.n < C.p := by
    rw [k₁.2.1]; exact hI.lt
  have rep₁ : InvJ C (tmv C K.M.n base s₁ K.R.x) (tmv C K.M.n base s₁ K.R.y)
      (tmv C K.M.n base s₁ K.R.z) (mul (winE k K.J j) P) := by
    have e : ∀ x, tmv C K.M.n base s₁ x = tmv C K.M.n base s x := fun x => by
      show toM _ _ _ = toM _ _ _; rw [k₁.2.1]
    rw [e, e, e]; exact hI.rep
  refine WP.seq (WP.mono (quadF_ok hL hFC hC hM3 hP hF hS₁ (i := j - 1) (by omega_using [hjn, hJ]) b₁ lt₁ rep₁)
    fun s₅ ⟨S₅, x₅, l₅, r₅⟩ => ?_)
  have hx₅ : s₅.gpr .rbx = BitVec.ofNat 64 (j - 1) := by rw [x₅, b₁]
  obtain ⟨-, -, -, hz₅⟩ := S₅.ro_tmv hL hF
  have hbits₅ : ∀ t < 4 * K.J, s₅.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by
      have := hL.bits
      rw [S₅.unch.byte (fun w hw => by have := hL.bits_w w hw; omega_using [ht, this]) (by have := S₅.scr.nowrap; omega)]
      exact hF.bits t ht
  refine WP.seq (WP.mono (winEntryR_ok hL hX (RepA.infinity hC) RepA.negY (P := P) hpn hone_lt hone
    S₅.scr S₅.mod (i := j - 1) (by omega_using [hjn, hJ]) hx₅ hbits₅ hz₅ S₅.tbl) fun s₆ h₆ => WP.seq (WP.mono h₆
      fun s₇ E₇ => ?_))
  have hn := S₅.scr.nowrap
  have S₇ := S₅.next hL E₇.scr (E₇.keep.mono clob_powClob) (E₇.unch.mono (entryW_loopW K))
  have eR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₇.mem base x K.M.n = wordsVal s₅.mem base x K.M.n :=
    fun x hx => E₇.unch.wordsVal (R_apart_entry hL hx) (by
      have := hL.lay.le x (winOther_mem (pt_other (K := K) (p := K.R) (Or.inl rfl) x hx)); omega_using [hn, this])
  have lt₇ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₇.mem base x K.M.n < C.p := fun x hx => by
    rw [eR x hx]; exact l₅ x hx
  have rep₇ : InvJ C (tmv C K.M.n base s₇ K.R.x) (tmv C K.M.n base s₇ K.R.y)
      (tmv C K.M.n base s₇ K.R.z) (mul (16 * winE k K.J j) P) := by
    have e : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base s₇ x = tmv C K.M.n base s₅ x := fun x hx => by
      show toM _ _ _ = toM _ _ _; rw [eR x hx]
    rw [e _ (by simp), e _ (by simp), e _ (by simp)]; exact r₅
  have hsep := win_sep hC hO hP hP0 (k := k) (J := K.J) (j := j - 1)
    (by rw [Nat.sub_add_cancel (by omega_using [hj] : 1 ≤ j)]; exact hb)
  rw [Nat.sub_add_cancel (by omega_using [hj] : 1 ≤ j)] at hsep
  refine WP.seq (WP.mono (sumF_ok hL hFC hp hC hM3 hF S₇ (hC.onCurve_mul hP _)
    (onCurve_winPt hC hP k (j - 1)) lt₇ E₇.lt rep₇ E₇.rep (fun h1 _ => (hsep h1).1))
    fun s₈ ⟨S₈, x₈, l₈, r₈⟩ => ?_)
  have hadd := win_add hC hP (k := k) (J := K.J) (j := j - 1) hk8 (by omega_using [hjn, hJ])
  rw [Nat.sub_add_cancel (by omega_using [hj] : 1 ≤ j)] at hadd
  rw [hadd] at r₈
  have hx₇ : s₇.gpr .rbx = BitVec.ofNat 64 (j - 1) := by rw [E₇.keep.gpr _ (rbx_not_clob _), hx₅]
  have hx₈ : s₈.gpr .rbx = BitVec.ofNat 64 (j - 1) := by rw [x₈, hx₇]
  refine WP.mono (cmpRbx_ok s₈ (j := j - 1) (i := 1) (by decide) (by omega_using [hjn, hJ]) hx₈) fun s₉ ⟨z₉, k₉⟩ => ⟨?_, z₉⟩
  refine ⟨S₈.rbxKeeps hL ((Keeps.mono k₉ (fun _ h => absurd h List.not_mem_nil))), by rw [k₉.1 _ (by simp), hx₈],
    by rw [k₉.2.1]; exact l₈, ?_⟩
  have e : ∀ x, tmv C K.M.n base s₉ x = tmv C K.M.n base s₈ x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [k₉.2.1]
  rw [e, e, e]; exact r₈


/-! ## The window method -/

/-- `[k - 8 Σ_{i<J} 16^i]P` into `R`, for `8 Σ_{i<J} 16^i ≤ k < 16^J` whose bits
are the table at `K.bits`, by windows in Jacobian coordinates with an affine
table (by the inversion `inv`, writing `IW`): for `P ≠ O` on a curve of
prime order `n` (`PrimeOrder`), with `16 winE k J 2 + 8 < n` (so that no
addition but the last is of equal or opposite points); only `invClob`,
`winW` and `IW` change. -/
theorem windowF_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hFC : FastCfg K C size)
    (hX : WinX K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true) (hP0 : P ≠ .infinity)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {inv : Prog isa} {IW : List (Nat × Nat)}
    (hI : InvSpecW K C base size inv IW) {s₀ : State} (hs : Scr s₀ base size)
    (hM : ModOkW K.M size C.p s₀.mem base) (hF₀ : WinFixed K C base s₀ P k) (hk : k < 16 ^ K.J)
    (hk8 : 8 * geom K.J ≤ k) (hJ2 : 2 ≤ K.J) (hb : 16 * winE k K.J 2 + 8 < C.n) :
    WP isa (Win.windowF K inv).inline s₀ fun s' => KeepRegs (invClob K.M.n) s₀ s' ∧
      Unch base (winW K ++ IW) s₀.mem s'.mem ∧ ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (mul (k - 8 * geom K.J) P) := by
  have hn := hs.nowrap
  have hJ := hL.J
  have hne : ∀ m, 1 ≤ m → m ≤ 8 → mul m P ≠ .infinity := by
    intro m h1 h8 h
    have h0 : zmul (m : Int) P = zmul 0 P := by
      rw [zmul_natCast, h, show (0 : Int) = ((0 : Nat) : Int) from rfl, zmul_natCast]
      rw [Spec.Weierstrass.mul]; simp
    have := hO.zmul_eq hC hP hP0 (by omega_arith) h0
    omega_arith
  have pc : ∀ r ∈ powClob K.M.n, r ∈ invClob K.M.n := fun r h => List.mem_cons_of_mem _ h
  rw [Win.windowF]
  simp only [Code.inline]
  refine WP.seq (WP.mono (build_ok hL hp hC hM3 hP hs hM hF₀) fun sb B => ?_)
  refine WP.seq (WP.mono (normTbl_ok hL hp hC hpn hone_lt hone hne hI B.scr B.mod B.tbl)
    fun s ⟨hs', Kn, Un, hM', T⟩ => ?_)
  have U₀ : Unch base (winW K ++ IW) s₀.mem s.mem := (B.unch.trans Un).mono fun w hw => by
    simp only [List.mem_append] at hw ⊢; rcases hw with hw | hw | hw <;> simp [hw]
  have hF : WinFixed K C base s P k := by
    refine hF₀.unch hL U₀ hn (fun x hx w hw => ?_) (fun w hw => ?_)
    · rcases List.mem_append.mp hw with hw | hw
      · exact hL.ro_w hx w hw
      · rcases hI.w w hw with rfl | rfl | ⟨-, h⟩
        · exact hL.lay.apart x _ (winRo_slots K x hx) (winOther_mem (by win_mem))
            fun e => hL.ro x hx (e ▸ by win_mem)
        · exact hL.lay.tmp x (winRo_slots K x hx)
        · exact h x (winRo_slots K x hx)
    · rcases List.mem_append.mp hw with hw | hw
      · exact hL.bits_w w hw
      · exact hI.bits w hw
  have S₁ : WinStR K C base size (RepA C) P s s := ⟨hs', ⟨fun _ _ => rfl, rfl, rfl⟩, Unch.refl _ _ _, hM', T⟩
  obtain ⟨rxy, rxz, ryz, -⟩ := hL.other_ne
  have wR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winOther K := pt_other (Or.inl rfl)
  have le : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x + 8 * K.M.n ≤ size := fun x hx =>
    hL.lay.le x (winOther_mem (wR x hx))
  have ap := fun {x y} (hx : x ∈ [K.R.x, K.R.y, K.R.z]) (hy : y ∈ [K.R.x, K.R.y, K.R.z]) (h : x ≠ y) =>
    hL.apart₂ (winOther_ws K x (wR x hx)) (winOther_ws K y (wR y hy)) h
  have axy := ap (x := K.R.x) (y := K.R.y) (by simp) (by simp) rxy
  have axz := ap (x := K.R.x) (y := K.R.z) (by simp) (by simp) rxz
  have ayz := ap (x := K.R.y) (y := K.R.z) (by simp) (by simp) ryz
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hone_lt
  refine WP.seq ?_
  rw [WinCfg.init, List.append_assoc, List.append_assoc, WP.block_append_iff]
  have W1 := setConst_ok S₁.scr (n := K.M.n) (o := K.R.x) (x := 0) (le _ (by simp)) (Nat.two_pow_pos _)
  refine WP.mono W1 fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := S₁.scr.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  have W2 := setConst_ok hs₂ (n := K.M.n) (o := K.R.y) (x := K.one) (le _ (by simp))
    (Nat.lt_trans hone_lt hpn)
  refine WP.mono W2 fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [WP.block_append_iff]
  have W3 := setConst_ok hs₃ (n := K.M.n) (o := K.R.z) (x := 0) (le _ (by simp)) (Nat.two_pow_pos _)
  refine WP.mono W3 fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  refine WP.mono (mov32Rbx_ok s₄ (j := K.J) (by omega_arith)) fun s₅ ⟨b₅, k₅⟩ => ?_
  have hU : Unch base (loopW K) s.mem s₅.mem := by
    rw [k₅.2.1]
    refine (O₂.unch.trans (O₃.unch.trans O₄.unch)).mono fun w hw => ?_
    simp only [List.mem_append, List.mem_singleton] at hw
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton]
    refine Or.inl ⟨w.1, ?_, ?_⟩
    · rcases hw with rfl | rfl | rfl
      · exact wR _ (by simp)
      · exact wR _ (by simp)
      · exact wR _ (by simp)
    · rcases hw with rfl | rfl | rfl <;> rfl
  have c1 : ∀ r ∈ [Reg.rax], r ∈ powClob K.M.n := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [powClob, clob]
  have S₅ : WinStR K C base size (RepA C) P s s₅ := S₁.next hL (hs₄.of_keeps k₅ (by decide))
    ((((k₂.mono c1).trans (k₃.mono c1)).trans (k₄.mono c1)).trans
      ((Keeps.regs k₅).mono (by intro r hr; simp only [List.mem_singleton] at hr; subst hr
                                simp [powClob]))) hU
  have b64 : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := le x hx; omega_arith
  have vx : wordsVal s₅.mem base K.R.x K.M.n = 0 := by
    rw [k₅.2.1, O₄.wordsVal axz (b64 _ (by simp)), O₃.wordsVal axy (b64 _ (by simp)), e₂]
  have vy : wordsVal s₅.mem base K.R.y K.M.n = K.one := by
    rw [k₅.2.1, O₄.wordsVal ayz (b64 _ (by simp)), e₃]
  have vz : wordsVal s₅.mem base K.R.z K.M.n = 0 := by rw [k₅.2.1, e₄]
  have I₅ : WinInvJ K C base size k P s s₅ K.J := by
    refine ⟨S₅, b₅, fun x hx => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · rw [vx]; exact hp0
      · rw [vy]; exact hone_lt
      · rw [vz]; exact hp0
    · refine Or.inl ⟨by rw [winE_top hk, mul_zero_pt'], ?_⟩
      show toM _ _ _ = 0
      rw [vz]; exact toM_zero _ _
  refine WP.seq (countLoop_ok (Inv := fun i t => WinInvJ K C base size k P s t (i + 1)) (n := K.J - 1)
    (fun i t h1 h2 hi => WP.mono (winStepF_ok hL hFC hX hp hC hM3 hO hP hP0 hpn hone_lt hone hF hk8
      (j := i + 1) (by omega_arith) (by omega_arith)
      (Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.mul_le_mul_left _
        (winE_le_of_le hk8 (by omega_arith) (by omega_arith))) _) hb) hi)
      fun u ⟨I, z⟩ => ⟨by rw [show i - 1 + 1 = i + 1 - 1 by omega_arith]; exact I,
        by rw [z]; congr 1; simp only [decide_eq_decide]; omega_arith⟩)
    (fun t hi => WP.mono (stepLast_ok hL hX hp hC hM3 hP hpn hone_lt hone hF hk8 hi)
      fun u ⟨S, l, r⟩ => ⟨((B.keep.mono pc).trans Kn).trans (S.keep.mono pc),
        (U₀.trans S.unch).mono fun w hw => by
          simp only [List.mem_append] at hw ⊢; rcases hw with (hw | hw) | hw <;> simp [hw],
        S.mod, l, by rw [← winE_zero]; exact r⟩)
    (by omega_arith) (by rw [Nat.sub_add_cancel (by omega_arith)]; exact I₅))


end VG.Proof.Weierstrass.X86_64.P521F
