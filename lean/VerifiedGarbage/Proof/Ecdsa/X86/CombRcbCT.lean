module

public import VerifiedGarbage.Proof.Ecdsa.X86.CombTaint
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Weierstrass.X86.TCombRcb
import VerifiedGarbage.Proof.Ecdsa.X86.GMul

/-!
# ECDSA on x86 (32-bit): the constant time of the comb by complete additions

`[k]G` by `TCombCfg.comb` leaks the same for any two scalars
(`gMulRcb_rel`, the `GMulRel` its callers' stages take), for any curve, given
the taint checks of its code (`CombRcbCT`: the constant, the start and an
iteration, each a curve's own instructions, checked for it). An iteration
is checked from the taint in which the counter, the working space and the
word holding the tables' address are public, which the comb's invariant
(`TCombInv`, of both runs) gives again after it: the entries read are at the
address the table of iteration `esi` has, the same in both runs, and every
entry of it is read whatever the digit.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

/-- The taint checks of a curve's comb by complete additions: `3b` to `EM`
and the start, from the working space's address; an iteration, from the
comb's taint; and the stack an iteration uses. -/
structure CombRcbCT (c : Cfg) (d : CombData) : Prop where
  prep : RelCT isa (VG.X86.Taint.Agree (τr [.edi]))
    (.block (Impl.Weierstrass.X86.setConst c.n (c.sl EM) (c.mont (3 * c.C.b)))) (fun _ _ => True)
  init : RelCT isa (VG.X86.Taint.Agree (τr [.edi])) (.block (c.combCfg d).init) (fun _ _ => True)
  step : ∀ b, RelCT isa (VG.X86.Taint.Agree (combτAt b)) (c.combCfg d).step (fun _ _ => True)
  sp : SpOk (c.combCfg d).step 20

variable {c : Cfg} {d : CombData} {scratchSecond : Bool}

/-- The comb's invariant supplies the public values an iteration's taint
check starts from, whatever the two scalars. -/
theorem combRcbInv_agree {base T : Addr} {s₀ t₀ s t : State} {k₁ k₂ j : Nat}
    (wf₁ : VG.X86.Taint.Wf (combτAt scratchSecond) s₀) (wf₂ : VG.X86.Taint.Wf (combτAt scratchSecond) t₀)
    (hw : s₀.wr = t₀.wr) (he : s₀.gpr .esp = t₀.gpr .esp)
    (h₁ : TCombInv (c.combCfg d) c.C base size k₁ T (c.combWords d) s₀ s j)
    (h₂ : TCombInv (c.combCfg d) c.C base size k₂ T (c.combWords d) t₀ t j) :
    VG.X86.Taint.Agree (combτAt scratchSecond) s t := by
  have w₁ := combWf_keep wf₁ h₁.keep.wr (h₁.keep.gpr _ (by decide)) (h₁.keep.gpr _ (by decide))
  have w₂ := combWf_keep wf₂ h₂.keep.wr (h₂.keep.gpr _ (by decide)) (h₂.keep.gpr _ (by decide))
  refine combAgree w₁ w₂ (by rw [h₁.keep.wr, h₂.keep.wr, hw])
    (h₁.esi.trans h₂.esi.symm) (widen32_inj (h₁.scr.edi.trans h₂.scr.edi.symm))
    (by rw [h₁.keep.gpr _ (by decide), h₂.keep.gpr _ (by decide), he]) ?_
  have b₁ := w₁.bases (.edi, combRegion scratchSecond, 0) (List.mem_singleton_self _)
  have b₂ := w₂.bases (.edi, combRegion scratchSecond, 0) (List.mem_singleton_self _)
  change addr (s.gpr .edi) 0 = (VG.X86.Taint.region s (combRegion scratchSecond)).base at b₁
  change addr (t.gpr .edi) 0 = (VG.X86.Taint.region t (combRegion scratchSecond)).base at b₂
  simp only [addr, BitVec.add_zero] at b₁ b₂
  have b₁' : (VG.X86.Taint.region s (combRegion scratchSecond)).base = base := b₁.symm.trans h₁.scr.edi
  have b₂' : (VG.X86.Taint.region t (combRegion scratchSecond)).base = base := b₂.symm.trans h₂.scr.edi
  simp only [VG.X86.Taint.byteAddr, b₁', b₂']
  exact widen32_inj (h₁.tsym.trans h₂.tsym.symm)

/-- The comb's loop leaks the same for two scalars: the invariant gives the
public table address again after each iteration. -/
theorem combRcbLoop_rel (hL : TCombLay (c.combCfg d) size) (hT : TCombTop (c.combCfg d)) (hC : Law c.C)
    (hG : onCurve c.C (G c.C) = true) (hV : TCombVals (c.combCfg d) c.C d.tbl)
    (hpn : c.C.p < 2 ^ (64 * (c.combCfg d).M.n)) (ct : CombRcbCT c d)
    {base T : Addr} {s₀ t₀ : State} {k₁ k₂ : Nat}
    (hF₁ : TCombFixed (c.combCfg d) c.C base size s₀ k₁ T (c.combWords d))
    (hF₂ : TCombFixed (c.combCfg d) c.C base size t₀ k₂ T (c.combWords d))
    (hb₁ : tmv c.C (c.combCfg d).M.n base s₀ (c.combCfg d).S.b3 = Fin.ofNat c.C.p (3 * c.C.b))
    (hb₂ : tmv c.C (c.combCfg d).M.n base t₀ (c.combCfg d).S.b3 = Fin.ofNat c.C.p (3 * c.C.b))
    (wf₁ : VG.X86.Taint.Wf (combτAt scratchSecond) s₀) (wf₂ : VG.X86.Taint.Wf (combτAt scratchSecond) t₀)
    (hw : s₀.wr = t₀.wr) (he : s₀.gpr .esp = t₀.gpr .esp) (n : Nat) :
    RelCT isa (fun s t => 1 ≤ n ∧ n ≤ (c.combCfg d).J ∧
      TCombInv (c.combCfg d) c.C base size k₁ T (c.combWords d) s₀ s n ∧
      TCombInv (c.combCfg d) c.C base size k₂ T (c.combWords d) t₀ t n)
      (.loop (c.combCfg d).step .ne) (fun _ _ => True) := by
  let I := fun n s t => 1 ≤ n ∧ n ≤ (c.combCfg d).J ∧
      TCombInv (c.combCfg d) c.C base size k₁ T (c.combWords d) s₀ s n ∧
      TCombInv (c.combCfg d) c.C base size k₂ T (c.combWords d) t₀ t n
  refine RelCT.loop (M := isa) I (fun j => ?_) n
  have step : RelCT isa (I j) (c.combCfg d).step (fun _ _ => True) :=
    (ct.step scratchSecond).mono (fun _ _ h => combRcbInv_agree wf₁ wf₂ hw he h.2.2.1 h.2.2.2)
      (fun _ _ _ => trivial)
  have step' := step.wp (F₁ := fun (s : State) =>
      TCombInv (c.combCfg d) c.C base size k₁ T (c.combWords d) s₀ s (j - 1) ∧
        s.zf = some (decide (j - 1 = 0)))
    (F₂ := fun (t : State) =>
      TCombInv (c.combCfg d) c.C base size k₂ T (c.combWords d) t₀ t (j - 1) ∧
        t.zf = some (decide (j - 1 = 0)))
    (fun _ _ h => ⟨step_ok hL hT hC hG hV hpn hF₁ hb₁ h.1 h.2.1 h.2.2.1 ct.sp,
      step_ok hL hT hC hG hV hpn hF₂ hb₂ h.1 h.2.1 h.2.2.2 ct.sp⟩)
  intro s t tr₁ tr₂ s' t' h e₁ e₂
  obtain ⟨eqtr, _, ⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ := step' _ _ _ _ _ _ h e₁ e₂
  have ev₁ : isa.eval .ne s' = some !decide (j - 1 = 0) := by change s'.zf.map (!·) = _; rw [z₁]; rfl
  have ev₂ : isa.eval .ne t' = some !decide (j - 1 = 0) := by change t'.zf.map (!·) = _; rw [z₂]; rfl
  refine ⟨eqtr, by rw [ev₁, ev₂], fun _ => trivial, fun ht => ?_⟩
  have hj' : j - 1 ≠ 0 := by
    rw [ev₁] at ht
    simpa using ht
  exact ⟨j - 1, by omega_using [hj'], by omega_using [hj'], by have := h.2.1; omega_using [this], i₁, i₂⟩

/-- `[k]G` by the comb by complete additions is constant time for two
arbitrary scalars when its working space's and tables' addresses agree. -/
theorem gMulRcb_rel (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c) (hcd : c.comb = some d)
    (hd : CombOk c d) (hj : d.jac = false) (ct : CombRcbCT c d) : GMulRel c d scratchSecond := by
  intro base g₁ g₂ s₀ t₀ k₁ k₂ hs₁ hs₂ F₁ F₂ hk₁ hk₂ hb₁ hb₂ hTM₁ hTM₂ hout hap₁ hap₂ hsp₁ hsp₂ hg wf₁
    wf₂ hw he
  have hgm : c.gMul = .seq (.block (Impl.Weierstrass.X86.setConst c.n (c.sl EM) (c.mont (3 * c.C.b))))
      (c.combCfg d).comb := by
    unfold Cfg.gMul; rw [hcd]; dsimp only; rw [ite_eq_right (by rw [hj]; decide)]
  rw [hgm]
  have hout₂ : ∀ i < (c.combWords d).length, ∀ b < 8,
      size ≤ ofs base ((g₂ .eax).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b) := by
    rw [← hg]; exact hout
  have htop := hd.top hj
  have hL := tcombLay hc hd
  have hV := tcombVals hc hC (hT d hcd).1
  have hedi : ∀ {x y : State}, Scr x base size → Scr y base size →
      VG.X86.Taint.Agree (τr [.edi]) x y := fun hx hy =>
    agree_regs fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact widen32_inj (hx.edi.trans hy.edi.symm)
  have prep := ct.prep.mono (P' := fun s t => s = s₀ ∧ t = t₀)
    (fun s t h => by rcases h with ⟨rfl, rfl⟩; exact hedi hs₁ hs₂) (fun _ _ _ => trivial)
  have prep' := prep.wp (fun _ _ h => by
    rcases h with ⟨rfl, rfl⟩
    exact ⟨combPrepare_ok hc hcd (3 * c.C.b) hs₁ F₁ hk₁ hb₁ hTM₁ hout hap₁ hsp₁,
      combPrepare_ok hc hcd (3 * c.C.b) hs₂ F₂ hk₂ hb₂ hTM₂ hout₂ hap₂ hsp₂⟩)
  refine prep'.seq ?_
  intro s t tr₁ tr₂ s' t' h e₁ e₂
  obtain ⟨_, ⟨K₁, S₁, M₁, T₁, _, v₁⟩, ⟨K₂, S₂, M₂, T₂, _, v₂⟩⟩ := h
  rw [← hg] at T₂
  have b3₁ : tmv c.C (c.combCfg d).M.n base s (c.combCfg d).S.b3 = Fin.ofNat c.C.p (3 * c.C.b) := by
    show toM c.C.p (2 ^ (64 * c.n)) (sv c base s EM) = _
    rw [v₁]; exact toM_cmont hc _
  have b3₂ : tmv c.C (c.combCfg d).M.n base t (c.combCfg d).S.b3 = Fin.ofNat c.C.p (3 * c.C.b) := by
    show toM c.C.p (2 ^ (64 * c.n)) (sv c base t EM) = _
    rw [v₂]; exact toM_cmont hc _
  have w₁ := combWf_keep wf₁ K₁.2.2 (K₁.1 _ (by decide)) (K₁.1 _ (by decide))
  have w₂ := combWf_keep wf₂ K₂.2.2 (K₂.1 _ (by decide)) (K₂.1 _ (by decide))
  have init := ct.init.mono (P' := fun x y => x = s ∧ y = t)
    (fun x y h => by rcases h with ⟨rfl, rfl⟩; exact hedi S₁ S₂) (fun _ _ _ => trivial)
  have init' := init.wp
    (F₁ := (TCombInv (c.combCfg d) c.C base size k₁ ((g₁ .eax).setWidth 64) (c.combWords d) s · (c.combCfg d).J))
    (F₂ := (TCombInv (c.combCfg d) c.C base size k₂ ((g₁ .eax).setWidth 64) (c.combWords d) t · (c.combCfg d).J))
    (fun _ _ h => by
      rcases h with ⟨rfl, rfl⟩
      exact ⟨init_ok hL hV hc.p_lt S₁ M₁ T₁, init_ok hL hV hc.p_lt S₂ M₂ T₂⟩)
  have hJ := hL.comb.J
  rw [Impl.Weierstrass.X86.TCombCfg.toComb_J] at hJ
  have loop := (combRcbLoop_rel hL ⟨htop.1, htop.2⟩ hC hc.onG hV hc.p_lt ct T₁ T₂ b3₁ b3₂ w₁ w₂
    (by rw [K₁.2.2, K₂.2.2, hw]) (by rw [K₁.1 _ (by decide), K₂.1 _ (by decide), he])
    (c.combCfg d).J).mono (P' := fun x y => True ∧
      TCombInv (c.combCfg d) c.C base size k₁ ((g₁ .eax).setWidth 64) (c.combWords d) s x (c.combCfg d).J ∧
      TCombInv (c.combCfg d) c.C base size k₂ ((g₁ .eax).setWidth 64) (c.combWords d) t y (c.combCfg d).J)
    (fun _ _ h => ⟨hJ.1, Nat.le_refl _, h.2.1, h.2.2⟩) (fun _ _ h => h)
  exact (init'.seq loop) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

end VG.Proof.Ecdsa.X86
