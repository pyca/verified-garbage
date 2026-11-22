module

public import VerifiedGarbage.Proof.Weierstrass.X86.TCombJEntry
public import VerifiedGarbage.Proof.Ecdsa.X86.CombLays
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJ
import VerifiedGarbage.Proof.Ecdsa.X86.GMul
import VerifiedGarbage.Proof.Ecdsa.X86.CombFinishCT
public import VerifiedGarbage.Proof.Ecdsa.X86.CombCode
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Weierstrass.X86.TCombJEntry
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombLays
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Weierstrass.X86.TCombJ
meta import VerifiedGarbage.Proof.Ecdsa.X86.GMul
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombFinishCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombCode
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
meta import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
import VerifiedGarbage.Proof.Weierstrass.X86.TComb
meta import VerifiedGarbage.Proof.Weierstrass.X86.TComb

/-! ### `Ecdsa.X86.CombStepCT`, which only this module used -/

section

/-!
# ECDSA over P-256 on x86 (32-bit): the constant time of the comb's iteration
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

variable {scratchSecond : Bool}

/-- One iteration reads a public table address, scans every entry, then
performs scalar arithmetic. The loop invariant supplies that address again
at the next iteration. -/
theorem combStep_rel : RelCT isa (VG.X86.Taint.Agree (combτAt scratchSecond)) combStep (fun _ _ => True) :=
  by
    cases scratchSecond <;>
      exact RelCT.taint (A := sseTaint) _ (fun _ _ h => h)
        (by taint_decide_weak VG.Proof.Ecdsa.X86.combWeak)

end VG.Proof.Ecdsa.X86

end

end

@[expose] public section

namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

variable {scratchSecond : Bool}

/-- The functional comb invariant supplies the public values used by one
iteration's taint proof, independently of the two secret scalars. -/
theorem combInv_agree {base T : Addr} {s₀ t₀ s t : State} {k₁ k₂ j : Nat}
    (wf₁ : VG.X86.Taint.Wf (combτAt scratchSecond) s₀) (wf₂ : VG.X86.Taint.Wf (combτAt scratchSecond) t₀) (hw : s₀.wr = t₀.wr)
    (he : s₀.gpr .esp = t₀.gpr .esp)
    (h₁ : TCombJInv p256K p256Comb.C base size k₁ T (p256Comb.combWords p256d) s₀ s j)
    (h₂ : TCombJInv p256K p256Comb.C base size k₂ T (p256Comb.combWords p256d) t₀ t j) :
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


/-- The comb loop has equal traces for distinct secret scalars. The
functional invariant re-establishes the public pointer after each step. -/
theorem combLoop_rel (hL : TCombLay p256K size) (hC : Law p256Comb.C) (ham3 : AM3 p256Comb.C)
    (hG : onCurve p256Comb.C (G p256Comb.C) = true) (hV : TCombVals p256K p256Comb.C p256d.tbl)
    (hpn : p256Comb.C.p < 2 ^ (64 * p256K.M.n))
    (hB : BoothOk p256Comb.C p256K.w p256K.J (2 ^ 256))
    {base T : Addr} {s₀ t₀ : State} {k₁ k₂ : Nat}
    (hF₁ : TCombFixed p256K p256Comb.C base size s₀ k₁ T (p256Comb.combWords p256d))
    (hF₂ : TCombFixed p256K p256Comb.C base size t₀ k₂ T (p256Comb.combWords p256d))
    (wf₁ : VG.X86.Taint.Wf (combτAt scratchSecond) s₀) (wf₂ : VG.X86.Taint.Wf (combτAt scratchSecond) t₀) (hw : s₀.wr = t₀.wr)
    (he : s₀.gpr .esp = t₀.gpr .esp) (n : Nat) :
    RelCT isa (fun s t => 1 ≤ n ∧ n < p256K.J ∧
      TCombJInv p256K p256Comb.C base size k₁ T (p256Comb.combWords p256d) s₀ s (p256K.J - n) ∧
      TCombJInv p256K p256Comb.C base size k₂ T (p256Comb.combWords p256d) t₀ t (p256K.J - n))
      (.loop p256K.stepJ .ne) (VG.X86.Taint.Agree (combτAt scratchSecond)) := by
  let I := fun n s t => 1 ≤ n ∧ n < p256K.J ∧
      TCombJInv p256K p256Comb.C base size k₁ T (p256Comb.combWords p256d) s₀ s (p256K.J - n) ∧
      TCombJInv p256K p256Comb.C base size k₂ T (p256Comb.combWords p256d) t₀ t (p256K.J - n)
  refine RelCT.loop (M := isa) I (fun j => ?_) n
  have ct : RelCT isa (I j) p256K.stepJ (fun _ _ => True) :=
    combStep_rel.mono (fun _ _ h => combInv_agree wf₁ wf₂ hw he h.2.2.1 h.2.2.2) (fun _ _ _ => trivial)
  have ct' := ct.wp (F₁ := fun (s : State) =>
      TCombJInv p256K p256Comb.C base size k₁ T (p256Comb.combWords p256d) s₀ s (p256K.J - j + 1) ∧
        s.zf = some (decide (p256K.J - j + 1 = p256K.J)))
    (F₂ := fun (t : State) =>
      TCombJInv p256K p256Comb.C base size k₂ T (p256Comb.combWords p256d) t₀ t (p256K.J - j + 1) ∧
        t.zf = some (decide (p256K.J - j + 1 = p256K.J)))
    (fun _ _ h => ⟨stepJ_ok hL hC ham3 hG hV hpn (by decide) hB hF₁.k_lt hF₁ (by omega) (by omega) h.2.2.1
        combStep_sp,
      stepJ_ok hL hC ham3 hG hV hpn (by decide) hB hF₂.k_lt hF₂ (by omega) (by omega) h.2.2.2 combStep_sp⟩)
  intro s t tr₁ tr₂ s' t' h e₁ e₂
  obtain ⟨eqtr, _, ⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ := ct' _ _ _ _ _ _ h e₁ e₂
  have ev₁ : isa.eval .ne s' = some !decide (p256K.J - j + 1 = p256K.J) := by change s'.zf.map (!·) = _; rw [z₁]; rfl
  have ev₂ : isa.eval .ne t' = some !decide (p256K.J - j + 1 = p256K.J) := by change t'.zf.map (!·) = _; rw [z₂]; rfl
  refine ⟨eqtr, by rw [ev₁, ev₂], fun _ => combInv_agree wf₁ wf₂ hw he i₁ i₂, fun ht => ?_⟩
  have hj : 1 ≤ j ∧ j < p256K.J := ⟨h.1, h.2.1⟩
  have hj' : j - 1 ≠ 0 := by
    rw [ev₁] at ht
    have : p256K.J - j + 1 ≠ p256K.J := by simpa using ht
    omega_arith
  exact ⟨j - 1, by omega_arith, by dsimp only [I]; rw [show p256K.J - (j - 1) = p256K.J - j + 1 by omega_arith]; exact ⟨by omega_arith, by omega_arith, i₁, i₂⟩⟩


theorem combFirst_rel : RelCT isa (VG.X86.Taint.Agree (combStartτAt scratchSecond)) p256K.first
    (fun _ _ => True) := by
  cases scratchSecond <;>
    exact RelCT.taint (A := sseTaint) _ (fun _ _ h => h)
      (by taint_decide_weak VG.Proof.Ecdsa.X86.combWeak)

/-- Initialize and run the comb with the same public addresses in both runs. -/
theorem combCore_rel (hL : TCombLay p256K size) (hC : Law p256Comb.C) (ham3 : AM3 p256Comb.C)
    (hG : onCurve p256Comb.C (G p256Comb.C) = true) (hV : TCombVals p256K p256Comb.C p256d.tbl)
    (hpn : p256Comb.C.p < 2 ^ (64 * p256K.M.n))
    (hB : BoothOk p256Comb.C p256K.w p256K.J (2 ^ 256))
    {base T : Addr} {s₀ t₀ : State} {k₁ k₂ : Nat}
    (hs₁ : Scr s₀ base size) (hs₂ : Scr t₀ base size)
    (hm₁ : ModOkW p256K.M size p256Comb.C.p s₀.mem base)
    (hm₂ : ModOkW p256K.M size p256Comb.C.p t₀.mem base)
    (hF₁ : TCombFixed p256K p256Comb.C base size s₀ k₁ T (p256Comb.combWords p256d))
    (hF₂ : TCombFixed p256K p256Comb.C base size t₀ k₂ T (p256Comb.combWords p256d))
    (wf₁ : VG.X86.Taint.Wf (combτAt scratchSecond) s₀) (wf₂ : VG.X86.Taint.Wf (combτAt scratchSecond) t₀) (hw : s₀.wr = t₀.wr)
    (he : s₀.gpr .esp = t₀.gpr .esp) :
    RelCT isa (fun s t => s = s₀ ∧ t = t₀) p256K.combJ (fun _ _ => True) := by
  have initial : VG.X86.Taint.Agree (combStartτAt scratchSecond) s₀ t₀ := by
    refine combStartAgree wf₁ wf₂ hw (widen32_inj (hs₁.edi.trans hs₂.edi.symm)) he ?_
    have b₁ := wf₁.bases (.edi, combRegion scratchSecond, 0) (List.mem_singleton_self _)
    have b₂ := wf₂.bases (.edi, combRegion scratchSecond, 0) (List.mem_singleton_self _)
    change addr (s₀.gpr .edi) 0 = (VG.X86.Taint.region s₀ (combRegion scratchSecond)).base at b₁
    change addr (t₀.gpr .edi) 0 = (VG.X86.Taint.region t₀ (combRegion scratchSecond)).base at b₂
    simp only [addr, BitVec.add_zero] at b₁ b₂
    have b₁' := b₁.symm.trans hs₁.edi
    have b₂' := b₂.symm.trans hs₂.edi
    simp only [VG.X86.Taint.byteAddr, b₁', b₂']
    exact widen32_inj (hF₁.tsym.trans hF₂.tsym.symm)
  have init : RelCT isa (fun s t => s = s₀ ∧ t = t₀) p256K.first (fun _ _ => True) := combFirst_rel.mono (fun s t h => by
    rcases h with ⟨rfl, rfl⟩; exact initial) (fun _ _ _ => trivial)
  have ini := init.wp
    (F₁ := fun s => TCombJInv p256K p256Comb.C base size k₁ T (p256Comb.combWords p256d) s₀ s 1)
    (F₂ := fun t => TCombJInv p256K p256Comb.C base size k₂ T (p256Comb.combWords p256d) t₀ t 1)
    (fun _ _ h => by rcases h with ⟨rfl, rfl⟩; exact
      ⟨firstJ_ok hL hC hG hV hpn (by decide) hs₁ hm₁ hF₁ combFirst_sp,
       firstJ_ok hL hC hG hV hpn (by decide) hs₂ hm₂ hF₂ combFirst_sp⟩)
  have finish := combFinish_rel (scratchSecond := scratchSecond)
  refine ini.seq (((combLoop_rel hL hC ham3 hG hV hpn hB hF₁ hF₂ wf₁ wf₂ hw he (p256K.J - 1)).seq
    (finish.mono (fun _ _ h => h) (fun _ _ _ => trivial))).mono ?_ (fun _ _ _ => trivial))
  intro s t h
  exact ⟨by decide, by decide, h.2.1, h.2.2⟩


/-- Fixed-base multiplication is constant time for two arbitrary scalars
when its scratch and static-table addresses agree. -/
theorem gMul_rel (hc : CfgOk p256Comb) (hC : Law p256Comb.C)
    (hT : CombTbls p256Comb) (hd : CombOk p256Comb p256d)
    {base : Addr} {g₁ g₂ : Reg → BitVec 32} {s₀ t₀ : State} {k₁ k₂ : Nat}
    (hs₁ : Scr s₀ base size) (hs₂ : Scr t₀ base size)
    (F₁ : Fixed p256Comb base g₁ s₀.mem) (F₂ : Fixed p256Comb base g₂ t₀.mem)
    (hk₁ : k₁ < 2 ^ (64 * p256Comb.n)) (hk₂ : k₂ < 2 ^ (64 * p256Comb.n))
    (hb₁ : ∀ t < 64 * p256Comb.n, s₀.mem (off base (bitsAt p256Comb.n 0 + t)) =
      if k₁.testBit t then 1 else 0)
    (hb₂ : ∀ t < 64 * p256Comb.n, t₀.mem (off base (bitsAt p256Comb.n 0 + t)) =
      if k₂.testBit t then 1 else 0)
    (hTM₁ : TblMem s₀ ((g₁ .eax).setWidth 64) (p256Comb.combWords p256d))
    (hTM₂ : TblMem t₀ ((g₂ .eax).setWidth 64) (p256Comb.combWords p256d))
    (hout : ∀ i < (p256Comb.combWords p256d).length, ∀ b < 8,
      size ≤ ofs base ((g₁ .eax).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b))
    (hap₁ : ∀ r ∈ s₀.wr ++ [below (s₀.gpr .esp) 20],
      Region.Disjoint ⟨(g₁ .eax).setWidth 64, 8 * (p256Comb.combWords p256d).length⟩ r)
    (hap₂ : ∀ r ∈ t₀.wr ++ [below (t₀.gpr .esp) 20],
      Region.Disjoint ⟨(g₂ .eax).setWidth 64, 8 * (p256Comb.combWords p256d).length⟩ r)
    (hsp₁ : 20 ≤ (s₀.gpr .esp).toNat) (hsp₂ : 20 ≤ (t₀.gpr .esp).toNat)
    (hg : g₁ .eax = g₂ .eax)
    (wf₁ : VG.X86.Taint.Wf (combτAt scratchSecond) s₀) (wf₂ : VG.X86.Taint.Wf (combτAt scratchSecond) t₀)
    (hw : s₀.wr = t₀.wr) (he : s₀.gpr .esp = t₀.gpr .esp) :
    RelCT isa (fun s t => s = s₀ ∧ t = t₀) (p256Comb.combBody p256d) (fun _ _ => True) := by
  have ham3 := ((hT p256d rfl).2 rfl).2
  have hout₂ : ∀ i < (p256Comb.combWords p256d).length, ∀ b < 8,
      size ≤ ofs base ((g₂ .eax).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b) := by
    rw [← hg]; exact hout
  have prep := RelCT.taint (A := taint) (P := fun s t => s = s₀ ∧ t = t₀) (τr [.edi])
    (fun s t h => by
      rcases h with ⟨rfl, rfl⟩
      exact agree_regs fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact widen32_inj (hs₁.edi.trans hs₂.edi.symm))
    (c := .block (Impl.Weierstrass.X86.setConst p256Comb.n (p256Comb.sl EM) (p256Comb.mont p256Comb.C.b)))
    (by taint_decide)
  have prep' := prep.wp (fun _ _ h => by
    rcases h with ⟨rfl, rfl⟩
    exact ⟨combPrepare_ok (d := p256d) hc rfl p256Comb.C.b hs₁ F₁ hk₁ hb₁ hTM₁ hout hap₁ hsp₁,
      combPrepare_ok (d := p256d) hc rfl p256Comb.C.b hs₂ F₂ hk₂ hb₂ hTM₂ hout₂ hap₂ hsp₂⟩)
  refine prep'.seq ?_
  intro s t tr₁ tr₂ s' t' h e₁ e₂
  obtain ⟨_, ⟨K₁, S₁, M₁, T₁, _, _⟩, ⟨K₂, S₂, M₂, T₂, _, _⟩⟩ := h
  rw [← hg] at T₂
  exact combCore_rel (tcombLay hc hd) hC ham3 hc.onG (tcombVals hc hC (hT p256d rfl).1) hc.p_lt
    ((hT p256d rfl).2 rfl).1
    S₁ S₂ M₁ M₂ T₁ T₂
    (combWf_keep wf₁ K₁.wr (K₁.gpr _ (by decide)) (K₁.gpr _ (by decide)))
    (combWf_keep wf₂ K₂.wr (K₂.gpr _ (by decide)) (K₂.gpr _ (by decide)))
    (by rw [K₁.wr, K₂.wr, hw]) (by rw [K₁.gpr _ (by decide), K₂.gpr _ (by decide), he])
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

end VG.Proof.Ecdsa.X86
