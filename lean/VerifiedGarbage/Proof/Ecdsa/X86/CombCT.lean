import VerifiedGarbage.Proof.Ecdsa.X86.CombSign
import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
import VerifiedGarbage.Proof.Framework.X86.TaintSym
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.Inline

namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

def p256d : CombData := ⟨7, Impl.P256.p256Comb7, Impl.P256.p256Comb7Start, "VG_P256_COMB"⟩
abbrev p256K := p256Comb.combCfg p256d

def combStep : Prog isa := p256K.step
materialize_code combStep

def combτ : VG.X86.Taint.T :=
  { regs := .ofList [.esi, .edi], flags := false, lens := [0, 8192],
    bases := [(.edi, 1, 0)], slots := [(1, 60, 4)] }

def combWeak (τ : VG.X86.Taint.T) : VG.X86.Taint.T := { τ with slots := [], wbases := [] }

/-- One iteration reads a public table address, scans every entry, then
performs scalar arithmetic. The loop invariant supplies that address again
at the next iteration. -/
theorem combStep_rel : RelCT isa (VG.X86.Taint.Agree combτ) combStep (fun _ _ => True) :=
  RelCT.taint (A := sseTaint) combτ (fun _ _ h => h)
    (by taint_decide_weak VG.Proof.Ecdsa.X86.combWeak)

/-- The loop's taint well-formedness only needs the scratch base and the
unchanged region metadata. -/
theorem combWf_keep {s t : State} (h : VG.X86.Taint.Wf combτ s)
    (hw : t.wr = s.wr) (he : t.gpr .edi = s.gpr .edi) : VG.X86.Taint.Wf combτ t := by
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hn
    rw [hw]; exact h.lens hn
  · intro p hp
    have : p = (.edi, 1, 0) := List.mem_singleton.mp hp
    subst p
    simp only [VG.X86.Taint.region, hw, he]
    exact h.bases _ (List.mem_singleton_self _)
  · intro p hp; cases hp
  · intro hp; cases hp
  · intro p hp; cases hp

/-- Re-establish the public table word from the functional invariant. -/
theorem combAgree {s t : State} (hs : VG.X86.Taint.Wf combτ s) (ht : VG.X86.Taint.Wf combτ t)
    (hw : s.wr = t.wr) (hi : s.gpr .esi = t.gpr .esi) (hd : s.gpr .edi = t.gpr .edi)
    (hp : s.mem.readW (VG.X86.Taint.byteAddr s 1 60) 32 =
      t.mem.readW (VG.X86.Taint.byteAddr t 1 60) 32) : VG.X86.Taint.Agree combτ s t := by
  refine ⟨⟨?_, fun h => by cases h⟩, fun _ => hw, hs, ht, ?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [combτ, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hi
    · exact hd
  · intro p hp
    have : p = (1, 60, 4) := List.mem_singleton.mp hp
    subst p; decide
  · intro p hmem k hlo hhi
    have : p = (1, 60, 4) := List.mem_singleton.mp hmem
    subst p
    have hk : k < 64 ∧ 60 ≤ k := by exact ⟨hhi, hlo⟩
    have e : ∀ u : State, VG.X86.Taint.byteAddr u 1 k =
        VG.X86.Taint.byteAddr u 1 60 + BitVec.ofNat 64 (k - 60) := by
      intro u
      unfold VG.X86.Taint.byteAddr
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_of_le hk.2]
    rw [e s, e t, Mem.readW_byte s.mem _ (by omega), Mem.readW_byte t.mem _ (by omega), hp]
  · intro h; cases h
  · intro k hlo hhi; have : k < 0 := hhi; omega


/-- Widening 32-bit words is injective. -/
theorem widen32_inj {x y : BitVec 32} (h : x.setWidth 64 = y.setWidth 64) : x = y := by
  have h' := congrArg (BitVec.setWidth 32) h
  simpa only [BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_eq] using h'

/-- The functional comb invariant supplies the public values used by one
iteration's taint proof, independently of the two secret scalars. -/
theorem combInv_agree {base T : Addr} {s₀ t₀ s t : State} {k₁ k₂ j : Nat}
    (wf₁ : VG.X86.Taint.Wf combτ s₀) (wf₂ : VG.X86.Taint.Wf combτ t₀) (hw : s₀.wr = t₀.wr)
    (h₁ : TCombInv p256K p256Comb.C base size k₁ T (p256Comb.combWords p256d) s₀ s j)
    (h₂ : TCombInv p256K p256Comb.C base size k₂ T (p256Comb.combWords p256d) t₀ t j) :
    VG.X86.Taint.Agree combτ s t := by
  have w₁ := combWf_keep wf₁ h₁.keep.wr (h₁.keep.gpr _ (by decide))
  have w₂ := combWf_keep wf₂ h₂.keep.wr (h₂.keep.gpr _ (by decide))
  refine combAgree w₁ w₂ (by rw [h₁.keep.wr, h₂.keep.wr, hw])
    (h₁.esi.trans h₂.esi.symm) (widen32_inj (h₁.scr.edi.trans h₂.scr.edi.symm)) ?_
  have b₁ := w₁.bases (.edi, 1, 0) (List.mem_singleton_self _)
  have b₂ := w₂.bases (.edi, 1, 0) (List.mem_singleton_self _)
  change addr (s.gpr .edi) 0 = (VG.X86.Taint.region s 1).base at b₁
  change addr (t.gpr .edi) 0 = (VG.X86.Taint.region t 1).base at b₂
  simp only [addr, BitVec.add_zero] at b₁ b₂
  have b₁' : (VG.X86.Taint.region s 1).base = base := b₁.symm.trans h₁.scr.edi
  have b₂' : (VG.X86.Taint.region t 1).base = base := b₂.symm.trans h₂.scr.edi
  simp only [VG.X86.Taint.byteAddr, b₁', b₂']
  exact widen32_inj (h₁.tsym.trans h₂.tsym.symm)


/-- The comb loop has equal traces for distinct secret scalars. The
functional invariant re-establishes the public pointer after each step. -/
theorem combLoop_rel (hL : TCombLay p256K size) (hC : Law p256Comb.C) (ham3 : AM3 p256Comb.C)
    (hG : onCurve p256Comb.C (G p256Comb.C) = true) (hV : TCombVals p256K p256Comb.C p256d.tbl)
    (hpn : p256Comb.C.p < 2 ^ (64 * p256K.M.n))
    {base T : Addr} {s₀ t₀ : State} {k₁ k₂ : Nat}
    (hF₁ : TCombFixed p256K p256Comb.C base size s₀ k₁ T (p256Comb.combWords p256d))
    (hF₂ : TCombFixed p256K p256Comb.C base size t₀ k₂ T (p256Comb.combWords p256d))
    (wf₁ : VG.X86.Taint.Wf combτ s₀) (wf₂ : VG.X86.Taint.Wf combτ t₀) (hw : s₀.wr = t₀.wr)
    (n : Nat) :
    RelCT isa (fun s t => 1 ≤ n ∧ n ≤ p256K.J ∧
      TCombInv p256K p256Comb.C base size k₁ T (p256Comb.combWords p256d) s₀ s n ∧
      TCombInv p256K p256Comb.C base size k₂ T (p256Comb.combWords p256d) t₀ t n)
      (.loop p256K.step .ne) (fun _ _ => True) := by
  let I := fun n s t => 1 ≤ n ∧ n ≤ p256K.J ∧
      TCombInv p256K p256Comb.C base size k₁ T (p256Comb.combWords p256d) s₀ s n ∧
      TCombInv p256K p256Comb.C base size k₂ T (p256Comb.combWords p256d) t₀ t n
  refine RelCT.loop (M := isa) I (fun j => ?_) n
  have ct : RelCT isa (I j) p256K.step (fun _ _ => True) :=
    combStep_rel.mono (fun _ _ h => combInv_agree wf₁ wf₂ hw h.2.2.1 h.2.2.2) (fun _ _ _ => trivial)
  have ct' := ct.wp (F₁ := fun (s : State) =>
      TCombInv p256K p256Comb.C base size k₁ T (p256Comb.combWords p256d) s₀ s (j - 1) ∧
        s.zf = some (decide (j - 1 = 0)))
    (F₂ := fun (t : State) =>
      TCombInv p256K p256Comb.C base size k₂ T (p256Comb.combWords p256d) t₀ t (j - 1) ∧
        t.zf = some (decide (j - 1 = 0)))
    (fun _ _ h => ⟨tstep_ok hL hC ham3 hG hV hpn hF₁ h.1 h.2.1 h.2.2.1,
      tstep_ok hL hC ham3 hG hV hpn hF₂ h.1 h.2.1 h.2.2.2⟩)
  intro s t tr₁ tr₂ s' t' h e₁ e₂
  obtain ⟨eqtr, _, ⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ := ct' _ _ _ _ _ _ h e₁ e₂
  have ev₁ : isa.eval .ne s' = some !decide (j - 1 = 0) := by change s'.zf.map (!·) = _; rw [z₁]; rfl
  have ev₂ : isa.eval .ne t' = some !decide (j - 1 = 0) := by change t'.zf.map (!·) = _; rw [z₂]; rfl
  refine ⟨eqtr, by rw [ev₁, ev₂], fun _ => trivial, fun ht => ?_⟩
  have hj : 1 ≤ j ∧ j ≤ p256K.J := ⟨h.1, h.2.1⟩
  have hj' : j - 1 ≠ 0 := by rw [ev₁] at ht; simpa using ht
  exact ⟨j - 1, by omega, by dsimp only [I]; exact ⟨by omega, by omega, i₁, i₂⟩⟩


/-- Initialize and run the comb with the same public addresses in both runs. -/
theorem combCore_rel (hL : TCombLay p256K size) (hC : Law p256Comb.C) (ham3 : AM3 p256Comb.C)
    (hG : onCurve p256Comb.C (G p256Comb.C) = true) (hV : TCombVals p256K p256Comb.C p256d.tbl)
    (hpn : p256Comb.C.p < 2 ^ (64 * p256K.M.n))
    {base T : Addr} {s₀ t₀ : State} {k₁ k₂ : Nat}
    (hs₁ : Scr s₀ base size) (hs₂ : Scr t₀ base size)
    (hm₁ : ModOkW p256K.M size p256Comb.C.p s₀.mem base)
    (hm₂ : ModOkW p256K.M size p256Comb.C.p t₀.mem base)
    (hF₁ : TCombFixed p256K p256Comb.C base size s₀ k₁ T (p256Comb.combWords p256d))
    (hF₂ : TCombFixed p256K p256Comb.C base size t₀ k₂ T (p256Comb.combWords p256d))
    (wf₁ : VG.X86.Taint.Wf combτ s₀) (wf₂ : VG.X86.Taint.Wf combτ t₀) (hw : s₀.wr = t₀.wr) :
    RelCT isa (fun s t => s = s₀ ∧ t = t₀)
      (.seq (.block p256K.initCore) (.loop p256K.step .ne)) (fun _ _ => True) := by
  have init := RelCT.taint (A := taint) (P := fun s t => s = s₀ ∧ t = t₀) (τr [.edi])
    (fun s t h => by
      rcases h with ⟨rfl, rfl⟩
      exact agree_regs fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact widen32_inj (hs₁.edi.trans hs₂.edi.symm))
    (c := .block p256K.initCore) (by taint_decide)
  have ini := init.wp
    (F₁ := fun s => TCombInv p256K p256Comb.C base size k₁ T (p256Comb.combWords p256d) s₀ s p256K.J)
    (F₂ := fun t => TCombInv p256K p256Comb.C base size k₂ T (p256Comb.combWords p256d) t₀ t p256K.J)
    (fun _ _ h => by rcases h with ⟨rfl, rfl⟩; exact
      ⟨tcombInit_ok hL hV hpn hs₁ hm₁ hF₁, tcombInit_ok hL hV hpn hs₂ hm₂ hF₂⟩)
  refine ini.seq ((combLoop_rel hL hC ham3 hG hV hpn hF₁ hF₂ wf₁ wf₂ hw p256K.J).mono ?_ (fun _ _ _ => trivial))
  intro s t h
  exact ⟨by decide, Nat.le_refl _, h.2.1, h.2.2⟩


/-- Fixed-base multiplication is constant time for two arbitrary scalars
when its scratch and static-table addresses agree. -/
theorem gMul_rel (hc : CfgOk p256Comb) (hC : Law p256Comb.C)
    (hT : CombTbls p256Comb) (hd : CombOk p256Comb p256d) (ham3 : AM3 p256Comb.C)
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
    (hg : g₁ .eax = g₂ .eax)
    (wf₁ : VG.X86.Taint.Wf combτ s₀) (wf₂ : VG.X86.Taint.Wf combτ t₀)
    (hw : s₀.wr = t₀.wr) :
    RelCT isa (fun s t => s = s₀ ∧ t = t₀) p256Comb.gMul (fun _ _ => True) := by
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
    exact ⟨combPrepare_ok hc rfl hs₁ F₁ hk₁ hb₁ hTM₁ hout,
      combPrepare_ok hc rfl hs₂ F₂ hk₂ hb₂ hTM₂ hout₂⟩)
  refine prep'.seq ?_
  intro s t tr₁ tr₂ s' t' h e₁ e₂
  obtain ⟨_, ⟨K₁, S₁, M₁, T₁⟩, ⟨K₂, S₂, M₂, T₂⟩⟩ := h
  rw [← hg] at T₂
  exact combCore_rel (tcombLay hc hd) hC ham3 hc.onG (tcombVals hc hC (hT p256d rfl)) hc.p_lt
    S₁ S₂ M₁ M₂ T₁ T₂
    (combWf_keep wf₁ K₁.wr (K₁.gpr _ (by decide)))
    (combWf_keep wf₂ K₂.wr (K₂.gpr _ (by decide)))
    (by rw [K₁.wr, K₂.wr, hw]) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

end VG.Proof.Ecdsa.X86
