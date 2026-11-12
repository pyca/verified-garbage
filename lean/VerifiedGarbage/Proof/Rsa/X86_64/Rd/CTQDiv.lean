module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTDiv
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
import VerifiedGarbage.Proof.Rsa.X86_64.WordStep
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTDiv
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordStep
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on x86-64: constant time, the division by words

`qDiv e`'s step reloads the count `j + 1` from the header and addresses the
dividend's digit and the quotient's word by it: its runs agree from states
whose count is the same (`QB`), the count being public. The step proper
(`WordReduce.step`) is checked from the registers `qDigit` pins, and needs
the loop's invariant (`QInv`) for its arithmetic; its setup needs the
divisor's top bit set (`FDp`) for the reciprocal.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Rsa.X86_64 (copyWords)

/-! ## A step, from a public count -/

/-- Before a step with the count `c` (`a = (p, c)`): `qBody_ok`'s hypotheses
at the wide width `W = 2 h + 4`. -/
structure QB (e : Nat) (a : RpP × Nat) (s : State) : Prop where
  ws : Ws s a.1.B a.1.Z (wW a.1.k)
  kb : 8 ≤ wk a.1.k ∧ wk a.1.k ≤ 128
  e1 : 1 ≤ e
  e3 : e ≤ 3
  cnt : word s.mem a.1.B (8 * sCt) = BitVec.ofNat 64 a.2
  c1 : 1 ≤ a.2
  cN : a.2 ≤ wk a.1.k + e
  hd : 2 ^ 63 ≤ (word s.mem a.1.B (slot (wW a.1.k) qD + 8 * (wk a.1.k - 1))).toNat
  hv : (word s.mem a.1.B (slot (wW a.1.k) qV)).toNat =
    (2 ^ 128 - 1) / (word s.mem a.1.B (slot (wW a.1.k) qD + 8 * (wk a.1.k - 1))).toNat - 2 ^ 64
  hx : wv s.mem a.1.B (slot (wW a.1.k) qR) (wk a.1.k) < wv s.mem a.1.B (slot (wW a.1.k) qD) (wk a.1.k)

theorem QB.lay {e : Nat} {a : RpP × Nat} {s : State} (h : QB e a s) : QLay (wW a.1.k) (wk a.1.k) e :=
  ⟨wW_eq _, h.kb.1, h.e1, h.e3⟩

/-- After `qLoad`. -/
def qLoadVal (a : RpP × Nat) : Reg → BitVec 64
  | .rdi => a.1.B
  | .r12 => BitVec.ofNat 64 (wW a.1.k)
  | .r9 => BitVec.ofNat 64 (8 * (wW a.1.k + 2))
  | .rbp => off a.1.B (slot (wW a.1.k) qV)
  | .r11 => off a.1.B (slot (wW a.1.k) qA)
  | .rcx => BitVec.ofNat 64 a.2
  | _ => 0

/-- The step's registers. -/
def qStepVal (a : RpP × Nat) : Reg → BitVec 64
  | .rdi => a.1.B
  | .rbx => off a.1.B (slot (wW a.1.k) qR)
  | .r10 => off a.1.B (slot (wW a.1.k) qD)
  | .r8 => off a.1.B (slot (wW a.1.k) qT)
  | .rbp => off a.1.B (slot (wW a.1.k) qV)
  | .r12 => BitVec.ofNat 64 (wk a.1.k)
  | _ => 0

/-- After `qLoad` and `qDigit`, from `s`. -/
def Q1 (e : Nat) (a : RpP × Nat) (t : State) : Prop :=
  ∃ s, QB e a s ∧ (∀ r ∈ [.rdi, .rbx, .r10, .r8, .rbp, .r12], t.gpr r = qStepVal a r) ∧
    t.mem = s.mem.writeW (off a.1.B (slot (wW a.1.k) qV + 8)) (word s.mem a.1.B (slot (wW a.1.k) qA + 8 * (a.2 - 1))) ∧
    Keep [.r12, .r9, .rbp, .r11, .rcx, .rdx, .rbx, .r10, .r8] s t

/-- After the step. -/
def Q2 (e : Nat) (a : RpP × Nat) (t : State) : Prop :=
  Ws t a.1.B a.1.Z (wW a.1.k) ∧ word t.mem a.1.B (8 * sCt) = BitVec.ofNat 64 a.2 ∧ 1 ≤ a.2 ∧
    a.2 ≤ wk a.1.k + e ∧ 8 ≤ wk a.1.k ∧ wk a.1.k ≤ 128 ∧ e ≤ 3

/-- After `qPos`. -/
def qPosVal (a : RpP × Nat) : Reg → BitVec 64
  | .rdi => a.1.B
  | .rbx => off a.1.B (slot (wW a.1.k) qQ)
  | .rax => BitVec.ofNat 64 a.2
  | _ => 0

theorem pins_list {α : Type} {Φ : α → State → Prop} {rs : List Reg} (f : α → Reg → BitVec 64)
    (h : ∀ a s, Φ a s → ∀ r ∈ rs, s.gpr r = f a r) : Pins Φ rs :=
  fun a _ _ h₁ h₂ r hr => (h a _ h₁ r hr).trans (h a _ h₂ r hr).symm

theorem qLoadDigit_ok {e : Nat} {a : RpP × Nat} {s : State} (h : QB e a s) :
    WP isa (.seq (.block qLoad) (.block qDigit)) s (Q1 e a) := by
  have hw := h.ws
  have hW := wW_eq a.1.k
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  have hw2 := hw.w2
  have kb := h.kb
  have e3 := h.e3
  obtain ⟨sA, sQ, sR, sD, sT, sV, s16⟩ := qSlots (wW a.1.k)
  rw [s16] at hZ
  have hc1 := h.c1
  have hcN := h.cN
  refine WP.seq (WP.mono (qLoad_ok hw h.cnt) fun s₁ ⟨hdi₁, h12₁, h9₁, hbp₁, h11₁, hcx₁, hm₁, k₁⟩ => ?_)
  refine WP.mono (qDigit_ok (hw.scr.congr k₁.2.2) hdi₁ h9₁ h12₁ hbp₁ h11₁ hcx₁ hc1 (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith)) fun t ⟨hbx, h10, h8', hbp, h12, hm, k₂⟩ => ?_
  refine ⟨s, h, fun r hr => ?_, by rw [hm, hm₁], (k₁.trans k₂).mono (by simp)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (k₂.gpr (by decide)).trans hdi₁
  · exact hbx
  · exact h10
  · exact h8'
  · exact hbp
  · rw [h12]; show _ = BitVec.ofNat 64 (wk a.1.k); congr 1; omega_arith

theorem qStepW_ok {e : Nat} {a : RpP × Nat} {t : State} (h1 : Q1 e a t) :
    WP isa Impl.Rsa.X86_64.WordReduce.step t (Q2 e a) := by
  obtain ⟨s, h, hr, hm₂, k12⟩ := h1
  have hbx₂ := hr .rbx (by simp)
  have h10₂ := hr .r10 (by simp)
  have h8₂ := hr .r8 (by simp)
  have hbp₂ := hr .rbp (by simp)
  have h12₂ := hr .r12 (by simp)
  simp only [qStepVal] at hbx₂ h10₂ h8₂ hbp₂ h12₂
  clear hr
  have hw := h.ws
  have hW := wW_eq a.1.k
  have h8 := h.kb.1
  have e3 := h.e3
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  have h256 := hw.h256
  have hw2 := hw.w2
  have kb := h.kb
  obtain ⟨sA, sQ, sR, sD, sT, sV, s16⟩ := qSlots (wW a.1.k)
  rw [s16] at hZ
  have hct : 8 * sCt = 200 := rfl
  have hc1 := h.c1
  have hcN := h.cN
  have hcnt := h.cnt
  have hhd := h.hd
  have hhv := h.hv
  have hhx := h.hx
  clear h
  obtain ⟨p, c⟩ := a
  unfold Q2
  simp only at *
  generalize wW p.k = W at *
  generalize wk p.k = hh at *
  have hs₂ := hw.scr.congr k12.2.2
  have wD : ∀ i < hh, word t.mem p.B (slot W qD + 8 * i) = word s.mem p.B (slot W qD + 8 * i) := fun i hi => by
    rw [hm₂]; exact (writeW_outside s.mem p.B _ (by q_omega)).word (by q_omega) (by q_omega)
  have wR : ∀ i < hh, word t.mem p.B (slot W qR + 8 * i) = word s.mem p.B (slot W qR + 8 * i) := fun i hi => by
    rw [hm₂]; exact (writeW_outside s.mem p.B _ (by q_omega)).word (by q_omega) (by q_omega)
  have vD : wv t.mem p.B (slot W qD) hh = wv s.mem p.B (slot W qD) hh := wv_congr wD
  have vR : wv t.mem p.B (slot W qR) hh = wv s.mem p.B (slot W qR) hh := wv_congr wR
  have tD : word t.mem p.B (slot W qD + 8 * (hh - 1)) = word s.mem p.B (slot W qD + 8 * (hh - 1)) :=
    wD _ (by omega_arith)
  have rV : word t.mem p.B (slot W qV) = word s.mem p.B (slot W qV) := by
    rw [hm₂]; exact (writeW_outside s.mem p.B _ (by q_omega)).word (by q_omega) (by q_omega)
  refine WP.mono (WordReduce.stepQ_ok hs₂ hbx₂ h10₂ h8₂ h12₂ hbp₂ (by omega_arith) (by omega_arith)
    (by q_omega) (by q_omega) (by q_omega) (by q_omega) (by q_omega) (by q_omega)
    (by rw [tD]; exact hhd) (by rw [rV, tD]; exact hhv) (by rw [vR, vD]; exact hhx))
    fun s₃ ⟨_, f₃, k₃, _⟩ => ?_
  have hw₂ : Ws t p.B p.Z W := hw.congrP (P := fun y => slot W qV + 8 ≤ y ∧ y < slot W qV + 16)
    (by rw [hm₂]; exact FrmP.of_writeW _ (by q_omega) fun _ h1 h2 => ⟨h1, h2⟩)
    (fun y hy => .inl (by omega_arith)) k12 (by decide)
  have hw₃ : Ws s₃ p.B p.Z W := hw₂.congr f₃ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Or.inl (by q_omega)) k₃ (by decide)
  refine ⟨hw₃, ?_, hc1, hcN, h8, kb.2, e3⟩
  rw [f₃.word_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> q_omega) (by q_omega), hm₂]
  rw [(writeW_outside s.mem p.B _ (by q_omega)).word (by q_omega) (by q_omega), hcnt]

theorem qBody_ct (e : Nat) : RelCT isa (Two (QB e)) qBody fun _ _ => True := by
  change RelCT isa _ (.seq (.block (qLoad ++ qDigit)) (.seq Impl.Rsa.X86_64.WordReduce.step
    (.block (qPos ++ qTail)))) _
  refine RelCT.seq (RelCT.block_append (pin_ct (Ψ := Q1 e) [.rdi] [.rdi, .r12, .r9, .rbp, .r11, .rcx] qLoadVal
    (pins_list (fun a => qLoadVal a) fun a s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.ws.rdi)
    (by taint_decide) (fun a s h => WP.mono (qLoad_ok h.ws h.cnt) fun t ⟨hdi, h12, h9, hbp, h11, hcx, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hdi
      · exact h12
      · exact h9
      · exact hbp
      · exact h11
      · exact hcx)
    (by taint_decide) fun a s h => qLoadDigit_ok h)) (RelCT.seq (two_post (Ψ := Q2 e)
      (two_taint [.rdi, .rbx, .r10, .r8, .rbp, .r12] (pins_list qStepVal fun a s h => h.choose_spec.2.1)
        (by taint_decide)) fun a s h => qStepW_ok h) ?_)
  refine RelCT.mono (RelCT.block_append (pin_ct (Ψ := fun _ _ => True) [.rdi] [.rdi, .rbx, .rax] qPosVal
    (pins_list (fun a => qPosVal a) fun a s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.1.rdi)
    (by taint_decide) (fun a s h => WP.mono (qPos_ok h.1 h.2.1) fun t ⟨hbx, hax, _, k⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (k.gpr (by decide)).trans h.1.rdi
      · exact hbx
      · exact hax)
    (by taint_decide) fun a s h => ?_)) (fun _ _ h => h) fun _ _ _ => trivial
  obtain ⟨hw, hc, hc1, hcN, h8, hk, e3⟩ := h
  have hZ := hw.hZ
  have h256 := hw.h256
  have hW := wW_eq a.1.k
  obtain ⟨sA, sQ, sR, sD, sT, sV, s16⟩ := qSlots (wW a.1.k)
  rw [s16] at hZ
  refine WP.seq (WP.mono (qPos_ok hw hc) fun t ⟨hbx, hax, _, k⟩ => WP.mono (qTail_ok (hw.scr.congr k.2.2)
    ((k.gpr (by decide)).trans hw.rdi) hbx hax hc1 (by omega_arith) (by omega_arith) h256) fun _ _ => trivial)

/-! ## `qDiv`'s setup -/

/-- The divisor's top bit set, for the public data. -/
def FDp (p : RpP) (s : State) : Prop := 2 ^ 63 ≤ (word s.mem p.B (slot (wW p.k) qD + 8 * (wk p.k - 1))).toNat

/-- Facts that writes to the arrays and the count keep. -/
abbrev ArrC (F : RpIn → State → Prop) : Prop := Stab F fun y => 256 ≤ y ∨ (200 ≤ y ∧ y < 208)

section
variable {F : RpIn → State → Prop}

theorem ArrC.arr (hF : ArrC F) : Arr F := fun I s t P h hf hP h1 h2 =>
  hF I s t P h hf (fun y hy => ⟨.inl (hP y hy).1, (hP y hy).2⟩) h1 h2

theorem outD {p : RpP} {s t : State} (h : GD wW F p s ∧ FDp p s) {o n : Nat}
    (ho : Outside p.B o n s.mem t.mem) (h256 : 256 ≤ o) (hon : o + n ≤ p.Z)
    (hfar : o + n ≤ slot (wW p.k) qD ∨ slot (wW p.k) qD + 8 * (wW p.k + 2) ≤ o) {regs : List Reg}
    (k : Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs) (hF : Arr F) : GD wW F p t ∧ FDp p t := by
  refine ⟨h.1.out ho h256 hon k hr hF, ?_⟩
  have hn := h.1.ws.scr.nowrap
  have hZ := h.1.ws.hZ
  have kb := h.1.kb
  have hW := wW_eq p.k
  have e16 := slotE (wW p.k) 16
  have eD := slotE (wW p.k) qD
  unfold FDp
  rw [ho.word (by simp only [qD] at *; omega_arith) (by simp only [qD] at *; omega_arith)]
  exact h.2

/-- `GD` after writes to arrays and the count. -/
theorem GD.frmC {p : RpP} {s t : State} (h : GD wW F p s) {rs : List (Nat × Nat)} (hf : Frm p.B rs s.mem t.mem)
    (hrs : ∀ r ∈ rs, (256 ≤ r.1 ∧ r.1 + r.2 ≤ p.Z) ∨ r = (200, 8)) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) (hF : ArrC F) : GD wW F p t := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have h256 := h.ws.h256
  have hP : ∀ y, (∃ r ∈ rs, r.1 ≤ y ∧ y < r.1 + r.2) → (256 ≤ y ∨ (200 ≤ y ∧ y < 208)) ∧ y < p.Z :=
    fun y ⟨r, hr, h1, h2⟩ => by
      rcases hrs r hr with ⟨a, b⟩ | rfl
      · exact ⟨.inl (by omega_arith), by omega_arith⟩
      · simp only at h1 h2; exact ⟨.inr ⟨h1, h2⟩, by omega_arith⟩
  have hf' : FrmP p.B (fun y => ∃ r ∈ rs, r.1 ≤ y ∧ y < r.1 + r.2) s.mem t.mem :=
    FrmP.of_frm hf fun r hr y h1 h2 => ⟨r, hr, h1, h2⟩
  refine h.next hf' (fun y hy => ⟨?_, (hP y hy).2⟩) k hr (fun c hc => ⟨c, ?_⟩)
    fun I e hFI => by subst e; exact hF I s t _ hFI hf' hP k.2.1 k.2.2
  · rcases (hP y hy).1 with a | a
    · exact .inl a
    · unfold DOk; omega_arith
  · unfold mw at hc ⊢
    rw [hf'.word_eq (fun y h1 h2 hy => by
      have := (hP y hy).1; simp only [Impl.Bignum.X86_64.Public.sMask, sFn] at h1 h2; omega_arith)
      (by simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith), hc]

theorem zeroQ_ct {j : Nat} (hj : j < 16) (hjD : j ≠ qD) (hF : Arr F) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8)) zeroAccLoop) hc).isSome = true) :
    RelCT isa (Two fun p s => GD wW F p s ∧ FDp p s) (zeroA j) (Two fun p s => GD wW F p s ∧ FDp p s) :=
  wsG_ct (w := wW) (F := F) (fun _ _ h => h.1) ht fun p s h => WP.mono (zeroA_ok h.1.ws hj) fun _ ⟨_, o, k⟩ =>
    outD h o (slot_256 _ _) (slot_Z h.1 hj) (by have := slot_far (w := wW p.k) hjD; omega_arith) k (by decide) hF

theorem qSeed_ct (e : Nat) (he1 : 1 ≤ e) (he3 : e ≤ 3) (hF : Arr F) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base qA .rsi ++ (base qR .rbx ++ (hOf ++
      ([.mov .rax (.reg .r12), .alu .add .rax (.imm (BitVec.ofNat 32 e)), .shift .shl .rax 3, .alu .add .rsi (.reg .rax),
        .alu .sub .r12 (.imm 1)] : List Instr))))) copyWords) hc).isSome = true) :
    RelCT isa (Two fun p s => GD wW F p s ∧ FDp p s) (qSeed e) (Two fun p s => GD wW F p s ∧ FDp p s) := by
  have eq : qSeed e = .seq (.block (ws ++ (base qA .rsi ++ (base qR .rbx ++ (hOf ++
      ([.mov .rax (.reg .r12), .alu .add .rax (.imm (BitVec.ofNat 32 e)), .shift .shl .rax 3, .alu .add .rsi (.reg .rax),
        .alu .sub .r12 (.imm 1)] : List Instr)))))) copyWords := by
    simp only [qSeed, List.append_assoc]
  rw [eq]
  refine wsG_ct (w := wW) (F := F) (fun _ _ h => h.1) ht fun p s h => ?_
  rw [← eq]
  have hw := h.1.ws
  have L : QLay (wW p.k) (wk p.k) e := ⟨wW_eq _, h.1.kb.1, he1, he3⟩
  have kb := h.1.kb
  have hW := wW_eq p.k
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  obtain ⟨sA, sQ, sR, sD, sT, sV, s16⟩ := qSlots (wW p.k)
  rw [s16] at hZ
  unfold qSeed
  refine WP.seq (WP.mono (qSeedB_ok hw L) fun u ⟨hsi, hbx, h12, mu, ku⟩ => ?_)
  have hsu := hw.scr.congr ku.2.2
  refine WP.mono (copyWords_ok hsi hbx h12 (by omega_arith) (by omega_arith) (by omega_arith)
    (fun i hi => hsu.ld (by omega_arith)) (fun i hi => hsu.st (by omega_arith))
    (fun i hi b hb => by rw [ofs_off p.B (by omega_arith)]; omega_arith)) fun t ⟨_, _, o, k⟩ => ?_
  rw [mu] at o
  exact outD h o (by omega_arith) (by omega_arith) (by omega_arith) (ku.trans k) (by decide) hF

theorem recipQ_ct (hF : Arr F) :
    RelCT isa (Two fun p s => GD wW F p s ∧ FDp p s)
      (.seq (.block (ws ++ base qD .r10 ++ base qV .r8 ++ hOf)) R2Words.recip)
      (Two fun p s => GD wW F p s ∧ FDp p s) := by
  have eq : ws ++ base qD .r10 ++ base qV .r8 ++ hOf = ws ++ (base qD .r10 ++ (base qV .r8 ++ hOf)) := by
    simp only [List.append_assoc]
  rw [eq]
  refine wsG_ct (w := wW) (F := F) (fun _ _ h => h.1) (by taint_decide) fun p s h => ?_
  rw [← eq]
  have hw := h.1.ws
  have L : QLay (wW p.k) (wk p.k) 1 := ⟨wW_eq _, h.1.kb.1, by decide, by decide⟩
  have kb := h.1.kb
  have hW := wW_eq p.k
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  obtain ⟨sA, sQ, sR, sD, sT, sV, s16⟩ := qSlots (wW p.k)
  rw [s16] at hZ
  refine WP.seq (WP.mono (qRcp_ok hw L) fun u ⟨h10, h8', h12, mu, ku⟩ =>
    WP.mono (R2w.recip_ok (hw.scr.congr ku.2.2) h10 h12 h8' (w := wk p.k) (by omega_arith) (by omega_arith)
      (by omega_arith) (by rw [mu]; exact h.2)) fun t ⟨m, k⟩ => ?_)
  rw [mu] at m
  have o : Outside p.B (slot (wW p.k) qV) 8 s.mem t.mem := by rw [m]; exact writeW_outside _ _ _ (by omega_arith)
  exact outD h o (by omega_arith) (by omega_arith) (by omega_arith) (ku.trans k) (by decide) hF

theorem qCnt_ct (e : Nat) (he1 : 1 ≤ e) (he3 : e ≤ 3) (hF : ArrC F) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (hOf ++ ([.mov .rax (.reg .r12),
      .alu .add .rax (.imm (BitVec.ofNat 32 e)), .store (hdr sCt) .rax] : List Instr))) hc).isSome = true) :
    RelCT isa (Two fun p s => GD wW F p s ∧ FDp p s)
      (.block (ws ++ hOf ++ ([.mov .rax (.reg .r12), .alu .add .rax (.imm (BitVec.ofNat 32 e)), .store (hdr sCt) .rax] :
        List Instr))) (Two fun p s => GD wW F p s ∧ FDp p s) := by
  rw [List.append_assoc]
  refine wsG_block_ct (w := wW) (F := F) (fun _ _ h => h.1) ht fun p s h => ?_
  rw [← List.append_assoc]
  have hw := h.1.ws
  have L : QLay (wW p.k) (wk p.k) e := ⟨wW_eq _, h.1.kb.1, he1, he3⟩
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  have h256 := hw.h256
  refine WP.mono (qCnt_ok hw L) fun t ⟨_, m, k⟩ => ⟨h.1.frmC (rs := [(200, 8)]) (by
    rw [m]; exact Frm.of_outside (writeW_outside _ _ _ (by simp only [sCt, sFn]; omega_arith)) (List.mem_singleton_self _))
    (fun r hr => .inr (List.mem_singleton.mp hr)) k (by decide) hF, ?_⟩
  have kb := h.1.kb
  have hW := wW_eq p.k
  have eD := slotE (wW p.k) qD
  unfold FDp
  rw [m, (writeW_outside s.mem p.B _ (by simp only [sCt, sFn]; omega_arith)).word (by simp only [qD] at *; simp only [sCt, sFn]; omega_arith)
    (by simp only [qD] at *; omega_arith)]
  exact h.2

end

/-! ## The division -/

/-- After `qDiv`'s setup: the loop's invariant with `h + e` steps left. -/
def QS (e : Nat) (F : RpIn → State → Prop) (p : RpP) (t : State) : Prop :=
  GD wW F p t ∧ ∃ M, 0 < M ∧ QInv t p.B p.Z (wW p.k) (wk p.k) e M (wk p.k + e) t ∧
    t.gpr .rax = BitVec.ofNat 64 (wk p.k + e) ∧
    2 ^ 63 ≤ (word t.mem p.B (slot (wW p.k) qD + 8 * (wk p.k - 1))).toNat ∧
    (word t.mem p.B (slot (wW p.k) qV)).toNat =
      (2 ^ 128 - 1) / (word t.mem p.B (slot (wW p.k) qD + 8 * (wk p.k - 1))).toNat - 2 ^ 64

/-- Before step `j` of `qDiv`'s loop. -/
def QL (e : Nat) (F : RpIn → State → Prop) (p : RpP) (j : Nat) (t : State) : Prop :=
  ∃ s₀ M, GD wW F p s₀ ∧ 0 < M ∧
    2 ^ 63 ≤ (word s₀.mem p.B (slot (wW p.k) qD + 8 * (wk p.k - 1))).toNat ∧
    (word s₀.mem p.B (slot (wW p.k) qV)).toNat =
      (2 ^ 128 - 1) / (word s₀.mem p.B (slot (wW p.k) qD + 8 * (wk p.k - 1))).toNat - 2 ^ 64 ∧
    QInv s₀ p.B p.Z (wW p.k) (wk p.k) e M (wk p.k + e - j) t

section
variable {F : RpIn → State → Prop}

theorem pos_of_top {m : Mem} {B : Addr} {d h : Nat} (h1 : 1 ≤ h) (hd : 2 ^ 63 ≤ (word m B (d + 8 * (h - 1))).toNat) :
    0 < wv m B d h := by
  have := wv_add m B d (h - 1) 1
  rw [show h - 1 + 1 = h by omega_arith] at this
  simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero] at this
  have hp := Nat.two_pow_pos (64 * (h - 1))
  have : 0 < 2 ^ (64 * (h - 1)) * (word m B (d + 8 * (h - 1))).toNat := Nat.mul_pos hp (by omega_arith)
  omega_arith

theorem qLoop_ct (e : Nat) (he1 : 1 ≤ e) (he3 : e ≤ 3) (hF : ArrC F) :
    RelCT isa (Two (QS e F)) (.loop qBody .ne) (Two (GD wW F)) := by
  refine ct_pre (two_loop (Φ := QL e F) (fun p => wk p.k + e)
    (two_map (fun q => (q.1, wk q.1.k + e - q.2)) (fun q s ⟨hj, s₀, M, g, hM, hd, hv, hI⟩ => ?_) (qBody_ct e))
    fun p j s hj ⟨s₀, M, g, hM, hd, hv, hI⟩ => ?_) fun p s ⟨g, M, hM, hI, ha, hd, hv⟩ =>
      ⟨by omega_arith, s, M, g, hM, hd, hv, by rw [Nat.sub_zero]; exact hI⟩
  · have kb := g.kb
    refine WP.mono (qIter_ok ⟨wW_eq _, kb.1, he1, he3⟩ hI (by omega_arith) (by omega_arith) hM hd hv)
      fun s' ⟨hI', _, hz⟩ => ⟨?_, fun hl => ⟨s₀, M, g, hM, hd, hv, ?_⟩, fun he => ?_⟩
    · simp only [eval, hz, Option.map_some, Option.some.injEq]
      by_cases hl : j + 1 < wk p.k + e
      · rw [decide_eq_true hl, decide_eq_false (by omega_arith)]; rfl
      · rw [decide_eq_false hl, decide_eq_true (by omega_arith)]; rfl
    · rwa [show wk p.k + e - (j + 1) = wk p.k + e - j - 1 by omega_arith]
    · have hn := hI'.ws.scr.nowrap
      have hZ := hI'.ws.hZ
      have hW := wW_eq p.k
      obtain ⟨sA, sQ, sR, sD, sT, sV, s16⟩ := qSlots (wW p.k)
      rw [s16] at hZ
      refine g.frmC hI'.frm (fun r hr => ?_) hI'.keep (by simp [mmRegs]) hF
      simp only [qRsAll, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact .inl ⟨by omega_using [sT], by omega_using [sT, hZ, hW]⟩
      · exact .inl ⟨by omega_using [sR], by omega_using [sR, hZ, hW]⟩
      · exact .inl ⟨by omega_using [sV], by omega_using [sV, hZ]⟩
      · exact .inl ⟨by omega_using [sQ], by omega_using [sQ, hZ]⟩
      · exact .inr rfl
  · obtain ⟨p, j⟩ := q
    simp only at hj hd hv hI ⊢
    have kb := g.kb
    exact ⟨hI.ws, kb, he1, he3, hI.cnt, by show 1 ≤ wk p.k + e - j; omega_using [hj], by show wk p.k + e - j ≤ wk p.k + e; omega_using [], by rw [hI.top]; exact hd,
      by rw [hI.recip, hI.top]; exact hv, by rw [hI.rem, hI.dv]; exact Nat.mod_lt _ hM⟩

theorem qPre_ct (e : Nat) (he1 : 1 ≤ e) (he3 : e ≤ 3) (hF : ArrC F) {h₁ h₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (tS : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base qA .rsi ++ (base qR .rbx ++ (hOf ++
      ([.mov .rax (.reg .r12), .alu .add .rax (.imm (BitVec.ofNat 32 e)), .shift .shl .rax 3, .alu .add .rsi (.reg .rax),
        .alu .sub .r12 (.imm 1)] : List Instr))))) copyWords) h₁).isSome = true)
    (tC : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (hOf ++ ([.mov .rax (.reg .r12),
      .alu .add .rax (.imm (BitVec.ofNat 32 e)), .store (hdr sCt) .rax] : List Instr))) h₂).isSome = true) :
    RelCT isa (Two fun p s => GD wW F p s ∧ FDp p s) (seqs [zeroA qQ, zeroA qR, zeroA qT, zeroA qV, qSeed e,
      .seq (.block (ws ++ base qD .r10 ++ base qV .r8 ++ hOf)) R2Words.recip,
      .block (ws ++ hOf ++ ([.mov .rax (.reg .r12), .alu .add .rax (.imm (BitVec.ofNat 32 e)), .store (hdr sCt) .rax] :
        List Instr))]) (Two (QS e F)) := by
  have hA := hF.arr
  refine two_post ((ct_cons (List.cons_ne_nil _ _) (zeroQ_ct (j := qQ) (by decide) (by decide) hA (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (zeroQ_ct (j := qR) (by decide) (by decide) hA (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (zeroQ_ct (j := qT) (by decide) (by decide) hA (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (zeroQ_ct (j := qV) (by decide) (by decide) hA (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (qSeed_ct e he1 he3 hA tS)
    (ct_cons (List.cons_ne_nil _ _) (recipQ_ct hA) (ct_one (qCnt_ct e he1 he3 hF tC)))))))).mono
      (fun _ _ h => h) fun _ _ _ => trivial) fun p s h => ?_
  have hw := h.1.ws
  have kb := h.1.kb
  have L : QLay (wW p.k) (wk p.k) e := ⟨wW_eq _, kb.1, he1, he3⟩
  refine WP.mono (qPre_ok hw L h.2) fun t ⟨hI, ha, top, rcp, _, _, _, f, k⟩ => ⟨?_, _,
    pos_of_top (by omega_arith) h.2, hI, ha, by rw [top]; exact h.2, rcp⟩
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  have hW := wW_eq p.k
  obtain ⟨sA, sQ, sR, sD, sT, sV, s16⟩ := qSlots (wW p.k)
  rw [s16] at hZ
  refine h.1.frmC f (fun r hr => ?_) k (by simp [mmRegs]) hF
  simp only [qDivRs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact .inl ⟨by omega_using [sQ], by omega_using [sQ, hZ]⟩
  · exact .inl ⟨by omega_using [sR], by omega_using [sR, hZ]⟩
  · exact .inl ⟨by omega_using [sT], by omega_using [sT, hZ]⟩
  · exact .inl ⟨by omega_using [sV], by omega_using [sV, hZ]⟩
  · exact .inr rfl

/-- `qDiv e`, from the divisor's top bit set. -/
theorem qDiv_ct (e : Nat) (he1 : 1 ≤ e) (he3 : e ≤ 3) (hF : ArrC F) {h₁ h₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (tS : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base qA .rsi ++ (base qR .rbx ++ (hOf ++
      ([.mov .rax (.reg .r12), .alu .add .rax (.imm (BitVec.ofNat 32 e)), .shift .shl .rax 3, .alu .add .rsi (.reg .rax),
        .alu .sub .r12 (.imm 1)] : List Instr))))) copyWords) h₁).isSome = true)
    (tC : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (hOf ++ ([.mov .rax (.reg .r12),
      .alu .add .rax (.imm (BitVec.ofNat 32 e)), .store (hdr sCt) .rax] : List Instr))) h₂).isSome = true) :
    RelCT isa (Two fun p s => GD wW F p s ∧ FDp p s) (seqs (qDiv e)) (Two (GD wW F)) := by
  have eq : qDiv e = [zeroA qQ, zeroA qR, zeroA qT, zeroA qV, qSeed e,
      .seq (.block (ws ++ base qD .r10 ++ base qV .r8 ++ hOf)) R2Words.recip,
      .block (ws ++ hOf ++ ([.mov .rax (.reg .r12), .alu .add .rax (.imm (BitVec.ofNat 32 e)), .store (hdr sCt) .rax] :
        List Instr))] ++ [.loop qBody .ne] := rfl
  rw [eq]
  exact ct_app (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) (qPre_ct e he1 he3 hF tS tC)
    (ct_one (qLoop_ct e he1 he3 hF))

end

end VG.Proof.Rsa.X86_64.Rd
