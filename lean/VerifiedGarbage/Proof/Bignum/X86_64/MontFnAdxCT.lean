import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdx

/-!
# `vg_rsa_mont_mul_adx`: constant time

After `zext`, for public indices (`AdxIn`): the head is checked by the taint
analysis from `rdi` and the indices; the size test and the choice of tiles
are taken alike in both runs because `w` and the indices are public; the
tiles are constant time for the slots the head wrote (`Ops`), and the
baseline's rounds from the bases; the tail addresses only from `rdi`, which
no instruction of the body writes.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.MontFn
open VG.Proof.MlKem.X86_64

/-- The public data of a call: the working space, its size, `w` and the indices. -/
structure CallData where
  B : Addr
  Z : Nat
  w : Nat
  o : Nat
  a : Nat
  b : Nat

/-- Indices of operands: arrays, not the function's own. -/
def Opnds (o a b : Nat) : Prop :=
  o < 8 ∧ a < 8 ∧ b < 8 ∧ o ≠ aAcc ∧ o ≠ aTmp ∧ a ≠ aAcc ∧ a ≠ aTmp ∧ b ≠ aAcc ∧ b ≠ aTmp

/-- After `zext`: the working space and its header, and the indices in
`rdx`, `rcx` and `r8`. -/
def AdxIn (d : CallData) (s : State) : Prop :=
  Scr s d.B d.Z ∧ s.gpr .rdi = d.B ∧ (∃ mi, Hdr s.mem d.B d.w mi) ∧ slot d.w 8 ≤ d.Z ∧ Opnds d.o d.a d.b ∧
    s.gpr .rdx = BitVec.ofNat 64 d.o ∧ s.gpr .rcx = BitVec.ofNat 64 d.a ∧ s.gpr .r8 = BitVec.ofNat 64 d.b

/-- After the head: also the operands' slots. -/
def AdxMid (d : CallData) (s : State) : Prop := AdxIn d s ∧ Ops s.mem d.B d.w (adxOps d.o d.a d.b)

theorem pins_adxIn : Pins AdxIn [.rdi, .rdx, .rcx, .r8] := by
  intro d s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨-, a₁, -, -, -, b₁, c₁, d₁⟩ := h₁
  obtain ⟨-, a₂, -, -, -, b₂, c₂, d₂⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]

theorem pins_adxMid : Pins AdxMid [.rdi, .rdx, .rcx, .r8] :=
  fun d s₁ s₂ h₁ h₂ => pins_adxIn d s₁ s₂ h₁.1 h₂.1

theorem AdxIn.of_keep {d : CallData} {s t : State} (h : AdxIn d s) (hm : t.mem = s.mem) {rs : List Reg}
    (k : Keep rs s t) (hcx' : t.gpr .rcx = s.gpr .rcx) (hr : Reg.rdi ∉ rs ∧ Reg.rdx ∉ rs ∧ Reg.r8 ∉ rs) :
    AdxIn d t := by
  obtain ⟨hs, hdi, ⟨mi, hH⟩, hZ, op, hdx, hcx, h8⟩ := h
  exact ⟨hs.congr k.2.2, (k.gpr hr.1).trans hdi, ⟨mi, hm ▸ hH⟩, hZ, op, (k.gpr hr.2.1).trans hdx,
    hcx'.trans hcx, (k.gpr hr.2.2).trans h8⟩

theorem head_fw (d : CallData) (s : State) (h : AdxIn d s) : WP isa (.block (saves ++ slotsIn)) s (AdxMid d) := by
  obtain ⟨hs, hdi, ⟨mi, hH⟩, hZ, op, hdx, hcx, h8⟩ := h
  refine WP.mono (adxRest_ok hs hdi hH hZ op.1 op.2.1 op.2.2.1 hdx hcx h8) fun t ⟨hm, k, _⟩ => ?_
  exact ⟨⟨hs.congr k.2.2, (k.gpr (by decide)).trans hdi, ⟨mi, hm ▸ headMem_hdr hH _ _ _⟩, hZ, op,
    (k.gpr (by decide)).trans hdx, (k.gpr (by decide)).trans hcx, (k.gpr (by decide)).trans h8⟩,
    hm ▸ headMem_ops _ _ _ _ _ _⟩

/-- The tiled code, for a layout the size test admits. -/
def adxLayout (d : CallData) (hZ : slot d.w 8 ≤ d.Z) (h : AlignOk d.w) : AdxTiledProduct.Layout :=
  ⟨d.B, d.Z, d.w, d.w / 8, hZ, by unfold AlignOk at h; omega, by unfold AlignOk at h; omega,
    by unfold AlignOk at h; omega⟩

theorem goodV_of_mid {d : CallData} {s : State} (h : AdxMid d s) (hZ : slot d.w 8 ≤ d.Z) (hA : AlignOk d.w) :
    AdxTiledProduct.GoodV (adxOps d.o d.a d.b) (adxLayout d hZ hA) s := by
  obtain ⟨⟨hs, hdi, ⟨mi, hH⟩, -⟩, hv⟩ := h
  exact ⟨⟨mi, hs, hdi, hH⟩, hv⟩

/-- The tiles. -/
theorem tiled_ct : RelCT isa (Two fun d s => (AdxMid d s ∧ s.zf = some (decide (AlignOk d.w))) ∧
    isa.eval .e s = some true) tiled fun _ _ => True := by
  unfold tiled
  refine RelCT.seq (two_piece (Ψ := fun d s => (AdxMid d s ∧ AlignOk d.w) ∧ s.zf = some (decide (d.a = d.b)))
    [.rcx, .r8] (fun d s₁ s₂ h₁ h₂ r hr => pins_adxMid d s₁ s₂ h₁.1.1 h₂.1.1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp))
    (by taint_decide) ?_) ?_
  · rintro d s ⟨⟨hm, hz⟩, he⟩
    have hA : AlignOk d.w := by simpa only [eval, hz, Option.some.injEq, decide_eq_true_eq] using he
    have ha := hm.1.2.2.2.2.1.2.1
    have hb := hm.1.2.2.2.2.1.2.2.1
    have hcx := hm.1.2.2.2.2.2.2.1
    have h8 := hm.1.2.2.2.2.2.2.2
    exact WP.mono (cmpIdx_ok ha hb hcx h8) fun t ⟨hz', hm', hc', k⟩ =>
      ⟨⟨⟨AdxIn.of_keep hm.1 hm' k hc' (by decide), hm' ▸ hm.2⟩, hA⟩, hz'⟩
  refine two_ite (fun d s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_
  · rintro s₁ s₂ t₁ t₂ s₁' s₂' ⟨d, ⟨⟨⟨h₁, hA⟩, z₁⟩, e₁⟩, ⟨⟨h₂, -⟩, -⟩, -⟩ e₁' e₂'
    have hab : d.a = d.b := by simpa only [eval, z₁, Option.some.injEq, decide_eq_true_eq] using e₁
    have hZ := h₁.1.2.2.2.1
    obtain ⟨-, ha, -, -, -, ha1, ha2, -⟩ := h₁.1.2.2.2.2.1
    exact AdxTiledSquare.montSquare_ct (ps := adxOps d.o d.a d.b) (mem_adxOps_o _ _ _) (mem_adxOps_a _ _ _) ha
      ha1 ha2 (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide) _ _ _ _ _ _
      ⟨adxLayout d hZ hA, goodV_of_mid h₁ hZ hA, goodV_of_mid h₂ hZ hA⟩ e₁' e₂'
  · rintro s₁ s₂ t₁ t₂ s₁' s₂' ⟨d, ⟨⟨⟨h₁, hA⟩, -⟩, -⟩, ⟨⟨h₂, -⟩, -⟩, -⟩ e₁' e₂'
    have hZ := h₁.1.2.2.2.1
    obtain ⟨-, ha, hb, -, -, ha1, ha2, hb1, hb2⟩ := h₁.1.2.2.2.2.1
    exact AdxTiledProduct.montMul_ct (ps := adxOps d.o d.a d.b) (mem_adxOps_o _ _ _) (mem_adxOps_a _ _ _)
      (mem_adxOps_b _ _ _) ha hb ha1 ha2 hb1 hb2 (by taint_decide) (by taint_decide) (by taint_decide)
      _ _ _ _ _ _ ⟨adxLayout d hZ hA, goodV_of_mid h₁ hZ hA, goodV_of_mid h₂ hZ hA⟩ e₁' e₂'

/-- `montMul`, from the bases `basesR` loads. -/
theorem fallback_ct : RelCT isa (Two fun d s => (AdxMid d s ∧ s.zf = some (decide (AlignOk d.w))) ∧
    isa.eval .e s = some false)
    (.seq (.block basesR) (.seq zeroAccLoop (.seq rounds (.seq subMod selectAcc)))) fun _ _ => True := by
  refine RelCT.seq (two_piece (Ψ := fun d => BasesL aN aAcc aTmp d.o d.a d.b ⟨d.B, d.Z, d.w⟩) [.rdi, .rdx, .rcx, .r8]
    (fun d s₁ s₂ h₁ h₂ => pins_adxMid d s₁ s₂ h₁.1.1 h₂.1.1) (by taint_decide) ?_)
    (two_taint _ (fun d => pins_bases aN aAcc aTmp d.o d.a d.b ⟨d.B, d.Z, d.w⟩) (by taint_decide))
  rintro d s ⟨⟨⟨⟨hs, hdi, ⟨mi, hH⟩, hZ, ⟨ho, ha, hb, -⟩, hdx, hcx, h8⟩, -⟩, -⟩, -⟩
  exact WP.mono (basesR_ok hs hdi hH hZ ho ha hb hdx hcx h8) fun t ⟨u1, u2, u3, u4, u5, u6, _, u8, _⟩ =>
    ⟨u1, u2, u3, u4, u5, u6, u8⟩

theorem adxBody_ct : RelCT isa (Two AdxMid) adxBody fun _ _ => True := by
  unfold adxBody
  refine RelCT.seq (two_piece (Ψ := fun d s => AdxMid d s ∧ s.zf = some (decide (AlignOk d.w))) [.rdi]
    (fun d s₁ s₂ h₁ h₂ r hr => pins_adxMid d s₁ s₂ h₁ h₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; simp [hr])) (by taint_decide) ?_)
    (two_ite (fun d s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) tiled_ct fallback_ct)
  rintro d s ⟨hm, hv⟩
  obtain ⟨hs, hdi, ⟨mi, hH⟩, hZ, -⟩ := id hm
  exact WP.mono (alignTest_ok hs hdi hH hZ) fun t ⟨hz, hm', k⟩ =>
    ⟨⟨AdxIn.of_keep hm hm' k (k.gpr (by decide)) (by decide), hm' ▸ hv⟩, hz⟩

/-- A relation after code that never writes `rdi`. -/
theorem RelCT.keepRdi {α : Type} {Φ : α → State → Prop} {c : Prog isa} {f : α → Addr}
    (h : RelCT isa (Two Φ) c fun _ _ => True) (hc : (instrs c).all (fun i => !Taint.clobbers i .rdi) = true)
    (hΦ : ∀ a s, Φ a s → s.gpr .rdi = f a) : RelCT isa (Two Φ) c (Two fun a s => s.gpr .rdi = f a) := by
  have hc' : ∀ i ∈ instrs c, Taint.clobbers i .rdi = false := fun i hi => by
    simpa using List.all_eq_true.mp hc i hi
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨a, h₁, h₂⟩ e₁ e₂
  exact ⟨(h _ _ _ _ _ _ ⟨a, h₁, h₂⟩ e₁ e₂).1, a, (Exec.gpr hc' e₁).trans (hΦ a _ h₁),
    (Exec.gpr hc' e₂).trans (hΦ a _ h₂)⟩

/-- `vg_rsa_mont_mul_adx` after the head. -/
theorem adxTail_ct : RelCT isa (Two AdxMid) (.seq adxBody (.block restore)) fun _ _ => True :=
  RelCT.seq (RelCT.keepRdi (f := CallData.B) adxBody_ct (by rw [← Code.allInstrs_eq]; decide +kernel)
    fun _ _ h => h.1.2.1)
    (two_taint [.rdi] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [h₁, h₂]) (by taint_decide))

/-- `vg_rsa_mont_mul_adx` after `zext`. -/
theorem adxCore_ct : RelCT isa (Two AdxIn) (.seq (.block (saves ++ slotsIn)) (.seq adxBody (.block restore)))
    fun _ _ => True :=
  RelCT.seq (two_piece _ pins_adxIn (by taint_decide) head_fw) adxTail_ct

/-- After the head, from `enter ++ slotsIn`. -/
theorem AdxMid.of_head {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {o a b : Nat} (op : Opnds o a b)
    (hm : t.mem = headMem s.mem B w o a b) (hdx : t.gpr .rdx = BitVec.ofNat 64 o)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 a) (h8 : t.gpr .r8 = BitVec.ofNat 64 b)
    (k : Keep [.rdx, .rcx, .r8, .rax] s t) : AdxMid ⟨B, Z, w, o, a, b⟩ t :=
  ⟨⟨hs.congr k.2.2, (k.gpr (by decide)).trans hdi, ⟨minv, hm ▸ headMem_hdr hH _ _ _⟩, hZ, op, hdx, hcx, h8⟩,
    hm ▸ headMem_ops _ _ _ _ _ _⟩

end VG.Proof.Bignum.X86_64
