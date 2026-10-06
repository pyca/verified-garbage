import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs

/-!
# RSA with the CRT on AArch64: constant time, the steps of `p`'s phase

How a phase is composed: each piece's claim, for a predicate that carries
its hypotheses and what correctness gives after it (`ct_step`), and
`subModArr` (`subModArr_ct`), whose two loops run from bases loaded from the
header: the loads before the second loop are checked from `x0` and `x12`,
which the first loop keeps (`smMid_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-! ## Composing pieces -/

/-- A piece whose claim holds for public data `g a`, then the rest, from
what correctness gives after the piece. -/
theorem ct_step {α β : Type} {Φ Ψ : α → State → Prop} {P : β → State → Prop} {c rest : Prog isa}
    (g : α → β) (hP : ∀ a s, Φ a s → P (g a) s) (hw : ∀ a s, Φ a s → WP isa c s (Ψ a))
    (hc : RelCT isa (Two P) c fun _ _ => True) (hr : RelCT isa (Two Ψ) rest fun _ _ => True) :
    RelCT isa (Two Φ) (.seq c rest) fun _ _ => True :=
  RelCT.seq (two_post (two_map g hP hc) hw) hr

/-- A piece checked by the taint analysis from the registers `rs`, then the rest. -/
theorem ct_taint {α : Type} {Φ Ψ : α → State → Prop} {c rest : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) (hr : RelCT isa (Two Ψ) rest fun _ _ => True) :
    RelCT isa (Two Φ) (.seq c rest) fun _ _ => True :=
  RelCT.seq (two_piece rs hpin h hw) hr

/-- A list of pieces whose claim holds for public data `g a`, then the rest. -/
theorem ct_steps {α β : Type} {Φ Ψ : α → State → Prop} {P : β → State → Prop} {c rest : List (Prog isa)}
    (hc0 : c ≠ []) (hr0 : rest ≠ []) (g : α → β) (hP : ∀ a s, Φ a s → P (g a) s)
    (hw : ∀ a s, Φ a s → WP isa (seqs c) s (Ψ a))
    (hc : RelCT isa (Two P) (seqs c) fun _ _ => True) (hr : RelCT isa (Two Ψ) (seqs rest) fun _ _ => True) :
    RelCT isa (Two Φ) (seqs (c ++ rest)) fun _ _ => True :=
  RelCT.seqs_append hc0 hr0 (ct_step g hP hw hc hr)

/-- The last piece. -/
theorem ct_last {α β : Type} {Φ : α → State → Prop} {P : β → State → Prop} {c : Prog isa}
    (g : α → β) (hP : ∀ a s, Φ a s → P (g a) s) (hc : RelCT isa (Two P) c fun _ _ => True) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  two_map g hP hc

/-! ## `subModArr` -/

/-- `subModArr`'s blocks and loops. -/
def smBlk1 (a b : Nat) : List Instr :=
  [ldh .x16 (sArr a), ldh .x17 (sArr b), ldh .x13 (sArr Public.aAcc), ldh .x12 sW, movi .x7 0, mov .x14 .x12,
    .subs .x .x3 .x7 .x7]

def smLoop1 : Prog isa :=
  countLoop .x14 [ld .x3 .x16, ld .x4 .x17, .sbcs .x .x3 .x3 .x4, st .x3 .x13, next .x16, next .x17, next .x13]

def smBlk3 (o : Nat) : List Instr :=
  borrowMask ++ [ldh .x10 (sArr Public.aN), ldh .x8 (sArr Public.aAcc), ldh .x5 (sArr o), mov .x14 .x12,
    .adds .x .x3 .x7 .x7]

def smLoop2 : Prog isa :=
  countLoop .x14 [ld .x3 .x10, .logic .and .x .x3 .x3 .x15, ld .x4 .x8, .adcs .x .x3 .x3 .x4, st .x3 .x5,
    next .x10, next .x8, next .x5]

theorem subModArr_eq (o a b : Nat) :
    seqs (subModArr o a b) = .seq (.block (smBlk1 a b)) (.seq smLoop1 (.seq (.block (smBlk3 o)) smLoop2)) := rfl

/-- `subModArr`'s hypotheses for its timing: the workspace and its size. -/
def SmPre (L : Ws) (s : State) : Prop := GoodW L s ∧ 2 ≤ L.w ∧ L.w < 2 ^ 31

/-- Before `subModArr aT aY aXc`'s first loop. -/
def Sm1 (L : Ws) (t : State) : Prop :=
  ∃ minv, Good t L.B L.Z L.w minv ∧ slot L.w 8 ≤ L.Z ∧ 2 ≤ L.w ∧ L.w < 2 ^ 31 ∧
    t.gpr .x16 = off L.B (slot L.w Public.aY) ∧ t.gpr .x17 = off L.B (slot L.w aXc) ∧
    t.gpr .x13 = off L.B (slot L.w Public.aAcc) ∧ t.gpr .x12 = BitVec.ofNat 64 L.w ∧ t.gpr .x7 = 0 ∧
    t.gpr .x14 = BitVec.ofNat 64 L.w ∧ t.c = true

/-- Before its second loop: its bases and count. -/
def Sm3 (L : Ws) (t : State) : Prop :=
  t.gpr .x0 = L.B ∧ t.gpr .x10 = off L.B (slot L.w Public.aN) ∧ t.gpr .x8 = off L.B (slot L.w Public.aAcc) ∧
    t.gpr .x5 = off L.B (slot L.w aT) ∧ t.gpr .x14 = BitVec.ofNat 64 L.w

theorem pins_smPre : Pins SmPre [.x0] := fun L s₁ s₂ h₁ h₂ => pins_goodW L s₁ s₂ h₁.1 h₂.1

theorem pins_sm1 : Pins Sm1 [.x0, .x12, .x13, .x14, .x16, .x17] := by
  intro L s₁ s₂ ⟨_, g₁, _, _, _, a₁, b₁, c₁, d₁, _, e₁, _⟩ ⟨_, g₂, _, _, _, a₂, b₂, c₂, d₂, _, e₂, _⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [g₁.x0, g₂.x0]
  · rw [d₁, d₂]
  · rw [c₁, c₂]
  · rw [e₁, e₂]
  · rw [a₁, a₂]
  · rw [b₁, b₂]

theorem pins_sm3 : Pins Sm3 [.x0, .x5, .x8, .x10, .x14] := by
  intro L s₁ s₂ ⟨a₁, b₁, c₁, d₁, e₁⟩ ⟨a₂, b₂, c₂, d₂, e₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [d₁, d₂]
  · rw [c₁, c₂]
  · rw [b₁, b₂]
  · rw [e₁, e₂]

/-- `subModArr aT aY aXc`'s first block. -/
theorem sm1_ok {L : Ws} {s : State} (h : SmPre L s) : WP isa (.block (smBlk1 Public.aY aXc)) s (Sm1 L) := by
  obtain ⟨⟨minv, hg, hZ⟩, hw, hw'⟩ := h
  have hl := GoodW.hl ⟨minv, hg, hZ⟩
  have sa : ∀ j < 8, sArr j < 32 := fun j hj => by unfold sArr; omega
  refine WP.mono (WP.keep [.x3, .x7, .x12, .x13, .x14, .x16, .x17] (Q := fun t =>
      t.gpr .x16 = off L.B (slot L.w Public.aY) ∧ t.gpr .x17 = off L.B (slot L.w aXc) ∧
      t.gpr .x13 = off L.B (slot L.w Public.aAcc) ∧ t.gpr .x12 = BitVec.ofNat 64 L.w ∧ t.gpr .x7 = 0 ∧
      t.gpr .x14 = BitVec.ofNat 64 L.w ∧ t.c = true ∧ t.mem = s.mem)
    (by brun [smBlk1, hg.x0, hdr_enc (sa _ (show Public.aY < 8 by decide)), hdr_enc (sa _ (show aXc < 8 by decide)),
      hdr_enc (sa _ (show Public.aAcc < 8 by decide)), hdr_enc (show sW < 32 by decide),
      hl _ (sa _ (show Public.aY < 8 by decide)), hl _ (sa _ (show aXc < 8 by decide)),
      hl _ (sa _ (show Public.aAcc < 8 by decide)), hl sW (by decide), hg.hdr.harr Public.aY (by decide),
      hg.hdr.harr aXc (by decide), hg.hdr.harr Public.aAcc (by decide), hg.hdr.hw])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h16, h17, h13, h12, h7, h14, hc, hm⟩, k⟩ => ?_
  exact ⟨minv, ⟨hg.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hg.x0, by rw [hm]; exact hg.hdr⟩, hZ, hw, hw',
    h16, h17, h13, h12, h7, h14, hc⟩

/-- `subModArr aT aY aXc`'s first loop and the block after it, as
`subModArr_ok` runs them. -/
theorem smMid_ok {L : Ws} {t : State} (h : Sm1 L t) :
    WP isa (.seq smLoop1 (.block (smBlk3 aT))) t (Sm3 L) := by
  obtain ⟨minv, hg, hZ, hw, hw', h16, h17, h13, h12, h7, h14, hc₁⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot L.w j + 8 * (L.w + 2) ≤ L.Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have sa : ∀ j < 8, sArr j < 32 := fun j hj => by unfold sArr; omega
  have h0' : SubInv t L.B L.Z (slot L.w Public.aY) (slot L.w aXc) (slot L.w Public.aAcc) 0 t :=
    ⟨hs, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, by rw [h13]; rfl, Outside.refl _ _ _ _,
      by rw [hc₁]; rfl⟩
  refine WP.seq (WP.mono (wp_countdown (N := L.w) (by omega) (by omega)
    (SubInv t L.B L.Z (slot L.w Public.aY) (slot L.w aXc) (slot L.w Public.aAcc))
    (fun j hj u hI _ => subStep_ok (by have := sl _ (show Public.aY < 8 by decide); omega)
      (by have := sl _ (show aXc < 8 by decide); omega) (by have := sl _ (show Public.aAcc < 8 by decide); omega)
      (by have := arr_sep (w := L.w) (show Public.aY ≠ Public.aAcc by decide); omega)
      (by have := arr_sep (w := L.w) (show aXc ≠ Public.aAcc by decide); omega) hj hI) h0' h14) fun s₂ hI => ?_)
  have s₂0 : s₂.gpr .x0 = L.B := (hI.keep.gpr .x0 (by decide)).trans hg.x0
  have s₂7 : s₂.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans h7
  have s₂12 : s₂.gpr .x12 = BitVec.ofNat 64 L.w := (hI.keep.gpr .x12 (by decide)).trans h12
  have hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off L.B (8 * i)) 8 := fun i hi =>
    hI.scr.ld (by have := hdr_lt_slot L.w 8 hi; omega)
  have fh : ∀ i < 32, word s₂.mem L.B (8 * i) = word t.mem L.B (8 * i) := fun i hi =>
    hI.out.word (Or.inl (by have := hdr_lt_slot L.w Public.aAcc hi; omega)) (by have := hdr_lt_slot L.w 8 hi; omega)
  have aN : word s₂.mem L.B (8 * sArr Public.aN) = off L.B (slot L.w Public.aN) :=
    (fh _ (sa _ (show Public.aN < 8 by decide))).trans (hg.hdr.harr _ (show Public.aN < 8 by decide))
  have aA : word s₂.mem L.B (8 * sArr Public.aAcc) = off L.B (slot L.w Public.aAcc) :=
    (fh _ (sa _ (show Public.aAcc < 8 by decide))).trans (hg.hdr.harr _ (show Public.aAcc < 8 by decide))
  have aT' : word s₂.mem L.B (8 * sArr aT) = off L.B (slot L.w aT) :=
    (fh _ (sa _ (show aT < 8 by decide))).trans (hg.hdr.harr aT (by decide))
  have e1 := hdr_enc (sa _ (show Public.aN < 8 by decide))
  have e2 := hdr_enc (sa _ (show Public.aAcc < 8 by decide))
  have e3 := hdr_enc (sa _ (show aT < 8 by decide))
  have l1 := hl₂ _ (sa _ (show Public.aN < 8 by decide))
  have l2 := hl₂ _ (sa _ (show Public.aAcc < 8 by decide))
  have l3 := hl₂ _ (sa _ (show aT < 8 by decide))
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x8, .x10, .x14, .x15] (Q := Sm3 L) ?_
    (by decide) (by decide) (by decide +kernel)) fun _ h => h.1
  brun [Sm3, smBlk3, borrowMask, s₂0, s₂7, s₂12, csel_mask_not, e1, e2, e3, l1, l2, l3, aN, aA, aT']

/-- `subModArr aT aY aXc`, `p`'s difference, is constant time. -/
theorem subModArr_ct : RelCT isa (Two SmPre) (seqs (subModArr aT Public.aY aXc)) fun _ _ => True := by
  rw [subModArr_eq]
  refine RelCT.seq (two_piece (Ψ := Sm1) [.x0] pins_smPre (by taint_decide) fun _ _ h => sm1_ok h) ?_
  refine RelCT.assoc (RelCT.seq (two_piece (Ψ := Sm3) [.x0, .x12, .x13, .x14, .x16, .x17] pins_sm1
    (by taint_decide) fun _ _ h => smMid_ok h) ?_)
  exact two_taint [.x0, .x5, .x8, .x10, .x14] pins_sm3 (by taint_decide)

end VG.Proof.Bignum.AArch64
