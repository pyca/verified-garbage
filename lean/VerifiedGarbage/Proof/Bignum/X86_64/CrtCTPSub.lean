import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs

/-!
# RSA with the CRT on x86-64: constant time, the steps of `p`'s phase

How a phase is composed: each piece's claim, for a predicate that carries
its hypotheses and what correctness gives after it (`ct_step`), and
`subModArr` (`subModArr_ct`), whose two loops run from bases loaded from the
header: the second block's header loads are checked from `rdi`, which the
first loop keeps (`subModArr_wp`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-! ## Composing pieces

`CTMain`'s `RelCT.seqs_append`, which this file cannot import (its names
clash with `CrtCTDefs`'). -/

theorem exec_seqs_app {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ []) {s s' : State} {t : List Leak}
    (e : Exec isa (seqs (a ++ b)) s t s') : Exec isa (.seq (seqs a) (seqs b)) s t s' := by
  induction a generalizing s t with
  | nil => exact absurd rfl ha
  | cons c a ih =>
    cases a with
    | nil =>
      obtain ⟨d, rest, rfl⟩ := List.exists_cons_of_ne_nil hb
      exact e
    | cons d rest =>
      change Exec isa (.seq c (seqs (d :: rest ++ b))) s t s' at e
      change Exec isa (.seq (.seq c (seqs (d :: rest))) (seqs b)) s t s'
      obtain ⟨t₁, t₂, s₁, rfl, e₁, e₂⟩ : ∃ t₁ t₂ s₁, t = t₁ ++ t₂ ∧ Exec isa c s t₁ s₁ ∧
          Exec isa (seqs (d :: rest ++ b)) s₁ t₂ s' := by
        cases e with
        | seq e₁ e₂ => exact ⟨_, _, _, rfl, e₁, e₂⟩
      have e₂' := ih (by simp) e₂
      obtain ⟨u₁, u₂, s₂, rfl, f₁, f₂⟩ : ∃ u₁ u₂ s₂, t₂ = u₁ ++ u₂ ∧ Exec isa (seqs (d :: rest)) s₁ u₁ s₂ ∧
          Exec isa (seqs b) s₂ u₂ s' := by
        cases e₂' with
        | seq f₁ f₂ => exact ⟨_, _, _, rfl, f₁, f₂⟩
      rw [← List.append_assoc]
      exact .seq (.seq e₁ f₁) f₂

theorem RelCT.seqs_app {P Q : State → State → Prop} {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ [])
    (h : RelCT isa P (.seq (seqs a) (seqs b)) Q) : RelCT isa P (seqs (a ++ b)) Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (exec_seqs_app ha hb e₁) (exec_seqs_app ha hb e₂)

/-- A piece whose claim holds for public data `g a`, then the rest, from
what correctness gives after the piece. -/
theorem ct_step {α β : Type} {Φ Ψ : α → State → Prop} {P : β → State → Prop} {c rest : Prog isa}
    (g : α → β) (hP : ∀ a s, Φ a s → P (g a) s) (hw : ∀ a s, Φ a s → WP isa c s (Ψ a))
    (hc : RelCT isa (Two P) c fun _ _ => True) (hr : RelCT isa (Two Ψ) rest fun _ _ => True) :
    RelCT isa (Two Φ) (.seq c rest) fun _ _ => True :=
  RelCT.seq (two_post (two_map g hP hc) hw) hr

/-- A piece checked by the taint analysis from the registers `rs`, then the rest. -/
theorem ct_taint {α : Type} {Φ Ψ : α → State → Prop} {c rest : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) (hr : RelCT isa (Two Ψ) rest fun _ _ => True) :
    RelCT isa (Two Φ) (.seq c rest) fun _ _ => True :=
  RelCT.seq (two_piece rs hpin h hw) hr

/-- A list of pieces whose claim holds for public data `g a`, then the rest. -/
theorem ct_steps {α β : Type} {Φ Ψ : α → State → Prop} {P : β → State → Prop} {c rest : List (Prog isa)}
    (hc0 : c ≠ []) (hr0 : rest ≠ []) (g : α → β) (hP : ∀ a s, Φ a s → P (g a) s)
    (hw : ∀ a s, Φ a s → WP isa (seqs c) s (Ψ a))
    (hc : RelCT isa (Two P) (seqs c) fun _ _ => True) (hr : RelCT isa (Two Ψ) (seqs rest) fun _ _ => True) :
    RelCT isa (Two Φ) (seqs (c ++ rest)) fun _ _ => True :=
  RelCT.seqs_app hc0 hr0 (ct_step g hP hw hc hr)

/-- The last piece. -/
theorem ct_last {α β : Type} {Φ : α → State → Prop} {P : β → State → Prop} {c : Prog isa}
    (g : α → β) (hP : ∀ a s, Φ a s → P (g a) s) (hc : RelCT isa (Two P) c fun _ _ => True) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  two_map g hP hc

/-! ## `subModArr` -/

/-- `subModArr`'s blocks and loops. -/
def smBlk1 (a b : Nat) : List Instr :=
  [.mov .r8 (.mem (hdr (sArr a))), .mov .r10 (.mem (hdr (sArr b))), .mov .rsi (.mem (hdr (sArr Public.aAcc))),
    .mov .r12 (.mem (hdr sW)), .mov32 .rbp (.imm 0)]

def smLoop1 : Prog isa :=
  wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .r8 .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)),
    .store (ix .rsi .r14) .rax, cfToRbp]

def smBlk3 (o : Nat) : List Instr :=
  [.mov .r15 (.reg .rbp), .mov32 .rbp (.imm 0), .mov .r10 (.mem (hdr (sArr Public.aN))),
    .mov .r8 (.mem (hdr (sArr Public.aAcc))), .mov .rbx (.mem (hdr (sArr o)))]

def smLoop2 : Prog isa :=
  wordLoop 0 [.mov .rax (.mem (ix .r10 .r14)), .alu .and .rax (.reg .r15), cfFromRbp,
    .alu .adc .rax (.mem (ix .r8 .r14)), .store (ix .rbx .r14) .rax, cfToRbp]

theorem subModArr_eq (o a b : Nat) :
    seqs (subModArr o a b) = .seq (.block (smBlk1 a b)) (.seq smLoop1 (.seq (.block (smBlk3 o)) smLoop2)) := rfl

/-- Before `subModArr`'s second loop: its bases and `w`. -/
def Sm3 (o : Nat) (L : Ws) (s : State) : Prop :=
  s.gpr .r10 = off L.B (slot L.w Public.aN) ∧ s.gpr .r8 = off L.B (slot L.w Public.aAcc) ∧
    s.gpr .rbx = off L.B (slot L.w o) ∧ s.gpr .r12 = BitVec.ofNat 64 L.w

/-- After `subModArr`'s first loop: the base in `rdi`, and the second block
gives `Sm3`. -/
def Sm2 (o : Nat) (L : Ws) (s : State) : Prop :=
  s.gpr .rdi = L.B ∧ WP isa (.block (smBlk3 o)) s (Sm3 o L)

/-- Before `subModArr`'s first loop: its bases and `w`, and the loop gives `Sm2`. -/
def Sm1 (o a b : Nat) (L : Ws) (s : State) : Prop :=
  s.gpr .r8 = off L.B (slot L.w a) ∧ s.gpr .r10 = off L.B (slot L.w b) ∧
    s.gpr .rsi = off L.B (slot L.w Public.aAcc) ∧ s.gpr .r12 = BitVec.ofNat 64 L.w ∧ WP isa smLoop1 s (Sm2 o L)

/-- `subModArr`'s hypotheses for its timing: the workspace and its size. -/
def SmPre (L : Ws) (s : State) : Prop := GoodW L s ∧ 2 ≤ L.w ∧ L.w < 2 ^ 31

/-- `subModArr`'s first block and loop, as `subModArr_ok` runs them. -/
theorem subModArr_wp {L : Ws} {s : State} (h : SmPre L s) {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (d3 : a ≠ Public.aAcc) (d4 : b ≠ Public.aAcc) :
    WP isa (.block (smBlk1 a b)) s (Sm1 o a b L) := by
  obtain ⟨⟨minv, hg, hZ⟩, hw, hw'⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot L.w j + 8 * (L.w + 2) ≤ L.Z := fun j hj => (slot_le hj).trans hZ
  have sp : ∀ {j k}, j ≠ k → slot L.w j + 8 * (L.w + 2) ≤ slot L.w k ∨ slot L.w k + 8 * (L.w + 2) ≤ slot L.w j :=
    fun h => slot_sep h
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off L.B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot L.w 8 hi; omega)
  have hacc : Public.aAcc < 8 := by decide
  have hmo : Public.aN < 8 := by decide
  refine WP.mono (WP.keep [.r8, .r10, .rsi, .r12, .rbp] (Q := fun t =>
      t.gpr .r8 = off L.B (slot L.w a) ∧ t.gpr .r10 = off L.B (slot L.w b) ∧
      t.gpr .rsi = off L.B (slot L.w Public.aAcc) ∧ t.gpr .r12 = BitVec.ofNat 64 L.w ∧ t.gpr .rbp = mask false ∧
      t.mem = s.mem)
    (by xrun [smBlk1, State.ea, hdr, hg.rdi, hdrOff, hl (sArr a) (by unfold sArr; omega),
      hl (sArr b) (by unfold sArr; omega), hl (sArr Public.aAcc) (by decide), hl sW (by decide),
      hg.hdr.harr a ha, hg.hdr.harr b hb, hg.hdr.harr Public.aAcc hacc, hg.hdr.hw]) rfl)
    fun s₁ ⟨⟨h8, h10, hsi, h12, hbp, hm₁⟩, k₁⟩ => ⟨h8, h10, hsi, h12, ?_⟩
  have hs₁ := hs.congr k₁.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → Keep [.r14] s₁ t → t.cf = s₁.cf →
      SubInv s₁ L.B L.Z (slot L.w a) (slot L.w b) (slot L.w Public.aAcc) 0 t := fun t h14 hm k _ =>
    ⟨hs₁.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp, by rw [hm]; rfl⟩⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := L.w) (by omega) hw'
    (SubInv s₁ L.B L.Z (slot L.w a) (slot L.w b) (slot L.w Public.aAcc)) h0
    (fun j _ hj t hI => subStep_ok h8 h10 hsi h12 (by omega) (by have := sl a ha; omega)
      (by have := sl b hb; omega) (by have := sl _ hacc; omega) (by have := sp d3; omega)
      (by have := sp d4; omega) hj hI)) fun s₂ hI => ?_
  have k12 := k₁.trans hI.keep
  have s₂di : s₂.gpr .rdi = L.B := (k12.gpr (by decide)).trans hg.rdi
  have hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off L.B (8 * i)) 8 := fun i hi =>
    hI.scr.ld (by have := hdr_lt_slot L.w 8 hi; omega)
  have fh : ∀ i < 32, word s₂.mem L.B (8 * i) = word s.mem L.B (8 * i) := fun i hi => by
    rw [hI.out.word (Or.inl (by have := hdr_lt_slot L.w Public.aAcc hi; omega)) (by
      have := hdr_lt_slot L.w 8 hi; omega), hm₁]
  have h12₂ : s₂.gpr .r12 = BitVec.ofNat 64 L.w := (hI.keep.gpr (by decide)).trans h12
  refine ⟨s₂di, WP.mono (WP.keep [.r15, .rbp, .r10, .r8, .rbx] (Q := fun t =>
      t.gpr .r10 = off L.B (slot L.w Public.aN) ∧ t.gpr .r8 = off L.B (slot L.w Public.aAcc) ∧
      t.gpr .rbx = off L.B (slot L.w o))
    (by xrun [smBlk3, State.ea, hdr, s₂di, hdrOff, hl₂ (sArr Public.aN) (by decide),
      hl₂ (sArr Public.aAcc) (by decide), hl₂ (sArr o) (by unfold sArr; omega),
      (fh _ (by decide)).trans (hg.hdr.harr Public.aN hmo), (fh _ (by decide)).trans (hg.hdr.harr Public.aAcc hacc),
      (fh _ (by unfold sArr; omega)).trans (hg.hdr.harr o ho)]) rfl)
    fun t ⟨⟨h10, h8, hbx⟩, k⟩ => ⟨h10, h8, hbx, (k.gpr (by decide)).trans h12₂⟩⟩

/-- `subModArr aT aY aXc`, `p`'s difference, is constant time. -/
theorem subModArr_ct : RelCT isa (Two SmPre) (seqs (subModArr aT Public.aY aXc)) fun _ _ => True := by
  rw [subModArr_eq]
  refine ct_taint [.rdi] (fun L s₁ s₂ ⟨⟨_, h₁, _⟩, _⟩ ⟨⟨_, h₂, _⟩, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rdi, h₂.rdi]) (by taint_decide)
    (fun L s h => subModArr_wp (o := aT) h (by decide) (by decide) (by decide) (by decide) (by decide)) ?_
  refine ct_taint [.r8, .r10, .rsi, .r12] (fun L s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.2.2.2.1, h₂.2.2.2.1]) (by taint_decide) (fun L s h => h.2.2.2.2) ?_
  refine ct_taint [.rdi] (fun L s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1, h₂.1]) (by taint_decide) (fun L s h => h.2) ?_
  exact two_taint [.r10, .r8, .rbx, .r12] (fun L s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide)

end VG.Proof.Bignum.X86_64
