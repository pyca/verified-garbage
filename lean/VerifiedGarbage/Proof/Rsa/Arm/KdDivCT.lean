module

public import VerifiedGarbage.Proof.Rsa.Arm.KdDiv
public import VerifiedGarbage.Proof.Rsa.Arm.KdMulCT

/-! # The key checks' division on ARMv7 (`KeyDiv.divW`) is constant time

The pieces between the loads of the window's offset (72) are checked by the
taint analysis (the instances' `DivTaint`). Between them, each run carries
`Ws`, `w` (16), the offset, and the rest of the step's correctness; the
registers a piece needs public are the same in both runs by the facts of the
piece before it. The steps' count is the same in both (`loop_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyDiv

open VG VG.Arm VG.Impl.Rsa.Arm.KeyDiv VG.Proof.Rsa.Arm.Keys VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd wp_dp op2_reg dpVal)
open VG.Impl.Rsa.Arm.Keys (ptr sC)

/-- `estA r`: the address of the window's top words up to its offset, and the offset. -/
theorem estA_facts {v : State} {B : BitVec 32} {Z w N r j : Nat} (h : Ws v B Z w N) (hr : r < N) (hN : N ≤ 256)
    (hJ : slot v.mem B sJ = 4 * j) (hdw : 3 ≤ w / 2) :
    WP isa (.block (estA r)) v fun u => Ws u B Z w N ∧ u.gpr .r0 = BitVec.ofNat 32 (4 * j) ∧
      u.gpr .r10 = B + BitVec.ofNat 32 (arr w r + 4 * (w / 2 - 3)) := by
  have := h.wle
  have fr := h.arr_fit hr
  simp only [S] at fr
  rw [estA]
  refine topPtr_ok h (r := .r10) (t := .r0) (by decide) (by decide) (by decide) (j := r) (i := 3) (by omega)
    (by omega) (by decide) (by omega) fun u1 p1 r1 m1 h1 => ?_
  refine wp_ldrSlot h1 (d := sJ) (by decide) fun u2 U2 => WP.block_nil ⟨h1.of_upd U2 (by decide) (by decide)
    (by decide), ?_, by rw [U2.other _ (by decide), p1]⟩
  rw [U2.gpr, m1, ← hJ]; exact (ofNat_toNat32 _).symm

/-- `ptr .r0 a ++ ptr .r10 b ++ [ldr .r1 sJ]`: two addresses and the offset. -/
theorem ptr2J_facts {v : State} {B : BitVec 32} {Z w N a b j : Nat} (h : Ws v B Z w N) (ha : a < N) (hb : b < N)
    (hN : N ≤ 256) (hJ : slot v.mem B sJ = 4 * j) :
    WP isa (.block (ptr .r0 a ++ ptr .r10 b ++ [.ldr .r1 .r8 sJ])) v fun u => Ws u B Z w N ∧
      u.gpr .r0 = B + BitVec.ofNat 32 (arr w a) ∧ u.gpr .r10 = B + BitVec.ofNat 32 (arr w b) ∧
      u.gpr .r1 = BitVec.ofNat 32 (4 * j) := by
  rw [List.append_assoc]
  refine ptr_ok h (r := .r0) (by decide) (j := a) (by omega) fun u1 p1 r1 m1 h1 => ?_
  refine ptr_ok h1 (r := .r10) (by decide) (j := b) (by omega) fun u2 p2 r2 m2 h2 => ?_
  refine wp_ldrSlot h2 (d := sJ) (by decide) fun u3 U3 => WP.block_nil ⟨h2.of_upd U3 (by decide) (by decide)
    (by decide), by rw [U3.other _ (by decide), r2.gpr _ (by decide), p1], by rw [U3.other _ (by decide), p2], ?_⟩
  rw [U3.gpr, m2, m1, ← hJ]; exact (ofNat_toNat32 _).symm

/-- `ptr .r0 a ++ [ldr .r1 sJ]`: an address and the offset. -/
theorem ptrJ_facts {v : State} {B : BitVec 32} {Z w N a j : Nat} (h : Ws v B Z w N) (ha : a < N)
    (hN : N ≤ 256) (hJ : slot v.mem B sJ = 4 * j) :
    WP isa (.block (ptr .r0 a ++ [.ldr .r1 .r8 sJ])) v fun u => Ws u B Z w N ∧
      u.gpr .r0 = B + BitVec.ofNat 32 (arr w a) ∧ u.gpr .r1 = BitVec.ofNat 32 (4 * j) := by
  refine ptr_ok h (r := .r0) (by decide) (j := a) (by omega) fun u1 p1 r1 m1 h1 => ?_
  refine wp_ldrSlot h1 (d := sJ) (by decide) fun u2 U2 => WP.block_nil ⟨h1.of_upd U2 (by decide) (by decide)
    (by decide), by rw [U2.other _ (by decide), p1], ?_⟩
  rw [U2.gpr, m1, ← hJ]; exact (ofNat_toNat32 _).symm

/-- A code's own facts and those of what follows it, from the same run. -/
theorem wp_seq_and {c rest : Prog isa} {s : State} {P F : State → Prop} (h₁ : WP isa c s P)
    (h₂ : WP isa (.seq c rest) s F) : WP isa c s fun v => P v ∧ WP isa rest v F :=
  wp_and h₁ (WP.seq_iff.mp h₂)

/-- The step's last block. -/
abbrev tailB : List Instr := [.ldr .r0 .r8 sJ, .subs .r0 .r0 (.imm 4), .str .r0 .r8 sJ]

/-- The taint analysis' facts for `divW a r m t nm u`. -/
structure DivTaint (a r m t nm u : Nat) : Prop where
  prep : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) (prep a r m nm) hc).isSome = true
  estA : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) (.block (estA r)) hc).isSome = true
  estB : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r0, .r7, .r8, .r9, .r10]) (.block estB) hc).isSome = true
  clearT : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) (clearT t) hc).isSome = true
  prodT : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) (prodT m t) hc).isSome = true
  subTA : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9])
    (.block (ptr .r0 u ++ ptr .r10 r ++ [.ldr .r1 .r8 sJ])) hc).isSome = true
  subTB : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r0, .r1, .r7, .r8, .r9, .r10])
    (.seq (.block ([.dp .add .r10 .r10 (.reg .r1)] ++ ptr .r12 t ++
      [.mov .lr (.shifted .r9 .lsr 1), .dp .add .lr .lr (.imm 1), .mov .r11 (.imm 0)]))
    (.seq VG.Impl.Bignum.Arm.subRow (.block [.str .r11 .r8 sC]))) hc).isSome = true
  selT : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) (selT t nm) hc).isSome = true
  subBA : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9])
    (.block (ptr .r0 r ++ [.ldr .r1 .r8 sJ])) hc).isSome = true
  subBB : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r0, .r1, .r7, .r8, .r9])
    (.seq (.block ([.dp .add .r0 .r0 (.reg .r1)] ++ ptr .r10 u ++ ptr .r12 t ++
      [.mov .lr (.shifted .r9 .lsr 1), .dp .add .lr .lr (.imm 1), .mov .r11 (.imm 0)]))
      VG.Impl.Bignum.Arm.subRow) hc).isSome = true
  tail : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) (.block tailB) hc).isSome = true
  cond : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9])
    (.block [.ldr .r0 .r8 sJ, .cmp .r0 (.imm 0)]) hc).isSome = true

/-- What a run carries between the step's pieces: `Ws`, `w`, the offset, and what follows. -/
def Bnd (B : BitVec 32) (Z w N j : Nat) (rest : Prog isa) (F : State → Prop) (u : State) : Prop :=
  Ws u B Z w N ∧ slot u.mem B 16 = w ∧ slot u.mem B sJ = 4 * j ∧ WP isa rest u F

theorem bnd_regs {B : BitVec 32} {Z w N j : Nat} {r₁ r₂ : Prog isa} {F₁ F₂ : State → Prop} :
    ∀ s t, Bnd B Z w N j r₁ F₁ s → Bnd B Z w N j r₂ F₂ t → ∀ r ∈ [Reg.r7, .r8, .r9], s.gpr r = t.gpr r :=
  fun _ _ h₁ h₂ => ws_regs' h₁.1 h₂.1

/-- A step is constant time, from runs that each carry its correctness `F` and the frame of
its estimate. -/
theorem step_ct {B : BitVec 32} {Z w N a r m t nm u j : Nat} (T : DivTaint a r m t nm u) (hr : r < N)
    (hm : m < N) (ht : t < N) (hnm : nm < N) (hu : u < N) (hN : N ≤ 256) (hru : r ≠ u) (htu : t ≠ u)
    (hmt : m ≠ t) (htn : t ≠ nm) (hrt : r ≠ t) (ht0 : t ≠ 0) (hdw : 3 ≤ w / 2) (hj : j + w / 2 ≤ w)
    {F₁ F₂ : State → Prop} :
    RelCT isa (fun s t' => (Bnd B Z w N j (step r m t nm u) F₁ s ∧ WP isa (.block (estimate r)) s
        (fun v => Ws v B Z w N ∧ slot v.mem B 16 = w ∧ slot v.mem B sJ = 4 * j)) ∧
      (Bnd B Z w N j (step r m t nm u) F₂ t' ∧ WP isa (.block (estimate r)) t'
        (fun v => Ws v B Z w N ∧ slot v.mem B 16 = w ∧ slot v.mem B sJ = 4 * j)))
      (step r m t nm u) fun s t' => F₁ s ∧ F₂ t' := by
  let EP (v : State) : Prop := Ws v B Z w N ∧ slot v.mem B 16 = w ∧ slot v.mem B sJ = 4 * j
  rw [step]
  simp only [VG.Impl.Rsa.Arm.Keys.seqs]
  -- `estA`.
  have fA : ∀ (F : State → Prop) (s : State), (Bnd B Z w N j (.seq (.block (estA r)) (.seq (.block estB)
      (.seq (clearT t) (.seq (prodT m t) (.seq (subT r t u) (.seq (selT t nm) (.seq (subBack r t u)
        (.block tailB)))))))) F s ∧ WP isa (.block (estimate r)) s EP) →
      WP isa (.block (estA r)) s fun x => (Ws x B Z w N ∧ x.gpr .r0 = BitVec.ofNat 32 (4 * j) ∧
        x.gpr .r10 = B + BitVec.ofNat 32 (arr w r + 4 * (w / 2 - 3))) ∧
        WP isa (.block estB) x EP ∧ WP isa (.seq (.block estB) (.seq (clearT t) (.seq (prodT m t)
          (.seq (subT r t u) (.seq (selT t nm) (.seq (subBack r t u) (.block tailB))))))) x F := by
    intro F s ⟨⟨W, c16, J, wpS⟩, wpE⟩
    rw [show estimate r = estA r ++ estB by simp [estA, estB, estimate], WP.block_append_iff] at wpE
    exact wp_and (estA_facts W hr hN J hdw) (wp_and wpE (WP.seq_iff.mp wpS))
  have nxt : ∀ {c rest : Prog isa} {F : State → Prop} {x : State} (P : State → Prop),
      WP isa c x P → (∀ v, P v → EP v) → WP isa (.seq c rest) x F →
      WP isa c x (Bnd B Z w N j rest F) := fun P h hp hw =>
    WP.mono (wp_seq_and h hw) fun v ⟨p, q⟩ => ⟨(hp v p).1, (hp v p).2.1, (hp v p).2.2, q⟩
  have kslots : ∀ {x v : State} {js ds : List Nat}, Keep B w js ds x.mem v.mem →
      (∀ d ∈ ds, 16 + 4 ≤ d ∨ d + 4 ≤ 16) → (∀ d ∈ ds, sJ + 4 ≤ d ∨ d + 4 ≤ sJ) →
      slot x.mem B 16 = w → slot x.mem B sJ = 4 * j → slot v.mem B 16 = w ∧ slot v.mem B sJ = 4 * j :=
    fun K h1 h2 c16 cJ => ⟨by rw [K.slot (by decide) h1]; exact c16, by rw [K.slot (by decide) h2]; exact cJ⟩
  refine RelCT.seq (piece [.r7, .r8, .r9] T.estA (fun s t h₁ h₂ => ws_regs' h₁.1.1 h₂.1.1) (fA F₁) (fA F₂)) ?_
  -- `estB`.
  have fB : ∀ (F : State → Prop) (x : State), ((Ws x B Z w N ∧ x.gpr .r0 = BitVec.ofNat 32 (4 * j) ∧
        x.gpr .r10 = B + BitVec.ofNat 32 (arr w r + 4 * (w / 2 - 3))) ∧
        WP isa (.block estB) x EP ∧ WP isa (.seq (.block estB) (.seq (clearT t) (.seq (prodT m t)
          (.seq (subT r t u) (.seq (selT t nm) (.seq (subBack r t u) (.block tailB))))))) x F) →
      WP isa (.block estB) x (Bnd B Z w N j (.seq (clearT t) (.seq (prodT m t)
          (.seq (subT r t u) (.seq (selT t nm) (.seq (subBack r t u) (.block tailB)))))) F) :=
    fun F x h => nxt EP h.2.1 (fun _ h => h) h.2.2
  refine RelCT.seq (piece [.r0, .r7, .r8, .r9, .r10] T.estB (fun s t h₁ h₂ => by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl | rfl)
    · rw [h₁.1.2.1, h₂.1.2.1]
    · rw [h₁.1.1.r7, h₂.1.1.r7]
    · rw [h₁.1.1.r8, h₂.1.1.r8]
    · rw [h₁.1.1.r9, h₂.1.1.r9]
    · rw [h₁.1.2.2, h₂.1.2.2]) (fB F₁) (fB F₂)) ?_
  -- `clearT`.
  have fC : ∀ (F : State → Prop) (x : State), Bnd B Z w N j (.seq (clearT t) (.seq (prodT m t)
          (.seq (subT r t u) (.seq (selT t nm) (.seq (subBack r t u) (.block tailB)))))) F x →
      WP isa (clearT t) x (Bnd B Z w N j (.seq (prodT m t)
          (.seq (subT r t u) (.seq (selT t nm) (.seq (subBack r t u) (.block tailB))))) F) :=
    fun F x ⟨W, c16, cJ, h⟩ => nxt _ (clearT_ok W ht ht0 hN)
      (fun v ⟨W', K, _, _⟩ => ⟨W', kslots K (by simp) (by simp) c16 cJ⟩) h
  refine RelCT.seq (piece [.r7, .r8, .r9] T.clearT bnd_regs (fC F₁) (fC F₂)) ?_
  -- `prodT`.
  have fP : ∀ (F : State → Prop) (x : State), Bnd B Z w N j (.seq (prodT m t)
          (.seq (subT r t u) (.seq (selT t nm) (.seq (subBack r t u) (.block tailB))))) F x →
      WP isa (prodT m t) x (Bnd B Z w N j
          (.seq (subT r t u) (.seq (selT t nm) (.seq (subBack r t u) (.block tailB)))) F) :=
    fun F x ⟨W, c16, cJ, h⟩ => nxt _ (prodT_ok W hm ht hmt hN c16 (by omega))
      (fun v ⟨W', K, _, _⟩ => ⟨W', kslots K (by simp) (by simp) c16 cJ⟩) h
  refine RelCT.seq (piece [.r7, .r8, .r9] T.prodT bnd_regs (fP F₁) (fP F₂)) ?_
  -- `subT`.
  let SP (v : State) : Prop := EP v ∧ slot v.mem B sC ≤ 1
  let R5 : Prog isa := .seq (selT t nm) (.seq (subBack r t u) (.block tailB))
  let XT : Prog isa := .seq (.block ([.dp .add .r10 .r10 (.reg .r1)] ++ ptr .r12 t ++
      [.mov .lr (.shifted .r9 .lsr 1), .dp .add .lr .lr (.imm 1), .mov .r11 (.imm 0)]))
    (.seq VG.Impl.Bignum.Arm.subRow (.block [.str .r11 .r8 sC]))
  have fT : ∀ (F : State → Prop) (x : State), Bnd B Z w N j (.seq (subT r t u) R5) F x →
      WP isa (.block (ptr .r0 u ++ ptr .r10 r ++ [.ldr .r1 .r8 sJ])) x fun y =>
        (Ws y B Z w N ∧ y.gpr .r0 = B + BitVec.ofNat 32 (arr w u) ∧ y.gpr .r10 = B + BitVec.ofNat 32 (arr w r) ∧
          y.gpr .r1 = BitVec.ofNat 32 (4 * j)) ∧ WP isa XT y fun v => SP v ∧ WP isa R5 v F := by
    intro F x ⟨W, c16, cJ, h⟩
    have a := wp_seq_and (rest := R5) (subT_ok W hr ht hu hN hru htu cJ hj) h
    rw [subT, WP.seq_iff] at a
    exact wp_and (ptr2J_facts W hu hr hN cJ) (WP.mono a fun y hy => WP.mono hy
      fun v ⟨⟨W', K, _, hc, _⟩, q⟩ => ⟨⟨⟨W', kslots K (by simp; decide) (by simp; decide) c16 cJ⟩, hc⟩, q⟩)
  refine RelCT.seq (RelCT.seq (piece [.r7, .r8, .r9] T.subTA bnd_regs (fT F₁) (fT F₂))
    (piece (Q₁ := fun v => SP v ∧ WP isa R5 v F₁) (Q₂ := fun v => SP v ∧ WP isa R5 v F₂)
      [.r0, .r1, .r7, .r8, .r9, .r10] T.subTB (fun s t h₁ h₂ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl | rfl | rfl | rfl)
      · rw [h₁.1.2.1, h₂.1.2.1]
      · rw [h₁.1.2.2.2, h₂.1.2.2.2]
      · rw [h₁.1.1.r7, h₂.1.1.r7]
      · rw [h₁.1.1.r8, h₂.1.1.r8]
      · rw [h₁.1.1.r9, h₂.1.1.r9]
      · rw [h₁.1.2.2.1, h₂.1.2.2.1]) (fun s h => h.2) (fun s h => h.2))) ?_
  -- `selT`.
  let R6 : Prog isa := .seq (subBack r t u) (.block tailB)
  have fL : ∀ (F : State → Prop) (x : State), (SP x ∧ WP isa R5 x F) →
      WP isa (selT t nm) x (Bnd B Z w N j R6 F) :=
    fun F x ⟨⟨⟨W, c16, cJ⟩, hc⟩, h⟩ => nxt _ (selT_ok W ht hnm hN ht0 htn hc)
      (fun v ⟨W', K, _, _⟩ => ⟨W', kslots K (by simp) (by simp) c16 cJ⟩) h
  refine RelCT.seq (piece [.r7, .r8, .r9] T.selT (fun s t h₁ h₂ => ws_regs' h₁.1.1.1 h₂.1.1.1) (fL F₁) (fL F₂)) ?_
  -- `subBack`.
  let YB : Prog isa := .seq (.block ([.dp .add .r0 .r0 (.reg .r1)] ++ ptr .r10 u ++ ptr .r12 t ++
      [.mov .lr (.shifted .r9 .lsr 1), .dp .add .lr .lr (.imm 1), .mov .r11 (.imm 0)]))
      VG.Impl.Bignum.Arm.subRow
  have fS : ∀ (F : State → Prop) (x : State), Bnd B Z w N j R6 F x →
      WP isa (.block (ptr .r0 r ++ [.ldr .r1 .r8 sJ])) x fun y =>
        (Ws y B Z w N ∧ y.gpr .r0 = B + BitVec.ofNat 32 (arr w r) ∧ y.gpr .r1 = BitVec.ofNat 32 (4 * j)) ∧
          WP isa YB y (Bnd B Z w N j (.block tailB) F) := by
    intro F x ⟨W, c16, cJ, h⟩
    have r0 : 160 ≤ arr w r := Nat.le_add_right _ _
    have fr := W.fit64 hr
    simp only [S] at fr
    have a := wp_seq_and (rest := .block tailB) (subBack_ok W hr ht hu hN hru hrt cJ hj) h
    rw [subBack, WP.seq_iff] at a
    refine wp_and (ptrJ_facts W hr hN cJ) (WP.mono a fun y hy => WP.mono hy
      fun v ⟨⟨W', O, _, _⟩, q⟩ => ⟨W', ?_, ?_, q⟩)
    · simp only [slot]; rw [O.w32 (Or.inl (by omega)) (by omega)]; exact c16
    · simp only [slot]; rw [O.w32 (Or.inl (by simp only [sJ]; omega)) (by simp only [sJ]; omega)]; exact cJ
  refine RelCT.seq (RelCT.seq (piece [.r7, .r8, .r9] T.subBA bnd_regs (fS F₁) (fS F₂))
    (piece (Q₁ := Bnd B Z w N j (.block tailB) F₁) (Q₂ := Bnd B Z w N j (.block tailB) F₂)
      [.r0, .r1, .r7, .r8, .r9] T.subBB (fun s t h₁ h₂ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl | rfl | rfl)
      · rw [h₁.1.2.1, h₂.1.2.1]
      · rw [h₁.1.2.2, h₂.1.2.2]
      · rw [h₁.1.1.r7, h₂.1.1.r7]
      · rw [h₁.1.1.r8, h₂.1.1.r8]
      · rw [h₁.1.1.r9, h₂.1.1.r9]) (fun s h => h.2) (fun s h => h.2))) ?_
  -- The last block.
  exact piece [.r7, .r8, .r9] T.tail bnd_regs (fun s h => h.2.2.2) (fun s h => h.2.2.2)

end VG.Proof.Rsa.Arm.KeyDiv
