module

public import VerifiedGarbage.Proof.Rsa.Arm.KdMul
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Rsa.Arm.KdDiv

/-! # The key checks' division on ARMv7 (`KeyDiv.divW`) is constant time

The pieces between the loads of the window's offset (72) are checked by the
taint analysis (the instances' `DivTaint`). Between them, each run carries
`Ws`, `w` (16), the offset, and the rest of the step's correctness; the
registers a piece needs public are the same in both runs by the facts of the
piece before it. The steps' count is the same in both (`loop_ok`).
-/

@[expose] public section

/-! ## The key checks' low product on ARMv7 (`KeyDiv.mulLo`) is constant time

Its pieces between the loads of the row's offset (72) are checked by the taint
analysis (the instances' `MulTaint`), from registers that correctness gives
both runs alike; the rows' count is the same in both (`mulRow_ok`).
-/

namespace VG.Proof.Rsa.Arm.KeyDiv

open VG VG.Arm VG.Impl.Rsa.Arm.KeyDiv VG.Proof.Rsa.Arm.Keys VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd)
open VG.Impl.Rsa.Arm.Keys (ptr copy)

theorem wp_and {c : Prog isa} {s : State} {P Q : State → Prop} (h₁ : WP isa c s P) (h₂ : WP isa c s Q) :
    WP isa c s fun t => P t ∧ Q t := by
  obtain ⟨t, s', e, p⟩ := h₁
  obtain ⟨t', s'', e', q⟩ := h₂
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact ⟨t, s', e, p, q⟩

/-- A piece the taint analysis checks with `rs` public: each run by its own correctness. -/
theorem piece {P₁ P₂ Q₁ Q₂ : State → Prop} {c : Prog isa} (rs : List Reg)
    (hc : ∃ hc, (VG.Taint.check taint (Taint.ofRegs rs) c hc).isSome = true)
    (regs : ∀ s t, P₁ s → P₂ t → ∀ r ∈ rs, s.gpr r = t.gpr r)
    (h₁ : ∀ s, P₁ s → WP isa c s Q₁) (h₂ : ∀ s, P₂ s → WP isa c s Q₂) :
    RelCT isa (fun s t => P₁ s ∧ P₂ t) c fun s t => Q₁ s ∧ Q₂ t := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s t h => Taint.agree_ofRegs (regs s t h.1 h.2)) hc).wp
    (F₁ := Q₁) (F₂ := Q₂) fun s t h => ⟨h₁ s h.1, h₂ t h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- `r7`–`r9` of two states of the same working space. -/
theorem ws_regs' {s t : State} {B : BitVec 32} {Z w N : Nat} (h₁ : Ws s B Z w N) (h₂ : Ws t B Z w N) :
    ∀ r ∈ [Reg.r7, .r8, .r9], s.gpr r = t.gpr r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · rw [h₁.r7, h₂.r7]
  · rw [h₁.r8, h₂.r8]
  · rw [h₁.r9, h₂.r9]

/-- A row's first block: `[o]`'s address and the row's offset. -/
theorem mrA_ok {s0 v : State} {B : BitVec 32} {Z w N o x y Y i : Nat} (I : MulInv s0 v B Z w N o x y Y i)
    (ho : o < N) (hN : N ≤ 256) :
    WP isa (.block (ptr .r0 o ++ ([.ldr .r2 .r8 sJ] : List Instr))) v fun u => Ws u B Z w N ∧
      u.gpr .r0 = B + BitVec.ofNat 32 (arr w o) ∧ u.gpr .r2 = BitVec.ofNat 32 (4 * i) := by
  refine ptr_ok I.ws (r := .r0) (by decide) (j := o) (by omega) fun u1 p1 r1 m1 h1 => ?_
  refine wp_ldrSlot h1 (d := sJ) (by decide) fun u2 U2 => WP.block_nil ⟨h1.of_upd U2 (by decide) (by decide)
    (by decide), by rw [U2.other _ (by decide), p1], ?_⟩
  rw [U2.gpr, m1, ← I.J]; exact (ofNat_toNat32 _).symm

/-- What `mulLo o x y` needs of each run. -/
def MulPre (B : BitVec 32) (Z w N x : Nat) (s : State) : Prop :=
  Ws s B Z w N ∧ slot s.mem B 16 = w ∧ num s.mem B w x < 2 ^ (32 * (w / 2)) ∧ num s.mem B w 0 = 0

/-- The taint analysis' facts for `mulLo o x y`. -/
structure MulTaint (o x y : Nat) : Prop where
  copy : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) (copy o 0) hc).isSome = true
  init : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9])
    (.block [.mov .r0 (.imm 0), .str .r0 .r8 sJ]) hc).isSome = true
  rowA : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9])
    (.block (ptr .r0 o ++ [.ldr .r2 .r8 sJ])) hc).isSome = true
  rowB : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r0, .r2, .r7, .r8, .r9])
    (.seq (.block ([.dp .add .r0 .r0 (.reg .r2)] ++ ptr .r12 y ++
      [.mov .r3 (.shifted .r2 .lsr 2), .dp .sub .lr .r9 (.reg .r3)] ++ ptr .r1 x ++
      [.dp .add .r1 .r1 (.reg .r2), .ldr .r1 .r1 0, .mov .r11 (.imm 0)]))
    (.seq VG.Impl.Bignum.Arm.row (.block (ctx ++ [.ldr .r0 .r8 sJ, .dp .add .r0 .r0 (.imm 4), .str .r0 .r8 sJ,
      .mov .r1 (.shifted .r9 .lsl 1), .cmp .r0 (.reg .r1)])))) hc).isSome = true

/-- `mulLo o x y` is constant time. -/
theorem mulLo_ct {B : BitVec 32} {Z w N o x y : Nat} (T : MulTaint o x y) (ho : o < N) (hx : x < N) (hy : y < N)
    (hN : N ≤ 256) (hox : o ≠ x) (hoy : o ≠ y) (ho0 : o ≠ 0) (hw : w % 2 = 0) (hw2 : 2 ≤ w) :
    RelCT isa (fun s t => MulPre B Z w N x s ∧ MulPre B Z w N x t) (mulLo o x y) fun _ _ => True := by
  refine (RelCT.exists_ (P := fun (p : State × State) s t => (s = p.1 ∧ MulPre B Z w N x p.1) ∧
    (t = p.2 ∧ MulPre B Z w N x p.2)) fun p => ?_).mono (fun s t h => ⟨(s, t), ⟨rfl, h.1⟩, rfl, h.2⟩)
    fun _ _ h => h
  obtain ⟨σ₁, σ₂⟩ := p
  rw [mulLo]
  simp only [VG.Impl.Rsa.Arm.Keys.seqs]
  let Q (σ : State) (v : State) := MulInv σ v B Z w N o x y (num σ.mem B w y) 0
  refine RelCT.seq (piece (Q₁ := fun v1 => Ws v1 B Z w N ∧ WP isa (.block [.mov .r0 (.imm 0), .str .r0 .r8 sJ]) v1
      (Q σ₁)) (Q₂ := fun v1 => Ws v1 B Z w N ∧ WP isa (.block [.mov .r0 (.imm 0), .str .r0 .r8 sJ]) v1 (Q σ₂))
    [.r7, .r8, .r9] T.copy (fun s t h₁ h₂ => by rw [h₁.1, h₂.1]; exact ws_regs' h₁.2.1 h₂.2.1)
    (fun s h => by
      obtain ⟨rfl, W, c16, -, z0⟩ := h; exact mulInit_ok x W ho hy hN hoy ho0 c16 hw2 z0)
    (fun s h => by
      obtain ⟨rfl, W, c16, -, z0⟩ := h; exact mulInit_ok x W ho hy hN hoy ho0 c16 hw2 z0)) ?_
  refine RelCT.seq (piece (Q₁ := Q σ₁) (Q₂ := Q σ₂) [.r7, .r8, .r9] T.init
    (fun s t h₁ h₂ => ws_regs' h₁.1 h₂.1) (fun s h => h.2) (fun s h => h.2)) ?_
  -- The rows.
  let I (n : Nat) (s t : State) : Prop := ∃ i, n = w / 2 - i ∧ i < w / 2 ∧
    MulInv σ₁ s B Z w N o x y (num σ₁.mem B w y) i ∧ MulInv σ₂ t B Z w N o x y (num σ₂.mem B w y) i
  refine (RelCT.loop (Q := fun _ _ => True) I (fun n => ?_) (w / 2)).mono
    (fun s t h => ⟨0, by omega, by omega, h.1, h.2⟩) fun _ _ h => h
  refine (RelCT.exists_ (P := fun i s t => n = w / 2 - i ∧ i < w / 2 ∧
    MulInv σ₁ s B Z w N o x y (num σ₁.mem B w y) i ∧ MulInv σ₂ t B Z w N o x y (num σ₂.mem B w y) i)
    fun i => ?_).mono (fun s t h => h) fun _ _ h => h
  by_cases hni : n = w / 2 - i ∧ i < w / 2
  swap
  · exact RelCT.of_false fun s t h => hni ⟨h.1, h.2.1⟩
  obtain ⟨hn, hi⟩ := hni
  let Post (σ : State) (v : State) := MulInv σ v B Z w N o x y (num σ.mem B w y) (i + 1) ∧
    v.z = decide (4 * (i + 1) = 2 * w)
  let RowB := (.seq (.block ([.dp .add .r0 .r0 (.reg .r2)] ++ ptr .r12 y ++
      [.mov .r3 (.shifted .r2 .lsr 2), .dp .sub .lr .r9 (.reg .r3)] ++ ptr .r1 x ++
      [.dp .add .r1 .r1 (.reg .r2), .ldr .r1 .r1 0, .mov .r11 (.imm 0)]))
    (.seq VG.Impl.Bignum.Arm.row (.block (ctx ++ [.ldr .r0 .r8 sJ, .dp .add .r0 .r0 (.imm 4), .str .r0 .r8 sJ,
      .mov .r1 (.shifted .r9 .lsl 1), .cmp .r0 (.reg .r1)]))) : Prog isa)
  let QA (σ : State) (u : State) := (Ws u B Z w N ∧ u.gpr .r0 = B + BitVec.ofNat 32 (arr w o) ∧
    u.gpr .r2 = BitVec.ofNat 32 (4 * i)) ∧ WP isa RowB u (Post σ)
  have fA : ∀ σ s, (n = w / 2 - i ∧ i < w / 2 ∧ MulInv σ s B Z w N o x y (num σ.mem B w y) i) →
      WP isa (.block (ptr .r0 o ++ [.ldr .r2 .r8 sJ])) s (QA σ) := fun σ s h => by
    have m := mulRow_ok h.2.2 ho hx hy hN hox hoy h.2.1
    rw [mulRow, WP.seq_iff] at m
    exact wp_and (mrA_ok h.2.2 ho hN) m
  have c := RelCT.seq (piece (P₁ := fun s => n = w / 2 - i ∧ i < w / 2 ∧
      MulInv σ₁ s B Z w N o x y (num σ₁.mem B w y) i)
    (P₂ := fun s => n = w / 2 - i ∧ i < w / 2 ∧ MulInv σ₂ s B Z w N o x y (num σ₂.mem B w y) i)
    [.r7, .r8, .r9] T.rowA (fun s t h₁ h₂ => ws_regs' h₁.2.2.ws h₂.2.2.ws) (fA σ₁) (fA σ₂))
    (piece (Q₁ := Post σ₁) (Q₂ := Post σ₂) [.r0, .r2, .r7, .r8, .r9] T.rowB (fun s t h₁ h₂ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl | rfl)
      · rw [h₁.1.2.1, h₂.1.2.1]
      · rw [h₁.1.2.2, h₂.1.2.2]
      · rw [h₁.1.1.r7, h₂.1.1.r7]
      · rw [h₁.1.1.r8, h₂.1.1.r8]
      · rw [h₁.1.1.r9, h₂.1.1.r9]) (fun s h => h.2) (fun s h => h.2))
  rw [mulRow]
  refine c.mono (fun s t h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.1, h.2.1, h.2.2.2⟩) fun s t ⟨⟨I₁, z₁⟩, ⟨I₂, z₂⟩⟩ => ?_
  refine ⟨?_, fun _ => trivial, fun e => ?_⟩
  · change some (!s.z) = some (!t.z); rw [z₁, z₂]
  · change some (!s.z) = some true at e
    rw [z₁] at e
    have hne : ¬4 * (i + 1) = 2 * w := fun h' => by simp [h'] at e
    exact ⟨w / 2 - (i + 1), by omega, i + 1, rfl, by omega, I₁, I₂⟩

end VG.Proof.Rsa.Arm.KeyDiv

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
    WP isa (.block (ptr .r0 a ++ ptr .r10 b ++ ([.ldr .r1 .r8 sJ] : List Instr))) v fun u => Ws u B Z w N ∧
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
    WP isa (.block (ptr .r0 a ++ ([.ldr .r1 .r8 sJ] : List Instr))) v fun u => Ws u B Z w N ∧
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

/-- What `divW a r m t nm u` needs of each run. -/
def DivPre (B : BitVec 32) (Z w N m : Nat) (s : State) : Prop :=
  Ws s B Z w N ∧ slot s.mem B 16 = w ∧ num s.mem B w m < 2 ^ (32 * (w / 2)) ∧
    0 < w32 s.mem (State.addr B) (arr w m + 4 * (w / 2 - 1)) ∧ num s.mem B w 0 = 0

/-- `divW a r m t nm u` is constant time. -/
theorem divW_ct {B : BitVec 32} {Z w N a r m t nm u : Nat} (T : DivTaint a r m t nm u) (ha : a < N)
    (hr : r < N) (hm : m < N) (ht : t < N) (hnm : nm < N) (hu : u < N) (hN : N ≤ 256) (hra : r ≠ a)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hmr : m ≠ r) (hmt : m ≠ t) (hmu : m ≠ u) (hnr : nm ≠ r)
    (htn : t ≠ nm) (hnu : nm ≠ u) (hnm' : nm ≠ m) (hr0 : r ≠ 0) (ht0 : t ≠ 0) (hu0 : u ≠ 0) (hn0 : nm ≠ 0)
    (hw6 : 6 ≤ w) :
    RelCT isa (fun s t' => DivPre B Z w N m s ∧ DivPre B Z w N m t') (divW a r m t nm u) fun _ _ => True := by
  have hdw : 3 ≤ w / 2 := by omega
  refine (RelCT.exists_ (P := fun (p : State × State) s t' => (s = p.1 ∧ DivPre B Z w N m p.1) ∧
    (t' = p.2 ∧ DivPre B Z w N m p.2)) fun p => ?_).mono (fun s t' h => ⟨(s, t'), ⟨rfl, h.1⟩, rfl, h.2⟩)
    fun _ _ h => h
  obtain ⟨σ₁, σ₂⟩ := p
  let Inv (σ : State) (n : Nat) (y : State) : Prop :=
    ∃ x0 z, DivSt x0 y B Z w N r m t nm u z (num σ.mem B w m) (num σ.mem B w a) n
  rw [divW]
  simp only [VG.Impl.Rsa.Arm.Keys.seqs]
  -- The preparation.
  have fP : ∀ σ s, (s = σ ∧ DivPre B Z w N m σ) → WP isa (prep a r m nm) s (Inv σ (w - w / 2)) := by
    rintro σ s ⟨rfl, W, c16, hMl, hT0, z0⟩
    exact WP.mono (prep_ok t u W ha hr hm hnm hN hra hmr hnm' hnr hr0 hn0 hw6 c16 rfl hMl hT0 z0)
      fun x0 ⟨⟨z, I0⟩, _, _⟩ => ⟨x0, z, I0⟩
  refine RelCT.seq (piece [.r7, .r8, .r9] T.prep (fun s t' h₁ h₂ => by rw [h₁.1, h₂.1]; exact ws_regs' h₁.2.1 h₂.2.1)
    (fP σ₁) (fP σ₂)) ?_
  -- The step from the invariant, with any of its correctness `G`.
  have stepI : ∀ {n : Nat} {x0₁ x0₂ : State} {z₁ z₂ : Nat} {G₁ G₂ : State → Prop},
      n + w / 2 ≤ w →
      RelCT isa (fun s t' => (DivSt x0₁ s B Z w N r m t nm u z₁ (num σ₁.mem B w m) (num σ₁.mem B w a) n ∧
          WP isa (step r m t nm u) s G₁) ∧
        (DivSt x0₂ t' B Z w N r m t nm u z₂ (num σ₂.mem B w m) (num σ₂.mem B w a) n ∧
          WP isa (step r m t nm u) t' G₂)) (step r m t nm u) fun s t' => G₁ s ∧ G₂ t' := by
    intro n x0₁ x0₂ z₁ z₂ G₁ G₂ hj
    exact (step_ct (a := a) (j := n) T hr hm ht hnm hu hN hru htu hmt htn hrt ht0 hdw hj).mono
      (fun s t' h => ⟨⟨⟨h.1.1.ws, h.1.1.pre.c16, h.1.1.J, h.1.2⟩, h.1.1.est hr hN hdw⟩,
        ⟨h.2.1.ws, h.2.1.pre.c16, h.2.1.J, h.2.2⟩, h.2.1.est hr hN hdw⟩) fun _ _ h => h
  -- The loop.
  let I (n : Nat) (s t' : State) : Prop := 1 ≤ n ∧ Inv σ₁ n s ∧ Inv σ₂ n t'
  have body : ∀ n, RelCT isa (I n) (.seq (step r m t nm u) (.block [.ldr .r0 .r8 sJ, .cmp .r0 (.imm 0)]))
      fun s t' => isa.eval .ne s = isa.eval .ne t' ∧ (isa.eval .ne s = some false → Inv σ₁ 0 s ∧ Inv σ₂ 0 t') ∧
        (isa.eval .ne s = some true → ∃ k < n, I k s t') := by
    intro n
    refine (RelCT.exists_ (P := fun (q : (State × Nat) × (State × Nat)) s t' => 1 ≤ n ∧
      DivSt q.1.1 s B Z w N r m t nm u q.1.2 (num σ₁.mem B w m) (num σ₁.mem B w a) n ∧
      DivSt q.2.1 t' B Z w N r m t nm u q.2.2 (num σ₂.mem B w m) (num σ₂.mem B w a) n) fun q => ?_).mono
      (fun s t' ⟨hn, ⟨x0, z, h₁⟩, ⟨x0', z', h₂⟩⟩ => ⟨((x0, z), (x0', z')), hn, h₁, h₂⟩) fun _ _ h => h
    obtain ⟨⟨x0₁, z₁⟩, ⟨x0₂, z₂⟩⟩ := q
    by_cases hn : 1 ≤ n ∧ n + w / 2 ≤ w
    swap
    · exact RelCT.of_false fun s t' h => hn ⟨h.1, h.2.1.hj⟩
    obtain ⟨hn, hj⟩ := hn
    let Pb (x0 : State) (z : Nat) (σ : State) (y : State) : Prop := isa.eval .ne y = some (!decide (n = 1)) ∧
      DivSt x0 y B Z w N r m t nm u z (num σ.mem B w m) (num σ.mem B w a) (n - 1)
    let G (x0 : State) (z : Nat) (σ : State) (y : State) : Prop := Ws y B Z w N ∧
      WP isa (.block [.ldr .r0 .r8 sJ, .cmp .r0 (.imm 0)]) y (Pb x0 z σ)
    have fG : ∀ {x0 z σ s}, DivSt x0 s B Z w N r m t nm u z (num σ.mem B w m) (num σ.mem B w a) n →
        WP isa (step r m t nm u) s (G x0 z σ) := fun {x0 z σ s} h => by
      have b := body_ok h hn hr hm ht hnm hu hN hrt hru htu hmr hmt hmu hnr htn hnu hr0 ht0 hu0 hdw
      rw [WP.seq_iff] at b
      exact WP.mono (wp_and (stepD_ok h hr hm ht hnm hu hN hrt hru htu hmr hmt hmu hnr htn hnu hr0 ht0 hu0 hdw) b)
        fun y ⟨⟨W, _⟩, c⟩ => ⟨W, c⟩
    have c := RelCT.seq ((stepI (G₁ := G x0₁ z₁ σ₁) (G₂ := G x0₂ z₂ σ₂) hj).mono
        (P' := fun s t' => 1 ≤ n ∧
          DivSt x0₁ s B Z w N r m t nm u z₁ (num σ₁.mem B w m) (num σ₁.mem B w a) n ∧
          DivSt x0₂ t' B Z w N r m t nm u z₂ (num σ₂.mem B w m) (num σ₂.mem B w a) n)
        (fun s t' h => ⟨⟨h.2.1, fG h.2.1⟩, h.2.2, fG h.2.2⟩) fun _ _ h => h)
      (piece (Q₁ := Pb x0₁ z₁ σ₁) (Q₂ := Pb x0₂ z₂ σ₂) [.r7, .r8, .r9] T.cond
        (fun s t' h₁ h₂ => ws_regs' h₁.1 h₂.1) (fun s h => h.2) (fun s h => h.2))
    refine c.mono (fun s t' h => h) fun s t' ⟨⟨c₁, I₁⟩, ⟨c₂, I₂⟩⟩ => ⟨by rw [c₁, c₂], fun e => ?_, fun e => ?_⟩
    · rw [c₁] at e
      have : n = 1 := by
        by_contra hne
        simp [hne] at e
      subst this
      exact ⟨⟨x0₁, z₁, I₁⟩, ⟨x0₂, z₂, I₂⟩⟩
    · rw [c₁] at e
      have : n ≠ 1 := fun hne => by simp [hne] at e
      exact ⟨n - 1, by omega, by omega, ⟨x0₁, z₁, I₁⟩, ⟨x0₂, z₂, I₂⟩⟩
  refine RelCT.seq (RelCT.loop (Q := fun s t' => Inv σ₁ 0 s ∧ Inv σ₂ 0 t') I body (w - w / 2) |>.mono
    (fun s t' h => ⟨by omega, h.1, h.2⟩) fun _ _ h => h) ?_
  -- The last step.
  refine (RelCT.exists_ (P := fun (q : (State × Nat) × (State × Nat)) s t' =>
      DivSt q.1.1 s B Z w N r m t nm u q.1.2 (num σ₁.mem B w m) (num σ₁.mem B w a) 0 ∧
      DivSt q.2.1 t' B Z w N r m t nm u q.2.2 (num σ₂.mem B w m) (num σ₂.mem B w a) 0) fun q => ?_).mono
    (fun s t' ⟨⟨x0, z, h₁⟩, ⟨x0', z', h₂⟩⟩ => ⟨((x0, z), (x0', z')), h₁, h₂⟩) fun _ _ h => h
  exact (stepI (G₁ := fun _ => True) (G₂ := fun _ => True) (by omega)).mono
    (fun s t' h => ⟨⟨h.1, WP.mono (stepD_ok h.1 hr hm ht hnm hu hN hrt hru htu hmr hmt hmu hnr htn hnu hr0 ht0 hu0
      hdw) fun _ _ => trivial⟩, h.2, WP.mono (stepD_ok h.2 hr hm ht hnm hu hN hrt hru htu hmr hmt hmu hnr htn hnu
      hr0 ht0 hu0 hdw) fun _ _ => trivial⟩) fun _ _ _ => trivial

end VG.Proof.Rsa.Arm.KeyDiv
