module

public import VerifiedGarbage.Proof.Rsa.Arm.KdMul
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! # The key checks' low product on ARMv7 (`KeyDiv.mulLo`) is constant time

Its pieces between the loads of the row's offset (72) are checked by the taint
analysis (the instances' `MulTaint`), from registers that correctness gives
both runs alike; the rows' count is the same in both (`mulRow_ok`).
-/

@[expose] public section

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
    WP isa (.block (ptr .r0 o ++ [.ldr .r2 .r8 sJ])) v fun u => Ws u B Z w N ∧
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
