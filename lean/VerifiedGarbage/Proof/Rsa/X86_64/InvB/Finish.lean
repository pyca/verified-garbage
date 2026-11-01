module

public import VerifiedGarbage.Proof.Rsa.X86_64.InvB.FinPieces
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Divstep.Tc
import Mathlib.Tactic.Ring

/-!
# RSA's inverse by divsteps on x86-64: the end

From the batches' state (`BS`): `t := a mod m` (`fin1_ok`); `t := ±t 2^K mod m`
for the sign of `f` and `K = 15 n + 10` (`fin2_ok`); `|f|` into the cleared
`aA`, and the two results copied out (`fin3_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.InvB

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Inv
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- `Ws` again, from the start's, after changes to the private arrays alone. -/
theorem Ws.of_frm {s t : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    (hf : Frm B [(slot w 16, 80 * (w + 2))] s.mem t.mem) (hs : Scr t B Z) (hdi : t.gpr .rdi = B) :
    Ws t B Z w := by
  have hn := h.scr.nowrap
  have hZ := h.hZ
  have hh : ∀ i, i < 32 → word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    hf.word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]
      have := hdr_lt_slot w 16 hi; exact Or.inl this) (by have := hdr_lt_slot w 16 hi; omega)
  exact ⟨hs, hdi, (hh sW (by decide)).trans h.hw, (hh sStride (by decide)).trans h.hS,
    fun j hj => (hh (sArr j) (by unfold sArr; omega)).trans (h.harr j hj), h.hZ, h.w1, h.w2⟩

theorem subRep_ok {B : Addr} {X : Nat} : ∀ (k : Nat) (t : State), t.gpr .rdi = B + BitVec.ofNat 64 (k * X) →
    t.gpr .r9 = BitVec.ofNat 64 X →
    WP isa (.block (List.replicate k (.alu .sub .rdi (.reg .r9)))) t fun t' =>
      t'.gpr .rdi = B ∧ t'.mem = t.mem ∧ Keep [.rdi] t t'
  | 0, t, h, _ => WP.block_nil ⟨by rw [h, Nat.zero_mul]; exact BitVec.add_zero _, rfl, Keep.refl _ _⟩
  | k + 1, t, h, h9 => by
    rw [List.replicate_succ, show (Instr.alu .sub .rdi (.reg .r9) :: List.replicate k (.alu .sub .rdi (.reg .r9))) =
      [.alu .sub .rdi (.reg .r9)] ++ List.replicate k (.alu .sub .rdi (.reg .r9)) from rfl, WP.block_append_iff]
    refine WP.mono (WP.keep [.rdi] (Q := fun t₁ => t₁.gpr .rdi = B + BitVec.ofNat 64 (k * X) ∧ t₁.mem = t.mem)
      (by
        xrun [h, h9]
        rw [Nat.succ_mul, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_sub_cancel]) rfl)
      fun t₁ ⟨⟨h₁, m₁⟩, k₁⟩ => ?_
    refine WP.mono (subRep_ok k t₁ h₁ ((k₁.gpr (by decide)).trans h9)) fun t' ⟨a, b, c⟩ =>
      ⟨a, b.trans m₁, (k₁.trans c).mono (by decide)⟩

/-- `unwin`: `rdi` back to the base, `r13 := n`. -/
theorem unwin_ok {s : State} {B : Addr} {w n : Nat} (hdi : s.gpr .rdi = off B (slot w 16))
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))) (h15 : s.gpr .r15 = BitVec.ofNat 64 n) :
    WP isa (.block unwin) s fun t => t.gpr .rdi = B ∧ t.gpr .r13 = BitVec.ofNat 64 n ∧ t.mem = s.mem ∧
      Keep [.rdi, .r13] s t := by
  unfold unwin aWin
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rdi] (Q := fun t₁ => t₁.gpr .rdi = B + BitVec.ofNat 64 (16 * (8 * (w + 2))) ∧
    t₁.mem = s.mem) (by
      xrun [hdi, sx_ofNat (show hdrBytes < 2 ^ 31 by decide)]
      rw [off, slot_eq, show hdrBytes = 256 from rfl, Nat.add_comm, BitVec.ofNat_add, ← BitVec.add_assoc,
        BitVec.add_sub_cancel]) rfl) fun s₁ ⟨⟨d₁, m₁⟩, k₁⟩ => ?_
  refine WP.mono (subRep_ok 16 s₁ d₁ ((k₁.gpr (by decide)).trans h9)) fun s₂ ⟨d₂, m₂, k₂⟩ => ?_
  refine WP.mono (WP.keep [.r13] (Q := fun t => t.gpr .r13 = BitVec.ofNat 64 n ∧ t.mem = s₂.mem) (by
    xrun [((k₁.trans k₂).gpr (by decide)).trans h15]) rfl) fun t ⟨⟨r13, mt⟩, kt⟩ =>
    ⟨(kt.gpr (by decide)).trans d₂, r13, by rw [mt, m₂, m₁], ((k₁.trans k₂).trans kt).mono (by decide)⟩

/-- The words of `[j]` from `n + 1` on are zero. -/
def HZ (m : Mem) (B : Addr) (w n j : Nat) : Prop := ∀ i, n + 1 ≤ i → i < w + 2 → word m B (slot w j + 8 * i) = 0

theorem HZ.of_zero {m : Mem} {B : Addr} {w n j : Nat} (h : wv m B (slot w j) (w + 2) = 0) : HZ m B w n j :=
  fun i _ hi => wv_zero_word h i hi

theorem HZ.out {m m' : Mem} {B : Addr} {w n j : Nat} (h : HZ m B w n j) {o L : Nat} (ho : Outside B o L m m')
    (hd : ∀ i, n + 1 ≤ i → i < w + 2 → slot w j + 8 * i + 8 ≤ o ∨ o + L ≤ slot w j + 8 * i)
    (hn : slot w j + 8 * (w + 2) ≤ 2 ^ 64) : HZ m' B w n j :=
  fun i h1 h2 => by rw [ho.word (hd i h1 h2) (by omega)]; exact h i h1 h2

theorem HZ.wv_eq {m : Mem} {B : Addr} {w n j : Nat} (h : HZ m B w n j) (hn : n + 1 ≤ w + 2) :
    VG.Proof.Bignum.wv m B (slot w j) (w + 2) = VG.Proof.Bignum.wv m B (slot w j) (n + 1) := by
  suffices ∀ k, n + 1 + k ≤ w + 2 → VG.Proof.Bignum.wv m B (slot w j) (n + 1 + k) = VG.Proof.Bignum.wv m B (slot w j) (n + 1) by
    have := this (w + 2 - (n + 1)) (by omega)
    rwa [show n + 1 + (w + 2 - (n + 1)) = w + 2 by omega] at this
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [show n + 1 + (k + 1) = (n + 1 + k) + 1 by omega, VG.Proof.Bignum.wv, h _ (by omega) (by omega), ih (by omega)]
    simp

/-- The first block of the end: `r12 := n + 1`, `r15` the mask of `a < 0`, the bases of `t`, `m`, `a`. -/
theorem fin1Blk_ok {s : State} {B : Addr} {Z w n : Nat} (h : FS B Z w n s) {a : Int}
    (hc : (wv s.mem B (slot w aA) (n + 1) : Int) % 2 ^ (64 * (n + 1)) = a % 2 ^ (64 * (n + 1)))
    (hx1 : -(2 ^ (64 * n) * 2 ^ 63 : Int) ≤ a) (hx2 : a < 2 ^ (64 * n) * 2 ^ 63) :
    WP isa (.block (countN ++ base aA .r8 ++ ([.mov .rax (.mem (ix .r8 .r13)), .shift .shr .rax 63,
      .mov32 .r15 (.imm 0), .alu .sub .r15 (.reg .rax), .mov32 .rbp (.imm 0)] : List Instr) ++ base aT .rbx ++
      base aP .r10)) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 (n + 1) ∧ t.gpr .r8 = off B (slot w aA) ∧ t.gpr .r15 = mask (decide (a < 0)) ∧
      t.gpr .rbp = mask false ∧ t.gpr .rbx = off B (slot w aT) ∧ t.gpr .r10 = off B (slot w aP) ∧
      t.mem = s.mem ∧ Keep [.r12, .r8, .rax, .r15, .rbp, .rbx, .r10] s t := by
  have hn := h.ws.scr.nowrap
  have zA := h.sl (show aA < 26 by decide)
  have hnw := h.nw
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 (n + 1) ∧ t.mem = s.mem) (by
    unfold countN
    xrun [h.r13]
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]) rfl) fun s₁ ⟨⟨r12₁, m₁⟩, k₁⟩ => ?_
  have h₁ := h.of_mem m₁ k₁ (by decide) (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aA (r := .r8) (by decide) h₁.ws.rdi h₁.r9) fun s₂ ⟨h8, m₂, k₂⟩ => ?_
  have hs₂ := h.ws.scr.congr (k₁.trans k₂).2.2
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .r15, .rbp] (Q := fun t => t.gpr .r15 = mask (decide (a < 0)) ∧
      t.gpr .rbp = mask false ∧ t.mem = s.mem) (by
    xrun [State.ea, ix, addr0 h8 ((k₂.gpr (by decide)).trans h₁.r13),
      hs₂.ld (d := slot w aA + 8 * n) (by omega), m₂, m₁, isNeg_mask]
    exact congrArg mask (decide_eq_decide.mpr (top_bit hc hx1 hx2))) rfl) fun s₃ ⟨⟨r15₃, bp₃, m₃⟩, k₃⟩ => ?_
  refine WP.mono (base2_ok aT aP (r₁ := .rbx) (r₂ := .r10) (by decide) (by decide) (by decide)
    (((k₂.trans k₃).gpr (by decide)).trans h₁.ws.rdi) (((k₂.trans k₃).gpr (by decide)).trans h₁.r9) (by decide))
    fun t ⟨bx, b10, mt, kt⟩ => ⟨((k₂.trans k₃).trans kt |>.gpr (by decide)).trans r12₁,
      (k₃.trans kt |>.gpr (by decide)).trans h8, (kt.gpr (by decide)).trans r15₃, (kt.gpr (by decide)).trans bp₃,
      bx, b10, by rw [mt, m₃], (((k₁.trans k₂).trans k₃).trans kt).mono (by decide)⟩

/-- The end's first part. -/
def fin1L : List (Prog isa) := [.block unwin, zeroA aT,
  .block (countN ++ base aA .r8 ++ ([.mov .rax (.mem (ix .r8 .r13)), .shift .shr .rax 63, .mov32 .r15 (.imm 0),
    .alu .sub .r15 (.reg .rax), .mov32 .rbp (.imm 0)] : List Instr) ++ base aT .rbx ++ base aP .r10),
  wordLoop 0 addMBody] ++ csubT

/-- `t := a mod m`, from the batches' state. -/
theorem fin1_ok {s₀ s : State} {B : Addr} {Z w n p mi : Nat} {I : Divstep.IState} (h0 : Ws s₀ B Z w)
    (hZ : slot w 26 ≤ Z) (hF : Frm B [(slot w 16, 80 * (w + 2))] s₀.mem s.mem) (hb : BS B Z w n p mi I s)
    (hn1 : 1 ≤ n) (hnw : n ≤ w) (hP : wv s.mem B (slot w aP) (n + 1) = p) (hpn : p < 2 ^ (64 * n))
    (ha : -(p : Int) < I.a ∧ I.a < 2 * p) :
    WP isa (seqs fin1L) s fun t => FS B Z w n t ∧ t.gpr .r12 = BitVec.ofNat 64 (n + 1) ∧
      ∃ t₁ : Nat, wv t.mem B (slot w aT) (n + 1) = t₁ ∧ t₁ < p ∧ (t₁ : Int) ≡ I.a [ZMOD p] ∧
      HZ t.mem B w n aT ∧ wv t.mem B (slot w aP) (n + 1) = p ∧
      wv t.mem B (slot w aF) (n + 1) = wv s.mem B (slot w aF) (n + 1) ∧
      Frm B [(slot w 16, 80 * (w + 2))] s₀.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have hn := hb.scr.nowrap
  have eF : slot w aF = 256 + 19 * (8 * (w + 2)) := slot_eq w 19
  have eA : slot w aA = 256 + 21 * (8 * (w + 2)) := slot_eq w 21
  have eT : slot w aT = 256 + 23 * (8 * (w + 2)) := slot_eq w 23
  have eS : slot w aS = 256 + 24 * (8 * (w + 2)) := slot_eq w 24
  have eP : slot w aP = 256 + 25 * (8 * (w + 2)) := slot_eq w 25
  have e26 : slot w 26 = 256 + 26 * (8 * (w + 2)) := slot_eq w 26
  have hw := h0.w2
  have hM : 2 * p < 2 ^ (64 * (n + 1)) := by
    rw [show 64 * (n + 1) = 64 * n + 64 by omega, Nat.pow_add]
    have : 2 ≤ 2 ^ 64 := by decide
    have := Nat.mul_le_mul_left (2 ^ (64 * n)) this
    omega
  have hH : (2 : Int) * p ≤ 2 ^ (64 * n) * 2 ^ 63 := by
    have : 2 * 2 ^ (64 * n) ≤ 2 ^ (64 * n) * 2 ^ 63 := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by decide)
    have : 2 * p ≤ 2 ^ (64 * n) * 2 ^ 63 := by omega
    exact_mod_cast this
  have hHpos : (0 : Int) < 2 ^ (64 * n) * 2 ^ 63 := by
    have := Nat.mul_pos (Nat.two_pow_pos (64 * n)) (Nat.two_pow_pos 63); exact_mod_cast this
  rw [fin1L, seqs_append_iff _ _ (by simp) (by simp [csubT])]
  simp only [seqs]
  -- `rdi` back.
  refine WP.seq (WP.mono (unwin_ok hb.rdi hb.r9 hb.r15) fun s₁ ⟨di₁, r13₁, m₁, k₁⟩ => ?_)
  have h₁ : FS B Z w n s₁ := ⟨Ws.of_frm h0 (by rw [m₁]; exact hF) (hb.scr.congr k₁.2.2) di₁, hZ,
    (k₁.gpr (by decide)).trans hb.r9, r13₁, hn1, hnw⟩
  -- `t := 0`.
  refine WP.seq (WP.mono (zeroAI_ok h₁.ws hZ (j := aT) (by decide)) fun s₂ ⟨zT₂, o₂, r9₂, k₂⟩ => ?_)
  have h₂ : FS B Z w n s₂ := ⟨wsOut h₁.ws o₂ k₂ (by decide), hZ, r9₂, (k₂.gpr (by decide)).trans r13₁, hn1, hnw⟩
  have zT := h₁.sl (show aT < 26 by decide)
  have tA : wv s₂.mem B (slot w aA) (n + 1) = wv s.mem B (slot w aA) (n + 1) := by
    rw [o₂.wv (Or.inl (by omega)) (by omega), m₁]
  refine WP.seq (WP.mono (fin1Blk_ok h₂ (a := I.a) (by rw [tA]; exact hb.a) (by omega) (by omega))
    fun s₃ ⟨r12₃, r8₃, r15₃, bp₃, bx₃, r10₃, m₃, k₃⟩ => ?_)
  have h₃ := h₂.of_mem m₃ k₃ (by decide) (by decide) (by decide)
  refine WP.mono (addM_ok h₃.ws.scr bx₃ r10₃ r8₃ r15₃ r12₃ bp₃ (N := n + 1) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)) fun s₄ ⟨c₄, _, hv₄, o₄, k₄⟩ => ?_
  have h₄ := h₃.of_out o₄ k₄ (by decide) (by decide) (by decide)
  have P₃ : wv s₃.mem B (slot w aP) (n + 1) = p := by
    rw [m₃, o₂.wv (Or.inr (by omega)) (by omega), m₁, hP]
  have A₃ : wv s₃.mem B (slot w aA) (n + 1) = wv s.mem B (slot w aA) (n + 1) := by rw [m₃, tA]
  rw [P₃, A₃] at hv₄
  -- The value: `a + (p if a < 0)`.
  have hA := Divstep.tc_eq (H := 2 ^ (64 * n) * 2 ^ 63) (x := I.a) (W := (wv s.mem B (slot w aA) (n + 1) : Int))
    hHpos (by omega) (by omega) (Int.natCast_nonneg _)
    (by have := wv_lt s.mem B (slot w aA) (n + 1)
        have e2 : (2 : Int) * (2 ^ (64 * n) * 2 ^ 63) = 2 ^ (64 * (n + 1)) := by
          rw [show 64 * (n + 1) = 64 * n + 63 + 1 by omega, pow_succ, pow_add]; ring
        rw [e2]; exact_mod_cast this)
    (by have e2 : (2 : Int) * (2 ^ (64 * n) * 2 ^ 63) = 2 ^ (64 * (n + 1)) := by
          rw [show 64 * (n + 1) = 64 * n + 63 + 1 by omega, pow_succ, pow_add]; ring
        rw [e2]; exact hb.a)
  have e2 : (2 : Int) * (2 ^ (64 * n) * 2 ^ 63) = 2 ^ (64 * (n + 1)) := by
    rw [show 64 * (n + 1) = 64 * n + 63 + 1 by omega, pow_succ, pow_add]; ring
  rw [e2] at hA
  have hT4lt := wv_lt s₄.mem B (slot w aT) (n + 1)
  have hv₄' : (wv s₄.mem B (slot w aT) (n + 1) : Int) + 2 ^ (64 * (n + 1)) * c₄.toNat =
      (if decide (I.a < 0) = true then (p : Int) else 0) + wv s.mem B (slot w aA) (n + 1) := by
    have := congrArg (fun x : Nat => (x : Int)) hv₄
    push_cast at this
    rw [this]
  have hM' : (2 : Int) * p < 2 ^ (64 * (n + 1)) := by exact_mod_cast hM
  have hT4lt' : (wv s₄.mem B (slot w aT) (n + 1) : Int) < 2 ^ (64 * (n + 1)) := by exact_mod_cast hT4lt
  have hT4 : (wv s₄.mem B (slot w aT) (n + 1) : Int) = I.a + if I.a < 0 then (p : Int) else 0 := by
    by_cases hneg : I.a < 0
    · simp only [hneg, decide_true, ↓reduceIte] at hv₄' hA ⊢
      cases c₄ <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.cast_zero, Nat.cast_one] at hv₄' <;> omega
    · simp only [hneg, decide_false, ↓reduceIte, Bool.false_eq_true] at hv₄' hA ⊢
      cases c₄ <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.cast_zero, Nat.cast_one] at hv₄' <;> omega
  -- `t := t - m` if not below `m`.
  have P₄ : wv s₄.mem B (slot w aP) (n + 1) = p := by rw [o₄.wv (Or.inr (by omega)) (by omega), P₃]
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  refine WP.mono (csubT_ok h₄ ((k₄.gpr (by decide)).trans r12₃) (N := n + 1) (by omega) (by omega) rfl P₄)
    fun t ⟨vt, f₅, F₅, k₅⟩ => ⟨h₄.ws.congr (rs := [(slot w aT, 8 * (n + 1)), (slot w aS, 8 * (n + 1))]) f₅
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact Mut.ofSlot _ _ _) k₅ (by decide) |> fun ws => ⟨ws, hZ,
      (k₅.gpr (by decide)).trans h₄.r9, (k₅.gpr (by decide)).trans h₄.r13, hn1, hnw⟩,
      (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans r12₃), _, vt, ?_, ?_, ?_, ?_, ?_, ?_,
      (k14.trans k₅).mono (by decide)⟩
  · split <;> omega
  · have hp0 : (0 : Int) ≤ p := Int.natCast_nonneg _
    split
    · rename_i hlt
      rw [hT4]
      split
      · exact Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩
      · rw [Int.add_zero]
    · rename_i hge
      rw [Nat.cast_sub (by omega), hT4]
      split
      · exact Int.modEq_iff_dvd.mpr ⟨0, by ring⟩
      · rw [Int.add_zero]; exact Int.modEq_iff_dvd.mpr ⟨1, by ring⟩
  · -- The words above `n` of `t` stay zero.
    have z₂ := HZ.of_zero (n := n) zT₂
    have o₄' := o₄
    rw [m₃] at o₄'
    have z₄ := z₂.out (o := slot w aT) (L := 8 * (n + 1)) o₄'
      (fun i h1 _ => Or.inr (by omega)) (by omega)
    intro i h1 h2
    rw [f₅.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega) (by omega)]
    exact z₄ i h1 h2
  · rw [f₅.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega) (by omega), P₄]
  · rw [f₅.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega) (by omega), o₄.wv (Or.inl (by omega)) (by omega), m₃,
      o₂.wv (Or.inl (by omega)) (by omega), m₁]
  · rw [← m₁] at hF
    have o₄' := o₄
    rw [m₃] at o₄'
    exact ((hF.trans (frW o₂ (by decide) (by decide) (by omega))).trans
      (frW o₄' (by decide) (by decide) (by omega))).trans F₅

/-- `r11 := 15 n + 10`, the count of doublings. -/
theorem r11Set_ok {s : State} {n : Nat} (h13 : s.gpr .r13 = BitVec.ofNat 64 n) :
    WP isa (.block [.mov .r11 (.reg .r13), .shift .shl .r11 4, .alu .sub .r11 (.reg .r13), .alu .add .r11 (.imm 10)])
      s fun t => t.gpr .r11 = BitVec.ofNat 64 (15 * n + 10) ∧ t.mem = s.mem ∧ Keep [.r11] s t := by
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 (15 * n + 10) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩
  xrun [h13]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    show (BitVec.signExtend 64 (10 : BitVec 32)).toNat = 10 from rfl]
  omega

/-- The end's second part. -/
def fin2L : List (Prog isa) := [
  .block (([.mov32 .rbp (.imm 0)] : List Instr) ++ base aP .r8 ++ base aT .r10 ++ base aS .rsi), wordLoop 0 subBody,
  .block (nonNeg aF ++ base aT .r8 ++ base aS .rsi), wordLoop 0 selBody,
  .block [.mov .r11 (.reg .r13), .shift .shl .r11 4, .alu .sub .r11 (.reg .r13), .alu .add .r11 (.imm 10)],
  .loop dbl .ne] ++ csubT

theorem frm2_wv {m m' : Mem} {B : Addr} {w N j k : Nat} (h : Frm B [(slot w aT, 8 * N), (slot w aS, 8 * N)] m m')
    (hj : j ≠ aT) (hj' : j ≠ aS) (hN : N ≤ w + 2) (hk : k ≤ w + 2) (hn : slot w j + 8 * (w + 2) ≤ 2 ^ 64) :
    wv m' B (slot w j) k = wv m B (slot w j) k :=
  h.wv_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := slot_far (w := w) hj; dsimp only; omega
    · have := slot_far (w := w) hj'; dsimp only; omega) (by omega)

/-- `t := ±t 2^K mod m` for the sign of `f` and `K = 15 n + 10`, from `t < m`. -/
theorem fin2_ok {s : State} {B : Addr} {Z w n p t₁ : Nat} {f : Int} (h : FS B Z w n s)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 (n + 1)) (hT : wv s.mem B (slot w aT) (n + 1) = t₁) (ht₁ : t₁ < p)
    (hZT : HZ s.mem B w n aT) (hP : wv s.mem B (slot w aP) (n + 1) = p) (hpn : p < 2 ^ (64 * n))
    (hf : (wv s.mem B (slot w aF) (n + 1) : Int) % 2 ^ (64 * (n + 1)) = f % 2 ^ (64 * (n + 1)))
    (hf1 : -(p : Int) ≤ f) (hf2 : f ≤ p) :
    WP isa (seqs fin2L) s fun t => FS B Z w n t ∧ t.gpr .r12 = BitVec.ofNat 64 (n + 1) ∧
      ∃ x : Nat, wv t.mem B (slot w aT) (n + 1) = x ∧ x < p ∧
      (x : Int) ≡ (if 0 ≤ f then (t₁ : Int) else -t₁) * 2 ^ (15 * n + 10) [ZMOD p] ∧
      HZ t.mem B w n aT ∧ wv t.mem B (slot w aP) (n + 1) = p ∧
      wv t.mem B (slot w aF) (n + 1) = wv s.mem B (slot w aF) (n + 1) ∧
      Frm B [(slot w 16, 80 * (w + 2))] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have hn := h.ws.scr.nowrap
  have hnw := h.nw; have hn1 := h.n1
  have eF : slot w aF = 256 + 19 * (8 * (w + 2)) := slot_eq w 19
  have eT : slot w aT = 256 + 23 * (8 * (w + 2)) := slot_eq w 23
  have eS : slot w aS = 256 + 24 * (8 * (w + 2)) := slot_eq w 24
  have eP : slot w aP = 256 + 25 * (8 * (w + 2)) := slot_eq w 25
  have e26 : slot w 26 = 256 + 26 * (8 * (w + 2)) := slot_eq w 26
  have hZ := h.z
  have hw := h.ws.w2
  have hM : 2 * p < 2 ^ (64 * (n + 1)) := by
    rw [show 64 * (n + 1) = 64 * n + 64 by omega, Nat.pow_add]
    have : 2 ≤ 2 ^ 64 := by decide
    have := Nat.mul_le_mul_left (2 ^ (64 * n)) this
    omega
  have hH : (p : Int) < 2 ^ (64 * n) * 2 ^ 63 := by
    have : 2 ^ (64 * n) ≤ 2 ^ (64 * n) * 2 ^ 63 := Nat.le_mul_of_pos_right _ (by decide)
    have : p < 2 ^ (64 * n) * 2 ^ 63 := by omega
    exact_mod_cast this
  rw [fin2L, seqs_append_iff _ _ (by simp) (by simp [csubT])]
  rw [show ([.block (([.mov32 .rbp (.imm 0)] : List Instr) ++ base aP .r8 ++ base aT .r10 ++ base aS .rsi),
      wordLoop 0 subBody, .block (nonNeg aF ++ base aT .r8 ++ base aS .rsi), wordLoop 0 selBody,
      .block [.mov .r11 (.reg .r13), .shift .shl .r11 4, .alu .sub .r11 (.reg .r13), .alu .add .r11 (.imm 10)],
      .loop dbl .ne] : List (Prog isa)) =
      [.block (([.mov32 .rbp (.imm 0)] : List Instr) ++ base aP .r8 ++ base aT .r10 ++ base aS .rsi),
        wordLoop 0 subBody] ++ ([.block (nonNeg aF ++ base aT .r8 ++ base aS .rsi), wordLoop 0 selBody] ++
      [.block [.mov .r11 (.reg .r13), .shift .shl .r11 4, .alu .sub .r11 (.reg .r13), .alu .add .r11 (.imm 10)],
        .loop dbl .ne]) from rfl,
    seqs_append_iff _ _ (by simp) (by simp)]
  -- `s := m - t`.
  refine WP.mono (subN_ok h (a := aP) (b := aT) (c := aS) (by decide) (by decide) (by decide) (by decide)
    (by decide) h12 (N := n + 1) (by omega) (by omega)) fun s₁ ⟨cb, _, hv₁, _, _, o₁, k₁⟩ => ?_
  have h₁ := h.of_out o₁ k₁ (by decide) (by decide) (by decide)
  rw [seqs_append_iff _ _ (by simp) (by simp)]
  rw [hT, hP] at hv₁
  have hS1 := wv_lt s₁.mem B (slot w aS) (n + 1)
  have hS₁ : wv s₁.mem B (slot w aS) (n + 1) = p - t₁ := by
    cases cb <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hv₁ <;> omega
  have T₁ : wv s₁.mem B (slot w aT) (n + 1) = t₁ := by rw [o₁.wv (Or.inl (by omega)) (by omega), hT]
  have F₁ : wv s₁.mem B (slot w aF) (n + 1) = wv s.mem B (slot w aF) (n + 1) := by
    rw [o₁.wv (Or.inl (by omega)) (by omega)]
  -- `t := s` if `f < 0`.
  refine WP.mono (selN_ok h₁ (nonNeg_ok h₁ (j := aF) (by decide) (x := f) (by rw [F₁]; exact hf) (by omega)
    (by omega)) (a := aT) (c := aS) (by decide) (by decide) (by decide) ((k₁.gpr (by decide)).trans h12)
    (N := n + 1) (by omega) (by omega)) fun s₂ ⟨hv₂, o₂, k₂⟩ => ?_
  have h₂ := h₁.of_out o₂ k₂ (by decide) (by decide) (by decide)
  rw [T₁, hS₁] at hv₂
  have P₂ : wv s₂.mem B (slot w aP) (n + 1) = p := by
    rw [o₂.wv (Or.inr (by omega)) (by omega), o₁.wv (Or.inr (by omega)) (by omega), hP]
  -- `K` doublings.
  refine WP.seq (WP.mono (r11Set_ok h₂.r13) fun s₃ ⟨r11₃, m₃, k₃⟩ => ?_)
  have h₃ := h₂.of_mem m₃ k₃ (by decide) (by decide) (by decide)
  have k13 := (k₁.trans k₂).trans k₃
  refine WP.mono (dblLoop_ok h₃ ((k13.gpr (by decide)).trans h12) (t₀ := if decide (0 ≤ f) = true then t₁ else p - t₁)
    (by rw [m₃, hv₂]) (by rw [m₃, P₂]) (by split <;> omega) hpn r11₃ (by omega) (by omega))
    fun s₄ ⟨h₄, r12₄, le₄, c₄, f₄, F₄, k₄⟩ => ?_
  have P₄ : wv s₄.mem B (slot w aP) (n + 1) = p := by
    rw [frm2_wv f₄ (by decide) (by decide) (by omega) (by omega) (by have := h.sl (show aP < 26 by decide); omega),
      m₃, P₂]
  refine WP.mono (csubT_ok h₄ r12₄ (N := n + 1) (by omega) (by omega) rfl P₄) fun t ⟨vt, f₅, F₅, k₅⟩ =>
    ⟨⟨h₄.ws.congr f₅ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact Mut.ofSlot _ _ _) k₅ (by decide), hZ,
      (k₅.gpr (by decide)).trans h₄.r9, (k₅.gpr (by decide)).trans h₄.r13, hn1, hnw⟩,
      (k₅.gpr (by decide)).trans r12₄, _, vt, ?_, ?_, ?_, ?_, ?_, ?_, ((k13.trans k₄).trans k₅).mono (by decide)⟩
  · have := h.sl (show aT < 26 by decide)
    split <;> omega
  · have hp0 : (0 : Int) ≤ p := Int.natCast_nonneg _
    have c₄' : (wv s₄.mem B (slot w aT) (n + 1) : Int) ≡ (if 0 ≤ f then (t₁ : Int) else -t₁) * 2 ^ (15 * n + 10)
        [ZMOD p] := by
      refine c₄.trans (Int.ModEq.mul_right _ ?_)
      by_cases h0 : 0 ≤ f
      · simp only [h0, decide_true, ↓reduceIte]; exact Int.ModEq.refl _
      · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [Nat.cast_sub (by omega)]
        exact Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩
    split
    · exact c₄'
    · rw [Nat.cast_sub (by omega)]
      exact (Int.modEq_iff_dvd.mpr ⟨1, by ring⟩).trans c₄'
  · intro i h1 h2
    have := h.sl (show aT < 26 by decide)
    have z₂ := (hZT.out o₁ (fun i _ _ => Or.inl (by omega)) (by omega)).out o₂ (fun i h1 _ => Or.inr (by omega))
      (by omega)
    rw [f₅.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega) (by omega), f₄.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega) (by omega), m₃]
    exact z₂ i h1 h2
  · rw [frm2_wv f₅ (by decide) (by decide) (by omega) (by omega) (by have := h.sl (show aP < 26 by decide); omega), P₄]
  · have := h.sl (show aF < 26 by decide)
    rw [frm2_wv f₅ (by decide) (by decide) (by omega) (by omega) (by omega),
      frm2_wv f₄ (by decide) (by decide) (by omega) (by omega) (by omega), m₃,
      o₂.wv (Or.inl (by omega)) (by omega), F₁]
  · rw [m₃] at F₄
    exact (((frW o₁ (by decide) (by decide) (by omega)).trans (frW o₂ (by decide) (by decide) (by omega))).trans
      F₄).trans F₅

end VG.Proof.Rsa.X86_64.InvB
