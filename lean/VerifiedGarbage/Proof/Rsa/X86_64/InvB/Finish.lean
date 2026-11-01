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

end VG.Proof.Rsa.X86_64.InvB
