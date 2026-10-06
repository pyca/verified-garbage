import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks

/-!
# A candidate on x86-64: Miller–Rabin's selection and comparisons

`selLoop_ok`: `[aXm] := bit ? [aB] : [aR1]` under the mask of the bit, in
`r15`; `eqMask_ok`: the mask of `[aY] = [j]`.
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

theorem sel_word (a b : BitVec 64) (c : Bool) : ((a ^^^ b) &&& mask c) ^^^ b = if c then a else b := by
  cases c
  · simp [mask_false]
  · rw [mask_true, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]; rfl

/-- After `j` words of the selection. -/
structure SelInv (s₀ : State) (B : Addr) (Z eA eB eD : Nat) (c : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rdx, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  done : ∀ i < j, word t.mem B (eD + 8 * i) = if c then word s₀.mem B (eA + 8 * i) else word s₀.mem B (eB + 8 * i)
  frame : Outside B eD (8 * j) s₀.mem t.mem

theorem selStep_ok {s₀ : State} {B : Addr} {Z w eA eB eD : Nat} {c : Bool}
    (h8 : s₀.gpr .r8 = off B eA) (hsi : s₀.gpr .rsi = off B eB) (hbx : s₀.gpr .rbx = off B eD)
    (h15 : s₀.gpr .r15 = mask c) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (hA : eA + 8 * w ≤ Z) (hB : eB + 8 * w ≤ Z) (hD : eD + 8 * w ≤ Z)
    (sA : eD + 8 * w ≤ eA ∨ eA + 8 * w ≤ eD) (sB : eD + 8 * w ≤ eB ∨ eB + 8 * w ≤ eD)
    {j : Nat} (hj : j < w) {t : State} (hI : SelInv s₀ B Z eA eB eD c j t) :
    WP isa (.block (([.mov .rax (.mem (ix .r8 .r14)), .mov .rdx (.mem (ix .rsi .r14)), .alu .xor .rax (.reg .rdx),
        .alu .and .rax (.reg .r15), .alu .xor .rax (.reg .rdx), .store (ix .rbx .r14) .rax] : List Instr) ++
        ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ SelInv s₀ B Z eA eB eD c (j + 1) t' := by
  have hn := hI.scr.nowrap
  have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans h8
  have tsi : t.gpr .rsi = off B eB := (hI.keep.gpr (by decide)).trans hsi
  have tbx : t.gpr .rbx = off B eD := (hI.keep.gpr (by decide)).trans hbx
  have t15 : t.gpr .r15 = mask c := (hI.keep.gpr (by decide)).trans h15
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have hvA : word t.mem B (eA + 8 * j) = word s₀.mem B (eA + 8 * j) :=
    hI.frame.word (by omega) (by omega)
  have hvB : word t.mem B (eB + 8 * j) = word s₀.mem B (eB + 8 * j) :=
    hI.frame.word (by omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t₁ => t₁.mem = t.mem.writeW (off B (eD + 8 * j))
      (if c then word s₀.mem B (eA + 8 * j) else word s₀.mem B (eB + 8 * j))) ?_ rfl)
    fun t₁ ⟨hm, k₁⟩ => ?_
  · xrun [State.ea, ix, addr0 t8 hI.r14, addr0 tsi hI.r14, addr0 tbx hI.r14,
      hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega), hI.scr.ld (show eB + 8 * j + 8 ≤ Z by omega),
      hI.scr.st (show eD + 8 * j + 8 ≤ Z by omega), t15, hvA, hvB, sel_word]
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14,
    fun i hi => ?_, ?_⟩
  · rw [hm', hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [(writeW_outside t.mem B _ (by omega)).word (by omega) (by omega)]; exact hI.done i hi
    · exact word_writeW_self _ _ _ _
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega) x (by omega)]
    exact hI.frame x (by omega)

/-- The selection loop: `w` words. -/
theorem selLoop_ok {s : State} {B : Addr} {Z w eA eB eD : Nat} {c : Bool} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B eA) (hsi : s.gpr .rsi = off B eB) (hbx : s.gpr .rbx = off B eD)
    (h15 : s.gpr .r15 = mask c) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hA : eA + 8 * w ≤ Z) (hB : eB + 8 * w ≤ Z) (hD : eD + 8 * w ≤ Z)
    (sA : eD + 8 * w ≤ eA ∨ eA + 8 * w ≤ eD) (sB : eD + 8 * w ≤ eB ∨ eB + 8 * w ≤ eD) :
    WP isa (wordLoop 0 [.mov .rax (.mem (ix .r8 .r14)), .mov .rdx (.mem (ix .rsi .r14)), .alu .xor .rax (.reg .rdx),
      .alu .and .rax (.reg .r15), .alu .xor .rax (.reg .rdx), .store (ix .rbx .r14) .rax]) s fun t =>
      wv t.mem B eD w = (if c then wv s.mem B eA w else wv s.mem B eB w) ∧ Scr t B Z ∧
      Outside B eD (8 * w) s.mem t.mem ∧ Keep [.rax, .rdx, .r14] s t := by
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw' (SelInv s B Z eA eB eD c)
    (fun t h14 hm k _ => ⟨hs.congr k.2.2, k.mono (by decide), h14, fun i hi => absurd hi (Nat.not_lt_zero _),
      by rw [hm]; exact Outside.refl _ _ _ _⟩)
    (fun j _ hj t hI => selStep_ok h8 hsi hbx h15 h12 (by omega) hA hB hD sA sB hj hI)) fun t hI => ?_
  refine ⟨?_, hI.scr, hI.frame, hI.keep⟩
  cases c
  · exact wv_congr2 fun i hi => by rw [hI.done i hi]; rfl
  · exact wv_congr2 fun i hi => by rw [hI.done i hi]; rfl

/-- `eqMask j`: the mask of `[aY] = [j]` into `rbp`, for an extra array `j`. -/
theorem eqMask_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {j : Nat} (hj : 7 < j)
    (hjZ : slot w j + 8 * (w + 2) ≤ Z) :
    WP isa (seqs (eqMask j)) s fun t =>
      t.gpr .rbp = mask (decide (wv s.mem B (slot w aY) w = wv s.mem B (slot w j) w)) ∧ t.mem = s.mem ∧
      Keep [.rax, .rbx, .rbp, .r10, .r12, .r14] s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have sY := Nat.le_trans (slot_le (w := w) (show aY < 8 by decide)) hZ
  unfold eqMask
  simp only [seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r12, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rbx = off B (slot w aY) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aY) (by decide), hg.hdr.hw,
      hg.hdr.harr aY (by decide)]) rfl) fun s₁ ⟨⟨h12, hbx, hm₁⟩, k₁⟩ => ?_
  have hg₁ : Good s₁ B Z w mi := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, by rw [hm₁]; exact hg.hdr⟩
  refine WP.mono (extBase_ok hg₁ hZ hw' (j := j) (by omega) (r := .r10) (by decide) rfl rfl)
    fun s₂ ⟨h10, hm₂, k₂⟩ => ?_
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = 0 ∧ t.mem = s₂.mem) (by xrun) rfl)
    fun s₃ ⟨⟨hbp, hm₃⟩, k₃⟩ => ?_
  have k13 := (k₁.trans k₂).trans k₃
  have hs₃ := (hg₁.scr.congr k₂.2.2).congr k₃.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₃.mem → Keep [.r14] s₃ t → t.cf = s₃.cf →
      OrInv s₃ B Z (fun j' => ∀ i < j', word s₃.mem B (slot w aY + 8 * i) = word s₃.mem B (slot w j + 8 * i))
        0 t := fun t h14 hm k _ =>
    ⟨hs₃.congr k.2.2, k.mono (by decide), hm, h14, by
      rw [(k.gpr (by decide) : t.gpr .rbp = s₃.gpr .rbp), hbp]
      exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw' _ h0
    (fun i _ hi t hI => xorStep_ok ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hbx))
      ((k₃.gpr (by decide)).trans h10) ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12)) (by omega)
      (by omega) (by omega) hi hI)) fun s₄ hI => ?_)
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask (decide (s₄.gpr .rbp = 0)) ∧ t.mem = s₄.mem) (by
    xrun
    rw [decide_lt_one]; rfl) rfl) fun t ⟨⟨hbp', hm⟩, k⟩ => ⟨?_, by rw [hm, hI.mem, hm₃, hm₂, hm₁],
      ((k13.trans hI.keep).trans k).mono (by decide)⟩
  rw [hbp']
  congr 1
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, hI.val, hm₃, hm₂, hm₁]
  exact ⟨fun h => (wv_congr2 fun i hi => (h i hi).symm).symm, fun h => wv_inj w h⟩

end VG.Proof.RsaKeyGen.X86_64
