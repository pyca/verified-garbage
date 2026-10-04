import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Impl.Rsa.X86_64.Crt

/-!
# Multiword arithmetic on x86-64: addition and subtraction modulo `m`

`addMod o a b`: `[o] := [a] + [b] mod m` (`addMod_ok`), as `double` does
for `2 [o]`. `subModArr o a b`: `[o] := [a] - [b] mod m` (`subModArr_ok`):
`subMod`'s loop into the accumulator, then `m` added under the mask of its
borrow.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-! ## Addition -/

/-- After `j` words of `addMod`'s loop: `A_j + 2^(64 j) c = a_j + b_j`. -/
structure AddInv (s₀ : State) (B : Addr) (Z eA ea eb : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B eA (8 * j) s₀.mem t.mem
  val : ∃ c : Bool, t.gpr .rbp = mask c ∧
    wv t.mem B eA j + 2 ^ (64 * j) * c.toNat = wv s₀.mem B ea j + wv s₀.mem B eb j

theorem addStep_ok {s₀ : State} {B : Addr} {Z w eA ea eb : Nat}
    (h8 : s₀.gpr .r8 = off B eA) (hbx : s₀.gpr .rbx = off B ea) (h9 : s₀.gpr .r9 = off B eb)
    (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (hA : eA + 8 * w ≤ Z) (ha : ea + 8 * w ≤ Z) (hb : eb + 8 * w ≤ Z)
    (sa : ea + 8 * w ≤ eA ∨ eA + 8 * w ≤ ea) (sb : eb + 8 * w ≤ eA ∨ eA + 8 * w ≤ eb)
    {j : Nat} (hj : j < w) {t : State} (hI : AddInv s₀ B Z eA ea eb j t) :
    WP isa (.block ([cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .adc .rax (.mem (ix .r9 .r14)),
        .store (ix .r8 .r14) .rax, cfToRbp] ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ AddInv s₀ B Z eA ea eb (j + 1) t' := by
  have hn := hI.scr.nowrap
  have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans h8
  have tbx : t.gpr .rbx = off B ea := (hI.keep.gpr (by decide)).trans hbx
  have t9 : t.gpr .r9 = off B eb := (hI.keep.gpr (by decide)).trans h9
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨c, hbp, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ =>
      ∃ c' : Bool, t₁.gpr .rbp = mask c' ∧ ∃ r : BitVec 64, t₁.mem = t.mem.writeW (off B (eA + 8 * j)) r ∧
        r.toNat + 2 ^ 64 * c'.toNat =
          (word t.mem B (ea + 8 * j)).toNat + (word t.mem B (eb + 8 * j)).toNat + c.toNat) ?_ rfl)
    fun t₁ ⟨⟨c', h₁, r, hm, hr⟩, k₁⟩ => ?_
  · unfold cfFromRbp cfToRbp
    xrun [State.ea, ix, addr0 t8 hI.r14, addr0 tbx hI.r14, addr0 t9 hI.r14, hbp, cf_mask,
      hI.scr.ld (show ea + 8 * j + 8 ≤ Z by omega), hI.scr.ld (show eb + 8 * j + 8 ≤ Z by omega),
      hI.scr.st (show eA + 8 * j + 8 ≤ Z by omega)]
    exact ⟨_, rfl, _, rfl, adc_toNat _ _ _⟩
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hx : word t.mem B (ea + 8 * j) = word s₀.mem B (ea + 8 * j) := hI.out.word (by omega) (by omega)
  have hy : word t.mem B (eb + 8 * j) = word s₀.mem B (eb + 8 * j) := hI.out.word (by omega) (by omega)
  rw [hx, hy] at hr
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    ⟨c', (k'.gpr (by decide)).trans h₁, ?_⟩⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B r (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega)]
    simp only [wv]
    rw [pow64_succ]
    grind

/-- `[o] := [a] + [b] mod m`, for `[a], [b] < m = [aN]`. -/
theorem addMod_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (d1 : o ≠ Public.aAcc) (d2 : o ≠ Public.aTmp) (d3 : a ≠ Public.aAcc) (d4 : b ≠ Public.aAcc)
    (hA : wv s.mem B (slot w a) w < wv s.mem B (slot w Public.aN) w)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w Public.aN) w) :
    WP isa (addMod o a b) s fun t =>
      wv t.mem B (slot w o) w = (wv s.mem B (slot w a) w + wv s.mem B (slot w b) w) %
        wv s.mem B (slot w Public.aN) w ∧
      Arrays B w [Public.aAcc, Public.aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have sp : ∀ {j k}, j ≠ k → slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j :=
    fun h => slot_sep h
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hacc : Public.aAcc < 8 := by decide
  have htmp : Public.aTmp < 8 := by decide
  have hmo : Public.aN < 8 := by decide
  have d5 : Public.aAcc ≠ Public.aN := by decide
  have d6 : Public.aAcc ≠ Public.aTmp := by decide
  have d7 : Public.aTmp ≠ Public.aN := by decide
  unfold addMod
  refine WP.seq (WP.mono (WP.keep [.rbx, .r9, .r10, .r8, .r12, .rsi, .rbp] (Q := fun t =>
      t.gpr .rbx = off B (slot w a) ∧ t.gpr .r9 = off B (slot w b) ∧ t.gpr .r10 = off B (slot w Public.aN) ∧
      t.gpr .r8 = off B (slot w Public.aAcc) ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rsi = off B (slot w Public.aTmp) ∧ t.gpr .rbp = mask false ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hl (sArr a) (by unfold sArr; omega),
      hl (sArr b) (by unfold sArr; omega), hl (sArr Public.aN) (by decide), hl (sArr Public.aAcc) (by decide),
      hl sW (by decide), hl (sArr Public.aTmp) (by decide), hH.harr a ha, hH.harr b hb, hH.harr Public.aN hmo,
      hH.harr Public.aAcc hacc, hH.harr Public.aTmp htmp, hH.hw]) rfl)
    fun s₁ ⟨⟨hbx, h9, h10, h8, h12, hsi₁, hbp, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → Keep [.r14] s₁ t → t.cf = s₁.cf →
      AddInv s₁ B Z (slot w Public.aAcc) (slot w a) (slot w b) 0 t := fun t h14 hm k _ =>
    ⟨hs₁.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp, by rw [hm]; rfl⟩⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw'
    (AddInv s₁ B Z (slot w Public.aAcc) (slot w a) (slot w b)) h0
    (fun j _ hj t hI => addStep_ok h8 hbx h9 h12 (by omega) (by have := sl _ hacc; omega)
      (by have := sl a ha; omega) (by have := sl b hb; omega) (by have := sp d3; omega)
      (by have := sp d4; omega) hj hI)) fun s₂ hI => ?_)
  obtain ⟨c, hc, hval⟩ := hI.val
  have s₂8 : s₂.gpr .r8 = off B (slot w Public.aAcc) := (hI.keep.gpr (by decide)).trans h8
  have s₂12 : s₂.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have s₂di : s₂.gpr .rdi = B := ((k₁.trans hI.keep).gpr (by decide)).trans hdi
  have s₂si : s₂.gpr .rsi = off B (slot w Public.aTmp) := (hI.keep.gpr (by decide)).trans hsi₁
  have hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off B (8 * i)) 8 := fun i hi =>
    hI.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have ho₂ : word s₂.mem B (8 * sArr o) = off B (slot w o) := by
    rw [hI.out.word (by have := hdr_lt_slot w Public.aAcc (show sArr o < 32 by unfold sArr; omega); omega) (by
      have := hdr_lt_slot w 8 (show sArr o < 32 by unfold sArr; omega); omega), hm₁]
    exact hH.harr o ho
  have hX : ∀ v : BitVec 64, (s₂.mem.writeW (off B (slot w Public.aAcc + 8 * w)) v).readW (off B (8 * sArr o)) 64 =
      off B (slot w o) := fun v => by
    have h1 := hdr_lt_slot w Public.aAcc (show sArr o < 32 by unfold sArr; omega)
    have h2 := hdr_lt_slot w 8 (show sArr o < 32 by unfold sArr; omega)
    exact ((writeW_outside s₂.mem B v (by have := sl _ hacc; omega)).word (Or.inl (by omega)) (by omega)).trans ho₂
  refine WP.seq (WP.mono (WP.keep [.rax, .rbp, .rbx] (Q := fun t => t.gpr .rsi = off B (slot w Public.aTmp) ∧
      t.gpr .rbx = off B (slot w o) ∧
      ∃ v : BitVec 64, v.toNat = c.toNat ∧ t.mem = s₂.mem.writeW (off B (slot w Public.aAcc + 8 * w)) v)
    (by
      unfold cfFromRbp
      xrun [State.ea, ix, hdr, s₂di, hdrOff, s₂si, addr0 s₂8 s₂12, hc, cf_mask,
        hI.scr.st (show slot w Public.aAcc + 8 * w + 8 ≤ Z by have := sl _ hacc; omega), sx0,
        hl₂ (sArr o) (by unfold sArr; omega), hX]
      refine ⟨_, ?_, rfl⟩
      cases c <;> rfl) rfl) fun s₃ ⟨⟨hsi, hbx₃, v, hv, hm₃⟩, k₃⟩ => ?_)
  have hs₃ := hI.scr.congr k₃.2.2
  have k13 := (hI.keep.trans k₃)
  have o3 : Outside B (slot w Public.aAcc) (8 * (w + 1)) s₁.mem s₃.mem := by
    rw [hm₃]
    intro x hx
    rw [writeW_outside s₂.mem B v (by have := sl _ hacc; omega) x (by omega)]
    exact hI.out x (by omega)
  rw [hm₁] at o3
  have fN : wv s₃.mem B (slot w Public.aN) w = wv s.mem B (slot w Public.aN) w :=
    o3.wv (by have := sp d5; omega) (by have := sl _ hmo; omega)
  have hTl : wv s₃.mem B (slot w Public.aAcc) w = wv s₂.mem B (slot w Public.aAcc) w := by
    rw [hm₃]; exact (writeW_outside s₂.mem B v (by have := sl _ hacc; omega)).wv (Or.inl (by omega))
      (by have := sl _ hacc; omega)
  have hTw : (word s₃.mem B (slot w Public.aAcc + 8 * w)).toNat = c.toNat := by
    rw [hm₃, word_writeW_self, hv]
  refine WP.seq (WP.mono (subMod_ok hs₃ ((k13.gpr (by decide)).trans h8) ((k13.gpr (by decide)).trans h10)
    hsi ((k13.gpr (by decide)).trans h12) (by omega) hw' (by have := sl _ hacc; omega)
    (by have := sl _ hmo; omega) (by have := sl _ htmp; omega) (by have := sp d6; omega)
    (by have := sp d7; omega)) fun s₄ ⟨c', lt, hbp', hlt, hD, ho₄, k₄⟩ => ?_)
  have hs₄ := hs₃.congr k₄.2.2
  have k14 := k13.trans k₄
  refine WP.mono (selectAcc_ok hs₄ ((k14.gpr (by decide)).trans h8) ((k₄.gpr (by decide)).trans hsi)
    ((k₄.gpr (by decide)).trans hbx₃) ((k14.gpr (by decide)).trans h12) hbp' (by omega) hw'
    (by have := sl _ hacc; omega) (by have := sl _ htmp; omega) (by have := sl o ho; omega)
    (by have := sp d1; omega) (by have := sp d2; omega)) fun t ⟨hv', hot, k₅⟩ => ?_
  have hacc₄ : wv s₄.mem B (slot w Public.aAcc) w = wv s₃.mem B (slot w Public.aAcc) w :=
    ho₄.wv (by have := sp d6; omega) (by have := sl _ hacc; omega)
  rw [fN] at hD
  rw [hm₁] at hval
  have hN0 : 0 < wv s.mem B (slot w Public.aN) w := by omega
  refine ⟨?_, ?_, ((k₁.trans k14).trans k₅).mono (by decide)⟩
  · rw [hv', hacc₄, hlt, hTw]
    have := VG.Proof.Bignum.csub_result (Tl := wv s₃.mem B (slot w Public.aAcc) w) (Tw := c.toNat) (Tw1 := 0)
      (D := wv s₄.mem B (slot w Public.aTmp) w) (m := wv s.mem B (slot w Public.aN) w) (R := 2 ^ (64 * w))
      (c := c'.toNat) (by have := wv_lt s.mem B (slot w Public.aN) w; omega) (wv_lt _ _ _ _) (Bool.toNat_le c')
      (wv_lt _ _ _ _) (by rw [hTl, Nat.mul_zero, Nat.add_zero]; omega) hD
    rw [Nat.mul_zero, Nat.add_zero, hTl, hval] at this
    rw [← this]
    by_cases h : c.toNat < c'.toNat <;> simp [h, hTl]
  · have a3 : Arrays B w [Public.aAcc, Public.aTmp, o] s.mem s₃.mem :=
      Arrays.of_outside (j := Public.aAcc) (by simp) o3 (Nat.le_refl _) (by omega)
    have a4 : Arrays B w [Public.aAcc, Public.aTmp, o] s₃.mem s₄.mem :=
      Arrays.of_outside (j := Public.aTmp) (by simp) ho₄ (Nat.le_refl _) (by omega)
    have a5 : Arrays B w [Public.aAcc, Public.aTmp, o] s₄.mem t.mem :=
      Arrays.of_outside (j := o) (by simp) hot (Nat.le_refl _) (by omega)
    exact (a3.trans a4).trans a5

/-! ## Subtraction -/

theorem and_mask (a : BitVec 64) (c : Bool) : (a &&& mask c).toNat = if c then a.toNat else 0 := by
  cases c
  · simp [mask_false]
  · simp only [mask_true, BitVec.and_allOnes, ite_true]

/-- After `j` words of the second loop of `subModArr`:
`O_j + 2^(64 j) c' = (c ? m_j : 0) + A_j`. -/
structure MaInv (s₀ : State) (B : Addr) (Z eo eN eA : Nat) (c : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B eo (8 * j) s₀.mem t.mem
  val : ∃ c' : Bool, t.gpr .rbp = mask c' ∧
    wv t.mem B eo j + 2 ^ (64 * j) * c'.toNat = (if c then wv s₀.mem B eN j else 0) + wv s₀.mem B eA j

theorem maStep_ok {s₀ : State} {B : Addr} {Z w eo eN eA : Nat} {c : Bool}
    (hbx : s₀.gpr .rbx = off B eo) (h10 : s₀.gpr .r10 = off B eN) (h8 : s₀.gpr .r8 = off B eA)
    (h15 : s₀.gpr .r15 = mask c) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (ho : eo + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z) (hA : eA + 8 * w ≤ Z)
    (sN : eN + 8 * w ≤ eo ∨ eo + 8 * w ≤ eN) (sA : eA + 8 * w ≤ eo ∨ eo + 8 * w ≤ eA)
    {j : Nat} (hj : j < w) {t : State} (hI : MaInv s₀ B Z eo eN eA c j t) :
    WP isa (.block (([.mov .rax (.mem (ix .r10 .r14)), .alu .and .rax (.reg .r15), cfFromRbp,
        .alu .adc .rax (.mem (ix .r8 .r14)), .store (ix .rbx .r14) .rax, cfToRbp] : List Instr) ++
        ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ MaInv s₀ B Z eo eN eA c (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = off B eo := (hI.keep.gpr (by decide)).trans hbx
  have t10 : t.gpr .r10 = off B eN := (hI.keep.gpr (by decide)).trans h10
  have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans h8
  have t15 : t.gpr .r15 = mask c := (hI.keep.gpr (by decide)).trans h15
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨c₀, hbp, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ =>
      ∃ c' : Bool, t₁.gpr .rbp = mask c' ∧ ∃ r : BitVec 64, t₁.mem = t.mem.writeW (off B (eo + 8 * j)) r ∧
        r.toNat + 2 ^ 64 * c'.toNat =
          (word t.mem B (eN + 8 * j) &&& mask c).toNat + (word t.mem B (eA + 8 * j)).toNat + c₀.toNat) ?_ rfl)
    fun t₁ ⟨⟨c', h₁, r, hm, hr⟩, k₁⟩ => ?_
  · unfold cfFromRbp cfToRbp
    xrun [State.ea, ix, addr0 tbx hI.r14, addr0 t10 hI.r14, addr0 t8 hI.r14, hbp, t15, cf_mask,
      hI.scr.ld (show eN + 8 * j + 8 ≤ Z by omega), hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega),
      hI.scr.st (show eo + 8 * j + 8 ≤ Z by omega)]
    exact ⟨_, rfl, _, rfl, adc_toNat _ _ _⟩
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hx : word t.mem B (eN + 8 * j) = word s₀.mem B (eN + 8 * j) := hI.out.word (by omega) (by omega)
  have hy : word t.mem B (eA + 8 * j) = word s₀.mem B (eA + 8 * j) := hI.out.word (by omega) (by omega)
  rw [hx, hy, and_mask] at hr
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    ⟨c', (k'.gpr (by decide)).trans h₁, ?_⟩⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B r (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega)]
    simp only [wv]
    rw [pow64_succ]
    cases c
    · simp only [ite_false, Bool.false_eq_true] at hr hval ⊢
      grind
    · simp only [ite_true] at hr hval ⊢
      grind

/-- `[o] := [a] - [b] mod m`, for `[a], [b] < m = [aN]`. -/
theorem subModArr_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (d1 : o ≠ Public.aAcc) (d2 : o ≠ Public.aN) (d3 : a ≠ Public.aAcc) (d4 : b ≠ Public.aAcc)
    (hA : wv s.mem B (slot w a) w < wv s.mem B (slot w Public.aN) w)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w Public.aN) w) :
    WP isa (seqs (subModArr o a b)) s fun t =>
      wv t.mem B (slot w o) w = (wv s.mem B (slot w a) w + wv s.mem B (slot w Public.aN) w -
        wv s.mem B (slot w b) w) % wv s.mem B (slot w Public.aN) w ∧
      Arrays B w [Public.aAcc, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have sp : ∀ {j k}, j ≠ k → slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j :=
    fun h => slot_sep h
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hacc : Public.aAcc < 8 := by decide
  have hmo : Public.aN < 8 := by decide
  have d5 : Public.aAcc ≠ Public.aN := by decide
  unfold subModArr
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r8, .r10, .rsi, .r12, .rbp] (Q := fun t =>
      t.gpr .r8 = off B (slot w a) ∧ t.gpr .r10 = off B (slot w b) ∧ t.gpr .rsi = off B (slot w Public.aAcc) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rbp = mask false ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hl (sArr a) (by unfold sArr; omega),
      hl (sArr b) (by unfold sArr; omega), hl (sArr Public.aAcc) (by decide), hl sW (by decide),
      hH.harr a ha, hH.harr b hb, hH.harr Public.aAcc hacc, hH.hw]) rfl)
    fun s₁ ⟨⟨h8, h10, hsi, h12, hbp, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → Keep [.r14] s₁ t → t.cf = s₁.cf →
      SubInv s₁ B Z (slot w a) (slot w b) (slot w Public.aAcc) 0 t := fun t h14 hm k _ =>
    ⟨hs₁.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp, by rw [hm]; rfl⟩⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw'
    (SubInv s₁ B Z (slot w a) (slot w b) (slot w Public.aAcc)) h0
    (fun j _ hj t hI => subStep_ok h8 h10 hsi h12 (by omega) (by have := sl a ha; omega)
      (by have := sl b hb; omega) (by have := sl _ hacc; omega) (by have := sp d3; omega)
      (by have := sp d4; omega) hj hI)) fun s₂ hI => ?_)
  obtain ⟨c, hc, hval⟩ := hI.val
  rw [hm₁] at hval
  have k12 := k₁.trans hI.keep
  have s₂di : s₂.gpr .rdi = B := (k12.gpr (by decide)).trans hdi
  have hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off B (8 * i)) 8 := fun i hi =>
    hI.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have fh : ∀ i < 32, word s₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    rw [hI.out.word (Or.inl (by have := hdr_lt_slot w Public.aAcc hi; omega)) (by
      have := hdr_lt_slot w 8 hi; omega), hm₁]
  refine WP.seq (WP.mono (WP.keep [.r15, .rbp, .r10, .r8, .rbx] (Q := fun t => t.gpr .r15 = mask c ∧
      t.gpr .rbp = mask false ∧ t.gpr .r10 = off B (slot w Public.aN) ∧ t.gpr .r8 = off B (slot w Public.aAcc) ∧
      t.gpr .rbx = off B (slot w o) ∧ t.mem = s₂.mem)
    (by xrun [State.ea, hdr, s₂di, hdrOff, hl₂ (sArr Public.aN) (by decide),
      hl₂ (sArr Public.aAcc) (by decide), hl₂ (sArr o) (by unfold sArr; omega), hc,
      (fh _ (by decide)).trans (hH.harr Public.aN hmo), (fh _ (by decide)).trans (hH.harr Public.aAcc hacc),
      (fh _ (by unfold sArr; omega)).trans (hH.harr o ho)]) rfl)
    fun s₃ ⟨⟨h15, hbp₃, h10₃, h8₃, hbx₃, hm₃⟩, k₃⟩ => ?_)
  have hs₃ := hI.scr.congr k₃.2.2
  have k13 := k12.trans k₃
  have h12₃ : s₃.gpr .r12 = BitVec.ofNat 64 w := ((hI.keep.trans k₃).gpr (by decide)).trans h12
  have h0' : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₃.mem → Keep [.r14] s₃ t → t.cf = s₃.cf →
      MaInv s₃ B Z (slot w o) (slot w Public.aN) (slot w Public.aAcc) c 0 t := fun t h14 hm k _ =>
    ⟨hs₃.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp₃, by rw [hm]; cases c <;> rfl⟩⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw'
    (MaInv s₃ B Z (slot w o) (slot w Public.aN) (slot w Public.aAcc) c) h0'
    (fun j _ hj t hI => maStep_ok hbx₃ h10₃ h8₃ h15 h12₃ (by omega) (by have := sl o ho; omega)
      (by have := sl _ hmo; omega) (by have := sl _ hacc; omega) (by have := sp (Ne.symm d2); omega)
      (by have := sp (Ne.symm d1); omega) hj hI)) fun t hI' => ?_
  obtain ⟨c', -, hv⟩ := hI'.val
  have oA : Outside B (slot w Public.aAcc) (8 * w) s.mem s₃.mem := by rw [hm₃, ← hm₁]; exact hI.out
  have fN : wv s₃.mem B (slot w Public.aN) w = wv s.mem B (slot w Public.aN) w :=
    oA.wv (by have := sp d5; omega) (by have := sl _ hmo; omega)
  have fA : wv s₃.mem B (slot w Public.aAcc) w = wv s₂.mem B (slot w Public.aAcc) w := by rw [hm₃]
  rw [fN, fA] at hv
  have hN := wv_lt s.mem B (slot w Public.aN) w
  have hR := wv_lt t.mem B (slot w o) w
  have hAc := wv_lt s₂.mem B (slot w Public.aAcc) w
  refine ⟨?_, ?_, ((k13.trans hI'.keep)).mono (by decide)⟩
  · generalize wv s₂.mem B (slot w Public.aAcc) w = D at *
    generalize wv s.mem B (slot w Public.aN) w = N at *
    generalize wv s.mem B (slot w a) w = x at *
    generalize wv s.mem B (slot w b) w = y at *
    generalize wv t.mem B (slot w o) w = r at *
    generalize (2 : Nat) ^ (64 * w) = R at *
    have hc1 := Bool.toNat_le c
    have hc2 := Bool.toNat_le c'
    cases c <;> cases c' <;> simp only [ite_true, ite_false, Bool.false_eq_true, Bool.toNat_true,
      Bool.toNat_false] at hv hval ⊢
    all_goals first
      | (rw [Nat.mod_eq_of_lt (by omega)]; omega)
      | (rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
  · have a1 : Arrays B w [Public.aAcc, o] s.mem s₃.mem :=
      Arrays.of_outside (j := Public.aAcc) (by simp) oA (Nat.le_refl _) (by omega)
    have a2 : Arrays B w [Public.aAcc, o] s₃.mem t.mem :=
      Arrays.of_outside (j := o) (by simp) hI'.out (Nat.le_refl _) (by omega)
    exact a1.trans a2

end VG.Proof.Bignum.X86_64
