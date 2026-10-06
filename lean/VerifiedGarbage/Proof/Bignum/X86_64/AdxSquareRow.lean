import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBlock

/-! Accumulating the ADX square's multiply-add blocks into a row. -/

namespace VG.Proof.Bignum.X86_64.AdxSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- A row's processed prefix and its carry equal the original prefix plus
`rdx` times the input prefix. The scalar stays in its register. -/
structure RowInv (s₀ : State) (B : Addr) (Z e eb : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rsi, .rax, .r11, .r12, .r13, .r15, .rcx, .r14, .rbx] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B e (8 * j) s₀.mem t.mem
  val : wv t.mem B e j + 2 ^ (64 * j) * (t.gpr .rcx).toNat =
    wv s₀.mem B e j + (s₀.gpr .rdx).toNat * wv s₀.mem B eb j + (s₀.gpr .rcx).toNat

/-- Appending either a four-word block or a single remainder word. -/
theorem RowInv.step {s₀ t t' : State} {B : Addr} {Z e eb j n w : Nat}
    (hI : RowInv s₀ B Z e eb j t) (hjn : j + n ≤ w)
    (hZ : e + 8 * w ≤ Z) (hZb : eb + 8 * w ≤ Z)
    (sb : eb + 8 * w ≤ e ∨ e + 8 * w ≤ eb)
    (hv : wv t'.mem B (e + 8 * j) n + 2 ^ (64 * n) * (t'.gpr .rcx).toNat =
      wv t.mem B (e + 8 * j) n + (t.gpr .rdx).toNat * wv t.mem B (eb + 8 * j) n + (t.gpr .rcx).toNat)
    (ho : Outside B (e + 8 * j) (8 * n) t.mem t'.mem)
    (h14 : t'.gpr .r14 = BitVec.ofNat 64 (j + n))
    (hk : Keep [.rsi, .rax, .r11, .r12, .r13, .r15, .rcx, .r14, .rbx] t t') :
    RowInv s₀ B Z e eb (j + n) t' := by
  have hn := hI.scr.nowrap
  have rT : wv t.mem B (e + 8 * j) n = wv s₀.mem B (e + 8 * j) n := hI.out.wv (by omega) (by omega)
  have rB : wv t.mem B (eb + 8 * j) n = wv s₀.mem B (eb + 8 * j) n := hI.out.wv (by omega) (by omega)
  have rL : wv t'.mem B e j = wv t.mem B e j := ho.wv (by omega) (by omega)
  rw [rT, rB, hI.keep.gpr (by decide)] at hv
  refine ⟨hI.scr.congr hk.2.2, (hI.keep.trans hk).mono (by simp), h14, ?_, ?_⟩
  · exact (hI.out.mono (o' := e) (n' := 8 * (j + n)) (Nat.le_refl _) (by omega)).trans
      (ho.mono (o' := e) (n' := 8 * (j + n)) (by omega) (by omega))
  · have hi := hI.val
    rw [wv_add, wv_add s₀.mem B e, wv_add s₀.mem B eb, rL, Nat.mul_add, Nat.pow_add]
    grind

/-- The four-word loop, from any already accumulated prefix. -/
theorem blocks_ok {s₀ s : State} {B : Addr} {Z e eb a w : Nat}
    (h8 : s₀.gpr .r8 = off B e) (h9 : s₀.gpr .r9 = off B eb)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 w)
    (hw4 : w % 4 = 0) (haw : 4 * a < w) (hw : w < 2 ^ 60)
    (hZ : e + 8 * w ≤ Z) (hZb : eb + 8 * w ≤ Z)
    (sb : eb + 8 * w ≤ e ∨ e + 8 * w ≤ eb)
    (hI : RowInv s₀ B Z e eb (4 * a) s) :
    WP isa (.loop (.block AdxSquare.mac4Store) .ne) s (RowInv s₀ B Z e eb w) := by
  refine wp_upto (a := a) (N := w / 4) (by omega) (fun k t => RowInv s₀ B Z e eb (4 * k) t ∧ t.gpr .rbx = BitVec.ofNat 64 w) ?_ ?_ ⟨hI, hbx⟩
  · intro k _ hk t h
    obtain ⟨h, hbx'⟩ := h
    have kp := h.keep
    refine WP.mono (mac4Store_ok h.scr ((kp.gpr (by decide)).trans h8)
      ((kp.gpr (by decide)).trans h9) h.r14 hbx'
      (by omega) (by omega) (by omega) (by omega)) fun t' ⟨hv, ho, h14, hz, kt⟩ => ⟨?_, ?_, (kt.gpr (by decide)).trans hbx'⟩
    · rw [hz]; congr 1; exact decide_eq_decide.mpr (by omega)
    · have step := h.step (by omega : 4 * k + 4 ≤ w) hZ hZb sb hv ho h14 (kt.mono (by simp))
      rw [show 4 * (k + 1) = 4 * k + 4 by omega]
      exact step
  · intro t h
    have he : 4 * (w / 4) = w := by omega
    exact he ▸ h.1

/-- The final zero to three words are handled by the same invariant. -/
theorem remainder_ok {s₀ s : State} {B : Addr} {Z e eb a w : Nat}
    (h8 : s₀.gpr .r8 = off B e) (h9 : s₀.gpr .r9 = off B eb)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 w) (haw : a < w) (hw : w < 2 ^ 60)
    (hZ : e + 8 * w ≤ Z) (hZb : eb + 8 * w ≤ Z)
    (sb : eb + 8 * w ≤ e ∨ e + 8 * w ≤ eb)
    (hI : RowInv s₀ B Z e eb a s) :
    WP isa (.loop (.block AdxSquare.mac1Store) .ne) s (RowInv s₀ B Z e eb w) := by
  refine wp_upto haw (fun j t => RowInv s₀ B Z e eb j t ∧ t.gpr .rbx = BitVec.ofNat 64 w)
    ?_ (fun _ h => h.1) ⟨hI, hbx⟩
  intro j _ hj t h
  obtain ⟨h, hbx'⟩ := h
  have kp := h.keep
  refine WP.mono (mac1Store_ok h.scr ((kp.gpr (by decide)).trans h8)
    ((kp.gpr (by decide)).trans h9) h.r14 hbx'
    (by omega) (by omega) (by omega) (by omega)) fun t' ⟨hv, ho, h14, hz, kt⟩ => ⟨hz, ?_, (kt.gpr (by decide)).trans hbx'⟩
  exact h.step (by omega : j + 1 ≤ w) hZ hZb sb hv ho h14 (kt.mono (by simp))

/-- Round a public word count down to a multiple of four. -/
theorem round4 (w : Nat) (hw : w < 2 ^ 64) :
    let q := BitVec.ofNat 64 w >>> 2
    q + q + (q + q) = BitVec.ofNat 64 (4 * (w / 4)) := by
  dsimp only
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

theorem rowStart_ok {s : State} {w : Nat} (hbp : s.gpr .rbp = BitVec.ofNat 64 w) (hw : w < 2 ^ 64) :
    WP isa (.block AdxSquare.rowStart) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (4 * (w / 4)) ∧ t.gpr .rcx = 0 ∧ t.gpr .r14 = 0 ∧
      t.zf = some (decide (4 * (w / 4) = 0)) ∧ t.mem = s.mem ∧ Keep [.rbx, .rcx, .r14] s t := by
  refine WP.mono (WP.keep [.rbx, .rcx, .r14] (Q := fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (4 * (w / 4)) ∧ t.gpr .rcx = 0 ∧ t.gpr .r14 = 0 ∧
      t.zf = some (decide (4 * (w / 4) = 0)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩
  unfold AdxSquare.rowStart
  xrun [hbp, round4 w hw]
  change (BitVec.ofNat 64 (4 * (w / 4)) - BitVec.ofNat 64 0 == 0) = _
  exact ofNat_sub_beq (by omega) (by decide)

/-- A complete multiply-add row, including lengths below four. -/
theorem macRow_ok {s : State} {B : Addr} {Z e eb w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B eb)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 w) (hw : w < 2 ^ 60)
    (hZ : e + 8 * w ≤ Z) (hZb : eb + 8 * w ≤ Z)
    (sb : eb + 8 * w ≤ e ∨ e + 8 * w ≤ eb) :
    WP isa AdxSquare.macRow s fun t =>
      wv t.mem B e w + 2 ^ (64 * w) * (t.gpr .rcx).toNat =
        wv s.mem B e w + (s.gpr .rdx).toNat * wv s.mem B eb w ∧
      Outside B e (8 * w) s.mem t.mem ∧ t.gpr .r14 = BitVec.ofNat 64 w ∧
      Keep [.rsi, .rax, .r11, .r12, .r13, .r15, .rcx, .r14, .rbx] s t := by
  unfold AdxSquare.macRow
  refine WP.seq (WP.mono (rowStart_ok hbp (by omega)) fun s₁ ⟨hbx₁, hcx₁, h14₁, hz₁, hm₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have h8₁ : s₁.gpr .r8 = off B e := (k₁.gpr (by decide)).trans h8
  have h9₁ : s₁.gpr .r9 = off B eb := (k₁.gpr (by decide)).trans h9
  have hi₁ : RowInv s₁ B Z e eb 0 s₁ :=
    ⟨hs₁, Keep.refl _ _, h14₁, Outside.refl _ _ _ _, by simp [wv]⟩
  have first : WP isa (.ite .ne (.loop (.block AdxSquare.mac4Store) .ne) (.block [])) s₁
      (RowInv s₁ B Z e eb (4 * (w / 4))) := by
    by_cases h0 : 4 * (w / 4) = 0
    · refine WP.ite false (by simp [eval, hz₁, h0]) (by simp) (fun _ => WP.block_nil ?_)
      rw [h0]; exact hi₁
    · refine WP.ite true (by simp [eval, hz₁, h0]) (fun _ => ?_) (by simp)
      exact blocks_ok (a := 0) h8₁ h9₁ hbx₁ (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) hi₁
  refine WP.seq (WP.mono first fun s₂ hI₂ => ?_)
  have k12 := k₁.trans hI₂.keep
  have hbp₂ : s₂.gpr .rbp = BitVec.ofNat 64 w := (k12.gpr (by decide)).trans hbp
  have mid : WP isa (.block AdxSquare.rowRemainder) s₂ fun t =>
      t.gpr .rbx = BitVec.ofNat 64 w ∧ t.zf = some (decide (4 * (w / 4) = w)) ∧
      t.mem = s₂.mem ∧ t.gpr .r14 = s₂.gpr .r14 ∧ Keep [.rbx, .r14] s₂ t := by
    refine WP.mono (WP.keep [.rbx, .r14] (Q := fun t => t.gpr .rbx = BitVec.ofNat 64 w ∧
      t.zf = some (decide (4 * (w / 4) = w)) ∧ t.mem = s₂.mem ∧ t.gpr .r14 = s₂.gpr .r14) ?_ rfl)
      fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
    unfold AdxSquare.rowRemainder
    xrun [hbp₂, hI₂.r14, ofNat_sub_beq (show 4 * (w / 4) < 2 ^ 64 by omega) (show w < 2 ^ 64 by omega)]
  refine WP.seq (WP.mono mid fun s₃ ⟨hbx₃, hz₃, hm₃, h14₃, k₃⟩ => ?_)
  have hI₃ : RowInv s₁ B Z e eb (4 * (w / 4)) s₃ :=
    ⟨hI₂.scr.congr k₃.2.2, (hI₂.keep.trans k₃).mono (by simp),
      h14₃.trans hI₂.r14, hm₃ ▸ hI₂.out, by
        rw [hm₃, k₃.gpr (by decide)]; exact hI₂.val⟩
  have last : WP isa (.ite .ne (.loop (.block AdxSquare.mac1Store) .ne) (.block [])) s₃
      (RowInv s₁ B Z e eb w) := by
    by_cases he : 4 * (w / 4) = w
    · refine WP.ite false (by simp [eval, hz₃, he]) (by simp) (fun _ => WP.block_nil ?_)
      exact he ▸ hI₃
    · refine WP.ite true (by simp [eval, hz₃, he]) (fun _ => ?_) (by simp)
      exact remainder_ok h8₁ h9₁ hbx₃ (by omega) hw hZ hZb sb hI₃
  refine WP.mono last fun t h => ⟨?_, ?_, h.r14, (k₁.trans h.keep).mono (by simp)⟩
  · have hv := h.val
    rw [hm₁, k₁.gpr (by decide), hcx₁] at hv
    simpa using hv
  · have ho := h.out
    rw [hm₁] at ho
    exact ho

end VG.Proof.Bignum.X86_64.AdxSquare
