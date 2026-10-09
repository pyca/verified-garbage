import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideGeneral
import VerifiedGarbage.Proof.Bignum.Square
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused

/-! The rows of the off-diagonal part of an ADX square. -/

namespace VG.Proof.Bignum.X86_64.AdxSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem off_add8 (B : Addr) (q : Nat) : off B q + 8 = off B (q + 8) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]; rfl

/-- The row carry is written above its processed words. -/
theorem crossTail_ok {s : State} {B : Addr} {Z e i w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B e) (h14 : s.gpr .r14 = BitVec.ofNat 64 i)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 i) (h10 : s.gpr .r10 = BitVec.ofNat 64 w)
    (hZ : e + 8 * i + 8 ≤ Z) (hi : i + 1 < 2 ^ 64) (hw : w < 2 ^ 64) :
    WP isa (.block AdxSquare.crossTail) s fun t =>
      t.mem = s.mem.writeW (off B (e + 8 * i)) (s.gpr .rcx) ∧
      t.gpr .r8 = off B (e + 8) ∧ t.gpr .rbp = BitVec.ofNat 64 (i + 1) ∧
      t.zf = some (decide (i + 1 = w)) ∧ Keep [.r8, .rbp] s t := by
  refine WP.mono (WP.keep [.r8, .rbp] (Q := fun t =>
      t.mem = s.mem.writeW (off B (e + 8 * i)) (s.gpr .rcx) ∧
      t.gpr .r8 = off B (e + 8) ∧ t.gpr .rbp = BitVec.ofNat 64 (i + 1) ∧
      t.zf = some (decide (i + 1 = w))) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  unfold AdxSquare.crossTail
  xrun [State.ea, ix, h8, h14, hbp, h10, addrK0, Nat.mul_zero, Nat.add_zero,
    hs.st hZ, off_add8, ofNat_add_one, ofNat_sub_beq hi hw]

/-- One row of cross products, with its carry included in the result. -/
theorem crossRow_ok {s : State} {B : Addr} {Z e eb i w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B eb)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 i) (h10 : s.gpr .r10 = BitVec.ofNat 64 w)
    (hi : i < w) (hw : w < 2 ^ 60)
    (hZ : e + 8 * (i + 1) ≤ Z) (hZb : eb + 8 * (i + 1) ≤ Z)
    (sb : eb + 8 * (i + 1) ≤ e ∨ e + 8 * (i + 1) ≤ eb) :
    WP isa AdxSquare.crossRow s fun t =>
      wv t.mem B e (i + 1) = wv s.mem B e i +
        (word s.mem B (eb + 8 * i)).toNat * wv s.mem B eb i ∧
      Outside B e (8 * (i + 1)) s.mem t.mem ∧
      t.gpr .r8 = off B (e + 8) ∧ t.gpr .rbp = BitVec.ofNat 64 (i + 1) ∧
      t.zf = some (decide (i + 1 = w)) ∧
      Keep [.rsi, .rdx, .rax, .r11, .r12, .r13, .r15, .rcx, .r14, .rbx, .r8, .rbp] s t := by
  have hn := hs.nowrap
  have rd : readSrc s (.mem (ix .r9 .rbp)) = some (word s.mem B (eb + 8 * i)) :=
    readSrc_word hs (by simpa using ea_ixk s h9 hbp 0) (by omega)
  unfold AdxSquare.crossRow
  refine WP.seq (WP.mono (movMem_ok s (dst := .rdx) rd) fun s₁ ⟨hdx, _, _, k₁⟩ => ?_)
  refine WP.seq (WP.mono (AdxSquareWide.generalRow_ok (hs.congr k₁.2.2.2) ((k₁.gpr (by decide)).trans h8)
    ((k₁.gpr (by decide)).trans h9) ((k₁.gpr (by decide)).trans hbp) (by omega)
    (by omega) (by omega) (by omega)) fun s₂ ⟨hv, ho, h14, k₂⟩ => ?_)
  have k12 := k₁.keep.trans k₂
  refine WP.mono (crossTail_ok (hs.congr k12.2.2) ((k12.gpr (by decide)).trans h8) h14
    ((k12.gpr (by decide)).trans hbp) ((k12.gpr (by decide)).trans h10)
    (by omega) (by omega) (by omega)) fun t ⟨hm, h8', hbp', hz, kt⟩ => ?_
  rw [k₁.2.1, hdx] at hv
  rw [k₁.2.1] at ho
  refine ⟨?_, ?_, h8', hbp', hz, (k12.trans kt).mono (by decide)⟩
  · rw [hm, wv_writeW_top _ _ _ _ _ (by omega)]
    exact hv
  · rw [hm]
    exact (ho.mono (Nat.le_refl _) (by omega)).trans
      ((writeW_outside s₂.mem B (s₂.gpr .rcx) (d := e + 8 * i) (by omega)).mono (by omega) (by omega))

/-- Replacing a contiguous digit window changes the whole value by the
window's change times its radix offset. -/
theorem wv_change_window {m m' : Mem} {B : Addr} {A n i len v : Nat}
    (hn : i + len ≤ n) (hA : A + 8 * n ≤ 2 ^ 64)
    (ho : Outside B (A + 8 * i) (8 * len) m m')
    (hv : wv m' B (A + 8 * i) len = wv m B (A + 8 * i) len + v) :
    wv m' B A n = wv m B A n + 2 ^ (64 * i) * v := by
  have hl : wv m' B A i = wv m B A i := ho.wv (by omega) (by omega)
  have hh : wv m' B (A + 8 * i + 8 * len) (n - (i + len)) =
      wv m B (A + 8 * i + 8 * len) (n - (i + len)) := ho.wv (by omega) (by omega)
  have he : n = i + (len + (n - (i + len))) := by omega
  have h1 := wv_add m' B A i (len + (n - (i + len)))
  have h2 := wv_add m B A i (len + (n - (i + len)))
  rw [← he] at h1 h2
  rw [h1, h2, wv_add m' B (A + 8 * i), wv_add m B (A + 8 * i), hl, hh, hv]
  grind

/-- The target-independent digit value agrees with the working-space one. -/
theorem value_words (m : Mem) (B : Addr) (eb i : Nat) :
    Square.value (2 ^ 64) (fun j => (word m B (eb + 8 * j)).toNat) i = wv m B eb i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Square.value, wv, ih, ← Nat.pow_mul, Nat.mul_comm (word m B (eb + 8 * i)).toNat]

/-- The off-diagonal product of the first `i` input words, counted once. -/
def crossValue (m : Mem) (B : Addr) (eb : Nat) (i : Nat) : Nat :=
  Square.cross (2 ^ 64) (fun j => (word m B (eb + 8 * j)).toNat) i

theorem crossValue_succ (m : Mem) (B : Addr) (eb i : Nat) :
    crossValue m B eb (i + 1) = crossValue m B eb i +
      wv m B eb i * (word m B (eb + 8 * i)).toNat * 2 ^ (64 * i) := by
  unfold crossValue
  rw [Square.cross, value_words, ← Nat.pow_mul]

/-- Before row `i`, the buffer holds the cross products of the first `i`
words. Words at and above `2 i` are still zero. -/
structure CrossInv (s₀ : State) (B : Addr) (Z A eb w : Nat) (i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rsi, .rdx, .rax, .r11, .r12, .r13, .r15, .rcx, .r14, .rbx, .r8, .rbp] s₀ t
  r8 : t.gpr .r8 = off B (A + 8 * i)
  rbp : t.gpr .rbp = BitVec.ofNat 64 i
  out : Outside B A (8 * (2 * w + 2)) s₀.mem t.mem
  val : wv t.mem B A (2 * w + 2) = crossValue s₀.mem B eb i
  zero : ∀ k, 2 * i ≤ k → k < 2 * w + 2 → word t.mem B (A + 8 * k) = 0

/-- Each row computes new cross products without changing earlier ones. -/
theorem crossStep_ok {s₀ t : State} {B : Addr} {Z A eb w i : Nat}
    (h9 : s₀.gpr .r9 = off B eb) (h10 : s₀.gpr .r10 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 60) (hi : i < w)
    (hA : A + 8 * (2 * w + 2) ≤ Z) (hb : eb + 8 * w ≤ Z)
    (sb : eb + 8 * w ≤ A ∨ A + 8 * (2 * w + 2) ≤ eb)
    (hI : CrossInv s₀ B Z A eb w i t) :
    WP isa AdxSquare.crossRow t fun t' =>
      t'.zf = some (decide (i + 1 = w)) ∧ CrossInv s₀ B Z A eb w (i + 1) t' := by
  have hn := hI.scr.nowrap
  have kp := hI.keep
  refine WP.mono (crossRow_ok hI.scr hI.r8 ((kp.gpr (by decide)).trans h9)
    hI.rbp ((kp.gpr (by decide)).trans h10) hi hw (by omega) (by omega) (by omega))
    fun t' ⟨hv, ho, h8', hbp', hz, kt⟩ => ⟨hz, ?_⟩
  have rB : wv t.mem B eb i = wv s₀.mem B eb i := hI.out.wv (by omega) (by omega)
  have rX : word t.mem B (eb + 8 * i) = word s₀.mem B (eb + 8 * i) := hI.out.word (by omega) (by omega)
  have z : word t.mem B (A + 8 * i + 8 * i) = 0 := by
    rw [show A + 8 * i + 8 * i = A + 8 * (2 * i) by omega]
    exact hI.zero _ (Nat.le_refl _) (by omega)
  have old : wv t.mem B (A + 8 * i) (i + 1) = wv t.mem B (A + 8 * i) i := by
    rw [wv, z]; simp
  rw [rB, rX, ← old] at hv
  have global := wv_change_window (n := 2 * w + 2) (by omega) (by omega) ho hv
  rw [hI.val] at global
  refine ⟨hI.scr.congr kt.2.2, (kp.trans kt).mono (by decide), ?_, hbp',
    hI.out.trans (ho.mono (o' := A) (n' := 8 * (2 * w + 2)) (by omega) (by omega)), ?_, ?_⟩
  · rw [h8']; congr 1
  · rw [global, crossValue_succ]
    grind
  · intro k hk hk'
    rw [ho.word (by omega) (by omega)]
    exact hI.zero k (by omega) hk'

theorem crossValue_congr {m m' : Mem} {B : Addr} {eb w : Nat}
    (h : ∀ j < w, word m' B (eb + 8 * j) = word m B (eb + 8 * j)) :
    crossValue m' B eb w = crossValue m B eb w := by
  induction w with
  | zero => rfl
  | succ w ih =>
    rw [crossValue_succ, crossValue_succ, ih (fun j hj => h j (by omega)), h w (by omega),
      wv_congr (fun j hj => h j (by omega))]

/-- All off-diagonal products are accumulated once, preserving the input. -/
theorem cross_ok {s : State} {B : Addr} {Z A eb w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B A) (h9 : s.gpr .r9 = off B eb)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 w) (hw1 : 2 ≤ w) (hw : w < 2 ^ 60)
    (hA : A + 8 * (2 * w + 2) ≤ Z) (hb : eb + 8 * w ≤ Z)
    (sb : eb + 8 * w ≤ A ∨ A + 8 * (2 * w + 2) ≤ eb) :
    WP isa AdxSquare.cross s fun t =>
      wv t.mem B A (2 * w + 2) = crossValue s.mem B eb w ∧
      Outside B A (8 * (2 * w + 2)) s.mem t.mem ∧
      (∀ k, 2 * w ≤ k → k < 2 * w + 2 → word t.mem B (A + 8 * k) = 0) ∧
      Keep [.rax, .rcx, .r14, .r10, .rbp, .r8, .rsi, .rdx, .r11, .r12, .r13, .r15, .rbx] s t := by
  have hn := hs.nowrap
  unfold AdxSquare.cross
  refine WP.seq (WP.mono (zeroWin_ok hs h8 hbx hw hA) fun s₁ ⟨hz₁, ho₁, k₁⟩ => ?_)
  have h8₁ : s₁.gpr .r8 = off B A := (k₁.gpr (by decide)).trans h8
  have hbx₁ : s₁.gpr .rbx = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans hbx
  have init : WP isa (.block [.mov .r10 (.reg .rbx), .mov32 .rbp (.imm 1), .alu .add .r8 (.imm 8)]) s₁ fun t =>
      t.gpr .r10 = BitVec.ofNat 64 w ∧ t.gpr .rbp = BitVec.ofNat 64 1 ∧
      t.gpr .r8 = off B (A + 8) ∧ t.mem = s₁.mem ∧ Keep [.r10, .rbp, .r8] s₁ t := by
    refine WP.mono (WP.keep [.r10, .rbp, .r8] (Q := fun t =>
      t.gpr .r10 = BitVec.ofNat 64 w ∧ t.gpr .rbp = BitVec.ofNat 64 1 ∧
      t.gpr .r8 = off B (A + 8) ∧ t.mem = s₁.mem) ?_ rfl)
      fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
    xrun [h8₁, hbx₁, off_add8]
  refine WP.seq (WP.mono init fun s₂ ⟨h10₂, hbp₂, h8₂, hm₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.2.2
  have h9₂ : s₂.gpr .r9 = off B eb := (k12.gpr (by decide)).trans h9
  have hI : CrossInv s₂ B Z A eb w 1 s₂ :=
    ⟨hs₂, Keep.refl _ _, h8₂, hbp₂, Outside.refl _ _ _ _, by
      rw [hm₂, wv_zero hz₁]; simp [crossValue, Square.cross, Square.value], fun k _ hk => by rw [hm₂]; exact hz₁ k hk⟩
  refine WP.mono (wp_upto (a := 1) (N := w) (by omega) (CrossInv s₂ B Z A eb w)
    (fun i _ hi t hI => crossStep_ok h9₂ h10₂ hw hi hA hb sb hI) (fun _ h => h) hI)
    fun t h => ⟨?_, ?_, h.zero, (k12.trans h.keep).mono (by decide)⟩
  · rw [h.val]
    apply crossValue_congr
    intro j hj
    rw [hm₂]
    exact ho₁.word (by omega) (by omega)
  · have ho := h.out
    rw [hm₂] at ho
    exact ho₁.trans ho

end VG.Proof.Bignum.X86_64.AdxSquare
