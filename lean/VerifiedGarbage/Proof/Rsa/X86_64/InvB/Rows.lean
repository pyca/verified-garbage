module
-- separate module: the inverse's proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Rsa.X86_64.InvB.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-!
# RSA's inverse by divsteps on x86-64: a batch's rows

A batch updates `(f, g)` and `(a, b)` a word at a time, in place, each pair in one
pass (`fgRow`, `abRow`). This file has the pieces of a column: a product
accumulated into two or three words (`term2_ok`, `term3_ok`, `termM_ok`), the
word stored with the top bits of the one before it (`outS_ok`), and the step to
the next column (`next_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.InvB

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Inv
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem ea_wm (t : State) (o : Nat) : t.ea (wm o) = t.gpr .rdi + BitVec.ofInt 64 (o : Int) := rfl

/-- A factor's value: a register's, or its window slot's. -/
def CoIs (s : State) (B : Addr) (Z eW : Nat) : Co → BitVec 64 → Prop
  | .reg r, K => s.gpr r = K ∧ r ≠ .rax ∧ r ≠ .rdx
  | .slot o, K => word s.mem B (eW + o) = K ∧ eW + o + 8 ≤ Z

theorem CoIs.congr {s t : State} {B : Addr} {Z eW : Nat} {c : Co} {K : BitVec 64} (h : CoIs s B Z eW c K)
    (hm : t.mem = s.mem) (hr : ∀ r, c = .reg r → t.gpr r = s.gpr r) : CoIs t B Z eW c K := by
  cases c with
  | reg r => exact ⟨(hr r rfl).trans h.1, h.2⟩
  | slot o => exact ⟨by rw [hm]; exact h.1, h.2⟩

/-- `rdx:rax := rax · K`. -/
theorem mulCo_ok {s : State} {B : Addr} {Z eW : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = off B eW)
    {c : Co} {K : BitVec 64} (hc : CoIs s B Z eW c K) :
    WP isa (.block (mulCo c)) s fun t =>
      (t.gpr .rax).toNat + 2 ^ 64 * (t.gpr .rdx).toNat = (s.gpr .rax).toNat * K.toNat ∧ t.mem = s.mem ∧
      Keep [.rax, .rdx] s t := by
  cases c with
  | reg r =>
    obtain ⟨hK, h1, h2⟩ := hc
    refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t =>
      (t.gpr .rax).toNat + 2 ^ 64 * (t.gpr .rdx).toNat = (s.gpr .rax).toNat * K.toNat ∧ t.mem = s.mem) ?_ rfl)
      fun t ⟨a, k⟩ => ⟨a.1, a.2, k⟩
    unfold mulCo
    xrun [hK]
    have := Nat.div_add_mod ((s.gpr .rax).toNat * K.toNat) (2 ^ 64)
    have hlt : (s.gpr .rax).toNat * K.toNat < 2 ^ 64 * 2 ^ 64 :=
      Nat.mul_lt_mul'' (s.gpr .rax).isLt K.isLt
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul hlt)]
    omega
  | slot o =>
    obtain ⟨hK, ho⟩ := hc
    refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t =>
      (t.gpr .rax).toNat + 2 ^ 64 * (t.gpr .rdx).toNat = (s.gpr .rax).toNat * K.toNat ∧ t.mem = s.mem) ?_ rfl)
      fun t ⟨a, k⟩ => ⟨a.1, a.2, k⟩
    unfold mulCo
    xrun [ea_wm, hdi, offD, hs.ld ho, hK]
    have := Nat.div_add_mod ((s.gpr .rax).toNat * K.toNat) (2 ^ 64)
    have hlt : (s.gpr .rax).toNat * K.toNat < 2 ^ 64 * 2 ^ 64 :=
      Nat.mul_lt_mul'' (s.gpr .rax).isLt K.isLt
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul hlt)]
    omega

/-- `mov rax, [x]; xor rax, [mask]`. -/
theorem ldx_ok {s : State} {B : Addr} {Z eW : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = off B eW)
    {x : MemOp} {e : Nat} (hx : s.ea x = off B e) (he : e + 8 ≤ Z) {m : Nat} (hm : eW + m + 8 ≤ Z) :
    WP isa (.block [.mov .rax (.mem x), .alu .xor .rax (.mem (wm m))]) s fun t =>
      t.gpr .rax = word s.mem B e ^^^ word s.mem B (eW + m) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.gpr .rax = word s.mem B e ^^^ word s.mem B (eW + m) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨a, k⟩ => ⟨a.1, a.2, k⟩
  xrun [hx, hs.ld he, ea_wm, hdi, offD, hs.ld hm]

/-- `add lo, x; adc hi, y` as numbers, if the sum fits. -/
theorem acc2 (a h x y : BitVec 64)
    (hs : a.toNat + 2 ^ 64 * h.toNat + x.toNat + 2 ^ 64 * y.toNat < 2 ^ 128) :
    (a + x).toNat + 2 ^ 64 * (h + y + BitVec.setWidth 64 (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + x.toNat)))).toNat =
      a.toNat + 2 ^ 64 * h.toNat + x.toNat + 2 ^ 64 * y.toNat := by
  have ha := a.isLt; have hh := h.isLt; have hx := x.isLt; have hy := y.isLt
  have hc : (BitVec.setWidth 64 (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + x.toNat)))).toNat =
      if 2 ^ 64 ≤ a.toNat + x.toNat then 1 else 0 := by split <;> simp [*]
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, hc]
  split <;> omega

/-- `lo:hi += K (x ^ mask)`. -/
theorem term2_ok {s : State} {B : Addr} {Z eW : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = off B eW)
    {x : MemOp} {e : Nat} (hx : s.ea x = off B e) (he : e + 8 ≤ Z) {m : Nat} (hm : eW + m + 8 ≤ Z)
    {c : Co} {K : BitVec 64} (hc : CoIs s B Z eW c K) {lo hi : Reg} (h1 : lo ≠ .rax) (h2 : lo ≠ .rdx)
    (h3 : hi ≠ .rax) (h4 : hi ≠ .rdx) (h5 : hi ≠ lo)
    (hk : writesOnly [.rax, .rdx, lo, hi] (.block (term2 x c m lo hi)) = true)
    (hsum : (s.gpr lo).toNat + 2 ^ 64 * (s.gpr hi).toNat +
      K.toNat * (word s.mem B e ^^^ word s.mem B (eW + m)).toNat < 2 ^ 128) :
    WP isa (.block (term2 x c m lo hi)) s fun t =>
      (t.gpr lo).toNat + 2 ^ 64 * (t.gpr hi).toNat = (s.gpr lo).toNat + 2 ^ 64 * (s.gpr hi).toNat +
        K.toNat * (word s.mem B e ^^^ word s.mem B (eW + m)).toNat ∧ t.mem = s.mem ∧
      Keep [.rax, .rdx, lo, hi] s t := by
  refine WP.mono (WP.keep [.rax, .rdx, lo, hi] (Q := fun t =>
    (t.gpr lo).toNat + 2 ^ 64 * (t.gpr hi).toNat = (s.gpr lo).toNat + 2 ^ 64 * (s.gpr hi).toNat +
        K.toNat * (word s.mem B e ^^^ word s.mem B (eW + m)).toNat ∧ t.mem = s.mem) ?_ hk)
    fun t ⟨a, k⟩ => ⟨a.1, a.2, k⟩
  unfold term2
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ldx_ok hs hdi hx he hm) fun s₁ ⟨a₁, m₁, k₁⟩ => ?_
  have hc₁ : CoIs s₁ B Z eW c K := hc.congr m₁ fun r hr => by
    subst hr; exact k₁.gpr (by simp [hc.2.1])
  refine WP.mono (mulCo_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi) hc₁) fun s₂ ⟨a₂, m₂, k₂⟩ => ?_
  have l₂ : s₂.gpr lo = s.gpr lo := (k₂.gpr (by simp [h1, h2])).trans (k₁.gpr (by simp [h1]))
  have i₂ : s₂.gpr hi = s.gpr hi := (k₂.gpr (by simp [h3, h4])).trans (k₁.gpr (by simp [h3]))
  rw [a₁] at a₂
  xrun [h1, h2, h3, h4, h5, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5]
  refine ⟨?_, by rw [m₂, m₁]⟩
  have := Nat.mul_comm K.toNat (word s.mem B e ^^^ word s.mem B (eW + m)).toNat
  rw [acc2 _ _ _ _ (by rw [l₂, i₂]; omega), l₂, i₂]
  omega

/-- `add a, x; adc b, y; adc c, 0` as numbers, if the sum fits. -/
theorem acc3 (a b c x y : BitVec 64)
    (hs : a.toNat + 2 ^ 64 * b.toNat + 2 ^ 128 * c.toNat + x.toNat + 2 ^ 64 * y.toNat < 2 ^ 192) :
    (a + x).toNat + 2 ^ 64 * (b + y + BitVec.setWidth 64 (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + x.toNat)))).toNat +
      2 ^ 128 * (c + BitVec.setWidth 64 (BitVec.ofBool (decide (2 ^ 64 ≤ b.toNat + y.toNat +
        (decide (2 ^ 64 ≤ a.toNat + x.toNat)).toNat)))).toNat =
      a.toNat + 2 ^ 64 * b.toNat + 2 ^ 128 * c.toNat + x.toNat + 2 ^ 64 * y.toNat := by
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt; have hx := x.isLt; have hy := y.isLt
  have e1 : (BitVec.setWidth 64 (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + x.toNat)))).toNat =
      (decide (2 ^ 64 ≤ a.toNat + x.toNat)).toNat := by
    by_cases h : 2 ^ 64 ≤ a.toNat + x.toNat <;> simp [h]
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, e1]
  by_cases h1 : 2 ^ 64 ≤ a.toNat + x.toNat
  · simp only [h1, decide_true, Bool.toNat_true]
    by_cases h2 : 2 ^ 64 ≤ b.toNat + y.toNat + 1
    · simp only [h2, decide_true]; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofBool, Bool.toNat_true]; omega
    · simp only [h2, decide_false]; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofBool, Bool.toNat_false]; omega
  · simp only [h1, decide_false, Bool.toNat_false]
    by_cases h2 : 2 ^ 64 ≤ b.toNat + y.toNat + 0
    · simp only [h2, decide_true]; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofBool, Bool.toNat_true]; omega
    · simp only [h2, decide_false]; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofBool, Bool.toNat_false]; omega

/-- `add lo, rax; adc mid, rdx; adc top, 0`. -/
theorem add3_ok {s : State} {lo mid top : Reg} (h2 : lo ≠ .rdx) (h5 : mid ≠ lo) (h8 : top ≠ lo)
    (h9 : top ≠ mid)
    (hsum : (s.gpr lo).toNat + 2 ^ 64 * (s.gpr mid).toNat + 2 ^ 128 * (s.gpr top).toNat +
      (s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .rdx).toNat < 2 ^ 192) :
    WP isa (.block [.alu .add lo (.reg .rax), .alu .adc mid (.reg .rdx), .alu .adc top (.imm 0)]) s fun t =>
      (t.gpr lo).toNat + 2 ^ 64 * (t.gpr mid).toNat + 2 ^ 128 * (t.gpr top).toNat =
        (s.gpr lo).toNat + 2 ^ 64 * (s.gpr mid).toNat + 2 ^ 128 * (s.gpr top).toNat +
        (s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .rdx).toNat ∧ t.mem = s.mem ∧
      (∀ r, r ≠ lo → r ≠ mid → r ≠ top → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  xrun [h2, h5, h8, h9, Ne.symm h2, Ne.symm h5, Ne.symm h8, Ne.symm h9]
  refine ⟨?_, fun r a b c => by simp [a, b, c]⟩
  rw [show BitVec.signExtend 64 (0 : BitVec 32) = 0 by decide, show ∀ x : BitVec 64, x + 0 = x from BitVec.add_zero]
  exact acc3 _ _ _ _ _ hsum

theorem ea_px (t : State) (d : Int) : t.ea (px d) = t.gpr .r8 + BitVec.ofInt 64 d := rfl
theorem ea_py (t : State) (d : Int) :
    t.ea (py d) = t.gpr .r8 + t.gpr .r9 * BitVec.ofNat 64 1 + BitVec.ofInt 64 d := rfl
theorem ea_pm (t : State) (d : Int) :
    t.ea (pm d) = t.gpr .r8 + t.gpr .r9 * BitVec.ofNat 64 4 + BitVec.ofInt 64 d := rfl

theorem off_m8 (p : Addr) (e : Nat) : off p (e + 8) + BitVec.ofInt 64 (-8) = off p e := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]
  rw [show BitVec.ofNat 64 8 + BitVec.ofInt 64 (-8) = 0 by decide]
  simp

theorem off_py0 (p : Addr) (e S : Nat) :
    off p e + BitVec.ofNat 64 S * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = off p (e + S) := by
  simp only [off, BitVec.ofNat_add]
  grind

theorem off_pym8 (p : Addr) (e S : Nat) :
    off p (e + 8) + BitVec.ofNat 64 S * BitVec.ofNat 64 1 + BitVec.ofInt 64 (-8) = off p (e + S) := by
  have h8 : BitVec.ofInt 64 (-8) = -BitVec.ofNat 64 8 := by decide
  simp only [off, BitVec.ofNat_add, h8]
  grind

theorem off_pm (p : Addr) (e S : Nat) :
    off p e + BitVec.ofNat 64 S * BitVec.ofNat 64 4 + BitVec.ofInt 64 0 = off p (e + 4 * S) := by
  simp only [off, BitVec.ofNat_add, BitVec.ofNat_mul]
  grind

/-- `K x ≤ K (2^64 - 1)` for a word `x`. -/
theorem mul_word_le (K : Nat) (x : BitVec 64) : K * x.toNat ≤ K * 2 ^ 64 :=
  Nat.mul_le_mul_left _ (Nat.le_of_lt x.isLt)

/-- The window's slots and the arrays' words that a column of a row reads. -/
structure ColEnv (s : State) (B : Addr) (Z eW e S : Nat) : Prop where
  scr : Scr s B Z
  rdi : s.gpr .rdi = off B eW
  r8 : s.gpr .r8 = off B e
  r9 : s.gpr .r9 = BitVec.ofNat 64 S
  win : eW + 96 ≤ Z
  x : e + 8 ≤ Z
  y : e + S + 8 ≤ Z

theorem ColEnv.congr {s t : State} {B : Addr} {Z eW e S : Nat} (h : ColEnv s B Z eW e S)
    (k : Keep [.rax, .rdx, .r10, .r11, .r12, .r13] s t) : ColEnv t B Z eW e S :=
  ⟨h.scr.congr k.2.2, (k.gpr (by decide)).trans h.rdi, (k.gpr (by decide)).trans h.r8,
    (k.gpr (by decide)).trans h.r9, h.win, h.x, h.y⟩

/-- A column of `fgRow`: `r10:r11 += |u| x'+ |v| y'` and `r12:r13 += |q| x'' + |r| y''`, for `x`, `y`
the words at `r8` and `r8 + r9` complemented under the coefficients' masks. -/
theorem fgCol_ok {s : State} {B : Addr} {Z eW e S : Nat} (E : ColEnv s B Z eW e S)
    {Ku Kv : BitVec 64} (hu : s.gpr .rcx = Ku) (hv : s.gpr .r14 = Kv)
    (huv : Ku.toNat + Kv.toNat ≤ 2 ^ 59)
    (hqr : (word s.mem B (eW + oQ)).toNat + (word s.mem B (eW + oR)).toNat ≤ 2 ^ 59)
    (h11 : s.gpr .r11 = 0) (h13 : s.gpr .r13 = 0) :
    WP isa (.block fgCol) s fun t =>
      (t.gpr .r10).toNat + 2 ^ 64 * (t.gpr .r11).toNat = (s.gpr .r10).toNat +
        Ku.toNat * (word s.mem B e ^^^ word s.mem B (eW + oMu)).toNat +
        Kv.toNat * (word s.mem B (e + S) ^^^ word s.mem B (eW + oMv)).toNat ∧
      (t.gpr .r12).toNat + 2 ^ 64 * (t.gpr .r13).toNat = (s.gpr .r12).toNat +
        (word s.mem B (eW + oQ)).toNat * (word s.mem B e ^^^ word s.mem B (eW + oMq)).toNat +
        (word s.mem B (eW + oR)).toNat * (word s.mem B (e + S) ^^^ word s.mem B (eW + oMr)).toNat ∧
      t.mem = s.mem ∧ Keep [.rax, .rdx, .r10, .r11, .r12, .r13] s t := by
  have hN := E.scr.nowrap
  have hW := E.win
  have z0 : (0 : BitVec 64).toNat = 0 := rfl
  have exs : ∀ t : State, t.gpr .r8 = off B e → t.ea (px 0) = off B e := fun t h => by
    rw [ea_px, h]; exact BitVec.add_zero _
  have eys : ∀ t : State, t.gpr .r8 = off B e → t.gpr .r9 = BitVec.ofNat 64 S → t.ea (py 0) = off B (e + S) :=
    fun t h h' => by rw [ea_py, h, h', off_py0]
  have l1 := mul_word_le Ku.toNat (word s.mem B e ^^^ word s.mem B (eW + oMu))
  have l2 := mul_word_le Kv.toNat (word s.mem B (e + S) ^^^ word s.mem B (eW + oMv))
  have l3 := mul_word_le (word s.mem B (eW + oQ)).toNat (word s.mem B e ^^^ word s.mem B (eW + oMq))
  have l4 := mul_word_le (word s.mem B (eW + oR)).toNat (word s.mem B (e + S) ^^^ word s.mem B (eW + oMr))
  have b1 : Ku.toNat * 2 ^ 64 + Kv.toNat * 2 ^ 64 ≤ 2 ^ 59 * 2 ^ 64 := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ huv
  have b2 : (word s.mem B (eW + oQ)).toNat * 2 ^ 64 + (word s.mem B (eW + oR)).toNat * 2 ^ 64 ≤ 2 ^ 59 * 2 ^ 64 := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hqr
  have r10l := (s.gpr .r10).isLt
  have r12l := (s.gpr .r12).isLt
  unfold fgCol
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (term2_ok E.scr E.rdi (exs s E.r8) E.x (by unfold oMu; omega) (c := .reg .rcx)
    ⟨hu, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) rfl
    (by rw [h11]; (try simp only [BitVec.toNat_zero]); omega)) fun s₁ ⟨a₁, m₁, k₁⟩ => ?_
  have E₁ := E.congr (k₁.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (term2_ok E₁.scr E₁.rdi (eys s₁ E₁.r8 E₁.r9) E.y (by unfold oMv; omega) (c := .reg .r14)
    ⟨(k₁.gpr (by decide)).trans hv, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide)
    (by decide) rfl (by rw [m₁, a₁, h11]; (try simp only [BitVec.toNat_zero]); omega)) fun s₂ ⟨a₂, m₂, k₂⟩ => ?_
  have E₂ := E₁.congr (k₂.mono (by decide))
  have m₂' : s₂.mem = s.mem := m₂.trans m₁
  rw [WP.block_append_iff]
  refine WP.mono (term2_ok E₂.scr E₂.rdi (exs s₂ E₂.r8) E.x (by unfold oMq; omega) (c := .slot oQ) (K := word s.mem B (eW + oQ))
    ⟨by rw [m₂'], by unfold oQ; omega⟩ (by decide) (by decide) (by decide) (by decide) (by decide) rfl
    (by rw [(k₂.gpr (by decide) : s₂.gpr .r12 = _), (k₁.gpr (by decide) : s₁.gpr .r12 = _),
      (k₂.gpr (by decide) : s₂.gpr .r13 = _), (k₁.gpr (by decide) : s₁.gpr .r13 = _), h13, m₂']
        (try simp only [BitVec.toNat_zero]); omega)) fun s₃ ⟨a₃, m₃, k₃⟩ => ?_
  have E₃ := E₂.congr (k₃.mono (by decide))
  have m₃' : s₃.mem = s.mem := m₃.trans m₂'
  refine WP.mono (term2_ok E₃.scr E₃.rdi (eys s₃ E₃.r8 E₃.r9) E.y (by unfold oMr; omega) (c := .slot oR) (K := word s.mem B (eW + oR))
    ⟨by rw [m₃'], by unfold oR; omega⟩ (by decide) (by decide) (by decide) (by decide) (by decide) rfl
    (by rw [a₃, m₃', m₂', (k₂.gpr (by decide) : s₂.gpr .r12 = _), (k₁.gpr (by decide) : s₁.gpr .r12 = _),
      (k₂.gpr (by decide) : s₂.gpr .r13 = _), (k₁.gpr (by decide) : s₁.gpr .r13 = _), h13]
        (try simp only [BitVec.toNat_zero]); omega)) fun t ⟨a₄, m₄, k₄⟩ => ?_
  refine ⟨?_, ?_, m₄.trans m₃', ((k₁.trans k₂).trans (k₃.trans k₄)).mono (by decide)⟩
  · rw [(k₄.gpr (by decide) : t.gpr .r10 = _), (k₄.gpr (by decide) : t.gpr .r11 = _),
      (k₃.gpr (by decide) : s₃.gpr .r10 = _), (k₃.gpr (by decide) : s₃.gpr .r11 = _), a₂, m₁, a₁, h11]
    (try simp only [BitVec.toNat_zero]); omega
  · rw [a₄, a₃, m₃', m₂', (k₂.gpr (by decide) : s₂.gpr .r12 = _), (k₁.gpr (by decide) : s₁.gpr .r12 = _),
      (k₂.gpr (by decide) : s₂.gpr .r13 = _), (k₁.gpr (by decide) : s₁.gpr .r13 = _), h13]
    (try simp only [BitVec.toNat_zero]); omega

/-- `outS`: the previous word's top bits and `lo`'s low into `dst` (word `e` of the first row if
`y` is false, of the second if it is true), then `prev := lo`, `lo := hi`, `hi := 0`. -/
theorem outS_ok {s : State} {B : Addr} {Z e S : Nat} (hs : Scr s B Z) (y : Bool)
    (h8 : s.gpr .r8 = off B (e + 8)) (h9 : s.gpr .r9 = BitVec.ofNat 64 S)
    (hz : e + (if y then S else 0) + 8 ≤ Z) {prev lo hi : Reg}
    (a1 : prev ≠ .rax) (a2 : lo ≠ .rax) (a3 : hi ≠ .rax) (a4 : prev ≠ lo) (a5 : prev ≠ hi) (a6 : lo ≠ hi)
    (a7 : prev ≠ .r8) (a8 : lo ≠ .r8) (a9 : prev ≠ .r9) (a10 : lo ≠ .r9)
    (hk : writesOnly [.rax, prev, lo, hi] (.block (outS prev lo hi (if y then py (-8) else px (-8))))) :
    WP isa (.block (outS prev lo hi (if y then py (-8) else px (-8)))) s fun t =>
      t.mem = s.mem.writeW (off B (e + if y then S else 0)) (s.gpr prev >>> 59 + s.gpr lo <<< 5) ∧
      t.gpr prev = s.gpr lo ∧ t.gpr lo = s.gpr hi ∧ t.gpr hi = 0 ∧ Keep [.rax, prev, lo, hi] s t := by
  refine WP.mono (WP.keep [.rax, prev, lo, hi] (Q := fun t =>
      t.mem = s.mem.writeW (off B (e + if y then S else 0)) (s.gpr prev >>> 59 + s.gpr lo <<< 5) ∧
      t.gpr prev = s.gpr lo ∧ t.gpr lo = s.gpr hi ∧ t.gpr hi = 0) ?_ hk) fun t ⟨a, k⟩ => ⟨a.1, a.2.1, a.2.2.1, a.2.2.2, k⟩
  cases y with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hz ⊢
    unfold outS
    xrun [ea_px, h8, off_m8, hs.st (show e + 8 ≤ Z by omega), a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
      Ne.symm a1, Ne.symm a2, Ne.symm a3, Ne.symm a4, Ne.symm a5, Ne.symm a6, Ne.symm a7, Ne.symm a8,
      Ne.symm a9, Ne.symm a10]
    done
  | true =>
    simp only [↓reduceIte] at hz ⊢
    unfold outS
    xrun [ea_py, h8, h9, off_pym8, hs.st hz, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
      Ne.symm a1, Ne.symm a2, Ne.symm a3, Ne.symm a4, Ne.symm a5, Ne.symm a6, Ne.symm a7, Ne.symm a8,
      Ne.symm a9, Ne.symm a10]
    done

theorem off_beq {p : Addr} {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (off p a == off p b) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have h2 : BitVec.ofNat 64 a = BitVec.ofNat 64 b := by
      simp only [off] at h'; grind
    have := congrArg BitVec.toNat h2
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- `add r8, 8; cmp r8, r15`: the next word, and whether it is the end. -/
theorem next_ok {s : State} {B : Addr} {e N j : Nat} (h8 : s.gpr .r8 = off B (e + 8 * j))
    (h15 : s.gpr .r15 = off B (e + 8 * N)) (hN : e + 8 * N < 2 ^ 64) (hj : j + 1 ≤ N) :
    WP isa (.block next) s fun t =>
      t.zf = some (decide (j + 1 = N)) ∧ t.gpr .r8 = off B (e + 8 * (j + 1)) ∧ t.mem = s.mem ∧
      Keep [.r8] s t := by
  have e8 : off B (e + 8 * j) + 8 = off B (e + 8 * (j + 1)) := by
    rw [show e + 8 * (j + 1) = e + 8 * j + 8 by omega]
    simp only [off, BitVec.add_assoc, BitVec.ofNat_add]; rfl
  refine WP.mono (WP.keep [.r8] (Q := fun t =>
      t.zf = some (decide (j + 1 = N)) ∧ t.gpr .r8 = off B (e + 8 * (j + 1)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨a, k⟩ => ⟨a.1, a.2.1, a.2.2, k⟩
  unfold next
  xrun [h8, h15, sub_beq_zero]
  refine ⟨?_, e8⟩
  rw [e8, off_beq (show e + 8 * (j + 1) < 2 ^ 64 by omega) hN, decide_eq_decide]
  omega

/-! ## The arithmetic of `fgRow`'s columns -/

theorem div_step {X P k : Nat} :
    (X + 2 ^ (64 * (k + 1)) * P) / 2 ^ (64 * (k + 1)) = X / 2 ^ (64 * (k + 1)) + P := by
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]

/-- A column of `fgRow`: with `X' = X + 2^(64 (k + 1)) P` the sum over one more word and
`a = X / 2^(64 (k + 1)) + P` the accumulator, the stored words and the new low word `a mod 2^64`
hold `X' mod 2^(64 (k + 2))` shifted by 59. -/
theorem fg_arith {k X P D b : Nat} (hD : D + 2 ^ (64 * k) * (b / 2 ^ 59) = X % 2 ^ (64 * (k + 1)) / 2 ^ 59) :
    D + 2 ^ (64 * k) * (b / 2 ^ 59 + (X / 2 ^ (64 * (k + 1)) + P) % 2 ^ 64 % 2 ^ 59 * 32) +
      2 ^ (64 * (k + 1)) * ((X / 2 ^ (64 * (k + 1)) + P) % 2 ^ 64 / 2 ^ 59) =
      (X + 2 ^ (64 * (k + 1)) * P) % 2 ^ (64 * (k + 1 + 1)) / 2 ^ 59 := by
  generalize ha : (X / 2 ^ (64 * (k + 1)) + P) % 2 ^ 64 = b'
  have hm : (X + 2 ^ (64 * (k + 1)) * P) % 2 ^ (64 * (k + 1 + 1)) =
      X % 2 ^ (64 * (k + 1)) + 2 ^ (64 * (k + 1)) * b' := by
    rw [pow64_succ (k + 1), Nat.mod_mul, Nat.add_mul_mod_self_left, div_step, ha]
  rw [hm]
  generalize hL : X % 2 ^ (64 * (k + 1)) = L at hD ⊢
  rw [pow59 k]
  generalize hA : 2 ^ (64 * k) = A at hD ⊢
  rw [Nat.mul_assoc (2 ^ 59) (A * 32) b', Nat.add_mul_div_left _ _ (by decide : 0 < 2 ^ 59), ← hD]
  have := Nat.div_add_mod b' (2 ^ 59)
  grind

/-- `fg_arith` with the column's two words `lo:hi = acc + P`. -/
theorem col_update {k X P D b acc lo hi : Nat} (hD : D + 2 ^ (64 * k) * (b / 2 ^ 59) = X % 2 ^ (64 * (k + 1)) / 2 ^ 59)
    (hacc : acc = X / 2 ^ (64 * (k + 1))) (h2 : lo + 2 ^ 64 * hi = acc + P) (hlo : lo < 2 ^ 64) :
    D + 2 ^ (64 * k) * (b / 2 ^ 59 + lo % 2 ^ 59 * 32) + 2 ^ (64 * (k + 1)) * (lo / 2 ^ 59) =
      (X + 2 ^ (64 * (k + 1)) * P) % 2 ^ (64 * (k + 1 + 1)) / 2 ^ 59 ∧
    lo = (X + 2 ^ (64 * (k + 1)) * P) / 2 ^ (64 * (k + 1)) % 2 ^ 64 ∧
    hi = (X + 2 ^ (64 * (k + 1)) * P) / 2 ^ (64 * (k + 1 + 1)) := by
  have el : lo = (acc + P) % 2 ^ 64 := by omega
  have eh : hi = (acc + P) / 2 ^ 64 := by omega
  have ed := div_step (X := X) (P := P) (k := k)
  refine ⟨?_, ?_, ?_⟩
  · have := fg_arith (P := P) hD
    rw [← hacc, ← el] at this
    exact this
  · rw [ed, ← hacc, el]
  · rw [pow64_succ (k + 1), ← Nat.div_div_eq_div_mul, ed, ← hacc, eh]

/-! ## `fgRow` -/

/-- A row's data: the working space, the window `eW`, the first array `eA` (the second at
`eA + S`), `n`, and the memory at the row's start. -/
structure Rw where
  B : Addr
  Z : Nat
  eW : Nat
  eA : Nat
  S : Nat
  n : Nat
  m : Mem

namespace Rw

/-- The window's word at `o`. -/
abbrev c (R : Rw) (o : Nat) : BitVec 64 := word R.m R.B (R.eW + o)

/-- `|c₁| X' + |c₂| Y' + (|c₁| & m₁) + (|c₂| & m₂)` over the first `j` words of the arrays, `X'`
and `Y'` complemented under the masks: the sum a row's accumulator holds. -/
def sum (R : Rw) (c₁ m₁ c₂ m₂ : Nat) (j : Nat) : Nat :=
  (R.c c₁).toNat * wvM R.m R.B R.eA (R.c m₁) j + (R.c c₂).toNat * wvM R.m R.B (R.eA + R.S) (R.c m₂) j +
    ((R.c c₁ &&& R.c m₁) + (R.c c₂ &&& R.c m₂)).toNat

theorem sum_succ (R : Rw) (c₁ m₁ c₂ m₂ j : Nat) :
    R.sum c₁ m₁ c₂ m₂ (j + 1) = R.sum c₁ m₁ c₂ m₂ j + 2 ^ (64 * j) *
      ((R.c c₁).toNat * (word R.m R.B (R.eA + 8 * j) ^^^ R.c m₁).toNat +
        (R.c c₂).toNat * (word R.m R.B (R.eA + R.S + 8 * j) ^^^ R.c m₂).toNat) := by
  simp only [sum, wvM]
  grind

/-- The layout a row needs. -/
structure Ok (R : Rw) : Prop where
  win : R.eW + 96 ≤ R.eA
  len : 8 * (R.n + 1) ≤ R.S
  z : R.eA + 4 * R.S + 8 * (R.n + 1) ≤ R.Z
  n1 : 1 ≤ R.n
  nowrap : R.B.toNat + R.Z ≤ 2 ^ 64

end Rw

/-- After `k + 1` columns of `fgRow` (`k` words stored): the words, the previous low word
(`rbx`, `rbp`) and the accumulator (`r10`, `r12`) hold the sums. -/
structure FgInv (R : Rw) (s₀ : State) (k : Nat) (t : State) : Prop where
  scr : Scr t R.B R.Z
  keep : Keep [.rax, .rdx, .rbx, .rbp, .r8, .r10, .r11, .r12, .r13] s₀ t
  r8 : t.gpr .r8 = off R.B (R.eA + 8 * (k + 1))
  r11 : t.gpr .r11 = 0
  r13 : t.gpr .r13 = 0
  frm : Frm R.B [(R.eA, 8 * k), (R.eA + R.S, 8 * k)] R.m t.mem
  valF : wv t.mem R.B R.eA k + 2 ^ (64 * k) * ((t.gpr .rbx).toNat / 2 ^ 59) =
    R.sum oU oMu oV oMv (k + 1) % 2 ^ (64 * (k + 1)) / 2 ^ 59
  lowF : (t.gpr .rbx).toNat = R.sum oU oMu oV oMv (k + 1) / 2 ^ (64 * k) % 2 ^ 64
  accF : (t.gpr .r10).toNat = R.sum oU oMu oV oMv (k + 1) / 2 ^ (64 * (k + 1))
  valG : wv t.mem R.B (R.eA + R.S) k + 2 ^ (64 * k) * ((t.gpr .rbp).toNat / 2 ^ 59) =
    R.sum oQ oMq oR oMr (k + 1) % 2 ^ (64 * (k + 1)) / 2 ^ 59
  lowG : (t.gpr .rbp).toNat = R.sum oQ oMq oR oMr (k + 1) / 2 ^ (64 * k) % 2 ^ 64
  accG : (t.gpr .r12).toNat = R.sum oQ oMq oR oMr (k + 1) / 2 ^ (64 * (k + 1))

/-- What `fgRow`'s loop keeps from its start `s₀`. -/
structure RowStart (R : Rw) (s₀ : State) : Prop where
  ok : R.Ok
  rdi : s₀.gpr .rdi = off R.B R.eW
  r9 : s₀.gpr .r9 = BitVec.ofNat 64 R.S
  r15 : s₀.gpr .r15 = off R.B (R.eA + 8 * (R.n + 1))
  rcx : s₀.gpr .rcx = R.c oU
  r14 : s₀.gpr .r14 = R.c oV
  huv : (R.c oU).toNat + (R.c oV).toNat ≤ 2 ^ 59
  hqr : (R.c oQ).toNat + (R.c oR).toNat ≤ 2 ^ 59

theorem FgInv.word {R : Rw} {s₀ t : State} {k : Nat} (h : FgInv R s₀ k t) (hR : R.Ok) {d : Nat}
    (hd : d + 8 ≤ R.eA ∨ (R.eA + 8 * k ≤ d ∧ d + 8 ≤ R.eA + R.S) ∨ R.eA + R.S + 8 * k ≤ d)
    (hz : d + 8 ≤ R.Z) : word t.mem R.B d = word R.m R.B d :=
  h.frm.word_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have := hR.len; have := hR.z; rcases hr with rfl | rfl <;> dsimp only <;> omega) (by have := hR.nowrap; omega)

/-- A column of `fgRow`'s loop, `k + 1 ≤ n`. -/
theorem fgStep_ok {R : Rw} {s₀ : State} (h₀ : RowStart R s₀) {k : Nat} (hk : k + 1 ≤ R.n) {t : State}
    (hI : FgInv R s₀ k t) :
    WP isa (.block (fgCol ++ outS .rbx .r10 .r11 (px (-8)) ++ outS .rbp .r12 .r13 (py (-8)) ++ next)) t
      fun t' => t'.zf = some (decide (k + 1 + 1 = R.n + 1)) ∧ FgInv R s₀ (k + 1) t' := by
  have hR := h₀.ok
  have hN := hR.nowrap; have hW := hR.win; have hL := hR.len; have hz := hR.z
  have tdi : t.gpr .rdi = off R.B R.eW := (hI.keep.gpr (by decide)).trans h₀.rdi
  have t9 : t.gpr .r9 = BitVec.ofNat 64 R.S := (hI.keep.gpr (by decide)).trans h₀.r9
  have E : ColEnv t R.B R.Z R.eW (R.eA + 8 * (k + 1)) R.S :=
    ⟨hI.scr, tdi, hI.r8, t9, by omega, by omega, by omega⟩
  have wc : ∀ o, o + 8 ≤ 96 → word t.mem R.B (R.eW + o) = R.c o := fun o ho =>
    hI.word hR (.inl (by omega)) (by omega)
  have wx : word t.mem R.B (R.eA + 8 * (k + 1)) = word R.m R.B (R.eA + 8 * (k + 1)) :=
    hI.word hR (.inr (.inl ⟨by omega, by omega⟩)) (by omega)
  have wy : word t.mem R.B (R.eA + 8 * (k + 1) + R.S) = word R.m R.B (R.eA + R.S + 8 * (k + 1)) := by
    rw [show R.eA + 8 * (k + 1) + R.S = R.eA + R.S + 8 * (k + 1) by omega]
    exact hI.word hR (.inr (.inr (by omega))) (by omega)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (fgCol_ok E ((hI.keep.gpr (by decide)).trans h₀.rcx) ((hI.keep.gpr (by decide)).trans h₀.r14)
    h₀.huv (by rw [wc oQ (by unfold oQ; omega), wc oR (by unfold oR; omega)]; exact h₀.hqr) hI.r11 hI.r13)
    fun s₁ ⟨aF, aG, m₁, k₁⟩ => ?_
  rw [wc oMu (by unfold oMu; omega), wc oMv (by unfold oMv; omega), wc oQ (by unfold oQ; omega),
    wc oMq (by unfold oMq; omega), wc oR (by unfold oR; omega), wc oMr (by unfold oMr; omega), wx, wy] at *
  have s8 : s₁.gpr .r8 = off R.B (R.eA + 8 * k + 8) := by
    rw [(k₁.gpr (by decide) : s₁.gpr .r8 = _), hI.r8, show R.eA + 8 * (k + 1) = R.eA + 8 * k + 8 by omega]
  have s9 : s₁.gpr .r9 = BitVec.ofNat 64 R.S := (k₁.gpr (by decide)).trans t9
  rw [WP.block_append_iff]
  refine WP.mono (outS_ok (hI.scr.congr k₁.2.2) false s8 s9 (by simp only [Bool.false_eq_true, ↓reduceIte]; omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) rfl) fun s₂ ⟨m₂, p₂, l₂, h₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (outS_ok (hI.scr.congr (k₂.2.2.trans k₁.2.2)) true
    ((k₂.gpr (by decide)).trans s8) ((k₂.gpr (by decide)).trans s9) (by simp only [↓reduceIte]; omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) rfl) fun s₃ ⟨m₃, p₃, l₃, h₃, k₃⟩ => ?_
  refine WP.mono (next_ok (B := R.B) (e := R.eA) (N := R.n + 1) (j := k + 1) (by rw [((k₂.trans k₃).gpr (by decide)), s8,
      show R.eA + 8 * k + 8 = R.eA + 8 * (k + 1) by omega])
    (by rw [(((k₁.trans k₂).trans k₃).gpr (by decide)), (hI.keep.gpr (by decide)), h₀.r15])
    (by omega) (by omega)) fun t' ⟨z', r8', m', k'⟩ => ⟨z', ?_⟩
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at m₂
  simp only [↓reduceIte] at m₃
  have bx₁ : s₁.gpr .rbx = t.gpr .rbx := k₁.gpr (by decide)
  have bp₁ : s₁.gpr .rbp = t.gpr .rbp := k₁.gpr (by decide)
  have hmt : t'.mem = (t.mem.writeW (off R.B (R.eA + 8 * k)) (t.gpr .rbx >>> 59 + s₁.gpr .r10 <<< 5)).writeW
      (off R.B (R.eA + R.S + 8 * k)) (t.gpr .rbp >>> 59 + s₁.gpr .r12 <<< 5) := by
    rw [m', m₃, m₂, m₁, (k₂.gpr (by decide) : s₂.gpr .rbp = _), (k₂.gpr (by decide) : s₂.gpr .r12 = _), bx₁, bp₁,
      Nat.add_right_comm R.eA (8 * k) R.S]
  have F := col_update (P := (R.c oU).toNat * (word R.m R.B (R.eA + 8 * (k + 1)) ^^^ R.c oMu).toNat +
      (R.c oV).toNat * (word R.m R.B (R.eA + R.S + 8 * (k + 1)) ^^^ R.c oMv).toNat) hI.valF hI.accF
    (by rw [aF]; omega) (s₁.gpr .r10).isLt
  have G := col_update (P := (R.c oQ).toNat * (word R.m R.B (R.eA + 8 * (k + 1)) ^^^ R.c oMq).toNat +
      (R.c oR).toNat * (word R.m R.B (R.eA + R.S + 8 * (k + 1)) ^^^ R.c oMr).toNat) hI.valG hI.accG
    (by rw [aG]; omega) (s₁.gpr .r12).isLt
  rw [← Rw.sum_succ] at F G
  have kk := (((k₁.trans k₂).trans k₃).trans k')
  have oW₁ := writeW_outside t.mem R.B (t.gpr .rbx >>> 59 + s₁.gpr .r10 <<< 5) (d := R.eA + 8 * k) (by omega)
  have oW₂ := writeW_outside (t.mem.writeW (off R.B (R.eA + 8 * k)) (t.gpr .rbx >>> 59 + s₁.gpr .r10 <<< 5)) R.B
    (t.gpr .rbp >>> 59 + s₁.gpr .r12 <<< 5) (d := R.eA + R.S + 8 * k) (by omega)
  refine ⟨hI.scr.congr kk.2.2, (hI.keep.trans kk).mono (by decide), r8', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(k'.gpr (by decide) : t'.gpr .r11 = _), (k₃.gpr (by decide) : s₃.gpr .r11 = _), h₂]
  · rw [(k'.gpr (by decide) : t'.gpr .r13 = _), h₃]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    rw [hmt, oW₂ x (by omega), oW₁ x (by omega)]
    exact hI.frm x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
  · rw [hmt, oW₂.wv (.inl (by omega)) (by omega), wv_writeW_top _ _ _ _ _ (by omega), shr59_word,
      (k'.gpr (by decide) : t'.gpr .rbx = _), (k₃.gpr (by decide) : s₃.gpr .rbx = _), p₂, ← F.1]
  · rw [(k'.gpr (by decide) : t'.gpr .rbx = _), (k₃.gpr (by decide) : s₃.gpr .rbx = _), p₂]; exact F.2.1
  · rw [(k'.gpr (by decide) : t'.gpr .r10 = _), (k₃.gpr (by decide) : s₃.gpr .r10 = _), l₂]; exact F.2.2
  · rw [hmt, wv_writeW_top _ _ _ _ _ (by omega), (oW₁.wv (.inr (by omega)) (by omega)), shr59_word,
      (k'.gpr (by decide) : t'.gpr .rbp = _), p₃, (k₂.gpr (by decide) : s₂.gpr .r12 = _), ← G.1]
  · rw [(k'.gpr (by decide) : t'.gpr .rbp = _), p₃, (k₂.gpr (by decide) : s₂.gpr .r12 = _)]; exact G.2.1
  · rw [(k'.gpr (by decide) : t'.gpr .r12 = _), l₃, (k₂.gpr (by decide) : s₂.gpr .r13 = _)]; exact G.2.2

/-- `ones`: `lo := (c₁ & m₁) + (c₂ & m₂)` from the window. -/
theorem ones_ok {s : State} {B : Addr} {Z eW : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = off B eW)
    (hW : eW + 96 ≤ Z) {cu mu cv mv : Nat} (h1 : cu + 8 ≤ 96) (h2 : mu + 8 ≤ 96) (h3 : cv + 8 ≤ 96)
    (h4 : mv + 8 ≤ 96) {lo : Reg} (hl : lo ≠ .rax) (hl' : lo ≠ .rdi)
    (hk : writesOnly [.rax, lo] (.block (ones cu mu cv mv lo)) = true) :
    WP isa (.block (ones cu mu cv mv lo)) s fun t =>
      t.gpr lo = (word s.mem B (eW + cu) &&& word s.mem B (eW + mu)) +
        (word s.mem B (eW + cv) &&& word s.mem B (eW + mv)) ∧ t.mem = s.mem ∧ Keep [.rax, lo] s t := by
  refine WP.mono (WP.keep [.rax, lo] (Q := fun t =>
      t.gpr lo = (word s.mem B (eW + cu) &&& word s.mem B (eW + mu)) +
        (word s.mem B (eW + cv) &&& word s.mem B (eW + mv)) ∧ t.mem = s.mem) ?_ hk)
    fun t ⟨a, k⟩ => ⟨a.1, a.2, k⟩
  unfold ones
  xrun [ea_wm, hdi, offD, hs.ld (show eW + cu + 8 ≤ Z by omega), hs.ld (show eW + mu + 8 ≤ Z by omega),
    hs.ld (show eW + cv + 8 ≤ Z by omega), hs.ld (show eW + mv + 8 ≤ Z by omega), hl, hl', Ne.symm hl, Ne.symm hl']

/-- `rowStart k`: `r8` to array `16 + k`, `r15` from `n` to its word `n + 1`. -/
theorem rowStart_ok {s : State} {B : Addr} {w n : Nat} (k : Nat) (hdi : s.gpr .rdi = off B (slot w 16))
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))) (h15 : s.gpr .r15 = BitVec.ofNat 64 n) :
    WP isa (.block (rowStart k)) s fun t =>
      t.gpr .r8 = off B (slot w (16 + k)) ∧ t.gpr .r15 = off B (slot w (16 + k) + 8 * (n + 1)) ∧ t.mem = s.mem ∧
      Keep [.r8, .r15] s t := by
  unfold rowStart
  rw [WP.block_append_iff]
  refine WP.mono (wa_ok k (r := .r8) (by decide) hdi h9) fun s₁ ⟨a₁, m₁, k₁⟩ => ?_
  refine WP.mono (WP.keep [.r15] (Q := fun t => t.gpr .r15 = off B (slot w (16 + k) + 8 * (n + 1)) ∧
    t.mem = s₁.mem ∧ t.gpr .r8 = s₁.gpr .r8) ?_ rfl) fun t ⟨⟨a, m, r8⟩, kt⟩ =>
    ⟨r8.trans a₁, a, m.trans m₁, (k₁.trans kt).mono (by decide)⟩
  have h15₁ : s₁.gpr .r15 = BitVec.ofNat 64 n := (k₁.gpr (by decide)).trans h15
  xrun [h15₁, a₁]
  have e : (BitVec.ofNat 64 n + 1) <<< 3 = BitVec.ofNat 64 (8 * (n + 1)) := by
    apply BitVec.eq_of_toNat_eq
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftLeft_eq, h1]
    omega
  rw [e]
  simp only [off, BitVec.ofNat_add]
  grind

/-- The row of `(f, g)` for the window at `slot w 16` and `n`. -/
def fgR (B : Addr) (Z w n : Nat) (m : Mem) : Rw := ⟨B, Z, slot w 16, slot w 19, 8 * (w + 2), n, m⟩

/-- `fgRow`'s setup: the bases, `|u|` and `|v|`, and the accumulators' start. -/
theorem fgSetup_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = off B (slot w 16)) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (h15 : s.gpr .r15 = BitVec.ofNat 64 n) (hW : slot w 16 + 96 ≤ Z) :
    WP isa (.block (rowStart 3 ++ ([.mov .rcx (.mem (wm oU)), .mov .r14 (.mem (wm oV))] : List Instr) ++
      ones oU oMu oV oMv .r10 ++ ([.mov32 .r11 (.imm 0)] : List Instr) ++
      ones oQ oMq oR oMr .r12 ++ ([.mov32 .r13 (.imm 0)] : List Instr))) s fun t =>
      t.gpr .r8 = off B (slot w 19) ∧ t.gpr .r15 = off B (slot w 19 + 8 * (n + 1)) ∧
      t.gpr .rcx = (fgR B Z w n s.mem).c oU ∧ t.gpr .r14 = (fgR B Z w n s.mem).c oV ∧
      t.gpr .r10 = ((fgR B Z w n s.mem).c oU &&& (fgR B Z w n s.mem).c oMu) +
        ((fgR B Z w n s.mem).c oV &&& (fgR B Z w n s.mem).c oMv) ∧ t.gpr .r11 = 0 ∧
      t.gpr .r12 = ((fgR B Z w n s.mem).c oQ &&& (fgR B Z w n s.mem).c oMq) +
        ((fgR B Z w n s.mem).c oR &&& (fgR B Z w n s.mem).c oMr) ∧ t.gpr .r13 = 0 ∧
      t.mem = s.mem ∧ Keep [.rax, .rcx, .r8, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (rowStart_ok 3 hdi h9 h15) fun s₁ ⟨a₁, b₁, m₁, k₁⟩ => ?_
  have hs₁ := hs.congr k₁.2.2
  have di₁ : s₁.gpr .rdi = off B (slot w 16) := (k₁.gpr (by decide)).trans hdi
  rw [show ∀ l : List Instr, ([Instr.mov .rcx (.mem (wm oU)), .mov .r14 (.mem (wm oV))] ++ l) =
    [Instr.mov .rcx (.mem (wm oU)), .mov .r14 (.mem (wm oV))] ++ l from fun _ => rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.rcx, .r14] (Q := fun t => t.gpr .rcx = word s.mem B (slot w 16 + oU) ∧
    t.gpr .r14 = word s.mem B (slot w 16 + oV) ∧ t.mem = s₁.mem) (by
      xrun [ea_wm, di₁, offD, hs₁.ld (show slot w 16 + oU + 8 ≤ Z by unfold oU; omega),
        hs₁.ld (show slot w 16 + oV + 8 ≤ Z by unfold oV; omega), m₁]) rfl)
    fun s₂ ⟨⟨a₂, b₂, m₂⟩, k₂⟩ => ?_
  have hs₂ := hs₁.congr k₂.2.2
  have di₂ : s₂.gpr .rdi = off B (slot w 16) := (k₂.gpr (by decide)).trans di₁
  rw [WP.block_append_iff]
  refine WP.mono (ones_ok hs₂ di₂ hW (cu := oU) (mu := oMu) (cv := oV) (mv := oMv) (by decide) (by decide)
    (by decide) (by decide) (lo := .r10) (by decide) (by decide) rfl) fun s₃ ⟨a₃, m₃, k₃⟩ => ?_
  rw [show ∀ l : List Instr, ([Instr.mov32 .r11 (.imm 0)] ++ l) = [Instr.mov32 .r11 (.imm 0)] ++ l from fun _ => rfl,
    WP.block_append_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = 0 ∧ t.mem = s₃.mem) (by xrun) rfl)
    fun s₄ ⟨⟨a₄, m₄⟩, k₄⟩ => ?_
  have hs₄ := (hs₂.congr k₃.2.2).congr k₄.2.2
  have di₄ : s₄.gpr .rdi = off B (slot w 16) := ((k₃.trans k₄).gpr (by decide)).trans di₂
  rw [WP.block_append_iff]
  refine WP.mono (ones_ok hs₄ di₄ hW (cu := oQ) (mu := oMq) (cv := oR) (mv := oMr) (by decide) (by decide)
    (by decide) (by decide) (lo := .r12) (by decide) (by decide) rfl) fun s₅ ⟨a₅, m₅, k₅⟩ => ?_
  refine WP.mono (WP.keep [.r13] (Q := fun t => t.gpr .r13 = 0 ∧ t.mem = s₅.mem) (by xrun) rfl)
    fun t ⟨⟨a₆, m₆⟩, k₆⟩ => ?_
  have mm : t.mem = s.mem := by rw [m₆, m₅, m₄, m₃, m₂, m₁]
  have m₄' : s₄.mem = s.mem := by rw [m₄, m₃, m₂, m₁]
  have m₂' : s₂.mem = s.mem := by rw [m₂, m₁]
  have kk := (((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, a₆, mm, kk.mono (by decide)⟩
  · rw [((((k₂.trans k₃).trans k₄).trans k₅).trans k₆).gpr (by decide), a₁]
  · rw [((((k₂.trans k₃).trans k₄).trans k₅).trans k₆).gpr (by decide), b₁]
  · rw [((((k₃.trans k₄).trans k₅).trans k₆)).gpr (by decide), a₂]; rfl
  · rw [((((k₃.trans k₄).trans k₅).trans k₆)).gpr (by decide), b₂]; rfl
  · rw [((k₄.trans k₅).trans k₆).gpr (by decide), a₃, m₂']; rfl
  · rw [(k₅.trans k₆).gpr (by decide), a₄]
  · rw [k₆.gpr (by decide), a₅, m₄']; rfl

theorem sum_zero (R : Rw) (c₁ m₁ c₂ m₂ : Nat) :
    R.sum c₁ m₁ c₂ m₂ 0 = ((R.c c₁ &&& R.c m₁) + (R.c c₂ &&& R.c m₂)).toNat := by
  simp [Rw.sum, wvM]

/-- `fgRow`'s first block: the setup and column 0; then the loop's invariant at its start. -/
theorem fgPre_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = off B (slot w 16)) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (h15 : s.gpr .r15 = BitVec.ofNat 64 n) (hR : (fgR B Z w n s.mem).Ok)
    (huv : ((fgR B Z w n s.mem).c oU).toNat + ((fgR B Z w n s.mem).c oV).toNat ≤ 2 ^ 59)
    (hqr : ((fgR B Z w n s.mem).c oQ).toNat + ((fgR B Z w n s.mem).c oR).toNat ≤ 2 ^ 59) :
    WP isa (.block (rowStart 3 ++ ([.mov .rcx (.mem (wm oU)), .mov .r14 (.mem (wm oV))] : List Instr) ++
      ones oU oMu oV oMv .r10 ++ ([.mov32 .r11 (.imm 0)] : List Instr) ++
      ones oQ oMq oR oMr .r12 ++ ([.mov32 .r13 (.imm 0)] : List Instr) ++ fgCol ++
      ([.mov .rbx (.reg .r10), .mov .r10 (.reg .r11), .mov32 .r11 (.imm 0), .mov .rbp (.reg .r12),
        .mov .r12 (.reg .r13), .mov32 .r13 (.imm 0), .alu .add .r8 (.imm 8)] : List Instr))) s fun t =>
      RowStart (fgR B Z w n s.mem) t ∧ FgInv (fgR B Z w n s.mem) t 0 t ∧
      Keep [.rax, .rdx, .rcx, .rbx, .rbp, .r8, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have hN := hR.nowrap; have hW := hR.win; have hL := hR.len; have hz := hR.z
  simp only [fgR] at hW hL hz
  rw [show ∀ (a b c d e f g h : List Instr), a ++ b ++ c ++ d ++ e ++ f ++ g ++ h =
    (a ++ b ++ c ++ d ++ e ++ f) ++ (g ++ h) from fun _ _ _ _ _ _ _ _ => by simp only [List.append_assoc],
    WP.block_append_iff]
  refine WP.mono (fgSetup_ok hs hdi h9 h15 (by omega)) fun s₁ ⟨r8₁, r15₁, cx₁, r14₁, r10₁, r11₁, r12₁, r13₁, m₁, k₁⟩ => ?_
  have hs₁ := hs.congr k₁.2.2
  have E : ColEnv s₁ B Z (slot w 16) (slot w 19) (8 * (w + 2)) :=
    ⟨hs₁, (k₁.gpr (by decide)).trans hdi, r8₁, (k₁.gpr (by decide)).trans h9, by omega, by omega, by omega⟩
  rw [WP.block_append_iff]
  refine WP.mono (fgCol_ok E cx₁ r14₁ huv (by rw [m₁]; exact hqr) r11₁ r13₁) fun s₂ ⟨aF, aG, m₂, k₂⟩ => ?_
  have r8₂ : s₂.gpr .r8 = off B (slot w 19) := (k₂.gpr (by decide)).trans r8₁
  refine WP.mono (WP.keep [.rbx, .r10, .r11, .rbp, .r12, .r13, .r8] (Q := fun t =>
    t.gpr .rbx = s₂.gpr .r10 ∧ t.gpr .r10 = s₂.gpr .r11 ∧ t.gpr .r11 = 0 ∧ t.gpr .rbp = s₂.gpr .r12 ∧
    t.gpr .r12 = s₂.gpr .r13 ∧ t.gpr .r13 = 0 ∧ t.gpr .r8 = off B (slot w 19 + 8 * (0 + 1)) ∧ t.mem = s₂.mem)
    (by
      xrun [r8₂]
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add]; rfl) rfl)
    fun t ⟨⟨bx, r10, r11, bp, r12, r13, r8, mt⟩, kt⟩ => ?_
  have mt' : t.mem = s.mem := by rw [mt, m₂, m₁]
  have kk := (k₁.trans k₂).trans kt
  rw [m₁, r10₁] at aF
  rw [m₁, r12₁] at aG
  have z0 : (0 : BitVec 64).toNat = 0 := rfl
  have eF : (fgR B Z w n s.mem).sum oU oMu oV oMv 1 = (s₂.gpr .r10).toNat + 2 ^ 64 * (s₂.gpr .r11).toNat := by
    rw [show (1 : Nat) = 0 + 1 from rfl, Rw.sum_succ, sum_zero]
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.add_zero, fgR, Rw.c] at aF ⊢; omega
  have eG : (fgR B Z w n s.mem).sum oQ oMq oR oMr 1 = (s₂.gpr .r12).toNat + 2 ^ 64 * (s₂.gpr .r13).toNat := by
    rw [show (1 : Nat) = 0 + 1 from rfl, Rw.sum_succ, sum_zero]
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.add_zero, fgR, Rw.c] at aG ⊢; omega
  have l10 := (s₂.gpr .r10).isLt
  have l12 := (s₂.gpr .r12).isLt
  refine ⟨⟨hR, (kk.gpr (by decide)).trans hdi, (kk.gpr (by decide)).trans h9, ?_, ?_, ?_, huv, hqr⟩,
    ⟨hs.congr kk.2.2, Keep.refl _ _, r8, r11, r13, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, kk.mono (by decide)⟩
  · rw [(k₂.trans kt).gpr (by decide), r15₁]; rfl
  · rw [(k₂.trans kt).gpr (by decide), cx₁]
  · rw [(k₂.trans kt).gpr (by decide), r14₁]
  · rw [mt']; exact Frm.refl _ _ _
  · rw [bx]; simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.zero_add, Nat.mul_one, eF]
    omega
  · rw [bx]; simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.zero_add, eF]; omega
  · rw [r10]; simp only [Nat.zero_add, Nat.mul_one, eF]; omega
  · rw [bp]; simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.zero_add, Nat.mul_one, eG]
    omega
  · rw [bp]; simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.zero_add, eG]; omega
  · rw [r12]; simp only [Nat.zero_add, Nat.mul_one, eG]; omega

/-- `outTop`: `prev`'s top bits and those of its sign word into `dst`. -/
theorem outTop_ok {s : State} {B : Addr} {Z e S : Nat} (hs : Scr s B Z) (y : Bool)
    (h8 : s.gpr .r8 = off B (e + 8)) (h9 : s.gpr .r9 = BitVec.ofNat 64 S)
    (hz : e + (if y then S else 0) + 8 ≤ Z) {prev : Reg} (a1 : prev ≠ .rax) (a2 : prev ≠ .rdx)
    (hk : writesOnly [.rax, .rdx] (.block (outTop prev (if y then py (-8) else px (-8))))) :
    WP isa (.block (outTop prev (if y then py (-8) else px (-8)))) s fun t =>
      t.mem = s.mem.writeW (off B (e + if y then S else 0))
        (s.gpr prev >>> 59 + (BitVec.setWidth 64 (0 : BitVec 32) - s.gpr prev >>> 63) <<< 5) ∧
      Keep [.rax, .rdx] s t := by
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t =>
      t.mem = s.mem.writeW (off B (e + if y then S else 0))
        (s.gpr prev >>> 59 + (BitVec.setWidth 64 (0 : BitVec 32) - s.gpr prev >>> 63) <<< 5)) ?_ hk)
    fun t ⟨a, k⟩ => ⟨a, k⟩
  cases y with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hz ⊢
    unfold outTop
    xrun [ea_px, h8, off_m8, hs.st (show e + 8 ≤ Z by omega), a1, a2, Ne.symm a1, Ne.symm a2]
  | true =>
    simp only [↓reduceIte] at hz ⊢
    unfold outTop
    xrun [ea_py, h8, h9, off_pym8, hs.st hz, a1, a2, Ne.symm a1, Ne.symm a2]

/-- `rowEnd k`: `r15` back to `n` from the end of array `16 + k`'s first `n + 1` words. -/
theorem rowEnd_ok {s : State} {B : Addr} {w n : Nat} (k : Nat) (hdi : s.gpr .rdi = off B (slot w 16))
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (h15 : s.gpr .r15 = off B (slot w (16 + k) + 8 * (n + 1))) (hn : 8 * (n + 1) < 2 ^ 64) :
    WP isa (.block (rowEnd k)) s fun t =>
      t.gpr .r15 = BitVec.ofNat 64 n ∧ t.mem = s.mem ∧ Keep [.rax, .r15] s t := by
  unfold rowEnd
  rw [WP.block_append_iff]
  refine WP.mono (wa_ok k (r := .rax) (by decide) hdi h9) fun s₁ ⟨a₁, m₁, k₁⟩ => ?_
  refine WP.mono (WP.keep [.r15] (Q := fun t => t.gpr .r15 = BitVec.ofNat 64 n ∧ t.mem = s₁.mem) ?_ rfl)
    fun t ⟨⟨a, m⟩, kt⟩ => ⟨a, m.trans m₁, (k₁.trans kt).mono (by decide)⟩
  have h15₁ : s₁.gpr .r15 = off B (slot w (16 + k) + 8 * (n + 1)) := (k₁.gpr (by decide)).trans h15
  xrun [h15₁, a₁]
  have e : off B (slot w (16 + k) + 8 * (n + 1)) - off B (slot w (16 + k)) = BitVec.ofNat 64 (8 * (n + 1)) := by
    simp only [off, BitVec.ofNat_add]; grind
  rw [e]
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  simp only [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, h1]
  omega

/-- `V / 2^59` with `V`'s sign word above it, modulo `2^(64 (n + 1))`: the shift of a number of
`n + 1` words as a signed number. -/
def shrS (n V : Nat) : Nat :=
  (V + 2 ^ (64 * (n + 1)) * (if 2 ^ (64 * n) * 2 ^ 63 ≤ V then 2 ^ 64 - 1 else 0)) / 2 ^ 59 % 2 ^ (64 * (n + 1))

/-- The last word of `fgRow`: with `x` the top word of `V`, the stored words and the word of `x`
and its sign hold `shrS n V`. -/
theorem top_arith {n D V : Nat} {x : BitVec 64} (hV : V < 2 ^ (64 * (n + 1))) (hx : x.toNat = V / 2 ^ (64 * n))
    (hD : D + 2 ^ (64 * n) * (x.toNat / 2 ^ 59) = V / 2 ^ 59) :
    D + 2 ^ (64 * n) * (x >>> 59 + (BitVec.setWidth 64 (0 : BitVec 32) - x >>> 63) <<< 5).toNat = shrS n V := by
  rw [shr59_word, maskOf_toNat, Nat.mul_add, ← Nat.add_assoc, hD, shrS, shr_top hV]
  congr 3
  unfold signW
  have e : (2 ^ 63 ≤ x.toNat) ↔ (2 ^ (64 * n) * 2 ^ 63 ≤ V) := by
    rw [hx, Nat.le_div_iff_mul_le (Nat.two_pow_pos _), Nat.mul_comm]
  by_cases h : 2 ^ (64 * n) * 2 ^ 63 ≤ V
  · simp only [e.mpr h, h, ↓reduceIte]
  · simp only [show ¬ 2 ^ 63 ≤ x.toNat from fun h' => h (e.mp h'), h, ↓reduceIte]

theorem top_word (X n : Nat) : X / 2 ^ (64 * n) % 2 ^ 64 = X % 2 ^ (64 * (n + 1)) / 2 ^ (64 * n) := by
  rw [pow64_succ, Nat.mod_mul_right_div_self]

theorem low_eq (X n : Nat) : X % 2 ^ (64 * (n + 1)) % 2 ^ (64 * (n + 1)) = X % 2 ^ (64 * (n + 1)) := Nat.mod_mod _ _

/-- `fgRow`: `(f, g)` replaced by the shifts of the two sums over their `n + 1` words. -/
theorem fgRow_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = off B (slot w 16)) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (h15 : s.gpr .r15 = BitVec.ofNat 64 n) (hR : (fgR B Z w n s.mem).Ok)
    (huv : ((fgR B Z w n s.mem).c oU).toNat + ((fgR B Z w n s.mem).c oV).toNat ≤ 2 ^ 59)
    (hqr : ((fgR B Z w n s.mem).c oQ).toNat + ((fgR B Z w n s.mem).c oR).toNat ≤ 2 ^ 59) :
    WP isa (seqs fgRow) s fun t =>
      wv t.mem B (slot w 19) (n + 1) =
        shrS n ((fgR B Z w n s.mem).sum oU oMu oV oMv (n + 1) % 2 ^ (64 * (n + 1))) ∧
      wv t.mem B (slot w 19 + 8 * (w + 2)) (n + 1) =
        shrS n ((fgR B Z w n s.mem).sum oQ oMq oR oMr (n + 1) % 2 ^ (64 * (n + 1))) ∧
      Frm B [(slot w 19, 8 * (n + 1)), (slot w 19 + 8 * (w + 2), 8 * (n + 1))] s.mem t.mem ∧
      t.gpr .r15 = BitVec.ofNat 64 n ∧
      Keep [.rax, .rdx, .rcx, .rbx, .rbp, .r8, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have hN := hR.nowrap; have hW := hR.win; have hL := hR.len; have hz := hR.z; have hn1 := hR.n1
  simp only [fgR] at hW hL hz hN hn1
  have e19 : slot w 19 = slot w 16 + 24 * (w + 2) := by unfold slot; omega
  unfold fgRow
  simp only [seqs]
  refine WP.seq (WP.mono (fgPre_ok hs hdi h9 h15 hR huv hqr) fun t₁ ⟨h₀, I₀, k₁⟩ => ?_)
  refine WP.seq (WP.mono (wp_upto (a := 1) (N := n + 1) (by omega)
    (fun j t => ∃ k, j = k + 1 ∧ FgInv (fgR B Z w n s.mem) t₁ k t)
    (fun j hj hjN t ⟨k, hk, hI⟩ => by
      subst hk
      exact WP.mono (fgStep_ok h₀ (show k + 1 ≤ n by omega) hI) fun t' ⟨z, h⟩ => ⟨z, k + 1, rfl, h⟩)
    (fun t h => h) ⟨0, rfl, I₀⟩) fun t₂ ⟨k, hk, I⟩ => ?_)
  rw [show k = n by omega] at I
  have hs₂ := I.scr
  have r9₂ : t₂.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) := (I.keep.gpr (by decide)).trans h₀.r9
  have di₂ : t₂.gpr .rdi = off B (slot w 16) := (I.keep.gpr (by decide)).trans h₀.rdi
  have r8₂ : t₂.gpr .r8 = off B (slot w 19 + 8 * n + 8) := by
    rw [I.r8]; simp only [fgR]; rw [show slot w 19 + 8 * (n + 1) = slot w 19 + 8 * n + 8 by omega]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (outTop_ok hs₂ false r8₂ r9₂ (by simp only [Bool.false_eq_true, ↓reduceIte, fgR]; omega)
    (prev := .rbx) (by decide) (by decide) rfl) fun t₃ ⟨m₃, k₃⟩ => ?_
  refine WP.mono (outTop_ok (hs₂.congr k₃.2.2) true ((k₃.gpr (by decide)).trans r8₂) ((k₃.gpr (by decide)).trans r9₂)
    (by simp only [↓reduceIte, fgR]; omega) (prev := .rbp) (by decide) (by decide) rfl) fun t₄ ⟨m₄, k₄⟩ => ?_
  refine WP.mono (rowEnd_ok (n := n) 3 ((k₃.trans k₄).gpr (by decide) |>.trans di₂) ((k₃.trans k₄).gpr (by decide) |>.trans r9₂)
    (by rw [((k₃.trans k₄).gpr (by decide)), (I.keep.gpr (by decide)), h₀.r15]; rfl) (by omega))
    fun t ⟨r15t, mt, kt⟩ => ?_
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at m₃
  simp only [↓reduceIte] at m₄
  have bp₃ : t₃.gpr .rbp = t₂.gpr .rbp := k₃.gpr (by decide)
  have hm : t.mem = (t₂.mem.writeW (off B (slot w 19 + 8 * n)) (t₂.gpr .rbx >>> 59 +
      (BitVec.setWidth 64 (0 : BitVec 32) - t₂.gpr .rbx >>> 63) <<< 5)).writeW (off B (slot w 19 + 8 * (w + 2) + 8 * n))
      (t₂.gpr .rbp >>> 59 + (BitVec.setWidth 64 (0 : BitVec 32) - t₂.gpr .rbp >>> 63) <<< 5) := by
    rw [mt, m₄, m₃, bp₃, Nat.add_right_comm (slot w 19) (8 * n) (8 * (w + 2))]; rfl
  have oW₁ := writeW_outside t₂.mem B (t₂.gpr .rbx >>> 59 +
      (BitVec.setWidth 64 (0 : BitVec 32) - t₂.gpr .rbx >>> 63) <<< 5) (d := slot w 19 + 8 * n) (by omega)
  have oW₂ := writeW_outside (t₂.mem.writeW (off B (slot w 19 + 8 * n)) (t₂.gpr .rbx >>> 59 +
      (BitVec.setWidth 64 (0 : BitVec 32) - t₂.gpr .rbx >>> 63) <<< 5)) B
      (t₂.gpr .rbp >>> 59 + (BitVec.setWidth 64 (0 : BitVec 32) - t₂.gpr .rbp >>> 63) <<< 5)
      (d := slot w 19 + 8 * (w + 2) + 8 * n) (by omega)
  have vF := I.valF; have lF := I.lowF; have vG := I.valG; have lG := I.lowG
  simp only [fgR] at vF lF vG lG
  rw [top_word] at lF lG
  refine ⟨?_, ?_, ?_, r15t, (k₁.trans (I.keep.trans ((k₃.trans k₄).trans kt))).mono (by decide)⟩
  · rw [hm, oW₂.wv (.inl (by omega)) (by omega), wv_writeW_top _ _ _ _ _ (by omega)]
    exact top_arith (Nat.mod_lt _ (Nat.two_pow_pos _)) lF vF
  · rw [hm, wv_writeW_top _ _ _ _ _ (by omega), oW₁.wv (.inr (by omega)) (by omega)]
    exact top_arith (Nat.mod_lt _ (Nat.two_pow_pos _)) lG vG
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    rw [hm, oW₂ x (by omega), oW₁ x (by omega)]
    have := I.frm x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, fgR]; omega)
    simp only [fgR] at this
    exact this

/-! ## The pieces of `abRow` -/

/-- `lo:mid:top += K (x ^ mask)`. -/
theorem term3_ok {s : State} {B : Addr} {Z eW : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = off B eW)
    {x : MemOp} {e : Nat} (hx : s.ea x = off B e) (he : e + 8 ≤ Z) {m : Nat} (hm : eW + m + 8 ≤ Z)
    {c : Co} {K : BitVec 64} (hc : CoIs s B Z eW c K) {lo mid top : Reg} (h1 : lo ≠ .rax) (h2 : lo ≠ .rdx)
    (h3 : mid ≠ .rax) (h4 : mid ≠ .rdx) (h5 : mid ≠ lo) (h6 : top ≠ .rax) (h7 : top ≠ .rdx) (h8 : top ≠ lo)
    (h9 : top ≠ mid)
    (hk : writesOnly [.rax, .rdx, lo, mid, top] (.block (term3 x c m lo mid top)) = true)
    (hsum : (s.gpr lo).toNat + 2 ^ 64 * (s.gpr mid).toNat + 2 ^ 128 * (s.gpr top).toNat +
      K.toNat * (word s.mem B e ^^^ word s.mem B (eW + m)).toNat < 2 ^ 192) :
    WP isa (.block (term3 x c m lo mid top)) s fun t =>
      (t.gpr lo).toNat + 2 ^ 64 * (t.gpr mid).toNat + 2 ^ 128 * (t.gpr top).toNat =
        (s.gpr lo).toNat + 2 ^ 64 * (s.gpr mid).toNat + 2 ^ 128 * (s.gpr top).toNat +
        K.toNat * (word s.mem B e ^^^ word s.mem B (eW + m)).toNat ∧ t.mem = s.mem ∧
      Keep [.rax, .rdx, lo, mid, top] s t := by
  refine WP.mono (WP.keep [.rax, .rdx, lo, mid, top] (Q := fun t =>
    (t.gpr lo).toNat + 2 ^ 64 * (t.gpr mid).toNat + 2 ^ 128 * (t.gpr top).toNat =
        (s.gpr lo).toNat + 2 ^ 64 * (s.gpr mid).toNat + 2 ^ 128 * (s.gpr top).toNat +
        K.toNat * (word s.mem B e ^^^ word s.mem B (eW + m)).toNat ∧ t.mem = s.mem) ?_ hk)
    fun t ⟨a, k⟩ => ⟨a.1, a.2, k⟩
  unfold term3
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ldx_ok hs hdi hx he hm) fun s₁ ⟨a₁, m₁, k₁⟩ => ?_
  have hc₁ : CoIs s₁ B Z eW c K := hc.congr m₁ fun r hr => by
    subst hr; exact k₁.gpr (by simp [hc.2.1])
  refine WP.mono (mulCo_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi) hc₁) fun s₂ ⟨a₂, m₂, k₂⟩ => ?_
  have l₂ : s₂.gpr lo = s.gpr lo := (k₂.gpr (by simp [h1, h2])).trans (k₁.gpr (by simp [h1]))
  have i₂ : s₂.gpr mid = s.gpr mid := (k₂.gpr (by simp [h3, h4])).trans (k₁.gpr (by simp [h3]))
  have t₂ : s₂.gpr top = s.gpr top := (k₂.gpr (by simp [h6, h7])).trans (k₁.gpr (by simp [h6]))
  rw [a₁] at a₂
  have := Nat.mul_comm K.toNat (word s.mem B e ^^^ word s.mem B (eW + m)).toNat
  refine WP.mono (add3_ok h2 h5 h8 h9 (by rw [l₂, i₂, t₂]; omega)) fun t ⟨v, mt, _, _⟩ => ⟨?_, by rw [mt, m₂, m₁]⟩
  rw [v, l₂, i₂, t₂]; omega

/-- `termM k`: `lo:mid:top += K m_j`, `m_j` the word at `r8 + 4 r9`. -/
theorem termM_ok {s : State} {B : Addr} {Z eW e S : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = off B eW)
    (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = BitVec.ofNat 64 S) (he : e + 4 * S + 8 ≤ Z)
    {c : Co} {K : BitVec 64} (hc : CoIs s B Z eW c K) {lo mid top : Reg} (h1 : lo ≠ .rax) (h2 : lo ≠ .rdx)
    (h3 : mid ≠ .rax) (h4 : mid ≠ .rdx) (h5 : mid ≠ lo) (h6 : top ≠ .rax) (h7 : top ≠ .rdx) (h8' : top ≠ lo)
    (h9' : top ≠ mid)
    (hk : writesOnly [.rax, .rdx, lo, mid, top] (.block (termM c lo mid top)) = true)
    (hsum : (s.gpr lo).toNat + 2 ^ 64 * (s.gpr mid).toNat + 2 ^ 128 * (s.gpr top).toNat +
      K.toNat * (word s.mem B (e + 4 * S)).toNat < 2 ^ 192) :
    WP isa (.block (termM c lo mid top)) s fun t =>
      (t.gpr lo).toNat + 2 ^ 64 * (t.gpr mid).toNat + 2 ^ 128 * (t.gpr top).toNat =
        (s.gpr lo).toNat + 2 ^ 64 * (s.gpr mid).toNat + 2 ^ 128 * (s.gpr top).toNat +
        K.toNat * (word s.mem B (e + 4 * S)).toNat ∧ t.mem = s.mem ∧ Keep [.rax, .rdx, lo, mid, top] s t := by
  refine WP.mono (WP.keep [.rax, .rdx, lo, mid, top] (Q := fun t =>
    (t.gpr lo).toNat + 2 ^ 64 * (t.gpr mid).toNat + 2 ^ 128 * (t.gpr top).toNat =
        (s.gpr lo).toNat + 2 ^ 64 * (s.gpr mid).toNat + 2 ^ 128 * (s.gpr top).toNat +
        K.toNat * (word s.mem B (e + 4 * S)).toNat ∧ t.mem = s.mem) ?_ hk)
    fun t ⟨a, k⟩ => ⟨a.1, a.2, k⟩
  unfold termM
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = word s.mem B (e + 4 * S) ∧ t.mem = s.mem)
    (by xrun [ea_pm, h8, h9, off_pm, hs.ld he]) rfl) fun s₁ ⟨⟨a₁, m₁⟩, k₁⟩ => ?_
  have hc₁ : CoIs s₁ B Z eW c K := hc.congr m₁ fun r hr => by
    subst hr; exact k₁.gpr (by simp [hc.2.1])
  refine WP.mono (mulCo_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi) hc₁) fun s₂ ⟨a₂, m₂, k₂⟩ => ?_
  have l₂ : s₂.gpr lo = s.gpr lo := (k₂.gpr (by simp [h1, h2])).trans (k₁.gpr (by simp [h1]))
  have i₂ : s₂.gpr mid = s.gpr mid := (k₂.gpr (by simp [h3, h4])).trans (k₁.gpr (by simp [h3]))
  have t₂ : s₂.gpr top = s.gpr top := (k₂.gpr (by simp [h6, h7])).trans (k₁.gpr (by simp [h6]))
  rw [a₁] at a₂
  have := Nat.mul_comm K.toNat (word s.mem B (e + 4 * S)).toNat
  refine WP.mono (add3_ok h2 h5 h8' h9' (by rw [l₂, i₂, t₂]; omega)) fun t ⟨v, mt, _, _⟩ => ⟨?_, by rw [mt, m₂, m₁]⟩
  rw [v, l₂, i₂, t₂]; omega

/-- The window's slots and the arrays' words that a column of `abRow` reads. -/
structure AbEnv (s : State) (B : Addr) (Z eW e S : Nat) : Prop where
  scr : Scr s B Z
  rdi : s.gpr .rdi = off B eW
  r8 : s.gpr .r8 = off B e
  r9 : s.gpr .r9 = BitVec.ofNat 64 S
  win : eW + 96 ≤ Z
  m : e + 4 * S + 8 ≤ Z

theorem AbEnv.congr {s t : State} {B : Addr} {Z eW e S : Nat} (h : AbEnv s B Z eW e S)
    (k : Keep [.rax, .rdx, .r10, .r11, .r12, .r13, .r14, .rbx] s t) : AbEnv t B Z eW e S :=
  ⟨h.scr.congr k.2.2, (k.gpr (by decide)).trans h.rdi, (k.gpr (by decide)).trans h.r8,
    (k.gpr (by decide)).trans h.r9, h.win, h.m⟩

/-- Three words as a number. -/
abbrev n3 (s : State) (lo mid top : Reg) : Nat :=
  (s.gpr lo).toNat + 2 ^ 64 * (s.gpr mid).toNat + 2 ^ 128 * (s.gpr top).toNat

/-- A column of `abRow`: `r10:r11:r12 += |u| x' + |v| y' + k m_j` and
`r13:r14:rbx += |q| x'' + |r| y'' + k' m_j`. -/
theorem abCol_ok {s : State} {B : Addr} {Z eW e S : Nat} (E : AbEnv s B Z eW e S)
    {Ku Kv : BitVec 64} (hu : s.gpr .rcx = Ku) (hv : s.gpr .rbp = Kv)
    (huv : Ku.toNat + Kv.toNat ≤ 2 ^ 59)
    (hqr : (word s.mem B (eW + oQ)).toNat + (word s.mem B (eW + oR)).toNat ≤ 2 ^ 59)
    (hD : n3 s .r10 .r11 .r12 < 2 ^ 66) (hE : n3 s .r13 .r14 .rbx < 2 ^ 66) :
    WP isa (.block abCol) s fun t =>
      n3 t .r10 .r11 .r12 = n3 s .r10 .r11 .r12 +
        Ku.toNat * (word s.mem B e ^^^ word s.mem B (eW + oMu)).toNat +
        Kv.toNat * (word s.mem B (e + S) ^^^ word s.mem B (eW + oMv)).toNat +
        (word s.mem B (eW + oKd)).toNat * (word s.mem B (e + 4 * S)).toNat ∧
      n3 t .r13 .r14 .rbx = n3 s .r13 .r14 .rbx +
        (word s.mem B (eW + oQ)).toNat * (word s.mem B e ^^^ word s.mem B (eW + oMq)).toNat +
        (word s.mem B (eW + oR)).toNat * (word s.mem B (e + S) ^^^ word s.mem B (eW + oMr)).toNat +
        (word s.mem B (eW + oKe)).toNat * (word s.mem B (e + 4 * S)).toNat ∧
      t.mem = s.mem ∧ Keep [.rax, .rdx, .r10, .r11, .r12, .r13, .r14, .rbx] s t := by
  have hN := E.scr.nowrap
  have hW := E.win
  have hm := E.m
  simp only [n3] at hD hE
  have exs : ∀ t : State, t.gpr .r8 = off B e → t.ea (px 0) = off B e := fun t h => by
    rw [ea_px, h]; exact BitVec.add_zero _
  have eys : ∀ t : State, t.gpr .r8 = off B e → t.gpr .r9 = BitVec.ofNat 64 S → t.ea (py 0) = off B (e + S) :=
    fun t h h' => by rw [ea_py, h, h', off_py0]
  have l1 := mul_word_le Ku.toNat (word s.mem B e ^^^ word s.mem B (eW + oMu))
  have l2 := mul_word_le Kv.toNat (word s.mem B (e + S) ^^^ word s.mem B (eW + oMv))
  have l3 := mul_word_le (word s.mem B (eW + oQ)).toNat (word s.mem B e ^^^ word s.mem B (eW + oMq))
  have l4 := mul_word_le (word s.mem B (eW + oR)).toNat (word s.mem B (e + S) ^^^ word s.mem B (eW + oMr))
  have l5 : (word s.mem B (eW + oKd)).toNat * (word s.mem B (e + 4 * S)).toNat ≤ 2 ^ 64 * 2 ^ 64 :=
    Nat.mul_le_mul (Nat.le_of_lt (BitVec.isLt _)) (Nat.le_of_lt (BitVec.isLt _))
  have l6 : (word s.mem B (eW + oKe)).toNat * (word s.mem B (e + 4 * S)).toNat ≤ 2 ^ 64 * 2 ^ 64 :=
    Nat.mul_le_mul (Nat.le_of_lt (BitVec.isLt _)) (Nat.le_of_lt (BitVec.isLt _))
  have b1 : Ku.toNat * 2 ^ 64 + Kv.toNat * 2 ^ 64 ≤ 2 ^ 59 * 2 ^ 64 := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ huv
  have b2 : (word s.mem B (eW + oQ)).toNat * 2 ^ 64 + (word s.mem B (eW + oR)).toNat * 2 ^ 64 ≤ 2 ^ 59 * 2 ^ 64 := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hqr
  unfold abCol
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (term3_ok E.scr E.rdi (exs s E.r8) (by omega) (by unfold oMu; omega) (c := .reg .rcx)
    ⟨hu, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by omega)) fun s₁ ⟨a₁, m₁, k₁⟩ => ?_
  have E₁ := E.congr (k₁.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (term3_ok E₁.scr E₁.rdi (eys s₁ E₁.r8 E₁.r9) (by omega) (by unfold oMv; omega) (c := .reg .rbp)
    ⟨(k₁.gpr (by decide)).trans hv, by decide, by decide⟩ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl (by rw [m₁, a₁]; omega))
    fun s₂ ⟨a₂, m₂, k₂⟩ => ?_
  have E₂ := E₁.congr (k₂.mono (by decide))
  have m₂' : s₂.mem = s.mem := m₂.trans m₁
  rw [WP.block_append_iff]
  refine WP.mono (termM_ok E₂.scr E₂.rdi E₂.r8 E₂.r9 hm (c := .slot oKd) (K := word s.mem B (eW + oKd))
    ⟨by rw [m₂'], by unfold oKd; omega⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by rw [m₂', a₂, m₁, a₁]; omega)) fun s₃ ⟨a₃, m₃, k₃⟩ => ?_
  have E₃ := E₂.congr (k₃.mono (by decide))
  have m₃' : s₃.mem = s.mem := m₃.trans m₂'
  have kE : n3 s₃ .r13 .r14 .rbx = n3 s .r13 .r14 .rbx := by
    simp only [n3, (k₃.gpr (by decide) : s₃.gpr .r13 = _), (k₃.gpr (by decide) : s₃.gpr .r14 = _),
      (k₃.gpr (by decide) : s₃.gpr .rbx = _), (k₂.gpr (by decide) : s₂.gpr .r13 = _),
      (k₂.gpr (by decide) : s₂.gpr .r14 = _), (k₂.gpr (by decide) : s₂.gpr .rbx = _),
      (k₁.gpr (by decide) : s₁.gpr .r13 = _), (k₁.gpr (by decide) : s₁.gpr .r14 = _),
      (k₁.gpr (by decide) : s₁.gpr .rbx = _)]
  rw [WP.block_append_iff]
  refine WP.mono (term3_ok E₃.scr E₃.rdi (exs s₃ E₃.r8) (by omega) (by unfold oMq; omega) (c := .slot oQ)
    (K := word s.mem B (eW + oQ)) ⟨by rw [m₃'], by unfold oQ; omega⟩ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl
    (by rw [m₃']; simp only [n3] at kE; omega)) fun s₄ ⟨a₄, m₄, k₄⟩ => ?_
  have E₄ := E₃.congr (k₄.mono (by decide))
  have m₄' : s₄.mem = s.mem := m₄.trans m₃'
  rw [WP.block_append_iff]
  refine WP.mono (term3_ok E₄.scr E₄.rdi (eys s₄ E₄.r8 E₄.r9) (by omega) (by unfold oMr; omega) (c := .slot oR)
    (K := word s.mem B (eW + oR)) ⟨by rw [m₄'], by unfold oR; omega⟩ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl
    (by rw [m₄', a₄, m₃']; simp only [n3] at kE; omega)) fun s₅ ⟨a₅, m₅, k₅⟩ => ?_
  have E₅ := E₄.congr (k₅.mono (by decide))
  have m₅' : s₅.mem = s.mem := m₅.trans m₄'
  refine WP.mono (termM_ok E₅.scr E₅.rdi E₅.r8 E₅.r9 hm (c := .slot oKe) (K := word s.mem B (eW + oKe))
    ⟨by rw [m₅'], by unfold oKe; omega⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by rw [m₅', a₅, m₄', a₄, m₃']; simp only [n3] at kE; omega))
    fun t ⟨a₆, m₆, k₆⟩ => ?_
  have kD : n3 t .r10 .r11 .r12 = n3 s₃ .r10 .r11 .r12 := by
    simp only [n3, (k₆.gpr (by decide) : t.gpr .r10 = _), (k₆.gpr (by decide) : t.gpr .r11 = _),
      (k₆.gpr (by decide) : t.gpr .r12 = _), (k₅.gpr (by decide) : s₅.gpr .r10 = _),
      (k₅.gpr (by decide) : s₅.gpr .r11 = _), (k₅.gpr (by decide) : s₅.gpr .r12 = _),
      (k₄.gpr (by decide) : s₄.gpr .r10 = _), (k₄.gpr (by decide) : s₄.gpr .r11 = _),
      (k₄.gpr (by decide) : s₄.gpr .r12 = _)]
  refine ⟨?_, ?_, m₆.trans m₅', ((((k₁.trans k₂).trans k₃).trans k₄).trans (k₅.trans k₆)).mono (by decide)⟩
  · simp only [n3] at kD a₃ a₂ a₁ ⊢; rw [kD, a₃, m₂', a₂, m₁, a₁]
  · simp only [n3] at kE a₆ a₅ a₄ ⊢; rw [a₆, m₅', a₅, m₄', a₄, m₃', kE]

/-- `shift3`: the three words down one. -/
theorem shift3_ok {s : State} {lo mid top : Reg} (h1 : mid ≠ lo) (h2 : top ≠ lo) (h3 : top ≠ mid)
    (hk : writesOnly [lo, mid, top] (.block (shift3 lo mid top)) = true) :
    WP isa (.block (shift3 lo mid top)) s fun t =>
      n3 t lo mid top = n3 s lo mid top / 2 ^ 64 ∧ t.mem = s.mem ∧ Keep [lo, mid, top] s t := by
  refine WP.mono (WP.keep [lo, mid, top] (Q := fun t => n3 t lo mid top = n3 s lo mid top / 2 ^ 64 ∧
    t.mem = s.mem) ?_ hk) fun t ⟨a, k⟩ => ⟨a.1, a.2, k⟩
  unfold shift3
  xrun [h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3]
  simp only [n3, setReg_gpr, Ne.symm h1, Ne.symm h2, Ne.symm h3, ↓reduceIte]
  have := (s.gpr lo).isLt; have := (s.gpr mid).isLt; have := (s.gpr top).isLt
  have z : (BitVec.setWidth 64 (0 : BitVec 32)).toNat = 0 := rfl
  omega

/-- `abRow`'s stores and shifts: the low words of the sums to the words before `r8` and `r8 + r9`,
the sums down a word. -/
theorem abOut_ok {s : State} {B : Addr} {Z e S : Nat} (hs : Scr s B Z) (h8 : s.gpr .r8 = off B (e + 8))
    (h9 : s.gpr .r9 = BitVec.ofNat 64 S) (hz : e + S + 8 ≤ Z) :
    WP isa (.block (([.store (px (-8)) .r10, .store (py (-8)) .r13] : List Instr) ++ shift3 .r10 .r11 .r12 ++
      shift3 .r13 .r14 .rbx)) s fun t =>
      t.mem = (s.mem.writeW (off B e) (s.gpr .r10)).writeW (off B (e + S)) (s.gpr .r13) ∧
      n3 t .r10 .r11 .r12 = n3 s .r10 .r11 .r12 / 2 ^ 64 ∧ n3 t .r13 .r14 .rbx = n3 s .r13 .r14 .rbx / 2 ^ 64 ∧
      Keep [.r10, .r11, .r12, .r13, .r14, .rbx] s t := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = (s.mem.writeW (off B e) (s.gpr .r10)).writeW
    (off B (e + S)) (s.gpr .r13)) (by
      xrun [ea_px, ea_py, h8, h9, off_m8, off_pym8, hs.st (show e + 8 ≤ Z by omega), hs.st hz]) rfl)
    fun s₁ ⟨m₁, k₁⟩ => ?_
  refine WP.mono (shift3_ok (lo := .r10) (mid := .r11) (top := .r12) (by decide) (by decide) (by decide) rfl)
    fun s₂ ⟨a₂, m₂, k₂⟩ => ?_
  refine WP.mono (shift3_ok (lo := .r13) (mid := .r14) (top := .rbx) (by decide) (by decide) (by decide) rfl)
    fun t ⟨a₃, m₃, k₃⟩ => ⟨by rw [m₃, m₂, m₁], ?_, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · simp only [n3] at a₂ ⊢
    rw [(k₃.gpr (by decide) : t.gpr .r10 = _), (k₃.gpr (by decide) : t.gpr .r11 = _),
      (k₃.gpr (by decide) : t.gpr .r12 = _), a₂, (k₁.gpr (by decide) : s₁.gpr .r10 = _),
      (k₁.gpr (by decide) : s₁.gpr .r11 = _), (k₁.gpr (by decide) : s₁.gpr .r12 = _)]
  · simp only [n3] at a₃ ⊢
    rw [a₃, (k₂.gpr (by decide) : s₂.gpr .r13 = _), (k₂.gpr (by decide) : s₂.gpr .r14 = _),
      (k₂.gpr (by decide) : s₂.gpr .rbx = _), (k₁.gpr (by decide) : s₁.gpr .r13 = _),
      (k₁.gpr (by decide) : s₁.gpr .r14 = _), (k₁.gpr (by decide) : s₁.gpr .rbx = _)]

/-- `kOf o`: `k := lo (-m⁻¹) mod 2^64` into the slot `o`, then `lo:mid:top += k m_j`. -/
theorem kOf_ok {s : State} {B : Addr} {Z eW e S : Nat} (E : AbEnv s B Z eW e S) {o : Nat} (ho : o + 8 ≤ 96)
    {lo mid top : Reg} (h1 : lo ≠ .rax) (h2 : lo ≠ .rdx)
    (h3 : mid ≠ .rax) (h4 : mid ≠ .rdx) (h5 : mid ≠ lo) (h6 : top ≠ .rax) (h7 : top ≠ .rdx) (h8 : top ≠ lo)
    (h9 : top ≠ mid) (hW : eW + 96 ≤ e ∨ e + 4 * S + 8 ≤ eW)
    (hk : writesOnly [.rax, .rdx, lo, mid, top] (.block (kOf o lo mid top)) = true)
    (hkM : writesOnly [.rax, .rdx, lo, mid, top] (.block (termM (.slot o) lo mid top)) = true)
    (hsum : n3 s lo mid top < 2 ^ 128) :
    WP isa (.block (kOf o lo mid top)) s fun t =>
      n3 t lo mid top = n3 s lo mid top +
        ((s.gpr lo).toNat * (word s.mem B (eW + oMi)).toNat % 2 ^ 64) * (word s.mem B (e + 4 * S)).toNat ∧
      t.mem = s.mem.writeW (off B (eW + o)) (BitVec.ofNat 64 ((s.gpr lo).toNat * (word s.mem B (eW + oMi)).toNat)) ∧
      Keep [.rax, .rdx, lo, mid, top] s t := by
  have hN := E.scr.nowrap; have hWZ := E.win; have hm := E.m
  simp only [n3] at hsum
  refine WP.mono (WP.keep [.rax, .rdx, lo, mid, top] (Q := fun t =>
      n3 t lo mid top = n3 s lo mid top +
        ((s.gpr lo).toNat * (word s.mem B (eW + oMi)).toNat % 2 ^ 64) * (word s.mem B (e + 4 * S)).toNat ∧
      t.mem = s.mem.writeW (off B (eW + o)) (BitVec.ofNat 64 ((s.gpr lo).toNat * (word s.mem B (eW + oMi)).toNat)))
    ?_ hk) fun t ⟨a, k⟩ => ⟨a.1, a.2, k⟩
  unfold kOf
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t =>
      t.gpr .rax = BitVec.ofNat 64 ((s.gpr lo).toNat * (word s.mem B (eW + oMi)).toNat) ∧
      t.mem = s.mem.writeW (off B (eW + o)) (BitVec.ofNat 64 ((s.gpr lo).toNat * (word s.mem B (eW + oMi)).toNat)))
    (by
      xrun [ea_wm, E.rdi, offD, E.scr.ld (show eW + oMi + 8 ≤ Z by unfold oMi; omega),
        E.scr.st (show eW + o + 8 ≤ Z by omega), h1, h2, Ne.symm h1, Ne.symm h2]) rfl)
    fun s₁ ⟨⟨a₁, m₁⟩, k₁⟩ => ?_
  have hs₁ := E.scr.congr k₁.2.2
  have oW := writeW_outside s.mem B (BitVec.ofNat 64 ((s.gpr lo).toNat * (word s.mem B (eW + oMi)).toNat))
    (d := eW + o) (by omega)
  have wm : word s₁.mem B (e + 4 * S) = word s.mem B (e + 4 * S) := by
    rw [m₁]; exact oW.word (by omega) (by omega)
  have wk : word s₁.mem B (eW + o) = BitVec.ofNat 64 ((s.gpr lo).toNat * (word s.mem B (eW + oMi)).toNat) := by
    rw [m₁]; exact word_writeW_self _ _ _ _
  have l₁ : s₁.gpr lo = s.gpr lo := k₁.gpr (by simp [h1, h2])
  have i₁ : s₁.gpr mid = s.gpr mid := k₁.gpr (by simp [h3, h4])
  have t₁ : s₁.gpr top = s.gpr top := k₁.gpr (by simp [h6, h7])
  have lk := (BitVec.ofNat 64 ((s.gpr lo).toNat * (word s.mem B (eW + oMi)).toNat)).isLt
  have lmw := (word s.mem B (e + 4 * S)).isLt
  have hb : ((s.gpr lo).toNat * (word s.mem B (eW + oMi)).toNat % 2 ^ 64) * (word s.mem B (e + 4 * S)).toNat ≤
      2 ^ 64 * 2 ^ 64 := Nat.mul_le_mul (Nat.le_of_lt (Nat.mod_lt _ (by decide))) (Nat.le_of_lt lmw)
  refine WP.mono (termM_ok hs₁ ((k₁.gpr (by decide)).trans E.rdi) ((k₁.gpr (by decide)).trans E.r8)
    ((k₁.gpr (by decide)).trans E.r9) hm (c := .slot o) (K := BitVec.ofNat 64 ((s.gpr lo).toNat *
      (word s.mem B (eW + oMi)).toNat)) ⟨wk, by omega⟩ h1 h2 h3 h4 h5 h6 h7 h8 h9 hkM
    (by rw [l₁, i₁, t₁, wm, BitVec.toNat_ofNat]; omega)) fun t ⟨v, mt, _⟩ => ⟨?_, by rw [mt, m₁]⟩
  simp only [n3]; rw [v, l₁, i₁, t₁, wm, BitVec.toNat_ofNat]

/-- `signX x; termR c m`: `lo:mid:top += |c| (S ^ mask)` for the sign word `S` of the word at `x`. -/
theorem sgnTerm_ok {s : State} {B : Addr} {Z eW e : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = off B eW)
    {x : MemOp} (hx : s.ea x = off B e) (he : e + 8 ≤ Z) {c m : Nat} (hc : eW + c + 8 ≤ Z) (hm : eW + m + 8 ≤ Z)
    {lo mid top : Reg} (h1 : lo ≠ .rax) (h2 : lo ≠ .rdx)
    (h3 : mid ≠ .rax) (h4 : mid ≠ .rdx) (h5 : mid ≠ lo) (h6 : top ≠ .rax) (h7 : top ≠ .rdx) (h8 : top ≠ lo)
    (h9 : top ≠ mid) (hlc : lo ≠ .rcx) (hmc : mid ≠ .rcx) (htc : top ≠ .rcx)
    (hk : writesOnly [.rax, .rdx, .rcx, lo, mid, top] (.block (signX x ++ termR c m lo mid top)) = true)
    (hsum : n3 s lo mid top < 2 ^ 128) :
    WP isa (.block (signX x ++ termR c m lo mid top)) s fun t =>
      n3 t lo mid top = n3 s lo mid top + (word s.mem B (eW + c)).toNat *
        ((BitVec.setWidth 64 (0 : BitVec 32) - word s.mem B e >>> 63) ^^^ word s.mem B (eW + m)).toNat ∧
      t.mem = s.mem ∧ Keep [.rax, .rdx, .rcx, lo, mid, top] s t := by
  simp only [n3] at hsum
  refine WP.mono (WP.keep [.rax, .rdx, .rcx, lo, mid, top] (Q := fun t =>
      n3 t lo mid top = n3 s lo mid top + (word s.mem B (eW + c)).toNat *
        ((BitVec.setWidth 64 (0 : BitVec 32) - word s.mem B e >>> 63) ^^^ word s.mem B (eW + m)).toNat ∧
      t.mem = s.mem) ?_ hk) fun t ⟨a, k⟩ => ⟨a.1, a.2, k⟩
  have hb : signX x ++ termR c m lo mid top = ([.mov .rax (.mem x), .shift .shr .rax 63, .mov32 .rdx (.imm 0),
      .alu .sub .rdx (.reg .rax), .mov .rax (.reg .rdx), .alu .xor .rax (.mem (wm m)), .mov .rcx (.mem (wm c)),
      .mul .rcx] : List Instr) ++ [.alu .add lo (.reg .rax), .alu .adc mid (.reg .rdx), .alu .adc top (.imm 0)] := rfl
  rw [hb, WP.block_append_iff]
  generalize hP : (word s.mem B (eW + c)).toNat *
    ((BitVec.setWidth 64 (0 : BitVec 32) - word s.mem B e >>> 63) ^^^ word s.mem B (eW + m)).toNat = P
  have hP' : ((BitVec.setWidth 64 (0 : BitVec 32) - word s.mem B e >>> 63) ^^^ word s.mem B (eW + m)).toNat *
      (word s.mem B (eW + c)).toNat = P := by rw [Nat.mul_comm]; exact hP
  have hPl : P < 2 ^ 64 * 2 ^ 64 := hP ▸ Nat.mul_lt_mul'' (BitVec.isLt _) (BitVec.isLt _)
  refine WP.mono (WP.keep [.rax, .rdx, .rcx] (Q := fun t =>
      t.gpr .rax = BitVec.ofNat 64 P ∧ t.gpr .rdx = BitVec.ofNat 64 (P / 2 ^ 64) ∧ t.mem = s.mem) (by
      xrun [hx, hs.ld he, ea_wm, hdi, offD, hs.ld hm, hs.ld hc, hP']) rfl)
    fun s₁ ⟨⟨a₁, d₁, m₁⟩, k₁⟩ => ?_
  have l₁ : s₁.gpr lo = s.gpr lo := k₁.gpr (by simp [h1, h2, hlc])
  have i₁ : s₁.gpr mid = s.gpr mid := k₁.gpr (by simp [h3, h4, hmc])
  have t₁ : s₁.gpr top = s.gpr top := k₁.gpr (by simp [h6, h7, htc])
  have ep : (s₁.gpr .rax).toNat + 2 ^ 64 * (s₁.gpr .rdx).toNat = P := by
    rw [a₁, d₁, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul hPl)]; omega
  refine WP.mono (add3_ok h2 h5 h8 h9 (by rw [l₁, i₁, t₁]; omega)) fun t ⟨v, mt, _, _⟩ => ⟨?_, by rw [mt, m₁]⟩
  simp only [n3]; rw [v, l₁, i₁, t₁]; omega

/-! ## `abRow` -/

namespace Rw

/-- The factor `k` of `m` for a row: the low word of the first column's sum times `-m⁻¹`. -/
def kv (R : Rw) (c₁ m₁ c₂ m₂ : Nat) : Nat := R.sum c₁ m₁ c₂ m₂ 1 % 2 ^ 64 * (R.c oMi).toNat % 2 ^ 64

/-- The sum and `k m` over the first `j` words: what `abRow`'s accumulator holds. -/
def dsum (R : Rw) (c₁ m₁ c₂ m₂ j : Nat) : Nat :=
  R.sum c₁ m₁ c₂ m₂ j + R.kv c₁ m₁ c₂ m₂ * wv R.m R.B (R.eA + 4 * R.S) j

theorem dsum_succ (R : Rw) (c₁ m₁ c₂ m₂ j : Nat) :
    R.dsum c₁ m₁ c₂ m₂ (j + 1) = R.dsum c₁ m₁ c₂ m₂ j + 2 ^ (64 * j) *
      ((R.c c₁).toNat * (word R.m R.B (R.eA + 8 * j) ^^^ R.c m₁).toNat +
        (R.c c₂).toNat * (word R.m R.B (R.eA + R.S + 8 * j) ^^^ R.c m₂).toNat +
        R.kv c₁ m₁ c₂ m₂ * (word R.m R.B (R.eA + 4 * R.S + 8 * j)).toNat) := by
  simp only [dsum, sum_succ, wv]
  grind

end Rw

/-- The row of `(a, b)` for the window at `slot w 16` and `n`. -/
def abR (B : Addr) (Z w n : Nat) (m : Mem) : Rw := ⟨B, Z, slot w 16, slot w 21, 8 * (w + 2), n, m⟩

/-- What `abRow`'s loop keeps from its start `s₀`, the factors `k` in the window. -/
structure AbStart (R : Rw) (s₀ : State) : Prop where
  ok : R.Ok
  rdi : s₀.gpr .rdi = off R.B R.eW
  r9 : s₀.gpr .r9 = BitVec.ofNat 64 R.S
  r15 : s₀.gpr .r15 = off R.B (R.eA + 8 * (R.n + 1))
  rcx : s₀.gpr .rcx = R.c oU
  rbp : s₀.gpr .rbp = R.c oV
  huv : (R.c oU).toNat + (R.c oV).toNat ≤ 2 ^ 59
  hqr : (R.c oQ).toNat + (R.c oR).toNat ≤ 2 ^ 59
  mem : s₀.mem = (R.m.writeW (off R.B (R.eW + oKd)) (BitVec.ofNat 64 (R.kv oU oMu oV oMv))).writeW
    (off R.B (R.eW + oKe)) (BitVec.ofNat 64 (R.kv oQ oMq oR oMr))

/-- After `k + 1` columns of `abRow` (`k` words stored): the words and the accumulators hold the
sums shifted down a word. -/
structure AbInv (R : Rw) (s₀ : State) (k : Nat) (t : State) : Prop where
  scr : Scr t R.B R.Z
  keep : Keep [.rax, .rdx, .r8, .r10, .r11, .r12, .r13, .r14, .rbx] s₀ t
  r8 : t.gpr .r8 = off R.B (R.eA + 8 * (k + 1))
  frm : Frm R.B [(R.eA, 8 * k), (R.eA + R.S, 8 * k)] s₀.mem t.mem
  valD : wv t.mem R.B R.eA k + 2 ^ (64 * k) * n3 t .r10 .r11 .r12 = R.dsum oU oMu oV oMv (k + 1) / 2 ^ 64
  valE : wv t.mem R.B (R.eA + R.S) k + 2 ^ (64 * k) * n3 t .r13 .r14 .rbx = R.dsum oQ oMq oR oMr (k + 1) / 2 ^ 64
  bD : n3 t .r10 .r11 .r12 < 2 ^ 66
  bE : n3 t .r13 .r14 .rbx < 2 ^ 66

/-- The words of the memory at `abRow`'s loop start, outside the factors' slots. -/
theorem AbStart.memW {R : Rw} {s₀ : State} (h : AbStart R s₀) {d : Nat}
    (hd : d + 8 ≤ R.eW + oKd ∨ R.eW + oKd + 8 ≤ d) (hd' : d + 8 ≤ R.eW + oKe ∨ R.eW + oKe + 8 ≤ d)
    (hz : d + 8 ≤ R.Z) : word s₀.mem R.B d = word R.m R.B d := by
  have := h.ok.nowrap; have := h.ok.win; have := h.ok.z
  rw [h.mem, (writeW_outside _ R.B _ (d := R.eW + oKe) (by unfold oKe; omega)).word hd' (by omega),
    (writeW_outside _ R.B _ (d := R.eW + oKd) (by unfold oKd; omega)).word hd (by omega)]

theorem AbStart.kd {R : Rw} {s₀ : State} (h : AbStart R s₀) :
    word s₀.mem R.B (R.eW + oKd) = BitVec.ofNat 64 (R.kv oU oMu oV oMv) := by
  have := h.ok.nowrap; have := h.ok.win; have := h.ok.z
  rw [h.mem, (writeW_outside _ R.B _ (d := R.eW + oKe) (by unfold oKe; omega)).word
    (by unfold oKd oKe; omega) (by unfold oKd; omega), word_writeW_self]

theorem AbStart.ke {R : Rw} {s₀ : State} (h : AbStart R s₀) :
    word s₀.mem R.B (R.eW + oKe) = BitVec.ofNat 64 (R.kv oQ oMq oR oMr) := by
  rw [h.mem, word_writeW_self]

theorem AbInv.memW {R : Rw} {s₀ t : State} {k : Nat} (h : AbInv R s₀ k t) (hR : R.Ok) {d : Nat}
    (hd : d + 8 ≤ R.eA ∨ (R.eA + 8 * k ≤ d ∧ d + 8 ≤ R.eA + R.S) ∨ R.eA + R.S + 8 * k ≤ d)
    (hz : d + 8 ≤ R.Z) : word t.mem R.B d = word s₀.mem R.B d :=
  h.frm.word_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have := hR.len; have := hR.z; rcases hr with rfl | rfl <;> dsimp only <;> omega) (by have := hR.nowrap; omega)

theorem kv_lt (R : Rw) (c₁ m₁ c₂ m₂ : Nat) : R.kv c₁ m₁ c₂ m₂ < 2 ^ 64 := Nat.mod_lt _ (by decide)

theorem ofNat_kv (R : Rw) (c₁ m₁ c₂ m₂ : Nat) : (BitVec.ofNat 64 (R.kv c₁ m₁ c₂ m₂)).toNat = R.kv c₁ m₁ c₂ m₂ := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (kv_lt _ _ _ _ _)]

/-- A column of `abRow`: the accumulator `A' = A + T` stored a word and shifted. -/
theorem ab_arith {k W A A' D T : Nat} (hv : W + 2 ^ (64 * k) * A = D / 2 ^ 64) (hA : A' = A + T) :
    W + 2 ^ (64 * k) * (A' % 2 ^ 64) + 2 ^ (64 * (k + 1)) * (A' / 2 ^ 64) =
      (D + 2 ^ (64 * (k + 1)) * T) / 2 ^ 64 := by
  rw [pow64_succ, show 2 ^ (64 * k) * 2 ^ 64 * T = 2 ^ 64 * (2 ^ (64 * k) * T) by grind,
    Nat.add_mul_div_left _ _ (by decide), ← hv]
  have := Nat.div_add_mod A' (2 ^ 64)
  subst hA
  grind

/-- A column of `abRow`'s loop, `k + 1 ≤ n`. -/
theorem abStep_ok {R : Rw} {s₀ : State} (h₀ : AbStart R s₀) {k : Nat} (hk : k + 1 ≤ R.n) {t : State}
    (hI : AbInv R s₀ k t) :
    WP isa (.block (abCol ++ ([.store (px (-8)) .r10, .store (py (-8)) .r13] : List Instr) ++
      shift3 .r10 .r11 .r12 ++ shift3 .r13 .r14 .rbx ++ next)) t
      fun t' => t'.zf = some (decide (k + 1 + 1 = R.n + 1)) ∧ AbInv R s₀ (k + 1) t' := by
  have hR := h₀.ok
  have hN := hR.nowrap; have hW := hR.win; have hL := hR.len; have hz := hR.z
  have tdi : t.gpr .rdi = off R.B R.eW := (hI.keep.gpr (by decide)).trans h₀.rdi
  have t9 : t.gpr .r9 = BitVec.ofNat 64 R.S := (hI.keep.gpr (by decide)).trans h₀.r9
  have E : AbEnv t R.B R.Z R.eW (R.eA + 8 * (k + 1)) R.S := ⟨hI.scr, tdi, hI.r8, t9, by omega, by omega⟩
  have wc : ∀ o, o + 8 ≤ 96 → (o + 8 ≤ oKd ∨ oKd + 8 ≤ o) → (o + 8 ≤ oKe ∨ oKe + 8 ≤ o) →
      word t.mem R.B (R.eW + o) = R.c o := fun o ho h1 h2 => by
    rw [hI.memW hR (.inl (by omega)) (by omega), h₀.memW (by omega) (by omega) (by omega)]
  have wkd : word t.mem R.B (R.eW + oKd) = BitVec.ofNat 64 (R.kv oU oMu oV oMv) := by
    rw [hI.memW hR (.inl (by unfold oKd; omega)) (by unfold oKd; omega), h₀.kd]
  have wke : word t.mem R.B (R.eW + oKe) = BitVec.ofNat 64 (R.kv oQ oMq oR oMr) := by
    rw [hI.memW hR (.inl (by unfold oKe; omega)) (by unfold oKe; omega), h₀.ke]
  have wA : ∀ d, R.eA + 8 * k ≤ d → d + 8 ≤ R.eA + R.S → word t.mem R.B d = word R.m R.B d := fun d h1 h2 => by
    rw [hI.memW hR (.inr (.inl ⟨h1, h2⟩)) (by omega), h₀.memW (by unfold oKd; omega) (by unfold oKe; omega) (by omega)]
  have wB : ∀ d, R.eA + R.S + 8 * k ≤ d → d + 8 ≤ R.Z → word t.mem R.B d = word R.m R.B d := fun d h1 h2 => by
    rw [hI.memW hR (.inr (.inr h1)) h2, h₀.memW (by unfold oKd; omega) (by unfold oKe; omega) h2]
  have wx := wA (R.eA + 8 * (k + 1)) (by omega) (by omega)
  have wy : word t.mem R.B (R.eA + 8 * (k + 1) + R.S) = word R.m R.B (R.eA + R.S + 8 * (k + 1)) := by
    rw [show R.eA + 8 * (k + 1) + R.S = R.eA + R.S + 8 * (k + 1) by omega]; exact wB _ (by omega) (by omega)
  have wm : word t.mem R.B (R.eA + 8 * (k + 1) + 4 * R.S) = word R.m R.B (R.eA + 4 * R.S + 8 * (k + 1)) := by
    rw [show R.eA + 8 * (k + 1) + 4 * R.S = R.eA + 4 * R.S + 8 * (k + 1) by omega]; exact wB _ (by omega) (by omega)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (abCol_ok E ((hI.keep.gpr (by decide)).trans h₀.rcx) ((hI.keep.gpr (by decide)).trans h₀.rbp)
    h₀.huv (by rw [wc oQ (by decide) (by decide) (by decide), wc oR (by decide) (by decide)
      (by decide)]; exact h₀.hqr) hI.bD hI.bE)
    fun s₁ ⟨aD, aE, m₁, k₁⟩ => ?_
  simp only [wc oMu (by decide) (by decide) (by decide), wc oMv (by decide) (by decide) (by decide),
    wc oQ (by decide) (by decide) (by decide), wc oMq (by decide) (by decide) (by decide),
    wc oR (by decide) (by decide) (by decide), wc oMr (by decide) (by decide) (by decide),
    wkd, wke, wx, wy, wm, ofNat_kv] at aD aE
  have s8 : s₁.gpr .r8 = off R.B (R.eA + 8 * k + 8) := by
    rw [(k₁.gpr (by decide) : s₁.gpr .r8 = _), hI.r8, show R.eA + 8 * (k + 1) = R.eA + 8 * k + 8 by omega]
  have s9 : s₁.gpr .r9 = BitVec.ofNat 64 R.S := (k₁.gpr (by decide)).trans t9
  rw [show ∀ (a b c d : List Instr), a ++ (b ++ (c ++ d)) = (a ++ b ++ c) ++ d from fun _ _ _ _ => by
    simp only [List.append_assoc], WP.block_append_iff]
  refine WP.mono (abOut_ok (hI.scr.congr k₁.2.2) s8 s9 (by omega)) fun s₂ ⟨m₂, oD, oE, k₂⟩ => ?_
  refine WP.mono (next_ok (B := R.B) (e := R.eA) (N := R.n + 1) (j := k + 1) (by rw [k₂.gpr (by decide), s8,
      show R.eA + 8 * k + 8 = R.eA + 8 * (k + 1) by omega])
    (by rw [(k₂.gpr (by decide)), (k₁.gpr (by decide)), (hI.keep.gpr (by decide)), h₀.r15])
    (by omega) (by omega)) fun t' ⟨z', r8', m', k'⟩ => ⟨z', ?_⟩
  have hmt : t'.mem = (t.mem.writeW (off R.B (R.eA + 8 * k)) (s₁.gpr .r10)).writeW
      (off R.B (R.eA + R.S + 8 * k)) (s₁.gpr .r13) := by
    rw [m', m₂, m₁, Nat.add_right_comm R.eA (8 * k) R.S]
  have kk := (k₁.trans k₂).trans k'
  have oW₁ := writeW_outside t.mem R.B (s₁.gpr .r10) (d := R.eA + 8 * k) (by omega)
  have oW₂ := writeW_outside (t.mem.writeW (off R.B (R.eA + 8 * k)) (s₁.gpr .r10)) R.B (s₁.gpr .r13)
    (d := R.eA + R.S + 8 * k) (by omega)
  have n3D : n3 t' .r10 .r11 .r12 = n3 s₁ .r10 .r11 .r12 / 2 ^ 64 := by
    rw [← oD]; simp only [n3, (k'.gpr (by decide) : t'.gpr .r10 = _), (k'.gpr (by decide) : t'.gpr .r11 = _),
      (k'.gpr (by decide) : t'.gpr .r12 = _)]
  have n3E : n3 t' .r13 .r14 .rbx = n3 s₁ .r13 .r14 .rbx / 2 ^ 64 := by
    rw [← oE]; simp only [n3, (k'.gpr (by decide) : t'.gpr .r13 = _), (k'.gpr (by decide) : t'.gpr .r14 = _),
      (k'.gpr (by decide) : t'.gpr .rbx = _)]
  have lD : (s₁.gpr .r10).toNat = n3 s₁ .r10 .r11 .r12 % 2 ^ 64 := by
    simp only [n3]; have := (s₁.gpr .r10).isLt; omega
  have lE : (s₁.gpr .r13).toNat = n3 s₁ .r13 .r14 .rbx % 2 ^ 64 := by
    simp only [n3]; have := (s₁.gpr .r13).isLt; omega
  have bxD := mul_word_le (R.c oU).toNat (word R.m R.B (R.eA + 8 * (k + 1)) ^^^ R.c oMu)
  have byD := mul_word_le (R.c oV).toNat (word R.m R.B (R.eA + R.S + 8 * (k + 1)) ^^^ R.c oMv)
  have bxE := mul_word_le (R.c oQ).toNat (word R.m R.B (R.eA + 8 * (k + 1)) ^^^ R.c oMq)
  have byE := mul_word_le (R.c oR).toNat (word R.m R.B (R.eA + R.S + 8 * (k + 1)) ^^^ R.c oMr)
  have bmD : R.kv oU oMu oV oMv * (word R.m R.B (R.eA + 4 * R.S + 8 * (k + 1))).toNat ≤ 2 ^ 64 * 2 ^ 64 :=
    Nat.mul_le_mul (Nat.le_of_lt (kv_lt _ _ _ _ _)) (Nat.le_of_lt (BitVec.isLt _))
  have bmE : R.kv oQ oMq oR oMr * (word R.m R.B (R.eA + 4 * R.S + 8 * (k + 1))).toNat ≤ 2 ^ 64 * 2 ^ 64 :=
    Nat.mul_le_mul (Nat.le_of_lt (kv_lt _ _ _ _ _)) (Nat.le_of_lt (BitVec.isLt _))
  have b1 : (R.c oU).toNat * 2 ^ 64 + (R.c oV).toNat * 2 ^ 64 ≤ 2 ^ 59 * 2 ^ 64 := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ h₀.huv
  have b2 : (R.c oQ).toNat * 2 ^ 64 + (R.c oR).toNat * 2 ^ 64 ≤ 2 ^ 59 * 2 ^ 64 := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ h₀.hqr
  refine ⟨hI.scr.congr kk.2.2, (hI.keep.trans kk).mono (by decide), r8', ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    rw [hmt, oW₂ x (by omega), oW₁ x (by omega)]
    exact hI.frm x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
  · rw [hmt, oW₂.wv (.inl (by omega)) (by omega), wv_writeW_top _ _ _ _ _ (by omega), lD, n3D, Rw.dsum_succ]
    exact ab_arith hI.valD (by rw [aD]; omega)
  · rw [hmt, wv_writeW_top _ _ _ _ _ (by omega), oW₁.wv (.inr (by omega)) (by omega), lE, n3E, Rw.dsum_succ]
    exact ab_arith hI.valE (by rw [aE]; omega)
  · rw [n3D, aD, Nat.div_lt_iff_lt_mul (by decide)]; have := hI.bD; omega
  · rw [n3E, aE, Nat.div_lt_iff_lt_mul (by decide)]; have := hI.bE; omega

/-- Column 0 of one of `abRow`'s sums: the start, the two products, the factor `k` into the slot
`o`, `k m₀`, and the shift. -/
theorem abHalf_ok {s : State} {B : Addr} {Z eW e S : Nat} (E : AbEnv s B Z eW e S)
    (hy : e + S + 8 ≤ Z) (hWe : eW + 96 ≤ e)
    {cu mu cv mv o : Nat} (h1 : cu + 8 ≤ 96) (h2 : mu + 8 ≤ 96) (h3 : cv + 8 ≤ 96) (h4 : mv + 8 ≤ 96)
    (ho : o + 8 ≤ 96)
    {lo mid top : Reg}
    {c₁ c₂ : Co} (hc₁ : CoIs s B Z eW c₁ (word s.mem B (eW + cu))) (hc₂ : CoIs s B Z eW c₂ (word s.mem B (eW + cv)))
    (hc₁' : ∀ r, c₁ = .reg r → r ≠ lo ∧ r ≠ mid ∧ r ≠ top)
    (hc₂' : ∀ r, c₂ = .reg r → r ≠ lo ∧ r ≠ mid ∧ r ≠ top)
    (hcc : (word s.mem B (eW + cu)).toNat + (word s.mem B (eW + cv)).toNat ≤ 2 ^ 59)
    (r1 : lo ≠ .rax) (r2 : lo ≠ .rdx) (r3 : mid ≠ .rax) (r4 : mid ≠ .rdx) (r5 : mid ≠ lo)
    (r6 : top ≠ .rax) (r7 : top ≠ .rdx) (r8 : top ≠ lo) (r9 : top ≠ mid) (r10 : lo ≠ .rdi)
    (r11 : lo ≠ .r8) (r12 : mid ≠ .r8) (r13 : top ≠ .r8) (r14 : lo ≠ .r9) (r15 : mid ≠ .r9) (r16 : top ≠ .r9)
    (r17 : mid ≠ .rdi) (r18 : top ≠ .rdi)
    (k1 : writesOnly [.rax, lo] (.block (ones cu mu cv mv lo)) = true)
    (k2 : writesOnly [mid, top] (.block [.mov32 mid (.imm 0), .mov32 top (.imm 0)]) = true)
    (k3 : writesOnly [.rax, .rdx, lo, mid, top] (.block (term3 (px 0) c₁ mu lo mid top)) = true)
    (k4 : writesOnly [.rax, .rdx, lo, mid, top] (.block (term3 (py 0) c₂ mv lo mid top)) = true)
    (k5 : writesOnly [.rax, .rdx, lo, mid, top] (.block (kOf o lo mid top)) = true)
    (k6 : writesOnly [.rax, .rdx, lo, mid, top] (.block (termM (.slot o) lo mid top)) = true)
    (k7 : writesOnly [lo, mid, top] (.block (shift3 lo mid top)) = true) :
    WP isa (.block (ones cu mu cv mv lo ++ ([.mov32 mid (.imm 0), .mov32 top (.imm 0)] : List Instr) ++
      term3 (px 0) c₁ mu lo mid top ++ term3 (py 0) c₂ mv lo mid top ++ kOf o lo mid top ++ shift3 lo mid top)) s
      fun t =>
      n3 t lo mid top = (((word s.mem B (eW + cu) &&& word s.mem B (eW + mu)) +
          (word s.mem B (eW + cv) &&& word s.mem B (eW + mv))).toNat +
          (word s.mem B (eW + cu)).toNat * (word s.mem B e ^^^ word s.mem B (eW + mu)).toNat +
          (word s.mem B (eW + cv)).toNat * (word s.mem B (e + S) ^^^ word s.mem B (eW + mv)).toNat +
        ((((word s.mem B (eW + cu) &&& word s.mem B (eW + mu)) +
          (word s.mem B (eW + cv) &&& word s.mem B (eW + mv))).toNat +
          (word s.mem B (eW + cu)).toNat * (word s.mem B e ^^^ word s.mem B (eW + mu)).toNat +
          (word s.mem B (eW + cv)).toNat * (word s.mem B (e + S) ^^^ word s.mem B (eW + mv)).toNat) % 2 ^ 64 *
          (word s.mem B (eW + oMi)).toNat % 2 ^ 64) * (word s.mem B (e + 4 * S)).toNat) / 2 ^ 64 ∧
      t.mem = s.mem.writeW (off B (eW + o)) (BitVec.ofNat 64 ((((word s.mem B (eW + cu) &&& word s.mem B (eW + mu)) +
          (word s.mem B (eW + cv) &&& word s.mem B (eW + mv))).toNat +
          (word s.mem B (eW + cu)).toNat * (word s.mem B e ^^^ word s.mem B (eW + mu)).toNat +
          (word s.mem B (eW + cv)).toNat * (word s.mem B (e + S) ^^^ word s.mem B (eW + mv)).toNat) % 2 ^ 64 *
          (word s.mem B (eW + oMi)).toNat)) ∧
      Keep [.rax, .rdx, lo, mid, top] s t := by
  have hN := E.scr.nowrap; have hW := E.win; have hm := E.m
  generalize hO : (word s.mem B (eW + cu) &&& word s.mem B (eW + mu)) + (word s.mem B (eW + cv) &&& word s.mem B (eW + mv)) = O
  generalize hX : (word s.mem B (eW + cu)).toNat * (word s.mem B e ^^^ word s.mem B (eW + mu)).toNat = X
  generalize hY : (word s.mem B (eW + cv)).toNat * (word s.mem B (e + S) ^^^ word s.mem B (eW + mv)).toNat = Y
  have bX : X ≤ (word s.mem B (eW + cu)).toNat * 2 ^ 64 := hX ▸ mul_word_le _ _
  have bY : Y ≤ (word s.mem B (eW + cv)).toNat * 2 ^ 64 := hY ▸ mul_word_le _ _
  have bXY : (word s.mem B (eW + cu)).toNat * 2 ^ 64 + (word s.mem B (eW + cv)).toNat * 2 ^ 64 ≤ 2 ^ 59 * 2 ^ 64 := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hcc
  have bO := O.isLt
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ones_ok E.scr E.rdi E.win h1 h2 h3 h4 r1 r10 k1) fun s₁ ⟨a₁, m₁, kk₁⟩ => ?_
  rw [hO] at a₁
  rw [show ∀ l : List Instr, ([Instr.mov32 mid (.imm 0), .mov32 top (.imm 0)] ++ l) =
    [Instr.mov32 mid (.imm 0), .mov32 top (.imm 0)] ++ l from fun _ => rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [mid, top] (Q := fun t => t.gpr mid = 0 ∧ t.gpr top = 0 ∧ t.mem = s₁.mem)
    (by xrun [r9, Ne.symm r9]) k2) fun s₂ ⟨⟨a₂, b₂, m₂⟩, kk₂⟩ => ?_
  have K12 : Keep [.rax, .rdx, lo, mid, top] s s₂ := (kk₁.trans kk₂).mono (by simp)
  have m₂' : s₂.mem = s.mem := m₂.trans m₁
  have hs₂ := E.scr.congr K12.2.2
  have di₂ : s₂.gpr .rdi = off B eW := (K12.gpr (by simp [Ne.symm r10, Ne.symm r17, Ne.symm r18])).trans E.rdi
  have r8₂ : s₂.gpr .r8 = off B e := (K12.gpr (by simp [Ne.symm r11, Ne.symm r12, Ne.symm r13])).trans E.r8
  have r9₂ : s₂.gpr .r9 = BitVec.ofNat 64 S := (K12.gpr (by simp [Ne.symm r14, Ne.symm r15, Ne.symm r16])).trans E.r9
  have n₂ : n3 s₂ lo mid top = O.toNat := by
    simp only [n3, a₂, b₂, (kk₂.gpr (by simp [Ne.symm r5, Ne.symm r8]) : s₂.gpr lo = _), a₁]; simp
  have cK : ∀ {c : Co} {K : BitVec 64}, CoIs s B Z eW c K → (∀ r, c = .reg r → r ≠ lo ∧ r ≠ mid ∧ r ≠ top) →
      ∀ {t : State}, Keep [.rax, .rdx, lo, mid, top] s t → t.mem = s.mem → CoIs t B Z eW c K :=
    fun {c} {K} hc hc' {t} k hm => hc.congr hm fun r hr => k.gpr (by
      have h' := hc' r hr; subst hr
      have h'' : s.gpr r = K ∧ r ≠ .rax ∧ r ≠ .rdx := hc
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨h''.2.1, h''.2.2, h'.1, h'.2.1, h'.2.2⟩)
  have n₂' := n₂
  simp only [n3] at n₂'
  rw [WP.block_append_iff]
  refine WP.mono (term3_ok (e := e) hs₂ di₂ (by rw [ea_px, r8₂]; exact BitVec.add_zero _) (by omega) (by omega)
    (cK hc₁ hc₁' K12 m₂') r1 r2 r3 r4 r5 r6 r7 r8 r9 k3 (by rw [n₂', m₂', hX]; omega)) fun s₃ ⟨a₃, m₃, kk₃⟩ => ?_
  have K13 := K12.trans kk₃
  have m₃' : s₃.mem = s.mem := m₃.trans m₂'
  rw [m₂', hX, n₂'] at a₃
  rw [WP.block_append_iff]
  refine WP.mono (term3_ok (e := e + S) (hs₂.congr kk₃.2.2)
    ((kk₃.gpr (by simp [Ne.symm r10, Ne.symm r17, Ne.symm r18])).trans di₂)
    (by rw [ea_py, (kk₃.gpr (by simp [Ne.symm r11, Ne.symm r12, Ne.symm r13])), r8₂,
      (kk₃.gpr (by simp [Ne.symm r14, Ne.symm r15, Ne.symm r16])), r9₂, off_py0]) hy (by omega)
    (cK hc₂ hc₂' (K13.mono (by simp)) m₃') r1 r2 r3 r4 r5 r6 r7 r8 r9 k4
    (by rw [a₃, m₃', hY]; omega)) fun s₄ ⟨a₄, m₄, kk₄⟩ => ?_
  have K14 := K13.trans kk₄
  have m₄' : s₄.mem = s.mem := m₄.trans m₃'
  rw [m₃', hY, a₃] at a₄
  have E₄ : AbEnv s₄ B Z eW e S := ⟨E.scr.congr K14.2.2, (K14.gpr (by simp [Ne.symm r10, Ne.symm r17, Ne.symm r18])).trans E.rdi,
    (K14.gpr (by simp [Ne.symm r11, Ne.symm r12, Ne.symm r13])).trans E.r8,
    (K14.gpr (by simp [Ne.symm r14, Ne.symm r15, Ne.symm r16])).trans E.r9, E.win, E.m⟩
  have n₄ : n3 s₄ lo mid top = O.toNat + X + Y := by simp only [n3]; rw [a₄]
  have lo₄ : (s₄.gpr lo).toNat = (O.toNat + X + Y) % 2 ^ 64 := by
    rw [← n₄]; simp only [n3]; have := (s₄.gpr lo).isLt; omega
  rw [WP.block_append_iff]
  refine WP.mono (kOf_ok E₄ ho r1 r2 r3 r4 r5 r6 r7 r8 r9 (.inl hWe) k5 k6 (by rw [n₄]; omega))
    fun s₅ ⟨a₅, m₅, kk₅⟩ => ?_
  refine WP.mono (shift3_ok r5 r8 r9 k7) fun t ⟨a₆, m₆, kk₆⟩ => ⟨?_, ?_, ((K14.trans kk₅).trans kk₆).mono (by simp)⟩
  · rw [a₆, a₅, n₄, lo₄, m₄']
  · rw [m₆, m₅, m₄', lo₄]

theorem ofNat_mod64 (x : Nat) : BitVec.ofNat 64 x = BitVec.ofNat 64 (x % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, Nat.mod_mod]

theorem sum_one (R : Rw) (c₁ m₁ c₂ m₂ : Nat) :
    R.sum c₁ m₁ c₂ m₂ 1 = ((R.c c₁ &&& R.c m₁) + (R.c c₂ &&& R.c m₂)).toNat +
      (R.c c₁).toNat * (word R.m R.B R.eA ^^^ R.c m₁).toNat +
      (R.c c₂).toNat * (word R.m R.B (R.eA + R.S) ^^^ R.c m₂).toNat := by
  rw [show (1 : Nat) = 0 + 1 from rfl, Rw.sum_succ, sum_zero]
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.add_zero]
  omega

theorem dsum_one (R : Rw) (c₁ m₁ c₂ m₂ : Nat) :
    R.dsum c₁ m₁ c₂ m₂ 1 = R.sum c₁ m₁ c₂ m₂ 1 + R.kv c₁ m₁ c₂ m₂ * (word R.m R.B (R.eA + 4 * R.S)).toNat := by
  simp only [Rw.dsum, wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero]

theorem half_lt (O K₁ K₂ x y m : BitVec 64) (k : Nat) (hK : K₁.toNat + K₂.toNat ≤ 2 ^ 59) (hk : k < 2 ^ 64) :
    O.toNat + K₁.toNat * x.toNat + K₂.toNat * y.toNat + k * m.toNat < 2 ^ 66 * 2 ^ 64 := by
  have h1 := mul_word_le K₁.toNat x
  have h2 := mul_word_le K₂.toNat y
  have h3 : k * m.toNat ≤ 2 ^ 64 * 2 ^ 64 := Nat.mul_le_mul (Nat.le_of_lt hk) (Nat.le_of_lt m.isLt)
  have h4 : K₁.toNat * 2 ^ 64 + K₂.toNat * 2 ^ 64 ≤ 2 ^ 59 * 2 ^ 64 := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hK
  have := O.isLt
  omega

/-- `abRow`'s first block: the setup, column 0 of each sum and the factors `k`; then the loop's
invariant at its start. -/
theorem abPre_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = off B (slot w 16)) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (h15 : s.gpr .r15 = BitVec.ofNat 64 n) (hR : (abR B Z w n s.mem).Ok)
    (huv : ((abR B Z w n s.mem).c oU).toNat + ((abR B Z w n s.mem).c oV).toNat ≤ 2 ^ 59)
    (hqr : ((abR B Z w n s.mem).c oQ).toNat + ((abR B Z w n s.mem).c oR).toNat ≤ 2 ^ 59) :
    WP isa (.block (rowStart 5 ++ ([.mov .rcx (.mem (wm oU)), .mov .rbp (.mem (wm oV))] : List Instr) ++
      ones oU oMu oV oMv .r10 ++ ([.mov32 .r11 (.imm 0), .mov32 .r12 (.imm 0)] : List Instr) ++
      term3 (px 0) (.reg .rcx) oMu .r10 .r11 .r12 ++ term3 (py 0) (.reg .rbp) oMv .r10 .r11 .r12 ++
      kOf oKd .r10 .r11 .r12 ++ shift3 .r10 .r11 .r12 ++
      ones oQ oMq oR oMr .r13 ++ ([.mov32 .r14 (.imm 0), .mov32 .rbx (.imm 0)] : List Instr) ++
      term3 (px 0) (.slot oQ) oMq .r13 .r14 .rbx ++ term3 (py 0) (.slot oR) oMr .r13 .r14 .rbx ++
      kOf oKe .r13 .r14 .rbx ++ shift3 .r13 .r14 .rbx ++ ([.alu .add .r8 (.imm 8)] : List Instr))) s fun t =>
      AbStart (abR B Z w n s.mem) t ∧ AbInv (abR B Z w n s.mem) t 0 t ∧
      Keep [.rax, .rdx, .rcx, .rbx, .rbp, .r8, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have hN := hR.nowrap; have hW := hR.win; have hL := hR.len; have hz := hR.z; have hn1 := hR.n1
  simp only [abR] at hW hL hz hN hn1
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (rowStart_ok 5 hdi h9 h15) fun s₁ ⟨a₁, b₁, m₁, k₁⟩ => ?_
  have hs₁ := hs.congr k₁.2.2
  have di₁ : s₁.gpr .rdi = off B (slot w 16) := (k₁.gpr (by decide)).trans hdi
  rw [show ∀ l : List Instr, ([Instr.mov .rcx (.mem (wm oU)), .mov .rbp (.mem (wm oV))] ++ l) =
    [Instr.mov .rcx (.mem (wm oU)), .mov .rbp (.mem (wm oV))] ++ l from fun _ => rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.rcx, .rbp] (Q := fun t => t.gpr .rcx = word s.mem B (slot w 16 + oU) ∧
    t.gpr .rbp = word s.mem B (slot w 16 + oV) ∧ t.mem = s₁.mem) (by
      xrun [ea_wm, di₁, offD, hs₁.ld (show slot w 16 + oU + 8 ≤ Z by unfold oU; omega),
        hs₁.ld (show slot w 16 + oV + 8 ≤ Z by unfold oV; omega), m₁]) rfl)
    fun s₂ ⟨⟨cx₂, bp₂, m₂⟩, k₂⟩ => ?_
  have m₂' : s₂.mem = s.mem := m₂.trans m₁
  have K2 := k₁.trans k₂
  have E₂ : AbEnv s₂ B Z (slot w 16) (slot w 21) (8 * (w + 2)) :=
    ⟨hs.congr K2.2.2, (K2.gpr (by decide)).trans hdi, (k₂.gpr (by decide)).trans a₁, (K2.gpr (by decide)).trans h9,
      by omega, by omega⟩
  rw [show ∀ (a b c d e f g : List Instr), a ++ (b ++ (c ++ (d ++ (e ++ (f ++ g))))) =
    (a ++ b ++ c ++ d ++ e ++ f) ++ g from fun _ _ _ _ _ _ _ => by simp only [List.append_assoc],
    WP.block_append_iff]
  refine WP.mono (abHalf_ok E₂ (by omega) (by omega) (cu := oU) (mu := oMu) (cv := oV) (mv := oMv) (o := oKd)
    (by decide) (by decide) (by decide) (by decide) (by decide) (lo := .r10) (mid := .r11) (top := .r12)
    (c₁ := .reg .rcx) (c₂ := .reg .rbp) ⟨by rw [cx₂, m₂'], by decide, by decide⟩
    ⟨by rw [bp₂, m₂'], by decide, by decide⟩ (fun r h => by cases h; decide) (fun r h => by cases h; decide)
    (by rw [m₂']; exact huv)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl rfl rfl rfl rfl rfl) fun s₃ ⟨nD, m₃, k₃⟩ => ?_
  rw [m₂'] at nD m₃
  have w3 : ∀ d, (d + 8 ≤ slot w 16 + oKd ∨ slot w 16 + oKd + 8 ≤ d) → d + 8 ≤ Z →
      word s₃.mem B d = word s.mem B d := fun d h1 h2 => by
    rw [m₃]; exact (writeW_outside _ B _ (d := slot w 16 + oKd) (by unfold oKd; omega)).word h1 (by omega)
  have wQ := w3 (slot w 16 + oQ) (by unfold oQ oKd; omega) (by unfold oQ; omega)
  have wMq := w3 (slot w 16 + oMq) (by unfold oMq oKd; omega) (by unfold oMq; omega)
  have wR := w3 (slot w 16 + oR) (by unfold oR oKd; omega) (by unfold oR; omega)
  have wMr := w3 (slot w 16 + oMr) (by unfold oMr oKd; omega) (by unfold oMr; omega)
  have wMi := w3 (slot w 16 + oMi) (by unfold oMi oKd; omega) (by unfold oMi; omega)
  have wa := w3 (slot w 21) (by unfold oKd; omega) (by omega)
  have wb := w3 (slot w 21 + 8 * (w + 2)) (by unfold oKd; omega) (by omega)
  have wp := w3 (slot w 21 + 4 * (8 * (w + 2))) (by unfold oKd; omega) (by omega)
  have K3 := K2.trans k₃
  have E₃ : AbEnv s₃ B Z (slot w 16) (slot w 21) (8 * (w + 2)) := E₂.congr (k₃.mono (by decide))
  rw [show ∀ (a b c d e f g : List Instr), a ++ (b ++ (c ++ (d ++ (e ++ (f ++ g))))) =
    (a ++ b ++ c ++ d ++ e ++ f) ++ g from fun _ _ _ _ _ _ _ => by simp only [List.append_assoc],
    WP.block_append_iff]
  refine WP.mono (abHalf_ok E₃ (by omega) (by omega) (cu := oQ) (mu := oMq) (cv := oR) (mv := oMr) (o := oKe)
    (by decide) (by decide) (by decide) (by decide) (by decide) (lo := .r13) (mid := .r14) (top := .rbx)
    (c₁ := .slot oQ) (c₂ := .slot oR) ⟨rfl, by unfold oQ; omega⟩ ⟨rfl, by unfold oR; omega⟩
    (fun r h => by cases h) (fun r h => by cases h)
    (by rw [wQ, wR]; exact hqr)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl rfl rfl rfl rfl rfl) fun s₄ ⟨nE, m₄, k₄⟩ => ?_
  rw [wQ, wMq, wR, wMr, wMi, wa, wb, wp] at nE
  rw [wQ, wMq, wR, wMr, wMi, wa, wb] at m₄
  have K4 := K3.trans k₄
  refine WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = off B (slot w 21 + 8 * (0 + 1)) ∧ t.mem = s₄.mem)
    (by
      xrun [((k₂.trans k₃).trans k₄).gpr (by decide) |>.trans a₁]
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add]; rfl) rfl)
    fun t ⟨⟨r8t, mt⟩, kt⟩ => ?_
  have KT := K4.trans kt
  have nD' : n3 t .r10 .r11 .r12 = n3 s₃ .r10 .r11 .r12 := by
    simp only [n3, (kt.gpr (by decide) : t.gpr .r10 = _), (kt.gpr (by decide) : t.gpr .r11 = _),
      (kt.gpr (by decide) : t.gpr .r12 = _), (k₄.gpr (by decide) : s₄.gpr .r10 = _),
      (k₄.gpr (by decide) : s₄.gpr .r11 = _), (k₄.gpr (by decide) : s₄.gpr .r12 = _)]
  have nE' : n3 t .r13 .r14 .rbx = n3 s₄ .r13 .r14 .rbx := by
    simp only [n3, (kt.gpr (by decide) : t.gpr .r13 = _), (kt.gpr (by decide) : t.gpr .r14 = _),
      (kt.gpr (by decide) : t.gpr .rbx = _)]
  have sD := sum_one (abR B Z w n s.mem) oU oMu oV oMv
  have sE := sum_one (abR B Z w n s.mem) oQ oMq oR oMr
  have dD := dsum_one (abR B Z w n s.mem) oU oMu oV oMv
  have dE := dsum_one (abR B Z w n s.mem) oQ oMq oR oMr
  simp only [abR, Rw.c, Rw.kv] at sD sE dD dE ⊢
  rw [sD] at dD; rw [sE] at dE
  refine ⟨⟨hR, (KT.gpr (by decide)).trans hdi, (KT.gpr (by decide)).trans h9, ?_, ?_, ?_, huv, hqr, ?_⟩,
    ⟨hs.congr KT.2.2, Keep.refl _ _, r8t, ?_, ?_, ?_, ?_, ?_⟩, KT.mono (by decide)⟩
  · rw [(k₂.trans (k₃.trans (k₄.trans kt))).gpr (by decide), b₁]
  · rw [(k₃.trans (k₄.trans kt)).gpr (by decide), cx₂]
  · rw [(k₃.trans (k₄.trans kt)).gpr (by decide), bp₂]
  · rw [mt, m₄, m₃]
    simp only [Rw.kv, sum_one, Rw.c, ← ofNat_mod64]
  · rw [mt]; exact Frm.refl _ _ _
  · simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]; rw [nD', nD, dD]
  · simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]; rw [nE', nE, dE]
  · rw [nD', nD, Nat.div_lt_iff_lt_mul (by decide)]
    have huv' := huv; simp only [abR, Rw.c] at huv'
    exact half_lt _ _ _ _ _ _ _ huv' (Nat.mod_lt _ (by decide))
  · rw [nE', nE, Nat.div_lt_iff_lt_mul (by decide)]
    have hqr' := hqr; simp only [abR, Rw.c] at hqr'
    exact half_lt _ _ _ _ _ _ _ hqr' (Nat.mod_lt _ (by decide))

/-- The sign words' terms of a sum of `abRow`, for its last column. -/
def Rw.sg (R : Rw) (c₁ m₁ c₂ m₂ : Nat) : Nat :=
  (R.c c₁).toNat * ((BitVec.setWidth 64 (0 : BitVec 32) - word R.m R.B (R.eA + 8 * R.n) >>> 63) ^^^ R.c m₁).toNat +
    (R.c c₂).toNat * ((BitVec.setWidth 64 (0 : BitVec 32) - word R.m R.B (R.eA + R.S + 8 * R.n) >>> 63) ^^^
      R.c m₂).toNat

/-- The last column of `abRow`: the word `lo` of `A + G` stored on top of `W`. -/
theorem ab_top {n W A D G : Nat} (hv : W + 2 ^ (64 * n) * A = D / 2 ^ 64) (hW : W < 2 ^ (64 * n)) :
    W + 2 ^ (64 * n) * ((A + G) % 2 ^ 64) = (D + 2 ^ (64 * (n + 1)) * G) / 2 ^ 64 % 2 ^ (64 * (n + 1)) := by
  rw [pow64_succ, show 2 ^ (64 * n) * 2 ^ 64 * G = 2 ^ 64 * (2 ^ (64 * n) * G) by grind,
    Nat.add_mul_div_left _ _ (by decide), ← hv, Nat.mod_mul,
    show W + 2 ^ (64 * n) * A + 2 ^ (64 * n) * G = W + 2 ^ (64 * n) * (A + G) by grind,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hW, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hW, Nat.zero_add]

/-- `abRow`'s stores of the last words. -/
theorem abStores_ok {s : State} {B : Addr} {Z e S : Nat} (hs : Scr s B Z) (h8 : s.gpr .r8 = off B (e + 8))
    (h9 : s.gpr .r9 = BitVec.ofNat 64 S) (hz : e + S + 8 ≤ Z) :
    WP isa (.block ([.store (px (-8)) .r10, .store (py (-8)) .r13] : List Instr)) s fun t =>
      t.mem = (s.mem.writeW (off B e) (s.gpr .r10)).writeW (off B (e + S)) (s.gpr .r13) ∧ Keep [] s t :=
  WP.keep [] (by xrun [ea_px, ea_py, h8, h9, off_m8, off_pym8, hs.st (show e + 8 ≤ Z by omega), hs.st hz]) rfl

/-- `abRow`: `(a, b)` replaced by the reductions of the two sums over their `n + 1` words and
their sign words. -/
theorem abRow_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = off B (slot w 16)) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (h15 : s.gpr .r15 = BitVec.ofNat 64 n) (hR : (abR B Z w n s.mem).Ok)
    (huv : ((abR B Z w n s.mem).c oU).toNat + ((abR B Z w n s.mem).c oV).toNat ≤ 2 ^ 59)
    (hqr : ((abR B Z w n s.mem).c oQ).toNat + ((abR B Z w n s.mem).c oR).toNat ≤ 2 ^ 59) :
    WP isa (seqs abRow) s fun t =>
      wv t.mem B (slot w 21) (n + 1) = ((abR B Z w n s.mem).dsum oU oMu oV oMv (n + 1) +
        2 ^ (64 * (n + 1)) * (abR B Z w n s.mem).sg oU oMu oV oMv) / 2 ^ 64 % 2 ^ (64 * (n + 1)) ∧
      wv t.mem B (slot w 21 + 8 * (w + 2)) (n + 1) = ((abR B Z w n s.mem).dsum oQ oMq oR oMr (n + 1) +
        2 ^ (64 * (n + 1)) * (abR B Z w n s.mem).sg oQ oMq oR oMr) / 2 ^ 64 % 2 ^ (64 * (n + 1)) ∧
      Frm B [(slot w 21, 8 * (n + 1)), (slot w 21 + 8 * (w + 2), 8 * (n + 1)), (slot w 16 + oKd, 8),
        (slot w 16 + oKe, 8)] s.mem t.mem ∧
      t.gpr .r15 = BitVec.ofNat 64 n ∧
      Keep [.rax, .rdx, .rcx, .rbx, .rbp, .r8, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have hN := hR.nowrap; have hW := hR.win; have hL := hR.len; have hz := hR.z; have hn1 := hR.n1
  simp only [abR] at hW hL hz hN hn1
  have e21 : slot w 21 = slot w 16 + 40 * (w + 2) := by unfold slot; omega
  unfold abRow
  simp only [seqs]
  refine WP.seq (WP.mono (abPre_ok hs hdi h9 h15 hR huv hqr) fun t₁ ⟨h₀, I₀, k₁⟩ => ?_)
  refine WP.seq (WP.mono (wp_upto (a := 1) (N := n + 1) (by omega)
    (fun j t => ∃ k, j = k + 1 ∧ AbInv (abR B Z w n s.mem) t₁ k t)
    (fun j hj hjN t ⟨k, hk, hI⟩ => by
      subst hk
      exact WP.mono (abStep_ok h₀ (show k + 1 ≤ n by omega) hI) fun t' ⟨z, h⟩ => ⟨z, k + 1, rfl, h⟩)
    (fun t h => h) ⟨0, rfl, I₀⟩) fun t₂ ⟨k, hk, I⟩ => ?_)
  rw [show k = n by omega] at I
  have hs₂ : Scr t₂ B Z := I.scr
  have r9₂ : t₂.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) := (I.keep.gpr (by decide)).trans h₀.r9
  have di₂ : t₂.gpr .rdi = off B (slot w 16) := (I.keep.gpr (by decide)).trans h₀.rdi
  have r8₂ : t₂.gpr .r8 = off B (slot w 21 + 8 * n + 8) := by
    rw [I.r8]; simp only [abR]; rw [show slot w 21 + 8 * (n + 1) = slot w 21 + 8 * n + 8 by omega]
  have exA : ∀ t : State, t.gpr .r8 = t₂.gpr .r8 → t.ea (px (-8)) = off B (slot w 21 + 8 * n) := fun t h => by
    rw [ea_px, h, r8₂, off_m8]
  have exB : ∀ t : State, t.gpr .r8 = t₂.gpr .r8 → t.gpr .r9 = t₂.gpr .r9 →
      t.ea (py (-8)) = off B (slot w 21 + 8 * n + 8 * (w + 2)) := fun t h h' => by
    rw [ea_py, h, h', r8₂, r9₂, off_pym8]
  -- the words the last column reads, as they were at the row's start
  have w₀ : ∀ d, (d + 8 ≤ slot w 16 + oKd ∨ slot w 16 + oKd + 8 ≤ d) →
      (d + 8 ≤ slot w 16 + oKe ∨ slot w 16 + oKe + 8 ≤ d) →
      (d + 8 ≤ slot w 21 ∨ (slot w 21 + 8 * n ≤ d ∧ d + 8 ≤ slot w 21 + 8 * (w + 2)) ∨
        slot w 21 + 8 * (w + 2) + 8 * n ≤ d) → d + 8 ≤ Z → word t₂.mem B d = word s.mem B d :=
    fun d h1 h2 h3 h4 => (I.memW (d := d) hR h3 h4).trans (h₀.memW h1 h2 h4)
  have wc : ∀ o, o + 8 ≤ 96 → (o + 8 ≤ oKd ∨ oKd + 8 ≤ o) → (o + 8 ≤ oKe ∨ oKe + 8 ≤ o) →
      word t₂.mem B (slot w 16 + o) = word s.mem B (slot w 16 + o) := fun o h1 h2 h3 =>
    w₀ _ (by omega) (by omega) (.inl (by omega)) (by omega)
  have wa : word t₂.mem B (slot w 21 + 8 * n) = word s.mem B (slot w 21 + 8 * n) :=
    w₀ _ (by unfold oKd; omega) (by unfold oKe; omega) (.inr (.inl ⟨by omega, by omega⟩)) (by omega)
  have wb : word t₂.mem B (slot w 21 + 8 * n + 8 * (w + 2)) = word s.mem B (slot w 21 + 8 * (w + 2) + 8 * n) := by
    rw [Nat.add_right_comm]
    exact w₀ _ (by unfold oKd; omega) (by unfold oKe; omega) (.inr (.inr (by omega))) (by omega)
  have bD := I.bD; have bE := I.bE
  have eb : ∀ l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ : List Instr,
      l₁ ++ (l₂ ++ (l₃ ++ (l₄ ++ (l₅ ++ (l₆ ++ (l₇ ++ (l₈ ++ (l₉ ++ l₁₀)))))))) =
      (l₁ ++ l₂) ++ ((l₃ ++ l₄) ++ ((l₅ ++ l₆) ++ ((l₇ ++ l₈) ++ (l₉ ++ l₁₀)))) := by
    intros; simp only [List.append_assoc]
  simp only [List.append_assoc]
  rw [eb, WP.block_append_iff]
  refine WP.mono (sgnTerm_ok (lo := .r10) (mid := .r11) (top := .r12) hs₂ di₂ (exA t₂ rfl) (by omega)
    (by unfold oU; omega) (by unfold oMu; omega) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl (by omega))
    fun t₃ ⟨n₃, m₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sgnTerm_ok (lo := .r13) (mid := .r14) (top := .rbx) (hs₂.congr k₃.2.2)
    ((k₃.gpr (by decide)).trans di₂) (exA t₃ (k₃.gpr (by decide))) (by omega)
    (by unfold oQ; omega) (by unfold oMq; omega) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl
    (by have : n3 t₃ .r13 .r14 .rbx = n3 t₂ .r13 .r14 .rbx := by
          simp only [n3, (k₃.gpr (by decide) : t₃.gpr .r13 = _), (k₃.gpr (by decide) : t₃.gpr .r14 = _),
            (k₃.gpr (by decide) : t₃.gpr .rbx = _)]
        omega))
    fun t₄ ⟨n₄, m₄, k₄⟩ => ?_
  have huv' := huv; simp only [abR, Rw.c] at huv'
  have hqr' := hqr; simp only [abR, Rw.c] at hqr'
  have m₃₂ : t₃.mem = t₂.mem := m₃
  have m₄₂ : t₄.mem = t₂.mem := m₄.trans m₃
  have d₄ : n3 t₄ .r10 .r11 .r12 = n3 t₃ .r10 .r11 .r12 := by
    simp only [n3, (k₄.gpr (by decide) : t₄.gpr .r10 = _), (k₄.gpr (by decide) : t₄.gpr .r11 = _),
      (k₄.gpr (by decide) : t₄.gpr .r12 = _)]
  have e₃ : n3 t₃ .r13 .r14 .rbx = n3 t₂ .r13 .r14 .rbx := by
    simp only [n3, (k₃.gpr (by decide) : t₃.gpr .r13 = _), (k₃.gpr (by decide) : t₃.gpr .r14 = _),
      (k₃.gpr (by decide) : t₃.gpr .rbx = _)]
  rw [wc oU (by decide) (by decide) (by decide), wc oMu (by decide) (by decide) (by decide), wa] at n₃
  rw [m₃₂, wc oQ (by decide) (by decide) (by decide), wc oMq (by decide) (by decide) (by decide), wa, e₃] at n₄
  have l1 := mul_word_le (word s.mem B (slot w 16 + oU)).toNat
    ((BitVec.setWidth 64 (0 : BitVec 32) - word s.mem B (slot w 21 + 8 * n) >>> 63) ^^^ word s.mem B (slot w 16 + oMu))
  have l2 := mul_word_le (word s.mem B (slot w 16 + oQ)).toNat
    ((BitVec.setWidth 64 (0 : BitVec 32) - word s.mem B (slot w 21 + 8 * n) >>> 63) ^^^ word s.mem B (slot w 16 + oMq))
  have K34 := k₃.trans k₄
  rw [WP.block_append_iff]
  refine WP.mono (sgnTerm_ok (lo := .r10) (mid := .r11) (top := .r12) (hs₂.congr K34.2.2)
    ((K34.gpr (by decide)).trans di₂) (exB t₄ (K34.gpr (by decide)) (K34.gpr (by decide))) (by omega)
    (by unfold oV; omega) (by unfold oMv; omega) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl
    (by rw [d₄, n₃]; omega)) fun t₅ ⟨n₅, m₅, k₅⟩ => ?_
  have K35 := K34.trans k₅
  have e₅ : n3 t₅ .r13 .r14 .rbx = n3 t₄ .r13 .r14 .rbx := by
    simp only [n3, (k₅.gpr (by decide) : t₅.gpr .r13 = _), (k₅.gpr (by decide) : t₅.gpr .r14 = _),
      (k₅.gpr (by decide) : t₅.gpr .rbx = _)]
  rw [WP.block_append_iff]
  refine WP.mono (sgnTerm_ok (lo := .r13) (mid := .r14) (top := .rbx) (hs₂.congr K35.2.2)
    ((K35.gpr (by decide)).trans di₂) (exB t₅ (K35.gpr (by decide)) (K35.gpr (by decide))) (by omega)
    (by unfold oR; omega) (by unfold oMr; omega) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl
    (by rw [e₅, n₄]; omega)) fun t₆ ⟨n₆, m₆, k₆⟩ => ?_
  have K36 := K35.trans k₆
  have m₅₂ : t₅.mem = t₂.mem := m₅.trans m₄₂
  rw [m₄₂, wc oV (by decide) (by decide) (by decide), wc oMv (by decide) (by decide) (by decide), wb, d₄, n₃] at n₅
  rw [m₅₂, wc oR (by decide) (by decide) (by decide), wc oMr (by decide) (by decide) (by decide), wb, e₅, n₄] at n₆
  have d₆ : n3 t₆ .r10 .r11 .r12 = n3 t₅ .r10 .r11 .r12 := by
    simp only [n3, (k₆.gpr (by decide) : t₆.gpr .r10 = _), (k₆.gpr (by decide) : t₆.gpr .r11 = _),
      (k₆.gpr (by decide) : t₆.gpr .r12 = _)]
  have r8₆ : t₆.gpr .r8 = off B (slot w 21 + 8 * n + 8) := (K36.gpr (by decide)).trans r8₂
  have r9₆ : t₆.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) := (K36.gpr (by decide)).trans r9₂
  rw [WP.block_append_iff]
  refine WP.mono (abStores_ok (hs₂.congr K36.2.2) r8₆ r9₆ (by omega)) fun t₇ ⟨m₇, k₇⟩ => ?_
  refine WP.mono (rowEnd_ok (n := n) 5 ((K36.trans k₇).gpr (by decide) |>.trans di₂)
    ((K36.trans k₇).gpr (by decide) |>.trans r9₂)
    (by rw [(K36.trans k₇).gpr (by decide), (I.keep.gpr (by decide)), h₀.r15]; rfl) (by omega))
    fun t ⟨r15t, mt, kt⟩ => ?_
  have m₆₂ : t₆.mem = t₂.mem := m₆.trans m₅₂
  have gD : (abR B Z w n s.mem).sg oU oMu oV oMv =
      (word s.mem B (slot w 16 + oU)).toNat * ((BitVec.setWidth 64 (0 : BitVec 32) - word s.mem B (slot w 21 + 8 * n) >>> 63)
        ^^^ word s.mem B (slot w 16 + oMu)).toNat +
      (word s.mem B (slot w 16 + oV)).toNat * ((BitVec.setWidth 64 (0 : BitVec 32) -
        word s.mem B (slot w 21 + 8 * (w + 2) + 8 * n) >>> 63) ^^^ word s.mem B (slot w 16 + oMv)).toNat := rfl
  have gE : (abR B Z w n s.mem).sg oQ oMq oR oMr =
      (word s.mem B (slot w 16 + oQ)).toNat * ((BitVec.setWidth 64 (0 : BitVec 32) - word s.mem B (slot w 21 + 8 * n) >>> 63)
        ^^^ word s.mem B (slot w 16 + oMq)).toNat +
      (word s.mem B (slot w 16 + oR)).toNat * ((BitVec.setWidth 64 (0 : BitVec 32) -
        word s.mem B (slot w 21 + 8 * (w + 2) + 8 * n) >>> 63) ^^^ word s.mem B (slot w 16 + oMr)).toNat := rfl
  have loD : (t₆.gpr .r10).toNat = (n3 t₂ .r10 .r11 .r12 + (abR B Z w n s.mem).sg oU oMu oV oMv) % 2 ^ 64 := by
    rw [gD]; have h := d₆.trans n₅; simp only [n3] at h ⊢; have := (t₆.gpr .r10).isLt; omega
  have loE : (t₆.gpr .r13).toNat = (n3 t₂ .r13 .r14 .rbx + (abR B Z w n s.mem).sg oQ oMq oR oMr) % 2 ^ 64 := by
    rw [gE]; have h := n₆; simp only [n3] at h ⊢; have := (t₆.gpr .r13).isLt; omega
  have oW₁ := writeW_outside t₆.mem B (t₆.gpr .r10) (d := slot w 21 + 8 * n) (by omega)
  have oW₂ := writeW_outside (t₆.mem.writeW (off B (slot w 21 + 8 * n)) (t₆.gpr .r10)) B (t₆.gpr .r13)
    (d := slot w 21 + 8 * n + 8 * (w + 2)) (by omega)
  refine ⟨?_, ?_, ?_, r15t, (k₁.trans (I.keep.trans ((K36.trans k₇).trans kt))).mono (by decide)⟩
  · rw [mt, m₇, oW₂.wv (.inl (by omega)) (by omega), wv_writeW_top _ _ _ _ _ (by omega), m₆₂, loD]
    exact ab_top I.valD (wv_lt _ _ _ _)
  · rw [mt, m₇, show slot w 21 + 8 * n + 8 * (w + 2) = slot w 21 + 8 * (w + 2) + 8 * n by omega,
      wv_writeW_top _ _ _ _ _ (by omega), oW₁.wv (.inr (by omega)) (by omega), m₆₂, loE]
    exact ab_top I.valE (wv_lt _ _ _ _)
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    rw [mt, m₇, oW₂ x (by omega), oW₁ x (by omega), m₆₂]
    have h1 := I.frm x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, abR]; omega)
    rw [h1, h₀.mem]
    simp only [abR]
    rw [writeW_outside _ B _ (d := slot w 16 + oKe) (by unfold oKe; omega) x (by unfold oKe at hx ⊢; omega),
      writeW_outside _ B _ (d := slot w 16 + oKd) (by unfold oKd; omega) x (by unfold oKd at hx ⊢; omega)]

end VG.Proof.Rsa.X86_64.InvB
