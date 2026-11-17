module

public import VerifiedGarbage.Impl.Bignum.X86_64.AdxSquareMac
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxStep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock

/-! ### `Bignum.X86_64.AdxSquareBlock`, which this module and modules that import it used -/

section

/-! The register-resident scalar multiply-add used by the square. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Adx
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem mac4_ok {s : State} {B : Addr} {Z e eb j : Nat} (hs : Scr s B Z) (h8 : s.gpr .r8 = off B e)
    (h9 : s.gpr .r9 = off B eb) (h14 : s.gpr .r14 = BitVec.ofNat 64 j) (hZ : e + 8 * j + 32 ≤ Z)
    (hZb : eb + 8 * j + 32 ≤ Z) :
    WP isa (.block AdxSquare.mac4) s fun t => t.cf = some false ∧ t.of = some false ∧
      t.gpr .rdx = s.gpr .rdx ∧
      (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat + 2 ^ 128 * (t.gpr .r13).toNat +
          2 ^ 192 * (t.gpr .r15).toNat + 2 ^ 256 * (t.gpr .rcx).toNat =
        (s.gpr .rdx).toNat * (word s.mem B (eb + 8 * j + 8 * 0)).toNat +
          2 ^ 64 * ((s.gpr .rdx).toNat * (word s.mem B (eb + 8 * j + 8 * 1)).toNat) +
          2 ^ 128 * ((s.gpr .rdx).toNat * (word s.mem B (eb + 8 * j + 8 * 2)).toNat) +
          2 ^ 192 * ((s.gpr .rdx).toNat * (word s.mem B (eb + 8 * j + 8 * 3)).toNat) +
          ((word s.mem B (e + 8 * j + 8 * 0)).toNat + 2 ^ 64 * (word s.mem B (e + 8 * j + 8 * 1)).toNat +
            2 ^ 128 * (word s.mem B (e + 8 * j + 8 * 2)).toNat + 2 ^ 192 * (word s.mem B (e + 8 * j + 8 * 3)).toNat) +
          (s.gpr .rcx).toNat ∧
      Keeps [.rsi, .rax, .r11, .r12, .r13, .r15, .rcx] s t := by
  obtain rb : ∀ k : Nat, k < 4 → readSrc s (.mem (ix .r9 .r14 (8 * (k : Int)))) = some (word s.mem B (eb + 8 * j + 8 * k)) :=
    fun k hk => readSrc_word hs (ea_ixk s h9 h14 k) (by omega_arith)
  obtain rt : ∀ k : Nat, k < 4 → readSrc s (.mem (ix .r8 .r14 (8 * (k : Int)))) = some (word s.mem B (e + 8 * j + 8 * k)) :=
    fun k hk => readSrc_word hs (ea_ixk s h8 h14 k) (by omega_arith)
  -- Reads through registers the steps keep.
  obtain kr : ∀ {rs : List Reg} {t : State}, Keeps rs s t → .r8 ∉ rs → .r9 ∉ rs → .r14 ∉ rs →
      (∀ k : Nat, k < 4 → readSrc t (.mem (ix .r9 .r14 (8 * (k : Int)))) = some (word s.mem B (eb + 8 * j + 8 * k))) ∧
      (∀ k : Nat, k < 4 → readSrc t (.mem (ix .r8 .r14 (8 * (k : Int)))) = some (word s.mem B (e + 8 * j + 8 * k))) :=
    fun K a b c => ⟨fun k hk => (K.readMem (by simpa [ix] using b) (by
        intro i hi; simp only [ix, Option.some.injEq] at hi; subst hi; exact c)).trans (rb k hk),
      fun k hk => (K.readMem (by simpa [ix] using a) (by
        intro i hi; simp only [ix, Option.some.injEq] at hi; subst hi; exact c)).trans (rt k hk)⟩
  unfold AdxSquare.mac4
  rw [WP.block_append_iff]
  refine WP.mono (xorRsi_ok s) fun s₂ ⟨_, c₂, o₂, K₂⟩ => ?_
  obtain ⟨rb₂, rt₂⟩ := kr K₂ (by decide) (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (wordA_ok s₂ (rb₂ 0 (by decide)) (rt₂ 0 (by decide)) c₂ o₂
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₃ ⟨a₁, p₁, ca₁, oa₁, e₀, k₃⟩ => ?_
  obtain K₃ := K₂.trans k₃
  obtain ⟨rb₃, rt₃⟩ := kr K₃ (by decide) (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (wordA_ok s₃ (rb₃ 1 (by decide)) (rt₃ 1 (by decide)) ca₁ oa₁
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₄ ⟨a₂, p₂, ca₂, oa₂, e₁, k₄⟩ => ?_
  obtain K₄ := K₃.trans k₄
  obtain ⟨rb₄, rt₄⟩ := kr K₄ (by decide) (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (wordA_ok s₄ (rb₄ 2 (by decide)) (rt₄ 2 (by decide)) ca₂ oa₂
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₅ ⟨a₃, p₃, ca₃, oa₃, e₂, k₅⟩ => ?_
  obtain K₅ := K₄.trans k₅
  obtain ⟨rb₅, rt₅⟩ := kr K₅ (by decide) (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (wordA_ok s₅ (rb₅ 3 (by decide)) (rt₅ 3 (by decide)) ca₃ oa₃
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₆ ⟨a₄, p₄, ca₄, oa₄, e₃, k₆⟩ => ?_
  refine WP.mono (close_ok s₆ ca₄ oa₄ (by decide)) fun t ⟨a₅, p₅, ca₅, oa₅, e₄, k₇⟩ => ?_
  obtain K := (K₅.trans k₆).trans k₇
  -- The registers along the way.
  obtain x₂ : s₂.gpr .rdx = s.gpr .rdx := K₂.gpr (by decide)
  obtain x₃ : s₃.gpr .rdx = s₂.gpr .rdx := k₃.gpr (by decide)
  obtain x₄ : s₄.gpr .rdx = s₂.gpr .rdx := (k₄.gpr (by decide)).trans x₃
  obtain x₅ : s₅.gpr .rdx = s₂.gpr .rdx := (k₅.gpr (by decide)).trans x₄
  obtain c₀ : s₂.gpr .rcx = s.gpr .rcx := K₂.gpr (by decide)
  obtain r11 : t.gpr .r11 = s₃.gpr .r11 := (k₇.gpr (by decide)).trans ((k₆.gpr (by decide)).trans
    ((k₅.gpr (by decide)).trans (k₄.gpr (by decide))))
  obtain r12 : t.gpr .r12 = s₄.gpr .r12 := (k₇.gpr (by decide)).trans ((k₆.gpr (by decide)).trans (k₅.gpr (by decide)))
  obtain r13 : t.gpr .r13 = s₅.gpr .r13 := (k₇.gpr (by decide)).trans (k₆.gpr (by decide))
  obtain r15 : t.gpr .r15 = s₆.gpr .r15 := k₇.gpr (by decide)
  rw [x₂] at e₀
  rw [x₃, x₂] at e₁
  rw [x₄, x₂] at e₂
  rw [x₅, x₂] at e₃
  rw [c₀] at e₀
  simp only [Bool.toNat_false] at e₀
  obtain hb : ∀ k, (s.gpr .rdx).toNat * (word s.mem B (eb + 8 * j + 8 * k)).toNat ≤
      (2 ^ 64 - 1) * (2 ^ 64 - 1) := fun k => Nat.mul_le_mul (by have := (s.gpr .rdx).isLt; omega_arith)
        (by have := (word s.mem B (eb + 8 * j + 8 * k)).isLt; omega_arith)
  obtain ⟨z₁, z₂, e⟩ := halfA_arith (hb 0) (hb 1) (hb 2) (hb 3) (word s.mem B (e + 8 * j + 8 * 0)).isLt
    (word s.mem B (e + 8 * j + 8 * 1)).isLt (word s.mem B (e + 8 * j + 8 * 2)).isLt
    (word s.mem B (e + 8 * j + 8 * 3)).isLt (s.gpr .rcx).isLt (s₃.gpr .r11).isLt (s₄.gpr .r12).isLt
    (s₅.gpr .r13).isLt (s₆.gpr .r15).isLt (t.gpr .rcx).isLt e₀ e₁ e₂ e₃ e₄
  refine ⟨?_, ?_, ?_, ?_, K.mono (by decide)⟩
  · rw [ca₅, Bool.toNat_eq_zero.mp z₁]
  · rw [oa₅, Bool.toNat_eq_zero.mp z₂]
  · rw [(k₇.gpr (by decide)).trans ((k₆.gpr (by decide)).trans x₅)]
    exact x₂
  · rw [r11, r12, r13, r15]; exact e


/-- Four multiply-add words, including the accumulator stores. -/
theorem mac4Store_ok {s : State} {B : Addr} {Z e eb j w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B eb)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 j) (hbx : s.gpr .rbx = BitVec.ofNat 64 w)
    (hZ : e + 8 * j + 32 ≤ Z) (hZb : eb + 8 * j + 32 ≤ Z)
    (hj : j + 4 < 2 ^ 64) (hw : w < 2 ^ 64) :
    WP isa (.block AdxSquare.mac4Store) s fun t =>
      wv t.mem B (e + 8 * j) 4 + 2 ^ 256 * (t.gpr .rcx).toNat =
        wv s.mem B (e + 8 * j) 4 + (s.gpr .rdx).toNat * wv s.mem B (eb + 8 * j) 4 +
          (s.gpr .rcx).toNat ∧
      Outside B (e + 8 * j) 32 s.mem t.mem ∧ t.gpr .r14 = BitVec.ofNat 64 (j + 4) ∧
      t.zf = some (decide (j + 4 = w)) ∧
      Keep [.rsi, .rax, .r11, .r12, .r13, .r15, .rcx, .r14] s t := by
  have hn := hs.nowrap
  rw [show AdxSquare.mac4Store = AdxSquare.mac4 ++ tail from rfl, WP.block_append_iff]
  refine WP.mono (mac4_ok hs h8 h9 h14 hZ hZb) fun a ⟨_, _, _, ea, ka⟩ => ?_
  refine WP.mono (tail_ok (hs.congr ka.2.2.2) ((ka.gpr (by decide)).trans h8)
    ((ka.gpr (by decide)).trans h14) ((ka.gpr (by decide)).trans hbx) hZ hj hw)
    fun t ⟨hm, h14', hz, kt⟩ => ?_
  obtain ⟨hv, ho⟩ := write4 a.mem B (e + 8 * j) (a.gpr .r11) (a.gpr .r12) (a.gpr .r13) (a.gpr .r15) (by omega_arith)
  rw [← hm] at hv ho
  rw [ka.2.1] at ho
  refine ⟨?_, ho, h14', hz, (ka.keep.trans kt).mono (by decide)⟩
  rw [hv, kt.gpr (by decide), wv4 s.mem B (e + 8 * j), wv4 s.mem B (eb + 8 * j), mul_w4]
  omega_arith

/-- The single-word remainder has the same multiply-add equation. -/
theorem mac1_ok {s : State} {B : Addr} {Z e eb j : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B eb)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 j)
    (hZ : e + 8 * j + 8 ≤ Z) (hZb : eb + 8 * j + 8 ≤ Z) :
    WP isa (.block AdxSquare.mac1) s fun t => t.cf = some false ∧ t.of = some false ∧
      (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .rcx).toNat =
        (s.gpr .rdx).toNat * (word s.mem B (eb + 8 * j)).toNat +
          (word s.mem B (e + 8 * j)).toNat + (s.gpr .rcx).toNat ∧
      Keeps [.rsi, .rax, .r11, .rcx] s t := by
  obtain rb : readSrc s (.mem (ix .r9 .r14 (8 * 0))) = some (word s.mem B (eb + 8 * j)) :=
    readSrc_word hs (by simpa using ea_ixk s h9 h14 0) hZb
  obtain rt : readSrc s (.mem (ix .r8 .r14 (8 * 0))) = some (word s.mem B (e + 8 * j)) :=
    readSrc_word hs (by simpa using ea_ixk s h8 h14 0) hZ
  unfold AdxSquare.mac1
  rw [WP.block_append_iff]
  obtain pre : WP isa (.block [.alu32 .xor .rsi (.reg .rsi), .mov .rax (.reg .rcx)]) s fun t =>
      t.cf = some false ∧ t.of = some false ∧ t.gpr .rax = s.gpr .rcx ∧ Keeps [.rsi, .rax] s t := by
    refine WP.mono (WP.keep [.rsi, .rax] (Q := fun t => t.cf = some false ∧ t.of = some false ∧
      t.gpr .rax = s.gpr .rcx ∧ t.mem = s.mem) (by xrun; rfl) rfl) fun t ⟨h, k⟩ =>
      ⟨h.1, h.2.1, h.2.2.1, k.1, h.2.2.2, k.2⟩
  refine WP.mono pre fun a ⟨ca, oa, ra, ka⟩ => ?_
  rw [WP.block_append_iff]
  obtain rb' := (ka.readMem (by decide) (by intro i hi; cases hi; decide)).trans rb
  obtain rt' := (ka.readMem (by decide) (by intro i hi; cases hi; decide)).trans rt
  refine WP.mono (wordA_ok a rb' rt' ca oa (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun b ⟨c, o, cb, ob, eb', kb⟩ => ?_
  refine WP.mono (close_ok b cb ob (by decide)) fun t ⟨c', o', ct, ot, et, kt⟩ => ?_
  obtain dx : a.gpr .rdx = s.gpr .rdx := ka.gpr (by decide)
  obtain lo : t.gpr .r11 = b.gpr .r11 := kt.gpr (by decide)
  rw [dx, ra] at eb'
  simp only [Bool.toNat_false] at eb'
  obtain hp : (s.gpr .rdx).toNat * (word s.mem B (eb + 8 * j)).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by have := (s.gpr .rdx).isLt; omega_arith) (by have := (word s.mem B (eb + 8 * j)).isLt; omega_arith)
  obtain ht := (word s.mem B (e + 8 * j)).isLt
  obtain hc := (s.gpr .rcx).isLt
  obtain zl : c'.toNat = 0 ∧ o'.toNat = 0 := by omega_arith
  refine ⟨?_, ?_, ?_, ((ka.trans kb).trans kt).mono (by decide)⟩
  · rw [ct, Bool.toNat_eq_zero.mp zl.1]
  · rw [ot, Bool.toNat_eq_zero.mp zl.2]
  · rw [lo]; omega_arith

/-- The remainder word, including its store and loop count. -/
theorem mac1Store_ok {s : State} {B : Addr} {Z e eb j w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B eb)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 j) (hbx : s.gpr .rbx = BitVec.ofNat 64 w)
    (hZ : e + 8 * j + 8 ≤ Z) (hZb : eb + 8 * j + 8 ≤ Z)
    (hj : j + 1 < 2 ^ 64) (hw : w < 2 ^ 64) :
    WP isa (.block AdxSquare.mac1Store) s fun t =>
      wv t.mem B (e + 8 * j) 1 + 2 ^ 64 * (t.gpr .rcx).toNat =
        wv s.mem B (e + 8 * j) 1 + (s.gpr .rdx).toNat * wv s.mem B (eb + 8 * j) 1 +
          (s.gpr .rcx).toNat ∧
      Outside B (e + 8 * j) 8 s.mem t.mem ∧ t.gpr .r14 = BitVec.ofNat 64 (j + 1) ∧
      t.zf = some (decide (j + 1 = w)) ∧ Keep [.rsi, .rax, .r11, .rcx, .r14] s t := by
  have hn := hs.nowrap
  unfold AdxSquare.mac1Store
  rw [WP.block_append_iff]
  refine WP.mono (mac1_ok hs h8 h9 h14 hZ hZb) fun a ⟨_, _, ea, ka⟩ => ?_
  obtain a8 : a.gpr .r8 = off B e := (ka.gpr (by decide)).trans h8
  obtain a14 : a.gpr .r14 = BitVec.ofNat 64 j := (ka.gpr (by decide)).trans h14
  obtain abx : a.gpr .rbx = BitVec.ofNat 64 w := (ka.gpr (by decide)).trans hbx
  obtain hsa : Scr a B Z := hs.congr ka.2.2.2
  refine WP.mono (WP.keep [.r14] (Q := fun t =>
      t.mem = a.mem.writeW (off B (e + 8 * j)) (a.gpr .r11) ∧
      t.gpr .r14 = BitVec.ofNat 64 (j + 1) ∧ t.zf = some (decide (j + 1 = w)))
    (by xrun [State.ea, ix, a8, a14, addrK0, Nat.mul_zero, Nat.add_zero, hsa.st hZ, a14, abx, ofNat_add_one, ofNat_sub_beq hj hw]) rfl)
    fun t ⟨⟨hm, h14', hz⟩, kt⟩ => ?_
  obtain ho := writeW_outside a.mem B (a.gpr .r11) (d := e + 8 * j) (by omega_arith)
  rw [← hm, ka.2.1] at ho
  refine ⟨?_, ho, h14', hz, (ka.keep.trans kt).mono (by decide)⟩
  simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.add_zero, Nat.one_mul, Nat.zero_add]
  rw [hm, word_writeW_self, kt.gpr (by decide)]
  omega_arith

end VG.Proof.Bignum.X86_64.AdxSquare

end

end

/-! Accumulating the ADX square's multiply-add blocks into a row. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- A multiply-add row: `[r8] += rdx · [r9]` over `rbp = n > 0` words, its
carry word into `rcx` and `r14 = n`, as the square's cross products and its
reduction use it. -/
structure RowOk (row : Prog isa) : Prop where
  ok : ∀ {s : State} {B : Addr} {Z e eb n : Nat}, Scr s B Z → s.gpr .r8 = off B e →
    s.gpr .r9 = off B eb → s.gpr .rbp = BitVec.ofNat 64 n → 0 < n → n < 2 ^ 60 → e + 8 * n ≤ Z →
    eb + 8 * n ≤ Z → (eb + 8 * n ≤ e ∨ e + 8 * n ≤ eb) →
    WP isa row s fun t =>
      wv t.mem B e n + 2 ^ (64 * n) * (t.gpr .rcx).toNat =
        wv s.mem B e n + (s.gpr .rdx).toNat * wv s.mem B eb n ∧
      Outside B e (8 * n) s.mem t.mem ∧ t.gpr .r14 = BitVec.ofNat 64 n ∧
      Keep [.rsi, .rax, .r11, .r12, .r13, .r15, .rcx, .r14, .rbx] s t

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
  have rT : wv t.mem B (e + 8 * j) n = wv s₀.mem B (e + 8 * j) n := hI.out.wv (by omega_arith) (by omega_arith)
  have rB : wv t.mem B (eb + 8 * j) n = wv s₀.mem B (eb + 8 * j) n := hI.out.wv (by omega_arith) (by omega_arith)
  have rL : wv t'.mem B e j = wv t.mem B e j := ho.wv (by omega_arith) (by omega_arith)
  rw [rT, rB, hI.keep.gpr (by decide)] at hv
  refine ⟨hI.scr.congr hk.2.2, (hI.keep.trans hk).mono (by decide), h14, ?_, ?_⟩
  · exact (hI.out.mono (o' := e) (n' := 8 * (j + n)) (Nat.le_refl _) (by omega_arith)).trans
      (ho.mono (o' := e) (n' := 8 * (j + n)) (by omega_arith) (by omega_arith))
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
  refine wp_upto (a := a) (N := w / 4) (by omega_arith) (fun k t => RowInv s₀ B Z e eb (4 * k) t ∧ t.gpr .rbx = BitVec.ofNat 64 w) ?_ ?_ ⟨hI, hbx⟩
  · intro k _ hk t h
    obtain ⟨h, hbx'⟩ := h
    have kp := h.keep
    refine WP.mono (mac4Store_ok h.scr ((kp.gpr (by decide)).trans h8)
      ((kp.gpr (by decide)).trans h9) h.r14 hbx'
      (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun t' ⟨hv, ho, h14, hz, kt⟩ => ⟨?_, ?_, (kt.gpr (by decide)).trans hbx'⟩
    · rw [hz]; congr 1; exact decide_eq_decide.mpr (by omega_arith)
    · have step := h.step (by omega_arith : 4 * k + 4 ≤ w) hZ hZb sb hv ho h14 (kt.mono (by decide))
      rw [show 4 * (k + 1) = 4 * k + 4 by omega_arith]
      exact step
  · intro t h
    have he : 4 * (w / 4) = w := by omega_arith
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
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun t' ⟨hv, ho, h14, hz, kt⟩ => ⟨hz, ?_, (kt.gpr (by decide)).trans hbx'⟩
  exact h.step (by omega_arith : j + 1 ≤ w) hZ hZb sb hv ho h14 (kt.mono (by decide))

/-- Round a public word count down to a multiple of four. -/
theorem round4 (w : Nat) (hw : w < 2 ^ 64) :
    let q := BitVec.ofNat 64 w >>> 2
    q + q + (q + q) = BitVec.ofNat 64 (4 * (w / 4)) := by
  dsimp only
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_arith

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
  exact ofNat_sub_beq (by omega_arith) (by decide)

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
  refine WP.seq (WP.mono (rowStart_ok hbp (by omega_arith)) fun s₁ ⟨hbx₁, hcx₁, h14₁, hz₁, hm₁, k₁⟩ => ?_)
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
      exact blocks_ok (a := 0) h8₁ h9₁ hbx₁ (by omega_arith) (by omega_arith) (by omega_arith)
        (by omega_arith) (by omega_arith) (by omega_arith) hi₁
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
    xrun [hbp₂, hI₂.r14, ofNat_sub_beq (show 4 * (w / 4) < 2 ^ 64 by omega_arith) (show w < 2 ^ 64 by omega_arith)]
  refine WP.seq (WP.mono mid fun s₃ ⟨hbx₃, hz₃, hm₃, h14₃, k₃⟩ => ?_)
  have hI₃ : RowInv s₁ B Z e eb (4 * (w / 4)) s₃ :=
    ⟨hI₂.scr.congr k₃.2.2, (hI₂.keep.trans k₃).mono (by decide),
      h14₃.trans hI₂.r14, hm₃ ▸ hI₂.out, by
        rw [hm₃, k₃.gpr (by decide)]; exact hI₂.val⟩
  have last : WP isa (.ite .ne (.loop (.block AdxSquare.mac1Store) .ne) (.block [])) s₃
      (RowInv s₁ B Z e eb w) := by
    by_cases he : 4 * (w / 4) = w
    · refine WP.ite false (by simp [eval, hz₃, he]) (by simp) (fun _ => WP.block_nil ?_)
      exact he ▸ hI₃
    · refine WP.ite true (by simp [eval, hz₃, he]) (fun _ => ?_) (by simp)
      exact remainder_ok h8₁ h9₁ hbx₃ (by omega_arith) hw hZ hZb sb hI₃
  refine WP.mono last fun t h => ⟨?_, ?_, h.r14, (k₁.trans h.keep).mono (by decide)⟩
  · have hv := h.val
    rw [hm₁, k₁.gpr (by decide), hcx₁] at hv
    simpa using hv
  · have ho := h.out
    rw [hm₁] at ho
    exact ho

end VG.Proof.Bignum.X86_64.AdxSquare
