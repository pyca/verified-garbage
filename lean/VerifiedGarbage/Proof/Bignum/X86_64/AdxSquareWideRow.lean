module

public import VerifiedGarbage.Impl.Bignum.X86_64.AdxSquareWide
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxSquareMac
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxStep
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxSquare

/-! ### `Bignum.X86_64.AdxSquareDiagonalStep`, which this module and modules that import it used -/

section

/-! Storing a pair of words after the square's diagonal addition. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem wv2 (m : Mem) (B : Addr) (d : Nat) :
    wv m B d 2 = (word m B d).toNat + 2 ^ 64 * (word m B (d + 8)).toNat := by
  simp only [wv, Nat.zero_add, Nat.add_zero, Nat.mul_zero, Nat.mul_one, Nat.pow_zero, Nat.one_mul]

theorem write2 (m : Mem) (B : Addr) (d : Nat) (x y : BitVec 64) (hd : d + 16 ≤ 2 ^ 64) :
    let m' := (m.writeW (off B d) x).writeW (off B (d + 8)) y
    wv m' B d 2 = x.toNat + 2 ^ 64 * y.toNat ∧ Outside B d 16 m m' := by
  intro m'
  have ho := writeW_outside m B x (d := d) (by omega_using [hd])
  have ho' := writeW_outside (m.writeW (off B d) x) B y (d := d + 8) (by omega_using [hd])
  refine ⟨?_, (ho.mono (Nat.le_refl _) (by omega_using [])).trans (ho'.mono (by omega_using []) (by omega_using []))⟩
  rw [wv2, ho'.word (by omega_using []) (by omega_using [hd]), word_writeW_self, word_writeW_self]

/-- A diagonal step's core: `rbx:r12:r11 = 2 (r11 + 2⁶⁴ r12) + rdx² + r15`,
as the diagonal step computes it. -/
structure CoreOk (core : List Instr) : Prop where
  ok : ∀ s : State, WP isa (.block core) s fun t =>
    (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat + 2 ^ 128 * (t.gpr .rbx).toNat =
      2 * ((s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .r12).toNat) +
        (s.gpr .rdx).toNat * (s.gpr .rdx).toNat + (s.gpr .r15).toNat ∧
    Keeps [.rsi, .rbx, .rax, .rcx, .r11, .r12] s t

/-- One pair of stored words, the exact carry, and public loop counts. -/
theorem diagonalStepWith_ok {core : List Instr} (hc : CoreOk core) {s : State} {B : Addr} {Z A eb i w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B A) (h9 : s.gpr .r9 = off B eb)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 i) (h14 : s.gpr .r14 = BitVec.ofNat 64 (2 * i))
    (h10 : s.gpr .r10 = BitVec.ofNat 64 w) (hi : i < w) (hw : w < 2 ^ 60)
    (hA : A + 16 * (i + 1) ≤ Z) (hb : eb + 8 * (i + 1) ≤ Z) :
    WP isa (AdxSquare.diagonalStepWith core) s fun t =>
      wv t.mem B (A + 16 * i) 2 + 2 ^ 128 * (t.gpr .r15).toNat =
        2 * wv s.mem B (A + 16 * i) 2 +
          (word s.mem B (eb + 8 * i)).toNat * (word s.mem B (eb + 8 * i)).toNat + (s.gpr .r15).toNat ∧
      Outside B (A + 16 * i) 16 s.mem t.mem ∧
      t.gpr .rbp = BitVec.ofNat 64 (i + 1) ∧ t.gpr .r14 = BitVec.ofNat 64 (2 * (i + 1)) ∧
      t.zf = some (decide (i + 1 = w)) ∧
      Keep [.rdx, .r11, .r12, .rsi, .rbx, .rax, .rcx, .r15, .rbp, .r14] s t := by
  have hn := hs.nowrap
  have ad : off B A + BitVec.ofNat 64 (2 * i) * BitVec.ofNat 64 8 + BitVec.ofInt 64 0 = off B (A + 16 * i) := by
    rw [addrK0]; congr 1; omega_using []
  have ad' : off B A + BitVec.ofNat 64 (2 * i) * BitVec.ofNat 64 8 + BitVec.ofInt 64 8 = off B (A + 16 * i + 8) := by
    rw [addrK1]; congr 1; omega_using []
  have src : off B eb + BitVec.ofNat 64 i * BitVec.ofNat 64 8 + BitVec.ofInt 64 0 = off B (eb + 8 * i) := by
    rw [addrK0]; congr 1
  have head : WP isa (.block AdxSquare.diagonalHead) s fun t =>
      t.gpr .rdx = word s.mem B (eb + 8 * i) ∧ t.gpr .r11 = word s.mem B (A + 16 * i) ∧
      t.gpr .r12 = word s.mem B (A + 16 * i + 8) ∧ t.mem = s.mem ∧ Keep [.rdx, .r11, .r12] s t := by
    refine WP.mono (WP.keep [.rdx, .r11, .r12] (Q := fun t =>
      t.gpr .rdx = word s.mem B (eb + 8 * i) ∧ t.gpr .r11 = word s.mem B (A + 16 * i) ∧
      t.gpr .r12 = word s.mem B (A + 16 * i + 8) ∧ t.mem = s.mem) ?_ rfl)
      fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
    unfold AdxSquare.diagonalHead
    xrun [State.ea, ix, h8, h9, hbp, h14, ad, ad', src,
      hs.ld (show eb + 8 * i + 8 ≤ Z by omega_using [hb]), hs.ld (show A + 16 * i + 8 ≤ Z by omega_using [hA]),
      hs.ld (show A + 16 * i + 8 + 8 ≤ Z by omega_using [hA])]
  unfold AdxSquare.diagonalStepWith
  refine WP.seq (WP.mono head fun s₁ ⟨hdx, h11, h12, hm₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (hc.ok s₁) fun s₂ ⟨hv, k₂⟩ => ?_)
  have k12 := k₁.trans k₂.keep
  have h8₂ : s₂.gpr .r8 = off B A := (k12.gpr (by decide)).trans h8
  have h14₂ : s₂.gpr .r14 = BitVec.ofNat 64 (2 * i) := (k12.gpr (by decide)).trans h14
  have hbp₂ : s₂.gpr .rbp = BitVec.ofNat 64 i := (k12.gpr (by decide)).trans hbp
  have h10₂ : s₂.gpr .r10 = BitVec.ofNat 64 w := (k12.gpr (by decide)).trans h10
  have hs₂ := hs.congr k12.2.2
  have cnt : BitVec.ofNat 64 (2 * i) + 2 = BitVec.ofNat 64 (2 * (i + 1)) := by
    rw [show 2 * (i + 1) = 2 * i + 2 by omega_using [], BitVec.ofNat_add]; rfl
  have tail : WP isa (.block AdxSquare.diagonalTail) s₂ fun t =>
      t.mem = (s₂.mem.writeW (off B (A + 16 * i)) (s₂.gpr .r11)).writeW (off B (A + 16 * i + 8)) (s₂.gpr .r12) ∧
      t.gpr .r15 = s₂.gpr .rbx ∧ t.gpr .rbp = BitVec.ofNat 64 (i + 1) ∧
      t.gpr .r14 = BitVec.ofNat 64 (2 * (i + 1)) ∧ t.zf = some (decide (i + 1 = w)) ∧
      Keep [.r15, .rbp, .r14] s₂ t := by
    refine WP.mono (WP.keep [.r15, .rbp, .r14] (Q := fun t =>
      t.mem = (s₂.mem.writeW (off B (A + 16 * i)) (s₂.gpr .r11)).writeW (off B (A + 16 * i + 8)) (s₂.gpr .r12) ∧
      t.gpr .r15 = s₂.gpr .rbx ∧ t.gpr .rbp = BitVec.ofNat 64 (i + 1) ∧
      t.gpr .r14 = BitVec.ofNat 64 (2 * (i + 1)) ∧ t.zf = some (decide (i + 1 = w))) ?_ rfl)
      fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩
    unfold AdxSquare.diagonalTail
    xrun [State.ea, ix, h8₂, h14₂, hbp₂, h10₂, ad, ad', cnt, ofNat_add_one,
      hs₂.st (show A + 16 * i + 8 ≤ Z by omega_using [hA]), hs₂.st (show A + 16 * i + 8 + 8 ≤ Z by omega_using [hA]),
      ofNat_sub_beq (show i + 1 < 2 ^ 64 by omega_using [hi, hw]) (show w < 2 ^ 64 by omega_using [hw])]
  refine WP.mono tail fun t ⟨hm, h15', hbp', h14', hz, kt⟩ => ?_
  obtain ⟨hval, ho⟩ := write2 s₂.mem B (A + 16 * i) (s₂.gpr .r11) (s₂.gpr .r12) (by omega_using [hA, hn])
  rw [← hm] at hval ho
  rw [k₂.2.1, hm₁] at ho
  refine ⟨?_, ho, hbp', h14', hz, (k12.trans kt).mono (by decide)⟩
  rw [hval, h15', wv2]
  rw [h11, h12, hdx, k₁.gpr (by decide)] at hv
  exact hv

end VG.Proof.Bignum.X86_64.AdxSquare

end

end

/-! ### `Bignum.X86_64.AdxSquareRow`, which this module and modules that import it used -/

section

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

end

end

/-! ## AdxSquareWideWord -/

@[expose] public section

section

/-! Word-level equations retain both carry flags across stores. -/
namespace VG.Proof.Bignum.X86_64.AdxSquareWide
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem store_ok {s : State} {B : Addr} {Z e j k : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B e) (h14 : s.gpr .r14 = BitVec.ofNat 64 j)
    (hZ : e + 8 * j + 8 * k + 8 ≤ Z) :
    WP isa (.block [.store (ix .r8 .r14 (8 * k)) .r11]) s fun t =>
      t.mem = s.mem.writeW (off B (e + 8 * j + 8 * k)) (s.gpr .r11) ∧
      t.cf = s.cf ∧ t.of = s.of ∧ Keep [] s t := by
  refine WP.mono (WP.keep [] (Q := fun t =>
      t.mem = s.mem.writeW (off B (e + 8 * j + 8 * k)) (s.gpr .r11) ∧
      t.cf = s.cf ∧ t.of = s.of) ?_ rfl) fun t ⟨h, kt⟩ => ⟨h.1, h.2.1, h.2.2, kt⟩
  xrun [ea_ixk s h8 h14 k, hs.st hZ]

theorem word_ok {s : State} {B : Addr} {Z e eb j k : Nat} {hi prev : Reg} {c o : Bool}
    (hs : Scr s B Z) (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B eb)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 j)
    (hZ : e + 8 * j + 8 * k + 8 ≤ Z) (hZb : eb + 8 * j + 8 * k + 8 ≤ Z)
    (hc : s.cf = some c) (ho : s.of = some o)
    (d1 : hi ≠ .r11) (d2 : prev ≠ hi) (d3 : prev ≠ .r11) (d4 : hi ≠ .r8) (d5 : hi ≠ .r14) :
    WP isa (.block (AdxSquareWide.word k hi prev)) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      (word t.mem B (e + 8 * j + 8 * k)).toNat +
        2 ^ 64 * ((t.gpr hi).toNat + c'.toNat + o'.toNat) =
        (word s.mem B (e + 8 * j + 8 * k)).toNat +
        (s.gpr .rdx).toNat * (word s.mem B (eb + 8 * j + 8 * k)).toNat +
        (s.gpr prev).toNat + c.toNat + o.toNat ∧
      Outside B (e + 8 * j + 8 * k) 8 s.mem t.mem ∧ Keep [hi, .r11] s t := by
  have hn := hs.nowrap
  unfold AdxSquareWide.word
  rw [WP.block_append_iff]
  refine WP.mono (wordA_ok s (readSrc_word hs (ea_ixk s h9 h14 k) hZb)
    (readSrc_word hs (ea_ixk s h8 h14 k) hZ) hc ho d1 d2 d3 d4 (by decide) d5 (by decide))
    fun a ⟨c', o', ca, oa, eq, ka⟩ => ?_
  refine WP.mono (store_ok (hs.congr ka.2.2.2) ((ka.gpr (by simp [Ne.symm d4])).trans h8)
    ((ka.gpr (by simp [Ne.symm d5])).trans h14) hZ) fun t ⟨hm, ct, ot, kt⟩ => ?_
  refine ⟨c', o', ct.trans ca, ot.trans oa, ?_, ?_, (ka.keep.trans kt).mono (by simp)⟩
  · rw [kt.gpr (by simp), hm, word_writeW_self]
    omega_using [eq]
  · rw [hm, ka.2.1]; exact writeW_outside _ _ _ (by omega_arith)
end VG.Proof.Bignum.X86_64.AdxSquareWide

end

/-! ## AdxSquareWidePair -/
section

/-! A pair returns the high half to `rcx`, leaving both flags live. -/
namespace VG.Proof.Bignum.X86_64.AdxSquareWide
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem pair_ok {s : State} {B : Addr} {Z e eb j k : Nat} {c o : Bool}
    (hs : Scr s B Z) (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B eb)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 j)
    (hZ : e + 8 * j + 8 * k + 16 ≤ Z) (hZb : eb + 8 * j + 8 * k + 16 ≤ Z)
    (sb : eb + 8 * j + 8 * k + 16 ≤ e + 8 * j + 8 * k ∨
      e + 8 * j + 8 * k + 16 ≤ eb + 8 * j + 8 * k)
    (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block (AdxSquareWide.pair k)) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      wv t.mem B (e + 8 * j + 8 * k) 2 +
        2 ^ 128 * ((t.gpr .rcx).toNat + c'.toNat + o'.toNat) =
        wv s.mem B (e + 8 * j + 8 * k) 2 +
        (s.gpr .rdx).toNat * wv s.mem B (eb + 8 * j + 8 * k) 2 +
        (s.gpr .rcx).toNat + c.toNat + o.toNat ∧
      Outside B (e + 8 * j + 8 * k) 16 s.mem t.mem ∧ Keep [.rax, .r11, .rcx] s t := by
  have hn := hs.nowrap
  unfold AdxSquareWide.pair
  rw [WP.block_append_iff]
  refine WP.mono (word_ok hs h8 h9 h14 (by omega_arith) (by omega_arith) hc ho
    (by decide) (by decide) (by decide) (by decide) (by decide))
    fun a ⟨ca, oa, hca, hoa, ea, outa, ka⟩ => ?_
  refine WP.mono (word_ok (k := k + 1) (hs.congr ka.2.2) ((ka.gpr (by decide)).trans h8)
    ((ka.gpr (by decide)).trans h9) ((ka.gpr (by decide)).trans h14)
    (by omega_arith) (by omega_arith) hca hoa (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t ⟨ct, ot, hct, hot, et, outt, kt⟩ => ?_
  have he : e + 8 * j + 8 * (k + 1) = e + 8 * j + 8 * k + 8 := by omega_arith
  have heb : eb + 8 * j + 8 * (k + 1) = eb + 8 * j + 8 * k + 8 := by omega_arith
  rw [he, heb, ka.gpr (by decide)] at et
  rw [he] at outt
  have lo : word t.mem B (e + 8 * j + 8 * k) = word a.mem B (e + 8 * j + 8 * k) :=
    outt.word (by omega_arith) (by omega_arith)
  have ti : word a.mem B (e + 8 * j + 8 * k + 8) = word s.mem B (e + 8 * j + 8 * k + 8) :=
    outa.word (by omega_arith) (by omega_arith)
  have bi : word a.mem B (eb + 8 * j + 8 * k + 8) = word s.mem B (eb + 8 * j + 8 * k + 8) :=
    outa.word (by omega_arith) (by omega_arith)
  rw [ti, bi] at et
  refine ⟨ct, ot, hct, hot, ?_, ?_, (ka.trans kt).mono (by simp)⟩
  · rw [AdxSquare.wv2, AdxSquare.wv2, AdxSquare.wv2, lo]
    simp only [Nat.mul_add]
    rw [Nat.mul_left_comm (s.gpr .rdx).toNat]
    omega_using [ea, et]
  · exact (outa.mono (o' := e + 8 * j + 8 * k) (n' := 16) (Nat.le_refl _) (by omega_arith)).trans
      (outt.mono (o' := e + 8 * j + 8 * k) (n' := 16) (by omega_arith) (by omega_arith))
end VG.Proof.Bignum.X86_64.AdxSquareWide

end

/-! ## AdxSquareWideChain -/
section

/-! Composing live-carry pairs into an unrolled multiply-add chain. -/
namespace VG.Proof.Bignum.X86_64.AdxSquareWide
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem chain_ok (n : Nat) {s : State} {B : Addr} {Z e eb j k : Nat} {c o : Bool}
    (hs : Scr s B Z) (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B eb)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 j)
    (hZ : e + 8 * j + 8 * k + 8 * (2 * n) ≤ Z) (hZb : eb + 8 * j + 8 * k + 8 * (2 * n) ≤ Z)
    (sb : eb + 8 * j + 8 * k + 8 * (2 * n) ≤ e + 8 * j + 8 * k ∨
      e + 8 * j + 8 * k + 8 * (2 * n) ≤ eb + 8 * j + 8 * k)
    (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block (AdxSquareWide.chain n k)) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      wv t.mem B (e + 8 * j + 8 * k) (2 * n) +
        2 ^ (64 * (2 * n)) * ((t.gpr .rcx).toNat + c'.toNat + o'.toNat) =
        wv s.mem B (e + 8 * j + 8 * k) (2 * n) +
        (s.gpr .rdx).toNat * wv s.mem B (eb + 8 * j + 8 * k) (2 * n) +
        (s.gpr .rcx).toNat + c.toNat + o.toNat ∧
      Outside B (e + 8 * j + 8 * k) (8 * (2 * n)) s.mem t.mem ∧ Keep [.rax, .r11, .rcx] s t := by
  induction n generalizing s k c o with
  | zero =>
    apply WP.block_nil
    exact ⟨c, o, hc, ho, by simp [wv], Outside.refl _ _ _ _, VG.Proof.MlKem.X86_64.Keep.refl _ _⟩
  | succ n ih =>
    have hn := hs.nowrap
    rw [AdxSquareWide.chain, WP.block_append_iff]
    refine WP.mono (pair_ok hs h8 h9 h14 (by omega_arith) (by omega_arith) (by omega_arith) hc ho)
      fun a ⟨ca, oa, hca, hoa, ea, outa, ka⟩ => ?_
    refine WP.mono (ih (k := k + 2) (hs.congr ka.2.2) ((ka.gpr (by decide)).trans h8)
      ((ka.gpr (by decide)).trans h9) ((ka.gpr (by decide)).trans h14)
      (by omega_arith) (by omega_arith) (by omega_arith) hca hoa)
      fun t ⟨ct, ot, hct, hot, et, outt, kt⟩ => ?_
    have he : e + 8 * j + 8 * (k + 2) = e + 8 * j + 8 * k + 8 * 2 := by omega_arith
    have heb : eb + 8 * j + 8 * (k + 2) = eb + 8 * j + 8 * k + 8 * 2 := by omega_arith
    rw [he, heb, ka.gpr (by decide)] at et
    rw [he] at outt
    have lo : wv t.mem B (e + 8 * j + 8 * k) 2 = wv a.mem B (e + 8 * j + 8 * k) 2 :=
      outt.wv (by omega_arith) (by omega_arith)
    have ti : wv a.mem B (e + 8 * j + 8 * k + 8 * 2) (2 * n) =
        wv s.mem B (e + 8 * j + 8 * k + 8 * 2) (2 * n) := outa.wv (by omega_arith) (by omega_arith)
    have bi : wv a.mem B (eb + 8 * j + 8 * k + 8 * 2) (2 * n) =
        wv s.mem B (eb + 8 * j + 8 * k + 8 * 2) (2 * n) := outa.wv (by omega_arith) (by omega_arith)
    rw [ti, bi] at et
    refine ⟨ct, ot, hct, hot, ?_, ?_, (ka.trans kt).mono (by simp)⟩
    · rw [show 2 * (n + 1) = 2 + 2 * n by omega_arith, wv_add, wv_add, wv_add, lo,
        show 64 * (2 + 2 * n) = 128 + 64 * (2 * n) by omega_arith, Nat.pow_add]
      grind
    · exact (outa.mono (o' := e + 8 * j + 8 * k) (n' := 8 * (2 * (n + 1))) (Nat.le_refl _) (by omega_arith)).trans
        (outt.mono (o' := e + 8 * j + 8 * k) (n' := 8 * (2 * (n + 1))) (by omega_arith) (by omega_arith))
end VG.Proof.Bignum.X86_64.AdxSquareWide

end

/-! ## AdxSquareWideBlock -/
section

/-! Closing a sixteen-word chain and advancing its public counter. -/
namespace VG.Proof.Bignum.X86_64.AdxSquareWide
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem carry_bound {R V T X Y C H : Nat} (hR : 0 < R) (hT : T < R)
    (hX : X < 2 ^ 64) (hY : Y < R) (hC : C < 2 ^ 64)
    (he : V + R * H = T + X * Y + C) : H < 2 ^ 64 := by
  have hp : X * Y ≤ (2 ^ 64 - 1) * (R - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  have hb : R * H < R * 2 ^ 64 := by omega_using [he, hp, hR, hT, hC]
  exact Nat.lt_of_mul_lt_mul_left hb

theorem block_ok {s : State} {B : Addr} {Z e eb j w : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B eb)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 j) (hbx : s.gpr .rbx = BitVec.ofNat 64 w)
    (hZ : e + 8 * j + 128 ≤ Z) (hZb : eb + 8 * j + 128 ≤ Z)
    (sb : eb + 8 * j + 128 ≤ e + 8 * j ∨ e + 8 * j + 128 ≤ eb + 8 * j)
    (hj : j + 16 < 2 ^ 64) (hw : w < 2 ^ 64) :
    WP isa (.block AdxSquareWide.block) s fun t =>
      wv t.mem B (e + 8 * j) 16 + 2 ^ 1024 * (t.gpr .rcx).toNat =
        wv s.mem B (e + 8 * j) 16 + (s.gpr .rdx).toNat * wv s.mem B (eb + 8 * j) 16 + (s.gpr .rcx).toNat ∧
      Outside B (e + 8 * j) 128 s.mem t.mem ∧ t.gpr .r14 = BitVec.ofNat 64 (j + 16) ∧
      t.zf = some (decide (j + 16 = w)) ∧ Keep [.rsi, .rax, .r11, .rcx, .r14] s t := by
  unfold AdxSquareWide.block
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (xorRsi_ok s) fun a ⟨_, ca, oa, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (chain_ok 8 (k := 0) (hs.congr ka.2.2.2) ((ka.gpr (by decide)).trans h8)
    ((ka.gpr (by decide)).trans h9) ((ka.gpr (by decide)).trans h14)
    (by simpa using hZ) (by simpa using hZb) (by simpa using sb) ca oa)
    fun b ⟨cb, ob, hcb, hob, eq, out, kb⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Bool.toNat_false, ka.2.1] at eq out
  rw [ka.gpr (r := .rdx) (by decide), ka.gpr (r := .rcx) (by decide)] at eq
  rw [WP.block_append_iff]
  refine WP.mono (close_ok b hcb hob (by decide)) fun d ⟨cd, od, _, _, ed, kd⟩ => ?_
  have hT := wv_lt s.mem B (e + 8 * j) 16
  have hB := wv_lt s.mem B (eb + 8 * j) 16
  simp only [Nat.reduceMul] at hT hB
  have hX := (s.gpr .rdx).isLt
  have hC := (s.gpr .rcx).isLt
  have hb : (b.gpr .rcx).toNat + cb.toNat + ob.toNat < 2 ^ 64 :=
    carry_bound (R := 2 ^ 1024) (V := wv b.mem B (e + 8 * j) 16)
      (T := wv s.mem B (e + 8 * j) 16) (X := (s.gpr .rdx).toNat)
      (Y := wv s.mem B (eb + 8 * j) 16) (C := (s.gpr .rcx).toNat)
      (Nat.two_pow_pos 1024) hT hX hB hC eq
  have eclose : (d.gpr .rcx).toNat = (b.gpr .rcx).toNat + cb.toNat + ob.toNat := by
    have := Bool.toNat_le cd; have := Bool.toNat_le od
    omega_using [ed, hb, this]
  have k := (ka.keep.trans kb).trans kd.keep
  have h14d := (k.gpr (by decide)).trans h14
  have hbxd := (k.gpr (by decide)).trans hbx
  have tail : WP isa (.block [.alu .add .r14 (.imm 16), .alu .cmp .r14 (.reg .rbx)]) d fun t =>
      t.gpr .r14 = BitVec.ofNat 64 (j + 16) ∧ t.zf = some (decide (j + 16 = w)) ∧
      t.mem = d.mem ∧ Keep [.r14] d t := by
    refine WP.mono (WP.keep [.r14] (Q := fun t => t.gpr .r14 = BitVec.ofNat 64 (j + 16) ∧
      t.zf = some (decide (j + 16 = w)) ∧ t.mem = d.mem) ?_ rfl) fun t ⟨h, kt⟩ => ⟨h.1, h.2.1, h.2.2, kt⟩
    have ha : BitVec.ofNat 64 j + 16 = BitVec.ofNat 64 (j + 16) := by
      rw [BitVec.ofNat_add]; rfl
    xrun [h14d, hbxd, ha, ofNat_sub_beq hj hw]
  refine WP.mono tail fun t ⟨ht14, htz, hm, kt⟩ => ⟨?_, ?_, ht14, htz, (k.trans kt).mono (by simp)⟩
  · rw [hm, kd.2.1, kt.gpr (by decide), eclose]; exact eq
  · rw [hm, kd.2.1]; exact out
end VG.Proof.Bignum.X86_64.AdxSquareWide

end

/-! ## AdxSquareWideRow -/
section

/-! A long-block row, with the existing row as the general-size fallback. -/
namespace VG.Proof.Bignum.X86_64.AdxSquareWide
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Proof.Bignum.X86_64.AdxSquare (RowInv)

theorem blocks_ok {s₀ s : State} {B : Addr} {Z e eb a w : Nat}
    (h8 : s₀.gpr .r8 = off B e) (h9 : s₀.gpr .r9 = off B eb)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 w)
    (hw16 : w % 16 = 0) (haw : 16 * a < w) (hw : w < 2 ^ 60)
    (hZ : e + 8 * w ≤ Z) (hZb : eb + 8 * w ≤ Z)
    (sb : eb + 8 * w ≤ e ∨ e + 8 * w ≤ eb)
    (hI : RowInv s₀ B Z e eb (16 * a) s) :
    WP isa (.loop (.block AdxSquareWide.block) .ne) s (RowInv s₀ B Z e eb w) := by
  refine wp_upto (a := a) (N := w / 16) (by omega_arith)
    (fun k t => RowInv s₀ B Z e eb (16 * k) t ∧ t.gpr .rbx = BitVec.ofNat 64 w) ?_ ?_ ⟨hI, hbx⟩
  · intro k _ hk t h
    obtain ⟨h, hbx'⟩ := h
    have kp := h.keep
    refine WP.mono (block_ok h.scr ((kp.gpr (by decide)).trans h8)
      ((kp.gpr (by decide)).trans h9) h.r14 hbx'
      (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
      fun t' ⟨hv, ho, h14, hz, kt⟩ => ⟨?_, ?_, (kt.gpr (by decide)).trans hbx'⟩
    · exact hz.trans (congrArg some (decide_eq_decide.mpr (by omega_using [hk, hw16])))
    · have step := @RowInv.step s₀ t t' B Z e eb (16 * k) 16 w h (by omega_using [hk, hw16] : 16 * k + 16 ≤ w) hZ hZb sb (by simpa only [Nat.reduceMul] using hv) ho h14 (kt.mono (by decide))
      rw [show 16 * (k + 1) = 16 * k + 16 by omega_using []]
      exact step
  · intro t h
    have he : 16 * (w / 16) = w := by omega_arith
    exact he ▸ h.1

theorem and15 (w : Nat) (hw : w < 2 ^ 64) :
    BitVec.ofNat 64 w &&& 15 = BitVec.ofNat 64 (w % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw,
    show (15 : BitVec 64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat]
  omega_arith

theorem row_ok {s : State} {B : Addr} {Z e eb w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B eb)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 w) (hw1 : 0 < w) (hw : w < 2 ^ 60)
    (hZ : e + 8 * w ≤ Z) (hZb : eb + 8 * w ≤ Z)
    (sb : eb + 8 * w ≤ e ∨ e + 8 * w ≤ eb) :
    WP isa AdxSquareWide.row s fun t =>
      wv t.mem B e w + 2 ^ (64 * w) * (t.gpr .rcx).toNat =
        wv s.mem B e w + (s.gpr .rdx).toNat * wv s.mem B eb w ∧
      Outside B e (8 * w) s.mem t.mem ∧ t.gpr .r14 = BitVec.ofNat 64 w ∧
      Keep [.rsi, .rax, .r11, .r12, .r13, .r15, .rcx, .r14, .rbx] s t := by
  have guard : WP isa (.block [.mov .rbx (.reg .rbp), .alu .and .rbx (.imm 15), .alu .cmp .rbx (.imm 0)]) s
      fun t => t.zf = some (decide (w % 16 = 0)) ∧ t.mem = s.mem ∧ Keep [.rbx] s t := by
    refine WP.mono (WP.keep [.rbx] (Q := fun t => t.zf = some (decide (w % 16 = 0)) ∧ t.mem = s.mem)
      ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
    xrun [hbp, and15 w (by omega_arith)]
    change ((BitVec.ofNat 64 w &&& 15) - BitVec.ofNat 64 0 == 0) = _
    rw [and15 w (by omega_arith)]
    exact ofNat_sub_beq (by omega_arith) (by decide)
  unfold AdxSquareWide.row
  refine WP.seq (WP.mono guard fun a ⟨hz, hm, ka⟩ => ?_)
  have ha8 := (ka.gpr (by decide)).trans h8
  have ha9 := (ka.gpr (by decide)).trans h9
  have habp := (ka.gpr (by decide)).trans hbp
  by_cases h16 : w % 16 = 0
  · refine WP.ite true (by simp [eval, hz, h16]) (fun _ => ?_) (by simp)
    have init : WP isa (.block [.mov .rbx (.reg .rbp), .mov32 .rcx (.imm 0), .mov32 .r14 (.imm 0)]) a
        fun t => t.gpr .rbx = BitVec.ofNat 64 w ∧ t.gpr .rcx = 0 ∧ t.gpr .r14 = 0 ∧
          t.mem = a.mem ∧ Keep [.rbx, .rcx, .r14] a t := by
      refine WP.mono (WP.keep [.rbx, .rcx, .r14] (Q := fun t => t.gpr .rbx = BitVec.ofNat 64 w ∧
        t.gpr .rcx = 0 ∧ t.gpr .r14 = 0 ∧ t.mem = a.mem) ?_ rfl)
        fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
      xrun [habp]
    refine WP.seq (WP.mono init fun b ⟨hbx, hcx, h14, hmb, kb⟩ => ?_)
    have kab := ka.trans kb
    have inv : RowInv b B Z e eb 0 b :=
      ⟨hs.congr kab.2.2, Keep.refl _ _, h14, Outside.refl _ _ _ _, by simp [wv]⟩
    refine WP.mono (blocks_ok (a := 0) ((kab.gpr (by decide)).trans h8)
      ((kab.gpr (by decide)).trans h9) hbx h16 (by omega_arith) hw hZ hZb sb inv)
      fun t hi => ⟨?_, ?_, hi.r14, (kab.trans hi.keep).mono (by decide)⟩
    · have hv := hi.val
      rw [hmb, hm, kab.gpr (by decide), hcx] at hv
      simpa using hv
    · have ho := hi.out; rw [hmb, hm] at ho; exact ho
  · refine WP.ite false (by simp [eval, hz, h16]) (by simp) (fun _ => ?_)
    refine WP.mono (AdxSquare.macRow_ok (hs.congr ka.2.2) ha8 ha9 habp hw hZ hZb sb)
      fun t ⟨hv, ho, h14, kt⟩ => ⟨?_, ?_, h14, (ka.trans kt).mono (by decide)⟩
    · rw [hm, ka.gpr (by decide)] at hv; exact hv
    · rw [hm] at ho; exact ho

end VG.Proof.Bignum.X86_64.AdxSquareWide

end
