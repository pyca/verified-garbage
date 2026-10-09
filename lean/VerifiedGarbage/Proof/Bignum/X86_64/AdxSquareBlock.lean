import VerifiedGarbage.Impl.Bignum.X86_64.AdxSquare
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock

/-! The register-resident scalar multiply-add used by the square. -/

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
  have rb : ∀ k : Nat, k < 4 → readSrc s (.mem (ix .r9 .r14 (8 * (k : Int)))) = some (word s.mem B (eb + 8 * j + 8 * k)) :=
    fun k hk => readSrc_word hs (ea_ixk s h9 h14 k) (by omega)
  have rt : ∀ k : Nat, k < 4 → readSrc s (.mem (ix .r8 .r14 (8 * (k : Int)))) = some (word s.mem B (e + 8 * j + 8 * k)) :=
    fun k hk => readSrc_word hs (ea_ixk s h8 h14 k) (by omega)
  -- Reads through registers the steps keep.
  have kr : ∀ {rs : List Reg} {t : State}, Keeps rs s t → .r8 ∉ rs → .r9 ∉ rs → .r14 ∉ rs →
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
  have K₃ := K₂.trans k₃
  obtain ⟨rb₃, rt₃⟩ := kr K₃ (by decide) (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (wordA_ok s₃ (rb₃ 1 (by decide)) (rt₃ 1 (by decide)) ca₁ oa₁
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₄ ⟨a₂, p₂, ca₂, oa₂, e₁, k₄⟩ => ?_
  have K₄ := K₃.trans k₄
  obtain ⟨rb₄, rt₄⟩ := kr K₄ (by decide) (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (wordA_ok s₄ (rb₄ 2 (by decide)) (rt₄ 2 (by decide)) ca₂ oa₂
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₅ ⟨a₃, p₃, ca₃, oa₃, e₂, k₅⟩ => ?_
  have K₅ := K₄.trans k₅
  obtain ⟨rb₅, rt₅⟩ := kr K₅ (by decide) (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (wordA_ok s₅ (rb₅ 3 (by decide)) (rt₅ 3 (by decide)) ca₃ oa₃
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₆ ⟨a₄, p₄, ca₄, oa₄, e₃, k₆⟩ => ?_
  refine WP.mono (close_ok s₆ ca₄ oa₄ (by decide)) fun t ⟨a₅, p₅, ca₅, oa₅, e₄, k₇⟩ => ?_
  have K := (K₅.trans k₆).trans k₇
  -- The registers along the way.
  have x₂ : s₂.gpr .rdx = s.gpr .rdx := K₂.gpr (by decide)
  have x₃ : s₃.gpr .rdx = s₂.gpr .rdx := k₃.gpr (by decide)
  have x₄ : s₄.gpr .rdx = s₂.gpr .rdx := (k₄.gpr (by decide)).trans x₃
  have x₅ : s₅.gpr .rdx = s₂.gpr .rdx := (k₅.gpr (by decide)).trans x₄
  have c₀ : s₂.gpr .rcx = s.gpr .rcx := K₂.gpr (by decide)
  have r11 : t.gpr .r11 = s₃.gpr .r11 := (k₇.gpr (by decide)).trans ((k₆.gpr (by decide)).trans
    ((k₅.gpr (by decide)).trans (k₄.gpr (by decide))))
  have r12 : t.gpr .r12 = s₄.gpr .r12 := (k₇.gpr (by decide)).trans ((k₆.gpr (by decide)).trans (k₅.gpr (by decide)))
  have r13 : t.gpr .r13 = s₅.gpr .r13 := (k₇.gpr (by decide)).trans (k₆.gpr (by decide))
  have r15 : t.gpr .r15 = s₆.gpr .r15 := k₇.gpr (by decide)
  rw [x₂] at e₀
  rw [x₃, x₂] at e₁
  rw [x₄, x₂] at e₂
  rw [x₅, x₂] at e₃
  rw [c₀] at e₀
  simp only [Bool.toNat_false] at e₀
  have hb : ∀ k, (s.gpr .rdx).toNat * (word s.mem B (eb + 8 * j + 8 * k)).toNat ≤
      (2 ^ 64 - 1) * (2 ^ 64 - 1) := fun k => Nat.mul_le_mul (by have := (s.gpr .rdx).isLt; omega)
        (by have := (word s.mem B (eb + 8 * j + 8 * k)).isLt; omega)
  obtain ⟨z₁, z₂, e⟩ := halfA_arith (hb 0) (hb 1) (hb 2) (hb 3) (word s.mem B (e + 8 * j + 8 * 0)).isLt
    (word s.mem B (e + 8 * j + 8 * 1)).isLt (word s.mem B (e + 8 * j + 8 * 2)).isLt
    (word s.mem B (e + 8 * j + 8 * 3)).isLt (s.gpr .rcx).isLt (s₃.gpr .r11).isLt (s₄.gpr .r12).isLt
    (s₅.gpr .r13).isLt (s₆.gpr .r15).isLt (t.gpr .rcx).isLt e₀ e₁ e₂ e₃ e₄
  refine ⟨?_, ?_, ?_, ?_, K.mono (by decide)⟩
  · rw [ca₅]; cases a₅ <;> simp_all
  · rw [oa₅]; cases p₅ <;> simp_all
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
  obtain ⟨hv, ho⟩ := write4 a.mem B (e + 8 * j) (a.gpr .r11) (a.gpr .r12) (a.gpr .r13) (a.gpr .r15) (by omega)
  rw [← hm] at hv ho
  rw [ka.2.1] at ho
  refine ⟨?_, ho, h14', hz, (ka.keep.trans kt).mono (by decide)⟩
  rw [hv, kt.gpr (by decide), wv4 s.mem B (e + 8 * j), wv4 s.mem B (eb + 8 * j), mul_w4]
  omega

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
  have rb : readSrc s (.mem (ix .r9 .r14 (8 * 0))) = some (word s.mem B (eb + 8 * j)) :=
    readSrc_word hs (by simpa using ea_ixk s h9 h14 0) hZb
  have rt : readSrc s (.mem (ix .r8 .r14 (8 * 0))) = some (word s.mem B (e + 8 * j)) :=
    readSrc_word hs (by simpa using ea_ixk s h8 h14 0) hZ
  unfold AdxSquare.mac1
  rw [WP.block_append_iff]
  have pre : WP isa (.block [.alu32 .xor .rsi (.reg .rsi), .mov .rax (.reg .rcx)]) s fun t =>
      t.cf = some false ∧ t.of = some false ∧ t.gpr .rax = s.gpr .rcx ∧ Keeps [.rsi, .rax] s t := by
    refine WP.mono (WP.keep [.rsi, .rax] (Q := fun t => t.cf = some false ∧ t.of = some false ∧
      t.gpr .rax = s.gpr .rcx ∧ t.mem = s.mem) (by xrun; rfl) rfl) fun t ⟨h, k⟩ =>
      ⟨h.1, h.2.1, h.2.2.1, k.1, h.2.2.2, k.2⟩
  refine WP.mono pre fun a ⟨ca, oa, ra, ka⟩ => ?_
  rw [WP.block_append_iff]
  have rb' := (ka.readMem (by decide) (by intro i hi; cases hi; decide)).trans rb
  have rt' := (ka.readMem (by decide) (by intro i hi; cases hi; decide)).trans rt
  refine WP.mono (wordA_ok a rb' rt' ca oa (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun b ⟨c, o, cb, ob, eb', kb⟩ => ?_
  refine WP.mono (close_ok b cb ob (by decide)) fun t ⟨c', o', ct, ot, et, kt⟩ => ?_
  have dx : a.gpr .rdx = s.gpr .rdx := ka.gpr (by decide)
  have lo : t.gpr .r11 = b.gpr .r11 := kt.gpr (by decide)
  rw [dx, ra] at eb'
  simp only [Bool.toNat_false] at eb'
  have hp : (s.gpr .rdx).toNat * (word s.mem B (eb + 8 * j)).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by have := (s.gpr .rdx).isLt; omega) (by have := (word s.mem B (eb + 8 * j)).isLt; omega)
  have ht := (word s.mem B (e + 8 * j)).isLt
  have hc := (s.gpr .rcx).isLt
  have zl : c'.toNat = 0 ∧ o'.toNat = 0 := by omega
  refine ⟨?_, ?_, ?_, ((ka.trans kb).trans kt).mono (by decide)⟩
  · rw [ct]; cases c' <;> simp_all
  · rw [ot]; cases o' <;> simp_all
  · rw [lo]; omega

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
  have a8 : a.gpr .r8 = off B e := (ka.gpr (by decide)).trans h8
  have a14 : a.gpr .r14 = BitVec.ofNat 64 j := (ka.gpr (by decide)).trans h14
  have abx : a.gpr .rbx = BitVec.ofNat 64 w := (ka.gpr (by decide)).trans hbx
  have hsa : Scr a B Z := hs.congr ka.2.2.2
  refine WP.mono (WP.keep [.r14] (Q := fun t =>
      t.mem = a.mem.writeW (off B (e + 8 * j)) (a.gpr .r11) ∧
      t.gpr .r14 = BitVec.ofNat 64 (j + 1) ∧ t.zf = some (decide (j + 1 = w)))
    (by xrun [State.ea, ix, a8, a14, addrK0, Nat.mul_zero, Nat.add_zero, hsa.st hZ, a14, abx, ofNat_add_one, ofNat_sub_beq hj hw]) rfl)
    fun t ⟨⟨hm, h14', hz⟩, kt⟩ => ?_
  have ho := writeW_outside a.mem B (a.gpr .r11) (d := e + 8 * j) (by omega)
  rw [← hm, ka.2.1] at ho
  refine ⟨?_, ho, h14', hz, (ka.keep.trans kt).mono (by decide)⟩
  simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.add_zero, Nat.one_mul, Nat.zero_add]
  rw [hm, word_writeW_self, kt.gpr (by decide)]
  omega

end VG.Proof.Bignum.X86_64.AdxSquare
