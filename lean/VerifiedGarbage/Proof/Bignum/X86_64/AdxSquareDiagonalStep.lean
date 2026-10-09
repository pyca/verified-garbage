import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonal

/-! Storing a pair of words after the square's diagonal addition. -/

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
  have ho := writeW_outside m B x (d := d) (by omega)
  have ho' := writeW_outside (m.writeW (off B d) x) B y (d := d + 8) (by omega)
  refine ⟨?_, (ho.mono (Nat.le_refl _) (by omega)).trans (ho'.mono (by omega) (by omega))⟩
  rw [wv2, ho'.word (by omega) (by omega), word_writeW_self, word_writeW_self]

/-- One pair of stored words, the exact carry, and public loop counts. -/
theorem diagonalStep_ok {s : State} {B : Addr} {Z A eb i w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B A) (h9 : s.gpr .r9 = off B eb)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 i) (h14 : s.gpr .r14 = BitVec.ofNat 64 (2 * i))
    (h10 : s.gpr .r10 = BitVec.ofNat 64 w) (hi : i < w) (hw : w < 2 ^ 60)
    (hA : A + 16 * (i + 1) ≤ Z) (hb : eb + 8 * (i + 1) ≤ Z) :
    WP isa AdxSquare.diagonalStep s fun t =>
      wv t.mem B (A + 16 * i) 2 + 2 ^ 128 * (t.gpr .r15).toNat =
        2 * wv s.mem B (A + 16 * i) 2 +
          (word s.mem B (eb + 8 * i)).toNat * (word s.mem B (eb + 8 * i)).toNat + (s.gpr .r15).toNat ∧
      Outside B (A + 16 * i) 16 s.mem t.mem ∧
      t.gpr .rbp = BitVec.ofNat 64 (i + 1) ∧ t.gpr .r14 = BitVec.ofNat 64 (2 * (i + 1)) ∧
      t.zf = some (decide (i + 1 = w)) ∧
      Keep [.rdx, .r11, .r12, .rsi, .rbx, .rax, .rcx, .r15, .rbp, .r14] s t := by
  have hn := hs.nowrap
  have ad : off B A + BitVec.ofNat 64 (2 * i) * BitVec.ofNat 64 8 + BitVec.ofInt 64 0 = off B (A + 16 * i) := by
    rw [addrK0]; congr 1; omega
  have ad' : off B A + BitVec.ofNat 64 (2 * i) * BitVec.ofNat 64 8 + BitVec.ofInt 64 8 = off B (A + 16 * i + 8) := by
    rw [addrK1]; congr 1; omega
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
      hs.ld (show eb + 8 * i + 8 ≤ Z by omega), hs.ld (show A + 16 * i + 8 ≤ Z by omega),
      hs.ld (show A + 16 * i + 8 + 8 ≤ Z by omega)]
  unfold AdxSquare.diagonalStep
  refine WP.seq (WP.mono head fun s₁ ⟨hdx, h11, h12, hm₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (diagonalCore_ok s₁) fun s₂ ⟨hv, k₂⟩ => ?_)
  have k12 := k₁.trans k₂.keep
  have h8₂ : s₂.gpr .r8 = off B A := (k12.gpr (by decide)).trans h8
  have h14₂ : s₂.gpr .r14 = BitVec.ofNat 64 (2 * i) := (k12.gpr (by decide)).trans h14
  have hbp₂ : s₂.gpr .rbp = BitVec.ofNat 64 i := (k12.gpr (by decide)).trans hbp
  have h10₂ : s₂.gpr .r10 = BitVec.ofNat 64 w := (k12.gpr (by decide)).trans h10
  have hs₂ := hs.congr k12.2.2
  have cnt : BitVec.ofNat 64 (2 * i) + 2 = BitVec.ofNat 64 (2 * (i + 1)) := by
    rw [show 2 * (i + 1) = 2 * i + 2 by omega, BitVec.ofNat_add]; rfl
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
      hs₂.st (show A + 16 * i + 8 ≤ Z by omega), hs₂.st (show A + 16 * i + 8 + 8 ≤ Z by omega),
      ofNat_sub_beq (show i + 1 < 2 ^ 64 by omega) (show w < 2 ^ 64 by omega)]
  refine WP.mono tail fun t ⟨hm, h15', hbp', h14', hz, kt⟩ => ?_
  obtain ⟨hval, ho⟩ := write2 s₂.mem B (A + 16 * i) (s₂.gpr .r11) (s₂.gpr .r12) (by omega)
  rw [← hm] at hval ho
  rw [k₂.2.1, hm₁] at ho
  refine ⟨?_, ho, hbp', h14', hz, (k12.trans kt).mono (by decide)⟩
  rw [hval, h15', wv2]
  rw [h11, h12, hdx, k₁.gpr (by decide)] at hv
  exact hv

end VG.Proof.Bignum.X86_64.AdxSquare
