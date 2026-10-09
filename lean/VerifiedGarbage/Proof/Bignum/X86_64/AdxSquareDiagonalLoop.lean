import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalStep
import VerifiedGarbage.Proof.Bignum.Square

/-! The complete diagonal-addition loop for an ADX square. -/

namespace VG.Proof.Bignum.X86_64.AdxSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

def diagonalValue (m : Mem) (B : Addr) (eb i : Nat) : Nat :=
  Square.diagonal (2 ^ 64) (fun j => (word m B (eb + 8 * j)).toNat) i

theorem diagonalValue_succ (m : Mem) (B : Addr) (eb i : Nat) :
    diagonalValue m B eb (i + 1) = diagonalValue m B eb i +
      (word m B (eb + 8 * i)).toNat * (word m B (eb + 8 * i)).toNat * 2 ^ (128 * i) := by
  unfold diagonalValue
  rw [Square.diagonal, ← Nat.pow_mul]
  have h : 2 ^ (128 * i) = 2 ^ (64 * i) * 2 ^ (64 * i) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [h]
  grind

structure DiagInv (s₀ : State) (B : Addr) (Z A eb : Nat) (i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rdx, .r11, .r12, .rsi, .rbx, .rax, .rcx, .r15, .rbp, .r14] s₀ t
  rbp : t.gpr .rbp = BitVec.ofNat 64 i
  r14 : t.gpr .r14 = BitVec.ofNat 64 (2 * i)
  out : Outside B A (16 * i) s₀.mem t.mem
  val : wv t.mem B A (2 * i) + 2 ^ (128 * i) * (t.gpr .r15).toNat =
    2 * wv s₀.mem B A (2 * i) + diagonalValue s₀.mem B eb i

theorem diagStep_ok {s₀ t : State} {B : Addr} {Z A eb w i : Nat}
    (h8 : s₀.gpr .r8 = off B A) (h9 : s₀.gpr .r9 = off B eb)
    (h10 : s₀.gpr .r10 = BitVec.ofNat 64 w) (hw : w < 2 ^ 60) (hi : i < w)
    (hA : A + 16 * w ≤ Z) (hb : eb + 8 * w ≤ Z)
    (sb : eb + 8 * w ≤ A ∨ A + 16 * w ≤ eb)
    (hI : DiagInv s₀ B Z A eb i t) :
    WP isa AdxSquare.diagonalStep t fun t' =>
      t'.zf = some (decide (i + 1 = w)) ∧ DiagInv s₀ B Z A eb (i + 1) t' := by
  have hn := hI.scr.nowrap
  have kp := hI.keep
  refine WP.mono (diagonalStep_ok hI.scr ((kp.gpr (by decide)).trans h8)
    ((kp.gpr (by decide)).trans h9) hI.rbp hI.r14 ((kp.gpr (by decide)).trans h10)
    hi hw (by omega) (by omega)) fun t' ⟨hv, ho, hbp, h14, hz, kt⟩ => ⟨hz, ?_⟩
  have rT : wv t.mem B (A + 16 * i) 2 = wv s₀.mem B (A + 16 * i) 2 := hI.out.wv (by omega) (by omega)
  have rX : word t.mem B (eb + 8 * i) = word s₀.mem B (eb + 8 * i) := hI.out.word (by omega) (by omega)
  have rL : wv t'.mem B A (2 * i) = wv t.mem B A (2 * i) := ho.wv (by omega) (by omega)
  rw [rT, rX] at hv
  refine ⟨hI.scr.congr kt.2.2, (kp.trans kt).mono (by decide), hbp, h14, ?_, ?_⟩
  · exact (hI.out.mono (o' := A) (n' := 16 * (i + 1)) (Nat.le_refl _) (by omega)).trans
      (ho.mono (o' := A) (n' := 16 * (i + 1)) (by omega) (by omega))
  · have hval := hI.val
    rw [show 2 * (i + 1) = 2 * i + 2 by omega, wv_add, wv_add s₀.mem B A, rL,
      show A + 8 * (2 * i) = A + 16 * i by omega, show 64 * (2 * i) = 128 * i by omega,
      show 128 * (i + 1) = 128 * i + 128 by omega, Nat.pow_add, diagonalValue_succ]
    grind

/-- The doubled cross products plus the diagonal, with the final carry
accounted for explicitly. -/
theorem diagonal_ok {s : State} {B : Addr} {Z A eb w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B A) (h9 : s.gpr .r9 = off B eb)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 w) (hw0 : 0 < w) (hw : w < 2 ^ 60)
    (hA : A + 16 * w ≤ Z) (hb : eb + 8 * w ≤ Z)
    (sb : eb + 8 * w ≤ A ∨ A + 16 * w ≤ eb) :
    WP isa AdxSquare.diagonal s fun t =>
      wv t.mem B A (2 * w) + 2 ^ (128 * w) * (t.gpr .r15).toNat =
        2 * wv s.mem B A (2 * w) + diagonalValue s.mem B eb w ∧
      Outside B A (16 * w) s.mem t.mem ∧
      Keep [.rdx, .r11, .r12, .rsi, .rbx, .rax, .rcx, .r15, .rbp, .r14] s t := by
  unfold AdxSquare.diagonal
  have init : WP isa (.block [.mov32 .r15 (.imm 0), .mov32 .rbp (.imm 0), .mov32 .r14 (.imm 0)]) s fun t =>
      t.gpr .r15 = 0 ∧ t.gpr .rbp = 0 ∧ t.gpr .r14 = 0 ∧ t.mem = s.mem ∧ Keep [.r15, .rbp, .r14] s t := by
    refine WP.mono (WP.keep [.r15, .rbp, .r14] (Q := fun t =>
      t.gpr .r15 = 0 ∧ t.gpr .rbp = 0 ∧ t.gpr .r14 = 0 ∧ t.mem = s.mem) (by xrun) rfl)
      fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  refine WP.seq (WP.mono init fun s₁ ⟨h15, hbp, h14, hm, k₁⟩ => ?_)
  have hI : DiagInv s₁ B Z A eb 0 s₁ :=
    ⟨hs.congr k₁.2.2, Keep.refl _ _, hbp, h14, Outside.refl _ _ _ _, by
      simp [wv, h15, diagonalValue, Square.diagonal]⟩
  refine WP.mono (wp_upto (a := 0) hw0 (DiagInv s₁ B Z A eb)
    (fun i _ hi t h => diagStep_ok ((k₁.gpr (by decide)).trans h8) ((k₁.gpr (by decide)).trans h9)
      ((k₁.gpr (by decide)).trans h10) hw hi hA hb sb h) (fun _ h => h) hI)
    fun t h => ⟨?_, ?_, (k₁.trans h.keep).mono (by decide)⟩
  · have hv := h.val
    rw [hm] at hv
    exact hv
  · have ho := h.out
    rw [hm] at ho
    exact ho

end VG.Proof.Bignum.X86_64.AdxSquare
