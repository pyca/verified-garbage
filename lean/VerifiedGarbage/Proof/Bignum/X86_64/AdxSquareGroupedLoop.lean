import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareGroupedGroup

/-! The terminating grouped diagonal loop, with the original memory frame. -/
namespace VG.Proof.Bignum.X86_64.AdxSquareGrouped
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxSquare (DiagInv diagonalValue)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem diagonal_ok {s : State} {B : Addr} {Z A eb w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B A) (h9 : s.gpr .r9 = off B eb)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 w) (hw0 : 0 < w) (hw : w < 2^60)
    (hw4 : w % 4 = 0) (hA : A+16*w ≤ Z) (hb : eb+8*w ≤ Z)
    (sep : eb+8*w ≤ A ∨ A+16*w ≤ eb) :
    WP isa AdxSquareGrouped.diagonal s fun t =>
      wv t.mem B A (2*w) + 2^(128*w)*(t.gpr .r15).toNat =
        2*wv s.mem B A (2*w) + diagonalValue s.mem B eb w ∧
      Outside B A (16*w) s.mem t.mem ∧
      Keep [.rdx,.r11,.r12,.rsi,.rbx,.rax,.rcx,.r15,.rbp,.r14] s t := by
  have hdiv : 4*(w/4) = w := by omega
  unfold AdxSquareGrouped.diagonal
  have init : WP isa (.block [.mov32 .r15 (.imm 0), .mov32 .rbp (.imm 0), .mov32 .r14 (.imm 0)]) s fun t =>
      t.gpr .r15 = 0 ∧ t.gpr .rbp = 0 ∧ t.gpr .r14 = 0 ∧ t.mem = s.mem ∧
      Keep [.r15,.rbp,.r14] s t := by
    refine WP.mono (WP.keep [.r15,.rbp,.r14] (Q := fun t =>
      t.gpr .r15 = 0 ∧ t.gpr .rbp = 0 ∧ t.gpr .r14 = 0 ∧ t.mem = s.mem)
      (by xrun) rfl) fun t ⟨h,k⟩ => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,k⟩
  refine WP.seq (WP.mono init fun s1 ⟨h15,hbp,h14,hm,k1⟩ => ?_)
  let Inv := fun j t => DiagInv s1 B Z A eb (4*j) t ∧ (t.gpr .r15).toNat ≤ 2
  have initial : Inv 0 s1 := ⟨
    ⟨hs.congr k1.2.2, Keep.refl _ _, hbp, h14, Outside.refl _ _ _ _, by
      simp [wv,h15,diagonalValue,Square.diagonal]⟩, by rw [h15]; decide⟩
  have body : ∀ j, 0 ≤ j → j < w/4 → ∀ t, Inv j t →
      WP isa AdxSquareGrouped.group t fun u =>
        u.zf = some (decide (j+1=w/4)) ∧ Inv (j+1) u := by
    intro j _ hj t ht
    refine WP.mono (group_ok ((k1.gpr (by decide)).trans h8) ((k1.gpr (by decide)).trans h9)
      ((k1.gpr (by decide)).trans h10) hw (by omega : 4*j+4 ≤ w) hA hb sep ht.1 ht.2)
      fun u ⟨hz,hd,hc⟩ => ?_
    have eq : (4*j+4=w) = (j+1=w/4) := propext ⟨by omega,by omega⟩
    refine ⟨by simpa only [eq] using hz, ?_, hc⟩
    simpa only [Nat.mul_add, Nat.mul_one] using hd
  refine WP.mono (wp_upto (a := 0) (by omega : 0 < w/4) Inv body (fun _ h => h) initial)
    fun t ⟨ht,_⟩ => ?_
  rw [hdiv] at ht
  refine ⟨?_,?_,(k1.trans ht.keep).mono (by simp)⟩
  · have hv := ht.val
    rw [hm] at hv
    exact hv
  · have ho := ht.out
    rw [hm] at ho
    exact ho

end VG.Proof.Bignum.X86_64.AdxSquareGrouped
