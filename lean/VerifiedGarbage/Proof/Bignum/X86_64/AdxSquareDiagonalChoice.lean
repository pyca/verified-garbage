import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareGroupedLoop

namespace VG.Proof.Bignum.X86_64.AdxSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem and3 (w : Nat) (hw : w < 2^64) :
    BitVec.ofNat 64 w &&& 3 = BitVec.ofNat 64 (w%4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw,
    show (3 : BitVec 64).toNat = 2^2-1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat]
  omega

theorem diagonalChoice_ok {s : State} {B : Addr} {Z A eb w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B A) (h9 : s.gpr .r9 = off B eb)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 w) (hw0 : 0 < w) (hw : w < 2^60)
    (hA : A+16*w ≤ Z) (hb : eb+8*w ≤ Z)
    (sep : eb+8*w ≤ A ∨ A+16*w ≤ eb) :
    WP isa AdxSquare.diagonalChoice s fun t =>
      wv t.mem B A (2*w) + 2^(128*w)*(t.gpr .r15).toNat =
        2*wv s.mem B A (2*w) + diagonalValue s.mem B eb w ∧
      Outside B A (16*w) s.mem t.mem ∧
      Keep [.rdx,.r11,.r12,.rsi,.rbx,.rax,.rcx,.r15,.rbp,.r14] s t := by
  unfold AdxSquare.diagonalChoice
  have test : WP isa (.block [.mov .rax (.reg .r10), .alu .and .rax (.imm 3), .alu .cmp .rax (.imm 0)]) s fun t =>
      t.zf = some (decide (w%4=0)) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
    refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.zf = some (decide (w%4=0)) ∧ t.mem = s.mem) ?_ rfl) fun t ⟨h,k⟩ => ⟨h.1,h.2,k⟩
    xrun [h10,and3 w (by omega)]
    change (BitVec.ofNat 64 (w%4) - BitVec.ofNat 64 0 == 0) = _
    exact ofNat_sub_beq (by omega) (by decide)
  refine WP.seq (WP.mono test fun a ⟨hz,hm,ka⟩ => ?_)
  by_cases h4 : w%4=0
  · refine WP.ite true (by simp [eval,hz,h4]) (fun _ => ?_) (by simp)
    refine WP.mono (AdxSquareGrouped.diagonal_ok (hs.congr ka.2.2)
      ((ka.gpr (by decide)).trans h8) ((ka.gpr (by decide)).trans h9)
      ((ka.gpr (by decide)).trans h10) hw0 hw h4 hA hb sep) fun t ⟨hv,ho,kt⟩ => ?_
    rw [hm] at hv ho
    exact ⟨hv,ho,(ka.trans kt).mono (by simp)⟩
  · refine WP.ite false (by simp [eval,hz,h4]) (by simp) (fun _ => ?_)
    refine WP.mono (diagonal_ok (hs.congr ka.2.2)
      ((ka.gpr (by decide)).trans h8) ((ka.gpr (by decide)).trans h9)
      ((ka.gpr (by decide)).trans h10) hw0 hw hA hb sep) fun t ⟨hv,ho,kt⟩ => ?_
    rw [hm] at hv ho
    exact ⟨hv,ho,(ka.trans kt).mono (by simp)⟩

end VG.Proof.Bignum.X86_64.AdxSquare
