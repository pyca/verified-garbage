import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRow

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
  refine wp_upto (a := a) (N := w / 16) (by omega)
    (fun k t => RowInv s₀ B Z e eb (16 * k) t ∧ t.gpr .rbx = BitVec.ofNat 64 w) ?_ ?_ ⟨hI, hbx⟩
  · intro k _ hk t h
    obtain ⟨h, hbx'⟩ := h
    have kp := h.keep
    refine WP.mono (block_ok h.scr ((kp.gpr (by decide)).trans h8)
      ((kp.gpr (by decide)).trans h9) h.r14 hbx'
      (by omega) (by omega) (by omega) (by omega) (by omega))
      fun t' ⟨hv, ho, h14, hz, kt⟩ => ⟨?_, ?_, (kt.gpr (by decide)).trans hbx'⟩
    · exact hz.trans (congrArg some (decide_eq_decide.mpr (by omega_using [hk, hw16])))
    · have step := @RowInv.step s₀ t t' B Z e eb (16 * k) 16 w h (by omega_using [hk, hw16] : 16 * k + 16 ≤ w) hZ hZb sb (by simpa only [Nat.reduceMul] using hv) ho h14 (kt.mono (by simp))
      rw [show 16 * (k + 1) = 16 * k + 16 by omega_using []]
      exact step
  · intro t h
    have he : 16 * (w / 16) = w := by omega
    exact he ▸ h.1

theorem and15 (w : Nat) (hw : w < 2 ^ 64) :
    BitVec.ofNat 64 w &&& 15 = BitVec.ofNat 64 (w % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw,
    show (15 : BitVec 64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat]
  omega

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
    xrun [hbp, and15 w (by omega)]
    change ((BitVec.ofNat 64 w &&& 15) - BitVec.ofNat 64 0 == 0) = _
    rw [and15 w (by omega)]
    exact ofNat_sub_beq (by omega) (by decide)
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
      ((kab.gpr (by decide)).trans h9) hbx h16 (by omega) hw hZ hZb sb inv)
      fun t hi => ⟨?_, ?_, hi.r14, (kab.trans hi.keep).mono (by simp)⟩
    · have hv := hi.val
      rw [hmb, hm, kab.gpr (by decide), hcx] at hv
      simpa using hv
    · have ho := hi.out; rw [hmb, hm] at ho; exact ho
  · refine WP.ite false (by simp [eval, hz, h16]) (by simp) (fun _ => ?_)
    refine WP.mono (AdxSquare.macRow_ok (hs.congr ka.2.2) ha8 ha9 habp hw hZ hZb sb)
      fun t ⟨hv, ho, h14, kt⟩ => ⟨?_, ?_, h14, (ka.trans kt).mono (by simp)⟩
    · rw [hm, ka.gpr (by decide)] at hv; exact hv
    · rw [hm] at ho; exact ho
end VG.Proof.Bignum.X86_64.AdxSquareWide
