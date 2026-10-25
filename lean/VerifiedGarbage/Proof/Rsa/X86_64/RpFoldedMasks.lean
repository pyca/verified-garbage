module

public import VerifiedGarbage.Impl.Rsa.X86_64.RecoverFolded
import VerifiedGarbage.Proof.Rsa.X86_64.RpCst
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.RpSq
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
public import VerifiedGarbage.Impl.Rsa.X86_64.Recover
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces

/-! # The capture masks of folded prime recovery -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Impl.Rsa.X86_64.Keys.Recover VG.Impl.Rsa.X86_64.Keys.Recover.Folded
open VG.Impl.Bignum.X86_64.Public (sMask)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

def flagsAt (w : Nat) : Nat := slot w aRoot + 8 * w

def permit (j : Option Nat) (sigma : Nat) : Bool :=
  match j with
  | none => true
  | some k => decide (k < sigma)

theorem active_ea {s : State} {B : Addr} {w : Nat}
    (h8 : s.gpr .r8 = off B (slot w aRoot)) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) :
    s.ea active = off B (flagsAt w) := by
  simp [State.ea, active, ix, h8, h12, flagsAt, off, BitVec.ofNat_add,
    BitVec.ofNat_mul, BitVec.add_assoc, BitVec.mul_comm]

theorem found_ea {s : State} {B : Addr} {w : Nat}
    (h8 : s.gpr .r8 = off B (slot w aRoot)) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) :
    s.ea found = off B (flagsAt w + 8) := by
  simp [State.ea, found, ix, h8, h12, flagsAt, off, BitVec.ofNat_add,
    BitVec.ofNat_mul, BitVec.add_assoc, BitVec.mul_comm]

theorem captureCore_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    {enable alive ok e1 em : Bool}
    (h8 : s.gpr .r8 = off B (slot w aRoot)) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (h15 : s.gpr .r15 = mask enable) (hdx : s.gpr .rdx = mask em)
    (ha : word s.mem B (flagsAt w) = mask alive)
    (ho : word s.mem B (flagsAt w + 8) = mask ok)
    (he : word s.mem B (8 * sMask) = mask e1) :
    WP isa (.block captureCore) s fun t =>
      t.gpr .rbp = mask (!(alive && enable && e1)) ∧
      t.mem = (s.mem.writeW (off B (flagsAt w + 8)) (mask (ok || (alive && enable && e1)))).writeW
        (off B (flagsAt w)) (mask (alive && !(enable && (e1 || em)))) ∧
      Keep [.rcx, .r15, .rax, .rbp, .r11, .rdx] s t := by
  have hz := h.hZ
  have hZ16 : slot w 16 ≤ 2 ^ 64 := by have := h.scr.nowrap; omega_arith
  have haZ : flagsAt w + 16 ≤ Z := by
    unfold flagsAt slot aRoot at *
    omega_arith
  have hmZ : 8 * sMask + 8 ≤ Z := by
    unfold slot at hz
    dsimp only [sMask, sFn]
    omega_arith
  have hea := active_ea h8 h12
  have heo := found_ea h8 h12
  have haddr : off B (slot w aRoot) + BitVec.ofNat 64 w * 8#64 = off B (flagsAt w) := by
    simpa only [State.ea, active, ix, h8, h12, show BitVec.ofInt 64 0 = 0#64 from rfl,
      BitVec.add_zero] using hea
  have haddr8 : off B (flagsAt w) + 8#64 = off B (flagsAt w + 8) := by
    simp [off, BitVec.ofNat_add, BitVec.add_assoc]
  unfold captureCore
  refine WP.mono (WP.keep [.rcx, .r15, .rax, .rbp, .r11, .rdx] (Q := fun t =>
      t.gpr .rbp = mask (!(alive && enable && e1)) ∧
      t.mem = (s.mem.writeW (off B (flagsAt w + 8)) (mask (ok || (alive && enable && e1)))).writeW
        (off B (flagsAt w)) (mask (alive && !(enable && (e1 || em))))) (by
    xrun [active, found, ix, h8, h12, haddr, haddr8, State.ea, hdr, h.rdi, hdrOff, h15, hdx, ha, ho, he,
      show BitVec.ofInt 64 0 = 0#64 from rfl, show BitVec.ofInt 64 8 = 8#64 from rfl,
      h.scr.ld (d := flagsAt w) (by omega_arith), h.scr.ld (d := flagsAt w + 8) (by omega_arith),
      h.scr.st (d := flagsAt w) (by omega_arith), h.scr.st (d := flagsAt w + 8) (by omega_arith),
      h.scr.ld (d := 8 * sMask) (by omega_arith), mask_and', mask_or, mask_not]
    cases alive <;> cases enable <;> cases ok <;> cases e1 <;> cases em <;> exact ⟨rfl, rfl⟩) rfl)
    fun t ⟨⟨hr, hm⟩, hk⟩ => ⟨hr, hm, hk⟩

theorem enabled_ok {s : State} {B : Addr} {Z w sigma : Nat} (h : Ws s B Z w)
    (hT : word s.mem B (8 * sT) = BitVec.ofNat 64 sigma) (hsigma : sigma < 2 ^ 64)
    {j : Option Nat} (hj : j = none ∨ j = some 1) :
    WP isa (.block (enabled j)) s fun u =>
      u.gpr .r15 = mask (permit j sigma) ∧ u.mem = s.mem ∧ Keep [.rax, .r15] s u := by
  have h256 := h.ws_ok
  have hZ := h.hZ
  have hdrZ : 8 * sT + 8 ≤ Z := by unfold slot at hZ; dsimp only [sT, sFn]; omega_arith
  rcases hj with rfl | rfl
  · refine WP.mono (WP.keep [.rax, .r15] (Q := fun u =>
        u.gpr .r15 = mask true ∧ u.mem = s.mem) (by
      simp only [enabled]
      xrun) (by decide)) fun u ⟨⟨h15, hm⟩, hk⟩ => ⟨h15, hm, hk⟩
  · refine WP.mono (WP.keep [.rax, .r15] (Q := fun u =>
        u.gpr .r15 = mask (decide (1 < sigma)) ∧ u.mem = s.mem) (by
      simp only [enabled]
      xrun [State.ea, hdr, h.rdi, hdrOff, hT, h.scr.ld (d := 8 * sT) (by omega_arith),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsigma, sbb_mask]
      rfl) (by decide)) fun u ⟨⟨h15, hm⟩, hk⟩ => ⟨h15, hm, hk⟩

theorem minusMask_ok {s : State} {em : Bool} (hem : decide (s.gpr .rbp = 0) = em) :
    WP isa (.block [.alu .cmp .rbp (.imm 1), .alu .sbb .rdx (.reg .rdx)]) s fun u =>
      u.gpr .rdx = mask em ∧ u.mem = s.mem ∧ Keep [.rdx, .rbp] s u := by
  refine WP.mono (WP.keep [.rdx, .rbp] (Q := fun u => u.gpr .rdx = mask em ∧ u.mem = s.mem) (by
    xrun [decide_lt_one', sbb_mask, hem]) rfl) fun _ h => ⟨h.1.1, h.1.2, h.2⟩

theorem captureMasks_ok {s : State} {B : Addr} {Z w sigma : Nat} (h : Ws s B Z w)
    {j : Option Nat} (hj : j = none ∨ j = some 1)
    (hT : word s.mem B (8 * sT) = BitVec.ofNat 64 sigma) (hsigma : sigma < 2 ^ 64)
    {alive ok e1 em : Bool} (hem : decide (s.gpr .rbp = 0) = em)
    (ha : word s.mem B (flagsAt w) = mask alive)
    (ho : word s.mem B (flagsAt w + 8) = mask ok)
    (he : word s.mem B (8 * sMask) = mask e1) :
    WP isa (.block (captureMasks j)) s fun u =>
      u.gpr .r8 = off B (slot w aRoot) ∧ u.gpr .rsi = off B (slot w Public.aY) ∧
      u.gpr .r12 = BitVec.ofNat 64 w ∧
      u.gpr .rbp = mask (!(alive && permit j sigma && e1)) ∧
      u.mem = (s.mem.writeW (off B (flagsAt w + 8)) (mask (ok || (alive && permit j sigma && e1)))).writeW
        (off B (flagsAt w)) (mask (alive && !(permit j sigma && (e1 || em)))) ∧
      Keep [.r12, .r9, .r8, .rsi, .rax, .rbp, .rcx, .rdx, .r11, .r15] s u := by
  have heq : captureMasks j =
      [.alu .cmp .rbp (.imm 1), .alu .sbb .rdx (.reg .rdx)] ++
      ((ws ++ base aRoot .r8 ++ base Public.aY .rsi) ++ (enabled j ++ captureCore)) := by
    simp only [captureMasks, List.append_assoc]
  rw [heq]
  refine WP.block_append_iff.mpr (WP.mono (minusMask_ok hem) fun s₁ ⟨hdx₁, m₁, k₁⟩ => ?_)
  have h₁ := h.congrG (js := []) (hs := []) (by rw [m₁]; exact Frm.refl _ _ _)
    (by simp) k₁ (by decide)
  refine WP.block_append_iff.mpr (WP.mono (bases2_ok h₁ aRoot Public.aY)
    fun s₂ ⟨h12₂, h8₂, hsi₂, m₂, k₂⟩ => ?_)
  have k02 := k₁.trans k₂
  have h₂ := h.congrG (js := []) (hs := []) (by rw [m₂, m₁]; exact Frm.refl _ _ _)
    (by simp) k02 (by decide)
  refine WP.block_append_iff.mpr (WP.mono (enabled_ok (sigma := sigma) h₂ (by rw [m₂, m₁]; exact hT) hsigma hj)
    fun s₃ ⟨h15₃, m₃, k₃⟩ => ?_)
  have k03 := k02.trans k₃
  have h₃ := h.congrG (js := []) (hs := []) (by rw [m₃, m₂, m₁]; exact Frm.refl _ _ _)
    (by simp) k03 (by decide)
  have h8₃ := (k₃.gpr (by decide)).trans h8₂
  have h12₃ := (k₃.gpr (by decide)).trans h12₂
  refine WP.mono (captureCore_ok (enable := permit j sigma) (alive := alive) (ok := ok) (e1 := e1) (em := em)
    h₃ h8₃ h12₃ h15₃
    (by rw [(k₃.gpr (by decide)), (k₂.gpr (by decide))]; exact hdx₁)
    (by rw [m₃, m₂, m₁]; exact ha) (by rw [m₃, m₂, m₁]; exact ho)
    (by rw [m₃, m₂, m₁]; exact he)) fun u ⟨hbp, mu, ku⟩ => ?_
  rw [m₃, m₂, m₁] at mu
  exact ⟨(ku.gpr (by decide)).trans h8₃,
    (ku.gpr (by decide)).trans ((k₃.gpr (by decide)).trans hsi₂),
    (ku.gpr (by decide)).trans h12₃, hbp, mu, (k03.trans ku).mono (by decide)⟩

end VG.Proof.Rsa.X86_64.RecoveryFolded
