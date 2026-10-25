module

import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Rsa.X86_64.RpSq
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
public import VerifiedGarbage.Proof.Rsa.RecoverFolded
public import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedMasks

/-! # Resetting the root tracker at a nonzero exponent digit -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Impl.Rsa.X86_64.Keys.Recover VG.Impl.Rsa.X86_64.Keys.Recover.Folded
open VG.Impl.Bignum.X86_64.Public (sMask)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem resetCore_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    {d0 alive ok e1 em : Bool} {V : BitVec 64}
    (h8 : s.gpr .r8 = off B (slot w aRoot)) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (hdx : s.gpr .rdx = mask em)
    (ha : word s.mem B (flagsAt w) = mask alive)
    (ho : word s.mem B (flagsAt w + 8) = mask ok)
    (he : word s.mem B (8 * sMask) = mask e1) (hV : word s.mem B (8 * sC2) = V)
    (hd : decide ((V >>> 62) = 0) = d0) :
    WP isa (.block resetCore) s fun u =>
      u.mem = (s.mem.writeW (off B (flagsAt w + 8)) (mask (ok && d0))).writeW
        (off B (flagsAt w)) (mask (if d0 then alive else !(e1 || em))) ∧
      Keep [.rax, .rdx, .rcx, .r15] s u := by
  have hz := h.hZ
  have haZ : flagsAt w + 16 ≤ Z := by unfold flagsAt slot aRoot at *; omega
  have hhZ := h.h256
  have ea := active_ea h8 h12
  have haddr : off B (slot w aRoot) + BitVec.ofNat 64 w * 8#64 = off B (flagsAt w) := by
    simpa only [State.ea, active, ix, h8, h12, show BitVec.ofInt 64 0 = 0#64 from rfl,
      BitVec.add_zero] using ea
  have haddr8 : off B (flagsAt w) + 8#64 = off B (flagsAt w + 8) := by
    simp [off, BitVec.ofNat_add, BitVec.add_assoc]
  have hf64 : flagsAt w + 8 + 8 ≤ 2 ^ 64 := by have := h.scr.nowrap; omega
  have ha64 : flagsAt w + 8 ≤ 2 ^ 64 := by omega
  have hafter : word (s.mem.writeW (off B (flagsAt w + 8)) (mask (ok && d0))) B (flagsAt w) = mask alive := by
    rw [(writeW_outside _ B (mask (ok && d0)) hf64).word (Or.inl (Nat.le_refl _)) ha64]
    exact ha
  unfold resetCore
  refine WP.mono (WP.keep [.rax, .rdx, .rcx, .r15] (Q := fun u =>
      u.mem = (s.mem.writeW (off B (flagsAt w + 8)) (mask (ok && d0))).writeW
        (off B (flagsAt w)) (mask (if d0 then alive else !(e1 || em)))) (by
    xrun [active, found, ix, h8, h12, haddr, haddr8, State.ea, hdr, h.rdi, hdrOff,
      hdx, ha, ho, he, hV, decide_lt_one', sbb_mask, hd, hafter,
      show BitVec.ofInt 64 0 = 0#64 from rfl, show BitVec.ofInt 64 8 = 8#64 from rfl,
      h.scr.ld (d := flagsAt w) (by omega), h.scr.ld (d := flagsAt w + 8) (by omega),
      h.scr.st (d := flagsAt w) (by omega), h.scr.st (d := flagsAt w + 8) (by omega),
      h.scr.ld (d := 8 * sMask) (by dsimp [sMask, sFn]; omega),
      h.scr.ld (d := 8 * sC2) (by dsimp [sC2, sFn]; omega), mask_and', mask_or, mask_not]
    cases d0 <;> cases alive <;> cases ok <;> cases e1 <;> cases em <;> rfl) rfl) fun _ h => h

theorem resetMasks_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    {d0 alive ok e1 em : Bool} {V : BitVec 64}
    (hem : decide (s.gpr .rbp = 0) = em)
    (ha : word s.mem B (flagsAt w) = mask alive)
    (ho : word s.mem B (flagsAt w + 8) = mask ok)
    (he : word s.mem B (8 * sMask) = mask e1) (hV : word s.mem B (8 * sC2) = V)
    (hd : decide ((V >>> 62) = 0) = d0) :
    WP isa (.block resetMasks) s fun u =>
      u.mem = (s.mem.writeW (off B (flagsAt w + 8)) (mask (ok && d0))).writeW
        (off B (flagsAt w)) (mask (if d0 then alive else !(e1 || em))) ∧
      Keep [.r12, .r9, .r8, .rax, .rbp, .rcx, .rdx, .r15] s u := by
  have heq : resetMasks = [.alu .cmp .rbp (.imm 1), .alu .sbb .rdx (.reg .rdx)] ++
      ((ws ++ base aRoot .r8) ++ resetCore) := by simp only [resetMasks, List.append_assoc]
  rw [heq]
  refine WP.block_append_iff.mpr (WP.mono (minusMask_ok hem) fun s₁ ⟨hdx₁, m₁, k₁⟩ => ?_)
  have h₁ := h.congrG (js := []) (hs := []) (by rw [m₁]; exact Frm.refl _ _ _)
    (by simp) k₁ (by decide)
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h₁.ws_ok
    fun s₂ ⟨h12₂, h9₂, m₂, k₂⟩ => ?_))
  refine WP.mono (base_ok aRoot (r := .r8) (by decide)
    ((k₂.gpr (by decide)).trans h₁.rdi) h9₂) fun s₃ ⟨h8₃, m₃, k₃⟩ => ?_
  have k03 := (k₁.trans k₂).trans k₃
  have h₃ := h.congrG (js := []) (hs := []) (by rw [m₃, m₂, m₁]; exact Frm.refl _ _ _)
    (by simp) k03 (by decide)
  refine WP.mono (resetCore_ok (d0 := d0) (alive := alive) (ok := ok) (e1 := e1) (em := em) (V := V)
    h₃ h8₃ ((k₃.gpr (by decide)).trans h12₂)
    (by rw [(k₃.gpr (by decide)), (k₂.gpr (by decide))]; exact hdx₁)
    (by rw [m₃, m₂, m₁]; exact ha) (by rw [m₃, m₂, m₁]; exact ho)
    (by rw [m₃, m₂, m₁]; exact he) (by rw [m₃, m₂, m₁]; exact hV) hd)
    fun u ⟨mu, ku⟩ => ?_
  rw [m₃, m₂, m₁] at mu
  exact ⟨mu, (k03.trans ku).mono (by decide)⟩

end VG.Proof.Rsa.X86_64.RecoveryFolded
