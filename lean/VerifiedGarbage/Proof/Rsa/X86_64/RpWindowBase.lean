module

import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Rsa.X86_64.RpSq
import VerifiedGarbage.Proof.Bignum.CrtExp
public import VerifiedGarbage.Proof.Rsa.X86_64.RpCst

/-! # Recovery windows: copies, multiplication and masked table selection -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt)

namespace RecoveryWindow

/-- A copy outside the recovery constants preserves their context. -/
theorem copy_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t o a : Nat}
    (hc : Cst s B Z w minv N el r t) (ho : o < 16) (ha : a < 16) (hoa : o ≠ a)
    (hco : o ∉ cArr) :
    WP isa (copyA o a) s fun u => Cst u B Z w minv N el r t ∧
      Frm B (rg w [o] []) s.mem u.mem ∧ Keep mmRegs s u ∧
      wv u.mem B (slot w o) w = wv s.mem B (slot w a) w := by
  refine WP.mono (copyA_ok hc.ws ho ha hoa) fun u ⟨hv, out, k⟩ => ?_
  have hf : Frm B (rg w [o] []) s.mem u.mem := Frm.rg_of_out out (by omega) _ _ (by simp)
  exact ⟨hc.congr hf (fun j hj => by simp only [List.mem_singleton]; intro he; exact hco (he ▸ hj))
    (by simp) k (by decide), hf, k.mono (by decide), hv⟩

/-- All window multiplications write `Y`, leaving the cached powers alone. -/
theorem mul_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t a b : Nat}
    (hc : Cst s B Z w minv N el r t) (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hlt : wv s.mem B (slot w b) w < N) :
    WP isa (M.mm aY a b) s fun u => Cst u B Z w minv N el r t ∧
      Frm B (rg w [aAcc, aTmp, aY] []) s.mem u.mem ∧ Keep mmRegs s u ∧
      wv u.mem B (slot w aY) w < N ∧
      wv u.mem B (slot w aY) w * 2 ^ (64 * w) % N =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % N := by
  have hw2 := hc.ws.w2
  have hg := hc.good
  refine WP.mono (M.mm_ok hg.1 hg.2 hc.ws.w1 (by omega) (by decide) ha hb
    (by decide) (by decide) ha1 hb1 hc.hinv (by rw [hc.hn]; exact hlt) ha2 hb2)
    fun u ⟨_, hlt', hv, arrays, k⟩ => ?_
  rw [hc.hn] at hlt' hv
  have hf : Frm B (rg w [aAcc, aTmp, aY] []) s.mem u.mem := Frm.rg_of_arrays arrays _ _ (by decide)
  exact ⟨hc.congr hf (by decide) (by simp) k (by decide), hf, k, hlt', hv⟩

theorem shr62 (x : BitVec 64) : x >>> 62 = BitVec.ofNat 64 (x.toNat / 2 ^ 62) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by have := x.isLt; omega_using [])]

/-- The fixed addresses and the mask of a two-bit digit unequal to `j`. -/
theorem pickRegs_ok {s : State} {B : Addr} {Z w a j V : Nat}
    (h : Ws s B Z w) (hj : j < 4)
    (hv : word s.mem B (8 * sC2) = BitVec.ofNat 64 V) (hV : V < 2 ^ 64) :
    WP isa (.block (ws ++ base aXm .r8 ++ base a .rsi ++
      ([.mov .rax (.mem (hdr sC2)), .shift .shr .rax 62,
        .alu .xor .rax (.imm (BitVec.ofNat 32 j)), .alu .cmp .rax (.imm 1),
        .alu .sbb .rbp (.reg .rbp), .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))] : List Instr))) s fun u =>
      u.gpr .r8 = off B (slot w aXm) ∧ u.gpr .rsi = off B (slot w a) ∧
      u.gpr .r12 = BitVec.ofNat 64 w ∧ u.gpr .rbp = mask (decide (V / 2 ^ 62 ≠ j)) ∧
      u.mem = s.mem ∧ Keep [.r12, .r9, .r8, .rsi, .rax, .rbp] s u := by
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun u₁ ⟨h12, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aXm (r := .r8) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9)
    fun u₂ ⟨h8, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok a (r := .rsi) (by decide) ((k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans h.rdi))
    ((k₂.gpr (by decide)).trans h9)) fun u₃ ⟨hsi, m₃, k₃⟩ => ?_
  have kk := (k₁.trans k₂).trans k₃
  have hs := h.scr.congr kk.2.2
  have hdi : u₃.gpr .rdi = B := (kk.gpr (by decide)).trans h.rdi
  have he : (BitVec.signExtend 64 (BitVec.ofNat 32 j)) = BitVec.ofNat 64 j := sx_ofNat (by omega)
  have hd : (BitVec.ofNat 64 (V / 2 ^ 62) ^^^ BitVec.ofNat 64 j = 0) ↔ V / 2 ^ 62 = j := by
    rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_eq_zero_iff]
    exact ofNat64_inj (by omega) (by omega)
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun u =>
    u.gpr .rbp = mask (decide (V / 2 ^ 62 ≠ j)) ∧ u.mem = u₃.mem) (by
      xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * sC2)
        (by have := h.h256; simp only [sC2, sFn]; omega), m₃, m₂, m₁, hv, shr62,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hV, he, decide_lt_one', hd, sbb_mask, mask_not]
      simp only [← decide_not]) rfl)
    fun u ⟨⟨hbp, mu⟩, k₄⟩ => ?_
  exact ⟨(k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans h8),
    (k₄.gpr (by decide)).trans hsi,
    (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12)),
    hbp, by rw [mu, m₃, m₂, m₁], (kk.trans k₄).mono (by decide)⟩

/-- One masked table entry, at an address independent of the digit. -/
theorem pick_ok {s : State} {B : Addr} {Z w a j V : Nat}
    (h : Ws s B Z w) (ha : a < 16) (hne : aXm ≠ a) (hj : j < 4)
    (hv : word s.mem B (8 * sC2) = BitVec.ofNat 64 V) (hV : V < 2 ^ 64) :
    WP isa (windowPick a j) s fun u =>
      Frm B (rg w [aXm] []) s.mem u.mem ∧ Keep mmRegs s u ∧
      wv u.mem B (slot w aXm) w =
        if V / 2 ^ 62 ≠ j then wv s.mem B (slot w aXm) w else wv s.mem B (slot w a) w := by
  unfold windowPick
  refine WP.seq (WP.mono (pickRegs_ok h hj hv hV) fun u₁ ⟨h8, hsi, h12, hbp, m₁, k₁⟩ => ?_)
  have hw1 := h.w1
  have hw2 := h.w2
  have sXm := h.sl (j := aXm) (by decide)
  have sa := h.sl ha
  refine WP.mono (sel_ok (h.scr.congr k₁.2.2) h8 hsi hbp h12 (by omega) (by omega) (by omega) (by omega)
    (by have := slot_far (w := w) hne; omega)) fun u ⟨hx, out, k₂⟩ => ?_
  rw [m₁] at hx out
  exact ⟨Frm.rg_of_out out (by omega) _ _ (by decide), (k₁.trans k₂).mono (by decide), by simpa using hx⟩

end RecoveryWindow
end VG.Proof.Rsa.X86_64
