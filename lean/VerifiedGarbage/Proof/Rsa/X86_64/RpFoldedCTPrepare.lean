module

import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedPrepare
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCTExp
public import VerifiedGarbage.Proof.Rsa.X86_64.RpCT2
import VerifiedGarbage.Proof.Rsa.X86_64.RpHalf
import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedPrepare
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCTExp
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpCT2
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpHalf
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops
public import VerifiedGarbage.Impl.Rsa.X86_64.RecoverFolded
public import VerifiedGarbage.Proof.Rsa.Ranges
public import VerifiedGarbage.Proof.Rsa.RecoverFolded
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
public import VerifiedGarbage.Proof.Rsa.X86_64.RpCT5
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.RpCT4
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpCT4

/-! # Fixed-work exponent alignment -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Impl.Rsa.X86_64.Keys.Recover VG.Impl.Rsa.X86_64.Keys.Recover.Folded
open VG.Impl.Bignum.X86_64.Public (aX aY aXm aAcc aTmp sMask)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open Rp

theorem copyExponent_gct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {o a : Nat}
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9])
      (.seq (.block (base a .rsi ++ base o .rbx))
        (.seq (.block [.alu .add .r12 (.imm 2), .alu .add .r12 (.reg .r12)]) VG.Impl.Rsa.X86_64.copyWords)) hint).isSome = true)
    (hw : ∀ p s, Φ p s → WP isa (copyExponent o a) s (Ψ p)) :
    RelCT isa (Two Φ) (copyExponent o a) (Two Ψ) := by
  have e : copyExponent o a = .seq (.block (ws ++ (base a .rsi ++ base o .rbx)))
      (.seq (.block [.alu .add .r12 (.imm 2), .alu .add .r12 (.reg .r12)]) VG.Impl.Rsa.X86_64.copyWords) := by
    simp only [copyExponent, List.append_assoc]
  rw [e]
  exact ws_ct B Z w hws ht fun p s h => e ▸ hw p s h

structure PB (p : RpP) (s : State) : Prop where
  ws : Ws s p.B p.Z (wk p.k)
  hel : word s.mem p.B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 p.el
  e1 : 1 ≤ p.el
  e2 : p.el ≤ 8 * wk p.k
  mlt : wv s.mem p.B (slot (wk p.k) aM) (2 * (wk p.k + 2)) < 2 ^ (64 * bW p)
  glt : wv s.mem p.B (slot (wk p.k) aG) (2 * (wk p.k + 2)) < 2 ^ (64 * bW p)

def halfPins (p : RpP) : Reg → BitVec 64
  | .rdi => p.B
  | .r8 => off p.B (slot (wk p.k) aM)
  | .rsi => off p.B (slot (wk p.k) aH)
  | .r12 => BitVec.ofNat 64 (bW p)
  | _ => 0

/-- The extra alignment mask leaves all pointers and loop sizes fixed. -/
theorem alignHead_pins {p : RpP} {s : State} (h : PB p s) :
    WP isa (.block (halfHead ++ ([.mov .rax (.mem (hdr sT)), .alu .and .rax (.imm 1),
      .mov32 .rbp (.imm 0), .alu .sub .rbp (.reg .rax)] : List Instr))) s
      fun u => ∀ r ∈ [Reg.rdi, .r8, .rsi, .r12], u.gpr r = halfPins p r := by
  have hw2 := h.ws.w2
  have h256 := h.ws.h256
  rw [WP.block_append_iff]
  refine WP.mono (halfHead_ok h.ws h.hel (by have := h.e2; omega_arith))
    fun u ⟨h8, hsi, h12, _, hdi, mu, ku⟩ => ?_
  have hs := h.ws.scr.congr ku.2.2
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun _ => True) (by
    xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * sT) (by dsimp [sT, sFn]; omega_arith)]
    exact ⟨_, rfl⟩) rfl) fun t ⟨_, k⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (k.gpr (by decide)).trans hdi
  · exact (k.gpr (by decide)).trans h8
  · exact (k.gpr (by decide)).trans hsi
  · exact (k.gpr (by decide)).trans h12

/-- A halving's memory addresses and two word loops use only public lengths. -/
theorem half_gct {Φ Ψ : RpP → State → Prop} (hpb : ∀ p s, Φ p s → PB p s)
    (align : Bool)
    (hw : ∀ p s, Φ p s → WP isa (if align then halfAlign else halfOnce) s (Ψ p)) :
    RelCT isa (Two Φ) (if align then halfAlign else halfOnce) (Two Ψ) := by
  have hpins : ∀ p s, Φ p s → WP isa (.block (if align then
      halfHead ++ [.mov .rax (.mem (hdr sT)), .alu .and .rax (.imm 1),
        .mov32 .rbp (.imm 0), .alu .sub .rbp (.reg .rax)] else halfHead)) s
      fun u => ∀ r ∈ [Reg.rdi, .r8, .rsi, .r12], u.gpr r = halfPins p r := by
    intro p s h
    cases align
    · have h := hpb p s h
      have hw2 := h.ws.w2
      exact WP.mono (halfHead_ok h.ws h.hel (by have := h.e2; omega_arith))
        fun _ ⟨h8, hsi, h12, _, hdi, _, _⟩ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact hdi
          · exact h8
          · exact hsi
          · exact h12
    · exact alignHead_pins (hpb p s h)
  cases align
  · unfold halfOnce
    rw [halfHead_eq]
    refine ws_pin_ct RpP.B RpP.Z (fun p => wk p.k) (fun p s h => (hpb p s h).ws)
      (by taint_decide) [.rdi, .r8, .rsi, .r12] halfPins ?_ (by taint_decide) ?_
    · simpa [halfHead_eq] using hpins
    · simpa [halfOnce, halfHead_eq] using hw
  · unfold halfAlign
    rw [halfHead_eq, List.append_assoc]
    refine ws_pin_ct RpP.B RpP.Z (fun p => wk p.k) (fun p s h => (hpb p s h).ws)
      (by taint_decide) [.rdi, .r8, .rsi, .r12] halfPins ?_ (by taint_decide) ?_
    · simpa [halfHead_eq, List.append_assoc] using hpins
    · simpa [halfAlign, halfHead_eq, List.append_assoc] using hw

/-- Halvings preserve the backup, the public lengths and the workspace. -/
theorem PB.half {p : RpP} {s u : State} (h : PB p s)
    (f : Frm p.B (rg (wk p.k) [aM, aM + 1, aH, aH + 1] [sT]) s.mem u.mem)
    {regs : List Reg} (k : Keep regs s u) (hr : .rdi ∉ regs)
    (hm : wv u.mem p.B (slot (wk p.k) aM) (2 * (wk p.k + 2)) < 2 ^ (64 * bW p)) : PB p u := by
  have hz : slot (wk p.k) 16 ≤ 2 ^ 64 := by have := h.ws.hZ; have := h.ws.scr.nowrap; omega_arith
  exact ⟨h.ws.congrG f (by decide) k hr,
    by rw [f.rg_word (by decide) (by decide)]; exact h.hel, h.e1, h.e2, hm,
    by rw [f.rg_wv2 hz (by decide) (by decide) (by decide) (by decide) (Nat.le_refl _)]; exact h.glt⟩

/-- The existing fixed halving scan needs only the bounded exponent. -/
theorem halvingBound_ct : RelCT isa (Two fun p s => PB p s ∧
    0 < wv s.mem p.B (slot (wk p.k) aM) (2 * (wk p.k + 2))) halving (Two PB) := by
  refine two_post ?_ ?_
  · unfold halving
    refine (RelCT.seq (R := Two fun p s => 0 < hN p ∧ HL p 0 s) ?_ halfLoop_ct).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)
    refine two_piece [.rdi] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.ws.rdi, h₂.1.ws.rdi]) (by taint_decide) ?_
    intro p s ⟨h, _⟩
    have hw := h.ws
    have hn := hw.scr.nowrap
    have h256 := hw.h256
    have hz := hw.hZ
    have hw2 := hw.w2
    let m := wv s.mem p.B (slot (wk p.k) aM) (2 * (wk p.k + 2))
    refine WP.mono (halfInit_ok hw h.hel (by have := h.e2; omega_arith))
      fun t ⟨h11, h13, mt, kt⟩ => ⟨by have := hw.w1; unfold hN; omega_arith, t, m, ?_, h.e1, h.e2, h.mlt, h11, ?_⟩
    · have o := writeW_outside s.mem p.B (0 : BitVec 64) (d := 8 * sT) (by simp only [sT, sFn]; omega_arith)
      rw [← mt] at o
      rw [o.word (Or.inl (by simp only [Impl.Bignum.X86_64.Public.sElen, sFn, sT]; omega_arith))
        (by simp only [Impl.Bignum.X86_64.Public.sElen, sFn]; omega_arith)]
      exact h.hel
    · have o := writeW_outside s.mem p.B (0 : BitVec 64) (d := 8 * sT) (by simp only [sT, sFn]; omega_arith)
      rw [← mt] at o
      have f : Frm p.B (rg (wk p.k) [] [sT]) s.mem t.mem := Frm.rg_of_hdr o _ _ (by decide)
      have hs₁ := slot_add (wk p.k) aM 2
      have hs₂ := slot_mono (w := wk p.k) (show aM + 2 ≤ 16 by decide)
      have hs₃ := hdr_lt_slot (wk p.k) aM (show sT < 32 by decide)
      exact ⟨hw.congrG f (by decide) kt (by decide), Keep.refl _ _, h13, Frm.refl _ _ _,
        by rw [o.wv (Or.inr (by omega_arith)) (by omega_arith)]; rfl, by rw [mt, word_writeW_self]; rfl⟩
  · intro p s ⟨h, hm0⟩
    have hw2 := h.ws.w2
    refine WP.mono (halving_ok h.ws h.hel h.e1 h.e2 rfl hm0 h.mlt)
      fun u ⟨_, hM, _, f, k⟩ => h.half (frm_halving f) k (by decide) ?_
    have hs := VG.Proof.Rsa.splitTwos_spec hm0
    have hle : (VG.Spec.Rsa.splitTwos (wv s.mem p.B (slot (wk p.k) aM) (2 * (wk p.k + 2)))).2 ≤
        wv s.mem p.B (slot (wk p.k) aM) (2 * (wk p.k + 2)) := by
      calc _ ≤ 2 ^ (VG.Spec.Rsa.splitTwos _).1 * (VG.Spec.Rsa.splitTwos _).2 :=
        Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
        _ = _ := hs.1.symm
    rw [hM]
    exact Nat.lt_of_le_of_lt hle h.mlt

theorem halfOnce_ct : RelCT isa (Two PB) halfOnce (Two PB) := by
  refine half_gct (fun _ _ h => h) false ?_
  intro p s h
  refine WP.mono (halfOnce_ok h.ws h.hel h.e2 rfl h.mlt) fun u ⟨hM, f, k⟩ =>
    h.half (half_frame f) k (by decide) ?_
  rw [hM]
  split
  · exact h.mlt
  · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h.mlt

theorem halfAlign_ct : RelCT isa (Two PB) halfAlign (Two PB) := by
  refine half_gct (fun _ _ h => h) true ?_
  intro p s h
  let t := (word s.mem p.B (8 * sT)).toNat
  refine WP.mono (halfAlign_ok h.ws h.hel h.e2 rfl h.mlt
    (t := t) (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]) (BitVec.isLt _)) fun u ⟨hM, f, k⟩ =>
      h.half (half_frame f) k (by decide) ?_
  rw [hM]
  split
  · exact h.mlt
  · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h.mlt

theorem backup_ct : RelCT isa (Two GR0) (copyExponent aG aM)
    (Two fun p s => PB p s ∧ 0 < wv s.mem p.B (slot (wk p.k) aM) (2 * (wk p.k + 2))) := by
  refine copyExponent_gct RpP.B RpP.Z (fun p => wk p.k)
    (fun _ _ ⟨_, _, e, h, _⟩ => e ▸ h.S.ws) (by taint_decide) ?_
  intro p s h
  obtain ⟨I, m₀, rfl, h, O, hv⟩ := h
  have hw := h.S.ws
  have hz : slot (wk I.k) 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega_arith
  have he2 : I.el ≤ 8 * wk I.k := by have := h.L.el2; unfold wk; omega_arith
  refine WP.mono (copyExponent_ok hw (o := aG) (a := aM) (by decide) (by decide) (by decide))
    fun u ⟨hG, o, k⟩ => ?_
  have f := pair_frame o
  have hM : wv u.mem I.B (slot (wk I.k) aM) (2 * (wk I.k + 2)) = I.D * I.E - 1 := by
    rw [f.rg_wv2 hz (by simp) (by decide) (by decide) (by decide) (Nat.le_refl _)]; exact h.M
  exact ⟨⟨hw.congrG f (by simp) k (by decide),
    by dsimp only [RpIn.pub]; rw [f.rg_word (by decide) (by simp)]; exact h.S.args.el,
    h.L.el1, he2, by dsimp only [RpIn.pub]; rw [hM]; exact h.mlt, by dsimp only [RpIn.pub]; rw [hG, h.M]; exact h.mlt⟩,
    by dsimp only [RpIn.pub]; rw [hM]; exact h.m0⟩

theorem restore_ct : RelCT isa (Two PB) (copyExponent aM aG) (Two PB) := by
  refine copyExponent_gct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) (by taint_decide) ?_
  intro p s h
  refine WP.mono (copyExponent_ok h.ws (o := aM) (a := aG) (by decide) (by decide) (by decide))
    fun u ⟨hM, o, k⟩ => ?_
  exact h.half ((pair_frame o).rg_mono (by decide) (by simp)) k (by decide) (by rw [hM]; exact h.glt)

/-- The complete alignment preparation has only public loop counts. -/
theorem prepareT_ct : RelCT isa (Two GR0) prepare fun _ _ => True := by
  simp only [prepare, seqs]
  refine RelCT.seq backup_ct (RelCT.seq halvingBound_ct (RelCT.seq restore_ct
    (RelCT.seq halfOnce_ct (RelCT.seq halfAlign_ct ?_))))
  exact two_taint [.rdi] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]) (by taint_decide)

end VG.Proof.Rsa.X86_64.RecoveryFolded
