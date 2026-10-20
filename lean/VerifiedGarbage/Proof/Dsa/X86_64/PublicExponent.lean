module

import VerifiedGarbage.Proof.Dsa.X86_64.PublicWindow
public import VerifiedGarbage.Impl.Dsa.X86_64.PublicPower
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Math

/-! # Composition of public windows into byte-string exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.PublicPower
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.PublicPower

theorem crtWinStep_ok (M : Mont) (Sq : MontS) {t s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x E v : Nat} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hv : v < 256) {j : Nat}
    (hj : j < 2) (hI : CWinInv t P wx minv X Xc (Sq.bd X (2 ^ (64 * wx))) Q x E v j s) :
    WP isa (seqs (window Sq.mm M.mm)) s fun s' => s'.zf = some (decide (j + 1 = 2)) ∧
      CWinInv t P wx minv X Xc (Sq.bd X (2 ^ (64 * wx))) Q x E v (j + 1) s' := by
  have hp : 16 ^ j ≤ 16 := by rcases (show j = 0 ∨ j = 1 by omega_arith) with rfl | rfl <;> decide
  refine WP.mono (crtWin_ok M Sq (E := E * 16 ^ j + v / 16 ^ (2 - j)) hI.ctx hI.tab hw hw' hR hI.ylt hI.y hI.v
    (by have := Nat.mul_le_mul_left v hp; omega_arith) hI.b (by omega_arith) (by omega_arith))
    fun s' ⟨hc', htab', hY', hYv', hV', hb', hz', hfr', k'⟩ => ⟨?_, hc', htab', hY', ?_, ?_, ?_,
      hI.frm.trans hfr', (hI.keep.trans k').mono (by decide)⟩
  · rw [hz']; congr 1; exact decide_eq_decide.mpr (by omega_arith)
  · intro hq; rw [hYv' hq, win_step hv hj]
  · rw [hV', Nat.pow_succ]; congr 1; rw [Nat.mul_comm 16, Nat.mul_assoc]
  · rw [hb']; congr 1

/-- The two windows of the byte `v`: `Y ≡ x^E R` becomes `x^(256 E + v) R`. -/
theorem crtWins_ok (M : Mont) (Sq : MontS) {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x E v : Nat} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hv : v < 256)
    (h0 : CWinInv t P wx minv X Xc (Sq.bd X (2 ^ (64 * wx))) Q x E v 0 t) :
    WP isa (.loop (seqs (window Sq.mm M.mm)) .ne) t (CWinInv t P wx minv X Xc (Sq.bd X (2 ^ (64 * wx))) Q x E v 2) :=
  wp_upto (a := 0) (N := 2) (by decide) (CWinInv t P wx minv X Xc (Sq.bd X (2 ^ (64 * wx))) Q x E v)
    (fun _ _ hj _ hI => crtWinStep_ok M Sq hw hw' hR hv hj hI) (fun _ h => h) h0

theorem crtByte_ok (M : Mont) (Sq : MontS) {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x : Nat} {ep : Addr} {L : Nat} {eb : List Byte} {i : Nat} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hL : eb.length = L) (hL' : L < 2 ^ 31) (hi : i < L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_arith))
    (hout : ∀ i < L, slot wx 8 + tabBytes wx ≤ ofs P (ep + BitVec.ofNat 64 i))
    (hI : CByteInv t₀ P wx minv X Xc (Sq.bd X (2 ^ (64 * wx))) Q x ep L eb i t) :
    WP isa (seqs [.block [.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI)),
        .movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr Crt.sV) .rax, .mov32 .rax (.imm 2),
        .store (hdr Crt.sBit) .rax],
      .loop (seqs (window Sq.mm M.mm)) .ne,
      .block [.mov .rax (.mem (hdr Crt.sI)), .alu .add .rax (.imm 1), .store (hdr Crt.sI) .rax,
        .alu .cmp .rax (.mem (hdr Crt.sExpLen))]]) t fun t' =>
      t'.zf = some (decide (i + 1 = L)) ∧ CByteInv t₀ P wx minv X Xc (Sq.bd X (2 ^ (64 * wx))) Q x ep L eb (i + 1) t' := by
  have hn := hI.ctx.scrT.nowrap
  simp only [seqs]
  rw [crtByteHead_eq]
  refine WP.seq ((WP.block_append_iff).mpr (WP.mono (crtByteHead1_ok hI) fun tₐ ⟨hax, hcx, hIₐ⟩ =>
    WP.mono (crtByteHead2_ok hL hi hrd hbytes hout hIₐ hax hcx) fun t₁ ⟨hm₁, k₁, hB0⟩ => ?_))
  have hv : (eb[i]'(by omega_arith)).toNat < 256 := (eb[i]'(by omega_arith)).isLt
  refine WP.seq (WP.mono (crtWins_ok M Sq hw hw' hR hv hB0) fun t₂ h₂ => ?_)
  -- The next byte.
  have hc₂ := h₂.ctx
  have hh₂ : ∀ k < 32, k ≠ Crt.sV → k ≠ Crt.sBit → k ≠ Crt.sNib → k ≠ Crt.sEnt → k ≠ Crt.sJ →
      word t₂.mem P (8 * k) = word tₐ.mem P (8 * k) := fun k hk h1 h2 h3 h4 h5 => by
    rw [h₂.frm.word_eq (crtWinRanges_hdr wx hk h1 h2 h3 h4 h5) (by omega_arith), hm₁,
      hdrStore_hdr (i := Crt.sBit) _ _ _ (by decide) hk (Ne.symm h2),
      hdrStore_hdr (i := Crt.sV) _ _ _ (by decide) hk (Ne.symm h1)]
  have hidx₂ := (hh₂ Crt.sI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hIₐ.idx
  have he₂ := (hh₂ Crt.sExp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hIₐ.e
  have hlen₂ := (hh₂ Crt.sExpLen (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    hIₐ.len
  have hlen₂' : (t₂.mem.writeW (off P (8 * Crt.sI)) (BitVec.ofNat 64 (i + 1))).readW (off P (8 * Crt.sExpLen)) 64 =
      BitVec.ofNat 64 L := by
    rw [← hlen₂]; exact hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide)
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t₂.mem.writeW (off P (8 * Crt.sI))
      (BitVec.ofNat 64 (i + 1)) ∧ t'.zf = some (decide (i + 1 = L))) (by
    xrun [State.ea, hdr, hc₂.good.rdi, hdrOff, hc₂.ld (i := Crt.sI) (by decide), hc₂.st (i := Crt.sI) (by decide),
      hidx₂, ofNat_add_one, hc₂.ld (i := Crt.sExpLen) (by decide), hlen₂',
      ofNat_sub_beq (show i + 1 < 2 ^ 64 by omega_arith) (show L < 2 ^ 64 by omega_arith)]) rfl)
    fun t' ⟨⟨hm', hz'⟩, k'⟩ => ⟨hz', ?_⟩
  have o' := writeW_outside t₂.mem P (d := 8 * Crt.sI) (BitVec.ofNat 64 (i + 1)) (by decide)
  rw [← hm'] at o'
  have f' : Frm P (crtExpRanges wx) t₂.mem t'.mem := Frm.of_outside o' (by simp [crtExpRanges])
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  have hYe : wv t'.mem P (slot wx aY) wx = wv t₂.mem P (slot wx aY) wx :=
    o'.wv (by have := hdr_lt_slot wx aY (show Crt.sI < 32 by decide); omega_arith) (by omega_arith)
  refine ⟨hc₂.of_frm f' k'.2.2 (k'.gpr (by decide)), ?_, hYe ▸ h₂.ylt, fun hq => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by rw [o'.word (by decide) (by decide)]; exact h₂.tab.tab,
      fun j hj => by rw [o'.wv (by have := hdr_lt_slot wx (8 + j) (show Crt.sI < 32 by decide); omega_arith)
        (by have := ent_le wx hj; omega_arith)]; exact h₂.tab.lt j hj,
      fun hq j hj => by rw [o'.wv (by have := hdr_lt_slot wx (8 + j) (show Crt.sI < 32 by decide); omega_arith)
        (by have := ent_le wx hj; omega_arith)]; exact h₂.tab.val hq j hj⟩
  · rw [hYe, h₂.y hq, pre_succ eb (by omega_arith)]
    congr 3
    simp only [Nat.reducePow, Nat.reduceSub, Nat.pow_zero, Nat.div_one]
    omega_arith
  · rw [hm', word_writeW_self]
  · rw [hm', hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide)]; exact he₂
  · rw [hm', hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide)]; exact hlen₂
  · have f₁ : Frm P (crtExpRanges wx) tₐ.mem t₁.mem := by
      rw [hm₁]
      exact (Frm.of_outside (writeW_outside tₐ.mem P _ (d := 8 * Crt.sV) (by decide))
        (by simp [crtExpRanges, crtWinRanges])).trans
        (Frm.of_outside (writeW_outside _ P _ (d := 8 * Crt.sBit) (by decide))
          (by simp [crtExpRanges, crtWinRanges]))
    exact ((hIₐ.frm.trans f₁).trans (h₂.frm.mono (crtWinRanges_sub wx))).trans f'
  · exact (((hIₐ.keep.trans k₁).trans h₂.keep).trans k').mono (by decide)

theorem crtExpLoop_ok (M : Mont) (Sq : MontS) {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X x : Nat}
    {Q : Prop} (hc : SubCtx s B Z o w wx minv) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem (off B o) (slot wx aN) wx = X)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : X % 2 = 1)
    (hxl : wv s.mem (off B o) (slot wx Crt.aXc) wx < X)
    (hxc : Q → wv s.mem (off B o) (slot wx Crt.aXc) wx % X = x * 2 ^ (64 * wx) % X)
    (hyl : wv s.mem (off B o) (slot wx aY) wx < X)
    (hyc : Q → wv s.mem (off B o) (slot wx aY) wx % X = 2 ^ (64 * wx) % X)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb) :
    WP isa (VG.Impl.Dsa.X86_64.PublicPower.expLoop Sq.mm M.mm sp sl) s fun t => SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx < Sq.bd X (2 ^ (64 * wx)) ∧
      (Q → wv t.mem (off B o) (slot wx aY) wx % X = x ^ Spec.Rsa.os2ip eb * 2 ^ (64 * wx) % X) ∧
      Frm (off B o) (crtExpRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hi := hc.hi
  have hlo := hc.lo
  have hBn := hc.scr.nowrap
  have hPn := hc.scrT.nowrap
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  have hR : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hodd _
  have hout : ∀ i < eb.length, slot wx 8 + tabBytes wx ≤ ofs (off B o) (ep + BitVec.ofNat 64 i) := fun i hi' => by
    have := he.out i hi'
    rcases ofs_rebase B (ep + BitVec.ofNat 64 i) (o := o) (by omega_arith) with ⟨_, h2⟩ | ⟨h1, _⟩
    · omega_arith
    · omega_arith
  unfold VG.Impl.Dsa.X86_64.PublicPower.expLoop
  refine WP.seq (WP.mono (crtExpHead_ok M hc hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc
    hsp hsl hep hel he) fun t₂ h₂ => ?_)
  have hXR : X ≤ 2 ^ (64 * wx) := by rw [← hn]; exact Nat.le_of_lt (wv_lt _ _ _ _)
  replace h₂ : CByteInv s (off B o) wx minv X (wv s.mem (off B o) (slot wx Crt.aXc) wx) (Sq.bd X (2 ^ (64 * wx)))
      Q x ep eb.length eb 0 t₂ := { h₂ with ylt := Nat.lt_of_lt_of_le h₂.ylt (Sq.le hXR) }
  unfold VG.Impl.Dsa.X86_64.PublicPower.byte
  refine wp_upto (a := 0) (N := eb.length) (by omega_arith)
    (CByteInv s (off B o) wx minv X (wv s.mem (off B o) (slot wx Crt.aXc) wx) (Sq.bd X (2 ^ (64 * wx))) Q x ep eb.length eb)
    (fun i _ hi' t hI => crtByte_ok M Sq hw2 (by omega_arith) hR rfl (by omega_arith) hi' he.rd he.val hout hI)
    (fun t hI => ?_) h₂
  exact ⟨hc.of_frmT hI.frm (crtExpRanges_ok wx) hI.keep.2.2 (hI.keep.gpr (by decide)), hI.ylt,
    fun hq => by rw [hI.y hq, pre_len], hI.frm, hI.keep⟩


end VG.Proof.Dsa.X86_64.PublicPower
