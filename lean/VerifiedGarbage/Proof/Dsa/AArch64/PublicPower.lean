module

public import VerifiedGarbage.Proof.Dsa.AArch64.Frame
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Impl.Dsa.AArch64.PublicPower
import VerifiedGarbage.Proof.Dsa.AArch64.EncodePower
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import VerifiedGarbage.Proof.Dsa.AArch64.Load
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Dsa.AArch64.PublicExponent`, which this module and modules that import it used -/

section

/-! # Exponentiation by public windows

As RSA's (`Proof/Bignum/AArch64/CrtExp.lean`), with the public windows of
`PublicWindow.lean`: two windows a byte, the bytes of the exponent, and the
whole loop after RSA's start and table (`crtExpHead_ok`). -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.PublicPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Impl.Dsa.AArch64.PublicPower

/-- The public loop's bytes. -/
def pubBytes (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .loop (seqs [.block byteHead, .loop (seqs (window mul)) (.nonzero .x .x3), .block byteNext]) (.nonzero .x .x3)

theorem pubExpLoop_eq (mul : Nat → Nat → Nat → Prog isa) (sp sl : Nat) :
    VG.Impl.Dsa.AArch64.PublicPower.expLoop mul sp sl = expInit sp sl :: (tabBuild mul ++ [pubBytes mul]) := by
  simp [VG.Impl.Dsa.AArch64.PublicPower.expLoop, expInit, pubBytes, byteHead, byteNext]

/-- Window `j` of the byte `v`. -/
theorem pubWinStep_ok (M : Mont) {t s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x E v : Nat} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hv : v < 256) {j : Nat}
    (hj : j < 2) (hI : CWinInv t P wx minv X Xc Q x E v j s) :
    WP isa (seqs (window M.mm)) s fun s' => CWinInv t P wx minv X Xc Q x E v (j + 1) s' ∧
      ((s'.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ 2) := by
  have hp : 16 ^ j ≤ 16 := by rcases (show j = 0 ∨ j = 1 by omega_arith) with rfl | rfl <;> decide
  refine WP.mono (pubWin_ok M (E := E * 16 ^ j + v / 16 ^ (2 - j)) hI.ctx hI.tab hw hw' hR hI.ylt hI.y hI.v
    (by have := Nat.mul_le_mul_left v hp; omega_arith) hI.b (by omega_arith))
    fun s' ⟨hc', htab', hY', hYv', hV', hb', h3', hfr', k'⟩ => ⟨⟨hc', htab', hY', ?_, ?_, ?_,
      hI.frm.trans hfr', (hI.keep.trans k').mono (by decide)⟩, ?_⟩
  · intro hq; rw [hYv' hq, win_step hv hj]
  · rw [hV', Nat.pow_succ]; congr 1; rw [Nat.mul_comm 16, Nat.mul_assoc]
  · rw [hb']; congr 1
  · rw [h3', cnt_ne (by omega_arith)]; omega_arith

/-- The two windows of the byte `v`: `Y ≡ x^E R` becomes `x^(256 E + v) R`. -/
theorem pubWins_ok (M : Mont) {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x E v : Nat} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hv : v < 256)
    (h0 : CWinInv t P wx minv X Xc Q x E v 0 t) :
    WP isa (.loop (seqs (window M.mm)) (.nonzero .x .x3)) t (CWinInv t P wx minv X Xc Q x E v 2) :=
  count_loop (cr := .x3) (n := 2) (by decide) (CWinInv t P wx minv X Xc Q x E v)
    (fun _ hj _ hI => pubWinStep_ok M hw hw' hR hv hj hI) h0


/-- One byte of the exponent: its two windows, then the next byte. -/
theorem pubByte_ok (M : Mont) {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x : Nat} {ep : Addr} {L : Nat} {eb : List Byte} {i : Nat} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hL : eb.length = L) (hL' : L < 2 ^ 31) (hi : i < L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega_arith))
    (hout : ∀ i < L, slot wx 8 + tabBytes wx ≤ ofs P (ep + BitVec.ofNat 64 i))
    (hI : CByteInv t₀ P wx minv X Xc Q x ep L eb i t) :
    WP isa (seqs [.block byteHead, .loop (seqs (window M.mm)) (.nonzero .x .x3), .block byteNext]) t fun t' =>
      CByteInv t₀ P wx minv X Xc Q x ep L eb (i + 1) t' ∧ ((t'.gpr .x3).toNat ≠ 0 ↔ i + 1 ≠ L) := by
  have hn := hI.ctx.scrT.nowrap
  simp only [seqs]
  refine WP.seq (WP.mono (crtByteHead_ok hL hi hrd hbytes hout hI) fun t₁ ⟨hm₁, k₁, hB0⟩ => ?_)
  have hv : (eb[i]'(by omega_arith)).toNat < 256 := (eb[i]'(by omega_arith)).isLt
  refine WP.seq (WP.mono (pubWins_ok M hw hw' hR hv hB0) fun t₂ h₂ => ?_)
  -- The next byte.
  have hc₂ := h₂.ctx
  have hh₂ : ∀ k < 32, k ≠ Crt.sV → k ≠ Crt.sBit → k ≠ Crt.sNib → k ≠ Crt.sEnt → k ≠ Crt.sJ →
      word t₂.mem P (8 * k) = word t.mem P (8 * k) := fun k hk h1 h2 h3 h4 h5 => by
    rw [h₂.frm.word_eq (crtWinRanges_hdr wx hk h1 h2 h3 h4 h5) (by omega_arith), hm₁,
      hdrStore_hdr (i := Crt.sBit) _ _ _ (by decide) hk (Ne.symm h2),
      hdrStore_hdr (i := Crt.sV) _ _ _ (by decide) hk (Ne.symm h1)]
  have hidx₂ := (hh₂ Crt.sI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI.idx
  have hlen₂ := (hh₂ Crt.sExpLen (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    hI.len
  have he₂ := (hh₂ Crt.sExp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI.e
  have hlen₂' : (t₂.mem.writeW (off P (8 * Crt.sI)) (BitVec.ofNat 64 (i + 1))).readW (off P (8 * Crt.sExpLen)) 64 =
      BitVec.ofNat 64 L := by
    rw [← hlen₂]; exact hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide)
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t' => t'.mem = t₂.mem.writeW (off P (8 * Crt.sI))
      (BitVec.ofNat 64 (i + 1)) ∧ t'.gpr .x3 = BitVec.ofNat 64 L - BitVec.ofNat 64 (i + 1)) (by
    brun [byteNext, hc₂.good.x0, hdr_enc (show Crt.sI < 32 by decide), hdr_enc (show Crt.sExpLen < 32 by decide),
      hc₂.ld (i := Crt.sI) (by decide), hc₂.st (i := Crt.sI) (by decide), hidx₂, ofNat_add_ofNat,
      hc₂.ld (i := Crt.sExpLen) (by decide), hlen₂']) (by decide) (by decide) (by decide +kernel))
    fun t' ⟨⟨hm', h3'⟩, k'⟩ => ⟨?_, ?_⟩
  · have o' := writeW_outside t₂.mem P (d := 8 * Crt.sI) (BitVec.ofNat 64 (i + 1)) (by decide)
    rw [← hm'] at o'
    have f' : Frm P (crtExpRanges wx) t₂.mem t'.mem := Frm.of_outside o' (by simp [crtExpRanges])
    have hY0 := slot_le (w := wx) (show aY < 8 by decide)
    have hYe : wv t'.mem P (slot wx aY) wx = wv t₂.mem P (slot wx aY) wx :=
      o'.wv (by have := hdr_lt_slot wx aY (show Crt.sI < 32 by decide); omega_arith) (by omega_arith)
    refine ⟨hc₂.of_frm f' k'.wr (k'.gpr .x0 (by decide)), ?_, hYe ▸ h₂.ylt, fun hq => ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    · have f₁ : Frm P (crtExpRanges wx) t.mem t₁.mem := by
        rw [hm₁]
        exact (Frm.of_outside (writeW_outside t.mem P _ (d := 8 * Crt.sV) (by decide))
          (by simp [crtExpRanges, crtWinRanges])).trans
          (Frm.of_outside (writeW_outside _ P _ (d := 8 * Crt.sBit) (by decide))
            (by simp [crtExpRanges, crtWinRanges]))
      exact ((hI.frm.trans f₁).trans (h₂.frm.mono (crtWinRanges_sub wx))).trans f'
    · exact (((hI.keep.trans k₁).trans h₂.keep).trans k').mono (by decide)
  · rw [h3', VG.Offset.ofNat_sub_ofNat (show i + 1 ≤ L by omega_arith), cnt_ne (by omega_arith)]
    omega_arith


/-- The exponentiation in a prime's workspace: `Y < X` and `[aXc] < X`
stay so, and if `Q` gives `Y ≡ R` and `[aXc] ≡ x R` modulo `X`, then
`Y ≡ x^d R`, for the exponent `d` whose `L` bytes `eb` (most significant
first) are at `ep`, outside the working space, the pointer and length in
the modulus' header slots `sp` and `sl`. -/
theorem pubExpLoop_ok (M : Mont) {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X x : Nat}
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
    WP isa (seqs (VG.Impl.Dsa.AArch64.PublicPower.expLoop M.mm sp sl)) s fun t => SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx < X ∧
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
  rw [pubExpLoop_eq, ← List.cons_append]
  refine wp_seqs_append (by simp) (by simp) (WP.mono (crtExpHead_ok M hc hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc
    hsp hsl hep hel) fun t₂ h₂ => ?_)
  simp only [seqs, pubBytes]
  refine WP.mono (count_loop (cr := .x3) (n := eb.length) (by omega_arith)
    (CByteInv s (off B o) wx minv X (wv s.mem (off B o) (slot wx Crt.aXc) wx) Q x ep eb.length eb)
    (fun i hi' t hI => pubByte_ok M hw2 (by omega_arith) hR rfl (by omega_arith) hi' he.rd he.val hout hI) h₂)
    fun t hI => ?_
  exact ⟨hc.of_frmT hI.frm (crtExpRanges_ok wx) hI.keep.wr (hI.keep.gpr .x0 (by decide)), hI.ylt,
    fun hq => by rw [hI.y hq, pre_len], hI.frm, hI.keep⟩


end VG.Proof.Dsa.AArch64.PublicPower

end

end

/-! # Public exponentiation through Montgomery encoding and decoding

As `Power.lean`, with the public windows (`PublicExponent.lean`). -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.PublicPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Dsa.AArch64
open VG.Impl.Dsa.AArch64

/-- DSA modular exponentiation in Montgomery representation. The exponent
is a nonempty byte string outside the scratch workspace; leading zeroes
are permitted. This lemma makes no primality or group-order assumption. -/
theorem expLoop_ok (M : Mont) {s : State} {B : Addr} {Z o w wx : Nat}
    {minv : BitVec 64} {m x : Nat}
    (hc : SubCtx s B Z o w wx minv) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : m % 2 = 1)
    (hxl : wv s.mem (off B o) (slot wx Crt.aXc) wx < m)
    (hxc : wv s.mem (off B o) (slot wx Crt.aXc) wx % m = x * 2 ^ (64 * wx) % m)
    (hyl : wv s.mem (off B o) (slot wx aY) wx < m)
    (hyc : wv s.mem (off B o) (slot wx aY) wx % m = 2 ^ (64 * wx) % m)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb) :
    WP isa (seqs (VG.Impl.Dsa.AArch64.PublicPower.expLoop M.mm sp sl)) s fun t =>
      SubCtx t B Z o w wx minv ∧ wv t.mem (off B o) (slot wx aY) wx < m ∧
      wv t.mem (off B o) (slot wx aY) wx % m =
        Spec.Dsa.powMod x (Spec.Dsa.decodeBE eb) m * 2 ^ (64 * wx) % m ∧
      Frm (off B o) (crtExpRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (pubExpLoop_ok M (Q := True) hc hw2 hwx hw30 hn hinv hodd hxl
    (fun _ => hxc) hyl (fun _ => hyc) hsp hsl hep hel hL1 hL2 he) fun t ht => ?_
  obtain ⟨hctx, hlt, hval, hframe, hkeep⟩ := ht
  refine ⟨hctx, hlt, ?_, hframe, hkeep⟩
  rw [VG.Proof.Dsa.powMod_eq, VG.Proof.Dsa.decodeBE_os2ip, Nat.mod_mul_mod]
  exact hval True.intro

/-- The ordinary result of exponentiation, for an odd (possibly composite)
modulus. The exponent may be caller bytes or bytes in the scratch suffix. -/
theorem encodedPower_ok (M : Mont) {s : State} {B : Addr} {Z o w wx m x : Nat}
    {minv : BitVec 64} (hc : SubCtx s B Z o w wx minv)
    (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hone : wv s.mem (off B o) (slot wx aOne) wx = 1)
    (hxl : wv s.mem (off B o) (slot wx Crt.aXc) wx < m)
    (hxc : wv s.mem (off B o) (slot wx Crt.aXc) wx % m = x * 2 ^ (64 * wx) % m)
    (hyl : wv s.mem (off B o) (slot wx aY) wx < m)
    (hyc : wv s.mem (off B o) (slot wx aY) wx % m = 2 ^ (64 * wx) % m)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb) :
    WP isa (VG.Impl.Dsa.AArch64.PublicPower.encodedPower M.mm sp sl) s fun t =>
      SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx = Spec.Dsa.powMod x (Spec.Dsa.decodeBE eb) m ∧
      ModCtx t (off B o) (slot wx 8) wx minv m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hmctx : ModCtx s (off B o) (slot wx 8) wx minv m := ⟨hc.good, hn, hinv⟩
  have hnZ := hc.good.scr.nowrap
  have hR := coprime_pow2 hodd (64 * wx)
  unfold VG.Impl.Dsa.AArch64.PublicPower.encodedPower
  refine WP.seq (WP.mono (expLoop_ok M hc hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc
    hsp hsl hep hel hL1 hL2 he) fun u ⟨hu, hlt, hv, hf, hk⟩ => ?_)
  have hmu := modCtx_exp hmctx hu.good hf (Nat.le_refl _)
  have oneSep := crtExpRanges_arr wx (j := aOne) (by decide) (by decide) (by decide) (by decide) (by decide)
  have oneSlot := slot_le (w := wx) (show aOne < 8 by decide)
  have huone : wv u.mem (off B o) (slot wx aOne) wx = 1 :=
    (hf.wv_eq (fun r hr => by have := oneSep r hr; omega_using [this]) (by omega_using [hnZ, oneSlot])).trans hone
  refine WP.mono (mont_step M hmu (Nat.le_refl _) hw2 (by omega_using [hwx, hw30])
    (by unfold MmUse; decide) (by rw [huone]; exact hm)) fun t ⟨hmt, hlt', hv', hf', hk'⟩ => ?_
  rw [huone] at hv'
  have result := VG.Proof.Dsa.mont_decode hR hv hv'
  rw [Nat.mod_eq_of_lt hlt', Nat.mod_eq_of_lt (VG.Proof.Dsa.powMod_lt _ _ (by omega_using [hm]))] at result
  exact ⟨arrays_context hu hf' (by decide) hk', result, hmt,
    (exp_work hf).trans (arrays_work hf' (by decide)), (hk.trans hk').mono (by decide)⟩

/-- Exponentiation of an ordinary, possibly unreduced base, using the
prepared constants and an exponent from the parent call header. -/
theorem powerCore_ok (M : Mont) {s : State} {B : Addr} {Z o w wx m x : Nat}
    {minv : BitVec 64} (hc : SubCtx s B Z o w wx minv)
    (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hone : wv s.mem (off B o) (slot wx aOne) wx = 1)
    (hx : wv s.mem (off B o) (slot wx aX) wx = x)
    (hR2 : wv s.mem (off B o) (slot wx aR2) wx = 2 ^ (128 * wx) % m)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb) :
    WP isa (VG.Impl.Dsa.AArch64.PublicPower.powerCore M.mm sp sl) s fun t =>
      SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx = Spec.Dsa.powMod x (Spec.Dsa.decodeBE eb) m ∧
      ModCtx t (off B o) (slot wx 8) wx minv m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hR2' : wv s.mem (off B o) (slot wx aR2) wx =
      (2 ^ (64 * wx) * 2 ^ (64 * wx)) % m := by
    rw [hR2, ← Nat.pow_add, show 64 * wx + 64 * wx = 128 * wx by omega_using []]
  unfold VG.Impl.Dsa.AArch64.PublicPower.powerCore
  refine WP.seq (WP.mono (encodePower_ok M ⟨hc.good, hn, hinv⟩ (Nat.le_refl _) hw2 (by omega_using [hwx, hw30])
    hm hodd hx hR2' hone) fun u ⟨hu, hux, huy, huone, hf, hk⟩ => ?_)
  have hcu := arrays_context hc hf (by decide) hk
  have hfu := arrays_work hf (by decide)
  have hsrc := work_source hc hfu hk he
  refine WP.mono (encodedPower_ok M hcu hw2 hwx hw30 hm hodd hu.modulus hu.inverse huone
    (by rw [hux]; exact Nat.mod_lt _ (by omega_using [hm]))
    (by rw [hux, Nat.mod_mod])
    (by rw [huy]; exact Nat.mod_lt _ (by omega_using [hm]))
    (by rw [huy, Nat.mod_mod]) hsp hsl
    ((work_parent hc hfu hsp).trans hep) ((work_parent hc hfu hsl).trans hel) hL1 hL2 hsrc)
    fun t ⟨hct, hresult, hmt, hft, hkt⟩ =>
      ⟨hct, hresult, hmt, hfu.trans hft, (hk.trans hkt).mono (by decide)⟩

/-- Complete exponentiation, including constants setup and loading the base.
Both byte buffers remain valid when they occupy the inactive scratch suffix. -/
theorem power_ok (M : Mont) {s : State} {B : Addr} {Z o w wx m : Nat}
    {minv : BitVec 64} (hc : SubCtx s B Z o w wx minv)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    {bp bl sp sl : Nat} (hbp : bp < 32) (hbl : bl < 32) (hsp : sp < 32) (hsl : sl < 32)
    {base exp : Addr} {bb eb : List Byte}
    (hb : word s.mem B (8 * bp) = base)
    (hblen : word s.mem B (8 * bl) = BitVec.ofNat 64 bb.length)
    (hbs : Src s B Z base bb) (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ wx)
    (he : word s.mem B (8 * sp) = exp)
    (helen : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hes : Src s B Z exp eb) (he1 : 1 ≤ eb.length) (he2 : eb.length ≤ 1024) :
    WP isa (VG.Impl.Dsa.AArch64.PublicPower.power M.mm bp bl sp sl) s fun t =>
      SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx =
        Spec.Dsa.powMod (Spec.Dsa.decodeBE bb) (Spec.Dsa.decodeBE eb) m ∧
      ModCtx t (off B o) (slot wx 8) wx minv m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold VG.Impl.Dsa.AArch64.PublicPower.power
  refine WP.seq (WP.mono (prepare_ok M hc hw2 hw48 hm hodd hn hinv)
    fun u ⟨hcu, hmu, huone, hur2, hfu, hku⟩ => ?_)
  refine WP.seq (WP.mono (load_ok hcu hw2 hwx hw30 (by decide) hbp hbl
    ((work_parent hc hfu hbp).trans hb) ((work_parent hc hfu hbl).trans hblen)
    (work_source hc hfu hku hbs) hb1 (by omega_using [hw48, hbw]) hbw)
    fun v ⟨hcv, hvbase, hfv, hkv⟩ => ?_)
  have hfa : Arrays (off B o) wx [aX] u.mem v.mem :=
    Arrays.of_outside (List.mem_singleton_self aX) hfv (Nat.le_refl _) (Nat.le_refl _)
  have hfw := arrays_work hfa (by decide)
  have hz := hcu.good.scr.nowrap
  have vn := (hfa.wv_of_not_mem (show aN < 8 by decide) (by decide) hz).trans hmu.modulus
  have vi : ((word v.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hfa.word0_of_not_mem (by decide) (by decide) hz (by omega_using [hw2])]
    exact hmu.inverse
  have vone := (hfa.wv_of_not_mem (show aOne < 8 by decide) (by decide) hz).trans huone
  have vr2 := (hfa.wv_of_not_mem (show aR2 < 8 by decide) (by decide) hz).trans hur2
  have hf := hfu.trans hfw
  have hk := (hku.trans hkv).mono (show ∀ r ∈ mmRegs ++ mmRegs, r ∈ mmRegs by decide)
  refine WP.mono (powerCore_ok M hcv hw2 hwx hw30 hm hodd vn vi vone hvbase vr2
    hsp hsl ((work_parent hc hf hsp).trans he) ((work_parent hc hf hsl).trans helen)
    he1 he2 (work_source hc hf hk hes)) fun t ⟨hct, hresult, hmt, hft, hkt⟩ =>
      ⟨hct, hresult, hmt, hf.trans hft, (hk.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.PublicPower
