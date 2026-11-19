module

public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.Frame
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Impl.Dsa.X86_64.PublicPower
import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Bignum.CrtExp
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Dsa.X86_64.PublicExponent`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.PublicWindow`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.PublicSquares`, which this module and modules that import it used -/

section

/-! # Four squarings with one emitted copy of the arithmetic -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.PublicPower
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.PublicPower

theorem squareCounter_change {s t : State} {P : Addr} {wx : Nat} {mi : BitVec 64} {X Xc v : Nat}
    (hc : CExpCtx s P wx mi X Xc)
    (hm : t.mem = s.mem.writeW (off P (8 * Crt.sNib)) (BitVec.ofNat 64 v))
    (hk : Keep [.rax] s t) :
    CExpCtx t P wx mi X Xc ∧ word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v ∧
    wv t.mem P (slot wx aY) wx = wv s.mem P (slot wx aY) wx ∧
    (∀ k < 32, k ≠ Crt.sNib → word t.mem P (8 * k) = word s.mem P (8 * k)) ∧
    Frm P (crtWinRanges wx) s.mem t.mem := by
  have ho := writeW_outside s.mem P (d := 8 * Crt.sNib) (BitVec.ofNat 64 v) (by decide)
  rw [← hm] at ho
  have hf : Frm P (crtWinRanges wx) s.mem t.mem := Frm.of_outside ho (by simp [crtWinRanges])
  refine ⟨hc.of_win hf hk.2.2 (hk.gpr (by decide)), ?_, ?_, ?_, hf⟩
  · rw [hm, word_writeW_self]
  · exact ho.wv (by have := hdr_lt_slot wx aY (show Crt.sNib < 32 by decide); omega_using [this])
      (by have := hc.scrT.nowrap; have := slot_le (w := wx) (show aY < 8 by decide); omega_arith)
  · intro k hk hn
    rw [hm, hdrStore_hdr _ _ _ (by decide) hk (Ne.symm hn)]

theorem squaresInit_ok {s : State} {P : Addr} {wx : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx s P wx mi X Xc) :
    WP isa (.block squaresInit) s fun t =>
      t.mem = s.mem.writeW (off P (8 * Crt.sNib)) (BitVec.ofNat 64 4) ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.mem = s.mem.writeW (off P (8 * Crt.sNib)) (BitVec.ofNat 64 4)) ?_ rfl)
    fun t ⟨hm, hk⟩ => ⟨hm, hk⟩
  xrun [squaresInit, State.ea, hdr, hc.good.rdi, hdrOff, hc.st (i := Crt.sNib) (by decide)]
  rfl

theorem squaresNext_ok {s : State} {P : Addr} {wx : Nat} {mi : BitVec 64} {X Xc n : Nat}
    (hc : CExpCtx s P wx mi X Xc) (hn : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 n)
    (hn1 : 1 ≤ n) (hn4 : n ≤ 4) :
    WP isa (.block squaresNext) s fun t =>
      t.mem = s.mem.writeW (off P (8 * Crt.sNib)) (BitVec.ofNat 64 (n - 1)) ∧
      t.zf = some (decide (n - 1 = 0)) ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.mem = s.mem.writeW (off P (8 * Crt.sNib)) (BitVec.ofNat 64 (n - 1)) ∧
    t.zf = some (decide (n - 1 = 0))) ?_ rfl) fun t ⟨⟨hm, hz⟩, hk⟩ => ⟨hm, hz, hk⟩
  xrun [squaresNext, State.ea, hdr, hc.good.rdi, hdrOff,
    hc.ld (i := Crt.sNib) (by decide), hc.st (i := Crt.sNib) (by decide), hn,
    ofNat64_pred hn1 (by omega_using [hn4]), ofNat64_beq_zero (show n - 1 < 2 ^ 64 by omega_using [hn4])]

theorem squares_ok (Sq : MontS) {s : State} {P : Addr} {wx : Nat} {mi : BitVec 64}
    {X Xc x E : Nat} {Q : Prop} (hc : CExpCtx s P wx mi X Xc)
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) X)
    (hY : wv s.mem P (slot wx aY) wx < Sq.bd X (2 ^ (64 * wx)))
    (hYv : Q → wv s.mem P (slot wx aY) wx % X = x ^ E * 2 ^ (64 * wx) % X) :
    WP isa (squares Sq.mm) s fun t => CExpCtx t P wx mi X Xc ∧
      wv t.mem P (slot wx aY) wx < Sq.bd X (2 ^ (64 * wx)) ∧
      (Q → wv t.mem P (slot wx aY) wx % X = x ^ (16 * E) * 2 ^ (64 * wx) % X) ∧
      (∀ k < 32, k ≠ Crt.sNib → word t.mem P (8 * k) = word s.mem P (8 * k)) ∧
      Frm P (crtWinRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  let I := fun n (t : State) => 1 ≤ n ∧ n ≤ 4 ∧ CExpCtx t P wx mi X Xc ∧
    wv t.mem P (slot wx aY) wx < Sq.bd X (2 ^ (64 * wx)) ∧
    (Q → wv t.mem P (slot wx aY) wx % X = x ^ (2 ^ (4 - n) * E) * 2 ^ (64 * wx) % X) ∧
    word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 n ∧
    (∀ k < 32, k ≠ Crt.sNib → word t.mem P (8 * k) = word s.mem P (8 * k)) ∧
    Frm P (crtWinRanges wx) s.mem t.mem ∧ Keep mmRegs s t
  unfold squares
  refine WP.seq (WP.mono (squaresInit_ok hc) fun u ⟨hm, ku⟩ => ?_)
  obtain ⟨hcu, count, value, hh, ff⟩ := squareCounter_change hc hm ku
  have start : I 4 u := ⟨by decide, by decide, hcu, value ▸ hY,
    by simpa only [Nat.sub_self, Nat.pow_zero, Nat.one_mul, value] using hYv,
    count, hh, ff, ku.mono (by decide)⟩
  refine WP.loop I ?_ 4 u start
  intro n t ht
  obtain ⟨hn1, hn4, hct, hlt, hv, hn, hhdr, hframe, hkeep⟩ := ht
  refine WP.seq (WP.mono (crtSqS_ok Sq hct hw hw' hR hlt hv)
    fun v ⟨hcv, vl, vv, vh, vf, vk⟩ => ?_)
  refine WP.mono (squaresNext_ok hcv ((vh _ (by decide)).trans hn) hn1 hn4)
    fun z ⟨zm, hz, zk⟩ => ?_
  obtain ⟨hcz, countz, valuez, hh, ff⟩ := squareCounter_change hcv zm zk
  have headers : ∀ k < 32, k ≠ Crt.sNib → word z.mem P (8 * k) = word s.mem P (8 * k) :=
    fun k hk hne => (hh k hk hne).trans ((vh k hk).trans (hhdr k hk hne))
  have frame := (hframe.trans vf).trans ff
  have keep : Keep mmRegs s z := ((hkeep.trans vk).trans zk).mono (by decide)
  have val : Q → wv z.mem P (slot wx aY) wx % X =
      x ^ (2 ^ (4 - (n - 1)) * E) * 2 ^ (64 * wx) % X := by
    intro hq
    have he : 2 * (2 ^ (4 - n) * E) = 2 ^ (4 - (n - 1)) * E := by
      rw [show 4 - (n - 1) = 4 - n + 1 by omega_using [hn1, hn4], Nat.pow_succ]
      ac_rfl
    rw [valuez, vv hq, he]
  by_cases hn : n = 1
  · subst n
    exact Or.inl ⟨by simp [eval, hz],
      hcz, valuez ▸ vl, by simpa using val, headers, frame, keep⟩
  · exact Or.inr ⟨by simp [eval, hz, show n - 1 ≠ 0 by omega_using [hn1, hn]],
      n - 1, by omega_using [hn1], by omega_using [hn1, hn], by omega_using [hn4], hcz, valuez ▸ vl, val,
      countz, headers, frame, keep⟩

end VG.Proof.Dsa.X86_64.PublicPower

end

end

/-! ### `Dsa.X86_64.PublicSelect`, which this module and modules that import it used -/

section

/-! # Direct selection of a public exponentiation-table digit -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.PublicPower
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.PublicPower

/-- Registers for a direct selection, without changing memory. -/
theorem selectHead_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc v : Nat}
    (hc : CExpCtx s P wx minv X Xc)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8))
    (hv : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (.block selectHead) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 wx ∧ t.gpr .rsi = off P (slot wx (8 + v)) ∧
      t.gpr .rbx = off P (slot wx Crt.aT) ∧ t.mem = s.mem ∧
      Keep [.r12, .rax, .rdx, .rsi, .rbx] s t := by
  refine WP.mono (WP.keep [.r12, .rax, .rdx, .rsi, .rbx] (Q := fun t =>
    t.gpr .r12 = BitVec.ofNat 64 wx ∧ t.gpr .rsi = off P (slot wx (8 + v)) ∧
    t.gpr .rbx = off P (slot wx Crt.aT) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  unfold selectHead
  xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := sW) (by decide),
    hc.ld (i := Crt.sNib) (by decide), hc.ld (i := Crt.sTab) (by decide),
    hc.ld (i := sArr Crt.aT) (by decide), hc.good.hdr.hw, hc.good.hdr.harr Crt.aT (by decide), ht, hv,
    execImul]
  simp only [BitVec.ofInt_mul, BitVec.ofInt_toInt]
  simp only [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add, ← BitVec.ofNat_mul,
    off, BitVec.add_assoc]
  congr 2
  unfold slot hdrBytes
  grind

/-- Copy the selected table entry; only the destination array changes. -/
theorem select_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc v : Nat}
    (hc : CExpCtx s P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hv : v < 16)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot wx 8))
    (hn : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa select s fun t => CExpCtx t P wx minv X Xc ∧
      wv t.mem P (slot wx Crt.aT) wx = wv s.mem P (slot wx (8 + v)) wx ∧
      Outside P (slot wx Crt.aT) (8 * wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hT := slot_le (w := wx) (show Crt.aT < 8 by decide)
  have hE := ent_le wx hv
  have hE0 := slot_mono wx (show 8 ≤ 8 + v by omega_using [])
  have hsep := slot_mono wx (show Crt.aT + 1 ≤ 8 by decide)
  have hz := hc.scrT.nowrap
  unfold select
  refine WP.seq (WP.mono (selectHead_ok hc ht hn) fun u ⟨h12, hsi, hbx, hm, hk⟩ => ?_)
  have hs := hc.scrT.congr hk.2.2
  refine WP.mono (copyWords_ok hsi hbx h12 (by omega_using [hw]) (by omega_using [hw']) (by omega_using [hT, hz])
    (fun i hi => hs.ld (by omega_using [hE, hi])) (fun i hi => hs.st (by omega_using [hT, hi]))
    (fun i hi b hb => by rw [ofs_off P (by omega_using [hE, hz, hi, hb])]; omega_using [hT, hE0])) fun t ⟨hval, _, hf, hkt⟩ => ?_
  rw [hm] at hf hval
  have k := (hk.trans hkt).mono (show ∀ r ∈ [.r12, .rax, .rdx, .rsi, .rbx] ++ [.rax, .r14], r ∈ mmRegs by decide)
  exact ⟨hc.of_win (Frm.of_outside (hf.mono (o' := slot wx Crt.aT) (n' := 8 * (wx + 2)) (by omega_using []) (by omega_using [])) (by simp [crtWinRanges])) k.2.2 (k.gpr (by decide)), hval, hf, k⟩

end VG.Proof.Dsa.X86_64.PublicPower

end

end

/-! # Correctness of public windows and zero-digit skipping -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.PublicPower
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.PublicPower

/-- Reading the public digit establishes the branch condition. -/
theorem test_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc v : Nat}
    (hc : CExpCtx s P wx minv X Xc) (hv : v < 16)
    (hn : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sNib)), .alu .test .rax (.reg .rax)]) s fun t =>
      t.mem = s.mem ∧ t.zf = some (decide (v = 0)) ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem ∧ t.zf = some (decide (v = 0))) ?_ rfl)
    fun t ⟨⟨hm, hz⟩, hk⟩ => ⟨hm, hz, hk⟩
  xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sNib) (by decide), hn,
    BitVec.and_self, ofNat64_beq_zero (show v < 2 ^ 64 by omega_using [hv])]

/-- A zero digit leaves the accumulator unchanged; other digits multiply
by their table entry. This identity holds for every odd modulus. -/
theorem applyWindow_ok (M : Mont) (Sq : MontS) {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64}
    {X Xc : Nat} {Q : Prop} {x E v : Nat}
    (hc : CExpCtx s P wx minv X Xc) (htab : CTab s.mem P wx X Q x)
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hv : v < 16)
    (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hY : wv s.mem P (slot wx aY) wx < Sq.bd X (2 ^ (64 * wx)))
    (hYv : Q → wv s.mem P (slot wx aY) wx % X = x ^ E * 2 ^ (64 * wx) % X)
    (hn : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (applyWindow M.mm) s fun t => CExpCtx t P wx minv X Xc ∧
      wv t.mem P (slot wx aY) wx < Sq.bd X (2 ^ (64 * wx)) ∧
      (Q → wv t.mem P (slot wx aY) wx % X = x ^ (E + v) * 2 ^ (64 * wx) % X) ∧
      (∀ k < 32, word t.mem P (8 * k) = word s.mem P (8 * k)) ∧
      Frm P (crtWinRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold applyWindow
  refine WP.seq (WP.mono (test_ok hc hv hn) fun u ⟨hm, hz, hk⟩ => ?_)
  have hf : Frm P (crtWinRanges wx) s.mem u.mem := hm ▸ Frm.refl _ _ _
  have hu := hc.of_win hf hk.2.2 (hk.gpr (by decide))
  by_cases hzero : v = 0
  · subst v
    refine WP.ite true (by simp only [eval, hz, decide_true]) (fun _ => WP.block_nil ?_) (by simp)
    exact ⟨hu, hm ▸ hY, by simpa only [hm, Nat.add_zero] using hYv,
      fun _ _ => by rw [hm], hf, hk.mono (by decide)⟩
  · refine WP.ite false (by simp only [eval, hz, hzero, decide_false]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (select_ok hu hw hw' hv (hm ▸ htab.tab) (hm ▸ hn))
      fun t ⟨ht, htval, hout, hkt⟩ => ?_)
    have hgt := slot_le (w := wx) (show Crt.aT < 8 by decide)
    have htsep := slot_sep (w := wx) (show aY ≠ Crt.aT by decide)
    have hsz := hc.scrT.nowrap
    have hyEq : wv t.mem P (slot wx aY) wx = wv u.mem P (slot wx aY) wx := hout.wv (by omega_using [htsep]) (by have := slot_le (w := wx) (show aY < 8 by decide); omega_using [hsz, this])
    have htframe : Frm P (crtWinRanges wx) u.mem t.mem :=
      Frm.of_outside (hout.mono (o' := slot wx Crt.aT) (n' := 8 * (wx + 2)) (by omega_using []) (by omega_using []))
        (by simp [crtWinRanges])
    refine WP.mono (crtMulT_ok M (Q := Q) (x := x) (E := E) (v := v) ht hw hw' hR
      (by rw [htval, hm]; exact htab.lt _ hv)
      (fun hq => by rw [hyEq, hm]; exact hYv hq)
      (fun hq => by rw [htval, hm]; exact htab.val hq _ hv))
      fun z ⟨hzctx, hzlt, hzval, hzhdr, hzf, hzk⟩ => ?_
    have hXR : X ≤ 2 ^ (64 * wx) := by rw [← hc.n]; exact Nat.le_of_lt (wv_lt _ _ _ _)
    exact ⟨hzctx, Nat.lt_of_lt_of_le hzlt (Sq.le hXR), hzval, fun k hki => by
      rw [hzhdr k hki, hout.word (by have := hdr_lt_slot wx Crt.aT hki; omega_using [this])
        (by have := hdr_lt_slot wx 8 hki; omega_using [hki]), hm],
      (hf.trans htframe).trans hzf, ((hk.trans hkt).trans hzk).mono (by decide)⟩

theorem crtWin_ok (M : Mont) (Sq : MontS) {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat} {Q : Prop}
    {x E V b : Nat} (hc : CExpCtx t P wx minv X Xc) (htab : CTab t.mem P wx X Q x) (hw : 2 ≤ wx)
    (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) X)
    (hY : wv t.mem P (slot wx aY) wx < Sq.bd X (2 ^ (64 * wx)))
    (hYv : Q → wv t.mem P (slot wx aY) wx % X = x ^ E * 2 ^ (64 * wx) % X)
    (hV : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 56)
    (hb : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) (hb1 : 1 ≤ b) (hb' : b < 2 ^ 31) :
    WP isa (seqs (window Sq.mm M.mm)) t fun t' => CExpCtx t' P wx minv X Xc ∧ CTab t'.mem P wx X Q x ∧
      wv t'.mem P (slot wx aY) wx < Sq.bd X (2 ^ (64 * wx)) ∧
      (Q → wv t'.mem P (slot wx aY) wx % X = x ^ (16 * E + V / 16 % 16) * 2 ^ (64 * wx) % X) ∧
      word t'.mem P (8 * Crt.sV) = BitVec.ofNat 64 (16 * V) ∧
      word t'.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (b - 1) ∧
      t'.zf = some (decide (b - 1 = 0)) ∧ Frm P (crtWinRanges wx) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hc.scrT.nowrap
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  unfold window
  simp only [seqs]
  refine WP.seq (WP.mono (squares_ok Sq hc hw hw' hR hY hYv)
    fun t₄ ⟨hc₄, hY₄, hYv₄, hh04, f04, k04⟩ => ?_)
  -- The window, and `sV` up.
  refine WP.seq (WP.mono (winMid_ok (V := V) hc₄ (by rw [hh04 _ (by decide) (by decide)]; exact hV) (by omega_arith)) fun t₅ ⟨hm₅, k₅⟩ => ?_)
  have o1 := writeW_outside t₄.mem P (d := 8 * Crt.sV) (BitVec.ofNat 64 (16 * V)) (by decide)
  have o2 := writeW_outside (t₄.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (16 * V))) P (d := 8 * Crt.sNib)
    (BitVec.ofNat 64 (V / 16 % 16)) (by decide)
  rw [← hm₅] at o2
  have f₅ : Frm P (crtWinRanges wx) t₄.mem t₅.mem :=
    (Frm.of_outside o1 (by simp [crtWinRanges])).trans (Frm.of_outside o2 (by simp [crtWinRanges]))
  have hc₅ := hc₄.of_win f₅ k₅.2.2 (k₅.gpr (by decide))
  have htab₅ : CTab t₅.mem P wx X Q x := htab.of_win (f04.trans f₅) hn
  have hY₅ : wv t₅.mem P (slot wx aY) wx = wv t₄.mem P (slot wx aY) wx := by
    rw [o2.wv (by have := hdr_lt_slot wx aY (show Crt.sNib < 32 by decide); omega_arith) (by omega_arith),
      o1.wv (by have := hdr_lt_slot wx aY (show Crt.sV < 32 by decide); omega_arith) (by omega_arith)]
  have hh₅ : ∀ k < 32, k ≠ Crt.sV → k ≠ Crt.sNib → word t₅.mem P (8 * k) = word t.mem P (8 * k) :=
    fun k hk h1 h2 => by
      rw [hm₅, hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h2), hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h1),
        hh04 k hk h2]
  have hv16 : V / 16 % 16 < 16 := Nat.mod_lt _ (by decide)
  refine WP.seq (WP.mono (applyWindow_ok M Sq (E := 16 * E) hc₅ htab₅ hw hw' hv16 hR
    (hY₅ ▸ hY₄)
    (fun hq => by rw [hY₅, hYv₄ hq])
    (by rw [hm₅, word_writeW_self])) fun t₇ ⟨hc₇, hY₇, hYv₇, hh₇, f₇, k₇⟩ => ?_)
  -- The count.
  refine WP.mono (crtBitEnd_ok hc₇ (by
    rw [hh₇ _ (by decide), hh₅ _ (by decide) (by decide) (by decide)]
    exact hb) hb1 hb') fun t' ⟨hm', hz', k'⟩ => ?_
  have o₈ := writeW_outside t₇.mem P (d := 8 * Crt.sBit) (BitVec.ofNat 64 (b - 1)) (by decide)
  rw [← hm'] at o₈
  have f₈ : Frm P (crtWinRanges wx) t₇.mem t'.mem := Frm.of_outside o₈ (by simp [crtWinRanges])
  have fall : Frm P (crtWinRanges wx) t.mem t'.mem := (f04.trans f₅ |>.trans f₇).trans f₈
  refine ⟨hc₇.of_win f₈ k'.2.2 (k'.gpr (by decide)), htab.of_win fall hn, ?_, ?_, ?_, ?_, hz', fall,
    (((k04.trans k₅).trans k₇).trans k').mono (by decide)⟩
  · rw [o₈.wv (by have := hdr_lt_slot wx aY (show Crt.sBit < 32 by decide); omega_arith) (by omega_arith)]; exact hY₇
  · intro hq
    rw [o₈.wv (by have := hdr_lt_slot wx aY (show Crt.sBit < 32 by decide); omega_arith) (by omega_arith)]
    exact hYv₇ hq
  · rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₇ _ (by decide),
      hm₅, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      word_writeW_self]
  · rw [hm', word_writeW_self]


end VG.Proof.Dsa.X86_64.PublicPower

end

end

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

end

end

/-! # Public exponentiation through Montgomery encoding and decoding -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.PublicPower
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.PublicPower

/-- DSA modular exponentiation in Montgomery representation. The exponent
is a nonempty byte string outside the scratch workspace; leading zeroes
are permitted. This lemma makes no primality or group-order assumption. -/
theorem expLoop_ok (M : Mont) (Sq : MontS) {s : State} {B : Addr} {Z o w wx : Nat}
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
    WP isa (VG.Impl.Dsa.X86_64.PublicPower.expLoop Sq.mm M.mm sp sl) s fun t =>
      SubCtx t B Z o w wx minv ∧ wv t.mem (off B o) (slot wx aY) wx < Sq.bd m (2 ^ (64 * wx)) ∧
      wv t.mem (off B o) (slot wx aY) wx % m =
        Spec.Dsa.powMod x (Spec.Dsa.decodeBE eb) m * 2 ^ (64 * wx) % m ∧
      Frm (off B o) (crtExpRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (crtExpLoop_ok M Sq (Q := True) hc hw2 hwx hw30 hn hinv hodd hxl
    (fun _ => hxc) hyl (fun _ => hyc) hsp hsl hep hel hL1 hL2 he) fun t ht => ?_
  obtain ⟨hctx, hlt, hval, hframe, hkeep⟩ := ht
  refine ⟨hctx, hlt, ?_, hframe, hkeep⟩
  rw [VG.Proof.Dsa.powMod_eq, VG.Proof.Dsa.decodeBE_os2ip, Nat.mod_mul_mod]
  exact hval True.intro

/-- The ordinary result of exponentiation, for an odd (possibly composite)
modulus. The exponent may be caller bytes or bytes in the scratch suffix. -/
theorem encodedPower_ok (M : Mont) (Sq : MontS) {s : State} {B : Addr} {Z o w wx m x : Nat}
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
    WP isa (VG.Impl.Dsa.X86_64.PublicPower.encodedPower Sq.mm M.mm sp sl) s fun t =>
      SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx = Spec.Dsa.powMod x (Spec.Dsa.decodeBE eb) m ∧
      ModCtx t (off B o) (slot wx 8) wx minv m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hmctx : ModCtx s (off B o) (slot wx 8) wx minv m := ⟨hc.good, hn, hinv⟩
  have hnZ := hc.good.scr.nowrap
  have hR := coprime_pow2 hodd (64 * wx)
  unfold VG.Impl.Dsa.X86_64.PublicPower.encodedPower
  refine WP.seq (WP.mono (expLoop_ok M Sq hc hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc
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
theorem powerCore_ok (M : Mont) (Sq : MontS) {s : State} {B : Addr} {Z o w wx m x : Nat}
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
    WP isa (VG.Impl.Dsa.X86_64.PublicPower.powerCore Sq.mm M.mm sp sl) s fun t =>
      SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx = Spec.Dsa.powMod x (Spec.Dsa.decodeBE eb) m ∧
      ModCtx t (off B o) (slot wx 8) wx minv m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hR2' : wv s.mem (off B o) (slot wx aR2) wx =
      (2 ^ (64 * wx) * 2 ^ (64 * wx)) % m := by
    rw [hR2, ← Nat.pow_add, show 64 * wx + 64 * wx = 128 * wx by omega_using []]
  unfold VG.Impl.Dsa.X86_64.PublicPower.powerCore
  refine WP.seq (WP.mono (encodePower_ok M ⟨hc.good, hn, hinv⟩ (Nat.le_refl _) hw2 (by omega_using [hwx, hw30])
    hm hodd hx hR2' hone) fun u ⟨hu, hux, huy, huone, hf, hk⟩ => ?_)
  have hcu := arrays_context hc hf (by decide) hk
  have hfu := arrays_work hf (by decide)
  have hsrc := work_source hc hfu hk he
  refine WP.mono (encodedPower_ok M Sq hcu hw2 hwx hw30 hm hodd hu.modulus hu.inverse huone
    (by rw [hux]; exact Nat.mod_lt _ (by omega_using [hm]))
    (by rw [hux, Nat.mod_mod])
    (by rw [huy]; exact Nat.mod_lt _ (by omega_using [hm]))
    (by rw [huy, Nat.mod_mod]) hsp hsl
    ((work_parent hc hfu hsp).trans hep) ((work_parent hc hfu hsl).trans hel) hL1 hL2 hsrc)
    fun t ⟨hct, hresult, hmt, hft, hkt⟩ =>
      ⟨hct, hresult, hmt, hfu.trans hft, (hk.trans hkt).mono (by decide)⟩

/-- Complete exponentiation, including constants setup and loading the base.
Both byte buffers remain valid when they occupy the inactive scratch suffix. -/
theorem power_ok (M : Mont) (Sq : MontS) {s : State} {B : Addr} {Z o w wx m : Nat}
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
    WP isa (VG.Impl.Dsa.X86_64.PublicPower.power Sq.mm M.mm bp bl sp sl) s fun t =>
      SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx =
        Spec.Dsa.powMod (Spec.Dsa.decodeBE bb) (Spec.Dsa.decodeBE eb) m ∧
      ModCtx t (off B o) (slot wx 8) wx minv m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold VG.Impl.Dsa.X86_64.PublicPower.power
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
  refine WP.mono (powerCore_ok M Sq hcv hw2 hwx hw30 hm hodd vn vi vone hvbase vr2
    hsp hsl ((work_parent hc hf hsp).trans he) ((work_parent hc hf hsl).trans helen)
    he1 he2 (work_source hc hf hk hes)) fun t ⟨hct, hresult, hmt, hft, hkt⟩ =>
      ⟨hct, hresult, hmt, hf.trans hft, (hk.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64.PublicPower
