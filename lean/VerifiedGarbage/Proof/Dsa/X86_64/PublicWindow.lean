module

public import VerifiedGarbage.Impl.Dsa.X86_64.PublicPower
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
public import VerifiedGarbage.Proof.Bignum.CrtExp
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Framework.Omega

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
