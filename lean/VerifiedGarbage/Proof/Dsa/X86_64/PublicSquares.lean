module

public import VerifiedGarbage.Impl.Dsa.X86_64.PublicPower
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.Framework.Omega

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
  · exact ho.wv (by have := hdr_lt_slot wx aY (show Crt.sNib < 32 by decide); omega)
      (by have := hc.scrT.nowrap; have := slot_le (w := wx) (show aY < 8 by decide); omega)
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
    ofNat64_pred hn1 (by omega), ofNat64_beq_zero (show n - 1 < 2 ^ 64 by omega)]

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
      rw [show 4 - (n - 1) = 4 - n + 1 by omega, Nat.pow_succ]
      ac_rfl
    rw [valuez, vv hq, he]
  by_cases hn : n = 1
  · subst n
    exact Or.inl ⟨by simp [eval, hz],
      hcz, valuez ▸ vl, by simpa using val, headers, frame, keep⟩
  · exact Or.inr ⟨by simp [eval, hz, show n - 1 ≠ 0 by omega],
      n - 1, by omega, by omega, by omega, hcz, valuez ▸ vl, val,
      countz, headers, frame, keep⟩

end VG.Proof.Dsa.X86_64.PublicPower
