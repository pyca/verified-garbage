module

import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
public import VerifiedGarbage.Proof.Rsa.X86_64.WordSetup
public import VerifiedGarbage.Proof.Rsa.X86_64.WordFrame
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.WordStep
import VerifiedGarbage.Proof.Bignum.WordStepNorm
import VerifiedGarbage.Proof.Bignum.LongDivision
meta import VerifiedGarbage.Proof.Bignum.Layout
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.WordStep
meta import VerifiedGarbage.Proof.Bignum.WordStepNorm
meta import VerifiedGarbage.Proof.Bignum.LongDivision
public import VerifiedGarbage.Impl.Rsa.X86_64.WordReduce
public import VerifiedGarbage.Proof.Bignum.X86_64.R2wSub
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Impl.Rsa.X86_64.WordReduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! ### `Rsa.X86_64.WordLoop`, which this module and modules that import it used -/

section

/-! ### `Rsa.X86_64.WordStep`, which this module and modules that import it used -/

section

/-! ### `Rsa.X86_64.WordSub`, which only this module used -/

section

/-! # The multiply-subtract with a low input word

The existing multiword subtraction invariant carries the low input digit
unchanged through its limb steps.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordReduce

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.R2Words
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Bignum.X86_64.R2w

theorem subHead_ok (s : State) {aM aT aD : Addr}
    (eM : s.gpr .r10 + BitVec.ofInt 64 0 = aM) (eT : s.gpr .r8 + BitVec.ofInt 64 0 = aT)
    (eD : s.gpr .rbp + BitVec.ofInt 64 8 = aD)
    (hMr : InRegions (s.rd ++ s.wr) aM 8) (hT : InRegions s.wr aT 8)
    (hD : InRegions (s.rd ++ s.wr) aD 8) :
    WP isa (.block Impl.Rsa.X86_64.WordReduce.subHead) s fun t =>
      ∃ (v : BitVec 64) (b : Bool), t.mem = s.mem.writeW aT v ∧ t.gpr .rbp = mask b ∧
        v.toNat + (s.gpr .rcx).toNat * (s.mem.readW aM 64).toNat =
          (s.mem.readW aD 64).toNat + 2 ^ 64 * ((t.gpr .r9).toNat + b.toNat) ∧
      Keep [.rax, .rdx, .rbp, .r9] s t := by
  refine WP.mono (WP.keep [.rax, .rdx, .rbp, .r9] (Q := fun t =>
    ∃ (v : BitVec 64) (b : Bool), t.mem = s.mem.writeW aT v ∧ t.gpr .rbp = mask b ∧
      v.toNat + (s.gpr .rcx).toNat * (s.mem.readW aM 64).toNat =
        (s.mem.readW aD 64).toNat + 2 ^ 64 * ((t.gpr .r9).toNat + b.toNat)) ?_ rfl)
    fun t ⟨h, k⟩ => let ⟨v, b, h1, h2, h3⟩ := h; ⟨v, b, h1, h2, h3, k⟩
  unfold Impl.Rsa.X86_64.WordReduce.subHead cfToRbp
  xrun [State.ea, at0, eM, eT, eD, hMr, hT, hD]
  refine ⟨_, _, rfl, rfl, ?_⟩
  have hm := mul_toNat (s.mem.readW aM 64) (s.gpr .rcx)
  have hs := sbb_toNat (s.mem.readW aD 64)
    (BitVec.ofNat 64 ((s.mem.readW aM 64).toNat * (s.gpr .rcx).toNat)) false
  simp only [Bool.toNat_false, Nat.add_zero,
    show (BitVec.ofBool false).setWidth 64 = (0#64 : BitVec 64) from rfl, BitVec.sub_zero] at hs
  rw [Nat.mul_comm (s.gpr .rcx).toNat]
  omega_arith

theorem mulSub_ok {s : State} {B : Addr} {Z w ex em et ev : Nat} (hs : Scr s B Z)
    (hbx : s.gpr .rbx = off B ex) (h10 : s.gpr .r10 = off B em) (h8 : s.gpr .r8 = off B et)
    (hbp : s.gpr .rbp = off B ev) (hV : ev + 16 ≤ Z)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hX : ex + 8 * w ≤ Z)
    (hM : em + 8 * w ≤ Z) (hT : et + 8 * (w + 1) ≤ Z)
    (sX : et + 8 * (w + 1) ≤ ex ∨ ex + 8 * w ≤ et) (sM : et + 8 * (w + 1) ≤ em ∨ em + 8 * w ≤ et) :
    WP isa Impl.Rsa.X86_64.WordReduce.mulSub s fun t => ∃ b : Bool,
      wv t.mem B et (w + 1) + (s.gpr .rcx).toNat * wv s.mem B em w =
        wv s.mem B ex w * 2 ^ 64 + (word s.mem B (ev + 8)).toNat + 2 ^ (64 * (w + 1)) * b.toNat ∧
      Outside B et (8 * (w + 1)) s.mem t.mem ∧ Keep [.rax, .rdx, .rbp, .r9, .r14] s t := by
  have hn := hs.nowrap
  unfold Impl.Rsa.X86_64.WordReduce.mulSub
  refine WP.seq (WP.mono (subHead_ok s (by rw [h10]; simp [off]) (by rw [h8]; simp [off])
    (by rw [hbp]; simp [off, BitVec.add_assoc, BitVec.ofNat_add])
    (hs.ld (d := em) (by omega_arith)) (hs.st (d := et) (by omega_arith)) (hs.ld hV)) fun t₁ ⟨v, b, hm₁, hbp₁, hv₁, k₁⟩ => ?_)
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 1 → t.mem = t₁.mem → Keep [.r14] t₁ t → t.cf = t₁.cf →
      MsInv s B Z ex em et (s.gpr .rcx).toNat 1 t (word s.mem B (ev + 8)).toNat := fun t h14 hm k _ => by
    refine ⟨hs.congr (k.2.2.trans k₁.2.2), (k₁.trans k).mono (by decide), h14, ?_, ⟨b, ?_, ?_⟩⟩
    · rw [hm, hm₁]
      intro x hx
      rw [writeW_outside s.mem B v (by omega_arith) x (by omega_arith)]
    · rw [k.gpr (by decide), hbp₁]
    · rw [hm, hm₁, k.gpr (by decide)]
      simp only [wv, Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.add_zero, Nat.pow_zero,
        word_writeW_self, Nat.one_mul, Nat.sub_self, Nat.zero_mul]
      exact hv₁
  refine WP.seq (WP.mono (wordLoop_ok (start := 1) (N := w) (by omega_arith) hw' (fun j t => MsInv s B Z ex em et (s.gpr .rcx).toNat j t (word s.mem B (ev + 8)).toNat)
    h0 (fun j hj1 hj t hI => msStep_ok hbx h10 h8 h12 hw' hX hM hT sX sM hj1 hj hI)) fun t₂ hI => ?_)
  obtain ⟨c, hbp₂, hval⟩ := hI.val
  have t₂bx : t₂.gpr .rbx = off B ex := (hI.keep.gpr (by decide)).trans hbx
  have t₂8 : t₂.gpr .r8 = off B et := (hI.keep.gpr (by decide)).trans h8
  have t₂12 : t₂.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  refine WP.mono (subTop_ok t₂ (addrm8 t₂bx t₂12 (by omega_arith)) (addr0 t₂8 t₂12) (hI.scr.ld (by omega_arith))
    (hI.scr.st (by omega_arith)) hbp₂) fun t ⟨v', c', hm, hv, k⟩ => ⟨c', ?_, ?_, (hI.keep.trans k).mono (by decide)⟩
  · have hx : t₂.mem.readW (off B (ex + 8 * (w - 1))) 64 = word s.mem B (ex + 8 * (w - 1)) :=
      hI.out.word (by omega_arith) (by omega_arith)
    rw [hx] at hv
    rw [hm, show w + 1 = w + 1 from rfl, wv_writeW_top _ _ _ _ _ (by omega_arith)]
    have ew : wv s.mem B ex w = wv s.mem B ex (w - 1) + 2 ^ (64 * (w - 1)) * (word s.mem B (ex + 8 * (w - 1))).toNat := by
      conv => lhs; rw [show w = (w - 1) + 1 by omega_arith]
      simp only [wv]
    have e1 : 2 ^ (64 * w) = 2 ^ (64 * (w - 1)) * 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega_arith
    have e2 : 2 ^ (64 * (w + 1)) = 2 ^ (64 * (w - 1)) * 2 ^ 64 * 2 ^ 64 := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega_arith
    rw [ew, e2]
    rw [e1] at hval ⊢
    grind
  · rw [hm]
    intro x hx
    rw [writeW_outside t₂.mem B v' (by omega_arith) x (by omega_arith)]
    exact hI.out x (by omega_arith)

end VG.Proof.Rsa.X86_64.WordReduce

end

end

/-! # A normalized remainder step with a full low input word

The 3-by-2 quotient estimate, multiword multiply-subtract and one masked
correction compute `(remainder * 2^64 + digit) mod modulus` at the factors' width, while
the surrounding workspace may have a different stride.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordReduce

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.R2Words
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Bignum.X86_64.R2w
open VG.Proof.Bignum.WordStep

/-- `WordStep.wordStepQ1_val` for the dividend `y`: `t₁ = y - q̂ m` modulo `W > 4 m`
and `m` added once if its top half is set is `y mod m`, for `⌊y / m⌋ ≤ q̂ ≤ ⌊y / m⌋ + 1`. -/
theorem stepQ1_val {W y M qh T1 T2 b c : Nat} (hM0 : 0 < M) (hMW : 2 * M < W / 2)
    (hge : y / M ≤ qh) (hle : qh ≤ y / M + 1)
    (hT1 : T1 < W) (hb : b < 2) (h1 : T1 + qh * M = y + W * b)
    (hT2 : T2 < W) (hc : c < 2) (h2 : T2 + W * c = T1 + if W / 2 ≤ T1 then M else 0) :
    T2 = y % M := by
  obtain ⟨hfin, hv1, hv2⟩ := addBack_one (W := W) hM0 hMW hge hle
  obtain e1 := twos_of_sub hT1 hb (by omega_using [h1]) hv1 hv2
  obtain hw1 : -((W : Int) / 2) ≤ addIfNeg M ((y : Nat) - (qh * M : Nat)) := by
    rw [hfin]; omega_using []
  obtain hw2 : addIfNeg M ((y : Nat) - (qh * M : Nat)) < (W : Int) / 2 := by
    rw [hfin]; have := Nat.mod_lt y hM0; omega_using [hMW, this]
  obtain e2 := twos_of_add hv1 hv2 hw1 hw2 e1 hT2 hc h2
  rw [e2, hfin]
  obtain hr := Nat.mod_lt y hM0
  obtain hMW' : M < W := Nat.lt_of_lt_of_le (by omega_using [hMW]) (Nat.div_le_self W 2)
  unfold twos
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr (Nat.lt_trans hr hMW')), Int.toNat_natCast]

/-- `step_ok`, with the quotient's digit `⌊(x 2^64 + digit) / m⌋` left as
`rcx + r11`: the estimate `q̂` and the mask of its correction. -/
theorem stepQ_ok {t : State} {B : Addr} {Z w ex em et ev : Nat} (hs : Scr t B Z)
    (hbx : t.gpr .rbx = off B ex) (h10 : t.gpr .r10 = off B em) (h8 : t.gpr .r8 = off B et)
    (h12 : t.gpr .r12 = BitVec.ofNat 64 w) (hbp : t.gpr .rbp = off B ev)
    (hw : 3 ≤ w) (hw' : w < 2 ^ 30)
    (hXz : ex + 8 * w ≤ Z) (hMz : em + 8 * w ≤ Z) (hTz : et + 8 * (w + 1) ≤ Z) (hE : ev + 16 ≤ Z)
    (sepX : et + 8 * (w + 1) ≤ ex ∨ ex + 8 * w ≤ et)
    (sepM : et + 8 * (w + 1) ≤ em ∨ em + 8 * w ≤ et)
    (hd : 2 ^ 63 ≤ (word t.mem B (em + 8 * (w - 1))).toNat)
    (hv : (word t.mem B ev).toNat =
      (2 ^ 128 - 1) / (word t.mem B (em + 8 * (w - 1))).toNat - 2 ^ 64)
    (hx : wv t.mem B ex w < wv t.mem B em w) :
    WP isa Impl.Rsa.X86_64.WordReduce.step t fun t' =>
      wv t'.mem B ex w = (wv t.mem B ex w * 2 ^ 64 + (word t.mem B (ev + 8)).toNat) % wv t.mem B em w ∧
      Frm B [(et, 8 * (w + 1)), (ex, 8 * w)] t.mem t'.mem ∧ Keep mmRegs t t' ∧
      (t'.gpr .rcx + t'.gpr .r11).toNat =
        (wv t.mem B ex w * 2 ^ 64 + (word t.mem B (ev + 8)).toNat) / wv t.mem B em w := by
  have hn := hs.nowrap
  unfold Impl.Rsa.X86_64.WordReduce.step
  change WP isa (.seq (.block quot) (.seq (.block refine3) (.seq Impl.Rsa.X86_64.WordReduce.mulSub
    (.seq addBack copyBack)))) t _
  generalize hX : wv t.mem B ex w = X at hx
  generalize hM : wv t.mem B em w = M at hx
  obtain hu := top_le (by omega_arith) (hX ▸ hM ▸ hx)
  have e1 : ex + 8 * w ≤ Z := hXz
  have e2 : em + 8 * w ≤ Z := hMz
  obtain e3 : ev + 8 ≤ Z := by omega_arith
  have eT : et + 8 * (w + 1) ≤ Z := hTz
  have sX : et + 8 * (w + 1) ≤ ex ∨ ex + 8 * w ≤ et := sepX
  have sM : et + 8 * (w + 1) ≤ em ∨ em + 8 * w ≤ et := sepM
  obtain hw31 : w < 2 ^ 31 := by omega_arith
  obtain hq := quot_ok hs hbx h10 h12 hbp (by omega_arith) e1 e2 e3 hu hd hv
  refine WP.seq (WP.mono hq fun t₂ ⟨h2cx, hm₂, k₂⟩ => ?_)
  obtain hs₂ := hs.congr k₂.2.2
  obtain t₂bx : t₂.gpr .rbx = off B ex := (k₂.gpr (by decide)).trans hbx
  obtain t₂10 : t₂.gpr .r10 = off B em := (k₂.gpr (by decide)).trans h10
  obtain t₂8 : t₂.gpr .r8 = off B et := (k₂.gpr (by decide)).trans h8
  obtain t₂12 : t₂.gpr .r12 = BitVec.ofNat 64 w := (k₂.gpr (by decide)).trans h12
  obtain t₂bp : t₂.gpr .rbp = off B ev := (k₂.gpr (by decide)).trans hbp
  -- The estimates.
  obtain hX' : X = (word t.mem B (ex + 8 * (w - 1))).toNat * 2 ^ (64 * (w - 1)) +
      (word t.mem B (ex + 8 * (w - 2))).toNat * 2 ^ (64 * (w - 2)) +
      (word t.mem B (ex + 8 * (w - 3))).toNat * 2 ^ (64 * (w - 3)) + wv t.mem B ex (w - 3) := by
    rw [← hX, show w = (w - 3) + 1 + 1 + 1 by omega_arith, wv_succ, wv_succ, wv_succ,
      show w - 3 + 1 + 1 + 1 - 1 = w - 3 + 1 + 1 by omega_arith, show w - 3 + 1 + 1 + 1 - 2 = w - 3 + 1 by omega_arith,
      show w - 3 + 1 + 1 + 1 - 3 = w - 3 by omega_arith]
    grind
  obtain hM' : M = (word t.mem B (em + 8 * (w - 1))).toNat * 2 ^ (64 * (w - 1)) +
      (word t.mem B (em + 8 * (w - 2))).toNat * 2 ^ (64 * (w - 2)) + wv t.mem B em (w - 2) := by
    rw [← hM, show w = (w - 2) + 1 + 1 by omega_arith, wv_succ, wv_succ, show w - 2 + 1 + 1 - 1 = w - 2 + 1 by omega_arith,
      show w - 2 + 1 + 1 - 2 = w - 2 by omega_arith]
    grind
  obtain ⟨hUD, hq1, hq2, -, -⟩ := norm3 hw hX' (wv_lt _ _ _ _) hM' (wv_lt _ _ _ _) (BitVec.isLt _) (BitVec.isLt _) hd hx
  obtain h2cx' := congrArg BitVec.toNat h2cx
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide))] at h2cx'
  obtain hD0 : 0 < (word t.mem B (em + 8 * (w - 1))).toNat * 2 ^ 64 + (word t.mem B (em + 8 * (w - 2))).toNat := by
    omega_arith
  obtain hr := refine3_ok hs₂ t₂bx t₂10 t₂12 hw e1 e2 (by rw [hm₂]) (by rw [hm₂]) hD0 hUD
    (by rw [h2cx']; exact hq1) (by rw [h2cx']; exact hq2)
  refine WP.seq (WP.mono hr fun t₂' ⟨h2'cx, hm₂', k₂'⟩ => ?_)
  obtain hs₂' := hs₂.congr k₂'.2.2
  obtain t₂'bx : t₂'.gpr .rbx = off B ex := (k₂'.gpr (by decide)).trans t₂bx
  obtain t₂'10 : t₂'.gpr .r10 = off B em := (k₂'.gpr (by decide)).trans t₂10
  obtain t₂'8 : t₂'.gpr .r8 = off B et := (k₂'.gpr (by decide)).trans t₂8
  obtain t₂'12 : t₂'.gpr .r12 = BitVec.ofNat 64 w := (k₂'.gpr (by decide)).trans t₂12
  obtain t₂'bp : t₂'.gpr .rbp = off B ev := (k₂'.gpr (by decide)).trans t₂bp
  obtain hms := mulSub_ok hs₂' t₂'bx t₂'10 t₂'8 t₂'bp hE t₂'12 (by omega_arith) hw31 e1 e2 eT sX sM
  refine WP.seq (WP.mono hms fun t₃ ⟨b, hv₃, ho₃, k₃⟩ => ?_)
  rw [h2'cx] at hv₃
  obtain hs₃ := hs₂'.congr k₃.2.2
  obtain t₃10 : t₃.gpr .r10 = off B em := (k₃.gpr (by decide)).trans t₂'10
  obtain t₃8 : t₃.gpr .r8 = off B et := (k₃.gpr (by decide)).trans t₂'8
  obtain t₃12 : t₃.gpr .r12 = BitVec.ofNat 64 w := (k₃.gpr (by decide)).trans t₂'12
  obtain hab₃ := addBack_ok' hs₃ t₃10 t₃8 t₃12 (by omega_arith) hw31 e2 eT sM
  refine WP.seq (WP.mono hab₃ fun t₅ ⟨c1, hv₅, ho₅, k₅, h11₅⟩ => ?_)
  obtain hs₅ := hs₃.congr k₅.2.2
  obtain t₅bx : t₅.gpr .rbx = off B ex :=
    (k₅.gpr (by decide)).trans ((k₃.gpr (by decide)).trans t₂'bx)
  obtain t₅8 : t₅.gpr .r8 = off B et := (k₅.gpr (by decide)).trans t₃8
  obtain t₅12 : t₅.gpr .r12 = BitVec.ofNat 64 w := (k₅.gpr (by decide)).trans t₃12
  unfold R2Words.copyBack
  refine WP.seq (WP.mono (WP.keep [.rsi] (Q := fun t' => t'.gpr .rsi = off B et ∧ t'.mem = t₅.mem)
    (by xrun [t₅8]) rfl) fun t₆ ⟨⟨h6si, hm₆⟩, k₆⟩ => ?_)
  obtain hsepw : ∀ j < w, ∀ b < 8, ofs B (off B (et + 8 * j) + BitVec.ofNat 64 b) < ex ∨
      ex + 8 * w ≤ ofs B (off B (et + 8 * j) + BitVec.ofNat 64 b) := fun j hj b hb => by
    rw [ofs_off B (by omega_arith)]; omega_arith
  obtain hs₆ := hs₅.congr k₆.2.2
  obtain hrd : ∀ j < w, InRegions (t₆.rd ++ t₆.wr) (off B (et + 8 * j)) 8 := fun j hj => hs₆.ld (by omega_arith)
  obtain hwr : ∀ j < w, InRegions t₆.wr (off B (ex + 8 * j)) 8 := fun j hj => hs₆.st (by omega_arith)
  obtain hcw := copyWords_ok (S := B) (D := B) h6si ((k₆.gpr (by decide)).trans t₅bx)
    ((k₆.gpr (by decide)).trans t₅12) (by omega_arith) hw31 (by omega_arith) hrd hwr hsepw
  refine WP.mono hcw fun t' ⟨hc, _, ho', k'⟩ => ?_
  -- Memory: `m`, `x` and the digit as on entry until the copy.
  obtain hm₂₂ : t₂'.mem = t.mem := by rw [hm₂', hm₂]
  obtain em3 : ∀ {d n}, d + 8 * n ≤ et ∨ et + 8 * (w + 1) ≤ d → d + 8 * n ≤ Z →
      wv t₃.mem B d n = wv t.mem B d n := fun h h' => by
    rw [ho₃.wv (by omega_arith) (by omega_arith), hm₂₂]
  rw [em3 (n := w) (d := em) (by omega_arith) (by omega_arith), hM] at hv₅
  rw [hm₂₂, hX, hM] at hv₃
  simp only [← top_half] at hv₅
  -- The quotient's bounds, for the dividend `y = x 2^64 + digit`.
  generalize hg : (word t.mem B (ev + 8)).toNat = g at hv₃
  obtain hg' : g < 2 ^ 64 := hg ▸ BitVec.isLt _
  obtain hMw : M < 2 ^ (64 * w) := by rw [← hM]; exact wv_lt _ _ _ _
  obtain hy : (X * 2 ^ 64 + g) / M < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (by omega_arith)]
    have := Nat.mul_le_mul_right (2 ^ 64) (show X + 1 ≤ M by omega_arith)
    rw [Nat.add_mul, Nat.one_mul] at this
    rw [Nat.mul_comm (2 ^ 64)]; omega_arith
  obtain hK : (X * 2 ^ 64 + g) / 2 ^ (64 * (w - 2)) = X / 2 ^ (64 * (w - 3)) := by
    rw [show 64 * (w - 2) = 64 + 64 * (w - 3) by omega_arith, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      div_pow_cancel hg']
  obtain e128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := Nat.pow_add 2 64 64
  obtain hXK : X / 2 ^ (64 * (w - 3)) = (word t.mem B (ex + 8 * (w - 1))).toNat * 2 ^ 128 +
      (word t.mem B (ex + 8 * (w - 2))).toNat * 2 ^ 64 + (word t.mem B (ex + 8 * (w - 3))).toNat := by
    obtain e : X = ((word t.mem B (ex + 8 * (w - 1))).toNat * 2 ^ 128 +
        (word t.mem B (ex + 8 * (w - 2))).toNat * 2 ^ 64 + (word t.mem B (ex + 8 * (w - 3))).toNat) *
          2 ^ (64 * (w - 3)) + wv t.mem B ex (w - 3) := by
      rw [hX', show 64 * (w - 1) = 64 * (w - 3) + 64 + 64 by omega_arith,
        show 64 * (w - 2) = 64 * (w - 3) + 64 by omega_arith, Nat.pow_add, Nat.pow_add, e128]
      generalize 2 ^ (64 * (w - 3)) = P; generalize 2 ^ 64 = Bq
      grind
    rw [e, div_pow_cancel (wv_lt _ _ _ _)]
  obtain hMK : M / 2 ^ (64 * (w - 2)) = (word t.mem B (em + 8 * (w - 1))).toNat * 2 ^ 64 +
      (word t.mem B (em + 8 * (w - 2))).toNat := by
    obtain e : M = ((word t.mem B (em + 8 * (w - 1))).toNat * 2 ^ 64 + (word t.mem B (em + 8 * (w - 2))).toNat) *
        2 ^ (64 * (w - 2)) + wv t.mem B em (w - 2) := by
      rw [hM', show 64 * (w - 1) = 64 * (w - 2) + 64 by omega_arith, Nat.pow_add]
      generalize 2 ^ (64 * (w - 2)) = P; generalize 2 ^ 64 = Bq
      grind
    rw [e, div_pow_cancel (wv_lt _ _ _ _)]
  obtain hD64 : 2 ^ 64 ≤ M / 2 ^ (64 * (w - 2)) := by rw [hMK]; omega_arith
  obtain ⟨hge, hle⟩ := qhat_trunc hy hD64
  rw [hK, hXK, hMK] at hge hle
  obtain hW : 2 * M < 2 ^ (64 * (w + 1)) / 2 := by
    rw [show 64 * (w + 1) = 64 * w + 64 by omega_arith, Nat.pow_add]
    omega_arith
  obtain hT3 := stepQ1_val (by omega_arith) hW hge hle (wv_lt _ _ _ _) (Bool.toNat_lt b) hv₃ (wv_lt _ _ _ _)
    (Bool.toNat_lt c1) hv₅
  obtain hlow : wv t₅.mem B et w = wv t₅.mem B et (w + 1) := by
    obtain hlt : wv t₅.mem B et (w + 1) < 2 ^ (64 * w) := by
      rw [hT3]; exact Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hMw
    rw [wv_succ] at hlt ⊢
    have : (word t₅.mem B (et + 8 * w)).toNat = 0 := by
      by_contra h
      have := Nat.mul_le_mul_left (2 ^ (64 * w)) (show 1 ≤ (word t₅.mem B (et + 8 * w)).toNat by omega_arith)
      omega_arith
    rw [this, Nat.mul_zero, Nat.add_zero]
  obtain f₃ : Frm B [(et, 8 * (w + 1)), (ex, 8 * w)] t₂'.mem t₃.mem :=
    Frm.of_outside ho₃ (by simp)
  obtain f₅ : Frm B [(et, 8 * (w + 1)), (ex, 8 * w)] t₃.mem t₅.mem :=
    Frm.of_outside ho₅ (by simp)
  obtain f' : Frm B [(et, 8 * (w + 1)), (ex, 8 * w)] t₆.mem t'.mem :=
    Frm.of_outside ho' (by simp)
  rw [hm₆] at f'
  obtain ff := (f₃.trans f₅).trans f'
  rw [hm₂₂] at ff
  refine ⟨?_, ff, ((((k₂.trans k₂').trans k₃).trans k₅).trans (k₆.trans k')).mono (by decide), ?_⟩
  · rw [hc, hm₆, hlow, hT3]
  -- The digit: `q̂`, less one where the step added `m` back.
  obtain tcx : t'.gpr .rcx = t₂'.gpr .rcx :=
    ((k₆.trans k').gpr (by decide)).trans ((k₅.gpr (by decide)).trans (k₃.gpr (by decide)))
  obtain t11 : t'.gpr .r11 = t₅.gpr .r11 := (k₆.trans k').gpr (by decide)
  rw [tcx, t11, h11₅, BitVec.toNat_add, h2'cx]
  obtain hd := Bignum.LongDivision.digit_eq (by omega_arith) hW hge hle (wv_lt _ _ _ _) (Bool.toNat_lt b) hv₃
  generalize hqh : min (((word t.mem B (ex + 8 * (w - 1))).toNat * 2 ^ 128 + (word t.mem B (ex + 8 * (w - 2))).toNat * 2 ^ 64 +
    (word t.mem B (ex + 8 * (w - 3))).toNat) / ((word t.mem B (em + 8 * (w - 1))).toNat * 2 ^ 64 +
      (word t.mem B (em + 8 * (w - 2))).toNat)) (2 ^ 64 - 1) = qh at hd hge hle hv₃ ⊢
  obtain hq : qh < 2 ^ 64 := by rw [← hqh]; exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)
  by_cases hN : 2 ^ 63 ≤ (word t₃.mem B (et + 8 * w)).toNat
  · simp only [(top_half t₃.mem B et w).mpr hN, ↓reduceIte] at hd
    simp only [hN, decide_true]
    obtain h1 : 1 ≤ qh := by
      rcases Nat.eq_zero_or_pos qh with h0 | h0
      · exfalso
        subst h0
        obtain hyM : (X * 2 ^ 64 + g) / M = 0 := by omega_arith
        have := (top_half t₃.mem B et w).mpr hN
        obtain hlt : X * 2 ^ 64 + g < M := (Nat.div_eq_zero_iff_lt (by omega_arith)).mp hyM
        have := wv_lt t₃.mem B et (w + 1)
        have : wv t₃.mem B et (w + 1) ≤ X * 2 ^ 64 + g := by
          rw [Nat.zero_mul, Nat.add_zero] at hv₃
          cases b <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hv₃ <;>
            omega_arith
        have : M < 2 ^ (64 * (w + 1)) / 2 := by omega_arith
        omega_arith
      · exact h0
    rw [show (mask true).toNat = 2 ^ 64 - 1 from rfl, show qh + (2 ^ 64 - 1) = (qh - 1) + 2 ^ 64 by omega_arith,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]
    exact hd
  · simp only [show ¬ (2 ^ (64 * (w + 1)) / 2 ≤ wv t₃.mem B et (w + 1)) from fun h => hN ((top_half _ _ _ _).mp h),
      ↓reduceIte] at hd
    simp only [hN, decide_false]
    rw [show (mask false).toNat = 0 from rfl, Nat.add_zero, Nat.mod_eq_of_lt hq]
    exact hd

/-- A normalized remainder step: `x := (x 2^64 + digit) mod m`. -/
theorem step_ok {t : State} {B : Addr} {Z w ex em et ev : Nat} (hs : Scr t B Z)
    (hbx : t.gpr .rbx = off B ex) (h10 : t.gpr .r10 = off B em) (h8 : t.gpr .r8 = off B et)
    (h12 : t.gpr .r12 = BitVec.ofNat 64 w) (hbp : t.gpr .rbp = off B ev)
    (hw : 3 ≤ w) (hw' : w < 2 ^ 30)
    (hXz : ex + 8 * w ≤ Z) (hMz : em + 8 * w ≤ Z) (hTz : et + 8 * (w + 1) ≤ Z) (hE : ev + 16 ≤ Z)
    (sepX : et + 8 * (w + 1) ≤ ex ∨ ex + 8 * w ≤ et)
    (sepM : et + 8 * (w + 1) ≤ em ∨ em + 8 * w ≤ et)
    (hd : 2 ^ 63 ≤ (word t.mem B (em + 8 * (w - 1))).toNat)
    (hv : (word t.mem B ev).toNat =
      (2 ^ 128 - 1) / (word t.mem B (em + 8 * (w - 1))).toNat - 2 ^ 64)
    (hx : wv t.mem B ex w < wv t.mem B em w) :
    WP isa Impl.Rsa.X86_64.WordReduce.step t fun t' =>
      wv t'.mem B ex w = (wv t.mem B ex w * 2 ^ 64 + (word t.mem B (ev + 8)).toNat) % wv t.mem B em w ∧
      Frm B [(et, 8 * (w + 1)), (ex, 8 * w)] t.mem t'.mem ∧ Keep mmRegs t t' :=
  WP.mono (stepQ_ok hs hbx h10 h8 h12 hbp hw hw' hXz hMz hTz hE sepX sepM hd hv hx) fun _ ⟨a, b, c, _⟩ => ⟨a, b, c⟩

end VG.Proof.Rsa.X86_64.WordReduce

end

end

/-! # Iterating normalized remainders over the private exponent -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordDivide

open VG VG.X86_64 VG.Impl.Rsa.X86_64.WordDivide
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem core_ok {s : State} {B : Addr} {Z W j : Nat} (h : Ws s B Z W)
    (hZ : slot W 17 ≤ Z) (hW : 6 ≤ W) (hj : 1 ≤ j) (hjW : j ≤ W)
    (hc : word s.mem B (slot W aV + 16) = BitVec.ofNat 64 j)
    (hd : 2 ^ 63 ≤ (word s.mem B (slot W aM + 8 * (W / 2 - 1))).toNat)
    (hv : (word s.mem B (slot W aV)).toNat =
      (2 ^ 128 - 1) / (word s.mem B (slot W aM + 8 * (W / 2 - 1))).toNat - 2 ^ 64)
    (hx : wv s.mem B (slot W aR) (W / 2) < wv s.mem B (slot W aM) (W / 2)) :
    WP isa (.seq (.block stepSetup) Impl.Rsa.X86_64.WordReduce.step) s fun t =>
      wv t.mem B (slot W aR) (W / 2) =
        (wv s.mem B (slot W aR) (W / 2) * 2 ^ 64 +
          (word s.mem B (slot W aD + 8 * (j - 1))).toNat) % wv s.mem B (slot W aM) (W / 2) ∧
      word t.mem B (slot W aV + 16) = BitVec.ofNat 64 j ∧
      Frm B (ranges W) s.mem t.mem ∧ Keep mmRegs s t := by
  have hz := window_bound h hZ
  have hn := h.scr.nowrap
  have hw := h.w2
  have hM := h.sl (j := aM) (by decide)
  have hR := h.sl (j := aR) (by decide)
  have hT := h.sl (j := aT) (by decide)
  have hsep : slot W aT + 8 * (W / 2 + 1) ≤ slot W aR ∨
      slot W aR + 8 * (W / 2) ≤ slot W aT := by
    simp only [slot, aT, aR]; omega_arith
  have hsepM : slot W aT + 8 * (W / 2 + 1) ≤ slot W aM ∨
      slot W aM + 8 * (W / 2) ≤ slot W aT := by
    simp only [slot, aT, aM]; omega_arith
  refine WP.seq (WP.mono (stepSetup_ok h hZ hj hjW hc) fun s₁ ⟨hbx, h10, h8, hbp, h12, hm₁, k₁⟩ => ?_)
  have f₁ : Frm B (ranges W) s.mem s₁.mem := by rw [hm₁]; exact range_store _ (by omega_arith) (by omega_arith) (by omega_arith)
  have h₁ := range_ws h f₁ k₁
  have M₁ := range_modulus f₁ (by omega_arith)
  have top₁ := range_top hW f₁ (by omega_arith)
  have recip₁ := range_recip f₁ (by omega_arith)
  have X₁ : wv s₁.mem B (slot W aR) (W / 2) = wv s.mem B (slot W aR) (W / 2) := by
    rw [hm₁]
    apply (writeW_outside s.mem B _ (by omega_arith)).wv _ (by omega_arith)
    left; simp only [slot, aR, aV]; omega_arith
  refine WP.mono (WordReduce.step_ok h₁.scr hbx h10 h8 h12 hbp
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) hsep hsepM (by rw [top₁]; exact hd) (by rw [recip₁, top₁]; exact hv)
    (by rw [X₁, M₁]; exact hx)) fun s₂ ⟨v₂, f₂, k₂⟩ => ?_
  have f₂' := range_core f₂
  have f02 := f₁.trans f₂'
  have k02 := k₁.trans k₂
  have h₂ := range_ws h f02 (k02.mono (by simp))
  have c₂ : word s₂.mem B (slot W aV + 16) = BitVec.ofNat 64 j := by
    rw [f₂.word_eq (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [slot, aT, aR, aV] <;> omega_arith) (by omega_arith)]
    rw [hm₁]
    rw [(writeW_outside s.mem B _ (by omega_arith)).word (Or.inr (by omega_arith)) (by omega_arith), hc]
  exact ⟨by rw [v₂, X₁, M₁, hm₁, word_writeW_self], c₂, f02, k02.mono (by simp)⟩

theorem body_ok {s : State} {B : Addr} {Z W j : Nat} (h : Ws s B Z W)
    (hZ : slot W 17 ≤ Z) (hW : 6 ≤ W) (hj : 1 ≤ j) (hjW : j ≤ W)
    (hc : word s.mem B (slot W aV + 16) = BitVec.ofNat 64 j)
    (hd : 2 ^ 63 ≤ (word s.mem B (slot W aM + 8 * (W / 2 - 1))).toNat)
    (hv : (word s.mem B (slot W aV)).toNat =
      (2 ^ 128 - 1) / (word s.mem B (slot W aM + 8 * (W / 2 - 1))).toNat - 2 ^ 64)
    (hx : wv s.mem B (slot W aR) (W / 2) < wv s.mem B (slot W aM) (W / 2)) :
    WP isa body s fun t =>
      wv t.mem B (slot W aR) (W / 2) =
        (wv s.mem B (slot W aR) (W / 2) * 2 ^ 64 +
          (word s.mem B (slot W aD + 8 * (j - 1))).toNat) % wv s.mem B (slot W aM) (W / 2) ∧
      word t.mem B (slot W aV + 16) = BitVec.ofNat 64 (j - 1) ∧
      t.gpr .rax = BitVec.ofNat 64 (j - 1) ∧ t.zf = some (decide (j = 1)) ∧
      Frm B (ranges W) s.mem t.mem ∧ Keep mmRegs s t := by
  have hz := window_bound h hZ
  have hn := h.scr.nowrap
  have hw := h.w2
  have hM := h.sl (j := aM) (by decide)
  have hR := h.sl (j := aR) (by decide)
  have hT := h.sl (j := aT) (by decide)
  have hsep : slot W aT + 8 * (W / 2 + 1) ≤ slot W aR ∨
      slot W aR + 8 * (W / 2) ≤ slot W aT := by
    simp only [slot, aT, aR]; omega_arith
  have hsepM : slot W aT + 8 * (W / 2 + 1) ≤ slot W aM ∨
      slot W aM + 8 * (W / 2) ≤ slot W aT := by
    simp only [slot, aT, aM]; omega_arith
  unfold body
  change WP isa (.seq (.block stepSetup) (.seq Impl.Rsa.X86_64.WordReduce.step (.block next))) s _
  refine WP.seq (WP.mono (stepSetup_ok h hZ hj hjW hc) fun s₁ ⟨hbx, h10, h8, hbp, h12, hm₁, k₁⟩ => ?_)
  have f₁ : Frm B (ranges W) s.mem s₁.mem := by rw [hm₁]; exact range_store _ (by omega_arith) (by omega_arith) (by omega_arith)
  have h₁ := range_ws h f₁ k₁
  have M₁ := range_modulus f₁ (by omega_arith)
  have top₁ := range_top hW f₁ (by omega_arith)
  have recip₁ := range_recip f₁ (by omega_arith)
  have X₁ : wv s₁.mem B (slot W aR) (W / 2) = wv s.mem B (slot W aR) (W / 2) := by
    rw [hm₁]
    apply (writeW_outside s.mem B _ (by omega_arith)).wv _ (by omega_arith)
    left; simp only [slot, aR, aV]; omega_arith
  refine WP.seq (WP.mono (WordReduce.step_ok h₁.scr hbx h10 h8 h12 hbp
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) hsep hsepM (by rw [top₁]; exact hd) (by rw [recip₁, top₁]; exact hv)
    (by rw [X₁, M₁]; exact hx)) fun s₂ ⟨v₂, f₂, k₂⟩ => ?_)
  have f₂' := range_core f₂
  have f02 := f₁.trans f₂'
  have k02 := k₁.trans k₂
  have h₂ := range_ws h f02 (k02.mono (by simp))
  have c₂ : word s₂.mem B (slot W aV + 16) = BitVec.ofNat 64 j := by
    rw [f₂.word_eq (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [slot, aT, aR, aV] <;> omega_arith) (by omega_arith)]
    rw [hm₁]
    rw [(writeW_outside s.mem B _ (by omega_arith)).word (Or.inr (by omega_arith)) (by omega_arith), hc]
  refine WP.mono (next_ok h₂ hZ hj hjW c₂) fun t ⟨ha, hz', hm₃, k₃⟩ => ?_
  have f₃ : Frm B (ranges W) s₂.mem t.mem := by rw [hm₃]; exact range_store _ (by omega_arith) (by omega_arith) (by omega_arith)
  have X₃ : wv t.mem B (slot W aR) (W / 2) = wv s₂.mem B (slot W aR) (W / 2) := by
    rw [hm₃]
    apply (writeW_outside s₂.mem B _ (by omega_arith)).wv _ (by omega_arith)
    left; simp only [slot, aR, aV]; omega_arith
  refine ⟨?_, ?_, ha, hz', f02.trans f₃, (k02.trans k₃).mono (by simp)⟩
  · rw [X₃, v₂, X₁, M₁, hm₁, word_writeW_self]
  · rw [hm₃, word_writeW_self]

/-- The loop from the digit `j₀`, the remainder the dividend's words from `j₀` on reduced, computes the
entire dividend's remainder. -/
theorem loop_ok {s : State} {B : Addr} {Z W j₀ : Nat} (h : Ws s B Z W)
    (hZ : slot W 17 ≤ Z) (hW : 6 ≤ W) (hj₀ : 1 ≤ j₀) (hj₀W : j₀ ≤ W)
    (hc : word s.mem B (slot W aV + 16) = BitVec.ofNat 64 j₀)
    (ha : s.gpr .rax = BitVec.ofNat 64 j₀)
    (hd : 2 ^ 63 ≤ (word s.mem B (slot W aM + 8 * (W / 2 - 1))).toNat)
    (hv : (word s.mem B (slot W aV)).toNat =
      (2 ^ 128 - 1) / (word s.mem B (slot W aM + 8 * (W / 2 - 1))).toNat - 2 ^ 64)
    (P : Nat → Nat)
    (hP : ∀ j, 1 ≤ j → j ≤ j₀ → P (j - 1) = (word s.mem B (slot W aD + 8 * (j - 1))).toNat + 2 ^ 64 * P j)
    (h0 : wv s.mem B (slot W aR) (W / 2) = P j₀ % wv s.mem B (slot W aM) (W / 2))
    (hMpos : 0 < wv s.mem B (slot W aM) (W / 2)) :
    WP isa (.loop body .ne) s fun t =>
      wv t.mem B (slot W aR) (W / 2) = P 0 % wv s.mem B (slot W aM) (W / 2) ∧
      Frm B (ranges W) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := h.scr.nowrap
  have hw := h.w2
  have hz := window_bound h hZ
  have hMz := h.sl (j := aM) (by decide)
  have hDz := h.sl (j := aD) (by decide)
  let M := wv s.mem B (slot W aM) (W / 2)
  let Inv (i : Nat) (t : State) : Prop :=
    Ws t B Z W ∧ word t.mem B (slot W aV + 16) = BitVec.ofNat 64 (j₀ - i) ∧
      wv t.mem B (slot W aR) (W / 2) = P (j₀ - i) % M ∧
      Frm B (ranges W) s.mem t.mem ∧ Keep mmRegs s t
  refine wp_countdown (cnt := .rax) (by omega_using [hw, hj₀W]) (by omega_using [hj₀]) Inv ?_ ?_ ?_ ha
  · intro i hi t hI hcnt
    obtain ⟨ht, ct, xt, ft, kt⟩ := hI
    have tm := range_modulus ft (by omega_arith)
    have tt := range_top hW ft (by omega_arith)
    have tv := range_recip ft (by omega_arith)
    refine WP.mono (body_ok ht hZ hW (by omega_using [hi]) (by omega_arith) ct
      (by rw [tt]; exact hd) (by rw [tv, tt]; exact hv)
      (by rw [xt, tm]; exact Nat.mod_lt _ hMpos)) fun t' ⟨xt', ct', at', zt', ft', kt'⟩ => ?_
    have ff := ft.trans ft'
    have kk : Keep mmRegs s t' := (kt.trans kt').mono (by simp)
    have nextI : Inv (i + 1) t' := by
      refine ⟨range_ws h ff kk, ?_, ?_, ff, kk⟩
      · simpa only [Nat.sub_add_eq] using ct'
      · rw [xt', xt, tm]
        have digit : word t.mem B (slot W aD + 8 * (j₀ - i - 1)) =
            word s.mem B (slot W aD + 8 * (j₀ - i - 1)) :=
          ft.word_eq (by
            intro r hr
            simp only [ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl <;> simp only [slot, aD, aR, aT, aV] <;> omega_arith)
            (by omega_arith)
        rw [digit, show j₀ - (i + 1) = j₀ - i - 1 by omega_arith, hP (j₀ - i) (by omega_using [hi]) (by omega_arith)]
        simp only [M, Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.add_comm, Nat.mul_comm]
    refine ⟨nextI, ?_, ?_⟩
    · rw [at', show t.gpr .rax = BitVec.ofNat 64 (j₀ - i) from hcnt,
        ofNat64_pred (by omega_using [hi]) (by omega_using [hw, hj₀W])]
    · rw [zt', show t.gpr .rax = BitVec.ofNat 64 (j₀ - i) from hcnt,
        ofNat64_pred (by omega_using [hi]) (by omega_using [hw, hj₀W]),
        ofNat64_beq_zero (by omega_using [hw, hj₀W])]
      simp only [show (j₀ - i - 1 = 0) ↔ j₀ - i = 1 by omega_using [hi]]
  · intro t hI
    obtain ⟨_, _, xt, ft, kt⟩ := hI
    exact ⟨by simpa only [Nat.sub_self] using xt, ft, kt⟩
  · exact ⟨h, by simpa using hc, by simpa only [Nat.sub_zero] using h0, Frm.refl _ _ _, Keep.refl _ _⟩

end VG.Proof.Rsa.X86_64.WordDivide

end

end

/-! # Initialization and complete word reduction -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordDivide

open VG VG.X86_64 VG.Impl.Rsa.X86_64.WordDivide
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The complete operation also clears the high remainder and writes the reciprocal. -/
def allRanges (W : Nat) : List (Nat × Nat) :=
  [(slot W aR, 8 * (W + 2)), (slot W aT, 8 * (W / 2 + 1)), (slot W aV, 24)]

theorem cover {B : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (hf : Frm B rs m m')
    (hc : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Frm B rs' m m' := by
  intro x hx
  apply hf x
  intro r hr
  obtain ⟨r', hr', h1, h2⟩ := hc r hr
  have := hx r' hr'
  omega_using [this, h1, h2]

theorem all_mut {W : Nat} {r : Nat × Nat} (hr : r ∈ allRanges W) : Mut r := by
  simp only [allRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact Mut.ofSlot _ _ _

theorem all_bound {s : State} {B : Addr} {Z W : Nat} (h : Ws s B Z W) (hZ : slot W 17 ≤ Z)
    {r : Nat × Nat} (hr : r ∈ allRanges W) : r.1 + r.2 ≤ Z := by
  simp only [allRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.sl (by decide)
  · have := h.sl (j := aT) (by decide); dsimp only; omega_arith
  · exact window_bound h hZ

theorem reciprocal_lt {d : Nat} (hd : 2 ^ 63 ≤ d) : (2 ^ 128 - 1) / d - 2 ^ 64 < 2 ^ 64 := by
  obtain hq : (2 ^ 128 - 1) / d < 2 ^ 65 := by
    apply (Nat.div_lt_iff_lt_mul (by omega_using [hd])).mpr
    omega_using [hd]
  omega_using [hq]

/-- The dividend's words from `j` on, for a dividend below `2^(64 X)`, `X = j + (W / 2 - 1)`: its
`W / 2 - 1` words from `j`. -/
theorem seeded_prefix (m : Mem) (B : Addr) {d W j X : Nat} (hjX : j + (W / 2 - 1) = X) (hX : X ≤ W)
    (hlt : wv m B d W < 2 ^ (64 * X)) :
    wv m B (d + 8 * j) (W - j) = wv m B (d + 8 * j) (W / 2 - 1) ∧
      wv m B (d + 8 * j) (W / 2 - 1) < 2 ^ (64 * (W / 2 - 1)) := by
  obtain e := wv_add m B d j (W - j)
  rw [show j + (W - j) = W by omega_arith] at e
  obtain hP : wv m B (d + 8 * j) (W - j) < 2 ^ (64 * (W / 2 - 1)) := by
    obtain hp : 2 ^ (64 * X) = 2 ^ (64 * j) * 2 ^ (64 * (W / 2 - 1)) := by
      rw [← Nat.pow_add, ← hjX, Nat.mul_add]
    have : 2 ^ (64 * j) * wv m B (d + 8 * j) (W - j) < 2 ^ (64 * j) * 2 ^ (64 * (W / 2 - 1)) := by
      rw [← hp]; omega_arith
    exact Nat.lt_of_mul_lt_mul_left this
  obtain low := wv_low_of_lt (m := m) (B := B) (e := d + 8 * j) (v := W / 2 - 1) (w := W - j) (by omega_arith) hP
  exact ⟨low.symm, low ▸ hP⟩

/-- Setup, seed, reciprocal, public counter and the word loop compute the remainder, for a
dividend of `j₀ + (W / 2 - 1)` words, `j₀` the first digit's index that `st` computes. -/
theorem codeWith_ok {s : State} {B : Addr} {Z W : Nat} (h : Ws s B Z W)
    (hZ : slot W 17 ≤ Z) (hW : 6 ≤ W) {st : List Instr} {j₀ : Nat} (hst : StartOk st W j₀)
    (hd : 2 ^ 63 ≤ (word s.mem B (slot W aM + 8 * (W / 2 - 1))).toNat)
    (hMpos : 0 < wv s.mem B (slot W aM) (W / 2)) :
    WP isa (codeWith st) s fun t =>
      (wv s.mem B (slot W aD) W < 2 ^ (64 * (j₀ + (W / 2 - 1))) → wv t.mem B (slot W aR) (W + 1) =
        wv s.mem B (slot W aD) W % wv s.mem B (slot W aM) (W / 2)) ∧
      Frm B (allRanges W) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := h.scr.nowrap
  have hw := h.w2
  obtain hz := window_bound h hZ
  obtain hM := h.sl (j := aM) (by decide)
  obtain hR := h.sl (j := aR) (by decide)
  obtain hD := h.sl (j := aD) (by decide)
  obtain sepRM := slot_far (w := W) (i := aR) (j := aM) (by decide)
  obtain sepRD := slot_far (w := W) (i := aR) (j := aD) (by decide)
  have hxw := hst.fit
  have hj1 := hst.pos
  unfold codeWith
  change WP isa (.seq (VG.Impl.Rsa.X86_64.Keys.zeroA aR) (.seq (seedWith st) (.seq (.block recipSetup)
    (.seq VG.Impl.Bignum.X86_64.R2Words.recip (.seq (.block (countSetupWith st)) (.loop body .ne)))))) s _
  refine WP.seq (WP.mono (zeroA_ok h (by decide)) fun s₀ ⟨z₀, o₀, k₀⟩ => ?_)
  obtain f₀ : Frm B (allRanges W) s.mem s₀.mem := Frm.of_outside o₀ (by simp [allRanges])
  obtain h₀ := h.congr f₀ (fun _ hr => all_mut hr) k₀ (by decide)
  refine WP.seq (WP.mono (seedWith_ok h₀ hW hst) fun s₁ ⟨v₁, oS, kS⟩ => ?_)
  obtain o₁ : Outside B (slot W aR) (8 * (W + 2)) s.mem s₁.mem :=
    o₀.trans (oS.mono (Nat.le_refl _) (by omega_arith))
  obtain f₁ : Frm B (allRanges W) s.mem s₁.mem := Frm.of_outside o₁ (by simp [allRanges])
  obtain h₁ := h.congr f₁ (fun _ hr => all_mut hr) (k₀.trans kS) (by decide)
  obtain M₁ : wv s₁.mem B (slot W aM) (W / 2) = wv s.mem B (slot W aM) (W / 2) :=
    o₁.wv (by omega_arith) (by omega_arith)
  obtain top₁ : word s₁.mem B (slot W aM + 8 * (W / 2 - 1)) = word s.mem B (slot W aM + 8 * (W / 2 - 1)) :=
    o₁.word (by omega_arith) (by omega_arith)
  obtain D₁ : wv s₁.mem B (slot W aD) W = wv s.mem B (slot W aD) W :=
    o₁.wv (by omega_arith) (by omega_arith)
  -- the remainder's words: the seed below `W / 2 - 1`, zero from there
  obtain zS : ∀ i, W / 2 - 1 ≤ i → i < W + 2 → word s₁.mem B (slot W aR + 8 * i) = 0 := fun i h1 h2 => by
    rw [oS.word (.inr (by omega_arith)) (by omega_arith)]
    exact (wv_eq_zero_iff _ _ _ _).mp z₀ i h2
  refine WP.seq (WP.mono (recipSetup_ok h₁) fun s₂ ⟨h10, h8, h12, m₂, k₂⟩ => ?_)
  refine WP.seq (WP.mono (R2w.recip_ok (h₁.scr.congr k₂.2.2) h10 h12 h8
    (by omega_arith) (by omega_arith) (by omega_arith) (by rw [m₂, top₁]; exact hd))
    fun s₃ ⟨m₃, k₃⟩ => ?_)
  obtain o₃ : Outside B (slot W aV) 8 s₁.mem s₃.mem := by
    rw [m₃, m₂]; exact writeW_outside _ _ _ (by omega_arith)
  obtain f₃ : Frm B (allRanges W) s₁.mem s₃.mem := by
    apply cover (Frm.of_outside o₃ (by simp : (slot W aV, 8) ∈ [(slot W aV, 8)]))
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, allRanges]
    exact ⟨(slot W aV, 24), by simp, (Nat.le_refl _), by omega_arith⟩
  obtain k03 := ((k₀.trans kS).trans k₂).trans k₃
  obtain h₃ := h₁.congr f₃ (fun _ hr => all_mut hr) (k₂.trans k₃) (by decide)
  refine WP.seq (WP.mono (countSetupWith_ok h₃ hZ hst)
    fun s₄ ⟨ha, m₄, k₄⟩ => ?_)
  obtain o₄ : Outside B (slot W aV + 16) 8 s₃.mem s₄.mem := by
    rw [m₄]; exact writeW_outside _ _ _ (by omega_arith)
  obtain f₄ : Frm B (allRanges W) s₃.mem s₄.mem := by
    rw [m₄]
    apply cover (range_store (B := B) (W := W) _ (by omega_arith) (by omega_arith) (by omega_arith))
    intro r hr
    simp only [ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨(slot W aR, 8 * (W + 2)), by simp [allRanges], (Nat.le_refl _), by omega_arith⟩
    · exact ⟨(slot W aT, 8 * (W / 2 + 1)), by simp [allRanges], (Nat.le_refl _), (Nat.le_refl _)⟩
    · exact ⟨(slot W aV, 24), by simp [allRanges], by omega_arith, by omega_arith⟩
  obtain h₄ := h₃.congr f₄ (fun _ hr => all_mut hr) k₄ (by decide)
  obtain eqM : wv s₄.mem B (slot W aM) (W / 2) = wv s.mem B (slot W aM) (W / 2) := by
    rw [o₄.wv (by simp only [slot, aM, aV]; omega_arith) (by omega_arith),
      o₃.wv (by simp only [slot, aM, aV]; omega_arith) (by omega_arith), M₁]
  obtain eqD : wv s₄.mem B (slot W aD) W = wv s.mem B (slot W aD) W := by
    rw [o₄.wv (by simp only [slot, aD, aV]; omega_arith) (by omega_arith),
      o₃.wv (by simp only [slot, aD, aV]; omega_arith) (by omega_arith), D₁]
  obtain eqTop : word s₄.mem B (slot W aM + 8 * (W / 2 - 1)) = word s.mem B (slot W aM + 8 * (W / 2 - 1)) := by
    rw [o₄.word (by simp only [slot, aM, aV]; omega_arith) (by omega_arith),
      o₃.word (by simp only [slot, aM, aV]; omega_arith) (by omega_arith), top₁]
  obtain R₄ : ∀ n, n ≤ W + 2 → wv s₄.mem B (slot W aR) n = wv s₁.mem B (slot W aR) n := fun n hn' => by
    rw [o₄.wv (by simp only [slot, aR, aV]; omega_arith) (by omega_arith),
      o₃.wv (by simp only [slot, aR, aV]; omega_arith) (by omega_arith)]
  obtain zhi : wv s₄.mem B (slot W aR + 8 * (W / 2)) (W + 2 - W / 2) = 0 := by
    rw [o₄.wv (by simp only [slot, aR, aV]; omega_arith) (by omega_arith),
      o₃.wv (by simp only [slot, aR, aV]; omega_arith) (by omega_arith)]
    exact wv_zero fun i hi => by rw [Nat.add_assoc, ← Nat.mul_add]; exact zS _ (by omega_arith) (by omega_arith)
  -- the remainder starts as the seed, below the divisor
  obtain z1 : wv s₄.mem B (slot W aR + 8 * (W / 2 - 1)) 1 = 0 := by
    rw [o₄.wv (by simp only [slot, aR, aV]; omega_arith) (by omega_arith),
      o₃.wv (by simp only [slot, aR, aV]; omega_arith) (by omega_arith)]
    exact wv_zero fun i hi => by
      rw [Nat.add_assoc, ← Nat.mul_add]; exact zS _ (by omega_arith) (by omega_arith)
  obtain e1 := wv_add s₄.mem B (slot W aR) (W / 2 - 1) 1
  rw [show W / 2 - 1 + 1 = W / 2 by omega_arith, z1, Nat.mul_zero, Nat.add_zero] at e1
  obtain Mlo : 2 ^ (64 * (W / 2 - 1)) ≤ wv s₄.mem B (slot W aM) (W / 2) := by
    obtain t := (R2w.top_half s₄.mem B (slot W aM) (W / 2 - 1)).mpr (by rw [eqTop]; exact hd)
    rw [show W / 2 - 1 + 1 = W / 2 by omega_arith] at t
    have : 2 ^ (64 * (W / 2 - 1)) ≤ 2 ^ (64 * (W / 2)) / 2 := by
      rw [show 64 * (W / 2) = 64 * (W / 2 - 1) + 63 + 1 by omega_arith, Nat.pow_succ, Nat.mul_div_cancel _ (by decide),
        Nat.pow_add]
      exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    omega_arith
  obtain R₀lt : wv s₄.mem B (slot W aR) (W / 2) < wv s₄.mem B (slot W aM) (W / 2) :=
    Nat.lt_of_lt_of_le (by rw [e1]; exact wv_lt _ _ _ _) Mlo
  -- the dividend's words below `j` after the remainder so far
  let R₀ := wv s₄.mem B (slot W aR) (W / 2)
  let P : Nat → Nat := fun j => R₀ * 2 ^ (64 * (j₀ - j)) + wv s₄.mem B (slot W aD + 8 * j) (j₀ - j)
  obtain hP : ∀ j, 1 ≤ j → j ≤ j₀ →
      P (j - 1) = (word s₄.mem B (slot W aD + 8 * (j - 1))).toNat + 2 ^ 64 * P j := fun j h1 h2 => by
    simp only [P]
    obtain ew := wv_add s₄.mem B (slot W aD + 8 * (j - 1)) 1 (j₀ - j)
    rw [show 1 + (j₀ - j) = j₀ - (j - 1) by omega_arith,
      show slot W aD + 8 * (j - 1) + 8 * 1 = slot W aD + 8 * j by omega_arith] at ew
    rw [ew, show j₀ - (j - 1) = (j₀ - j) + 1 by omega_arith, Nat.mul_add, Nat.pow_add]
    simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.pow_zero, Nat.one_mul]
    rw [show 2 ^ (64 * 1) = 2 ^ 64 from rfl, Nat.mul_add]
    ac_rfl
  obtain h0 : wv s₄.mem B (slot W aR) (W / 2) = P (j₀) % wv s₄.mem B (slot W aM) (W / 2) := by
    simp only [P, Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, wv, Nat.add_zero]
    exact (Nat.mod_eq_of_lt R₀lt).symm
  refine WP.mono (loop_ok h₄ hZ hW hj1 (by omega_arith) (by rw [m₄, word_writeW_self]) ha (by rw [eqTop]; exact hd)
    (by rw [o₄.word (d := slot W aV) (Or.inl (by omega_arith)) (by omega_arith), m₃, m₂, word_writeW_self,
          BitVec.toNat_ofNat, eqTop];
        rw [Nat.mod_eq_of_lt (reciprocal_lt (by rw [top₁]; exact hd)), top₁])
    P hP h0 (by rw [eqM]; exact hMpos)) fun t ⟨v, fl, kl⟩ => ?_
  obtain hi : wv t.mem B (slot W aR + 8 * (W / 2)) (W + 1 - W / 2) = 0 := by
    obtain zh' := wv_eq_zero_iff _ _ _ _ |>.mp zhi
    apply wv_zero
    intro i hi
    rw [fl.word_eq (by
      intro r hr
      simp only [ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [slot, aR, aT, aV] <;> omega_arith) (by omega_arith)]
    exact zh' i (by omega_arith)
  refine ⟨fun hX => ?_, ?_, ((k03.trans k₄).trans kl).mono (by decide)⟩
  · -- the seed is the dividend's words from `j₀`, so `P 0` is the dividend
    obtain hX₄ : wv s₄.mem B (slot W aD) W < 2 ^ (64 * (j₀ + (W / 2 - 1))) := by rw [eqD]; exact hX
    obtain ⟨pfx, -⟩ := seeded_prefix s₄.mem B (d := slot W aD) rfl hxw hX₄
    obtain Dj : wv s₄.mem B (slot W aD + 8 * j₀) (W / 2 - 1) =
        wv s₀.mem B (slot W aD + 8 * j₀) (W / 2 - 1) := by
      rw [o₄.wv (.inl (by simp only [slot, aD, aV]; omega_arith)) (by omega_arith),
        o₃.wv (.inl (by simp only [slot, aD, aV]; omega_arith)) (by omega_arith),
        oS.wv (.inr (by simp only [slot, aD, aR]; omega_arith)) (by omega_arith)]
    obtain seedv : R₀ = wv s₄.mem B (slot W aD + 8 * j₀) (W - j₀) := by
      simp only [R₀]; rw [e1, R₄ _ (by omega_arith), v₁, ← Dj, pfx]
    obtain P0 : P 0 = wv s₄.mem B (slot W aD) W := by
      simp only [P, Nat.sub_zero, Nat.mul_zero, Nat.add_zero]
      obtain ed := wv_add s₄.mem B (slot W aD) (j₀) (W - j₀)
      rw [show j₀ + (W - j₀) = W by omega_arith, ← seedv] at ed
      rw [ed, Nat.add_comm, Nat.mul_comm]
    have := wv_add t.mem B (slot W aR) (W / 2) (W + 1 - W / 2)
    rw [show W / 2 + (W + 1 - W / 2) = W + 1 by omega_arith, hi, Nat.mul_zero, Nat.add_zero] at this
    rw [this, v, P0, eqD, eqM, Nat.add_zero]
  · apply ((f₁.trans f₃).trans f₄).trans
    apply cover fl
    intro r hr
    simp only [ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨(slot W aR, 8 * (W + 2)), by simp [allRanges], (Nat.le_refl _), by omega_arith⟩
    · exact ⟨(slot W aT, 8 * (W / 2 + 1)), by simp [allRanges], (Nat.le_refl _), (Nat.le_refl _)⟩
    · exact ⟨(slot W aV, 24), by simp [allRanges], by omega_arith, by omega_arith⟩

/-- `codeWith_ok` for `code top`, a dividend of `xw W top` words. -/
theorem code_ok {s : State} {B : Addr} {Z W : Nat} (h : Ws s B Z W)
    (hZ : slot W 17 ≤ Z) (hW : 6 ≤ W) {top : Option Nat} (hk : ∀ k, top = some k → k ≤ W / 2)
    (hd : 2 ^ 63 ≤ (word s.mem B (slot W aM + 8 * (W / 2 - 1))).toNat)
    (hMpos : 0 < wv s.mem B (slot W aM) (W / 2)) :
    WP isa (code top) s fun t =>
      (wv s.mem B (slot W aD) W < 2 ^ (64 * xw W top) → wv t.mem B (slot W aR) (W + 1) =
        wv s.mem B (slot W aD) W % wv s.mem B (slot W aM) (W / 2)) ∧
      Frm B (allRanges W) s.mem t.mem ∧ Keep mmRegs s t := by
  have hw := h.w2
  rw [← j0_add top (W := W) (by omega_arith)]
  exact codeWith_ok h hZ hW (start_startOk hW (by omega_arith) hk) hd hMpos

end VG.Proof.Rsa.X86_64.WordDivide
