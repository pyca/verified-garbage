module

public import VerifiedGarbage.Proof.Dsa.X86_64.Frame
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! ### `Dsa.X86_64.MinusCore`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.MinusHead`, which only this module used -/

section

/-! # The first limb of DSA modulus-minus constants -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev minusHead (amount : Nat) : List Instr :=
  [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aN))),
    .mov .rbx (.mem (hdr (sArr aY))), .mov .rax (.mem (at0 .rsi)),
    .alu .sub .rax (.imm (BitVec.ofNat 32 amount)), .store (at0 .rbx) .rax, cfToRbp]

theorem minusHead_ok {s : State} {B : Addr} {Z w amount : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (ha : amount < 2 ^ 31) :
    WP isa (.block (minusHead amount)) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rsi = off B (slot w aN) ∧
      t.gpr .rbx = off B (slot w aY) ∧ Outside B (slot w aY) 8 s.mem t.mem ∧
      (∃ c : Bool, t.gpr .rbp = mask c ∧
        wv t.mem B (slot w aY) 1 + amount = wv s.mem B (slot w aN) 1 + 2 ^ 64 * c.toNat) ∧
      Keep [.r12, .rsi, .rbx, .rax, .rbp] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (Nat.le_trans (hdr_lt_slot w 8 hi) hZ)
  have hn := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hy := Nat.le_trans (slot_le (w := w) (show aY < 8 by decide)) hZ
  have hbound := hg.scr.nowrap
  refine WP.mono (WP.keep [.r12, .rsi, .rbx, .rax, .rbp] (Q := fun t =>
    t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rsi = off B (slot w aN) ∧
    t.gpr .rbx = off B (slot w aY) ∧ ∃ c : Bool, t.gpr .rbp = mask c ∧
    ∃ r : BitVec 64, t.mem = s.mem.writeW (off B (slot w aY)) r ∧
      r.toNat + amount = (word s.mem B (slot w aN)).toNat + 2 ^ 64 * c.toNat) ?_ rfl)
    fun t ⟨⟨ht12, htsi, htbx, c, htc, r, htm, hval⟩, hk⟩ => ?_
  · unfold minusHead cfToRbp
    xrun [State.ea, hdr, at0, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aN) (by decide),
      hl (sArr aY) (by decide), hg.hdr.hw, hg.hdr.harr aN (by decide), hg.hdr.harr aY (by decide),
      hg.scr.ld (show slot w aN + 8 ≤ Z by omega_using [hn]), hg.scr.st (show slot w aY + 8 ≤ Z by omega_using [hy]),
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, sx_ofNat ha]
    refine ⟨_, rfl, _, rfl, ?_⟩
    have h := sbb_toNat (word s.mem B (slot w aN)) (BitVec.ofNat 64 amount) false
    simpa only [Bool.toNat_false, Nat.add_zero,
      show (BitVec.ofBool false).setWidth 64 = 0#64 from rfl, BitVec.sub_zero,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show amount < 2 ^ 64 by omega_using [ha])] using h
  · refine ⟨ht12, htsi, htbx, ?_, ⟨c, htc, ?_⟩, hk⟩
    · rw [htm]; exact writeW_outside _ _ _ (by omega_using [hy, hbound])
    · rw [htm]
      simpa only [wv, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.pow_zero, Nat.one_mul,
        word_writeW_self] using hval

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.MinusStep`, which only this module used -/

section

/-! # Borrow propagation when forming DSA modulus-minus constants -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- After `j` words of `modulusMinus`'s loop: `Y_j + amount = N_j + 2^(64 j) c`. -/
structure MinusInv (s₀ : State) (B : Addr) (Z eN eY amount : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B eY (8 * j) s₀.mem t.mem
  val : ∃ c : Bool, t.gpr .rbp = mask c ∧
    wv t.mem B eY j + amount = wv s₀.mem B eN j + 2 ^ (64 * j) * c.toNat

theorem minusStep_ok {s₀ : State} {B : Addr} {Z w eN eY amount : Nat}
    (hbx : s₀.gpr .rbx = off B eY) (hsi : s₀.gpr .rsi = off B eN) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (hY : eY + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z)
    (hsep : eY + 8 * w ≤ eN ∨ eN + 8 * w ≤ eY) {j : Nat} (hj : j < w) {t : State}
    (hI : MinusInv s₀ B Z eN eY amount j t) :
    WP isa (.block (([cfFromRbp, .mov .rax (.mem (ix .rsi .r14)), .alu .sbb .rax (.imm 0),
        .store (ix .rbx .r14) .rax, cfToRbp] : List Instr) ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ MinusInv s₀ B Z eN eY amount (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = off B eY := (hI.keep.gpr (by decide)).trans hbx
  have tsi : t.gpr .rsi = off B eN := (hI.keep.gpr (by decide)).trans hsi
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨c, hbp, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ =>
      ∃ c' : Bool, t₁.gpr .rbp = mask c' ∧ ∃ r : BitVec 64, t₁.mem = t.mem.writeW (off B (eY + 8 * j)) r ∧
        r.toNat + c.toNat = (word t.mem B (eN + 8 * j)).toNat + 2 ^ 64 * c'.toNat) ?_ rfl)
    fun t₁ ⟨⟨c', h₁, r, hm, hr⟩, k₁⟩ => ?_
  · unfold cfFromRbp cfToRbp
    xrun [State.ea, ix, addr0 tbx hI.r14, addr0 tsi hI.r14, hbp, cf_mask, sx0,
      hI.scr.ld (show eN + 8 * j + 8 ≤ Z by omega_arith), hI.scr.st (show eY + 8 * j + 8 ≤ Z by omega_arith)]
    refine ⟨_, rfl, _, rfl, ?_⟩
    have := sbb_toNat (word t.mem B (eN + 8 * j)) 0 c
    simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero, Nat.zero_add] at this ⊢
    exact this
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega_arith) (by omega_arith)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hx : word t.mem B (eN + 8 * j) = word s₀.mem B (eN + 8 * j) := hI.out.word (by omega_arith) (by omega_arith)
  rw [hx] at hr
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    ⟨c', (k'.gpr (by decide)).trans h₁, ?_⟩⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B r (by omega_arith) x (by omega_arith)]
    exact hI.out x (by omega_arith)
  · have hlow : wv t.mem B eY j = wv (t.mem.writeW (off B (eY + 8 * j)) r) B eY j :=
      ((writeW_outside t.mem B r (by omega_arith)).wv (Or.inl (by omega_arith)) (by omega_arith)).symm
    rw [hm', hm]
    simp only [wv]
    rw [← hlow, word_writeW_self, pow64_succ]
    grind

end VG.Proof.Dsa.X86_64

end

end


/-! # Complete subtraction for DSA modulus-minus constants -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev minusTail : List Instr := [cfFromRbp, .mov .rax (.mem (ix .rsi .r14)), .alu .sbb .rax (.imm 0),
  .store (ix .rbx .r14) .rax, cfToRbp]

/-- Copy the modulus minus a small constant into the ordinary result array.
The input modulus is preserved, including its leading-zero padding. -/
theorem minusCore_ok {s : State} {B : Addr} {Z w amount : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (ha : amount < 2 ^ 31) (hm : amount ≤ wv s.mem B (slot w aN) w) :
    WP isa (.seq (.block (minusHead amount)) (wordLoop 1 minusTail)) s fun t =>
      wv t.mem B (slot w aY) w = wv s.mem B (slot w aN) w - amount ∧
      Outside B (slot w aY) (8 * w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hnowrap := hg.scr.nowrap
  have hy := Nat.le_trans (slot_le (w := w) (show aY < 8 by decide)) hZ
  have hn := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hsep := slot_sep (w := w) (show aY ≠ aN by decide)
  refine WP.seq (WP.mono (minusHead_ok hg hZ ha) fun u ⟨hu12, husi, hubx, hfu, hval, hku⟩ => ?_)
  have huN : ∀ k ≤ w, wv u.mem B (slot w aN) k = wv s.mem B (slot w aN) k :=
    fun k hk => hfu.wv (by omega_using [hsep, hk]) (by omega_using [hnowrap, hn, hk])
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 1 → t.mem = u.mem → Keep [.r14] u t → t.cf = u.cf →
      MinusInv u B Z (slot w aN) (slot w aY) amount 1 t := by
    intro t ht14 htm hkt _
    obtain ⟨c, huc, huv⟩ := hval
    refine ⟨hg.scr.congr (hkt.2.2.trans hku.2.2), hkt.mono (by decide), ht14,
      by rw [htm]; exact Outside.refl _ _ _ _, ⟨c, (hkt.gpr (by decide)).trans huc, ?_⟩⟩
    rw [htm, huN 1 (by omega_using [hw])]
    exact huv
  refine WP.mono (wordLoop_ok (start := 1) (N := w) (by omega_using [hw]) hw'
    (MinusInv u B Z (slot w aN) (slot w aY) amount) h0
    (fun j _ hj t hi => minusStep_ok hubx husi hu12 (by omega_using [hw']) (by omega_using [hy]) (by omega_using [hn]) (by omega_using [hsep]) hj hi))
    fun t ht => ?_
  obtain ⟨c, _, hv⟩ := ht.val
  rw [huN w (Nat.le_refl _)] at hv
  have hvlt := wv_lt t.mem B (slot w aY) w
  refine ⟨?_, (hfu.mono (Nat.le_refl _) (by omega_using [hw])).trans ht.out, (hku.trans ht.keep).mono (by decide)⟩
  cases c
  · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hv
    omega_using [hv]
  · simp only [Bool.toNat_true, Nat.mul_one] at hv
    omega_using [hm, hvlt, hv]

end VG.Proof.Dsa.X86_64

end

end

/-! # Modulus-minus constants in a linked DSA workspace -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem minus_ok {s : State} {B : Addr} {Z o w wx m amount : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hm : ModCtx s (off B o) (slot wx 8) wx minv m)
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 31) (ha : amount < 2 ^ 31) (ham : amount ≤ m) :
    WP isa (.seq (.block (minusHead amount)) (wordLoop 1 minusTail)) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx aY) wx = m - amount ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (minusCore_ok hc.good (Nat.le_refl _) hw hw' ha (by rw [hm.modulus]; exact ham))
    fun t ⟨ht, hf, hk⟩ => ?_
  have harr : Arrays (off B o) wx [aY] s.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self aY) hf (Nat.le_refl _) (by omega_using [])
  have hct := arrays_context hc harr (by decide) hk
  have hz := hc.good.scr.nowrap
  have hn := (harr.wv_of_not_mem (show aN < 8 by decide) (by decide) hz).trans hm.modulus
  have hi : ((word t.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [harr.word0_of_not_mem (by decide) (by decide) hz (by omega_using [hw])]
    exact hm.inverse
  rw [hm.modulus] at ht
  exact ⟨hct, ⟨hct.good, hn, hi⟩, ht, arrays_work harr (by decide), hk⟩

end VG.Proof.Dsa.X86_64
