module

public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombHorner
public import VerifiedGarbage.Proof.Mont.Arm.Words
public import VerifiedGarbage.Proof.Weierstrass.Arm.Bits
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombIndex
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombMagnitude
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombBody
import VerifiedGarbage.Proof.Weierstrass.CombDigitTopW
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Decode one signed comb digit, reading only the last window's real bits. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Proof.X25519.Arm VG.Proof.Mont.Arm

theorem lastTest_ok (K : TCombCfg) {s : State} {j : Nat}
    (hj : j<2^32) (hJ : K.J-1<2^32)
    (enc : encodable (BitVec.ofNat 32 (K.J-1))=true)
    (gj : s.gpr .r11=BitVec.ofNat 32 j) :
    WP isa (.block K.lastTest) s fun t =>
      t.z=decide (j=K.J-1) ∧ RegOnly [] s t := by
  unfold TCombCfg.lastTest
  refine wp_cmp (op2_imm enc) fun t f z => WP.block_nil ⟨?_,⟨f.rest _,f.mem⟩⟩
  rw [z,gj]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq]
  change BitVec.ofNat 32 j-BitVec.ofNat 32 (K.J-1)=0#32 ↔ j=K.J-1
  rw [sub_zero_iff,ofNat32_eq hj hJ]

theorem hornerWindow_ok (K : TCombCfg) {s : State} {base : Addr} {size len j count : Nat}
    (hs : Scr s base size) (hf : Far s base len)
    (hw : K.w<9) (hc : count≤K.w) (hd : K.L.bits<8192)
    (ho : K.L.bits%4096+K.w≤4096) (hl : K.L.bits+K.w*j+count≤len)
    (hp : s.gpr .r4=s.gpr .r12+BitVec.ofNat 32 (K.w*j+farOff K.L.bits))
    {v : Nat → Nat} (hv : ∀ i,v i≤1)
    (hb : ∀ i<count,s.mem (VG.Proof.Mont.off base (K.L.bits+K.w*j+i))=BitVec.ofNat 8 (v i)) :
    WP isa (.block (K.horner count)) s fun t =>
      t.gpr .r9=BitVec.ofNat 32 (hornerVal v 0 count) ∧ RegOnly [.r5,.r9] s t := by
  unfold TCombCfg.horner
  refine hornerAt_ok K hv count 0 s (by omega) (by omega) fun i hi => ?_
  have fa := far_add hd
  have ea : State.addr (s.gpr .r4+BitVec.ofNat 32 (K.L.bits%4096+0+i))=
      VG.Proof.Mont.off base (K.L.bits+K.w*j+i) := by
    rw [hf.ea_reg hs hp (by omega)]
    congr 1
    omega
  rw [ea]
  exact ⟨hf.read (by omega),by simpa only [Nat.zero_add] using hb i hi⟩

theorem digitWords_ok (K : TCombCfg) {s : State} {base : Addr} {size len j : Nat}
    (hs : Scr s base size) (hf : Far s base len)
    (hw : K.w<9) (ht : K.topBits≤K.w)
    (hj : j<2^32) (hJ : K.J-1<2^32)
    (enc : encodable (BitVec.ofNat 32 (K.J-1))=true)
    (hd : K.L.bits<8192) (ho : K.L.bits%4096+K.w≤4096)
    (hl : K.L.bits+K.w*j+(if j=K.J-1 then K.topBits else K.w)≤len)
    (gj : s.gpr .r11=BitVec.ofNat 32 j)
    {v : Nat → Nat} (hv : ∀ i,v i≤1)
    (hb : ∀ i<(if j=K.J-1 then K.topBits else K.w),
      s.mem (VG.Proof.Mont.off base (K.L.bits+K.w*j+i))=BitVec.ofNat 8 (v i)) :
    WP isa K.digit s fun t =>
      t.gpr .r9=BitVec.ofNat 32
        (magH K.H (hornerVal v 0 (if j=K.J-1 then K.topBits else K.w))) ∧
      RegOnly [.r4,.r5,.r9] s t := by
  let count := if j=K.J-1 then K.topBits else K.w
  have hc : count≤K.w := by dsimp only [count]; split <;> omega
  unfold TCombCfg.digit
  rw [WP.seq_iff]
  refine WP.mono (windowIndex_ok K hw gj) fun s₁ ⟨p₁,k₁⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (lastTest_ok K hj hJ enc (by rw [k₁.keep.gpr .r11 (by decide),gj]))
    fun s₂ ⟨z₂,k₂⟩ => ?_
  have keep₂ : Rest [.r4] s s₂ := k₁.keep.trans (k₂.keep.mono (by simp))
  have mem₂ : s₂.mem=s.mem := k₂.mem.trans k₁.mem
  have hs₂ := hs.of_rest keep₂ (by decide)
  have hf₂ := hf.of_rest keep₂
  have p₂ : s₂.gpr .r4=s₂.gpr .r12+BitVec.ofNat 32 (K.w*j+farOff K.L.bits) := by
    rw [k₂.keep.gpr .r4 (by decide),p₁,k₂.keep.gpr .r12 (by decide)]
  have decode : WP isa
      (.ite .eq (.block (K.horner K.topBits)) (.block (K.horner K.w))) s₂ fun t =>
      t.gpr .r9=BitVec.ofNat 32 (hornerVal v 0 count) ∧ RegOnly [.r5,.r9] s₂ t := by
    have hh := hornerWindow_ok K hs₂ hf₂ hw hc hd ho hl p₂ hv
      (by intro i hi; rw [mem₂]; exact hb i hi)
    by_cases h : j=K.J-1
    · apply WP.ite true (by change some s₂.z=some true; simp only [z₂,h,decide_true])
      · intro _; simpa only [count,h,↓reduceIte] using hh
      · intro impossible; cases impossible
    · apply WP.ite false (by change some s₂.z=some false; simp only [z₂,h,decide_false])
      · intro impossible; cases impossible
      · intro _; simpa only [count,h,↓reduceIte] using hh
  rw [WP.seq_iff]
  refine WP.mono decode fun s₃ ⟨v₃,k₃⟩ => ?_
  have hvlt : hornerVal v 0 count<2^K.w :=
    Nat.lt_of_lt_of_le (hornerVal_lt hv 0 count) (Nat.pow_le_pow_right (by decide) hc)
  refine WP.mono (magnitude_ok K hw hvlt v₃) fun s₄ ⟨v₄,k₄⟩ =>
    ⟨v₄,⟨((keep₂.mono (by simp)).trans (k₃.keep.mono (by simp))).trans k₄.keep,
      k₄.mem.trans (k₃.mem.trans mem₂)⟩⟩

theorem digit_ok (K : TCombCfg) {s : State} {base : Addr} {size len j k : Nat}
    (hs : Scr s base size) (hf : Far s base len)
    (hw : K.w<9) (hj : j<K.J) (hJ : K.J-1<2^32)
    (enc : encodable (BitVec.ofNat 32 (K.J-1))=true)
    (start : K.w*(K.J-1)≤K.L.nbits) (cover : K.L.nbits≤K.w*K.J)
    (hd : K.L.bits<8192) (ho : K.L.bits%4096+K.w≤4096)
    (hl : K.L.bits+K.L.nbits≤len) (hk : k<2^K.L.nbits)
    (gj : s.gpr .r11=BitVec.ofNat 32 j)
    (hb : ∀ i<K.L.nbits,s.mem (VG.Proof.Mont.off base (K.L.bits+i))=
      if k.testBit i then 1 else 0) :
    WP isa K.digit s fun t =>
      t.gpr .r9=BitVec.ofNat 32 (magH K.H (combWin K.w k j)) ∧ RegOnly [.r4,.r5,.r9] s t := by
  let count := if j=K.J-1 then K.topBits else K.w
  have bounds := windowBits_bounds hj start cover
  change count≤K.w ∧ K.w*j+count≤K.L.nbits ∧
    (count=K.w ∨ K.w*j+count=K.L.nbits) at bounds
  let v := fun i => (k.testBit (K.w*j+i)).toNat
  have hv : ∀ i,v i≤1 := by
    intro i
    dsimp only [v]
    cases k.testBit (K.w*j+i) <;> decide
  have bytes : ∀ i<count,s.mem (VG.Proof.Mont.off base (K.L.bits+K.w*j+i))=
      BitVec.ofNat 8 (v i) := by
    intro i hi
    rw [show K.L.bits+K.w*j+i=K.L.bits+(K.w*j+i) by omega,hb _ (by omega)]
    dsimp only [v]
    cases k.testBit (K.w*j+i) <;> rfl
  refine WP.mono (digitWords_ok K hs hf hw (topWindow_le (by omega) cover)
    (by omega) hJ enc hd ho (by omega) gj hv bytes) fun t ⟨val,keep⟩ => ⟨?_,keep⟩
  rw [val]
  change BitVec.ofNat 32 (magH K.H (hornerVal v 0 count))=_
  rw [window_without_padding bounds.1 bounds.2.2 hk]

end VG.Proof.Weierstrass.Arm.TComb
