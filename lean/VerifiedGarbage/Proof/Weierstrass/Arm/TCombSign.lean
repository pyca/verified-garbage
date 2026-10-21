module

public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombHorner
public import VerifiedGarbage.Proof.Mont.Arm.Words
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombIndex
import VerifiedGarbage.Proof.Weierstrass.Arm.Const
import VerifiedGarbage.Proof.Weierstrass.CombDigitTopW
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! The digit's sign uses its top bit, with a zero virtual bit in the last window. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Proof.X25519.Arm VG.Proof.Mont.Arm

theorem signRead_ok (K : TCombCfg) {s : State} {base : Addr} {size len j : Nat} {b : Bool}
    (hs : Scr s base size) (hf : Far s base len)
    (hw : 1≤K.w ∧ K.w<9) (hd : K.L.bits<8192)
    (ho : K.L.bits%4096+K.w≤4096) (hl : K.L.bits+K.w*j+K.w≤len)
    (gj : s.gpr .r11=BitVec.ofNat 32 j)
    (hb : s.mem (VG.Proof.Mont.off base (K.L.bits+K.w*j+K.w-1))=if b then 1 else 0) :
    WP isa (.block K.signRead) s fun t =>
      t.gpr .r10=(if b then 0 else BitVec.allOnes 32) ∧ RegOnly [.r4,.r10] s t := by
  unfold TCombCfg.signRead
  refine VG.Proof.X25519.Arm.WP.append (windowIndex_ok K hw.2 gj) fun s₁ ⟨p₁,k₁⟩ => ?_
  have hs₁ := hs.of_rest k₁.keep (by decide)
  have hf₁ := hf.of_rest k₁.keep
  have fa := far_add hd
  have ea : State.addr (s₁.gpr .r4+BitVec.ofNat 32 (K.L.bits%4096+K.w-1))=
      VG.Proof.Mont.off base (K.L.bits+K.w*j+K.w-1) := by
    rw [hf₁.ea_reg hs₁ p₁ (by omega)]
    congr 1
    omega
  refine wp_ldrb (by omega) ea (hf₁.read (by omega)) fun s₂ u₂ =>
    wp_dp (op2_imm (by decide)) fun s₃ u₃ => WP.block_nil ?_
  refine ⟨?_,⟨(k₁.keep.mono (by simp)).trans
      ((u₂.rest (by simp)).trans (u₃.rest (by simp))),u₃.mem.trans (u₂.mem.trans k₁.mem)⟩⟩
  rw [u₃.gpr,dpVal,u₂.gpr,k₁.mem,hb]
  cases b <;> rfl

theorem onesMask_ok (s : State) :
    WP isa (.block [.movw .r10 0xffff,.movt .r10 0xffff]) s fun t =>
      t.gpr .r10=BitVec.allOnes 32 ∧ RegOnly [.r10] s t := by
  refine wp_movw fun s₁ u₁ => wp_movt fun s₂ u₂ => WP.block_nil ?_
  exact ⟨by rw [u₂.gpr,u₁.gpr]; rfl,
    ⟨(u₁.rest (by simp)).trans (u₂.rest (by simp)),u₂.mem.trans u₁.mem⟩⟩

theorem signMask_bit_ok (K : TCombCfg) {s : State} {base : Addr} {size len j k : Nat}
    (hs : Scr s base size) (hf : Far s base len)
    (hw : 1≤K.w ∧ K.w<9) (hj : j<K.J) (hJ : K.J-1<2^32)
    (enc : encodable (BitVec.ofNat 32 (K.J-1))=true)
    (start : K.w*(K.J-1)≤K.L.nbits) (cover : K.L.nbits≤K.w*K.J)
    (hd : K.L.bits<8192) (ho : K.L.bits%4096+K.w≤4096)
    (hl : K.L.bits+K.L.nbits≤len) (hk : k<2^K.L.nbits)
    (gj : s.gpr .r11=BitVec.ofNat 32 j)
    (hb : ∀ i<K.L.nbits,s.mem (VG.Proof.Mont.off base (K.L.bits+i))=
      if k.testBit i then 1 else 0) :
    WP isa K.signMask s fun t =>
      t.gpr .r10=(if k.testBit (K.w*j+(K.w-1)) then 0 else BitVec.allOnes 32) ∧
      RegOnly [.r4,.r10] s t := by
  have bounds := windowBits_bounds hj start cover
  change (if j=K.J-1 then K.topBits else K.w)≤K.w ∧
    K.w*j+(if j=K.J-1 then K.topBits else K.w)≤K.L.nbits ∧
    ((if j=K.J-1 then K.topBits else K.w)=K.w ∨
      K.w*j+(if j=K.J-1 then K.topBits else K.w)=K.L.nbits) at bounds
  have read (u : State) (keep : RegOnly [] s u) (hr : K.w*j+K.w≤K.L.nbits) :
      WP isa (.block K.signRead) u fun t =>
        t.gpr .r10=(if k.testBit (K.w*j+(K.w-1)) then 0 else BitVec.allOnes 32) ∧
        RegOnly [.r4,.r10] s t := by
    refine WP.mono (signRead_ok K (j := j) (b := k.testBit (K.w*j+(K.w-1)))
      (hs.of_rest keep.keep (by decide)) (hf.of_rest keep.keep)
      hw hd ho (by omega) (by rw [keep.keep.gpr .r11 (by decide),gj]) ?_)
      fun t ⟨val,rest⟩ => ⟨val,⟨(keep.keep.mono (by simp)).trans rest.keep,rest.mem.trans keep.mem⟩⟩
    rw [keep.mem,show K.L.bits+K.w*j+K.w-1=K.L.bits+(K.w*j+(K.w-1)) by omega]
    exact hb _ (by omega)
  unfold TCombCfg.signMask
  by_cases shortTop : K.topBits<K.w
  · simp only [shortTop,↓reduceIte]
    rw [WP.seq_iff]
    refine WP.mono (lastTest_ok K (by omega) hJ enc gj) fun u ⟨zero,keep⟩ => ?_
    by_cases last : j=K.J-1
    · apply WP.ite true (by change some u.z=some true; simp only [zero,last,decide_true])
      · intro _
        have e : K.w*j+K.topBits=K.L.nbits := by
          rw [last]
          exact Nat.add_sub_of_le start
        have high : k.testBit (K.w*j+(K.w-1))=false := by
          rw [Nat.testBit_eq_decide_div_mod_eq,
            Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) (by omega)))]
          decide
        refine WP.mono (onesMask_ok u) fun t ⟨val,rest⟩ => ?_
        refine ⟨?_,⟨(keep.keep.mono (by simp)).trans (rest.keep.mono (by simp)),rest.mem.trans keep.mem⟩⟩
        rw [val,high]
        rfl
      · intro impossible; cases impossible
    · apply WP.ite false (by change some u.z=some false; simp only [zero,last,decide_false])
      · intro impossible; cases impossible
      · intro _
        apply read u keep
        simpa only [last,↓reduceIte] using bounds.2.1
  · simp only [shortTop,↓reduceIte]
    apply read s ⟨Rest.refl _ _,rfl⟩
    have cw : K.w≤(if j=K.J-1 then K.topBits else K.w) := by split <;> omega
    omega

theorem signMask_ok (K : TCombCfg) {s : State} {base : Addr} {size len j k : Nat}
    (hs : Scr s base size) (hf : Far s base len)
    (hw : 1≤K.w ∧ K.w<9) (hj : j<K.J) (hJ : K.J-1<2^32)
    (enc : encodable (BitVec.ofNat 32 (K.J-1))=true)
    (start : K.w*(K.J-1)≤K.L.nbits) (cover : K.L.nbits≤K.w*K.J)
    (hd : K.L.bits<8192) (ho : K.L.bits%4096+K.w≤4096)
    (hl : K.L.bits+K.L.nbits≤len) (hk : k<2^K.L.nbits)
    (gj : s.gpr .r11=BitVec.ofNat 32 j)
    (hb : ∀ i<K.L.nbits,s.mem (VG.Proof.Mont.off base (K.L.bits+i))=
      if k.testBit i then 1 else 0) :
    WP isa K.signMask s fun t =>
      t.gpr .r10=(if K.H≤combWin K.w k j then 0 else BitVec.allOnes 32) ∧
      RegOnly [.r4,.r10] s t := by
  refine WP.mono (signMask_bit_ok K hs hf hw hj hJ enc start cover hd ho hl hk gj hb)
    fun t ⟨val,keep⟩ => ⟨?_,keep⟩
  rw [val,testBit_top k K.w j hw.1]
  change (if decide (K.H≤combWin K.w k j) then (0 : BitVec 32) else BitVec.allOnes 32)=_
  by_cases h : K.H≤combWin K.w k j
  · simp only [h,decide_true,↓reduceIte]
  · simp only [h,decide_false,↓reduceIte]
    rfl

end VG.Proof.Weierstrass.Arm.TComb
