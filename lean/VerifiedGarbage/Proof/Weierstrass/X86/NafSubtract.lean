import VerifiedGarbage.Proof.Weierstrass.X86.NafSubChain
import VerifiedGarbage.Proof.Weierstrass.Naf5
import VerifiedGarbage.Proof.Weierstrass.X86.TCombDigit

/-! The sign-extended subtraction produces twice the next NAF residual. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Weierstrass.X86 VG.Proof.Mont.X86 VG.Proof.Mont

theorem nafWord_toNat (k j : Nat) :
    (BitVec.ofInt 32 (Naf5.digit k j)).toNat =
      if Naf5.negative k j then 2^32-Naf5.magnitude k j else Naf5.magnitude k j := by
  have hb := Naf5.magnitude_le k j
  simp only [Naf5.digit,BitVec.toNat_ofInt]
  cases hn : Naf5.negative k j
  · simp only [Bool.false_eq_true,ite_false]
    change ((Naf5.magnitude k j:Int)%4294967296).toNat=_
    omega
  · have hp := Naf5.negative_magnitude_pos k j hn
    simp only [ite_true]
    change ((-(Naf5.magnitude k j:Int))%4294967296).toNat=_
    omega

theorem nafSign_toNat (k j : Nat) :
    (0#32-(BitVec.ofInt 32 (Naf5.digit k j)>>>31)).toNat =
      if Naf5.negative k j then 2^32-1 else 0 := by
  have hb := Naf5.magnitude_le k j
  have hp := Naf5.negative_magnitude_pos k j
  simp only [BitVec.toNat_sub,BitVec.toNat_zero,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,nafWord_toNat]
  cases hn : Naf5.negative k j
  · simp only [Bool.false_eq_true,ite_false]; omega
  · have hp := hp hn
    simp only [ite_true]; omega

theorem nafDigitVal9 (k j : Nat) :
    nafDigitVal (BitVec.ofInt 32 (Naf5.digit k j))
      (0#32-(BitVec.ofInt 32 (Naf5.digit k j)>>>31)) 8 =
      if Naf5.negative k j then 2^288-Naf5.magnitude k j else Naf5.magnitude k j := by
  simp only [nafDigitVal,nafWord_toNat,nafSign_toNat]
  have := Naf5.magnitude_le k j
  cases hn : Naf5.negative k j <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

theorem nafSubtract_next {v v' : Nat} {c : Bool} (k j : Nat)
    (hv : v=Naf5.residual k j) (hb : v≤2^256) (hlt : v'<2^288)
    (he : v'+nafDigitVal (BitVec.ofInt 32 (Naf5.digit k j))
      (0#32-(BitVec.ofInt 32 (Naf5.digit k j)>>>31)) 8 = v+2^288*c.toNat) :
    v'=2*Naf5.residual k (j+1) := by
  rw [nafDigitVal9] at he
  have hr := Naf5.recurrence k j
  have hm := Naf5.magnitude_le k j
  cases hn : Naf5.negative k j <;>
    simp only [hn,Bool.false_eq_true,ite_false,ite_true] at he hr <;>
    cases c <;> simp only [Bool.toNat_false,Bool.toNat_true] at he <;> omega

theorem nafSign_ok (s : State) :
    WP isa (.block Naf.sign) s fun t =>
      t.gpr .edx=0#32-(s.gpr .ecx>>>31) ∧ CKeeps [.eax,.edx] s t := by
  unfold Naf.sign
  refine wp_movS rfl fun s₁ U₁ _ => ?_
  refine wp_shr (by decide) fun s₂ U₂ _ => ?_
  refine wp_movS rfl fun s₃ U₃ _ => ?_
  refine wp_subS rfl fun t U₄ _ => WP.block_nil ?_
  refine ⟨?_,fun r hr => ?_,?_,?_,?_⟩
  · rw [U₄.gpr,U₃.gpr,U₃.other _ (by decide),U₂.gpr,U₁.gpr]
    rfl
  · have ha : r≠.eax := fun h => hr (h ▸ (by simp))
    have hd : r≠.edx := fun h => hr (h ▸ (by simp))
    rw [U₄.other _ hd,U₃.other _ hd,U₂.other _ ha,U₁.other _ ha]
  · rw [U₄.mem,U₃.mem,U₂.mem,U₁.mem]
  · rw [U₄.rd,U₃.rd,U₂.rd,U₁.rd]
  · rw [U₄.wr,U₃.wr,U₂.wr,U₁.wr]

theorem nafSubtract_ok {s : State} {base : Addr} {size work k j : Nat}
    (hs : Scr s base size) (ha : work+36≤size)
    (hx : s.gpr .ecx=BitVec.ofInt 32 (Naf5.digit k j))
    (hv : val32 s.mem base work 9=Naf5.residual k j)
    (hb : Naf5.residual k j≤2^256) :
    WP isa (.block (Naf.subtractDigit work)) s fun t =>
      val32 t.mem base work 9=2*Naf5.residual k (j+1) ∧
      Keeps [.eax,.edx] s t ∧ Outside base work 36 s.mem t.mem := by
  rw [Naf.subtractDigit,List.append_assoc,WP.block_append_iff]
  refine WP.mono (nafSign_ok s) fun a ⟨va,ka⟩ => ?_
  refine WP.mono (nafSubChain_ok (hs.of_keeps ka.keeps (by decide)) 8 ha)
    fun t ⟨ot,⟨c,hc,vt⟩,kt⟩ => ⟨?_,ka.keeps.trans (kt.mono (by decide)),?_⟩
  · rw [va,ka.1 .ecx (by decide),ka.2.1,hx] at vt
    have hlt : val32 t.mem base work 9 < 2^288 := by
      simpa only [show 32*9=288 from rfl] using val32_lt t.mem base work 9
    have radix : (2:Nat)^288 = 497323236409786642155382248146820840100456150797347717440463976893159497012533375533056 := by decide +kernel
    have ve : val32 t.mem base work 9 + nafDigitVal (BitVec.ofInt 32 (Naf5.digit k j))
        (0#32-(BitVec.ofInt 32 (Naf5.digit k j)>>>31)) 8 =
        val32 s.mem base work 9 + 2^288*c.toNat := by
      simpa only [Nat.reduceAdd,Nat.reduceMul,radix] using vt
    exact nafSubtract_next (c := c) k j hv (by omega) hlt ve
  · rw [ka.2.1] at ot
    exact ot

end VG.Proof.Weierstrass.X86
