module

public import VerifiedGarbage.Proof.Bignum.Arm.CombDigitTooth
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.CombDigitBit

/-! Five statically fixed teeth produce the complete secret digit. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombDigit
open VG VG.Arm VG.Proof.X25519.Arm

def prefixValue (bs : List Byte) (N i d : Nat) : Nat → Nat
  | 0 => 0
  | j+1 => prefixValue bs N i d j + 2^j*value bs N (i+j*d)

theorem prefixValue_lt (bs : List Byte) (N i d j : Nat) : prefixValue bs N i d j<2^j := by
  induction j with
  | zero => simp [prefixValue]
  | succ j ih =>
    have bit := value_lt bs N (i+j*d)
    have product : 2^j*value bs N (i+j*d) ≤ 2^j := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2^j) (show value bs N (i+j*d)≤1 by omega)
    simp only [prefixValue,Nat.pow_succ]
    omega

private structure GatherInv (s0 : State) (bs : List Byte) (N i d j : Nat) (s : State) : Prop where
  index : s.gpr .r9=BitVec.ofNat 32 (i+j*d)
  digit : s.gpr .r10=BitVec.ofNat 32 (prefixValue bs N i d j)
  mem : s.mem=s0.mem
  rest : Rest clobbers s0 s

/-- Raw byte semantics; the public-width bridge identifies this with the comb digit. -/
theorem code_ok (s : State) {src : BitVec 32} {bs : List Byte} {N i d : Nat}
    (source : Source src bs s) (widthBound : N≤8*bs.length) (size : bs.length<2^32)
    (positions : i+5*d<2^31) (widthFit : N<2^31)
    (ptr : s.gpr .r4=src) (length : s.gpr .r5=BitVec.ofNat 32 bs.length)
    (row : s.gpr .r6=BitVec.ofNat 32 i) (stride : s.gpr .r7=BitVec.ofNat 32 d)
    (width : s.gpr .r8=BitVec.ofNat 32 N) :
    WP isa VG.Impl.Bignum.Arm.CombDigit.code s fun t =>
      t.gpr .r11=BitVec.ofNat 32 (prefixValue bs N i d 5) ∧
      (t.gpr .r11).toNat<32 ∧ t.mem=s.mem ∧ Rest clobbers s t := by
  have step (j : Nat) (hj : j<5) (t : State) (h : GatherInv s bs N i d j t) :
      WP isa (VG.Impl.Bignum.Arm.CombDigit.tooth j) t (GatherInv s bs N i d (j+1)) := by
    have posBound : j*d≤5*d := Nat.mul_le_mul_right d (by omega)
    have nextBound : (j+1)*d≤5*d := Nat.mul_le_mul_right d (by omega)
    refine WP.mono (tooth_ok t (source.of_mem h.mem h.rest) widthBound size
      (by omega) widthFit (by omega) (prefixValue_lt bs N i d j) hj
      ((h.rest.gpr .r4 (by simp [clobbers])).trans ptr)
      ((h.rest.gpr .r5 (by simp [clobbers])).trans length)
      h.index ((h.rest.gpr .r8 (by simp [clobbers])).trans width)
      ((h.rest.gpr .r7 (by simp [clobbers])).trans stride) h.digit) ?_
    rintro u ⟨index,digit,mem,rest⟩
    refine ⟨?_,digit,mem.trans h.mem,h.rest.trans rest⟩
    simpa only [Nat.add_mul,Nat.one_mul,Nat.add_assoc] using index
  unfold VG.Impl.Bignum.Arm.CombDigit.code
  rw [WP.seq_iff]
  refine wp_mov (op2_reg _ _) fun a one => ?_
  refine wp_mov (op2_imm (by decide)) fun b two => WP.block_nil ?_
  have init : GatherInv s bs N i d 0 b := by
    refine ⟨?_,?_,two.mem.trans one.mem,(one.rest (by simp [clobbers])).trans (two.rest (by simp [clobbers]))⟩
    · simpa only [Nat.zero_mul,Nat.add_zero] using (two.other .r9 (by decide)).trans (one.gpr.trans row)
    · exact two.gpr
  rw [WP.seq_iff]
  refine WP.mono (step 0 (by decide) b init) ?_
  intro s1 h1
  rw [WP.seq_iff]
  refine WP.mono (step 1 (by decide) s1 h1) ?_
  intro s2 h2
  rw [WP.seq_iff]
  refine WP.mono (step 2 (by decide) s2 h2) ?_
  intro s3 h3
  rw [WP.seq_iff]
  refine WP.mono (step 3 (by decide) s3 h3) ?_
  intro s4 h4
  rw [WP.seq_iff]
  refine WP.mono (step 4 (by decide) s4 h4) ?_
  intro s5 h5
  refine wp_mov (op2_reg _ _) fun t last => WP.block_nil ?_
  have result : t.gpr .r11=BitVec.ofNat 32 (prefixValue bs N i d 5) := last.gpr.trans h5.digit
  have bounded : prefixValue bs N i d 5<32 := prefixValue_lt bs N i d 5
  refine ⟨result,?_,last.mem.trans h5.mem,h5.rest.trans (last.rest (by simp [clobbers]))⟩
  rw [result,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  exact bounded

end VG.Proof.Bignum.Arm.CombDigit
