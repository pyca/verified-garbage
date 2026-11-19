module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveControl
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveContext
import VerifiedGarbage.Proof.Ffdh.Arm.Block
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialValue
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.Arm.TrialDivision16
import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Impl.Bignum.Arm.TrialDivision16
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialOctets
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialStart
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialFlag
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Table
public import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveMath
import Mathlib.Data.Nat.GCD.Basic

/-! ### `Ffdh.Arm.ParameterCandidate.PairMath`, which this module and modules that import it used -/

section

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/TrialOffsetMath.lean`, which only this module imported.
section

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate

theorem offset_divides_half {p divisor : Nat} (oddP : p%2=1) (oddD : divisor%2=1) :
    ((p+(divisor-1))%divisor=0) ↔ (((p-1)/2)%divisor=0) := by
  have rearrange : p+(divisor-1)=(p-1)+divisor := by omega
  rw [rearrange,Nat.add_mod_right]
  have twice : p-1=2*((p-1)/2) := by omega
  rw [twice,←Nat.dvd_iff_mod_eq_zero,←Nat.dvd_iff_mod_eq_zero]
  have coprime : Nat.Coprime 2 divisor := by
    show Nat.gcd 2 divisor=1
    rw [Nat.gcd_rec,oddD]
    rfl
  rw [Nat.mul_div_cancel_left _ (by decide : 0<2)]
  exact coprime.symm.dvd_mul_left

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG
open VG.Impl.Ffdh.Arm.ParameterCandidate (trialCount)

theorem pairAny_mono {value a b : Nat} (bound : a≤b) (hit : pairAny value a=true) :
    pairAny value b=true := by
  simp only [pairAny,List.any_eq_true,List.mem_range] at hit ⊢
  obtain ⟨i,hi,divides⟩ := hit
  exact ⟨i,by omega_using [bound, hi],divides⟩

theorem pairNext_progress {n value i : Nat} (more : i<trialCount n) :
    i<pairNext n value i ∧ pairNext n value i≤trialCount n := by
  unfold pairNext
  split <;> omega_using [more]

theorem pairAny_eq {value count : Nat} (bound : count≤1024) (odd : value%2=1) :
    pairAny value count = (sieveAny value count || sieveAny ((value-1)/2) count) := by
  apply Bool.eq_iff_iff.mpr
  simp only [pairAny,sieveAny,List.any_eq_true,List.mem_range,Bool.or_eq_true,beq_iff_eq]
  have equivalent (i : Nat) (hi : i<count) :
      (VG.Impl.RsaKeyGen.tabEntry i-1+value)%VG.Impl.RsaKeyGen.tabEntry i=0 ↔
        ((value-1)/2)%VG.Impl.RsaKeyGen.tabEntry i=0 := by
    rw [Nat.add_comm]
    exact offset_divides_half odd (VG.Proof.RsaKeyGen.tabEntry_facts (by omega_using [bound, hi] : i<1024)).1
  constructor
  · rintro ⟨i,hi,h|h⟩
    · exact Or.inl ⟨i,hi,h⟩
    · exact Or.inr ⟨i,hi,(equivalent i hi).mp h⟩
  · rintro (⟨i,hi,h⟩|⟨i,hi,h⟩)
    · exact ⟨i,hi,Or.inl h⟩
    · exact ⟨i,hi,Or.inr ((equivalent i hi).mpr h)⟩

theorem pair_shape {value bits : Nat} (largeP : 8161<value) (largeQ : 8161<(value-1)/2)
    (oddP : value%2=1) (oddQ : ((value-1)/2)%2=1) :
    (!pairAny value (trialCount ((bits+7)/8))) =
      ((Spec.Ffdh.primeShape value && !Spec.RsaKeyGen.obviouslyComposite bits value) &&
        (Spec.Ffdh.primeShape ((value-1)/2) && !Spec.RsaKeyGen.obviouslyComposite bits ((value-1)/2))) := by
  rw [←sieve_shape largeP oddP,←sieve_shape largeQ oddQ,pairAny_eq (trialCount_bound _) oddP]
  cases sieveAny value (trialCount ((bits+7)/8)) <;>
    cases sieveAny ((value-1)/2) (trialCount ((bits+7)/8)) <;> rfl

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.PairTrials`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.PairEntry`, which this module and modules that import it used -/

section

/-! Reload one RSA table entry for both moduli without advancing the cursor. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG.Impl.Ffdh.Arm.ParameterCandidate (trialCount)
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (arrAt)

theorem pairEntry_ok {s : State} {dst base : BitVec 32} {n i : Nat}
    (h : SieveContext dst base n s) (bound : i < (trialCount n))
    (cursor : s.gpr .r10 = base + BitVec.ofNat 32 (arrAt ((n + 7) / 8) 34 + 4 * i)) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.pairEntry) s fun t =>
      (t.gpr .r7 = BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry i) ∧
        t.mem = s.mem) ∧
        Rest [.r7] s t := by
  have limitBound := trialCount_bound n
  have indexBound : i < 1024 := by omega_using [bound, limitBound]
  have read := h.tableReadable i indexBound
  have word : s.mem.readW (off (State.addr base) (arrAt ((n + 7) / 8) 34 + 4 * i)) 32 =
      BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry i) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := tableEntry_small indexBound; omega_using [this] :
      VG.Impl.RsaKeyGen.tabEntry i < 2 ^ 32)]
    exact h.table i indexBound
  have address : State.addr (base + BitVec.ofNat 32 (arrAt ((n + 7) / 8) 34 + 4 * i)) =
      off (State.addr base) (arrAt ((n + 7) / 8) 34 + 4 * i) :=
    VG.Arm.addr_add (by have := h.tableFits; omega_using [indexBound, this])
  refine withRest_all [.r7] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.pairEntry
  ffrun [BitVec.add_zero, cursor, address, read, word]

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.PairTrialSmall`, which only this module used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.PairTrialLoop`, which only this module used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.PairTrialStep`, which only this module used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.PairTrialRedc`, which only this module used -/

section

/-! Simultaneous p and p-1 trial division through the shared RSA reducer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Proof.RsaKeyGen VG.Proof.Bignum.Arm.TrialDivision16
open VG.Impl.Ffdh.Arm.ParameterCandidate

theorem trialPairRedc_ok {u : State} {h acc s sv : Nat} (digitValue : (u.gpr .r7).toNat = h) (hh : h < 2 ^ 16)
    (accValue : u.gpr .r8 = BitVec.ofNat 32 acc) (hacc : acc < 2 * s) (r4 : (u.gpr .r4).toNat = sv)
    (r3 : u.gpr .r3 = BitVec.ofNat 32 s) (hs : 3 ≤ s ∧ s < 8162) (hinv : (s * sv + 1) % 2 ^ 16 = 0)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ u', Rest [.r8, .r7, .r6] u u' → u'.mem = u.mem →
      (∀ a', a' < 2 * s → a' * 2 ^ 16 % s = (h + acc) % s → u'.gpr .r8 = BitVec.ofNat 32 a' →
        WP isa (.block rest) u' Q)) :
    WP isa (.block (trialPairRedc ++ rest)) u Q := by
  simp only [trialPairRedc, VG.Impl.Bignum.Arm.TrialDivision16.redcAt, List.cons_append, List.nil_append]
  refine wp_dp (op2_reg _ _) fun u1 v1 => wp_mul fun u2 v2 => wp_mov (op2_lsl (by decide)) fun u3 v3 =>
    wp_mov (op2_lsr (by decide)) fun u4 v4 => wp_mul fun u5 v5 => wp_dp (op2_reg _ _) fun u6 v6 =>
      wp_mov (op2_lsr (by decide)) fun u7 v7 => ?_
  have k7 : Rest [.r8, .r7, .r6] u u7 := (v1.rest (by simp)).trans ((v2.rest (by simp)).trans
    ((v3.rest (by simp)).trans ((v4.rest (by simp)).trans ((v5.rest (by simp)).trans ((v6.rest (by simp)).trans
      (v7.rest (by simp)))))))
  have m7 : u7.mem = u.mem := by rw [v7.mem, v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
  have ha : acc < 2 ^ 32 := by omega_using [hacc, hs]
  -- `X = h + acc`, `q = X sv mod 2^16`.
  have x1 : (u1.gpr .r7).toNat = h + acc := by
    rw [v1.gpr, dpVal, BitVec.toNat_add, digitValue, accValue, toNat_imm ha]; omega_using [hh, hacc, hs]
  have q4 : (u4.gpr .r6).toNat = (h + acc) * sv % 2 ^ 16 := by
    rw [v4.gpr, v3.gpr, lo16, v2.gpr, BitVec.toNat_mul, x1, v1.other _ (by decide), r4,
      Nat.mod_mod_of_dvd _ (by decide)]
  have hq := Nat.mod_lt ((h + acc) * sv) (Nat.two_pow_pos 16)
  have s5 : (u5.gpr .r6).toNat = (h + acc) * sv % 2 ^ 16 * s := by
    rw [v5.gpr, BitVec.toNat_mul, q4, v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide),
      v1.other _ (by decide), r3, toNat_imm (by omega_using [hs])]
    apply Nat.mod_eq_of_lt
    have : (h + acc) * sv % 2 ^ 16 * s < 2 ^ 16 * 8162 := Nat.mul_lt_mul'' hq hs.2
    omega_using [this]
  have x5 : (u5.gpr .r7).toNat = h + acc := by
    rw [v5.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide), x1]
  have s6 : (u6.gpr .r6).toNat = h + acc + (h + acc) * sv % 2 ^ 16 * s := by
    rw [v6.gpr, dpVal, BitVec.toNat_add, s5, x5]
    have : (h + acc) * sv % 2 ^ 16 * s < 2 ^ 16 * 8162 := Nat.mul_lt_mul'' hq hs.2
    omega_using [digitValue, hh, hacc, r4, hs, hinv, ha, x1, q4, hq, s5, x5, this]
  obtain ⟨_, hlt, hcong⟩ := redc16_math (X := h + acc) (s := s) (sv := sv) hinv (by
    have : 3 * 2 ^ 16 ≤ s * 2 ^ 16 := Nat.mul_le_mul_right _ hs.1
    omega_using [digitValue, hh, hacc, hs, hinv, ha, x1, q4, hq, s5, x5, s6, this])
  refine k u7 k7 m7 _ hlt hcong ?_
  apply BitVec.eq_of_toNat_eq
  rw [v7.gpr, hi16, s6, toNat_imm (by omega_arith)]


open VG.Proof.Ffdh.Arm.ParameterCandidate
open VG.Proof.RsaKeyGen VG.Proof.Bignum.Arm.TrialDivision16
open VG.Impl.Ffdh.Arm.ParameterCandidate (trialDigit)

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end


/-! Simultaneous p and p-1 trial division through the shared RSA reducer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Impl.Ffdh.Arm.ParameterCandidate

theorem trialPairStep_ok (s : State) {n acc offset divisor inverse : Nat}
    (positive : 0<n) (fits : n<2^32) (count : s.gpr .r1=BitVec.ofNat 32 n)
    (readLow : InRegions (s.rd++s.wr) (State.addr (s.gpr .r0-1)) 1)
    (readHigh : 1<n → InRegions (s.rd++s.wr) (State.addr (s.gpr .r0-2)) 1)
    (accValue : s.gpr .r2=BitVec.ofNat 32 acc) (accBound : acc<2*divisor)
    (offsetValue : s.gpr .r8=BitVec.ofNat 32 offset) (offsetBound : offset<2*divisor)
    (divValue : s.gpr .r3=BitVec.ofNat 32 divisor) (divBound : 3≤divisor ∧ divisor<8162)
    (invValue : (s.gpr .r4).toNat=inverse) (invCorrect : (divisor*inverse+1)%2^16=0) :
    WP isa trialPairStep s fun t => ∃ a b, a<2*divisor ∧ b<2*divisor ∧
      a*2^16%divisor=(trialDigitNat s.mem (s.gpr .r0) n+acc)%divisor ∧
      b*2^16%divisor=(trialDigitNat s.mem (s.gpr .r0) n+offset)%divisor ∧
      t.gpr .r2=BitVec.ofNat 32 a ∧ t.gpr .r8=BitVec.ofNat 32 b ∧
      t.gpr .r0=s.gpr .r0-BitVec.ofNat 32 (min 2 n) ∧
      t.gpr .r1=BitVec.ofNat 32 (n-min 2 n) ∧ t.z=decide (n≤2) ∧
      t.mem=s.mem ∧ Rest [.r0,.r1,.r2,.r5,.r6,.r7,.r8] s t := by
  unfold trialPairStep
  refine WP.seq (WP.mono (trialDigit_ok s positive fits count readLow readHigh) ?_)
  rintro u ⟨⟨ptr,cnt,word,mem⟩,rest⟩
  have digitValue : (u.gpr .r5).toNat=trialDigitNat s.mem (s.gpr .r0) n := by
    rw [word]
    unfold trialDigitNat
    by_cases last : n=1
    · simp only [last,ite_true,show (0 : BitVec 32)=0#32 from rfl,BitVec.or_zero,Nat.add_zero,BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (by have := (s.mem (State.addr (s.gpr .r0-1))).isLt;omega_using [])
    · rw [ite_eq_right last,ite_eq_right last,trialDigit_value]
  have digitBound : trialDigitNat s.mem (s.gpr .r0) n<2^16 := by
    have lo := (s.mem (State.addr (s.gpr .r0-1))).isLt
    have hi := (s.mem (State.addr (s.gpr .r0-2))).isLt
    unfold trialDigitNat
    split <;> omega_using []
  simp only [List.cons_append,List.nil_append]
  refine wp_mov (op2_reg _ _) fun v save => ?_
  have kept : Rest [.r0,.r1,.r2,.r5,.r6,.r7,.r8] s v :=
    (rest.mono (by simp)).trans (save.rest (by simp))
  refine VG.Proof.Bignum.Arm.TrialDivision16.redc_ok
    (by rw [save.other .r5 (by decide)];exact digitValue) digitBound
    ((save.other .r2 (by decide)).trans ((rest.gpr .r2 (by simp)).trans accValue)) accBound
    (by rw [save.other .r4 (by decide),rest.gpr .r4 (by simp)];exact invValue)
    ((save.other .r3 (by decide)).trans ((rest.gpr .r3 (by simp)).trans divValue)) divBound invCorrect ?_
  intro x keepX memX a boundA congA valA
  have xdigit : (x.gpr .r7).toNat=trialDigitNat s.mem (s.gpr .r0) n := by
    rw [keepX.gpr .r7 (by simp),save.gpr]
    exact digitValue
  refine trialPairRedc_ok xdigit digitBound
    ((keepX.gpr .r8 (by simp)).trans ((save.other .r8 (by decide)).trans ((rest.gpr .r8 (by simp)).trans offsetValue))) offsetBound
    (by rw [keepX.gpr .r4 (by simp),save.other .r4 (by decide),rest.gpr .r4 (by simp)];exact invValue)
    ((keepX.gpr .r3 (by simp)).trans ((save.other .r3 (by decide)).trans ((rest.gpr .r3 (by simp)).trans divValue)))
    divBound invCorrect ?_
  intro y keepY memY b boundB congB valB
  refine wp_cmp (op2_imm (by decide)) fun t final flag => WP.block_nil ?_
  refine ⟨a,b,boundA,boundB,congA,congB,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [final.gpr,keepY.gpr .r2 (by simp),valA]
  · rw [final.gpr,valB]
  · rw [final.gpr,keepY.gpr .r0 (by simp),keepX.gpr .r0 (by simp),save.other .r0 (by decide),ptr]
  · rw [final.gpr,keepY.gpr .r1 (by simp),keepX.gpr .r1 (by simp),save.other .r1 (by decide),cnt]
  · rw [flag,keepY.gpr .r1 (by simp),keepX.gpr .r1 (by simp),save.other .r1 (by decide),cnt]
    rw [show (0 : BitVec 32)=0#32 from rfl,BitVec.sub_zero]
    change (BitVec.ofNat 32 (n-min 2 n)==(0 : BitVec 32))=_
    rw [ofNat_beq_zero (by omega_using [fits] : n-min 2 n<2^32)]
    simp only [show n-min 2 n=0 ↔ n≤2 by omega_using []]
  · rw [final.mem,memY,memX,save.mem,mem]
  · exact kept.trans ((keepX.mono (by simp)).trans ((keepY.mono (by simp)).trans (final.rest _)))


end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end


/-! Simultaneous p and p-1 trial division through the shared RSA reducer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Impl.Ffdh.Arm.ParameterCandidate

theorem trialPairLoop_ok (s : State) {n divisor inverse initialA initialB : Nat}
    (positive : 0<n) (fits : n<2^32)
    (count : s.gpr .r1=BitVec.ofNat 32 n) (read : TrialReadable s (s.gpr .r0) n)
    (accA : s.gpr .r2=BitVec.ofNat 32 initialA) (boundA : initialA<2*divisor)
    (accB : s.gpr .r8=BitVec.ofNat 32 initialB) (boundB : initialB<2*divisor)
    (divValue : s.gpr .r3=BitVec.ofNat 32 divisor) (divBound : 3≤divisor ∧ divisor<8162)
    (invValue : (s.gpr .r4).toNat=inverse) (invCorrect : (divisor*inverse+1)%2^16=0) :
    WP isa (.loop trialPairStep .ne) s fun t => ∃ a b j, a<2*divisor ∧ b<2*divisor ∧
      t.gpr .r2=BitVec.ofNat 32 a ∧ t.gpr .r8=BitVec.ofNat 32 b ∧
      a*2^(16*j)%divisor=(initialA+trialValue s.mem (s.gpr .r0) n)%divisor ∧
      b*2^(16*j)%divisor=(initialB+trialValue s.mem (s.gpr .r0) n)%divisor ∧
      t.gpr .r1=0 ∧ t.mem=s.mem ∧ Rest [.r0,.r1,.r2,.r5,.r6,.r7,.r8] s t := by
  let regs : List Reg := [.r0,.r1,.r2,.r5,.r6,.r7,.r8]
  let originalA := initialA+trialValue s.mem (s.gpr .r0) n
  let originalB := initialB+trialValue s.mem (s.gpr .r0) n
  let inv := fun k t => ∃ j a b, 0<k ∧ k<2^32 ∧ TrialReadable t (t.gpr .r0) k ∧
    t.gpr .r1=BitVec.ofNat 32 k ∧ a<2*divisor ∧ b<2*divisor ∧
    t.gpr .r2=BitVec.ofNat 32 a ∧ t.gpr .r8=BitVec.ofNat 32 b ∧
    (a+trialValue t.mem (t.gpr .r0) k)*2^(16*j)%divisor=originalA%divisor ∧
    (b+trialValue t.mem (t.gpr .r0) k)*2^(16*j)%divisor=originalB%divisor ∧
    t.mem=s.mem ∧ Rest regs s t
  refine WP.loop (M:=isa) inv ?_ n s ?_
  · intro k u h
    obtain ⟨j,a,b,kp,kfit,readable,cnt,ab,bb,av,bv,congA,congB,memory,rest⟩ := h
    refine WP.mono (trialPairStep_ok u kp kfit cnt (readable.low kp) (fun h => readable.high h)
      av ab bv bb ((rest.gpr .r3 (by simp [regs])).trans divValue) divBound
      (by rw [rest.gpr .r4 (by simp [regs])];exact invValue) invCorrect) ?_
    rintro t ⟨a',b',ab',bb',stepA,stepB,av',bv',ptr,cnt',flag,mem,keep⟩
    have congruenceA : (a'+trialValue t.mem (t.gpr .r0) (k-min 2 k))*
        2^(16*(j+1))%divisor=originalA%divisor := by
      rw [trialValue_step u.mem (u.gpr .r0) kp] at congA
      rw [mem,ptr]
      exact trialRemaining_congruence stepA congA
    have congruenceB : (b'+trialValue t.mem (t.gpr .r0) (k-min 2 k))*
        2^(16*(j+1))%divisor=originalB%divisor := by
      rw [trialValue_step u.mem (u.gpr .r0) kp] at congB
      rw [mem,ptr]
      exact trialRemaining_congruence stepB congB
    have nextRead : TrialReadable t (t.gpr .r0) (k-min 2 k) := by
      rw [ptr]
      exact readable.advance keep (Nat.min_le_right 2 k)
    have kept : Rest regs s t := rest.trans keep
    by_cases last : k≤2
    · have remZero : k-min 2 k=0 := by omega_using [last]
      left
      refine ⟨?_,a',b',j+1,ab',bb',av',bv',?_,?_,?_,mem.trans memory,kept⟩
      · change some (!t.z)=some false
        simp only [flag,last,decide_true,Bool.not_true]
      · simpa only [remZero,trialValue,Nat.add_zero] using congruenceA
      · simpa only [remZero,trialValue,Nat.add_zero] using congruenceB
      · rw [cnt',remZero];rfl
    · right
      refine ⟨?_,k-min 2 k,by omega_using [kp],j+1,a',b',by omega_using [last],by omega_using [kfit],nextRead,cnt',ab',bb',av',bv',
        congruenceA,congruenceB,mem.trans memory,kept⟩
      change some (!t.z)=some true
      simp only [flag,last,decide_false,Bool.not_false]
  · refine ⟨0,initialA,initialB,positive,fits,read,count,boundA,boundB,accA,accB,?_,?_,rfl,Rest.refl _ _⟩
    all_goals simp only [Nat.mul_zero,Nat.pow_zero,Nat.mul_one];rfl

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Simultaneous p and p-1 trial division through the shared RSA reducer. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/PairTrialFlag.lean`, which only this module imported.
section

/-! Simultaneous p and p-1 trial division through the shared RSA reducer. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Impl.Ffdh.Arm.ParameterCandidate

theorem trialPairFlag_ok (s : State) :
    WP isa trialPairFlag s fun t =>
      t.z=((s.gpr .r2==0 || s.gpr .r2==s.gpr .r3) || (s.gpr .r8==0 || s.gpr .r8==s.gpr .r3)) ∧
      t.mem=s.mem ∧ Rest [.r2] s t := by
  unfold trialPairFlag
  rw [WP.seq_iff]
  refine WP.mono (trialFlag_ok s) ?_
  rintro u ⟨flag,memory,rest⟩
  cases first : (s.gpr .r2==0 || s.gpr .r2==s.gpr .r3) with
  | true =>
    refine WP.ite true (by change some u.z=some true;rw [flag,first]) ?_ (by intro h;cases h)
    intro _
    refine WP.block_nil ⟨?_,memory,rest.mono (by simp)⟩
    rw [flag,first];rfl
  | false =>
    refine WP.ite false (by change some u.z=some false;rw [flag,first]) (by intro h;cases h) ?_
    intro _
    refine WP.seq (wp_mov (op2_reg _ _) fun v upd => WP.block_nil ?_)
    refine WP.mono (trialFlag_ok v) ?_
    rintro t ⟨last,memT,restT⟩
    refine ⟨?_,memT.trans (upd.mem.trans memory),
      (rest.mono (by simp)).trans ((upd.rest (by simp)).trans (restT.mono (by simp)))⟩
    rw [last,upd.gpr,rest.gpr .r8 (by simp),upd.other .r3 (by decide),rest.gpr .r3 (by simp)]
    rfl


end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Impl.Ffdh.Arm.ParameterCandidate

private theorem reducedFlag {acc value divisor j : Nat}
    (odd : divisor%2=1) (bound : acc<2*divisor) (db : divisor<8162)
    (congruence : acc*2^(16*j)%divisor=value%divisor) :
    ((BitVec.ofNat 32 acc==0)||(BitVec.ofNat 32 acc==BitVec.ofNat 32 divisor))=decide (value%divisor=0) := by
  rw [ofNat_beq_zero (by omega_using [bound, db] : acc<2^32),ofNat_beq_eq (by omega_using [bound, db] : acc<2^32) (by omega_using [db] : divisor<2^32),
    ←Bool.decide_or]
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using (trialDigit_divides odd bound congruence).symm

theorem trialPair_ok (s : State) (dst : BitVec 32) {n prime : Nat}
    (positive : 0<n) (fits : n<2^32) (bufferFits : dst.toNat+n≤2^32)
    (primeBound : prime<1024)
    (divisor : s.gpr .r7=BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry prime))
    (readOut : InRegions (s.rd++s.wr) (State.addr (s.sp+4)) 4)
    (readWidth : InRegions (s.rd++s.wr) (State.addr (s.sp+12)) 4)
    (out : s.mem.readW (State.addr (s.sp+4)) 32=dst)
    (width : s.mem.readW (State.addr (s.sp+12)) 32=BitVec.ofNat 32 n)
    (read : TrialReadable s (dst+BitVec.ofNat 32 n) n) :
    WP isa trialPair s fun t =>
      t.z=(decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)%VG.Impl.RsaKeyGen.tabEntry prime=0) ||
        decide ((VG.Impl.RsaKeyGen.tabEntry prime-1+Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n))%
          VG.Impl.RsaKeyGen.tabEntry prime=0)) ∧ t.mem=s.mem ∧
      Rest [.r0,.r1,.r2,.r3,.r4,.r5,.r6,.r7,.r8] s t := by
  have facts := VG.Proof.RsaKeyGen.tabEntry_facts primeBound
  unfold trialPair
  refine WP.seq (WP.mono (trialStart_ok s dst n readOut readWidth out width) ?_)
  rintro u ⟨⟨ptr,cnt,zero,div,inverse,mem⟩,rest⟩
  unfold trialPairInit
  refine WP.seq (wp_dp (op2_imm (by decide)) fun w init => WP.block_nil ?_)
  have kept : Rest [.r0,.r1,.r2,.r3,.r4,.r5,.r6,.r7,.r8] s w :=
    (rest.mono (by simp)).trans (init.rest (by simp))
  have ptrW : w.gpr .r0=dst+BitVec.ofNat 32 n := (init.other .r0 (by decide)).trans ptr
  have cntW : w.gpr .r1=BitVec.ofNat 32 n := (init.other .r1 (by decide)).trans cnt
  have accA : w.gpr .r2=BitVec.ofNat 32 0 := (init.other .r2 (by decide)).trans zero
  have accB : w.gpr .r8=BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry prime-1) := by
    rw [init.gpr,dpVal,div,divisor]
    exact BitVec.ofNat_sub_ofNat_of_le _ 1 (by decide) (by omega_using [facts])
  have divW : w.gpr .r3=BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry prime) :=
    (init.other .r3 (by decide)).trans (div.trans divisor)
  have memW : w.mem=s.mem := init.mem.trans mem
  have readable : TrialReadable w (w.gpr .r0) n := by
    rw [ptrW]
    intro i hi
    rw [kept.rd,kept.wr]
    exact read i hi
  have inv : (w.gpr .r4).toNat=(VG.Proof.RsaKeyGen.ninv (BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry prime))).toNat := by
    rw [init.other .r4 (by decide),inverse,divisor]
  refine WP.seq (WP.mono (trialPairLoop_ok w positive fits cntW readable accA (by omega_using [facts]) accB (by omega_using [facts])
    divW facts.2 inv (VG.Proof.RsaKeyGen.ninv_tab primeBound)) ?_)
  rintro v ⟨a,b,j,ab,bb,av,bv,congA,congB,_,memory,keep⟩
  have inputValue : trialValue w.mem (w.gpr .r0) n=Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) := by
    rw [memW,ptrW,trialValue_octets,trialBytes_at _ _ fits bufferFits]
  rw [inputValue,Nat.zero_add] at congA
  rw [inputValue] at congB
  have divV : v.gpr .r3=BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry prime) :=
    (keep.gpr .r3 (by simp)).trans divW
  refine WP.mono (trialPairFlag_ok v) ?_
  rintro t ⟨flag,memT,restT⟩
  refine ⟨?_,memT.trans (memory.trans memW),kept.trans ((keep.mono (by simp)).trans (restT.mono (by simp)))⟩
  rw [flag,av,bv,divV,reducedFlag facts.1 ab facts.2.2 congA,reducedFlag facts.1 bb facts.2.2 congB]


end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end


/-! Each prime rejects p or p-1 before the sieve advances to its next entry. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm
open VG.Impl.Ffdh.Arm.ParameterCandidate (trialCount)

theorem pairTrials_ok {s : State} {dst base : BitVec 32} {n value i : Nat}
    (ctx : SieveContext dst base n s) (more : i<trialCount n)
    (cursor : s.gpr .r10=base+BitVec.ofNat 32 (Proof.Rsa.Mont.arrAt ((n+7)/8) 34+4*i))
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)=value) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.pairTrials s fun t =>
      t.z=(value%VG.Impl.RsaKeyGen.tabEntry i==0 ||
        (VG.Impl.RsaKeyGen.tabEntry i-1+value)%VG.Impl.RsaKeyGen.tabEntry i==0) ∧
      t.mem=s.mem ∧ Rest [.r0,.r1,.r2,.r3,.r4,.r5,.r6,.r7,.r8] s t := by
  have bound := trialCount_bound n
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.pairTrials
  rw [WP.seq_iff]
  refine WP.mono (pairEntry_ok ctx more cursor) ?_
  rintro u ⟨⟨prime,memU⟩,restU⟩
  have ctxU := ctx.after_memory memU restU
  refine WP.mono (trialPair_ok u dst ctxU.read.positive ctxU.read.countFits ctxU.read.bufferFits
    (by omega_using [more, bound] : i<1024) prime (ctxU.read.frame.read (by decide)) (ctxU.read.frame.read (by decide))
    ctxU.read.out ctxU.read.width ctxU.read.readable) ?_
  rintro t ⟨flag,memory,rest⟩
  refine ⟨?_,memory.trans memU,(restU.mono (by simp)).trans rest⟩
  rwa [memU,number,←Bool.beq_eq_decide_eq,←Bool.beq_eq_decide_eq] at flag

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! One compact-table sieve iteration uses RSA's verified native reducer. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/PairControl.lean`, which only this module imported.
section

/-! Advance the shared prime cursor and bounded count once for each pair of trials. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG.Impl.Ffdh.Arm.ParameterCandidate (trialCount)
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem pairAdvanceCount_ok {s : State} {count : Nat} (positive : 0 < count) (bound : count ≤ 1024)
    (saved : s.gpr .r11 = BitVec.ofNat 32 count) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.pairAdvance ++ VG.Impl.Ffdh.Arm.ParameterCandidate.sieveCount)) s fun t =>
      (t.gpr .r10 = s.gpr .r10 + 4 ∧ t.gpr .r11 = BitVec.ofNat 32 (count - 1) ∧
        t.z = decide (count = 1) ∧ t.mem = s.mem) ∧ Rest [.r10, .r11] s t := by
  have subtract : BitVec.ofNat 32 count - (1 : BitVec 32) = BitVec.ofNat 32 (count - 1) :=
    BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) positive
  have zero : (BitVec.ofNat 32 (count - 1) == (0 : BitVec 32)) = decide (count = 1) := by
    rw [ofNat_beq_zero (by omega : count - 1 < 2 ^ 32)]
    exact decide_eq_decide.mpr (by omega)
  refine withRest_all [.r10, .r11] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.pairAdvance VG.Impl.Ffdh.Arm.ParameterCandidate.sieveCount
  ffrun [List.cons_append, List.nil_append, saved, subtract, zero]

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG.Impl.Ffdh.Arm.ParameterCandidate (trialCount)
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm

theorem pairActiveStep_ok {s0 s : State} {dst base : BitVec 32} {n value i : Nat}
    (inv : PairInv s0 dst base n value i s) (more : i < (trialCount n)) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.pairActiveStep s fun t =>
      PairInv s0 dst base n value (i + 1) t ∧ t.z = decide (i + 1 = (trialCount n)) := by
  have limitBound := trialCount_bound n
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.pairActiveStep VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (pairTrials_ok inv.context more inv.cursor inv.candidate) ?_)
  rintro v ⟨divides,memV,restV⟩
  have ctxV := inv.context.after_memory memV restV
  have old : v.mem.readW (State.addr (v.sp+64#32)) 32 = if pairAny value i then 1 else 0 := by
    rw [memV,restV.sp]
    exact inv.bad
  refine WP.seq (WP.mono (sieveFlag_ok ctxV.read.frame.space old) ?_)
  rintro a ⟨badA,changedA,restA⟩
  have ctxA := ctxV.after_frame changedA restA
  have through : Rest sieveRegs s a :=
    (restV.mono (by simp [sieveRegs])).trans (restA.mono (by simp [sieveRegs]))
  have countA : a.gpr .r11=BitVec.ofNat 32 (trialCount n-i) := by
    rw [restA.gpr .r11 (by simp),restV.gpr .r11 (by simp)]
    exact inv.count
  refine WP.seq (WP.mono (pairAdvanceCount_ok (by omega_using [more] : 0<trialCount n-i) (by omega_using [limitBound]) countA) ?_)
  rintro t ⟨⟨cursorT,countT,zeroT,memT⟩,restT⟩
  refine WP.block_nil ⟨⟨ctxA.after_memory memT restT,by omega_using [more],?_,?_,?_,?_,?_,
    (inv.rest.trans through).trans (restT.mono (by simp [sieveRegs]))⟩,?_⟩
  · rw [cursorT,restA.gpr .r10 (by simp),restV.gpr .r10 (by simp),inv.cursor]
    change (base+BitVec.ofNat 32 (Proof.Rsa.Mont.arrAt ((n+7)/8) 34+4*i))+BitVec.ofNat 32 4 = _
    rw [BitVec.add_assoc,BitVec.ofNat_add_ofNat]
    have offset : Proof.Rsa.Mont.arrAt ((n+7)/8) 34+4*i+4 =
        Proof.Rsa.Mont.arrAt ((n+7)/8) 34+4*(i+1) := by omega_using []
    rw [offset]
  · simpa only [show trialCount n-i-1=trialCount n-(i+1) by omega_using []] using countT
  · rw [divides,←pairAny_succ] at badA
    rw [memT,restT.sp]
    exact badA
  · rw [memT,ctxV.bytes_after changedA,memV]
    exact inv.candidate
  · have changed : Frame [sieveLocal s0.sp] s.mem t.mem := by
      rw [memT]
      simpa only [restV.sp,inv.rest.sp,memV] using changedA
    exact inv.changed.trans changed
  · rw [zeroT]
    exact decide_eq_decide.mpr (by omega_using [])

theorem pairStep_ok {s0 s : State} {dst base : BitVec 32} {n value i : Nat}
    (inv : PairInv s0 dst base n value i s) (more : i < (trialCount n)) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.pairStep s fun t =>
      PairInv s0 dst base n value (pairNext n value i) t ∧ t.z = decide (pairNext n value i = trialCount n) := by
  have limitBound := trialCount_bound n
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.pairStep
  refine WP.seq (WP.mono (sieveFinish_ok inv.context.read.frame.space inv.bad) ?_)
  rintro u ⟨⟨flag, memory⟩, rest⟩
  have invU : PairInv s0 dst base n value i u := by
    refine ⟨inv.context.after_memory memory rest, inv.index, ?_, ?_, ?_, ?_, ?_,
      inv.rest.trans (rest.mono (by simp [sieveRegs]))⟩
    · rw [rest.gpr .r10 (by simp)]; exact inv.cursor
    · rw [rest.gpr .r11 (by simp)]; exact inv.count
    · rw [memory, rest.sp]; exact inv.bad
    · rw [memory]; exact inv.candidate
    · rw [memory]; exact inv.changed
  cases bad : pairAny value i with
  | false =>
    have zero : u.z = true := by simpa only [bad, Bool.not_false] using flag
    refine WP.ite true (by change some u.z = some true; rw [zero]) ?_ (by intro h; cases h)
    intro _
    simpa only [pairNext, bad, Bool.false_eq_true, ite_false] using pairActiveStep_ok invU more
  | true =>
    have zero : u.z = false := by simpa only [bad, Bool.not_true] using flag
    refine WP.ite false (by change some u.z = some false; rw [zero]) (by intro h; cases h) ?_
    intro _
    refine WP.mono (sieveSkip_ok u) ?_
    rintro t ⟨⟨cursor, count, last, mem⟩, restT⟩
    simp only [pairNext, bad, ite_true, decide_true]
    have totalBad := pairAny_mono inv.index bad
    refine ⟨⟨invU.context.after_memory mem restT, Nat.le_refl _, ?_, ?_, ?_, ?_, ?_,
      invU.rest.trans (restT.mono (by simp [sieveRegs]))⟩, last⟩
    · rw [cursor, invU.cursor, invU.count, BitVec.shiftLeft_eq_mul_twoPow]
      change (base + BitVec.ofNat 32 (Proof.Rsa.Mont.arrAt ((n+7)/8) 34+4*i)) +
        BitVec.ofNat 32 (trialCount n-i)*BitVec.ofNat 32 4 = _
      rw [BitVec.ofNat_mul_ofNat,BitVec.add_assoc,BitVec.ofNat_add_ofNat]
      have offset : Proof.Rsa.Mont.arrAt ((n+7)/8) 34+4*i+(trialCount n-i)*4 =
          Proof.Rsa.Mont.arrAt ((n+7)/8) 34+4*trialCount n := by
        have := inv.index
        omega_using [more]
      rw [offset]
    · rw [Nat.sub_self]
      exact count.trans (by decide)
    · rw [mem, restT.sp, invU.bad, bad, totalBad]
    · rw [mem]; exact invU.candidate
    · rw [mem]; exact invU.changed

end VG.Proof.Ffdh.Arm.ParameterCandidate
