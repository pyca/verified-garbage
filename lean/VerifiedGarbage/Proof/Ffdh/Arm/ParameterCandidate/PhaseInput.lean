module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessState
public import VerifiedGarbage.Impl.Ffdh.Arm.Arithmetic
public import VerifiedGarbage.Proof.Bignum.Arm.PcStack
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyFrame
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyOps
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Bignum.Arm.CallStack
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Draw
import VerifiedGarbage.Proof.Ffdh.Arm.DomainSharedPrepareAt
import VerifiedGarbage.Impl.Bignum.Arm.R2
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
public import VerifiedGarbage.Impl.Ffdh.Arm.CandidatePrepare
public import VerifiedGarbage.Proof.Ffdh.Arm.Prepare
import VerifiedGarbage.Proof.Ffdh.Arm.NormalizedPrepare
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpDoubling
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Ffdh.Arm.ParameterCandidate.MontStride`, which this module and modules that import it used -/

section

/-! The shared compact round's stride is a complete u64 header word. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Rsa.Mont (numAt)

def strideMemory (m : Mem) (base : BitVec 32) (w : Nat) : Mem :=
  (m.writeW (off (State.addr base) 224) (BitVec.ofNat 32 (8 * (w + 2)))).writeW
    (off (State.addr base) 228) (0#32)

theorem keyStride_words {s : State} {base : BitVec 32} {capacity w : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (ptr : s.gpr .r0 = base) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.keyStride) s fun t =>
      t.mem = strideMemory s.mem base w ∧ Rest [.r1] s t := by
  have fit := ready.arrayFit (j := 0) (by decide)
  have write224 : InRegions s.wr (State.addr (base + 224#32)) 4 := by
    rw [VG.Arm.addr_add (by have := workspace.nowrap; simp only [Proof.Rsa.Mont.arrAt,
      Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] at fit; omega_using [this, fit])]
    exact workspace.write (by simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
      Nat.zero_mul, Nat.add_zero] at fit; omega_using [fit])
  have write228 : InRegions s.wr (State.addr (base + 228#32)) 4 := by
    rw [VG.Arm.addr_add (by have := workspace.nowrap; simp only [Proof.Rsa.Mont.arrAt,
      Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] at fit; omega_using [this, fit])]
    exact workspace.write (by simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
      Nat.zero_mul, Nat.add_zero] at fit; omega_using [fit])
  refine withRest_all [.r1] ?_ (by rfl) (by rfl)
  have stride := ready.r7
  rw [keyView_stride] at stride
  have addr224 : State.addr (base + 224#32) = off (State.addr base) 224 :=
    VG.Arm.addr_add (by have := workspace.nowrap; simp only [Proof.Rsa.Mont.arrAt,
      Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] at fit; omega_using [this, fit])
  have addr228 : State.addr (base + 228#32) = off (State.addr base) 228 :=
    VG.Arm.addr_add (by have := workspace.nowrap; simp only [Proof.Rsa.Mont.arrAt,
      Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] at fit; omega_using [this, fit])
  change s.gpr .r7 = _ at stride
  rw [addr224] at write224
  rw [addr228] at write228
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.keyStride strideMemory
  ffrun [ptr, stride, write224, write228, addr224, addr228,
    show (0 : BitVec 32) = 0#32 from rfl]

theorem strideMemory_write64 (m : Mem) (base : BitVec 32) {w : Nat} (bound : w ≤ 1024) :
    strideMemory m base w = m.writeW (off (State.addr base) 224) (BitVec.ofNat 64 (8 * (w + 2))) := by
  unfold strideMemory
  have offset : off (State.addr base) 228 = off (State.addr base) 224 + BitVec.ofNat 64 4 := by
    rw [Offset.add_add]
  rw [offset, ← VG.Proof.Rc2.Word32.write64_pair]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
  rw [Nat.mod_eq_of_lt (by omega_using [bound] : 8 * (w + 2) < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega_using [bound] : 8 * (w + 2) < 2 ^ 64)]

theorem strideMemory_frame (m : Mem) (base : BitVec 32) {w : Nat} (bound : w ≤ 1024) :
    Frame [⟨off (State.addr base) 224, 8⟩] m (strideMemory m base w) := by
  rw [strideMemory_write64 m base bound]
  exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)

theorem keyStride_ok {s : State} {base : BitVec 32} {capacity w : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (data : MontData base capacity w s.mem) (ptr : s.gpr .r0 = base) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.keyStride) s fun t =>
      KeyReady base capacity w t ∧ MontData base capacity w t.mem ∧
      t.mem.readW (off (State.addr base) 224) 64 = BitVec.ofNat 64 (8 * (w + 2)) ∧
      (∀ j, j < 35 → numAt t.mem (State.addr base) w j = numAt s.mem (State.addr base) w j) ∧
      Frame [⟨off (State.addr base) 224, 8⟩] s.mem t.mem ∧ Rest [.r1] s t := by
  have wBound : w ≤ 1024 := by have := ready.wle; omega_using [this]
  refine WP.mono (keyStride_words workspace ready ptr) ?_
  rintro t ⟨mem, rest⟩
  have frame : Frame [⟨off (State.addr base) 224, 8⟩] s.mem t.mem := by
    rw [mem]
    exact strideMemory_frame s.mem base wBound
  have values (j : Nat) (jBound : j < 35) : numAt t.mem (State.addr base) w j = numAt s.mem (State.addr base) w j := by
    unfold numAt
    apply congrArg BitVec.toNat
    refine frame.read (r := ⟨off (State.addr base) (Proof.Rsa.Mont.arrAt w j), 8 * w⟩)
      (Region.contains_self _ _) ?_ (by omega_using [wBound])
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    have scale := Nat.mul_le_mul_right (8 * (w + 2)) (show j ≤ 35 by omega_using [jBound])
    apply Offset.disjoint _ (.inr ?_) (by simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using [wBound, scale]) (by decide)
    simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
    omega_using []
  have dataT := data.after_value frame (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact (Offset.disjoint_base _ (by decide : 128 ≤ 224) (by decide : 224 + 8 ≤ 2 ^ 64)).symm) (values 0 (by decide))
  refine ⟨ready.rest rest (by decide) (by decide) (by decide), dataT.1, ?_, values, frame, rest⟩
  rw [mem, strideMemory_write64 s.mem base wBound, Mem.readW_writeW_self64]

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.CandidatePrepare`, which this module and modules that import it used -/

section

/-! The public byte count selects normalized setup only where the shaped
candidate guarantees a nonzero highest radix word. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm

theorem candidatePrepareChoice_ok (s : State) {base src : BitVec 32} {len k : Nat}
    (h : PrepareInput base src len k s)
    (normalized : k % 8 = 1 ∨ 2 ^ (64 * (Spec.Rsa.modulusWords k - 1)) ≤
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) :
    WP isa (.block VG.Impl.Ffdh.Arm.CandidatePrepare.choose) s fun v =>
      PrepareInput base src len k v ∧
      (k % 8 = 1 ∨ 2 ^ (64 * (Spec.Rsa.modulusWords k - 1)) ≤
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt v.mem (State.addr src) k)) ∧
      v.z = decide (k % 8 = 1) ∧ v.mem = s.mem ∧ Rest [.r1] s v := by
  simp only [VG.Impl.Ffdh.Arm.CandidatePrepare.choose]
  refine wp_dp (op2_imm (by decide)) fun u hu => ?_
  refine wp_cmp (op2_imm (by decide)) fun v hv zero => WP.block_nil ?_
  have rest : Rest [.r1] s v := (hu.rest (by simp)).trans ((hv.rest []).mono (by simp))
  have memory : v.mem = s.mem := hv.mem.trans hu.mem
  have input : PrepareInput base src len k v := by
    refine ⟨h.workspace.congr rest.wr, ?_, ?_, ?_, h.minLength,h.maxLength,h.space,
      h.sourceFits,?_,h.separate,?_,?_⟩
    · have f : Frame [⟨State.addr base,8*len⟩] s.mem v.mem := by rw [memory];exact Frame.refl _ _
      simpa only [memory,rest.sp] using h.stack.after_workspace f rest
    · rw [rest.gpr .r0 (by simp)];exact h.ptr
    · rw [rest.gpr .r6 (by simp)];exact h.count
    · rw [rest.rd,rest.wr];exact h.readable
    · rw [memory];exact h.large
    · rw [memory];exact h.odd
  have branch : v.z = decide (k % 8 = 1) := by
    rw [zero, hu.gpr, dpVal, h.count]
    have mask : (BitVec.ofNat 32 k &&& (7 : BitVec 32)).toNat = k % 8 := by
      rw [BitVec.toNat_and,BitVec.toNat_ofNat]
      change (k % 2^32) &&& (2^3-1) = _
      rw [Nat.and_two_pow_sub_one_eq_mod]
      omega_using []
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro eq
      have emask : (BitVec.ofNat 32 k &&& (7 : BitVec 32)) = 1 := by
        calc
          _ = ((BitVec.ofNat 32 k &&& (7 : BitVec 32)) - 1) + 1 := (BitVec.sub_add_cancel _ _).symm
          _ = 1 := by rw [eq]; rfl
      have e := congrArg BitVec.toNat emask
      rw [mask] at e
      exact e
    · intro eq
      have emask : (BitVec.ofNat 32 k &&& (7 : BitVec 32)) = 1 :=
        BitVec.eq_of_toNat_eq (by rw [mask]; exact eq)
      rw [emask]; rfl
  exact ⟨input,by rw [memory];exact normalized,branch,memory,rest⟩

theorem candidatePrepare_ok (s : State) {base src : BitVec 32} {len k : Nat}
    {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len (Spec.Rsa.modulusWords k) P regions)
    (h : PrepareInput base src len k s) (hp : P s)
    (normalized : k % 8 = 1 ∨ 2 ^ (64 * (Spec.Rsa.modulusWords k - 1)) ≤
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) :
    WP isa (VG.Impl.Ffdh.Arm.CandidatePrepare.code K.op) s fun t =>
      ArithmeticReady base len (Spec.Rsa.modulusWords k) t ∧
      numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 0 =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 4 =
        2 ^ (128 * Spec.Rsa.modulusWords k) % Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      P t ∧ Frame regions s.mem t.mem ∧
      Rest VG.Proof.Bignum.Arm.roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.CandidatePrepare.code, WP.seq_iff]
  refine WP.mono (candidatePrepareChoice_ok s h normalized) ?_
  rintro v ⟨input,_,branch,memory,rest⟩
  have hv : P v := K.stable (by rw [memory]; exact Frame.refl _ _) (rest.mono (by simp [roundClobbers])) hp
  have finish (t : State) (ready : ArithmeticReady base len (Spec.Rsa.modulusWords k) t)
      (n : Proof.Rsa.Mont.numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 0 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt v.mem (State.addr src) k))
      (r2 : Proof.Rsa.Mont.numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 4 = 2^(128*Spec.Rsa.modulusWords k) % Spec.Rsa.os2ip (Spec.Rsa.bytesAt v.mem (State.addr src) k))
      (pt : P t) (frame : Frame regions v.mem t.mem) (rt : Rest roundClobbers v t) :=
    And.intro ready (And.intro (memory ▸ n) (And.intro (memory ▸ r2) (And.intro pt
      (And.intro (by simpa only [memory] using frame) ((rest.mono (by simp [roundClobbers])).trans rt)))))
  refine WP.ite v.z rfl ?_ ?_
  · intro _
    refine WP.mono (sharedPrepare_ok v K (TwoExp.inlineDoubling _ _ _ P regions K.workspace K.stable) input hv) ?_
    rintro t ⟨ready,n,r2,pt,frame,rt⟩
    exact finish t ready n r2 pt frame rt
  · intro selected
    have notBoundary : k % 8 ≠ 1 := by
      rw [branch] at selected
      simpa only [decide_eq_false_iff_not] using selected
    have bound := normalized.resolve_left notBoundary
    refine WP.mono (normalizedPrepare_ok v K (TwoExp.inlineDoubling _ _ _ P regions K.workspace K.stable) input hv (by rw [memory];exact bound)) ?_
    rintro t ⟨ready,n,r2,pt,frame,rt⟩
    exact finish t ready n r2 pt frame rt

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.MontPrepare`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.MontArrays`, which only this module used -/

section

/-! Prepare the compact Miller–Rabin constants through RSA's existing
array routines. Clearing native padding makes both views agree exactly. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.Keys (num Keep opRegs)
open VG.Proof.Rsa.Mont (numAt)

private theorem subtract_exact {a b r modulus borrow : Nat} (le : b ≤ a) (small : r < modulus)
    (value : r + b = a + modulus * borrow) (bit : borrow ≤ 1) : r = a - b := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp bit with zero | one
  · rw [zero, Nat.mul_zero, Nat.add_zero] at value
    omega_using [value]
  · rw [one, Nat.mul_one] at value
    omega_using [le, small, value]

theorem montKeyArrays_ok {s : State} {base : BitVec 32} {capacity w : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (data : MontData base capacity w s.mem)
    (rSmall : numAt s.mem (State.addr base) w 1 ≤ numAt s.mem (State.addr base) w 0) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.montKeyArrays s fun t =>
      KeyReady base capacity w t ∧ MontData base capacity w t.mem ∧
      Keep (base + 96#32) (2 * w + 2) [0, 1, 9, 10] [] s.mem t.mem ∧
      num t.mem (base + 96#32) (2 * w + 2) 0 = numAt s.mem (State.addr base) w 0 ∧
      num t.mem (base + 96#32) (2 * w + 2) 9 = numAt s.mem (State.addr base) w 1 ∧
      numAt t.mem (State.addr base) w 9 = numAt s.mem (State.addr base) w 1 ∧
      numAt t.mem (State.addr base) w 10 =
        numAt s.mem (State.addr base) w 0 - numAt s.mem (State.addr base) w 1 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Rest opRegs s t := by
  have fits := ready.baseShiftFits workspace
  have nBound := numAt_lt s.mem (State.addr base) w 0
  have rBound : numAt s.mem (State.addr base) w 1 < 2 ^ (64 * w) := Nat.lt_of_le_of_lt rSmall nBound
  simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.montKeyArrays, VG.Impl.Ffdh.Arm.ParameterCandidate.seqs ]
  refine WP.seq (WP.mono (keyClrTop_ok workspace ready (j := 0) (by decide)) ?_)
  rintro s1 ⟨ready1, keep1, n1, rest1⟩
  have workspace1 := workspace.congr rest1.wr
  have r1 := key_keep_number workspace ready (j := 1) (by decide) (by simp) keep1
  refine WP.seq (WP.mono (keyClrTop_ok workspace1 ready1 (j := 1) (by decide)) ?_)
  rintro s2 ⟨ready2, keep2, r2, rest2⟩
  rw [r1] at r2
  have workspace2 := workspace1.congr rest2.wr
  have n2 := (keep2.num (j := 0) (by simp) (by simp) (ready1.fit64 (by decide))).trans n1
  refine WP.seq (WP.mono (keyCopy_ok workspace2 ready2 (o := 9) (a := 1) (by decide) (by decide) (by decide)) ?_)
  rintro s3 ⟨ready3, keep3, r3, rest3⟩
  rw [r2] at r3
  have workspace3 := workspace2.congr rest3.wr
  have n3 := (keep3.num (j := 0) (by simp) (by simp) (ready2.fit64 (by decide))).trans n2
  refine WP.seq (WP.mono (keySub3_ok workspace3 ready3 (o := 10) (a := 0) (b := 9)
    (by decide) (by decide) (by decide) (by decide) (by decide)) ?_)
  rintro t ⟨ready4, keep4, difference, borrow, rest4⟩
  rw [n3, r3] at difference
  have exactDifference := subtract_exact rSmall
    (val32_lt t.mem (State.addr (base + 96#32)) (VG.Proof.Rsa.Arm.Keys.arr (2 * w + 2) 10) (2 * w + 2))
    difference borrow
  change num t.mem (base + 96#32) (2 * w + 2) 10 = _ at exactDifference
  have n4 := (keep4.num (j := 0) (by simp) (by simp) (ready3.fit64 (by decide))).trans n3
  have r4 := (keep4.num (j := 9) (by simp) (by simp) (ready3.fit64 (by decide))).trans r3
  have number0 : numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 := by
    rw [keyView_number_low t.mem base w 0 fits (by rw [n4]; exact nBound), n4]
  have number9 : numAt t.mem (State.addr base) w 9 = numAt s.mem (State.addr base) w 1 := by
    rw [keyView_number_low t.mem base w 9 fits (by rw [r4]; exact rBound), r4]
  have number10 : numAt t.mem (State.addr base) w 10 =
      numAt s.mem (State.addr base) w 0 - numAt s.mem (State.addr base) w 1 := by
    rw [keyView_number_low t.mem base w 10 fits (by rw [exactDifference]; omega_using [nBound]), exactDifference]
  have keep : Keep (base + 96#32) (2 * w + 2) [0, 1, 9, 10] [] s.mem t.mem :=
    ((keep1.mono (by simp)).trans (keep2.mono (by simp))).trans
      ((keep3.mono (by simp)).trans (keep4.mono (by simp)))
  have frame := key_keep_frame workspace ready (by simp) keep
  have data4 := data.after_value frame (keyArrayRegions.header workspace ready (by simp)) number0
  exact WP.block_nil ⟨ready4, data4.1, keep, n4, r4, number9, number10, number0,
    rest1.trans (rest2.trans (rest3.trans rest4))⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Complete native Montgomery preparation for each safe-prime phase,
composing the same arithmetic and array routines that RSA uses. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/MontKeySetup.lean`, which only this module imported.
section

/-! Compose the native RSA array view and compact-round header constants. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.Keys (num)
open VG.Proof.Rsa.Mont (numAt)

theorem montKeySetup_ok {s : State} {base : BitVec 32} {capacity k : Nat}
    (workspace : Workspace s base (8 * capacity))
    (data : MontData base capacity (Spec.Rsa.modulusWords k) s.mem)
    (minLength : 64 ≤ k) (maxLength : k ≤ 1024) (space : Spec.Rsa.scratchWords k ≤ capacity)
    (readBase : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (saved : s.mem.readW (State.addr s.sp) 32 = base)
    (rSmall : numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) 1 ≤
      numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) 0) :
    WP isa (.seq (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.keyContext ++
      VG.Impl.Ffdh.Arm.ParameterCandidate.keyStride)) VG.Impl.Ffdh.Arm.ParameterCandidate.montKeyArrays)
      s fun t =>
      KeyReady base capacity (Spec.Rsa.modulusWords k) t ∧
      MontData base capacity (Spec.Rsa.modulusWords k) t.mem ∧
      num t.mem (base + 96#32) (2 * Spec.Rsa.modulusWords k + 2) 0 =
        numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) 0 ∧
      numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 9 =
        numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) 1 ∧
      numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 10 =
        numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) 0 -
          numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) 1 ∧
      numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 0 =
        numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) 0 ∧
      t.mem.readW (off (State.addr base) 224) 64 = BitVec.ofNat 64 (8 * (Spec.Rsa.modulusWords k + 2)) ∧
      (∀ j, j < 30 → j ∉ [0, 1, 9, 10] → numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) j =
        numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) j) ∧
      Frame [⟨State.addr base, 8 * capacity⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff, WP.block_append_iff]
  refine WP.mono (keyContext_ready s workspace data minLength maxLength space readBase saved) ?_
  rintro u ⟨readyU, ptrU, memU, restU⟩
  have dataU : MontData base capacity (Spec.Rsa.modulusWords k) u.mem := memU ▸ data
  have workspaceU := workspace.congr restU.wr
  refine WP.mono (keyStride_ok workspaceU readyU dataU ptrU) ?_
  rintro v ⟨readyV, dataV, strideV, valuesV, frameV, restV⟩
  have frameV' : Frame [⟨State.addr base, 8 * capacity⟩] s.mem v.mem := by
    rw [← memU]
    refine frameV.sub ?_
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    refine ⟨⟨State.addr base, 8 * capacity⟩, by simp, Offset.sub_base _ ?_⟩
    have fit := readyU.arrayFit (j := 0) (by decide)
    simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] at fit
    omega
  have valueV (j : Nat) (bound : j < 35) : numAt v.mem (State.addr base) (Spec.Rsa.modulusWords k) j =
      numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) j := by rw [valuesV j bound, memU]
  refine WP.mono (montKeyArrays_ok (workspaceU.congr restV.wr) readyV dataV (by
    rw [valueV 1 (by decide), valueV 0 (by decide)]; exact rSmall)) ?_
  rintro t ⟨readyT, dataT, keepT, nT, _, rT, minusT, numberT, restT⟩
  rw [valueV 0 (by decide)] at nT numberT minusT
  rw [valueV 1 (by decide)] at rT minusT
  have frameT := key_keep_workspace (workspaceU.congr restV.wr) readyV (by simp) keepT
  have strideT := key_keep_header (workspaceU.congr restV.wr) readyV (by simp) (by decide : 224 + 8 ≤ 256) keepT
  refine ⟨readyT, dataT, nT, rT, minusT, numberT, strideT.trans strideV, ?_, frameV'.trans frameT,
    (restU.mono (by simp [roundClobbers])).trans ((restV.mono (by simp [roundClobbers])).trans
      (restT.mono (by simp [roundClobbers, VG.Proof.Rsa.Arm.Keys.opRegs])))⟩
  intro j bound outside
  have unchanged : ∀ a ∈ [0, 1, 9, 10], a ≠ j := by
    intro a member same
    exact outside (same ▸ member)
  rw [key_keep_number (workspaceU.congr restV.wr) readyV bound unchanged keepT, valueV j (by omega)]

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/MontOne.lean`, which only this module imported.
section

/-! Reuse RSA's Montgomery encoding proof to produce the compact round's
representation of one. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt arrAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem montOne_ok (b : MontBackend) {s : State} {base : BitVec 32} {capacity w n : Nat}
    (ready : ArithmeticReady base capacity w s) (calls : CallStack base capacity s)
    (modulus : numAt s.mem (State.addr base) w 0 = n) (odd : n % 2 = 1)
    (r2 : numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % n) :
    WP isa (.seq (VG.Impl.Bignum.Arm.smallConst 1 1) (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul 1 1 4)) s fun t =>
      ArithmeticReady base capacity w t ∧ CallStack base capacity t ∧ numAt t.mem (State.addr base) w 0 = n ∧
      numAt t.mem (State.addr base) w 1 = 2 ^ (64 * w) % n ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % n ∧
      Frame [⟨State.addr base, 8 * capacity⟩, FrameStack.belowA s.sp 48] s.mem t.mem ∧
      Rest roundClobbers s t := by
  have fits : arrAt w 8 ≤ 8 * capacity := ready.width ▸ ready.layout.2.2.1
  have op (j : Nat) (bound : j = 0 ∨ j = 1 ∨ j = 4) : Operand j := by
    rcases bound with rfl | rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  rw [WP.seq_iff]
  refine WP.mono (smallConst_ok s 1 ready (o := 1) (by decide) (by decide) (by decide) (by decide)) ?_
  rintro u ⟨readyU, oneU, _, keepsU, frameU, restU⟩
  change numAt u.mem (State.addr base) w 1 = 1 at oneU
  have modulusU := (keeps_array_num keepsU fits (op 0 (by simp)) (by decide)).trans modulus
  have r2U := (keeps_array_num keepsU fits (op 4 (by simp)) (by decide)).trans r2
  refine WP.mono (montCallEncode_ok b u readyU (calls.of_rest restU) (op 1 (by simp)) (op 1 (by simp))
    (by decide) modulusU odd r2U) ?_
  rintro t ⟨readyT, callsT, modulusT, oneT, keepsT, frameT, restT⟩
  rw [oneU, Nat.one_mul] at oneT
  rw [restU.sp] at frameT
  exact ⟨readyT, callsT, modulusT, oneT, (keeps_array_num keepsT fits (op 4 (by simp)) (by decide)).trans r2U,
    (frameU.mono (by simp)).trans frameT, restU.trans restT⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Rsa.Mont (numAt)

structure MontPrepInput (base src : BitVec 32) (capacity k : Nat) (s : State) : Prop where
  workspace : Workspace s base (8 * capacity)
  stack : PcStack base (s.mem.readW (off (State.addr s.sp) 4) 32) src capacity k s
  minLength : 64 ≤ k
  maxLength : k ≤ 1024
  space : Spec.Rsa.publicScratchWords k ≤ capacity
  sourceFits : src.toNat + k ≤ Nat.pow 2 32
  readable : InRegions (s.rd ++ s.wr) (State.addr src) k
  separate : (⟨State.addr src, k⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩
  large : 1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)
  odd : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) % 2 = 1
  normalized : k % 8 = 1 ∨ 2 ^ (64 * (Spec.Rsa.modulusWords k - 1)) ≤
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)
  calls : CallStack base capacity s

private theorem prepareHead_ok {s : State} {base src : BitVec 32} {capacity k : Nat}
    (h : MontPrepInput base src capacity k s) :
    WP isa (.block [.ldrSp .r0 0, .ldrSp .r6 12]) s fun t =>
      (t.gpr .r0 = base ∧ t.gpr .r6 = BitVec.ofNat 32 k ∧ t.mem = s.mem) ∧ Rest [.r0, .r6] s t := by
  have read0 := h.stack.read (d := 0) (by decide)
  simp only [off, BitVec.add_zero] at read0
  have read12 := h.stack.read (d := 12) (by decide)
  have addr12 : State.addr (s.sp + 12#32) = off (State.addr s.sp) 12 :=
    VG.Arm.addr_add (by have := h.stack.nowrap; omega_using [this])
  refine withRest_all [.r0, .r6] ?_ (by rfl) (by rfl)
  ffrun [BitVec.add_zero, addr12, read0, read12, h.stack.savedBase, h.stack.savedCount]

theorem montPrep_ok (b : MontBackend) {s : State} {base src : BitVec 32} {capacity k : Nat}
    (h : MontPrepInput base src capacity k s) (space : Spec.Rsa.scratchWords k ≤ capacity) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.montPrep (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul)) s fun t =>
      KeyReady base capacity (Spec.Rsa.modulusWords k) t ∧
      MontData base capacity (Spec.Rsa.modulusWords k) t.mem ∧
      VG.Proof.Rsa.Arm.Keys.num t.mem (base + 96#32) (2 * Spec.Rsa.modulusWords k + 2) 0 =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 9 =
        Nat.pow 2 (64 * Spec.Rsa.modulusWords k) % Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 10 =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) -
          Nat.pow 2 (64 * Spec.Rsa.modulusWords k) % Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 0 =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 4 =
        Nat.pow 2 (128 * Spec.Rsa.modulusWords k) % Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      t.mem.readW (off (State.addr base) 224) 64 = BitVec.ofNat 64 (8 * (Spec.Rsa.modulusWords k + 2)) ∧
      Frame [⟨State.addr base, 8 * capacity⟩, FrameStack.belowA s.sp 48] s.mem t.mem ∧
      Rest roundClobbers s t := by
  simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.montPrep, VG.Impl.Ffdh.Arm.ParameterCandidate.seqs]
  refine WP.seq (WP.mono (prepareHead_ok h) ?_)
  rintro u ⟨⟨ptrU, countU, memU⟩, restU⟩
  have inputU : PrepareInput base src capacity k u := by
    refine ⟨h.workspace.congr restU.wr, ?_, ptrU, countU, h.minLength, h.maxLength,
      h.space, h.sourceFits, ?_, h.separate, ?_, ?_⟩
    · have frame : Frame [⟨State.addr base, 8 * capacity⟩] s.mem u.mem := by rw [memU]; exact Frame.refl _ _
      simpa only [memU, restU.sp] using h.stack.after_workspace frame restU
    · rw [restU.rd, restU.wr]; exact h.readable
    · rw [memU]; exact h.large
    · rw [memU]; exact h.odd
  let K := TwoExp.sharedMontgomery base s.sp capacity (Spec.Rsa.modulusWords k) b.name b.mul
    (fun _ _ _ ho ha hb v input => b.correct v input ho ha hb) b.stackOk
  have hp : TwoExp.CallReady base s.sp capacity u := ⟨h.calls.of_rest restU, restU.sp⟩
  refine WP.seq (WP.mono (candidatePrepare_ok u K inputU hp (by rw [memU]; exact h.normalized)) ?_)
  rintro v ⟨readyV, nV, r2V, hpV, frameV, restV⟩
  rw [memU] at nV r2V frameV
  change Frame [⟨State.addr base, 8 * capacity⟩, FrameStack.belowA s.sp 48] s.mem v.mem at frameV
  refine WP.seq (WP.mono (montOne_ok b readyV hpV.1 nV h.odd r2V) ?_)
  rintro a ⟨readyA, _, nA, rA, r2A, frameA, restA⟩
  rw [hpV.2] at frameA
  refine WP.seq (WP.mono (montKeySetup_ok readyA.workspace (MontData.of_ready readyA)
    h.minLength h.maxLength space readyA.stackRead readyA.saved (by
      rw [nA, rA]
      exact Nat.le_of_lt (Nat.mod_lt _ (by have := h.large; omega_using [this])))) ?_)
  rintro t ⟨readyT, dataT, nT, rT, minusT, numberT, strideT, arraysT, frameT, restT⟩
  rw [nA] at nT minusT numberT
  rw [rA] at rT minusT
  exact WP.block_nil ⟨readyT, dataT, nT, rT, minusT, numberT,
    (arraysT 4 (by decide) (by decide)).trans r2A, strideT,
    frameV.trans (frameA.trans (frameT.mono (by simp))), (restU.mono (by simp [roundClobbers])).trans
      (restV.trans (restA.trans restT))⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Phase arguments after the native q/p policy header has been initialized. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm

structure PhaseInput (p : WitnessParams) (src : BitVec 32) (k used : Nat) (s : State) : Prop where
  preparation : MontPrepInput p.base src p.capacity k s
  saved : SavedFrame (witnessValues p used 0) witnessSlots s
  words : p.words = Spec.Rsa.modulusWords k
  modulus : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) = p.modulus
  space : Spec.Rsa.scratchWords k ≤ p.capacity
  stackScratch : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.base, 8 * p.capacity⟩
  stackBelow : 104 ≤ s.sp.toNat
  belowScratch : (FrameStack.belowA s.sp 104).Disjoint ⟨State.addr p.base, 8 * p.capacity⟩
  bitsExact : p.bits = Spec.RsaKeyGen.bitLength (p.modulus - 1)
  bitsPositive : 0 < p.bits
  bitsBound : p.bits ≤ 8192
  bitsFit : p.bits ≤ 64 * p.words
  checksPositive : 0 < p.checks
  checksBound : p.checks ≤ 128
  usedBound : used ≤ p.bytes.length
  tapeCount : p.bytes.length < 2 ^ 32
  tapeFits : p.tape.toNat + p.bytes.length ≤ 2 ^ 32
  tapeRead : InRegions (s.rd ++ s.wr) (State.addr p.tape) p.bytes.length
  tapeScratch : (⟨State.addr p.tape, p.bytes.length⟩ : Region).Disjoint ⟨State.addr p.base, 8 * p.capacity⟩
  tapeStack : (⟨State.addr p.tape, p.bytes.length⟩ : Region).Disjoint ⟨State.addr s.sp, 72⟩
  tapeBelow : (⟨State.addr p.tape, p.bytes.length⟩ : Region).Disjoint (FrameStack.belowA s.sp 104)
  tapeBytes : Spec.Rsa.bytesAt s.mem (State.addr p.tape) p.bytes.length = p.bytes

end VG.Proof.Ffdh.Arm.ParameterCandidate
