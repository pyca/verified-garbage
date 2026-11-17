module

public import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.PairedConsts
public import VerifiedGarbage.Proof.MlDsa.PairedResponseContract
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemoryCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.Framework.Offset
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Basic.IsEmpty.Defs
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirstMemory
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckSlot
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZ
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintVec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseWord
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckSource
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseMath
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.MlDsa
import VerifiedGarbage.Proof.MlDsa.Sign.Iter
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedProductField

/-! ### `MlDsa.AArch64.Optimized.PairedPassOutput`, which this module and modules that import it used -/

section

/-! ## From `PairedPassRead.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

/-- Different strided iterations touch disjoint output vectors. -/
theorem checkSlice_sep (out : Addr) {u k : Nat} (hu : u<8) (hk : k<8) (hne : k≠u)
    (i j : Fin 2 × Fin 8) :
    Mem.Sep (checkAddr (out+BitVec.ofNat 64 (16*k)) i) 16
      (checkAddr (out+BitVec.ofNat 64 (16*u)) j) 16 := by
  simp only [checkAddr,BitVec.add_assoc,←BitVec.ofNat_add]
  exact Offset.sep out (by omega_using [hu, hk, hne]) (by omega_using [hk]) (by omega_using [hu])

/-- A final-pass prefix has not overwritten vectors belonging to later slices. -/
theorem finalPass_read_future (hint : Bool) (work out aux : Addr) (c : CheckConstants)
    (d : CheckData) {u k : Nat} (hu : u≤k) (hk : k<8) (i : Fin 2 × Fin 8) :
    (finalPassData hint work out aux c d u).mem.read (checkAddr (out+BitVec.ofNat 64 (16*k)) i) 16=
      d.mem.read (checkAddr (out+BitVec.ofNat 64 (16*k)) i) 16 := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [finalPassData,checkRun_read_other _ _ _ _ _ _ _ _
      (fun j _ => checkSlice_sep out (by omega_using [hk, hu]) hk (by omega_using [hu]) i j),ih (by omega_using [hu])]

/-- Auxiliary input reads survive all final-pass output writes. -/
theorem finalPass_read_aux (hint : Bool) (work out aux : Addr) (c : CheckConstants)
    (d : CheckData) {u k : Nat} (hu : u≤8) (hk : k<8) (i : Fin 2 × Fin 8)
    (hd : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩) :
    (finalPassData hint work out aux c d u).mem.read (checkAddr (aux+BitVec.ofNat 64 (16*k)) i) 16=
      d.mem.read (checkAddr (aux+BitVec.ofNat 64 (16*k)) i) 16 := by
  apply (finalPass_frame hint work out aux c d hu).read (r:=⟨aux,2048⟩)
  · simp only [checkAddr,BitVec.add_assoc,←BitVec.ofNat_add]
    exact Offset.contains_base aux (by omega_using [hk]) (by omega_using [hk])
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact hd
  · decide

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedPassOutput.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem allChecks_mem (i : Fin 2 × Fin 8) : i∈allChecks := pairIndices_mem i

theorem allChecks_nodup : allChecks.Nodup := by decide +kernel

theorem checkAddr_contains (base : Addr) {u : Nat} (hu : u<8) (i : Fin 2 × Fin 8) :
    (⟨base,2048⟩ : Region).Contains (checkAddr (base+BitVec.ofNat 64 (16*u)) i) 16 := by
  simp only [checkAddr,BitVec.add_assoc,←BitVec.ofNat_add]
  exact Offset.contains_base base (by omega_using [hu]) (by omega_using [hu])

/-- Every written vector has its exact final value, even when later slices
have run; inputs are read from the original memory and raw inverse bank. -/
theorem finalPass_read_written (hint : Bool) (work out aux : Addr) (c : CheckConstants)
    (d : CheckData) {n k : Nat} (hn : n≤8) (hk : k<n) (i : Fin 2 × Fin 8)
    (hw : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩) :
    (finalPassData hint work out aux c d n).mem.read (checkAddr (out+BitVec.ofNat 64 (16*k)) i) 16=
      checkOutput hint ((Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*k)) 128 i.1))[i.2.val])
        (d.mem.read (checkAddr (out+BitVec.ofNat 64 (16*k)) i) 16)
        (d.mem.read (checkAddr (aux+BitVec.ofNat 64 (16*k)) i) 16) c := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : k=n
    · subst k
      rw [finalPass_step hint work out aux c d (by omega_using [hn]) hw]
      rw [checkRun_read_slot _ _ _ _ _ _ _ i (allChecks_mem i) allChecks_nodup
        (fun j _ hne => checkAddr_sep _ hne)
        (fun j _ => ha.sep (checkAddr_contains aux (by omega_using [hn]) i) (checkAddr_contains out (by omega_using [hn]) j))]
      rw [finalPass_read_future hint work out aux c d (Nat.le_refl _) (by omega_using [hn]) i,
        finalPass_read_aux hint work out aux c d (by omega_using [hn]) (by omega_using [hn]) i ha]
    · rw [finalPassData,checkRun_read_other _ _ _ _ _ _ _ _
        (fun j _ => checkSlice_sep out (by omega_using [hn]) (by omega_using [hn, hk]) he i j)]
      exact ih (by omega_using [hn]) (by omega_using [hk, he])

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

end

/-! ### `MlDsa.AArch64.Optimized.PairedCoordinates`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

/-- The final paired pass visits each coefficient in the public strided order. -/
theorem checkAddr_coeff (m : Mem) (out : Addr) (u : Nat) (i : Fin 2 × Fin 8)
    {e : Nat} (he : e<4) :
    vword (m.read (checkAddr (out+BitVec.ofNat 64 (16*u)) i) 16) e=
      coeffAt m (pairPolyPtr out i.1.val) (4*u+32*i.2.val+e) := by
  rw [VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he]
  simp only [checkAddr,coeffAt,pairPolyPtr,BitVec.add_assoc,←BitVec.ofNat_add]
  rw [show 16*u+(1024*i.1.val+128*i.2.val)+4*e=
    1024*i.1.val+4*(4*u+32*i.2.val+e) by omega_using []]

theorem paired_coordinate {k : Nat} (hk : k<n) :
    k=4*(k%32/4)+32*(k/32)+k%4 ∧ k%32/4<8 ∧ k/32<8 ∧ k%4<4 := by
  change k<256 at hk
  omega_using [hk]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

/-! ### `MlDsa.AArch64.Optimized.PairedCheckCoverage`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.Spec.MlDsa

theorem checkCoverage (P : Nat → Nat → Prop) :
    (∀e<4,∀u<8,∀i:Fin 2 × Fin 8,P i.1.val (4*u+32*i.2.val+e)) ↔
      ∀j<2,∀k<n,P j k := by
  constructor
  · intro hall j hj k hk
    obtain ⟨heq,hu,hi,he⟩ := paired_coordinate hk
    have h := hall _ he _ hu (⟨j,hj⟩,⟨k/32,hi⟩)
    simpa only [←heq] using h
  · intro hall e he u hu i
    exact hall i.1.val i.1.isLt _ (by change 4*u+32*i.2.val+e<256; omega_using [he, hu])

theorem paired_norm_iff (f : Nat → Poly) {B : Nat} (hB : 0<B) :
    normRq ((List.range 2).map f)<B ↔ ∀j<2,∀k<n,normZq (f j)[k]!<B := by
  rw [VG.Proof.MlDsa.Sign.normRq_lt_iff _ hB]
  simp only [List.forall_mem_map,List.mem_range]
  apply forall_congr'
  intro j
  apply forall_congr'
  intro _
  exact VG.Proof.MlDsa.Round.normRq_lt _ _

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

/-! ### `MlDsa.AArch64.Optimized.PairedMaskSemantic`, which this module and modules that import it used -/

section

/-! ## From `PairedPassFlags.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

def passMask (hint : Bool) (work out : Addr) (c : CheckConstants)
    (m : Mem) (k : Nat) (i : Fin 2 × Fin 8) (e : Nat) : BitVec 32 :=
  checkMask hint ((Inverse.rawFinalValues (readPair m (work+BitVec.ofNat 64 (16*k)) 128 i.1))[i.2.val])
    (m.read (checkAddr (out+BitVec.ofNat 64 (16*k)) i) 16) c e

/-- A final-pass lane accepts exactly when every original coefficient check
accepts, together with its incoming rejection accumulator. -/
theorem finalPass_flag_zero_iff (hint : Bool) (work out aux : Addr) (c : CheckConstants)
    (d : CheckData) {n : Nat} (hn : n≤8)
    (hw : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩) {e : Nat} (he : e<4) :
    vword (finalPassData hint work out aux c d n).flags e=0 ↔
      vword d.flags e=0 ∧ ∀k<n,∀i,passMask hint work out c d.mem k i e=0 := by
  induction n with
  | zero => simp only [finalPassData,Nat.not_lt_zero,false_implies,forall_const,and_true]
  | succ n ih =>
    rw [finalPass_step hint work out aux c d (by omega_using [hn]) hw,
      checkRun_flag_zero_iff _ _ _ _ _ _ _ allChecks_nodup he,ih (by omega_using [hn])]
    have hlast : (∀i∈allChecks,
        checkMask hint ((Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*n)) 128 i.1))[i.2.val])
          ((finalPassData hint work out aux c d n).mem.read
            (checkAddr (out+BitVec.ofNat 64 (16*n)) i) 16) c e=0) ↔
        ∀i,passMask hint work out c d.mem n i e=0 := by
      simp only [finalPass_read_future hint work out aux c d (Nat.le_refl n) (by omega_using [hn]),
        allChecks_mem,true_implies,passMask]
    rw [hlast]
    constructor
    · rintro ⟨⟨h0,hprev⟩,hlast⟩
      refine ⟨h0,fun k hk i => ?_⟩
      by_cases hkn : k<n
      · exact hprev k hkn i
      · have heq : k=n := by omega_using [hk, hkn]
        subst k
        exact hlast i
    · rintro ⟨h0,hall⟩
      exact ⟨⟨h0,fun k hk => hall k (by omega_using [hk])⟩,hall n (by omega_using [])⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedMaskSemantic.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Optimized.Response

theorem normMask_zero {x : BitVec 32} {B : Nat} (hB : 1≤B) (hB' : B≤524288)
    (hl : -8380417<x.toInt) (hh : x.toInt<8380417) :
    normMask x (BitVec.ofNat 32 (B-1)) (BitVec.ofNat 32 (2*B-1))=0 ↔
      -(B:Int)<x.toInt ∧ x.toInt<(B:Int) := by
  rw [normMask_value hB hB' hl hh]
  split
  · rename_i h
    exact ⟨fun _ => h,fun _ => rfl⟩
  · rename_i h
    exact ⟨fun hz => False.elim ((by decide : (-1 : BitVec 32)≠0) hz),
      fun hx => False.elim (h hx)⟩

/-- The z machine mask is zero exactly at the specification's strict norm. -/
theorem zMask_zero {a b : BitVec 32} {B : Nat} (ha : a.toNat<8380417)
    (hb : -8380417<b.toInt ∧ b.toInt<2*8380417) (hB : 1≤B) (hB' : B≤524288) :
    normMask (reduceWord (b+a)) (BitVec.ofNat 32 (B-1)) (BitVec.ofNat 32 (2*B-1))=0 ↔
      normZq (ofInt ((a.toNat:Int)+b.toInt))<B := by
  rw [BitVec.add_comm b a]
  have hi := addReduced_int a b ha hb
  have bounds := reduce32_bounds (by omega_using [hb] : -2*8380417<(a.toNat:Int)+b.toInt)
    (by omega_using [ha, hb] : (a.toNat:Int)+b.toInt<3*8380417)
  rw [normMask_zero hB hB' (by rw [hi]; omega_using [bounds]) (by rw [hi]; omega_using [bounds]),hi]
  exact (reduce32_norm_iff _ _ (by omega_using [hb]) (by omega_using [ha, hb]) hB').symm

/-- The hint path checks the inverse product itself against the strict bound. -/
theorem hMask_zero {b : BitVec 32} {B : Nat}
    (hb : -8380417<b.toInt ∧ b.toInt<2*8380417) (hB : 1≤B) (hB' : B≤524288) :
    normMask (reduceWord b) (BitVec.ofNat 32 (B-1)) (BitVec.ofNat 32 (2*B-1))=0 ↔
      normZq (ofInt b.toInt)<B := by
  have hi := reduceWord_int b (by omega_using [hb]) (by omega_using [hb])
  have bounds := reduce32_bounds (by omega_using [hb] : -2*8380417<b.toInt)
    (by omega_using [hb] : b.toInt<3*8380417)
  rw [normMask_zero hB hB' (by rw [hi]; omega_using [bounds]) (by rw [hi]; omega_using [bounds]),hi]
  exact (reduce32_norm_iff _ _ (by omega_using [hb]) (by omega_using [hb]) hB').symm

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

end

/-! ### `MlDsa.AArch64.Optimized.PairedZStoredField`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.ResponseHintField`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem hint_cancel (r c : Zq) : r+c+(-c)=r := by
  apply Fin.ext
  rw [VG.Proof.MlDsa.Arith.val_add',VG.Proof.MlDsa.Arith.val_add',VG.Proof.MlDsa.Arith.val_neg]
  have hr := r.isLt
  have hc := c.isLt
  simp only [q] at *
  omega_using []

theorem hint_makeHint {g : Nat} (hg : IsG g) (r : Zq) (c : Int)
    (hc : -4202495≤c ∧ c≤4210685) :
    makeHint g (-ofInt c) (r+ofInt c)=
      decide (hintPredicate g (lowBits g r+c) (highBits g r)) := by
  unfold makeHint
  rw [hint_cancel]
  simp only [hint_high_change hg r c hc]

theorem hintWord_field {g : Nat} (hg : IsG g) (r : Zq) (raw lo high : BitVec 32)
    (hrl : -8380417<raw.toInt) (hrh : raw.toInt<2*8380417)
    (hl : lo.toInt=lowBits g r) (hh : high.toInt=highBits g r) :
    hintWord (BitVec.ofNat 32 g) (reduceWord raw+lo) high=
      if makeHint g (-ofInt (reduce32 raw.toInt)) (r+ofInt (reduce32 raw.toInt)) then 1 else 0 := by
  have hb := reduce32_bounds (by omega_using [hrl] : -2*8380417<raw.toInt) (by omega_using [hrh] : raw.toInt<3*8380417)
  have hi := reduceWord_int raw (by omega_using [hrl]) (by omega_using [hrh])
  have hlo := lowBits_bounds hg r
  have hgb : 1≤g ∧ g≤524288 := by rcases hg with rfl | rfl <;> decide
  have hadd := addWord_int (reduceWord raw) lo (by rw [hi,hl]; omega_using [hb, hlo, hgb]) (by rw [hi,hl]; omega_using [hb, hlo, hgb])
  have hsum : (reduceWord raw+lo).toInt=lowBits g r+reduce32 raw.toInt := by rw [hadd,hi,hl]; omega_using []
  rw [hintWord_value hgb.1 hgb.2 _ _ (by rw [hsum]; omega_using [hb, hlo, hgb]) (by rw [hsum]; omega_using [hb, hlo, hgb]),
    hsum,hh,hint_makeHint hg r _ hb]
  simp only [decide_eq_true_eq]

/-- Reduction changes only the integer representative of the challenge product. -/
theorem reduce32_field (x : Int) : ofInt (reduce32 x)=ofInt x := by
  apply Fin.ext
  have h1 := VG.Proof.MlDsa.KeyGen.ofInt_val (reduce32 x)
  have h2 := VG.Proof.MlDsa.KeyGen.ofInt_val x
  have h3 := reduce32_mod x
  omega_using [h1, h2, h3]

theorem hintWord_raw_field {g : Nat} (hg : IsG g) (r : Zq) (raw lo high : BitVec 32)
    (hrl : -8380417<raw.toInt) (hrh : raw.toInt<2*8380417)
    (hl : lo.toInt=lowBits g r) (hh : high.toInt=highBits g r) :
    hintWord (BitVec.ofNat 32 g) (reduceWord raw+lo) high=
      BitVec.ofNat 32 (makeHint g (-ofInt raw.toInt) (r+ofInt raw.toInt)).toNat := by
  rw [hintWord_field hg r raw lo high hrl hrh hl hh,reduce32_field]
  cases makeHint g (-ofInt raw.toInt) (r+ofInt raw.toInt) <;> rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

end

/-! ## From `PairedZUnused.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

/-- The z check does not read or depend on its auxiliary argument. -/
theorem checkStep_z_aux (raw : BitVec 128) (out aux aux' : Addr)
    (c : CheckConstants) (d : CheckData) :
    checkStep false raw out aux c d=checkStep false raw out aux' c d := by
  simp only [checkStep,Bool.false_eq_true,ite_false]

theorem checkRun_z_aux (v : Values) (out aux aux' : Addr) (c : CheckConstants)
    (d : CheckData) (js : List (Fin 2 × Fin 8)) :
    checkRun false v out aux c d js=checkRun false v out aux' c d js := by
  induction js generalizing d with
  | nil => rfl
  | cons i js ih =>
    simp only [checkRun]
    rw [checkStep_z_aux _ _ _ (aux'+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val)),ih]

theorem finalPass_z_aux (work out aux aux' : Addr) (c : CheckConstants)
    (d : CheckData) (n : Nat) :
    finalPassData false work out aux c d n=finalPassData false work out aux' c d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finalPassData,ih]
    exact checkRun_z_aux _ _ _ _ _ _ _

/-- Exact z output with an arbitrary unused auxiliary argument. -/
theorem finalPass_z_read_written (work out aux : Addr) (c : CheckConstants)
    (d : CheckData) {n k : Nat} (hn : n≤8) (hk : k<n) (i : Fin 2 × Fin 8)
    (hw : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩) :
    (finalPassData false work out aux c d n).mem.read (checkAddr (out+BitVec.ofNat 64 (16*k)) i) 16=
      checkOutput false ((Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*k)) 128 i.1))[i.2.val])
        (d.mem.read (checkAddr (out+BitVec.ofNat 64 (16*k)) i) 16) 0 c := by
  rw [finalPass_z_aux work out aux work]
  have h := finalPass_read_written false work out work c d hn hk i hw hw
  simpa only [checkOutput,Bool.false_eq_true,ite_false] using h

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZFieldValues.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Optimized.Response

/-- The fused z store is the same centered representative on successful and
unsuccessful attempts. -/
theorem zOutput_field {raw low high : BitVec 128} (c : CheckConstants)
    {e : Nat} (he : e<4) (hl : (vword low e).toNat<8380417)
    (hr : -8380417<(vword raw e).toInt ∧ (vword raw e).toInt<2*8380417) :
    let x := vword (checkOutput false raw low high c) e;
    -4202495≤x.toInt ∧ x.toInt≤4210685 ∧
      ofInt x.toInt=ofInt ((vword low e).toNat+(vword raw e).toInt) := by
  simp only [checkOutput,laneVector_word _ he,Bool.false_eq_true,ite_false]
  rw [BitVec.add_comm (vword raw e),addReduced_int _ _ hl hr]
  have hb := reduce32_bounds (by omega_using [hr] : -2*8380417<(vword low e).toNat+(vword raw e).toInt)
    (by omega_using [hl, hr] : (vword low e).toNat+(vword raw e).toInt<3*8380417)
  exact ⟨hb.1,hb.2,reduce32_field _⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZStoredField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem firstPass_checkInput_read {m : Mem} {work challenge secret out : Addr} {u : Nat}
    (hu : u<8) (i : Fin 2 × Fin 8)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨work,2048⟩) :
    (firstPassMem m work challenge secret 8).read (checkAddr (out+BitVec.ofNat 64 (16*u)) i) 16=
      m.read (checkAddr (out+BitVec.ofNat 64 (16*u)) i) 16 := by
  exact (firstPass_frame (m:=m) (a:=challenge) (b:=secret) (by decide : 8≤8)).read
    (checkAddr_contains out hu i)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)

theorem zPass_stored_field {m : Mem} {work challenge secret out aux : Addr} {u e : Nat}
    (hu : u<8) (he : e<4) (i : Fin 2 × Fin 8) (c : CheckConstants)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) (flags count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,flags,count⟩
    let x := coeffAt (finalPassData false work out aux c d 8).mem
      (pairPolyPtr out i.1.val) (4*u+32*i.2.val+e);
    -4202495≤x.toInt ∧ x.toInt≤4210685 ∧
      ofInt x.toInt=(add (polyAt m (pairPolyPtr out i.1.val))
        (pairedProduct m challenge secret i.1.val))[4*u+32*i.2.val+e]! := by
  dsimp only
  have hk : 4*u+32*i.2.val+e<n := by change 4*u+32*i.2.val+e<256; omega_using [hu, he]
  have hr := rawFinal_field hu hc hs i.1 (Inverse.positiveReduced_is hp.1)
    (Inverse.positiveReduced_is (hp.2 i.1.val i.1.isLt)) i.2 he
  rw [←checkAddr_coeff _ out u i he,
    finalPass_z_read_written work out aux c _ (by decide : 8≤8) hu i ho]
  have hv := zOutput_field c he (raw := (Inverse.rawFinalValues
    (readPair (firstPassMem m work challenge secret 8) (work+BitVec.ofNat 64 (16*u)) 128 i.1))[i.2.val])
    (high := 0)
    (low := (firstPassMem m work challenge secret 8).read (checkAddr (out+BitVec.ofNat 64 (16*u)) i) 16)
    (by rw [firstPass_checkInput_read hu i ho.symm,checkAddr_coeff _ _ _ _ he]; exact hy _ i.1.isLt _ hk)
    ⟨hr.1,hr.2.1⟩
  refine ⟨hv.1,hv.2.1,hv.2.2.trans ?_⟩
  rw [firstPass_checkInput_read hu i ho.symm,checkAddr_coeff _ _ _ _ he,
    ofInt_add,ofInt_nat_eq,←polyAt_get _ _ hk,hr.2.2,add_get _ _ hk]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

end

/-! ### `MlDsa.AArch64.Optimized.PairedZVerified`, which only this module used -/

section

/-! ## From `PairedZContractTiming.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedZ_public {s t : State}
    (h : (pairedZContract (abi.withConsts pairedConsts)).pub s t) :
    Taint.AgreeS ["VG_MLDSA_INV_PAIR"] (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4]) s t := by
  sig_pub [pairedZContract,pairedZSig,abi,argRegs,Abi.withConsts,pairedConsts_eq] at h
  obtain ⟨hsp,htable,h0,h1,h2,h3,h4⟩ := h
  refine ⟨VG.Proof.MlKem.AArch64.agree_of hsp ?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl <;> with_reducible assumption
  · intro name hn
    have he : name="VG_MLDSA_INV_PAIR" := by simpa only [List.mem_singleton] using hn
    subst name
    exact htable

theorem pairedZ_contract_ct : ConstantTime isa
    (pairedZContract (abi.withConsts pairedConsts)).pre
    (pairedZContract (abi.withConsts pairedConsts)).pub (selected .z) := by
  intro s t tr1 tr2 s' t' _ _ hp he hf
  exact z_ct s t tr1 tr2 s' t' trivial trivial (pairedZ_public hp) he hf

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZEntryFrame.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

structure ZEntryFrame (s : State) (m : Mem) : Prop where
  products : pairedProductsReduced m (s.gpr .x0) (s.gpr .x1)
  data : ∀j<2,Reduced m (pairPolyPtr (s.gpr .x2) j)
  sum : ∀j<2,add (polyAt m (pairPolyPtr (s.gpr .x2) j)) (pairedProduct m (s.gpr .x0) (s.gpr .x1) j)=
    add (polyAt s.mem (pairPolyPtr (s.gpr .x2) j)) (pairedProduct s.mem (s.gpr .x0) (s.gpr .x1) j)

theorem zEntry_frame {s : State} {m : Mem} (h : ZSpecPre s)
    (hf : Frame [⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩] s.mem m) : ZEntryFrame s m := by
  have hc : ∀r∈[⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩],(⟨s.gpr .x0,1024⟩:Region).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.commonWork.sub_right (Offset.sub_base _ (by decide))
  have hs : ∀r∈[⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩],(⟨s.gpr .x1,2048⟩:Region).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.secretWork.sub_right (Offset.sub_base _ (by decide))
  have ho : ∀r∈[⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩],(⟨s.gpr .x2,2048⟩:Region).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.dataWork.sub_right (Offset.sub_base _ (by decide))
  refine ⟨pairedProductsReduced_frame hf hc hs h.products,?_,?_⟩
  · intro j hj
    apply VG.Proof.MlDsa.Verify.reduced_frame hf _ (h.data j hj)
    intro r hr
    exact (ho r hr).sub_left (Offset.sub_base _ (by omega_using [hj]))
  · intro j hj
    rw [pairedProduct_frame hf hc hs hj,VG.Proof.MlDsa.Verify.polyAt_frame hf]
    intro r hr
    exact (ho r hr).sub_left (Offset.sub_base _ (by omega_using [hj]))

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZAllFields.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

theorem zPass_all_fields {m : Mem} {work challenge secret out aux : Addr} (c : CheckConstants)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) (flags count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,flags,count⟩
    let result := (finalPassData false work out aux c d 8).mem
    ∀j<2,CenteredReduced result (pairPolyPtr out j) ∧
      signedPolyAt result (pairPolyPtr out j)=add (polyAt m (pairPolyPtr out j))
        (pairedProduct m challenge secret j) := by
  dsimp only
  intro j hj
  have hv : ∀k<n,
      let x := coeffAt (finalPassData false work out aux c
        ⟨firstPassMem m work challenge secret 8,flags,count⟩ 8).mem (pairPolyPtr out j) k;
      -4202495≤x.toInt ∧ x.toInt≤4210685 ∧
        ofInt x.toInt=(add (polyAt m (pairPolyPtr out j)) (pairedProduct m challenge secret j))[k]! := by
    intro k hk
    obtain ⟨heq,hu,hi,he⟩ := paired_coordinate hk
    have h := zPass_stored_field (aux:=aux) hu he (⟨j,hj⟩,⟨k/32,hi⟩) c hc hs ho hp hy flags count
    simpa only [←heq] using h
  constructor
  · intro k hk
    have h := hv k hk
    change -8380417<_ ∧ _<8380417
    exact ⟨by omega,by omega⟩
  · apply Vector.ext
    intro k hk
    simpa only [signedPolyAt,Vector.getElem_ofFn,VG.Proof.MlDsa.Arith.getElem!_eq _ hk] using (hv k hk).2.2

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZLaneNorm.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem zLane_norm {m : Mem} {work challenge secret out : Addr} {u e B : Nat}
    (hu : u<8) (he : e<4) (i : Fin 2 × Fin 8) (c : CheckConstants)
    (hlower : vword c.lower e=BitVec.ofNat 32 (B-1))
    (hwidth : vword c.width e=BitVec.ofNat 32 (2*B-1))
    (hB : 1≤B) (hB' : B≤524288)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨out,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) :
    passMask false work out c (firstPassMem m work challenge secret 8) u i e=0 ↔
      normZq (add (polyAt m (pairPolyPtr out i.1.val))
        (pairedProduct m challenge secret i.1.val))[4*u+32*i.2.val+e]!<B := by
  have hk : 4*u+32*i.2.val+e<n := by change 4*u+32*i.2.val+e<256; omega_using [hu, he]
  have hr := rawFinal_field hu hc hs i.1 (Inverse.positiveReduced_is hp.1)
    (Inverse.positiveReduced_is (hp.2 i.1.val i.1.isLt)) i.2 he
  simp only [passMask,checkMask,Bool.false_eq_true,ite_false,hlower,hwidth]
  rw [firstPass_checkInput_read hu i ho,checkAddr_coeff _ _ _ _ he,
    zMask_zero (hy _ i.1.isLt _ hk) ⟨hr.1,hr.2.1⟩ hB hB',
    ofInt_add,ofInt_nat_eq,←polyAt_get _ _ hk,hr.2.2,add_get _ _ hk]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZAccess.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

private theorem accessRegion {p : Addr} {len : Nat} {rs : List Region}
    (h : (⟨p,len⟩:Region)∈rs) {off : Nat} (ho : off+16≤len) (hl : len<2^64) :
    InRegions rs (p+BitVec.ofNat 64 off) 16 :=
  ⟨_,h,Offset.contains_base p ho (by omega_using [ho, hl])⟩

theorem ZSpecPre.access {s : State} (h : ZSpecPre s) : EntryAccess s := by
  constructor
  · intro off ho
    exact accessRegion (by rw [h.rd]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.rd]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.rd]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.wr]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.wr]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.wr]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.wr]; simp) ho (by decide)

/-- The public paired-z signature provides every actual access, including the
saved register area, without assigning memory to the unused fourth argument. -/
theorem pairedZ_machine {s : State} (h : ZSpecPre s) :
    WP isa (selected .z) s fun t =>
      ∃a u,Arguments s a ∧ Frame [⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩] s.mem a.mem ∧
        Prepared a u ∧ CheckSetup false a u ∧ Keep entryRegs s t ∧
        let d := finalPassData false (s.gpr .x4) (s.gpr .x2) (s.gpr .x3) (constantsAt u) (dataAt u) 8
        t.mem=d.mem ∧ t.gpr .x0=dataReturn .z d := by
  have htw := h.tableSep (⟨s.gpr .x4,2176⟩:Region) (by rw [h.wr]; simp)
  have htd := h.tableSep (⟨s.gpr .x2,2048⟩:Region) (by rw [h.wr]; simp)
  exact selected_check_ok false h.access h.table.words
    (htw.sub_right (Region.sub_prefix (by decide)))
    (htw.sub_right (Offset.sub_base _ (by decide))) htd
    (h.dataWork.symm.sub_left (Offset.sub_base _ (by decide))) (by simp)

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZPreIntro.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedZ_pre_intro {s : State} (h : ZSpecPre s)
    (held : ∀i<512,s.mem.readW (s.syms "VG_MLDSA_INV_PAIR"+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (fitTable : (s.syms "VG_MLDSA_INV_PAIR").toNat+4096≤2^64)
    (fit0 : (s.gpr .x0).toNat+1024≤2^64) (fit1 : (s.gpr .x1).toNat+2048≤2^64)
    (fit2 : (s.gpr .x2).toNat+2048≤2^64)
    (fit4 : (s.gpr .x4).toNat+2176≤2^64) :
    (pairedZContract (abi.withConsts pairedConsts)).pre s := by
  sig_pre [pairedZContract,pairedZSig,abi,argRegs,pairedConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,PairedTable.expandedWords_length,stackBelow]
  exact ⟨by rw [h.rd]; rfl,held,fitTable,h.tableSep,h.tableAl,by rw [h.rd]; rfl,h.wr,
    h.commonData,h.commonWork,h.secretData,h.secretWork,
    h.dataWork,fit0,fit1,fit2,fit4,h.products,h.data,h.boundLow,h.boundHigh⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZNormComplete.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

theorem zPass_norm_complete {m : Mem} {work challenge secret out aux : Addr} {B : Nat}
    (c : CheckConstants)
    (hlower : ∀e<4,vword c.lower e=BitVec.ofNat 32 (B-1))
    (hwidth : ∀e<4,vword c.width e=BitVec.ofNat 32 (2*B-1))
    (hB : 1≤B) (hB' : B≤524288)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) (count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,0,count⟩
    (∀e<4,vword (finalPassData false work out aux c d 8).flags e=0) ↔
      normRq ((List.range 2).map fun j => add (polyAt m (pairPolyPtr out j))
        (pairedProduct m challenge secret j))<B := by
  dsimp only
  rw [paired_norm_iff _ (by omega_using [hB]),←checkCoverage]
  apply forall_congr'
  intro e
  apply forall_congr'
  intro he
  rw [finalPass_flag_zero_iff false work out aux c _ (by decide : 8≤8) ho he]
  have hz : vword (0 : BitVec 128) e=0 := by simp [vword]
  simp only [hz,true_and]
  apply forall_congr'
  intro u
  apply forall_congr'
  intro hu
  apply forall_congr'
  intro i
  exact zLane_norm hu he i c (hlower e he) (hwidth e he) hB hB' hc hs ho.symm hp hy

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZSat.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

def zSatWith (m : Mem) : State where
  gpr r := if r=.x0 then 4096 else if r=.x1 then 8192 else if r=.x2 then 12288
    else if r=.x3 then 16384 else if r=.x4 then 20480 else if r=.x5 then 95232
    else if r=.x6 then 1 else 0
  sp := 131072
  syms _ := 65536
  mem := m
  rd := [⟨4096,1024⟩,⟨8192,2048⟩,⟨65536,4096⟩]
  wr := [⟨12288,2048⟩,⟨20480,2176⟩]

theorem zSatWith_pre (m : Mem)
    (held : ∀i<512,m.readW (65536+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (hprod : pairedProductsReduced m 4096 8192)
    (hdata : ∀j<2,Reduced m (pairPolyPtr 12288 j)) :
    (pairedZContract (abi.withConsts pairedConsts)).pre (zSatWith m) := by
  apply pairedZ_pre_intro (s:=zSatWith m) ?_ held (by dsimp only [zSatWith]; decide) (by dsimp only [zSatWith]; decide) (by dsimp only [zSatWith]; decide) (by dsimp only [zSatWith]; decide) (by dsimp only [zSatWith]; decide)
  refine ⟨rfl,rfl,?_,?_,?_,?_,?_,?_,?_,hprod,hdata,by dsimp only [zSatWith]; decide,by dsimp only [zSatWith]; decide,by dsimp only [zSatWith]; try decide⟩
  · intro i hi
    refine (held i hi).trans ?_
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rw [PairedTable.expandedWords_length]; exact hi),
      Option.getD_some,getElem!_pos _ _ (by rw [PairedTable.expandedWords_length]; exact hi)]
  · intro r hr
    change r∈[⟨12288,2048⟩,⟨20480,2176⟩] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact Region.disjoint_of_sep (by dsimp only [zSatWith]; decide)
  all_goals exact Region.disjoint_of_sep (by dsimp only [zSatWith]; decide)

def zSat : State := zSatWith pairedSatMem

theorem pairedZ_sat : (pairedZContract (abi.withConsts pairedConsts)).pre zSat := by
  apply zSatWith_pre pairedSatMem pairedSat_held
  · refine ⟨pairedSat_positive (by decide : 4096≤32768),?_⟩
    intro j hj
    change PositiveReduced pairedSatMem (8192+BitVec.ofNat 64 (1024*j))
    rw [show (8192:BitVec 64)=BitVec.ofNat 64 8192 by rfl,←BitVec.ofNat_add]
    exact pairedSat_positive (by omega_using [hj])
  · intro j hj
    change Reduced pairedSatMem (12288+BitVec.ofNat 64 (1024*j))
    rw [show (12288:BitVec 64)=BitVec.ofNat 64 12288 by rfl,←BitVec.ofNat_add]
    exact pairedSat_reduced (by omega_using [hj])

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZReturnSemantic.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Optimized.Response

theorem zPass_return {m : Mem} {work challenge secret out aux : Addr} {B : Nat}
    (c : CheckConstants)
    (hlower : ∀e<4,vword c.lower e=BitVec.ofNat 32 (B-1))
    (hwidth : ∀e<4,vword c.width e=BitVec.ofNat 32 (2*B-1))
    (hB : 1≤B) (hB' : B≤524288)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) (count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,0,count⟩
    finishValue (finalPassData false work out aux c d 8).flags=
      if normRq ((List.range 2).map fun j => add (polyAt m (pairPolyPtr out j))
        (pairedProduct m challenge secret j))<B then 1 else 0 := by
  dsimp only
  have hn := zPass_norm_complete (aux:=aux) c hlower hwidth hB hB' hc hs ho hp hy count
  dsimp only at hn
  rw [finishValue_accept _ (finalPass_masks _ _ _ _ _ _ _ (by intro e he; left; simp [vword])),
    hn]
  split <;> simp_all only

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZFunctional.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

structure ZResult (s t : State) : Prop where
  keep : Keep entryRegs s t
  fields : ∀j<2,CenteredReduced t.mem (pairPolyPtr (s.gpr .x2) j) ∧
    signedPolyAt t.mem (pairPolyPtr (s.gpr .x2) j)=add (polyAt s.mem (pairPolyPtr (s.gpr .x2) j))
      (pairedProduct s.mem (s.gpr .x0) (s.gpr .x1) j)
  ret : t.gpr .x0=if normRq ((List.range 2).map fun j => add (polyAt s.mem (pairPolyPtr (s.gpr .x2) j))
    (pairedProduct s.mem (s.gpr .x0) (s.gpr .x1) j))<Round.arg32 s .x6 then 1 else 0

theorem pairedZ_functional {s : State} (h : ZSpecPre s) :
    WP isa (selected .z) s (ZResult s) := by
  refine WP.mono (pairedZ_machine h) fun t ⟨a,u,ha,hf,hp,hl,ht,hmem,hret⟩ => ?_
  have hframe := zEntry_frame h hf
  have hdata : dataAt u=⟨firstPassMem a.mem (s.gpr .x4) (s.gpr .x0) (s.gpr .x1) 8,0,u.v .v14⟩ := by
    unfold dataAt
    rw [hp.mem,ha.work,ha.common,ha.secret,hl.flags]
  have hlower : ∀e<4,vword (constantsAt u).lower e=BitVec.ofNat 32 (Round.arg32 s .x6-1) := by
    intro e he
    change vword (u.v .v9) e=_
    rw [hl.lower e he,ha.bound]
    exact bound_sub_one _ h.boundLow
  have hwidth : ∀e<4,vword (constantsAt u).width e=BitVec.ofNat 32 (2*Round.arg32 s .x6-1) := by
    intro e he
    change vword (u.v .v10) e=_
    rw [hl.width e he,ha.bound]
    exact bound_width _ h.boundLow
  have hc := h.commonWork.sub_right (Region.sub_prefix (by decide : 2048≤2176))
  have hs := h.secretWork.sub_right (Region.sub_prefix (by decide : 2048≤2176))
  have ho := h.dataWork.symm.sub_left (Region.sub_prefix (by decide : 2048≤2176))
  have hfields := zPass_all_fields (aux:=s.gpr .x3) (constantsAt u) hc hs ho hframe.products hframe.data 0 (u.v .v14)
  have hvalue := zPass_return (aux:=s.gpr .x3) (constantsAt u) hlower hwidth h.boundLow h.boundHigh
    hc hs ho hframe.products hframe.data (u.v .v14)
  dsimp only at hfields hvalue
  rw [hdata] at hmem hret
  refine ⟨ht,?_,?_⟩
  · intro j hj
    rw [hmem]
    have hv := hfields j hj
    rw [hframe.sum j hj] at hv
    exact hv
  · rw [hret]
    change Response.finishValue _=_
    rw [hvalue]
    have he : ((List.range 2).map fun j => add (polyAt a.mem (pairPolyPtr (s.gpr .x2) j))
        (pairedProduct a.mem (s.gpr .x0) (s.gpr .x1) j))=
        ((List.range 2).map fun j => add (polyAt s.mem (pairPolyPtr (s.gpr .x2) j))
        (pairedProduct s.mem (s.gpr .x0) (s.gpr .x1) j)) := by
      apply List.map_congr_left
      intro j hj
      exact hframe.sum j (List.mem_range.mp hj)
    rw [he]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedZ_post {s t : State} (h : ZResult s t) :
    (pairedZContract (abi.withConsts pairedConsts)).post s t := by
  sig_post [pairedZContract,pairedZSig,abi,argRegs,Abi.withConsts,pairedConsts_eq]
  refine ⟨h.fields,?_⟩
  rw [h.ret]
  split <;> rfl

theorem pairedZ_correct (s : State)
    (h : (pairedZContract (abi.withConsts pairedConsts)).pre s) :
    ∃tr t,Exec isa (selected .z) s tr t ∧ abiPreserved s t ∧
      (pairedZContract (abi.withConsts pairedConsts)).post s t := by
  obtain ⟨tr,t,he,hr⟩ := pairedZ_functional (pairedZ_pre h)
  exact ⟨tr,t,he,entryKeep_abi hr.keep,pairedZ_post hr⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

/-- Exact selected batched response-sum kernel, including all-path outputs,
strict norm return, restored ABI, and the shared public-input timing policy. -/
theorem pairedZ_verified : Verified target (selected .z)
    (pairedZContract (abi.withConsts pairedConsts)) :=
  ⟨pairedZ_correct,pairedZ_contract_ct,⟨zSat,pairedZ_sat⟩⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

end


/-! ## From `PairedZCall.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedZ_callee (S : Nat) :
    CalleeOk S (selected .z) (pairedZContract (abi.withConsts pairedConsts)) := by
  refine CalleeOk.of_ct pairedZ_verified.1 pairedZ_verified.2.1 (by lit_decide) (fun _ _ h => h) ?_
  change 0≤S
  exact Nat.zero_le _

abbrev pairedZArgs (c secret y unused work : Ptr) (gamma bound : Nat) : List (Reg × Arg) :=
  [(.x0,.ptr c),(.x1,.ptr secret),(.x2,.ptr y),(.x3,.ptr unused),(.x4,.ptr work),
    (.x5,.imm gamma),(.x6,.imm bound)]

structure PairedZReady (c secret y work : Ptr) (bound : Nat) (s : State) : Prop where
  cFit : (pa s c).toNat+1024≤2^64
  secretFit : (pa s secret).toNat+2048≤2^64
  yFit : (pa s y).toNat+2048≤2^64
  workFit : (pa s work).toNat+2176≤2^64
  held : ∀i<512,s.mem.readW (s.syms "VG_MLDSA_INV_PAIR"+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0
  tableFit : (s.syms "VG_MLDSA_INV_PAIR").toNat+4096≤2^64
  tableApart : ∀r∈[⟨pa s y,2048⟩,⟨pa s work,2176⟩],
    (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint r
  cY : (⟨pa s c,1024⟩:Region).Disjoint ⟨pa s y,2048⟩
  cWork : (⟨pa s c,1024⟩:Region).Disjoint ⟨pa s work,2176⟩
  secretY : (⟨pa s secret,2048⟩:Region).Disjoint ⟨pa s y,2048⟩
  secretWork : (⟨pa s secret,2048⟩:Region).Disjoint ⟨pa s work,2176⟩
  yWork : (⟨pa s y,2048⟩:Region).Disjoint ⟨pa s work,2176⟩
  products : pairedProductsReduced s.mem (pa s c) (pa s secret)
  data : ∀j<2,Reduced s.mem (pairPolyPtr (pa s y) j)
  boundLow : 1≤bound
  boundHigh : bound≤524288
  readable : Covers ([⟨pa s c,1024⟩,⟨pa s secret,2048⟩,⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩]++
    [⟨pa s y,2048⟩,⟨pa s work,2176⟩]) (s.rd++s.wr)
  writable : Covers [⟨pa s y,2048⟩,⟨pa s work,2176⟩] s.wr
  tableAligned : (s.syms "VG_MLDSA_INV_PAIR").toNat%64=0

theorem pairedZAt_pre {s s1 : State} {c secret y unused work : Ptr} {gamma bound : Nat}
    (h : PairedZReady c secret y work bound s)
    (h1 : Args (pairedZArgs c secret y unused work gamma bound) s s1) (hy : s1.syms=s.syms) :
    (pairedZContract (abi.withConsts pairedConsts)).pre
      (s1.callEntry.withRegions [⟨pa s c,1024⟩,⟨pa s secret,2048⟩,⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩]
        [⟨pa s y,2048⟩,⟨pa s work,2176⟩]) := by
  have hb : s1.gpr .x6=BitVec.ofNat 64 bound := h1.imm (by simp [pairedZArgs])
  have hb32 := imm32 (v:=bound) (by have := h.boundHigh; omega_using [this])
  sig_pre [pairedZContract,pairedZSig,abi,argRegs,pairedConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,PairedTable.expandedWords_length,stackBelow]
  simp only [hy,Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r4 h1,Args.mem h1,Arg.val,hb,hb32]
  exact ⟨True.intro,h.held,h.tableFit,h.tableApart _ (by simp),h.tableApart _ (by simp),h.tableAligned,True.intro,True.intro,h.cY,h.cWork,h.secretY,h.secretWork,
    h.yWork,h.cFit,h.secretFit,h.yFit,h.workFit,h.products,h.data,h.boundLow,h.boundHigh⟩

theorem pairedZArgs_ok {c secret y unused work : Ptr} {gamma bound : Nat}
    (hc : (Arg.ptr c).Ok) (hs : (Arg.ptr secret).Ok) (hy : (Arg.ptr y).Ok)
    (hu : (Arg.ptr unused).Ok) (hw : (Arg.ptr work).Ok) :
    ∀x∈pairedZArgs c secret y unused work gamma bound,x.2.Ok ∧ x.1∈argRegs := by
  simp only [pairedZArgs,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨hc,by simp⟩
  · exact ⟨hs,by simp⟩
  · exact ⟨hy,by simp⟩
  · exact ⟨hu,by simp⟩
  · exact ⟨hw,by simp⟩
  · exact ⟨True.intro,by simp⟩
  · exact ⟨True.intro,by simp⟩

theorem pairedZAt_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State}
    {c secret y unused work : Ptr} {gamma bound : Nat}
    (hc : (Arg.ptr c).Ok) (hs : (Arg.ptr secret).Ok) (hy : (Arg.ptr y).Ok)
    (hu : (Arg.ptr unused).Ok) (hw : (Arg.ptr work).Ok)
    (h : PairedZReady c secret y work bound s) :
    WP isa (callAt nm (selected .z) (pairedZArgs c secret y unused work gamma bound)) s fun t =>
      Post S s t [⟨pa s y,2048⟩,⟨pa s work,2176⟩] ∧
      (∀j<2,CenteredReduced t.mem (pairPolyPtr (pa s y) j) ∧
        signedPolyAt t.mem (pairPolyPtr (pa s y) j)=add (polyAt s.mem (pairPolyPtr (pa s y) j))
          (pairedProduct s.mem (pa s c) (pa s secret) j)) ∧
      (t.gpr .x0).setWidth 32=if normRq ((List.range 2).map fun j =>
        add (polyAt s.mem (pairPolyPtr (pa s y) j)) (pairedProduct s.mem (pa s c) (pa s secret) j))<bound then 1 else 0 := by
  refine WP.mono (callAtSyms_ok hS (pairedZ_callee S) (pairedZArgs_ok hc hs hy hu hw) (by simp)
    (fun s1 h1 hy => pairedZAt_pre h h1 hy) h.readable h.writable) fun t ⟨hP,s1,h1,hq⟩ => ⟨hP,?_⟩
  have hb : s1.gpr .x6=BitVec.ofNat 64 bound := h1.imm (by simp [pairedZArgs])
  have hb32 := imm32 (v:=bound) (by have := h.boundHigh; omega_using [this])
  sig_post [pairedZContract,pairedZSig,abi,argRegs,pairedConsts_eq,Abi.withConsts] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1,hb,hb32] at hq
  exact hq

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZCallTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedZAt_tr {S : Nat} {nm : String} {c secret out unused work : Ptr} {gamma bound : Nat}
    (hc : (Arg.ptr c).Ok) (hs : (Arg.ptr secret).Ok) (ho : (Arg.ptr out).Ok)
    (hu : (Arg.ptr unused).Ok) (hw : (Arg.ptr work).Ok)
    {Q : State → State → Prop}
    (hQ : ∀x y,Q x y → PairedZReady c secret out work bound x ∧ PairedZReady c secret out work bound y ∧
      pa x c=pa y c ∧ pa x secret=pa y secret ∧ pa x out=pa y out ∧ pa x unused=pa y unused ∧
      pa x work=pa y work ∧ x.sp=y.sp ∧ x.syms "VG_MLDSA_INV_PAIR"=y.syms "VG_MLDSA_INV_PAIR") :
    RelCT isa Q (callAt nm (selected .z) (pairedZArgs c secret out unused work gamma bound)) fun _ _ => True := by
  refine callAtSyms_tr (pairedZ_callee S) (pairedZArgs_ok hc hs ho hu hw) (by simp)
    fun x y x1 y1 hp h1 h2 hy1 hy2 => ?_
  obtain ⟨rx,ry,ec,es,eo,eu,ew,esp,et⟩ := hQ x y hp
  refine ⟨[⟨pa x c,1024⟩,⟨pa x secret,2048⟩,⟨x.syms "VG_MLDSA_INV_PAIR",4096⟩],
    [⟨pa x out,2048⟩,⟨pa x work,2176⟩],pairedZAt_pre rx h1 hy1,?_,?_,rx.readable,rx.writable,?_,?_⟩
  · rw [ec,es,eo,ew,et]
    exact pairedZAt_pre ry h2 hy2
  · sig_pub [pairedZContract,pairedZSig,abi,argRegs,Abi.withConsts,pairedConsts_eq]
    rw [hy1,hy2,Args.r0 h1,Args.r0 h2,Args.r1 h1,Args.r1 h2,Args.r2 h1,Args.r2 h2,
      Args.r3 h1,Args.r3 h2,Args.r4 h1,Args.r4 h2,Args.sp h1,Args.sp h2]
    exact ⟨esp,et,ec,es,eo,eu,ew⟩
  · rw [ec,es,eo,ew,et]; exact ry.readable
  · rw [eo,ew]; exact ry.writable

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
