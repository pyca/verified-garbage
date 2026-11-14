module
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Batch
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Scalar
import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Parse
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Spec.MlKem

/-! ### `MlKem.AArch64.Rej8Steps`, which only this module used -/

section

/-! ### `MlKem.AArch64.Rej8Prefix`, which only this module used -/

section

/-! ### `MlKem.AArch64.Rej8Memory`, which only this module used -/

section

/-! # Polynomial-prefix effects of the vector rejection stores -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem

theorem coeffAddr_add (p : Addr) (j k : Nat) :
    coeffAddr p j + BitVec.ofNat 64 (4*k) = coeffAddr p (j+k) := by
  simp only [coeffAddr,ptr_add,Nat.mul_add]

/-- A vector store changes exactly four consecutive polynomial words. -/
theorem coeffAt_write16 (m : Mem) (p : Addr) (x : BitVec 128) {i j : Nat}
    (hi : i<256) (hj : j+4≤256) :
    coeffAt (m.write (coeffAddr p j) 16 x) p i =
      if j≤i ∧ i<j+4 then vword x (i-j) else coeffAt m p i := by
  rw [← ofVWords_vword x,write16]
  have h4 : coeffAddr p j+BitVec.ofNat 64 4=coeffAddr p (j+1) := coeffAddr_add p j 1
  have h8 : coeffAddr p j+BitVec.ofNat 64 8=coeffAddr p (j+2) := coeffAddr_add p j 2
  have h12 : coeffAddr p j+BitVec.ofNat 64 12=coeffAddr p (j+3) := coeffAddr_add p j 3
  rw [h4,h8,h12,
    coeffAt_writeW _ p (show i<n from hi) (show j+3<n by change j+3<256; omega_using [hj]),
    coeffAt_writeW _ p (show i<n from hi) (show j+2<n by change j+2<256; omega_using [hj]),
    coeffAt_writeW _ p (show i<n from hi) (show j+1<n by change j+1<256; omega_using [hj]),
    coeffAt_writeW _ p (show i<n from hi) (show j<n by change j<256; omega_using [hj])]
  rw [ofVWords_vword]
  by_cases h3 : j+3=i
  · rw [ite_eq_left h3,ite_eq_left (by omega_using [h3]),show i-j=3 by omega_using [h3]]
  · rw [ite_eq_right h3]
    by_cases h2 : j+2=i
    · rw [ite_eq_left h2,ite_eq_left (by omega_using [h2]),show i-j=2 by omega_using [h2]]
    · rw [ite_eq_right h2]
      by_cases h1 : j+1=i
      · rw [ite_eq_left h1,ite_eq_left (by omega_using [h1]),show i-j=1 by omega_using [h1]]
      · rw [ite_eq_right h1]
        by_cases h0 : j=i
        · rw [ite_eq_left h0,ite_eq_left (by omega_using [h0]),show i-j=0 by omega_using [h0]]
        · rw [ite_eq_right h0,ite_eq_right (by omega_using [h3, h2, h1, h0])]

/-- The two stores affect exactly the eight-word reservation, even when
only some of those slots contain accepted coefficients. -/
theorem coeffAt_updatedMem (s : State) {p : Addr} {j i : Nat}
    (h3 : s.gpr .x3=coeffAddr p j) (hj : j+8≤256) (hi : i<256) :
    coeffAt (updatedMem s) p i =
      if j≤i ∧ i<j+4 then vword (wideLo (compactValue (candidatesAt s) (maskAt s)) (s.v .v21)) (i-j)
      else if j+4≤i ∧ i<j+8 then vword (wideHi (compactValue (candidatesAt s) (maskAt s)) (s.v .v21)) (i-(j+4))
      else coeffAt s.mem p i := by
  rw [updatedMem,ite_eq_right Bool.false_ne_true,h3,show coeffAddr p j+16=coeffAddr p (j+4) from coeffAddr_add p j 4,
    coeffAt_write16 _ _ _ hi (by omega_using [hj]),coeffAt_write16 _ _ _ hi (by omega_using [hj])]
  have h : j+4+4=j+8 := by omega_using []
  rw [h]
  by_cases hlo : j≤i ∧ i<j+4
  · rw [ite_eq_right (by omega_using [hlo]),ite_eq_left hlo,ite_eq_left hlo]
  · rw [ite_eq_right hlo]
    by_cases hhi : j+4≤i ∧ i<j+8
    · simp only [ite_eq_left hhi,ite_eq_right hlo]
    · simp only [ite_eq_right hhi,ite_eq_right hlo]

/-- Coefficient `i` after the stores of a batch at coefficient `j`, with either width: the
accepted candidates in order from `j`, zeros after them up to `j + 8`, and the coefficients
before. -/
theorem coeffAtW_updatedMem (w16 : Bool) (s : State) {p : Addr} {j i : Nat}
    (h3 : s.gpr .x3 = cAddr w16 p j) (hj : j+8≤256) (hi : i<256) (hz : ∀ i<8, vhalf (s.v .v21) i=0) :
    (coeffAtW (cw w16) (updatedMem s w16) p i).toNat =
      if j≤i ∧ i<j+8 then
        (if i-j < acceptedCount s then
          (vhalf (candidatesAt s) ((Impl.MlKem.AArch64.Rej8.acceptedLanes (maskAt s)).getD (i-j) 0)).toNat
        else 0)
      else (coeffAtW (cw w16) s.mem p i).toNat := by
  have hm : maskAt s<256 := acceptanceMask_bound (candidatesAt s)
  cases w16
  · show (coeffAt (updatedMem s) p i).toNat = _
    rw [coeffAt_updatedMem s h3 hj hi]
    by_cases hlo : j≤i ∧ i<j+4
    · rw [ite_eq_left hlo, ite_eq_left ⟨hlo.1, by omega_using [hlo]⟩,
        (widened_coeffs (candidatesAt s) (s.v .v21) hm hz (i := i-j) (by omega_using [hlo])).1]
      simp only [acceptedCount]
      by_cases c : i-j < (Impl.MlKem.AArch64.Rej8.acceptedLanes (maskAt s)).length <;> simp [c]
    · rw [ite_eq_right hlo]
      by_cases hhi : j+4≤i ∧ i<j+8
      · rw [ite_eq_left hhi, ite_eq_left ⟨by omega_using [hhi], hhi.2⟩,
          (widened_coeffs (candidatesAt s) (s.v .v21) hm hz (i := i-(j+4)) (by omega_using [hhi])).2,
          show 4+(i-(j+4)) = i-j by omega_using [hhi]]
        simp only [acceptedCount]
        by_cases c : i-j < (Impl.MlKem.AArch64.Rej8.acceptedLanes (maskAt s)).length <;> simp [c]
      · rw [ite_eq_right hhi, ite_eq_right (by omega_using [hlo, hhi])]
        rfl
  · show (coeffAtW 16 (updatedMem s true) p i).toNat = _
    rw [show updatedMem s true = s.mem.write (s.gpr .x3) 16 (compactValue (candidatesAt s) (maskAt s)) from rfl,
      h3, show cAddr true p j = p + BitVec.ofNat 64 (2*j) from rfl, coeffAtW16_write _ _ hj hi]
    by_cases c : j≤i ∧ i<j+8
    · rw [ite_eq_left c, ite_eq_left c, compact_half _ hm (by omega_using [c])]
      simp only [acceptedCount]
      by_cases c' : i-j < (Impl.MlKem.AArch64.Rej8.acceptedLanes (maskAt s)).length <;> simp [c']
    · rw [ite_eq_right c, ite_eq_right c]
      rfl

end VG.Proof.MlKem.AArch64.Rej8

end

end


/-! # The batch appends exactly the accepted coefficients to the existing prefix -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Rej8
open VG.Proof.MlKem.AArch64.Sample (cv)

def acceptedValues (s : State) : List Zq :=
  (acceptedLanes (maskAt s)).map fun i => ofNat (vhalf (candidatesAt s) i).toNat

theorem acceptedValues_length (s : State) : (acceptedValues s).length=acceptedCount s := by
  simp only [acceptedValues,acceptedCount,List.length_map]

theorem accepted_value_lt (s : State) {k : Nat} (hk : k<acceptedCount s) :
    (vhalf (candidatesAt s) ((acceptedLanes (maskAt s)).getD k 0)).toNat < 3329 := by
  have hm : (acceptedLanes (maskAt s)).getD k 0 ∈ acceptedLanes (maskAt s) := by
    have h := List.getElem_mem (l := acceptedLanes (maskAt s)) hk
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,Option.getD_some] using h
  have hi := accepted_mem hm
  have hb := (List.mem_filter.mp hm).2
  change ((acceptanceMask (candidatesAt s) / 2^((acceptedLanes (maskAt s)).getD k 0))%2 == 1) = true at hb
  rw [acceptanceMask_bits _ hi] at hb
  exact of_decide_eq_true hb

/-- Stores beyond the compacted prefix are irrelevant: later batches may
overwrite them, and bounded failure clears the entire remaining suffix. -/
theorem append_cvW {w16 : Bool} {L R : List Zq} {i : Nat} (hi : L.length≤i) :
    Sample.cvW w16 (L++R) i=Sample.cvW w16 R (i-L.length) := by
  simp only [Sample.cvW,List.getD_eq_getElem?_getD,List.getElem?_append_right hi]

theorem append_cvW_left {w16 : Bool} {L R : List Zq} {i : Nat} (hi : i<L.length) :
    Sample.cvW w16 (L++R) i=Sample.cvW w16 L i := by
  simp only [Sample.cvW,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

/-- `batch_prefix` with either width. -/
theorem batch_prefixW (w16 : Bool) (s : State) {p : Addr} {L : List Zq}
    (h3 : s.gpr .x3=cAddr w16 p L.length) (hroom : L.length+8≤256)
    (hz : ∀i<8,vhalf (s.v .v21) i=0) (hp : Scalar.CoeffsW w16 s.mem p L) :
    Scalar.CoeffsW w16 (updatedMem s w16) p (L++acceptedValues s) := by
  intro i hi
  have hn : acceptedCount s≤8 := accepted_length (maskAt s)
  have hlen : i<L.length+acceptedCount s := by
    simpa only [List.length_append,acceptedValues_length] using hi
  have hi256 : i<256 := by omega_using [hroom, hn, hlen]
  apply BitVec.eq_of_toNat_eq
  rw [coeffAtW_updatedMem w16 s h3 hroom hi256 hz]
  by_cases hbefore : i<L.length
  · rw [ite_eq_right (by omega_using [hbefore]),hp i hbefore,append_cvW_left hbefore]
  · have hk : i-L.length<acceptedCount s := by omega_using [hlen, hbefore]
    rw [ite_eq_left ⟨by omega_using [hbefore],by omega_using [hn, hlen]⟩,ite_eq_left hk,append_cvW (by omega_using [hbefore])]
    have hv := accepted_value_lt s hk
    have he : (acceptedValues s).getD (i-L.length) 0 =
        ofNat (vhalf (candidatesAt s) ((acceptedLanes (maskAt s)).getD (i-L.length) 0)).toNat := by
      simp only [acceptedValues,List.getD_eq_getElem?_getD,List.getElem?_map,
        List.getElem?_eq_getElem (show i-L.length<(acceptedLanes (maskAt s)).length from hk),
        Option.map_some,Option.getD_some]
    have hq : q = 3329 := rfl
    simp only [Sample.cvW,he,BitVec.toNat_ofNat,val_ofNat]
    cases w16 <;> simp only [cw,Bool.false_eq_true,ite_false,ite_true,Nat.reducePow,hq] <;> omega_using [hv]

end VG.Proof.MlKem.AArch64.Rej8

end

end

/-! # Stable vector rejection agrees with successive scalar sampling steps -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Rej8Decode.lean`, which only this module imported.
section

/-! # Agreement between packed candidates and the specified byte decoder -/

section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem

private theorem three_toNat (m : Mem) (p : Addr) :
    (m.read p 3).toNat = (m p).toNat+256*(m (p+1)).toNat+65536*(m (p+2)).toNat := by
  simp only [Mem.read,BitVec.toNat_append]
  have he : p+1+1=p+2 := by bv_omega
  rw [he]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (m p).isLt,
      ← Nat.shiftLeft_add_eq_or_of_lt (m (p+1)).isLt,
      ← Nat.shiftLeft_add_eq_or_of_lt (m (p+2)).isLt]
  simp only [Nat.shiftLeft_eq,show (0#0).toNat=0 from rfl]
  omega

theorem candidate_even (m : Mem) (p : Addr) (j : Nat) :
    (candidate m p (2*j)).toNat =
      (m (p+BitVec.ofNat 64 (3*j))).toNat +
        256*((m (p+BitVec.ofNat 64 (3*j)+1)).toNat%16) := by
  simp only [candidate, Nat.mul_div_cancel_left _ (by decide : 0<2),
    Nat.mul_mod_right, Nat.mul_zero,BitVec.toNat_setWidth_of_le (by decide : 12≤16),
    BitVec.extractLsb'_toNat,Nat.shiftRight_zero,three_toNat]
  have h0 := (m (p+BitVec.ofNat 64 (3*j))).isLt
  omega

theorem candidate_odd (m : Mem) (p : Addr) (j : Nat) :
    (candidate m p (2*j+1)).toNat =
      (m (p+BitVec.ofNat 64 (3*j)+1)).toNat/16 +
        16*(m (p+BitVec.ofNat 64 (3*j)+2)).toNat := by
  have hd : (2*j+1)/2=j := by omega
  have hm : (2*j+1)%2=1 := by omega
  simp only [candidate,hd,hm,Nat.mul_one,BitVec.toNat_setWidth_of_le (by decide : 12≤16),
    BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,three_toNat]
  have h0 := (m (p+BitVec.ofNat 64 (3*j))).isLt
  have h1 := (m (p+BitVec.ofNat 64 (3*j)+1)).isLt
  have h2 := (m (p+BitVec.ofNat 64 (3*j)+2)).isLt
  omega

end VG.Proof.MlKem.AArch64.Rej8
end

end

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Impl.MlKem.AArch64.Rej8

def acceptValue (L : List Zq) (v : Nat) : List Zq :=
  if v<q then L++[ofNat v] else L

theorem acceptValue_length (L : List Zq) (v : Nat) :
    (acceptValue L v).length≤L.length+1 := by
  unfold acceptValue
  split <;> simp_all

theorem fold_accept (L : List Zq) (is : List Nat) (f : Nat → Nat) :
    is.foldl (fun a i => acceptValue a (f i)) L =
      L++((is.filter fun i => decide (f i<q)).map fun i => ofNat (f i)) := by
  induction is generalizing L with
  | nil => simp
  | cons i is ih =>
    simp only [List.foldl_cons,ih,List.filter_cons]
    unfold acceptValue
    by_cases h : f i<q <;> simp [h,List.append_assoc]

theorem acceptedValues_filter (s : State) :
    acceptedValues s =
      ((List.range 8).filter fun i => decide ((candidate s.mem (s.gpr .x2) i).toNat<q)).map
        fun i => ofNat (candidate s.mem (s.gpr .x2) i).toNat := by
  unfold acceptedValues acceptedLanes
  have hf : (List.range 8).filter (fun i => (maskAt s / 2^i)%2 == 1) =
      (List.range 8).filter (fun i => decide ((candidate s.mem (s.gpr .x2) i).toNat<q)) := by
    apply List.filter_congr
    intro i hi
    have hb : i<8 := List.mem_range.mp hi
    rw [maskAt,acceptanceMask_bits _ hb]
    rw [candidatesAt,parsed_candidate _ _ hb]
  rw [hf]
  apply List.map_congr_left
  intro i hi
  have hb : i<8 := List.mem_range.mp (List.mem_filter.mp hi).1
  rw [candidatesAt,parsed_candidate _ _ hb]

theorem sampleStepCap_accept {L : List Zq} (h : L.length+2≤256) (a b c : Byte) :
    sampleStepCap L a b c =
      acceptValue (acceptValue L (a.toNat+256*(b.toNat%16))) (b.toNat/16+16*c.toNat) := by
  have hn : n=256 := rfl
  have hl : L.length≠n := by omega_using [h, hn]
  have hlen := acceptValue_length L (a.toNat+256*(b.toNat%16))
  have hroom : (acceptValue L (a.toNat+256*(b.toNat%16))).length<n := by omega_using [h, hn, hlen]
  simp only [sampleStepCap,ite_eq_right hl,sampleStep,acceptValue] at *
  simp only [hroom,and_true]


theorem four_steps (L : List Zq) (B : Nat → Byte) (h : L.length+8≤256) :
    sampleAfter L B 4 =
      [(B 0).toNat+256*((B 1).toNat%16), (B 1).toNat/16+16*(B 2).toNat,
       (B 3).toNat+256*((B 4).toNat%16), (B 4).toNat/16+16*(B 5).toNat,
       (B 6).toNat+256*((B 7).toNat%16), (B 7).toNat/16+16*(B 8).toNat,
       (B 9).toNat+256*((B 10).toNat%16), (B 10).toNat/16+16*(B 11).toNat].foldl
        acceptValue L := by
  let a₁ := acceptValue L ((B 0).toNat+256*((B 1).toNat%16))
  let a₂ := acceptValue a₁ ((B 1).toNat/16+16*(B 2).toNat)
  let a₃ := acceptValue a₂ ((B 3).toNat+256*((B 4).toNat%16))
  let a₄ := acceptValue a₃ ((B 4).toNat/16+16*(B 5).toNat)
  let a₅ := acceptValue a₄ ((B 6).toNat+256*((B 7).toNat%16))
  let a₆ := acceptValue a₅ ((B 7).toNat/16+16*(B 8).toNat)
  have h₁ : a₁.length≤L.length+1 := acceptValue_length _ _
  have h₂ : a₂.length≤a₁.length+1 := acceptValue_length _ _
  have h₃ : a₃.length≤a₂.length+1 := acceptValue_length _ _
  have h₄ : a₄.length≤a₃.length+1 := acceptValue_length _ _
  have h₅ : a₅.length≤a₄.length+1 := acceptValue_length _ _
  have h₆ : a₆.length≤a₅.length+1 := acceptValue_length _ _
  simp only [sampleAfter]
  rw [sampleStepCap_accept (by omega_using [h] : L.length+2≤256)]
  change sampleStepCap (sampleStepCap (sampleStepCap a₂ _ _ _) _ _ _) _ _ _ = _
  rw [sampleStepCap_accept (by omega_using [h, h₁, h₂] : a₂.length+2≤256)]
  change sampleStepCap (sampleStepCap a₄ _ _ _) _ _ _ = _
  rw [sampleStepCap_accept (by omega_using [h, h₁, h₂, h₃, h₄] : a₄.length+2≤256)]
  change sampleStepCap a₆ _ _ _ = _
  rw [sampleStepCap_accept (by omega_using [h, h₁, h₂, h₃, h₄, h₅, h₆] : a₆.length+2≤256)]
  rfl


theorem batch_steps (s : State) (L : List Zq) (h : L.length+8≤256) :
    L++acceptedValues s = sampleAfter L (fun i => s.mem (s.gpr .x2+BitVec.ofNat 64 i)) 4 := by
  rw [acceptedValues_filter,←fold_accept]
  rw [four_steps L _ h]
  change [0,1,2,3,4,5,6,7].foldl
    (fun a i => acceptValue a (candidate s.mem (s.gpr .x2) i).toNat) L = _
  simp only [List.foldl_cons,List.foldl_nil]
  rw [candidate_even _ _ 0,candidate_odd _ _ 0,
    candidate_even _ _ 1,candidate_odd _ _ 1,
    candidate_even _ _ 2,candidate_odd _ _ 2,
    candidate_even _ _ 3,candidate_odd _ _ 3]
  simp only [BitVec.add_assoc]
  rfl

end VG.Proof.MlKem.AArch64.Rej8

end

end


/-! # Vector-batch preservation of the scalar rejection invariant -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem sampleAfter_add (L : List Zq) (B : Nat → Byte) (t k : Nat) :
    sampleAfter (sampleAfter L B t) (fun i => B (3*t+i)) k=sampleAfter L B (t+k) := by
  induction k with
  | zero => simp only [sampleAfter_zero,Nat.add_zero]
  | succ k ih =>
    rw [sampleAfter_succ,ih,show t+(k+1)=(t+k)+1 by omega_using [],sampleAfter_succ]
    congr 1 <;> congr 1 <;> omega_using []

theorem batch_frameW (w16 : Bool) (s : State) {aP : Addr} {L : List Zq}
    (h3 : s.gpr .x3=cAddr w16 aP L.length) (hroom : L.length+8≤256) :
    Frame [polyRegion aP] s.mem (updatedMem s w16) := by
  cases w16
  · unfold updatedMem
    rw [ite_eq_right Bool.false_ne_true]
    apply Frame.write (r := polyRegion aP) (Frame.write (r := polyRegion aP) (Frame.refl _ _) (by simp) _ ?_) (by simp) _ ?_
    · rw [h3]
      exact contains_off (by simp only [cs_eq, Bool.false_eq_true, ite_false]; omega_using [hroom]) (by decide)
    · rw [h3]
      change (polyRegion aP).Contains (aP+BitVec.ofNat 64 (4*L.length)+BitVec.ofNat 64 16) 16
      rw [ptr_add]
      exact contains_off (by omega_using [hroom]) (by decide)
  · unfold updatedMem
    rw [ite_eq_left rfl]
    refine Frame.write (r := polyRegion aP) (Frame.refl _ _) (by simp) _ ?_
    rw [h3]
    exact contains_off (by simp only [cs_eq, ite_true]; omega_using [hroom]) (by decide)

theorem batch_invW {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte}
    {bP aP : Addr} {s₀ s u : State} (h : Scalar.InvW w16 initial N B bP aP s₀ t s)
    (hroom : (Scalar.LA initial B t).length+8≤256)
    (hz : ∀i<8,vhalf (s.v .v21) i=0)
    (hb : ∀i<12,s.mem (s.gpr .x2+BitVec.ofNat 64 i)=B (3*t+i))
    (hp : BatchPostW w16 s u) : Scalar.InvW w16 initial N B bP aP s₀ (t+4) u := by
  have he : Scalar.LA initial B t++acceptedValues s=Scalar.LA initial B (t+4) := by
    rw [batch_steps s _ hroom,sampleAfter_congr _ hb,sampleAfter_add]
  have hlen : (Scalar.LA initial B (t+4)).length=
      (Scalar.LA initial B t).length+acceptedCount s := by
    rw [←he,List.length_append,acceptedValues_length]
  have hcount : acceptedCount s≤8 := accepted_length _
  refine ⟨⟨hp.keep.rd.trans h.acc.rd,hp.keep.wr.trans h.acc.wr,hp.keep.sp.trans h.acc.sp,
    by omega_using [hroom, hlen, hcount],?_,?_,?_,?_,?_,⟩,(h.keep.trans hp.keep).mono (by decide),?_,?_,?_⟩
  · rw [hp.output,h.acc.x3,cAddr_add,hlen]
  · rw [hp.remain,h.acc.x4,hlen]
    omega_using []
  · rw [hp.keep.get .x9,h.acc.x9]
  · rw [hp.mem,←he]
    exact batch_prefixW w16 s h.acc.x3 hroom hz h.acc.coeffs
  · rw [hp.mem]
    exact h.acc.frame.trans (batch_frameW w16 s h.acc.x3 hroom)
  · rw [hp.input,h.x2]
    change bP+BitVec.ofNat 64 (3*t)+BitVec.ofNat 64 12=_
    rw [ptr_add]
    congr 2
  · rw [hp.chunks,h.x5]
    omega_using []
  · rw [hp.keep.get .x10,h.x10]

end VG.Proof.MlKem.AArch64.Rej8
