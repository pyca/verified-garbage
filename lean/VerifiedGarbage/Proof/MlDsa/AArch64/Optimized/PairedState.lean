module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Paired
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePackedBank
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem

/-! ### `MlDsa.AArch64.Optimized.PairedShape`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem bank_safe {j : Nat} (hj : j<16) :
    vr j∉([.v24,.v25,.v26,.v27,.v28,.v29,.v30,.v31] : List VReg) := by
  have h : ∀j∈List.range 16,vr j∉([.v24,.v25,.v26,.v27,.v28,.v29,.v30,.v31] : List VReg) := by decide
  exact h j (List.mem_range.mpr hj)

theorem bank_injective {a b : Nat} (ha : a<16) (hb : b<16) (h : vr a=vr b) : a=b := by
  have hi : ∀a b:Fin 16,vr a.val=vr b.val → a=b := by decide
  exact congrArg Fin.val (hi ⟨a,ha⟩ ⟨b,hb⟩ h)

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

/-! ### `MlDsa.AArch64.Optimized.PairedPackedBank`, which only this module used -/

section

/-! ## From `PairedPacked.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.Inverse (gather scatter packedResult)

/-- Packed inverse layers use exact gather/scatter permutations; their
only field multiplication is on the difference branch. -/
theorem packed_ok (a b : VReg) (len : Nat) (hab : a≠b)
    (ha : a∉[.v24,.v25,.v26]) (hb : b∉[.v24,.v25,.v26])
    {s : State} {rest : List Instr} {Q : State → Prop} {z : Nat → Int}
    (hz : ∀ e<4, 0≤z e ∧ z e<8380417)
    (hzw : ∀ e<4, vword (s.v .v28) e=BitVec.ofInt 32 (z e))
    (hbw : ∀ e<4, vword (s.v .v29) e=BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀ e<4, vword (s.v .v31) e=8380417#32)
    (k : ∀ t, VChg [.v24,.v25,.v26,.v27,a,b] s t →
      t.v a=packedResult len false (s.v a) (s.v b) z →
      t.v b=packedResult len true (s.v a) (s.v b) z → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.PairedBase.packed a b len ++ rest)) s Q := by
  have ha16 : a≠.v24 := fun h => ha (by simp [h])
  have ha18 : a≠.v26 := fun h => ha (by simp [h])
  have hb16 : b≠.v24 := fun h => hb (by simp [h])
  simp only [VG.Impl.MlDsa.AArch64.Optimized.PairedBase.packed,
    List.cons_append,List.nil_append]
  refine wp_vop (d := .v24) rfl fun s₁ h₁ => wp_vop (d := .v25) rfl fun s₂ h₂ =>
    wp_vop (d := .v26) rfl fun s₃ h₃ => wp_vop (d := .v24) rfl fun s₄ h₄ => ?_
  have hx : s₂.v .v24=gather len false (s.v a) (s.v b) := by
    rw [h₂.get .v24,h₁.v]
    rfl
  have hy : s₂.v .v25=gather len true (s.v a) (s.v b) := by
    rw [h₂.v,h₁.get a ha16,h₁.get b hb16]
    rfl
  have hd : s₄.v .v26=VArr.s4.map2 (fun _ a b => a-b)
      (gather len false (s.v a) (s.v b)) (gather len true (s.v a) (s.v b)) := by
    rw [h₄.get .v26,h₃.v,hx,hy]
  have hs : s₄.v .v24=VArr.s4.map2 (fun _ a b => a+b)
      (gather len false (s.v a) (s.v b)) (gather len true (s.v a) (s.v b)) := by
    rw [h₄.v,h₃.get .v24,h₃.get .v25,hx,hy]
  refine fastMul_ok (d := .v26) (tmp := .v27) (zr := .v28) (br := .v29) (qr := .v31)
    (by decide) (by decide) (by decide) (by decide) hz ?_ ?_ ?_ fun s₅ hc hv => ?_
  · simpa only [h₄.get .v28,h₃.get .v28,h₂.get .v28,h₁.get .v28] using hzw
  · simpa only [h₄.get .v29,h₃.get .v29,h₂.get .v29,h₁.get .v29] using hbw
  · simpa only [h₄.get .v31,h₃.get .v31,h₂.get .v31,h₁.get .v31] using hqw
  · have hm : s₅.v .v26=fastVector (s₄.v .v26) z := by
      apply VG.AArch64.vec_ext
      intro e he
      rw [hv e he,fastVector_word _ _ he]
    have hf : s₅.v .v24=s₄.v .v24 := hc.get .v24 (by decide)
    by_cases hl : len=1
    · simp only [hl,ite_true]
      refine wp_vop (d := a) rfl fun s₆ h₆ => wp_vop (d := b) rfl fun t h₇ => ?_
      refine k t (VChg.mono (((((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄.chg).trans hc).trans
        (h₆.chg.trans h₇.chg)) ?_) ?_ ?_
      · intro r hr
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
        grind only
      · rw [h₇.get a hab,h₆.v,hf,hm,hd,hs]
        simp [packedResult,scatter,hl]
      · rw [h₇.v,h₆.get .v24 (Ne.symm ha16),h₆.get .v26 (Ne.symm ha18),hf,hm,hd,hs]
        simp [packedResult,scatter,hl]
    · simp only [hl,ite_false]
      refine wp_vop (d := a) rfl fun s₆ h₆ => wp_vop (d := b) rfl fun t h₇ => ?_
      refine k t (VChg.mono (((((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄.chg).trans hc).trans
        (h₆.chg.trans h₇.chg)) ?_) ?_ ?_
      · intro r hr
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
        grind only
      · rw [h₇.get a hab,h₆.v,hf,hm,hd,hs]
        simp [packedResult,scatter,hl]
      · rw [h₇.v,h₆.get .v24 (Ne.symm ha16),h₆.get .v26 (Ne.symm ha18),hf,hm,hd,hs]
        simp [packedResult,scatter,hl]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedPackedBank.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Proof.MlDsa.AArch64.Optimized.Inverse (packedValues)

def packedClobs (r : Vector VReg 8) (i j : Fin 8) : List VReg :=
  [.v24,.v25,.v26,.v27,r[i.val],r[j.val]]

theorem packedBank_ok (r : Vector VReg 8) (i j : Fin 8) (len : Nat) (hij : i ≠ j)
    (hinj : Function.Injective (fun a : Fin 8 => r[a.val]))
    (hsmall : ∀ a : Fin 8, r[a.val]∉[.v24,.v25,.v26,.v27])
    {s : State} {rest : List Instr} {Q : State → Prop} {values : Vector (BitVec 128) 8}
    {z : Nat → Int} (hbank : Bank s r values)
    (hz : ∀ e<4, 0≤z e ∧ z e<8380417)
    (hzw : ∀ e<4, vword (s.v .v28) e=BitVec.ofInt 32 (z e))
    (hbw : ∀ e<4, vword (s.v .v29) e=BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀ e<4, vword (s.v .v31) e=8380417#32)
    (k : ∀ t, VChg (packedClobs r i j) s t →
      Bank t r (packedValues values i j len z) → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.PairedBase.packed r[i.val] r[j.val] len ++ rest)) s Q := by
  have hs (a : Fin 8) : r[a.val]∉[.v24,.v25,.v26] := fun h => hsmall a (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    grind only)
  refine packed_ok _ _ len (fun h => hij (hinj h)) (hs i) (hs j)
    hz hzw hbw hqw fun t hc ha hb => k t hc ?_
  intro a
  simp only [packedValues,Vector.getElem_set]
  by_cases hja : j=a
  · subst a
    simp only [ite_true]
    rw [hb,hbank i,hbank j]
  · have hja' : j.val≠a.val := fun h => hja (Fin.ext h)
    simp only [hja',ite_false]
    by_cases hia : i=a
    · subst a
      simp only [ite_true]
      rw [ha,hbank i,hbank j]
    · have hia' : i.val≠a.val := fun h => hia (Fin.ext h)
      simp only [hia',ite_false]
      rw [hc.get _ ?_,hbank a]
      have hri : r[a.val]≠r[i.val] := fun h => hia (hinj h).symm
      have hrj : r[a.val]≠r[j.val] := fun h => hja (hinj h).symm
      have hm := hsmall a
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hm ⊢
      exact ⟨hm.1,hm.2.1,hm.2.2.1,hm.2.2.2,hri,hrj⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase (vr)

def bankRegs (p : Fin 2) : Vector VReg 8 := Vector.ofFn fun j => vr (8*p.val+j.val)
abbrev Values := Fin 2 → Vector (BitVec 128) 8
def Banks (s : State) (v : Values) : Prop := ∀p,Bank s (bankRegs p) (v p)

theorem bankRegs_inj (p : Fin 2) : Function.Injective (fun j : Fin 8 => (bankRegs p)[j.val]) := by
  intro i j h
  simp only [bankRegs,Vector.getElem_ofFn] at h
  apply Fin.ext
  have he := bank_injective (by omega_using []) (by omega_using []) h
  omega_using [he]

theorem bankRegs_safe (p : Fin 2) (j : Fin 8) :
    (bankRegs p)[j.val]∉[.v24,.v25,.v26,.v27] := by
  have h := bank_safe (j := 8*p.val+j.val) (by omega_using [])
  simp only [bankRegs,Vector.getElem_ofFn,List.mem_cons,List.not_mem_nil,or_false] at *
  grind only

theorem bankRegs_cross (p q : Fin 2) (hpq : p≠q) (i j : Fin 8) :
    (bankRegs p)[i.val]≠(bankRegs q)[j.val] := by
  intro h
  simp only [bankRegs,Vector.getElem_ofFn] at h
  have he := bank_injective (by omega_using []) (by omega_using []) h
  apply hpq
  apply Fin.ext
  omega_using [he]

/-- Updating one bank preserves the entire other polynomial bank. -/
theorem Banks.packed {s t : State} {v : Values} (hs : Banks s v)
    (p : Fin 2) (i j : Fin 8) (len : Nat) (z : Nat → Int)
    (hc : VChg (packedClobs (bankRegs p) i j) s t)
    (hv : Bank t (bankRegs p) (Inverse.packedValues (v p) i j len z)) :
    Banks t (fun q => if q=p then Inverse.packedValues (v p) i j len z else v q) := by
  intro q
  by_cases hp : q=p
  · subst q
    simpa only [ite_true] using hv
  · simp only [hp,ite_false]
    intro k
    rw [hc.get _ ?_,hs q k]
    have ht := bankRegs_safe q k
    have hi := bankRegs_cross q p hp k i
    have hj := bankRegs_cross q p hp k j
    simp only [packedClobs,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only


theorem packedBanks_ok (p : Fin 2) (i j : Fin 8) (len : Nat) (hij : i≠j)
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Values} {z : Nat → Int}
    (hv : Banks s v) (hz : ∀e<4,0≤z e ∧ z e<8380417)
    (hzw : ∀e<4,vword (s.v .v28) e=BitVec.ofInt 32 (z e))
    (hbw : ∀e<4,vword (s.v .v29) e=BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀e<4,vword (s.v .v31) e=8380417#32)
    (k : ∀t,VChg (packedClobs (bankRegs p) i j) s t →
      Banks t (fun q => if q=p then Inverse.packedValues (v p) i j len z else v q) →
      WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.PairedBase.packed
      (bankRegs p)[i.val] (bankRegs p)[j.val] len++rest)) s Q := by
  refine packedBank_ok (bankRegs p) i j len hij (bankRegs_inj p) (bankRegs_safe p)
    (hv p) hz hzw hbw hqw fun t hc ht => ?_
  exact k t hc (hv.packed p i j len z hc ht)

end VG.Proof.MlDsa.AArch64.Optimized.Paired
