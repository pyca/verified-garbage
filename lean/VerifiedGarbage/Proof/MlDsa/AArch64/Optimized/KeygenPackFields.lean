import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackField
import VerifiedGarbage.Proof.Framework.Range

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack

structure FieldState where
  mem : Mem
  acc : BitVec 64

def fieldStep (d : Nat) (out : Addr) (value : Nat → BitVec 64) (j : Nat) (s : FieldState) : FieldState :=
  ⟨fieldMem d j s.mem out s.acc (value j),fieldAcc d j s.acc (value j)⟩

def fieldsRun (d : Nat) (out : Addr) (value : Nat → BitVec 64) (s : FieldState) : Nat → FieldState
  | 0 => s
  | j+1 => fieldStep d out value j (fieldsRun d out value s j)

theorem fields_ok (d c : Nat) (hd : d≤20) (hc : c≤8) (s : State)
    (hw : ∀off,off+8≤d*c/8 → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) 8) :
    WP isa (.block ((List.range c).flatMap (field d))) s fun t =>
      Keep [.x9,.x10,.x11] s t ∧ t.v=s.v ∧
      t.mem=(fieldsRun d (s.gpr .x2) (fieldValue s.v) ⟨s.mem,s.gpr .x9⟩ c).mem ∧
      t.gpr .x9=(fieldsRun d (s.gpr .x2) (fieldValue s.v) ⟨s.mem,s.gpr .x9⟩ c).acc := by
  let I := fun j t=>Keep [.x9,.x10,.x11] s t ∧ t.v=s.v ∧
    t.mem=(fieldsRun d (s.gpr .x2) (fieldValue s.v) ⟨s.mem,s.gpr .x9⟩ j).mem ∧
    t.gpr .x9=(fieldsRun d (s.gpr .x2) (fieldValue s.v) ⟨s.mem,s.gpr .x9⟩ j).acc
  refine wp_range_flatMap (M:=isa) I (fun j t hj ht=>?_) c (Nat.le_refl _) s
    ⟨Keep.refl _ _,rfl,rfl,rfl⟩
  rcases ht with ⟨hk,hv,hm,ha⟩
  refine WP.mono (field_ok d j hd (by omega) t ?_) fun u ⟨⟨⟨hu9,hum⟩,hu⟩,huv⟩ => ?_
  · intro hf
    have hprod : d*(j+1)≤d*c := Nat.mul_le_mul_left d (by omega)
    rw [Nat.mul_succ] at hprod
    simpa only [hk.wr,hk.get .x2] using hw (d*j/64*8) (by omega)
  · refine ⟨(hk.trans hu).mono,huv.trans hv,?_,?_⟩
    · rw [hum,hk.get .x2,hv,hm,ha]
      rfl
    · rw [hu9,hv,ha]
      rfl

theorem fieldsRun_values (d : Nat) (out : Addr) (v w : Nat → BitVec 64) (s : FieldState)
    {n : Nat} (h : ∀j<n,v j=w j) : fieldsRun d out v s n=fieldsRun d out w s n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [fieldsRun,fieldsRun,ih (by intro j hj; exact h j (by omega))]
    simp only [fieldStep,h n (by omega)]

theorem fieldsRun_acc_irrel (d : Nat) (hd : d≤20) (out : Addr) (v : Nat → BitVec 64)
    (m : Mem) (a b : BitVec 64) {n : Nat} (hn : 0<n) :
    fieldsRun d out v ⟨m,a⟩ n=fieldsRun d out v ⟨m,b⟩ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : n=0
    · subst n
      have h64 : ¬64≤d := by omega
      have h64' : ¬64<d := by omega
      simp only [fieldsRun,fieldStep,fieldMem,fieldAcc,joined,Nat.mul_zero,Nat.zero_mod,
        Nat.zero_add,h64,h64',↓reduceIte]
    · rw [fieldsRun,fieldsRun,ih (by omega)]

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
