module

import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.KeygenPack
import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! ### `MlDsa.AArch64.Optimized.KeygenPackField`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack

def fieldValue (v : VReg → BitVec 128) (j : Nat) : BitVec 64 :=
  (vword (v (if j<4 then .v0 else .v1)) (j%4)).setWidth 64

def joined (d j : Nat) (acc value : BitVec 64) : BitVec 64 :=
  if d*j%64=0 then value else acc ||| (value <<< (d*j%64))

def fieldAcc (d j : Nat) (acc value : BitVec 64) : BitVec 64 :=
  if d*j%64+d>64 then value >>> (64-d*j%64) else joined d j acc value

def fieldMem (d j : Nat) (m : Mem) (out : Addr) (acc value : BitVec 64) : Mem :=
  if d*j%64+d≥64 then m.writeW (out+BitVec.ofNat 64 (d*j/64*8)) (joined d j acc value) else m

theorem field_ok (d j : Nat) (hd : d≤20) (hj : j<8) (s : State)
    (hw : d*j%64+d≥64 → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 (d*j/64*8)) 8) :
    WP isa (.block (field d j)) s fun t =>
      ((t.gpr .x9=fieldAcc d j (s.gpr .x9) (fieldValue s.v j) ∧
        t.mem=fieldMem d j s.mem (s.gpr .x2) (s.gpr .x9) (fieldValue s.v j)) ∧
       Keep [.x9,.x10,.x11] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by dsimp only [field]; (repeat' split) <;> rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by dsimp only [field]; (repeat' split) <;> rfl) (hv:=by dsimp only [field]; (repeat' split) <;> rfl)
  have hs : d*j%64<64 := Nat.mod_lt _ (by decide)
  have hj4 : j%4<4 := Nat.mod_lt _ (by decide)
  have hidx : j%4*32<128 := by omega_using []
  have hd64 : ¬64≤d := by omega_using [hd]
  have hd64' : ¬64<d := by omega_using [hd]
  have hprod : d*j≤20*7 := Nat.mul_le_mul hd (by omega_using [hj])
  have ho : d*j/64*8<4096*8 := by omega_using [hprod]
  have ho8 : d*j/64*8%8=0 := by omega_using []
  by_cases hzero : d*j%64=0
  · by_cases hfull : d*j%64+d≥64
    · omega
    · have hnot : ¬d*j%64+d>64 := by omega_using [hd, hzero]
      simp only [field,hzero,↓reduceIte,List.cons_append,List.nil_append,fieldAcc,joined,fieldMem]
      arun [Option.bind_some,exec,Impl.MlKem.AArch64.mov,addr,Size.bytes,State.store,State.read,Mem.writeW,fieldValue,vword,hidx,Nat.zero_add,hd64,hd64']
  · by_cases hfull : d*j%64+d≥64
    · by_cases hcross : d*j%64+d>64
      · have hshift : 64-d*j%64<64 := by omega_using [hd, hj, hs, hj4, hidx, hd64, hd64', hprod, ho, ho8, hzero, hfull, hcross]
        simp only [field,hzero,hfull,hcross,↓reduceIte,List.cons_append,List.nil_append,fieldAcc,joined,fieldMem]
        arun [Option.bind_some,exec,Impl.MlKem.AArch64.mov,addr,Size.bytes,State.store,State.read,Mem.writeW,fieldValue,vword,hidx,hw hfull,hs,ho,ho8,hshift]
      · simp only [field,hzero,hfull,hcross,↓reduceIte,List.cons_append,List.nil_append,fieldAcc,joined,fieldMem]
        arun [Option.bind_some,exec,Impl.MlKem.AArch64.mov,addr,Size.bytes,State.store,State.read,Mem.writeW,fieldValue,vword,hidx,hw hfull,hs,ho,ho8]
    · have hcross : ¬d*j%64+d>64 := by omega_using [hfull]
      simp only [field,hzero,hfull,hcross,↓reduceIte,List.cons_append,List.nil_append,fieldAcc,joined,fieldMem]
      arun [Option.bind_some,exec,Impl.MlKem.AArch64.mov,addr,Size.bytes,State.store,State.read,Mem.writeW,fieldValue,vword,hidx,hs]

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

end

@[expose] public section

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
  refine WP.mono (field_ok d j hd (by omega_using [hc, hj]) t ?_) fun u ⟨⟨⟨hu9,hum⟩,hu⟩,huv⟩ => ?_
  · intro hf
    have hprod : d*(j+1)≤d*c := Nat.mul_le_mul_left d (by omega_using [hj])
    rw [Nat.mul_succ] at hprod
    simpa only [hk.wr,hk.get .x2] using hw (d*j/64*8) (by omega_using [hf, hprod])
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
    rw [fieldsRun,fieldsRun,ih (by intro j hj; exact h j (by omega_using [hj]))]
    simp only [fieldStep,h n (by omega_using [])]

theorem fieldsRun_acc_irrel (d : Nat) (hd : d≤20) (out : Addr) (v : Nat → BitVec 64)
    (m : Mem) (a b : BitVec 64) {n : Nat} (hn : 0<n) :
    fieldsRun d out v ⟨m,a⟩ n=fieldsRun d out v ⟨m,b⟩ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : n=0
    · subst n
      have h64 : ¬64≤d := by omega_using [hd]
      have h64' : ¬64<d := by omega_using [hd]
      simp only [fieldsRun,fieldStep,fieldMem,fieldAcc,joined,Nat.mul_zero,Nat.zero_mod,
        Nat.zero_add,h64,h64',↓reduceIte]
    · rw [fieldsRun,fieldsRun,ih (by omega_using [h])]

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
