module

public import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeStoreCopy
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildGroup
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildDoubleCode
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleOutput

/-! ### `Weierstrass.AArch64.P521Native.BuildFrame`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64

def buildStoreCopy (r : Reg) : Nat → Nat → Nat → List Instr
  | 0,_,_ => []
  | n+1,a,o => .ldr .x .x1 .x0 a :: .str .x .x1 r o :: buildStoreCopy r n (a+8) (o+8)

theorem build_store_copy_ok {base table : Addr} {W cap : Nat} {r : Reg} (hr : r≠.x1)
    (apart : Region.Disjoint ⟨base,W⟩ ⟨table,cap⟩) :
    ∀n {s : State} {a o : Nat},Scr s base W → PtrW s r table cap →
      a+8*n≤W → o+8*n≤cap → a%8=0 → o%8=0 →
      WP isa (.block (buildStoreCopy r n a o)) s fun t =>
        wordsVal t.mem table o n=wordsVal s.mem base a n ∧ KeepRegs [.x1] s t ∧
        VG.Proof.Mont.Outside table o (8*n) s.mem t.mem
  | 0,s,a,o,_,_,_,_,_,_ => WP.block_nil ⟨rfl,⟨fun _ _ => rfl,rfl,rfl,rfl⟩,VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | n+1,s,a,o,hs,pt,ha,ho,ha8,ho8 => by
    change WP isa (.block (([.ldr .x .x1 .x0 a] : List Instr)++
      (([.str .x .x1 r o] : List Instr)++buildStoreCopy r n (a+8) (o+8)))) s _
    rw [WP.block_append_iff]
    refine WP.mono (ldR_ok hs.ptr (d:=a) (by omega_arith) ha8 .x1) fun u ⟨loaded,ku,_⟩ => ?_
    have ptu := pt.of_keepRegs (Keeps.regs ku) (by simpa only [List.mem_singleton] using hr)
    rw [WP.block_append_iff]
    refine WP.mono (stR_ok ptu (d:=o) (by omega_arith) ho8 .x1) fun v stored => ?_
    have kv : KeepRegs [.x1] s v := by
      rw [stored]
      exact ⟨ku.gpr,ku.rd,ku.wr,ku.sp⟩
    have ov : VG.Proof.Mont.Outside table o 8 s.mem v.mem := by
      rw [stored,ku.mem]
      exact VG.Proof.Mont.writeW_outside s.mem table (d:=o) (u.gpr .x1) (by have e:=pt.enc; omega_arith)
    have first : VG.Proof.Mont.word v.mem table o=VG.Proof.Mont.word s.mem base a := by
      rw [stored,VG.Proof.Mont.word_writeW_self,loaded]
    have hsv := hs.of_keepRegs kv (by decide)
    have ptv := pt.of_keepRegs kv (by simpa only [List.mem_singleton] using hr)
    refine WP.mono (build_store_copy_ok hr apart n hsv ptv (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith)) fun t ⟨tail,kt,ot⟩ => ?_
    have wordSaved : VG.Proof.Mont.word t.mem table o=VG.Proof.Mont.word v.mem table o := ot.word (Or.inl (by omega_arith)) (by have e:=pt.enc; omega_arith)
    have workspaceUnchanged : Unch base [(W,2^64)] s.mem v.mem :=
      (ov.mono (by omega_arith : 0≤o) (by omega_arith : o+8≤0+cap)).unch_far apart
    have sourceSame := workspaceUnchanged.wordsVal (d:=a+8) (k:=n)
      (by intro w hw; rw [List.mem_singleton.mp hw]; exact Or.inl (by omega_arith))
      (by have h:=hs.enc; omega_arith)
    refine ⟨?_,kv.trans kt,?_⟩
    · simp only [VG.Proof.Mont.wordsVal]
      rw [wordSaved,first,tail,sourceSame]
    · exact (ov.mono (by omega_arith) (by omega_arith)).trans (ot.mono (by omega_arith) (by omega_arith))


end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native
open VG.Proof.Weierstrass.AArch64.Mont (off_off)

def buildCopyPoint : List Instr := copyPt 9 ⟨1504,1576,1648⟩ ⟨1288,1360,1432⟩

theorem build_copy_source15 : (outerBlock015.drop 338).take 54=buildCopyPoint := by lit_decide

theorem build_copy_source27 : (outerBlock027.drop 55).take 54=buildCopyPoint := by lit_decide

theorem build_store_source15 : (outerBlock015.drop 284).take 54=buildStoreCopy .x20 27 1288 0 := by lit_decide

theorem build_store_source27 : (outerBlock027.drop 1).take 54=buildStoreCopy .x20 27 1288 0 := by lit_decide

theorem build_copy_point_ok {base : Addr} {s : State} (hs : Scr s base 8192) :
    WP isa (.block buildCopyPoint) s fun t =>
      wordsVal t.mem base 1504 9=wordsVal s.mem base 1288 9 ∧
      wordsVal t.mem base 1576 9=wordsVal s.mem base 1360 9 ∧
      wordsVal t.mem base 1648 9=wordsVal s.mem base 1432 9 ∧
      KeepRegs [.x1] s t ∧ Unch base [(1504,72),(1576,72),(1648,72)] s.mem t.mem := by
  exact VG.Proof.Weierstrass.AArch64.copyPt_ok hs (n:=9)
    (o:=⟨1504,1576,1648⟩) (a:=⟨1288,1360,1432⟩)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem build_output_ptr {s : State} {table : Addr} {e : Nat}
    (pt : PtrW s .x26 table 3456) (he : e+216≤3456) (g : s.gpr .x20=off table e) :
    PtrW s .x20 (off table e) 216 := by
  refine ⟨g,?_,by decide,?_⟩
  · intro d hd
    change InRegions s.wr (off (off table e) d) 8
    rw [off_off]
    exact pt.st (e+d) (by omega_arith)
  · have hn := pt.nowrap
    have he64 : e<2^64 := by omega_arith
    have hf : table.toNat+e<2^64 := by omega_arith
    change (table + BitVec.ofNat 64 e).toNat + 216 ≤ 2^64
    rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt he64,Nat.mod_eq_of_lt hf]
    omega_arith

theorem build_output_apart {base table : Addr} {W e : Nat}
    (apart : Region.Disjoint ⟨base,W⟩ ⟨table,3456⟩) (he : e+216≤3456) :
    Region.Disjoint ⟨base,W⟩ ⟨off table e,216⟩ := apart.sub_right (VG.Offset.sub_base table he)

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass

theorem build_double_verified {s : State} {base : Addr} {W : Nat}
    (hs : Scr s base W) (hW : 4024≤W) (hMax : W≤8192)
    (px : wordsVal s.mem base 2800 9<fieldPrime)
    (py : wordsVal s.mem base 3160 9<fieldPrime)
    (pz : wordsVal s.mem base 424 9<fieldPrime) :
    WP isa buildDoubleMachine s fun t =>
      canonicalPoint t.mem base 1288 ∧
      ordinaryPoint t.mem base 1288=dblJF (Fin.ofNat fieldPrime (wordsVal s.mem base 2800 9))
        (Fin.ofNat fieldPrime (wordsVal s.mem base 3160 9)) (Fin.ofNat fieldPrime (wordsVal s.mem base 424 9)) ∧
      Scr t base W ∧ FieldPublic s t ∧ FieldProgramFrame base id buildDoubleOps s.mem t.mem := by
  let E : Nat → Fin fieldPrime := fun d => Fin.ofNat fieldPrime (wordsVal s.mem base d 9)
  have inv : OrdinaryInv base fieldPrime id [2800,3160,424] E (fun _ => 1) s := by
    constructor
    · intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl
      · simpa only [Nat.one_mul,id] using px
      · simpa only [Nat.one_mul,id] using py
      · simpa only [Nat.one_mul,id] using pz
    · intro x _; rfl
  apply build_double_machine_wp.mpr
  refine WP.mono (field_program_ok hW hMax build_field_layout buildDoubleOps hs inv
    (by intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl|rfl <;> simp [buildSlot])
    buildDouble_slots buildDouble_reads buildDouble_coeffs) fun t ⟨it,ht,pt,ft⟩ => ?_
  have bx := it.bound 1288 (by decide)
  have byy := it.bound 1360 (by decide)
  have bz := it.bound 1432 (by decide)
  have vx := it.value 1288 (by decide)
  have vy := it.value 1360 (by decide)
  have vz := it.value 1432 (by decide)
  simp only [id] at vx vy vz
  refine ⟨⟨?_,?_,?_⟩,?_,ht,pt,ft⟩
  · simpa only [id,Nat.one_mul] using bx
  · simpa only [id,Nat.one_mul] using byy
  · simpa only [id,Nat.one_mul] using bz
  · change (Fin.ofNat fieldPrime (wordsVal t.mem base 1288 9),
      Fin.ofNat fieldPrime (wordsVal t.mem base 1360 9),Fin.ofNat fieldPrime (wordsVal t.mem base 1432 9))=_
    rw [vx,vy,vz]
    exact buildDouble_value E

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass Spec.Weierstrass

theorem build_double_group {C : Curve} (hp : C.p=fieldPrime) (law : Law C) (ha : AM3 C)
    {s : State} {base : Addr} {W : Nat} {Q : Point C}
    (hs : Scr s base W) (hW : 4024≤W) (hMax : W≤8192)
    (px : wordsVal s.mem base 2800 9<fieldPrime) (py : wordsVal s.mem base 3160 9<fieldPrime)
    (pz : wordsVal s.mem base 424 9<fieldPrime)
    (hQ : onCurve C Q=true)
    (current : InvJ C (Fin.ofNat C.p (wordsVal s.mem base 2800 9))
      (Fin.ofNat C.p (wordsVal s.mem base 3160 9))
      (Fin.ofNat C.p (wordsVal s.mem base 424 9)) Q) :
    WP isa buildDoubleMachine s fun t =>
      canonicalPoint t.mem base 1288 ∧
      InvJ C (pointAt C t.mem base 1288).1 (pointAt C t.mem base 1288).2.1
        (pointAt C t.mem base 1288).2.2 (Spec.Weierstrass.add Q Q) ∧
      Scr t base W ∧ FieldPublic s t ∧ FieldProgramFrame base id buildDoubleOps s.mem t.mem := by
  refine WP.mono (build_double_verified hs hW hMax px py pz) fun t ⟨bound,value,ht,pt,ft⟩ => ?_
  exact ⟨bound,dbl_coordinate_transfer hp law ha value hQ current,ht,pt,ft⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

/-- Both table-building arithmetic schedules write only the point temporaries and
    the existing field multiplication scratch. -/
def BuildFrame (base : Addr) (m m' : Mem) : Prop :=
  ∀x,(ofs base x<1288 ∨ 2152≤ofs base x) →
    (ofs base x<3952 ∨ 4024≤ofs base x) → m' x=m x

theorem build_double_frame {base : Addr} {m m' : Mem}
    (h : FieldProgramFrame base id buildDoubleOps m m') : BuildFrame base m m' := by
  intro x hx hs
  apply h x ?_ hs
  intro op ho
  have bounds : 1288≤op.out ∧ op.out+72≤2152 := by
    simp only [buildDoubleOps,List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  simp only [id]
  omega_arith

theorem build_mixed_frame {base : Addr} {m m' : Mem}
    (h : FieldProgramFrame base id buildMixedOps m m') : BuildFrame base m m' := by
  intro x hx hs
  apply h x ?_ hs
  intro op ho
  have bounds : 1288≤op.out ∧ op.out+72≤2152 := by
    simp only [buildMixedOps,List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  simp only [id]
  omega_arith

theorem BuildFrame.unch {base : Addr} {m m' : Mem} (h : BuildFrame base m m') :
    Unch base [(1288,864),(3952,72)] m m' := by
  intro x hx
  exact h x (hx (1288,864) (by simp)) (hx (3952,72) (by simp))

theorem BuildFrame.readonly {base : Addr} {m m' : Mem} (h : BuildFrame base m m') :
    ∀d k,d+8*k≤1288 ∨ (2152≤d ∧ d+8*k≤3952) ∨ 4024≤d → d+8*k≤8192 →
      wordsVal m' base d k=wordsVal m base d k := by
  intro d k hd hmax
  apply h.unch.wordsVal
  · intro w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl <;> simp only <;> omega_arith
  · omega_arith

end VG.Proof.Weierstrass.AArch64.P521Native

end

end

/-! ### `Weierstrass.AArch64.P521Native.BuildSeedStore`, which the modules that import this one used -/

section

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG.Impl.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass

def buildSeedStore : List Instr := buildStoreCopy .x26 9 2800 0 ++
  buildStoreCopy .x26 9 3160 72 ++ buildStoreCopy .x26 9 424 144

theorem build_seed_store_source : (outerBlock007.take 55).drop 1=buildSeedStore := by lit_decide

theorem build_seed_store_ok {base table : Addr} {s : State}
    (hs : Scr s base 8192) (pt : PtrW s .x26 table 216)
    (apart : Region.Disjoint ⟨base,8192⟩ ⟨table,216⟩) :
    WP isa (.block (buildSeedStore)) s fun t =>
      wordsVal t.mem table 0 9=wordsVal s.mem base 2800 9 ∧
      wordsVal t.mem table 72 9=wordsVal s.mem base 3160 9 ∧
      wordsVal t.mem table 144 9=wordsVal s.mem base 424 9 ∧
      KeepRegs [.x1] s t ∧ Outside table 0 216 s.mem t.mem := by
  rw [buildSeedStore,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (build_store_copy_ok (by decide : Reg.x26≠.x1) apart 9 hs pt (a:=2800) (o:=0)
    (by decide) (by decide) (by decide) (by decide)) fun u ⟨xu,ku,fu⟩ => ?_
  have hu := hs.of_keepRegs ku (by decide)
  have pu := pt.of_keepRegs ku (by decide)
  have wu := (fu.mono (by decide) (by decide : 0+8*9≤0+216)).unch_far apart
  refine WP.mono (build_store_copy_ok (by decide : Reg.x26≠.x1) apart 9 hu pu
    (a:=3160) (o:=72) (by decide) (by decide) (by decide) (by decide)) fun v ⟨yv,kv,fv⟩ => ?_
  have hv := hu.of_keepRegs kv (by decide)
  have pv := pu.of_keepRegs kv (by decide)
  have wv := (fv.mono (by decide) (by decide : 72+8*9≤0+216)).unch_far apart
  refine WP.mono (build_store_copy_ok (by decide : Reg.x26≠.x1) apart 9 hv pv
    (a:=424) (o:=144) (by decide) (by decide) (by decide) (by decide)) fun t ⟨zt,kt,ft⟩ => ?_
  refine ⟨?_,?_,?_,ku.trans (kv.trans kt),?_⟩
  · rw [ft.wordsVal (Or.inl (by decide)) (by decide),fv.wordsVal (Or.inl (by decide)) (by decide),xu]
  · rw [ft.wordsVal (Or.inl (by decide)) (by decide),yv]
    exact wu.wordsVal (by intro w hw; rw [List.mem_singleton.mp hw]; exact Or.inl (by decide)) (by decide)
  · rw [zt,wv.wordsVal (by intro w hw; rw [List.mem_singleton.mp hw]; exact Or.inl (by decide)) (by decide)]
    exact wu.wordsVal (by intro w hw; rw [List.mem_singleton.mp hw]; exact Or.inl (by decide)) (by decide)
  · exact (fu.mono (by decide) (by decide : 0+72≤0+216)).trans
      ((fv.mono (by decide) (by decide : 72+72≤0+216)).trans
        (ft.mono (by decide) (by decide : 144+72≤0+216)))

end VG.Proof.Weierstrass.AArch64.P521Native

end

end

/-! ### `Weierstrass.AArch64.P521Native.BuildAdvance`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass

theorem build_store_point_split : buildStoreCopy .x20 27 1288 0=
    buildStoreCopy .x20 9 1288 0 ++ buildStoreCopy .x20 9 1360 72 ++
      buildStoreCopy .x20 9 1432 144 := by lit_decide

theorem build_store_point_ok {base table : Addr} {s : State}
    (hs : Scr s base 8192) (pt : PtrW s .x20 table 216)
    (apart : Region.Disjoint ⟨base,8192⟩ ⟨table,216⟩) :
    WP isa (.block (buildStoreCopy .x20 27 1288 0)) s fun t =>
      wordsVal t.mem table 0 9=wordsVal s.mem base 1288 9 ∧
      wordsVal t.mem table 72 9=wordsVal s.mem base 1360 9 ∧
      wordsVal t.mem table 144 9=wordsVal s.mem base 1432 9 ∧
      KeepRegs [.x1] s t ∧ Outside table 0 216 s.mem t.mem := by
  rw [build_store_point_split,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (build_store_copy_ok (by decide : Reg.x20≠.x1) apart 9 hs pt
    (by decide) (by decide) (by decide) (by decide)) fun u ⟨xu,ku,fu⟩ => ?_
  have hu := hs.of_keepRegs ku (by decide)
  have pu := pt.of_keepRegs ku (by decide)
  have wu := (fu.mono (by decide) (by decide : 0+8*9≤0+216)).unch_far apart
  refine WP.mono (build_store_copy_ok (by decide : Reg.x20≠.x1) apart 9 hu pu
    (a:=1360) (o:=72) (by decide) (by decide) (by decide) (by decide)) fun v ⟨yv,kv,fv⟩ => ?_
  have hv := hu.of_keepRegs kv (by decide)
  have pv := pu.of_keepRegs kv (by decide)
  have wv := (fv.mono (by decide) (by decide : 72+8*9≤0+216)).unch_far apart
  refine WP.mono (build_store_copy_ok (by decide : Reg.x20≠.x1) apart 9 hv pv
    (a:=1432) (o:=144) (by decide) (by decide) (by decide) (by decide)) fun t ⟨zt,kt,ft⟩ => ?_
  refine ⟨?_,?_,?_,ku.trans (kv.trans kt),?_⟩
  · rw [ft.wordsVal (Or.inl (by decide)) (by decide),fv.wordsVal (Or.inl (by decide)) (by decide),xu]
  · rw [ft.wordsVal (Or.inl (by decide)) (by decide),yv]
    exact wu.wordsVal (by intro w hw; rw [List.mem_singleton.mp hw]; exact Or.inl (by decide)) (by decide)
  · rw [zt,wv.wordsVal (by intro w hw; rw [List.mem_singleton.mp hw]; exact Or.inl (by decide)) (by decide)]
    exact wu.wordsVal (by intro w hw; rw [List.mem_singleton.mp hw]; exact Or.inl (by decide)) (by decide)
  · exact (fu.mono (by decide) (by decide : 0+72≤0+216)).trans
      ((fv.mono (by decide) (by decide : 72+72≤0+216)).trans
        (ft.mono (by decide) (by decide : 144+72≤0+216)))

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass

def buildAdvance : Prog isa := .seq (.block (buildStoreCopy .x20 27 1288 0)) (.block buildCopyPoint)

theorem build_advance_ok {base table : Addr} {s : State}
    (hs : Scr s base 8192) (pt : PtrW s .x20 table 216)
    (apart : Region.Disjoint ⟨base,8192⟩ ⟨table,216⟩) :
    WP isa buildAdvance s fun t =>
      (∀c,c<3 → wordsVal t.mem table (72*c) 9=wordsVal s.mem base (1288+72*c) 9) ∧
      (∀c,c<3 → wordsVal t.mem base (1504+72*c) 9=wordsVal s.mem base (1288+72*c) 9) ∧
      KeepRegs [.x1] s t ∧
      (∀x,8192≤ofs base x → (ofs table x<0 ∨ 216≤ofs table x) → t.mem x=s.mem x) ∧
      Unch base [(1504,72),(1576,72),(1648,72),(8192,2^64)] s.mem t.mem := by
  rw [buildAdvance,WP.seq_iff]
  refine WP.mono (build_store_point_ok hs pt apart) fun u ⟨xu,yu,zu,ku,fu⟩ => ?_
  have hu := hs.of_keepRegs ku (by decide)
  have wu := fu.unch_far apart
  refine WP.mono (build_copy_point_ok hu) fun t ⟨xt,yt,zt,kt,ft⟩ => ?_
  have tableKept (d : Nat) (hd : d+72≤216) : wordsVal t.mem table d 9=wordsVal u.mem table d 9 := by
    have oa : Outside base 0 8192 u.mem t.mem := ft.outside (by
      intro w hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl|rfl <;> decide)
    have tableFrame := oa.unch_far apart.symm
    exact tableFrame.wordsVal
      (by intro w hw; rw [List.mem_singleton.mp hw]; exact Or.inl (by omega_arith)) (by omega_arith)
  refine ⟨?_,?_,ku.trans kt,?_,?_⟩
  · intro c hc
    have cases : c=0 ∨ c=1 ∨ c=2 := by omega_arith
    rcases cases with rfl|rfl|rfl
    · rw [tableKept 0 (by decide)]; exact xu
    · rw [tableKept 72 (by decide)]; exact yu
    · rw [tableKept 144 (by decide)]; exact zu
  · intro c hc
    have cases : c=0 ∨ c=1 ∨ c=2 := by omega_arith
    rcases cases with rfl|rfl|rfl
    all_goals try simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one]
    · rw [xt]; exact wu.wordsVal (by intro w hw; rw [List.mem_singleton.mp hw]; exact Or.inl (by decide)) (by decide)
    · rw [yt]; exact wu.wordsVal (by intro w hw; rw [List.mem_singleton.mp hw]; exact Or.inl (by decide)) (by decide)
    · rw [zt]; exact wu.wordsVal (by intro w hw; rw [List.mem_singleton.mp hw]; exact Or.inl (by decide)) (by decide)
  · intro x hx ht
    exact (ft.far (by
      intro w hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl|rfl <;> simp only <;> omega_arith)).trans (fu x ht)
  · exact (wu.trans ft).mono (by
      intro w hw
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
      rcases hw with rfl|rfl|rfl|rfl <;> simp)

end VG.Proof.Weierstrass.AArch64.P521Native

end

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Ed25519.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native

def buildCounter : List Instr := [.addImm .x .x20 .x20 216,.subImm .x .x19 .x19 1]

theorem build_counter_source : outerBlock027.drop 109=buildCounter := by lit_decide

theorem build_counter_ok (s : State) :
    WP isa (.block buildCounter) s fun t =>
      t.gpr .x20=s.gpr .x20+216#64 ∧ t.gpr .x19=s.gpr .x19-1#64 ∧
      Keeps [.x20,.x19] s t ∧ t.v=s.v := by
  apply WP.of_runBlock
  simp only [buildCounter,
    runBlock_cons,runStep_some,runBlock_nil,reduceExec,Size.bits,Nat.reduceLT,
    RegUpd.gpr_write,RegUpd.v_write,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,
    Option.some.injEq,exists_eq_left']
  refine ⟨rfl,rfl,⟨?_,by simp only [RegUpd.mem_write],by simp only [RegUpd.rd_write],
    by simp only [RegUpd.wr_write],by simp only [RegUpd.sp_write]⟩,trivial⟩
  reg_keeps

theorem build_counter_pointer {table : Addr} {m : Nat} :
    (off table (216*m))+216#64=off table (216*(m+1)) := by
  dsimp only [off]
  rw [Nat.mul_add,Nat.mul_one,BitVec.ofNat_add]
  exact BitVec.add_assoc _ _ _

theorem build_counter_count (m : Nat) (hm : m<16) :
    BitVec.ofNat 64 (16-m)-1#64=BitVec.ofNat 64 (16-(m+1)) := by
  have he : 16-m=(16-(m+1))+1 := by omega_arith
  rw [he,BitVec.ofNat_add,BitVec.add_sub_cancel]

end VG.Proof.Weierstrass.AArch64.P521Native
