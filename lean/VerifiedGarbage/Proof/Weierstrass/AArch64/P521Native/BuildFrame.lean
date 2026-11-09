module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeStoreCopy
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildGroup
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildDoubleCode
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleOutput

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
