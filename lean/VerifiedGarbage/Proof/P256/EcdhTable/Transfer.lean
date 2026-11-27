module

public import VerifiedGarbage.Proof.P256.EcdhTable.Dblu
public import VerifiedGarbage.Proof.P256.EcdhTable.Zaddu
public import VerifiedGarbage.Proof.P256.EcdhJac.DbluCertificate
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import VerifiedGarbage.Proof.P256.EcdhTable.DbluRaw
public import VerifiedGarbage.Proof.P256.EcdhJac.State
import VerifiedGarbage.Proof.Weierstrass.JacMadd
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.P256.EcdhJac.Dblu
import VerifiedGarbage.Proof.P256.EcdhJac.Frame
import VerifiedGarbage.Proof.P256.EcdhJac.ZadduCertificate

/-! ### `P256.EcdhJac.Zaddu`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

theorem zaddu_x (hC : Law C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) (hn17 : 17 ≤ C.n) {m : Nat} (h2 : 2 ≤ m) (h15 : m ≤ 15) {X1 Y1 X2 Y2 Z : Fe C}
    (h1 : InvJ C X1 Y1 Z P) (hm : InvJ C X2 Y2 Z (mul m P)) (hz : Z ≠ 0) : X1 - X2 ≠ 0 := by
  intro hx
  obtain ⟨ne1, ne2⟩ := Window5.tbl_noexc hC hO hP hP0 hn17 h2 h15
  have hx' : X1 * (Z * Z) - X2 * (Z * Z) = 0 := by
    -- `-lia`: Lean 4.36's `grind` builds a proof the kernel rejects from `lia`
    -- over `Fin` of a non-literal modulus (lean4#15857, fixed in 4.37).
    have e : X1 * (Z * Z) - X2 * (Z * Z) = (X1 - X2) * (Z * Z) := by grind -lia
    rw [e, hx]; grind -lia
  by_cases hy : Y1 * Z * (Z * Z) - Y2 * Z * (Z * Z) = 0
  · exact ne1 (hm.same hC h1 hz hz hx' hy)
  · exact ne2 (hm.opposite hC (hC.onCurve_mul hP m) hP h1 hz hz hx' hy)

end VG.Proof.P256.EcdhJac

end

end

/-! ### `P256.EcdhTable.ZadduRaw`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

theorem zaddu_raw_ok (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {base : Addr} {P : Point C} {k m : Nat} {s : State} (hP : onCurve C P=true)
    (hm2 : 2≤m) (hm15 : m≤15) (hf : Fixed base P k s)
    (hp : JPt base s selectedSlot (mul m P))
    (hl : ∀x∈[K.D.x,K.D.y],wordsVal s.mem base x 4<C.p)
    (hd : InvJ C (tmv C 4 base s K.D.x) (tmv C 4 base s K.D.y) (tmv C 4 base s K.E.z) P) :
    WP isa (.block (Impl.P256.EcdhJac.zadduOps.flatMap Impl.P256.VerifySparse.op)) s fun t =>
      Frame base work s t ∧ Fixed base P k t ∧ JPt base t selectedSlot (mul (m+1) P) ∧
      (∀x∈[K.D.x,K.D.y],wordsVal t.mem base x 4<C.p) ∧
      InvJ C (tmv C 4 base t K.D.x) (tmv C 4 base t K.D.y) (tmv C 4 base t K.E.z) P ∧ t.gpr .x19=s.gpr .x19 := by
  have hi : Inv M base 8192 C.p Sl [K.D.x,K.D.y,K.E.x,K.E.y,K.E.z,5400] (tmv C 4 base s) s := by
    refine ⟨hf.field.scr,hf.field.mod,by decide,?_,fun _ _ => rfl⟩
    intro x hx
    have hh : x=K.D.x∨x=K.D.y∨x=K.E.x∨x=K.E.y∨x=K.E.z∨x=5400 := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hx
    rcases hh with rfl|rfl|rfl|rfl|rfl|rfl
    · exact hl _ (by decide)
    · exact hl _ (by decide)
    · exact hp.lt 0 (by decide)
    · exact hp.lt 1 (by decide)
    · exact hp.lt 2 (by decide)
    · exact hp.lt 3 (by decide)
  rw [zaddu_eq]
  refine WP.mono (table_raw_field (N:=zadduN) (by decide)
    (by decide : readsOk zadduN [0,1,8,9,10,11]=true) hi (by decide)) fun t ⟨kt,it,eqs⟩ => ?_
  have fr := tblFrame kt
  have vals := fun {i : Nat} (h : i∈zadduN.map FOp.out) => tbl_val it eqs h
  obtain ⟨ht,h11,h12⟩ := zadduN_run (fun j => tmv C 4 base s (tblσ j))
  generalize runOps zadduN (fun j => tmv C 4 base s (tblσ j))=r at vals ht h11 h12
  have h2 : tmv C 4 base s (tblσ 11)=tmv C 4 base s (tblσ 10)*tmv C 4 base s (tblσ 10) := hp.z2
  have jp : InvJ C (tmv C 4 base s K.P.x) (tmv C 4 base s K.P.y) 1 P := by
    have h := InvJ.of_rep01 hf.peer (Or.inl hf.one); rw [hf.one] at h; exact h
  have p0 : P≠.infinity := fun hh => hC.one_ne_zero ((jp.z_zero_iff hC).mpr hh)
  have hx := zaddu_x hC hO hP p0 (by decide) hm2 hm15 hd hp.jac hp.z
  obtain ⟨js,jd⟩ := InvJ.zaddu hC ha hP (hC.onCurve_mul hP m) hd hp.jac hp.z hx
  have hm : add (mul m P) P=mul (m+1) P := by
    calc
      add (mul m P) P=add (mul m P) (mul 1 P) := by rw [mul_one_pt]
      _=mul (m+1) P := hC.add_mul_mul hP m 1
  rw [hm] at js
  change ((r 8,r 9,r 10),(r 0,r 1))=zadduF _ _ _ _ _ at ht
  change InvJ C (zadduF (tmv C 4 base s (tblσ 0)) (tmv C 4 base s (tblσ 1))
    (tmv C 4 base s (tblσ 8)) (tmv C 4 base s (tblσ 9)) (tmv C 4 base s (tblσ 10))).1.1
    (zadduF (tmv C 4 base s (tblσ 0)) (tmv C 4 base s (tblσ 1))
    (tmv C 4 base s (tblσ 8)) (tmv C 4 base s (tblσ 9)) (tmv C 4 base s (tblσ 10))).1.2.1
    (zadduF (tmv C 4 base s (tblσ 0)) (tmv C 4 base s (tblσ 1))
    (tmv C 4 base s (tblσ 8)) (tmv C 4 base s (tblσ 9)) (tmv C 4 base s (tblσ 10))).1.2.2 _ at js
  have js' : InvJ C (r 8) (r 9) (r 10) (mul (m+1) P) := by
    have hh := congrArg (fun q : (Fe C × Fe C × Fe C) × (Fe C × Fe C) =>
      InvJ C q.1.1 q.1.2.1 q.1.2.2 (mul (m+1) P)) ht
    exact hh.mpr js
  have jd' : InvJ C (r 0) (r 1) (r 10) P := by
    have hh := congrArg (fun q : (Fe C × Fe C × Fe C) × (Fe C × Fe C) =>
      InvJ C q.2.1 q.2.2 q.1.2.2 P) ht
    exact hh.mpr jd
  have hz : r 10≠0 := fun hh => Window5.mul_ne_infinity hO hP p0 (by omega_using [])
    (by
      have hn : 17≤C.n := by decide
      omega_using [hm15, hn]) ((js'.z_zero_iff hC).mp hh)
  have v0 := vals (i:=0) (by decide)
  have v1 := vals (i:=1) (by decide)
  have hv : ∀i<5,tmv C 4 base t (selectedSlot i)=r (8+i) ∧ wordsVal t.mem base (selectedSlot i) 4<C.p := by
    intro i hi
    have : i=0∨i=1∨i=2∨i=3∨i=4 := by omega_using [hi]
    rcases this with rfl|rfl|rfl|rfl|rfl
    · exact vals (i:=8) (by decide)
    · exact vals (i:=9) (by decide)
    · exact vals (i:=10) (by decide)
    · exact vals (i:=11) (by decide)
    · exact vals (i:=12) (by decide)
  refine ⟨fr,hf.keep (frame_build fr),⟨fun i hi => (hv i hi).2,?_,?_,?_,?_⟩,?_,?_,kt.gpr _ (by decide)⟩
  · rw [(hv 0 (by decide)).1,(hv 1 (by decide)).1,(hv 2 (by decide)).1]; exact js'
  · rw [(hv 2 (by decide)).1]; exact hz
  · rw [(hv 3 (by decide)).1,(hv 2 (by decide)).1]; exact h11 h2
  · rw [(hv 4 (by decide)).1,(hv 3 (by decide)).1,(hv 2 (by decide)).1]; exact h12
  · intro x hx
    rcases List.mem_cons.mp hx with rfl|hx
    · exact v0.2
    · rw [List.mem_singleton.mp hx]; exact v1.2
  · change InvJ C (tmv C 4 base t (tblσ 0)) (tmv C 4 base t (tblσ 1)) (tmv C 4 base t (tblσ 10)) P
    rw [v0.1,v1.1,(vals (i:=10) (by decide)).1]
    exact jd'

end VG.Proof.P256.EcdhJac

end

end


@[expose] public section

namespace VG.Proof.P256.EcdhTable
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open EcdhJac Spec.Weierstrass

theorem observed_words {base : Addr} {s t : State} {observe : Nat → Prop}
    (hw : ∀ off,observe off → off%8=0 → off+8≤8192 → word t.mem base off=word s.mem base off)
    {d : Nat} (hd : d%8=0) (hb : d+32≤8192) (ho : ∀i<4,observe (d+8*i)) :
    wordsVal t.mem base d 4=wordsVal s.mem base d 4 := by
  have h0 := hw d (by simpa using ho 0 (by decide)) hd (by omega_using [hb])
  have h1 := hw (d+8) (by simpa using ho 1 (by decide)) (by omega_using [hd]) (by omega_using [hb])
  have h2 := hw (d+16) (by simpa using ho 2 (by decide)) (by omega_using [hd]) (by omega_using [hb])
  have h3 := hw (d+24) (by simpa using ho 3 (by decide)) (by omega_using [hd]) (by omega_using [hb])
  simp only [wordsVal,show d+8+8=d+16 by omega_using [],show d+8+8+8=d+24 by omega_using [],h0,h1,h2,h3]

 theorem dblu_ok (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {base : Addr} {P : Point C} {k : Nat} {s : State} (hP : onCurve C P=true)
    (hf : Fixed base P k s) :
    WP isa (Impl.P256.EcdhTable.program true) s fun t =>
      EcdhJac.Frame base work s t ∧ Fixed base P k t ∧ JPt base t selectedSlot (mul 2 P) ∧
      InvJ C (tmv C 4 base t K.S.t3) (tmv C 4 base t K.S.t2) (tmv C 4 base t K.E.z) P ∧
      wordsVal t.mem base K.S.t3 4<C.p ∧ wordsVal t.mem base K.S.t2 4<C.p := by
  refine WP.mono (Dblu.refine hf.field.scr (dblu_raw_ok hC ha hO hP hf)) fun t ⟨u,hu,hw,hk⟩ => ?_
  have fr : EcdhJac.Frame base work s t := hk.widenRegs allocated_regs
  have he : ∀d∈[704,736,768,864,896,5400,5432],wordsVal t.mem base d 4=wordsVal u.mem base d 4 := by
    intro d hd
    apply observed_words hw
    · exact (show ∀d∈[704,736,768,864,896,5400,5432],d%8=0 from by decide) d hd
    · exact (show ∀d∈[704,736,768,864,896,5400,5432],d+32≤8192 from by decide) d hd
    · exact (show ∀d∈[704,736,768,864,896,5400,5432],∀i<4,Dblu.observe (d+8*i) from by decide +kernel) d hd
  have ht : ∀d∈[704,736,768,864,896,5400,5432],tmv C 4 base t d=tmv C 4 base u d := by
    intro d hd; unfold tmv; rw [he d hd]
  refine ⟨fr,hf.keep (frame_build fr),hu.2.2.1.congr ?_,?_,?_,?_⟩
  · intro i hi
    exact he _ ((show ∀i<5,selectedSlot i∈[704,736,768,864,896,5400,5432] from by decide) i hi)
  · rw [ht _ (by decide),ht _ (by decide),ht _ (by decide)]
    exact hu.2.2.2.1
  · rw [he _ (by decide)]; exact hu.2.2.2.2.1
  · rw [he _ (by decide)]; exact hu.2.2.2.2.2

theorem zaddu_ok (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {base : Addr} {P : Point C} {k m : Nat} {s : State} (hP : onCurve C P=true)
    (hm2 : 2≤m) (hm15 : m≤15) (hf : Fixed base P k s)
    (hp : JPt base s selectedSlot (mul m P))
    (hl : ∀x∈[K.D.x,K.D.y],wordsVal s.mem base x 4<C.p)
    (hd : InvJ C (tmv C 4 base s K.D.x) (tmv C 4 base s K.D.y) (tmv C 4 base s K.E.z) P) :
    WP isa (Impl.P256.EcdhTable.program false) s fun t =>
      EcdhJac.Frame base work s t ∧ Fixed base P k t ∧ JPt base t selectedSlot (mul (m+1) P) ∧
      (∀x∈[K.D.x,K.D.y],wordsVal t.mem base x 4<C.p) ∧
      InvJ C (tmv C 4 base t K.D.x) (tmv C 4 base t K.D.y) (tmv C 4 base t K.E.z) P ∧ t.gpr .x19=s.gpr .x19 := by
  refine WP.mono (Zaddu.refine hf.field.scr (zaddu_raw_ok hC ha hO hP hm2 hm15 hf hp hl hd))
    fun t ⟨u,hu,hw,hk⟩ => ?_
  have fr : EcdhJac.Frame base work s t := hk.widenRegs allocated_regs
  have he : ∀d∈[608,640,704,736,768,5400,5432],wordsVal t.mem base d 4=wordsVal u.mem base d 4 := by
    intro d hd
    apply observed_words hw
    · exact (show ∀d∈[608,640,704,736,768,5400,5432],d%8=0 from by decide) d hd
    · exact (show ∀d∈[608,640,704,736,768,5400,5432],d+32≤8192 from by decide) d hd
    · exact (show ∀d∈[608,640,704,736,768,5400,5432],∀i<4,Zaddu.observe (d+8*i) from by decide +kernel) d hd
  have ht : ∀d∈[608,640,704,736,768,5400,5432],tmv C 4 base t d=tmv C 4 base u d := by
    intro d hd; unfold tmv; rw [he d hd]
  refine ⟨fr,hf.keep (frame_build fr),hu.2.2.1.congr ?_,?_,?_,hk.regs.gpr _ allocatedRegs_x19⟩
  · intro i hi
    exact he _ ((show ∀i<5,selectedSlot i∈[608,640,704,736,768,5400,5432] from by decide) i hi)
  · intro d hd
    rw [he d (by exact (show ∀d∈[K.D.x,K.D.y],d∈[608,640,704,736,768,5400,5432] from by decide) d hd)]
    exact hu.2.2.2.1 d hd
  · rw [ht _ (by decide),ht _ (by decide),ht _ (by decide)]
    exact hu.2.2.2.2.1

end VG.Proof.P256.EcdhTable
