import VerifiedGarbage.Proof.P256.EcdhTable.Dblu
import VerifiedGarbage.Proof.P256.EcdhTable.Zaddu
import VerifiedGarbage.Proof.P256.EcdhTable.DbluRaw
import VerifiedGarbage.Proof.P256.EcdhTable.ZadduRaw

namespace VG.Proof.P256.EcdhTable
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open EcdhJac Spec.Weierstrass

theorem observed_words {base : Addr} {s t : State} {observe : Nat → Prop}
    (hw : ∀ off,observe off → off%8=0 → off+8≤8192 → word t.mem base off=word s.mem base off)
    {d : Nat} (hd : d%8=0) (hb : d+32≤8192) (ho : ∀i<4,observe (d+8*i)) :
    wordsVal t.mem base d 4=wordsVal s.mem base d 4 := by
  have h0 := hw d (by simpa using ho 0 (by decide)) hd (by omega)
  have h1 := hw (d+8) (by simpa using ho 1 (by decide)) (by omega) (by omega)
  have h2 := hw (d+16) (by simpa using ho 2 (by decide)) (by omega) (by omega)
  have h3 := hw (d+24) (by simpa using ho 3 (by decide)) (by omega) (by omega)
  simp only [wordsVal,show d+8+8=d+16 by omega,show d+8+8+8=d+24 by omega,h0,h1,h2,h3]

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
