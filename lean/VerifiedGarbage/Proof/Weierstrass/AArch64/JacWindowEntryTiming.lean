import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoadTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowNegTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowEntry
import VerifiedGarbage.Proof.Framework.RelCTAssoc

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

local macro "jmem" : tactic => `(tactic| simp only [jacLive,jacWinSlots,jacWinWrites,
  winRo,winOther,rcbR,rcbW,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,true_or,or_true])

structure JacEntryChecks (K : WinCfg) : Prop where
  lookup : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x2]))
    (.block (Jacobian.publicEntry K))
  neg : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]))
    (.block (negYW K.M 5 K.neg K.zero K.E.y K.bits))

theorem jacSignedEntry_relCT {K : WinCfg} {C : Curve} {base : Addr} {size k j a : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hTbl : K.tbl<4096) (hBits : K.bits+5≤4096)
    (hj : j<52) (ha : 1≤a) (h16 : a≤16) (hc : JacEntryChecks K)
    {P : Point C} {E : Nat → Fe C} :
    RelCT isa (fun s t => FieldPair K.M base size C.p (·∈jacWinSlots K) (jacLive K) E s t ∧
      JacStable K C base P k s ∧ JacStable K C base P k t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j ∧
      s.gpr .x2=BitVec.ofNat 64 a ∧ t.gpr .x2=BitVec.ofNat 64 a)
      (.block (Jacobian.publicEntry K ++ negYW K.M 5 K.neg K.zero K.E.y K.bits))
      (fun s t => ∃ E', FieldPair K.M base size C.p (·∈jacWinSlots K) (jacLive K) E' s t) := by
  have hD : ∀ x∈jacCoords K.E, x∈jacWinSlots K := by
    intro x hx; simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jmem
  have hT : ∀ x∈jacCoords (Jacobian.tablePt K a), x∈jacLive K := by
    intro x hx
    apply List.mem_append_right
    simp only [jacCoords,Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact jacTbl_mem K ha h16 (c:=0) (by decide)
    · exact jacTbl_mem K ha h16 (c:=1) (by decide)
    · exact jacTbl_mem K ha h16 (c:=2) (by decide)
  have hap : K.E.x+96≤K.tbl+96*(a-1) ∨ K.tbl+96*(a-1)+96≤K.E.x := by
    have hx := hL.tbl K.E.x (by jmem)
    have hy := hL.tbl K.E.y (by jmem)
    have hz := hL.tbl K.E.z (by jmem)
    rw [hL.exy] at hy
    rw [hL.exz] at hz
    omega
  have load := jacPublic_relCT (base:=base) (E:=E) hL.lay hAl hL.n hL.exy hL.exz hD hT hap ha hTbl hc.lookup
  have load' : RelCT isa (fun s t => FieldPair K.M base size C.p (·∈jacWinSlots K) (jacLive K) E s t ∧
      JacStable K C base P k s ∧ JacStable K C base P k t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j ∧
      s.gpr .x2=BitVec.ofNat 64 a ∧ t.gpr .x2=BitVec.ofNat 64 a)
      (.block (Jacobian.publicEntry K))
      (fun s t => ∃ E', FieldPair K.M base size C.p (·∈jacWinSlots K) (jacLive K) E' s t ∧
        JacStable K C base P k s ∧ JacStable K C base P k t ∧
        s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j) := by
    intro s t ts tt s' t' ⟨hp,ss,st,s19,t19,s2,t2⟩ es et
    obtain ⟨he,E',pair⟩ := load _ _ _ _ _ _ ⟨hp,s2,t2⟩ es et
    obtain ⟨_,_,xs,ks,_,_⟩ := jacPublicFields_ok hL.lay hAl hL.n hL.exy hL.exz hp.left s2 ha hTbl hD hT hap
    obtain ⟨_,_,xt,kt,_,_⟩ := jacPublicFields_ok hL.lay hAl hL.n hL.exy hL.exz hp.right t2 ha hTbl hD hT hap
    obtain ⟨_,rfl⟩ := Exec.det es xs
    obtain ⟨_,rfl⟩ := Exec.det et xt
    have hw : ∀ x∈[K.E.x,K.E.y,K.E.z], x∈winOther K := by
      intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl <;> jmem
    exact ⟨he,E',pair.sub (fun _ hx => List.mem_append_right _ hx),
      ss.keep hL hJ hp.left.scr.nowrap (ks.mono hw).unch,
      st.keep hL hJ hp.right.scr.nowrap (kt.mono hw).unch,
      (ks.gpr _ (x19_not_clob _)).trans s19,(kt.gpr _ (x19_not_clob _)).trans t19⟩
  apply RelCT.block_append
  apply RelCT.seq load'
  apply RelCT.exists_
  intro E'
  have hnd := hL.nodup
  simp only [winOther,rcbW,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,
    List.not_mem_nil,or_false,not_or] at hnd
  intro s t ts tt s' t' ⟨hp,ss,st,s19,t19⟩ es et
  have hzero : E' K.zero=0 := by rw [←hp.left.val _ (by jmem),ss.zero,toM_zero]
  have hbn := hL.bits_w K.neg (by jmem)
  have hbt := hL.bits_tmp
  have hbn' : K.bits+260≤K.neg ∨ K.neg+8*K.M.n≤K.bits := by rw [hL.n]; exact hbn
  have hbt' : K.bits+260≤K.M.tmp ∨ K.M.tmp+8*K.M.n≤K.bits := by rw [hL.n]; exact hbt
  have neg := negFieldWindow_relCT (base:=base) (k:=k) (V:=jacLive K) hL.lay hAl hm (E:=E') (by jmem) (by jmem) (by jmem)
    (by grind : K.neg≠K.E.y) hzero (by decide : 1≤5) (by decide : 5<65536)
    (by omega : 5*j+5≤260) hL.bits (by omega : K.bits+5-1<4096) hbn' hbt' hc.neg
  obtain ⟨he,hp'⟩ := neg _ _ _ _ _ _ ⟨hp,s19,t19,ss.bits,st.bits⟩ es et
  exact ⟨he,_,hp'.sub (fun _ hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))⟩

end VG.Proof.Weierstrass.AArch64
