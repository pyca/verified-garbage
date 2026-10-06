import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStore
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeInvariant

/-! The counted table-building iteration preserves every earlier multiple. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem jacTreeLive_next (K : WinCfg) {m : Nat} (hm : 1≤m) :
    ∀ x∈jacTreeLive K (m+1), x∈jacCoords (Jacobian.tablePt K (m+1)) ++ jacCoords K.R ++
      ([K.E.x,K.E.y,K.E.z,K.D.x,K.D.y,K.D.z]++jacTreeLive K m) := by
  intro x hx
  simp only [jacTreeLive,show 2≤m+1 by omega,↓reduceIte,List.mem_append] at hx
  have oldro : ∀ x∈winRo K, x∈jacTreeLive K m := by
    intro x hx
    simp only [jacTreeLive,List.mem_append]
    exact Or.inl (Or.inl (Or.inl hx))
  rcases hx with ((hx | hx) | hx) | hx
  · have ho := oldro x hx
    simp only [List.mem_append]; grind
  · simp only [List.mem_append,jacCoords]; grind
  · simp only [List.mem_append]; grind
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    have hi' := List.mem_range.mp hi
    by_cases h : i<3*m
    · have ho : K.tbl+32*i∈jacTreeLive K m := List.mem_append_right _
        (List.mem_map.mpr ⟨i,List.mem_range.mpr h,rfl⟩)
      simp only [List.mem_append]; grind
    · have hn : K.tbl+32*i∈jacCoords (Jacobian.tablePt K (m+1)) := by
        simp only [jacCoords,Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false]
        omega
      simp only [List.mem_append]; grind

theorem JacWinLay.rcbApart_RP {K : WinCfg} {size : Nat} (hL : JacWinLay K size) (hJ : K.J=52) :
    RcbApart K.S K.R K.P K.D := by
  have old := hL.toWinLay hJ
  have h := old.rcbApart_D (Or.inl rfl)
  refine ⟨h.nodup,fun x hx hw => ?_⟩
  have he : x∈winRo K ∨ x∈rcbR K.S K.R K.R := by
    simp only [winRo,rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  rcases he with he | he
  · exact hL.ro x he (List.mem_append_right _ hw)
  · exact h.apart x he hw

/-- A table coordinate of an earlier entry differs from every new-entry coordinate. -/
theorem jacTable_ne {K : WinCfg} {a m x y : Nat} (ha : 1≤a) (ham : a≤m)
    (hx : x∈jacCoords (Jacobian.tablePt K a)) (hy : y∈jacCoords (Jacobian.tablePt K (m+1))) : x≠y := by
  simp only [jacCoords,Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx hy
  omega

theorem jacTree_step_ok {K : WinCfg} {C : Curve} {base : Addr} {size m : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    (ht : K.tbl<4096) (hOne : K.one<C.p) {P : Point C} (hP : onCurve C P=true)
    (hm1 : 1≤m) (hm15 : m≤15) {s₀ s : State} (hI : JacTreeInv K C base size P s₀ s m) :
    WP isa (Jacobian.jacTreeStep K 16) s fun t => JacTreeInv K C base size P s₀ t (m+1) := by
  have hf := hI.field
  have hv := jacTreeLive_read K m
  have ve : m%2≠1 → ∀ x∈[K.E.x,K.E.y,K.E.z], x∈jacTreeLive K m := by
    intro ho x hx; apply jacTreeLive_ED K (by omega) x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have vtab := jacTreeLive_table K (a := (m+1)/2) (m := m) (by omega) (by omega)
  have jtab := hI.table ((m+1)/2) (by omega) (by omega)
  unfold Jacobian.jacTreeStep
  apply WP.seq
  refine WP.mono (jacTreeArithmetic_ok hL hJ hAl hm hC ha ht hOne (hL.rcbApart_RP hJ) hm1 hm15
    hf hv ve vtab hI.counter hP hI.source hI.point jtab) fun u ⟨eu,ka,iu,ju⟩ => ?_
  have pu : u.gpr .x20=off base (K.tbl+96*((m+1)-1)) := by
    rw [ka.gpr _ (by rw [hL.n]; decide),hI.pointer,Nat.add_sub_cancel]
  have vd : ∀ x∈rcbR K.S K.D K.D, x∈[K.E.x,K.E.y,K.E.z,K.D.x,K.D.y,K.D.z]++jacTreeLive K m := by
    intro x hx
    have hsa := hv K.S.a (by simp [rcbR])
    have hsb := hv K.S.b3 (by simp [rcbR])
    simp only [rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  rw [WP.block_append_iff]
  refine WP.mono (jacTreeCopyStore_ok hL hAl (by omega) (by omega) iu vd pu ju)
    fun v ⟨ks,iv,jr,jnew⟩ => ?_
  let W := winOther K ++ jacCoords (Jacobian.tablePt K (m+1))
  have kas : ProgKeep K.M base W s v := (ka.mono (fun _ hx => List.mem_append_left _ hx)).trans ks
  have p19 : v.gpr .x19=BitVec.ofNat 64 (16-m) := by
    rw [kas.gpr _ (by rw [hL.n]; decide),hI.counter]
  have p20 : v.gpr .x20=off base (K.tbl+96*m) := by
    rw [kas.gpr _ (by rw [hL.n]; decide),hI.pointer]
  refine WP.mono (jacAdvanceTable_ok p19 p20 hm15) fun t ⟨hc,hp,kc⟩ => ?_
  have it := (iv.of_keeps kc (by decide)).to_tmv.sub (jacTreeLive_next K hm1)
  have slots : ∀ x∈W, x∈jacWinSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (List.mem_append_right _ hx)
    · exact jacTblPt_mem K (by omega) (by omega) x hx
  have kct : KeepRegs (jacTreeClob K) v t := (Keeps.regs kc).mono (fun _ hx => List.mem_append_right _ hx)
  have kst : KeepRegs (jacTreeClob K) s t :=
    (KeepRegs.mono ⟨kas.gpr,kas.rd,kas.wr,kas.sp⟩ (fun _ hx => List.mem_append_left _ hx)).trans kct
  have uw : Unch base (jacTreeWrites K) s.mem t.mem := by
    rw [kc.mem]
    apply kas.unch.mono
    intro w hw
    simp only [jacTreeWrites,List.mem_append,List.mem_map,List.mem_singleton] at hw ⊢
    rcases hw with ⟨x,hx,rfl⟩ | rfl
    · refine Or.inl ⟨x,?_,rfl⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ hx
      · apply List.mem_append_right
        have hh := jacTblPt_mem K (by omega : 1≤m+1) (by omega : m+1≤16) x hx
        simp only [Jacobian.tablePt,jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact jacTbl_mem K (by omega) (by omega) (c:=0) (by decide)
        · exact jacTbl_mem K (by omega) (by omega) (c:=1) (by decide)
        · exact jacTbl_mem K (by omega) (by omega) (c:=2) (by decide)
    · exact Or.inr rfl
  have roeq (x : Nat) (hx : x∈winRo K) : tmv C K.M.n base t x=tmv C K.M.n base s x := by
    unfold tmv; rw [kc.mem]
    rw [kas.slot hL.lay hf.scr slots (List.mem_append_left _ (List.mem_append_left _ hx)) ?_]
    intro hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hL.ro x hx hw
    · have sep := hL.tbl x (List.mem_append_left _ hx)
      simp only [jacCoords,Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hw
      omega
  refine ⟨it,?_,?_,?_,hc,hp,hI.keep.trans kst,?_⟩
  · simpa only [tmv,kc.mem] using jr
  · rw [roeq _ (by simp [winRo]),roeq _ (by simp [winRo]),roeq _ (by simp [winRo])]
    exact hI.source
  · intro a ha1 ham
    by_cases he : a=m+1
    · subst a; simpa only [tmv,kc.mem] using jnew
    · have ham' : a≤m := by omega
      have teq (x : Nat) (hx : x∈jacCoords (Jacobian.tablePt K a)) :
          tmv C K.M.n base t x=tmv C K.M.n base s x := by
        unfold tmv; rw [kc.mem]
        rw [kas.slot hL.lay hf.scr slots (jacTblPt_mem K ha1 (by omega) x hx) ?_]
        intro hw
        rcases List.mem_append.mp hw with hw | hw
        · have sep := hL.tbl x (List.mem_append_right _ hw)
          simp only [jacCoords,Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx
          omega
        · exact jacTable_ne ha1 ham' hx hw rfl
      rw [teq _ (by simp [jacCoords]),teq _ (by simp [jacCoords]),teq _ (by simp [jacCoords])]
      exact hI.table a ha1 ham'
  · exact (hI.unch.trans uw).mono (fun _ hw => (List.mem_append.mp hw).elim id id)

end VG.Proof.Weierstrass.AArch64
