import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeInvariant
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStore
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStep

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem jacTree_pointer_ok {K : WinCfg} {base : Addr} {size : Nat} {s : State}
    (hs : Scr s base size) (ht : K.tbl<4096) :
    WP isa (.block [.addImm .x .x20 .x0 K.tbl]) s fun t =>
      t.gpr .x20 = off base K.tbl ∧ Keeps [.x20] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    Size.bits,BitVec.setWidth_eq,ht,ite_true,hs.x0,
    Option.some.injEq,exists_eq_left']
  refine ⟨trivial,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write,hr,ite_false]

theorem jacTree_initCounter_ok {s : State} {base : Addr} {tbl : Nat}
    (h20 : s.gpr .x20=off base tbl) :
    WP isa (.block [.addImm .x .x20 .x20 96,.movz .x .x19 15 0]) s fun t =>
      t.gpr .x20=off base (tbl+96) ∧ t.gpr .x19=15 ∧ Keeps [.x19,.x20] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    Size.bits,BitVec.setWidth_eq,show 96<4096 by decide,show 16*0<64 by decide,
    ite_true,ite_false,reduceCtorEq,h20,Option.some.injEq,exists_eq_left']
  refine ⟨?_,rfl,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · simp only [off,BitVec.add_assoc,BitVec.ofNat_add_ofNat]
  · simp only [List.mem_cons,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

/-- All writes made while constructing the table avoid the curve constants and input point. -/
theorem jacTree_ro_words {K : WinCfg} {size : Nat} (hL : JacWinLay K size)
    {base : Addr} {m m' : Mem} (hu : Unch base (jacTreeWrites K) m m')
    (hn : base.toNat+size ≤ 2^64) {x : Nat} (hx : x ∈ winRo K) :
    wordsVal m' base x K.M.n = wordsVal m base x K.M.n := by
  have hs : x ∈ jacWinSlots K := List.mem_append_left _ (List.mem_append_left _ hx)
  have hl := hL.lay.le x hs
  apply hu.wordsVal _ (by omega)
  intro w hw
  simp only [jacTreeWrites,List.mem_append,List.mem_map,List.mem_singleton] at hw
  rcases hw with ⟨y,hy,rfl⟩ | rfl
  · have hys : y ∈ jacWinSlots K := by
      simp only [jacWinWrites,jacWinSlots,List.mem_append] at hy ⊢
      rcases hy with hy | hy
      · exact Or.inl (Or.inr hy)
      · exact Or.inr hy
    apply hL.lay.apart x y hs hys
    intro he
    simp only [jacWinWrites,List.mem_append] at hy
    rcases hy with hy | hy
    · exact hL.ro x hx (he ▸ hy)
    · obtain ⟨i,hi,heq⟩ := List.mem_map.mp hy
      have ht := hL.tbl x (List.mem_append_left _ hx)
      have hi' := List.mem_range.mp hi
      omega
  · exact hL.lay.tmp x hs

theorem jacTree_progUnch {K : WinCfg} {base : Addr} {W : List Nat} {s t : State}
    (hk : ProgKeep K.M base W s t) (hw : ∀ x ∈ W, x ∈ jacWinWrites K) :
    Unch base (jacTreeWrites K) s.mem t.mem := hk.unch.mono (by
  intro w h
  simp only [List.mem_append,List.mem_map,List.mem_singleton] at h
  rcases h with ⟨x,hx,rfl⟩ | rfl
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨x,hw x hx,rfl⟩)
  · exact List.mem_append_right _ (by simp))


/-- Initialize R and the first Jacobian table entry from the public point. -/
theorem jacTree_init_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : JacWinLay K size) (hAl : Aligned K.M (·∈jacWinSlots K)) (ht : K.tbl<4096)
    {s : State} (hI : Inv K.M base size C.p (·∈jacWinSlots K) (winRo K) (tmv C K.M.n base s) s)
    {P : Point C} (hP : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
      (tmv C K.M.n base s K.P.z) P) :
    WP isa (.block (copyPt 4 K.R K.P ++ ([.addImm .x .x20 .x0 K.tbl] : List Instr) ++ Jacobian.tableStore K ++
      ([.addImm .x .x20 .x20 96,.movz .x .x19 15 0] : List Instr))) s
      (fun t => JacTreeInv K C base size P s t 1) := by
  have rwsub : ∀ x∈rcbW K.S K.R, x∈winOther K := by
    intro x hx
    simp only [rcbW,winOther,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hx ⊢
    grind
  have hApart : RcbApart K.S K.P K.P K.R := by
    refine ⟨hL.rcbApart_DR.nodup,?_⟩
    intro x hx hw
    apply hL.ro x ?_ (rwsub x hw)
    simp only [rcbR,winRo,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have hSl : ∀ x∈rcbW K.S K.R ++ rcbR K.S K.P K.P, x∈jacWinSlots K := by
    intro x hx
    apply List.mem_append_left
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_right _ (rwsub x hx)
    · apply List.mem_append_left
      simp only [rcbR,winRo,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
      grind
  have hV : ∀ x∈rcbR K.S K.P K.P, x∈winRo K := by
    intro x hx
    simp only [rcbR,winRo,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  rw [List.append_assoc,List.append_assoc,WP.block_append_iff,←hL.n]
  refine WP.mono (copyPointJ_ok hL.lay hAl hApart hSl hI hV hP) fun a ⟨ea,ka,ia,ja⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (jacTree_pointer_ok (K := K) ia.scr ht) fun b ⟨pb,kb⟩ => ?_
  have ib := ia.of_keeps kb (by decide)
  have tm : ∀ x, tmv C K.M.n base b x = tmv C K.M.n base a x := by
    intro x; unfold tmv; rw [kb.mem]
  have pb' : b.gpr .x20=off base (K.tbl+96*(1-1)) := by simpa using pb
  have rmem : ∀ x∈[K.R.x,K.R.y,K.R.z], x∈winOther K := by
    intro x hx
    simp only [winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have smem := jacTblPt_mem K (a := 1) (by decide) (by decide)
  have sep : K.R.x+96 ≤ K.tbl+96*(1-1) ∨ K.tbl+96*(1-1)+96 ≤ K.R.x := by
    have hx := hL.tbl K.R.x (List.mem_append_right _ (rmem _ (by simp)))
    have hz := hL.tbl K.R.z (List.mem_append_right _ (rmem _ (by simp)))
    rw [hL.rxz] at hz
    omega
  rw [WP.block_append_iff]
  refine WP.mono (jacStorePoint_ok hL.lay hL.n hL.rxy hL.rxz ib pb'
    (hAl.sl _ (hSl _ (by simp [rcbW]))) smem
    (fun _ hx => List.mem_append_left _ hx) sep ja) fun c ⟨kc,ic,jc⟩ => ?_
  have pc : c.gpr .x20=off base K.tbl := by
    rw [kc.gpr _ (by rw [hL.n]; decide),pb]
  refine WP.mono (jacTree_initCounter_ok pc) fun t ⟨pt,ct,kt⟩ => ?_
  have it := ic.of_keeps kt (by decide)
  have cu : Unch base (jacTreeWrites K) b.mem c.mem := jacTree_progUnch kc
    (fun x hx => List.mem_append_right _ (by
      have hh := smem x hx
      simp only [Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact jacTbl_mem K (a := 1) (c := 0) (by decide) (by decide) (by decide)
      · exact jacTbl_mem K (a := 1) (c := 1) (by decide) (by decide) (by decide)
      · exact jacTbl_mem K (a := 1) (c := 2) (by decide) (by decide) (by decide)))
  have au := jacTree_progUnch ka (fun x hx => List.mem_append_left _ (rwsub x hx))
  have ut : Unch base (jacTreeWrites K) s.mem t.mem := by
    rw [kt.mem]
    rw [kb.mem] at cu
    exact (au.trans cu).mono (fun w hw => (List.mem_append.mp hw).elim id id)
  have rpoint : InvJ C (tmv C K.M.n base t K.R.x) (tmv C K.M.n base t K.R.y)
      (tmv C K.M.n base t K.R.z) P := by
    have eqv (x : Nat) (hx : x∈[K.R.x,K.R.y,K.R.z]) : tmv C K.M.n base t x = tmv C K.M.n base b x := by
      unfold tmv
      rw [kt.mem,kc.slot hL.lay ib.scr smem
        (List.mem_append_left _ (List.mem_append_right _ (rmem x hx))) ?_]
      intro hx'
      have hh := hL.tbl x (List.mem_append_right _ (rmem x hx))
      simp only [Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx'
      rcases hx' with rfl | rfl | rfl <;> omega
    rw [eqv _ (by simp),eqv _ (by simp),eqv _ (by simp)]
    exact ib.point_tmv (fun _ hx => List.mem_append_left _ hx) ja
  refine ⟨?_,?_,?_,?_,ct,?_,?_,ut⟩
  · apply it.to_tmv.sub
    intro x hx
    simp only [jacTreeLive,jacTreeSlots,Jacobian.tablePt,List.range_succ,List.range_zero,
      List.map_append,List.map_cons,List.map_nil,List.nil_append,
      Nat.mul_one,Nat.sub_self,Nat.mul_zero,Nat.add_zero,show ¬2≤1 by decide,↓reduceIte,
      List.append_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,show 32*2=64 from rfl] at hx ⊢
    grind
  · rw [mul_one_pt]; exact rpoint
  · have ev (x : Nat) (hx : x∈winRo K) : tmv C K.M.n base t x=tmv C K.M.n base s x := by
      unfold tmv
      rw [jacTree_ro_words hL ut hI.scr.nowrap hx]
    rw [ev _ (by simp [winRo]),ev _ (by simp [winRo]),ev _ (by simp [winRo])]
    exact hP
  · intro a ha ha1
    obtain rfl : a=1 := by omega
    rw [mul_one_pt]
    unfold tmv at jc ⊢
    rw [kt.mem]
    exact jc
  · simpa only [Nat.mul_one] using pt
  · have hcl : ∀ r∈clob K.M.n, r∈jacTreeClob K := fun _ hr => List.mem_append_left _ hr
    have kb' := (Keeps.regs kb).mono (rs' := jacTreeClob K) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [jacTreeClob])
    have kt' := (Keeps.regs kt).mono (rs' := jacTreeClob K)
      (fun _ hr => List.mem_append_right _ hr)
    exact ((⟨ka.gpr,ka.rd,ka.wr,ka.sp⟩ : KeepRegs (clob K.M.n) s a).mono hcl).trans
      (kb'.trans (((⟨kc.gpr,kc.rd,kc.wr,kc.sp⟩ : KeepRegs (clob K.M.n) b c).mono hcl).trans kt'))



/-- Construct all sixteen positive multiples using the addition/doubling tree. -/
theorem jacTree_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    (ht : K.tbl<4096) (hOne : K.one<C.p) {P : Point C} (hP : onCurve C P=true)
    {s : State} (hI : Inv K.M base size C.p (·∈jacWinSlots K) (winRo K) (tmv C K.M.n base s) s)
    (hJP : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
      (tmv C K.M.n base s K.P.z) P) :
    WP isa (Jacobian.jacBuildTree K 16) s (fun t => JacTreeInv K C base size P s t 16) := by
  unfold Jacobian.jacBuildTree
  refine WP.seq (WP.mono (jacTree_init_ok hL hAl ht hI hJP) fun a ia => ?_)
  apply countLoop_ok (Inv := fun j t => JacTreeInv K C base size P s t (16-j))
    (n := 15) (by decide)
  · intro j u hj hj15 hu
    refine WP.mono (jacTree_step_ok hL hJ hAl hm hC ha ht hOne hP (by omega) (by omega) hu)
      fun t it => ?_
    have he : 16-j+1=16-(j-1) := by omega
    refine ⟨he ▸ it,?_⟩
    have hc := it.counter
    have he' : 16-(16-j+1)=j-1 := by omega
    rwa [he'] at hc
  · intro t it; exact it
  · decide
  · exact ia

/-- Table construction initializes the complete variable-window environment. -/
theorem JacTreeInv.ready {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat}
    {P : Point C} {s t : State} (hL : JacWinLay K size) (hI : JacTreeInv K C base size P s t 16)
    (hz : wordsVal s.mem base K.zero K.M.n=0)
    (hb : ∀ i<260, s.mem (off base (K.bits+i))=if k.testBit i then 1 else 0) :
    Inv K.M base size C.p (·∈jacWinSlots K) (jacLive K) (tmv C K.M.n base t) t ∧
      JacStable K C base P k t := by
  refine ⟨jacTreeLive_full K ▸ hI.field,?_,hI.table,?_⟩
  · rw [jacTree_ro_words hL hI.unch hI.field.scr.nowrap (by simp [winRo]),hz]
  · intro i hi
    have hn := hI.field.scr.nowrap
    rw [hI.unch.byte (fun w hw => ?_) (by have := hL.bits; omega),hb i hi]
    simp only [jacTreeWrites,List.mem_append,List.mem_map,List.mem_singleton] at hw
    rcases hw with ⟨x,hx,rfl⟩ | rfl
    · have hb' := hL.bits_w x hx
      dsimp only; rw [hL.n]; omega
    · have hb' := hL.bits_tmp
      dsimp only; rw [hL.n]; omega


end VG.Proof.Weierstrass.AArch64
