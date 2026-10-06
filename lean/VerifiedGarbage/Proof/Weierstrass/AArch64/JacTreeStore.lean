import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeArithmetic
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop

/-! Store the new table multiple and advance the public loop counters. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

def jacCoords (p : Pt) : List Nat := [p.x,p.y,p.z]

theorem ProgKeep.slot {M : Mod} {base : Addr} {size : Nat} {Sl : Nat → Prop}
    {s t : State} {W : List Nat} (hL : Lay M size Sl) (hs : Scr s base size)
    (hk : ProgKeep M base W s t) (hW : ∀ x∈W, Sl x) {x : Nat}
    (hx : Sl x) (hn : x∉W) : wordsVal t.mem base x M.n=wordsVal s.mem base x M.n := by
  apply hk.unch.wordsVal _ (by have := hL.le x hx; have := hs.nowrap; omega)
  intro w hw
  simp only [List.mem_append,List.mem_map,List.mem_singleton] at hw
  rcases hw with ⟨y,hy,rfl⟩ | rfl
  · exact hL.apart x y hx (hW y hy) (fun he => hn (he ▸ hy))
  · exact hL.tmp x hx

theorem jacAdvance_ok {s : State} {base : Addr} {m : Nat}
    (h19 : s.gpr .x19=BitVec.ofNat 64 (16-m))
    (h20 : s.gpr .x20=off base (m*96)) (hm : m≤15) :
    WP isa (.block [.addImm .x .x20 .x20 96,decCounter]) s fun t =>
      t.gpr .x19=BitVec.ofNat 64 (16-(m+1)) ∧
      t.gpr .x20=off base ((m+1)*96) ∧ Keeps [.x19,.x20] s t := by
  apply WP.of_runBlock
  simp only [decCounter,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    show (96:Nat)<4096 by decide,show (1:Nat)<4096 by decide,ite_true,RegUpd.gpr_write,
    BitVec.setWidth_eq,Size.bits,reduceCtorEq,ite_false,h19,h20,Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · rw [BitVec.ofNat_sub_ofNat_of_le (16-m) 1 (by decide) (by omega)]
    congr 1
  · simp only [off,Nat.add_mul,BitVec.ofNat_add,BitVec.add_assoc,Nat.one_mul]
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

/-- The pointer increment works relative to the beginning of the table. -/
theorem jacAdvanceTable_ok {K : WinCfg} {s : State} {base : Addr} {m : Nat}
    (h19 : s.gpr .x19=BitVec.ofNat 64 (16-m))
    (h20 : s.gpr .x20=off base (K.tbl+96*m)) (hm : m≤15) :
    WP isa (.block [.addImm .x .x20 .x20 96,decCounter]) s fun t =>
      t.gpr .x19=BitVec.ofNat 64 (16-(m+1)) ∧
      t.gpr .x20=off base (K.tbl+96*(m+1)) ∧ Keeps [.x19,.x20] s t := by
  have hp : s.gpr .x20=off (off base K.tbl) (m*96) := by
    rw [h20]; simp only [off,Nat.mul_comm,BitVec.ofNat_add,BitVec.add_assoc]
  refine WP.mono (jacAdvance_ok h19 hp hm) fun t ⟨hc,ht,hk⟩ => ⟨hc,?_,hk⟩
  rw [ht]; simp only [off,Nat.mul_comm,BitVec.ofNat_add,BitVec.add_assoc]

/-- Copy the newly computed multiple to the accumulator and its table slot. -/
theorem jacTreeCopyStore_ok {K : WinCfg} {C : Curve} {base : Addr} {size a : Nat}
    (hL : JacWinLay K size) (hAl : Aligned K.M (·∈jacWinSlots K))
    (ha : 1≤a) (ha16 : a≤16) {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (·∈jacWinSlots K) V E s)
    (hV : ∀ x∈rcbR K.S K.D K.D, x∈V)
    (h20 : s.gpr .x20=off base (K.tbl+96*(a-1))) {P : Point C}
    (hJ : InvJ C (E K.D.x) (E K.D.y) (E K.D.z) P) :
    WP isa (.block (copyPt 4 K.R K.D ++ Jacobian.tableStore K)) s fun t =>
      ProgKeep K.M base (winOther K ++ jacCoords (Jacobian.tablePt K a)) s t ∧
      Inv K.M base size C.p (·∈jacWinSlots K)
        (jacCoords (Jacobian.tablePt K a) ++ jacCoords K.R ++ V) (tmv C K.M.n base t) t ∧
      InvJ C (tmv C K.M.n base t K.R.x) (tmv C K.M.n base t K.R.y) (tmv C K.M.n base t K.R.z) P ∧
      InvJ C (tmv C K.M.n base t (Jacobian.tablePt K a).x)
        (tmv C K.M.n base t (Jacobian.tablePt K a).y) (tmv C K.M.n base t (Jacobian.tablePt K a).z) P := by
  have hs : ∀ x∈rcbW K.S K.R ++ rcbR K.S K.D K.D, x∈jacWinSlots K := by
    intro x hx; apply List.mem_append_left
    simp only [rcbW,rcbR,winRo,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have rmem : ∀ x∈jacCoords K.R, x∈winOther K := by
    intro x hx; simp only [jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have smem := jacTblPt_mem K ha ha16
  rw [WP.block_append_iff,← hL.n]
  refine WP.mono (copyPoint_ok hL.lay hAl hL.rcbApart_DR hs hI hV) fun u ⟨eu,ku,iu,hu⟩ => ?_
  have ju : InvJ C (eu K.R.x) (eu K.R.y) (eu K.R.z) P := by
    simp only [Prod.mk.injEq] at hu
    rw [hu.1,hu.2.1,hu.2.2]; exact hJ
  have pu : u.gpr .x20=off base (K.tbl+96*(a-1)) := by
    rw [ku.gpr _ (by rw [hL.n]; decide),h20]
  have sep : K.R.x+96≤K.tbl+96*(a-1) ∨ K.tbl+96*(a-1)+96≤K.R.x := by
    have x := hL.tbl K.R.x (List.mem_append_right _ (rmem _ (by simp [jacCoords])))
    have z := hL.tbl K.R.z (List.mem_append_right _ (rmem _ (by simp [jacCoords])))
    rw [hL.rxz] at z
    omega
  refine WP.mono (jacStorePoint_ok hL.lay hL.n hL.rxy hL.rxz iu pu
    (hAl.sl _ (hs _ (by simp [rcbW]))) smem (fun _ hx => List.mem_append_left _ hx) sep ju)
    fun t ⟨kt,it,jt⟩ => ⟨(ku.mono ?_).trans (kt.mono (fun _ hx => List.mem_append_right _ hx)),it,?_,jt⟩
  · intro x hx; apply List.mem_append_left
    simp only [rcbW,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  · have eqv (x : Nat) (hx : x∈jacCoords K.R) : tmv C K.M.n base t x = tmv C K.M.n base u x := by
      unfold tmv
      rw [kt.slot hL.lay iu.scr smem (List.mem_append_left _ (List.mem_append_right _ (rmem x hx))) ?_]
      intro ht
      simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
      simp only [Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases hx with rfl | rfl | rfl <;> rw [hL.rxy,hL.rxz] at * <;> omega
    rw [eqv _ (by simp [jacCoords]),eqv _ (by simp [jacCoords]),eqv _ (by simp [jacCoords])]
    exact iu.point_tmv (fun _ hx => List.mem_append_left _ hx) ju

end VG.Proof.Weierstrass.AArch64
