module

public import VerifiedGarbage.Proof.Weierstrass.X86.NafAdjust
public import VerifiedGarbage.Proof.Weierstrass.X86.TCombOne
import VerifiedGarbage.Proof.Weierstrass.X86.NafPoint
import VerifiedGarbage.Proof.Weierstrass.X86.JacAdd
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86.RegUpd
public import VerifiedGarbage.Proof.Weierstrass.WinLay
public import VerifiedGarbage.Impl.Weierstrass.X86.Naf
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Weierstrass.X86.NafLayout`, which this module and modules that import it used -/

section

/-! The eight-entry odd-multiple table and cached double and its disjoint scratch slots. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86
open VG VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Proof.Mont

def nafTblSlots (K : WinCfg) : List Nat := (List.range 27).map fun i => K.tbl+32*i

def nafSlots (K : WinCfg) : List Nat := winRo K ++ winOther K ++ nafTblSlots K

def nafWrites (K : WinCfg) : List Nat := winOther K ++ nafTblSlots K

/-- The five-bit loop has eight odd multiples, one cached double, and 260 scalar bytes. -/
structure NafLay (K : WinCfg) (size : Nat) : Prop where
  size_le : size ≤ 8192
  n : K.M.n = 4
  lay : Lay K.M size (· ∈ nafSlots K)
  ro : ∀ x ∈ winRo K, x ∉ winOther K
  nodup : (winOther K).Nodup
  tbl : ∀ x ∈ winRo K ++ winOther K, x+32 ≤ K.tbl ∨ K.tbl+864 ≤ x
  bits : K.bits+260 ≤ size
  bits_w : ∀ w ∈ nafWrites K, K.bits+260 ≤ w ∨ w+32 ≤ K.bits
  bits_tmp : K.bits+260 ≤ K.M.tmp ∨ K.M.tmp+32 ≤ K.bits
  exy : K.E.y = K.E.x+32
  exz : K.E.z = K.E.x+64
  rxy : K.R.y = K.R.x+32
  rxz : K.R.z = K.R.x+64

/-- A coordinate of an entry from 1 through 9 is one of the table slots. -/
theorem nafTbl_mem (K : WinCfg) {a c : Nat} (ha : 1 ≤ a) (h9 : a ≤ 9) (hc : c < 3) :
    K.tbl+96*(a-1)+32*c ∈ nafTblSlots K := by
  apply List.mem_map.mpr
  refine ⟨3*(a-1)+c,List.mem_range.mpr (by omega),?_⟩
  omega_using []

/-- Every coordinate of a table point belongs to the complete environment. -/
theorem nafTblPt_mem (K : WinCfg) (hn : K.M.n=4) {a : Nat} (ha : 1 ≤ a) (h9 : a ≤ 9) :
    ∀ x ∈ [(K.tblPt a).x,(K.tblPt a).y,(K.tblPt a).z],
      x ∈ nafSlots K := by
  intro x hx
  apply List.mem_append_right
  simp only [WinCfg.tblPt,hn,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact nafTbl_mem K ha h9 (c := 0) (by decide)
  · exact nafTbl_mem K ha h9 (c := 1) (by decide)
  · exact nafTbl_mem K ha h9 (c := 2) (by decide)

/-- The complete 864-byte table fits in the scratch allocation. -/
theorem NafLay.table_le {K : WinCfg} {size : Nat} (hL : NafLay K size) :
    K.tbl+864 ≤ size := by
  have h := hL.lay.le (K.tbl+32*26) (List.mem_append_right _
    (List.mem_map.mpr ⟨26,by decide,rfl⟩))
  rw [hL.n] at h
  omega_using [h]

/-- The previous eight-entry layout is a sub-layout of this allocation. -/
theorem NafLay.old_slots {K : WinCfg} {size : Nat} (hL : NafLay K size) :
    ∀ x ∈ winSlots K, x ∈ nafSlots K := by
  intro x hx
  simp only [winSlots,nafSlots,List.mem_append] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl hx
  · apply Or.inr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    apply List.mem_map.mpr
    refine ⟨i,List.mem_range.mpr (by have := List.mem_range.mp hi; omega_using [this]),?_⟩
    simp only [hL.n]

/-- Existing coordinate and scratch-separation lemmas remain available for
the working points, while the new table includes the cached double. -/
theorem NafLay.toWinLay {K : WinCfg} {size : Nat} (hL : NafLay K size)
    (hJ : K.J=65) : WinLay K size := by
  refine ⟨?_,hL.ro,hL.nodup,?_,by rw [hL.n]; decide,by rw [hJ]; decide,?_,?_⟩
  · exact { le := fun x hx => hL.lay.le x (hL.old_slots x hx)
            mo := fun x hx => hL.lay.mo x (hL.old_slots x hx)
            tmp := fun x hx => hL.lay.tmp x (hL.old_slots x hx)
            apart := fun x y hx hy hxy => hL.lay.apart x y (hL.old_slots x hx) (hL.old_slots y hy) hxy }
  · intro x hx
    have := hL.tbl x hx
    rw [hL.n]; omega_using [this]
  · have := hL.bits; rw [hJ]; omega_using [this]
  · intro w hw
    simp only [winW,List.mem_append,List.mem_map,List.mem_singleton] at hw
    rcases hw with ⟨x,hx,rfl⟩ | rfl
    · have hnew : x ∈ nafWrites K := by
        simp only [winWs,nafWrites,List.mem_append] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl hx
        · apply Or.inr
          obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
          apply List.mem_map.mpr
          refine ⟨i,List.mem_range.mpr (by have := List.mem_range.mp hi; omega_using [this]),?_⟩
          simp only [hL.n]
      have := hL.bits_w x hnew
      dsimp only
      rw [hL.n,hJ]; omega_using [this]
    · have := hL.bits_tmp
      dsimp only
      rw [hL.n,hJ]; omega_using [this]

/-- Reversing the two work points also separates all doubling operands. -/
theorem NafLay.rcbApart_DR {K : WinCfg} {size : Nat} (hL : NafLay K size) :
    RcbApart K.S K.D K.D K.R := by
  have hnd := hL.nodup
  have ha := hL.ro K.S.a (by simp [winRo])
  have hb := hL.ro K.S.b3 (by simp [winRo])
  simp only [winOther,rcbW,List.cons_append,List.nil_append,List.nodup_cons,
    List.mem_cons,List.not_mem_nil,or_false,not_or] at hnd ha hb
  refine ⟨?_,?_⟩ <;>
    simp only [rcbW,rcbR,List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,
      List.nodup_nil,and_true,forall_eq_or_imp,forall_eq] <;> grind

/-- The running odd multiple and cached double can be added into `D`. -/
theorem NafLay.rcbApart_twice {K : WinCfg} {size : Nat} (hL : NafLay K size) (hJ : K.J=65) :
    RcbApart K.S K.R (Naf.twice K) K.D := by
  have h := (hL.toWinLay hJ).rcbApart_D (Or.inl rfl)
  refine ⟨h.nodup,fun x hx hw => ?_⟩
  have he : x∈rcbR K.S K.R K.R ∨ x∈[(Naf.twice K).x,(Naf.twice K).y,(Naf.twice K).z] := by
    simp only [rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  rcases he with he | he
  · exact h.apart x he hw
  · have sep := hL.tbl x (List.mem_append_right _ (List.mem_append_right _ hw))
    simp only [Naf.twice,WinCfg.tblPt,hL.n,List.mem_cons,List.not_mem_nil,or_false] at he
    omega_using [sep, he]

/-- The initial double goes into the ninth point, outside the eight-entry odd table. -/
theorem NafLay.rcbApart_init {K : WinCfg} {size : Nat} (hL : NafLay K size) (hJ : K.J=65) :
    RcbApart K.S K.P K.P (Naf.twice K) := by
  let ts := [K.S.t0,K.S.t1,K.S.t2,K.S.t3,K.S.t4,K.S.t5]
  have ets (o : Pt) : rcbW K.S o=ts++[o.x,o.y,o.z] := rfl
  have hn := (hL.toWinLay hJ).other_ne.2.2.2.2.2.2.2.2.2
  rw [ets,List.nodup_append] at hn
  have hts : ∀ x∈ts, x∈winRo K++winOther K := rcbW_mem_other
  have ht : ∀ x∈winRo K++winOther K,
      x∉[(Naf.twice K).x,(Naf.twice K).y,(Naf.twice K).z] := by
    intro x hx he
    have sep := hL.tbl x hx
    simp only [Naf.twice,WinCfg.tblPt,hL.n,List.mem_cons,List.not_mem_nil,or_false] at he
    omega_using [sep, he]
  refine ⟨?_,?_⟩
  · rw [ets,List.nodup_append]
    refine ⟨hn.1,?_,fun x hx y hy he => ht x (hts x hx) (he ▸ hy)⟩
    simp only [Naf.twice,WinCfg.tblPt,hL.n,List.nodup_cons,List.mem_cons,List.not_mem_nil,
      or_false,not_or,List.nodup_nil,not_false_eq_true,and_true]
    and_intros <;> omega_using []
  · intro x hx hw
    have hr : x∈winRo K := by
      simp only [rcbR,winRo,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
      grind
    rw [ets,List.mem_append] at hw
    rcases hw with hw | hw
    · exact hL.ro x hr (List.mem_append_right _ (List.mem_append_left _ hw))
    · exact ht x (List.mem_append_left _ hr) hw

end VG.Proof.Weierstrass.X86

end

end

/-! ## `NafTableState` -/

@[expose] public section

section

/-! The odd-multiple table retains its initialized prefix and cached double. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont Spec.Weierstrass

def nafTableSlots (K : WinCfg) (m : Nat) : List Nat :=
  (List.range (3*m)).map fun i => K.tbl+32*i

def nafTableLive (K : WinCfg) (m : Nat) : List Nat :=
  winRo K++jacCoords K.R++jacCoords (Naf.twice K)++nafTableSlots K m

def nafTableClob (_K : WinCfg) : List Reg := clob++[.esi]

def nafTableWrites (K : WinCfg) (wk : Nat) : List (Nat×Nat) :=
  (nafWrites K).map (·,8*K.M.n)++[(K.M.tmp,8*K.M.n),(wk,64*K.M.n),Mont.outW]

structure NafTableInv (K : WinCfg) (C : Curve) (base : Addr) (size wk : Nat)
    (P : Point C) (s₀ s : State) (m : Nat) : Prop where
  field : Inv K.M base size C.p (·∈nafSlots K) (nafTableLive K m) (tmv C K.M.n base s) s
  point : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y)
    (tmv C K.M.n base s K.R.z) (mul (2*m-1) P)
  twice : InvJ C (tmv C K.M.n base s (Naf.twice K).x) (tmv C K.M.n base s (Naf.twice K).y)
    (tmv C K.M.n base s (Naf.twice K).z) (mul 2 P)
  table : ∀ a,1≤a → a≤m → InvJ C (tmv C K.M.n base s (K.tblPt a).x)
    (tmv C K.M.n base s (K.tblPt a).y) (tmv C K.M.n base s (K.tblPt a).z) (mul (2*a-1) P)
  counter : s.gpr .esi=BitVec.ofNat 32 m
  keep : KeepRegs (nafTableClob K) s₀ s
  unch : Unch base (nafTableWrites K wk) s₀.mem s.mem

theorem nafTableLive_read (K : WinCfg) (m : Nat) :
    ∀ x∈rcbR K.S K.R (Naf.twice K),x∈nafTableLive K m := by
  intro x hx
  simp only [nafTableLive,jacCoords,winRo,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

theorem nafTableLive_next (K : WinCfg) (hn : K.M.n=4) (m : Nat) :
    ∀ x∈nafTableLive K (m+1),x∈jacCoords (K.tblPt (m+1))++jacCoords K.R++
      (jacCoords K.D++nafTableLive K m) := by
  intro x hx
  simp only [nafTableLive,List.mem_append] at hx
  rcases hx with ((hx|hx)|hx)|hx
  all_goals try {simp only [List.mem_append,nafTableLive]; grind}
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
  have hi' := List.mem_range.mp hi
  by_cases h : i<3*m
  · have ho : K.tbl+32*i∈nafTableLive K m := List.mem_append_right _
      (List.mem_map.mpr ⟨i,List.mem_range.mpr h,rfl⟩)
    simp only [List.mem_append]; grind
  · have hn' : K.tbl+32*i∈jacCoords (K.tblPt (m+1)) := by
      simp only [jacCoords,WinCfg.tblPt,hn,List.mem_cons,List.not_mem_nil,or_false]
      omega_arith
    simp only [List.mem_append]; grind

theorem nafTable_progUnch {K : WinCfg} {base : Addr} {wk : Nat} {W : List Nat} {s t : State}
    (hk : ProgKeep K.M base wk W s t) (hw : ∀ x∈W,x∈nafWrites K) :
    Unch base (nafTableWrites K wk) s.mem t.mem := by
  apply hk.unch.mono
  intro w hw'
  simp only [nafTableWrites,progW,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hw' ⊢
  rcases hw' with ⟨x,hx,rfl⟩|rfl|rfl|rfl
  · exact Or.inl ⟨x,hw x hx,rfl⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem nafTable_advance_ok {s : State} {m : Nat} (hm : m<8)
    (hc : s.gpr .esi=BitVec.ofNat 32 m) :
    WP isa (.block [.alu .add .esi (.imm 1),.alu .cmp .esi (.imm 8)]) s fun t =>
      t.gpr .esi=BitVec.ofNat 32 (m+1) ∧ t.cf=some (decide (m+1<8)) ∧ CKeeps [.esi] s t := by
  have he : BitVec.ofNat 32 m+(1 : BitVec 32)=BitVec.ofNat 32 (m+1) := by
    change BitVec.ofNat 32 m+BitVec.ofNat 32 1=_
    rw [BitVec.ofNat_add]
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.cf_arithFlags,
    ite_true,hc,he,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · congr 1
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show m+1<2^32 from by omega_arith)]
    rfl
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

end VG.Proof.Weierstrass.X86

end

/-! ## `NafTableCopy` -/

section

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont Spec.Weierstrass

theorem nafCopyStore_ok {F : Impl.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size m wk : Nat}
    (hL : NafLay K size) (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K)) (hm : m<8) 
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (·∈nafSlots K) V E s)
    (hV : ∀ x∈jacCoords K.D,x∈V) (hc : s.gpr .esi=BitVec.ofNat 32 m)
    {P : Point C} (hp : InvJ C (E K.D.x) (E K.D.y) (E K.D.z) P) :
    WP isa (.block (copyPt 4 K.R K.D++Naf.tableStore K)) s fun t =>
      ProgKeep K.M base wk (jacCoords K.R++jacCoords (K.tblPt (m+1))) s t ∧
      Inv K.M base size C.p (·∈nafSlots K) (jacCoords (K.tblPt (m+1))++jacCoords K.R++V) (tmv C K.M.n base t) t ∧
      InvJ C (tmv C K.M.n base t K.R.x) (tmv C K.M.n base t K.R.y) (tmv C K.M.n base t K.R.z) P ∧
      InvJ C (tmv C K.M.n base t (K.tblPt (m+1)).x) (tmv C K.M.n base t (K.tblPt (m+1)).y)
        (tmv C K.M.n base t (K.tblPt (m+1)).z) P := by
  have rr : ∀ x∈jacCoords K.R,x∈winOther K := by
    intro x hx
    simp only [jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have rs : ∀ x∈jacCoords K.R,x∈nafSlots K := fun x hx =>
    List.mem_append_left _ (List.mem_append_right _ (rr x hx))
  have hA := hL.rcbApart_DR
  have hN : (jacCoords K.R).Nodup := hA.nodup.drop (i:=6)
  have hqa : ∀ x∈jacCoords K.D,∀ y∈jacCoords K.R,x≠y := by
    intro x hx y hy he
    apply hA.apart x (by
      simp only [jacCoords,rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
      grind)
    rw [he]
    simp only [jacCoords,rcbW,List.mem_cons,List.not_mem_nil,or_false] at hy ⊢
    grind
  have sep : K.R.x+96≤K.tbl ∨ K.tbl+768≤K.R.x := by
    have hx := hL.tbl K.R.x (List.mem_append_right _ (rr _ (by simp [jacCoords])))
    have hz := hL.tbl K.R.z (List.mem_append_right _ (rr _ (by simp [jacCoords])))
    rw [hL.rxz] at hz
    omega_arith
  rw [WP.block_append_iff,←hL.n]
  refine WP.mono (copyPointFields_ok hL.lay hAcc hN hqa rs hI hV) fun a ⟨ea,ka,ia,va⟩ => ?_
  have ja : InvJ C (tmv C K.M.n base a K.R.x) (tmv C K.M.n base a K.R.y) (tmv C K.M.n base a K.R.z) P := by
    apply ia.point_tmv (fun _ hx => List.mem_append_left _ hx)
    simp only [Prod.mk.injEq] at va
    rw [va.1,va.2.1,va.2.2]
    exact hp
  have ca : a.gpr .esi=BitVec.ofNat 32 m := (ka.gpr _ (by decide)).trans hc
  have ts := nafTblPt_mem K hL.n (a:=m+1) (by omega_arith) (by omega_arith)
  refine WP.mono (nafTablePoint_ok hL.lay hAcc hL.n hL.rxy hL.rxz ia.to_tmv hm ca
    (by have := hL.table_le; omega_arith) ts (fun _ hx => List.mem_append_left _ hx) sep ja)
    fun t ⟨kt,it,jt⟩ => ?_
  refine ⟨(ka.mono (fun _ hx => List.mem_append_left _ hx)).trans
      (kt.mono (fun _ hx => List.mem_append_right _ hx)),?_,?_,jt⟩
  · exact it.sub (by intro x hx; simpa only [List.mem_append,or_assoc] using hx)
  · apply kt.invJ hL.lay hAcc ia.scr ts rs ?_ ja
    intro x hx hy
    have hs := hL.tbl x (List.mem_append_right _ (rr x hx))
    simp only [jacCoords,WinCfg.tblPt,hL.n,List.mem_cons,List.not_mem_nil,or_false] at hy
    omega_arith

end VG.Proof.Weierstrass.X86

end

/-! ## `NafTableInit` -/

section

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont Spec.Weierstrass

theorem nafTable_initCounter_ok (s : State) :
    WP isa (.block [.mov .esi (.imm 1)]) s fun t => t.gpr .esi=1 ∧ CKeeps [.esi] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,readSrc,
    Option.map_some,RegUpd.gpr_setReg,ite_true,Option.some.injEq,exists_eq_left']
  exact ⟨trivial,fun r hr => by simp only [List.mem_singleton] at hr; simp only [RegUpd.gpr_setReg,hr,ite_false],rfl,rfl,rfl⟩

theorem nafTable_init_ok {F : Impl.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : NafLay K size) (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K)) (hJ : K.J=65) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hC : Law C) (ha : AM3 C) {P : Point C} (hP : onCurve C P=true) {s : State}
    (hI : Inv K.M base size C.p (·∈nafSlots K) (winRo K) (tmv C K.M.n base s) s)
    (hp : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y) (tmv C K.M.n base s K.P.z) P) :
    WP isa (.seq (fprog F (dblJMul K.S K.P (Naf.twice K)))
      (.block (copyPt 4 (K.tblPt 1) K.P++copyPt 4 K.R K.P++([.mov .esi (.imm 1)] : List Instr)))) s
      (fun t => NafTableInv K C base size wk P s t 1) := by
  have rr : ∀ x∈jacCoords K.R,x∈winOther K := by
    intro x hx; simp only [jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have pr : ∀ x∈jacCoords K.P,x∈winRo K := by
    intro x hx; simp only [jacCoords,winRo,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have slO : ∀ x∈winOther K,x∈nafSlots K := fun _ hx => List.mem_append_left _ (List.mem_append_right _ hx)
  have slR : ∀ x∈winRo K,x∈nafSlots K := fun _ hx => List.mem_append_left _ (List.mem_append_left _ hx)
  have bs := nafTblPt_mem K hL.n (a:=9) (by decide) (by decide)
  have ts := nafTblPt_mem K hL.n (a:=1) (by decide) (by decide)
  have bt (a : Nat) (ha : 1≤a) (ha9 : a≤9) : ∀ x∈jacCoords (K.tblPt a),x∈nafTblSlots K := by
    intro x hx
    simp only [jacCoords,WinCfg.tblPt,hL.n,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    · exact nafTbl_mem K ha ha9 (c:=0) (by decide)
    · exact nafTbl_mem K ha ha9 (c:=1) (by decide)
    · exact nafTbl_mem K ha ha9 (c:=2) (by decide)
  have dv : ∀ x∈rcbR K.S K.P K.P,x∈winRo K := by
    intro x hx; simp only [rcbR,winRo,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  have dw : ∀ x∈rcbW K.S (Naf.twice K),x∈nafWrites K := by
    intro x hx
    have he : x∈winOther K ∨ x∈jacCoords (Naf.twice K) := by
      simp only [rcbW,winOther,jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
    exact he.elim (List.mem_append_left _) (fun h => List.mem_append_right _ (bt 9 (by decide) (by decide) x h))
  have ds : ∀ x∈rcbW K.S (Naf.twice K)++rcbR K.S K.P K.P,x∈nafSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · have h := dw x hx
      simp only [nafWrites,nafSlots,List.mem_append] at h ⊢; grind
    · exact slR x (dv x hx)
  have da := hL.rcbApart_init hJ
  apply WP.seq
  refine WP.mono (jacDouble_ok hL.lay hAcc hm hC ha da ds hI dv hP hp) fun a ⟨ka,ia,ja⟩ => ?_
  have ja : InvJ C (tmv C K.M.n base a (Naf.twice K).x) (tmv C K.M.n base a (Naf.twice K).y)
      (tmv C K.M.n base a (Naf.twice K).z) (mul 2 P) := by
    have h := ia.point_tmv (fun _ hx => List.mem_append_left _ hx) ja
    rw [←mul_one_pt P,hC.add_mul_mul hP] at h
    simpa only [show 1+1=2 from rfl] using h
  have pa := ka.invJ hL.lay hAcc hI.scr (fun x hx => ds x (List.mem_append_left _ hx))
    (fun x hx => slR x (pr x hx)) (fun x hx => da.apart x (by
      simp only [jacCoords,rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind)) hp
  rw [List.append_assoc,WP.block_append_iff,←hL.n]
  refine WP.mono (copyPointFields_ok hL.lay hAcc (q:=K.P) (o:=K.tblPt 1)
    (by simp [jacCoords,WinCfg.tblPt,hL.n]) (by
      intro x hx y hy he
      have hs := hL.tbl x (List.mem_append_left _ (pr x hx))
      simp only [jacCoords,WinCfg.tblPt,hL.n,List.mem_cons,List.not_mem_nil,or_false] at hy
      omega_arith) ts ia.to_tmv (fun x hx => List.mem_append_right _ (pr x hx))) fun b ⟨eb,kb,ib,vb⟩ => ?_
  have jb : InvJ C (tmv C K.M.n base b (K.tblPt 1).x) (tmv C K.M.n base b (K.tblPt 1).y)
      (tmv C K.M.n base b (K.tblPt 1).z) P := by
    apply ib.point_tmv (fun _ hx => List.mem_append_left _ hx)
    simp only [Prod.mk.injEq] at vb
    rw [vb.1,vb.2.1,vb.2.2]; exact pa
  have pb := kb.invJ hL.lay hAcc ia.scr ts (fun x hx => slR x (pr x hx)) (by
    intro x hx hy
    have hs := hL.tbl x (List.mem_append_left _ (pr x hx))
    simp only [jacCoords,WinCfg.tblPt,hL.n,List.mem_cons,List.not_mem_nil,or_false] at hy; omega_arith) pa
  have bb := kb.invJ hL.lay hAcc ia.scr ts bs (by
    intro x hx hy
    simp only [jacCoords,WinCfg.tblPt,hL.n,List.mem_cons,List.not_mem_nil,or_false] at hx hy; omega_arith) ja
  rw [WP.block_append_iff]
  refine WP.mono (copyPointFields_ok hL.lay hAcc (q:=K.P) (o:=K.R)
    (by simp [jacCoords,hL.rxy,hL.rxz])
    (fun x hx y hy he => hL.ro x (pr x hx) (he ▸ rr y hy))
    (fun x hx => slO x (rr x hx)) ib.to_tmv
    (fun x hx => List.mem_append_right _ (List.mem_append_right _ (pr x hx)))) fun c ⟨ec,kc,ic,vc⟩ => ?_
  have jc : InvJ C (tmv C K.M.n base c K.R.x) (tmv C K.M.n base c K.R.y) (tmv C K.M.n base c K.R.z) P := by
    apply ic.point_tmv (fun _ hx => List.mem_append_left _ hx)
    simp only [Prod.mk.injEq] at vc
    rw [vc.1,vc.2.1,vc.2.2]; exact pb
  have sep (a : Nat) (ha : 1≤a) (ha9 : a≤9) : ∀ x∈jacCoords (K.tblPt a),x∉jacCoords K.R := by
    intro x hx hy
    have hs := hL.tbl x (List.mem_append_right _ (rr x hy))
    simp only [jacCoords,WinCfg.tblPt,hL.n,List.mem_cons,List.not_mem_nil,or_false] at hx; omega_arith
  have bc := kc.invJ hL.lay hAcc ib.scr (fun x hx => slO x (rr x hx)) bs (sep 9 (by decide) (by decide)) bb
  have tc := kc.invJ hL.lay hAcc ib.scr (fun x hx => slO x (rr x hx)) ts (sep 1 (by decide) (by decide)) jb
  refine WP.mono (nafTable_initCounter_ok c) fun t ⟨ct,kt⟩ => ?_
  have it := (ic.of_keeps kt (by decide)).to_tmv
  have ua := nafTable_progUnch ka dw
  have ub := nafTable_progUnch kb (fun x hx => List.mem_append_right _ (bt 1 (by decide) (by decide) x hx))
  have uc := nafTable_progUnch kc (fun x hx => List.mem_append_left _ (rr x hx))
  refine ⟨it.sub ?_,?_,?_,?_,ct,?_,?_⟩
  · intro x hx
    simp only [nafTableLive,jacCoords,nafTableSlots,Naf.twice,WinCfg.tblPt,hL.n,List.range_succ,List.range_zero,
      List.map_append,List.map_cons,List.map_nil,List.nil_append,Nat.mul_one,Nat.sub_self,Nat.mul_zero,Nat.add_zero,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false,show 32*2=64 from rfl] at hx ⊢
    grind
  · rw [show 2*1-1=1 from rfl,mul_one_pt]; simpa only [tmv,kt.2.1] using jc
  · simpa only [tmv,kt.2.1,Naf.twice] using bc
  · intro a ha ha1
    obtain rfl : a=1 := by omega_arith
    rw [show 2*1-1=1 from rfl,mul_one_pt]; simpa only [tmv,kt.2.1] using tc
  · have lift {W : List Nat} {u v : State} (k : ProgKeep K.M base wk W u v) : KeepRegs (nafTableClob K) u v :=
      (Keeps.mono ⟨k.gpr,k.rd,k.wr⟩ (fun _ hx => List.mem_append_left _ hx))
    exact (lift ka).trans ((lift kb).trans ((lift kc).trans
      ((CKeeps.regs kt).mono (fun _ hx => List.mem_append_right _ hx))))
  · rw [kt.2.1]
    exact (ua.trans (ub.trans uc)).mono (by intro w hw; simpa only [List.mem_append,or_self] using hw)

end VG.Proof.Weierstrass.X86

end

/-! ## `NafTableStep` -/

section

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont Spec.Weierstrass

theorem nafTable_step_ok {F : Impl.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size m wk : Nat}
    (hL : NafLay K size) (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K)) (hJ : K.J=65)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
     (hOne : K.one<C.p) {P : Point C} (hP : onCurve C P=true)
    (hm1 : 1≤m) (hm7 : m≤7) {s₀ s : State} (hI : NafTableInv K C base size wk P s₀ s m) :
    WP isa (Naf.tableStep K F) s fun t => NafTableInv K C base size wk P s₀ t (m+1) ∧ t.cf=some (decide (m+1<8)) := by
  have hf := hI.field
  have hv := nafTableLive_read K m
  have ds : ∀ x∈rcbW K.S K.D ++ rcbR K.S K.R (Naf.twice K), x∈nafSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ hx))
    · have he : x∈winRo K ++ winOther K ∨ x∈jacCoords (Naf.twice K) := by
        simp only [rcbR,winRo,winOther,jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
        grind
      rcases he with he | he
      · exact List.mem_append_left _ he
      · exact nafTblPt_mem K hL.n (by decide) (by decide) x he
  unfold Naf.tableStep
  apply WP.seq
  refine WP.mono (jacAdd_ok hL.lay hAcc hm hC ha (hL.rcbApart_twice hJ) ds hf hv hOne
    (hC.onCurve_mul hP _) (hC.onCurve_mul hP _) hI.point hI.twice) fun u ⟨eu,ka,iu,ju⟩ => ?_
  have jw : InvJ C (eu K.D.x) (eu K.D.y) (eu K.D.z) (mul (2*(m+1)-1) P) := by
    rw [hC.add_mul_mul hP,show 2*m-1+2=2*(m+1)-1 by omega_arith] at ju
    exact ju
  have ka := ka.mono (W' := winOther K) (fun _ hx => List.mem_append_right _ hx)
  have cm : u.gpr .esi=BitVec.ofNat 32 m := by
    rw [ka.gpr _ (by decide),hI.counter]
  rw [WP.block_append_iff]
  refine WP.mono (nafCopyStore_ok hL hAcc (by omega_arith) iu
    (fun _ hx => List.mem_append_left _ hx) cm jw) fun v ⟨ks,iv,jr,jnew⟩ => ?_
  let W := winOther K ++ jacCoords (K.tblPt (m+1))
  have kas : ProgKeep K.M base wk W s v := (ka.mono (fun _ hx => List.mem_append_left _ hx)).trans (ks.mono (by
    intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · apply List.mem_append_left
      simp only [jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
      grind
    · exact List.mem_append_right _ hx))
  have cb : v.gpr .esi=BitVec.ofNat 32 m := by
    rw [kas.gpr _ (by decide),hI.counter]
  refine WP.mono (nafTable_advance_ok (by omega_arith) cb) fun t ⟨hc,cf,kc⟩ => ?_
  have it := (iv.of_keeps kc (by decide)).to_tmv.sub (nafTableLive_next K hL.n m)
  have slots : ∀ x∈W, x∈nafSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (List.mem_append_right _ hx)
    · exact nafTblPt_mem K hL.n (by omega_arith) (by omega_arith) x hx
  have kct : KeepRegs (nafTableClob K) v t := (CKeeps.regs kc).mono (fun _ hx => List.mem_append_right _ hx)
  have kst : KeepRegs (nafTableClob K) s t :=
    (Keeps.mono ⟨kas.gpr,kas.rd,kas.wr⟩ (fun _ hx => List.mem_append_left _ hx)).trans kct
  have uw : Unch base (nafTableWrites K wk) s.mem t.mem := by
    rw [kc.2.1]
    apply kas.unch.mono
    intro w hw
    simp only [nafTableWrites,nafWrites,progW,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
    rcases hw with ⟨x,hx,rfl⟩ | rfl | rfl | rfl
    · refine Or.inl ⟨x,?_,rfl⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact Or.inl hx
      · apply Or.inr
        simp only [WinCfg.tblPt,hL.n,jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact nafTbl_mem K (by omega_arith) (by omega_arith) (c:=0) (by decide)
        · exact nafTbl_mem K (by omega_arith) (by omega_arith) (c:=1) (by decide)
        · exact nafTbl_mem K (by omega_arith) (by omega_arith) (c:=2) (by decide)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  have beq (x : Nat) (hx : x∈jacCoords (Naf.twice K)) : tmv C K.M.n base t x=tmv C K.M.n base s x := by
    unfold tmv; rw [kc.2.1]
    rw [kas.slot hL.lay hAcc hf.scr slots (nafTblPt_mem K hL.n (by decide) (by decide) x hx) ?_]
    intro hw
    rcases List.mem_append.mp hw with hw | hw
    · have sep := hL.tbl x (List.mem_append_right _ hw)
      simp only [jacCoords,Naf.twice,WinCfg.tblPt,hL.n,List.mem_cons,List.not_mem_nil,or_false] at hx
      omega_arith
    · simp only [jacCoords,Naf.twice,WinCfg.tblPt,hL.n,List.mem_cons,List.not_mem_nil,or_false] at hx hw
      omega_arith
  refine ⟨⟨it,?_,?_,?_,hc,hI.keep.trans kst,?_⟩,cf⟩
  · simpa only [tmv,kc.2.1] using jr
  · rw [beq _ (by simp [jacCoords]),beq _ (by simp [jacCoords]),beq _ (by simp [jacCoords])]
    exact hI.twice
  · intro a ha1 ham
    by_cases he : a=m+1
    · subst a; simpa only [tmv,kc.2.1] using jnew
    · have ham' : a≤m := by omega_arith
      have teq (x : Nat) (hx : x∈jacCoords (K.tblPt a)) :
          tmv C K.M.n base t x=tmv C K.M.n base s x := by
        unfold tmv; rw [kc.2.1]
        rw [kas.slot hL.lay hAcc hf.scr slots (nafTblPt_mem K hL.n ha1 (by omega_arith) x hx) ?_]
        intro hw
        rcases List.mem_append.mp hw with hw | hw
        · have sep := hL.tbl x (List.mem_append_right _ hw)
          simp only [jacCoords,WinCfg.tblPt,hL.n,List.mem_cons,List.not_mem_nil,or_false] at hx
          omega_arith
        · simp only [jacCoords,WinCfg.tblPt,hL.n,List.mem_cons,List.not_mem_nil,or_false] at hx hw
          omega_arith
      rw [teq _ (by simp [jacCoords]),teq _ (by simp [jacCoords]),teq _ (by simp [jacCoords])]
      exact hI.table a ha1 ham'
  · exact (hI.unch.trans uw).mono (fun _ hw => (List.mem_append.mp hw).elim id id)

end VG.Proof.Weierstrass.X86

end

/-! ## `NafTable` -/

section

/-! Construction of the eight odd multiples used by the public verifier. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

/-- Build `P, 3P, …, 15P`, retaining the double in the ninth point. -/
theorem nafTable_ok {F : Impl.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : NafLay K size) (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K)) (hJ : K.J=65)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
     (hOne : K.one<C.p) {P : Point C} (hP : onCurve C P=true)
    {s : State} (hI : Inv K.M base size C.p (·∈nafSlots K) (winRo K) (tmv C K.M.n base s) s)
    (hJP : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
      (tmv C K.M.n base s K.P.z) P) :
    WP isa (Naf.table K F) s (fun t => NafTableInv K C base size wk P s t 8) := by
  unfold Naf.table
  apply WP.assoc
  refine WP.seq (WP.mono (nafTable_init_ok hL hAcc hJ hm hC ha hP hI hJP) fun a ia => ?_)
  refine WP.loop (M:=isa)
    (fun j t => 1≤j ∧ j≤7 ∧ NafTableInv K C base size wk P s t (8-j))
    (fun j u ⟨hj,hj7,hu⟩ => ?_) 7 a ⟨by decide,by decide,ia⟩
  refine WP.mono (nafTable_step_ok hL hAcc hJ hm hC ha hOne hP (by omega_arith) (by omega_arith) hu)
    fun t ⟨it,cf⟩ => ?_
  by_cases hj1 : j=1
  · subst j
    exact Or.inl ⟨cf,it⟩
  · refine Or.inr ⟨?_,j-1,by omega_arith,by omega_arith,by omega_arith,?_⟩
    · change t.cf=some true
      rw [cf]; exact congrArg some (decide_eq_true (by omega_arith))
    · rw [show 8-(j-1)=8-j+1 from by omega_arith]
      exact it

/-- Table construction leaves the recoded scalar bytes intact. -/
theorem NafTableInv.digits {K : WinCfg} {C : Curve} {base : Addr} {size m wk : Nat}
    {P : Point C} {β : Nat → BitVec 8} {s t : State} (hL : NafLay K size) (hBitsWk : K.bits+260≤wk)
    (hI : NafTableInv K C base size wk P s t m)
    (hb : ∀ i<257, s.mem (off base (K.bits+i))=β i) :
    ∀ i<257, t.mem (off base (K.bits+i))=β i := by
  intro i hi
  rw [hI.unch.byte (fun w hw => ?_) (by have := hL.bits; have := hI.field.scr.nowrap; omega_arith),hb i hi]
  simp only [nafTableWrites,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with ⟨x,hx,rfl⟩ | rfl | rfl | rfl
  · have hb' := hL.bits_w x hx
    dsimp only; rw [hL.n]; omega_arith
  · have hb' := hL.bits_tmp
    dsimp only; rw [hL.n]; omega_arith

  · dsimp only; omega_arith
  · have := hL.bits; have := hL.size_le
    dsimp only [Mont.outW]; omega_arith

end VG.Proof.Weierstrass.X86

end
