import VerifiedGarbage.Proof.Weierstrass.X86.NafLayout
import VerifiedGarbage.Proof.Weierstrass.X86.NafPoint
import VerifiedGarbage.Proof.Weierstrass.X86.JacAdd

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
      omega
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
    rw [Nat.mod_eq_of_lt (show m+1<2^32 from by omega)]
    rfl
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

end VG.Proof.Weierstrass.X86
