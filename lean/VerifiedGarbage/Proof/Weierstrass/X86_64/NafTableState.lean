import VerifiedGarbage.Proof.Weierstrass.X86_64.NafLayout
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafPoint
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacAdd

/-! The odd-multiple table retains its initialized prefix and cached double. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

def nafTableSlots (K : WinCfg) (m : Nat) : List Nat :=
  (List.range (3*m)).map fun i => K.tbl+8*K.M.n*i

def nafTableLive (K : WinCfg) (m : Nat) : List Nat :=
  winRo K++jacCoords K.R++jacCoords (Naf.twice K)++nafTableSlots K m

def nafTableClob (K : WinCfg) : List Reg := clob K.M.n++[.rbx]

def nafTableWrites (K : WinCfg) : List (Nat×Nat) :=
  (nafWrites K).map (·,8*K.M.n)++[(K.M.tmp,8*K.M.n)]

structure NafTableInv (K : WinCfg) (C : Curve) (base : Addr) (size : Nat)
    (P : Point C) (s₀ s : State) (m : Nat) : Prop where
  field : Inv K.M base size C.p (·∈nafSlots K) (nafTableLive K m) (tmv C K.M.n base s) s
  point : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y)
    (tmv C K.M.n base s K.R.z) (mul (2*m-1) P)
  twice : InvJ C (tmv C K.M.n base s (Naf.twice K).x) (tmv C K.M.n base s (Naf.twice K).y)
    (tmv C K.M.n base s (Naf.twice K).z) (mul 2 P)
  table : ∀ a,1≤a → a≤m → InvJ C (tmv C K.M.n base s (K.tblPt a).x)
    (tmv C K.M.n base s (K.tblPt a).y) (tmv C K.M.n base s (K.tblPt a).z) (mul (2*a-1) P)
  counter : s.gpr .rbx=BitVec.ofNat 64 m
  keep : KeepRegs (nafTableClob K) s₀ s
  unch : Unch base (nafTableWrites K) s₀.mem s.mem

theorem nafTableLive_read (K : WinCfg) (m : Nat) :
    ∀ x∈rcbR K.S K.R (Naf.twice K),x∈nafTableLive K m := by
  intro x hx
  simp only [nafTableLive,jacCoords,winRo,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

theorem nafTableLive_next (K : WinCfg) (m : Nat) :
    ∀ x∈nafTableLive K (m+1),x∈jacCoords (K.tblPt (m+1))++jacCoords K.R++
      (jacCoords K.D++nafTableLive K m) := by
  intro x hx
  simp only [nafTableLive,List.mem_append] at hx
  rcases hx with ((hx|hx)|hx)|hx
  all_goals try {simp only [List.mem_append,nafTableLive]; grind}
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
  have hi' := List.mem_range.mp hi
  by_cases h : i<3*m
  · have ho : K.tbl+8*K.M.n*i∈nafTableLive K m := List.mem_append_right _
      (List.mem_map.mpr ⟨i,List.mem_range.mpr h,rfl⟩)
    simp only [List.mem_append]; grind
  · have hn' : K.tbl+8*K.M.n*i∈jacCoords (K.tblPt (m+1)) := by
      simp only [jacCoords,tblPt_x,tblPt_y,tblPt_z,Nat.add_sub_cancel,List.mem_cons,
        List.not_mem_nil,or_false]
      obtain rfl|rfl|rfl : i=3*m ∨ i=3*m+1 ∨ i=3*m+2 := by omega
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    simp only [List.mem_append]; grind

theorem nafTable_progUnch {K : WinCfg} {base : Addr} {W : List Nat} {s t : State}
    (hk : ProgKeep K.M base W s t) (hw : ∀ x∈W,x∈nafWrites K) :
    Unch base (nafTableWrites K) s.mem t.mem := by
  apply hk.unch.mono
  intro w hw'
  simp only [nafTableWrites,List.mem_append,List.mem_map,List.mem_singleton] at hw' ⊢
  rcases hw' with ⟨x,hx,rfl⟩|rfl
  · exact Or.inl ⟨x,hw x hx,rfl⟩
  · exact Or.inr rfl

theorem nafTable_advance_ok {s : State} {m : Nat} (hm : m<8)
    (hc : s.gpr .rbx=BitVec.ofNat 64 m) :
    WP isa (.block [.alu .add .rbx (.imm 1),.alu .cmp .rbx (.imm 8)]) s fun t =>
      t.gpr .rbx=BitVec.ofNat 64 (m+1) ∧ t.cf=some (decide (m+1<8)) ∧ Keeps [.rbx] s t := by
  have he : BitVec.ofNat 64 m+(1 : BitVec 32).signExtend 64=BitVec.ofNat 64 (m+1) := by
    change BitVec.ofNat 64 m+BitVec.ofNat 64 1=_
    rw [BitVec.ofNat_add]
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,
    Option.bind_some,RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.cf_arithFlags,
    ite_true,hc,he,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · congr 1
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show m+1<2^64 from by omega)]
    rfl
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_arithFlags,RegUpd.gpr_setReg,hr,ite_false]

end VG.Proof.Weierstrass.X86_64
