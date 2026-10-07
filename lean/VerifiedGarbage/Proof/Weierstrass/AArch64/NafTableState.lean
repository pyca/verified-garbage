import VerifiedGarbage.Proof.Weierstrass.AArch64.NafInvariant
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTree

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

def nafTableLive (K : WinCfg) (m : Nat) : List Nat :=
  winRo K ++ jacCoords K.R ++ jacCoords K.D ++ jacCoords (Naf.twice K) ++ jacTreeSlots K m

structure NafTableInv (K : WinCfg) (C : Curve) (base : Addr) (size : Nat)
    (P : Point C) (s₀ s : State) (m : Nat) : Prop where
  field : Inv K.M base size C.p (·∈jacWinSlots K) (nafTableLive K m) (tmv C K.M.n base s) s
  point : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y)
    (tmv C K.M.n base s K.R.z) (mul (2*m-1) P)
  twice : InvJ C (tmv C K.M.n base s (Naf.twice K).x) (tmv C K.M.n base s (Naf.twice K).y)
    (tmv C K.M.n base s (Naf.twice K).z) (mul 2 P)
  table : ∀ a, 1≤a → a≤m → InvJ C (tmv C K.M.n base s (Jacobian.tablePt K a).x)
    (tmv C K.M.n base s (Jacobian.tablePt K a).y)
    (tmv C K.M.n base s (Jacobian.tablePt K a).z) (mul (2*a-1) P)
  counter : s.gpr .x19=BitVec.ofNat 64 (8-m)
  pointer : s.gpr .x20=off base (K.tbl+96*m)
  keep : KeepRegs (jacTreeClob K) s₀ s
  unch : Unch base (jacTreeWrites K) s₀.mem s.mem

theorem nafTableLive_read (K : WinCfg) (m : Nat) :
    ∀ x∈rcbR K.S K.R (Naf.twice K), x∈nafTableLive K m := by
  intro x hx
  simp only [nafTableLive,jacCoords,winRo,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

theorem nafTableLive_next (K : WinCfg) {m : Nat} (hm : 1≤m) :
    ∀ x∈nafTableLive K (m+1), x∈jacCoords (Jacobian.tablePt K (m+1)) ++ jacCoords K.R ++
      (jacCoords K.D++nafTableLive K m) := by
  intro x hx
  simp only [nafTableLive,List.mem_append] at hx
  rcases hx with (((hx | hx) | hx) | hx) | hx
  all_goals try {simp only [List.mem_append,nafTableLive]; grind}
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
  have hi' := List.mem_range.mp hi
  by_cases h : i<3*m
  · have ho : K.tbl+32*i∈nafTableLive K m := List.mem_append_right _
      (List.mem_map.mpr ⟨i,List.mem_range.mpr h,rfl⟩)
    simp only [List.mem_append]; grind
  · have hn : K.tbl+32*i∈jacCoords (Jacobian.tablePt K (m+1)) := by
      simp only [jacCoords,Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false]
      omega
    simp only [List.mem_append]; grind

theorem JacWinLay.rcbApart_twice {K : WinCfg} {size : Nat} (hL : JacWinLay K size) (hJ : K.J=52) :
    RcbApart K.S K.R (Naf.twice K) K.D := by
  have h := (hL.toWinLay hJ).rcbApart_D (Or.inl rfl)
  refine ⟨h.nodup,fun x hx hw => ?_⟩
  have he : x∈rcbR K.S K.R K.R ∨ x∈jacCoords (Naf.twice K) := by
    simp only [rcbR,jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  rcases he with he | he
  · exact h.apart x he hw
  · have sep := hL.tbl x (List.mem_append_right _ (List.mem_append_right _ hw))
    simp only [jacCoords,Naf.twice,Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at he
    omega

theorem nafAdvance_ok {K : WinCfg} {s : State} {base : Addr} {m : Nat}
    (h19 : s.gpr .x19=BitVec.ofNat 64 (8-m))
    (h20 : s.gpr .x20=off base (K.tbl+96*m)) (hm : m≤7) :
    WP isa (.block [.addImm .x .x20 .x20 96,decCounter]) s fun t =>
      t.gpr .x19=BitVec.ofNat 64 (8-(m+1)) ∧
      t.gpr .x20=off base (K.tbl+96*(m+1)) ∧ Keeps [.x19,.x20] s t := by
  apply WP.of_runBlock
  simp only [decCounter,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    show (96:Nat)<4096 by decide,show (1:Nat)<4096 by decide,ite_true,RegUpd.gpr_write,
    BitVec.setWidth_eq,Size.bits,reduceCtorEq,ite_false,h19,h20,Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · rw [BitVec.ofNat_sub_ofNat_of_le (8-m) 1 (by decide) (by omega)]
    congr 1
  · simp only [off,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc,Nat.mul_one]
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

end VG.Proof.Weierstrass.AArch64
