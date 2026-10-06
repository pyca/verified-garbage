import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowInvariant

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

def jacTreeSlots (K : WinCfg) (m : Nat) : List Nat :=
  (List.range (3*m)).map fun i => K.tbl+32*i

def jacTreeLive (K : WinCfg) (m : Nat) : List Nat :=
  winRo K ++ [K.R.x,K.R.y,K.R.z] ++
  (if 2≤m then [K.E.x,K.E.y,K.E.z,K.D.x,K.D.y,K.D.z] else []) ++ jacTreeSlots K m

def jacTreeClob (K : WinCfg) : List Reg := clob K.M.n ++ [.x19,.x20]

def jacTreeWrites (K : WinCfg) : List (Nat × Nat) :=
  (jacWinWrites K).map (·,8*K.M.n) ++ [(K.M.tmp,8*K.M.n)]

/-- At entry m, the first m multiples are stored and R holds the last one.
E and D become initialized after the first arithmetic iteration. -/
structure JacTreeInv (K : WinCfg) (C : Curve) (base : Addr) (size : Nat)
    (P : Point C) (s₀ s : State) (m : Nat) : Prop where
  field : Inv K.M base size C.p (· ∈ jacWinSlots K) (jacTreeLive K m) (tmv C K.M.n base s) s
  point : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y)
    (tmv C K.M.n base s K.R.z) (mul m P)
  source : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
    (tmv C K.M.n base s K.P.z) P
  table : ∀ a, 1≤a → a≤m → InvJ C (tmv C K.M.n base s (Jacobian.tablePt K a).x)
    (tmv C K.M.n base s (Jacobian.tablePt K a).y)
    (tmv C K.M.n base s (Jacobian.tablePt K a).z) (mul a P)
  counter : s.gpr .x19 = BitVec.ofNat 64 (16-m)
  pointer : s.gpr .x20 = off base (K.tbl+96*m)
  keep : KeepRegs (jacTreeClob K) s₀ s
  unch : Unch base (jacTreeWrites K) s₀.mem s.mem

 theorem jacTreeLive_read (K : WinCfg) (m : Nat) :
    ∀ x ∈ rcbR K.S K.R K.P, x ∈ jacTreeLive K m := by
  intro x hx
  simp only [jacTreeLive,winRo,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

 theorem jacTreeLive_ED (K : WinCfg) {m : Nat} (hm : 2≤m) :
    ∀ x ∈ [K.E.x,K.E.y,K.E.z,K.D.x,K.D.y,K.D.z], x ∈ jacTreeLive K m := by
  intro x hx
  simp only [jacTreeLive,hm,↓reduceIte,List.mem_append]
  exact Or.inl (Or.inr hx)

 theorem jacTreeLive_table (K : WinCfg) {a m : Nat} (ha : 1≤a) (ham : a≤m) :
    ∀ x ∈ [(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z],
      x ∈ jacTreeLive K m := by
  intro x hx
  apply List.mem_append_right
  simp only [Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact List.mem_map.mpr ⟨3*(a-1),List.mem_range.mpr (by omega),by omega⟩
  · exact List.mem_map.mpr ⟨3*(a-1)+1,List.mem_range.mpr (by omega),by omega⟩
  · exact List.mem_map.mpr ⟨3*(a-1)+2,List.mem_range.mpr (by omega),by omega⟩

 theorem jacTreeLive_full (K : WinCfg) : jacTreeLive K 16 = jacLive K := by
  simp only [jacTreeLive,jacTreeSlots,jacLive,jacTblSlots,show 2≤16 by decide,↓reduceIte]
  simp only [List.append_assoc,List.cons_append,List.nil_append]

end VG.Proof.Weierstrass.AArch64
