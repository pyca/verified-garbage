import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Points
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Jacobian
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindow
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafWindowTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafPrep
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafPrepTiming

/-! ## `JacLayout` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64.Cfg (jacWinCfg)

/-- The sixteen Jacobian entries occupy forty-eight field slots. -/
def jacTblI : List Nat := (List.range 48).map (WT + ·)

theorem jacTblSlots_eq (c : Cfg) (hn : c.n=4) :
    jacTblSlots (jacWinCfg c) = jacTblI.map c.sl := by
  simp only [jacTblSlots,jacTblI,List.map_map]
  apply List.map_congr_left
  intro i _
  change c.sl WT + 32*i = c.sl (WT+i)
  rw [sl_eq4 c (Nat.le_of_eq hn), sl_eq4 c (Nat.le_of_eq hn), hn]
  omega

theorem jacSlots_eq (c : Cfg) (hn : c.n=4) :
    jacWinSlots (jacWinCfg c) = (roI++otherI++jacTblI).map c.sl := by
  rw [jacWinSlots,jacTblSlots_eq c hn,List.map_append,List.map_append]; rfl

theorem jacWrites_eq (c : Cfg) (hn : c.n=4) :
    jacTreeWrites (jacWinCfg c) = slW c (otherI++jacTblI++[TMP]) := by
  rw [jacTreeWrites,jacWinWrites,jacTblSlots_eq c hn]
  simp only [slW,List.map_append,List.map_map]; rfl

theorem jacLay {c : Cfg} (hc : CfgOk c) (hn : c.n=4) : JacWinLay (jacWinCfg c) size := by
  have hSl : Lay c.MP' size (·∈(roI++otherI++jacTblI).map c.sl) := by
    refine ⟨?_,?_,?_,?_⟩
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
      have hb : i<136 := (show ∀ i∈roI++otherI++jacTblI,i<136 by decide) i hi
      change c.sl i + 8*c.n ≤ size
      rw [sl_eq4 c (Nat.le_of_eq hn), hn]; change 64+32*i+32≤8192; omega
    · intro x y hx hy hxy
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hy
      exact sl_apart4 c (Nat.le_of_eq hn) (fun e => hxy (e ▸ rfl))
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
      exact sl_apart4 c (Nat.le_of_eq hn) ((show ∀ i∈roI++otherI++jacTblI,i≠MP by decide) i hi)
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
      exact sl_apart4 c (Nat.le_of_eq hn) ((show ∀ i∈roI++otherI++jacTblI,i≠TMP by decide) i hi)
  refine ⟨hn,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [jacSlots_eq c hn]; exact hSl
  · exact map_sl_disj hc.n0 (l₁:=roI) (l₂:=otherI) (by decide)
  · exact map_sl_nodup hc.n0 (l:=otherI) (by decide)
  · intro x hx
    have hx' : x∈(roI++otherI).map c.sl := by rw [List.map_append]; exact hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx'
    have h := (show ∀ i∈roI++otherI,i<WT by decide) i hi
    change c.sl i+32≤c.sl WT ∨ c.sl WT+1536≤c.sl i
    rw [sl_eq4 c (Nat.le_of_eq hn), sl_eq4 c (Nat.le_of_eq hn), hn]
    simp only [WT] at h ⊢
    omega
  · change c.sl WB+260≤8192
    rw [sl_eq4 c (Nat.le_of_eq hn), hn]; decide
  · intro w hw
    have he : jacWinWrites (jacWinCfg c)=(otherI++jacTblI).map c.sl := by
      rw [jacWinWrites,jacTblSlots_eq c hn,List.map_append]; rfl
    rw [he] at hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    have hb := (show ∀ i∈otherI++jacTblI,i<WB ∨ WT≤i by decide) i hi
    change c.sl WB+260≤c.sl i ∨ c.sl i+32≤c.sl WB
    rw [sl_eq4 c (Nat.le_of_eq hn), sl_eq4 c (Nat.le_of_eq hn), hn]
    simp only [WB,WT] at hb ⊢
    omega
  · change c.sl WB+260≤c.sl TMP ∨ c.sl TMP+32≤c.sl WB
    rw [sl_eq4 c (Nat.le_of_eq hn), sl_eq4 c (Nat.le_of_eq hn), hn]; decide
  · change c.sl TY=c.sl TX+32; rw [sl_eq4 c (Nat.le_of_eq hn), sl_eq4 c (Nat.le_of_eq hn), hn]; rfl
  · change c.sl TZ=c.sl TX+64; rw [sl_eq4 c (Nat.le_of_eq hn), sl_eq4 c (Nat.le_of_eq hn), hn]; rfl
  · change c.sl RY=c.sl RX+32; rw [sl_eq4 c (Nat.le_of_eq hn), sl_eq4 c (Nat.le_of_eq hn), hn]; rfl
  · change c.sl RZ=c.sl RX+64; rw [sl_eq4 c (Nat.le_of_eq hn), sl_eq4 c (Nat.le_of_eq hn), hn]; rfl

theorem jacAligned (c : Cfg) (hn : c.n=4) : Aligned (jacWinCfg c).M (·∈jacWinSlots (jacWinCfg c)) := by
  refine ⟨?_,MP'_A c,fun _ _ h => nomatch (callOf_small (M := c.MP') (Nat.le_of_eq hn)).symm.trans h⟩
  intro x hx
  rw [jacSlots_eq c hn] at hx
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
  exact sl_mod8 c i

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JacWinPrep` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (V)
open VG.Impl.Ecdsa.Verify.AArch64.Cfg (jacWinCfg)
variable {c : Cfg}

theorem jacWinPrep_ok (hc : CfgOk c) (hn4 : c.n=4) (hC : Law c.C) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) {P : Point c.C}
    (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P)
 :
    WP isa (Impl.Ecdsa.Verify.AArch64.Cfg.jacWinPrep c) s fun t =>
      Inv (jacWinCfg c).M base size c.C.p (·∈jacWinSlots (jacWinCfg c))
        (winRo (jacWinCfg c)) (tmv c.C c.n base t) t ∧
      JacWindowInput (jacWinCfg c) c.C base P (sv c base s V+16*Window5.geom 52) t ∧
      (∀ x∈winRo (jacWinCfg c),tmv c.C c.n base t x=tmv c.C c.n base s x) ∧
      t.sp=s.sp ∧ Unch base (winX c) s.mem t.mem ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have hk : wordsVal s.mem base (c.sl V) c.n < 2 ^ (64 * c.n) := wordsVal_lt _ _ _ _
  have hk256 : wordsVal s.mem base (c.sl V) c.n < 2^256 := by simpa only [hn4] using hk
  have hrec := Window5.recode_lt hk256
  have hbound : 32^52 ≤ 2^(64*(c.n+1)) := by
    rw [show (32:Nat)=2^5 from rfl,← Nat.pow_mul]
    apply Nat.pow_le_pow_right
    · decide
    · rw [hn4]; decide
  have hsum := Nat.lt_of_lt_of_le hrec hbound
  have hoff : 16*Window5.geom 52 < 2^(64*(c.n+1)) := by omega
  have hWK : c.sl WK + 16 * c.n ≤ size := by
    have := sl_le' c h7 (i := WK + 1) (by decide)
    simp (disch := decide) only [sl_eq] at this ⊢; rw [Nat.mul_add] at this; omega
  have hKW := sl_lt c (show V < WK by decide)
  have h16 : (16 : Nat) ^ (16 * c.n + 1) ≤ 2 ^ (64 * (c.n + 1)) := by
    rw [show (16 : Nat) = 2 ^ 4 by rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hJ : (winQ c).J = 16 * c.n + 1 := rfl
  have hK : c.winK = c.sl WK := rfl
  have hB : c.winBits = c.sl WB := rfl
  have e69 : c.sl WK + 16 * c.n = c.sl WB := by simp (disch := decide) only [sl_eq]; unfold WK WB; omega
  have hB4 : c.sl WB + 8 ≤ 4096 := by
    simp (disch := decide) only [sl_eq]; unfold WB
    have : 8 * c.n * 55 ≤ 8 * 9 * 55 := Nat.mul_le_mul_right _ (by omega)
    omega
  have hBs : c.sl WB + 64 * (c.n + 1) ≤ c.sl WT := by
    simp (disch := decide) only [sl_eq]; unfold WB WT
    have : 8 * c.n * 87 = 8 * c.n * 55 + 256 * c.n := by omega
    omega
  have hTs := sl_le' c h7 (i := WT) (by decide)
  rw [Impl.Ecdsa.Verify.AArch64.Cfg.jacWinPrep]
  rw [← hn4, show (40:Nat)=8*(c.n+1) by omega,
    show Impl.Ecdsa.Verify.AArch64.Cfg.jacOffset=16*Window5.geom 52 from Window5.offset_eq.symm]
  refine WP.seq ?_
  rw [hK]
  refine WP.mono (addConst_ok hs (n := c.n) (src := c.sl V) (dst := c.sl WK)
    (c := 16*Window5.geom 52) h0 h7 (sl_le c h7 (show V<45 by decide)) (by omega) (sl_mod8 c _) (sl_mod8 c _)
    (Or.inl (by omega)) hoff hsum) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (x0_not_clob _)
  rw [hB]
  refine WP.mono (bits_ok hs₁ (n := c.n + 1) (src := c.sl WK) (dst := c.sl WB) (by omega) (by omega)
    (by omega) (by omega) (by omega) hB4 (Or.inl (by omega))) fun s₂ ⟨b₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [e₁] at b₂
  have U₂ : Unch base (winX c) s.mem s₂.mem :=
    ((O₁.mono (o' := c.sl WK) (n' := 16 * c.n) (Nat.le_refl _) (by omega)).unch.trans
      ((O₂.mono (o' := c.sl WB) (n' := 64 * (c.n + 1)) (Nat.le_refl _) (by omega)).unch)).mono
      (by intro w hw; simpa [winX, hK, hB] using hw)
  have F₂ := F.unch h7 hn fixedOk_winX U₂
  have e₂ : ∀ {i}, i < 45 → sv c base s₂ i = sv c base s i := fun hi =>
    sv_unch U₂ h7 hn hi (apart_winX4 (Nat.le_of_eq hn4) hi)
  have hM₂ := modP_of hc F₂.mp
  have tv : ∀ {i}, i < 45 → tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl i) := fun hi => by
    show toM _ _ (sv c base s₂ _) = toM _ _ (sv c base s _); rw [e₂ hi]
  have hlt : ∀ x∈winRo (jacWinCfg c),wordsVal s₂.mem base x c.n<c.C.p := by
    intro x hx
    simp only [winRo,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F₂.ap (hmont _)
    · exact lt_of_eq_of_lt F₂.bm (hmont _)
    · exact lt_of_eq_of_lt F₂.zero (by omega)
    · exact lt_of_eq_of_lt (e₂ (i:=PX) (by decide)) hpx
    · exact lt_of_eq_of_lt (e₂ (i:=PY) (by decide)) hpy
    · exact lt_of_eq_of_lt F₂.onep (Nat.mod_lt _ (by omega))
  have hI : Inv (jacWinCfg c).M base size c.C.p (·∈jacWinSlots (jacWinCfg c))
      (winRo (jacWinCfg c)) (tmv c.C c.n base s₂) s₂ :=
    ⟨hs₂,hM₂,fun _ hx => List.mem_append_left _ (List.mem_append_left _ hx),hlt,fun _ _ => rfl⟩
  have one : tmv c.C c.n base s₂ (c.sl ONEP)=1 := by
    change toM _ _ (wordsVal s₂.mem base (c.sl ONEP) c.n)=1
    rw [F₂.onep]
    have hm1 := toM_cmont hc.toBaseCfgOk 1
    have ho : Fin.ofNat c.C.p 1 = (1:Fe c.C) := by rfl
    simpa only [Cfg.mont,Cfg.R,Nat.one_mul,ho] using hm1
  have hp : Rep c.C (tmv c.C c.n base s₂ (c.sl PX)) (tmv c.C c.n base s₂ (c.sl PY))
      (tmv c.C c.n base s₂ (c.sl ONEP)) P := by
    rw [tv (by decide),tv (by decide),tv (by decide)]; exact hrep
  have hj : InvJ c.C (tmv c.C c.n base s₂ (c.sl PX)) (tmv c.C c.n base s₂ (c.sl PY))
      (tmv c.C c.n base s₂ (c.sl ONEP)) P := by
    have hh := InvJ.of_rep hC hp
    simpa only [one,Lean.Grind.Semiring.mul_one] using hh
  refine ⟨hI,⟨F₂.zero,fun i hi => b₂ i (by rw [hn4]; omega),hj⟩,?_,k₂.sp.trans k₁.sp,U₂,k₂.rd.trans k₁.rd,k₂.wr.trans k₁.wr⟩
  intro x hx
  simp only [winRo,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [tv (i := AP) (by decide), tv (i := BM) (by decide), tv (i := ZERO) (by decide),
    tv (i := PX) (by decide), tv (i := PY) (by decide), tv (i := ONEP) (by decide)]

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JacWindow` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (V)
open VG.Impl.Ecdsa.Verify.AArch64.Cfg (jacWinCfg)
variable {c : Cfg}

structure JacWinMulPost (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  rd : s'.rd=s.rd
  wr : s'.wr=s.wr
  unch : Unch base (winX c ++ slW c (otherI++jacTblI++[TMP])) s.mem s'.mem
  mod : ModOkA c.MP' size c.C.p s'.mem base
  lt : ∀ x∈[c.sl RX,c.sl RY,c.sl RZ],wordsVal s'.mem base x c.n<c.C.p
  q : Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
    (tmv c.C c.n base s' (c.sl RZ)) (mul k P)

theorem jacWinMul_ok (hc : CfgOk c) (hn4 : c.n=4) (hC : Law c.C) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) {P : Point c.C} (hP : onCurve c.C P = true)
    (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P)
    {rest : Prog isa} {R : State → Prop}
    (h : ∀ s', JacWinMulPost c base P (sv c base s V) s s' → WP isa rest s' R) :
    WP isa (.seq (Impl.Ecdsa.Verify.AArch64.Cfg.jacWinPrep c) (.seq (Jacobian.jacWindow (jacWinCfg c) 5) rest)) s R := by
  have hmont : ∀ x,c.mont x<c.C.p := fun x => Nat.mod_lt _ (by have := hc.p_ge; omega)
  have hk : sv c base s V<2^256 := by
    simpa only [sv,hn4] using wordsVal_lt s.mem base (c.sl V) c.n
  have hrec := Window5.recode_lt hk
  apply WP.seq
  refine WP.mono (jacWinPrep_ok hc hn4 hC hs F hpx hpy hrep)
    fun s₂ ⟨hI,⟨hz,hb,hj⟩,_,_,U₂,rd₂,wr₂⟩ => ?_
  refine WP.seq (WP.mono (jacWindow_ok (jacLay hc hn4) rfl (jacAligned c hn4)
    (unitMod_pow_two hc.p_odd (64*c.n)) hC hc.am3
    (by change c.sl WT<4096; simp (disch := decide) only [sl_eq]; rw [hn4]; decide)
    (by change c.sl WB+5≤4096; simp (disch := decide) only [sl_eq]; rw [hn4]; decide) (hmont 1)
    (toM_cmont hc 1) (Nat.le_add_left _ _) hrec hP hI hz hb hj)
    fun s₃ ⟨K₃,U₃,M₃,L₃,R₃⟩ => h s₃ ?_)
  rw [jacWrites_eq c hn4] at U₃
  rw [Nat.add_sub_cancel] at R₃
  have nx0 : Reg.x0 ∉ jacWindowClob (jacWinCfg c) := by
    simp only [jacWindowClob,tcombClob]
    rw [show (jacWinCfg c).M.n=4 from hn4]
    decide
  exact ⟨hI.scr.of_keepRegs K₃ nx0,K₃.rd.trans rd₂,K₃.wr.trans wr₂,U₂.trans U₃,M₃,L₃,R₃⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `NafWinPrep` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (V)
open VG.Impl.Ecdsa.Verify.AArch64.Cfg (jacWinCfg)
variable {c : Cfg}

theorem nafWinPrep_ok (hc : CfgOk c) (hn4 : c.n=4) (hC : Law c.C) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) {P : Point c.C}
    (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P)
 :
    WP isa (Impl.Ecdsa.Verify.AArch64.Cfg.nafWinPrep c) s fun t =>
      Inv (jacWinCfg c).M base size c.C.p (·∈jacWinSlots (jacWinCfg c))
        (winRo (jacWinCfg c)) (tmv c.C c.n base t) t ∧
      NafWindowInput (jacWinCfg c) c.C base P (sv c base s V) t ∧
      (∀ x∈winRo (jacWinCfg c),tmv c.C c.n base t x=tmv c.C c.n base s x) ∧
      t.sp=s.sp ∧ Unch base (winX c) s.mem t.mem ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have hB : (jacWinCfg c).bits = c.sl WB := rfl
  rw [Impl.Ecdsa.Verify.AArch64.Cfg.nafWinPrep]
  refine WP.mono (nafPrep_ok (jacWinCfg c) hs
    (by simpa only [hn4] using sl_le c h7 (i:=V) (by decide)) (sl_mod8 c _)
    (by rw [hB]; simp (disch := decide) only [sl_eq]; rw [hn4]; decide)
    (by rw [hB]; simp (disch := decide) only [sl_eq]; rw [hn4]; decide)) fun s₂ ⟨p₂,k₂,O₂⟩ => ?_
  have hs₂ := p₂.scr
  have b₂ := p₂.digits
  rw [←hn4] at b₂
  have U₂ : Unch base (winX c) s.mem s₂.mem := by
    have u := (O₂.mono (o':=c.sl WB) (n':=64*(c.n+1)) (by rw [hB]) (by rw [hB,hn4]; omega)).unch
    exact u.mono (by intro w hw; simp only [List.mem_singleton] at hw; subst hw; change _ ∈ [(c.winK,16*c.n),(c.winBits,64*(c.n+1))]; exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))
  have F₂ := F.unch h7 hn fixedOk_winX U₂
  have e₂ : ∀ {i}, i < 45 → sv c base s₂ i = sv c base s i := fun hi =>
    sv_unch U₂ h7 hn hi (apart_winX4 (Nat.le_of_eq hn4) hi)
  have hM₂ := modP_of hc F₂.mp
  have tv : ∀ {i}, i < 45 → tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl i) := fun hi => by
    show toM _ _ (sv c base s₂ _) = toM _ _ (sv c base s _); rw [e₂ hi]
  have hlt : ∀ x∈winRo (jacWinCfg c),wordsVal s₂.mem base x c.n<c.C.p := by
    intro x hx
    simp only [winRo,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F₂.ap (hmont _)
    · exact lt_of_eq_of_lt F₂.bm (hmont _)
    · exact lt_of_eq_of_lt F₂.zero (by omega)
    · exact lt_of_eq_of_lt (e₂ (i:=PX) (by decide)) hpx
    · exact lt_of_eq_of_lt (e₂ (i:=PY) (by decide)) hpy
    · exact lt_of_eq_of_lt F₂.onep (Nat.mod_lt _ (by omega))
  have hI : Inv (jacWinCfg c).M base size c.C.p (·∈jacWinSlots (jacWinCfg c))
      (winRo (jacWinCfg c)) (tmv c.C c.n base s₂) s₂ :=
    ⟨hs₂,hM₂,fun _ hx => List.mem_append_left _ (List.mem_append_left _ hx),hlt,fun _ _ => rfl⟩
  have one : tmv c.C c.n base s₂ (c.sl ONEP)=1 := by
    change toM _ _ (wordsVal s₂.mem base (c.sl ONEP) c.n)=1
    rw [F₂.onep]
    have hm1 := toM_cmont hc.toBaseCfgOk 1
    have ho : Fin.ofNat c.C.p 1 = (1:Fe c.C) := by rfl
    simpa only [Cfg.mont,Cfg.R,Nat.one_mul,ho] using hm1
  have hp : Rep c.C (tmv c.C c.n base s₂ (c.sl PX)) (tmv c.C c.n base s₂ (c.sl PY))
      (tmv c.C c.n base s₂ (c.sl ONEP)) P := by
    rw [tv (by decide),tv (by decide),tv (by decide)]; exact hrep
  have hj : InvJ c.C (tmv c.C c.n base s₂ (c.sl PX)) (tmv c.C c.n base s₂ (c.sl PY))
      (tmv c.C c.n base s₂ (c.sl ONEP)) P := by
    have hh := InvJ.of_rep hC hp
    simpa only [one,Lean.Grind.Semiring.mul_one] using hh
  refine ⟨hI,⟨F₂.zero,fun i hi => b₂ i hi,hj⟩,?_,k₂.sp,U₂,k₂.rd,k₂.wr⟩
  intro x hx
  simp only [winRo,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [tv (i := AP) (by decide), tv (i := BM) (by decide), tv (i := ZERO) (by decide),
    tv (i := PX) (by decide), tv (i := PY) (by decide), tv (i := ONEP) (by decide)]

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `NafWindow` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (V)
open VG.Impl.Ecdsa.Verify.AArch64.Cfg (jacWinCfg)
variable {c : Cfg}

theorem nafWinMul_ok (hc : CfgOk c) (hn4 : c.n=4) (hC : Law c.C) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) {P : Point c.C} (hP : onCurve c.C P = true)
    (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P)
    {rest : Prog isa} {R : State → Prop}
    (h : ∀ s', JacWinMulPost c base P (sv c base s V) s s' → WP isa rest s' R) :
    WP isa (.seq (Impl.Ecdsa.Verify.AArch64.Cfg.nafWinPrep c) (.seq (Naf.window (jacWinCfg c)) rest)) s R := by
  have hmont : ∀ x,c.mont x<c.C.p := fun x => Nat.mod_lt _ (by have := hc.p_ge; omega)
  have hk : sv c base s V<2^256 := by
    simpa only [sv,hn4] using wordsVal_lt s.mem base (c.sl V) c.n
  apply WP.seq
  refine WP.mono (nafWinPrep_ok hc hn4 hC hs F hpx hpy hrep)
    fun s₂ ⟨hI,⟨hz,hb,hj⟩,_,_,U₂,rd₂,wr₂⟩ => ?_
  refine WP.seq (WP.mono (nafWindow_ok (jacLay hc hn4) rfl (jacAligned c hn4)
    (unitMod_pow_two hc.p_odd (64*c.n)) hC hc.am3
    (by change c.sl WT<4096; simp (disch := decide) only [sl_eq]; rw [hn4]; decide)
    (by change c.sl WB+5≤4096; simp (disch := decide) only [sl_eq]; rw [hn4]; decide) (hmont 1)
    (toM_cmont hc 1) hk hP hI hz hb hj)
    fun s₃ ⟨K₃,U₃,M₃,L₃,R₃⟩ => h s₃ ?_)
  rw [jacWrites_eq c hn4] at U₃
  have nx0 : Reg.x0 ∉ jacWindowClob (jacWinCfg c) := by
    simp only [jacWindowClob,tcombClob]
    rw [show (jacWinCfg c).M.n=4 from hn4]
    decide
  exact ⟨hI.scr.of_keepRegs K₃ nx0,K₃.rd.trans rd₂,K₃.wr.trans wr₂,U₂.trans U₃,M₃,L₃,R₃⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JacWindowTiming` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (V)
open VG.Impl.Ecdsa.Verify.AArch64.Cfg (jacWinCfg jacWinPrep)

structure JacWinState (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s : State) : Prop where
  scr : Scr s base size
  fixed : ∃ g, Fixed c base g s.mem
  px : sv c base s PX<c.C.p
  py : sv c base s PY<c.C.p
  rep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
    (tmv c.C c.n base s (c.sl ONEP)) P
  scalar : sv c base s V=k

structure JacWinPublic (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s t : State) : Prop where
  left : JacWinState c base P k s
  right : JacWinState c base P k t
  sp : s.sp=t.sp
  px : tmv c.C c.n base s (c.sl PX)=tmv c.C c.n base t (c.sl PX)
  py : tmv c.C c.n base s (c.sl PY)=tmv c.C c.n base t (c.sl PY)

theorem JacWinPublic.fields {c : Cfg} {base : Addr} {P : Point c.C} {k : Nat} {s t : State}
    (h : JacWinPublic c base P k s t) :
    ∀ x∈winRo (jacWinCfg c),tmv c.C c.n base s x=tmv c.C c.n base t x := by
  obtain ⟨_,fs⟩ := h.left.fixed
  obtain ⟨_,ft⟩ := h.right.fixed
  intro x hx
  simp only [winRo,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · change toM _ _ (wordsVal s.mem base (c.sl AP) c.n)=toM _ _ (wordsVal t.mem base (c.sl AP) c.n)
    rw [fs.ap,ft.ap]
  · change toM _ _ (wordsVal s.mem base (c.sl BM) c.n)=toM _ _ (wordsVal t.mem base (c.sl BM) c.n)
    rw [fs.bm,ft.bm]
  · change toM _ _ (wordsVal s.mem base (c.sl ZERO) c.n)=toM _ _ (wordsVal t.mem base (c.sl ZERO) c.n)
    rw [fs.zero,ft.zero]
  · exact h.px
  · exact h.py
  · change toM _ _ (wordsVal s.mem base (c.sl ONEP) c.n)=toM _ _ (wordsVal t.mem base (c.sl ONEP) c.n)
    rw [fs.onep,ft.onep]

/-- The signature-derived scalar preparation and variable-point window use
only common public scalar bits and public point coordinates. -/
theorem jacWinMul_relCT {c : Cfg} (hc : CfgOk c) (hn4 : c.n=4) (hC : Law c.C)
    (hprep : FieldCT (jacWinPrep c)) (hchecks : JacWindowChecks (jacWinCfg c))
    {base : Addr} {P : Point c.C} {k : Nat} (hP : onCurve c.C P=true) :
    RelCT isa (JacWinPublic c base P k)
      (.seq (jacWinPrep c) (Jacobian.jacWindow (jacWinCfg c) 5))
      (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  intro s t ts tt s' t' hp es et
  obtain ⟨_,fs⟩ := hp.left.fixed
  obtain ⟨_,ft⟩ := hp.right.fixed
  cases es with | seq ps ws =>
    cases et with | seq pt wt =>
      obtain ⟨_,_,xs,is,bs,vs,ks,_,_,_⟩ := jacWinPrep_ok hc hn4 hC hp.left.scr fs hp.left.px hp.left.py hp.left.rep
      obtain ⟨_,_,xt,it,bt,vt,kt,_,_,_⟩ := jacWinPrep_ok hc hn4 hC hp.right.scr ft hp.right.px hp.right.py hp.right.rep
      obtain ⟨_,rfl⟩ := Exec.det ps xs
      obtain ⟨_,rfl⟩ := Exec.det pt xt
      have he := hprep _ _ _ _ _ _ trivial trivial ⟨hp.sp,fun r hr => by
        simp only [Taint.mem_ofRegs,List.mem_singleton] at hr
        subst hr
        exact hp.left.scr.x0.trans hp.right.scr.x0.symm⟩ ps pt
      have pair : FieldPair (jacWinCfg c).M base size c.C.p (·∈jacWinSlots (jacWinCfg c))
          (winRo (jacWinCfg c)) _ _ _ :=
        ⟨is,it.congr_env (fun x hx => (vt x hx).trans ((hp.fields x hx).symm.trans (vs x hx).symm)),
          ks.trans (hp.sp.trans kt.symm)⟩
      rw [hp.left.scalar] at bs
      rw [hp.right.scalar] at bt
      have hk : k<2^256 := by
        rw [←hp.left.scalar]
        simpa only [sv,hn4] using wordsVal_lt s.mem base (c.sl V) c.n
      have hrec := Window5.recode_lt hk
      have hmont : ∀ x,c.mont x<c.C.p := fun x => Nat.mod_lt _ (by have := hc.p_ge; omega)
      obtain ⟨hw,_,post⟩ := jacWindow_relCT (jacLay hc hn4) rfl (jacAligned c hn4)
        (unitMod_pow_two hc.p_odd (64*c.n)) hC hc.am3
        (by change c.sl WT<4096; simp (disch := decide) only [sl_eq]; rw [hn4]; decide)
        (by change c.sl WB+5≤4096; simp (disch := decide) only [sl_eq]; rw [hn4]; decide) (hmont 1)
        (toM_cmont hc 1) (Nat.le_add_left _ _) hrec hchecks hP
        _ _ _ _ _ _ ⟨pair,bs,bt⟩ ws wt
      exact ⟨by rw [he,hw],post.public⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `NafWindowTiming` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (V)
open VG.Impl.Ecdsa.Verify.AArch64.Cfg (jacWinCfg nafWinPrep)

theorem nafWinPrep_relCT {c : Cfg} (hc : CfgOk c) (hn4 : c.n=4)
    (checks : NafPrepChecks (jacWinCfg c) (c.sl V)) {base : Addr} {P : Point c.C} {k : Nat} :
    RelCT isa (JacWinPublic c base P k) (nafWinPrep c) (fun _ _ => True) := by
  have h := nafPrep_relCT (jacWinCfg c) (base:=base)
    (by simpa only [hn4] using sl_le c hc.n10 (i:=V) (by decide)) (sl_mod8 c _)
    (by change c.sl WB<4096; simp (disch := decide) only [sl_eq]; rw [hn4]; decide)
    (by change c.sl WB+257≤size; simp (disch := decide) only [sl_eq]; rw [hn4]; decide) checks
  exact h.mono (fun _ _ hp => ⟨hp.left.scr,hp.right.scr,hp.sp,by
    rw [←hn4]; exact hp.left.scalar.trans hp.right.scalar.symm⟩) (fun _ _ h => h)

/-- The signature-derived scalar preparation and variable-point window use
only common public scalar bits and public point coordinates. -/
theorem nafWinMul_relCT {c : Cfg} (hc : CfgOk c) (hn4 : c.n=4) (hC : Law c.C)
    (hchecks : NafWindowChecks (jacWinCfg c))
    {base : Addr} {P : Point c.C} {k : Nat} (hP : onCurve c.C P=true)
    (hprep : RelCT isa (JacWinPublic c base P k) (nafWinPrep c) (fun _ _ => True)) :
    RelCT isa (JacWinPublic c base P k)
      (.seq (nafWinPrep c) (Naf.window (jacWinCfg c)))
      (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  intro s t ts tt s' t' hp es et
  obtain ⟨_,fs⟩ := hp.left.fixed
  obtain ⟨_,ft⟩ := hp.right.fixed
  cases es with | seq ps ws =>
    cases et with | seq pt wt =>
      obtain ⟨_,_,xs,is,bs,vs,ks,_,_,_⟩ := nafWinPrep_ok hc hn4 hC hp.left.scr fs hp.left.px hp.left.py hp.left.rep
      obtain ⟨_,_,xt,it,bt,vt,kt,_,_,_⟩ := nafWinPrep_ok hc hn4 hC hp.right.scr ft hp.right.px hp.right.py hp.right.rep
      obtain ⟨_,rfl⟩ := Exec.det ps xs
      obtain ⟨_,rfl⟩ := Exec.det pt xt
      have he := (hprep _ _ _ _ _ _ hp ps pt).1
      have pair : FieldPair (jacWinCfg c).M base size c.C.p (·∈jacWinSlots (jacWinCfg c))
          (winRo (jacWinCfg c)) _ _ _ :=
        ⟨is,it.congr_env (fun x hx => (vt x hx).trans ((hp.fields x hx).symm.trans (vs x hx).symm)),
          ks.trans (hp.sp.trans kt.symm)⟩
      rw [hp.left.scalar] at bs
      rw [hp.right.scalar] at bt
      have hk : k<2^256 := by
        rw [←hp.left.scalar]
        simpa only [sv,hn4] using wordsVal_lt s.mem base (c.sl V) c.n
      have hmont : ∀ x,c.mont x<c.C.p := fun x => Nat.mod_lt _ (by have := hc.p_ge; omega)
      obtain ⟨hw,_,post⟩ := nafWindow_relCT (jacLay hc hn4) rfl (jacAligned c hn4)
        (unitMod_pow_two hc.p_odd (64*c.n)) hC hc.am3
        (by change c.sl WT<4096; simp (disch := decide) only [sl_eq]; rw [hn4]; decide)
        (by change c.sl WB+5≤4096; simp (disch := decide) only [sl_eq]; rw [hn4]; decide) (hmont 1)
        (toM_cmont hc 1) hk hchecks hP
        _ _ _ _ _ _ ⟨pair,bs,bt⟩ ws wt
      exact ⟨by rw [he,hw],post.public⟩

end VG.Proof.Ecdsa.Verify.AArch64

end
