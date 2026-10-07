import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigitRead
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafNeg
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeArithmetic

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

local macro "nmem" : tactic => `(tactic| simp only [nafLive,jacWinSlots,winRo,winOther,rcbR,rcbW,
  List.mem_append,List.mem_cons,List.not_mem_nil,or_false,true_or,or_true])

theorem nafEntry_ok {K : WinCfg} {C : Curve} {base : Addr} {size e j : Nat}
    {β : Nat → BitVec 8} (hL : JacWinLay K size) (hJ : K.J=52)
    (hAl : Aligned K.M (·∈jacWinSlots K)) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hTbl : K.tbl<4096) (hBits : K.bits<4096) (hj : j<257)
    (hmag : 1≤nafMagnitude (β j)) (hmag15 : nafMagnitude (β j)≤15)
    (hodd : nafMagnitude (β j)%2=1)
    {P : Point C} {s : State} (h : NafCore K C base size P β e s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) (h2 : s.gpr .x2=(β j).setWidth 64) :
    WP isa (Naf.signedEntry K) s fun t =>
      ProgKeep K.M base (winOther K) s t ∧ NafCore K C base size P β e t ∧
      Inv K.M base size C.p (·∈jacWinSlots K) ([K.E.x,K.E.y,K.E.z]++nafLive K) (tmv C K.M.n base t) t ∧
      InvJ C (tmv C K.M.n base t K.E.x) (tmv C K.M.n base t K.E.y) (tmv C K.M.n base t K.E.z)
        (if nafNegative (β j) then negPt (mul (nafMagnitude (β j)) P) else mul (nafMagnitude (β j)) P) := by
  let a := (nafMagnitude (β j)+1)/2
  have ha : 1≤a := by dsimp [a]; omega
  have ha8 : a≤8 := by dsimp [a]; omega
  have he : 2*a-1=nafMagnitude (β j) := by dsimp [a]; omega
  have hd : ∀ x∈[K.E.x,K.E.y,K.E.z],x∈jacWinSlots K := by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> nmem
  have hw : ∀ x∈[K.E.x,K.E.y,K.E.z],x∈winOther K := by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> nmem
  have hn := hL.nodup
  simp only [winOther,rcbW,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,
    List.not_mem_nil,or_false,not_or] at hn
  have hr : ∀ x∈[K.R.x,K.R.y,K.R.z],x∉[K.E.x,K.E.y,K.E.z] := by
    intro x hx hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx hy
    grind
  have ht : ∀ x∈[(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z],x∈nafLive K := by
    intro x hx
    apply List.mem_append_right
    simp only [Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact List.mem_map.mpr ⟨3*(a-1),List.mem_range.mpr (by omega),by omega⟩
    · exact List.mem_map.mpr ⟨3*(a-1)+1,List.mem_range.mpr (by omega),by omega⟩
    · exact List.mem_map.mpr ⟨3*(a-1)+2,List.mem_range.mpr (by omega),by omega⟩
  have sep : K.E.x+96≤K.tbl+96*(a-1) ∨ K.tbl+96*(a-1)+96≤K.E.x := by
    have hx := hL.tbl K.E.x (by nmem)
    have hy := hL.tbl K.E.y (by nmem)
    have hz := hL.tbl K.E.z (by nmem)
    rw [hL.exy] at hy; rw [hL.exz] at hz
    omega
  rw [Naf.signedEntry]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (nafIndex_ok h2) fun u ⟨u2,ku⟩ => ?_
  have cu := h.of_keeps ku (by decide)
  have kpu : ProgKeep K.M base (winOther K) s u := keeps_prog ku (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [clob])
  refine WP.mono (jacPublicPoint_ok hL.lay hAl hL.n hL.exy hL.exz cu.field u2 ha hTbl hd ht sep
    (cu.stable.table a ha ha8)) fun v ⟨kv,iv,jv⟩ => ?_
  rw [he] at jv
  have cv := cu.of_write hL hJ kv hw hr (iv.sub (fun _ hx => List.mem_append_right _ hx))
  have pv : v.gpr .x19=BitVec.ofNat 64 j := by rw [kv.gpr _ (x19_not_clob _),ku.gpr _ (by decide),h19]
  have kp := kpu.trans (kv.mono hw)
  apply WP.seq
  refine WP.mono (nafSignRead_ok iv.scr hBits (by have := hL.bits; omega) pv (cv.stable.bits j hj))
    fun w ⟨w3,kw⟩ => ?_
  have cw := cv.of_keeps kw (by decide)
  have iw := iv.of_keeps kw (by decide)
  have jw : InvJ C (tmv C K.M.n base v K.E.x) (tmv C K.M.n base v K.E.y)
      (tmv C K.M.n base v K.E.z) (mul (nafMagnitude (β j)) P) := jv
  have tm : tmv C K.M.n base w=tmv C K.M.n base v := by funext x; unfold tmv; rw [kw.mem]
  rw [←tm] at iw jw
  have kpw := keeps_prog (M:=K.M) (base:=base) (W:=winOther K) kw (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp [clob])
  have kp' := kp.trans kpw
  refine WP.ite (nafNegative (β j)) (by
    change some (w.read .x .x3 != 0)=some (nafNegative (β j))
    rw [read_x,w3]; cases nafNegative (β j) <;> decide) (fun hb => ?_) (fun hb => ?_)
  · have hz : tmv C K.M.n base w K.zero=0 := by unfold tmv; rw [cw.stable.zero,toM_zero]
    refine WP.mono (nafNeg_ok hL.lay hAl hm iw (by
      intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> nmem)
      (by grind) (by grind) hz jw) fun t ⟨kt,it,jt⟩ => ?_
    have hyw : ∀ x∈[K.E.y],x∈winOther K := by intro x hx; rw [List.mem_singleton.mp hx]; nmem
    have cr := cw.of_write hL hJ kt hyw (by
      intro x hx hy; simp only [List.mem_singleton] at hy; subst hy
      exact hr _ hx (by simp)) (it.sub (fun _ hx => List.mem_append_right _ hx)).to_tmv
    refine ⟨kp'.trans (kt.mono hyw),cr,it.to_tmv,?_⟩
    rw [hb]; exact it.point_tmv (fun _ hx => List.mem_append_left _ hx) jt
  · apply WP.block_nil
    refine ⟨kp',cw,iw,?_⟩
    rw [hb]; exact jw

end VG.Proof.Weierstrass.AArch64
