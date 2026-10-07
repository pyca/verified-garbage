import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindow
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafFinish
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTable

/-! The full public Jacobian variable-point multiplication. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps)

/-- Reset the accumulator and set the 256-iteration public loop counter. -/
theorem nafReset_ok {K : WinCfg} {C : Curve} {base : Addr} {size e : Nat} {β : Nat → BitVec 8}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hOne : K.one<C.p) {P : Point C} {s : State} (h : NafCore K C base size P β e s) :
    WP isa (.block (Jacobian.infinity K K.R ++ ([.movz .x .x19 256 0] : List Instr))) s fun t =>
      JacLoopKeep K base s t ∧ NafCore K C base size P β 0 t ∧ t.gpr .x19=256 := by
  rw [WP.block_append_iff]
  have sl : ∀ x ∈ [K.R.x,K.R.y,K.R.z], x ∈ jacWinSlots K := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [jacWinSlots,winOther]
  refine WP.mono (infinityPoint_ok hL.lay hAl sl h.field hOne) fun a ⟨E,ka,ia,ja⟩ => ?_
  have kp : ProgKeep K.M base (winOther K) s a := ka.mono (by
    intro x hx
    simp only [rcbW,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind)
  have i' := ia.sub (fun x (hx : x ∈ nafLive K) => List.mem_append_right _ hx)
  have j' : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) (mul 0 P) := by
    have he : mul 0 P=Point.infinity := by rw [Spec.Weierstrass.mul]; simp
    rw [he]; exact ja
  have ca := h.next hL hJ kp i' j'
  refine WP.mono (setCounter_ok a (j := 256) (by decide)) fun t ⟨t19,kt⟩ =>
    ⟨?_,ca.of_keeps kt (by decide),t19⟩
  refine ⟨((⟨kp.gpr,kp.rd,kp.wr,kp.sp⟩ : KeepRegs (clob K.M.n) s a).mono
    (fun _ hr => List.mem_cons_of_mem _ hr)).trans ((Keeps.regs kt).mono (by simp)),?_⟩
  simpa only [kt.mem,jacLoopWrites] using kp.unch



/-- Scalar multiplication with the sparse signed five-bit table, 256 Jacobian
iterations, and one canonical homogeneous conversion. -/
theorem nafWindow_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    (hTbl : K.tbl<4096) (hBits : K.bits+5≤4096) (hOne : K.one<C.p)
    (hone : toM C.p (2^(64*K.M.n)) K.one=1)
    (hk : k<2^256)
    {P : Point C} (hP : onCurve C P=true) {s : State}
    (hI : Inv K.M base size C.p (·∈jacWinSlots K) (winRo K) (tmv C K.M.n base s) s)
    (hz : wordsVal s.mem base K.zero K.M.n=0)
    (hb : ∀ i<257, s.mem (off base (K.bits+i))=Naf5.byte k i)
    (hJP : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
      (tmv C K.M.n base s K.P.z) P) :
    WP isa (Naf.window K) s fun t =>
      KeepRegs (jacWindowClob K) s t ∧ Unch base (jacTreeWrites K) s.mem t.mem ∧
      ModOkA K.M size C.p t.mem base ∧
      (∀ x ∈ [K.R.x,K.R.y,K.R.z], wordsVal t.mem base x K.M.n<C.p) ∧
      Rep C (tmv C K.M.n base t K.R.x) (tmv C K.M.n base t K.R.y)
        (tmv C K.M.n base t K.R.z) (mul k P) := by
  rw [Naf.window]
  apply WP.seq
  refine WP.mono (nafTable_ok hL hJ hAl hm hC ha hTbl hOne hP hI hJP) fun a ta => ?_
  obtain ⟨ia,sa⟩ := ta.ready hL hz hb
  have ca : NafCore K C base size P (Naf5.byte k) 15 a := ⟨ia,sa,ta.point⟩
  apply WP.seq
  refine WP.mono (nafReset_ok hL hJ hAl hOne ca) fun b ⟨kb,cb,b19⟩ => ?_
  apply WP.assoc
  apply WP.seq
  refine WP.mono (nafRun_ok hL hJ hAl hm hC ha hOne hTbl (by omega) hk hP cb b19)
    fun c ⟨kc,cc,_⟩ => ?_
  refine WP.mono (nafFinish_ok hL hJ hAl hm hC hOne hone hBits cc)
    fun t ⟨kt,ut,mt,lt,pt⟩ => ⟨?_,?_,mt,lt,pt⟩
  · have tr : ∀ r ∈ jacTreeClob K, r ∈ jacWindowClob K := by
      rw [jacTreeClob,jacWindowClob,hL.n]; decide
    have lr : ∀ r ∈ Reg.x19::clob K.M.n, r ∈ jacWindowClob K := by
      rw [jacWindowClob,hL.n]; decide
    exact (ta.keep.mono tr).trans ((kb.regs.mono lr).trans
      ((kc.regs.mono lr).trans (kt.mono (fun _ hr => List.mem_cons_of_mem _ hr))))
  · have sub : ∀ w ∈ jacLoopWrites K, w ∈ jacTreeWrites K := by
      intro w hw
      simp only [jacLoopWrites,jacTreeWrites,List.mem_append,List.mem_map,List.mem_singleton] at hw ⊢
      rcases hw with ⟨x,hx,rfl⟩ | rfl
      · exact Or.inl ⟨x,List.mem_append_left _ hx,rfl⟩
      · exact Or.inr rfl
    have u1 := ta.unch.trans (kb.mem.mono sub)
    have u2 := (kc.mem.mono sub).trans (ut.mono sub)
    exact (u1.trans u2).mono (fun _ hw => by
      simp only [List.mem_append] at hw
      rcases hw with (hw | hw) | (hw | hw) <;> exact hw)

end VG.Proof.Weierstrass.AArch64
