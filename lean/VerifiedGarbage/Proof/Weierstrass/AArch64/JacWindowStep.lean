import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSum

/-! A complete five-bit iteration of the public Jacobian loop. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem jacDigitAdd_ok {K : WinCfg} {C : Curve} {base : Addr} {size k j : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (· ∈ jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hTbl : K.tbl<4096) (hBits : K.bits+5≤4096)
    (hk : 16*Window5.geom 52≤k) (hj : j<52)
    {P : Point C} (hP : onCurve C P=true) {s : State}
    (h : JacCore K C base size P k (32*Window5.winE k 52 (j+1)) s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (Jacobian.jacDigitAdd K 5) s fun t =>
      ProgKeep K.M base (winOther K) s t ∧ JacCore K C base size P k (Window5.winE k 52 j) t := by
  let T : TCombCfg := ⟨K.M,K.S,K.R,K.E,K.D,K.neg,K.zero,K.bits,260,"",5,52,(0,0),K.one⟩
  have wd := digitW_ok T h.field.scr (k := k) (j := j) (N := 260)
    (by simp [T]) (by simp [T]) (by dsimp [T]; omega) hL.bits hBits h19 h.stable.bits
  change WP isa (.seq (.block T.digit) (.ite (.nonzero .x .x2) (Jacobian.jacSignedAdd K 5) (.block []))) s _
  apply WP.seq
  refine WP.mono wd fun a ⟨h2,ka⟩ => ?_
  have h2' : a.gpr .x2=BitVec.ofNat 64 (magH 16 (Window5.nib k j)) := by
    simpa only [T,TCombCfg.H,Window5.combWin_five] using h2
  have core := h.of_keeps ka (by decide)
  have pk : ProgKeep K.M base (winOther K) s a := by
    refine ⟨fun r hr => ka.gpr r (fun hh => hr ?_),ka.rd,ka.wr,ka.sp,fun _ _ _ => congrFun ka.mem _⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
    rcases hh with rfl | rfl | rfl | rfl | rfl <;> rw [hL.n] <;> decide
  have h19' : a.gpr .x19=BitVec.ofNat 64 j := by rw [ka.gpr _ (by decide),h19]
  have hmag : magH 16 (Window5.nib k j)≤16 := magH_le (Nat.mod_lt _ (by decide))
  have hz : BitVec.ofNat 64 (magH 16 (Window5.nib k j))=0 ↔ magH 16 (Window5.nib k j)=0 := by
    constructor
    · intro he
      have he' : (BitVec.ofNat 64 (magH 16 (Window5.nib k j))).toNat=0 := congrArg BitVec.toNat he
      simpa only [BitVec.toNat_zero,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : magH 16 (Window5.nib k j)<2^64)] using he'
    · intro he; rw [he]; rfl
  refine WP.ite (decide (magH 16 (Window5.nib k j)≠0)) (by
    change some (a.read .x .x2 != 0) = _
    rw [read_x,h2']
    by_cases he : magH 16 (Window5.nib k j)=0
    · simp [he]
    · have hb : BitVec.ofNat 64 (magH 16 (Window5.nib k j))≠0 := fun he' => he (hz.mp he')
      simp [he,Size.bits]
      exact hb) (fun hnonzero => ?_) (fun hzero => ?_)
  · have hnz := of_decide_eq_true hnonzero
    rw [Jacobian.jacSignedAdd]
    apply WP.seq
    refine WP.mono (jacSignedEntry_ok hL hJ hAl hm hTbl hBits hj core h19' h2' hnz)
      fun b ⟨kb,cb,jb⟩ => ?_
    exact WP.mono (jacAddDigit_ok hL hJ hAl hm hC ha hOne hk hj hP cb jb)
      (fun t ⟨kt,ct⟩ => ⟨pk.trans (kb.trans kt),ct⟩)
  · have he : magH 16 (Window5.nib k j)=0 := by simpa using of_decide_eq_false hzero
    have hnib : Window5.nib k j=16 := by unfold magH at he; split at he <;> omega
    have heq : Window5.winE k 52 j = 32*Window5.winE k 52 (j+1) := by
      have hs := Window5.winE_step hk hj
      rw [hnib] at hs
      omega
    apply WP.block_nil
    exact ⟨pk,heq.symm ▸ core⟩

/-- The loop may change its public counter as well as arithmetic registers. -/
structure JacLoopKeep (K : WinCfg) (base : Addr) (s t : State) : Prop where
  regs : KeepRegs (.x19 :: clob K.M.n) s t
  mem : Unch base (jacLoopWrites K) s.mem t.mem

theorem JacLoopKeep.refl (K : WinCfg) (base : Addr) (s : State) : JacLoopKeep K base s s :=
  ⟨⟨fun _ _ => rfl,rfl,rfl,rfl⟩,fun _ _ => rfl⟩

theorem JacLoopKeep.trans {K : WinCfg} {base : Addr} {s t u : State}
    (h : JacLoopKeep K base s t) (h' : JacLoopKeep K base t u) : JacLoopKeep K base s u :=
  ⟨h.regs.trans h'.regs,(h.mem.trans h'.mem).mono (fun _ hw =>
    (List.mem_append.mp hw).elim id id)⟩

/-- A full iteration, including the public counter decrement. -/
theorem jacStep_ok {K : WinCfg} {C : Curve} {base : Addr} {size k j : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (· ∈ jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hTbl : K.tbl<4096) (hBits : K.bits+5≤4096)
    (hk : 16*Window5.geom 52≤k) (hj : j<52)
    {P : Point C} (hP : onCurve C P=true) {s : State}
    (h : JacCore K C base size P k (Window5.winE k 52 (j+1)) s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 (j+1)) :
    WP isa (Jacobian.jacStep K 5) s fun t =>
      JacLoopKeep K base s t ∧ JacCore K C base size P k (Window5.winE k 52 j) t ∧
      t.gpr .x19=BitVec.ofNat 64 j := by
  rw [Jacobian.jacStep]
  apply WP.seq
  refine WP.mono (decCounter_ok s (by omega) (by omega) h19) fun a ⟨a19,ka⟩ => ?_
  have core := h.of_keeps ka (by decide)
  apply WP.seq
  refine WP.mono (jacFiveCore_ok hL hJ hAl hm hC ha hP core) fun b ⟨kb,cb⟩ => ?_
  have b19 : b.gpr .x19=BitVec.ofNat 64 j := by
    rw [kb.gpr _ (x19_not_clob _),a19]
    simp only [Nat.add_sub_cancel]
  refine WP.mono (jacDigitAdd_ok hL hJ hAl hm hC ha hOne hTbl hBits hk hj hP cb b19)
    fun t ⟨kt,ct⟩ => ⟨?_,ct,?_⟩
  · have kp := kb.trans kt
    refine ⟨(Keeps.regs ka).mono (by simp) |>.trans
      ((⟨kp.gpr,kp.rd,kp.wr,kp.sp⟩ : KeepRegs (clob K.M.n) a t).mono
        (fun _ hr => List.mem_cons_of_mem _ hr)),?_⟩
    simpa only [ka.mem,jacLoopWrites] using kp.unch
  · rw [kt.gpr _ (x19_not_clob _),b19]

end VG.Proof.Weierstrass.AArch64
