import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyCheck

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- The early finish differs only in its actual batch count and scaling constants. -/
def earlyCfg (P : InvCfg) (B m : Nat) : InvCfg :=
  let c := 2^(5*B)*(2^(64*P.M.n))^3 % m
  {P with B:=B,C:=c,Cn:=m-c}

def earlyCheck (P : InvCfg) : List Instr :=
  [ld .x2 P.sG] ++ (List.range (P.L-1)).flatMap fun i =>
    [ld .x3 (P.sG+8*(i+1)),.logic .orr .x .x2 .x2 .x3]

/-- The original-batch early-exit tail, before applying register allocation. -/
def earlyTail (P : InvCfg) (B m : Nat) : Prog isa :=
  .seq (.block (earlyCheck P)) <|
    .ite (.nonzero .x .x2)
      (.seq (.block [.movz .x .x19 1 0]) (.seq P.batch (.block P.finish)))
      (.block (earlyCfg P B m).finish)

theorem IInv.of_keeps {P : InvCfg} {base : Addr} {I : Divstep.IState} {s t : State}
    (hI : IInv P base I s) {rs : List Reg} (h : Keeps rs s t) (h1 : .x1∉rs) : IInv P base I t :=
  ⟨by rw [h.gpr _ h1]; exact hI.d, by rw [h.mem]; exact hI.f,
    by rw [h.mem]; exact hI.g, by rw [h.mem]; exact hI.a, by rw [h.mem]; exact hI.b⟩

theorem IInv.of_earlyCfg {P : InvCfg} {B m : Nat} {base : Addr} {I : Divstep.IState} {s : State}
    (h : IInv (earlyCfg P B m) base I s) : IInv P base I s := ⟨h.d,h.f,h.g,h.a,h.b⟩

theorem IInv.earlyCfg {P : InvCfg} {base : Addr} {I : Divstep.IState} {s : State}
    (h : IInv P base I s) (B m : Nat) : IInv (earlyCfg P B m) base I s := ⟨h.d,h.f,h.g,h.a,h.b⟩

theorem InvLay.earlyCfg {P : InvCfg} {size : Nat} (hL : InvLay P size) (B m : Nat) :
    InvLay (earlyCfg P B m) size := by
  exact ⟨hL.n4,hL.n10,hL.acc,hL.base,hL.tbl,hL.acc8,hL.base8,hL.tbl8,hL.mod,
    hL.acc_base,hL.acc_tbl,hL.base_tbl,hL.acc_tmp,hL.tbl_tmp,hL.mo_acc,hL.mo_tbl,hL.mo_tmp,hL.base_mo⟩

private theorem batch_mod {P : InvCfg} {base : Addr} {size m : Nat} {s t : State}
    (hL : InvLay P size) (hs : Scr s base size) (hM : ModOkA P.M size m s.mem base)
    (hU : Unch base (batchW P) s.mem t.mem) : ModOkA P.M size m t.mem base := by
  refine ⟨hM.n0,hM.n10,hM.mo,hM.tmp,hM.sep,?_,hM.inv,hM.red, hM.call⟩
  rw [hU.wordsVal (fun w hw => by
    simp only [batchW,List.mem_cons,List.not_mem_nil,or_false] at hw
    subst hw
    dsimp only
    omega_using [hL.mo_tbl,hL.n4]) (by omega_using [hM.mo,hs.nowrap])]
  exact hM.val

private theorem batch_frame {P : InvCfg} {base : Addr} {s t : State}
    (hU : Unch base (batchW P) s.mem t.mem) (hn : 4≤P.M.n) : Unch base (invW P) s.mem t.mem := by
  intro x hx
  apply hU x
  intro w hw
  simp only [batchW,List.mem_cons,List.not_mem_nil,or_false] at hw
  subst hw
  have hh := hx (P.tbl,9*(8*P.M.n)) (by simp [invW])
  dsimp only at hh ⊢
  omega

/-- One optional final batch, selected solely by whether the signed remainder is zero. -/
theorem earlyTail_ok {P : InvCfg} {B : Nat} {base : Addr} {size m X : Nat} [NeZero m]
    (hpr : m.Prime) (hT : InvToM m) (hL : InvLay P size)
    (hm2 : 2<m) (hR : UnitMod m (2^(64*P.M.n))) {s : State}
    (hs : Scr s base size) (hM : ModOkA P.M size m s.mem base) (hX : X<m)
    (hC : InvOk P m) (hB : B+1=P.B)
    (hc : 0<(earlyCfg P B m).C)
    (hI : IInv P base (Divstep.invRun 59 m P.M.minv.toNat X B) s) :
    WP isa (earlyTail P B m) s fun t =>
      KeepRegs (powClob P.M.n) s t ∧ Unch base (invW P) s.mem t.mem ∧
      wordsVal t.mem base P.acc P.M.n<m ∧
      toM m (2^(64*P.M.n)) (wordsVal t.mem base P.acc P.M.n)=
        toM m (2^(64*P.M.n)) X ^ (m-2) := by
  have hm2' : m%2=1 := by
    rcases Nat.even_or_odd m with ⟨k,hk⟩ | ⟨k,hk⟩
    · have := hpr.eq_one_or_self_of_dvd 2 ⟨k, by omega⟩; omega
    · omega
  have hmi : ((m : Int)*(P.M.minv.toNat : Int)+1)%2^64=0 := by exact_mod_cast hM.inv
  obtain ⟨bd,bf1,bf,bg,ba0,ba1,bb0,bb1⟩ := Divstep.invRun_bounds
    (N:=59) (by decide) (p:=m) (m:=P.M.minv.toNat) (x:=X)
    (by exact_mod_cast hm2') (by exact_mod_cast hpr.one_lt) hmi (by omega) (by exact_mod_cast hX) B
  have hn := hs.nowrap
  have hsub := invClob_sub hL.n4 hL.n10
  obtain ⟨eL,eF,eG,eA,eB,eNF,eNG,eT⟩ := slots P
  rw [earlyTail]
  refine WP.seq (WP.mono (earlyCheck_ok hs (n:=P.L) (a:=P.sG)
    (by omega_using [eL]) (by omega_using [eG,eL,hL.tbl,hL.n4])
    (by omega_using [eG,hL.tbl8])) fun a ⟨az,ka⟩ => ?_)
  have ha := hs.of_keeps ka (by decide)
  have ia := hI.of_keeps ka (by decide)
  have ma : ModOkA P.M size m a.mem base := by rw [ka.mem]; exact hM
  have kap : KeepRegs (powClob P.M.n) s a := (Keeps.regs ka).mono fun r hr => hsub r (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> decide)
  have eval : isa.eval (.nonzero .x .x2) a = some (decide (wordsVal s.mem base P.sG P.L≠0)) := by
    change some (a.read .x .x2 != 0)=_
    rw [read_x]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne,decide_eq_true_eq,ne_eq,az]
  apply WP.ite _ eval
  · intro _
    refine WP.seq (WP.mono (movzI_ok a .x19 1) fun b ⟨b19,kb⟩ => ?_)
    have hb := ha.of_keeps kb (by decide)
    have ib := ia.of_keeps kb (by decide)
    have mb : ModOkA P.M size m b.mem base := by rw [kb.mem]; exact ma
    refine WP.seq (WP.mono (batch_ok hL hb mb ib (by
      have hlim := hC.B16
      have hbi : B<2^16 := by omega
      have hbound : ((59*B : Nat) : Int)≤59*2^16 := by exact_mod_cast (Nat.mul_le_mul_left 59 hbi.le)
      omega) bf1 bf bg (by rw [abs_of_nonneg ba0]; exact ba1.le)
      (by rw [abs_of_nonneg bb0]; exact bb1.le) (j:=1) (by decide) (by decide) b19)
      fun c ⟨ic,_,kc,uc⟩ => ?_)
    have ic' : IInv P base (Divstep.invRun 59 m P.M.minv.toNat X P.B) c := by
      rw [←hB]
      exact ic
    have done : (Divstep.invRun 59 m P.M.minv.toNat X P.B).g=0 := by
      have hd := (Divstep.invRun_dfg (N:=59) (p:=(m:Int)) (m:=P.M.minv.toNat) (x:=X)
        (by exact_mod_cast hm2') P.B).1
      have hfn : (m : Int)<2^(64*P.M.n) := by exact_mod_cast (hM.val ▸ wordsVal_lt s.mem base P.M.mo P.M.n)
      have hzero := (Divstep.divsteps_words (by exact_mod_cast hm2') (by omega : (0:Int)≤X)
        (by exact_mod_cast hX.le) hfn hC.bound).1
      rw [←hd] at hzero
      exact hzero
    refine WP.mono (finish_early_ok hpr hT hL hm2 hR (hb.of_keepRegs kc (by decide))
      (batch_mod hL hb mb uc) hX ic' done hC.C hC.Cpos hC.Cn) fun t ⟨kt,ut,lt,et⟩ =>
      ⟨(kap.trans ((Keeps.regs kb).mono fun r hr => hsub r (by rw [List.mem_singleton] at hr; subst hr; decide))).trans ((kc.mono hsub).trans kt),
        ?_,lt,et⟩
    intro x hx
    rw [ut x hx,(batch_frame uc hL.n4) x hx,kb.mem,ka.mem]
  · intro hz
    have hw : wordsVal s.mem base P.sG P.L=0 := by simpa using of_decide_eq_false hz
    have hmwords : (m : Int)<(2^(64*P.L) : Nat) := by
      have hm0 := hM.val ▸ wordsVal_lt s.mem base P.M.mo P.M.n
      have hh : 2^(64*P.M.n)≤(2^(64*P.L) : Nat) := Nat.pow_le_pow_right (by decide) (by omega_using [eL])
      exact_mod_cast (lt_of_lt_of_le hm0 hh)
    have hg := hI.g_zero_of_words (lt_of_le_of_lt bg hmwords) hw
    refine WP.mono (finish_early_ok hpr hT (hL.earlyCfg B m) hm2 hR ha ma hX ⟨ia.d,ia.f,ia.g,ia.a,ia.b⟩ hg rfl hc rfl)
      fun t ⟨kt,ut,lt,et⟩ => ⟨kap.trans kt,?_,lt,et⟩
    intro x hx
    rw [ut x hx,ka.mem]

/-- Early inversion using the existing, unallocated batch implementation. -/
def earlyInv (P : InvCfg) (B m : Nat) : Prog isa :=
  .seq (.block (earlyCfg P B m).init)
    (.seq (.loop P.batch (.nonzero .x .x19)) (earlyTail P B m))

/-- An early check one batch before the established bound preserves the full inversion contract. -/
theorem earlyInv_ok {P : InvCfg} {B : Nat} {base : Addr} {size m : Nat} [NeZero m]
    (hpr : m.Prime) (hT : InvToM m) (hL : InvLay P size)
    (hm2 : 2<m) (hR : UnitMod m (2^(64*P.M.n))) {s : State}
    (hs : Scr s base size) (hM : ModOkA P.M size m s.mem base)
    (hX : wordsVal s.mem base P.base P.M.n<m)
    (hC : InvOk P m) (hB1 : 1≤B) (hB : B+1=P.B)
    (hc : 0<(earlyCfg P B m).C) :
    WP isa (earlyInv P B m) s fun t =>
      KeepRegs (powClob P.M.n) s t ∧ Unch base (invW P) s.mem t.mem ∧
      wordsVal t.mem base P.acc P.M.n<m ∧
      toM m (2^(64*P.M.n)) (wordsVal t.mem base P.acc P.M.n)=
        toM m (2^(64*P.M.n)) (wordsVal s.mem base P.base P.M.n) ^ (m-2) := by
  have hb16 : B<2^16 := by have := hC.B16; omega
  have hm2' : m%2=1 := by
    rcases Nat.even_or_odd m with ⟨k,hk⟩ | ⟨k,hk⟩
    · have := hpr.eq_one_or_self_of_dvd 2 ⟨k, by omega⟩; omega
    · omega
  let Q := earlyCfg P B m
  have hQ := hL.earlyCfg B m
  have hsub := invClob_sub hL.n4 hL.n10
  rw [earlyInv]
  refine WP.seq (WP.mono (init_ok hQ hs hM hb16) fun a ⟨ia,a19,ka,ua⟩ => ?_)
  have ha := hs.of_keepRegs ka (by decide)
  have ma := batch_mod hL hs hM ua
  have kap : KeepRegs (powClob P.M.n) s a := ka.mono fun r hr => hsub r (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  refine WP.seq (WP.mono (loop_ok hQ ha ma hX hm2' (by omega) hB1 hb16 ia a19)
    fun b ⟨ib,kb,ub⟩ => ?_)
  have hb := ha.of_keepRegs kb (by decide)
  have mb := batch_mod hL ha ma ub
  refine WP.mono (earlyTail_ok hpr hT hL hm2 hR hb mb hX hC hB hc
    ⟨ib.d,ib.f,ib.g,ib.a,ib.b⟩) fun t ⟨kt,ut,lt,et⟩ =>
    ⟨kap.trans ((kb.mono hsub).trans kt),?_,lt,et⟩
  intro x hx
  rw [ut x hx,(batch_frame ub hL.n4) x hx,(batch_frame ua hL.n4) x hx]

end VG.Proof.Weierstrass.AArch64
