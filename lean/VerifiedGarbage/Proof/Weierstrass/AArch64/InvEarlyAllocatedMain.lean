import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyAllocated

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Impl.Ecdsa.Verify.AArch64.P256Allocated (inverseBatch inverseNine inverseCheck)

abbrev invAllocatedModulus := p256.C.n

def invAllocatedTail : Prog isa :=
  .seq (.block inverseCheck) <|
    .ite (.nonzero .x .x2)
      (.seq (.block [.movz .x .x19 1 0]) (.seq inverseBatch (.block invAllocatedCfg.finish)))
      (.block inverseNine.finish)

def invAllocatedBody : Prog isa :=
  .seq (.block inverseNine.init)
    (.seq (.loop inverseBatch (.nonzero .x .x19)) invAllocatedTail)

 theorem invAllocated_powClob : ∀ r∈powClob invAllocatedCfg.M.n,r∈invAllocatedRegs := by decide

 theorem invAllocated_original_frame {base : Addr} {s t : State}
    (hU : Unch base (invW invAllocatedCfg) s.mem t.mem) : Unch base invAllocatedW s.mem t.mem := by
  apply hU.cover
  decide

 theorem invAllocated_odd (_hp : invAllocatedModulus.Prime) : invAllocatedModulus%2=1 := by decide

 theorem invAllocated_nine_pos : 0<inverseNine.C := by decide +kernel

 theorem invAllocated_nine_eq : inverseNine=earlyCfg invAllocatedCfg 9 invAllocatedModulus := rfl

/-- Correctness of the public early-exit tail after register allocation. -/
theorem invAllocated_tail_ok {base : Addr} {size X : Nat} [NeZero invAllocatedModulus]
    (hsize : 8192≤size) (hpr : invAllocatedModulus.Prime) (hT : InvToM invAllocatedModulus)
    (hL : InvLay invAllocatedCfg size) (hR : UnitMod invAllocatedModulus (2^256))
    {s : State} (hs : Scr s base size)
    (hM : ModOkA invAllocatedCfg.M size invAllocatedModulus s.mem base)
    (hX : X<invAllocatedModulus) (hC : InvOk invAllocatedCfg invAllocatedModulus)
    (hI : IInv invAllocatedCfg base (Divstep.invRun 59 invAllocatedModulus invAllocatedCfg.M.minv.toNat X 9) s) :
    WP isa invAllocatedTail s fun t =>
      KeepRegs invAllocatedRegs s t ∧ Unch base invAllocatedW s.mem t.mem ∧
      wordsVal t.mem base invAllocatedCfg.acc 4<invAllocatedModulus ∧
      toM invAllocatedModulus (2^256) (wordsVal t.mem base invAllocatedCfg.acc 4)=
        toM invAllocatedModulus (2^256) X ^ (invAllocatedModulus-2) := by
  have hm2 : 2<invAllocatedModulus := by decide
  have hm2' := invAllocated_odd hpr
  have hmi : ((invAllocatedModulus : Int)*(invAllocatedCfg.M.minv.toNat : Int)+1)%2^64=0 := by exact_mod_cast hM.inv
  obtain ⟨bd,bf1,bf,bg,ba0,ba1,bb0,bb1⟩ := Divstep.invRun_bounds (N:=59) (by decide)
    (p:=invAllocatedModulus) (m:=invAllocatedCfg.M.minv.toNat) (x:=X)
    (by exact_mod_cast hm2') (by exact_mod_cast hpr.one_lt) hmi (by omega) (by exact_mod_cast hX) 9
  rw [invAllocatedTail]
  refine WP.seq (WP.mono (earlyCheck_ok hs (n:=5) (a:=2312) (by decide) (by omega) (by decide))
    fun a ⟨az,ka⟩ => ?_)
  have ha := hs.of_keeps ka (by decide)
  have ia := hI.of_keeps ka (by decide)
  have ma : ModOkA invAllocatedCfg.M size invAllocatedModulus a.mem base := by rw [ka.mem]; exact hM
  have kap : KeepRegs invAllocatedRegs s a := (Keeps.regs ka).mono (by decide)
  have eval : isa.eval (.nonzero .x .x2) a=some (decide (wordsVal s.mem base 2312 5≠0)) := by
    change some (a.read .x .x2 != 0)=_
    rw [read_x]
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne,decide_eq_true_eq,ne_eq,az]
  apply WP.ite _ eval
  · intro _
    refine WP.seq (WP.mono (movzI_ok a .x19 1) fun b ⟨b19,kb⟩ => ?_)
    have hb := ha.of_keeps kb (by decide)
    have ib := ia.of_keeps kb (by decide)
    have mb : ModOkA invAllocatedCfg.M size invAllocatedModulus b.mem base := by rw [kb.mem]; exact ma
    refine WP.seq (WP.mono (invAllocated_batch_ok hsize hL hb mb ib (by norm_num at bd ⊢; omega)
      bf1 bf bg (by rw [abs_of_nonneg ba0]; exact ba1.le) (by rw [abs_of_nonneg bb0]; exact bb1.le)
      (j:=1) (by decide) (by decide) b19) fun c ⟨ic,_,kc,uc⟩ => ?_)
    have ic' : IInv invAllocatedCfg base
        (Divstep.invRun 59 invAllocatedModulus invAllocatedCfg.M.minv.toNat X 10) c := ic
    have done : (Divstep.invRun 59 invAllocatedModulus invAllocatedCfg.M.minv.toNat X 10).g=0 := by
      have hd := (Divstep.invRun_dfg (N:=59) (p:=(invAllocatedModulus:Int))
        (m:=invAllocatedCfg.M.minv.toNat) (x:=X) (by exact_mod_cast hm2') 10).1
      have hz := (Divstep.divsteps_590 (by exact_mod_cast hm2') (by omega : (0:Int)≤X)
        (by exact_mod_cast hX.le) (by decide : (invAllocatedModulus:Int)≤2^256) (by decide : 590≤59*10)).1
      rw [←hd] at hz
      exact hz
    refine WP.mono (finish_early_ok hpr hT hL hm2 hR (hb.of_keepRegs kc (by decide))
      (invAllocated_mod hb mb uc) hX ic' done hC.C hC.Cpos hC.Cn) fun t ⟨kt,ut,lt,et⟩ =>
      ⟨(kap.trans ((Keeps.regs kb).mono (by decide))).trans (kc.trans (kt.mono invAllocated_powClob)),?_,lt,et⟩
    intro x hx
    rw [(invAllocated_original_frame ut) x hx,(invAllocated_batch_frame uc) x hx,kb.mem,ka.mem]
  · intro hz
    have hw : wordsVal s.mem base 2312 5=0 := by simpa only [ne_eq,decide_eq_false_iff_not,not_not] using hz
    have hg := hI.g_zero_of_words (lt_of_le_of_lt bg (by decide +kernel : (invAllocatedModulus:Int)<(2^(64*invAllocatedCfg.L):Nat))) hw
    have hl9 : InvLay inverseNine size := by rw [invAllocated_nine_eq]; exact hL.earlyCfg _ _
    refine WP.mono (finish_early_ok hpr hT hl9 hm2 hR ha ma hX (ia.earlyCfg 9 invAllocatedModulus) hg
      rfl invAllocated_nine_pos rfl) fun t ⟨kt,ut,lt,et⟩ =>
      ⟨kap.trans (kt.mono invAllocated_powClob),?_,lt,et⟩
    intro x hx
    rw [(invAllocated_original_frame ut) x hx,ka.mem]

/-- Full value and explicit spill/register frames for the allocated inverse body. -/
theorem invAllocated_body_ok {base : Addr} {size : Nat} [NeZero invAllocatedModulus]
    (hsize : 8192≤size) (hpr : invAllocatedModulus.Prime) (hT : InvToM invAllocatedModulus)
    (hL : InvLay invAllocatedCfg size) (hR : UnitMod invAllocatedModulus (2^256))
    {s : State} (hs : Scr s base size)
    (hM : ModOkA invAllocatedCfg.M size invAllocatedModulus s.mem base)
    (hX : wordsVal s.mem base invAllocatedCfg.base 4<invAllocatedModulus)
    (hC : InvOk invAllocatedCfg invAllocatedModulus) :
    WP isa invAllocatedBody s fun t =>
      KeepRegs invAllocatedRegs s t ∧ Unch base invAllocatedW s.mem t.mem ∧
      wordsVal t.mem base invAllocatedCfg.acc 4<invAllocatedModulus ∧
      toM invAllocatedModulus (2^256) (wordsVal t.mem base invAllocatedCfg.acc 4)=
        toM invAllocatedModulus (2^256) (wordsVal s.mem base invAllocatedCfg.base 4) ^ (invAllocatedModulus-2) := by
  have hl9 : InvLay inverseNine size := by rw [invAllocated_nine_eq]; exact hL.earlyCfg _ _
  rw [invAllocatedBody]
  refine WP.seq (WP.mono (init_ok hl9 hs hM (by decide)) fun a ⟨ia,a19,ka,ua⟩ => ?_)
  have ua' : Unch base invAllocatedBatchW s.mem a.mem := ua.cover (by decide)
  have ha := hs.of_keepRegs ka (by decide)
  have ma := invAllocated_mod hs hM ua'
  have ia' := IInv.of_earlyCfg (P:=invAllocatedCfg) (B:=9) (m:=invAllocatedModulus) ia
  refine WP.seq (WP.mono (invAllocated_loop_ok hsize hL ha ma hX (invAllocated_odd hpr)
    hpr.one_lt (B:=9) (by decide) (by decide) ia' a19)
    fun b ⟨ib,kb,ub⟩ => ?_)
  refine WP.mono (invAllocated_tail_ok hsize hpr hT hL hR (ha.of_keepRegs kb (by decide))
    (invAllocated_mod ha ma ub) hX hC ib) fun t ⟨kt,ut,lt,et⟩ =>
      ⟨(ka.mono (by decide)).trans (kb.trans kt),?_,lt,et⟩
  intro x hx
  rw [ut x hx,(invAllocated_batch_frame ub) x hx,(invAllocated_batch_frame ua') x hx]

end VG.Proof.Weierstrass.AArch64
