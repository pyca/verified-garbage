import VerifiedGarbage.Proof.P256.EcdhInverse.Loop
import VerifiedGarbage.Proof.P256.EcdhInverse.Finish
import VerifiedGarbage.Proof.P256.EcdhInverse.Extra

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

def body : Prog isa := .seq (.block (([.movz .x .x27 0 0] : List Instr)++cfg.init)) <|
  .seq (.loop Impl.P256.EcdhInverse.batch (.nonzero .x .x19)) (.block cfg.finish)

def inverseMemory : List (Nat × Nat) := bodyMemory++[(7800,72)]

theorem zero27_ok (s : State) : WP isa (.block [.movz .x .x27 0 0]) s fun t =>
    t.gpr .x27=0 ∧ Keeps [.x27] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,RegUpd.gpr_write,
    ↓reduceIte,Option.some.injEq,exists_eq_left',
    show (16*0:Nat)<Size.x.bits by decide]
  refine ⟨rfl,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  simp only [RegUpd.gpr_write,hr,↓reduceIte]

theorem body_ok {base : Addr} {m : Nat} [NeZero m]
    (hpr : m.Prime) (hT : InvToM m) (hL : InvLay cfg 8192)
    (hm2 : 2<m) (hR : UnitMod m (2^256)) {s : State}
    (hs : Scr s base 8192) (hM : ModOkA cfg.M 8192 m s.mem base)
    (hX : wordsVal s.mem base cfg.base 4<m) (hC : InvOk cfg m) :
    WP isa body s fun t => KeepRegs batchRegs s t ∧ Unch base bodyMemory s.mem t.mem ∧
      wordsVal t.mem base cfg.acc 4<m ∧
      toM m (2^256) (wordsVal t.mem base cfg.acc 4)=
        toM m (2^256) (wordsVal s.mem base cfg.base 4)^(m-2) := by
  have hodd : m%2=1 := by
    rcases Nat.even_or_odd m with ⟨k,hk⟩|⟨k,hk⟩
    · have := hpr.eq_one_or_self_of_dvd 2 ⟨k,by omega⟩; omega
    · omega
  rw [body]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (zero27_ok s) fun a ⟨az,ka⟩ => ?_
  have ha := hs.of_keeps ka (by decide)
  have ma : ModOkA cfg.M 8192 m a.mem base := by rw [ka.mem]; exact hM
  refine WP.mono (init_ok hL ha ma hC.B16) fun b ⟨ib,b19,kb,ub⟩ => ?_
  have hb := ha.of_keepRegs kb (by decide)
  have bz : b.gpr .x27=0 := by rw [kb.gpr _ (by decide)]; exact az
  have ub' : Unch base batchMemory a.mem b.mem := ub.cover (by decide)
  have mb := mod_keep ha ma ub'
  have hx : wordsVal a.mem base cfg.base 4<m := by rw [ka.mem]; exact hX
  refine WP.seq (WP.mono (packed_loop_ok hL hb mb hx hodd (by omega) ib b19 bz)
    fun c ⟨ic,kc,uc⟩ => ?_)
  have hc := hb.of_keepRegs kc (by decide)
  have mc := mod_keep hb mb uc
  refine WP.mono (finish_power_ok hpr hT hL hm2 hR hc mc hx ic hC)
    fun t ⟨kt,ut,lt,et⟩ => ⟨?_,?_,lt,?_⟩
  · have kra : KeepRegs [.x27] s a := ⟨ka.gpr,ka.rd,ka.wr,ka.sp⟩
    exact (((kra.mono (by decide)).trans (kb.mono (by decide))).trans kc).trans (kt.mono (by decide))
  · have ub'' : Unch base bodyMemory a.mem b.mem := ub.cover (by decide)
    have uc' : Unch base bodyMemory b.mem c.mem := uc.cover (by decide)
    have ut' : Unch base bodyMemory c.mem t.mem := ut.cover (by decide)
    intro x hx
    rw [ut' x hx,uc' x hx,ub'' x hx,ka.mem]
  · change toM m (2^256) (wordsVal t.mem base cfg.acc 4)=
        toM m (2^256) (wordsVal a.mem base cfg.base 4)^(m-2) at et
    rw [et,ka.mem]

theorem inverse_ok {base : Addr} {m : Nat} [NeZero m]
    (hpr : m.Prime) (hT : InvToM m) (hL : InvLay cfg 8192)
    (hm2 : 2<m) (hR : UnitMod m (2^256)) {s : State}
    (hs : Scr s base 8192) (hM : ModOkA cfg.M 8192 m s.mem base)
    (hX : wordsVal s.mem base cfg.base 4<m) (hC : InvOk cfg m) :
    WP isa Impl.P256.EcdhInverse.inverse s fun t =>
      KeepRegs (powClob 4) s t ∧ Unch base inverseMemory s.mem t.mem ∧
      wordsVal t.mem base cfg.acc 4<m ∧
      toM m (2^256) (wordsVal t.mem base cfg.acc 4)=
        toM m (2^256) (wordsVal s.mem base cfg.base 4)^(m-2) := by
  have full : WP isa (.seq (.block Impl.P256.EcdhInverse.saveExtra)
      (.seq body (.block Impl.P256.EcdhInverse.restoreExtra))) s (fun t =>
        KeepRegs (powClob 4) s t ∧ Unch base inverseMemory s.mem t.mem ∧
        wordsVal t.mem base cfg.acc 4<m ∧
        toM m (2^256) (wordsVal t.mem base cfg.acc 4)=
          toM m (2^256) (wordsVal s.mem base cfg.base 4)^(m-2)) := by
    refine WP.seq (WP.mono (saveExtra_ok hs (by decide)) fun a ⟨ka,ua,sa⟩ => ?_)
    have ha := hs.of_keepRegs ka (by simp)
    have ma : ModOkA cfg.M 8192 m a.mem base := by
      refine ⟨hM.n0,hM.n10,hM.mo,hM.tmp,hM.sep,?_,hM.inv,hM.red,hM.call⟩
      rw [ua.wordsVal (by decide) (by decide)]
      exact hM.val
    have va : wordsVal a.mem base cfg.base 4=wordsVal s.mem base cfg.base 4 :=
      ua.wordsVal (by decide) (by decide)
    refine WP.seq (WP.mono (body_ok hpr hT hL hm2 hR ha ma (by rw [va]; exact hX) hC)
      fun b ⟨kb,ub,lb,eb⟩ => ?_)
    have hb := ha.of_keepRegs kb (by decide)
    have sb := savedExtra_keep sa ub (by decide)
    refine WP.mono (restoreExtra_ok hb (by decide) sb) fun t ⟨kt,vt⟩ => ⟨?_,?_,?_,?_⟩
    · exact (restoreExtra_frame ka kb kt vt).mono (by decide)
    · intro x hx
      rw [kt.mem,ub x (fun w hw => hx w (List.mem_append_left _ hw)),
        ua x (hx (7800,72) (List.mem_append_right _ (by simp)))]
    · rw [kt.mem]; exact lb
    · rw [kt.mem,eb,va]
  simpa only [Impl.P256.EcdhInverse.inverse,body,Impl.P256.EcdhInverse.P,
    Impl.P256.EcdhInverse.c,cfg,WP.seq_iff (M:=isa),WP.block_append_iff (M:=isa)] using full

end VG.Proof.P256.EcdhInverse
