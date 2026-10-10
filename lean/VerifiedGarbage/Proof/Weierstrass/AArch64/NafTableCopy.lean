import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSum
import VerifiedGarbage.Proof.Weierstrass.Naf5
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafEntryTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafArithmeticTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoop
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafInvariant
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTree

/-! ## `NafDigit` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem nafMagnitude_byte (k j : Nat) : nafMagnitude (Naf5.byte k j)=Naf5.magnitude k j :=
  Naf5.byte_magnitude k j

theorem nafNegative_byte (k j : Nat) : nafNegative (Naf5.byte k j)=Naf5.negative k j :=
  Naf5.byte_negative k j

private theorem nafByteTest : ∀ b : BitVec 8,
    (b.setWidth 64 != 0)=decide (nafMagnitude b≠0) := by decide +kernel

theorem nafDigit_ok {K : WinCfg} {C : Curve} {base : Addr} {size k j : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hTbl : K.tbl<4096) (hBits : K.bits<4096) (hj : j<257)
    {P : Point C} (hP : onCurve C P=true) {s : State}
    (h : NafCore K C base size P (Naf5.byte k) (2*Naf5.residual k (j+1)) s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (Naf.digit K) s fun t =>
      ProgKeep K.M base (winOther K) s t ∧
      NafCore K C base size P (Naf5.byte k) (Naf5.residual k j) t := by
  rw [Naf.digit]
  apply WP.seq
  refine WP.mono (nafRead_ok h.field.scr hBits (by have := hL.bits; omega) h19
    (h.stable.bits j hj) .x2) fun u ⟨u2,ku⟩ => ?_
  have cu := h.of_keeps ku (by decide)
  have u19 : u.gpr .x19=BitVec.ofNat 64 j := (ku.gpr _ (by decide)).trans h19
  have kp : ProgKeep K.M base (winOther K) s u := keeps_prog ku (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp [clob])
  refine WP.ite (decide (Naf5.magnitude k j≠0)) (by
    change some (u.read .x .x2 != 0)=_
    rw [read_x,u2,nafByteTest,nafMagnitude_byte]) (fun hn => ?_) (fun hz => ?_)
  · have hm0 : Naf5.magnitude k j≠0 := of_decide_eq_true hn
    apply WP.seq
    refine WP.mono (nafEntry_ok hL hJ hAl hm hTbl hBits hj
      (by rw [nafMagnitude_byte]; omega) (by rw [nafMagnitude_byte]; exact Naf5.magnitude_le k j)
      (by rw [nafMagnitude_byte]; exact (Naf5.magnitude_odd_or_zero k j).resolve_left hm0)
      cu u19 u2) fun v ⟨kv,cv,iv,jv⟩ => ?_
    simp only [nafNegative_byte,nafMagnitude_byte] at jv
    exact WP.mono (nafAdd_ok hL hJ hAl hm hC ha hOne hP (Naf5.onCurve_point hC hP k j)
      (Naf5.add_step hC hP k j) cv iv jv) fun t ⟨kt,ct⟩ => ⟨kp.trans (kv.trans kt),ct⟩
  · have hm0 : Naf5.magnitude k j=0 := by simpa only [ne_eq,not_not] using of_decide_eq_false hz
    have he : Naf5.residual k j=2*Naf5.residual k (j+1) := by
      have hh := Naf5.recurrence k j
      rw [hm0] at hh
      split at hh <;> omega
    apply WP.block_nil
    exact ⟨kp,he.symm ▸ cu⟩

end VG.Proof.Weierstrass.AArch64

end

/-! ## `NafDigitTiming` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (read_x)

structure NafDigitChecks (K : WinCfg) : Prop where
  entry : NafEntryChecks K
  add : JacAddChecks K K.R K.E K.D
  copy : FieldCT (.block (copyPt K.M.n K.R K.D))
  digit : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]))
    (.block (Naf.digitRead K))

theorem nafDigit_relCT {K : WinCfg} {C : Curve} {base : Addr} {size k j e : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hOne : K.one<C.p)
    (hTbl : K.tbl<4096) (hBits : K.bits<4096) (hj : j<257) (hc : NafDigitChecks K)
    {P : Point C} {E : Nat → Fe C} :
    RelCT isa (fun s t => FieldPair K.M base size C.p (·∈jacWinSlots K) (nafLive K) E s t ∧
      NafCore K C base size P (Naf5.byte k) e s ∧ NafCore K C base size P (Naf5.byte k) e t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
      (Naf.digit K)
      (fun s t => ∃ E', FieldPair K.M base size C.p (·∈jacWinSlots K) (nafLive K) E' s t) := by
  have digit : RelCT isa (fun s t => FieldPair K.M base size C.p (·∈jacWinSlots K) (nafLive K) E s t ∧
      NafCore K C base size P (Naf5.byte k) e s ∧ NafCore K C base size P (Naf5.byte k) e t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
      (.block (Naf.digitRead K))
      (fun s t => FieldPair K.M base size C.p (·∈jacWinSlots K) (nafLive K) E s t ∧
      NafCore K C base size P (Naf5.byte k) e s ∧ NafCore K C base size P (Naf5.byte k) e t ∧
      s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j ∧
      s.gpr .x2=(Naf5.byte k j).setWidth 64 ∧ t.gpr .x2=(Naf5.byte k j).setWidth 64) := by
    intro s t ts tt s' t' ⟨hp,cs,ct,ps,pt⟩ es et
    obtain ⟨_,_,xs,vs,ks⟩ := nafRead_ok hp.left.scr hBits (by have := hL.bits; omega) ps (cs.stable.bits j hj) .x2
    obtain ⟨_,_,xt,vt,kt⟩ := nafRead_ok hp.right.scr hBits (by have := hL.bits; omega) pt (ct.stable.bits j hj) .x2
    obtain ⟨_,rfl⟩ := Exec.det es xs
    obtain ⟨_,rfl⟩ := Exec.det et xt
    have pub : AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]) s t := by
      refine ⟨hp.sp,fun r hr => ?_⟩
      simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.left.scr.x0.trans hp.right.scr.x0.symm
      · exact ps.trans pt.symm
    refine ⟨hc.digit _ _ _ _ _ _ trivial trivial pub es et,
      ⟨hp.left.of_keeps ks (by decide),hp.right.of_keeps kt (by decide),ks.sp.trans (hp.sp.trans kt.sp.symm)⟩,
      cs.of_keeps ks (by decide),ct.of_keeps kt (by decide),
      (ks.gpr _ (by decide)).trans ps,(kt.gpr _ (by decide)).trans pt,vs,vt⟩
  rw [Naf.digit]
  apply RelCT.seq digit
  apply RelCT.ite
  · intro s t ⟨_,_,_,_,_,s2,t2⟩
    change some (s.read .x .x2 != 0) = some (t.read .x .x2 != 0)
    rw [read_x,read_x,s2,t2]
  · intro s t ts tt s' t' ⟨⟨hp,cs,ct,s19,t19,s2,t2⟩,hn⟩ es et
    have anz : Naf5.magnitude k j≠0 := by
      intro hz
      have hb : Naf5.byte k j=0 := (Naf5.byte_zero_iff k j).mpr hz
      change some (s.read .x .x2 != 0)=some true at hn
      rw [read_x,s2,hb] at hn
      contradiction
    have entry := nafEntry_relCT (base:=base) (P:=P) (E:=E) (β:=Naf5.byte k) hL hJ hAl hm hTbl hBits hj
      (by rw [nafMagnitude_byte]; omega) (by rw [nafMagnitude_byte]; exact Naf5.magnitude_le k j) hc.entry
    have add := fun E' => nafAdd_relCT (base:=base) (E:=E') hL hJ hAl hm hOne hc.add hc.copy
    exact (RelCT.seq entry (RelCT.exists_ add)) _ _ _ _ _ _
      ⟨hp,cs.stable,ct.stable,s19,t19,s2,t2⟩ es et
  · intro s t ts tt s' t' ⟨⟨hp,_,_,_,_,_,_⟩,_⟩ es et
    have hs : s'=s ∧ ts=[] := by cases es with | block he => simp only [execBlock,Option.some.injEq,Prod.mk.injEq] at he; exact ⟨he.1.symm,he.2.symm⟩
    have ht : t'=t ∧ tt=[] := by cases et with | block he => simp only [execBlock,Option.some.injEq,Prod.mk.injEq] at he; exact ⟨he.1.symm,he.2.symm⟩
    rcases hs with ⟨rfl,rfl⟩
    rcases ht with ⟨rfl,rfl⟩
    exact ⟨rfl,_,hp⟩

end VG.Proof.Weierstrass.AArch64

end

/-! ## `NafLoop` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps)

theorem nafStep_ok {K : WinCfg} {C : Curve} {base : Addr} {size k j : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hTbl : K.tbl<4096) (hBits : K.bits<4096) (hj : j<256)
    {P : Point C} (hP : onCurve C P=true) {s : State}
    (h : NafCore K C base size P (Naf5.byte k) (Naf5.residual k (j+1)) s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 (j+1)) :
    WP isa (Naf.step K) s fun t =>
      JacLoopKeep K base s t ∧ NafCore K C base size P (Naf5.byte k) (Naf5.residual k j) t ∧
      t.gpr .x19=BitVec.ofNat 64 j := by
  rw [Naf.step]
  apply WP.seq
  refine WP.mono (decCounter_ok s (by omega) (by omega) h19) fun a ⟨a19,ka⟩ => ?_
  have ca := h.of_keeps ka (by decide)
  apply WP.assoc
  apply WP.seq
  refine WP.mono (nafDoubleCore_ok hL hJ hAl hm hC ha hP ca) fun b ⟨kb,cb⟩ => ?_
  have b19 : b.gpr .x19=BitVec.ofNat 64 j := by
    rw [kb.gpr _ (x19_not_clob _),a19,Nat.add_sub_cancel]
  refine WP.mono (nafDigit_ok hL hJ hAl hm hC ha hOne hTbl hBits (by omega) hP cb b19)
    fun t ⟨kt,ct⟩ => ⟨?_,ct,?_⟩
  · have kp := kb.trans kt
    refine ⟨(Keeps.regs ka).mono (by simp) |>.trans
      ((⟨kp.gpr,kp.rd,kp.wr,kp.sp⟩ : KeepRegs (clob K.M.n) a t).mono
        (fun _ hr => List.mem_cons_of_mem _ hr)),?_⟩
    simpa only [ka.mem,jacLoopWrites] using kp.unch
  · rw [kt.gpr _ (x19_not_clob _),b19]

theorem nafLoop_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hTbl : K.tbl<4096) (hBits : K.bits<4096)
    {P : Point C} (hP : onCurve C P=true) {s : State}
    (h : NafCore K C base size P (Naf5.byte k) (Naf5.residual k 256) s)
    (h19 : s.gpr .x19=256) :
    WP isa (.loop (Naf.step K) (.nonzero .x .x19)) s fun t =>
      JacLoopKeep K base s t ∧ NafCore K C base size P (Naf5.byte k) k t ∧ t.gpr .x19=0 := by
  let I := fun j t => JacLoopKeep K base s t ∧
    NafCore K C base size P (Naf5.byte k) (Naf5.residual k j) t ∧ t.gpr .x19=BitVec.ofNat 64 j
  apply countLoop_ok (Inv:=I) (n:=256) (by decide)
  · intro j a hj1 hj256 hi
    obtain ⟨ka,ca,a19⟩ := hi
    have he : j-1+1=j := by omega
    have cp : NafCore K C base size P (Naf5.byte k) (Naf5.residual k (j-1+1)) a := he.symm ▸ ca
    have ap : a.gpr .x19=BitVec.ofNat 64 (j-1+1) := he.symm ▸ a19
    refine WP.mono (nafStep_ok hL hJ hAl hm hC ha hOne hTbl hBits (by omega) hP cp ap)
      fun t ⟨kt,ct,t19⟩ => ⟨⟨ka.trans kt,ct,t19⟩,t19⟩
  · intro t ht
    obtain ⟨kt,ct,t19⟩ := ht
    exact ⟨kt,ct,t19⟩
  · decide
  · exact ⟨JacLoopKeep.refl K base s,h,h19⟩

/-- Seed bit256 directly, then execute the remaining 256 public digits. -/
theorem nafRun_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hTbl : K.tbl<4096) (hBits : K.bits<4096) (hk : k<2^256)
    {P : Point C} (hP : onCurve C P=true) {s : State}
    (h : NafCore K C base size P (Naf5.byte k) 0 s) (h19 : s.gpr .x19=256) :
    WP isa (.seq (Naf.digit K) (.loop (Naf.step K) (.nonzero .x .x19))) s fun t =>
      JacLoopKeep K base s t ∧ NafCore K C base size P (Naf5.byte k) k t ∧ t.gpr .x19=0 := by
  have he : 2*Naf5.residual k (256+1)=0 := by rw [Naf5.residual_zero257 hk,Nat.mul_zero]
  apply WP.seq
  refine WP.mono (nafDigit_ok hL hJ hAl hm hC ha hOne hTbl hBits (by decide) hP (he.symm ▸ h) h19)
    fun a ⟨ka,ca⟩ => ?_
  have a19 : a.gpr .x19=256 := (ka.gpr _ (x19_not_clob _)).trans h19
  refine WP.mono (nafLoop_ok hL hJ hAl hm hC ha hOne hTbl hBits hP ca a19) fun t ⟨kt,ct,t19⟩ => ⟨?_,ct,t19⟩
  have kp : JacLoopKeep K base s a := ⟨(⟨ka.gpr,ka.rd,ka.wr,ka.sp⟩ : KeepRegs (clob K.M.n) s a).mono
    (fun _ hr => List.mem_cons_of_mem _ hr),ka.unch⟩
  exact kp.trans kt

end VG.Proof.Weierstrass.AArch64

end

/-! ## `NafStepTiming` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

def NafPair (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C)
    (k e j : Nat) (s t : State) : Prop :=
  (∃ E, FieldPair K.M base size C.p (·∈jacWinSlots K) (nafLive K) E s t) ∧
  NafCore K C base size P (Naf5.byte k) e s ∧ NafCore K C base size P (Naf5.byte k) e t ∧
  s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j

structure NafStepChecks (K : WinCfg) : Prop where
  double : FieldCT (Naf.double K K.R K.D)
  copy : FieldCT (.block (copyPt K.M.n K.R K.D))
  digit : NafDigitChecks K
  dec : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x19]))
    (.block [decCounter])

theorem nafStep_relCT {K : WinCfg} {C : Curve} {base : Addr} {size k j : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hTbl : K.tbl<4096) (hBits : K.bits<4096)
    (hj : j<256) (hc : NafStepChecks K)
    {P : Point C} (hP : onCurve C P=true) :
    RelCT isa (NafPair K C base size P k (Naf5.residual k (j+1)) (j+1))
      (Naf.step K) (NafPair K C base size P k (Naf5.residual k j) j) := by
  have raw : RelCT isa (NafPair K C base size P k (Naf5.residual k (j+1)) (j+1))
      (.seq (.block [decCounter]) (.seq (.seq (Naf.double K K.R K.D) (.block (copyPt 4 K.R K.D))) (Naf.digit K)))
      (fun s t => ∃ E, FieldPair K.M base size C.p (·∈jacWinSlots K) (nafLive K) E s t) := by
    intro s t ts tt s' t' ⟨⟨E,hp⟩,cs,ct,ps,pt⟩ es et
    change Exec isa (.seq (.block [decCounter]) (.seq ((.seq (Naf.double K K.R K.D) (.block (copyPt 4 K.R K.D)))) (Naf.digit K))) s ts s' at es
    change Exec isa (.seq (.block [decCounter]) (.seq ((.seq (Naf.double K K.R K.D) (.block (copyPt 4 K.R K.D)))) (Naf.digit K))) t tt t' at et
    cases es with | seq ds bs =>
      cases et with | seq dt bt =>
        obtain ⟨_,_,xs,vs,ks⟩ := decCounter_ok s (by omega : 1≤j+1) (by omega : j+1<2^64) ps
        obtain ⟨_,_,xt,vt,kt⟩ := decCounter_ok t (by omega : 1≤j+1) (by omega : j+1<2^64) pt
        obtain ⟨_,rfl⟩ := Exec.det ds xs
        obtain ⟨_,rfl⟩ := Exec.det dt xt
        have hd := hc.dec _ _ _ _ _ _ trivial trivial ⟨hp.sp,fun r hr => by
          simp only [Taint.mem_ofRegs,List.mem_singleton] at hr
          subst hr
          exact ps.trans pt.symm⟩ ds dt
        have pair : FieldPair K.M base size C.p (·∈jacWinSlots K) (nafLive K) E _ _ :=
          ⟨hp.left.of_keeps ks (by decide),hp.right.of_keeps kt (by decide),ks.sp.trans (hp.sp.trans kt.sp.symm)⟩
        have ca := cs.of_keeps ks (by decide)
        have cb := ct.of_keeps kt (by decide)
        cases bs with | seq fs gs =>
          cases bt with | seq ft gt =>
            obtain ⟨hf,E',pair'⟩ := nafDouble_relCT hL hJ hAl hm hc.double hc.copy _ _ _ _ _ _ pair fs ft
            obtain ⟨_,_,xf,kf,cf⟩ := nafDoubleCore_ok hL hJ hAl hm hC ha hP ca
            obtain ⟨_,_,xg,kg,cg⟩ := nafDoubleCore_ok hL hJ hAl hm hC ha hP cb
            obtain ⟨_,rfl⟩ := Exec.det fs xf
            obtain ⟨_,rfl⟩ := Exec.det ft xg
            have s19 := (kf.gpr _ (x19_not_clob _)).trans vs
            simp only [Nat.add_sub_cancel] at s19
            have t19 := (kg.gpr _ (x19_not_clob _)).trans vt
            simp only [Nat.add_sub_cancel] at t19
            obtain ⟨hg,hp'⟩ := nafDigit_relCT hL hJ hAl hm hOne hTbl hBits (by omega) hc.digit
              _ _ _ _ _ _ ⟨pair',cf,cg,s19,t19⟩ gs gt
            exact ⟨by rw [hd,hf,hg],hp'⟩
  intro s t ts tt s' t' hp es et
  have regroup : ∀ {u v tr}, Exec isa (Naf.step K) u tr v →
      Exec isa (.seq (.block [decCounter]) (.seq (.seq (Naf.double K K.R K.D)
        (.block (copyPt 4 K.R K.D))) (Naf.digit K))) u tr v := by
    intro u v tr ex
    cases ex with | seq ea eb =>
      cases eb with | seq ec ed =>
        cases ed with | seq ee ef =>
          simpa only [List.append_assoc] using Exec.seq ea (Exec.seq (Exec.seq ec ee) ef)
  obtain ⟨he,pair⟩ := raw _ _ _ _ _ _ hp (regroup es) (regroup et)
  obtain ⟨_,cs,ct,ps,pt⟩ := hp
  obtain ⟨_,_,xs,_,cs',ps'⟩ := nafStep_ok hL hJ hAl hm hC ha hOne hTbl hBits hj hP cs ps
  obtain ⟨_,_,xt,_,ct',pt'⟩ := nafStep_ok hL hJ hAl hm hC ha hOne hTbl hBits hj hP ct pt
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  exact ⟨he,pair,cs',ct',ps',pt'⟩

end VG.Proof.Weierstrass.AArch64

end

/-! ## `NafLoopTiming` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (read_x)

theorem nafLoop_relCT {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hTbl : K.tbl<4096) (hBits : K.bits<4096)
    (hc : NafStepChecks K)
    {P : Point C} (hP : onCurve C P=true) :
    RelCT isa (NafPair K C base size P k (Naf5.residual k 256) 256)
      (.loop (Naf.step K) (.nonzero .x .x19))
      (NafPair K C base size P k k 0) := by
  let I := fun j s t => 1≤j ∧ j≤256 ∧ NafPair K C base size P k (Naf5.residual k j) j s t
  have step : ∀ j, RelCT isa (I j) (Naf.step K) (fun s t =>
      eval (.nonzero .x .x19) s=eval (.nonzero .x .x19) t ∧
      (eval (.nonzero .x .x19) s=some false → NafPair K C base size P k k 0 s t) ∧
      (eval (.nonzero .x .x19) s=some true → ∃ n<j, I n s t)) := by
    intro j
    by_cases hj : 1≤j
    · by_cases hj256 : j≤256
      · refine (nafStep_relCT hL hJ hAl hm hC ha hOne hTbl hBits (j:=j-1) (by omega) hc hP).mono
          (P':=I j) (fun _ _ h => by simpa only [Nat.sub_add_cancel hj] using h.2.2) ?_
        intro s t hp
        have s19 := hp.2.2.2.1
        have t19 := hp.2.2.2.2
        refine ⟨by simp only [eval,State.read,s19,t19],fun he => ?_,fun he => ?_⟩
        · have hz : j-1=0 := by
            by_contra hn
            have hb : (BitVec.ofNat 64 (j-1) != 0)=true := by
              rw [bne_iff_ne]
              intro hh
              have hh' := congrArg BitVec.toNat hh
              simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : j-1<2^64)] at hh'
              exact hn hh'
            have htrue : eval (.nonzero .x .x19) s=some true := by
              change some (s.read .x .x19 != 0)=some true
              rw [read_x,s19,hb]
            rw [htrue] at he; cases he
          simpa only [hz,Naf5.residual_zero] using hp
        · have hz : j-1≠0 := by
            intro hz; simp only [eval,State.read,s19,hz] at he; cases he
          exact ⟨j-1,by omega,by omega,by omega,hp⟩
      · exact RelCT.of_false (fun _ _ h => hj256 h.2.1)
    · exact RelCT.of_false (fun _ _ h => hj h.1)
  exact (RelCT.loop I step 256).mono (fun _ _ h => ⟨by decide,by decide,by
    exact h⟩) (fun _ _ h => h)


theorem nafRun_relCT {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hTbl : K.tbl<4096) (hBits : K.bits<4096) (hk : k<2^256) (hc : NafStepChecks K)
    {P : Point C} (hP : onCurve C P=true) :
    RelCT isa (NafPair K C base size P k 0 256)
      (.seq (Naf.digit K) (.loop (Naf.step K) (.nonzero .x .x19)))
      (NafPair K C base size P k k 0) := by
  have seed : RelCT isa (NafPair K C base size P k 0 256) (Naf.digit K)
      (NafPair K C base size P k (Naf5.residual k 256) 256) := by
    intro s t ts tt s' t' ⟨⟨E,hp⟩,cs,ct,ps,pt⟩ es et
    obtain ⟨he,E',pair⟩ := nafDigit_relCT hL hJ hAl hm hOne hTbl hBits (by decide) hc.digit
      _ _ _ _ _ _ ⟨hp,cs,ct,ps,pt⟩ es et
    have hz : 2*Naf5.residual k (256+1)=0 := by rw [Naf5.residual_zero257 hk,Nat.mul_zero]
    obtain ⟨_,_,xs,ks,cs'⟩ := nafDigit_ok hL hJ hAl hm hC ha hOne hTbl hBits (by decide) hP (hz.symm ▸ cs) ps
    obtain ⟨_,_,xt,kt,ct'⟩ := nafDigit_ok hL hJ hAl hm hC ha hOne hTbl hBits (by decide) hP (hz.symm ▸ ct) pt
    obtain ⟨_,rfl⟩ := Exec.det es xs
    obtain ⟨_,rfl⟩ := Exec.det et xt
    exact ⟨he,⟨E',pair⟩,cs',ct',(ks.gpr _ (x19_not_clob _)).trans ps,
      (kt.gpr _ (x19_not_clob _)).trans pt⟩
  exact RelCT.seq seed (nafLoop_relCT hL hJ hAl hm hC ha hOne hTbl hBits hc hP)

end VG.Proof.Weierstrass.AArch64

end

/-! ## `NafTableState` -/

section

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

end

/-! ## `NafTableCopy` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

theorem copyPointFields_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    {q o : Pt} (hN : (jacCoords o).Nodup)
    (hqa : ∀ x∈jacCoords q, ∀ y∈jacCoords o, x≠y)
    (hO : ∀ x∈jacCoords o, Sl x)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hV : ∀ x∈jacCoords q, x∈V) :
    WP isa (.block (copyPt M.n o q)) s fun t =>
      ∃ E', ProgKeep M base (jacCoords o) s t ∧
      Inv M base size m Sl (jacCoords o ++ V) E' t ∧
      (E' o.x,E' o.y,E' o.z)=(E q.x,E q.y,E q.z) := by
  have hn := hN
  simp only [jacCoords,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    or_false,not_or,List.nodup_nil,and_true] at hn
  have hox := hO o.x (by simp [jacCoords])
  have hoy := hO o.y (by simp [jacCoords])
  have hoz := hO o.z (by simp [jacCoords])
  have hqx := hV q.x (by simp [jacCoords])
  have hqy := hV q.y (by simp [jacCoords])
  have hqz := hV q.z (by simp [jacCoords])
  rw [copyPt,List.append_assoc,WP.block_append_iff]
  refine WP.mono (copyField_ok hL hAl hI hox hqx) fun a ⟨ka,ia⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyField_ok hL hAl ia hoy (List.mem_cons_of_mem _ hqy)) fun b ⟨kb,ib⟩ => ?_
  refine WP.mono (copyField_ok hL hAl ib hoz
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hqz))) fun t ⟨kt,it⟩ => ?_
  refine ⟨_,(progKeep_of_op ka (by simp [jacCoords])).trans
    ((progKeep_of_op kb (by simp [jacCoords])).trans (progKeep_of_op kt (by simp [jacCoords]))),
    it.sub ?_,?_⟩
  · intro x hx
    simp only [jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  · simp only [Function.update_self,Function.update_of_ne hn.1.1,
      Function.update_of_ne hn.1.2,Function.update_of_ne hn.2.1,
      Function.update_of_ne (hqa q.y (by simp [jacCoords]) o.x (by simp [jacCoords])),
      Function.update_of_ne (hqa q.z (by simp [jacCoords]) o.x (by simp [jacCoords])),
      Function.update_of_ne (hqa q.z (by simp [jacCoords]) o.y (by simp [jacCoords]))]

theorem ProgKeep.invJ {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} {s t : State} {W : List Nat} (hL : Lay M size Sl) (hs : Scr s base size)
    (hk : ProgKeep M base W s t) (hW : ∀ x∈W, Sl x) {p : Pt}
    (hp : ∀ x∈jacCoords p, Sl x) (hDisj : ∀ x∈jacCoords p, x∉W) {P : Point C}
    (hJ : InvJ C (tmv C M.n base s p.x) (tmv C M.n base s p.y) (tmv C M.n base s p.z) P) :
    InvJ C (tmv C M.n base t p.x) (tmv C M.n base t p.y) (tmv C M.n base t p.z) P := by
  have eqv (x : Nat) (hx : x∈jacCoords p) : tmv C M.n base t x=tmv C M.n base s x := by
    unfold tmv; rw [hk.slot hL hs hW (hp x hx) (hDisj x hx)]
  rw [eqv _ (by simp [jacCoords]),eqv _ (by simp [jacCoords]),eqv _ (by simp [jacCoords])]
  exact hJ

end VG.Proof.Weierstrass.AArch64

end
