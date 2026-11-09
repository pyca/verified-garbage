module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowData
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowFiveDoubles
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowCopy
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowLookupCode
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowMixedStep
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.P521Native

 theorem window_block142_source : outerBlock142=windowCopy++windowLookupCode++windowMixedArgs := by
  rw [←window_copy_source,←window_lookup_source,←window_mixed_args_source,←List.take_add,List.take_append_drop]

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Impl.Weierstrass.AArch64.P521Native

 def windowIteration : Prog isa := .seq (.block outerBlock137) (.seq windowFiveDoubles windowAddPhase)

 structure WindowStepPublic (s t : State) : Prop where
  base : t.gpr .x0=s.gpr .x0
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp
  gp : ∀r∈fieldPublicRegs,r≠.x30 → r≠.x19 → t.gpr r=s.gpr r
  v29 : t.v .v29=s.v .v29
  v31 : t.v .v31=s.v .v31

 theorem window_iteration_ok {s : State} {base table : Addr} {k j : Nat}
    (data : WindowData base table k s) (hj : j<105)
    (apart : Region.Disjoint ⟨base,8192⟩ ⟨table,3456⟩)
    (bound : canonicalPoint s.mem base 1072)
    (counter : s.gpr .x19=BitVec.ofNat 64 (j+1)) :
    WP isa windowIteration s fun t =>
      canonicalPoint t.mem base 1072 ∧ ordinaryPoint t.mem base 1072=
        windowSelectF (windowDbl (windowDbl (windowDbl (windowDbl (windowDbl (ordinaryPoint s.mem base 1072))))))
          (windowAffine s.mem table k j) ∧
      WindowData base table k t ∧ WindowPhaseFrame base s.mem t.mem ∧ WindowStepPublic s t ∧
      t.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x4=BitVec.ofNat 64 j-1#64 := by
  rw [windowIteration,WP.seq_iff]
  refine WP.mono (window_counter_enter s) fun u ⟨c19,_,ku,vu⟩ => ?_
  have u0 : u.gpr .x0=base := (ku.gpr _ (by decide)).trans data.scr.x0
  have hu : Scr u (u.gpr .x0) 8192 := by rw [u0]; exact data.scr.of_keeps ku (by decide)
  have bu : canonicalPoint u.mem (u.gpr .x0) 1072 := by rw [u0,ku.mem]; exact bound
  rw [counter,window_counter_enter_value] at c19
  rw [WP.seq_iff]
  refine WP.mono (window_five_doubles_ok hu (by decide) bu (by omega_arith) c19)
    fun v ⟨bv,pv,fv,kv,v19⟩ => ?_
  rw [u0] at bv pv fv
  have frameV : WindowPhaseFrame base s.mem v.mem := by
    rw [←ku.mem]
    exact fun x hp _ ht => fv x (by omega_arith) ht
  have v0 : v.gpr .x0=s.gpr .x0 := kv.base.trans (ku.gpr _ (by decide))
  have v26 : v.gpr .x26=s.gpr .x26 := (kv.gp .x26 (by decide) (by decide) (by decide)).trans (ku.gpr _ (by decide))
  have dv : WindowData base table k v := data.of_frame apart frameV v0 v26 (kv.rd.trans ku.rd) (kv.wr.trans ku.wr)
  refine WP.mono (window_add_phase_ok dv.scr hj bv dv.readable apart dv.zero dv.canonical v19 dv.bits)
    fun t ⟨bt,pt,ht,ft,kt,t4⟩ => ?_
  have ftot : WindowPhaseFrame base s.mem t.mem := WindowPhaseFrame.trans frameV ft
  have t0 : t.gpr .x0=s.gpr .x0 := kt.base.trans v0
  have t26 : t.gpr .x26=s.gpr .x26 := (kt.gp .x26 (by decide) (by decide)).trans v26
  have dt : WindowData base table k t := data.of_frame apart ftot t0 t26
    (kt.rd.trans (kv.rd.trans ku.rd)) (kt.wr.trans (kv.wr.trans ku.wr))
  refine ⟨bt,?_,dt,ftot,?_,?_,?_⟩
  · rw [pv,ku.mem,WindowPhaseFrame.affine frameV apart k j] at pt
    exact pt
  · have fresh : ∀r∈fieldPublicRegs,r≠.x19 → r∉[Reg.x19,Reg.x2] := by decide
    exact ⟨t0,kt.rd.trans (kv.rd.trans ku.rd),kt.wr.trans (kv.wr.trans ku.wr),kt.sp.trans (kv.sp.trans ku.sp),
      fun r hr hn hc => (kt.gp r hr hn).trans ((kv.gp r
        ((by decide : ∀r∈fieldPublicRegs,r∈preserved) r hr) hn hc).trans (ku.gpr r (fresh r hr hc))),
      by rw [kt.v29,kv.v29,vu],by rw [kt.v31,kv.v31,vu]⟩
  · exact (kt.gp .x19 (by decide) (by decide)).trans v19
  · rw [v19] at t4
    exact t4

 theorem window_iteration_source {s : State} {Q : State → Prop} :
    WP isa windowIteration s Q ↔ WP isa (sequence [
      .block outerBlock137,loop24,.block outerBlock141,callNormalDouble,
      .block outerBlock142,callNormalMadd,.block outerBlock143]) s Q := by
  rw [window_block142_source]
  simp only [windowIteration,windowFiveDoubles,windowAddPhase,windowCopyLookup,windowCompleteAdd,windowMixedStep,
    sequence,List.foldr_cons,List.foldr_nil,VG.WP.seq_iff (M:=isa),VG.WP.block_append_iff (M:=isa),VG.WP.block_nil_iff (M:=isa)]

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

 def windowFiveValue (A : Fin fieldPrime×Fin fieldPrime×Fin fieldPrime) :=
  windowDbl (windowDbl (windowDbl (windowDbl (windowDbl A))))

 def windowStepValue (m : Mem) (table : Addr) (k j : Nat)
    (A : Fin fieldPrime×Fin fieldPrime×Fin fieldPrime) :=
  windowSelectF (windowFiveValue A) (windowAffine m table k j)

 def windowNonfinal (m : Mem) (table : Addr) (k : Nat) :
    Nat → (Fin fieldPrime×Fin fieldPrime×Fin fieldPrime) → (Fin fieldPrime×Fin fieldPrime×Fin fieldPrime)
  | 0,A => A
  | j+1,A => windowNonfinal m table k j (windowStepValue m table k (j+1) A)

 theorem WindowPhaseFrame.run {base table : Addr} {m m' : Mem}
    (frame : WindowPhaseFrame base m m') (apart : Region.Disjoint ⟨base,8192⟩ ⟨table,3456⟩)
    (k n : Nat) (A : Fin fieldPrime×Fin fieldPrime×Fin fieldPrime) :
    windowNonfinal m' table k n A=windowNonfinal m table k n A := by
  induction n generalizing A with
  | zero => rfl
  | succ n ih =>
    simp only [windowNonfinal,ih,windowStepValue,WindowPhaseFrame.affine frame apart k (n+1)]

 theorem WindowStepPublic.trans {s t u : State} (h : WindowStepPublic s t) (g : WindowStepPublic t u) : WindowStepPublic s u :=
  ⟨g.base.trans h.base,g.rd.trans h.rd,g.wr.trans h.wr,g.sp.trans h.sp,
    fun r hr hn hc => (g.gp r hr hn hc).trans (h.gp r hr hn hc),g.v29.trans h.v29,g.v31.trans h.v31⟩

 theorem window_counter_positive (j : Nat) (hj : 2≤j) (htop : j<105) :
    BitVec.ofNat 64 j-1#64≠0#64 := by
  rw [show 1#64=BitVec.ofNat 64 1 from rfl,BitVec.ofNat_sub_ofNat_of_le j 1 (by decide) (by omega_arith)]
  intro h
  have e := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at e
  have small : j-1<2^64 := by omega_arith
  rw [Nat.mod_eq_of_lt small] at e
  omega_arith

end VG.Proof.Weierstrass.AArch64.P521Native
