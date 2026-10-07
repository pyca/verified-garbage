import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointPrep
import VerifiedGarbage.Proof.Weierstrass.AArch64.ArithmeticTable
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTable

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 Spec.Weierstrass

structure JointTablePost (base : Addr) (g : Reg → BitVec 64) (P : Point p256.C) (u v : Nat)
    (s t : State) : Prop where
  table : NafTableInv P256Joint.cfg.K p256.C base size P s t 8
  field : Inv P256Joint.cfg.K.M base size p256.C.p (·∈jointSlots P256Joint.cfg)
    (nafLive P256Joint.cfg.K) (tmv p256.C 4 base t) t
  stable : NafStable P256Joint.cfg.K p256.C base P (FastNaf.byte 5 v) t
  generator : ∀ j<257,t.mem (off base (P256Joint.cfg.gBits+j))=FastNaf.byte 7 u j
  one : tmv p256.C 4 base t P256Joint.cfg.onep=1
  fixed : Fixed p256 base g t.mem
  syms : t.syms=s.syms

theorem jointTableStage_ok (certs : Forward.Arithmetic.Cases) (hc : CfgOk p256) (hC : Law p256.C)
    {base : Addr} {g : Reg → BitVec 64} {P : Point p256.C} (hP : onCurve p256.C P=true)
    {s₀ s : State} (h : JointPrepPost base g P s₀ s) :
    WP isa (ArithmeticTable.table P256Joint.cfg.K) s
      (JointTablePost base g P (sv p256 base s₀ U) (sv p256 base s₀ V) s) := by
  have hL := jacLay hc rfl
  refine WP.mono_syms (arithmeticTable_ok certs hL rfl (jacAligned p256 rfl)
    (unitMod_pow_two hc.p_odd _) (by decide) hC hc.am3 (by decide) (by change 2^(64*4)%p256.C.p<p256.C.p; exact Nat.mod_lt _ (by have := hc.p_ge; omega))
    hP h.field h.peer.2.2) fun t ht sy => ?_
  obtain ⟨hi,hstable⟩ := ht.ready hL h.peer.1 h.peer.2.1
  have F := h.fixed.unch hc.n10 h.field.scr.nowrap (W:=jacTreeWrites P256Joint.cfg.K)
    (by unfold FixedOk; decide +kernel) ht.unch
  have hone : tmv p256.C 4 base t P256Joint.cfg.onep=1 := by
    change toM _ _ (wordsVal t.mem base P256Joint.cfg.onep 4)=1
    have he := jacTree_ro_words hL ht.unch ht.field.scr.nowrap (x:=P256Joint.cfg.onep) (by decide +kernel)
    change wordsVal t.mem base P256Joint.cfg.onep 4=wordsVal s.mem base P256Joint.cfg.onep 4 at he
    rw [he]
    exact h.one
  refine ⟨ht,⟨hi.scr,hi.mod,?_,hi.lt,hi.val⟩,hstable,?_,hone,F,sy⟩
  · intro x hx
    exact List.mem_append_left _ (List.mem_append_left _ (hi.sl x hx))
  · intro j hj
    rw [ht.unch.byte (fun w hw => ?_) (by change 1504+j<2^64; omega),h.generator j hj]
    have ha : ∀ w∈jacTreeWrites P256Joint.cfg.K,
        1768≤w.1 ∨ w.1+w.2≤1504 := by decide +kernel
    have hw' := ha w hw
    change 1504+j<w.1 ∨ w.1+w.2≤1504+j
    omega

end VG.Proof.Ecdsa.Verify.AArch64
