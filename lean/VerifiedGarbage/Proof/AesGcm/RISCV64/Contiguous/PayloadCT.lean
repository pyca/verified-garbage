module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.Payload
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.Timing
import VerifiedGarbage.Proof.AesGcm.RISCV64.CryptOk
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTAbsorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.AesGcm.RISCV64.Contiguous
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.MaskPayload
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal

/-! # Timing of the shared RISC-V seal payload -/

public section
namespace VG.Proof.AesGcm.RISCV64.Contiguous
open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Impl.AesGcm.RISCV64.Contiguous (masks)
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_taint rel_seq)
open VG.Spec.Gcm (Block blockAt)

theorem maskData_rel {V : Reg → BitVec 64} {sp X D : Addr} {R : Nat} {ha hb : Block} {a b : List Byte} {s t : State}
    (L : Lay (V .s2) (V .s1) (V .s0)) (p : PayloadIn V sp X D R ha a s) (q : PayloadIn V sp X D R hb b t)
    (small : (V .s11).toNat≤240) : RelCT isa (Eq2 s t) (.seq masks shortXor) TT := by
  have prep {v : State} {H : Block} {aad : List Byte} (h : PayloadIn V sp X D R H aad v) :=
    masks_wp L h.env (n := (V .s11).toNat) (by simpa using h.len) small h.roundsReg h.rounds h.keys
  obtain ⟨_,cert⟩ : ∃ h, (taint.check (Taint.ofRegs [.s0,.s4,.s5,.s8]) shortXor h).isSome = true := ⟨_,by taint_decide⟩
  refine rel_seq (rel_taint [.s0,.s1,.s3,.s5,.s7] (p.env.sp.trans q.env.sp.symm) ?_ (by taint_decide)) (prep p) (prep q)
    fun u v ⟨eu,gu,_,_,_⟩ ⟨ev,gv,_,_,_⟩ => rel_taint [.s0,.s4,.s5,.s8] (eu.sp.trans ev.sp.symm) ?_ cert
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact p.env.s0.trans q.env.s0.symm
    · exact p.env.s1.trans q.env.s1.symm
    · exact p.env.s3.trans q.env.s3.symm
    · exact p.len.trans q.len.symm
    · exact (p.env.fr _ (by decide)).trans (q.env.fr _ (by decide)).symm
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact eu.s0.trans ev.s0.symm
    · rw [gu _ (by decide),gv _ (by decide),p.src,q.src]
    · rw [gu _ (by decide),gv _ (by decide),p.len,q.len]
    · rw [gu _ (by decide),gv _ (by decide),p.dst,q.dst]

theorem longCtr_ct {c st w sp X D kb : Addr} {R n : Nat} (L : Lay c st w) :
    CT (CrMB true true kb c st w sp R X D n 0 0) (.seq (cryptWholeB true true) (cryptTailB true true)) := by
  apply CT.seq (J := CrMB true true kb c st w sp R X D n 0 (16*(n/16))) (cryptWholeB_ct L) ?_ (cryptTailB_ct L)
  intro s h
  obtain ⟨V,icb,P,m0,ctx,s1,s0,hP,mid,bk⟩ := h
  have lv := L.v ctx s1 s0
  refine WP.mono (WP.with_rdwr' (cryptWholeB_ok lv mid (mid.ciph lv) (fun h => (bk h).2))) fun t ⟨⟨j,eq,mt,_⟩,rd,wr⟩ => ?_
  have idx : j=16*(n/16) := by simpa using eq
  rw [idx] at mt
  exact ⟨V,icb,P,m0,ctx,s1,s0,hP,mt,fun h => ⟨(bk h).1,(bk h).2.of_eq rd wr⟩⟩

end VG.Proof.AesGcm.RISCV64.Contiguous
