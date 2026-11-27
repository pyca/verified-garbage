module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.PreparedTiming
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.AesGcm.RISCV64

/-! # Constant-time absorption and padding with the prepared GHASH table -/

public section
namespace VG.Proof.AesGcm.RISCV64
open VG VG.RISCV64 VG.Impl.Gcm.RISCV64.Prepared
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_seq rel_taint)

open VG.Impl.AesGcm.RISCV64
open VG.Spec.Gcm (blockAt)
open VG.Proof.Gather.RISCV64 (rel_ite)

abbrev padRange (w : Addr) : List Region := [⟨w+BitVec.ofNat 64 96,16⟩]

theorem preparedFlush_rel {K bk c st w sp : Addr} {s t : State} {yo q : Nat}
    (lay : Lay c st w) (y : yo=0 ∨ yo=16) (hq : q<16)
    (v : EnvC c st w sp s) (h : EnvC c st w sp t)
    (u : s.gpr .s6=BitVec.ofNat 64 q) (z : t.gpr .s6=BitVec.ofNat 64 q)
    (a : HashScope K bk (padRange w) s) (b : HashScope K bk (padRange w) t) :
    RelCT isa (Eq2 s t) (flushWith preparedInvocation yo) TT := by
  refine rel_ite (eval_zero u (by omega_arith)) (eval_zero z (by omega_arith))
    (fun _ => preparedSkip_rel) fun hq' => ?_
  have hn : q≠0 := by simpa using hq'
  have pins : ∀ k∈[Reg.s6,.s1,.s0],s.gpr k=t.gpr k := by
    intro k hk;rcases List.mem_cons.mp hk with rfl|hs
    · exact u.trans z.symm
    · exact v.pin h (by simpa using Or.inr hs)
  obtain ⟨V,vc,vs,vw,ve⟩ := v
  obtain ⟨W,wc,ws,ww,we⟩ := h
  refine rel_seq (rel_taint [.s6,.s1,.s0] (ve.sp.trans we.sp.symm) pins (by taint_decide))
    (WP.with_rdwr (flushCopy_ok (lay.v vc vs vw) y ⟨ve,rfl⟩ u hq hn))
    (WP.with_rdwr (flushCopy_ok (lay.v wc ws ww) y ⟨we,rfl⟩ z hq hn))
    fun i j ⟨iv,ird,iwr,isp⟩ ⟨jv,jrd,jwr,jsp⟩ => ?_
  refine preparedOne_rel y (.inr ⟨rfl,rfl⟩) (ghIn_T ⟨V,vc,vs,vw,iv.env⟩)
    (ghIn_T ⟨W,wc,ws,ww,jv.env⟩) (a.after ⟨ird,iwr,isp⟩ ?_) (b.after ⟨jrd,jwr,jsp⟩ ?_)
  · simpa only [vw] using iv.frame
  · simpa only [ww] using jv.frame

private theorem lensFields {c st w sp : Addr} {s : State} (e : EnvC c st w sp s) :
    WP isa (.block VG.Impl.AesGcm.RISCV64.lensBlock) s fun t => EnvC c st w sp t ∧
      Keeps' s t ∧ Frame (padRange w) s.mem t.mem := by
  obtain ⟨V,vc,vs,vw,h⟩ := e
  refine WP.mono (lensStore_ok h) fun t ⟨mem,regs,keep⟩ => ?_
  have env := h.keep (fun r hr => regs r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide)) keep.sp keep.rd keep.wr
  refine ⟨⟨V,vc,vs,vw,env⟩,keep,?_⟩
  have eq := VG.WriteBytes.writeBytes_append s.mem (V .s0+BitVec.ofNat 64 96)
    (ByteLoad.beBytes 8 (s.gpr .s4 <<< 3)) (ByteLoad.beBytes 8 (s.gpr .s6 <<< 3)) (by simp [ByteLoad.beBytes_length])
  rw [ByteLoad.beBytes_length,add_ofNat_assoc] at eq
  rw [eq,vw] at mem
  rw [mem]; exact writeBytes_frame' _ (by simp [ByteLoad.beBytes_length])

theorem preparedLens_rel {K bk c st w sp : Addr} {s t : State} {yo : Nat}
    (y : yo=0 ∨ yo=16) (v : EnvC c st w sp s) (h : EnvC c st w sp t)
    (a : HashScope K bk (padRange w) s) (b : HashScope K bk (padRange w) t) :
    RelCT isa (Eq2 s t) (lensWith preparedInvocation yo) TT := by
  refine rel_seq (rel_taint [.s0] (v.sp.trans h.sp.symm) (fun r hr => v.pin h (by simpa using Or.inr (Or.inr (List.mem_singleton.mp hr)) )) (by taint_decide))
    (lensFields v) (lensFields h) fun i j ⟨ie,ik,ifr⟩ ⟨je,jk,jfr⟩ => ?_
  exact preparedOne_rel y (.inr ⟨rfl,rfl⟩) (ghIn_T ie) (ghIn_T je) (a.after ik ifr) (b.after jk jfr)

end VG.Proof.AesGcm.RISCV64
