module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.Payload
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.Timing
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
open VG.Impl.AesGcm.RISCV64.Contiguous (masks maskTag)
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_taint rel_seq)
open VG.Spec.Gcm (Block blockAt)

private theorem rel_env {V : Reg → BitVec 64} {sp : Addr} {s t : State} {p : Prog isa}
    (a : Env V sp s) (b : Env V sp t) (rs : List Reg) (hr : ∀ r ∈ rs, r ∈ frozen)
    {hint : VG.Taint.Hint taint.T} (cert : (taint.check (Taint.ofRegs rs) p hint).isSome=true) :
    RelCT isa (Eq2 s t) p TT := rel_taint rs (a.sp.trans b.sp.symm) (fun r h => (a.fr r (hr r h)).trans (b.fr r (hr r h)).symm) cert

private theorem lens_env [VG.Proof.Gcm.RISCV64.GhashLaw] {V : Reg → BitVec 64} {sp : Addr} {s : State}
    (L : Lay (V .s2) (V .s1) (V .s0)) (he : Env V sp s) :
    WP isa (.seq (.block [mov .s4 .s10,mov .s6 .s11]) (lens 16)) s (Env V sp) := by
  apply WP.seq
  refine Steps.wp_mv fun v a => Steps.wp_mv fun u b => WP.block_nil ?_
  have eu := he.keep (fun r hr => (b.other r (by revert r;decide)).trans (a.other r (by revert r;decide)))
    (b.sp.trans a.sp) (b.rd.trans a.rd) (b.wr.trans a.wr)
  exact WP.mono (lens_ok L (.inr rfl) eu rfl) fun _ h => h.1

theorem maskTag_rel [VG.Proof.Gcm.RISCV64.GhashLaw] {V : Reg → BitVec 64} {sp : Addr} {s t : State}
    (L : Lay (V .s2) (V .s1) (V .s0)) (a : Env V sp s) (b : Env V sp t) :
    RelCT isa (Eq2 s t) maskTag TT := by
  unfold maskTag
  apply RelCT.assoc
  refine rel_seq (rel_env a b [.s0,.s1,.s2,.s10,.s11] (by decide) (by taint_decide))
    (lens_env L a) (lens_env L b) fun _ _ x y => ?_
  exact rel_env x y [.s0,.s1] (by decide) (by taint_decide)

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

end VG.Proof.AesGcm.RISCV64.Contiguous
