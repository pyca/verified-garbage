module
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Piece
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CryptOk
import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
meta import VerifiedGarbage.Impl.AesGcm.X86_64.DirectGather
meta import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Whole
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-! Public pointer and length progress through an unaligned fragment and the out-of-place counter call. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Impl.AesGcm.X86_64.DirectGather
open VG.Proof.ChaCha20Poly1305.X86_64.Gather (Eq2 TT rel_seq rel_ite rel_skip rel_regs)
open VG.Proof.Gcm (Ctr)
open VG.Spec.Gcm (Block)
variable {Ctx St W SP Q D : Addr} {R n P : Nat} {s t : State}

private theorem suffix_rel (a : PieceInput Ctx St W SP R Q D n s) (b : PieceInput Ctx St W SP R Q D n t)
    (off : s.gpr .rsi = t.gpr .rsi) : RelCT isa (Eq2 s t) suffix TT := by
  apply rel_regs [.rsi, .rbx, .rbp, .r12, .r14] _ ⟨_, by taint_decide⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [off, a.rbx.trans b.rbx.symm, a.rbp.trans b.rbp.symm, a.r12.trans b.r12.symm,
    a.env.r14.trans b.env.r14.symm]

private theorem whole_rel (c : Proof.Aes.X86_64.Ctr32ToImpl) (L : Lay Ctx St W SP)
    (a : PieceInput Ctx St W SP R Q D n s) (b : PieceInput Ctx St W SP R Q D n t) :
    RelCT isa (Eq2 s t) (whole ⟨c.callee.name,c.callee.code⟩) TT := by
  apply rel_seq (rel_regs [.rbp] (fun _ hr => List.mem_singleton.mp hr ▸ a.rbp.trans b.rbp.symm)
    ⟨_, by taint_decide⟩) (whole_test a) (whole_test b)
  intro u v x y
  refine rel_ite (b := decide (n/16 = 0)) x.zero y.zero (fun _ => rel_skip) fun _ => ?_
  apply rel_seq (rel_regs [.r15] (fun _ hr => List.mem_singleton.mp hr ▸ x.input.env.r15.trans y.input.env.r15.symm)
    ⟨_, by taint_decide⟩) (whole_args L x.input x.nb) (whole_args L y.input y.nb)
  intro i j h k
  apply ctrTo_rel c
  rintro _ _ ⟨rfl, rfl⟩
  exact ⟨_, _, _, _, _, _, _, h.call, k.call, h.env.rsp.trans k.env.rsp.symm⟩

theorem piece_rel (v : GcmImpl) (c : Proof.Aes.X86_64.Ctr32ToImpl) (L : Lay Ctx St W SP)
    (a : PieceInput Ctx St W SP R Q D n s) (b : PieceInput Ctx St W SP R Q D n t)
    (os : s.gpr .rsi=BitVec.ofNat 64 (P%16)) (ot : t.gpr .rsi=BitVec.ofNat 64 (P%16)) (hn : 0<n)
    {cs ct : Block} (cs0 : Ctr s.mem (St+48#64) (St+64#64) (ciphOf s.mem Ctx R) cs P)
    (ct0 : Ctr t.mem (St+48#64) (St+64#64) (ciphOf t.mem Ctx R) ct P) :
    RelCT isa (Eq2 s t) (.seq suffix (.seq (whole ⟨c.callee.name,c.callee.code⟩) (cryptTailG v.callees true))) TT := by
  let k := suffixLen P n
  let m := n - k
  let j := 16 * (m / 16)
  have kn : k ≤ n := by dsimp [k,suffixLen]; split <;> omega
  have jm : j ≤ m := by dsimp [j]; omega
  have al : m=0 ∨ (P+k)%16=0 := by dsimp [m,k,suffixLen]; split <;> omega
  have finish : m-j=0 ∨ ((P+k)+j)%16=0 := by dsimp [j]; omega
  apply rel_seq (suffix_rel a b (os.trans ot.symm)) (WP.with_rdwr (suffix_ok a os hn cs0))
    (WP.with_rdwr (suffix_ok b ot hn ct0))
  rintro x y ⟨sa,ra,wa⟩ ⟨sb,rb,wb⟩
  have px := sa.head.drop a kn ra wa sa.src sa.dst sa.left
  have py := sb.head.drop b kn rb wb sb.src sb.dst sb.left
  have cx := sa.head.ctr
  have cy := sb.head.ctr
  rw [← ciph_frame sa.head.frame (ctx_crFrame L (a.dst.take kn)) a.rounds.2] at cx
  rw [← ciph_frame sb.head.frame (ctx_crFrame L (b.dst.take kn)) b.rounds.2] at cy
  apply rel_seq (whole_rel c L px py) (WP.with_rdwr (whole_ok c L px al cx)) (WP.with_rdwr (whole_ok c L py al cy))
  rintro u z ⟨ua,ru,wu⟩ ⟨zb,rz,wz⟩
  have pu := ua.head.drop px jm ru wu ua.src ua.dst ua.left
  have pz := zb.head.drop py jm rz wz zb.src zb.dst zb.left
  rintro _ _ tr tr' a' b' ⟨rfl,rfl⟩ ea eb
  exact ⟨tail_rel v L pu pz finish tr a' ea tr' b' eb, trivial⟩

end VG.Proof.AesGcm.X86_64.DirectGather
