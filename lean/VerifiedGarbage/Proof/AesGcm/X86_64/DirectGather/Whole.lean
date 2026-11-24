module
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Fragment
public import VerifiedGarbage.Impl.AesGcm.X86_64.DirectGather
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.StreamTo

/-! Direct counter-mode call for the full blocks in one gather fragment. -/
@[expose] public section
set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Impl.AesGcm.X86_64.DirectGather
open VG.Spec.Gcm (Block)
open VG.Proof.Gcm (Ctr)
variable {Ctx St W SP Q D : Addr} {R n : Nat} {s : State}

theorem ctrCallArgs {offset : Nat} (fits : 96 ≤ offset ∧ offset+2048 ≤ 2560) (L : Lay Ctx St W SP) (e : Env Ctx St W SP s)
    (q : DataOk St W SP s Q (16*n)) (d : DataW Ctx St W SP s D (16*n))
    (layout : Q = D ∨ (⟨Q,16*n⟩ : Region).Disjoint ⟨D,16*n⟩) (rounds : R = 10 ∨ R = 12 ∨ R = 14)
    (di : s.gpr .rdi = Ctx) (si : s.gpr .rsi = BitVec.ofNat 64 R)
    (dx : s.gpr .rdx = St+48#64) (cx : s.gpr .rcx = Q) (o : s.gpr .r11 = D)
    (nb : s.gpr .r8 = BitVec.ofNat 64 n) (scr : s.gpr .r9 = W+BitVec.ofNat 64 offset) :
    CtrToCall s Ctx (St+48#64) Q D (W+BitVec.ofNat 64 offset) R n := by
  have ks : Region.Sub ⟨Ctx,240⟩ ⟨Ctx,256⟩ := Region.sub_prefix (by decide)
  have cs : Region.Sub ⟨St+48#64,16⟩ ⟨St,80⟩ := Lay.stSub (by decide)
  have ws : Region.Sub ⟨W+BitVec.ofNat 64 offset,2048⟩ ⟨W,2560⟩ := Lay.wSub fits.2
  refine ⟨di, si, dx, cx, nb, scr, o, rounds, q.wrap, d.ok.wrap, (L.cs.sub_left ks).sub_right cs,
    d.ctx.sub_left ks, (L.cw'.sub_left ks).sub_right ws, (q.st.sub_right cs).symm,
    (d.ok.st.sub_right cs).symm, L.st_w (by decide) (.inr fits), layout,
    q.w.sub_right ws, d.ok.w.sub_right ws, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e.rsp]; exact L.kc.sub_right ks
  · rw [e.rsp]; exact L.ks.sub_right cs
  · rw [e.rsp]; exact q.stk
  · rw [e.rsp]; exact d.ok.stk
  · rw [e.rsp]; exact L.kw.sub_right ws
  · refine covers_cons ?_ (covers_cons q.rd (covers_cons (covers_left (e.perm.stC (by decide)))
      (covers_cons (covers_left d.wr) (covers_left (e.perm.wC fits.2)))))
    exact fun a m ⟨_, hr, hc⟩ => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact e.perm.ctx a m ⟨_, List.mem_singleton_self _, by
        simp only [Region.Contains] at hc ⊢; omega⟩
  · exact covers_cons (e.perm.stC (by decide)) (covers_cons d.wr (e.perm.wC fits.2))

abbrev wholeArgs : List Instr :=
  ([.mov .rcx (.reg .rbx),.mov .r11 (.reg .r12),.mov .rax (.reg .rbp),.alu .and .rbp (imm 15),
    .alu .sub .rax (.reg .rbp),.alu .add .rbx (.reg .rax),.alu .add .r12 (.reg .rax),
    .mov .rdi (.reg .r13),load .rsi roundsO] : List Instr) ++ ptr .rdx .r14 48 ++ ptr .r9 .r15 scrO

structure ArgsOut (Ctx St W SP Q D : Addr) (R n : Nat) (s t : State) : Prop where
  env : Env Ctx St W SP t
  src : t.gpr .rbx = Q + BitVec.ofNat 64 (16*(n/16))
  dst : t.gpr .r12 = D + BitVec.ofNat 64 (16*(n/16))
  left : t.gpr .rbp = BitVec.ofNat 64 (n%16)
  call : CtrToCall t Ctx (St+48#64) Q D (W+512#64) R (n/16)
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem whole_args (L : Lay Ctx St W SP) (p : PieceInput Ctx St W SP R Q D n s)
    (nb : s.gpr .r8 = BitVec.ofNat 64 (n/16)) :
    WP isa (.block wholeArgs) s (ArgsOut Ctx St W SP Q D R n s) := by
  have hn := p.src.lt
  have hh := p.env.perm.wR (show 176+8≤2560 by decide)
  have mask := and15 (BitVec.ofNat 64 n)
  rw [toNat_ofNat_of_lt hn] at mask
  change BitVec.ofNat 64 n &&& 15#64 = BitVec.ofNat 64 (n%16) at mask
  have span : BitVec.ofNat 64 n - BitVec.ofNat 64 (n%16) = BitVec.ofNat 64 (16*(n/16)) := by
    rw [ofNat_sub (by omega) hn]; congr 1; omega
  have bound : 16*(n/16) ≤ n := by omega
  have pre : Region.Sub ⟨Q,16*(n/16)⟩ ⟨Q,n⟩ := Region.sub_prefix bound
  have e := p.env
  have h13 := e.r13
  have h14 := e.r14
  have h15 := e.r15
  have rr := p.rounds.1
  have bx := p.rbx
  have bp := p.rbp
  have d := p.r12
  unfold wholeArgs load ptr
  apply WP.of_runBlock
  refine ⟨_, by xrun [h15, hh, rr], ?_⟩
  generalize ht : (State.setReg _ .r9 (W+512#64)) = t
  have env' : Env Ctx St W SP t := by
    subst t
    exact e.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]) rfl rfl
  subst t
  refine ⟨env', ?_, ?_, ?_, ctrCallArgs (offset:=512) (by decide) L env' ((p.src.take bound).of_eq rfl rfl)
    ((p.dst.take bound).of_eq rfl rfl) (.inr ((p.apart.sub_left pre).sub_right (Region.sub_prefix bound))) p.rounds.2
    ?_ ?_ ?_ ?_ ?_ ?_ ?_, rfl, rfl, rfl⟩
  all_goals simp [gpr_setReg, gpr_arithFlags, bp, bx, d, h13, h14, h15, rr, mask, span, nb]

abbrev wholeTest : List Instr :=
  [.mov .r8 (.reg .rbp),.shift .shr .r8 4,.alu .test .r8 (.reg .r8)]

structure Tested (Ctx St W SP Q D : Addr) (R n : Nat) (s t : State) : Prop where
  input : PieceInput Ctx St W SP R Q D n t
  nb : t.gpr .r8 = BitVec.ofNat 64 (n/16)
  zero : t.zf = some (decide (n/16=0))
  mem : t.mem=s.mem
  rd : t.rd=s.rd
  wr : t.wr=s.wr

theorem whole_test (p : PieceInput Ctx St W SP R Q D n s) :
    WP isa (.block wholeTest) s (Tested Ctx St W SP Q D R n s) := by
  have h := p.src.lt
  have bp := p.rbp
  have shift := shr4 n h
  have zero := and_self_beq (a := n/16) (by omega)
  apply WP.of_runBlock
  refine ⟨_, by unfold wholeTest; xrun [bp, shift], ?_⟩
  refine ⟨⟨p.env.keep (fun r hr => ?_) rfl rfl, p.rounds, p.src.of_eq rfl rfl,
    p.dst.of_eq rfl rfl, p.apart, ?_, ?_, ?_⟩, ?_, ?_, rfl, rfl, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setFlags,gpr_arithFlags,gpr_setReg]
  · simpa [gpr_setFlags,gpr_arithFlags,gpr_setReg] using p.rbx
  · simpa [gpr_setFlags,gpr_arithFlags,gpr_setReg] using p.r12
  · simpa [gpr_setFlags,gpr_arithFlags,gpr_setReg] using p.rbp
  · simp [gpr_setFlags,gpr_arithFlags,gpr_setReg]
  · simp only [zf_arithFlags,zero]

theorem whole_ok (v : Proof.Aes.X86_64.Ctr32ToImpl) (L : Lay Ctx St W SP)
    (p : PieceInput Ctx St W SP R Q D n s) {icb : Block} {P : Nat}
    (align : n=0 ∨ P%16=0) (ctr : Ctr s.mem (St+48#64) (St+64#64) (ciphOf s.mem Ctx R) icb P) :
    WP isa (whole ⟨v.callee.name,v.callee.code⟩) s (SpanOutput Ctx St W SP Q D R n (16*(n/16)) P icb s) := by
  refine WP.seq ((whole_test p).mono fun t ht => ?_)
  refine WP.ite (decide (n/16=0)) (show isa.eval .e t = _ from ht.zero) (fun hz => ?_) (fun hz => ?_)
  · have z : n/16=0 := by simpa using hz
    refine WP.block_nil ⟨⟨ht.input.env, ht.input.rounds, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · simpa [z,ht.mem] using ctr
    · simp [z,Spec.Aes.bytesAt,Gcm.xorKs]
    · rw [ht.mem]; exact Frame.refl _ _
    · simpa [z] using ht.input.rbx
    · simpa [z] using ht.input.r12
    · simpa [z] using ht.input.rbp
  · have nz : n/16≠0 := by simpa using hz
    have alp := align.resolve_left (by omega)
    refine WP.seq ((whole_args L ht.input ht.nb).mono fun u a => ?_)
    refine (ctrTo_call v a.call).mono fun t' b => ?_
    have mem := a.mem.trans ht.mem
    have env := a.env.of_saved b.saved b.rd b.wr
    have out := b.out
    have counter := b.ctr
    rw [mem] at out counter
    have both := Gcm.ctr_wholeTo ctr alp out counter
    have frame := b.frame
    rw [a.env.rsp,mem] at frame
    have d := p.dst.take (k:=16*(n/16)) (by omega)
    refine ⟨⟨env, rounds_frame frame (fun r hr => ?_) p.rounds, both.2, both.1,
      frame.sub (fun r hr => ?_)⟩, ?_, ?_, ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (L.st_w (by decide) (.inr ⟨by decide,by decide⟩)).symm
      · exact (d.ok.w.sub_right (Lay.wSub (by decide))).symm
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w (by decide)).symm
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_,List.mem_cons_of_mem _ (List.mem_cons_self ..),Region.sub_prefix (by decide)⟩
      · exact ⟨_,List.mem_cons_self ..,fun _ h => h⟩
      · exact ⟨_,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),fun _ h => h⟩
      · exact ⟨_,by simp,fun _ h => h⟩
    · rw [b.saved _ (by decide),a.src]
    · rw [b.saved _ (by decide),a.dst]
    · rw [b.saved _ (by decide),a.left]; congr 1; omega

end VG.Proof.AesGcm.X86_64.DirectGather
