module
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Finish
public import VerifiedGarbage.Impl.AesGcm.X86_64.Contiguous
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Impl.AesGcm.X86_64.Contiguous

/-! Finish a contiguous payload from the original source buffer. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.ContiguousSeal
open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)
open VG.WriteBytes

theorem tailPtr_ok {Ctx W SP S : Addr} {n r : Nat} {s : State}
    (env : Env Ctx (W+16#64) W SP s) (slot : InRegions (s.rd++s.wr) (SP+8#64) 8)
    (src : s.mem.readW (SP+8#64) 64=S)
    (total : s.mem.readW (W+192#64) 64=BitVec.ofNat 64 n) (len : s.mem.readW (W+208#64) 64=BitVec.ofNat 64 r)
    (le : r≤n) :
    ∃ t, runBlock isa (Contiguous.regs .rbx) s = some t ∧ t.gpr .rbx=S+BitVec.ofNat 64 (n-r) ∧
      (∀ z, z≠.rbx → t.gpr z=s.gpr z) ∧ t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.xmm=s.xmm := by
  have rt := env.perm.wR (show 192+8≤2560 by decide)
  have rr := env.perm.wR (show 208+8≤2560 by decide)
  have ptr : S+BitVec.ofNat 64 n-BitVec.ofNat 64 r = S+BitVec.ofNat 64 (n-r) := by
    rw [← Offset.ofNat_sub_ofNat le, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  unfold Contiguous.regs
  refine ⟨_,by xrun [Contiguous.src,env.rsp,env.r15,slot,src,total,len,rt,rr],?_,?_,?_,?_,?_,?_⟩
  · simpa only [gpr_setReg_self] using ptr
  · intro z nz; simp [gpr_setReg,nz]
  all_goals rfl

theorem vecArgs_ok {Ctx W SP S D : Addr} {n r : Nat} {s : State}
    (env : Env Ctx (W+16#64) W SP s) (dat : s.mem.readW (W+200#64) 64=D)
    (tlen : s.mem.readW (W+192#64) 64=BitVec.ofNat 64 n) (len : s.mem.readW (W+208#64) 64=BitVec.ofNat 64 r)
    (le : r≤n) (slot : InRegions (s.rd++s.wr) (SP+8#64) 8) (src : s.mem.readW (SP+8#64) 64=S)
    (slots : (⟨SP+8#64,8⟩ : Region).Disjoint ⟨W,2560⟩) :
    ∃ t, runBlock isa (Impl.AesGcm.X86_64.Short.finTextArgs ++ Contiguous.regs .rbx) s=some t ∧
      t.mem = writeBytes s.mem (W+512#64) (List.replicate 16 0) ∧
      t.gpr .rdi=W+512#64 ∧ t.gpr .rsi=D ∧ t.gpr .rdx=W+1040#64 ∧ t.gpr .rcx=BitVec.ofNat 64 r ∧
      t.gpr .rbx=S+BitVec.ofNat 64 (n-r) ∧ (∀ z ∈ [Reg.rsp,.r13,.r14,.r15], t.gpr z=s.gpr z) ∧
      t.rd=s.rd ∧ t.wr=s.wr ∧ ∀ x, x≠.xmm7 → t.xmm x=s.xmm x := by
  obtain ⟨u,run,mu,di,si,dx,cx,gu,ru,wu,xu⟩ := Short.finTextArgs_ok s env dat len
  have keep (z) (hz : z ∈ [Reg.r13,.r14,.r15,.rsp]) : u.gpr z=s.gpr z := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl <;> exact gu _ (by decide) (by decide) (by decide) (by decide)
  have frame : Frame [⟨W+512#64,16⟩] s.mem u.mem := by
    rw [mu]; exact writeBytes_frame' _ (List.length_replicate ..)
  have memslot : u.mem.readW (SP+8#64) 64=S := by
    rw [frame.readW (Region.contains_self _ _) (fun b hb => by
      obtain rfl := List.mem_singleton.mp hb; exact slots.sub_right (Lay.wSub (by decide))) (by decide), src]
  have memw (i : Nat) (hi : i+8≤512) :
      u.mem.readW (W+BitVec.ofNat 64 i) 64=s.mem.readW (W+BitVec.ofNat 64 i) 64 := by
    apply frame.readW (Region.contains_self _ _) _ (by decide)
    intro b hb; obtain rfl := List.mem_singleton.mp hb
    exact Offset.disjoint W (.inl hi) (by omega_using [hi]) (by decide)
  obtain ⟨v,run',reg,gv,mv,rv,wv,xv⟩ := tailPtr_ok (env.keep keep ru wu)
    (by rw [ru,wu]; exact slot) memslot ((memw 192 (by decide)).trans tlen) ((memw 208 (by decide)).trans len) le
  refine ⟨v,by rw [runBlock_append,run]; exact run',mv.trans mu,(gv _ (by decide)).trans di,
    (gv _ (by decide)).trans si,(gv _ (by decide)).trans dx,(gv _ (by decide)).trans cx,reg,?_,
    rv.trans ru,wv.trans wu,fun q neq => by rw [xv,xu q neq]⟩
  intro z hz
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl <;> exact (gv _ (by decide)).trans (keep _ (by decide))

theorem vecTail_ok {Ctx W SP S D : Addr} {H : Block} {al n r : Nat} {s : State}
    (P : Short.FinPre Ctx W SP H al n r D s) (le : r≤n)
    (slot : InRegions (s.rd++s.wr) (SP+8#64) 8) (src : s.mem.readW (SP+8#64) 64=S)
    (slots : (⟨SP+8#64,8⟩ : Region).Disjoint ⟨W,2560⟩)
    (read : Covers [⟨S+BitVec.ofNat 64 (n-r),r⟩] (s.rd++s.wr))
    (alias : S+BitVec.ofNat 64 (n-r)=D ∨ (⟨S+BitVec.ofNat 64 (n-r),r⟩ : Region).Disjoint ⟨D,r⟩)
    (apart : (⟨S+BitVec.ofNat 64 (n-r),r⟩ : Region).Disjoint ⟨W,2560⟩) :
    WP isa (.seq (.block (Impl.AesGcm.X86_64.Short.finTextArgs ++ Contiguous.regs .rbx))
      (.seq (Impl.AesGcm.X86_64.Short.xorText true .rbx)
      (.block (Impl.AesGcm.X86_64.Short.finLens ++ Impl.AesGcm.X86_64.Short.finGh2 ++ Impl.AesGcm.X86_64.Short.tagK 0)))) s fun t =>
      Env Ctx (W+16#64) W SP t ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ Frame [⟨W,16⟩,⟨W+512#64,32⟩,⟨D,r⟩] s.mem t.mem ∧
      bytesAt t.mem D r = Short.xb s.mem (S+BitVec.ofNat 64 (n-r)) (W+1040#64) r ∧
      blockAt t.mem W = Spec.Gcm.ghashFrom H (blockAt s.mem (yA W))
        [Spec.Gcm.ofBytes (Short.xb s.mem (S+BitVec.ofNat 64 (n-r)) (W+1040#64) r ++ Spec.Gcm.zeros (16-r)),
         Spec.Gcm.ofBytes (Proof.Gcm.lensBlock al n)] ^^^ blockAt s.mem (W+1024#64) := by
  exact Short.finTailFrom_ok _ .rbx P (by decide) (vecArgs_ok P.env P.dat P.tlen P.len le slot src slots) read alias apart

end VG.Proof.AesGcm.X86_64.ContiguousSeal
