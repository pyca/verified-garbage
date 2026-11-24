module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Standalone
public import VerifiedGarbage.Proof.AesGcm.AArch64.Tag
public import VerifiedGarbage.Proof.AesGcm.AArch64.Crypt
public import VerifiedGarbage.Proof.AesGcm.AArch64.Flush
import VerifiedGarbage.Proof.AesGcm.AArch64.Absorb
import VerifiedGarbage.Proof.AesGcm.AArch64.Body
import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Standalone
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.Spec.Gcm
open VG.Impl.AesGcm.AArch64.Contiguous.Standalone
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (lensBlock)
variable {wn R : Nat} {C St W SP Tg : Addr} {s : State} {k : Reg → Addr}

abbrev argsRegs : List Reg := [.x0,.x1,.x2,.x3,.x4,.x5,.x6]

theorem tagArgs_ok (L : Lay wn C St W) (env : Env wn C St W SP s) (tag : DataW wn C St W s Tg 16)
    (hr : R=10 ∨ R=12 ∨ R=14) (rounds : s.gpr .x22 = BitVec.ofNat 64 R)
    (slot : s.mem.readW (W+BitVec.ofNat 64 tlO) 64 = Tg) :
    WP isa (.block tagArgs) s (fun t => Regs argsRegs s t ∧
      CtrToCall t C St (St+BitVec.ofNat 64 16) Tg (W+BitVec.ofNat 64 512) R 1 (wn-512)) := by
  have read := env.perm.wR (d := tlO) (n := 8) (by decide)
  change InRegions (s.rd ++ s.wr) (W+248#64) 8 at read
  apply WP.of_runBlock
  refine ⟨_,by arun [tagArgs,env.x19,read],?_⟩
  refine ⟨⟨by others_tac,rfl,rfl,rfl,rfl⟩,?_⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,hr,?_,tag.ok.wrap,by decide,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [gpr_write,env.x21]
  · simp [gpr_write,rounds]
  · simp [gpr_write,env.x20]
  · simp [gpr_write,env.x20]
  · simp [gpr_write]
  · simp [gpr_write]
  · change s.mem.read (W+248#64) 8 = Tg
    exact slot
  · rw [BitVec.toNat_add_of_lt (by have := L.sw; simp; omega)]
    simp; have := L.sw; omega
  · exact L.cs.sub_left (Region.sub_prefix (by decide)) |>.sub_right (Region.sub_prefix (by decide))
  · exact tag.ctx.sub_left (Region.sub_prefix (by decide))
  · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by have := L.hWn; omega))
  · simpa using L.st_st (a := 0) (d := 16) (by decide) (by decide) (by decide)
  · exact tag.ok.st.symm.sub_left (Region.sub_prefix (by decide))
  · simpa using L.st_wn (a := 0) (n := 16) (d := 512) (k := wn-512) (by decide) (.inr ⟨by decide,by have := L.hWn; omega⟩)
  · exact .inr (tag.ok.st.symm.sub_left (Lay.stSub (by decide)))
  · exact L.st_wn (by decide) (.inr ⟨by decide,by have := L.hWn; omega⟩)
  · exact tag.ok.w.sub_right (Lay.wSub (by have := L.hWn; omega))
  · change Covers ([⟨C,240⟩,⟨St+BitVec.ofNat 64 16,16⟩] ++ [⟨St,16⟩,⟨Tg,16⟩,⟨W+BitVec.ofNat 64 512,wn-512⟩]) (s.rd++s.wr)
    refine covers_cons ?_ (covers_cons (covers_left (env.perm.stC (by decide))) (covers_cons ?_
      (covers_cons (covers_left tag.wr) (covers_left (env.perm.wCn (by have := L.hWn; omega))))))
    · intro addr m hh
      rcases hh with ⟨r,hr,hc⟩
      simp only [List.mem_singleton] at hr; subst r
      exact env.perm.ctx addr m ⟨⟨C,256⟩,List.mem_singleton_self _,by simp only [Region.Contains] at hc ⊢; omega⟩
    · simpa using covers_left (env.perm.stC (d := 0) (n := 16) (by decide))
  · change Covers [⟨St,16⟩,⟨Tg,16⟩,⟨W+BitVec.ofNat 64 512,wn-512⟩] s.wr
    refine covers_cons ?_ (covers_cons tag.wr (env.perm.wCn (by have := L.hWn; omega)))
    simpa using env.perm.stC (d := 0) (n := 16) (by decide)

structure DirectTagOut (wn : Nat) (C St W SP Tg : Addr) (k : Reg → Addr) (value : Block)
    (m : Mem) (s : State) : Prop where
  env : Env wn C St W SP s
  kept : Kept k s
  bytes : bytesAt s.mem Tg 16 = toBytes value
  frame : Frame [⟨St,16⟩,⟨Tg,16⟩,⟨W+BitVec.ofNat 64 512,wn-512⟩] m s.mem

theorem direct_ok (L : Lay wn C St W) (v : GcmImpl) (env : Env wn C St W SP s)
    (hk : Kept k s) (tag : DataW wn C St W s Tg 16) (hr : R=10 ∨ R=12 ∨ R=14)
    (rounds : s.gpr .x22 = BitVec.ofNat 64 R) (slot : s.mem.readW (W+BitVec.ofNat 64 tlO) 64 = Tg)
    (hv : v.ctr.scratch ≤ wn-512) :
    WP isa (.seq (.block tagArgs) (ctrCallG v.callees true)) s
      (DirectTagOut wn C St W SP Tg k ((blockAt s.mem (St+BitVec.ofNat 64 16)) ^^^
        ciphOf s.mem C R (blockAt s.mem St)) s.mem) := by
  refine WP.seq ((tagArgs_ok L env tag hr rounds slot).mono fun t ⟨r,c⟩ => ?_)
  refine (ctrTo_callLe v.ctr hv c).mono fun u q => ?_
  have gout := q.out
  rw [blocksAt_one,blocksAt_one,ctr32_single,List.cons.injEq] at gout
  have e := env.of_regs r
  refine ⟨e.of_saved q.saved q.sp q.rd q.wr,(hk.of_eq fun reg h => r.others reg (by
    simp only [keptRegs,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl <;> decide)).of_saved q.saved,?_,?_⟩
  · rw [Proof.Cmac.bytesAt_blockAt,gout.1,r.mem]
  · simpa only [r.mem] using q.frame

theorem lengths_ok (L : Lay wn C St W) (v : GcmImpl) (env : Env wn C St W SP s) (hk : Kept k s) :
    WP isa (lens v.callees 16 .x26 .x27) s
      (TOut wn C St W SP k 16 (s.gpr .x25).toNat
        (ghashFrom (blockAt s.mem (C+BitVec.ofNat 64 240)) (blockAt s.mem (St+BitVec.ofNat 64 16))
          [ofBytes (lensBlock (s.gpr .x26).toNat (s.gpr .x27).toNat)]) s.mem) := by
  exact WP.seq ((lensSeg_ok L (yo := 16) (.inr rfl) env hk (by change s.gpr .x25 = BitVec.ofNat 64 (s.gpr .x25).toNat; simp) (by decide)).mono fun _ h =>
    lensCall_ok L (.inr rfl) v h)

abbrev directFrame (wn : Nat) (St W Tg : Addr) :=
  tFrame St W 16 ++ [⟨St,16⟩,⟨Tg,16⟩,⟨W+BitVec.ofNat 64 512,wn-512⟩]

theorem tagSlot {m m' : Mem} (L : Lay wn C St W) (frame : Frame (tFrame St W 16) m m') :
    m'.readW (W+BitVec.ofNat 64 tlO) 64 = m.readW (W+BitVec.ofNat 64 tlO) 64 := by
  apply frame.readW (r := ⟨W+BitVec.ofNat 64 tlO,8⟩) (Region.contains_self _ _) _ (by decide)
  intro r hr
  simp only [tFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact (L.st_w (by decide) (.inr ⟨by decide,by decide⟩)).symm
  · exact L.w_wn (by decide) (by have := L.hWn; change 248+8 ≤ wn; omega) (by have := L.hWn; omega)
  · exact L.w_wn (by decide) (by have := L.hWn; change 248+8 ≤ wn; omega) (by have := L.hWn; omega)

theorem tag_ok (L : Lay wn C St W) (v : GcmImpl) (e : Env wn C St W SP s)
    (hk : Kept k s) (tag : DataW wn C St W s Tg 16) (hr : R=10 ∨ R=12 ∨ R=14)
    (rounds : s.gpr .x22 = BitVec.ofNat 64 R) (slot : s.mem.readW (W+BitVec.ofNat 64 tlO) 64 = Tg)
    (hv : v.ctr.scratch ≤ wn-512) :
    WP isa (tagDirect v.callees) s fun t => Env wn C St W SP t ∧ Kept k t ∧
      bytesAt t.mem Tg 16 = toBytes (ghashFrom (blockAt s.mem (C+BitVec.ofNat 64 240))
        (blockAt s.mem (St+BitVec.ofNat 64 16)) [ofBytes (lensBlock (s.gpr .x26).toNat (s.gpr .x27).toNat)]
          ^^^ ciphOf s.mem C R (blockAt s.mem St)) ∧ Frame (directFrame wn St W Tg) s.mem t.mem := by
  refine WP.seq ((WP.with_rdwr (lengths_ok L v e hk)).mono fun t ⟨a,rd,wr⟩ => ?_)
  have nonce : blockAt t.mem St = blockAt s.mem St := blockAt_frame a.frame fun r h => by
    simp only [tFrame,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl
    · simpa using L.st_st (a:=0) (n:=16) (d:=16) (k:=16) (.inl (by decide)) (by decide) (by decide)
    · simpa using L.st_w (a:=0) (n:=16) (d:=96) (k:=16) (by decide) (.inr ⟨by decide,by decide⟩)
    · simpa using L.st_wn (a:=0) (n:=16) (d:=512) (k:=256) (by decide) (.inr ⟨by decide,by have := L.hWn; omega⟩)
  have cipher := ciph_frame a.frame (fun r h => by
    simp only [tFrame,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl
    · exact L.cs.sub_right (Lay.stSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by have := L.hWn; omega))
    · exact L.cw'.sub_right (Lay.wSub (by have := L.hWn; omega))) hr
  refine (direct_ok L v a.env a.kept (tag.of_eq rd wr) hr ((a.kept _ (by decide)).trans
    ((hk _ (by decide)).symm.trans rounds)) ((tagSlot L a.frame).trans slot) hv).mono fun u b => ?_
  exact ⟨b.env,b.kept,by rw [b.bytes,a.out,nonce,cipher],
    (a.frame.mono fun _ h => List.mem_append_left _ h).trans (b.frame.mono fun _ h => List.mem_append_right _ h)⟩

end VG.Proof.AesGcm.AArch64.Contiguous.Standalone
