module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Prepared.Verified
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Callee
import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
public import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps

/-! # Calling prepared GHASH with the contiguous operation’s key and stack arguments -/

@[expose] public section
namespace VG.Proof.AesGcm.RISCV64
open VG.Impl.Gcm.RISCV64.Prepared
open VG VG.RISCV64 VG.Proof.Gcm.RISCV64
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

def cachedContract (H : Block) : Contract isa where
  pre s := CachedPre H s ∧ 112 ≤ s.sp.toNat
  post := hashDone H
  pub := ghashX.pub

theorem cached_correct {H : Block} (s : State) (h : (cachedContract H).pre s) :
    ∃ t s', Exec isa cachedHash s t s' ∧ abiPreserved s s' ∧ (cachedContract H).post s s' :=
  preparedHash_law s h.1 h.2

/-- The read-only 288-byte suffix of the bitsliced key, at a GHASH call. -/
structure TableAt (s : State) (T : Addr) (H : Block) : Prop where
  al : T.toNat%8=0
  stack : (below s.sp 2048).Disjoint ⟨T,288⟩
  read : Covers [⟨T,288⟩] (s.rd++s.wr)
  key : ∃ h0 h1, H=h0++h1 ∧ Tab (VG.Proof.Gcm.Holes.key0 h0 h1) (VG.Proof.Gcm.Holes.key1 h0 h1)
    (fun off => s.mem.readW (T+BitVec.ofNat 64 off) 64)

def cachedEntry (s : State) (T Y D S : Addr) (n : Nat) :=
  s.callEntry.withRegions [⟨T,288⟩,⟨D,16*n⟩] [⟨Y,16⟩,⟨S,256⟩]

theorem cached_call_pre {s : State} {K Y D S T : Addr} {n : Nat} {H : Block}
    (g : GhCall s K Y D S n) (t : TableAt s T H) (e : State) (a0 : e.gpr .a0=T)
    (args : ∀ r, r ≠ .a0 → r ≠ .t0 → e.gpr r=s.gpr r) (mem : e.mem=s.mem) (sp : e.sp=s.sp) :
    (cachedContract H).pre (cachedEntry e T Y D S n) := by
  have ge : 112 ≤ s.sp.toNat := by omega_using [g.spge]
  have fo : CompactFrame (allocd 112 (cachedEntry e T Y D S n)).sp (allocd 112 (cachedEntry e T Y D S n)) := by
    refine ⟨?_,?_,List.mem_cons_self⟩
    · change (e.sp-BitVec.ofNat 64 112).toNat %16=0
      rw [sp,toNat_sub_ofNat' ge];omega_using [g.spal]
    · change (e.sp-BitVec.ofNat 64 112).toNat +112≤2^64
      rw [sp,toNat_sub_ofNat' ge]
      have := s.sp.isLt
      omega_using []
  have sf : (below s.sp 112).Sub (below s.sp 2048) := VG.RISCV64.below_sub (by decide) (by decide)
  constructor
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,fo,?_⟩ <;>
      simp only [cachedEntry, State.withRegions_gpr, State.withRegions_sp, State.withRegions_rd,
        State.withRegions_wr, State.withRegions_mem, State.callEntry_mem, State.callEntry_sp, allocd,
        callEntry_gpr' _ (by decide : Reg.a0 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.a1 ∉ linkRegs),
        callEntry_gpr' _ (by decide : Reg.a2 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.a3 ∉ linkRegs),
        callEntry_gpr' _ (by decide : Reg.a4 ∉ linkRegs), a0,args .a1 (by decide) (by decide),
        args .a2 (by decide) (by decide),args .a3 (by decide) (by decide),args .a4 (by decide) (by decide),
        g.a1,g.a2,g.a3,g.a4,toNat64 g.n_lt,sp,mem]
    exacts [t.al, (t.stack.sub_left sf), (g.ky.sub_left sf), (g.kd.sub_left sf), g.dfit, t.key]
  · change 112≤e.sp.toNat
    rwa [sp]

theorem cached_call_wp {s : State} {K Y D S T : Addr} {n : Nat}
    (g : GhCall s K Y D S n) (t : TableAt s T (blockAt s.mem K)) (e : State) (a0 : e.gpr .a0=T)
    (args : ∀ r, r ≠ .a0 → r ≠ .t0 → e.gpr r=s.gpr r)
    (mem : e.mem=s.mem) (sp : e.sp=s.sp) (rd : e.rd=s.rd) (wr : e.wr=s.wr) :
    WP isa (.call "vg_ghash_prepared" cachedHash) e (GhPost s K Y D S n) := by
  let H := blockAt s.mem K
  refine WP.callAny (k:=cachedContract H) cached_correct (rd:=[⟨T,288⟩,⟨D,16*n⟩]) (wr:=[⟨Y,16⟩,⟨S,256⟩])
    (cached_call_pre g t e a0 args mem sp) ?_ (wr ▸ g.writes) ?_ (by change 112<2^64;decide)
  · rw [rd,wr]
    rintro a l ⟨r,hr,c⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact t.read _ _ ⟨_,List.mem_cons_self,c⟩
    all_goals exact g.reads _ _ ⟨_,by simp,c⟩
  · intro u hrd hwr hsp hf hcs post
    refine ⟨hrd.trans rd,hwr.trans wr,hsp.trans sp, fun r hr => (hcs _ hr).trans (args _ (by revert hr;revert r; decide) (by revert hr;revert r;decide)), ?_,?_⟩
    · rw [sp,mem] at hf
      exact VG.RISCV64.Frame.below_mono (wr:=[⟨Y,16⟩,⟨S,256⟩]) hf (by change 112≤2048;decide) (by decide)
    · simpa only [cachedContract,hashDone,State.withRegions_gpr,State.withRegions_mem,State.callEntry_mem,
        callEntry_gpr' _ (by decide : Reg.a1 ∉ linkRegs),callEntry_gpr' _ (by decide : Reg.a2 ∉ linkRegs),
        callEntry_gpr' _ (by decide : Reg.a3 ∉ linkRegs),args .a1 (by decide) (by decide),
        args .a2 (by decide) (by decide),args .a3 (by decide) (by decide),g.a1,g.a2,g.a3,toNat64 g.n_lt,mem] using post

end VG.Proof.AesGcm.RISCV64

namespace VG.Proof.AesGcm.RISCV64
open VG.Impl.Gcm.RISCV64.Prepared
open VG VG.RISCV64 VG.Proof.Gcm.RISCV64
open VG.Spec.Gcm (Block blockAt)
structure HashInput (s : State) (H : Block) : Prop where
  slotAlign : (s.sp+BitVec.ofNat 64 16).toNat%8=0
  slotRead : InRegions (s.rd++s.wr) (s.sp+BitVec.ofNat 64 16) 8
  table : TableAt s (s.mem.readW (s.sp+BitVec.ofNat 64 16) 64+BitVec.ofNat 64 960) H

/-- The precomputation is precisely the table consumed by the scalar multiplier. -/
theorem TableAt.of_sliced {s : State} {bk ctx : Addr} (ks : Spec.Gcm.CtxSlicedRepr s.mem bk ctx)
    (al : (bk+BitVec.ofNat 64 960).toNat%8=0)
    (apart : (below s.sp 2048).Disjoint ⟨bk+BitVec.ofNat 64 960,288⟩)
    (read : Covers [⟨bk+BitVec.ofNat 64 960,288⟩] (s.rd++s.wr)) :
    TableAt s (bk+BitVec.ofNat 64 960) (Spec.Gcm.ctxH s.mem ctx) := by
  have tab : Tab (Spec.Gcm.ghashKey0 (Spec.Gcm.ctxH s.mem ctx))
      (Spec.Gcm.ghashKey1 (Spec.Gcm.ctxH s.mem ctx))
      (fun d => s.mem.readW ((bk+BitVec.ofNat 64 960)+BitVec.ofNat 64 d) 64) := by
    intro i hi j hj
    dsimp only
    rw [BitVec.add_assoc,BitVec.ofNat_add_ofNat,ks.2 i hi j hj,ghashOperand_eq]
    rfl
  rw [Spec.Gcm.ctxH,blockAt_hOf,hOf,w2,ghashKey0_append,ghashKey1_append] at tab
  refine ⟨al,apart,read,_,_,?_,tab⟩
  exact blockAt_hOf _ _

/-- Payload and scratch writes preserve the prepared table when their regions stay
outside the key. This covers either permitted payload layout. -/
theorem TableAt.frame {s t : State} {T : Addr} {H : Block} {rs : List Region}
    (h : TableAt s T H) (f : Frame rs s.mem t.mem)
    (apart : ∀ r∈rs,(⟨T,288⟩ : Region).Disjoint r)
    (sp : t.sp=s.sp) (read : Covers [⟨T,288⟩] (t.rd++t.wr)) : TableAt t T H := by
  obtain ⟨al,stack,_,h0,h1,e,tab⟩ := h
  refine ⟨al,sp ▸ stack,read,h0,h1,e,?_⟩
  intro i hi j hj
  dsimp only
  rw [f.readW (r:=⟨T,288⟩) (Offset.contains_base _ (by omega_using [hi,hj]) (by omega_using [hi,hj])) apart (by decide)]
  exact tab i hi j hj

theorem loadPrepared_wp {s : State} {H : Block} (c : HashInput s H) :
    WP isa (.block loadPrepared) s fun e =>
      e.gpr .a0=s.mem.readW (s.sp+BitVec.ofNat 64 16) 64 + BitVec.ofNat 64 960 ∧
      (∀ r,r ≠ .a0 → r ≠ .t0 → e.gpr r=s.gpr r) ∧
      e.mem=s.mem ∧ e.sp=s.sp ∧ e.rd=s.rd ∧ e.wr=s.wr := by
  obtain ⟨al,rd,_⟩ := c
  unfold loadPrepared
  mrun [al,rd]
  exact fun r a b => by simp [a,b]

theorem preparedInvocation_wp {s : State} {K Y D S : Addr} {n : Nat}
    (g : GhCall s K Y D S n) (c : HashInput s (blockAt s.mem K)) :
    WP isa preparedInvocation s (GhPost s K Y D S n) :=
  WP.seq (WP.mono (loadPrepared_wp c) (fun e ⟨hp,hr,hm,hs,hd,hw⟩ => cached_call_wp g c.table e hp hr hm hs hd hw))

theorem TableAt.transfer {s t : State} {T : Addr} {H : Block} {rs : List Region}
    (h : TableAt s T H) (f : Frame rs s.mem t.mem) (apart : ∀ r∈rs,(⟨T,288⟩ : Region).Disjoint r)
    (stack : (below t.sp 2048).Disjoint ⟨T,288⟩) (read : Covers [⟨T,288⟩] (t.rd++t.wr)) :
    TableAt t T H := by
  let u := { t with sp := s.sp }
  obtain k := (h.frame (t:=u) f apart rfl read).key
  exact ⟨h.al,stack,read,k⟩

/-- Pin the public address of the prepared table across writes to the payload, scratch and private frame. -/
def HashScope (K bk : Addr) (rs : List Region) (s : State) : Prop :=
  ∀ t, Keeps' s t → Frame rs s.mem t.mem →
    HashInput t (blockAt t.mem K) ∧ t.mem.readW (t.sp+BitVec.ofNat 64 16) 64=bk

theorem HashScope.after {K bk : Addr} {rs : List Region} {s t : State} (q : HashScope K bk rs s)
    (h : Keeps' s t) (f : Frame rs s.mem t.mem) : HashScope K bk rs t := by
  intro u k fm
  exact q u ⟨k.rd.trans h.rd,k.wr.trans h.wr,k.sp.trans h.sp⟩ (f.trans fm)

theorem HashScope.kept {K bk : Addr} {rs : List Region} {s t : State} (q : HashScope K bk rs s)
    (h : Keeps s t) : HashScope K bk rs t :=
  q.after ⟨h.rd,h.wr,h.sp⟩ (h.mem ▸ Frame.refl _ _)

theorem HashScope.now {K bk : Addr} {rs : List Region} {s : State} (q : HashScope K bk rs s) :
    HashInput s (blockAt s.mem K) ∧ s.mem.readW (s.sp+BitVec.ofNat 64 16) 64=bk :=
  q s ⟨rfl,rfl,rfl⟩ (Frame.refl _ _)

theorem HashScope.narrow {K bk : Addr} {rs rs' : List Region} {s : State} (q : HashScope K bk rs s)
    (sub : ∀ r∈rs',∃ r'∈rs,r.Sub r') : HashScope K bk rs' s := fun t k f => q t k (f.sub sub)

theorem HashScope.action {K bk : Addr} {rs : List Region} {s : State} (q : HashScope K bk rs s) :
    FramedHashAction preparedInvocation K rs s := by
  intro t keep f u regs Y D S n g
  exact preparedInvocation_wp g (((q.after keep f).kept regs).now.1)

/-- The prepared invocation satisfies the same call law throughout a scope whose
writes cannot change the stack argument, prepared table, or original hash key. -/
theorem preparedHashScope {s : State} {K : Addr} {rs : List Region} (c : HashInput s (blockAt s.mem K))
    (slot : ∀ r∈rs,(⟨s.sp+BitVec.ofNat 64 16,8⟩ : Region).Disjoint r)
    (table : ∀ r∈rs,(⟨s.mem.readW (s.sp+BitVec.ofNat 64 16) 64+BitVec.ofNat 64 960,288⟩ : Region).Disjoint r)
    (key : ∀ r∈rs,(⟨K,16⟩ : Region).Disjoint r) :
    HashScope K (s.mem.readW (s.sp+BitVec.ofNat 64 16) 64) rs s := by
  intro u keep fm
  have eq := fm.readW (Region.contains_self (s.sp+BitVec.ofNat 64 16) 8) slot (by decide : 64/8<2^64)
  refine ⟨⟨keep.sp ▸ c.slotAlign,?_,?_⟩,by rw [keep.sp,eq]⟩
  · rw [keep.sp,keep.rd,keep.wr];exact c.slotRead
  · rw [keep.sp,eq,blockAt_frame fm key]
    exact c.table.frame fm table keep.sp (by rw [keep.rd,keep.wr];exact c.table.read)

end VG.Proof.AesGcm.RISCV64
