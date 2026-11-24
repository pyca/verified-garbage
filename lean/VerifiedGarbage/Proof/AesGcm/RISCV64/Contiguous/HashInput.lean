module

public import VerifiedGarbage.Impl.Gcm.RISCV64.Prepared
public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Spec.Gcm.Bitsliced
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Callee
import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
public import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps


/-! # The prepared GHASH key and writable regions of a contiguous seal -/

@[expose] public section
namespace VG.Proof.AesGcm.RISCV64
open VG.Impl.Gcm.RISCV64.Prepared
open VG VG.RISCV64 VG.Proof.Gcm.RISCV64
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

/-- The read-only 288-byte suffix of the bitsliced key, at a GHASH call. -/
structure TableAt (s : State) (T : Addr) (H : Block) : Prop where
  al : T.toNat%8=0
  stack : (below s.sp 2048).Disjoint ⟨T,288⟩
  read : Covers [⟨T,288⟩] (s.rd++s.wr)
  key : ∀ i < 9, ∀ j < 4, s.mem.readW (T+BitVec.ofNat 64 (8*(4*i+j))) 64 =
    Spec.Gcm.ghashOperand H i &&& Spec.Gcm.ghashClass j

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
  refine ⟨al,apart,read,fun i hi j hj => ?_⟩
  rw [BitVec.add_assoc,BitVec.ofNat_add_ofNat]
  exact ks.2 i hi j hj

/-- Payload and scratch writes preserve the prepared table when their regions stay
outside the key. This covers either permitted payload layout. -/
theorem TableAt.frame {s t : State} {T : Addr} {H : Block} {rs : List Region}
    (h : TableAt s T H) (f : Frame rs s.mem t.mem)
    (apart : ∀ r∈rs,(⟨T,288⟩ : Region).Disjoint r)
    (sp : t.sp=s.sp) (read : Covers [⟨T,288⟩] (t.rd++t.wr)) : TableAt t T H := by
  obtain ⟨al,stack,_,tab⟩ := h
  refine ⟨al,sp ▸ stack,read,?_⟩
  intro i hi j hj
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

theorem TableAt.transfer {s t : State} {T : Addr} {H : Block} {rs : List Region}
    (h : TableAt s T H) (f : Frame rs s.mem t.mem) (apart : ∀ r∈rs,(⟨T,288⟩ : Region).Disjoint r)
    (stack : (below t.sp 2048).Disjoint ⟨T,288⟩) (read : Covers [⟨T,288⟩] (t.rd++t.wr)) :
    TableAt t T H := by
  let u := { t with sp := s.sp }
  obtain k := (h.frame (t:=u) f apart rfl read).key
  exact ⟨h.al,stack,read,k⟩

/-- Pin the public address of the prepared table across writes to the payload, scratch and private frame. -/
structure HashScope (K bk : Addr) (rs : List Region) (s : State) : Prop where
  action : FramedHashAction preparedInvocation K rs s
  pinned : ∀ t, Keeps' s t → Frame rs s.mem t.mem →
    HashInput t (blockAt t.mem K) ∧ t.mem.readW (t.sp+BitVec.ofNat 64 16) 64=bk

theorem HashScope.after {K bk : Addr} {rs : List Region} {s t : State} (q : HashScope K bk rs s)
    (h : Keeps' s t) (f : Frame rs s.mem t.mem) : HashScope K bk rs t := by
  refine ⟨FramedHashAction.after q.action h f,?_⟩
  intro u k fm
  exact q.pinned u ⟨k.rd.trans h.rd,k.wr.trans h.wr,k.sp.trans h.sp⟩ (f.trans fm)

theorem HashScope.kept {K bk : Addr} {rs : List Region} {s t : State} (q : HashScope K bk rs s)
    (h : Keeps s t) : HashScope K bk rs t :=
  q.after ⟨h.rd,h.wr,h.sp⟩ (h.mem ▸ Frame.refl _ _)

theorem HashScope.now {K bk : Addr} {rs : List Region} {s : State} (q : HashScope K bk rs s) :
    HashInput s (blockAt s.mem K) ∧ s.mem.readW (s.sp+BitVec.ofNat 64 16) 64=bk :=
  q.pinned s ⟨rfl,rfl,rfl⟩ (Frame.refl _ _)

theorem HashScope.narrow {K bk : Addr} {rs rs' : List Region} {s : State} (q : HashScope K bk rs s)
    (sub : ∀ r∈rs',∃ r'∈rs,r.Sub r') : HashScope K bk rs' s :=
  ⟨FramedHashAction.narrow q.action sub,fun t k f => q.pinned t k (f.sub sub)⟩

abbrev PreparedInvocationLaw : Prop := ∀ {s : State} {K Y D S : Addr} {n : Nat},
  GhCall s K Y D S n → HashInput s (blockAt s.mem K) → WP isa preparedInvocation s (GhPost s K Y D S n)

/-- The prepared invocation satisfies the same call law throughout a scope whose
writes cannot change the stack argument, prepared table, or original hash key. -/
theorem preparedHashScope (run : PreparedInvocationLaw) {s : State} {K : Addr} {rs : List Region} (c : HashInput s (blockAt s.mem K))
    (slot : ∀ r∈rs,(⟨s.sp+BitVec.ofNat 64 16,8⟩ : Region).Disjoint r)
    (table : ∀ r∈rs,(⟨s.mem.readW (s.sp+BitVec.ofNat 64 16) 64+BitVec.ofNat 64 960,288⟩ : Region).Disjoint r)
    (key : ∀ r∈rs,(⟨K,16⟩ : Region).Disjoint r) :
    HashScope K (s.mem.readW (s.sp+BitVec.ofNat 64 16) 64) rs s := by
  suffices p : ∀ u, Keeps' s u → Frame rs s.mem u.mem →
      HashInput u (blockAt u.mem K) ∧ u.mem.readW (u.sp+BitVec.ofNat 64 16) 64=s.mem.readW (s.sp+BitVec.ofNat 64 16) 64 by
    refine ⟨?_,p⟩
    intro t keep fm u regs Y D S n g
    exact run g (p u ⟨regs.rd.trans keep.rd,regs.wr.trans keep.wr,regs.sp.trans keep.sp⟩ (regs.mem ▸ fm)).1
  intro u keep fm
  have eq := fm.readW (Region.contains_self (s.sp+BitVec.ofNat 64 16) 8) slot (by decide : 64/8<2^64)
  refine ⟨⟨keep.sp ▸ c.slotAlign,?_,?_⟩,by rw [keep.sp,eq]⟩
  · rw [keep.sp,keep.rd,keep.wr];exact c.slotRead
  · rw [keep.sp,eq,blockAt_frame fm key]
    exact c.table.frame fm table keep.sp (by rw [keep.rd,keep.wr];exact c.table.read)

end VG.Proof.AesGcm.RISCV64
