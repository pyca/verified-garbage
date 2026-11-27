module

-- separate module: Recover public pointers and region permissions across nonce and AAD without unfolding the AES payload.

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.Access
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.Prepare
import VerifiedGarbage.Proof.Framework.Offset

/-! # Recover source and destination permissions after authenticating the nonce and AAD -/

public section
namespace VG.Proof.AesGcm.PPC64LE.Contiguous
open VG VG.PPC64LE

structure Positions (s u : State) : Prop where
  key : u.gpr .r29=s.gpr .r3
  rounds : u.gpr .r28=s.gpr .r4
  work : u.gpr .r31=Contiguous.work s
  stream : u.gpr .r30=Contiguous.work s+16
  src : u.gpr .r19=s.gpr .r9
  dst : u.gpr .r27=s.gpr .r10
  len : u.gpr .r23=stackArg s 0
  aadLen : u.gpr .r22=s.gpr .r8
  tag : u.gpr .r20=stackArg s 1
  rd : u.rd=s.rd
  wr : u.wr=frameR 1280 s::s.wr

theorem positions {s e t u : State} (p : Args s e) (q : Started e (work s) t) (z : ReadyData s e t u)
    (rd : u.rd=t.rd) (wr : u.wr=t.wr) : Positions s u := by
  have atSlot (i : Nat) (hi : i<2) : e.mem.readW (e.sp+BitVec.ofNat 64 (96+8*i)) 64=stackArg s i := by
    rw [p.sp];exact p.copied i hi
  exact ⟨z.env.r29.trans (q.key.trans (p.regs _ (by decide) (by decide))),
    (z.env.fr _ (by decide)).trans (q.rounds.trans (p.regs _ (by decide) (by decide))),
    z.env.r31.trans q.scratch,z.env.r30.trans q.stream,
    (z.env.fr _ (by decide)).trans (q.src.trans (p.regs _ (by decide) (by decide))),
    (z.env.fr _ (by decide)).trans (q.dst.trans (p.regs _ (by decide) (by decide))),
    (z.env.fr _ (by decide)).trans (q.len.trans (atSlot 0 (by decide))),
    (z.env.fr _ (by decide)).trans (q.aadLen.trans (p.regs _ (by decide) (by decide))),
    (z.env.fr _ (by decide)).trans (q.tag.trans (atSlot 1 (by decide))),
    rd.trans (q.entered.keeps.rd.trans p.rd),wr.trans (q.entered.keeps.wr.trans p.wr)⟩

theorem Positions.space {s u : State} (g : Positions s u) (h : CallLayout s)
    (perm : Perm (u.gpr .r29) (u.gpr .r30) (u.gpr .r31) u) : PayloadSpace u := by
  let T := stackArg s 0
  have slabIn : (slab u).Sub (workR s) := by rw [slab,g.work];exact Offset.sub_base _ (by decide)
  have sep {r : Region} (hr : r∈argsRegions s) : r.Disjoint (slab u) :=
    ((stack_disjoint h hr).symm.sub_right (work_sub s)).sub_right slabIn
  have len : datLen u=T.toNat := by rw [datLen,g.len]
  have dstWrites : Covers [dstR s] u.wr := by
    rw [g.wr,h.wr];exact covers_mem (by simp)
  have sourceReads : Covers [srcR s] (u.rd++u.wr) := by
    by_cases eq : s.gpr .r9=s.gpr .r10
    · simpa only [srcR,dstR,eq] using dstWrites.right
    · rw [g.rd,h.rd];simp only [eq,↓reduceIte,List.cons_append,List.nil_append];apply covers_mem;simp
  have src := args_data h (r:=srcR s) (by simp [argsRegions]) T.isLt sourceReads
  have dst := args_data h (r:=dstR s) (by simp [argsRegions]) T.isLt dstWrites.right
  refine ⟨perm,(args_lay h).v g.key g.stream g.work,?_,?_,?_,?_,?_,?_⟩
  · refine ⟨?_,?_,?_⟩
    · rw [g.stream,g.work,g.src,len];exact src
    · rw [g.key,g.stream,g.work,g.dst,len];exact ⟨dst,dstWrites,h.cd⟩
    · rw [g.src,g.dst,len];exact h.alias
  · rw [srcRegion,g.src,len];exact sep (r:=srcR s) (by simp [argsRegions])
  · rw [dat,g.dst,len];exact sep (r:=dstR s) (by simp [argsRegions])
  · rw [ctxRegion,g.key];exact sep (r:=ctxR s) (by simp [argsRegions])
  · rw [slab,g.stream,g.work];exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  · rw [g.wr]
    apply Covers.one
    refine ⟨_,List.mem_cons_self,?_⟩
    change (frameR 1280 s).Contains (u.gpr .r31+448) 704
    have eq : Contiguous.work s+448=base s+BitVec.ofNat 64 (128+448) := BitVec.add_assoc ..
    rw [g.work,eq]
    exact Offset.contains _ (by decide) (by decide) (by decide)

end VG.Proof.AesGcm.PPC64LE.Contiguous
