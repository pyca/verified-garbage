module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.Contiguous
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Buffers
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.PPC64LE.DirectGather.Bulk

/-! # The contiguous POWER seal call to the shared eight-block AES/GHASH kernel -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.Contiguous
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE.Contiguous (fusedArgs fused)

def fusedState (s : State) : State :=
  let u := ((s.write .r3 (s.gpr .r29)).write .r4 (s.gpr .r28)).write .r5 (s.gpr .r30+48)
  let u := (u.write .r6 (s.gpr .r30+16)).write .r7 (s.gpr .r19)
  let u := (u.write .r8 (s.gpr .r23 >>> 7)).write .r8 ((s.gpr .r23 >>> 7) <<< 3)
  (u.write .r9 (s.gpr .r27)).write .r10 (s.gpr .r31+448)

theorem fusedArgs_wp (s : State) : WP isa (.block fusedArgs) s (· = fusedState s) := by
  crun [fusedArgs,fusedState,mov,BitVec.or_self]

def fusedBlocks (s : State) : Nat := 8*((s.gpr .r23).toNat/128)

theorem count_eq (s : State) : ((fusedState s).gpr .r8).toNat = fusedBlocks s := by
  change (((s.gpr .r23 >>> 7) <<< 3).toNat) = _
  simp only [fusedBlocks,BitVec.toNat_shiftLeft,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq,Nat.reducePow]
  rw [Nat.mod_eq_of_lt (by have z := (s.gpr .r23).isLt; omega_using [z])]
  omega

def fusedRead (s : State) : List Region := [⟨s.gpr .r29,256⟩,⟨s.gpr .r19,16*fusedBlocks s⟩]
def fusedWrite (s : State) : List Region := [⟨s.gpr .r30+48,16⟩,⟨s.gpr .r30+16,16⟩,
  ⟨s.gpr .r27,16*fusedBlocks s⟩,⟨s.gpr .r31+448,704⟩]

def called (s : State) : State := (fusedState s).callEntry.withRegions (fusedRead s) (fusedWrite s)

/-- The core's ordinary writable layout is the same for both forms. The
source may be the output itself, otherwise it must be outside the write set. -/
structure FusedAccess (s : State) : Prop where
  ctxDst : (⟨s.gpr .r29,256⟩ : Region).Disjoint ⟨s.gpr .r27,16*fusedBlocks s⟩
  ctxCtr : (⟨s.gpr .r29,256⟩ : Region).Disjoint ⟨s.gpr .r30+48,16⟩
  ctxHash : (⟨s.gpr .r29,256⟩ : Region).Disjoint ⟨s.gpr .r30+16,16⟩
  ctrDst : (⟨s.gpr .r30+48,16⟩ : Region).Disjoint ⟨s.gpr .r27,16*fusedBlocks s⟩
  hashDst : (⟨s.gpr .r30+16,16⟩ : Region).Disjoint ⟨s.gpr .r27,16*fusedBlocks s⟩
  scratch : ∀ r ∈ [⟨s.gpr .r29,256⟩, ⟨s.gpr .r30+48,16⟩, ⟨s.gpr .r30+16,16⟩,
    (⟨s.gpr .r27,16*fusedBlocks s⟩ : Region)], r.Disjoint ⟨s.gpr .r31+448,704⟩
  buffers : s.gpr .r19 = s.gpr .r27 ∨ ∀ r ∈ fusedWrite s, (⟨s.gpr .r19,16*fusedBlocks s⟩ : Region).Disjoint r
  dstFit : (s.gpr .r27).toNat + 16*fusedBlocks s ≤ 2^64
  rounds : (s.gpr .r28).toNat=10 ∨ (s.gpr .r28).toNat=12 ∨ (s.gpr .r28).toNat=14

theorem fused_pre {s : State} (a : FusedAccess s) : SplitBlocks.BufferPre (called s) := by
  let u := called s
  let t := SplitBlocks.Contract.prep (SplitBlocks.bufferState u)
  let n := fusedBlocks s
  let key : Region := ⟨s.gpr .r29,256⟩
  let cb : Region := ⟨s.gpr .r30+48,16⟩
  let y : Region := ⟨s.gpr .r30+16,16⟩
  let dst : Region := ⟨s.gpr .r27,16*n⟩
  let src : Region := ⟨s.gpr .r19,16*n⟩
  let w := s.gpr .r31+448
  have count : (u.gpr .r8).toNat = n := count_eq s
  have full : SplitBlocks.prefixCount u = n := by
    rw [SplitBlocks.prefixCount_eq,count]
    dsimp [n,fusedBlocks]
    omega
  have work : Covers [⟨w,704⟩] t.wr := covers_mem (by
    change (⟨w,704⟩ : Region) ∈ [cb,y,dst,⟨w,704⟩]; simp)
  have sub : (⟨w+64,640⟩ : Region).Sub ⟨w,704⟩ := Offset.sub_base _ (by decide)
  have ctrHash : cb.Disjoint y := Offset.disjoint (s.gpr .r30) (.inr (by decide)) (by decide) (by decide)
  have sh : ∀ r ∈ [key,cb,y,dst], r.Disjoint ⟨w,704⟩ := a.scratch
  refine ⟨?_,a.rounds,work,.inr (full.trans count.symm)⟩
  rw [count,full]
  refine ⟨⟨?_,covers_prefix work (by decide),sh,a.dstFit⟩,Nat.le_refl _,?_,?_,?_⟩
  · refine ⟨?_,?_,?_,?_,a.ctxCtr,a.ctxHash,ctrHash,by have h:=a.dstFit; omega⟩
    · exact covers_mem (by change key ∈ [key,src] ++ [cb,y,dst,⟨w,704⟩]; simp)
    · change Covers [cb,y,dst,⟨w+64,640⟩] [cb,y,dst,⟨w,704⟩]
      exact Covers.cons (covers_mem (by simp)) (Covers.cons (covers_mem (by simp))
        (Covers.cons (covers_mem (by simp)) (covers_off work (d := 64) (n := 640) (by decide) (by decide))))
    · intro r hr; exact (sh r hr).sub_right sub
    · intro r hr
      change r ∈ [key,cb,y] at hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [a.ctxDst,a.ctrDst,a.hashDst]
  · change ((u.gpr .r8 >>> 3) <<< 3) = BitVec.ofNat 64 n
    rw [← full]; simp only [SplitBlocks.prefixCount,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  · change InRegions ([key,src]++[cb,y,dst,⟨w,704⟩]) src.base src.len
    exact ⟨src,by simp,Region.contains_self _ _⟩
  · rcases a.buffers with same | apart
    · exact .inl same
    · right; intro r hr
      change r ∈ [⟨w,704⟩,dst,cb,y] at hr
      apply apart r
      change r ∈ [cb,y,dst,⟨w,704⟩]
      simpa only [List.mem_cons,List.not_mem_nil,or_false,or_comm,or_left_comm,or_assoc] using hr

structure FusedResult (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  regs : ∀ r ∈ preserved, t.gpr r = s.gpr r
  frame : Frame (fusedWrite s) s.mem t.mem
  data : VG.Spec.Gcm.blocksAt t.mem (s.gpr .r27) (fusedBlocks s) = SplitBlocks.bufferOutput (called s)
  counter : VG.Spec.Gcm.blockAt t.mem (s.gpr .r30+48) =
    Nat.repeat VG.Spec.Gcm.inc32 (fusedBlocks s) (VG.Spec.Gcm.blockAt s.mem (s.gpr .r30+48))
  hash : VG.Spec.Gcm.blockAt t.mem (s.gpr .r30+16) = VG.Spec.Gcm.ghashFrom
    (VG.Spec.Gcm.ctxH s.mem (s.gpr .r29)) (VG.Spec.Gcm.blockAt s.mem (s.gpr .r30+16))
    (SplitBlocks.bufferOutput (called s))

theorem fused_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {s : State} (access : SplitBlocks.BufferPre (called s))
    (read : Covers (fusedRead s ++ fusedWrite s) (s.rd ++ s.wr)) (write : Covers (fusedWrite s) s.wr) :
    WP isa fused s (FusedResult s) := by
  refine WP.seq (WP.mono (fusedArgs_wp s) fun _ eq => ?_)
  subst_vars
  refine WP.call (k := SplitBlocks.bufferContract) SplitBlocks.encryptBuffers_correct
    (rd := fusedRead s) (wr := fusedWrite s) access read write ?_
  intro t rd wr sp frame regs _ out
  have count : ((called s).gpr .r8).toNat = fusedBlocks s := count_eq s
  refine ⟨rd,wr,sp,?_,frame,?_,?_,?_⟩
  · intro r hr; rw [regs r hr]
    have keep : ∀ r ∈ preserved, r≠.r3 ∧ r≠.r4 ∧ r≠.r5 ∧ r≠.r6 ∧ r≠.r7 ∧ r≠.r8 ∧ r≠.r9 ∧ r≠.r10 := by decide
    obtain ⟨h3,h4,h5,h6,h7,h8,h9,h10⟩ := keep r hr
    simp [fusedState,State.write,h3,h4,h5,h6,h7,h8,h9,h10]
  · rw [← count]; exact out.data
  · rw [← count]; exact out.ctr
  · exact out.hash

end VG.Proof.AesGcm.PPC64LE.Contiguous
