module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Verified
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

/-! # The shared register-only POWER8 GCM block entry -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SplitBlocks
open VG VG.PPC64LE

def bufferState (s : State) : State :=
  (((s.write .r11 (s.gpr .r10)).write .r10 (s.gpr .r8)).write .r8 (s.gpr .r8 >>> 3)).write .r8 ((s.gpr .r8 >>> 3) <<< 3)

theorem bufferArgs_ok (s : State) :
    WP isa (.block Impl.AesGcm.PPC64LE.SplitBlocks.bufferArgs) s (· = bufferState s) := by
  apply WP.of_runBlock
  simp only [Impl.AesGcm.PPC64LE.SplitBlocks.bufferArgs,Impl.Aes.PPC64LE.Crypto.mov,
    runBlock_cons,runStep_some,runBlock_nil,exec_logic,BitVec.or_self,
    exec_lsr_d (sh := 3) (by decide),exec_lsl (sh := 3) (by decide),
    RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true,Option.some.injEq,exists_eq_left']
  rfl

/-- For identical buffers the partial group already occupies the destination.
A disjoint caller hands the kernel an integral number of groups. Both layouts
therefore consume the same list of source blocks. -/
theorem buffers_input (s : State) (n k : Nat) (hk : k≤n)
    (hkn : ((bufferState s).gpr .r8).toNat=k) (hn : ((bufferState s).gpr .r10).toNat=n)
    (layout : s.gpr .r7=s.gpr .r9 ∨ k=n) :
    inBlocks (bufferState s)=Spec.Gcm.blocksAt s.mem (s.gpr .r7) n := by
  unfold inBlocks
  rw [hkn,hn]
  change Spec.Gcm.blocksAt s.mem (s.gpr .r7) k ++ (Spec.Gcm.blocksAt s.mem (s.gpr .r9) n).drop k=_
  rcases layout with h | rfl
  · rw [← h]
    have hp : (Spec.Gcm.blocksAt s.mem (s.gpr .r7) n).take k=Spec.Gcm.blocksAt s.mem (s.gpr .r7) k := by
      simp only [Spec.Gcm.blocksAt,← List.map_take,List.take_range,Nat.min_eq_left hk]
    rw [← hp,List.take_append_drop]
  · simp only [List.drop_eq_nil_of_le (show (Spec.Gcm.blocksAt s.mem (s.gpr .r9) k).length ≤ k by
      simp only [Spec.Gcm.blocksAt,List.length_map,List.length_range,Nat.le_refl]),List.append_nil]

theorem encryptBuffers_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    (s : State) (lay : Wrapper.Layout (Contract.prep (bufferState s)) (s.gpr .r8).toNat
      (((s.gpr .r8 >>> 3) <<< 3).toNat))
    (rounds : (s.gpr .r4).toNat=10 ∨ (s.gpr .r4).toNat=12 ∨ (s.gpr .r4).toNat=14)
    (scratch : Covers [⟨s.gpr .r10,704⟩] s.wr) :
    WP isa Impl.AesGcm.PPC64LE.SplitBlocks.encryptBuffers s (CryptPost false (bufferState s)) := by
  apply WP.seq
  refine WP.mono (bufferArgs_ok s) fun _ h => ?_
  subst_vars
  exact rest_wp false (bufferState s) lay rounds scratch

def prefixCount (s : State) : Nat := (((s.gpr .r8 >>> 3) <<< 3).toNat)

structure BufferPre (s : State) : Prop where
  layout : Wrapper.Layout (Contract.prep (bufferState s)) (s.gpr .r8).toNat (prefixCount s)
  rounds : (s.gpr .r4).toNat=10 ∨ (s.gpr .r4).toNat=12 ∨ (s.gpr .r4).toNat=14
  scratch : Covers [⟨s.gpr .r10,704⟩] s.wr
  input : s.gpr .r7=s.gpr .r9 ∨ prefixCount s=(s.gpr .r8).toNat

def bufferOutput (s : State) := Spec.Gcm.ctr32
  (Spec.Gcm.ctxCiph s.mem (s.gpr .r3) (s.gpr .r4).toNat) (Spec.Gcm.blockAt s.mem (s.gpr .r5))
  (Spec.Gcm.blocksAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)

structure BufferPost (s t : State) : Prop where
  data : Spec.Gcm.blocksAt t.mem (s.gpr .r9) (s.gpr .r8).toNat=bufferOutput s
  ctr : Spec.Gcm.blockAt t.mem (s.gpr .r5)=Nat.repeat Spec.Gcm.inc32 (s.gpr .r8).toNat
    (Spec.Gcm.blockAt s.mem (s.gpr .r5))
  hash : Spec.Gcm.blockAt t.mem (s.gpr .r6)=Spec.Gcm.ghashFrom (Spec.Gcm.ctxH s.mem (s.gpr .r3))
    (Spec.Gcm.blockAt s.mem (s.gpr .r6)) (bufferOutput s)

/-- The two callers share the same source-based postcondition. -/
theorem encryptBuffers_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    (s : State) (h : BufferPre s) : ∃ tr t, Exec isa Impl.AesGcm.PPC64LE.SplitBlocks.encryptBuffers s tr t ∧
      abiPreserved s t ∧ BufferPost s t := by
  obtain ⟨tr,t,he,hp⟩ := encryptBuffers_wp s h.layout h.rounds h.scratch
  have input := buffers_input s _ _ h.layout.bound rfl rfl h.input
  have out : outBlocks (bufferState s)=bufferOutput s := by
    unfold outBlocks
    rw [input]
    rfl
  refine ⟨tr,t,he,⟨?_,Exec.sp he,hp.lr⟩,⟨hp.out.trans out,hp.counter,?_⟩⟩
  · intro r hr
    have keep : ∀ r ∈ preserved, r≠.r8 ∧ r≠.r10 ∧ r≠.r11 := by decide
    simpa only [bufferState,RegUpd.gpr_write,(keep r hr).1,(keep r hr).2.1,(keep r hr).2.2,ite_false]
      using hp.saved r hr
  · have hy := hp.y
    rw [Bool.cond_false,out] at hy
    exact hy

theorem sameLayout {a b : State} {n k : Nat} (h : Wrapper.Layout a n k)
    (k3 : b.gpr .r3=a.gpr .r3) (k5 : b.gpr .r5=a.gpr .r5) (k6 : b.gpr .r6=a.gpr .r6)
    (k7 : b.gpr .r7=a.gpr .r7) (k9 : b.gpr .r9=a.gpr .r9)
    (k17 : b.gpr .r17=a.gpr .r17) (k19 : b.gpr .r19=a.gpr .r19)
    (rd : b.rd=a.rd) (wr : b.wr=a.wr) : Wrapper.Layout b n k := by
  have key : Blocks.coreKey (Blocks.wrapperView b)=Blocks.coreKey (Blocks.wrapperView a) :=
    congrArg (fun p => (⟨p,256⟩ : Region)) k3
  have ctr : Blocks.coreCounter (Blocks.wrapperView b)=Blocks.coreCounter (Blocks.wrapperView a) :=
    congrArg (fun p => (⟨p,16⟩ : Region)) k5
  have hash : Blocks.coreY (Blocks.wrapperView b)=Blocks.coreY (Blocks.wrapperView a) :=
    congrArg (fun p => (⟨p,16⟩ : Region)) k6
  have data : Blocks.coreData (Blocks.wrapperView b) n=Blocks.coreData (Blocks.wrapperView a) n :=
    congrArg (fun p => (⟨p,16*n⟩ : Region)) k7
  refine ⟨⟨h.wrapper.core.congr k3 k5 k7 k6 (congrArg (·+64) k9) rd wr,?_,?_,?_⟩,
    h.bound,k19.trans h.left,?_,?_⟩
  · rw [k9,wr]; exact h.wrapper.header
  · rw [key,ctr,hash,data,k9]; exact h.wrapper.scratch
  · rw [k7]; exact h.wrapper.fit
  · rw [rd,wr,k17]; exact h.reads
  · simpa only [Blocks.wrapperFullWrites,sourceRegion,k9,k7,k17,data,ctr,hash] using h.buffers

def bufferContract : VG.Contract isa where
  pre := BufferPre
  post := BufferPost
  pub s t := s.sp=t.sp ∧ ∀ r ∈ ([.r3,.r4,.r5,.r6,.r7,.r8,.r9,.r10] : List Reg), s.gpr r=t.gpr r

theorem prefixCount_eq (s : State) : prefixCount s=(s.gpr .r8).toNat/8*8 := by
  simp only [prefixCount,BitVec.toNat_shiftLeft,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq,Nat.reducePow]
  exact Nat.mod_eq_of_lt (by have h := (s.gpr .r8).isLt; omega_using [h])

end VG.Proof.AesGcm.PPC64LE.SplitBlocks
