import VerifiedGarbage.Proof.TripleDes.X86.VerifiedBlock
import VerifiedGarbage.Impl.TripleDes.X86.Ecb
import VerifiedGarbage.Proof.Rc2.X86.Cbc.CallFrame
import VerifiedGarbage.Proof.TripleDes.EcbMemory
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.TripleDes.Contract
import VerifiedGarbage.Proof.TripleDes.X86.ConstantTime
import VerifiedGarbage.Proof.TripleDes.Scratch

/-! ## `Call` -/

section

namespace VG.Proof.TripleDes.X86.Ecb

open VG VG.X86 VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)
open VG.Proof.Rc2.X86.Cbc (callWithGpr)

def kept : List Reg := [.ebx, .esi, .edi, .ebp, .esp]

def blockCode (d : Spec.TripleDes.Direction) : Prog isa :=
  match d with | .encrypt => encryptBlock | .decrypt => decryptBlock

theorem block_nosp (d : Spec.TripleDes.Direction) : NoSp (blockCode d) := by
  apply NoSp.of_all
  cases d
  · change encryptBlock.allInstrs _ = true
    lit_decide
  · change decryptBlock.allInstrs _ = true
    lit_decide

theorem block_stack (d : Spec.TripleDes.Direction) : stackUse (blockCode d) = 0 := by
  cases d <;> simp only [blockCode, encryptBlock, decryptBlock, block, blockBody, pass, stackUse,
    Nat.max_self]

theorem blockCall_eq (d : Spec.TripleDes.Direction) : Impl.TripleDes.X86.Ecb.blockCall d =
    .frame (.push [.ebp, .esi, .ebx])
      (.call (match d with | .encrypt => "vg_triple_des_encrypt_block" | .decrypt => "vg_triple_des_decrypt_block")
        (blockCode d)) (.pop .eax 3) := by cases d <;> rfl

structure CallPre (s : State) : Prop where
  reads : Covers [⟨addr32 (s.gpr .ebx), 384⟩, ⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 512⟩] (s.rd ++ s.wr)
  writes : Covers [⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 512⟩] s.wr
  keyScratch : (Region.mk (addr32 (s.gpr .ebx)) 384).Disjoint ⟨addr32 (s.gpr .ebp), 512⟩
  dataScratch : (Region.mk (addr32 (s.gpr .esi)) 8).Disjoint ⟨addr32 (s.gpr .ebp), 512⟩
  keyFit : (s.gpr .ebx).toNat + 384 ≤ 2 ^ 32
  dataFit : (s.gpr .esi).toNat + 8 ≤ 2 ^ 32
  bufFit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32
  stackLo : 16 ≤ (s.gpr .esp).toNat
  stackKey : (below (s.gpr .esp) 16).Disjoint ⟨addr32 (s.gpr .ebx), 384⟩
  stackData : (below (s.gpr .esp) 16).Disjoint ⟨addr32 (s.gpr .esi), 8⟩
  stackBuf : (below (s.gpr .esp) 16).Disjoint ⟨addr32 (s.gpr .ebp), 512⟩

structure CallPost (d : Spec.TripleDes.Direction) (s s' : State) : Prop where
  reg : ∀ r ∈ kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 512⟩, below (s.gpr .esp) 16] s.mem s'.mem
  output : Spec.TripleDes.blockAt s'.mem (addr32 (s.gpr .esi)) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (addr32 (s.gpr .ebx))) d (Spec.TripleDes.blockAt s.mem (addr32 (s.gpr .esi)))

theorem call_ok (d : Spec.TripleDes.Direction) (s : State) (hp : CallPre s) :
    WP isa (Impl.TripleDes.X86.Ecb.blockCall d) s (CallPost d s) := by
  rw [blockCall_eq]
  let rs : List Reg := [.ebp, .esi, .ebx]
  have hrs : .esp ∉ rs := by decide
  have fit : 4 * rs.length + 4 ≤ (s.gpr .esp).toNat := hp.stackLo
  let sE := (pushed rs s).callEntry
  have a0 : arg sE 0 = s.gpr .ebx := by rw [callEntry_arg fit hrs (by decide)]; rfl
  have a1 : arg sE 1 = s.gpr .esi := by rw [callEntry_arg fit hrs (by decide)]; rfl
  have a2 : arg sE 2 = s.gpr .ebp := by rw [callEntry_arg fit hrs (by decide)]; rfl
  have eA : argAddr sE 0 = ((s.gpr .esp) - BitVec.ofNat 32 12).setWidth 64 := by rw [callEntry_argAddr0]; rfl
  have eSp : sE.gpr .esp = s.gpr .esp - BitVec.ofNat 32 16 := by rw [callEntry_esp']; rfl
  have b12 : Region.Sub (below (s.gpr .esp) 12) (below (s.gpr .esp) 16) := below_sub (by decide) hp.stackLo
  have r4 : Region.Sub ⟨((s.gpr .esp) - BitVec.ofNat 32 16).setWidth 64, 4⟩ (below (s.gpr .esp) 16) :=
    Region.sub_prefix (by decide)
  have hcode : blockCode d = block d := by cases d <;> rfl
  refine callWithGpr (c := blockCode d) (k := blockContract d)
    (by rw [hcode]; exact block_correct d) (block_nosp d) (by decide) hrs
    (by rw [block_stack]; exact hp.stackLo) (rd := [⟨addr32 (s.gpr .ebx), 384⟩, ⟨argAddr sE 0, 12⟩])
    (wr := [⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 512⟩]) ⟨?_, ?_, ?_⟩ ?_
  · change (blockContract d).pre (sE.withRegions _ _)
    simp only [blockContract, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, eA, eSp]
    refine ⟨trivial, trivial, hp.keyScratch, hp.dataScratch, hp.stackData.sub_left b12,
      hp.stackBuf.sub_left b12, hp.stackData.sub_left r4, hp.stackBuf.sub_left r4,
      hp.keyFit, hp.dataFit, hp.bufFit, ?_⟩
    rw [sub_toNat hp.stackLo]
    have := (s.gpr .esp).isLt
    omega
  · intro a n ⟨r, hr, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
    · apply InRegions_append_cons.mpr
      left
      rw [eA] at hc
      exact hc
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
  · intro a n h
    obtain ⟨r, hr, hc⟩ := hp.writes a n h
    exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩
  · intro s' rd wr cs frame ⟨s₂, mem₂, gpr₂, post⟩
    rw [block_stack] at frame
    change (blockContract d).post (sE.withRegions _ _) s₂ at post
    simp only [blockContract, State.withRegions_mem, arg_withRegions,
      a0, a1, mem₂] at post
    have stackFrame := callEntry_frame fit hrs
    change Frame [below (s.gpr .esp) 16] s.mem sE.mem at stackFrame
    refine ⟨?_, cs, rd, wr, frame, ?_⟩
    · intro r hr
      have fact : ∀ r ∈ kept, r ∈ calleeSaved := by decide
      exact cs r (fact r hr)
    · rw [post,
        VG.Proof.TripleDes.scheduleAt_eq_of_frame (p := addr32 (s.gpr .ebx)) stackFrame
          (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact hp.stackKey.symm),
        VG.Proof.TripleDes.blockAt_eq_of_frame (p := addr32 (s.gpr .esi)) stackFrame
          (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact hp.stackData.symm)]

end VG.Proof.TripleDes.X86.Ecb

end

/-! ## `Pre` -/

section

/-! # Permissions and separation for one ECB step -/

namespace VG.Proof.TripleDes.X86.Ecb

open VG VG.X86
open VG.Proof.Rc2.X86 (addr32 addr_add)

abbrev keyR (s : State) : Region := ⟨addr32 (s.gpr .ebx), 384⟩
abbrev dataR (s : State) (n : Nat := 1) : Region := ⟨addr32 (s.gpr .esi), 8 * n⟩
abbrev bufR (s : State) : Region := ⟨addr32 (s.gpr .ebp), 1024⟩

structure StepPre (s : State) (n : Nat := 1) : Prop where
  reads : Covers [keyR s, dataR s n, bufR s] (s.rd ++ s.wr)
  writes : Covers [dataR s n, bufR s] s.wr
  keyData : (keyR s).Disjoint (dataR s n)
  keyBuf : (keyR s).Disjoint (bufR s)
  dataBuf : (dataR s n).Disjoint (bufR s)
  keyFit : (s.gpr .ebx).toNat + 384 ≤ 2 ^ 32
  dataFit : (s.gpr .esi).toNat + 8 * n ≤ 2 ^ 32
  bufFit : (s.gpr .ebp).toNat + 1024 ≤ 2 ^ 32
  stackLo : 16 ≤ (s.gpr .esp).toNat
  stackKey : (below (s.gpr .esp) 16).Disjoint (keyR s)
  stackData : (below (s.gpr .esp) 16).Disjoint (dataR s n)
  stackBuf : (below (s.gpr .esp) 16).Disjoint (bufR s)

theorem StepPre.transport {s s' : State} {n : Nat} (hp : StepPre s n)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (regs : ∀ r ∈ kept, s'.gpr r = s.gpr r) : StepPre s' n := by
  have a := regs .ebx (by decide)
  have c := regs .esi (by decide)
  have d := regs .ebp (by decide)
  have sp := regs .esp (by decide)
  constructor
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.reads
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.writes
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.keyData
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.keyBuf
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.dataBuf
  · simpa only [a] using hp.keyFit
  · simpa only [c] using hp.dataFit
  · simpa only [d] using hp.bufFit
  · rw [sp]; exact hp.stackLo
  · simpa only [keyR, sp, a] using hp.stackKey
  · simpa only [dataR, sp, c] using hp.stackData
  · simpa only [bufR, sp, d] using hp.stackBuf

theorem StepPre.call {s : State} (hp : StepPre s) : CallPre s := by
  constructor
  · have hc : Covers [⟨addr32 (s.gpr .ebx), 384⟩, ⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 512⟩]
        [keyR s, dataR s, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨keyR s, by simp, 0, by simp, by simp⟩
      · exact ⟨dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.reads a n (hc a n h)
  · have hc : Covers [⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 512⟩] [dataR s, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.writes a n (hc a n h)
  · exact hp.keyBuf.sub_right (Region.sub_prefix (by decide))
  · exact hp.dataBuf.sub_right (Region.sub_prefix (by decide))
  · exact hp.keyFit
  · exact hp.dataFit
  · omega_using [hp.bufFit]
  · exact hp.stackLo
  · exact hp.stackKey
  · exact hp.stackData
  · exact hp.stackBuf.sub_right (Region.sub_prefix (by decide))


end VG.Proof.TripleDes.X86.Ecb

end

/-! ## `Slice` -/

section

/-! # Restricting ECB permissions to a consecutive subrange -/

namespace VG.Proof.TripleDes.X86.Ecb

open VG VG.X86
open VG.Proof.Rc2.X86 (addr32 addr_add)

theorem StepPre.slice {s s' : State} {n m i : Nat} (hp : StepPre s n) (bound : i + m ≤ n) (hm : 1 ≤ m)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (key : s'.gpr .ebx = s.gpr .ebx)
    (buf : s'.gpr .ebp = s.gpr .ebp)
    (sp : s'.gpr .esp = s.gpr .esp)
    (ptr : s'.gpr .esi = s.gpr .esi + BitVec.ofNat 32 (8 * i)) : StepPre s' m := by
  have fit : (s.gpr .esi).toNat + 8 * i < 2 ^ 32 := by omega_using [hp.dataFit, bound, hm]
  have ptrAddr : addr32 (s'.gpr .esi) = addr32 (s.gpr .esi) + BitVec.ofNat 64 (8 * i) := by
    rw [ptr, addr_add fit]
  have sub : Region.Sub (dataR s' m) (dataR s n) := by
    change Region.Sub ⟨addr32 (s'.gpr .esi), 8 * m⟩ ⟨addr32 (s.gpr .esi), 8 * n⟩
    rw [ptrAddr]
    exact Offset.sub_base _ (by omega)
  constructor
  · have hc : Covers [keyR s', dataR s' m, bufR s'] [keyR s, dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨keyR s, by simp, 0, by simp [key], by simp⟩
      · exact ⟨dataR s n, by simp, 8 * i, ptrAddr, by change 8 * i + 8 * m ≤ 8 * n; omega⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [rd, wr]
    exact fun a k h => hp.reads a k (hc a k h)
  · have hc : Covers [dataR s' m, bufR s'] [dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨dataR s n, by simp, 8 * i, ptrAddr, by change 8 * i + 8 * m ≤ 8 * n; omega⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [wr]
    exact fun a k h => hp.writes a k (hc a k h)
  · simpa only [keyR, key] using hp.keyData.sub_right sub
  · simpa only [keyR, bufR, key, buf] using hp.keyBuf
  · simpa only [bufR, buf] using hp.dataBuf.sub_left sub
  · rw [key]; exact hp.keyFit
  · rw [ptr]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using [fit] : 8 * i < 2 ^ 32), Nat.mod_eq_of_lt fit]
    omega_using [hp.dataFit, bound]
  · rw [buf]; exact hp.bufFit
  · rw [sp]; exact hp.stackLo
  · simpa only [keyR, key, sp] using hp.stackKey
  · rw [sp]; exact hp.stackData.sub_right sub
  · simpa only [bufR, buf, sp] using hp.stackBuf

theorem StepPre.head {s : State} {n : Nat} (hp : StepPre s n) (hn : 1 ≤ n) : StepPre s :=
  hp.slice (i := 0) hn (by decide) rfl rfl rfl rfl rfl (by simp)

end VG.Proof.TripleDes.X86.Ecb

end

/-! ## `Steps` -/

section

namespace VG.Proof.TripleDes.X86.Ecb
open VG VG.X86 VG.X86.RegUpd VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (Keep)

theorem advance_ok (s : State) :
    ∃ s', runBlock isa Impl.TripleDes.X86.Ecb.advance s = some s' ∧
      s'.gpr .esi = s.gpr .esi + 8 ∧ s'.gpr .edi = s.gpr .edi - 1 ∧
      isa.eval .ne s' = some (!(s.gpr .edi - 1 == 0)) ∧ Keep [.esi, .edi] s s' := by
  refine ⟨_, by
    simp only [Impl.TripleDes.X86.Ecb.advance, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, Option.bind_some, gpr_setReg, gpr_arithFlags,
      reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
  · rfl
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2, ite_false]

theorem counter_branch (x : BitVec 32) (hlo : 0 < x.toNat) :
    ((x - 1) != (0 : BitVec 32)) = decide (1 < x.toNat) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, decide_eq_true_eq]
  bv_omega_using [hlo]

end VG.Proof.TripleDes.X86.Ecb

end

/-! ## `Body` -/

section

namespace VG.Proof.TripleDes.X86.Ecb
open VG VG.X86 VG.Spec.TripleDes
open VG.Proof.Rc2.X86 (addr32)

structure BodyPost (d : Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .esi = s.gpr .esi + 8
  count : s'.gpr .edi = BitVec.ofNat 32 (n - 1)
  flag : isa.eval .ne s' = some (decide (1 < n))
  reg : ∀ r ∈ kept, r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [dataR s, ⟨addr32 (s.gpr .ebp), 512⟩, below (s.gpr .esp) 16] s.mem s'.mem
  data : Spec.TripleDes.blockAt s'.mem (addr32 (s.gpr .esi)) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
      (Spec.TripleDes.blockAt s.mem (addr32 (s.gpr .esi)))

theorem body_ok (d : Direction) (s : State) (n : Nat) (hn : 1 ≤ n) (bound : n < 2 ^ 32)
    (count : s.gpr .edi = BitVec.ofNat 32 n) (hp : StepPre s) :
    WP isa (.seq (Impl.TripleDes.X86.Ecb.blockCall d) (.block Impl.TripleDes.X86.Ecb.advance)) s
      (BodyPost d s n) := by
  apply WP.seq
  apply WP.mono (call_ok d s hp.call)
  intro s₁ h₁
  obtain ⟨s₂, run₂, ptr₂, count₂, flag₂, keep₂⟩ := advance_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have count' : s₁.gpr .edi - 1 = BitVec.ofNat 32 (n - 1) := by
    rw [h₁.reg .edi (by decide), count]
    exact Offset.ofNat_sub_ofNat hn
  refine ⟨by rw [ptr₂, h₁.reg .esi (by decide)], count₂.trans count', ?_, ?_,
    keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr, ?_, ?_⟩
  · rw [flag₂]
    change some ((s₁.gpr .edi - 1) != (0 : BitVec 32)) = _
    have value : (s₁.gpr .edi).toNat = n := by
      rw [h₁.reg .edi (by decide), count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    rw [counter_branch _ (by rw [value]; omega_using [hn]), value]
  · intro r hr hs hb
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.reg r hr)
  · rw [keep₂.mem]; exact h₁.mem
  · rw [keep₂.mem]; exact h₁.output

theorem BodyPost.tail {d : Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (hn : 1 ≤ n) : StepPre s' n :=
  hp.slice (i := 1) (by omega) hn h.rd h.wr
    (h.reg .ebx (by decide) (by decide) (by decide))
    (h.reg .ebp (by decide) (by decide) (by decide))
    (h.reg .esp (by decide) (by decide) (by decide)) h.ptr

end VG.Proof.TripleDes.X86.Ecb

end

/-! ## `LoopFrame` -/

section

/-! # Frames for successive ECB blocks -/

namespace VG.Proof.TripleDes.X86.Ecb

open VG VG.X86
open VG.Proof.Rc2.X86 (addr32 addr_add)

def stepWrites (s : State) : List Region := [dataR s, ⟨addr32 (s.gpr .ebp), 512⟩, below (s.gpr .esp) 16]

def loopWrites (s : State) (n : Nat) : List Region := [dataR s n, ⟨addr32 (s.gpr .ebp), 512⟩, below (s.gpr .esp) 16]

theorem loopFrame_slice {s s' : State} {n m i : Nat} {a b : Mem}
    (h : Frame (loopWrites s' m) a b) (bound : i + m ≤ n) (fit : (s.gpr .esi).toNat + 8 * i < 2 ^ 32)
    (buf : s'.gpr .ebp = s.gpr .ebp)
    (sp : s'.gpr .esp = s.gpr .esp)
    (ptr : s'.gpr .esi = s.gpr .esi + BitVec.ofNat 32 (8 * i)) :
    Frame (loopWrites s n) a b := by
  apply h.sub
  intro r hr
  simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨dataR s n, by simp [loopWrites], ?_⟩
    change Region.Sub ⟨addr32 (s'.gpr .esi), 8 * m⟩ ⟨addr32 (s.gpr .esi), 8 * n⟩
    rw [ptr, addr_add fit]
    exact Offset.sub_base _ (by omega)
  · refine ⟨⟨addr32 (s.gpr .ebp), 512⟩, by simp [loopWrites], ?_⟩
    rw [buf]; exact fun _ h => h
  · refine ⟨below (s.gpr .esp) 16, by simp [loopWrites], ?_⟩
    rw [sp]; exact fun _ h => h

theorem BodyPost.frame {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hn : 1 ≤ n) : Frame (loopWrites s n) s.mem s'.mem :=
  loopFrame_slice (m := 1) (i := 0) h.mem hn (s.gpr .esi).isLt rfl rfl (by simp)

theorem BodyPost.schedule {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hp : StepPre s) :
    Spec.TripleDes.scheduleAt s'.mem (addr32 (s.gpr .ebx)) = Spec.TripleDes.scheduleAt s.mem (addr32 (s.gpr .ebx)) := by
  apply VG.Proof.TripleDes.scheduleAt_eq_of_frame _ h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.keyData
      (And.intro (hp.keyBuf.sub_right (Region.sub_prefix (by decide : 512 ≤ 1024))) hp.stackKey.symm)

theorem BodyPost.tailData {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64) :
    Spec.TripleDes.blocksAt s'.mem (addr32 (s.gpr .esi) + 8) n = Spec.TripleDes.blocksAt s.mem (addr32 (s.gpr .esi) + 8) n := by
  have sub : Region.Sub ⟨addr32 (s.gpr .esi) + 8, 8 * n⟩ (dataR s (n + 1)) :=
    Offset.sub_base _ (by change 8 + 8 * n ≤ 8 * (n + 1); omega)
  have sep : (Region.mk (addr32 (s.gpr .esi) + 8) (8 * n)).Disjoint (dataR s) :=
    Offset.disjoint_base _ (d := 8) (n := 8 * n) (k := 8) (by decide) (by omega)
  apply VG.Proof.TripleDes.blocksAt_frame h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro sep
      (And.intro ((hp.dataBuf.sub_left sub).sub_right (Region.sub_prefix (by decide : 512 ≤ 1024)))
        (hp.stackData.sub_right sub).symm)

theorem firstBlock_frame {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat} {m : Mem}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64)
    (frame : Frame (loopWrites s' n) s'.mem m) (hn : 1 ≤ n) :
    Spec.TripleDes.blockAt m (addr32 (s.gpr .esi)) = Spec.TripleDes.blockAt s'.mem (addr32 (s.gpr .esi)) := by
  have first : Region.Sub (dataR s) (dataR s (n + 1)) := Region.sub_prefix (by change 8 ≤ 8 * (n + 1); omega)
  have sep : (dataR s).Disjoint ⟨addr32 (s.gpr .esi) + 8, 8 * n⟩ :=
    Offset.base_disjoint _ (e := 8) (n := 8 * n) (k := 8) (by decide) (by omega)
  apply VG.Proof.TripleDes.blockAt_eq_of_frame _ frame
  have buf := h.reg .ebp (by decide) (by decide) (by decide)
  have ptrAddr : addr32 (s'.gpr .esi) = addr32 (s.gpr .esi) + 8 := by
    rw [h.ptr]
    exact addr_add (k := 8) (by omega_using [hp.dataFit, hn])
  have sp := h.reg .esp (by decide) (by decide) (by decide)
  simpa only [loopWrites, dataR, buf, ptrAddr, sp,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro sep
      (And.intro ((hp.dataBuf.sub_left first).sub_right (Region.sub_prefix (by decide : 512 ≤ 1024)))
        (hp.stackData.sub_right first).symm)

end VG.Proof.TripleDes.X86.Ecb

end

/-! ## `Loop` -/

section

/-! # Correctness of the ECB loop on complete blocks -/

namespace VG.Proof.TripleDes.X86.Ecb

open VG VG.X86
open VG.Proof.Rc2.X86 (addr32 addr_add)
open VG.Proof.TripleDes (blocksAt_cons)

structure LoopPost (d : Spec.TripleDes.Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .esi = s.gpr .esi + BitVec.ofNat 32 (8 * n)
  count : s'.gpr .edi = 0
  reg : ∀ r ∈ kept, r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (loopWrites s n) s.mem s'.mem
  data : Spec.TripleDes.blocksAt s'.mem (addr32 (s.gpr .esi)) n =
    Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
      (Spec.TripleDes.blocksAt s.mem (addr32 (s.gpr .esi)) n)

theorem ecb_cons (keys : Spec.TripleDes.Schedule) (d : Spec.TripleDes.Direction)
    (b : Spec.TripleDes.Block) (bs : List Spec.TripleDes.Block) :
    Spec.TripleDes.ecb keys d (b :: bs) = blockResult keys d b :: Spec.TripleDes.ecb keys d bs := by
  cases d <;> rfl

theorem loop_ok (d : Spec.TripleDes.Direction) (n : Nat) :
    ∀ s : State, 1 ≤ n → 8 * n ≤ 2 ^ 32 → StepPre s n → s.gpr .edi = BitVec.ofNat 32 n →
      WP isa (.loop (.seq (Impl.TripleDes.X86.Ecb.blockCall d) (.block Impl.TripleDes.X86.Ecb.advance)) .ne) s (LoopPost d s n) := by
  induction n with
  | zero => intro s hn; omega
  | succ n ih =>
    intro s hn bound hp count
    obtain ⟨t₁, s₁, exec₁, h₁⟩ := body_ok d s (n + 1) hn (by omega) count (hp.head hn)
    by_cases hz : n = 0
    · subst n
      refine ⟨_, s₁, Exec.loopExit exec₁ ?_, ?_⟩
      · change isa.eval .ne s₁ = some false
        simpa only [Nat.zero_add, Nat.lt_irrefl, decide_false] using h₁.flag
      · refine ⟨h₁.ptr, h₁.count, h₁.reg, h₁.rd, h₁.wr, h₁.frame (by decide), ?_⟩
        · rw [blocksAt_cons, blocksAt_cons, ecb_cons]
          simp only [Spec.TripleDes.blocksAt, List.range_zero, List.map_nil,
            Spec.TripleDes.ecb, List.map_nil]
          exact congrArg (· :: []) h₁.data
    · have hp₁ := h₁.tail hp (by omega)
      obtain ⟨t₂, s₂, exec₂, h₂⟩ := ih s₁ (by omega) (by omega) hp₁ (by simpa using h₁.count)
      refine ⟨_, s₂, Exec.loopNext exec₁ ?_ exec₂, ?_⟩
      · change isa.eval .ne s₁ = some true
        simpa only [show 1 < n + 1 by omega, decide_true] using h₁.flag
      · have key := h₁.schedule (hp.head hn)
        have tail := h₁.tailData hp (by omega_using [bound])
        have data := h₂.data
        have ki := h₁.reg .ebx (by decide) (by decide) (by decide)
        have bi := h₁.reg .ebp (by decide) (by decide) (by decide)
        have ptrAddr : addr32 (s₁.gpr .esi) = addr32 (s.gpr .esi) + 8 := by
          rw [h₁.ptr]
          exact addr_add (k := 8) (by omega_using [hp.dataFit, hz])
        rw [ki, ptrAddr, key, tail] at data
        refine ⟨?_, h₂.count, ?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, ?_, ?_⟩
        · rw [h₂.ptr, h₁.ptr, BitVec.add_assoc]
          exact congrArg (s.gpr .esi + ·) (by
            change BitVec.ofNat 32 8 + BitVec.ofNat 32 (8 * n) = _
            rw [← BitVec.ofNat_add]
            exact congrArg (BitVec.ofNat 32) (by omega))
        · intro r hr hs hb
          exact (h₂.reg r hr hs hb).trans (h₁.reg r hr hs hb)
        · exact (h₁.frame hn).trans (loopFrame_slice (i := 1) h₂.mem (by omega) (by omega_using [hp.dataFit, hz]) bi (h₁.reg .esp (by decide) (by decide) (by decide)) h₁.ptr)
        · have first := firstBlock_frame h₁ hp (by omega_using [bound]) h₂.mem (by omega)
          rw [blocksAt_cons, first, h₁.data, data, blocksAt_cons, ecb_cons]

theorem maybeLoop_ok (d : Spec.TripleDes.Direction) (s : State) (n : Nat) (bound : 8 * n ≤ 2 ^ 32)
    (hp : StepPre s n) (count : s.gpr .edi = BitVec.ofNat 32 n)
    (initialFlag : isa.eval .e s = some (decide (n = 0)))
    :
    WP isa (.ite .e (.block []) (.loop (.seq (Impl.TripleDes.X86.Ecb.blockCall d) (.block Impl.TripleDes.X86.Ecb.advance)) .ne)) s (LoopPost d s n) := by
  have flag' := initialFlag
  by_cases hz : n = 0
  · subst n
    apply WP.ite true (by change isa.eval .e s = some true; simpa only [decide_true] using flag')
    · intro _
      apply WP.block_nil
      refine ⟨by simp, count, fun _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _, ?_⟩
      · rfl
    · simp
  · apply WP.ite false (by change isa.eval .e s = some false; simpa only [hz, decide_false] using flag')
    · simp
    · intro _
      exact loop_ok d n s (by omega) bound hp count


end VG.Proof.TripleDes.X86.Ecb

end

/-! ## `IO` -/

section

namespace VG.Proof.TripleDes.X86.Ecb
open VG VG.X86 VG.X86.Straight VG.X86.RegUpd VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (Keep addr32)

theorem subtract_zero (x : BitVec 32) : x - (0 : BitVec 32) = x := by bv_omega

def savedMem (s : State) : Mem :=
  (((s.mem.writeW (addr32 (s.gpr .eax) + BitVec.ofNat 64 512) (s.gpr .ebp)).writeW
    (addr32 (s.gpr .eax) + BitVec.ofNat 64 516) (s.gpr .ebx)).writeW
    (addr32 (s.gpr .eax) + BitVec.ofNat 64 520) (s.gpr .esi)).writeW
    (addr32 (s.gpr .eax) + BitVec.ofNat 64 524) (s.gpr .edi)

theorem save_ok (s : State) (fit : (s.gpr .eax).toNat + 1024 ≤ 2 ^ 32)
    (hw : ∀ k ∈ [512, 516, 520, 524], InRegions s.wr (addr (s.gpr .eax) k) 4) :
    ∃ s', runBlock isa Impl.TripleDes.X86.Ecb.save s = some s' ∧ Keep [] {s with mem := savedMem s} s' := by
  have h0 := hw 512 (by decide)
  have h1 := hw 516 (by decide)
  have h2 := hw 520 (by decide)
  have h3 := hw 524 (by decide)
  simp only [addr] at h0 h1 h2 h3
  refine ⟨_, by
    change runBlock isa [.store (memOp .eax 512) .ebp, .store (memOp .eax 516) .ebx,
      .store (memOp .eax 520) .esi, .store (memOp .eax 524) .edi] s = _
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store32, State.ea,
      memOp, h0, h1, h2, h3, ite_true]
    rfl, ?_⟩
  refine ⟨fun _ _ => rfl, ?_, rfl, rfl⟩
  change (((s.mem.writeW (addr (s.gpr .eax) 512) (s.gpr .ebp)).writeW
    (addr (s.gpr .eax) 516) (s.gpr .ebx)).writeW
    (addr (s.gpr .eax) 520) (s.gpr .esi)).writeW
    (addr (s.gpr .eax) 524) (s.gpr .edi) = savedMem s
  unfold savedMem
  rw [addr_eq (by omega_using [fit] : (s.gpr .eax).toNat + 512 < 2 ^ 32),
    addr_eq (by omega_using [fit] : (s.gpr .eax).toNat + 516 < 2 ^ 32),
    addr_eq (by omega_using [fit] : (s.gpr .eax).toNat + 520 < 2 ^ 32),
    addr_eq (by omega_using [fit] : (s.gpr .eax).toNat + 524 < 2 ^ 32)]
  rfl

theorem savedMem_frame (s : State) :
    Frame [⟨addr32 (s.gpr .eax), 1024⟩] s.mem (savedMem s) := by
  unfold savedMem
  apply Frame.writeW _ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  apply Frame.writeW _ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  apply Frame.writeW _ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains_base _ (by decide) (by decide))

theorem setup_ok (s : State)
    (hr : ∀ i ∈ [1, 2, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4) :
    ∃ s', runBlock isa Impl.TripleDes.X86.Ecb.setup s = some s' ∧
      s'.gpr .ebp = s.gpr .eax ∧ s'.gpr .ebx = arg s 0 ∧ s'.gpr .esi = arg s 1 ∧
      s'.gpr .edi = arg s 2 ∧ isa.eval .e s' = some (arg s 2 == 0) ∧
      Keep [.ebp, .ebx, .esi, .edi] s s' := by
  have h0 := hr 1 (by decide)
  have h1 := hr 2 (by decide)
  have h2 := hr 3 (by decide)
  simp only [wordAddr, addr] at h0 h1 h2
  refine ⟨_, by
    simp only [Impl.TripleDes.X86.Ecb.setup, rr, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.load32, State.ea, memOp, h0, h1, h2, ite_true,
      Option.bind_some, Option.map_some, gpr_setReg, mem_setReg, rd_setReg,
      wr_setReg, reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact (argument_word s 0).symm
  · exact (argument_word s 1).symm
  · exact (argument_word s 2).symm
  · change some (((s.mem.readW (wordAddr (s.gpr .esp) 3) 32) - (0 : BitVec 32)) == (0 : BitVec 32)) = _
    rw [← argument_word s 2]
    exact congrArg (fun x : BitVec 32 => some (x == 0)) (subtract_zero (arg s 2))
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem restore_ok (original s : State)
    (hr : ∀ k ∈ [512, 516, 520, 524], InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) k) 4)
    (hv : ∀ i < 4, s.mem.readW (addr (s.gpr .ebp) (512 + 4 * i)) 32 = original.gpr (savedReg i)) :
    ∃ s', runBlock isa Impl.TripleDes.X86.Ecb.restore s = some s' ∧
      (∀ r ∈ savedRegs, s'.gpr r = original.gpr r) ∧
      Keep (.eax :: savedRegs) s s' := by
  have h0 := hr 512 (by decide)
  have h1 := hr 516 (by decide)
  have h2 := hr 520 (by decide)
  have h3 := hr 524 (by decide)
  have v0 := hv 0 (by decide)
  have v1 := hv 1 (by decide)
  have v2 := hv 2 (by decide)
  have v3 := hv 3 (by decide)
  simp only [addr] at h0 h1 h2 h3
  refine ⟨_, by
    change runBlock isa [rr .eax .ebp, .mov .ebp (.mem (memOp .eax 512)),
      .mov .ebx (.mem (memOp .eax 516)), .mov .esi (.mem (memOp .eax 520)),
      .mov .edi (.mem (memOp .eax 524))] s = _
    simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load32, State.ea, memOp, h0, h1, h2, h3, ite_true, Option.map_some,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, reduceCtorEq, ite_false]
    rfl, ?_, ?_⟩
  · intro r hr
    simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact v0
    · exact v1
    · exact v2
    · exact v3
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

theorem loadScratch_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 4) 4) :
    ∃ s', runBlock isa [.mov .eax (.mem (memOp .esp 16))] s = some s' ∧
      s'.gpr .eax = arg s 3 ∧ Keep [.eax] s s' := by
  have he : exec (.mov .eax (.mem (memOp .esp 16))) s = some (s.setReg .eax (arg s 3)) := by
    simp only [exec, readSrc, State.load32, State.ea, memOp]
    change (if InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 4) 4 then
      some (s.mem.readW (wordAddr (s.gpr .esp) 4) 32) else none).map (s.setReg .eax) = _
    rw [ite_eq_left hr, ← argument_word s 3, Option.map_some]
  refine ⟨s.setReg .eax (arg s 3), by simp only [runBlock_cons, he, runStep_some, runBlock_nil],
    gpr_setReg_self _ _ _, ?_⟩
  exact ⟨fun r hr => gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using hr), rfl, rfl, rfl⟩

theorem savedMem_eq (s : State) : savedMem s = VG.Proof.Rc2.X86.saveMem s.mem
    (addr32 (s.gpr .eax) + BitVec.ofNat 64 512) (fun i => s.gpr (savedReg i)) 4 := by
  simp only [VG.Proof.Rc2.X86.saveMem_succ]
  change savedMem s = (((s.mem.writeW ((addr32 (s.gpr .eax) + BitVec.ofNat 64 512) + BitVec.ofNat 64 0) (s.gpr .ebp)).writeW
    ((addr32 (s.gpr .eax) + BitVec.ofNat 64 512) + BitVec.ofNat 64 4) (s.gpr .ebx)).writeW
    ((addr32 (s.gpr .eax) + BitVec.ofNat 64 512) + BitVec.ofNat 64 8) (s.gpr .esi)).writeW
    ((addr32 (s.gpr .eax) + BitVec.ofNat 64 512) + BitVec.ofNat 64 12) (s.gpr .edi)
  simp only [Offset.add_ofNat_add_ofNat]
  rfl

theorem savedMem_read (s : State) (i : Nat) (hi : i < 4) :
    (savedMem s).readW (addr32 (s.gpr .eax) + BitVec.ofNat 64 (512 + 4 * i)) 32 =
      s.gpr (savedReg i) := by
  rw [savedMem_eq, ← Offset.add_ofNat_add_ofNat]
  exact VG.Proof.Rc2.X86.saveMem_read _ _ _ 4 (by decide) i hi

theorem LoopPost.scratchRead {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : LoopPost d s n s') (hp : StepPre s n) (i : Nat) (hi : 512 ≤ i ∧ i + 4 ≤ 1024) :
    s'.mem.readW (addr32 (s.gpr .ebp) + BitVec.ofNat 64 i) 32 =
      s.mem.readW (addr32 (s.gpr .ebp) + BitVec.ofNat 64 i) 32 := by
  have sub : Region.Sub ⟨addr32 (s.gpr .ebp) + BitVec.ofNat 64 i, 4⟩ (bufR s) :=
    Offset.sub_base _ hi.2
  have sep : (Region.mk (addr32 (s.gpr .ebp) + BitVec.ofNat 64 i) 4).Disjoint
      ⟨addr32 (s.gpr .ebp), 512⟩ := Offset.disjoint_base _ (by omega_using [hi]) (by omega_using [hi])
  apply h.mem.readW (r := ⟨addr32 (s.gpr .ebp) + BitVec.ofNat 64 i, 4⟩)
    (Region.contains_self _ _) (hn := by decide)
  simpa only [loopWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.dataBuf.sub_right sub).symm)
      (And.intro sep (hp.stackBuf.sub_right sub).symm)

end VG.Proof.TripleDes.X86.Ecb

end

/-! ## `Contract` -/

section

namespace VG.Proof.TripleDes.X86.Ecb
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)

def contract (d : Spec.TripleDes.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨addr32 (arg s 0), 384⟩
    let data : Region := ⟨addr32 (arg s 1), 8 * (arg s 2).toNat⟩
    let buf : Region := ⟨addr32 (arg s 3), 1024⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨addr32 (s.gpr .esp), 4⟩
    let stack := below (s.gpr .esp) 16
    s.rd = [key, args] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧ args.Disjoint data ∧ args.Disjoint buf ∧
      ret.Disjoint data ∧ ret.Disjoint buf ∧ stack.Disjoint key ∧ stack.Disjoint data ∧
      stack.Disjoint buf ∧ (arg s 0).toNat + 384 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 1024 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
      16 ≤ (s.gpr .esp).toNat ∧ (arg s 1).toNat + 8 * (arg s 2).toNat ≤ 2 ^ 32
  post s s' := Spec.TripleDes.blocksAt s'.mem (addr32 (arg s 1)) (arg s 2).toNat =
    Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (addr32 (arg s 0))) d
      (Spec.TripleDes.blocksAt s.mem (addr32 (arg s 1)) (arg s 2).toNat)
  pub s t := s.gpr .esp = t.gpr .esp ∧ ∀ i < 4, arg s i = arg t i

end VG.Proof.TripleDes.X86.Ecb

end

/-! ## `Correct` -/

section

namespace VG.Proof.TripleDes.X86.Ecb
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32 argContainsCount)

theorem counter_zero (x : BitVec 32) : (x == 0) = decide (x.toNat = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact BitVec.eq_of_toNat_eq (show x.toNat = (0 : BitVec 32).toNat from h)

theorem ecb_correct (d : Spec.TripleDes.Direction) (s : State) (hs : (contract d).pre s) :
    WP isa (Impl.TripleDes.X86.Ecb.ecb d) s (fun s' => abiPreserved s s' ∧ (contract d).post s s') := by
  obtain ⟨rd, wr, keyData, keyBuf, dataBuf, argsData, argsBuf, retData, retBuf,
    stackKey, stackData, stackBuf, keyFit, bufFit, spFit, stackLo, fit⟩ := hs
  have writes (i : Nat) (hi : i + 4 ≤ 1024) : InRegions s.wr
      (addr32 (arg s 3) + BitVec.ofNat 64 i) 4 := by
    rw [wr]
    exact ⟨⟨addr32 (arg s 3), 1024⟩, by simp, Offset.contains_base _ hi (by omega_using [hi])⟩
  have argRead (i : Nat) (hlo : 1 ≤ i) (hhi : i ≤ 4) :
      InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4 := by
    rw [rd, wr, wordAddr, addr_eq (by omega_using [spFit, hhi])]
    have hc := argContainsCount s 4 spFit (i - 1) (by omega_using [hlo, hhi])
    rw [show 4 + 4 * (i - 1) = 4 * i by omega_using [hlo]] at hc
    exact ⟨⟨argAddr s 0, 16⟩, by simp, hc⟩
  rw [Impl.TripleDes.X86.Ecb.ecb]
  apply WP.seq
  obtain ⟨s₀, run₀, buf₀, keep₀⟩ := loadScratch_ok s (argRead 4 (by decide) (by decide))
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  have g₀ (r : Reg) (hr : r ≠ .eax) := keep₀.reg r (by simpa only [List.mem_singleton] using hr)
  apply WP.seq
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := save_ok s₀ (by rw [buf₀]; exact bufFit) (by
    intro k hk
    rw [keep₀.wr, buf₀, addr_eq (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> omega_using [bufFit])]
    exact writes k (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s₀.gpr r := keep₁.reg r (by simp)
  have sp₁ : s₁.gpr .esp = s.gpr .esp := (g₁ .esp).trans (g₀ .esp (by decide))
  have saveFrame : Frame [⟨addr32 (arg s 3), 1024⟩] s.mem s₁.mem := by
    rw [keep₁.mem, ← keep₀.mem, ← buf₀]; exact savedMem_frame s₀
  have args₁ := VG.Proof.Rc2.X86.arguments_frame 4 saveFrame sp₁ spFit
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact argsBuf)
  have reads₁ : ∀ i ∈ [1, 2, 3], InRegions (s₁.rd ++ s₁.wr) (wordAddr (s₁.gpr .esp) i) 4 := by
    intro i hi
    rw [keep₁.rd, keep₁.wr, keep₀.rd, keep₀.wr, sp₁]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact argRead 1 (by decide) (by decide)
    · exact argRead 2 (by decide) (by decide)
    · exact argRead 3 (by decide) (by decide)
  obtain ⟨s₂, run₂, buf₂, key₂, data₂, count₂, flag₂, keep₂⟩ := setup_ok s₁ reads₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [args₁ 0 (by decide)] at key₂
  rw [args₁ 1 (by decide)] at data₂
  rw [args₁ 2 (by decide)] at count₂ flag₂
  rw [g₁, buf₀] at buf₂
  have sp₂ := (keep₂.reg .esp (by decide)).trans sp₁
  have rd₂ := keep₂.rd.trans (keep₁.rd.trans keep₀.rd)
  have wr₂ := keep₂.wr.trans (keep₁.wr.trans keep₀.wr)
  have mem₂ : s₂.mem = savedMem s₀ := keep₂.mem.trans keep₁.mem
  have scratchFrame : Frame [⟨addr32 (arg s 3), 1024⟩] s.mem s₂.mem := by
    rw [mem₂, ← keep₀.mem, ← buf₀]; exact savedMem_frame s₀
  have initialKey := VG.Proof.TripleDes.scheduleAt_eq_of_frame (addr32 (arg s 0)) scratchFrame
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact keyBuf)
  have initialData := VG.Proof.TripleDes.blocksAt_frame scratchFrame (addr32 (arg s 1)) (arg s 2).toNat
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact dataBuf)
  have hp₂ : StepPre s₂ (arg s 2).toNat := by
    constructor
    · simp only [Covers, keyR, dataR, bufR, key₂, data₂, buf₂, rd₂, wr₂, rd, wr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with h | h | h <;> simp_all only [or_true, true_or], hc⟩
    · simp only [dataR, bufR, data₂, buf₂, wr₂, wr]
      exact fun _ _ h => h
    · simpa only [keyR, dataR, key₂, data₂] using keyData
    · simpa only [keyR, bufR, key₂, buf₂] using keyBuf
    · simpa only [dataR, bufR, data₂, buf₂] using dataBuf
    · rw [key₂]; exact keyFit
    · rw [data₂]; exact fit
    · rw [buf₂]; exact bufFit
    · rw [sp₂]; exact stackLo
    · simpa only [keyR, sp₂, key₂] using stackKey
    · simpa only [dataR, sp₂, data₂] using stackData
    · simpa only [bufR, sp₂, buf₂] using stackBuf
  apply WP.seq
  apply WP.mono (maybeLoop_ok d s₂ (arg s 2).toNat (by omega_using [fit]) hp₂
    (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using count₂)
    (flag₂.trans (congrArg some (counter_zero (arg s 2)))))
  intro s₃ h₃
  have rd₃ := h₃.rd.trans rd₂
  have wr₃ := h₃.wr.trans wr₂
  have buf₃ := (h₃.reg .ebp (by decide) (by decide) (by decide)).trans buf₂
  have reads₃ : ∀ k ∈ [512, 516, 520, 524], InRegions (s₃.rd ++ s₃.wr) (addr (s₃.gpr .ebp) k) 4 := by
    intro k hk
    have bound : k + 4 ≤ 1024 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> decide
    rw [rd₃, wr₃, buf₃, addr_eq (by omega_using [bufFit, bound])]
    obtain ⟨r, hr, hc⟩ := writes k bound
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have stored₃ : ∀ i < 4, s₃.mem.readW (addr (s₃.gpr .ebp) (512 + 4 * i)) 32 = s.gpr (savedReg i) := by
    intro i hi
    have h := h₃.scratchRead hp₂ (512 + 4 * i) (by omega_using [hi])
    rw [buf₂, mem₂, ← buf₀, savedMem_read s₀ i hi] at h
    rw [buf₀] at h
    rw [buf₃, addr_eq (by omega_using [bufFit, hi])]
    have reg : savedReg i ≠ .eax := (show ∀ i < 4, savedReg i ≠ .eax by decide) i hi
    exact h.trans (g₀ _ reg)
  obtain ⟨s₄, run₄, saved₄, keep₄⟩ := restore_ok s s₃ reads₃ stored₃
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  constructor
  · constructor
    · intro r hr
      have regs : ∀ r ∈ calleeSaved, r ∈ savedRegs ∨ r = .esp := by decide
      rcases regs r hr with saved | rfl
      · exact saved₄ r saved
      · rw [keep₄.reg .esp (by decide), h₃.reg .esp (by decide) (by decide) (by decide), sp₂]
    · have stackRet : (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint (below (s.gpr .esp) 16) := by
        change (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint ⟨_, 16⟩
        rw [VG.X86.Taint.sub_setWidth stackLo]
        exact Offset.base_disjoint_below _ (by decide)
      have retSep : ∀ r ∈ loopWrites s₂ (arg s 2).toNat, (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint r := by
        simpa only [loopWrites, dataR, data₂, buf₂, sp₂,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
          And.intro retData (And.intro (retBuf.sub_right (Region.sub_prefix (by decide : 512 ≤ 1024))) stackRet)
      change s₄.mem.readW (addr32 (s.gpr .esp)) 32 = s.mem.readW (addr32 (s.gpr .esp)) 32
      rw [keep₄.mem, h₃.mem.readW (Region.contains_self _ _) retSep (by decide),
        scratchFrame.readW (Region.contains_self _ _) (by
          intro r hr; obtain rfl := List.mem_singleton.mp hr; exact retBuf) (by decide)]
  · have out := h₃.data
    rw [key₂, data₂, initialKey, initialData] at out
    change Spec.TripleDes.blocksAt s₄.mem (addr32 (arg s 1)) (arg s 2).toNat = _
    rw [keep₄.mem]; exact out

end VG.Proof.TripleDes.X86.Ecb

end

/-! ## `ConstantTime` -/

section

namespace VG.Proof.TripleDes.X86.Ecb
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)

theorem ecbTaint_wf {d : Spec.TripleDes.Direction} {s : State} (hs : (contract d).pre s) : VG.X86.Taint.Wf ecbTaint s := by
  obtain ⟨_, hwr, _, _, dataSep, argsData, argsScratch, retData, retScratch, _, stackData, stackBuf, _, scratchFit, spFit, stackLo, dataFit⟩ := hs
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨spFit, ?_⟩, ?_⟩ ?_
  · rw [hwr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨dataSep, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr32, BitVec.toNat_setWidth] <;> omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) retData argsData
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) retScratch argsScratch
  · intro p hp
    simp only [ecbTaint, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, addr32, arg, argAddr]
  · intro _
    refine ⟨stackLo, ?_⟩
    intro r hr
    have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16 =
        (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 := (VG.X86.Taint.sub_setWidth stackLo).symm
    change (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16, 16⟩ : Region).Disjoint r
    rw [e]
    simp only [hwr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact stackData
    · exact stackBuf

theorem ecbTaint_agree {d : Spec.TripleDes.Direction} {s t : State} (hs : (contract d).pre s)
    (ht : (contract d).pre t) (hp : (contract d).pub s t) :
    VG.X86.Taint.Agree ecbTaint s t := by
  obtain ⟨sp, args⟩ := hp
  have fit : ∀ s, (contract d).pre s → (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 := by
    intro s hs; obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _, _⟩ := hs; exact h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, ecbTaint_wf hs,
    ecbTaint_wf ht, VG.X86.Taint.slotsOk_empty,
    VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [ecbTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [hs.2.1, ht.2.1, args 1 (by decide), args 2 (by decide), args 3 (by decide)]
  · simp only [ecbTaint] at hk
    rw [show VG.X86.Taint.depth ecbTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (fit _ hs) h4 hk, VG.X86.Taint.argByte_eq (fit _ ht) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))

end VG.Proof.TripleDes.X86.Ecb

end

/-! ## `Verified` -/

section

namespace VG.Proof.TripleDes.X86.Ecb
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)

def wideContract (d : Spec.TripleDes.Direction) : Contract isa :=
  { contract d with
    pre := fun s =>
    let key : Region := ⟨addr32 (arg s 0), 384⟩
    let data : Region := ⟨addr32 (arg s 1), 8 * (arg s 2).toNat⟩
    let buf : Region := ⟨addr32 (arg s 3), 1024⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨addr32 (s.gpr .esp), 4⟩
    let stack := below (s.gpr .esp) 16
    s.rd = [key] ∧ s.wr = [data, buf, args] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧ args.Disjoint data ∧ args.Disjoint buf ∧
      ret.Disjoint data ∧ ret.Disjoint buf ∧ stack.Disjoint key ∧ stack.Disjoint data ∧
      stack.Disjoint buf ∧ (arg s 0).toNat + 384 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 1024 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
      16 ≤ (s.gpr .esp).toNat ∧ (arg s 1).toNat + 8 * (arg s 2).toNat ≤ 2 ^ 32 }

def narrowRd (s : State) : List Region := [⟨addr32 (arg s 0), 384⟩, ⟨argAddr s 0, 16⟩]
def narrowWr (s : State) : List Region :=
  [⟨addr32 (arg s 1), 8 * (arg s 2).toNat⟩, ⟨addr32 (arg s 3), 1024⟩]

local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [VG.Proof.TripleDes.X86.Ecb.contract, VG.Proof.TripleDes.X86.Ecb.wideContract,
    VG.Proof.TripleDes.X86.Ecb.narrowRd, VG.Proof.TripleDes.X86.Ecb.narrowWr, VG.X86.arg_withRegions,
    VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
    VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $(loc)?)

theorem wide_pre (d : Spec.TripleDes.Direction) (s : State) (h : (wideContract d).pre s) :
    (contract d).pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  obtain ⟨_, _, h⟩ := h
  narrow
  exact ⟨trivial, trivial, h⟩

def satState : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else if a = 0x4011 then 0x30 else 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 1024⟩, ⟨0x4004, 16⟩]

theorem wide_implies (d : Spec.TripleDes.Direction) :
    (wideContract d).Implies (Proof.TripleDes.ecbScratchContract abi d 16) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.TripleDes.ecbScratchContract, Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argSlots, argVal, argBytes, addr32, wideContract, contract, below] at h
    sig_split h
    sig_reduce [Proof.TripleDes.ecbScratchContract, Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argSlots, argVal, argBytes, addr32, wideContract, contract, below]
    sig_simp [Proof.TripleDes.ecbScratchContract, Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argSlots, argVal, argBytes, addr32, wideContract, contract, below] []
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (rw [Taint.sub_setWidth (by omega)]; simp only [Nat.mul_comm] at *; with_reducible assumption)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.TripleDes.ecbScratchContract, Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argSlots, argVal, argBytes, addr32, wideContract, contract, below]
  · sig_implies_pub [Proof.TripleDes.ecbScratchContract, Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argSlots, argVal, argBytes, addr32, wideContract, contract, below]
  · sig_implies_sat [Proof.TripleDes.ecbScratchContract, Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argSlots, argVal, argBytes, addr32, wideContract, contract, below]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem ecb_constantTime (d : Spec.TripleDes.Direction) :
    ConstantTime isa (contract d).pre (contract d).pub (Impl.TripleDes.X86.Ecb.ecb d) := by
  cases d
  · exact ecbEncrypt_constantTime _ _ (fun _ _ h₁ h₂ hp => ecbTaint_agree h₁ h₂ hp)
  · exact ecbDecrypt_constantTime _ _ (fun _ _ h₁ h₂ hp => ecbTaint_agree h₁ h₂ hp)

theorem ecb_verified (d : Spec.TripleDes.Direction) :
    Verified target (Impl.TripleDes.X86.Ecb.ecb d) (Proof.TripleDes.ecbScratchContract abi d 16) := by
  have hsat := (wide_implies d).sat_left
  have narrowSat : ∃ s, (contract d).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wide_pre d s hs⟩
  apply Verified.of_implies _ (wide_implies d)
  refine Verified.narrowTo
    (Verified.of_correct (ecb_correct d) (ecb_constantTime d) (.refl narrowSat))
    narrowRd narrowWr (wide_pre d) ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp_all only [or_true, true_or]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp_all only [or_true, true_or]
  · intro s s' _ h
    narrow at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    narrow
    exact h

theorem encrypt_verified : Verified target Impl.TripleDes.X86.Ecb.encrypt (Proof.TripleDes.ecbEncryptScratchContract abi 16) := ecb_verified .encrypt
theorem decrypt_verified : Verified target Impl.TripleDes.X86.Ecb.decrypt (Proof.TripleDes.ecbDecryptScratchContract abi 16) := ecb_verified .decrypt

end VG.Proof.TripleDes.X86.Ecb

end
