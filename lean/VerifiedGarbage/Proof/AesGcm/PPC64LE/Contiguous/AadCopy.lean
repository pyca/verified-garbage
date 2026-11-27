module

-- separate module: The short AAD copy uses independent aligned and byte-remainder loops.

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.Contiguous
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Loops
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.DirectGather.Bulk
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes

/-! # Direct word-sized copies into the short POWER AAD block -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.Contiguous
open VG VG.PPC64LE VG.WriteBytes VG.Impl.AesGcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE.Contiguous (takeWord)
open VG.Spec.Aes (bytesAt)

private theorem copyWord_mem (m : Mem) (src dst : Addr) (n : Nat) :
    m.writeW dst (m.readW src (8*n)) = writeBytes m dst (bytesAt m src n) := by
  simp only [Mem.writeW,Mem.readW]
  rw [show 8*n/8=n by omega,BitVec.setWidth_eq,BitVec.setWidth_eq,write_eq_writeBytes]
  congr 1
  simp only [bytesAt]
  exact List.map_congr_left fun j hj => Mem.extractLsb'_read _ _ (List.mem_range.mp hj)

abbrev copyRegs : List Reg := [.r0,.r3,.r4,.r5,.r6,.r7,.r11]

structure Copied (s : State) (src dst : Addr) (len count : Nat) (t : State) : Prop where
  r3 : t.gpr .r3 = src + BitVec.ofNat 64 count
  r4 : t.gpr .r4 = dst + BitVec.ofNat 64 count
  r5 : t.gpr .r5 = BitVec.ofNat 64 (len-count)
  mem : t.mem = writeBytes s.mem dst (bytesAt s.mem src count)
  regs : Keep copyRegs s t

private theorem word {size : VG.PPC64LE.Size} {s : State} {src dst : Addr} {len : Nat}
    (width : size=.w ∨ size=.d) (hs : s.gpr .r3=src) (hd : s.gpr .r4=dst)
    (hn : s.gpr .r5=BitVec.ofNat 64 len) (enough : size.bytes ≤ len) (hlt : len<2^64)
    (read : InRegions (s.rd++s.wr) src size.bytes) (write : InRegions s.wr dst size.bytes) :
    WP isa (.block [.load size .r7 .r3 0,.store size .r7 .r4 0,.addi .r3 .r3 size.bytes,
      .addi .r4 .r4 size.bytes,.subi .r5 .r5 size.bytes]) s (Copied s src dst len size.bytes) := by
  suffices run : WP isa (.block [.load size .r7 .r3 0,.store size .r7 .r4 0,.addi .r3 .r3 size.bytes,
      .addi .r4 .r4 size.bytes,.subi .r5 .r5 size.bytes]) s fun t =>
      t.gpr .r3=src+BitVec.ofNat 64 size.bytes ∧ t.gpr .r4=dst+BitVec.ofNat 64 size.bytes ∧
      t.gpr .r5=BitVec.ofNat 64 (len-size.bytes) ∧ t.mem=writeBytes s.mem dst (bytesAt s.mem src size.bytes) by
    rcases width with rfl | rfl <;>
      exact WP.mono (WP.keep copyRegs run (by decide)) fun _ ⟨⟨r3,r4,r5,mem⟩,k⟩ => ⟨r3,r4,r5,mem,k⟩
  rcases width with rfl | rfl
  all_goals
    apply WP.of_runBlock
    simp only [Size.bytes] at read write enough
    simp only [runBlock_cons,runStep_some,runBlock_nil,exec,addr,State.load,State.store,
      State.write,Size.bytes,hs,hd,hn,BitVec.add_zero,
      read,write,Option.bind_some,Option.map_some,Option.some.injEq,exists_eq_left',reduceCtorEq,ne_eq,
      not_false_eq_true,Nat.reduceLT,show (4: Nat) ≤ 32768 by decide,show (8: Nat) ≤ 32768 by decide,true_and,reduceIte,Nat.reducePow,Nat.reduceMod,↓reduceIte,and_self,implies_true]
  · exact ⟨ofNat_sub64 enough hlt,by simpa [Mem.writeW,Mem.readW,BitVec.setWidth_setWidth_of_le] using copyWord_mem s.mem src dst 4⟩
  · exact ⟨ofNat_sub64 enough hlt,by simpa [Mem.writeW,Mem.readW] using copyWord_mem s.mem src dst 8⟩
private theorem take_wp {size : VG.PPC64LE.Size} {shift len : Nat} {s : State} {src dst : Addr}
    (width : size=.w ∨ size=.d) (amount : 2^shift = size.bytes) (sh : shift < 64)
    (hs : s.gpr .r3 = src) (hd : s.gpr .r4 = dst) (hn : s.gpr .r5 = BitVec.ofNat 64 len)
    (hlt : len < 2^64)
    (read : size.bytes ≤ len → InRegions (s.rd++s.wr) src size.bytes)
    (write : size.bytes ≤ len → InRegions s.wr dst size.bytes) :
    WP isa (takeWord size shift) s (Copied s src dst len (if len < size.bytes then 0 else size.bytes)) := by
  let t := s.write .r11 (BitVec.ofNat 64 (len / size.bytes))
  have step : WP isa (.block [.lsr .d .r11 .r5 shift]) s (· = t) := by
    crun [hn,sh,t,DirectGather.shrNat shift hlt,amount]
  refine WP.seq (WP.mono step fun u hu => ?_)
  subst u
  refine WP.ite (decide (len / size.bytes = 0)) (eval_zero (s := t) (r := .r11) (by rfl)
    (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlt)) (fun small => ?_) (fun big => ?_)
  · have hdiv : len / size.bytes = 0 := by simpa using small
    have pos : 0 < size.bytes := by rcases width with rfl|rfl <;> decide
    have lt := (Nat.div_eq_zero_iff_lt pos).mp hdiv
    simp only [lt,↓reduceIte]
    apply WP.block_nil
    exact ⟨by simpa [t, State.write] using hs, by simpa [t, State.write] using hd,
      by simpa [t, State.write] using hn, by simp [t, State.write,bytesAt,writeBytes_nil],
      ⟨fun r hr => by have ne : r ≠ .r11 := fun eq => hr (by simp [eq,copyRegs]); simp [t,State.write,ne],rfl,rfl⟩⟩
  · have hdiv : len / size.bytes ≠ 0 := by simpa using big
    have le : size.bytes ≤ len := Nat.le_of_not_gt fun lt => hdiv (Nat.div_eq_of_lt lt)
    simp only [Nat.not_lt.mpr le,↓reduceIte]
    refine WP.mono (word (s := t) width hs hd hn le hlt (read le) (write le)) fun u out => ?_
    exact { out with regs := ⟨fun r hr => by
      rw [out.regs.gpr hr]
      have ne : r ≠ .r11 := fun eq => hr (by simp [eq,copyRegs])
      simp [t,State.write,ne],out.regs.2⟩ }

private theorem Copied.append {s t v : State} {src dst : Addr} {len i j : Nat}
    (a : Copied s src dst len i t)
    (b : Copied t (src+BitVec.ofNat 64 i) (dst+BitVec.ofNat 64 i) (len-i) j v)
    (apart : (⟨src,len⟩ : Region).Disjoint ⟨dst,len⟩) (fit : i+j ≤ len) (hlt : len<2^64) :
    Copied s src dst len (i+j) v := by
  have frame : Frame [⟨dst,i⟩] s.mem t.mem := by
    rw [a.mem]
    exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Region.contains_self _ _)
  have keep := bytesAt_frame frame (p := src+BitVec.ofNat 64 i) (n := j) (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl
    exact (apart.sub_left (Offset.sub_base src fit)).sub_right (Region.sub_prefix (by omega))) (by omega)
  refine ⟨by rw [b.r3,add_ofNat_assoc],by rw [b.r4,add_ofNat_assoc],by rw [b.r5,Nat.sub_sub],
    ?_, ⟨fun r hr => (b.regs.gpr hr).trans (a.regs.gpr hr),b.regs.2.1.trans a.regs.2.1,
      b.regs.2.2.trans a.regs.2.2⟩⟩
  have app := writeBytes_append s.mem dst (bytesAt s.mem src i) (bytesAt s.mem (src+BitVec.ofNat 64 i) j)
    (by rw [length_bytesAt,length_bytesAt]; omega)
  rw [length_bytesAt] at app
  rw [b.mem,keep,a.mem,app,← bytesAt_add]

private theorem remainder_wp {s : State} {src dst : Addr} {n : Nat}
    (hs : s.gpr .r3 = src) (hd : s.gpr .r4 = dst) (hn : s.gpr .r5 = BitVec.ofNat 64 n)
    (hlt : n<2^64) (read : Covers [⟨src,n⟩] (s.rd++s.wr)) (write : Covers [⟨dst,n⟩] s.wr)
    (apart : (⟨src,n⟩ : Region).Disjoint ⟨dst,n⟩) :
    WP isa (.ite (.zero .d .r5) (.block []) copyLoop) s (Copied s src dst n n) := by
  refine WP.ite (decide (n=0)) (eval_zero hn hlt) (fun h => ?_) (fun h => ?_)
  · have eq : n = 0 := by simpa using h
    subst n
    exact WP.block_nil ⟨by simpa using hs,by simpa using hd,hn,
      by simp [bytesAt,writeBytes_nil],Keep.refl _ _⟩
  · have ne : n ≠ 0 := by simpa using h
    have loop := copyLoop_ok s ⟨hs,hd,hn,by omega,hlt,read,write,apart⟩
    exact WP.mono (WP.keep copyRegs loop (by decide)) fun _ ⟨⟨mem,l⟩,k⟩ =>
      ⟨l.r3,l.r4,by simpa using l.r5,mem,k⟩

private theorem take_next {s t : State} {src dst : Addr} {len i shift : Nat} {size : VG.PPC64LE.Size}
    (a : Copied s src dst len i t) (width : size=.w ∨ size=.d) (amount : 2^shift=size.bytes) (sh : shift<64)
    (hi : i ≤ len) (hlt : len<2^64) (read : Covers [⟨src,len⟩] (s.rd++s.wr))
    (write : Covers [⟨dst,len⟩] s.wr) (apart : (⟨src,len⟩ : Region).Disjoint ⟨dst,len⟩) :
    WP isa (takeWord size shift) t fun u => ∃ j, j ≤ len ∧ Copied s src dst len j u := by
  refine WP.mono (take_wp width amount sh a.r3 a.r4 a.r5 (by omega) (fun h => ?_) (fun h => ?_)) fun u b => ?_
  · rw [a.regs.2.1,a.regs.2.2]
    exact in_off read (by omega) hlt
  · rw [a.regs.2.2]
    exact in_off write (by omega) hlt
  · have fit : i + (if len-i < size.bytes then 0 else size.bytes) ≤ len := by split <;> omega
    exact ⟨_,fit,a.append b apart fit hlt⟩

/-- Short AAD path: the two optional word loads and the residual byte loop copy
exactly the requested bytes, including zero-length and unaligned input. -/
theorem copy_short_wp {s : State} {src dst : Addr} {n : Nat}
    (hs : s.gpr .r3 = src) (hd : s.gpr .r4 = dst) (hn : s.gpr .r5 = BitVec.ofNat 64 n)
    (hlt : n<2^64) (read : Covers [⟨src,n⟩] (s.rd++s.wr)) (write : Covers [⟨dst,n⟩] s.wr)
    (apart : (⟨src,n⟩ : Region).Disjoint ⟨dst,n⟩) :
    WP isa (.seq (takeWord .d 3) (.seq (takeWord .w 2) (.ite (.zero .d .r5) (.block []) copyLoop)))
      s (Copied s src dst n n) := by
  have start : Copied s src dst n 0 s := ⟨by simpa using hs,by simpa using hd,by simpa using hn,
    by simp [bytesAt,writeBytes_nil],Keep.refl _ _⟩
  refine WP.seq (WP.mono (take_next (size := .d) (shift := 3) start (.inr rfl) rfl (by decide)
    (Nat.zero_le _) hlt read write apart) fun t ⟨i,hi,ai⟩ => ?_)
  refine WP.seq (WP.mono (take_next (size := .w) (shift := 2) ai (.inl rfl) rfl (by decide)
    hi hlt read write apart) fun u ⟨j,hj,aj⟩ => ?_)
  have fit : j + (n-j) = n := by omega
  have bound : j + (n-j) ≤ n := by omega
  refine WP.mono (remainder_wp aj.r3 aj.r4 aj.r5 (by omega) ?_ ?_ ?_) fun v r => ?_
  · rw [aj.regs.2.1,aj.regs.2.2]
    exact covers_off read bound hlt
  · rw [aj.regs.2.2]
    exact covers_off write bound hlt
  · exact (apart.sub_left (Offset.sub_base src bound)).sub_right (Offset.sub_base dst bound)
  · simpa only [fit] using aj.append r apart bound hlt

end VG.Proof.AesGcm.PPC64LE.Contiguous
