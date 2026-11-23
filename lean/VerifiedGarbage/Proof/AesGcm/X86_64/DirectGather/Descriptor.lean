module
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.LoopState
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-! Read one descriptor after the optional authenticated prefix. -/
@[expose] public section
set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Impl.AesGcm.X86_64.DirectGather
open VG.Spec.Aes (bytesAt)

def slot (m : Mem) (W : Addr) (d : Nat) (v : Addr) := m.writeW (W+BitVec.ofNat 64 d) v
theorem slot_other (m : Mem) (W v : Addr) (a b : Nat) (ab : a+8≤b ∨ b+8≤a)
    (ha : a+8≤2560) (hb : b+8≤2560) :
    (slot m W b v).readW (W+BitVec.ofNat 64 a) 64=m.readW (W+BitVec.ofNat 64 a) 64 :=
  Mem.readW_writeW_sep (Offset.sep W ab (by omega) (by omega)) (by decide)

def loadedMem (m : Mem) (W ptr : Addr) (n : Nat) : Mem :=
  slot (slot (slot m W 256 (ptr+16#64)) W 264 0) W 240 (BitVec.ofNat 64 n)

structure DescriptorInput (W P Q D : Addr) (n skip pos : Nat) (s : State) : Prop where
  work : s.gpr .r15=W
  wp : Covers [⟨W,2560⟩] s.wr
  ptr : s.mem.readW (W+256#64) 64=P
  source : s.mem.readW P 64=Q
  size : s.mem.readW (P+8#64) 64=BitVec.ofNat 64 n
  pre : s.mem.readW (W+264#64) 64=BitVec.ofNat 64 skip
  position : s.mem.readW (W+240#64) 64=BitVec.ofNat 64 pos
  dst : s.mem.readW (W+200#64) 64=D
  rp : InRegions (s.rd++s.wr) P 8
  rn : InRegions (s.rd++s.wr) (P+8#64) 8

structure Loaded (W P Q D : Addr) (n skip pos : Nat) (s t : State) : Prop where
  src : t.gpr .rbx=Q+BitVec.ofNat 64 skip
  left : t.gpr .rbp=BitVec.ofNat 64 (n-skip)
  dst : t.gpr .r12=D+BitVec.ofNat 64 pos
  off : t.gpr .rsi=BitVec.ofNat 64 (pos%16)
  zero : t.zf=some (decide (n-skip=0))
  kept : ∀ r∈[Reg.r13,.r14,.r15,.rsp],t.gpr r=s.gpr r
  mem : t.mem=loadedMem s.mem W P (pos+(n-skip))
  rd : t.rd=s.rd
  wr : t.wr=s.wr

theorem loadPiece_ok {s : State} {W P Q D : Addr} {n sk pos : Nat} (p : DescriptorInput W P Q D n sk pos s)
    (hn : n<2^64) (hk : sk≤n) (hp : pos<2^64) :
    WP isa (.block loadPiece) s (Loaded W P Q D n sk pos s) := by
  have w (d : Nat) (h : d+8≤2560) : InRegions s.wr (W+BitVec.ofNat 64 d) 8 := in_off p.wp h (by decide)
  have r (d : Nat) (h : d+8≤2560) : InRegions (s.rd++s.wr) (W+BitVec.ofNat 64 d) 8 := in_left (w d h)
  have w1 := w 256 (by decide); have w2 := w 264 (by decide); have w3 := w 240 (by decide)
  have r1 := r 256 (by decide); have r2 := r 264 (by decide); have r3 := r 240 (by decide); have r4 := r 200 (by decide)
  have sep (m : Mem) (v : Addr) (a b : Nat) (h : a+8≤b ∨ b+8≤a) (ha : a+8≤2560) (hb : b+8≤2560) :=
    slot_other m W v a b h ha hb
  have k1 := sep s.mem (P+16#64) 264 256 (by decide) (by decide) (by decide)
  have p1 := sep s.mem (P+16#64) 240 256 (by decide) (by decide) (by decide)
  have p2 := sep (slot s.mem W 256 (P+16#64)) 0 240 264 (by decide) (by decide) (by decide)
  have d1 := sep s.mem (P+16#64) 200 256 (by decide) (by decide) (by decide)
  have d2 := sep (slot s.mem W 256 (P+16#64)) 0 200 264 (by decide) (by decide) (by decide)
  unfold slot at k1 p1 p2 d1 d2
  have m := and15 (BitVec.ofNat 64 pos)
  change BitVec.ofNat 64 pos &&& 15#64 = BitVec.ofNat 64 ((BitVec.ofNat 64 pos).toNat%16) at m
  rw [toNat_ofNat_of_lt hp] at m
  have sub := ofNat_sub hk hn
  have zero := and_self_beq (a:=n-sk) (by omega)
  have vrd : (((s.mem.writeW (W+256#64) (P+16#64)).writeW (W+264#64) (0#64)).readW (W+240#64) 64)=BitVec.ofNat 64 pos := p2.trans (p1.trans p.position)
  have drd : (((s.mem.writeW (W+256#64) (P+16#64)).writeW (W+264#64) (0#64)).readW (W+200#64) 64)=D := d2.trans (d1.trans p.dst)
  obtain ⟨reg,_,ptr,src,len,skip,pos,dst,rp,rn⟩ := p
  apply WP.of_runBlock
  refine ⟨_,by unfold loadPiece load store; xrun [reg,ptr,src,len,skip,pos,dst,rp,rn,BitVec.add_zero,
    r1,r2,r3,r4,w1,w2,w3,k1,vrd,drd,sub,m,ofNat_add_ofNat], ?_⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,rfl,rfl⟩
  · simp [gpr_setReg,gpr_arithFlags,vrd,drd,m]
  · simp [gpr_setReg,gpr_arithFlags,vrd,drd,m]
  · simp [gpr_setReg,gpr_arithFlags,vrd,drd,m]
  · simp [gpr_setReg,gpr_arithFlags,vrd,drd,m]
  · simp only [zf_arithFlags,zero]
  · intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> simp [gpr_setReg,gpr_arithFlags]
  · change (((s.mem.writeW _ _).writeW _ _).writeW _ _) = _
    simp only [loadedMem,slot,show BitVec.setWidth 64 (0#32)=0#64 from rfl,vrd,ofNat_add_ofNat] <;> rfl

/-- Only the three descriptor-progress slots are changed. -/
theorem loadedMem_frame (m : Mem) (W P : Addr) (n : Nat) :
    Frame [⟨W+224#64,48⟩] m (loadedMem m W P n) := by
  have sub (d : Nat) (lo : 224≤d) (hi : d+8≤272) : (⟨W+224#64,48⟩ : Region).Contains (W+BitVec.ofNat 64 d) 8 := by
    have e : W+BitVec.ofNat 64 d=(W+224#64)+BitVec.ofNat 64 (d-224) := by
      rw [add_ofNat_assoc,Nat.add_sub_of_le lo]
    rw [e]; exact Offset.contains_base _ (by omega) (by omega)
  exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) (P+16#64) (sub 256 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) (0#64) (sub 264 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) (BitVec.ofNat 64 n) (sub 240 (by decide) (by decide))

theorem loadedMem_slots (m : Mem) (W P : Addr) (n : Nat) :
    (loadedMem m W P n).readW (W+256#64) 64=P+16#64 ∧ (loadedMem m W P n).readW (W+264#64) 64=0 ∧
    (loadedMem m W P n).readW (W+240#64) 64=BitVec.ofNat 64 n ∧
    (loadedMem m W P n).readW (W+224#64) 64=m.readW (W+224#64) 64 := by
  have same (m : Mem) (d : Nat) (v : Addr) : (slot m W d v).readW (W+BitVec.ofNat 64 d) 64=v :=
    Mem.readW_writeW_self64 ..
  unfold loadedMem
  refine ⟨?_,?_,same ..,?_⟩
  · rw [slot_other _ _ _ 256 240 (by decide) (by decide) (by decide),
        slot_other _ _ _ 256 264 (by decide) (by decide) (by decide),same]
  · rw [slot_other _ _ _ 264 240 (by decide) (by decide) (by decide),same]
  · rw [slot_other _ _ _ 224 240 (by decide) (by decide) (by decide),
        slot_other _ _ _ 224 264 (by decide) (by decide) (by decide),
        slot_other _ _ _ 224 256 (by decide) (by decide) (by decide)]

abbrev advance := [load .r10 tlO,.alu .sub .r10 (imm 1),store .r10 tlO]

structure Advanced (W : Addr) (n : Nat) (s t : State) : Prop where
  kept : ∀ r∈[Reg.r13,.r14,.r15,.rsp],t.gpr r=s.gpr r
  mem : t.mem=slot s.mem W 224 (BitVec.ofNat 64 (n-1))
  zero : t.zf=some (decide (n-1=0))
  rd : t.rd=s.rd
  wr : t.wr=s.wr

theorem advance_ok {s : State} {W : Addr} {n : Nat} (work : s.gpr .r15=W)
    (wr : InRegions s.wr (W+224#64) 8) (num : s.mem.readW (W+224#64) 64=BitVec.ofNat 64 n)
    (hn : 0<n) (hlt : n<2^64) : WP isa (.block advance) s (Advanced W n s) := by
  have read := in_left (rd:=s.rd) wr
  have sub := ofNat_sub (a:=n) (b:=1) hn hlt
  have zero : (BitVec.ofNat 64 (n-1)==0)=decide (n-1=0) := by
    rw [← and_self_beq (a:=n-1) (by omega),BitVec.and_self]
  apply WP.of_runBlock
  refine ⟨_,by unfold advance load store; xrun [work,wr,read,num,sub],?_⟩
  refine ⟨?_,rfl,?_,rfl,rfl⟩
  · intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> simp [gpr_arithFlags,gpr_setReg]
  · change some (BitVec.ofNat 64 (n-1)==0)=_
    rw [zero]

end VG.Proof.AesGcm.X86_64.DirectGather
