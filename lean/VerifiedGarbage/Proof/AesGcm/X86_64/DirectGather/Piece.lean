module

public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Fragment
public import VerifiedGarbage.Impl.AesGcm.X86_64.DirectGather
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Whole
import VerifiedGarbage.Proof.AesGcm.X86_64.CryptOk
import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
import VerifiedGarbage.Proof.Framework.Offset

@[expose] public section

/-! Consume saved keystream at the beginning of an unaligned fragment. -/
set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64.DirectGather
open VG.Spec.Gcm (Block)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (Ctr xorKs)
variable {Ctx St W SP Q D : Addr} {R n : Nat} {s : State}

private abbrev setupSuffix : List Instr :=
  [.mov32 .rcx (imm 16),.alu .sub .rcx (.reg .rsi),.alu .cmp .rbp (.reg .rcx),.cmov .b .rcx (.reg .rbp),
   .alu .add .rsi (.reg .r14),.alu .add .rsi (imm 64),.mov .rdi (.reg .r12)]

private structure XorArgs (Ctx St W SP Q D : Addr) (R n o : Nat) (s t : State) : Prop where
  inp : PieceInput Ctx St W SP R Q D n t
  loop : LoopPre t (St+BitVec.ofNat 64 (64+o)) D (min (16-o) n)
  mem : t.mem=s.mem
  rd : t.rd=s.rd
  wr : t.wr=s.wr

private theorem xorArgs (p : PieceInput Ctx St W SP R Q D n s) {o : Nat}
    (hr : s.gpr .rsi=BitVec.ofNat 64 o) (ho : o<16) (hn : 0<n) :
    WP isa (.block setupSuffix) s (XorArgs Ctx St W SP Q D R n o s) := by
  have diff := ofNat_sub (a:=16) (b:=o) (by omega) (by decide)
  have hp := p.rbp
  have op := p.r12
  have st := p.env.r14
  have cn := toNat_ofNat_of_lt p.src.lt
  have co := toNat_ofNat_of_lt (n:=16-o) (by omega)
  have addr : BitVec.ofNat 64 o + St + 64#64 = St+BitVec.ofNat 64 (64+o) := by
    rw [BitVec.ofNat_add]; ac_rfl
  have fin (u : State) (endState : runBlock isa setupSuffix s = some u)
      (regs : ∀ r ∈ [Reg.r13,.r14,.r15,.rsp,.rbx,.rbp,.r12], u.gpr r = s.gpr r)
      (length : u.gpr .rcx = BitVec.ofNat 64 (min (16-o) n))
      (src : u.gpr .rsi=St+BitVec.ofNat 64 (64+o)) (out : u.gpr .rdi=D)
      (mem : u.mem=s.mem) (rd : u.rd=s.rd) (wr : u.wr=s.wr) :
      WP isa (.block setupSuffix) s (XorArgs Ctx St W SP Q D R n o s) := by
    have e := p.env.keep (fun r hr => regs r (by simpa using List.mem_append_left [.rbx,.rbp,.r12] hr)) rd wr
    have inp : PieceInput Ctx St W SP R Q D n u := ⟨e,by rw [mem]; exact p.rounds,p.src.of_eq rd wr,p.dst.of_eq rd wr,
      p.apart,(regs .rbx (by decide)).trans p.rbx,(regs .r12 (by decide)).trans p.r12,(regs .rbp (by decide)).trans p.rbp⟩
    have d := inp.dst.take (Nat.min_le_right (16-o) n)
    exact WP.of_runBlock ⟨u,endState,inp,⟨src,out,length,by omega,by omega,
      covers_left (e.perm.stC (by omega)),d.wr,(d.ok.st.sub_right (Lay.stSub (by omega))).symm⟩,mem,rd,wr⟩
  have red : (18446744073709551616 - o % 18446744073709551616 + 16) % 18446744073709551616 = 16-o := by omega
  have red' : (16-o)%18446744073709551616 = 16-o := by omega
  by_cases small : n < 16-o
  all_goals
    apply fin _ (by unfold setupSuffix; xrun [hr,hp,diff,cn,co,red,red',small,st,op])
    · intro r h; simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [red,red',small,gpr_setReg,gpr_arithFlags]
    · first | simp [gpr_setReg,gpr_arithFlags,hr,hp,diff,red,red',small,Nat.min_eq_right (by omega : n≤16-o)] |
        simp [gpr_setReg,gpr_arithFlags,hr,hp,diff,red,red',small,Nat.min_eq_left (by omega : 16-o≤n)]
    · simp [gpr_setReg,gpr_arithFlags,hr,st,addr,red,red',small]
    · simp [gpr_setReg,gpr_arithFlags,op,red,red',small]
    all_goals simp [red,red',small,diff,mem_setReg,mem_arithFlags,rd_setReg,rd_arithFlags,wr_setReg,wr_arithFlags]

/-- Number of text bytes from this fragment using the previous counter block. -/
def suffixLen (P n : Nat) : Nat := if P%16=0 then 0 else min (16-P%16) n

theorem suffix_ok {P : Nat} {icb : Block} (p : PieceInput Ctx St W SP R Q D n s)
    (ptr : s.gpr .rsi=BitVec.ofNat 64 (P%16)) (hn : 0<n)
    (ctr : Ctr s.mem (St+48#64) (St+64#64) (ciphOf s.mem Ctx R) icb P) :
    WP isa suffix s (SpanOutput Ctx St W SP Q D R n (suffixLen P n) P icb s) := by
  have ho : P%16<16 := Nat.mod_lt _ (by decide)
  obtain ⟨t,test,zf,gpr,mem,rd,wr⟩ := test_ok s .rsi ptr (by omega)
  have pt : PieceInput Ctx St W SP R Q D n t := ⟨p.env.keep (fun r _ => by rw [gpr]) rd wr,
    by rw [mem]; exact p.rounds,p.src.of_eq rd wr,p.dst.of_eq rd wr,p.apart,
    by rw [gpr,p.rbx],by rw [gpr,p.r12],by rw [gpr,p.rbp]⟩
  refine WP.seq (WP.of_runBlock ⟨t,test,?_⟩)
  refine WP.ite (decide (P%16=0)) (eval_e zf) (fun eq => ?_) (fun ne => ?_)
  · have eq' : P%16=0 := by simpa using eq
    have z : suffixLen P n=0 := by simp [suffixLen,eq']
    refine WP.block_nil ⟨⟨pt.env,pt.rounds,by simpa [z,mem] using ctr,by simp [z,bytesAt,xorKs],
      by rw [mem]; exact Frame.refl _ _⟩,by simpa [z] using pt.rbx,by simpa [z] using pt.r12,
      by simpa [z] using pt.rbp⟩
  · have ne' : P%16≠0 := by simpa using ne
    let k := min (16-P%16) n
    have len : suffixLen P n=k := by simp [suffixLen,ne',k]
    have kn : k≤n := Nat.min_le_right _ _
    have pos : 0<k := by dsimp [k]; omega
    have cap : P%16+k≤16 := by dsimp [k]; omega
    refine WP.seq ((xorArgs pt (by rw [gpr,ptr]) ho hn).mono fun u a => ?_)
    have q := a.inp.src.take kn
    have d := a.inp.dst.take kn
    refine WP.seq ((xorLoopG_ok true u a.loop a.inp.rbx q.rd
      (.inr ((p.apart.sub_left (Region.sub_prefix kn)).sub_right (Region.sub_prefix kn)))).mono fun z ⟨m,g,dr,dw⟩ => ?_)
    rw [a.mem,mem] at m
    have hg (r : Reg) (hr : r∈[Reg.rbx,.r12,.rbp,.rcx,.r13,.r14,.r15,.rsp]) : z.gpr r=u.gpr r := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact g _ (by decide) (by decide) (by decide)
    have bx := (hg .rbx (by decide)).trans a.inp.rbx
    have bp := (hg .rbp (by decide)).trans a.inp.rbp
    have dptr := (hg .r12 (by decide)).trans a.inp.r12
    have cx := (hg .rcx (by decide)).trans a.loop.rcx
    change z.gpr .rcx=BitVec.ofNat 64 k at cx
    have ez := a.inp.env.keep (fun r hr => hg r (List.mem_append_right [Reg.rbx,.r12,.rbp,.rcx] hr)) dr dw
    have xl := length_xorBytes s.mem Q (St+BitVec.ofNat 64 (64+P%16)) k
    have fr : Frame [⟨D,k⟩] s.mem z.mem := by rw [m]; exact writeBytes_frame' _ xl
    have st (off : Nat) (h : off+16≤80) :
        ∀ r∈[(⟨D,k⟩ : Region)], (⟨St+BitVec.ofNat 64 off,16⟩ : Region).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact (d.ok.st.sub_right (Lay.stSub h)).symm
    have rr := rounds_frame fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (d.ok.w.sub_right (Lay.wSub (by decide))).symm) p.rounds
    have cc := (ctr.head ne' cap).congr (blockAt_frame fr (st 48 (by decide))) (blockAt_frame fr (st 64 (by decide)))
    have out : bytesAt z.mem D k=xorKs (ciphOf s.mem Ctx R) icb P (bytesAt s.mem Q k) := by
      have e := bytesAt_writeBytes_self s.mem D _ (by rw [xl]; omega)
      rw [xl] at e
      rw [m,e,xorBytes]
      have h := Gcm.ctr_head ctr ne' (d:=bytesAt s.mem Q k) (by rw [length_bytesAt]; exact cap)
      rw [length_bytesAt,add_ofNat_assoc] at h
      exact h
    have sub := ofNat_sub kn p.src.lt
    apply WP.of_runBlock
    refine ⟨_,by xrun [cx,bx,bp,dptr,sub],?_⟩
    refine ⟨⟨ez.keep (fun r hr => ?_) rfl rfl, rr, by simpa only [len,mem_setReg,mem_arithFlags] using cc,
      by simpa only [len,mem_setReg,mem_arithFlags] using out, ?_⟩, ?_, ?_, ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl <;> simp [gpr_setReg,gpr_arithFlags]
    · rw [len]; exact fr.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_,List.mem_cons_self ..,fun _ h => h⟩
    all_goals simp [gpr_setReg,gpr_arithFlags,len]

end VG.Proof.AesGcm.X86_64.DirectGather

/-! Compose the three counter-mode spans of one direct gather fragment. -/
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Impl.AesGcm.X86_64.DirectGather
open VG.Spec.Gcm (Block)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (Ctr xorKs)
variable {Ctx St W SP Q D : Addr} {R n P k : Nat} {icb : Block} {s t u : State}

theorem PieceOutput.drop (p : PieceInput Ctx St W SP R Q D n s)
    (a : PieceOutput Ctx St W SP R icb P Q D k s t) (kn : k≤n) (rd : t.rd=s.rd) (wr : t.wr=s.wr)
    (src : t.gpr .rbx=Q+BitVec.ofNat 64 k) (dst : t.gpr .r12=D+BitVec.ofNat 64 k)
    (left : t.gpr .rbp=BitVec.ofNat 64 (n-k)) :
    PieceInput Ctx St W SP R (Q+BitVec.ofNat 64 k) (D+BitVec.ofNat 64 k) (n-k) t := by
  refine ⟨a.env,a.rounds,(p.src.drop kn).of_eq rd wr,(p.dst.drop kn).of_eq rd wr,
    (p.apart.sub_left (Offset.sub_base Q (by omega))).sub_right (Offset.sub_base D (by omega)),
    src,dst,left⟩

private theorem Frame.textSub {D' : Addr} {l : Nat} {m m' : Mem}
    (f : Frame (crFrame St W SP D' l) m m') (h : Region.Sub ⟨D',l⟩ ⟨D,n⟩) :
    Frame (crFrame St W SP D n) m m' := by
  exact f.sub fun r hr => by
    rcases List.mem_cons.mp hr with rfl|hr
    · exact ⟨_,List.mem_cons_self ..,h⟩
    · exact ⟨_,List.mem_cons_of_mem _ hr,fun _ a => a⟩

private theorem PieceOutput.bind (L : Lay Ctx St W SP) (p : PieceInput Ctx St W SP R Q D n s)
    (a : PieceOutput Ctx St W SP R icb P Q D k s t) (kn : k≤n)
    (b : PieceOutput Ctx St W SP R icb (P+k) (Q+BitVec.ofNat 64 k) (D+BitVec.ofNat 64 k) (n-k) t u) :
    PieceOutput Ctx St W SP R icb P Q D n s u := by
  have left := p.dst.take kn
  have src := p.src.drop kn
  have cip := ciph_frame a.frame (ctx_crFrame L left) p.rounds.2
  have source : bytesAt t.mem (Q+BitVec.ofNat 64 k) (n-k)=bytesAt s.mem (Q+BitVec.ofNat 64 k) (n-k) := by
    apply bytesAt_frame a.frame _ (Nat.le_of_lt src.lt)
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact (p.apart.sub_left (Offset.sub_base Q (by omega))).sub_right (Region.sub_prefix kn)
    · exact src.st.sub_right (Lay.stSub (by decide))
    · exact src.w.sub_right (Lay.wSub (by decide))
    · exact src.stk.symm
  have dest : bytesAt u.mem D k=bytesAt t.mem D k := by
    apply bytesAt_frame b.frame _ (Nat.le_of_lt left.ok.lt)
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact split_disj kn p.dst.ok.lt
    · exact left.ok.st.sub_right (Lay.stSub (by decide))
    · exact left.ok.w.sub_right (Lay.wSub (by decide))
    · exact left.ok.stk.symm
  obtain bc := b.ctr
  obtain bo := b.out
  rw [cip] at bc bo
  rw [source] at bo
  refine ⟨b.env,b.rounds,by simpa [Nat.add_assoc,Nat.add_sub_of_le kn] using bc,?_,
    (Frame.textSub a.frame (Region.sub_prefix kn)).trans (Frame.textSub b.frame (Offset.sub_base D (by omega)))⟩
  have cut (m : Mem) (base : Addr) : bytesAt m base n = bytesAt m base k ++ bytesAt m (base+BitVec.ofNat 64 k) (n-k) := by
    rw [← bytesAt_add,Nat.add_sub_of_le kn]
  rw [cut u.mem D,cut s.mem Q,dest,a.out,bo,Gcm.xorKs_append,length_bytesAt]

theorem piece_ok (v : GcmImpl) (c : Proof.Aes.X86_64.Ctr32ToImpl) (L : Lay Ctx St W SP)
    (p : PieceInput Ctx St W SP R Q D n s) (off : s.gpr .rsi=BitVec.ofNat 64 (P%16)) (hn : 0<n)
    (ctr : Ctr s.mem (St+48#64) (St+64#64) (ciphOf s.mem Ctx R) icb P) :
    WP isa (.seq suffix (.seq (whole ⟨c.callee.name,c.callee.code⟩) (cryptTailG v.callees true))) s
      (PieceOutput Ctx St W SP R icb P Q D n s) := by
  let k := suffixLen P n
  let m := n-k
  have kn : k≤n := by dsimp [k,suffixLen]; split <;> omega
  have align : m=0 ∨ (P+k)%16=0 := by dsimp [m,k,suffixLen]; split <;> omega
  refine WP.seq ((WP.with_rdwr (suffix_ok p off hn ctr)).mono fun t ⟨a,rd,wr⟩ => ?_)
  have pt := a.head.drop p kn rd wr a.src a.dst a.left
  have cip := ciph_frame a.head.frame (ctx_crFrame L (p.dst.take kn)) p.rounds.2
  have ct := a.head.ctr
  rw [← cip] at ct
  refine WP.seq ((WP.with_rdwr (whole_ok c L pt align ct)).mono fun u ⟨b,rd',wr'⟩ => ?_)
  let j := 16*(m/16)
  have jm : j≤m := by dsimp [j]; omega
  have pu := b.head.drop pt jm rd' wr' b.src b.dst b.left
  have cip' := ciph_frame b.head.frame (ctx_crFrame L (pt.dst.take jm)) pt.rounds.2
  have ct' := b.head.ctr
  rw [← cip'] at ct'
  have short : m-j<16 := by dsimp [j]; omega
  have endAlign : m-j=0 ∨ ((P+k)+j)%16=0 := by dsimp [j]; omega
  refine (tail_ok v L pu short endAlign ct').mono fun z d => ?_
  exact a.head.bind L p kn (b.head.bind L pt jm d)

end VG.Proof.AesGcm.X86_64.DirectGather
