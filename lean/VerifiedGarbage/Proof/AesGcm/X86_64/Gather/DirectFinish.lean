module

public import VerifiedGarbage.Impl.AesGcm.X86_64.DirectGather
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Seal
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.TailPre

@[expose] public section
namespace VG.Proof.AesGcm.X86_64.Gather.DirectTail
open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Impl.AesGcm.X86_64.DirectGather
open VG.Proof.AesGcm.X86_64.Short
open VG.WriteBytes

theorem word_ok (wide : Bool) (s : State) {S K O G : Addr} {i : Nat}
    (src : s.gpr .rbx=S) (key : s.gpr .rdx=K) (out : s.gpr .rsi=O) (auth : s.gpr .rdi=G)
    (off : s.gpr .r10=BitVec.ofNat 64 i)
    (r₁ : InRegions (s.rd++s.wr) (S+BitVec.ofNat 64 i) (if wide then 8 else 4))
    (r₂ : InRegions (s.rd++s.wr) (K+BitVec.ofNat 64 i) (if wide then 8 else 4))
    (w₁ : InRegions s.wr (O+BitVec.ofNat 64 i) (if wide then 8 else 4))
    (w₂ : InRegions s.wr (G+BitVec.ofNat 64 i) (if wide then 8 else 4)) :
    ∃ t, runBlock isa (word wide) s=some t ∧
      t.mem=xw true s.mem (O+BitVec.ofNat 64 i) (G+BitVec.ofNat 64 i)
        (xb s.mem (S+BitVec.ofNat 64 i) (K+BitVec.ofNat 64 i) (if wide then 8 else 4)) ∧
      t.gpr .r10=BitVec.ofNat 64 (i+if wide then 8 else 4) ∧
      (∀ r, r≠.rax → r≠.r10 → t.gpr r=s.gpr r) ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ ZKeep [] s t := by
  have es := ea_idx s .rbx src off
  have ek := ea_idx s .rdx key off
  have ed := ea_idx s .rsi out off
  have eg := ea_idx s .rdi auth off
  cases wide <;> simp only [Bool.false_eq_true,ite_false,ite_true] at r₁ r₂ w₁ w₂ ⊢
  all_goals
    refine ⟨_,by xrun [Impl.AesGcm.X86_64.DirectGather.word,Impl.AesGcm.X86_64.Short.kB,es,ek,ed,eg,r₁,r₂,w₁,w₂],?_⟩
    refine ⟨?_,?_,?_,rfl,rfl,fun _ _ _ _ => rfl⟩
    · simp only [mem_setReg,mem_arithFlags,xw,ite_true,xb]
      first | rw [←writeW_xor32,←writeW_xor32]; congr 1 <;> simp | rw [←writeW_xor64,←writeW_xor64]
    · simp only [gpr_setReg,ite_true,off]; exact (BitVec.ofNat_add _ _).symm
    · intro r h₁ h₂; simp [gpr_setReg,h₁,h₂]

theorem byte_ok (s : State) {S K O G : Addr} {i n : Nat}
    (src : s.gpr .rbx=S) (key : s.gpr .rdx=K) (out : s.gpr .rsi=O) (auth : s.gpr .rdi=G)
    (off : s.gpr .r10=BitVec.ofNat 64 i) (len : s.gpr .rcx=BitVec.ofNat 64 n)
    (r₁ : InRegions (s.rd++s.wr) (S+BitVec.ofNat 64 i) 1)
    (r₂ : InRegions (s.rd++s.wr) (K+BitVec.ofNat 64 i) 1)
    (w₁ : InRegions s.wr (O+BitVec.ofNat 64 i) 1)
    (w₂ : InRegions s.wr (G+BitVec.ofNat 64 i) 1) :
    ∃ t, runBlock isa tailByte s=some t ∧
      t.mem=xw true s.mem (O+BitVec.ofNat 64 i) (G+BitVec.ofNat 64 i)
        [s.mem (S+BitVec.ofNat 64 i) ^^^ s.mem (K+BitVec.ofNat 64 i)] ∧
      t.gpr .r10=BitVec.ofNat 64 i+1 ∧
      t.zf=some (BitVec.ofNat 64 i+1-BitVec.ofNat 64 n==0) ∧
      (∀ r, r≠.rax → r≠.r9 → r≠.r10 → t.gpr r=s.gpr r) ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ ZKeep [] s t := by
  have es := ea_idx s .rbx src off
  have ek := ea_idx s .rdx key off
  have ed := ea_idx s .rsi out off
  have eg := ea_idx s .rdi auth off
  refine ⟨_,by xrun [tailByte,Impl.AesGcm.X86_64.Short.kB,es,ek,ed,eg,r₁,r₂,w₁,w₂],?_⟩
  refine ⟨?_,?_,?_,?_,rfl,rfl,fun _ _ _ _ => rfl⟩
  · simp only [mem_setReg,mem_arithFlags,setWidth8_xor,xw,ite_true,writeW8_eq]
  · simp [gpr_setReg,off]
  · simp [off,len]
  · intro r h₁ h₂ h₃; simp [gpr_setReg,h₁,h₂,h₃]


/-- The register bases are indexed by an absolute offset. The regions begin at
`start` so the second fragment only requires access to bytes it actually owns. -/
structure Span where
  src : Addr
  key : Addr
  dst : Addr
  auth : Addr
  start : Nat
  len : Nat

namespace Span

abbrev atStart (a : Span) (b : Addr) := b+BitVec.ofNat 64 a.start
abbrev range (a : Span) (b : Addr) : Region := ⟨a.atStart b,a.len⟩

theorem index (a : Span) (b : Addr) (i : Nat) :
    b+BitVec.ofNat 64 (a.start+i)=a.atStart b+BitVec.ofNat 64 i := by
  rw [BitVec.ofNat_add,←BitVec.add_assoc]

end Span

structure SpanPre (a : Span) (s : State) : Prop where
  src : s.gpr .rbx=a.src
  key : s.gpr .rdx=a.key
  out : s.gpr .rsi=a.dst
  auth : s.gpr .rdi=a.auth
  endReg : s.gpr .rcx=BitVec.ofNat 64 (a.start+a.len)
  bound : a.start+a.len≤16
  srcR : Covers [a.range a.src] (s.rd++s.wr)
  keyR : Covers [a.range a.key] (s.rd++s.wr)
  outW : Covers [a.range a.dst] s.wr
  authW : Covers [a.range a.auth] s.wr
  srcOut : (a.range a.src).Disjoint (a.range a.dst)
  srcAuth : (a.range a.src).Disjoint (a.range a.auth)
  keyOut : (a.range a.key).Disjoint (a.range a.dst)
  keyAuth : (a.range a.key).Disjoint (a.range a.auth)
  outAuth : (a.range a.dst).Disjoint (a.range a.auth)

structure SpanAt (a : Span) (s : State) (i : Nat) (t : State) : Prop where
  ptr : t.gpr .r10=BitVec.ofNat 64 (a.start+i)
  mem : t.mem=xw true s.mem (a.atStart a.dst) (a.atStart a.auth)
    (xb s.mem (a.atStart a.src) (a.atStart a.key) i)
  regs : ∀ r, r≠.rax → r≠.r8 → r≠.r9 → r≠.r10 → t.gpr r=s.gpr r
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  z : ZKeep [] s t

namespace SpanPre
variable {a : Span} {s t : State} {i : Nat} (p : SpanPre a s) (h : SpanAt a s i t)
include p

theorem access {b : Addr} {k : Nat} {rs : List Region} (cov : Covers [a.range b] rs) (le : i+k≤a.len) :
    InRegions rs (b+BitVec.ofNat 64 (a.start+i)) k := by
  rw [a.index]
  exact cov _ _ ⟨_,List.mem_singleton_self _,Offset.contains_base _ le (by omega_using [p.bound,le])⟩

include h

theorem append_mem {k : Nat} (le : i+k≤a.len) :
    xw true t.mem (a.dst+BitVec.ofNat 64 (a.start+i)) (a.auth+BitVec.ofNat 64 (a.start+i))
      (xb t.mem (a.src+BitVec.ofNat 64 (a.start+i)) (a.key+BitVec.ofNat 64 (a.start+i)) k) =
    xw true s.mem (a.atStart a.dst) (a.atStart a.auth)
      (xb s.mem (a.atStart a.src) (a.atStart a.key) (i+k)) := by
  let xs := xb s.mem (a.atStart a.src) (a.atStart a.key) i
  have xl : xs.length=i := length_xb _ _ _ _
  have read {b : Addr} (out : (a.range b).Disjoint (a.range a.dst))
      (auth : (a.range b).Disjoint (a.range a.auth)) :
      Spec.Aes.bytesAt t.mem (a.atStart b+BitVec.ofNat 64 i) k=
      Spec.Aes.bytesAt s.mem (a.atStart b+BitVec.ofNat 64 i) k := by
    rw [h.mem]
    exact xw_bytesAt xl le (by omega_using [p.bound])
      ((out.sub_left (Offset.sub_base _ le)).sub_right (Region.sub_prefix (by omega_using [le])))
      (fun _ => (auth.sub_left (Offset.sub_base _ le)).sub_right (Region.sub_prefix (by omega_using [le])))
  rw [a.index,a.index,a.index,a.index,xb_add]
  have xs' : xb t.mem (a.atStart a.src+BitVec.ofNat 64 i) (a.atStart a.key+BitVec.ofNat 64 i) k =
      xb s.mem (a.atStart a.src+BitVec.ofNat 64 i) (a.atStart a.key+BitVec.ofNat 64 i) k := by
    simp only [xb,read p.srcOut p.srcAuth,read p.keyOut p.keyAuth]
  rw [xs',h.mem]
  let ys := xb s.mem (a.atStart a.src+BitVec.ofNat 64 i) (a.atStart a.key+BitVec.ofNat 64 i) k
  have yl : ys.length=k := length_xb _ _ _ _
  have eq := xw_append true s.mem xs ys (by omega_using [p.bound] : a.len<2^63)
    (by rw [xl,yl]; exact le) (fun _ => p.outAuth)
  rw [xl] at eq
  exact eq

theorem bytes_ok (pos : i<a.len) : WP isa tailBytes t (SpanAt a s a.len) := by
  refine WP.loop (M:=isa) (body:=.block tailByte) (c:=.ne)
    (fun k u => ∃ j, k=a.len-j ∧ j<a.len ∧ SpanAt a s j u) ?_ (a.len-i) t ⟨i,rfl,pos,h⟩
  rintro k u ⟨j,rfl,hj,atj⟩
  have fit : j+1≤a.len := by omega_using [hj]
  obtain ⟨v,run,m,off,zf,g,rd,wr,z⟩ := byte_ok u
    ((atj.regs _ (by decide) (by decide) (by decide) (by decide)).trans p.src)
    ((atj.regs _ (by decide) (by decide) (by decide) (by decide)).trans p.key)
    ((atj.regs _ (by decide) (by decide) (by decide) (by decide)).trans p.out)
    ((atj.regs _ (by decide) (by decide) (by decide) (by decide)).trans p.auth) atj.ptr
    ((atj.regs _ (by decide) (by decide) (by decide) (by decide)).trans p.endReg)
    (by rw [atj.rd,atj.wr]; exact p.access p.srcR fit)
    (by rw [atj.rd,atj.wr]; exact p.access p.keyR fit)
    (by rw [atj.wr]; exact p.access p.outW fit) (by rw [atj.wr]; exact p.access p.authW fit)
  have hv : SpanAt a s (j+1) v := by
    refine ⟨?_,?_,fun r ra rb rc rt => (g r ra rc rt).trans (atj.regs r ra rb rc rt),
      rd.trans atj.rd,wr.trans atj.wr,atj.z.trans z⟩
    · rw [off,succ_ofNat,Nat.add_assoc]
    · rw [m,←p.append_mem atj fit]
      simp only [xb,bytesAt_one,List.zipWith_cons_cons,List.zipWith_nil_left]
  have flag : v.zf=some (decide (j+1=a.len)) := by
    rw [zf,succ_ofNat,Offset.ofNat_sub_ofNat_beq (by omega_using [p.bound,fit]) (by omega_using [p.bound])]
    simp [Nat.add_assoc]
  apply WP.of_runBlock
  refine ⟨v,run,?_⟩
  by_cases he : j+1=a.len
  · exact .inl ⟨by simp [eval,flag,he],he ▸ hv⟩
  · exact .inr ⟨by simp [eval,flag,he],a.len-(j+1),by omega,j+1,rfl,by omega,hv⟩


theorem word_step (wide : Bool) (le : i+(if wide then 8 else 4)≤a.len) :
    WP isa (.block (Impl.AesGcm.X86_64.DirectGather.word wide)) t (SpanAt a s (i+if wide then 8 else 4)) := by
  obtain ⟨v,run,m,off,g,rd,wr,z⟩ := word_ok wide t
    ((h.regs _ (by decide) (by decide) (by decide) (by decide)).trans p.src)
    ((h.regs _ (by decide) (by decide) (by decide) (by decide)).trans p.key)
    ((h.regs _ (by decide) (by decide) (by decide) (by decide)).trans p.out)
    ((h.regs _ (by decide) (by decide) (by decide) (by decide)).trans p.auth) h.ptr
    (by rw [h.rd,h.wr]; exact p.access p.srcR le) (by rw [h.rd,h.wr]; exact p.access p.keyR le)
    (by rw [h.wr]; exact p.access p.outW le) (by rw [h.wr]; exact p.access p.authW le)
  refine WP.of_runBlock ⟨v,run,?_,m.trans (p.append_mem h le),fun r ra rb rc rt => (g r ra rt).trans (h.regs r ra rb rc rt),
    rd.trans h.rd,wr.trans h.wr,h.z.trans z⟩
  rw [off,Nat.add_assoc]

theorem remaining {k : Nat} (hk : k<2^31) (hi : i≤a.len) :
    WP isa (.block [.mov .r8 (.reg .rcx),.alu .sub .r8 (.reg .r10),.alu .cmp .r8 (imm k)]) t
      (fun u => SpanAt a s i u ∧ u.gpr .r8=BitVec.ofNat 64 (a.len-i) ∧ u.cf=some (decide (a.len-i<k))) := by
  have cx := (h.regs _ (by decide) (by decide) (by decide) (by decide)).trans p.endReg
  have sub : BitVec.ofNat 64 (a.start+a.len)-BitVec.ofNat 64 (a.start+i)=BitVec.ofNat 64 (a.len-i) := by
    rw [Offset.ofNat_sub_ofNat (by omega_using [hi]),Nat.add_sub_add_left]
  apply WP.of_runBlock
  refine ⟨_,by xrun [cx,h.ptr,sub,imm_eq hk],?_⟩
  refine ⟨⟨h.ptr,h.mem,fun r ra rb rc rt => ?_,h.rd,h.wr,h.z⟩,rfl,?_⟩
  · simp only [gpr_arithFlags,gpr_setReg_of_ne _ _ rb]; exact h.regs r ra rb rc rt
  · simp only [cf_arithFlags,toNat_ofNat_of_lt (show a.len-i<2^64 by omega_using [p.bound]),
      toNat_ofNat_of_lt (show k<2^64 by omega_using [hk])]

theorem cmp8 (hi : i≤a.len) (r8 : t.gpr .r8=BitVec.ofNat 64 (a.len-i)) :
    WP isa (.block [.alu .cmp .r8 (imm 8)]) t
      (fun u => SpanAt a s i u ∧ u.cf=some (decide (a.len-i<8))) := by
  apply WP.of_runBlock
  refine ⟨_,by xrun [r8],?_⟩
  refine ⟨⟨h.ptr,h.mem,h.regs,h.rd,h.wr,h.z⟩,?_⟩
  simp only [cf_arithFlags,toNat_ofNat_of_lt (show a.len-i<2^64 by omega_using [p.bound,hi])]
  rfl

theorem doneTest (hi : i≤a.len) :
    WP isa (.block [.alu .cmp .rcx (.reg .r10)]) t
      (fun u => SpanAt a s i u ∧ u.zf=some (decide (i=a.len))) := by
  have cx := (h.regs _ (by decide) (by decide) (by decide) (by decide)).trans p.endReg
  apply WP.of_runBlock
  refine ⟨_,by xrun [cx,h.ptr],?_⟩
  refine ⟨⟨h.ptr,h.mem,h.regs,h.rd,h.wr,h.z⟩,?_⟩
  simp only [zf_arithFlags,Offset.ofNat_sub_ofNat_beq (x:=a.start+a.len) (y:=a.start+i) (by omega_using [p.bound]) (by omega_using [p.bound,hi]),
    Nat.add_left_cancel_iff,Option.some.injEq]
  simp only [eq_comm]

theorem finalBytes (hi : i≤a.len) :
    WP isa (.seq (.block [.alu .cmp .rcx (.reg .r10)]) (.ite .e (.block []) tailBytes)) t (SpanAt a s a.len) := by
  refine WP.seq (WP.mono (p.doneTest h hi) fun u ⟨hu,cmp⟩ => ?_)
  refine WP.ite (decide (i=a.len)) (by simp [eval,cmp]) (fun eq => ?_) (fun ne => ?_)
  · exact WP.block_nil ((of_decide_eq_true eq) ▸ hu)
  · exact p.bytes_ok hu (by have := of_decide_eq_false ne; omega)

theorem afterEight (hi : i≤a.len) : WP isa (.seq
    (.block [.mov .r8 (.reg .rcx),.alu .sub .r8 (.reg .r10),.alu .cmp .r8 (imm 4)])
    (.seq (.ite .b (.block []) (.block (Impl.AesGcm.X86_64.DirectGather.word false)))
      (.seq (.block [.alu .cmp .rcx (.reg .r10)]) (.ite .e (.block []) tailBytes)))) t (SpanAt a s a.len) := by
  refine WP.seq (WP.mono (p.remaining h (k:=4) (by decide) hi) fun u ⟨hu,_,cmp⟩ => ?_)
  apply WP.seq
  refine WP.ite (decide (a.len-i<4)) (by simp [eval,cmp]) (fun _ => WP.block_nil (p.finalBytes hu hi)) (fun ne => ?_)
  have le : i+4≤a.len := by have := of_decide_eq_false ne; omega
  exact WP.mono (p.word_step hu false le) fun _ hu' => p.finalBytes hu' le

theorem xor_ok (hi : i<a.len) : WP isa tailXor t (SpanAt a s a.len) := by
  refine WP.seq (WP.mono (p.remaining h (k:=4) (by decide) (Nat.le_of_lt hi)) fun u ⟨hu,r8,cmp⟩ => ?_)
  refine WP.ite (decide (a.len-i<4)) (by simp [eval,cmp]) (fun _ => p.bytes_ok hu hi) (fun _ => ?_)
  refine WP.seq (WP.mono (p.cmp8 hu (Nat.le_of_lt hi) r8) fun v ⟨hv,cmp'⟩ => ?_)
  apply WP.seq
  refine WP.ite (decide (a.len-i<8)) (by simp [eval,cmp']) (fun _ => WP.block_nil (p.afterEight hv (Nat.le_of_lt hi))) (fun ne => ?_)
  have le : i+8≤a.len := by have := of_decide_eq_false ne; omega
  exact WP.mono (p.word_step hv true le) fun _ hv' => p.afterEight hv' le

end SpanPre

end VG.Proof.AesGcm.X86_64.Gather.DirectTail
end

public section
namespace VG.Proof.AesGcm.X86_64.Gather.DirectTail
open VG VG.X86_64 VG.Proof.AesGcm.X86_64.Short
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Gcm (Block blockAt)
open VG.Spec.Aes (bytesAt)

open VG.WriteBytes VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.DirectGather

structure TailCursors (a : TailArgs) (s : State) : Prop where
  desc : s.gpr .r11=a.descriptors
  first : s.gpr .rbx=a.tail1
  count : s.gpr .rcx=BitVec.ofNat 64 (a.firstLen%16)
  out : s.gpr .rsi=a.output
  rem : s.gpr .rbp=BitVec.ofNat 64 a.remaining

theorem tailArgs_ok {a : TailArgs} {H : Block} {s : State} (p : TailPre a H s) :
    ∃ u, runBlock isa tailArgs s=some u ∧ TailPre a H u ∧ TailCursors a u ∧
      u.zf=some (BitVec.ofNat 64 a.remaining==0) ∧ u.mem=s.mem ∧ u.rd=s.rd ∧ u.wr=s.wr := by
  have dr : InRegions (s.rd++s.wr) a.descriptors 8 :=
    p.descR _ _ ⟨_,List.mem_singleton_self _,by simp [Region.Contains]⟩
  have dl : InRegions (s.rd++s.wr) (a.descriptors+8#64) 8 :=
    p.descR _ _ ⟨_,List.mem_singleton_self _,Offset.contains_base a.descriptors (d:=8) (by decide) (by decide)⟩
  have nlt := Nat.lt_of_le_of_lt p.firstLe p.lenLt
  have amd := and15 (BitVec.ofNat 64 a.firstLen)
  rw [toNat_ofNat_of_lt nlt,imm_eq (by decide)] at amd
  have sub : BitVec.ofNat 64 a.firstLen-BitVec.ofNat 64 (a.firstLen%16)=BitVec.ofNat 64 a.consumed := by
    rw [ofNat_sub (Nat.mod_le ..) nlt]
    congr 1
    omega_using [show a.consumed=16*(a.firstLen/16) from rfl]
  have rem : BitVec.ofNat 64 a.len-BitVec.ofNat 64 a.consumed=BitVec.ofNat 64 a.remaining :=
    ofNat_sub (by omega_using [p.firstLe,show a.consumed=16*(a.firstLen/16) from rfl]) p.lenLt
  have dw := p.env.perm.wR (show 200+8≤2560 by decide)
  have lw := p.env.perm.wR (show 192+8≤2560 by decide)
  refine ⟨_,by xrun [tailArgs,BitVec.add_zero,p.env.rsp,p.env.r15,p.stackR,p.desc,dr,dl,p.first,p.firstLen,imm_eq (by decide : 15<2^31),amd,sub,dw,p.data,lw,p.len,rem],?_⟩
  refine ⟨?_,?_,?_,rfl,rfl,rfl⟩
  · exact {p with env := ⟨p.env.r13,p.env.r14,p.env.r15,p.env.rsp,p.env.perm.of_eq rfl rfl⟩}
  · exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  · simp only [zf_arithFlags,BitVec.and_self]

theorem tailStart_ok {a : TailArgs} {s : State} (env : Env a.ctx (a.work+16#64) a.work a.sp s) (h : TailCursors a s) :
    ∃ u, runBlock isa tailStart s=some u ∧
      u.mem=writeBytes s.mem (a.work+512#64) (List.replicate 16 0) ∧
      TailCursors a u ∧ u.gpr .rdi=a.work+512#64 ∧ u.gpr .rdx=a.work+1040#64 ∧ u.gpr .r10=0 ∧
      u.zf=some (BitVec.ofNat 64 (a.firstLen%16)==0) ∧
      Env a.ctx (a.work+16#64) a.work a.sp u ∧ u.rd=s.rd ∧ u.wr=s.wr ∧
      (∀ q, q≠.xmm7 → u.xmm q=s.xmm q) := by
  obtain ⟨v,run,m,x,g,rd,wr⟩ := zeroCipherBlock_ok s env
  rw [tailStart,runBlock_append,run,Option.bind_some]
  refine ⟨_,by xrun [g,env.r15,h.count,Impl.AesGcm.X86_64.Short.gO,Impl.AesGcm.X86_64.Short.kO],?_⟩
  refine ⟨m.trans (writeW_zero128 ..),⟨?_,?_,?_,?_,?_⟩,?_,?_,rfl,?_,?_,rd,wr,x⟩
  · exact (congrFun g _).trans h.desc
  · exact (congrFun g _).trans h.first
  · exact (congrFun g _).trans h.count
  · exact (congrFun g _).trans h.out
  · exact (congrFun g _).trans h.rem
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp
  · exact ⟨(congrFun g _).trans env.r13,(congrFun g _).trans env.r14,(congrFun g _).trans env.r15,
        (congrFun g _).trans env.rsp,env.perm.of_eq rd wr⟩

abbrev TailArgs.span (a : TailArgs) (src : Addr) (i n : Nat) : Span :=
  ⟨src,a.work+1040#64,a.output,a.work+512#64,i,n⟩

theorem span_range {a : TailArgs} {src : Addr} {i n : Nat} (fit : i+n≤a.remaining)
    (bound : a.remaining≤16) :
    let x := a.span src i n
    (x.range x.dst).Sub a.outR ∧ (x.range x.auth).Sub a.wR ∧ (x.range x.key).Sub a.wR ∧
    (x.range x.key).Disjoint (x.range x.auth) := by
  dsimp only [TailArgs.span,Span.range,Span.atStart]
  rw [add_ofNat_ofNat a.work 512 i,add_ofNat_ofNat a.work 1040 i]
  exact ⟨Offset.sub_base a.output fit,Offset.sub_base a.work (d:=512+i) (n:=n) (k:=2560) (by omega),
    Offset.sub_base a.work (d:=1040+i) (n:=n) (k:=2560) (by omega),
    Offset.disjoint a.work (d:=1040+i) (n:=n) (e:=512+i) (k:=n) (.inr (by omega)) (by omega) (by omega)⟩

theorem span_pre {a : TailArgs} {src : Addr} {i n : Nat} {s : State} (fit : i+n≤a.remaining)
    (bound : a.remaining≤16) (env : Env a.ctx (a.work+16#64) a.work a.sp s)
    (outW : Covers [a.outR] s.wr) (outWork : a.outR.Disjoint a.wR)
    (sourceR : Covers [(a.span src i n).range src] (s.rd++s.wr))
    (sourceW : ((a.span src i n).range src).Disjoint a.wR)
    (sourceO : ((a.span src i n).range src).Disjoint a.outR)
    (b : s.gpr .rbx=src) (k : s.gpr .rdx=a.work+1040#64) (o : s.gpr .rsi=a.output)
    (g : s.gpr .rdi=a.work+512#64) (rc : s.gpr .rcx=BitVec.ofNat 64 (i+n)) :
    SpanPre (a.span src i n) s := by
  obtain ⟨od,gh,ky,kg⟩ := span_range (src:=src) fit bound
  have restrict (base : Addr) (off m : Nat) {rs : List Region} (hit : off+n≤m) (cov : Covers [⟨base,m⟩] rs) :
      Covers [⟨base+BitVec.ofNat 64 off,n⟩] rs :=
    (Covers.of_sub (rs:=[⟨base+BitVec.ofNat 64 off,n⟩]) (rs':=[⟨base,m⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨_,List.mem_singleton_self _,off,rfl,hit⟩)).trans cov
  have w (d : Nat) (ok : d+i+n≤2560) : Covers [⟨a.work+BitVec.ofNat 64 d+BitVec.ofNat 64 i,n⟩] s.wr := by
    rw [add_ofNat_ofNat]
    exact restrict _ _ _ ok env.perm.w
  exact ⟨b,k,o,g,rc,Nat.le_trans fit bound,sourceR,(w 1040 (by omega)).right,restrict _ _ _ fit outW,
    w 512 (by omega),sourceO.sub_right od,sourceW.sub_right gh,(outWork.symm.sub_left ky).sub_right od,
    kg,(outWork.sub_left od).sub_right gh⟩

namespace TailArgs

theorem counts (a : TailArgs) (le : a.firstLen≤a.len) : a.remaining=a.firstLen%16+a.secondLen := by
  simp only [remaining,consumed,secondLen]
  omega

theorem cipher_split (a : TailArgs) (le : a.firstLen≤a.len) (m : Mem) :
    a.cipherBytes m=xb m a.tail1 (a.work+1040#64) (a.firstLen%16) ++
      xb m a.second (a.work+1040#64+BitVec.ofNat 64 (a.firstLen%16)) a.secondLen := by
  simp only [cipherBytes,textBytes,a.counts le,bytesAt_add,xb]
  exact List.zipWith_append (by rw [length_bytesAt,length_bytesAt])

abbrev span1 (a : TailArgs) := a.span a.tail1 0 (a.firstLen%16)
abbrev source2 (a : TailArgs) := a.second-BitVec.ofNat 64 (a.firstLen%16)
abbrev span2 (a : TailArgs) := a.span a.source2 (a.firstLen%16) a.secondLen

theorem span2_base (a : TailArgs) : a.span2.atStart a.source2=a.second := BitVec.sub_add_cancel ..

end TailArgs

structure TailsStart (a : TailArgs) (orig s : State) : Prop where
  env : Env a.ctx (a.work+16#64) a.work a.sp s
  cursors : TailCursors a s
  key : s.gpr .rdx=a.work+1040#64
  auth : s.gpr .rdi=a.work+512#64
  off : s.gpr .r10=0
  zf : s.zf=some (BitVec.ofNat 64 (a.firstLen%16)==0)
  slot : 0<a.secondLen → s.mem.readW a.secondSlot.base 64=a.second
  rd : s.rd=orig.rd
  wr : s.wr=orig.wr

structure TailsDone (a : TailArgs) (s t : State) : Prop where
  env : Env a.ctx (a.work+16#64) a.work a.sp t
  mem : t.mem=xw true s.mem a.output (a.work+512#64) (a.cipherBytes s.mem)
  z : ZKeep [] s t
  rd : t.rd=s.rd
  wr : t.wr=s.wr

theorem SpanAt.start {a : Span} {s : State} (off : s.gpr .r10=BitVec.ofNat 64 a.start) : SpanAt a s 0 s :=
  ⟨off,by simp [xb,bytesAt,xw_nil],fun _ _ _ _ _ => rfl,rfl,rfl,fun _ _ _ _ => rfl⟩

theorem firstTail_ok {a : TailArgs} {H : Block} {orig s : State} (p : TailPre a H orig) (b : TailsStart a orig s) :
    WP isa (.ite .e (.block []) tailXor) s (SpanAt a.span1 s (a.firstLen%16)) := by
  have reg : a.span1.range a.tail1=a.firstR := by simp [Span.range,Span.atStart]
  have n := a.counts p.firstLe
  have sp : SpanPre a.span1 s := span_pre (i:=0) (by omega) p.bounded b.env (b.wr ▸ p.write) p.outWork
    (by rw [reg,b.rd,b.wr]; exact p.firstRead) (reg ▸ p.firstWork) (reg ▸ p.firstOut)
    b.cursors.first b.key b.cursors.out b.auth (by simpa using b.cursors.count)
  have init : SpanAt a.span1 s 0 s := SpanAt.start b.off
  have flag := and_self_beq (a:=a.firstLen%16) (by omega)
  simp only [BitVec.and_self] at flag
  refine WP.ite (decide (a.firstLen%16=0)) (by simp only [eval,b.zf,flag]) (fun hz => ?_) (fun hn => ?_)
  · exact WP.block_nil ((of_decide_eq_true hz).symm ▸ init)
  · exact sp.xor_ok init (Nat.pos_of_ne_zero (of_decide_eq_false hn))

theorem cmpSecond_ok {a : TailArgs} {s u : State} (cur : TailCursors a s)
    (one : SpanAt a.span1 s (a.firstLen%16) u) (bound : a.remaining≤16) :
    ∃ v, runBlock isa [.alu .cmp .r10 (.reg .rbp)] u=some v ∧ SpanAt a.span1 s (a.firstLen%16) v ∧
      v.zf=some (decide (a.firstLen%16=a.remaining)) := by
  have ptr : u.gpr .r10=BitVec.ofNat 64 (a.firstLen%16) := by simpa using one.ptr
  have rb := (one.regs _ (by decide) (by decide) (by decide) (by decide)).trans cur.rem
  refine ⟨_,by xrun [ptr,rb],?_⟩
  refine ⟨⟨one.ptr,one.mem,one.regs,one.rd,one.wr,one.z⟩,?_⟩
  simp only [zf_arithFlags,sub_beq (a:=a.firstLen%16) (b:=a.remaining) (by omega) (by omega)]

theorem SpanAt.env {b : Span} {s u : State} {i : Nat} (h : SpanAt b s i u)
    {a : TailArgs} (env : Env a.ctx (a.work+16#64) a.work a.sp s) :
    Env a.ctx (a.work+16#64) a.work a.sp u :=
  ⟨(h.regs _ (by decide) (by decide) (by decide) (by decide)).trans env.r13,
    (h.regs _ (by decide) (by decide) (by decide) (by decide)).trans env.r14,
    (h.regs _ (by decide) (by decide) (by decide) (by decide)).trans env.r15,
    (h.regs _ (by decide) (by decide) (by decide) (by decide)).trans env.rsp,
    env.perm.of_eq h.rd h.wr⟩

abbrev firstCipher (a : TailArgs) (m : Mem) := xb m a.tail1 (a.work+1040#64) (a.firstLen%16)

theorem first_exact {a : TailArgs} {s u : State} (h : SpanAt a.span1 s (a.firstLen%16) u) :
    u.mem=xw true s.mem a.output (a.work+512#64) (firstCipher a s.mem) := by
  simpa [Span.atStart] using h.mem

theorem first_frame {a : TailArgs} {s u : State} (h : SpanAt a.span1 s (a.firstLen%16) u)
    (le : a.firstLen≤a.len) : Frame [a.outR,⟨a.work+512#64,16⟩] s.mem u.mem := by
  rw [first_exact h]
  have f := xw_frame true s.mem a.output (a.work+512#64) (firstCipher a s.mem)
  rw [length_xb] at f
  apply f.sub
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact ⟨_,List.mem_cons_self ..,Region.sub_prefix (by omega_using [a.counts le])⟩
  · exact ⟨_,by simp,Region.sub_prefix (Nat.le_of_lt (Nat.mod_lt _ (by decide)))⟩

theorem secondArgs_ok {a : TailArgs} {s u : State} (h : SpanAt a.span1 s (a.firstLen%16) u)
    (cu : TailCursors a s) (slot : u.mem.readW a.secondSlot.base 64=a.second)
    (readSlot : InRegions (u.rd++u.wr) a.secondSlot.base 8) :
    ∃ v, runBlock isa secondArgs u=some v ∧ v.mem=u.mem ∧ v.gpr .rbx=a.source2 ∧
      v.gpr .rcx=BitVec.ofNat 64 a.remaining ∧ (∀ r,r≠.rbx → r≠.rcx → v.gpr r=u.gpr r) ∧
      v.rd=u.rd ∧ v.wr=u.wr ∧ ZKeep [] u v := by
  have off : u.gpr .r10=BitVec.ofNat 64 (a.firstLen%16) := by simpa using h.ptr
  have de := (h.regs _ (by decide) (by decide) (by decide) (by decide)).trans cu.desc
  have re := (h.regs _ (by decide) (by decide) (by decide) (by decide)).trans cu.rem
  change u.mem.readW (a.descriptors+16#64) 64=a.second at slot
  change InRegions (u.rd++u.wr) (a.descriptors+16#64) 8 at readSlot
  refine ⟨_,by xrun [secondArgs,de,re,slot,readSlot,off],?_⟩
  refine ⟨rfl,rfl,rfl,?_,rfl,rfl,fun _ _ _ _ => rfl⟩
  intro r hb hc
  simp only [gpr_setReg_of_ne _ _ hb,gpr_setReg_of_ne _ _ hc,gpr_arithFlags]

theorem away {a : TailArgs} {r : Region} (dest : r.Disjoint a.outR) (work : r.Disjoint a.wR) :
      ∀ q ∈ [a.outR,⟨a.work+512#64,16⟩],r.Disjoint q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl
    · exact dest
    · exact work.sub_right (Offset.sub_base a.work (by decide))

theorem second_slot {a : TailArgs} {H : Block} {orig s v : State} (p : TailPre a H orig)
    (b : TailsStart a orig s) (one : SpanAt a.span1 s (a.firstLen%16) v) (pos : 0<a.secondLen) :
    v.mem.readW a.secondSlot.base 64=a.second ∧ InRegions (v.rd++v.wr) a.secondSlot.base 8 := by
  have fr := first_frame one p.firstLe
  have sl := (fr.readW (r:=a.secondSlot) (a:=a.secondSlot.base) (w:=64) (by simp [Region.Contains])
    (away (p.slotOut pos) (p.slotWork pos)) (by decide)).trans (b.slot pos)
  exact ⟨sl,by rw [one.rd,one.wr,b.rd,b.wr]; exact p.secondSlotR pos⟩

theorem tails_ok {a : TailArgs} {H : Block} {orig s : State}
    (p : TailPre a H orig) (b : TailsStart a orig s) : WP isa tails s (TailsDone a s) := by
  refine WP.seq (WP.mono (firstTail_ok p b) fun u one => ?_)
  obtain ⟨v,run,one,flag⟩ := cmpSecond_ok b.cursors one p.bounded
  apply WP.seq
  refine WP.of_runBlock ⟨v,run,?_⟩
  refine WP.ite (decide (a.firstLen%16=a.remaining)) (by simp [eval,flag]) (fun hz => ?_) (fun hn => ?_)
  · apply WP.block_nil
    have zero : a.secondLen=0 := by omega_using [a.counts p.firstLe,of_decide_eq_true hz]
    refine ⟨one.env b.env,?_,one.z,one.rd,one.wr⟩
    rw [a.cipher_split p.firstLe,zero]
    simpa [xb,bytesAt] using first_exact one
  · have pos : 0<a.secondLen := by omega_using [a.counts p.firstLe,of_decide_eq_false hn]
    have fr := first_frame one p.firstLe
    have vv := one.env b.env
    obtain ⟨slot,read⟩ := second_slot p b one pos
    obtain ⟨w,prep,m,src,count,regs,rd,wr,z⟩ := secondArgs_ok one b.cursors slot read
    apply WP.seq
    refine WP.of_runBlock ⟨w,prep,?_⟩
    have env : Env a.ctx (a.work+16#64) a.work a.sp w := ⟨(regs _ (by decide) (by decide)).trans vv.r13,
      (regs _ (by decide) (by decide)).trans vv.r14,(regs _ (by decide) (by decide)).trans vv.r15,
      (regs _ (by decide) (by decide)).trans vv.rsp,vv.perm.of_eq rd wr⟩
    have rd' : w.rd=s.rd := rd.trans one.rd
    have wr' : w.wr=s.wr := wr.trans one.wr
    have unchanged (r : Reg) (hb : r≠.rbx) (hc : r≠.rcx) (ha : r≠.rax) (hi : r≠.r8) (hj : r≠.r9) (ht : r≠.r10) :
        w.gpr r=s.gpr r := (regs _ hb hc).trans (one.regs _ ha hi hj ht)
    have reg : a.span2.range a.source2=a.secondR := by simp only [Span.range,a.span2_base]
    have sp : SpanPre a.span2 w := span_pre (i:=a.firstLen%16) (Nat.le_of_eq (a.counts p.firstLe).symm) p.bounded env
      (by rw [wr',b.wr]; exact p.write) p.outWork (by rw [reg,rd',wr',b.rd,b.wr]; exact p.secondRead pos)
      (reg ▸ p.secondWork pos) (reg ▸ p.secondOut pos) src
      ((unchanged _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b.key)
      ((unchanged _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b.cursors.out)
      ((unchanged _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b.auth)
      (by rw [←a.counts p.firstLe]; exact count)
    have off := (regs .r10 (by decide) (by decide)).trans one.ptr
    refine WP.mono (sp.xor_ok (SpanAt.start (by simpa using off)) pos) fun t two => ?_
    refine ⟨two.env env,?_,(one.z.trans z).trans two.z,two.rd.trans rd',two.wr.trans wr'⟩
    let K := a.work+1040#64+BitVec.ofNat 64 (a.firstLen%16)
    have sr := bytesAt_frame fr (away (p.secondOut pos) (p.secondWork pos)) (by omega_using [p.bounded,a.counts p.firstLe])
    have ks : (⟨K,a.secondLen⟩ : Region).Sub a.wR := by
      dsimp only [K]; rw [add_ofNat_ofNat]; exact Offset.sub_base _ (by omega_using [a.counts p.firstLe,p.bounded])
    have kg : (⟨K,a.secondLen⟩ : Region).Disjoint ⟨a.work+512#64,16⟩ := by
      dsimp only [K]; rw [add_ofNat_ofNat]
      exact Offset.disjoint _ (.inr (by omega)) (by omega_using [a.counts p.firstLe,p.bounded]) (by decide)
    have kr : bytesAt v.mem K a.secondLen=bytesAt s.mem K a.secondLen := bytesAt_frame fr (fun q hq => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl|rfl
      · exact p.outWork.symm.sub_left ks
      · exact kg) (by omega_using [a.counts p.firstLe,p.bounded])
    have xy : xb w.mem a.second K a.secondLen=xb s.mem a.second K a.secondLen := by simp only [xb,m,sr,kr]
    rw [two.mem,a.span2_base,show a.span2.atStart a.span2.key=K from rfl,xy,m,first_exact one,a.cipher_split p.firstLe]
    have eq := xw_append true s.mem (S:=a.output) (D:=a.work+512#64) (n:=a.remaining) (firstCipher a s.mem)
      (xb s.mem a.second K a.secondLen) (by omega_using [p.bounded])
      (by rw [length_xb,length_xb,←a.counts p.firstLe])
      (fun _ => p.outWork.sub_right (Offset.sub_base _ (by omega_using [p.bounded])))
    rw [length_xb] at eq
    exact eq

abbrev padR (a : TailArgs) : Region := ⟨a.work+512#64,16⟩
abbrev tailFrame (a : TailArgs) : List Region := [a.outR,padR a]
abbrev finalFrame (a : TailArgs) : List Region := [⟨a.work,16⟩,⟨a.work+512#64,32⟩,a.outR]

theorem cipher_length {a : TailArgs} {m : Mem} (le : a.firstLen≤a.len) : (a.cipherBytes m).length=a.remaining := by
  rw [a.cipher_split le,List.length_append,length_xb,length_xb,a.counts le]

theorem zero_frame {a : TailArgs} {m m' : Mem} (zero : m'=writeBytes m (a.work+512#64) (List.replicate 16 0)) :
    Frame [padR a] m m' := zero ▸ writeBytes_frame' _ (List.length_replicate ..)

theorem zero_cipher {a : TailArgs} {H : Block} {orig : State} (p : TailPre a H orig) {m : Mem}
    (f : Frame [padR a] orig.mem m) : a.cipherBytes m=a.cipherBytes orig.mem := by
  have read {d : Addr} {n : Nat} (h : (⟨d,n⟩ : Region).Disjoint (padR a)) (le : n≤16) :
      bytesAt m d n=bytesAt orig.mem d n := bytesAt_frame f (fun q hq => by
        simp only [List.mem_singleton] at hq; exact hq ▸ h) (by omega)
  have sub : (padR a).Sub a.wR := Offset.sub_base a.work (by decide)
  have second : bytesAt m a.second a.secondLen=bytesAt orig.mem a.second a.secondLen := by
    by_cases e : a.secondLen=0
    · simp [e,bytesAt]
    · exact read ((p.secondWork (Nat.pos_of_ne_zero e)).sub_right sub) (by omega_using [a.counts p.firstLe,p.bounded])
  have ky : (⟨a.work+1040#64,a.remaining⟩ : Region).Disjoint (padR a) :=
    Offset.disjoint _ (.inr (by decide)) (by omega_using [p.bounded]) (by decide)
  simp only [TailArgs.cipherBytes,TailArgs.textBytes,read (p.firstWork.sub_right sub) (by omega),second,read ky p.bounded]

theorem stage_mem {a : TailArgs} {n : Nat} {m m₀ m' : Mem} {xs : List Byte}
    (hn : n≤16) (out : (⟨a.output,n⟩ : Region).Disjoint a.wR)
    (len : xs.length=n) (zero : m₀=writeBytes m (a.work+512#64) (List.replicate 16 0))
    (cipher : m'=xw true m₀ a.output (a.work+512#64) xs) :
    bytesAt m' a.output n=xs ∧ bytesAt m' (a.work+512#64) 16=xs++Spec.Gcm.zeros (16-n) := by
  let g := a.work+512#64
  have d : (⟨a.output,n⟩ : Region).Disjoint ⟨g,n⟩ := out.sub_right (Offset.sub_base a.work (by omega))
  have same (m₁ : Mem) (b : Addr) : bytesAt (writeBytes m₁ b xs) b n=xs := by
    rw [←len]
    exact bytesAt_writeBytes_self _ _ _ (by omega)
  have z16 : bytesAt m₀ g 16 = List.replicate 16 0 := by rw [zero]; exact bytesAt_writeBytes_self _ _ _ (by decide)
  have zrest : bytesAt m₀ (g+BitVec.ofNat 64 n) (16-n)=Spec.Gcm.zeros (16-n) := by
    obtain e := bytesAt_add m₀ g n (16-n)
    rw [Nat.add_sub_cancel' hn,z16,show List.replicate 16 (0 : Byte)=List.replicate n 0++List.replicate (16-n) 0 by
      rw [List.replicate_append_replicate,Nat.add_sub_cancel' hn]] at e
    exact ((List.append_inj e (by rw [List.length_replicate,length_bytesAt])).2).symm
  have outside {b : Addr} {k : Nat} {m₁ : Mem} {q : Addr} (sep : (⟨b,k⟩ : Region).Disjoint ⟨q,n⟩) (le : k≤16) :
      bytesAt (writeBytes m₁ q xs) b k=bytesAt m₁ b k := bytesAt_frame (writeBytes_frame' _ len) (fun r hr => by
        simp only [List.mem_singleton] at hr; exact hr ▸ sep) (by omega)
  simp only [cipher,xw,ite_true]
  refine ⟨(outside d hn).trans (same ..),?_⟩
  change bytesAt _ g 16=_
  rw [←Nat.add_sub_cancel' hn,bytesAt_add,Nat.add_sub_cancel' hn,same]
  congr 1
  rw [outside (Offset.disjoint_base g (Nat.le_refl n) (by omega)) (by omega)]
  refine (outside (q:=a.output) ?_ (by omega)).trans zrest
  apply out.symm.sub_left
  dsimp only [g]; rw [add_ofNat_ofNat]
  exact Offset.sub_base a.work (by omega)

abbrev authBlocks (a : TailArgs) (m : Mem) :=
  (if a.remaining=0 then [] else [Spec.Gcm.ofBytes (a.cipherBytes m++Spec.Gcm.zeros (16-a.remaining))]) ++
    [Spec.Gcm.ofBytes (Proof.Gcm.lensBlock a.aadLen a.len)]

structure TailDone (a : TailArgs) (H : Block) (s t : State) : Prop where
  env : Env a.ctx (a.work+16#64) a.work a.sp t
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  frame : Frame (finalFrame a) s.mem t.mem
  data : bytesAt t.mem a.output a.remaining=a.cipherBytes s.mem
  tag : blockAt t.mem a.work=Spec.Gcm.ghashFrom H (blockAt s.mem (yA a.work)) (authBlocks a s.mem) ^^^
    blockAt s.mem (a.work+1024#64)

theorem positiveFinish {a : TailArgs} {H : Block} {s b t : State} (p : TailPre a H s)
    (pos : a.remaining≠0) (mb : b.mem=writeBytes s.mem (a.work+512#64) (List.replicate 16 0))
    (rb : b.rd=s.rd) (wb : b.wr=s.wr) (xb : ∀ q,q≠.xmm7 → b.xmm q=s.xmm q) (done : TailsDone a b t) :
    WP isa (.block (Impl.AesGcm.X86_64.Short.finLens ++ Impl.AesGcm.X86_64.Short.finGh2 ++ Impl.AesGcm.X86_64.Short.tagK 0)) t
      (TailDone a H s) := by
  have fz := zero_frame mb
  have c := zero_cipher p fz
  have ct := done.mem.trans (congrArg (xw true b.mem a.output (a.work+512#64)) c)
  obtain ⟨dst,buf⟩ := stage_mem p.bounded p.outWork (cipher_length p.firstLe) mb ct
  have f : Frame (tailFrame a) s.mem t.mem := by
    refine (fz.mono (by simp [tailFrame])).trans ?_
    rw [ct]
    have g := xw_frame true b.mem a.output (a.work+512#64) (a.cipherBytes s.mem)
    rw [cipher_length p.firstLe] at g
    refine g.sub (fun r hr => ?_)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact ⟨a.outR,List.mem_cons_self ..,fun _ hit => hit⟩
    · exact ⟨padR a,by simp [tailFrame],Region.sub_prefix p.bounded⟩
  have away {d k : Nat} (small : d+k≤512 ∨ 528≤d) (fit : d+k≤2560) :
      ∀ q ∈ tailFrame a,(⟨a.work+BitVec.ofNat 64 d,k⟩ : Region).Disjoint q := by
    intro q hq
    simp only [tailFrame,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl
    · exact p.outWork.symm.sub_left (Offset.sub_base a.work fit)
    · exact Offset.disjoint a.work small (by omega) (by decide)
  have rW (d : Nat) (small : d+8≤512) : t.mem.readW (a.work+BitVec.ofNat 64 d) 64=s.mem.readW (a.work+BitVec.ofNat 64 d) 64 :=
    f.readW (r:=⟨a.work+BitVec.ofNat 64 d,8⟩) (by simp [Region.Contains]) (away (.inl small) (by omega)) (by decide)
  have zx (q : XReg) (hq : q≠.xmm7) : t.xmm q=s.xmm q := (done.z q (by simp) 0 (by decide)).trans (xb q hq)
  refine WP.mono (finStaged_ok true (H:=H) (D:=a.work) (r:=16) done.env
    ((zx _ (by decide)).trans p.x0) ((zx _ (by decide)).trans p.x1)
    (by rw [zx _ (by decide)]; exact p.h1) (by rw [zx _ (by decide),zx _ (by decide)]; exact p.h2)
    ((rW _ (by decide)).trans p.aad) ((rW _ (by decide)).trans p.len)) fun v ⟨ev,rv,wv,fv,tag⟩ => ?_
  refine ⟨ev,(rv.trans done.rd).trans rb,(wv.trans done.wr).trans wb,?_,?_,?_⟩
  · refine (f.sub (fun r hr => ?_)).trans (fv.mono (by simp [finalFrame]))
    simp only [tailFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact ⟨a.outR,by simp [finalFrame],fun _ hit => hit⟩
    · exact ⟨⟨a.work+512#64,32⟩,by simp [finalFrame],Region.sub_prefix (by decide)⟩
  · rw [bytesAt_frame fv (fun r hr => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl
      · exact p.outWork.sub_right (Region.sub_prefix (by decide))
      · exact p.outWork.sub_right (Offset.sub_base a.work (by decide))
      · exact p.outWork.sub_right (Region.sub_prefix (by decide))) (by omega_using [p.bounded])]
    exact dst
  · have y : blockAt t.mem (yA a.work)=blockAt s.mem (yA a.work) := by
      simp only [yA,add_ofNat_ofNat]
      exact blockAt_frame f (away (.inl (by decide)) (by decide))
    have mask := blockAt_frame (p:=a.work+1024#64) f (away (.inr (by decide)) (by decide))
    have staged : blockAt t.mem (a.work+512#64)=Spec.Gcm.ofBytes (a.cipherBytes s.mem++Spec.Gcm.zeros (16-a.remaining)) := by rw [Spec.Gcm.blockAt,buf]
    rw [y,mask,staged] at tag
    simpa [authBlocks,pos] using tag

theorem tailArgs_branch_ok {a : TailArgs} {H : Block} {s : State} (p : TailPre a H s) (cu : TailCursors a s)
    (flag : s.zf=some (BitVec.ofNat 64 a.remaining==0)) :
    WP isa (.ite .e (.block (Impl.AesGcm.X86_64.Short.finLens ++ Impl.AesGcm.X86_64.Short.finGh1 ++ Impl.AesGcm.X86_64.Short.tagK 0))
      (.seq (.block tailStart) (.seq tails (.block (Impl.AesGcm.X86_64.Short.finLens ++ Impl.AesGcm.X86_64.Short.finGh2 ++
        Impl.AesGcm.X86_64.Short.tagK 0))))) s (TailDone a H s) := by
  have zf := and_self_beq (a:=a.remaining) (by omega_using [p.bounded])
  simp only [BitVec.and_self] at zf
  refine WP.ite (decide (a.remaining=0)) (by simp only [eval,flag,zf]) (fun eq => ?_) (fun ne => ?_)
  · have z := of_decide_eq_true eq
    refine WP.mono (finStaged_ok false (H:=H) (D:=a.output) (r:=a.remaining) p.env p.x0 p.x1 p.h1 p.h2 p.aad p.len)
      fun t ⟨env,rd,wr,f,tg⟩ => ?_
    refine ⟨env,rd,wr,f,?_,?_⟩
    · have nil := List.length_eq_zero_iff.mp ((cipher_length (m:=s.mem) p.firstLe).trans z)
      simp only [z,nil,bytesAt,List.range_zero,List.map_nil]
    · simpa [authBlocks,z] using tg
  · obtain ⟨b,run,mb,cb,auth,key,off,zfb,eb,rd,wr,xb⟩ := tailStart_ok p.env cu
    apply WP.seq
    refine WP.of_runBlock ⟨b,run,?_⟩
    have slot (pos : 0<a.secondLen) : b.mem.readW a.secondSlot.base 64=a.second := by
      have sf := zero_frame mb
      refine (sf.readW (r:=a.secondSlot) (a:=a.secondSlot.base) (w:=64) (by simp [Region.Contains])
        (fun r hr => ?_) (by decide)).trans (p.second pos)
      simp only [List.mem_singleton] at hr
      exact hr ▸ (p.slotWork pos).sub_right (Offset.sub_base a.work (by decide))
    exact WP.seq (WP.mono (tails_ok p ⟨eb,cb,key,auth,off,zfb,slot,rd,wr⟩) fun t done =>
      positiveFinish p (of_decide_eq_false ne) mb rd wr xb done)

theorem twoTail_ok {a : TailArgs} {H : Block} {s : State} (p : TailPre a H s) : WP isa twoTail s (TailDone a H s) := by
  obtain ⟨u,run,h,cu,fl,m,rd,wr⟩ := tailArgs_ok p
  apply WP.seq
  refine WP.of_runBlock ⟨u,run,WP.mono (tailArgs_branch_ok h cu fl) (fun t d => ?_)⟩
  exact ⟨d.env,d.rd.trans rd,d.wr.trans wr,m ▸ d.frame,m ▸ d.data,m ▸ d.tag⟩

end VG.Proof.AesGcm.X86_64.Gather.DirectTail
end
