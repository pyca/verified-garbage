module

import VerifiedGarbage.Proof.Rsa.X86.Chain.Chunk
import VerifiedGarbage.Proof.Mont.X86.Square.Scalar
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Rsa.X86.Chain.Word

/-! A public-count loop over eight-word chunks and scalar tails. -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Chain
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt

structure Inv (s₀ : State) (base : Addr) (a b d n i : Nat) (op : AluOp) (s : State) : Prop where
  keep : Keeps [.eax,.ebx,.ecx,.edx,.ebp,.edi] s₀ s
  pa : PtrAt s base .ebp (a+4*i)
  pb : PtrAt s base .ebx (b+4*i)
  pd : PtrAt s base .edi (d+4*i)
  count : (s.gpr .edx).toNat=4*(n-i)
  frame : Outside base d (4*i) s₀.mem s.mem
  value : ∃ c : Bool,s.gpr .ecx=cmask c ∧
    Rel op (val32 s.mem base d i) (val32 s₀.mem base a i)
      (val32 s₀.mem base b i) (2^(32*i)) 0 c.toNat

theorem Inv.flags {s₀ s t : State} {base : Addr} {a b d n i : Nat} {op : AluOp}
    (I : Inv s₀ base a b d n i op s) (F : Fupd s t) : Inv s₀ base a b d n i op t := by
  refine ⟨I.keep.trans (F.keeps _),?_,?_,?_,?_,?_,?_⟩
  · simpa only [PtrAt,F.gpr] using I.pa
  · simpa only [PtrAt,F.gpr] using I.pb
  · simpa only [PtrAt,F.gpr] using I.pd
  · simpa only [F.gpr] using I.count
  · simpa only [F.mem] using I.frame
  · simpa only [F.gpr,F.mem] using I.value

theorem inv_chunk {s₀ s : State} {base : Addr} {size a b d n i k : Nat} {op : AluOp}
    (hw : Ws s₀ base size) (hop : op=.adc ∨ op=.sbb)
    (ha : a+4*n≤size) (hb : b+4*n≤size) (hd : d+4*n≤size)
    (da : d≤a ∨ a+4*n≤d) (db : d≤b ∨ b+4*n≤d)
    (small : 4*n<2^32) (ik : i+k≤n) (I : Inv s₀ base a b d n i op s) :
    WP isa (.block (VG.Impl.Rsa.X86.Chain.chunk op k)) s (Inv s₀ base a b d n (i+k) op) := by
  obtain ⟨c,C,V⟩ := I.value
  refine WP.mono (chunk_ok (hw.of_keeps I.keep) hop I.pa I.pb I.pd
    (by omega) (by omega) (by omega) (by omega) (by omega) I.count (by omega) C) ?_
  rintro t ⟨O,K,pa,pb,pd,count,c',C',V'⟩
  have aw : val32 s.mem base (a+4*i) k=val32 s₀.mem base (a+4*i) k :=
    I.frame.val32 (by omega) (by have := hw.nowrap;omega)
  have bw : val32 s.mem base (b+4*i) k=val32 s₀.mem base (b+4*i) k :=
    I.frame.val32 (by omega) (by have := hw.nowrap;omega)
  have preVal : val32 t.mem base d i=val32 s.mem base d i :=
    O.val32 (by omega) (by have := hw.nowrap;omega)
  rw [aw,bw] at V'
  refine ⟨I.keep.trans K,?_,?_,?_,by omega,
    (I.frame.mono (Nat.le_refl _) (by omega)).trans (O.mono (by omega) (by omega)),c',C',?_⟩
  · simpa only [Nat.mul_add,Nat.add_assoc] using pa
  · simpa only [Nat.mul_add,Nat.add_assoc] using pb
  · simpa only [Nat.mul_add,Nat.add_assoc] using pd
  · rw [val32_append,val32_append,val32_append,preVal,Nat.mul_add,Nat.pow_add]
    simpa only [Nat.mul_comm] using rel_join V V'

theorem loop_ok {s : State} {base : Addr} {size a b d n : Nat} {op : AluOp}
    (hw : Ws s base size) (hop : op=.adc ∨ op=.sbb) (hn : 0<n)
    (ha : a+4*n≤size) (hb : b+4*n≤size) (hd : d+4*n≤size)
    (da : d≤a ∨ a+4*n≤d) (db : d≤b ∨ b+4*n≤d)
    (pa : PtrAt s base .ebp a) (pb : PtrAt s base .ebx b) (pd : PtrAt s base .edi d)
    (count : (s.gpr .edx).toNat=4*n) (mask : s.gpr .ecx=cmask false) :
    WP isa (VG.Impl.Rsa.X86.Chain.loop op) s (Inv s base a b d n n op) := by
  have small : 4*n<2^32 := by have := (s.gpr .edx).isLt;omega
  have initial : Inv s base a b d n 0 op s := by
    refine ⟨Keeps.refl _ _,by simpa using pa,by simpa using pb,by simpa using pd,
      by simpa using count,Outside.refl _ _ _ _,false,mask,?_⟩
    simp [Rel,val32]
  unfold VG.Impl.Rsa.X86.Chain.loop
  refine WP.loop (M := isa)
    (fun rem t => ∃ i,rem=n-i ∧ i<n ∧ Inv s base a b d n i op t) ?_ n s ⟨0,rfl,hn,initial⟩
  rintro rem t ⟨i,rfl,hi,I⟩
  have finish {k : Nat} (hk : 0<k) (ik : i+k≤n) {u : State}
      (J : Inv s base a b d n (i+k) op u) :
      WP isa (.block [.alu .cmp .edx (.imm 0)]) u fun v =>
        (eval .ne v=some false ∧ Inv s base a b d n n op v) ∨
        eval .ne v=some true ∧ ∃ rem',rem'<n-i ∧ ∃ i',rem'=n-i' ∧ i'<n ∧ Inv s base a b d n i' op v := by
    refine wp_cmpS rfl fun v F Z => WP.block_nil ?_
    have J' := J.flags F
    have word : u.gpr .edx=BitVec.ofNat 32 (4*(n-(i+k))) :=
      BitVec.eq_of_toNat_eq (by rw [J.count,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)])
    have zero : v.zf=some (decide (i+k=n)) := by
      rw [Z,word]
      change some ((BitVec.ofNat 32 (4*(n-(i+k))) - 0#32 == 0#32)) = _
      simp only [BitVec.sub_zero]
      apply congrArg some
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq,decide_eq_true_eq]
      constructor
      · intro H
        have Hn := congrArg BitVec.toNat H
        simp only [BitVec.toNat_ofNat] at Hn
        omega
      · intro done
        simp [done]
    by_cases done : i+k=n
    · exact .inl ⟨by simp only [eval,zero,done,decide_true,Option.map_some,Bool.not_true],done ▸ J'⟩
    · exact .inr ⟨by simp only [eval,zero,decide_eq_false done,Option.map_some,Bool.not_false],
        n-(i+k),by omega,i+k,rfl,by omega,J'⟩
  refine WP.seq (VG.Proof.Mont.X86.Square.wp_cmpCF rfl fun u F C => WP.block_nil ?_)
  have I' := I.flags F
  have choose : eval .ae u=some (!decide (4*(n-i)<32)) := by
    change u.cf.map not=_
    rw [C,I.count]
    rfl
  refine WP.seq (WP.ite (!decide (4*(n-i)<32)) choose ?_ ?_)
  · intro yes
    have ik : i+8≤n := by
      have ge : ¬4*(n-i)<32 := by simpa using yes
      omega
    exact WP.mono (inv_chunk hw hop ha hb hd da db small ik I') fun v J => finish (by decide) ik J
  · intro _
    have ik : i+1≤n := by omega
    exact WP.mono (inv_chunk hw hop ha hb hd da db small ik I') fun v J => finish (by decide) ik J

end VG.Proof.Rsa.X86.Chain
