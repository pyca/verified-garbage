module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
public import VerifiedGarbage.Impl.Rsa.X86.Chain
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
public import VerifiedGarbage.TCB.X86.Isa

/-! ### `Mont.X86.Square.Scalar`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86

theorem wp_cmpCF {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {src : Src} {v : BitVec 32}
    (h : readSrc s src = some v)
    (k : ∀ t, VG.X86.Wp.Fupd s t → t.cf = some (decide ((s.gpr d).toNat < v.toNat)) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .cmp d src :: is)) s Q :=
  VG.X86.Wp.cons (s' := arithFlags s (s.gpr d-v) (decide ((s.gpr d).toNat<v.toNat)) (subOverflow (s.gpr d) v (s.gpr d-v)))
    (by simp only [exec, execAlu, h, Option.bind_some]) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

end VG.Proof.Mont.X86.Square

end

end

/-! ### `Rsa.X86.Chain.Word`, which only this module used -/

section

/-! One carry-preserving word, sharing the existing add/subtract arithmetic lemmas. -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Chain
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt

def Rel (op : AluOp) (v a b p cin cout : Nat) : Prop :=
  if op = .adc then v+p*cout=a+b+cin else v+b+cin=a+p*cout

theorem rel_join {op : AluOp} {v a b p cin c w x y r c' : Nat}
    (h : Rel op v a b p cin c) (hw : Rel op w x y r c c') :
    Rel op (v+p*w) (a+p*x) (b+p*y) (r*p) cin c' := by
  unfold Rel at *
  by_cases hop : op = .adc <;> simp only [hop, ↓reduceIte] at *
  · have E := congrArg (p*·) hw
    simp only [Nat.mul_add,Nat.mul_left_comm,Nat.mul_comm] at E ⊢
    omega_using [h, E]
  · have E := congrArg (p*·) hw
    simp only [Nat.mul_add,Nat.mul_left_comm,Nat.mul_comm] at E ⊢
    omega_using [h, E]

theorem rel_step {op : AluOp} {v a b p cin c w x y c' : Nat}
    (h : Rel op v a b p cin c) (hw : Rel op w x y (2^32) c c') :
    Rel op (v+p*w) (a+p*x) (b+p*y) (2^32*p) cin c' := by
  exact rel_join h hw

theorem word_ok {s : State} {base : Addr} {size a b d j : Nat} {op : AluOp} {cin : Bool}
    (hw : Ws s base size) (hop : op=.adc ∨ op=.sbb)
    (pa : PtrAt s base .ebp a) (pb : PtrAt s base .ebx b) (pd : PtrAt s base .edi d)
    (ha : a+4*j+4≤size) (hb : b+4*j+4≤size) (hd : d+4*j+4≤size)
    (cf : s.cf=some cin) :
    WP isa (.block (VG.Impl.Rsa.X86.Chain.word op (4*j))) s fun t =>
      Outside base (d+4*j) 4 s.mem t.mem ∧ Keeps [.eax] s t ∧
      ∃ cout : Bool, t.cf=some cout ∧
        Rel op (w32 t.mem base (d+4*j)) (w32 s.mem base (a+4*j))
          (w32 s.mem base (b+4*j)) (2^32) cin.toNat cout.toNat := by
  unfold VG.Impl.Rsa.X86.Chain.word
  refine wp_movS (readSrc_ptr hw pa ha) fun s₁ U cf₁ => ?_
  have hw₁ := hw.of_keeps U.keeps
  have pb₁ : PtrAt s₁ base .ebx b := by rw [PtrAt,U.other _ (by decide)]; exact pb
  have read := readSrc_ptr hw₁ pb₁ hb
  have carry : s₁.cf=some cin := by rw [cf₁,cf]
  have Step : WP isa (.block [.alu op .eax (.mem (at_ .ebx (4*j)))]) s₁ fun t =>
      Keeps [.eax] s₁ t ∧ t.mem=s₁.mem ∧ ∃ cout : Bool,t.cf=some cout ∧
        Rel op (t.gpr .eax).toNat (w32 s.mem base (a+4*j))
          (w32 s.mem base (b+4*j)) (2^32) cin.toNat cout.toNat := by
    rcases hop with rfl|rfl
    · refine wp_adcS read carry fun t T C => WP.block_nil ⟨T.keeps,T.mem,_,C,?_⟩
      have H := adc_rel (s₁.gpr .eax) (s₁.mem.readW (off base (b+4*j)) 32) cin
      simpa [Rel,T.gpr,U.gpr,U.mem,w32] using H
    · refine wp_sbbS read carry fun t T C => WP.block_nil ⟨T.keeps,T.mem,_,C,?_⟩
      have H := sbb_rel (s₁.gpr .eax) (s₁.mem.readW (off base (b+4*j)) 32) cin
      simpa [Rel,T.gpr,U.gpr,U.mem,w32] using H
  change WP isa (.block ([.alu op .eax (.mem (at_ .ebx (4*j)))] ++
    [.store (at_ .edi (4*j)) .eax])) s₁ _
  refine WP.block_append (WP.mono Step fun t ⟨K,M,c,C,V⟩ => ?_)
  have hw₂ := hw₁.of_keeps K
  have pd₂ : PtrAt t base .edi d := by rw [PtrAt,K.1 _ (by decide),U.other _ (by decide)];exact pd
  refine wp_storeS (ea_ptr hw₂ pd₂ (by omega_using [hd])) (ws_write hw₂ hd) fun u S => WP.block_nil ?_
  refine ⟨?_,(U.keeps.trans K).trans (S.keeps _),c,by rw [S.cf,C],?_⟩
  · rw [S.mem,M,U.mem]
    exact writeW32_outside _ _ _ (by have := hw.nowrap;omega_using [hd, this])
  · rw [S.mem,w32_write_self]
    exact V

end VG.Proof.Rsa.X86.Chain

end

end

/-! ### `Rsa.X86.Chain.Loop`, which only this module used -/

section

/-! ### `Rsa.X86.Chain.Chunk`, which only this module used -/

section

/-! ### `Rsa.X86.Chain.Words`, which only this module used -/

section

/-! A carry chain of any fixed number of words, with pointers held still. -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Chain
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt

theorem words_ok {s : State} {base : Addr} {size a b d n : Nat} {op : AluOp} {cin : Bool}
    (hw : Ws s base size) (hop : op=.adc ∨ op=.sbb)
    (pa : PtrAt s base .ebp a) (pb : PtrAt s base .ebx b) (pd : PtrAt s base .edi d)
    (ha : a+4*n≤size) (hb : b+4*n≤size) (hd : d+4*n≤size)
    (da : d≤a ∨ a+4*n≤d) (db : d≤b ∨ b+4*n≤d) (cf : s.cf=some cin) :
    WP isa (.block ((List.range n).flatMap fun j => VG.Impl.Rsa.X86.Chain.word op (4*j))) s fun t =>
      Outside base d (4*n) s.mem t.mem ∧ Keeps [.eax] s t ∧
      ∃ cout : Bool,t.cf=some cout ∧
        Rel op (val32 t.mem base d n) (val32 s.mem base a n)
          (val32 s.mem base b n) (2^(32*n)) cin.toNat cout.toNat := by
  have all : ∀ k,k≤n → WP isa
      (.block ((List.range k).flatMap fun j => VG.Impl.Rsa.X86.Chain.word op (4*j))) s fun t =>
      Outside base d (4*k) s.mem t.mem ∧ Keeps [.eax] s t ∧
      ∃ cout : Bool,t.cf=some cout ∧
        Rel op (val32 t.mem base d k) (val32 s.mem base a k)
          (val32 s.mem base b k) (2^(32*k)) cin.toNat cout.toNat := by
    intro k
    induction k with
    | zero =>
      intro _
      refine WP.block_nil ⟨Outside.refl _ _ _ _,Keeps.refl _ _,cin,cf,?_⟩
      simp only [Rel,val32,Nat.mul_zero,Nat.pow_zero,Nat.one_mul,Nat.zero_add]
      split <;> trivial
    | succ k ih =>
      intro hk
      simp only [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
      refine WP.block_append (WP.mono (ih (by omega_using [hk])) fun t ⟨O,K,c,C,V⟩ => ?_)
      have ht := hw.of_keeps K
      have pa' : PtrAt t base .ebp a := by rw [PtrAt,K.1 _ (by decide)];exact pa
      have pb' : PtrAt t base .ebx b := by rw [PtrAt,K.1 _ (by decide)];exact pb
      have pd' : PtrAt t base .edi d := by rw [PtrAt,K.1 _ (by decide)];exact pd
      refine WP.mono (word_ok ht hop pa' pb' pd' (by omega_using [ha, hk]) (by omega_using [hb, hk]) (by omega_using [hd, hk]) C) ?_
      rintro u ⟨O',K',c',C',V'⟩
      have aw : w32 t.mem base (a+4*k)=w32 s.mem base (a+4*k) :=
        O.w32 (by omega_using [da, hk]) (by have := hw.nowrap;omega_using [ha, hk, this])
      have bw : w32 t.mem base (b+4*k)=w32 s.mem base (b+4*k) :=
        O.w32 (by omega_using [db, hk]) (by have := hw.nowrap;omega_using [hb, hk, this])
      have preVal : val32 u.mem base d k=val32 t.mem base d k :=
        O'.val32 (by omega_using []) (by have := hw.nowrap;omega_using [hd, hk, this])
      rw [aw,bw] at V'
      refine ⟨(O.mono (Nat.le_refl _) (by omega_using [])).trans (O'.mono (by omega_using []) (by omega_using [])),
        K.trans K',c',C',?_⟩
      rw [val32_succ,val32_succ,val32_succ,preVal,pow32_succ]
      exact rel_step V V'
  exact all n (Nat.le_refl _)

end VG.Proof.Rsa.X86.Chain

end

end


/-! The fixed carry chain followed by public pointer and count updates. -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Chain
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86.PublicRt (wp_carry)

theorem chunk_ok {s : State} {base : Addr} {size a b d n k : Nat} {op : AluOp} {cin : Bool}
    (hw : Ws s base size) (hop : op=.adc ∨ op=.sbb)
    (pa : PtrAt s base .ebp a) (pb : PtrAt s base .ebx b) (pd : PtrAt s base .edi d)
    (ha : a+4*k≤size) (hb : b+4*k≤size) (hd : d+4*k≤size)
    (da : d≤a ∨ a+4*k≤d) (db : d≤b ∨ b+4*k≤d)
    (count : (s.gpr .edx).toNat=4*n) (kn : k≤n)
    (mask : s.gpr .ecx=cmask cin) :
    WP isa (.block (VG.Impl.Rsa.X86.Chain.chunk op k)) s fun t =>
      Outside base d (4*k) s.mem t.mem ∧ Keeps [.eax,.ebx,.ecx,.edx,.ebp,.edi] s t ∧
      PtrAt t base .ebp (a+4*k) ∧ PtrAt t base .ebx (b+4*k) ∧ PtrAt t base .edi (d+4*k) ∧
      (t.gpr .edx).toNat=4*(n-k) ∧ ∃ cout : Bool,t.gpr .ecx=cmask cout ∧
        Rel op (val32 t.mem base d k) (val32 s.mem base a k)
          (val32 s.mem base b k) (2^(32*k)) cin.toNat cout.toNat := by
  unfold VG.Impl.Rsa.X86.Chain.chunk
  simp only [List.cons_append,List.nil_append]
  refine wp_carry mask fun u U C => ?_
  have hu := hw.of_keeps U.keeps
  have pu (r : Reg) (h : r≠.ecx) : u.gpr r=s.gpr r := U.other r h
  have pa' : PtrAt u base .ebp a := by rw [PtrAt,pu _ (by decide)];exact pa
  have pb' : PtrAt u base .ebx b := by rw [PtrAt,pu _ (by decide)];exact pb
  have pd' : PtrAt u base .edi d := by rw [PtrAt,pu _ (by decide)];exact pd
  refine WP.block_append (WP.mono (words_ok hu hop pa' pb' pd' ha hb hd da db C) fun v ⟨O,K,c,Cv,V⟩ => ?_)
  refine wp_sbb_self Cv fun v₁ S => ?_
  refine wp_addS rfl fun v₂ A _ => wp_addS rfl fun v₃ B _ => wp_addS rfl fun v₄ D _ => ?_
  refine wp_subS rfl fun t E _ => WP.block_nil ?_
  have Kr : Keeps [.eax,.ecx] s v₁ := ((U.keeps.mono (by decide)).trans (K.mono (by decide))).trans (S.keeps.mono (by decide))
  have keep : Keeps [.eax,.ebx,.ecx,.edx,.ebp,.edi] s v₄ :=
    (((Kr.mono (by decide)).trans (A.keeps.mono (by decide))).trans (B.keeps.mono (by decide))).trans (D.keeps.mono (by decide))
  have mem : t.mem=v.mem := by rw [E.mem,D.mem,B.mem,A.mem,S.mem]
  have reg (r : Reg) (h : r≠.eax ∧ r≠.ecx) : v₁.gpr r=s.gpr r := Kr.1 r (by simpa using h)
  refine ⟨by rw [mem];simpa only [U.mem] using O,keep.trans (E.keeps.mono (by decide)),?_,?_,?_,?_,c,?_,?_⟩
  · rw [PtrAt,E.other _ (by decide),D.other _ (by decide),B.other _ (by decide),A.gpr,reg _ (by decide)]
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [count, kn] : 4*k<2^32)] using ptr_add pa (BitVec.ofNat 32 (4*k))
  · rw [PtrAt,E.other _ (by decide),D.other _ (by decide),B.gpr,A.other _ (by decide),reg _ (by decide)]
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [count, kn] : 4*k<2^32)] using ptr_add pb (BitVec.ofNat 32 (4*k))
  · rw [PtrAt,E.other _ (by decide),D.gpr,B.other _ (by decide),A.other _ (by decide),reg _ (by decide)]
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [count, kn] : 4*k<2^32)] using ptr_add pd (BitVec.ofNat 32 (4*k))
  · rw [E.gpr,D.other _ (by decide),B.other _ (by decide),A.other _ (by decide),reg _ (by decide),BitVec.toNat_sub,count,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [count, kn] : 4*k<2^32)]
    omega_using [count, kn]
  · rw [E.other _ (by decide),D.other _ (by decide),B.other _ (by decide),A.other _ (by decide),S.gpr]
  · rw [mem]
    simpa only [U.mem] using V

end VG.Proof.Rsa.X86.Chain

end

end


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
  have small : 4*n<2^32 := by have := (s.gpr .edx).isLt;omega_using [count]
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
      BitVec.eq_of_toNat_eq (by rw [J.count,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [count])])
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
        omega_using [hn, ha, hb, hd, da, db, count, small, hi, hk, ik, H, Hn]
      · intro done
        simp [done]
    by_cases done : i+k=n
    · exact .inl ⟨by simp only [eval,zero,done,decide_true,Option.map_some,Bool.not_true],done ▸ J'⟩
    · exact .inr ⟨by simp only [eval,zero,decide_eq_false done,Option.map_some,Bool.not_false],
        n-(i+k),by omega_using [hi, hk],i+k,rfl,by omega_using [ik, done],J'⟩
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
      omega_using [ge]
    exact WP.mono (inv_chunk hw hop ha hb hd da db small ik I') fun v J => finish (by decide) ik J
  · intro _
    have ik : i+1≤n := by omega_using [hi]
    exact WP.mono (inv_chunk hw hop ha hb hd da db small ik I') fun v J => finish (by decide) ik J

end VG.Proof.Rsa.X86.Chain

end

end


/-! Addition and subtraction interfaces matching the existing key-workspace loops. -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Chain
open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem addLoop_ok {s : State} {base : Addr} {size a b d n : Nat}
    (hw : Ws s base size) (hn : 0<n)
    (ha : a+4*n≤size) (hb : b+4*n≤size) (hd : d+4*n≤size)
    (da : d≤a ∨ a+4*n≤d) (db : d≤b ∨ b+4*n≤d)
    (pa : PtrAt s base .ebp a) (pb : PtrAt s base .ebx b) (pd : PtrAt s base .edi d)
    (count : (s.gpr .edx).toNat=4*n) (mask : s.gpr .ecx=cmask false) :
    WP isa (VG.Impl.Rsa.X86.Chain.loop .adc) s fun t =>
      Outside base d (4*n) s.mem t.mem ∧ PtrAt t base .ebp (a+4*n) ∧ PtrAt t base .edi (d+4*n) ∧
      (∃ c : Bool,t.gpr .ecx=cmask c ∧ val32 t.mem base d n+2^(32*n)*c.toNat=
        val32 s.mem base a n+val32 s.mem base b n) ∧
      Keeps [.eax,.ebx,.ecx,.edx,.ebp,.edi] s t := by
  refine WP.mono (loop_ok hw (.inl rfl) hn ha hb hd da db pa pb pd count mask) fun t I => ?_
  obtain ⟨c,C,V⟩ := I.value
  exact ⟨I.frame,I.pa,I.pd,⟨c,C,by simpa only [Rel,ite_true,Nat.add_zero] using V⟩,I.keep⟩

theorem subLoop_ok {s : State} {base : Addr} {size a b d n : Nat}
    (hw : Ws s base size) (hn : 0<n)
    (ha : a+4*n≤size) (hb : b+4*n≤size) (hd : d+4*n≤size)
    (da : d≤a ∨ a+4*n≤d) (db : d≤b ∨ b+4*n≤d)
    (pa : PtrAt s base .ebp a) (pb : PtrAt s base .ebx b) (pd : PtrAt s base .edi d)
    (count : (s.gpr .edx).toNat=4*n) (mask : s.gpr .ecx=cmask false) :
    WP isa (VG.Impl.Rsa.X86.Chain.loop .sbb) s fun t =>
      Outside base d (4*n) s.mem t.mem ∧ PtrAt t base .ebp (a+4*n) ∧
      (∃ c : Bool,t.gpr .ecx=cmask c ∧ val32 t.mem base d n+val32 s.mem base b n=
        val32 s.mem base a n+2^(32*n)*c.toNat) ∧
      Keeps [.eax,.ebx,.ecx,.edx,.ebp,.edi] s t := by
  refine WP.mono (loop_ok hw (.inr rfl) hn ha hb hd da db pa pb pd count mask) fun t I => ?_
  obtain ⟨c,C,V⟩ := I.value
  exact ⟨I.frame,I.pa,⟨c,C,by simpa [Rel] using V⟩,I.keep⟩

end VG.Proof.Rsa.X86.Chain
