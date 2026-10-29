module

public import VerifiedGarbage.Proof.Rsa.X86.Chain.Word
import VerifiedGarbage.Proof.Framework.Omega
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
      refine WP.block_append (WP.mono (ih (by omega)) fun t ⟨O,K,c,C,V⟩ => ?_)
      have ht := hw.of_keeps K
      have pa' : PtrAt t base .ebp a := by rw [PtrAt,K.1 _ (by decide)];exact pa
      have pb' : PtrAt t base .ebx b := by rw [PtrAt,K.1 _ (by decide)];exact pb
      have pd' : PtrAt t base .edi d := by rw [PtrAt,K.1 _ (by decide)];exact pd
      refine WP.mono (word_ok ht hop pa' pb' pd' (by omega) (by omega) (by omega) C) ?_
      rintro u ⟨O',K',c',C',V'⟩
      have aw : w32 t.mem base (a+4*k)=w32 s.mem base (a+4*k) :=
        O.w32 (by omega) (by have := hw.nowrap;omega)
      have bw : w32 t.mem base (b+4*k)=w32 s.mem base (b+4*k) :=
        O.w32 (by omega) (by have := hw.nowrap;omega)
      have preVal : val32 u.mem base d k=val32 t.mem base d k :=
        O'.val32 (by omega) (by have := hw.nowrap;omega)
      rw [aw,bw] at V'
      refine ⟨(O.mono (Nat.le_refl _) (by omega)).trans (O'.mono (by omega) (by omega)),
        K.trans K',c',C',?_⟩
      rw [val32_succ,val32_succ,val32_succ,preVal,pow32_succ]
      exact rel_step V V'
  exact all n (Nat.le_refl _)

end VG.Proof.Rsa.X86.Chain
