module

import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicCoreTiming
import VerifiedGarbage.Proof.Dsa.X86.Comb.PrivateBodyTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
public import VerifiedGarbage.Proof.Dsa.X86.PowEntry
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.TCB.X86.Target

/-! Public preparation uses the shared calling boundary and proven public core. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

structure PublicBodyInput (n e m g x : Nat) (base : Addr) (s : State) : Prop where
  entry : Pow.Entry s base (layout n e).size
  modulus : wordsVal s.mem base (slot n 0) n=m
  generator : wordsVal s.mem base (slot n 5) n=g
  exponent : val32 s.mem base (slot n 8) e=x

theorem publicBody_relCT {n e : Nat} (h : Supported n e) (base : Addr) (m g x : Nat)
    (hm : 1<m) (odd : m%2=1) :
    RelCT isa (fun s t => PublicBodyInput n e m g x base s ∧ PublicBodyInput n e m g x base t ∧
      s.gpr .esp=t.gpr .esp ∧ arg s 0=arg t 0 ∧
      readSrc s (.mem (VG.Impl.Mont.X86.at_ .esp 4))=some (arg s 0) ∧
      readSrc t (.mem (VG.Impl.Mont.X86.at_ .esp 4))=some (arg t 0))
      (body true n e) (fun _ _ => True) := by
  have hz : 24≤(layout n e).size := by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  unfold body
  refine RelCT.seq (R := fun s t => PublicCoreInput n e m g x base s ∧ PublicCoreInput n e m g x base t) ?_
    (RelCT.seq (publicCore_relCT h base m g x hm odd)
      ((checkedProgramChange (σ := { regs := .ofList [], flags := false }) (hint := .block []) rfl rfl).mono
        (fun _ _ h => h) (fun _ _ _ => trivial)))
  intro s t tr ur sf tf ⟨S,T,A⟩ Es Et
  have step {u v : State} (U : PublicBodyInput n e m g x base u) {trace}
      (E : Exec isa (.block VG.Impl.Dsa.X86.Pow.save) u trace v) : PublicCoreInput n e m g x base v := by
    obtain ⟨C,_,O,_⟩ := wp_result (Pow.save_ok U.entry hz) E
    have bounds : 24≤slot n 0 ∧ slot n 0+8*n≤2^64 ∧ 24≤slot n 5 ∧ slot n 5+8*n≤2^64 ∧
        24≤slot n 8 ∧ slot n 8+4*e≤2^64 := by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
    refine ⟨⟨C,?_⟩,?_,?_⟩
    · exact (O.wordsVal (.inr bounds.1) bounds.2.1).trans U.modulus
    · exact (O.wordsVal (.inr bounds.2.2.1) bounds.2.2.2.1).trans U.generator
    · exact (O.val32 (by have := bounds.2.2.2.2.1; omega) bounds.2.2.2.2.2).trans U.exponent
  exact ⟨(save_relCT _ _ _ _ _ _ A Es Et).1,step S Es,step T Et⟩

end VG.Proof.Dsa.X86.Comb
