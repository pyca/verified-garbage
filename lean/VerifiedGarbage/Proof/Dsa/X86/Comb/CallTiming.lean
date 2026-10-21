module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
public import VerifiedGarbage.Proof.Dsa.X86.WorkspaceCallTiming
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicVerified
import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicBodyTiming
import VerifiedGarbage.Proof.Dsa.X86.Comb.PrivateBodyTiming
import VerifiedGarbage.Proof.Dsa.X86.Comb.BodyWide
import VerifiedGarbage.Proof.Dsa.X86.PowCallFrame

/-! The public and secret exponent calls share a proved relational calling boundary. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem entry_readArg {s : State} {base : Addr} {size : Nat} (E : Pow.Entry s base size) :
    readSrc s (.mem (VG.Impl.Mont.X86.at_ .esp 4))=some (arg s 0) := by
  change s.load32 (argAddr s 0)=some (arg s 0)
  unfold State.load32
  rw [ite_eq_left E.arg]
  rfl

theorem entry_arg_eq {s t : State} {base : Addr} {size : Nat}
    (E : Pow.Entry s base size) (F : Pow.Entry t base size) : arg s 0=arg t 0 := by
  have H := congrArg (fun x : BitVec 64 => x.setWidth 32) (E.base_eq.trans F.base_eq.symm)
  simpa only [BitVec.setWidth_setWidth_of_le _ (by decide : 32≤64),BitVec.setWidth_eq] using H

def PublicValues (n e m g x : Nat) (base : Addr) (mem : Mem) : Prop :=
  wordsVal mem base (slot n 0) n=m ∧ wordsVal mem base (slot n 5) n=g ∧ val32 mem base (slot n 8) e=x

theorem publicBodyWide_relCT {n e size : Nat} (h : Supported n e) (base : Addr) (m g x : Nat)
    (fits : (layout n e).size≤size) (hm : 1<m) (odd : m%2=1) :
    RelCT isa (fun s t => Pow.Entry s base size ∧ Pow.Entry t base size ∧ s.gpr .esp=t.gpr .esp ∧
      PublicValues n e m g x base s.mem ∧ PublicValues n e m g x base t.mem)
      (body true n e) (fun _ _ => True) := by
  intro s t tr ur sf tf ⟨S,T,SP,A,B⟩ E F
  obtain ⟨u,Eu⟩ := publicNarrowRun h S fits A.1 hm odd E
  obtain ⟨v,Ev⟩ := publicNarrowRun h T fits B.1 hm odd F
  have Sn := (narrowResources S fits).1
  have Tn := (narrowResources T fits).1
  exact publicBody_relCT h base m g x hm odd _ _ _ _ _ _
    ⟨⟨Sn,A.1,A.2.1,A.2.2⟩,⟨Tn,B.1,B.2.1,B.2.2⟩,SP,entry_arg_eq Sn Tn,
      entry_readArg Sn,entry_readArg Tn⟩ Eu Ev

theorem privateCall_relCT {n e : Nat} (h : Supported n e) (base : Addr) (size : Nat) :
    RelCT isa (WorkspacePair base size (fun _ _ => True)) (call false n e) (fun _ _ => True) := by
  apply workspaceCall_relCT (fun _ _ _ => trivial)
  intro s t tr ur sf tf ⟨S,T,SP,_⟩ E F
  exact private_body_relCT h _ _ _ _ _ _ ⟨SP,entry_arg_eq S T,entry_readArg S,entry_readArg T⟩ E F

theorem publicCall_relCT {n e : Nat} (h : Supported n e) (base : Addr) (size m g x : Nat)
    (fits : (layout n e).size≤size) (hm : 1<m) (odd : m%2=1) :
    RelCT isa (WorkspacePair base size (fun a b => PublicValues n e m g x base a ∧ PublicValues n e m g x base b))
      (call true n e) (fun _ _ => True) := by
  apply workspaceCall_relCT (timing := publicBodyWide_relCT h base m g x fits hm odd)
  intro s t a b ⟨S,T,RS,RT,_,A,B⟩ Fa Fb
  have keep {s : State} {mem : Mem} (S : Scr s base size) (R : Pow.Room (s.gpr .esp) base size)
      (V : PublicValues n e m g x base s.mem) (F : Frame [below (s.gpr .esp) 12] s.mem mem) :
      PublicValues n e m g x base mem := by
    have bounds : slot n 0+8*n≤(layout n e).size ∧ slot n 5+8*n≤(layout n e).size ∧
        slot n 8+4*e≤(layout n e).size := by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
    have vals := fun d k hd => Pow.frame_val32 R S.nowrap F (d := d) (k := k) hd
    refine ⟨?_,?_,(vals _ _ (by omega)).trans V.2.2⟩
    · rw [wordsVal_eq_val32,vals _ _ (by omega),←wordsVal_eq_val32]; exact V.1
    · rw [wordsVal_eq_val32,vals _ _ (by omega),←wordsVal_eq_val32]; exact V.2.1
  exact ⟨keep S RS A Fa,keep T RT B Fb⟩

end VG.Proof.Dsa.X86.Comb
