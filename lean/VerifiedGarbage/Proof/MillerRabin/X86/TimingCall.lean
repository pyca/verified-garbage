module

public import VerifiedGarbage.Proof.MillerRabin.X86.TimingCallPre
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Call

/-! # Actual prepared Montgomery calls expose only their public geometry -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem MulReady.entry_eq {g : Geometry} {capacity b : Nat} {p : BitVec 32}
    {s : State} (S : MulReady g capacity b p s) :
    (pushed mulArgs s).callEntry.withRegions [below p 20] [⟨g.W, g.L⟩] = mulEntry g s := by
  unfold mulEntry
  rw [callEntry_argAddr0, S.sp]
  rfl

theorem mulCall_trace {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    {g : Geometry} (v : g.Valid) {capacity b : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (right : Proof.Rsa.Mont.Operand b) :
    RelCT isa (fun s t => MulReady g capacity b p s ∧ MulReady g capacity b p t)
      (.frame (.push mulArgs) (.call name code) (.pop .eax 5)) (fun _ _ => True) := by
  refine VG.X86.RelCT.callWith verified.1 verified.2.1 [below p 20] [⟨g.W, g.L⟩] ?_
  intro s t ⟨S, T⟩
  refine ⟨S.callPre v length right, T.callPre v length right, S.sp.trans T.sp.symm, ?_⟩
  rw [S.entry_eq, T.entry_eq]
  exact S.publicInputs v T

theorem pair_of_keeps {g : Geometry} {s t u z : State} (H : Pair g [.edi] s t)
    (Cu : Context g u) (Cz : Context g z) {rs : List Reg}
    (Ku : Keeps rs s u) (Kz : Keeps rs t z) (sp : .esp ∉ rs) (base : .edi ∉ rs) :
    Pair g [.edi] u z := by
  refine ⟨Cu, Cz, agree_regs ?_⟩
  intro r mem
  change r ∈ [.esp, .edi] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · rw [Ku.1 .esp sp, Kz.1 .esp sp]
    exact H.2.2.rf.1 .esp (by decide)
  · rw [Ku.1 .edi base, Kz.1 .edi base]
    exact round_regs H.2.2 (by decide)

end VG.Proof.MillerRabin.X86
