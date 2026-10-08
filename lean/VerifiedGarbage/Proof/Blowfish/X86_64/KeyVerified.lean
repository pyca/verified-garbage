import VerifiedGarbage.Proof.Blowfish.X86_64.KeyMain
import VerifiedGarbage.Proof.Blowfish.X86_64.ConstantTime
import VerifiedGarbage.Proof.Blowfish.Scratch
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Contract

/-! # Key expansion meets its contract, with the working space as an argument -/

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish VG.Proof.Blowfish

/-- The key expansion contract as the code sees it. -/
def keyC : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let sch : Region := ⟨s.gpr .rdx, 4168⟩
    let buf : Region := ⟨s.gpr .rcx, 32⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [sch, buf] ∧ key.Disjoint sch ∧ key.Disjoint buf ∧ sch.Disjoint buf ∧
      ret.Disjoint sch ∧ ret.Disjoint buf ∧ validKey (s.gpr .rsi).toNat ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 4168 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 32 ≤ 2 ^ 64
  post s s' := scheduleAt s'.mem (s.gpr .rdx) = expandKey (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub := PublicRegs [.rdi, .rsi, .rdx, .rcx, .rsp]

def keySatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 4168⟩, ⟨0x4000, 32⟩]

theorem expandKey_ok (s : State) (hs : keyC.pre s) :
    ∃ t s', Exec isa Impl.Blowfish.X86_64.expandKey s t s' ∧ abiPreserved s s' ∧ keyC.post s s' := by
  obtain ⟨rd, wr, kS, -, SB, rS, rB, valid, fK, fS, fB⟩ := hs
  obtain ⟨t, s', he, hp⟩ := expandKey_correct ⟨valid, rd, wr, kS, SB, fK, fS, fB⟩
  refine ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he ⟨fun r hr => ?_, ?_⟩, hp.sched⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hp.gpr _ (by decide)
  · refine hp.frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact rS
    · exact rB

theorem expandKey_verified :
    Verified target Impl.Blowfish.X86_64.expandKey (Proof.Blowfish.expandKeyScratchContract abi) := by
  refine Verified.of_correct (k := keyC) expandKey_ok (expandKey_constantTime _) ?_
  sig_implies [Proof.Blowfish.expandKeyScratchContract, Proof.Blowfish.expandKeyScratchSig, Spec.Blowfish.expandKeyPre,
    Spec.Blowfish.expandKeyPost, Spec.Blowfish.validKey, abi, argRegs, keyC, publicRegs_five] [keySatState]
    using keySatState

end VG.Proof.Blowfish.X86_64
