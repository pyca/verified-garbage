import VerifiedGarbage.Proof.Seed.X86_64.Key
import VerifiedGarbage.Proof.Seed.X86_64.Verified

/-! # Key expansion meets its contract, with the scratch buffer as an argument -/

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64

def keyContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 16⟩
    let sched : Region := ⟨s.gpr .rsi, 128⟩
    let buf : Region := ⟨s.gpr .rdx, 1056⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [sched, buf] ∧ key.Disjoint sched ∧ key.Disjoint buf ∧
      sched.Disjoint buf ∧ ret.Disjoint sched ∧ ret.Disjoint buf
  post s s' :=
    Spec.Seed.scheduleAt s'.mem (s.gpr .rsi) = Spec.Seed.expandKey (Spec.Seed.blockAt s.mem (s.gpr .rdi))
  pub := PublicRegs [.rdi, .rsi, .rdx, .rsp]

def keySatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 1056⟩]

theorem expandKey_correct (s : State) (hs : keyContract.pre s) :
    ∃ t s', Exec isa Impl.Seed.X86_64.expandKey s t s' ∧ abiPreserved s s' ∧ keyContract.post s s' := by
  obtain ⟨rd, wr, ks, kb, sb, rs, rb⟩ := hs
  obtain ⟨t, s', he, hp⟩ := expandKey_ok (s := s)
    { scratch := by rw [wr]; exact List.mem_cons_of_mem _ List.mem_cons_self
      schedIn := by rw [wr]; exact List.mem_cons_self
      keyIn := by rw [rd]; exact List.mem_cons_self
      keySched := ks
      keyBuf := kb
      schedBuf := sb
      retSched := rs
      retBuf := rb }
  exact ⟨t, s', he, abiPreserved_of_exec (c := Impl.Seed.X86_64.expandKey) (by lit_decide) he hp.gpr, hp.sched⟩

theorem publicRegs_four (s₁ s₂ : State) : PublicRegs [.rdi, .rsi, .rdx, .rsp] s₁ s₂ ↔
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rsp = s₂.gpr .rsp := by simp [PublicRegs]

theorem expandKey_verified : Verified target Impl.Seed.X86_64.expandKey
    (Proof.Seed.expandKeyScratchContract abi 132) := by
  refine Verified.of_correct expandKey_correct (expandKey_constantTime _) ?_
  sig_implies [Proof.Seed.expandKeyScratchContract, Proof.Seed.expandKeyScratchSig, Proof.Seed.expandKeyPost,
    abi, argRegs, keyContract, publicRegs_four] [keySatState] using keySatState

end VG.Proof.Seed.X86_64
