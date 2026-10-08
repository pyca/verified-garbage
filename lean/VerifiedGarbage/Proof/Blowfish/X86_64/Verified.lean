import VerifiedGarbage.Proof.Blowfish.X86_64.Ecb
import VerifiedGarbage.Proof.Blowfish.X86_64.ConstantTime
import VerifiedGarbage.Proof.Blowfish.Scratch
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Contract

/-! # The ECB functions meet their contracts, with the working space as an argument -/

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish VG.Proof.Blowfish

def dir (up : Bool) : Direction := if up then .encrypt else .decrypt

/-- The ECB contract as the code sees it. -/
def ecbC (up : Bool) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 4168⟩
    let data : Region := ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩
    let buf : Region := ⟨s.gpr .rcx, 256⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧ ret.Disjoint data ∧ ret.Disjoint buf ∧
      (s.gpr .rsi).toNat + 8 * (s.gpr .rdx).toNat ≤ 2 ^ 64
  post s s' :=
    blocksAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat =
      ecb (scheduleAt s.mem (s.gpr .rdi)) (dir up) (blocksAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
  pub := PublicRegs [.rdi, .rsi, .rdx, .rcx, .rsp]

theorem ecb_blocks (K : Schedule) (up : Bool) (m m' : Mem) (D : Addr) (n : Nat)
    (h : ∀ b < n, blockAt m' (wAt D b) = blockOut K up (blockAt m (wAt D b))) :
    blocksAt m' D n = ecb K (dir up) (blocksAt m D n) := by
  simp only [blocksAt, Spec.Blowfish.ecb, List.map_map]
  apply List.map_congr_left
  intro b hb
  rw [Function.comp_apply, h b (List.mem_range.mp hb)]
  cases up <;> rfl

def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 4168⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 256⟩]

theorem ecb_ok (up : Bool) (s : State) (hs : (ecbC up).pre s) :
    ∃ t s', Exec isa (Impl.Blowfish.X86_64.ecb up) s t s' ∧ abiPreserved s s' ∧ (ecbC up).post s s' := by
  obtain ⟨rd, wr, kd, kb, db, rdt, rb, fit⟩ := hs
  obtain ⟨t, s', he, hp⟩ := ecb_correct up ⟨rd, wr, kd, kb, db, rdt, rb, fit⟩
  refine ⟨t, s', he, abiPreserved_of_exec (by cases up <;> lit_decide) he ⟨fun r hr => ?_, ?_⟩,
    ecb_blocks _ _ _ _ _ _ hp.done⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hp.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · refine hp.frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact rdt
    · exact rb

theorem encrypt_verified : Verified target encrypt (Proof.Blowfish.ecbEncryptScratchContract abi 0) := by
  refine Verified.of_correct (k := ecbC true) (ecb_ok true) (encrypt_constantTime _) ?_
  sig_implies [Proof.Blowfish.ecbEncryptScratchContract, Proof.Blowfish.ecbScratchContract,
    Proof.Blowfish.ecbScratchSig, Spec.Blowfish.ecbPost, abi, argRegs, ecbC, dir, publicRegs_five]
    [satState] using satState

theorem decrypt_verified : Verified target decrypt (Proof.Blowfish.ecbDecryptScratchContract abi 0) := by
  refine Verified.of_correct (k := ecbC false) (ecb_ok false) (decrypt_constantTime _) ?_
  sig_implies [Proof.Blowfish.ecbDecryptScratchContract, Proof.Blowfish.ecbScratchContract,
    Proof.Blowfish.ecbScratchSig, Spec.Blowfish.ecbPost, abi, argRegs, ecbC, dir, publicRegs_five]
    [satState] using satState

end VG.Proof.Blowfish.X86_64
