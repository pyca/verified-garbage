module

public import VerifiedGarbage.Proof.Seed.X86_64.Ecb
public import VerifiedGarbage.Proof.Seed.X86_64.ConstantTime
public import VerifiedGarbage.Spec.Seed.Contract
public import VerifiedGarbage.Proof.Seed.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Seed.X86_64.Lit

/-! # The ECB functions meet their contracts, with the scratch buffer as an argument -/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64

/-- With `n` bytes of working space at `rcx` (1056 for ECB, 1088 for the blocks functions). -/
def contract (d : Spec.Seed.Direction) (n : Nat := 1056) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 128⟩
    let data : Region := ⟨s.gpr .rsi, 16 * (s.gpr .rdx).toNat⟩
    let buf : Region := ⟨s.gpr .rcx, n⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧ ret.Disjoint data ∧ ret.Disjoint buf ∧
      (s.gpr .rsi).toNat + 16 * (s.gpr .rdx).toNat ≤ 2 ^ 64
  post s s' :=
    Spec.Seed.blocksAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat =
      Spec.Seed.ecb (Spec.Seed.scheduleAt s.mem (s.gpr .rdi)) d
        (Spec.Seed.blocksAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
  pub := PublicRegs [.rdi, .rsi, .rdx, .rcx, .rsp]

theorem ecbPre_of {s : State} {d : Spec.Seed.Direction} {n : Nat} (hn : 1056 ≤ n) (hs : (contract d n).pre s) :
    EcbPre s := by
  obtain ⟨rd, wr, kd, kb, db, rdt, rb, fit⟩ := hs
  have sub : Region.Sub ⟨s.gpr .rcx, 8 * Impl.Seed.X86_64.scratchSlots⟩ ⟨s.gpr .rcx, n⟩ :=
    Region.sub_prefix (by unfold Impl.Seed.X86_64.scratchSlots; omega)
  exact { scratch := ⟨n, by unfold Impl.Seed.X86_64.scratchSlots; omega, by
            rw [wr]; exact List.mem_cons_of_mem _ List.mem_cons_self⟩
          dataIn := by rw [wr]; exact List.mem_cons_self
          keyIn := by rw [rd]; exact List.mem_cons_self
          keyData := kd
          keyBuf := kb.sub_right sub
          dataBuf := db.sub_right sub
          retData := rdt
          retBuf := rb.sub_right sub
          fit := by omega }

theorem ecbTaint_wf (d : Spec.Seed.Direction) {n : Nat} (hn : 1056 ≤ n) (hn' : n ≤ 2 ^ 64) (s : State)
    (hs : (contract d n).pre s) : Taint.Wf ecbTaint s := by
  obtain ⟨_, hwr, _, _, dataSep, _, _, fit⟩ := hs
  refine ⟨?_, ?_⟩
  · intro _
    rw [hwr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 0 ≤ 16 * (s.gpr .rdx).toNat; omega)
        (List.Forall₂.cons (by change 8 * Impl.Seed.X86_64.scratchSlots ≤ n; unfold Impl.Seed.X86_64.scratchSlots; omega)
          List.Forall₂.nil)
    · exact List.Pairwise.cons
        (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact dataSep)
        (List.Pairwise.cons (by simp) List.Pairwise.nil)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · change 16 * (s.gpr .rdx).toNat ≤ 2 ^ 64; omega
      · exact hn'
  · intro p hp
    simp only [ecbTaint, List.mem_singleton] at hp
    subst p
    unfold Taint.region
    rw [hwr]
    change s.gpr .rcx = s.gpr .rcx + (0 : BitVec 64)
    exact (BitVec.add_zero _).symm

theorem ecbTaint_agree (d : Spec.Seed.Direction) {n : Nat} (hn : 1056 ≤ n) (hn' : n ≤ 2 ^ 64) (s t : State)
    (hs : (contract d n).pre s) (ht : (contract d n).pre t)
    (hp : (contract d n).pub s t) : X86_64.Taint.Agree ecbTaint s t := by
  refine ⟨?_, ?_, ecbTaint_wf d hn hn' s hs, ecbTaint_wf d hn hn' t ht, ?_, ?_, ?_, X86_64.Taint.noXr⟩
  · constructor
    · intro r hr
      exact hp r (by simpa only [ecbTaint, RegSet.mem_ofList] using hr)
    · intro h
      change false = true at h
      contradiction
  · intro _
    rw [hs.2.1, ht.2.1, hp .rsi (by decide), hp .rdx (by decide), hp .rcx (by decide)]
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro r hr
    simp only [ecbTaint, RegSet.not_mem_empty] at hr

def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 1056⟩]

theorem ecb_correct (d : Spec.Seed.Direction) {n : Nat} (hn : 1056 ≤ n) (s : State) (hs : (contract d n).pre s) :
    ∃ t s', Exec isa (Impl.Seed.X86_64.ecb d) s t s' ∧ gprPreserved s s' ∧ (contract d n).post s s' := by
  obtain ⟨t, s', he, hp⟩ := ecb_ok d (ecbPre_of hn hs)
  exact ⟨t, s', he, hp.gpr, ecb_blocks _ _ _ _ _ _ hp.done⟩

theorem encrypt_correct {n : Nat} (hn : 1056 ≤ n) (s : State) (hs : (contract .encrypt n).pre s) :
    ∃ t s', Exec isa Impl.Seed.X86_64.encrypt s t s' ∧ abiPreserved s s' ∧
      (contract .encrypt n).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := ecb_correct .encrypt hn s hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := Impl.Seed.X86_64.encrypt) (by lit_decide) he hg, hp⟩

theorem decrypt_correct {n : Nat} (hn : 1056 ≤ n) (s : State) (hs : (contract .decrypt n).pre s) :
    ∃ t s', Exec isa Impl.Seed.X86_64.decrypt s t s' ∧ abiPreserved s s' ∧
      (contract .decrypt n).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := ecb_correct .decrypt hn s hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := Impl.Seed.X86_64.decrypt) (by lit_decide) he hg, hp⟩

theorem publicRegs_five (s₁ s₂ : State) : PublicRegs [.rdi, .rsi, .rdx, .rcx, .rsp] s₁ s₂ ↔
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp := by
  simp [PublicRegs]

/-- `satState` with the 1088 bytes of `vg_seed_*_blocks`'s working space. -/
def satStateBlocks : State := { satState with wr := [⟨0x2000, 0⟩, ⟨0x3000, 1088⟩] }

/-- ECB against `vg_seed_encrypt_blocks`'s contract: its working space is 136 words, of which
the code uses the first 132. -/
theorem encrypt_blocks_verified : Verified target Impl.Seed.X86_64.encrypt
    (Proof.Seed.blocksContract abi .encrypt) := by
  refine Verified.of_correct (encrypt_correct (n := 1088) (by decide))
    (encrypt_constantTime _ _ (ecbTaint_agree .encrypt (n := 1088) (by decide) (by decide))) ?_
  sig_implies [Proof.Seed.blocksContract, Proof.Seed.blocksSig, Spec.Seed.ecbPost, abi, argRegs,
    contract, publicRegs_five] [satStateBlocks] using satStateBlocks

theorem decrypt_blocks_verified : Verified target Impl.Seed.X86_64.decrypt
    (Proof.Seed.blocksContract abi .decrypt) := by
  refine Verified.of_correct (decrypt_correct (n := 1088) (by decide))
    (decrypt_constantTime _ _ (ecbTaint_agree .decrypt (n := 1088) (by decide) (by decide))) ?_
  sig_implies [Proof.Seed.blocksContract, Proof.Seed.blocksSig, Spec.Seed.ecbPost, abi, argRegs,
    contract, publicRegs_five] [satStateBlocks] using satStateBlocks

end VG.Proof.Seed.X86_64
