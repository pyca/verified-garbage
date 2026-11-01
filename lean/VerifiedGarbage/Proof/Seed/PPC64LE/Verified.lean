module

public import VerifiedGarbage.Proof.Seed.PPC64LE.Ecb
public import VerifiedGarbage.Proof.Seed.Scratch
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Spec.Seed.Contract
public import VerifiedGarbage.Proof.Seed.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Seed.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Seed.PPC64LE.Ecb
meta import VerifiedGarbage.Proof.Seed.Scratch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Spec.Seed.Contract
meta import VerifiedGarbage.Proof.Seed.Contract
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Seed.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Spec.Seed
public import VerifiedGarbage.TCB.Artifact

/-!
# The ECB functions meet their contracts, with the scratch buffer as an argument

`encrypt_blocks_verified` and `decrypt_blocks_verified`: `ecb d` is correct
(`ecb_ok`) and constant time, by the taint analysis with the pointers, `n`
and the stack pointer public, against `vg_seed_{en,de}crypt_blocks`'s
contract, whose working space has 136 words (the code uses 130).
`ecb_correct'` adds what the modes' core needs of the call beyond the
contract (`EcbPost`).
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE

/-- ECB with `n` bytes of working space at `r6` (1040, the 130 words the code
uses, or 1088 for the blocks functions). -/
def contract (d : Spec.Seed.Direction) (n : Nat := 8 * Impl.Seed.PPC64LE.scratchSlots) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 128⟩
    let data : Region := ⟨s.gpr .r4, 16 * (s.gpr .r5).toNat⟩
    let buf : Region := ⟨s.gpr .r6, n⟩
    s.rd = [key] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧ (s.gpr .r4).toNat + 16 * (s.gpr .r5).toNat ≤ 2 ^ 64
  post s s' :=
    Spec.Seed.blocksAt s'.mem (s.gpr .r4) (s.gpr .r5).toNat =
      Spec.Seed.ecb (Spec.Seed.scheduleAt s.mem (s.gpr .r3)) d
        (Spec.Seed.blocksAt s.mem (s.gpr .r4) (s.gpr .r5).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6

theorem ecbPre_of {s : State} {d : Spec.Seed.Direction} {n : Nat} (hn : 8 * Impl.Seed.PPC64LE.scratchSlots ≤ n)
    (hs : (contract d n).pre s) : EcbPre s := by
  obtain ⟨rd, wr, kd, kb, db, fit⟩ := hs
  have sub : Region.Sub ⟨s.gpr .r6, 8 * Impl.Seed.PPC64LE.scratchSlots⟩ ⟨s.gpr .r6, n⟩ :=
    Region.sub_prefix hn
  exact { scratch := ⟨n, hn, by rw [wr]; exact List.mem_cons_of_mem _ List.mem_cons_self⟩
          dataIn := by rw [wr]; exact List.mem_cons_self
          keyIn := by rw [rd]; exact List.mem_cons_self
          keyData := kd
          keyBuf := kb.sub_right sub
          dataBuf := db.sub_right sub
          fit := by omega }

/-- The registers ECB writes. -/
def ecbWrites : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20,
   .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

/-- The callee-saved registers, from those the code saves and `r2`, which it never writes. -/
theorem abi_of {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (hs : ∀ p ∈ Impl.Seed.PPC64LE.savedRegs, s'.gpr p.1 = s.gpr p.1) (h2 : s'.gpr .r2 = s.gpr .r2)
    (hlr : s'.lr = s.lr) : abiPreserved s s' := by
  refine ⟨fun r hr => ?_, Exec.sp he, hlr⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact h2
  · exact hs (.r14, 112) (by decide)
  · exact hs (.r15, 113) (by decide)
  · exact hs (.r16, 114) (by decide)
  · exact hs (.r17, 115) (by decide)
  · exact hs (.r18, 116) (by decide)
  · exact hs (.r19, 117) (by decide)
  · exact hs (.r20, 118) (by decide)
  · exact hs (.r21, 119) (by decide)
  · exact hs (.r22, 120) (by decide)
  · exact hs (.r23, 121) (by decide)
  · exact hs (.r24, 122) (by decide)
  · exact hs (.r25, 123) (by decide)
  · exact hs (.r26, 124) (by decide)
  · exact hs (.r27, 125) (by decide)
  · exact hs (.r28, 126) (by decide)
  · exact hs (.r29, 127) (by decide)
  · exact hs (.r30, 128) (by decide)
  · exact hs (.r31, 129) (by decide)

/-- ECB, with what its proof (`ecb_ok`) gives beyond the contract. -/
theorem ecb_correct' (d : Spec.Seed.Direction) {n : Nat} (hn : 8 * Impl.Seed.PPC64LE.scratchSlots ≤ n)
    (s : State) (hs : (contract d n).pre s) :
    ∃ t s', Exec isa (Impl.Seed.PPC64LE.ecb d) s t s' ∧ abiPreserved s s' ∧ (contract d n).post s s' ∧
      EcbPost d s s' := by
  have hc : (Impl.Seed.PPC64LE.ecb d).noCalls = true := by cases d <;> lit_decide
  obtain ⟨t, s', he, hp, hk⟩ := WP.keep ecbWrites (ecb_ok d (ecbPre_of hn hs)) (by cases d <;> lit_decide) hc
  exact ⟨t, s', he, abi_of he hp.saved (hk.gpr (by decide)) (Exec.lr he hc (by cases d <;> lit_decide)),
    ecb_blocks _ _ _ _ _ _ hp.done, hp⟩

theorem ecb_correct (d : Spec.Seed.Direction) {n : Nat} (hn : 8 * Impl.Seed.PPC64LE.scratchSlots ≤ n)
    (s : State) (hs : (contract d n).pre s) :
    ∃ t s', Exec isa (Impl.Seed.PPC64LE.ecb d) s t s' ∧ abiPreserved s s' ∧ (contract d n).post s s' := by
  obtain ⟨t, s', he, ha, hp, -⟩ := ecb_correct' d hn s hs
  exact ⟨t, s', he, ha, hp⟩

theorem ecb_ct (d : Spec.Seed.Direction) (n : Nat) :
    ConstantTime isa (contract d n).pre (contract d n).pub (Impl.Seed.PPC64LE.ecb d) := by
  have hag : ∀ s₁ s₂, (contract d n).pre s₁ → (contract d n).pre s₂ → (contract d n).pub s₁ s₂ →
      taint.Agree (Taint.ofRegs [.r3, .r4, .r5, .r6]) s₁ s₂ := by
    intro s₁ s₂ _ _ hp
    obtain ⟨hsp, h3, h4, h5, h6⟩ := hp
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  cases d
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) hag (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) hag (by taint_decide)

def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 1088⟩]

/-- ECB against `vg_seed_encrypt_blocks`'s contract: its working space is 136
words, of which the code uses the first 130. -/
theorem encrypt_blocks_verified : Verified target Impl.Seed.PPC64LE.encrypt
    (Proof.Seed.blocksContract abi .encrypt) := by
  refine Verified.of_correct (ecb_correct .encrypt (n := 1088) (by decide)) (ecb_ct .encrypt 1088) ?_
  sig_implies [Proof.Seed.blocksContract, Proof.Seed.blocksSig, Spec.Seed.ecbPost, abi, argRegs,
    contract] [satState] using satState

theorem decrypt_blocks_verified : Verified target Impl.Seed.PPC64LE.decrypt
    (Proof.Seed.blocksContract abi .decrypt) := by
  refine Verified.of_correct (ecb_correct .decrypt (n := 1088) (by decide)) (ecb_ct .decrypt 1088) ?_
  sig_implies [Proof.Seed.blocksContract, Proof.Seed.blocksSig, Spec.Seed.ecbPost, abi, argRegs,
    contract] [satState] using satState

end VG.Proof.Seed.PPC64LE
