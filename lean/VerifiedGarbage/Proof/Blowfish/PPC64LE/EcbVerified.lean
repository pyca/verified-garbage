module

public import VerifiedGarbage.Proof.Blowfish.PPC64LE.Ecb
public import VerifiedGarbage.Proof.Blowfish.Scratch
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Blowfish.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Blowfish.PPC64LE.Ecb
meta import VerifiedGarbage.Proof.Blowfish.Scratch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Blowfish.PPC64LE.Lit

/-! # Blowfish ECB on PPC64LE meets its contract, with the working space as an argument -/

@[expose] public section

namespace VG.Proof.Blowfish.PPC64LE

open VG VG.PPC64LE VG.Impl.Blowfish.PPC64LE VG.Spec.Blowfish VG.Proof.Blowfish

def dir (up : Bool) : Direction := if up then .encrypt else .decrypt

/-- The ECB contract as the code sees it. -/
def ecbC (up : Bool) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 4168⟩
    let data : Region := ⟨s.gpr .r4, 8 * (s.gpr .r5).toNat⟩
    let buf : Region := ⟨s.gpr .r6, 256⟩
    s.rd = [key] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧ data.Disjoint buf ∧
      (s.gpr .r4).toNat + 8 * (s.gpr .r5).toNat ≤ 2 ^ 64
  post s s' :=
    blocksAt s'.mem (s.gpr .r4) (s.gpr .r5).toNat =
      Spec.Blowfish.ecb (scheduleAt s.mem (s.gpr .r3)) (dir up) (blocksAt s.mem (s.gpr .r4) (s.gpr .r5).toNat)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

theorem ecb_blocks (K : Schedule) (up : Bool) (m m' : Mem) (D : Addr) (n : Nat)
    (h : ∀ b < n, blockAt m' (wAt D b) = blockOut K up (blockAt m (wAt D b))) :
    blocksAt m' D n = Spec.Blowfish.ecb K (dir up) (blocksAt m D n) := by
  simp only [blocksAt, Spec.Blowfish.ecb, List.map_map]
  apply List.map_congr_left
  intro b hb
  rw [Function.comp_apply, h b (List.mem_range.mp hb)]
  cases up <;> rfl

/-- The registers ECB writes. -/
def ecbRegs : List Reg := [.r0, .r4, .r5, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17]

theorem ecb_ok (up : Bool) (hw : writesOnly ecbRegs (Impl.Blowfish.PPC64LE.ecb up) = true)
    (hn : (Impl.Blowfish.PPC64LE.ecb up).noCalls = true)
    (hl : (instrs (Impl.Blowfish.PPC64LE.ecb up)).all (fun i => !i.writesLr) = true)
    (s : State) (hs : (ecbC up).pre s) :
    ∃ t s', Exec isa (Impl.Blowfish.PPC64LE.ecb up) s t s' ∧ abiPreserved s s' ∧ (ecbC up).post s s' := by
  obtain ⟨rd, wr, kd, kb, db, fit⟩ := hs
  obtain ⟨t, s', he, hp, hk⟩ := WP.keep ecbRegs (ecb_wp up ⟨rd, wr, kd, kb, db, fit⟩) hw hn
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.lr he hn hl⟩, ecb_blocks _ _ _ _ _ _ hp.done⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    first
    | exact hp.saved _ (by decide)
    | exact hk.gpr (by decide)

theorem ecb_agree (up : Bool) : ∀ s₁ s₂, (ecbC up).pre s₁ → (ecbC up).pre s₂ → (ecbC up).pub s₁ s₂ →
    taint.Agree (Taint.ofRegs [.r3, .r4, .r5, .r6]) s₁ s₂ := by
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1

theorem encrypt_ct : ConstantTime isa (ecbC true).pre (ecbC true).pub encrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) (ecb_agree true) (by taint_decide)

theorem decrypt_ct : ConstantTime isa (ecbC false).pre (ecbC false).pub decrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) (ecb_agree false) (by taint_decide)

def ecbSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r6 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 4168⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 256⟩]

theorem encrypt_verified : Verified target encrypt (Proof.Blowfish.ecbEncryptScratchContract abi 0) := by
  refine Verified.of_correct (k := ecbC true) (ecb_ok true (by lit_decide) (by lit_decide)
    (by rw [← Code.allInstrs_eq]; lit_decide)) encrypt_ct ?_
  sig_implies [Proof.Blowfish.ecbEncryptScratchContract, Proof.Blowfish.ecbScratchContract,
    Proof.Blowfish.ecbScratchSig, Spec.Blowfish.ecbPost, abi, argRegs, ecbC, dir]
    [ecbSat] using ecbSat

theorem decrypt_verified : Verified target decrypt (Proof.Blowfish.ecbDecryptScratchContract abi 0) := by
  refine Verified.of_correct (k := ecbC false) (ecb_ok false (by lit_decide) (by lit_decide)
    (by rw [← Code.allInstrs_eq]; lit_decide)) decrypt_ct ?_
  sig_implies [Proof.Blowfish.ecbDecryptScratchContract, Proof.Blowfish.ecbScratchContract,
    Proof.Blowfish.ecbScratchSig, Spec.Blowfish.ecbPost, abi, argRegs, ecbC, dir]
    [ecbSat] using ecbSat

end VG.Proof.Blowfish.PPC64LE
