module

public import VerifiedGarbage.Proof.Cast5.Rounds
public import VerifiedGarbage.Impl.Cast5.AArch64.Tbl
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Cast5.Contract
public import VerifiedGarbage.Proof.Blowfish.AArch64.ConstantTime
public import VerifiedGarbage.Proof.Cast5.AArch64.TblEcb
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Cast5.AArch64.TblLit
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Cast5.AArch64.TblLit
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Impl.Cast5.AArch64.Tbl
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Cast5.Contract

/-!
# CAST5 ECB on AArch64, by batches of sixteen blocks: verified against the shared contracts

The pointers, the number of rounds and the count of blocks are public, and
so is everything the code computes from them (the batches, the round
counts, the addresses of the subkeys and of the table's planes): every
address and branch. The rotation amounts are multiplied in (`umull`), and
the S-box indices are only ever `tbl`/`tbx` operands.
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64.Tbl

open VG VG.AArch64 VG.Impl.Cast5.AArch64.Tbl
open VG.Proof.Blowfish.AArch64 (PublicRegs wAt savedRegs)

def dir (up : Bool) : Spec.Cast5.Direction := if up then .encrypt else .decrypt

/-- The ECB contract as the code sees it. -/
def ecbC (up : Bool) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 128⟩
    let data : Region := ⟨s.gpr .x2, 8 * (s.gpr .x3).toNat⟩
    let buf : Region := ⟨s.gpr .x4, 256⟩
    s.rd = [key] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧
      (s.gpr .x2).toNat + 8 * (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 16)
  post s s' :=
    Spec.Cast5.blocksAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
      Spec.Cast5.ecb (Spec.Cast5.scheduleAt s.mem (s.gpr .x0)) (s.gpr .x1).toNat (dir up)
        (Spec.Cast5.blocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub := PublicRegs [.x0, .x1, .x2, .x3, .x4]

theorem ecb_blocks (K : Spec.Cast5.Schedule) (N : Nat) (up : Bool) (m m' : Mem) (D : Addr) (n : Nat)
    (h : ∀ b < n, Spec.Cast5.blockAt m' (wAt D b) = blockOut K N up (Spec.Cast5.blockAt m (wAt D b))) :
    Spec.Cast5.blocksAt m' D n = Spec.Cast5.ecb K N (dir up) (Spec.Cast5.blocksAt m D n) := by
  simp only [Spec.Cast5.blocksAt, Spec.Cast5.ecb, List.map_map]
  apply List.map_congr_left
  intro b hb
  rw [Function.comp_apply, h b (List.mem_range.mp hb)]
  cases up <;> rfl

theorem ecbEncrypt_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.x0, .x1, .x2, .x3, .x4]) ecbEncrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem ecbDecrypt_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.x0, .x1, .x2, .x3, .x4]) ecbDecrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x3000 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 256⟩]

theorem publicRegs_five (s₁ s₂ : State) :
    PublicRegs [.x0, .x1, .x2, .x3, .x4] s₁ s₂ ↔
      s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
        s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 := by
  simp [PublicRegs]

theorem ecb_ok (up : Bool) (s : State) (hs : (ecbC up).pre s) :
    ∃ t s', Exec isa (ecb up) s t s' ∧ abiPreserved s s' ∧ (ecbC up).post s s' := by
  obtain ⟨hrd, hwr, keyData, keyBuf, dataBuf, fit, rounds⟩ := hs
  obtain ⟨t, s', he, ⟨hb, hv⟩, hg⟩ := WP.gprs (c := ecb up) (ecb_correct up ⟨hrd, hwr, keyData, keyBuf,
    dataBuf, fit, rounds⟩) (rs := preserved) (by cases up <;> lit_decide) (by cases up <;> rfl)
  refine ⟨t, s', he, ⟨hg, VG.AArch64.Exec.sp he, fun r hr => by rw [hv r hr]⟩,
    ecb_blocks _ _ _ _ _ _ _ hb⟩

theorem ecbEncrypt_verified :
    Verified AArch64.target ecbEncrypt (Proof.Cast5.ecbEncryptRoundsContract AArch64.abi) := by
  refine Verified.of_correct (k := ecbC true) (ecb_ok true) (ecbEncrypt_constantTime _) ?_
  sig_implies [Proof.Cast5.ecbEncryptRoundsContract, Proof.Cast5.ecbRoundsContract, Spec.Cast5.ecbSig,
    Spec.Cast5.ecbPre, Proof.Cast5.ecbRoundsPost, abi, argRegs, ecbC, dir, publicRegs_five]
    [satState] using satState

theorem ecbDecrypt_verified :
    Verified AArch64.target ecbDecrypt (Proof.Cast5.ecbDecryptRoundsContract AArch64.abi) := by
  refine Verified.of_correct (k := ecbC false) (ecb_ok false) (ecbDecrypt_constantTime _) ?_
  sig_implies [Proof.Cast5.ecbDecryptRoundsContract, Proof.Cast5.ecbRoundsContract, Spec.Cast5.ecbSig,
    Spec.Cast5.ecbPre, Proof.Cast5.ecbRoundsPost, abi, argRegs, ecbC, dir, publicRegs_five]
    [satState] using satState

end VG.Proof.Cast5.AArch64.Tbl
