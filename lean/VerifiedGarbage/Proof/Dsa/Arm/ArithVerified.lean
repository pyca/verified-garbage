module

public import VerifiedGarbage.Proof.Dsa.Arm.Arith
public import VerifiedGarbage.Proof.Dsa.Arm.PowVerified
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Dsa.ModPowContract
meta import VerifiedGarbage.Proof.Dsa.ModArithContract
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.ModPowContract
public import VerifiedGarbage.Proof.Dsa.ModArithContract

/-!
# DSA's reductions and products as functions on 32-bit ARM: `Verified`

`vg_dsa_mulmod_{n}` and `vg_dsa_reduce_{n}` against their contracts
(`Proof/Dsa/ModArithContract.lean`), from `mulK` and `reduceK`, as `PowVerified.lean`
does for `vg_dsa_pow_{n}_{e}`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Pow

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm.Pow VG.Impl.Dsa.Arm.Arith
open VG.Proof.Dsa.ModPow (numAt Keeps)

/-! ## Products -/

/-- `vg_dsa_mulmod_{n}`'s contract on ARM, as the shared contract states it. -/
def mulArm (n : Nat) : Contract isa where
  pre := (powArm n 1).pre
  post s t :=
    let ws := State.addr (s.gpr .r0)
    numAt t.mem ws (resS n) (8 * n) =
        numAt s.mem ws (baseS n) (8 * n) * numAt s.mem ws (expS n) (8 * n) % numAt s.mem ws (modS n) (8 * n) ∧
      Keeps ws (s.gpr .r1).toNat (scratch n) s.mem t.mem
  pub := (powArm n 1).pub

theorem keeps_of_outs {s t : State} {rs : List (Nat × Nat)} (hnw : (s.gpr .r0).toNat + (s.gpr .r1).toNat * 8 ≤ 2 ^ 32)
    (O : Outs (State.addr (s.gpr .r0)) rs s.mem t.mem) :
    Keeps (State.addr (s.gpr .r0)) (s.gpr .r1).toNat rs s.mem t.mem := fun i hi hj =>
  O _ fun r hr => by
    rw [show ofs (State.addr (s.gpr .r0)) (State.addr (s.gpr .r0) + BitVec.ofNat 64 i) = i by
      simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by omega)]]
    exact hj r hr

theorem mulArm_correct {n : Nat} (hn : 0 < n) (hn48 : n ≤ 48) (s : State) (h : (mulArm n).pre s) :
    ∃ tr t, Exec isa (mulBody n) s tr t ∧ abiPreserved s t ∧ (mulArm n).post s t := by
  obtain ⟨tr, t, ex, abi, V, O⟩ := mulK_correct hn hn48 s (powArm_pre (e := 1) h)
  exact ⟨tr, t, ex, abi, by simp only [numAt_eq8]; exact V, keeps_of_outs h.2.2.1 O⟩

theorem mulArm_ct (n : Nat) (hn : 0 < n) (hn48 : n ≤ 48) : ConstantTime isa (mulArm n).pre (mulArm n).pub (mulBody n) :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => mulK_ct n hn hn48 _ _ _ _ _ _ (powArm_pre (e := 1) h₁) (powArm_pre (e := 1) h₂) hp.2.1 e₁ e₂

theorem mulArm_implies {n : Nat} (hn : 0 < n) (hn48 : n ≤ 48) :
    (mulArm n).Implies (Proof.Dsa.ModArith.mulContract (mulLayout n) Arm.abi) where
  pre := by
    sig_implies_pre [Proof.Dsa.ModArith.mulContract, Proof.Dsa.ModPow.sig, mulArm, powArm, mulLayout, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  post := by
    sig_implies_post [Proof.Dsa.ModArith.mulContract, Proof.Dsa.ModPow.sig, mulArm, powArm, mulLayout, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  pub := by
    sig_implies_pub [Proof.Dsa.ModArith.mulContract, Proof.Dsa.ModPow.sig, mulArm, powArm, mulLayout, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  sat := by
    refine ⟨satState, ?_⟩
    sig_pre [Proof.Dsa.ModArith.mulContract, Proof.Dsa.ModPow.sig, mulLayout, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    sig_and_intros
    · decide
    · decide
    · decide
    · rw [show BitVec.toNat (620 : BitVec 32) = 620 from rfl]
      simp only [contextBytes, slot, stride]; omega
    all_goals
      obtain ⟨k, hk⟩ : ∃ k, 8 * n = k + 2 := ⟨8 * n - 2, by omega⟩
      unfold numAt
      rw [hk]
    · exact (read_ones _ k).1
    · exact Nat.lt_of_lt_of_le (by decide) (read_ones _ k).2

theorem mulVerified (n : Nat) (hn : 0 < n := by decide) (hn48 : n ≤ 48 := by decide) :
    Verified Arm.target (mulBody n) (Proof.Dsa.ModArith.mulContract (mulLayout n) Arm.abi) :=
  Verified.of_correct (mulArm_correct hn hn48) (mulArm_ct n hn hn48) (mulArm_implies hn hn48)

/-! ## Reductions -/

/-- `vg_dsa_reduce_{n}`'s contract on ARM, as the shared contract states it. -/
def reduceArm (n : Nat) : Contract isa where
  pre s :=
    let ws := State.addr (s.gpr .r0)
    let M := numAt s.mem ws (modS n) (8 * n)
    s.rd = [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩] ∧ s.wr = [⟨ws, (s.gpr .r1).toNat * 8⟩] ∧
      Region.Disjoint ⟨ws, (s.gpr .r1).toNat * 8⟩ ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat * 8 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
      contextBytes n ≤ 8 * (s.gpr .r1).toNat ∧ M % 2 = 1 ∧ 255 < M
  post s t :=
    let ws := State.addr (s.gpr .r0)
    numAt t.mem ws (resS n) (8 * n) =
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) %
          numAt s.mem ws (modS n) (8 * n) ∧
      Keeps ws (s.gpr .r1).toNat (scratch n) s.mem t.mem
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2 ∧
    s.gpr .r3 = t.gpr .r3

theorem reduceArm_pre {n : Nat} {s : State} (h : (reduceArm n).pre s) : (reduceK n).pre s := by
  obtain ⟨hrd, hwr, hd, hnw, hfit, hz, hodd, hm⟩ := h
  simp only [numAt_eq8] at hodd hm
  exact ⟨hrd, hwr, hnw, hfit, by omega, hd, hodd, hm⟩

theorem reduceArm_correct {n : Nat} (hn : 0 < n) (hn48 : n ≤ 48) (s : State) (h : (reduceArm n).pre s) :
    ∃ tr t, Exec isa (reduceBody n) s tr t ∧ abiPreserved s t ∧ (reduceArm n).post s t := by
  obtain ⟨tr, t, ex, abi, V, O⟩ := reduceK_correct hn hn48 s (reduceArm_pre h)
  exact ⟨tr, t, ex, abi, by simp only [numAt_eq8]; exact V, keeps_of_outs h.2.2.2.1 O⟩

theorem reduceArm_ct {n : Nat} (hn : 0 < n) (hn48 : n ≤ 48) :
    ConstantTime isa (reduceArm n).pre (reduceArm n).pub (reduceBody n) :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => reduceK_ct n hn hn48 _ _ _ _ _ _ (reduceArm_pre h₁) (reduceArm_pre h₂)
    ⟨hp.2.1, hp.2.2.2.1, hp.2.2.2.2⟩ e₁ e₂

/-- A state satisfying the reduction's contract: `satState`'s working space,
and no bytes. -/
def satReduce : State := { satState with
  gpr := fun r => match r with | .r0 => 0x1000 | .r1 => 620 | .r2 => 0x3000 | _ => 0
  rd := [⟨0x3000, 0⟩] }

theorem reduceArm_implies {n : Nat} (hn : 0 < n) (hn48 : n ≤ 48) :
    (reduceArm n).Implies (Proof.Dsa.ModArith.reduceContract (reduceLayout n) Arm.abi) where
  pre := by
    sig_implies_pre [Proof.Dsa.ModArith.reduceContract, Proof.Dsa.ModArith.reduceSig, reduceArm, reduceLayout,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  post := by
    sig_implies_post [Proof.Dsa.ModArith.reduceContract, Proof.Dsa.ModArith.reduceSig, reduceArm, reduceLayout,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  pub := by
    sig_implies_pub [Proof.Dsa.ModArith.reduceContract, Proof.Dsa.ModArith.reduceSig, reduceArm, reduceLayout,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  sat := by
    refine ⟨satReduce, ?_⟩
    sig_pre [Proof.Dsa.ModArith.reduceContract, Proof.Dsa.ModArith.reduceSig, reduceLayout, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    sig_and_intros
    · decide
    · decide
    · decide
    · exact Region.disjoint_of_sep (by decide)
    · decide
    · decide
    · rw [show BitVec.toNat (620 : BitVec 32) = 620 from rfl]
      simp only [contextBytes, slot, stride]; omega
    all_goals
      obtain ⟨k, hk⟩ : ∃ k, 8 * n = k + 2 := ⟨8 * n - 2, by omega⟩
      unfold numAt
      rw [hk]
    · exact (read_ones _ k).1
    · exact (read_ones _ k).2

theorem reduceVerified (n : Nat) (hn : 0 < n := by decide) (hn48 : n ≤ 48 := by decide) :
    Verified Arm.target (reduceBody n) (Proof.Dsa.ModArith.reduceContract (reduceLayout n) Arm.abi) :=
  Verified.of_correct (reduceArm_correct hn hn48) (reduceArm_ct hn hn48) (reduceArm_implies hn hn48)

end VG.Proof.Dsa.Arm.Pow
