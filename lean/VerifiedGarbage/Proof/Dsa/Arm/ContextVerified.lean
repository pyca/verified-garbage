module

public import VerifiedGarbage.Proof.Dsa.Arm.ContextBody
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.ModPowContract
public import VerifiedGarbage.Proof.Dsa.MontContextContract

/-! # The shared context helper against its public arithmetic contract -/

@[expose] public section
namespace VG.Proof.Dsa.Arm.Context
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm.Context
open VG.Proof.Dsa.ModPow (numAt Keeps)

/-- A four-byte integer is the word used by the arithmetic. -/
theorem numAt_word (m : Mem) (base : Addr) (d : Nat) : numAt m base d 4 = w32 m base d := rfl

def setupArm (n : Nat) : Contract isa where
  pre s :=
    let ws := State.addr (s.gpr .r0)
    let M := numAt s.mem ws (modS n) (8 * n)
    s.rd = [] ∧ s.wr = [⟨ws, (s.gpr .r1).toNat * 8⟩] ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat * 8 ≤ 2 ^ 32 ∧
      contextBytes n ≤ 8 * (s.gpr .r1).toNat ∧ M % 2 = 1 ∧ 1 < M
  post s t :=
    let ws := State.addr (s.gpr .r0)
    let M := numAt s.mem ws (modS n) (8 * n)
    (M * numAt t.mem ws invO 4 + 1) % 2 ^ 16 = 0 ∧
      numAt t.mem ws (oneS n) (8 * n) = 1 ∧
      numAt t.mem ws (rrS n) (8 * n) = 2 ^ (128 * n) % M ∧
      Keeps ws (s.gpr .r1).toNat (scratch n) s.mem t.mem
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1

theorem setupArm_pre {n : Nat} {s : State} (H : (setupArm n).pre s) : (setupK n).pre s := by
  obtain ⟨hrd, hwr, hnw, hz, hodd, hm1⟩ := H
  simp only [Pow.numAt_eq8] at hodd hm1
  exact ⟨hrd, hwr, hnw, by omega, hodd, hm1⟩

theorem setupArm_correct {n : Nat} (hn : 0 < n) (hn48 : n ≤ 48) (s : State) (H : (setupArm n).pre s) :
    ∃ tr t, Exec isa (body n) s tr t ∧ abiPreserved s t ∧ (setupArm n).post s t := by
  obtain ⟨tr, t, Ex, P, Inv, One, RR, O⟩ := setupK_correct hn hn48 s (setupArm_pre H)
  refine ⟨tr, t, Ex, P, ?_, ?_, ?_, fun i hi hj => O _ fun r hr => ?_⟩
  · simpa only [Pow.numAt_eq8, numAt_word] using Inv
  · simpa only [Pow.numAt_eq8] using One
  · simpa only [Pow.numAt_eq8] using RR
  · rw [show ofs (State.addr (s.gpr .r0)) (State.addr (s.gpr .r0) + BitVec.ofNat 64 i) = i by
      simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by have := H.2.2.1; omega)]]
    exact hj r hr

theorem setupArm_ct (n : Nat) : ConstantTime isa (setupArm n).pre (setupArm n).pub (body n) :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => setupK_ct n _ _ _ _ _ _ (setupArm_pre h₁) (setupArm_pre h₂) hp.2.1 e₁ e₂

def satState : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 620 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem _ := 1
  rd := []
  wr := [⟨0x1000, 4960⟩]

theorem setupArm_implies {n : Nat} (hn : 0 < n) (hn48 : n ≤ 48) :
    (setupArm n).Implies (Proof.Dsa.MontContext.setupContract (layout n) Arm.abi) where
  pre := by
    sig_implies_pre [Proof.Dsa.MontContext.setupContract, Proof.Dsa.MontContext.sig, Proof.Dsa.ModPow.sig,
      setupArm, layout, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  post := by
    sig_implies_post [Proof.Dsa.MontContext.setupContract, Proof.Dsa.MontContext.sig, Proof.Dsa.ModPow.sig,
      setupArm, layout, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  pub := by
    sig_implies_pub [Proof.Dsa.MontContext.setupContract, Proof.Dsa.MontContext.sig, Proof.Dsa.ModPow.sig,
      setupArm, layout, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  sat := by
    refine ⟨satState, ?_⟩
    sig_pre [Proof.Dsa.MontContext.setupContract, Proof.Dsa.MontContext.sig, Proof.Dsa.ModPow.sig,
      layout, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
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
    · exact (Pow.read_ones _ k).1
    · exact Nat.lt_of_lt_of_le (by decide) (Pow.read_ones _ k).2

theorem verified (n : Nat) (hn : 0 < n := by decide) (hn48 : n ≤ 48 := by decide) :
    Verified Arm.target (body n) (Proof.Dsa.MontContext.setupContract (layout n) Arm.abi) :=
  Verified.of_correct (setupArm_correct hn hn48) (setupArm_ct n) (setupArm_implies hn hn48)

end VG.Proof.Dsa.Arm.Context
