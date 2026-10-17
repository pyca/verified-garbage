module

public import VerifiedGarbage.Proof.Dsa.Arm.Pow
public import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA's exponentiation as a function on 32-bit ARM: `Verified`

`vg_dsa_pow_{n}_{e}` against its contract (`Spec/Dsa/ModPow.lean`), from
`powK_correct` and `powK_ct`: the contract's numbers are the bytes `Mem.read`
reads (`numAt`), the same as the words `val32` reads (`read_eq_val32`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Pow

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm.Pow
open VG.Spec.Dsa.ModPow (numAt Keeps)

/-- The `4k` bytes at `base + d` are its `k` 32-bit words. -/
theorem read_eq_val32 (m : Mem) (base : Addr) : ∀ (k d : Nat),
    (m.read (off base d) (4 * k)).toNat = val32 m base d k
  | 0, d => by simp [Mem.read, val32]
  | k + 1, d => by
    rw [show 4 * (k + 1) = 4 * k + 4 from rfl, read_toNat_add, val32, ← read_eq_val32 m base k (d + 4),
      Offset.add_add]
    congr 1

theorem numAt_eq8 (m : Mem) (base : Addr) (d n : Nat) : numAt m base d (8 * n) = val32 m base d (2 * n) := by
  rw [← wordsVal_eq_val32, ← read_eq_wordsVal]; rfl

theorem numAt_eq4 (m : Mem) (base : Addr) (d e : Nat) : numAt m base d (4 * e) = val32 m base d e := by
  rw [← read_eq_val32]; rfl

/-- The contract on ARM, as `Spec.Dsa.ModPow.powContract` states it. -/
def powArm (n e : Nat) : Contract isa where
  pre s :=
    let ws := State.addr (s.gpr .r0)
    let M := numAt s.mem ws (modS n) (8 * n)
    s.rd = [] ∧ s.wr = [⟨ws, (s.gpr .r1).toNat * 8⟩] ∧ (s.gpr .r0).toNat + (s.gpr .r1).toNat * 8 ≤ 2 ^ 32 ∧
      contextBytes n ≤ 8 * (s.gpr .r1).toNat ∧ M % 2 = 1 ∧ 1 < M
  post s t :=
    let ws := State.addr (s.gpr .r0)
    numAt t.mem ws (resS n) (8 * n) =
        numAt s.mem ws (baseS n) (8 * n) ^ numAt s.mem ws (expS n) (4 * e) % numAt s.mem ws (modS n) (8 * n) ∧
      Keeps ws (s.gpr .r1).toNat (scratch n) s.mem t.mem
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1

theorem powArm_pre {n e : Nat} {s : State} (h : (powArm n e).pre s) : (powK n e).pre s := by
  obtain ⟨hrd, hwr, hnw, hz, hodd, hm1⟩ := h
  simp only [numAt_eq8] at hodd hm1
  exact ⟨hrd, hwr, hnw, by omega, hodd, hm1⟩

theorem powArm_correct {n e : Nat} (hn : 0 < n) (hn48 : n ≤ 48) (he : 0 < e) (hen : e ≤ 2 * n) (s : State)
    (h : (powArm n e).pre s) :
    ∃ tr t, Exec isa (body n e) s tr t ∧ abiPreserved s t ∧ (powArm n e).post s t := by
  obtain ⟨tr, t, ex, abi, V, O⟩ := powK_correct hn hn48 he hen s (powArm_pre h)
  have hnw := h.2.2.1
  refine ⟨tr, t, ex, abi, ?_, fun i hi hj => O _ fun r hr => ?_⟩
  · simp only [numAt_eq8, numAt_eq4]; exact V
  · rw [show ofs (State.addr (s.gpr .r0)) (State.addr (s.gpr .r0) + BitVec.ofNat 64 i) = i by
      simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by omega)]]
    exact hj r hr

theorem powArm_ct (n e : Nat) : ConstantTime isa (powArm n e).pre (powArm n e).pub (body n e) :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => powK_ct n e _ _ _ _ _ _ (powArm_pre h₁) (powArm_pre h₂) hp.2.1 e₁ e₂

/-- A state satisfying the contract: the working space at `0x1000`, of 620
words, every byte 1. -/
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

/-- Bytes of 1: an odd number, above 1 when there are at least two. -/
theorem read_ones (a : Addr) : ∀ k, (Mem.read (fun _ => 1) a (k + 2)).toNat % 2 = 1 ∧
    1 < (Mem.read (fun _ => 1) a (k + 2)).toNat := by
  intro k
  rw [VG.Proof.Mont.read_toNat_succ, VG.Proof.Mont.read_toNat_succ]
  rw [show (1 : BitVec 8).toNat = 1 from rfl]
  omega

theorem powArm_implies {n e : Nat} (hn : 0 < n) (hn48 : n ≤ 48) :
    (powArm n e).Implies (Spec.Dsa.ModPow.powContract (layout n e) Arm.abi) where
  pre := by
    sig_implies_pre [Spec.Dsa.ModPow.powContract, Spec.Dsa.ModPow.sig, powArm, layout, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  post := by
    sig_implies_post [Spec.Dsa.ModPow.powContract, Spec.Dsa.ModPow.sig, powArm, layout, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  pub := by
    sig_implies_pub [Spec.Dsa.ModPow.powContract, Spec.Dsa.ModPow.sig, powArm, layout, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  sat := by
    refine ⟨satState, ?_⟩
    sig_pre [Spec.Dsa.ModPow.powContract, Spec.Dsa.ModPow.sig, layout, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
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
    · exact (read_ones _ k).2

theorem verified (n e : Nat) (hn : 0 < n := by decide) (hn48 : n ≤ 48 := by decide) (he : 0 < e := by decide)
    (hen : e ≤ 2 * n := by decide) :
    Verified Arm.target (body n e) (Spec.Dsa.ModPow.powContract (layout n e) Arm.abi) :=
  Verified.of_correct (powArm_correct hn hn48 he hen) (powArm_ct n e) (powArm_implies hn hn48)

end VG.Proof.Dsa.Arm.Pow
