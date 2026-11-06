module

public import VerifiedGarbage.Proof.Dsa.Arm.Pow
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Dsa.ModPowContract
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.ModPowContract

/-!
# DSA's exponentiation as a function on 32-bit ARM: `Verified`

`vg_dsa_pow_{n}_{e}` against its contract (`Proof/Dsa/ModPowContract.lean`), from
`powK_correct` and `powK_ct`: the contract's numbers are the bytes `Mem.read`
reads (`numAt`), the same as the words `val32` reads (`read_eq_val32`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Pow

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm.Pow
open VG.Proof.Dsa.ModPow (numAt Keeps)

/-- The contract on ARM, as `Proof.Dsa.ModPow.powContract` states it. -/
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

theorem powArm_ct (n e : Nat) (hn : 0 < n) (hn48 : n ≤ 48) : ConstantTime isa (powArm n e).pre (powArm n e).pub (body n e) :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => powK_ct n e hn hn48 _ _ _ _ _ _ (powArm_pre h₁) (powArm_pre h₂) hp.2.1 e₁ e₂

end VG.Proof.Dsa.Arm.Pow
