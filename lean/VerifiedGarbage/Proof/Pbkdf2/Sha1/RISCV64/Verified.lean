module

public import VerifiedGarbage.Proof.Pbkdf2.Sha1.RISCV64.Fin
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Correct
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Impl.Pbkdf2.Sha1.RISCV64

/-!
# PBKDF2-HMAC-SHA-1's iteration on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. Constant time (`ct`), as for
every Merkle–Damgård hash function's iteration
(`Proof/Pbkdf2/RISCV64/Correct.lean`): the taint analysis of `main` after the
entry block, which zero-extends `n`, the one input public only in its low
32 bits (`RelCT.wpDep`). `iterate_verified`: `correct` and `ct` meet the
iteration's contract with `Wi` bytes of scratch space (`iterK`), and the
shared contract of `Spec.Hmac.sha1I` (`iterate`), with no stack.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Sha1.RISCV64

open VG VG.RISCV64 VG.Impl.Pbkdf2.Sha1.RISCV64
open VG.Proof.Pbkdf2.RISCV64 (Entry entry_ok nn iterK pre_of iterImp iterSat)
open VG.Proof.Pbkdf2.RISCV64.Sha1 (it hashOkW)

/-- The taint analysis of `main`, which the kernel checks. -/
theorem main_ck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) main hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `iterate` is constant time, for any precondition whose public data are `iterK`'s. -/
theorem ct {pre : State → Prop} {pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, pub s₁ s₂ → s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
      (s₁.gpr .a2).setWidth 32 = (s₂.gpr .a2).setWidth 32 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧
      s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp) :
    ConstantTime isa pre pub iterate := by
  obtain ⟨_, hb⟩ := main_ck
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.seq ?_ (RelCT.taint (A := taint)
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) (fun _ _ h => h) hb))
  have ag4 : ∀ s₁ s₂ : State, pre s₁ ∧ pre s₂ ∧ pub s₁ s₂ →
      taint.Agree (Taint.ofRegs [.a0, .a1, .a3, .a4]) s₁ s₂ := by
    rintro s₁ s₂ ⟨_, _, hq⟩
    obtain ⟨h0, h1, _, h3, h4, hsp⟩ := hpub s₁ s₂ hq
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [h0, h1, h3, h4]
  refine RelCT.mono (RelCT.wpDep (F := Entry) (RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a3, .a4])
    ag4 (by rw [entry_eq]; taint_decide)) fun s₁ s₂ _ => ⟨by rw [entry_eq]; exact entry_ok s₁,
      by rw [entry_eq]; exact entry_ok s₂⟩) (fun _ _ h => h) ?_
  rintro s₁' s₂' ⟨-, σ₁, σ₂, ⟨_, _, hq⟩, a, b⟩
  obtain ⟨h0, h1, h2, h3, h4, hsp⟩ := hpub σ₁ σ₂ hq
  refine ⟨by rw [a.sp, b.sp, hsp], fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a.other _ (by decide), b.other _ (by decide), h0]
  · rw [a.other _ (by decide), b.other _ (by decide), h1]
  · rw [a.a2, b.a2, nn, nn, h2]
  · rw [a.other _ (by decide), b.other _ (by decide), h3]
  · rw [a.other _ (by decide), b.other _ (by decide), h4]

theorem noFrames : iterate.noFrames = true := by decide

/-- `iterate` meets the iteration's contract, with `Wi` bytes of working space. -/
theorem verifiedW (Wi : Nat) (h₁ : 227 ≤ Wi) (h₂ : Wi ≤ 8192) :
    ∀ s, (iterK Spec.Hmac.sha1S Wi).pre s →
      ∃ t s', Exec isa iterate s t s' ∧ abiPreserved s s' ∧ (iterK Spec.Hmac.sha1S Wi).post s s' := by
  intro s hs
  have ho := hashOkW Wi h₁ h₂
  obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of (P := it) rfl rfl hs) ho.sizes ho.link
  exact ⟨t, s', he, h₁, h₂⟩

/-- `iterate` against the shared contract of `Spec.Hmac.sha1I`. -/
theorem iterate_verified : Verified RISCV64.target iterate (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha1I RISCV64.abi 0) := by
  have hs : ∃ s, (Proof.Pbkdf2.Instance.iterateContract Spec.Hmac.sha1I RISCV64.abi 0).pre s := by
    inst_sat [Proof.Pbkdf2.Instance.iterateContract, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig,
      Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, RISCV64.abi, RISCV64.argRegs]
      using iterSat 84 20 448
  have imp := iterImp hs
  have v : Verified RISCV64.target iterate (iterK Spec.Hmac.sha1S (8 * Spec.Hmac.sha1I.scratch)) :=
    ⟨verifiedW _ (by decide) (by decide), ct (fun _ _ h => h), imp.sat_left⟩
  exact v.of_implies imp

end VG.Proof.Pbkdf2.Sha1.RISCV64
