module

public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.FwdU
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.FwdW
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.RunI
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.ModelI
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Ctx
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.MlKem.Mem16
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.MlKem
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.LitI

/-!
# ML-KEM on AArch64: the 16-bit inverse NTTs, by the machine

`nttInv` (`nttInv_run`), which first stores the table in the working space (`halves_ok`),
transforms the polynomial at `x0` in place: the machine's state at the start holds of the
caller's (`initU_rel`), with the inverse's model (`modelI`), and its run (`checkIN_ok`) leaves
the reduced coefficients of `NTT⁻¹` in the polynomial.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Ntt16 (halves_ok)

theorem nttInv_split : Impl.MlKem.AArch64.Ntt16.nttInv =
    .seq (.block (Impl.MlKem.AArch64.Ntt16.halves Impl.MlKem.AArch64.Ntt16.invTableHalves .x1 512 ++ invHead))
      invRest := by
  rw [Impl.MlKem.AArch64.Ntt16.nttInv, invHead, List.append_assoc]
  rfl

theorem nttInv_run (s₀ : State) (hi : InN s₀) :
    WP isa Impl.MlKem.AArch64.Ntt16.nttInv s₀ fun s' =>
      s'.sp = s₀.sp ∧ PolyIs s'.mem (s₀.gpr .x0) (nttInv (polyAt s₀.mem (s₀.gpr .x0))) := by
  rw [nttInv_split, WP.seq_iff, WP.block_append_iff]
  have hreg : polyRegion (s₀.gpr .x1) ∈ s₀.wr := by rw [hi.wr]; simp
  have hlen : Impl.MlKem.AArch64.Ntt16.invTableHalves.length = 256 := by
    rw [Impl.MlKem.AArch64.Ntt16.invTableHalves.lit_eq]; decide +kernel
  refine WP.mono (halves_ok Impl.MlKem.AArch64.Ntt16.invTableHalves (r := .x1) (by decide) (off := 512)
    (by rw [hlen]) (by decide) hreg) fun s₁ h₁ => ?_
  change WP isa (.block invHead) s₁ (fun s₂ => WP isa invRest s₂ _)
  rw [← WP.seq_iff]
  change WP isa nttInvTail s₁ _
  have e0 : s₁.gpr .x0 = s₀.gpr .x0 := h₁.keep.get .x0 (by decide)
  have e1 : s₁.gpr .x1 = s₀.gpr .x1 := h₁.keep.get .x1 (by decide)
  have hm : ∀ k < 1024, s₁.mem (s₀.gpr .x0 + BitVec.ofNat 64 k) = s₀.mem (s₀.gpr .x0 + BitVec.ofNat 64 k) :=
    fun k hk => h₁.frame _ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact fun h => hi.disj _ (Offset.contains_base _ (show k + 1 ≤ 1024 by omega) (by omega)) h)
  have hp : ∀ i < n, coeffAt s₁.mem (s₀.gpr .x0) i = coeffAt s₀.mem (s₀.gpr .x0) i :=
    fun i hi' => coeffAt_congr hm hi'
  have hpoly : polyAt s₁.mem (s₀.gpr .x0) = polyAt s₀.mem (s₀.gpr .x0) :=
    Vector.ext fun i hi' => by simp only [polyAt, Vector.getElem_ofFn]; rw [hp i hi']
  have hi₁ : InN s₁ := ⟨by rw [h₁.keep.wr, hi.wr, e0, e1], by rw [e0, e1]; exact hi.disj,
    fun i hi' => by rw [e0, hp i hi']; exact hi.red i hi'⟩
  have hc := checkIN_ok
  generalize hx : initIU.runP invRules rsN 16 nttInvTail = x at hc
  cases x with
  | none => cases hc
  | some σ =>
    have hrel := initU_rel (rs := rsN) (s₀ := s₁) (tb := s₁.gpr .x1 + BitVec.ofNat 64 512) (L := Li (Wu s₁))
      (O := Oi (Wu s₁)) (fun _ => rfl) rfl rfl rfl rfl rfl rfl itabT_get (fun j hj => by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.zero_add, e1]
        exact h₁.tab j (by rw [hlen]; exact hj))
    refine WP.mono (runP_ok (modelI (Wu s₁)) (ctxN hi₁) 16 _ hrel hx) fun s' h' =>
      ⟨by rw [h'.sp, h₁.keep.sp], ?_⟩
    rw [← hpoly, ← e0]
    exact polyIs_of_outU rfl rfl rfl h' hc fun p hp => Oi_nttInv (Wu s₁) _ (fun p hp => lrep_redU hi₁.red hp) hp

end VG.Proof.MlKem.AArch64.NttR
