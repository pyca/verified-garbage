import VerifiedGarbage.Proof.Argon2.Arm.Compress
import VerifiedGarbage.Proof.Argon2.Arm.CompressLit
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Argon2.Contract

/-!
# Argon2 compression on ARMv7: verified

Constant time is the taint analysis on the literal code: the pointers are
public, and `out`, kept in `scratch` across the rounds, is a public slot of
it. `compress_verified'` is the proof against `compressArm`, which the
derivation uses for its calls; the shared contract
`Spec.Argon2.compressContract` implies it (`compress_verified`).
-/

namespace VG.Proof.Argon2.Arm

open VG VG.Arm VG.Spec.Argon2

/-- The pointers are public, and they are the bases of `out` and `scratch`. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [1024, 4096],
    bases := [(.r2, 0), (.r3, 1)] }

theorem wf₀ {s : State} (hp : Pre s) : VG.Arm.Taint.Wf τ₀ s := by
  have ho := hp.out_fits; have hsc := hp.scr_fits
  refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp' => ?_, fun h => absurd h (Nat.lt_irrefl 0),
    fun _ h => (List.not_mem_nil h).elim⟩
  · simp only [hp.wr, τ₀]
    exact .cons (by simp) (.cons (by simp) .nil)
  · simp only [hp.wr]
    exact .cons (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.out_scr)
      (.cons (fun _ h => (List.not_mem_nil h).elim) .nil)
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [MdStream.Arm.addr_toNat] <;> omega
  · simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> simp [VG.Arm.Taint.region, hp.wr]

theorem agree₀ {s₁ s₂ : State} (h₁ : compressArm.pre s₁) (h₂ : compressArm.pre s₂)
    (hpub : compressArm.pub s₁ s₂) : VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p0, p1, p2, p3⟩ := hpub
  have hp₁ := pre_of _ h₁; have hp₂ := pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂,
    fun sl h => by simp [τ₀] at h, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [outR, scrR, op, scr, p2, p3]

theorem compress_ct : ConstantTime isa compressArm.pre compressArm.pub Impl.Argon2.Arm.compress :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hpub => agree₀ h₁ h₂ hpub) (by taint_decide)

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x1400 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 1024⟩, ⟨0x1400, 1024⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 4096⟩]

theorem sat_pre : compressArm.pre satState := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩ <;>
  exact Region.disjoint_of_sep (by decide)

/-- The proof, against the contract the derivation's calls use. -/
theorem compress_verified' : Verified Arm.target Impl.Argon2.Arm.compress compressArm := by
  refine ⟨fun s hs => ?_, compress_ct, ⟨satState, sat_pre⟩⟩
  obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩

theorem compress_implies : compressArm.Implies (Spec.Argon2.compressContract Arm.abi) := by
  sig_implies [Spec.Argon2.compressContract, Spec.Argon2.compressSig, compressArm, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [satState, Mem.readW, Mem.read] using satState

/-- The emitted function, against the shared contract. -/
theorem compress_verified :
    Verified Arm.target Impl.Argon2.Arm.compress (Spec.Argon2.compressContract Arm.abi) :=
  compress_verified'.of_implies compress_implies

end VG.Proof.Argon2.Arm
