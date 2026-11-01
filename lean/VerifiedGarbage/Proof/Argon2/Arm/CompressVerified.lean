module

public import VerifiedGarbage.Proof.Argon2.Arm.Compress
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Argon2.Arm.CompressContract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Argon2.Arm.CompressLit
public import VerifiedGarbage.Impl.Argon2.Arm.Compress
import VerifiedGarbage.Proof.Argon2.Arm.Mix
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Argon2.Arm.Compress
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Argon2.Arm.CompressContract
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Argon2.Arm.CompressLit
meta import VerifiedGarbage.Impl.Argon2.Arm.Compress
meta import VerifiedGarbage.Proof.Argon2.Arm.Mix
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Argon2.Contract

/-!
# Argon2 compression on ARMv7: verified

Constant time puts together the taint analysis of each piece, from what
both runs agree on (`RelCT`): the pointers are public; the passes over the
rows and columns depend only on `scratch` (`rounds_ct`); and `out`, loaded
from `scratch` after the rounds, is the same in both runs, by correctness. `compress_verified'` is the proof against `compressArm`, which the
derivation uses for its calls; the shared contract
`Proof.Argon2.compressContract` implies it (`compress_verified`).
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm

open VG VG.Arm VG.Spec.Argon2
open VG.Impl.Argon2.Arm (outOff)
open VG.Proof.Sha512.Arm (A A_eq)
open VG.Proof.MdStream.Arm (wp_ldr)

/-- The pointers are public. -/
theorem agree₀ {s₁ s₂ : State} (hpub : compressArm.pub s₁ s₂) :
    VG.Arm.Taint.Agree (VG.Arm.Taint.ofRegs [.r0, .r1, .r2, .r3]) s₁ s₂ := by
  obtain ⟨p0, p1, p2, p3⟩ := hpub
  exact VG.Arm.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- Two runs from the precondition, with the same pointers. -/
def P₀ (s₁ s₂ : State) : Prop := compressArm.pre s₁ ∧ compressArm.pre s₂ ∧ compressArm.pub s₁ s₂

/-- After the initialization, from states related by `P₀`. -/
def R₁ (s₁ s₂ : State) : Prop := ∃ σ₁ σ₂, P₀ σ₁ σ₂ ∧ InitInv σ₁ s₁ 256 ∧ InitInv σ₂ s₂ 256

/-- What the rounds keep: `r3`, the regions, and the word holding `out`. -/
def Kept (u t : State) : Prop :=
  t.gpr .r3 = u.gpr .r3 ∧ t.rd = u.rd ∧ t.wr = u.wr ∧
    t.mem.readW (A (u.gpr .r3) outOff) 32 = u.mem.readW (A (u.gpr .r3) outOff) 32

/-- After the rounds. -/
def R₂ (s₁ s₂ : State) : Prop := ∃ u₁ u₂, R₁ u₁ u₂ ∧ Kept u₁ s₁ ∧ Kept u₂ s₂

/-- `out` loaded: in `r2`, with `r3` still `scratch`. -/
def Loaded (u t : State) : Prop := t.gpr .r2 = u.mem.readW (A (u.gpr .r3) outOff) 32 ∧ t.gpr .r3 = u.gpr .r3

/-- After loading `out`. -/
def R₃ (s₁ s₂ : State) : Prop := ∃ u₁ u₂, R₂ u₁ u₂ ∧ Loaded u₁ s₁ ∧ Loaded u₂ s₂

section
variable {σ s : State} (hp : Pre σ) (h : InitInv σ s 256)
include hp h

omit hp in
theorem InitInv.r3 : s.gpr .r3 = scr σ := h.regs _ (by decide) (by decide)

theorem InitInv.scr : Scr (s.gpr .r3) s.wr := by
  rw [h.r3, h.wr]; exact ⟨hp.scr_fits, fun o ho => hp.scr_wr rfl ho⟩

theorem InitInv.out : s.mem.readW (A (s.gpr .r3) outOff) 32 = op σ := by
  have := h.saved (.r2, outOff) (by decide)
  rw [h.r3, A_eq (by have := hp.scr_fits; simp only [outOff]; omega)]; exact this

end

theorem init_all {σ : State} (hp : Pre σ) :
    WP isa (.block (Impl.Argon2.Arm.prologue ++ (List.range 256).flatMap Impl.Argon2.Arm.initWord)) σ
      (InitInv σ · 256) :=
  prologue_ok hp fun _ h₁ => init_ok hp h₁ 256 (Nat.le_refl _)

theorem compress_ct : ConstantTime isa compressArm.pre compressArm.pub Impl.Argon2.Arm.compress := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  unfold Impl.Argon2.Arm.compress
  -- The prologue and the initialization: the pointers are public.
  have h₁ : RelCT isa P₀ (.block (Impl.Argon2.Arm.prologue ++
      (List.range 256).flatMap Impl.Argon2.Arm.initWord)) R₁ := by
    have ct : RelCT isa P₀ (.block (Impl.Argon2.Arm.prologue ++
        (List.range 256).flatMap Impl.Argon2.Arm.initWord)) fun _ _ => True :=
      RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs [.r0, .r1, .r2, .r3]) (fun _ _ h => agree₀ h.2.2)
        (by taint_decide)
    refine (ct.wpDep (F := fun σ s => InitInv σ s 256)
      fun s₁ s₂ h => ⟨init_all (pre_of _ h.1), init_all (pre_of _ h.2.1)⟩).mono (fun _ _ h => h) ?_
    rintro s₁ s₂ ⟨-, h⟩
    exact h
  -- The rounds: `scratch` is the same in both runs.
  have h₂ : RelCT isa R₁ Impl.Argon2.Arm.rounds R₂ := by
    have ct : RelCT isa R₁ Impl.Argon2.Arm.rounds fun _ _ => True := by
      refine rounds_ct.mono ?_ fun _ _ _ => trivial
      rintro s₁ s₂ ⟨σ₁, σ₂, ⟨q₁, q₂, pub⟩, i₁, i₂⟩
      have hp₁ := pre_of _ q₁; have hp₂ := pre_of _ q₂
      exact ⟨by rw [i₁.r3, i₂.r3]; exact pub.2.2.2, i₁.scr hp₁, i₂.scr hp₂⟩
    have kept {σ u : State} (hp : Pre σ) (i : InitInv σ u 256) : WP isa Impl.Argon2.Arm.rounds u (Kept u) :=
      (rounds_ok (i.scr hp)).mono fun t ht => ⟨ht.r3, ht.rd, ht.wr,
        outside_pass (by rw [i.r3]; exact hp.scr_fits) ht.frame (.inr ⟨by decide, by decide⟩)⟩
    refine (ct.wpDep (F := Kept) fun s₁ s₂ h => ?_).mono (fun _ _ h => h) ?_
    · obtain ⟨σ₁, σ₂, ⟨q₁, q₂, -⟩, i₁, i₂⟩ := h
      exact ⟨kept (pre_of _ q₁) i₁, kept (pre_of _ q₂) i₂⟩
    · rintro s₁ s₂ ⟨-, h⟩
      exact h
  -- Loading `out`: `r3` is `scratch`, in both runs.
  have h₃ : RelCT isa R₂ (.block [.ldr .r2 .r3 outOff]) R₃ := by
    have ct : RelCT isa R₂ (.block [.ldr .r2 .r3 outOff]) fun _ _ => True := by
      refine RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs [.r3]) (fun s₁ s₂ h => ?_) (by taint_decide)
      obtain ⟨u₁, u₂, ⟨σ₁, σ₂, ⟨q₁, q₂, pub⟩, i₁, i₂⟩, k₁, k₂⟩ := h
      exact VG.Arm.Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [k₁.1, k₂.1, i₁.r3, i₂.r3]; exact pub.2.2.2
    have load {σ u t : State} (hp : Pre σ) (i : InitInv σ u 256) (k : Kept u t) :
        WP isa (.block [.ldr .r2 .r3 outOff]) t (Loaded t) :=
      wp_ldr (by decide) rfl (by
        rw [k.2.1, k.2.2.1, k.1, i.r3, i.rd, i.wr]; exact hp.in_scr rfl (by decide))
        fun t' u' => WP.block_nil ⟨u'.gpr, u'.other _ (by decide)⟩
    refine (ct.wpDep (F := Loaded) fun s₁ s₂ h => ?_).mono (fun _ _ h => h) ?_
    · obtain ⟨u₁, u₂, ⟨σ₁, σ₂, ⟨q₁, q₂, -⟩, i₁, i₂⟩, k₁, k₂⟩ := h
      exact ⟨load (pre_of _ q₁) i₁ k₁, load (pre_of _ q₂) i₂ k₂⟩
    · rintro s₁ s₂ ⟨-, h⟩
      exact h
  -- The output and the epilogue: `out` and `scratch` are public.
  have h₄ : RelCT isa R₃ (.block Impl.Argon2.Arm.epilogue) fun _ _ => True := by
    refine RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs [.r2, .r3]) (fun s₁ s₂ h => ?_) (by taint_decide)
    obtain ⟨t₁, t₂, ⟨u₁, u₂, ⟨σ₁, σ₂, ⟨q₁, q₂, pub⟩, i₁, i₂⟩, k₁, k₂⟩, l₁, l₂⟩ := h
    have hp₁ := pre_of _ q₁; have hp₂ := pre_of _ q₂
    exact VG.Arm.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [l₁.1, l₂.1, k₁.1, k₂.1, k₁.2.2.2, k₂.2.2.2, i₁.out hp₁, i₂.out hp₂]; exact pub.2.2.1
      · rw [l₁.2, l₂.2, k₁.1, k₂.1, i₁.r3, i₂.r3]; exact pub.2.2.2
  exact h₁.seq (h₂.seq (h₃.seq h₄))

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

theorem compress_implies : compressArm.Implies (Proof.Argon2.compressContract Arm.abi) := by
  sig_implies [Proof.Argon2.compressContract, Proof.Argon2.compressSig, compressArm, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [satState, Mem.readW, Mem.read] using satState

/-- The emitted function, against the shared contract. -/
theorem compress_verified :
    Verified Arm.target Impl.Argon2.Arm.compress (Proof.Argon2.compressContract Arm.abi) :=
  compress_verified'.of_implies compress_implies

end VG.Proof.Argon2.Arm
