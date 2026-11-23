module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Instances
import VerifiedGarbage.Proof.Framework.X86_64.ScrubFill
import VerifiedGarbage.Proof.Framework.Lit

/-! The shared encryption leaf fits the existing seal callers' stack and register cleanup. -/

@[expose] public section
namespace VG.Proof.AesGcm.X86_64

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64
open VG.Impl.AesGcm.X86_64 (Fn)

private theorem seal_fill {k : Nat} (c g : Fn) (p : Prog isa) {minimum : Nat}
    (hc : calleeSide c.code k 0 = true) (hg : calleeSide g.code k 0 = true) :
    Fill k (fun _ => 0) (Impl.AesGcm.X86_64.BlocksToDec.sealPrepared ctrStub ghStub p true minimum)
      (Impl.AesGcm.X86_64.BlocksToDec.sealPrepared c g p true minimum) := by
  fill_calls_wide

private theorem level_of_backend {v : GcmVariant} {nm : StitchToName} (h : v.shortBackend = some nm) :
    nm.lv.level ≤ v.lvG.level := by
  suffices v.toLv = nm.lv by rw [← this]; exact level_join_right _ _
  rcases he : v.stitch with _ | pt
  · simp [GcmVariant.shortBackend,he] at h
  · rcases hp : pt.toPart with _ | x
    · simp [GcmVariant.shortBackend,he,hp] at h
    · simp [GcmVariant.shortBackend,he,hp] at h
      simp [GcmVariant.toLv,he,hp,h]

theorem selectSealLeaf_side {M} (v : GcmVariant) (name : String)
    (supported : Bool) (short : FusedShortOk M) (wide : Option (PLift (WideSealOk M))) :
    ∀ b ∈ selectSealLeaf v name supported short wide, calleeSide b.fn.code v.lvG.level 8 = true := by
  intro b mem
  have hc := calleeSide_mono (Nat.le_trans (level_join_right v.lv v.ctrTo.level)
    (level_join_left (v.lv.join v.ctrTo.level) v.toLv)) (Nat.le_refl _) v.ctrTo.side
  have hg := calleeSide_mono (Nat.le_trans (v.impl.lv_le v.own).2.2.1
    (show v.lv.level ≤ v.lvG.level from Nat.le_trans (level_join_left _ _) (level_join_left _ _)))
    (Nat.le_refl _) v.impl.gh.side
  cases supported with
  | false => simp [selectSealLeaf] at mem
  | true =>
    cases hn : v.shortBackend with
    | none => simp [selectSealLeaf,hn] at mem
    | some nm =>
      have hl := level_of_backend hn
      cases nm with
      | vaes =>
        simp [selectSealLeaf,hn] at mem
        subst b
        exact calleeSide_of_fill (seal_fill _ _ _ hc hg) hl (by lit_decide)
      | aesniAvx =>
        simp [selectSealLeaf,hn] at mem
        subst b
        exact calleeSide_of_fill (seal_fill _ _ _ hc hg) hl (by lit_decide)
      | vaesAvx512 =>
        cases wide with
        | none => simp [selectSealLeaf,hn] at mem
        | some ok =>
          simp [selectSealLeaf,hn] at mem
          subst b
          exact calleeSide_of_fill (seal_fill _ _ _ hc hg) hl (by lit_decide)

theorem sealLeafF_side (v : GcmVariant) : ∀ b ∈ sealLeafF v, calleeSide b.fn.code v.lvG.level 24 = true :=
  fun b h => calleeSide_mono (Nat.le_refl _) (by decide : 8 ≤ 24) (selectSealLeaf_side v _ _ _ _ b h)

theorem sealLeafF16_side (v : GcmVariant) : ∀ b ∈ sealLeafF16 v, calleeSide b.fn.code v.lvG.level 24 = true :=
  fun b h => calleeSide_mono (Nat.le_refl _) (by decide : 8 ≤ 24) (selectSealLeaf_side v _ _ _ _ b h)

theorem withSameDst_side (f : Fn) {k : Nat} (h : calleeSide f.code k 8 = true) :
    calleeSide f.withSameDst.code k 8 = true := by
  have level : (Instr.mov .r10 (.reg .r8)).vecLevel = 0 := rfl
  simpa [level, Impl.AesGcm.X86_64.Fn.withSameDst, calleeSide, Code.x86_64Depth, Code.allInstrs,
    UpperLock.inames, Instr.vecLevelR, loadsMxcsr] using h

end VG.Proof.AesGcm.X86_64
