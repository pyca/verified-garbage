module

public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Entry
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Depth

/-! # Saving the caller's registers around key preparation -/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.PreparedKey
open VG.Impl.MlDsa.AArch64.Call (Ptr)
open VG.Spec.Sha3 (bytesAt)

theorem preserved_other_kept :
    ∀ r ∈ preserved, r ≠ .x24 → r ≠ .x30 → r ∈ keptRegs := by decide

theorem frame_depth_bounds {d : Nat} (h : 16 * d + 64 < 2 ^ 64) :
    16 * (d + 1 + 1 + 1) + 16 < 2 ^ 64 ∧
    16 * (d + 1 + 1) + 16 < 2 ^ 64 ∧
    16 * (d + 1) + 16 < 2 ^ 64 ∧ 16 * d + 16 < 2 ^ 64 := by
  omega

theorem prepareFrame_correct {bytes count : Nat} {body : Prog isa}
    {B : Mem → Addr → Prop} {ws : List (Ptr × Nat)}
    (hdepth : 16 * body.aarch64Depth + 64 < 2 ^ 64)
    (hbody : ∀ s, Lay 16 (input bytes) (output bytes count) s →
      WP isa body s fun t => PPostB 16 s t ws ∧ t.gpr .x24 = s.gpr .x24 ∧
        bytesAt t.mem (pa s (.x26, 0)) bytes = bytesAt s.mem (pa s (.x25, 0)) bytes ∧
        B t.mem (pa s (.x26, 0)))
    {σ : State} (h : EntryPre bytes count σ)
    (hb : bytes < 2 ^ 32) (ho : bytes + 1024 * count < 2 ^ 32) :
    WP isa (prepareFrame body) σ fun t => abiPreserved σ t ∧
      bytesAt t.mem (σ.gpr .x1) bytes = bytesAt σ.mem (σ.gpr .x0) bytes ∧
      B t.mem (σ.gpr .x1) := by
  have hd := frame_depth_bounds hdepth
  unfold prepareFrame
  simp only [List.foldr_cons, List.foldr_nil]
  have g0 := frame_guards (s := σ) h (offset := 0) (by decide) rfl (by simp)
  refine WP.frameReg g0.1 g0.2 ?_ (by simpa only [Code.aarch64Depth, Instr.frameUnits, Nat.zero_max] using hd.1)
  have g1 := frame_guards (s := pushState .x25 σ) h (offset := 16) (by decide) rfl rfl
  refine WP.frameReg g1.1 g1.2 ?_ (by simpa only [Code.aarch64Depth, Instr.frameUnits, Nat.zero_max] using hd.2.1)
  have g2 := frame_guards (s := pushState .x26 (pushState .x25 σ)) h
    (offset := 32) (by decide) rfl (by simp only [pushState, BitVec.sub_sub]; rfl)
  refine WP.frameReg g2.1 g2.2 ?_ (by simpa only [Code.aarch64Depth, Instr.frameUnits, Nat.zero_max] using hd.2.2.1)
  have g3 := frame_guards (s := pushState .x28 (pushState .x26 (pushState .x25 σ))) h
    (offset := 48) (by decide) rfl (by simp only [pushState, BitVec.sub_sub]; rfl)
  refine WP.frameReg g3.1 g3.2 ?_ (by simpa only [Code.aarch64Depth, Nat.zero_max] using hd.2.2.2)
  refine WP.seq (WP.mono (setup_ok (innerState σ)) fun s ⟨hs, h25, h26, h28⟩ => ?_)
  change s.gpr .x25 = σ.gpr .x0 at h25
  change s.gpr .x26 = σ.gpr .x1 at h26
  change s.gpr .x28 = σ.gpr .x2 at h28
  have L := entry_layout h hb ho hs.rd hs.wr (hs.sp.trans (inner_sp σ)) h25 h26 h28
  refine WP.mono (hbody s L) fun t ⟨ht, h24, hout, hB⟩ => ?_
  refine ⟨⟨?_, rfl, ?_⟩, ?_, ?_⟩
  · intro r hr
    by_cases e25 : r = .x25
    · subst r
      simp [State.write]
    by_cases e26 : r = .x26
    · subst r
      simp [State.write]
    by_cases e28 : r = .x28
    · subst r
      simp [State.write]
    by_cases e30 : r = .x30
    · subst r
      simp [State.write]
    simp only [State.write, e25, e26, e28, e30, ite_false]
    by_cases e24 : r = .x24
    · subst r
      rw [h24, hs.get .x24]
      rfl
    · rw [ht.bs r (preserved_other_kept r hr e24 e30), hs.get r (by simp [e25, e26, e28])]
      rfl
  · intro r hr
    exact (ht.vcs r hr).trans (hs.keep.vcs r hr)
  · change bytesAt t.mem (σ.gpr .x1) bytes = bytesAt σ.mem (σ.gpr .x0) bytes
    rw [pa, pa, h25, h26, BitVec.add_zero, BitVec.add_zero, hs.mem, inner_source h hb] at hout
    exact hout
  · change B t.mem (σ.gpr .x1)
    simpa only [pa, h26, BitVec.add_zero] using hB

end VG.Proof.MlDsa.AArch64.PreparedKey
