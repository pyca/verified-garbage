module

public import VerifiedGarbage.Proof.X448.RISCV64.Setup
public import VerifiedGarbage.Proof.X448.RISCV64.Slots
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# X448 on RISCV64: the whole function's contract

`vg_x448`'s contract on this target (`x448RISCV64`), and facts about the
slots and the output that its proof (`Proof/X448/RISCV64/R64/Verified.lean`)
uses.
-/

@[expose] public section

namespace VG.Proof.X448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X448.RISCV64 VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Spec.X448 (P Fe bytesAt)
open VG.Proof.X25519 (leBytes)
open VG.Proof.X448 (toFe ladderAfter ladderAfter_swap_le)

/-- `vg_x448(out = a0, scalar = a1, point = a2, scratch = a3)`. -/
def x448RISCV64 : Contract RISCV64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 56⟩
    let sc : Region := ⟨s.gpr .a1, 56⟩
    let pt : Region := ⟨s.gpr .a2, 56⟩
    let ws : Region := ⟨s.gpr .a3, 8192⟩
    s.rd = [sc, pt] ∧ s.wr = [out, ws] ∧ out.Disjoint sc ∧ out.Disjoint pt ∧ out.Disjoint ws ∧
      sc.Disjoint ws ∧ pt.Disjoint ws
  post s s' := bytesAt s'.mem (s.gpr .a0) 56 =
    VG.Spec.X448.x448 (bytesAt s.mem (s.gpr .a1) 56) (bytesAt s.mem (s.gpr .a2) 56)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

theorem XPre.of {s : State} (h : x448RISCV64.pre s) : XPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

section
variable {b : Addr}

/-- The slots stay through a write of `BITS`. -/
theorem SlotsOk.bits {m m' : Mem} {qs : List Nat} {v : Nat → Fe} (hS : SlotsOk m b qs v)
    (hq : (qs.all fun q => q + 56 ≤ BITS) = true)
    (hf : Frame [⟨b + BitVec.ofNat 64 BITS, 448⟩] m m') : SlotsOk m' b qs v := by
  intro q hq'
  have h := List.all_eq_true.mp hq q hq'
  simp only [decide_eq_true_eq] at h
  have hB : BITS = 1064 := rfl
  have e := limb_frame (o := q) hf fun r hr k hk => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  rw [FS, V, val32_congr e]; exact hS q hq'

end

theorem bytesAt_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 56⟩ r) : bytesAt m' p 56 = bytesAt m p 56 := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf _ fun r hr hc => hd r hr _ (Offset.contains_base _ (by omega) (by omega)) hc

end VG.Proof.X448.RISCV64
