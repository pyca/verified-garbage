module

import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.X25519.AArch64.Lit
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.X25519.AArch64.Ladder
public import VerifiedGarbage.Proof.X25519.AArch64.Setup
public import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Impl.X25519.AArch64
import VerifiedGarbage.Proof.X25519.AArch64.Ops
import VerifiedGarbage.Proof.X25519.Invert
import Mathlib.Logic.Function.Basic
/-!
# X25519 on AArch64: the whole function

The contract the proof is written against (the facts of
`Spec.X25519.x25519Contract` it uses, stated for AArch64), and the correctness
of `vg_x25519` against it: every write is in the working space but the
result's, so the arguments are read unchanged, and the callee-saved registers
it uses are restored from the working space.
-/

@[expose] public section

namespace VG.Proof.X25519

open VG VG.AArch64 in
/-- `vg_x25519(out = x0, scalar = x1, point = x2, scratch = x3)`. -/
def x25519AArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 32⟩
    let scalar : Region := ⟨s.gpr .x1, 32⟩
    let point : Region := ⟨s.gpr .x2, 32⟩
    let scratch : Region := ⟨s.gpr .x3, 4096⟩
    s.rd = [scalar, point] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      scalar.Disjoint scratch ∧ point.Disjoint scratch
  post s s' := Spec.X25519.bytesAt s'.mem (s.gpr .x0) 32 =
    Spec.X25519.x25519 (Spec.X25519.bytesAt s.mem (s.gpr .x1) 32)
      (Spec.X25519.bytesAt s.mem (s.gpr .x2) 32)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.X25519

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64 VG.Spec.X25519 VG.Proof.X25519

/-! ## Regions of the working space, and outside it -/

theorem saveR_disj (b : Addr) {e n : Nat} (h : 48 ≤ e) (he : e + n ≤ 2 ^ 64) :
    (saveR b).Disjoint ⟨b + BitVec.ofNat 64 e, n⟩ := Offset.base_disjoint b h he

theorem sub_scR (b : Addr) {d n : Nat} (h : d + n ≤ 4096) :
    Region.Sub ⟨b + BitVec.ofNat 64 d, n⟩ (scR b) := Offset.sub_base b h

/-- A byte of an argument outside the working space is unchanged. -/
theorem byte_out {b p : Addr} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r (scR b)) (hd : (⟨p, 32⟩ : Region).Disjoint (scR b)) {i : Nat}
    (hi : i < 32) : m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf.bytes (R := ⟨p, 32⟩) (fun r hr => hd.sub_right (hs r hr)) (by show (32 : Nat) ≤ 2 ^ 64; decide) hi

theorem bytesAt_out {b p : Addr} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r (scR b)) (hd : (⟨p, 32⟩ : Region).Disjoint (scR b)) :
    bytesAt m' p 32 = bytesAt m p 32 := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => byte_out hf hs hd (List.mem_range.mp hi)

/-- A saved register's word is unchanged by writes elsewhere. -/
theorem save_frame {b : Addr} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (saveR b).Disjoint r) {k : Nat} (hk : k < 6) :
    wd m' b (SAVE + 8 * k) = wd m b (SAVE + 8 * k) := by
  simp only [wd]
  rw [hf.readW (r := saveR b) (Offset.contains_base b (by simp only [SAVE]; omega)
    (by simp only [SAVE]; omega)) hd (by decide)]

/-! ## The arguments, decoded -/

theorem clampB_eq {m m₀ : Mem} {sc : Addr}
    (h : ∀ i < 32, m (sc + BitVec.ofNat 64 i) = m₀ (sc + BitVec.ofNat 64 i)) {t : Nat} (ht : t < 255) :
    clampB (fun i => m (sc + BitVec.ofNat 64 i)) t =
      BitVec.ofNat 8 (bit (decodeScalar25519 (bytesAt m₀ sc 32)) t) := by
  rw [scalar_bit (length_bytesAt _ _ _) ht]
  simp only [clampB]
  repeat' split
  · rfl
  · rfl
  · have hg : (bytesAt m₀ sc 32).getD (t / 8) 0 = m₀ (sc + BitVec.ofNat 64 (t / 8)) := by
      simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (show t / 8 < 32 by omega), Option.map_some, Option.getD_some]
    rw [hg, h _ (by omega)]
    rfl

/-! ## The whole function -/

/-- The precondition, by name. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨s₀.gpr .x1, 32⟩, ⟨s₀.gpr .x2, 32⟩]
  wr : s₀.wr = [⟨s₀.gpr .x0, 32⟩, ⟨s₀.gpr .x3, 4096⟩]
  out_sc : (⟨s₀.gpr .x0, 32⟩ : Region).Disjoint ⟨s₀.gpr .x3, 4096⟩
  scalar_sc : (⟨s₀.gpr .x1, 32⟩ : Region).Disjoint ⟨s₀.gpr .x3, 4096⟩
  point_sc : (⟨s₀.gpr .x2, 32⟩ : Region).Disjoint ⟨s₀.gpr .x3, 4096⟩

theorem Pre.of (s₀ : State) (h : Proof.X25519.x25519AArch64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

end VG.Proof.X25519.AArch64
