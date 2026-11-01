module

public import VerifiedGarbage.Proof.Ed25519.Contract
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseStep
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseInit
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseEncode
import VerifiedGarbage.Proof.X448.Field
import VerifiedGarbage.Proof.Ed25519.RISCV64.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X25519.RISCV64.Pass
public import VerifiedGarbage.Impl.Ed448.RISCV64.ScalarBase
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Proof.X448.RISCV64.Field
public import VerifiedGarbage.Proof.X448.RISCV64.Ladder
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Ed448's base-point multiplication on RISCV64: the whole function

`vg_ed448_scalar_base` writes the encoding of `[s]B` to `out`
(`scalarBase_correct`), given that the ladder `ladder2` over all 456 bits
encodes `[s]B` (`BaseLadder2Ok`, proven in `Proof/Ed448/Facts.lean` and passed
in by the registration).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (BITS X2 Z2)
open VG.Spec.X448 (Fe)
open VG.Spec.Ed448 (Point basePoint identity)

/-- `scalarBaseContract` by register: `out = a0`, `scalar = a1`,
`scratch = a2`. -/
def baseRISCV64 : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 57⟩
    let sc : Region := ⟨s.gpr .a1, 57⟩
    let ws : Region := ⟨s.gpr .a2, 8192⟩
    s.rd = [sc] ∧ s.wr = [out, ws] ∧ out.Disjoint sc ∧ out.Disjoint ws ∧ sc.Disjoint ws
  post s s' := Spec.Ed448.bytesAt s'.mem (s.gpr .a0) 57 =
    Spec.Ed448.scalarBase (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 57)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.sp = s₂.sp

section
variable {b : Addr}

/-- An element below `BITS` or above its 456 bytes stays through a write of them. -/
theorem fs_bits {m m' : Mem} (hf : Frame [⟨b + BitVec.ofNat 64 BITS, 456⟩] m m') {q : Nat}
    (hq : q + 56 ≤ BITS ∨ BITS + 456 ≤ q) (hq' : q + 56 ≤ 2048) : FS m' b q = FS m b q := by
  have hB : BITS = 1064 := rfl
  have e : ∀ k < 14, limb m' b q k = limb m b q k :=
    limb_frame hf fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by omega_using [hq, hk]) (by omega_using [hq', hk]) (by omega_using [hB])
  rw [FS, V, val32_congr e]; rfl

/-- The scalar, outside the working space, stays. -/
theorem bytesAt_ws {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {p : Addr}
    (hd : Region.Disjoint ⟨p, 57⟩ ⟨b, 2048⟩) (hrs : ∀ r ∈ rs, Region.Sub r ⟨b, 2048⟩) :
    Spec.Ed448.bytesAt m' p 57 = Spec.Ed448.bytesAt m p 57 := by
  simp only [Spec.Ed448.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf _ fun r hr hc => hd _ (Offset.contains_base _ (by omega) (by omega)) (hrs r hr _ hc)

end

theorem scalarBase_correct (hl : Proof.Ed448.BaseLadder2Ok) {s : State} (hp : baseRISCV64.pre s) :
    WP isa scalarBase s fun s' => baseRISCV64.post s s' := by
  obtain ⟨hrd, hwr, hos, how, hsw⟩ := hp
  have hB : BITS = 1064 := rfl
  obtain ⟨b, hb⟩ : ∃ b, b = Proof.Ed25519.RISCV64.base (s.gpr .a2) := ⟨_, rfl⟩
  have hsub : Region.Sub ⟨b, 2048⟩ ⟨s.gpr .a2, 8192⟩ := by
    have := Proof.Ed25519.RISCV64.base_sub (s.gpr .a2) (o := 0) (n := 2048) (by decide)
    rwa [BitVec.add_zero, ← hb] at this
  have hws : Region.Disjoint ⟨s.gpr .a1, 57⟩ ⟨b, 2048⟩ := hsw.sub_right hsub
  have hwo : Region.Disjoint ⟨b, 2048⟩ ⟨s.gpr .a0, 57⟩ := (how.sub_right hsub).symm
  have hwsr : (⟨s.gpr .a2, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  unfold scalarBase
  rw [show Impl.X448.RISCV64.align = Impl.X25519.RISCV64.align from rfl]
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_mv fun s1 u1 => WP.append (Proof.Ed25519.RISCV64.align_ok (q := s.gpr .a2) u1.gpr
    (by rw [u1.wr]; exact hwsr)) fun s1' ⟨hc1, hr1, hm1⟩ => WP.mono (initSlots_ok (b := b) (hb ▸ hc1))
    fun s2 ⟨hr2, hf2, hv2⟩ => ?_)
  have hr2' : Rest [.a3, .a4] s s2 := (u1.rest (by decide)).trans ((hr1.mono (by decide)).trans (hr2.mono (by decide)))
  have hc2 : Ctx b s2 := (hb ▸ hc1).of_rest hr2 (by decide)
  have hk2 : Spec.Ed448.bytesAt s2.mem (s.gpr .a1) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .a1) 57 := by
    rw [bytesAt_ws hf2 hws fun r hr => ?_, hm1, u1.mem]
    simp only [initQ, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Offset.sub_base _ (by decide)
  -- The scalar's bits.
  refine WP.seq (WP.mono (baseBits_ok hc2 (by rw [hr2'.gpr _ (by decide)])
    (by rw [hr2'.rd, hr2'.wr, hrd]; simp) hws) fun s3 ⟨hc3, hr3, hf3, hb3⟩ => ?_)
  rw [hk2] at hb3
  have fe : ∀ q ∈ initQ, FS s2.mem b q = Proof.X448.toFe (initVal q) := fun q hq => by
    rw [FS, hv2 q hq]
  have hS3 : SlotsOk s3.mem b RQ (ptV identity identity) := fun q hq => by
    simp only [RQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rw [fs_bits hf3 (by rcases hq with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hq with rfl | rfl | rfl | rfl <;> decide), fe q (by
        rcases hq with rfl | rfl | rfl | rfl <;> decide)]
    rcases hq with rfl | rfl | rfl | rfl <;>
      simp only [initVal, ptV, RX, RY, RZ, QX, QY, QZ, DK, PX, PY, PZ, X2, Z2, Nat.reduceEqDiff, ↓reduceIte,
        Proof.X448.toFe_self]
  have hQ3 : QOk b s3.mem := by
    refine ⟨?_, ?_, ?_⟩ <;>
      rw [fs_bits hf3 (by decide) (by decide), fe _ (by decide)] <;>
      simp only [initVal, RX, RY, RZ, QX, QY, QZ, X2, Z2, Nat.reduceEqDiff, ↓reduceIte, Proof.X448.toFe_self]
  -- The loop and the encoding.
  refine WP.seq (WP.mono (baseLoop_ok hc3 hb3 hQ3 hS3) fun s4 ⟨hst4, hc4, hS4⟩ => ?_)
  have h34 : s4.gpr .a0 = s.gpr .a0 := by
    rw [hst4.rest.gpr _ (by decide), hr3.gpr _ (by decide), hr2'.gpr _ (by decide)]
  refine WP.mono (baseEncode_ok hc4 h34 (by rw [hst4.rest.wr, hr3.wr, hr2'.wr, hwr]; simp) hwo hS4)
    fun s5 h5 => ?_
  show Spec.Ed448.bytesAt s5.mem (s.gpr .a0) 57 = _
  rw [h5, hl _ (Proof.Ed448.decodeLE_below (by simp [Spec.Ed448.bytesAt]))]
  rfl

end VG.Proof.Ed448.RISCV64
