module

public import VerifiedGarbage.Proof.Modes.PPC64LE.Modes
import VerifiedGarbage.Proof.Modes.Ctr32Step
public import VerifiedGarbage.Impl.Modes.Ctr32
public import VerifiedGarbage.Proof.Modes.Ctr32
public import VerifiedGarbage.Proof.Modes.Steps

/-!
# Counter mode with GCM's `inc₃₂` on PPC64LE, for any core with 16-byte blocks

`ctr32_wp`: `Mode.ctr32`'s steps (`seq_wp`) over the core's cipher, with
the data and the counter block left as `Spec.Gcm.ctr32` and `inc₃₂ⁿ` give
them (`ctr32_gcm`).
-/

@[expose] public section

namespace VG.Proof.Modes.PPC64LE

open VG VG.PPC64LE VG.Impl.Modes VG.Impl.Modes.PPC64LE
open VG.Spec.Aes (bytesAt)

variable {c : Core} (cs : CoreSpec c) {s₀ : State} {k : cs.Key}

theorem ctr32_wp (hbw : c.bw = 4) (hp : SeqPre c Mode.ctr32 s₀) (hk : cs.KeyArgs s₀ (wrs0 c Mode.ctr32 s₀) k) :
    WP isa (c.seq Mode.ctr32) s₀ fun s' => abiPreserved s₀ s' ∧
      (chunksAt (4 * c.bw) s'.mem (Dp s₀) (N s₀)).map Spec.Gcm.ofBytes =
        Spec.Gcm.ctr32 (onBlocks (cs.cipher k)) (Spec.Gcm.ofBytes (iv0 c s₀))
          ((blocks0 (c := c) s₀).map Spec.Gcm.ofBytes) ∧
      Spec.Gcm.ofBytes (bytesAt s'.mem (P s₀) (4 * c.bw)) =
        Nat.repeat Spec.Gcm.inc32 (N s₀) (Spec.Gcm.ofBytes (iv0 c s₀)) := by
  have b := blk_bounds (c := c) (st := Mode.ctr32.step) (by simp [Mode.ctr32, hbw])
  have hc : ∀ x, (cs.cipher k x).length = 16 := by simpa [hbw] using cs.cipher_len k
  have hcomp : Computes Mode.ctr32 (4 * c.bw) (cs.cipher k) (ctr32F (cs.cipher k)) := by
    simpa [hbw] using ctr32_computes hc
  have ht : (iv0 c s₀).length = 16 := by simp [iv0, bytesAt, hbw]
  have hx : ∀ x ∈ blocks0 (c := c) s₀, x.length = 16 := by
    intro x hx
    simp only [blocks0, chunksAt, List.mem_map, List.mem_range] at hx
    obtain ⟨j, -, rfl⟩ := hx
    simp [bytesAt, hbw]
  obtain ⟨g1, g2⟩ := ctr32_gcm hc ht hx
  have e : xs0 Mode.ctr32 s₀ = blocks0 (c := c) s₀ := by simp [xs0, blocks0, Mode.ctr32, hbw]
  have es : Mode.ctr32.step = 4 * c.bw := by simp [Mode.ctr32, hbw]
  refine WP.mono (seq_wp cs hp (copyBlk_inBounds (by simpa [hbw] using b _) (by simpa [hbw] using b _))
    (fun o ho => ?_) hcomp hk) fun s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, ?_⟩
  · simp only [Mode.ctr32, List.mem_append, List.mem_singleton] at ho
    rcases ho with ho | rfl
    · exact xorBlk_inBounds (by simpa [hbw] using b _) (by simpa [hbw] using b _)
        (by simpa [hbw] using b _) o ho
    · simp [Op.InBounds, Op.width, lens, Mode.ctr32, hbw]
  · rw [← es, h2, e]; exact g1
  · rw [h3 rfl, e, g2, blocks0, chunksAt_length]

end VG.Proof.Modes.PPC64LE
