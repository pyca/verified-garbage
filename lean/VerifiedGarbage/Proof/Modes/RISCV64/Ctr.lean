module

public import VerifiedGarbage.Proof.Modes.RISCV64.Modes
public import VerifiedGarbage.Impl.Modes.Ctr
import VerifiedGarbage.Proof.Modes.CtrStep

/-!
# Counter mode on RISCV64, for any core with 16-byte blocks

`ctr_wp`: `Mode.ctr`'s steps (`seq_wp`) over the core's cipher, with the
data and the counter block left as `Spec.Ctr.crypt` and `Spec.Ctr.next`
give them; `ctr_changes`: what it changes besides (`Changes`).
-/

@[expose] public section

namespace VG.Proof.Modes.RISCV64

open VG VG.RISCV64 VG.Impl.Modes VG.Impl.Modes.RISCV64
open VG.Spec.Aes (bytesAt)

variable {c : Core} (cs : CoreSpec c) {s₀ : State} {k : cs.Key}

theorem ctr_wp (hbw : c.bw = 4) (hp : SeqPre c Mode.ctr s₀) (hk : cs.KeyArgs s₀ (wrs0 c Mode.ctr s₀) k) :
    WP isa (c.seq Mode.ctr) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem (Dp s₀) (N s₀) =
        Spec.Ctr.crypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem (P s₀) (4 * c.bw) = Spec.Ctr.next (iv0 c s₀) (N s₀) := by
  have b := blk_bounds (c := c) (st := Mode.ctr.step) (by simp [Mode.ctr, hbw])
  have hc : ∀ x, (cs.cipher k x).length = 16 := by simpa [hbw] using cs.cipher_len k
  have hcomp : Computes Mode.ctr (4 * c.bw) (cs.cipher k) (ctrF (cs.cipher k)) := by
    simpa [hbw] using ctr_computes hc
  refine WP.mono (seq_wp cs hp (copyBlk_inBounds (by simpa [hbw] using b _) (by simpa [hbw] using b _))
    (fun o ho => ?_) hcomp hk) fun s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, ?_⟩
  · simp only [Mode.ctr, List.mem_append, List.mem_singleton] at ho
    rcases ho with ho | rfl
    · exact xorBlk_inBounds (by simpa [hbw] using b _) (by simpa [hbw] using b _)
        (by simpa [hbw] using b _) o ho
    · simp [Op.InBounds, Op.width, lens, Mode.ctr, hbw]
  · simpa [hbw, Mode.ctr, xs0, blocks0] using h2.trans (ctr_run _ _ _).1.symm
  · rw [h3 rfl, ← (ctr_run _ _ _).2, chunksAt_length]

theorem ctr_changes (hbw : c.bw = 4) (hp : SeqPre c Mode.ctr s₀) (hk : cs.KeyArgs s₀ (wrs0 c Mode.ctr s₀) k) :
    WP isa (c.seq Mode.ctr) s₀ (Changes c Mode.ctr s₀) := by
  have b := blk_bounds (c := c) (st := Mode.ctr.step) (by simp [Mode.ctr, hbw])
  have hc : ∀ x, (cs.cipher k x).length = 16 := by simpa [hbw] using cs.cipher_len k
  have hcomp : Computes Mode.ctr (4 * c.bw) (cs.cipher k) (ctrF (cs.cipher k)) := by
    simpa [hbw] using ctr_computes hc
  refine WP.mono (seq_changes_wp cs hp (copyBlk_inBounds (by simpa [hbw] using b _) (by simpa [hbw] using b _))
    (fun o ho => ?_) hcomp hk) fun _ h => h.2.2.2
  simp only [Mode.ctr, List.mem_append, List.mem_singleton] at ho
  rcases ho with ho | rfl
  · exact xorBlk_inBounds (by simpa [hbw] using b _) (by simpa [hbw] using b _)
      (by simpa [hbw] using b _) o ho
  · simp [Op.InBounds, Op.width, lens, Mode.ctr, hbw]

end VG.Proof.Modes.RISCV64
