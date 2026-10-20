module

public import VerifiedGarbage.Proof.Modes.X86.Modes
public import VerifiedGarbage.Impl.Modes.Ctr
import VerifiedGarbage.Proof.Modes.CtrStep

@[expose] public section

namespace VG.Proof.Modes.X86

open VG VG.X86 VG.Impl.Modes VG.Impl.Modes.X86
open VG.Spec.Aes (bytesAt)

variable {c : Core} (cs : CoreSpec c) {s₀ : State} {k : cs.Key}

theorem ctr_wp (hbw : c.bw = 4) (hp : SeqPre c Mode.ctr s₀) (hk : cs.KeyArgs s₀ [scrR s₀ c] k) :
    WP isa (c.seq Mode.ctr) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem ((Dp s₀ c).setWidth 64) (N s₀ c) =
        Spec.Ctr.crypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem ((P s₀ c).setWidth 64) (4 * c.bw) = Spec.Ctr.next (iv0 c s₀) (N s₀ c) := by
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

end VG.Proof.Modes.X86
