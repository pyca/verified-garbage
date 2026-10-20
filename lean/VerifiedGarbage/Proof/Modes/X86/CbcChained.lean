module

public import VerifiedGarbage.Proof.Modes.X86.Modes
public import VerifiedGarbage.Impl.Modes.CbcChained
import VerifiedGarbage.Proof.Modes.StepsChained

/-!
# CBC that updates the chaining value on x86 (32-bit), for any core

`seq_wp` for `Mode.cbcEncChained` and `Mode.cbcDecChained`: the data as
`Spec.Cbc.encrypt` and `Spec.Cbc.decrypt` under the core's cipher (as
`cbcEnc_wp` and `cbcDec_wp`), and the IV replaced with the chaining value to
continue from (`Spec.Cbc.next`).
-/

@[expose] public section

namespace VG.Proof.Modes.X86

open VG VG.X86 VG.Impl.Modes VG.Impl.Modes.X86
open VG.Spec.Aes (bytesAt)

variable {c : Core} (cs : CoreSpec c) {s₀ : State} {k : cs.Key}

theorem cbcEncChained_wp (hp : SeqPre c (Mode.cbcEncChained c.bw) s₀) (hk : cs.KeyArgs s₀ [scrR s₀ c] k) :
    WP isa (c.seq (Mode.cbcEncChained c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem ((Dp s₀ c).setWidth 64) (N s₀ c) =
        Spec.Cbc.encrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem ((P s₀ c).setWidth 64) (4 * c.bw) =
        Spec.Cbc.next (iv0 c s₀) (Spec.Cbc.encrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀)) := by
  have b := blk_bounds (c := c) (st := (Mode.cbcEncChained c.bw).step) rfl
  refine WP.mono (seq_wp cs hp (xorBlk_inBounds (b _) (b _) (b _))
    (fun o ho => (List.mem_append.mp ho).elim (copyBlk_inBounds (b _) (b _) o) (copyBlk_inBounds (b _) (b _) o))
    (cbcEncChained_computes (cs.cipher_len k)) hk) fun s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, ?_⟩
  · exact h2.trans (by rw [encrypt_run]; rfl)
  · rw [h3 rfl, encrypt_run_next]; rfl

theorem cbcDecChained_wp (hp : SeqPre c (Mode.cbcDecChained c.bw) s₀) (hk : cs.KeyArgs s₀ [scrR s₀ c] k) :
    WP isa (c.seq (Mode.cbcDecChained c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem ((Dp s₀ c).setWidth 64) (N s₀ c) =
        Spec.Cbc.decrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem ((P s₀ c).setWidth 64) (4 * c.bw) = Spec.Cbc.next (iv0 c s₀) (blocks0 (c := c) s₀) := by
  have b := blk_bounds (c := c) (st := (Mode.cbcDecChained c.bw).step) rfl
  refine WP.mono (seq_wp cs hp (copyBlk_inBounds (b _) (b _)) (fun o ho => ?_)
    (cbcDecChained_computes (cs.cipher_len k)) hk) fun s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, ?_⟩
  · simp only [Mode.cbcDecChained, Mode.cbcDec, List.mem_append] at ho
    rcases ho with (ho | ho) | ho
    · exact xorBlk_inBounds (b _) (b _) (b _) o ho
    · exact copyBlk_inBounds (b _) (b _) o ho
    · exact copyBlk_inBounds (b _) (b _) o ho
  · exact h2.trans (by rw [decrypt_run]; rfl)
  · rw [h3 rfl, decrypt_run_next]; rfl

end VG.Proof.Modes.X86
