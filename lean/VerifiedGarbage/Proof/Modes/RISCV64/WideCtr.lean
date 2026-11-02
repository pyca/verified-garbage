module
-- separate module: batched counter mode on every RISC-V core, apart from the batched decryptions of `Wide.lean`

public import VerifiedGarbage.Proof.Modes.RISCV64.Wide
public import VerifiedGarbage.Proof.Modes.WideCtr
public import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.Modes.Ctr32

/-!
# Counter mode on RISC-V, a group of blocks at a time, for any core

`ctrWide_wp`, `ctr32Wide_wp`: `Core.seq2` over counter mode with the counter
block stepped before the block cipher, `2 ^ lg` blocks a step
(`Mode.ctrWide`, `Mode.ctr32Wide`) while that many are left, then one
(`Mode.ctrEarly`, `Mode.ctr32Early`), with the conclusions of `ctr_wp` and
`ctr32_wp` (`Ctr.lean`, `Ctr32.lean`). Their steps are those of
`ctrEarlyWide_loops`, from `ctrWide_computes` and `ctrEarly_computes`
(`Proof/Modes/WideCtr.lean`).
-/

@[expose] public section

namespace VG.Proof.Modes.RISCV64

open VG VG.RISCV64 VG.Impl.Modes VG.Impl.Modes.RISCV64
open VG.Spec.Aes (bytesAt)

variable {c : Core} (cs : CoreSpec c) {s₀ : State} {k : cs.Key} {lg : Nat}

/-- The loops of `seq2` over counter mode with the counter block stepped by
`o` before the block cipher. -/
theorem ctrEarlyWide_loops {o : Op} {g : List Byte → List Byte} (hbw : c.bw = 4) (hg : IncOp o g)
    (hsh : ∀ L st j, Op.shift L st j o = o) (hgl : ∀ c, c.length = 16 → (g c).length = 16)
    (ho : ∀ len : Loc → Nat, 16 ≤ len .chn → o.InBounds len)
    (hlg : lg ≤ 11) (hG : 2 ^ lg ≤ c.G) (hstle : 2 ^ lg * 16 ≤ 2032) :
    LoopsOk cs (Mode.ctrEarlyWith o) (ctrStep (cs.cipher k) g) s₀ k
      (.seq (c.loopWide (Mode.widen (2 ^ lg) 16 (Mode.ctrEarlyWith o)) lg) (c.steps (Mode.ctrEarlyWith o))) := by
  have e4 : 4 * c.bw = 16 := by rw [hbw]
  have hc : ∀ x, (cs.cipher k x).length = 16 := fun x => by rw [cs.cipher_len, e4]
  obtain ⟨hw1, hw2⟩ := ctrWide_inBounds (len := lens c (2 ^ lg * 16) (4 * c.bw * 2 ^ lg)) hsh
    (ho _ (by simp [lens, e4])) (2 ^ lg) (by simp [lens, Nat.mul_comm]) (by simp [lens, e4])
    (by simp [lens, e4])
  obtain ⟨hn1, hn2⟩ := ctrEarly_inBounds (len := lens c 16 (4 * c.bw)) (ho _ (by simp [lens, e4]))
    (by simp [lens]) (by simp [lens, e4]) (by simp [lens, e4])
  have hcw := ctrWide_computes hc hg hsh hgl (2 ^ lg)
  have hB := bufCipher_blocks (c := c) (ciph := cs.cipher k) hG
  rw [e4] at hB
  refine wideSteps_ok cs hlg hG rfl hstle hw1 hw2 (by rw [e4]; exact hcw) (by rw [e4]; exact hB)
    (by rw [e4]; exact ctrStep_blockwise hc hgl) hn1 hn2 (by rw [e4]; exact ctrEarly_computes hc hg hgl)

/-- Counter mode, `2 ^ lg` blocks at a time. -/
theorem ctrWide_wp (hbw : c.bw = 4) (hlg : lg ≤ 11) (hG : 2 ^ lg ≤ c.G) (hstle : 2 ^ lg * 16 ≤ 2032)
    (hp : SeqPre c Mode.ctrEarly s₀) (hk : cs.KeyArgs s₀ (wrs0 c Mode.ctrEarly s₀) k) :
    WP isa (c.seq2 (Mode.ctrWide (2 ^ lg)) Mode.ctrEarly lg) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem (Dp s₀) (N s₀) =
        Spec.Ctr.crypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem (P s₀) (4 * c.bw) = Spec.Ctr.next (iv0 c s₀) (N s₀) ∧
      Changes c Mode.ctrEarly s₀ s' :=
  WP.mono (seq2_changes_wp cs hp (ctrEarlyWide_loops cs hbw incOp_ctr (fun _ _ _ => rfl) inc_length
    (fun len h => ⟨by simpa [Op.width, Mode.ctrInc] using h, by simpa [Op.width, Mode.ctrInc] using h,
      fun _ _ h => by cases h⟩) hlg hG hstle) hk) fun s' ⟨h1, h2, h3, h4⟩ =>
    ⟨h1, by simpa [hbw, Mode.ctrEarly, Mode.ctrEarlyWith, xs0, blocks0, ← ctrF_eq] using
        h2.trans (ctr_run _ _ _).1.symm,
      by rw [h3 rfl, ← ctrF_eq, ← (ctr_run _ _ _).2, xs0, chunksAt_length], h4⟩

/-- Counter mode with GCM's `inc₃₂`, `2 ^ lg` blocks at a time. -/
theorem ctr32Wide_wp (hbw : c.bw = 4) (hlg : lg ≤ 11) (hG : 2 ^ lg ≤ c.G) (hstle : 2 ^ lg * 16 ≤ 2032)
    (hp : SeqPre c Mode.ctr32Early s₀) (hk : cs.KeyArgs s₀ (wrs0 c Mode.ctr32Early s₀) k) :
    WP isa (c.seq2 (Mode.ctr32Wide (2 ^ lg)) Mode.ctr32Early lg) s₀ fun s' => abiPreserved s₀ s' ∧
      (chunksAt (4 * c.bw) s'.mem (Dp s₀) (N s₀)).map Spec.Gcm.ofBytes =
        Spec.Gcm.ctr32 (onBlocks (cs.cipher k)) (Spec.Gcm.ofBytes (iv0 c s₀))
          ((blocks0 (c := c) s₀).map Spec.Gcm.ofBytes) ∧
      Spec.Gcm.ofBytes (bytesAt s'.mem (P s₀) (4 * c.bw)) =
        Nat.repeat Spec.Gcm.inc32 (N s₀) (Spec.Gcm.ofBytes (iv0 c s₀)) ∧
      Changes c Mode.ctr32Early s₀ s' := by
  have hc : ∀ x, (cs.cipher k x).length = 16 := by simpa [hbw] using cs.cipher_len k
  have ht : (iv0 c s₀).length = 16 := by simp [iv0, bytesAt, hbw]
  have hx : ∀ x ∈ blocks0 (c := c) s₀, x.length = 16 := by
    intro x hx
    simp only [blocks0, chunksAt, List.mem_map, List.mem_range] at hx
    obtain ⟨j, -, rfl⟩ := hx
    simp [bytesAt, hbw]
  obtain ⟨g1, g2⟩ := ctr32_gcm hc ht hx
  have e : xs0 Mode.ctr32Early s₀ = blocks0 (c := c) s₀ := by
    simp [xs0, blocks0, Mode.ctr32Early, Mode.ctrEarlyWith, hbw]
  have es : Mode.ctr32Early.step = 4 * c.bw := by simp [Mode.ctr32Early, Mode.ctrEarlyWith, hbw]
  refine WP.mono (seq2_changes_wp cs hp (ctrEarlyWide_loops cs hbw incOp_ctr32 (fun _ _ _ => rfl) inc32B_length
    (fun len h => ⟨by simp [Op.width, Mode.ctr32Inc]; omega, by simp [Op.width, Mode.ctr32Inc]; omega,
      fun _ _ h => by cases h⟩) hlg hG hstle) hk) fun s' ⟨h1, h2, h3, h4⟩ => ⟨h1, ?_, ?_, h4⟩
  · rw [← es, h2, e, ← ctr32F_eq]; exact g1
  · rw [h3 rfl, e, ← ctr32F_eq, g2, blocks0, chunksAt_length]

end VG.Proof.Modes.RISCV64
