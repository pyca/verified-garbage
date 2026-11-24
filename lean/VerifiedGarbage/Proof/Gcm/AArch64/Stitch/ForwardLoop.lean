module

public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Forward
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.SealBuffers
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.Interleave
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.Block

-- separate module: The batch invariant and its induction do not depend on the ABI register save and restore used by ForwardCall.
@[expose] public section
namespace VG.Proof.Gcm.AArch64.Stitch
open VG VG.AArch64 VG.Impl.Gcm.AArch64.Stitch
open VG.Proof.Gcm.AArch64.Pmull (VOnly exec_rev64b)
open VG.Proof.Aes.AArch64.Aese (setV_v_self setV_v_of_ne)

abbrev cipherRegs : List VReg := [.v8,.v9,.v10,.v11,.v12,.v13,.v14,.v15]

private theorem cipherReg_inj : ∀ i ∈ List.range 8, ∀ j ∈ List.range 8, cipherReg i = cipherReg j → i = j := by
  decide

theorem capture_ok (s : State) : WP isa (.block capture) s fun t =>
    (∀ j < 8, t.v (cipherReg j) = VRevOp.eval .rev64b (s.v (breg j))) ∧ VOnly cipherRegs s t := by
  refine wp_range_flatMap (M := isa) (fun n t =>
    (∀ j < n, t.v (cipherReg j) = VRevOp.eval .rev64b (s.v (breg j))) ∧ VOnly cipherRegs s t)
    (f := fun j => [.vop (.rev .rev64b (cipherReg j) (breg j))]) ?_ 8 (Nat.le_refl _) s ?_
  · rintro i t hi ⟨hv, fr⟩
    have hm : cipherReg i ∈ cipherRegs := by unfold cipherReg; split <;> decide
    rw [WP.block_cons_iff]
    refine ⟨_, exec_rev64b _ _ _, WP.block_nil ⟨fun j hj => ?_, ?_⟩⟩
    · by_cases h : j = i
      · subst j
        rw [setV_v_self, fr.v _ (by unfold breg; split <;> decide)]
      · rw [setV_v_of_ne _ _ (fun e => h (cipherReg_inj j (by simp; omega) i (by simp; omega) e))]
        exact hv j (by omega)
    · exact ⟨fun r hr => (setV_v_of_ne _ _ (show r ≠ cipherReg i from fun e => hr (e.symm ▸ hm))).trans (fr.v r hr),
        fr.gpr, fr.mem, fr.rd, fr.wr, fr.sp⟩
  · exact ⟨fun _ h => by omega, VOnly.refl _ _⟩

/-- The seal invariant observes only the GHASH accumulator and its reduction
constant among the vector registers. -/
theorem SealInv.of_capture {s₀ s t : State} {c h : Nat} (hi : SealInv s₀ c h s)
    (fr : VOnly cipherRegs s t) : SealInv s₀ c h t where
  le := hi.le
  x9 := by rw [fr.gpr, hi.x9]
  x10 := by simpa only [State.read, fr.gpr] using hi.x10
  x11 := by rw [fr.gpr, hi.x11]
  x15 := by rw [fr.gpr, hi.x15]
  gpr := fun r hr => (congrFun fr.gpr r).trans (hi.gpr r hr)
  y := (fr.v _ (by decide)).trans hi.y
  cr := (fr.v _ (by decide)).trans hi.cr
  data := fr.mem ▸ hi.data
  frame := fr.mem ▸ hi.frame
  sp := fr.sp.trans hi.sp
  rd := fr.rd.trans hi.rd
  wr := fr.wr.trans hi.wr

/-- An intermediate buffer equality for the two reads of batch ciphertext. -/
theorem batch_read {s₀ t : State} {c : Nat} (hi : SealInv s₀ (c+1) c t)
    (hv : EncValues s₀ c t) (j : Nat) (hj : j < 8) :
    t.mem.read (t.gpr .x9 + BitVec.ofNat 64 (16*j)) 16 = t.v (breg j) := by
  apply Mem.read_eq_of_bytes
  intro k hk
  have hn := hi.le
  rw [hi.x9, Offset.add_add, Offset.add_add, show 128*c + (16*j + k) = 16*(8*c+j)+k by omega]
  rw [hi.data _ (by omega), ite_eq_left (by omega)]
  exact (BitVec.xor_comm _ _).trans (hv j hj k hk).symm

theorem capture_batch {s₀ s : State} {c : Nat} (hi : SealInv s₀ (c+1) c s) (hv : EncValues s₀ c s) :
    WP isa (.block capture) s fun t => SealInv s₀ (c+1) c t ∧ CipherBatch t := by
  refine WP.mono (capture_ok s) fun t ⟨hc, fr⟩ => ⟨hi.of_capture fr, fun j hj => ?_⟩
  rw [hc j hj, blkV, fr.mem, fr.gpr, batch_read hi hv j hj]

end VG.Proof.Gcm.AArch64.Stitch

namespace VG.Proof.Gcm.AArch64.Stitch
open VG VG.AArch64 VG.Impl.Gcm.AArch64.Stitch

private theorem of_equal_run {x y : List Instr} {s : State} {Q : State → Prop}
    (he : runBlock isa x s = runBlock isa y s) (h : WP isa (.block y) s Q) : WP isa (.block x) s Q := by
  apply WP.of_runBlock
  rw [he]
  exact VG.AArch64.Interleave.runBlock_of_WP h

private theorem parts_forward_run {s₀ s : State} (hp : SealToPre s₀) {h : Nat} (hh : h+1 < nb s₀)
    (hi : SealInv s₀ (h+1) h s) (cache : CipherBatch s) :
    runBlock isa (residentParts (rounds s₀)) s = runBlock isa (parts (rounds s₀) 128 .x15) s := by
  have hm := VG.Interleave.weaveG_merge (fuse (aesPart (rounds s₀) 128 .x15)) (ghPart.map fun i => [i])
  rw [fuse_flatten, flatten_singles] at hm
  have ho := VG.Interleave.run_merge hm (partsTo_indeps hp.rounds (.inr rfl)) (s := s) trivial
  change runBlock isa (parts (rounds s₀) 128 .x15) s = _ at ho
  rw [run_forwardParts_eq_seq hp.rounds, ho, VG.AArch64.Interleave.runBlock_append,
    VG.AArch64.Interleave.runBlock_append]
  obtain ⟨t, ht, _, _, fr⟩ := VG.AArch64.Interleave.runBlock_of_WP
    (aesToStep hp hi hh (show 128*h+128 = 128*(h+1) by omega) (by decide) (by decide))
  rw [ht, Option.bind_some, Option.bind_some]
  have g9 : t.gpr .x9 = s.gpr .x9 := fr.gpr _ (by decide)
  have g19 : t.gpr .x19 = s.gpr .x19 := fr.gpr _ (by decide)
  apply run_forwardGh
  · intro j hj
    rw [fr.v _ (by unfold cipherReg; split <;> decide), cache j hj]
    simp only [blkV, fr.mem, g9]
  · exact ghIn_at hp.toKPre.toM (g9.trans hi.x9) (by omega)
      (g19.trans (hi.gpr _ (notMem_kRegsT _ (by decide)))) (by rw [fr.rd, fr.wr, hi.rd, hi.wr])

private theorem advance_eq (xs : List Instr) : xs ++ ([.addImm .x .x15 .x15 128, .addImm .x .x9 .x9 128] : List Instr) ++
    ([.subImm .x .x11 .x11 1] : List Instr) = xs ++ adv true := by rw [List.append_assoc]; rfl

private theorem stepForward {s₀ s : State} (hp : SealToPre s₀) (gh : Gh8Ok) {h : Nat}
    (hh : h+1 < nb s₀) (hi : SealInv s₀ (h+1) h s) (cache : CipherBatch s) :
    WP isa (.block (residentParts (rounds s₀) ++ stores 128 ++ adv true ++ capture)) s
      fun t => SealInv s₀ (h+1+1) (h+1) t ∧ CipherBatch t := by
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun t => SealInv s₀ (h+1+1) (h+1) t ∧ EncValues s₀ (h+1) t)
    (of_equal_run (y := parts (rounds s₀) 128 .x15 ++ stores 128 ++ adv true) ?_ ?_) fun _ p =>
      capture_batch p.1 p.2
  · simp only [List.append_assoc, VG.AArch64.Interleave.runBlock_append, parts_forward_run hp hh hi cache]
  · exact encToBody_values hp gh hh (by omega) (by omega) (.inr rfl) hi
      (fun j hj => ciphertext_of_dataInvM hi.data (by omega) (by have := hi.le; omega))

private theorem firstForward {s₀ s : State} (hp : SealToPre s₀) (hi : SealInv s₀ 0 0 s) :
    WP isa (.block ((aesPart (rounds s₀) 0 .x15).flatMap lowerXor3 ++ stores 0 ++ ([.subImm .x .x11 .x11 1] : List Instr) ++ capture))
      s fun t => SealInv s₀ 1 0 t ∧ CipherBatch t := by
  rw [WP.block_append_iff]
  refine WP.mono (of_equal_run (y := aesPart (rounds s₀) 0 .x15 ++ stores 0 ++ [.subImm .x .x11 .x11 1])
    ?_ (firstTo_values hp hi)) fun _ p => capture_batch p.1 p.2
  simp only [List.append_assoc, VG.AArch64.Interleave.runBlock_append]
  rw [run_lowerXor3_block (aesPart (rounds s₀) 0 .x15) s]

private theorem lastForward {s₀ s : State} (hp : SealToPre s₀) (gh : Gh8Ok)
    (hi : SealInv s₀ (nb s₀) (nb s₀-1) s) (hc : CipherBatch s) :
    WP isa (.block (residentHash.flatMap lowerXor3 ++ ([.addImm .x .x15 .x15 128, .addImm .x .x9 .x9 128] : List Instr)))
      s (SealInv s₀ (nb s₀) (nb s₀)) := by
  refine of_equal_run ?_ (lastTo_ok hp gh hi)
  have h1 := hp.nb1
  have hgin := ghIn_at hp.toKPre.toM hi.x9 (by omega) (hi.gpr _ (notMem_kRegsT _ (by decide)))
    (by rw [hi.rd, hi.wr])
  simp only [VG.AArch64.Interleave.runBlock_append]
  rw [run_lowerXor3_block residentHash s, run_forwardGh hc hgin]

private def retained (s₀ : State) (c h : Nat) (s : State) : Prop := SealInv s₀ c h s ∧ CipherBatch s

theorem forwardLoop_ok {s₀ s : State} (hp : SealToPre s₀) (gh : Gh8Ok) (hi : SealInv s₀ 0 0 s) :
    WP isa (forwardLoop (rounds s₀)) s (SealInv s₀ (nb s₀) (nb s₀)) := by
  have h1 := hp.nb1
  have hn := hp.toKPre.toM.n16
  simp only [forwardLoop, advance_eq]
  refine WP.seq (WP.mono (firstForward hp hi) fun _ ⟨hI₁, cache⟩ => ?_)
  refine WP.seq (WP.mono (Q := retained s₀ (nb s₀) (nb s₀-1)) ?_ fun _ p => lastForward hp gh p.1 p.2)
  refine WP.ite (decide (nb s₀-1 = 0)) (VG.Proof.Aes.AArch64.Aese.eval_zero hI₁.x11 (by omega)) (fun h => ?_) (fun h => ?_)
  · have he : nb s₀ = 1 := by simp at h; omega
    exact WP.block_nil (by rw [he]; exact ⟨hI₁, cache⟩)
  · let I : Nat → State → Prop := fun m t => ∃ k, m = nb s₀ - (k+1) ∧ k+1 < nb s₀ ∧ retained s₀ (k+1) k t
    apply WP.loop (M := isa) I
    · rintro m t ⟨k, rfl, hk, inv, hc⟩
      refine WP.mono (stepForward hp gh hk inv hc) fun t ⟨inv', hc'⟩ => ?_
      have test : isa.eval (.nonzero .x .x11) t = some (!decide (nb s₀ - (k+1+1) = 0)) :=
        VG.Proof.Aes.AArch64.Aese.eval_nonzero inv'.x11 (by omega)
      rw [test]
      by_cases done_ : nb s₀ - (k + 1 + 1) = 0
      · have e : k+1+1 = nb s₀ := by omega
        exact .inl ⟨by simp [done_], by rw [← e, show k+1+1-1=k+1 by omega]; exact ⟨inv', hc'⟩⟩
      · exact .inr ⟨by simp [done_], nb s₀ - (k + 1 + 1), by omega, k+1, rfl, by omega, inv', hc'⟩
    · exact ⟨0, rfl, by simp at h; omega, hI₁, cache⟩

theorem forwardCore_ok {s₀ : State} (hp : SealToPre s₀) (gh : Gh8Ok) :
    WP isa (.seq (.block setup) (.seq (byRounds forwardLoop) (.block finish))) s₀ (SealToPost s₀) :=
  encLoopTo_ok hp forwardLoop fun _ hi => forwardLoop_ok hp gh hi

end VG.Proof.Gcm.AArch64.Stitch
