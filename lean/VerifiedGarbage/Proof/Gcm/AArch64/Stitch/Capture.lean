module

public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Forward
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.SealBuffers
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith

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
