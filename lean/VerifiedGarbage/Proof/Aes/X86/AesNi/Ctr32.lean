module

import VerifiedGarbage.Proof.Aes.X86.AesNi.Loops
import VerifiedGarbage.Proof.Aes.X86.AesNi.Restore
import VerifiedGarbage.Proof.Aes.X86.AesNi.CT
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Proof.Gcm.Contract
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Invariant
public import VerifiedGarbage.Proof.Aes.X86.Ctr32
import VerifiedGarbage.Proof.Aes.X86.AesNi.Prologue
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit

@[expose] public section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86
open VG.Proof.Aes.X86 (CPre GPre dstP ctrPost schP nRounds ctrP datP nBlk ctrSat)
open VG.Spec.Gcm (blockAt blocksAt)

/-- The invariant at exit is exactly the standard's CTR block list, from the
source to the destination. -/
theorem Inv.blocks_end {to : Bool} {s₀ s : State} (hI : Inv to s₀ (nBlk s₀) (nBlk s₀) s) :
    blocksAt s.mem ((dstP to s₀).setWidth 64) (nBlk s₀) =
      Spec.Gcm.ctr32 (ciph s₀) (cb s₀)
        (blocksAt s₀.mem ((datP s₀).setWidth 64) (nBlk s₀)) := by
  apply List.ext_getElem
  · simp [blocksAt, Spec.Gcm.ctr32, Spec.Gcm.keystream]
  · intro k h₁ h₂
    have hk : k < nBlk s₀ := by simpa [blocksAt] using h₁
    have hb := hI.blocks k hk
    simp only [hk, ite_true] at hb
    simp only [blocksAt, Spec.Gcm.ctr32, Spec.Gcm.keystream, List.getElem_map,
      List.getElem_range, List.getElem_zipWith, List.length_map, List.length_range]
    exact hb

/-- `edx` set for the loops: out of place, to the destination. -/
theorem setDst_ok {to : Bool} {s₀ s₁ : State} (hp : GPre to s₀) (hs : Start s₀ s₁) :
    WP isa (.block (Impl.Aes.X86.AesNi.setDst to)) s₁ fun s =>
      Inv to s₀ 0 0 s ∧ s.cf = some (decide (nBlk s₀ < 6)) := by
  cases to
  · exact WP.block_nil ⟨Inv.of_start hp hs (fun _ _ => rfl) hs.edx rfl rfl rfl, hs.cf⟩
  · refine Wp.cons (arg_exec hp hs.toSetup (i := 6) (.inr ⟨rfl, rfl⟩) .edx) (WP.block_nil ⟨?_, ?_⟩)
    · refine Inv.of_start hp hs (fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr) ?_ rfl rfl rfl
      rw [RegUpd.gpr_setReg_self]
      simp only [edxAt, ↓reduceIte, dstP, Nat.mul_zero, BitVec.add_zero]
    · rw [RegUpd.cf_setReg]; exact hs.cf

/-- The counter pointer back in `edx` for `restore`. -/
theorem setCtr_ok {to : Bool} {s₀ s : State} (hp : GPre to s₀) {c p : Nat} (hI : Inv to s₀ c p s) :
    WP isa (.block (Impl.Aes.X86.AesNi.setCtr to)) s fun s' =>
      s'.gpr .edx = ctrP s₀ ∧ (∀ r, r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  cases to
  · exact WP.block_nil ⟨hI.edx, fun _ _ => rfl, rfl, rfl, rfl⟩
  · refine Wp.cons (arg_exec' hp hI.esp hI.rd hI.frame (fun r hr => ?_) (i := 2) (.inl (by decide)) .edx)
      (WP.block_nil ⟨RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.aD
    · exact hp.aB

/-- Complete functional correctness and cdecl ABI preservation, in place
and out of place. -/
theorem correct {to : Bool} {s₀ : State} (hp : GPre to s₀) :
    WP isa (Impl.Aes.X86.AesNi.ctr32With to) s₀ fun s' =>
      abiPreserved s₀ s' ∧ ctrPost to s₀ s' := by
  unfold Impl.Aes.X86.AesNi.ctr32With
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (prologue_ok s₀ hp) fun s₁ hs => WP.mono (setDst_ok hp hs) fun s₂ ⟨hI, hcf⟩ => ?_
  refine loops_ok hp hI hcf _ fun s₃ hI₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (setCtr_ok hp hI₃) fun s₄ ⟨edx₄, g₄, m₄, rd₄, wr₄⟩ => ?_
  refine WP.mono (restore_ok hp (nBlk s₀) (by rw [m₄]; exact hI₃.saved) edx₄
    (by rw [g₄ _ (by decide)]; exact hI₃.ebp) (by rw [g₄ _ (by decide)]; exact hI₃.esp)
    (by rw [rd₄]; exact hI₃.rd) (by rw [wr₄]; exact hI₃.wr) (by rw [m₄]; exact hI₃.frame)
    (by rw [g₄ _ (by decide)]; exact hI₃.ebx)) fun s' ⟨habi, hctr, hdata, _, _⟩ => ?_
  exact ⟨habi, hdata.trans (by rw [m₄]; exact hI₃.blocks_end), hctr⟩

/-- `vg_aes_ctr32_to_aesni` in place. -/
theorem ctr32_correct (s : State) (hs : Proof.Aes.ctr32X86.pre s) :
    ∃ t s', Exec isa Impl.Aes.X86.AesNi.ctr32To s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.ctr32X86.post s s' :=
  have hp := CPre.of hs
  (correct hp.gpre).imp fun _ ⟨s', he, h, h₂, h₃⟩ =>
    ⟨s', he, h, by simpa only [ctrPost, dstP, ↓reduceIte, hp.same] using h₂, h₃⟩

theorem ctr32To_correct (s : State) (hs : Proof.Aes.ctr32ToX86.pre s) :
    ∃ t s', Exec isa Impl.Aes.X86.AesNi.ctr32To s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.ctr32ToX86.post s s' :=
  (correct (GPre.ofTo hs)).imp fun _ ⟨s', he, h⟩ => ⟨s', he, h⟩

end VG.Proof.Aes.X86.AesNi
