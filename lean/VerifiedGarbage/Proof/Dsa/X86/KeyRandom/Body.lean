module

public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckFrame
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckArgs
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Entry
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Finish
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallResult
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Generate

/-! # The key-generation body checks before consuming randomness -/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.GenerateKey

theorem body_ok (C : CheckCall.CheckFn) (D : DeriveFn) {s₀ : State} (A : KeyABI s₀) :
    WP isa (body C.name D.name C.code D.code) (allocated KeyRandom.frameBytes s₀) (Finished s₀) := by
  have h0 := alloc_ready A
  unfold body
  refine WP.seq (WP.block_append (WP.mono (entry_ok h0 (allocated_gpr _ _ (by decide))
    (allocated_gpr _ _ (by decide)) (allocated_gpr _ _ (by decide)) (allocated_gpr _ _ (by decide)))
    fun t ⟨ht, saved, used, status, _⟩ => ?_))
  change WP isa (.block (checkArgs ++ [])) t _
  refine CheckCall.checkArgs_ok A ht fun u hu mu ku => WP.block_nil ?_
  have ou := CheckCall.argsMem_outs s₀ t.mem
  rw [← mu] at ou
  have slots : CheckCall.CallSlots s₀ u := fun i hi => by rw [mu]; exact CheckCall.argsMem_slots s₀ _ _ i hi
  refine WP.seq (WP.mono (CheckCall.call_ok C A hu slots) fun v ⟨hv, frame, _, eax⟩ => ?_)
  have low (d : Nat) (hd : 44 ≤ d) (hd' : d + 4 ≤ 120) :
      slot v.mem (rBase s₀) d = slot t.mem (rBase s₀) d := by
    rw [CheckCall.call_frame_slot A frame hd hd', outs_high ou (e := 44) (by decide) hd (by omega)]
  have savedV : Saved s₀ v.mem := saved.of_slots fun d hd hd' => low d hd (by omega)
  have usedV : slot v.mem (rBase s₀) oUsed = 0 := by rw [low _ (by decide) (by decide)]; exact used
  have statusV : slot v.mem (rBase s₀) oStatus = 0 := by rw [low _ (by decide) (by decide)]; exact status
  rw [checkResult_eq A hu] at eax
  refine WP.seq (wp_cmpi fun w fw _ zw => WP.block_nil ?_)
  have hw := hv.fupd fw
  have savedW : Saved s₀ w.mem := by rw [fw.mem]; exact savedV
  have usedW : slot w.mem (rBase s₀) oUsed = 0 := by rw [fw.mem]; exact usedV
  rw [eax] at zw
  by_cases valid : checked s₀ = true
  · simp only [valid, ite_true] at zw
    refine WP.seq (WP.ite false (by simp only [eval, zw]; rfl) (fun e => Bool.noConfusion e)
      (fun _ => WP.mono (generate_ok D A hw valid savedW usedW) fun sf F => ?_))
    exact finish_ok A F (result_status_le A) (result_key A)
  · simp only [valid] at zw
    refine WP.seq (WP.ite true (by simp only [eval, zw]; rfl) (fun _ => WP.block_nil ?_) (fun e => Bool.noConfusion e))
    have R := result_eq A
    simp only [valid] at R
    refine finish_ok A ⟨hw, ?_, ?_, ?_, savedW⟩ (result_status_le A) (result_key A)
    · rw [R]; exact usedW
    · rw [R, fw.mem]; exact statusV
    · rw [R]; intro e; contradiction

end VG.Proof.Dsa.X86.KeyRandom
