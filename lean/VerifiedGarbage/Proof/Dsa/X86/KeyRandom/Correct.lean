module

public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Finish
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckInvoke
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Invoke

import VerifiedGarbage.Proof.Dsa.X86.RandomSignCorrect
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckFrame
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckArgs
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Entry
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallResult
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Generate
/-!
# The key generator meets its contract (x86)

`code` reserves its frame and runs the body (`body_ok`): on return the
callee-saved registers and the return address are as on entry, and the
status, `out` and `used` are those of `Spec.Dsa.generateKeyBytes`.
-/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/KeyRandom/Body.lean`, which only this module imported.
section

/-! # The key-generation body checks before consuming randomness -/

section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.GenerateKey

theorem bodyWith_ok {I : State → Mem → Prop} (C : CheckInvoke I) (D : DeriveInvoke I) (stable : StableScratch I) {s₀ : State} (A : KeyABI s₀) :
    WP isa (bodyWith C.code D.code) (allocated KeyRandom.frameBytes s₀) (Finished s₀) := by
  have h0 := alloc_ready A
  unfold bodyWith
  refine WP.seq (WP.block_append (WP.mono (entry_ok h0 (allocated_gpr _ _ (by decide))
    (allocated_gpr _ _ (by decide)) (allocated_gpr _ _ (by decide)) (allocated_gpr _ _ (by decide)))
    fun t ⟨ht, saved, used, status, _⟩ => ?_))
  change WP isa (.block (checkArgs ++ [])) t _
  refine CheckCall.checkArgs_ok A ht fun u hu mu ku => WP.block_nil ?_
  have ou := CheckCall.argsMem_outs s₀ t.mem
  rw [← mu] at ou
  have slots : CheckCall.CallSlots s₀ u := fun i hi => by rw [mu]; exact CheckCall.argsMem_slots s₀ _ _ i hi
  refine WP.seq (WP.mono (C.correct A hu slots) fun v ⟨hv, frame, _, eax, invariant⟩ => ?_)
  have low (d : Nat) (hd : 44 ≤ d) (hd' : d + 4 ≤ 120) :
      slot v.mem (rBase s₀) d = slot t.mem (rBase s₀) d := by
    rw [CheckCall.call_frame_slot A frame hd hd', outs_high ou (e := 44) (by decide) hd (by omega)]
  have savedV : Saved s₀ v.mem := saved.of_slots fun d hd hd' => low d hd (by omega)
  have usedV : slot v.mem (rBase s₀) oUsed = 0 := by rw [low _ (by decide) (by decide)]; exact used
  have statusV : slot v.mem (rBase s₀) oStatus = 0 := by rw [low _ (by decide) (by decide)]; exact status
  rw [checkResult_eq A hu] at eax invariant
  refine WP.seq (wp_cmpi fun w fw _ zw => WP.block_nil ?_)
  have hw := hv.fupd fw
  have savedW : Saved s₀ w.mem := by rw [fw.mem]; exact savedV
  have usedW : slot w.mem (rBase s₀) oUsed = 0 := by rw [fw.mem]; exact usedV
  rw [eax] at zw
  by_cases valid : checked s₀ = true
  · simp only [valid, ite_true] at zw
    refine WP.seq (WP.ite false (by simp only [eval, zw]; rfl) (fun e => Bool.noConfusion e)
      (fun _ => WP.mono (generateWith_ok D stable A hw valid savedW usedW (by rw [fw.mem]; exact invariant valid)) fun sf F => ?_))
    exact finish_ok A F (result_status_le A) (result_key A)
  · simp only [valid] at zw
    refine WP.seq (WP.ite true (by simp only [eval, zw]; rfl) (fun _ => WP.block_nil ?_) (fun e => Bool.noConfusion e))
    have R := result_eq A
    simp only [valid] at R
    refine finish_ok A ⟨hw, ?_, ?_, ?_, savedW⟩ (result_status_le A) (result_key A)
    · rw [R]; exact usedW
    · rw [R, fw.mem]; exact statusV
    · rw [R]; intro e; contradiction

theorem body_ok (C : CheckCall.CheckFn) (D : DeriveFn) {s₀ : State} (A : KeyABI s₀) :
    WP isa (body C.name D.name C.code D.code) (allocated KeyRandom.frameBytes s₀) (Finished s₀) :=
  bodyWith_ok C.invoke D.invoke (fun _ _ _ => trivial) A

end VG.Proof.Dsa.X86.KeyRandom
end

end

@[expose] public section

namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.GenerateKey

theorem bodyWith_noSp (check derive : Prog isa) (C : NoSp check) (D : NoSp derive) : NoSp (bodyWith check derive) := by
  unfold bodyWith generateWith sampledWith
  exact .seq' (.of_all (by decide +kernel)) (.seq' C
    (.seq' (.of_all (by decide +kernel)) (.seq'
      (.ite' (.of_all (by decide +kernel))
        (.seq' (.of_all (by decide +kernel)) (.seq' (.of_all (by decide +kernel))
          (.ite' (.of_all (by decide +kernel))
            (.seq' (.of_all (by decide +kernel)) (.seq' (.of_all (by decide +kernel))
              (.ite' (.seq' (.of_all (by decide +kernel)) (.seq' D (.of_all (by decide +kernel))))
                (.of_all (by decide +kernel)))))))))
      (.of_all (by decide +kernel)))))

theorem codeWith_ok {I : State → Mem → Prop} (C : CheckInvoke I) (D : DeriveInvoke I)
    (stable : StableScratch I) (nc : NoSp C.code) (nd : NoSp D.code) {s₀ : State} (A : KeyABI s₀) :
    WP isa (codeWith C.code D.code) s₀ fun s' => ∃ u, Finished s₀ u ∧ s' = freed KeyRandom.frameBytes u :=
  WP.alloc ⟨by decide, by decide, by decide⟩ (by have := A.stackLow; unfold KeyRandom.frameBytes; omega)
    (bodyWith_noSp C.code D.code nc nd) (WP.mono (bodyWith_ok C D stable A) fun u hu => ⟨u, hu, rfl⟩)

theorem body_noSp (C : CheckCall.CheckFn) (D : DeriveFn) : NoSp (body C.name D.name C.code D.code) :=
  bodyWith_noSp _ _ (.call' C.noSp) (.call' D.noSp)

theorem code_ok (C : CheckCall.CheckFn) (D : DeriveFn) {s₀ : State} (A : KeyABI s₀) :
    WP isa (code C.name D.name C.code D.code) s₀ fun s' => ∃ u, Finished s₀ u ∧ s' = freed KeyRandom.frameBytes u :=
  codeWith_ok C.invoke D.invoke (fun _ _ _ => trivial) (.call' C.noSp) (.call' D.noSp) A

theorem freed_esp_eq {s₀ u : State} (A : KeyABI s₀) (h : Ready s₀ u) :
    (freed KeyRandom.frameBytes u).gpr .esp = s₀.gpr .esp := by
  rw [freed_esp]
  have h1 := h.rf.esp
  rw [← alloc_base A] at h1
  have e : u.gpr .esp = s₀.gpr .esp - BitVec.ofNat 32 KeyRandom.frameBytes := by
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h1
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide : 2 ^ 32 ≤ 2 ^ 64)),
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide : 2 ^ 32 ≤ 2 ^ 64))] at this
    exact this
  rw [e, BitVec.sub_add_cancel]

/-- `vg_dsa_generate_key` meets its contract. -/
theorem generateKeyWith_correct {I : State → Mem → Prop} (C : CheckInvoke I) (D : DeriveInvoke I)
    (stable : StableScratch I) (nc : NoSp C.code) (nd : NoSp D.code) (s : State) (hpre : (Spec.Dsa.generateKeyContract abi 232).pre s) :
    ∃ t s', Exec isa (codeWith C.code D.code) s t s' ∧ abiPreserved s s' ∧
      (Spec.Dsa.generateKeyContract abi 232).post s s' := by
  have A := keyABI_of hpre
  obtain ⟨t, s', he, u, hF, rfl⟩ := codeWith_ok C D stable nc nd A
  refine ⟨t, _, he, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [freed_gpr _ _ (by decide)]; exact hF.ebx
    · rw [freed_gpr _ _ (by decide)]; exact hF.esi
    · rw [freed_gpr _ _ (by decide)]; exact hF.edi
    · rw [freed_gpr _ _ (by decide)]; exact hF.ebp
    · exact freed_esp_eq A hF.ready
  · show u.mem.readW _ 32 = _
    have hs := A.stackLow
    refine hF.ready.frame.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩)
      (by have := Offset.contains_base ((s.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide)
            (by decide)
          rwa [BitVec.add_zero] at this) (fun r hr => ?_) (by decide)
    simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.base_disjoint_below _ (by decide)
    · exact A.retOut
    · exact A.retScratch
    · exact A.retUsed
  · sig_post [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argSlots, argVal, argBytes, stackBelow]
    have hle := result_status_le A
    have hul : (rResult s).used < 2 ^ 32 := by
      have := result_used_le A
      have : (rInput s).rand.length < 2 ^ 32 := by simp only [rInput, rBytes_length]; exact BitVec.isLt _
      omega
    refine ⟨?_, hF.out, ?_⟩
    · rw [BitVec.setWidth_append_eq_right]
      show (u.gpr .eax).toNat = (rResult s).status
      rw [hF.eax, toNat_ofNat_lt (by omega)]
    · show Spec.Rsa.wordsAt u.mem (argumentPointer s 2) 1 = [BitVec.ofNat 64 (rResult s).used]
      simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero]
      refine congrArg (· :: []) (BitVec.eq_of_toNat_eq ?_)
      have := word_eq_w32 u.mem (argumentPointer s 2) 0
      simp only [Mont.word, w32, off] at this
      show (u.mem.readW (argumentPointer s 2 + BitVec.ofNat 64 0) 64).toNat = _
      rw [this, show (0 + 4 : Nat) = 4 from rfl]
      have lo : (u.mem.readW (argumentPointer s 2 + BitVec.ofNat 64 0) 32) = _ := hF.usedLo
      have hi : (u.mem.readW (argumentPointer s 2 + BitVec.ofNat 64 4) 32) = _ := hF.usedHi
      rw [lo, hi, toNat_ofNat_lt hul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rfl

theorem generateKey_correct (C : CheckCall.CheckFn) (D : DeriveFn) (s : State) (hpre : (Spec.Dsa.generateKeyContract abi 232).pre s) :
    ∃ t s', Exec isa (code C.name D.name C.code D.code) s t s' ∧ abiPreserved s s' ∧
      (Spec.Dsa.generateKeyContract abi 232).post s s' :=
  generateKeyWith_correct C.invoke D.invoke (fun _ _ _ => trivial) (.call' C.noSp) (.call' D.noSp) s hpre

end VG.Proof.Dsa.X86.KeyRandom
