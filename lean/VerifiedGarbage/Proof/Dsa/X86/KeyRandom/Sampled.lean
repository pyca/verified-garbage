module

public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Invoke
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Finish
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallArgs
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Sample
import VerifiedGarbage.Proof.Dsa.X86.RandomAttempt
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Result
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallResult

/-! # An accepted draw is derived once; exhaustion returns without derivation -/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.GenerateKey

theorem sampledWith_ok {I : State → Mem → Prop} (F : DeriveInvoke I) (stable : StableScratch I) {s₀ t : State} (A : KeyABI s₀) (hc : checked s₀ = true)
    (O : SampleOut s₀ 0 (draw s₀) t) (saved : Saved s₀ t.mem)
    (invariant : I s₀ t.mem)
    (eax : t.gpr .eax = BitVec.ofNat 32 (VG.Proof.Dsa.Random.sampleStatus (draw s₀))) :
    WP isa (sampledWith F.code) t (Fin s₀) := by
  obtain ⟨d, S⟩ := O.smp
  have h := S.ready
  have hql := rQBytes_le A
  have hle := sampleStatus_le (draw s₀)
  unfold sampledWith
  refine WP.seq (wp_cmpi fun u fv _ z => WP.block_nil ?_)
  have hu := h.fupd fv
  rw [eax, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq (by omega) (by decide)] at z
  have Su := S.mem A hu fv.mem
  cases hsc : (draw s₀).scalar with
  | none =>
    have hst : VG.Proof.Dsa.Random.sampleStatus (draw s₀) ≠ 1 := by
      simp only [VG.Proof.Dsa.Random.sampleStatus, hsc]; split <;> simp
    refine WP.ite false (by simp only [eval, z, hst, decide_false]) (fun e => Bool.noConfusion e)
      (fun _ => WP.block_nil ?_)
    have R := result_eq A
    simp only [hc, ite_true, hsc] at R
    refine ⟨hu, ?_, ?_, ?_, by rw [fv.mem]; exact saved⟩
    · rw [R]; simpa only [Nat.zero_add] using Su.usedW
    · rw [R, fv.mem]; exact O.status
    · rw [R]; intro e; exact (hst e).elim
  | some k =>
    have hst : VG.Proof.Dsa.Random.sampleStatus (draw s₀) = 1 := by
      simp only [VG.Proof.Dsa.Random.sampleStatus, hsc]
    refine WP.ite true (by simp only [eval, z, hst, decide_true]) (fun _ => ?_) (fun e => Bool.noConfusion e)
    refine WP.seq (?_ : WP isa (.block (deriveArgs ++ [])) u _)
    refine deriveArgs_ok A hu fun v hv mv kv => WP.block_nil ?_
    have ov := argsMem_outs s₀ u.mem (u.gpr .esp)
    rw [← mv] at ov
    have C : CallSlots s₀ v := fun i hi => by
      rw [mv, kv.1 .esp (by decide)]; exact argsMem_slots s₀ _ _ i hi
    have scalar : Spec.Rsa.bytesAt v.mem (off (rBase s₀) oNonce) (rQBytes s₀).length =
        Spec.Dsa.encodeBE (rQBytes s₀).length k := by
      rw [outs_frame_bytes ov (by decide) (by unfold oNonce; omega), fv.mem]
      exact O.nonce k hsc
    have result := callResult_eq A hv scalar
    have Iv : I s₀ v.mem := stable ov (by decide) (by rw [fv.mem]; exact invariant)
    refine WP.seq (WP.mono (F.correct A hv C hc Iv) fun w ⟨hw, fw, _, ew, bw⟩ => ?_)
    have Sw := (Su.after_args A hv ov).after_call A hw fw
    have savedW : Saved s₀ w.mem := saved.of_slots fun e he he' => by
      rw [call_frame_slot A fw he (by omega), outs_high ov (e := 44) (by decide) he (by omega), fv.mem]
    rw [result] at ew bw
    refine wp_slot hw.rf (by decide) ew fun sf rf mf gf rd wr _ _ => WP.block_nil ?_
    have K : Keeps [] w sf := ⟨fun r _ => by rw [gf], rd, wr⟩
    have frame : Frame [rStack s₀] w.mem sf.mem := by rw [mf]; exact frame_store s₀ _ (by decide) _
    have R := result_eq A
    simp only [hc, ite_true, hsc] at R
    refine ⟨hw.congr K frame, ?_, ?_, ?_, ?_⟩
    · rw [R, mf, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]
      simpa only [Nat.zero_add] using Sw.usedW
    · rw [R, mf, slot_write_self]
    · intro _
      rw [R]
      rw [rBytes_frame frame (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact A.stackOutWide.symm)
        (by have := A.outBound; omega)]
      exact bw
    · exact savedW.of_slots fun e he he' => by
        rw [mf, slot_write_ne _ _ _ (by unfold oStatus; omega) (by omega) (by unfold oStatus; omega)]

theorem sampled_ok (F : DeriveFn) {s₀ t : State} (A : KeyABI s₀) (hc : checked s₀ = true)
    (O : SampleOut s₀ 0 (draw s₀) t) (saved : Saved s₀ t.mem)
    (eax : t.gpr .eax = BitVec.ofNat 32 (VG.Proof.Dsa.Random.sampleStatus (draw s₀))) :
    WP isa (sampled F.name F.code) t (Fin s₀) :=
  sampledWith_ok F.invoke (fun _ _ _ => trivial) A hc O saved trivial eax

end VG.Proof.Dsa.X86.KeyRandom
