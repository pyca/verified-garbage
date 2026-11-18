module

public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Invoke
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Finish
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Result
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Sample
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Copy
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallArgs
import VerifiedGarbage.Proof.Dsa.X86.RandomAttempt
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallResult
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.State
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.X86.GenerateKey
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckPre
public import VerifiedGarbage.Proof.Mont.Words32

/-! ### `Dsa.X86.KeyRandom.CheckFrame`, which the modules that import this one used -/

section

/-! ### `Dsa.X86.KeyRandom.CheckArgs`, which the modules that import this one used -/

section

/-! # The domain checker's six outgoing arguments -/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom.CheckCall
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.GenerateKey

def argsMem (s₀ : State) (m : Mem) : Mem :=
  ((((((m.writeW (off (rBase s₀) 0) (X86.arg s₀ 3)).writeW (off (rBase s₀) 4) (X86.arg s₀ 4)).writeW (off (rBase s₀) 8) (X86.arg s₀ 5)).writeW (off (rBase s₀) 12) (X86.arg s₀ 6)).writeW (off (rBase s₀) 16) (X86.arg s₀ 9)).writeW (off (rBase s₀) 20) (X86.arg s₀ 10))

theorem argsMem_slots (s₀ : State) (m : Mem) (sp : BitVec 32) :
    ∀ i < 6, slot (argsMem s₀ m) (rBase s₀) (4 * i) = callVal s₀ sp i := by
  intro i hi
  unfold argsMem
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ =>
    simp (disch := decide) only [slot_write_self, slot_write_ne, Nat.reduceMul, callVal]

theorem argsMem_outs (s₀ : State) (m : Mem) : Outs (rBase s₀) [(0, 24)] m (argsMem s₀ m) := by
  unfold argsMem
  have e := fun {m : Mem} {d : Nat} (v : BitVec 32) (h : d + 4 ≤ 24) =>
    KeyRandom.store_in (rBase s₀) m (rs := [(0, 24)]) (o := 0) (n := 24) (d := d) v
      (List.mem_singleton_self _) (Nat.zero_le _) h (by omega_using [h])
  exact (((((e _ (by decide)).trans (e _ (by decide))).trans (e _ (by decide))).trans
    (e _ (by decide))).trans (e _ (by decide))).trans (e _ (by decide))

theorem checkArgs_ok {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ u, Ready s₀ u → u.mem = argsMem s₀ t.mem → Keeps [.eax] t u → WP isa (.block is) u Q) :
    WP isa (.block (checkArgs ++ is)) t Q := by
  unfold checkArgs
  simp only [List.append_assoc]
  refine KeyRandom.copyArg_ok A h (by decide) (by decide) fun u1 h1 m1 k1 => ?_
  refine KeyRandom.copyArg_ok A h1 (by decide) (by decide) fun u2 h2 m2 k2 => ?_
  refine KeyRandom.copyArg_ok A h2 (by decide) (by decide) fun u3 h3 m3 k3 => ?_
  refine KeyRandom.copyArg_ok A h3 (by decide) (by decide) fun u4 h4 m4 k4 => ?_
  refine KeyRandom.copyArg_ok A h4 (by decide) (by decide) fun u5 h5 m5 k5 => ?_
  refine KeyRandom.copyArg_ok A h5 (by decide) (by decide) fun u6 h6 m6 k6 => ?_
  refine k u6 h6 ?_ ((((((k1).trans k2).trans k3).trans k4).trans k5).trans k6)
  rw [m6, m5, m4, m3, m2, m1]
  rfl

end VG.Proof.Dsa.X86.KeyRandom.CheckCall

end

end

/-! # The checker leaves the saved registers and consumption slots untouched -/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom.CheckCall
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom

/-- The frame above its argument words is apart from where the call writes. -/
theorem call_frame_byte {s₀ : State} (A : KeyABI s₀) {m m' : Mem} (hf : Frame (callWrites s₀) m m')
    {d : Nat} (h₁ : 44 ≤ d) (h₂ : d < 120) : m' (off (rBase s₀) d) = m (off (rBase s₀) d) := by
  rw [rBase_off, rLow_off]
  have hs : (rStack s₀).Contains (off (rCall s₀) (88 + (24 + d))) 1 :=
    Offset.contains_base _ (by omega_using [h₂]) (by omega_using [h₂])
  refine hf _ fun r hr => ?_
  simp only [callWrites, callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact A.stackScratchWide _ hs
  · rw [rLow_off]
    exact (Offset.disjoint (rCall s₀) (d := 88 + (24 + d)) (n := 1) (e := 88 + 24) (k := 24) (by omega_using [h₁])
      (by omega_using [h₂]) (by omega_using [])) _ (self_contains _)
  · exact (Offset.disjoint_base (rCall s₀) (d := 88 + (24 + d)) (n := 1) (k := 112) (by omega_using [])
      (by omega_using [h₂])) _ (self_contains _)

theorem call_frame_slot {s₀ : State} (A : KeyABI s₀) {m m' : Mem} (hf : Frame (callWrites s₀) m m')
    {d : Nat} (h₁ : 44 ≤ d) (h₂ : d + 4 ≤ 120) : slot m' (rBase s₀) d = slot m (rBase s₀) d :=
  Mem.readW_congr fun i hi => by
    have : i < 4 := hi
    rw [show off (rBase s₀) d + BitVec.ofNat 64 i = off (rBase s₀) (d + i) by
      rw [off, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]]
    exact call_frame_byte A hf (by omega_using [h₁]) (by omega_using [h₂, hi])

end VG.Proof.Dsa.X86.KeyRandom.CheckCall

end

end

/-! # Prepare and sample a private scalar after accepting the domain -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/KeyRandom/Sampled.lean`, which only this module imported.
section

/-! # An accepted draw is derived once; exhaustion returns without derivation -/

section
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

end VG.Proof.Dsa.X86.KeyRandom
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.GenerateKey

theorem generateWith_ok {I : State → Mem → Prop} (F : DeriveInvoke I) (stable : StableScratch I) {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t)
    (hc : checked s₀ = true) (saved : Saved s₀ t.mem) (used : slot t.mem (rBase s₀) oUsed = 0)
    (invariant : I s₀ t.mem) :
    WP isa (generateWith F.code) t (Fin s₀) := by
  have hq := checked_q hc
  have hql := rQBytes_le A
  have hfit := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  unfold generateWith
  refine WP.seq (WP.mono (prepare_ok A h) fun u ⟨ax, P, hu, ou, _⟩ => ?_)
  have low : ∀ d, d + 4 ≤ oQ → slot u.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd =>
    outs_low ou (by decide) hd (by unfold oQ at hd; omega_using [hd])
  refine WP.seq (wp_cmpi fun v fv _ z => WP.block_nil ?_)
  have hv := hu.fupd fv
  have savedV : Saved s₀ v.mem := by
    rw [fv.mem]; exact saved.of_slots fun d _ hd => low d (by unfold oQ; omega_using [hd])
  have usedV : slot v.mem (rBase s₀) oUsed = 0 := by rw [fv.mem, low _ (by decide)]; exact used
  have prepared := P hq
  rw [ax] at z
  change 1 < Spec.Dsa.decodeBE (rQBytes s₀) at hq
  simp only [hq, ite_true] at z
  refine WP.ite false (by simp only [eval, z]; rfl) (fun e => Bool.noConfusion e) (fun _ => ?_)
  have initial : Smp s₀ 0 (slot v.mem (rBase s₀) oDraws).toNat v := by
    refine ⟨hv, by rw [fv.mem]; exact prepared.q, by rw [fv.mem]; exact prepared.width,
      by rw [fv.mem]; exact prepared.mask, usedV, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq],
      fun i hi => by rw [fv.mem]; exact prepared.nonce i (by omega_using [hql, hi]), Nat.zero_le _⟩
  refine WP.seq (WP.mono (sample_ok A initial hq) fun w ⟨O, eax, _, ow, _⟩ => ?_)
  rw [← draw_spl] at O eax
  have Iv : I s₀ v.mem := by rw [fv.mem]; exact stable ou (by decide) invariant
  exact sampledWith_ok F stable A hc O (savedV.of_slots fun d _ hd => outs_low ow (by decide) hd (by omega_using [hd]))
    (stable ow (by decide) Iv) eax

end VG.Proof.Dsa.X86.KeyRandom
