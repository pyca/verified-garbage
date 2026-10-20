module
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeySample

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets

/-! # Key generation's public inputs, and what its leak fixes -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

structure KeygenPublicAgree (s t : State) : Prop where
  sp : s.sp = t.sp
  regs : ∀ r ∈ argRegs, s.gpr r = t.gpr r
  args : ∀ i < 3, stackArg s i = stackArg t i
  params : (keygenInput s).params = (keygenInput t).params

theorem KeygenPublicAgree.base {s t : State} (h : KeygenPublicAgree s t) : randomBase s = randomBase t := by
  unfold randomBase
  rw [h.sp]

theorem KeygenPublicAgree.pLen {s t : State} (h : KeygenPublicAgree s t) :
    (keygenInput s).pLen = (keygenInput t).pLen :=
  congrArg BitVec.toNat (h.regs .x5 (by decide))

theorem KeygenPublicAgree.qLen {s t : State} (h : KeygenPublicAgree s t) :
    (keygenInput s).qLen = (keygenInput t).qLen :=
  congrArg BitVec.toNat (h.regs .x6 (by decide))

theorem KeygenPublicAgree.checked {s t : State} (h : KeygenPublicAgree s t) : keygenChecked s = keygenChecked t := by
  unfold keygenChecked
  rw [h.pLen, h.qLen, h.params]

theorem KeygenPublicAgree.qBytes {s t : State} (h : KeygenPublicAgree s t) : keygenQBytes s = keygenQBytes t := by
  unfold keygenQBytes
  rw [h.pLen, h.qLen, h.params]

theorem keygen_public_related {extra : Nat} {s t : State}
    (h : (Spec.Dsa.generateKeyContract abi (extra + 256)).pub s t) :
    KeygenPublicAgree s t ∧ (keygenResult s).status = (keygenResult t).status ∧
      (keygenResult s).used = (keygenResult t).used ∧ (keygenResult s).trace = (keygenResult t).trace := by
  sig_pub [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, keygenStackArgs] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hleak, hdi, hsi, hdx, hcx, h8, h9, h6, h7, a0, a1, a2⟩ := h
  have hregs : ∀ r ∈ argRegs, s.gpr r = t.gpr r := by
    intro r hr
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hdi, hsi, hdx, hcx, h8, h9, h6, h7]
  have hargs : ∀ i < 3, stackArg s i = stackArg t i := by
    intro i hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hc with rfl | rfl | rfl
    exacts [a0, a1, a2]
  change ((keygenInput s).params.map (·.toNat) ++ [(keygenResult s).status, (keygenResult s).used] ++
      (keygenResult s).trace) = ((keygenInput t).params.map (·.toNat) ++
      [(keygenResult t).status, (keygenResult t).used] ++ (keygenResult t).trace) at hleak
  rw [List.append_assoc, List.append_assoc] at hleak
  have hlen : ((keygenInput s).params.map (·.toNat)).length = ((keygenInput t).params.map (·.toNat)).length := by
    simp only [keygenInput, List.length_map, bytesAt_length, h8]
  obtain ⟨hp, hrest⟩ := List.append_inj hleak hlen
  have hp' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hp
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hrest
  exact ⟨⟨hsp, hregs, hargs, hp'⟩, hrest⟩

theorem keygen_sample_trace_le (q fuel : Nat) (rand : List Byte) :
    ∀ x ∈ (Spec.Dsa.Random.sample q fuel rand).trace, x ≤ 4 := by
  induction fuel generalizing rand with
  | zero => simp [Spec.Dsa.Random.sample]
  | succ fuel ih =>
    rw [Spec.Dsa.Random.sample]
    split
    · simp
    · dsimp only
      split
      · simp
      · split
        · simp
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · decide
          · exact ih _ x hx

/-- The sampler's trace is the result's trace without the derivation's mark. -/
theorem keygen_draw_trace {extra : Nat} {s : State} (h : GenerateKeyABI extra s) (hc : keygenChecked s = true) :
    (keygenResult s).trace.filter (fun x => decide (x ≤ 4)) = (keygenDraw s).trace := by
  have hle := keygen_sample_trace_le (Spec.Dsa.decodeBE (keygenQBytes s)) 128 (keygenInput s).rand
  rw [keygen_result_checked h hc]
  cases (keygenDraw s).scalar with
  | none => exact List.filter_eq_self.mpr fun x hx => decide_eq_true (hle x hx)
  | some k =>
    dsimp only
    rw [List.filter_append, List.filter_eq_self.mpr fun x hx => decide_eq_true (hle x hx)]
    split <;> exact List.append_nil _

end VG.Proof.Dsa.AArch64
