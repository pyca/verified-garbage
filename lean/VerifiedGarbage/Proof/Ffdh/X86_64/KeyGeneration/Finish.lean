module
public import VerifiedGarbage.Impl.Ffdh.X86_64.KeyGeneration.Search
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Data
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.Table

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Outputs
import VerifiedGarbage.Proof.Framework.Offset

/-! # Returning from the key search: the octets consumed, the status and r12 -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

theorem KeyInput.used_scr {p : KeyPublic} {s : State} (h : KeyInput p s) {t : State}
    (hw : t.wr = s.wr) : Scr t p.up 8 := by
  refine Scr.of_mem (by rw [hw, h.1.2.2.2.1, ← h.2]; simp [inWrites, inUsed, keyOfState]) ?_
  rw [← h.2]
  exact h.nowrap (r := inUsed s) (by simp [inWrites])

/-- The word for the octets consumed is apart from the outputs and the
controller's words. -/
theorem KeyInput.used_disjoint {p : KeyPublic} {s : State} (h : KeyInput p s) :
    (⟨p.xp, p.len⟩ : Region).Disjoint ⟨p.up, 8⟩ ∧ (⟨p.yp, p.len⟩ : Region).Disjoint ⟨p.up, 8⟩ ∧
      (⟨p.control, 128⟩ : Region).Disjoint ⟨p.up, 8⟩ := by
  have hpw := h.writes_pairwise
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hrsi, hrcx, -, -, -, -, -⟩ := h.1
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hpw
  rw [← h.2]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [inX, inUsed, keyOfState, hrsi] using hpw.1.2.1
  · simpa only [inY, inUsed, keyOfState, hrcx] using hpw.2.1.1
  · simpa only [inUsed, inCtl, keyOfState] using hpw.2.2.1.2.symm

theorem key_finish_values {p : KeyPublic} {original s : State} {result : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original result s) :
    WP isa (.block finish) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 result.status ∧ t.gpr .r12 = original.gpr .r12 ∧
      t.mem = s.mem.writeW p.up (BitVec.ofNat 64 result.used) ∧
      Keep [.rax, .rcx, .rdx, .r12] s t := by
  have scr := h.input.control_scr (t := s) h.wr
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hup : InRegions s.wr p.up 8 := by
    simpa only [off, BitVec.add_zero] using (h.input.used_scr h.wr).st (d := 0) (by decide)
  refine WP.mono (WP.keep [.rax, .rcx, .rdx, .r12] (Q := fun t =>
    t.gpr .rax = BitVec.ofNat 64 result.status ∧ t.gpr .r12 = original.gpr .r12 ∧
    t.mem = s.mem.writeW p.up (BitVec.ofNat 64 result.used)) ?_ rfl)
    fun _ ⟨⟨ha, hr, hm⟩, k⟩ => ⟨ha, hr, hm, k⟩
  unfold finish
  xrun [State.ea, field, off, h.r12, h.usedPtr, h.used, h.status, h.savedR12,
    BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, hup,
    hl 120 (by decide), hl 88 (by decide), hl 112 (by decide), hl 32 (by decide)]

/-- What the search returns, for its result. -/
def KeyReturned (p : KeyPublic) (result : Spec.Ffdh.KeySearchResult) (t : State) : Prop :=
  ((t.gpr .rax).setWidth 32).toNat = result.status ∧ KeyOutput p result t.mem ∧
    Spec.Rsa.wordsAt t.mem p.control 4 = p.policy result ∧
    Spec.Rsa.wordsAt t.mem p.up 1 = [BitVec.ofNat 64 result.used]

theorem key_finish {p : KeyPublic} {original s : State} {result : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original result s) :
    WP isa (.block finish) s fun t => KeyReturned p result t ∧
      (∀ reg ∈ calleeSaved, t.gpr reg = original.gpr reg) ∧ t.rd = original.rd ∧ t.wr = original.wr := by
  refine WP.mono (key_finish_values h) fun t ⟨ha, hr12, hm, k⟩ => ?_
  have hd := h.input.used_disjoint
  have hk := h.input.len_lt
  have hf : Frame [⟨p.up, 8⟩] s.mem t.mem := by
    rw [hm]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hb : ∀ q : Addr, (⟨q, p.len⟩ : Region).Disjoint ⟨p.up, 8⟩ →
      Spec.Rsa.bytesAt t.mem q p.len = Spec.Rsa.bytesAt s.mem q p.len := by
    intro q hq
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hq)
      (show p.len ≤ 2 ^ 64 by omega) (List.mem_range.mp hi)
  have hc (j : Nat) (hj : j < 4) : word t.mem p.control (8 * j) = word s.mem p.control (8 * j) :=
    hf.readW (r := ⟨p.control, 128⟩)
      (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hd.2.2) (by decide)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, k.2.1.trans h.rd, k.2.2.trans h.wr⟩
  · rw [ha]
    have : result.status < 4 := by unfold Spec.Ffdh.KeySearchResult.status; split <;> decide
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · have ho := h.output
    unfold KeyOutput at ho ⊢
    rw [hb _ hd.1, hb _ hd.2.1]
    exact ho
  · have he : Spec.Rsa.wordsAt t.mem p.control 4 = Spec.Rsa.wordsAt s.mem p.control 4 := by
      change [word t.mem p.control 0, word t.mem p.control 8, word t.mem p.control 16,
        word t.mem p.control 24] = _
      rw [hc 0 (by decide), hc 1 (by decide), hc 2 (by decide), hc 3 (by decide)]
      rfl
    exact he.trans h.policy
  · change [word t.mem p.up 0] = [_]
    rw [hm]
    congr 1
    simpa only [Bignum.word, off, BitVec.add_zero] using
      Mem.readW_writeW_self64 s.mem p.up (BitVec.ofNat 64 result.used)
  · intro reg hreg
    by_cases he : reg = .r12
    · subst he; exact hr12
    · exact (k.gpr (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
        rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact (he rfl).elim | decide)).trans (h.saved reg hreg he)

end VG.Proof.Ffdh.X86_64.KeyGeneration
