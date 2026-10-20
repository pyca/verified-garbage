module
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawSample
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TapeHead

/-! # FFDH parameter generation on x86-64: checked draw or tape exhaustion -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

def drawValue (p : WitnessParams) (bs : List Byte) : Nat :=
  Spec.Rsa.os2ip (bs.take p.len) % 2 ^ p.bits

def DrawStep (p : WitnessParams) (rp : Addr) (used : Nat) (bs : List Byte) (s t : State) : Prop :=
  (if p.len ≤ bs.length then
    DrawState p (off rp p.len) (used + p.len) (bs.drop p.len) t ∧
      wv t.mem p.I (slot p.w aXm) p.w = drawValue p bs ∧
      t.zf = some (!decide (2 ≤ drawValue p bs ∧ drawValue p bs < p.N - 1)) ∧
      word t.mem p.O (8 * oStatus) = 1
   else DrawState p rp used bs t ∧ t.zf = some false ∧ word t.mem p.O (8 * oStatus) = 0) ∧
    DrawSaved p s.mem t.mem ∧ DrawFrame p s.mem t.mem ∧ Keep mmRegs s t

theorem drawBody_ok {p : WitnessParams} {rp : Addr} {used : Nat} {bs : List Byte} {s : State}
    (h : DrawState p rp used bs s) : WP isa drawBody s (DrawStep p rp used bs s) := by
  have houter : Scr s p.O 256 := by
    simpa [off] using h.scr.sub (o := 0) (n := 256) p.space_bounds.1 (by decide)
  unfold drawBody
  refine WP.seq (WP.mono (drawHead_ok h.ready.good.scr p.space_bounds.2.1 houter h.ready.good.rdi
    h.link h.left h.len (by omega_using [h.countBound]) (by omega_using [p.width_bounds.2.2.2.1]))
    fun u ⟨hcf, hm, k⟩ => ?_)
  have hu := h.same_mem hm k ((k.gpr (by decide)).trans h.ready.good.rdi)
  by_cases havail : p.len ≤ bs.length
  · refine WP.ite false (by simp [eval, hcf, show ¬bs.length < p.len by omega]) (by simp) (fun _ => ?_)
    refine WP.mono (drawSample_ok hu havail) fun t ⟨ht, hx, hz, hs, hh, hf, kt⟩ => ?_
    simp only [DrawStep, ite_eq_left havail]
    refine ⟨⟨ht, hx, hz, hs⟩, ?_, ?_, (k.trans kt).mono (by decide)⟩
    · intro j hj h12 h13 h14 h19
      rw [hh j hj h19, advanceMem_saved _ _ _ _ _ _ j hj h12 h13 h14, hm]
    · rw [← hm]; exact hf
  · have hshort : bs.length < p.len := by omega
    refine WP.ite true (by simp [eval, hcf, hshort]) (fun _ => ?_) (by simp)
    have houteru : Scr u p.O 256 := houter.congr k.2.2
    refine WP.mono (drawShort_ok hu.ready.good.scr p.space_bounds.2.1 houteru hu.ready.good.rdi hu.link)
      fun t ⟨hmt, hz, kt⟩ => ?_
    obtain ⟨ht, _, hh, hf⟩ := hu.status_write (0#64) hmt kt ((kt.gpr (by decide)).trans hu.ready.good.rdi)
    simp only [DrawStep, ite_eq_right havail]
    refine ⟨⟨ht, hz, ?_⟩, ?_, ?_, (k.trans kt).mono (by decide)⟩
    · rw [hmt]; exact word_writeW_self _ _ _ _
    · intro j hj _ _ _ h19
      rw [hh j hj h19, hm]
    · rw [← hm]; exact hf

end VG.Proof.Ffdh.X86_64.ParameterCandidate
