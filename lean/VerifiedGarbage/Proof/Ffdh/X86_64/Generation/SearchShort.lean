module
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchDone

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRequestDone
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchExhausted
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchMemory
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRestore
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout

/-! # Entropy exhaustion and bounded native refill requests -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem short_guard {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    WP isa (.block [.mov .rax (.mem (field 11)), .alu .cmp .rax (.mem (field 2))]) s fun t =>
      SearchLive p original used remaining t ∧ t.mem = s.mem ∧
      t.gpr .rax = BitVec.ofNat 64 (p.c.rand.length - used) ∧
      eval .ae t = some (decide (Spec.Ffdh.parameterEntropy p.c.bits ≤ p.c.rand.length - used)) := by
  have scr := h.input.control_scr h.wr
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hv11 : word s.mem p.control 88 = BitVec.ofNat 64 (p.c.rand.length - used) :=
    h.headers (11, BitVec.ofNat 64 (p.c.rand.length - used)) (by simp [SearchPublic.headers])
  have hv2 : word s.mem p.control 16 = BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits) :=
    h.headers (2, BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits)) (by simp [SearchPublic.headers])
  have ht := h.input.tape_lt
  have hc := h.input.entropy_bound
  have hn : (BitVec.ofNat 64 (p.c.rand.length - used)).toNat = p.c.rand.length - used :=
    toNat_ofNat_of_lt (by omega_using [ht])
  have hcn : (BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits)).toNat = Spec.Ffdh.parameterEntropy p.c.bits :=
    toNat_ofNat_of_lt (by omega_using [hc])
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem ∧
    t.gpr .rax = BitVec.ofNat 64 (p.c.rand.length - used) ∧
    eval .ae t = some (decide (Spec.Ffdh.parameterEntropy p.c.bits ≤ p.c.rand.length - used))) ?_ rfl)
    fun _ ⟨⟨hm, ha, he⟩, k⟩ => ⟨h.keep k hm (by decide), hm, ha, he⟩
  xrun [State.ea, field, off, h.r12, hv11, hv2, hn, hcn, eval, Nat.reduceMul,
    BitVec.ofInt_natCast, hl 88 (by decide), hl 16 (by decide)]
  change (!decide (p.c.rand.length - used < Spec.Ffdh.parameterEntropy p.c.bits)) =
    decide (Spec.Ffdh.parameterEntropy p.c.bits ≤ p.c.rand.length - used)
  by_cases hb : Spec.Ffdh.parameterEntropy p.c.bits ≤ p.c.rand.length - used
  · simp [hb, show ¬p.c.rand.length - used < Spec.Ffdh.parameterEntropy p.c.bits by omega_using [hb]]
  · simp [hb, show p.c.rand.length - used < Spec.Ffdh.parameterEntropy p.c.bits by omega_using [hb]]

def shortResult (p : SearchPublic) (used remaining : Nat) : Spec.Ffdh.ParameterSearchResult :=
  if Spec.Ffdh.parameterEntropy p.c.bits ≤ p.c.rand.length - used then .exhausted used
  else .entropy remaining (Spec.Ffdh.parameterRequest p.c.bits (p.c.rand.length - used)) used

theorem search_short {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s)
    (hout : Spec.Rsa.bytesAt s.mem p.c.op p.c.k = List.replicate p.c.k 0) :
    WP isa short s (SearchDone p original (shortResult p used remaining)) := by
  unfold short
  refine WP.seq (WP.mono (short_guard h) fun u ⟨hu, hm, ha, he⟩ => ?_)
  refine WP.ite (decide (Spec.Ffdh.parameterEntropy p.c.bits ≤ p.c.rand.length - used)) he ?_ ?_
  · intro hb
    rw [shortResult, ite_eq_left (of_decide_eq_true hb)]
    exact search_exhausted hu
  · intro hb
    rw [shortResult, ite_eq_right (of_decide_eq_false hb)]
    exact search_request_done hu ha (by rw [hm]; exact hout)

end VG.Proof.Ffdh.X86_64.Generation
