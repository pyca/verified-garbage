module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.KeyStep
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchGuards
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # The loop

Each iteration searches for the progress' prime, classifies the result, and
goes on while the status is 4, to a state of a lower measure; the loop ends
with the key search's result.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 (RoundImpl)
open VG.Proof.Ffdh.X86_64.Generation (second_status_guard)
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

theorem cmp3_guard {s : State} {status : Nat}
    (hs : s.gpr .rax = BitVec.ofNat 64 status) (h64 : status < 2 ^ 64) :
    WP isa (.block [.alu .cmp .rax (.imm 3)]) s fun t =>
      (eval .e t = some (decide (status = 3)) ∧ t.mem = s.mem) ∧ Keep [.rax] s t := by
  have he : (BitVec.ofNat 64 status == (3 : BitVec 64)) = decide (status = 3) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h64]
    rfl
  refine WP.keep [.rax] ?_ rfl
  xrun [hs, eval, sub_beq_zero, he]

section

variable {p : GenPublic} {original s t : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}

/-- After the search: what it leaves, classified. -/
theorem classify_ok (hi : GenIter p original final used st s) (ha : AfterSearch p original used st s t) :
    WP isa (classify keyCall) t (Classified p original final used st) := by
  have hf := hi.1.input.cfacts
  unfold classify
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (after_head hi ha) fun u ⟨he, hax, hcx, hm⟩ => ?_)
  have hu64 : (rOf p original used st).used < 2 ^ 64 := by
    have := hm.frame.used_le; have := hf.rand64; omega
  cases ho : (rOf p original used st).outcome with
  | entropy k a =>
    have hs : (rOf p original used st).status = 0 := by rw [rOf_status, ho]; rfl
    rw [hs] at he
    exact WP.ite true he (fun _ => classify_entropy hm hax ho) (fun h => by cases h)
  | exhausted =>
    have hs : (rOf p original used st).status = 3 := by rw [rOf_status, ho]; rfl
    rw [hs] at he hax
    refine WP.ite false he (fun h => by cases h) (fun _ => ?_)
    refine WP.seq (WP.mono (cmp3_guard hax (by decide)) fun v ⟨⟨he2, hmem⟩, k⟩ => ?_)
    have hv := hm.keep hmem k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide))
    exact WP.ite true he2 (fun _ => classify_exhausted hv ho) (fun h => by cases h)
  | accepted c =>
    have hs : (rOf p original used st).status = 1 := by rw [rOf_status, ho]; rfl
    rw [hs] at he hax
    refine WP.ite false he (fun h => by cases h) (fun _ => ?_)
    refine WP.seq (WP.mono (cmp3_guard hax (by decide)) fun v ⟨⟨he2, hmem⟩, k⟩ => ?_)
    have hv := hm.keep hmem k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide))
    have hcx' : v.gpr .rcx = BitVec.ofNat 64 (rOf p original used st).used := by
      rw [k.gpr (by decide)]; exact hcx
    refine WP.ite false he2 (fun h => by cases h) (fun _ => ?_)
    refine WP.seq (WP.mono (test_guard hcx' hu64) fun w ⟨⟨he3, hmem3⟩, k3⟩ => ?_)
    have hw := hv.keep hmem3 k3.2.1 k3.2.2 (fun r hr => k3.gpr (by revert r; decide))
    refine WP.ite (decide ((rOf p original used st).used = 0)) he3 (fun h0 => ?_) (fun h0 => ?_)
    · exact WP.mono (classify_none hw ho (of_decide_eq_true h0)) fun _ h => Or.inr h
    · have hpos : 0 < (rOf p original used st).used := by
        have := of_decide_eq_false h0; omega
      unfold accepted
      refine WP.seq (WP.mono (phase_ok hw.frame) fun x ⟨⟨he4, hmem4⟩, k4⟩ => ?_)
      have hx := hw.keep hmem4 k4.2.1 k4.2.2 (fun r hr => k4.gpr (by revert r; decide))
      obtain ⟨left, phase, remaining⟩ := st
      cases phase with
      | p =>
        refine WP.ite true he4 (fun _ => ?_) (fun h => by cases h)
        refine WP.mono (nextPrime_ok hx.frame (phase := 1) (by decide)) fun y ⟨hym, k5⟩ => Or.inl ?_
        exact classify_p hx ho hpos rfl hym k5.2.1 k5.2.2 (fun r hr => k5.gpr (by revert r; decide))
      | q pB =>
        refine WP.ite false he4 (fun h => by cases h) (fun _ => ?_)
        exact classify_key hx ho hpos rfl

/-- The loop's test: the status, against 4. -/
theorem status_guard (h : GenFrame p original used st s) {w : Nat} (hw : word s.mem p.F 80 = BitVec.ofNat 64 w)
    (h64 : w < 2 ^ 64) :
    WP isa (.block [.mov .rax (.mem (field 10)), .alu .cmp .rax (.imm 4)]) s fun t =>
      (eval .e t = some (decide (w = 4)) ∧ t.mem = s.mem) ∧ Keep [.rax] s t := by
  have hl : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 80) 8 := h.scr.ld (d := 80) (by decide)
  have hw' : s.mem.readW (p.F + BitVec.ofNat 64 80) 64 = BitVec.ofNat 64 w := hw
  have he : (BitVec.ofNat 64 w == (4 : BitVec 64)) = decide (w = 4) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]
    rfl
  refine WP.keep [.rax] ?_ rfl
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, h.r12, hl, hw', eval,
    sub_beq_zero, he]

theorem GenInv.keep {n : Nat} (h : GenInv p original final n s) (hm : t.mem = s.mem) (hr : t.rd = s.rd)
    (hw : t.wr = s.wr) (hg : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r) : GenInv p original final n t := by
  obtain ⟨used, st, hn, ⟨hl, hfin⟩⟩ := h
  refine ⟨used, st, hn, ⟨⟨hl.toGenFrame.keep hm hr hw hg, ?_⟩, hfin⟩⟩
  rw [hm]; exact hl.key

theorem GenDone.keep (h : GenDone p original final s) (hm : t.mem = s.mem) (hr : t.rd = s.rd)
    (hw : t.wr = s.wr) (hg : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r) : GenDone p original final t := by
  obtain ⟨g, h1, h2, h3⟩ := h
  refine ⟨g.keep hm hr hw hg, ?_, ?_, ?_⟩ <;> rw [hm]
  exacts [h1, h2, h3]

theorem keyStatus_lt (r : KeySearchResult) : r.keyStatus < 4 := by
  unfold KeySearchResult.keyStatus
  split <;> decide

end

/-- An iteration: the search, its classification and the loop's test. -/
theorem gen_iteration (v : RoundImpl) {p : GenPublic} {original s : State} {final : KeySearchResult} {n : Nat}
    (h : GenInv p original final n s) :
    WP isa (iteration (searchCall v) keyCall) s fun t =>
      (eval .e t = some false ∧ GenDone p original final t) ∨
      (eval .e t = some true ∧ ∃ m < n, GenInv p original final m t) := by
  obtain ⟨used, st, rfl, hi⟩ := h
  unfold iteration
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (search_run v hi.1) fun t ha => ?_)
  refine WP.seq (WP.mono (classify_ok hi ha) fun u hc => ?_)
  rcases hc with ⟨h4, ⟨st', e, hl', hm, htail, -, -⟩, ⟨tr, hfin⟩⟩ | hd
  · refine WP.mono (status_guard hl'.toGenFrame h4 (by decide)) fun x ⟨⟨hx, hmem⟩, k⟩ => Or.inr ⟨hx, _, hm, ?_⟩
    refine GenInv.keep ⟨_, st', rfl, ⟨hl', tr ++ e, ?_⟩⟩ hmem k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide))
    rw [hfin, htail, consume_consume]
  · have hlt := keyStatus_lt final
    refine WP.mono (status_guard hd.1 hd.2.1 (by omega)) fun x ⟨⟨hx, hmem⟩, k⟩ => Or.inl ⟨?_, ?_⟩
    · rw [hx]; congr 1; simp only [decide_eq_false_iff_not]; omega
    · exact hd.keep hmem k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide))

theorem gen_loop (v : RoundImpl) {p : GenPublic} {original s : State} {final : KeySearchResult} {n : Nat}
    (h : GenInv p original final n s) :
    WP isa (.loop (iteration (searchCall v) keyCall) .e) s (GenDone p original final) :=
  WP.loop (M := isa) (body := iteration (searchCall v) keyCall) (c := .e) (Q := GenDone p original final)
    (GenInv p original final) (fun _ _ h => gen_iteration v h) n s h

end VG.Proof.RsaKeyGen.X86_64.Generate
