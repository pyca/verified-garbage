module

public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Start

import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Tactic.TermCongr
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Impl.Ffdh.X86_64.CheckPrivate
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Flags
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Math
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Tail
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Scalar
/-! # FFDH private-key validation on x86-64: correctness and ABI -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/CheckPrivate/Main.lean`, which only this module imported.
section

/-! # FFDH private-key validation on x86-64: full main computation -/

section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def mainStatus (p : KpP) (xb : List Byte) : Nat :=
  if p.sv then if p.fl xb ∧ p.z xb = Spec.Rsa.os2ip p.yb then 1 else 0 else 2

theorem mainStatus_lt (p : KpP) (xb : List Byte) : mainStatus p xb < 3 := by
  unfold mainStatus
  split
  · split <;> decide
  · decide

private theorem retInner_ok {s : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {r : Nat}
    (hc : SubCtx s B Z o w w mi) (hr : r < 2 ^ 32) : WP isa (retInner r) s fun t =>
      t.gpr .rdi = B ∧ t.gpr .rax = BitVec.ofNat 64 r ∧ t.mem = s.mem ∧ Keep [.rdi, .rax] s t := by
  unfold retInner
  refine WP.seq (WP.mono (leave_ok hc) fun u ⟨hd, hm, k⟩ => ?_)
  exact WP.mono (ret_ok u hr) fun t ⟨ha, hm', kk⟩ =>
    ⟨(kk.gpr (by decide)).trans hd, ha, hm'.trans hm, (k.trans kk).mono (by decide)⟩

private theorem main_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.main M.mm E.code (.seq (.block r2Head) R.code) =
      seqs (((([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup) ++
        VG.Impl.Rsa.X86_64.Crt.loadArr aXm sX sXl) ++
          (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange ++
            ([.block [.alu .test .rax (.reg .rax)], .ite .e (retInner 2)
              (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.tail M.mm E.code (.seq (.block r2Head) R.code)))] :
              List (Prog isa)))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.main, List.append_assoc]

theorem main_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {p : KpP} {xb : List Byte} {s : State}
    (h : Base p xb s) (hd : s.gpr .rdi = p.B) (hG : word s.mem p.B (8 * sG) = off p.dp p.k)
    (hQ : word s.mem p.B (8 * sQ) = off p.dp (2 * p.k)) (hm : p.mv = true) :
    WP isa (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.main M.mm E.code (.seq (.block r2Head) R.code)) s
      (StepPost p s fun t => t.gpr .rdi = p.B ∧ t.gpr .rax = BitVec.ofNat 64 (mainStatus p xb)) := by
  rw [main_eq]
  have hodd := (valid_facts hm h.k1).1
  refine wp_seqs_append (by simp [pSetup, VG.Impl.Rsa.X86_64.Crt.loadArr]) (by simp)
    (WP.mono (setup_work h hd hG hQ hm) fun u₁ S₁ => ?_)
  obtain ⟨mi, hw₁, hd₁⟩ := S₁.1
  refine wp_seqs_append (a := VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange)
    (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange, isNonzero, geArr, cmpArr]) (by simp)
    (WP.mono (scalar_ok hw₁ hd₁ hodd) fun u₂ S₂ => ?_)
  have hw₂ := S₂.1.1
  have hd₂ := S₂.1.2.1
  simp only [seqs]
  refine WP.seq (WP.mono (test_bit_ok S₂.1.2.2) fun u₃ ⟨hz, hmem, k⟩ => ?_)
  have hw₃ := hw₂.keep hmem k
  have hd₃ := (k.gpr (by decide)).trans hd₂
  have S₃ : StepPost p u₂ (fun _ => True) u₃ := ⟨trivial, by rw [hmem]; exact InScr.refl _ _ _,
    (fun _ _ => by rw [hmem]), k.mono (by decide)⟩
  have H := (S₁.trans S₂).trans S₃
  refine WP.ite (!decide (p.sv = true)) (by simp [eval, hz]) (fun hs => ?_) (fun hs => ?_)
  · have hsv : p.sv = false := by cases h : p.sv <;> simp_all
    exact WP.mono (retInner_ok (hw₃.mem.ctx hd₃) (r := 2) (by decide)) fun t ⟨hd', ha, hmem', kk⟩ =>
      ⟨⟨hd', by simpa only [mainStatus, hsv, Bool.false_eq_true, ↓reduceIte] using ha⟩,
        by rw [hmem']; exact H.2.1,
        (fun i hi => by rw [hmem']; exact H.2.2.1 i hi), keep_trans H.2.2.2 (kk.mono (by decide))⟩
  · have hsv : p.sv = true := by cases h : p.sv <;> simp_all
    exact WP.mono (tail_ok M E R hw₃ hd₃ hm) fun t S₄ =>
      ⟨⟨S₄.1.1, by
        have he : BitVec.ofNat 64 (mainStatus p xb) = bit (p.fl xb ∧ p.z xb = Spec.Rsa.os2ip p.yb) := by
          simp only [mainStatus, hsv, ↓reduceIte]
          split <;> rfl
        rw [he]; exact S₄.1.2⟩, (H.trans S₄).2⟩

theorem mainStatus_eq {p : KpP} {xb : List Byte} {s : State} (h : Base p xb s)
    (hm : p.mv = true) (ha : Spec.Ffdh.parametersValid p.params = true) :
    mainStatus p xb = Spec.Ffdh.privateStatus p.params (Spec.Rsa.os2ip p.yb) (Spec.Rsa.os2ip xb) := by
  have ho := (valid_facts hm h.k1).1
  cases hsv : p.sv with
  | false =>
    have hx : Spec.Ffdh.privateValid p.params (Spec.Rsa.os2ip xb) = false := h.valid.trans hsv
    have hr := (privateStatus_scalar p.params (Spec.Rsa.os2ip p.yb) (Spec.Rsa.os2ip xb)).mpr hx
    simpa only [mainStatus, hsv, Bool.false_eq_true, ↓reduceIte] using hr.symm
  | true =>
    have hx : Spec.Ffdh.privateValid p.params (Spec.Rsa.os2ip xb) = true := h.valid.trans hsv
    rw [privateStatus_power ha _ _ hx]
    simp only [mainStatus, hsv, ↓reduceIte]
    congr 1
    apply propext
    change (p.fl xb ∧ p.z xb = Spec.Rsa.os2ip p.yb) ↔
      ((1 < p.z xb ∧ p.z xb < p.P - 1) ∧ p.z xb = Spec.Rsa.os2ip p.yb)
    unfold KpP.fl
    rw [lt_pm1 ho]

end VG.Proof.Ffdh.X86_64.CheckPrivate
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Spec.Ffdh

theorem body_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {s : State} (hpre : kpPre s) :
    WP isa (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.body M.mm E.code (.seq (.block r2Head) R.code)) s fun t =>
      kpPost s t ∧ t.gpr .rdi = (kpOf s).B ∧ InScr (kpOf s).B (kpOf s).Z s.mem t.mem ∧
      (∀ i < 6, word t.mem (kpOf s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧ Keep (.rdi :: mmRegs) s t := by
  have c := kpCtx_of hpre
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.body
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (entry_base c) fun u ⟨hb, hd, hi, hs, k⟩ => ?_
  refine WP.mono (dom_base hb hd) fun v ⟨hb', hz, hd', hG, hQ, hi', hs', k'⟩ => ?_
  have H := hi.trans hi'
  have K := keep_trans k k'
  have hS : ∀ i < 6, word v.mem (kpOf s).B (8 * i) = s.gpr (saved.getD i .rax) :=
    fun i hi => (hs' i hi).trans (hs i hi)
  refine WP.ite (!(kpOf s).mv) (by simp [eval, hz]) (fun hf => ?_) (fun hf => ?_)
  · have hm : (kpOf s).mv = false := by simpa only [Bool.not_eq_true'] using hf
    refine WP.mono (ret_ok v (r := 0) (by decide)) fun t ⟨_, hmem, kk⟩ =>
      ⟨?_, (kk.gpr (by decide)).trans hd', by rw [hmem]; exact H,
        (fun i hi => by rw [hmem]; exact hS i hi), keep_trans K (kk.mono (by decide))⟩
    intro hv
    have hm' := domainValid_mod hv
    change (kpOf s).mv = true at hm'
    rw [hm] at hm'
    contradiction
  · have hm : (kpOf s).mv = true := by simpa only [Bool.not_eq_false'] using hf
    refine WP.mono (main_ok M E R hb' hd' hG hQ hm) fun t ⟨⟨hd'', ha⟩, hi'', hs'', kk⟩ =>
      ⟨?_, hd'', H.trans hi'', (fun i hi => (hs'' i hi).trans (hS i hi)), keep_trans K kk⟩
    intro hv
    have hp : parametersValid (kpOf s).params = true := by
      unfold domainValid at hv
      exact ((Bool.and_eq_true _ _).mp hv).1
    have hst : mainStatus (kpOf s) (kpX s) < 2 ^ 32 := (mainStatus_lt _ _).trans (by decide)
    change ((t.gpr .rax).setWidth 32).toNat = privateStatus (kpOf s).params (Spec.Rsa.os2ip (kpOf s).yb) (Spec.Rsa.os2ip (kpX s))
    rw [ha]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (hst.trans (by decide)), Nat.mod_eq_of_lt hst]
    exact mainStatus_eq hb' hm hp

theorem kp_correct (M : Mont) (E : CrtExpL M) (R : R2Impl M)
    (hmx : (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code M.mm E.code (.seq (.block r2Head) R.code)).allInstrs
      (fun i => !loadsMxcsr i) = true) (s : State) (h : kpContract.pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code M.mm E.code (.seq (.block r2Head) R.code)) s tr t ∧
      abiPreserved s t ∧ kpContract.post s t := by
  have hpre := h
  have c := kpCtx_of h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hRetScr, _⟩ := h
  suffices hw : WP isa (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code M.mm E.code (.seq (.block r2Head) R.code)) s
      fun t => gprPreserved s t ∧ kpContract.post s t by
    obtain ⟨tr, t, he, hg, hp⟩ := hw
    exact ⟨tr, t, he, abiPreserved_of_exec hmx he hg, hp⟩
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code
  refine WP.seq (WP.mono (body_ok M E R hpre) fun u ⟨hp, hd, hf, hs, k⟩ => ?_)
  have hZ := c.hZ
  have hk := c.k1
  refine WP.mono (exit_ok (c.hs.congr k.2.2) hd (by omega) hs)
    fun t ⟨hRestore, hm, kk⟩ => ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact (kk.gpr (by decide)).trans (k.gpr (by decide))
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
  · rw [hm]
    apply Mem.readW_congr
    intro i hi
    exact hf _ (out_scr hRetScr (contains_byte (s.gpr .rsp) hi (by decide)))
  · change kpPost s t
    unfold kpPost
    rw [kk.gpr (show .rax ∉ saved by decide)]
    exact hp

end VG.Proof.Ffdh.X86_64.CheckPrivate
