module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Sieve
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
public import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! # FFDH parameter candidates on x86-64: reuse RSA's proven trial reductions -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Proof.RsaKeyGen.X86_64
open VG.Proof.MlKem.X86_64

theorem sieve_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hTZ : slot w aTab + 2048 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) :
    WP isa sieve s fun t =>
      t.zf = some (!(anyPre (wv s.mem B (slot w aN) w) 53)) ∧ Good t B Z w minv ∧
      Frm B [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r12, .r13, .r14, .r15] s t := by
  have hn := hg.scr.nowrap
  have hT2 : 8 * kT2 + 8 ≤ slot w aN := hdr_lt_slot w aN (by decide)
  have hTa : slot w aN + 8 * (w + 2) ≤ slot w aTab := by unfold slot aN aTab; omega
  have hTa' : 8 * kT2 + 8 ≤ slot w aTab := hdr_lt_slot w aTab (by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  unfold sieve
  simp only [List.cons_append, List.nil_append, seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (extBase_ok hg hZ hw' (j := aTab) (by decide) (r := .rbx) (by decide) rfl rfl)
    fun s₁ ⟨hbx₁, hm₁, k₁⟩ => ?_
  refine WP.mono (tabWrites_ok (hg.scr.congr k₁.2.2) hTZ hbx₁ 256 (Nat.le_refl _)) fun s₂ ⟨htab₂, ho₂, k₂⟩ => ?_
  have hm₂ : ∀ i < 32, word s₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    rw [ho₂.word (Or.inl (by have := hdr_lt_slot w aTab hi; omega)) (by omega), hm₁]
  have hdi₂ : s₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi)
  have hg₂ : Good s₂ B Z w minv := ⟨hg.scr.congr (k₂.2.2.trans k₁.2.2), hdi₂,
    ⟨by rw [hm₂ sW (by decide)]; exact hg.hdr.hw, by rw [hm₂ sMinv (by decide)]; exact hg.hdr.hminv,
      fun j hj => by rw [hm₂ (sArr j) (by unfold sArr; omega)]; exact hg.hdr.harr j hj⟩⟩
  have hc₂ : wv s₂.mem B (slot w aN) w = wv s.mem B (slot w aN) w := by
    rw [ho₂.wv (k := w) (Or.inl (by omega)) (by omega), hm₁]
  have hst : ∀ i < 32, InRegions s₂.wr (off B (8 * i)) 8 := fun i hi =>
    hg₂.scr.st (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.seq (WP.mono (WP.keep [.rax, .r13] (Q := fun t => t.mem = (s₂.mem.writeW (off B (8 * kT0))
      (BitVec.ofNat 64 13)).writeW (off B (8 * kT2)) (0 : BitVec 64) ∧ t.gpr .r13 = BitVec.ofNat 64 0) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hst kT0 (by decide), hst kT2 (by decide), sx_ofNat]
    rfl) rfl) fun t₄ ⟨⟨hm₄, h13₄⟩, k₄⟩ => ?_)
  have hoA : Outside B (8 * kT0) 8 s₂.mem (s₂.mem.writeW (off B (8 * kT0)) (BitVec.ofNat 64 13)) :=
    writeW_outside _ _ _ (by unfold kT0 sFn; omega_arith)
  have hoB : ∀ m : Mem, Outside B (8 * kT2) 8 m (m.writeW (off B (8 * kT2)) (0 : BitVec 64)) :=
    fun m => writeW_outside _ _ _ (by unfold kT2 sFn; omega_arith)
  have hg₄ : Good t₄ B Z w minv := ⟨hg₂.scr.congr k₄.2.2, (k₄.gpr (by decide)).trans hg₂.rdi,
    by rw [hm₄]; exact (hg₂.hdr.store (by decide) (by decide) _).store (by decide) (by decide) _⟩
  have hc₄ : wv t₄.mem B (slot w aN) w = wv s.mem B (slot w aN) w := by
    rw [hm₄, (hoB _).wv (Or.inr hT2) (by omega_arith), hoA.wv (Or.inr (by unfold kT0 kT2 sFn at *; omega_arith)) (by omega_arith), hc₂]
  have hN₄ : word t₄.mem B (8 * kT0) = BitVec.ofNat 64 13 := by
    rw [hm₄, (hoB _).word (Or.inl (by unfold kT0 kT2 sFn; omega_arith)) (by unfold kT0 sFn; omega_arith), word_writeW_self]
  have htab₄ : ∀ i < 256, word t₄.mem B (slot w aTab + 8 * i) = BitVec.ofNat 64 (tabWord i) := fun i hi => by
    rw [hm₄, (hoB _).word (Or.inr (by omega_arith)) (by omega_arith),
      hoA.word (Or.inr (by have := hdr_lt_slot w aTab (show kT0 < 32 by decide); omega_arith)) (by omega_arith)]
    exact htab₂ i hi
  have hf₄ : word t₄.mem B (8 * kT2) = mask (anyPre (wv t₄.mem B (slot w aN) w) (4 * 0)) := by
    rw [hm₄, word_writeW_self]; unfold anyPre; rw [Nat.mul_zero, show List.range 0 = [] from rfl, List.any_nil, mask_false]
  unfold sieveWord sieveLoad
  refine WP.seq (WP.mono (wp_upto (a := 0) (N := 13) (by omega_arith)
    (fun k t' => TLInv t₄ B Z w (slot w aTab) 13 minv k t' ∧
      word t'.mem B (8 * kT2) = mask (anyPre (wv t₄.mem B (slot w aN) w) (4 * k)))
    (fun k _ hk t' ⟨hI, hf⟩ => WP.mono (tlIter_ok hZ hw hw' hTZ (by decide) hk hI hf)
      fun t'' ⟨hz, hI', hf'⟩ => ⟨hz, hI', hf'⟩) (fun t' h => h)
    ⟨⟨hg₄, h13₄, hN₄, htab₄, rfl, Frm.refl _ _ _, Keep.refl _ _⟩, hf₄⟩) fun t₅ ⟨hI₅, hf₅⟩ => ?_)
  refine WP.seq (WP.mono (tlLoad_ok hZ hw' hTZ (by decide) hI₅) fun t₆ ⟨hI₆, hT1₆, hf₆⟩ => ?_)
  rw [hf₅] at hf₆
  refine wp_seqs_append (a := trialEntry 0) (by simp [trialEntry]) (by simp)
    (WP.mono (tlEntry_ok hZ hw hw' hTa' hTZ (by decide) (by decide) hI₆
      (by simpa only [Nat.mul_zero, Nat.add_zero] using hf₆) hT1₆) fun t₇ ⟨hI₇, hf₇, _⟩ => ?_)
  have hl₇ : InRegions (t₇.rd ++ t₇.wr) (off B (8 * kT2)) 8 :=
    hI₇.good.scr.ld (by have := hdr_lt_slot w 8 (show kT2 < 32 by decide); omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (!(anyPre (wv s.mem B (slot w aN) w) 53)) ∧
      t.mem = t₇.mem) (by
    xrun [State.ea, hdr, hI₇.good.rdi, hdrOff, hl₇, hf₇, BitVec.and_self, hc₄]
    cases anyPre (wv s.mem B (slot w aN) w) 53 <;> decide) rfl)
    fun t ⟨⟨hz, hm⟩, k⟩ => ⟨hz, ⟨hI₇.good.scr.congr k.2.2, (k.gpr (by decide)).trans hI₇.good.rdi,
      by rw [hm]; exact hI₇.good.hdr⟩, ?_, ?_⟩
  · intro x hx
    rw [hm, hI₇.frm x (fun r hr => hx r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h])), hm₄,
      hoB _ x (hx (8 * kT2, 8) (by simp)), hoA x (hx (8 * kT0, 8) (by simp)),
      ho₂ x (hx (slot w aTab, 2048) (by simp)), hm₁]
  · exact (((k₁.trans k₂).trans k₄).trans hI₇.keep |>.trans k).mono (by decide)

/-- For an odd candidate above the sieve table, ZF is exactly primeShape. -/
theorem sieve_shape_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hTZ : slot w aTab + 2048 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hp : 8161 < wv s.mem B (slot w aN) w) (ho : wv s.mem B (slot w aN) w % 2 = 1) :
    WP isa sieve s fun t =>
      t.zf = some (Spec.Ffdh.primeShape (wv s.mem B (slot w aN) w)) ∧ Good t B Z w minv ∧
      Frm B [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r12, .r13, .r14, .r15] s t := by
  simpa only [VG.Proof.Ffdh.ParameterCandidate.primeShape_sieve hp ho, anyPre] using
    sieve_ok hg hZ hTZ hw hw'

theorem oddTest_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) :
    WP isa (.block oddTest) s fun t =>
      t.zf = some (decide (wv s.mem B (slot w aN) w % 2 = 1)) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sArr aN)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot w 8 (show sArr aN < 32 by decide); omega)
  have hn : InRegions (s.rd ++ s.wr) (off B (slot w aN)) 8 :=
    hg.scr.ld (by have := slot_le (w := w) (show aN < 8 by decide); omega)
  have he : ((word s.mem B (slot w aN) &&& 1) == 1) = decide (wv s.mem B (slot w aN) w % 2 = 1) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    rw [← BitVec.toNat_inj, BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl,
      show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    rw [← wv_mod64 s.mem B (slot w aN) hw, Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ 64 by decide)]
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.zf = some (decide (wv s.mem B (slot w aN) w % 2 = 1)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hz, hm⟩, k⟩ => ⟨hz, hm, k⟩
  unfold oddTest
  xrun [State.ea, hdr, at0, hg.rdi, hdrOff, hl, hn, BitVec.ofInt_ofNat, BitVec.add_zero, hg.hdr.harr aN (by decide)]
  simpa only [sub_beq_zero, show BitVec.signExtend 64 (1 : BitVec 32) = 1 from by decide] using he

/-- Includes the candidate's oddness test, so this is exactly primeShape for either p or q. -/
theorem primeCheck_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hTZ : slot w aTab + 2048 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hp : 8161 < wv s.mem B (slot w aN) w) :
    WP isa primeCheck s fun t =>
      t.zf = some (Spec.Ffdh.primeShape (wv s.mem B (slot w aN) w)) ∧ Good t B Z w minv ∧
      Frm B [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r12, .r13, .r14, .r15] s t := by
  unfold primeCheck
  refine WP.seq (WP.mono (oddTest_ok hg hZ hw) fun u ⟨hz, hm, k⟩ => ?_)
  have hgu : Good u B Z w minv := ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
    by rw [hm]; exact hg.hdr⟩
  refine WP.ite (decide (wv s.mem B (slot w aN) w % 2 = 1)) (by simp [eval, hz]) ?_ ?_
  · intro ho
    have ho' : wv s.mem B (slot w aN) w % 2 = 1 := of_decide_eq_true ho
    exact WP.mono (sieve_shape_ok hgu hZ hTZ hw hw' (by rw [hm]; exact hp) (by rw [hm]; exact ho'))
      fun t ⟨hz', hg', hf, k'⟩ => ⟨by simpa only [hm] using hz', hg', by rw [← hm]; exact hf,
        (k.trans k').mono (by decide)⟩
  · intro ho
    have ho' : ¬ wv s.mem B (slot w aN) w % 2 = 1 := of_decide_eq_false ho
    exact WP.block_nil ⟨by simpa [Spec.Ffdh.primeShape, Bool.beq_eq_decide_eq, ho', ho] using hz,
      hgu, by rw [hm]; exact Frm.refl _ _ _, k.mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
