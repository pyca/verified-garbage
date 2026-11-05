module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Sieve
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
public import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! # FFDH parameter candidates on x86-64: RSA's trial division, with its proven reductions -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Proof.RsaKeyGen.X86_64
open VG.Proof.MlKem.X86_64

/-- The table's words the sieve divides by, for the requested width `bits`:
256 above 1024 bits, else 128. -/
def sieveCount (bits : Nat) : Nat := if 1025 ≤ bits then 256 else 128

/-- `sieve`: ZF set iff none of the table's first `4 (sieveCount bits)`
entries divides the candidate in `aN`, `bits` in RDX. -/
theorem sieve_ok {s : State} {B : Addr} {Z w bits : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hTZ : slot w aTab + 2048 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hb : bits < 2 ^ 32) (hdx : s.gpr .rdx = BitVec.ofNat 64 bits) :
    WP isa sieve s fun t =>
      t.zf = some (!(anyPre (wv s.mem B (slot w aN) w) (4 * sieveCount bits))) ∧ Good t B Z w minv ∧
      Frm B [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r12, .r13, .r14, .r15] s t := by
  have hn := hg.scr.nowrap
  have hT2 : 8 * kT2 + 8 ≤ slot w aN := hdr_lt_slot w aN (by decide)
  have hTa : slot w aN + 8 * (w + 2) ≤ slot w aTab := by unfold slot aN aTab; omega_arith
  have hTa' : 8 * kT2 + 8 ≤ slot w aTab := hdr_lt_slot w aTab (by decide)
  unfold sieve
  simp only [seqs]
  -- The table, and the number of its words to use.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (extBase_ok hg hZ hw' (j := aTab) (by decide) (r := .rbx) (by decide) rfl rfl)
    fun s₁ ⟨hbx₁, hm₁, k₁⟩ => ?_
  refine WP.mono (tabWrites_ok (hg.scr.congr k₁.2.2) hTZ hbx₁ 256 (Nat.le_refl _)) fun s₂ ⟨htab₂, ho₂, k₂⟩ => ?_
  have hm₂ : ∀ i < 32, word s₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    rw [ho₂.word (Or.inl (by have := hdr_lt_slot w aTab hi; omega_arith)) (by omega_arith), hm₁]
  have hdi₂ : s₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi)
  have hdx₂ : s₂.gpr .rdx = BitVec.ofNat 64 bits := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hdx)
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 128 ∧
      t.cf = some (decide (bits < 1025)) ∧ t.mem = s₂.mem) (by
    xrun [hdx₂, sx_ofNat]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
      show (BitVec.signExtend 64 (1025 : BitVec 32)).toNat = 1025 by decide]) rfl)
    fun s₃ ⟨⟨hax₃, hcf₃, hm₃⟩, k₃⟩ => ?_
  have hg₃ : Good s₃ B Z w minv := ⟨hg.scr.congr (k₃.2.2.trans (k₂.2.2.trans k₁.2.2)), (k₃.gpr (by decide)).trans hdi₂,
    ⟨by rw [hm₃, hm₂ sW (by decide)]; exact hg.hdr.hw, by rw [hm₃, hm₂ sMinv (by decide)]; exact hg.hdr.hminv,
      fun j hj => by rw [hm₃, hm₂ (sArr j) (by unfold sArr; omega_arith)]; exact hg.hdr.harr j hj⟩⟩
  have hc₃ : wv s₃.mem B (slot w aN) w = wv s.mem B (slot w aN) w := by
    rw [hm₃, ho₂.wv (k := w) (Or.inl (by omega_arith)) (by omega_arith), hm₁]
  have ho₃ : Outside B (slot w aTab) 2048 s.mem s₃.mem := by rw [hm₃, ← hm₁]; exact ho₂
  generalize hNdef : sieveCount bits = N
  have hN : N ≤ 256 ∧ 1 ≤ N := by rw [← hNdef]; unfold sieveCount; split <;> omega_arith
  have hN128 : bits < 1025 → N = 128 := fun h => by rw [← hNdef]; unfold sieveCount; split <;> omega_arith
  have hN256 : ¬ bits < 1025 → N = 256 := fun h => by rw [← hNdef]; unfold sieveCount; split <;> omega_arith
  -- From `rax = N`: the counts, the loop and ZF.
  have cont : ∀ t : State, t.gpr .rax = BitVec.ofNat 64 N → t.mem = s₃.mem → Keep [.rax] s₃ t →
      WP isa (.seq (.block [.store (hdr kT0) .rax, .mov32 .rax (.imm 0), .store (hdr kT2) .rax, .mov32 .r13 (.imm 0)])
        (.seq (.loop (seqs sieveWord) .ne)
          (.block [.mov .rax (.mem (hdr kT2)), .alu .test .rax (.reg .rax)]))) t fun t =>
      t.zf = some (!anyPre (wv s.mem B (slot w aN) w) (4 * N)) ∧ Good t B Z w minv ∧
      Frm B [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r12, .r13, .r14, .r15] s t := by
    intro t hax hmt kt
    have hgt : Good t B Z w minv := ⟨hg₃.scr.congr kt.2.2, (kt.gpr (by decide)).trans hg₃.rdi, by rw [hmt]; exact hg₃.hdr⟩
    have hst : ∀ i < 32, InRegions t.wr (off B (8 * i)) 8 := fun i hi => hgt.scr.st (by have := hdr_lt_slot w 8 hi; omega_arith)
    refine WP.seq (WP.mono (WP.keep [.rax, .r13] (Q := fun t' => t'.mem = (t.mem.writeW (off B (8 * kT0))
        (BitVec.ofNat 64 N)).writeW (off B (8 * kT2)) (0 : BitVec 64) ∧ t'.gpr .r13 = BitVec.ofNat 64 0) (by
      xrun [State.ea, hdr, hgt.rdi, hdrOff, hst kT0 (by decide), hst kT2 (by decide), hax, sx_ofNat]
      rfl) rfl) fun t₄ ⟨⟨hm₄, h13₄⟩, k₄⟩ => ?_)
    have hoA : Outside B (8 * kT0) 8 t.mem (t.mem.writeW (off B (8 * kT0)) (BitVec.ofNat 64 N)) :=
      writeW_outside _ _ _ (by unfold kT0 sFn; omega_arith)
    have hoB : ∀ m : Mem, Outside B (8 * kT2) 8 m (m.writeW (off B (8 * kT2)) (0 : BitVec 64)) :=
      fun m => writeW_outside _ _ _ (by unfold kT2 sFn; omega_arith)
    have hg₄ : Good t₄ B Z w minv := ⟨hgt.scr.congr k₄.2.2, (k₄.gpr (by decide)).trans hgt.rdi,
      by rw [hm₄]; exact (hgt.hdr.store (by decide) (by decide) _).store (by decide) (by decide) _⟩
    have hc₄ : wv t₄.mem B (slot w aN) w = wv s.mem B (slot w aN) w := by
      rw [hm₄, (hoB _).wv (Or.inr hT2) (by omega_arith),
        hoA.wv (Or.inr (by unfold kT0 kT2 sFn at *; omega_arith)) (by omega_arith), hmt, hc₃]
    have hN₄ : word t₄.mem B (8 * kT0) = BitVec.ofNat 64 N := by
      rw [hm₄, (hoB _).word (Or.inl (by unfold kT0 kT2 sFn; omega_arith)) (by unfold kT0 sFn; omega_arith),
        word_writeW_self]
    have htab₄ : ∀ i < 256, word t₄.mem B (slot w aTab + 8 * i) = BitVec.ofNat 64 (tabWord i) := fun i hi => by
      rw [hm₄, (hoB _).word (Or.inr (by omega_arith)) (by omega_arith),
        hoA.word (Or.inr (by have := hdr_lt_slot w aTab (show kT0 < 32 by decide); omega_arith)) (by omega_arith),
        hmt, hm₃]; exact htab₂ i hi
    have hf₄ : word t₄.mem B (8 * kT2) = mask (anyPre (wv t₄.mem B (slot w aN) w) (4 * 0)) := by
      rw [hm₄, word_writeW_self]; unfold anyPre
      rw [Nat.mul_zero, show List.range 0 = [] from rfl, List.any_nil, mask_false]
    unfold sieveWord sieveLoad
    refine WP.seq (WP.mono (wp_upto (a := 0) (N := N) (by omega_arith)
      (fun k t' => TLInv t₄ B Z w (slot w aTab) N minv k t' ∧
        word t'.mem B (8 * kT2) = mask (anyPre (wv t₄.mem B (slot w aN) w) (4 * k)))
      (fun k _ hk t' ⟨hI, hf⟩ => WP.mono (tlIter_ok hZ hw hw' hTZ hN.1 hk hI hf)
        fun t'' ⟨hz, hI', hf'⟩ => ⟨hz, hI', hf'⟩) (fun t' h => h)
      ⟨⟨hg₄, h13₄, hN₄, htab₄, rfl, Frm.refl _ _ _, Keep.refl _ _⟩, hf₄⟩) fun t₅ ⟨hI₅, hf₅⟩ => ?_)
    have hl₅ : InRegions (t₅.rd ++ t₅.wr) (off B (8 * kT2)) 8 :=
      hI₅.good.scr.ld (by have := hdr_lt_slot w 8 (show kT2 < 32 by decide); omega_arith)
    refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.zf = some (!anyPre (wv s.mem B (slot w aN) w) (4 * N)) ∧
        t'.mem = t₅.mem) (by
      xrun [State.ea, hdr, hI₅.good.rdi, hdrOff, hl₅, hf₅, BitVec.and_self, hc₄]
      cases anyPre (wv s.mem B (slot w aN) w) (4 * N) <;> decide) rfl)
      fun t' ⟨⟨hz, hm'⟩, k'⟩ => ⟨hz, ⟨hI₅.good.scr.congr k'.2.2, (k'.gpr (by decide)).trans hI₅.good.rdi,
        by rw [hm']; exact hI₅.good.hdr⟩, ?_, ?_⟩
    · intro x hx
      rw [hm', hI₅.frm x (fun r hr => hx r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h])), hm₄,
        hoB _ x (hx (8 * kT2, 8) (by simp)), hoA x (hx (8 * kT0, 8) (by simp)), hmt,
        ho₃ x (hx (slot w aTab, 2048) (by simp))]
    · exact (((((k₁.trans k₂).trans k₃).trans kt).trans k₄).trans hI₅.keep |>.trans k').mono (by decide)
  refine WP.seq (WP.ite (decide (bits < 1025)) (by simp [eval, hcf₃])
    (fun h => WP.block_nil (cont s₃ ?_ rfl (Keep.refl _ _)))
    (fun h => WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 N ∧ t.mem = s₃.mem) (by
      xrun [sx_ofNat]; rw [hN256 (by simpa using h)]; rfl) rfl) fun t ⟨⟨h1, h2⟩, k⟩ => cont t h1 h2 k))
  rw [hax₃, hN128 (by simpa using h)]

theorem anyPre_mono {c m n : Nat} (h : m ≤ n) (ha : anyPre c m = true) : anyPre c n = true := by
  unfold anyPre at *
  obtain ⟨i, hi, hd⟩ := List.any_eq_true.mp ha
  exact List.any_eq_true.mpr ⟨i, List.mem_range.mpr (Nat.lt_of_lt_of_le (List.mem_range.mp hi) h), hd⟩

/-- Above the table's largest prime, an odd candidate passes the sieve iff
it has `primeShape` and is not `obviouslyComposite` for the requested width. -/
theorem sieve_shape {c bits : Nat} (hc : 8161 < c) (ho : c % 2 = 1) :
    (!anyPre c (4 * sieveCount bits)) =
      (Spec.Ffdh.primeShape c && !Spec.RsaKeyGen.obviouslyComposite bits c) := by
  have htrial : anyPre c (4 * sieveCount bits) = Spec.RsaKeyGen.obviouslyComposite bits c := by
    have he := VG.Proof.RsaKeyGen.trialAny_eq (w := if 1025 ≤ bits then 17 else 16) hc
    have hw : (if 17 ≤ (if 1025 ≤ bits then 17 else 16) then 256 else 128) = sieveCount bits := by
      unfold sieveCount; split <;> simp
    have hb : Spec.RsaKeyGen.obviouslyComposite (64 * if 1025 ≤ bits then 17 else 16) c =
        Spec.RsaKeyGen.obviouslyComposite bits c := by
      unfold Spec.RsaKeyGen.obviouslyComposite Spec.RsaKeyGen.trialPrimes
      by_cases h : 1025 ≤ bits
      · simp only [h, ↓reduceIte, show 1024 < 64 * 17 by decide, show 1024 < bits by omega]
      · simp only [h, ↓reduceIte, show ¬ 1024 < 64 * 16 by decide, show ¬ 1024 < bits by omega]
    rw [hw, hb] at he
    exact he
  have h53 : 53 ≤ 4 * sieveCount bits := by unfold sieveCount; split <;> omega
  rw [VG.Proof.Ffdh.ParameterCandidate.primeShape_sieve hc ho, ← htrial]
  cases hA : anyPre c (4 * sieveCount bits)
  · have h' : ((List.range 53).any fun i => c % VG.Impl.RsaKeyGen.tabEntry i == 0) = false := by
      cases h5 : ((List.range 53).any fun i => c % VG.Impl.RsaKeyGen.tabEntry i == 0)
      · rfl
      · have := anyPre_mono h53 h5; rw [hA] at this; contradiction
    simp [h']
  · simp

theorem oddTest_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) :
    WP isa (.block oddTest) s fun t =>
      t.zf = some (decide (wv s.mem B (slot w aN) w % 2 = 1)) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sArr aN)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot w 8 (show sArr aN < 32 by decide); omega_arith)
  have hn : InRegions (s.rd ++ s.wr) (off B (slot w aN)) 8 :=
    hg.scr.ld (by have := slot_le (w := w) (show aN < 8 by decide); omega_arith)
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

end VG.Proof.Ffdh.X86_64.ParameterCandidate
