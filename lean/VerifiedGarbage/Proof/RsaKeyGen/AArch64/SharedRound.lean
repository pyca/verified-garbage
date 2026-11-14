module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrWit
public import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrRound
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrTail

/-! ### `RsaKeyGen.AArch64.SharedWitness`, which only this module used -/

section

/-! # Witness preparation for a generic shared Miller–Rabin round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Rsa.AArch64
open VG.Proof.Rsa (slot_lt)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY)

def witnessRanges (w : Nat) : List (Nat × Nat) := witRanges w ++
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)),
    (slot w aXm, 8 * (w + 2)), (slot w aB, 8 * (w + 2))]

/-- `witnessRanges`'s ranges, in the header and in the arrays. -/
theorem witnessRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [(216, 8), (0, 8)]
    [(1, 1), (2, 1), (3, 1), (5, 1), (8, 1)] (witnessRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append,
    witRanges, witnessRanges, Public.aX, Public.aAcc, Public.aTmp, Public.aXm, aX, aAcc, aTmp, aXm, aB, sFn, kU, kUsed] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr ⟨(1, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inr ⟨(2, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(3, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(5, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(8, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩

theorem sharedWitness_ok (M : Mont) {s : State} {B : Addr} {Z w c bm : Nat} (hw4 : 4 ≤ w) (hw128 : w ≤ 128)
    (hc : MrCtx s B Z w c bm)
    (hR2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hb : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w)
    {rp : Addr} {used : Nat} {r : List Byte} (hR : word s.mem B (8 * kRand) = rp)
    (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hsrc : Src s B Z rp r) (hlen : used + 8 * w ≤ r.length) :
    WP isa (seqs (mrWitness ++ ([M.mm aXm aX aR2, copyA aB aXm] : List (Prog isa)))) s fun t =>
      MrCtx t B Z w c
        ((Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).1 *
          2 ^ (64 * w) % c) ∧
      wv t.mem B (slot w aXm) w =
        (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).1 *
          2 ^ (64 * w) % c ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kU) =
        mask (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).2 ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (used + 8 * w) ∧
      Frm B (witnessRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.ws.scr.nowrap
  have hZ := hc.ws.hZ
  have hw' : w < 2 ^ 31 := by omega_using [hw128]
  have hRc : Nat.Coprime (2 ^ (64 * w)) c := VG.Proof.Bignum.coprime_pow2 hodd _
  have hc0 : 0 < c := by omega_using [hc1]
  have sl : ∀ {j : Nat}, j < 16 → slot w j + 8 * (w + 2) ≤ Z := fun hj => by
    have := slot_lt (w := w) hj; omega_using [hZ, this]
  have sR2 := sl (show aR2 < 16 by decide)
  have sB := sl (show aB < 16 by decide)
  have sY := sl (show aY < 16 by decide)
  have sXm := sl (show aXm < 16 by decide)
  refine wp_seqs_append (by simp [mrWitness]) (by simp) ?_
  refine WP.mono (mrWitness_ok hc hw4 hw128 hodd hb hR hU hK (Src.seg hsrc hlen) (by
    simp only [VG.Proof.RsaKeyGen.seg, List.length_take, List.length_drop]; omega_using [hlen]))
    fun s₁ ⟨hc₁, hx₁, hu₁, hus₁, hf₁, k₁⟩ => ?_
  generalize Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w))) = wt
    at hx₁ hu₁ ⊢
  have hR2₁ : wv s₁.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c := by
    rw [hf₁.wv_eq (d := slot w aR2) (k := w) (by rd_disj) (by omega_using [hn, sR2])]; exact hR2
  simp only [seqs]
  -- `b R mod c` into `aXm`.
  have hg₁ := hc₁.good
  refine WP.seq (WP.mono (M.mm_ok hg₁.1 hg₁.2 hc₁.ws.w1 hw' (o := aXm) (a := aX) (b := aR2) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc₁.inv
    (by rw [hR2₁, hc₁.n]; exact Nat.mod_lt _ hc0)) fun s₂ ⟨_, hlt₂, hy₂, ha₂, k₂⟩ => ?_)
  rw [hc₁.n] at hlt₂ hy₂
  rw [hx₁, hR2₁] at hy₂
  have hXm : wv s₂.mem B (slot w aXm) w = wt.1 * 2 ^ (64 * w) % c := by
    rw [← Nat.mod_eq_of_lt hlt₂]
    refine VG.Proof.Bignum.mont_cancel hRc ?_
    rw [hy₂, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  have f₂ : Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))]
      s₁.mem s₂.mem := Frm.of_arrays ha₂ (by simp)
  have hc₂ : MrCtx s₂ B Z w c bm := hc₁.of_frm f₂ (by kmut) k₂ (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
  -- `[aB] := b R mod c`.
  refine WP.mono (copyA_ok hc₂.ws (o := aB) (a := aXm) (by decide) (by decide) (by decide))
    fun s₃ ⟨hv₃, o₃, _, _, k₃⟩ => ?_
  rw [hXm] at hv₃
  have f₃ : Frm B [(slot w aB, 8 * (w + 2))] s₂.mem s₃.mem :=
    Frm.of_outside (o₃.mono (o' := slot w aB) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_using [])) (by simp)
  have hc₃ := hc₂.setB f₃ (by kmut) k₃ (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) hv₃
  have f13 : Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)),
      (slot w aXm, 8 * (w + 2)), (slot w aB, 8 * (w + 2))] s₁.mem s₃.mem :=
    (f₂.mono (by simp)).trans (f₃.mono (by simp))
  refine ⟨hc₃, ?_, ?_, ?_, ?_, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · rw [f₃.wv_eq (d := slot w aXm) (k := w) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (by omega_using [hn, sXm])]
    exact hXm
  · rw [f13.wv_eq (d := slot w aR2) (k := w) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (by omega_using [hn, sR2])]
    exact hR2₁
  · rw [f13.word_eq (d := 8 * kU) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [kU]; omega_using [])]
    exact hu₁
  · rw [f13.word_eq (d := 8 * kUsed) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [kUsed, sFn]; omega_using [])]
    exact hus₁
  · exact (hf₁.mono (fun r hr => List.mem_append_left _ hr)).trans
      (f13.mono (fun r hr => List.mem_append_right _ hr))

end VG.Proof.RsaKeyGen.AArch64

end

end


/-! # RSA's prepared witness and a generic shared round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.MillerRabin VG.Proof.MillerRabin.AArch64
open VG.Proof.Rsa (slot_lt)
open VG.Proof.MlKem.AArch64 (Keep)

def sharedMidRanges (w : Nat) : List (Nat × Nat) := witnessRanges w ++ Caller.callRanges w

/-- The kernel's calls' ranges, in the header and in the arrays. -/
theorem sharedKernel_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [(8, 8), (184, 8), (208, 8), (232, 8), (240, 8)]
    [(7, 1), (2, 1), (3, 1), (5, 1), (6, 1), (8, 1), (11, 16)] (Caller.callRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append, Caller.callRanges,
    mutRanges, Proof.MillerRabin.Round.compact, List.map_cons, List.map_nil, Caller.pad, aOne, Proof.Rsa.Mont.arrAt,
    Proof.Rsa.Mont.hdrBytes] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr ⟨(7, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inr ⟨(2, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(3, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(5, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(6, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(8, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(11, 16), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩

theorem sharedMidRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w
    ([(216, 8), (0, 8)] ++ [(8, 8), (184, 8), (208, 8), (232, 8), (240, 8)])
    ([(1, 1), (2, 1), (3, 1), (5, 1), (8, 1)] ++ [(7, 1), (2, 1), (3, 1), (5, 1), (6, 1), (8, 1), (11, 16)])
    (sharedMidRanges w) :=
  VG.Proof.RsaKeyGen.shape_append (witnessRanges_shape w) (sharedKernel_shape w)

theorem sharedKernel_hdr (w j : Nat) (hj : j ∈ [0, 16, 17, 18, 19, 20, 21, 22, 24, 25, 27]) :
    ∀ r ∈ Caller.callRanges w, 8 * j + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * j := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact VG.Proof.RsaKeyGen.hdr_of_shape (sharedKernel_shape w) (by decide) (by decide)

private theorem kernel_r2 (w : Nat) :
    ∀ r ∈ Caller.callRanges w, slot w aR2 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aR2 :=
  VG.Proof.RsaKeyGen.arr_of_shape (sharedKernel_shape w) (by decide) (by decide) (by omega_using [])

private theorem witness_exp (w : Nat) : ∀ r ∈ witnessRanges w, r.1 + r.2 ≤ slot w aE := by
  intro r hr
  apply roundRanges_lt w r
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hr))

theorem sharedMid_ok (M : Mont) (R : Kernel) {s : State} {B : Addr} {Z w c bm : Nat}
    (h4 : 4 ≤ w) (h128 : w ≤ 128) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hc : MrCtx s B Z w c bm) (he : ECtx s.mem B w c)
    (hR2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c) (hc1 : 1 < c)
    (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c)
    {rp : Addr} {used : Nat} {r : List Byte}
    (hR : word s.mem B (8 * kRand) = rp) (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w)) (hsrc : Src s B Z rp r)
    (hlen : used + 8 * w ≤ r.length)
    {i uni ch : Nat} (hI : word s.mem B (8 * kI) = BitVec.ofNat 64 i)
    (hN : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni) (hC : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch) :
    WP isa (seqs ((mrWitness ++ ([M.mm aXm aX aR2, copyA aB aXm] : List (Prog isa))) ++ R.run)) s fun t =>
      (∃ bm', MrCtx t B Z w c bm') ∧ ECtx t.mem B w c ∧
      word t.mem B (8 * kFlag) = mask (passOf c w used r) ∧
      word t.mem B (8 * kI) = BitVec.ofNat 64 i ∧ word t.mem B (8 * kUni) = BitVec.ofNat 64 uni ∧
      word t.mem B (8 * kChecks) = BitVec.ofNat 64 ch ∧
      word t.mem B (8 * kU) = mask (wtOf c w used r).2 ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (used + 8 * w) ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c ∧
      Frm B (sharedMidRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have ho : c % 2 = 1 := hsh.1
  have hc3 : 3 ≤ c := by omega_arith
  obtain ⟨_, hb, _⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_arith) hsh
  have hn := hc.ws.scr.nowrap
  have hz := hc.ws.hZ
  refine wp_seqs_append (by simp [mrWitness]) R.nonempty ?_
  refine WP.mono (sharedWitness_ok M h4 h128 hc hR2 ho hc1 hb hR hU hK hsrc hlen) ?_
  rintro u ⟨hcu, hx, hr2, hu, hus, hfrm, hk⟩
  have heu : ECtx u.mem B w c := he.of_frm hfrm (fun r hr => Or.inr (witness_exp w r hr)) (by omega_arith)
  have hx' : wv u.mem B (slot w aXm) w = (wtOf c w used r).1 % c * 2 ^ (64 * w) % c := by
    simpa only [wtOf, Nat.mod_mul_mod] using hx
  refine WP.mono (R.ok hcu heu h4 h128 hEZ ho hc3 hx') ?_
  rintro t ⟨hct, het, hf, hfr, kt⟩
  have hfm : Frm B (sharedMidRanges w) s.mem t.mem :=
    (hfrm.mono (fun r hr => List.mem_append_left _ hr)).trans
      (hfr.mono (fun r hr => List.mem_append_right _ hr))
  refine ⟨hct, het, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfm, (hk.trans kt).mono (by decide)⟩
  · simpa only [Proof.MillerRabin.Round.round, passOf] using hf
  · rw [hfm.word_eq (d := 8 * kI) ?_ (by simp only [kI, kElen, sFn]; omega_arith)]
    · exact hI
    · intro r hr
      rcases List.mem_append.mp hr with hw | hk
      · simp only [witnessRanges, witRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) <;> rd_disj
      · exact sharedKernel_hdr w kI (by simp [kI, kElen, sFn]) r hk
  · rw [hfm.word_eq (d := 8 * kUni) ?_ (by simp only [kUni, kP, sFn]; omega_arith)]
    · exact hN
    · intro r hr
      rcases List.mem_append.mp hr with hw | hk
      · simp only [witnessRanges, witRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) <;> rd_disj
      · exact sharedKernel_hdr w kUni (by simp [kUni, kP, sFn]) r hk
  · rw [hfm.word_eq (d := 8 * kChecks) ?_ (by simp only [kChecks, kE, sFn]; omega_arith)]
    · exact hC
    · intro r hr
      rcases List.mem_append.mp hr with hw | hk
      · simp only [witnessRanges, witRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) <;> rd_disj
      · exact sharedKernel_hdr w kChecks (by simp [kChecks, kE, sFn]) r hk
  · rw [hfr.word_eq (sharedKernel_hdr w kU (by simp [kU])) (by simp only [kU]; omega_arith)]
    exact hu
  · rw [hfr.word_eq (sharedKernel_hdr w kUsed (by simp [kUsed, sFn])) (by simp only [kUsed, sFn]; omega_arith)]
    exact hus
  · have hslot := VG.Proof.Rsa.slot_lt (w := w) (show aR2 < 16 by decide)
    rw [hfr.wv_eq (kernel_r2 w) (by omega_arith)]
    exact hr2

/-- The round's scratch areas plus RSA's status and counters. -/
def sharedRoundRanges (w : Nat) : List (Nat × Nat) :=
  sharedMidRanges w ++ [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)]

theorem sharedRoundRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w
    ([(216, 8), (0, 8)] ++ [(8, 8), (184, 8), (208, 8), (232, 8), (240, 8)] ++ [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)])
    ([(1, 1), (2, 1), (3, 1), (5, 1), (8, 1)] ++ [(7, 1), (2, 1), (3, 1), (5, 1), (6, 1), (8, 1), (11, 16)] ++ [])
    (sharedRoundRanges w) :=
  VG.Proof.RsaKeyGen.shape_append (sharedMidRanges_shape w) (VG.Proof.RsaKeyGen.shape_self w _)


theorem sharedRound_ok (M : Mont) (R : Kernel) {s : State} {B : Addr} {Z w c bm : Nat} (hw4 : 4 ≤ w) (hw128 : w ≤ 128)
    (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hc : MrCtx s B Z w c bm) (hE : ECtx s.mem B w c)
    (hR2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c) (hc1 : 1 < c)
    (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c)
    {rp : Addr} {used : Nat} {r : List Byte} (hR : word s.mem B (8 * kRand) = rp)
    (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hsrc : Src s B Z rp r) (hlen : used + 8 * w ≤ r.length)
    {i uni ch : Nat} (hI : word s.mem B (8 * kI) = BitVec.ofNat 64 i)
    (hN : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni) (hC : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch)
    (hi : i < 2 ^ 61) (huni : uni < 2 ^ 61) (hch : ch < 2 ^ 62) :
    WP isa (seqs (mrRoundWith M.mm R.run)) s fun t =>
      (∃ bm', MrCtx t B Z w c bm') ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (used + 8 * w) ∧
      word t.mem B (8 * kStat) = BitVec.ofNat 64
        (if Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2
            (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).1 then
          (if i + 1 < 17 ∨ uni + (Spec.RsaKeyGen.witness (c - 1)
              (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).2.toNat < ch then 4 else 1)
        else 3) ∧
      (Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2
          (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).1 = true →
        word t.mem B (8 * kI) = BitVec.ofNat 64 (i + 1) ∧
        word t.mem B (8 * kUni) = BitVec.ofNat 64 (uni + (Spec.RsaKeyGen.witness (c - 1)
          (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).2.toNat)) ∧
      Frm B (sharedRoundRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.ws.scr.nowrap
  have hZ := hc.ws.hZ
  have sR2 : slot w aR2 + 8 * (w + 2) ≤ Z := by have := slot_lt (w := w) (show aR2 < 16 by decide); omega_using [hZ, this]
  simp only [mrRoundWith]
  refine wp_seqs_append (by simp [mrWitness]) (by simp) ?_
  refine WP.mono (sharedMid_ok M R hw4 hw128 hEZ hc hE hR2 hc1 hsh hR hU hK hsrc hlen hI hN hC)
    fun s₂ ⟨⟨bm₂, hc₂⟩, he₂, hfl₂, hI₂, hN₂, hC₂, hU₂, hUs₂, hR2₂, hf02, k₁₂⟩ => ?_
  simp only [wtOf, passOf] at hc₂ hU₂ hfl₂
  generalize Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w))) = wt
    at hc₂ hU₂ hfl₂ ⊢
  generalize Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1
    (Spec.Rsa.splitTwos (c - 1)).2 wt.1 = f at hfl₂ ⊢
  refine WP.mono (roundTail_ok hc₂.ws hfl₂ hI₂ hU₂ hN₂ hC₂ (by omega_arith) (by omega_using [huni]) hch) fun t ⟨hm, k⟩ => ?_
  have hft : Frm B [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)] s₂.mem t.mem := by
    rw [hm]
    have wI := Frm.of_outside (rs := [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)])
      (writeW_outside s₂.mem B (BitVec.ofNat 64 (i + 1)) (d := 8 * kI) (by simp only [kI, kElen, sFn]; omega_using []))
      (by simp)
    cases f
    · exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by simp only [kStat, sFn]; omega_using [])) (by simp)
    · exact (wI.trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kUni) (by simp only [kUni, kP, sFn]; omega_using []))
        (by simp))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by simp only [kStat, sFn]; omega_using []))
        (by simp))
  refine ⟨⟨bm₂, hc₂.of_frm hft (by kmut) k (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)⟩,
    ?_, ?_, ?_, ?_, ?_, (k₁₂.trans k).mono (by decide)⟩
  · rw [hft.wv_eq (d := slot w aR2) (k := w) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (by omega_using [hn, sR2])]; exact hR2₂
  · rw [hft.word_eq (d := 8 * kUsed) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [kUsed, sFn]; omega_using [])]; exact hUs₂
  · rw [hm]; cases f <;> simp only [↓reduceIte, Bool.false_eq_true, word_writeW_self]
  · intro hf
    rw [hm, hf]
    simp only [↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        word_writeW_self]
    · rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · exact (hf02.mono fun r hr => List.mem_append_left _ hr).trans (hft.mono (by simp))

/-- Every write remains below the exponent array, including caller save slots. -/
theorem sharedRoundRanges_lt (w : Nat) : ∀ r ∈ sharedRoundRanges w, r.1 + r.2 ≤ slot w aE := by
  intro r hr
  simp only [sharedRoundRanges, sharedMidRanges, witnessRanges, witRanges, Caller.callRanges,
    mutRanges, Proof.MillerRabin.Round.compact, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Caller.pad, slot, hdrBytes, aOne, aE, aX, aAcc, aTmp, aXm, aB,
      kUsed, kU, kI, kUni, kStat, kElen, kP, sFn, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
    omega_arith

end VG.Proof.RsaKeyGen.AArch64
