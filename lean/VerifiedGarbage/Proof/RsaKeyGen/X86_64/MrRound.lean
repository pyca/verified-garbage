import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWitAll

/-!
# A candidate on x86-64: one round of Miller–Rabin

`roundPre_ok`: the witness `b`, `b R mod c` into `aXm` and `aB`, and
`y := 1` (`R mod c` into `aY`).
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The octets of `rand` from `a`. -/
theorem Src.seg {s : State} {B : Addr} {Z : Nat} {rp : Addr} {r : List Byte} (h : Src s B Z rp r) {a n : Nat}
    (ha : a + n ≤ r.length) : Src s B Z (rp + BitVec.ofNat 64 a) (VG.Proof.RsaKeyGen.seg r a n) := by
  have hl : (VG.Proof.RsaKeyGen.seg r a n).length = n := by
    simp only [VG.Proof.RsaKeyGen.seg, List.length_take, List.length_drop]; omega
  have he : ∀ i, rp + BitVec.ofNat 64 a + BitVec.ofNat 64 i = rp + BitVec.ofNat 64 (a + i) := fun i => by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [he]; exact h.rd (a + i) (by omega)
  · rw [he, h.val (a + i) (by omega)]
    simp only [VG.Proof.RsaKeyGen.seg, List.getElem_take, List.getElem_drop]
  · rw [he]; exact h.out (a + i) (by omega)

/-- What the start of a round changes. -/
def preRanges (w : Nat) : List (Nat × Nat) :=
  witRanges w ++ [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2)),
    (slot w aB, 8 * (w + 2)), (slot w aY, 8 * (w + 2))]

theorem roundPre_eq (mul : Nat → Nat → Nat → Prog isa) :
    mrWitness ++ [mul aXm aX aR2,
      .block ([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aXm)))] ++ extBase aB .rbx), copyWords,
      .block ([.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aY)))] ++ extBase aR1 .rsi), copyWords] =
    mrWitness ++ ([mul aXm aX aR2] ++
      ([.block ([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aXm)))] ++ extBase aB .rbx), copyWords] ++
      [.block ([.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aY)))] ++ extBase aR1 .rsi), copyWords])) := rfl

/-- `MrCtx` with a new witness. -/
theorem MrCtx.setB {s t : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm bm' : Nat} {rs : List (Nat × Nat)}
    (hc : MrCtx s B Z w mi c bm) (hd : MrDims B Z w) (hf : Frm B rs s.mem t.mem) (hs : Scr t B Z)
    (hdi : t.gpr .rdi = B) (hh : ∀ r ∈ rs, 128 ≤ r.1)
    (dN : ∀ r ∈ rs, slot w aN + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aN)
    (d1 : ∀ r ∈ rs, slot w aR1 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aR1)
    (dm : ∀ r ∈ rs, slot w aRm1 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aRm1)
    (hb : wv t.mem B (slot w aB) w = bm') : MrCtx t B Z w mi c bm' := by
  have hn := hc.good.scr.nowrap
  have hx := hd.x
  have hb1 : slot w aRm1 + 8 * (w + 2) ≥ slot w aR1 + 8 * w := by unfold slot aRm1 aR1; omega
  have hb0 : slot w aRm1 + 8 * (w + 2) ≥ slot w aN + 8 * w := by unfold slot aRm1 aN; omega
  have := hd.w4
  refine ⟨⟨hs, hdi, Hdr.of_frm hc.good.hdr hf hh⟩, ?_, ?_, hb, ?_, ?_⟩
  · rw [hf.word_eq (d := slot w aN) (fun r hr => by have := dN r hr; omega) (by omega)]; exact hc.inv
  · rw [hf.wv_eq dN (by omega)]; exact hc.n
  · rw [hf.wv_eq d1 (by omega)]; exact hc.r1
  · rw [hf.wv_eq dm (by omega)]; exact hc.rm1

/-- The start of a round. -/
theorem roundPre_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm : Nat}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm)
    (hR2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hb : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w)
    {rp : Addr} {used : Nat} {r : List Byte} (hR : word s.mem B (8 * kRand) = rp)
    (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hsrc : Src s B Z rp r) (hlen : used + 8 * w ≤ r.length) :
    WP isa (seqs (mrWitness ++ [M.mm aXm aX aR2,
      .block ([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aXm)))] ++ extBase aB .rbx), copyWords,
      .block ([.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aY)))] ++ extBase aR1 .rsi), copyWords])) s
      fun t =>
      MrCtx t B Z w mi c
        ((Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).1 *
          2 ^ (64 * w) % c) ∧
      wv t.mem B (slot w aY) w = 2 ^ (64 * w) % c ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kU) =
        mask (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).2 ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (used + 8 * w) ∧
      Frm B (preRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hg := hc.good
  have hZ := hd.z
  have hXZ := hd.x
  have hw4 := hd.w4
  have hw' : w < 2 ^ 31 := by have := hd.w64; omega
  have hn := hg.scr.nowrap
  have hRc : Nat.Coprime (2 ^ (64 * w)) c := VG.Proof.Bignum.coprime_pow2 hodd _
  have hc0 : 0 < c := by omega
  rw [roundPre_eq]
  refine wp_seqs_append (by simp [mrWitness]) (by simp) ?_
  refine WP.mono (mrWitness_ok hd hc hodd hb hR hU hK (VG.Proof.RsaKeyGen.X86_64.Src.seg hsrc hlen) (by
    simp only [VG.Proof.RsaKeyGen.seg, List.length_take, List.length_drop]; omega))
    fun s₁ ⟨hc₁, hx₁, hu₁, hus₁, hf₁, k₁⟩ => ?_
  generalize hwt : Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w))) = wt
    at hx₁ hu₁ ⊢
  have hR2₁ : wv s₁.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c := by
    rw [hf₁.wv_eq (d := slot w aR2) (k := w) (by simp only [witRanges]; rng_disj)
      (by have := slot_le (w := w) (show aR2 < 8 by decide); omega)]; exact hR2
  -- `b R mod c` into `aXm`.
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (M.mm_ok hc₁.good hZ (by omega) hw' (o := aXm) (a := aX) (b := aR2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hc₁.inv
    (by rw [hR2₁, hc₁.n]; exact Nat.mod_lt _ hc0)) fun s₂ ⟨hg₂, hlt₂, hy₂, ha₂, k₂⟩ => ?_
  rw [hc₁.n] at hlt₂ hy₂
  rw [hx₁, hR2₁] at hy₂
  have hXm : wv s₂.mem B (slot w aXm) w = wt.1 * 2 ^ (64 * w) % c := by
    rw [← Nat.mod_eq_of_lt hlt₂]
    refine VG.Proof.Bignum.mont_cancel hRc ?_
    rw [hy₂, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  have hc₂ : MrCtx s₂ B Z w mi c bm := hc₁.of_frm hd (Frm.of_arrays ha₂
    (rs := [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))]) (by simp))
    hg₂.scr hg₂.rdi (by rng_disj) (by rng_disj) (by rng_disj) (by rng_disj) (by rng_disj)
  -- `[aB] := b R mod c`.
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (copyToExt_ok hg₂ hZ (by omega) hw' (a := aXm) (d := aB) (by decide) (by decide)
    (by unfold slot aB aRm1 at *; omega)) fun s₃ ⟨hv₃, ho₃, k₃⟩ => ?_
  rw [hXm] at hv₃
  have hg₃ : Good s₃ B Z w mi := ⟨hg₂.scr.congr k₃.2.2, (k₃.gpr (by decide)).trans hg₂.rdi,
    Hdr.outside hg₂.hdr ho₃ (by unfold slot; omega)⟩
  have hf₃ : Frm B [(slot w aB, 8 * (w + 2))] s₂.mem s₃.mem :=
    Frm.of_outside (ho₃.mono (o' := slot w aB) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega)) (by simp)
  have hc₃ := hc₂.setB hd hf₃ hg₃.scr hg₃.rdi (by rng_disj) (by rng_disj) (by rng_disj) (by rng_disj) hv₃
  -- `[aY] := R mod c`.
  refine WP.mono (copyFromExt_ok hg₃ hZ (by omega) hw' (a := aY) (d := aR1) (by decide) (by decide)
    (by unfold slot aR1 aRm1 at *; omega)) fun t ⟨hv, ho, k⟩ => ?_
  rw [hc₃.r1] at hv
  have hgt : Good t B Z w mi := ⟨hg₃.scr.congr k.2.2, (k.gpr (by decide)).trans hg₃.rdi,
    Hdr.outside hg₃.hdr ho (by unfold slot; omega)⟩
  have hft : Frm B [(slot w aY, 8 * (w + 2))] s₃.mem t.mem :=
    Frm.of_outside (ho.mono (o' := slot w aY) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega)) (by simp)
  have hf23 : Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2)),
      (slot w aB, 8 * (w + 2)), (slot w aY, 8 * (w + 2))] s₁.mem t.mem :=
    ((Frm.of_arrays ha₂ (by simp)).trans (hf₃.mono (by simp))).trans (hft.mono (by simp))
  refine ⟨hc₃.of_frm hd hft hgt.scr hgt.rdi (by rng_disj) (by rng_disj) (by rng_disj) (by rng_disj) (by rng_disj),
    hv, ?_, ?_, ?_, ?_, ((((k₁.trans k₂).trans k₃).trans k).mono (by decide))⟩
  · rw [hf23.wv_eq (d := slot w aR2) (k := w) (by rng_disj)
      (by have := slot_le (w := w) (show aR2 < 8 by decide); omega)]; exact hR2₁
  · rw [hf23.word_eq (d := 8 * kU) (by rng_disj) (by unfold kU sFn; omega)]; exact hu₁
  · rw [hf23.word_eq (d := 8 * kUsed) (by rng_disj) (by unfold kUsed sFn; omega)]; exact hus₁
  · exact (hf₁.mono fun r hr => List.mem_append_left _ hr).trans (hf23.mono (by simp [preRanges, witRanges]))

end VG.Proof.RsaKeyGen.X86_64
