module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitGuards
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitValues

/-! # Correct native parameter-generation initialization, including validation -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation

/-- The full initialization result, including invalid public inputs. -/
def InitPost (bits generator : Nat) (m : Mem) (B : Addr) (t : State) : Prop :=
  match Spec.Ffdh.parameterInit bits generator with
  | none => t.gpr .rax = 0 ∧ t.mem = cleared m B
  | some _ => t.gpr .rax = 1 ∧ t.mem = initialized m B bits

private theorem valid_init {bits generator : Nat} (hlo : 512 ≤ bits) (hhi : bits ≤ 8192)
    (hg : generator = 2 ∨ generator = 5) :
    Spec.Ffdh.parameterInit bits generator = some [Spec.Ffdh.parameterAttempts bits,
      (bits + 7) / 8, Spec.Ffdh.parameterEntropy bits, 512 * ((bits + 7) / 8)] := by
  rcases hg with rfl | rfl <;> simp [Spec.Ffdh.parameterInit, hlo, hhi]

private theorem invalid_generator {bits generator : Nat} (h2 : generator ≠ 2) (h5 : generator ≠ 5) :
    Spec.Ffdh.parameterInit bits generator = none := by
  simp [Spec.Ffdh.parameterInit, h2, h5]

private theorem clear_result {s : State} {B : Addr} {bits generator : Nat} {m : Mem}
    (scr : Scr s B 128) (hdi : s.gpr .rdi = B) (hm : s.mem = m)
    (hinvalid : Spec.Ffdh.parameterInit bits generator = none) :
    WP isa clear s (InitPost bits generator m B) := by
  refine WP.mono (clear_ok scr hdi) fun t ⟨ha, ht⟩ => ?_
  simp only [InitPost, hinvalid]
  exact ⟨ha, by simpa only [hm] using ht⟩

private theorem initialize_result {s : State} {B : Addr} {bits generator : Nat} {m : Mem}
    (scr : Scr s B 128) (hdi : s.gpr .rdi = B) (hsi : s.gpr .rsi = BitVec.ofNat 64 bits)
    (hm : s.mem = m) (hlo : 512 ≤ bits) (hhi : bits ≤ 8192) (hg : generator = 2 ∨ generator = 5) :
    WP isa initializeState s (InitPost bits generator m B) := by
  refine WP.mono (initialize_ok scr hdi hsi hhi) fun t ⟨ha, ht⟩ => ?_
  simp only [InitPost, valid_init hlo hhi hg]
  exact ⟨ha, by simpa only [hm] using ht⟩

theorem generator_init_ok {s : State} {B : Addr} {bits generator : Nat} {m : Mem}
    (scr : Scr s B 128) (hdi : s.gpr .rdi = B) (hsi : s.gpr .rsi = BitVec.ofNat 64 bits)
    (hgen : ((s.gpr .rdx).setWidth 32).toNat = generator) (hm : s.mem = m)
    (hlo : 512 ≤ bits) (hhi : bits ≤ 8192) :
    WP isa checkGenerator s (InitPost bits generator m B) := by
  unfold checkGenerator
  refine WP.seq (WP.mono (generator_guard_nat s 2 (by decide)) fun u ⟨⟨he, hmem⟩, k⟩ => ?_)
  rw [hgen] at he
  have hu : u.mem = m := hmem.trans hm
  have hdu : u.gpr .rdi = B := (k.gpr (by decide)).trans hdi
  have hsu : u.gpr .rsi = BitVec.ofNat 64 bits := (k.gpr (by decide)).trans hsi
  refine WP.ite (decide (generator = 2)) he ?_ ?_
  · intro h2
    exact initialize_result (scr.congr k.2.2) hdu hsu hu hlo hhi (Or.inl (of_decide_eq_true h2))
  · intro h2
    have hn2 := of_decide_eq_false h2
    refine WP.seq (WP.mono (generator_guard_nat u 5 (by decide)) fun v ⟨⟨he5, hmem5⟩, kv⟩ => ?_)
    have hgu : ((u.gpr .rdx).setWidth 32).toNat = generator := by
      rw [k.gpr (by decide)]; exact hgen
    rw [hgu] at he5
    have hv : v.mem = m := hmem5.trans hu
    have hdv : v.gpr .rdi = B := (kv.gpr (by decide)).trans hdu
    have hsv : v.gpr .rsi = BitVec.ofNat 64 bits := (kv.gpr (by decide)).trans hsu
    refine WP.ite (decide (generator = 5)) he5 ?_ ?_
    · intro h5
      exact initialize_result ((scr.congr k.2.2).congr kv.2.2) hdv hsv hv hlo hhi
        (Or.inr (of_decide_eq_true h5))
    · intro h5
      exact clear_result ((scr.congr k.2.2).congr kv.2.2) hdv hv
        (invalid_generator hn2 (of_decide_eq_false h5))

theorem checks_ok {s : State} {B : Addr} (scr : Scr s B 128) (hdi : s.gpr .rdi = B) :
    WP isa checks s (InitPost (s.gpr .rsi).toNat ((s.gpr .rdx).setWidth 32).toNat s.mem B) := by
  let bits := (s.gpr .rsi).toNat
  let generator := ((s.gpr .rdx).setWidth 32).toNat
  change WP isa checks s (InitPost bits generator s.mem B)
  unfold checks
  refine WP.seq (WP.mono (lower_guard s) fun u ⟨⟨he, hm⟩, k⟩ => ?_)
  change eval .b u = some (decide (bits < 512)) at he
  have hdu : u.gpr .rdi = B := (k.gpr (by decide)).trans hdi
  refine WP.ite (decide (bits < 512)) he ?_ ?_
  · intro hlow
    refine clear_result (scr.congr k.2.2) hdu hm ?_
    have hn : ¬512 ≤ bits := by omega_using [of_decide_eq_true hlow]
    simp [Spec.Ffdh.parameterInit, hn]
  · intro hlow
    have hlo : 512 ≤ bits := by omega_using [of_decide_eq_false hlow]
    refine WP.seq (WP.mono (upper_guard u) fun v ⟨⟨he2, hm2⟩, kv⟩ => ?_)
    have hbu : (u.gpr .rsi).toNat = bits := by rw [k.gpr (by decide)]
    rw [hbu] at he2
    have hdv : v.gpr .rdi = B := (kv.gpr (by decide)).trans hdu
    have hmv : v.mem = s.mem := hm2.trans hm
    refine WP.ite (decide (8193 ≤ bits)) he2 ?_ ?_
    · intro hhigh
      refine clear_result ((scr.congr k.2.2).congr kv.2.2) hdv hmv ?_
      have hn : ¬bits ≤ 8192 := by omega_using [of_decide_eq_true hhigh]
      simp [Spec.Ffdh.parameterInit, hn]
    · intro hhigh
      have hhi : bits ≤ 8192 := by omega_using [of_decide_eq_false hhigh]
      refine generator_init_ok ((scr.congr k.2.2).congr kv.2.2) hdv ?_ ?_ hmv hlo hhi
      · rw [kv.gpr (by decide), k.gpr (by decide)]
        simp only [bits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · rw [kv.gpr (by decide), k.gpr (by decide)]

theorem init_ok {s : State} {B : Addr} (scr : Scr s B 128) (hdi : s.gpr .rdi = B) :
    WP isa init s (InitPost (s.gpr .rsi).toNat ((s.gpr .rdx).setWidth 32).toNat s.mem B) := by
  unfold init
  refine WP.seq (WP.mono (WP.keep [.rdx] (Q := fun u =>
    u.gpr .rdx = ((s.gpr .rdx).setWidth 32).setWidth 64 ∧ u.mem = s.mem)
    (by xrun []) rfl) fun u ⟨⟨hdx, hm⟩, k⟩ => ?_)
  have hdu : u.gpr .rdi = B := (k.gpr (by decide)).trans hdi
  refine WP.mono (checks_ok (scr.congr k.2.2) hdu) fun t ht => ?_
  have hs : (u.gpr .rsi).toNat = (s.gpr .rsi).toNat := by rw [k.gpr (by decide)]
  have hg : ((u.gpr .rdx).setWidth 32).toNat = ((s.gpr .rdx).setWidth 32).toNat := by
    rw [hdx]
    simp only [BitVec.toNat_setWidth]
    omega
  simpa only [hs, hg, hm] using ht

end VG.Proof.Ffdh.X86_64.Generation
