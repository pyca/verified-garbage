module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeState
import VerifiedGarbage.Proof.Framework.Omega

/-! # The loop's immutable arguments survive one draw and round -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaKeyGen.AArch64

def primeExtras (P : PrimeParams) : List Region := [⟨P.p, P.len⟩]

theorem PrimeParams.z256 (P : PrimeParams) : 256 ≤ P.Z := by
  exact Nat.le_trans (Nat.le_add_right 256 (28 * (8 * (P.w + 2)))) P.room

theorem PrimeParams.exponentRoom (P : PrimeParams) : slot P.w aE + 8 * (P.w + 2) ≤ P.Z := by
  have he : slot P.w aE + 8 * (P.w + 2) = slot P.w 28 := by
    simp only [slot, hdrBytes, aE]; omega_arith
  rw [he]; exact P.room

theorem PrimeParams.extras_disjoint (P : PrimeParams) :
    ∀ r ∈ primeExtras P, Region.Disjoint ⟨P.B, P.Z⟩ r := by
  intro r hr
  change r ∈ [⟨P.p, P.len⟩] at hr
  rw [List.mem_singleton.mp hr]
  exact P.bufferSeparate

theorem PrimeParams.tape_extras (P : PrimeParams) :
    ∀ r ∈ primeExtras P, Region.Disjoint ⟨P.rp, P.rand.length⟩ r := by
  intro r hr
  change r ∈ [⟨P.p, P.len⟩] at hr
  rw [List.mem_singleton.mp hr]
  exact P.tapeBuffer

theorem prime_frame_word {P : PrimeParams} {m m' : Mem} {rs : List (Nat × Nat)} {k : Nat}
    (hn : P.B.toNat + P.Z ≤ 2 ^ 64) (hf : WorkFrame P.B rs (primeExtras P) m m')
    (hk : k < 32) (hh : ∀ r ∈ rs, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k) :
    word m' P.B (8 * k) = word m P.B (8 * k) :=
  hf.word_eq hh (by have := P.z256; omega) hn P.extras_disjoint

theorem PrimeState.advance {P : PrimeParams} {used used' : Nat} {s t : State}
    {rs : List (Nat × Nat)} (h : PrimeState P used s)
    (ht : ModulusReady t P.B P.Z P.w P.N)
    (hu : word t.mem P.B (8 * kUsed) = BitVec.ofNat 64 used')
    (hf : WorkFrame P.B rs (primeExtras P) s.mem t.mem) (hk : Keep mmRegs s t)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ P.Z)
    (hh : ∀ k ∈ [kOut, kUsedP, kLen, kRand, kRandLen, kChecks], ∀ r ∈ rs,
      8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k) : PrimeState P used' t := by
  have hword : ∀ k ∈ [kOut, kUsedP, kLen, kRand, kRandLen, kChecks],
      word t.mem P.B (8 * k) = word s.mem P.B (8 * k) := by
    intro k hmem
    have hk32 : k < 32 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact prime_frame_word h.ready.ws.scr.nowrap hf hk32 (hh k hmem)
  refine ⟨ht, ?_, ?_, ?_, ?_, ?_, hu, ?_, ?_, ?_⟩
  · exact (hword kOut (by simp)).trans h.ptr
  · exact (hword kUsedP (by simp)).trans h.len
  · exact (hword kLen (by simp)).trans h.draw
  · exact (hword kRand (by simp)).trans h.rand
  · exact (hword kRandLen (by simp)).trans h.randLen
  · exact (hword kChecks (by simp)).trans h.checks
  · exact source_of_work h.source hf hr P.tape_extras P.randMax hk
  · intro i hi
    rw [hk.wr]
    exact h.writable i hi

theorem PrimeState.of_mem {P : PrimeParams} {used : Nat} {s t : State}
    (h : PrimeState P used s) (hm : t.mem = s.mem) (hk : Keep mmRegs s t) : PrimeState P used t := by
  have ht := h.ready.of_words P.exponentRoom (fun d _ => by rw [hm]) hk.wr
    ((hk.gpr .x0 (by decide)).trans h.ready.ws.x0)
  exact h.advance (rs := []) ht (by rw [hm]; exact h.used)
    (by rw [hm]; exact WorkFrame.refl _ _ _ _) hk (by simp) (by simp)

end VG.Proof.Dsa.AArch64.Generation
