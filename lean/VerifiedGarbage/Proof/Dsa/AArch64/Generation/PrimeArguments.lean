module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Arguments
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeBytes
import VerifiedGarbage.Proof.Framework.Omega

/-! # Initialize all primality arguments from the persistent native frame -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.Generation
open VG.Impl.RsaKeyGen.AArch64.Candidate

private theorem prime_arguments_fit {candidate len draw checks : Nat}
    (hc : candidate < 2 ^ 16) (hl : len < 2 ^ 16) (hd : draw < 2 ^ 16) (hk : checks < 2 ^ 16) :
    ∀ a ∈ primeArguments candidate len draw checks, argumentFits a := by
  intro a ha
  simp only [primeArguments, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only [argumentFits]
  · decide
  · exact ⟨by decide, by decide, hl⟩
  · exact ⟨by decide, by decide, hd⟩
  · exact ⟨by decide, by decide, hk⟩
  · exact ⟨by decide, by decide, by decide, hc⟩
  · decide
  · decide
  · decide

/-- The only inputs to setup are the candidate location, public sizes,
and frame words already retained by the hash helpers. -/
theorem primeArguments_ok {P : PrimeParams} {s : State} {used candidate : Nat}
    {W : Nat → BitVec 64} (hg : VG.Proof.Rsa.AArch64.Ws s P.B P.Z P.w)
    (hc : candidate < 2 ^ 16) (hk : P.checks < 2 ^ 16)
    {F : Addr} (hsp : s.sp = F)
    (hr : ∀ k < 34, InRegions (s.rd ++ s.wr) (off F (8 * k)) 8)
    (hwords : ∀ k < 34, word s.mem F (8 * k) = W k)
    (hsep : ∀ k < 34, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off P.B (8 * j)) 8)
    (hwp : W 5 + BitVec.ofNat 64 VG.Impl.Dsa.Generation.Layout.witness = P.p)
    (hwr : W 14 = P.rp) (hwl : W 15 = BitVec.ofNat 64 P.rand.length)
    (hwu : W 16 = BitVec.ofNat 64 used)
    (htape : Src s P.B P.Z P.rp P.rand)
    (hout : ∀ i < P.len, InRegions s.wr (off P.p i) 1) :
    WP isa (.block (headerArguments (primeArguments candidate P.len P.drawBytes P.checks))) s fun t =>
      PrimeArguments P used t ∧ word t.mem P.B 160 = W 5 + BitVec.ofNat 64 candidate ∧
      Outside P.B 128 128 s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  have hf := prime_arguments_fit (len := P.len) (draw := P.drawBytes) hc (by have := P.lenDraw; have := P.drawMax; omega)
    (by have := P.drawMax; omega) hk
  have hB : Scr s P.B 256 := by
    simpa only [off, BitVec.add_zero] using hg.scr.sub (o := 0) (n := 256) hg.h256 (by decide)
  refine WP.mono (headerArguments_ok _ hf hB hg.x0 hsp hr hwords hsep) fun t ⟨hm, kt⟩ => ?_
  have ho : Outside P.B 128 128 s.mem t.mem := by
    rw [hm]; exact argumentWrites_outside _ _ _ _ hf
  have wh (k : Nat) (hk32 : k < 32) : word t.mem P.B (8 * k) =
      argumentWords W (fun j => word s.mem P.B (8 * j)) (primeArguments candidate P.len P.drawBytes P.checks) k := by
    rw [hm]; exact argumentWrites_word _ _ _ _ hf hk32
  have hh (d : Nat) (hd : d + 8 ≤ 128) : word t.mem P.B d = word s.mem P.B d :=
    ho.word (Or.inl hd) (by omega)
  have stride : word t.mem P.B 224 = word s.mem P.B 224 := wh 28 (by decide)
  have hg' : VG.Proof.Rsa.AArch64.Ws t P.B P.Z P.w :=
    ⟨hg.scr.congr kt.wr, (kt.gpr _ (by decide)).trans hg.x0,
      (hh 48 (by decide)).trans hg.hw, stride.trans hg.hS,
      fun j hj => (hh (8 * VG.Impl.Bignum.sArr j) (by unfold VG.Impl.Bignum.sArr; omega)).trans (hg.harr j hj),
      hg.hZ, hg.w1, hg.w2⟩
  refine ⟨⟨hg', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ho, kt⟩
  · rw [wh kOut (by decide)]; simpa only [primeArguments, argumentWords, argumentValue,
      kOut, VG.Impl.Bignum.sFn, Nat.reduceAdd, Nat.reduceEqDiff, ite_false, ite_true] using hwp
  · rw [wh kUsedP (by decide)]; rfl
  · rw [wh kLen (by decide)]; rfl
  · rw [wh kRand (by decide)]
    simpa [primeArguments, argumentWords, argumentValue, kRand, VG.Impl.Bignum.sFn] using hwr
  · rw [wh kRandLen (by decide)]
    simpa [primeArguments, argumentWords, argumentValue, kRandLen, VG.Impl.Bignum.sFn] using hwl
  · rw [wh kUsed (by decide)]
    simpa [primeArguments, argumentWords, argumentValue, kUsed, VG.Impl.Bignum.sFn] using hwu
  · rw [wh kChecks (by decide)]; rfl
  · apply htape.congrK _ kt
    intro a ha
    exact ho a (Or.inr (Nat.le_trans hg.h256 ha))
  · intro i hi; rw [kt.wr]; exact hout i hi
  · exact wh 20 (by decide)

end VG.Proof.Dsa.AArch64.Generation
