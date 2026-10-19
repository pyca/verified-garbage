module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Arguments
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeBytes
import VerifiedGarbage.Proof.Framework.Omega

/-! # Initialize all primality arguments from the persistent native frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.Generation
open VG.Impl.RsaKeyGen.X86_64.Candidate

private theorem prime_arguments_fit {candidate len draw checks : Nat}
    (hc : candidate < 2 ^ 31) (hl : len < 2 ^ 31) (hd : draw < 2 ^ 31) (hk : checks < 2 ^ 31) :
    ∀ a ∈ primeArguments candidate len draw checks, argumentFits a := by
  intro a ha
  simp only [primeArguments, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only [argumentFits]
  · decide
  · exact ⟨by decide, by decide, hd⟩
  · exact ⟨by decide, by decide, hl⟩
  · exact ⟨by decide, by decide, hk⟩
  · exact ⟨by decide, by decide, by decide, hc⟩
  · decide
  · decide
  · decide

/-- The only inputs to setup are the candidate location, public sizes,
and frame words already retained by the hash helpers. -/
theorem primeArguments_ok {P : PrimeParams} {s : State} {mi : BitVec 64} {used candidate : Nat}
    {W : Nat → BitVec 64} (hg : Good s P.B P.Z P.w mi)
    (hc : candidate < 2 ^ 31) (hk : P.checks < 2 ^ 31)
    (hsp : s.gpr .rsp = P.sp)
    (hr : ∀ k < 37, InRegions (s.rd ++ s.wr) (off P.sp (8 * k)) 8)
    (hwords : ∀ k < 37, word s.mem P.sp (8 * k) = W k)
    (hsep : ∀ k < 37, ∀ j < 32, Mem.Sep (off P.sp (8 * k)) 8 (off P.B (8 * j)) 8)
    (hwp : W 5 + BitVec.ofNat 64 VG.Impl.Dsa.Generation.Layout.witness = P.p)
    (hwr : W 13 = P.rp) (hwl : W 15 = BitVec.ofNat 64 P.rand.length)
    (hwu : W 16 = BitVec.ofNat 64 used)
    (htape : Src s P.B P.Z P.rp P.rand)
    (hout : ∀ i < P.len, InRegions s.wr (off P.p i) 1) :
    WP isa (.block (headerArguments (primeArguments candidate P.len P.drawBytes P.checks))) s fun t =>
      PrimeArguments P mi used t ∧ word t.mem P.B 160 = W 5 + BitVec.ofNat 64 candidate ∧
      Outside P.B 128 128 s.mem t.mem ∧ Keep [.rax] s t := by
  have hf := prime_arguments_fit (len := P.len) (draw := P.drawBytes) hc (by have := P.lenDraw; have := P.drawMax; omega)
    (by have := P.drawMax; omega) hk
  have hB : Scr s P.B 256 := by
    simpa only [off, BitVec.add_zero] using hg.scr.sub (o := 0) (n := 256) P.z256 (by decide)
  refine WP.mono (headerArguments_ok _ hf hB hg.rdi hsp hr hwords hsep) fun t ⟨hm, kt⟩ => ?_
  have ho : Outside P.B 128 128 s.mem t.mem := by
    rw [hm]; exact argumentWrites_outside _ _ _ _ hf
  have wh (k : Nat) (hk32 : k < 32) : word t.mem P.B (8 * k) =
      argumentWords W (fun j => word s.mem P.B (8 * j)) (primeArguments candidate P.len P.drawBytes P.checks) k := by
    rw [hm]; exact argumentWrites_word _ _ _ _ hf hk32
  have hg' : Good t P.B P.Z P.w mi :=
    ⟨hg.scr.congr kt.2.2, (kt.gpr (by decide)).trans hg.rdi, hg.hdr.of_frm (Frm.of_outside ho (List.mem_singleton_self _)) (by simp)⟩
  refine ⟨⟨hg', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ho, kt⟩
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
    exact ho a (Or.inr (Nat.le_trans P.z256 ha))
  · intro i hi; rw [kt.2.2]; exact hout i hi
  · exact (kt.gpr (by decide)).trans hsp
  · exact wh 20 (by decide)

end VG.Proof.Dsa.X86_64.Generation
