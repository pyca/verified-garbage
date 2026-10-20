module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundPowerCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReady
import VerifiedGarbage.Proof.Dsa.X86.Generation.RestoreExponent
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeEffects
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrepareExponent
import VerifiedGarbage.Proof.Dsa.X86.Generation.CopyCT

/-! # Every witness uses the candidate's saved public exponent and Montgomery context -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

def PrimeRoundAt (G : PrimeConfig) (value : Nat) (s : State) : Prop :=
  PrimeReady G s ∧ wordsVal s.mem G.base (slot G.n 5) G.n = value

def primeRoundPublic (G : PrimeConfig) (value : Nat) : RoundPublic × Nat :=
  (⟨G.base, G.modulus, G.size, value, G.twos - 1⟩, G.exponent)

theorem primeRestore_ok {G : PrimeConfig} {value : Nat} {s : State} (R : PrimeRoundAt G value s) :
    WP isa (restoreExponent G.n) s (RoundPowerAt G.n (2 * G.n) (primeRoundPublic G value)) := by
  have width := G.width
  have bound : G.size ≤ 2 ^ 64 := by have := R.1.context.scr.nowrap; omega
  have positive : 0 < G.n := by have := G.lenMin; unfold PrimeConfig.n; omega
  refine WP.mono (restoreExponent_ok R.1.context.scr positive width G.room G.twosPos R.1.twos)
    fun t ⟨count, exponent, O, K⟩ => ?_
  have F := primeFrame_restore (witness := G.witness.setWidth 64) (len := G.len) O width G.flagRoom bound
  have Rt := R.1.keep F K (by decide) (by decide)
  have value' : wordsVal t.mem G.base (slot G.n 5) G.n = value := by
    rw [← R.2, wordsVal_eq_val32, wordsVal_eq_val32]
    apply O.val32
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [slot, stride, roundCount] <;> omega
    · simp only [slot, stride]; omega
  have room : roundStatus + 4 ≤ G.size := by have := G.flagRoom; unfold roundStatus primeIsUniform at *; omega
  exact ⟨⟨Rt.context, width, room, Rt.one, Rt.r2, count,
    by change G.twos - 1 < 2 ^ 32; have := G.twos32; omega⟩, exponent.trans R.1.exponent, value'⟩

theorem primeRound_ct (G : PrimeConfig) :
    RelCT isa (Two (PrimeRoundAt G)) (.seq (restoreExponent G.n) (round G.n (2 * G.n))) (fun _ _ => True) := by
  have positive : 0 < G.n := by have := G.lenMin; unfold PrimeConfig.n; omega
  refine RelCT.seq (two_post (Ψ := fun value => RoundPowerAt G.n (2 * G.n) (primeRoundPublic G value))
    ((restoreExponent_ct G.n).mono ?_ (fun _ _ h => h)) (fun _ _ R => primeRestore_ok R))
    (two_map (primeRoundPublic G) (fun _ _ h => h) (round_ct G.n (2 * G.n) (by omega) (by omega)))
  rintro s t ⟨value, hs, ht⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  exact BitVec.eq_of_toNat_eq (hs.1.context.scr.edi_toNat.trans ht.1.context.scr.edi_toNat.symm)
end VG.Proof.Dsa.X86.Generation
