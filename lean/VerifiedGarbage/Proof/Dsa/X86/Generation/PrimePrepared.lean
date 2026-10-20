module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeInputs
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Prime
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimePrepare

/-! # Prepare the candidate context and saved odd exponent exactly once -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

theorem primePrepared_ok {G : PrimeConfig} {s : State} (R : PrimeInputs G s) :
    WP isa (primePrepare G.len) s fun t => PrimeReady G t ∧
      t.mem.readW (off G.base primeUsed) 32 = s.mem.readW (off G.base primeUsed) 32 ∧
      Outs G.base (primePrepareWrites G.n) s.mem t.mem ∧ Keeps powerClob s t := by
  have width := G.width
  have positive : 0 < G.n := by have := G.lenMin; unfold PrimeConfig.n; omega
  have room : primeExponent + 8 * G.n ≤ G.size := G.room
  unfold primePrepare
  refine WP.seq (WP.mono (contextSetup_ok (n := G.n) R.scratch positive (by omega)
    (by unfold contextBytes slot stride primeExponent at *; omega) R.modulus R.gtOne R.odd)
    fun a ⟨Ca, one, r2, Oa, Ka⟩ => ?_)
  refine WP.mono (primePrepare_ok Ca width room one r2 R.odd) fun t ⟨Ct, onet, r2t, twos, exponent, Ot, Kt⟩ => ?_
  have O : Outs G.base (primePrepareWrites G.n) s.mem t.mem :=
    (Oa.mono (fun _ hr => List.mem_append_left _ hr)).trans
      (Ot.mono (fun _ hr => List.mem_append_right _ hr))
  have K := Ka.trans (Kt.mono (by decide))
  have header (d : Nat) (hd : d = primeTape ∨ d = primeTapeLen ∨ d = primeWitness ∨ d = primeUsed) :=
    primePrepareWrites_header O width hd
  exact ⟨⟨Ct, onet, r2t, exponent, twos,
    (header _ (.inl rfl)).trans R.tape,
    (header _ (.inr (.inl rfl))).trans R.tapeLen,
    (header _ (.inr (.inr (.inl rfl)))).trans R.witness,
    by intro i hi; rw [K.2.1, K.2.2]; exact R.tapeRead i hi,
    by intro i hi; rw [K.2.1, K.2.2]; exact R.witnessRead i hi,
    by intro i hi; rw [K.2.1, K.2.2]; exact R.witnessReadByte i hi,
    by intro i hi; rw [K.2.2]; exact R.witnessWrite i hi⟩,
    header _ (.inr (.inr (.inr rfl))), O, K⟩
end VG.Proof.Dsa.X86.Generation
