module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeState
public import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeSetup
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontSetup
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeState
meta import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeSetup
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontSetup
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr

/-! # Constant-time Montgomery initialization for full and padded DSA candidates -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64

def PrimeSetupBefore (p : PrimeParams) (s : State) : Prop :=
  (∃ mi, Good s p.B p.Z p.w mi) ∧ wv s.mem p.B (slot p.w aN) p.w = p.N ∧ p.w ≤ 48

def PrimeParams.product (p : PrimeParams) (mi : BitVec 64) : ProductPublic :=
  ⟨⟨p.B, p.Z, p.w, mi⟩, p.N, p.dims.z, by change 2 ≤ p.w; have := p.dims.w4; omega,
    by change p.w < 2 ^ 31; have := p.dims.w128; omega⟩

def PrimeInverse (p : PrimeParams) (s : State) : Prop := ∃ mi, SetupPre (p.product mi) s

theorem primeHeadArgs_state {p : PrimeParams} {s : State} (h : PrimeSetupBefore p s) :
    WP isa (.block [.mov .r10 (.mem (hdr (sArr aN))), .mov .r12 (.mem (hdr sW))]) s
      (fun t => t.gpr .rdi = p.B ∧ t.gpr .r10 = off p.B (slot p.w aN)) := by
  obtain ⟨mi, hg⟩ := h.1
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot p.w 8 hi; have := p.dims.z; omega)
  xrun [State.ea, hdr, hdrOff, hg.rdi, hl (sArr aN) (by decide), hl sW (by decide), hg.hdr.harr aN (by decide)]

theorem primeHead_ct : RelCT isa (Two PrimeSetupBefore)
    (.block Impl.Ffdh.X86_64.ParameterCandidate.prepareHead) (fun _ _ => True) := by
  unfold Impl.Ffdh.X86_64.ParameterCandidate.prepareHead
  change RelCT isa (Two PrimeSetupBefore) (.block
    (([.mov .r10 (.mem (hdr (sArr aN))), .mov .r12 (.mem (hdr sW))] : List Instr) ++
      ([.mov .rbx (.mem (at0 .r10))] ++ Impl.Bignum.X86_64.minv ++
        [.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)]))) _
  apply RelCT.block_append (M := isa)
  refine RelCT.seq (two_post (two_taint [.rdi] ?_ (by taint_decide))
    (fun _ _ h => primeHeadArgs_state h)) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    obtain ⟨mi, hs⟩ := hs.1
    obtain ⟨mi', ht⟩ := ht.1
    exact hs.rdi.trans ht.rdi.symm
  · exact two_taint [.rdi, .r10] (by
      intro p s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.trans ht.2.symm) (by taint_decide)

theorem primeHead_inverse {p : PrimeParams} {s : State} (h : PrimeSetupBefore p s) :
    WP isa (.block Impl.Ffdh.X86_64.ParameterCandidate.prepareHead) s (PrimeInverse p) := by
  obtain ⟨mi, hg⟩ := h.1
  have hw := p.dims.w4
  have hnow := hg.scr.nowrap
  have hfit := p.dims.z
  have hodd : (word s.mem p.B (slot p.w aN)).toNat % 2 = 1 := by
    rw [← wv_mod64 (n := p.w) _ _ _ (by omega), h.2.1,
      Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ 64 by decide)]
    exact p.odd
  refine WP.mono (msHead_ok hg p.dims.z hodd) fun t ⟨ht, hi, _, _, _, hm, _⟩ => ?_
  have hn : wv t.mem p.B (slot p.w aN) p.w = p.N := by
    rw [hm, hdrStore_wv _ _ _ (by decide) (by decide) (by omega)]
    exact h.2.1
  have hinv : ((word t.mem p.B (slot p.w aN)).toNat * (t.gpr .r15).toNat + 1) % 2 ^ 64 = 0 := by
    rw [hm, hdrStore_word _ _ _ (by decide) (by decide) (by omega)]
    exact hi
  exact ⟨t.gpr .r15, ⟨ht, hn, hinv⟩, h.2.2, by change 1 < p.N; have := p.n3; omega, p.odd⟩

theorem primeInverse_public {s t : State} (h : Two PrimeInverse s t) : Two SetupPre s t := by
  obtain ⟨p, ⟨mi, hs⟩, ⟨mi', ht⟩⟩ := h
  have hw := p.dims.w4
  have low₁ : (word s.mem p.B (slot p.w aN)).toNat = p.N % 2 ^ 64 := by
    rw [← wv_mod64 (n := p.w) _ _ _ (by omega), show wv s.mem p.B (slot p.w aN) p.w = p.N from hs.1.modulus]
  have low₂ : (word t.mem p.B (slot p.w aN)).toNat = p.N % 2 ^ 64 := by
    rw [← wv_mod64 (n := p.w) _ _ _ (by omega), show wv t.mem p.B (slot p.w aN) p.w = p.N from ht.1.modulus]
  have hi := hs.1.inverse
  have hi' := ht.1.inverse
  change ((word s.mem p.B (slot p.w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0 at hi
  change ((word t.mem p.B (slot p.w aN)).toNat * mi'.toNat + 1) % 2 ^ 64 = 0 at hi'
  rw [low₁] at hi
  rw [low₂] at hi'
  have he := minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact p.odd) hi hi'
  subst mi'
  exact ⟨p.product mi, hs, ht⟩

theorem primeR2_ct (M : Mont) : RelCT isa (Two PrimeSetupBefore)
    (Impl.Dsa.X86_64.Generation.primeR2 M.mm) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.primeR2
  exact RelCT.seq (two_post primeHead_ct (fun _ _ h => primeHead_inverse h))
    ((constants_ct M).mono (fun _ _ h => primeInverse_public h) (fun _ _ h => h))

end VG.Proof.Dsa.X86_64.Generation
