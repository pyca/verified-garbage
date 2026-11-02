module

public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Body
public import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.ModPowContract
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract

/-! # The probable-prime test meets its contract's functional part -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.X86_64.Spill VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64.ProbablePrime VG.Impl.Dsa.Generation.Layout VG.Proof.MillerRabin.X86_64

/-- No byte of `ws` but those of the test's scratch ranges is in a region the test changes. -/
theorem keeps_of_frame {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) {m : Mem}
    (hf : Frame (changed bits s) s.mem m) :
    Proof.Dsa.ModPow.Keeps (s.gpr .rdi) (s.gpr .rsi).toNat (layout bits).scratch s.mem m := by
  intro i hi hout
  have hw := A.wsBound
  have hlen : len bits ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have h1 := hout (witness, len bits) (by simp [layout])
  have h2 := hout (arithmetic, arithmeticBytes) (by simp [layout])
  have hc : (wsRegion s).Contains (s.gpr .rdi + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  apply hf
  intro r hr hx
  simp only [changed, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · have hd := Offset.disjoint (s.gpr .rdi) (d := i) (n := 1) (e := arithmetic) (k := arithmeticBytes)
      (by simp only at h2; omega) (by omega) (by have : arithmetic + arithmeticBytes ≤ 2 ^ 64 := (by decide); omega)
    exact hd _ (Region.contains_self _ _) hx
  · have hd := Offset.disjoint (s.gpr .rdi) (d := i) (n := 1) (e := witness) (k := len bits)
      (by simp only at h1; omega) (by omega)
      (by have : witness + 384 ≤ 2 ^ 64 := (by decide); have := hlen; omega)
    exact hd _ (Region.contains_self _ _) hx
  · exact (A.stackWs.sub_left (below_frame_sub s)) _ hx hc
  · have hs := frame_stack_sub s (d := 0) (n := 56) (by decide)
    simp only [off, BitVec.add_zero] at hs
    exact A.stackWs _ (hs _ hx) hc
  · exact A.wsUsed _ hc hx

theorem correct (M : Mont) (K : Kernel)
    (ctl : ctlOk (code M.mm K.run) = true) (s : State) (pre : contract.pre s) :
    ∃ trace t, Exec isa (code M.mm K.run) s trace t ∧ abiPreserved s t ∧ contract.post s t := by
  obtain ⟨hb, A⟩ := primeABI_of pre
  have hwl : witness + len (s.gpr .r9).toNat ≤ domainCheck := by
    rcases hb with h | h | h | h | h <;> rw [h] <;> decide
  have hl : 56 ≤ (s.gpr .rsp).toNat := by have : 184 ≤ (s.gpr .rsp).toNat := A.stackLower; omega
  obtain ⟨trace, f, he, hsp, hpost⟩ := alloc_frame_ok (bytes := 56) (by decide) hl
    (Q := fun f => f.gpr .rsp = s.gpr .rsp ∧ BodyPost (s.gpr .r9).toNat s f)
    (WP.mono (body_ok M K hb A) fun t ⟨h1, h2, _, hp⟩ => ⟨h1, h2, freeState_rsp h1, by
      obtain ⟨hr, hu, hm, hg⟩ := hp
      exact ⟨hr, hu, hm, fun r hr' => by
        have : r ≠ .rsp := by revert r; decide
        simp only [freeState, State.setReg, this, ite_false]
        exact hg r hr'⟩⟩)
  obtain ⟨hrax, hused, hframe, hgpr⟩ := hpost
  refine ⟨trace, f, he, ⟨?_, ?_, VG.X86_64.Exec.ctl ctl he⟩, ?_⟩
  · intro r hr
    by_cases h : r = .rsp
    · subst h; exact hsp
    · exact hgpr r (by revert r; decide)
  · apply hframe.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) _ (by decide)
    intro r hr
    simp only [changed, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact A.retWs.sub_right (ws_sub A (by decide))
    · exact A.retWs.sub_right (ws_sub A hwl)
    · exact (Offset.base_disjoint_below _ (by decide)).sub_right (below_frame_sub s)
    · have hs := frame_stack_sub s (d := 0) (n := 56) (by decide)
      simp only [off, BitVec.add_zero] at hs
      exact (Offset.base_disjoint_below _ (by decide)).sub_right hs
    · exact A.retUsed
  · sig_post [contract, Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig, abi,
      argRegs]
    refine ⟨?_, keeps_of_frame hb A hframe, fun b rest h => ?_⟩
    · rw [hrax]
      have st : ∀ o : Option (Bool × Spec.RsaKeyGen.Rand),
          (BitVec.setWidth 32 (BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status o))).toNat =
            Proof.Dsa.ProbablePrime.status o := by
        intro o
        rcases o with _ | ⟨_ | _, _⟩ <;> rfl
      exact st _
    · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero]
      rw [show s.gpr .r8 + BitVec.ofNat 64 0 = s.gpr .r8 from BitVec.add_zero _, hused b rest h]

end VG.Proof.Dsa.X86_64.ProbablePrime
