module

public import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Body
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.ModPowContract
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract

/-! # The probable-prime test meets its contract's functional part -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.ProbablePrime
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Impl.Dsa.AArch64.ProbablePrime VG.Impl.Dsa.Generation.Layout
open VG.Proof.Dsa.AArch64.Generation (allocState freeState alloc_frame_ok)

/-- No byte of `ws` but those of the test's scratch ranges is in a region the test changes. -/
theorem keeps_of_frame {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) {m : Mem}
    (hf : Frame (changed bits s) s.mem m) :
    Proof.Dsa.ModPow.Keeps (s.gpr .x0) (s.gpr .x1).toNat (layout bits).scratch s.mem m := by
  intro i hi hout
  have hw := A.wsBound
  have hlen : len bits ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have h1 := hout (witness, len bits) (by simp [layout])
  have h2 := hout (arithmetic, arithmeticBytes) (by simp [layout])
  have hc : (wsRegion s).Contains (s.gpr .x0 + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  apply hf
  intro r hr hx
  simp only [changed, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · have hd := Offset.disjoint (s.gpr .x0) (d := i) (n := 1) (e := arithmetic) (k := arithmeticBytes)
      (by simp only at h2; omega) (by omega) (by have : arithmetic + arithmeticBytes ≤ 2 ^ 64 := (by decide); omega)
    exact hd _ (Region.contains_self _ _) hx
  · have hd := Offset.disjoint (s.gpr .x0) (d := i) (n := 1) (e := witness) (k := len bits)
      (by simp only at h1; omega) (by omega)
      (by have : witness + 384 ≤ 2 ^ 64 := (by decide); have := hlen; omega)
    exact hd _ (Region.contains_self _ _) hx
  · exact (A.stackWs.sub_left (frame_sub s)) _ hx hc
  · exact A.wsUsed _ hc hx

theorem correct (M : Mont) (K : Kernel) {bits : Nat} (hb : Supported bits) (s : State)
    (pre : (contract bits).pre s) :
    ∃ trace t, Exec isa (code bits M.mm K.run) s trace t ∧ abiPreserved s t ∧ (contract bits).post s t := by
  have A := primeABI_of pre
  obtain ⟨trace, t, he, hpre, hpost⟩ := alloc_frame_ok (bytes := 272) (by decide) A.stackLower
    (Q := fun t => abiPreserved s t ∧ BodyPost bits s t)
    (WP.mono (body_ok M K hb A) fun t ⟨hsp, hwr, _, hp⟩ => ⟨hsp, hwr, ⟨hp.2.2.2.1, by
        change t.sp + BitVec.ofNat 64 272 = s.sp
        rw [hsp]; exact BitVec.sub_add_cancel .., hp.2.2.2.2⟩, hp⟩)
  obtain ⟨hx0, hused, hframe, _, _⟩ := hpost
  refine ⟨trace, t, he, hpre, ?_⟩
  sig_post [contract, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs]
  refine ⟨?_, keeps_of_frame hb A hframe, fun b rest h => ?_⟩
  · rw [hx0]
    have st : ∀ o : Option (Bool × Spec.RsaKeyGen.Rand),
        (BitVec.setWidth 32 (BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status o))).toNat =
          Proof.Dsa.ProbablePrime.status o := by
      intro o
      rcases o with _ | ⟨_ | _, _⟩ <;> rfl
    exact st _
  · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero]
    rw [show s.gpr .x4 + BitVec.ofNat 64 0 = s.gpr .x4 from BitVec.add_zero _, hused b rest h]

end VG.Proof.Dsa.AArch64.ProbablePrime
