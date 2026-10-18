module

public import VerifiedGarbage.Proof.Dsa.X86.PowABI
import VerifiedGarbage.Proof.Framework.Omega

/-! # Correctness and secrecy of callable IA-32 exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Pow
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Pow

theorem scratch_fits {n size : Nat} (h : contextBytes n ≤ size) :
    ∀ r ∈ scratch n, r.1 + r.2 ≤ size := by
  intro r hr
  simp only [scratch, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only [contextBytes, slot, stride] at * <;> omega

theorem correct {n e : Nat} (hn : 0 < n) (hn48 : n ≤ 48) (he : 0 < e) (hen : e ≤ 2 * n)
    (s : State) (h : (Spec.Dsa.ModPow.powContract (layout n e) abi 20).pre s) :
    ∃ tr t, Exec isa (body n e) s tr t ∧ abiPreserved s t ∧
      (Spec.Dsa.ModPow.powContract (layout n e) abi 20).post s t := by
  have A := abi_of h
  have M : wordsVal s.mem (ws s) (slot n 0) n =
      Spec.Dsa.ModPow.numAt s.mem (ws s) (slot n 0) (8 * n) := (numAt_eq8 ..).symm
  obtain ⟨tr, t, E, V, O, R, _, _⟩ := body_ok A.entry A.size hn hn48 he hen M A.gt_one A.odd
  have F : Frame [⟨ws s, bytes s⟩] s.mem t.mem := by
    intro x hx
    apply O x
    intro r hr
    have H := hx _ (List.mem_singleton_self _)
    have B := scratch_fits A.size r hr
    simp only [Region.Contains, ofs] at H ⊢
    omega
  refine ⟨tr, t, E, ⟨R, ?_⟩, ?_⟩
  · exact F.readW (by
      simpa only [BitVec.add_zero] using
        Offset.contains_base ((s.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide) (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact A.retScratch) (by decide)
  · sig_post [Spec.Dsa.ModPow.powContract, Spec.Dsa.ModPow.sig, layout, abi, argSlots, argVal, argBytes]
    refine ⟨?_, ?_⟩
    · simpa only [numAt_eq8, numAt_eq4] using V
    · intro i hi hj
      apply O _
      intro r hr
      have bound := A.bound
      rw [show ofs (ws s) (ws s + BitVec.ofNat 64 i) = i by
        simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by dsimp only [bytes] at bound; omega)]]
      exact hj r hr

theorem publicArgs {n e : Nat} {s t : State}
    (H : (Spec.Dsa.ModPow.powContract (layout n e) abi 20).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 := by
  sig_pub [Spec.Dsa.ModPow.powContract, Spec.Dsa.ModPow.sig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor <;> with_reducible assumption

theorem ABI.readArg {n e : Nat} {s : State} (A : ABI n e s) :
    readSrc s (.mem (VG.Impl.Mont.X86.at_ .esp 4)) = some (arg s 0) := by
  show s.load32 (argAddr s 0) = some (arg s 0)
  rw [State.load32, ite_eq_left_iff.mpr fun h => absurd A.entry.arg h]
  rfl

theorem constantTime (n e : Nat) (he : 0 < e) :
    ConstantTime isa (Spec.Dsa.ModPow.powContract (layout n e) abi 20).pre
      (Spec.Dsa.ModPow.powContract (layout n e) abi 20).pub (body n e) := by
  intro s t tr ur sf tf hs ht hp E F
  have A := publicArgs hp
  exact ((body_relCT n e he) s t tr ur sf tf
    ⟨A.1, A.2, (abi_of hs).readArg, (abi_of ht).readArg⟩ E F).1

end VG.Proof.Dsa.X86.Pow
