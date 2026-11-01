module

public import VerifiedGarbage.Proof.Dsa.X86.PowABI
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Dsa.X86.PowTiming
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Dsa.X86.PowBody
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.ModPowContract

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

theorem correct {n e : Nat} (hn : 2 ≤ n) (hn48 : n ≤ 48) (he : 1 < e) (hen : e ≤ 2 * n)
    (s : State) (h : (Proof.Dsa.ModPow.powContract (layout n e) abi 96).pre s) :
    ∃ tr t, Exec isa (body n e) s tr t ∧ abiPreserved s t ∧
      (Proof.Dsa.ModPow.powContract (layout n e) abi 96).post s t := by
  have A := abi_of h
  have M : wordsVal s.mem (ws s) (slot n 0) n =
      Proof.Dsa.ModPow.numAt s.mem (ws s) (slot n 0) (8 * n) := (numAt_eq8 ..).symm
  have Rm := A.room
  obtain ⟨tr, t, E, V, O, R, _, _⟩ := body_ok (A.entry (by decide)) Rm A.size hn hn48 he hen M A.gt_one A.odd
  have F : Frame [⟨ws s, bytes s⟩, below (s.gpr .esp) 96] s.mem t.mem := by
    intro x hx
    have H := hx _ (List.mem_cons_self ..)
    refine O x (fun r hr => ?_) (hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    have B := scratch_fits A.size r hr
    simp only [Region.Contains, ofs] at H ⊢
    omega
  refine ⟨tr, t, E, ⟨R, ?_⟩, ?_⟩
  · exact F.readW (by
      simpa only [BitVec.add_zero] using
        Offset.contains_base ((s.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide) (by decide))
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact A.retScratch
        · simp only [below]
          rw [VG.X86.Taint.sub_setWidth A.stackLow]
          exact Offset.base_disjoint_below _ (by decide)) (by decide)
  · sig_post [Proof.Dsa.ModPow.powContract, Proof.Dsa.ModPow.sig, layout, abi, argSlots, argVal, argBytes]
    refine ⟨?_, ?_⟩
    · simpa only [numAt_eq8, numAt_eq4] using V
    · intro i hi hj
      have bound := A.bound
      have e : ofs (ws s) (ws s + BitVec.ofNat 64 i) = i := by
        simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by dsimp only [bytes] at bound; omega)]
      refine O _ (fun r hr => by rw [e]; exact hj r hr) fun hz => ?_
      have := OutsS.zone_ofs Rm hz
      rw [e] at this
      dsimp only [bytes] at this
      omega

theorem publicArgs {n e : Nat} {s t : State}
    (H : (Proof.Dsa.ModPow.powContract (layout n e) abi 96).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 := by
  sig_pub [Proof.Dsa.ModPow.powContract, Proof.Dsa.ModPow.sig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor <;> with_reducible assumption

theorem ABI.readArg {n e k : Nat} {s : State} (A : ABI n e s k) (hk : 20 ≤ k := by decide) :
    readSrc s (.mem (VG.Impl.Mont.X86.at_ .esp 4)) = some (arg s 0) := by
  show s.load32 (argAddr s 0) = some (arg s 0)
  rw [State.load32, ite_eq_left_iff.mpr fun h => absurd (A.entry hk).arg h]
  rfl

theorem ABI.bodyIn {n e : Nat} {s : State} (A : ABI n e s 96) : BodyIn n s := by
  have M : wordsVal s.mem (ws s) (slot n 0) n = Proof.Dsa.ModPow.numAt s.mem (ws s) (slot n 0) (8 * n) :=
    (numAt_eq8 ..).symm
  exact ⟨bytes s, (A.entry (by decide)), A.room, A.size, M ▸ A.gt_one, M ▸ A.odd⟩

theorem constantTime {n e : Nat} (hn : 2 ≤ n) (hn48 : n ≤ 48) (he : 1 < e) (hen : e ≤ 2 * n) :
    ConstantTime isa (Proof.Dsa.ModPow.powContract (layout n e) abi 96).pre
      (Proof.Dsa.ModPow.powContract (layout n e) abi 96).pub (body n e) := by
  intro s t tr ur sf tf hs ht hp E F
  have A := publicArgs hp
  exact ((body_relCT n e hn hn48 he hen) s t tr ur sf tf
    ⟨A.1, A.2, (abi_of hs).readArg, (abi_of ht).readArg, (abi_of hs).bodyIn, (abi_of ht).bodyIn⟩ E F).1

end VG.Proof.Dsa.X86.Pow
