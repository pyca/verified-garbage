module

public import VerifiedGarbage.Impl.Dsa.X86.Arith
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Dsa.X86.RedTiming
import VerifiedGarbage.Proof.Dsa.X86.PowCorrect
import VerifiedGarbage.Proof.Dsa.X86.PowVerified
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
public import VerifiedGarbage.Proof.Dsa.ModPowContract
public import VerifiedGarbage.Proof.Dsa.ModArithContract

@[expose] public section
namespace VG.Proof.Dsa.X86.Red
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Arith
open VG.Proof.Dsa.X86.Pow (ws bytes numAt_eq8 scratch_fits)

theorem argAddr_off (s : State) (i : Nat) (h : (s.gpr .esp).toNat + 4 + 4 * i + 4 ≤ 2 ^ 32) :
    argAddr s i = argAddr s 0 + BitVec.ofNat 64 (4 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [argAddr, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have := (s.gpr .esp).isLt
  omega

/-- The facts of the contract's precondition. -/
theorem in_of {n : Nat} {s : State}
    (h : (Proof.Dsa.ModArith.reduceContract (reduceLayout n) abi 20).pre s) :
    BodyIn n (bytes s) s ∧ Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨ws s, bytes s⟩ ∧ 20 ≤ (s.gpr .esp).toNat := by
  sig_pre [Proof.Dsa.ModArith.reduceContract, Proof.Dsa.ModArith.reduceSig, reduceLayout, abi, argSlots, argVal,
    argBytes, stackBelow] at h
  obtain ⟨low, high, rd, wr, wsData, wsArgs, retWs, _, _, belowWs, _, _, wsFit, dataFit, size, odd, large⟩ := h
  have H : (ws s).toNat + bytes s ≤ 2 ^ 32 := by
    simpa only [ws, bytes, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans (arg s 0).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using wsFit
  have dataNat : ((arg s 2).setWidth 64).toNat = (arg s 2).toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (arg s 2).isLt (by decide))]
  have argsIn : (⟨argAddr s 0, 16⟩ : Region) ∈ s.rd ++ s.wr := by
    rw [rd]; exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have argIn (i : Nat) (hi : i < 4) : InRegions (s.rd ++ s.wr) (argAddr s i) 4 := by
    refine ⟨_, argsIn, ?_⟩
    rw [argAddr_off s i (by omega)]
    exact Offset.contains_base _ (by omega) (by omega)
  have argApart (i : Nat) (hi : i < 4) : Region.Disjoint ⟨argAddr s i, 4⟩ ⟨ws s, bytes s⟩ := by
    rw [argAddr_off s i (by omega)]
    exact (wsArgs.symm).sub_left (Offset.sub_base _ (by omega))
  refine ⟨⟨⟨⟨?_, rfl, by rw [wr]; exact List.mem_cons_self .., H, ?_⟩, argIn 2 (by decide), argIn 3 (by decide),
    argApart 2 (by decide), argApart 3 (by decide), rfl, by simp, (arg s 3).isLt, ?_⟩,
    by dsimp only [bytes]; omega, by rw [Pow.numAt_eq8] at large; exact large,
    by rw [Pow.numAt_eq8] at odd; exact odd⟩, retWs, low⟩
  · exact argIn 0 (by decide)
  · apply VG.Proof.Weierstrass.X86.stkOk_of (by decide : 20 ≤ 20) low H ?_ belowWs
    have := size
    simp only [contextBytes, slot, stride] at this
    dsimp only [bytes]; omega
  · have dataIn : (⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩ : Region) ∈ s.rd ++ s.wr := by
      rw [rd]; exact List.mem_append_left _ (List.mem_cons_self ..)
    refine ⟨by omega, fun i hi => ⟨_, dataIn, Offset.contains_base _ (by omega) (by omega)⟩, fun i hi => ?_,
      ⟨_, dataIn, by simp [Region.Contains]⟩⟩
    have outside := wsData.symm _ (Offset.contains_base ((arg s 2).setWidth 64) (d := i) (n := 1)
      (k := (arg s 3).toNat) (by omega) (by omega))
    simp only [Region.Contains] at outside
    simp only [ofs]
    have := size
    simp only [ws] at outside ⊢
    omega

/-- A run of the body from a state ready for it, its return address apart
from the working space. -/
theorem run {n size : Nat} (hn : 0 < n) (hn48 : n ≤ 48) {s : State} (B : BodyIn n size s)
    (ret : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨ws s, size⟩) :
    ∃ tr t, Exec isa (reduceBody n) s tr t ∧ abiPreserved s t ∧
      wordsVal t.mem (ws s) (slot n 6) n =
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat) %
          wordsVal s.mem (ws s) (slot n 0) n ∧
      Outs (ws s) (VG.Impl.Dsa.X86.Pow.scratch n) s.mem t.mem := by
  obtain ⟨tr, t, E, V, O, R, _, _⟩ := body_ok B.input B.size hn hn48 rfl B.large B.odd
  have F : Frame [⟨ws s, size⟩] s.mem t.mem := by
    intro x hx
    have H := hx _ (List.mem_cons_self ..)
    refine O x (fun r hr => ?_)
    have Bd := scratch_fits B.size r hr
    simp only [Region.Contains, ofs] at H ⊢
    omega
  refine ⟨tr, t, E, ⟨R, ?_⟩, V, O⟩
  exact F.readW (by
      simpa only [BitVec.add_zero] using
        Offset.contains_base ((s.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide) (by decide))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl
      exact ret) (by decide)

theorem correct {n : Nat} (hn : 0 < n) (hn48 : n ≤ 48)
    (s : State) (h : (Proof.Dsa.ModArith.reduceContract (reduceLayout n) abi 20).pre s) :
    ∃ tr t, Exec isa (reduceBody n) s tr t ∧ abiPreserved s t ∧
      (Proof.Dsa.ModArith.reduceContract (reduceLayout n) abi 20).post s t := by
  obtain ⟨B, ret, _⟩ := in_of h
  have bound := B.input.entry.nowrap
  obtain ⟨tr, t, E, A, V, O⟩ := run hn hn48 B ret
  refine ⟨tr, t, E, A, ?_⟩
  sig_post [Proof.Dsa.ModArith.reduceContract, Proof.Dsa.ModArith.reduceSig, reduceLayout, abi, argSlots, argVal,
    argBytes]
  refine ⟨?_, ?_⟩
  · simpa only [numAt_eq8] using V
  · intro i hi hj
    have e : ofs (ws s) (ws s + BitVec.ofNat 64 i) = i := by
      simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by dsimp only [bytes] at bound; omega)]
    exact O _ (fun r hr => by rw [e]; exact hj r hr)

theorem publicArgs {n : Nat} {s t : State}
    (H : (Proof.Dsa.ModArith.reduceContract (reduceLayout n) abi 20).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 4, arg s i = arg t i := by
  sig_pub [Proof.Dsa.ModArith.reduceContract, Proof.Dsa.ModArith.reduceSig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  refine ⟨by with_reducible assumption, fun i hi => ?_⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
    with_reducible assumption

theorem readArg {n size : Nat} {s : State} (B : BodyIn n size s) :
    readSrc s (.mem (VG.Impl.Mont.X86.at_ .esp 4)) = some (arg s 0) := by
  show s.load32 (argAddr s 0) = some (arg s 0)
  rw [State.load32, ite_eq_left_iff.mpr fun h => absurd B.input.entry.arg h]
  rfl

theorem constantTime {n : Nat} (hn : 0 < n) :
    ConstantTime isa (Proof.Dsa.ModArith.reduceContract (reduceLayout n) abi 20).pre
      (Proof.Dsa.ModArith.reduceContract (reduceLayout n) abi 20).pub (reduceBody n) := by
  intro s t tr ur sf tf hs ht hp E F
  have A := publicArgs hp
  have B₁ := (in_of hs).1
  have B₂ := (in_of ht).1
  have e : bytes t = bytes s := by simp only [bytes, A.2 1 (by decide)]
  rw [e] at B₂
  exact ((body_relCT n (bytes s) hn) s t tr ur sf tf ⟨A.1, A.2, readArg B₁, readArg B₂, B₁, B₂⟩ E F).1

/-- Ones below `2³¹`, where the working space is, and the arguments at
`esp + 4`: the working space at `0x1000`, of `0x1000` words, and no bytes
at `0x100000`. -/
def satMem (a : Addr) : BitVec 8 :=
  if a.toNat < 0x80000000 then 1
  else if a = 0xf0000005 ∨ a = 0xf0000009 ∨ a = 0xf000000e then 0x10 else 0

def satState : State where
  gpr r := if r = .esp then 0xf0000000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x100000, 0⟩, ⟨0xf0000004, 16⟩]
  wr := [⟨0x1000, 0x8000⟩]

theorem satMem_read {n : Nat} (hn48 : n ≤ 48) :
    Mem.read satMem (BitVec.setWidth 64 (4096 : BitVec 32) + BitVec.ofNat 64 (slot n 0)) (8 * n) =
      Mem.read (fun _ => 1) (BitVec.setWidth 64 (4096 : BitVec 32) + BitVec.ofNat 64 (slot n 0)) (8 * n) := by
  refine Mem.read_congr fun i hi => ?_
  have h0 : slot n 0 = 64 := by simp only [slot]; omega
  unfold satMem
  split
  · rfl
  · rename_i h
    exfalso
    apply h
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h0]
    simp only [show (4096 : BitVec 32).toNat = 4096 from rfl]
    omega

theorem satisfiable {n : Nat} (hn : 0 < n) (hn48 : n ≤ 48) :
    ∃ s, (Proof.Dsa.ModArith.reduceContract (reduceLayout n) abi 20).pre s := by
  refine ⟨satState, ?_⟩
  have a0 : arg satState 0 = 0x1000 := by decide
  have a1 : arg satState 1 = 0x1000 := by decide
  have a2 : arg satState 2 = 0x100000 := by decide
  have a3 : arg satState 3 = 0 := by decide
  sig_pre [Proof.Dsa.ModArith.reduceContract, Proof.Dsa.ModArith.reduceSig, reduceLayout, abi, argSlots, argVal,
    argBytes, stackBelow]
  simp only [a0, a1, a2, a3]
  sig_and_intros
  all_goals try decide
  all_goals try exact Region.disjoint_of_sep (by decide)
  · rw [show BitVec.toNat (4096 : BitVec 32) = 4096 from rfl]
    simp only [contextBytes, slot, stride]; omega
  all_goals
    unfold Proof.Dsa.ModPow.numAt
    rw [satMem_read hn48]
    obtain ⟨k, hk⟩ : ∃ k, 8 * n = k + 2 := ⟨8 * n - 2, by omega⟩
    rw [hk]
  · exact (Pow.read_ones _ k).1
  · exact (Pow.read_ones _ k).2

theorem verified (n : Nat) (hn : 0 < n := by decide) (hn48 : n ≤ 48 := by decide) :
    Verified target (reduceBody n) (Proof.Dsa.ModArith.reduceContract (reduceLayout n) abi 20) :=
  ⟨correct hn hn48, constantTime hn, satisfiable hn hn48⟩

end VG.Proof.Dsa.X86.Red
