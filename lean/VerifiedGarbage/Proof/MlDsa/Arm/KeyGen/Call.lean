module

public import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Site
public import VerifiedGarbage.Proof.MlDsa.Contract
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.MlKem.Arm.Prf
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlKem.Arm.Loops
public import VerifiedGarbage.Proof.MlKem.Arm.NttInv
public import VerifiedGarbage.Proof.MlKem.Arm.RowSum
public import VerifiedGarbage.Proof.MlKem.Arm.SampleCT
public import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Proof.Sha3.Arith
public import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb
public import VerifiedGarbage.Proof.Sha3.Arm.Stream.Pad
public import VerifiedGarbage.Spec.MlDsa.Contract
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.MlKem.Arm.Keccak
import VerifiedGarbage.Proof.MlKem.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-! ### `MlDsa.Arm.KeyGen.Contracts`, which this module and modules that import it used -/

section

/-!
# ML-DSA on 32-bit ARM: the contracts of the primitives, evaluated

For each primitive the top-level functions call, its contract's precondition
(`ntt_pre`, …), from plain facts about the state `x` the callee starts from:
the arguments in their registers (and the fifth in the stack slot, `stackArg x
0`), the regions it is given, their disjointness and the stack below `x.sp`;
what its postcondition says (`…_post`); and its public data, from the
equalities of two such states (`…_pub`). Each is proven once, by evaluating
the contract (`sig_pre`, `sig_post`, `sig_pub`) on a state that is a variable.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `vg_mldsa_ntt`, `vg_mldsa_inv_ntt` -/

section
variable {stk : Nat} {x y : State}

theorem ip_pre {t : Poly → Poly} {f w : BitVec 32} (g0 : x.gpr .r0 = f) (g1 : x.gpr .r1 = w)
    (hrd : x.rd = []) (hwr : x.wr = [regA f 1024, regA w 1024]) (hsp : stk ≤ x.sp.toNat)
    (hd : (regA f 1024).Disjoint (regA w 1024)) (kf : (below x stk).Disjoint (regA f 1024))
    (kw : (below x stk).Disjoint (regA w 1024)) (ff : f.toNat + 1024 ≤ 2 ^ 32) (fw : w.toNat + 1024 ≤ 2 ^ 32)
    (hr : Reduced x.mem (State.addr f)) : (inPlaceContract Arm.abi t stk).pre x := by
  sig_pre [inPlaceContract, inPlaceSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1]
  try simp only [State.addr] at *
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | (have := State.sp _ |>.isLt; omega_arith) | omega_arith | skip)
    | (have := State.sp _ |>.isLt; omega_arith)
    | omega_arith
    | skip
  all_goals assumption

theorem ip_post {t : Poly → Poly} (h : (inPlaceContract Arm.abi t stk).post x y) :
    PolyIs y.mem (State.addr (x.gpr .r0)) (t (polyAt x.mem (State.addr (x.gpr .r0)))) := by
  sig_post [inPlaceContract, inPlaceSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  exact h

theorem ip_pub {t : Poly → Poly} (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1) :
    (inPlaceContract Arm.abi t stk).pub x y := by
  sig_pub [inPlaceContract, inPlaceSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1⟩

end

/-! ## `vg_mldsa_multiply_ntt`, `vg_mldsa_multiply_add_ntt` -/

section
variable {stk : Nat} {x y : State} {h f g : BitVec 32}

theorem mul_pre (g0 : x.gpr .r0 = h) (g1 : x.gpr .r1 = f) (g2 : x.gpr .r2 = g)
    (hrd : x.rd = [regA f 1024, regA g 1024]) (hwr : x.wr = [regA h 1024]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (regA h 1024).Disjoint (regA f 1024)) (d2 : (regA h 1024).Disjoint (regA g 1024))
    (kh : (below x stk).Disjoint (regA h 1024)) (kf : (below x stk).Disjoint (regA f 1024))
    (kg : (below x stk).Disjoint (regA g 1024)) (fh : h.toNat + 1024 ≤ 2 ^ 32) (ff : f.toNat + 1024 ≤ 2 ^ 32)
    (fg : g.toNat + 1024 ≤ 2 ^ 32) (rf : Reduced x.mem (State.addr f)) (rg : Reduced x.mem (State.addr g)) :
    (mulContract Arm.abi stk).pre x := by
  sig_pre [mulContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2]
  try simp only [State.addr] at *
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | (have := State.sp _ |>.isLt; omega_arith) | omega_arith | skip)
    | (have := State.sp _ |>.isLt; omega_arith)
    | omega_arith
    | skip
  all_goals assumption

theorem mul_post (hp : (mulContract Arm.abi stk).post x y) :
    PolyIs y.mem (State.addr (x.gpr .r0))
      (multiplyNTT (polyAt x.mem (State.addr (x.gpr .r1))) (polyAt x.mem (State.addr (x.gpr .r2)))) := by
  sig_post [mulContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem mulAdd_pre (g0 : x.gpr .r0 = h) (g1 : x.gpr .r1 = f) (g2 : x.gpr .r2 = g)
    (hrd : x.rd = [regA f 1024, regA g 1024]) (hwr : x.wr = [regA h 1024]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (regA h 1024).Disjoint (regA f 1024)) (d2 : (regA h 1024).Disjoint (regA g 1024))
    (kh : (below x stk).Disjoint (regA h 1024)) (kf : (below x stk).Disjoint (regA f 1024))
    (kg : (below x stk).Disjoint (regA g 1024)) (fh : h.toNat + 1024 ≤ 2 ^ 32) (ff : f.toNat + 1024 ≤ 2 ^ 32)
    (fg : g.toNat + 1024 ≤ 2 ^ 32) (rh : Reduced x.mem (State.addr h)) (rf : Reduced x.mem (State.addr f))
    (rg : Reduced x.mem (State.addr g)) : (mulAddContract Arm.abi stk).pre x := by
  sig_pre [mulAddContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2]
  try simp only [State.addr] at *
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | (have := State.sp _ |>.isLt; omega_arith) | omega_arith | skip)
    | (have := State.sp _ |>.isLt; omega_arith)
    | omega_arith
    | skip
  all_goals assumption

theorem mulAdd_post (hp : (mulAddContract Arm.abi stk).post x y) :
    PolyIs y.mem (State.addr (x.gpr .r0)) (add (polyAt x.mem (State.addr (x.gpr .r0)))
      (multiplyNTT (polyAt x.mem (State.addr (x.gpr .r1))) (polyAt x.mem (State.addr (x.gpr .r2))))) := by
  sig_post [mulAddContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem mul_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) : (mulContract Arm.abi stk).pub x y := by
  sig_pub [mulContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1, h2⟩

theorem mulAdd_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) : (mulAddContract Arm.abi stk).pub x y := by
  sig_pub [mulAddContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1, h2⟩

end

/-! ## `vg_mldsa_add`, `vg_mldsa_sub` -/

section
variable {stk : Nat} {x y : State} {f g : BitVec 32}

theorem add_pre (g0 : x.gpr .r0 = f) (g1 : x.gpr .r1 = g) (hrd : x.rd = [regA g 1024])
    (hwr : x.wr = [regA f 1024]) (hsp : stk ≤ x.sp.toNat) (d1 : (regA f 1024).Disjoint (regA g 1024))
    (kf : (below x stk).Disjoint (regA f 1024)) (kg : (below x stk).Disjoint (regA g 1024))
    (ff : f.toNat + 1024 ≤ 2 ^ 32) (fg : g.toNat + 1024 ≤ 2 ^ 32) (rf : Reduced x.mem (State.addr f))
    (rg : Reduced x.mem (State.addr g)) : (addContract Arm.abi stk).pre x := by
  sig_pre [addContract, accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1]
  try simp only [State.addr] at *
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | (have := State.sp _ |>.isLt; omega_arith) | omega_arith | skip)
    | (have := State.sp _ |>.isLt; omega_arith)
    | omega_arith
    | skip
  all_goals assumption

theorem add_post (hp : (addContract Arm.abi stk).post x y) :
    PolyIs y.mem (State.addr (x.gpr .r0))
      (add (polyAt x.mem (State.addr (x.gpr .r0))) (polyAt x.mem (State.addr (x.gpr .r1)))) := by
  sig_post [addContract, accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem add_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1) :
    (addContract Arm.abi stk).pub x y := by
  sig_pub [addContract, accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1⟩

theorem sub_pre (g0 : x.gpr .r0 = f) (g1 : x.gpr .r1 = g) (hrd : x.rd = [regA g 1024])
    (hwr : x.wr = [regA f 1024]) (hsp : stk ≤ x.sp.toNat) (d1 : (regA f 1024).Disjoint (regA g 1024))
    (kf : (below x stk).Disjoint (regA f 1024)) (kg : (below x stk).Disjoint (regA g 1024))
    (ff : f.toNat + 1024 ≤ 2 ^ 32) (fg : g.toNat + 1024 ≤ 2 ^ 32) (rf : Reduced x.mem (State.addr f))
    (rg : Reduced x.mem (State.addr g)) : (subContract Arm.abi stk).pre x := by
  sig_pre [subContract, accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1]
  try simp only [State.addr] at *
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | (have := State.sp _ |>.isLt; omega_arith) | omega_arith | skip)
    | (have := State.sp _ |>.isLt; omega_arith)
    | omega_arith
    | skip
  all_goals assumption

theorem sub_post (hp : (subContract Arm.abi stk).post x y) :
    PolyIs y.mem (State.addr (x.gpr .r0))
      (sub (polyAt x.mem (State.addr (x.gpr .r0))) (polyAt x.mem (State.addr (x.gpr .r1)))) := by
  sig_post [subContract, accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem sub_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1) :
    (subContract Arm.abi stk).pub x y := by
  sig_pub [subContract, accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1⟩

end

/-! ## `vg_mldsa_rej_ntt_poly`, `vg_mldsa_rej_bounded_poly` -/

section
variable {stk : Nat} {x y : State} {sd a w e : BitVec 32}

theorem rejNtt_pre (g0 : x.gpr .r0 = sd) (g1 : x.gpr .r1 = a) (g2 : x.gpr .r2 = w)
    (hrd : x.rd = [regA sd 34]) (hwr : x.wr = [regA a 1024, regA w 2048]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (regA sd 34).Disjoint (regA a 1024)) (d2 : (regA sd 34).Disjoint (regA w 2048))
    (d3 : (regA a 1024).Disjoint (regA w 2048))
    (k1 : (below x stk).Disjoint (regA sd 34)) (k2 : (below x stk).Disjoint (regA a 1024))
    (k3 : (below x stk).Disjoint (regA w 2048)) (f1 : sd.toNat + 34 ≤ 2 ^ 32) (f2 : a.toNat + 1024 ≤ 2 ^ 32)
    (f3 : w.toNat + 2048 ≤ 2 ^ 32) : (rejNTTContract Arm.abi stk).pre x := by
  sig_pre [rejNTTContract, rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2]
  try simp only [State.addr] at *
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | (have := State.sp _ |>.isLt; omega_arith) | omega_arith | skip)
    | (have := State.sp _ |>.isLt; omega_arith)
    | omega_arith
    | skip
  all_goals assumption

theorem rejNtt_post (hp : (rejNTTContract Arm.abi stk).post x y) :
    ((y.gpr .r0 = 1 → Reduced y.mem (State.addr (x.gpr .r1))) ∧
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt x.mem (State.addr (x.gpr .r0)) 34)) (y.gpr .r0)
        (polyAt y.mem (State.addr (x.gpr .r1)))) := by
  sig_post [rejNTTContract, rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  rwa [setWidth_append32] at hp

theorem rejNtt_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2)
    (hl : bytesAt x.mem (State.addr (x.gpr .r0)) 34 = bytesAt y.mem (State.addr (y.gpr .r0)) 34) :
    (rejNTTContract Arm.abi stk).pub x y := by
  sig_pub [rejNTTContract, rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, congrArg leakBytes hl, h0, h1, h2⟩

theorem rejBounded_pre (g0 : x.gpr .r0 = sd) (g1 : x.gpr .r1 = e) (g2 : x.gpr .r2 = a) (g3 : x.gpr .r3 = w)
    (hrd : x.rd = [regA sd 66]) (hwr : x.wr = [regA a 1024, regA w 2048]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (regA sd 66).Disjoint (regA a 1024)) (d2 : (regA sd 66).Disjoint (regA w 2048))
    (d3 : (regA a 1024).Disjoint (regA w 2048))
    (k1 : (below x stk).Disjoint (regA sd 66)) (k2 : (below x stk).Disjoint (regA a 1024))
    (k3 : (below x stk).Disjoint (regA w 2048)) (f1 : sd.toNat + 66 ≤ 2 ^ 32) (f2 : a.toNat + 1024 ≤ 2 ^ 32)
    (f3 : w.toNat + 2048 ≤ 2 ^ 32) (he : e.toNat = 2 ∨ e.toNat = 4) : (rejBoundedContract Arm.abi stk).pre x := by
  sig_pre [rejBoundedContract, rejBoundedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, g3]
  try simp only [State.addr] at *
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | (have := State.sp _ |>.isLt; omega_arith) | omega_arith | skip)
    | (have := State.sp _ |>.isLt; omega_arith)
    | omega_arith
    | skip
  all_goals assumption

theorem rejBounded_post (hp : (rejBoundedContract Arm.abi stk).post x y) :
    ((y.gpr .r0 = 1 → Reduced y.mem (State.addr (x.gpr .r2))) ∧
      Outcome (fun b => (rejBoundedPoly (x.gpr .r1).toNat b.rejBounded (bytesAt x.mem (State.addr (x.gpr .r0)) 66)).map
        toRq) (y.gpr .r0) (polyAt y.mem (State.addr (x.gpr .r2)))) := by
  sig_post [rejBoundedContract, rejBoundedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  rwa [setWidth_append32] at hp

theorem rejBounded_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) (h3 : x.gpr .r3 = y.gpr .r3)
    (hl : rejBoundedLeak (x.gpr .r1).toNat (bytesAt x.mem (State.addr (x.gpr .r0)) 66) =
      rejBoundedLeak (y.gpr .r1).toNat (bytesAt y.mem (State.addr (y.gpr .r0)) 66)) :
    (rejBoundedContract Arm.abi stk).pub x y := by
  sig_pub [rejBoundedContract, rejBoundedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, hl, h0, h1, h2, h3⟩

end

/-! ## `vg_mldsa_power2round` -/

section
variable {stk : Nat} {x y : State} {t t1 t0 : BitVec 32}

theorem p2r_pre (g0 : x.gpr .r0 = t) (g1 : x.gpr .r1 = t1) (g2 : x.gpr .r2 = t0)
    (hrd : x.rd = [regA t 1024]) (hwr : x.wr = [regA t1 1024, regA t0 1024]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (regA t 1024).Disjoint (regA t1 1024)) (d2 : (regA t 1024).Disjoint (regA t0 1024))
    (d3 : (regA t1 1024).Disjoint (regA t0 1024))
    (k1 : (below x stk).Disjoint (regA t 1024)) (k2 : (below x stk).Disjoint (regA t1 1024))
    (k3 : (below x stk).Disjoint (regA t0 1024)) (f1 : t.toNat + 1024 ≤ 2 ^ 32) (f2 : t1.toNat + 1024 ≤ 2 ^ 32)
    (f3 : t0.toNat + 1024 ≤ 2 ^ 32) (hr : Reduced x.mem (State.addr t)) : (power2RoundContract Arm.abi stk).pre x := by
  sig_pre [power2RoundContract, power2RoundSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2]
  try simp only [State.addr] at *
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | (have := State.sp _ |>.isLt; omega_arith) | omega_arith | skip)
    | (have := State.sp _ |>.isLt; omega_arith)
    | omega_arith
    | skip
  all_goals assumption

theorem p2r_post (hp : (power2RoundContract Arm.abi stk).post x y) :
    NatPolyIs y.mem (State.addr (x.gpr .r1))
        ((polyAt x.mem (State.addr (x.gpr .r0))).map fun c => (power2Round c).1.toNat) ∧
      PolyIs y.mem (State.addr (x.gpr .r2)) ((polyAt x.mem (State.addr (x.gpr .r0))).map fun c => ofInt (power2Round c).2) := by
  sig_post [power2RoundContract, power2RoundSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem p2r_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) : (power2RoundContract Arm.abi stk).pub x y := by
  sig_pub [power2RoundContract, power2RoundSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1, h2⟩

end

/-! ## `vg_mldsa_simple_bit_pack`, `vg_mldsa_bit_pack` -/

section
variable {stk : Nat} {x y : State} {f a b o l : BitVec 32}

theorem sbp_pre (g0 : x.gpr .r0 = f) (g1 : x.gpr .r1 = b) (g2 : x.gpr .r2 = o) (g3 : x.gpr .r3 = l)
    (hrd : x.rd = [regA f 1024]) (hwr : x.wr = [regA o l.toNat]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (regA f 1024).Disjoint (regA o l.toNat))
    (k1 : (below x stk).Disjoint (regA f 1024)) (k2 : (below x stk).Disjoint (regA o l.toNat))
    (f1 : f.toNat + 1024 ≤ 2 ^ 32) (f2 : o.toNat + l.toNat ≤ 2 ^ 32) (hb : b.toNat ∈ simpleBitPackBounds)
    (hl : l.toNat = 32 * bitlen b.toNat) (hc : ∀ i < n, (coeffAt x.mem (State.addr f) i).toNat ≤ b.toNat) :
    (simpleBitPackContract Arm.abi stk).pre x := by
  sig_pre [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, g3]
  try simp only [State.addr] at *
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | (have := State.sp _ |>.isLt; omega_arith) | omega_arith | skip)
    | (have := State.sp _ |>.isLt; omega_arith)
    | omega_arith
    | skip
  all_goals assumption

theorem sbp_post (hp : (simpleBitPackContract Arm.abi stk).post x y) :
    bytesAt y.mem (State.addr (x.gpr .r2)) (x.gpr .r3).toNat =
      simpleBitPack (natPolyAt x.mem (State.addr (x.gpr .r0))) (x.gpr .r1).toNat := by
  sig_post [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem sbp_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) (h3 : x.gpr .r3 = y.gpr .r3) : (simpleBitPackContract Arm.abi stk).pub x y := by
  sig_pub [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1, h2, h3⟩

theorem bp_pre (g0 : x.gpr .r0 = f) (g1 : x.gpr .r1 = a) (g2 : x.gpr .r2 = b) (g3 : x.gpr .r3 = o)
    (ga : stackArg x 0 = l)
    (hrd : x.rd = [regA f 1024, ⟨stackArgAddr x 0, 4⟩]) (hwr : x.wr = [regA o l.toNat]) (hsp : stk ≤ x.sp.toNat)
    (hs4 : x.sp.toNat + 4 ≤ 2 ^ 32)
    (d1 : (regA f 1024).Disjoint (regA o l.toNat)) (d2 : (regA o l.toNat).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (k1 : (below x stk).Disjoint (regA f 1024)) (k2 : (below x stk).Disjoint (regA o l.toNat))
    (k3 : (below x stk).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (f1 : f.toNat + 1024 ≤ 2 ^ 32) (f2 : o.toNat + l.toNat ≤ 2 ^ 32) (hab : (a.toNat, b.toNat) ∈ bitPackParams)
    (hl : l.toNat = 32 * bitlen (a.toNat + b.toNat)) (hr : Reduced x.mem (State.addr f))
    (hc : ∀ i < n, -(a.toNat : Int) ≤ modPm (coeffAt x.mem (State.addr f) i).toNat q ∧
      modPm (coeffAt x.mem (State.addr f) i).toNat q ≤ b.toNat) :
    (bitPackContract Arm.abi stk).pre x := by
  sig_pre [bitPackContract, bitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, g3, ga]
  try simp only [State.addr] at *
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | (have := State.sp _ |>.isLt; omega_arith) | omega_arith | skip)
    | (have := State.sp _ |>.isLt; omega_arith)
    | omega_arith
    | skip
  all_goals assumption

theorem bp_post (hp : (bitPackContract Arm.abi stk).post x y) :
    bytesAt y.mem (State.addr (x.gpr .r3)) (stackArg x 0).toNat =
      bitPack ((polyAt x.mem (State.addr (x.gpr .r0))).map fun c => modPm c.val q) (x.gpr .r1).toNat
        (x.gpr .r2).toNat := by
  sig_post [bitPackContract, bitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem bp_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) (h3 : x.gpr .r3 = y.gpr .r3) (ha : stackArg x 0 = stackArg y 0) :
    (bitPackContract Arm.abi stk).pub x y := by
  sig_pub [bitPackContract, bitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1, h2, h3, ha⟩

end

/-! ## `vg_mldsa_sample_in_ball` -/

section
variable {stk : Nat} {x y : State} {ct len tau c w : BitVec 32}

theorem ball_pre (g0 : x.gpr .r0 = ct) (g1 : x.gpr .r1 = len) (g2 : x.gpr .r2 = tau) (g3 : x.gpr .r3 = c)
    (ga : stackArg x 0 = w)
    (hrd : x.rd = [regA ct len.toNat, ⟨stackArgAddr x 0, 4⟩]) (hwr : x.wr = [regA c 1024, regA w 2048])
    (hsp : stk ≤ x.sp.toNat) (hs4 : x.sp.toNat + 4 ≤ 2 ^ 32)
    (d1 : (regA ct len.toNat).Disjoint (regA c 1024)) (d2 : (regA ct len.toNat).Disjoint (regA w 2048))
    (d3 : (regA c 1024).Disjoint (regA w 2048)) (d4 : (regA c 1024).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (d5 : (regA w 2048).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (k1 : (below x stk).Disjoint (regA ct len.toNat)) (k2 : (below x stk).Disjoint (regA c 1024))
    (k3 : (below x stk).Disjoint (regA w 2048)) (k4 : (below x stk).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (f1 : ct.toNat + len.toNat ≤ 2 ^ 32) (f2 : c.toNat + 1024 ≤ 2 ^ 32) (f3 : w.toNat + 2048 ≤ 2 ^ 32)
    (hp : (len.toNat, tau.toNat) ∈ ballParams) : (sampleInBallContract Arm.abi stk).pre x := by
  sig_pre [sampleInBallContract, sampleInBallSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, g3, ga]
  try simp only [State.addr] at *
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | (have := State.sp _ |>.isLt; omega_arith) | omega_arith | skip)
    | (have := State.sp _ |>.isLt; omega_arith)
    | omega_arith
    | skip
  all_goals assumption

theorem ball_post (hp : (sampleInBallContract Arm.abi stk).post x y) :
    ((y.gpr .r0 = 1 → Reduced y.mem (State.addr (x.gpr .r3))) ∧
      Outcome (fun b => (sampleInBall (x.gpr .r2).toNat b.ball
        (bytesAt x.mem (State.addr (x.gpr .r0)) (x.gpr .r1).toNat)).map toRq) (y.gpr .r0)
        (polyAt y.mem (State.addr (x.gpr .r3)))) := by
  sig_post [sampleInBallContract, sampleInBallSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  rwa [setWidth_append32] at hp

theorem ball_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) (h3 : x.gpr .r3 = y.gpr .r3) (ha : stackArg x 0 = stackArg y 0)
    (hl : bytesAt x.mem (State.addr (x.gpr .r0)) (x.gpr .r1).toNat =
      bytesAt y.mem (State.addr (y.gpr .r0)) (y.gpr .r1).toNat) :
    (sampleInBallContract Arm.abi stk).pub x y := by
  sig_pub [sampleInBallContract, sampleInBallSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, congrArg leakBytes hl, h0, h1, h2, h3, ha⟩

end

/-! ## `vg_mldsa_use_hint` -/

section
variable {stk : Nat} {x y : State} {h r g2 o : BitVec 32}

theorem useHint_pre (g0 : x.gpr .r0 = h) (g1 : x.gpr .r1 = r) (gg : x.gpr .r2 = g2) (g3 : x.gpr .r3 = o)
    (hrd : x.rd = [regA h 1024, regA r 1024]) (hwr : x.wr = [regA o 1024]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (regA h 1024).Disjoint (regA o 1024)) (d2 : (regA r 1024).Disjoint (regA o 1024))
    (k1 : (below x stk).Disjoint (regA h 1024)) (k2 : (below x stk).Disjoint (regA r 1024))
    (k3 : (below x stk).Disjoint (regA o 1024)) (f1 : h.toNat + 1024 ≤ 2 ^ 32) (f2 : r.toNat + 1024 ≤ 2 ^ 32)
    (f3 : o.toNat + 1024 ≤ 2 ^ 32) (hg : g2.toNat ∈ gamma2s) (hr : Reduced x.mem (State.addr r)) :
    (useHintContract Arm.abi stk).pre x := by
  sig_pre [useHintContract, useHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, gg, g3]
  try simp only [State.addr] at *
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | (have := State.sp _ |>.isLt; omega_arith) | omega_arith | skip)
    | (have := State.sp _ |>.isLt; omega_arith)
    | omega_arith
    | skip
  all_goals assumption

theorem useHint_post (hp : (useHintContract Arm.abi stk).post x y) :
    NatPolyIs y.mem (State.addr (x.gpr .r3)) (Vector.zipWith (fun hj rj => (useHint (x.gpr .r2).toNat hj rj).toNat)
      ((hintAt x.mem (State.addr (x.gpr .r0)) 1).headD (Vector.replicate n false))
      (polyAt x.mem (State.addr (x.gpr .r1)))) := by
  sig_post [useHintContract, useHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem useHint_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) (h3 : x.gpr .r3 = y.gpr .r3) : (useHintContract Arm.abi stk).pub x y := by
  sig_pub [useHintContract, useHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1, h2, h3⟩

end

/-! ## `vg_mldsa_bit_unpack`, `vg_mldsa_unpack_t1` -/

section
variable {stk : Nat} {x y : State} {v len a b f : BitVec 32}

theorem bu_pre (g0 : x.gpr .r0 = v) (g1 : x.gpr .r1 = len) (g2 : x.gpr .r2 = a) (g3 : x.gpr .r3 = b)
    (ga : stackArg x 0 = f)
    (hrd : x.rd = [regA v len.toNat, ⟨stackArgAddr x 0, 4⟩]) (hwr : x.wr = [regA f 1024])
    (hsp : stk ≤ x.sp.toNat) (hs4 : x.sp.toNat + 4 ≤ 2 ^ 32)
    (d1 : (regA v len.toNat).Disjoint (regA f 1024)) (d2 : (regA f 1024).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (k1 : (below x stk).Disjoint (regA v len.toNat)) (k2 : (below x stk).Disjoint (regA f 1024))
    (k3 : (below x stk).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (f1 : v.toNat + len.toNat ≤ 2 ^ 32) (f2 : f.toNat + 1024 ≤ 2 ^ 32)
    (hab : (a.toNat, b.toNat) ∈ bitPackParams) (hl : len.toNat = 32 * bitlen (a.toNat + b.toNat)) :
    (bitUnpackContract Arm.abi stk).pre x := by
  sig_pre [bitUnpackContract, bitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, g3, ga]
  try simp only [State.addr] at *
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | (have := State.sp _ |>.isLt; omega_arith) | omega_arith | skip)
    | (have := State.sp _ |>.isLt; omega_arith)
    | omega_arith
    | skip
  all_goals assumption

theorem bu_post (hp : (bitUnpackContract Arm.abi stk).post x y) :
    PolyIs y.mem (State.addr (stackArg x 0))
      (toRq (bitUnpack (bytesAt x.mem (State.addr (x.gpr .r0)) (x.gpr .r1).toNat) (x.gpr .r2).toNat
        (x.gpr .r3).toNat)) := by
  sig_post [bitUnpackContract, bitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem bu_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) (h3 : x.gpr .r3 = y.gpr .r3) (ha : stackArg x 0 = stackArg y 0) :
    (bitUnpackContract Arm.abi stk).pub x y := by
  sig_pub [bitUnpackContract, bitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1, h2, h3, ha⟩

theorem t1_pre (g0 : x.gpr .r0 = v) (g1 : x.gpr .r1 = f)
    (hrd : x.rd = [regA v 320]) (hwr : x.wr = [regA f 1024]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (regA v 320).Disjoint (regA f 1024))
    (k1 : (below x stk).Disjoint (regA v 320)) (k2 : (below x stk).Disjoint (regA f 1024))
    (f1 : v.toNat + 320 ≤ 2 ^ 32) (f2 : f.toNat + 1024 ≤ 2 ^ 32) :
    (unpackT1Contract Arm.abi stk).pre x := by
  sig_pre [unpackT1Contract, unpackT1Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1]
  try simp only [State.addr] at *
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | (have := State.sp _ |>.isLt; omega_arith) | omega_arith | skip)
    | (have := State.sp _ |>.isLt; omega_arith)
    | omega_arith
    | skip
  all_goals assumption

theorem t1_post (hp : (unpackT1Contract Arm.abi stk).post x y) :
    PolyIs y.mem (State.addr (x.gpr .r1))
      ((simpleBitUnpack (bytesAt x.mem (State.addr (x.gpr .r0)) 320) t1Max).map fun c => ofInt (c * 2 ^ d : Nat)) := by
  sig_post [unpackT1Contract, unpackT1Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem t1_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1) :
    (unpackT1Contract Arm.abi stk).pub x y := by
  sig_pub [unpackT1Contract, unpackT1Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1⟩

end

/-! ## `vg_mldsa_hint_bit_unpack` -/

section
variable {stk : Nat} {x y : State} {yy len om h hl : BitVec 32}

theorem hbu_pre (g0 : x.gpr .r0 = yy) (g1 : x.gpr .r1 = len) (g2 : x.gpr .r2 = om) (g3 : x.gpr .r3 = h)
    (ga : stackArg x 0 = hl)
    (hrd : x.rd = [regA yy len.toNat, ⟨stackArgAddr x 0, 4⟩]) (hwr : x.wr = [regA h (hl.toNat * 4)])
    (hsp : stk ≤ x.sp.toNat) (hs4 : x.sp.toNat + 4 ≤ 2 ^ 32)
    (d1 : (regA yy len.toNat).Disjoint (regA h (hl.toNat * 4)))
    (d2 : (regA h (hl.toNat * 4)).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (k1 : (below x stk).Disjoint (regA yy len.toNat)) (k2 : (below x stk).Disjoint (regA h (hl.toNat * 4)))
    (k3 : (below x stk).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (f1 : yy.toNat + len.toNat ≤ 2 ^ 32) (f2 : h.toNat + hl.toNat * 4 ≤ 2 ^ 32)
    (hp : (om.toNat, len.toNat - om.toNat) ∈ hintParams) (ho : om.toNat ≤ len.toNat)
    (hh : hl.toNat = 256 * (len.toNat - om.toNat)) :
    (hintBitUnpackContract Arm.abi stk).pre x := by
  sig_pre [hintBitUnpackContract, hintBitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, g3, ga]
  try simp only [State.addr] at *
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | (have := State.sp _ |>.isLt; omega_arith) | omega_arith | skip)
    | (have := State.sp _ |>.isLt; omega_arith)
    | omega_arith
    | skip
  all_goals assumption

theorem hbu_post (hp : (hintBitUnpackContract Arm.abi stk).post x y) :
    match hintBitUnpack (x.gpr .r2).toNat ((x.gpr .r1).toNat - (x.gpr .r2).toNat)
      (bytesAt x.mem (State.addr (x.gpr .r0)) (x.gpr .r1).toNat) with
    | some hint => y.gpr .r0 = 1 ∧ HintIs y.mem (State.addr (x.gpr .r3)) ((x.gpr .r1).toNat - (x.gpr .r2).toNat) hint
    | none => y.gpr .r0 = 0 := by
  sig_post [hintBitUnpackContract, hintBitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  rwa [setWidth_append32] at hp

theorem hbu_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) (h3 : x.gpr .r3 = y.gpr .r3) (ha : stackArg x 0 = stackArg y 0)
    (hl : bytesAt x.mem (State.addr (x.gpr .r0)) (x.gpr .r1).toNat =
      bytesAt y.mem (State.addr (y.gpr .r0)) (y.gpr .r1).toNat) :
    (hintBitUnpackContract Arm.abi stk).pub x y := by
  sig_pub [hintBitUnpackContract, hintBitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, congrArg leakBytes hl, h0, h1, h2, h3, ha⟩

end

/-! ## `vg_mldsa_norm_lt` -/

section
variable {stk : Nat} {x y : State} {f : BitVec 32}

theorem normLt_pre (g0 : x.gpr .r0 = f) (hrd : x.rd = [regA f 1024]) (hwr : x.wr = [])
    (hsp : stk ≤ x.sp.toNat) (k1 : (below x stk).Disjoint (regA f 1024)) (f1 : f.toNat + 1024 ≤ 2 ^ 32)
    (hr : Reduced x.mem (State.addr f)) : (normLtContract Arm.abi stk).pre x := by
  sig_pre [normLtContract, normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0]
  try simp only [State.addr] at *
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | (have := State.sp _ |>.isLt; omega_arith) | omega_arith | skip)
    | (have := State.sp _ |>.isLt; omega_arith)
    | omega_arith
    | skip
  all_goals assumption

theorem normLt_post (hp : (normLtContract Arm.abi stk).post x y) :
    y.gpr .r0 = if normRq [polyAt x.mem (State.addr (x.gpr .r0))] < (x.gpr .r1).toNat then 1 else 0 := by
  sig_post [normLtContract, normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  rwa [setWidth_append32] at hp

theorem normLt_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1) :
    (normLtContract Arm.abi stk).pub x y := by
  sig_pub [normLtContract, normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1⟩

end

end VG.Proof.MlDsa.Arm.KeyGen

end

end

/-!
# ML-DSA on 32-bit ARM: calling the primitives on the buffers of a `Site`

A call of each primitive, with its arguments pointers into the buffers of a
`Site` (`PtrIn`): the callee's precondition from the layout (`ip_preS`, …),
what the call changes and what its postcondition says (`ip_ok`, …), and that
two runs of it with the same pointers leak the same (`ip_tr`, …).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A pointer, in a register of the layout, to `l` bytes of a buffer (but the stack). -/
def PtrIn (L : Lay) (q : Ptr) (l : Nat) : Prop := argOk (.ptr q) = true ∧ inB L.sizes (tri q l) = true

section
variable {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : Site L Wb STK s)
include hs

theorem Site.regE {q : Ptr} {l : Nat} (pq : PtrIn L q l) (hl : 0 < l) :
    regA (L.ptr (ix q.1) + BitVec.ofNat 32 q.2) l = L.R (ix q.1) q.2 l := by
  simp only [regA, (hs.addr pq.2 hl).1]

theorem Site.fitE {q : Ptr} {l : Nat} (pq : PtrIn L q l) (hl : 0 < l) :
    (L.ptr (ix q.1) + BitVec.ofNat 32 q.2).toNat + l ≤ 2 ^ 32 := (hs.addr pq.2 hl).2

theorem Site.addrE {q : Ptr} {l : Nat} (pq : PtrIn L q l) (hl : 0 < l) :
    State.addr (L.ptr (ix q.1) + BitVec.ofNat 32 q.2) = lpa L q := (hs.addr pq.2 hl).1

/-- A pointer argument's register after the moves. -/
theorem Site.gE {as : List (Reg × Arg)} (hg : glueOk as = true) (hn : (as.map Prod.fst).Nodup) {d : Reg} {q : Ptr}
    (hm : (d, .ptr q) ∈ as) (hq : argOk (.ptr q) = true) :
    (glueSt s as).gpr d = L.ptr (ix q.1) + BitVec.ofNat 32 q.2 := by
  rw [glueSt_arg s hg hn hm, hs.val hq]

/-- A buffer the state may write. -/
theorem Site.cwE {q : Ptr} {l : Nat} (pq : PtrIn L q l) (wq : ix q.1 ∈ Wb) : Covers [L.R (ix q.1) q.2 l] s.wr :=
  Site.covW (w := (ix q.1, q.2, l)) pq.2 (hs.cw _ wq (inB_bounds pq.2).1)

/-- A buffer the state may read. -/
theorem Site.crE {q : Ptr} {l : Nat} (pq : PtrIn L q l) : Covers [L.R (ix q.1) q.2 l] (s.rd ++ s.wr) :=
  Site.covR (w := (ix q.1, q.2, l)) pq.2 (hs.cr _ (by have := (inB_bounds pq.2).2.1; rw [hs.len] at this; exact this) (inB_bounds pq.2).1)

/-- Two regions apart, one of them written. -/
theorem Site.dE {q q' : Ptr} {l l' : Nat} (hd : sepB L.sizes (tri q l) (tri q' l') = true)
    (hw : ix q.1 ∈ Wb ∨ ix q'.1 ∈ Wb) : (L.R (ix q.1) q.2 l).Disjoint (L.R (ix q'.1) q'.2 l') := disjW hs.ok hd hw

/-- The stack below the stack pointer is apart from a buffer. -/
theorem Site.kE {q : Ptr} {l : Nat} (pq : PtrIn L q l) {n : Nat} (hn : n ≤ STK) {x : State} (hx : x.sp = s.sp) :
    (below x n).Disjoint (L.R (ix q.1) q.2 l) := by
  have := (hs.stkD pq.2 hn).symm
  simp only [below, hx] at this ⊢
  exact this

end

theorem view_glue_sp (s : State) (as : List (Reg × Arg)) (rd wr : List Region) :
    (view (glueSt s as) rd wr).sp = s.sp := glueSt_sp s as

theorem view_glue_mem (s : State) (as : List (Reg × Arg)) (rd wr : List Region) :
    (view (glueSt s as) rd wr).mem = s.mem := glueSt_mem s as

/-- The registers of the layout, the stack pointer, and the pointers of both
runs are the same. -/
theorem Site.gpr_eq {L : Lay} {Wb : List Nat} {STK : Nat} {x y : State} (hx : Site L Wb STK x) (hy : Site L Wb STK y)
    {as : List (Reg × Arg)} (hg : glueOk as = true) (hn : (as.map Prod.fst).Nodup) {d : Reg} {a : Arg} (hm : (d, a) ∈ as) :
    (glueSt x as).gpr d = (glueSt y as).gpr d := by
  rw [glueSt_arg x hg hn hm, glueSt_arg y hg hn hm]
  cases a with
  | imm v => rfl
  | ptr q =>
    have ha : argOk (.ptr q) = true := by
      have := List.all_eq_true.mp hg _ hm; simp only [Bool.and_eq_true] at this; exact this.2
    rw [hx.val ha, hy.val ha]

/-- Kept, with the regions written those of the triples `W`. -/
theorem Site.keptW {L : Lay} {Wb : List Nat} {STK : Nat} {s s' : State} (hs : Site L Wb STK s)
    (W : List (Nat × Nat × Nat)) {n : Nat} (hn : n ≤ STK) (hk : Kept (L.RL W ++ [below s n]) s s') :
    Kept (L.RL (W ++ [(1, 0, STK)])) s s' :=
  hs.kept_stk (fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact ⟨w, hw, fun _ h => h⟩) hn hk

theorem imm_toNat {v : Nat} (h : v < 2 ^ 32) : (BitVec.ofNat 32 v).toNat = v := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-! ## Calls in a frame that pushes the stack argument -/

section
variable {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : Site L Wb STK s) (s1 : State)
  (e1 : s1.sp = s.sp) (rd wr : List Region)
include hs e1

omit hs in
theorem push_sp : (view (pushed [.r12] s1) rd wr).sp = s.sp - BitVec.ofNat 32 4 := by
  simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, e1]; rfl

omit hs in
theorem push_spN (h4 : 4 ≤ s.sp.toNat) : (view (pushed [.r12] s1) rd wr).sp.toNat = s.sp.toNat - 4 := by
  rw [push_sp s1 e1]; bv_omega

omit hs in
theorem push_argAddr : stackArgAddr (view (pushed [.r12] s1) rd wr) 0 = State.addr (s.sp - BitVec.ofNat 32 4) := by
  show State.addr ((view (pushed [.r12] s1) rd wr).sp + BitVec.ofNat 32 (4 * 0)) = _
  rw [push_sp s1 e1]; congr 1; bv_omega

omit hs e1 in
theorem push_arg : stackArg (view (pushed [.r12] s1) rd wr) 0 = s1.gpr .r12 := by
  have e : stackArgAddr (view (pushed [.r12] s1) rd wr) 0 = State.addr (s1.sp - BitVec.ofNat 32 4) := by
    show State.addr ((pushed [.r12] s1).sp + BitVec.ofNat 32 (4 * 0)) = _
    rw [pushed_sp]; congr 1; simp only [List.length_cons, List.length_nil]; bv_omega
  show (pushed [.r12] s1).mem.readW (stackArgAddr (view (pushed [.r12] s1) rd wr) 0) 32 = _
  rw [e]; exact pushed12_word s1

/-- The stack a callee in the frame may use is apart from a buffer. -/
theorem push_kE {q : Ptr} {l : Nat} (pq : PtrIn L q l) {n : Nat} (hn : 4 + n ≤ STK) :
    (below (view (pushed [.r12] s1) rd wr) n).Disjoint (L.R (ix q.1) q.2 l) := by
  have h4 : 4 + n ≤ s.sp.toNat := Nat.le_trans hn hs.spk
  refine ((hs.stkD pq.2 hn).symm).sub_left ?_
  intro x hx
  have := addr_toNat' s.sp
  have := addr_toNat' (s.sp - BitVec.ofNat 32 4)
  simp only [Region.Contains, push_sp s1 e1] at hx ⊢
  bv_omega

/-- The stack slot of the argument is apart from a buffer. -/
theorem push_aE {q : Ptr} {l : Nat} (pq : PtrIn L q l) :
    (L.R (ix q.1) q.2 l).Disjoint ⟨stackArgAddr (view (pushed [.r12] s1) rd wr) 0, 4⟩ := by
  rw [push_argAddr s1 e1 rd wr]
  refine (hs.stkD pq.2 (n := 4) (by have := hs.s8; omega_using [this])).sub_right ?_
  intro x hx
  have := addr_toNat' s.sp
  have := addr_toNat' (s.sp - BitVec.ofNat 32 4)
  have := hs.s8; have := hs.spk
  simp only [Region.Contains] at hx ⊢
  bv_omega

/-- The stack a callee in the frame may use is apart from the stack slot of its argument. -/
theorem push_kA {n : Nat} (hn : 4 + n ≤ STK) :
    (below (view (pushed [.r12] s1) rd wr) n).Disjoint ⟨stackArgAddr (view (pushed [.r12] s1) rd wr) 0, 4⟩ := by
  rw [push_argAddr s1 e1 rd wr]
  intro x hx hy
  have := addr_toNat' (s.sp - BitVec.ofNat 32 4)
  have := hs.s8; have := hs.spk
  simp only [Region.Contains, push_sp s1 e1] at hx hy
  bv_omega

/-- The memory of the frame: the pushed word below the stack pointer. -/
theorem push_frame (hm : s1.mem = s.mem) : Frame [below s 4] s.mem (view (pushed [.r12] s1) rd wr).mem := by
  have h4 : 4 ≤ s1.sp.toNat := by rw [e1]; have := hs.s8; have := hs.spk; omega_arith
  have := pushed12_frame s1 h4
  simp only [below, e1, hm] at this
  exact this

/-- A buffer's bytes in the frame. -/
theorem push_bytes (hm : s1.mem = s.mem) {q : Ptr} {l : Nat} (pq : PtrIn L q l) (hl : l ≤ 2 ^ 64) :
    ∀ k < l, (view (pushed [.r12] s1) rd wr).mem (lpa L q + BitVec.ofNat 64 k) = s.mem (lpa L q + BitVec.ofNat 64 k) :=
  Proof.MlKem.bytes_frame (push_frame hs s1 e1 rd wr hm) (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hs.stkD pq.2 (by have := hs.s8; omega_using [this])) hl

omit hs e1 in
theorem push_fit (h4 : 4 ≤ s.sp.toNat) (e1 : s1.sp = s.sp) :
    (view (pushed [.r12] s1) rd wr).sp.toNat + 4 ≤ 2 ^ 32 := by
  rw [push_spN s1 e1 rd wr h4]; have := s.sp.isLt; omega_using []

end

theorem sp4 {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : Site L Wb STK s) : 4 ≤ s.sp.toNat := by
  have := hs.s8; have := hs.spk; omega_arith

/-- A polynomial of a buffer in the frame. -/
theorem push_reduced {L : Lay} {Wb : List Nat} {STK : Nat} {s s1 : State} (hs : Site L Wb STK s) (e1 : s1.sp = s.sp)
    (hm : s1.mem = s.mem) (rd wr : List Region) {q : Ptr} (pq : PtrIn L q 1024) :
    Reduced (view (pushed [.r12] s1) rd wr).mem (lpa L q) ↔ Reduced s.mem (lpa L q) :=
  ⟨Proof.MlDsa.Verify.reduced_congr fun k hk => (push_bytes hs s1 e1 rd wr hm pq (by decide) k hk).symm,
    Proof.MlDsa.Verify.reduced_congr (push_bytes hs s1 e1 rd wr hm pq (by decide))⟩

theorem push_polyAt {L : Lay} {Wb : List Nat} {STK : Nat} {s s1 : State} (hs : Site L Wb STK s) (e1 : s1.sp = s.sp)
    (hm : s1.mem = s.mem) (rd wr : List Region) {q : Ptr} (pq : PtrIn L q 1024) :
    polyAt (view (pushed [.r12] s1) rd wr).mem (lpa L q) = polyAt s.mem (lpa L q) :=
  Proof.MlDsa.Verify.polyAt_congr (push_bytes hs s1 e1 rd wr hm pq (by decide))

theorem push_coeffAt {L : Lay} {Wb : List Nat} {STK : Nat} {s s1 : State} (hs : Site L Wb STK s) (e1 : s1.sp = s.sp)
    (hm : s1.mem = s.mem) (rd wr : List Region) {q : Ptr} (pq : PtrIn L q 1024) {i : Nat} (hi : i < n) :
    coeffAt (view (pushed [.r12] s1) rd wr).mem (lpa L q) i = coeffAt s.mem (lpa L q) i :=
  Proof.MlDsa.Verify.coeffAt_congr (push_bytes hs s1 e1 rd wr hm pq (by decide)) hi

theorem push_bytesAt {L : Lay} {Wb : List Nat} {STK : Nat} {s s1 : State} (hs : Site L Wb STK s) (e1 : s1.sp = s.sp)
    (hm : s1.mem = s.mem) (rd wr : List Region) {q : Ptr} {l : Nat} (pq : PtrIn L q l) (hl : l < 2 ^ 64) :
    bytesAt (view (pushed [.r12] s1) rd wr).mem (lpa L q) l = bytesAt s.mem (lpa L q) l := by
  have hb := push_bytes hs s1 e1 rd wr hm pq (Nat.le_of_lt hl)
  exact Proof.MlKem.bytesAt_eq! (by simp [bytesAt]) fun k hk => by
    rw [Proof.MlKem.bytesAt_getElem! _ _ hk, hb k hk]

/-! ## `vg_mldsa_ntt`, `vg_mldsa_inv_ntt` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {t : Poly → Poly} {f w : Ptr}

abbrev ipArgs (f w : Ptr) : List (Reg × Arg) := [(.r0, .ptr f), (.r1, .ptr w)]
abbrev ipWr (L : Lay) (f w : Ptr) : List Region := [L.R (ix f.1) f.2 1024, L.R (ix w.1) w.2 1024]

theorem ip_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (pf : PtrIn L f 1024)
    (pw : PtrIn L w 1024) (wf : ix f.1 ∈ Wb) (hd : sepB L.sizes (tri f 1024) (tri w 1024) = true)
    (hr : Reduced s.mem (lpa L f)) :
    (inPlaceContract Arm.abi t stk).pre (view (glueSt s (ipArgs f w)) [] (ipWr L f w)) := by
  have hg : glueOk (ipArgs f w) = true := by simp [glueOk, pf.1, pw.1]
  have hn : ((ipArgs f w).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide
  have hsp := view_glue_sp s (ipArgs f w) [] (ipWr L f w)
  refine ip_pre (by rw [view_r0, hs.gE hg hn (by simp) pf.1]) (by rw [view_r1, hs.gE hg hn (by simp) pw.1]) rfl
    (by rw [State.withRegions_wr, hs.regE pf (by decide), hs.regE pw (by decide)])
    (by rw [hsp]; exact Nat.le_trans hstk hs.spk) ?_ ?_ ?_ (hs.fitE pf (by decide)) (hs.fitE pw (by decide)) ?_
  · rw [hs.regE pf (by decide), hs.regE pw (by decide)]; exact hs.dE hd (.inl wf)
  · rw [hs.regE pf (by decide)]; exact hs.kE pf hstk hsp
  · rw [hs.regE pw (by decide)]; exact hs.kE pw hstk hsp
  · rw [view_glue_mem, hs.addrE pf (by decide)]; exact hr

theorem ip_ok {c : Prog isa} (hc : Callee c (fun stk => inPlaceContract Arm.abi t stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (pf : PtrIn L f 1024) (pw : PtrIn L w 1024)
    (wf : ix f.1 ∈ Wb) (ww : ix w.1 ∈ Wb) (hd : sepB L.sizes (tri f 1024) (tri w 1024) = true)
    (hr : Reduced s.mem (lpa L f)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri f 1024, tri w 1024, (1, 0, STK)]) s s' →
      PolyIs s'.mem (lpa L f) (t (polyAt s.mem (lpa L f))) → Q s') :
    WP isa (callAt name c (ipArgs f w)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  have hg : glueOk (ipArgs f w) = true := by simp [glueOk, pf.1, pw.1]
  have hn : ((ipArgs f w).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide
  have cw : Covers (ipWr L f w) s.wr := covers_cons' (hs.cwE pf wf) (covers_cons' (hs.cwE pw ww) covers_nil')
  refine callV hver.1 hg (ip_preS hs (Nat.le_trans hstk hS) pf pw wf hd hr) (Covers.right cw) cw
    (by have := hs.spk; have := hc.stack; omega_arith) fun s' hk hp =>
      hQ s' (hs.kept_stk (W := [tri f 1024, tri w 1024]) (fun r hr => ?_) (Nat.le_trans hc.stack hS) hk) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
  · have := ip_post hp
    rwa [State.withRegions_mem, view_r0, hs.gE hg hn (by simp) pf.1, hs.addrE pf (by decide), view_glue_mem] at this

theorem ip_tr {c : Prog isa} (hc : Callee c (fun stk => inPlaceContract Arm.abi t stk) S) (hS : S ≤ STK)
    {name : String} (pf : PtrIn L f 1024) (pw : PtrIn L w 1024) (wf : ix f.1 ∈ Wb) (ww : ix w.1 ∈ Wb)
    (hd : sepB L.sizes (tri f 1024) (tri w 1024) = true) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (lpa L f) ∧
      Reduced y.mem (lpa L f)) :
    RelCT isa P (callAt name c (ipArgs f w)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  have hg : glueOk (ipArgs f w) = true := by simp [glueOk, pf.1, pw.1]
  have hn : ((ipArgs f w).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide
  refine callV_tr hver.1 hver.2.1 hg fun x y h => ?_
  obtain ⟨hx, hy, hsp, rx, ry⟩ := hP x y h
  have cx : Covers (ipWr L f w) x.wr := covers_cons' (hx.cwE pf wf) (covers_cons' (hx.cwE pw ww) covers_nil')
  have cy : Covers (ipWr L f w) y.wr := covers_cons' (hy.cwE pf wf) (covers_cons' (hy.cwE pw ww) covers_nil')
  refine ⟨[], ipWr L f w, ip_preS hx (Nat.le_trans hstk hS) pf pw wf hd rx,
    ip_preS hy (Nat.le_trans hstk hS) pf pw wf hd ry, ip_pub ?_ ?_ ?_, Covers.right cx, cx, Covers.right cy, cy⟩
  · rw [view_glue_sp, view_glue_sp, hsp]
  · rw [view_r0, view_r0, hx.gE hg hn (by simp) pf.1, hy.gE hg hn (by simp) pf.1]
  · rw [view_r1, view_r1, hx.gE hg hn (by simp) pw.1, hy.gE hg hn (by simp) pw.1]

end

end VG.Proof.MlDsa.Arm.KeyGen
