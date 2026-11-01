module

public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.MlDsa.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on PPC64LE: the contracts of the primitives, evaluated

As on 32-bit ARM (`Proof/MlDsa/Arm/KeyGen/Contracts.lean`): for each
primitive the top-level functions call, its contract's precondition
(`ip_pre`, …), from plain facts about the state `x` the callee starts from:
the arguments in their registers, the regions it is given, their
disjointness and the stack below `x.sp`; what its postcondition says
(`…_post`); and its public data, from the equalities of two such states
(`…_pub`). Each is proven once, by evaluating the contract (`sig_pre`,
`sig_post`, `sig_pub`) on a state that is a variable. Every argument is in a
register; a `u32` argument is the low word of its register.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.KeyGen

open VG VG.PPC64LE
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- `l` bytes at `a`. -/
abbrev reg (a : Addr) (l : Nat) : Region := ⟨a, l⟩

/-! ## `vg_mldsa_ntt`, `vg_mldsa_inv_ntt` -/

section
variable {stk : Nat} {x y : State}

theorem ip_pre {t : Poly → Poly} {f w : Addr} (g3 : x.gpr .r3 = f) (g4 : x.gpr .r4 = w)
    (hrd : x.rd = []) (hwr : x.wr = [reg f 1024, reg w 1024]) (hsp : stk ≤ x.sp.toNat)
    (hd : (reg f 1024).Disjoint (reg w 1024)) (kf : (below x.sp stk).Disjoint (reg f 1024))
    (kw : (below x.sp stk).Disjoint (reg w 1024)) (ff : f.toNat + 1024 ≤ 2 ^ 64) (fw : w.toNat + 1024 ≤ 2 ^ 64)
    (hr : Reduced x.mem f) :
    (inPlaceContract PPC64LE.abi t stk).pre x := by
  sig_pre [inPlaceContract, inPlaceSig, PPC64LE.abi, PPC64LE.argRegs]
  simp only [g3, g4]
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | omega | skip)
    | omega
    | skip
  all_goals assumption

theorem ip_post {t : Poly → Poly} (h : (inPlaceContract PPC64LE.abi t stk).post x y) :
    PolyIs y.mem (x.gpr .r3) (t (polyAt x.mem (x.gpr .r3))) := by
  sig_post [inPlaceContract, inPlaceSig, PPC64LE.abi, PPC64LE.argRegs] at h
  exact h

theorem ip_pub {t : Poly → Poly} (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4) :
    (inPlaceContract PPC64LE.abi t stk).pub x y := by
  sig_pub [inPlaceContract, inPlaceSig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨hsp, h3, h4⟩

end

/-! ## `vg_mldsa_multiply_ntt`, `vg_mldsa_multiply_add_ntt` -/

section
variable {stk : Nat} {x y : State} {h f g : Addr}

theorem mul_pre (g3 : x.gpr .r3 = h) (g4 : x.gpr .r4 = f) (g5 : x.gpr .r5 = g)
    (hrd : x.rd = [reg f 1024, reg g 1024]) (hwr : x.wr = [reg h 1024]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (reg h 1024).Disjoint (reg f 1024)) (d2 : (reg h 1024).Disjoint (reg g 1024))
    (kh : (below x.sp stk).Disjoint (reg h 1024)) (kf : (below x.sp stk).Disjoint (reg f 1024))
    (kg : (below x.sp stk).Disjoint (reg g 1024)) (fh : h.toNat + 1024 ≤ 2 ^ 64) (ff : f.toNat + 1024 ≤ 2 ^ 64)
    (fg : g.toNat + 1024 ≤ 2 ^ 64) (rf : Reduced x.mem f) (rg : Reduced x.mem g) :
    (mulContract PPC64LE.abi stk).pre x := by
  sig_pre [mulContract, mulSig, PPC64LE.abi, PPC64LE.argRegs]
  simp only [g3, g4, g5]
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | omega | skip)
    | omega
    | skip
  all_goals assumption

theorem mul_post (hp : (mulContract PPC64LE.abi stk).post x y) :
    PolyIs y.mem (x.gpr .r3) (multiplyNTT (polyAt x.mem (x.gpr .r4)) (polyAt x.mem (x.gpr .r5))) := by
  sig_post [mulContract, mulSig, PPC64LE.abi, PPC64LE.argRegs] at hp
  exact hp

theorem mulAdd_pre (g3 : x.gpr .r3 = h) (g4 : x.gpr .r4 = f) (g5 : x.gpr .r5 = g)
    (hrd : x.rd = [reg f 1024, reg g 1024]) (hwr : x.wr = [reg h 1024]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (reg h 1024).Disjoint (reg f 1024)) (d2 : (reg h 1024).Disjoint (reg g 1024))
    (kh : (below x.sp stk).Disjoint (reg h 1024)) (kf : (below x.sp stk).Disjoint (reg f 1024))
    (kg : (below x.sp stk).Disjoint (reg g 1024)) (fh : h.toNat + 1024 ≤ 2 ^ 64) (ff : f.toNat + 1024 ≤ 2 ^ 64)
    (fg : g.toNat + 1024 ≤ 2 ^ 64) (rh : Reduced x.mem h) (rf : Reduced x.mem f) (rg : Reduced x.mem g) :
    (mulAddContract PPC64LE.abi stk).pre x := by
  sig_pre [mulAddContract, mulSig, PPC64LE.abi, PPC64LE.argRegs]
  simp only [g3, g4, g5]
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | omega | skip)
    | omega
    | skip
  all_goals assumption

theorem mulAdd_post (hp : (mulAddContract PPC64LE.abi stk).post x y) :
    PolyIs y.mem (x.gpr .r3) (add (polyAt x.mem (x.gpr .r3))
      (multiplyNTT (polyAt x.mem (x.gpr .r4)) (polyAt x.mem (x.gpr .r5)))) := by
  sig_post [mulAddContract, mulSig, PPC64LE.abi, PPC64LE.argRegs] at hp
  exact hp

theorem mul_pub (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4)
    (h5 : x.gpr .r5 = y.gpr .r5) : (mulContract PPC64LE.abi stk).pub x y := by
  sig_pub [mulContract, mulSig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨hsp, h3, h4, h5⟩

theorem mulAdd_pub (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4)
    (h5 : x.gpr .r5 = y.gpr .r5) : (mulAddContract PPC64LE.abi stk).pub x y := by
  sig_pub [mulAddContract, mulSig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨hsp, h3, h4, h5⟩

end

/-! ## `vg_mldsa_add` -/

section
variable {stk : Nat} {x y : State} {f g : Addr}

theorem add_pre (g3 : x.gpr .r3 = f) (g4 : x.gpr .r4 = g) (hrd : x.rd = [reg g 1024])
    (hwr : x.wr = [reg f 1024]) (hsp : stk ≤ x.sp.toNat) (d1 : (reg f 1024).Disjoint (reg g 1024))
    (kf : (below x.sp stk).Disjoint (reg f 1024)) (kg : (below x.sp stk).Disjoint (reg g 1024))
    (ff : f.toNat + 1024 ≤ 2 ^ 64) (fg : g.toNat + 1024 ≤ 2 ^ 64) (rf : Reduced x.mem f)
    (rg : Reduced x.mem g) : (addContract PPC64LE.abi stk).pre x := by
  sig_pre [addContract, accSig, PPC64LE.abi, PPC64LE.argRegs]
  simp only [g3, g4]
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | omega | skip)
    | omega
    | skip
  all_goals assumption

theorem add_post (hp : (addContract PPC64LE.abi stk).post x y) :
    PolyIs y.mem (x.gpr .r3) (add (polyAt x.mem (x.gpr .r3)) (polyAt x.mem (x.gpr .r4))) := by
  sig_post [addContract, accSig, PPC64LE.abi, PPC64LE.argRegs] at hp
  exact hp

theorem add_pub (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4) :
    (addContract PPC64LE.abi stk).pub x y := by
  sig_pub [addContract, accSig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨hsp, h3, h4⟩

end

/-! ## `vg_mldsa_rej_ntt_poly`, `vg_mldsa_rej_bounded_poly` -/

section
variable {stk : Nat} {x y : State} {sd a w : Addr}

theorem rejNtt_pre (g3 : x.gpr .r3 = sd) (g4 : x.gpr .r4 = a) (g5 : x.gpr .r5 = w)
    (hrd : x.rd = [reg sd 34]) (hwr : x.wr = [reg a 1024, reg w 2048]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (reg sd 34).Disjoint (reg a 1024)) (d2 : (reg sd 34).Disjoint (reg w 2048))
    (d3 : (reg a 1024).Disjoint (reg w 2048))
    (k1 : (below x.sp stk).Disjoint (reg sd 34)) (k2 : (below x.sp stk).Disjoint (reg a 1024))
    (k3 : (below x.sp stk).Disjoint (reg w 2048)) (f1 : sd.toNat + 34 ≤ 2 ^ 64) (f2 : a.toNat + 1024 ≤ 2 ^ 64)
    (f3 : w.toNat + 2048 ≤ 2 ^ 64) : (rejNTTContract PPC64LE.abi stk).pre x := by
  sig_pre [rejNTTContract, rejNTTSig, PPC64LE.abi, PPC64LE.argRegs]
  simp only [g3, g4, g5]
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | omega | skip)
    | omega
    | skip
  all_goals assumption

theorem rejNtt_post (hp : (rejNTTContract PPC64LE.abi stk).post x y) :
    ((y.gpr .r3).setWidth 32 = 1 → Reduced y.mem (x.gpr .r4)) ∧
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt x.mem (x.gpr .r3) 34)) ((y.gpr .r3).setWidth 32)
        (polyAt y.mem (x.gpr .r4)) := by
  sig_post [rejNTTContract, rejNTTSig, PPC64LE.abi, PPC64LE.argRegs] at hp
  exact hp

theorem rejNtt_pub (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4)
    (h5 : x.gpr .r5 = y.gpr .r5) (hl : bytesAt x.mem (x.gpr .r3) 34 = bytesAt y.mem (y.gpr .r3) 34) :
    (rejNTTContract PPC64LE.abi stk).pub x y := by
  sig_pub [rejNTTContract, rejNTTSig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨hsp, congrArg leakBytes hl, h3, h4, h5⟩

end

section
variable {stk : Nat} {x y : State} {sd a w : Addr} {e : BitVec 32}

theorem rejBounded_pre (g3 : x.gpr .r3 = sd) (g4 : (x.gpr .r4).setWidth 32 = e) (g5 : x.gpr .r5 = a)
    (g6 : x.gpr .r6 = w)
    (hrd : x.rd = [reg sd 66]) (hwr : x.wr = [reg a 1024, reg w 2048]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (reg sd 66).Disjoint (reg a 1024)) (d2 : (reg sd 66).Disjoint (reg w 2048))
    (d3 : (reg a 1024).Disjoint (reg w 2048))
    (k1 : (below x.sp stk).Disjoint (reg sd 66)) (k2 : (below x.sp stk).Disjoint (reg a 1024))
    (k3 : (below x.sp stk).Disjoint (reg w 2048)) (f1 : sd.toNat + 66 ≤ 2 ^ 64) (f2 : a.toNat + 1024 ≤ 2 ^ 64)
    (f3 : w.toNat + 2048 ≤ 2 ^ 64) (he : e.toNat = 2 ∨ e.toNat = 4) :
    (rejBoundedContract PPC64LE.abi stk).pre x := by
  sig_pre [rejBoundedContract, rejBoundedSig, PPC64LE.abi, PPC64LE.argRegs]
  simp only [g3, g4, g5, g6]
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | omega | skip)
    | omega
    | skip
  all_goals assumption

theorem rejBounded_post (hp : (rejBoundedContract PPC64LE.abi stk).post x y) :
    ((y.gpr .r3).setWidth 32 = 1 → Reduced y.mem (x.gpr .r5)) ∧
      Outcome (fun b => (rejBoundedPoly ((x.gpr .r4).setWidth 32).toNat b.rejBounded (bytesAt x.mem (x.gpr .r3) 66)).map
        toRq) ((y.gpr .r3).setWidth 32) (polyAt y.mem (x.gpr .r5)) := by
  sig_post [rejBoundedContract, rejBoundedSig, PPC64LE.abi, PPC64LE.argRegs] at hp
  exact hp

theorem rejBounded_pub (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4)
    (h5 : x.gpr .r5 = y.gpr .r5) (h6 : x.gpr .r6 = y.gpr .r6)
    (hl : rejBoundedLeak ((x.gpr .r4).setWidth 32).toNat (bytesAt x.mem (x.gpr .r3) 66) =
      rejBoundedLeak ((y.gpr .r4).setWidth 32).toNat (bytesAt y.mem (y.gpr .r3) 66)) :
    (rejBoundedContract PPC64LE.abi stk).pub x y := by
  sig_pub [rejBoundedContract, rejBoundedSig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨hsp, hl, h3, congrArg _ h4, h5, h6⟩

end

/-! ## `vg_mldsa_power2round` -/

section
variable {stk : Nat} {x y : State} {t t1 t0 : Addr}

theorem p2r_pre (g3 : x.gpr .r3 = t) (g4 : x.gpr .r4 = t1) (g5 : x.gpr .r5 = t0)
    (hrd : x.rd = [reg t 1024]) (hwr : x.wr = [reg t1 1024, reg t0 1024]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (reg t 1024).Disjoint (reg t1 1024)) (d2 : (reg t 1024).Disjoint (reg t0 1024))
    (d3 : (reg t1 1024).Disjoint (reg t0 1024))
    (k1 : (below x.sp stk).Disjoint (reg t 1024)) (k2 : (below x.sp stk).Disjoint (reg t1 1024))
    (k3 : (below x.sp stk).Disjoint (reg t0 1024)) (f1 : t.toNat + 1024 ≤ 2 ^ 64) (f2 : t1.toNat + 1024 ≤ 2 ^ 64)
    (f3 : t0.toNat + 1024 ≤ 2 ^ 64) (hr : Reduced x.mem t) : (power2RoundContract PPC64LE.abi stk).pre x := by
  sig_pre [power2RoundContract, power2RoundSig, PPC64LE.abi, PPC64LE.argRegs]
  simp only [g3, g4, g5]
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | omega | skip)
    | omega
    | skip
  all_goals assumption

theorem p2r_post (hp : (power2RoundContract PPC64LE.abi stk).post x y) :
    NatPolyIs y.mem (x.gpr .r4) ((polyAt x.mem (x.gpr .r3)).map fun c => (power2Round c).1.toNat) ∧
      PolyIs y.mem (x.gpr .r5) ((polyAt x.mem (x.gpr .r3)).map fun c => ofInt (power2Round c).2) := by
  sig_post [power2RoundContract, power2RoundSig, PPC64LE.abi, PPC64LE.argRegs] at hp
  exact hp

theorem p2r_pub (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4)
    (h5 : x.gpr .r5 = y.gpr .r5) : (power2RoundContract PPC64LE.abi stk).pub x y := by
  sig_pub [power2RoundContract, power2RoundSig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨hsp, h3, h4, h5⟩

end

/-! ## `vg_mldsa_simple_bit_pack`, `vg_mldsa_bit_pack` -/

section
variable {stk : Nat} {x y : State} {f o : Addr} {a b : BitVec 32} {l : BitVec 64}

theorem sbp_pre (g3 : x.gpr .r3 = f) (g4 : (x.gpr .r4).setWidth 32 = b) (g5 : x.gpr .r5 = o) (g6 : x.gpr .r6 = l)
    (hrd : x.rd = [reg f 1024]) (hwr : x.wr = [reg o l.toNat]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (reg f 1024).Disjoint (reg o l.toNat))
    (k1 : (below x.sp stk).Disjoint (reg f 1024)) (k2 : (below x.sp stk).Disjoint (reg o l.toNat))
    (f1 : f.toNat + 1024 ≤ 2 ^ 64) (f2 : o.toNat + l.toNat ≤ 2 ^ 64) (hb : b.toNat ∈ simpleBitPackBounds)
    (hl : l.toNat = 32 * bitlen b.toNat) (hc : ∀ i < n, (coeffAt x.mem f i).toNat ≤ b.toNat) :
    (simpleBitPackContract PPC64LE.abi stk).pre x := by
  sig_pre [simpleBitPackContract, simpleBitPackSig, PPC64LE.abi, PPC64LE.argRegs]
  simp only [g3, g4, g5, g6]
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | omega | skip)
    | omega
    | skip
  all_goals assumption

theorem sbp_post (hp : (simpleBitPackContract PPC64LE.abi stk).post x y) :
    bytesAt y.mem (x.gpr .r5) (x.gpr .r6).toNat =
      simpleBitPack (natPolyAt x.mem (x.gpr .r3)) ((x.gpr .r4).setWidth 32).toNat := by
  sig_post [simpleBitPackContract, simpleBitPackSig, PPC64LE.abi, PPC64LE.argRegs] at hp
  exact hp

theorem sbp_pub (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4)
    (h5 : x.gpr .r5 = y.gpr .r5) (h6 : x.gpr .r6 = y.gpr .r6) : (simpleBitPackContract PPC64LE.abi stk).pub x y := by
  sig_pub [simpleBitPackContract, simpleBitPackSig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨hsp, h3, congrArg _ h4, h5, h6⟩

theorem bp_pre (g3 : x.gpr .r3 = f) (g4 : (x.gpr .r4).setWidth 32 = a) (g5 : (x.gpr .r5).setWidth 32 = b)
    (g6 : x.gpr .r6 = o) (g7 : x.gpr .r7 = l)
    (hrd : x.rd = [reg f 1024]) (hwr : x.wr = [reg o l.toNat]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (reg f 1024).Disjoint (reg o l.toNat))
    (k1 : (below x.sp stk).Disjoint (reg f 1024)) (k2 : (below x.sp stk).Disjoint (reg o l.toNat))
    (f1 : f.toNat + 1024 ≤ 2 ^ 64) (f2 : o.toNat + l.toNat ≤ 2 ^ 64) (hab : (a.toNat, b.toNat) ∈ bitPackParams)
    (hl : l.toNat = 32 * bitlen (a.toNat + b.toNat)) (hr : Reduced x.mem f)
    (hc : ∀ i < n, -(a.toNat : Int) ≤ modPm (coeffAt x.mem f i).toNat q ∧
      modPm (coeffAt x.mem f i).toNat q ≤ b.toNat) :
    (bitPackContract PPC64LE.abi stk).pre x := by
  sig_pre [bitPackContract, bitPackSig, PPC64LE.abi, PPC64LE.argRegs]
  simp only [g3, g4, g5, g6, g7]
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | omega | skip)
    | omega
    | skip
  all_goals assumption

theorem bp_post (hp : (bitPackContract PPC64LE.abi stk).post x y) :
    bytesAt y.mem (x.gpr .r6) (x.gpr .r7).toNat =
      bitPack ((polyAt x.mem (x.gpr .r3)).map fun c => modPm c.val q) ((x.gpr .r4).setWidth 32).toNat
        ((x.gpr .r5).setWidth 32).toNat := by
  sig_post [bitPackContract, bitPackSig, PPC64LE.abi, PPC64LE.argRegs] at hp
  exact hp

theorem bp_pub (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4)
    (h5 : x.gpr .r5 = y.gpr .r5) (h6 : x.gpr .r6 = y.gpr .r6) (h7 : x.gpr .r7 = y.gpr .r7) :
    (bitPackContract PPC64LE.abi stk).pub x y := by
  sig_pub [bitPackContract, bitPackSig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨hsp, h3, congrArg _ h4, congrArg _ h5, h6, h7⟩

end

end VG.Proof.MlDsa.PPC64LE.KeyGen
