module

public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.MlDsa.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on RISC-V: the contracts of the primitives, evaluated

As on PPC64LE (`Proof/MlDsa/PPC64LE/KeyGen/Contracts.lean`): for each
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

namespace VG.Proof.MlDsa.RISCV64.KeyGen

open VG VG.RISCV64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- `l` bytes at `a`. -/
abbrev reg (a : Addr) (l : Nat) : Region := ⟨a, l⟩

/-! ## `vg_mldsa_ntt`, `vg_mldsa_inv_ntt` -/

section
variable {stk : Nat} {x y : State}

theorem ip_pre {t : Poly → Poly} {f w : Addr} (g3 : x.gpr .a0 = f) (g4 : x.gpr .a1 = w)
    (hrd : x.rd = []) (hwr : x.wr = [reg f 1024, reg w 1024]) (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0)
    (al_f : f.toNat % 4 = 0) (al_w : w.toNat % 8 = 0)
    (hd : (reg f 1024).Disjoint (reg w 1024)) (kf : (below x.sp stk).Disjoint (reg f 1024))
    (kw : (below x.sp stk).Disjoint (reg w 1024)) (ff : f.toNat + 1024 ≤ 2 ^ 64) (fw : w.toNat + 1024 ≤ 2 ^ 64)
    (hr : Reduced x.mem f) :
    (inPlaceContract RISCV64.abi t stk).pre x := by
  sig_pre [inPlaceContract, inPlaceSig, RISCV64.abi, RISCV64.argRegs]
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

theorem ip_post {t : Poly → Poly} (h : (inPlaceContract RISCV64.abi t stk).post x y) :
    PolyIs y.mem (x.gpr .a0) (t (polyAt x.mem (x.gpr .a0))) := by
  sig_post [inPlaceContract, inPlaceSig, RISCV64.abi, RISCV64.argRegs] at h
  exact h

theorem ip_pub {t : Poly → Poly} (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1) :
    (inPlaceContract RISCV64.abi t stk).pub x y := by
  sig_pub [inPlaceContract, inPlaceSig, RISCV64.abi, RISCV64.argRegs]
  exact ⟨hsp, h3, h4⟩

end

/-! ## `vg_mldsa_multiply_ntt`, `vg_mldsa_multiply_add_ntt` -/

section
variable {stk : Nat} {x y : State} {h f g : Addr}

theorem mul_pre (g3 : x.gpr .a0 = h) (g4 : x.gpr .a1 = f) (g5 : x.gpr .a2 = g)
    (hrd : x.rd = [reg f 1024, reg g 1024]) (hwr : x.wr = [reg h 1024]) (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0)
    (al_h : h.toNat % 4 = 0) (al_f : f.toNat % 4 = 0) (al_g : g.toNat % 4 = 0)
    (d1 : (reg h 1024).Disjoint (reg f 1024)) (d2 : (reg h 1024).Disjoint (reg g 1024))
    (kh : (below x.sp stk).Disjoint (reg h 1024)) (kf : (below x.sp stk).Disjoint (reg f 1024))
    (kg : (below x.sp stk).Disjoint (reg g 1024)) (fh : h.toNat + 1024 ≤ 2 ^ 64) (ff : f.toNat + 1024 ≤ 2 ^ 64)
    (fg : g.toNat + 1024 ≤ 2 ^ 64) (rf : Reduced x.mem f) (rg : Reduced x.mem g) :
    (mulContract RISCV64.abi stk).pre x := by
  sig_pre [mulContract, mulSig, RISCV64.abi, RISCV64.argRegs]
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

theorem mul_post (hp : (mulContract RISCV64.abi stk).post x y) :
    PolyIs y.mem (x.gpr .a0) (multiplyNTT (polyAt x.mem (x.gpr .a1)) (polyAt x.mem (x.gpr .a2))) := by
  sig_post [mulContract, mulSig, RISCV64.abi, RISCV64.argRegs] at hp
  exact hp

theorem mulAdd_pre (g3 : x.gpr .a0 = h) (g4 : x.gpr .a1 = f) (g5 : x.gpr .a2 = g)
    (hrd : x.rd = [reg f 1024, reg g 1024]) (hwr : x.wr = [reg h 1024]) (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0)
    (al_h : h.toNat % 4 = 0) (al_f : f.toNat % 4 = 0) (al_g : g.toNat % 4 = 0)
    (d1 : (reg h 1024).Disjoint (reg f 1024)) (d2 : (reg h 1024).Disjoint (reg g 1024))
    (kh : (below x.sp stk).Disjoint (reg h 1024)) (kf : (below x.sp stk).Disjoint (reg f 1024))
    (kg : (below x.sp stk).Disjoint (reg g 1024)) (fh : h.toNat + 1024 ≤ 2 ^ 64) (ff : f.toNat + 1024 ≤ 2 ^ 64)
    (fg : g.toNat + 1024 ≤ 2 ^ 64) (rh : Reduced x.mem h) (rf : Reduced x.mem f) (rg : Reduced x.mem g) :
    (mulAddContract RISCV64.abi stk).pre x := by
  sig_pre [mulAddContract, mulSig, RISCV64.abi, RISCV64.argRegs]
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

theorem mulAdd_post (hp : (mulAddContract RISCV64.abi stk).post x y) :
    PolyIs y.mem (x.gpr .a0) (add (polyAt x.mem (x.gpr .a0))
      (multiplyNTT (polyAt x.mem (x.gpr .a1)) (polyAt x.mem (x.gpr .a2)))) := by
  sig_post [mulAddContract, mulSig, RISCV64.abi, RISCV64.argRegs] at hp
  exact hp

theorem mul_pub (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1)
    (h5 : x.gpr .a2 = y.gpr .a2) : (mulContract RISCV64.abi stk).pub x y := by
  sig_pub [mulContract, mulSig, RISCV64.abi, RISCV64.argRegs]
  exact ⟨hsp, h3, h4, h5⟩

theorem mulAdd_pub (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1)
    (h5 : x.gpr .a2 = y.gpr .a2) : (mulAddContract RISCV64.abi stk).pub x y := by
  sig_pub [mulAddContract, mulSig, RISCV64.abi, RISCV64.argRegs]
  exact ⟨hsp, h3, h4, h5⟩

end

/-! ## `vg_mldsa_add` -/

section
variable {stk : Nat} {x y : State} {f g : Addr}

theorem add_pre (g3 : x.gpr .a0 = f) (g4 : x.gpr .a1 = g) (hrd : x.rd = [reg g 1024])
    (hwr : x.wr = [reg f 1024]) (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0)
    (al_f : f.toNat % 4 = 0) (al_g : g.toNat % 4 = 0) (d1 : (reg f 1024).Disjoint (reg g 1024))
    (kf : (below x.sp stk).Disjoint (reg f 1024)) (kg : (below x.sp stk).Disjoint (reg g 1024))
    (ff : f.toNat + 1024 ≤ 2 ^ 64) (fg : g.toNat + 1024 ≤ 2 ^ 64) (rf : Reduced x.mem f)
    (rg : Reduced x.mem g) : (addContract RISCV64.abi stk).pre x := by
  sig_pre [addContract, accSig, RISCV64.abi, RISCV64.argRegs]
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

theorem add_post (hp : (addContract RISCV64.abi stk).post x y) :
    PolyIs y.mem (x.gpr .a0) (add (polyAt x.mem (x.gpr .a0)) (polyAt x.mem (x.gpr .a1))) := by
  sig_post [addContract, accSig, RISCV64.abi, RISCV64.argRegs] at hp
  exact hp

theorem add_pub (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1) :
    (addContract RISCV64.abi stk).pub x y := by
  sig_pub [addContract, accSig, RISCV64.abi, RISCV64.argRegs]
  exact ⟨hsp, h3, h4⟩

end

/-! ## `vg_mldsa_rej_ntt_poly`, `vg_mldsa_rej_bounded_poly` -/

section
variable {stk : Nat} {x y : State} {sd a w : Addr}

theorem rejNtt_pre (g3 : x.gpr .a0 = sd) (g4 : x.gpr .a1 = a) (g5 : x.gpr .a2 = w)
    (hrd : x.rd = [reg sd 34]) (hwr : x.wr = [reg a 1024, reg w 2048]) (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0)
    (al_a : a.toNat % 4 = 0) (al_w : w.toNat % 8 = 0)
    (d1 : (reg sd 34).Disjoint (reg a 1024)) (d2 : (reg sd 34).Disjoint (reg w 2048))
    (d3 : (reg a 1024).Disjoint (reg w 2048))
    (k1 : (below x.sp stk).Disjoint (reg sd 34)) (k2 : (below x.sp stk).Disjoint (reg a 1024))
    (k3 : (below x.sp stk).Disjoint (reg w 2048)) (f1 : sd.toNat + 34 ≤ 2 ^ 64) (f2 : a.toNat + 1024 ≤ 2 ^ 64)
    (f3 : w.toNat + 2048 ≤ 2 ^ 64) : (rejNTTContract RISCV64.abi stk).pre x := by
  sig_pre [rejNTTContract, rejNTTSig, RISCV64.abi, RISCV64.argRegs]
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

theorem rejNtt_post (hp : (rejNTTContract RISCV64.abi stk).post x y) :
    ((y.gpr .a0).setWidth 32 = 1 → Reduced y.mem (x.gpr .a1)) ∧
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt x.mem (x.gpr .a0) 34)) ((y.gpr .a0).setWidth 32)
        (polyAt y.mem (x.gpr .a1)) := by
  sig_post [rejNTTContract, rejNTTSig, RISCV64.abi, RISCV64.argRegs] at hp
  exact hp

theorem rejNtt_pub (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1)
    (h5 : x.gpr .a2 = y.gpr .a2) (hl : bytesAt x.mem (x.gpr .a0) 34 = bytesAt y.mem (y.gpr .a0) 34) :
    (rejNTTContract RISCV64.abi stk).pub x y := by
  sig_pub [rejNTTContract, rejNTTSig, RISCV64.abi, RISCV64.argRegs]
  exact ⟨hsp, congrArg leakBytes hl, h3, h4, h5⟩

end

section
variable {stk : Nat} {x y : State} {sd a w : Addr} {e : BitVec 32}

theorem rejBounded_pre (g3 : x.gpr .a0 = sd) (g4 : (x.gpr .a1).setWidth 32 = e) (g5 : x.gpr .a2 = a)
    (g6 : x.gpr .a3 = w)
    (hrd : x.rd = [reg sd 66]) (hwr : x.wr = [reg a 1024, reg w 2048]) (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0)
    (al_a : a.toNat % 4 = 0) (al_w : w.toNat % 8 = 0)
    (d1 : (reg sd 66).Disjoint (reg a 1024)) (d2 : (reg sd 66).Disjoint (reg w 2048))
    (d3 : (reg a 1024).Disjoint (reg w 2048))
    (k1 : (below x.sp stk).Disjoint (reg sd 66)) (k2 : (below x.sp stk).Disjoint (reg a 1024))
    (k3 : (below x.sp stk).Disjoint (reg w 2048)) (f1 : sd.toNat + 66 ≤ 2 ^ 64) (f2 : a.toNat + 1024 ≤ 2 ^ 64)
    (f3 : w.toNat + 2048 ≤ 2 ^ 64) (he : e.toNat = 2 ∨ e.toNat = 4) :
    (rejBoundedContract RISCV64.abi stk).pre x := by
  sig_pre [rejBoundedContract, rejBoundedSig, RISCV64.abi, RISCV64.argRegs]
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

theorem rejBounded_post (hp : (rejBoundedContract RISCV64.abi stk).post x y) :
    ((y.gpr .a0).setWidth 32 = 1 → Reduced y.mem (x.gpr .a2)) ∧
      Outcome (fun b => (rejBoundedPoly ((x.gpr .a1).setWidth 32).toNat b.rejBounded (bytesAt x.mem (x.gpr .a0) 66)).map
        toRq) ((y.gpr .a0).setWidth 32) (polyAt y.mem (x.gpr .a2)) := by
  sig_post [rejBoundedContract, rejBoundedSig, RISCV64.abi, RISCV64.argRegs] at hp
  exact hp

theorem rejBounded_pub (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1)
    (h5 : x.gpr .a2 = y.gpr .a2) (h6 : x.gpr .a3 = y.gpr .a3)
    (hl : rejBoundedLeak ((x.gpr .a1).setWidth 32).toNat (bytesAt x.mem (x.gpr .a0) 66) =
      rejBoundedLeak ((y.gpr .a1).setWidth 32).toNat (bytesAt y.mem (y.gpr .a0) 66)) :
    (rejBoundedContract RISCV64.abi stk).pub x y := by
  sig_pub [rejBoundedContract, rejBoundedSig, RISCV64.abi, RISCV64.argRegs]
  exact ⟨hsp, hl, h3, congrArg _ h4, h5, h6⟩

end

/-! ## `vg_mldsa_power2round` -/

section
variable {stk : Nat} {x y : State} {t t1 t0 : Addr}

theorem p2r_pre (g3 : x.gpr .a0 = t) (g4 : x.gpr .a1 = t1) (g5 : x.gpr .a2 = t0)
    (hrd : x.rd = [reg t 1024]) (hwr : x.wr = [reg t1 1024, reg t0 1024]) (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0)
    (al_t : t.toNat % 4 = 0) (al_t1 : t1.toNat % 4 = 0) (al_t0 : t0.toNat % 4 = 0)
    (d1 : (reg t 1024).Disjoint (reg t1 1024)) (d2 : (reg t 1024).Disjoint (reg t0 1024))
    (d3 : (reg t1 1024).Disjoint (reg t0 1024))
    (k1 : (below x.sp stk).Disjoint (reg t 1024)) (k2 : (below x.sp stk).Disjoint (reg t1 1024))
    (k3 : (below x.sp stk).Disjoint (reg t0 1024)) (f1 : t.toNat + 1024 ≤ 2 ^ 64) (f2 : t1.toNat + 1024 ≤ 2 ^ 64)
    (f3 : t0.toNat + 1024 ≤ 2 ^ 64) (hr : Reduced x.mem t) : (power2RoundContract RISCV64.abi stk).pre x := by
  sig_pre [power2RoundContract, power2RoundSig, RISCV64.abi, RISCV64.argRegs]
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

theorem p2r_post (hp : (power2RoundContract RISCV64.abi stk).post x y) :
    NatPolyIs y.mem (x.gpr .a1) ((polyAt x.mem (x.gpr .a0)).map fun c => (power2Round c).1.toNat) ∧
      PolyIs y.mem (x.gpr .a2) ((polyAt x.mem (x.gpr .a0)).map fun c => ofInt (power2Round c).2) := by
  sig_post [power2RoundContract, power2RoundSig, RISCV64.abi, RISCV64.argRegs] at hp
  exact hp

theorem p2r_pub (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1)
    (h5 : x.gpr .a2 = y.gpr .a2) : (power2RoundContract RISCV64.abi stk).pub x y := by
  sig_pub [power2RoundContract, power2RoundSig, RISCV64.abi, RISCV64.argRegs]
  exact ⟨hsp, h3, h4, h5⟩

end

/-! ## `vg_mldsa_simple_bit_pack`, `vg_mldsa_bit_pack` -/

section
variable {stk : Nat} {x y : State} {f o : Addr} {a b : BitVec 32} {l : BitVec 64}

theorem sbp_pre (g3 : x.gpr .a0 = f) (g4 : (x.gpr .a1).setWidth 32 = b) (g5 : x.gpr .a2 = o) (g6 : x.gpr .a3 = l)
    (hrd : x.rd = [reg f 1024]) (hwr : x.wr = [reg o l.toNat]) (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0)
    (al_f : f.toNat % 4 = 0)
    (d1 : (reg f 1024).Disjoint (reg o l.toNat))
    (k1 : (below x.sp stk).Disjoint (reg f 1024)) (k2 : (below x.sp stk).Disjoint (reg o l.toNat))
    (f1 : f.toNat + 1024 ≤ 2 ^ 64) (f2 : o.toNat + l.toNat ≤ 2 ^ 64) (hb : b.toNat ∈ simpleBitPackBounds)
    (hl : l.toNat = 32 * bitlen b.toNat) (hc : ∀ i < n, (coeffAt x.mem f i).toNat ≤ b.toNat) :
    (simpleBitPackContract RISCV64.abi stk).pre x := by
  sig_pre [simpleBitPackContract, simpleBitPackSig, RISCV64.abi, RISCV64.argRegs]
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

theorem sbp_post (hp : (simpleBitPackContract RISCV64.abi stk).post x y) :
    bytesAt y.mem (x.gpr .a2) (x.gpr .a3).toNat =
      simpleBitPack (natPolyAt x.mem (x.gpr .a0)) ((x.gpr .a1).setWidth 32).toNat := by
  sig_post [simpleBitPackContract, simpleBitPackSig, RISCV64.abi, RISCV64.argRegs] at hp
  exact hp

theorem sbp_pub (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1)
    (h5 : x.gpr .a2 = y.gpr .a2) (h6 : x.gpr .a3 = y.gpr .a3) : (simpleBitPackContract RISCV64.abi stk).pub x y := by
  sig_pub [simpleBitPackContract, simpleBitPackSig, RISCV64.abi, RISCV64.argRegs]
  exact ⟨hsp, h3, congrArg _ h4, h5, h6⟩

theorem bp_pre (g3 : x.gpr .a0 = f) (g4 : (x.gpr .a1).setWidth 32 = a) (g5 : (x.gpr .a2).setWidth 32 = b)
    (g6 : x.gpr .a3 = o) (g7 : x.gpr .a4 = l)
    (hrd : x.rd = [reg f 1024]) (hwr : x.wr = [reg o l.toNat]) (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0)
    (al_f : f.toNat % 4 = 0)
    (d1 : (reg f 1024).Disjoint (reg o l.toNat))
    (k1 : (below x.sp stk).Disjoint (reg f 1024)) (k2 : (below x.sp stk).Disjoint (reg o l.toNat))
    (f1 : f.toNat + 1024 ≤ 2 ^ 64) (f2 : o.toNat + l.toNat ≤ 2 ^ 64) (hab : (a.toNat, b.toNat) ∈ bitPackParams)
    (hl : l.toNat = 32 * bitlen (a.toNat + b.toNat)) (hr : Reduced x.mem f)
    (hc : ∀ i < n, -(a.toNat : Int) ≤ modPm (coeffAt x.mem f i).toNat q ∧
      modPm (coeffAt x.mem f i).toNat q ≤ b.toNat) :
    (bitPackContract RISCV64.abi stk).pre x := by
  sig_pre [bitPackContract, bitPackSig, RISCV64.abi, RISCV64.argRegs]
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

theorem bp_post (hp : (bitPackContract RISCV64.abi stk).post x y) :
    bytesAt y.mem (x.gpr .a3) (x.gpr .a4).toNat =
      bitPack ((polyAt x.mem (x.gpr .a0)).map fun c => modPm c.val q) ((x.gpr .a1).setWidth 32).toNat
        ((x.gpr .a2).setWidth 32).toNat := by
  sig_post [bitPackContract, bitPackSig, RISCV64.abi, RISCV64.argRegs] at hp
  exact hp

theorem bp_pub (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1)
    (h5 : x.gpr .a2 = y.gpr .a2) (h6 : x.gpr .a3 = y.gpr .a3) (h7 : x.gpr .a4 = y.gpr .a4) :
    (bitPackContract RISCV64.abi stk).pub x y := by
  sig_pub [bitPackContract, bitPackSig, RISCV64.abi, RISCV64.argRegs]
  exact ⟨hsp, h3, congrArg _ h4, congrArg _ h5, h6, h7⟩

end

end VG.Proof.MlDsa.RISCV64.KeyGen
