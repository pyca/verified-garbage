module
-- separate module: the contracts of signing's primitives, built in parallel with `CallSP` and `CallV`, which `CallS` also imports, as on PPC64LE

public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Contracts
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on RISC-V: the contracts of the primitives only signing calls, evaluated

As `Contracts.lean`, for `vg_mldsa_expand_mask_poly`, `vg_mldsa_high_bits`,
`vg_mldsa_low_bits`, `vg_mldsa_make_hint` and `vg_mldsa_hint_bit_pack`. A
`usize` argument is its whole register, and a `u32` argument or result the
low word of its register.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.KeyGen

open VG VG.RISCV64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `vg_mldsa_expand_mask_poly` -/

section
variable {stk : Nat} {x y : State} {sd a w : Addr} {g1 : BitVec 32}

theorem em_pre (g3 : x.gpr .a0 = sd) (g4 : (x.gpr .a1).setWidth 32 = g1) (g5 : x.gpr .a2 = a) (g6 : x.gpr .a3 = w)
    (hrd : x.rd = [reg sd 66]) (hwr : x.wr = [reg a 1024, reg w 2048]) (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0)
    (al_a : a.toNat % 4 = 0) (al_w : w.toNat % 8 = 0)
    (d1 : (reg sd 66).Disjoint (reg a 1024)) (d2 : (reg sd 66).Disjoint (reg w 2048))
    (d3 : (reg a 1024).Disjoint (reg w 2048))
    (k1 : (below x.sp stk).Disjoint (reg sd 66)) (k2 : (below x.sp stk).Disjoint (reg a 1024))
    (k3 : (below x.sp stk).Disjoint (reg w 2048)) (f1 : sd.toNat + 66 ≤ 2 ^ 64) (f2 : a.toNat + 1024 ≤ 2 ^ 64)
    (f3 : w.toNat + 2048 ≤ 2 ^ 64) (hg : g1.toNat = 2 ^ 17 ∨ g1.toNat = 2 ^ 19) :
    (expandMaskContract RISCV64.abi stk).pre x := by
  sig_pre [expandMaskContract, expandMaskSig, RISCV64.abi, RISCV64.argRegs]
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

theorem em_post (hp : (expandMaskContract RISCV64.abi stk).post x y) :
    PolyIs y.mem (x.gpr .a2) (toRq (bitUnpack (H (bytesAt x.mem (x.gpr .a0) 66)
      (32 * (1 + bitlen (((x.gpr .a1).setWidth 32).toNat - 1)))) (((x.gpr .a1).setWidth 32).toNat - 1)
      ((x.gpr .a1).setWidth 32).toNat)) := by
  sig_post [expandMaskContract, expandMaskSig, RISCV64.abi, RISCV64.argRegs] at hp
  exact hp

theorem em_pub (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1)
    (h5 : x.gpr .a2 = y.gpr .a2) (h6 : x.gpr .a3 = y.gpr .a3) : (expandMaskContract RISCV64.abi stk).pub x y := by
  sig_pub [expandMaskContract, expandMaskSig, RISCV64.abi, RISCV64.argRegs]
  exact ⟨hsp, h3, congrArg _ h4, h5, h6⟩

end

/-! ## `vg_mldsa_high_bits`, `vg_mldsa_low_bits` -/

section
variable {stk : Nat} {x y : State} {r o : Addr} {g2 : BitVec 32}

theorem hb_pre (g3 : x.gpr .a0 = r) (g4 : (x.gpr .a1).setWidth 32 = g2) (g5 : x.gpr .a2 = o)
    (hrd : x.rd = [reg r 1024]) (hwr : x.wr = [reg o 1024]) (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0)
    (al_r : r.toNat % 4 = 0) (al_o : o.toNat % 4 = 0)
    (d1 : (reg r 1024).Disjoint (reg o 1024))
    (k1 : (below x.sp stk).Disjoint (reg r 1024)) (k2 : (below x.sp stk).Disjoint (reg o 1024))
    (f1 : r.toNat + 1024 ≤ 2 ^ 64) (f2 : o.toNat + 1024 ≤ 2 ^ 64) (hg : g2.toNat ∈ gamma2s) (hr : Reduced x.mem r) :
    (highBitsContract RISCV64.abi stk).pre x := by
  sig_pre [highBitsContract, bitsSig, RISCV64.abi, RISCV64.argRegs]
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

theorem hb_post (hp : (highBitsContract RISCV64.abi stk).post x y) :
    NatPolyIs y.mem (x.gpr .a2)
      ((polyAt x.mem (x.gpr .a0)).map fun c => (highBits ((x.gpr .a1).setWidth 32).toNat c).toNat) := by
  sig_post [highBitsContract, bitsSig, RISCV64.abi, RISCV64.argRegs] at hp
  exact hp

theorem hb_pub (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1)
    (h5 : x.gpr .a2 = y.gpr .a2) : (highBitsContract RISCV64.abi stk).pub x y := by
  sig_pub [highBitsContract, bitsSig, RISCV64.abi, RISCV64.argRegs]
  exact ⟨hsp, h3, congrArg _ h4, h5⟩

theorem lb_pre (g3 : x.gpr .a0 = r) (g4 : (x.gpr .a1).setWidth 32 = g2) (g5 : x.gpr .a2 = o)
    (hrd : x.rd = [reg r 1024]) (hwr : x.wr = [reg o 1024]) (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0)
    (al_r : r.toNat % 4 = 0) (al_o : o.toNat % 4 = 0)
    (d1 : (reg r 1024).Disjoint (reg o 1024))
    (k1 : (below x.sp stk).Disjoint (reg r 1024)) (k2 : (below x.sp stk).Disjoint (reg o 1024))
    (f1 : r.toNat + 1024 ≤ 2 ^ 64) (f2 : o.toNat + 1024 ≤ 2 ^ 64) (hg : g2.toNat ∈ gamma2s) (hr : Reduced x.mem r) :
    (lowBitsContract RISCV64.abi stk).pre x := by
  sig_pre [lowBitsContract, bitsSig, RISCV64.abi, RISCV64.argRegs]
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

theorem lb_post (hp : (lowBitsContract RISCV64.abi stk).post x y) :
    PolyIs y.mem (x.gpr .a2)
      ((polyAt x.mem (x.gpr .a0)).map fun c => ofInt (lowBits ((x.gpr .a1).setWidth 32).toNat c)) := by
  sig_post [lowBitsContract, bitsSig, RISCV64.abi, RISCV64.argRegs] at hp
  exact hp

theorem lb_pub (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1)
    (h5 : x.gpr .a2 = y.gpr .a2) : (lowBitsContract RISCV64.abi stk).pub x y := by
  sig_pub [lowBitsContract, bitsSig, RISCV64.abi, RISCV64.argRegs]
  exact ⟨hsp, h3, congrArg _ h4, h5⟩

end

/-! ## `vg_mldsa_make_hint` -/

section
variable {stk : Nat} {x y : State} {z r h : Addr} {g2 : BitVec 32}

theorem mh_pre (g3 : x.gpr .a0 = z) (g4 : x.gpr .a1 = r) (gg : (x.gpr .a2).setWidth 32 = g2) (g6 : x.gpr .a3 = h)
    (hrd : x.rd = [reg z 1024, reg r 1024]) (hwr : x.wr = [reg h 1024]) (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0)
    (al_z : z.toNat % 4 = 0) (al_r : r.toNat % 4 = 0) (al_h : h.toNat % 4 = 0)
    (d1 : (reg z 1024).Disjoint (reg h 1024)) (d2 : (reg r 1024).Disjoint (reg h 1024))
    (k1 : (below x.sp stk).Disjoint (reg z 1024)) (k2 : (below x.sp stk).Disjoint (reg r 1024))
    (k3 : (below x.sp stk).Disjoint (reg h 1024)) (f1 : z.toNat + 1024 ≤ 2 ^ 64) (f2 : r.toNat + 1024 ≤ 2 ^ 64)
    (f3 : h.toNat + 1024 ≤ 2 ^ 64) (hg : g2.toNat ∈ gamma2s) (hz : Reduced x.mem z) (hr : Reduced x.mem r) :
    (makeHintContract RISCV64.abi stk).pre x := by
  sig_pre [makeHintContract, makeHintSig, RISCV64.abi, RISCV64.argRegs]
  simp only [g3, g4, gg, g6]
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

theorem mh_post (hp : (makeHintContract RISCV64.abi stk).post x y) :
    HintIs y.mem (x.gpr .a3) 1 [Vector.zipWith (makeHint ((x.gpr .a2).setWidth 32).toNat) (polyAt x.mem (x.gpr .a0))
      (polyAt x.mem (x.gpr .a1))] ∧
    ((y.gpr .a0).setWidth 32).toNat = hintOnes [Vector.zipWith (makeHint ((x.gpr .a2).setWidth 32).toNat)
      (polyAt x.mem (x.gpr .a0)) (polyAt x.mem (x.gpr .a1))] := by
  sig_post [makeHintContract, makeHintSig, RISCV64.abi, RISCV64.argRegs] at hp
  exact hp

theorem mh_pub (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1)
    (h5 : x.gpr .a2 = y.gpr .a2) (h6 : x.gpr .a3 = y.gpr .a3) : (makeHintContract RISCV64.abi stk).pub x y := by
  sig_pub [makeHintContract, makeHintSig, RISCV64.abi, RISCV64.argRegs]
  exact ⟨hsp, h3, h4, congrArg _ h5, h6⟩

end

/-! ## `vg_mldsa_hint_bit_pack` -/

section
variable {stk : Nat} {x y : State} {h o hl len : Addr} {om : BitVec 32}

theorem hbp_pre (g3 : x.gpr .a0 = h) (g4 : x.gpr .a1 = hl) (g5 : (x.gpr .a2).setWidth 32 = om) (g6 : x.gpr .a3 = o)
    (g7 : x.gpr .a4 = len)
    (hrd : x.rd = [reg h (hl.toNat * 4)]) (hwr : x.wr = [reg o len.toNat]) (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0)
    (al_h : h.toNat % 4 = 0)
    (d1 : (reg h (hl.toNat * 4)).Disjoint (reg o len.toNat))
    (k1 : (below x.sp stk).Disjoint (reg h (hl.toNat * 4))) (k2 : (below x.sp stk).Disjoint (reg o len.toNat))
    (f1 : h.toNat + hl.toNat * 4 ≤ 2 ^ 64) (f2 : o.toNat + len.toNat ≤ 2 ^ 64)
    (hp : (om.toNat, len.toNat - om.toNat) ∈ hintParams) (ho : om.toNat ≤ len.toNat)
    (hh : hl.toNat = 256 * (len.toNat - om.toNat))
    (hc : hintOnes (hintAt x.mem h (len.toNat - om.toNat)) ≤ om.toNat) :
    (hintBitPackContract RISCV64.abi stk).pre x := by
  sig_pre [hintBitPackContract, hintBitPackSig, RISCV64.abi, RISCV64.argRegs]
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

theorem hbp_post (hp : (hintBitPackContract RISCV64.abi stk).post x y) :
    bytesAt y.mem (x.gpr .a3) (x.gpr .a4).toNat =
      hintBitPack ((x.gpr .a2).setWidth 32).toNat ((x.gpr .a4).toNat - ((x.gpr .a2).setWidth 32).toNat)
        (hintAt x.mem (x.gpr .a0) ((x.gpr .a4).toNat - ((x.gpr .a2).setWidth 32).toNat)) := by
  sig_post [hintBitPackContract, hintBitPackSig, RISCV64.abi, RISCV64.argRegs] at hp
  exact hp

theorem hbp_pub (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1)
    (h5 : x.gpr .a2 = y.gpr .a2) (h6 : x.gpr .a3 = y.gpr .a3) (h7 : x.gpr .a4 = y.gpr .a4)
    (hl : (List.range (x.gpr .a1).toNat).map (fun i => (coeffAt x.mem (x.gpr .a0) i).toNat) =
      (List.range (y.gpr .a1).toNat).map (fun i => (coeffAt y.mem (y.gpr .a0) i).toNat)) :
    (hintBitPackContract RISCV64.abi stk).pub x y := by
  sig_pub [hintBitPackContract, hintBitPackSig, RISCV64.abi, RISCV64.argRegs]
  exact ⟨hsp, hl, h3, h4, congrArg _ h5, h6, h7⟩

end

end VG.Proof.MlDsa.RISCV64.KeyGen
