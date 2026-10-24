module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Contracts
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on PPC64LE: the contracts of the primitives only signing calls, evaluated

As `Contracts.lean`, for `vg_mldsa_expand_mask_poly`, `vg_mldsa_high_bits`,
`vg_mldsa_low_bits`, `vg_mldsa_make_hint` and `vg_mldsa_hint_bit_pack`. A
`usize` argument is its whole register, and a `u32` argument or result the
low word of its register.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.KeyGen

open VG VG.PPC64LE
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `vg_mldsa_expand_mask_poly` -/

section
variable {stk : Nat} {x y : State} {sd a w : Addr} {g1 : BitVec 32}

theorem em_pre (g3 : x.gpr .r3 = sd) (g4 : (x.gpr .r4).setWidth 32 = g1) (g5 : x.gpr .r5 = a) (g6 : x.gpr .r6 = w)
    (hrd : x.rd = [reg sd 66]) (hwr : x.wr = [reg a 1024, reg w 2048]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (reg sd 66).Disjoint (reg a 1024)) (d2 : (reg sd 66).Disjoint (reg w 2048))
    (d3 : (reg a 1024).Disjoint (reg w 2048))
    (k1 : (below x.sp stk).Disjoint (reg sd 66)) (k2 : (below x.sp stk).Disjoint (reg a 1024))
    (k3 : (below x.sp stk).Disjoint (reg w 2048)) (f1 : sd.toNat + 66 ≤ 2 ^ 64) (f2 : a.toNat + 1024 ≤ 2 ^ 64)
    (f3 : w.toNat + 2048 ≤ 2 ^ 64) (hg : g1.toNat = 2 ^ 17 ∨ g1.toNat = 2 ^ 19) :
    (expandMaskContract PPC64LE.abi stk).pre x := by
  sig_pre [expandMaskContract, expandMaskSig, PPC64LE.abi, PPC64LE.argRegs]
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

theorem em_post (hp : (expandMaskContract PPC64LE.abi stk).post x y) :
    PolyIs y.mem (x.gpr .r5) (toRq (bitUnpack (H (bytesAt x.mem (x.gpr .r3) 66)
      (32 * (1 + bitlen (((x.gpr .r4).setWidth 32).toNat - 1)))) (((x.gpr .r4).setWidth 32).toNat - 1)
      ((x.gpr .r4).setWidth 32).toNat)) := by
  sig_post [expandMaskContract, expandMaskSig, PPC64LE.abi, PPC64LE.argRegs] at hp
  exact hp

theorem em_pub (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4)
    (h5 : x.gpr .r5 = y.gpr .r5) (h6 : x.gpr .r6 = y.gpr .r6) : (expandMaskContract PPC64LE.abi stk).pub x y := by
  sig_pub [expandMaskContract, expandMaskSig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨hsp, h3, congrArg _ h4, h5, h6⟩

end

/-! ## `vg_mldsa_high_bits`, `vg_mldsa_low_bits` -/

section
variable {stk : Nat} {x y : State} {r o : Addr} {g2 : BitVec 32}

theorem hb_pre (g3 : x.gpr .r3 = r) (g4 : (x.gpr .r4).setWidth 32 = g2) (g5 : x.gpr .r5 = o)
    (hrd : x.rd = [reg r 1024]) (hwr : x.wr = [reg o 1024]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (reg r 1024).Disjoint (reg o 1024))
    (k1 : (below x.sp stk).Disjoint (reg r 1024)) (k2 : (below x.sp stk).Disjoint (reg o 1024))
    (f1 : r.toNat + 1024 ≤ 2 ^ 64) (f2 : o.toNat + 1024 ≤ 2 ^ 64) (hg : g2.toNat ∈ gamma2s) (hr : Reduced x.mem r) :
    (highBitsContract PPC64LE.abi stk).pre x := by
  sig_pre [highBitsContract, bitsSig, PPC64LE.abi, PPC64LE.argRegs]
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

theorem hb_post (hp : (highBitsContract PPC64LE.abi stk).post x y) :
    NatPolyIs y.mem (x.gpr .r5)
      ((polyAt x.mem (x.gpr .r3)).map fun c => (highBits ((x.gpr .r4).setWidth 32).toNat c).toNat) := by
  sig_post [highBitsContract, bitsSig, PPC64LE.abi, PPC64LE.argRegs] at hp
  exact hp

theorem hb_pub (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4)
    (h5 : x.gpr .r5 = y.gpr .r5) : (highBitsContract PPC64LE.abi stk).pub x y := by
  sig_pub [highBitsContract, bitsSig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨hsp, h3, congrArg _ h4, h5⟩

theorem lb_pre (g3 : x.gpr .r3 = r) (g4 : (x.gpr .r4).setWidth 32 = g2) (g5 : x.gpr .r5 = o)
    (hrd : x.rd = [reg r 1024]) (hwr : x.wr = [reg o 1024]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (reg r 1024).Disjoint (reg o 1024))
    (k1 : (below x.sp stk).Disjoint (reg r 1024)) (k2 : (below x.sp stk).Disjoint (reg o 1024))
    (f1 : r.toNat + 1024 ≤ 2 ^ 64) (f2 : o.toNat + 1024 ≤ 2 ^ 64) (hg : g2.toNat ∈ gamma2s) (hr : Reduced x.mem r) :
    (lowBitsContract PPC64LE.abi stk).pre x := by
  sig_pre [lowBitsContract, bitsSig, PPC64LE.abi, PPC64LE.argRegs]
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

theorem lb_post (hp : (lowBitsContract PPC64LE.abi stk).post x y) :
    PolyIs y.mem (x.gpr .r5)
      ((polyAt x.mem (x.gpr .r3)).map fun c => ofInt (lowBits ((x.gpr .r4).setWidth 32).toNat c)) := by
  sig_post [lowBitsContract, bitsSig, PPC64LE.abi, PPC64LE.argRegs] at hp
  exact hp

theorem lb_pub (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4)
    (h5 : x.gpr .r5 = y.gpr .r5) : (lowBitsContract PPC64LE.abi stk).pub x y := by
  sig_pub [lowBitsContract, bitsSig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨hsp, h3, congrArg _ h4, h5⟩

end

/-! ## `vg_mldsa_make_hint` -/

section
variable {stk : Nat} {x y : State} {z r h : Addr} {g2 : BitVec 32}

theorem mh_pre (g3 : x.gpr .r3 = z) (g4 : x.gpr .r4 = r) (gg : (x.gpr .r5).setWidth 32 = g2) (g6 : x.gpr .r6 = h)
    (hrd : x.rd = [reg z 1024, reg r 1024]) (hwr : x.wr = [reg h 1024]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (reg z 1024).Disjoint (reg h 1024)) (d2 : (reg r 1024).Disjoint (reg h 1024))
    (k1 : (below x.sp stk).Disjoint (reg z 1024)) (k2 : (below x.sp stk).Disjoint (reg r 1024))
    (k3 : (below x.sp stk).Disjoint (reg h 1024)) (f1 : z.toNat + 1024 ≤ 2 ^ 64) (f2 : r.toNat + 1024 ≤ 2 ^ 64)
    (f3 : h.toNat + 1024 ≤ 2 ^ 64) (hg : g2.toNat ∈ gamma2s) (hz : Reduced x.mem z) (hr : Reduced x.mem r) :
    (makeHintContract PPC64LE.abi stk).pre x := by
  sig_pre [makeHintContract, makeHintSig, PPC64LE.abi, PPC64LE.argRegs]
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

theorem mh_post (hp : (makeHintContract PPC64LE.abi stk).post x y) :
    HintIs y.mem (x.gpr .r6) 1 [Vector.zipWith (makeHint ((x.gpr .r5).setWidth 32).toNat) (polyAt x.mem (x.gpr .r3))
      (polyAt x.mem (x.gpr .r4))] ∧
    ((y.gpr .r3).setWidth 32).toNat = hintOnes [Vector.zipWith (makeHint ((x.gpr .r5).setWidth 32).toNat)
      (polyAt x.mem (x.gpr .r3)) (polyAt x.mem (x.gpr .r4))] := by
  sig_post [makeHintContract, makeHintSig, PPC64LE.abi, PPC64LE.argRegs] at hp
  exact hp

theorem mh_pub (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4)
    (h5 : x.gpr .r5 = y.gpr .r5) (h6 : x.gpr .r6 = y.gpr .r6) : (makeHintContract PPC64LE.abi stk).pub x y := by
  sig_pub [makeHintContract, makeHintSig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨hsp, h3, h4, congrArg _ h5, h6⟩

end

/-! ## `vg_mldsa_hint_bit_pack` -/

section
variable {stk : Nat} {x y : State} {h o hl len : Addr} {om : BitVec 32}

theorem hbp_pre (g3 : x.gpr .r3 = h) (g4 : x.gpr .r4 = hl) (g5 : (x.gpr .r5).setWidth 32 = om) (g6 : x.gpr .r6 = o)
    (g7 : x.gpr .r7 = len)
    (hrd : x.rd = [reg h (hl.toNat * 4)]) (hwr : x.wr = [reg o len.toNat]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (reg h (hl.toNat * 4)).Disjoint (reg o len.toNat))
    (k1 : (below x.sp stk).Disjoint (reg h (hl.toNat * 4))) (k2 : (below x.sp stk).Disjoint (reg o len.toNat))
    (f1 : h.toNat + hl.toNat * 4 ≤ 2 ^ 64) (f2 : o.toNat + len.toNat ≤ 2 ^ 64)
    (hp : (om.toNat, len.toNat - om.toNat) ∈ hintParams) (ho : om.toNat ≤ len.toNat)
    (hh : hl.toNat = 256 * (len.toNat - om.toNat))
    (hc : hintOnes (hintAt x.mem h (len.toNat - om.toNat)) ≤ om.toNat) :
    (hintBitPackContract PPC64LE.abi stk).pre x := by
  sig_pre [hintBitPackContract, hintBitPackSig, PPC64LE.abi, PPC64LE.argRegs]
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

theorem hbp_post (hp : (hintBitPackContract PPC64LE.abi stk).post x y) :
    bytesAt y.mem (x.gpr .r6) (x.gpr .r7).toNat =
      hintBitPack ((x.gpr .r5).setWidth 32).toNat ((x.gpr .r7).toNat - ((x.gpr .r5).setWidth 32).toNat)
        (hintAt x.mem (x.gpr .r3) ((x.gpr .r7).toNat - ((x.gpr .r5).setWidth 32).toNat)) := by
  sig_post [hintBitPackContract, hintBitPackSig, PPC64LE.abi, PPC64LE.argRegs] at hp
  exact hp

theorem hbp_pub (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4)
    (h5 : x.gpr .r5 = y.gpr .r5) (h6 : x.gpr .r6 = y.gpr .r6) (h7 : x.gpr .r7 = y.gpr .r7)
    (hl : (List.range (x.gpr .r4).toNat).map (fun i => (coeffAt x.mem (x.gpr .r3) i).toNat) =
      (List.range (y.gpr .r4).toNat).map (fun i => (coeffAt y.mem (y.gpr .r3) i).toNat)) :
    (hintBitPackContract PPC64LE.abi stk).pub x y := by
  sig_pub [hintBitPackContract, hintBitPackSig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨hsp, hl, h3, h4, congrArg _ h5, h6, h7⟩

end

end VG.Proof.MlDsa.PPC64LE.KeyGen
