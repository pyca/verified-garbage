module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Contracts
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on PPC64LE: the contracts of the primitives verification and signing call, evaluated

As `Contracts.lean`, for the primitives key generation does not call:
`vg_mldsa_sub`, `vg_mldsa_sample_in_ball`, `vg_mldsa_use_hint`,
`vg_mldsa_bit_unpack`, `vg_mldsa_unpack_t1`, `vg_mldsa_hint_bit_unpack` and
`vg_mldsa_norm_lt`. A `usize` argument is its whole register, and a `u32`
argument or result the low word of its register.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.KeyGen

open VG VG.PPC64LE
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `vg_mldsa_sub` -/

section
variable {stk : Nat} {x y : State} {f g : Addr}

theorem sub_pre (g3 : x.gpr .r3 = f) (g4 : x.gpr .r4 = g) (hrd : x.rd = [reg g 1024])
    (hwr : x.wr = [reg f 1024]) (hsp : stk ≤ x.sp.toNat) (d1 : (reg f 1024).Disjoint (reg g 1024))
    (kf : (below x.sp stk).Disjoint (reg f 1024)) (kg : (below x.sp stk).Disjoint (reg g 1024))
    (ff : f.toNat + 1024 ≤ 2 ^ 64) (fg : g.toNat + 1024 ≤ 2 ^ 64) (rf : Reduced x.mem f)
    (rg : Reduced x.mem g) : (subContract PPC64LE.abi stk).pre x := by
  sig_pre [subContract, accSig, PPC64LE.abi, PPC64LE.argRegs]
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

theorem sub_post (hp : (subContract PPC64LE.abi stk).post x y) :
    PolyIs y.mem (x.gpr .r3) (sub (polyAt x.mem (x.gpr .r3)) (polyAt x.mem (x.gpr .r4))) := by
  sig_post [subContract, accSig, PPC64LE.abi, PPC64LE.argRegs] at hp
  exact hp

theorem sub_pub (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4) :
    (subContract PPC64LE.abi stk).pub x y := by
  sig_pub [subContract, accSig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨hsp, h3, h4⟩

end

/-! ## `vg_mldsa_sample_in_ball` -/

section
variable {stk : Nat} {x y : State} {ct c w len : Addr} {tau : BitVec 32}

theorem ball_pre (g3 : x.gpr .r3 = ct) (g4 : x.gpr .r4 = len) (g5 : (x.gpr .r5).setWidth 32 = tau)
    (g6 : x.gpr .r6 = c) (g7 : x.gpr .r7 = w)
    (hrd : x.rd = [reg ct len.toNat]) (hwr : x.wr = [reg c 1024, reg w 2048]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (reg ct len.toNat).Disjoint (reg c 1024)) (d2 : (reg ct len.toNat).Disjoint (reg w 2048))
    (d3 : (reg c 1024).Disjoint (reg w 2048))
    (k1 : (below x.sp stk).Disjoint (reg ct len.toNat)) (k2 : (below x.sp stk).Disjoint (reg c 1024))
    (k3 : (below x.sp stk).Disjoint (reg w 2048))
    (f1 : ct.toNat + len.toNat ≤ 2 ^ 64) (f2 : c.toNat + 1024 ≤ 2 ^ 64) (f3 : w.toNat + 2048 ≤ 2 ^ 64)
    (hp : (len.toNat, tau.toNat) ∈ ballParams) : (sampleInBallContract PPC64LE.abi stk).pre x := by
  sig_pre [sampleInBallContract, sampleInBallSig, PPC64LE.abi, PPC64LE.argRegs]
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

theorem ball_post (hp : (sampleInBallContract PPC64LE.abi stk).post x y) :
    (((y.gpr .r3).setWidth 32 = 1 → Reduced y.mem (x.gpr .r6)) ∧
      Outcome (fun b => (sampleInBall ((x.gpr .r5).setWidth 32).toNat b.ball
        (bytesAt x.mem (x.gpr .r3) (x.gpr .r4).toNat)).map toRq) ((y.gpr .r3).setWidth 32)
        (polyAt y.mem (x.gpr .r6))) := by
  sig_post [sampleInBallContract, sampleInBallSig, PPC64LE.abi, PPC64LE.argRegs] at hp
  exact hp

theorem ball_pub (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4)
    (h5 : x.gpr .r5 = y.gpr .r5) (h6 : x.gpr .r6 = y.gpr .r6) (h7 : x.gpr .r7 = y.gpr .r7)
    (hl : bytesAt x.mem (x.gpr .r3) (x.gpr .r4).toNat = bytesAt y.mem (y.gpr .r3) (y.gpr .r4).toNat) :
    (sampleInBallContract PPC64LE.abi stk).pub x y := by
  sig_pub [sampleInBallContract, sampleInBallSig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨hsp, congrArg leakBytes hl, h3, h4, congrArg _ h5, h6, h7⟩

end

/-! ## `vg_mldsa_use_hint` -/

section
variable {stk : Nat} {x y : State} {h r o : Addr} {g2 : BitVec 32}

theorem useHint_pre (g3 : x.gpr .r3 = h) (g4 : x.gpr .r4 = r) (gg : (x.gpr .r5).setWidth 32 = g2)
    (g6 : x.gpr .r6 = o)
    (hrd : x.rd = [reg h 1024, reg r 1024]) (hwr : x.wr = [reg o 1024]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (reg h 1024).Disjoint (reg o 1024)) (d2 : (reg r 1024).Disjoint (reg o 1024))
    (k1 : (below x.sp stk).Disjoint (reg h 1024)) (k2 : (below x.sp stk).Disjoint (reg r 1024))
    (k3 : (below x.sp stk).Disjoint (reg o 1024)) (f1 : h.toNat + 1024 ≤ 2 ^ 64) (f2 : r.toNat + 1024 ≤ 2 ^ 64)
    (f3 : o.toNat + 1024 ≤ 2 ^ 64) (hg : g2.toNat ∈ gamma2s) (hr : Reduced x.mem r) :
    (useHintContract PPC64LE.abi stk).pre x := by
  sig_pre [useHintContract, useHintSig, PPC64LE.abi, PPC64LE.argRegs]
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

theorem useHint_post (hp : (useHintContract PPC64LE.abi stk).post x y) :
    NatPolyIs y.mem (x.gpr .r6) (Vector.zipWith (fun hj rj => (useHint ((x.gpr .r5).setWidth 32).toNat hj rj).toNat)
      ((hintAt x.mem (x.gpr .r3) 1).headD (Vector.replicate n false)) (polyAt x.mem (x.gpr .r4))) := by
  sig_post [useHintContract, useHintSig, PPC64LE.abi, PPC64LE.argRegs] at hp
  exact hp

theorem useHint_pub (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4)
    (h5 : x.gpr .r5 = y.gpr .r5) (h6 : x.gpr .r6 = y.gpr .r6) : (useHintContract PPC64LE.abi stk).pub x y := by
  sig_pub [useHintContract, useHintSig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨hsp, h3, h4, congrArg _ h5, h6⟩

end

/-! ## `vg_mldsa_bit_unpack`, `vg_mldsa_unpack_t1` -/

section
variable {stk : Nat} {x y : State} {v f len : Addr} {a b : BitVec 32}

theorem bu_pre (g3 : x.gpr .r3 = v) (g4 : x.gpr .r4 = len) (g5 : (x.gpr .r5).setWidth 32 = a)
    (g6 : (x.gpr .r6).setWidth 32 = b) (g7 : x.gpr .r7 = f)
    (hrd : x.rd = [reg v len.toNat]) (hwr : x.wr = [reg f 1024]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (reg v len.toNat).Disjoint (reg f 1024))
    (k1 : (below x.sp stk).Disjoint (reg v len.toNat)) (k2 : (below x.sp stk).Disjoint (reg f 1024))
    (f1 : v.toNat + len.toNat ≤ 2 ^ 64) (f2 : f.toNat + 1024 ≤ 2 ^ 64)
    (hab : (a.toNat, b.toNat) ∈ bitPackParams) (hl : len.toNat = 32 * bitlen (a.toNat + b.toNat)) :
    (bitUnpackContract PPC64LE.abi stk).pre x := by
  sig_pre [bitUnpackContract, bitUnpackSig, PPC64LE.abi, PPC64LE.argRegs]
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

theorem bu_post (hp : (bitUnpackContract PPC64LE.abi stk).post x y) :
    PolyIs y.mem (x.gpr .r7)
      (toRq (bitUnpack (bytesAt x.mem (x.gpr .r3) (x.gpr .r4).toNat) ((x.gpr .r5).setWidth 32).toNat
        ((x.gpr .r6).setWidth 32).toNat)) := by
  sig_post [bitUnpackContract, bitUnpackSig, PPC64LE.abi, PPC64LE.argRegs] at hp
  exact hp

theorem bu_pub (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4)
    (h5 : x.gpr .r5 = y.gpr .r5) (h6 : x.gpr .r6 = y.gpr .r6) (h7 : x.gpr .r7 = y.gpr .r7) :
    (bitUnpackContract PPC64LE.abi stk).pub x y := by
  sig_pub [bitUnpackContract, bitUnpackSig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨hsp, h3, h4, congrArg _ h5, congrArg _ h6, h7⟩

theorem t1_pre (g3 : x.gpr .r3 = v) (g4 : x.gpr .r4 = f)
    (hrd : x.rd = [reg v 320]) (hwr : x.wr = [reg f 1024]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (reg v 320).Disjoint (reg f 1024))
    (k1 : (below x.sp stk).Disjoint (reg v 320)) (k2 : (below x.sp stk).Disjoint (reg f 1024))
    (f1 : v.toNat + 320 ≤ 2 ^ 64) (f2 : f.toNat + 1024 ≤ 2 ^ 64) :
    (unpackT1Contract PPC64LE.abi stk).pre x := by
  sig_pre [unpackT1Contract, unpackT1Sig, PPC64LE.abi, PPC64LE.argRegs]
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

theorem t1_post (hp : (unpackT1Contract PPC64LE.abi stk).post x y) :
    PolyIs y.mem (x.gpr .r4)
      ((simpleBitUnpack (bytesAt x.mem (x.gpr .r3) 320) t1Max).map fun c => ofInt (c * 2 ^ d : Nat)) := by
  sig_post [unpackT1Contract, unpackT1Sig, PPC64LE.abi, PPC64LE.argRegs] at hp
  exact hp

theorem t1_pub (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4) :
    (unpackT1Contract PPC64LE.abi stk).pub x y := by
  sig_pub [unpackT1Contract, unpackT1Sig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨hsp, h3, h4⟩

end

/-! ## `vg_mldsa_hint_bit_unpack` -/

section
variable {stk : Nat} {x y : State} {yy h len hl : Addr} {om : BitVec 32}

theorem hbu_pre (g3 : x.gpr .r3 = yy) (g4 : x.gpr .r4 = len) (g5 : (x.gpr .r5).setWidth 32 = om)
    (g6 : x.gpr .r6 = h) (g7 : x.gpr .r7 = hl)
    (hrd : x.rd = [reg yy len.toNat]) (hwr : x.wr = [reg h (hl.toNat * 4)]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (reg yy len.toNat).Disjoint (reg h (hl.toNat * 4)))
    (k1 : (below x.sp stk).Disjoint (reg yy len.toNat)) (k2 : (below x.sp stk).Disjoint (reg h (hl.toNat * 4)))
    (f1 : yy.toNat + len.toNat ≤ 2 ^ 64) (f2 : h.toNat + hl.toNat * 4 ≤ 2 ^ 64)
    (hp : (om.toNat, len.toNat - om.toNat) ∈ hintParams) (ho : om.toNat ≤ len.toNat)
    (hh : hl.toNat = 256 * (len.toNat - om.toNat)) :
    (hintBitUnpackContract PPC64LE.abi stk).pre x := by
  sig_pre [hintBitUnpackContract, hintBitUnpackSig, PPC64LE.abi, PPC64LE.argRegs]
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

theorem hbu_post (hp : (hintBitUnpackContract PPC64LE.abi stk).post x y) :
    match hintBitUnpack ((x.gpr .r5).setWidth 32).toNat ((x.gpr .r4).toNat - ((x.gpr .r5).setWidth 32).toNat)
      (bytesAt x.mem (x.gpr .r3) (x.gpr .r4).toNat) with
    | some hint => (y.gpr .r3).setWidth 32 = 1 ∧
        HintIs y.mem (x.gpr .r6) ((x.gpr .r4).toNat - ((x.gpr .r5).setWidth 32).toNat) hint
    | none => (y.gpr .r3).setWidth 32 = 0 := by
  sig_post [hintBitUnpackContract, hintBitUnpackSig, PPC64LE.abi, PPC64LE.argRegs] at hp
  exact hp

theorem hbu_pub (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4)
    (h5 : x.gpr .r5 = y.gpr .r5) (h6 : x.gpr .r6 = y.gpr .r6) (h7 : x.gpr .r7 = y.gpr .r7)
    (hl : bytesAt x.mem (x.gpr .r3) (x.gpr .r4).toNat = bytesAt y.mem (y.gpr .r3) (y.gpr .r4).toNat) :
    (hintBitUnpackContract PPC64LE.abi stk).pub x y := by
  sig_pub [hintBitUnpackContract, hintBitUnpackSig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨hsp, congrArg leakBytes hl, h3, h4, congrArg _ h5, h6, h7⟩

end

/-! ## `vg_mldsa_norm_lt` -/

section
variable {stk : Nat} {x y : State} {f : Addr}

theorem normLt_pre (g3 : x.gpr .r3 = f) (hrd : x.rd = [reg f 1024]) (hwr : x.wr = [])
    (hsp : stk ≤ x.sp.toNat) (k1 : (below x.sp stk).Disjoint (reg f 1024)) (f1 : f.toNat + 1024 ≤ 2 ^ 64)
    (hr : Reduced x.mem f) : (normLtContract PPC64LE.abi stk).pre x := by
  sig_pre [normLtContract, normLtSig, PPC64LE.abi, PPC64LE.argRegs]
  simp only [g3]
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

theorem normLt_post (hp : (normLtContract PPC64LE.abi stk).post x y) :
    (y.gpr .r3).setWidth 32 =
      if normRq [polyAt x.mem (x.gpr .r3)] < ((x.gpr .r4).setWidth 32).toNat then 1 else 0 := by
  sig_post [normLtContract, normLtSig, PPC64LE.abi, PPC64LE.argRegs] at hp
  exact hp

theorem normLt_pub (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4) :
    (normLtContract PPC64LE.abi stk).pub x y := by
  sig_pub [normLtContract, normLtSig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨hsp, h3, congrArg _ h4⟩

end

end VG.Proof.MlDsa.PPC64LE.KeyGen
