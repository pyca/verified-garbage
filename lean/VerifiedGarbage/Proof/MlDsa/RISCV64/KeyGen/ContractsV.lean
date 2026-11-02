module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Contracts
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on RISC-V: the contracts of the primitives verification and signing call, evaluated

As `Contracts.lean`, for the primitives key generation does not call:
`vg_mldsa_sub`, `vg_mldsa_sample_in_ball`, `vg_mldsa_use_hint`,
`vg_mldsa_bit_unpack`, `vg_mldsa_unpack_t1`, `vg_mldsa_hint_bit_unpack` and
`vg_mldsa_norm_lt`. A `usize` argument is its whole register, and a `u32`
argument or result the low word of its register.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.KeyGen

open VG VG.RISCV64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `vg_mldsa_sub` -/

section
variable {stk : Nat} {x y : State} {f g : Addr}

theorem sub_pre (g3 : x.gpr .a0 = f) (g4 : x.gpr .a1 = g) (hrd : x.rd = [reg g 1024])
    (hwr : x.wr = [reg f 1024]) (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0)
    (al_f : f.toNat % 4 = 0) (al_g : g.toNat % 4 = 0) (d1 : (reg f 1024).Disjoint (reg g 1024))
    (kf : (below x.sp stk).Disjoint (reg f 1024)) (kg : (below x.sp stk).Disjoint (reg g 1024))
    (ff : f.toNat + 1024 ≤ 2 ^ 64) (fg : g.toNat + 1024 ≤ 2 ^ 64) (rf : Reduced x.mem f)
    (rg : Reduced x.mem g) : (subContract RISCV64.abi stk).pre x := by
  sig_pre [subContract, accSig, RISCV64.abi, RISCV64.argRegs]
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

theorem sub_post (hp : (subContract RISCV64.abi stk).post x y) :
    PolyIs y.mem (x.gpr .a0) (sub (polyAt x.mem (x.gpr .a0)) (polyAt x.mem (x.gpr .a1))) := by
  sig_post [subContract, accSig, RISCV64.abi, RISCV64.argRegs] at hp
  exact hp

theorem sub_pub (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1) :
    (subContract RISCV64.abi stk).pub x y := by
  sig_pub [subContract, accSig, RISCV64.abi, RISCV64.argRegs]
  exact ⟨hsp, h3, h4⟩

end

/-! ## `vg_mldsa_sample_in_ball` -/

section
variable {stk : Nat} {x y : State} {ct c w len : Addr} {tau : BitVec 32}

theorem ball_pre (g3 : x.gpr .a0 = ct) (g4 : x.gpr .a1 = len) (g5 : (x.gpr .a2).setWidth 32 = tau)
    (g6 : x.gpr .a3 = c) (g7 : x.gpr .a4 = w)
    (hrd : x.rd = [reg ct len.toNat]) (hwr : x.wr = [reg c 1024, reg w 2048]) (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0)
    (al_c : c.toNat % 4 = 0) (al_w : w.toNat % 8 = 0)
    (d1 : (reg ct len.toNat).Disjoint (reg c 1024)) (d2 : (reg ct len.toNat).Disjoint (reg w 2048))
    (d3 : (reg c 1024).Disjoint (reg w 2048))
    (k1 : (below x.sp stk).Disjoint (reg ct len.toNat)) (k2 : (below x.sp stk).Disjoint (reg c 1024))
    (k3 : (below x.sp stk).Disjoint (reg w 2048))
    (f1 : ct.toNat + len.toNat ≤ 2 ^ 64) (f2 : c.toNat + 1024 ≤ 2 ^ 64) (f3 : w.toNat + 2048 ≤ 2 ^ 64)
    (hp : (len.toNat, tau.toNat) ∈ ballParams) : (sampleInBallContract RISCV64.abi stk).pre x := by
  sig_pre [sampleInBallContract, sampleInBallSig, RISCV64.abi, RISCV64.argRegs]
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

theorem ball_post (hp : (sampleInBallContract RISCV64.abi stk).post x y) :
    (((y.gpr .a0).setWidth 32 = 1 → Reduced y.mem (x.gpr .a3)) ∧
      Outcome (fun b => (sampleInBall ((x.gpr .a2).setWidth 32).toNat b.ball
        (bytesAt x.mem (x.gpr .a0) (x.gpr .a1).toNat)).map toRq) ((y.gpr .a0).setWidth 32)
        (polyAt y.mem (x.gpr .a3))) := by
  sig_post [sampleInBallContract, sampleInBallSig, RISCV64.abi, RISCV64.argRegs] at hp
  exact hp

theorem ball_pub (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1)
    (h5 : x.gpr .a2 = y.gpr .a2) (h6 : x.gpr .a3 = y.gpr .a3) (h7 : x.gpr .a4 = y.gpr .a4)
    (hl : bytesAt x.mem (x.gpr .a0) (x.gpr .a1).toNat = bytesAt y.mem (y.gpr .a0) (y.gpr .a1).toNat) :
    (sampleInBallContract RISCV64.abi stk).pub x y := by
  sig_pub [sampleInBallContract, sampleInBallSig, RISCV64.abi, RISCV64.argRegs]
  exact ⟨hsp, congrArg leakBytes hl, h3, h4, congrArg _ h5, h6, h7⟩

end

/-! ## `vg_mldsa_use_hint` -/

section
variable {stk : Nat} {x y : State} {h r o : Addr} {g2 : BitVec 32}

theorem useHint_pre (g3 : x.gpr .a0 = h) (g4 : x.gpr .a1 = r) (gg : (x.gpr .a2).setWidth 32 = g2)
    (g6 : x.gpr .a3 = o)
    (hrd : x.rd = [reg h 1024, reg r 1024]) (hwr : x.wr = [reg o 1024]) (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0)
    (al_h : h.toNat % 4 = 0) (al_r : r.toNat % 4 = 0) (al_o : o.toNat % 4 = 0)
    (d1 : (reg h 1024).Disjoint (reg o 1024)) (d2 : (reg r 1024).Disjoint (reg o 1024))
    (k1 : (below x.sp stk).Disjoint (reg h 1024)) (k2 : (below x.sp stk).Disjoint (reg r 1024))
    (k3 : (below x.sp stk).Disjoint (reg o 1024)) (f1 : h.toNat + 1024 ≤ 2 ^ 64) (f2 : r.toNat + 1024 ≤ 2 ^ 64)
    (f3 : o.toNat + 1024 ≤ 2 ^ 64) (hg : g2.toNat ∈ gamma2s) (hr : Reduced x.mem r) :
    (useHintContract RISCV64.abi stk).pre x := by
  sig_pre [useHintContract, useHintSig, RISCV64.abi, RISCV64.argRegs]
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

theorem useHint_post (hp : (useHintContract RISCV64.abi stk).post x y) :
    NatPolyIs y.mem (x.gpr .a3) (Vector.zipWith (fun hj rj => (useHint ((x.gpr .a2).setWidth 32).toNat hj rj).toNat)
      ((hintAt x.mem (x.gpr .a0) 1).headD (Vector.replicate n false)) (polyAt x.mem (x.gpr .a1))) := by
  sig_post [useHintContract, useHintSig, RISCV64.abi, RISCV64.argRegs] at hp
  exact hp

theorem useHint_pub (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1)
    (h5 : x.gpr .a2 = y.gpr .a2) (h6 : x.gpr .a3 = y.gpr .a3) : (useHintContract RISCV64.abi stk).pub x y := by
  sig_pub [useHintContract, useHintSig, RISCV64.abi, RISCV64.argRegs]
  exact ⟨hsp, h3, h4, congrArg _ h5, h6⟩

end

/-! ## `vg_mldsa_bit_unpack`, `vg_mldsa_unpack_t1` -/

section
variable {stk : Nat} {x y : State} {v f len : Addr} {a b : BitVec 32}

theorem bu_pre (g3 : x.gpr .a0 = v) (g4 : x.gpr .a1 = len) (g5 : (x.gpr .a2).setWidth 32 = a)
    (g6 : (x.gpr .a3).setWidth 32 = b) (g7 : x.gpr .a4 = f)
    (hrd : x.rd = [reg v len.toNat]) (hwr : x.wr = [reg f 1024]) (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0)
    (al_f : f.toNat % 4 = 0)
    (d1 : (reg v len.toNat).Disjoint (reg f 1024))
    (k1 : (below x.sp stk).Disjoint (reg v len.toNat)) (k2 : (below x.sp stk).Disjoint (reg f 1024))
    (f1 : v.toNat + len.toNat ≤ 2 ^ 64) (f2 : f.toNat + 1024 ≤ 2 ^ 64)
    (hab : (a.toNat, b.toNat) ∈ bitPackParams) (hl : len.toNat = 32 * bitlen (a.toNat + b.toNat)) :
    (bitUnpackContract RISCV64.abi stk).pre x := by
  sig_pre [bitUnpackContract, bitUnpackSig, RISCV64.abi, RISCV64.argRegs]
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

theorem bu_post (hp : (bitUnpackContract RISCV64.abi stk).post x y) :
    PolyIs y.mem (x.gpr .a4)
      (toRq (bitUnpack (bytesAt x.mem (x.gpr .a0) (x.gpr .a1).toNat) ((x.gpr .a2).setWidth 32).toNat
        ((x.gpr .a3).setWidth 32).toNat)) := by
  sig_post [bitUnpackContract, bitUnpackSig, RISCV64.abi, RISCV64.argRegs] at hp
  exact hp

theorem bu_pub (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1)
    (h5 : x.gpr .a2 = y.gpr .a2) (h6 : x.gpr .a3 = y.gpr .a3) (h7 : x.gpr .a4 = y.gpr .a4) :
    (bitUnpackContract RISCV64.abi stk).pub x y := by
  sig_pub [bitUnpackContract, bitUnpackSig, RISCV64.abi, RISCV64.argRegs]
  exact ⟨hsp, h3, h4, congrArg _ h5, congrArg _ h6, h7⟩

theorem t1_pre (g3 : x.gpr .a0 = v) (g4 : x.gpr .a1 = f)
    (hrd : x.rd = [reg v 320]) (hwr : x.wr = [reg f 1024]) (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0)
    (al_f : f.toNat % 4 = 0)
    (d1 : (reg v 320).Disjoint (reg f 1024))
    (k1 : (below x.sp stk).Disjoint (reg v 320)) (k2 : (below x.sp stk).Disjoint (reg f 1024))
    (f1 : v.toNat + 320 ≤ 2 ^ 64) (f2 : f.toNat + 1024 ≤ 2 ^ 64) :
    (unpackT1Contract RISCV64.abi stk).pre x := by
  sig_pre [unpackT1Contract, unpackT1Sig, RISCV64.abi, RISCV64.argRegs]
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

theorem t1_post (hp : (unpackT1Contract RISCV64.abi stk).post x y) :
    PolyIs y.mem (x.gpr .a1)
      ((simpleBitUnpack (bytesAt x.mem (x.gpr .a0) 320) t1Max).map fun c => ofInt (c * 2 ^ d : Nat)) := by
  sig_post [unpackT1Contract, unpackT1Sig, RISCV64.abi, RISCV64.argRegs] at hp
  exact hp

theorem t1_pub (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1) :
    (unpackT1Contract RISCV64.abi stk).pub x y := by
  sig_pub [unpackT1Contract, unpackT1Sig, RISCV64.abi, RISCV64.argRegs]
  exact ⟨hsp, h3, h4⟩

end

/-! ## `vg_mldsa_hint_bit_unpack` -/

section
variable {stk : Nat} {x y : State} {yy h len hl : Addr} {om : BitVec 32}

theorem hbu_pre (g3 : x.gpr .a0 = yy) (g4 : x.gpr .a1 = len) (g5 : (x.gpr .a2).setWidth 32 = om)
    (g6 : x.gpr .a3 = h) (g7 : x.gpr .a4 = hl)
    (hrd : x.rd = [reg yy len.toNat]) (hwr : x.wr = [reg h (hl.toNat * 4)]) (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0)
    (al_h : h.toNat % 4 = 0)
    (d1 : (reg yy len.toNat).Disjoint (reg h (hl.toNat * 4)))
    (k1 : (below x.sp stk).Disjoint (reg yy len.toNat)) (k2 : (below x.sp stk).Disjoint (reg h (hl.toNat * 4)))
    (f1 : yy.toNat + len.toNat ≤ 2 ^ 64) (f2 : h.toNat + hl.toNat * 4 ≤ 2 ^ 64)
    (hp : (om.toNat, len.toNat - om.toNat) ∈ hintParams) (ho : om.toNat ≤ len.toNat)
    (hh : hl.toNat = 256 * (len.toNat - om.toNat)) :
    (hintBitUnpackContract RISCV64.abi stk).pre x := by
  sig_pre [hintBitUnpackContract, hintBitUnpackSig, RISCV64.abi, RISCV64.argRegs]
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

theorem hbu_post (hp : (hintBitUnpackContract RISCV64.abi stk).post x y) :
    match hintBitUnpack ((x.gpr .a2).setWidth 32).toNat ((x.gpr .a1).toNat - ((x.gpr .a2).setWidth 32).toNat)
      (bytesAt x.mem (x.gpr .a0) (x.gpr .a1).toNat) with
    | some hint => (y.gpr .a0).setWidth 32 = 1 ∧
        HintIs y.mem (x.gpr .a3) ((x.gpr .a1).toNat - ((x.gpr .a2).setWidth 32).toNat) hint
    | none => (y.gpr .a0).setWidth 32 = 0 := by
  sig_post [hintBitUnpackContract, hintBitUnpackSig, RISCV64.abi, RISCV64.argRegs] at hp
  exact hp

theorem hbu_pub (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1)
    (h5 : x.gpr .a2 = y.gpr .a2) (h6 : x.gpr .a3 = y.gpr .a3) (h7 : x.gpr .a4 = y.gpr .a4)
    (hl : bytesAt x.mem (x.gpr .a0) (x.gpr .a1).toNat = bytesAt y.mem (y.gpr .a0) (y.gpr .a1).toNat) :
    (hintBitUnpackContract RISCV64.abi stk).pub x y := by
  sig_pub [hintBitUnpackContract, hintBitUnpackSig, RISCV64.abi, RISCV64.argRegs]
  exact ⟨hsp, congrArg leakBytes hl, h3, h4, congrArg _ h5, h6, h7⟩

end

/-! ## `vg_mldsa_norm_lt` -/

section
variable {stk : Nat} {x y : State} {f : Addr}

theorem normLt_pre (g3 : x.gpr .a0 = f) (hrd : x.rd = [reg f 1024]) (hwr : x.wr = [])
    (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0)
    (al_f : f.toNat % 4 = 0) (k1 : (below x.sp stk).Disjoint (reg f 1024)) (f1 : f.toNat + 1024 ≤ 2 ^ 64)
    (hr : Reduced x.mem f) : (normLtContract RISCV64.abi stk).pre x := by
  sig_pre [normLtContract, normLtSig, RISCV64.abi, RISCV64.argRegs]
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

theorem normLt_post (hp : (normLtContract RISCV64.abi stk).post x y) :
    (y.gpr .a0).setWidth 32 =
      if normRq [polyAt x.mem (x.gpr .a0)] < ((x.gpr .a1).setWidth 32).toNat then 1 else 0 := by
  sig_post [normLtContract, normLtSig, RISCV64.abi, RISCV64.argRegs] at hp
  exact hp

theorem normLt_pub (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1) :
    (normLtContract RISCV64.abi stk).pub x y := by
  sig_pub [normLtContract, normLtSig, RISCV64.abi, RISCV64.argRegs]
  exact ⟨hsp, h3, congrArg _ h4⟩

end

end VG.Proof.MlDsa.RISCV64.KeyGen
