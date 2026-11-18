module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Inv
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.StepsCT
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Samp
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.CallSP
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Contracts
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.CallV
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.MlDsa.Sign.Leak
import VerifiedGarbage.Proof.MlDsa.Sign.Setup
import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.ContractsV
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlKem.Mem

/-! ### `MlDsa.PPC64LE.KeyGen.CallS`, which only this module used -/

section

/-! ### `MlDsa.PPC64LE.KeyGen.ContractsS`, which only this module used -/

section

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

end

end


/-!
# ML-DSA on PPC64LE: calling the primitives only signing uses

As `ip_ok` and `ip_tr` (`Call.lean`), in the buffers of a `Site`:
`vg_mldsa_expand_mask_poly`, `vg_mldsa_high_bits`, `vg_mldsa_low_bits`,
`vg_mldsa_make_hint` and `vg_mldsa_hint_bit_pack`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.KeyGen

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Impl.MlDsa.PPC64LE.KeyGen
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `vg_mldsa_expand_mask_poly` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {sd a w : Ptr} {g1 : Nat}

abbrev emArgs (sd : Ptr) (g1 : Nat) (a w : Ptr) : List (Reg × Arg) :=
  [(.r3, .ptr sd), (.r4, .imm g1), (.r5, .ptr a), (.r6, .ptr w)]

theorem em_hg (m : RbOk L Wb sd a w) (hg : g1 = 2 ^ 17 ∨ g1 = 2 ^ 19) : glueOk (emArgs sd g1 a w) = true := by
  have : argOk (.imm g1) = true := argOk_imm (by omega_arith)
  simp [glueOk, argReg, m.ps.1, m.pa.1, m.pw.1, this]

theorem emArgs_nodup : ((emArgs sd g1 a w).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide

theorem em_vg {s : State} (hs : Site L Wb STK s) (m : RbOk L Wb sd a w) (hg : g1 = 2 ^ 17 ∨ g1 = 2 ^ 19)
    (rd wr : List Region) :
    (view (glueSt s (emArgs sd g1 a w)) rd wr).gpr .r3 = lpa L sd ∧
    (view (glueSt s (emArgs sd g1 a w)) rd wr).gpr .r4 = BitVec.ofNat 64 g1 ∧
    (view (glueSt s (emArgs sd g1 a w)) rd wr).gpr .r5 = lpa L a ∧
    (view (glueSt s (emArgs sd g1 a w)) rd wr).gpr .r6 = lpa L w :=
  ⟨hs.vG (em_hg m hg) emArgs_nodup (by simp) m.ps.1 (by decide) _ _,
    vI (em_hg m hg) emArgs_nodup (by simp) (by decide) _ _,
    hs.vG (em_hg m hg) emArgs_nodup (by simp) m.pa.1 (by decide) _ _,
    hs.vG (em_hg m hg) emArgs_nodup (by simp) m.pw.1 (by decide) _ _⟩

theorem em_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : RbOk L Wb sd a w)
    (hg : g1 = 2 ^ 17 ∨ g1 = 2 ^ 19) :
    (expandMaskContract PPC64LE.abi stk).pre (view (glueSt s (emArgs sd g1 a w)) (rbRd L sd) (rnWr L a w)) := by
  have hsp := view_glue_sp s (emArgs sd g1 a w) (rbRd L sd) (rnWr L a w)
  obtain ⟨g3, g4, g5, g6⟩ := em_vg hs m hg (rbRd L sd) (rnWr L a w)
  have e4 : ((view (glueSt s (emArgs sd g1 a w)) (rbRd L sd) (rnWr L a w)).gpr .r4).setWidth 32 =
      BitVec.ofNat 32 g1 := by
    rw [g4]; exact imm32 (by omega_arith)
  exact em_pre g3 e4 g5 g6 rfl rfl (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.dE m.d1 (.inr m.wa))
    (hs.dE m.d2 (.inr m.ww)) (hs.dE m.d3 (.inl m.wa)) (hs.kE m.ps hstk hsp) (hs.kE m.pa hstk hsp)
    (hs.kE m.pw hstk hsp) (hs.fitE m.ps (by decide)) (hs.fitE m.pa (by decide)) (hs.fitE m.pw (by decide))
    (by rw [imm32_toNat (by omega_arith)]; exact hg)

theorem em_ok {c : Prog isa} (hc : Callee c (fun stk => expandMaskContract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : RbOk L Wb sd a w) (hg : g1 = 2 ^ 17 ∨ g1 = 2 ^ 19)
    {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri a 1024, tri w 2048, (1, 0, STK)]) s s' →
      PolyIs s'.mem (lpa L a) (toRq (bitUnpack (H (bytesAt s.mem (lpa L sd) 66) (32 * (1 + bitlen (g1 - 1))))
        (g1 - 1) g1)) → Q s') :
    WP isa (callAt name c (emArgs sd g1 a w)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := rb_cov hs m
  refine callV hver.1 (hs.depth hc.stack hS) (em_hg m hg) (em_preS hs (Nat.le_trans hstk hS) m hg) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri a 1024, tri w 2048] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g3, g4, g5, -⟩ := em_vg hs m hg (rbRd L sd) (rnWr L a w)
  have := em_post hp
  rwa [State.withRegions_mem, g3, g4, g5, view_glue_mem, imm32 (by omega_arith), imm32_toNat (by omega_arith)] at this

theorem em_tr {c : Prog isa} (hc : Callee c (fun stk => expandMaskContract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : RbOk L Wb sd a w) (hg : g1 = 2 ^ 17 ∨ g1 = 2 ^ 19) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp) :
    RelCT isa P (callAt name c (emArgs sd g1 a w)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 (em_hg m hg) fun x y hxy => ?_
  obtain ⟨hx, hy, hsp⟩ := hP x y hxy
  obtain ⟨gx3, gx4, gx5, gx6⟩ := em_vg hx m hg (rbRd L sd) (rnWr L a w)
  obtain ⟨gy3, gy4, gy5, gy6⟩ := em_vg hy m hg (rbRd L sd) (rnWr L a w)
  exact ⟨rbRd L sd, rnWr L a w, em_preS hx (Nat.le_trans hstk hS) m hg, em_preS hy (Nat.le_trans hstk hS) m hg,
    em_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4]) (by rw [gx5, gy5])
      (by rw [gx6, gy6]), (rb_cov hx m).1, (rb_cov hx m).2, (rb_cov hy m).1, (rb_cov hy m).2⟩

end

/-! ## `vg_mldsa_high_bits`, `vg_mldsa_low_bits` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {r o : Ptr} {g2 : Nat}

abbrev bitsArgs (r : Ptr) (g2 : Nat) (o : Ptr) : List (Reg × Arg) := [(.r3, .ptr r), (.r4, .imm g2), (.r5, .ptr o)]
abbrev bitsRd (L : Lay) (r : Ptr) : List Region := [L.R (ix r.1) r.2 1024]
abbrev bitsWr (L : Lay) (o : Ptr) : List Region := [L.R (ix o.1) o.2 1024]

/-- The facts `vg_mldsa_high_bits` and `vg_mldsa_low_bits` need of their arguments. -/
structure BitsOk (L : Lay) (Wb : List Nat) (r : Ptr) (g2 : Nat) (o : Ptr) : Prop where
  pr : PtrIn L r 1024
  po : PtrIn L o 1024
  wo : ix o.1 ∈ Wb
  d1 : sepB L.sizes (tri r 1024) (tri o 1024) = true
  hg : g2 ∈ gamma2s
  lt : g2 < 2 ^ 31

theorem BitsOk.hg' (m : BitsOk L Wb r g2 o) : glueOk (bitsArgs r g2 o) = true := by
  have h1 : argOk (.imm g2) = true := argOk_imm m.lt
  simp [glueOk, argReg, m.pr.1, m.po.1, h1]

theorem bitsArgs_nodup : ((bitsArgs r g2 o).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide

theorem bits_vg {s : State} (hs : Site L Wb STK s) (m : BitsOk L Wb r g2 o) (rd wr : List Region) :
    (view (glueSt s (bitsArgs r g2 o)) rd wr).gpr .r3 = lpa L r ∧
    (view (glueSt s (bitsArgs r g2 o)) rd wr).gpr .r4 = BitVec.ofNat 64 g2 ∧
    (view (glueSt s (bitsArgs r g2 o)) rd wr).gpr .r5 = lpa L o :=
  ⟨hs.vG m.hg' bitsArgs_nodup (by simp) m.pr.1 (by decide) _ _, vI m.hg' bitsArgs_nodup (by simp) (by decide) _ _,
    hs.vG m.hg' bitsArgs_nodup (by simp) m.po.1 (by decide) _ _⟩

theorem bits_cov {s : State} (hs : Site L Wb STK s) (m : BitsOk L Wb r g2 o) :
    Covers (bitsRd L r ++ bitsWr L o) (s.rd ++ s.wr) ∧ Covers (bitsWr L o) s.wr :=
  ⟨Covers.append_left (Covers.cons (hs.crE m.pr) Covers.nil) (Covers.right (Covers.cons (hs.cwE m.po m.wo) Covers.nil)),
    Covers.cons (hs.cwE m.po m.wo) Covers.nil⟩

theorem hb_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : BitsOk L Wb r g2 o)
    (hr : Reduced s.mem (lpa L r)) :
    (highBitsContract PPC64LE.abi stk).pre (view (glueSt s (bitsArgs r g2 o)) (bitsRd L r) (bitsWr L o)) := by
  have hsp := view_glue_sp s (bitsArgs r g2 o) (bitsRd L r) (bitsWr L o)
  obtain ⟨g3, g4, g5⟩ := bits_vg hs m (bitsRd L r) (bitsWr L o)
  have e4 : ((view (glueSt s (bitsArgs r g2 o)) (bitsRd L r) (bitsWr L o)).gpr .r4).setWidth 32 =
      BitVec.ofNat 32 g2 := by
    rw [g4]; exact imm32 (by have := m.lt; omega_arith)
  refine hb_pre g3 e4 g5 rfl rfl (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.dE m.d1 (.inr m.wo))
    (hs.kE m.pr hstk hsp) (hs.kE m.po hstk hsp) (hs.fitE m.pr (by decide)) (hs.fitE m.po (by decide))
    (by rw [imm32_toNat (by have := m.lt; omega_arith)]; exact m.hg) ?_
  rw [view_glue_mem]; exact hr

theorem lb_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : BitsOk L Wb r g2 o)
    (hr : Reduced s.mem (lpa L r)) :
    (lowBitsContract PPC64LE.abi stk).pre (view (glueSt s (bitsArgs r g2 o)) (bitsRd L r) (bitsWr L o)) := by
  have hsp := view_glue_sp s (bitsArgs r g2 o) (bitsRd L r) (bitsWr L o)
  obtain ⟨g3, g4, g5⟩ := bits_vg hs m (bitsRd L r) (bitsWr L o)
  have e4 : ((view (glueSt s (bitsArgs r g2 o)) (bitsRd L r) (bitsWr L o)).gpr .r4).setWidth 32 =
      BitVec.ofNat 32 g2 := by
    rw [g4]; exact imm32 (by have := m.lt; omega_arith)
  refine lb_pre g3 e4 g5 rfl rfl (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.dE m.d1 (.inr m.wo))
    (hs.kE m.pr hstk hsp) (hs.kE m.po hstk hsp) (hs.fitE m.pr (by decide)) (hs.fitE m.po (by decide))
    (by rw [imm32_toNat (by have := m.lt; omega_arith)]; exact m.hg) ?_
  rw [view_glue_mem]; exact hr

theorem hb_ok {c : Prog isa} (hc : Callee c (fun stk => highBitsContract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : BitsOk L Wb r g2 o)
    (hr : Reduced s.mem (lpa L r)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri o 1024, (1, 0, STK)]) s s' →
      NatPolyIs s'.mem (lpa L o) ((polyAt s.mem (lpa L r)).map fun c => (highBits g2 c).toNat) → Q s') :
    WP isa (callAt name c (bitsArgs r g2 o)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := bits_cov hs m
  refine callV hver.1 (hs.depth hc.stack hS) m.hg' (hb_preS hs (Nat.le_trans hstk hS) m hr) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri o 1024] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g3, g4, g5⟩ := bits_vg hs m (bitsRd L r) (bitsWr L o)
  have := hb_post hp
  rwa [State.withRegions_mem, g3, g4, g5, view_glue_mem, imm32 (by have := m.lt; omega_arith),
    imm32_toNat (by have := m.lt; omega_arith)] at this

theorem lb_ok {c : Prog isa} (hc : Callee c (fun stk => lowBitsContract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : BitsOk L Wb r g2 o)
    (hr : Reduced s.mem (lpa L r)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri o 1024, (1, 0, STK)]) s s' →
      PolyIs s'.mem (lpa L o) ((polyAt s.mem (lpa L r)).map fun c => ofInt (lowBits g2 c)) → Q s') :
    WP isa (callAt name c (bitsArgs r g2 o)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := bits_cov hs m
  refine callV hver.1 (hs.depth hc.stack hS) m.hg' (lb_preS hs (Nat.le_trans hstk hS) m hr) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri o 1024] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g3, g4, g5⟩ := bits_vg hs m (bitsRd L r) (bitsWr L o)
  have := lb_post hp
  rwa [State.withRegions_mem, g3, g4, g5, view_glue_mem, imm32 (by have := m.lt; omega_arith),
    imm32_toNat (by have := m.lt; omega_arith)] at this

theorem hb_tr {c : Prog isa} (hc : Callee c (fun stk => highBitsContract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : BitsOk L Wb r g2 o) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (lpa L r) ∧
      Reduced y.mem (lpa L r)) :
    RelCT isa P (callAt name c (bitsArgs r g2 o)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg' fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rx, ry⟩ := hP x y hxy
  obtain ⟨gx3, gx4, gx5⟩ := bits_vg hx m (bitsRd L r) (bitsWr L o)
  obtain ⟨gy3, gy4, gy5⟩ := bits_vg hy m (bitsRd L r) (bitsWr L o)
  exact ⟨bitsRd L r, bitsWr L o, hb_preS hx (Nat.le_trans hstk hS) m rx, hb_preS hy (Nat.le_trans hstk hS) m ry,
    hb_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4]) (by rw [gx5, gy5]),
    (bits_cov hx m).1, (bits_cov hx m).2, (bits_cov hy m).1, (bits_cov hy m).2⟩

theorem lb_tr {c : Prog isa} (hc : Callee c (fun stk => lowBitsContract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : BitsOk L Wb r g2 o) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (lpa L r) ∧
      Reduced y.mem (lpa L r)) :
    RelCT isa P (callAt name c (bitsArgs r g2 o)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg' fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rx, ry⟩ := hP x y hxy
  obtain ⟨gx3, gx4, gx5⟩ := bits_vg hx m (bitsRd L r) (bitsWr L o)
  obtain ⟨gy3, gy4, gy5⟩ := bits_vg hy m (bitsRd L r) (bitsWr L o)
  exact ⟨bitsRd L r, bitsWr L o, lb_preS hx (Nat.le_trans hstk hS) m rx, lb_preS hy (Nat.le_trans hstk hS) m ry,
    lb_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4]) (by rw [gx5, gy5]),
    (bits_cov hx m).1, (bits_cov hx m).2, (bits_cov hy m).1, (bits_cov hy m).2⟩

end

/-! ## `vg_mldsa_make_hint` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {z r h : Ptr} {g2 : Nat}

abbrev mhArgs (z r : Ptr) (g2 : Nat) (h : Ptr) : List (Reg × Arg) :=
  [(.r3, .ptr z), (.r4, .ptr r), (.r5, .imm g2), (.r6, .ptr h)]

theorem mh_vg {s : State} (hs : Site L Wb STK s) (m : UhOk L Wb z r g2 h) (rd wr : List Region) :
    (view (glueSt s (mhArgs z r g2 h)) rd wr).gpr .r3 = lpa L z ∧
    (view (glueSt s (mhArgs z r g2 h)) rd wr).gpr .r4 = lpa L r ∧
    (view (glueSt s (mhArgs z r g2 h)) rd wr).gpr .r5 = BitVec.ofNat 64 g2 ∧
    (view (glueSt s (mhArgs z r g2 h)) rd wr).gpr .r6 = lpa L h :=
  uh_vg hs m rd wr

theorem mh_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : UhOk L Wb z r g2 h)
    (hz : Reduced s.mem (lpa L z)) (hr : Reduced s.mem (lpa L r)) :
    (makeHintContract PPC64LE.abi stk).pre (view (glueSt s (mhArgs z r g2 h)) (uhRd L z r) (uhWr L h)) := by
  have hsp := view_glue_sp s (mhArgs z r g2 h) (uhRd L z r) (uhWr L h)
  obtain ⟨g3, g4, g5, g6⟩ := mh_vg hs m (uhRd L z r) (uhWr L h)
  have e5 : ((view (glueSt s (mhArgs z r g2 h)) (uhRd L z r) (uhWr L h)).gpr .r5).setWidth 32 =
      BitVec.ofNat 32 g2 := by
    rw [g5]; exact imm32 (by have := m.lt; omega_arith)
  refine mh_pre g3 g4 e5 g6 rfl rfl (by rw [hsp]; exact Nat.le_trans hstk hs.spk)
    (hs.dE m.d1 (.inr m.wo)) (hs.dE m.d2 (.inr m.wo)) (hs.kE m.ph hstk hsp) (hs.kE m.pr hstk hsp)
    (hs.kE m.po hstk hsp) (hs.fitE m.ph (by decide)) (hs.fitE m.pr (by decide)) (hs.fitE m.po (by decide))
    (by rw [imm32_toNat (by have := m.lt; omega_arith)]; exact m.hg) ?_ ?_
  · rw [view_glue_mem]; exact hz
  · rw [view_glue_mem]; exact hr

theorem mh_ok {c : Prog isa} (hc : Callee c (fun stk => makeHintContract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : UhOk L Wb z r g2 h)
    (hz : Reduced s.mem (lpa L z)) (hr : Reduced s.mem (lpa L r)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri h 1024, (1, 0, STK)]) s s' →
      HintIs s'.mem (lpa L h) 1 [Vector.zipWith (makeHint g2) (polyAt s.mem (lpa L z)) (polyAt s.mem (lpa L r))] →
      ((s'.gpr .r3).setWidth 32).toNat =
        hintOnes [Vector.zipWith (makeHint g2) (polyAt s.mem (lpa L z)) (polyAt s.mem (lpa L r))] → Q s') :
    WP isa (callAt name c (mhArgs z r g2 h)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := uh_cov hs m
  refine callV hver.1 (hs.depth hc.stack hS) m.hg' (mh_preS hs (Nat.le_trans hstk hS) m hz hr) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri h 1024] (Nat.le_trans hc.stack hS) hk) ?_ ?_
  all_goals
    obtain ⟨g3, g4, g5, g6⟩ := mh_vg hs m (uhRd L z r) (uhWr L h)
    have := mh_post hp
    rw [g3, g4, g5, g6, view_glue_mem, State.withRegions_mem, State.withRegions_gpr, imm32 (by have := m.lt; omega_arith),
      imm32_toNat (by have := m.lt; omega_arith)] at this
  exacts [this.1, this.2]

theorem mh_tr {c : Prog isa} (hc : Callee c (fun stk => makeHintContract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : UhOk L Wb z r g2 h) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (lpa L z) ∧
      Reduced x.mem (lpa L r) ∧ Reduced y.mem (lpa L z) ∧ Reduced y.mem (lpa L r)) :
    RelCT isa P (callAt name c (mhArgs z r g2 h)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg' fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rxz, rxr, ryz, ryr⟩ := hP x y hxy
  obtain ⟨gx3, gx4, gx5, gx6⟩ := mh_vg hx m (uhRd L z r) (uhWr L h)
  obtain ⟨gy3, gy4, gy5, gy6⟩ := mh_vg hy m (uhRd L z r) (uhWr L h)
  exact ⟨uhRd L z r, uhWr L h, mh_preS hx (Nat.le_trans hstk hS) m rxz rxr,
    mh_preS hy (Nat.le_trans hstk hS) m ryz ryr,
    mh_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4]) (by rw [gx5, gy5])
      (by rw [gx6, gy6]), (uh_cov hx m).1, (uh_cov hx m).2, (uh_cov hy m).1, (uh_cov hy m).2⟩

end

/-! ## `vg_mldsa_hint_bit_pack` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {h y : Ptr} {hl om len : Nat}

abbrev hbpArgs (h : Ptr) (hl om : Nat) (y : Ptr) (len : Nat) : List (Reg × Arg) :=
  [(.r3, .ptr h), (.r4, .imm hl), (.r5, .imm om), (.r6, .ptr y), (.r7, .imm len)]
abbrev hbpRd (L : Lay) (h : Ptr) (hl : Nat) : List Region := [L.R (ix h.1) h.2 (hl * 4)]
abbrev hbpWr (L : Lay) (y : Ptr) (len : Nat) : List Region := [L.R (ix y.1) y.2 len]

/-- The facts `vg_mldsa_hint_bit_pack` needs of its arguments. -/
structure HbpOk (L : Lay) (Wb : List Nat) (h : Ptr) (hl om : Nat) (y : Ptr) (len : Nat) : Prop where
  ph : PtrIn L h (hl * 4)
  py : PtrIn L y len
  wy : ix y.1 ∈ Wb
  d1 : sepB L.sizes (tri h (hl * 4)) (tri y len) = true
  hp : (om, len - om) ∈ hintParams
  ho : om ≤ len
  hh : hl = 256 * (len - om)
  lt : 0 < len ∧ len < 2 ^ 31 ∧ om < 2 ^ 31 ∧ 0 < hl * 4 ∧ hl < 2 ^ 31

theorem HbpOk.hg (m : HbpOk L Wb h hl om y len) : glueOk (hbpArgs h hl om y len) = true := by
  obtain ⟨-, l1, l2, -, l4⟩ := m.lt
  have h1 : argOk (.imm hl) = true := argOk_imm l4
  have h2 : argOk (.imm om) = true := argOk_imm l2
  have h3 : argOk (.imm len) = true := argOk_imm l1
  simp [glueOk, argReg, m.ph.1, m.py.1, h1, h2, h3]

theorem hbpArgs_nodup : ((hbpArgs h hl om y len).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil]; decide

theorem hbp_vg {s : State} (hs : Site L Wb STK s) (m : HbpOk L Wb h hl om y len) (rd wr : List Region) :
    (view (glueSt s (hbpArgs h hl om y len)) rd wr).gpr .r3 = lpa L h ∧
    (view (glueSt s (hbpArgs h hl om y len)) rd wr).gpr .r4 = BitVec.ofNat 64 hl ∧
    (view (glueSt s (hbpArgs h hl om y len)) rd wr).gpr .r5 = BitVec.ofNat 64 om ∧
    (view (glueSt s (hbpArgs h hl om y len)) rd wr).gpr .r6 = lpa L y ∧
    (view (glueSt s (hbpArgs h hl om y len)) rd wr).gpr .r7 = BitVec.ofNat 64 len :=
  ⟨hs.vG m.hg hbpArgs_nodup (by simp) m.ph.1 (by decide) _ _, vI m.hg hbpArgs_nodup (by simp) (by decide) _ _,
    vI m.hg hbpArgs_nodup (by simp) (by decide) _ _, hs.vG m.hg hbpArgs_nodup (by simp) m.py.1 (by decide) _ _,
    vI m.hg hbpArgs_nodup (by simp) (by decide) _ _⟩

theorem hbp_cov {s : State} (hs : Site L Wb STK s) (m : HbpOk L Wb h hl om y len) :
    Covers (hbpRd L h hl ++ hbpWr L y len) (s.rd ++ s.wr) ∧ Covers (hbpWr L y len) s.wr :=
  ⟨Covers.append_left (Covers.cons (hs.crE m.ph) Covers.nil) (Covers.right (Covers.cons (hs.cwE m.py m.wy) Covers.nil)),
    Covers.cons (hs.cwE m.py m.wy) Covers.nil⟩

theorem hbp_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : HbpOk L Wb h hl om y len)
    (hc : hintOnes (hintAt s.mem (lpa L h) (len - om)) ≤ om) :
    (hintBitPackContract PPC64LE.abi stk).pre
      (view (glueSt s (hbpArgs h hl om y len)) (hbpRd L h hl) (hbpWr L y len)) := by
  have hsp := view_glue_sp s (hbpArgs h hl om y len) (hbpRd L h hl) (hbpWr L y len)
  obtain ⟨g3, g4, g5, g6, g7⟩ := hbp_vg hs m (hbpRd L h hl) (hbpWr L y len)
  obtain ⟨l0, ll, lo, h0, lh⟩ := m.lt
  have e5 : ((view (glueSt s (hbpArgs h hl om y len)) (hbpRd L h hl) (hbpWr L y len)).gpr .r5).setWidth 32 =
      BitVec.ofNat 32 om := by
    rw [g5]; exact imm32 (by omega_arith)
  refine hbp_pre g3 g4 e5 g6 g7 (by rw [State.withRegions_rd, imm_toNat (by omega_arith)])
    (by rw [State.withRegions_wr, imm_toNat (by omega_arith)]) (by rw [hsp]; exact Nat.le_trans hstk hs.spk) ?_ ?_ ?_
    (by rw [imm_toNat (by omega_arith)]; exact hs.fitE m.ph h0) (by rw [imm_toNat (by omega_arith)]; exact hs.fitE m.py l0)
    (by rw [imm32_toNat (by omega_arith), imm_toNat (by omega_arith)]; exact m.hp)
    (by rw [imm32_toNat (by omega_arith), imm_toNat (by omega_arith)]; exact m.ho)
    (by rw [imm32_toNat (by omega_arith), imm_toNat (by omega_arith), imm_toNat (by omega_arith)]; exact m.hh)
    (by rw [imm32_toNat (by omega_arith), imm_toNat (by omega_arith), view_glue_mem]; exact hc)
  · rw [imm_toNat (by omega_arith), imm_toNat (by omega_arith)]; exact hs.dE m.d1 (.inr m.wy)
  · rw [imm_toNat (by omega_arith)]; exact hs.kE m.ph hstk hsp
  · rw [imm_toNat (by omega_arith)]; exact hs.kE m.py hstk hsp

theorem hbp_ok {c : Prog isa} (hc : Callee c (fun stk => hintBitPackContract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : HbpOk L Wb h hl om y len)
    (hcn : hintOnes (hintAt s.mem (lpa L h) (len - om)) ≤ om) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri y len, (1, 0, STK)]) s s' →
      bytesAt s'.mem (lpa L y) len = hintBitPack om (len - om) (hintAt s.mem (lpa L h) (len - om)) → Q s') :
    WP isa (callAt name c (hbpArgs h hl om y len)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := hbp_cov hs m
  obtain ⟨l0, ll, lo, h0, lh⟩ := m.lt
  refine callV hver.1 (hs.depth hc.stack hS) m.hg (hbp_preS hs (Nat.le_trans hstk hS) m hcn) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri y len] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g3, g4, g5, g6, g7⟩ := hbp_vg hs m (hbpRd L h hl) (hbpWr L y len)
  have := hbp_post hp
  rwa [g3, g5, g6, g7, view_glue_mem, State.withRegions_mem, imm32 (by omega_arith), imm32_toNat (by omega_arith),
    imm_toNat (by omega_arith)] at this

theorem hbp_tr {c : Prog isa} (hc : Callee c (fun stk => hintBitPackContract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : HbpOk L Wb h hl om y len) {P : State → State → Prop}
    (hP : ∀ x y', P x y' → Site L Wb STK x ∧ Site L Wb STK y' ∧ x.sp = y'.sp ∧
      hintOnes (hintAt x.mem (lpa L h) (len - om)) ≤ om ∧ hintOnes (hintAt y'.mem (lpa L h) (len - om)) ≤ om ∧
      (List.range hl).map (fun i => (coeffAt x.mem (lpa L h) i).toNat) =
        (List.range hl).map (fun i => (coeffAt y'.mem (lpa L h) i).toNat)) :
    RelCT isa P (callAt name c (hbpArgs h hl om y len)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨l0, ll, lo, h0, lh⟩ := m.lt
  refine callV_tr hver.1 hver.2.1 m.hg fun x y' hxy => ?_
  obtain ⟨hx, hy, hsp, cx, cy, hl'⟩ := hP x y' hxy
  obtain ⟨gx3, gx4, gx5, gx6, gx7⟩ := hbp_vg hx m (hbpRd L h hl) (hbpWr L y len)
  obtain ⟨gy3, gy4, gy5, gy6, gy7⟩ := hbp_vg hy m (hbpRd L h hl) (hbpWr L y len)
  refine ⟨hbpRd L h hl, hbpWr L y len, hbp_preS hx (Nat.le_trans hstk hS) m cx, hbp_preS hy (Nat.le_trans hstk hS) m cy,
    hbp_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4]) (by rw [gx5, gy5])
      (by rw [gx6, gy6]) (by rw [gx7, gy7]) ?_, (hbp_cov hx m).1, (hbp_cov hx m).2, (hbp_cov hy m).1,
    (hbp_cov hy m).2⟩
  rw [gx3, gy3, gx4, gy4, view_glue_mem, view_glue_mem, imm_toNat (by omega_arith)]
  exact hl'

end

end VG.Proof.MlDsa.PPC64LE.KeyGen

end

end


/-!
# ML-DSA signing on PPC64LE: the primitives, two runs, and the branches on the result

What the proofs need of the implementations of the primitives (`SPrimsOk`):
verified with at most `S` bytes of stack, and, as on 32-bit ARM
(`Proof/MlDsa/Arm/Sign/PhaseA.lean`), for the two samplers whose results the
function branches on, that the result is a function of their public data
(`RetPub`) and that they succeed only if the sampling finishes within
`maxBounds`. A call of such a sampler gives the same result in two runs
(`callVRet_tr`). Then: `ρ` is public (`pub_rho`); two runs with the same
layout (`STwo1`, `STwo2`) and the constant time of a piece without calls by
the taint analysis from the pointers.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sign

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv taint31 taint4
  Regs2 Callee CallRel glueOk glueSt glue_ok glueSt_rd glueSt_wr glue_noMem)
open VG.Impl.MlDsa.PPC64LE.KeyGen (callAt)
open VG.Impl.MlDsa.PPC64LE.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The primitives -/

/-- The result of `c` (the low word of `r3`) is the same in two runs from
states that satisfy `k.pre` and agree on `k.pub`. -/
def RetPub (k : Contract isa) (c : Prog isa) : Prop :=
  RelCT isa (fun s₁ s₂ => k.pre s₁ ∧ k.pre s₂ ∧ k.pub s₁ s₂) c
    fun s₁ s₂ => (s₁.gpr .r3).setWidth 32 = (s₂.gpr .r3).setWidth 32

/-- What the proofs need of the implementations `P` of the primitives: each
verified against its contract with at most `S` bytes of stack, and the facts
about the two samplers the function branches on. -/
structure SPrimsOk (P : Prims) (S : Nat) : Prop where
  ntt : Callee P.ntt (fun stk => nttContract PPC64LE.abi stk) S
  invNtt : Callee P.invNtt (fun stk => nttInvContract PPC64LE.abi stk) S
  mul : Callee P.mul (fun stk => mulContract PPC64LE.abi stk) S
  mulAdd : Callee P.mulAdd (fun stk => mulAddContract PPC64LE.abi stk) S
  add : Callee P.add (fun stk => addContract PPC64LE.abi stk) S
  sub : Callee P.sub (fun stk => subContract PPC64LE.abi stk) S
  rejNTT : Callee P.rejNTT (fun stk => rejNTTContract PPC64LE.abi stk) S
  expandMask : Callee P.expandMask (fun stk => expandMaskContract PPC64LE.abi stk) S
  ball : Callee P.ball (fun stk => sampleInBallContract PPC64LE.abi stk) S
  highBits : Callee P.highBits (fun stk => highBitsContract PPC64LE.abi stk) S
  lowBits : Callee P.lowBits (fun stk => lowBitsContract PPC64LE.abi stk) S
  normLt : Callee P.normLt (fun stk => normLtContract PPC64LE.abi stk) S
  makeHint : Callee P.makeHint (fun stk => makeHintContract PPC64LE.abi stk) S
  simpleBitPack : Callee P.simpleBitPack (fun stk => simpleBitPackContract PPC64LE.abi stk) S
  bitPack : Callee P.bitPack (fun stk => bitPackContract PPC64LE.abi stk) S
  bitUnpack : Callee P.bitUnpack (fun stk => bitUnpackContract PPC64LE.abi stk) S
  hintBitPack : Callee P.hintBitPack (fun stk => hintBitPackContract PPC64LE.abi stk) S
  /-- With some stack (at most `S`) it is verified with, `vg_mldsa_rej_ntt_poly`'s result depends
  only on its public data (its seed), and it succeeds only if `RejNTTPoly` finishes within
  `maxBounds`. -/
  rejX : ∃ stk, stk ≤ S ∧ Verified PPC64LE.target P.rejNTT (rejNTTContract PPC64LE.abi stk) ∧
    RetPub (rejNTTContract PPC64LE.abi stk) P.rejNTT ∧
    ∀ s t s', (rejNTTContract PPC64LE.abi stk).pre s → Exec isa P.rejNTT s t s' →
      (s'.gpr .r3).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (s.gpr .r3) 34)).isSome
  /-- Likewise, `vg_mldsa_sample_in_ball`'s result depends only on its public data (`c̃`), and it
  succeeds only if `SampleInBall` finishes within `maxBounds`. -/
  ballX : ∃ stk, stk ≤ S ∧ Verified PPC64LE.target P.ball (sampleInBallContract PPC64LE.abi stk) ∧
    RetPub (sampleInBallContract PPC64LE.abi stk) P.ball ∧
    ∀ s t s', (sampleInBallContract PPC64LE.abi stk).pre s → Exec isa P.ball s t s' →
      (s'.gpr .r3).setWidth 32 = 1 →
      (sampleInBall ((s.gpr .r5).setWidth 32).toNat maxBounds.ball
        (bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)).isSome

/-! ## Calls whose results are public -/

/-- The run of a call narrowed to the regions its contract gives it: the
same trace, and the same registers. -/
theorem narrow_run {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} {t : List Leak} {s' : State}
    (hpre : k.pre (s.withRegions rd wr)) (hc : PPC64LE.Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : PPC64LE.Covers wr s.wr)
    (he : Exec isa c s t s') : ∃ s'', Exec isa c (s.withRegions rd wr) t s'' ∧ s''.gpr = s'.gpr := by
  obtain ⟨t', s'', he', -⟩ := hv _ hpre
  have hw' := Exec.widen he' (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions, State.withRegions_self] at hw'
  obtain ⟨rfl, rfl⟩ := Exec.det he hw'
  exact ⟨_, he', rfl⟩

/-- A call of verified code whose result is public in its own runs gives the
same result in two runs whose narrowed entry states satisfy its precondition
and agree on its public data. -/
theorem RelCT.callRet {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : RetPub k c) {P : State → State → Prop} (rd wr : List Region)
    (hP : ∀ s₁ s₂, P s₁ s₂ →
      k.pre (s₁.callEntry.withRegions rd wr) ∧ k.pre (s₂.callEntry.withRegions rd wr) ∧
      k.pub (s₁.callEntry.withRegions rd wr) (s₂.callEntry.withRegions rd wr) ∧
      PPC64LE.Covers (rd ++ wr) (s₁.rd ++ s₁.wr) ∧ PPC64LE.Covers wr s₁.wr ∧
      PPC64LE.Covers (rd ++ wr) (s₂.rd ++ s₂.wr) ∧ PPC64LE.Covers wr s₂.wr) :
    RelCT isa P (.call n c) fun s₁ s₂ => (s₁.gpr .r3).setWidth 32 = (s₂.gpr .r3).setWidth 32 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨p₁, p₂, hpub, c₁, w₁, c₂, w₂⟩ := hP _ _ hp
  cases e₁ with
  | call h₁ b₁ r₁ =>
    cases e₂ with
    | call h₂ b₂ r₂ =>
      rw [call_callEntry, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      obtain ⟨n₁, x₁, g₁⟩ := narrow_run hv p₁ (by simpa using c₁) (by simpa using w₁) b₁
      obtain ⟨n₂, x₂, g₂⟩ := narrow_run hv p₂ (by simpa using c₂) (by simpa using w₂) b₂
      obtain ⟨ht, hrax⟩ := hr _ _ _ _ _ _ ⟨p₁, p₂, hpub⟩ x₁ x₂
      rw [ret_eq r₁, ret_eq r₂]
      exact ⟨by simp only [ht], show _ = _ by rw [← g₁, ← g₂]; exact hrax⟩

/-- `callV_tr`, with the result of a callee that is public (`RetPub`). -/
theorem callVRet_tr {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : RetPub k c) {as : List (Reg × Impl.MlDsa.PPC64LE.KeyGen.Arg)} (hg : glueOk as = true)
    {P : State → State → Prop}
    (hP : ∀ x y, P x y → ∃ rd wr, CallRel k rd wr x y (glueSt x as) (glueSt y as)) :
    RelCT isa P (callAt name c as) fun x y => (x.gpr .r3).setWidth 32 = (y.gpr .r3).setWidth 32 := by
  unfold callAt
  refine RelCT.seq (RelCT.wpDep (F := fun x x1 => x1 = glueSt x as) (relct_noMem (glue_noMem as))
    fun x y _ => ⟨glue_ok hg x, glue_ok hg y⟩) ?_
  refine RelCT.mono (P := fun (a b : State) => ∃ rw : List Region × List Region, ∃ x y : State,
      CallRel k rw.1 rw.2 x y a b ∧ x.rd = a.rd ∧ x.wr = a.wr ∧ y.rd = b.rd ∧ y.wr = b.wr)
    (RelCT.exists_ fun (rw : List Region × List Region) => RelCT.callRet hv hr rw.1 rw.2
      fun a b ⟨x, y, h, e1, e2, e3, e4⟩ => by
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
        exact ⟨h1, h2, h3, by rwa [← e1, ← e2], by rwa [← e2], by rwa [← e3, ← e4], by rwa [← e4]⟩) ?_
    fun _ _ h => h
  rintro a b ⟨-, x, y, hp, rfl, rfl⟩
  obtain ⟨rd, wr, h⟩ := hP x y hp
  exact ⟨(rd, wr), x, y, h, (glueSt_rd x as).symm, (glueSt_wr x as).symm, (glueSt_rd y as).symm,
    (glueSt_wr y as).symm⟩

/-! ## The samplers' calls, with their bounds -/

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {L : Lay} {Wb : List Nat} {STK : Nat}
include hP

/-- `rn_ok`, and the success of `RejNTTPoly` within `maxBounds` if the call succeeded. -/
theorem rn_okX {s : State} (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} {sd a w : Impl.MlDsa.PPC64LE.KeyGen.Ptr}
    (m : KeyGen.RnOk L Wb sd a w) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri a 1024, tri w 2048, (1, 0, STK)]) s s' →
      ((s'.gpr .r3).setWidth 32 = 1 → Reduced s'.mem (lpa L a)) →
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem (lpa L sd) 34)) ((s'.gpr .r3).setWidth 32)
        (polyAt s'.mem (lpa L a)) →
      ((s'.gpr .r3).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (lpa L sd) 34)).isSome) → Q s') :
    WP isa (callAt name P.rejNTT (KeyGen.rnArgs sd a w)) s Q := by
  obtain ⟨stk, hstk, hver, -, hmax⟩ := hP.rejX
  obtain ⟨c1, c2⟩ := KeyGen.rn_cov hs m
  have hv : ∀ s₀, (rejNTTContract PPC64LE.abi stk).pre s₀ → ∃ t s', Exec isa P.rejNTT s₀ t s' ∧
      abiPreserved s₀ s' ∧ ((rejNTTContract PPC64LE.abi stk).post s₀ s' ∧
        ((s'.gpr .r3).setWidth 32 = 1 →
          (rejNTTPoly maxBounds.rejNTT (bytesAt s₀.mem (s₀.gpr .r3) 34)).isSome)) := fun s₀ h₀ => by
    obtain ⟨t, s', e, ha, hp⟩ := hver.1 s₀ h₀
    exact ⟨t, s', e, ha, hp, hmax s₀ t s' h₀ e⟩
  refine KeyGen.callV (k := { rejNTTContract PPC64LE.abi stk with
      post := fun s₀ s' => (rejNTTContract PPC64LE.abi stk).post s₀ s' ∧
        ((s'.gpr .r3).setWidth 32 = 1 →
          (rejNTTPoly maxBounds.rejNTT (bytesAt s₀.mem (s₀.gpr .r3) 34)).isSome) }) hv
    (hs.depth hP.rejNTT.stack hS) m.hg (KeyGen.rn_preS hs (Nat.le_trans hstk hS) m) c1 c2
    fun s' hk ⟨hp, hx⟩ => hQ s' (hs.keptW [tri a 1024, tri w 2048] (Nat.le_trans hP.rejNTT.stack hS) hk) ?_ ?_ ?_
  all_goals
    obtain ⟨g3, g4, -⟩ := KeyGen.rn_vg hs m (KeyGen.rnRd L sd) (KeyGen.rnWr L a w)
    have := KeyGen.rejNtt_post hp
    rw [State.withRegions_mem, State.withRegions_gpr, g3, g4, KeyGen.view_glue_mem] at this
    rw [g3, KeyGen.view_glue_mem, State.withRegions_gpr] at hx
  exacts [this.1, this.2, hx]

/-- `ball_ok`, and the success of `SampleInBall` within `maxBounds` if the call succeeded. -/
theorem ball_okX {s : State} (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String}
    {ct c w : Impl.MlDsa.PPC64LE.KeyGen.Ptr} {len tau : Nat} (m : KeyGen.BallOk L Wb ct len tau c w)
    {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri c 1024, tri w 2048, (1, 0, STK)]) s s' →
      ((s'.gpr .r3).setWidth 32 = 1 → Reduced s'.mem (lpa L c)) →
      Outcome (fun b => (sampleInBall tau b.ball (bytesAt s.mem (lpa L ct) len)).map toRq)
        ((s'.gpr .r3).setWidth 32) (polyAt s'.mem (lpa L c)) →
      ((s'.gpr .r3).setWidth 32 = 1 → (sampleInBall tau maxBounds.ball (bytesAt s.mem (lpa L ct) len)).isSome) →
      Q s') :
    WP isa (callAt name P.ball (KeyGen.ballArgs ct len tau c w)) s Q := by
  obtain ⟨stk, hstk, hver, -, hmax⟩ := hP.ballX
  obtain ⟨c1, c2⟩ := KeyGen.ball_cov hs m
  obtain ⟨l0, ll, lt⟩ := m.lt
  have hv : ∀ s₀, (sampleInBallContract PPC64LE.abi stk).pre s₀ → ∃ t s', Exec isa P.ball s₀ t s' ∧
      abiPreserved s₀ s' ∧ ((sampleInBallContract PPC64LE.abi stk).post s₀ s' ∧
        ((s'.gpr .r3).setWidth 32 = 1 → (sampleInBall ((s₀.gpr .r5).setWidth 32).toNat maxBounds.ball
          (bytesAt s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat)).isSome)) := fun s₀ h₀ => by
    obtain ⟨t, s', e, ha, hp⟩ := hver.1 s₀ h₀
    exact ⟨t, s', e, ha, hp, hmax s₀ t s' h₀ e⟩
  refine KeyGen.callV (k := { sampleInBallContract PPC64LE.abi stk with
      post := fun s₀ s' => (sampleInBallContract PPC64LE.abi stk).post s₀ s' ∧
        ((s'.gpr .r3).setWidth 32 = 1 → (sampleInBall ((s₀.gpr .r5).setWidth 32).toNat maxBounds.ball
          (bytesAt s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat)).isSome) }) hv
    (hs.depth hP.ball.stack hS) m.hg (KeyGen.ball_preS hs (Nat.le_trans hstk hS) m) c1 c2
    fun s' hk ⟨hp, hx⟩ => hQ s' (hs.keptW [tri c 1024, tri w 2048] (Nat.le_trans hP.ball.stack hS) hk) ?_ ?_ ?_
  all_goals
    obtain ⟨g3, g4, g5, g6, -⟩ := KeyGen.ball_vg hs m (KeyGen.ballRd L ct len) (KeyGen.ballWr L c w)
    have := KeyGen.ball_post hp
    rw [State.withRegions_mem, State.withRegions_gpr, g3, g4, g5, g6, KeyGen.view_glue_mem,
      KeyGen.imm32 (by omega_arith), KeyGen.imm32_toNat (by omega_arith), KeyGen.imm_toNat (by omega_arith)] at this
    rw [g3, g4, g5, KeyGen.view_glue_mem, State.withRegions_gpr, KeyGen.imm32 (by omega_arith), KeyGen.imm32_toNat (by omega_arith),
      KeyGen.imm_toNat (by omega_arith)] at hx
  exacts [this.1, this.2, hx]

theorem rn_trRet (hS : S ≤ STK) {name : String} {sd a w : Impl.MlDsa.PPC64LE.KeyGen.Ptr}
    (m : KeyGen.RnOk L Wb sd a w) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧
      bytesAt x.mem (lpa L sd) 34 = bytesAt y.mem (lpa L sd) 34) :
    RelCT isa Q (callAt name P.rejNTT (KeyGen.rnArgs sd a w))
      fun x y => (x.gpr .r3).setWidth 32 = (y.gpr .r3).setWidth 32 := by
  obtain ⟨stk, hstk, hver, hret, -⟩ := hP.rejX
  refine callVRet_tr hver.1 hret m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, hl⟩ := hQ x y hxy
  obtain ⟨gx3, gx4, gx5⟩ := KeyGen.rn_vg hx m (KeyGen.rnRd L sd) (KeyGen.rnWr L a w)
  obtain ⟨gy3, gy4, gy5⟩ := KeyGen.rn_vg hy m (KeyGen.rnRd L sd) (KeyGen.rnWr L a w)
  refine ⟨KeyGen.rnRd L sd, KeyGen.rnWr L a w, KeyGen.rn_preS hx (Nat.le_trans hstk hS) m,
    KeyGen.rn_preS hy (Nat.le_trans hstk hS) m,
    KeyGen.rejNtt_pub (by rw [KeyGen.view_glue_sp, KeyGen.view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4])
      (by rw [gx5, gy5]) ?_, (KeyGen.rn_cov hx m).1, (KeyGen.rn_cov hx m).2, (KeyGen.rn_cov hy m).1,
    (KeyGen.rn_cov hy m).2⟩
  rw [gx3, gy3, KeyGen.view_glue_mem, KeyGen.view_glue_mem]
  exact hl

theorem ball_trRet (hS : S ≤ STK) {name : String} {ct c w : Impl.MlDsa.PPC64LE.KeyGen.Ptr} {len tau : Nat}
    (m : KeyGen.BallOk L Wb ct len tau c w) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧
      bytesAt x.mem (lpa L ct) len = bytesAt y.mem (lpa L ct) len) :
    RelCT isa Q (callAt name P.ball (KeyGen.ballArgs ct len tau c w))
      fun x y => (x.gpr .r3).setWidth 32 = (y.gpr .r3).setWidth 32 := by
  obtain ⟨stk, hstk, hver, hret, -⟩ := hP.ballX
  obtain ⟨l0, ll, lt⟩ := m.lt
  refine callVRet_tr hver.1 hret m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, hl⟩ := hQ x y hxy
  obtain ⟨gx3, gx4, gx5, gx6, gx7⟩ := KeyGen.ball_vg hx m (KeyGen.ballRd L ct len) (KeyGen.ballWr L c w)
  obtain ⟨gy3, gy4, gy5, gy6, gy7⟩ := KeyGen.ball_vg hy m (KeyGen.ballRd L ct len) (KeyGen.ballWr L c w)
  refine ⟨KeyGen.ballRd L ct len, KeyGen.ballWr L c w, KeyGen.ball_preS hx (Nat.le_trans hstk hS) m,
    KeyGen.ball_preS hy (Nat.le_trans hstk hS) m,
    KeyGen.ball_pub (by rw [KeyGen.view_glue_sp, KeyGen.view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4])
      (by rw [gx5, gy5]) (by rw [gx6, gy6]) (by rw [gx7, gy7]) ?_, (KeyGen.ball_cov hx m).1, (KeyGen.ball_cov hx m).2,
    (KeyGen.ball_cov hy m).1, (KeyGen.ball_cov hy m).2⟩
  rw [gx3, gy3, gx4, gy4, KeyGen.view_glue_mem, KeyGen.view_glue_mem, KeyGen.imm_toNat (by omega_arith)]
  exact hl

end

/-! ## Two runs related by more than their entry states -/

/-- Two runs, each satisfying `I` from its entry state, related by `E`. -/
def RR (p : Params) (STK : Nat) (I E : State → State → Prop) (x y : State) : Prop :=
  Rel2 (SPre p STK) (sPub p) I x y ∧ E x y

theorem WP.conj {c : Prog isa} {s : State} {Q₁ Q₂ : State → Prop} (h₁ : WP isa c s Q₁) (h₂ : WP isa c s Q₂) :
    WP isa c s fun s' => Q₁ s' ∧ Q₂ s' := by
  obtain ⟨t, s', e, q₁⟩ := h₁
  obtain ⟨_, _, e', q₂⟩ := h₂
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact ⟨t, _, e, q₁, q₂⟩

/-- A piece that takes each run from `I` to `J` and from `s` to `s'` with
`F s s'`, and leaks the same from runs related by `RR I E`, with `Q₀` of the
final states. -/
theorem stepRR {p : Params} {STK : Nat} {I J E E' Q₀ F : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, SPre p STK σ → I σ s → WP isa c s fun s' => J σ s' ∧ F s s')
    (ht : RelCT isa (RR p STK I E) c Q₀)
    (hE : ∀ x y x' y', RR p STK I E x y → F x x' → F y y' → Q₀ x' y' → E' x' y') :
    RelCT isa (RR p STK I E) c (RR p STK J E') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', hq⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, he⟩ := hr
  obtain ⟨_, u₁, f₁, g₁, k₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂, k₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', ⟨σ₁, σ₂, p₁, p₂, hpub, g₁, g₂⟩, hE _ _ _ _ ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, he⟩ k₁ k₂ hq⟩

/-! ## `ρ` -/

theorem signLeak_head (p : Params) (sk μ rnd : List Byte) :
    ∃ X, signLeak p sk μ rnd = leakBytes (sk.take 32) ++ X := by
  unfold signLeak
  rcases e : skDecode p sk with ⟨ρ, K, tr, s₁, s₂, t₀⟩
  have hρ : ρ = sk.take 32 := by rw [← Proof.MlDsa.Sign.skRho_eq p sk, e]
  subst hρ
  exact ⟨_, rfl⟩

theorem leak_rho {p : Params} {sk₁ sk₂ μ₁ μ₂ r₁ r₂ : List Byte} (h1 : sk₁.length = p.skLen)
    (h2 : sk₂.length = p.skLen) (h : signLeak p sk₁ μ₁ r₁ = signLeak p sk₂ μ₂ r₂) :
    sk₁.take 32 = sk₂.take 32 := by
  obtain ⟨X₁, e₁⟩ := signLeak_head p sk₁ μ₁ r₁
  obtain ⟨X₂, e₂⟩ := signLeak_head p sk₂ μ₂ r₂
  rw [e₁, e₂] at h
  refine Proof.MlDsa.Sign.leakBytes_inj (List.append_inj h ?_).1
  rw [Proof.MlDsa.Sign.leakBytes_length, Proof.MlDsa.Sign.leakBytes_length, List.length_take, List.length_take, h1, h2]

theorem pub_rho {p : Params} {σ₁ σ₂ : State} (h : sPub p σ₁ σ₂) : (skOf p σ₁).take 32 = (skOf p σ₂).take 32 :=
  leak_rho (Proof.MlKem.bytesAt_length _ _ _) (Proof.MlKem.bytesAt_length _ _ _) h.2.2.2.2.2.2

/-! ## The state, but for `r3` and `r24` -/

theorem SC1.regs2 {p : Params} {STK : Nat} {σ s s' : State} (h : SC1 p STK σ s) (hr : Regs2 s s') :
    SC1 p STK σ s' :=
  ⟨h.site.regs2 hr, hr.rd.trans h.rd, hr.wr.trans h.wr, hr.sp.trans h.sp,
    fun r hp hs => by
      have : r ≠ .r3 ∧ r ≠ .r24 := ⟨fun e => by subst e; simp [preserved] at hp,
        fun e => by subst e; simp [savedTop] at hs⟩
      rw [hr.gpr r this.1 this.2]; exact h.pres r hp hs,
    by rw [hr.mem]; exact h.sav, by rw [hr.mem]; exact h.sig, by rw [hr.mem]; exact h.sk, by rw [hr.mem]; exact h.mu,
    by rw [hr.mem]; exact h.rnd⟩

theorem SC2.regs2 {p : Params} {STK : Nat} {σ s s' : State} (h : SC2 p STK σ s) (hr : Regs2 s s') :
    SC2 p STK σ s' :=
  ⟨h.site.regs2 hr, hr.rd.trans h.rd, hr.wr.trans h.wr, hr.sp.trans h.sp,
    fun r hp hs => by
      have : r ≠ .r3 ∧ r ≠ .r24 := ⟨fun e => by subst e; simp [preserved] at hp,
        fun e => by subst e; simp [savedTop] at hs⟩
      rw [hr.gpr r this.1 this.2]; exact h.pres r hp hs,
    by rw [hr.mem]; exact h.sav, by rw [hr.mem]; exact h.sk, by rw [hr.mem]; exact h.mu⟩

/-! ## Two runs -/

section
variable {p : Params} {STK : Nat}

theorem sc1_twoL {σ₁ σ₂ x y : State} (pub : sPub p σ₁ σ₂) (h₁ : SC1 p STK σ₁ x) (h₂ : SC1 p STK σ₂ y) :
    Two (slay1 p STK σ₁) sWb1 STK x y :=
  ⟨h₁.site, slay1_pub pub ▸ h₂.site, by rw [h₁.sp, h₂.sp, pub.1]⟩

theorem sc2_twoL {σ₁ σ₂ x y : State} (pub : sPub p σ₁ σ₂) (h₁ : SC2 p STK σ₁ x) (h₂ : SC2 p STK σ₂ y) :
    Two (slay2 p STK σ₁) sWb2 STK x y :=
  ⟨h₁.site, slay2_pub pub ▸ h₂.site, by rw [h₁.sp, h₂.sp, pub.1]⟩

/-- A piece without calls before the hash of `ρ″`, checked by the taint
analysis from `scratch`. -/
theorem srel1 {I : State → State → Prop} (hI : ∀ σ s, I σ s → SC1 p STK σ s)
    {c : Prog isa} {hc : VG.Taint.Hint VG.PPC64LE.taint.T}
    (h : (VG.PPC64LE.taint.check (Taint.ofRegs [.r31]) c hc).isSome = true) :
    RelCT isa (Rel2 (SPre p STK) (sPub p) I) c fun _ _ => True :=
  rel_of (RelCT.exists_ fun _ => taint31 (fun _ _ h => h) h)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc1_twoL pub (hI _ _ h₁) (hI _ _ h₂)⟩

/-- A piece without calls after the hash of `ρ″`, checked by the taint
analysis from `scratch`. -/
theorem srel2 {I : State → State → Prop} (hI : ∀ σ s, I σ s → SC2 p STK σ s)
    {c : Prog isa} {hc : VG.Taint.Hint VG.PPC64LE.taint.T}
    (h : (VG.PPC64LE.taint.check (Taint.ofRegs [.r31]) c hc).isSome = true) :
    RelCT isa (Rel2 (SPre p STK) (sPub p) I) c fun _ _ => True :=
  rel_of (RelCT.exists_ fun _ => taint31 (fun _ _ h => h) h)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub (hI _ _ h₁) (hI _ _ h₂)⟩

/-- `srel1`, from all the pointers. -/
theorem srel1p {I : State → State → Prop} (hI : ∀ σ s, I σ s → SC1 p STK σ s)
    {c : Prog isa} {hc : VG.Taint.Hint VG.PPC64LE.taint.T}
    (h : (VG.PPC64LE.taint.check (Taint.ofRegs [.r28, .r29, .r30, .r31]) c hc).isSome = true) :
    RelCT isa (Rel2 (SPre p STK) (sPub p) I) c fun _ _ => True :=
  rel_of (RelCT.exists_ fun _ => taint4 (fun _ _ h => h) h)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc1_twoL pub (hI _ _ h₁) (hI _ _ h₂)⟩

/-- `srel2`, from all the pointers. -/
theorem srel2p {I : State → State → Prop} (hI : ∀ σ s, I σ s → SC2 p STK σ s)
    {c : Prog isa} {hc : VG.Taint.Hint VG.PPC64LE.taint.T}
    (h : (VG.PPC64LE.taint.check (Taint.ofRegs [.r28, .r29, .r30, .r31]) c hc).isSome = true) :
    RelCT isa (Rel2 (SPre p STK) (sPub p) I) c fun _ _ => True :=
  rel_of (RelCT.exists_ fun _ => taint4 (fun _ _ h => h) h)
    fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, sc2_twoL pub (hI _ _ h₁) (hI _ _ h₂)⟩

end

end VG.Proof.MlDsa.PPC64LE.Sign
