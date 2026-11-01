module

public import VerifiedGarbage.Proof.Ed448.RISCV64.BaseStep
public import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.X448.RISCV64.Freeze
import VerifiedGarbage.Proof.X448.RISCV64.Invert
import VerifiedGarbage.Proof.X448.Invert
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.X25519.RISCV64.Mul
import VerifiedGarbage.Proof.X25519.RISCV64.Pass
import VerifiedGarbage.Proof.X448.RISCV64.R64.Invert
public import VerifiedGarbage.Proof.X448.RISCV64.Slots

/-!
# Ed448 on RISCV64: the encoding of `R`

`baseEncode` writes the encoding of the point in `R` to `out`
(`baseEncode_ok`): `1/Z` by X448's `invert`, `x = X/Z` fully reduced into
`out` for its low bit, then `y = Y/Z` over it, and the bit at the top of the
57th byte (`encodePoint_code`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (ACC X2 Z2 R Y freeze)
open VG.Spec.X448 (Fe P)
open VG.Spec.Ed448 (Point)

section
variable {b : Addr}

/-- The slots below `Y` stay through `freeze`. -/
theorem slots_freeze {m m' : Mem} {o : Addr}
    (hf : Frame [⟨b + BitVec.ofNat 64 Y, 56⟩, ⟨o, 56⟩] m m') (hd : Region.Disjoint ⟨b, 2048⟩ ⟨o, 56⟩)
    {qs : List Nat} {v : Nat → Fe} (hS : SlotsOk m b qs v) (hq : (qs.all fun q => q + 56 ≤ Y) = true) :
    SlotsOk m' b qs v := by
  intro q hq'
  have h := List.all_eq_true.mp hq q hq'
  simp only [decide_eq_true_eq] at h
  have hY : Y = 896 := rfl
  have e := limb_frame (o := q) hf fun r hr k hk => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (.inl (by omega_using [h, hk])) (by omega_using [h, hk, hY]) (by omega_using [hY])
    · exact hd.sub_left (Offset.sub_base _ (by omega_using [h, hY, hk]))
  rw [FS, V, val32_congr e]; exact hS q hq'

/-- The slots of the encoding. -/
def EQ : List Nat := [R, RX, RY, RZ]

theorem low_bit (x : Nat) :
    (BitVec.ofNat 64 (BitVec.ofNat 8 x).toNat &&& BitVec.ofNat 64 1) <<< 7 =
      BitVec.ofNat 64 (128 * (x % 2)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.and_one_is_mod, Nat.shiftLeft_eq]
  omega_arith

theorem byte0 {m : Mem} {o : Addr} {x : Nat} (h : VG.Spec.X448.bytesAt m o 56 = Proof.X25519.leBytes 56 x) :
    m o = BitVec.ofNat 8 x := by
  have e := congrArg List.head? h
  rw [show (56 : Nat) = 0 + 1 + 55 from rfl, Proof.X25519.leBytes_add, Proof.X25519.leBytes_add] at e
  simp only [VG.Spec.X448.bytesAt, Proof.X25519.leBytes, List.range_succ, List.range_zero] at e
  simpa using e

theorem baseEncode_ok {s : State} (hc : Ctx b s) {o : Addr} (h3 : s.gpr .a0 = o)
    (hout : (⟨o, 57⟩ : Region) ∈ s.wr) (hdisj : Region.Disjoint ⟨b, 2048⟩ ⟨o, 57⟩) {p : Point}
    (hS : SlotsOk s.mem b RQ (ptV p p)) :
    WP isa baseEncode s fun s' => Spec.Ed448.bytesAt s'.mem o 57 = Spec.Ed448.encodePoint p := by
  have hd56 : Region.Disjoint ⟨b, 2048⟩ ⟨o, 56⟩ := hdisj.sub_right (Region.sub_prefix (by decide))
  have hv : ∀ q ∈ EQ, q ≠ R → FS s.mem b q = ptV p p q := fun q hq hqR => hS q (by
    simp only [EQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact absurd rfl hqR
    all_goals decide)
  unfold baseEncode
  refine WP.seq (WP.mono (R64.invertQ_ok (qs := EQ) (by decide) (by decide) (by decide) hc hv rfl)
    fun s1 ⟨hst1, hc1, hS1⟩ => ?_)
  refine WP.seq (WP.mono (R64.mulS (o := X2) (x := RX) (y := R) (by decide) (by decide) (by decide)
    (by decide) hc1 hS1) fun s2 ⟨hr2, _, hS2⟩ => ?_)
  have hr2' : Rest R64.work s s2 := hst1.rest.trans (hr2.mono (by decide))
  have hc2 : Ctx b s2 := hc1.of_rest hr2 (by decide)
  have h32 : s2.gpr .a0 = o := by rw [hr2'.gpr _ (by decide), h3]
  refine WP.seq (WP.append (freeze_ok hc2 h32
    (fun k hk => in_base (len := 57) (by rw [hr2'.wr]; exact hout) (by omega_arith) (by omega_arith)) hd56)
    fun s3 ⟨hb3, hr3, hf3, _⟩ => ?_)
  have hS3 := slots_freeze hf3 hd56 hS2 (by decide)
  have h33 : s3.gpr .a0 = o := by rw [hr3.gpr _ (by decide), h32]
  have hw3 : s3.wr = s.wr := by rw [hr3.wr, hr2'.wr]
  refine wp_lbz (a := o) (by decide) (by rw [h33, BitVec.add_zero])
    (by have := in_base (P := o) (d := 0) (n := 1) (List.mem_append_right s3.rd (hw3 ▸ hout)) (by decide)
          (by decide)
        rwa [BitVec.add_zero] at this) fun s4 u4 => ?_
  refine wp_li (by decide) fun s5 u5 => wp_and fun s6 u6 => wp_sll (by decide) fun s7 u7 => WP.block_nil ?_
  -- `x` and its low bit.
  have ex : FS s2.mem b X2 = p.X * VG.Proof.X448.pw p.Z (P - 2) := by
    rw [hS2 X2 (by decide)]
    simp only [upd, ptV, RX, RY, RZ, X2, Z2, R, Nat.reduceEqDiff, ↓reduceIte]
  have e12 : s7.gpr .t1 = BitVec.ofNat 64 (128 * ((p.X * VG.Proof.X448.pw p.Z (P - 2)).val % 2)) := by
    rw [u7.gpr, u6.gpr, u5.gpr, u5.other _ (by decide), u4.gpr, byte0 hb3, ← low_bit]
    congr 4
    rw [← ex]; rfl
  have hr7 : Rest [.a6, .t1] s3 s7 :=
    (u4.rest (by decide)).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans (u7.rest (by decide))))
  have hm7 : s7.mem = s3.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem]
  have hc7 : Ctx b s7 := (hc2.of_rest hr3 (by decide)).of_rest hr7 (by decide)
  have hS7 := hS3
  rw [← hm7] at hS7
  -- `y`.
  refine WP.seq (WP.mono (R64.mulS (o := X2) (x := RY) (y := R) (by decide) (by decide) (by decide)
    (by decide) hc7 hS7) fun s8 ⟨hr8, _, hS8⟩ => ?_)
  have hc8 : Ctx b s8 := hc7.of_rest hr8 (by decide)
  have h38 : s8.gpr .a0 = o := by rw [hr8.gpr _ (by decide), hr7.gpr _ (by decide), h33]
  have hw8 : s8.wr = s.wr := by rw [hr8.wr, hr7.wr, hw3]
  refine WP.append (freeze_ok hc8 h38
    (fun k hk => in_base (len := 57) (by rw [hw8]; exact hout) (by omega_arith) (by omega_arith)) hd56)
    fun s9 ⟨hb9, hr9, _, _⟩ => ?_
  refine wp_sb (a := o + BitVec.ofNat 64 56) (by decide)
    (by rw [hr9.gpr _ (by decide), h38])
    (by rw [hr9.wr, hw8]; exact in_base hout (by decide) (by decide)) fun s10 u10 => WP.block_nil ?_
  have ey : FS s8.mem b X2 = p.Y * VG.Proof.X448.pw p.Z (P - 2) := by
    rw [hS8 X2 (by decide)]
    simp only [upd, ptV, RX, RY, RZ, X2, Z2, R, Nat.reduceEqDiff, ↓reduceIte]
  have hm10 : s10.mem = s9.mem.writeW (o + BitVec.ofNat 64 56) ((s9.gpr .t1).setWidth 8) := u10.mem
  have e12' : s9.gpr .t1 = s7.gpr .t1 := by rw [hr9.gpr _ (by decide), hr8.gpr _ (by decide)]
  -- The bytes.
  obtain ⟨X, Y', Z⟩ := p
  rw [Proof.Ed448.encodePoint_code, Proof.X448.invert_eq, Proof.X448.pow_pw,
    show (57 : Nat) = 56 + 1 from rfl, Proof.Ed448.bytesAt_eq, Proof.X25519.bytesAt_add]
  refine (congrArg (· ++ Spec.X25519.bytesAt s10.mem (o + BitVec.ofNat 64 56) 1) ?_).trans
    (congrArg (Proof.X25519.leBytes 56 (Y' * VG.Proof.X448.pw Z (P - 2)).val ++ ·) ?_)
  · have f : Frame [⟨o + BitVec.ofNat 64 56, 1⟩] s9.mem s10.mem := by
      rw [hm10]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ (8 / 8))
    have e : Spec.X25519.bytesAt s10.mem o 56 = Spec.X25519.bytesAt s9.mem o 56 := by
      simp only [Spec.X25519.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      have hi := List.mem_range.mp hi
      exact f _ fun r hr hc => by
        rw [List.mem_singleton.mp hr] at hc
        exact Offset.disjoint o (d := i) (n := 1) (e := 56) (k := 1) (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
          _ (Region.contains_self _ _) hc
    rw [e]
    refine hb9.trans (congrArg (Proof.X25519.leBytes 56) ?_)
    rw [← VG.Proof.X448.toFe_val, ← ey]; rfl
  · show [s10.mem (o + BitVec.ofNat 64 56 + BitVec.ofNat 64 0)] = _
    rw [hm10, BitVec.add_zero, VG.WriteBytes.writeW8_apply, ite_eq_left (by simp), e12', e12]
    exact congrArg (· :: []) (stb_byte (toNat_imm (by omega_arith)))

end

end VG.Proof.Ed448.RISCV64
