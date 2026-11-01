module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.BitPack
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.BitPack
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.SimpleBitPack
meta import VerifiedGarbage.Proof.MlDsa.Pack.Arith
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream

/-!
# ML-DSA on PPC64LE: `vg_mldsa_bit_unpack` and `vg_mldsa_unpack_t1`

The coefficient of a field `y` is `b - y` modulo `q` (`buFin`, as `bm`
computes it, with `b` in `r4` and `q` in `r7`), or `y · 2¹³` (`t1Fin`). The
loop is proven once for every width (`unpackLoop_ok`); `unpackLoop_buFin_ok`
states what the loop of `buFin` does for any state, which
`vg_mldsa_bit_unpack` (by its five cases) and `vg_mldsa_expand_mask_poly`
use, and `unpackLoop_ct18` and `unpackLoop_ct20` that it is constant time,
for ExpandMask.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Pack

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack

/-! ## The coefficients -/

/-- The word `buFin` stores for the field `y`, for `b = B`. -/
abbrev buWord (B y : Nat) : BitVec 32 := (bm (BitVec.ofNat 64 B) (BitVec.ofNat 64 y)).setWidth 32

theorem buFin_ok (B d : Nat) : FinOk buFin d (buWord B) (RB B) := fun j s hR hj hout _ => by
  unfold buFin
  rw [WP.block_append_iff]
  refine WP.mono (bMinus_ok hR) fun s₁ ⟨⟨g₁, m₁⟩, k₁⟩ =>
    wp_stw (by decide) hj (by rw [k₁.gpr (by decide)]) (by rw [k₁.2.2]; exact hout) fun s₂ m₂ =>
      wp_nil ⟨?_, (k₁.trans (rs' := []) ⟨fun r _ => by rw [m₂.gpr], m₂.rd, m₂.wr⟩).mono (by decide)⟩
  rw [m₂.mem, m₁, g₁]
  simp only [buWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The word `t1Fin` stores for the field `y`. -/
abbrev t1Word (y : Nat) : BitVec 32 := (BitVec.ofNat 64 y <<< 13).setWidth 32

theorem t1Fin_ok : FinOk t1Fin 10 t1Word fun _ => True := fun j s _ hj hout _ => by
  refine WP.keep _ ?_ rfl rfl
  unfold t1Fin
  refine wp_lsl (by decide) fun s₁ u₁ =>
    wp_stw (by decide) hj (by rw [u₁.other _ (by decide)]) (by rw [u₁.wr]; exact hout) fun s₂ m₂ =>
      wp_nil ?_
  rw [m₂.mem, u₁.mem, u₁.gpr]
  simp only [t1Word, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- A field of `d ≤ 20` bits of the input. -/
theorem field_lt (X d k : Nat) (hd : d ≤ 20) : X / 2 ^ (d * k) % 2 ^ d < 2 ^ 20 :=
  Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos d)) (Nat.pow_le_pow_right (by decide) hd)

/-! ## The loop of `BitUnpack`, for any state

`unpackLoop buFin d c nb` for `BitUnpack(v, a, B)` with `bitlen (a + B) = d`
(ExpandMask runs it for `(B, d, c, nb)` = `(2¹⁷, 18, 4, 9)` and
`(2¹⁹, 20, 2, 5)`, with `a = B - 1`), from any state with `B` in `r4`, `q` in
`r7` (`RB B`), and in `r10` the address of `32 d` readable bytes and in `r11`
that of a writable polynomial, disjoint: it writes `BitUnpack` of the bytes to
the polynomial, reduced, and changes nothing else but the registers
`loopRegs`.
-/

theorem unpackLoop_buFin_ok {B d c nb : Nat} (hs : Shape d c nb) (hB19 : B ≤ 2 ^ 19) {a : Nat}
    (hd : bitlen (a + B) = d) {s : State} (hR : RB B s)
    (hin : (⟨s.gpr .r10, 32 * d⟩ : Region) ∈ s.rd ++ s.wr) (hout : polyRegion (s.gpr .r11) ∈ s.wr)
    (hsep : Region.Disjoint ⟨s.gpr .r10, 32 * d⟩ (polyRegion (s.gpr .r11))) :
    WP isa (unpackLoop buFin d c nb) s fun s' =>
      PolyIs s'.mem (s.gpr .r11) (toRq (bitUnpack (bytesAt s.mem (s.gpr .r10) (32 * d)) a B)) ∧
        Frame [polyRegion (s.gpr .r11)] s.mem s'.mem ∧ Keep loopRegs s s' := by
  refine WP.mono (unpackLoop_ok (buFin_ok B d) (RB_stable B) hs (sE := s) hR hin hout hsep rfl rfl rfl rfl rfl
    (Keep.refl _ _)) fun s' ⟨hc, hf, hk⟩ => ⟨?_, hf, hk⟩
  have hq := q_eq
  refine polyIs_of_toNat fun i hi => ?_
  have hy := field_lt (inNum s.mem (s.gpr .r10) d) d i hs.d20
  have hy' := hy
  unfold inNum at hy'
  have hbm := bm_toNat (b := BitVec.ofNat 64 B)
    (x := BitVec.ofNat 64 (inNum s.mem (s.gpr .r10) d / 2 ^ (d * i) % 2 ^ d))
    (by rw [BitVec.toNat_ofNat]; omega_arith) (by rw [BitVec.toNat_ofNat]; omega_arith)
  rw [hc i hi, buWord, BitVec.toNat_setWidth, hbm, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show B < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show _ < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show (B + q - inNum s.mem (s.gpr .r10) d / 2 ^ (d * i) % 2 ^ d) % q < 2 ^ 32 from
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega_arith)) (by omega_arith)),
    toRq, Vector.getElem_map, bitUnpack_get _ _ _ hi, hd, ofInt_sub (by omega_arith)]

/-- The loop of `BitUnpack` for `γ₁ = 2¹⁷` is constant time, with `r10` and
`r11` public. -/
theorem unpackLoop_ct18 {P : State → State → Prop}
    (hP : ∀ a b, P a b → a.sp = b.sp ∧ a.gpr .r10 = b.gpr .r10 ∧ a.gpr .r11 = b.gpr .r11) :
    RelCT isa P (unpackLoop buFin 18 4 9) fun _ _ => True :=
  RelCT.taint (A := VG.PPC64LE.taint) (Taint.ofRegs [.r10, .r11]) (fun a b h => ⟨(hP a b h).1, fun x hx => by
    rw [Taint.mem_ofRegs] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    exacts [(hP a b h).2.1, (hP a b h).2.2]⟩) (by taint_decide)

/-- The loop of `BitUnpack` for `γ₁ = 2¹⁹` is constant time, with `r10` and
`r11` public. -/
theorem unpackLoop_ct20 {P : State → State → Prop}
    (hP : ∀ a b, P a b → a.sp = b.sp ∧ a.gpr .r10 = b.gpr .r10 ∧ a.gpr .r11 = b.gpr .r11) :
    RelCT isa P (unpackLoop buFin 20 2 5) fun _ _ => True :=
  RelCT.taint (A := VG.PPC64LE.taint) (Taint.ofRegs [.r10, .r11]) (fun a b h => ⟨(hP a b h).1, fun x hx => by
    rw [Taint.mem_ofRegs] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    exacts [(hP a b h).2.1, (hP a b h).2.2]⟩) (by taint_decide)

/-! ## `vg_mldsa_bit_unpack` -/

/-- What `bitUnpack` leaves. -/
def BuPost (s₀ s' : State) : Prop :=
  PolyIs s'.mem (s₀.gpr .r7)
    (toRq (bitUnpack (bytesAt s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat) (lo s₀ .r5) (lo s₀ .r6)))

theorem bu_wp {s₀ : State} (hp : BuPre s₀) : WP isa Impl.MlDsa.PPC64LE.Pack.bitUnpack s₀ (BuPost s₀) := by
  unfold Impl.MlDsa.PPC64LE.Pack.bitUnpack
  refine WP.seq (WP.mono (mov2Q_ok (a := .r3) (b := .r7) (by decide) (by decide) (by decide) s₀)
    fun s₁ ⟨⟨g10, g11, g7, m₁⟩, k₁⟩ => ?_)
  have ab := mem_bitPackParams hp.ab
  have go : ∀ {d c nb B : Nat}, Shape d c nb → lo s₀ .r6 = B → B ≤ 2 ^ 19 →
      loadBVal B = BitVec.ofNat 64 B → bitlen (lo s₀ .r5 + B) = d → ∀ s : State, Same s₁ s →
      WP isa (withB B (unpackLoop buFin d c nb)) s (BuPost s₀) := by
    intro d c nb B hs hB hB19 hBl hd s hS
    have hlen := hp.len
    rw [hB, hd] at hlen
    refine WP.seq (WP.mono (loadB_ok .r4 hBl s) fun s₂ ⟨⟨g4, m₂⟩, k₂⟩ => ?_)
    have x10 : s₂.gpr .r10 = s₀.gpr .r3 := by rw [k₂.gpr (by decide), hS.1.gpr (by decide), g10]
    have x11 : s₂.gpr .r11 = s₀.gpr .r7 := by rw [k₂.gpr (by decide), hS.1.gpr (by decide), g11]
    have xrd : s₂.rd = s₀.rd := by rw [k₂.2.1, hS.1.2.1, k₁.2.1]
    have xwr : s₂.wr = s₀.wr := by rw [k₂.2.2, hS.1.2.2, k₁.2.2]
    have xm : s₂.mem = s₀.mem := by rw [m₂, hS.2, m₁]
    refine WP.mono (unpackLoop_buFin_ok (s := s₂) hs hB19 hd
      ⟨g4, by rw [k₂.gpr (by decide), hS.1.gpr (by decide), g7]⟩
      (by rw [x10, xrd, hp.rd, ← hlen]; exact List.mem_append_left _ (List.mem_singleton_self _))
      (by rw [x11, xwr, hp.wr]; exact List.mem_singleton_self _)
      (by rw [x10, x11, ← hlen]; exact hp.disj))
      fun s₃ ⟨hpoly, _, _⟩ => ?_
    rw [x11, x10, xm, ← hB, ← hlen] at hpoly
    exact hpoly
  refine sel_ok .r6 (by decide) 2 (by decide) (by decide) _ _ s₁ (fun s₂ h₂ e => ?_) (fun s₂ h₂ n2 => ?_)
  · have e6 : lo s₁ .r6 = lo s₀ .r6 := by simp only [lo]; rw [k₁.gpr (by decide)]
    rw [e6] at e
    exact go (d := 3) (c := 8) (nb := 3) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show lo s₀ .r5 = 2 by omega_arith]; decide) s₂ h₂
  have e6 : ∀ s, Same s₁ s → lo s .r6 = lo s₀ .r6 := fun s h => by
    simp only [lo]; rw [h.1.gpr (by decide), k₁.gpr (by decide)]
  rw [e6 s₁ ⟨Keep.refl _ _, rfl⟩] at n2
  refine sel_ok .r6 (by decide) 4 (by decide) (by decide) _ _ s₂ (fun s₃ h₃ e => ?_) (fun s₃ h₃ n4 => ?_)
  · rw [e6 s₂ h₂] at e
    exact go (d := 4) (c := 2) (nb := 1) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show lo s₀ .r5 = 4 by omega_arith]; decide) s₃ (h₂.trans h₃)
  rw [e6 s₂ h₂] at n4
  refine sel_ok .r6 (by decide) 4096 (by decide) (by decide) _ _ s₃ (fun s₄ h₄ e => ?_) (fun s₄ h₄ n4096 => ?_)
  · rw [e6 s₃ (h₂.trans h₃)] at e
    exact go (d := 13) (c := 8) (nb := 13) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show lo s₀ .r5 = 4095 by omega_arith]; decide) s₄ ((h₂.trans h₃).trans h₄)
  rw [e6 s₃ (h₂.trans h₃)] at n4096
  refine sel_ok .r6 (by decide) 131072 (by decide) (by decide) _ _ s₄ (fun s₅ h₅ e => ?_) (fun s₅ h₅ n17 => ?_)
  · rw [e6 s₄ ((h₂.trans h₃).trans h₄)] at e
    exact go (d := 18) (c := 4) (nb := 9) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show lo s₀ .r5 = 131071 by omega_arith]; decide) s₅ (((h₂.trans h₃).trans h₄).trans h₅)
  · rw [e6 s₄ ((h₂.trans h₃).trans h₄)] at n17
    have e : lo s₀ .r6 = 524288 := by omega_arith
    exact go (d := 20) (c := 2) (nb := 5) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show lo s₀ .r5 = 524287 by omega_arith]; decide) s₅ (((h₂.trans h₃).trans h₄).trans h₅)

theorem bitUnpack_ct :
    ConstantTime isa (bitUnpackContract PPC64LE.abi).pre (bitUnpackContract PPC64LE.abi).pub
      Impl.MlDsa.PPC64LE.Pack.bitUnpack := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold Impl.MlDsa.PPC64LE.Pack.bitUnpack
  refine RelCT.seq (R := Agr .r6) (((relct_noMem (by rfl)).wpDep
    (F := fun (σ s' : State) => ((s'.gpr .r10 = σ.gpr .r3 ∧ s'.gpr .r11 = σ.gpr .r7 ∧
      s'.gpr .r7 = BitVec.ofNat 64 q ∧ s'.mem = σ.mem) ∧ Keep [.r10, .r11, .r7] σ s') ∧ s'.sp = σ.sp)
    fun a b _ => ⟨WP.withSp (mov2Q_ok (by decide) (by decide) (by decide) a),
      WP.withSp (mov2Q_ok (by decide) (by decide) (by decide) b)⟩).mono (fun _ _ h => h)
    fun a' b' ⟨_, σ₁, σ₂, ⟨_, _, hpub⟩, ⟨⟨⟨g₁, h₁, _⟩, k₁⟩, p₁⟩, ⟨⟨⟨g₂, h₂, _⟩, k₂⟩, p₂⟩⟩ => by
      sig_pub [bitUnpackContract, bitUnpackSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
      obtain ⟨hsp, e3, -, -, e6, e7⟩ := hpub
      refine ⟨by rw [p₁, p₂, hsp], by rw [g₁, g₂, e3], by rw [h₁, h₂, e7], ?_⟩
      simp only [lo]; rw [k₁.gpr (by decide), k₂.gpr (by decide), e6]) ?_
  exact sel_ct (by decide) (by decide) (leaf_ct (by taint_decide))
    (sel_ct (by decide) (by decide) (leaf_ct (by taint_decide))
      (sel_ct (by decide) (by decide) (leaf_ct (by taint_decide))
        (sel_ct (by decide) (by decide) (leaf_ct (by taint_decide)) (leaf_ct (by taint_decide)))))

/-- A state satisfying the precondition. -/
def buSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 96 | .r5 => 2 | .r6 => 2 | .r7 => 0x2000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 96⟩]
  wr := [⟨0x2000, 1024⟩]

example : ∃ pre post leak, bitUnpackContract PPC64LE.abi =
    bitUnpackSig.contract PPC64LE.target.abi pre post true 0 leak := ⟨_, _, _, rfl⟩

theorem bitUnpack_verified :
    Verified PPC64LE.target Impl.MlDsa.PPC64LE.Pack.bitUnpack (bitUnpackContract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, bitUnpack_ct, ?_⟩
  · obtain ⟨t, s', he, hpost⟩ := bu_wp (BuPre.of hs)
    refine ⟨t, s', he, abi_of (by rw [← Code.allInstrs_eq]; decide +kernel) (by decide +kernel)
      (by rw [← Code.allInstrs_eq]; decide +kernel) he, ?_⟩
    sig_post [bitUnpackContract, bitUnpackSig, PPC64LE.abi, PPC64LE.argRegs]
    exact hpost
  · refine ⟨buSat, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [bitUnpackContract, bitUnpackSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | (simp only [bitPackParams]; decide +kernel)
        | decide +kernel

/-! ## `vg_mldsa_unpack_t1` -/

theorem t1_wp {s₀ : State} (hp : T1Pre s₀) :
    WP isa Impl.MlDsa.PPC64LE.Pack.unpackT1 s₀ fun s' =>
      PolyIs s'.mem (s₀.gpr .r4)
        ((simpleBitUnpack (bytesAt s₀.mem (s₀.gpr .r3) 320) t1Max).map fun c => ofInt (c * 2 ^ d : Nat)) := by
  unfold Impl.MlDsa.PPC64LE.Pack.unpackT1
  refine WP.seq (WP.mono (mov2_ok (a := .r3) (b := .r4) (by decide) (by decide) (by decide) s₀)
    fun s₁ ⟨⟨g10, g11, m₁⟩, k₁⟩ => ?_)
  refine WP.mono (unpackLoop_ok t1Fin_ok true_stable (c := 4) (nb := 5) (by constructor <;> decide)
    (pv := s₀.gpr .r3) (pp := s₀.gpr .r4) (m₀ := s₀.mem) (rd := s₀.rd) (wr := s₀.wr) (sE := s₁) trivial
    (by rw [hp.rd]; exact List.mem_append_left _ (List.mem_singleton_self _))
    (by rw [hp.wr]; exact List.mem_singleton_self _) hp.disj g10 g11 (by rw [k₁.2.1]) (by rw [k₁.2.2]) m₁
    (Keep.refl _ _))
    fun s' ⟨hc, _, _⟩ => ?_
  refine polyIs_of_toNat fun i hi => ?_
  have hy : inNum s₀.mem (s₀.gpr .r3) 10 / 2 ^ (10 * i) % 2 ^ 10 < 2 ^ 10 := Nat.mod_lt _ (by decide)
  rw [hc i hi, t1Word, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show _ < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show _ < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show _ < 2 ^ 32 by omega_arith), Vector.getElem_map,
    simpleBitUnpack_get _ _ hi, show bitlen t1Max = 10 by decide, ofInt_t1 hy]

theorem unpackT1_ct :
    ConstantTime isa (unpackT1Contract PPC64LE.abi).pre (unpackT1Contract PPC64LE.abi).pub
      Impl.MlDsa.PPC64LE.Pack.unpackT1 :=
  RelCT.constantTime (RelCT.taint (A := VG.PPC64LE.taint) (Taint.ofRegs [.r3, .r4]) (fun a b h => by
    obtain ⟨_, _, hpub⟩ := h
    sig_pub [unpackT1Contract, unpackT1Sig, PPC64LE.abi, PPC64LE.argRegs] at hpub
    obtain ⟨hsp, h3, h4⟩ := hpub
    refine ⟨hsp, fun x hx => ?_⟩
    rw [Taint.mem_ofRegs] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    exacts [h3, h4]) (by taint_decide))

/-- A state satisfying the precondition. -/
def t1Sat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 320⟩]
  wr := [⟨0x2000, 1024⟩]

example : ∃ pre post leak, unpackT1Contract PPC64LE.abi =
    unpackT1Sig.contract PPC64LE.target.abi pre post true 0 leak := ⟨_, _, _, rfl⟩

theorem unpackT1_verified :
    Verified PPC64LE.target Impl.MlDsa.PPC64LE.Pack.unpackT1 (unpackT1Contract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, unpackT1_ct, ?_⟩
  · obtain ⟨t, s', he, hpost⟩ := t1_wp (T1Pre.of hs)
    refine ⟨t, s', he, abi_of (by rw [← Code.allInstrs_eq]; decide +kernel) (by decide +kernel)
      (by rw [← Code.allInstrs_eq]; decide +kernel) he, ?_⟩
    sig_post [unpackT1Contract, unpackT1Sig, PPC64LE.abi, PPC64LE.argRegs]
    exact hpost
  · refine ⟨t1Sat, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [unpackT1Contract, unpackT1Sig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals decide +kernel

end VG.Proof.MlDsa.PPC64LE.Pack
