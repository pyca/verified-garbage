module

public import VerifiedGarbage.Impl.Rsa.Arm.Inverse
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Rsa.Arm.Inv.Geo
public import VerifiedGarbage.Proof.Divstep.Libsecp
import VerifiedGarbage.Proof.Bignum.Arm.AddCarry
import VerifiedGarbage.Proof.Mont.Arm.Step
import VerifiedGarbage.Proof.Rsa.Arm.Inv.Ops
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! # The fused passes of `inverse` on ARMv7

`term_ok`: `term` adds a coefficient's magnitude times a word XORed with its sign mask to a
64-bit accumulator.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Inv
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Proof.Mont
open VG.Impl.Rsa.Arm.Keys.Inv
open VG.Proof.X25519.Arm (Rest Upd wp_ldr wp_str wp_dp wp_mov wp_mul wp_subs op2_imm op2_reg op2_lsl op2_lsr
  dpVal toNat_shr toNat_shl toNat_mul_lt)
open VG.Proof.Bignum.Arm (wp_adds wp_adc)
open VG.Proof.Mont.Arm (wp_mla)

/-- The accumulator `hi:lo`. -/
abbrev acc64 (lo hi : BitVec 32) : Nat := lo.toNat + 2 ^ 32 * hi.toNat

theorem acc64_lt (lo hi : BitVec 32) : acc64 lo hi < 2 ^ 64 := by
  have := lo.isLt; have := hi.isLt; simp only [acc64]; omega

/-- `adds lo, lo, a` and `adc hi, hi, b`. -/
theorem acc64_add (lo hi a b : BitVec 32) :
    acc64 (lo + a) (hi + b + (if decide (2 ^ 32 ≤ lo.toNat + a.toNat) = true then 1 else 0)) =
      (acc64 lo hi + a.toNat + 2 ^ 32 * b.toNat) % 2 ^ 64 := by
  have := lo.isLt; have := hi.isLt; have := a.isLt; have := b.isLt
  simp only [acc64, decide_eq_true_eq]
  have o1 : (1 : BitVec 32).toNat = 1 := rfl
  have o0 : (0 : BitVec 32).toNat = 0 := rfl
  split
  · rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, o1]; omega
  · rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, o0]; omega

/-- A product below `2^32`, as a word shifted by 16 bits into the accumulator. -/
theorem shl_shr16 (p : BitVec 32) : (p <<< 16).toNat + 2 ^ 32 * (p >>> 16).toNat = p.toNat * 2 ^ 16 := by
  rw [toNat_shl, toNat_shr]; have := p.isLt; omega

/-- `mla hi, a, b, hi`. -/
theorem acc64_mla (lo hi a b : BitVec 32) :
    acc64 lo (a * b + hi) = (acc64 lo hi + 2 ^ 32 * (a.toNat * b.toNat)) % 2 ^ 64 := by
  have := lo.isLt; have := hi.isLt
  simp only [acc64, BitVec.toNat_add, BitVec.toNat_mul]
  rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 by decide]
  rw [Nat.mod_add_mod]
  generalize a.toNat * b.toNat = P
  omega

/-- `adds lo, lo, a` and `adc hi, hi, b` as two updates. -/
theorem pair_acc {s7 s8 s9 : State} {lo hi : Reg} (hlh : lo ≠ hi) {a b : BitVec 32}
    (u8 : Upd s7 s8 lo (s7.gpr lo + a)) (c8 : s8.c = decide (2 ^ 32 ≤ (s7.gpr lo).toNat + a.toNat))
    (u9 : Upd s8 s9 hi (s8.gpr hi + b + if s8.c then 1 else 0)) :
    acc64 (s9.gpr lo) (s9.gpr hi) = (acc64 (s7.gpr lo) (s7.gpr hi) + a.toNat + 2 ^ 32 * b.toNat) % 2 ^ 64 := by
  rw [u9.gpr, u9.other _ hlh, u8.gpr, u8.other _ hlh.symm, c8]
  exact acc64_add _ _ _ _

/-- The registers of a `term`: its source and accumulator apart from each other and from its
temporaries and `r12`. -/
structure TermRegs (xs lo hi : Reg) : Prop where
  l6 : lo ≠ .r6
  l7 : lo ≠ .r7
  l9 : lo ≠ .r9
  l10 : lo ≠ .r10
  l12 : lo ≠ .r12
  h6 : hi ≠ .r6
  h7 : hi ≠ .r7
  h9 : hi ≠ .r9
  h10 : hi ≠ .r10
  h12 : hi ≠ .r12
  lh : lo ≠ hi
  x6 : xs ≠ .r6
  x12 : xs ≠ .r12

/-- The words a `term` reads: the source word and its coefficient's mask and halves. -/
abbrev sw (s : State) (d : Nat) : BitVec 32 := s.mem.readW (State.addr (s.gpr .r12 + BitVec.ofNat 32 d)) 32

theorem term_ok {s : State} {xs lo hi : Reg} {xo t : Nat} (hr : TermRegs xs lo hi) (hxo : xo < 4096)
    (ht : coefOff t + 8 < 4096)
    (hx : InRegions (s.rd ++ s.wr) (State.addr (s.gpr xs + BitVec.ofNat 32 xo)) 4)
    (hm : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 (coefOff t))) 4)
    (hl : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 (coefOff t + 4))) 4)
    (hh : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 (coefOff t + 8))) 4)
    (hcl : (sw s (coefOff t + 4)).toNat < 2 ^ 16) (hch : (sw s (coefOff t + 8)).toNat < 2 ^ 16)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.mem = s.mem → Rest [.r6, .r7, .r9, .r10, lo, hi] s s' →
      acc64 (s'.gpr lo) (s'.gpr hi) = (acc64 (s.gpr lo) (s.gpr hi) +
        ((sw s (coefOff t + 4)).toNat + 2 ^ 16 * (sw s (coefOff t + 8)).toNat) *
          (s.mem.readW (State.addr (s.gpr xs + BitVec.ofNat 32 xo)) 32 ^^^ sw s (coefOff t)).toNat) % 2 ^ 64 →
      WP isa (.block is) s' Q) :
    WP isa (.block (term xs xo t lo hi ++ is)) s Q := by
  have s16 : (1 ≤ 16 ∧ 16 ≤ 31) := by decide
  simp only [term, List.cons_append, List.nil_append]
  refine wp_ldr hxo rfl hx fun s1 u1 => ?_
  have e12 : s1.gpr .r12 = s.gpr .r12 := u1.other _ (by decide)
  refine wp_ldr (by omega) rfl (by rw [u1.rd, u1.wr, e12]; exact hm) fun s2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  refine wp_mov (op2_lsr s16) fun s4 u4 => ?_
  refine wp_dp (op2_lsl s16) fun s5 u5 => ?_
  have e12' : s5.gpr .r12 = s.gpr .r12 := by
    rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), e12]
  have m5 : s5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have rw5 : s5.rd = s.rd ∧ s5.wr = s.wr := ⟨by rw [u5.rd, u4.rd, u3.rd, u2.rd, u1.rd],
    by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]⟩
  refine wp_ldr (by omega) rfl (by rw [rw5.1, rw5.2, e12']; exact hl) fun s6 u6 => ?_
  refine wp_mul fun s7 u7 => ?_
  refine wp_adds (op2_reg _ _) fun s8 u8 c8 => ?_
  refine wp_adc (op2_imm (by decide)) fun s9 u9 _ => ?_
  refine wp_mul fun s10 u10 => ?_
  refine wp_adds (op2_lsl s16) fun s11 u11 c11 => ?_
  refine wp_adc (op2_lsr s16) fun s12 u12 _ => ?_
  have e12'' : s12.gpr .r12 = s.gpr .r12 := by
    rw [u12.other _ hr.h12.symm, u11.other _ hr.l12.symm, u10.other _ (by decide), u9.other _ hr.h12.symm,
      u8.other _ hr.l12.symm, u7.other _ (by decide), u6.other _ (by decide), e12']
  have m12 : s12.mem = s.mem := by
    rw [u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, m5]
  have rw12 : s12.rd = s.rd ∧ s12.wr = s.wr := ⟨by rw [u12.rd, u11.rd, u10.rd, u9.rd, u8.rd, u7.rd, u6.rd, rw5.1],
    by rw [u12.wr, u11.wr, u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, rw5.2]⟩
  refine wp_ldr (by omega) rfl (by rw [rw12.1, rw12.2, e12'']; exact hh) fun s13 u13 => ?_
  refine wp_mul fun s14 u14 => ?_
  refine wp_adds (op2_lsl s16) fun s15 u15 c15 => ?_
  refine wp_adc (op2_lsr s16) fun s16' u16 _ => ?_
  refine wp_mla fun s17 u17 => ?_
  -- The values.
  generalize hX : s.mem.readW (State.addr (s.gpr xs + BitVec.ofNat 32 xo)) 32 = X at k
  generalize hM : sw s (coefOff t) = M at k
  generalize hL : sw s (coefOff t + 4) = CL at k hcl
  generalize hH : sw s (coefOff t + 8) = CH at k hch
  have v6 : s1.gpr .r6 = X := by rw [u1.gpr, hX]
  have v7 : s2.gpr .r7 = M := by rw [u2.gpr, u1.mem, e12, ← hM]
  have v3 : s3.gpr .r6 = X ^^^ M := by rw [u3.gpr, u2.other _ (by decide), v6, v7]; rfl
  have v4 : s4.gpr .r7 = (X ^^^ M) >>> 16 := by rw [u4.gpr, v3]
  have v5 : s5.gpr .r6 = (X ^^^ M) &&& ~~~(((X ^^^ M) >>> 16) <<< 16) := by
    rw [u5.gpr, u4.other _ (by decide), v3, v4]; rfl
  generalize hxl : (X ^^^ M) &&& ~~~(((X ^^^ M) >>> 16) <<< 16) = xl at v5
  generalize hxh : (X ^^^ M) >>> 16 = xh at v4
  have bl : xl.toNat < 2 ^ 16 := by rw [← hxl, low16]; omega
  have bh : xh.toNat < 2 ^ 16 := by rw [← hxh, toNat_shr]; have := (X ^^^ M).isLt; omega
  have xs16 : (X ^^^ M).toNat = xl.toNat + 2 ^ 16 * xh.toNat := by
    rw [← hxl, ← hxh, low16, toNat_shr]; omega
  have v9 : s6.gpr .r9 = CL := by rw [u6.gpr, m5, e12', ← hL]
  have p1 : s7.gpr .r10 = xl * CL := by rw [u7.gpr, u6.other _ (by decide), v5, v9]
  have lt (x y : BitVec 32) (hx : x.toNat < 2 ^ 16) (hy : y.toNat < 2 ^ 16) : (x * y).toNat = x.toNat * y.toNat :=
    toNat_mul_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_of_lt hy) (by omega)) (by decide))
  have a9 := pair_acc hr.lh u8 c8 u9
  have z0 : (0 : BitVec 32).toNat = 0 := rfl
  rw [p1, lt _ _ bl hcl, z0] at a9
  have r7_10 : s10.gpr .r7 = xh := by
    rw [u10.other _ (by decide), u9.other _ hr.h7.symm, u8.other _ hr.l7.symm, u7.other _ (by decide),
      u6.other _ (by decide), u5.other _ (by decide), v4]
  have r9_10 : s10.gpr .r9 = CL := by
    rw [u10.other _ (by decide), u9.other _ hr.h9.symm, u8.other _ hr.l9.symm, u7.other _ (by decide), v9]
  have p2 : s10.gpr .r10 = xh * CL := by rw [u10.gpr, u9.other _ hr.h7.symm, u8.other _ hr.l7.symm,
    u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), v4, ← r9_10,
    u10.other _ (by decide), u9.other _ hr.h9.symm, u8.other _ hr.l9.symm, u7.other _ (by decide)]
  have a12 := pair_acc hr.lh u11 c11 u12
  rw [u11.other _ hr.l10.symm, p2, Nat.add_assoc, shl_shr16, lt _ _ bh hcl] at a12
  have e10 : s9.gpr lo = s10.gpr lo ∧ s9.gpr hi = s10.gpr hi :=
    ⟨(u10.other _ hr.l10).symm, (u10.other _ hr.h10).symm⟩
  have v13 : s13.gpr .r9 = CH := by rw [u13.gpr, m12, e12'', ← hH]
  have r6_13 : s13.gpr .r6 = xl := by
    rw [u13.other _ (by decide), u12.other _ hr.h6.symm, u11.other _ hr.l6.symm, u10.other _ (by decide),
      u9.other _ hr.h6.symm, u8.other _ hr.l6.symm, u7.other _ (by decide), u6.other _ (by decide), v5]
  have p3 : s14.gpr .r10 = xl * CH := by rw [u14.gpr, r6_13, v13]
  have a16 := pair_acc hr.lh u15 c15 u16
  rw [u15.other _ hr.l10.symm, p3, Nat.add_assoc, shl_shr16, lt _ _ bl hch] at a16
  have e14 : s13.gpr lo = s14.gpr lo ∧ s13.gpr hi = s14.gpr hi ∧ s12.gpr lo = s13.gpr lo ∧ s12.gpr hi = s13.gpr hi :=
    ⟨(u14.other _ hr.l10).symm, (u14.other _ hr.h10).symm, (u13.other _ hr.l9).symm, (u13.other _ hr.h9).symm⟩
  have r7_16 : s16'.gpr .r7 = xh := by
    rw [u16.other _ hr.h7.symm, u15.other _ hr.l7.symm, u14.other _ (by decide), u13.other _ (by decide),
      u12.other _ hr.h7.symm, u11.other _ hr.l7.symm, r7_10]
  have r9_16 : s16'.gpr .r9 = CH := by
    rw [u16.other _ hr.h9.symm, u15.other _ hr.l9.symm, u14.other _ (by decide), v13]
  have a17 : acc64 (s17.gpr lo) (s17.gpr hi) = (acc64 (s16'.gpr lo) (s16'.gpr hi) + 2 ^ 32 * (xh.toNat * CH.toNat)) % 2 ^ 64 := by
    rw [u17.gpr, u17.other _ hr.lh, r7_16, r9_16]; exact acc64_mla _ _ _ _
  have e7 : s7.gpr lo = s.gpr lo ∧ s7.gpr hi = s.gpr hi := by
    constructor
    · rw [u7.other _ hr.l10, u6.other _ hr.l9, u5.other _ hr.l6, u4.other _ hr.l7, u3.other _ hr.l6,
        u2.other _ hr.l7, u1.other _ hr.l6]
    · rw [u7.other _ hr.h10, u6.other _ hr.h9, u5.other _ hr.h6, u4.other _ hr.h7, u3.other _ hr.h6,
        u2.other _ hr.h7, u1.other _ hr.h6]
  refine k s17 ?_ ?_ ?_
  · rw [u17.mem, u16.mem, u15.mem, u14.mem, u13.mem, m12]
  · have mem : ∀ r ∈ ([.r6, .r7, .r9, .r10, lo, hi] : List Reg), r ∈ ([.r6, .r7, .r9, .r10, lo, hi] : List Reg) :=
      fun _ h => h
    exact (u1.rest (by simp)).trans <| (u2.rest (by simp)).trans <| (u3.rest (by simp)).trans <|
      (u4.rest (by simp)).trans <| (u5.rest (by simp)).trans <| (u6.rest (by simp)).trans <|
      (u7.rest (by simp)).trans <| (u8.rest (by simp)).trans <| (u9.rest (by simp)).trans <|
      (u10.rest (by simp)).trans <| (u11.rest (by simp)).trans <| (u12.rest (by simp)).trans <|
      (u13.rest (by simp)).trans <| (u14.rest (by simp)).trans <| (u15.rest (by simp)).trans <|
      (u16.rest (by simp)).trans (u17.rest (by simp))
  · rw [a17, a16, ← e14.1, ← e14.2.1, ← e14.2.2.1, ← e14.2.2.2, a12, ← e10.1, ← e10.2, a9, e7.1, e7.2, xs16]
    have := acc64_lt (s.gpr lo) (s.gpr hi)
    generalize acc64 (s.gpr lo) (s.gpr hi) = A at *
    rw [Nat.mod_add_mod, Nat.add_assoc, Nat.mod_add_mod, Nat.add_assoc, Nat.mod_add_mod]
    congr 1
    grind

/-! ## A word's terms of both rows -/

/-- A term: its source pointer, its coefficient's slot, and its row (`false`: `r3:r2`, `true`: `r5:r4`). -/
structure TSpec where
  xs : Reg
  t : Nat
  row : Bool

abbrev rlo (row : Bool) : Reg := if row then .r4 else .r2
abbrev rhi (row : Bool) : Reg := if row then .r5 else .r3

/-- The code of a word's terms, at the offset `zo` from the sources. -/
def tcode (zo : Nat) : List TSpec → List Instr
  | [] => []
  | sp :: L => term sp.xs zo sp.t (rlo sp.row) (rhi sp.row) ++ tcode zo L

/-- A coefficient's magnitude from its halves. -/
abbrev cmag (s : State) (t : Nat) : Nat := (sw s (coefOff t + 4)).toNat + 2 ^ 16 * (sw s (coefOff t + 8)).toNat

/-- A term's value. -/
abbrev tval (s : State) (zo : Nat) (sp : TSpec) : Nat :=
  cmag s sp.t * (s.mem.readW (State.addr (s.gpr sp.xs + BitVec.ofNat 32 zo)) 32 ^^^ sw s (coefOff sp.t)).toNat

/-- A row's terms. -/
def tsum (s : State) (zo : Nat) (row : Bool) : List TSpec → Nat
  | [] => 0
  | sp :: L => (if sp.row = row then tval s zo sp else 0) + tsum s zo row L

abbrev acc (s : State) (row : Bool) : Nat := acc64 (s.gpr (rlo row)) (s.gpr (rhi row))

/-- What a term needs. -/
structure TOk (s : State) (zo : Nat) (sp : TSpec) : Prop where
  t5 : sp.t ≤ 5
  xs : sp.xs ∉ [.r2, .r3, .r4, .r5, .r6, .r7, .r9, .r10, .r12]
  src : InRegions (s.rd ++ s.wr) (State.addr (s.gpr sp.xs + BitVec.ofNat 32 zo)) 4
  m : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 (coefOff sp.t))) 4
  l : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 (coefOff sp.t + 4))) 4
  h : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 (coefOff sp.t + 8))) 4
  cl : (sw s (coefOff sp.t + 4)).toNat < 2 ^ 16
  ch : (sw s (coefOff sp.t + 8)).toNat < 2 ^ 16

abbrev tClob : List Reg := [.r2, .r3, .r4, .r5, .r6, .r7, .r9, .r10]

theorem TOk.congr {s s' : State} {zo : Nat} {sp : TSpec} (h : TOk s zo sp) (hm : s'.mem = s.mem)
    (hr : Rest tClob s s') : TOk s' zo sp ∧ tval s' zo sp = tval s zo sp := by
  have ex : s'.gpr sp.xs = s.gpr sp.xs := hr.gpr _ fun e => h.xs (by
    simp only [tClob, List.mem_cons, List.not_mem_nil, or_false] at e ⊢
    rcases e with e | e | e | e | e | e | e | e <;> simp [e])
  have e12 : s'.gpr .r12 = s.gpr .r12 := hr.gpr _ (by decide)
  have rw' : s'.rd ++ s'.wr = s.rd ++ s.wr := by rw [hr.rd, hr.wr]
  have esw : ∀ d, sw s' d = sw s d := fun d => by simp only [sw, e12, hm]
  refine ⟨⟨h.t5, h.xs, by rw [rw', ex]; exact h.src, by rw [rw', e12]; exact h.m, by rw [rw', e12]; exact h.l,
    by rw [rw', e12]; exact h.h, by rw [esw]; exact h.cl, by rw [esw]; exact h.ch⟩, ?_⟩
  simp only [tval, cmag, esw, ex, hm]

theorem terms_ok {zo : Nat} (hzo : zo < 4096) :
    ∀ (L : List TSpec) {s : State} {is : List Instr} {Q : State → Prop}, (∀ sp ∈ L, TOk s zo sp) →
    (∀ s', s'.mem = s.mem → Rest tClob s s' →
      (∀ row, acc s' row = (acc s row + tsum s zo row L) % 2 ^ 64) → WP isa (.block is) s' Q) →
    WP isa (.block (tcode zo L ++ is)) s Q
  | [], s, is, Q, _, k => by
    refine k s rfl (Rest.refl _ _) fun row => ?_
    simp only [tsum, Nat.add_zero]; exact (Nat.mod_eq_of_lt (acc64_lt _ _)).symm
  | sp :: L, s, is, Q, hL, k => by
    have h0 := hL sp (by simp)
    rw [tcode, List.append_assoc]
    have tr : TermRegs sp.xs (rlo sp.row) (rhi sp.row) := by
      have := h0.xs
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
      cases sp.row <;> exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide, by decide, this.2.2.2.2.1, this.2.2.2.2.2.2.2.2⟩
    refine term_ok tr (by omega) (by simp only [coefOff]; have := h0.t5; omega) h0.src h0.m h0.l h0.h h0.cl h0.ch
      fun s1 m1 r1 v1 => ?_
    have sub : ∀ b : Bool, ∀ r ∈ ([.r6, .r7, .r9, .r10, rlo b, rhi b] : List Reg), r ∈ tClob := by decide
    have r1' : Rest tClob s s1 := r1.mono (sub sp.row)
    refine terms_ok hzo L (fun sp' h' => (TOk.congr (hL sp' (by simp [h'])) m1 r1').1) fun s' m' r' v' => ?_
    refine k s' (m'.trans m1) (r1'.trans r') fun row => ?_
    have eL : tsum s1 zo row L = tsum s zo row L := by
      clear v' k
      induction L with
      | nil => rfl
      | cons a L ih =>
        simp only [tsum]
        rw [(TOk.congr (hL a (by simp)) m1 r1').2, ih fun x hx => hL x (by
          simp only [List.mem_cons] at hx ⊢
          rcases hx with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h))]
    rw [v' row, eL, tsum]
    by_cases hr : sp.row = row
    · subst hr
      simp only [↓reduceIte, acc]
      rw [v1, Nat.mod_add_mod, Nat.add_assoc]
    · simp only [hr, ↓reduceIte, Nat.zero_add, acc]
      have dis : ∀ b c : Bool, b ≠ c → rlo c ∉ ([.r6, .r7, .r9, .r10, rlo b, rhi b] : List Reg) ∧
          rhi c ∉ ([.r6, .r7, .r9, .r10, rlo b, rhi b] : List Reg) := by decide
      rw [r1.gpr _ (dis _ _ hr).1, r1.gpr _ (dis _ _ hr).2]

/-! ## A row's output words -/

theorem InRegions.rdwr {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨R, hR, hs⟩ := h; exact ⟨R, List.mem_append_right _ hR, hs⟩

/-- `out0`: the top two bits of `lo` to `[p]`, and the carry down. -/
theorem out0_ok {s : State} {p lo hi : Reg} (hp6 : p ≠ .r6) (hh6 : hi ≠ .r6) (hlh : lo ≠ hi)
    {a0 : Addr} (e0 : State.addr (s.gpr p + BitVec.ofNat 32 0) = a0) (w0 : InRegions s.wr a0 4)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.mem = s.mem.writeW a0 (s.gpr lo >>> 30) → s'.gpr lo = s.gpr hi → s'.gpr hi = 0 →
      Rest [.r6, lo, hi] s s' → WP isa (.block is) s' Q) :
    WP isa (.block (out0 p lo hi ++ is)) s Q := by
  simp only [out0, List.cons_append, List.nil_append]
  refine wp_mov (op2_lsr (by decide)) fun s1 u1 => ?_
  refine wp_str (a := a0) (by decide) (by rw [u1.other _ hp6]; exact e0) (by rw [u1.wr]; exact w0) fun s2 u2 => ?_
  refine wp_mov (op2_reg _ _) fun s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun s4 u4 => ?_
  refine k s4 ?_ ?_ u4.gpr ?_
  · rw [u4.mem, u3.mem, u2.mem, u1.mem, u1.gpr]
  · rw [u4.other _ hlh, u3.gpr, u2.gpr, u1.other _ hh6]
  · exact (u1.rest (by simp)).trans ((u2.rest _).trans ((u3.rest (by simp)).trans (u4.rest (by simp))))

/-- `outW`: `[p] |= lo << 2`, the top two bits of `lo` to `[p + 4]`, and the carry down. -/
theorem outW_ok {s : State} {p lo hi : Reg} (hp6 : p ≠ .r6) (hl6 : lo ≠ .r6) (hh6 : hi ≠ .r6) (hlh : lo ≠ hi)
    {a0 a1 : Addr} (e0 : State.addr (s.gpr p + BitVec.ofNat 32 0) = a0)
    (e1 : State.addr (s.gpr p + BitVec.ofNat 32 4) = a1) (w0 : InRegions s.wr a0 4) (w1 : InRegions s.wr a1 4)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.mem = (s.mem.writeW a0 (s.mem.readW a0 32 ||| s.gpr lo <<< 2)).writeW a1 (s.gpr lo >>> 30) →
      s'.gpr lo = s.gpr hi → s'.gpr hi = 0 → Rest [.r6, lo, hi] s s' → WP isa (.block is) s' Q) :
    WP isa (.block (outW p lo hi ++ is)) s Q := by
  simp only [outW, List.cons_append, List.nil_append]
  refine wp_ldr (a := a0) (by decide) e0 (InRegions.rdwr w0) fun s1 u1 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s2 u2 => ?_
  have ep : s2.gpr p = s.gpr p := by rw [u2.other _ hp6, u1.other _ hp6]
  refine wp_str (a := a0) (by decide) (by rw [ep]; exact e0) (by rw [u2.wr, u1.wr]; exact w0) fun s3 u3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => ?_
  refine wp_str (a := a1) (by decide) (by rw [u4.other _ hp6, u3.gpr, ep]; exact e1)
    (by rw [u4.wr, u3.wr, u2.wr, u1.wr]; exact w1) fun s5 u5 => ?_
  refine wp_mov (op2_reg _ _) fun s6 u6 => ?_
  refine wp_mov (op2_imm (by decide)) fun s7 u7 => ?_
  refine k s7 ?_ ?_ u7.gpr ?_
  · rw [u7.mem, u6.mem, u5.mem, u4.mem, u4.gpr, u3.mem, u3.gpr, u2.gpr, u2.mem, u1.mem, u1.gpr,
      u2.other _ hl6, u1.other _ hl6]
    rfl
  · rw [u7.other _ hlh, u6.gpr, u5.gpr, u4.other _ hh6, u3.gpr, u2.other _ hh6, u1.other _ hh6]
  · exact (u1.rest (by simp)).trans <| (u2.rest (by simp)).trans <| (u3.rest _).trans <|
      (u4.rest (by simp)).trans <| (u5.rest _).trans <| (u6.rest (by simp)).trans (u7.rest (by simp))

/-- `outTop`: `[p] |= (lo - corr) << 2`, with `corr` the word at `r12 + corrOff row`. -/
theorem outTop_ok {s : State} {p lo : Reg} {row : Nat} (hp6 : p ≠ .r6) (hl6 : lo ≠ .r6) (hpl : p ≠ lo)
    (hr : corrOff row < 4096) {a0 : Addr} (e0 : State.addr (s.gpr p + BitVec.ofNat 32 0) = a0)
    (w0 : InRegions s.wr a0 4)
    (hc : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 (corrOff row))) 4)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.mem = s.mem.writeW a0 (s.mem.readW a0 32 ||| (s.gpr lo - sw s (corrOff row)) <<< 2) →
      Rest [.r6, lo] s s' → WP isa (.block is) s' Q) :
    WP isa (.block (outTop p lo row ++ is)) s Q := by
  simp only [outTop, List.cons_append, List.nil_append]
  refine wp_ldr hr rfl hc fun s1 u1 => ?_
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  have ep : s2.gpr p = s.gpr p := by rw [u2.other _ hpl, u1.other _ hp6]
  refine wp_ldr (a := a0) (by decide) (by rw [ep]; exact e0) (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact (InRegions.rdwr w0))
    fun s3 u3 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s4 u4 => ?_
  refine wp_str (a := a0) (by decide) (by rw [u4.other _ hp6, u3.other _ hp6, ep]; exact e0)
    (by rw [u4.wr, u3.wr, u2.wr, u1.wr]; exact w0) fun s5 u5 => ?_
  refine k s5 ?_ ?_
  · rw [u5.mem, u4.mem, u4.gpr, u3.mem, u3.gpr, u3.other _ hl6, u2.mem, u2.gpr, u1.mem, u1.gpr, u1.other _ hl6]
    rfl
  · exact (u1.rest (by simp)).trans <| (u2.rest (by simp)).trans <| (u3.rest (by simp)).trans <|
      (u4.rest (by simp)).trans (u5.rest _)

/-! ## The arithmetic of a row's words -/

/-- `w | x << 2` for `w < 4`. -/
theorem or_shl2 (w x : BitVec 32) (hw : w.toNat < 4) : (w ||| x <<< 2).toNat = w.toNat + 4 * (x.toNat % 2 ^ 30) := by
  rw [BitVec.toNat_or, toNat_shl, show x.toNat * 2 ^ 2 % 2 ^ 32 = (x.toNat % 2 ^ 30) <<< 2 by
    rw [Nat.shiftLeft_eq]; omega, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (i := 2) hw, Nat.shiftLeft_eq]
  omega

/-- A row's step: from the low `i` words `V0 + P w` (`P = 2^(32 (i - 1))`) of `(S mod 2^(32 i)) / 2^30`,
the carry `S / 2^(32 i)` plus the word's terms `T`, to `i + 1` words. -/
theorem stepM {P S T V0 w : Nat} (hV : V0 + P * w = S % (2 ^ 32 * P) / 2 ^ 30) (hV0 : V0 < P) :
    w < 4 ∧
    V0 + P * (w + 4 * ((S / (2 ^ 32 * P) + T) % 2 ^ 32 % 2 ^ 30)) +
        2 ^ 32 * P * ((S / (2 ^ 32 * P) + T) % 2 ^ 32 / 2 ^ 30) =
      (S + T * (2 ^ 32 * P)) % (2 ^ 32 * (2 ^ 32 * P)) / 2 ^ 30 ∧
    (S + T * (2 ^ 32 * P)) / (2 ^ 32 * (2 ^ 32 * P)) = (S / (2 ^ 32 * P) + T) / 2 ^ 32 := by
  generalize hQ : 2 ^ 32 * P = Q at *
  have hQ0 : 0 < Q := by omega
  have hS := Nat.div_add_mod S Q
  generalize S / Q = q at *
  generalize hr : S % Q = r at *
  have hrQ : r < Q := hr ▸ Nat.mod_lt _ hQ0
  generalize hA : q + T = A
  have hA' := Nat.div_add_mod A (2 ^ 32)
  generalize A / 2 ^ 32 = h at *
  generalize hl : A % 2 ^ 32 = l at *
  have hl32 : l < 2 ^ 32 := hl ▸ Nat.mod_lt _ (by decide)
  have eS : S + T * Q = h * (2 ^ 32 * Q) + (l * Q + r) := by
    have e : q + T = 2 ^ 32 * h + l := by omega
    rw [← hS, show Q * q + r + T * Q = Q * (q + T) + r by grind, e]; grind
  have lQ : l * Q + r < 2 ^ 32 * Q := by
    have : (l + 1) * Q ≤ 2 ^ 32 * Q := Nat.mul_le_mul_right _ hl32
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  have hQ4 : Q = 2 ^ 30 * (4 * P) := by rw [← hQ]; omega
  have r30 : r / 2 ^ 30 < 4 * P := by
    rw [Nat.div_lt_iff_lt_mul (by decide), Nat.mul_comm]; rw [hQ4] at hrQ; exact hrQ
  refine ⟨?_, ?_, ?_⟩
  · rw [← hV] at r30
    by_contra hw
    have : P * 4 ≤ P * w := Nat.mul_le_mul_left _ (by omega)
    omega
  · rw [eS, Nat.mul_add_mod_of_lt lQ, show l * Q + r = r + 4 * P * l * 2 ^ 30 by rw [hQ4]; grind,
      Nat.add_mul_div_right _ _ (by decide), ← hV, ← hQ]
    have := Nat.div_add_mod l (2 ^ 30)
    generalize l / 2 ^ 30 = a at *
    generalize l % 2 ^ 30 = b at *
    rw [← this]; grind
  · rw [eS, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt lQ, Nat.zero_add]

/-! ## A pass: its rows' sums -/

open VG.Proof.Rsa.Arm.Keys

/-- A word above the arrays a frame names. -/
theorem Keep.above {B : BitVec 32} {W : Nat} {js : List Nat} {m m' : Mem} (h : Keep B W js [] m m')
    {d : Nat} (hj : ∀ j ∈ js, arr W j + S W ≤ d) (fit : d + 4 ≤ 2 ^ 64) :
    w32 m' (State.addr B) d = w32 m (State.addr B) d := by
  have := Outs.val32 (k := 1) (d := d) h (fun r hr => ?_) (by omega)
  · simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  simp only [ranges, List.mem_append, List.mem_map, List.not_mem_nil, false_and, exists_false, or_false] at hr
  obtain ⟨k, hk, rfl⟩ := hr
  have := hj k hk; dsimp only; omega

/-- A pass: the workspace, the memory it starts from, its sources' arrays, its terms, and its rows'
starting carries. -/
structure Pass where
  B : BitVec 32
  W : Nat
  k : Nat
  mI : Mem
  arrOf : Reg → Nat
  L : List TSpec
  srcs : List Reg
  init : Bool → Nat

namespace Pass

/-- Word `j` of array `a`. -/
abbrev xw (p : Pass) (a j : Nat) : BitVec 32 := p.mI.readW (off (State.addr p.B) (arr p.W a + 4 * j)) 32
/-- The scratch word at byte `d`. -/
abbrev scw (p : Pass) (d : Nat) : BitVec 32 := p.mI.readW (off (State.addr p.B) (arr p.W bT1 + d)) 32
/-- Coefficient `t`'s magnitude. -/
abbrev cm (p : Pass) (t : Nat) : Nat := (p.scw (coefOff t + 4)).toNat + 2 ^ 16 * (p.scw (coefOff t + 8)).toNat

/-- A row's terms at word `j`. -/
def tw (p : Pass) (row : Bool) (j : Nat) : List TSpec → Nat
  | [] => 0
  | sp :: L => (if sp.row = row then p.cm sp.t * (p.xw (p.arrOf sp.xs) j ^^^ p.scw (coefOff sp.t)).toNat else 0) +
      tw p row j L

/-- A row's sum over its low `i` words. -/
def rs (p : Pass) (row : Bool) : Nat → Nat
  | 0 => p.init row
  | i + 1 => rs p row i + tw p row i p.L * 2 ^ (32 * i)

/-- A row's coefficients' magnitudes. -/
def csum (p : Pass) (row : Bool) : List TSpec → Nat
  | [] => 0
  | sp :: L => (if sp.row = row then p.cm sp.t else 0) + csum p row L

/-- A row's output array (`r0`'s or `r1`'s). -/
abbrev out (p : Pass) (row : Bool) : Nat := p.arrOf (if row then .r1 else .r0)

theorem tw_le (p : Pass) (row : Bool) (j : Nat) : ∀ L : List TSpec, tw p row j L ≤ csum p row L * (2 ^ 32 - 1)
  | [] => Nat.zero_le _
  | sp :: L => by
    have ih := tw_le p row j L
    simp only [tw, csum]
    have hx := (p.xw (p.arrOf sp.xs) j ^^^ p.scw (coefOff sp.t)).isLt
    generalize (p.xw (p.arrOf sp.xs) j ^^^ p.scw (coefOff sp.t)).toNat = x at *
    generalize p.cm sp.t = c
    split
    · have := Nat.mul_le_mul_left c (show x ≤ 2 ^ 32 - 1 by omega)
      rw [Nat.add_mul]; omega
    · rw [Nat.add_mul]; omega

end Pass

/-- What a pass needs at its start `σ`: the workspace (`Gk` but `r9`), its sources pointing at their
arrays (below the scratch, `r0`'s and `r1`'s apart), the scratch at `r12`, the coefficients' halves
below `2^16` and each row's magnitudes below `2^32`, the rows' carries, and `k` at scratch byte 8. -/
structure Pass.Ok (p : Pass) (σ : State) (Z N : Nat) : Prop where
  g : Gk σ p.B Z p.W p.k N
  hN : 15 ≤ N
  hW : 8 ≤ p.W
  mem : σ.mem = p.mI
  srcs : ∀ r ∈ p.srcs, r ∈ [.r0, .r1, .r11] ∧ p.arrOf r < bT1 ∧
    σ.gpr r = p.B + BitVec.ofNat 32 (arr p.W (p.arrOf r))
  r0 : .r0 ∈ p.srcs
  r1 : .r1 ∈ p.srcs
  nodup : p.srcs.Nodup
  outs : p.out false ≠ p.out true
  terms : ∀ sp ∈ p.L, sp.xs ∈ p.srcs ∧ sp.t ≤ 5 ∧ (p.scw (coefOff sp.t + 4)).toNat < 2 ^ 16 ∧
    (p.scw (coefOff sp.t + 8)).toNat < 2 ^ 16
  r12 : σ.gpr .r12 = p.B + BitVec.ofNat 32 (arr p.W bT1)
  lo : ∀ row, (σ.gpr (rlo row)).toNat = p.init row
  hi : ∀ row, σ.gpr (rhi row) = 0
  csum : ∀ row, p.csum row p.L < 2 ^ 32
  kw : p.scw 8 = BitVec.ofNat 32 p.k

/-- After `i ≥ 1` words of a pass from `σ`. -/
structure Pass.Inv (p : Pass) (σ : State) (i : Nat) (s : State) : Prop where
  rest : Rest (tClob ++ (.lr :: p.srcs)) σ s
  ptr : ∀ r ∈ p.srcs, s.gpr r = p.B + BitVec.ofNat 32 (arr p.W (p.arrOf r) + 4 * (i - 1))
  cnt : s.gpr .lr = BitVec.ofNat 32 (p.k + 1 - i)
  lo : ∀ row, (s.gpr (rlo row)).toNat = p.rs row i / 2 ^ (32 * i)
  hi : ∀ row, s.gpr (rhi row) = 0
  keep : Keep p.B p.W [p.out false, p.out true] [] p.mI s.mem
  high : ∀ row j, i ≤ j → j ≤ p.k →
    w32 s.mem (State.addr p.B) (arr p.W (p.out row) + 4 * j) = w32 p.mI (State.addr p.B) (arr p.W (p.out row) + 4 * j)
  low : ∀ row, val32 s.mem (State.addr p.B) (arr p.W (p.out row)) i = p.rs row i % 2 ^ (32 * i) / 2 ^ 30

namespace Pass.Ok
variable {p : Pass} {σ : State} {Z N : Nat}

theorem arr_lt (ok : p.Ok σ Z N) {r : Reg} (hr : r ∈ p.srcs) : p.arrOf r < N :=
  Nat.lt_of_lt_of_le (ok.srcs r hr).2.1 (by simp only [bT1]; have := ok.hN; omega)

theorem out_src (ok : p.Ok σ Z N) (row : Bool) : (if row then Reg.r1 else Reg.r0) ∈ p.srcs := by
  cases row
  · exact ok.r0
  · exact ok.r1

/-- An address at byte `d` of the workspace from a pointer to byte `x`. -/
theorem addr_at (ok : p.Ok σ Z N) {x d : Nat} (h : x + d < Z) :
    State.addr (p.B + BitVec.ofNat 32 x + BitVec.ofNat 32 d) = off (State.addr p.B) (x + d) := by
  rw [VG.Offset.add_add]; exact ok.g.addr h

theorem scr_fit (ok : p.Ok σ Z N) {d : Nat} (hd : d + 4 ≤ 3 * S p.W) : arr p.W bT1 + d + 4 ≤ Z := by
  have := ok.g.fits
  have : arr p.W 14 ≤ arr p.W N := arr_mono (by have := ok.hN; omega)
  simp only [bT1, arr, S] at *; omega

theorem src_fit (ok : p.Ok σ Z N) {r : Reg} (hr : r ∈ p.srcs) {d : Nat} (hd : d + 4 ≤ S p.W) :
    arr p.W (p.arrOf r) + d + 4 ≤ Z := by
  have := ok.g.arr_fit (ok.arr_lt hr); omega

/-- The terms at word `j` from pointers at byte `o` of their arrays. -/
theorem terms_at (ok : p.Ok σ Z N) {s : State} {zo o j : Nat} (hzo : o + zo = 4 * j) (hj : j ≤ p.k)
    (hrd : s.rd = σ.rd) (hwr : s.wr = σ.wr) (h12 : s.gpr .r12 = σ.gpr .r12)
    (hp : ∀ r ∈ p.srcs, s.gpr r = p.B + BitVec.ofNat 32 (arr p.W (p.arrOf r) + o))
    (hx : ∀ r ∈ p.srcs, s.mem.readW (off (State.addr p.B) (arr p.W (p.arrOf r) + 4 * j)) 32 = p.xw (p.arrOf r) j)
    (hs : ∀ d, d + 4 ≤ 3 * S p.W → s.mem.readW (off (State.addr p.B) (arr p.W bT1 + d)) 32 = p.scw d) :
    (∀ sp ∈ p.L, TOk s zo sp) ∧ ∀ row, tsum s zo row p.L = p.tw row j p.L := by
  have hk := ok.g.kle
  have hW := ok.hW
  have hS40 : 40 ≤ S p.W := by simp only [S]; omega
  have sa : ∀ d, d + 4 ≤ 3 * S p.W → State.addr (s.gpr .r12 + BitVec.ofNat 32 d) = off (State.addr p.B) (arr p.W bT1 + d) :=
    fun d hd => by rw [h12, ok.r12]; exact ok.addr_at (by have := ok.scr_fit hd; omega)
  have sv : ∀ d, d + 4 ≤ 3 * S p.W → sw s d = p.scw d := fun d hd => by simp only [sw]; rw [sa d hd, hs d hd]
  have sr : ∀ d, d + 4 ≤ 3 * S p.W → InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 d)) 4 :=
    fun d hd => by rw [sa d hd, hrd, hwr]; exact ok.g.read (ok.scr_fit hd)
  have xa : ∀ r ∈ p.srcs, State.addr (s.gpr r + BitVec.ofNat 32 zo) = off (State.addr p.B) (arr p.W (p.arrOf r) + 4 * j) :=
    fun r hr => by
      rw [hp r hr, ok.addr_at (by have := ok.src_fit hr (d := 4 * j) (by simp only [S]; omega); omega),
        Nat.add_assoc, hzo]
  have one : ∀ sp ∈ p.L, TOk s zo sp ∧ tval s zo sp = p.cm sp.t * (p.xw (p.arrOf sp.xs) j ^^^ p.scw (coefOff sp.t)).toNat := by
    intro sp hsp
    obtain ⟨hx', ht, hcl, hch⟩ := ok.terms sp hsp
    have hxs := (ok.srcs _ hx').1
    have ct : coefOff sp.t + 8 + 4 ≤ 3 * S p.W := by simp only [coefOff]; omega
    refine ⟨⟨ht, ?_, ?_, sr _ (by omega), sr _ (by omega), sr _ ct, ?_, ?_⟩, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxs ⊢
      rcases hxs with e | e | e <;> rw [e] <;> decide
    · rw [xa _ hx', hrd, hwr]
      exact ok.g.read (ok.src_fit hx' (by simp only [S]; omega))
    · rw [sv _ (by omega)]; exact hcl
    · rw [sv _ ct]; exact hch
    · simp only [tval, cmag]
      rw [sv _ (by omega), sv _ ct, sv _ (by simp only [coefOff]; omega), xa _ hx', hx _ hx']
  refine ⟨fun sp h => (one sp h).1, fun row => ?_⟩
  have : ∀ L : List TSpec, (∀ sp ∈ L, sp ∈ p.L) → tsum s zo row L = p.tw row j L := by
    intro L hL
    induction L with
    | nil => rfl
    | cons a L ih =>
      simp only [tsum, Pass.tw]
      rw [(one a (hL a (by simp))).2, ih fun x hx => hL x (by simp [hx])]
  exact this _ fun _ h => h

end Pass.Ok

namespace Pass.Ok
variable {p : Pass} {σ : State} {Z N : Nat}

theorem out_lt (ok : p.Ok σ Z N) (row : Bool) : p.out row < bT1 := (ok.srcs _ (ok.out_src row)).2.1

theorem out_ne (ok : p.Ok σ Z N) {row row' : Bool} (h : row ≠ row') : p.out row ≠ p.out row' := by
  cases row <;> cases row' <;> first | exact absurd rfl h | exact ok.outs | exact ok.outs.symm

/-- Rows' sums: below `2^64` at each word. -/
theorem acc_fit (ok : p.Ok σ Z N) (row : Bool) (j c : Nat) (hc : c < 2 ^ 32) : c + p.tw row j p.L < 2 ^ 64 := by
  have := Pass.tw_le p row j p.L
  have := ok.csum row
  have : p.csum row p.L * (2 ^ 32 - 1) ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul_right _ (by omega)
  omega

/-- A word of an output array after a store into one. -/
theorem w32_store (ok : p.Ok σ Z N) (m : Mem) {row row' : Bool} {j j' : Nat} (hj : j ≤ p.k) (hj' : j' ≤ p.k)
    (v : BitVec 32) :
    w32 (m.writeW (off (State.addr p.B) (arr p.W (p.out row') + 4 * j')) v) (State.addr p.B) (arr p.W (p.out row) + 4 * j) =
      if row = row' ∧ j = j' then v.toNat else w32 m (State.addr p.B) (arr p.W (p.out row) + 4 * j) := by
  have hk := ok.g.kle
  have f := ok.g.arr_fit (Nat.lt_of_lt_of_le (ok.out_lt row) (by simp only [bT1]; have := ok.hN; omega))
  have f' := ok.g.arr_fit (Nat.lt_of_lt_of_le (ok.out_lt row') (by simp only [bT1]; have := ok.hN; omega))
  have nw : (State.addr p.B).toNat + Z ≤ 2 ^ 32 := by rw [VG.Proof.X25519.Arm.addr_toNat]; exact ok.g.nowrap
  split
  · obtain ⟨rfl, rfl⟩ := ‹row = row' ∧ j = j'›
    exact w32_write_self _ _ _ _
  · rename_i h
    refine w32_write_ne nw (by simp only [S] at f'; omega) (by simp only [S] at f; omega) ?_ v
    by_cases e : row = row'
    · subst e
      have : j ≠ j' := fun e' => h ⟨rfl, e'⟩
      omega
    · have := arr_disj (w := p.W) (ok.out_ne e); simp only [S] at this; omega

/-- A store into an output array's word keeps the frame. -/
theorem keep_store (ok : p.Ok σ Z N) (m : Mem) {row : Bool} {j : Nat} (hj : j ≤ p.k) (v : BitVec 32) :
    Keep p.B p.W [p.out false, p.out true] [] m (m.writeW (off (State.addr p.B) (arr p.W (p.out row) + 4 * j)) v) := by
  have hk := ok.g.kle
  have f := ok.g.arr_fit (Nat.lt_of_lt_of_le (ok.out_lt row) (by simp only [bT1]; have := ok.hN; omega))
  have := ok.g.nowrap
  exact Keep.of_arr (n := 4) (writeW32_outside m _ v (by simp only [S] at f; omega))
    (by simp only [S]; omega) (by cases row <;> simp)

/-- Scratch words under a frame of the output arrays. -/
theorem scr_keep (ok : p.Ok σ Z N) {m : Mem} (h : Keep p.B p.W [p.out false, p.out true] [] p.mI m) {d : Nat}
    (hd : d + 4 ≤ 3 * S p.W) : m.readW (off (State.addr p.B) (arr p.W bT1 + d)) 32 = p.scw d := by
  apply BitVec.eq_of_toNat_eq
  refine Keep.above h (fun j hj => ?_) (by have := ok.scr_fit hd; have := ok.g.nowrap; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl <;> exact Nat.le_trans (arr_end (ok.out_lt _)) (Nat.le_add_right _ _)

/-- Source words under a frame of the output arrays: those above the outputs' written words. -/
theorem src_keep (ok : p.Ok σ Z N) {m : Mem} (h : Keep p.B p.W [p.out false, p.out true] [] p.mI m)
    {i j : Nat} (hij : i ≤ j) (hj : j ≤ p.k)
    (hhigh : ∀ row j, i ≤ j → j ≤ p.k → w32 m (State.addr p.B) (arr p.W (p.out row) + 4 * j) =
      w32 p.mI (State.addr p.B) (arr p.W (p.out row) + 4 * j))
    {r : Reg} (hr : r ∈ p.srcs) :
    m.readW (off (State.addr p.B) (arr p.W (p.arrOf r) + 4 * j)) 32 = p.xw (p.arrOf r) j := by
  apply BitVec.eq_of_toNat_eq
  have hk := ok.g.kle
  by_cases e : p.arrOf r = p.out false ∨ p.arrOf r = p.out true
  · rcases e with e | e
    · rw [e]; exact hhigh false j hij hj
    · rw [e]; exact hhigh true j hij hj
  · simp only [not_or] at e
    refine Keep.word h (by simp only [S]; omega) (fun x hx => ?_) (by simp) (ok.g.fit64 (ok.arr_lt hr))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact fun h' => e.1 h'.symm
    · exact fun h' => e.2 h'.symm

end Pass.Ok

namespace Pass.Ok
variable {p : Pass} {σ : State} {Z N : Nat}

theorem src_reg (ok : p.Ok σ Z N) {r : Reg} (hr : r ∈ p.srcs) : r ∉ tClob ∧ r ≠ .lr ∧ r ≠ .r12 := by
  have := (ok.srcs r hr).1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl <;> decide

theorem out_reg (row : Bool) : (if row then Reg.r1 else Reg.r0) ∉ ([.r6, rlo row, rhi row] : List Reg) ∧
    (if row then Reg.r1 else Reg.r0) ∉ ([.r6, rlo (!row), rhi (!row)] : List Reg) := by
  cases row <;> decide

/-- The pass's first word: the terms at word 0 and the outputs' words 0, then the count. -/
theorem word0 (ok : p.Ok σ Z N) {is : List Instr} {Q : State → Prop}
    (k : ∀ s, p.Inv σ 1 s → WP isa (.block is) s Q) :
    WP isa (.block (tcode 0 p.L ++ (out0 .r0 .r2 .r3 ++ (out0 .r1 .r4 .r5 ++ (.ldr .lr .r12 8 :: is))))) σ Q := by
  have hk := ok.g.kle
  have hk0 := ok.g.kpos
  have hW := ok.hW
  obtain ⟨tok, tv⟩ := ok.terms_at (zo := 0) (o := 0) (j := 0) rfl (Nat.zero_le _) rfl rfl rfl
    (fun r hr => by rw [(ok.srcs r hr).2.2, Nat.add_zero])
    (fun r hr => by rw [ok.mem])
    (fun d _ => by rw [ok.mem])
  refine terms_ok (by decide) p.L tok fun s1 m1 r1 v1 => ?_
  -- The rows' sums at word 0.
  have a1 : ∀ row, acc s1 row = p.rs row 1 := fun row => by
    rw [v1 row, tv row]
    simp only [acc, acc64, Pass.rs, Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
    rw [ok.lo row, ok.hi row, show (0 : BitVec 32).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
    exact Nat.mod_eq_of_lt (ok.acc_fit row 0 _ (by rw [← ok.lo row]; exact BitVec.isLt _))
  have ptr1 : ∀ r ∈ p.srcs, s1.gpr r = p.B + BitVec.ofNat 32 (arr p.W (p.arrOf r)) := fun r hr =>
    (r1.gpr r (ok.src_reg hr).1).trans (ok.srcs r hr).2.2
  have ea : ∀ row, State.addr (s1.gpr (if row then .r1 else .r0) + BitVec.ofNat 32 0) =
      off (State.addr p.B) (arr p.W (p.out row) + 4 * 0) := fun row => by
    rw [ptr1 _ (ok.out_src row), ok.addr_at (by have := ok.src_fit (ok.out_src row) (d := 0) (by simp only [S]; omega); omega)]
  have wa : ∀ (s : State), s.wr = σ.wr → ∀ row (j : Nat), j ≤ p.k →
      InRegions s.wr (off (State.addr p.B) (arr p.W (p.out row) + 4 * j)) 4 := fun s hs row j hj => by
    rw [hs]; exact ok.g.write (by have := ok.src_fit (ok.out_src row) (d := 4 * j) (by simp only [S]; omega); omega)
  refine out0_ok (by decide) (by decide) (by decide) (ea false) (wa _ r1.wr false 0 (Nat.zero_le _))
    fun s2 m2 l2 h2 r2 => ?_
  refine out0_ok (a0 := off (State.addr p.B) (arr p.W (p.out true) + 4 * 0)) (by decide) (by decide) (by decide)
    (by rw [r2.gpr _ (by decide)]; exact ea true) (wa _ (r2.wr.trans r1.wr) true 0 (Nat.zero_le _))
    fun s3 m3 l3 h3 r3 => ?_
  have k3 : Keep p.B p.W [p.out false, p.out true] [] p.mI s3.mem := by
    rw [m3, m2, m1, ← ok.mem]
    exact (ok.keep_store _ (Nat.zero_le _) _).trans (ok.keep_store _ (Nat.zero_le _) _)
  have e12 : s3.gpr .r12 = σ.gpr .r12 := by
    rw [r3.gpr _ (by decide), r2.gpr _ (by decide), r1.gpr _ (by decide)]
  refine wp_ldr (a := off (State.addr p.B) (arr p.W bT1 + 8)) (by decide)
    (by rw [e12, ok.r12]; exact ok.addr_at (by have := ok.scr_fit (d := 8) (by simp only [S]; omega); omega))
    (by rw [r3.rd, r2.rd, r1.rd, r3.wr, r2.wr, r1.wr]
        exact ok.g.read (ok.scr_fit (d := 8) (by simp only [S]; omega))) fun s4 u4 => ?_
  have m4 : s4.mem = s3.mem := u4.mem
  have rr : Rest (tClob ++ (.lr :: p.srcs)) σ s4 :=
    (r1.mono fun r h => List.mem_append_left _ h).trans <| (r2.mono (by simp)).trans <|
      (r3.mono (by simp)).trans (u4.rest (by simp))
  -- Words of the outputs.
  have wv : ∀ row j, j ≤ p.k → w32 s4.mem (State.addr p.B) (arr p.W (p.out row) + 4 * j) =
      if j = 0 then ((s1.gpr (rlo row)) >>> 30).toNat else w32 p.mI (State.addr p.B) (arr p.W (p.out row) + 4 * j) := by
    intro row j hj
    rw [m4, m3, ok.w32_store _ hj (Nat.zero_le _), m2, ok.w32_store _ hj (Nat.zero_le _), m1, ok.mem]
    have l23 : s2.gpr .r4 = s1.gpr .r4 := r2.gpr _ (by decide)
    cases row <;> by_cases e : j = 0 <;> simp [e, l23, rlo]
  have lohi : ∀ row, (s1.gpr (rlo row)).toNat = p.rs row 1 % 2 ^ 32 ∧ (s1.gpr (rhi row)).toNat = p.rs row 1 / 2 ^ 32 :=
    fun row => by
      have := a1 row; simp only [acc, acc64] at this
      have := (s1.gpr (rlo row)).isLt
      omega
  obtain ⟨lf, hf⟩ := lohi false
  obtain ⟨lt, ht⟩ := lohi true
  simp only [rlo, rhi, Bool.false_eq_true, ↓reduceIte] at lf hf lt ht
  refine k s4 ⟨rr, fun r hr => ?_, ?_, fun row => ?_, fun row => ?_, m4 ▸ k3, fun row j hj hjk => ?_, fun row => ?_⟩
  · have hr3 := (ok.srcs r hr).1
    have e := (ok.srcs r hr).2.2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr3
    rcases hr3 with rfl | rfl | rfl <;>
    · rw [u4.other _ (by decide), r3.gpr _ (by decide), r2.gpr _ (by decide), r1.gpr _ (by decide), e]
      simp
  · rw [u4.gpr, ok.scr_keep k3 (by simp only [S]; omega), ok.kw, Nat.add_sub_cancel]
  · cases row <;> simp only [rlo, Bool.false_eq_true, ↓reduceIte, Nat.mul_one]
    · rw [u4.other _ (by decide), r3.gpr _ (by decide), l2, hf]
    · rw [u4.other _ (by decide), l3, r2.gpr _ (by decide), ht]
  · cases row <;> simp only [rhi, Bool.false_eq_true, ↓reduceIte]
    · rw [u4.other _ (by decide), r3.gpr _ (by decide), h2]
    · rw [u4.other _ (by decide), h3]
  · simp only [wv row j hjk, show ¬ j = 0 by omega, ↓reduceIte]
  · simp only [val32, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
    have := wv row 0 (Nat.zero_le _)
    simp only [Nat.mul_zero, Nat.add_zero, ↓reduceIte] at this
    rw [this, toNat_shr, (lohi row).1]

end Pass.Ok

/-- The top word of `(S mod 2^(32 i)) / 2^30` is below 4. -/
theorem low_top {m : Mem} {base : Addr} {d n S : Nat}
    (hV : val32 m base d (n + 1) = S % 2 ^ (32 * (n + 1)) / 2 ^ 30) : w32 m base (d + 4 * n) < 4 := by
  rw [val32_succ, pow32_succ] at hV
  exact (stepM (T := 0) (by rw [hV]) (val32_lt _ _ _ _)).1

/-- A row's low words after a step. -/
theorem low_step {m m' : Mem} {base : Addr} {d n S T lo : Nat}
    (hlo : lo = (S / 2 ^ (32 * (n + 1)) + T) % 2 ^ 32)
    (hV : val32 m base d (n + 1) = S % 2 ^ (32 * (n + 1)) / 2 ^ 30)
    (hlow : ∀ j < n, w32 m' base (d + 4 * j) = w32 m base (d + 4 * j))
    (hw0 : w32 m' base (d + 4 * n) = w32 m base (d + 4 * n) + 4 * (lo % 2 ^ 30))
    (hw1 : w32 m' base (d + 4 * (n + 1)) = lo / 2 ^ 30) :
    val32 m' base d (n + 2) = (S + T * 2 ^ (32 * (n + 1))) % 2 ^ (32 * (n + 2)) / 2 ^ 30 ∧
      (S + T * 2 ^ (32 * (n + 1))) / 2 ^ (32 * (n + 2)) = (S / 2 ^ (32 * (n + 1)) + T) / 2 ^ 32 := by
  rw [val32_succ, pow32_succ] at hV
  have st := stepM (T := T) (by rw [hV]) (val32_lt _ _ _ _)
  rw [val32_succ, val32_succ, val32_congr hlow, hw0, hw1, show 32 * (n + 2) = 32 * (n + 1 + 1) by omega]
  simp only [pow32_succ] at *
  rw [← hlo] at st
  refine ⟨?_, st.2.2⟩
  rw [← st.2.1, Nat.mul_add]

/-- The pointers' advance. -/
def incs (rs : List Reg) : List Instr := rs.map fun r => .dp .add r r (.imm 4)

theorem incs_ok : ∀ (rs : List Reg), rs.Nodup → ∀ {s : State} {is : List Instr} {Q : State → Prop},
    (∀ s', (∀ r ∈ rs, s'.gpr r = s.gpr r + 4) → Rest rs s s' → s'.mem = s.mem → WP isa (.block is) s' Q) →
    WP isa (.block (incs rs ++ is)) s Q
  | [], _, s, _, _, k => k s (by simp) (Rest.refl _ _) rfl
  | r :: rs, hnd, s, is, Q, k => by
    simp only [incs, List.map_cons, List.cons_append]
    refine wp_dp (op2_imm (by decide)) fun s1 u1 => ?_
    have hn := List.nodup_cons.mp hnd
    refine incs_ok rs hn.2 fun s' h' r' m' => k s' (fun x hx => ?_) ((u1.rest (by simp)).trans
      (r'.mono fun x hx => List.mem_cons_of_mem _ hx)) (m'.trans u1.mem)
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · rw [r'.gpr _ hn.1, u1.gpr]; rfl
    · rw [h' x hx, u1.other _ (fun e => hn.1 (e ▸ hx))]

/-- The body of a pass's loop. -/
def Pass.body (p : Pass) : List Instr :=
  tcode 4 p.L ++ (outW .r0 .r2 .r3 ++ (outW .r1 .r4 .r5 ++ (incs p.srcs ++ [.subs .lr .lr (.imm 1)])))

namespace Pass.Ok
variable {p : Pass} {σ : State} {Z N : Nat}

/-- One word of a pass's loop. -/
theorem body_ok (ok : p.Ok σ Z N) {s : State} {n : Nat} (I : p.Inv σ (n + 1) s) (hn : n + 1 ≤ p.k) :
    WP isa (.block p.body) s fun t => p.Inv σ (n + 2) t ∧ t.z = decide (n + 2 = p.k + 1) := by
  have hk := ok.g.kle
  have hW := ok.hW
  have nr : ∀ r, r ∉ ([.r0, .r1, .r11] : List Reg) → r ∉ tClob → r ≠ .lr → r ∉ tClob ++ (.lr :: p.srcs) := by
    intro r h1 h2 h3 hm
    rcases List.mem_append.mp hm with hm | hm
    · exact h2 hm
    rcases List.mem_cons.mp hm with hm | hm
    · exact h3 hm
    · exact h1 (ok.srcs r hm).1
  obtain ⟨tok, tv⟩ := ok.terms_at (zo := 4) (o := 4 * n) (j := n + 1) (by omega) hn I.rest.rd I.rest.wr
    (I.rest.gpr _ (nr .r12 (by decide) (by decide) (by decide))) (fun r hr => by rw [I.ptr r hr, Nat.add_sub_cancel])
    (fun r hr => ok.src_keep I.keep (Nat.le_refl _) hn I.high hr)
    (fun d hd => ok.scr_keep I.keep hd)
  simp only [Pass.body]
  refine terms_ok (by decide) p.L tok fun s1 m1 r1 v1 => ?_
  have a1 : ∀ row, acc s1 row = p.rs row (n + 1) / 2 ^ (32 * (n + 1)) + p.tw row (n + 1) p.L := fun row => by
    rw [v1 row, tv row]
    simp only [acc, acc64]
    rw [I.lo row, I.hi row, show (0 : BitVec 32).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
    exact Nat.mod_eq_of_lt (ok.acc_fit row _ _ (by rw [← I.lo row]; exact BitVec.isLt _))
  have lohi : ∀ row, (s1.gpr (rlo row)).toNat = (p.rs row (n + 1) / 2 ^ (32 * (n + 1)) + p.tw row (n + 1) p.L) % 2 ^ 32 ∧
      (s1.gpr (rhi row)).toNat = (p.rs row (n + 1) / 2 ^ (32 * (n + 1)) + p.tw row (n + 1) p.L) / 2 ^ 32 :=
    fun row => by
      have := a1 row; simp only [acc, acc64] at this
      have := (s1.gpr (rlo row)).isLt
      omega
  have ptr1 : ∀ r ∈ p.srcs, s1.gpr r = p.B + BitVec.ofNat 32 (arr p.W (p.arrOf r) + 4 * n) := fun r hr => by
    rw [r1.gpr r (ok.src_reg hr).1, I.ptr r hr, Nat.add_sub_cancel]
  have ofit : ∀ row (d : Nat), d + 4 ≤ S p.W → arr p.W (p.out row) + d + 4 ≤ Z := fun row d hd =>
    ok.src_fit (ok.out_src row) hd
  have ea : ∀ (t : State) (r : Reg) row (o : Nat), o ≤ 4 →
      t.gpr r = p.B + BitVec.ofNat 32 (arr p.W (p.out row) + 4 * n) →
      State.addr (t.gpr r + BitVec.ofNat 32 o) =
        off (State.addr p.B) (arr p.W (p.out row) + 4 * n + o) := fun t r row o ho h => by
    rw [h, ok.addr_at (by have := ofit row (4 * n + o) (by simp only [S]; omega); omega)]
  have wa : ∀ (t : State), t.wr = σ.wr → ∀ row (j : Nat), j ≤ p.k →
      InRegions t.wr (off (State.addr p.B) (arr p.W (p.out row) + 4 * j)) 4 := fun t ht row j hj => by
    rw [ht]; exact ok.g.write (by have := ofit row (4 * j) (by simp only [S]; omega); omega)
  have wr1 : s1.wr = σ.wr := r1.wr.trans I.rest.wr
  refine outW_ok (a0 := off (State.addr p.B) (arr p.W (p.out false) + 4 * n))
    (a1 := off (State.addr p.B) (arr p.W (p.out false) + 4 * (n + 1))) (by decide) (by decide) (by decide) (by decide)
    (by rw [ea s1 .r0 false 0 (by omega) (ptr1 _ ok.r0)]; rfl)
    (by rw [ea s1 .r0 false 4 (by omega) (ptr1 _ ok.r0)]; rfl)
    (wa _ wr1 false n (by omega)) (wa _ wr1 false (n + 1) hn) fun s2 m2 l2 h2 r2 => ?_
  have wr2 : s2.wr = σ.wr := r2.wr.trans wr1
  have p2 : s2.gpr .r1 = p.B + BitVec.ofNat 32 (arr p.W (p.out true) + 4 * n) := by
    rw [r2.gpr _ (by decide)]; exact ptr1 _ ok.r1
  refine outW_ok (a0 := off (State.addr p.B) (arr p.W (p.out true) + 4 * n))
    (a1 := off (State.addr p.B) (arr p.W (p.out true) + 4 * (n + 1))) (by decide) (by decide) (by decide) (by decide)
    (by rw [ea s2 .r1 true 0 (by omega) p2]; rfl)
    (by rw [ea s2 .r1 true 4 (by omega) p2]; rfl)
    (wa _ wr2 true n (by omega)) (wa _ wr2 true (n + 1) hn) fun s3 m3 l3 h3 r3 => ?_
  refine incs_ok p.srcs ok.nodup fun s4 v4 r4 m4 => ?_
  refine wp_subs (op2_imm (by decide)) fun s5 u5 z5 => WP.block_nil ?_
  have hn' : n ≤ p.k := by omega
  -- The output words.
  have rB : s2.mem.readW (off (State.addr p.B) (arr p.W (p.out true) + 4 * n)) 32 =
      s.mem.readW (off (State.addr p.B) (arr p.W (p.out true) + 4 * n)) 32 := by
    apply BitVec.eq_of_toNat_eq
    change w32 s2.mem _ _ = w32 s.mem _ _
    rw [m2, ok.w32_store _ hn' hn, ok.w32_store _ hn' hn', m1]
    simp
  have e4 : s2.gpr .r4 = s1.gpr .r4 := r2.gpr _ (by decide)
  have wv : ∀ row j, j ≤ p.k → w32 s5.mem (State.addr p.B) (arr p.W (p.out row) + 4 * j) =
      if j = n + 1 then ((s1.gpr (rlo row)) >>> 30).toNat
      else if j = n then (s.mem.readW (off (State.addr p.B) (arr p.W (p.out row) + 4 * n)) 32 ||| s1.gpr (rlo row) <<< 2).toNat
      else w32 s.mem (State.addr p.B) (arr p.W (p.out row) + 4 * j) := by
    intro row j hj
    rw [u5.mem, m4, m3, ok.w32_store _ hj hn, ok.w32_store _ hj hn', rB, e4, m2, ok.w32_store _ hj hn,
      ok.w32_store _ hj hn', m1]
    cases row <;> by_cases e1 : j = n + 1 <;> by_cases e0 : j = n <;> simp [e1, e0, rlo] <;> omega
  -- The registers.
  have nc : ∀ r ∈ p.srcs, s3.gpr r = s.gpr r := fun r hr => by
    have h3 := (ok.srcs r hr).1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h3
    rcases h3 with rfl | rfl | rfl <;> rw [r3.gpr _ (by decide), r2.gpr _ (by decide), r1.gpr _ (by decide)]
  have lr4 : s4.gpr .lr = s.gpr .lr := by
    rw [r4.gpr _ (ok.src_reg · |>.2.1 rfl), r3.gpr _ (by decide), r2.gpr _ (by decide), r1.gpr _ (by decide)]
  have rg4 : ∀ r, r ∉ p.srcs → r ≠ .lr → s5.gpr r = s3.gpr r := fun r h1 h2 => by
    rw [u5.other _ h2, r4.gpr _ h1]
  have nsrc : ∀ r, r ∉ ([.r0, .r1, .r11] : List Reg) → r ∉ p.srcs := fun r h h' => h (ok.srcs r h').1
  obtain ⟨lf, hf⟩ := lohi false
  obtain ⟨lt, ht⟩ := lohi true
  simp only [rlo, rhi, Bool.false_eq_true, ↓reduceIte] at lf hf lt ht
  have st : ∀ row, val32 s5.mem (State.addr p.B) (arr p.W (p.out row)) (n + 2) =
        p.rs row (n + 2) % 2 ^ (32 * (n + 2)) / 2 ^ 30 ∧
      p.rs row (n + 2) / 2 ^ (32 * (n + 2)) = (p.rs row (n + 1) / 2 ^ (32 * (n + 1)) + p.tw row (n + 1) p.L) / 2 ^ 32 := by
    intro row
    have top := low_top (I.low row)
    refine low_step (lohi row).1 (I.low row) (fun j hj => ?_) ?_ ?_
    · rw [wv row j (by omega)]; simp [show j ≠ n + 1 by omega, show j ≠ n by omega]
    · simp only [wv row n hn', show ¬ n = n + 1 by omega, ↓reduceIte]
      rw [or_shl2 _ _ top]
    · simp only [wv row (n + 1) hn, ↓reduceIte]
      rw [toNat_shr, (lohi row).1]
  refine ⟨⟨?_, fun r hr => ?_, ?_, fun row => ?_, fun row => ?_, ?_, fun row j hj hjk => ?_, fun row => (st row).1⟩, ?_⟩
  · exact I.rest.trans <| (r1.mono fun r h => List.mem_append_left _ h).trans <| (r2.mono (by simp)).trans <|
      (r3.mono (by simp)).trans <| (r4.mono fun r h => by simp [h]).trans (u5.rest (by simp))
  · rw [u5.other _ (ok.src_reg hr).2.1, v4 r hr, nc r hr, I.ptr r hr]
    show _ + BitVec.ofNat 32 4 = _
    rw [VG.Offset.add_add]; congr 2
  · rw [u5.gpr, lr4, I.cnt]
    show BitVec.ofNat 32 (p.k + 1 - (n + 1)) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  · rw [(st row).2]
    cases row <;> simp only [rlo, Bool.false_eq_true, ↓reduceIte]
    · rw [rg4 _ (nsrc _ (by decide)) (by decide), r3.gpr _ (by decide), l2, hf]
    · rw [rg4 _ (nsrc _ (by decide)) (by decide), l3, r2.gpr _ (by decide), ht]
  · cases row <;> simp only [rhi, Bool.false_eq_true, ↓reduceIte]
    · rw [rg4 _ (nsrc _ (by decide)) (by decide), r3.gpr _ (by decide), h2]
    · rw [rg4 _ (nsrc _ (by decide)) (by decide), h3]
  · rw [u5.mem, m4, m3, m2, m1]
    exact I.keep.trans ((((ok.keep_store _ hn' _).trans (ok.keep_store _ hn _)).trans
      (ok.keep_store _ hn' _)).trans (ok.keep_store _ hn _))
  · simp only [wv row j hjk, show ¬ j = n + 1 by omega, show ¬ j = n by omega, ↓reduceIte]
    exact I.high row j (by omega) hjk
  · have := ok.g.wle
    rw [z5, lr4, I.cnt]
    show (BitVec.ofNat 32 (p.k + 1 - (n + 1)) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), VG.Proof.X25519.Arm.ofNat_beq_zero (by omega)]
    simp only [decide_eq_decide]; omega

end Pass.Ok

namespace Pass.Ok
variable {p : Pass} {σ : State} {Z N : Nat}

/-- A pass's loop: words `1` to `k`. -/
theorem loop_ok (ok : p.Ok σ Z N) {s : State} (I : p.Inv σ 1 s) :
    WP isa (.loop (.block p.body) .ne) s (p.Inv σ (p.k + 1)) := by
  have hk := ok.g.kpos
  refine WP.loop (M := isa) (fun n t => ∃ i, i + n = p.k ∧ 0 < n ∧ p.Inv σ (i + 1) t) ?_ p.k s
    ⟨0, by omega, hk, I⟩
  rintro n t ⟨i, hin, hn, hi⟩
  refine WP.mono (body_ok ok hi (by omega)) fun u ⟨hu, hz⟩ => ?_
  by_cases he : i + 2 = p.k + 1
  · exact Or.inl ⟨by change some (!u.z) = some false; simp only [hz, he, decide_true, Bool.not_true],
      by rw [show p.k + 1 = i + 2 by omega]; exact hu⟩
  · exact Or.inr ⟨by change some (!u.z) = some true; simp only [hz, he, decide_false, Bool.not_false],
      n - 1, by omega, i + 1, by omega, by omega, hu⟩

/-- The rows' top words: the carries less the corrections. -/
theorem top_ok (ok : p.Ok σ Z N) {s : State} (I : p.Inv σ (p.k + 1) s) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Rest (tClob ++ (.lr :: p.srcs)) σ t → Keep p.B p.W [p.out false, p.out true] [] p.mI t.mem →
      (∀ row, val32 t.mem (State.addr p.B) (arr p.W (p.out row)) (p.k + 1) =
        p.rs row (p.k + 1) % 2 ^ (32 * (p.k + 1)) / 2 ^ 30 + 2 ^ (32 * p.k + 2) *
          ((BitVec.ofNat 32 (p.rs row (p.k + 1) / 2 ^ (32 * (p.k + 1))) - p.scw (corrOff (if row then 1 else 0))).toNat
            % 2 ^ 30)) →
      WP isa (.block is) t Q) :
    WP isa (.block (outTop .r0 .r2 0 ++ (outTop .r1 .r4 1 ++ is))) s Q := by
  have hk := ok.g.kle
  have hW := ok.hW
  have e12 : s.gpr .r12 = σ.gpr .r12 := I.rest.gpr _ (by
    intro hm
    rcases List.mem_append.mp hm with hm | hm
    · simp at hm
    rcases List.mem_cons.mp hm with hm | hm
    · simp at hm
    · have := (ok.srcs _ hm).1; simp at this)
  have ca : ∀ (t : State), t.gpr .r12 = σ.gpr .r12 → t.rd = σ.rd → t.wr = σ.wr → ∀ row : Nat, row ≤ 1 →
      InRegions (t.rd ++ t.wr) (State.addr (t.gpr .r12 + BitVec.ofNat 32 (corrOff row))) 4 ∧
      State.addr (t.gpr .r12 + BitVec.ofNat 32 (corrOff row)) = off (State.addr p.B) (arr p.W bT1 + corrOff row) :=
    fun t h12 hrd hwr row hr => by
      have hf := ok.scr_fit (d := corrOff row) (by simp only [corrOff, S]; omega)
      have ea : State.addr (t.gpr .r12 + BitVec.ofNat 32 (corrOff row)) = off (State.addr p.B) (arr p.W bT1 + corrOff row) := by
        rw [h12, ok.r12]; exact ok.addr_at (by omega)
      exact ⟨by rw [ea, hrd, hwr]; exact ok.g.read hf, ea⟩
  have ptr : ∀ row, s.gpr (if row then .r1 else .r0) = p.B + BitVec.ofNat 32 (arr p.W (p.out row) + 4 * p.k) := fun row => by
    rw [I.ptr _ (ok.out_src row), Nat.add_sub_cancel]
  have ofit : ∀ row (d : Nat), d + 4 ≤ S p.W → arr p.W (p.out row) + d + 4 ≤ Z := fun row d hd =>
    ok.src_fit (ok.out_src row) hd
  have ea : ∀ row, State.addr (s.gpr (if row then .r1 else .r0) + BitVec.ofNat 32 0) =
      off (State.addr p.B) (arr p.W (p.out row) + 4 * p.k) := fun row => by
    rw [ptr row, ok.addr_at (by have := ofit row (4 * p.k) (by simp only [S]; omega); omega), Nat.add_zero]
  have wa : ∀ (t : State), t.wr = σ.wr → ∀ row,
      InRegions t.wr (off (State.addr p.B) (arr p.W (p.out row) + 4 * p.k)) 4 := fun t ht row => by
    rw [ht]; exact ok.g.write (by have := ofit row (4 * p.k) (by simp only [S]; omega); omega)
  obtain ⟨c0, a0⟩ := ca s e12 I.rest.rd I.rest.wr 0 (by omega)
  refine outTop_ok (a0 := off (State.addr p.B) (arr p.W (p.out false) + 4 * p.k)) (by decide) (by decide)
    (by decide) (by simp only [corrOff]; omega) (ea false) (wa _ I.rest.wr false) c0 fun s1 m1 r1 => ?_
  have e12' : s1.gpr .r12 = σ.gpr .r12 := (r1.gpr _ (by decide)).trans e12
  obtain ⟨c1, a1⟩ := ca s1 e12' (r1.rd.trans I.rest.rd) (r1.wr.trans I.rest.wr) 1 (by omega)
  refine outTop_ok (a0 := off (State.addr p.B) (arr p.W (p.out true) + 4 * p.k)) (by decide) (by decide)
    (by decide) (by simp only [corrOff]; omega) (by rw [r1.gpr _ (by decide)]; exact ea true)
    (wa _ (r1.wr.trans I.rest.wr) true) c1 fun s2 m2 r2 => ?_
  have kp : Keep p.B p.W [p.out false, p.out true] [] p.mI s2.mem := by
    rw [m2, m1]; exact I.keep.trans ((ok.keep_store _ (Nat.le_refl _) _).trans (ok.keep_store _ (Nat.le_refl _) _))
  refine k s2 (I.rest.trans ((r1.mono (by simp)).trans (r2.mono (by simp)))) kp fun row => ?_
  have sc0 : sw s (corrOff 0) = p.scw (corrOff 0) := by
    simp only [sw]; rw [a0, ok.scr_keep I.keep (by simp only [corrOff, S]; omega)]
  have sc1 : sw s1 (corrOff 1) = p.scw (corrOff 1) := by
    simp only [sw]; rw [a1, m1, ok.scr_keep (I.keep.trans (ok.keep_store _ (Nat.le_refl _) _))
      (by simp only [corrOff, S]; omega)]
  have rB : s1.mem.readW (off (State.addr p.B) (arr p.W (p.out true) + 4 * p.k)) 32 =
      s.mem.readW (off (State.addr p.B) (arr p.W (p.out true) + 4 * p.k)) 32 := by
    apply BitVec.eq_of_toNat_eq
    change w32 s1.mem _ _ = w32 s.mem _ _
    rw [m1, ok.w32_store _ (Nat.le_refl _) (Nat.le_refl _)]
    simp
  have lo : ∀ row, s.gpr (rlo row) = BitVec.ofNat 32 (p.rs row (p.k + 1) / 2 ^ (32 * (p.k + 1))) := fun row => by
    rw [← I.lo row, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have e4 : s1.gpr .r4 = s.gpr .r4 := r1.gpr _ (by decide)
  have wv : ∀ j, j ≤ p.k → w32 s2.mem (State.addr p.B) (arr p.W (p.out row) + 4 * j) =
      if j = p.k then (s.mem.readW (off (State.addr p.B) (arr p.W (p.out row) + 4 * p.k)) 32 |||
        (BitVec.ofNat 32 (p.rs row (p.k + 1) / 2 ^ (32 * (p.k + 1))) - p.scw (corrOff (if row then 1 else 0))) <<< 2).toNat
      else w32 s.mem (State.addr p.B) (arr p.W (p.out row) + 4 * j) := by
    intro j hj
    rw [m2, ok.w32_store _ hj (Nat.le_refl _), rB, e4, sc1, m1, ok.w32_store _ hj (Nat.le_refl _), sc0]
    have l0 := lo false
    have l1 := lo true
    simp only [rlo, Bool.false_eq_true, ↓reduceIte] at l0 l1
    cases row <;> by_cases e : j = p.k <;> simp [e, l0, l1]
  have top := low_top (n := p.k) (I.low row)
  have lowk : val32 s2.mem (State.addr p.B) (arr p.W (p.out row)) p.k =
      val32 s.mem (State.addr p.B) (arr p.W (p.out row)) p.k :=
    val32_congr fun j hj => by rw [wv j (by omega)]; simp [show j ≠ p.k by omega]
  have hw : (s.mem.readW (off (State.addr p.B) (arr p.W (p.out row) + 4 * p.k)) 32).toNat =
      w32 s.mem (State.addr p.B) (arr p.W (p.out row) + 4 * p.k) := rfl
  have wk := wv p.k (Nat.le_refl _)
  simp only [↓reduceIte] at wk
  rw [val32_succ, lowk, wk, or_shl2 _ _ top, hw, ← I.low row, val32_succ, Nat.pow_add,
    show (2 : Nat) ^ 2 = 4 from rfl]
  generalize (2 : Nat) ^ (32 * p.k) = P
  rw [Nat.mul_add, Nat.mul_assoc]; omega

end Pass.Ok

/-! ## A row's value -/

/-- The top word less the correction, modulo `2^30`. -/
theorem sub_mod30 (h C : Nat) (hC : C < 2 ^ 32) :
    (((BitVec.ofNat 32 h - BitVec.ofNat 32 C).toNat % 2 ^ 30 : Nat) : Int) = ((h : Int) - C) % 2 ^ 30 := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hC]
  omega

/-- A row's output, `(R mod 2^L) / 2^30 + 2^(L - 30) ((R / 2^L - C) mod 2^30)`, is `V / 2^30` modulo `2^L`
(`Q = 2^L = 2^30 P`) for `R = V + C 2^L` and `V` a multiple of `2^30`. -/
theorem out_val {P Q R C : Nat} {V : Int} (hQ : Q = 2 ^ 30 * P) (hR : (R : Int) = V + C * Q)
    (hdiv : (2 : Int) ^ 30 ∣ V) (hC : C < 2 ^ 32) :
    ((R % Q / 2 ^ 30 + P * ((BitVec.ofNat 32 (R / Q) - BitVec.ofNat 32 C).toNat % 2 ^ 30) : Nat) : Int) % Q =
      V / 2 ^ 30 % Q := by
  have e1 : ((R % Q / 2 ^ 30 + P * ((BitVec.ofNat 32 (R / Q) - BitVec.ofNat 32 C).toNat % 2 ^ 30) : Nat) : Int) =
      ((R % Q / 2 ^ 30 : Nat) : Int) + (P : Int) * ((((R / Q : Nat) : Int) - C) % 2 ^ 30) := by
    rw [Int.natCast_add, Int.natCast_mul, sub_mod30 _ _ hC]
  rw [e1]
  have hS := Nat.div_add_mod R Q
  generalize R / Q = h at *
  generalize R % Q = r at *
  have hQi : (Q : Int) = 2 ^ 30 * P := by rw [hQ, Int.natCast_mul, Int.natCast_pow]; rfl
  have hRi : (R : Int) = Q * h + r := by rw [← hS, Int.natCast_add, Int.natCast_mul]
  have hV : V = (Q : Int) * ((h : Int) - C) + r := by rw [Int.mul_sub]; grind
  have hr : (2 : Int) ^ 30 ∣ (r : Int) := by
    have : (2 : Int) ^ 30 ∣ (Q : Int) * ((h : Int) - C) := by rw [hQi, Int.mul_assoc]; exact Int.dvd_mul_right _ _
    exact (Int.dvd_add_right this).mp (hV ▸ hdiv)
  obtain ⟨r', hr'⟩ := hr
  have er : ((r / 2 ^ 30 : Nat) : Int) = r' := by
    rw [Int.natCast_ediv, hr', Int.natCast_pow]
    exact Int.mul_ediv_cancel_left _ (by decide)
  have eV : V / 2 ^ 30 = P * ((h : Int) - C) + r' := by
    rw [hV, hQi, hr', Int.mul_assoc, ← Int.mul_add]
    exact Int.mul_ediv_cancel_left _ (by decide)
  rw [er, eV]
  have := Int.emod_add_mul_ediv ((h : Int) - C) (2 ^ 30)
  generalize ((h : Int) - C) % 2 ^ 30 = a at *
  generalize ((h : Int) - C) / 2 ^ 30 = b at *
  rw [← this, Int.mul_add, ← Int.mul_assoc, Int.mul_comm (P : Int) (2 ^ 30), ← hQi, Int.add_comm _ r',
    ← Int.add_assoc, Int.add_mul_emod_self_left, Int.add_comm]

namespace Pass

/-- A source's low `n` words XORed with a mask. -/
def xv (p : Pass) (a : Nat) (M : BitVec 32) : Nat → Nat
  | 0 => 0
  | n + 1 => xv p a M n + (p.xw a n ^^^ M).toNat * 2 ^ (32 * n)

/-- A row's terms over the low `n` words. -/
def rowv (p : Pass) (row : Bool) (n : Nat) : List TSpec → Nat
  | [] => 0
  | sp :: L => (if sp.row = row then p.cm sp.t * p.xv (p.arrOf sp.xs) (p.scw (coefOff sp.t)) n else 0) + rowv p row n L

theorem rowv_succ (p : Pass) (row : Bool) (n : Nat) :
    ∀ L, p.rowv row (n + 1) L = p.rowv row n L + p.tw row n L * 2 ^ (32 * n)
  | [] => by simp only [rowv, tw, Nat.zero_mul, Nat.add_zero]
  | sp :: L => by
    simp only [rowv, tw, xv, rowv_succ p row n L]
    split <;> grind

theorem rs_eq (p : Pass) (row : Bool) : ∀ n, p.rs row n = p.init row + p.rowv row n p.L
  | 0 => by
    simp only [rs]
    suffices ∀ L, p.rowv row 0 L = 0 by rw [this, Nat.add_zero]
    intro L; induction L with
    | nil => rfl
    | cons sp L ih => simp [rowv, xv, ih]
  | n + 1 => by rw [rs, rs_eq p row n, rowv_succ, Nat.add_assoc]

theorem xv_zero (p : Pass) (a : Nat) : ∀ n, p.xv a 0 n = val32 p.mI (State.addr p.B) (arr p.W a) n
  | 0 => rfl
  | n + 1 => by
    have z : ∀ x : BitVec 32, x ^^^ (0 : BitVec 32) = x := fun x => by simp
    rw [xv, xv_zero p a n, val32_succ, z, Nat.mul_comm (2 ^ _)]

theorem xv_ones (p : Pass) (a : Nat) : ∀ n, p.xv a (BitVec.allOnes 32) n + 1 + val32 p.mI (State.addr p.B) (arr p.W a) n = 2 ^ (32 * n)
  | 0 => rfl
  | n + 1 => by
    have ih := xv_ones p a n
    rw [xv, val32_succ, pow32_succ]
    have hx : (p.xw a n ^^^ BitVec.allOnes 32).toNat = 2 ^ 32 - 1 - (p.xw a n).toNat := by
      rw [BitVec.xor_allOnes, BitVec.toNat_not]
    rw [hx]
    have hw := (p.xw a n).isLt
    have e : (p.xw a n).toNat = w32 p.mI (State.addr p.B) (arr p.W a + 4 * n) := rfl
    rw [e] at hw ⊢
    generalize w32 p.mI (State.addr p.B) (arr p.W a + 4 * n) = w at *
    generalize 2 ^ (32 * n) = P at *
    generalize p.xv a (BitVec.allOnes 32) n = A at *
    have h1 : (2 ^ 32 - 1 - w) * P + (1 + w) * P = 2 ^ 32 * P := by rw [← Nat.add_mul]; congr 1; omega
    rw [Nat.add_mul, Nat.one_mul] at h1
    rw [Nat.mul_comm P w]
    omega

end Pass

/-- A term's value, signed: `|c| (X ^ m_c) + |c| [c < 0] - 2^L |c| [c < 0 ≠ X < 0] = c X`, for `X`'s low `L` bits
`Xn = X + 2^L [X < 0]`. -/
theorem term_signed {c X : Int} {L Xn xvv : Nat} (hXn : (Xn : Int) = X + if X < 0 then 2 ^ L else 0)
    (hxv : (xvv : Int) = if c < 0 then (2 : Int) ^ L - 1 - (Xn : Int) else (Xn : Int)) :
    (c.natAbs : Int) * xvv + (if c < 0 then (c.natAbs : Int) else 0) -
      (if (c < 0) ≠ (X < 0) then (c.natAbs : Int) else 0) * 2 ^ L = c * X := by
  have ha : (c.natAbs : Int) = if c < 0 then -c else c := by split <;> omega
  by_cases hc : c < 0 <;> by_cases hX : X < 0 <;> simp only [hc, hX, ↓reduceIte, ne_eq, not_true_eq_false,
    Int.add_zero] at hXn hxv ha ⊢
  · rw [hxv, ha, hXn]; grind
  · rw [hxv, ha, hXn]; grind
  · rw [hxv, ha, hXn]; grind
  · rw [hxv, ha, hXn]; grind

namespace Pass

/-- A row's coefficients' magnitudes where negative (its starting carry), where their sign differs
from their source's (its correction), and its signed value, for the coefficients `c` by slot and the
sources' values `X` by array. -/
def ninit (row : Bool) (c : Nat → Int) : List TSpec → Nat
  | [] => 0
  | sp :: L => (if sp.row = row ∧ c sp.t < 0 then (c sp.t).natAbs else 0) + ninit row c L

def ncorr (p : Pass) (row : Bool) (c : Nat → Int) (X : Nat → Int) : List TSpec → Nat
  | [] => 0
  | sp :: L => (if sp.row = row ∧ (c sp.t < 0) ≠ (X (p.arrOf sp.xs) < 0) then (c sp.t).natAbs else 0) +
      ncorr p row c X L

def sval (p : Pass) (row : Bool) (c : Nat → Int) (X : Nat → Int) : List TSpec → Int
  | [] => 0
  | sp :: L => (if sp.row = row then c sp.t * X (p.arrOf sp.xs) else 0) + sval p row c X L

theorem rowv_signed (p : Pass) (row : Bool) (n : Nat) (c : Nat → Int) (X : Nat → Int) :
    ∀ L : List TSpec,
    (∀ sp ∈ L, p.scw (coefOff sp.t) = (if c sp.t < 0 then BitVec.allOnes 32 else 0) ∧
      p.cm sp.t = (c sp.t).natAbs ∧
      (val32 p.mI (State.addr p.B) (arr p.W (p.arrOf sp.xs)) n : Int) =
        X (p.arrOf sp.xs) + if X (p.arrOf sp.xs) < 0 then 2 ^ (32 * n) else 0) →
    (p.rowv row n L : Int) + ninit row c L - (p.ncorr row c X L : Int) * 2 ^ (32 * n) = p.sval row c X L
  | [] => fun _ => by simp [rowv, ninit, ncorr, sval]
  | sp :: L => fun h => by
    have ih := rowv_signed p row n c X L fun x hx => h x (List.mem_cons_of_mem _ hx)
    obtain ⟨hm, hc, hX⟩ := h sp (by simp)
    simp only [rowv, ninit, ncorr, sval]
    by_cases hr : sp.row = row
    · simp only [hr, true_and, ↓reduceIte]
      have ts := term_signed (c := c sp.t) (X := X (p.arrOf sp.xs)) (L := 32 * n) hX
        (xvv := p.xv (p.arrOf sp.xs) (p.scw (coefOff sp.t)) n) (by
          rw [hm]
          split
          · have h' := congrArg (fun x : Nat => (x : Int)) (p.xv_ones (p.arrOf sp.xs) n)
            simp only [Int.natCast_add, Int.natCast_pow, Int.natCast_one] at h'
            have : ((2 : Nat) : Int) = 2 := rfl
            rw [this] at h'
            omega
          · rw [xv_zero])
      rw [hc]
      simp only [Int.natCast_add, Int.natCast_mul]
      have e1 : ((if c sp.t < 0 then (c sp.t).natAbs else 0 : Nat) : Int) = if c sp.t < 0 then ((c sp.t).natAbs : Int) else 0 := by
        split <;> rfl
      have e2 : ((if (c sp.t < 0) ≠ (X (p.arrOf sp.xs) < 0) then (c sp.t).natAbs else 0 : Nat) : Int) =
          if (c sp.t < 0) ≠ (X (p.arrOf sp.xs) < 0) then ((c sp.t).natAbs : Int) else 0 := by split <;> rfl
      rw [e1, e2, ← ts, ← ih, Int.add_mul]; omega
    · simp only [hr, false_and, ↓reduceIte, Nat.zero_add, Int.zero_add]
      exact ih

/-- A row's output: its signed value divided by `2^30`, modulo `2^(32 (k + 1))`. -/
theorem row_result (p : Pass) (row : Bool) (c X : Nat → Int)
    (hd : ∀ sp ∈ p.L, p.scw (coefOff sp.t) = (if c sp.t < 0 then BitVec.allOnes 32 else 0) ∧
      p.cm sp.t = (c sp.t).natAbs ∧
      (val32 p.mI (State.addr p.B) (arr p.W (p.arrOf sp.xs)) (p.k + 1) : Int) =
        X (p.arrOf sp.xs) + if X (p.arrOf sp.xs) < 0 then 2 ^ (32 * (p.k + 1)) else 0)
    (hinit : p.init row = ninit row c p.L)
    (hcorr : p.scw (corrOff (if row then 1 else 0)) = BitVec.ofNat 32 (p.ncorr row c X p.L))
    (hlt : p.ncorr row c X p.L < 2 ^ 32) (hdiv : (2 : Int) ^ 30 ∣ p.sval row c X p.L) {m : Mem}
    (hv : val32 m (State.addr p.B) (arr p.W (p.out row)) (p.k + 1) =
        p.rs row (p.k + 1) % 2 ^ (32 * (p.k + 1)) / 2 ^ 30 + 2 ^ (32 * p.k + 2) *
          ((BitVec.ofNat 32 (p.rs row (p.k + 1) / 2 ^ (32 * (p.k + 1))) - p.scw (corrOff (if row then 1 else 0))).toNat
            % 2 ^ 30)) :
    (val32 m (State.addr p.B) (arr p.W (p.out row)) (p.k + 1) : Int) % 2 ^ (32 * (p.k + 1)) =
      p.sval row c X p.L / 2 ^ 30 % 2 ^ (32 * (p.k + 1)) := by
  have hQ : 2 ^ (32 * (p.k + 1)) = 2 ^ 30 * 2 ^ (32 * p.k + 2) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hR : (p.rs row (p.k + 1) : Int) = p.sval row c X p.L + (p.ncorr row c X p.L : Int) * ((2 ^ (32 * (p.k + 1)) : Nat) : Int) := by
    have := p.rowv_signed row (p.k + 1) c X p.L hd
    rw [p.rs_eq, Int.natCast_add, hinit, Int.natCast_pow]
    have e2 : ((2 : Nat) : Int) = 2 := rfl
    rw [e2]; omega
  have := out_val (P := 2 ^ (32 * p.k + 2)) hQ hR hdiv hlt
  rw [hv, hcorr]
  have e : ((2 ^ (32 * (p.k + 1)) : Nat) : Int) = 2 ^ (32 * (p.k + 1)) := by
    rw [Int.natCast_pow]; rfl
  rw [← e, hQ]
  rw [hQ] at this
  exact this

end Pass

/-! ## The coefficients' preparation -/

/-- The sign mask of a word. -/
abbrev smask (x : BitVec 32) : BitVec 32 := if x.toInt < 0 then BitVec.allOnes 32 else 0

/-- A word's magnitude, as `absMask` leaves it. -/
abbrev wabs (x : BitVec 32) : BitVec 32 := (x ^^^ ((x >>> 31) - ((x >>> 31) <<< 1))) - ((x >>> 31) - ((x >>> 31) <<< 1))

theorem mask_val (x : BitVec 32) : (x >>> 31) - ((x >>> 31) <<< 1) = smask x := by
  have hs := sign_bit x
  have hm : x.toInt < 0 ↔ 2 ^ 31 ≤ x.toNat := by
    rw [BitVec.toInt_eq_toNat_cond]; have := x.isLt; split <;> omega
  simp only [smask]
  by_cases h : 2 ^ 31 ≤ x.toNat
  · have e1 : x >>> 31 = 1 := by apply BitVec.eq_of_toNat_eq; rw [hs]; simp only [h, ↓reduceIte]; rfl
    rw [e1]; simp only [hm.mpr h, ↓reduceIte]; decide
  · have e1 : x >>> 31 = 0 := by apply BitVec.eq_of_toNat_eq; rw [hs]; simp only [h, ↓reduceIte]; rfl
    rw [e1]; simp only [show ¬ x.toInt < 0 from fun h' => h (hm.mp h'), ↓reduceIte]; decide

/-- The preparation's workspace: `Gk` with `r12` at the scratch, `W ≥ 8` and `N ≥ 15`. -/
structure SG (s : State) (B : BitVec 32) (Z W k N : Nat) : Prop where
  g : Gk s B Z W k N
  hN : 15 ≤ N
  hW : 8 ≤ W
  r12 : s.gpr .r12 = B + BitVec.ofNat 32 (arr W bT1)

/-- The scratch word at byte `d`. -/
abbrev scr (m : Mem) (B : BitVec 32) (W d : Nat) : BitVec 32 := m.readW (off (State.addr B) (arr W bT1 + d)) 32

namespace SG
variable {s : State} {B : BitVec 32} {Z W k N : Nat}

theorem of {t : State} (h : SG s B Z W k N) {ws : List Reg} (r : Rest ws s t) (h7 : .r7 ∉ ws := by decide)
    (h8 : .r8 ∉ ws := by decide) (h9 : .r9 ∉ ws := by decide) (h12 : .r12 ∉ ws := by decide) : SG t B Z W k N :=
  ⟨h.g.rest r h7 h8 h9, h.hN, h.hW, (r.gpr _ h12).trans h.r12⟩

theorem fit (h : SG s B Z W k N) {d : Nat} (hd : d + 4 ≤ 120) : arr W bT1 + d + 4 ≤ Z := by
  have := h.g.fits
  have := h.hW
  have : arr W 14 ≤ arr W N := arr_mono (by have := h.hN; omega)
  simp only [bT1, arr, S] at *; omega

theorem addr (h : SG s B Z W k N) {d : Nat} (hd : d + 4 ≤ 120) :
    State.addr (s.gpr .r12 + BitVec.ofNat 32 d) = off (State.addr B) (arr W bT1 + d) := by
  rw [h.r12, VG.Offset.add_add]; exact h.g.addr (by have := h.fit hd; omega)

theorem str {is : List Instr} {Q : State → Prop} (h : SG s B Z W k N) {d : Nat} (hd : d + 4 ≤ 120) {t : Reg}
    (kk : ∀ s', VG.Proof.X25519.Arm.Mupd s s' (s.mem.writeW (off (State.addr B) (arr W bT1 + d)) (s.gpr t)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.str t .r12 d :: is)) s Q :=
  wp_str (by omega) (h.addr hd) (h.g.write (h.fit hd)) kk

theorem ldr {is : List Instr} {Q : State → Prop} (h : SG s B Z W k N) {d : Nat} (hd : d + 4 ≤ 120) {t : Reg}
    (kk : ∀ s', Upd s s' t (scr s.mem B W d) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr t .r12 d :: is)) s Q :=
  wp_ldr (by omega) (h.addr hd) (h.g.read (h.fit hd)) kk

/-- A store to the scratch keeps the other scratch words. -/
theorem scr_store (h : SG s B Z W k N) (m : Mem) {d d' : Nat} (hd : d + 4 ≤ 120) (hd' : d' + 4 ≤ 120)
    (hsep : d + 4 ≤ d' ∨ d' + 4 ≤ d) (v : BitVec 32) :
    scr (m.writeW (off (State.addr B) (arr W bT1 + d')) v) B W d = scr m B W d := by
  have := h.fit hd; have := h.fit hd'; have := h.g.nowrap
  exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

theorem scr_self (m : Mem) (d : Nat) (v : BitVec 32) :
    scr (m.writeW (off (State.addr B) (arr W bT1 + d)) v) B W d = v := Mem.readW_writeW_self32 _ _ _

/-- `scr_store` for aligned offsets. -/
theorem scr_ne (h : SG s B Z W k N) (m : Mem) {d d' : Nat} (hd : d + 4 ≤ 120 ∧ d' + 4 ≤ 120 ∧ d % 4 = 0 ∧ d' % 4 = 0)
    (hne : d ≠ d') (v : BitVec 32) :
    (m.writeW (off (State.addr B) (arr W bT1 + d')) v).readW (off (State.addr B) (arr W bT1 + d)) 32 =
      m.readW (off (State.addr B) (arr W bT1 + d)) 32 :=
  h.scr_store m hd.1 hd.2.1 (by omega) v

/-- A store to the scratch is in the arrays `bT1`, `bT2` and `bA1`. -/
theorem keep (h : SG s B Z W k N) (m : Mem) {d : Nat} (hd : d + 4 ≤ 120) (v : BitVec 32) :
    Keep B W [bT1, bT2, bA1] [] m (m.writeW (off (State.addr B) (arr W bT1 + d)) v) := by
  have hf := h.fit hd
  have := h.g.nowrap
  have wo := writeW32_outside m (State.addr B) (d := arr W bT1 + d) v (by omega)
  intro x hx
  refine wo x ?_
  simp only [ranges, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
  have := h.hW
  simp only [bT1, bT2, bA1, arr, S] at hx hd ⊢
  omega

/-- Array words below the scratch are kept. -/
theorem keep_word {m m' : Mem} (h : SG s B Z W k N) (hk : Keep B W [bT1, bT2, bA1] [] m m') {j d : Nat}
    (hj : j < bT1) (hd : d + 4 ≤ S W) : w32 m' (State.addr B) (arr W j + d) = w32 m (State.addr B) (arr W j + d) := by
  have := Outs.val32 (k := 1) (d := arr W j + d) hk (fun r hr => ?_)
    (by have := h.g.fit64 (j := j) (by simp only [bT1] at hj; have := h.hN; omega); omega)
  · simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  simp only [ranges, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  have e1 := arr_end (w := W) hj
  rcases hr with rfl | rfl | rfl
  · dsimp only; omega
  · have : arr W bT1 ≤ arr W bT2 := arr_mono (by decide)
    dsimp only; omega
  · have : arr W bT1 ≤ arr W bA1 := arr_mono (by decide)
    dsimp only; omega

end SG

namespace SG
variable {s : State} {B : BitVec 32} {Z W k N : Nat}

/-- The word at byte `d` of array `a`. -/
abbrev aword (m : Mem) (B : BitVec 32) (W a d : Nat) : BitVec 32 := m.readW (off (State.addr B) (arr W a + d)) 32

/-- `topMask a`: `r5 :=` the sign mask of word `k` of array `a`. -/
theorem topMask_ok (h : SG s B Z W k N) {a : Nat} (ha : a < bT1) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, t.gpr .r5 = smask (aword s.mem B W a (4 * k)) → Rest [.r3, .r5] s t → t.mem = s.mem →
      WP isa (.block is) t Q) :
    WP isa (.block (topMask a ++ is)) s Q := by
  have hk := h.g.kle
  have hW := h.g.wle
  simp only [topMask, List.append_assoc]
  refine h.g.ptr_ok (by decide) (by simp only [bT1] at ha; omega) fun t1 p1 r1 m1 g1 => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_dp (op2_lsl (by decide)) fun t2 u2 => ?_
  have fa : arr W a + 4 * k + 4 ≤ Z := by
    have := h.g.arr_fit (j := a) (by have := h.hN; simp only [bT1] at ha; omega); simp only [S] at this; omega
  have v2 : t2.gpr .r3 = B + BitVec.ofNat 32 (arr W a + 4 * k) := by
    rw [u2.gpr, dpVal, p1, r1.gpr _ (by decide), h.g.r9, BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have := h.g.nowrap
    rw [BitVec.toNat_add, toNat_shl, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  refine wp_ldr (a := off (State.addr B) (arr W a + 4 * k)) (by decide)
    (by rw [v2, BitVec.add_zero]; exact h.g.addr (by omega))
    (by rw [u2.rd, u2.wr, r1.rd, r1.wr]; exact h.g.read fa) fun t3 u3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t4 u4 => ?_
  refine wp_dp (op2_lsl (by decide)) fun t5 u5 => ?_
  refine kk t5 ?_ ((r1.mono (by simp)).trans <| (u2.rest (by simp)).trans <| (u3.rest (by simp)).trans <|
    (u4.rest (by simp)).trans (u5.rest (by simp))) (by rw [u5.mem, u4.mem, u3.mem, u2.mem, m1])
  rw [u5.gpr, dpVal, u4.gpr, u3.gpr, u2.mem, m1, ← mask_val]

/-- `ldCoef c`: `r1 :=` the coefficient `c`. -/
theorem ldCoef_ok (h : SG s B Z W k N) (c : Coef) (ha : c.arr < bT1) (ho : c.off + 4 ≤ S W) (ho' : c.off < 4096)
    {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, t.gpr .r1 = aword s.mem B W c.arr c.off → Rest [.r1, .r3] s t → t.mem = s.mem →
      WP isa (.block is) t Q) :
    WP isa (.block (ldCoef c ++ is)) s Q := by
  simp only [ldCoef, List.append_assoc]
  refine h.g.ptr_ok (by decide) (by simp only [bT1] at ha; omega) fun t1 p1 r1 m1 g1 => ?_
  have fa := h.g.arr_fit (j := c.arr) (by have := h.hN; simp only [bT1] at ha; omega)
  simp only [List.cons_append, List.nil_append]
  refine wp_ldr (a := off (State.addr B) (arr W c.arr + c.off)) ho'
    (by rw [p1, VG.Offset.add_add]; exact h.g.addr (by omega))
    (by rw [r1.rd, r1.wr]; exact h.g.read (by omega)) fun t2 u2 => ?_
  exact kk t2 (by rw [u2.gpr, m1]) ((r1.mono (by simp)).trans (u2.rest (by simp))) (by rw [u2.mem, m1])

end SG

namespace SG
variable {s : State} {B : BitVec 32} {Z W k N : Nat}

/-- The low half of a word. -/
abbrev lowh (x : BitVec 32) : BitVec 32 := x &&& ~~~((x >>> 16) <<< 16)

/-- `coefStore t`: the coefficient in `r1` to slot `t`: its sign mask (left in `r2`), and its magnitude's
halves; its magnitude left in `r1`. -/
theorem coefStore_ok (h : SG s B Z W k N) {t : Nat} (ht : t ≤ 5) {is : List Instr} {Q : State → Prop}
    (kk : ∀ u, u.gpr .r1 = wabs (s.gpr .r1) → u.gpr .r2 = smask (s.gpr .r1) → Rest [.r1, .r2, .r3] s u →
      u.mem = ((s.mem.writeW (off (State.addr B) (arr W bT1 + coefOff t)) (smask (s.gpr .r1))).writeW
        (off (State.addr B) (arr W bT1 + (coefOff t + 8))) (wabs (s.gpr .r1) >>> 16)).writeW
        (off (State.addr B) (arr W bT1 + (coefOff t + 4))) (lowh (wabs (s.gpr .r1))) →
      WP isa (.block is) u Q) :
    WP isa (.block (coefStore t ++ is)) s Q := by
  have c0 : coefOff t + 4 ≤ 120 := by simp only [coefOff]; omega
  have c8 : coefOff t + 8 + 4 ≤ 120 := by simp only [coefOff]; omega
  have c4 : coefOff t + 4 + 4 ≤ 120 := by simp only [coefOff]; omega
  simp only [coefStore, absMask, List.cons_append, List.nil_append]
  refine wp_mov (op2_lsr (by decide)) fun s1 u1 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  refine wp_dp (op2_reg _ _) fun s4 u4 => ?_
  have h4 : SG s4 B Z W k N := h.of ((u1.rest (by simp)).trans <| (u2.rest (by simp)).trans <|
    (u3.rest (by simp)).trans (u4.rest (ws := [.r1, .r2]) (by simp)))
  have m2 : s4.gpr .r2 = smask (s.gpr .r1) := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, dpVal, u1.gpr, ← mask_val]
  have m1 : s4.gpr .r1 = wabs (s.gpr .r1) := by
    rw [u4.gpr, dpVal, u3.gpr, dpVal, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide),
      u2.gpr, dpVal, u1.gpr]
  refine h4.str c0 fun s5 u5 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s6 u6 => ?_
  have h6 : SG s6 B Z W k N := h4.of ((u5.rest [.r3]).trans (u6.rest (by simp)))
  refine h6.str c8 fun s7 u7 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s8 u8 => ?_
  have h8 : SG s8 B Z W k N := h6.of ((u7.rest [.r3]).trans (u8.rest (by simp)))
  refine h8.str c4 fun s9 u9 => ?_
  have e1 : s6.gpr .r1 = wabs (s.gpr .r1) := by rw [u6.other _ (by decide), u5.gpr, m1]
  refine kk s9 ?_ ?_ ?_ ?_
  · rw [u9.gpr, u8.other _ (by decide), u7.gpr, e1]
  · rw [u9.gpr, u8.other _ (by decide), u7.gpr, u6.other _ (by decide), u5.gpr, m2]
  · exact (u1.rest (by simp)).trans <| (u2.rest (by simp)).trans <| (u3.rest (by simp)).trans <|
      (u4.rest (by simp)).trans <| (u5.rest _).trans <| (u6.rest (by simp)).trans <| (u7.rest _).trans <|
      (u8.rest (by simp)).trans (u9.rest _)
  · have v3a : s6.gpr .r3 = wabs (s.gpr .r1) >>> 16 := by rw [u6.gpr, u5.gpr, m1]
    have v3b : s8.gpr .r3 = lowh (wabs (s.gpr .r1)) := by
      rw [u8.gpr, dpVal, u7.gpr, u6.other _ (by decide), v3a, u5.gpr, m1]
    rw [u9.mem, v3b, u8.mem, u7.mem, v3a, u6.mem, u5.mem, m2, u4.mem, u3.mem, u2.mem, u1.mem]

/-- `corrAdd`: the coefficient's correction (sign mask `r2`, source's `r5`, magnitude `r1`) to `r4`,
and its starting carry to `r10`. -/
theorem corrAdd_ok {is : List Instr} {Q : State → Prop}
    (kk : ∀ u, u.gpr .r4 = s.gpr .r4 + ((s.gpr .r2 ^^^ s.gpr .r5) &&& s.gpr .r1) →
      u.gpr .r10 = s.gpr .r10 + (s.gpr .r1 &&& s.gpr .r2) → Rest [.r3, .r4, .r10] s u → u.mem = s.mem →
      WP isa (.block is) u Q) :
    WP isa (.block (corrAdd ++ is)) s Q := by
  simp only [corrAdd, List.cons_append, List.nil_append]
  refine wp_dp (op2_reg _ _) fun s1 u1 => ?_
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  refine wp_dp (op2_reg _ _) fun s4 u4 => ?_
  refine wp_dp (op2_reg _ _) fun s5 u5 => ?_
  refine kk s5 ?_ ?_ ?_ (by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem])
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, dpVal, u2.other .r4 (by decide),
      u1.other .r4 (by decide), u2.gpr, dpVal, u1.gpr, dpVal, u1.other .r1 (by decide)]
  · rw [u5.gpr, dpVal, u4.gpr, dpVal, u4.other .r10 (by decide), u3.other .r10 (by decide),
      u2.other .r10 (by decide), u1.other .r10 (by decide), u3.other .r1 (by decide), u2.other .r1 (by decide),
      u1.other .r1 (by decide), u3.other .r2 (by decide), u2.other .r2 (by decide), u1.other .r2 (by decide)]
  · exact (u1.rest (by simp)).trans <| (u2.rest (by simp)).trans <| (u3.rest (by simp)).trans <|
      (u4.rest (by simp)).trans (u5.rest (by simp))

end SG

namespace SG
variable {s : State} {B : BitVec 32} {Z W k N : Nat}

/-- A scratch store. -/
abbrev wr (m : Mem) (B : BitVec 32) (W d : Nat) (v : BitVec 32) : Mem := m.writeW (off (State.addr B) (arr W bT1 + d)) v

/-- A coefficient's three scratch stores. -/
abbrev wrC (m : Mem) (B : BitVec 32) (W t : Nat) (x : BitVec 32) : Mem :=
  wr (wr (wr m B W (coefOff t) (smask x)) B W (coefOff t + 8) (wabs x >>> 16)) B W (coefOff t + 4) (lowh (wabs x))

/-- An array word below the scratch, after stores to the scratch. -/
theorem aword_keep (h : SG s B Z W k N) {m m' : Mem} (hk : Keep B W [bT1, bT2, bA1] [] m m') {j d : Nat}
    (hj : j < bT1) (hd : d + 4 ≤ S W) : aword m' B W j d = aword m B W j d :=
  BitVec.eq_of_toNat_eq (h.keep_word hk hj hd)

theorem keepC (h : SG s B Z W k N) (m : Mem) {t : Nat} (ht : t ≤ 5) (x : BitVec 32) :
    Keep B W [bT1, bT2, bA1] [] m (wrC m B W t x) := by
  have c0 : coefOff t + 4 ≤ 120 := by simp only [coefOff]; omega
  have c8 : coefOff t + 8 + 4 ≤ 120 := by simp only [coefOff]; omega
  have c4 : coefOff t + 4 + 4 ≤ 120 := by simp only [coefOff]; omega
  exact ((h.keep _ c0 _).trans (h.keep _ c8 _)).trans (h.keep _ c4 _)

/-- `rowPrep`: a row's two coefficients (`c₁` on array `x`, `c₂` on `y`) to slots `t₁` and `t₂`, its
correction and its starting carry. -/
theorem rowPrep_ok (h : SG s B Z W k N) {x y t₁ t₂ row : Nat} {c₁ c₂ : Coef} (hx : x < bT1) (hy : y < bT1)
    (hc₁ : c₁.arr < bT1) (hc₂ : c₂.arr < bT1) (ho₁ : c₁.off ≤ 8) (ho₂ : c₂.off ≤ 8) (ht₁ : t₁ ≤ 5) (ht₂ : t₂ ≤ 5)
    (hr : row ≤ 1) {is : List Instr} {Q : State → Prop}
    (kk : ∀ u, SG u B Z W k N → Rest [.r1, .r2, .r3, .r4, .r5, .r10] s u →
      u.mem = wr (wr (wrC (wrC s.mem B W t₁ (aword s.mem B W c₁.arr c₁.off)) B W t₂ (aword s.mem B W c₂.arr c₂.off))
        B W (corrOff row)
          (0 + ((smask (aword s.mem B W c₁.arr c₁.off) ^^^ smask (aword s.mem B W x (4 * k))) &&&
              wabs (aword s.mem B W c₁.arr c₁.off)) +
            ((smask (aword s.mem B W c₂.arr c₂.off) ^^^ smask (aword s.mem B W y (4 * k))) &&&
              wabs (aword s.mem B W c₂.arr c₂.off))))
        B W (carryOff row)
          (0 + (wabs (aword s.mem B W c₁.arr c₁.off) &&& smask (aword s.mem B W c₁.arr c₁.off)) +
            (wabs (aword s.mem B W c₂.arr c₂.off) &&& smask (aword s.mem B W c₂.arr c₂.off))) →
      WP isa (.block is) u Q) :
    WP isa (.block (rowPrep x y c₁ c₂ t₁ t₂ row ++ is)) s Q := by
  have hW := h.hW
  have hS : 8 + 4 ≤ S W := by simp only [S]; omega
  have hk4 : 4 * k + 4 ≤ S W := by have := h.g.kle; simp only [S]; omega
  simp only [rowPrep, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  refine wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have h2 : SG s2 B Z W k N := h.of ((u1.rest (ws := [.r4, .r10]) (by simp)).trans (u2.rest (by simp)))
  have m2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  refine h2.topMask_ok hx fun s3 v3 r3 m3 => ?_
  have h3 := h2.of r3
  refine h3.ldCoef_ok c₁ hc₁ (by omega) (by omega) fun s4 v4 r4 m4 => ?_
  have h4 := h3.of r4
  refine h4.coefStore_ok ht₁ fun s5 a5 m5 r5 mm5 => ?_
  have h5 := h4.of r5
  refine corrAdd_ok fun s6 c6 d6 r6 mm6 => ?_
  have h6 := h5.of r6
  have k6 : Keep B W [bT1, bT2, bA1] [] s.mem s6.mem := by
    rw [mm6, mm5, m4, m3, m2]; exact h.keepC _ ht₁ _
  refine h6.topMask_ok hy fun s7 v7 r7 m7 => ?_
  have h7 := h6.of r7
  refine h7.ldCoef_ok c₂ hc₂ (by omega) (by omega) fun s8 v8 r8 m8 => ?_
  have h8 := h7.of r8
  refine h8.coefStore_ok ht₂ fun s9 a9 m9 r9 mm9 => ?_
  have h9 := h8.of r9
  refine corrAdd_ok fun s10 c10 d10 r10 mm10 => ?_
  have h10 := h9.of r10
  refine h10.str (by simp only [corrOff]; omega) fun s11 u11 => ?_
  have h11 := h10.of (u11.rest [])
  refine h11.str (by simp only [carryOff]; omega) fun s12 u12 => ?_
  refine kk s12 (h11.of (u12.rest [])) ?_ ?_
  · exact (u1.rest (by simp)).trans <| (u2.rest (by simp)).trans <| (r3.mono (by simp)).trans <|
      (r4.mono (by simp)).trans <| (r5.mono (by simp)).trans <| (r6.mono (by simp)).trans <|
      (r7.mono (by simp)).trans <| (r8.mono (by simp)).trans <| (r9.mono (by simp)).trans <|
      (r10.mono (by simp)).trans <| (u11.rest _).trans (u12.rest _)
  · -- The values.
    have e4 : s4.gpr .r1 = aword s.mem B W c₁.arr c₁.off := by rw [v4, m3, m2]
    have e3 : s3.gpr .r5 = smask (aword s.mem B W x (4 * k)) := by rw [v3, m2]
    have e7 : s7.gpr .r5 = smask (aword s.mem B W y (4 * k)) := by
      rw [v7, h.aword_keep k6 hy hk4]
    have e8 : s8.gpr .r1 = aword s.mem B W c₂.arr c₂.off := by
      rw [v8, m7, h.aword_keep k6 hc₂ (by omega)]
    have g5 : s5.gpr .r4 = 0 ∧ s5.gpr .r5 = smask (aword s.mem B W x (4 * k)) ∧ s5.gpr .r10 = 0 :=
      ⟨by rw [r5.gpr _ (by decide), r4.gpr _ (by decide), r3.gpr _ (by decide), u2.other _ (by decide), u1.gpr],
       by rw [r5.gpr _ (by decide), r4.gpr _ (by decide), e3],
       by rw [r5.gpr _ (by decide), r4.gpr _ (by decide), r3.gpr _ (by decide), u2.gpr]⟩
    have g6 : s6.gpr .r4 = 0 + ((smask (aword s.mem B W c₁.arr c₁.off) ^^^ smask (aword s.mem B W x (4 * k))) &&&
          wabs (aword s.mem B W c₁.arr c₁.off)) ∧
        s6.gpr .r10 = 0 + (wabs (aword s.mem B W c₁.arr c₁.off) &&& smask (aword s.mem B W c₁.arr c₁.off)) :=
      ⟨by rw [c6, g5.1, g5.2.1, m5, a5, e4], by rw [d6, g5.2.2, m5, a5, e4]⟩
    have g9 : s9.gpr .r4 = s6.gpr .r4 ∧ s9.gpr .r5 = smask (aword s.mem B W y (4 * k)) ∧ s9.gpr .r10 = s6.gpr .r10 :=
      ⟨by rw [r9.gpr _ (by decide), r8.gpr _ (by decide), r7.gpr _ (by decide)],
       by rw [r9.gpr _ (by decide), r8.gpr _ (by decide), e7],
       by rw [r9.gpr _ (by decide), r8.gpr _ (by decide), r7.gpr _ (by decide)]⟩
    have g10r4 := c10
    have g10r10 := d10
    rw [g9.1, g9.2.1, m9, a9, e8, g6.1] at g10r4
    rw [g9.2.2, m9, a9, e8, g6.2] at g10r10
    have mm8 : s8.mem = wrC s.mem B W t₁ (aword s.mem B W c₁.arr c₁.off) := by
      rw [m8, m7, mm6, mm5, m4, m3, m2, e4]
    rw [u12.mem, u11.gpr, u11.mem, mm10, mm9, e8, mm8, g10r4, g10r10]

end SG

/-! ## `md`: the multiple of `m` -/

/-- A word's value modulo `2^32` from its signed value. -/
theorem toNat_cong (x : BitVec 32) : (x.toNat : Int) = x.toInt % 2 ^ 32 := by
  rw [BitVec.toInt_eq_toNat_cond]; have := x.isLt; split <;> omega

/-- A word's signed value from its value modulo `2^32`, in range. -/
theorem toInt_of_cong {x : BitVec 32} {i : Int} (h : (x.toNat : Int) = i % 2 ^ 32) (hr : -2 ^ 31 ≤ i ∧ i < 2 ^ 31) :
    x.toInt = i := by
  rw [BitVec.toInt_eq_toNat_cond]; have := x.isLt; split <;> omega

theorem cong_add {a b : BitVec 32} {A B : Int} (ha : (a.toNat : Int) = A % 2 ^ 32) (hb : (b.toNat : Int) = B % 2 ^ 32) :
    ((a + b).toNat : Int) = (A + B) % 2 ^ 32 := by
  rw [BitVec.toNat_add]; omega

theorem cong_sub {a b : BitVec 32} {A B : Int} (ha : (a.toNat : Int) = A % 2 ^ 32) (hb : (b.toNat : Int) = B % 2 ^ 32) :
    ((a - b).toNat : Int) = (A - B) % 2 ^ 32 := by
  rw [BitVec.toNat_sub]; omega

theorem cong_mul {a b : BitVec 32} {A B : Int} (ha : (a.toNat : Int) = A % 2 ^ 32) (hb : (b.toNat : Int) = B % 2 ^ 32) :
    ((a * b).toNat : Int) = (A * B) % 2 ^ 32 := by
  have e2 : ((2 ^ 32 : Nat) : Int) = 2 ^ 32 := rfl
  rw [BitVec.toNat_mul, Int.natCast_emod, Int.natCast_mul, ha, hb, e2, ← Int.mul_emod]

theorem low30 (x : BitVec 32) : (x &&& ~~~(BitVec.ofNat 32 0xC0000000)).toNat = x.toNat % 2 ^ 30 := by
  rw [show ~~~(BitVec.ofNat 32 0xC0000000) = BitVec.ofNat 32 (2 ^ 30 - 1) by decide, BitVec.toNat_and,
    BitVec.toNat_ofNat, show (2 ^ 30 - 1) % 2 ^ 32 = 2 ^ 30 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]

theorem and_smask (c t : BitVec 32) : (c &&& smask t) = if t.toInt < 0 then c else 0 := by
  simp only [smask]; split
  · exact BitVec.and_allOnes
  · simp

/-- `mdPrep`'s multiple: `md₀ - ((md₀ - np (u d₀ + v e₀)) mod 2^30)`, for `md₀` the coefficients of the
negative inputs, is `mdOf`. -/
theorem md_word {c1 c2 dt et d0 e0 np : BitVec 32} {d e : Int}
    (hd0 : (d0.toNat : Int) = d % 2 ^ 32) (he0 : (e0.toNat : Int) = e % 2 ^ 32)
    (hds : dt.toInt < 0 ↔ d < 0) (hes : et.toInt < 0 ↔ e < 0)
    (huv : c1.toInt.natAbs + c2.toInt.natAbs ≤ 2 ^ 30) :
    ((c1 &&& smask dt) + (c2 &&& smask et) -
        (((c1 &&& smask dt) + (c2 &&& smask et) - (c2 * e0 + c1 * d0) * np) &&& ~~~(BitVec.ofNat 32 0xC0000000))).toInt =
      VG.Proof.Divstep.mdOf 30 np.toNat c1.toInt c2.toInt d e := by
  have hu := toNat_cong c1
  have hv := toNat_cong c2
  have hn : (np.toNat : Int) = (np.toNat : Int) % 2 ^ 32 := by have := np.isLt; omega
  have h0 : ((0 : BitVec 32).toNat : Int) = (0 : Int) % 2 ^ 32 := rfl
  have m1 : ((c1 &&& smask dt).toNat : Int) = (if d < 0 then c1.toInt else 0) % 2 ^ 32 := by
    rw [and_smask]; by_cases h : d < 0
    · simp only [hds.mpr h, h, ↓reduceIte]; exact hu
    · simp only [show ¬ dt.toInt < 0 from fun h' => h (hds.mp h'), h, ↓reduceIte]; exact h0
  have m2 : ((c2 &&& smask et).toNat : Int) = (if e < 0 then c2.toInt else 0) % 2 ^ 32 := by
    rw [and_smask]; by_cases h : e < 0
    · simp only [hes.mpr h, h, ↓reduceIte]; exact hv
    · simp only [show ¬ et.toInt < 0 from fun h' => h (hes.mp h'), h, ↓reduceIte]; exact h0
  have mm := cong_add m1 m2
  have sS := cong_add (cong_mul hv he0) (cong_mul hu hd0)
  have X := cong_sub mm (cong_mul sS hn)
  generalize hX : (c1 &&& smask dt) + (c2 &&& smask et) - (c2 * e0 + c1 * d0) * np = Xw at X
  have hx : ((Xw &&& ~~~(BitVec.ofNat 32 0xC0000000)).toNat : Int) =
      ((if d < 0 then c1.toInt else 0) + (if e < 0 then c2.toInt else 0) - np.toNat * (c1.toInt * d + c2.toInt * e)) %
        2 ^ 30 := by
    rw [low30, Int.natCast_emod, X]
    have : (c2.toInt * e + c1.toInt * d) * (np.toNat : Int) = (np.toNat : Int) * (c1.toInt * d + c2.toInt * e) := by
      rw [Int.mul_comm, Int.add_comm]
    rw [this]; omega
  have hr := cong_sub mm (b := Xw &&& ~~~(BitVec.ofNat 32 0xC0000000))
    (B := ((if d < 0 then c1.toInt else 0) + (if e < 0 then c2.toInt else 0) -
      np.toNat * (c1.toInt * d + c2.toInt * e)) % 2 ^ 30) (by rw [hx]; omega)
  unfold VG.Proof.Divstep.mdOf
  simp only
  refine toInt_of_cong hr ?_
  have := Int.emod_nonneg ((if d < 0 then c1.toInt else 0) + (if e < 0 then c2.toInt else 0) -
    np.toNat * (c1.toInt * d + c2.toInt * e)) (show (2 : Int) ^ 30 ≠ 0 by decide)
  have := Int.emod_lt_of_pos ((if d < 0 then c1.toInt else 0) + (if e < 0 then c2.toInt else 0) -
    np.toNat * (c1.toInt * d + c2.toInt * e)) (show (0 : Int) < 2 ^ 30 by decide)
  constructor <;> split <;> split <;> omega

namespace SG
variable {s : State} {B : BitVec 32} {Z W k N : Nat}

/-- `ptr r3 j` and a load from it. -/
theorem ldArr_ok (h : SG s B Z W k N) {j d : Nat} (hj : j < bT1) (hd : d + 4 ≤ S W) (hd' : d < 4096) {dst : Reg}
    {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, t.gpr dst = aword s.mem B W j d → Rest [.r3, dst] s t → t.mem = s.mem → WP isa (.block is) t Q) :
    WP isa (.block (ptr .r3 j ++ (.ldr dst .r3 d :: is))) s Q := by
  refine h.g.ptr_ok (by decide) (by simp only [bT1] at hj; omega) fun t1 p1 r1 m1 g1 => ?_
  have fa := h.g.arr_fit (j := j) (by have := h.hN; simp only [bT1] at hj; omega)
  refine wp_ldr (a := off (State.addr B) (arr W j + d)) hd'
    (by rw [p1, VG.Offset.add_add]; exact h.g.addr (by omega))
    (by rw [r1.rd, r1.wr]; exact h.g.read (by omega)) fun t2 u2 => ?_
  exact kk t2 (by rw [u2.gpr, m1]) ((r1.mono (by simp)).trans (u2.rest (by simp))) (by rw [u2.mem, m1])

/-- `mdPrep`: a row's `md` (coefficients `c₁` on `d`, `c₂` on `e`) to slot `t`, its correction and starting
carry added to the row's. -/
theorem mdPrep_ok (h : SG s B Z W k N) {c₁ c₂ : Coef} {t row : Nat}
    (hc₁ : c₁.arr < bT1) (hc₂ : c₂.arr < bT1) (ho₁ : c₁.off ≤ 8) (ho₂ : c₂.off ≤ 8) (ht : t ≤ 5) (hr : row ≤ 1)
    {is : List Instr} {Q : State → Prop}
    (kk : ∀ u, SG u B Z W k N → Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r11] s u →
      let w₁ := aword s.mem B W c₁.arr c₁.off
      let w₂ := aword s.mem B W c₂.arr c₂.off
      let md0 := (w₁ &&& smask (aword s.mem B W bD (4 * k))) + (w₂ &&& smask (aword s.mem B W bE (4 * k)))
      let md := md0 - ((md0 - (w₂ * aword s.mem B W bE 0 + w₁ * aword s.mem B W bD 0) *
        s.mem.readW (off (State.addr B) sB) 32) &&& ~~~(BitVec.ofNat 32 0xC0000000))
      u.mem = wr (wr (wrC s.mem B W t md) B W (corrOff row) (scr s.mem B W (corrOff row) + (wabs md &&& smask md)))
        B W (carryOff row) (scr s.mem B W (carryOff row) + (wabs md &&& smask md)) →
      WP isa (.block is) u Q) :
    WP isa (.block (mdPrep c₁ c₂ t row ++ is)) s Q := by
  have hW := h.hW
  have hS : 8 + 4 ≤ S W := by simp only [S]; omega
  have hk4 : 4 * k + 4 ≤ S W := by have := h.g.kle; simp only [S]; omega
  have hdr : hdr ≤ Z := Nat.le_trans (Nat.le_add_right _ _) h.g.fits
  simp only [mdPrep, List.append_assoc, List.cons_append, List.nil_append]
  refine h.topMask_ok (by decide) fun s1 v1 r1 m1 => ?_
  have h1 := h.of r1
  refine h1.ldCoef_ok c₁ hc₁ (by omega) (by omega) fun s2 v2 r2 m2 => ?_
  have h2 := h1.of r2
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  have h3 := h2.of (u3.rest (ws := [.r0]) (by simp))
  refine h3.ldArr_ok (j := bD) (d := 0) (by decide) (by simp only [S]; omega) (by decide) fun s4 v4 r4 m4 => ?_
  have h4 := h3.of r4
  refine wp_mul fun s5 u5 => ?_
  have h5 := h4.of (u5.rest (ws := [.r11]) (by simp))
  refine h5.topMask_ok (by decide) fun s6 v6 r6 m6 => ?_
  have h6 := h5.of r6
  refine h6.ldCoef_ok c₂ hc₂ (by omega) (by omega) fun s7 v7 r7 m7 => ?_
  have h7 := h6.of r7
  refine wp_dp (op2_reg _ _) fun s8 u8 => ?_
  refine wp_dp (op2_reg _ _) fun s9 u9 => ?_
  have h9 := h7.of ((u8.rest (ws := [.r0, .r4]) (by simp)).trans (u9.rest (by simp)))
  refine h9.ldArr_ok (j := bE) (d := 0) (by decide) (by simp only [S]; omega) (by decide) fun s10 v10 r10 m10 => ?_
  have h10 := h9.of r10
  refine wp_mla fun s11 u11 => ?_
  have sBz : sB + 4 ≤ Z := by simp only [sB]; simp only [VG.Impl.Rsa.Arm.Keys.hdr] at hdr; omega
  have sBa : State.addr (s11.gpr .r8 + BitVec.ofNat 32 sB) = off (State.addr B) sB := by
    rw [u11.other _ (by decide), h10.g.r8]; exact h.g.addr (by omega)
  have sBr : InRegions (s11.rd ++ s11.wr) (off (State.addr B) sB) 4 := by
    rw [u11.rd, u11.wr]; exact h10.g.read sBz
  refine wp_ldr (a := off (State.addr B) sB) (by decide) sBa sBr fun s12 u12 => ?_
  refine wp_mul fun s13 u13 => ?_
  refine wp_dp (op2_reg _ _) fun s14 u14 => ?_
  refine wp_dp (op2_imm (by decide)) fun s15 u15 => ?_
  refine wp_dp (op2_reg _ _) fun s16 u16 => ?_
  have h16 := h10.of ((u11.rest (ws := [.r1, .r3, .r11]) (by simp)).trans <| (u12.rest (by simp)).trans <|
    (u13.rest (by simp)).trans <| (u14.rest (by simp)).trans <| (u15.rest (by simp)).trans (u16.rest (by simp)))
  refine h16.coefStore_ok ht fun s17 a17 m17 r17 mm17 => ?_
  have h17 := h16.of r17
  refine wp_dp (op2_reg _ _) fun s18 u18 => ?_
  have h18 := h17.of (u18.rest (ws := [.r3]) (by simp))
  refine h18.ldr (by simp only [corrOff]; omega) fun s19 u19 => ?_
  refine wp_dp (op2_reg _ _) fun s20 u20 => ?_
  have h20 := h18.of ((u19.rest (ws := [.r4]) (by simp)).trans (u20.rest (by simp)))
  refine h20.str (by simp only [corrOff]; omega) fun s21 u21 => ?_
  have h21 := h20.of (u21.rest [])
  refine h21.ldr (by simp only [carryOff]; omega) fun s22 u22 => ?_
  refine wp_dp (op2_reg _ _) fun s23 u23 => ?_
  have h23 := h21.of ((u22.rest (ws := [.r4]) (by simp)).trans (u23.rest (by simp)))
  refine h23.str (by simp only [carryOff]; omega) fun s24 u24 => ?_
  refine kk s24 (h23.of (u24.rest [])) ?_ ?_
  · exact (r1.mono (by simp)).trans <| (r2.mono (by simp)).trans <| (u3.rest (by simp)).trans <|
      (r4.mono (by simp)).trans <| (u5.rest (by simp)).trans <| (r6.mono (by simp)).trans <|
      (r7.mono (by simp)).trans <| (u8.rest (by simp)).trans <| (u9.rest (by simp)).trans <|
      (r10.mono (by simp)).trans <| (u11.rest (by simp)).trans <| (u12.rest (by simp)).trans <|
      (u13.rest (by simp)).trans <| (u14.rest (by simp)).trans <| (u15.rest (by simp)).trans <|
      (u16.rest (by simp)).trans <| (r17.mono (by simp)).trans <| (u18.rest (by simp)).trans <|
      (u19.rest (by simp)).trans <| (u20.rest (by simp)).trans <| (u21.rest _).trans <|
      (u22.rest (by simp)).trans <| (u23.rest (by simp)).trans (u24.rest _)
  · have ms : s16.mem = s.mem := by
      rw [u16.mem, u15.mem, u14.mem, u13.mem, u12.mem, u11.mem, m10, u9.mem, u8.mem, m7, m6, u5.mem, m4, u3.mem,
        m2, m1]
    have m3 : s3.mem = s.mem := by rw [u3.mem, m2, m1]
    have m9 : s9.mem = s.mem := by rw [u9.mem, u8.mem, m7, m6, u5.mem, m4, m3]
    -- The registers.
    have e2 : s2.gpr .r1 = aword s.mem B W c₁.arr c₁.off := by rw [v2, m1]
    have e3 : s3.gpr .r0 = aword s.mem B W c₁.arr c₁.off &&& smask (aword s.mem B W bD (4 * k)) := by
      rw [u3.gpr, dpVal, e2, r2.gpr _ (by decide), v1]
    have e5 : s5.gpr .r11 = aword s.mem B W c₁.arr c₁.off * aword s.mem B W bD 0 := by
      rw [u5.gpr, v4, r4.gpr _ (by decide), u3.other _ (by decide), e2, m3]
    have e7 : s7.gpr .r1 = aword s.mem B W c₂.arr c₂.off := by rw [v7, m6, u5.mem, m4, m3]
    have e9 : s9.gpr .r0 = (aword s.mem B W c₁.arr c₁.off &&& smask (aword s.mem B W bD (4 * k))) +
        (aword s.mem B W c₂.arr c₂.off &&& smask (aword s.mem B W bE (4 * k))) := by
      rw [u9.gpr, dpVal, u8.other _ (by decide), r7.gpr _ (by decide), r6.gpr _ (by decide), u5.other _ (by decide),
        r4.gpr _ (by decide), e3, u8.gpr, dpVal, e7, r7.gpr _ (by decide), v6, u5.mem, m4, m3]
    have e11 : s11.gpr .r11 = aword s.mem B W c₂.arr c₂.off * aword s.mem B W bE 0 +
        aword s.mem B W c₁.arr c₁.off * aword s.mem B W bD 0 := by
      rw [u11.gpr, v10, r10.gpr _ (by decide), u9.other _ (by decide), u8.other _ (by decide), e7, m9,
        r10.gpr _ (by decide), u9.other _ (by decide), u8.other _ (by decide), r7.gpr _ (by decide),
        r6.gpr _ (by decide), e5]
    have e15 : s15.gpr .r11 = (s9.gpr .r0 - s11.gpr .r11 * s.mem.readW (off (State.addr B) sB) 32) &&&
        ~~~(BitVec.ofNat 32 0xC0000000) := by
      rw [u15.gpr, dpVal, u14.gpr, dpVal, u13.other _ (by decide), u12.other _ (by decide), u11.other _ (by decide),
        r10.gpr _ (by decide), u13.gpr, u12.gpr, u12.other _ (by decide), u11.mem, m10, m9]
      rfl
    have e16 : s16.gpr .r1 = s9.gpr .r0 - s15.gpr .r11 := by
      rw [u16.gpr, dpVal, u15.other _ (by decide), u14.other _ (by decide), u13.other _ (by decide),
        u12.other _ (by decide), u11.other _ (by decide), r10.gpr _ (by decide)]
    rw [e15, e9, e11] at e16
    generalize hmd : s16.gpr .r1 = md at e16
    rw [e16] at hmd
    -- The scratch.
    have c19 : s19.gpr .r4 = scr s.mem B W (corrOff row) := by
      rw [u19.gpr, u18.mem, mm17, ms]
      simp (disch := (simp only [coefOff, corrOff, carryOff]; omega)) only [h.scr_ne]
    have c3 : s19.gpr .r3 = wabs (s16.gpr .r1) &&& smask (s16.gpr .r1) := by
      rw [u19.other _ (by decide), u18.gpr, dpVal, a17, m17]
    have c20 : s20.gpr .r4 = scr s.mem B W (corrOff row) + (wabs (s16.gpr .r1) &&& smask (s16.gpr .r1)) := by
      rw [u20.gpr, dpVal, c19, c3]
    have c22 : s22.gpr .r4 = scr s.mem B W (carryOff row) := by
      rw [u22.gpr, u21.mem, u20.mem, u19.mem, u18.mem, mm17, ms]
      simp (disch := (simp only [coefOff, corrOff, carryOff]; omega)) only [h.scr_ne]
    have c23 : s23.gpr .r4 = scr s.mem B W (carryOff row) + (wabs (s16.gpr .r1) &&& smask (s16.gpr .r1)) := by
      rw [u23.gpr, dpVal, c22, u22.other _ (by decide), u21.gpr, u20.other _ (by decide), c3]
    rw [u24.mem, u23.mem, u22.mem, u21.mem, u20.mem, u19.mem, u18.mem, mm17, ms, c23, c20, hmd]

end SG
