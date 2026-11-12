module

public import VerifiedGarbage.Impl.Rsa.Arm.Inverse
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Rsa.Arm.Inv.Geo
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
