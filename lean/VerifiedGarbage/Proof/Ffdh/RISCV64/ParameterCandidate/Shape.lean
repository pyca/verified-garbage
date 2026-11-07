module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.Base
meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Impl.RsaKeyGen.Primes
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.Sieve
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.WordCut
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.WordHalf
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.RsaKeyGen.Bits
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ffdh.RISCV64.Search

-- separate module: the candidate's shape checks, whose symbolic executions the tests' changes need not re-check

/-!
# An FFDH parameter candidate on RISC-V: the candidate and its shape

As on PPC64LE (`Proof/Ffdh/PPC64LE/ParameterCandidate/{Shape,Residue,Halve,MainShape}.lean`
and the shape checks of `Main.lean`): `shapeP_ok`, the first `out_len`
octets of the tape into array 0, cut to `bits` bits with its top and low
bits set (`candidateOf`); `residue_ok`, the generator's congruence;
`halveQ_ok`, q from p in place; `shape_iff`, the flags all clear exactly when
the specification's shape checks pass; and `MB`, p's working space with
`hBad` zero exactly when a proposition holds, through each check.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.ParameterCandidate

variable {C : Nat}

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Ffdh.RISCV64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.RISCV64.Steps (eval_zero eval_zero_ofNat)
open VG.Impl.MillerRabin.RISCV64.Search VG.Impl.Ffdh.RISCV64.Search
open VG.Proof.Ffdh.RISCV64.Search (rw_self frm_writeW shl3_ofNat smallMod_ok smRegs bad_post sieve_ok trRegs)
open VG.Impl.Bignum.RISCV64.Precompute (loadN)

theorem slot_zero (w : Nat) : slot w 0 = 256 := by simp [slot, hdrBytes]

/-! ## The candidate p -/

/-- The registers `shapeP` writes. -/
def shRegs : List Reg := [.s7, .s8, .a0, .s0, .t3, .t4, .t5]

/-- `shapeP`'s first block: the tape's address and `out_len`. -/
theorem shapeHead_ok {p : PP} {s : State} (h : St p s) :
    WP isa (.block [ldh .s7 hRand, ldh .s8 hLen]) s fun u => (u.gpr .s7 = off p.rp 0 ∧
      u.gpr .s8 = BitVec.ofNat 64 p.L ∧ u.mem = s.mem) ∧ Keep [.s7, .s8] s u := by
  refine WP.keep [.s7, .s8] ?_ (by rfl) (by rfl)
  simp only [ldh, hRand, hLen]
  brun [h.s6, h.ld (d := 136) (by decide), h.ld (d := 24) (by decide), h.al (d := 136) (by decide) (by decide),
    h.al (d := 24) (by decide) (by decide), h.args.rand', h.args.len', BitVec.add_zero]

theorem shapeP_ok {p : PP} {s : State} (h : St p s) (hp : Ph p p.bits C s) (hrl : p.L ≤ p.r.length) :
    WP isa shapeP s fun t =>
      (wv t.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) =
          Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)) ∧
        Frm p.B [(slot (wOf p.bits) 0, 8 * wOf p.bits)] s.mem t.mem) ∧ Keep shRegs s t := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hn := h.dims.n
  have hnw := h.scr.nowrap
  have h7 := hp.a7
  have h0 := hp.t0
  have htop := hp.topW
  generalize hwd : wOf p.bits = w at h7 h0 htop ⊢
  have hw8 : 8 ≤ w := by simp only [wOf] at hwd; omega_arith
  have hw128 : w ≤ 128 := by simp only [wOf] at hwd; omega_arith
  have hLw : p.L ≤ 8 * w := by simp only [wOf, PP.L] at hwd ⊢; omega_arith
  have hZ : slot w 0 + 8 * w ≤ p.Z := by simp only [slot, hdrBytes, PP.Z, PP.L] at hn ⊢; omega_arith
  have hL1 : 1 ≤ p.L := by simp only [PP.L]; omega_arith
  unfold shapeP
  refine WP.seq (WP.mono (shapeHead_ok h) fun u ⟨⟨u7, u8, um⟩, ku⟩ => ?_)
  have hrd : ∀ i < p.L, InRegions (u.rd ++ u.wr) (off p.rp i) 1 := fun i hi => by
    rw [ku.2.1, ku.2.2]; exact h.bufs.rdR i (by omega_arith)
  refine WP.seq (WP.mono (loadN_ok (h.scr.congr ku.2.2) ((ku.gpr (by decide)).trans h7) u7 u8
    ((ku.gpr (by decide)).trans h0) hL1 hLw (by omega_arith) (by simp [slot, hdrBytes]) (by simp [slot, hdrBytes]) hZ hrd
    (fun i hi => h.bufs.sepR i (by omega_arith))) fun v ⟨vv, vo, kv⟩ => ?_)
  have kuv := ku.trans kv
  rw [um, Pre.wordsVal_eq_wv, h.take_bytes hrl] at vv
  -- The top word's mask, from the header.
  have hk1 : 1 ≤ p.bits + 64 - 64 * w := by simp only [wOf] at hwd; omega_arith
  have hk2 : p.bits + 64 - 64 * w ≤ 64 := by simp only [wOf] at hwd; omega_arith
  generalize hkd : p.bits + 64 - 64 * w = k at htop hk1 hk2
  have tv : v.mem.readW (p.B + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (2 ^ k - 1) := by
    show word v.mem p.B 192 = _
    rw [Outside.word vo (by simp only [slot, hdrBytes]; omega_arith) (by omega_arith), um]; exact htop
  have e3 : off p.B (slot w 0 + 8 * w) - BitVec.ofNat 64 8 = off p.B (slot w 0 + 8 * (w - 1)) := by
    rw [off_sub _ (by omega_arith)]; congr 2; omega_arith
  have hsv : Scr v p.B p.Z := h.scr.congr kuv.2.2
  have sT : InRegions v.wr (off p.B (slot w 0 + 8 * (w - 1))) 8 := hsv.st (by omega_arith)
  have lT : InRegions (v.rd ++ v.wr) (off p.B (slot w 0 + 8 * (w - 1))) 8 := hsv.ld (by omega_arith)
  have aT : (off p.B (slot w 0 + 8 * (w - 1))).toNat % 8 = 0 := hsv.al8 (by omega_arith) (by simp only [slot, hdrBytes]; omega_arith)
  have sA : InRegions v.wr (off p.B (slot w 0)) 8 := hsv.st (by omega_arith)
  have lA : InRegions (v.rd ++ v.wr) (off p.B (slot w 0)) 8 := hsv.ld (by omega_arith)
  have aA : (off p.B (slot w 0)).toNat % 8 = 0 := hsv.al8 (by omega_arith) (by simp only [slot, hdrBytes]; omega_arith)
  have eA : ∀ x : BitVec 64, (v.mem.writeW (off p.B (slot w 0 + 8 * (w - 1))) x).readW (off p.B (slot w 0)) 64 =
      v.mem.readW (off p.B (slot w 0)) 64 := fun x => rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)
  have ebit : (BitVec.ofNat 64 (2 ^ k - 1)) >>> 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 (2 ^ (k - 1)) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega_arith⟩
    rw [Nat.add_sub_cancel, Nat.pow_succ]
    have : 2 ^ j ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega_arith)
    have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    generalize 2 ^ j = P at *
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    omega_arith
  have l192 : InRegions (v.rd ++ v.wr) (p.B + BitVec.ofNat 64 192) 8 := by
    rw [kuv.2.1, kuv.2.2]; exact h.ld (d := 192) (by decide)
  have a192 : (p.B + BitVec.ofNat 64 192).toNat % 8 = 0 := h.al (d := 192) (by decide) (by decide)
  refine WP.mono (WP.keep [.t3, .t4, .t5] (Q := fun t => t.mem =
      (v.mem.writeW (off p.B (slot w 0 + 8 * (w - 1)))
        ((v.mem.readW (off p.B (slot w 0 + 8 * (w - 1))) 64 &&& BitVec.ofNat 64 (2 ^ k - 1)) |||
          BitVec.ofNat 64 (2 ^ (k - 1)))).writeW (off p.B (slot w 0))
        (v.mem.readW (off p.B (slot w 0)) 64 ||| BitVec.ofNat 64 1)) ?_ (by rfl) (by rfl))
    fun t ⟨tm, kt⟩ => ⟨⟨?_, ?_⟩, (kuv.trans kt).mono (by decide)⟩
  · simp only [ldh, hTop]
    brun [(kuv.gpr (by decide)).trans h7, (kuv.gpr (by decide)).trans h0,
      (kuv.gpr (by decide)).trans h.s6, shl3_ofNat, e3, sT, lT, aT, sA, lA, aA, eA, l192, a192, tv, ebit,
      BitVec.add_zero, add_ofNat_zero]
  · have hb : 64 * (w - 1) + k = p.bits := by simp only [wOf] at hwd; omega_arith
    rw [← hb, ← vv]
    refine Proof.Ffdh.ParameterCandidate.wv_shape (by omega_arith) hk1 hk2 ?_ ?_ fun j hj0 hj => ?_
    · simp only [word, off] at tm ⊢; rw [tm, rw_self]; rfl
    · simp only [word, off] at tm ⊢
      rw [tm, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), rw_self]
    · simp only [word, off] at tm ⊢
      rw [tm, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
        rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
  · rw [um] at vo
    have hr : ∀ a, a + 8 ≤ 8 * w → ∃ r ∈ [(slot w 0, 8 * w)], r.1 ≤ slot w 0 + a ∧ slot w 0 + a + 8 ≤ r.1 + r.2 :=
      fun a ha => ⟨_, List.mem_singleton_self _, by dsimp only; omega_arith, by dsimp only; omega_arith⟩
    simp only [off] at tm
    rw [tm]
    have f1 := frm_writeW (Frm.of_outside vo (List.mem_singleton_self _)) (a := slot w 0 + 8 * (w - 1))
      ((v.mem.readW (p.B + BitVec.ofNat 64 (slot w 0 + 8 * (w - 1))) 64 &&& BitVec.ofNat 64 (2 ^ k - 1)) |||
        BitVec.ofNat 64 (2 ^ (k - 1))) (hr _ (by omega_arith)) (by omega_arith)
    have f2 := frm_writeW f1 (a := slot w 0 + 0)
      (v.mem.readW (p.B + BitVec.ofNat 64 (slot w 0)) 64 ||| BitVec.ofNat 64 1) (hr _ (by omega_arith)) (by omega_arith)
    simpa only [Nat.add_zero] using f2

/-! ## The generator's congruence -/

/-- The congruence the generator asks of p. -/
def goodRes (g x : Nat) : Prop := if g = 2 then x % 24 = 11 else x % 10 = 3 ∨ x % 10 = 7

/-- The registers `residue` writes. -/
def resRegs : List Reg := [.t3, .s1, .s0, .s2, .s3, .s4, .t4, .t5]

theorem res2 : ∀ r < 24, (BitVec.ofNat 64 r ^^^ BitVec.ofNat 64 11 = 0#64 ↔ r = 11) := by decide

theorem res5 : ∀ r < 10, ((BitVec.ofNat 64 r ||| BitVec.ofNat 64 4) ^^^ BitVec.ofNat 64 7 = 0#64 ↔ r = 3 ∨ r = 7) := by
  decide

theorem residue_ok {p : PP} {s : State} (h : St p s) (hp : Ph p p.bits C s) :
    WP isa residue s fun t =>
      ((word t.mem p.B (8 * hBad) = 0#64 ↔ goodRes p.g (wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits))) ∧
        Frm p.B [(8 * hBad, 8)] s.mem t.mem) ∧ Keep resRegs s t := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hn := h.dims.n
  have h7 := hp.a7
  have h0 := hp.t0
  generalize hwd : wOf p.bits = w at h7 h0 ⊢
  have hw8 : 8 ≤ w := by simp only [wOf] at hwd; omega_arith
  have hw128 : w ≤ 128 := by simp only [wOf] at hwd; omega_arith
  have hZ : slot w 0 + 8 * w ≤ p.Z := by simp only [slot, hdrBytes, PP.Z, PP.L] at hn ⊢; omega_arith
  generalize hx : wv s.mem p.B (slot w 0) w = x
  have kd : ∀ d, d < 2 ^ 11 → 2 ≤ d → ∀ (tail : List Instr) {u : State} (Q : State → Prop),
      St p u → u.gpr .a7 = off p.B (slot w 0) → u.gpr .t0 = BitVec.ofNat 64 w → u.mem = s.mem →
      (∀ t', t'.gpr .s0 = BitVec.ofNat 64 (x % d) → t'.mem = s.mem → St p t' →
        WP isa (.block tail) t' fun t => Q t ∧ Keep (.s1 :: smRegs) t' t) →
      WP isa (.seq (.block [.li .s1 d]) (.seq smallMod (.block tail))) u fun t => Q t ∧ Keep resRegs u t := by
    intro d hd hd2 tail u Q hu u7 u0 um ht
    have hli : WP isa (.block [.li .s1 d]) u fun v => ((v.gpr .s1 = BitVec.ofNat 64 d ∧ v.mem = u.mem) ∧
        Keep [.s1] u v) ∧ v.sp = u.sp := by
      refine WP.rdwr (WP.keep _ ?_ (by rfl) (by rfl)) |>.mono fun v ⟨a, _, _, b⟩ => ⟨a, b⟩
      brun [exec_li (show imm12 (d : Int) by unfold imm12; omega)]
      exact BitVec.ofInt_natCast 64 d
    refine WP.seq (WP.mono hli fun v ⟨⟨⟨v1, vm⟩, kv⟩, vsp⟩ => ?_)
    refine WP.seq (WP.mono (WP.rdwr (smallMod_ok (hu.scr.congr kv.2.2) ((kv.gpr (by decide)).trans u7)
      ((kv.gpr (by decide)).trans u0) v1 (by omega_arith) (by omega_arith) hZ (by simp [slot, hdrBytes]) hd2
      (by omega_arith))) fun t' ⟨⟨⟨t3, tm'⟩, kt'⟩, _, _, tsp'⟩ => ?_)
    rw [vm, um, hx] at t3
    have k3 := kv.trans kt'
    refine WP.mono (ht t' t3 (by rw [tm', vm, um]) (hu.step (by rw [tm', vm]; exact Frm.refl _ _ _) k3
      (tsp'.trans vsp))) fun t ⟨q, kt⟩ => ⟨q, (k3.trans kt).mono (by decide)⟩
  unfold residue
  refine WP.seq (WP.mono (WP.rdwr (WP.keep [.t3] (Q := fun u => u.gpr .t3 = BitVec.ofNat 64 p.g - BitVec.ofNat 64 2 ∧
      u.mem = s.mem)
    (by simp only [ldh, hGen]
        brun [h.s6, h.ld (d := 128) (by decide), h.al (d := 128) (by decide) (by decide), h.args.gen'])
    (by rfl) (by rfl))) fun u ⟨⟨⟨u3, um⟩, ku⟩, _, _, usp⟩ => ?_)
  have hu := h.step (by rw [um]; exact Frm.refl _ _ _) ku usp
  have u7 := (ku.gpr (by decide)).trans h7
  have u0 := (ku.gpr (by decide)).trans h0
  refine WP.ite (u.gpr .t3 == 0) (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · have hg : p.g = 2 := by
      rcases h.dims.g with hg | hg <;> rw [u3, hg] at hb
      · exact hg
      · exact absurd hb (by decide)
    refine WP.mono (kd 24 (by decide) (by decide) _ _ hu u7 u0 um fun t' t3 tm' ht' => ?_)
      fun t ⟨q, k⟩ => ⟨q, (ku.trans k).mono (by decide)⟩
    refine WP.mono (WP.keep [.s0] (Q := fun t => t.mem = s.mem.writeW (p.B + BitVec.ofNat 64 200)
      (BitVec.ofNat 64 (x % 24) ^^^ BitVec.ofNat 64 11)) ?_ (by rfl) (by rfl)) fun t ⟨tm, kt⟩ =>
        ⟨bad_post tm ?_, kt.mono (by decide)⟩
    · simp only [sth, hBad]
      brun [ht'.s6, ht'.st (d := 200) (by decide), ht'.al (d := 200) (by decide) (by decide), tm', t3]
    · rw [res2 _ (Nat.mod_lt _ (by decide)), goodRes, ite_eq_left hg]
  · have hg : p.g = 5 := by
      rcases h.dims.g with hg | hg <;> rw [u3, hg] at hb
      · exact absurd hb (by decide)
      · exact hg
    refine WP.mono (kd 10 (by decide) (by decide) _ _ hu u7 u0 um fun t' t3 tm' ht' => ?_)
      fun t ⟨q, k⟩ => ⟨q, (ku.trans k).mono (by decide)⟩
    refine WP.mono (WP.keep [.s0] (Q := fun t => t.mem = s.mem.writeW (p.B + BitVec.ofNat 64 200)
      ((BitVec.ofNat 64 (x % 10) ||| BitVec.ofNat 64 4) ^^^ BitVec.ofNat 64 7)) ?_ (by rfl) (by rfl))
      fun t ⟨tm, kt⟩ => ⟨bad_post tm ?_, kt.mono (by decide)⟩
    · simp only [sth, hBad]
      brun [ht'.s6, ht'.st (d := 200) (by decide), ht'.al (d := 200) (by decide) (by decide), tm', t3]
    · rw [res5 _ (Nat.mod_lt _ (by decide)), goodRes, ite_eq_right (by omega_arith)]

/-! ## q -/

theorem low_flag (x : BitVec 64) : (x &&& 1#64) ^^^ 1#64 = 0#64 ↔ x.toNat % 2 = 1 := by
  have e : x &&& 1#64 = BitVec.ofNat 64 (x.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.and_one_is_mod]
    omega_arith
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h] <;> decide

theorem wv_mod_two (m : Mem) (p : Addr) (d : Nat) {w : Nat} (hw : 1 ≤ w) :
    wv m p d w % 2 = (word m p d).toNat % 2 := by
  have e := VG.Proof.RsaKeyGen.testBit_wv m p d w 0 (by omega_arith)
  simp only [Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.zero_mod, Nat.testBit_zero, decide_eq_decide] at e
  omega_arith

/-- The registers `halveQ` writes. -/
def hqRegs : List Reg := [.t3, .t4, .t5, .t6]

/-- Word `j` of the halved number. -/
abbrev halfW (m : Mem) (B : Addr) (a j : Nat) : BitVec 64 :=
  (word m B (a + 8 * j) >>> 1) ||| (word m B (a + 8 * (j + 1)) <<< 63)

theorem halveQ_ok {p : PP} {s : State} {w x : Nat} (hs : St p s) (h7 : s.gpr .a7 = off p.B (slot w 0))
    (h0 : s.gpr .t0 = BitVec.ofNat 64 w) (hx : wv s.mem p.B (slot w 0) w = x) (hw2 : 2 ≤ w)
    (hw : w < 2 ^ 31) (hZ : slot w 0 + 8 * w ≤ p.Z) :
    WP isa halveQ s fun t =>
      (wv t.mem p.B (slot w 0) w = x / 2 ∧
        (word t.mem p.B (8 * hBad) = 0#64 ↔ word s.mem p.B (8 * hBad) = 0#64 ∧ x / 2 % 2 = 1) ∧
        Frm p.B [(slot w 0, 8 * w), (8 * hBad, 8)] s.mem t.mem) ∧ Keep hqRegs s t := by
  have hnw := hs.scr.nowrap
  rw [slot_zero] at h7 hx hZ ⊢
  simp only [PP.Z] at hZ hnw
  unfold halveQ
  refine WP.seq (WP.mono (WP.keep [.t3, .t4] (Q := fun u => u.gpr .t3 = off p.B 256 ∧
      u.gpr .t4 = BitVec.ofNat 64 (w - 1) ∧ u.mem = s.mem) ?_ (by rfl) (by rfl)) fun u ⟨⟨u3, u4, um⟩, ku⟩ => ?_)
  · brun [h7, h0, BitVec.add_zero, add_ofNat_zero]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  let Inv : Nat → State → Prop := fun i t =>
    (t.gpr .t3 = off p.B (256 + 8 * i) ∧ (∀ j < i, word t.mem p.B (256 + 8 * j) = halfW s.mem p.B 256 j) ∧
      (∀ j, i ≤ j → j < w → word t.mem p.B (256 + 8 * j) = word s.mem p.B (256 + 8 * j)) ∧
      Frm p.B [(256, 8 * w)] s.mem t.mem) ∧ Keep hqRegs s t
  refine WP.seq (WP.mono (wp_countdown (cnt := .t4) (N := w - 1) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨⟨t3, tlo, thi, tf⟩, kt⟩ _ => ?_)
    ⟨⟨by rw [u3], fun j hj => absurd hj (Nat.not_lt_zero _), fun j _ _ => by rw [um],
      by rw [um]; exact Frm.refl _ _ _⟩, ku.mono (by decide)⟩ u4) fun t ht => ?_)
  · have hsc : Scr t p.B (8 * p.n) := hs.scr.congr kt.2.2
    have l0 : InRegions (t.rd ++ t.wr) (off p.B (256 + 8 * i)) 8 := hsc.ld (by omega_arith)
    have l1 : InRegions (t.rd ++ t.wr) (off p.B (256 + 8 * (i + 1))) 8 := hsc.ld (by omega_arith)
    have s0 : InRegions t.wr (off p.B (256 + 8 * i)) 8 := hsc.st (by omega_arith)
    have a0 : (off p.B (256 + 8 * i)).toNat % 8 = 0 := hsc.al8 (by omega_arith) (by omega_arith)
    have a1 : (off p.B (256 + 8 * (i + 1))).toNat % 8 = 0 := hsc.al8 (by omega_arith) (by omega_arith)
    have e8 : off p.B (256 + 8 * i) + BitVec.ofNat 64 8 = off p.B (256 + 8 * (i + 1)) := by
      rw [off_add, show 256 + 8 * i + 8 = 256 + 8 * (i + 1) by omega_arith]
    have r0 : t.mem.readW (off p.B (256 + 8 * i)) 64 = word s.mem p.B (256 + 8 * i) :=
      thi i (by omega_arith) (by omega_arith)
    have r1 : t.mem.readW (off p.B (256 + 8 * (i + 1))) 64 = word s.mem p.B (256 + 8 * (i + 1)) :=
      thi (i + 1) (by omega_arith) (by omega_arith)
    refine WP.mono (WP.keep [.t3, .t4, .t5, .t6] (Q := fun u => u.gpr .t3 = off p.B (256 + 8 * (i + 1)) ∧
        u.mem = t.mem.writeW (off p.B (256 + 8 * i)) (halfW s.mem p.B 256 i) ∧
        u.gpr .t4 = t.gpr .t4 - BitVec.ofNat 64 1) ?_ (by rfl) (by rfl))
      fun u ⟨⟨u3, um, u4⟩, ku⟩ => ⟨⟨⟨u3, ?_, ?_, ?_⟩, (kt.trans ku).mono (by decide)⟩, u4⟩
    · brun [t3, BitVec.add_zero, add_ofNat_zero, e8, l0, l1, s0, a0, a1, r0, r1]
    · intro j hj
      rw [um]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [word, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact tlo j hj
      · exact rw_self _ _ _
    · intro j hj hj'
      rw [um, word, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
      exact thi j (by omega_arith) hj'
    · rw [um]
      exact frm_writeW tf _ ⟨_, List.mem_singleton_self _, by dsimp only; omega_arith, by dsimp only; omega_arith⟩
        (by omega_arith)
  obtain ⟨⟨t3, tlo, thi, tf⟩, kt⟩ := ht
  have hsc : Scr t p.B (8 * p.n) := hs.scr.congr kt.2.2
  have lT : InRegions (t.rd ++ t.wr) (off p.B (256 + 8 * (w - 1))) 8 := hsc.ld (by omega_arith)
  have sT : InRegions t.wr (off p.B (256 + 8 * (w - 1))) 8 := hsc.st (by omega_arith)
  have aT : (off p.B (256 + 8 * (w - 1))).toNat % 8 = 0 := hsc.al8 (by omega_arith) (by omega_arith)
  have rT : t.mem.readW (off p.B (256 + 8 * (w - 1))) 64 = word s.mem p.B (256 + 8 * (w - 1)) :=
    thi (w - 1) (by omega_arith) (by omega_arith)
  have h6 : t.gpr .s6 = p.B := (kt.gpr (by decide)).trans hs.s6
  have t7 : t.gpr .a7 = off p.B 256 := (kt.gpr (by decide)).trans h7
  have lB : InRegions (t.rd ++ t.wr) (p.B + BitVec.ofNat 64 200) 8 := hsc.ld (d := 200) (by omega_arith)
  have sB : InRegions t.wr (p.B + BitVec.ofNat 64 200) 8 := hsc.st (d := 200) (by omega_arith)
  have aB : (p.B + BitVec.ofNat 64 200).toNat % 8 = 0 := hsc.al8 (d := 200) (by omega_arith) (by decide)
  have l0 : InRegions (t.rd ++ t.wr) (off p.B 256) 8 := hsc.ld (by omega_arith)
  have a0 : (off p.B 256).toNat % 8 = 0 := hsc.al8 (by omega_arith) (by decide)
  have rB : ∀ v : BitVec 64, (t.mem.writeW (off p.B (256 + 8 * (w - 1))) v).readW (p.B + BitVec.ofNat 64 200) 64 =
      word s.mem p.B 200 := fun v => by
    rw [rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
    exact tf.word_eq (fun r hr => by rw [List.mem_singleton] at hr; subst hr; dsimp only; omega_arith) (by omega_arith)
  have r0 : ∀ v : BitVec 64, (t.mem.writeW (off p.B (256 + 8 * (w - 1))) v).readW (off p.B 256) 64 =
      halfW s.mem p.B 256 0 := fun v => by
    rw [show off p.B 256 = off p.B (256 + 8 * 0) from rfl, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
    exact tlo 0 (by omega_arith)
  refine WP.mono (WP.keep [.t4, .t5] (Q := fun u => u.mem =
      (t.mem.writeW (off p.B (256 + 8 * (w - 1))) (word s.mem p.B (256 + 8 * (w - 1)) >>> 1)).writeW
        (p.B + BitVec.ofNat 64 200) (word s.mem p.B 200 ||| ((halfW s.mem p.B 256 0 &&& 1#64) ^^^ 1#64))) ?_
      (by rfl) (by rfl)) fun u ⟨um, ku⟩ => ⟨?_, (kt.trans ku).mono (by decide)⟩
  · simp only [ldh, sth, hBad]
    brun [t3, t7, h6, BitVec.add_zero, add_ofNat_zero, lT, sT, aT, rT, lB, sB, aB, l0, a0, rB, r0]
  have hv : wv u.mem p.B 256 w = x / 2 := by
    rw [← hx]
    refine Proof.Ffdh.ParameterCandidate.wv_half (by omega_arith) (fun j hj => ?_) ?_
    · rw [um, word, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
        rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
      exact tlo j (by omega_arith)
    · rw [um, word, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), rw_self]
  refine ⟨hv, ?_, ?_⟩
  · have e := wv_mod_two u.mem p.B 256 (w := w) (by omega_arith)
    have t0 : t.mem.readW (p.B + BitVec.ofNat 64 256) 64 = halfW s.mem p.B 256 0 := tlo 0 (by omega_arith)
    rw [hv, um, word, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), t0] at e
    simp only [word, off, hBad, Nat.reduceMul, um, rw_self, BitVec.or_eq_zero_iff, low_flag]
    rw [e]
  · rw [um]
    refine frm_writeW (frm_writeW (tf.mono fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self) _
        ⟨_, List.mem_cons_self, by dsimp only; omega_arith, by dsimp only; omega_arith⟩ (by omega_arith)) _
      ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by decide, by decide⟩ (by omega_arith)

/-! ## The shape checks -/

theorem oddPrimes_eq : oddPrimes256 = (List.range 53).map VG.Impl.RsaKeyGen.tabEntry := by
  unfold VG.Impl.RsaKeyGen.tabEntry VG.Impl.RsaKeyGen.slots
  rw [VG.Impl.RsaKeyGen.primes.lit_eq]
  decide +kernel

theorem noDiv_iff (x : Nat) :
    (∀ d ∈ oddPrimes256, x % d ≠ 0) ↔ ((List.range 53).any fun i => x % VG.Impl.RsaKeyGen.tabEntry i == 0) = false := by
  rw [oddPrimes_eq, List.any_eq_false]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, beq_iff_eq]

theorem shape_iff {bits g x : Nat} (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192) (hg : g = 2 ∨ g = 5) :
    (goodRes g (Spec.Ffdh.candidateOf bits x) ∧ (∀ d ∈ oddPrimes256, Spec.Ffdh.candidateOf bits x % d ≠ 0) ∧
        Spec.Ffdh.candidateOf bits x / 2 % 2 = 1 ∧ ∀ d ∈ oddPrimes256, Spec.Ffdh.candidateOf bits x / 2 % d ≠ 0) ↔
      (Spec.Ffdh.generationShape bits g (Spec.Ffdh.candidateOf bits x) &&
        Spec.Ffdh.primeShape (Spec.Ffdh.candidateOf bits x) &&
        Spec.Ffdh.primeShape ((Spec.Ffdh.candidateOf bits x - 1) / 2)) = true := by
  obtain ⟨ho, hl, hu⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := bits) (by omega_arith) x
  have hbl := (VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (bits := bits) (by omega_arith) x).1
  obtain ⟨hql, _⟩ := VG.Proof.Ffdh.ParameterCandidate.half_shape (by omega_arith) ho hl hu
  generalize Spec.Ffdh.candidateOf bits x = c at ho hl hu hbl hql ⊢
  have hq : (c - 1) / 2 = c / 2 := by omega_arith
  have big : 8161 < c := Nat.lt_of_lt_of_le (by decide : 8161 < 2 ^ 13)
    (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega_arith : 13 ≤ bits - 1)) hl)
  have bigq : 8161 < c / 2 := by
    rw [← hq]
    exact Nat.lt_of_lt_of_le (by decide : 8161 < 2 ^ 13)
      (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega_arith : 13 ≤ bits - 2)) hql)
  have hgen : Spec.Ffdh.generationShape bits g c = true ↔ goodRes g c := by
    unfold Spec.Ffdh.generationShape goodRes
    rcases hg with rfl | rfl <;> simp [hb1, hb2, hbl]
  have hp := VG.Proof.Ffdh.ParameterCandidate.primeShape_sieve big ho
  rw [hq]
  simp only [Bool.and_eq_true, hgen, hp, Bool.not_eq_eq_eq_not, Bool.not_true, ← noDiv_iff c]
  by_cases hqo : c / 2 % 2 = 1
  · rw [VG.Proof.Ffdh.ParameterCandidate.primeShape_sieve bigq hqo]
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, ← noDiv_iff (c / 2), hqo, true_and, and_assoc]
  · have hf : Spec.Ffdh.primeShape (c / 2) = false := by
      unfold Spec.Ffdh.primeShape; simp [hqo]
    rw [hf]
    simp [hqo]

/-! ## Through the shape checks -/

/-- `Ph` survives a change of memory that keeps the header but `hBad`. -/
theorem Ph.keepBad {p : PP} {mb : Nat} {s t : State} (h : Ph p mb C s)
    (r7 : t.gpr .a7 = s.gpr .a7) (r0 : t.gpr .t0 = s.gpr .t0) (r5 : t.gpr .s5 = s.gpr .s5)
    (hw : ∀ d, d + 8 ≤ 200 ∨ (208 ≤ d ∧ d + 8 ≤ 256) → word t.mem p.B d = word s.mem p.B d) : Ph p mb C t :=
  ⟨r7.trans h.a7, r0.trans h.t0, r5.trans h.s5, (hw 248 (by decide)).trans h.mbW,
    (hw 216 (by decide)).trans h.kW, (hw 48 (by decide)).trans h.wW, (hw 224 (by decide)).trans h.strideW,
    fun j hj => (hw _ (by omega_arith)).trans (h.arrW j hj), (hw 168 (by decide)).trans h.checksW, h.k1, h.k2,
    (hw 192 (by decide)).trans h.topW⟩

/-- A piece of the shape checks, which changes `hBad` and array 0 at most. -/
theorem shapeStep {p : PP} {s t : State} (h : St p s) (hp : Ph p p.bits C s)
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 p.L) {rs : List (Nat × Nat)} (hf : Frm p.B rs s.mem t.mem)
    (hr : ∀ r ∈ rs, r = (200, 8) ∨ r = (256, 8 * wOf p.bits)) {regs : List Reg} (k : Keep regs s t)
    (hsp : t.sp = s.sp) (h7 : Reg.a7 ∉ regs := by decide) (h0 : Reg.t0 ∉ regs := by decide)
    (h5 : Reg.s5 ∉ regs := by decide) (h6 : Reg.s6 ∉ regs := by decide) :
    St p t ∧ Ph p p.bits C t ∧ word t.mem p.B 152 = BitVec.ofNat 64 p.L := by
  have hdn := h.dims.n
  have hb2 := h.dims.b2
  have hb1 := h.dims.b1
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hw : wOf p.bits = (p.bits + 63) / 64 := rfl
  have st := h.step (Frm.toMut hf fun r hr' => by
    rcases hr r hr' with rfl | rfl
    · exact InMut.hdr (i := 25) (by decide)
    · exact InMut.arrays (by omega_arith) (by simp only [saveBytes]; omega_arith)) k hsp h6
  have wd : ∀ d, d + 8 ≤ 200 ∨ (208 ≤ d ∧ d + 8 ≤ 256) → word t.mem p.B d = word s.mem p.B d := fun d hd =>
    hf.word_eq (fun r hr' => by rcases hr r hr' with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
  exact ⟨st, hp.keepBad (k.gpr h7) (k.gpr h0) (k.gpr h5) wd, (wd 152 (by decide)).trans hu⟩

/-- `hBad` into `t3`. -/
theorem badLoad_ok {p : PP} {s : State} (h : St p s) :
    WP isa (.block [ldh .t3 hBad]) s fun t => (t.gpr .t3 = word s.mem p.B 200 ∧ t.mem = s.mem ∧ Keep [.t3] s t) ∧
      t.sp = s.sp :=
  WP.mono (WP.rdwr (WP.keep [.t3] (Q := fun t => t.gpr .t3 = word s.mem p.B 200 ∧ t.mem = s.mem)
    (by simp only [ldh, hBad]; brun [h.s6, h.ld (d := 200) (by decide), h.al (d := 200) (by decide) (by decide)])
    (by rfl) (by rfl))) fun _ ⟨⟨⟨t5, tm⟩, k⟩, _, _, hsp⟩ => ⟨⟨t5, tm, k⟩, hsp⟩

instance (g x : Nat) : Decidable (goodRes g x) := by unfold goodRes; infer_instance

/-- The table at `T`, where the state names it, readable, aligned, and
apart from the working space of `Z` bytes at `B`. -/
structure TabIn (B : Addr) (Z : Nat) (T : Addr) (s : State) : Prop where
  sym : s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = T
  tab : TabAt T s.mem
  rd : (⟨T, 8192⟩ : Region) ∈ s.rd
  fit : T.toNat + 8192 ≤ 2 ^ 64
  al : T.toNat % 8 = 0
  dj : (⟨T, 8192⟩ : Region).Disjoint ⟨B, Z⟩

/-- The table survives a change of the working space. -/
theorem TabIn.step {B T : Addr} {Z : Nat} {s t : State} {rs : List (Nat × Nat)}
    (h : TabIn B Z T s) (sy : t.syms = s.syms) (hf : Frm B rs s.mem t.mem) (hr : ∀ r ∈ rs, r.1 + r.2 ≤ Z)
    (krd : t.rd = s.rd) : TabIn B Z T t := by
  refine ⟨sy ▸ h.sym, fun i hi => ?_, by rw [krd]; exact h.rd, h.fit, h.al, h.dj⟩
  rw [← h.tab i hi]
  refine Mem.readW_congr fun j hj => (hf _ fun r hr' => .inr ?_)
  have hj' : j < 8 := by omega
  have hc : (⟨T, 8192⟩ : Region).Contains (T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j) 1 := by
    simp only [Region.Contains, BitVec.add_assoc, Offset.add_sub_cancel_left, BitVec.ofNat_add_ofNat,
      BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hn := h.dj _ hc
  simp only [Region.Contains, Nat.not_le] at hn
  have := hr r hr'
  unfold ofs
  omega

/-- In p's working space, with `x` in array 0, `hBad` zero iff `B`, and
the table at `T`. -/
structure MB (p : PP) (T : Addr) (x : Nat) (B : Prop) (t : State) : Prop where
  st : St p t
  ph : Ph p p.bits (Spec.Ffdh.primeChecks p.bits) t
  u : word t.mem p.B 152 = BitVec.ofNat 64 p.L
  n : wv t.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = x
  bad : word t.mem p.B (8 * hBad) = 0#64 ↔ B
  tab : TabIn p.B p.Z T t

theorem phR_used : ∀ r ∈ phRanges ++ [(8 * hTop, 8)], 152 + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 152 := by
  intro r hr
  simp only [phRanges, hTop, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

theorem phR_low : ∀ r ∈ phRanges ++ [(8 * hTop, 8)], r.1 + r.2 ≤ 256 := by
  intro r hr
  simp only [phRanges, hTop, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

/-- p's working space, and p. -/
theorem mainA_ok {p : PP} {s : State} (h : St p s) (hU : word s.mem p.B 152 = BitVec.ofNat 64 p.L)
    (hL : p.L ≤ p.r.length) :
    WP isa (.seq (phase false) shapeP) s fun t => St p t ∧ Ph p p.bits (Spec.Ffdh.primeChecks p.bits) t ∧
      word t.mem p.B 152 = BitVec.ofNat 64 p.L ∧
      wv t.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) =
        Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)) ∧
      (∀ r ∈ phRanges ++ [(8 * hTop, 8)] ++ [(256, 8 * wOf p.bits)], r.1 + r.2 ≤ p.Z) ∧
      Frm p.B (phRanges ++ [(8 * hTop, 8)] ++ [(256, 8 * wOf p.bits)]) s.mem t.mem ∧ t.rd = s.rd := by
  have hsl : slot (wOf p.bits) 0 = 256 := slot_zero _
  have hdn := h.dims.n
  have hb2 := h.dims.b2
  have hwe : wOf p.bits = (p.bits + 63) / 64 := rfl
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hZe : p.Z = 8 * p.n := rfl
  refine WP.seq (WP.mono (phase_ok h false) fun t₁ ⟨⟨⟨st₁, ph₁, hf₁⟩, k₁⟩, _⟩ => ?_)
  simp only [mbOf, Bool.false_eq_true, ↓reduceIte] at ph₁
  have hU₁ : word t₁.mem p.B 152 = BitVec.ofNat 64 p.L := by rw [hf₁.word_eq phR_used (by decide)]; exact hU
  refine WP.mono (WP.rdwr (shapeP_ok st₁ ph₁ hL)) fun t₂ ⟨⟨⟨hn₂, f₂⟩, k₂⟩, _, _, sp₂⟩ => ?_
  obtain ⟨st₂, ph₂, hU₂⟩ := shapeStep st₁ ph₁ hU₁ f₂ (fun r hr => by
    rw [List.mem_singleton.mp hr, hsl]; exact .inr rfl) k₂ sp₂
  refine ⟨st₂, ph₂, hU₂, hn₂, fun r hr => ?_, ?_, k₂.2.1.trans k₁.2.1⟩
  · rcases List.mem_append.mp hr with hr | hr
    · have := phR_low r hr; omega_arith
    · rw [List.mem_singleton.mp hr]; dsimp only; omega_arith
  · exact (hf₁.mono fun r hr => List.mem_append_left _ hr).trans
      (by rw [hsl] at f₂; exact f₂.mono fun r hr => List.mem_append_right _ hr)

/-- p's congruence. -/
theorem residue_mb {p : PP} {T : Addr} {s : State} {x : Nat} (h : St p s)
    (hp : Ph p p.bits (Spec.Ffdh.primeChecks p.bits) s) (ht : TabIn p.B p.Z T s)
    (hU : word s.mem p.B 152 = BitVec.ofNat 64 p.L) (hn : wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = x) :
    WP isa residue s (MB p T x (goodRes p.g x)) := by
  have hdn := h.dims.n
  have hb2 := h.dims.b2
  have hsl : slot (wOf p.bits) 0 = 256 := slot_zero _
  have hwe : wOf p.bits = (p.bits + 63) / 64 := rfl
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hZe : p.Z = 8 * p.n := rfl
  refine WP.mono_syms (WP.rdwr (residue_ok h hp)) fun t ⟨⟨⟨hb, f⟩, k⟩, _, _, tsp⟩ sy => ?_
  rw [hn] at hb
  obtain ⟨st, ph, hU'⟩ := shapeStep h hp hU f (fun r hr => .inl (List.mem_singleton.mp hr)) k tsp
  refine ⟨st, ph, hU', ?_, hb, ht.step sy f (fun r hr => by
    rw [List.mem_singleton.mp hr]; dsimp only; first | (simp only [hBad]; omega_arith) | omega_arith) k.2.1⟩
  rw [f.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr, hsl]; exact .inr (by decide)) (by omega_arith)]; exact hn

/-- `hBad` into `t3`. -/
theorem MB.badLoad {p : PP} {T : Addr} {x : Nat} {B : Prop} {s : State} (h : MB p T x B s) :
    WP isa (.block [ldh .t3 hBad]) s fun t => MB p T x B t ∧ t.gpr .t3 = word s.mem p.B 200 := by
  refine WP.mono_syms (badLoad_ok h.st) fun t ⟨⟨t5, tm, k⟩, tsp⟩ sy => ?_
  obtain ⟨st, ph, hU⟩ := shapeStep h.st h.ph h.u (rs := []) (by rw [tm]; exact Frm.refl _ _ _) (by simp) k tsp
  exact ⟨⟨st, ph, hU, by rw [tm]; exact h.n, by rw [tm]; exact h.bad,
    h.tab.step sy (rs := []) (by rw [tm]; exact Frm.refl _ _ _) (by simp) k.2.1⟩, t5⟩

/-- A sieve of array 0. -/
theorem MB.sieve {p : PP} {T : Addr} {x : Nat} {B : Prop} {s : State} (h : MB p T x B s) :
    WP isa VG.Impl.Ffdh.RISCV64.ParameterCandidate.sieve s (MB p T x (B ∧ ∀ d ∈ oddPrimes256, x % d ≠ 0)) := by
  have hb1 := h.st.dims.b1
  have hb2 := h.st.dims.b2
  have hdn := h.st.dims.n
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hwe : wOf p.bits = (p.bits + 63) / 64 := rfl
  have hZe : p.Z = 8 * p.n := rfl
  have hsl : slot (wOf p.bits) 0 = 256 := slot_zero _
  have hZw : slot (wOf p.bits) 0 + 8 * wOf p.bits ≤ p.Z := by rw [hsl]; omega_arith
  refine WP.mono_syms (WP.rdwr (sieve_ok oddPrimes256 VG.Proof.Ffdh.RISCV64.Search.oddPrimes256_bounds
    h.st.scr h.st.s6 h.ph.a7 h.ph.t0 h.n (by omega_arith) (by omega_arith) hZw (by rw [hsl]) (by omega_arith)))
    fun t ⟨⟨⟨hb, f⟩, k⟩, _, _, tsp⟩ sy => ?_
  obtain ⟨st, ph, hU⟩ := shapeStep h.st h.ph h.u f (fun r hr => .inl (List.mem_singleton.mp hr)) k tsp
  refine ⟨st, ph, hU, ?_, hb.trans (and_congr h.bad Iff.rfl), h.tab.step sy f (fun r hr => by
    rw [List.mem_singleton.mp hr]; dsimp only; first | (simp only [hBad]; omega_arith) | omega_arith) k.2.1⟩
  rw [f.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr, hsl]; exact .inr (by decide)) (by omega_arith)]; exact h.n

/-- q from p. -/
theorem MB.halve {p : PP} {T : Addr} {x : Nat} {B : Prop} {s : State} (h : MB p T x B s) :
    WP isa halveQ s (MB p T (x / 2) (B ∧ x / 2 % 2 = 1)) := by
  have hb1 := h.st.dims.b1
  have hb2 := h.st.dims.b2
  have hdn := h.st.dims.n
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hwe : wOf p.bits = (p.bits + 63) / 64 := rfl
  have hZe : p.Z = 8 * p.n := rfl
  have hsl : slot (wOf p.bits) 0 = 256 := slot_zero _
  have hZw : slot (wOf p.bits) 0 + 8 * wOf p.bits ≤ p.Z := by rw [hsl]; omega_arith
  refine WP.mono_syms (WP.rdwr (halveQ_ok h.st h.ph.a7 h.ph.t0 h.n (by omega_arith) (by omega_arith) hZw))
    fun t ⟨⟨⟨hn, hb, f⟩, k⟩, _, _, tsp⟩ sy => ?_
  obtain ⟨st, ph, hU⟩ := shapeStep h.st h.ph h.u f (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hsl]; exact .inr rfl
    · exact .inl rfl) k tsp
  exact ⟨st, ph, hU, hn, hb.trans (and_congr h.bad Iff.rfl), h.tab.step sy f (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only <;> first | (simp only [hBad]; omega_arith) | omega_arith) k.2.1⟩

end VG.Proof.Ffdh.RISCV64.ParameterCandidate
