module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyBody
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.KeyPair
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Gk
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Sign
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Output
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyInv
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyQ
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Table
import VerifiedGarbage.Proof.Bignum.PPC64LE.ModExpPow
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Ctx
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.ModArithReduce
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRounds
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCore
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Bignum.Octets

/-! ### `Dsa.PPC64LE.Sign.Inverse`, which only this module used -/

section

/-!
# DSA signing on PPC64LE: `w = k^(q − 2) mod q`

`inverseK_ok`: verification's `inverse_ok` (`VerifyInv.lean`) with the base
k, the nonce at `r28`, in place of s.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Verify
  VG.Impl.Dsa.PPC64LE.Sign
open VG.Proof.Bignum (slot slot_sep)

theorem inverseK_ok {s : State} {L : Lay} {key sig dig : Addr} (h : QS s L key sig dig) (hL : L.Ok)
    (hsg : Src s L sig L.ql) (hq2 : 2 ≤ arrQ s.mem L 0) (hqo : arrQ s.mem L 0 % 2 = 1)
    (h8 : arrQ s.mem L 8 = 2 ^ (128 * 4) % arrQ s.mem L 0) :
    WP isa inverseK s fun t =>
      (QS t L key sig dig ∧
        arrQ t.mem L 4 = kOf s.mem L sig ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.ql) %
          arrQ s.mem L 0 ∧
        arrQ t.mem L 8 = arrQ s.mem L 8 ∧ QArr L s.mem t.mem ∧ arrQ t.mem L 9 = arrQ s.mem L 9) ∧
        Keep invRegs s t := by
  obtain hRR := pow_sq_eq 4
  generalize (2 : Nat) ^ (128 * 4) = R2 at h8 hRR
  have hql := hL.ql
  have hpl := hL.pl
  have e70 : slot 4 0 = 256 := rfl
  have e71 : slot 4 1 = 304 := rfl
  have e74 : slot 4 4 = 448 := rfl
  have e78 : slot 4 8 = 640 := rfl
  unfold inverseK
  refine WP.seq (WP.mono (ptrR_ok h.regs) fun s₁ ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
  obtain Q1 := h.step k1 (by decide)
  refine WP.seq (WP.mono (loadQ_ok (j := 4) Q1 hL (by decide) (by decide)
      ((hsg.keep k1.rd k1.wr).sub (o := 0) (k := L.ql) (by omega_arith)) (by rw [a12, off, BitVec.add_zero]) a6
      (by omega_arith) (by omega_arith))
    fun s₂ ⟨⟨Q2, v4, _, o2, qa2⟩, k2⟩ => ?_)
  rw [m1, off, BitVec.add_zero] at v4
  rw [m1] at o2 qa2
  refine WP.seq (WP.mono (copy_ok Q2.inq.env (o := 1) (a := 8) (by decide) (by decide) (by decide))
    fun s₃ ⟨⟨v1, o3⟩, k3⟩ => ?_)
  obtain qa3 : QArr L s₂.mem s₃.mem := QArr.of o3 (by rw [e71]) (by rw [e71]; decide)
  obtain Q3 := Q2.step k3 (by decide)
  obtain a8s : arr s₂.mem L.Q 4 8 = arrQ s.mem L 8 := Outside.val32 o2 (by rw [e74, e78]; omega_arith) (by decide)
  obtain a0s : arr s₃.mem L.Q 4 0 = arrQ s.mem L 0 := (qa2.trans qa3).arr0
  obtain a4s : arr s₃.mem L.Q 4 4 = kOf s.mem L sig := by
    rw [arr, Outside.val32 o3 (by rw [e74, e71]; omega_arith) (by decide)]; exact v4
  obtain hbuf : Spec.Rsa.bytesAt s₃.mem L.Buf L.ql = Spec.Rsa.bytesAt s.mem L.Buf L.ql :=
    (qa2.trans qa3).bufBytes (by omega_arith)
  -- The exponent's pointer and length, and `-q⁻¹`.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ptrBuf_ok hL Q3.regs) fun s₄ ⟨⟨b12, b6, m4⟩, k4⟩ => ?_
  refine WP.mono (WP.keep [.r30, .r31] (Q := fun u => u.gpr .r30 = L.Buf ∧
      u.gpr .r31 = BitVec.ofNat 64 L.ql ∧ u.mem = s₄.mem) (by prun [b12, b6, BitVec.add_zero]) (by decide))
    fun s₅ ⟨⟨c30, c31, m5⟩, k5⟩ => ?_
  obtain k35 := k4.trans k5
  have kk := k35
  obtain hs5 : Scr s₅ L.Q 1600 := Q3.inq.env.hs.congr k35.wr
  obtain h10 : s₅.gpr .r10 = off L.Q (slot 4 0) := (k35.gpr .r10 (by decide)).trans Q3.inq.env.h10
  obtain hm5 : s₅.mem = s₃.mem := by rw [m5, m4]
  obtain hodd : (word s₅.mem L.Q (slot 4 0)).toNat % 2 = 1 :=
    word_odd _ _ _ (2 * 4) (by decide) (by rw [hm5]; show arr s₃.mem L.Q 4 0 % 2 = 1; rw [a0s]; exact hqo)
  refine WP.mono (Pub.minv_ok hs5 h10 (by decide) hodd) fun s₆ ⟨⟨i12, inv, m6⟩, k6⟩ => ?_
  obtain k36 := k35.trans k6
  obtain hm6 : s₆.mem = s₃.mem := by rw [m6, hm5]
  rw [← m6] at inv
  obtain a1s : arr s₃.mem L.Q 4 1 = R2 % arrQ s.mem L 0 := by
    rw [v1, a8s, h8]
  refine WP.seq (WP.mono (ModExp.powSecret_ok (hs5.congr k6.wr) (by decide) (by decide) (by decide)
    ((k6.gpr .r10 (by decide)).trans h10) ((k36.gpr .r29 (by decide)).trans Q3.inq.env.h29)
    ((k36.gpr .r11 (by decide)).trans Q3.inq.env.h11) i12 inv
    (by rw [hm6]; show 2 ≤ arr s₃.mem L.Q 4 0; rw [a0s]; exact hq2)
    (by rw [hm6]; show arr s₃.mem L.Q 4 0 % 2 = 1; rw [a0s]; exact hqo)
    (by rw [hm6]; show arr s₃.mem L.Q 4 1 < arr s₃.mem L.Q 4 0; rw [a1s, a0s]; exact Nat.mod_lt _ (by omega_arith))
    (D := L.Buf) (L := L.ql)
    (show s₆.gpr .r30 = off L.Buf 0 by rw [k6.gpr .r30 (by decide), c30, off, BitVec.add_zero])
    ((k6.gpr .r31 (by decide)).trans c31)
    (by omega_arith) (by omega_arith)
    (fun i hi => by
      rw [k36.rd, k36.wr]
      exact (ScrL.bufN (s := s₃) Q3.scr hL (n := L.ql) (by omega_arith)).ld (show i + 1 ≤ L.ql by omega_arith))
    (buf_apartQ L (by omega_arith))) fun s₇ ⟨⟨pw, o7⟩, k7⟩ => ?_)
  rw [hm6] at pw o7
  obtain qa7 : QArr L s₃.mem s₇.mem := QArr.of (outs_within o7 (lo := slot 4 1) (hi := slot 4 8)
    (by simp only [Pub.powRs, List.map, List.mem_cons, List.not_mem_nil, or_false]; intro r hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [slot_eq] <;> omega_arith))
    (Nat.le_refl _) (by rw [e78, e71]; omega_arith)
  obtain o7' : Outside L.Q (slot 4 1) (slot 4 8 - slot 4 1) s₃.mem s₇.mem := outs_within o7
    (by simp only [Pub.powRs, List.map, List.mem_cons, List.not_mem_nil, or_false]; intro r hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [slot_eq] <;> omega_arith)
  refine WP.mono (WP.keep [.r31] (Q := fun u => u.gpr .r31 = L.Q ∧ u.mem = s₇.mem)
      (by prun [((k36.trans k7).gpr .r23 (by decide)).trans Q3.inq.h23, BitVec.add_zero]) (by decide))
    fun t ⟨⟨t31, mt⟩, kt⟩ => ?_
  obtain kall := ((((k1.trans k2).trans k3).trans k36).trans k7).trans kt
  refine ⟨⟨⟨⟨⟨h.inq.env.hs.congr kall.wr, (kt.gpr .r10 (by decide)).trans
      ((k7.gpr .r10 (by decide)).trans ((k6.gpr .r10 (by decide)).trans h10)),
      (kall.gpr .r29 (by decide)).trans h.inq.env.h29, (kall.gpr .r11 (by decide)).trans h.inq.env.h11, t31,
      by decide, by decide, by decide⟩, (kall.gpr .r21 (by decide)).trans h.inq.h21,
      (kall.gpr .r23 (by decide)).trans h.inq.h23⟩, h.scr.congr kall.wr,
      h.regs.keep kall⟩, ?_, ?_,
    by rw [mt]; exact qa2.trans (qa3.trans qa7), ?_⟩, kall.mono (by decide)⟩
  · rw [arrQ, mt]
    obtain rr : val32 s₃.mem L.Q (slot 4 1) (2 * 4) = 2 ^ (64 * 4) * 2 ^ (64 * 4) % val32 s₃.mem L.Q (slot 4 0) (2 * 4) := by
      rw [hRR]; exact a1s.trans (by rw [← a0s])
    show val32 s₇.mem L.Q (slot 4 4) (2 * 4) = _
    rw [pw rr, hbuf]
    show arr s₃.mem L.Q 4 4 ^ _ % arr s₃.mem L.Q 4 0 = _
    rw [a4s, a0s]
  · rw [arrQ, mt]
    show val32 s₇.mem L.Q (slot 4 8) (2 * 4) = _
    rw [Outside.val32 o7' (by rw [e78, e71]; omega_arith) (by decide)]
    show arr s₃.mem L.Q 4 8 = _
    rw [arr, Outside.val32 o3 (by rw [e71, e78]; omega_arith) (by decide)]
    exact a8s

  · rw [arrQ, mt]
    show val32 s₇.mem L.Q (slot 4 9) (2 * 4) = val32 s.mem L.Q (slot 4 9) (2 * 4)
    rw [Outside.val32 o7' (by simp only [slot_eq]; omega_arith) (by decide),
      Outside.val32 o3 (by rw [e71]; simp only [slot_eq]; omega_arith) (by decide),
      Outside.val32 o2 (by rw [e74]; simp only [slot_eq]; omega_arith) (by decide)]

end VG.Proof.Dsa.PPC64LE

end

end

/-! ### `Dsa.PPC64LE.Sign.S`, which only this module used -/

section

/-! ### `Dsa.PPC64LE.Sign.Add`, which only this module used -/

section

/-!
# DSA signing on PPC64LE: addition modulo q

`addArr_ok`: the accumulator's `n + 1` digits := the sum of two numbers of
`n` digits (as `double_ok`, `Proof/Bignum/PPC64LE/PreDouble.lean`, with a
second source). `addMod_ok`: `[o] := [a] + [b] mod m` in the arrays of
`Env`, through arrays 2 and 3 (as `doubleBitMod_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Sign
open VG.Proof.Bignum (slot slot_sep)

/-- A digit of the addition, on bit vectors: `D = x + y + c`, whose low 32 bits
are the digit and whose bits above are the carry. -/
theorem add_arith (x y : BitVec 32) (c : BitVec 64) (hc : c.toNat ≤ 1) :
    let D := x.setWidth 64 + y.setWidth 64 + c
    (D >>> 32).toNat ≤ 1 ∧ (D.setWidth 32).toNat + 2 ^ 32 * (D >>> 32).toNat = x.toNat + y.toNat + c.toNat := by
  intro D
  have hx := x.isLt
  have hy := y.isLt
  obtain vD : D.toNat = x.toNat + y.toNat + c.toNat := by
    simp only [D, BitVec.toNat_add, toNat_ext32]
    omega_arith
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_setWidth, vD]
  omega_arith

/-- The registers `addArr` writes. -/
def addArrRegs : List Reg := [.r0, .r3, .r14, .r15, .r16, .r17, .r20]

/-- `addArr`, `x` and `y` (`n` digits) at `dX` and `dY` and the accumulator at
`dA`: the accumulator's `n + 1` digits are `x + y`. -/
theorem addArr_ok {s : State} {B : Addr} {Z dA dX dY n : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B dA) (h5 : s.gpr .r5 = off B dX) (h16 : s.gpr .r16 = off B dY)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 n)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hA : dA + 4 * (n + 1) ≤ Z) (hX : dX + 4 * n ≤ Z) (hY : dY + 4 * n ≤ Z)
    (dXA : dX + 4 * n ≤ dA ∨ dA + 4 * (n + 1) ≤ dX) (dYA : dY + 4 * n ≤ dA ∨ dA + 4 * (n + 1) ≤ dY) :
    WP isa addArr s fun s' =>
      val32 s'.mem B dA (n + 1) = val32 s.mem B dX n + val32 s.mem B dY n ∧
      Mont.Outside B dA (4 * (n + 1)) s.mem s'.mem ∧ Keep addArrRegs s s' := by
  have hnw := hs.nowrap
  unfold addArr
  refine WP.seq ?_
  obtain hpre : WP isa (.block [.addi .r14 .r8 0, .addi .r15 .r5 0, .addi .r17 .r11 0, .li .r20 0]) s
      fun s₁ => (s₁.gpr .r14 = off B dA ∧ s₁.gpr .r15 = off B dX ∧ s₁.gpr .r17 = BitVec.ofNat 64 n ∧
        s₁.gpr .r20 = 0 ∧ s₁.mem = s.mem) ∧ Keep [.r14, .r15, .r17, .r20] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h8, h5, h11, BitVec.add_zero]
    rfl
  refine WP.mono hpre fun s₁ ⟨⟨i14, i15, i17, i20, im⟩, k₁⟩ => ?_
  obtain i16 : s₁.gpr .r16 = off B dY := (k₁.gpr .r16 (by decide)).trans h16
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (dA + 4 * i) ∧ t.gpr .r15 = off B (dX + 4 * i) ∧ t.gpr .r16 = off B (dY + 4 * i) ∧
      (t.gpr .r20).toNat ≤ 1 ∧ Mont.Outside B dA (4 * i) s.mem t.mem ∧
      val32 t.mem B dA i + 2 ^ (32 * i) * (t.gpr .r20).toNat = val32 s.mem B dX i + val32 s.mem B dY i ∧
      Keep addArrRegs s t
  refine WP.seq (WP.mono (wp_countdown (body := .block ([.load .w .r0 .r15 0, .load .w .r3 .r16 0,
      .add .r0 .r0 .r3, .add .r0 .r0 .r20, .store .w .r0 .r14 0, .lsr .d .r20 .r0 32, .addi .r14 .r14 4,
      .addi .r15 .r15 4, .addi .r16 .r16 4] ++ ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := n) (by omega_arith) (by omega_arith) Inv (fun i hi t ⟨j14, j15, j16, j20, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [i14]; rfl, by rw [i15]; rfl, by rw [i16]; rfl, by rw [i20]; decide,
      by rw [← im]; exact Mont.Outside.refl _ _ _ _, by simp [val32, i20], k₁.mono (by decide)⟩ i17)
    fun t ⟨j14, _, _, j20, jout, jeq, jk⟩ => ?_)
  · have hst := (show WP isa (.block [.load .w .r0 .r15 0, .load .w .r3 .r16 0, .add .r0 .r0 .r3,
        .add .r0 .r0 .r20, .store .w .r0 .r14 0, .lsr .d .r20 .r0 32, .addi .r14 .r14 4, .addi .r15 .r15 4,
        .addi .r16 .r16 4, .subi .r17 .r17 1]) t fun t' =>
        let D := (t.mem.readW (off B (dX + 4 * i)) 32).setWidth 64 +
          (t.mem.readW (off B (dY + 4 * i)) 32).setWidth 64 + t.gpr .r20
        t'.gpr .r14 = off B (dA + 4 * i + 4) ∧ t'.gpr .r15 = off B (dX + 4 * i + 4) ∧
          t'.gpr .r16 = off B (dY + 4 * i + 4) ∧
          t'.gpr .r20 = D >>> 32 ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem.writeW (off B (dA + 4 * i)) (D.setWidth 32) ∧
          Keep addArrRegs t t' from by
      refine WP.mono (WP.keep addArrRegs (Q := fun t' =>
        let D := (t.mem.readW (off B (dX + 4 * i)) 32).setWidth 64 +
          (t.mem.readW (off B (dY + 4 * i)) 32).setWidth 64 + t.gpr .r20
        t'.gpr .r14 = off B (dA + 4 * i + 4) ∧ t'.gpr .r15 = off B (dX + 4 * i + 4) ∧
          t'.gpr .r16 = off B (dY + 4 * i + 4) ∧
          t'.gpr .r20 = D >>> 32 ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem.writeW (off B (dA + 4 * i)) (D.setWidth 32)) ?_ (by decide))
        fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, k⟩
      prun [j14, j15, j16, (hs.congr jk.wr).ld (show dX + 4 * i + 4 ≤ Z by omega_arith),
        (hs.congr jk.wr).ld (show dY + 4 * i + 4 ≤ Z by omega_arith),
        (hs.congr jk.wr).st (show dA + 4 * i + 4 ≤ Z by omega_arith)])
    refine WP.mono hst fun t' ⟨l14, l15, l16, l20, l17, lm, lk⟩ =>
      ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, (jk.trans lk).mono (by simp [addArrRegs])⟩, l17⟩
    · rw [l14, show dA + 4 * i + 4 = dA + 4 * (i + 1) by omega_arith]
    · rw [l15, show dX + 4 * i + 4 = dX + 4 * (i + 1) by omega_arith]
    · rw [l16, show dY + 4 * i + 4 = dY + 4 * (i + 1) by omega_arith]
    · rw [l20]; exact (add_arith _ _ _ j20).1
    · rw [lm]
      exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
        ((writeW32_outside _ B (d := dA + 4 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
    · have wx : w32 t.mem B (dX + 4 * i) = w32 s.mem B (dX + 4 * i) := jout.w32 (by omega_arith) (by omega_arith)
      obtain wy : w32 t.mem B (dY + 4 * i) = w32 s.mem B (dY + 4 * i) := jout.w32 (by omega_arith) (by omega_arith)
      obtain k := (add_arith (t.mem.readW (off B (dX + 4 * i)) 32) (t.mem.readW (off B (dY + 4 * i)) 32) _ j20).2
      rw [lm, l20, val32_write_top _ _ _ _ _ (by omega_arith), val32_succ s.mem B dX i, val32_succ s.mem B dY i,
        ← pow32_mul i]
      rw [← wx, ← wy]
      change _ + 2 ^ 32 * _ = w32 t.mem B (dX + 4 * i) + w32 t.mem B (dY + 4 * i) + (t.gpr .r20).toNat at k
      change _ = (_ + _ * w32 t.mem B (dX + 4 * i)) + (_ + _ * w32 t.mem B (dY + 4 * i))
      grind
  · have hfin : WP isa (.block [.store .w .r20 .r14 0]) t fun t' =>
        t'.mem = t.mem.writeW (off B (dA + 4 * n)) ((t.gpr .r20).setWidth 32) ∧ Keep [] t t' := by
      refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = t.mem.writeW (off B (dA + 4 * n))
        ((t.gpr .r20).setWidth 32)) ?_ (by decide)) fun t' ⟨h, k⟩ => ⟨h, k⟩
      prun [j14, (hs.congr jk.wr).st (show dA + 4 * n + 4 ≤ Z by omega_arith)]
    refine WP.mono hfin fun t' ⟨lm, lk⟩ => ⟨?_, ?_, (jk.trans lk).mono (by simp)⟩
    · rw [lm, val32_write_top _ _ _ _ _ (by omega_arith), ← jeq]
      congr 2
      rw [BitVec.toNat_setWidth]
      omega_arith
    · rw [lm]
      exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
        ((writeW32_outside _ B (d := dA + 4 * n) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))

/-- The registers `addMod` writes. -/
def addModRegs : List Reg := [.r0, .r3, .r5, .r8, .r9, .r14, .r15, .r16, .r17, .r20]

/-- `addMod`'s change of memory: arrays 2 and 3, then array `o`. -/
def AddFrame (B : Addr) (w o : Nat) (m m' : Mem) : Prop :=
  ∃ m₁, Outside B (slot w 2) (2 * (8 * (w + 2))) m m₁ ∧ Outside B (slot w o) (8 * (w + 2)) m₁ m'

/-- `addMod o a b`, in the arrays of `Env` with the modulus in array 0:
`[o] := [a] + [b] mod [0]`, for `[a] + [b] < 2 [0]`. -/
theorem addMod_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) {o a b : Nat}
    (ho : o < 28) (ha : a < 28) (hb : b < 28) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2) (ha3 : a ≠ 3)
    (hb2 : b ≠ 2) (hb3 : b ≠ 3) (hlt : arr s.mem B w a + arr s.mem B w b < 2 * arr s.mem B w 0) :
    WP isa (addMod o a b) s fun t =>
      (arr t.mem B w o = (arr s.mem B w a + arr s.mem B w b) % arr s.mem B w 0 ∧ AddFrame B w o s.mem t.mem) ∧
        Keep addModRegs s t := by
  have hnw := h.hs.nowrap
  have hw := h.hw
  have hw' := h.hw'
  have hZ := h.hZ
  obtain e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have hh : hdrBytes = 256 := rfl
  obtain sl := fun {j : Nat} (hj : j < 28) => slot_lt (w := w) hj
  obtain hO := sl ho; have hA := sl ha; have hB := sl hb
  obtain e0 := e 0; have e2 := e 2; have e3 := e 3; have e4 := e 4
  obtain eo := e o; have ea := e a; have eb := e b; have eo1 := e (o + 1)
  obtain e28 := e 28
  unfold addMod
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .r5) (by decide) (by decide) a) fun t₁ ⟨⟨a5, m1⟩, k1⟩ => ?_
  obtain e1 := h.keep k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (e1.base (rd := .r16) (by decide) (by decide) b) fun t₂ ⟨⟨a16, m2⟩, k2⟩ => ?_
  obtain e2' := e1.keep k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (e2'.base (rd := .r8) (by decide) (by decide) 2) fun t₃ ⟨⟨a8, m3⟩, k3⟩ => ?_
  obtain e3' := e2'.keep k3 (by decide)
  refine WP.mono (e3'.base (rd := .r9) (by decide) (by decide) 3) fun t₄ ⟨⟨a9, m4⟩, k4⟩ => ?_
  obtain e4' := e3'.keep k4 (by decide)
  obtain hm4 : t₄.mem = s.mem := by rw [m4, m3, m2, m1]
  obtain g8 : t₄.gpr .r8 = off B (slot w 2) := (k4.gpr .r8 (by decide)).trans a8
  obtain g5 : t₄.gpr .r5 = off B (slot w a) :=
    (k4.gpr .r5 (by decide)).trans ((k3.gpr .r5 (by decide)).trans ((k2.gpr .r5 (by decide)).trans a5))
  obtain g16 : t₄.gpr .r16 = off B (slot w b) := (k4.gpr .r16 (by decide)).trans ((k3.gpr .r16 (by decide)).trans a16)
  obtain k14 := ((k1.trans k2).trans k3).trans k4
  obtain ma : (o + 1) * (8 * (w + 2)) = o * (8 * (w + 2)) + 8 * (w + 2) := by rw [Nat.add_mul, Nat.one_mul]
  obtain sep : ∀ {j k : Nat}, j ≠ k → j < 28 → k < 28 →
      slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j := fun hjk hj hk => by
    rcases Nat.lt_or_gt_of_ne hjk with hl | hl
    · exact .inl (slot_lt hl)
    · exact .inr (slot_lt hl)
  obtain sa2 := sep ha2 ha (by decide); have sb2 := sep hb2 hb (by decide)
  obtain sa3 := sep ha3 ha (by decide); have sb3 := sep hb3 hb (by decide)
  obtain so2 := sep ho2 ho (by decide); have so3 := sep ho3 ho (by decide)
  -- The sum.
  refine WP.seq (WP.mono (addArr_ok (n := 2 * w) (dA := slot w 2) (dX := slot w a) (dY := slot w b) e4'.hs
    g8 g5 g16 e4'.h11 (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun s₂ ⟨hd, out₂, k₂⟩ => ?_)
  rw [hm4] at hd out₂
  obtain hs₂ := e4'.hs.congr k₂.wr
  obtain m₂ : val32 s₂.mem B (slot w 0) (2 * w) = val32 s.mem B (slot w 0) (2 * w) :=
    out₂.val32 (by omega_arith) (by omega_arith)
  obtain k₂' := k14.trans k₂
  refine WP.seq (WP.mono (subMod_ok (n := 2 * w) (dA := slot w 2) (dT := slot w 3) (dM := slot w 0) hs₂
    (by rw [k₂.gpr .r8 (by decide), g8]) (by rw [k₂.gpr .r9 (by decide), a9])
    (by rw [k₂'.gpr .r10 (by decide), h.h10]) (by rw [k₂.gpr .r11 (by decide), e4'.h11])
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₃ ⟨⟨c, hc, hD, h20⟩, out₃, k₃⟩ => ?_)
  rw [m₂] at hD
  obtain hs₃ := hs₂.congr k₃.wr
  obtain k23 := k₂.trans k₃
  obtain accA : val32 s₃.mem B (slot w 2) (2 * w) = val32 s₂.mem B (slot w 2) (2 * w) :=
    out₃.val32 (by omega_arith) (by omega_arith)
  refine WP.seq ?_
  obtain e₃ := e4'.keep k23 (by decide)
  refine WP.mono (e₃.base (rd := .r5) (by decide) (by decide) o) fun s₄ ⟨⟨a5', m₄⟩, k₄⟩ => ?_
  obtain k24 := k23.trans k₄
  refine WP.mono (selectAcc_ok (n := 2 * w) (dA := slot w 2) (dT := slot w 3) (dO := slot w o)
    (b := decide (w32 s₂.mem B (slot w 2 + 4 * (2 * w)) < c)) (hs₃.congr k₄.wr)
    (by rw [k24.gpr .r8 (by decide), g8]) (by rw [k24.gpr .r9 (by decide), a9])
    a5' (by rw [k24.gpr .r11 (by decide), e4'.h11])
    (by rw [k₄.gpr .r20 (by decide), h20]; simp only [decide_eq_true_eq])
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun t ⟨hv, out₅, k₅⟩ => ⟨⟨?_, ?_⟩, (((k14.trans k23).trans k₄).trans k₅).mono (by decide)⟩
  · rw [m₄, accA] at hv
    obtain hM := val32_lt s.mem B (slot w 0) (2 * w)
    rw [val32_succ] at hd
    show val32 t.mem B (slot w o) (2 * w) = (val32 s.mem B (slot w a) (2 * w) + val32 s.mem B (slot w b) (2 * w)) %
      val32 s.mem B (slot w 0) (2 * w)
    rw [hv, ← hd, ← Nat.add_zero (w32 s₂.mem B (slot w 2 + 4 * (2 * w))),
      ← Nat.mul_zero (2 ^ 64),
      ← VG.Proof.Bignum.csub_result hM (val32_lt _ _ _ _) hc (val32_lt _ _ _ _)
        (by rw [Nat.mul_zero, Nat.add_zero, hd]; exact hlt) hD]
    by_cases hb' : w32 s₂.mem B (slot w 2 + 4 * (2 * w)) < c <;> simp [hb']
  · refine ⟨s₄.mem, ?_, out₅.mono (Nat.le_refl _) (by omega_arith)⟩
    rw [m₄]
    exact (out₂.mono (by omega_arith) (by omega_arith)).trans (out₃.mono (by omega_arith) (by omega_arith))

/-- Arrays other than 2, 3 and `o` are kept by `addMod`. -/
theorem AddFrame.arr_eq {B : Addr} {Z w o : Nat} {m m' : Mem} (h : AddFrame B w o m m') (hZ : slot w 28 ≤ Z)
    (hnw : B.toNat + Z ≤ 2 ^ 64) {j : Nat} (hj : j < 28) (hj2 : j ≠ 2) (hj3 : j ≠ 3) (hjo : j ≠ o) (ho : o < 28) :
    arr m' B w j = arr m B w j := by
  obtain ⟨m₁, h₁, h₂⟩ := h
  obtain hJ := slot_lt (w := w) hj
  obtain sep : ∀ {k : Nat}, j ≠ k → k < 28 →
      slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j := fun hjk hk => by
    rcases Nat.lt_or_gt_of_ne hjk with hl | hl
    · exact .inl (slot_lt hl)
    · exact .inr (slot_lt hl)
  obtain s2 := sep hj2 (by decide)
  obtain s3 := sep hj3 (by decide)
  obtain so := sep hjo ho
  obtain e3 : slot w 3 = slot w 2 + 8 * (w + 2) := by simp only [slot]; omega_arith
  unfold VG.Proof.MillerRabin.PPC64LE.arr
  rw [Outside.val32 h₂ (by omega_arith) (by omega_arith), Outside.val32 h₁ (by omega_arith) (by omega_arith)]

end VG.Proof.Dsa.PPC64LE

end

end


/-!
# DSA signing on PPC64LE: `s = w (z + x r) mod q`

* `mont28_ok`: `PubMont.lean`'s `montOpN_ok` for any of the 28 arrays a
  working space of `slot w 28` octets holds, as `sValue` multiplies by r in
  array 9;
* `sValue_ok`: in the Q space, with q in array 0, w in array 4, `R² mod q` in
  array 8 and r in array 9, `w (z + x r) mod q` into array 6 (z the digest's
  scalar, x the key's last `q_len` octets).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Sign
open VG.Proof.Bignum (slot slot_sep hdr_lt_slot)

/-! ## Montgomery multiplications of any array -/

/-- `montOp o a b` for `o` among 5 and 6 and any arrays `a` and `b`, `[b] < c`. -/
theorem mont28_ok {s : State} {B : Addr} {Z w : Nat} (h : MCtx s B Z w) {o a b : Nat}
    (ho : o = 5 ∨ o = 6) (ha : a < 28) (ha2 : a ≠ 2) (hb : b < 28) (hb2 : b ≠ 2)
    (hB : arr s.mem B w b < arr s.mem B w 0) :
    WP isa (PublicChecked.montOp o a b) s fun t =>
      (arr t.mem B w o < arr s.mem B w 0 ∧
        arr t.mem B w o * 2 ^ (64 * w) % arr s.mem B w 0 = arr s.mem B w a * arr s.mem B w b % arr s.mem B w 0 ∧
        Outs B (montRanges w o) s.mem t.mem ∧ w32 t.mem B (slot w 0) = w32 s.mem B (slot w 0)) ∧
      Keep Pub.montRegs s t := by
  have hw := h.hw
  have hw' := h.hw'
  obtain h8 := slot_lt (w := w) (show 8 < 28 by decide)
  refine WP.mono (Pub.montOpN_ok h.hs (n := 28) (by decide) (by omega_using [ho]) ha hb (by omega_using [ho]) (by omega_using [ho]) ha2 hb2
    (by omega_arith) (by omega_arith) h.hZ h.h10 h.h29 h.h11 h.h12 h.inv hB) fun t ⟨⟨hlt, heq, hout⟩, k⟩ =>
    ⟨⟨hlt, heq, hout, ?_⟩, k⟩
  refine congrArg BitVec.toNat (Mem.readW_congr fun i hi => hout _ fun r hr => ?_)
  have := h.hs.nowrap
  obtain h0 := slot_lt (w := w) (show 0 < 28 by decide)
  have hZ := h.hZ
  rw [ofs_off B (by omega_arith)]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases ho with rfl | rfl <;> rcases hr with rfl | rfl | rfl <;> simp only [slot] <;> omega_arith

/-! ## The arrays a step keeps -/

/-- The Q space's arrays but those in `ws` are kept. -/
def AKeep (L : Lay) (ws : List Nat) (m m' : Mem) : Prop :=
  ∀ j, j < 28 → j ∉ ws → arrQ m' L j = arrQ m L j

theorem AKeep.get {L : Lay} {ws : List Nat} {m m' : Mem} (h : AKeep L ws m m') (j : Nat)
    (hj : j < 28 := by decide) (hn : j ∉ ws := by decide) : arr m' L.Q 4 j = arr m L.Q 4 j :=
  h j hj hn

theorem AKeep.trans {L : Lay} {ws ws' : List Nat} {m₁ m₂ m₃ : Mem} (h₁ : AKeep L ws m₁ m₂)
    (h₂ : AKeep L ws' m₂ m₃) : AKeep L (ws ++ ws') m₁ m₃ := fun j hj hn =>
  (h₂ j hj fun h => hn (List.mem_append_right _ h)).trans (h₁ j hj fun h => hn (List.mem_append_left _ h))

theorem AKeep.of_eq {L : Lay} {m m' : Mem} (h : m' = m) : AKeep L [] m m' := fun _ _ _ => by rw [h]

theorem AKeep.one {L : Lay} {o n : Nat} {m m' : Mem} (h : Outside L.Q (slot 4 o) n m m') (hn : n ≤ 48) :
    AKeep L [o] m m' := fun j hj ho =>
  Outside.arrEq (h.mono (Nat.le_refl _) (by omega_arith)) hj (by simpa only [List.mem_singleton] using ho) (by decide)

theorem AKeep.red {L : Lay} {m m' : Mem} (h : Outside L.Q (slot 4 1) (24 * (4 + 2)) m m') :
    AKeep L [1, 2, 3] m m' := fun j hj hn => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  exact Outside.val32 h (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith)

theorem AKeep.add {L : Lay} {o : Nat} {m m' : Mem} (h : AddFrame L.Q 4 o m m') (hnw : L.Q.toNat + 1600 ≤ 2 ^ 64)
    (ho : o < 28) : AKeep L [2, 3, o] m m' := fun j hj hn => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  exact h.arr_eq (Z := 1600) (by decide) hnw hj hn.1 hn.2.1 hn.2.2 ho

theorem AKeep.mont {L : Lay} {o : Nat} {m m' : Mem} (h : Outs L.Q (montRanges 4 o) m m') :
    AKeep L [2, 3, o] m m' := fun j hj hn => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  exact Outs.arrEq_mont h hj hn.1 hn.2.1 hn.2.2 (by decide)

theorem AddFrame.qarr {L : Lay} {o : Nat} {m m' : Mem} (h : AddFrame L.Q 4 o m m') (ho1 : 1 ≤ o) (ho : o < 28) :
    QArr L m m' := by
  obtain ⟨m₁, h₁, h₂⟩ := h
  exact (QArr.of h₁ (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith)).trans
    (QArr.of h₂ (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith))

/-! ## s -/

/-- The registers `sValue` writes. -/
def sValueRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r24, .r25,
    .r30]

/-- `sValueRegs`, and `r10` and `r31`, which `sValue` restores. -/
def sValueAll : List Reg := .r10 :: .r31 :: sValueRegs

/-- `sValue`: in the Q space, `w (z + x r) mod q` into array 6. -/
theorem sValue_ok {s : State} {L : Lay} {key nonce dig : Addr} {qb d : Nat} (h : QS s L key nonce dig)
    (hL : L.Ok) (h2 : s.gpr .r2 = pack L.pl L.ql qb d) (hqb : qb ≤ L.ql) (hd : d < 2 ^ 16)
    (hdg : Src s L dig (min d qb)) (hk : Src s L key (3 * L.pl + 2 * L.ql))
    (hq3 : 3 ≤ arrQ s.mem L 0) (hqo : arrQ s.mem L 0 % 2 = 1)
    (h8 : arrQ s.mem L 8 = 2 ^ (128 * 4) % arrQ s.mem L 0)
    (h4 : arrQ s.mem L 4 < arrQ s.mem L 0) (h9 : arrQ s.mem L 9 < arrQ s.mem L 0)
    (hz : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) < 2 * arrQ s.mem L 0) :
    WP isa sValue s fun t =>
      (QS t L key nonce dig ∧
        arrQ t.mem L 6 = arrQ s.mem L 4 * ((Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) %
          arrQ s.mem L 0 + xOf s.mem L key * arrQ s.mem L 9 % arrQ s.mem L 0) % arrQ s.mem L 0) %
            arrQ s.mem L 0 ∧
        arrQ t.mem L 9 = arrQ s.mem L 9 ∧ QArr L s.mem t.mem) ∧ Keep sValueRegs s t := by
  have hql := hL.ql
  obtain hcop : Nat.Coprime (2 ^ (64 * 4)) (arrQ s.mem L 0) := VG.Proof.Bignum.coprime_pow2 hqo _
  obtain hRR := pow_sq_eq 4
  generalize (2 : Nat) ^ (128 * 4) = R2 at h8 hRR
  have hnw : L.Q.toNat + 1600 ≤ 2 ^ 64 := h.inq.env.hs.nowrap
  unfold sValue
  -- z into array 6, 0 into array 7, `z mod q` into array 6.
  refine WP.seq (WP.mono (prod_scalar_ok h hL h2 hqb hd hdg) fun s₁ ⟨⟨Q1, v6, o1⟩, k1⟩ => ?_)
  generalize Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) = z at v6 hz ⊢
  obtain f1 : AKeep L [6] s.mem s₁.mem := AKeep.one o1 (by omega_arith)
  obtain qa1 : QArr L s.mem s₁.mem := QArr.of o1 (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith)
  refine WP.seq (WP.mono (zeroArr_ok Q1.inq.env (j := 7) (by decide)) fun s₂ ⟨⟨z7, o2⟩, k2⟩ => ?_)
  obtain Q2 := Q1.step k2 (by decide)
  obtain f2 : AKeep L [7] s₁.mem s₂.mem := AKeep.one o2 (by omega_arith)
  obtain qa2 : QArr L s₁.mem s₂.mem := QArr.of o2 (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith)
  obtain q2 : arr s₂.mem L.Q 4 0 = arrQ s.mem L 0 := (qa1.trans qa2).arr0
  obtain z2 : arr s₂.mem L.Q 4 6 = z := (f2.get 6).trans v6
  refine WP.seq (WP.mono (addMod_ok Q2.inq.env (o := 6) (a := 6) (b := 7) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [z2, z7, q2]; omega_arith)) fun s₃ ⟨⟨a6, fr3⟩, k3⟩ => ?_)
  rw [z2, z7, q2, Nat.add_zero] at a6
  obtain Q3 := Q2.step k3 (by decide)
  obtain f3 := AKeep.add fr3 hnw (by decide)
  obtain qa13 : QArr L s.mem s₃.mem := (qa1.trans qa2).trans (AddFrame.qarr fr3 (by decide) (by decide))
  have q3 : arr s₃.mem L.Q 4 0 = arrQ s.mem L 0 := qa13.arr0
  obtain k13 := (k1.trans k2).trans k3
  -- x's octets, and `x mod q` into array 1.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (ptrX_ok Q3.regs) fun s₄ ⟨⟨b12, b6, m4⟩, k4⟩ => ?_
  refine WP.mono (WP.keep [.r30, .r31] (Q := fun u => u.gpr .r30 = off key (3 * L.pl + L.ql) ∧
      u.gpr .r31 = BitVec.ofNat 64 L.ql ∧ u.mem = s₄.mem) (by prun [b12, b6, BitVec.add_zero]) (by decide))
    fun s₅ ⟨⟨c30, c31, m5⟩, k5⟩ => ?_
  obtain k35 := k4.trans k5
  have e3 := Q3.inq.env
  obtain hx := (hk.keep (k13.trans k35).rd (k13.trans k35).wr).sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega_arith)
  refine WP.seq (WP.mono (ModArith.reduce_ok (B := L.Q) (Z := 1600) (w := 4) (D := off key (3 * L.pl + L.ql))
    (L := L.ql) (e3.hs.congr k35.wr) (by decide) (by decide) (by decide)
    ((k35.gpr .r10 (by decide)).trans e3.h10) ((k35.gpr .r29 (by decide)).trans e3.h29)
    ((k35.gpr .r11 (by decide)).trans e3.h11)
    (by rw [m5, m4]; show 0 < arr s₃.mem L.Q 4 0; rw [q3]; omega_arith)
    (by rw [c30]; exact (BitVec.add_zero _).symm) c31 (by omega_arith) (by omega_arith) hx.rd (hx.sepQ hL))
    fun s₆ ⟨⟨v1, o6⟩, k6⟩ => ?_)
  obtain x6 : arr s₆.mem L.Q 4 1 = xOf s.mem L key % arrQ s.mem L 0 := by
    refine v1.trans ?_
    rw [m5, m4, (hk.sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega_arith)).bytes (qa13.qbody.body hL) hL.z256]
    show _ % arr s₃.mem L.Q 4 0 = _
    rw [q3]
    rfl
  obtain f6 := AKeep.red o6
  obtain qa6 : QArr L s₅.mem s₆.mem := QArr.of o6 (Nat.le_refl _) (by simp only [slot_eq]; omega_arith)
  refine WP.seq (WP.mono (WP.keep [.r31] (Q := fun u => u.gpr .r31 = L.Q ∧ u.mem = s₆.mem)
      (by prun [((k35.trans k6).gpr .r23 (by decide)).trans Q3.inq.h23, BitVec.add_zero]) (by decide))
    fun s₇ ⟨⟨a31, m7⟩, k7⟩ => ?_)
  obtain k37 := (k35.trans k6).trans k7
  obtain Q7 : QS s₇ L key nonce dig := ⟨⟨⟨e3.hs.congr k37.wr, (k37.gpr .r10 (by decide)).trans e3.h10,
    (k37.gpr .r29 (by decide)).trans e3.h29, (k37.gpr .r11 (by decide)).trans e3.h11, a31, e3.hw, e3.hw', e3.hZ⟩,
    (k37.gpr .r21 (by decide)).trans Q3.inq.h21, (k37.gpr .r23 (by decide)).trans Q3.inq.h23⟩,
    Q3.scr.congr k37.wr, Q3.regs.keep k37⟩
  -- `x mod q` into array 5, `R² mod q` into array 1, `-q⁻¹`.
  refine WP.seq (WP.mono (copy_ok Q7.inq.env (o := 5) (a := 1) (by decide) (by decide) (by decide))
    fun s₈ ⟨⟨v5, o8⟩, k8⟩ => ?_)
  rw [m7, x6] at v5
  obtain Q8 := Q7.step k8 (by decide)
  obtain f8 : AKeep L [5] s₇.mem s₈.mem := AKeep.one o8 (by omega_arith)
  refine WP.seq (WP.mono (copy_ok Q8.inq.env (o := 1) (a := 8) (by decide) (by decide) (by decide))
    fun s₉ ⟨⟨v1', o9⟩, k9⟩ => ?_)
  obtain Q9 := Q8.step k9 (by decide)
  obtain f9 : AKeep L [1] s₈.mem s₉.mem := AKeep.one o9 (by omega_arith)
  obtain F38 := ((AKeep.of_eq (L := L) (m5.trans m4)).trans f6).trans ((AKeep.of_eq m7).trans f8)
  obtain F08 := ((f1.trans f2).trans f3).trans F38
  obtain qa35 : QArr L s₃.mem s₅.mem := by rw [m5, m4]; exact QArr.refl _ _
  obtain qa68 : QArr L s₆.mem s₈.mem := by
    rw [← m7]; exact QArr.of o8 (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith)
  obtain qa9 : QArr L s.mem s₉.mem := (((qa13.trans qa35).trans qa6).trans qa68).trans
    (QArr.of o9 (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith))
  have q9 : arr s₉.mem L.Q 4 0 = arrQ s.mem L 0 := qa9.arr0
  obtain hodd : (word s₉.mem L.Q (slot 4 0)).toNat % 2 = 1 :=
    word_odd _ _ _ (2 * 4) (by decide) (by show arr s₉.mem L.Q 4 0 % 2 = 1; rw [q9]; exact hqo)
  refine WP.seq (WP.mono (Pub.minv_ok Q9.inq.env.hs Q9.inq.env.h10 (by decide) hodd)
    fun s₁₀ ⟨⟨i12, inv, m10⟩, k10⟩ => ?_)
  obtain M10 : MCtx s₁₀ L.Q 1600 4 := ⟨Q9.inq.env.keep k10 (by decide), i12, by rw [m10]; exact inv⟩
  obtain Q10 := Q9.step k10 (by decide)
  obtain F010 := (F08.trans f9).trans (AKeep.of_eq (L := L) m10)
  obtain A0 : arr s₁₀.mem L.Q 4 0 = arrQ s.mem L 0 := by rw [m10]; exact q9
  obtain A1 : arr s₁₀.mem L.Q 4 1 = R2 % arrQ s.mem L 0 := by rw [m10, v1', F08.get 8]; exact h8
  obtain A4 : arr s₁₀.mem L.Q 4 4 = arrQ s.mem L 4 := F010.get 4
  obtain A5 : arr s₁₀.mem L.Q 4 5 = xOf s.mem L key % arrQ s.mem L 0 := by rw [m10, f9.get 5]; exact v5
  obtain A6 : arr s₁₀.mem L.Q 4 6 = z % arrQ s.mem L 0 :=
    ((F38.trans f9).trans (AKeep.of_eq (L := L) m10)).get 6 |>.trans a6
  obtain A9 : arr s₁₀.mem L.Q 4 9 = arrQ s.mem L 9 := F010.get 9
  -- `x r mod q` into array 5.
  refine WP.seq (WP.mono (mont28_ok M10 (o := 5) (a := 5) (b := 9) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [A9, A0]; exact h9)) fun s₁₁ ⟨⟨_, e11, o11, w11⟩, k11⟩ => ?_)
  obtain M11 := M10.keep k11 (by decide) w11
  obtain Q11 := Q10.step k11 (by decide)
  rw [A0, A5, A9] at e11
  obtain f11 := AKeep.mont o11
  obtain B0 : arr s₁₁.mem L.Q 4 0 = arrQ s.mem L 0 := (f11.get 0).trans A0
  obtain B1 : arr s₁₁.mem L.Q 4 1 = R2 % arrQ s.mem L 0 := (f11.get 1).trans A1
  refine WP.seq (WP.mono (mont28_ok M11 (o := 5) (a := 5) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [B1, B0]; exact Nat.mod_lt _ (by omega_arith))) fun s₁₂ ⟨⟨l12, e12, o12, w12⟩, k12⟩ => ?_)
  obtain M12 := M11.keep k12 (by decide) w12
  obtain Q12 := Q11.step k12 (by decide)
  rw [B0] at l12
  rw [B0, B1] at e12
  obtain X12 : arr s₁₂.mem L.Q 4 5 = xOf s.mem L key % arrQ s.mem L 0 * arrQ s.mem L 9 % arrQ s.mem L 0 :=
    prod_mont_back hcop l12 e11 (by rw [e12, hRR])
  obtain f12 := AKeep.mont o12
  obtain F1012 := f11.trans f12
  obtain C0 : arr s₁₂.mem L.Q 4 0 = arrQ s.mem L 0 := (F1012.get 0).trans A0
  obtain C6 : arr s₁₂.mem L.Q 4 6 = z % arrQ s.mem L 0 := (F1012.get 6).trans A6
  -- `z + x r mod q` into array 6.
  obtain l1 := Nat.mod_lt z (show 0 < arrQ s.mem L 0 by omega_arith)
  obtain l2 := Nat.mod_lt (xOf s.mem L key % arrQ s.mem L 0 * arrQ s.mem L 9) (show 0 < arrQ s.mem L 0 by omega_arith)
  refine WP.seq (WP.mono (addMod_ok M12.toEnv (o := 6) (a := 6) (b := 5) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [C6, X12, C0]; omega_arith)) fun s₁₃ ⟨⟨a13, fr13⟩, k13'⟩ => ?_)
  rw [C6, X12, C0, Nat.mod_mul_mod] at a13
  obtain qa13' := AddFrame.qarr fr13 (by decide) (by decide)
  obtain M13 := M12.keep k13' (by decide)
    (Outside.w32 qa13' (by simp only [slot_eq]; omega_arith) (by simp only [slot_eq]; omega_arith))
  obtain Q13 := Q12.step k13' (by decide)
  obtain f13 := AKeep.add fr13 hnw (by decide)
  obtain F1013 := F1012.trans f13
  obtain D0 : arr s₁₃.mem L.Q 4 0 = arrQ s.mem L 0 := (F1013.get 0).trans A0
  obtain D1 : arr s₁₃.mem L.Q 4 1 = R2 % arrQ s.mem L 0 := (F1013.get 1).trans A1
  obtain D4 : arr s₁₃.mem L.Q 4 4 = arrQ s.mem L 4 := (F1013.get 4).trans A4
  -- `w (z + x r) mod q` into array 6.
  refine WP.seq (WP.mono (mont28_ok M13 (o := 6) (a := 6) (b := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [D4, D0]; exact h4)) fun s₁₄ ⟨⟨_, e14, o14, w14⟩, k14⟩ => ?_)
  obtain M14 := M13.keep k14 (by decide) w14
  obtain Q14 := Q13.step k14 (by decide)
  rw [D0, a13, D4] at e14
  obtain f14 := AKeep.mont o14
  obtain E0 : arr s₁₄.mem L.Q 4 0 = arrQ s.mem L 0 := (f14.get 0).trans D0
  obtain E1 : arr s₁₄.mem L.Q 4 1 = R2 % arrQ s.mem L 0 := (f14.get 1).trans D1
  refine WP.mono (mont28_ok M14 (o := 6) (a := 6) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [E1, E0]; exact Nat.mod_lt _ (by omega_arith))) fun t ⟨⟨lt, et, ot, _⟩, kt⟩ => ?_
  rw [E0] at lt
  rw [E0, E1] at et
  obtain ft := AKeep.mont ot
  obtain Ft := (((F010.trans F1013).trans f14).trans ft)
  obtain qat : QArr L s.mem t.mem := (((qa9.trans (by rw [m10]; exact QArr.refl _ _)).trans
    (prod_qarr o11 (by decide))).trans ((prod_qarr o12 (by decide)).trans qa13')).trans
    ((prod_qarr o14 (by decide)).trans (prod_qarr ot (by decide)))
  obtain Qt := Q14.step kt (by decide)
  obtain kw : Keep sValueAll s t :=
    (((((((((((((k1.mono (rs' := sValueAll)).trans' (k2.mono)).trans' (k3.mono)).trans' (k4.mono)).trans'
      (k5.mono)).trans' (k6.mono)).trans' (k7.mono)).trans' (k8.mono)).trans' (k9.mono)).trans'
      (k10.mono)).trans' (k11.mono)).trans' (k12.mono)).trans' (k13'.mono)).trans' ((k14.mono).trans' (kt.mono))
  refine ⟨⟨Qt, ?_, Ft.get 9, qat⟩, ⟨fun r hr => ?_, kw.rd, kw.wr, kw.sp, kw.lr⟩⟩
  · exact (prod_mont_back hcop lt e14 (by rw [et, hRR])).trans (by rw [Nat.mul_comm _ (arrQ s.mem L 4)])
  · by_cases e10 : r = .r10
    · subst e10; rw [Qt.inq.env.h10, h.inq.env.h10]
    by_cases e31 : r = .r31
    · subst e31; rw [Qt.inq.env.h31, h.inq.env.h31]
    exact kw.gpr r fun h' => (List.mem_cons.mp h').elim e10 fun h' => (List.mem_cons.mp h').elim e31 hr

end VG.Proof.Dsa.PPC64LE

end

end


/-!
# DSA signing on PPC64LE: after the check of the key

`sbody_ok`: for a key with `g^x mod p = y`, `Sign.body` writes to `out` r's
and s's `q_len` octets, most significant first, and leaves 1 in `r3`, exactly
when `0 < x < q`, `0 < k < q`, `g^x mod p = y`, `r ≠ 0` and `s ≠ 0`
(`SignOk`), for
`r = (g^k mod p) mod q` (`sigR`) and `s = k^(q − 2) (z + x r) mod q`
(`sigS`), z the digest's first `min(digest_len, bitLength q / 8)` octets;
else zeros and 0. Memory changes only in `scratch`, apart from the saved
registers, and in `out`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Sign
open VG.Proof.Bignum (slot)

/-- r, from the key and the nonce. -/
def sigR (p q g k : Nat) : Nat := g ^ k % p % q

/-- s, from x, the nonce, the digest's scalar and r. -/
def sigS (q x k z r : Nat) : Nat := k ^ (q - 2) % q * ((z % q + x * r % q) % q) % q

/-- The checks of signing past the public key's. -/
def SignOk (p q g y x k z : Nat) : Prop :=
  (0 < x ∧ x < q) ∧ (0 < k ∧ k < q) ∧ g ^ x % p = y ∧ sigR p q g k ≠ 0 ∧ sigS q x k z (sigR p q g k) ≠ 0

instance (p q g y x k z : Nat) : Decidable (SignOk p q g y x k z) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A change past `scratch`'s header keeps its word `hOut`. -/
theorem Body.hOut {L : Lay} {m m' : Mem} (h : Body L m m') : word m' L.S hOut = word m L.S hOut :=
  Outside.word h (Or.inl (by decide)) (by decide)

/-- A change past `scratch`'s header keeps its word `hMask`. -/
theorem Body.hMask {L : Lay} {m m' : Mem} (h : Body L m m') : word m' L.S hMask = word m L.S hMask :=
  Outside.word h (Or.inl (by decide)) (by decide)

/-- `2^bitLength q ≤ 2 q`. -/
theorem pow_bitLength_le {q : Nat} (hq : q ≠ 0) : 2 ^ Spec.Dsa.bitLength q ≤ 2 * q := by
  simp only [Spec.Dsa.bitLength, hq, ite_false]
  rw [Nat.pow_succ]
  have := Nat.log2_self_le hq
  omega_arith

theorem encodeBE_zero (n : Nat) : Spec.Dsa.encodeBE n 0 = List.replicate n 0 := by
  rw [VG.Proof.Dsa.encodeBE_i2osp, VG.Proof.Bignum.i2osp_zero']

/-- Two values' octets, one after the other. -/
theorem out_bytes {m : Mem} {out : Addr} {ql a b : Nat} (ha : a < 256 ^ ql) (hb : b < 256 ^ ql)
    (h1 : Spec.Rsa.os2ip (Spec.Rsa.bytesAt m out ql) = a)
    (h2 : Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off out ql) ql) = b) :
    Spec.Rsa.bytesAt m out (2 * ql) = Spec.Dsa.encodeBE ql a ++ Spec.Dsa.encodeBE ql b := by
  obtain e1 := VG.Proof.Dsa.bytesAt_slice m out (total := 2 * ql) (offset := 0) (len := ql) (by omega_arith)
  obtain e2 := VG.Proof.Dsa.bytesAt_slice m out (total := 2 * ql) (offset := ql) (len := ql) (by omega_arith)
  simp only [List.drop_zero, BitVec.add_zero] at e1
  rw [List.take_of_length_le (by simp only [List.length_drop, VG.Proof.Bignum.bytesAt_length]; omega_arith)] at e2
  rw [← List.take_append_drop ql (Spec.Rsa.bytesAt m out (2 * ql)), e1, e2,
    (VG.Proof.Dsa.encodeBE_eq_bytes (VG.Proof.Bignum.bytesAt_length _ _ _) ha).mpr h1.symm,
    (VG.Proof.Dsa.encodeBE_eq_bytes (VG.Proof.Bignum.bytesAt_length _ _ _) hb).mpr h2.symm]

/-- q fits in its `q_len` octets. -/
theorem qOf_lt {s₀ s : State} {L : Lay} {key : Addr} (hkp : Kept L s₀.mem s.mem)
    (hk : Src s L key (3 * L.pl + L.ql)) : qOf s₀.mem L key < 2 ^ (8 * L.ql) := by
  rw [← (key_kept hk hkp.out).2.1, qOf, ← VG.Proof.Bignum.pow256_eq]
  have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)
  rwa [VG.Proof.Bignum.bytesAt_length] at this

/-- `Sign.body` up to `output` (here any `c`): `sValue` leaves r in the Q
space's array 9, s in its array 6, and in the header's word `hMask` the mask
of the checks but `s ≠ 0`, keeping `hOut`. -/
theorem sprefix_ok {s₀ s : State} {L : Lay} {key nonce dig out : Addr} {d : Nat} {c : Prog isa}
    {Q : State → Prop}
    (hL : L.Ok) (hK : KeyOk s₀.mem L key) (hc : Checked s₀ s L key nonce dig d)
    (hkp : Kept L s₀.mem s.mem) (hk : Src s L key (3 * L.pl + 2 * L.ql)) (hn : Src s L nonce L.ql)
    (hd : d < 2 ^ 16) (hdg : Src s L dig d) (hw : word s.mem L.S hOut = out)
    (hcont : ∀ t, QS t L key nonce dig → Kept L s.mem t.mem → word t.mem L.S hOut = out →
      word t.mem L.S hMask = mask (
        decide ((0 < kOf s.mem L nonce ∧ kOf s.mem L nonce < qOf s₀.mem L key) ∧
          (0 < xOf s.mem L key ∧ xOf s.mem L key < qOf s₀.mem L key) ∧
          sigR (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (kOf s.mem L nonce) ≠ 0)) →
      arrQ t.mem L 9 = sigR (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (kOf s.mem L nonce) →
      arrQ t.mem L 6 = sigS (qOf s₀.mem L key) (xOf s.mem L key) (kOf s.mem L nonce)
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d (Spec.Dsa.bitLength (qOf s₀.mem L key) / 8))))
        (sigR (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (kOf s.mem L nonce)) →
      Keep bodyRegs s t → WP isa c t Q) :
    WP isa (.seq (.block markValid) (.seq gk (.seq rRanges (.seq Verify.qMinus2 (.seq inverseK
      (.seq sValue c)))))) s Q := by
  have hZ := hL.z256
  have hpl := hL.pl
  have hql := hL.ql
  have hnw := hL.nowrap
  have hw16 := hL.wp_ge
  have hw8 := hL.wp_eq
  have hbe := hL.buf_end
  have hq28 : L.qOff = slot L.wp 28 := rfl
  obtain hqZ : slot L.wp 28 + 1600 ≤ L.Z := by simp only [Lay.bOff, Lay.qOff] at hbe; omega_arith
  obtain e8 := Lay.slot_eq L.wp 8; have e24 := Lay.slot_eq L.wp 24; have e28 := Lay.slot_eq L.wp 28
  obtain ⟨ip, scr, regs, p0, -, p8, q0, -, r2⟩ := hc
  obtain hk3 : Src s L key (3 * L.pl + L.ql) := hk.take (by omega_arith)
  obtain ⟨-, -, eg, ey⟩ := key_kept hk3 hkp.out
  obtain hqlt := qOf_lt hkp hk3
  unfold KeyOk at hK
  generalize pOf s₀.mem L key = p at hK p0 p8 hcont
  generalize qOf s₀.mem L key = q at hK q0 r2 hqlt hcont
  generalize gOf s₀.mem L key = g at hK eg hcont
  generalize yOf s₀.mem L key = y at hK ey hcont
  obtain B := VG.Proof.Dsa.supported_bounds hK.1.1
  have hqo : q % 2 = 1 := hK.1.2.1
  have hpo : p % 2 = 1 := hK.1.2.2
  obtain hq8 : Spec.Dsa.bitLength q = 8 * (Spec.Dsa.bitLength q / 8) := by
    have := hK.1.1; unfold Spec.Dsa.supportedSizes at this; omega_arith
  generalize Spec.Dsa.bitLength q / 8 = n at r2 hq8 hcont
  obtain hnq : n ≤ L.ql := by
    obtain hq0 : q ≠ 0 := by omega_arith
    obtain hlog : q.log2 < 8 * L.ql := (Nat.log2_lt hq0).mpr hqlt
    have : Spec.Dsa.bitLength q = q.log2 + 1 := by simp [Spec.Dsa.bitLength, hq0]
    omega_arith
  -- The values read from outside `scratch`, kept.
  obtain hdgn : Src s L dig (min d n) := hdg.take (Nat.min_le_left _ _)
  obtain vals : ∀ {m : Mem}, Kept L s.mem m → xOf m L key = xOf s.mem L key ∧ kOf m L nonce = kOf s.mem L nonce ∧
      gOf m L key = g ∧ Spec.Rsa.bytesAt m dig (min d n) = Spec.Rsa.bytesAt s.mem dig (min d n) := fun hm =>
    ⟨by simp only [xOf]; rw [(hk.sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega_arith)).kept hm.out],
      by simp only [kOf]; rw [hn.kept hm.out], (key_kept hk3 hm.out).2.2.1.trans eg, hdgn.kept hm.out⟩
  generalize hX : xOf s.mem L key = X at vals hcont
  generalize kOf s.mem L nonce = K at vals hcont
  -- The mask of `g^x mod p = y`, all ones.
  refine WP.seq (WP.mono (markValid_ok hL scr regs ip)
    fun s₁ ⟨⟨mx₁, ip₁, o₁, p0₁, sav₁, hout₁⟩, k₁⟩ => ?_)
  obtain K₁ : Kept L s.mem s₁.mem := ⟨o₁.mono (Nat.zero_le _) (by omega_arith), sav₁⟩
  obtain q0₁ : arrQ s₁.mem L 0 = q := by
    rw [arrQ, arr, Outside.val32 (keepQ_of hL fun x hx => o₁ x (Or.inr (by omega_arith))) (by decide) (by decide)]
    exact q0
  obtain p8₁ : arrP s₁.mem L 24 = arrP s.mem L 24 :=
    Outside.val32 o₁ (Or.inr (by omega_arith)) (by omega_arith)
  -- `g^k mod p` to the buffer.
  refine WP.seq (WP.mono (gk_ok (p := p) hL (scr.congr k₁.wr) (regs.keep k₁) ip₁ (hk.keep k₁.rd k₁.wr)
      (hn.keep k₁.rd k₁.wr) (p0₁.trans p0) (by omega_arith) hpo (p8₁.trans p8))
    fun s₂ ⟨⟨gk₂, ip₂, B₂, Qk₂, _, _, _, a4₂⟩, k₂⟩ => ?_)
  rw [(vals K₁).2.2.1, (vals K₁).2.1] at gk₂
  obtain K₂ := K₁.trans (Kept.ofBody hL B₂)
  obtain k₁₂ := k₁.trans k₂
  obtain q0₂ : arrQ s₂.mem L 0 = q := by
    rw [arrQ, arr, Outside.val32 Qk₂ (by decide) (by decide)]; exact q0₁
  obtain mx₂ : word s₂.mem L.S hMask = mask true := (Body.hMask B₂).trans mx₁
  obtain hout₂ : word s₂.mem L.S hOut = out := ((Body.hOut B₂).trans hout₁).trans hw
  -- r, and the masks of the ranges; `R² mod q`.
  refine WP.seq (WP.mono (rRanges_ok hL (scr.congr k₁₂.wr) ((regs.keep k₁).keep k₂) (hk.keep k₁₂.rd k₁₂.wr)
      (hn.keep k₁₂.rd k₁₂.wr) ip₂ a4₂ (by rw [q0₂]; omega_arith) (by rw [q0₂]; exact hqo) mx₂)
    fun s₃ ⟨⟨Q₃, r9₃, m₃, h8₃, a0₃, mf, Bf, fb⟩, k₃⟩ => ?_)
  rw [q0₂, gk₂] at r9₃
  rw [q0₂, gk₂, (vals K₂).1, (vals K₂).2.1, Bool.true_and] at m₃
  rw [q0₂] at h8₃
  obtain K₃ := (K₂.trans (Kept.ofBody hL Bf)).trans (Kept.ofMask hL fb)
  obtain k₁₃ := k₁₂.trans k₃
  obtain q0₃ : arrQ s₃.mem L 0 = q := a0₃.trans q0₂
  obtain hout₃ : word s₃.mem L.S hOut = out := by
    rw [Outside.word fb (Or.inr (by decide)) (by decide), Body.hOut Bf]; exact hout₂
  -- `q − 2`.
  refine WP.seq (WP.mono (qMinus2_ok Q₃ hL (by rw [q0₃]; omega_arith) (by rw [q0₃]; exact hqlt))
    fun s₅ ⟨⟨Q₅, bq₅, a8₅, qb₅, a9₅⟩, k₅⟩ => ?_)
  rw [q0₃] at bq₅
  obtain q0₅ : arrQ s₅.mem L 0 = q := qb₅.arr0.trans q0₃
  obtain B₃₅ : Body L s₃.mem s₅.mem := qb₅.body hL
  obtain K₅ := K₃.trans (Kept.ofBody hL B₃₅)
  obtain k₁₅ := k₁₃.trans k₅
  -- `w = k^(q − 2) mod q`.
  refine WP.seq (WP.mono (inverseK_ok Q₅ hL (hn.keep k₁₅.rd k₁₅.wr) (by rw [q0₅]; omega_arith) (by rw [q0₅]; exact hqo)
      (by rw [a8₅, h8₃, q0₅])) fun s₆ ⟨⟨Q₆, w4₆, a8₆, qa₆, a9₆⟩, k₆⟩ => ?_)
  rw [q0₅, bq₅, (vals K₅).2.1] at w4₆
  obtain q0₆ : arrQ s₆.mem L 0 = q := qa₆.arr0.trans q0₅
  obtain B₃₆ := B₃₅.trans (qa₆.qbody.body hL)
  obtain K₆ := K₃.trans (Kept.ofBody hL B₃₆)
  obtain k₁₆ := k₁₅.trans k₆
  obtain r9₆ : arrQ s₆.mem L 9 = g ^ K % p % q := a9₆.trans (a9₅.trans r9₃)
  -- s.
  obtain hz : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s₆.mem dig (min d n)) < 2 * arrQ s₆.mem L 0 := by
    rw [(vals K₆).2.2.2, q0₆]
    refine Nat.lt_of_lt_of_le (VG.Proof.Dsa.decodeBE_lt _) ?_
    rw [VG.Proof.Bignum.bytesAt_length]
    refine Nat.le_trans (Nat.pow_le_pow_right (by decide) (Nat.min_le_right d n)) ?_
    have := pow_bitLength_le (q := q) (by omega_arith)
    rw [hq8, Nat.pow_mul] at this
    exact this
  refine WP.seq (WP.mono (sValue_ok Q₆ hL ((k₁₆.gpr .r2 (by decide)).trans r2) hnq hd
      (hdgn.keep k₁₆.rd k₁₆.wr) (hk.keep k₁₆.rd k₁₆.wr) (by rw [q0₆]; omega_arith) (by rw [q0₆]; exact hqo)
      (by rw [a8₆, a8₅, h8₃, q0₆]) (by rw [w4₆, q0₆]; exact Nat.mod_lt _ (by omega_arith))
      (by rw [r9₆, q0₆]; exact Nat.mod_lt _ (by omega_arith)) hz)
    fun s₇ ⟨⟨Q₇, s6₇, a9₇, qa₇⟩, k₇⟩ => ?_)
  rw [q0₆, w4₆, r9₆, (vals K₆).1, (vals K₆).2.2.2] at s6₇
  obtain B₃₇ := B₃₆.trans (qa₇.qbody.body hL)
  exact hcont s₇ Q₇ (K₃.trans (Kept.ofBody hL B₃₇)) ((Body.hOut B₃₇).trans hout₃) ((Body.hMask B₃₇).trans m₃)
    (a9₇.trans r9₆) s6₇ (keep_but21 (k₁₆.trans k₇) (by decide) (by decide))

theorem sbody_ok {s₀ s : State} {L : Lay} {key nonce dig out : Addr} {d : Nat}
    (hL : L.Ok) (hK : KeyOk s₀.mem L key)
    (hgx : gOf s₀.mem L key ^ xOf s.mem L key % pOf s₀.mem L key = yOf s₀.mem L key)
    (hc : Checked s₀ s L key nonce dig d)
    (hkp : Kept L s₀.mem s.mem) (hk : Src s L key (3 * L.pl + 2 * L.ql)) (hn : Src s L nonce L.ql)
    (hd : d < 2 ^ 16) (hdg : Src s L dig d)
    (hw : word s.mem L.S hOut = out) (ho : Scr s out (2 * L.ql)) (hos : Src s L out (2 * L.ql)) :
    WP isa Sign.body s fun t =>
      (Spec.Rsa.bytesAt t.mem out (2 * L.ql) =
          (if SignOk (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (yOf s₀.mem L key)
              (xOf s.mem L key) (kOf s.mem L nonce)
              (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d (Spec.Dsa.bitLength (qOf s₀.mem L key) / 8))))
            then Spec.Dsa.encodeBE L.ql (sigR (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key)
                (kOf s.mem L nonce)) ++
              Spec.Dsa.encodeBE L.ql (sigS (qOf s₀.mem L key) (xOf s.mem L key) (kOf s.mem L nonce)
                (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d (Spec.Dsa.bitLength (qOf s₀.mem L key) / 8))))
                (sigR (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (kOf s.mem L nonce)))
            else List.replicate (2 * L.ql) 0) ∧
        t.gpr .r3 = BitVec.ofNat 64 (if SignOk (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key)
            (yOf s₀.mem L key) (xOf s.mem L key) (kOf s.mem L nonce)
            (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d (Spec.Dsa.bitLength (qOf s₀.mem L key) / 8))))
          then 1 else 0) ∧
        (∃ m, Kept L s.mem m ∧ Outside out 0 (2 * L.ql) m t.mem) ∧ t.gpr .r21 = L.S ∧ ScrL t L) ∧
        Keep bodyRegs s t := by
  obtain hqlt := qOf_lt hkp (hk.take (by omega_arith))
  have scr := hc.scr
  unfold Sign.body
  refine sprefix_ok hL hK hc hkp hk hn hd hdg hw fun s₇ Q₇ K₇ hout₇ m₇ r9₇ s6₇ k₁₇ => ?_
  unfold KeyOk at hK
  generalize pOf s₀.mem L key = p at hK hgx m₇ r9₇ s6₇ ⊢
  generalize qOf s₀.mem L key = q at hK hqlt m₇ r9₇ s6₇ ⊢
  generalize gOf s₀.mem L key = g at hK hgx m₇ r9₇ s6₇ ⊢
  generalize yOf s₀.mem L key = y at hK hgx m₇ ⊢
  generalize xOf s.mem L key = X at hgx m₇ s6₇ ⊢
  generalize kOf s.mem L nonce = K at m₇ r9₇ s6₇ ⊢
  generalize Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d (Spec.Dsa.bitLength q / 8))) = Z at s6₇ ⊢
  obtain B := VG.Proof.Dsa.supported_bounds hK.1.1
  -- The output.
  obtain hrq : sigR p q g K < q := Nat.mod_lt _ (by omega_arith)
  obtain hsq : sigS q X K Z (sigR p q g K) < q := Nat.mod_lt _ (by omega_arith)
  refine WP.mono (output_ok hL Q₇ hout₇ m₇
      (ho.congr k₁₇.wr) (hos.keep k₁₇.rd k₁₇.wr) (by rw [r9₇]; omega_arith) (by rw [s6₇]; omega_arith))
    fun t ⟨⟨o1, o2, t3, mo, qo, oo⟩, kt⟩ => ?_
  rw [r9₇, s6₇] at o1
  rw [s6₇] at o2 t3
  obtain hcb : (decide ((0 < K ∧ K < q) ∧ (0 < X ∧ X < q) ∧ sigR p q g K ≠ 0) &&
      decide (sigS q X K Z (sigR p q g K) ≠ 0)) = decide (SignOk p q g y X K Z) := by
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    unfold SignOk sigR
    constructor
    · rintro ⟨⟨h2, h3, h4⟩, h5⟩; exact ⟨h3, h2, hgx, h4, h5⟩
    · rintro ⟨h1, h2, -, h4, h5⟩; exact ⟨⟨h2, h1, h4⟩, h5⟩
  rw [hcb] at o1 o2 t3
  obtain h256 : ∀ v, v < q → v < 256 ^ L.ql := fun v hv => by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; omega_arith
  refine ⟨⟨?_, ?_, ⟨mo, K₇.trans (Kept.ofBody hL (qo.qbody.body hL)), oo⟩,
    (kt.gpr .r21 (by decide)).trans Q₇.inq.h21, scr.congr (k₁₇.trans kt).wr⟩,
    keep_but21 (k₁₇.trans kt) (by decide) (by decide)⟩
  · by_cases hc : SignOk p q g y X K Z
    · simp only [hc, decide_true, ite_true] at o1 o2 ⊢
      exact out_bytes (h256 _ hrq) (h256 _ hsq) o1 o2
    · simp only [hc, decide_false, Bool.false_eq_true, ite_false] at o1 o2 ⊢
      rw [out_bytes (Nat.pow_pos (by decide : 0 < 256)) (Nat.pow_pos (by decide : 0 < 256)) o1 o2, encodeBE_zero,
        List.replicate_append_replicate, Nat.two_mul]
  · rw [t3]
    simp only [decide_eq_true_eq]

end VG.Proof.Dsa.PPC64LE
