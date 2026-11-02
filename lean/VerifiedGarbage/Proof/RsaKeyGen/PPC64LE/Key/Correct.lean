module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLaw
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Result
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBytes
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvCorrect
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem

/-!
# `vg_rsa_keygen_key` on PPC64LE: correctness

`post_of`: what the body establishes is `keyP`'s postcondition, by
`key_result`. `key_correct`: with the entry and the restore of the saved
registers (as `vg_rsa_crt_values`'s, `Proof/Rsa/PPC64LE/CvCorrect.lean`),
`code` meets `keyP`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG.Proof.Rsa.PPC64LE (InvLaw)
open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.RsaKeyGen.PPC64LE.Key (code nArr aN aD aP aQ aDP aDQ aQi)
open VG.Impl.Rsa.PPC64LE.CrtValues (restore)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)
open VG.Proof.Rsa.PPC64LE.CrtValues (savedReg bytes_zero)

/-- An output's bytes, under the mask. -/
theorem Outs.bytes {s0 : State} {m t : Mem} {os : List (Addr × Nat × Nat)} (h : Outs s0 m true t os)
    {O : Addr} {L j : Nat} (ho : (O, L, j) ∈ os) (hL : L ≤ 4 * kW s0) (h64 : L < 2 ^ 64) :
    Spec.Rsa.bytesAt t O L = Spec.Rsa.i2osp (num m (kB s0) (kW s0) j % 256 ^ L) L :=
  bytes_of_store hL fun c hc => by rw [h _ ho c hc (by omega_arith)]; rfl

/-- An output's bytes, zero without the mask. -/
theorem Outs.zero {s0 : State} {m t : Mem} {os : List (Addr × Nat × Nat)} (h : Outs s0 m false t os)
    {O : Addr} {L j : Nat} (ho : (O, L, j) ∈ os) (h64 : L < 2 ^ 64) :
    Spec.Rsa.bytesAt t O L = List.replicate L 0 :=
  bytes_zero fun c hc => by rw [h _ ho c hc (by omega_arith)]; rfl

theorem status_toNat (a b : Nat) (ha : a ≤ 1) (hb : b ≤ 1) :
    ((BitVec.ofNat 64 (2 * a + b)).setWidth 32).toNat = 2 * a + b := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_arith

theorem post_of {s0 t : State} (h : keyP.pre s0) (bp : BodyPost s0 t) : keyP.post s0 t := by
  obtain ⟨m, D, x, -, hD, xl, xd, inv, r3, outs, vN, vD, vP, vQ, vDP, vDQ, vQi⟩ := bp
  have p := kpre h
  obtain ⟨-, -, -, hlw, -⟩ := pre_ws h
  have l1 := p.l1
  have l2 := p.l2
  have kr := key_result h xl xd inv
  have hres : resOf s0 = match Spec.RsaKeyGen.keyFromPrimes (16 * kL s0) (eIn s0) (pIn s0) (qIn s0) with
      | .inl (.ok k) => .inl (.ok [Spec.Rsa.i2osp k.n (2 * kL s0), Spec.Rsa.i2osp k.d (2 * kL s0),
          Spec.Rsa.i2osp k.p (kL s0), Spec.Rsa.i2osp k.q (kL s0), Spec.Rsa.i2osp k.dP (kL s0),
          Spec.Rsa.i2osp k.dQ (kL s0), Spec.Rsa.i2osp k.qInv (kL s0)])
      | .inl (.error f) => .inl (.error f)
      | .inr () => .inr () := rfl
  have i1 : ∀ (c : Prop) [Decidable c], (if c then 1 else 0 : Nat) ≤ 1 := fun c _ => flag01 c
  show ((t.gpr .r3).setWidth 32).toNat = Spec.RsaKeyGen.keyStatus (resOf s0) ∧ _
  rw [r3, status_toNat _ _ (i1 _) (i1 _), hres, kr]
  have nl := p.nl
  by_cases hm : kMask s0 D
  · have hs : ¬ kSmall s0 D := hm.1
    obtain ⟨-, top, -, g, pp, qq, -, -, -⟩ := id hm
    have hP : kP s0 < 2 ^ (8 * kL s0) := by
      have := hpl_of s0; have := hql_of s0; simp only [kP]; split <;> with_reducible assumption
    have hQ : kQ s0 < 2 ^ (8 * kL s0) := by
      have := hpl_of s0; have := hql_of s0; simp only [kQ]; split <;> with_reducible assumption
    simp only [hm, hs, ↓reduceIte]
    refine ⟨rfl, ?_⟩
    simp only [hm, decide_true] at outs
    -- `p` and `q` are at least 3: an odd 1 makes `n` too small.
    have p3 : 3 ≤ kP s0 := by
      by_contra c
      have : kP s0 = 1 := by omega_arith
      rw [this, Nat.one_mul] at top
      exact top (Nat.lt_of_lt_of_le hQ (Nat.pow_le_pow_right (n := 2) (by decide) (show 8 * kL s0 ≤ 16 * kL s0 - 1 by omega_arith)))
    have q3 : 3 ≤ kQ s0 := by
      by_contra c
      have : kQ s0 = 1 := by omega_arith
      rw [this, Nat.mul_one] at top
      exact top (Nat.lt_of_lt_of_le hP (Nat.pow_le_pow_right (n := 2) (by decide) (show 8 * kL s0 ≤ 16 * kL s0 - 1 by omega_arith)))
    have hM : mL (kP s0) = kP s0 := mL_of ⟨by omega_arith, pp⟩
    rw [hM] at xl
    have h16 : 2 ^ (16 * kL s0) = 2 ^ (8 * kL s0) * 2 ^ (8 * kL s0) := by rw [← Nat.pow_add]; congr 1; omega_arith
    have b8 : (256 : Nat) ^ kL s0 = 2 ^ (8 * kL s0) := by rw [Nat.pow_mul]
    have b16 : (256 : Nat) ^ (2 * kL s0) = 2 ^ (16 * kL s0) := by
      rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; congr 1; omega_arith
    have hW : 32 * kW s0 = 16 * kL s0 := by omega_arith
    simp only [outBytes, nl]
    have bN := outs.bytes (O := s0.gpr .r3) (L := 2 * kL s0) (j := aN) (by simp) (by omega_arith) (by omega_arith)
    have bD := outs.bytes (O := s0.gpr .r5) (L := 2 * kL s0) (j := aD) (by simp) (by omega_arith) (by omega_arith)
    have bP := outs.bytes (O := s0.gpr .r7) (L := kL s0) (j := aP) (by simp) (by omega_arith) (by omega_arith)
    have bQ := outs.bytes (O := s0.gpr .r9) (L := kL s0) (j := aQ) (by simp) (by omega_arith) (by omega_arith)
    have bDP := outs.bytes (O := PPC64LE.stackArg s0 0) (L := kL s0) (j := aDP) (by simp) (by omega_arith) (by omega_arith)
    have bDQ := outs.bytes (O := PPC64LE.stackArg s0 2) (L := kL s0) (j := aDQ) (by simp) (by omega_arith) (by omega_arith)
    have bQi := outs.bytes (O := PPC64LE.stackArg s0 4) (L := kL s0) (j := aQi) (by simp) (by omega_arith) (by omega_arith)
    rw [bN, bD, bP, bQ, bDP, bDQ, bQi, vN, vD, vP, vQ, vDP, vDQ, vQi, b8, b16]
    simp only [show ¬ kP s0 - 1 = 0 by omega_arith, show ¬ kQ s0 - 1 = 0 by omega_arith, ↓reduceIte]
    rw [hW] at hD
    have e1 : kP s0 * kQ s0 % 2 ^ (16 * kL s0) = kP s0 * kQ s0 :=
      Nat.mod_eq_of_lt (by rw [h16]; exact Nat.mul_lt_mul'' hP hQ)
    have e5 : D % (kP s0 - 1) % 2 ^ (8 * kL s0) = D % (kP s0 - 1) :=
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega_arith)) (by omega_arith))
    have e6 : D % (kQ s0 - 1) % 2 ^ (8 * kL s0) = D % (kQ s0 - 1) :=
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega_arith)) (by omega_arith))
    rw [e1, e5, e6, Nat.mod_eq_of_lt hD, Nat.mod_eq_of_lt hP, Nat.mod_eq_of_lt hQ,
      Nat.mod_eq_of_lt (show x < 2 ^ (8 * kL s0) by omega_arith)]
  · simp only [hm, decide_false] at outs
    have z : outZero s0 t.mem := by
      simp only [outZero, nl]
      exact ⟨outs.zero (j := aN) (by simp) (by omega_arith), outs.zero (j := aD) (by simp) (by omega_arith),
        outs.zero (j := aP) (by simp) (by omega_arith), outs.zero (j := aQ) (by simp) (by omega_arith),
        outs.zero (j := aDP) (by simp) (by omega_arith), outs.zero (j := aDQ) (by simp) (by omega_arith),
        outs.zero (j := aQi) (by simp) (by omega_arith)⟩
    by_cases hs : kSmall s0 D
    · simp only [hm, hs, ↓reduceIte]
      exact ⟨rfl, z⟩
    · simp only [hm, hs, ↓reduceIte]
      exact ⟨rfl, z⟩

/-- `restore`: the saved registers from the header. -/
theorem restore_ok {s0 t : State} {m : Mem} (h : Fr s0 m t) :
    WP isa (.block restore) t fun u => (u.gpr .r14 = s0.gpr .r14 ∧ u.gpr .r15 = s0.gpr .r15 ∧
      u.gpr .r16 = s0.gpr .r16 ∧ u.gpr .r17 = s0.gpr .r17 ∧ u.gpr .r18 = s0.gpr .r18 ∧
      u.gpr .r19 = s0.gpr .r19 ∧ u.gpr .r20 = s0.gpr .r20 ∧ u.gpr .r21 = s0.gpr .r21 ∧
      u.gpr .r22 = s0.gpr .r22 ∧ u.gpr .r23 = s0.gpr .r23 ∧ u.gpr .r24 = s0.gpr .r24 ∧
      u.gpr .r29 = s0.gpr .r29 ∧ u.gpr .r30 = s0.gpr .r30 ∧ u.gpr .r31 = s0.gpr .r31 ∧ u.mem = t.mem) ∧
      Keep [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r29, .r30, .r31] t u := by
  have p := kpre h.pre
  have nw := p.wS
  have hzs := p.sl
  have hm : (⟨kB s0, kZ s0⟩ : Region) ∈ t.wr := by rw [h.wr, p.wr]; simp
  have hs : Scr t (kB s0) (kZ s0) := Scr.of_mem hm nw
  have e : ∀ i < 14, t.mem.readW (off (kB s0) (8 * i)) 64 = s0.gpr (savedReg i) := fun i hi => by
    rw [h.readW (by omega_arith)]; exact h.hdr i hi
  have e0 := e 0 (by decide); have e1 := e 1 (by decide); have e2 := e 2 (by decide)
  have e3 := e 3 (by decide); have e4 := e 4 (by decide); have e5 := e 5 (by decide)
  have e6 := e 6 (by decide); have e7 := e 7 (by decide); have e8 := e 8 (by decide)
  have e9 := e 9 (by decide); have e10 := e 10 (by decide); have e11 := e 11 (by decide)
  have e12 := e 12 (by decide); have e13 := e 13 (by decide)
  simp only [savedReg, Nat.reduceMul] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
  refine WP.keep _ ?_ (by decide)
  prun [restore, h.r31, hs.ld (d := 0) (n := 8) (by omega_arith), hs.ld (d := 8) (n := 8) (by omega_arith),
    hs.ld (d := 16) (n := 8) (by omega_arith), hs.ld (d := 24) (n := 8) (by omega_arith),
    hs.ld (d := 32) (n := 8) (by omega_arith), hs.ld (d := 40) (n := 8) (by omega_arith),
    hs.ld (d := 48) (n := 8) (by omega_arith), hs.ld (d := 56) (n := 8) (by omega_arith),
    hs.ld (d := 64) (n := 8) (by omega_arith), hs.ld (d := 72) (n := 8) (by omega_arith),
    hs.ld (d := 80) (n := 8) (by omega_arith), hs.ld (d := 88) (n := 8) (by omega_arith),
    hs.ld (d := 96) (n := 8) (by omega_arith), hs.ld (d := 104) (n := 8) (by omega_arith),
    e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13]
  exact e0

theorem key_correct [InvLaw] (s : State) (h : keyP.pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ keyP.post s t := by
  show WP isa code s fun t => abiPreserved s t ∧ keyP.post s t
  unfold code
  refine WP.seq (WP.mono (entry_ok h) fun s1 ⟨b1, a1, k1⟩ => ?_)
  refine WP.seq (WP.mono (body_ok b1 a1) fun t ⟨bp, kt⟩ => ?_)
  obtain ⟨m, D, x, ft, rest⟩ := id bp
  refine WP.mono (restore_ok ft) fun u ⟨⟨u14, u15, u16, u17, u18, u19, u20, u21, u22, u23, u24, u29, u30, u31,
      um⟩, ku⟩ => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · have K := (k1.trans kt).trans ku
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
      first | exact K.gpr _ (by decide) | with_reducible assumption
  · rw [ku.sp, kt.sp, k1.sp]
  · rw [ku.lr, kt.lr, k1.lr]
  · have e3 : u.gpr .r3 = t.gpr .r3 := ku.gpr _ (by decide)
    have po := post_of h bp
    show _ ∧ _
    rw [um, e3]
    exact po

end VG.Proof.RsaKeyGen.PPC64LE.Key
