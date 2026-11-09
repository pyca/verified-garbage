module

public import VerifiedGarbage.Proof.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.Body
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.KeyOp
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_keygen_key` on RISC-V: correctness, and verified given the constant time

`key_result`: `keyFromPrimes` of the inputs is the key of the body's numbers
under `kMask`, `.inr ()` (the status 2) under `kSmall`, and an error
otherwise (`Proof/RsaKeyGen/KeyOp.lean`'s `keyFromPrimes_code`). `post_of`:
what the body establishes is `fnPost`. `code_correct`: with the entry and
the restore of the saved registers, `code` meets `fnPost`. `key_verified_of`:
`Verified`, given the constant time, as PPC64LE's
(`Proof/RsaKeyGen/PPC64LE/Key/{Result,Correct,Verified}.lean`).
-/

-- separate module: the correctness proof is not re-checked with every change to the constant-time proof

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Key

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (restore)
open VG.Impl.RsaKeyGen.RISCV64.Key (code entry body aN aD aP aQ aDP aDQ aQi)

theorem mL_eq (P : Nat) : mL P = VG.Proof.RsaKeyGen.qModP P := by
  unfold mL good VG.Proof.RsaKeyGen.qModP
  by_cases a : P < 3 <;> by_cases b : P % 2 = 1 <;> simp [a, b]

theorem key_result {s0 : State} (h : PreC s0) {D x : Nat} (hxl : x < mL (kP s0))
    (hx : ((mL (kP s0) : Nat) : Int) ∣ (x : Int) * kQ s0 - Nat.gcd (kQ s0) (mL (kP s0)))
    (hinv : okv (eIn s0) (kLc s0) → Spec.Rsa.inverse (eIn s0) (kLc s0) = some D) :
    Spec.RsaKeyGen.keyFromPrimes (16 * pLen s0) (eIn s0) (pIn s0) (qIn s0) =
      if kMask s0 D then .inl (.ok ⟨kP s0 * kQ s0, eIn s0, D, kP s0, kQ s0, D % (kP s0 - 1), D % (kQ s0 - 1), x⟩)
      else if kSmall s0 D then .inr () else .inl (.error .internal) := by
  have hpl := pIn_lt s0
  have hql := qIn_lt s0
  have hel := eIn_lt h
  rw [mL_eq] at hxl hx
  rw [VG.Proof.RsaKeyGen.keyFromPrimes_code h.p32 h.p512 hpl hql hel hx hxl]
  by_cases ok : okv (eIn s0) (kLc s0)
  · have hi := hinv ok
    simp only [kLc, kP, kQ] at hi
    rw [hi]
    dsimp only
    by_cases hs : D ≤ 2 ^ (8 * pLen s0)
    · have sm : kSmall s0 D := ⟨ok, by omega⟩
      have nm : ¬ kMask s0 D := fun m => m.1 sm
      simp only [hs, nm, sm, ↓reduceIte]
    · have sm : ¬ kSmall s0 D := fun a => hs (by have := a.2; omega)
      simp only [hs, sm, ↓reduceIte]
      by_cases hm : kMask s0 D
      · simp only [hm, ↓reduceIte]
        refine ite_eq_left ?_
        obtain ⟨-, top, -, g, pp, qq, ee, e3, e33⟩ := hm
        rw [← mL_eq]
        simp only [kP, kQ] at top g pp qq
        simp [Spec.Rsa.exponentValid, g, pp, qq, ee, e33]
        simp only [pLen] at top
        exact ⟨Nat.le_of_not_lt top, by omega⟩
      · simp only [hm, ↓reduceIte]
        refine ite_eq_right fun c => ?_
        apply hm
        simp only [Bool.and_eq_true, decide_eq_true_eq, Spec.Rsa.exponentValid, beq_iff_eq] at c
        obtain ⟨⟨⟨⟨top, g⟩, pp⟩, qq⟩, ⟨ee, e3⟩, e33⟩ := c
        rw [← mL_eq] at g
        exact ⟨sm, by simp only [kP, kQ, pLen]; omega, ok, g, pp, qq, ee, by omega, e33⟩
  · have hi := okv_none ok
    simp only [kLc, kP, kQ] at hi
    rw [hi]
    have sm : ¬ kSmall s0 D := fun a => ok a.1
    have nm : ¬ kMask s0 D := fun m => ok m.2.2.1
    simp only [nm, sm, ↓reduceIte]

/-- An output's bytes, under the mask. -/
theorem Outs.bytes {s0 : State} {m t : Mem} {os : List (Addr × Nat × Nat)} (h : Outs s0 m true t os)
    {O : Addr} {L j : Nat} (ho : (O, L, j) ∈ os) (hL : L ≤ 8 * wOf s0) :
    Spec.Rsa.bytesAt t O L = Spec.Rsa.i2osp (num m (bOf s0) (wOf s0) j % 256 ^ L) L :=
  bytes_of_store hL fun c hc => by rw [h _ ho c hc]; rfl

/-- An output's bytes, zero without the mask. -/
theorem Outs.zero {s0 : State} {m t : Mem} {os : List (Addr × Nat × Nat)} (h : Outs s0 m false t os)
    {O : Addr} {L j : Nat} (ho : (O, L, j) ∈ os) : Spec.Rsa.bytesAt t O L = List.replicate L 0 := by
  simp only [Spec.Rsa.bytesAt]
  apply List.ext_getElem (by simp)
  intro i h1 _
  simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
  rw [h _ ho i (by simpa using h1)]
  rfl

theorem status_toNat (a b : Nat) (ha : a ≤ 1) (hb : b ≤ 1) :
    ((BitVec.ofNat 64 (2 * a + b)).setWidth 32).toNat = 2 * a + b := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem post_of {s0 t : State} (h : PreC s0) (bp : BodyPost s0 t) : fnPost s0 t := by
  obtain ⟨m, D, x, -, hD, xl, xd, inv, r3, outs, vN, vD, vP, vQ, vDP, vDQ, vQi⟩ := bp
  have w4 := h.wOf_eq
  have l1 := h.p32
  have nl := h.hn
  have kr := key_result h xl xd inv
  have hres : resOf s0 = match Spec.RsaKeyGen.keyFromPrimes (16 * pLen s0) (eIn s0) (pIn s0) (qIn s0) with
      | .inl (.ok k) => .inl (.ok [Spec.Rsa.i2osp k.n (2 * pLen s0), Spec.Rsa.i2osp k.d (2 * pLen s0),
          Spec.Rsa.i2osp k.p (pLen s0), Spec.Rsa.i2osp k.q (pLen s0), Spec.Rsa.i2osp k.dP (pLen s0),
          Spec.Rsa.i2osp k.dQ (pLen s0), Spec.Rsa.i2osp k.qInv (pLen s0)])
      | .inl (.error f) => .inl (.error f)
      | .inr () => .inr () := rfl
  show ((t.gpr .a0).setWidth 32).toNat = Proof.RsaKeyGen.keyStatus (resOf s0) ∧ _
  rw [r3, status_toNat _ _ (flag01 _) (flag01 _), hres, kr]
  have hP := kP_lt s0
  have hQ := kQ_lt s0
  have lN : 2 * pLen s0 ≤ 8 * wOf s0 := by omega
  have lP : pLen s0 ≤ 8 * wOf s0 := by omega
  by_cases hm : kMask s0 D
  · have hs : ¬ kSmall s0 D := hm.1
    obtain ⟨-, top, -, g, pp, qq, -, -, -⟩ := id hm
    simp only [hm, hs, ↓reduceIte]
    refine ⟨rfl, ?_⟩
    simp only [hm, decide_true] at outs
    -- `p` and `q` are at least 3: an odd 1 makes `n` too small.
    have p3 : 3 ≤ kP s0 := by
      by_contra c
      have : kP s0 = 1 := by omega
      rw [this, Nat.one_mul] at top
      exact top (Nat.lt_of_lt_of_le hQ (Nat.pow_le_pow_right (n := 2) (by decide)
        (show 8 * pLen s0 ≤ 16 * pLen s0 - 1 by omega)))
    have q3 : 3 ≤ kQ s0 := by
      by_contra c
      have : kQ s0 = 1 := by omega
      rw [this, Nat.mul_one] at top
      exact top (Nat.lt_of_lt_of_le hP (Nat.pow_le_pow_right (n := 2) (by decide)
        (show 8 * pLen s0 ≤ 16 * pLen s0 - 1 by omega)))
    have hM : mL (kP s0) = kP s0 := mL_of ⟨by omega, pp⟩
    rw [hM] at xl
    have h16 : 2 ^ (16 * pLen s0) = 2 ^ (8 * pLen s0) * 2 ^ (8 * pLen s0) := by
      rw [← Nat.pow_add]; congr 1; omega
    have b8 : (256 : Nat) ^ pLen s0 = 2 ^ (8 * pLen s0) := by rw [Nat.pow_mul]
    have b16 : (256 : Nat) ^ (2 * pLen s0) = 2 ^ (16 * pLen s0) := by
      rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; congr 1; omega
    have hW : 64 * wOf s0 = 16 * pLen s0 := by omega
    have hp' : (s0.gpr .a5).toNat = pLen s0 := rfl
    simp only [outBytes, nl, hp']
    have bN := outs.bytes (O := s0.gpr .a0) (L := 2 * pLen s0) (j := aN) (by simp) lN
    have bD := outs.bytes (O := s0.gpr .a2) (L := 2 * pLen s0) (j := aD) (by simp) lN
    have bP := outs.bytes (O := s0.gpr .a4) (L := pLen s0) (j := aP) (by simp) lP
    have bQ := outs.bytes (O := s0.gpr .a6) (L := pLen s0) (j := aQ) (by simp) lP
    have bDP := outs.bytes (O := stackArg s0 0) (L := pLen s0) (j := aDP) (by simp) lP
    have bDQ := outs.bytes (O := stackArg s0 2) (L := pLen s0) (j := aDQ) (by simp) lP
    have bQi := outs.bytes (O := stackArg s0 4) (L := pLen s0) (j := aQi) (by simp) lP
    rw [bN, bD, bP, bQ, bDP, bDQ, bQi]
    rw [vN, vD, vP, vQ, vDP, vDQ, vQi]
    simp only [b8, b16]
    simp only [show ¬ kP s0 - 1 = 0 by omega, show ¬ kQ s0 - 1 = 0 by omega, ↓reduceIte]
    rw [hW] at hD
    have e1 : kP s0 * kQ s0 % 2 ^ (16 * pLen s0) = kP s0 * kQ s0 :=
      Nat.mod_eq_of_lt (by rw [h16]; exact Nat.mul_lt_mul'' hP hQ)
    have e5 : D % (kP s0 - 1) % 2 ^ (8 * pLen s0) = D % (kP s0 - 1) :=
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega))
    have e6 : D % (kQ s0 - 1) % 2 ^ (8 * pLen s0) = D % (kQ s0 - 1) :=
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega))
    rw [e1, e5, e6, Nat.mod_eq_of_lt hD, Nat.mod_eq_of_lt hP, Nat.mod_eq_of_lt hQ,
      Nat.mod_eq_of_lt (show x < 2 ^ (8 * pLen s0) by omega)]
  · simp only [hm, decide_false] at outs
    have z : outZero s0 t.mem := by
      simp only [outZero, nl]
      exact ⟨outs.zero (j := aN) (by simp), outs.zero (j := aD) (by simp), outs.zero (j := aP) (by simp),
        outs.zero (j := aQ) (by simp), outs.zero (j := aDP) (by simp), outs.zero (j := aDQ) (by simp),
        outs.zero (j := aQi) (by simp)⟩
    by_cases hs : kSmall s0 D
    · simp only [hm, hs, ↓reduceIte]
      exact ⟨rfl, z⟩
    · simp only [hm, hs, ↓reduceIte]
      exact ⟨rfl, z⟩

theorem code_correct [VG.Proof.Rsa.RISCV64.InvLaw] (s : State) (hpre : (Proof.RsaKeyGen.keyContract RISCV64.abi).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ fnPost s t := by
  show WP isa code s fun t => abiPreserved s t ∧ fnPost s t
  have h := preC_of hpre
  refine WP.mono (WP.rdwr (Q := fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.gpr .ra = s.gpr .ra ∧
    fnPost s t) ?_) fun t ⟨⟨hp, hra, hpost⟩, _, _, hsp⟩ => ⟨⟨hp, hsp, hra⟩, hpost⟩
  rw [show code = .seq (.block entry) (.seq body (.block restore)) from rfl, WP.seq_iff]
  refine WP.mono (entry_ok h) fun e ⟨c, a7⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (body_ok h c a7) fun t bp => ?_
  obtain ⟨-, -, -, ce, -⟩ := id bp
  refine WP.mono (restore_ok h ce) fun v ⟨vp, vra, vm, va⟩ => ⟨vp, vra, ?_⟩
  have po := post_of h bp
  unfold fnPost at po ⊢
  rw [vm, va]
  exact po

/-- `vg_rsa_keygen_key`, given its constant time. -/
theorem key_verified_of [VG.Proof.Rsa.RISCV64.InvLaw] (hct : ConstantTime isa (Proof.RsaKeyGen.keyContract RISCV64.abi).pre
    (Proof.RsaKeyGen.keyContract RISCV64.abi).pub code) :
    Verified RISCV64.target code (Proof.RsaKeyGen.keyContract RISCV64.abi) :=
  Verified.of_correct (k := fnContract) code_correct hct key_implies

end VG.Proof.RsaKeyGen.RISCV64.Key
