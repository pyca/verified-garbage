module

import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.KSStore
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Ctx
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Load
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Elem.Check
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Table
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
public import VerifiedGarbage.Proof.Bignum.PPC64LE.ModExpPow
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Generation
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.St
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Pieces
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Bytes
import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.KSLoad
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Test
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! ### `Dsa.PPC64LE.Gen.Power`, which only this module used -/

section

/-! # DSA parameter generation on PPC64LE: the power in the P space

`power pLen qLen` (`Impl/Dsa/PPC64LE/Generation.lean`) works in the P space,
`pZ pLen` bytes at `pB` of `scratch`, as a Miller–Rabin working space
(`Env`, with `w = p_len / 8`): `powA_ok`, p from `sPBE` into array 0 and
`R² mod p` into array 1; `powC_ok`, h from `fH` into array 4, its power by
the exponent at `sE` into array 4, and `r0 = 0` exactly when it is above 1
and below p.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation
open VG.Proof.Bignum (slot)

/-- What a block keeps, with the stack pointer and the link register. -/
abbrev BKeep := VG.Proof.Bignum.PPC64LE.Keep

/-- The P space's bytes. -/
abbrev pZ (pLen : Nat) : Nat := kB pLen - pB

/-- The P space's digits. -/
abbrev pw (pLen : Nat) : Nat := pLen / 8

/-- The code before the power: p into array 0, and `R² mod p` into array 1. -/
abbrev powA (pLen : Nat) : Prog isa :=
  .seq (.seq (.seq (.block (enterP pLen ++ [scr .r12 sPBE, .li .r6 pLen])) (VG.Impl.Dsa.PPC64LE.loadArr 0))
    (.block (PublicChecked.base .r5 1 ++ PublicChecked.base .r8 2 ++ PublicChecked.base .r9 3))) Precompute.r2

theorem pZ_eq {pLen : Nat} (h : pLen = 128 ∨ pLen = 256 ∨ pLen = 384) : slot (pw pLen) 28 = pZ pLen := by
  rcases h with rfl | rfl | rfl <;> decide

/-- The registers `powA` writes. -/
def powARegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r20, .r21, .r23, .r29, .r31]

/-- `powA`: into the P space at `B = S + pB`, p from the `pLen` bytes at
`S + sPBE` into array 0 (word `w` zero), and `R² mod p` into array 1. -/
theorem powA_ok {s : State} {S : Addr} {pLen : Nat} (hl : pLen = 128 ∨ pLen = 256 ∨ pLen = 384)
    (h28 : s.gpr .r28 = S) (hs : Scr s (off S pB) (pZ pLen))
    (hrd : ∀ i < pLen, InRegions (s.rd ++ s.wr) (off (off S sPBE) i) 1)
    (hsep : ∀ i < pLen, ∀ x, ofs (off S pB) x < pZ pLen → off (off S sPBE) i ≠ x)
    (hp : 2 ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off S sPBE) pLen)) :
    WP isa (powA pLen) s fun t =>
      (Env t (off S pB) (pZ pLen) (pw pLen) ∧ t.gpr .r21 = off S pB ∧ t.gpr .r23 = off S pB ∧
        arr t.mem (off S pB) (pw pLen) 0 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off S sPBE) pLen) ∧
        word t.mem (off S pB) (slot (pw pLen) 0 + 8 * pw pLen) = 0 ∧
        arr t.mem (off S pB) (pw pLen) 1 =
          2 ^ (128 * pw pLen) % Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off S sPBE) pLen) ∧
        Outside (off S pB) (slot (pw pLen) 0) (4 * (8 * (pw pLen + 2))) s.mem t.mem) ∧
      BKeep powARegs s t := by
  have hZ := pZ_eq hl
  have hnw := hs.nowrap
  have pb15 : pB + 256 < 2 ^ 15 := by decide
  have pl15 : pLen < 2 ^ 15 := by omega_using [hl]
  have w15 : pLen / 4 < 2 ^ 15 := by omega_using [hl]
  have p15 : pLen + 16 < 2 ^ 15 := by omega_using [hl]
  have wd : 2 * pw pLen = pLen / 4 := by rcases hl with rfl | rfl | rfl <;> decide
  have wd2 : 8 * (pw pLen + 2) = pLen + 16 := by rcases hl with rfl | rfl | rfl <;> decide
  have e : ∀ j, slot (pw pLen) j = hdrBytes + j * (8 * (pw pLen + 2)) := fun _ => rfl
  have hh : hdrBytes = 256 := rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4
  -- Into the P space.
  have hb : WP isa (.block (enterP pLen ++ [scr .r12 sPBE, .li .r6 pLen])) s fun u =>
      (u.gpr .r21 = off S pB ∧ u.gpr .r23 = off S pB ∧ u.gpr .r31 = off S pB ∧
        u.gpr .r10 = off (off S pB) (slot (pw pLen) 0) ∧ u.gpr .r11 = BitVec.ofNat 64 (2 * pw pLen) ∧
        u.gpr .r29 = BitVec.ofNat 64 (8 * (pw pLen + 2)) ∧ u.gpr .r12 = off S sPBE ∧
        u.gpr .r6 = BitVec.ofNat 64 pLen ∧ u.mem = s.mem) ∧
        BKeep [.r21, .r23, .r31, .r10, .r11, .r29, .r12, .r6] s u := by
    refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ (by rfl)
    simp only [enterP, scr, List.cons_append, List.nil_append]
    prun [h28, exec_addi (show Reg.r28 ≠ .r0 by decide) (show pB < 2 ^ 15 by decide),
      exec_addi (show Reg.r21 ≠ .r0 by decide) (show hdrBytes < 2 ^ 15 by decide),
      exec_addi (show Reg.r28 ≠ .r0 by decide) (show sPBE < 2 ^ 15 by decide), exec_li w15, exec_li p15,
      exec_li pl15, wd, wd2, BitVec.add_zero]
    rw [e0, Nat.zero_mul, Nat.add_zero]
  unfold powA
  refine WP.seq (WP.seq (WP.seq (WP.mono hb fun s₁ ⟨⟨a21, a23, a31, a10, a11, a29, a12, a6, m1⟩, k1⟩ => ?_)))
  have en1 : Env s₁ (off S pB) (pZ pLen) (pw pLen) :=
    ⟨hs.congr k1.wr, a10, a29, a11, a31, by omega_using [hl, wd], by omega_using [hl, wd], by rw [hZ]⟩
  refine WP.mono (VG.Proof.Dsa.PPC64LE.loadArr_ok en1 (j := 0) (by decide) a12 a6 (by omega_using [hl]) (by omega_using [hl, wd])
    (fun i hi => by rw [k1.rd, k1.wr]; exact hrd i hi) (fun i hi x hx => hsep i hi x hx))
    fun s₂ ⟨⟨v0, top0, o2, b10⟩, k2⟩ => ?_
  rw [m1] at v0 o2
  have en2 := VG.Proof.Dsa.PPC64LE.env_keep10 en1 k2 (by decide) b10
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (en2.base (rd := .r5) (by decide) (by decide) 1) fun s₃ ⟨⟨a5, m3⟩, k3⟩ => ?_
  have en3 := en2.keep k3 (by decide)
  refine WP.mono (en3.base (rd := .r8) (by decide) (by decide) 2) fun s₄ ⟨⟨a8, m4⟩, k4⟩ => ?_
  have en4 := en3.keep k4 (by decide)
  refine WP.mono (en4.base (rd := .r9) (by decide) (by decide) 3) fun s₅ ⟨⟨a9, m5⟩, k5⟩ => ?_
  have en5 := en4.keep k5 (by decide)
  have hm5 : s₅.mem = s₂.mem := by rw [m5, m4, m3]
  have v0' : val32 s₅.mem (off S pB) (slot (pw pLen) 0) (2 * pw pLen) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off S sPBE) pLen) := by rw [hm5]; exact v0
  refine WP.mono (r2_ok en5.hs ((k5.gpr .r8 (by decide)).trans a8) a9 en5.h10
    ((k5.gpr .r5 (by decide)).trans ((k4.gpr .r5 (by decide)).trans a5)) en5.h11 (by omega_using [hl, wd]) (by omega_using [hl, wd])
    (by rw [e, hZ.symm.trans (e 28)]; omega_using []) (by rw [v0']; exact hp)) fun t ⟨hr2, o7, k7⟩ => ?_
  rw [v0'] at hr2
  have k1t := (((k1.trans k2).trans k3).trans ((k4.trans k5).trans k7))
  have k2t := (k2.trans k3).trans ((k4.trans k5).trans k7)
  refine ⟨⟨en5.keep k7 (by decide), (k2t.gpr .r21 (by decide)).trans a21, (k2t.gpr .r23 (by decide)).trans a23,
    ?_, ?_, hr2, ?_⟩, k1t.mono (by decide)⟩
  · show val32 t.mem (off S pB) (slot (pw pLen) 0) (2 * pw pLen) = _
    rw [Outside.val32 o7 (by omega_using [e0, e1]) (by omega_using [hl, wd, hh, e0]), hm5]; exact v0
  · rw [Outside.word o7 (by omega_using [e0, e1]) (by omega_using [hl, wd, hh, e0]), hm5]; exact top0
  · rw [hm5] at o7
    exact (o2.mono (by omega_using []) (by omega_using [])).trans (o7.mono (by omega_using [e0, e1]) (by omega_using [e0, e1]))

theorem outs_within' {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m') {lo hi : Nat}
    (hw : ∀ r ∈ rs, lo ≤ r.1 ∧ r.1 + r.2 ≤ hi) : Outside B lo (hi - lo) m m' :=
  fun x hx => h x fun r hr => by have := hw r hr; omega_using [hx, this]

/-- The code after h's pointer: h into array 4, its power, and the range check. -/
abbrev powC (pLen qLen : Nat) : Prog isa :=
  .seq (VG.Impl.Dsa.PPC64LE.loadArr 4) (.seq (.block (PublicChecked.minv ++ [scr .r30 sE, .li .r31 (eBytes pLen qLen)]))
    (.seq ModExp.powSecret (.seq (.block ([.addi .r31 .r23 0] ++ zeroTop4)) VG.Impl.Dsa.PPC64LE.elemRange)))

/-- The registers `powC` writes. -/
def powCRegs : List Reg :=
  VG.Proof.Dsa.PPC64LE.loadRegs ++ [.r0, .r3, .r4, .r12, .r30, .r31] ++ ModExp.powSRegs ++
    [.r31, .r10, .r14, .r0] ++ VG.Proof.Dsa.PPC64LE.elemRangeRegs

/-- `powC`: h (the `pLen` bytes at `H`, `r12`) into array 4, `h^e mod p` for
the `eB` bytes of `e` at `S + sE`, and `r0 = 0` exactly when it is above 1
and below p. -/
theorem powC_ok {s : State} {S H : Addr} {pLen qLen p : Nat} (hl : pLen = 128 ∨ pLen = 256 ∨ pLen = 384)
    (en : Env s (off S pB) (pZ pLen) (pw pLen)) (h23 : s.gpr .r23 = off S pB) (h28 : s.gpr .r28 = S)
    (h12 : s.gpr .r12 = H) (h6 : s.gpr .r6 = BitVec.ofNat 64 pLen)
    (hHrd : ∀ i < pLen, InRegions (s.rd ++ s.wr) (off H i) 1)
    (hHsep : ∀ i < pLen, ∀ x, ofs (off S pB) x < pZ pLen → off H i ≠ x)
    (heB : 1 ≤ eBytes pLen qLen) (heB' : eBytes pLen qLen < 2 ^ 15)
    (hErd : ∀ i < eBytes pLen qLen, InRegions (s.rd ++ s.wr) (off (off S sE) i) 1)
    (hEsep : ∀ i < eBytes pLen qLen, ∀ x, ofs (off S pB) x < pZ pLen → off (off S sE) i ≠ x)
    (hp0 : arr s.mem (off S pB) (pw pLen) 0 = p) (hz0 : word s.mem (off S pB) (slot (pw pLen) 0 + 8 * pw pLen) = 0)
    (hp : 2 ≤ p) (hpo : p % 2 = 1) (hrr : arr s.mem (off S pB) (pw pLen) 1 = 2 ^ (128 * pw pLen) % p) :
    WP isa (powC pLen qLen) s fun t =>
      (arr t.mem (off S pB) (pw pLen) 4 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem H pLen) ^
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off S sE) (eBytes pLen qLen)) % p ∧
        (t.gpr .r0 = 0 ↔ 1 < arr t.mem (off S pB) (pw pLen) 4 ∧ arr t.mem (off S pB) (pw pLen) 4 < p) ∧
        Env t (off S pB) (pZ pLen) (pw pLen) ∧
        Outside (off S pB) (slot (pw pLen) 1) (7 * (8 * (pw pLen + 2))) s.mem t.mem) ∧
      BKeep powCRegs s t := by
  have hZ := pZ_eq hl
  have hnw := en.hs.nowrap
  have hw4 := en.hw
  have hw' := en.hw'
  have e : ∀ j, slot (pw pLen) j = hdrBytes + j * (8 * (pw pLen + 2)) := fun _ => rfl
  have hh : hdrBytes = 256 := rfl
  have e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4; have e8 := e 8; have e28 := e 28
  have wl : 8 * pw pLen = pLen := by rcases hl with rfl | rfl | rfl <;> decide
  have sE15 : sE < 2 ^ 15 := by decide
  -- h into array 4.
  unfold powC
  refine WP.seq (WP.mono (VG.Proof.Dsa.PPC64LE.loadArr_ok en (j := 4) (by decide) h12 h6 (by omega_using [hl]) (by omega_using [wl])
    hHrd hHsep) fun s₂ ⟨⟨v4, top4, o2, a10⟩, k2⟩ => ?_)
  have en2 := VG.Proof.Dsa.PPC64LE.env_keep10 en k2 (by decide) a10
  -- `-p⁻¹`, and the exponent's pointer and length.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have p2 : val32 s₂.mem (off S pB) (slot (pw pLen) 0) (2 * pw pLen) = p := by
    rw [Outside.val32 o2 (by omega_using [e0, e4]) (by omega_using [hw', hh, e0])]; exact hp0
  have hlow : (word s₂.mem (off S pB) (slot (pw pLen) 0)).toNat % 2 = 1 := by
    have h1 := word_eq_w32 s₂.mem (off S pB) (slot (pw pLen) 0)
    have h2 : val32 s₂.mem (off S pB) (slot (pw pLen) 0) (2 * pw pLen - 1 + 1) =
        w32 s₂.mem (off S pB) (slot (pw pLen) 0) + 2 ^ 32 *
          val32 s₂.mem (off S pB) (slot (pw pLen) 0 + 4) (2 * pw pLen - 1) := rfl
    rw [Nat.sub_add_cancel (by omega_using [hw4] : 1 ≤ 2 * pw pLen), p2] at h2
    omega
  refine WP.mono (Pub.minv_ok en2.hs en2.h10 (by omega) hlow) fun s₃ ⟨⟨r12lt, r12inv, m3⟩, k3⟩ => ?_
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r30, .r31] (Q := fun t => t.gpr .r30 = off S sE ∧
      t.gpr .r31 = BitVec.ofNat 64 (eBytes pLen qLen) ∧ t.mem = s₃.mem) (by
      prun [scr, (k3.gpr .r28 (by decide)).trans ((k2.gpr .r28 (by decide)).trans h28), exec_li heB',
        exec_addi (show Reg.r28 ≠ .r0 by decide) sE15]) (by rfl)) fun s₄ ⟨⟨a30, a31, m4⟩, k4⟩ => ?_
  have k34 := k3.trans k4
  have p4 : val32 s₄.mem (off S pB) (slot (pw pLen) 0) (2 * pw pLen) = p := by rw [m4, m3]; exact p2
  have r1 : val32 s₄.mem (off S pB) (slot (pw pLen) 1) (2 * pw pLen) = 2 ^ (128 * pw pLen) % p := by
    rw [m4, m3, Outside.val32 o2 (by omega_using [e1, e4]) (by omega_using [hw', hh, e1])]; exact hrr
  have x4 : val32 s₄.mem (off S pB) (slot (pw pLen) 4) (2 * pw pLen) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem H pLen) := by rw [m4, m3]; exact v4
  have eE : Spec.Rsa.bytesAt s₄.mem (off S sE) (eBytes pLen qLen) =
      Spec.Rsa.bytesAt s.mem (off S sE) (eBytes pLen qLen) := by
    rw [m4, m3]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => o2 _ ?_
    have hi := List.mem_range.mp hi
    rcases Nat.lt_or_ge (VG.Proof.Bignum.ofs (off S pB) (off (off S sE) i)) (pZ pLen) with h | h
    · exact absurd rfl (hEsep i hi _ h)
    · exact .inr (Nat.le_trans (by omega : slot (pw pLen) 4 + 8 * (pw pLen + 1) ≤ pZ pLen) h)
  refine WP.seq (WP.mono (ModExp.powSecret_ok (D := off S sE) (L := eBytes pLen qLen) (en2.hs.congr k34.wr)
    (by omega_using [hw4]) (by omega_using [hw']) (by omega) ((k34.gpr .r10 (by decide)).trans en2.h10)
    ((k34.gpr .r29 (by decide)).trans en2.h29) ((k34.gpr .r11 (by decide)).trans en2.h11)
    ((k4.gpr .r12 (by decide)).symm ▸ r12lt)
    (by rw [k4.gpr .r12 (by decide), m4, m3]; exact r12inv) (by rw [p4]; exact hp) (by rw [p4]; exact hpo)
    (by rw [r1, p4]; exact Nat.mod_lt _ (by omega_using [hp])) (by rw [a30]; exact (BitVec.add_zero _).symm) a31 heB
    (by omega_using [heB']) (by rw [(k2.trans k34).rd, (k2.trans k34).wr]; exact hErd)
    (fun i hi x hx => hEsep i hi x hx)) fun s₅ ⟨⟨hpow, o5⟩, k5⟩ => ?_)
  rw [eE, p4, x4] at hpow
  have v5 := hpow (by rw [r1, ← Nat.pow_add, show 64 * pw pLen + 64 * pw pLen = 128 * pw pLen by omega_using []])
  -- `r31` back, and array 4's word `w` zero.
  refine WP.seq ?_
  have k25 := (k2.trans k34).trans k5
  have b23 : s₅.gpr .r23 = off S pB := (k25.gpr .r23 (by decide)).trans h23
  have b10 : s₅.gpr .r10 = off (off S pB) (slot (pw pLen) 0) :=
    (k5.gpr .r10 (by decide)).trans ((k34.gpr .r10 (by decide)).trans en2.h10)
  have b29 : s₅.gpr .r29 = BitVec.ofNat 64 (8 * (pw pLen + 2)) :=
    (k5.gpr .r29 (by decide)).trans ((k34.gpr .r29 (by decide)).trans en2.h29)
  have a14 : off S (pB + slot (pw pLen) 0 + 8 * (pw pLen + 2) + 8 * (pw pLen + 2) + 8 * (pw pLen + 2) +
      8 * (pw pLen + 2) + 8 * (pw pLen + 2)) - 16#64 = off S (pB + (slot (pw pLen) 4 + 8 * pw pLen)) := by
    rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, off, VG.Offset.add_ofNat_sub S (by omega_using [])]
    congr 2; omega_using [e0, e4]
  have st : InRegions s₅.wr (off S (pB + (slot (pw pLen) 4 + 8 * pw pLen))) 8 := by
    have h := ((en2.hs.congr k34.wr).congr k5.wr).st (show slot (pw pLen) 4 + 8 * pw pLen + 8 ≤ pZ pLen by omega)
    dsimp only [VG.Proof.Bignum.off, VG.Proof.Mont.off] at h ⊢
    rwa [BitVec.add_assoc, ← BitVec.ofNat_add] at h
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r31, .r10, .r14, .r0] (Q := fun t =>
      t.gpr .r31 = off S pB ∧ t.gpr .r10 = off (off S pB) (slot (pw pLen) 0) ∧
      t.mem = s₅.mem.writeW (off (off S pB) (slot (pw pLen) 4 + 8 * pw pLen)) (0 : BitVec 64)) (by
      simp only [zeroTop4, PublicChecked.base, List.replicate, List.cons_append, List.nil_append]
      prun [b23, b10, b29, BitVec.add_zero, off_add, a14, hh, st, VG.Proof.Bignum.off_off]
      exact ⟨by rw [e0, hh, Nat.zero_mul, Nat.add_zero], rfl⟩
) (by decide)) fun s₆ ⟨⟨a31', a10', m6⟩, k6⟩ => ?_
  have k6' := (k34.trans k5).trans k6
  have en6 : Env s₆ (off S pB) (pZ pLen) (pw pLen) := ⟨en2.hs.congr k6'.wr, a10',
    (k6'.gpr .r29 (by decide)).trans en2.h29, (k6'.gpr .r11 (by decide)).trans en2.h11, a31', en.hw, en.hw', en.hZ⟩
  have wo : Outside (off S pB) (slot (pw pLen) 4 + 8 * pw pLen) 8 s₅.mem s₆.mem := by
    rw [m6]; exact fun x hx => VG.Proof.Bignum.writeW_outside s₅.mem (off S pB) 0 (by omega_using [hw', hh, e4]) x hx
  have top6 : word s₆.mem (off S pB) (slot (pw pLen) 4 + 8 * pw pLen) = 0 := by
    rw [m6]; exact VG.Proof.Bignum.word_writeW_self _ _ _ _
  have o5' : Outside (off S pB) (slot (pw pLen) 1) (slot (pw pLen) 8 - slot (pw pLen) 1) s₄.mem s₅.mem :=
    outs_within' o5 fun r hr => by
      simp only [Pub.powRs, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> rw [e, e] <;> omega_arith
  have v6 : arr s₆.mem (off S pB) (pw pLen) 4 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem H pLen) ^
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off S sE) (eBytes pLen qLen)) % p := by
    show val32 s₆.mem (off S pB) (slot (pw pLen) 4) (2 * pw pLen) = _
    rw [Outside.val32 wo (by omega_using []) (by omega_using [hw', hh, e4])]; exact v5
  have p6 : arr s₆.mem (off S pB) (pw pLen) 0 = p := by
    show val32 s₆.mem (off S pB) (slot (pw pLen) 0) (2 * pw pLen) = _
    rw [Outside.val32 wo (by omega_using [e0, e4]) (by omega_using [hw', hh, e0]), Outside.val32 o5' (by omega_using [e0, e1]) (by omega_using [hw', hh, e0])]; exact p4
  refine WP.mono (VG.Proof.Dsa.PPC64LE.elemRange_ok en6 top6) fun t ⟨⟨r0, v7, o7, en7⟩, k7⟩ => ?_
  rw [p6] at r0
  refine ⟨⟨by rw [v7]; exact v6, by rw [v7]; exact r0, en7, ?_⟩, ((k2.trans k6').trans k7).mono (by decide)⟩
  rw [m4, m3] at o5'
  exact (((o2.mono (by omega_using [e1, e4]) (by omega_using [e1, e4])).trans (o5'.mono (by omega_using []) (by omega_using [e1, e8]))).trans
    (wo.mono (by omega_using [e1, e4]) (by omega_using [e1, e4]))).trans (o7.mono (by omega_using [e1, e3]) (by omega_using [e1, e3]))

end VG.Proof.Dsa.PPC64LE.Gen

end

end


/-! # DSA parameter generation on PPC64LE: `h^((p − 1) / q) mod p` as a piece

`power_vp`: `power`, from a stage of the search whose claims hold p at
`sPBE` and `(p − 1) / q` at `sE`, apart from the P space, and whose header
word `fH` points at the `pLen` bytes of `h`: the stage kept, array 4 of the
P space `h^((p − 1) / q) mod p`, and `r0 = 0` exactly when it is above 1 and
below p. Its three pieces (`powA`, `h`'s pointer, `powC`) are analysed
apart, the last with the P space's registers and `h`'s pointer public; the
certificate of `powC`, whose code depends on the lengths, is a hypothesis,
which each instance discharges.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation
open VG.Proof.Bignum (slot)

/-- An address outside `[S + a, S + a + Z)`, by its distance from `S`, is
at least `Z` past `S + a`. -/
theorem le_ofs_off {S x : Addr} {a Z : Nat} (ha0 : a < 2 ^ 64) (ha : a + Z ≤ 2 ^ 64)
    (h : (x - S).toNat < a ∨ a + Z ≤ (x - S).toNat) : Z ≤ VG.Proof.Bignum.ofs (off S a) x := by
  have hlt := (x - S).isLt
  simp only [VG.Proof.Bignum.ofs, off]
  rw [Offset.toNat_sub_add x S (by omega_using [ha0])]
  rcases h with h | h
  · rw [Nat.mod_eq_of_lt (by omega_using [h])]; omega_using [ha]
  · rw [show 2 ^ 64 - a + (x - S).toNat = (x - S).toNat - a + 2 ^ 64 by omega_using [h], Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_using [])]
    omega_using [h]

/-- The P space's base. -/
abbrev GP.pS (G : GP) : Addr := off G.scr pB

/-- The certificate of `powC`. -/
abbrev CertC (pLen qLen : Nat) : Prop := ∃ hc, (VG.Taint.checkR VG.PPC64LE.taint VG.Proof.Bignum.PPC64LE.montSums
  (Taint.ofRegs [.r28, .r12, .r6, .r10, .r11, .r21, .r23, .r29, .r31]) (powC pLen qLen) hc).isSome = true ∧
  VG.Taint.fillR VG.Proof.Bignum.PPC64LE.montSums (powC pLen qLen) hc = powC pLen qLen

section
variable {G : GP} {STK : Nat} {σ : State} {V : Nat → BitVec 64} {LS : List Nat} {s : State}

theorem GI.pBig (h : GI G STK σ V LS s) : pB + pZ G.pLen ≤ G.scrLen * 8 ∧ pB ≤ kB G.pLen := by
  have := h.wBig; have := h.kBig
  have : pB ≤ kB G.pLen := by rcases h.lens3 with e | e | e <;> rw [e] <;> decide
  exact ⟨by simp only [pZ]; omega_arith, this⟩

/-- A range of `scratch` as a working space. -/
theorem GI.scrAt (h : GI G STK σ V LS s) {o n : Nat} (ho : o + n ≤ G.scrLen * 8) (hn : 0 < n) : Scr s (off G.scr o) n := by
  have := h.scrFit
  refine ⟨⟨G.scr, o, G.scrLen * 8, by rw [h.wr, h.pre.wr, h.hG]; simp, rfl, ho, by omega_using [this]⟩, ?_⟩
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show o < 2 ^ 64 by omega_using [ho, hn, this]), Nat.mod_eq_of_lt (by omega_using [ho, hn, this])]
  omega_using [ho, this]

/-- The bytes of `scratch` at `a`, below the P space, as a source of a load into it. -/
theorem GI.srcBelow (h : GI G STK σ V LS s) {a n : Nat} (ha : a + n ≤ pB) :
    (∀ i < n, InRegions (s.rd ++ s.wr) (off (off G.scr a) i) 1) ∧
      ∀ i < n, ∀ x, VG.Proof.Bignum.ofs G.pS x < pZ G.pLen → off (off G.scr a) i ≠ x := by
  have ⟨pb, _⟩ := h.pBig
  have fit := h.scrFit
  refine ⟨fun i hi => ?_, fun i hi x hx e => ?_⟩
  · rw [show off (off G.scr a) i = G.sa (a + i) from G.sa_add a i]
    exact h.inRdWr (by omega_using [ha, pb, hi])
  · subst e
    have d : (off (off G.scr a) i - G.scr).toNat = a + i := by
      rw [show off (off G.scr a) i = G.scr + BitVec.ofNat 64 (a + i) from G.sa_add a i, Offset.add_sub_cancel_left,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [ha, pb, fit, hi])]
    have : pZ G.pLen ≤ VG.Proof.Bignum.ofs G.pS (off (off G.scr a) i) :=
      le_ofs_off (S := G.scr) (a := pB) (by decide) (by omega_using [pb, fit]) (.inl (by omega_using [ha, hi, d]))
    omega_using [hx, this]

end

/-- Bytes apart from `scratch` are apart from the P space. -/
theorem src_apart {G : GP} {H : Addr} {n : Nat} (hd : Region.Disjoint ⟨H, n⟩ G.rScr) (hfit : H.toNat + n ≤ 2 ^ 64)
    (hp : pB + pZ G.pLen ≤ G.scrLen * 8) :
    ∀ i < n, ∀ x, VG.Proof.Bignum.ofs G.pS x < pZ G.pLen → off H i ≠ x := by
  intro i hi x hx e
  subst e
  have := past_of_disjoint' hd (a := off H i) (Offset.contains_base _ (show i + 1 ≤ n by omega_using [hi]) (by omega_using [hfit, hi]))
  have : pZ G.pLen ≤ VG.Proof.Bignum.ofs G.pS (off H i) :=
    le_ofs_off (S := G.scr) (a := pB) (by decide) (by omega_using [hp, this]) (.inr (by omega_using [hp, this]))
  omega_using [hx, this]

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- A step that writes the P space alone keeps a stage whose claims are apart from it. -/
theorem SS.of_pspace {σ s t : State} {ws : List Reg} (h : SS G 176 σ c s) (k : BKeep ws s t)
    {lo n : Nat} (o : VG.Proof.Bignum.Outside G.pS lo n s.mem t.mem) (hn : lo + n ≤ pZ G.pLen)
    (hcl : ∀ x ∈ c.cl, Apart pB (pZ G.pLen) x) (h28 : .r28 ∉ ws := by decide) : SS G 176 σ c t := by
  have ⟨pb, pk⟩ := h.gi.pBig
  have hE := h.gi.hEnd_le
  have f0 : Frame [G.rs pB (pZ G.pLen)] s.mem t.mem :=
    frame_of_outside (L := pZ G.pLen) (o.mono (Nat.zero_le _) (by omega_using [hn]))
  have f : Frame (G.rss [(pB, pZ G.pLen)] ++ [rBelow σ 176]) s.mem t.mem :=
    f0.mono fun r hr => List.mem_append_left _ hr
  exact h.of_scrs (ws := ws) ⟨k.gpr, k.rd, k.wr⟩ k.sp (os := [(pB, pZ G.pLen)])
    (fun p hp => by
      rw [List.mem_singleton] at hp; subst hp
      refine ⟨by simp only [hEnd, fSave, pB]; omega_using [], .inl (by simp only [List.length_replicate, pZ]; omega_using [pk]),
        by simp only [List.length_replicate]; omega_using [pb]⟩) f (cl' := c.cl)
    (fun x hx => .inl ⟨hx, fun p hp => by rw [List.mem_singleton] at hp; subst hp; exact hcl x hx⟩) h28

/-- After `powA`: p in array 0, its word `w` zero, and `R² mod p` in array 1. -/
abbrev PA (G : GP) (c : Cfg) (X : State → Prop) (pv : Nat) (σ s : State) : Prop :=
  St G c X σ s ∧ Env s G.pS (pZ G.pLen) (pw G.pLen) ∧ s.gpr .r21 = G.pS ∧ s.gpr .r23 = G.pS ∧
    arr s.mem G.pS (pw G.pLen) 0 = pv ∧ word s.mem G.pS (slot (pw G.pLen) 0 + 8 * pw G.pLen) = 0 ∧
    arr s.mem G.pS (pw G.pLen) 1 = 2 ^ (128 * pw G.pLen) % pv

/-- p from `sPBE` into the P space. -/
theorem powA_vp {pv : Nat} (hPc : (sPBE, Spec.Rsa.i2osp pv G.pLen) ∈ c.cl) (hpv : pv < 256 ^ G.pLen)
    (hp2 : 2 ≤ pv) (hcl : ∀ x ∈ c.cl, Apart pB (pZ G.pLen) x) :
    VP (St G c X) (powA G.pLen) (PA G c X pv) := by
  refine VP.pub (SS.pub fun σ s h => h.1) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
    (powA G.pLen), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_
  have gi := h.gi
  have ⟨pb, _⟩ := gi.pBig
  have l := gi.lens3
  have hb' : Spec.Rsa.bytesAt s.mem (off G.scr sPBE) G.pLen = Spec.Rsa.i2osp pv G.pLen := by
    have := h.sb _ hPc
    simp only [VG.Proof.Rsa.i2osp_length] at this
    exact this
  have ev : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off G.scr sPBE) G.pLen) = pv := by
    rw [hb', VG.Proof.Rsa.os2ip_i2osp, Nat.mod_eq_of_lt hpv]
  have hsrc := gi.srcBelow (a := sPBE) (n := G.pLen) (by rcases l with e | e | e <;> rw [e] <;> decide)
  refine WP.mono (powA_ok l gi.r28 (gi.scrAt pb (by simp only [pZ]; rcases l with e | e | e <;> rw [e] <;> decide)) hsrc.1 hsrc.2 (by rw [ev]; exact hp2))
    fun t ⟨⟨en, a21, a23, v0, z0, v1, o⟩, k⟩ => ?_
  rw [ev] at v0 v1
  refine ⟨⟨h.of_pspace k o ?_ hcl, x⟩, en, a21, a23, v0, z0, v1⟩
  have hZ := pZ_eq l
  have e : ∀ j, slot (pw G.pLen) j = hdrBytes + j * (8 * (pw G.pLen + 2)) := fun _ => rfl
  rw [← hZ, e, e]; simp only [hdrBytes]; omega_using []

/-- After `h`'s pointer and its length. -/
abbrev PE (G : GP) (c : Cfg) (X : State → Prop) (pv : Nat) (H : Addr) (σ s : State) : Prop :=
  PA G c X pv σ s ∧ s.gpr .r12 = H ∧ s.gpr .r6 = BitVec.ofNat 64 G.pLen

/-- `h`'s pointer, from the header word `fH`, and its length. -/
theorem hPtr_vp {pv : Nat} {H : Addr} (hH : fH ∈ c.LS) (hHv : c.V fH = H) :
    VP (PA G c X pv) (.block [ld .r12 fH, .li .r6 G.pLen]) (PE G c X pv H) := by
  refine VP.pub (SS.pub fun σ s h => h.1.1) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
    (.block [ld .r12 fH, .li .r6 G.pLen]), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s ⟨⟨h, x⟩, en, a21, a23, v0, z0, v1⟩ => ?_
  have l := h.lens
  have hE := h.gi.hEnd_le
  have p15 : G.pLen < 2 ^ 15 := by rcases l with e | e | e <;> rw [e] <;> decide
  refine WP.cons (s' := s.write .r12 H) ?_ (WP.cons (s' := (s.write .r12 H).write .r6 (BitVec.ofNat 64 G.pLen))
    (exec_li p15) (WP.block_nil ?_))
  · rw [show ld .r12 fH = .load .d .r12 .r28 fH from rfl, exec_load_d (by decide) ⟨by decide, by decide⟩
      (by rw [h.gi.r28]; exact h.gi.inRdWr (by simp only [hEnd, fSave, fH] at hE ⊢; omega_using [hE])), h.gi.r28,
      show s.mem.readW (G.scr + BitVec.ofNat 64 fH) 64 = H from (h.gi.slotV hH).trans hHv]
  have k : BKeep [.r12, .r6] s ((s.write .r12 H).write .r6 (BitVec.ofNat 64 G.pLen)) :=
    (VG.Proof.Bignum.PPC64LE.Keep.write s .r12 H).trans (VG.Proof.Bignum.PPC64LE.Keep.write _ .r6 _)
  refine ⟨⟨⟨h.of_keep ⟨k.gpr, k.rd, k.wr⟩ rfl k.sp, x⟩, en.keep k (by decide), (k.gpr .r21 (by decide)).trans a21,
    (k.gpr .r23 (by decide)).trans a23, v0, z0, v1⟩, ?_, (Upd.write _ _ _).gpr⟩
  rw [(Upd.write _ .r6 _).other .r12 (by decide), (Upd.write _ _ _).gpr]

/-- h into array 4, its power, and the range check. -/
theorem powC_vp {pv ev : Nat} {H : Addr} {hb : List Byte} (cert : CertC G.pLen G.qLen)
    (hEc : (sE, Spec.Rsa.i2osp ev (eBytes G.pLen G.qLen)) ∈ c.cl) (hev : ev < 256 ^ eBytes G.pLen G.qLen)
    (hp2 : 2 ≤ pv) (hpo : pv % 2 = 1) (hcl : ∀ x ∈ c.cl, Apart pB (pZ G.pLen) x)
    (hsrc : ∀ σ s, St G c X σ s → (∀ i < G.pLen, InRegions (s.rd ++ s.wr) (off H i) 1) ∧
      Region.Disjoint ⟨H, G.pLen⟩ G.rScr ∧ H.toNat + G.pLen ≤ 2 ^ 64 ∧ Spec.Rsa.bytesAt s.mem H G.pLen = hb) :
    VP (PE G c X pv H) (powC G.pLen G.qLen) (fun σ t => St G c X σ t ∧ Env t G.pS (pZ G.pLen) (pw G.pLen) ∧
      arr t.mem G.pS (pw G.pLen) 4 = Spec.Rsa.os2ip hb ^ ev % pv ∧
      (t.gpr .r0 = 0 ↔ 1 < arr t.mem G.pS (pw G.pLen) 4 ∧ arr t.mem G.pS (pw G.pLen) 4 < pv)) := by
  refine VP.taintR _ cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
      rw [(SS.pub (G := G) (fun σ s (h : PE G c X pv H σ s) => h.1.1.1) σ₁ s₁ h₁).2,
        (SS.pub (G := G) (fun σ s (h : PE G c X pv H σ s) => h.1.1.1) σ₂ s₂ h₂).2])
    (fun σ₁ σ₂ s₁ s₂ ⟨⟨⟨h₁, _⟩, e₁, b21, b23, _⟩, c12, c6⟩ ⟨⟨⟨h₂, _⟩, e₂, d21, d23, _⟩, f12, f6⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h₁.gi.r28, h₂.gi.r28]
      · rw [c12, f12]
      · rw [c6, f6]
      · rw [e₁.h10, e₂.h10]
      · rw [e₁.h11, e₂.h11]
      · rw [b21, d21]
      · rw [b23, d23]
      · rw [e₁.h29, e₂.h29]
      · rw [e₁.h31, e₂.h31]) fun σ s ⟨⟨⟨h, x⟩, en, a21, a23, v0, z0, v1⟩, a12, a6⟩ => ?_
  have gi := h.gi
  have ⟨pb, _⟩ := gi.pBig
  have l := gi.lens
  have l3 := gi.lens3
  have heB : 1 ≤ eBytes G.pLen G.qLen ∧ eBytes G.pLen G.qLen < 2 ^ 15 ∧ sE + eBytes G.pLen G.qLen ≤ pB := by
    simp only [eBytes]; rcases l with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> decide
  have hEb : Spec.Rsa.bytesAt s.mem (off G.scr sE) (eBytes G.pLen G.qLen) =
      Spec.Rsa.i2osp ev (eBytes G.pLen G.qLen) := by
    have := h.sb _ hEc
    simp only [VG.Proof.Rsa.i2osp_length] at this
    exact this
  have ev' : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off G.scr sE) (eBytes G.pLen G.qLen)) = ev := by
    rw [hEb, VG.Proof.Rsa.os2ip_i2osp, Nat.mod_eq_of_lt hev]
  obtain ⟨hrd, hdj, hfit, hbs⟩ := hsrc σ s ⟨h, x⟩
  have hE := gi.srcBelow (a := sE) (n := eBytes G.pLen G.qLen) heB.2.2
  refine WP.mono (powC_ok l3 en a23 gi.r28 a12 a6 hrd (src_apart hdj hfit pb) heB.1 heB.2.1 hE.1 hE.2 v0 z0 hp2
    hpo v1) fun t ⟨⟨v4, r0, en', o⟩, k⟩ => ?_
  rw [ev', hbs] at v4
  refine ⟨⟨h.of_pspace k o ?_ hcl, x⟩, en', v4, r0⟩
  have hZ := pZ_eq l3
  have e : ∀ j, slot (pw G.pLen) j = hdrBytes + j * (8 * (pw G.pLen + 2)) := fun _ => rfl
  rw [← hZ, e, e]; simp only [hdrBytes]; omega_using []

/-- `power`: `h^e mod p` into array 4 of the P space, for p at `sPBE`, `e`
at `sE` and `h` at the header word `fH`, and `r0 = 0` exactly when it is
above 1 and below p. -/
theorem power_vp {pv ev : Nat} {H : Addr} {hb : List Byte} (cert : CertC G.pLen G.qLen)
    (hPc : (sPBE, Spec.Rsa.i2osp pv G.pLen) ∈ c.cl) (hpv : pv < 256 ^ G.pLen) (hp2 : 2 ≤ pv) (hpo : pv % 2 = 1)
    (hEc : (sE, Spec.Rsa.i2osp ev (eBytes G.pLen G.qLen)) ∈ c.cl) (hev : ev < 256 ^ eBytes G.pLen G.qLen)
    (hH : fH ∈ c.LS) (hHv : c.V fH = H) (hcl : ∀ x ∈ c.cl, Apart pB (pZ G.pLen) x)
    (hsrc : ∀ σ s, St G c X σ s → (∀ i < G.pLen, InRegions (s.rd ++ s.wr) (off H i) 1) ∧
      Region.Disjoint ⟨H, G.pLen⟩ G.rScr ∧ H.toNat + G.pLen ≤ 2 ^ 64 ∧ Spec.Rsa.bytesAt s.mem H G.pLen = hb) :
    VP (St G c X) (power G.pLen G.qLen) (fun σ t => St G c X σ t ∧ Env t G.pS (pZ G.pLen) (pw G.pLen) ∧
      arr t.mem G.pS (pw G.pLen) 4 = Spec.Rsa.os2ip hb ^ ev % pv ∧
      (t.gpr .r0 = 0 ↔ 1 < arr t.mem G.pS (pw G.pLen) 4 ∧ arr t.mem G.pS (pw G.pLen) 4 < pv)) :=
  VP.assoc (VP.assoc (VP.assoc (VP.seq (powA_vp hPc hpv hp2 hcl)
    (VP.seq (hPtr_vp hH hHv) (powC_vp cert hEc hev hp2 hpo hcl hsrc)))))

/-- `g`, array 4 of the P space, big-endian at `sG`. -/
theorem gStore_vp {g : Nat} (hg : g < 2 ^ (8 * G.pLen)) (hcl : ∀ x ∈ c.cl, Apart sG G.pLen x) :
    VP (fun σ s => St G c X σ s ∧ Env s G.pS (pZ G.pLen) (pw G.pLen) ∧ arr s.mem G.pS (pw G.pLen) 4 = g)
      (.seq (.block [scr .r12 sG, .li .r6 G.pLen]) (VG.Impl.Dsa.PPC64LE.storeBE 4))
      (St G { c with cl := (sG, Spec.Rsa.i2osp g G.pLen) :: c.cl } X) := by
  refine VP.pub (SS.pub fun σ s h => h.1.1) [.r10, .r29] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
    (Taint.ofRegs [.r28, .r10, .r29]) (.seq (.block [scr .r12 sG, .li .r6 G.pLen]) (VG.Impl.Dsa.PPC64LE.storeBE 4)),
    by kernel_rfl⟩ (fun σ₁ σ₂ s₁ s₂ ⟨_, e₁, _⟩ ⟨_, e₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [e₁.h10, e₂.h10]
      · rw [e₁.h29, e₂.h29]) fun σ s ⟨⟨h, x⟩, en, v4⟩ => ?_
  have gi := h.gi
  have l := gi.lens3
  have ⟨pb, pk⟩ := gi.pBig
  have hE := gi.hEnd_le
  have hl : G.pLen < 2 ^ 15 ∧ 1 ≤ G.pLen ∧ G.pLen ≤ 8 * pw G.pLen ∧ sG + G.pLen ≤ pB := by
    rcases l with e | e | e <;> rw [e] <;> decide
  refine WP.seq (WP.cons (s' := s.write .r12 (off G.scr sG)) ?_ (WP.cons
    (s' := (s.write .r12 (off G.scr sG)).write .r6 (BitVec.ofNat 64 G.pLen)) (exec_li hl.1) (WP.block_nil ?_)))
  · rw [show scr .r12 sG = .addi .r12 .r28 sG from rfl, exec_addi (by decide) (by decide), gi.r28]
  have k : BKeep [.r12, .r6] s ((s.write .r12 (off G.scr sG)).write .r6 (BitVec.ofNat 64 G.pLen)) :=
    (VG.Proof.Bignum.PPC64LE.Keep.write s .r12 _).trans (VG.Proof.Bignum.PPC64LE.Keep.write _ .r6 _)
  refine WP.mono (VG.Proof.Dsa.PPC64LE.storeBE_ok (j := 4) (O := off G.scr sG) (k := G.pLen)
    (en.keep k (by decide)) (by decide) ((gi.scrAt (o := sG) (n := G.pLen) (by omega_using [pb, hl]) hl.2.1).congr k.wr)
    (by rw [(Upd.write _ .r6 _).other .r12 (by decide), (Upd.write _ _ _).gpr]) (Upd.write _ _ _).gpr hl.2.1
    hl.2.2.1 ?_) fun t ⟨⟨vt, ot⟩, kt⟩ => ?_
  · intro x hx
    have fit := gi.scrFit
    have e := Offset.toNat_sub_add x G.scr (d := sG) (by decide)
    have hlt := (x - G.scr).isLt
    change (x - (G.scr + BitVec.ofNat 64 sG)).toNat < G.pLen at hx
    rw [e] at hx
    exact le_ofs_off (by decide) (by omega_using [pb, fit]) (.inl (by
      by_cases hy : sG ≤ (x - G.scr).toNat
      · rw [show 2 ^ 64 - sG + (x - G.scr).toNat = (x - G.scr).toNat - sG + 2 ^ 64 by omega_using [hy], Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega_using [])] at hx
        omega_using [hl, hx]
      · rw [Nat.mod_eq_of_lt (by omega_using [hy])] at hx; omega_using [hl, hx]))
  have kk := k.trans kt
  have bt : Spec.Rsa.bytesAt t.mem (off G.scr sG) G.pLen = Spec.Rsa.i2osp g G.pLen := by
    have e1 : Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (off G.scr sG) G.pLen) = g := by
      rw [vt, VG.Proof.Dsa.PPC64LE.read_low _ _ hl.2.2.1 (by
        show arr s.mem G.pS (pw G.pLen) 4 < _; rw [v4]; exact hg)]
      exact v4
    have := VG.Proof.Rsa.i2osp_os2ip (Spec.Rsa.bytesAt t.mem (off G.scr sG) G.pLen)
    rw [e1, show (Spec.Rsa.bytesAt t.mem (off G.scr sG) G.pLen).length = G.pLen by simp [Spec.Rsa.bytesAt]] at this
    exact this.symm
  have f0 : Frame [G.rs sG G.pLen] s.mem t.mem := frame_of_outside (L := G.pLen) ot
  refine ⟨h.of_scrs (ws := [.r12, .r6] ++ VG.Proof.Dsa.PPC64LE.storeRegs) ⟨kk.gpr, kk.rd, kk.wr⟩ kk.sp
    (os := [(sG, G.pLen)]) (fun p hp => by
      rw [List.mem_singleton] at hp; subst hp
      refine ⟨by show hEnd ≤ sG; decide, .inl (by simp only [List.length_replicate]; omega_using [pk, hl]),
        by simp only [List.length_replicate]; omega_using [pb, hl]⟩)
    (f0.mono fun r hr => List.mem_append_left _ hr) (fun y hy => ?_), x⟩
  rcases List.mem_cons.mp hy with rfl | hy
  · refine .inr ⟨by simp only [VG.Proof.Rsa.i2osp_length]; exact bt, ?_⟩
    refine ⟨by show hEnd ≤ sG; decide, .inl (by simp only [VG.Proof.Rsa.i2osp_length]; omega_using [pk, hl]),
      by simp only [VG.Proof.Rsa.i2osp_length]; omega_using [pb, hl]⟩
  · exact .inl ⟨hy, fun p hp => by rw [List.mem_singleton] at hp; subst hp; exact hcl y hy⟩

/-- `g` stored, and `fG` := 1. -/
theorem gOut_vp {g : Nat} (hg : g < 2 ^ (8 * G.pLen)) (hcl : ∀ x ∈ c.cl, Apart sG G.pLen x) :
    VP (fun σ s => St G c X σ s ∧ Env s G.pS (pZ G.pLen) (pw G.pLen) ∧ arr s.mem G.pS (pw G.pLen) 4 = g)
      (VG.Impl.Rsa.PPC64LE.Keys.seqs [.block [scr .r12 sG, .li .r6 G.pLen], VG.Impl.Dsa.PPC64LE.storeBE 4, .block (stImm fG 1)])
      (St G ({ c with cl := (sG, Spec.Rsa.i2osp g G.pLen) :: c.cl }.setV fG 1) X) :=
  VP.assoc (VP.seq (gStore_vp hg hcl) (stImm_vp (o := fG) (v := 1) (fun σ s h => h.1) (by decide) (varOk_of (by decide))
    fun σ s t h h' _ => ⟨h', h.2⟩))

end

end VG.Proof.Dsa.PPC64LE.Gen
