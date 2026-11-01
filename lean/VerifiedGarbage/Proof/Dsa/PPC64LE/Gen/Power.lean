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
  have pl15 : pLen < 2 ^ 15 := by omega
  have w15 : pLen / 4 < 2 ^ 15 := by omega
  have p15 : pLen + 16 < 2 ^ 15 := by omega
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
    ⟨hs.congr k1.wr, a10, a29, a11, a31, by omega, by omega, by rw [hZ]⟩
  refine WP.mono (VG.Proof.Dsa.PPC64LE.loadArr_ok en1 (j := 0) (by decide) a12 a6 (by omega) (by omega)
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
    ((k5.gpr .r5 (by decide)).trans ((k4.gpr .r5 (by decide)).trans a5)) en5.h11 (by omega) (by omega)
    (by rw [e, hZ.symm.trans (e 28)]; omega) (by rw [v0']; exact hp)) fun t ⟨hr2, o7, k7⟩ => ?_
  rw [v0'] at hr2
  have k1t := (((k1.trans k2).trans k3).trans ((k4.trans k5).trans k7))
  have k2t := (k2.trans k3).trans ((k4.trans k5).trans k7)
  refine ⟨⟨en5.keep k7 (by decide), (k2t.gpr .r21 (by decide)).trans a21, (k2t.gpr .r23 (by decide)).trans a23,
    ?_, ?_, hr2, ?_⟩, k1t.mono (by decide)⟩
  · show val32 t.mem (off S pB) (slot (pw pLen) 0) (2 * pw pLen) = _
    rw [Outside.val32 o7 (by omega) (by omega), hm5]; exact v0
  · rw [Outside.word o7 (by omega) (by omega), hm5]; exact top0
  · rw [hm5] at o7
    exact (o2.mono (by omega) (by omega)).trans (o7.mono (by omega) (by omega))

theorem outs_within' {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m') {lo hi : Nat}
    (hw : ∀ r ∈ rs, lo ≤ r.1 ∧ r.1 + r.2 ≤ hi) : Outside B lo (hi - lo) m m' :=
  fun x hx => h x fun r hr => by have := hw r hr; omega

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
  refine WP.seq (WP.mono (VG.Proof.Dsa.PPC64LE.loadArr_ok en (j := 4) (by decide) h12 h6 (by omega) (by omega)
    hHrd hHsep) fun s₂ ⟨⟨v4, top4, o2, a10⟩, k2⟩ => ?_)
  have en2 := VG.Proof.Dsa.PPC64LE.env_keep10 en k2 (by decide) a10
  -- `-p⁻¹`, and the exponent's pointer and length.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have p2 : val32 s₂.mem (off S pB) (slot (pw pLen) 0) (2 * pw pLen) = p := by
    rw [Outside.val32 o2 (by omega) (by omega)]; exact hp0
  have hlow : (word s₂.mem (off S pB) (slot (pw pLen) 0)).toNat % 2 = 1 := by
    have h1 := word_eq_w32 s₂.mem (off S pB) (slot (pw pLen) 0)
    have h2 : val32 s₂.mem (off S pB) (slot (pw pLen) 0) (2 * pw pLen - 1 + 1) =
        w32 s₂.mem (off S pB) (slot (pw pLen) 0) + 2 ^ 32 *
          val32 s₂.mem (off S pB) (slot (pw pLen) 0 + 4) (2 * pw pLen - 1) := rfl
    rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * pw pLen), p2] at h2
    omega
  refine WP.mono (Pub.minv_ok en2.hs en2.h10 (by omega) hlow) fun s₃ ⟨⟨r12lt, r12inv, m3⟩, k3⟩ => ?_
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r30, .r31] (Q := fun t => t.gpr .r30 = off S sE ∧
      t.gpr .r31 = BitVec.ofNat 64 (eBytes pLen qLen) ∧ t.mem = s₃.mem) (by
      prun [scr, (k3.gpr .r28 (by decide)).trans ((k2.gpr .r28 (by decide)).trans h28), exec_li heB',
        exec_addi (show Reg.r28 ≠ .r0 by decide) sE15]) (by rfl)) fun s₄ ⟨⟨a30, a31, m4⟩, k4⟩ => ?_
  have k34 := k3.trans k4
  have p4 : val32 s₄.mem (off S pB) (slot (pw pLen) 0) (2 * pw pLen) = p := by rw [m4, m3]; exact p2
  have r1 : val32 s₄.mem (off S pB) (slot (pw pLen) 1) (2 * pw pLen) = 2 ^ (128 * pw pLen) % p := by
    rw [m4, m3, Outside.val32 o2 (by omega) (by omega)]; exact hrr
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
    (by omega) (by omega) (by omega) ((k34.gpr .r10 (by decide)).trans en2.h10)
    ((k34.gpr .r29 (by decide)).trans en2.h29) ((k34.gpr .r11 (by decide)).trans en2.h11)
    ((k4.gpr .r12 (by decide)).symm ▸ r12lt)
    (by rw [k4.gpr .r12 (by decide), m4, m3]; exact r12inv) (by rw [p4]; exact hp) (by rw [p4]; exact hpo)
    (by rw [r1, p4]; exact Nat.mod_lt _ (by omega)) (by rw [a30]; exact (BitVec.add_zero _).symm) a31 heB
    (by omega) (by rw [(k2.trans k34).rd, (k2.trans k34).wr]; exact hErd)
    (fun i hi x hx => hEsep i hi x hx)) fun s₅ ⟨⟨hpow, o5⟩, k5⟩ => ?_)
  rw [eE, p4, x4] at hpow
  have v5 := hpow (by rw [r1, ← Nat.pow_add, show 64 * pw pLen + 64 * pw pLen = 128 * pw pLen by omega])
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
    rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, off, VG.Offset.add_ofNat_sub S (by omega)]
    congr 2; omega
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
    rw [m6]; exact fun x hx => VG.Proof.Bignum.writeW_outside s₅.mem (off S pB) 0 (by omega) x hx
  have top6 : word s₆.mem (off S pB) (slot (pw pLen) 4 + 8 * pw pLen) = 0 := by
    rw [m6]; exact VG.Proof.Bignum.word_writeW_self _ _ _ _
  have o5' : Outside (off S pB) (slot (pw pLen) 1) (slot (pw pLen) 8 - slot (pw pLen) 1) s₄.mem s₅.mem :=
    outs_within' o5 fun r hr => by
      simp only [Pub.powRs, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> rw [e, e] <;> omega
  have v6 : arr s₆.mem (off S pB) (pw pLen) 4 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem H pLen) ^
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off S sE) (eBytes pLen qLen)) % p := by
    show val32 s₆.mem (off S pB) (slot (pw pLen) 4) (2 * pw pLen) = _
    rw [Outside.val32 wo (by omega) (by omega)]; exact v5
  have p6 : arr s₆.mem (off S pB) (pw pLen) 0 = p := by
    show val32 s₆.mem (off S pB) (slot (pw pLen) 0) (2 * pw pLen) = _
    rw [Outside.val32 wo (by omega) (by omega), Outside.val32 o5' (by omega) (by omega)]; exact p4
  refine WP.mono (VG.Proof.Dsa.PPC64LE.elemRange_ok en6 top6) fun t ⟨⟨r0, v7, o7, en7⟩, k7⟩ => ?_
  rw [p6] at r0
  refine ⟨⟨by rw [v7]; exact v6, by rw [v7]; exact r0, en7, ?_⟩, ((k2.trans k6').trans k7).mono (by decide)⟩
  rw [m4, m3] at o5'
  exact (((o2.mono (by omega) (by omega)).trans (o5'.mono (by omega) (by omega))).trans
    (wo.mono (by omega) (by omega))).trans (o7.mono (by omega) (by omega))

end VG.Proof.Dsa.PPC64LE.Gen
