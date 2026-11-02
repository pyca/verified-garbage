module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Out
import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rsa.PrivCheck

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: correctness

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecCorrect.lean`): the frame's allocation, the
setup, the private-key operation, `D`, `DH`, `KDK`, `CL`, `AM`, the
alternative length, the scan, the output and the restores
(`code_correct`), to the outcome on the registers and the stack (`fnPost`,
`result_ok`).
-/

@[expose] public section

/-! ## `vg_rsa_pkcs1_decrypt` on RISC-V: the selection

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecFin.lean`): the validity and `*msg_len`
(`outInit_ok`), the output's loop, and the result and our caller's registers
(`finish_ok`): `selPart_ok`, from `SCN` to `Fin`.
-/

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (mov)
open VG.Proof.RsaPkcs1Enc (firstZero outByte)

/-- `AM`. -/
abbrev amOf (s : State) (kd : List Byte) : List Byte :=
  Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "message") (s.gpr .a4).toNat

/-- The validity of `EM`, as the scan found it. -/
abbrev vOfEM (s : State) (EM : List Byte) : Bool := Proof.RsaPkcs1Enc.vEM EM (s.gpr .a4).toNat

/-- The selected length. -/
abbrev lenOf (s : State) (EM : List Byte) (kd : List Byte) : Nat :=
  Proof.RsaPkcs1Enc.lselOf (vOfEM s EM) ((firstZero EM (s.gpr .a4).toNat).getD 0)
    (Spec.RsaPkcs1Enc.altLength (s.gpr .a4).toNat (clOf kd)) (s.gpr .a4).toNat

theorem sep_lt (EM : List Byte) {k : Nat} (hk : 0 < k) : (firstZero EM k).getD 0 < k := by
  cases h : firstZero EM k with
  | none => simp; omega
  | some i => exact (Proof.RsaPkcs1Enc.firstZero_some h).2.1

/-- At the end of the body: the output and `*msg_len` written, the result in
`a0` and our caller's registers back. -/
structure Fin (s : State) (R : BitVec 64) (EM AM : List Byte) (v ok : Bool) (len : Nat) (u : State) : Prop where
  abi : abiPreserved s (freed frameBytes u)
  a0 : u.gpr .a0 = R
  out : ∀ i < (s.gpr .a4).toNat, u.mem (s.gpr .a0 + BitVec.ofNat 64 i) =
    outByte v ok ((s.gpr .a4).toNat - len) i (EM.getD i 1) (AM.getD i 0)
  ml : u.mem.readW (s.gpr .a2) 64 = BitVec.ofNat 64 len &&& bm ok

section
variable {s : State} (h : DPre s) {R : BitVec 64}
include h

/-- `*msg_len := len & ok`; then `AM` in `a0` and the index zero. -/
theorem outInit_ok {t : State} (hc : Fr3 s R t) :
    WP isa (.block outInit) t fun u => Fr3 s R u ∧ u.mem = t.mem.writeW (s.gpr .a2) (t.gpr .t6) ∧
      u.gpr .a0 = scA s sAM ∧ u.gpr .a1 = BitVec.ofNat 64 0 ∧ Kept [.a0, .a1] t u := by
  have hw : InRegions t.wr (s.gpr .a2) 8 := by rw [hc.wr, h.hwr]; exact ⟨mlR s, by simp, Region.contains_self _ _⟩
  unfold outInit
  refine wp_sd (by rw [hc.s3, BitVec.add_zero]) h.mal hw fun w₁ m₁ => wp_addi (imm := sAM) (fun w₂ p₂ f₂ =>
    wp_li (imm := 0) (by decide) fun u p₃ f₃ => wp_nil ?_) (by decide)
  have F : Frame [mlR s] t.mem w₁.mem := by
    rw [m₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have O₂ : Only [.a0, .a1] w₁ u := (p₂.trans p₃).mono
  have K : Kept [.a0, .a1] t u := (m₁.keep.trans O₂.keep).mono
  have hc₁ : Fr3 s R w₁ := hc.store h m₁.keep (.inr rfl) (fun _ h => h) F
  refine ⟨hc₁.only O₂, by rw [p₃.mem, p₂.mem, m₁.mem], ?_, f₃, K⟩
  rw [p₃.get .a0, f₂, m₁.gpr, hc.s0]

/-- The result, and our caller's registers. -/
theorem finish_ok {t : State} (hc : Fr3 s R t) :
    WP isa (.block finish) t fun u => abiPreserved s (freed frameBytes u) ∧ u.gpr .a0 = R ∧ u.mem = t.mem := by
  unfold finish
  refine wp_mov fun w o e => ?_
  have hw : Fr3 s R w := hc.only o
  exact WP.mono (restore_ok h hw.saves) fun u ⟨ua, u0, um⟩ => ⟨ua, by rw [u0, e, hc.r], by rw [um, o.mem]⟩

/-- The selection: the validity, `*msg_len`, the output and the end. -/
theorem selPart_ok {EM kd : List Byte} {t : State} (hs : SCN s R EM kd t)
    (hR : (R ^^^ BitVec.ofNat 64 1).toNat < 2 ^ 63) :
    WP isa selPart t (Fin s R EM (amOf s kd) (vOfEM s EM) (decide (R ^^^ BitVec.ofNat 64 1 = 0)) (lenOf s EM kd)) := by
  have hk := h.k2
  have hk64 := h.k1
  have hsep := sep_lt EM (k := (s.gpr .a4).toNat) (by omega)
  have hal := Proof.RsaPkcs1Enc.altLength_le (s.gpr .a4).toNat (clOf kd)
  have o0 := outIn h hs.toPost (i := 0) (by omega)
  rw [BitVec.add_zero] at o0
  unfold selPart
  refine WP.seq (WP.mono (validBlock_ok hs.toPost o0 (outIn h hs.toPost (by omega)) hs.a4 hs.a5 hs.al hs.a6 hs.a7
    (by omega) hR) fun t₁ ⟨O₁, x1, x2, x4, x3, x6, x5⟩ => ?_)
  -- The values the block computed.
  have e0 : t.mem (s.gpr .a0) = EM.getD 0 1 := by
    rw [← hs.em, bytes_getD' _ _ (by omega), BitVec.add_zero]
  have e1 : t.mem (s.gpr .a0 + BitVec.ofNat 64 1) = EM.getD 1 1 := by rw [← hs.em, bytes_getD' _ _ (by omega)]
  have eL : (if Proof.RsaPkcs1Enc.vOf (EM.getD 0 1) (EM.getD 1 1) (firstZero EM (s.gpr .a4).toNat).isSome
      ((firstZero EM (s.gpr .a4).toNat).getD 0) then s.gpr .a4 - BitVec.ofNat 64 ((firstZero EM (s.gpr .a4).toNat).getD 0) -
        BitVec.ofNat 64 1 else BitVec.ofNat 64 (Spec.RsaPkcs1Enc.altLength (s.gpr .a4).toNat (clOf kd))) =
      BitVec.ofNat 64 (lenOf s EM kd) := by
    simp only [lenOf, vOfEM, Proof.RsaPkcs1Enc.vEM, Proof.RsaPkcs1Enc.lselOf]
    split
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_sub_of_le
          (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]; omega),
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    · rfl
  have hlen : lenOf s EM kd ≤ (s.gpr .a4).toNat := by
    simp only [lenOf, Proof.RsaPkcs1Enc.lselOf]; split <;> omega
  simp only [e0, e1] at x4 x6 x5
  rw [eL] at x6 x5
  rw [show s.gpr .a4 - BitVec.ofNat 64 (lenOf s EM kd) = BitVec.ofNat 64 ((s.gpr .a4).toNat - lenOf s EM kd) by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    omega] at x5
  have hc₁ : Fr3 s R t₁ := hs.toPost.fr3.only O₁
  -- `*msg_len`.
  refine WP.seq (WP.mono (outInit_ok h hc₁) fun t₂ ⟨hc₂, m₂, x0, xa1, K₂⟩ => ?_)
  rw [x6] at m₂
  have F₂ : Frame [mlR s] t₁.mem t₂.mem := by
    rw [m₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have bk : ∀ (X : Region), X.Disjoint (mlR s) → X.len ≤ 2 ^ 64 → ∀ i < X.len,
      t₂.mem (X.base + BitVec.ofNat 64 i) = t.mem (X.base + BitVec.ofNat 64 i) := fun X hX hl i hi => by
    rw [F₂.bytes (fun Y hY' => by rw [List.mem_singleton.mp hY']; exact hX) hl hi, O₁.mem]
  have hwo := h.wo; have h4 := h.h1
  have h0 : OInv s R (BitVec.ofNat 64 (lenOf s EM kd) &&& bm (decide (R ^^^ BitVec.ofNat 64 1 = 0))) EM (amOf s kd)
      (vOfEM s EM) (decide (R ^^^ BitVec.ofNat 64 1 = 0)) ((s.gpr .a4).toNat - lenOf s EM kd) 0 t₂ :=
    { toFr3 := hc₂
      ml := by rw [m₂, Mem.readW_writeW_self64]
      a1 := xa1
      t1 := by rw [K₂.gpr _ (by decide), x1, BitVec.add_zero]
      a0 := by rw [x0, BitVec.add_zero]
      a3 := by rw [K₂.gpr _ (by decide), x3]
      a4 := by rw [K₂.gpr _ (by decide), x4]
      a5 := by rw [K₂.gpr _ (by decide), x5]
      a6 := by rw [K₂.gpr _ (by decide), O₁.get .a6, hs.a6]
      a7 := by rw [K₂.gpr _ (by decide), O₁.get .a7, hs.a7]
      done := fun j hj => absurd hj (Nat.not_lt_zero _)
      todo := fun j _ hj => by
        rw [show s.gpr .a0 = (oR s).base from rfl, bk (oR s) h.om (by show (s.gpr .a1).toNat ≤ 2 ^ 64; omega) j
          (by show j < (s.gpr .a1).toNat; omega), show (oR s).base = s.gpr .a0 from rfl, ← hs.em, bytes_getD' _ _ hj]
      am := fun j hj => by
        rw [show scA s sAM = (⟨scA s sAM, (s.gpr .a4).toNat⟩ : Region).base from rfl,
          bk ⟨scA s sAM, (s.gpr .a4).toNat⟩ ((h.ms.symm.sub_left (scSub h (by unfold sAM scrBytes; omega))))
            (by show (s.gpr .a4).toNat ≤ 2 ^ 64; omega) j hj]
        have ham : Spec.Rsa.bytesAt t.mem (scA s sAM) (s.gpr .a4).toNat = amOf s kd := hs.am
        rw [← ham, bytes_getD' _ _ hj] }
  refine WP.seq (WP.mono (selLoop_ok h (by omega) h0 (by rw [K₂.gpr _ (by decide), x2])) fun t₃ h₃ => ?_)
  refine WP.mono (finish_ok h h₃.toFr3) fun u ⟨ua, u0, um⟩ => ⟨ua, u0, fun i hi => ?_, ?_⟩
  · rw [um]; exact h₃.done i hi
  · rw [um]; exact h₃.ml

end

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Proof.RsaPkcs1Enc (outByte)

/-- The outcome, on the registers and the stack. -/
def fnPost (s s' : State) : Prop :=
  Spec.RsaPkcs1Enc.writtenMsg s'.mem (s.gpr .a0) (s.gpr .a2) (s.gpr .a4).toNat ((s'.gpr .a0).setWidth 32)
    (Spec.RsaPkcs1Enc.decrypt (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat) (dBytes s)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat) (cOf s))

theorem zx_setWidth (x : BitVec 64) : (zx x).setWidth 32 = x.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [zx, BitVec.toNat_setWidth]
  omega

theorem zx_one (x : BitVec 64) : decide (zx x ^^^ BitVec.ofNat 64 1 = 0) = decide (x.setWidth 32 = 1) := by
  have : zx x ^^^ BitVec.ofNat 64 1 = 0 ↔ x.setWidth 32 = 1 := by
    rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_eq_zero_iff]
    constructor
    · intro h; rw [← zx_setWidth, h]; rfl
    · intro h; simp only [zx, h]; rfl
  simp only [this]

theorem zx_lt (x : BitVec 64) : (zx x ^^^ BitVec.ofNat 64 1).toNat < 2 ^ 63 := by
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat]
  have : (zx x).toNat < 2 ^ 32 := by simp only [zx, BitVec.toNat_setWidth]; omega
  exact Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow (n := 32) this (by decide)) (by decide)

/-- RSADP, as the specification calls the private-key operation. -/
def rsadpOf (s : State) (C : List Byte) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat) C
    (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat)

/-- The outcome, from what the private-key operation gave and the end. -/
theorem result_ok {s : State} (h : DPre s) {x : BitVec 64} {mc : Mem} {t : State} {kd : List Byte}
    (hkd : kd = Spec.RsaPkcs1Enc.kdk (s.gpr .a4).toNat (dBytes s) (cOf s))
    (hres : Spec.Rsa.writtenOutcome mc (s.gpr .a0) (s.gpr .a4).toNat (x.setWidth 32) (rsadpOf s (cOf s)))
    (hx : t.gpr .a0 = zx x)
    (hout : ∀ i < (s.gpr .a4).toNat, t.mem (s.gpr .a0 + BitVec.ofNat 64 i) =
      outByte (vOfEM s (Spec.Rsa.bytesAt mc (s.gpr .a0) (s.gpr .a4).toNat)) (decide (zx x ^^^ BitVec.ofNat 64 1 = 0))
        ((s.gpr .a4).toNat - lenOf s (Spec.Rsa.bytesAt mc (s.gpr .a0) (s.gpr .a4).toNat) kd) i
        ((Spec.Rsa.bytesAt mc (s.gpr .a0) (s.gpr .a4).toNat).getD i 1) ((amOf s kd).getD i 0))
    (hml : t.mem.readW (s.gpr .a2) 64 =
      BitVec.ofNat 64 (lenOf s (Spec.Rsa.bytesAt mc (s.gpr .a0) (s.gpr .a4).toNat) kd) &&&
        bm (decide (zx x ^^^ BitVec.ofNat 64 1 = 0)))
    (hAM : (amOf s kd).length = (s.gpr .a4).toNat) : fnPost s t := by
  have hk := h.k1
  unfold fnPost
  have hn : (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat).length = (s.gpr .a4).toNat :=
    Proof.Rsa.bytesAt_length' _ _ _
  have hC : (cOf s).length = (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat).length := by
    rw [hn]; exact Proof.Rsa.bytesAt_length' _ _ _
  have hbytes : Spec.Rsa.bytesAt t.mem (s.gpr .a0) (s.gpr .a4).toNat =
      (List.range (s.gpr .a4).toNat).map fun i => t.mem (s.gpr .a0 + BitVec.ofNat 64 i) := rfl
  have hw : Spec.Rsa.wordsAt t.mem (s.gpr .a2) 1 = [t.mem.readW (s.gpr .a2) 64] := by
    simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
  simp only [Spec.RsaPkcs1Enc.decrypt]
  show Spec.RsaPkcs1Enc.writtenMsg _ _ _ _ _ (Spec.RsaPkcs1Enc.decryptWith (rsadpOf s)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat).length (dBytes s) (cOf s))
  cases hO : rsadpOf s (cOf s) with
  | ok EM' =>
    rw [hO] at hres
    obtain ⟨hr, hb⟩ := hres
    have hok : decide (zx x ^^^ BitVec.ofNat 64 1 = 0) = true := by rw [zx_one, hr]; rfl
    rw [Proof.RsaPkcs1Enc.decryptWith_of_ok hC (by rw [hn]; omega) hO]
    subst hb
    have hEMl := Proof.Rsa.bytesAt_length' mc (s.gpr .a0) (s.gpr .a4).toNat
    have hal := Proof.RsaPkcs1Enc.altLength_le (s.gpr .a4).toNat (clOf kd)
    obtain ⟨hL1, hmap⟩ := Proof.RsaPkcs1Enc.sel_eq hEMl hAM (by omega) hal
    have hM : Spec.RsaPkcs1Enc.implicitDecode (dBytes s) (cOf s) (Spec.Rsa.bytesAt mc (s.gpr .a0) (s.gpr .a4).toNat) =
        (if Spec.RsaPkcs1Enc.valid (Spec.Rsa.bytesAt mc (s.gpr .a0) (s.gpr .a4).toNat) then
          Spec.RsaPkcs1Enc.lastN (Spec.RsaPkcs1Enc.msgLength (Spec.Rsa.bytesAt mc (s.gpr .a0) (s.gpr .a4).toNat))
            (Spec.Rsa.bytesAt mc (s.gpr .a0) (s.gpr .a4).toNat)
        else Spec.RsaPkcs1Enc.lastN (Spec.RsaPkcs1Enc.altLength (s.gpr .a4).toNat (clOf kd)) (amOf s kd)) := by
      simp only [Spec.RsaPkcs1Enc.implicitDecode, Spec.RsaPkcs1Enc.alternative, hEMl, hkd]
    rw [hM]
    refine ⟨by rw [hx, zx_setWidth, hr], ?_, ?_⟩
    · rw [hbytes, ← hmap]
      exact List.map_congr_left fun i hi => by rw [hout i (List.mem_range.mp hi), hok]
    · rw [hw, hml, hok, show bm true = BitVec.allOnes 64 from rfl, BitVec.and_allOnes, ← hL1]
  | invalid =>
    rw [hO] at hres
    obtain ⟨hr, -⟩ := hres
    have hok : decide (zx x ^^^ BitVec.ofNat 64 1 = 0) = false := by rw [zx_one, hr]; rfl
    rw [Proof.RsaPkcs1Enc.decryptWith_of_invalid hO]
    refine ⟨by rw [hx, zx_setWidth, hr], ?_, ?_⟩
    · rw [hbytes, List.map_congr_left (g := fun _ => (0 : Byte)) fun i hi => by
        rw [hout i (List.mem_range.mp hi), hok, Proof.RsaPkcs1Enc.outByte_false]]
      rw [List.map_const', List.length_range]
    · rw [hw, hml, hok]; simp [bm]
  | fault =>
    rw [hO] at hres
    obtain ⟨hr, -⟩ := hres
    have hok : decide (zx x ^^^ BitVec.ofNat 64 1 = 0) = false := by rw [zx_one, hr]; rfl
    rw [Proof.RsaPkcs1Enc.decryptWith_of_fault hC (by rw [hn]; omega) hO]
    refine ⟨by rw [hx, zx_setWidth, hr], ?_, ?_⟩
    · rw [hbytes, List.map_congr_left (g := fun _ => (0 : Byte)) fun i hi => by
        rw [hout i (List.mem_range.mp hi), hok, Proof.RsaPkcs1Enc.outByte_false]]
      rw [List.map_const', List.length_range]
    · rw [hw, hml, hok]; simp [bm]

theorem code_correct (s : State) (hpre : (Spec.RsaPkcs1Enc.decryptContract RISCV64.abi stackBytes).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ fnPost s t := by
  show WP isa code s fun t => abiPreserved s t ∧ fnPost s t
  have h := dPre_of hpre
  have hk := h.k2
  unfold code
  refine WP.allocLe ⟨by decide, by decide, by decide⟩ (by have := h.sp1; unfold stackBytes at this; omega) ?_
  unfold body
  refine WP.seq (WP.mono (setup_ok h) fun t₁ A => ?_)
  refine WP.seq (call_ok h A fun t₂ A₂ => ?_)
  refine WP.seq (WP.mono (dBuild_ok h A₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (hashD_ok h h₃) fun t₄ h₄ => ?_)
  refine WP.seq (WP.mono (kdkMac_ok h h₄) fun t₅ h₅ => ?_)
  refine WP.seq (WP.mono (clLoop_ok h h₅.toPost h₅.kdk) fun t₆ h₆ => ?_)
  refine WP.seq (WP.mono (amLoop_ok h h₆) fun t₇ h₇ => ?_)
  refine WP.seq (WP.mono (maskPart_ok h h₇) fun t₈ h₈ => ?_)
  refine WP.seq (WP.mono (alPart_ok h h₈) fun t₉ h₉ => ?_)
  refine WP.seq (WP.mono (scanPart_ok h h₉) fun t₁₀ h₁₀ => ?_)
  refine WP.mono (selPart_ok h h₁₀ (zx_lt _)) fun u hu => ⟨hu.abi, ?_⟩
  have hAM : (amOf s (Spec.RsaPkcs1Enc.kdk (s.gpr .a4).toNat (dBytes s) (cOf s))).length = (s.gpr .a4).toNat := by
    show (Spec.RsaPkcs1Enc.irprf _ _ _).length = _
    rw [← h₇.am]; exact Proof.Rsa.bytesAt_length' _ _ _
  simp only [freed]
  refine result_ok h rfl ?_ hu.a0 hu.out hu.ml hAM
  exact A₂.out

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec
