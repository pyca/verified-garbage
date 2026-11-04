module

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Sg.Pre
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Pub
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Mgf
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.RsaPss.SignCases
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaPss.Encoding
import VerifiedGarbage.Proof.RsaPss.CtPad
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# RSASSA-PSS signing on RISC-V: the checks, and the outcome by cases

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Sg/Checks.lean`, `Sg/Spec.lean`): for a modulus whose
first byte is not zero, `lo` is EMSA-PSS's (`lo_eq`); `chkEm_ok` and
`chkSalt_ok`: whether `emLen < hLen + 2` and whether the salt is longer than
`emLen - hLen - 2`, in `a0`; `fail_ok`: `encFail` writes zeros to `out` and
returns 0. `signOut G s`, what the contract asks of a call from `s`: it is
`invalid` if the modulus' first byte is zero (`signOut_zero`) or the salt
does not fit (`signOut_long`), and otherwise the private operation
(`privOut`) on the encoding `encEm`, with `lo` and the mask `c` the code
computes (`signOut_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64.Sg

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64.Sign VG.WriteBytes
open VG.Impl.RsaOaep.RISCV64 (encFail)
open VG.Proof.RsaOaep.RISCV64 (Base Fits fx Saves kR ne_zero_ltBit msgBit slR_sub)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only wp_li wp_sub wp_subi wp_srl wp_or wp_mov wp_nil fill_ok)

/-- `lo` as a number. -/
def loN (s : State) : Nat := if (s.mem (s.gpr .a2)).toNat = 1 then 1 else 0

theorem ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

theorem loN_le (s : State) : loN s ≤ 1 := by unfold loN; split <;> omega

theorem lo_eq {s : State} (h0 : s.mem (s.gpr .a2) ≠ 0) : loS s = BitVec.ofNat 64 (loN s) := by
  have hn : (s.mem (s.gpr .a2)).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
  have := (Proof.RsaPss.RISCV64.byte_ok _ (s.mem (s.gpr .a2)).isLt hn).1
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  exact this

section
variable {D : Nat} {s : State} (P : PreS D s)
include P

theorem Entered.only {t t' : State} {rs : List Reg} (E : Entered s t) (o : Only rs t t')
    (hrs : ∀ r ∈ rs, r ∉ .s0 :: fx ++ ([.t1] : List Reg) := by decide) : Entered s t' :=
  ⟨E.base.only (fits P) o fun r h h' => hrs r h (List.mem_append_left _ h'),
    (o.gpr .t1 fun h => hrs _ h (List.mem_append_right _ (List.mem_singleton_self _))).trans E.t1,
    by rw [o.mem]; exact E.sp⟩

theorem k_lo (h0 : s.mem (s.gpr .a2) ≠ 0) : s.gpr .a3 - loS s = BitVec.ofNat 64 (kk s - loN s) := by
  have hk1 : 64 ≤ kk s := P.k1
  have ek : (s.gpr .a3).toNat = kk s := rfl
  have := loN_le s
  rw [lo_eq h0, ← ofNat_toNat (s.gpr .a3), Offset.ofNat_sub_ofNat (by omega)]

/-- `chkEm`: whether `emLen < hLen + 2`. -/
theorem chkEm_ok {H : Impl.Hmac.Stream.RISCV64.Hash} (hD64 : H.D ≤ 64) {t : State} (E : Entered s t)
    (h0 : s.mem (s.gpr .a2) ≠ 0) :
    WP isa (.block (chkEm H)) t fun t' => Entered s t' ∧
      (t'.gpr .a0 != 0) = decide (kk s - loN s < H.D + 2) := by
  have hk2 : kk s ≤ 1024 := P.k2
  refine wp_sub fun t₁ o₁ e₁ => wp_subi (imm := H.D + 2) (h := by omega) fun t₂ o₂ e₂ => wp_srl fun t₃ o₃ e₃ =>
    wp_nil ?_
  have k₃ : Only [.a0] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine ⟨E.only P k₃, ?_⟩
  rw [e₃, e₂, e₁, Base.sk E.base, Base.slo E.base, k_lo P h0]
  exact ne_zero_ltBit (by omega) (by omega)

/-- `chkSalt`: whether the salt is longer than `emLen - hLen - 2`. -/
theorem chkSalt_ok {H : Impl.Hmac.Stream.RISCV64.Hash} (hD64 : H.D ≤ 64) {t : State} (E : Entered s t)
    (h0 : s.mem (s.gpr .a2) ≠ 0) (hem : H.D + 2 ≤ kk s - loN s) :
    WP isa (.block (chkSalt H)) t fun t' => Entered s t' ∧
      (t'.gpr .a0 != 0) = decide (kk s - loN s - (H.D + 2) < (stackArg s 11).toNat) := by
  have hk2 : kk s ≤ 1024 := P.k2
  refine wp_sub fun t₅ o₅ e₅ => wp_subi (imm := H.D + 2) (h := by omega) fun t₆ o₆ e₆ => wp_sub fun t₇ o₇ e₇ =>
    wp_srl fun t₈ o₈ e₈ => wp_srl fun t₉ o₉ e₉ => wp_or fun t₁₀ o₁₀ e₁₀ => wp_nil ?_
  have k₁₀ : Only [.a0, .a2] t t₁₀ := (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans o₁₀))))).mono
  refine ⟨E.only P k₁₀, ?_⟩
  rw [e₁₀, o₉.get .a0, e₉, e₈, o₈.get .s4, e₇, o₇.get .s4, e₆, o₆.get .s4, e₅, o₅.get .s4, Base.sk E.base,
    Base.slo E.base, Base.ssl E.base, k_lo P h0, Offset.ofNat_sub_ofNat hem, BitVec.or_comm]
  have := msgBit (x := kk s - loN s - (H.D + 2)) (y := (stackArg s 11).toNat) (by omega) (BitVec.isLt _)
  rwa [ofNat_toNat] at this

theorem oR_eq : oR s = ⟨s.gpr .a0, (s.gpr .a3).toNat⟩ := by rw [oR, P.ok]

/-- `encFail`: zeros to `out`, and 0. -/
theorem fail_ok {t : State} (h : Base Ss vS s t) :
    WP isa encFail t fun t' => Saves s t' ∧ t'.rd = s.rd ∧ t'.gpr .a0 = 0 ∧
      Spec.Rsa.bytesAt t'.mem (s.gpr .a0) (kk s) = List.replicate (kk s) 0 := by
  have hk1 := P.k1; have hk2 := P.k2
  have ek : kk s = (s.gpr .a3).toNat := rfl
  refine WP.seq (WP.seq (wp_mov fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_li (imm := 0) (by decide)
    fun t₃ o₃ e₃ => wp_nil ?_))
  have k₃ : Only [.a1, .t5, .t0] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  have hout : ∀ i < kk s, InRegions t₃.wr (s.gpr .a0 + BitVec.ofNat 64 i) 1 := fun i hi => by
    rw [k₃.wr, h.wr]
    exact ⟨oR s, List.mem_cons_of_mem _ (by rw [P.hwr]; simp),
      Offset.contains_base _ (by rw [P.ok]; omega) (by have := P.wo; omega)⟩
  refine WP.mono (fill_ok (p := s.gpr .a0) (n := kk s) (b := 0) (by omega) (by omega)
    (by rw [o₃.get .a1, o₂.get .a1, e₁, Base.sout h]) (by rw [o₃.get .t5, e₂, o₁.get .s1, Base.sk h]; simp)
    (by rw [e₃]; rfl) hout) fun t₄ ⟨k₄, m₄⟩ => wp_li (imm := 0) (by decide) fun t₅ o₅ e₅ => wp_nil ?_
  have hko : (kR s).Disjoint ⟨s.gpr .a0, (s.gpr .a3).toNat⟩ := by
    rw [← oR_eq P]; exact P.ko.sub_left kR_sub
  have hf : Frame [⟨s.gpr .a0, kk s⟩] t.mem t₅.mem := by
    have := Proof.RsaPkcs1Sig.frame_writeBytes t₃.mem (s.gpr .a0) (List.replicate (kk s) (0 : Byte))
    rw [List.length_replicate] at this
    rw [o₅.mem, m₄, ← k₃.mem] at *; exact this
  have K := (k₃.keep.trans (k₄.trans o₅.keep)).mono (rs' := [.a0, .a1, .t5, .t0])
  refine ⟨h.sv.keep K hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact hko.sub_left (slR_sub s)),
    K.rd.trans h.rd, by rw [e₅]; rfl, ?_⟩
  have := Proof.RsaPkcs1Sig.bytesAt_writeBytes t₃.mem (s.gpr .a0) (List.replicate (kk s) (0 : Byte))
    (by simp; omega)
  rw [List.length_replicate] at this
  rw [o₅.mem, m₄, this]

end

end VG.Proof.RsaPss.RISCV64.Sg

namespace VG.Proof.RsaPss

open Spec Spec.RsaPss
open Mgf1 (Hash xorBytes mgf1)
open Proof.Mgf1 (Valid xorBytes_length mgf1_length)

/-! ## The encoding with a modulus, for two hash functions

As `encodeK_eq` and `sign_eq` (`Proof/RsaPss/EncBytes.lean`,
`SignCases.lean`), with the hash function `H` and MGF1's `G`. -/

variable (H G : Hash)

theorem encodeK_eq₂ (hH : Valid H) (hG : Valid G) {n₀ : Byte} {rest mHash salt : List Byte} (h0 : n₀ ≠ 0)
    (hm : mHash.length = H.len) {emBits emLen lo db : Nat}
    (hb : bitLength (Rsa.os2ip (n₀ :: rest)) - 1 = emBits) (he : emLength emBits = emLen)
    (hlo : (n₀ :: rest).length - emLen = lo) (hdb : emLen - H.len - 1 = db)
    (hfit : H.len + salt.length + 2 ≤ emLen) :
    encodeK H G (n₀ :: rest) mHash salt =
      some ((List.range (n₀ :: rest).length).map
        (emT lo db salt.length salt (H.hash (zeros 8 ++ mHash ++ salt))
          (mgf1 G (H.hash (zeros 8 ++ mHash ++ salt)) db) ((0xFF : Byte) >>> (8 * emLen - emBits)))) := by
  have hEL := emLength_eq rest h0
  rw [hb, he] at hEL
  have hle : emLen ≤ (n₀ :: rest).length := by rw [hEL, List.length_cons]; split <;> omega_arith
  simp only [encodeK, encode, hb, he, hdb, hlo]
  rw [ifn (by omega_arith)]
  simp only [Option.map_some]
  generalize hgen : H.hash (zeros 8 ++ mHash ++ salt) = h
  have hh : h.length = H.len := by rw [← hgen]; exact hH.2 _
  have hmk : (mgf1 G h db).length = db := mgf1_length hG _ _
  have hdbl : (zeros (emLen - salt.length - H.len - 2) ++ 0x01 :: salt).length = db := by
    simp only [List.length_append, zeros_length, List.length_cons]; omega_arith
  have hX : (clearTop (8 * emLen - emBits) (xorBytes (zeros (emLen - salt.length - H.len - 2) ++ 0x01 :: salt)
      (mgf1 G h db))).length = db := by
    rw [clearTop_length, xorBytes_length, hdbl, hmk, Nat.min_self]
  refine congrArg some (eq_range_map ?_ fun i hi => ?_)
  · simp only [List.length_append, zeros_length, hX, hh, List.length_cons, List.length_nil]
    simp only [List.length_cons] at hlo hle; omega_arith
  simp only [List.length_cons] at hi hlo hle
  simp only [emT, getD_app, List.length_append, zeros_length, hX, hh]
  have hlodb : lo + db + H.len + 1 = rest.length + 1 := by omega_arith
  by_cases h1 : i < lo
  · simp only [h1, ↓reduceIte]; exact zeros_getD _ _
  simp only [h1, ↓reduceIte]
  by_cases h2 : i - lo < db
  · have h2' : i - lo < db + H.len := by omega_arith
    simp only [h2, h2', ↓reduceIte, clearTop_getD]
    have hx : ∀ j < db, (xorBytes (zeros (emLen - salt.length - H.len - 2) ++ 1 :: salt) (mgf1 G h db)).getD j 0 =
        (if j < db - salt.length - 1 then 0 else if j = db - salt.length - 1 then 1
          else salt.getD (j - (db - salt.length)) 0) ^^^ (mgf1 G h db).getD j 0 := fun j hj => by
      rw [xorBytes_getD (by rw [hdbl]; exact hj) (by rw [hmk]; exact hj), db_getD,
        show emLen - salt.length - H.len - 2 = db - salt.length - 1 by omega_arith,
        show j - (db - salt.length - 1) - 1 = j - (db - salt.length) by omega_arith]
    by_cases h3 : i - lo = 0
    · simp only [h3, ↓reduceIte]; rw [hx 0 (by omega_arith)]
    · simp only [h3, ↓reduceIte]; rw [hx _ h2]
  · simp only [h2, ↓reduceIte]
    by_cases h4 : i - lo < db + H.len
    · simp only [h4, ↓reduceIte]
    · simp only [h4, ↓reduceIte]
      rw [show i - lo - (db + H.len) = 0 by omega_arith]; rfl

theorem sign_long₂ {nB : List Byte} (eB pB qB dPB dQB qInvB mHash salt : List Byte)
    (h : emLength (bitLength (Rsa.os2ip nB) - 1) < H.len + salt.length + 2) :
    sign H G nB eB pB qB dPB dQB qInvB mHash salt = .invalid := by
  simp only [sign, encodeK, encode]
  rw [ifp (Or.inr h)]
  rfl

theorem sign_eq₂ (hH : Valid H) (hG : Valid G) {n₀ : Byte} {rest eB pB qB dPB dQB qInvB mHash salt : List Byte}
    (h0 : n₀ ≠ 0) (hm : mHash.length = H.len) {emBits emLen lo db : Nat}
    (hb : bitLength (Rsa.os2ip (n₀ :: rest)) - 1 = emBits) (he : emLength emBits = emLen)
    (hlo : (n₀ :: rest).length - emLen = lo) (hdb : emLen - H.len - 1 = db)
    (hfit : H.len + salt.length + 2 ≤ emLen) :
    sign H G (n₀ :: rest) eB pB qB dPB dQB qInvB mHash salt =
      Rsa.privateChecked (n₀ :: rest) eB ((List.range (n₀ :: rest).length).map
        (emT lo db salt.length salt (H.hash (zeros 8 ++ mHash ++ salt))
          (Mgf1.mgf1 G (H.hash (zeros 8 ++ mHash ++ salt)) db) ((0xFF : Byte) >>> (8 * emLen - emBits))))
        pB qB dPB dQB qInvB := by
  simp only [sign, encodeK_eq₂ H G hH hG h0 hm hb he hlo hdb hfit]

end VG.Proof.RsaPss

namespace VG.Proof.RsaPss.RISCV64.Sg

open VG VG.RISCV64
open VG.Proof.RsaPss.RISCV64 (cmB byte_ok)

/-- The digest and the salt, from the entry state. -/
abbrev digB (D : Nat) (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 8) D
abbrev saltB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 10) (stackArg s 11).toNat

variable (H G : Spec.Mgf1.Hash)

/-- The private operation on `em`, with the entry's key. -/
def privOut (s : State) (em : List Byte) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) em
    (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .a7).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .a7).toNat)

/-- The outcome `signContract.post` asks for. -/
def signOut (s : State) : Spec.Rsa.Outcome :=
  Spec.RsaPss.sign H G (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .a7).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .a7).toNat)
    (digB H.len s) (saltB s)

/-- `H = Hash(0⁸ ‖ mHash ‖ salt)`. -/
abbrev hS (s : State) : List Byte := H.hash (Spec.RsaPss.zeros 8 ++ digB H.len s ++ saltB s)

/-- `dbLen`. -/
abbrev dbS (s : State) : Nat := kk s - loN s - H.len - 1

/-- The mask of `maskedDB`'s first byte, as a byte. -/
abbrev cS (s : State) : Byte := (cmB (s.mem (s.gpr .a2))).setWidth 8

/-- The encoding, as `k` bytes. -/
def encEm (s : State) : List Byte :=
  (List.range (kk s)).map (RsaPss.emT (loN s) (dbS H s) (stackArg s 11).toNat (saltB s) (hS H s)
    (Spec.Mgf1.mgf1 G (hS H s) (dbS H s)) (cS s))

theorem bytesAt_cons (m : Mem) (p : Addr) {k : Nat} (hk : 1 ≤ k) :
    Spec.Rsa.bytesAt m p k = m p :: Spec.Rsa.bytesAt m (p + 1) (k - 1) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Spec.Rsa.bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_sub_cancel]
  refine List.cons_eq_cons.mpr ⟨by simp, List.map_congr_left fun i _ => ?_⟩
  simp only [Function.comp, BitVec.add_assoc]
  rw [show (1 : Addr) + BitVec.ofNat 64 i = BitVec.ofNat 64 (i + 1) by
    rw [BitVec.add_comm, ← BitVec.ofNat_add_ofNat]; rfl]

theorem signOut_zero {s : State} (hk : 1 ≤ kk s) (h0 : s.mem (s.gpr .a2) = 0) : signOut H G s = .invalid := by
  unfold signOut
  rw [bytesAt_cons _ _ hk, h0]
  exact RsaPss.sign_zero₂ G H ..

theorem emLen_eq {s : State} (hk : 1 ≤ kk s) (h0 : s.mem (s.gpr .a2) ≠ 0) :
    Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip
      (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (kk s))) - 1) = kk s - loN s := by
  rw [bytesAt_cons _ _ hk, RsaPss.emLength_eq _ h0, VG.Proof.RsaPkcs1Sig.bytesAt_length]
  unfold loN
  split <;> omega

theorem signOut_long {s : State} (hk : 1 ≤ kk s) (h0 : s.mem (s.gpr .a2) ≠ 0)
    (h : kk s - loN s < H.len + (stackArg s 11).toNat + 2) : signOut H G s = .invalid := by
  unfold signOut
  refine RsaPss.sign_long₂ H G _ _ _ _ _ _ _ _ ?_
  rw [emLen_eq hk h0, VG.Proof.RsaPkcs1Sig.bytesAt_length]
  exact h

theorem cS_eq {s : State} (h0 : s.mem (s.gpr .a2) ≠ 0) :
    cS s = if (s.mem (s.gpr .a2)).toNat = 1 then 0xFF
      else BitVec.ofNat 8 (2 ^ Nat.log2 (s.mem (s.gpr .a2)).toNat - 1) := by
  have hn : (s.mem (s.gpr .a2)).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
  have := (byte_ok _ (s.mem (s.gpr .a2)).isLt hn).2
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  unfold cS
  rw [this]
  split
  · rfl
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    exact Nat.mod_mod_of_dvd _ (by decide)

theorem signOut_eq (hH : Proof.Mgf1.Valid H) (hG : Proof.Mgf1.Valid G) {s : State} (hk : 1 ≤ kk s)
    (h0 : s.mem (s.gpr .a2) ≠ 0) (hfit : H.len + (stackArg s 11).toNat + 2 ≤ kk s - loN s) :
    signOut H G s = privOut s (encEm H G s) := by
  have hel := emLen_eq hk h0
  have hc := RsaPss.mask_eq (Spec.Rsa.bytesAt s.mem (s.gpr .a2 + 1) (kk s - 1)) h0
  unfold signOut privOut encEm
  generalize hnB : Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat = nB at hel ⊢
  rw [bytesAt_cons _ _ hk] at hnB
  subst hnB
  rw [RsaPss.sign_eq₂ H G hH hG h0 (lo := loN s) (db := dbS H s)
    (VG.Proof.RsaPkcs1Sig.bytesAt_length _ _ _) rfl hel
    (by rw [List.length_cons, VG.Proof.RsaPkcs1Sig.bytesAt_length]; unfold loN; split <;> omega) rfl
    (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length]; exact hfit)]
  rw [hel] at hc
  rw [hc, ← cS_eq h0]
  simp only [List.length_cons, VG.Proof.RsaPkcs1Sig.bytesAt_length]
  rw [Nat.sub_add_cancel hk]

end VG.Proof.RsaPss.RISCV64.Sg
