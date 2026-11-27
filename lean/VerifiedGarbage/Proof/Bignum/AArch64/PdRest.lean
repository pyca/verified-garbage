module

import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.R2
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.ModArith
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Bignum.AArch64.WordIO
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.ByteDigits
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Bignum.AArch64.WordIOStore`, which this module and modules that import it used -/

section

/-!
# Words into big-endian bytes, a word at a time, on AArch64

`storeWords` writes the `w` words of an array, and'ed with a mask `x15`, as
the `k = 8 w` bytes ending at `out + k`: after `j` words, the last `8 j`
bytes hold bytes `0, …, 8 j - 1` of the masked number (`SWInv`). `storeW`
takes it or `storeBE` by `k mod 8` (`storeW_ok`, with `storeBE_ok`'s
statement but for the bytes' one region).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WordIO

open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.ByteDigits
open VG.Proof.MlKem.AArch64 (Keep count_loop eval_zero)

theorem masked_digit (m : Mem) (B : Addr) (ed w : Nat) {j : Nat} (hj : j < w) (c : Bool) :
    word m B (ed + 8 * j) &&& mask c = BitVec.ofNat 64 ((if c then wv m B ed w else 0) / 256 ^ (8 * j)) := by
  apply BitVec.eq_of_toNat_eq
  rw [and_mask_toNat, word_of_wv _ _ _ _ hj, BitVec.toNat_ofNat, pow256]
  cases c <;> simp

/-- After `j` words of `storeWords` from `s`. -/
structure SWInv (s : State) (B out : Addr) (ed k Y : Nat) (j : Nat) (t : State) : Prop where
  wr : t.wr = s.wr
  rd : t.rd = s.rd
  keep : Keep [.x1, .x3, .x5, .x9] s t
  x1 : t.gpr .x1 = out + BitVec.ofNat 64 (k - 8 * j)
  x5 : t.gpr .x5 = off B (ed + 8 * j)
  x9 : t.gpr .x9 = BitVec.ofNat 64 (k - 8 * j)
  bytes : ∀ z < 8 * j, t.mem (out + BitVec.ofNat 64 (k - 1 - z)) = BitVec.ofNat 8 (Y / 256 ^ z)
  frame : ∀ x, (∀ z < 8 * j, x ≠ out + BitVec.ofNat 64 (k - 1 - z)) → t.mem x = s.mem x

theorem storeWordsStep_ok {s t : State} {B out : Addr} {Z ed k w : Nat} {c : Bool}
    (hs : Scr s B Z) (h15 : s.gpr .x15 = mask c) (hk : k = 8 * w) (hk' : k < 2 ^ 31) (hed : ed + 8 * w ≤ Z)
    (hout : InRegions s.wr out k) (hsep : ∀ i < k, Z ≤ ofs B (out + BitVec.ofNat 64 i))
    {j : Nat} (hj : j < w) (h : SWInv s B out ed k (if c then wv s.mem B ed w else 0) j t) :
    WP isa (.block [ld .x3 .x5, .logic .and .x .x3 .x3 .x15, .rev .x3 .x3, .subImm .x .x1 .x1 8, st .x3 .x1, next .x5,
        .subImm .x .x9 .x9 8]) t fun u =>
      SWInv s B out ed k (if c then wv s.mem B ed w else 0) (j + 1) u ∧ ((u.gpr .x9).toNat ≠ 0 ↔ j + 1 ≠ w) := by
  have hn := hs.nowrap
  have hwd : word t.mem B (ed + 8 * j) = word s.mem B (ed + 8 * j) := by
    apply Mem.readW_congr
    intro b hb
    apply h.frame
    intro z hz he
    have hsep' := hsep (k - 1 - z) (by omega_using [hk, hj])
    rw [← he, ofs_off B (by omega_using [hed, hj, hn, hb])] at hsep'
    omega_using [hed, hj, hb, hsep']
  have hread : InRegions (t.rd ++ t.wr) (off B (ed + 8 * j)) 8 := by
    rw [h.rd, h.wr]; exact hs.ld (by omega_using [hed, hj])
  have hwrite : InRegions t.wr (out + BitVec.ofNat 64 (k - 8 * (j + 1))) 8 := by
    rw [h.wr]; exact VG.CallLay.inRegions_sub hout (by omega_using [hk, hj]) (by omega_using [hk'])
  have hx1 : out + BitVec.ofNat 64 (k - 8 * j) - BitVec.ofNat 64 8 = out + BitVec.ofNat 64 (k - 8 * (j + 1)) := by
    rw [VG.Offset.add_ofNat_sub out (by omega_using [hk, hj])]; congr 2
  have hx5 : off B (ed + 8 * j) + BitVec.ofNat 64 8 = off B (ed + 8 * (j + 1)) := by
    rw [off_add, show ed + 8 * j + 8 = ed + 8 * (j + 1) by omega_using []]
  have hx9 : BitVec.ofNat 64 (k - 8 * j) - BitVec.ofNat 64 8 = BitVec.ofNat 64 (k - 8 * (j + 1)) := by
    rw [VG.Offset.ofNat_sub_ofNat (by omega_using [hk, hj])]; congr 1
  have h15' : t.gpr .x15 = mask c := (h.keep.gpr .x15 (by decide)).trans h15
  refine WP.mono (WP.keep [.x1, .x3, .x5, .x9] (Q := fun u =>
    u.mem = t.mem.writeW (out + BitVec.ofNat 64 (k - 8 * (j + 1)))
      (rev64 (BitVec.ofNat 64 ((if c then wv s.mem B ed w else 0) / 256 ^ (8 * j)))) ∧
    u.gpr .x1 = out + BitVec.ofNat 64 (k - 8 * (j + 1)) ∧ u.gpr .x5 = off B (ed + 8 * (j + 1)) ∧
    u.gpr .x9 = BitVec.ofNat 64 (k - 8 * (j + 1))) ?_ (by decide) (by decide) (by decide +kernel))
    fun u ⟨⟨hm, h1, h5, h9⟩, ku⟩ => ?_
  · brun [h.x1, h.x5, h.x9, hread, exec_rev, h15', hwd, masked_digit _ _ _ _ hj c, hx1, hx5, hx9, hwrite]
  · refine ⟨⟨ku.wr.trans h.wr, ku.rd.trans h.rd, (h.keep.trans ku).mono (by decide), h1, h5, h9, fun z hz => ?_,
      fun x hx => ?_⟩, ?_⟩
    · rw [hm]
      have hd : ((out + BitVec.ofNat 64 (k - 1 - z)) - (out + BitVec.ofNat 64 (k - 8 * (j + 1)))).toNat =
          k - 1 - z - (k - 8 * (j + 1)) := VG.Offset.sub_toNat out (by omega_using [hz]) (by omega_using [hk'])
      change (if ((out + BitVec.ofNat 64 (k - 1 - z)) - (out + BitVec.ofNat 64 (k - 8 * (j + 1)))).toNat < 8 then
        (rev64 (BitVec.ofNat 64 ((if c then wv s.mem B ed w else 0) / 256 ^ (8 * j)))).extractLsb'
          (8 * ((out + BitVec.ofNat 64 (k - 1 - z)) - (out + BitVec.ofNat 64 (k - 8 * (j + 1)))).toNat) 8
        else t.mem (out + BitVec.ofNat 64 (k - 1 - z))) = _
      rw [hd]
      by_cases hzold : z < 8 * j
      · rw [ite_eq_right (by omega_using [hk, hj, hzold])]; exact h.bytes z hzold
      · rw [ite_eq_left (by omega_using [hzold]), rev64_byte _ (by omega_using [hzold]), extract_nat _ (by omega_using []), Nat.div_div_eq_div_mul,
          ← Nat.pow_add]
        congr 3; omega_using [hk, hj, hz, hzold]
    · rw [hm]
      apply Eq.trans (Mem.write_apply ?_) (h.frame x (fun z hz => hx z (by omega_using [hz])))
      intro hin
      let b := (x - (out + BitVec.ofNat 64 (k - 8 * (j + 1)))).toNat
      have hb : b < 8 := hin
      have he : x = out + BitVec.ofNat 64 (k - 8 * (j + 1) + b) := by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        change x = (out + BitVec.ofNat 64 (k - 8 * (j + 1))) + BitVec.ofNat 64 b
        simp only [b, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        rw [BitVec.add_comm (out + BitVec.ofNat 64 (k - 8 * (j + 1))) _, BitVec.sub_add_cancel]
      apply hx (8 * (j + 1) - 1 - b) (by omega_using [])
      rw [he]
      congr 2; omega_using [hk, hj, hin]
    · rw [h9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hk'])]
      omega_using [hk, hj]

theorem storeWords_ok {s : State} {B out : Addr} {Z ed k w : Nat} {c : Bool}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B ed) (h1 : s.gpr .x1 = out + BitVec.ofNat 64 k)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 k) (h15 : s.gpr .x15 = mask c)
    (hk : k = 8 * w) (hk1 : 0 < k) (hk' : k < 2 ^ 31) (hed : ed + 8 * w ≤ Z)
    (hout : InRegions s.wr out k) (hsep : ∀ i < k, Z ≤ ofs B (out + BitVec.ofNat 64 i)) :
    WP isa storeWords s fun t =>
      (List.range k).map (fun i => t.mem (out + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B ed w else 0) k ∧
      (∀ x, (∀ j < k, x ≠ out + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧
      t.wr = s.wr ∧ t.rd = s.rd ∧ Keep [.x1, .x3, .x5, .x9] s t := by
  unfold storeWords
  refine WP.seq (WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = off B ed ∧ t.mem = s.mem)
    (by brun [h8]) (by decide) (by decide) (by decide +kernel)) fun a ⟨⟨h5, hm⟩, ka⟩ => ?_)
  have hs' := hs.congr ka.wr
  have hm' : wv a.mem B ed w = wv s.mem B ed w := by rw [hm]
  have h0 : SWInv a B out ed k (if c then wv s.mem B ed w else 0) 0 a :=
    ⟨rfl, rfl, Keep.refl _ _, by rw [(ka.gpr .x1 (by decide)).trans h1, Nat.mul_zero, Nat.sub_zero],
      by rw [h5, Nat.mul_zero, Nat.add_zero], by rw [(ka.gpr .x9 (by decide)).trans h9, Nat.mul_zero, Nat.sub_zero],
      fun z hz => absurd hz (by omega_using []), fun _ _ => rfl⟩
  have hr : InRegions a.wr out k := by rw [ka.wr]; exact hout
  refine WP.mono (count_loop (cr := .x9) (n := w) (by omega)
    (SWInv a B out ed k (if c then wv s.mem B ed w else 0))
    (fun j hj t h => by
      rw [← hm'] at h ⊢
      exact storeWordsStep_ok hs' ((ka.gpr .x15 (by decide)).trans h15) hk hk' hed hr hsep hj h) h0)
    fun t h => ⟨?_, ?_, h.wr.trans ka.wr, h.rd.trans ka.rd, (ka.trans h.keep).mono (by decide)⟩
  · apply List.ext_getElem (by simp [Spec.Rsa.i2osp])
    intro i hi _
    have hik : i < k := by simpa using hi
    simp only [List.getElem_map, List.getElem_range, Spec.Rsa.i2osp]
    have hb := h.bytes (k - 1 - i) (by omega_using [hk, hk1])
    rwa [show k - 1 - (k - 1 - i) = i by omega_using [hik]] at hb
  · intro x hx
    rw [h.frame x (fun i hi => hx _ (by omega_using [hk1])), hm]

/-- `storeW`: `storeBE` (`storeBE_ok`), for bytes in one region. -/
theorem storeW_ok {s : State} {B : Addr} {Z ed k w : Nat} {out : Addr} {c : Bool}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B ed) (h1 : s.gpr .x1 = out + BitVec.ofNat 64 k)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 k) (h15 : s.gpr .x15 = mask c) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hw : w = (k + 7) / 8) (hed : ed + 8 * w ≤ Z)
    (hout : InRegions s.wr out k)
    (hsep : ∀ j < k, Z ≤ ofs B (out + BitVec.ofNat 64 j)) :
    WP isa storeW s fun t =>
      (List.range k).map (fun i => t.mem (out + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B ed w else 0) k ∧
      (∀ x, (∀ j < k, x ≠ out + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧
      t.wr = s.wr ∧ t.rd = s.rd ∧ Keep [.x1, .x2, .x3, .x5, .x6, .x9] s t := by
  unfold storeW
  refine WP.seq (WP.mono (WP.keep [.x2, .x6] (Q := fun a => a.gpr .x2 = BitVec.ofNat 64 k &&& (BitVec.ofNat 16 7).setWidth 64 ∧
      a.mem = s.mem) (by brun [h9]) (by decide) (by decide) (by decide +kernel)) fun a ⟨⟨h2, hm⟩, ka⟩ => ?_)
  have hs' := hs.congr ka.wr
  have hr : InRegions a.wr out k := by rw [ka.wr]; exact hout
  have a1 := (ka.gpr .x1 (by decide)).trans h1
  have a8 := (ka.gpr .x8 (by decide)).trans h8
  have a9 := (ka.gpr .x9 (by decide)).trans h9
  have a15 := (ka.gpr .x15 (by decide)).trans h15
  refine WP.ite (decide (k % 8 = 0)) (by rw [eval_zero, h2, and7_zero (by omega_using [hk'])]) ?_ ?_
  · intro h8'
    have h8' := of_decide_eq_true h8'
    refine WP.mono (storeWords_ok hs' a8 a1 a9 a15 (w := w) (by omega_using [hw, h8']) (by omega_using [hk1]) hk' hed hr hsep)
      fun t ⟨hv, ho, hw', hr', kt⟩ => ⟨by simpa only [hm] using hv, fun x hx => (ho x hx).trans (congrFun hm x),
        hw'.trans ka.wr, hr'.trans ka.rd, (ka.trans kt).mono (by decide)⟩
  · intro _
    refine WP.mono (storeBE_ok hs' a8 a1 a9 a15 hk1 hk' hw hed
      (fun i hi => VG.CallLay.inRegions_sub hr (by omega_using [hi]) (by omega_using [hk'])) hsep)
      fun t ⟨hv, ho, hw', hr', kt⟩ => ⟨by simpa only [hm] using hv, fun x hx => (ho x hx).trans (congrFun hm x),
        hw'.trans ka.wr, hr'.trans ka.rd, (ka.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.AArch64.WordIO

end

end

/-!
# `vg_rsa_public_precomputed` on AArch64: the computation

The input, the mask of `input < m`, `-m⁻¹` and the number 1 (`pdSetup_ok`),
for any values of `m` and `R² mod m` that pass the checks.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Precomputed
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

variable {M : Mont}

/-- What the public-key operation leaves: `i2osp r k` to `out`, the flag `c`
returned, and memory outside the working space and `out` unchanged. -/
structure MainPost (s t : State) (B : Addr) (Z k : Nat) (op : Addr) (r : Nat) (c : Bool) : Prop where
  bytes : (List.range k).map (fun i => t.mem (op + BitVec.ofNat 64 i)) = Spec.Rsa.i2osp r k
  x0 : t.gpr .x0 = BitVec.ofNat 64 c.toNat
  frame : ∀ x, Z ≤ ofs B x → (∀ j < k, x ≠ op + BitVec.ofNat 64 j) → t.mem x = s.mem x
  keep : Keep (.x0 :: mmRegs) s t

/-- What `rest` starts from: the header `entry` leaves, `m` and `R² mod m`
(here any `R < N`) in their arrays, as the checks accepted them. -/
structure PdPre (s : State) (B : Addr) (Z k : Nat) (op ep ip : Addr) (L : Nat) (eb xb : List Byte) (N R : Nat) :
    Prop where
  scr : Scr s B Z
  x0 : s.gpr .x0 = B
  z : slot ((k + 7) / 8) 8 ≤ Z
  k1 : 64 ≤ k
  k2 : k ≤ 1024
  hO : word s.mem B (8 * sOut) = op
  hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k
  hE : word s.mem B (8 * sE) = ep
  hL : word s.mem B (8 * sElen) = BitVec.ofNat 64 L
  hIn : word s.mem B (8 * sIn) = ip
  hW : word s.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8)
  hb : ∀ j < 8, word s.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j)
  n : wv s.mem B (slot ((k + 7) / 8) aN) ((k + 7) / 8) = N
  r : wv s.mem B (slot ((k + 7) / 8) aR2) ((k + 7) / 8) = R
  odd : N % 2 = 1
  n1 : 1 < N
  rlt : R < N
  x : Src s B Z ip xb
  xspan : InRegions (s.rd ++ s.wr) ip k
  e : Src s B Z ep eb
  xl : xb.length = k
  el : eb.length = L
  L1 : 1 ≤ L
  L2 : L ≤ k
  out : InRegions s.wr op k
  outSep : ∀ j < k, Z ≤ ofs B (op + BitVec.ofNat 64 j)

/-- `x` with `x R ≡ X`, for `R` invertible modulo `N > 1`. -/
theorem exists_mont {R N : Nat} (hR : Nat.Coprime R N) (hN1 : 1 < N) (X : Nat) :
    ∃ x, X % N = x * R % N := by
  obtain ⟨x, -, hx⟩ := ModArith.exists_mul_mod_eq hR (by omega_using [hN1]) X
  exact ⟨x, hx.symm⟩

/-- The input into its array. -/
theorem pdIn_ok {s : State} {B : Addr} {Z k : Nat} {ip : Addr} {xb : List Byte} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 9 ≤ k) (hk : k < 2 ^ 31)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hIn : word s.mem B (8 * sIn) = ip)
    (hb : ∀ j < 8, word s.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j)) (hx : Src s B Z ip xb)
    (hxspan : InRegions (s.rd ++ s.wr) ip k) (hxl : xb.length = k) :
    WP isa (.seq (.block [ldh .x1 sIn, ldh .x2 sK, ldh .x8 (sArr aX)]) loadW) s fun t =>
      wv t.mem B (slot ((k + 7) / 8) aX) ((k + 7) / 8) = Spec.Rsa.os2ip xb ∧
      Arrays B ((k + 7) / 8) [aX] s.mem t.mem ∧ Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x8] s t := by
  have hn := hs.nowrap
  obtain h8 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  obtain h0' := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  have eK : sK = 18 := rfl
  have eIn : sIn = 21 := rfl
  have eAX : sArr aX = 9 := rfl
  refine WP.seq (WP.mono (WP.keep [.x1, .x2, .x8] (Q := fun t => t.gpr .x1 = ip ∧
      t.gpr .x2 = BitVec.ofNat 64 k ∧ t.gpr .x8 = off B (slot ((k + 7) / 8) aX) ∧ t.mem = s.mem) (by
    brun [h0, hdr_enc (show sIn < 32 by decide), hdr_enc (show sK < 32 by decide),
      hdr_enc (show sArr aX < 32 by decide), hs.ld (d := 8 * sIn) (by omega_using [hZ, h8, h0', eIn]),
          hs.ld (d := 8 * sK) (by omega_using [hZ, h8, h0', eK]),
      hs.ld (d := 8 * sArr aX) (by omega_using [hZ, h8, h0', eAX]), hIn, hK,
          hb aX (by decide)]) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨h1, h2, h8', hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (loadArrW_ok (hs.congr k₁.wr) (by decide) hZ
    (hx.congrK (by rw [hm₁]; exact InScr.refl _ _ _) k₁) (by rw [k₁.rd, k₁.wr]; exact hxspan) hxl
    (by omega_using [hk1]) hk h1 h2 h8')
    fun t ⟨hv, ha, k₂⟩ => ⟨hv, by rw [hm₁] at ha; exact ha, (k₁.trans k₂).mono (by decide)⟩

/-- After the setup: the modulus `N`, `-N⁻¹` in the header, the input `X`,
the number 1, and the mask of `X < N`. -/
structure SetupOut (t : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N X : Nat) : Prop where
  good : Good t B Z w minv
  n : wv t.mem B (slot w aN) w = N
  inv : ((word t.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0
  x : wv t.mem B (slot w aX) w = X
  one : wv t.mem B (slot w aOne) w = 1
  mask : word t.mem B (8 * sMask) = mask (decide (X < N))

theorem csel_mask (c : Bool) :
    (if (!c) = true then (0 : BitVec 64) else 0 - BitVec.ofNat 64 1) = mask c := by
  cases c <;> rfl

/-- The steps after the input: the mask of `X < N`, `-N⁻¹` and the number 1. -/
def setupSteps : List (Prog isa) := [
  .block [ldh .x12 sW, ldh .x16 (sArr aX), ldh .x17 (sArr aN), movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7],
  cmpLoop,
  .block ([.subImm .x .x4 .x7 1, .csel .x .x15 .x7 .x4, sth .x15 sMask, ldh .x8 (sArr aN), ld .x3 .x8] ++ minv ++
    [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0]),
  setWord aOne]

/-- The mask of `X < N`, `-N⁻¹` and the number 1. -/
theorem pdSetup_ok {s : State} {B : Addr} {Z w : Nat} {N X : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hW : word s.mem B (8 * sW) = BitVec.ofNat 64 w)
    (hb : ∀ j < 8, word s.mem B (8 * sArr j) = off B (slot w j))
    (hN : wv s.mem B (slot w aN) w = N) (hX : wv s.mem B (slot w aX) w = X) (hodd : N % 2 = 1) :
    WP isa (seqs setupSteps) s fun t => ∃ minv, SetupOut t B Z w minv N X ∧
      Frm B [(8 * sMinv, 8), (8 * sMask, 8), (slot w aOne, 8 * (w + 2))] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  obtain h0' := slot_le (w := w) (show 0 < 8 by decide)
  obtain h8 := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have eW : sW = 6 := rfl
  have eM : sMinv = 7 := rfl
  have eK : sMask = 22 := rfl
  have eAX : sArr aX = 9 := rfl
  have eAN : sArr aN = 8 := rfl
  obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_using [hZ, h0', h8, hi])
  unfold setupSteps
  refine WP.seq (WP.mono (WP.keep [.x3, .x7, .x12, .x14, .x16, .x17] (Q := fun t =>
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x16 = off B (slot w aX) ∧ t.gpr .x17 = off B (slot w aN) ∧
      t.gpr .x7 = 0 ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧ t.c = true ∧ t.mem = s.mem) (by
    brun [h0, hdr_enc (show sW < 32 by decide), hdr_enc (show sArr aX < 32 by decide),
      hdr_enc (show sArr aN < 32 by decide), hl sW (by omega_arith), hl (sArr aX) (by omega_using [eAX]),
          hl (sArr aN) (by omega_using [eAN]),
      hW, hb aX (by decide), hb aN (by decide)]) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨h12, h16, h17, h7, h14, hc₁, hm₁⟩, k₁⟩ => ?_)
  obtain hs₁ := hs.congr k₁.wr
  refine WP.seq (WP.mono (cmpLoop_ok hs₁ h16 h17 h14 hc₁ (by omega_using [hw]) hw'
    (by have := slot_le (w := w) (show aX < 8 by decide); omega_using [hZ, this])
    (by have := slot_le (w := w) (show aN < 8 by decide); omega_using [hZ, this])) fun t₂ ⟨hc₂, hm₂, k₂⟩ => ?_)
  rw [hm₁, hN, hX] at hc₂
  obtain hs₂ := hs₁.congr k₂.wr
  obtain hm₂' : t₂.mem = s.mem := hm₂.trans hm₁
  obtain h0₂ : t₂.gpr .x0 = B := (k₂.gpr .x0 (by decide)).trans ((k₁.gpr .x0 (by decide)).trans h0)
  -- `-N⁻¹`.
  obtain hodd₀ : (word s.mem B (slot w aN)).toNat % 2 = 1 := by
    rw [← wv_mod64 _ _ _ (show 1 ≤ w by omega_using [hw]), Nat.mod_mod_of_dvd _ (by decide), hN, hodd]
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  obtain hst : ∀ i < 32, InRegions t₂.wr (off B (8 * i)) 8 := fun i hi => hs₂.st (by omega_using [hZ, h0', h8, hi])
  obtain hsN : (s.mem.writeW (off B (8 * sMask)) (mask (decide (X < N)))).readW (off B (8 * sArr aN)) 64 =
      off B (slot w aN) := by
    rw [← hb aN (by decide)]
    exact (writeW_outside _ B _ (by omega_using [eK])).word (by omega_using [eK, eAN]) (by omega_using [eAN])
  obtain hsN' : (s.mem.writeW (off B (8 * sMask)) (mask (decide (X < N)))).readW (off B (slot w aN)) 64 =
      word s.mem B (slot w aN) :=
    (writeW_outside _ B _ (by omega_using [eK])).word (by have := hdr_lt_slot w aN (show sMask < 32 by decide); omega_using [this])
      (by have := slot_le (w := w) (show aN < 8 by decide); omega_using [hZ, hn, this])
  refine WP.mono (WP.keep [.x3, .x4, .x8, .x15] (Q := fun t => t.gpr .x3 = word s.mem B (slot w aN) ∧
      t.mem = s.mem.writeW (off B (8 * sMask)) (mask (decide (X < N)))) (by
    brun [h0₂, (k₂.gpr .x7 (by decide)).trans h7, hc₂, hdr_enc (show sMask < 32 by decide),
      hdr_enc (show sArr aN < 32 by decide), hst sMask (by omega_using [eK]), hs₂.ld (d := 8 * sArr aN) (by omega_using [hZ, h0', h8, eAN]),
      hm₂', csel_mask, hsN, hsN', hs₂.ld (d := slot w aN) (by have := slot_le (w := w) (show aN < 8 by decide); omega_using [hZ, this])])
      (by decide) (by decide) (by decide +kernel))
    fun t₃ ⟨⟨h3₃, hm₃⟩, k₃⟩ => ?_
  refine WP.mono (minv_ok t₃ (by rw [h3₃]; exact hodd₀)) fun t₄ ⟨hinv, k₄, hm₄⟩ => ?_
  rw [h3₃] at hinv
  obtain hs₄ := (hs₂.congr k₃.wr).congr k₄.wr
  obtain h0₄ : t₄.gpr .x0 = B := (k₄.gpr .x0 (by decide)).trans ((k₃.gpr .x0 (by decide)).trans h0₂)
  obtain hW₄ : (t₄.mem.writeW (off B (8 * sMinv)) (t₄.gpr .x15)).readW (off B (8 * sW)) 64 = BitVec.ofNat 64 w := by
    rw [← hW]
    obtain e1 : (t₄.mem.writeW (off B (8 * sMinv)) (t₄.gpr .x15)).readW (off B (8 * sW)) 64 = word t₄.mem B (8 * sW) :=
      (writeW_outside _ B _ (d := 8 * sMinv) (by omega_using [eM])).word (d := 8 * sW) (by omega_using [eW, eM]) (by omega_using [eW])
    rw [e1, hm₄, hm₃]
    exact (writeW_outside _ B _ (d := 8 * sMask) (by omega_using [eK])).word (d := 8 * sW) (by omega_using [eW, eK]) (by omega_using [eW])
  refine WP.mono (WP.keep [.x9, .x12, .x13] (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x9 = 1 ∧
      t.gpr .x13 = BitVec.ofNat 64 0 ∧ t.mem = t₄.mem.writeW (off B (8 * sMinv)) (t₄.gpr .x15)) (by
    brun [h0₄, hdr_enc (show sMinv < 32 by decide), hdr_enc (show sW < 32 by decide),
      hs₄.st (d := 8 * sMinv) (by omega_using [hZ, h0', h8, eM]),
          hs₄.ld (d := 8 * sW) (by omega_using [hZ, h0', h8, eW]), hW₄]) (by decide) (by decide) (by decide +kernel))
    fun t₅ ⟨⟨h12₅, h9₅, h13₅, hm₅⟩, k₅⟩ => ?_
  obtain hs₅ := hs₄.congr k₅.wr
  obtain h0₅ : t₅.gpr .x0 = B := (k₅.gpr .x0 (by decide)).trans h0₄
  obtain hm₅' : t₅.mem = (s.mem.writeW (off B (8 * sMask)) (mask (decide (X < N)))).writeW (off B (8 * sMinv))
      (t₄.gpr .x15) := by rw [hm₅, hm₄, hm₃]
  obtain hwv : ∀ j < 8, wv t₅.mem B (slot w j) w = wv s.mem B (slot w j) w := fun j hj => by
    have := slot_le (w := w) hj
    rw [hm₅', (writeW_outside _ B _ (by omega_using [eM])).wv (by have := hdr_lt_slot w j (show sMinv < 32 by decide); omega_using [this])
      (by omega_using [hZ, hn, this]), (writeW_outside _ B _ (by omega_using [eK])).wv
      (by have := hdr_lt_slot w j (show sMask < 32 by decide); omega_using [this]) (by omega_arith)]
  obtain hw0 : word t₅.mem B (slot w aN) = word s.mem B (slot w aN) := by
    have := slot_le (w := w) (show aN < 8 by decide)
    rw [hm₅', (writeW_outside _ B _ (by omega_using [eM])).word
      (by have := hdr_lt_slot w aN (show sMinv < 32 by decide); omega_using [this]) (by omega_using [hZ, hn, this])]; exact hsN'
  obtain hhd : ∀ i < 32, i ≠ sMask → i ≠ sMinv → word t₅.mem B (8 * i) = word s.mem B (8 * i) := fun i hi h1 h2 => by
    rw [hm₅', hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h2), hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h1)]
  obtain hH : Hdr t₅.mem B w (t₄.gpr .x15) :=
    ⟨by rw [hhd sW (by decide) (by decide) (by decide)]; exact hW,
      by rw [hm₅', word_writeW_self],
      fun j hj => by rw [hhd (sArr j) (by unfold sArr; omega_using [hj]) (by unfold sArr sMask sFn; omega_using [hj])
        (by unfold sArr sMinv; omega_using [])]; exact hb j hj⟩
  refine WP.mono (setWord_ok hs₅ h0₅ hH hZ h12₅ hw' (o := aOne) (by decide) (i := 0) (by omega_using [hw]) h13₅)
    fun t ⟨hone, ho, k₆⟩ => ⟨t₄.gpr .x15, ?_, ?_, ?_⟩
  · have ha : Arrays B w [aOne] t₅.mem t.mem := Arrays.of_outside (List.mem_singleton_self _) ho
      (Nat.le_refl _) (Nat.le_refl _)
    obtain hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_using [hZ, hn]
    refine ⟨⟨hs₅.congr k₆.wr, (k₆.gpr .x0 (by decide)).trans h0₅, ha.hdr hH⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ha.wv_of_not_mem (by decide) (by decide) hn', hwv aN (by decide), hN]
    · rw [ha.word0_of_not_mem (by decide) (by decide) hn' (by omega_using [hw]), hw0]; exact hinv
    · rw [ha.wv_of_not_mem (by decide) (by decide) hn', hwv aX (by decide), hX]
    · rw [hone, h9₅]; rfl
    · rw [ha.hslot (by decide), hm₅', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm₅'] at ho
    exact ((Frm.of_outside (writeW_outside _ B _ (by omega_using [eK])) (by simp)).trans
      (Frm.of_outside (writeW_outside _ B _ (by omega_using [eM])) (by simp))).trans (Frm.of_outside ho (by simp))
  · exact (((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).mono (by decide)

/-! ## The result -/

theorem mask_and1 (c : Bool) : mask c &&& 1 = BitVec.ofNat 64 c.toNat := by
  cases c <;> decide

/-- A byte of the working space is not one of `out`'s. -/
theorem scr_ne_out {B out : Addr} {Z k : Nat} (hsep : ∀ j < k, Z ≤ ofs B (out + BitVec.ofNat 64 j))
    {d i : Nat} (hd : d + i < Z) (hZ : Z ≤ 2 ^ 64) :
    ∀ j < k, off B d + BitVec.ofNat 64 i ≠ out + BitVec.ofNat 64 j := by
  intro j hj he
  obtain h := hsep j hj
  rw [← he, ofs_off B (by omega_using [hd, hZ])] at h
  omega_using [hd, h]

/-- The steps of the result. -/
def outSteps : List (Prog isa) := [
  .block [ldh .x8 (sArr aY), ldh .x1 sOut, ldh .x9 sK, .add .x .x1 .x1 .x9, ldh .x15 sMask],
  storeW,
  .block [ldh .x0 sMask, movi .x3 1, .logic .and .x .x0 .x0 .x3]]

/-- The result: `i2osp (c ? Y : 0)` to `out`, and `c` returned. -/
theorem outPhase_ok {s : State} {B : Addr} {Z k : Nat} {minv : BitVec 64} {Y : Nat} {out : Addr} {c : Bool}
    (hg : Good s B Z ((k + 7) / 8) minv) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hY : wv s.mem B (slot ((k + 7) / 8) aY) ((k + 7) / 8) = Y)
    (hO : word s.mem B (8 * sOut) = out) (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hM : word s.mem B (8 * sMask) = mask c)
    (hout : InRegions s.wr out k)
    (hsep : ∀ j < k, Z ≤ ofs B (out + BitVec.ofNat 64 j)) :
    WP isa (seqs outSteps) s fun t =>
      (List.range k).map (fun i => t.mem (out + BitVec.ofNat 64 i)) = Spec.Rsa.i2osp (if c then Y else 0) k ∧
      t.gpr .x0 = BitVec.ofNat 64 c.toNat ∧
      (∀ x, (∀ j < k, x ≠ out + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧
      Keep (.x0 :: mmRegs) s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  obtain h0 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  obtain h0' := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_using [hZ, h0, h0', hi])
  unfold outSteps
  refine WP.seq (WP.mono (WP.keep [.x1, .x8, .x9, .x15] (Q := fun t =>
      t.gpr .x8 = off B (slot ((k + 7) / 8) aY) ∧ t.gpr .x1 = out + BitVec.ofNat 64 k ∧
      t.gpr .x9 = BitVec.ofNat 64 k ∧ t.gpr .x15 = mask c ∧ t.mem = s.mem) (by
    brun [hg.x0, hdr_enc (show sArr aY < 32 by decide), hdr_enc (show sOut < 32 by decide),
      hdr_enc (show sK < 32 by decide), hdr_enc (show sMask < 32 by decide),
      hl (sArr aY) (by decide), hl sOut (by decide), hl sK (by decide),
      hl sMask (by decide), hg.hdr.harr aY (by decide), hO, hK, hM]) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨h8, h1, h9, h15, hm₁⟩, k₁⟩ => ?_)
  obtain hs₁ := hs.congr k₁.wr
  refine WP.seq (WP.mono (WordIO.storeW_ok hs₁ h8 h1 h9 h15 hk1 hk' rfl
    (by have := slot_le (w := (k + 7) / 8) (show aY < 8 by decide); omega_using [hZ, this])
    (by rw [k₁.wr]; exact hout) hsep) fun t₂ ⟨hb₂, hf₂, hwr₂, hrd₂, k₂⟩ => ?_)
  rw [hm₁, hY] at hb₂
  obtain hw₂ : ∀ i < 32, word t₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    apply Mem.readW_congr
    intro b hb
    rw [hf₂ _ (scr_ne_out hsep (d := 8 * i) (i := b) (by omega_using [hZ, h0, h0', hi, hb]) (by omega_using [hn])), hm₁]
  obtain hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off B (8 * i)) 8 := fun i hi => by
    rw [hrd₂, hwr₂, k₁.rd, k₁.wr]; exact hl i hi
  obtain h0₂ : t₂.gpr .x0 = B := (k₂.gpr .x0 (by decide)).trans ((k₁.gpr .x0 (by decide)).trans hg.x0)
  refine WP.mono (WP.keep [.x0, .x3] (Q := fun t => t.gpr .x0 = BitVec.ofNat 64 c.toNat ∧ t.mem = t₂.mem) (by
    brun [h0₂, hdr_enc (show sMask < 32 by decide), hl₂ sMask (by decide), hw₂ sMask (by decide), hM,
      show BitVec.setWidth 64 (1#16) = (1 : BitVec 64) from rfl, mask_and1])
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨hx, hm⟩, k₃⟩ => ⟨by rw [hm]; exact hb₂, hx,
      fun x hx' => by rw [hm, hf₂ x hx', hm₁], ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-! ## `rest` -/

/-- The input, the mask, `-m⁻¹` and 1. -/
theorem pdSetupAll_ok {s : State} {B : Addr} {Z k : Nat} {op ep ip : Addr} {L : Nat} {eb xb : List Byte} {N R : Nat}
    (h : PdPre s B Z k op ep ip L eb xb N R) :
    WP isa (seqs (([.block [ldh .x1 sIn, ldh .x2 sK, ldh .x8 (sArr aX)], loadW] : List (Prog isa)) ++ setupSteps)) s fun t => ∃ minv,
      SetupOut t B Z ((k + 7) / 8) minv N (Spec.Rsa.os2ip xb) ∧ Frm B (pdAll ((k + 7) / 8)) s.mem t.mem ∧
      Keep mmRegs s t ∧ wv t.mem B (slot ((k + 7) / 8) aR2) ((k + 7) / 8) = R := by
  have hk1 := h.k1
  have hk2 := h.k2
  have hZ := h.z
  have hs := h.scr
  have hn := hs.nowrap
  obtain hn' : B.toNat + slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega_using [hZ, hn]
  refine wp_seqs_append (by simp) (by simp [setupSteps])
    (WP.mono (pdIn_ok hs h.x0 hZ (by omega_using [hk1]) (by omega_using [hk2]) h.hK h.hIn h.hb h.x h.xspan h.xl) fun t₁ ⟨hX₁, ha₁, k₁⟩ => ?_)
  obtain f₁ : Frm B (pdAll ((k + 7) / 8)) s.mem t₁.mem := Frm.of_arrays ha₁ (by simp [pdAll])
  refine WP.mono (pdSetup_ok (hs.congr k₁.wr) ((k₁.gpr .x0 (by decide)).trans h.x0) hZ (by omega_arith) (by omega_using [hk2])
      (by rw [ha₁.hslot (by decide)]; exact h.hW) (fun j hj => by rw [ha₁.hslot (by unfold sArr; omega_arith)]; exact h.hb j hj)
      (by rw [ha₁.wv_of_not_mem (by decide) (by decide) hn']; exact h.n) hX₁ h.odd)
      fun t₂ ⟨minv, so, f₂', k₂⟩ => ⟨minv, so, f₁.trans (f₂'.mono (by simp [pdAll])), (k₁.trans k₂).mono (by decide), ?_⟩
  rw [f₂'.wv_eq (fun r hr => by
      have := hdr_lt_slot ((k + 7) / 8) aR2 (show 31 < 32 by decide)
      have := slot_sep (w := (k + 7) / 8) (show aR2 ≠ aOne by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [sMinv, sMask, sFn] at * <;> omega_arith)
      (by have := slot_le (w := (k + 7) / 8) (show aR2 < 8 by decide); omega_using [hn', this]),
    ha₁.wv_of_not_mem (by decide) (by decide) hn']
  exact h.r

end VG.Proof.Bignum.AArch64
