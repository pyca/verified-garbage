module

public import VerifiedGarbage.Impl.Aes.Vperm
public import VerifiedGarbage.Proof.Aes.Vector
import VerifiedGarbage.Proof.Aes.InvSboxSpec
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: its checks of the tables evaluate the S-box at every byte (seconds in the kernel), once for the targets that use them.

/-!
# AES by vector permutations: the tables are the cipher's rounds

A state is held as the bytes `L x` (`Lv`), in decryption as the bytes `D x`
(`Dec.Dv`). What the tables say of one byte is checked at every byte
(`sbo_eq`, `sb1_eq`, `sb2_eq`), `L` is linear (`L_xor`: it is the XOR of its
values at the bits of its argument), and a shuffle by constant indices is a
permutation of the bytes (`p_sr`, `p_rsr`, `p_r3sr`, `p_rot`): so `mixV` of
`ioV` and `joV` of a state is a round on the bytes under `L` (`mixV_eq`),
and `lastV` the last round (`lastV_eq`). The code that computes them is each
target's (`AArch64/Vperm.lean`, `X86/Vperm.lean`).
-/

@[expose] public section

namespace VG.Proof.Aes.Vperm

open VG VG.VectorCrypto
open VG.Impl.Aes.Vperm
open VG.Proof.Aes.Vector (st vbyte_mapBytes vbyte_shiftRows vbyte_mixColumns ext_vbyte vbyte_xor st_ext getD_st
  getD_shiftRows getD_subBytes)
open VG.Spec.Aes (subBytes shiftRows)

/-! ## One byte -/

/-- A one-register `tbl` of one byte: 0 for an index of 16 or more. -/
def nib (T : BitVec 128) (i : BitVec 8) : BitVec 8 := if i.toNat < 16 then vbyte T i.toNat else 0

/-- `L x ⊕ L 0x63`, as `keyx` computes it. -/
def Lc (x : BitVec 8) : BitVec 8 := nib keyHi (x >>> 4) ^^^ nib keyLo (x &&& 0x0f)

/-- The byte `x`, as the state holds it. -/
def L (x : BitVec 8) : BitVec 8 := Lc x ^^^ 0xf2

/-- `io` of a byte of the state. -/
def ioB (y : BitVec 8) : BitVec 8 :=
  nib inv (nib inv (y >>> 4) ^^^ nib inva (y &&& 0x0f)) ^^^ ((y &&& 0x0f) ^^^ y >>> 4)

/-- `jo` of a byte of the state. -/
def joB (y : BitVec 8) : BitVec 8 :=
  nib inv (nib inv ((y &&& 0x0f) ^^^ y >>> 4) ^^^ nib inva (y &&& 0x0f)) ^^^ y >>> 4

/-! ### The specification's S-boxes, on the 256 bytes at once

`aesSbox` and `aesInvSbox` take an inverse in GF(2⁸), thirteen products, for every byte. The
checks of the tables against them (`sbo_eq`, `Dec.isb_eq`) read them from the specification's
computation on truth tables instead (`Proof/Aes/SboxSpec.lean`, `InvSboxSpec.lean`), which the
kernel evaluates once for the 256 bytes. -/

/-- The truth tables of the bits of a byte, on the 256 bytes. -/
private def inTabs : List Nat :=
  (List.range 8).map fun k => VG.Bitslice.tableOf (fun c => c.testBit k) 256

private theorem row_inTabs {c : Nat} (hc : c < 256) : row inTabs c = BitVec.ofNat 8 c := by
  refine row_ext fun j hj => ?_
  simp only [inTabs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, VG.Bitslice.testBit_tableOf, hc, decide_true, Bool.true_and,
    BitVec.getLsbD_ofNat, hj]

/-- The S-box of a byte, read from the truth tables. -/
private theorem aesSbox_row (b : BitVec 8) : aesSbox b = row (sboxT inTabs) b.toNat := by
  rw [row_sboxT (by simp [inTabs]) b.isLt, row_inTabs b.isLt, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, Vector.sbox_eq]

/-- The inverse S-box of a byte, read from the truth tables. -/
private theorem aesInvSbox_row (b : BitVec 8) : aesInvSbox b = row (invSboxT inTabs) b.toNat := by
  rw [row_invSboxT _ b.isLt, row_inTabs b.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    Vector.invSbox_eq]

/-- The S-box, from the tables. -/
theorem sbo_eq : ∀ x : BitVec 8,
    aesSbox x = nib sbou (ioB (L x)) ^^^ nib sbot (joB (L x)) ^^^ 0x63 := by
  obtain h : ∀ x : BitVec 8, row (sboxT inTabs) x.toNat =
      nib sbou (ioB (L x)) ^^^ nib sbot (joB (L x)) ^^^ 0x63 := by decide +kernel
  exact fun x => (aesSbox_row x).trans (h x)

theorem sb1_tab : ∀ x : BitVec 8, nib sb1u (ioB (L x)) ^^^ nib sb1t (joB (L x)) =
    L (nib sbou (ioB (L x)) ^^^ nib sbot (joB (L x)) ^^^ 0x63 ^^^ 0x63) := by decide +kernel

theorem sb2_tab : ∀ x : BitVec 8, nib sb2u (ioB (L x)) ^^^ nib sb2t (joB (L x)) =
    L (aesMul 0x02 (nib sbou (ioB (L x)) ^^^ nib sbot (joB (L x)) ^^^ 0x63 ^^^ 0x63)) := by decide +kernel

theorem sb1_eq (x : BitVec 8) :
    nib sb1u (ioB (L x)) ^^^ nib sb1t (joB (L x)) = L (aesSbox x ^^^ 0x63) := by
  rw [sbo_eq x]; exact sb1_tab x

theorem sb2_eq (x : BitVec 8) :
    nib sb2u (ioB (L x)) ^^^ nib sb2t (joB (L x)) = L (aesMul 0x02 (aesSbox x ^^^ 0x63)) := by
  rw [sbo_eq x]; exact sb2_tab x

/-- The bits of `x`, each through `f`. -/
def bits (f : BitVec 8 → BitVec 8) (x : BitVec 8) : BitVec 8 :=
  (if x.getLsbD 0 then f 1 else 0) ^^^ (if x.getLsbD 1 then f 2 else 0) ^^^
  (if x.getLsbD 2 then f 4 else 0) ^^^ (if x.getLsbD 3 then f 8 else 0) ^^^
  (if x.getLsbD 4 then f 16 else 0) ^^^ (if x.getLsbD 5 then f 32 else 0) ^^^
  (if x.getLsbD 6 then f 64 else 0) ^^^ (if x.getLsbD 7 then f 128 else 0)

theorem ite_bxor (p q : Bool) (v : BitVec 8) :
    (if (p ^^ q) = true then v else 0) = (if p = true then v else 0) ^^^ (if q = true then v else 0) := by
  cases p <;> cases q <;> simp

/-- A function that is the XOR of its values at the bits of its argument
is linear. -/
theorem xor_of_bits {f : BitVec 8 → BitVec 8} (h : ∀ x, f x = bits f x) (a b : BitVec 8) :
    f (a ^^^ b) = f a ^^^ f b := by
  rw [h (a ^^^ b), h a, h b]
  simp only [bits, BitVec.getLsbD_xor, ite_bxor]
  ac_rfl

theorem L_bits : ∀ x : BitVec 8, L x = bits L x := by decide +kernel

theorem L_xor (a b : BitVec 8) : L (a ^^^ b) = L a ^^^ L b := xor_of_bits L_bits a b

theorem L_c63 : L 0x63 = 0xf2 := by decide +kernel
theorem L2_c63 : ∀ u : BitVec 8, L (aesMul 0x02 (u ^^^ 0x63)) = L (aesMul 0x02 u) ^^^ 0x90 := by decide +kernel
theorem mul3_eq : ∀ u : BitVec 8, aesMul 0x03 u = aesMul 0x02 u ^^^ u := by decide +kernel
theorem mul1_eq : ∀ u : BitVec 8, aesMul 0x01 u = u := by decide +kernel

/-- The round keys' `L 0x63` cancel. -/
theorem Lc_xor (a b : BitVec 8) : Lc a ^^^ Lc b = L (a ^^^ b) := by
  rw [L_xor, L, L]
  generalize (0xf2 : BitVec 8) = p
  generalize Lc a = a
  generalize Lc b = b
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases p.getLsbD i <;> rfl

/-- A byte of a round: MixColumns of the S-box's bytes `u₀`, …, `u₃` of a
column, and the round key's `k`, under `L`. -/
theorem mix_byte (u₀ u₁ u₂ u₃ k : BitVec 8) :
    L (u₃ ^^^ 0x63) ^^^ Lc k ^^^ (L (aesMul 0x02 (u₀ ^^^ 0x63)) ^^^ L (u₁ ^^^ 0x63)) ^^^
        (L (aesMul 0x02 (u₁ ^^^ 0x63)) ^^^ L (u₂ ^^^ 0x63)) =
      L (aesMul 0x02 u₀ ^^^ aesMul 0x03 u₁ ^^^ aesMul 0x01 u₂ ^^^ aesMul 0x01 u₃ ^^^ k) := by
  rw [mul3_eq, mul1_eq, mul1_eq, L2_c63, L2_c63,
    show Lc k = L k ^^^ 0xf2 by rw [L, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]]
  simp only [L_xor, L_c63]
  generalize L (aesMul 0x02 u₀) = a
  generalize L (aesMul 0x02 u₁) = b
  generalize L u₁ = c
  generalize L u₂ = d
  generalize L u₃ = e
  generalize L k = f
  generalize (0xf2 : BitVec 8) = p
  generalize (0x90 : BitVec 8) = q
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  generalize a.getLsbD i = a
  generalize b.getLsbD i = b
  generalize c.getLsbD i = c
  generalize d.getLsbD i = d
  generalize e.getLsbD i = e
  generalize f.getLsbD i = f
  generalize p.getLsbD i = p
  generalize q.getLsbD i = q
  revert a b c d e f p q
  decide

/-! ## The vectors -/

/-- A one-register `tbl`: the bytes of `n` at the indices in `m`. -/
def tblV (n m : BitVec 128) : BitVec 128 :=
  ofVBytes fun i =>
    let idx := (vbyte m i).toNat
    if idx < 16 then vbyte n idx else 0

theorem vbyte_tblV (n m : BitVec 128) {e : Nat} (he : e < 16) : vbyte (tblV n m) e = nib n (vbyte m e) :=
  Vector.vbyte_ofVBytes _ he

/-- `ushr` by 4 of the bytes. -/
def ushr4 (x : BitVec 128) : BitVec 128 := ofVBytes fun e => vbyte x e >>> 4

theorem vbyte_ushr4 (x : BitVec 128) {e : Nat} (he : e < 16) : vbyte (ushr4 x) e = vbyte x e >>> 4 := by
  exact Vector.vbyte_ofVBytes _ he

theorem vbyte_and (x y : BitVec 128) (e : Nat) : vbyte (x &&& y) e = vbyte x e &&& vbyte y e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [vbyte, hi]

theorem vbyte_mask : ∀ e < 16, vbyte mask e = 0x0f := by decide +kernel
theorem vbyte_c63 : ∀ e < 16, vbyte c63 e = 0x63 := by decide +kernel

/-- `keyx`'s result. -/
def LcV (x : BitVec 128) : BitVec 128 := tblV keyHi (ushr4 x) ^^^ tblV keyLo (x &&& mask)

theorem vbyte_LcV (x : BitVec 128) {e : Nat} (he : e < 16) : vbyte (LcV x) e = Lc (vbyte x e) := by
  rw [LcV, vbyte_xor, vbyte_tblV _ _ he, vbyte_tblV _ _ he, vbyte_ushr4 _ he, vbyte_and, vbyte_mask e he]
  rfl

/-- `invert`'s results. -/
def ioV (x : BitVec 128) : BitVec 128 :=
  tblV inv (tblV inv (ushr4 x) ^^^ tblV inva (x &&& mask)) ^^^ ((x &&& mask) ^^^ ushr4 x)

def joV (x : BitVec 128) : BitVec 128 :=
  tblV inv (tblV inv ((x &&& mask) ^^^ ushr4 x) ^^^ tblV inva (x &&& mask)) ^^^ ushr4 x

theorem vbyte_ioV (x : BitVec 128) {e : Nat} (he : e < 16) : vbyte (ioV x) e = ioB (vbyte x e) := by
  rw [ioV, vbyte_xor, vbyte_tblV _ _ he, vbyte_xor, vbyte_tblV _ _ he, vbyte_tblV _ _ he, vbyte_xor,
    vbyte_ushr4 _ he, vbyte_and, vbyte_mask e he]
  rfl

theorem vbyte_joV (x : BitVec 128) {e : Nat} (he : e < 16) : vbyte (joV x) e = joB (vbyte x e) := by
  rw [joV, vbyte_xor, vbyte_tblV _ _ he, vbyte_xor, vbyte_tblV _ _ he, vbyte_tblV _ _ he, vbyte_xor,
    vbyte_ushr4 _ he, vbyte_and, vbyte_mask e he]
  rfl

/-- The state `x`, as the code holds it. -/
def Lv (x : BitVec 128) : BitVec 128 := ofVBytes fun e => L (vbyte x e)

theorem vbyte_Lv (x : BitVec 128) {e : Nat} (he : e < 16) : vbyte (Lv x) e = L (vbyte x e) :=
  Vector.vbyte_ofVBytes _ he

/-- The block and the first round key. -/
theorem first_eq (x k : BitVec 128) : LcV x ^^^ LcV k = Lv (x ^^^ k) := by
  apply ext_vbyte
  intro e he
  rw [vbyte_xor, vbyte_LcV _ he, vbyte_LcV _ he, vbyte_Lv _ he, vbyte_xor, Lc_xor]

/-! ## The permutations -/

/-- ShiftRows' index. -/
def srI (t : Nat) : Nat := t % 4 + 4 * ((t / 4 + t % 4) % 4)

/-- The index of a column's byte `n` further on. -/
def rI (n t : Nat) : Nat := (t % 4 + n) % 4 + 4 * (t / 4)

theorem p_sr : ∀ t < 16, (vbyte sr t).toNat = srI t := by decide +kernel
theorem p_rsr : ∀ t < 16, (vbyte rsr t).toNat = srI (rI 1 t) := by decide +kernel
theorem p_r3sr : ∀ t < 16, (vbyte r3sr t).toNat = srI (rI 3 t) := by decide +kernel
theorem p_rot : ∀ t < 16, (vbyte rot t).toNat = rI 1 t := by decide +kernel
theorem srI_lt : ∀ t < 16, srI t < 16 := by decide
theorem rI_lt : ∀ n < 4, ∀ t < 16, rI n t < 16 := by decide
theorem rI_rI : ∀ t < 16, rI 1 (rI 1 t) = rI 2 t := by decide
theorem rI_zero : ∀ t < 16, rI 0 t = t := by decide

/-- A `tbl` by constant indices. -/
theorem vbyte_perm (x : BitVec 128) {P : BitVec 128} {e n : Nat} (he : e < 16)
    (h : (vbyte P e).toNat = n) (hn : n < 16) : vbyte (tblV x P) e = vbyte x n := by
  rw [vbyte_tblV _ _ he, nib, h, ite_eq_left hn]

/-! ## A round -/

/-- `L` of the S-box, less `0x63`, of the bytes: `mix`'s `v0` after its
first lookups. -/
def sA (io jo : BitVec 128) : BitVec 128 := tblV sb1u io ^^^ tblV sb1t jo

/-- Twice it. -/
def sA2 (io jo : BitVec 128) : BitVec 128 := tblV sb2u io ^^^ tblV sb2t jo

def mixX (io jo : BitVec 128) : BitVec 128 := tblV (sA2 io jo) sr ^^^ tblV (sA io jo) rsr

/-- `mix`'s result. -/
def mixV (io jo k : BitVec 128) : BitVec 128 :=
  tblV (sA io jo) r3sr ^^^ k ^^^ mixX io jo ^^^ tblV (mixX io jo) rot

theorem vbyte_sA (x : BitVec 128) {e : Nat} (he : e < 16) :
    vbyte (sA (ioV (Lv x)) (joV (Lv x))) e = L (aesSbox (vbyte x e) ^^^ 0x63) := by
  rw [sA, vbyte_xor, vbyte_tblV _ _ he, vbyte_tblV _ _ he, vbyte_ioV _ he, vbyte_joV _ he, vbyte_Lv _ he]
  exact sb1_eq _

theorem vbyte_sA2 (x : BitVec 128) {e : Nat} (he : e < 16) :
    vbyte (sA2 (ioV (Lv x)) (joV (Lv x))) e = L (aesMul 0x02 (aesSbox (vbyte x e) ^^^ 0x63)) := by
  rw [sA2, vbyte_xor, vbyte_tblV _ _ he, vbyte_tblV _ _ he, vbyte_ioV _ he, vbyte_joV _ he, vbyte_Lv _ he]
  exact sb2_eq _

theorem vbyte_mixX (x : BitVec 128) {e : Nat} (he : e < 16) :
    vbyte (mixX (ioV (Lv x)) (joV (Lv x))) e =
      L (aesMul 0x02 (aesSbox (vbyte x (srI e)) ^^^ 0x63)) ^^^
        L (aesSbox (vbyte x (srI (rI 1 e))) ^^^ 0x63) := by
  obtain h1 := rI_lt 1 (by decide) e he
  rw [mixX, vbyte_xor, vbyte_perm _ he (p_sr e he) (srI_lt e he),
    vbyte_perm _ he (p_rsr e he) (srI_lt _ h1), vbyte_sA2 _ (srI_lt e he), vbyte_sA _ (srI_lt _ h1)]

/-- `invert` and `mix` are a round, on the bytes under `L`. -/
theorem mixV_eq (x k : BitVec 128) :
    mixV (ioV (Lv x)) (joV (Lv x)) (LcV k) =
      Lv (aesMixColumns (aesMapBytes aesSbox (aesShiftRows x)) ^^^ k) := by
  apply ext_vbyte
  intro e he
  obtain h0 := rI_lt 0 (by decide) e he
  obtain h1 := rI_lt 1 (by decide) e he
  obtain h2 := rI_lt 2 (by decide) e he
  obtain h3 := rI_lt 3 (by decide) e he
  rw [mixV, vbyte_xor, vbyte_xor, vbyte_xor, vbyte_perm _ he (p_r3sr e he) (srI_lt _ h3),
    vbyte_perm _ he (p_rot e he) h1, vbyte_mixX _ he, vbyte_mixX _ h1, vbyte_sA _ (srI_lt _ h3),
    vbyte_LcV _ he, rI_rI e he, vbyte_Lv _ he, vbyte_xor, vbyte_mixColumns _ he]
  change _ = L (aesMul 0x02 (vbyte (aesMapBytes aesSbox (aesShiftRows x)) (rI 0 e)) ^^^
    aesMul 0x03 (vbyte (aesMapBytes aesSbox (aesShiftRows x)) (rI 1 e)) ^^^
    aesMul 0x01 (vbyte (aesMapBytes aesSbox (aesShiftRows x)) (rI 2 e)) ^^^
    aesMul 0x01 (vbyte (aesMapBytes aesSbox (aesShiftRows x)) (rI 3 e)) ^^^ vbyte k e)
  rw [vbyte_mapBytes _ _ h0, vbyte_mapBytes _ _ h1, vbyte_mapBytes _ _ h2, vbyte_mapBytes _ _ h3,
    vbyte_shiftRows _ h0, vbyte_shiftRows _ h1, vbyte_shiftRows _ h2, vbyte_shiftRows _ h3, rI_zero e he]
  exact mix_byte _ _ _ _ _

/-- `last`'s result. -/
def lastV (io jo k : BitVec 128) : BitVec 128 := tblV (tblV sbou io ^^^ tblV sbot jo) sr ^^^ (k ^^^ c63)

/-- `invert` and `last` are the last round. -/
theorem lastV_eq (x k : BitVec 128) :
    lastV (ioV (Lv x)) (joV (Lv x)) k = aesMapBytes aesSbox (aesShiftRows x) ^^^ k := by
  apply ext_vbyte
  intro e he
  obtain hs := srI_lt e he
  rw [lastV, vbyte_xor, vbyte_perm _ he (p_sr e he) hs, vbyte_xor, vbyte_tblV _ _ hs, vbyte_tblV _ _ hs,
    vbyte_ioV _ hs, vbyte_joV _ hs, vbyte_Lv _ hs, vbyte_xor, vbyte_c63 e he, vbyte_xor,
    vbyte_mapBytes _ _ he, vbyte_shiftRows _ he, sbo_eq,
    show e % 4 + 4 * ((e / 4 + e % 4) % 4) = srI e from rfl]
  generalize nib sbou _ ^^^ nib sbot _ = a
  generalize vbyte k e = b
  generalize (0x63 : BitVec 8) = c
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

/-- SubBytes and ShiftRows of a state. -/
theorem shiftSub_st (v : BitVec 128) :
    st (aesMapBytes aesSbox (aesShiftRows v)) = shiftRows (subBytes (st v)) := by
  apply st_ext
  intro i hi
  obtain hs : i % 4 + 4 * ((i / 4 + i % 4) % 4) < 16 := by omega_arith
  rw [getD_st _ hi, getD_shiftRows _ hi, getD_subBytes _ hs, getD_st _ hs, vbyte_mapBytes _ _ hi,
    vbyte_shiftRows _ hi]
  exact congrFun VG.Proof.Aes.Vector.sbox_eq _

/-! ## Decryption: one byte -/

namespace Dec

open VG.Impl.Aes.Vperm.Dec
open VG.Proof.Aes.Vector (vbyte_invShiftRows vbyte_invMixColumns)

/-- The byte `x`, as the decryption's state holds it. -/
def D (x : BitVec 8) : BitVec 8 := nib dh (x >>> 4) ^^^ nib dl (x &&& 0x0f)

/-- `D`, less `D 0`: it is linear. -/
def Dl (x : BitVec 8) : BitVec 8 := D x ^^^ 0xd1

/-- The inverse S-box, from the tables. -/
theorem isb_eq : ∀ z : BitVec 8,
    aesInvSbox z = nib dbou (ioB (D z)) ^^^ nib dbot (joB (D z)) := by
  obtain h : ∀ z : BitVec 8, row (invSboxT inTabs) z.toNat =
      nib dbou (ioB (D z)) ^^^ nib dbot (joB (D z)) := by decide +kernel
  exact fun z => (aesInvSbox_row z).trans (h z)

/-- A round key's byte, through a pair of the tables. -/
def Yb (l h : BitVec 128) (x : BitVec 8) : BitVec 8 := nib l (x &&& 0x0f) ^^^ nib h (x >>> 4)

theorem Dl_bits : ∀ x : BitVec 8, Dl x = bits Dl x := by decide +kernel

theorem Dl_xor (a b : BitVec 8) : Dl (a ^^^ b) = Dl a ^^^ Dl b := xor_of_bits Dl_bits a b

/-! The products by the coefficients of InvMixColumns, under `Dl`, are linear. -/

theorem g0_xor (a b : BitVec 8) : Dl (aesMul 0x0e (a ^^^ b)) = Dl (aesMul 0x0e a) ^^^ Dl (aesMul 0x0e b) :=
  (congrArg Dl (mul_xor (.inl rfl) a b)).trans (Dl_xor _ _)
theorem g1_xor (a b : BitVec 8) : Dl (aesMul 0x0b (a ^^^ b)) = Dl (aesMul 0x0b a) ^^^ Dl (aesMul 0x0b b) :=
  (congrArg Dl (mul_xor (.inr (.inl rfl)) a b)).trans (Dl_xor _ _)
theorem g2_xor (a b : BitVec 8) : Dl (aesMul 0x0d (a ^^^ b)) = Dl (aesMul 0x0d a) ^^^ Dl (aesMul 0x0d b) :=
  (congrArg Dl (mul_xor (.inr (.inr (.inl rfl))) a b)).trans (Dl_xor _ _)
theorem g3_xor (a b : BitVec 8) : Dl (aesMul 0x09 (a ^^^ b)) = Dl (aesMul 0x09 a) ^^^ Dl (aesMul 0x09 b) :=
  (congrArg Dl (mul_xor (.inr (.inr (.inr rfl))) a b)).trans (Dl_xor _ _)

/-! A pair of tables of the rounds is the inverse S-box's pair under a linear function, table by
table. -/

theorem nib_map {t u : BitVec 128} {g : BitVec 8 → BitVec 8} (h0 : g 0 = 0)
    (h : ∀ v < 16, nib t (BitVec.ofNat 8 v) = g (nib u (BitVec.ofNat 8 v))) (i : BitVec 8) : nib t i = g (nib u i) := by
  by_cases hi : i.toNat < 16
  · have := h _ hi
    rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  · rw [nib, nib, ite_eq_right hi, ite_eq_right hi, h0]

theorem pair_map {t t' u u' : BitVec 128} {g : BitVec 8 → BitVec 8} (hg : ∀ a b, g (a ^^^ b) = g a ^^^ g b)
    (h : ∀ v < 16, nib t (BitVec.ofNat 8 v) = g (nib u (BitVec.ofNat 8 v)) ∧
      nib t' (BitVec.ofNat 8 v) = g (nib u' (BitVec.ofNat 8 v))) (i j : BitVec 8) :
    nib t i ^^^ nib t' j = g (nib u i ^^^ nib u' j) := by
  have h0 : g 0 = 0 := by
    have := hg 0 0
    rwa [BitVec.xor_self, BitVec.xor_self] at this
  rw [hg, nib_map h0 (fun v hv => (h v hv).1), nib_map h0 (fun v hv => (h v hv).2)]

theorem x0_tab (z : BitVec 8) : nib x0u (ioB (D z)) ^^^ nib x0t (joB (D z)) =
    Dl (aesMul 0x0e (nib dbou (ioB (D z)) ^^^ nib dbot (joB (D z)))) :=
  pair_map (t := x0u) (t' := x0t) (u := dbou) (u' := dbot) (g := fun x => Dl (aesMul 0x0e x)) g0_xor (by decide +kernel) _ _
theorem x1_tab (z : BitVec 8) : nib x1u (ioB (D z)) ^^^ nib x1t (joB (D z)) =
    Dl (aesMul 0x0b (nib dbou (ioB (D z)) ^^^ nib dbot (joB (D z)))) :=
  pair_map (t := x1u) (t' := x1t) (u := dbou) (u' := dbot) (g := fun x => Dl (aesMul 0x0b x)) g1_xor (by decide +kernel) _ _
theorem x2_tab (z : BitVec 8) : nib x2u (ioB (D z)) ^^^ nib x2t (joB (D z)) =
    Dl (aesMul 0x0d (nib dbou (ioB (D z)) ^^^ nib dbot (joB (D z)))) :=
  pair_map (t := x2u) (t' := x2t) (u := dbou) (u' := dbot) (g := fun x => Dl (aesMul 0x0d x)) g2_xor (by decide +kernel) _ _
theorem x3_tab (z : BitVec 8) : nib x3u (ioB (D z)) ^^^ nib x3t (joB (D z)) =
    Dl (aesMul 0x09 (nib dbou (ioB (D z)) ^^^ nib dbot (joB (D z)))) :=
  pair_map (t := x3u) (t' := x3t) (u := dbou) (u' := dbot) (g := fun x => Dl (aesMul 0x09 x)) g3_xor (by decide +kernel) _ _

/-- A byte, from its nibbles. -/
theorem nibbles : ∀ x : BitVec 8, (x &&& (0x0f : BitVec 8)).toNat < 16 ∧ (x >>> 4).toNat < 16 ∧
    (x &&& (0x0f : BitVec 8)) ^^^ ((x >>> 4) <<< 4) = x := by decide +kernel

/-- A pair of tables is an affine function if each is on the 16 nibbles. -/
theorem Yb_of {l h : BitVec 128} {g : BitVec 8 → BitVec 8} {c : BitVec 8}
    (hg : ∀ a b, g (a ^^^ b) = g a ^^^ g b)
    (ht : ∀ v < 16, nib l (BitVec.ofNat 8 v) = g (BitVec.ofNat 8 v) ^^^ nib l 0 ∧
      nib h (BitVec.ofNat 8 v) = g (BitVec.ofNat 8 v <<< 4) ^^^ nib h 0)
    (hc : nib l 0 ^^^ nib h 0 = c) (x : BitVec 8) : Yb l h x = g x ^^^ c := by
  obtain ⟨h1, h2, h3⟩ := nibbles x
  have e1 := (ht _ h1).1
  have e2 := (ht _ h2).2
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at e1 e2
  have e3 : g x = g (x &&& 0x0f) ^^^ g ((x >>> 4) <<< 4) := by rw [← hg, h3]
  rw [Yb, e1, e2, e3, ← hc]
  ac_rfl

theorem y0_tab (x : BitVec 8) : Yb y0l y0h x = D (aesMul 0x0e x) := by
  refine (Yb_of (g := fun x => Dl (aesMul 0x0e x)) (c := 0xd1) g0_xor (by decide +kernel) (by decide +kernel) x).trans ?_
  show (D _ ^^^ 0xd1) ^^^ 0xd1 = _
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
theorem y1_tab (x : BitVec 8) : Yb y1l y1h x = Dl (aesMul 0x0b x) :=
  (Yb_of (g := fun x => Dl (aesMul 0x0b x)) (c := 0) g1_xor (by decide +kernel) (by decide +kernel) x).trans (BitVec.xor_zero ..)
theorem y2_tab (x : BitVec 8) : Yb y2l y2h x = Dl (aesMul 0x0d x) :=
  (Yb_of (g := fun x => Dl (aesMul 0x0d x)) (c := 0) g2_xor (by decide +kernel) (by decide +kernel) x).trans (BitVec.xor_zero ..)
theorem y3_tab (x : BitVec 8) : Yb y3l y3h x = Dl (aesMul 0x09 x) :=
  (Yb_of (g := fun x => Dl (aesMul 0x09 x)) (c := 0) g3_xor (by decide +kernel) (by decide +kernel) x).trans (BitVec.xor_zero ..)

/-- A byte of a round: InvMixColumns of the inverse S-box's bytes `u₀`, …,
`u₃` of a column, each XORed with the round key's byte, under `D`. -/
theorem imix_byte (u₀ u₁ u₂ u₃ k₀ k₁ k₂ k₃ : BitVec 8) :
    Dl (aesMul 0x0e u₀) ^^^ Dl (aesMul 0x0b u₁) ^^^
        (D (aesMul 0x0e k₀) ^^^ Dl (aesMul 0x0b k₁) ^^^ Dl (aesMul 0x0d k₂) ^^^ Dl (aesMul 0x09 k₃)) ^^^
        (Dl (aesMul 0x0d u₂) ^^^ Dl (aesMul 0x09 u₃)) =
      D (aesMul 0x0e (u₀ ^^^ k₀) ^^^ aesMul 0x0b (u₁ ^^^ k₁) ^^^ aesMul 0x0d (u₂ ^^^ k₂) ^^^
        aesMul 0x09 (u₃ ^^^ k₃)) := by
  obtain hD : ∀ x, D x = Dl x ^^^ 0xd1 := fun x => by
    rw [Dl, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  rw [hD, hD, Dl_xor, Dl_xor, Dl_xor, g0_xor, g1_xor, g2_xor, g3_xor]
  ac_rfl

/-! ## Decryption: the vectors -/

/-- The state `x`, as the decryption holds it. -/
def Dv (x : BitVec 128) : BitVec 128 := ofVBytes fun e => D (vbyte x e)

theorem vbyte_Dv (x : BitVec 128) {e : Nat} (he : e < 16) : vbyte (Dv x) e = D (vbyte x e) :=
  Vector.vbyte_ofVBytes _ he

/-- `first`'s result. -/
def firstV (x : BitVec 128) : BitVec 128 := tblV dh (ushr4 x) ^^^ tblV dl (x &&& mask)

theorem firstV_eq (x : BitVec 128) : firstV x = Dv x := by
  apply ext_vbyte
  intro e he
  rw [firstV, vbyte_xor, vbyte_tblV _ _ he, vbyte_tblV _ _ he, vbyte_ushr4 _ he, vbyte_and, vbyte_mask e he,
    vbyte_Dv _ he]
  rfl

/-- `keyTerm`'s result, on the round key `k`. -/
def Yv (l h k : BitVec 128) : BitVec 128 := tblV l (k &&& mask) ^^^ tblV h (ushr4 k)

theorem vbyte_Yv (l h k : BitVec 128) {e : Nat} (he : e < 16) : vbyte (Yv l h k) e = Yb l h (vbyte k e) := by
  rw [Yv, vbyte_xor, vbyte_tblV _ _ he, vbyte_tblV _ _ he, vbyte_ushr4 _ he, vbyte_and, vbyte_mask e he]
  rfl

/-- `key`'s result. -/
def keyV (k : BitVec 128) : BitVec 128 :=
  Yv y0l y0h k ^^^ tblV (Yv y1l y1h k) rot ^^^ tblV (Yv y2l y2h k) rot2 ^^^ tblV (Yv y3l y3h k) rot3

/-- InvShiftRows' index. -/
def isrI (t : Nat) : Nat := t % 4 + 4 * ((t / 4 + 4 - t % 4) % 4)

theorem p_p0 : ∀ t < 16, (vbyte p0 t).toNat = isrI (rI 0 t) := by decide +kernel
theorem p_p1 : ∀ t < 16, (vbyte p1 t).toNat = isrI (rI 1 t) := by decide +kernel
theorem p_p2 : ∀ t < 16, (vbyte p2 t).toNat = isrI (rI 2 t) := by decide +kernel
theorem p_p3 : ∀ t < 16, (vbyte p3 t).toNat = isrI (rI 3 t) := by decide +kernel
theorem p_rot2 : ∀ t < 16, (vbyte rot2 t).toNat = rI 2 t := by decide +kernel
theorem p_rot3 : ∀ t < 16, (vbyte rot3 t).toNat = rI 3 t := by decide +kernel
theorem isrI_lt : ∀ t < 16, isrI t < 16 := by decide

theorem vbyte_keyV (k : BitVec 128) {e : Nat} (he : e < 16) :
    vbyte (keyV k) e = D (aesMul 0x0e (vbyte k e)) ^^^ Dl (aesMul 0x0b (vbyte k (rI 1 e))) ^^^
      Dl (aesMul 0x0d (vbyte k (rI 2 e))) ^^^ Dl (aesMul 0x09 (vbyte k (rI 3 e))) := by
  obtain h1 := rI_lt 1 (by decide) e he
  obtain h2 := rI_lt 2 (by decide) e he
  obtain h3 := rI_lt 3 (by decide) e he
  rw [keyV, vbyte_xor, vbyte_xor, vbyte_xor, vbyte_perm _ he (p_rot e he) h1,
    vbyte_perm _ he (p_rot2 e he) h2, vbyte_perm _ he (p_rot3 e he) h3, vbyte_Yv _ _ _ he,
    vbyte_Yv _ _ _ h1, vbyte_Yv _ _ _ h2, vbyte_Yv _ _ _ h3, y0_tab, y1_tab, y2_tab, y3_tab]

/-- A product of the inverse S-box's bytes, permuted: a term of `mix`. -/
def xV (u t p io jo : BitVec 128) : BitVec 128 := tblV (tblV u io ^^^ tblV t jo) p

/-- `mix`'s result. -/
def mixV (io jo k : BitVec 128) : BitVec 128 :=
  xV x0u x0t p0 io jo ^^^ xV x1u x1t p1 io jo ^^^ k ^^^ (xV x2u x2t p2 io jo ^^^ xV x3u x3t p3 io jo)

theorem vbyte_xV {u t p : BitVec 128} {c : BitVec 8} {n : Nat} (hn : n < 4)
    (hp : ∀ e < 16, (vbyte p e).toNat = isrI (rI n e))
    (ht : ∀ z : BitVec 8, nib u (ioB (D z)) ^^^ nib t (joB (D z)) =
      Dl (aesMul c (nib dbou (ioB (D z)) ^^^ nib dbot (joB (D z)))))
    (x : BitVec 128) {e : Nat} (he : e < 16) :
    vbyte (xV u t p (ioV (Dv x)) (joV (Dv x))) e = Dl (aesMul c (aesInvSbox (vbyte x (isrI (rI n e))))) := by
  obtain hs := isrI_lt _ (rI_lt n hn e he)
  rw [xV, vbyte_perm _ he (hp e he) hs, vbyte_xor, vbyte_tblV _ _ hs, vbyte_tblV _ _ hs, vbyte_ioV _ hs,
    vbyte_joV _ hs, vbyte_Dv _ hs, ht, isb_eq]

/-- `invert` and `mix` are a round of the inverse cipher, on the bytes
under `D`. -/
theorem mixV_eq (x k : BitVec 128) :
    mixV (ioV (Dv x)) (joV (Dv x)) (keyV k) =
      Dv (aesInvMixColumns (aesMapBytes aesInvSbox (aesInvShiftRows x) ^^^ k)) := by
  apply ext_vbyte
  intro e he
  obtain h0 := rI_lt 0 (by decide) e he
  obtain h1 := rI_lt 1 (by decide) e he
  obtain h2 := rI_lt 2 (by decide) e he
  obtain h3 := rI_lt 3 (by decide) e he
  rw [mixV, vbyte_xor, vbyte_xor, vbyte_xor, vbyte_xor, vbyte_xV (by decide) p_p0 x0_tab _ he,
    vbyte_xV (by decide) p_p1 x1_tab _ he, vbyte_xV (by decide) p_p2 x2_tab _ he,
    vbyte_xV (by decide) p_p3 x3_tab _ he, vbyte_keyV _ he, vbyte_Dv _ he, vbyte_invMixColumns _ he]
  change _ = D (aesMul 0x0e (vbyte (aesMapBytes aesInvSbox (aesInvShiftRows x) ^^^ k) (rI 0 e)) ^^^
    aesMul 0x0b (vbyte (aesMapBytes aesInvSbox (aesInvShiftRows x) ^^^ k) (rI 1 e)) ^^^
    aesMul 0x0d (vbyte (aesMapBytes aesInvSbox (aesInvShiftRows x) ^^^ k) (rI 2 e)) ^^^
    aesMul 0x09 (vbyte (aesMapBytes aesInvSbox (aesInvShiftRows x) ^^^ k) (rI 3 e)))
  rw [vbyte_xor, vbyte_xor, vbyte_xor, vbyte_xor, vbyte_mapBytes _ _ h0, vbyte_mapBytes _ _ h1,
    vbyte_mapBytes _ _ h2, vbyte_mapBytes _ _ h3, vbyte_invShiftRows _ h0, vbyte_invShiftRows _ h1,
    vbyte_invShiftRows _ h2, vbyte_invShiftRows _ h3]
  rw [show vbyte k (rI 0 e) = vbyte k e by rw [rI_zero e he]]
  exact imix_byte _ _ _ _ _ _ _ _

/-- `last`'s result. -/
def lastV (io jo k : BitVec 128) : BitVec 128 := tblV (tblV dbou io ^^^ tblV dbot jo) p0 ^^^ k

/-- `invert` and `last` are the last round of the inverse cipher. -/
theorem lastV_eq (x k : BitVec 128) :
    lastV (ioV (Dv x)) (joV (Dv x)) k = aesMapBytes aesInvSbox (aesInvShiftRows x) ^^^ k := by
  apply ext_vbyte
  intro e he
  obtain hs := isrI_lt _ (rI_lt 0 (by decide) e he)
  rw [lastV, vbyte_xor, vbyte_perm _ he (p_p0 e he) hs, vbyte_xor, vbyte_tblV _ _ hs, vbyte_tblV _ _ hs,
    vbyte_ioV _ hs, vbyte_joV _ hs, vbyte_Dv _ hs, ← isb_eq, vbyte_xor, vbyte_mapBytes _ _ he,
    vbyte_invShiftRows _ he, rI_zero e he]
  rfl

end Dec

end VG.Proof.Aes.Vperm
