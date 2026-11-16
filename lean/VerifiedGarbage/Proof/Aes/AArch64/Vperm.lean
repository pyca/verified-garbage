module

public import VerifiedGarbage.Impl.Aes.AArch64.Vperm
public import VerifiedGarbage.Proof.Aes.Vector
public import VerifiedGarbage.Proof.Framework.AArch64.Tbl
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: its checks of the tables evaluate the S-box at every byte (seconds in the kernel), which a change to the proofs of the entry points (`OneBlock.lean`) need not repeat.

/-!
# AES on AArch64: one block by vector permutations

`Vperm.core` is FIPS 197's cipher on the state in `v0` (`core_ok`). The
state is held as the bytes `L x` (`Lv`). What the tables say of one byte is
checked at every byte (`sbo_eq`, `sb1_eq`, `sb2_eq`), `L` is linear
(`L_xor`: it is the XOR of its values at the bits of its argument), and a
`tbl` by constant indices is a permutation of the bytes (`p_sr`, `p_rsr`,
`p_r3sr`, `p_rot`): so `invert` and `mix` are a round on the bytes under
`L` (`mixV_eq`), and `invert` and `last` the last round (`lastV_eq`).
-/

@[expose] public section

namespace VG.Proof.Aes.AArch64.Vperm

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64
open VG.Impl.Aes.AArch64.Vperm
open VG.Proof.Aes.Vector (st KeyIs rnds rnds_zero rnds_succ cipher_eq eor_st aesmc_st keyIs_readW
  vbyte_mapBytes vbyte_shiftRows vbyte_mixColumns ext_vbyte st_ext getD_st getD_shiftRows getD_subBytes)
open VG.Spec.Aes (roundKey cipher addRoundKey bytesAt subBytes shiftRows mixColumns)

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

/-- The S-box, from the tables. -/
theorem sbo_eq : ∀ x : BitVec 8,
    aesSbox x = nib sbou (ioB (L x)) ^^^ nib sbot (joB (L x)) ^^^ 0x63 := by decide +kernel

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
def ushr4 (x : BitVec 128) : BitVec 128 := VArr.b16.map2 (fun w a b => VShiftOp.ushr.eval 4 w a b) x x

theorem vbyte_ushr4 (x : BitVec 128) {e : Nat} (he : e < 16) : vbyte (ushr4 x) e = vbyte x e >>> 4 := by
  simp only [ushr4, VArr.map2]
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
  have h1 := rI_lt 1 (by decide) e he
  rw [mixX, vbyte_xor, vbyte_perm _ he (p_sr e he) (srI_lt e he),
    vbyte_perm _ he (p_rsr e he) (srI_lt _ h1), vbyte_sA2 _ (srI_lt e he), vbyte_sA _ (srI_lt _ h1)]

/-- `invert` and `mix` are a round, on the bytes under `L`. -/
theorem mixV_eq (x k : BitVec 128) :
    mixV (ioV (Lv x)) (joV (Lv x)) (LcV k) =
      Lv (aesMixColumns (aesMapBytes aesSbox (aesShiftRows x)) ^^^ k) := by
  apply ext_vbyte
  intro e he
  have h0 := rI_lt 0 (by decide) e he
  have h1 := rI_lt 1 (by decide) e he
  have h2 := rI_lt 2 (by decide) e he
  have h3 := rI_lt 3 (by decide) e he
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
  have hs := srI_lt e he
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

/-! ## The tables -/

/-- What `setup` leaves in the vector registers. -/
structure Consts (s : State) : Prop where
  v16 : s.v .v16 = mask
  v17 : s.v .v17 = inv
  v18 : s.v .v18 = inva
  v19 : s.v .v19 = sb1u
  v20 : s.v .v20 = sb1t
  v21 : s.v .v21 = sb2u
  v22 : s.v .v22 = sb2t
  v23 : s.v .v23 = sr
  v24 : s.v .v24 = rsr
  v25 : s.v .v25 = r3sr
  v26 : s.v .v26 = rot
  v27 : s.v .v27 = keyLo
  v28 : s.v .v28 = keyHi
  v29 : s.v .v29 = sbou
  v30 : s.v .v30 = sbot
  v31 : s.v .v31 = c63

/-- The registers the rounds write. -/
abbrev temps : List VReg := [.v0, .v1, .v2, .v3, .v4, .v5, .v6]

theorem Consts.of_v {s t : State} (h : Consts s) (hv : ∀ r, r ∉ temps → t.v r = s.v r) : Consts t :=
  ⟨(hv _ (by decide)).trans h.v16, (hv _ (by decide)).trans h.v17, (hv _ (by decide)).trans h.v18,
    (hv _ (by decide)).trans h.v19, (hv _ (by decide)).trans h.v20, (hv _ (by decide)).trans h.v21,
    (hv _ (by decide)).trans h.v22, (hv _ (by decide)).trans h.v23, (hv _ (by decide)).trans h.v24,
    (hv _ (by decide)).trans h.v25, (hv _ (by decide)).trans h.v26, (hv _ (by decide)).trans h.v27,
    (hv _ (by decide)).trans h.v28, (hv _ (by decide)).trans h.v29, (hv _ (by decide)).trans h.v30,
    (hv _ (by decide)).trans h.v31⟩

/-- A vector is its two doublewords. -/
theorem halves_append (x : BitVec 128) : x.extractLsb' 64 64 ++ x.extractLsb' 0 64 = x :=
  ofVDwords_halves x

theorem tabWords_length : tabWords.length = 32 := by simp [tabWords]

/-- The two words of vector `j` of the static, as `ldrqTbl` loads them. -/
theorem tabWords_pair {j : Nat} (hj : j < 16) :
    tabWords.getD (16 * j / 8 + 1) 0 ++ tabWords.getD (16 * j / 8) 0 = tabVec j := by
  have g : ∀ i < 32, tabWords.getD i 0 = (tabVec (i / 2)).extractLsb' (64 * (i % 2)) 64 := fun i hi => by
    simp [tabWords, hi]
  rw [show 16 * j / 8 = 2 * j by omega_arith, g _ (by omega_arith), g _ (by omega_arith),
    show (2 * j + 1) / 2 = j by omega_arith, show (2 * j + 1) % 2 = 1 by omega_arith,
    show 2 * j / 2 = j by omega_arith, show 2 * j % 2 = 0 by omega_arith]
  exact halves_append _

/-- Loading vector `j` of the static, whose address is in `x6`. -/
theorem exec_tld {j : Nat} (hj : j < 16) {s : State} (hx : s.gpr .x6 = s.syms tabName) :
    exec (tld j) s = some (s.setV (treg j) (tabVec j)) := by
  have hc : s.gpr .x6 = s.syms tabName ∧ 16 * j % 16 = 0 ∧ 16 * j < 65536 ∧
      16 * j / 8 + 2 ≤ tabWords.length :=
    ⟨hx, by omega_arith, by omega_arith, by rw [tabWords_length]; omega_arith⟩
  simp only [tld, exec, ite_eq_left_of_eq_true _ _ (eq_true hc), tabWords_pair hj]

/-- What a load of a static changes. -/
structure Loaded (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  syms : t.syms = s.syms

theorem Loaded.refl (s : State) : Loaded s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Loaded.trans {a b c : State} (h₁ : Loaded a b) (h₂ : Loaded b c) : Loaded a c :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp,
    h₂.syms.trans h₁.syms⟩

theorem Loaded.setV (s : State) (r : VReg) (x : BitVec 128) : Loaded s (s.setV r x) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The tables from the static into the table registers. -/
theorem tldTable_ok {s : State} (hx : s.gpr .x6 = s.syms tabName) :
    WP isa (.block ((List.range 16).map tld)) s fun t =>
      (∀ r < 16, t.v (treg r) = tabVec r) ∧ (∀ w, (∀ r < 16, w ≠ treg r) → t.v w = s.v w) ∧ Loaded s t := by
  suffices h : ∀ n ≤ 16, WP isa (.block ((List.range n).map tld)) s fun t =>
      (∀ r < n, t.v (treg r) = tabVec r) ∧ (∀ w, (∀ r < n, w ≠ treg r) → t.v w = s.v w) ∧ Loaded s t from
    h 16 (Nat.le_refl _)
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ h => absurd h (by omega_arith), fun _ _ => rfl, Loaded.refl s⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega_arith)) fun a ⟨arow, av, al⟩ => ?_
    rw [WP.block_cons_iff]
    refine ⟨_, exec_tld (j := n) (by omega_arith) (by rw [al.gpr, al.syms]; exact hx),
      WP.block_nil ⟨fun r hr => ?_, fun w hw => ?_, al.trans (Loaded.setV _ _ _)⟩⟩
    · by_cases he : r = n
      · subst he; exact v_setV_self _ _ _
      · rw [v_setV_of_ne _ _ (fun e => he (treg_inj r (by omega_arith) n (by omega_arith) e)),
          arow r (by omega_arith)]
    · rw [v_setV_of_ne _ _ (hw n (by omega_arith)), av w (fun r hr => hw r (by omega_arith))]

theorem treg_notTemp : ∀ r < 16, treg r ∉ temps := by decide

/-- `setup`: the tables, from the static, through `x6`. -/
theorem setup_ok (s : State) :
    WP isa (.block setup) s fun t => Consts t ∧ t.v .v0 = s.v .v0 ∧
      (∀ g, g ≠ .x6 → t.gpr g = s.gpr g) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  unfold setup
  let a := s.write .x .x6 (s.syms tabName)
  have ax : a.gpr .x6 = a.syms tabName := gpr_write_self _ _ _ _
  rw [List.singleton_append, WP.block_cons_iff]
  refine ⟨a, exec_adrSym, ?_⟩
  refine WP.mono (tldTable_ok ax) fun t ⟨trow, tv, tl⟩ => ?_
  refine ⟨⟨trow 0 (by decide), trow 1 (by decide), trow 2 (by decide), trow 3 (by decide),
    trow 4 (by decide), trow 5 (by decide), trow 6 (by decide), trow 7 (by decide), trow 8 (by decide),
    trow 9 (by decide), trow 10 (by decide), trow 11 (by decide), trow 12 (by decide),
    trow 13 (by decide), trow 14 (by decide), trow 15 (by decide)⟩, ?_, fun g h6 => ?_, tl.mem, tl.rd,
    tl.wr, tl.sp⟩
  · rw [tv _ (fun r hr e => treg_notTemp r hr (e ▸ by decide))]
    rfl
  · rw [tl.gpr]; exact gpr_write_of_ne _ _ _ h6

/-! ## The code of a round -/

/-- `keyx`, on the block (`v0`, through `v1`) or a round key (`v5`, through
`v6`). -/
theorem keyx_run (s : State) (hc : Consts s) {d t : VReg}
    (hd : (d = .v0 ∧ t = .v1) ∨ (d = .v5 ∧ t = .v6)) :
    ∃ u, runBlock isa (keyx d t) s = some u ∧ u.v d = LcV (s.v d) ∧ VOnly [d, t] s u := by
  let a := s.setV t (s.v d &&& s.v .v16)
  let b := a.setV d (ushr4 (a.v d))
  let c := b.setV t (tblV (b.v .v27) (b.v t))
  let e := c.setV d (tblV (c.v .v28) (c.v d))
  let u := e.setV d (e.v d ^^^ e.v t)
  have o : VOnly [d, t] s u :=
    ((((VOnly.setV s (by simp) _).trans (VOnly.setV a (by simp) _)).trans (VOnly.setV b (by simp) _)).trans
      (VOnly.setV c (by simp) _)).trans (VOnly.setV e (by simp) _)
  refine ⟨u, ?_, ?_, o⟩
  · rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  · rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [u, e, c, b, a, v_setV, reduceCtorEq, ite_true, ite_false, hc.v16, hc.v27, hc.v28, LcV]

/-- `invert`: `io` and `jo` of the state's bytes. -/
theorem invert_run (s : State) (hc : Consts s) :
    ∃ t, runBlock isa invert s = some t ∧ t.v .v2 = ioV (s.v .v0) ∧ t.v .v3 = joV (s.v .v0) ∧
      VOnly [.v0, .v1, .v2, .v3, .v4] s t := by
  let a := s.setV .v1 (s.v .v0 &&& s.v .v16)
  let b := a.setV .v0 (ushr4 (a.v .v0))
  let c := b.setV .v2 (tblV (b.v .v18) (b.v .v1))
  let d := c.setV .v1 (c.v .v1 ^^^ c.v .v0)
  let e := d.setV .v3 (tblV (d.v .v17) (d.v .v0))
  let f := e.setV .v4 (tblV (e.v .v17) (e.v .v1))
  let g := f.setV .v3 (f.v .v3 ^^^ f.v .v2)
  let h := g.setV .v4 (g.v .v4 ^^^ g.v .v2)
  let i := h.setV .v2 (tblV (h.v .v17) (h.v .v3))
  let j := i.setV .v3 (tblV (i.v .v17) (i.v .v4))
  let k := j.setV .v2 (j.v .v2 ^^^ j.v .v1)
  let t := k.setV .v3 (k.v .v3 ^^^ k.v .v0)
  refine ⟨t, rfl, ?_, ?_, ?_⟩
  · simp only [t, k, j, i, h, g, f, e, d, c, b, a, v_setV, reduceCtorEq, ite_true, ite_false, hc.v16,
      hc.v17, hc.v18, ioV]
  · simp only [t, k, j, i, h, g, f, e, d, c, b, a, v_setV, reduceCtorEq, ite_true, ite_false, hc.v16,
      hc.v17, hc.v18, joV]
  · exact (((((((((((VOnly.setV s (by simp) _).trans (VOnly.setV a (by simp) _)).trans
      (VOnly.setV b (by simp) _)).trans (VOnly.setV c (by simp) _)).trans (VOnly.setV d (by simp) _)).trans
      (VOnly.setV e (by simp) _)).trans (VOnly.setV f (by simp) _)).trans (VOnly.setV g (by simp) _)).trans
      (VOnly.setV h (by simp) _)).trans (VOnly.setV i (by simp) _)).trans (VOnly.setV j (by simp) _)).trans
      (VOnly.setV k (by simp) _)

/-- `mix`, on `io` and `jo` in `v2` and `v3` and the round key in `v5`. -/
theorem mix_run (s : State) (hc : Consts s) :
    ∃ t, runBlock isa mix s = some t ∧ t.v .v0 = mixV (s.v .v2) (s.v .v3) (s.v .v5) ∧
      VOnly [.v0, .v1, .v2, .v3] s t := by
  let a := s.setV .v0 (tblV (s.v .v19) (s.v .v2))
  let b := a.setV .v1 (tblV (a.v .v20) (a.v .v3))
  let c := b.setV .v2 (tblV (b.v .v21) (b.v .v2))
  let d := c.setV .v3 (tblV (c.v .v22) (c.v .v3))
  let e := d.setV .v0 (d.v .v0 ^^^ d.v .v1)
  let f := e.setV .v2 (e.v .v2 ^^^ e.v .v3)
  let g := f.setV .v1 (tblV (f.v .v2) (f.v .v23))
  let h := g.setV .v3 (tblV (g.v .v0) (g.v .v24))
  let i := h.setV .v0 (tblV (h.v .v0) (h.v .v25))
  let j := i.setV .v1 (i.v .v1 ^^^ i.v .v3)
  let k := j.setV .v0 (j.v .v0 ^^^ j.v .v5)
  let l := k.setV .v3 (tblV (k.v .v1) (k.v .v26))
  let m := l.setV .v0 (l.v .v0 ^^^ l.v .v1)
  let t := m.setV .v0 (m.v .v0 ^^^ m.v .v3)
  refine ⟨t, rfl, ?_, ?_⟩
  · simp only [t, m, l, k, j, i, h, g, f, e, d, c, b, a, v_setV, reduceCtorEq, ite_true, ite_false,
      hc.v19, hc.v20, hc.v21, hc.v22, hc.v23, hc.v24, hc.v25, hc.v26, mixV, mixX, sA, sA2]
  · exact (((((((((((((VOnly.setV s (by simp) _).trans (VOnly.setV a (by simp) _)).trans
      (VOnly.setV b (by simp) _)).trans (VOnly.setV c (by simp) _)).trans (VOnly.setV d (by simp) _)).trans
      (VOnly.setV e (by simp) _)).trans (VOnly.setV f (by simp) _)).trans (VOnly.setV g (by simp) _)).trans
      (VOnly.setV h (by simp) _)).trans (VOnly.setV i (by simp) _)).trans (VOnly.setV j (by simp) _)).trans
      (VOnly.setV k (by simp) _)).trans (VOnly.setV l (by simp) _)).trans (VOnly.setV m (by simp) _)

/-- `last`, on `io` and `jo` in `v2` and `v3` and the round key in `v5`. -/
theorem last_run (s : State) (hc : Consts s) :
    ∃ t, runBlock isa last s = some t ∧ t.v .v0 = lastV (s.v .v2) (s.v .v3) (s.v .v5) ∧
      VOnly [.v0, .v1, .v5] s t := by
  let a := s.setV .v0 (tblV (s.v .v29) (s.v .v2))
  let b := a.setV .v1 (tblV (a.v .v30) (a.v .v3))
  let c := b.setV .v0 (b.v .v0 ^^^ b.v .v1)
  let d := c.setV .v0 (tblV (c.v .v0) (c.v .v23))
  let e := d.setV .v5 (d.v .v5 ^^^ d.v .v31)
  let t := e.setV .v0 (e.v .v0 ^^^ e.v .v5)
  refine ⟨t, rfl, ?_, ?_⟩
  · simp only [t, e, d, c, b, a, v_setV, reduceCtorEq, ite_true, ite_false, hc.v23, hc.v29, hc.v30,
      hc.v31, lastV]
  · exact (((((VOnly.setV s (by simp) _).trans (VOnly.setV a (by simp) _)).trans
      (VOnly.setV b (by simp) _)).trans (VOnly.setV c (by simp) _)).trans (VOnly.setV d (by simp) _)).trans
      (VOnly.setV e (by simp) _)

/-! ## The rounds -/

theorem VOnly.sp {ds : List VReg} {s s' : State} (h : VOnly ds s s') : s'.sp = s.sp := by
  rw [h.1]

theorem vonly_mono {ds es : List VReg} {s s' : State} (h : VOnly ds s s') (hs : ∀ r ∈ ds, r ∈ es) :
    VOnly es s s' :=
  ⟨h.1, fun r hr => h.2 r fun hd => hr (hs r hd)⟩

theorem read_x (s : State) (r : Reg) : s.read .x r = s.gpr r := by
  simp [State.read, Size.bits]

theorem ofNat_bne_zero {k : Nat} (h0 : 0 < k) (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k != 0) = true := by
  rw [bne_iff_ne]
  intro h
  have h' := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at h'
  have h'' : k = 0 := h'
  omega_using [h0, h'']

theorem ofNat_sub_one {k : Nat} (h : 1 ≤ k) :
    BitVec.ofNat 64 k - BitVec.ofNat 64 1 = BitVec.ofNat 64 (k - 1) :=
  BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) h

/-- ShiftRows and SubBytes, in either order. -/
theorem shiftSub_st (v : BitVec 128) :
    st (aesMapBytes aesSbox (aesShiftRows v)) = shiftRows (subBytes (st v)) := by
  apply st_ext
  intro i hi
  have hs : i % 4 + 4 * ((i / 4 + i % 4) % 4) < 16 := by omega_arith
  rw [getD_st _ hi, getD_shiftRows _ hi, getD_subBytes _ hs, getD_st _ hs, vbyte_mapBytes _ _ hi,
    vbyte_shiftRows _ hi]
  exact congrFun VG.Proof.Aes.Vector.sbox_eq _

/-- A round key from the schedule, into `v5`. -/
theorem key_run (s : State) {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 off) 16) :
    ∃ t, runBlock isa [.ldrq .v5 .x0 off] s = some t ∧
      t.v .v5 = s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 off) 128 ∧ VOnly [.v5] s t :=
  ⟨s.setV .v5 (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 off) 128),
    by rw [runBlock_cons, Aese.exec_ldrq ho hin, runStep_some, runBlock_nil], v_setV_self _ _ _,
    VOnly.setV s (by simp) _⟩

/-- After `j` full rounds from the state `x`, with the key schedule at `K`:
the state `X` as `Lv X` in `v0`, `x0` at round key `j`, and `R − 1 − j` in
`x1`. -/
structure RInv (s₀ : State) (K : Addr) (R : Nat) (w : List Byte) (x : Spec.Aes.State) (j : Nat)
    (s : State) : Prop where
  consts : Consts s
  x0 : s.gpr .x0 = K + BitVec.ofNat 64 (16 * j)
  x1 : s.gpr .x1 = BitVec.ofNat 64 (R - 1 - j)
  st : ∃ X, s.v .v0 = Lv X ∧ st X = rnds w x j
  gpr : ∀ r, r ≠ .x0 → r ≠ .x1 → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- A full round. -/
theorem round_ok {s₀ : State} {K : Addr} {R : Nat} {x : Spec.Aes.State} (hK : (⟨K, 240⟩ : Region) ∈ s₀.rd)
    (hR : R ≤ 14) {j : Nat} (hj : j + 2 ≤ R) {s : State}
    (hI : RInv s₀ K R (bytesAt s₀.mem K (16 * (R + 1))) x j s) :
    WP isa (.block round) s (RInv s₀ K R (bytesAt s₀.mem K (16 * (R + 1))) x (j + 1)) := by
  obtain ⟨X, hX, hst⟩ := hI.st
  unfold round
  rw [show ([.addImm .x .x0 .x0 16, .ldrq .v5 .x0 0] : List Instr) =
    [.addImm .x .x0 .x0 16] ++ [.ldrq .v5 .x0 0] from rfl, List.append_assoc, List.append_assoc,
    List.append_assoc, List.append_assoc, WP.block_append_iff]
  let a := s.write .x .x0 (s.read .x .x0 + BitVec.ofNat 64 16)
  rw [WP.block_cons_iff]
  refine ⟨a, exec_addImm_x (imm := 16) (by decide), WP.block_nil ?_⟩
  have a0 : a.gpr .x0 = K + BitVec.ofNat 64 (16 * (j + 1)) := by
    rw [show a.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 16 by simp [a, State.write, read_x], hI.x0,
      BitVec.add_assoc, ← BitVec.ofNat_add]
    rfl
  have ard : a.rd = s₀.rd := hI.rd
  have amem : a.mem = s₀.mem := hI.mem
  have ac : Consts a := hI.consts.of_v fun _ _ => rfl
  rw [WP.block_append_iff]
  obtain ⟨b, hb, b5, ob⟩ := key_run a (off := 0) (by decide) ⟨_, List.mem_append_left _ (by rw [ard]; exact hK),
    by rw [a0, BitVec.add_zero]; exact Offset.contains_base K (by omega_arith) (by omega_arith)⟩
  refine WP.of_runBlock ⟨b, hb, ?_⟩
  have ob' : VOnly temps a b := vonly_mono ob (by decide)
  have bc : Consts b := ac.of_v ob'.2
  rw [WP.block_append_iff]
  obtain ⟨c, hc, c5, oc⟩ := keyx_run b bc (.inr ⟨rfl, rfl⟩)
  refine WP.of_runBlock ⟨c, hc, ?_⟩
  have oc' : VOnly temps b c := vonly_mono oc (by decide)
  have cc : Consts c := bc.of_v oc'.2
  rw [WP.block_append_iff]
  obtain ⟨d, hd, d2, d3, od⟩ := invert_run c cc
  refine WP.of_runBlock ⟨d, hd, ?_⟩
  have od' : VOnly temps c d := vonly_mono od (by decide)
  have dc : Consts d := cc.of_v od'.2
  rw [WP.block_append_iff]
  obtain ⟨e, he, e0, oe⟩ := mix_run d dc
  refine WP.of_runBlock ⟨e, he, ?_⟩
  have oe' : VOnly temps d e := vonly_mono oe (by decide)
  have o : VOnly temps a e := ((ob'.trans oc').trans od').trans oe'
  let f := e.write .x .x1 (e.read .x .x1 - BitVec.ofNat 64 1)
  rw [WP.block_cons_iff]
  refine ⟨f, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  have hk : KeyIs (a.mem.readW (a.gpr .x0 + BitVec.ofNat 64 0) 128)
      (roundKey (bytesAt s₀.mem K (16 * (R + 1))) (j + 1)) := by
    rw [a0, BitVec.add_zero, amem]
    exact keyIs_readW s₀.mem K (by omega_arith)
  have c0 : c.v .v0 = Lv X := by
    rw [oc.2 _ (by decide), ob.2 _ (by decide)]
    exact hX
  have d5 : d.v .v5 = LcV (a.mem.readW (a.gpr .x0 + BitVec.ofNat 64 0) 128) := by
    rw [od.2 _ (by decide), c5, b5]
  have ex1 : e.gpr .x1 = BitVec.ofNat 64 (R - 1 - j) := by
    rw [o.gpr, show a.gpr .x1 = s.gpr .x1 by simp [a, State.write]]; exact hI.x1
  refine ⟨dc.of_v oe'.2, ?_, ?_,
    ⟨aesMixColumns (aesMapBytes aesSbox (aesShiftRows X)) ^^^
      a.mem.readW (a.gpr .x0 + BitVec.ofNat 64 0) 128, ?_, ?_⟩, fun r h0 h1 => ?_, o.mem.trans amem, o.rd.trans ard,
    o.wr.trans hI.wr, (VOnly.sp o).trans hI.sp⟩
  · rw [show f.gpr .x0 = e.gpr .x0 by simp [f, State.write], o.gpr]; exact a0
  · rw [show f.gpr .x1 = e.gpr .x1 - BitVec.ofNat 64 1 by simp [f, State.write, read_x], ex1,
      ofNat_sub_one (by omega_arith), Nat.sub_sub]
  · rw [show f.v .v0 = e.v .v0 from rfl, e0, d2, d3, d5, c0]
    exact mixV_eq _ _
  · rw [eor_st hk, aesmc_st, shiftSub_st, hst, rnds_succ]
  · rw [show f.gpr r = e.gpr r by simp [f, State.write, h1], o.gpr,
      show a.gpr r = s.gpr r by simp [a, State.write, h0]]
    exact hI.gpr r h0 h1

/-- The full rounds: `R − 1` of them. -/
theorem loop_ok {s₀ : State} {K : Addr} {R : Nat} {x : Spec.Aes.State} (hK : (⟨K, 240⟩ : Region) ∈ s₀.rd)
    (hR : R ≤ 14) (hR2 : 2 ≤ R) {s : State} (hI : RInv s₀ K R (bytesAt s₀.mem K (16 * (R + 1))) x 0 s) :
    WP isa (.loop (.block round) (.nonzero .x .x1)) s
      (RInv s₀ K R (bytesAt s₀.mem K (16 * (R + 1))) x (R - 1)) := by
  refine WP.loop (M := isa) (fun n t => ∃ j, n = R - 1 - j ∧ j + 2 ≤ R ∧
    RInv s₀ K R (bytesAt s₀.mem K (16 * (R + 1))) x j t) ?_ (R - 1) s ⟨0, rfl, hR2, hI⟩
  rintro n t ⟨j, hn, hj, hI⟩
  refine WP.mono (round_ok hK hR hj hI) fun t' hI' => ?_
  have he : isa.eval (.nonzero .x .x1) t' = some (BitVec.ofNat 64 (R - 1 - (j + 1)) != 0) := by
    simp [AArch64.eval, State.read, hI'.x1]
  rcases Nat.lt_or_ge (j + 2) R with h | h
  · exact .inr ⟨by rw [he, ofNat_bne_zero (by omega_arith) (by omega_arith)], R - 1 - (j + 1), by omega_arith,
      j + 1, rfl, h, hI'⟩
  · have e : j + 1 = R - 1 := by omega_arith
    refine .inl ⟨by rw [he, show R - 1 - (j + 1) = 0 by omega_arith]; rfl, ?_⟩
    rw [← e]; exact hI'

/-- The last round. -/
theorem last_ok {s₀ : State} {K : Addr} {R : Nat} {x : Spec.Aes.State} (hK : (⟨K, 240⟩ : Region) ∈ s₀.rd)
    (hR : R ≤ 14) (hR2 : 2 ≤ R) {s : State}
    (hI : RInv s₀ K R (bytesAt s₀.mem K (16 * (R + 1))) x (R - 1) s) :
    WP isa (.block (([.ldrq .v5 .x0 16] : List Instr) ++ invert ++ last)) s fun t =>
      st (t.v .v0) = cipher R (bytesAt s₀.mem K (16 * (R + 1))) x ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → t.gpr r = s₀.gpr r) ∧ t.mem = s₀.mem ∧ t.rd = s₀.rd ∧ t.wr = s₀.wr ∧
      t.sp = s₀.sp := by
  obtain ⟨X, hX, hst⟩ := hI.st
  rw [List.append_assoc, WP.block_append_iff]
  have ea : s.gpr .x0 + BitVec.ofNat 64 16 = K + BitVec.ofNat 64 (16 * R) := by
    rw [hI.x0, BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * (R - 1) + 16 = 16 * R by omega_arith]
  obtain ⟨b, hb, b5, ob⟩ := key_run s (off := 16) (by decide)
    ⟨_, List.mem_append_left _ (by rw [hI.rd]; exact hK),
      by rw [ea]; exact Offset.contains_base K (by omega_arith) (by omega_arith)⟩
  refine WP.of_runBlock ⟨b, hb, ?_⟩
  have ob' : VOnly temps s b := vonly_mono ob (by decide)
  have bc : Consts b := hI.consts.of_v ob'.2
  rw [WP.block_append_iff]
  obtain ⟨d, hd, d2, d3, od⟩ := invert_run b bc
  refine WP.of_runBlock ⟨d, hd, ?_⟩
  have od' : VOnly temps b d := vonly_mono od (by decide)
  have dc : Consts d := bc.of_v od'.2
  obtain ⟨t, ht, t0, ot⟩ := last_run d dc
  have ot' : VOnly temps d t := vonly_mono ot (by decide)
  have o : VOnly temps s t := (ob'.trans od').trans ot'
  refine WP.of_runBlock ⟨t, ht, ?_, fun r h0 h1 => ?_, o.mem.trans hI.mem, o.rd.trans hI.rd,
    o.wr.trans hI.wr, (VOnly.sp o).trans hI.sp⟩
  · have hk : KeyIs (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 16) 128)
        (roundKey (bytesAt s₀.mem K (16 * (R + 1))) R) := by
      rw [ea, hI.mem]
      exact keyIs_readW s₀.mem K (by omega_arith)
    rw [t0, d2, d3, od.2 _ (by decide), b5, show b.v .v0 = s.v .v0 from ob.2 _ (by decide), hX, lastV_eq,
      eor_st hk, shiftSub_st, hst]
    rfl
  · rw [o.gpr]; exact hI.gpr r h0 h1

/-- `first`: the block and the first round key. -/
theorem first_ok {s : State} {K : Addr} {R : Nat} (hc : Consts s) (hK : (⟨K, 240⟩ : Region) ∈ s.rd)
    (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (hR : 2 ≤ R ∧ R ≤ 14) :
    WP isa (.block first) s (RInv s K R (bytesAt s.mem K (16 * (R + 1))) (st (s.v .v0)) 0) := by
  unfold first
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  obtain ⟨a, ha, a5, oa⟩ := key_run s (off := 0) (by decide) ⟨_, List.mem_append_left _ hK,
    by rw [h0]; exact Offset.contains_base K (by decide) (by decide)⟩
  refine WP.of_runBlock ⟨a, ha, ?_⟩
  have oa' : VOnly temps s a := vonly_mono oa (by decide)
  have ac : Consts a := hc.of_v oa'.2
  rw [WP.block_append_iff]
  obtain ⟨b, hb, b0, ob⟩ := keyx_run a ac (.inl ⟨rfl, rfl⟩)
  refine WP.of_runBlock ⟨b, hb, ?_⟩
  have ob' : VOnly temps a b := vonly_mono ob (by decide)
  have bc : Consts b := ac.of_v ob'.2
  rw [WP.block_append_iff]
  obtain ⟨c, hc', c5, oc⟩ := keyx_run b bc (.inr ⟨rfl, rfl⟩)
  refine WP.of_runBlock ⟨c, hc', ?_⟩
  have oc' : VOnly temps b c := vonly_mono oc (by decide)
  have o : VOnly temps s c := (oa'.trans ob').trans oc'
  let d := c.setV .v0 (c.v .v0 ^^^ c.v .v5)
  let f := d.write .x .x1 (d.read .x .x1 - BitVec.ofNat 64 1)
  rw [WP.block_cons_iff]
  refine ⟨d, exec_eorv _ _ _ _, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨f, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  have hk : KeyIs (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 0) 128)
      (roundKey (bytesAt s.mem K (16 * (R + 1))) 0) := by
    have h := keyIs_readW s.mem K (L := 16 * (R + 1)) (j := 0) (by omega_arith)
    rw [Nat.mul_zero] at h
    rw [h0]
    exact h
  have dg : d.gpr = s.gpr := o.gpr
  refine ⟨(bc.of_v oc'.2).of_v fun r hr => v_setV_of_ne _ _ (fun e => hr (e ▸ by decide)), ?_, ?_,
    ⟨s.v .v0 ^^^ s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 0) 128, ?_, ?_⟩, fun r _ h1 => ?_, o.mem, o.rd,
    o.wr, (VOnly.sp o :)⟩
  · rw [show f.gpr .x0 = d.gpr .x0 by simp [f, State.write], dg, h0]
    exact (BitVec.add_zero K).symm
  · rw [show f.gpr .x1 = d.gpr .x1 - BitVec.ofNat 64 1 by simp [f, State.write, read_x], dg, h1,
      ofNat_sub_one (by omega_arith)]
    rfl
  · rw [show f.v .v0 = d.v .v0 from rfl, show d.v .v0 = c.v .v0 ^^^ c.v .v5 from v_setV_self _ _ _, c5, oc.2 _ (by decide), b0,
      show b.v .v5 = a.v .v5 from ob.2 _ (by decide), a5, show a.v .v0 = s.v .v0 from oa.2 _ (by decide)]
    exact first_eq _ _
  · rw [eor_st hk, rnds_zero]
  · rw [show f.gpr r = d.gpr r by simp [f, State.write, h1], dg]

/-- `core` is the cipher, on the state in `v0`, with the schedule at `x0`
and the rounds in `x1`. -/
theorem core_ok {s : State} {K : Addr} {R : Nat} (hK : (⟨K, 240⟩ : Region) ∈ s.rd) (h0 : s.gpr .x0 = K)
    (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    WP isa core s fun t =>
      st (t.v .v0) = cipher R (bytesAt s.mem K (16 * (R + 1))) (st (s.v .v0)) ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x6 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.sp = s.sp := by
  have hR14 : R ≤ 14 := by omega_arith
  have hR2 : 2 ≤ R := by omega_arith
  unfold core
  refine WP.seq (WP.mono (setup_ok s) fun a ⟨ac, a0, ag, am, ard, awr, asp⟩ => ?_)
  have hKa : (⟨K, 240⟩ : Region) ∈ a.rd := by rw [ard]; exact hK
  unfold rounds
  refine WP.seq (WP.mono (first_ok ac hKa ((ag _ (by decide)).trans h0) ((ag _ (by decide)).trans h1)
    ⟨hR2, hR14⟩) fun c hI => ?_)
  refine WP.seq (WP.mono (loop_ok hKa hR14 hR2 hI) fun d hd => ?_)
  refine WP.mono (last_ok hKa hR14 hR2 hd) fun t ⟨tst, tg, tm, trd, twr, tsp⟩ => ?_
  refine ⟨by rw [tst, am, a0], fun r h0 h1 h6 => (tg r h0 h1).trans (ag r h6), tm.trans am,
    trd.trans ard, twr.trans awr, tsp.trans asp⟩

/-! ## Decryption: one byte -/

namespace Dec

open VG.Impl.Aes.AArch64.Vperm.Dec
open VG.Proof.Aes.Vector (vbyte_invShiftRows vbyte_invMixColumns st_aesimc st_invSub)

/-- The byte `x`, as the decryption's state holds it. -/
def D (x : BitVec 8) : BitVec 8 := nib dh (x >>> 4) ^^^ nib dl (x &&& 0x0f)

/-- `D`, less `D 0`: it is linear. -/
def Dl (x : BitVec 8) : BitVec 8 := D x ^^^ 0xd1

/-- The inverse S-box, from the tables. -/
theorem isb_eq : ∀ z : BitVec 8,
    aesInvSbox z = nib dbou (ioB (D z)) ^^^ nib dbot (joB (D z)) := by decide +kernel

theorem x0_tab : ∀ z : BitVec 8, nib x0u (ioB (D z)) ^^^ nib x0t (joB (D z)) =
    Dl (aesMul 0x0e (nib dbou (ioB (D z)) ^^^ nib dbot (joB (D z)))) := by decide +kernel
theorem x1_tab : ∀ z : BitVec 8, nib x1u (ioB (D z)) ^^^ nib x1t (joB (D z)) =
    Dl (aesMul 0x0b (nib dbou (ioB (D z)) ^^^ nib dbot (joB (D z)))) := by decide +kernel
theorem x2_tab : ∀ z : BitVec 8, nib x2u (ioB (D z)) ^^^ nib x2t (joB (D z)) =
    Dl (aesMul 0x0d (nib dbou (ioB (D z)) ^^^ nib dbot (joB (D z)))) := by decide +kernel
theorem x3_tab : ∀ z : BitVec 8, nib x3u (ioB (D z)) ^^^ nib x3t (joB (D z)) =
    Dl (aesMul 0x09 (nib dbou (ioB (D z)) ^^^ nib dbot (joB (D z)))) := by decide +kernel

/-- A round key's byte, through a pair of the tables. -/
def Yb (l h : BitVec 128) (x : BitVec 8) : BitVec 8 := nib l (x &&& 0x0f) ^^^ nib h (x >>> 4)

theorem y0_tab : ∀ x : BitVec 8, Yb y0l y0h x = D (aesMul 0x0e x) := by decide +kernel
theorem y1_tab : ∀ x : BitVec 8, Yb y1l y1h x = Dl (aesMul 0x0b x) := by decide +kernel
theorem y2_tab : ∀ x : BitVec 8, Yb y2l y2h x = Dl (aesMul 0x0d x) := by decide +kernel
theorem y3_tab : ∀ x : BitVec 8, Yb y3l y3h x = Dl (aesMul 0x09 x) := by decide +kernel

theorem Dl_bits : ∀ x : BitVec 8, Dl x = bits Dl x := by decide +kernel
theorem g0_bits : ∀ x : BitVec 8,
    Dl (aesMul 0x0e x) = bits (fun x => Dl (aesMul 0x0e x)) x := by decide +kernel
theorem g1_bits : ∀ x : BitVec 8,
    Dl (aesMul 0x0b x) = bits (fun x => Dl (aesMul 0x0b x)) x := by decide +kernel
theorem g2_bits : ∀ x : BitVec 8,
    Dl (aesMul 0x0d x) = bits (fun x => Dl (aesMul 0x0d x)) x := by decide +kernel
theorem g3_bits : ∀ x : BitVec 8,
    Dl (aesMul 0x09 x) = bits (fun x => Dl (aesMul 0x09 x)) x := by decide +kernel

/-- A byte of a round: InvMixColumns of the inverse S-box's bytes `u₀`, …,
`u₃` of a column, each XORed with the round key's byte, under `D`. -/
theorem imix_byte (u₀ u₁ u₂ u₃ k₀ k₁ k₂ k₃ : BitVec 8) :
    Dl (aesMul 0x0e u₀) ^^^ Dl (aesMul 0x0b u₁) ^^^
        (D (aesMul 0x0e k₀) ^^^ Dl (aesMul 0x0b k₁) ^^^ Dl (aesMul 0x0d k₂) ^^^ Dl (aesMul 0x09 k₃)) ^^^
        (Dl (aesMul 0x0d u₂) ^^^ Dl (aesMul 0x09 u₃)) =
      D (aesMul 0x0e (u₀ ^^^ k₀) ^^^ aesMul 0x0b (u₁ ^^^ k₁) ^^^ aesMul 0x0d (u₂ ^^^ k₂) ^^^
        aesMul 0x09 (u₃ ^^^ k₃)) := by
  have hD : ∀ x, D x = Dl x ^^^ 0xd1 := fun x => by
    rw [Dl, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  rw [hD, hD, xor_of_bits Dl_bits, xor_of_bits Dl_bits, xor_of_bits Dl_bits,
    xor_of_bits (f := fun x => Dl (aesMul 0x0e x)) g0_bits, xor_of_bits (f := fun x => Dl (aesMul 0x0b x)) g1_bits,
    xor_of_bits (f := fun x => Dl (aesMul 0x0d x)) g2_bits, xor_of_bits (f := fun x => Dl (aesMul 0x09 x)) g3_bits]
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
  have h1 := rI_lt 1 (by decide) e he
  have h2 := rI_lt 2 (by decide) e he
  have h3 := rI_lt 3 (by decide) e he
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
  have hs := isrI_lt _ (rI_lt n hn e he)
  rw [xV, vbyte_perm _ he (hp e he) hs, vbyte_xor, vbyte_tblV _ _ hs, vbyte_tblV _ _ hs, vbyte_ioV _ hs,
    vbyte_joV _ hs, vbyte_Dv _ hs, ht, isb_eq]

/-- `invert` and `mix` are a round of the inverse cipher, on the bytes
under `D`. -/
theorem mixV_eq (x k : BitVec 128) :
    mixV (ioV (Dv x)) (joV (Dv x)) (keyV k) =
      Dv (aesInvMixColumns (aesMapBytes aesInvSbox (aesInvShiftRows x) ^^^ k)) := by
  apply ext_vbyte
  intro e he
  have h0 := rI_lt 0 (by decide) e he
  have h1 := rI_lt 1 (by decide) e he
  have h2 := rI_lt 2 (by decide) e he
  have h3 := rI_lt 3 (by decide) e he
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
  have hs := isrI_lt _ (rI_lt 0 (by decide) e he)
  rw [lastV, vbyte_xor, vbyte_perm _ he (p_p0 e he) hs, vbyte_xor, vbyte_tblV _ _ hs, vbyte_tblV _ _ hs,
    vbyte_ioV _ hs, vbyte_joV _ hs, vbyte_Dv _ hs, ← isb_eq, vbyte_xor, vbyte_mapBytes _ _ he,
    vbyte_invShiftRows _ he, rI_zero e he]
  rfl

end Dec

end VG.Proof.Aes.AArch64.Vperm
