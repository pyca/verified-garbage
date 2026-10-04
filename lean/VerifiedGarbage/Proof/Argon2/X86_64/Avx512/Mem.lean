import VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Gb
import VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Rows

/-!
# Argon2 on x86-64 with AVX-512: 64-byte loads and stores

Quadword `k` of a register after a 64-byte load (`qz_load`), of a register
as a stored value (`zmm_qz`), and a word of memory after a 64-byte store
(`read_write512`); the block P permutes as scratch holds it, by pairs of
columns (`cv`, with the word of each quadword of each 64-byte chunk:
`cvIdx`).
-/

namespace VG.Proof.Argon2.X86_64.Avx512

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64 (at_)
open VG.Impl.Argon2.X86_64.Avx512
open VG.Proof.Argon2.X86_64 (off Scratch ea_at)
open VG.Proof.Argon2.X86_64.Avx2 (VKeep)
open VG.Proof.Poly1305.X86_64.Avx512 (qz)

/-! ## Registers -/

theorem qz_setMem (s : State) (m : Mem) (r : XReg) (k : Nat) : qz (s.setMem m) r k = qz s r k := by
  simp only [qz, State.setMem_zlane]

theorem qword_extract512 (v : BitVec 512) (l : Nat) {i : Nat} (hi : i < 2) :
    qword (v.extractLsb' (128 * l) 128) i = v.extractLsb' (64 * (2 * l + i)) 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [qword, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    decide_eq_true (show 64 * i + j < 128 by omega)]
  congr 1; omega

theorem pick4_extract (v : BitVec 512) {l : Nat} (hl : l < 4) :
    pick4 (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128)
      (v.extractLsb' 384 128) l = v.extractLsb' (128 * l) 128 := by
  have := pick4_lanes (fun l => v.extractLsb' (128 * l) 128) hl
  simpa only [Nat.reduceMul] using this

theorem qz_setZ_load (s : State) (d r : XReg) (v : BitVec 512) {k : Nat} (hk : k < 8) :
    qz (s.setZ d (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128)
      (v.extractLsb' 384 128)) r k = if r = d then v.extractLsb' (64 * k) 64 else qz s r k := by
  simp only [qz, State.zlane_setZ _ _ _ _ _ _ _ (show k / 2 < 4 by omega)]
  split
  · rw [pick4_extract _ (show k / 2 < 4 by omega), qword_extract512 _ _ (Nat.mod_lt _ (by decide)),
      show 2 * (k / 2) + k % 2 = k by omega]
  · rfl

theorem qz_load (s : State) (d r : XReg) (m : Mem) (a : Addr) {k : Nat} (hk : k < 8) :
    qz (s.setZ d ((m.readW a 512).extractLsb' 0 128) ((m.readW a 512).extractLsb' 128 128)
      ((m.readW a 512).extractLsb' 256 128) ((m.readW a 512).extractLsb' 384 128)) r k =
      if r = d then m.readW (a + BitVec.ofNat 64 (8 * k)) 64 else qz s r k := by
  rw [qz_setZ_load _ _ _ _ hk, show 64 * k = 8 * (8 * k) by omega,
    readW_extract _ _ (k := 8 * k) (n := 8) (by omega)]

/-- Quadword `k` of a register, as a stored value. -/
theorem extract64_split (x : BitVec 512) (a : Nat) :
    x.extractLsb' a 64 = x.extractLsb' (a + 32) 32 ++ x.extractLsb' a 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true, Bool.true_and]
  split
  · rename_i h
    rw [decide_eq_true h, Bool.true_and]
  · rw [decide_eq_true (show j - 32 < 32 by omega), Bool.true_and]
    congr 1; omega

theorem zmm_qz (s : State) (r : XReg) {k : Nat} (hk : k < 8) :
    (s.zmm r).extractLsb' (64 * k) 64 = qz s r k := by
  have e0 : (s.zmm r).extractLsb' (64 * k) 32 = dword (s.zlane r (k / 2)) (2 * (k % 2)) := by
    have := State.zmm_extract s r (l := k / 2) (q := 2 * (k % 2)) (by omega) (by omega)
    rw [show 8 * (16 * (k / 2) + 4 * (2 * (k % 2))) = 64 * k by omega] at this
    exact this
  have e1 : (s.zmm r).extractLsb' (64 * k + 32) 32 = dword (s.zlane r (k / 2)) (2 * (k % 2) + 1) := by
    have := State.zmm_extract s r (l := k / 2) (q := 2 * (k % 2) + 1) (by omega) (by omega)
    rw [show 8 * (16 * (k / 2) + 4 * (2 * (k % 2) + 1)) = 64 * k + 32 by omega] at this
    exact this
  rw [qz, Proof.Poly1305.X86_64.Avx2.qword_eq, extract64_split, e0, e1]

/-! ## Memory -/

/-- A word at `p + d` after 64 bytes are written at `p + e`. -/
theorem read_write512 (m : Mem) (p : Addr) {d e : Nat} (hd : d + 8 ≤ 4096) (he : e + 64 ≤ 4096)
    (h8 : d % 8 = 0) (he8 : e % 8 = 0) (v : BitVec 512) :
    (m.writeW (off p e) v).readW (off p d) 64 =
      if e ≤ d ∧ d < e + 64 then v.extractLsb' (64 * ((d - e) / 8)) 64 else m.readW (off p d) 64 := by
  split
  · rename_i h
    rw [show off p d = off p e + BitVec.ofNat 64 (8 * ((d - e) / 8)) from
      (Offset.add_add_eq p (by omega)).symm]
    refine (readW_writeW_inside _ _ v (k := 8 * ((d - e) / 8)) (n := 8) (by omega) (by decide)).trans ?_
    rw [show 8 * (8 * ((d - e) / 8)) = 64 * ((d - e) / 8) by omega]
  · exact readW_writeW_off m p v (n := 8) (by omega) (by omega) (by omega)

/-- The offset in `[1024, 2048)` of scratch of word `i` of the block P
permutes: in register `i / 32` of columns `2c`, `2c + 1` (`c = i % 16 / 4`),
quadword `cvQ i`. -/
def cvQ (i : Nat) : Nat := 4 * (i % 16 / 2 % 2) + 2 * (i / 16 % 2) + i % 2

def cvOff (i : Nat) : Nat := 256 * (i % 16 / 4) + 64 * (i / 32) + 8 * cvQ i

/-- The block P permutes, as scratch holds it. -/
def cv (m : Mem) (p : Addr) : Block := Vector.ofFn fun i => m.readW (off p (1024 + cvOff i.val)) 64

theorem cv_get (m : Mem) (p : Addr) (i : Nat) (hi : i < 128) :
    (cv m p)[i] = m.readW (off p (1024 + cvOff i)) 64 := by
  simp only [cv, Vector.getElem_ofFn]

/-- Where the words are, as bounded facts. -/
theorem cvOff_lt : ∀ i < 128, cvOff i + 8 ≤ 1024 ∧ cvOff i % 8 = 0 := by decide

theorem cvOff_in : ∀ i < 128, ∀ c < 4, ∀ k < 4,
    (1024 + 256 * c + 64 * k ≤ 1024 + cvOff i ∧ 1024 + cvOff i < 1024 + 256 * c + 64 * k + 64 ↔
      i % 16 / 4 = c ∧ i / 32 = k) := by decide

theorem cvOff_q : ∀ i < 128, (1024 + cvOff i - (1024 + 256 * (i % 16 / 4) + 64 * (i / 32))) / 8 = cvQ i := by
  decide

theorem cvQ_lt : ∀ i < 128, cvQ i < 8 := by decide

/-- The word of quadword `e` of register `k` of columns `2c`, `2c + 1`: word
`4k + e % 4` of column `2c + e / 4`. -/
def cvIdx (c k e : Nat) : Nat := 16 * (2 * k + e % 4 / 2) + 4 * c + 2 * (e / 4) + e % 2

theorem cvIdx_colIndex {c k e : Nat} (hc : c < 4) (hk : k < 4) (he : e < 8) :
    (colIndex ⟨2 * c + e / 4, by omega⟩ ⟨4 * k + e % 4, by omega⟩).val = cvIdx c k e := by
  simp only [colIndex, cvIdx]; omega

theorem cvOff_cvIdx : ∀ c < 4, ∀ k < 4, ∀ e < 8, cvOff (cvIdx c k e) = 256 * c + 64 * k + 8 * e := by
  decide

theorem cvIdx_lt {c k e : Nat} (hc : c < 4) (hk : k < 4) (he : e < 8) : cvIdx c k e < 128 := by
  simp only [cvIdx]; omega

/-- A word of `cv` after a 64-byte write to the chunk at `colOff c k`. -/
theorem cv_write512 (m : Mem) (p : Addr) {c k : Nat} (hc : c < 4) (hk : k < 4) (v : BitVec 512)
    (i : Nat) (hi : i < 128) :
    (cv (m.writeW (off p (colOff c k)) v) p)[i] =
      if i % 16 / 4 = c ∧ i / 32 = k then v.extractLsb' (64 * cvQ i) 64 else (cv m p)[i] := by
  have ho := cvOff_lt i hi
  rw [cv_get _ _ _ hi, cv_get _ _ _ hi, colOff, read_write512 _ _ (by omega) (by omega)
    (by omega) (by omega)]
  by_cases h : i % 16 / 4 = c ∧ i / 32 = k
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ((cvOff_in i hi c hc k hk).mpr h)),
      ite_eq_left_of_eq_true _ _ (eq_true h), ← h.1, ← h.2, cvOff_q i hi]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (mt (cvOff_in i hi c hc k hk).mp h)),
      ite_eq_right_of_eq_false _ _ (eq_false h)]

/-- The register of columns `2c`, `2c + 1` at `colOff c k`, as `cv` holds it. -/
theorem cv_chunk (m : Mem) (p : Addr) {c k e : Nat} (hc : c < 4) (hk : k < 4) (he : e < 8) :
    m.readW (off p (colOff c k) + BitVec.ofNat 64 (8 * e)) 64 =
      (cv m p)[cvIdx c k e]'(cvIdx_lt hc hk he) := by
  rw [cv_get _ _ _ (cvIdx_lt hc hk he), cvOff_cvIdx c hc k hk e he, Offset.add_add, colOff,
    show 1024 + 256 * c + 64 * k + 8 * e = 1024 + (256 * c + 64 * k + 8 * e) by omega]

end VG.Proof.Argon2.X86_64.Avx512
