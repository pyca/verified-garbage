module

import VerifiedGarbage.Proof.Framework.Offset

import VerifiedGarbage.Proof.Sha256.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Lit
import Mathlib.Data.List.Nodup
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Sha256.Spec
public import VerifiedGarbage.Impl.Sha256.PPC64LE
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# SHA-256 compression function on PPC64LE: the message schedule and the rounds

Untrusted: everything here is checked by Lean.
-/

@[expose] public section

namespace VG.Proof.Sha256.PPC64LE

open VG VG.PPC64LE VG.Impl.Sha256.PPC64LE
open VG.Spec.Sha256 (HashValue Word Block K W bsig0 bsig1 ch maj ssig0 ssig1)

private theorem zero_or128 (x : BitVec 128) : (0 : BitVec 128) ||| x = x := BitVec.zero_or

theorem packed_words (f : Nat → BitVec 32) :
    (List.range 4).foldl (fun x i => x ||| ((f i).setWidth 128 <<< (32*(3-i)))) (0 : BitVec 128) =
      f 0 ++ f 1 ++ f 2 ++ f 3 := by
  simp only [show List.range 4 = [0,1,2,3] from rfl, List.foldl_cons, List.foldl_nil,
    Nat.reduceSub, Nat.reduceMul, zero_or128, BitVec.shiftLeft_zero]
  have h := BitVec.setWidth_append_append_append_eq_shiftLeft_setWidth_or
    (b := f 0) (b' := f 1) (b'' := f 2) (b''' := f 3) (w'''' := 128)
  rw [BitVec.setWidth_eq] at h
  exact h.symm

theorem vword_dword (x : BitVec 128) (j : Nat) (hj : j < 4) :
    vword x j = (vdword x (j/2)).extractLsb' (32*(1-j%2)) 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb : 32*(1-j%2)+i < 64 := by omega
  have he : 32*(3-j)+i = 64*(1-j/2)+(32*(1-j%2)+i) := by omega
  simp only [vword, vdword, BitVec.getLsbD_extractLsb', hi, hb, decide_true,
    Bool.true_and, he]

theorem widen32_eq (x : BitVec 32) : x.setWidth 64 = (0#32) ++ x := by
  have h := BitVec.setWidth_eq_append (x := x) (w := 64) (by decide)
  simpa only [Nat.reduceSub, BitVec.cast_eq] using h

theorem packed_pairs (f : Nat → BitVec 32) :
    (List.range 4).foldl (fun x i => x ||| ((f i).setWidth 128 <<< (32*(3-i)))) (0 : BitVec 128) =
      (f 0 ++ f 1) ++ (f 2 ++ f 3) := by
  rw [packed_words]
  simpa only [BitVec.cast_eq] using (BitVec.append_assoc (x₁ := f 0 ++ f 1) (x₂ := f 2) (x₃ := f 3))


theorem pair_words (x : BitVec 128) (a : BitVec 32) (j : Nat) (hj : j < 2)
    (h : vdword x j = a.setWidth 64) :
    vword x (2*j) = 0#32 ∧ vword x (2*j+1) = a := by
  constructor
  · rw [vword_dword x (2*j) (by omega)]
    simp only [show 2*j/2 = j by omega, show 2*j%2 = 0 by omega,
      Nat.reduceSub, Nat.reduceMul, h, widen32_eq, BitVec.extractLsb'_append_eq_left]
  · rw [vword_dword x (2*j+1) (by omega)]
    simp only [show (2*j+1)/2 = j by omega, show (2*j+1)%2 = 1 by omega,
      Nat.reduceSub, Nat.reduceMul, h, widen32_eq, BitVec.extractLsb'_append_eq_right]

theorem high64_packed (f : Nat → BitVec 32) :
    vdword ((List.range 4).foldl (fun x i => x ||| ((f i).setWidth 128 <<< (32*(3-i))))
      (0 : BitVec 128)) 0 = f 0 ++ f 1 := by
  rw [packed_pairs]
  exact BitVec.extractLsb'_append_eq_left

theorem sigma256_zero : ∀ st one, sigma256 st one 0#32 = 0#32 := by decide

theorem high64_add32 (x y : BitVec 128) (a b : BitVec 32)
    (hx : vdword x 0 = a.setWidth 64) (hy : vdword y 0 = b.setWidth 64) :
    vdword ((List.range 4).foldl (fun z i => z |||
      ((vword x i + vword y i).setWidth 128 <<< (32*(3-i)))) (0 : BitVec 128)) 0 =
      (a+b).setWidth 64 := by
  have ⟨hx0,hx1⟩ := pair_words x a 0 (by decide) hx
  have ⟨hy0,hy1⟩ := pair_words y b 0 (by decide) hy
  rw [high64_packed]
  simp only [Nat.mul_zero, Nat.zero_add] at hx0 hx1 hy0 hy1
  rw [hx0, hx1, hy0, hy1, BitVec.zero_add, ←widen32_eq]

theorem high64_sigma32 (x : BitVec 128) (a : BitVec 32) (st one : Bool)
    (hx : vdword x 0 = a.setWidth 64) :
    vdword ((List.range 4).foldl (fun z i => z |||
      ((sigma256 st ((if one then 5 else 0).testBit (3-i)) (vword x i)).setWidth 128 <<<
        (32*(3-i)))) (0 : BitVec 128)) 0 = (sigma256 st one a).setWidth 64 := by
  have ⟨hx0,hx1⟩ := pair_words x a 0 (by decide) hx
  simp only [Nat.mul_zero, Nat.zero_add] at hx0 hx1
  have hm0 : (if one then 5 else 0).testBit 3 = false := by cases one <;> decide
  have hm1 : (if one then 5 else 0).testBit 2 = one := by cases one <;> decide
  rw [high64_packed]
  simp only [Nat.reduceSub, hm0, hm1, hx0, hx1, sigma256_zero, ←widen32_eq]


/-- Each working word is zero-padded to a doubleword in a vector. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  vdword (s.vpr (vvar t 0)) 0 = v[0].setWidth 64 ∧
  vdword (s.vpr (vvar t 1)) 0 = v[1].setWidth 64 ∧
  vdword (s.vpr (vvar t 2)) 0 = v[2].setWidth 64 ∧
  vdword (s.vpr (vvar t 3)) 0 = v[3].setWidth 64 ∧
  vdword (s.vpr (vvar t 4)) 0 = v[4].setWidth 64 ∧
  vdword (s.vpr (vvar t 5)) 0 = v[5].setWidth 64 ∧
  vdword (s.vpr (vvar t 6)) 0 = v[6].setWidth 64 ∧
  vdword (s.vpr (vvar t 7)) 0 = (v[7] + roundBias t).setWidth 64

def pubRegs : List Reg := [.r3, .r4, .r5, .r6, .r2, .r18, .r20, .r21, .r22, .r23, .r24, .r25, .r26,
  .r27, .r28, .r29, .r30, .r31]

theorem sigma256_bsig0 (x : Word) : VG.PPC64LE.sigma256 true false x = bsig0 x := rfl

theorem sigma256_bsig1 (x : Word) : VG.PPC64LE.sigma256 true true x = bsig1 x := rfl

theorem t1_biased_add_tree (h k w s c : Word) :
    (h+k)+w+c+s = h+s+c+k+w := by ac_rfl

theorem vvar_succ (t k : Nat) (hk : k < 7) : vvar (t + 1) (k + 1) = vvar t k := by
  simp only [vvar]; congr 1; omega

theorem vvar_succ_zero (t : Nat) : vvar (t + 1) 0 = vvar t 7 := by
  simp only [vvar]; congr 1; omega

theorem vround_nodup (t : Nat) :
    ([vvar t 0, vvar t 1, vvar t 2, vvar t 3, vvar t 4, vvar t 5, vvar t 6, vvar t 7,
      .v12, .v13, .v14, .v15] : List VReg).Nodup := by
  simp only [vvar]
  have := Nat.mod_lt t (show 8 > 0 by omega)
  generalize t % 8 = c at *
  revert this; revert c; decide

theorem vvar_mem (t k : Nat) : vvar t k ∈ vwork := by
  unfold vvar List.getD
  cases h : vwork[(k + 8 - t % 8) % 8]?
  · simp [vwork]
  · exact List.mem_of_getElem? h

theorem round_pairs_frame (t : Nat) : ∀ r ∈ pairs,
    r ≠ vvar t 3 ∧ r ≠ vvar t 7 ∧ r ≠ vvar t 6 ∧ r ≠ .v12 ∧ r ≠ .v13 ∧ r ≠ .v14 ∧ r ≠ .v15 := by
  intro r hr
  have h : ∀ a ∈ vwork, r ≠ a := by
    intro a ha
    have h : ∀ a ∈ vwork, ∀ b ∈ pairs, a ≠ b := by decide
    exact (h a ha r hr).symm
  have ht : ∀ r ∈ pairs, r ≠ .v12 ∧ r ≠ .v13 ∧ r ≠ .v14 ∧ r ≠ .v15 := by decide
  exact ⟨h _ (vvar_mem t 3), h _ (vvar_mem t 7), h _ (vvar_mem t 6), ht r hr⟩

theorem ks_length : Spec.Sha256.Ks.length = 64 := by decide

theorem kWords_length : kWords.length = 66 := by
  simp only [kWords, List.length_append, List.length_map, ks_length,
    List.length_cons, List.length_nil, Nat.reduceAdd]

theorem map_widen_getD (xs : List Word) (j : Nat) :
    (xs.map (fun w => w.setWidth 64)).getD j 0 = (xs.getD j 0).setWidth 64 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases xs[j]? with
  | none => exact (by decide)
  | some w => rfl

theorem kWords_get (j : Nat) (hj : j ≤ 64) :
    kWords.getD j 0 = (roundBias j).setWidth 64 := by
  by_cases h : j < 64
  · simp only [kWords, roundBias, K, List.getD_eq_getElem?_getD,
      List.getElem?_append, List.length_map, ks_length, h, ite_true]
    exact map_widen_getD Spec.Sha256.Ks j
  · have he : j = 64 := by omega
    subst j
    simp only [kWords, roundBias, List.getD_eq_getElem?_getD, List.getElem?_append,
      List.length_map, ks_length, Nat.lt_irrefl, ite_false, Nat.sub_self,
      List.getElem?_cons_zero, Option.getD_some]
    decide

theorem kIndex_next (t : Nat) : kIndex t + BitVec.ofNat 64 8 = kIndex (t+1) := by
  unfold kIndex
  rw [← BitVec.ofNat_add]
  congr 1

theorem exec_kld (d : VReg) (j : Nat) (s : State) (hj : j ≤ 64)
    (hb : s.gpr .r18 = s.syms kSym) (hi : s.gpr .r19 = BitVec.ofNat 64 (8*j)) :
    exec (.lxvd2xTbl d .r18 .r19 kSym kWords) s =
      some (s.writeV d ((roundBias j).setWidth 64 ++ kWords.getD (j+1) 0)) := by
  have hin : (s.gpr .r19).toNat = 8*j := by
    rw [hi, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  simp only [reduceExec]
  rw [ite_eq_left ⟨by decide, hb, by rw [hin]; omega, by rw [hin, kWords_length]; omega⟩]
  rw [hin, show (8*j)/8 = j by omega, kWords_get j hj]


theorem high64_append (a b : BitVec 64) : (a ++ b).extractLsb' 64 64 = a :=
  BitVec.extractLsb'_append_eq_left

theorem high32_append (a b : BitVec 32) : (a ++ b).extractLsb' 32 32 = a :=
  BitVec.extractLsb'_append_eq_left

theorem low32_append (a b : BitVec 32) : (a ++ b).extractLsb' 0 32 = b :=
  BitVec.extractLsb'_append_eq_right

/-- The working state stays in vectors, so neither sigma needs a register-bank transfer. -/
theorem round_ok (t : Nat) (ht : t < 64) (s : State) (v : HashValue) (w : Word)
    (hb : s.gpr .r18 = s.syms kSym) (hi : s.gpr .r19 = kIndex t)
    (hv : Vars t s v) (hw : vdword (s.vpr .v15) 0 = w.setWidth 64) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) s' (roundKW v (K t) w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ pubRegs, s'.gpr r = s.gpr r) ∧
      (∀ r ∈ pairs, s'.vpr r = s.vpr r) ∧ s'.gpr .r19 = kIndex (t+1) := by
  have hpairs := round_pairs_frame t
  have hs := vround_nodup t
  have hs' := List.nodup_reverse.mpr hs
  simp only [Vars, vvar_succ_zero, vvar_succ t _ (show 0 < 7 by omega),
    vvar_succ t _ (show 1 < 7 by omega), vvar_succ t _ (show 2 < 7 by omega),
    vvar_succ t _ (show 3 < 7 by omega), vvar_succ t _ (show 4 < 7 by omega),
    vvar_succ t _ (show 5 < 7 by omega), vvar_succ t _ (show 6 < 7 by omega)] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  apply WP.of_runBlock
  simp only [Impl.Sha256.PPC64LE.round, Impl.Sha2.PPC64LE.round]
  generalize vvar t 0 = a at *
  generalize vvar t 1 = b at *
  generalize vvar t 2 = c at *
  generalize vvar t 3 = d at *
  generalize vvar t 4 = e at *
  generalize vvar t 5 = f at *
  generalize vvar t 6 = g at *
  generalize vvar t 7 = h at *
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, or_false, not_or,
    List.nodup_nil, and_true] at hs hs'
  simp only [vdword, Nat.sub_zero, Nat.mul_one] at h0 h1 h2 h3 h4 h5 h6 h7
  simp only [vdword, Nat.sub_zero, Nat.mul_one] at hw
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_kld .v14 (t+1) s (by omega) hb hi,
    exec_addi (n := .r19) (imm := 8) (by decide) (by decide), reduceExec, reduceVOpEval,
    Option.map_some, ↓vpr_writeV, ↓vpr_write, gpr_writeV, mem_writeV, rd_writeV, wr_writeV,
    vdword, Nat.sub_zero, Nat.mul_one, ↓high64_append, choice_select, BitVec.extractLsb'_xor,
    ↓packed_pairs, vword_dword, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Nat.reduceMul,
    widen32_eq, ↓high32_append, ↓low32_append,
    BitVec.zero_add, BitVec.zero_xor, BitVec.zero_and, sigma256_zero,
    BitVec.extractLsb'_and,
    show (5 : Nat).testBit 3 = false by decide, show (5 : Nat).testBit 2 = true by decide,
    show (0 : Nat).testBit 3 = false by decide, show (0 : Nat).testBit 2 = false by decide,
    isa, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hs, hs', h0, h1, h2, h3, h4, h5, h6, h7, hw, Option.some.injEq, exists_eq_left',
    Nat.reduceAdd, Nat.reduceLT, Bool.false_eq_true, ↓ite_eq_left, ↓reduceIte, true_and, hi, kIndex_next, and_true]
  refine ⟨?_, ?_, ?_⟩
  · simp only [roundKW, ch_eq, maj_eq, sigma256_bsig0, sigma256_bsig1,
      Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ]
    have hb : roundBias t = K t := by simp only [roundBias, ht, ite_true]
    simp only [majority_xor_select, hb,
      t1_biased_add_tree v[7] (K t) w (bsig1 v[4]) (((v[5] ^^^ v[6]) &&& v[4]) ^^^ v[6]),
      and_self]
  · intro r hr
    have hn : r ≠ .r19 := (show ∀ r ∈ pubRegs, r ≠ Reg.r19 by decide) r hr
    simp only [hn, ite_false]
  · intro r hr
    obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := hpairs r hr
    simp only [h0,h1,h2,h3,h4,h5,h6,ite_false]


theorem slot_ok (j : Nat) : slot j < 2 ^ 15 ∧ slot j % 4 = 0 := by
  simp only [slot]; omega

abbrev slotAddr (scr : Addr) (j : Nat) : Addr := scr + BitVec.ofNat 64 (slot j)

theorem low64_append (a b : BitVec 64) : (a ++ b).extractLsb' 0 64 = b :=
  BitVec.extractLsb'_append_eq_right

theorem preg_mem (n : Nat) : preg n ∈ pairs := by
  unfold preg List.getD
  cases h : pairs[n % 8]?
  · simp [pairs]
  · exact List.mem_of_getElem? h

theorem preg_eq_iff (i j : Nat) : preg i = preg j ↔ i % 8 = j % 8 := by
  simp only [preg]
  have hi := Nat.mod_lt i (show 8 > 0 by decide)
  have hj := Nat.mod_lt j (show 8 > 0 by decide)
  generalize i % 8 = a at *
  generalize j % 8 = b at *
  revert hj; revert b; revert hi; revert a; decide

/-- All complete pairs generated so far that remain in the ring. -/
def PairWin (n : Nat) (s : State) (M : Block) : Prop :=
  ∀ j, j < n → n ≤ j+8 → s.vpr (preg j) = (W M (2*j)).setWidth 64 ++ (W M (2*j+1)).setWidth 64

/-- The schedule changes one pair, temporary vectors, and scalar temporaries. -/
def PairPost (n : Nat) (M : Block) (s u : State) : Prop :=
  u.vpr (preg n) = (W M (2*n)).setWidth 64 ++ (W M (2*n+1)).setWidth 64 ∧
  (∀ r ∈ pairs, r ≠ preg n → u.vpr r = s.vpr r) ∧
  (∀ r ∈ vwork, u.vpr r = s.vpr r) ∧
  (∀ r, r ≠ T0 → r ≠ T1 → r ≠ .r0 → u.gpr r = s.gpr r) ∧
  u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr

theorem pairPost_win {n : Nat} {M : Block} {s u : State}
    (h : PairWin n s M) (hp : PairPost n M s u) : PairWin (n+1) u M := by
  intro j hj hj'
  by_cases he : j = n
  · subst j; exact hp.1
  · have hn : preg j ≠ preg n := by
      simp only [ne_eq, preg_eq_iff]; omega
    rw [hp.2.1 _ (preg_mem j) hn]
    exact h j (by omega) (by omega)

theorem pair_work_disjoint : ∀ r ∈ vwork, ∀ p ∈ pairs,
    r ≠ p ∧ r ≠ .v12 ∧ r ≠ .v13 ∧ r ≠ .v14 := by decide

theorem pair_temps_disjoint : ∀ p ∈ pairs, p ≠ .v12 ∧ p ≠ .v13 ∧ p ≠ .v14 := by decide

theorem pair_load_ok (n : Nat) (hn : n < 8) (M : Block) (s : State) (bp : Addr)
    (hr4 : s.gpr .r4 = bp)
    (hin : ∀ j < 16, InRegions (s.rd ++ s.wr) (bp + BitVec.ofNat 64 (4*j)) 4)
    (hblk : ∀ j < 16, rev32 (s.mem.readW (bp + BitVec.ofNat 64 (4*j)) 32) = W M j) :
    WP isa (.block (schedulePair n)) s (PairPost n M s) := by
  have i0 := hin (2*n) (by omega)
  have i1 := hin (2*n+1) (by omega)
  have b0 := hblk (2*n) (by omega)
  have b1 := hblk (2*n+1) (by omega)
  have he0 : 4*(2*n) = 8*n := by omega
  have he1 : 4*(2*n+1) = 8*n+4 := by omega
  rw [he0] at i0 b0
  rw [he1] at i1 b1
  have hp := pair_temps_disjoint _ (preg_mem n)
  have hw : ∀ r ∈ vwork, r ≠ preg n ∧ r ≠ .v12 ∧ r ≠ .v13 ∧ r ≠ .v14 :=
    fun r hr => pair_work_disjoint r hr _ (preg_mem n)
  have hpair : ∀ r ∈ pairs, r ≠ .v12 := fun r hr => (pair_temps_disjoint r hr).1
  apply WP.of_runBlock
  simp only [schedulePair, Impl.Sha2.PPC64LE.schedulePair, hn, ite_true, Bool.false_eq_true, ite_false, T0, T1, PairPost]
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_li (show 8*n < 2^15 by omega), exec_li (show 8*n+4 < 2^15 by omega),
    exec_loadRev_w (show (Reg.r4 : Reg) ≠ .r0 by decide), exec_sldoi8, reduceExec, isa,
    vpr_writeV, vpr_write, gpr_writeV, mem_writeV, rd_writeV, wr_writeV,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hr4, i0, i1, b0, b1, hp.1, hp.1.symm, high64_append, low64_append,
    Option.some.injEq, exists_eq_left', reduceCtorEq, ↓reduceIte, ne_eq, and_self, true_and]
  refine ⟨?_, ?_, ?_⟩
  · intro r hr hne
    simp only [hne, hpair r hr, ite_false]
  · intro r hr
    obtain ⟨a,b,_,_⟩ := hw r hr
    simp only [a,b,ite_false]
  · refine ⟨?_, True.intro⟩
    intro r h0 h1 h2
    simp only [h0,h1,h2,ite_false]

theorem pair_regs_nodup (n : Nat) :
    ([preg n, preg (n+1), preg (n+4), preg (n+5), preg (n+7), .v12, .v13, .v14] : List VReg).Nodup := by
  have h1 : (n+1)%8 = (n%8+1)%8 := by omega
  have h4 : (n+4)%8 = (n%8+4)%8 := by omega
  have h5 : (n+5)%8 = (n%8+5)%8 := by omega
  have h7 : (n+7)%8 = (n%8+7)%8 := by omega
  simp only [preg, h1,h4,h5,h7]
  clear h1 h4 h5 h7
  have h := Nat.mod_lt n (show 8 > 0 by decide)
  generalize n % 8 = a at *
  revert h; revert a; decide


theorem high64_four (a b c d : BitVec 32) :
    ((a ++ b) ++ (c ++ d)).extractLsb' 64 64 = a ++ b :=
  BitVec.extractLsb'_append_eq_left

theorem low64_four (a b c d : BitVec 32) :
    ((a ++ b) ++ (c ++ d)).extractLsb' 0 64 = c ++ d :=
  BitVec.extractLsb'_append_eq_right

theorem pair_compute_ok (n : Nat) (hn : 8 ≤ n) (M : Block) (s : State)
    (hwin : PairWin n s M) :
    WP isa (.block (schedulePair n)) s (PairPost n M s) := by
  have e0 := hwin (n-8) (by omega) (by omega)
  have e1 := hwin (n-7) (by omega) (by omega)
  have e4 := hwin (n-4) (by omega) (by omega)
  have e5 := hwin (n-3) (by omega) (by omega)
  have e7 := hwin (n-1) (by omega) (by omega)
  rw [show preg (n-8) = preg n by apply (preg_eq_iff _ _).mpr; omega] at e0
  rw [show preg (n-7) = preg (n+1) by apply (preg_eq_iff _ _).mpr; omega] at e1
  rw [show preg (n-4) = preg (n+4) by apply (preg_eq_iff _ _).mpr; omega] at e4
  rw [show preg (n-3) = preg (n+5) by apply (preg_eq_iff _ _).mpr; omega] at e5
  rw [show preg (n-1) = preg (n+7) by apply (preg_eq_iff _ _).mpr; omega] at e7
  have hs := pair_regs_nodup n
  have hs' := List.nodup_reverse.mpr hs
  have hw : ∀ r ∈ vwork, r ≠ preg n ∧ r ≠ .v12 ∧ r ≠ .v13 ∧ r ≠ .v14 :=
    fun r hr => pair_work_disjoint r hr _ (preg_mem n)
  have hp : ∀ r ∈ pairs, r ≠ .v12 ∧ r ≠ .v13 ∧ r ≠ .v14 := pair_temps_disjoint
  apply WP.of_runBlock
  simp only [schedulePair, Impl.Sha2.PPC64LE.schedulePair, show ¬n < 8 by omega, ite_false, Bool.false_eq_true, PairPost]
  generalize preg n = a at *
  generalize preg (n+1) = b at *
  generalize preg (n+4) = c at *
  generalize preg (n+5) = d at *
  generalize preg (n+7) = e at *
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, or_false, not_or,
    List.nodup_nil, and_true] at hs hs'
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_sldoi8, reduceExec, reduceVOpEval,
    Option.map_some, ↓vpr_writeV, gpr_writeV, mem_writeV, rd_writeV, wr_writeV,
    vdword, Nat.sub_zero, Nat.mul_one, Nat.mul_zero, high64_four, low64_four,
    ↓packed_pairs, vword_dword, Nat.reduceDiv, Nat.reduceMod,
    widen32_eq, ↓high32_append, ↓low32_append, high32_append, low32_append, BitVec.zero_add, sigma256_zero,
    show (5 : Nat).testBit 3 = false by decide, show (5 : Nat).testBit 2 = true by decide,
    show (5 : Nat).testBit 1 = false by decide, show (5 : Nat).testBit 0 = true by decide,
    show (0 : Nat).testBit 3 = false by decide, show (0 : Nat).testBit 2 = false by decide,
    show (0 : Nat).testBit 1 = false by decide, show (0 : Nat).testBit 0 = false by decide,
    isa, e0, e1, e4, e5, e7, hs, hs',
    Option.some.injEq, exists_eq_left', Nat.reduceSub, Nat.reduceLT,
    Bool.false_eq_true, ↓reduceIte, and_self]
  refine ⟨?_, ?_, ?_⟩
  · rw [W_ge M (t := 2*n) (by omega), W_ge M (t := 2*n+1) (by omega)]
    simp only [VG.PPC64LE.sigma256, Bool.false_eq_true, ite_true, ite_false]
    have a0 : 2*(n-1) = 2*n-2 := by omega
    have a1 : 2*(n-1)+1 = 2*n-1 := by omega
    have a2 : 2*(n-8) = 2*n-16 := by omega
    have a3 : 2*(n-8)+1 = 2*n-15 := by omega
    have a4 : 2*(n-7) = 2*n-14 := by omega
    have a5 : 2*(n-4)+1 = 2*n-7 := by omega
    have a6 : 2*(n-3) = 2*n-6 := by omega
    have b0 : 2*n+1-2 = 2*n-1 := by omega
    have b1 : 2*n+1-7 = 2*n-6 := by omega
    have b2 : 2*n+1-15 = 2*n-14 := by omega
    have b3 : 2*n+1-16 = 2*n-15 := by omega
    simp only [a0,a2,a4,a5,a6,b0,b1,b2,b3,ssig0,ssig1,
      show 2*n-16+1 = 2*n-15 by omega, show 2*n-2+1 = 2*n-1 by omega]
    apply congrArg₂ (· ++ ·) <;> apply congrArg (fun w : Word => (0#32) ++ w) <;> ac_rfl
  · intro r hr hne
    obtain ⟨h0,h1,h2⟩ := hp r hr
    simp only [hne,h0,h1,h2,ite_false]
  · refine ⟨?_, ⟨fun _ _ _ _ => True.intro, True.intro⟩⟩
    intro r hr
    obtain ⟨h0,h1,h2,h3⟩ := hw r hr
    simp only [h0,h1,h2,h3,ite_false]


theorem schedule_ok (t : Nat) (s : State) (M : Block) (bp : Addr)
    (hr4 : s.gpr .r4 = bp)
    (hin : ∀ j < 16, InRegions (s.rd ++ s.wr) (bp + BitVec.ofNat 64 (4*j)) 4)
    (hblk : ∀ j < 16, rev32 (s.mem.readW (bp + BitVec.ofNat 64 (4*j)) 32) = W M j)
    (hwin : PairWin ((t+1)/2) s M) :
    WP isa (.block (schedule t)) s fun u =>
      vdword (u.vpr .v15) 0 = (W M t).setWidth 64 ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      (∀ r, r ≠ T0 → r ≠ T1 → r ≠ .r0 → u.gpr r = s.gpr r) ∧
      (∀ r ∈ vwork, u.vpr r = s.vpr r) ∧ PairWin ((t+2)/2) u M := by
  have hp15 : ∀ r ∈ pairs, r ≠ .v15 := by decide
  have hw15 : ∀ r ∈ vwork, r ≠ .v15 := by decide
  by_cases ht : t % 2 = 0
  · have hr : (t+1)/2 = t/2 := by omega
    have hr' : (t+2)/2 = t/2+1 := by omega
    have he : 2*(t/2) = t := by omega
    rw [hr] at hwin
    have hp : WP isa (.block (schedulePair (t/2))) s (PairPost (t/2) M s) := by
      by_cases hn : t/2 < 8
      · exact pair_load_ok _ hn M s bp hr4 hin hblk
      · exact pair_compute_ok _ (by omega) M s hwin
    simp only [schedule, ht, ite_true]
    rw [WP.block_append_iff]
    refine WP.mono hp fun v hv => ?_
    have hwin' := pairPost_win hwin hv
    obtain ⟨hv, hpf, hw, hgp, hm, hrd, hwr⟩ := hv
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, reduceVOpEval, Option.map_some, isa,
      vpr_writeV, gpr_writeV, mem_writeV, rd_writeV, wr_writeV, BitVec.or_self,
      vdword, Nat.sub_zero, Nat.mul_one, hv, high64_append, he, hm, hrd, hwr,
      Option.some.injEq, exists_eq_left', ite_true, true_and]
    refine ⟨hgp, ?_, ?_⟩
    · intro r hr
      simp only [hw15 r hr, ite_false]
      exact hw r hr
    · intro j hj hj'
      simp only [vpr_writeV, hp15 _ (preg_mem j), ite_false]
      exact hwin' j (by omega) (by omega)
  · have hr : (t+1)/2 = t/2+1 := by omega
    have hr' : (t+2)/2 = (t+1)/2 := by omega
    have he : 2*(t/2)+1 = t := by omega
    have hp := hwin (t/2) (by omega) (by omega)
    have hn := (pair_temps_disjoint _ (preg_mem (t/2))).1
    simp only [schedule, ht, ite_false]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_sldoi8, isa,
      vpr_writeV, gpr_writeV, mem_writeV, rd_writeV, wr_writeV,
      vdword, Nat.sub_zero, Nat.mul_one, hp, high64_append, low64_append, he,
      Option.some.injEq, exists_eq_left', ite_true, true_and]
    refine ⟨fun _ _ _ _ => True.intro, ?_, ?_⟩
    · intro r hr
      simp only [hw15 r hr, ite_false]
    · intro j hj hj'
      simp only [vpr_writeV, hp15 _ (preg_mem j), ite_false]
      exact hwin j (by omega) (by omega)

/-! ## The 64 rounds -/

theorem pubRegs_ne' : ∀ r ∈ pubRegs, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 ∧ r ≠ .r0 := by decide

theorem pubRegs_ne {r : Reg} (h : r ∈ pubRegs) : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 ∧ r ≠ .r0 :=
  pubRegs_ne' r h

/-- The window `⟨scr, 64⟩`. -/
abbrev winRegion (scr : Addr) : Region := ⟨scr, 64⟩

theorem win_contains (scr : Addr) (j : Nat) : (winRegion scr).Contains (slotAddr scr j) 4 := by
  exact Offset.contains_base scr (d := slot j) (by unfold slot; omega) (by unfold slot; omega)

theorem slot_sep (scr : Addr) {i j : Nat} (h : i % 16 ≠ j % 16) :
    Mem.Sep (slotAddr scr i) 4 (slotAddr scr j) 4 := by
  apply Offset.sep scr (d := slot i) (e := slot j)
  · unfold slot; omega
  · unfold slot; omega
  · unfold slot; omega

/-- Rounds invariant, relative to the state `sB` at the start of the rounds. -/
structure RInv (H : HashValue) (M : Block) (scr : Addr) (sB : State) (t : Nat) (s : State) : Prop where
  vars : Vars t s (VG.Spec.Sha256.rounds H M t)
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [winRegion scr] sB.mem s.mem
  mem : s.mem = sB.mem
  syms : s.syms = sB.syms
  index : s.gpr .r19 = kIndex t
  win : PairWin ((t+1)/2) s M

theorem vvar_add16 (t k : Nat) : vvar (t+16) k = vvar t k := by
  simp only [vvar]
  congr 1
  omega

theorem preg_add8 (n : Nat) : preg (n+8) = preg n := by
  simp only [preg]
  congr 1
  omega

theorem schedulePair_add8 (n : Nat) (hn : 8 ≤ n) : schedulePair (n+8) = schedulePair n := by
  have he (j : Nat) : preg (n+8+j) = preg (n+j) := by
    simp only [preg]
    congr 1
    omega
  simp only [schedulePair, Impl.Sha2.PPC64LE.schedulePair, show ¬ n+8 < 8 by omega,
    show ¬ n < 8 by omega, ite_false, he, preg_add8]

theorem schedule_add16 (t : Nat) (ht : 16 ≤ t) : schedule (t+16) = schedule t := by
  have he : (t+16)%2 = t%2 := by omega
  have hd : (t+16)/2 = t/2+8 := by omega
  simp only [schedule, he, hd, schedulePair_add8 _ (by omega : 8 ≤ t/2), preg_add8]

theorem round_add16 (t : Nat) : round (t+16) = round t := by
  simp only [Impl.Sha256.PPC64LE.round, Impl.Sha2.PPC64LE.round, vvar_add16]

theorem roundRange_add16 (t n : Nat) (ht : 16 ≤ t) : roundRange (t+16) n = roundRange t n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [roundRange, ih, show t+16+n = (t+n)+16 by omega,
      schedule_add16 _ (by omega : 16 ≤ t+n), round_add16]

theorem chunk_period (j : Nat) : roundRange (16+16*j) 16 = computedChunk := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 16+16*(j+1) = (16+16*j)+16 by omega,
      roundRange_add16 _ _ (by omega), ih]

private theorem chunk_counter : ∀ i ∈ instrs computedChunk, dstOf i ≠ some Reg.r14 := by
  have h : (instrs computedChunk).all (fun i => decide (dstOf i ≠ some Reg.r14)) = true := by
    rw [← Code.allInstrs_eq]
    lit_decide
  intro i hi
  exact of_decide_eq_true (List.all_eq_true.mp h i hi)
theorem round_step_ok (H : HashValue) (M : Block) (bp scr : Addr) (sB : State)
    (hrsi : sB.gpr .r4 = bp)
    (hbin : ∀ t : Nat, t < 16 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofNat 64 (4*t)) 4)
    (hblk : ∀ m, Frame [winRegion scr] sB.mem m → ∀ t : Nat, t < 16 →
      rev32 (m.readW (bp + BitVec.ofNat 64 (4*t)) 32) = W M t)
    (hb : sB.gpr .r18 = sB.syms kSym) (t : Nat) (ht : t < 64) (s : State)
    (hs : RInv H M scr sB t s) :
    WP isa (.block (schedule t ++ round t)) s (RInv H M scr sB (t+1)) := by
  rw [WP.block_append_iff]
  have hr4 : s.gpr .r4 = bp := (hs.pub .r4 (by decide)).trans hrsi
  refine WP.mono_syms (schedule_ok t s M bp hr4
    (fun j hj => by rw [hs.rd, hs.wr]; exact hbin j hj) (hblk _ hs.frame) hs.win)
    fun s₁ ⟨hT0, hm₁, hrd₁, hwr₁, hr₁, hvr₁, hw₁⟩ hsy₁ => ?_
  have hv₁ : Vars t s₁ (VG.Spec.Sha256.rounds H M t) := by
    have hv := hs.vars
    have e : ∀ k, s₁.vpr (vvar t k) = s.vpr (vvar t k) :=
      fun k => hvr₁ _ (vvar_mem t k)
    simp only [Vars, e] at hv ⊢
    exact hv
  have hb₁ : s₁.gpr .r18 = s₁.syms kSym := by
    rw [hr₁ .r18 (by decide) (by decide) (by decide), hs.pub .r18 (by decide), hsy₁, hs.syms]
    exact hb
  have hi₁ : s₁.gpr .r19 = kIndex t := by
    rw [hr₁ .r19 (by decide) (by decide) (by decide), hs.index]
  refine WP.mono_syms (round_ok t (by omega) s₁ _ _ hb₁ hi₁ hv₁ hT0)
    fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂, hp₂, hi₂⟩ hsy₂ => ?_
  refine ⟨?_, fun r hr => ?_, by rw [hrd₂, hrd₁, hs.rd],
    by rw [hwr₂, hwr₁, hs.wr], ?_, ?_, hsy₂.trans (hsy₁.trans hs.syms), hi₂, ?_⟩
  · rw [rounds_succ, round_eq]; exact hv₂
  · have hn : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ .r0 := by
      have h : ∀ r ∈ pubRegs, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ .r0 := by decide
      exact h r hr
    rw [hr₂ r hr, hr₁ r hn.1 hn.2.1 hn.2.2, hs.pub r hr]
  · rw [hm₂, hm₁]; exact hs.frame
  · rw [hm₂, hm₁, hs.mem]
  · intro j hj hj'
    rw [hp₂ _ (preg_mem j)]
    exact hw₁ j hj hj'

theorem roundRange_ok (H : HashValue) (M : Block) (bp scr : Addr) (sB : State)
    (hrsi : sB.gpr .r4 = bp)
    (hbin : ∀ t : Nat, t < 16 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofNat 64 (4*t)) 4)
    (hblk : ∀ m, Frame [winRegion scr] sB.mem m → ∀ t : Nat, t < 16 →
      rev32 (m.readW (bp + BitVec.ofNat 64 (4*t)) 32) = W M t)
    (hb : sB.gpr .r18 = sB.syms kSym) (start : Nat) (s : State)
    (hs : RInv H M scr sB start s) :
    ∀ n, start+n ≤ 64 → WP isa (roundRange start n) s (RInv H M scr sB (start+n)) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil hs
  | succ n ih =>
    exact WP.seq (WP.mono (ih (by omega)) fun u hu =>
      round_step_ok H M bp scr sB hrsi hbin hblk hb (start+n) (by omega) u hu)

theorem RInv.write_counter {H : HashValue} {M : Block} {scr : Addr} {sB s : State} {t : Nat}
    (h : RInv H M scr sB t s) (x : BitVec 64) : RInv H M scr sB t (s.write .r14 x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Vars, vpr_write] using h.vars
  · intro r hr
    have hn : r ≠ Reg.r14 := (show ∀ r ∈ pubRegs, r ≠ Reg.r14 by decide) r hr
    rw [RegUpd.gpr_write_of_ne _ _ hn]
    exact h.pub r hr
  · simpa only [RegUpd.rd_write] using h.rd
  · simpa only [RegUpd.wr_write] using h.wr
  · simpa only [RegUpd.mem_write] using h.frame
  · simpa only [RegUpd.mem_write] using h.mem
  · simpa only [write_syms] using h.syms
  · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using h.index
  · simpa only [PairWin, vpr_write] using h.win

theorem counter_nonzero (m : Nat) (hm : m ≤ 3) :
    (BitVec.ofNat 64 m != 0) = decide (m ≠ 0) :=
  (show ∀ m ≤ 3, (BitVec.ofNat 64 m != 0) = decide (m ≠ 0) by decide) m hm

theorem counter_eval (m : Nat) (hm : m ≤ 3) (s : State) :
    eval (.nonzero .d .r14) (s.write .r14 (BitVec.ofNat 64 m)) = some (decide (m ≠ 0)) := by
  simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, RegUpd.gpr_write_self, counter_nonzero m hm]

/-- The 64 rounds, with the complete message window in vectors. -/
theorem rounds_ok (H : HashValue) (M : Block) (bp scr : Addr) (sB : State)
    (hrsi : sB.gpr .r4 = bp) (_hrcx : sB.gpr .r6 = scr)
    (_hin : ∀ j, InRegions (sB.rd ++ sB.wr) (slotAddr scr j) 4)
    (_hout : ∀ j, InRegions sB.wr (slotAddr scr j) 4)
    (hbin : ∀ t : Nat, t < 16 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofNat 64 (4*t)) 4)
    (hblk : ∀ m, Frame [winRegion scr] sB.mem m → ∀ t : Nat, t < 16 →
      rev32 (m.readW (bp + BitVec.ofNat 64 (4*t)) 32) = W M t)
    (h0 : Vars 0 sB H) (hb : sB.gpr .r18 = sB.syms kSym)
    (hi : sB.gpr .r19 = kIndex 0) :
    ∀ t ≤ 64, WP isa (rounds t) sB (RInv H M scr sB t) := by
  intro t ht
  induction t with
  | zero =>
    refine WP.block_nil (M := isa) ⟨?_, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, rfl, rfl, hi, ?_⟩
    · rw [rounds_zero]; exact h0
    · intro j hj _; omega
  | succ t ih =>
    exact WP.seq (WP.mono (ih (by omega)) fun s hs =>
      round_step_ok H M bp scr sB hrsi hbin hblk hb t (by omega) s hs)

theorem roundsLoop_ok (H : HashValue) (M : Block) (bp scr : Addr) (sB : State)
    (hrsi : sB.gpr .r4 = bp) (hrcx : sB.gpr .r6 = scr)
    (hin : ∀ j, InRegions (sB.rd ++ sB.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions sB.wr (slotAddr scr j) 4)
    (hbin : ∀ t : Nat, t < 16 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofNat 64 (4*t)) 4)
    (hblk : ∀ m, Frame [winRegion scr] sB.mem m → ∀ t : Nat, t < 16 →
      rev32 (m.readW (bp + BitVec.ofNat 64 (4*t)) 32) = W M t)
    (h0 : Vars 0 sB H) (hb : sB.gpr .r18 = sB.syms kSym)
    (hi : sB.gpr .r19 = kIndex 0) :
    WP isa roundsLoop sB (RInv H M scr sB 64) := by
  let Inv : Nat → State → Prop := fun m s =>
    1 ≤ m ∧ m ≤ 3 ∧ RInv H M scr sB (64-16*m) s ∧ s.gpr .r14 = BitVec.ofNat 64 m
  have step : ∀ m s, Inv m s → WP isa
      (.seq computedChunk (.block [.subi .r14 .r14 1])) s (fun s' =>
        (eval (.nonzero .d .r14) s' = some false ∧ RInv H M scr sB 64 s') ∨
        (eval (.nonzero .d .r14) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
    intro m s ⟨hm, hm3, hR, hc⟩
    have he : roundRange (64-16*m) 16 = computedChunk := by
      rw [show 64-16*m = 16+16*(3-m) by omega]
      exact chunk_period _
    have hw := WP.gpr (roundRange_ok H M bp scr sB hrsi hbin hblk hb _ s hR 16 (by omega))
      (r := .r14) (by rw [he]; exact chunk_counter)
    rw [he] at hw
    refine WP.seq (WP.mono hw fun u ⟨hU, hctr⟩ => ?_)
    apply WP.of_runBlock
    refine ⟨u.write .r14 (BitVec.ofNat 64 (m-1)), ?_, ?_⟩
    · simp only [runBlock_cons, exec_subi (show Reg.r14 ≠ .r0 by decide) (show 1 ≤ 2^15 by decide),
        runStep_some, runBlock_nil, hctr, hc, BitVec.ofNat_sub_ofNat_of_le (w := 64) m 1 (by decide) hm]
    · have hV : RInv H M scr sB (64-16*(m-1)) (u.write .r14 (BitVec.ofNat 64 (m-1))) := by
        simpa only [show 64-16*m+16 = 64-16*(m-1) by omega] using hU.write_counter (BitVec.ofNat 64 (m-1))
      have hev := counter_eval (m-1) (by omega) u
      by_cases hlast : m = 1
      · left
        refine ⟨?_, ?_⟩
        · rw [hev]
          simp only [hlast, Nat.sub_self, ne_eq, not_true_eq_false, decide_false]
        · simpa only [hlast, Nat.sub_self, Nat.mul_zero, Nat.sub_zero] using hV
      · right
        refine ⟨?_, m-1, by omega, by omega, by omega, hV, ?_⟩
        · rw [hev]
          simp only [Option.some.injEq, decide_eq_true_eq]
          omega
        · exact RegUpd.gpr_write_self _ _ _
  refine WP.seq (WP.mono (rounds_ok H M bp scr sB hrsi hrcx hin hout hbin hblk h0 hb hi 16 (by decide))
    fun s16 h16 => ?_)
  refine WP.seq (WP.of_runBlock ⟨s16.write .r14 (BitVec.ofNat 64 3), ?_, ?_⟩)
  · simp only [runBlock_cons, exec_li (show 3 < 2^15 by decide), runStep_some, runBlock_nil]
  · exact WP.loop (M := isa) Inv step 3 _
      ⟨by decide, by decide, h16.write_counter _, RegUpd.gpr_write_self _ _ _⟩



end VG.Proof.Sha256.PPC64LE
