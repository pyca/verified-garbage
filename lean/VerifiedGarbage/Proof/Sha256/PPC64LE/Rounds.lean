module

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


end VG.Proof.Sha256.PPC64LE
