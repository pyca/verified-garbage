module

import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Setup
import VerifiedGarbage.Proof.Aes.X86.AesNi.Data
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Aes.X86.Ctr32CT
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Rounds

/-! ### `Aes.X86.AesNi.Context`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86
open VG.Proof.Aes.X86 (GPre dstP dstR srcR schP nRounds ctrP datP nBlk scrP schR ctrR scrR)
open VG.Spec.Gcm (Block blockAt aesWith)

section
variable (s₀ : State)
abbrev sch : List Byte := Spec.Aes.bytesAt s₀.mem ((schP s₀).setWidth 64) (16 * (nRounds s₀ + 1))
abbrev cb : Block := blockAt s₀.mem ((ctrP s₀).setWidth 64)
abbrev ciph : Block → Block := aesWith (nRounds s₀) (sch s₀)
abbrev bAddr (k : Nat) : Addr := (datP s₀).setWidth 64 + BitVec.ofNat 64 (16 * k)
abbrev blk (k : Nat) : Block := blockAt s₀.mem (bAddr s₀ k)
/-- Where block `k` of the result goes: `bAddr` in place. -/
abbrev tAddr (to : Bool) (k : Nat) : Addr := (dstP to s₀).setWidth 64 + BitVec.ofNat 64 (16 * k)
abbrev pfx : BitVec 96 := (s₀.mem.readW ((ctrP s₀).setWidth 64) 128).extractLsb' 0 96
end

namespace GPre
variable {to : Bool} {s₀ : State} (hp : GPre to s₀)
include hp

omit hp in
theorem key_contains {j : Nat} (hj : j ≤ 14) :
    (schR s₀).Contains ((schP s₀).setWidth 64 + BitVec.ofNat 64 (16 * j)) 16 :=
  Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

theorem block_contains {k : Nat} (hk : k < nBlk s₀) :
    (srcR s₀).Contains (bAddr s₀ k) 16 :=
  Offset.contains_base _ (by omega_using [hk]) (by have h := hp.fSrc; omega_using [hk, h])

theorem block_in {k : Nat} (hk : k < nBlk s₀) : InRegions (s₀.rd ++ s₀.wr) (bAddr s₀ k) 16 :=
  ⟨srcR s₀, hp.rSrc, block_contains hp hk⟩

theorem tblock_contains {k : Nat} (hk : k < nBlk s₀) :
    (dstR to s₀).Contains (tAddr s₀ to k) 16 :=
  Offset.contains_base _ (by omega_using [hk]) (by have h := hp.fD; omega_using [hk, h])

theorem block_out {k : Nat} (hk : k < nBlk s₀) : InRegions s₀.wr (tAddr s₀ to k) 16 :=
  ⟨dstR to s₀, hp.wD, tblock_contains hp hk⟩

/-- Data and scratch writes preserve every byte of the schedule. -/
theorem sch_frame {m : Mem} (hf : Frame [dstR to s₀, scrR s₀] s₀.mem m) :
    Spec.Aes.bytesAt m ((schP s₀).setWidth 64) (16 * (nRounds s₀ + 1)) = sch s₀ := by
  have hn : 16 * (nRounds s₀ + 1) ≤ 240 := by
    rcases hp.rounds with h | h | h <;> omega_using [h]
  simp only [sch, Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact hf.bytes (R := ⟨(schP s₀).setWidth 64, 16 * (nRounds s₀ + 1)⟩) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dSD.sub_left (Region.sub_prefix hn)
    · exact hp.dSB.sub_left (Region.sub_prefix hn)) (by change 16 * (nRounds s₀ + 1) ≤ 2 ^ 64; omega_using [hn]) hi

/-- The readable round keys and their standard byte representation. -/
theorem keys {s : State} (hptr : s.gpr .eax = schP s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hf : Frame [dstR to s₀, scrR s₀] s₀.mem s.mem) :
    Keys (nRounds s₀) (sch s₀) s := by
  have hnr : nRounds s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  have he : ∀ j ≤ nRounds s₀, s.ea (Impl.Aes.X86.AesNi.at_ .eax (16 * j)) =
      (schP s₀).setWidth 64 + BitVec.ofNat 64 (16 * j) := by
    intro j hj
    rw [ea_mk]
    simp only [Impl.Aes.X86.AesNi.at_]
    rw [hptr]
    exact addr_eq (by have h := hp.fS; omega_using [hnr, hj, h])
  refine ⟨hnr, fun j hj => ?_, fun j hj => ?_⟩
  · rw [he j hj, hrd, hwr]
    exact ⟨schR s₀, List.mem_append_left _ hp.rS, key_contains (Nat.le_trans hj hnr)⟩
  · rw [he j hj, ← sch_frame hp hf]
    have h := byte_roundKey s.mem ((schP s₀).setWidth 64)
      (L := 16 * (nRounds s₀ + 1)) (j := j) (by omega_using [hj])
    rw [ofInt_natCast] at h
    exact h

end GPre
end VG.Proof.Aes.X86.AesNi

end

end

/-! ### `Aes.X86.AesNi.Invariant`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86
open VG.Proof.Aes.X86 (GPre dstP dstR srcR schP nRounds ctrP datP nBlk scrP scrR ctrR)
open VG.Spec.Gcm (blockAt inc32)

/-- `edx` in the loops: the counter pointer in place, and out of place the
destination of block `p`. -/
abbrev edxAt (to : Bool) (s₀ : State) (p : Nat) : BitVec 32 :=
  if to then dstP to s₀ + BitVec.ofNat 32 (16 * p) else ctrP s₀

/-- After c encrypted blocks, public data/count registers point at block p.
The prefix and saved callee registers stay in scratch throughout both loops. -/
structure Inv (to : Bool) (s₀ : State) (c p : Nat) (s : State) : Prop where
  le : c ≤ nBlk s₀
  ebx : s.gpr .ebx = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 c
  esp : s.gpr .esp = s₀.gpr .esp
  ecx : s.gpr .ecx = arg s₀ 1
  edx : s.gpr .edx = edxAt to s₀ p
  ebp : s.gpr .ebp = scrP s₀
  esi : s.gpr .esi = datP s₀ + BitVec.ofNat 32 (16 * p)
  edi : s.gpr .edi = BitVec.ofNat 32 (nBlk s₀ - p)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dstR to s₀, scrR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  scratchPrefix : s.mem.readW (addr (scrP s₀) 16) 128 = (0 : BitVec 32) ++ pfx s₀
  blocks : ∀ k < nBlk s₀,
    blockAt s.mem (tAddr s₀ to k) = if k < c then
      blk s₀ k ^^^ ciph s₀ (Nat.repeat inc32 k (cb s₀)) else blockAt s₀.mem (tAddr s₀ to k)

/-- A subrange of the encrypted run lies in the public destination region. -/
theorem run_in {to : Bool} {s₀ : State} {c n : Nat} (hn : c + n ≤ nBlk s₀) :
    Region.Sub ⟨tAddr s₀ to c, 16 * n⟩ (dstR to s₀) :=
  Offset.sub_base _ (by omega_using [hn])

/-- A destination block outside the encrypted run cannot overlap that run. -/
theorem run_sep {to : Bool} {s₀ : State} (hp : GPre to s₀) {c n k : Nat} (hk : k < nBlk s₀)
    (hn : c + n ≤ nBlk s₀) (hout : ¬ (c ≤ k ∧ k < c + n)) :
    Region.Disjoint ⟨tAddr s₀ to k, 16⟩ ⟨tAddr s₀ to c, 16 * n⟩ := by
  have hw := hp.fD
  exact Offset.disjoint _ (by omega_using [hout]) (by omega_using [hk, hw]) (by omega_using [hn, hw])

/-- The source blocks not yet read are as they were: they are the
destination's in place, and apart from everything written out of place. -/
theorem Inv.src {to : Bool} {s₀ s : State} (hp : GPre to s₀) {c p : Nat} (hI : Inv to s₀ c p s) {k : Nat}
    (hk : k < nBlk s₀) (hc : c ≤ k) : blockAt s.mem (bAddr s₀ k) = blk s₀ k := by
  rcases hp.sd with he | hdis
  · have e : bAddr s₀ k = tAddr s₀ to k := by simp only [bAddr, tAddr, he]
    have hb := hI.blocks k hk
    rw [ite_eq_right (show ¬ k < c by omega_using [hc])] at hb
    rw [e, hb, ← e]
  · exact blockAt_frame hI.frame fun r hr => by
      have hs : Region.Sub ⟨bAddr s₀ k, 16⟩ (srcR s₀) := Offset.sub_base _ (by omega_using [hk])
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hdis.sub_left hs
      · exact hp.dSrcB.sub_left hs

/-- Entry setup, with `edx` set for the loops, supplies the loop invariant
before any data is encrypted. -/
theorem Inv.of_start {to : Bool} {s₀ s₁ s : State} (hp : GPre to s₀) (hs : Start s₀ s₁)
    (hg : ∀ r, r ≠ .edx → s.gpr r = s₁.gpr r) (hedx : s.gpr .edx = edxAt to s₀ 0) (hm : s.mem = s₁.mem)
    (hrd : s.rd = s₁.rd) (hwr : s.wr = s₁.wr) : Inv to s₀ 0 0 s := by
  refine ⟨Nat.zero_le _, ?_, by rw [hg _ (by decide)]; exact hs.esp, by rw [hg _ (by decide)]; exact hs.ecx,
    hedx, by rw [hg _ (by decide)]; exact hs.ebp, ?_, ?_, by rw [hrd]; exact hs.rd, by rw [hwr]; exact hs.wr,
    ?_, by rw [hm]; exact hs.saved, by rw [hm]; exact hs.scratchPrefix, ?_⟩
  · rw [hg _ (by decide), hs.ebx, BitVec.add_zero]
  · rw [hg _ (by decide), hs.esi, Nat.mul_zero, BitVec.add_zero]
  · rw [hg _ (by decide)]; simpa only [Nat.sub_zero] using hs.edi
  · rw [hm]; exact hs.frame.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩
  · intro k hk
    simp only [Nat.not_lt_zero, ite_false]
    rw [hm]
    exact blockAt_frame hs.frame (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact hp.dDB.sub_left (run_in (s₀ := s₀) (c := k) (n := 1) (by omega_using [hk])))

end VG.Proof.Aes.X86.AesNi

end

end

@[expose] public section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86 VG.X86.RegUpd
open VG.Proof.Aes.X86 (GPre datP nBlk)

/-- Bounded natural counts are zero exactly when their word is zero. -/
theorem beq_ofNat_zero {k : Nat} (hk : k < 2 ^ 32) :
    (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  by_cases h : k = 0
  · subst h; rfl
  · have he : BitVec.ofNat 32 k ≠ 0 := fun e => h (by
      have he := congrArg BitVec.toNat e
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at he)
    rw [beq_eq_false_iff_ne.mpr he]
    simp [h]

/-- Public pointer and remaining-count advancement, without changing memory:
out of place the destination pointer advances with the source's. -/
theorem advance_ok {to : Bool} {s₀ : State} (hp : GPre to s₀) {c p n : Nat}
    (hn : p + n ≤ nBlk s₀) {s : State} (hI : Inv to s₀ c p s) :
    WP isa (.block (([.alu .add .esi (.imm (BitVec.ofNat 32 (16 * n)))] : List Instr) ++
      Impl.Aes.X86.AesNi.advTo to (BitVec.ofNat 32 (16 * n)) ++
      ([.alu .sub .edi (.imm (BitVec.ofNat 32 n))] : List Instr))) s fun s' =>
      Inv to s₀ c (p + n) s' ∧ s'.zf = some (decide (nBlk s₀ - (p + n) = 0)) := by
  have hw := hp.fSrc
  have hsub : BitVec.ofNat 32 (nBlk s₀ - p) - BitVec.ofNat 32 n =
      BitVec.ofNat 32 (nBlk s₀ - (p + n)) := by
    rw [Offset.ofNat_sub_ofNat (by omega_using [hn])]
    exact congrArg (BitVec.ofNat 32) (by omega_using [])
  have hadd : ∀ X : BitVec 32, (X + BitVec.ofNat 32 (16 * p)) + BitVec.ofNat 32 (16 * n) =
      X + BitVec.ofNat 32 (16 * (p + n)) := fun X => by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (fun k => X + BitVec.ofNat 32 k) (by omega_using [])
  have hI' := hI
  cases to
  · have hedx := hI.edx
    simp only [edxAt, Bool.false_eq_true, ↓reduceIte] at hedx
    apply WP.of_runBlock
    simp only [Impl.Aes.X86.AesNi.advTo, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.cons_append,
      List.nil_append, reduceCtorEq, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil,
      isa, exec, execAlu, readSrc, gpr_setReg, gpr_arithFlags, hI.esi, hI.edi,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨{ hI with esi := ?_, edi := ?_, edx := ?_ }, ?_⟩
    · exact hedx
    · simp only [reduceCtorEq, ↓reduceIte, gpr_setReg, gpr_arithFlags]
      exact hadd _
    · simp only [gpr_setReg_self]
      exact hsub
    · rw [zf_setReg, zf_arithFlags, hsub, beq_ofNat_zero (by omega_using [hw])]
  · have hedx := hI.edx
    simp only [edxAt, ↓reduceIte] at hedx
    apply WP.of_runBlock
    simp only [Impl.Aes.X86.AesNi.advTo, ↓reduceIte, List.cons_append,
      List.nil_append, reduceCtorEq, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil,
      isa, exec, execAlu, readSrc, gpr_setReg, gpr_arithFlags, hI.esi, hI.edi, hedx,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨{ hI with esi := ?_, edi := ?_, edx := ?_ }, ?_⟩
    · exact hadd _
    · simp only [reduceCtorEq, ↓reduceIte, gpr_setReg, gpr_arithFlags]
      exact hadd _
    · simp only [gpr_setReg_self]
      exact hsub
    · rw [zf_setReg, zf_arithFlags, hsub, beq_ofNat_zero (by omega_using [hw])]

/-- The bulk-loop branch depends only on the public remaining count. -/
theorem cmpEdi_ok {to : Bool} {s₀ : State} {c p n : Nat} (hn : n < 2 ^ 32)
    (hp : p ≤ nBlk s₀) {s : State} (hI : Inv to s₀ c p s) :
    WP isa (.block [.alu .cmp .edi (.imm (BitVec.ofNat 32 n))]) s fun s' =>
      Inv to s₀ c p s' ∧ s'.cf = some (decide (nBlk s₀ - p < n)) := by
  have hnb : nBlk s₀ < 2 ^ 32 := (arg s₀ 4).isLt
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, execAlu,
    readSrc, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨hI.le, hI.ebx, hI.esp, hI.ecx, hI.edx, hI.ebp, hI.esi, hI.edi,
    hI.rd, hI.wr, hI.frame, hI.saved, hI.scratchPrefix, hI.blocks⟩, ?_⟩
  simp only [cf_arithFlags, hI.edi, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (show nBlk s₀ - p < 2 ^ 32 by omega)]

/-- Zero detection between the bulk and tail loops also uses only the count. -/
theorem testEdi_ok {to : Bool} {s₀ : State} {c p : Nat} {s : State} (hI : Inv to s₀ c p s) :
    WP isa (.block [.alu .test .edi (.reg .edi)]) s fun s' =>
      Inv to s₀ c p s' ∧ s'.zf = some (decide (nBlk s₀ - p = 0)) := by
  have hnb : nBlk s₀ < 2 ^ 32 := (arg s₀ 4).isLt
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, execAlu,
    readSrc, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨hI.le, hI.ebx, hI.esp, hI.ecx, hI.edx, hI.ebp, hI.esi, hI.edi,
    hI.rd, hI.wr, hI.frame, hI.saved, hI.scratchPrefix, hI.blocks⟩, ?_⟩
  rw [zf_arithFlags, BitVec.and_self, hI.edi, beq_ofNat_zero (by omega_using [hnb])]

end VG.Proof.Aes.X86.AesNi
