import VerifiedGarbage.Proof.Sha1.X86.ShaNi.Rounds
import VerifiedGarbage.Proof.Sha1.X86.ShaNi.Lit
import VerifiedGarbage.Proof.Sha1.X86.Compress
import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Const
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-!
# SHA-1 compression function on x86 with the SHA extensions

`compress_verified` proves `Impl.Sha1.X86.ShaNi.compress` against the same
contract as the scalar `vg_sha1_compress` (`Proof.Sha1.compressX86`),
reusing its precondition (`Pre`), its block lemmas and its initial taint: the
rounds are those of `Rounds.lean`; around them, the hash value is loaded and
stored, and the working variables at the start of each block are kept in
`scratch[0..32)` and added back at its end.
-/

namespace VG.Proof.Sha1.X86.ShaNi

open VG VG.X86 VG.Impl.Sha1.X86.ShaNi
open VG.Proof.Sha1.X86 (Pre pre_of st bp nb scr esp₀ stR blR scrR retR H₀ blkAddr blk
  blk_word compressBlocks_succ contains_sub st_eq harg_of)
open VG.Proof.Sha256.X86.ShaNi (movd_value shift_last_value or_last_value)
open VG.Spec.Sha1 (HashValue Word Block W stateAt compressBlocks compress)

/-! ## Loading and storing the hash value -/

theorem const_ok (c : BitVec 128) (s : State) :
    WP isa (.block (const c)) s fun s' =>
      s'.xmm .xmm7 = c ∧
      (∀ r, r ≠ .xmm7 → r ≠ .xmm2 → s'.xmm r = s.xmm r) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ldq : ∀ a b, XBinOp.eval .punpckldq a b =
      ofDwords (dword a 0) (dword b 0) (dword a 1) (dword b 1) := fun _ _ => rfl
  apply WP.of_runBlock
  simp only [Nat.reduceAdd, and_self, const, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, XOp.exec, isa, movd_value, ldq,
    dword_ofDwords_0, dword_ofDwords_1, punpcklqdq_eq,
    shift_last_value,
    RegUpd.gpr_setReg_self,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.xmm_setReg,
    RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm,
    RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    reduceCtorEq, not_false_eq_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r h7 h2 => ?_, fun r hr => ?_, trivial⟩
  · exact (or_last_value _ _ _ _).trans (ofDwords_dword c)
  · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setXmm_of_ne, h7, h2, not_false_eq_true]
  · simp only [RegUpd.gpr_setXmm, RegUpd.gpr_setReg_of_ne, hr, not_false_eq_true]

theorem loadState_ok (s : State) (p : BitVec 32)
    (harg : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4)
    (hv : s.mem.readW (addr (s.gpr .esp) 4) 32 = p)
    (h0 : InRegions (s.rd ++ s.wr) (addr p 0) 16) (h4 : InRegions (s.rd ++ s.wr) (addr p 4) 16) :
    WP isa (.block loadState) s fun s' =>
      s'.xmm .xmm0 = shufDwords (s.mem.readW (addr p 0) 128) 0x1b ∧
      s'.xmm .xmm1 = XShiftOp.eval .pslldq (XShiftOp.eval .psrldq (s.mem.readW (addr p 4) 128) 12) 12 ∧
      (∀ r, r ≠ .edx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [loadState, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, XOp.exec, isa,
    State.load32, State.load128, ea_at, harg, hv, ite_true, RegUpd.gpr_setReg_self,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, h0, h4,
    RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm,
    RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    reduceCtorEq, not_false_eq_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, trivial, trivial, trivial⟩
  simp only [RegUpd.gpr_setReg_of_ne, hr, not_false_eq_true]

theorem loadArgs_ok (s : State)
    (h8 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4)
    (h12 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 12) 4)
    (h16 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4) :
    WP isa (.block loadArgs) s fun s' =>
      s'.gpr .ecx = s.mem.readW (addr (s.gpr .esp) 8) 32 ∧
      s'.gpr .edx = s.mem.readW (addr (s.gpr .esp) 16) 32 ∧
      s'.gpr .eax = s.mem.readW (addr (s.gpr .esp) 12) 32 ∧
      s'.zf = some (s.mem.readW (addr (s.gpr .esp) 12) 32 &&& s.mem.readW (addr (s.gpr .esp) 12) 32 == 0) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧
      s'.xmm = s.xmm ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [loadArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, isa,
    State.load32, ea_at, RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, h8, h12, h16,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.xmm_arithFlags, RegUpd.zf_arithFlags, RegUpd.xmm_setReg,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, fun r ha hc hd => ?_, trivial, trivial, trivial, trivial⟩
  simp only [ha, hc, hd, ↓reduceIte]

theorem stateAt_lo (m : Mem) {p : BitVec 32} (hfit : p.toNat + 20 ≤ 2 ^ 32) {j : Nat} (hj : j < 4) :
    dword (m.readW (addr p 0) 128) j = (stateAt m (p.setWidth 64))[j] := by
  rw [addr_eq (by omega), dword_readW _ _ hj]
  simp only [stateAt, Vector.getElem_ofFn]
  rw [Offset.add_ofNat_add_ofNat, Nat.zero_add]

theorem stateAt_e (m : Mem) {p : BitVec 32} (hfit : p.toNat + 20 ≤ 2 ^ 32) :
    dword (m.readW (addr p 4) 128) 3 = (stateAt m (p.setWidth 64))[4] := by
  rw [addr_eq (by omega), dword_readW _ _ (by decide)]
  simp only [stateAt, Vector.getElem_ofFn]
  rw [Offset.add_ofNat_add_ofNat]

theorem getLsbD_zero32 (i : Nat) : (0 : Word).getLsbD i = false := by simp

theorem shift_e (x : BitVec 128) :
    XShiftOp.eval .pslldq (XShiftOp.eval .psrldq x 12) 12 = ofDwords 0 0 0 (dword x 3) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e : min (12 : BitVec 8).toNat 16 * 8 = 96 := rfl
  simp only [XShiftOp.eval, e, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, getLsbD_ofDwords,
    getLsbD_dword]
  rcases (by omega : i < 96 ∨ 96 ≤ i) with h | h
  · simp only [h, decide_true, Bool.not_true, Bool.and_false, Bool.false_and, getLsbD_zero32]
    rcases (by omega : i < 32 ∨ (32 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96)) with h' | h' | h' <;>
    simp (disch := omega) only [ite_eq_left, ite_eq_right]
  · simp (disch := omega) only [hi, show ¬ i < 96 by omega, show ¬ i < 32 by omega,
      show ¬ i - 32 < 32 by omega, show ¬ i - 32 - 32 < 32 by omega, show i - 32 - 32 - 32 = i - 96 by omega,
      show i - 96 < 32 by omega, decide_true, decide_false, Bool.not_false, Bool.true_and, ite_false]

/-- `B, C, D, E` from `A, B, C, D` and `E`. -/
theorem por_e (a b c d e : Word) :
    XBinOp.eval .por (XShiftOp.eval .psrldq (ofDwords a b c d) 4) (ofDwords 0 0 0 e) = ofDwords b c d e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e32 : min (4 : BitVec 8).toNat 16 * 8 = 32 := rfl
  simp only [XBinOp.eval, XShiftOp.eval, e32, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, getLsbD_ofDwords,
    getLsbD_zero32]
  rcases (by omega : i < 32 ∨ (32 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96) ∨ 96 ≤ i) with h | h | h | h <;>
  simp (disch := omega) only [ite_eq_left, ite_eq_right, Bool.or_false]
  · exact congrArg _ (by omega)
  · exact congrArg _ (by omega)
  · exact congrArg _ (by omega)
  · rw [BitVec.getLsbD_of_ge d _ (by omega), Bool.false_or]

theorem shufDwords_1b (a : BitVec 128) :
    shufDwords a 0x1b = ofDwords (dword a 3) (dword a 2) (dword a 1) (dword a 0) := rfl

/-- The hash value as the loaded registers hold it. -/
theorem loaded_eq (m : Mem) {p : BitVec 32} (hfit : p.toNat + 20 ≤ 2 ^ 32) :
    shufDwords (m.readW (addr p 0) 128) 0x1b = abcd (stateAt m (p.setWidth 64)) ∧
    XShiftOp.eval .pslldq (XShiftOp.eval .psrldq (m.readW (addr p 4) 128) 12) 12 =
      eReg (stateAt m (p.setWidth 64)) := by
  refine ⟨?_, ?_⟩
  · rw [shufDwords_1b, stateAt_lo _ hfit (show 0 < 4 by decide), stateAt_lo _ hfit (show 1 < 4 by decide),
      stateAt_lo _ hfit (show 2 < 4 by decide), stateAt_lo _ hfit (show 3 < 4 by decide)]
    rfl
  · rw [shift_e, stateAt_e _ hfit]; rfl

/-- The hash value after storing `x` at `p + 4` and `y` at `p`. -/
theorem stateAt_store (m : Mem) {p : BitVec 32} (hfit : p.toNat + 20 ≤ 2 ^ 32) (x y : BitVec 128) :
    stateAt ((m.writeW (addr p 4) x).writeW (addr p 0) y) (p.setWidth 64) =
      #v[dword y 0, dword y 1, dword y 2, dword y 3, dword x 3] := by
  rw [addr_eq (k := 4) (by omega), addr_eq (k := 0) (by omega)]
  generalize p.setWidth 64 = P
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn]
  by_cases hlo : j < 4
  · rw [show P + BitVec.ofNat 64 (4 * j) = P + BitVec.ofNat 64 0 + BitVec.ofNat 64 (4 * j) by
      rw [Offset.add_ofNat_add_ofNat, Nat.zero_add],
      readW_writeW128 _ _ _ hlo]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl
  · obtain rfl : j = 4 := by omega
    rw [Mem.readW_writeW_sep (Offset.sep P (by omega) (by omega) (by omega)) (by decide),
      show P + BitVec.ofNat 64 (4 * 4) = P + BitVec.ofNat 64 4 + BitVec.ofNat 64 (4 * 3) by
        rw [Offset.add_ofNat_add_ofNat],
      readW_writeW128 _ _ _ (by omega)]
    rfl

/-- `ABCD` and `E`, stored back as the hash value. -/
theorem store_ok (s : State) (p : BitVec 32) (v : HashValue)
    (harg : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4)
    (hv : s.mem.readW (addr (s.gpr .esp) 4) 32 = p) (hfit : p.toNat + 20 ≤ 2 ^ 32)
    (h0 : InRegions s.wr (addr p 0) 16) (h4 : InRegions s.wr (addr p 4) 16)
    (x0 : s.xmm .xmm0 = abcd v) (x1 : s.xmm .xmm1 = eReg v) :
    WP isa (.block store) s fun s' =>
      (∃ x y : BitVec 128, s'.mem = (s.mem.writeW (addr p 4) x).writeW (addr p 0) y) ∧
      stateAt s'.mem (p.setWidth 64) = v ∧
      (∀ r, r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [store, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, XOp.exec, isa,
    State.load32, State.store128, ea_at, harg, hv, ite_true, RegUpd.gpr_setReg_self,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.xmm_setReg, h0, h4,
    RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm,
    RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm, x0, x1, eval_movdqa,
    reduceCtorEq, not_false_eq_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨_, _, rfl⟩, ?_, fun r hr => ?_, trivial, trivial⟩
  · rw [stateAt_store _ hfit]
    simp only [shufDwords_1b, abcd, eReg, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
      dword_ofDwords_3, por_e]
    apply Vector.ext
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp only [RegUpd.gpr_setReg_of_ne, hr, not_false_eq_true]

/-! ## A block -/

theorem save_ok (s : State)
    (h0 : InRegions s.wr (addr (s.gpr .edx) 0) 16) (h16 : InRegions s.wr (addr (s.gpr .edx) 16) 16) :
    WP isa (.block save) s fun s' =>
      s'.mem = (s.mem.writeW (addr (s.gpr .edx) 0) (s.xmm .xmm0)).writeW
        (addr (s.gpr .edx) 16) (s.xmm .xmm1) ∧
      s'.xmm = s.xmm ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [save, runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.store128,
    ea_at, h0, h16, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem finish_ok (s : State) (H : HashValue) (M : Block)
    (h0 : s.xmm .xmm0 = abcd (Spec.Sha1.rounds H M (4 * 20)))
    (h1 : (dword (s.xmm .xmm1) 3).rotateLeft 30 = (Spec.Sha1.rounds H M (4 * 20))[4])
    (i0 : InRegions (s.rd ++ s.wr) (addr (s.gpr .edx) 0) 16)
    (i16 : InRegions (s.rd ++ s.wr) (addr (s.gpr .edx) 16) 16)
    (v0 : s.mem.readW (addr (s.gpr .edx) 0) 128 = abcd H)
    (v16 : s.mem.readW (addr (s.gpr .edx) 16) 128 = eReg H) :
    WP isa (.block finish) s fun s' =>
      s'.xmm .xmm0 = abcd (compress H M) ∧ s'.xmm .xmm1 = eReg (compress H M) ∧
      s'.xmm .xmm7 = s.xmm .xmm7 ∧
      s'.gpr .ecx = s.gpr .ecx + 64 ∧ s'.gpr .eax = s.gpr .eax - 1 ∧
      (∀ r, r ≠ .ecx → r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.zf = some (s.gpr .eax - 1 == 0) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [finish, runBlock_cons, runStep_some, runBlock_nil,
    exec, XOp.exec, execAlu, readSrc, isa, State.load128, ea_at, i0, i16, ite_true,
    RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm,
    RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.xmm_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.xmm_arithFlags, RegUpd.zf_arithFlags, RegUpd.zf_setReg,
    reduceCtorEq, not_false_eq_true, h0, v0, v16, paddd_abcd, nexte_eReg _ _ _ h1,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, trivial, trivial, trivial, fun r hc ha => ?_, trivial, trivial, trivial, trivial⟩
  simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne, hc, ha, not_false_eq_true,
    RegUpd.gpr_setXmm]

/-! ## The loop over the blocks -/

theorem Pre.blk_fit {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) :
    (blkAddr s₀ i).toNat + 64 ≤ 2 ^ 32 := by
  have hb := hp.blk_fits
  simp only [blkAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 64 * i < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show (bp s₀).toNat + 64 * i < 2 ^ 32 by omega)]
  omega

theorem Pre.blk_vec {s₀ : State} (hp : Pre s₀) {i n : Nat} (hi : i < nb s₀) (hn : n < 4) :
    InRegions (s₀.rd ++ s₀.wr) (addr (blkAddr s₀ i) (16 * n)) 16 := by
  have he : (blkAddr s₀ i).setWidth 64 = (bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) := by
    simpa only [blkAddr, addr] using addr_eq (x := bp s₀) (k := 64 * i)
      (by have := hp.blk_fits; omega)
  refine ⟨blR s₀, by simp only [hp.rd, List.mem_append, List.mem_cons, true_or], ?_⟩
  rw [addr_eq (by have := Pre.blk_fit hp hi; omega), he, Offset.add_add]
  exact Offset.contains_base _ (by omega) (by have := hp.blk_fits; omega)

theorem Pre.scr_vec {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d + 16 ≤ 112) :
    InRegions s₀.wr (addr (scr s₀) d) 16 :=
  ⟨scrR s₀, by simp [hp.wr], contains_sub hd (by omega) (hp.scr_eq (by omega))⟩

theorem Pre.st_vec {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d + 16 ≤ 20) :
    InRegions s₀.wr (addr (st s₀) d) 16 :=
  ⟨stR s₀, by simp [hp.wr], contains_sub hd (by omega) (st_eq hp (by omega))⟩

theorem in_read_of_write {rd wr : List Region} {p : Addr} {n : Nat}
    (h : InRegions wr p n) : InRegions (rd ++ wr) p n := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, List.mem_append.mpr (.inr hr), hc⟩

/-- Writing 16 bytes at `scratch + d`. -/
theorem scr_write {s₀ : State} (hp : Pre s₀) (m : Mem) (v : BitVec 128) {d : Nat} (hd : d + 16 ≤ 112) :
    Frame [scrR s₀] m (m.writeW (addr (scr s₀) d) v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) v
    (contains_sub hd (by omega) (hp.scr_eq (by omega)))

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  x0 : s.xmm .xmm0 = abcd (compressBlocks (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) i)
  x1 : s.xmm .xmm1 = eReg (compressBlocks (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) i)
  edx : s.gpr .edx = scr s₀
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [scrR s₀] s₀.mem s.mem

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  x7 : s.xmm .xmm7 = bswapMask
  ecx : s.gpr .ecx = blkAddr s₀ i
  eax : s.gpr .eax = BitVec.ofNat 32 (nb s₀ - i)

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  have vecwr : ∀ d : Nat, d + 16 ≤ 112 → InRegions s.wr (addr (s.gpr .edx) d) 16 := by
    intro d hd; rw [hL.wr, hL.edx]; exact Pre.scr_vec hp hd
  refine WP.seq (WP.mono (save_ok s (vecwr 0 (by decide)) (vecwr 16 (by decide)))
    fun s₁ ⟨hm₁, hx₁, hg₁, hrd₁, hwr₁⟩ => ?_)
  have hf₁ : Frame [scrR s₀] s₀.mem s₁.mem := by
    rw [hm₁, hL.edx]
    exact (hL.frame.trans (scr_write hp _ _ (by decide))).trans (scr_write hp _ _ (by decide))
  have v0 : s₁.mem.readW (addr (scr s₀) 0) 128 = abcd (compressBlocks (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) i) := by
    rw [hm₁, hL.edx, hp.scr_eq (by decide), hp.scr_eq (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self _ _ 16 _ (by decide), hL.x0]
  have v16 : s₁.mem.readW (addr (scr s₀) 16) 128 = eReg (compressBlocks (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) i) := by
    rw [hm₁, hL.edx, Mem.readW_writeW_self _ _ 16 _ (by decide), hL.x1]
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) (blkAddr s₀ i) s₁ (by rw [hg₁, hL.ecx])
    (Pre.blk_fit hp hi) (by rw [hx₁, hL.x7])
    (fun n hn => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact Pre.blk_vec hp hi hn)
    (fun t ht => by
      rw [hf₁.readW (hp.blk_contains hi ht) (by simpa using hp.blk_scr) (by decide)]
      exact blk_word hp hi ht)
    (by rw [hx₁, hL.x0]) (by rw [hx₁, hL.x1]) 20 (Nat.le_refl _)) fun s₂ hR => ?_)
  have hedx₂ : s₂.gpr .edx = scr s₀ := by rw [hR.gpr, hg₁, hL.edx]
  have hx1 : (dword (s₂.xmm .xmm1) 3).rotateLeft 30 =
      (Spec.Sha1.rounds (compressBlocks (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) i) (blk s₀ i) (4 * 20))[4] := by
    have := hR.x1; simpa only [ECarry, Nat.reduceMul, Nat.reduceEqDiff, ite_false] using this
  have rw₂ : ∀ d : Nat, d + 16 ≤ 112 → InRegions (s₂.rd ++ s₂.wr) (addr (s₂.gpr .edx) d) 16 := by
    intro d hd
    rw [hR.rd, hR.wr, hrd₁, hwr₁, hL.rd, hL.wr, hedx₂]
    exact in_read_of_write (Pre.scr_vec hp hd)
  refine WP.mono (finish_ok s₂ _ _ hR.x0 hx1 (rw₂ 0 (by decide)) (rw₂ 16 (by decide))
    (by rw [hedx₂, hR.mem, v0]) (by rw [hedx₂, hR.mem, v16]))
    fun s₃ ⟨f0, f1, f7, fecx, feax, fg, fzf, fm, frd, fwr⟩ => ?_
  have g₂ : s₂.gpr = s.gpr := by rw [hR.gpr, hg₁]
  have heax : s₂.gpr .eax - 1 = BitVec.ofNat 32 (nb s₀ - (i + 1)) := by
    rw [g₂, hL.eax, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.ofNat_sub_ofNat (by omega),
      Nat.sub_sub]
  have hcommon : Common s₀ (i + 1) s₃ :=
    ⟨by rw [f0, compressBlocks_succ], by rw [f1, compressBlocks_succ],
      by rw [fg _ (by decide) (by decide), hedx₂],
      fun r ha hc hd => by rw [fg r hc ha, g₂, hL.gpr r ha hc hd],
      by rw [frd, hR.rd, hrd₁, hL.rd], by rw [fwr, hR.wr, hwr₁, hL.wr], by rw [fm, hR.mem]; exact hf₁⟩
  have hev : eval .ne s₃ = some (!(s₂.gpr .eax - 1 == 0)) := by
    simp only [eval, fzf, Option.map_some]
  rw [heax] at hev
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    refine ⟨?_, by omega, { hcommon with x7 := ?_, ecx := ?_, eax := ?_ }⟩
    · rw [hev]
      have h0 : BitVec.ofNat 32 (nb s₀ - (i + 1)) ≠ 0 := by
        intro h
        have h' := congrArg BitVec.toNat h
        have hn : nb s₀ < 2 ^ 32 := (VG.X86.arg s₀ 2).isLt
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hn)] at h'
        exact hne h'
      simpa using h0
    · rw [f7, hR.x7, hx₁, hL.x7]
    · rw [fecx, g₂, hL.ecx, blkAddr, blkAddr, BitVec.add_assoc]
      rw [show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, ← BitVec.ofNat_add]
      exact congrArg (fun n => bp s₀ + BitVec.ofNat 32 n) (by omega)
    · rw [feax, heax]

theorem loop_ok {s₀ : State} (hp : Pre s₀) (hpos : 0 < nb s₀) {s : State}
    (hL : LInv s₀ 0 s) :
    WP isa (.loop body .ne) s (Common s₀ (nb s₀)) := by
  let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
  have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
    rintro m s ⟨i, rfl, hi, hL⟩
    refine WP.mono (body_ok hp hi hL) fun s' h => ?_
    rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
    · exact .inl ⟨he, hc⟩
    · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
  exact WP.loop (M := isa) Inv hstep (nb s₀) s ⟨0, rfl, hpos, hL⟩

/-! ## The whole function -/

theorem load_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block load) s₀ fun s' => LInv s₀ 0 s' ∧ s'.zf = some (arg s₀ 2 &&& arg s₀ 2 == 0) := by
  have shape : load = loadState ++ (const bswapMask ++ loadArgs) := by
    simp only [load, List.append_assoc]
  rw [shape, WP.block_append_iff]
  have hst := hp.st_fits
  refine WP.mono (loadState_ok s₀ (st s₀) (hp.in_arg (by decide) (by decide)) rfl
    (in_read_of_write (Pre.st_vec hp (by decide))) (in_read_of_write (Pre.st_vec hp (by decide))))
    fun s₁ ⟨x0, x1, hg₁, hm₁, hrd₁, hwr₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok bswapMask s₁) fun s₂ ⟨x7, hx₂, hg₂, hm₂, hrd₂, hwr₂⟩ => ?_
  have esp₂ : s₂.gpr .esp = esp₀ s₀ := by rw [hg₂ _ (by decide), hg₁ _ (by decide)]
  have rd₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [hrd₂, hwr₂, hrd₁, hwr₁]
  refine WP.mono (loadArgs_ok s₂ (by rw [esp₂, rd₂]; exact hp.in_arg (by decide) (by decide))
    (by rw [esp₂, rd₂]; exact hp.in_arg (by decide) (by decide))
    (by rw [esp₂, rd₂]; exact hp.in_arg (by decide) (by decide)))
    fun s₃ ⟨ecx, edx, eax, zf, hg₃, hx₃, hm₃, hrd₃, hwr₃⟩ => ?_
  have m₂ : s₂.mem = s₀.mem := by rw [hm₂, hm₁]
  have a1 : s₂.mem.readW (addr (s₂.gpr .esp) 8) 32 = bp s₀ := by rw [esp₂, m₂]; rfl
  have a2 : s₂.mem.readW (addr (s₂.gpr .esp) 12) 32 = arg s₀ 2 := by rw [esp₂, m₂]; rfl
  have a3 : s₂.mem.readW (addr (s₂.gpr .esp) 16) 32 = scr s₀ := by rw [esp₂, m₂]; rfl
  have lv := loaded_eq s₀.mem hst
  have hc : Common s₀ 0 s₃ :=
    ⟨by rw [hx₃, hx₂ _ (by decide) (by decide), x0, lv.1]; rfl,
      by rw [hx₃, hx₂ _ (by decide) (by decide), x1, lv.2]; rfl,
      by rw [edx, a3],
      fun r ha hc hd => by rw [hg₃ r ha hc hd, hg₂ r ha, hg₁ r hd],
      by rw [hrd₃, hrd₂, hrd₁], by rw [hwr₃, hwr₂, hwr₁], by rw [hm₃, m₂]; exact Frame.refl _ _⟩
  refine ⟨{ hc with x7 := ?_, ecx := ?_, eax := ?_ }, ?_⟩
  · rw [hx₃, x7]
  · rw [ecx, a1]; simp [blkAddr]
  · rw [eax, a2]; simp [nb]
  · rw [zf, a2]

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha1.compressX86.post s₀ s' := by
  refine WP.seq (WP.mono (load_ok hp) fun s₁ ⟨hL₀, hzf⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc => ?_)
  · refine WP.ite (arg s₀ 2 &&& arg s₀ 2 == 0) (by simp only [eval, hzf]) (fun h => ?_) (fun h => ?_)
    · have h0 : nb s₀ = 0 := by
        simp only [BitVec.and_self, beq_iff_eq] at h; simp [nb, h]
      exact WP.block_nil (M := isa) (h0 ▸ hL₀.toCommon)
    · have hpos : 0 < nb s₀ := by
        simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
        exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
      exact loop_ok hp hpos hL₀
  · have hst := hp.st_fits
    have hesp : s₂.gpr .esp = esp₀ s₀ := hc.gpr .esp (by decide) (by decide) (by decide)
    have hf : Frame [stR s₀, scrR s₀] s₀.mem s₂.mem :=
      hc.frame.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]
    refine WP.mono (store_ok s₂ (st s₀) _
      (by rw [hesp, hc.rd, hc.wr]; exact hp.in_arg (by decide) (by decide))
      (by rw [hesp]; exact harg_of hp hf) hst
      (by rw [hc.wr]; exact Pre.st_vec hp (by decide)) (by rw [hc.wr]; exact Pre.st_vec hp (by decide))
      hc.x0 hc.x1)
      fun s' ⟨⟨x, y, hm'⟩, hstate, hg', _, _⟩ => ⟨⟨fun r hr => ?_, ?_⟩, hstate⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      have hne : r ≠ .edx ∧ r ≠ .eax ∧ r ≠ .ecx := by
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [hg' r hne.1, hc.gpr r hne.2.1 hne.2.2 hne.1]
    · have c : ∀ d : Nat, d + 16 ≤ 20 → (stR s₀).Contains (addr (st s₀) d) (128 / 8) :=
        fun d hd => contains_sub hd (by omega) (st_eq hp (by omega))
      have m := List.mem_cons_self (a := stR s₀) (l := [scrR s₀])
      have hf' : Frame [stR s₀, scrR s₀] s₀.mem s'.mem := by
        rw [hm']; exact (hf.writeW m x (c 4 (by decide))).writeW m y (c 0 (by decide))
      exact hf'.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr⟩) (by decide)

theorem compress_verified :
    Verified X86.target Impl.Sha1.X86.ShaNi.compress Proof.Sha1.compressX86 :=
  ⟨fun s hs => correct (pre_of s hs),
    VG.Taint.constantTime (A := sseTaint) Proof.Sha1.X86.τ₀
      (fun _ _ h₁ h₂ hpub => Proof.Sha1.X86.agree₀ h₁ h₂ hpub) (by taint_decide),
    ⟨Proof.Sha1.X86.satState, Proof.Sha1.X86.sat_pre⟩⟩

theorem compress_nosp : NoSp Impl.Sha1.X86.ShaNi.compress := NoSp.of_all (by lit_decide)
theorem compress_stack : stackUse Impl.Sha1.X86.ShaNi.compress = 0 := by lit_decide

end VG.Proof.Sha1.X86.ShaNi
