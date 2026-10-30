module

public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Impl.Rc2.X86.Lookup
public import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
public import VerifiedGarbage.Proof.Framework.X86.SseLanes
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.Sse

/-!
# RC2 on x86: PITABLE in SSE2 registers

`piLookup` (`Impl/Rc2/X86/Lookup.lean`) leaves PITABLE[EAX & 255] in EAX
(`piLookupSse_ok`), keeping memory: the 16 bytes at EDI it passes the result
through are stored back. Lane `k` of group `g` holds PITABLE's dword
`4 g + k` (`piWord`); the dword `q = i >> 2` survives its mask (`LanesAt`),
and its byte `i & 3` is chosen by two conditional shifts.

`lrun`, `splat` and `found` serve the schedule's lookup too
(`KeyLookup.lean`).
-/

@[expose] public section

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.Lanes VG.X86.RegUpd VG.Impl.Rc2.X86

theorem ea_memOp (s : State) (b : Reg) (d : Nat) : s.ea (memOp b d) = addr (s.gpr b) d := rfl

/-- `lrun`: a block run by `simp`, one instruction at a time, the state a
chain of register, flag and memory updates (as `crun`, `Proof/Cast5/X86/Run.lean`). -/
tactic_template "lrun" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
                       apply WP.of_runBlock
                       refine ⟨?_, ?_, ?_⟩
                       rotate_left
                       · set_option linter.unusedSimpArgs false in
                         simp only [runBlock_cons, runStep_some, runBlock_nil, imm, rr,
                         exec, readSrc, ea_memOp, State.load32, State.store32, State.load128, State.store128, execAlu, execShift,
                         XOp.exec, Option.map_some, Option.bind_some,
                         gpr_setReg, mem_setReg, rd_setReg, wr_setReg, xmm_setReg,
                         gpr_setFlags, mem_setFlags, rd_setFlags, wr_setFlags, xmm_setFlags,
                         gpr_arithFlags, mem_arithFlags, rd_arithFlags, wr_arithFlags, xmm_arithFlags,
                         gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, xmm_setXmm_self, xmm_setXmm_of_ne,
                         Option.some.injEq, exists_eq_left',
                         ite_true, ite_false, reduceCtorEq, ↓reduceIte, Nat.reduceMul, Nat.reduceAdd, Nat.reduceLT,
                         Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceEqDiff,
                         and_self, eq_self_iff_true, not_false_eq_true, true_and, and_true, List.cons_append,
                         List.nil_append, $ls,*]
                         first | done | rfl))

/-- `lrun []`. -/
tactic_template "lrun" : tactic => `(tactic| lrun [])

/-! ## Lanes -/

/-- `n` in every lane. -/
noncomputable def splat (n : Nat) : Nat → BitVec 32 := fun _ => BitVec.ofNat 32 n

/-- Lane `k` once the groups `0 … c - 1` of the dwords `tab` are visited, for
dword `d`. -/
noncomputable def found (tab : Nat → BitVec 32) (d c k : Nat) : BitVec 32 :=
  if d < 4 * c ∧ d % 4 = k then tab d else 0

theorem found_succ (tab : Nat → BitVec 32) {d c k : Nat} (hd : d < 64) (hc : c < 16) (hk : k < 4) :
    (found tab d c k ||| (tab (4 * c + k) &&&
        if BitVec.ofNat 32 d = BitVec.ofNat 32 (4 * c + k) then 0xFFFFFFFF else 0)) =
      found tab d (c + 1) k := by
  unfold found
  by_cases h : d = 4 * c + k
  · subst h
    rw [ite_eq_right (by omega), ite_eq_left rfl, ite_eq_left (by omega)]
    rw [show (0xFFFFFFFF : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
    exact BitVec.zero_or
  · have hn : BitVec.ofNat 32 d ≠ BitVec.ofNat 32 (4 * c + k) := fun e => h (by
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat] at this
      omega)
    rw [ite_eq_right hn, show ∀ y : BitVec 32, y &&& 0 = 0 from fun y => BitVec.eq_of_getLsbD_eq (by simp),
      show ∀ y : BitVec 32, y ||| 0 = y from fun y => BitVec.eq_of_getLsbD_eq (by simp)]
    by_cases h2 : d < 4 * c ∧ d % 4 = k
    · rw [ite_eq_left h2, ite_eq_left (by omega)]
    · rw [ite_eq_right h2, ite_eq_right (by omega)]

theorem found_zero (tab : Nat → BitVec 32) (d : Nat) : L (found tab d 0) = 0 := by
  rw [show (0 : BitVec 128) = L fun _ => 0 by decide]
  exact L_congr fun k _ => by simp [found]

/-- The lane numbers `0, 1, 2, 3`. -/
theorem lanes_0123 :
    XBinOp.eval .paddd (shufDwords ((0 : BitVec 96) ++ (1#32)) 17) (shufDwords ((0 : BitVec 96) ++ (2#32)) 5) =
      L fun k => BitVec.ofNat 32 (4 * 0 + k) := by decide

/-- Four dwords, from `movd`s and unpacks. -/
theorem lanes_movd (a b c d : BitVec 32) :
    XBinOp.eval .punpcklqdq (XBinOp.eval .punpckldq ((0 : BitVec 96) ++ a) ((0 : BitVec 96) ++ b))
      (XBinOp.eval .punpckldq ((0 : BitVec 96) ++ c) ((0 : BitVec 96) ++ d)) = ofDwords a b c d := by
  have lo : ∀ v : BitVec 32, dword ((0 : BitVec 96) ++ v) 0 = v := fun v =>
    BitVec.eq_of_getLsbD_eq fun i hi => by
      simp only [dword, BitVec.getLsbD_extractLsb', Nat.mul_zero, Nat.zero_add, hi, decide_true, Bool.true_and,
        BitVec.getLsbD_append, ite_true]
  have hi1 : ∀ v : BitVec 32, dword ((0 : BitVec 96) ++ v) 1 = 0 := fun v =>
    BitVec.eq_of_getLsbD_eq fun i hi => by
      simp only [dword, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
        BitVec.getLsbD_append, show ¬ 32 * 1 + i < 32 by omega, ite_false]
      simp
  rw [punpcklqdq_eq, punpckldq_eq, punpckldq_eq, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_0,
    dword_ofDwords_1, lo, lo, lo, lo]

/-! ## The groups -/

/-- The state of the lookup with groups `0 … c - 1` visited, from `s₀`, for
dword `d`. -/
structure LanesAt (s₀ : State) (d c : Nat) (s : State) : Prop where
  x0 : s.xmm .xmm0 = L (splat d)
  x1 : s.xmm .xmm1 = L (found piWord d c)
  x2 : s.xmm .xmm2 = L fun k => BitVec.ofNat 32 (4 * c + k)
  x3 : s.xmm .xmm3 = L (splat 4)
  x6 : s.xmm .xmm6 = L (splat 0xFFFFFFFF)
  gpr : ∀ r, r ≠ .edx → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem group_ok {s₀ s : State} {d c : Nat} (hd : d < 64) (hc : c < 16) (h : LanesAt s₀ d c s) :
    WP isa (.block (piGroup piWord c)) s fun t => LanesAt s₀ d (c + 1) t := by
  obtain ⟨h0, h1, h2, h3, h6, hg, hm, hrd, hwr⟩ := h
  unfold piGroup piLanes
  lrun
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := decide) only [xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg, movdqa_L, gpr_setXmm,
      gpr_setReg, mem_setXmm, mem_setReg, rd_setXmm, rd_setReg, wr_setXmm, wr_setReg]
  · exact h0
  · rw [lanes_movd, h0, h1, h2, h6, pxor_L, paddd_L, psrld_L, pslld_L, por_L,
      show ofDwords (piWord (4 * c)) (piWord (4 * c + 1)) (piWord (4 * c + 2)) (piWord (4 * c + 3)) =
        L fun k => piWord (4 * c + k) from rfl, pand_L, por_L]
    refine L_congr fun k hk => ?_
    rw [show splat d k = BitVec.ofNat 32 d from rfl,
      show splat 0xFFFFFFFF k = (0xFFFFFFFF : BitVec 32) from rfl,
      mask_eq (by simp only [BitVec.toNat_ofNat]; omega) (by omega)]
    exact found_succ _ hd hc hk
  · rw [h2, h3, paddd_L]
    refine L_congr fun k _ => ?_
    simp only [splat, ← BitVec.ofNat_add]
    congr 1; omega
  · exact h3
  · exact h6
  · intro r hr
    simp only [hr, ite_false]
    exact hg r hr
  · exact hm
  · exact hrd
  · exact hwr

theorem groups_ok {s₀ : State} {d : Nat} (hd : d < 64) :
    ∀ n ≤ 16, ∀ s, LanesAt s₀ d 0 s →
      WP isa (.block ((List.range n).flatMap (piGroup piWord))) s fun t => LanesAt s₀ d n t := by
  intro n hn
  induction n with
  | zero => intro s h; exact WP.block_nil h
  | succ n ih =>
    intro s h
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (ih (by omega) s h) fun t ht => group_ok hd (by omega) ht


/-! ## The start -/

theorem idx_and255 (x : BitVec 32) : x &&& 255 = BitVec.ofNat 32 (x.setWidth 8).toNat := by
  have hl : (x.setWidth 8).toNat < 256 := (x.setWidth 8).isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_setWidth]
  exact Nat.and_two_pow_sub_one_eq_mod _ 8

theorem idx_shr2 (x : BitVec 32) :
    BitVec.ofNat 32 (x.setWidth 8).toNat >>> 2 = BitVec.ofNat 32 ((x.setWidth 8).toNat / 4) := by
  have hl : (x.setWidth 8).toNat < 256 := (x.setWidth 8).isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]

theorem piStartSse_ok (s : State) :
    WP isa (.block piStart) s fun t =>
      LanesAt t (((s.gpr .eax).setWidth 8).toNat / 4) 0 t ∧
      t.gpr .ebx = BitVec.ofNat 32 ((s.gpr .eax).setWidth 8).toNat ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edx → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold piStart
  lrun [idx_and255, idx_shr2]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, fun _ _ => rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [ne_eq, not_false_eq_true, xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg, gpr_setXmm,
      gpr_setReg, gpr_setFlags, gpr_arithFlags, mem_setXmm, mem_setReg,
      mem_setFlags, mem_arithFlags, rd_setXmm, rd_setReg, rd_setFlags, rd_arithFlags, wr_setXmm, wr_setReg,
      wr_setFlags, wr_arithFlags,
      reduceCtorEq, ite_true, ite_false]
  · exact bcast_L _
  · rw [found_zero, XBinOp.eval, BitVec.xor_self]; rfl
  · exact lanes_0123
  · exact bcast_L _
  · exact bcast_L _
  · intro r ha hb hc
    simp only [ha, hb, hc, ite_false]

/-! ## The end -/

theorem or_zero32 (y : BitVec 32) : y ||| 0 = y := BitVec.eq_of_getLsbD_eq (by simp)
theorem zero_or32 (y : BitVec 32) : 0 ||| y = y := BitVec.eq_of_getLsbD_eq (by simp)

/-- The lanes ORed together, into every lane. -/
theorem orLanes {d : Nat} (D : BitVec 32) :
    XBinOp.eval .por
        (XBinOp.eval .por (L fun k => if d % 4 = k then D else 0)
          (shufDwords (L fun k => if d % 4 = k then D else 0) 0x4E))
        (shufDwords (XBinOp.eval .por (L fun k => if d % 4 = k then D else 0)
          (shufDwords (L fun k => if d % 4 = k then D else 0) 0x4E)) 0xB1) = L fun _ => D := by
  refine L_ext fun k hk => ?_
  have h4 : d % 4 < 4 := Nat.mod_lt _ (by decide)
  rcases cases4 hk with rfl | rfl | rfl | rfl <;>
  rcases cases4 h4 with h | h | h | h <;>
    simp (disch := decide) only [dword_por, dword_shufDwords, dword_L, h, ite_true, ite_false,
      or_zero32, zero_or32, Nat.reduceMul,
      show (BitVec.extractLsb' 0 2 (78 : BitVec 8)).toNat = 2 from rfl, show (BitVec.extractLsb' 2 2 (78 : BitVec 8)).toNat = 3 from rfl, show (BitVec.extractLsb' 4 2 (78 : BitVec 8)).toNat = 0 from rfl, show (BitVec.extractLsb' 6 2 (78 : BitVec 8)).toNat = 1 from rfl,
      show (BitVec.extractLsb' 0 2 (177 : BitVec 8)).toNat = 1 from rfl, show (BitVec.extractLsb' 2 2 (177 : BitVec 8)).toNat = 0 from rfl, show (BitVec.extractLsb' 4 2 (177 : BitVec 8)).toNat = 3 from rfl, show (BitVec.extractLsb' 6 2 (177 : BitVec 8)).toNat = 2 from rfl,
      show ¬ (0 : Nat) = 1 by decide, show ¬ (0 : Nat) = 2 by decide,
      show ¬ (0 : Nat) = 3 by decide, show ¬ (1 : Nat) = 0 by decide, show ¬ (1 : Nat) = 2 by decide,
      show ¬ (1 : Nat) = 3 by decide, show ¬ (2 : Nat) = 0 by decide, show ¬ (2 : Nat) = 1 by decide,
      show ¬ (2 : Nat) = 3 by decide, show ¬ (3 : Nat) = 0 by decide, show ¬ (3 : Nat) = 1 by decide,
      show ¬ (3 : Nat) = 2 by decide]

theorem found_end {d : Nat} (hd : d < 64) :
    L (found piWord d 16) = L fun k => if d % 4 = k then piWord d else 0 :=
  L_congr fun k _ => by simp only [found, show d < 4 * 16 by omega, true_and]


theorem psrld_L' (f : Nat → BitVec 32) {n : Nat} (hn : n < 32) :
    XShiftOp.eval .psrld (L f) (BitVec.ofNat 8 n) = L fun k => f k >>> n :=
  L_ext fun k hk => by
    rw [dword_psrld _ _ (by rw [BitVec.toNat_ofNat]; omega) hk, dword_L _ hk, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]

/-- `-(m & 1)`: all ones if `m` is odd. -/
theorem mask_bit (m : Nat) (hm : m < 2 ^ 32) :
    ((BitVec.ofNat 32 m &&& (1 : BitVec 32)) ^^^ (4294967295 : BitVec 32)) + (1 : BitVec 32) =
      if m % 2 = 1 then BitVec.allOnes 32 else 0 := by
  have hb : BitVec.ofNat 32 m &&& (1 : BitVec 32) = BitVec.ofNat 32 (m % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (1 : BitVec 32).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [hb]
  rcases Nat.mod_two_eq_zero_or_one m with h | h <;> rw [h] <;> decide

/-- `v ^ ((v >> n ^ v) & mask)`: `v >> n` where the mask is all ones. -/
theorem sel_shift (v : BitVec 32) (n : Nat) (c : Prop) [Decidable c] :
    v ^^^ ((v >>> n ^^^ v) &&& (if c then BitVec.allOnes 32 else 0)) = if c then v >>> n else v := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h, BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_comm v,
      BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · rw [ite_eq_right h, ite_eq_right h, show ∀ y : BitVec 32, y &&& 0 = 0 from fun y => BitVec.eq_of_getLsbD_eq (by simp),
      show ∀ y : BitVec 32, y ^^^ 0 = y from fun y => BitVec.eq_of_getLsbD_eq (by simp)]

theorem idx_shr1 {i : Nat} (hi : i < 256) : BitVec.ofNat 32 i >>> 1 = BitVec.ofNat 32 (i / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]

set_option linter.unusedSimpArgs false in
/-- Shift every lane of `xmm1` right by `sh` if bit `n` (0 or 1) of `EBX` is
set, the mask in `x` (`xmm2` or `xmm3`). -/
theorem selBit_ok (s : State) {x : XReg} (hx : x = .xmm2 ∨ x = .xmm3) {n sh : Nat} (hn : n = 0 ∨ n = 1)
    (hsh : sh < 32) {i : Nat} (hi : i < 256) {v : BitVec 32}
    (h1 : s.xmm .xmm1 = L fun _ => v) (hb : s.gpr .ebx = BitVec.ofNat 32 i) :
    WP isa (.block (bitMask x n ++ shiftIf x sh)) s fun t =>
      t.xmm .xmm1 = (L fun _ => if i / 2 ^ n % 2 = 1 then v >>> sh else v) ∧
      (∀ r, r ≠ .edx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hm0 : ((BitVec.ofNat 32 i &&& (1 : BitVec 32)) ^^^ (4294967295 : BitVec 32)) + (1 : BitVec 32) =
      if i / 2 ^ 0 % 2 = 1 then BitVec.allOnes 32 else 0 := by
    rw [Nat.pow_zero, Nat.div_one]; exact mask_bit i (by omega)
  have hm1 : ((BitVec.ofNat 32 i >>> 1 &&& (1 : BitVec 32)) ^^^ (4294967295 : BitVec 32)) + (1 : BitVec 32) =
      if i / 2 ^ 1 % 2 = 1 then BitVec.allOnes 32 else 0 := by
    rw [idx_shr1 hi, Nat.pow_one]; exact mask_bit _ (by omega)
  rcases hx with rfl | rfl <;> rcases hn with rfl | rfl <;> unfold bitMask shiftIf <;> lrun [hb] <;>
    refine ⟨?_, ?_, rfl, rfl, rfl⟩
  all_goals first
    | (intro r hr
       simp (disch := decide) only [gpr_setXmm, gpr_setReg, gpr_setFlags, gpr_arithFlags, hr, ite_false])
    | (simp (disch := decide) only [xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg, xmm_setFlags,
         xmm_arithFlags, movdqa_L, ite_true, ite_false, reduceCtorEq]
       rw [h1, psrld_L' _ hsh, pxor_L]
       first | rw [hm0] | rw [hm1]
       rw [bcast_L, pand_L, pxor_L]
       exact L_congr fun k _ => sel_shift _ _ _)


/-! ## Through EDI -/

/-- A write over a write of what was there. -/
theorem writeW_restore (m : Mem) (a : Addr) (X : BitVec 128) :
    (m.writeW a X).writeW a (m.readW a 128) = m := by
  funext x
  simp only [Mem.writeW, Mem.write]
  by_cases h : (x - a).toNat < 128 / 8
  · rw [ite_eq_left h]
    have e := byte_readW m a (w := 128) (k := (x - a).toNat) (by omega)
    rw [show BitVec.setWidth (8 * (128 / 8)) (m.readW a 128) = m.readW a 128 from BitVec.setWidth_eq _, e,
      BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  · rw [ite_eq_right h, ite_eq_right h]

theorem readW_writeW128_0 (m : Mem) (a : Addr) (X : BitVec 128) : (m.writeW a X).readW a 32 = dword X 0 := by
  have := readW_writeW128 m a X (j := 0) (by decide)
  simpa using this

/-- Lane 0 of `xmm1`'s low byte, through the 16 bytes at EDI, stored back. -/
theorem extract_ok (s : State) (hw : InRegions s.wr (addr (s.gpr .edi) 0) 16) :
    WP isa (.block [.movdquLoad .xmm7 (memOp .edi 0), .movdquStore (memOp .edi 0) .xmm1,
      .mov .eax (.mem (memOp .edi 0)), .movdquStore (memOp .edi 0) .xmm7, .alu .and .eax (.imm 255)]) s
      fun t => t.gpr .eax = dword (s.xmm .xmm1) 0 &&& 255 ∧ (∀ r, r ≠ .eax → t.gpr r = s.gpr r) ∧
        t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨r, hr, hc⟩ := hw
  have hrd : InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) 0) 16 := ⟨r, List.mem_append_right _ hr, hc⟩
  have hrd4 : InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) 0) 4 :=
    ⟨r, List.mem_append_right _ hr, by simp only [Region.Contains] at hc ⊢; omega⟩
  have hw' : InRegions s.wr (addr (s.gpr .edi) 0) 16 := ⟨r, hr, hc⟩
  lrun [hrd, hrd4, hw']
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, readW_writeW128_0]
  · intro r' hr'
    simp only [gpr_setReg, gpr_arithFlags, hr', ite_false]
  · show (_ : Mem) = _
    simp only [mem_setReg, mem_arithFlags]
    exact writeW_restore _ _ _

/-! ## The byte -/

theorem byte4 (x0 x1 x2 x3 : BitVec 8) {b : Nat} (hb : b < 4) :
    ((x0.setWidth 32 ||| x1.setWidth 32 <<< 8 ||| x2.setWidth 32 <<< 16 ||| x3.setWidth 32 <<< 24) >>> (8 * b)) &&&
      BitVec.ofNat 32 (2 ^ 8 - 1) = ([x0, x1, x2, x3].getD b 0).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  rcases cases4 hb with rfl | rfl | rfl | rfl <;>
  by_cases h8 : j < 8 <;>
    simp (disch := omega) [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hj, h8,
      BitVec.getLsbD_of_ge, decide_eq_true, decide_eq_false]


theorem pi_sel (i : Nat) :
    (if i / 2 ^ 0 % 2 = 1 then
        (if i / 2 ^ 1 % 2 = 1 then piWord (i / 4) >>> 16 else piWord (i / 4)) >>> 8
      else if i / 2 ^ 1 % 2 = 1 then piWord (i / 4) >>> 16 else piWord (i / 4)) &&& (255 : BitVec 32) =
      (Spec.Rc2.piTable.getD i 0).setWidth 32 := by
  rw [show (255 : BitVec 32) = BitVec.ofNat 32 (2 ^ 8 - 1) from rfl, Nat.pow_zero, Nat.pow_one, Nat.div_one]
  have hb : i % 4 < 4 := Nat.mod_lt _ (by decide)
  have e : i = 4 * (i / 4) + i % 4 := by omega
  have key : (piWord (i / 4) >>> (8 * (i % 4))) &&& BitVec.ofNat 32 (2 ^ 8 - 1) =
      ([Spec.Rc2.piTable.getD (4 * (i / 4)) 0, Spec.Rc2.piTable.getD (4 * (i / 4) + 1) 0,
        Spec.Rc2.piTable.getD (4 * (i / 4) + 2) 0, Spec.Rc2.piTable.getD (4 * (i / 4) + 3) 0].getD (i % 4) 0).setWidth 32 :=
    byte4 _ _ _ _ hb
  rcases cases4 hb with h | h | h | h
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [h] at key
    have := key
    simp only [Nat.mul_zero, BitVec.ushiftRight_zero, List.getD_cons_zero] at this
    rw [this, show 4 * (i / 4) = i by omega]
  · rw [ite_eq_left (by omega), ite_eq_right (by omega)]
    rw [h] at key
    have := key
    simp only [Nat.mul_one, List.getD_cons_succ, List.getD_cons_zero] at this
    rw [this, show 4 * (i / 4) + 1 = i by omega]
  · rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    rw [h] at key
    have := key
    simp only [List.getD_cons_succ, List.getD_cons_zero, show 8 * 2 = 16 from rfl] at this
    rw [this, show 4 * (i / 4) + 2 = i by omega]
  · rw [ite_eq_left (by omega), ite_eq_left (by omega), ← BitVec.shiftRight_add]
    rw [h] at key
    have := key
    simp only [List.getD_cons_succ, List.getD_cons_zero, show 8 * 3 = 16 + 8 from rfl] at this
    rw [this, show 4 * (i / 4) + 3 = i by omega]

/-- The lanes ORed together, into every lane. -/
theorem orStep_ok (s : State) {d : Nat} (hd : d < 64) (h1 : s.xmm .xmm1 = L (found piWord d 16)) :
    WP isa (.block [.xop (.pshufd .xmm4 .xmm1 0x4E), .xop (.bin .por .xmm1 .xmm4),
      .xop (.pshufd .xmm4 .xmm1 0xB1), .xop (.bin .por .xmm1 .xmm4)]) s fun t =>
      t.xmm .xmm1 = (L fun _ => piWord d) ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  lrun
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  simp only [xmm_setXmm_self]
  rw [h1, found_end hd]
  exact orLanes _

/-- PITABLE[EAX & 255] into EAX, keeping memory. -/
theorem piLookupSse_ok (s : State) (hw : InRegions s.wr (addr (s.gpr .edi) 0) 16) :
    WP isa (.block piLookup) s fun t =>
      t.gpr .eax = (Spec.Rc2.pi ((s.gpr .eax).setWidth 8)).setWidth 32 ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hi : ((s.gpr .eax).setWidth 8).toNat < 256 := ((s.gpr .eax).setWidth 8).isLt
  rw [piLookup, piLookupWith, List.append_assoc, WP.block_append_iff]
  refine WP.mono (piStartSse_ok s) fun t ⟨hl, hb, hg, hm, hrd, hwr⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (groups_ok (by omega) 16 (Nat.le_refl _) t hl) fun u hu => ?_
  have edi : u.gpr .edi = s.gpr .edi := (hu.gpr .edi (by decide)).trans (hg .edi (by decide) (by decide) (by decide))
  unfold piEnd
  simp only [List.append_assoc]
  rw [show ([.xop (.pshufd .xmm4 .xmm1 0x4E), .xop (.bin .por .xmm1 .xmm4), .xop (.pshufd .xmm4 .xmm1 0xB1),
      .xop (.bin .por .xmm1 .xmm4)] : List Instr) ++ _ = _ ++ _ from rfl, WP.block_append_iff]
  refine WP.mono (orStep_ok u (by omega) hu.x1) fun v ⟨v1, vg, vm, vrd, vwr⟩ => ?_
  have vb : v.gpr .ebx = BitVec.ofNat 32 ((s.gpr .eax).setWidth 8).toNat := by
    rw [vg, hu.gpr .ebx (by decide)]; exact hb
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (selBit_ok v (.inl rfl) (.inr rfl) (by decide) hi v1 vb) fun w ⟨w1, wg, wm, wrd, wwr⟩ => ?_
  have wb : w.gpr .ebx = BitVec.ofNat 32 ((s.gpr .eax).setWidth 8).toNat := by rw [wg .ebx (by decide)]; exact vb
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (selBit_ok w (.inr rfl) (.inl rfl) (by decide) hi w1 wb) fun x ⟨x1, xg, xm, xrd, xwr⟩ => ?_
  have xedi : x.gpr .edi = s.gpr .edi := by rw [xg .edi (by decide), wg .edi (by decide), vg]; exact edi
  have hw' : InRegions x.wr (addr (x.gpr .edi) 0) 16 := by
    rw [xwr, wwr, vwr, hu.wr, hwr, xedi]; exact hw
  refine WP.mono (extract_ok x hw') fun y ⟨y1, yg, ym, yrd, ywr⟩ => ⟨?_, fun r ha hb' hd => ?_, ?_, ?_, ?_⟩
  · rw [y1, x1, dword_L _ (by decide), pi_sel _]; rfl
  · rw [yg r ha, xg r hd, wg r hd, vg, hu.gpr r hd, hg r ha hb' hd]
  · rw [ym, xm, wm, vm, hu.mem, hm]
  · rw [yrd, xrd, wrd, vrd, hu.rd, hrd]
  · rw [ywr, xwr, wwr, vwr, hu.wr, hwr]

end VG.Proof.Rc2.X86
