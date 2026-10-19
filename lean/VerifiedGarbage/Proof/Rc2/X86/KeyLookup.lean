module

import VerifiedGarbage.Proof.Rc2.X86.RoundSteps
public import VerifiedGarbage.Proof.Rc2.X86.PiLookup
public import VerifiedGarbage.Proof.Rc2.X86.KeySteps
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.CallLay
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RC2 on x86: the schedule's word in SSE2 registers

`keyLookup` (`Impl/Rc2/X86/Lookup.lean`) leaves in EAX word `EAX & 63` of
the schedule at EDI (`keyLookup_ok`). Its 32 dwords are visited four at a
time, lane `k` of chunk `c` holding dword `4 c + k`; the dword `d` whose
number is `(EAX & 63) >> 1` survives its mask (`ChunkAt`), and its half is
chosen by bit 0. The lanes pass through the 16 bytes at `[ebp + 48]`.
-/

@[expose] public section

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.Lanes VG.X86.RegUpd VG.Impl.Rc2.X86

/-! ## The values -/

/-- Dword `j` of the schedule at `p`. -/
def sdword (m : Mem) (p : BitVec 32) (j : Nat) : BitVec 32 :=
  m.readW (p.setWidth 64 + BitVec.ofNat 64 (4 * j)) 32

/-- The state of the lookup with chunks `0 … c - 1` visited, from `s₀`, for
dword `d`. -/
structure ChunkAt (s₀ : State) (d c : Nat) (s : State) : Prop where
  x0 : s.xmm .xmm0 = L (splat d)
  x1 : s.xmm .xmm1 = L (found (sdword s₀.mem (s₀.gpr .edi)) d c)
  x2 : s.xmm .xmm2 = L fun k => BitVec.ofNat 32 (4 * c + k)
  x3 : s.xmm .xmm3 = L (splat 4)
  x6 : s.xmm .xmm6 = L (splat 0xFFFFFFFF)
  gpr : s.gpr = s₀.gpr
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem chunk_ok {s₀ s : State} {d c : Nat} (hd : d < 32) (hc : c < 8) (h : ChunkAt s₀ d c s)
    (fit : (s₀.gpr .edi).toNat + 128 ≤ 2 ^ 32)
    (hr : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .edi) (16 * c)) 16) :
    WP isa (.block (lookChunk c)) s fun t => ChunkAt s₀ d (c + 1) t := by
  obtain ⟨h0, h1, h2, h3, h6, hg, hm, hrd, hwr⟩ := h
  have hr' : InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) (16 * c)) 16 := by rw [hrd, hwr, hg]; exact hr
  unfold lookChunk
  lrun [hr']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := decide) only [xmm_setXmm_self, xmm_setXmm_of_ne, movdqa_L, gpr_setXmm, mem_setXmm,
      rd_setXmm, wr_setXmm]
  · exact h0
  · rw [h0, h1, h2, h6, pxor_L, paddd_L, psrld_L, pslld_L, por_L, readW128_L, pand_L, por_L]
    refine L_congr fun k hk => ?_
    have ha : addr (s.gpr .edi) (16 * c) + BitVec.ofNat 64 (4 * k) =
        (s₀.gpr .edi).setWidth 64 + BitVec.ofNat 64 (4 * (4 * c + k)) := by
      rw [hg, addr_eq (by omega), Offset.add_add, show 16 * c + 4 * k = 4 * (4 * c + k) by omega]
    rw [hm, ha, show splat d k = BitVec.ofNat 32 d from rfl,
      show splat 0xFFFFFFFF k = (0xFFFFFFFF : BitVec 32) from rfl,
      mask_eq (by simp only [BitVec.toNat_ofNat]; omega) (by omega)]
    exact found_succ _ (by omega) (by omega) hk
  · rw [h2, h3, paddd_L]
    refine L_congr fun k _ => ?_
    simp only [splat, ← BitVec.ofNat_add]
    congr 1; omega
  · exact h3
  · exact h6
  · exact hg
  · exact hm
  · exact hrd
  · exact hwr

theorem chunks_ok {s₀ : State} {d : Nat} (hd : d < 32)
    (fit : (s₀.gpr .edi).toNat + 128 ≤ 2 ^ 32)
    (hr : ∀ c < 8, InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .edi) (16 * c)) 16) :
    ∀ n ≤ 8, ∀ s, ChunkAt s₀ d 0 s →
      WP isa (.block ((List.range n).flatMap lookChunk)) s fun t => ChunkAt s₀ d n t := by
  intro n hn
  induction n with
  | zero => intro s h; exact WP.block_nil h
  | succ n ih =>
    intro s h
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (ih (by omega) s h) fun t ht => chunk_ok hd (by omega) ht fit (hr n (by omega))

/-! ## The halves of a dword -/

theorem byte_bit (m : Mem) (a : Addr) {i : Nat} (hi : i < 32) :
    (m.readW a 32).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8) := by
  simp only [Mem.readW, BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and]
  exact getLsbD_read _ _ (by omega)

/-- Two bytes as a word, in a dword. -/
theorem pair_bit (x y : Byte) (i : Nat) :
    ((x.setWidth 16 ||| y.setWidth 16 <<< 8).setWidth 32).getLsbD i =
      if i < 8 then x.getLsbD i else if i < 16 then y.getLsbD (i - 8) else false := by
  by_cases h8 : i < 8
  · simp [h8, show i < 16 by omega, show i < 32 by omega]
  · by_cases h16 : i < 16
    · simp [h8, h16, show i < 32 by omega, BitVec.getLsbD_of_ge x i (by omega)]
    · simp [h8, h16, BitVec.getLsbD_of_ge x i (by omega)]

/-- The low half of a dword read, as its two bytes. -/
theorem readW32_lo (m : Mem) (a : Addr) :
    m.readW a 32 &&& BitVec.ofNat 32 (2 ^ 16 - 1) =
      ((m a).setWidth 16 ||| (m (a + BitVec.ofNat 64 1)).setWidth 16 <<< 8).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_and, byte_bit m a hi, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, pair_bit]
  by_cases h8 : i < 8
  · simp [Nat.div_eq_of_lt h8, Nat.mod_eq_of_lt h8, h8, show i < 16 by omega, hi]
  · by_cases h16 : i < 16
    · simp [show i / 8 = 1 by omega, show i % 8 = i - 8 by omega, h8, h16, hi]
    · simp [h8, h16]

/-- The high half of a dword read, as its two bytes. -/
theorem readW32_hi (m : Mem) (a : Addr) :
    m.readW a 32 >>> 16 =
      ((m (a + BitVec.ofNat 64 2)).setWidth 16 ||| (m (a + BitVec.ofNat 64 3)).setWidth 16 <<< 8).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_ushiftRight, pair_bit]
  by_cases h16 : 16 + i < 32
  · rw [byte_bit m a h16]
    by_cases h8 : i < 8
    · simp [show (16 + i) / 8 = 2 by omega, show (16 + i) % 8 = i by omega, h8]
    · simp [show (16 + i) / 8 = 3 by omega, show (16 + i) % 8 = i - 8 by omega, h8, show i < 16 by omega]
  · simp only [Mem.readW, BitVec.getLsbD_setWidth, show ¬ i < 8 by omega, show ¬ i < 16 by omega, ite_false]
    rw [BitVec.getLsbD_of_ge _ _ (by omega), Bool.and_false]


/-! ## The start -/

theorem idx_and (x : BitVec 32) : x &&& 63 = BitVec.ofNat 32 (x.setWidth 6).toNat := by
  have hl : (x.setWidth 6).toNat < 64 := (x.setWidth 6).isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_setWidth]
  exact Nat.and_two_pow_sub_one_eq_mod _ 6

theorem idx_shr (x : BitVec 32) :
    BitVec.ofNat 32 (x.setWidth 6).toNat >>> 1 = BitVec.ofNat 32 ((x.setWidth 6).toNat / 2) := by
  have hl : (x.setWidth 6).toNat < 64 := (x.setWidth 6).isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]

theorem start_ok (s : State) :
    WP isa (.block lookStart) s fun t =>
      ChunkAt t (((s.gpr .eax).setWidth 6).toNat / 2) 0 t ∧
      t.gpr .ebx = BitVec.ofNat 32 ((s.gpr .eax).setWidth 6).toNat ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold lookStart
  lrun [idx_and, idx_shr]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [ne_eq, not_false_eq_true, xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg, gpr_setXmm, gpr_setReg, gpr_setFlags, gpr_arithFlags, mem_setXmm, mem_setReg,
      mem_setFlags, mem_arithFlags, rd_setXmm, rd_setReg, rd_setFlags, rd_arithFlags, wr_setXmm,
      wr_setReg, wr_setFlags, wr_arithFlags, reduceCtorEq, ite_true, ite_false]
  · exact bcast_L _
  · rw [found_zero, XBinOp.eval, BitVec.xor_self]; rfl
  · exact lanes_0123
  · exact bcast_L _
  · exact bcast_L _
  · intro r ha hb hc
    simp only [ha, hb, hc, ite_false]

/-! ## The end -/

theorem lane_read {m : Mem} {B : BitVec 32} (fit : B.toNat + 64 ≤ 2 ^ 32) (f : Nat → BitVec 32) {k : Nat}
    (hk : k < 4) : (m.writeW (addr B 48) (L f)).readW (addr B (48 + 4 * k)) 32 = f k := by
  rw [show addr B (48 + 4 * k) = addr B 48 + BitVec.ofNat 64 (4 * k) by
      rw [addr_eq (by omega), addr_eq (by omega), Offset.add_add],
    readW_writeW128 _ _ _ hk, dword_L _ hk]

theorem half_sel (D : BitVec 32) (i : Nat) :
    (D &&& ((((BitVec.ofNat 32 i &&& 1#32) ^^^ 4294967295#32) + 1#32) ^^^ 4294967295#32) &&& 65535#32 |||
        D >>> 16 &&& (((BitVec.ofNat 32 i &&& 1#32) ^^^ 4294967295#32) + 1#32)) =
      if i % 2 = 0 then D &&& BitVec.ofNat 32 (2 ^ 16 - 1) else D >>> 16 := by
  have hb : BitVec.ofNat 32 i &&& 1#32 = BitVec.ofNat 32 (i % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [show (1 : Nat) % 2 ^ 32 = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [hb]
  rcases Nat.mod_two_eq_zero_or_one i with h | h <;> rw [h]
  · simp only [ite_true]
    rw [show ((BitVec.ofNat 32 0 ^^^ 4294967295#32) + 1#32) = 0#32 by decide,
      show (0#32 ^^^ 4294967295#32) = BitVec.allOnes 32 by decide, BitVec.and_allOnes, BitVec.and_zero,
      BitVec.or_zero]
  · simp only [show (1 = 0) = False by decide, ite_false]
    rw [show ((BitVec.ofNat 32 1 ^^^ 4294967295#32) + 1#32) = BitVec.allOnes 32 by decide,
      show (BitVec.allOnes 32 ^^^ 4294967295#32) = 0#32 by decide, BitVec.and_zero, BitVec.zero_and,
      BitVec.and_allOnes, BitVec.zero_or]

theorem end_ok (t : State) {f : Nat → BitVec 32} {D : BitVec 32} {i : Nat}
    (h1 : t.xmm .xmm1 = L f) (hf : f 0 ||| f 1 ||| f 2 ||| f 3 = D)
    (hb : t.gpr .ebx = BitVec.ofNat 32 i)
    (fit : (t.gpr .ebp).toNat + 64 ≤ 2 ^ 32)
    (hw : InRegions t.wr (addr (t.gpr .ebp) 48) 16) :
    WP isa (.block lookEnd) t fun u =>
      u.gpr .eax = (if i % 2 = 0 then D &&& BitVec.ofNat 32 (2 ^ 16 - 1) else D >>> 16) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → u.gpr r = t.gpr r) ∧
      u.mem = t.mem.writeW (addr (t.gpr .ebp) 48) (t.xmm .xmm1) ∧ u.rd = t.rd ∧ u.wr = t.wr := by
  have hr (k : Nat) (hk : k < 4) : InRegions (t.rd ++ t.wr) (addr (t.gpr .ebp) (48 + 4 * k)) 4 := by
    obtain ⟨r, hr, hc⟩ := CallLay.inRegions_sub (off := 4 * k) (l := 4) hw (by omega) (by decide)
    refine ⟨r, List.mem_append_right _ hr, ?_⟩
    rw [addr_eq (by omega)]
    rw [addr_eq (by omega), Offset.add_add] at hc
    exact hc
  have e (k : Nat) (hk : k < 4) :=
    lane_read (m := t.mem) fit f hk
  rw [← h1] at e
  unfold lookEnd
  lrun [hw, hr 0 (by decide), hr 1 (by decide), hr 2 (by decide), hr 3 (by decide), e 0 (by decide),
    e 1 (by decide), e 2 (by decide), e 3 (by decide), hb]
  refine ⟨?_, ?_, rfl, rfl, rfl⟩ <;>
    simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, reduceCtorEq, ite_true, ite_false]
  · rw [← hf]
    exact half_sel _ i
  · intro r ha hb hc
    simp only [ha, hb, hc, ite_false]


/-! ## The lookup -/

theorem found_or (m : Mem) (p : BitVec 32) {d : Nat} (hd : d < 32) :
    (found (sdword m p) d 8 0 ||| found (sdword m p) d 8 1 ||| found (sdword m p) d 8 2 |||
      found (sdword m p) d 8 3) = sdword m p d := by
  have h4 : d % 4 < 4 := Nat.mod_lt _ (by decide)
  have z : ∀ y : BitVec 32, y ||| 0 = y := fun y => BitVec.eq_of_getLsbD_eq (by simp)
  have z' : ∀ y : BitVec 32, 0 ||| y = y := fun y => BitVec.eq_of_getLsbD_eq (by simp)
  unfold found
  rcases cases4 h4 with h | h | h | h <;>
    simp only [h, show d < 4 * 8 by omega, true_and, ite_true, ite_false,
      show ¬ (0 : Nat) = 1 by decide, show ¬ (0 : Nat) = 2 by decide, show ¬ (0 : Nat) = 3 by decide,
      show ¬ (1 : Nat) = 0 by decide, show ¬ (1 : Nat) = 2 by decide, show ¬ (1 : Nat) = 3 by decide,
      show ¬ (2 : Nat) = 0 by decide, show ¬ (2 : Nat) = 1 by decide, show ¬ (2 : Nat) = 3 by decide,
      show ¬ (3 : Nat) = 0 by decide, show ¬ (3 : Nat) = 1 by decide, show ¬ (3 : Nat) = 2 by decide, z, z']

theorem sdword_word (m : Mem) (p : BitVec 32) {i : Nat} (hi : i < 64) :
    (if i % 2 = 0 then sdword m p (i / 2) &&& BitVec.ofNat 32 (2 ^ 16 - 1) else sdword m p (i / 2) >>> 16) =
      ((Spec.Rc2.scheduleAt m (addr32 p)).getD i 0).setWidth 32 := by
  rw [scheduleAt_getD _ _ _ hi, addr_eq_def]
  unfold sdword
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [ite_eq_left h, readW32_lo, Offset.add_add, show 4 * (i / 2) = 2 * i by omega,
      show 2 * i + 1 = 2 * i + 1 from rfl]
  · rw [ite_eq_right (by omega), readW32_hi, Offset.add_add, Offset.add_add,
      show 4 * (i / 2) + 2 = 2 * i by omega, show 4 * (i / 2) + 3 = 2 * i + 1 by omega]

/-- Word `EAX & 63` of the schedule at EDI, through the 16 bytes at `[ebp + 48]`. -/
theorem keyLookup_ok (s : State)
    (fit : (s.gpr .edi).toNat + 128 ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi)) 128)
    (sfit : (s.gpr .ebp).toNat + 64 ≤ 2 ^ 32)
    (writable : InRegions s.wr (addr (s.gpr .ebp) 48) 16) :
    WP isa (.block keyLookup) s (fun s' =>
      s'.gpr .eax = ((Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .edi))).getD
        ((s.gpr .eax).setWidth 6).toNat 0).setWidth 32 ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨addr (s.gpr .ebp) 48, 16⟩] s.mem s'.mem) := by
  have hi : ((s.gpr .eax).setWidth 6).toNat < 64 := ((s.gpr .eax).setWidth 6).isLt
  rw [keyLookup, List.append_assoc, WP.block_append_iff]
  refine WP.mono (start_ok s) fun t ⟨hc, hb, hg, hm, hrd, hwr⟩ => ?_
  have edi : t.gpr .edi = s.gpr .edi := hg .edi (by decide) (by decide) (by decide)
  have ebp : t.gpr .ebp = s.gpr .ebp := hg .ebp (by decide) (by decide) (by decide)
  have hr : ∀ c < 8, InRegions (t.rd ++ t.wr) (addr (t.gpr .edi) (16 * c)) 16 := fun c hc => by
    rw [hrd, hwr, edi, addr_eq (by omega)]
    exact CallLay.inRegions_sub readable (by omega) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (chunks_ok (by omega) (by rw [edi]; exact fit) hr 8 (Nat.le_refl _) t hc) fun u hu => ?_
  have hw : InRegions u.wr (addr (u.gpr .ebp) 48) 16 := by
    rw [hu.wr, hwr, congrFun hu.gpr .ebp, ebp]; exact writable
  refine WP.mono (end_ok u (i := ((s.gpr .eax).setWidth 6).toNat) hu.x1 (found_or _ _ (by omega))
    (by rw [congrFun hu.gpr .ebx]; exact hb) (by rw [congrFun hu.gpr .ebp, ebp]; exact sfit) hw)
    fun v ⟨he, hg', hm', hrd', hwr'⟩ => ⟨?_, fun r ha hb hc => ?_, ?_, ?_, ?_⟩
  · rw [he, sdword_word _ _ hi, hm, edi]
  · rw [hg' r ha hb hc, congrFun hu.gpr r, hg r ha hb hc]
  · rw [hrd', hu.rd, hrd]
  · rw [hwr', hu.wr, hwr]
  · rw [hm', hu.mem, hm, congrFun hu.gpr .ebp, ebp]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)

end VG.Proof.Rc2.X86
