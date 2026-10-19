module

public import VerifiedGarbage.Impl.Rc2.Arm.Lookup
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Rc2
public import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.Select32

/-! # Correctness of the baseline Arm RC2 key lookup

`keyLookup` visits the 32 words of the key schedule at `r0`, eight entries
(four words) per iteration from the last, and leaves the entry at the index
in `r12` (`keyLookup_ok`). With `z` the index plus 8 XOR the counter, each
pair of words is multiplied by a bit that is 1 exactly when the index is one
of its four entries (`pairBits`); the index's word of the pair kept, and its
half of that word, are then selected (`keySelect_ok`). -/

@[expose] public section

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Proof.Rc2.Word32

/-- A register-only block preserves memory, regions, and other GPRs. -/
structure Keep (written : List Reg) (s s' : State) : Prop where
  reg : ∀ r, r ∉ written → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keep.trans {rs : List Reg} {s s' s'' : State}
    (h : Keep rs s s') (h' : Keep rs s' s'') : Keep rs s s'' :=
  ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), h'.mem.trans h.mem,
    h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem Keep.weaken {rs rs' : List Reg} {s s' : State} (h : Keep rs s s')
    (hsub : ∀ r ∈ rs, r ∈ rs') : Keep rs' s s' :=
  ⟨fun r hr => h.reg r (fun hm => hr (hsub r hm)), h.mem, h.rd, h.wr⟩

theorem maskBits (x : BitVec 32) (n : Nat) (hn : n ≤ 32) :
    x <<< (32 - n) >>> (32 - n) = (x.setWidth n).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  have ha : 32 - n + i < 32 ↔ i < n := by omega
  have hb : ¬32 - n + i < 32 - n := by omega
  simp only [ha, hb, hi, decide_true, decide_false, Bool.not_false,
    Bool.and_true, Bool.true_and, Nat.add_sub_cancel_left]

theorem scheduleAt_getD (m : Mem) (p : Addr) (i : Nat) (hi : i < 64) :
    (Spec.Rc2.scheduleAt m p).getD i 0 =
      (m (p + BitVec.ofNat 64 (2 * i))).setWidth 16 |||
        (m (p + BitVec.ofNat 64 (2 * i + 1))).setWidth 16 <<< 8 := by
  simp [Spec.Rc2.scheduleAt, Vector.getD, hi]

/-- Any `n` bytes at offset `d` of the 128 bytes of the key schedule. -/
theorem key_in {rs : List Region} {a : Addr} (h : InRegions rs a 128) {d n : Nat}
    (hd : d + n ≤ 128) : InRegions rs (a + BitVec.ofNat 64 d) n := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  unfold Region.Contains at hc ⊢
  rw [BitVec.add_sub_comm, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega)]
  have := Nat.mod_le ((a - r.base).toNat + d) (2 ^ 64)
  omega

/-- The registers a key lookup writes. -/
def lookupRegs : List Reg := [.r12, .r3, .r8, .r9, .r10, .r11, .lr]

/-- The registers the loop of a key lookup writes. -/
def scanRegs : List Reg := [.r3, .r8, .r9, .r10, .r11, .lr]

/-- Word `q` of the key schedule at `K` in `m`: entries `2 q` and `2 q + 1`. -/
def kw (m : Mem) (K : BitVec 32) (q : Nat) : BitVec 32 :=
  m.readW (State.addr K + BitVec.ofNat 64 (4 * q)) 32

/-- Accumulator `k` once the entries from `8 lim` on are visited: word
`2 (x / 4) + k`, of the four entries of the index `x`, if they are among
them. -/
def kAcc (m : Mem) (K : BitVec 32) (x lim k : Nat) : BitVec 32 :=
  if lim ≤ x / 8 then kw m K (2 * (x / 4) + k) else 0

/-- The bits of a pair of words: with `z` the index plus 8 XOR the counter
`8 (p + 1)`, `z < 4` exactly when the index is one of entries `8 p … 8 p +
3`, and `z ^ 4 < 4` exactly when it is one of `8 p + 4 … 8 p + 7`. -/
theorem pairBits : ∀ x < 64, ∀ p < 8,
    ((BitVec.ofNat 32 (x + 8) ^^^ BitVec.ofNat 32 (8 * (p + 1))) - 4) >>> 31 =
      (if x / 4 = 2 * p then 1 else 0 : BitVec 32) ∧
    (((BitVec.ofNat 32 (x + 8) ^^^ BitVec.ofNat 32 (8 * (p + 1))) ^^^ 4) - 4) >>> 31 =
      (if x / 4 = 2 * p + 1 then 1 else 0 : BitVec 32) := by
  decide +kernel

/-- The bits of the index that select its word and its half. -/
theorem indexBits : ∀ x < 64,
    (BitVec.ofNat 32 (x + 8) >>> 1 &&& 1) = (if x / 2 % 2 = 1 then 1 else 0 : BitVec 32) ∧
    (BitVec.ofNat 32 (x + 8) &&& 1) = (if x % 2 = 1 then 1 else 0 : BitVec 32) := by
  decide +kernel

theorem mul_bit (w : BitVec 32) (c : Prop) [Decidable c] :
    w * (if c then 1 else 0 : BitVec 32) = if c then w else 0 := by
  split
  · exact BitVec.mul_one w
  · exact BitVec.mul_zero

theorem or_ite_zero (a w : BitVec 32) (c : Prop) [Decidable c] :
    (a ||| if c then w else 0) = if c then a ||| w else a := by
  split
  · rfl
  · exact BitVec.or_zero

theorem xor_select (a b : BitVec 32) (c : Prop) [Decidable c] :
    a ^^^ (b ^^^ a) * (if c then 1 else 0 : BitVec 32) = if c then b else a := by
  rw [mul_bit]
  split
  · rw [BitVec.xor_comm b a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · exact BitVec.xor_zero

theorem xor_select' (a b : BitVec 32) (c : Prop) [Decidable c] :
    a ^^^ (a ^^^ b) * (if c then 1 else 0 : BitVec 32) = if c then b else a := by
  rw [mul_bit]
  split
  · rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · exact BitVec.xor_zero

theorem extractHalf (x : BitVec 32) (i : Nat) :
    ((x.extractLsb' (8 * (2 * i)) 8).setWidth 16 |||
      (x.extractLsb' (8 * (2 * i + 1)) 8).setWidth 16 <<< 8) =
        (x >>> (16 * i)).setWidth 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight]
  by_cases h : j < 8
  · simp only [hj, h, decide_true, Bool.true_and, Bool.not_true,
      Bool.false_and, Bool.or_false]
    apply congrArg x.getLsbD
    omega
  · simp only [hj, h, decide_true, Bool.true_and, decide_false, Bool.false_and,
      Bool.not_false, Bool.false_or, show j - 8 < 16 by omega, show j - 8 < 8 by omega]
    apply congrArg x.getLsbD
    omega

theorem maskBits16 (x : BitVec 32) : x <<< 16 >>> 16 = (x.setWidth 16).setWidth 32 :=
  maskBits x 16 (by decide)

theorem encodable_imm : encodable (1 : BitVec 32) = true ∧ encodable (4 : BitVec 32) = true ∧
    encodable (8 : BitVec 32) = true ∧ encodable (16 : BitVec 32) = true ∧
    encodable (63 : BitVec 32) = true ∧ encodable (112 : BitVec 32) = true := by decide

theorem gpr_subFlags_lookup (s : State) (x y : BitVec 32) (r : Reg) :
    (subFlags s x y).gpr r = s.gpr r := rfl

/-- The pair of words at `lr + off`, `lr + off + 4`, under the bit from `z`
in `r10`. -/
theorem keyPair_ok (s : State) (off : Nat) (hoff : off + 4 < 4096)
    (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 (off + 4))) 4) :
    ∃ s', runBlock isa (keyPair off) s = some s' ∧
      s'.gpr .r3 = s.gpr .r3 ||| s.gpr .r8 * ((s.gpr .r10 - 4) >>> 31) ∧
      s'.gpr .r11 = s.gpr .r11 |||
        s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 (off + 4))) 32 * ((s.gpr .r10 - 4) >>> 31) ∧
      Keep [.r3, .r8, .r10, .r11] s s' := by
  refine ⟨_, by
    simp only [keyPair, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some,
      State.load32, encodable_imm, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, reduceCtorEq,
      hoff, hin, Nat.reduceLeDiff, and_self, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h3, h8, h10, h11⟩ := hr
      simp only [gpr_setReg, h3, h8, h10, h11, ite_false]
    · rfl
    · rfl
    · rfl

/-- The state of the scan from `s₀` before the eight entries from `8 p`,
the entries after them visited. -/
structure KeyScanAt (s₀ : State) (x p : Nat) (s : State) : Prop where
  r12 : s.gpr .r12 = BitVec.ofNat 32 (x + 8)
  r9 : s.gpr .r9 = BitVec.ofNat 32 (8 * (p + 1))
  lr : s.gpr .lr = s₀.gpr .r0 + BitVec.ofNat 32 (16 * p)
  r3 : s.gpr .r3 = kAcc s₀.mem (s₀.gpr .r0) x (p + 1) 0
  r11 : s.gpr .r11 = kAcc s₀.mem (s₀.gpr .r0) x (p + 1) 1
  keep : Keep scanRegs s₀ s

theorem lk_or_zero (v : BitVec 32) : v ||| 0 = v := BitVec.eq_of_getLsbD_eq (by simp)

theorem lk_zero_or (v : BitVec 32) : 0 ||| v = v := BitVec.eq_of_getLsbD_eq (by simp)

theorem kAcc_step (m : Mem) (K : BitVec 32) {x p : Nat} (k : Nat) {q₀ q₁ : Nat}
    (h₀ : q₀ = 4 * p + k) (h₁ : q₁ = 4 * p + 2 + k) :
    ((kAcc m K x (p + 1) k ||| if x / 4 = 2 * p then kw m K q₀ else 0) |||
      if x / 4 = 2 * p + 1 then kw m K q₁ else 0) = kAcc m K x p k := by
  unfold kAcc
  by_cases h : x / 8 = p
  · rw [ite_eq_right (show ¬p + 1 ≤ x / 8 by omega), ite_eq_left (show p ≤ x / 8 by omega), lk_zero_or]
    by_cases h' : x / 4 = 2 * p
    · rw [ite_eq_left h', ite_eq_right (show ¬x / 4 = 2 * p + 1 by omega), lk_or_zero]
      exact congrArg (kw m K) (by omega)
    · rw [ite_eq_right h', ite_eq_left (show x / 4 = 2 * p + 1 by omega), lk_zero_or]
      exact congrArg (kw m K) (by omega)
  · rw [ite_eq_right (show ¬x / 4 = 2 * p by omega), ite_eq_right (show ¬x / 4 = 2 * p + 1 by omega),
      lk_or_zero, lk_or_zero]
    by_cases h' : p + 1 ≤ x / 8
    · rw [ite_eq_left h', ite_eq_left (show p ≤ x / 8 by omega)]
    · rw [ite_eq_right h', ite_eq_right (show ¬p ≤ x / 8 by omega)]

theorem key_addr {K : BitVec 32} (fit : K.toNat + 128 ≤ 2 ^ 32) {p d : Nat} (hd : 16 * p + d < 128) :
    State.addr (K + BitVec.ofNat 32 (16 * p) + BitVec.ofNat 32 d) =
      State.addr K + BitVec.ofNat 64 (16 * p + d) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, addr_add (by omega)]

theorem keyHead_ok (s : State) (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) 4) :
    ∃ s', runBlock isa [.ldr .r8 .lr 0, .dp .eor .r10 .r12 (.reg .r9)] s = some s' ∧
      s'.gpr .r8 = s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) 32 ∧
      s'.gpr .r10 = s.gpr .r12 ^^^ s.gpr .r9 ∧ Keep [.r8, .r10] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some,
      State.load32, hin, Nat.reduceLT, ite_true]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2, ite_false]
    · rfl
    · rfl
    · rfl

theorem keyHead4_ok (s : State) (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 8)) 4) :
    ∃ s', runBlock isa [.ldr .r8 .lr 8, .dp .eor .r10 .r12 (.reg .r9), .dp .eor .r10 .r10 (.imm 4)] s = some s' ∧
      s'.gpr .r8 = s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 8)) 32 ∧
      s'.gpr .r10 = (s.gpr .r12 ^^^ s.gpr .r9) ^^^ 4 ∧ Keep [.r8, .r10] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some,
      State.load32, hin, encodable_imm, Nat.reduceLT, ite_true]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2, ite_false]
    · rfl
    · rfl
    · rfl

theorem keyNext_ok (s : State) :
    ∃ s', runBlock isa [.dp .sub .lr .lr (.imm 16), .subs .r9 .r9 (.imm 8)] s = some s' ∧
      s'.gpr .lr = s.gpr .lr - 16 ∧ s'.gpr .r9 = s.gpr .r9 - 8 ∧ s'.z = (s.gpr .r9 - 8 == 0) ∧
      Keep [.r9, .lr] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some,
      encodable_imm, ite_true]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_subFlags_lookup, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_setReg, gpr_subFlags_lookup, reduceCtorEq, ite_true, ite_false]
  · simp only [z_setReg, gpr_setReg, reduceCtorEq, ite_false]; rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_subFlags_lookup, hr.1, hr.2, ite_false]
    · rfl
    · rfl
    · rfl

theorem keep_scan {rs : List Reg} {s s' : State} (h : Keep rs s s') (hrs : ∀ r ∈ rs, r ∈ scanRegs) :
    Keep scanRegs s s' := h.weaken hrs

/-- Eight entries: each accumulator gains its word of the index's four
entries if they are among them; on to the eight before. -/
theorem keyScan_step {s₀ s : State} {x p : Nat} (hx : x < 64) (hp : p < 8)
    (fit : (s₀.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.gpr .r0)) 128)
    (h : KeyScanAt s₀ x p s) :
    WP isa (.block keyBody) s fun t =>
      (p = 0 → kAcc s₀.mem (s₀.gpr .r0) x 0 0 = t.gpr .r3 ∧ kAcc s₀.mem (s₀.gpr .r0) x 0 1 = t.gpr .r11 ∧
        t.gpr .r12 = BitVec.ofNat 32 (x + 8) ∧ Keep scanRegs s₀ t) ∧
      (0 < p → KeyScanAt s₀ x (p - 1) t) ∧ t.z = decide (p = 0) := by
  have bits := pairBits x hx p hp
  -- Every state of the body has `s`'s memory, regions, `lr`, `r9` and `r12`
  -- until the last two instructions.
  have kin {t : State} (k : Keep scanRegs s t) (hl : t.gpr .lr = s.gpr .lr) (d : Nat)
      (hd : 16 * p + d + 4 ≤ 128) :
      InRegions (t.rd ++ t.wr) (State.addr (t.gpr .lr + BitVec.ofNat 32 d)) 4 := by
    rw [k.rd, k.wr, hl, h.keep.rd, h.keep.wr, h.lr, key_addr fit (by omega)]
    exact key_in readable hd
  have kword {t : State} (k : Keep scanRegs s t) (hl : t.gpr .lr = s.gpr .lr) (d : Nat)
      (q : Nat) (hq : d = 4 * q) (hd : 16 * p + d < 128) :
      t.mem.readW (State.addr (t.gpr .lr + BitVec.ofNat 32 d)) 32 =
        kw s₀.mem (s₀.gpr .r0) (4 * p + q) := by
    rw [k.mem, hl, h.lr, key_addr fit hd, h.keep.mem, kw]
    congr 3; omega
  have k₀ : Keep scanRegs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  simp only [keyBody, List.append_assoc]
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, r8₁, r10₁, keep₁⟩ := keyHead_ok s (kin k₀ rfl 0 (by omega))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have ks₁ := keep_scan keep₁ (by decide)
  have lr₁ : s₁.gpr .lr = s.gpr .lr := keep₁.reg .lr (by decide)
  rw [WP.block_append_iff]
  obtain ⟨s₂, run₂, r3₂, r11₂, keep₂⟩ := keyPair_ok s₁ 0 (by decide) (kin ks₁ lr₁ 4 (by omega))
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have ks₂ := ks₁.trans (keep_scan keep₂ (by decide))
  have lr₂ : s₂.gpr .lr = s.gpr .lr := (keep₂.reg .lr (by decide)).trans lr₁
  rw [r8₁, r10₁, keep₁.reg .r3 (by decide),
    h.r12, h.r9, bits.1, mul_bit, kword k₀ rfl 0 0 rfl (by omega)] at r3₂
  rw [r10₁, keep₁.reg .r11 (by decide),
    h.r12, h.r9, bits.1, mul_bit, kword ks₁ lr₁ (0 + 4) 1 rfl (by omega)] at r11₂
  rw [WP.block_append_iff]
  obtain ⟨s₃, run₃, r8₃, r10₃, keep₃⟩ := keyHead4_ok s₂ (kin ks₂ lr₂ 8 (by omega))
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have ks₃ := ks₂.trans (keep_scan keep₃ (by decide))
  have lr₃ : s₃.gpr .lr = s.gpr .lr := (keep₃.reg .lr (by decide)).trans lr₂
  have r12₂ : s₂.gpr .r12 = s.gpr .r12 := ks₂.reg .r12 (by decide)
  have r9₂ : s₂.gpr .r9 = s.gpr .r9 := (keep₂.reg .r9 (by decide)).trans (keep₁.reg .r9 (by decide))
  rw [WP.block_append_iff]
  obtain ⟨s₄, run₄, r3₄, r11₄, keep₄⟩ := keyPair_ok s₃ 8 (by decide) (kin ks₃ lr₃ 12 (by omega))
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have ks₄ := ks₃.trans (keep_scan keep₄ (by decide))
  have lr₄ : s₄.gpr .lr = s.gpr .lr := (keep₄.reg .lr (by decide)).trans lr₃
  rw [r8₃, r10₃, keep₃.reg .r3 (by decide), r12₂, r9₂, h.r12, h.r9, bits.2, mul_bit,
    kword ks₂ lr₂ 8 2 rfl (by omega), r3₂] at r3₄
  rw [r10₃, keep₃.reg .r11 (by decide), r12₂, r9₂, h.r12, h.r9, bits.2, mul_bit,
    kword ks₃ lr₃ (8 + 4) 3 rfl (by omega), r11₂] at r11₄
  obtain ⟨s₅, run₅, lr₅, r9₅, z₅, keep₅⟩ := keyNext_ok s₄
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have ks₅ := h.keep.trans (ks₄.trans (keep_scan keep₅ (by decide)))
  have r9₄ : s₄.gpr .r9 = BitVec.ofNat 32 (8 * (p + 1)) :=
    (keep₄.reg .r9 (by decide)).trans ((keep₃.reg .r9 (by decide)).trans (r9₂.trans h.r9))
  have r3₅ : s₅.gpr .r3 = kAcc s₀.mem (s₀.gpr .r0) x p 0 := by
    rw [keep₅.reg .r3 (by decide), r3₄, h.r3]
    exact kAcc_step _ _ 0 (by omega) (by omega)
  have r11₅ : s₅.gpr .r11 = kAcc s₀.mem (s₀.gpr .r0) x p 1 := by
    rw [keep₅.reg .r11 (by decide), r11₄, h.r11]
    exact kAcc_step _ _ 1 (by omega) (by omega)
  have r12₅ : s₅.gpr .r12 = BitVec.ofNat 32 (x + 8) :=
    (keep₅.reg .r12 (by decide)).trans ((ks₄.reg .r12 (by decide)).trans h.r12)
  refine ⟨fun hp0 => ⟨?_, ?_, r12₅, ks₅⟩, fun hp0 => ⟨r12₅, ?_, ?_, ?_, ?_, ks₅⟩, ?_⟩
  · rw [r3₅, hp0]
  · rw [r11₅, hp0]
  · rw [r9₅, r9₄, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl,
      BitVec.ofNat_sub_ofNat_of_le (8 * (p + 1)) 8 (by decide) (by omega)]
    congr 1; omega
  · rw [lr₅, lr₄, h.lr, show 16 * p = 16 * (p - 1) + 16 by omega, ← BitVec.ofNat_add_ofNat,
      ← BitVec.add_assoc]
    exact BitVec.add_sub_cancel _ _
  · rw [r3₅, Nat.sub_add_cancel hp0]
  · rw [r11₅, Nat.sub_add_cancel hp0]
  · rw [z₅, r9₄]
    by_cases hp0 : p = 0
    · subst hp0; rfl
    · rw [decide_eq_false hp0]
      have : BitVec.ofNat 32 (8 * (p + 1)) - 8 ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
        simp at this; omega
      simpa using this

/-- The selection: the word `2 (x / 4) + (x / 2) % 2` of the pair in `r3`
and `r11`, then its half `x % 2`, zero-extended, in `r12`. -/
theorem keySelect_ok (s : State) {x : Nat} (hx : x < 64) (h12 : s.gpr .r12 = BitVec.ofNat 32 (x + 8)) :
    ∃ s', runBlock isa keySelect s = some s' ∧
      s'.gpr .r12 = (((if x / 2 % 2 = 1 then s.gpr .r11 else s.gpr .r3) >>> (16 * (x % 2))).setWidth 16).setWidth 32 ∧
      Keep lookupRegs s s' := by
  refine ⟨_, by
    simp only [keySelect, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some,
      encodable_imm, Nat.reduceLeDiff, and_self, ite_true]
    rfl, ?_⟩
  have bits := indexBits x hx
  refine ⟨?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
    rw [h12, bits.1, bits.2, xor_select, maskBits16]
    refine congrArg (fun w : BitVec 32 => (w.setWidth 16).setWidth 32) ?_
    rw [xor_select']
    by_cases hb : x % 2 = 1
    · rw [ite_eq_left hb, hb, Nat.mul_one]
    · rw [ite_eq_right hb, show x % 2 = 0 by omega, Nat.mul_zero, BitVec.ushiftRight_zero]
  · constructor
    · intro r hr
      simp only [lookupRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h12', h3, _, _, h10, h11, _⟩ := hr
      simp only [gpr_setReg, h12', h3, h10, h11, ite_false]
    · rfl
    · rfl
    · rfl

theorem kw_entry (m : Mem) (K : BitVec 32) (x : Nat) :
    ((kw m K (x / 2) >>> (16 * (x % 2))).setWidth 16) =
      (m (State.addr K + BitVec.ofNat 64 (2 * x))).setWidth 16 |||
        (m (State.addr K + BitVec.ofNat 64 (2 * x + 1))).setWidth 16 <<< 8 := by
  rw [kw, ← extractHalf, ← Mem.readW_byte _ _ (i := 2 * (x % 2)) (by omega),
    ← Mem.readW_byte _ _ (i := 2 * (x % 2) + 1) (by omega),
    Offset.add_add, Offset.add_add, show 4 * (x / 2) + 2 * (x % 2) = 2 * x by omega,
    show 4 * (x / 2) + (2 * (x % 2) + 1) = 2 * x + 1 by omega]

/-- The lookup: `r12 := schedule[r12 & 63]`; only `lookupRegs` are written. -/
theorem keyLookup_ok (s : State) (fit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0)) 128) :
    WP isa keyLookup s (fun s' =>
      s'.gpr .r12 = ((Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))).getD
        ((s.gpr .r12).setWidth 6).toNat 0).setWidth 32 ∧
      Keep lookupRegs s s') := by
  obtain ⟨x, hx⟩ : ∃ x, ((s.gpr .r12).setWidth 6).toNat = x := ⟨_, rfl⟩
  have hx64 : x < 64 := hx ▸ ((s.gpr .r12).setWidth 6).isLt
  rw [hx]
  unfold keyLookup
  refine WP.seq (WP.mono (Q := fun s₁ => KeyScanAt s₁ x 7 s₁ ∧ Keep lookupRegs s s₁) ?_ fun s₁ ⟨h₁, k₁⟩ => ?_)
  · refine WP.of_runBlock ⟨_, by
      simp only [keyStart, imm, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval,
        Option.map_some, encodable_imm, ite_true]
      rfl, ?_⟩
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩, ?_⟩
    · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
      rw [← hx]
      apply BitVec.eq_of_toNat_eq
      have h63 : (s.gpr .r12).toNat &&& 63 = (s.gpr .r12).toNat % 2 ^ 6 :=
        Nat.and_two_pow_sub_one_eq_mod _ 6
      simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
        show (63 : BitVec 32).toNat = 63 from rfl, show (8 : BitVec 32).toNat = 8 from rfl, h63]
    · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]; rfl
    · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]; rfl
    · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
      simp [kAcc, show ¬8 ≤ x / 8 by omega]
    · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
      simp [kAcc, show ¬8 ≤ x / 8 by omega]
    · constructor
      · intro r hr
        simp only [lookupRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        obtain ⟨h12, h3, _, h9, _, h11, hl⟩ := hr
        simp only [gpr_setReg, h12, h3, h9, h11, hl, ite_false]
      · rfl
      · rfl
      · rfl
  have ptr₁ : s₁.gpr .r0 = s.gpr .r0 := k₁.reg .r0 (by decide)
  have fit₁ : (s₁.gpr .r0).toNat + 128 ≤ 2 ^ 32 := by rw [ptr₁]; exact fit
  have read₁ : InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r0)) 128 := by
    rw [k₁.rd, k₁.wr, ptr₁]; exact readable
  have loop : WP isa (.loop (.block keyBody) .ne) s₁ (fun v =>
      kAcc s₁.mem (s₁.gpr .r0) x 0 0 = v.gpr .r3 ∧ kAcc s₁.mem (s₁.gpr .r0) x 0 1 = v.gpr .r11 ∧
        v.gpr .r12 = BitVec.ofNat 32 (x + 8) ∧ Keep scanRegs s₁ v) := by
    refine WP.loop (M := isa) (fun n (v : State) => n < 8 ∧ KeyScanAt s₁ x n v) ?_ 7 s₁ ⟨by decide, h₁⟩
    rintro n v ⟨hn, hv⟩
    refine WP.mono (keyScan_step hx64 hn fit₁ read₁ hv) fun w ⟨hfin, hnext, wz⟩ => ?_
    by_cases he : n = 0
    · exact .inl ⟨by show some (!w.z) = _; rw [wz, decide_eq_true he]; rfl, hfin he⟩
    · exact .inr ⟨by show some (!w.z) = _; rw [wz, decide_eq_false he]; rfl, n - 1, by omega,
        by omega, hnext (by omega)⟩
  refine WP.seq (WP.mono loop fun v ⟨a0, a1, v12, kv⟩ => ?_)
  obtain ⟨s₃, run₃, out₃, keep₃⟩ := keySelect_ok v hx64 v12
  refine WP.of_runBlock ⟨s₃, run₃, ?_, ?_⟩
  · rw [out₃, ← a0, ← a1, k₁.mem, ptr₁, scheduleAt_getD _ _ _ hx64, ← kw_entry _ _ x]
    refine congrArg (fun w : BitVec 32 => ((w >>> (16 * (x % 2))).setWidth 16).setWidth 32) ?_
    simp only [kAcc, Nat.zero_le, ite_true]
    by_cases hb : x / 2 % 2 = 1
    · rw [ite_eq_left hb]; exact congrArg _ (by omega)
    · rw [ite_eq_right hb]; exact congrArg _ (by omega)
  · exact (k₁.trans (kv.weaken (by
      intro r hr; simp only [scanRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h | h | h | h | h <;> subst h <;> decide))).trans keep₃

end VG.Proof.Rc2.Arm
