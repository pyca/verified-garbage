module

public import VerifiedGarbage.Impl.Rc2.Arm.Lookup
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Spec.Rc2
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.Select32

/-! # Correctness of the baseline Arm RC2 key lookup

`keyLookup` visits the 32 words of the key schedule at `r0` as eight rows of
four words, and leaves the entry at the index in `r12` (`keyLookup_ok`).
Each row's words are multiplied by a bit that is 1 exactly when the index is
one of the row's eight entries (`rowBit`) and added to their columns'
registers, which then hold the words of the index's row (`keyRows_ok`); the
index's word of the four, and its half of that word, are then chosen by
bits of the index (`keySelect_ok`). The facts about a row's bit and a choice
by a bit are also those of key expansion's lookups in PITABLE
(`PiScan.lean`). -/

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
  have ha : 32 - n + i < 32 ↔ i < n := by omega_arith
  have hb : ¬32 - n + i < 32 - n := by omega_arith
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
  rw [BitVec.add_sub_comm, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_arith)]
  have := Nat.mod_le ((a - r.base).toNat + d) (2 ^ 64)
  omega_arith

/-- The registers a key lookup writes. -/
def lookupRegs : List Reg := [.r12, .r3, .r8, .r9, .r10, .r11, .lr]

/-- The registers the rows of a key lookup write. -/
def scanRegs : List Reg := [.r3, .r8, .r9, .r10, .r11, .lr]

/-- Word `q` of the key schedule at `K` in `m`: entries `2 q` and `2 q + 1`. -/
def kw (m : Mem) (K : BitVec 32) (q : Nat) : BitVec 32 :=
  m.readW (State.addr K + BitVec.ofNat 64 (4 * q)) 32

/-! ## A row's bit, and a choice by a bit -/

/-- The bit of row `r`, for an index `32 a + b`: 1 exactly when the index is
one of the row's eight entries. -/
theorem rowBit_split : ∀ r < 32, ∀ a < 8, ∀ b < 32,
    ((BitVec.ofNat 32 (32 * a + b) ^^^ BitVec.ofNat 32 (8 * r)) - 8) >>> 31 =
      (if (32 * a + b) / 8 = r then 1 else 0 : BitVec 32) := by decide

theorem rowBit {n r : Nat} (hn : n < 256) (hr : r < 32) :
    ((BitVec.ofNat 32 n ^^^ BitVec.ofNat 32 (8 * r)) - 8) >>> 31 = (if n / 8 = r then 1 else 0 : BitVec 32) := by
  have := rowBit_split r hr (n / 32) (by omega_arith) (n % 32) (Nat.mod_lt _ (by decide))
  rwa [Nat.div_add_mod] at this

/-- The low three bits of an index `32 a + b`, as the code takes them. -/
theorem idxBits_split : ∀ a < 8, ∀ b < 32,
    (BitVec.ofNat 32 (32 * a + b) <<< 29) >>> 31 = (if (32 * a + b) / 4 % 2 = 1 then 1 else 0 : BitVec 32) ∧
    (BitVec.ofNat 32 (32 * a + b) <<< 30) >>> 31 = (if (32 * a + b) / 2 % 2 = 1 then 1 else 0 : BitVec 32) ∧
    (BitVec.ofNat 32 (32 * a + b) &&& 1) = (if (32 * a + b) % 2 = 1 then 1 else 0 : BitVec 32) := by decide

theorem idxBits {n : Nat} (hn : n < 256) :
    (BitVec.ofNat 32 n <<< 29) >>> 31 = (if n / 4 % 2 = 1 then 1 else 0 : BitVec 32) ∧
    (BitVec.ofNat 32 n <<< 30) >>> 31 = (if n / 2 % 2 = 1 then 1 else 0 : BitVec 32) ∧
    (BitVec.ofNat 32 n &&& 1) = (if n % 2 = 1 then 1 else 0 : BitVec 32) := by
  have := idxBits_split (n / 32) (by omega_arith) (n % 32) (Nat.mod_lt _ (by decide))
  rwa [Nat.div_add_mod] at this

theorem mul_bit (w : BitVec 32) (c : Prop) [Decidable c] :
    w * (if c then 1 else 0 : BitVec 32) = if c then w else 0 := by
  split
  · exact BitVec.mul_one w
  · exact BitVec.mul_zero

/-- A choice between `a` and `b` by a bit. -/
theorem sub_select (a b : BitVec 32) (c : Prop) [Decidable c] :
    (b - a) * (if c then 1 else 0 : BitVec 32) + a = if c then b else a := by
  rw [mul_bit]
  split
  · exact BitVec.sub_add_cancel b a
  · exact BitVec.zero_add a

/-- A column's register after a row: the word `f q` of the index's row `q`,
once that row is passed. -/
theorem acc_step (f : Nat → BitVec 32) (q k : Nat) :
    f k * (if q = k then 1 else 0 : BitVec 32) + (if q < k then f q else 0) = if q < k + 1 then f q else 0 := by
  rw [mul_bit]
  rcases Nat.lt_trichotomy q k with h | h | h
  · rw [ite_eq_right (Nat.ne_of_lt h), ite_eq_left h, ite_eq_left (Nat.lt_succ_of_lt h)]
    exact BitVec.zero_add _
  · subst h
    rw [ite_eq_left rfl, ite_eq_right (Nat.lt_irrefl _), ite_eq_left (Nat.lt_succ_self _)]
    exact BitVec.add_zero _
  · rw [ite_eq_right (Nat.ne_of_gt h), ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]
    exact BitVec.add_zero _

/-- An immediate below 256 is encodable (rotation 0). -/
theorem encodable_small {v : BitVec 32} (h : v.toNat < 256) : encodable v = true :=
  List.any_eq_true.2 ⟨0, by simp, by
    have h0 : v.rotateLeft (2 * 0) = v := by ext i; simp
    simpa only [h0, decide_eq_true_eq] using h⟩

theorem encodable_row {r : Nat} (hr : r < 32) : encodable (BitVec.ofNat 32 (8 * r)) = true :=
  encodable_small (by rw [BitVec.toNat_ofNat]; omega_arith)

theorem flatMap_succ {α : Type} (f : Nat → List α) (n : Nat) :
    (List.range (n + 1)).flatMap f = (List.range n).flatMap f ++ f n := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

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
    omega_arith
  · simp only [hj, h, decide_true, Bool.true_and, decide_false, Bool.false_and,
      Bool.not_false, Bool.false_or, show j - 8 < 16 by omega_arith, show j - 8 < 8 by omega_arith]
    apply congrArg x.getLsbD
    omega_arith

theorem maskBits16 (x : BitVec 32) : x <<< 16 >>> 16 = (x.setWidth 16).setWidth 32 :=
  maskBits x 16 (by decide)

theorem encodable_imm : encodable (1 : BitVec 32) = true ∧ encodable (8 : BitVec 32) = true ∧
    encodable (63 : BitVec 32) = true := by decide

theorem key_addr {K : BitVec 32} (fit : K.toNat + 128 ≤ 2 ^ 32) {d : Nat} (hd : d < 128) :
    State.addr (K + BitVec.ofNat 32 d) = State.addr K + BitVec.ofNat 64 d :=
  addr_add (by omega_arith)

/-! ## The rows -/

/-- A row: each column's register gains the row's word of the column times
the row's bit. -/
theorem keyRow_ok (s : State) {x r : Nat} (hx : x < 64) (hr : r < 8)
    (h12 : s.gpr .r12 = BitVec.ofNat 32 x)
    (hin : ∀ d < 4, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 (16 * r + 4 * d))) 4) :
    ∃ s', runBlock isa (keyRow r) s = some s' ∧
      s'.gpr .r9 = s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 (16 * r))) 32 *
        (if x / 8 = r then 1 else 0 : BitVec 32) + s.gpr .r9 ∧
      s'.gpr .r10 = s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 (16 * r + 4))) 32 *
        (if x / 8 = r then 1 else 0 : BitVec 32) + s.gpr .r10 ∧
      s'.gpr .r11 = s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 (16 * r + 8))) 32 *
        (if x / 8 = r then 1 else 0 : BitVec 32) + s.gpr .r11 ∧
      s'.gpr .lr = s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 (16 * r + 12))) 32 *
        (if x / 8 = r then 1 else 0 : BitVec 32) + s.gpr .lr ∧
      Keep scanRegs s s' := by
  have er := encodable_row (r := r) (by omega_arith)
  have ho0 : 16 * r < 4096 := by omega_arith
  have ho1 : 16 * r + 4 < 4096 := by omega_arith
  have ho2 : 16 * r + 8 < 4096 := by omega_arith
  have ho3 : 16 * r + 12 < 4096 := by omega_arith
  have hin0 := hin 0 (by decide)
  have hin1 := hin 1 (by decide)
  have hin2 := hin 2 (by decide)
  have hin3 := hin 3 (by decide)
  rw [Nat.mul_zero, Nat.add_zero] at hin0
  have bit := rowBit (n := x) (r := r) (by omega_arith) (by omega_arith)
  refine ⟨_, by
    simp only [keyRow, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some, State.load32,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, reduceCtorEq, hin0, hin1, hin2, hin3, er, encodable_imm,
      ho0, ho1, ho2, ho3, Nat.reduceLeDiff, and_self, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
    rw [h12, bit]
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
    rw [h12, bit]
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
    rw [h12, bit]
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
    rw [h12, bit]
  · constructor
    · intro q hq
      simp only [scanRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      obtain ⟨h3, h8, h9, h10, h11, hl⟩ := hq
      simp only [gpr_setReg, h3, h8, h9, h10, h11, hl, ite_false]
    · rfl
    · rfl
    · rfl

/-- Column `c` once the rows before `k` are visited: word `4 (x / 8) + c`,
of the index's row, if that row is among them. -/
def kAcc (m : Mem) (K : BitVec 32) (x k c : Nat) : BitVec 32 :=
  if x / 8 < k then kw m K (4 * (x / 8) + c) else 0

/-- The state of the lookup from `s₀` with the rows before `k` visited. -/
structure KeyScanAt (s₀ : State) (x k : Nat) (s : State) : Prop where
  r12 : s.gpr .r12 = BitVec.ofNat 32 x
  r9 : s.gpr .r9 = kAcc s₀.mem (s₀.gpr .r0) x k 0
  r10 : s.gpr .r10 = kAcc s₀.mem (s₀.gpr .r0) x k 1
  r11 : s.gpr .r11 = kAcc s₀.mem (s₀.gpr .r0) x k 2
  lr : s.gpr .lr = kAcc s₀.mem (s₀.gpr .r0) x k 3
  keep : Keep scanRegs s₀ s

theorem kAcc_succ (m : Mem) (K : BitVec 32) (x k c : Nat) {a : Addr}
    (ha : a = State.addr K + BitVec.ofNat 64 (4 * (4 * k + c))) :
    m.readW a 32 * (if x / 8 = k then 1 else 0 : BitVec 32) + kAcc m K x k c = kAcc m K x (k + 1) c := by
  rw [ha]
  exact acc_step (fun r => kw m K (4 * r + c)) (x / 8) k

theorem keyRows_ok {s₀ : State} {x : Nat} (hx : x < 64) (fit : (s₀.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.gpr .r0)) 128) :
    ∀ k ≤ 8, ∀ s, KeyScanAt s₀ x 0 s →
      WP isa (.block ((List.range k).flatMap keyRow)) s (KeyScanAt s₀ x k) := by
  intro k hk
  induction k with
  | zero => intro s hs; exact WP.block_nil hs
  | succ k ih =>
    intro s hs
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_arith) s hs) fun t ht => ?_
    have t0 : t.gpr .r0 = s₀.gpr .r0 := ht.keep.reg .r0 (by decide)
    have ea : ∀ d < 4, State.addr (t.gpr .r0 + BitVec.ofNat 32 (16 * k + 4 * d)) =
        State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (4 * k + d)) := fun d hd => by
      rw [t0, key_addr fit (d := 16 * k + 4 * d) (by omega_arith),
        show 16 * k + 4 * d = 4 * (4 * k + d) by omega_arith]
    obtain ⟨u, run, u9, u10, u11, ul, uk⟩ := keyRow_ok t (r := k) hx (by omega_arith) ht.r12 fun d hd => by
      rw [ea d hd, ht.keep.rd, ht.keep.wr]
      exact key_in readable (by omega_arith)
    refine WP.of_runBlock ⟨u, run, ?_, ?_, ?_, ?_, ?_, ht.keep.trans uk⟩
    · rw [uk.reg .r12 (by decide), ht.r12]
    · rw [u9, ht.r9, ht.keep.mem]
      exact kAcc_succ _ _ x k 0 (ea 0 (by decide))
    · rw [u10, ht.r10, ht.keep.mem]
      exact kAcc_succ _ _ x k 1 (ea 1 (by decide))
    · rw [u11, ht.r11, ht.keep.mem]
      exact kAcc_succ _ _ x k 2 (ea 2 (by decide))
    · rw [ul, ht.lr, ht.keep.mem]
      exact kAcc_succ _ _ x k 3 (ea 3 (by decide))

/-! ## The choice -/

/-- The choice: the word `(x / 2) % 4` of the four in `r9`, `r10`, `r11` and
`lr`, then its half `x % 2`, zero-extended, in `r12`. -/
theorem keySelect_ok (s : State) {x : Nat} (hx : x < 64) (h12 : s.gpr .r12 = BitVec.ofNat 32 x) :
    ∃ s', runBlock isa keySelect s = some s' ∧
      s'.gpr .r12 = (((if x / 2 % 2 = 1 then (if x / 4 % 2 = 1 then s.gpr .lr else s.gpr .r10)
        else (if x / 4 % 2 = 1 then s.gpr .r11 else s.gpr .r9)) >>> (16 * (x % 2))).setWidth 16).setWidth 32 ∧
      Keep lookupRegs s s' := by
  obtain ⟨b2, b1, b0⟩ := idxBits (n := x) (by omega_arith)
  refine ⟨_, by
    simp only [keySelect, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some,
      encodable_imm, Nat.reduceLeDiff, and_self, ite_true]
    rfl, ?_⟩
  refine ⟨?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
    rw [h12, b2, b1, b0, sub_select, sub_select, sub_select, sub_select, maskBits16]
    refine congrArg (fun w : BitVec 32 => (w.setWidth 16).setWidth 32) ?_
    by_cases hb : x % 2 = 1
    · rw [ite_eq_left hb, hb, Nat.mul_one]
    · rw [ite_eq_right hb, show x % 2 = 0 by omega_arith, Nat.mul_zero, BitVec.ushiftRight_zero]
  · constructor
    · intro r hr
      simp only [lookupRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h12', h3, _, h9, h10, h11, hl⟩ := hr
      simp only [gpr_setReg, h12', h3, h9, h10, h11, hl, ite_false]
    · rfl
    · rfl
    · rfl

theorem kw_entry (m : Mem) (K : BitVec 32) (x : Nat) :
    ((kw m K (x / 2) >>> (16 * (x % 2))).setWidth 16) =
      (m (State.addr K + BitVec.ofNat 64 (2 * x))).setWidth 16 |||
        (m (State.addr K + BitVec.ofNat 64 (2 * x + 1))).setWidth 16 <<< 8 := by
  rw [kw, ← extractHalf, ← Mem.readW_byte _ _ (i := 2 * (x % 2)) (by omega_arith),
    ← Mem.readW_byte _ _ (i := 2 * (x % 2) + 1) (by omega_arith),
    Offset.add_add, Offset.add_add, show 4 * (x / 2) + 2 * (x % 2) = 2 * x by omega_arith,
    show 4 * (x / 2) + (2 * (x % 2) + 1) = 2 * x + 1 by omega_arith]

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
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (Q := fun s₁ => KeyScanAt s₁ x 0 s₁ ∧ Keep lookupRegs s s₁) (WP.of_runBlock ⟨_, by
      simp only [keyStart, imm, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval,
        Option.map_some, encodable_imm, ite_true]
      rfl, ?_⟩) fun s₁ ⟨h₁, k₁⟩ => ?_
  · have z : ∀ c, (BitVec.ofNat 16 0).setWidth 32 = kAcc s.mem (s.gpr .r0) x 0 c := fun c => by
      unfold kAcc; rw [ite_eq_right (Nat.not_lt_zero _)]; rfl
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩, ?_⟩
    · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
      rw [← hx]
      apply BitVec.eq_of_toNat_eq
      have h63 : (s.gpr .r12).toNat &&& 63 = (s.gpr .r12).toNat % 2 ^ 6 :=
        Nat.and_two_pow_sub_one_eq_mod _ 6
      simp only [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
        show (63 : BitVec 32).toNat = 63 from rfl, h63]
      omega_arith
    · simp only [gpr_setReg, mem_setReg, reduceCtorEq, ite_false, ite_true]; exact z 0
    · simp only [gpr_setReg, mem_setReg, reduceCtorEq, ite_false, ite_true]; exact z 1
    · simp only [gpr_setReg, mem_setReg, reduceCtorEq, ite_false, ite_true]; exact z 2
    · simp only [gpr_setReg, mem_setReg, reduceCtorEq, ite_false, ite_true]; exact z 3
    · constructor
      · intro r hr
        simp only [lookupRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        obtain ⟨h12, _, _, h9, h10, h11, hl⟩ := hr
        simp only [gpr_setReg, h12, h9, h10, h11, hl, ite_false]
      · rfl
      · rfl
      · rfl
  have ptr₁ : s₁.gpr .r0 = s.gpr .r0 := k₁.reg .r0 (by decide)
  have fit₁ : (s₁.gpr .r0).toNat + 128 ≤ 2 ^ 32 := by rw [ptr₁]; exact fit
  have read₁ : InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r0)) 128 := by
    rw [k₁.rd, k₁.wr, ptr₁]; exact readable
  rw [WP.block_append_iff]
  refine WP.mono (keyRows_ok hx64 fit₁ read₁ 8 (Nat.le_refl _) s₁ h₁) fun v hv => ?_
  obtain ⟨s₃, run₃, out₃, keep₃⟩ := keySelect_ok v hx64 hv.r12
  refine WP.of_runBlock ⟨s₃, run₃, ?_, ?_⟩
  · rw [out₃, hv.r9, hv.r10, hv.r11, hv.lr, k₁.mem, ptr₁, scheduleAt_getD _ _ _ hx64, ← kw_entry _ _ x]
    refine congrArg (fun w : BitVec 32 => ((w >>> (16 * (x % 2))).setWidth 16).setWidth 32) ?_
    have hq : x / 8 < 8 := by omega_arith
    simp only [kAcc, hq, ite_true]
    by_cases hb : x / 2 % 2 = 1 <;> by_cases hc : x / 4 % 2 = 1
    · rw [ite_eq_left hb, ite_eq_left hc]; exact congrArg _ (by omega_arith)
    · rw [ite_eq_left hb, ite_eq_right hc]; exact congrArg _ (by omega_arith)
    · rw [ite_eq_right hb, ite_eq_left hc]; exact congrArg _ (by omega_arith)
    · rw [ite_eq_right hb, ite_eq_right hc]; exact congrArg _ (by omega_arith)
  · exact (k₁.trans (hv.keep.weaken (by
      intro r hr; simp only [scanRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h | h | h | h | h <;> subst h <;> decide))).trans keep₃

end VG.Proof.Rc2.Arm
