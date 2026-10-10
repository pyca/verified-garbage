import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop

/-!
# Short Weierstrass curves on AArch64: tables of bits, and masks of bits

`bits src dst (8 n)` writes the bits of the `n`-word number at `src`, one byte
each, to the table at `dst` (`bits_ok`): a loop over its bytes, from the top
one down, each giving eight bytes of the table (`bitsBody_ok`). `bitMask d`
makes the mask `x3` of the byte `x19` of the table at `d` (`bitMask_ok`): all
ones for a 1, zero for a 0 (`bitMask_bool_ok`).
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-! ## Masks -/

/-- A byte loaded by `ldrb`, as a word: zero-extended. -/
theorem read1_zext (m : Mem) (a : Addr) :
    ((m.read a 1).setWidth 32).setWidth 64 = (m a).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Mem.read, BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  by_cases h : i < 8
  · simp [h, show i < 32 by omega_arith]
  · simp [h, BitVec.getLsbD_of_ge (m a) i (by omega_arith)]

/-- A byte at `x0 + x19 + d`, through `x16`, zero-extended into `t`. -/
theorem ldrbTbl_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d k : Nat}
    (hk : s.gpr .x19 = BitVec.ofNat 64 k) (hd : d + k + 1 ≤ size) (hd' : d < 4096) (t : Reg) :
    WP isa (.block [.add .x .x16 .x0 .x19, .ldrb t .x16 d]) s fun s' =>
      s'.gpr t = (s.mem (off base (d + k))).setWidth 64 ∧ Keeps [.x16, t] s s' ∧ s'.c = s.c := by
  have ha : s.gpr .x0 + s.gpr .x19 + BitVec.ofNat 64 d = off base (d + k) := by
    rw [hs.x0, hk, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm]
  have hr : InRegions (s.rd ++ s.wr) (off base (d + k)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, hs.contains (d := d + k) (n := 1) hd (by decide)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, RegUpd.gpr_write,
    BitVec.setWidth_eq, ite_true, Nat.mod_one, show d < 4096 * 1 by omega_arith, and_self, Option.bind_some,
    State.load, RegUpd.rd_write, RegUpd.wr_write, ha, hr, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨read1_zext _ _, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- `x3 = -[x0 + x19 + d]`, the byte zero-extended. -/
theorem bitMask_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d t : Nat}
    (ht : s.gpr .x19 = BitVec.ofNat 64 t) (hd : d + t + 1 ≤ size) (hd' : d < 4096) :
    WP isa (.block (bitMask d)) s fun s' =>
      s'.gpr .x3 = 0 - (s.mem (off base (d + t))).setWidth 64 ∧ Keeps [.x1, .x3, .x7, .x16] s s' := by
  rw [bitMask, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movz0_ok s .x7) fun s₁ ⟨z₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [show ([.add .x .x16 .x0 .x19, .ldrb .x1 .x16 d, .sub .x .x3 .x7 .x1] : List Instr) =
    [.add .x .x16 .x0 .x19, .ldrb .x1 .x16 d] ++ [.sub .x .x3 .x7 .x1] from rfl, WP.block_append_iff]
  refine WP.mono (ldrbTbl_ok hs₁ (k := t) (by rw [k₁.gpr _ (by decide), ht]) hd hd' .x1)
    fun s₂ ⟨b₂, k₂, _⟩ => ?_
  have hz₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr _ (by decide), z₁]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left', hz₂, b₂, k₁.mem]
  refine ⟨trivial, fun r hr => ?_, (RegUpd.mem_write _ _ _ _).trans (k₂.mem.trans k₁.mem),
    (RegUpd.rd_write _ _ _ _).trans (k₂.rd.trans k₁.rd), (RegUpd.wr_write _ _ _ _).trans (k₂.wr.trans k₁.wr),
    (RegUpd.sp_write _ _ _ _).trans (k₂.sp.trans k₁.sp)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [RegUpd.gpr_write_of_ne _ _ _ hr.2.1, k₂.gpr r (by simp [hr.1, hr.2.2.2]),
    k₁.gpr r (by simpa using hr.2.2.1)]

theorem neg_bit (c : Bool) :
    0 - ((if c then 1 else 0 : BitVec 8)).setWidth 64 = (if c then BitVec.allOnes 64 else 0) := by
  cases c <;> decide

/-- The mask of a byte that is 0 or 1. -/
theorem bitMask_bool_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d t : Nat}
    (ht : s.gpr .x19 = BitVec.ofNat 64 t) (hd : d + t + 1 ≤ size) (hd' : d < 4096) {c : Bool}
    (hc : s.mem (off base (d + t)) = if c then 1 else 0) :
    WP isa (.block (bitMask d)) s fun s' =>
      s'.gpr .x3 = (if c then BitVec.allOnes 64 else 0) ∧ Keeps [.x1, .x3, .x7, .x16] s s' :=
  WP.mono (bitMask_ok hs ht hd hd') fun _ ⟨e, k⟩ => ⟨by rw [e, hc, neg_bit], k⟩

/-! ## The table of bits -/

/-- The body of `bits`' loop. -/
def bitsBody (src dst : Nat) : List Instr :=
  [decCounter, .add .x .x16 .x0 .x19, .ldrb .x1 .x16 src, .lsl .x .x17 .x19 3, .add .x .x17 .x0 .x17] ++
    (List.range 8).flatMap (bitJ dst)

theorem bits_eq (src dst nbytes : Nat) :
    bits src dst nbytes = .seq (.block [.movz .x .x19 (BitVec.ofNat 16 nbytes) 0, .movz .x .x5 1 0])
      (.loop (.block (bitsBody src dst)) (.nonzero .x .x19)) :=
  rfl

theorem bit_byte : ∀ b : BitVec 8, ∀ j < 8,
    (((((b.setWidth 64 >>> j) &&& 1).setWidth 32).setWidth 8) : BitVec 8) =
      if b.getLsbD j then 1 else 0 := by decide +kernel

theorem bit_byte0 : ∀ b : BitVec 8,
    ((((b.setWidth 64 &&& 1).setWidth 32).setWidth 8) : BitVec 8) =
      if b.getLsbD 0 then 1 else 0 := by decide +kernel

/-- Byte `j` of the eight at `x17 + dst`: bit `j` of the byte in `x1`. -/
theorem bitJ_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {i : Nat}
    (h17 : s.gpr .x17 = off base (8 * i)) {b : BitVec 8} (ha : s.gpr .x1 = b.setWidth 64)
    (h5 : s.gpr .x5 = 1) {dst j : Nat} (hj : j < 8) (hd : dst + (8 * i + j) + 1 ≤ size)
    (hdj : dst + j < 4096) :
    WP isa (.block (bitJ dst j)) s fun s' => KeepRegs [.x2] s s' ∧
      s'.mem = s.mem.writeW (off base (dst + (8 * i + j))) (if b.getLsbD j then 1 else 0 : BitVec 8) := by
  have hadr : s.gpr .x17 + BitVec.ofNat 64 (dst + j) = off base (dst + (8 * i + j)) := by
    rw [h17, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact congrArg (fun k => base + BitVec.ofNat 64 k) (by omega_arith)
  have w : InRegions s.wr (off base (dst + (8 * i + j))) 1 :=
    ⟨_, hs.wr, hs.contains (n := 1) hd (by decide)⟩
  apply WP.of_runBlock
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [bitJ, ite_true, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
      runBlock_nil, exec, addr, Nat.mod_one, show dst + 0 < 4096 * 1 by omega_arith, and_self,
      ite_true, Option.bind_some, State.store, RegUpd.gpr_write, RegUpd.wr_write, BitVec.setWidth_eq,
      reduceCtorEq, ite_false, hadr, w, Option.some.injEq, exists_eq_left', ha, h5, bit_byte0,
      State.read]
    refine ⟨⟨fun r hr => ?_, rfl, rfl, rfl⟩, ?_⟩
    · simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_write, hr, ite_false]
    · rw [Mem.writeW]; rfl
  · simp only [bitJ, show ¬j = 0 by omega_arith, ite_false, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, Nat.mod_one,
      show dst + j < 4096 * 1 by omega_arith, and_self, ite_true, Option.bind_some, State.store,
      RegUpd.gpr_write, RegUpd.wr_write, BitVec.setWidth_eq, reduceCtorEq, hadr, w,
      show j < Size.x.bits by dsimp only [Size.bits]; omega_arith,
      Option.some.injEq, exists_eq_left', ha, h5, State.read]
    refine ⟨⟨fun r hr => ?_, rfl, rfl, rfl⟩, ?_⟩
    · simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_write, hr, ite_false]
    · rw [Mem.writeW, ← bit_byte b j hj]; rfl

/-- The first `k` bits of the byte in `x1`. -/
theorem bitJs_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {i : Nat}
    (h17 : s.gpr .x17 = off base (8 * i)) {b : BitVec 8} (ha : s.gpr .x1 = b.setWidth 64)
    (h5 : s.gpr .x5 = 1) {dst : Nat} (hd : dst + 8 * i + 8 ≤ size) (hd' : dst + 8 ≤ 4096) : ∀ k ≤ 8,
    WP isa (.block ((List.range k).flatMap (bitJ dst))) s fun s' => KeepRegs [.x2] s s' ∧
      (∀ j < k, s'.mem (off base (dst + (8 * i + j))) = if b.getLsbD j then 1 else 0) ∧
      Outside base (dst + 8 * i) k s.mem s'.mem
  | 0, _ => WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl, rfl⟩, fun _ h => absurd h (Nat.not_lt_zero _),
      Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (bitJs_ok hs h17 ha h5 hd hd' k (by omega_arith)) fun s₁ ⟨k₁, e₁, O₁⟩ => ?_
    refine WP.mono (bitJ_ok (hs.of_keepRegs k₁ (by decide)) (i := i) (by rw [k₁.gpr _ (by decide), h17])
      (b := b) (by rw [k₁.gpr _ (by decide), ha]) (by rw [k₁.gpr _ (by decide), h5]) (dst := dst)
      (j := k) (by omega_arith) (by omega_arith) (by omega_arith)) fun s₂ ⟨k₂, m₂⟩ => ?_
    have O₂ : Outside base (dst + (8 * i + k)) 1 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW8_outside _ _ _ (by omega_arith)
    refine ⟨k₁.trans k₂, fun j hj => ?_,
      (O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂ _ (by rw [ofs_off0 base (d := dst + (8 * i + j)) (by omega_arith)]; omega_arith), e₁ j h]
    · obtain rfl : j = k := by omega_arith
      rw [m₂, writeW8_self]

/-- `r = 1`. -/
theorem movz1_ok (s : State) (r : Reg) :
    WP isa (.block [.movz .x r 1 0]) s fun s' => s'.gpr r = 1 ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide,
    ite_true, RegUpd.gpr_write_self, Option.some.injEq, exists_eq_left']
  refine ⟨by decide, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hq
  exact RegUpd.gpr_write_of_ne _ _ _ hq

/-- `x17 = x0 + 8 x19`. -/
theorem rowAddr_ok (s : State) {base : Addr} {k : Nat} (h0 : s.gpr .x0 = base)
    (hk : s.gpr .x19 = BitVec.ofNat 64 k) :
    WP isa (.block [.lsl .x .x17 .x19 3, .add .x .x17 .x0 .x17]) s fun s' =>
      s'.gpr .x17 = off base (8 * k) ∧ Keeps [.x17] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 3 < Size.x.bits by decide, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq, reduceCtorEq,
    ite_false, Option.some.injEq, exists_eq_left', h0, hk]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · rw [BitVec.shiftLeft_eq_mul_twoPow, show (BitVec.twoPow 64 3 : BitVec 64) = BitVec.ofNat 64 8 by decide,
      ← BitVec.ofNat_mul, Nat.mul_comm]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

/-- One byte of the number at `src`, the one below `x19 = i + 1`: its bits to
the table at `dst`, with `x5 = 1`. -/
theorem bitsBody_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {src dst i : Nat}
    (ht : s.gpr .x19 = BitVec.ofNat 64 (i + 1)) (hi : i + 1 < 2 ^ 64) (h5 : s.gpr .x5 = 1)
    (hsrc : src + i + 1 ≤ size) (hsrc' : src < 4096) (hd : dst + 8 * i + 8 ≤ size)
    (hd' : dst + 8 ≤ 4096) :
    WP isa (.block (bitsBody src dst)) s fun s' =>
      s'.gpr .x19 = BitVec.ofNat 64 i ∧ KeepRegs [.x1, .x2, .x16, .x17, .x19] s s' ∧
      (∀ j < 8, s'.mem (off base (dst + (8 * i + j))) =
        if (s.mem (off base (src + i))).getLsbD j then 1 else 0) ∧
      Outside base (dst + 8 * i) 8 s.mem s'.mem := by
  rw [bitsBody, List.cons_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (decCounter_ok s (j := i + 1) (by omega_arith) hi ht) fun s₁ ⟨c₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [Nat.add_sub_cancel] at c₁
  rw [show ([.add .x .x16 .x0 .x19, .ldrb .x1 .x16 src, .lsl .x .x17 .x19 3, .add .x .x17 .x0 .x17] ++
      (List.range 8).flatMap (bitJ dst) : List Instr) = [.add .x .x16 .x0 .x19, .ldrb .x1 .x16 src] ++
      ([.lsl .x .x17 .x19 3, .add .x .x17 .x0 .x17] ++ (List.range 8).flatMap (bitJ dst)) from rfl,
    WP.block_append_iff]
  refine WP.mono (ldrbTbl_ok hs₁ c₁ (d := src) (by omega_arith) hsrc' .x1) fun s₂ ⟨a₂, k₂, _⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (rowAddr_ok s₂ hs₂.x0 (k := i) (by rw [k₂.gpr _ (by decide), c₁])) fun s₃ ⟨r₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (bitJs_ok hs₃ r₃ (b := s.mem (off base (src + i)))
    (by rw [k₃.gpr _ (by decide), a₂, k₁.mem]) (by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide),
      k₁.gpr _ (by decide), h5]) hd hd' 8 (Nat.le_refl _)) fun s₄ ⟨k₄, e₄, O₄⟩ => ?_
  refine ⟨by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), c₁],
    ((((Keeps.regs k₁).mono (by simp)).trans ((Keeps.regs k₂).mono (by simp))).trans
      ((Keeps.regs k₃).mono (by simp))).trans (k₄.mono (by simp)), e₄, ?_⟩
  rw [k₃.mem, k₂.mem, k₁.mem] at O₄; exact O₄

/-- `bits`' loop invariant, at `x19 = i`: the bytes from `i` up are done. -/
structure BInv (base : Addr) (size src dst n : Nat) (s₀ s : State) (i : Nat) : Prop where
  scr : Scr s base size
  x5 : s.gpr .x5 = 1
  x19 : s.gpr .x19 = BitVec.ofNat 64 i
  keep : KeepRegs [.x1, .x2, .x5, .x16, .x17, .x19] s₀ s
  mem : Outside base dst (64 * n) s₀.mem s.mem
  bits : ∀ t, 8 * i ≤ t → t < 64 * n → s.mem (off base (dst + t)) =
    if (s₀.mem (off base (src + t / 8))).getLsbD (t % 8) then 1 else 0

/-- `bits src dst (8 n)`: byte `t` of the table at `dst` is bit `t` of the
`n`-word number at `src`. -/
theorem bits_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n src dst : Nat}
    (hn0 : 0 < n) (hn : n < 2 ^ 12) (hsrc : src + 8 * n ≤ size) (hdst : dst + 64 * n ≤ size)
    (hsrc' : src < 4096) (hdst' : dst + 8 ≤ 4096)
    (hsep : src + 8 * n ≤ dst ∨ dst + 64 * n ≤ src) :
    WP isa (bits src dst (8 * n)) s fun s' =>
      (∀ t < 64 * n, s'.mem (off base (dst + t)) =
        if (wordsVal s.mem base src n).testBit t then 1 else 0) ∧
      KeepRegs [.x1, .x2, .x5, .x16, .x17, .x19] s s' ∧ Outside base dst (64 * n) s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [bits_eq]
  refine WP.seq (WP.mono (show WP isa (.block [.movz .x .x19 (BitVec.ofNat 16 (8 * n)) 0,
      .movz .x .x5 1 0]) s (fun s' => BInv base size src dst n s s' (8 * n)) by
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (setCounter_ok s (j := 8 * n) (by omega_arith)) fun s₁ ⟨c₁, k₁⟩ => ?_
    refine WP.mono (movz1_ok s₁ .x5) fun s₂ ⟨o₂, k₂⟩ => ?_
    have k₁₂ : KeepRegs [.x1, .x2, .x5, .x16, .x17, .x19] s s₂ :=
      ((Keeps.regs k₁).mono (by simp)).trans ((Keeps.regs k₂).mono (by simp))
    refine ⟨hs.of_keepRegs k₁₂ (by decide), o₂, by rw [k₂.gpr _ (by decide), c₁], k₁₂,
      by rw [k₂.mem, k₁.mem]; exact Outside.refl _ _ _ _, fun t ht ht' => absurd ht' (by omega_arith)⟩)
    fun s₁ h₁ => ?_)
  refine countLoop_ok (Inv := fun j s' => BInv base size src dst n s s' j) (n := 8 * n) (by omega_arith)
    (fun j s' h1 h2 hb => ?_) (fun s' hb => ⟨fun t ht => ?_, hb.keep, hb.mem⟩) (by omega_arith) h₁
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega_arith⟩
    refine WP.mono (bitsBody_ok hb.scr hb.x19 (by omega_arith) hb.x5 (by omega_arith) hsrc' (by omega_arith) (by omega_arith))
      fun s'' ⟨b', k', bits', O'⟩ => ?_
    have hbyte : s'.mem (off base (src + i)) = s.mem (off base (src + i)) :=
      hb.mem _ (by rw [ofs_off0 base (d := src + i) (by omega_arith)]; omega_arith)
    refine ⟨⟨hb.scr.of_keepRegs k' (by decide), by rw [k'.gpr _ (by decide), hb.x5], b',
      hb.keep.trans (k'.mono (by simp)), hb.mem.trans (O'.mono (by omega_arith) (by omega_arith)),
      fun t ht ht' => ?_⟩, by rw [b']; rfl⟩
    rcases Nat.lt_or_ge t (8 * (i + 1)) with h | h
    · have e := bits' (t - 8 * i) (by omega_arith)
      rw [show 8 * i + (t - 8 * i) = t by omega_arith, hbyte] at e
      rw [e, show t / 8 = i by omega_arith, show t % 8 = t - 8 * i by omega_arith]
    · rw [O' _ (by rw [ofs_off0 base (d := dst + t) (by omega_arith)]; omega_arith), hb.bits t h ht']
  · rw [hb.bits t (by omega_arith) ht, show t = 8 * (t / 8) + t % 8 from (Nat.div_add_mod t 8).symm,
      testBit_byte s.mem base (a := src) (n := n) (by omega_arith) (Nat.mod_lt _ (by decide))]
    simp only [show (8 * (t / 8) + t % 8) / 8 = t / 8 by omega_arith, show (8 * (t / 8) + t % 8) % 8 = t % 8 by omega_arith]

end VG.Proof.Weierstrass.AArch64
