module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Blake2.Spec
public import VerifiedGarbage.Impl.Blake2.RISCV64
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd

/-!
# BLAKE2 compression function on RISC-V: the rounds

The structure of the PPC64LE proof (`VG.Proof.Blake2.PPC64LE`), written once
for both word sizes, over the operand size `z` (`.d` for BLAKE2b, `.w` for
BLAKE2s, words of `z.bits` bits). The registers are 64 bits and `add` and
`xor` act on all of them, so a word of the work vector is the low `z.bits`
bits of its register (`Vars`): the rotations (`rot_ok`) and the stores of
words read only those. Each `G` is three kinds of pieces (`addx_ok`, `rot_ok`,
`cx_ok`), each symbolically executed once, for any registers; the message
words are read from the copy of the block in the scratch space (`Msg`).
-/

@[expose] public section

namespace VG.Proof.Blake2.RISCV64

open VG VG.RISCV64
open VG.Impl.Blake2.RISCV64 (sz wd ws wreg T RT SB mOff)
open VG.Spec.Blake2 (Params Work Block)

/-! ## Words of `z.bits` bits -/

/-- The width of the loads and stores of words. -/
abbrev zW : Size → Width
  | .w => .w
  | .d => .d

/-- The size of a word in bytes. -/
abbrev zB (z : Size) : Nat := (zW z).bytes

theorem sz_bits (z : Size) : sz z.bits = z := by cases z <;> rfl

theorem wd_bits (z : Size) : wd z.bits = zW z := by cases z <;> rfl

theorem ws_bits (z : Size) : ws z.bits = zB z := by cases z <;> rfl

theorem bits_div (z : Size) : z.bits / 8 = zB z := by cases z <;> rfl

theorem bits_le (z : Size) : z.bits ≤ 64 := by cases z <;> decide

theorem zB_le (z : Size) : zB z ≤ 8 := by cases z <;> decide

theorem zB_pos (z : Size) : 0 < zB z := by cases z <;> decide

theorem ext_trunc (z : Size) (v : BitVec z.bits) : (v.setWidth 64).setWidth z.bits = v := by
  cases z
  · rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  · simp only [Size.bits, BitVec.setWidth_eq]

theorem trunc_ofNat (z : Size) (n : Nat) : (BitVec.ofNat 64 n).setWidth z.bits = BitVec.ofNat z.bits n := by
  cases z
  · simp only [Size.bits]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_mod_of_dvd _ (by decide)]
  · exact BitVec.setWidth_eq _

theorem lo_add (z : Size) (x y : BitVec 64) :
    (x + y).setWidth z.bits = x.setWidth z.bits + y.setWidth z.bits :=
  BitVec.setWidth_add x y (bits_le z)

theorem lo_xor (z : Size) (x y : BitVec 64) :
    (x ^^^ y).setWidth z.bits = x.setWidth z.bits ^^^ y.setWidth z.bits := by
  ext i hi; simp

/-- An offset `d` of an address that is a multiple of 8 is aligned for words
if `d` is. -/
theorem al (z : Size) {p : Addr} (hp : p.toNat % 8 = 0) {d : Nat} (hd : d % zB z = 0) :
    (p + BitVec.ofNat 64 d).toNat % zB z = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := p.isLt
  cases z <;> simp only [zB, Width.bytes] at hd ⊢ <;> omega

theorem exec_ld {z : Size} {s : State} {t n : Reg} {off : Nat} (ho : off < 2048)
    (ha : (s.gpr n + BitVec.ofNat 64 off).toNat % zB z = 0)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) (zB z)) :
    exec (.load (wd z.bits) t n off) s =
      some (s.write t ((s.mem.readW (s.gpr n + BitVec.ofNat 64 off) z.bits).setWidth 64)) := by
  rw [wd_bits]
  cases z
  · exact exec_load_w ho ha h
  · rw [exec_load_d ho ha h, BitVec.setWidth_eq]

theorem exec_st {z : Size} {s : State} {t n : Reg} {off : Nat} (ho : off < 2048)
    (ha : (s.gpr n + BitVec.ofNat 64 off).toNat % zB z = 0)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) (zB z)) :
    exec (.store (wd z.bits) t n off) s =
      some { s with mem := s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) ((s.gpr t).setWidth z.bits) } := by
  rw [wd_bits]
  cases z
  · exact exec_store_w ho ha h
  · rw [exec_store_d ho ha h, BitVec.setWidth_eq]

theorem readW_writeW_self (z : Size) (m : Mem) (a : Addr) (v : BitVec z.bits) :
    (m.writeW a v).readW a z.bits = v := by
  cases z
  · exact Mem.readW_writeW_self32 m a v
  · exact Mem.readW_writeW_self64 m a v

/-! ## The pieces of `G` -/

section G
variable {z : Size} (P : Params z.bits)

/-- The rotations of `P` are encodable at the word size, and not zero. -/
def ROk : Prop :=
  0 < P.R1 ∧ P.R1 < z.bits ∧ 0 < P.R2 ∧ P.R2 < z.bits ∧ 0 < P.R3 ∧ P.R3 < z.bits ∧
    0 < P.R4 ∧ P.R4 < z.bits

/-- What a piece of `G` leaves: the other registers, the memory and the
regions. -/
def Keeps (s s' : State) (a b : Reg) : Prop :=
  (∀ q, q ≠ a → q ≠ b → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem rot_ok {d : Reg} (hd : d ≠ RT) {r : Nat} (h0 : 0 < r) (hr : r < z.bits) (s : State) :
    WP isa (.block (Impl.Blake2.RISCV64.rot (w := z.bits) d r)) s fun s' =>
      (s'.gpr d).setWidth z.bits = ((s.gpr d).setWidth z.bits).rotateRight r ∧ Keeps s s' d RT := by
  apply WP.of_runBlock
  cases z
  · simp only [Impl.Blake2.RISCV64.rot, sz, Size.bits, show (32 : Nat) ≠ 64 by decide, ite_false,
      runBlock_cons, runStep_some, runBlock_nil, exec_shift_w hr,
      exec_shift_w (show 32 - r < 32 by omega), exec_logic, RegUpd.gpr_write, hd, Ne.symm hd,
      ite_true, ite_false, Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun q h1 h2 => by simp only [RegUpd.gpr_write, h1, h2, ite_false], rfl, rfl, rfl⟩
    rw [lo32_or, lo32_sext, lo32_sext, BitVec.rotateRight_def, Nat.mod_eq_of_lt hr, BitVec.or_comm]
  · simp only [Impl.Blake2.RISCV64.rot, sz, Size.bits, ite_true,
      runBlock_cons, runStep_some, runBlock_nil, exec_shift_d hr,
      exec_shift_d (show 64 - r < 64 by omega), exec_logic, RegUpd.gpr_write, hd, Ne.symm hd,
      ite_true, ite_false, Option.some.injEq, exists_eq_left', BitVec.setWidth_eq]
    refine ⟨?_, fun q h1 h2 => by simp only [RegUpd.gpr_write, h1, h2, ite_false], rfl, rfl, rfl⟩
    rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt hr, BitVec.or_comm]

/-- `a := a + b + x; d := d ^ a`, with `x` the word at `off` of the scratch space. -/
theorem addx_ok {a b d : Reg} (had : a ≠ d) (haT : a ≠ T) (hbT : b ≠ T)
    (hdT : d ≠ T) {off : Nat} (ho : off < 2048) (s : State) (va vb vd x : BitVec z.bits)
    (ha : (s.gpr a).setWidth z.bits = va) (hb : (s.gpr b).setWidth z.bits = vb)
    (hd : (s.gpr d).setWidth z.bits = vd)
    (hal : (s.gpr SB + BitVec.ofNat 64 off).toNat % zB z = 0)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr SB + BitVec.ofNat 64 off) (zB z))
    (hx : s.mem.readW (s.gpr SB + BitVec.ofNat 64 off) z.bits = x) :
    WP isa (.block [.load (wd z.bits) T SB off, .add a a b, .add a a T, .logic .xor d d a]) s
      fun s' => (s'.gpr a).setWidth z.bits = va + vb + x ∧
        (s'.gpr d).setWidth z.bits = vd ^^^ (va + vb + x) ∧
        (∀ q, q ≠ a → q ≠ d → q ≠ T → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_ld ho hal hin, exec_add, exec_logic,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, had, Ne.symm had,
    haT, Ne.symm haT, hdT, hbT, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, fun q h1 h2 h3 => by simp only [h1, h2, h3, ite_false], trivial, trivial,
    trivial⟩
  · rw [lo_add, lo_add, ha, hb, ext_trunc, hx]
  · rw [lo_xor, lo_add, lo_add, ha, hb, hd, ext_trunc, hx]

/-- `c := c + d; b := b ^ c`. -/
theorem cx_ok {b c d : Reg} (hbc : b ≠ c) (s : State) (vb vc vd : BitVec z.bits)
    (hb : (s.gpr b).setWidth z.bits = vb) (hc : (s.gpr c).setWidth z.bits = vc)
    (hd : (s.gpr d).setWidth z.bits = vd) :
    WP isa (.block [.add c c d, .logic .xor b b c]) s fun s' =>
      (s'.gpr c).setWidth z.bits = vc + vd ∧ (s'.gpr b).setWidth z.bits = vb ^^^ (vc + vd) ∧
      Keeps s s' b c := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_logic,
    RegUpd.gpr_write, hbc, Ne.symm hbc, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ?_, fun q h1 h2 => by simp only [RegUpd.gpr_write, h1, h2, ite_false], rfl, rfl,
    rfl⟩
  · rw [lo_add, hc, hd]
  · rw [lo_xor, lo_add, hb, hc, hd]

/-- `G` on the registers `a, b, c, d` (all different, and different from `T`,
`RT` and `SB`), with the message words at `mOff + ws · j` and `mOff + ws · k`
of the scratch space at `p`. -/
theorem g_ok (hR : ROk P) {a b c d : Reg} (hs : [a, b, c, d, T, RT, SB].Nodup) {j k : Nat}
    (hoj : mOff + ws z.bits * j < 2048) (hok : mOff + ws z.bits * k < 2048)
    (s : State) (va vb vc vd x y : BitVec z.bits) (p : Addr)
    (ha : (s.gpr a).setWidth z.bits = va) (hb : (s.gpr b).setWidth z.bits = vb)
    (hc : (s.gpr c).setWidth z.bits = vc) (hd : (s.gpr d).setWidth z.bits = vd)
    (hp : s.gpr SB = p)
    (halj : (p + BitVec.ofNat 64 (mOff + ws z.bits * j)).toNat % zB z = 0)
    (halk : (p + BitVec.ofNat 64 (mOff + ws z.bits * k)).toNat % zB z = 0)
    (hij : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (mOff + ws z.bits * j)) (zB z))
    (hik : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (mOff + ws z.bits * k)) (zB z))
    (hx : s.mem.readW (p + BitVec.ofNat 64 (mOff + ws z.bits * j)) z.bits = x)
    (hy : s.mem.readW (p + BitVec.ofNat 64 (mOff + ws z.bits * k)) z.bits = y) :
    WP isa (.block (Impl.Blake2.RISCV64.g P a b c d j k)) s fun s' =>
      (s'.gpr a).setWidth z.bits = (mix P va vb vc vd x y).1 ∧
      (s'.gpr b).setWidth z.bits = (mix P va vb vc vd x y).2.1 ∧
      (s'.gpr c).setWidth z.bits = (mix P va vb vc vd x y).2.2.1 ∧
      (s'.gpr d).setWidth z.bits = (mix P va vb vc vd x y).2.2.2 ∧
      (∀ r, r ≠ a → r ≠ b → r ≠ c → r ≠ d → r ≠ T → r ≠ RT → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p1, h1, p2, h2, p3, h3, p4, h4⟩ := hR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hs
  obtain ⟨⟨hab, hac, had, haT, haR, haS⟩, ⟨hbc, hbd, hbT, hbR, hbS⟩, ⟨hcd, hcT, hcR, hcS⟩,
    ⟨hdT, hdR, hdS⟩, ⟨hTR, hTS⟩, hRS⟩ := hs
  simp only [Impl.Blake2.RISCV64.g, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (addx_ok had haT hbT hdT hoj s va vb vd x ha hb hd (by rw [hp]; exact halj)
    (by rw [hp]; exact hij) (by rw [hp]; exact hx)) fun s₁ ⟨a₁, d₁, o₁, m₁, r₁, w₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (rot_ok hdR p1 h1 s₁) fun s₂ ⟨d₂, o₂, m₂, r₂, w₂⟩ => ?_
  rw [d₁] at d₂
  have b₂ : (s₂.gpr b).setWidth z.bits = vb := by rw [o₂ b hbd hbR, o₁ b (Ne.symm hab) hbd hbT, hb]
  have c₂ : (s₂.gpr c).setWidth z.bits = vc := by rw [o₂ c hcd hcR, o₁ c (Ne.symm hac) hcd hcT, hc]
  rw [WP.block_append_iff]
  refine WP.mono (cx_ok hbc s₂ _ _ _ b₂ c₂ d₂) fun s₃ ⟨c₃, b₃, o₃, m₃, r₃, w₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (rot_ok hbR p2 h2 s₃) fun s₄ ⟨b₄, o₄, m₄, r₄, w₄⟩ => ?_
  rw [b₃] at b₄
  have a₄ : (s₄.gpr a).setWidth z.bits = va + vb + x := by
    rw [o₄ a hab haR, o₃ a hab hac, o₂ a had haR, a₁]
  have d₄ : (s₄.gpr d).setWidth z.bits = (vd ^^^ (va + vb + x)).rotateRight P.R1 := by
    rw [o₄ d (Ne.symm hbd) hdR, o₃ d (Ne.symm hbd) (Ne.symm hcd), d₂]
  have S₄ : s₄.gpr SB = p := by
    rw [o₄ SB (Ne.symm hbS) (Ne.symm hRS), o₃ SB (Ne.symm hbS) (Ne.symm hcS), o₂ SB (Ne.symm hdS) (Ne.symm hRS),
      o₁ SB (Ne.symm haS) (Ne.symm hdS) (Ne.symm hTS), hp]
  have M₄ : s₄.mem = s.mem := by rw [m₄, m₃, m₂, m₁]
  have I₄ : s₄.rd ++ s₄.wr = s.rd ++ s.wr := by rw [r₄, r₃, r₂, r₁, w₄, w₃, w₂, w₁]
  rw [WP.block_append_iff]
  refine WP.mono (addx_ok had haT hbT hdT hok s₄ _ _ _ y a₄ b₄ d₄ (by rw [S₄]; exact halk)
    (by rw [S₄, I₄]; exact hik) (by rw [S₄, M₄]; exact hy)) fun s₅ ⟨a₅, d₅, o₅, m₅, r₅, w₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (rot_ok hdR p3 h3 s₅) fun s₆ ⟨d₆, o₆, m₆, r₆, w₆⟩ => ?_
  rw [d₅] at d₆
  have b₆ : (s₆.gpr b).setWidth z.bits = (vb ^^^ (vc + (vd ^^^ (va + vb + x)).rotateRight P.R1)).rotateRight P.R2 := by
    rw [o₆ b hbd hbR, o₅ b (Ne.symm hab) hbd hbT, b₄]
  have c₆ : (s₆.gpr c).setWidth z.bits = vc + (vd ^^^ (va + vb + x)).rotateRight P.R1 := by
    rw [o₆ c hcd hcR, o₅ c (Ne.symm hac) hcd hcT, o₄ c (Ne.symm hbc) hcR, c₃]
  rw [WP.block_append_iff]
  refine WP.mono (cx_ok hbc s₆ _ _ _ b₆ c₆ d₆) fun s₇ ⟨c₇, b₇, o₇, m₇, r₇, w₇⟩ => ?_
  refine WP.mono (rot_ok hbR p4 h4 s₇) fun s₈ ⟨b₈, o₈, m₈, r₈, w₈⟩ => ?_
  rw [b₇] at b₈
  refine ⟨?_, b₈, ?_, ?_, fun r ra rb rc rd rT rR => ?_, by rw [m₈, m₇, m₆, m₅, M₄],
    by rw [r₈, r₇, r₆, r₅, r₄, r₃, r₂, r₁], by rw [w₈, w₇, w₆, w₅, w₄, w₃, w₂, w₁]⟩
  · rw [o₈ a hab haR, o₇ a hab hac, o₆ a had haR, a₅]; rfl
  · rw [o₈ c (Ne.symm hbc) hcR, c₇]; rfl
  · rw [o₈ d (Ne.symm hbd) hdR, o₇ d (Ne.symm hbd) (Ne.symm hcd), d₆]; rfl
  · rw [o₈ r rb rR, o₇ r rb rc, o₆ r rd rR, o₅ r ra rd rT, o₄ r rb rR, o₃ r rb rc, o₂ r rd rR,
      o₁ r ra rd rT]

end G

/-! ## The work vector in registers -/

/-- The registers of the work vector. -/
def wregs : List Reg :=
  [.a3, .a4, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4, .s5]

theorem wreg_mem' : ∀ k < 16, wreg k ∈ wregs := by decide

theorem wreg_mem {k : Nat} (hk : k < 16) : wreg k ∈ wregs := wreg_mem' k hk

theorem wreg_inj' : ∀ i < 16, ∀ j < 16, wreg i = wreg j → i = j := by decide

theorem wreg_ne {i j : Nat} (hi : i < 16) (hj : j < 16) (h : i ≠ j) : wreg i ≠ wreg j :=
  fun e => h (wreg_inj' i hi j hj e)

theorem ne_wreg {q : Reg} (hq : q ∉ wregs) {k : Nat} (hk : k < 16) : q ≠ wreg k :=
  fun e => hq (by rw [e]; exact wreg_mem hk)

theorem wreg_ne_of {q : Reg} (hq : q ∉ wregs) {k : Nat} (hk : k < 16) : wreg k ≠ q :=
  fun e => hq (e ▸ wreg_mem hk)

theorem T_not_mem : T ∉ wregs := by decide
theorem RT_not_mem : RT ∉ wregs := by decide
theorem SB_not_mem : SB ∉ wregs := by decide

section Rounds
variable {z : Size} (P : Params z.bits)

/-- The work vector `v` is in the low `z.bits` bits of its registers. -/
def Vars (s : State) (v : Work z.bits) : Prop :=
  ∀ k (hk : k < 16), (s.gpr (wreg k)).setWidth z.bits = (v[k]'(by omega))

/-- The rounds invariant, relative to the state `sB` at their start: the work
vector `v` is in its registers, and nothing else has changed but `T` and `RT`. -/
structure RI (sB : State) (v : Work z.bits) (s : State) : Prop where
  vars : Vars s v
  other : ∀ q, q ∉ wregs → q ≠ T → q ≠ RT → s.gpr q = sB.gpr q
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

/-- The message block `M` is at `mOff` of the scratch space at `p` (a multiple
of 8), in the permitted regions. -/
structure Msg (M : Block z.bits) (p : Addr) (s : State) : Prop where
  sb : s.gpr SB = p
  al : p.toNat % 8 = 0
  inr : ∀ j < 16, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (mOff + zB z * j)) (zB z)
  word : ∀ j (hj : j < 16), s.mem.readW (p + BitVec.ofNat 64 (mOff + zB z * j)) z.bits = M ⟨j, hj⟩

theorem Msg.of_RI {M : Block z.bits} {p : Addr} {sB s : State} {v : Work z.bits} (h : Msg M p sB)
    (hr : RI sB v s) : Msg M p s :=
  ⟨(hr.other _ SB_not_mem (by decide) (by decide)).trans h.sb, h.al,
    by rw [hr.rd, hr.wr]; exact h.inr, by rw [hr.mem]; exact h.word⟩

theorem mOff_al (z : Size) (j : Nat) : (mOff + zB z * j) % zB z = 0 := by
  cases z <;> simp only [mOff, zB, Width.bytes] <;> omega

theorem gAt_ok (hR : ROk P) {x y c d : Nat} (hx : x < 16) (hy : y < 16) (hc : c < 16) (hd : d < 16)
    (hq : [x, y, c, d].Nodup) (r i : Nat) {M : Block z.bits} {p : Addr} {sB s : State}
    {v : Work z.bits} (hM : Msg M p sB) (h : RI sB v s) :
    WP isa (Impl.Blake2.RISCV64.gAt P r i x y c d) s (RI sB (Spec.Blake2.G P v ⟨x, hx⟩ ⟨y, hy⟩
      ⟨c, hc⟩ ⟨d, hd⟩ (M (Spec.Blake2.sigmaAt r (2 * i))) (M (Spec.Blake2.sigmaAt r (2 * i + 1))))) := by
  have hm := hM.of_RI h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hq
  obtain ⟨⟨nxy, nxc, nxd⟩, ⟨nyc, nyd⟩, ncd, -⟩ := hq
  have hs : [wreg x, wreg y, wreg c, wreg d, T, RT, SB].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    exact ⟨⟨wreg_ne hx hy nxy, wreg_ne hx hc nxc, wreg_ne hx hd nxd, wreg_ne_of T_not_mem hx,
        wreg_ne_of RT_not_mem hx, wreg_ne_of SB_not_mem hx⟩,
      ⟨wreg_ne hy hc nyc, wreg_ne hy hd nyd, wreg_ne_of T_not_mem hy, wreg_ne_of RT_not_mem hy,
        wreg_ne_of SB_not_mem hy⟩,
      ⟨wreg_ne hc hd ncd, wreg_ne_of T_not_mem hc, wreg_ne_of RT_not_mem hc,
        wreg_ne_of SB_not_mem hc⟩,
      ⟨wreg_ne_of T_not_mem hd, wreg_ne_of RT_not_mem hd, wreg_ne_of SB_not_mem hd⟩, by decide⟩
  have sj := (Spec.Blake2.sigmaAt r (2 * i)).isLt
  have sk := (Spec.Blake2.sigmaAt r (2 * i + 1)).isLt
  have ob : ∀ j < 16, mOff + ws z.bits * j < 2048 := fun j hj => by
    rw [ws_bits]; have := zB_le z
    have := Nat.mul_le_mul this (Nat.le_of_lt_succ hj)
    simp only [mOff]; omega
  refine WP.mono (g_ok P hR hs (ob _ sj) (ob _ sk) s (v[x]'(by omega)) (v[y]'(by omega))
    (v[c]'(by omega)) (v[d]'(by omega)) (M (Spec.Blake2.sigmaAt r (2 * i)))
    (M (Spec.Blake2.sigmaAt r (2 * i + 1))) p (h.vars x hx) (h.vars y hy)
    (h.vars c hc) (h.vars d hd) hm.sb (by rw [ws_bits]; exact al z hm.al (mOff_al z _))
    (by rw [ws_bits]; exact al z hm.al (mOff_al z _)) (by rw [ws_bits]; exact hm.inr _ sj)
    (by rw [ws_bits]; exact hm.inr _ sk) (by rw [ws_bits]; exact hm.word _ sj)
    (by rw [ws_bits]; exact hm.word _ sk))
    fun s' ⟨ha, hb, hc', hd', ho, hmem, hrd, hwr⟩ => ⟨fun k hk => ?_, fun q hq hT hRT => ?_,
      hmem.trans h.mem, hrd.trans h.rd, hwr.trans h.wr⟩
  · rw [G_get P v (a := ⟨x, hx⟩) (b := ⟨y, hy⟩) (c := ⟨c, hc⟩) (d := ⟨d, hd⟩) nxy nxc nxd nyc nyd
      ncd _ _ k hk]
    simp only
    by_cases ey : y = k
    · subst ey; simp only [ite_true]; exact hb
    by_cases ec : c = k
    · subst ec; simp only [ey, ite_true, ite_false]; exact hc'
    by_cases ed : d = k
    · subst ed; simp only [ey, ec, ite_true, ite_false]; exact hd'
    by_cases ex : x = k
    · subst ex; simp only [ey, ec, ed, ite_true, ite_false]; exact ha
    simp only [ey, ec, ed, ex, ite_false]
    rw [ho _ (wreg_ne hk hx (Ne.symm ex)) (wreg_ne hk hy (Ne.symm ey)) (wreg_ne hk hc (Ne.symm ec))
      (wreg_ne hk hd (Ne.symm ed)) (wreg_ne_of T_not_mem hk) (wreg_ne_of RT_not_mem hk)]
    exact h.vars k hk
  · rw [ho q (ne_wreg hq hx) (ne_wreg hq hy) (ne_wreg hq hc) (ne_wreg hq hd) hT hRT]
    exact h.other q hq hT hRT

theorem round_ok (hR : ROk P) (r : Nat) {M : Block z.bits} {p : Addr} {sB s : State}
    {v : Work z.bits} (hM : Msg M p sB) (h : RI sB v s) :
    WP isa (Impl.Blake2.RISCV64.round P r) s (RI sB (Spec.Blake2.round P M v r)) := by
  unfold Impl.Blake2.RISCV64.round
  refine WP.seq (WP.mono (gAt_ok P hR (x := 0) (y := 4) (c := 8) (d := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 0 hM h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok P hR (x := 1) (y := 5) (c := 9) (d := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 1 hM h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok P hR (x := 2) (y := 6) (c := 10) (d := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 2 hM h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok P hR (x := 3) (y := 7) (c := 11) (d := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 3 hM h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok P hR (x := 0) (y := 5) (c := 10) (d := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 4 hM h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok P hR (x := 1) (y := 6) (c := 11) (d := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 5 hM h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok P hR (x := 2) (y := 7) (c := 8) (d := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 6 hM h) fun s h => ?_)
  refine WP.mono (gAt_ok P hR (x := 3) (y := 4) (c := 9) (d := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 7 hM h) fun s h => ?_
  exact h

theorem rounds_ok (hR : ROk P) {M : Block z.bits} {p : Addr} {sB : State} {v : Work z.bits}
    (hM : Msg M p sB) (h : RI sB v sB) (n : Nat) :
    WP isa (Impl.Blake2.RISCV64.rounds P n) sB
      (RI sB ((List.range n).foldl (Spec.Blake2.round P M) v)) := by
  induction n with
  | zero => exact WP.block_nil (M := isa) h
  | succ n ih =>
    refine WP.seq (WP.mono ih fun s hs => ?_)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact round_ok P hR n hM hs

end Rounds

end VG.Proof.Blake2.RISCV64
