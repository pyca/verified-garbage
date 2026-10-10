import VerifiedGarbage.Proof.Ed25519.X86_64.WindowStep
import VerifiedGarbage.Proof.Ed25519.X86_64.CombConstants
import VerifiedGarbage.Proof.Ed25519.X86_64.CombNeg
import VerifiedGarbage.Proof.Ed25519.X86_64.PointSelect
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowEntry
import Mathlib.Tactic.Module
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-! Merged from `Proof.Ed25519.X86_64.CombDigit`. -/
section
/-!
# The comb's digits

Step `c` reads chunk `2c + 1` (`c < 26`) or `2(c - 26)` of the scalar, five of
its bits, expanded one per byte at byte 768 of the scratch (`combIdx`), by
Horner's rule, from table `c` or `c - 26` (`combTblIdx`); chunk 51 is bit 255
alone.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

/-- The chunk step `c` reads. -/
def combIdx (c : Nat) : Nat := if c < 26 then 2 * c + 1 else 2 * (c - 26)

/-- The table step `c` reads. -/
def combTblIdx (c : Nat) : Nat := if c < 26 then c else c - 26

theorem combIdx_lt {c : Nat} (hc : c < 52) : combIdx c < 52 := by
  unfold combIdx; split <;> omega

theorem combTblIdx_lt {c : Nat} (hc : c < 52) : combTblIdx c < 26 := by
  unfold combTblIdx; split <;> omega

theorem combIndex_ok (s : State) {c : Nat} (hc : c < 52) (hb : s.gpr .rbx = BitVec.ofNat 64 c) :
    WP isa combIndex s fun t => t.gpr .rcx = BitVec.ofNat 64 (5 * combIdx c) ∧
      t.gpr .r9 = BitVec.ofNat 64 (combTblIdx c) ∧ Keeps [.rcx, .r9] s t := by
  rw [combIndex]
  have h10 : BitVec.ofNat 64 c + BitVec.ofNat 64 c + (BitVec.ofNat 64 c + BitVec.ofNat 64 c) +
      (BitVec.ofNat 64 c + BitVec.ofNat 64 c + (BitVec.ofNat 64 c + BitVec.ofNat 64 c)) +
      (BitVec.ofNat 64 c + BitVec.ofNat 64 c) = BitVec.ofNat 64 (10 * c) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hcf : decide ((BitVec.ofNat 64 c).toNat < ((26 : BitVec 32).signExtend 64).toNat) =
      decide (c < 26) := by
    rw [show (26 : BitVec 32).signExtend 64 = BitVec.ofNat 64 26 from rfl, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    congr 1; apply propext; omega
  refine WP.seq (WP.mono (show WP isa (.block [.mov .rcx (.reg .rbx), .alu .add .rcx (.reg .rcx),
      .mov .r9 (.reg .rcx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
      .alu .add .rcx (.reg .r9), .mov .r9 (.reg .rbx), .alu .cmp .rbx (.imm 26)]) s
      (fun t => t.gpr .rcx = BitVec.ofNat 64 (10 * c) ∧ t.gpr .r9 = BitVec.ofNat 64 c ∧
        t.cf = some (decide (c < 26)) ∧ Keeps [.rcx, .r9] s t) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, hb, h10, hcf, ite_true,
      ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false])
    fun a ⟨ac, a9, af, ka⟩ => ?_)
  refine WP.ite (decide (c < 26)) (by simp only [eval, af]) (fun h => ?_) (fun h => ?_)
  · have hc26 : c < 26 := of_decide_eq_true h
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ac, ite_true, ite_false, reduceCtorEq,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨?_, ?_, fun r hr => ?_, ka.2.1, ka.2.2.1, ka.2.2.2⟩
    · apply BitVec.eq_of_toNat_eq
      simp only [combIdx, hc26, ↓reduceIte, BitVec.toNat_add, BitVec.toNat_ofNat,
        show (5 : BitVec 32).signExtend 64 = BitVec.ofNat 64 5 from rfl]
      omega
    · simp only [combTblIdx, hc26, ↓reduceIte]; exact a9
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, ite_false]
      exact ka.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact hr)
  · have hc26 : ¬ c < 26 := of_decide_eq_false h
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ac, a9, ite_true, ite_false, reduceCtorEq,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨?_, ?_, fun r hr => ?_, ka.2.1, ka.2.2.1, ka.2.2.2⟩
    · apply BitVec.eq_of_toNat_eq
      simp only [combIdx, hc26, ↓reduceIte, BitVec.toNat_sub, BitVec.toNat_ofNat,
        show (260 : BitVec 32).signExtend 64 = BitVec.ofNat 64 260 from rfl]
      omega
    · apply BitVec.eq_of_toNat_eq
      simp only [combTblIdx, hc26, ↓reduceIte, BitVec.toNat_sub, BitVec.toNat_ofNat,
        show (26 : BitVec 32).signExtend 64 = BitVec.ofNat 64 26 from rfl]
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]
      exact ka.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact hr)

theorem digit_bits (S i : Nat) :
    (S / 32 ^ i) % 32 = (((((S / 2 ^ (5 * i + 4)) % 2 * 2 + (S / 2 ^ (5 * i + 3)) % 2) * 2 +
      (S / 2 ^ (5 * i + 2)) % 2) * 2 + (S / 2 ^ (5 * i + 1)) % 2) * 2 + (S / 2 ^ (5 * i)) % 2) := by
  have h32 : 32 ^ i = 2 ^ (5 * i) := by rw [pow_mul]; norm_num
  have e : ∀ t, S / 2 ^ (5 * i + t) = S / 32 ^ i / 2 ^ t := fun t => by
    rw [h32, Nat.div_div_eq_div_mul, ← pow_add]
  rw [e 4, e 3, e 2, e 1, ← Nat.add_zero (5 * i), e 0]
  simp only [pow_zero, Nat.div_one, Nat.reducePow]
  omega

theorem combBit_ea {s : State} {base : Addr} (hs : Scratch s base) {i : Nat}
    (hrcx : s.gpr .rcx = BitVec.ofNat 64 (5 * i)) (t : Nat) :
    s.ea { base := .rdi, index := some .rcx, disp := 768 + (t : Int) } =
      off base (768 + (5 * i + t)) := by
  simp only [State.ea, hs.rdi, hrcx, BitVec.mul_one]
  rw [show (768 : Int) + (t : Int) = ((768 + t : Nat) : Int) by omega, BitVec.ofInt_natCast,
    BitVec.add_assoc, ← BitVec.ofNat_add]
  exact congrArg (off base) (by omega)

theorem loadBit_ok {s : State} {base : Addr} (hs : Scratch s base) {S i : Nat}
    (hrcx : s.gpr .rcx = BitVec.ofNat 64 (5 * i))
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2))
    (dst : Reg) (t : Nat) (ht : 5 * i + t < 256) :
    WP isa (.block [combBit dst t]) s fun u =>
      u.gpr dst = BitVec.ofNat 64 ((S / 2 ^ (5 * i + t)) % 2) ∧ Keeps [dst] s u := by
  have hr : InRegions (s.rd ++ s.wr) (off base (768 + (5 * i + t))) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by omega) (by omega)⟩
  have bit : (s.mem (off base (768 + (5 * i + t)))).setWidth 64 =
      BitVec.ofNat 64 ((S / 2 ^ (5 * i + t)) % 2) := by
    rw [hb _ ht]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  apply WP.of_runBlock
  simp only [combBit, runBlock_cons, runStep_some, runBlock_nil, exec, State.load8,
    combBit_ea hs hrcx, hr, bit, ite_true, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_setReg_self]
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem addRax_ok (s : State) (r : Reg) :
    WP isa (.block [.alu .add .rax (.reg r)]) s fun u =>
      u.gpr .rax = s.gpr .rax + s.gpr r ∧ Keeps [.rax] s u := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨trivial, fun q hq => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hq, ite_false]

theorem combDigit_ok {s : State} {base : Addr} (hs : Scratch s base) {S i : Nat} (hi : i < 51)
    (hrcx : s.gpr .rcx = BitVec.ofNat 64 (5 * i))
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa (.block combDigit) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 ((S / 32 ^ i) % 32) ∧ Keeps [.rax, .rdx] s t := by
  rw [show combDigit = [combBit .rax 4] ++ ([.alu .add .rax (.reg .rax)] ++ ([combBit .rdx 3] ++
      ([.alu .add .rax (.reg .rdx)] ++ ([.alu .add .rax (.reg .rax)] ++ ([combBit .rdx 2] ++
      ([.alu .add .rax (.reg .rdx)] ++ ([.alu .add .rax (.reg .rax)] ++ ([combBit .rdx 1] ++
      ([.alu .add .rax (.reg .rdx)] ++ ([.alu .add .rax (.reg .rax)] ++ ([combBit .rdx 0] ++
      [.alu .add .rax (.reg .rdx)]))))))))))) from rfl]
  have keep : ∀ {x y : State} {rs : List Reg}, Keeps rs x y → (∀ r ∈ rs, r = .rax ∨ r = .rdx) →
      Keeps [.rax, .rdx] x y := fun k h => ⟨fun r hr => k.1 r (fun hm => by
        rcases h r hm with rfl | rfl <;> simp at hr), k.2⟩
  have tr : ∀ {x y z : State}, Keeps [.rax, .rdx] x y → Keeps [.rax, .rdx] y z →
      Keeps [.rax, .rdx] x z := fun a b => ⟨fun r hr => (b.1 r hr).trans (a.1 r hr),
        b.2.1.trans a.2.1, b.2.2.1.trans a.2.2.1, b.2.2.2.trans a.2.2.2⟩
  have st : ∀ {x : State}, Keeps [.rax, .rdx] s x → Scratch x base ∧
      x.gpr .rcx = BitVec.ofNat 64 (5 * i) ∧
      ∀ q < 256, x.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2) := fun k =>
    ⟨⟨(k.1 _ (by decide)).trans hs.rdi, k.2.2.2 ▸ hs.wr, hs.nowrap⟩,
      (k.1 _ (by decide)).trans hrcx, fun q hq => by rw [k.2.1]; exact hb q hq⟩
  rw [WP.block_append_iff]
  refine WP.mono (loadBit_ok hs hrcx hb .rax 4 (by omega)) fun a ⟨a4, ka⟩ => ?_
  have ka' := keep ka (by simp)
  rw [WP.block_append_iff]
  refine WP.mono (addRax_ok a .rax) fun a' ⟨a'v, ka₂⟩ => ?_
  have ka'' := tr ka' (keep ka₂ (by simp))
  obtain ⟨hsa, hca, hba⟩ := st ka''
  rw [WP.block_append_iff]
  refine WP.mono (loadBit_ok hsa hca hba .rdx 3 (by omega)) fun b ⟨b3, kb⟩ => ?_
  have kb' := tr ka'' (keep kb (by simp))
  rw [WP.block_append_iff]
  refine WP.mono (addRax_ok b .rdx) fun b' ⟨b'v, kb₂⟩ => ?_
  have kb'' := tr kb' (keep kb₂ (by simp))
  rw [WP.block_append_iff]
  refine WP.mono (addRax_ok b' .rax) fun c ⟨cv, kc⟩ => ?_
  have kc' := tr kb'' (keep kc (by simp))
  obtain ⟨hsc, hcc, hbc⟩ := st kc'
  rw [WP.block_append_iff]
  refine WP.mono (loadBit_ok hsc hcc hbc .rdx 2 (by omega)) fun d ⟨d2, kd⟩ => ?_
  have kd' := tr kc' (keep kd (by simp))
  rw [WP.block_append_iff]
  refine WP.mono (addRax_ok d .rdx) fun e ⟨ev, ke⟩ => ?_
  have ke' := tr kd' (keep ke (by simp))
  rw [WP.block_append_iff]
  refine WP.mono (addRax_ok e .rax) fun f ⟨fv, kf⟩ => ?_
  have kf' := tr ke' (keep kf (by simp))
  obtain ⟨hsf, hcf, hbf⟩ := st kf'
  rw [WP.block_append_iff]
  refine WP.mono (loadBit_ok hsf hcf hbf .rdx 1 (by omega)) fun g ⟨g1, kg⟩ => ?_
  have kg' := tr kf' (keep kg (by simp))
  rw [WP.block_append_iff]
  refine WP.mono (addRax_ok g .rdx) fun h ⟨hv, kh⟩ => ?_
  have kh' := tr kg' (keep kh (by simp))
  rw [WP.block_append_iff]
  refine WP.mono (addRax_ok h .rax) fun u ⟨uv, ku⟩ => ?_
  have ku' := tr kh' (keep ku (by simp))
  obtain ⟨hsu, hcu, hbu⟩ := st ku'
  rw [WP.block_append_iff]
  refine WP.mono (loadBit_ok hsu hcu hbu .rdx 0 (by omega)) fun w ⟨w0, kw⟩ => ?_
  have kw' := tr ku' (keep kw (by simp))
  refine WP.mono (addRax_ok w .rdx) fun t ⟨tv, kt⟩ => ⟨?_, tr kw' (keep kt (by simp))⟩
  rw [tv, w0, kw.1 _ (by decide), uv, hv, g1, kg.1 _ (by decide), fv, ev, d2, kd.1 _ (by decide), cv,
    b'v, b3, kb.1 _ (by decide), a'v, a4, digit_bits S i, Nat.add_zero]
  have l0 := Nat.mod_lt (S / 2 ^ (5 * i)) (show 2 > 0 by decide)
  have l1 := Nat.mod_lt (S / 2 ^ (5 * i + 1)) (show 2 > 0 by decide)
  have l2 := Nat.mod_lt (S / 2 ^ (5 * i + 2)) (show 2 > 0 by decide)
  have l3 := Nat.mod_lt (S / 2 ^ (5 * i + 3)) (show 2 > 0 by decide)
  have l4 := Nat.mod_lt (S / 2 ^ (5 * i + 4)) (show 2 > 0 by decide)
  generalize S / 2 ^ (5 * i) % 2 = b0 at *
  generalize S / 2 ^ (5 * i + 1) % 2 = b1 at *
  generalize S / 2 ^ (5 * i + 2) % 2 = b2 at *
  generalize S / 2 ^ (5 * i + 3) % 2 = b3 at *
  generalize S / 2 ^ (5 * i + 4) % 2 = b4 at *
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem rbxCmp_ok (s : State) (c k : Nat) (hc : c < 64) (hk : k < 64)
    (hb : s.gpr .rbx = BitVec.ofNat 64 c) :
    WP isa (.block [.alu .cmp .rbx (.imm (BitVec.ofNat 32 k))]) s fun t =>
      t.zf = some (decide (c = k)) ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have he : (BitVec.ofNat 32 k).signExtend 64 = BitVec.ofNat 64 k := by
    have : ∀ k < 64, (BitVec.ofNat 32 k).signExtend 64 = BitVec.ofNat 64 k := by decide
    exact this k hk
  have hz : (BitVec.ofNat 64 c - BitVec.ofNat 64 k == 0) = decide (c = k) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega_using [hc, hk]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, hb, he, hz, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, rfl, rfl, rfl⟩

/-- The top chunk, bit 255 alone, is chunk 51 of a scalar below `2^256`. -/
theorem top_chunk {S : Nat} (hS : S < 2 ^ 256) : (S / 2 ^ (5 * 51 + 0)) % 2 = (S / 32 ^ 51) % 32 := by
  rw [show (32 : Nat) ^ 51 = 2 ^ (5 * 51 + 0) by norm_num]
  have : S / 2 ^ (5 * 51 + 0) < 2 :=
    Nat.div_lt_of_lt_mul (by rw [show 2 ^ (5 * 51 + 0) * 2 = 2 ^ 256 by norm_num]; exact hS)
  omega

theorem combChunk_ok {s : State} {base : Addr} (hs : Scratch s base) {S c : Nat} (hc : c < 52)
    (hS : S < 2 ^ 256) (hb : s.gpr .rbx = BitVec.ofNat 64 c)
    (hrcx : s.gpr .rcx = BitVec.ofNat 64 (5 * combIdx c))
    (hbits : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa combChunk s fun t =>
      t.gpr .rax = BitVec.ofNat 64 ((S / 32 ^ combIdx c) % 32) ∧ Keeps [.rax, .rdx] s t := by
  rw [combChunk]
  refine WP.seq (WP.mono (rbxCmp_ok s c 25 (by omega) (by decide) hb) fun a ⟨az, ag, am, ar, aw⟩ => ?_)
  have hsa : Scratch a base := ⟨by rw [ag]; exact hs.rdi, aw ▸ hs.wr, hs.nowrap⟩
  have ka : Keeps [.rax, .rdx] s a := ⟨fun r _ => by rw [ag], am, ar, aw⟩
  have hca : a.gpr .rcx = BitVec.ofNat 64 (5 * combIdx c) := by rw [ag]; exact hrcx
  have hba : ∀ q < 256, a.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2) := by
    rw [am]; exact hbits
  refine WP.ite (decide (c = 25)) (by simp only [eval, az]) (fun h => ?_) (fun h => ?_)
  · have h25 : c = 25 := of_decide_eq_true h
    have hi : combIdx c = 51 := by subst h25; rfl
    rw [hi] at hca ⊢
    refine WP.mono (loadBit_ok hsa hca hba .rax 0 (by decide)) fun t ⟨tv, kt⟩ =>
      ⟨by rw [tv, top_chunk hS], ⟨fun r hr => (kt.1 r (by simp at hr ⊢; exact hr.1)).trans (ka.1 r hr),
        kt.2.1.trans ka.2.1, kt.2.2.1.trans ka.2.2.1, kt.2.2.2.trans ka.2.2.2⟩⟩
  · have h25 : c ≠ 25 := of_decide_eq_false h
    have hi : combIdx c < 51 := by unfold combIdx; split <;> omega
    refine WP.mono (combDigit_ok hsa hi hca hba) fun t ⟨tv, kt⟩ => ⟨tv, ?_⟩
    exact ⟨fun r hr => (kt.1 r hr).trans (ka.1 r hr), kt.2.1.trans ka.2.1, kt.2.2.1.trans ka.2.2.1,
      kt.2.2.2.trans ka.2.2.2⟩

end VG.Proof.Ed25519.X86_64
end

/-! Merged from `Proof.Ed25519.X86_64.CombSign`. -/
section
/-!
# The comb's signed digits

`combSign` turns the chunk `n` into the digit `n - 16`'s magnitude, in `rax`,
and the mask of its sign, at byte `combSignMask`; `combNeg` negates the
selected cached point in slots 4–7 under that mask.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

/-- The magnitude of the digit `n - 16`. -/
def mag (n : Nat) : Nat := if n < 16 then 16 - n else n - 16

/-- The mask of the digit `n - 16`'s sign: all ones if it is negative. -/
def signMask (n : Nat) : BitVec 64 := if n < 16 then BitVec.allOnes 64 else 0

private theorem sign_fact : ∀ n < 32,
    ((BitVec.ofNat 64 n - (16 : BitVec 32).signExtend 64 ^^^
        0#64 - (BitVec.ofBool (decide ((BitVec.ofNat 64 n).toNat <
          ((16 : BitVec 32).signExtend 64).toNat))).setWidth 64) -
      (0#64 - (BitVec.ofBool (decide ((BitVec.ofNat 64 n).toNat <
        ((16 : BitVec 32).signExtend 64).toNat))).setWidth 64) = BitVec.ofNat 64 (mag n)) ∧
    0#64 - (BitVec.ofBool (decide ((BitVec.ofNat 64 n).toNat <
      ((16 : BitVec 32).signExtend 64).toNat))).setWidth 64 = signMask n := by
  decide +kernel

theorem combSign_ok {s : State} {base : Addr} (hs : Scratch s base) {n : Nat} (hn : n < 32)
    (hax : s.gpr .rax = BitVec.ofNat 64 n) :
    WP isa (.block combSign) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (mag n) ∧ t.mem.readW (off base combSignMask) 64 = signMask n ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base combSignMask 8 s.mem t.mem := by
  have hw : InRegions s.wr (off base combSignMask) 8 :=
    ⟨_, hs.wr, Offset.contains_base _ (by simp only [combSignMask]; omega) (by simp only [combSignMask]; omega)⟩
  apply WP.of_runBlock
  simp only [combSign, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.store64, Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.cf_setReg, RegUpd.cf_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, hs.rdi, hax, hw, ite_true, ite_false, reduceCtorEq,
    BitVec.sub_self, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨(sign_fact n hn).1, ?_, fun r h1 h2 => ?_, rfl, trivial, ?_⟩
  · rw [Mem.readW_writeW_self64]; exact (sign_fact n hn).2
  · simp only [h1, h2, ite_false]
  · exact VG.Proof.X25519.X86_64.writeW_outside _ _ _ (by simp only [combSignMask]; omega)

/-! ## The negation -/

/-- The cached point `c` negated: `[Y + X, Y - X, -2dT, 2Z]` for `[Y - X, Y + X, 2dT, 2Z]`. -/
def negCached (c : Spec.Ed25519.Point) : Spec.Ed25519.Point := ⟨c.Y, c.X, 0 - c.Z, c.T⟩

theorem negCached_cache (q : Spec.Ed25519.Point) : negCached (cache q) = cache (negPoint q) := by
  simp only [negCached, cache, negPoint, Spec.Ed25519.Point.mk.injEq]
  refine ⟨toZ_inj.1 ?_, toZ_inj.1 ?_, toZ_inj.1 ?_, trivial⟩ <;>
    simp only [toZ_add, toZ_sub, toZ_mul, toZ_zero] <;> ring

variable {fld : Arith} [EdArith fld]

theorem loadSignMask_ok {s : State} {base : Addr} (hs : Scratch s base) {m : BitVec 64}
    (hm : s.mem.readW (off base combSignMask) 64 = m) :
    WP isa (.block [.mov .rcx (.mem (Impl.X25519.X86_64.sc combSignMask))]) s fun t =>
      t.gpr .rcx = m ∧ Keeps [.rcx] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base combSignMask) 8 :=
    ⟨_, List.mem_append_right _ hs.wr,
      Offset.contains_base _ (by simp only [combSignMask]; omega) (by simp only [combSignMask]; omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, hs.rdi, hr, hm, ite_true, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem signMask_eq (n : Nat) : signMask n = Proof.X25519.X86_64.mask (decide (n < 16)) := by
  by_cases h : n < 16 <;> simp [signMask, Proof.X25519.X86_64.mask, h]

theorem combNeg_ok {s : State} {base : Addr} (hs : Scratch s base) {n : Nat}
    (hm : s.mem.readW (off base combSignMask) 64 = signMask n) :
    WP isa (.block combNeg) s fun t =>
      point (env t.mem base) 4 5 6 7 = (if n < 16 then negCached (point (env s.mem base) 4 5 6 7)
        else point (env s.mem base) 4 5 6 7) ∧ Keep base s t ∧
      (∀ i : Slot, (i.val < 4 ∨ 10 ≤ i.val) → env t.mem base i = env s.mem base i) ∧
      Outside base (offset 4) 96 s.mem t.mem := by
  rw [combNeg, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadSignMask_ok hs (m := signMask n) hm) fun b ⟨bc, kb⟩ => ?_
  have hsb := hs.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (swapFieldX_ok hsb 4 5 (by decide) (by decide) (sw := decide (n < 16))
    (by rw [bc, signMask_eq])) fun u ⟨ku, uc, uv, uo⟩ => ?_
  have hsu := hsb.of_keep ku
  refine WP.mono (negFieldWide_ok hsu (x := offset 6) (by decide) (sw := decide (n < 16))
    (by rw [uc, bc, signMask_eq])) fun t ⟨tOp, _, tF⟩ => ?_
  have kbk : Keep base s b := ⟨fun r hr => kb.1 r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; decide)),
    kb.2.2.1, kb.2.2.2, by rw [kb.2.1]; exact Outside.refl _ _ _ _⟩
  have ktOp : Keep base u t :=
    ⟨tOp.gpr, tOp.rd, tOp.wr, fun x hx => tOp.mem x (by simp only [offset] at *; omega)⟩
  have henv : ∀ i : Slot, i ≠ 6 → env t.mem base i = env u.mem base i := fun i hi =>
    congrArg VG.Proof.X25519.toFe (tOp.mem.fe (by
      have := i.isLt
      simp only [offset] at *
      rcases Nat.lt_trichotomy i.val 6 with h | h | h
      · left; omega
      · exact absurd (Fin.ext h) hi
      · right; omega) (by simp only [offset]; have := i.isLt; omega))
  have hbs : env b.mem base = env s.mem base := by rw [kb.2.1]
  have hu : env u.mem base = swapEnv 4 5 (decide (n < 16)) (env s.mem base) := by rw [uv, hbs]
  have h6 : env u.mem base 6 = env s.mem base 6 := by rw [hu]; simp [swapEnv]
  have e4 : env t.mem base 4 = (if n < 16 then env s.mem base 5 else env s.mem base 4) := by
    rw [henv 4 (by decide), hu]; by_cases h : n < 16 <;> simp [swapEnv, h]
  have e5 : env t.mem base 5 = (if n < 16 then env s.mem base 4 else env s.mem base 5) := by
    rw [henv 5 (by decide), hu]; by_cases h : n < 16 <;> simp [swapEnv, h]
  have e7 : env t.mem base 7 = env s.mem base 7 := by
    rw [henv 7 (by decide), hu]; simp [swapEnv]
  have e6 : env t.mem base 6 = (if n < 16 then 0 - env s.mem base 6 else env s.mem base 6) := by
    show VG.Proof.X25519.X86_64.F t.mem base (offset 6) = _
    rw [tF]
    by_cases h : n < 16
    · simp only [h, decide_true, ↓reduceIte]
      rw [show VG.Proof.X25519.X86_64.F u.mem base (offset 6) = env u.mem base 6 from rfl, h6,
        zero_sub]
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [show VG.Proof.X25519.X86_64.F u.mem base (offset 6) = env u.mem base 6 from rfl, h6]
  refine ⟨?_, (kbk.trans ku).trans ktOp, fun i hi => ?_, ?_⟩
  · by_cases h : n < 16
    · simp only [point, e4, e5, e6, e7, h, ↓reduceIte, negCached]
    · simp only [point, e4, e5, e6, e7, h, ↓reduceIte]
  · have hi6 : i ≠ 6 := fun h => by subst h; simp at hi
    have hi4 : i ≠ 4 := fun h => by subst h; simp at hi
    have hi5 : i ≠ 5 := fun h => by subst h; simp at hi
    rw [henv i hi6, hu]
    simp [swapEnv, hi4, hi5]
  · have hsb : Outside base (offset 4) 96 s.mem b.mem := by rw [kb.2.1]; exact Outside.refl _ _ _ _
    exact (hsb.trans (uo.mono (by decide) (by decide))).trans (tOp.mem.mono (by decide) (by decide))

end VG.Proof.Ed25519.X86_64
end

/-!
# The comb's loop

After step `c`, the accumulator represents `[v]B` for the partial sum `v =
combVal S c`: `G` and the odd digits `d_{2j+1} 1024^j` for `j < c` while `c ≤
26`, then 32 times all of those, `G` again, and the even digits `d_{2j}
1024^j` for `j < c - 26`, with the digits `d_i = n_i - 16`. At `c = 52` that is
the scalar (`comb_sum`), since `G = 16 Σ_{j < 26} 1024^j`.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

variable {fld : Arith} [EdArith fld]

/-- Digit `i` of `S` in radix 32. -/
def nib (S i : Nat) : Nat := (S / 32 ^ i) % 32

/-- `Σ_{j < c} n_{2j+1} 1024^j`. -/
def oddSum (S : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => oddSum S c + nib S (2 * c + 1) * 1024 ^ c

/-- `Σ_{j < c} n_{2j} 1024^j`. -/
def evenSum (S : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => evenSum S c + nib S (2 * c) * 1024 ^ c

theorem comb_partial (S : Nat) : ∀ n, 32 * oddSum S n + evenSum S n = S % 1024 ^ n
  | 0 => by simp [oddSum, evenSum, Nat.mod_one]
  | n + 1 => by
    have ih := comb_partial S n
    have h32 : 1024 ^ n = 32 ^ (2 * n) := by rw [pow_mul]; norm_num
    have hd : S / 32 ^ (2 * n + 1) = S / 32 ^ (2 * n) / 32 := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ]
    have hm : S % 1024 ^ (n + 1) = S % 1024 ^ n + 1024 ^ n * (S / 1024 ^ n % 1024) := by
      rw [pow_succ, Nat.mod_mul]
    simp only [oddSum, evenSum, nib]
    rw [hm, ← ih, hd, h32]
    generalize S / 32 ^ (2 * n) = x
    generalize 32 ^ (2 * n) = y
    have : x % 1024 = x % 32 + 32 * (x / 32 % 32) := by omega
    rw [this]; ring

/-- `Σ_{j < c} 1024^j`. -/
def geom : Nat → Nat
  | 0 => 0
  | c + 1 => geom c + 1024 ^ c

theorem combGVal_eq : combGVal = 16 * geom 26 := by decide

/-- The comb's digit `i`: `n_i - 16`, from `-16` to `15`. -/
def sdig (S i : Nat) : ℤ := (nib S i : ℤ) - 16

/-- `Σ_{j < c} d_{2j+1} 1024^j`. -/
def oddSumZ (S : Nat) : Nat → ℤ
  | 0 => 0
  | c + 1 => oddSumZ S c + sdig S (2 * c + 1) * 1024 ^ c

/-- `Σ_{j < c} d_{2j} 1024^j`. -/
def evenSumZ (S : Nat) : Nat → ℤ
  | 0 => 0
  | c + 1 => evenSumZ S c + sdig S (2 * c) * 1024 ^ c

theorem oddSumZ_eq (S : Nat) : ∀ c, oddSumZ S c = oddSum S c - 16 * geom c
  | 0 => rfl
  | c + 1 => by
    simp only [oddSumZ, oddSum, geom, oddSumZ_eq S c, sdig]
    push_cast; ring

theorem evenSumZ_eq (S : Nat) : ∀ c, evenSumZ S c = evenSum S c - 16 * geom c
  | 0 => rfl
  | c + 1 => by
    simp only [evenSumZ, evenSum, geom, evenSumZ_eq S c, sdig]
    push_cast; ring

/-- The accumulator's multiple of `B` after `c` steps. -/
def combVal (S c : Nat) : ℤ :=
  if c ≤ 26 then combGVal + oddSumZ S c else 32 * (combGVal + oddSumZ S 26) + combGVal + evenSumZ S (c - 26)

theorem comb_sum {S : Nat} (hS : S < 2 ^ 256) : combVal S 52 = S := by
  simp only [combVal, show ¬ 52 ≤ 26 by decide, ↓reduceIte, show 52 - 26 = 26 from rfl, oddSumZ_eq,
    evenSumZ_eq, combGVal_eq]
  have h := comb_partial S 26
  rw [Nat.mod_eq_of_lt (by have : (2 : Nat) ^ 256 < 1024 ^ 26 := by norm_num
                           omega)] at h
  have h' : (32 * oddSum S 26 + evenSum S 26 : ℤ) = S := by exact_mod_cast h
  push_cast
  linear_combination h'

theorem combIdx_nib (S c : Nat) (hc : c < 52) :
    sdig S (combIdx c) * 1024 ^ (combTblIdx c) +
      (if c = 26 then 32 * combVal S c + combGVal else combVal S c) = combVal S (c + 1) := by
  unfold combIdx combTblIdx combVal
  by_cases h : c < 26
  · simp only [h, ↓reduceIte, show c ≠ 26 by omega, show c ≤ 26 by omega, show c + 1 ≤ 26 by omega,
      oddSumZ]
    ring
  · have hs : c + 1 - 26 = (c - 26) + 1 := by omega
    by_cases h26 : c = 26
    · subst h26
      simp only [show ¬ 26 < 26 by decide, ↓reduceIte, le_refl, show ¬ 27 ≤ 26 by decide,
        show 27 - 26 = 0 + 1 from rfl, evenSumZ, show 26 - 26 = 0 from rfl]
      ring
    · simp only [h, h26, ↓reduceIte, show ¬ c ≤ 26 by omega, show ¬ c + 1 ≤ 26 by omega, hs, evenSumZ]
      ring

/-- The accumulator's multiple of `B` after `c` steps, from `[G']B` (`combStart`), for which five
doublings make up for the digits' offset (`combStart_32`). -/
def combValS (S c : Nat) : ℤ :=
  if c ≤ 26 then combStartVal + oddSumZ S c else 32 * (combStartVal + oddSumZ S 26) + evenSumZ S (c - 26)

theorem combValS_sum {S : Nat} (hS : S < 2 ^ 256) : combValS S 52 • baseAff = (S : ℤ) • baseAff := by
  have e : combValS S 52 = (S : ℤ) + ((32 * combStartVal : Nat) : ℤ) - ((33 * combGVal : Nat) : ℤ) := by
    have h := comb_sum hS
    simp only [combVal, combValS, show ¬ 52 ≤ 26 by decide, ↓reduceIte, show 52 - 26 = 26 from rfl] at h ⊢
    push_cast
    linear_combination h
  rw [e, sub_smul, add_smul]
  simp only [natCast_zsmul]
  rw [combStart_32, add_sub_cancel_right]

theorem combIdx_nibS (S c : Nat) (hc : c < 52) :
    sdig S (combIdx c) * 1024 ^ (combTblIdx c) +
      (if c = 26 then 32 * combValS S c else combValS S c) = combValS S (c + 1) := by
  unfold combIdx combTblIdx combValS
  by_cases h : c < 26
  · simp only [h, ↓reduceIte, show c ≠ 26 by omega, show c ≤ 26 by omega, show c + 1 ≤ 26 by omega,
      oddSumZ]
    ring
  · have hs : c + 1 - 26 = (c - 26) + 1 := by omega
    by_cases h26 : c = 26
    · subst h26
      simp only [show ¬ 26 < 26 by decide, ↓reduceIte, le_refl, show ¬ 27 ≤ 26 by decide,
        show 27 - 26 = 0 + 1 from rfl, evenSumZ]
      ring
    · simp only [h, h26, ↓reduceIte, show ¬ c ≤ 26 by omega, show ¬ c + 1 ≤ 26 by omega, hs, evenSumZ]
      ring

/-! ## Counters -/

theorem rbxNext52_ok (s : State) (n : Nat) (hn : n < 52) (hc : s.gpr .rbx = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 52)]) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (n + 1) ∧ t.zf = some (decide (n + 1 = 52)) ∧
      Keeps [.rbx] s t := by
  have ha : BitVec.ofNat 64 n + (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (n + 1) := by
    rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add]
  have hz : (BitVec.ofNat 64 (n + 1) - (52 : BitVec 32).signExtend 64 == 0) =
      decide (n + 1 = 52) := by
    rw [show (52 : BitVec 32).signExtend 64 = BitVec.ofNat 64 52 from rfl]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega_using [hn]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags,
    hc, ha, hz, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-! ## A step -/

/-- The loop's invariant, after `c` steps. -/
structure CombInv (s₀ : State) (base T : Addr) (S c : Nat) (s : State) : Prop where
  bound : c ≤ 52
  scratch : Scratch s base
  counter : s.gpr .rbx = BitVec.ofNat 64 c
  d : env s.mem base 16 = Spec.Ed25519.d
  bits : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)
  value : Rep (point (env s.mem base) 0 1 2 3) (combValS S c • baseAff)
  keep : PowersKeep base 56 7368 s₀ s
  tbl : CombTbl s T

theorem bits_far {base : Addr} {q : Nat} (hq : q < 256) :
    ofs base (off base (768 + q)) = 768 + q := Proof.X25519.X86_64.ofs_off' base (by omega)

/-- The affine addition's body (`vg_ed25519_r64_add_affine_ext`'s): the point in slots 0–3 plus `q`,
whose affine cached form is in slots 4–6. -/
theorem affBody_ok {s : State} {base : Addr} (hs : Scratch s base) (q : Spec.Ed25519.Point)
    (hq : (⟨env s.mem base 4, env s.mem base 5, env s.mem base 6, 2⟩ : Spec.Ed25519.Point) = cache q) :
    WP isa (Point64.bodies fld).aff s fun t => Keep base s t ∧ point (env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) :=
  WP.mono (Point64.fn_keep hs pointAddAffineOps Point64.addAffineFn_keeps (by decide)) fun t ⟨kt, vt⟩ => by
    rw [vt]
    exact ⟨kt, pointAddAffine_eval _ q hq, pointAddAffine_high _⟩

theorem zsmul_32 (v : ℤ) (g : Nat) (P : EPoint dZ) :
    (32 : Nat) • (v • P) + g • P = (32 * v + g) • P := by
  rw [add_smul, mul_smul, ← natCast_zsmul, ← natCast_zsmul]; rfl

theorem zsmul_32' (v : ℤ) (P : EPoint dZ) : (32 : Nat) • (v • P) = (32 * v) • P := by
  rw [mul_smul, ← natCast_zsmul]; rfl

/-- A doubling, the body of `vg_ed25519_r64_double_ext`: `[2]` of the point in slots 0–3. -/
theorem dblBody_ok {s : State} {base : Addr} {a : EPoint dZ} (hs : Scratch s base)
    (ha : Rep (point (env s.mem base) 0 1 2 3) a) :
    WP isa ((Point64.bodies fld).dbl true) s fun t => Rep (point (env t.mem base) 0 1 2 3) ((2 : Nat) • a) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧ DoubleKeep base s t := by
  refine WP.mono (PtOk.dbl (pt := Point64.bodies fld) hs true)
    fun t ⟨kt, vt⟩ => ⟨?_, fun i hi => by rw [vt]; exact point_ops_high _ (by decide) _ i hi,
      ⟨fun r _ hc => kt.gpr r hc, kt.rd, kt.wr, kt.mem⟩⟩
  rw [vt, two_nsmul]
  exact (dblOps_rep _ true ha.proj).2 rfl

/-- Five doublings: `[32]` of the point in slots 0–3. -/
theorem combDouble_ok {s : State} {base : Addr} {a : EPoint dZ} (hs : Scratch s base)
    (ha : Rep (point (env s.mem base) 0 1 2 3) a) :
    WP isa (combDouble (Point64.bodies fld)) s fun t => Rep (point (env t.mem base) 0 1 2 3) ((32 : Nat) • a) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧ DoubleKeep base s t := by
  rw [combDouble]
  refine WP.seq (WP.mono (dblBody_ok (fld := fld) hs ha) fun b₁ ⟨r₁, h₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (dblBody_ok (fld := fld) (k₁.scratch hs) r₁) fun b₂ ⟨r₂, h₂, k₂⟩ => ?_)
  have k₂' := k₁.trans k₂
  refine WP.seq (WP.mono (dblBody_ok (fld := fld) (k₂'.scratch hs) r₂) fun b₃ ⟨r₃, h₃, k₃⟩ => ?_)
  have k₃' := k₂'.trans k₃
  refine WP.seq (WP.mono (dblBody_ok (fld := fld) (k₃'.scratch hs) r₃) fun b₄ ⟨r₄, h₄, k₄⟩ => ?_)
  have k₄' := k₃'.trans k₄
  refine WP.mono (dblBody_ok (fld := fld) (k₄'.scratch hs) r₄) fun t ⟨r₅, h₅, k₅⟩ =>
    ⟨?_, fun i hi => (h₅ i hi).trans ((h₄ i hi).trans ((h₃ i hi).trans ((h₂ i hi).trans (h₁ i hi)))),
      k₄'.trans k₅⟩
  simp only [smul_smul] at r₅
  exact r₅

/-- `r8` = the magnitude in `rax`, and `rdx` = the table index in `r9`. -/
theorem combMagIdx_ok (s : State) {m j : Nat} (ha : s.gpr .rax = BitVec.ofNat 64 m)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 j) :
    WP isa (.block [.mov .r8 (.reg .rax), .mov .rdx (.reg .r9)]) s fun t =>
      t.gpr .r8 = BitVec.ofNat 64 m ∧ t.gpr .rdx = BitVec.ofNat 64 j ∧ Keeps [.r8, .rdx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg, ha, h9,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

theorem combStep_ok {sel : List Instr} (hsel : SelOk sel) {s₀ s : State} {base T : Addr} {S c : Nat}
    (h : CombInv s₀ base T S c s) (hfar : TblFar base T) (hS : S < 2 ^ 256) (hc : c < 52) :
    WP isa (combStep sel (Point64.bodies fld)) s fun t => t.zf = some (decide (c + 1 = 52)) ∧
      CombInv s₀ base T S (c + 1) t := by
  rw [combStep]
  refine WP.seq (WP.mono_syms (rbxCmp_ok s c 26 (by omega) (by decide) h.counter)
    fun a ⟨az, ag, am, ar, aw⟩ asy => ?_)
  have hsa : Scratch a base := ⟨by rw [ag]; exact h.scratch.rdi, aw ▸ h.scratch.wr, h.scratch.nowrap⟩
  have kas : PowersKeep base 56 7368 s a := ⟨fun r _ _ _ => by rw [ag], ar, aw, by rw [am]; exact TableFrame.refl _ _ _ _⟩
  -- The doublings, before the even digits.
  have hite : WP isa (.ite .e (combDouble (Point64.bodies fld)) (.block [])) a fun b =>
      Scratch b base ∧ b.gpr .rbx = BitVec.ofNat 64 c ∧ env b.mem base 16 = Spec.Ed25519.d ∧
      (∀ q < 256, b.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) ∧
      Rep (point (env b.mem base) 0 1 2 3)
        ((if c = 26 then 32 * combValS S c else combValS S c) • baseAff) ∧
      PowersKeep base 56 7368 a b := by
    refine WP.ite (decide (c = 26)) (by simp only [eval, az]) (fun hy => ?_) (fun hn => ?_)
    · have h26 : c = 26 := of_decide_eq_true hy
      refine WP.mono (combDouble_ok (fld := fld) (a := combValS S c • baseAff) hsa (by rw [am]; exact h.value))
        fun b ⟨br, bh, bk⟩ => ?_
      refine ⟨bk.scratch hsa, (bk.gpr _ (by decide) (by decide)).trans (by rw [ag]; exact h.counter),
        by rw [bh 16 (by decide), am]; exact h.d,
        fun q hq => by
          rw [bk.mem _ (by rw [bits_far hq]; omega), am]
          exact h.bits q hq, ?_,
        (⟨fun r _ hs hc' => bk.gpr r hs hc', bk.rd, bk.wr, TableFrame.workspace bk.mem⟩ :
          PowersKeep base 56 7368 a b)⟩
      simp only [h26, ↓reduceIte]
      rw [← zsmul_32']
      subst h26
      exact br
    · have h26 : c ≠ 26 := of_decide_eq_false hn
      refine WP.block_nil ⟨hsa, by rw [ag]; exact h.counter, by rw [am]; exact h.d,
        fun q hq => by rw [am]; exact h.bits q hq, by simp only [h26, ↓reduceIte]; rw [am]; exact h.value,
        PowersKeep.refl _ _ _ _⟩
  refine WP.seq (WP.mono_syms hite fun b ⟨hsb, bc, bd, bbits, bv, kb⟩ bsy => ?_)
  -- The chunk's bit index and table.
  refine WP.seq (WP.mono_syms (combIndex_ok b hc bc) fun e ⟨ec, e9, ke⟩ esy => ?_)
  have hse : Scratch e base := hsb.of_keeps ke (by decide)
  have ec' : e.gpr .rbx = BitVec.ofNat 64 c := by rw [ke.1 _ (by decide)]; exact bc
  -- The chunk.
  refine WP.seq (WP.mono_syms (combChunk_ok (S := S) hse hc hS ec' ec (by rw [ke.2.1]; exact bbits))
    fun f ⟨fax, kf⟩ fsy => ?_)
  have kse : PowersKeep base 56 7368 s f :=
    (((kas.trans kb).trans (PowersKeep.of_keeps ke (by decide))).trans (PowersKeep.of_keeps kf (by decide)))
  have te : CombTbl f T := h.tbl.keep hfar kse (by rw [fsy, esy, bsy, asy])
  have hn : nib S (combIdx c) < 32 := Nat.mod_lt _ (by decide)
  have hmag : mag (nib S (combIdx c)) < 17 := by unfold mag; split <;> omega
  have hsf : Scratch f base := hse.of_keeps kf (by decide)
  -- Its sign and magnitude, and the table's entry.
  apply WP.seq
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono_syms (combSign_ok (n := nib S (combIdx c)) hsf hn fax)
    fun f' ⟨f'ax, f'm, f'g, f'r, f'w, f'mem⟩ f'sy => ?_
  have hsf' : Scratch f' base := ⟨(f'g _ (by decide) (by decide)).trans hsf.rdi, f'w ▸ hsf.wr, hsf.nowrap⟩
  have f'c : f'.gpr .rbx = BitVec.ofNat 64 c := by
    rw [f'g _ (by decide) (by decide), kf.1 _ (by decide)]; exact ec'
  have f'9 : f'.gpr .r9 = BitVec.ofNat 64 (combTblIdx c) := by
    rw [f'g _ (by decide) (by decide), kf.1 _ (by decide)]; exact e9
  rw [WP.block_append_iff]
  refine WP.mono_syms (combMagIdx_ok f' f'ax f'9) fun g ⟨g8, gx, kg⟩ gsy => ?_
  have hsg : Scratch g base := hsf'.of_keeps kg (by decide)
  have ksg : PowersKeep base 56 7368 f g :=
    (⟨fun r _ _ hcl => f'g r (by rintro rfl; exact hcl (by decide)) (by rintro rfl; exact hcl (by decide)),
        f'r, f'w, TableFrame.table (f'mem.mono (by simp only [combSignMask]; omega)
          (by simp only [combSignMask]; omega))⟩ : PowersKeep base 56 7368 f f').trans
      (PowersKeep.of_keeps kg (by decide))
  have tg : CombTbl g T := te.keep hfar ksg (by rw [gsy, f'sy])
  rw [WP.block_append_iff]
  refine WP.mono_syms (hsel hsg tg (combTblIdx_lt hc) (by omega) gx g8)
    fun u ⟨uq, uo, ug, ur, uw, usy⟩ _ => ?_
  have hsu : Scratch u base := ⟨by rw [ug _ (by decide) (by decide) (by decide)]; exact hsg.rdi,
    by rw [uw]; exact hsg.wr, hsg.nowrap⟩
  have ku : Keep base g u := ⟨fun r hr => ug r (fun h => hr (by subst h; decide))
      (fun h => hr (by subst h; decide)) (fun h => hr (by subst h; decide)), ur, uw,
    uo.mono (by decide) (by decide)⟩
  have gsm : g.mem.readW (off base combSignMask) 64 = signMask (nib S (combIdx c)) := by
    rw [kg.2.1]; exact f'm
  have usm : u.mem.readW (off base combSignMask) 64 = signMask (nib S (combIdx c)) :=
    (uo.word (d := combSignMask) (Or.inr (by simp only [combSignMask, offset]; omega))
      (by simp only [combSignMask]; omega)).trans gsm
  have tu : CombTbl u T := tg.keep hfar (PowersKeep.of_keep ku) usy
  -- Negated for a negative digit.
  refine WP.mono_syms (combNeg_ok hsu usm) fun u' ⟨u'q, ku', ue', u'o⟩ u'sy => ?_
  have hsu' : Scratch u' base := hsu.of_keep ku'
  have eu : ∀ x : Slot, (x.val < 4 ∨ 16 ≤ x.val) → env u'.mem base x = env b.mem base x := fun x hx => by
    have hux : env u.mem base x = env g.mem base x := by
      simp only [env]
      exact Outside_F uo (by simp only [offset]; omega) (by simp only [offset]; omega)
    rw [ue' x (by omega), hux, kg.2.1, table_env f'mem (by simp only [combSignMask]; omega), kf.2.1, ke.2.1]
  have ud : env u'.mem base 16 = Spec.Ed25519.d := (eu 16 (by decide)).trans bd
  have up : point (env u'.mem base) 0 1 2 3 = point (env b.mem base) 0 1 2 3 := by
    simp only [point, eu 0 (by decide), eu 1 (by decide), eu 2 (by decide), eu 3 (by decide)]
  obtain ⟨q₀, hq₀, hrq₀⟩ := combCached_ok (combTblIdx c) (mag (nib S (combIdx c))) (combTblIdx_lt hc) hmag
  let q := if nib S (combIdx c) < 16 then negPoint q₀ else q₀
  have hsel : (⟨env u.mem base 4, env u.mem base 5, env u.mem base 6, 2⟩ : Spec.Ed25519.Point) = cache q₀ := by
    rw [← hq₀]
    have e4 := uq 0 (by decide); have e5 := uq 1 (by decide); have e6 := uq 2 (by decide)
    simp only [combField] at e4 e5 e6
    have t2 : (combCached (combTblIdx c) (mag (nib S (combIdx c)))).T = 2 := by
      simp only [combCached]; split <;> rfl
    show (⟨Proof.X25519.X86_64.F u.mem base (offset 4), Proof.X25519.X86_64.F u.mem base (offset 5),
      Proof.X25519.X86_64.F u.mem base (offset 6), 2⟩ : Spec.Ed25519.Point) = _
    rw [show offset 5 = offset 4 + 32 * 1 from rfl, show offset 6 = offset 4 + 32 * 2 from rfl,
      show offset 4 = offset 4 + 32 * 0 from rfl, e4, e5, e6, ← t2]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
  have hq : (⟨env u'.mem base 4, env u'.mem base 5, env u'.mem base 6, 2⟩ : Spec.Ed25519.Point) = cache q := by
    have hx := congrArg Spec.Ed25519.Point.X u'q
    have hy := congrArg Spec.Ed25519.Point.Y u'q
    have hz := congrArg Spec.Ed25519.Point.Z u'q
    by_cases hlt : nib S (combIdx c) < 16
    · simp only [hlt, ↓reduceIte, point, negCached] at hx hy hz
      have hs' := congrArg negCached hsel
      rw [negCached_cache] at hs'
      simp only [q, hlt, ↓reduceIte, ← hs', negCached, hx, hy, hz]
    · simp only [hlt, ↓reduceIte, point] at hx hy hz
      simp only [q, hlt, ↓reduceIte, ← hsel, hx, hy, hz]
  have hrq : Rep q ((sdig S (combIdx c) * 1024 ^ (combTblIdx c)) • baseAff) := by
    by_cases hlt : nib S (combIdx c) < 16
    · simp only [hlt, ↓reduceIte, q]
      have e : sdig S (combIdx c) * 1024 ^ (combTblIdx c) =
          -(((mag (nib S (combIdx c)) * 1024 ^ (combTblIdx c) : Nat) : ℤ)) := by
        simp only [sdig, mag, hlt, ↓reduceIte]; push_cast [Nat.cast_sub (by omega : nib S (combIdx c) ≤ 16)]; ring
      rw [e, neg_smul, natCast_zsmul]
      exact hrq₀.neg
    · simp only [hlt, ↓reduceIte, q]
      have e : sdig S (combIdx c) * 1024 ^ (combTblIdx c) =
          (((mag (nib S (combIdx c)) * 1024 ^ (combTblIdx c) : Nat) : ℤ)) := by
        simp only [sdig, mag, hlt, ↓reduceIte]; push_cast [Nat.cast_sub (by omega : 16 ≤ nib S (combIdx c))]; ring
      rw [e, natCast_zsmul]
      exact hrq₀
  -- The addition and the counter.
  refine WP.seq (WP.mono_syms (affBody_ok (fld := fld) hsu' q hq) fun v ⟨kv, vp, vh⟩ vsy => ?_)
  have vc : v.gpr .rbx = BitVec.ofNat 64 c := by
    rw [kv.gpr _ (by decide), ku'.gpr _ (by decide), ug _ (by decide) (by decide) (by decide),
      kg.1 _ (by decide), f'c]
  refine WP.mono_syms (rbxNext52_ok v c hc vc) fun t ⟨tc, tz, kt⟩ tsy => ⟨tz, ?_⟩
  have kbu : PowersKeep base 56 7368 b u' :=
    ((((PowersKeep.of_keeps ke (by decide)).trans (PowersKeep.of_keeps kf (by decide))).trans ksg).trans
      (PowersKeep.of_keep ku)).trans (PowersKeep.of_keep ku')
  have kst : PowersKeep base 56 7368 s t :=
    ((((kas.trans kb).trans kbu).trans (PowersKeep.of_keep kv)).trans (PowersKeep.of_keeps kt (by decide)))
  refine ⟨by omega, hsu'.of_keep kv |>.of_keeps kt (by decide), tc, ?_, fun x hx => ?_, ?_,
    h.keep.trans kst, tu.keep hfar (((PowersKeep.of_keep ku').trans (PowersKeep.of_keep kv)).trans
      (PowersKeep.of_keeps kt (by decide))) (by rw [tsy, vsy, u'sy])⟩
  · rw [kt.2.1, vh 16 (by decide), ud]
  · have hb := bits_far (base := base) hx
    rw [kt.2.1, kv.mem _ (by rw [hb]; omega), ku'.mem _ (by rw [hb]; omega),
      uo _ (by rw [hb]; simp only [offset]; omega), kg.2.1,
      f'mem _ (by rw [hb]; simp only [combSignMask]; omega), kf.2.1, ke.2.1]
    exact bbits x hx
  · rw [kt.2.1, vp, up, ← combIdx_nibS S c hc, add_smul, add_comm]
    exact pointAdd_rep bv hrq

/-! ## The loop -/

/-- `combMultiply` with the selection `sel`, its doublings' calls inlined. -/
theorem combMultiplyWith_ok {sel : List Instr} (hsel : SelOk sel) {s : State} {base T : Addr}
    (hs : Scratch s base) {S : Nat}
    (hS : S < 2 ^ (16 * 16)) (hd : env s.mem base 16 = Spec.Ed25519.d)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2))
    (ht : CombTbl s T) (hfar : TblFar base T) :
    WP isa (combMultiply fld sel (Point64.bodies fld)) s fun t =>
      Rep (point (env t.mem base) 0 1 2 3) (S • baseAff) ∧ PowersKeep base 56 7368 s t := by
  have hS' : S < 2 ^ 256 := hS
  rw [combMultiply]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono_syms (fieldCodeWide_ok (fld := fld) hs (constPointOps combStart)) fun a ⟨ka, va⟩ asy => ?_
  refine WP.mono_syms (rbxSet_ok a 0 (by decide)) fun b ⟨bc, kb⟩ bsy => ?_
  have init : CombInv s base T S 0 b := by
    refine ⟨by decide, (hs.of_keep ka).of_keeps kb (by decide), bc, ?_, fun q hq => ?_, ?_,
      (PowersKeep.of_keep ka).trans (PowersKeep.of_keeps kb (by decide)),
      ht.keep hfar ((PowersKeep.of_keep ka).trans (PowersKeep.of_keeps kb (by decide))) (by rw [bsy, asy])⟩
    · rw [kb.2.1, va, point_ops_high _ (by decide) _ 16 (by decide), hd]
    · rw [kb.2.1, ka.mem _ (by rw [bits_far hq]; omega)]; exact hb q hq
    · rw [kb.2.1, va, constPoint_eval, show combValS S 0 = (combStartVal : ℤ) by simp [combValS, oddSumZ],
        natCast_zsmul]
      exact combStart_ok
  apply WP.loop (fun n t => CombInv s base T S (52 - n) t ∧ 0 < n ∧ n ≤ 52) (n := 52)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine WP.mono (combStep_ok (fld := fld) hsel ht hfar hS' (by omega)) fun u ⟨uz, hu⟩ => ?_
    by_cases hk : k = 0
    · subst hk
      refine Or.inl ⟨by simp only [eval, uz, show 52 - (0 + 1) + 1 = 52 from rfl, decide_true,
        Option.map_some, Bool.not_true], ?_, hu.keep⟩
      have hv := hu.value
      rw [show 52 - (0 + 1) + 1 = 52 from rfl, combValS_sum hS', natCast_zsmul] at hv
      exact hv
    · refine Or.inr ⟨by simp only [eval, uz, show ¬ (52 - (k + 1) + 1 = 52) by omega, decide_false,
        Option.map_some, Bool.not_false], k, by omega, ?_, by omega, by omega⟩
      rw [show 52 - k = 52 - (k + 1) + 1 by omega]; exact hu
  · exact ⟨init, by decide, by decide⟩

theorem combMultiply_ok {s : State} {base T : Addr} (hs : Scratch s base) {S : Nat}
    (hS : S < 2 ^ (16 * 16)) (hd : env s.mem base 16 = Spec.Ed25519.d)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2))
    (ht : CombTbl s T) (hfar : TblFar base T) :
    WP isa (combMultiply fld combSelect (Point64.bodies fld)) s fun t =>
      Rep (point (env t.mem base) 0 1 2 3) (S • baseAff) ∧ PowersKeep base 56 7368 s t :=
  combMultiplyWith_ok combSelect_sel hs hS hd hb ht hfar

end VG.Proof.Ed25519.X86_64
