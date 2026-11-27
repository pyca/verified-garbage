module

import VerifiedGarbage.Proof.Ed25519.Bytes
public import VerifiedGarbage.Impl.Ed25519.AArch64.PublicKey
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Layout
import VerifiedGarbage.Proof.Ed25519.Expanded
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Ed25519.AArch64.Whole.CopyDigest`, which the modules that import this one used -/

section

/-! # The copy of a cached SHA-512 digest to `frame 192` (AArch64)

`copyWords` copies the eight words at `x1`, the digest `D` in a region the body only reads, to
`x15`, `frame 192`, where hashing the seed leaves its digest. Proven once over `Whole.Ctx`, for
both signing's and the public key's layouts. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Whole
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey

variable {E : Addr} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {R W : List Region}

/-- The digest's 64 bytes at `D`: read only, and outside everything the body writes. -/
structure CopySrc (E : Addr) (R W : List Region) (D : Addr) : Prop where
  mem : (⟨D, 64⟩ : Region) ∈ R
  out : ∀ r ∈ W ++ [FR E, CK E], Region.Disjoint ⟨D, 64⟩ r

structure CopyInv (E : Addr) (g : Reg → BitVec 64) (v : VReg → BitVec 128) (m₀ : Mem)
    (R W : List Region) (D : Addr) (n : Nat) (t : State) : Prop where
  ctx : Ctx E g v m₀ R W t
  x1 : t.gpr .x1 = D
  x15 : t.gpr .x15 = E + BitVec.ofNat 64 192
  words : ∀ j < n, t.mem.readW (E + BitVec.ofNat 64 (192 + 8 * j)) 64 =
    m₀.readW (D + BitVec.ofNat 64 (8 * j)) 64

/-- The digest's words, as on entry. -/
theorem CopySrc.word {D : Addr} (hs : CopySrc E R W D) {t : State} (hc : Ctx E g v m₀ R W t)
    {k : Nat} (hk : k < 8) :
    t.mem.readW (D + BitVec.ofNat 64 (8 * k)) 64 = m₀.readW (D + BitVec.ofNat 64 (8 * k)) 64 :=
  hc.frame.readW (r := ⟨D, 64⟩) (Offset.contains_base D (by omega_using [hk]) (by omega_using [hk])) hs.out (by decide)

theorem copyWord_ok {D : Addr} (hs : CopySrc E R W D) {k : Nat} (hk : k < 8) {t : State}
    (hi : CopyInv E g v m₀ R W D k t) :
    WP isa (.block [.ldr .x .x9 .x1 (8 * k), .str .x .x9 .x15 (8 * k)]) t
      (CopyInv E g v m₀ R W D (k + 1)) := by
  have hc := hi.ctx
  have src : InRegions (t.rd ++ t.wr) (t.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [hi.x1, hc.rd]
    exact ⟨_, List.mem_append_left _ hs.mem, Offset.contains_base D (by omega_using [hk]) (by omega_using [hk])⟩
  have dst : InRegions t.wr (E + BitVec.ofNat 64 (192 + 8 * k)) 8 :=
    hc.writable_frame (Offset.contains_base E (by omega_using [hk]) (by omega_using [hk]))
  apply WP.of_runBlock
  rw [runBlock_cons, exec_ldr_x ⟨by omega_using [], by omega_using [hk]⟩ src, runStep_some, runBlock_cons,
    exec_str_x ⟨by omega_using [], by omega_using [hk]⟩ (by
      simpa only [RegUpd.wr_write, RegUpd.gpr_write, reduceCtorEq, ite_false, hi.x15,
        Offset.add_add] using dst),
    runStep_some, runBlock_nil]
  simp only [Option.some.injEq, exists_eq_left', RegUpd.gpr_write, reduceCtorEq, ite_false,
    ite_true, hi.x15, hi.x1, Offset.add_add, RegUpd.mem_write, BitVec.setWidth_eq]
  have hf : Frame [⟨E + BitVec.ofNat 64 (192 + 8 * k), 8⟩] t.mem
      (t.mem.writeW (E + BitVec.ofNat 64 (192 + 8 * k))
        (t.mem.readW (D + BitVec.ofNat 64 (8 * k)) 64)) :=
    (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  refine ⟨hc.of_frame rfl rfl rfl (fun r hr _ => ?_) (fun _ _ => rfl) hf ?_, ?_, ?_, ?_⟩
  · rw [RegUpd.gpr_write_of_ne]
    rintro rfl; simp [preserved] at hr
  · intro r hr
    rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ (by omega_using [hk]))
  · exact (RegUpd.gpr_write_of_ne (s := t) .x (r := .x9) (r' := .x1)
      (t.mem.readW (D + BitVec.ofNat 64 (8 * k)) 64) (by decide)).trans hi.x1
  · exact (RegUpd.gpr_write_of_ne (s := t) .x (r := .x9) (r' := .x15)
      (t.mem.readW (D + BitVec.ofNat 64 (8 * k)) 64) (by decide)).trans hi.x15
  · intro j hj
    by_cases hjk : j = k
    · subst j
      rw [Mem.readW_writeW_self64]
      exact hs.word hc hk
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_using [hjk]) (by omega_using [hk, hj]) (by omega_using [hk])) (by decide)]
      exact hi.words j (by omega_using [hj, hjk])

theorem copyWords_ok {D : Addr} (hs : CopySrc E R W D) :
    ∀ n ≤ 8, ∀ {t : State}, CopyInv E g v m₀ R W D 0 t →
      WP isa (.block ((List.range n).flatMap fun k => [.ldr .x .x9 .x1 (8 * k), .str .x .x9 .x15 (8 * k)]))
        t (CopyInv E g v m₀ R W D n)
  | 0, _, _, h => WP.block_nil h
  | n + 1, hn, _, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (copyWords_ok hs n (by omega_using [hn]) h) fun _ hu => copyWord_ok hs (by omega_using [hn]) hu

/-- After the copy, the 64 bytes at `frame 192` are the digest's. -/
theorem copy_digest {D : Addr} (hs : CopySrc E R W D) {t : State} (h0 : CopyInv E g v m₀ R W D 0 t) :
    WP isa (.block copyWords) t fun u => Ctx E g v m₀ R W u ∧
      Spec.Ed25519.bytesAt u.mem (E + 192) 64 = Spec.Ed25519.bytesAt m₀ D 64 :=
  WP.mono (copyWords_ok hs 8 (Nat.le_refl _) h0) fun u hu => ⟨hu.ctx, by
    change Spec.Sha512.bytesAt u.mem (E + BitVec.ofNat 64 192) 64 = _
    refine Proof.Ed25519.bytesAt_of_words fun k hk => ?_
    rw [Offset.add_add]
    exact hu.words k hk⟩

end VG.Proof.Ed25519.AArch64.Whole

end

end

/-! Merged from `Proof.Ed25519.AArch64.PublicKey.PruneArithmetic`. -/

@[expose] public section

section
namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG

theorem and_sub8 (x k : Nat) (hk : 3 ≤ k) : x &&& (2 ^ k - 8) = 8 * (x / 8 % 2 ^ (k - 3)) := by
  have e : 2 ^ k - 8 = 2 ^ 3 * (2 ^ (k - 3) - 1) := by
    rw [Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, Nat.add_sub_cancel' hk]
  rw [e, show (8 : Nat) = 2 ^ 3 from rfl]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul, Nat.testBit_mod_two_pow,
    Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
  by_cases h : 3 ≤ i
  · simp only [h, decide_true, Bool.true_and, Nat.sub_add_cancel h]
    cases x.testBit i <;> simp
  · simp [h]

theorem or_two_pow {y k : Nat} (h : y < 2 ^ k) : y ||| 2 ^ k = 2 ^ k + y := by
  have := Nat.two_pow_add_eq_or_of_lt h 1
  rw [Nat.mul_one] at this
  rw [this, Nat.or_comm]

/-- The pruning of `Spec.Ed25519.prune`, on four 64-bit words. -/
theorem prune_words (d₀ d₁ d₂ d₃ : BitVec 64) :
    ((d₀.toNat + 2 ^ 64 * d₁.toNat + 2 ^ 128 * d₂.toNat + 2 ^ 192 * d₃.toNat) &&& (2 ^ 254 - 8)) |||
        2 ^ 254 =
      (d₀ &&& BitVec.ofNat 64 (2 ^ 64 - 8)).toNat + 2 ^ 64 * d₁.toNat + 2 ^ 128 * d₂.toNat +
        2 ^ 192 * ((d₃ &&& BitVec.ofNat 64 (2 ^ 62 - 1)) ||| BitVec.ofNat 64 (2 ^ 62)).toNat := by
  have h₀ := d₀.isLt; have h₁ := d₁.isLt; have h₂ := d₂.isLt; have h₃ := d₃.isLt
  have c₁ : (2 ^ 64 - 8) % 2 ^ 64 = 2 ^ 64 - 8 := by decide
  have c₂ : (2 ^ 62 - 1) % 2 ^ 64 = 2 ^ 62 - 1 := by decide
  have c₃ : (2 ^ 62) % 2 ^ 64 = 2 ^ 62 := by decide
  rw [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, c₁, c₂, c₃, and_sub8 _ 64 (by omega_using []), and_sub8 _ 254 (by omega_using []),
    Nat.and_two_pow_sub_one_eq_mod, or_two_pow (Nat.mod_lt _ (by omega_using [])), or_two_pow (by omega_using [])]
  simp only [show (2 : Nat) ^ (254 - 3) = 2 ^ 251 from rfl, show (2 : Nat) ^ (64 - 3) = 2 ^ 61 from rfl]
  omega_using []

end VG.Proof.Ed25519.AArch64.PublicKey
end

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey

def pruneValue (k : Nat) (x : BitVec 64) : BitVec 64 :=
  if k = 0 then x &&& BitVec.ofNat 64 (2 ^ 64 - 8)
  else if k = 3 then (x &&& BitVec.ofNat 64 (2 ^ 62 - 1)) ||| BitVec.ofNat 64 (2 ^ 62)
  else x

structure Step (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  v : t.v = s.v
  regs : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x15 → t.gpr r = s.gpr r

theorem Step.trans {s t u : State} (h : Step s t) (h' : Step t u) : Step s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp, h'.v.trans h.v,
    fun r h9 h10 h15 => (h'.regs r h9 h10 h15).trans (h.regs r h9 h10 h15)⟩

theorem pruneWord_ok {s : State} {k : Nat} (hk : k < 4)
    (hr : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (192 + 8 * k)) 8)
    (hw : InRegions s.wr (s.sp + BitVec.ofNat 64 (32 + 8 * k)) 8) :
    WP isa (.block (pruneWord k)) s fun t => Step s t ∧
      t.mem = s.mem.writeW (s.sp + BitVec.ofNat 64 (32 + 8 * k))
        (pruneValue k (s.mem.readW (s.sp + BitVec.ofNat 64 (192 + 8 * k)) 64)) := by
  have ho : (192 + 8 * k) % 8 = 0 ∧ 192 + 8 * k < 32768 := by omega_using [hk]
  have hs : 32 + 8 * k < 4096 := by omega_using [hk]
  apply WP.of_runBlock
  by_cases h0 : k = 0
  · subst k
    simp only [pruneWord, pruneLow, pruneValue, ite_true, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, State.load, Size.bits, Size.bytes,
      State.read, State.store, addr, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
      RegUpd.wr_write, RegUpd.sp_write, RegUpd.v_write, BitVec.setWidth_eq,
      Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
      ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, hr, hw,
      BitVec.shiftLeft_zero, BitVec.add_zero, Mem.readW, Mem.writeW, Option.some.injEq,
      exists_eq_left']
    refine ⟨⟨rfl, rfl, rfl, rfl, ?_⟩, ?_⟩
    · intro r h9 h10 h15
      simp only [RegUpd.gpr_write, h9, h10, h15, ite_false]
    · rfl
  · by_cases h3 : k = 3
    · subst k
      simp only [pruneWord, pruneHigh, pruneValue, h0, ite_true, ite_false,
        List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
        exec, State.load, Size.bits, Size.bytes, State.read, State.store, addr,
        RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
        RegUpd.sp_write, RegUpd.v_write, BitVec.setWidth_eq,
        Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
        ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, hr, hw,
        BitVec.shiftLeft_zero, BitVec.add_zero, Mem.readW, Mem.writeW, Option.some.injEq,
        exists_eq_left']
      refine ⟨⟨rfl, rfl, rfl, rfl, ?_⟩, ?_⟩
      · intro r h9 h10 h15
        simp only [RegUpd.gpr_write, h9, h10, h15, ite_false]
      · rfl
    · simp only [pruneWord, pruneValue, h0, h3, ite_false, List.cons_append, List.nil_append,
        runBlock_cons, runStep_some, runBlock_nil, exec, State.load, Size.bits, Size.bytes,
        State.read, State.store, addr, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
        RegUpd.wr_write, RegUpd.sp_write, RegUpd.v_write, BitVec.setWidth_eq,
        ho, hs, and_self, ite_true, ite_false, reduceCtorEq, Option.map_some,
        Option.bind_some, hr, hw, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, BitVec.add_zero,
        Mem.readW, Mem.writeW, Option.some.injEq, exists_eq_left']
      refine ⟨⟨rfl, rfl, rfl, rfl, ?_⟩, True.intro⟩
      intro r h9 _ h15
      simp only [RegUpd.gpr_write, h9, h15, ite_false]

theorem Step.refl (s : State) : Step s s := ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩

structure PruneInv (s : State) (n : Nat) (t : State) : Prop where
  step : Step s t
  frame : Frame [⟨s.sp + 32, 32⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (s.sp + BitVec.ofNat 64 (32 + 8 * j)) 64 =
    pruneValue j (s.mem.readW (s.sp + BitVec.ofNat 64 (192 + 8 * j)) 64)

theorem prunePrefix_ok {s : State} (hw : (⟨s.sp, 256⟩ : Region) ∈ s.wr) :
    ∀ n ≤ 4, WP isa (.block ((List.range n).flatMap pruneWord)) s (PruneInv s n)
  | 0, _ => WP.block_nil ⟨.refl s, Frame.refl _ _, fun _ h => by omega⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (prunePrefix_ok hw n (by omega_using [hn])) fun u hu => ?_
    have ur : InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (192 + 8 * n)) 8 := by
      rw [hu.step.sp, hu.step.wr]
      exact ⟨_, List.mem_append_right _ hw, Offset.contains_base _ (by omega_using [hn]) (by omega_using [hn])⟩
    have uw : InRegions u.wr (u.sp + BitVec.ofNat 64 (32 + 8 * n)) 8 := by
      rw [hu.step.sp, hu.step.wr]
      exact ⟨_, hw, Offset.contains_base _ (by omega_using [hn]) (by omega_using [hn])⟩
    refine WP.mono (pruneWord_ok (by omega_using [hn]) ur uw) fun t ⟨kt, mt⟩ => ?_
    rw [hu.step.sp] at mt
    have same : u.mem.readW (s.sp + BitVec.ofNat 64 (192 + 8 * n)) 64 =
        s.mem.readW (s.sp + BitVec.ofNat 64 (192 + 8 * n)) 64 := by
      apply hu.frame.readW (Region.contains_self _ _) _ (by decide)
      simp only [List.mem_singleton]
      rintro r rfl
      exact Offset.disjoint _ (e := 32) (k := 32) (by omega_using []) (by omega_using [hn]) (by decide)
    rw [same] at mt
    refine ⟨hu.step.trans kt, ?_, fun j hj => ?_⟩
    · rw [mt]
      exact hu.frame.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (e := 32) (k := 32) (by omega_using []) (by omega_using [hn]) (by decide))
    · rw [mt]
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep ?_ (by decide)]
        · exact hu.words j (by omega_using [hj, hjn])
        · exact Offset.sep _ (by omega_using [hjn]) (by omega_using [hn, hj]) (by omega_using [hn])

theorem decode_words (m : Mem) (p : Addr) :
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32) =
      (m.readW p 64).toNat + 2 ^ 64 * (m.readW (p + 8) 64).toNat +
      2 ^ 128 * (m.readW (p + 16) 64).toNat + 2 ^ 192 * (m.readW (p + 24) 64).toNat := by
  rw [Proof.Ed25519.decodeLE_eq]
  exact Proof.X25519.leNum_bytesAt_words64 m p

/-- Prune the first half of the seed digest into its separate scalar buffer. -/
theorem prune_ok {s : State} (hw : (⟨s.sp, 256⟩ : Region) ∈ s.wr)
    {digest : List Byte} (hh : Spec.Sha512.bytesAt s.mem (s.sp + 192) 64 = digest) :
    WP isa (.block prune) s fun t => Step s t ∧
      Frame [⟨s.sp + 32, 32⟩] s.mem t.mem ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem (s.sp + 32) 32) =
        Spec.Ed25519.prune digest := by
  refine WP.mono (prunePrefix_ok hw 4 (by decide)) fun t ht => ⟨ht.step, ht.frame, ?_⟩
  have take : (Spec.Sha512.bytesAt s.mem (s.sp + 192) 64).take 32 =
      Spec.Ed25519.bytesAt s.mem (s.sp + 192) 32 := by
    simp [Spec.Sha512.bytesAt, Spec.Ed25519.bytesAt, ← List.map_take, List.take_range]
  rw [Spec.Ed25519.prune, ← hh, take, decode_words, decode_words]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have w0 := ht.words 0 (by decide)
  have w1 := ht.words 1 (by decide)
  have w2 := ht.words 2 (by decide)
  have w3 := ht.words 3 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceEqDiff, pruneValue, ↓reduceIte] at w0 w1 w2 w3
  change t.mem.readW (s.sp + (32 : BitVec 64)) 64 = _ at w0
  rw [w0, w1, w2, w3]
  exact (prune_words _ _ _ _).symm

end VG.Proof.Ed25519.AArch64.PublicKey
