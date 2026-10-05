import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Impl.Ed25519.Arm.PublicKey
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.Prune`. -/
section

/-! Merged from `Proof.Ed25519.Arm.PublicKey.PruneArithmetic`. -/
section
namespace VG.Proof.Ed25519.Arm.PublicKey
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

theorem prune_words (d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 32) :
    ((d0.toNat + 2 ^ 32 * d1.toNat + 2 ^ 64 * d2.toNat + 2 ^ 96 * d3.toNat + 2 ^ 128 * d4.toNat + 2 ^ 160 * d5.toNat + 2 ^ 192 * d6.toNat + 2 ^ 224 * d7.toNat) &&& (2 ^ 254 - 8)) ||| 2 ^ 254 =
      (d0 &&& BitVec.ofNat 32 (2 ^ 32 - 8)).toNat + 2 ^ 32 * d1.toNat + 2 ^ 64 * d2.toNat + 2 ^ 96 * d3.toNat + 2 ^ 128 * d4.toNat + 2 ^ 160 * d5.toNat + 2 ^ 192 * d6.toNat + 2 ^ 224 * ((d7 &&& BitVec.ofNat 32 (2 ^ 30 - 1)) ||| BitVec.ofNat 32 (2 ^ 30)).toNat := by
  have h0 := d0.isLt; have h1 := d1.isLt; have h2 := d2.isLt; have h3 := d3.isLt; have h4 := d4.isLt; have h5 := d5.isLt; have h6 := d6.isLt; have h7 := d7.isLt
  have c₁ : (2 ^ 32 - 8) % 2 ^ 32 = 2 ^ 32 - 8 := by decide
  have c₂ : (2 ^ 30 - 1) % 2 ^ 32 = 2 ^ 30 - 1 := by decide
  have c₃ : (2 ^ 30) % 2 ^ 32 = 2 ^ 30 := by decide
  rw [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, c₁, c₂, c₃, VG.Proof.Ed25519.Arm.PublicKey.and_sub8 _ 32 (by omega), VG.Proof.Ed25519.Arm.PublicKey.and_sub8 _ 254 (by omega),
    Nat.and_two_pow_sub_one_eq_mod, VG.Proof.Ed25519.Arm.PublicKey.or_two_pow (Nat.mod_lt _ (by omega)), VG.Proof.Ed25519.Arm.PublicKey.or_two_pow (by omega)]
  simp only [show (2 : Nat) ^ (254 - 3) = 2 ^ 251 from rfl, show (2 : Nat) ^ (32 - 3) = 2 ^ 29 from rfl]
  omega

end VG.Proof.Ed25519.Arm.PublicKey
end

namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.PublicKey

def addr (E : BitVec 32) (d : Nat) : Addr := State.addr (E + BitVec.ofNat 32 d)
theorem addr_eq {E : BitVec 32} {d : Nat} (h : E.toNat + d < 2 ^ 32) :
    VG.Proof.Ed25519.Arm.PublicKey.addr E d = E.setWidth 64 + BitVec.ofNat 64 d := Arm.addr_add h

def pruneValue (k : Nat) (x : BitVec 32) : BitVec 32 :=
  if k = 0 then x &&& 0xfffffff8
  else if k = 7 then (x &&& 0x3fffffff) ||| 0x40000000 else x

structure Step (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  regs : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r12 → t.gpr r = s.gpr r

theorem Step.refl (s : State) : VG.Proof.Ed25519.Arm.PublicKey.Step s s := ⟨rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
theorem Step.trans {s t u : State} (a : VG.Proof.Ed25519.Arm.PublicKey.Step s t) (b : VG.Proof.Ed25519.Arm.PublicKey.Step t u) : VG.Proof.Ed25519.Arm.PublicKey.Step s u :=
  ⟨b.rd.trans a.rd, b.wr.trans a.wr, b.sp.trans a.sp,
    fun r h0 h1 h12 => (b.regs r h0 h1 h12).trans (a.regs r h0 h1 h12)⟩

theorem pruneWord_ok {s : State} {E : BitVec 32} {k : Nat} (he : s.sp = E) (hk : k < 8)
    (hr : InRegions (s.rd ++ s.wr) (VG.Proof.Ed25519.Arm.PublicKey.addr E (184 + 4 * k)) 4)
    (hw : InRegions s.wr (VG.Proof.Ed25519.Arm.PublicKey.addr E (24 + 4 * k)) 4) :
    WP isa (.block (pruneWord k)) s fun t => VG.Proof.Ed25519.Arm.PublicKey.Step s t ∧
      t.mem = s.mem.writeW (VG.Proof.Ed25519.Arm.PublicKey.addr E (24 + 4 * k))
        (VG.Proof.Ed25519.Arm.PublicKey.pruneValue k (s.mem.readW (VG.Proof.Ed25519.Arm.PublicKey.addr E (184 + 4 * k)) 32)) := by
  simp only [VG.Proof.Ed25519.Arm.PublicKey.addr] at hr hw ⊢
  have h184 : 184 + 4 * k < 4096 := by omega
  have h4 : 4 * k < 4096 := by omega
  have ha : BitVec.ofNat 32 24 + BitVec.ofNat 32 (4 * k) = BitVec.ofNat 32 (24 + 4 * k) :=
    (BitVec.ofNat_add 24 (4 * k)).symm
  by_cases h0 : k = 0
  · subst k
    apply WP.of_runBlock
    simp only [pruneWord, pruneLow, VG.Proof.Ed25519.Arm.PublicKey.pruneValue, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, State.store32,
      RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
      RegUpd.sp_setReg, reduceCtorEq, he, hr, hw, Op2.eval,
      Nat.reduceMul, Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false,
      Option.map_some, Option.some.injEq, exists_eq_left', BitVec.add_zero]
    refine ⟨⟨rfl, rfl, he.symm, ?_⟩, ?_⟩
    · intro r hn0 hn1 hn12
      simp only [RegUpd.gpr_setReg, hn0, hn1, hn12, ite_false]
    · rfl
  · by_cases h7 : k = 7
    · subst k
      apply WP.of_runBlock
      simp only [pruneWord, pruneHigh, VG.Proof.Ed25519.Arm.PublicKey.pruneValue, List.cons_append, List.nil_append,
        runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, State.store32,
        RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
        RegUpd.sp_setReg, reduceCtorEq, he, hr, hw, Op2.eval,
        Nat.reduceMul, Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false,
        Option.map_some, Option.some.injEq, exists_eq_left', BitVec.add_assoc, BitVec.reduceAdd]
      refine ⟨⟨rfl, rfl, he.symm, ?_⟩, ?_⟩
      · intro r hn0 hn1 hn12
        simp only [RegUpd.gpr_setReg, hn0, hn1, hn12, ite_false]
      · rfl
    · apply WP.of_runBlock
      simp only [pruneWord, VG.Proof.Ed25519.Arm.PublicKey.pruneValue, h0, h7, ite_false, List.cons_append, List.nil_append,
        runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, State.store32,
        RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
        RegUpd.sp_setReg, reduceCtorEq, he, h184, h4, Nat.reduceLT, ite_true,
        hr, hw, Option.map_some, Option.some.injEq, exists_eq_left', BitVec.add_assoc, ha]
      refine ⟨⟨rfl, rfl, he.symm, ?_⟩, True.intro⟩
      intro r hn0 _ hn12
      simp only [RegUpd.gpr_setReg, hn0, hn12, ite_false]

/-- The frame bounds supply readable and writable words. -/
theorem frame_word {s : State} {E : BitVec 32} (hf : E.toNat + 248 ≤ 2 ^ 32)
    (hw : (⟨E.setWidth 64, 248⟩ : Region) ∈ s.wr) {d : Nat} (hd : d + 4 ≤ 248) :
    InRegions s.wr (VG.Proof.Ed25519.Arm.PublicKey.addr E d) 4 := by
  refine ⟨_, hw, ?_⟩
  rw [VG.Proof.Ed25519.Arm.PublicKey.addr_eq (by omega_using [hf, hd])]
  exact Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd])

structure PruneInv (E : BitVec 32) (s : State) (n : Nat) (t : State) : Prop where
  step : VG.Proof.Ed25519.Arm.PublicKey.Step s t
  frame : Frame [⟨E.setWidth 64 + BitVec.ofNat 64 24, 32⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (VG.Proof.Ed25519.Arm.PublicKey.addr E (24 + 4 * j)) 32 =
    VG.Proof.Ed25519.Arm.PublicKey.pruneValue j (s.mem.readW (VG.Proof.Ed25519.Arm.PublicKey.addr E (184 + 4 * j)) 32)

theorem prunePrefix_ok {s : State} {E : BitVec 32} (he : s.sp = E)
    (hf : E.toNat + 248 ≤ 2 ^ 32) (hw : (⟨E.setWidth 64, 248⟩ : Region) ∈ s.wr) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap pruneWord)) s (VG.Proof.Ed25519.Arm.PublicKey.PruneInv E s n)
  | 0, _ => WP.block_nil ⟨Step.refl s, Frame.refl _ _, fun _ h => by omega_using [h]⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed25519.Arm.PublicKey.prunePrefix_ok he hf hw n (by omega_using [hn])) fun u hu => ?_
    have ur : InRegions (u.rd ++ u.wr) (VG.Proof.Ed25519.Arm.PublicKey.addr E (184 + 4 * n)) 4 := by
      obtain ⟨r, hr, hc⟩ := VG.Proof.Ed25519.Arm.PublicKey.frame_word hf (hu.step.wr ▸ hw) (d := 184 + 4 * n) (by omega_using [hn])
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    have uw := VG.Proof.Ed25519.Arm.PublicKey.frame_word hf (hu.step.wr ▸ hw) (d := 24 + 4 * n) (by omega_using [hn])
    refine WP.mono (VG.Proof.Ed25519.Arm.PublicKey.pruneWord_ok (hu.step.sp.trans he) (by omega_using [hn]) ur uw) fun t ⟨kt, mt⟩ => ?_
    have a192 : VG.Proof.Ed25519.Arm.PublicKey.addr E (184 + 4 * n) = E.setWidth 64 + BitVec.ofNat 64 (184 + 4 * n) :=
      VG.Proof.Ed25519.Arm.PublicKey.addr_eq (by omega_using [hf, hn])
    have a32 : VG.Proof.Ed25519.Arm.PublicKey.addr E (24 + 4 * n) = E.setWidth 64 + BitVec.ofNat 64 (24 + 4 * n) :=
      VG.Proof.Ed25519.Arm.PublicKey.addr_eq (by omega_using [hf, hn])
    have same : u.mem.readW (VG.Proof.Ed25519.Arm.PublicKey.addr E (184 + 4 * n)) 32 = s.mem.readW (VG.Proof.Ed25519.Arm.PublicKey.addr E (184 + 4 * n)) 32 := by
      rw [a192]
      apply hu.frame.readW (Region.contains_self _ _) _ (by decide)
      simp only [List.mem_singleton]
      rintro r rfl
      exact Offset.disjoint _ (by omega_using [hn]) (by omega_using [hn]) (by omega_using [hn])
    rw [same] at mt
    refine ⟨hu.step.trans kt, ?_, fun j hj => ?_⟩
    · rw [mt, a32]
      exact hu.frame.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_using []) (by omega_using [hn]) (by decide))
    · rw [mt]
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (a := VG.Proof.Ed25519.Arm.PublicKey.addr E (24 + 4 * j)) (b := VG.Proof.Ed25519.Arm.PublicKey.addr E (24 + 4 * n)) ?_ (by decide)]
        · exact hu.words j (by omega_using [hj, hjn])
        · rw [a32, VG.Proof.Ed25519.Arm.PublicKey.addr_eq (by omega_using [hf, hj, hn])]
          exact Offset.sep _ (by omega_using [hj, hjn]) (by omega_using [hj, hn]) (by omega_using [hn])

theorem decode_words (m : Mem) (p : Addr) :
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32) =
      (m.readW p 32).toNat + 2 ^ 32 * (m.readW (p + 4) 32).toNat +
      2 ^ 64 * (m.readW (p + 8) 32).toNat + 2 ^ 96 * (m.readW (p + 12) 32).toNat +
      2 ^ 128 * (m.readW (p + 16) 32).toNat + 2 ^ 160 * (m.readW (p + 20) 32).toNat +
      2 ^ 192 * (m.readW (p + 24) 32).toNat + 2 ^ 224 * (m.readW (p + 28) 32).toNat := by
  rw [Proof.Ed25519.decodeLE_eq]
  exact Proof.X25519.leNum_bytesAt_words32 m p

/-- Prune the first half of a SHA-512 digest into the separate scalar buffer. -/
theorem prune_ok {s : State} {E : BitVec 32} (he : s.sp = E)
    (hf : E.toNat + 248 ≤ 2 ^ 32) (hw : (⟨E.setWidth 64, 248⟩ : Region) ∈ s.wr)
    {digest : List Byte} (hh : Spec.Sha512.bytesAt s.mem (E.setWidth 64 + 184) 64 = digest) :
    WP isa (.block prune) s fun t => VG.Proof.Ed25519.Arm.PublicKey.Step s t ∧
      Frame [⟨E.setWidth 64 + 24, 32⟩] s.mem t.mem ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem (E.setWidth 64 + 24) 32) =
        Spec.Ed25519.prune digest := by
  refine WP.mono (VG.Proof.Ed25519.Arm.PublicKey.prunePrefix_ok he hf hw 8 (by decide)) fun t ht => ⟨ht.step, ht.frame, ?_⟩
  have words : ∀ j < 8, t.mem.readW (E.setWidth 64 + BitVec.ofNat 64 (24 + 4 * j)) 32 =
      VG.Proof.Ed25519.Arm.PublicKey.pruneValue j (s.mem.readW (E.setWidth 64 + BitVec.ofNat 64 (184 + 4 * j)) 32) := by
    intro j hj
    have h := ht.words j hj
    rw [VG.Proof.Ed25519.Arm.PublicKey.addr_eq (by omega_using [hf, hj]), VG.Proof.Ed25519.Arm.PublicKey.addr_eq (by omega_using [hf, hj])] at h
    exact h
  have take : (Spec.Sha512.bytesAt s.mem (E.setWidth 64 + 184) 64).take 32 =
      Spec.Ed25519.bytesAt s.mem (E.setWidth 64 + 184) 32 := by
    simp [Spec.Sha512.bytesAt, Spec.Ed25519.bytesAt, ← List.map_take, List.take_range]
  rw [Spec.Ed25519.prune, ← hh, take, VG.Proof.Ed25519.Arm.PublicKey.decode_words, VG.Proof.Ed25519.Arm.PublicKey.decode_words]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have w0 := words 0 (by decide)
  have w1 := words 1 (by decide)
  have w2 := words 2 (by decide)
  have w3 := words 3 (by decide)
  have w4 := words 4 (by decide)
  have w5 := words 5 (by decide)
  have w6 := words 6 (by decide)
  have w7 := words 7 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceEqDiff, VG.Proof.Ed25519.Arm.PublicKey.pruneValue, ↓reduceIte] at w0 w1 w2 w3 w4 w5 w6 w7
  change t.mem.readW (E.setWidth 64 + (24 : BitVec 64)) 32 = _ at w0
  rw [w0, w1, w2, w3, w4, w5, w6, w7]
  exact (VG.Proof.Ed25519.Arm.PublicKey.prune_words _ _ _ _ _ _ _ _).symm

end VG.Proof.Ed25519.Arm.PublicKey

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.PruneCT`. -/
section

namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.PublicKey

theorem pruneWord_ct (k : Nat) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (pruneWord k)) (fun a b => a.sp = b.sp) := by
  apply Whole.block_append_ct (Whole.block_append_ct
    (Whole.step_sp_ct (fun _ _ h => by simp only [addrs, h]) Whole.block_nil_ct) ?_)
    (Whole.frame_store_ct _ _ _)
  split
  · exact Whole.quiet_block_ct _ (by simp [pruneLow, addrs])
  · split
    · exact Whole.quiet_block_ct _ (by simp [pruneHigh, addrs])
    · exact Whole.block_nil_ct

theorem prune_sp_ct : RelCT isa (fun a b => a.sp = b.sp) (.block prune) (fun a b => a.sp = b.sp) :=
  Whole.flatMap_sp_ct _ _ (fun k _ => VG.Proof.Ed25519.Arm.PublicKey.pruneWord_ct k)

end VG.Proof.Ed25519.Arm.PublicKey

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.Verified`. -/
section

/-! Merged from `Proof.Ed25519.Arm.PublicKey.Correct`. -/
section
/-! Merged from `Proof.Ed25519.Arm.PublicKey.Layout`. -/
section
namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

structure Lay where
  out : BitVec 32
  seed : BitVec 32
  scr : BitVec 32
  E : BitVec 32

namespace Lay
variable (L : VG.Proof.Ed25519.Arm.PublicKey.Lay)
abbrev OUT : Region := ⟨State.addr L.out, 32⟩
abbrev SEED : Region := ⟨State.addr L.seed, 32⟩
abbrev SCR : Region := ⟨State.addr L.scr, 8192⟩
abbrev ARGS : Region := Whole.ARGS L.E
abbrev FR : Region := Whole.FR L.E
abbrev STK : Region := ⟨State.addr L.E, 280⟩
def inputs : List Region := [L.SEED, L.ARGS]
def outputs : List Region := [L.OUT, L.SCR]
def value (j : Nat) : BitVec 32 := match j with | 0 => L.out | 1 => L.seed | _ => L.scr
structure Ok : Prop where
  top : L.E.toNat + 272 ≤ 2 ^ 32
  os : L.OUT.Disjoint L.SEED
  oc : L.OUT.Disjoint L.SCR
  sc : L.SEED.Disjoint L.SCR
  ko : L.STK.Disjoint L.OUT
  ks : L.STK.Disjoint L.SEED
  kc : L.STK.Disjoint L.SCR
  no : L.out.toNat + 32 ≤ 2 ^ 32
  ns : L.seed.toNat + 32 ≤ 2 ^ 32
  nc : L.scr.toNat + 8192 ≤ 2 ^ 32
end Lay

abbrev Ctx (L : VG.Proof.Ed25519.Arm.PublicKey.Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) :=
  Whole.Ctx L.E g m₀ L.inputs L.outputs t

def Arguments (L : VG.Proof.Ed25519.Arm.PublicKey.Lay) (m : Mem) : Prop :=
  ∀ j < 3, m.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 = L.value j

def argValue (L : VG.Proof.Ed25519.Arm.PublicKey.Lay) : Value → BitVec 32
  | .const n => BitVec.ofNat 32 n
  | .frame d => L.E + BitVec.ofNat 32 d
  | .caller j d => L.value j + BitVec.ofNat 32 d

variable {L : VG.Proof.Ed25519.Arm.PublicKey.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem frame_sub (L : VG.Proof.Ed25519.Arm.PublicKey.Lay) : Region.Sub L.FR L.STK := Region.sub_prefix (by decide : 248 ≤ 280)
theorem args_sub (L : VG.Proof.Ed25519.Arm.PublicKey.Lay) : Region.Sub L.ARGS L.STK := Offset.sub_base _ (by decide : 248 + 24 ≤ 280)

theorem Ctx.seed_bytes (hc : VG.Proof.Ed25519.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) :
    Spec.Ed25519.bytesAt t.mem (State.addr L.seed) 32 = Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32 := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hc.frame.bytes (R := L.SEED) ?_ (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.os.symm
  · exact hL.sc
  · exact (hL.ks.sub_left (VG.Proof.Ed25519.Arm.PublicKey.frame_sub L)).symm

theorem Ctx.arg_word (hc : VG.Proof.Ed25519.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) {j : Nat} (hj : j < 3) :
    t.mem.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 =
      m₀.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 := by
  refine hc.frame.readW (r := L.ARGS)
    (Offset.contains _ (e := 248) (k := 24) (by omega) (by omega) (by decide)) ?_ (by decide)
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.ko.sub_left (VG.Proof.Ed25519.Arm.PublicKey.args_sub L)
  · exact hL.kc.sub_left (VG.Proof.Ed25519.Arm.PublicKey.args_sub L)
  · exact Offset.disjoint_base _ (by decide : 248 ≤ 248) (by decide : 248 + 24 ≤ 2 ^ 64)

theorem value_eq (hc : VG.Proof.Ed25519.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.PublicKey.Arguments L m₀)
    (v : Value) (hi : ∀ j d, v = .caller j d → j < 3) : Whole.value L.E t.mem v = VG.Proof.Ed25519.Arm.PublicKey.argValue L v := by
  cases v with
  | const => rfl
  | frame => rfl
  | caller j d =>
    simp only [Whole.value, VG.Proof.Ed25519.Arm.PublicKey.argValue]
    rw [hc.arg_word hL (hi j d rfl), ha j (hi j d rfl)]

theorem setup_ok (hc : VG.Proof.Ed25519.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.PublicKey.Arguments L m₀)
    {args : List (Reg × Value)} {stk : List Value} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3)
    (hr : ∀ p ∈ args, p.1 ∉ preserved)
    (hs : stk.length ≤ 6) (hvs : ∀ v ∈ stk, Whole.valid v)
    (his : ∀ v ∈ stk, ∀ j d, v = .caller j d → j < 3) :
    WP isa (.block (setup args stk)) t fun u => VG.Proof.Ed25519.Arm.PublicKey.Ctx L g m₀ u ∧
      Frame [⟨State.addr L.E, 24⟩] t.mem u.mem ∧
      (∀ p ∈ args, u.gpr p.1 = VG.Proof.Ed25519.Arm.PublicKey.argValue L p.2) ∧
      (∀ j (hj : j < stk.length), stackArg u j = VG.Proof.Ed25519.Arm.PublicKey.argValue L (stk[j]'hj)) := by
  refine WP.mono (hc.setup hL.top hn hv hs hvs (by simp [Lay.inputs]) hr)
    fun u ⟨hu, hm, hregs, hstk⟩ => ⟨hu, hm, ?_, ?_⟩
  · intro p hp
    rw [hregs p hp, VG.Proof.Ed25519.Arm.PublicKey.value_eq hc hL ha _ (hi p hp)]
  · intro j hj
    rw [hstk j hj, VG.Proof.Ed25519.Arm.PublicKey.value_eq hc hL ha _ (his _ (List.getElem_mem hj))]

end VG.Proof.Ed25519.Arm.PublicKey
end

/-! Merged from `Proof.Ed25519.Arm.PublicKey.Hash`. -/
section
namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.PublicKey
open VG.Impl.Ed25519.Arm.Whole (callWith)

variable {L : VG.Proof.Ed25519.Arm.PublicKey.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem setup_repr (hL : L.Ok) {u : State} (hf : Frame [⟨State.addr L.E, 24⟩] t.mem u.mem)
    {msg : List Byte} (hh : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr) msg) :
    Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem (State.addr L.scr) msg := by
  refine Proof.Sha512.Stream.repr_congr (mem := t.mem) ?_ hh
  intro i hi
  refine hf.bytes (R := Whole.SHA L.scr) ?_ (by change 192 ≤ 2 ^ 64; decide) hi
  rintro r hr
  rw [List.mem_singleton.mp hr]
  exact ((hL.kc.sub_left (Region.sub_prefix (by decide : 24 ≤ 280))).sub_right (Whole.sha_sub L.scr)).symm

theorem init_step (hc : VG.Proof.Ed25519.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.PublicKey.Arguments L m₀) :
    WP isa (callWith initArgs Spec.Sha512.init512Api.name (Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512)) t
      fun u => VG.Proof.Ed25519.Arm.PublicKey.Ctx L g m₀ u ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem (State.addr L.scr) [] := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.PublicKey.setup_ok hc hL ha (args := [(.r0, .caller 2 0)]) (stk := [])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])
    (by decide) (by simp) (by simp)) fun u ⟨hu, _, hs, _⟩ => ?_)
  have h0 := hs (.r0, .caller 2 0) (by simp)
  simp only [VG.Proof.Ed25519.Arm.PublicKey.argValue, Lay.value, BitVec.add_zero] at h0
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact WP.mono (Whole.init_call hu (Whole.init_pre h0 hL.nc) (Whole.covers_writes hw) hw h0)
    fun v ⟨hv, _, hh⟩ => ⟨hv, hh⟩

theorem update_covers (L : VG.Proof.Ed25519.Arm.PublicKey.Lay) : Covers (Whole.updateRd L.E L.seed 32 ++ Whole.hashWr L.scr)
    (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨L.SEED, by simp [Lay.inputs], 0, (BitVec.add_zero _).symm, by change 0 + (32#32).toNat ≤ 32; decide⟩
  · exact ⟨L.FR, by simp, 0, (BitVec.add_zero _).symm, by change 0 + 12 ≤ 248; decide⟩
  · exact ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by change 0 + 192 ≤ 8192; decide⟩
  · exact ⟨L.SCR, by simp [Lay.outputs], 192, rfl, by change 192 + 272 ≤ 8192; decide⟩

theorem update_step (hc : VG.Proof.Ed25519.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.PublicKey.Arguments L m₀)
    (hh : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr) []) :
    WP isa (callWith updateArgs Spec.Sha512.updateScratchApi.name Impl.Sha512.Arm.Stream.update) t fun u =>
      VG.Proof.Ed25519.Arm.PublicKey.Ctx L g m₀ u ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem (State.addr L.scr)
        (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.PublicKey.setup_ok hc hL ha
    (args := [(.r0, .caller 2 0), (.r2, .const 0), (.r3, .const 0)])
    (stk := [.caller 1 0, .const 32, .caller 2 192])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])
    (by decide) (by simp [Whole.valid]) (by simp)) fun u ⟨hu, hm, hs, st⟩ => ?_)
  have h0 := hs (.r0, .caller 2 0) (by simp)
  have h2 := hs (.r2, .const 0) (by simp)
  have h3 := hs (.r3, .const 0) (by simp)
  have a0 := st 0 (by decide)
  have a1 := st 1 (by decide)
  have a2 := st 2 (by decide)
  simp only [VG.Proof.Ed25519.Arm.PublicKey.argValue, Lay.value, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at h0 h2 h3 a0 a1 a2
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  have hp := Whole.update_pre hu.sp h0 a0 a1 a2 hL.sc
    (hL.kc.sub_left (Region.sub_prefix (by decide : 12 ≤ 280))) hL.nc hL.ns
    (by have := hL.top; omega)
  have count : Proof.Sha512.countArm u = BitVec.ofNat 64 ([] : List Byte).length := by
    rw [Proof.Sha512.countArm, h2, h3]
    rfl
  refine WP.mono (Whole.update_call hu hp (VG.Proof.Ed25519.Arm.PublicKey.update_covers L) hw h0 a0 a1 count (VG.Proof.Ed25519.Arm.PublicKey.setup_repr hL hm hh))
    fun u' ⟨hu', _, hr⟩ => ⟨hu', ?_⟩
  change Spec.Sha512.Repr _ u'.mem _ ([] ++ Spec.Ed25519.bytesAt u.mem (State.addr L.seed) 32) at hr
  rw [List.nil_append, hu.seed_bytes hL] at hr
  exact hr

theorem digest_addr (hL : L.Ok) : State.addr (L.E + 184) = State.addr L.E + 184 :=
  addr_add (k := 184) (by have := hL.top; omega)

theorem finalize_writes (hL : L.Ok) : ∀ r ∈ Whole.finalizeWr L.scr (L.E + 184),
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by change 0 + 192 ≤ 8192; decide⟩
  · exact .inl ⟨184, VG.Proof.Ed25519.Arm.PublicKey.digest_addr hL, by change 184 + 64 ≤ 248; decide⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 192, rfl, by change 192 + 272 ≤ 8192; decide⟩

theorem finalize_covers (hL : L.Ok) :
    Covers (Whole.finalizeRd L.E ++ Whole.finalizeWr L.scr (L.E + 184))
      (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  intro a n ⟨r, hr, hh⟩
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr] at hh
    exact ⟨L.FR, List.mem_append_right _ List.mem_cons_self, by
      change (a - State.addr L.E).toNat + n ≤ 248
      change (a - State.addr L.E).toNat + n ≤ 8 at hh
      omega⟩
  · exact Whole.covers_writes (VG.Proof.Ed25519.Arm.PublicKey.finalize_writes hL) a n ⟨r, hr, hh⟩

theorem finalize_step (hc : VG.Proof.Ed25519.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.PublicKey.Arguments L m₀)
    (hh : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr)
      (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32)) :
    WP isa (callWith finalizeArgs Spec.Sha512.finalizeScratchApi.name Impl.Sha512.Arm.Stream.finalize) t fun u =>
      VG.Proof.Ed25519.Arm.PublicKey.Ctx L g m₀ u ∧ Spec.Ed25519.bytesAt u.mem (State.addr L.E + 184) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.PublicKey.setup_ok hc hL ha
    (args := [(.r0, .caller 2 0), (.r2, .const 32), (.r3, .const 0)])
    (stk := [.frame 184, .caller 2 192])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])
    (by decide) (by simp [Whole.valid]) (by simp)) fun u ⟨hu, hm, hs, st⟩ => ?_)
  have h0 := hs (.r0, .caller 2 0) (by simp)
  have h2 := hs (.r2, .const 32) (by simp)
  have h3 := hs (.r3, .const 0) (by simp)
  have a0 := st 0 (by decide)
  have a1 := st 1 (by decide)
  simp only [VG.Proof.Ed25519.Arm.PublicKey.argValue, Lay.value, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at h0 h2 h3 a0 a1
  have hd : Region.Disjoint ⟨State.addr (L.E + 184), 64⟩ L.SCR := by
    rw [VG.Proof.Ed25519.Arm.PublicKey.digest_addr hL]
    exact hL.kc.sub_left (Offset.sub_base _ (by decide : 184 + 64 ≤ 280))
  have ds : (Whole.CALLARGS L.E 8).Disjoint ⟨State.addr (L.E + 184), 64⟩ := by
    rw [VG.Proof.Ed25519.Arm.PublicKey.digest_addr hL]
    exact Offset.base_disjoint _ (by decide) (by decide)
  have nf : (L.E + 184).toNat + 64 ≤ 2 ^ 32 := by
    have ht := hL.top
    rw [BitVec.toNat_add_of_lt (by change L.E.toNat + 184 < 2 ^ 32; omega)]
    change L.E.toNat + 184 + 64 ≤ 2 ^ 32
    omega
  have hp := Whole.finalize_pre hu.sp h0 a0 a1 hd
    (hL.kc.sub_left (Region.sub_prefix (by decide : 8 ≤ 280))) ds hL.nc nf
    (by have := hL.top; omega)
  have hl : (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32).length = 32 := by
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]
  have count : Proof.Sha512.countArm u = BitVec.ofNat 64 (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32).length := by
    rw [hl, Proof.Sha512.countArm, h2, h3]
    rfl
  refine WP.mono (Whole.finalize_call hu hp (VG.Proof.Ed25519.Arm.PublicKey.finalize_covers hL) (VG.Proof.Ed25519.Arm.PublicKey.finalize_writes hL) h0 a0 count
    (VG.Proof.Ed25519.Arm.PublicKey.setup_repr hL hm hh) (by rw [hl]; decide)) fun u' ⟨hu', _, hd⟩ => ⟨hu', ?_⟩
  rw [addr_add (k := 184) (by have := hL.top; omega)] at hd
  exact hd

theorem hash_ok (hc : VG.Proof.Ed25519.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.PublicKey.Arguments L m₀) :
    WP isa hash t fun u => VG.Proof.Ed25519.Arm.PublicKey.Ctx L g m₀ u ∧
      Spec.Ed25519.bytesAt u.mem (State.addr L.E + 184) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32) := by
  exact WP.seq (WP.mono (VG.Proof.Ed25519.Arm.PublicKey.init_step hc hL ha) fun t₁ ⟨h₁, hh₁⟩ =>
    WP.seq (WP.mono (VG.Proof.Ed25519.Arm.PublicKey.update_step h₁ hL ha hh₁) fun t₂ ⟨h₂, hh₂⟩ => VG.Proof.Ed25519.Arm.PublicKey.finalize_step h₂ hL ha hh₂))

end VG.Proof.Ed25519.Arm.PublicKey
end

/-! Merged from `Proof.Ed25519.Arm.PublicKey.Base`. -/
section
namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.PublicKey
open VG.Impl.Ed25519.Arm.Whole (callWith)

variable {L : VG.Proof.Ed25519.Arm.PublicKey.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem base_noFrames : Impl.Ed25519.Arm.scalarBase.noFrames = true := by lit_decide

def BaseArgs (L : VG.Proof.Ed25519.Arm.PublicKey.Lay) (t : State) : Prop :=
  t.gpr .r0 = L.out ∧ t.gpr .r1 = L.E + 24 ∧ t.gpr .r2 = L.scr

theorem scalar_addr (hL : L.Ok) : State.addr (L.E + 24) = State.addr L.E + 24 :=
  addr_add (k := 24) (by have := hL.top; omega)

theorem base_pre (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.PublicKey.BaseArgs L t) :
    scalarBaseLocal.pre (t.callEntry.withRegions [⟨State.addr L.E + 24, 32⟩] L.outputs) := by
  obtain ⟨h0, h1, h2⟩ := ha
  simp only [scalarBaseLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), h0, h1, h2, VG.Proof.Ed25519.Arm.PublicKey.scalar_addr hL]
  refine ⟨True.intro, rfl, (hL.ko.sub_left (Offset.sub_base _ (by decide : 24 + 32 ≤ 280))).symm,
    hL.oc, hL.kc.sub_left (Offset.sub_base _ (by decide : 24 + 32 ≤ 280)), hL.no, ?_, hL.nc⟩
  have h := hL.top
  rw [BitVec.toNat_add_of_lt (by change L.E.toNat + 24 < 2 ^ 32; omega)]
  change L.E.toNat + 24 + 32 ≤ 2 ^ 32
  omega

theorem base_covers (L : VG.Proof.Ed25519.Arm.PublicKey.Lay) : Covers ([⟨State.addr L.E + 24, 32⟩] ++ L.outputs)
    (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]
    exact ⟨Whole.FR L.E, List.mem_append_right _ List.mem_cons_self, 24, rfl, by change 24 + 32 ≤ 248; decide⟩
  · exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr), 0, by simp⟩

theorem base_writes (L : VG.Proof.Ed25519.Arm.PublicKey.Lay) : ∀ r ∈ L.outputs,
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R :=
  fun r hr => .inr ⟨r, hr, 0, (BitVec.add_zero _).symm, by simp⟩

theorem base_call (hc : VG.Proof.Ed25519.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.PublicKey.BaseArgs L t) :
    WP isa (.call "vg_ed25519_scalar_base" Impl.Ed25519.Arm.scalarBase) t fun u =>
      VG.Proof.Ed25519.Arm.PublicKey.Ctx L g m₀ u ∧ Spec.Ed25519.bytesAt u.mem (State.addr L.out) 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt t.mem (State.addr L.E + 24) 32) := by
  refine Whole.call_ok hc scalarBase_ok VG.Proof.Ed25519.Arm.PublicKey.base_noFrames (VG.Proof.Ed25519.Arm.PublicKey.base_pre hL ha) (VG.Proof.Ed25519.Arm.PublicKey.base_covers L)
    (VG.Proof.Ed25519.Arm.PublicKey.base_writes L) fun u hu _ hp => ⟨hu, ?_⟩
  change Spec.Ed25519.bytesAt u.mem (State.addr (t.callEntry.gpr .r0)) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt t.mem (State.addr (t.callEntry.gpr .r1)) 32) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), ha.1, ha.2.1, VG.Proof.Ed25519.Arm.PublicKey.scalar_addr hL] at hp
  exact hp

theorem prune_step (hc : VG.Proof.Ed25519.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) {digest : List Byte}
    (hh : Spec.Ed25519.bytesAt t.mem (State.addr L.E + 184) 64 = digest) :
    WP isa (.block prune) t fun u => VG.Proof.Ed25519.Arm.PublicKey.Ctx L g m₀ u ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt u.mem (State.addr L.E + 24) 32) = Spec.Ed25519.prune digest := by
  have hwrite : (⟨State.addr L.E, 248⟩ : Region) ∈ t.wr := by rw [hc.wr]; exact List.mem_cons_self
  refine WP.mono (VG.Proof.Ed25519.Arm.PublicKey.prune_ok hc.sp (by have := hL.top; omega) hwrite hh) fun u ⟨hu, hf, hp⟩ => ⟨?_, hp⟩
  refine hc.of_frame hu.rd hu.wr hu.sp ?_ hf ?_
  · intro r hr _
    apply hu.regs r <;> intro h <;> subst r <;> simp [preserved] at hr
  · rintro r hr
    rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ (by decide : 24 + 32 ≤ 248))

theorem base_step (hc : VG.Proof.Ed25519.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.PublicKey.Arguments L m₀) {n : Nat}
    (hs : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem (State.addr L.E + 24) 32) = n) :
    WP isa (callWith baseArgs "vg_ed25519_scalar_base" Impl.Ed25519.Arm.scalarBase) t fun u =>
      VG.Proof.Ed25519.Arm.PublicKey.Ctx L g m₀ u ∧ Spec.Ed25519.bytesAt u.mem (State.addr L.out) 32 =
        Spec.Ed25519.encodePoint (Spec.Ed25519.pointMul n Spec.Ed25519.basePoint) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.PublicKey.setup_ok hc hL ha
    (args := [(.r0, .caller 0 0), (.r1, .frame 24), (.r2, .caller 2 0)]) (stk := [])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])
    (by decide) (by simp) (by simp)) fun u ⟨hu, hm, hav, _⟩ => ?_)
  have h0 := hav (.r0, .caller 0 0) (by simp)
  have h1 := hav (.r1, .frame 24) (by simp)
  have h2 := hav (.r2, .caller 2 0) (by simp)
  simp only [VG.Proof.Ed25519.Arm.PublicKey.argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  have he : Spec.Ed25519.bytesAt u.mem (State.addr L.E + 24) 32 =
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 24) 32 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun i hi => hm.bytes (R := ⟨State.addr L.E + 24, 32⟩) ?_
      (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint_base _ (by decide) (by decide)
  refine WP.mono (VG.Proof.Ed25519.Arm.PublicKey.base_call hu hL ⟨h0, h1, h2⟩) fun u' ⟨hu', hp⟩ => ⟨hu', ?_⟩
  rw [hp, he, Spec.Ed25519.scalarBase, hs]

theorem wipe_step (hc : VG.Proof.Ed25519.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) :
    WP isa (.block wipe) t fun u => VG.Proof.Ed25519.Arm.PublicKey.Ctx L g m₀ u ∧
      Spec.Ed25519.bytesAt u.mem (State.addr L.out) 32 = Spec.Ed25519.bytesAt t.mem (State.addr L.out) 32 := by
  refine WP.mono (Whole.Ctx.zeroWords hc (by have := hL.top; omega) (start := 6) (count := 56) (by decide))
    fun u ⟨hu, hf, _⟩ => ⟨hu, ?_⟩
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes (R := L.OUT) ?_
    (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rintro r hr
  rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (Offset.sub_base _ (by decide : 4 * 6 + 4 * 56 ≤ 280))).symm

end VG.Proof.Ed25519.Arm.PublicKey
end

/-! Merged from `Proof.Ed25519.Arm.PublicKey.Entry`. -/
section
namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm

def pkLocal : Contract isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 32⟩
    let seed : Region := ⟨State.addr (s.gpr .r1), 32⟩
    let scr : Region := ⟨State.addr (s.gpr .r2), 8192⟩
    let stk : Region := ⟨State.addr s.sp - 280, 280⟩
    s.rd = [seed] ∧ s.wr = [out, scr] ∧
      out.Disjoint seed ∧ out.Disjoint scr ∧ seed.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint seed ∧ stk.Disjoint scr ∧
      (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ s.sp.toNat
  post s t := Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r0)) 32 =
    Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32)
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2

def lay (s : State) : VG.Proof.Ed25519.Arm.PublicKey.Lay := ⟨s.gpr .r0, s.gpr .r1, s.gpr .r2, Whole.base s⟩

theorem lay_ok {s : State} (h : pkLocal.pre s) : (VG.Proof.Ed25519.Arm.PublicKey.lay s).Ok := by
  obtain ⟨_, _, os, oc, sc, ko, ks, kc, no, ns, nc, hb⟩ := h
  have he := Whole.base_addr hb
  have top := Whole.base_top hb
  have hs := s.sp.isLt
  refine ⟨by change (Whole.base s).toNat + 272 ≤ 2 ^ 32; omega, os, oc, sc, ?_, ?_, ?_, no, ns, nc⟩
  · change (⟨State.addr (Whole.base s), 280⟩ : Region).Disjoint _
    rw [he]; exact ko
  · change (⟨State.addr (Whole.base s), 280⟩ : Region).Disjoint _
    rw [he]; exact ks
  · change (⟨State.addr (Whole.base s), 280⟩ : Region).Disjoint _
    rw [he]; exact kc

theorem entry_below {s : State} (h : pkLocal.pre s) : 280 ≤ s.sp.toNat := h.2.2.2.2.2.2.2.2.2.2.2

theorem entry_writes {s : State} (h : pkLocal.pre s) :
    ∀ r ∈ s.wr, (Whole.stack s).Disjoint r := by
  intro r hr
  rw [h.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (VG.Proof.Ed25519.Arm.PublicKey.lay_ok h).ko
  · exact (VG.Proof.Ed25519.Arm.PublicKey.lay_ok h).kc

theorem entry_ctx {s p : State} (h : pkLocal.pre s) (hp : Whole.Saved (Whole.entered s) 3 p) :
    VG.Proof.Ed25519.Arm.PublicKey.Ctx (VG.Proof.Ed25519.Arm.PublicKey.lay s) s.gpr p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  simpa only [Whole.bodyRd, h.1, Whole.bodyWr, h.2.1, VG.Proof.Ed25519.Arm.PublicKey.Ctx, Lay.inputs, Lay.outputs,
    Lay.SEED, Lay.OUT, Lay.SCR, Lay.ARGS, VG.Proof.Ed25519.Arm.PublicKey.lay, List.cons_append, List.nil_append] using hc

theorem entry_args {s p : State} (hs : 280 ≤ s.sp.toNat) (hp : Whole.Saved (Whole.entered s) 3 p) : VG.Proof.Ed25519.Arm.PublicKey.Arguments (VG.Proof.Ed25519.Arm.PublicKey.lay s) p.mem := by
  intro j hj
  have hw := Whole.saved_words hs (by decide : 3 ≤ 6)
    (by simp only [Nat.reduceSub, Nat.mul_zero, Nat.add_zero]; exact Nat.le_of_lt s.sp.isLt) hp hj
  have he : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases he with rfl | rfl | rfl <;> exact hw

def satState : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x4000 | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩]

theorem pk_implies : pkLocal.Implies (Spec.Ed25519.publicKeyContract Arm.abi 280) := by
  sig_implies [Spec.Ed25519.publicKeyContract, Spec.Ed25519.publicKeySig,
    Spec.Ed25519.scratchWords, VG.Proof.Ed25519.Arm.PublicKey.pkLocal, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [satState] using VG.Proof.Ed25519.Arm.PublicKey.satState

end VG.Proof.Ed25519.Arm.PublicKey
end

namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.PublicKey

variable {L : VG.Proof.Ed25519.Arm.PublicKey.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem body_ok (hc : VG.Proof.Ed25519.Arm.PublicKey.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.PublicKey.Arguments L m₀) :
    WP isa body t fun u => VG.Proof.Ed25519.Arm.PublicKey.Ctx L g m₀ u ∧
      Spec.Ed25519.bytesAt u.mem (State.addr L.out) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.PublicKey.hash_ok hc hL ha) fun u ⟨hu, hh⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.PublicKey.prune_step hu hL hh) fun u' ⟨hu', hs⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.PublicKey.base_step hu' hL ha hs) fun u'' ⟨hu'', hp⟩ => ?_)
  exact WP.mono (VG.Proof.Ed25519.Arm.PublicKey.wipe_step hu'' hL) fun w ⟨hw, hm⟩ => ⟨hw, hm.trans hp⟩

theorem body_noFrames : body.noFrames = true := by
  simp only [body, Impl.Ed25519.Arm.PublicKey.hash, Impl.Ed25519.Arm.Whole.callWith, Code.noFrames,
    Impl.Sha512.Arm.Stream.init, Bool.and_self]
  rw [VG.Proof.Ed25519.Arm.PublicKey.base_noFrames]
  rfl

theorem publicKey_ok {s : State} (h : pkLocal.pre s) :
    WP isa VG.Impl.Ed25519.Arm.PublicKey.code s fun u => abiPreserved s u ∧ pkLocal.post s u := by
  have hw := Whole.wrap_ok VG.Proof.Ed25519.Arm.PublicKey.body_noFrames (by decide : 3 ≤ 6) (VG.Proof.Ed25519.Arm.PublicKey.entry_below h)
    (by simp only [Nat.reduceSub, Nat.mul_zero, Nat.add_zero]; exact Nat.le_of_lt s.sp.isLt)
    (by intro j hj h4; omega) (VG.Proof.Ed25519.Arm.PublicKey.entry_writes h)
    (P := fun m m' _ => Spec.Ed25519.bytesAt m' (State.addr (s.gpr .r0)) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m (State.addr (s.gpr .r1)) 32))
    (fun p hp => WP.mono (VG.Proof.Ed25519.Arm.PublicKey.body_ok (VG.Proof.Ed25519.Arm.PublicKey.entry_ctx h hp) (VG.Proof.Ed25519.Arm.PublicKey.lay_ok h) (VG.Proof.Ed25519.Arm.PublicKey.entry_args (VG.Proof.Ed25519.Arm.PublicKey.entry_below h) hp))
      fun u ⟨hu, ho⟩ => ⟨by
        simpa only [Whole.bodyRd, h.1, VG.Proof.Ed25519.Arm.PublicKey.Ctx, Lay.inputs, Lay.outputs, Lay.SEED, Lay.OUT,
          Lay.SCR, Lay.ARGS, VG.Proof.Ed25519.Arm.PublicKey.lay, h.2.1, List.cons_append, List.nil_append] using hu, ho⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  have hs : Spec.Ed25519.bytesAt m (State.addr (s.gpr .r1)) 32 =
      Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun i hi => hf.bytes (R := ⟨State.addr (s.gpr .r1), 32⟩) ?_
      (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact (VG.Proof.Ed25519.Arm.PublicKey.lay_ok h).ks.symm
  change Spec.Ed25519.bytesAt u.mem (State.addr (s.gpr .r0)) 32 = _
  rw [hp, hs]

end VG.Proof.Ed25519.Arm.PublicKey
end

/-! Merged from `Proof.Ed25519.Arm.PublicKey.CT`. -/
section
/-! Merged from `Proof.Ed25519.Arm.PublicKey.CTReady`. -/
section
/-! Merged from `Proof.Ed25519.Arm.PublicKey.CTCommon`. -/
section
namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

abbrev Two (L : VG.Proof.Ed25519.Arm.PublicKey.Lay) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem)
    (P : State → Prop) (a b : State) := (VG.Proof.Ed25519.Arm.PublicKey.Ctx L g₁ m₁ a ∧ P a) ∧ (VG.Proof.Ed25519.Arm.PublicKey.Ctx L g₂ m₂ b ∧ P b)

def Slots (L : VG.Proof.Ed25519.Arm.PublicKey.Lay) (args : List (Reg × Value)) (stk : List Value) (s : State) :=
  (∀ p ∈ args, s.gpr p.1 = VG.Proof.Ed25519.Arm.PublicKey.argValue L p.2) ∧ ∀ j (hj : j < stk.length), stackArg s j = VG.Proof.Ed25519.Arm.PublicKey.argValue L (stk[j]'hj)

variable {L : VG.Proof.Ed25519.Arm.PublicKey.Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem setup_ct (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.PublicKey.Arguments L m₁) (hb : VG.Proof.Ed25519.Arm.PublicKey.Arguments L m₂)
    (args : List (Reg × Value)) (stk : List Value)
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    (hs : stk.length ≤ 6) (hvs : ∀ v ∈ stk, Whole.valid v)
    (his : ∀ v ∈ stk, ∀ j d, v = .caller j d → j < 3) :
    RelCT isa (VG.Proof.Ed25519.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) (.block (setup args stk))
      (VG.Proof.Ed25519.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ (VG.Proof.Ed25519.Arm.PublicKey.Slots L args stk)) := by
  refine Whole.rel_wp ((Whole.setup_ct args stk).mono
    (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩
    exact WP.mono (VG.Proof.Ed25519.Arm.PublicKey.setup_ok hc hL ha hn hv hi hr hs hvs his) fun _ ⟨hc, _, hg, ht⟩ => ⟨hc, hg, ht⟩
  · intro t ⟨hc, _⟩
    exact WP.mono (VG.Proof.Ed25519.Arm.PublicKey.setup_ok hc hL hb hn hv hi hr hs hvs his) fun _ ⟨hc, _, hg, ht⟩ => ⟨hc, hg, ht⟩

theorem call_ct {args : List (Reg × Value)} {stk : List Value} {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (hn : c.noFrames = true)
    (ready : ∀ t, t.sp = L.E → VG.Proof.Ed25519.Arm.PublicKey.Slots L args stk t → Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, a.sp = b.sp →
      (∀ p ∈ args, a.callEntry.gpr p.1 = b.callEntry.gpr p.1) →
      (∀ j < stk.length, stackArg a j = stackArg b j) →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw))
    (hl : ∀ p ∈ args, p.1 ∉ linkRegs) :
    RelCT isa (VG.Proof.Ed25519.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ (VG.Proof.Ed25519.Arm.PublicKey.Slots L args stk)) (.call name c)
      (VG.Proof.Ed25519.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp ?_ ?_ ?_
  · refine Whole.callEx correct ct fun a b h => ?_
    let ra := ready a h.1.1.sp h.1.2
    let rb := ready b h.2.1.sp h.2.2
    obtain ⟨ca, wa⟩ := ra.covers_state h.1.1
    obtain ⟨cb, wb⟩ := rb.covers_state h.2.1
    refine ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ (h.1.1.sp.trans h.2.1.sp.symm) ?_ ?_, ca, wa, cb, wb⟩
    · intro p hp
      rw [State.callEntry_gpr _ (hl p hp), State.callEntry_gpr _ (hl p hp), h.1.2.1 p hp, h.2.2.1 p hp]
    · intro j hj
      exact (h.1.2.2 j hj).trans (h.2.2.2 j hj).symm
  · intro t ⟨hc, hs⟩
    exact WP.mono ((ready t hc.sp hs).wp hc correct hn) fun _ hu => ⟨hu, trivial⟩
  · intro t ⟨hc, hs⟩
    exact WP.mono ((ready t hc.sp hs).wp hc correct hn) fun _ hu => ⟨hu, trivial⟩

end VG.Proof.Ed25519.Arm.PublicKey
end

namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

def initValues : List (Reg × Value) := [(.r0, .caller 2 0)]
def updateValues : List (Reg × Value) := [(.r0, .caller 2 0), (.r2, .const 0), (.r3, .const 0)]
def updateStack : List Value := [.caller 1 0, .const 32, .caller 2 192]
def finalizeValues : List (Reg × Value) := [(.r0, .caller 2 0), (.r2, .const 32), (.r3, .const 0)]
def finalizeStack : List Value := [.frame 184, .caller 2 192]
def baseValues : List (Reg × Value) := [(.r0, .caller 0 0), (.r1, .frame 24), (.r2, .caller 2 0)]

variable {L : VG.Proof.Ed25519.Arm.PublicKey.Lay} {t : State}

def init_ready (hL : L.Ok) (hs : VG.Proof.Ed25519.Arm.PublicKey.Slots L VG.Proof.Ed25519.Arm.PublicKey.initValues [] t) :
    Whole.CallReady (Proof.Sha512.initArm Spec.Sha512.H0_512) L.E L.inputs L.outputs t := by
  have h0 := hs.1 (.r0, .caller 2 0) (by simp [VG.Proof.Ed25519.Arm.PublicKey.initValues])
  simp only [VG.Proof.Ed25519.Arm.PublicKey.argValue, Lay.value, BitVec.add_zero] at h0
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨[], Whole.initWr L.scr, Whole.init_pre h0 hL.nc, Whole.covers_writes hw, hw⟩

def update_ready (hL : L.Ok) (he : t.sp = L.E) (hs : VG.Proof.Ed25519.Arm.PublicKey.Slots L VG.Proof.Ed25519.Arm.PublicKey.updateValues VG.Proof.Ed25519.Arm.PublicKey.updateStack t) :
    Whole.CallReady Proof.Sha512.updateArm L.E L.inputs L.outputs t := by
  have h0 := hs.1 (.r0, .caller 2 0) (by simp [VG.Proof.Ed25519.Arm.PublicKey.updateValues])
  have a0 := hs.2 0 (by decide)
  have a1 := hs.2 1 (by decide)
  have a2 := hs.2 2 (by decide)
  simp only [VG.Proof.Ed25519.Arm.PublicKey.updateStack, VG.Proof.Ed25519.Arm.PublicKey.argValue, Lay.value, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at h0 a0 a1 a2
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨Whole.updateRd L.E L.seed 32, Whole.hashWr L.scr,
    Whole.update_pre he h0 a0 a1 a2 hL.sc
      (hL.kc.sub_left (Region.sub_prefix (by decide : 12 ≤ 280))) hL.nc hL.ns
      (by have := hL.top; omega), VG.Proof.Ed25519.Arm.PublicKey.update_covers L, hw⟩

def finalize_ready (hL : L.Ok) (he : t.sp = L.E) (hs : VG.Proof.Ed25519.Arm.PublicKey.Slots L VG.Proof.Ed25519.Arm.PublicKey.finalizeValues VG.Proof.Ed25519.Arm.PublicKey.finalizeStack t) :
    Whole.CallReady Proof.Sha512.finalizeArm L.E L.inputs L.outputs t := by
  have h0 := hs.1 (.r0, .caller 2 0) (by simp [VG.Proof.Ed25519.Arm.PublicKey.finalizeValues])
  have a0 := hs.2 0 (by decide)
  have a1 := hs.2 1 (by decide)
  simp only [VG.Proof.Ed25519.Arm.PublicKey.finalizeStack, VG.Proof.Ed25519.Arm.PublicKey.argValue, Lay.value, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at h0 a0 a1
  have hd : Region.Disjoint ⟨State.addr (L.E + 184), 64⟩ L.SCR := by
    rw [VG.Proof.Ed25519.Arm.PublicKey.digest_addr hL]
    exact hL.kc.sub_left (Offset.sub_base _ (by decide : 184 + 64 ≤ 280))
  have ds : (Whole.CALLARGS L.E 8).Disjoint ⟨State.addr (L.E + 184), 64⟩ := by
    rw [VG.Proof.Ed25519.Arm.PublicKey.digest_addr hL]
    exact Offset.base_disjoint _ (by decide) (by decide)
  have nf : (L.E + 184).toNat + 64 ≤ 2 ^ 32 := by
    have ht := hL.top
    rw [BitVec.toNat_add_of_lt (by change L.E.toNat + 184 < 2 ^ 32; omega)]
    change L.E.toNat + 184 + 64 ≤ 2 ^ 32
    omega
  exact ⟨Whole.finalizeRd L.E, Whole.finalizeWr L.scr (L.E + 184),
    Whole.finalize_pre he h0 a0 a1 hd
      (hL.kc.sub_left (Region.sub_prefix (by decide : 8 ≤ 280))) ds hL.nc nf
      (by have := hL.top; omega), VG.Proof.Ed25519.Arm.PublicKey.finalize_covers hL, VG.Proof.Ed25519.Arm.PublicKey.finalize_writes hL⟩

def base_ready (hL : L.Ok) (hs : VG.Proof.Ed25519.Arm.PublicKey.Slots L VG.Proof.Ed25519.Arm.PublicKey.baseValues [] t) :
    Whole.CallReady scalarBaseLocal L.E L.inputs L.outputs t := by
  have h0 := hs.1 (.r0, .caller 0 0) (by simp [VG.Proof.Ed25519.Arm.PublicKey.baseValues])
  have h1 := hs.1 (.r1, .frame 24) (by simp [VG.Proof.Ed25519.Arm.PublicKey.baseValues])
  have h2 := hs.1 (.r2, .caller 2 0) (by simp [VG.Proof.Ed25519.Arm.PublicKey.baseValues])
  simp only [VG.Proof.Ed25519.Arm.PublicKey.argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  exact ⟨[⟨State.addr L.E + 24, 32⟩], L.outputs, VG.Proof.Ed25519.Arm.PublicKey.base_pre hL ⟨h0, h1, h2⟩, VG.Proof.Ed25519.Arm.PublicKey.base_covers L, VG.Proof.Ed25519.Arm.PublicKey.base_writes L⟩

end VG.Proof.Ed25519.Arm.PublicKey
end

namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.PublicKey

variable {L : VG.Proof.Ed25519.Arm.PublicKey.Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem init_ct (hL : L.Ok) : RelCT isa (VG.Proof.Ed25519.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ (VG.Proof.Ed25519.Arm.PublicKey.Slots L VG.Proof.Ed25519.Arm.PublicKey.initValues []))
    (.call Spec.Sha512.init512Api.name (Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512)) (VG.Proof.Ed25519.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed25519.Arm.PublicKey.call_ct (Proof.Sha512.Arm.Stream.init_verified _).1
    (Proof.Sha512.Arm.Stream.init_verified _).2.1 rfl (fun _ _ h => VG.Proof.Ed25519.Arm.PublicKey.init_ready hL h)
  · intro a b ar aw br bw hsp hg ht
    exact hg (.r0, .caller 2 0) (by simp [VG.Proof.Ed25519.Arm.PublicKey.initValues])
  · simp [VG.Proof.Ed25519.Arm.PublicKey.initValues, linkRegs]

theorem update_ct (hL : L.Ok) : RelCT isa (VG.Proof.Ed25519.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ (VG.Proof.Ed25519.Arm.PublicKey.Slots L VG.Proof.Ed25519.Arm.PublicKey.updateValues VG.Proof.Ed25519.Arm.PublicKey.updateStack))
    (.call Spec.Sha512.updateScratchApi.name Impl.Sha512.Arm.Stream.update) (VG.Proof.Ed25519.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed25519.Arm.PublicKey.call_ct Proof.Sha512.Arm.Stream.Update.update_verified.1 Proof.Sha512.Arm.Stream.Update.update_verified.2.1
    Whole.update_noFrames (fun _ he h => VG.Proof.Ed25519.Arm.PublicKey.update_ready hL he h)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg (.r0, .caller 2 0) (by simp [VG.Proof.Ed25519.Arm.PublicKey.updateValues]), hg (.r2, .const 0) (by simp [VG.Proof.Ed25519.Arm.PublicKey.updateValues]), hg (.r3, .const 0) (by simp [VG.Proof.Ed25519.Arm.PublicKey.updateValues]), ht 0 (by decide), ht 1 (by decide), ht 2 (by decide)⟩
  · simp [VG.Proof.Ed25519.Arm.PublicKey.updateValues, linkRegs]

theorem finalize_ct (hL : L.Ok) : RelCT isa (VG.Proof.Ed25519.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ (VG.Proof.Ed25519.Arm.PublicKey.Slots L VG.Proof.Ed25519.Arm.PublicKey.finalizeValues VG.Proof.Ed25519.Arm.PublicKey.finalizeStack))
    (.call Spec.Sha512.finalizeScratchApi.name Impl.Sha512.Arm.Stream.finalize) (VG.Proof.Ed25519.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed25519.Arm.PublicKey.call_ct Proof.Sha512.Arm.Stream.Finalize.finalize_verified.1 Proof.Sha512.Arm.Stream.Finalize.finalize_verified.2.1
    Whole.finalize_noFrames (fun _ he h => VG.Proof.Ed25519.Arm.PublicKey.finalize_ready hL he h)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg (.r0, .caller 2 0) (by simp [VG.Proof.Ed25519.Arm.PublicKey.finalizeValues]), hg (.r2, .const 32) (by simp [VG.Proof.Ed25519.Arm.PublicKey.finalizeValues]), hg (.r3, .const 0) (by simp [VG.Proof.Ed25519.Arm.PublicKey.finalizeValues]), ht 0 (by decide), ht 1 (by decide)⟩
  · simp [VG.Proof.Ed25519.Arm.PublicKey.finalizeValues, linkRegs]

theorem base_ct (hL : L.Ok) : RelCT isa (VG.Proof.Ed25519.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ (VG.Proof.Ed25519.Arm.PublicKey.Slots L VG.Proof.Ed25519.Arm.PublicKey.baseValues []))
    (.call "vg_ed25519_scalar_base" Impl.Ed25519.Arm.scalarBase) (VG.Proof.Ed25519.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed25519.Arm.PublicKey.call_ct scalarBase_ok scalarBase_ct VG.Proof.Ed25519.Arm.PublicKey.base_noFrames (fun _ _ h => VG.Proof.Ed25519.Arm.PublicKey.base_ready hL h)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg (.r0, .caller 0 0) (by simp [VG.Proof.Ed25519.Arm.PublicKey.baseValues]), hg (.r1, .frame 24) (by simp [VG.Proof.Ed25519.Arm.PublicKey.baseValues]), hg (.r2, .caller 2 0) (by simp [VG.Proof.Ed25519.Arm.PublicKey.baseValues])⟩
  · simp [VG.Proof.Ed25519.Arm.PublicKey.baseValues, linkRegs]

theorem prune_ct (hL : L.Ok) : RelCT isa (VG.Proof.Ed25519.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) (.block prune)
    (VG.Proof.Ed25519.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp (prune_sp_ct.mono (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm)
    (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩
    exact WP.mono (VG.Proof.Ed25519.Arm.PublicKey.prune_step hc hL (digest := Spec.Ed25519.bytesAt t.mem (State.addr L.E + 184) 64) rfl)
      fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, _⟩
    exact WP.mono (VG.Proof.Ed25519.Arm.PublicKey.prune_step hc hL (digest := Spec.Ed25519.bytesAt t.mem (State.addr L.E + 184) 64) rfl)
      fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

theorem wipe_ct (hL : L.Ok) : RelCT isa (VG.Proof.Ed25519.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) (.block wipe)
    (VG.Proof.Ed25519.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp ((Whole.zeroWords_ct 6 56).mono
    (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩; exact WP.mono (VG.Proof.Ed25519.Arm.PublicKey.wipe_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, _⟩; exact WP.mono (VG.Proof.Ed25519.Arm.PublicKey.wipe_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

theorem body_ct (hL : L.Ok) (ha : VG.Proof.Ed25519.Arm.PublicKey.Arguments L m₁) (hb : VG.Proof.Ed25519.Arm.PublicKey.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed25519.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) body (VG.Proof.Ed25519.Arm.PublicKey.Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have i := VG.Proof.Ed25519.Arm.PublicKey.setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb VG.Proof.Ed25519.Arm.PublicKey.initValues []
    (by decide) (by simp [VG.Proof.Ed25519.Arm.PublicKey.initValues, Whole.valid]) (by simp [VG.Proof.Ed25519.Arm.PublicKey.initValues])
    (by simp [VG.Proof.Ed25519.Arm.PublicKey.initValues, preserved]) (by decide) (by simp [Whole.valid])
    (by simp)
  have u := VG.Proof.Ed25519.Arm.PublicKey.setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb VG.Proof.Ed25519.Arm.PublicKey.updateValues VG.Proof.Ed25519.Arm.PublicKey.updateStack
    (by decide) (by simp [VG.Proof.Ed25519.Arm.PublicKey.updateValues, Whole.valid]) (by simp [VG.Proof.Ed25519.Arm.PublicKey.updateValues])
    (by simp [VG.Proof.Ed25519.Arm.PublicKey.updateValues, preserved]) (by decide) (by simp [VG.Proof.Ed25519.Arm.PublicKey.updateStack, Whole.valid])
    (by simp [VG.Proof.Ed25519.Arm.PublicKey.updateStack])
  have f := VG.Proof.Ed25519.Arm.PublicKey.setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb VG.Proof.Ed25519.Arm.PublicKey.finalizeValues VG.Proof.Ed25519.Arm.PublicKey.finalizeStack
    (by decide) (by simp [VG.Proof.Ed25519.Arm.PublicKey.finalizeValues, Whole.valid]) (by simp [VG.Proof.Ed25519.Arm.PublicKey.finalizeValues])
    (by simp [VG.Proof.Ed25519.Arm.PublicKey.finalizeValues, preserved]) (by decide) (by simp [VG.Proof.Ed25519.Arm.PublicKey.finalizeStack, Whole.valid])
    (by simp [VG.Proof.Ed25519.Arm.PublicKey.finalizeStack])
  have b := VG.Proof.Ed25519.Arm.PublicKey.setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb VG.Proof.Ed25519.Arm.PublicKey.baseValues []
    (by decide) (by simp [VG.Proof.Ed25519.Arm.PublicKey.baseValues, Whole.valid]) (by simp [VG.Proof.Ed25519.Arm.PublicKey.baseValues])
    (by simp [VG.Proof.Ed25519.Arm.PublicKey.baseValues, preserved]) (by decide) (by simp [Whole.valid])
    (by simp)
  exact ((i.seq (VG.Proof.Ed25519.Arm.PublicKey.init_ct hL)).seq ((u.seq (VG.Proof.Ed25519.Arm.PublicKey.update_ct hL)).seq (f.seq (VG.Proof.Ed25519.Arm.PublicKey.finalize_ct hL)))).seq
    ((VG.Proof.Ed25519.Arm.PublicKey.prune_ct hL).seq ((b.seq (VG.Proof.Ed25519.Arm.PublicKey.base_ct hL)).seq (VG.Proof.Ed25519.Arm.PublicKey.wipe_ct hL)))

theorem lay_eq {s t : State} (hp : pkLocal.pub s t) : VG.Proof.Ed25519.Arm.PublicKey.lay s = VG.Proof.Ed25519.Arm.PublicKey.lay t := by
  obtain ⟨sp, h0, h1, h2⟩ := hp
  simp only [VG.Proof.Ed25519.Arm.PublicKey.lay, Whole.base, sp, h0, h1, h2]

theorem publicKey_ct : ConstantTime isa pkLocal.pre pkLocal.pub VG.Impl.Ed25519.Arm.PublicKey.code := by
  refine Whole.wrap_ct (by decide : 3 ≤ 6) (fun _ _ hp => hp.1)
    (fun _ hs => VG.Proof.Ed25519.Arm.PublicKey.entry_below hs) ?_ (by intro s hs j hj h4; omega) ?_ ?_
  · intro s _
    simp only [Nat.reduceSub, Nat.mul_zero, Nat.add_zero]
    exact Nat.le_of_lt s.sp.isLt
  · intro s hs p hp
    exact WP.mono (VG.Proof.Ed25519.Arm.PublicKey.body_ok (VG.Proof.Ed25519.Arm.PublicKey.entry_ctx hs hp) (VG.Proof.Ed25519.Arm.PublicKey.lay_ok hs) (VG.Proof.Ed25519.Arm.PublicKey.entry_args (VG.Proof.Ed25519.Arm.PublicKey.entry_below hs) hp)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := VG.Proof.Ed25519.Arm.PublicKey.lay_eq hp
    have hq : VG.Proof.Ed25519.Arm.PublicKey.Ctx (VG.Proof.Ed25519.Arm.PublicKey.lay s) t.gpr q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ VG.Proof.Ed25519.Arm.PublicKey.entry_ctx ht hqb
    have hqa : VG.Proof.Ed25519.Arm.PublicKey.Arguments (VG.Proof.Ed25519.Arm.PublicKey.lay s) q.mem := he ▸ VG.Proof.Ed25519.Arm.PublicKey.entry_args (VG.Proof.Ed25519.Arm.PublicKey.entry_below ht) hqb
    exact ⟨(VG.Proof.Ed25519.Arm.PublicKey.body_ct (VG.Proof.Ed25519.Arm.PublicKey.lay_ok hs) (VG.Proof.Ed25519.Arm.PublicKey.entry_args (VG.Proof.Ed25519.Arm.PublicKey.entry_below hs) hpa) hqa _ _ _ _ _ _
      ⟨⟨VG.Proof.Ed25519.Arm.PublicKey.entry_ctx hs hpa, trivial⟩, ⟨hq, trivial⟩⟩ ea eb).1, trivial⟩

end VG.Proof.Ed25519.Arm.PublicKey
end

namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.PublicKey

theorem publicKey_verified :
    Verified Arm.target VG.Impl.Ed25519.Arm.PublicKey.code (Spec.Ed25519.publicKeyContract Arm.abi 280) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => VG.Proof.Ed25519.Arm.PublicKey.publicKey_ok h) VG.Proof.Ed25519.Arm.PublicKey.publicKey_ct (.refl pk_implies.sat_left))
    VG.Proof.Ed25519.Arm.PublicKey.pk_implies

end VG.Proof.Ed25519.Arm.PublicKey

end
