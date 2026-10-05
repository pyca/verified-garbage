import VerifiedGarbage.Impl.Ed25519.AArch64.PublicKey
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Prune`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.PublicKey.PruneArithmetic`. -/
section
namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG

theorem and_sub8 (x k : Nat) (hk : 3 ≤ k) : x &&& (2 ^ k - 8) = 8 * (x / 8 % 2 ^ (k - 3)) := by
  have e : 2 ^ k - 8 = 2 ^ 3 * (2 ^ (k - 3) - 1) := by
    rw [Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, Nat.add_sub_cancel' hk]; rfl
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
    BitVec.toNat_ofNat, c₁, c₂, c₃, VG.Proof.Ed25519.AArch64.PublicKey.and_sub8 _ 64 (by omega), VG.Proof.Ed25519.AArch64.PublicKey.and_sub8 _ 254 (by omega),
    Nat.and_two_pow_sub_one_eq_mod, VG.Proof.Ed25519.AArch64.PublicKey.or_two_pow (Nat.mod_lt _ (by omega)), VG.Proof.Ed25519.AArch64.PublicKey.or_two_pow (by omega)]
  simp only [show (2 : Nat) ^ (254 - 3) = 2 ^ 251 from rfl, show (2 : Nat) ^ (64 - 3) = 2 ^ 61 from rfl]
  omega

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

theorem Step.trans {s t u : State} (h : VG.Proof.Ed25519.AArch64.PublicKey.Step s t) (h' : VG.Proof.Ed25519.AArch64.PublicKey.Step t u) : VG.Proof.Ed25519.AArch64.PublicKey.Step s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp, h'.v.trans h.v,
    fun r h9 h10 h15 => (h'.regs r h9 h10 h15).trans (h.regs r h9 h10 h15)⟩

theorem pruneWord_ok {s : State} {k : Nat} (hk : k < 4)
    (hr : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (192 + 8 * k)) 8)
    (hw : InRegions s.wr (s.sp + BitVec.ofNat 64 (32 + 8 * k)) 8) :
    WP isa (.block (pruneWord k)) s fun t => VG.Proof.Ed25519.AArch64.PublicKey.Step s t ∧
      t.mem = s.mem.writeW (s.sp + BitVec.ofNat 64 (32 + 8 * k))
        (VG.Proof.Ed25519.AArch64.PublicKey.pruneValue k (s.mem.readW (s.sp + BitVec.ofNat 64 (192 + 8 * k)) 64)) := by
  have ho : (192 + 8 * k) % 8 = 0 ∧ 192 + 8 * k < 32768 := by omega
  have hs : 32 + 8 * k < 4096 := by omega
  apply WP.of_runBlock
  by_cases h0 : k = 0
  · subst k
    simp only [pruneWord, pruneLow, VG.Proof.Ed25519.AArch64.PublicKey.pruneValue, ite_true, List.cons_append, List.nil_append,
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
      simp only [pruneWord, pruneHigh, VG.Proof.Ed25519.AArch64.PublicKey.pruneValue, h0, ite_true, ite_false,
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
    · simp only [pruneWord, VG.Proof.Ed25519.AArch64.PublicKey.pruneValue, h0, h3, ite_false, List.cons_append, List.nil_append,
        runBlock_cons, runStep_some, runBlock_nil, exec, State.load, Size.bits, Size.bytes,
        State.read, State.store, addr, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
        RegUpd.wr_write, RegUpd.sp_write, RegUpd.v_write, BitVec.setWidth_eq,
        ho, hs, and_self, ite_true, ite_false, reduceCtorEq, Option.map_some,
        Option.bind_some, hr, hw, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, BitVec.add_zero,
        Mem.readW, Mem.writeW, Option.some.injEq, exists_eq_left']
      refine ⟨⟨rfl, rfl, rfl, rfl, ?_⟩, True.intro⟩
      intro r h9 _ h15
      simp only [RegUpd.gpr_write, h9, h15, ite_false]

theorem Step.refl (s : State) : VG.Proof.Ed25519.AArch64.PublicKey.Step s s := ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩

structure PruneInv (s : State) (n : Nat) (t : State) : Prop where
  step : VG.Proof.Ed25519.AArch64.PublicKey.Step s t
  frame : Frame [⟨s.sp + 32, 32⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (s.sp + BitVec.ofNat 64 (32 + 8 * j)) 64 =
    VG.Proof.Ed25519.AArch64.PublicKey.pruneValue j (s.mem.readW (s.sp + BitVec.ofNat 64 (192 + 8 * j)) 64)

theorem prunePrefix_ok {s : State} (hw : (⟨s.sp, 256⟩ : Region) ∈ s.wr) :
    ∀ n ≤ 4, WP isa (.block ((List.range n).flatMap pruneWord)) s (VG.Proof.Ed25519.AArch64.PublicKey.PruneInv s n)
  | 0, _ => WP.block_nil ⟨.refl s, Frame.refl _ _, fun _ h => by omega⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed25519.AArch64.PublicKey.prunePrefix_ok hw n (by omega)) fun u hu => ?_
    have ur : InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (192 + 8 * n)) 8 := by
      rw [hu.step.sp, hu.step.wr]
      exact ⟨_, List.mem_append_right _ hw, Offset.contains_base _ (by omega) (by omega)⟩
    have uw : InRegions u.wr (u.sp + BitVec.ofNat 64 (32 + 8 * n)) 8 := by
      rw [hu.step.sp, hu.step.wr]
      exact ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩
    refine WP.mono (VG.Proof.Ed25519.AArch64.PublicKey.pruneWord_ok (by omega) ur uw) fun t ⟨kt, mt⟩ => ?_
    rw [hu.step.sp] at mt
    have same : u.mem.readW (s.sp + BitVec.ofNat 64 (192 + 8 * n)) 64 =
        s.mem.readW (s.sp + BitVec.ofNat 64 (192 + 8 * n)) 64 := by
      apply hu.frame.readW (Region.contains_self _ _) _ (by decide)
      simp only [List.mem_singleton]
      rintro r rfl
      exact Offset.disjoint _ (e := 32) (k := 32) (by omega) (by omega) (by decide)
    rw [same] at mt
    refine ⟨hu.step.trans kt, ?_, fun j hj => ?_⟩
    · rw [mt]
      exact hu.frame.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (e := 32) (k := 32) (by omega) (by omega) (by decide))
    · rw [mt]
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep ?_ (by decide)]
        · exact hu.words j (by omega)
        · exact Offset.sep _ (by omega) (by omega) (by omega)

theorem decode_words (m : Mem) (p : Addr) :
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32) =
      (m.readW p 64).toNat + 2 ^ 64 * (m.readW (p + 8) 64).toNat +
      2 ^ 128 * (m.readW (p + 16) 64).toNat + 2 ^ 192 * (m.readW (p + 24) 64).toNat := by
  rw [Proof.Ed25519.decodeLE_eq]
  exact Proof.X25519.leNum_bytesAt_words64 m p

/-- Prune the first half of the seed digest into its separate scalar buffer. -/
theorem prune_ok {s : State} (hw : (⟨s.sp, 256⟩ : Region) ∈ s.wr)
    {digest : List Byte} (hh : Spec.Sha512.bytesAt s.mem (s.sp + 192) 64 = digest) :
    WP isa (.block prune) s fun t => VG.Proof.Ed25519.AArch64.PublicKey.Step s t ∧
      Frame [⟨s.sp + 32, 32⟩] s.mem t.mem ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem (s.sp + 32) 32) =
        Spec.Ed25519.prune digest := by
  refine WP.mono (VG.Proof.Ed25519.AArch64.PublicKey.prunePrefix_ok hw 4 (by decide)) fun t ht => ⟨ht.step, ht.frame, ?_⟩
  have take : (Spec.Sha512.bytesAt s.mem (s.sp + 192) 64).take 32 =
      Spec.Ed25519.bytesAt s.mem (s.sp + 192) 32 := by
    simp [Spec.Sha512.bytesAt, Spec.Ed25519.bytesAt, ← List.map_take, List.take_range]
  rw [Spec.Ed25519.prune, ← hh, take, VG.Proof.Ed25519.AArch64.PublicKey.decode_words, VG.Proof.Ed25519.AArch64.PublicKey.decode_words]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have w0 := ht.words 0 (by decide)
  have w1 := ht.words 1 (by decide)
  have w2 := ht.words 2 (by decide)
  have w3 := ht.words 3 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceEqDiff, VG.Proof.Ed25519.AArch64.PublicKey.pruneValue, ↓reduceIte] at w0 w1 w2 w3
  change t.mem.readW (s.sp + (32 : BitVec 64)) 64 = _ at w0
  rw [w0, w1, w2, w3]
  exact (VG.Proof.Ed25519.AArch64.PublicKey.prune_words _ _ _ _).symm

end VG.Proof.Ed25519.AArch64.PublicKey

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.CTCommon`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.PublicKey.Layout`. -/
section
namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

structure Lay where
  out : Addr
  seed : Addr
  scr : Addr
  E : Addr

namespace Lay
variable (L : VG.Proof.Ed25519.AArch64.PublicKey.Lay)
abbrev OUT : Region := ⟨L.out, 32⟩
abbrev SEED : Region := ⟨L.seed, 32⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
abbrev ARGS : Region := Whole.ARGS L.E
abbrev FR : Region := Whole.FR L.E
abbrev STK : Region := ⟨L.E, 336⟩
/-- The frame of a callee, below the locals. -/
abbrev CK : Region := Whole.CK L.E
def inputs : List Region := [L.SEED, L.ARGS]
def outputs : List Region := [L.OUT, L.SCR]
def value (j : Nat) : Addr := match j with | 0 => L.out | 1 => L.seed | _ => L.scr
structure Ok : Prop where
  os : L.OUT.Disjoint L.SEED
  oc : L.OUT.Disjoint L.SCR
  sc : L.SEED.Disjoint L.SCR
  ko : L.STK.Disjoint L.OUT
  ks : L.STK.Disjoint L.SEED
  kc : L.STK.Disjoint L.SCR
  no : L.out.toNat + 32 ≤ 2 ^ 64
  ns : L.seed.toNat + 32 ≤ 2 ^ 64
  nc : L.scr.toNat + 8192 ≤ 2 ^ 64
  e16 : 16 ≤ L.E.toNat
  co : L.CK.Disjoint L.OUT
  cs : L.CK.Disjoint L.SEED
  cc : L.CK.Disjoint L.SCR
end Lay

abbrev Ctx (L : VG.Proof.Ed25519.AArch64.PublicKey.Lay) (g : Reg → Addr) (vec : VReg → BitVec 128) (m₀ : Mem) (t : State) :=
  Whole.Ctx L.E g vec m₀ L.inputs L.outputs t

def Arguments (L : VG.Proof.Ed25519.AArch64.PublicKey.Lay) (m : Mem) : Prop :=
  ∀ j < 3, m.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 = L.value j

def argValue (L : VG.Proof.Ed25519.AArch64.PublicKey.Lay) : Value → Addr
  | .const n => BitVec.ofNat 64 n
  | .frame d => L.E + BitVec.ofNat 64 d
  | .caller j d => L.value j + BitVec.ofNat 64 d

variable {L : VG.Proof.Ed25519.AArch64.PublicKey.Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem frame_sub (L : VG.Proof.Ed25519.AArch64.PublicKey.Lay) : Region.Sub L.FR L.STK := Region.sub_prefix (by decide : 256 ≤ 336)
theorem args_sub (L : VG.Proof.Ed25519.AArch64.PublicKey.Lay) : Region.Sub L.ARGS L.STK := Offset.sub_base _ (by decide : 256 + 48 ≤ 336)

theorem Ctx.seed_bytes (hc : VG.Proof.Ed25519.AArch64.PublicKey.Ctx L g vec m₀ t) (hL : L.Ok) :
    Spec.Ed25519.bytesAt t.mem L.seed 32 = Spec.Ed25519.bytesAt m₀ L.seed 32 := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hc.frame.bytes (R := L.SEED) ?_ (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact hL.os.symm
  · exact hL.sc
  · exact (hL.ks.sub_left (VG.Proof.Ed25519.AArch64.PublicKey.frame_sub L)).symm
  · exact hL.cs.symm

theorem Ctx.arg_word (hc : VG.Proof.Ed25519.AArch64.PublicKey.Ctx L g vec m₀ t) (hL : L.Ok) {j : Nat} (hj : j < 3) :
    t.mem.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 =
      m₀.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 := by
  refine hc.frame.readW (r := L.ARGS)
    (Offset.contains _ (e := 256) (k := 48) (by omega) (by omega) (by decide)) ?_ (by decide)
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact hL.ko.sub_left (VG.Proof.Ed25519.AArch64.PublicKey.args_sub L)
  · exact hL.kc.sub_left (VG.Proof.Ed25519.AArch64.PublicKey.args_sub L)
  · exact Offset.disjoint_base _ (by decide : 256 ≤ 256) (by decide : 256 + 48 ≤ 2 ^ 64)
  · exact ((Offset.below_disjoint L.E (m := 16) (l := 304) (by decide)).sub_right
      (Offset.sub_base _ (by decide : 256 + 48 ≤ 304))).symm

theorem setup_ok (hc : VG.Proof.Ed25519.AArch64.PublicKey.Ctx L g vec m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.PublicKey.Arguments L m₀)
    {args : List (Reg × Value)} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (setup args)) t fun u => VG.Proof.Ed25519.AArch64.PublicKey.Ctx L g vec m₀ u ∧ u.mem = t.mem ∧
      ∀ p ∈ args, u.gpr p.1 = VG.Proof.Ed25519.AArch64.PublicKey.argValue L p.2 := by
  refine WP.mono (hc.setup hn hv (by simp [Lay.inputs]) hr) fun u ⟨hu, hm, hs⟩ => ⟨hu, hm, ?_⟩
  intro p hp
  rw [hs p hp]
  rcases p with ⟨r, v⟩
  cases v with
  | const => rfl
  | frame => rfl
  | caller j d =>
    have hj := hi (r, .caller j d) hp j d rfl
    simp only [Whole.value, VG.Proof.Ed25519.AArch64.PublicKey.argValue]
    change t.mem.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 + BitVec.ofNat 64 d = _
    rw [hc.arg_word hL hj, ha j hj]

end VG.Proof.Ed25519.AArch64.PublicKey
end

/-! Merged from `Proof.Ed25519.AArch64.PublicKey.Base`. -/
section
namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey
open VG.Impl.Ed25519.AArch64.Whole (callWith)

variable {L : VG.Proof.Ed25519.AArch64.PublicKey.Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem base_noFrames : Impl.Ed25519.AArch64.scalarBase.noFrames = true := by lit_decide

def BaseArgs (L : VG.Proof.Ed25519.AArch64.PublicKey.Lay) (t : State) : Prop :=
  t.gpr .x0 = L.out ∧ t.gpr .x1 = L.E + 32 ∧ t.gpr .x2 = L.scr

theorem base_pre (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.PublicKey.BaseArgs L t) :
    scalarBaseLocal.pre (t.callEntry.withRegions [⟨L.E + 32, 32⟩] L.outputs) := by
  obtain ⟨h0, h1, h2⟩ := ha
  simp only [scalarBaseLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h0, h1, h2]
  exact ⟨True.intro, rfl, hL.kc.sub_left (Offset.sub_base _ (by decide : 32 + 32 ≤ 336)), hL.nc⟩

theorem base_covers (L : VG.Proof.Ed25519.AArch64.PublicKey.Lay) : Covers ([⟨L.E + 32, 32⟩] ++ L.outputs)
    (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]
    exact ⟨Whole.FR L.E, List.mem_append_right _ List.mem_cons_self, 32, rfl, by change 32 + 32 ≤ 256; decide⟩
  · exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr), 0, by simp⟩

theorem base_writes (L : VG.Proof.Ed25519.AArch64.PublicKey.Lay) : ∀ r ∈ L.outputs,
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R :=
  fun r hr => .inr ⟨r, hr, 0, (BitVec.add_zero _).symm, by simp⟩

theorem base_call (hc : VG.Proof.Ed25519.AArch64.PublicKey.Ctx L g vec m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.PublicKey.BaseArgs L t) :
    WP isa (.call "vg_ed25519_scalar_base" Impl.Ed25519.AArch64.scalarBase) t fun u =>
      VG.Proof.Ed25519.AArch64.PublicKey.Ctx L g vec m₀ u ∧ Spec.Ed25519.bytesAt u.mem L.out 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt t.mem (L.E + 32) 32) := by
  refine Whole.call_ok hc scalarBase_ok VG.Proof.Ed25519.AArch64.PublicKey.base_noFrames (VG.Proof.Ed25519.AArch64.PublicKey.base_pre hL ha) (VG.Proof.Ed25519.AArch64.PublicKey.base_covers L)
    (VG.Proof.Ed25519.AArch64.PublicKey.base_writes L) fun u hu _ hp => ⟨hu, ?_⟩
  change Spec.Ed25519.bytesAt u.mem (t.callEntry.gpr .x0) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt t.mem (t.callEntry.gpr .x1) 32) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), ha.1, ha.2.1] at hp
  exact hp

theorem prune_step (hc : VG.Proof.Ed25519.AArch64.PublicKey.Ctx L g vec m₀ t) {digest : List Byte}
    (hh : Spec.Ed25519.bytesAt t.mem (L.E + 192) 64 = digest) :
    WP isa (.block prune) t fun u => VG.Proof.Ed25519.AArch64.PublicKey.Ctx L g vec m₀ u ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt u.mem (L.E + 32) 32) = Spec.Ed25519.prune digest := by
  have hwrite : (⟨t.sp, 256⟩ : Region) ∈ t.wr := by rw [hc.sp, hc.wr]; exact List.mem_cons_self
  have hash : Spec.Sha512.bytesAt t.mem (t.sp + 192) 64 = digest := by rw [hc.sp]; exact hh
  refine WP.mono (VG.Proof.Ed25519.AArch64.PublicKey.prune_ok hwrite hash) fun u ⟨hu, hf, hp⟩ => ⟨?_, ?_⟩
  · refine hc.of_frame hu.rd hu.wr hu.sp ?_ ?_ hf ?_
    · intro r hr _
      apply hu.regs r <;> intro h <;> subst r <;> simp [preserved] at hr
    · intro r _; rw [hu.v]
    · rintro r hr
      rw [List.mem_singleton.mp hr, hc.sp]
      exact .inl (Offset.sub_base _ (by decide : 32 + 32 ≤ 256))
  · rw [hc.sp] at hp
    exact hp

theorem base_step (hc : VG.Proof.Ed25519.AArch64.PublicKey.Ctx L g vec m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.PublicKey.Arguments L m₀) {n : Nat}
    (hs : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem (L.E + 32) 32) = n) :
    WP isa (callWith baseArgs "vg_ed25519_scalar_base" Impl.Ed25519.AArch64.scalarBase) t fun u =>
      VG.Proof.Ed25519.AArch64.PublicKey.Ctx L g vec m₀ u ∧ Spec.Ed25519.bytesAt u.mem L.out 32 =
        Spec.Ed25519.encodePoint (Spec.Ed25519.pointMul n Spec.Ed25519.basePoint) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.PublicKey.setup_ok hc hL ha
    (args := [(.x0, .caller 0 0), (.x1, .frame 32), (.x2, .caller 2 0)])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])) fun u ⟨hu, hm, hav⟩ => ?_)
  have h0 := hav (.x0, .caller 0 0) (by simp)
  have h1 := hav (.x1, .frame 32) (by simp)
  have h2 := hav (.x2, .caller 2 0) (by simp)
  simp only [VG.Proof.Ed25519.AArch64.PublicKey.argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  refine WP.mono (VG.Proof.Ed25519.AArch64.PublicKey.base_call hu hL ⟨h0, h1, h2⟩) fun u' ⟨hu', hp⟩ => ⟨hu', ?_⟩
  rw [hp, hm, Spec.Ed25519.scalarBase, hs]

theorem wipe_step (hc : VG.Proof.Ed25519.AArch64.PublicKey.Ctx L g vec m₀ t) (hL : L.Ok) :
    WP isa (.block wipe) t fun u => VG.Proof.Ed25519.AArch64.PublicKey.Ctx L g vec m₀ u ∧
      Spec.Ed25519.bytesAt u.mem L.out 32 = Spec.Ed25519.bytesAt t.mem L.out 32 := by
  refine WP.mono (Whole.Ctx.zeroWords hc (start := 4) (count := 28) (by decide)) fun u ⟨hu, hf, _⟩ => ⟨hu, ?_⟩
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes (R := L.OUT) ?_
    (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rintro r hr
  rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (Offset.sub_base _ (by decide : 8 * 4 + 8 * 28 ≤ 336))).symm

end VG.Proof.Ed25519.AArch64.PublicKey
end

/-! Merged from `Proof.Ed25519.AArch64.PublicKey.Hash`. -/
section
namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey
open VG.Impl.Ed25519.AArch64.Whole (callWith)

variable {L : VG.Proof.Ed25519.AArch64.PublicKey.Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem init_step (hc : VG.Proof.Ed25519.AArch64.PublicKey.Ctx L g vec m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.PublicKey.Arguments L m₀) :
    WP isa (callWith initArgs Spec.Sha512.init512Api.name
      (Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512)) t fun u =>
      VG.Proof.Ed25519.AArch64.PublicKey.Ctx L g vec m₀ u ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem L.scr [] := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.PublicKey.setup_ok hc hL ha (args := [(.x0, .caller 2 0)])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])) fun u ⟨hu, _, hs⟩ => ?_)
  have h0 := hs (.x0, .caller 2 0) (by simp)
  simp only [VG.Proof.Ed25519.AArch64.PublicKey.argValue, Lay.value, BitVec.add_zero] at h0
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact WP.mono (Whole.init_call hu (Whole.init_pre h0) (Whole.covers_writes hw) hw h0)
    fun v ⟨hv, _, hh⟩ => ⟨hv, hh⟩

theorem update_step (v : Whole.Backend) (hc : VG.Proof.Ed25519.AArch64.PublicKey.Ctx L g vec m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.PublicKey.Arguments L m₀)
    (hh : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr []) :
    WP isa (callWith updateArgs (Spec.Sha512.updateScratchApi.name ++ v.suffix) v.update) t fun u =>
      VG.Proof.Ed25519.AArch64.PublicKey.Ctx L g vec m₀ u ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem L.scr
        (Spec.Ed25519.bytesAt m₀ L.seed 32) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.PublicKey.setup_ok hc hL ha
    (args := [(.x0, .caller 2 0), (.x1, .const 0), (.x2, .caller 1 0), (.x3, .const 32), (.x4, .caller 2 192)])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have h0 := hs (.x0, .caller 2 0) (by simp)
  have h1 := hs (.x1, .const 0) (by simp)
  have h2 := hs (.x2, .caller 1 0) (by simp)
  have h3 := hs (.x3, .const 32) (by simp)
  have h4 := hs (.x4, .caller 2 192) (by simp)
  simp only [VG.Proof.Ed25519.AArch64.PublicKey.argValue, Lay.value, BitVec.add_zero] at h0 h1 h2 h3 h4
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  have hp := Whole.update_pre h0 h2 h3 h4 hL.sc (by rw [hu.sp]; exact hL.e16) (by rw [hu.sp]; exact hL.cc)
    (by rw [hu.sp]; exact hL.cs)
  have cv : Covers (Whole.updateRd L.seed 32 ++ Whole.hashWr L.scr)
      (L.inputs ++ Whole.FR L.E :: L.outputs) := by
    intro a n hin
    obtain ⟨r, hr, hh⟩ := hin
    rcases List.mem_append.mp hr with hr | hr
    ·
      simp only [Whole.updateRd, List.mem_singleton] at hr
      subst r
      exact ⟨L.SEED, List.mem_append_left _ (by simp [Lay.inputs]), hh⟩
    · exact Whole.covers_writes hw a n ⟨r, hr, hh⟩
  refine WP.mono (Whole.update_call v hu hp cv hw (prev := []) h0 h2 h3 h1 (hm ▸ hh)) fun u' ⟨hu', _, hr⟩ => ⟨hu', ?_⟩
  simp only [List.nil_append, BitVec.toNat_ofNat] at hr
  rw [hu.seed_bytes hL] at hr
  exact hr

theorem finalize_writes (L : VG.Proof.Ed25519.AArch64.PublicKey.Lay) : ∀ r ∈ Whole.finalizeWr L.scr (L.E + 192),
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by change 0 + 192 ≤ 8192; decide⟩
  · exact .inl ⟨192, rfl, by change 192 + 64 ≤ 256; decide⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 192, rfl, by change 192 + 688 ≤ 8192; decide⟩

theorem finalize_step (v : Whole.Backend) (hc : VG.Proof.Ed25519.AArch64.PublicKey.Ctx L g vec m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.PublicKey.Arguments L m₀)
    (hh : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr (Spec.Ed25519.bytesAt m₀ L.seed 32)) :
    WP isa (callWith finalizeArgs (Spec.Sha512.finalizeScratchApi.name ++ v.suffix) v.finalize) t fun u =>
      VG.Proof.Ed25519.AArch64.PublicKey.Ctx L g vec m₀ u ∧ Spec.Ed25519.bytesAt u.mem (L.E + 192) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m₀ L.seed 32) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.PublicKey.setup_ok hc hL ha
    (args := [(.x0, .caller 2 0), (.x1, .const 32), (.x2, .frame 192), (.x3, .caller 2 192)])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have h0 := hs (.x0, .caller 2 0) (by simp)
  have h1 := hs (.x1, .const 32) (by simp)
  have h2 := hs (.x2, .frame 192) (by simp)
  have h3 := hs (.x3, .caller 2 192) (by simp)
  simp only [VG.Proof.Ed25519.AArch64.PublicKey.argValue, Lay.value, BitVec.add_zero] at h0 h1 h2 h3
  have hd : Region.Disjoint ⟨L.E + 192, 64⟩ L.SCR :=
    hL.kc.sub_left (Offset.sub_base _ (by decide : 192 + 64 ≤ 336))
  have hp := Whole.finalize_pre h0 h2 h3 hd (by rw [hu.sp]; exact hL.e16) (by rw [hu.sp]; exact hL.cc)
    (by rw [hu.sp]; exact Whole.ck_frame (by decide : 192 + 64 ≤ 304))
  have hw := VG.Proof.Ed25519.AArch64.PublicKey.finalize_writes L
  have hl : (Spec.Ed25519.bytesAt m₀ L.seed 32).length = 32 := by
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]
  exact WP.mono (Whole.finalize_call v hu hp (Whole.covers_writes hw) hw h0 h2
    (by rw [hl]; exact h1) (hm ▸ hh) (by rw [hl]; decide)) fun u' ⟨hu', _, hd⟩ => ⟨hu', hd⟩

theorem hash_ok (v : Whole.Backend) (hc : VG.Proof.Ed25519.AArch64.PublicKey.Ctx L g vec m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.PublicKey.Arguments L m₀) :
    WP isa (hash v.code v.suffix) t fun u => VG.Proof.Ed25519.AArch64.PublicKey.Ctx L g vec m₀ u ∧
      Spec.Ed25519.bytesAt u.mem (L.E + 192) 64 = Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m₀ L.seed 32) := by
  exact WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.PublicKey.init_step hc hL ha) fun t₁ ⟨h₁, hh₁⟩ =>
    WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.PublicKey.update_step v h₁ hL ha hh₁) fun t₂ ⟨h₂, hh₂⟩ => VG.Proof.Ed25519.AArch64.PublicKey.finalize_step v h₂ hL ha hh₂))

end VG.Proof.Ed25519.AArch64.PublicKey
end

/-! Merged from `Proof.Ed25519.AArch64.PublicKey.Correct`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.PublicKey.Entry`. -/
section
namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64

def pkLocal : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 32⟩
    let seed : Region := ⟨s.gpr .x1, 32⟩
    let scr : Region := ⟨s.gpr .x2, 8192⟩
    let stk : Region := below s.sp 352
    s.rd = [seed] ∧ s.wr = [out, scr] ∧
      out.Disjoint seed ∧ out.Disjoint scr ∧ seed.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint seed ∧ stk.Disjoint scr ∧
      (s.gpr .x0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 32 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64 ∧ 352 ≤ s.sp.toNat
  post s t := Spec.Ed25519.bytesAt t.mem (s.gpr .x0) 32 =
    Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 32)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2

def lay (s : State) : VG.Proof.Ed25519.AArch64.PublicKey.Lay := ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, Whole.base s⟩

theorem lay_ok {s : State} (h : pkLocal.pre s) : (VG.Proof.Ed25519.AArch64.PublicKey.lay s).Ok := by
  obtain ⟨_, _, os, oc, sc, ko, ks, kc, no, ns, nc, hsp⟩ := h
  exact ⟨os, oc, sc, ko.sub_left (Whole.stk_sub s), ks.sub_left (Whole.stk_sub s),
    kc.sub_left (Whole.stk_sub s), no, ns, nc, Whole.base_16 hsp, ko.sub_left (Whole.ck_sub s),
    ks.sub_left (Whole.ck_sub s), kc.sub_left (Whole.ck_sub s)⟩

theorem entry_below {s : State} (h : pkLocal.pre s) : 352 ≤ s.sp.toNat := h.2.2.2.2.2.2.2.2.2.2.2

theorem entry_writes {s : State} (h : pkLocal.pre s) :
    ∀ r ∈ s.wr, (below s.sp 352).Disjoint r := by
  intro r hr
  rw [h.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.1

theorem entry_ctx {s p : State} (h : pkLocal.pre s) (hp : Whole.Saved (Whole.entered s) 6 p) :
    VG.Proof.Ed25519.AArch64.PublicKey.Ctx (VG.Proof.Ed25519.AArch64.PublicKey.lay s) s.gpr s.v p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  simpa only [Whole.bodyRd, h.1, Whole.bodyWr, h.2.1, VG.Proof.Ed25519.AArch64.PublicKey.Ctx, Lay.inputs, Lay.outputs,
    Lay.SEED, Lay.OUT, Lay.SCR, Lay.ARGS, VG.Proof.Ed25519.AArch64.PublicKey.lay, List.cons_append, List.nil_append] using hc

theorem entry_args {s p : State} (hp : Whole.Saved (Whole.entered s) 6 p) : VG.Proof.Ed25519.AArch64.PublicKey.Arguments (VG.Proof.Ed25519.AArch64.PublicKey.lay s) p.mem := by
  intro j hj
  have hw := Whole.saved_words hp (j := j) (by omega)
  have he : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases he with rfl | rfl | rfl <;> exact hw

def satState : State where
  gpr r := match r with | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x4000 | _ => 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩]

theorem pk_implies : pkLocal.Implies (Spec.Ed25519.publicKeyContract AArch64.abi 352) := by
  sig_implies [Spec.Ed25519.publicKeyContract, Spec.Ed25519.publicKeySig,
    Spec.Ed25519.scratchWords, VG.Proof.Ed25519.AArch64.PublicKey.pkLocal, below, AArch64.abi, AArch64.argRegs]
    [satState] using VG.Proof.Ed25519.AArch64.PublicKey.satState

end VG.Proof.Ed25519.AArch64.PublicKey
end

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey

variable {L : VG.Proof.Ed25519.AArch64.PublicKey.Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem body_ok (v : Whole.Backend) (hc : VG.Proof.Ed25519.AArch64.PublicKey.Ctx L g vec m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.PublicKey.Arguments L m₀) :
    WP isa (body v.code v.suffix) t fun u => VG.Proof.Ed25519.AArch64.PublicKey.Ctx L g vec m₀ u ∧
      Spec.Ed25519.bytesAt u.mem L.out 32 = Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ L.seed 32) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.PublicKey.hash_ok v hc hL ha) fun u ⟨hu, hh⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.PublicKey.prune_step hu hh) fun u' ⟨hu', hs⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.PublicKey.base_step hu' hL ha hs) fun u'' ⟨hu'', hp⟩ => ?_)
  exact WP.mono (VG.Proof.Ed25519.AArch64.PublicKey.wipe_step hu'' hL) fun w ⟨hw, hm⟩ => ⟨hw, hm.trans hp⟩

theorem body_depth (v : Whole.Backend) : (body v.code v.suffix).aarch64Depth ≤ 1 := by
  have hu := Whole.update_depth v
  have hf := Whole.finalize_depth v
  change (Impl.Sha512.AArch64.Stream.updateWith v.suffix v.code).aarch64Depth ≤ 1 at hu
  change (Impl.Sha512.AArch64.Stream.finalizeWith v.suffix v.code).aarch64Depth ≤ 1 at hf
  have hb := Whole.depth_zero_of_noFrames VG.Proof.Ed25519.AArch64.PublicKey.base_noFrames
  simp only [body, Impl.Ed25519.AArch64.PublicKey.hash, Impl.Ed25519.AArch64.Whole.callWith,
    Code.aarch64Depth, Nat.max_le, Impl.Sha512.AArch64.Stream.init, hb]
  omega

theorem publicKey_ok (v : Whole.Backend) {s : State} (h : pkLocal.pre s) :
    WP isa (code v.code v.suffix) s fun u => abiPreserved s u ∧ pkLocal.post s u := by
  have hw := Whole.wrap_ok (VG.Proof.Ed25519.AArch64.PublicKey.body_depth v) (VG.Proof.Ed25519.AArch64.PublicKey.entry_below h) (VG.Proof.Ed25519.AArch64.PublicKey.entry_writes h)
    (P := fun m m' _ => Spec.Ed25519.bytesAt m' (s.gpr .x0) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m (s.gpr .x1) 32))
    (fun p hp => WP.mono (VG.Proof.Ed25519.AArch64.PublicKey.body_ok v (VG.Proof.Ed25519.AArch64.PublicKey.entry_ctx h hp) (VG.Proof.Ed25519.AArch64.PublicKey.lay_ok h) (VG.Proof.Ed25519.AArch64.PublicKey.entry_args hp)) fun u ⟨hu, ho⟩ => ⟨by
      simpa only [Whole.bodyRd, h.1, VG.Proof.Ed25519.AArch64.PublicKey.Ctx, Lay.inputs, Lay.outputs, Lay.SEED, Lay.OUT,
        Lay.SCR, Lay.ARGS, VG.Proof.Ed25519.AArch64.PublicKey.lay, h.2.1, List.cons_append, List.nil_append] using hu, ho⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  have hs : Spec.Ed25519.bytesAt m (s.gpr .x1) 32 = Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 32 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun i hi => hf.bytes (R := ⟨s.gpr .x1, 32⟩) ?_
      (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact (VG.Proof.Ed25519.AArch64.PublicKey.lay_ok h).ks.symm
  change Spec.Ed25519.bytesAt u.mem (s.gpr .x0) 32 = _
  rw [hp, hs]

end VG.Proof.Ed25519.AArch64.PublicKey
end

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

abbrev Two (L : VG.Proof.Ed25519.AArch64.PublicKey.Lay) (g₁ g₂ : Reg → Addr) (v₁ v₂ : VReg → BitVec 128) (m₁ m₂ : Mem)
    (P : State → Prop) (a b : State) := (VG.Proof.Ed25519.AArch64.PublicKey.Ctx L g₁ v₁ m₁ a ∧ P a) ∧ (VG.Proof.Ed25519.AArch64.PublicKey.Ctx L g₂ v₂ m₂ b ∧ P b)

def Slots (L : VG.Proof.Ed25519.AArch64.PublicKey.Lay) (args : List (Reg × Value)) (s : State) := ∀ p ∈ args, s.gpr p.1 = VG.Proof.Ed25519.AArch64.PublicKey.argValue L p.2

variable {L : VG.Proof.Ed25519.AArch64.PublicKey.Lay} {g₁ g₂ : Reg → Addr} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem setup_ct (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.PublicKey.Arguments L m₁) (hb : VG.Proof.Ed25519.AArch64.PublicKey.Arguments L m₂)
    (args : List (Reg × Value)) (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setup args)) hint).isSome = true) :
    RelCT isa (VG.Proof.Ed25519.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block (setup args))
      (VG.Proof.Ed25519.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ (VG.Proof.Ed25519.AArch64.PublicKey.Slots L args)) := by
  refine Whole.rel_wp (Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) ht) ?_ ?_
  · intro t ⟨hc, _⟩
    exact WP.mono (VG.Proof.Ed25519.AArch64.PublicKey.setup_ok hc hL ha hn hv hi hr) fun _ ⟨hc, _, hs⟩ => ⟨hc, hs⟩
  · intro t ⟨hc, _⟩
    exact WP.mono (VG.Proof.Ed25519.AArch64.PublicKey.setup_ok hc hL hb hn hv hi hr) fun _ ⟨hc, _, hs⟩ => ⟨hc, hs⟩

theorem call_ct {args : List (Reg × Value)} {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (hd : c.aarch64Depth ≤ 1)
    (ready : ∀ t, t.sp = L.E → VG.Proof.Ed25519.AArch64.PublicKey.Slots L args t → Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, a.sp = b.sp →
      (∀ p ∈ args, a.callEntry.gpr p.1 = b.callEntry.gpr p.1) →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw))
    (hl : ∀ p ∈ args, p.1 ∉ linkRegs) :
    RelCT isa (VG.Proof.Ed25519.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ (VG.Proof.Ed25519.AArch64.PublicKey.Slots L args)) (.call name c)
      (VG.Proof.Ed25519.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp ?_ ?_ ?_
  · refine Whole.callEx correct ct fun a b h => ?_
    let ra := ready a h.1.1.sp h.1.2
    let rb := ready b h.2.1.sp h.2.2
    obtain ⟨ca, wa⟩ := ra.covers_state h.1.1
    obtain ⟨cb, wb⟩ := rb.covers_state h.2.1
    refine ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ (h.1.1.sp.trans h.2.1.sp.symm) ?_, ca, wa, cb, wb⟩
    intro p hp
    rw [State.callEntry_gpr _ (hl p hp), State.callEntry_gpr _ (hl p hp), h.1.2 p hp, h.2.2 p hp]
  · intro t ⟨hc, hs⟩
    exact WP.mono ((ready t hc.sp hs).wpF hc correct hd) fun _ hu => ⟨hu, trivial⟩
  · intro t ⟨hc, hs⟩
    exact WP.mono ((ready t hc.sp hs).wpF hc correct hd) fun _ hu => ⟨hu, trivial⟩

end VG.Proof.Ed25519.AArch64.PublicKey

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Verified`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.PublicKey.CT`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.PublicKey.CTReady`. -/
section
namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

def initValues : List (Reg × Value) := [(.x0, .caller 2 0)]
def updateValues : List (Reg × Value) :=
  [(.x0, .caller 2 0), (.x1, .const 0), (.x2, .caller 1 0), (.x3, .const 32), (.x4, .caller 2 192)]
def finalizeValues : List (Reg × Value) :=
  [(.x0, .caller 2 0), (.x1, .const 32), (.x2, .frame 192), (.x3, .caller 2 192)]
def baseValues : List (Reg × Value) := [(.x0, .caller 0 0), (.x1, .frame 32), (.x2, .caller 2 0)]

variable {L : VG.Proof.Ed25519.AArch64.PublicKey.Lay} {t : State}

def init_ready (hs : VG.Proof.Ed25519.AArch64.PublicKey.Slots L VG.Proof.Ed25519.AArch64.PublicKey.initValues t) :
    Whole.CallReady (Proof.Sha512.initAArch64 Spec.Sha512.H0_512) L.E L.inputs L.outputs t := by
  have h0 := hs (.x0, .caller 2 0) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.initValues])
  simp only [VG.Proof.Ed25519.AArch64.PublicKey.argValue, Lay.value, BitVec.add_zero] at h0
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨[], Whole.initWr L.scr, Whole.init_pre h0, Whole.covers_writes hw, hw⟩

def update_ready (hL : L.Ok) (hsp : t.sp = L.E) (hs : VG.Proof.Ed25519.AArch64.PublicKey.Slots L VG.Proof.Ed25519.AArch64.PublicKey.updateValues t) :
    Whole.CallReady Proof.Sha512.updateAArch64 L.E L.inputs L.outputs t := by
  have h0 := hs (.x0, .caller 2 0) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.updateValues])
  have h2 := hs (.x2, .caller 1 0) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.updateValues])
  have h3 := hs (.x3, .const 32) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.updateValues])
  have h4 := hs (.x4, .caller 2 192) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.updateValues])
  simp only [VG.Proof.Ed25519.AArch64.PublicKey.argValue, Lay.value, BitVec.add_zero] at h0 h2 h3 h4
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  refine ⟨Whole.updateRd L.seed 32, Whole.hashWr L.scr, Whole.update_pre h0 h2 h3 h4 hL.sc
    (by rw [hsp]; exact hL.e16) (by rw [hsp]; exact hL.cc) (by rw [hsp]; exact hL.cs), ?_, hw⟩
  intro a n hin
  obtain ⟨r, hr, hh⟩ := hin
  rcases List.mem_append.mp hr with hr | hr
  · simp only [Whole.updateRd, List.mem_singleton] at hr
    subst r
    exact ⟨L.SEED, List.mem_append_left _ (by simp [Lay.inputs]), hh⟩
  · exact Whole.covers_writes hw a n ⟨r, hr, hh⟩

def finalize_ready (hL : L.Ok) (hsp : t.sp = L.E) (hs : VG.Proof.Ed25519.AArch64.PublicKey.Slots L VG.Proof.Ed25519.AArch64.PublicKey.finalizeValues t) :
    Whole.CallReady Proof.Sha512.finalizeAArch64 L.E L.inputs L.outputs t := by
  have h0 := hs (.x0, .caller 2 0) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.finalizeValues])
  have h2 := hs (.x2, .frame 192) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.finalizeValues])
  have h3 := hs (.x3, .caller 2 192) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.finalizeValues])
  simp only [VG.Proof.Ed25519.AArch64.PublicKey.argValue, Lay.value, BitVec.add_zero] at h0 h2 h3
  have hd : Region.Disjoint ⟨L.E + 192, 64⟩ L.SCR :=
    hL.kc.sub_left (Offset.sub_base _ (by decide : 192 + 64 ≤ 336))
  exact ⟨[], Whole.finalizeWr L.scr (L.E + 192), Whole.finalize_pre h0 h2 h3 hd
    (by rw [hsp]; exact hL.e16) (by rw [hsp]; exact hL.cc)
    (by rw [hsp]; exact Whole.ck_frame (by decide : 192 + 64 ≤ 304)),
    Whole.covers_writes (VG.Proof.Ed25519.AArch64.PublicKey.finalize_writes L), VG.Proof.Ed25519.AArch64.PublicKey.finalize_writes L⟩

def base_ready (hL : L.Ok) (hs : VG.Proof.Ed25519.AArch64.PublicKey.Slots L VG.Proof.Ed25519.AArch64.PublicKey.baseValues t) :
    Whole.CallReady scalarBaseLocal L.E L.inputs L.outputs t := by
  have h0 := hs (.x0, .caller 0 0) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.baseValues])
  have h1 := hs (.x1, .frame 32) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.baseValues])
  have h2 := hs (.x2, .caller 2 0) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.baseValues])
  simp only [VG.Proof.Ed25519.AArch64.PublicKey.argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  exact ⟨[⟨L.E + 32, 32⟩], L.outputs, VG.Proof.Ed25519.AArch64.PublicKey.base_pre hL ⟨h0, h1, h2⟩, VG.Proof.Ed25519.AArch64.PublicKey.base_covers L, VG.Proof.Ed25519.AArch64.PublicKey.base_writes L⟩

end VG.Proof.Ed25519.AArch64.PublicKey
end

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey

variable {L : VG.Proof.Ed25519.AArch64.PublicKey.Lay} {g₁ g₂ : Reg → Addr} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem init_ct : RelCT isa (VG.Proof.Ed25519.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ (VG.Proof.Ed25519.AArch64.PublicKey.Slots L VG.Proof.Ed25519.AArch64.PublicKey.initValues))
    (.call Spec.Sha512.init512Api.name (Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512))
    (VG.Proof.Ed25519.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed25519.AArch64.PublicKey.call_ct (Proof.Sha512.AArch64.Stream.init_verified _).1
    (Proof.Sha512.AArch64.Stream.init_verified _).2.1 (Whole.depth_of_noFrames rfl) (fun _ _ h => VG.Proof.Ed25519.AArch64.PublicKey.init_ready h)
  · intro a b ar aw br bw hsp hg
    exact ⟨hg (.x0, .caller 2 0) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.initValues]), hsp⟩
  · simp [VG.Proof.Ed25519.AArch64.PublicKey.initValues, linkRegs]

theorem update_ct (v : Whole.Backend) (hL : L.Ok) :
    RelCT isa (VG.Proof.Ed25519.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ (VG.Proof.Ed25519.AArch64.PublicKey.Slots L VG.Proof.Ed25519.AArch64.PublicKey.updateValues))
      (.call (Spec.Sha512.updateScratchApi.name ++ v.suffix) v.update)
      (VG.Proof.Ed25519.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed25519.AArch64.PublicKey.call_ct v.update_verified.1 v.update_verified.2.1 (Whole.update_depth v) (fun _ hsp h => VG.Proof.Ed25519.AArch64.PublicKey.update_ready hL hsp h)
  · intro a b ar aw br bw hsp hg
    exact ⟨hg (.x0, .caller 2 0) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.updateValues]), hg (.x1, .const 0) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.updateValues]),
      hg (.x2, .caller 1 0) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.updateValues]), hg (.x3, .const 32) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.updateValues]),
      hg (.x4, .caller 2 192) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.updateValues]), hsp⟩
  · simp [VG.Proof.Ed25519.AArch64.PublicKey.updateValues, linkRegs]

theorem finalize_ct (v : Whole.Backend) (hL : L.Ok) :
    RelCT isa (VG.Proof.Ed25519.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ (VG.Proof.Ed25519.AArch64.PublicKey.Slots L VG.Proof.Ed25519.AArch64.PublicKey.finalizeValues))
      (.call (Spec.Sha512.finalizeScratchApi.name ++ v.suffix) v.finalize)
      (VG.Proof.Ed25519.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed25519.AArch64.PublicKey.call_ct v.finalize_verified.1 v.finalize_verified.2.1 (Whole.finalize_depth v) (fun _ hsp h => VG.Proof.Ed25519.AArch64.PublicKey.finalize_ready hL hsp h)
  · intro a b ar aw br bw hsp hg
    exact ⟨hg (.x0, .caller 2 0) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.finalizeValues]), hg (.x1, .const 32) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.finalizeValues]),
      hg (.x2, .frame 192) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.finalizeValues]), hg (.x3, .caller 2 192) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.finalizeValues]), hsp⟩
  · simp [VG.Proof.Ed25519.AArch64.PublicKey.finalizeValues, linkRegs]

theorem base_ct (hL : L.Ok) : RelCT isa (VG.Proof.Ed25519.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ (VG.Proof.Ed25519.AArch64.PublicKey.Slots L VG.Proof.Ed25519.AArch64.PublicKey.baseValues))
    (.call "vg_ed25519_scalar_base" Impl.Ed25519.AArch64.scalarBase)
    (VG.Proof.Ed25519.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply VG.Proof.Ed25519.AArch64.PublicKey.call_ct scalarBase_ok scalarBase_ct (Whole.depth_of_noFrames VG.Proof.Ed25519.AArch64.PublicKey.base_noFrames) (fun _ _ h => VG.Proof.Ed25519.AArch64.PublicKey.base_ready hL h)
  · intro a b ar aw br bw hsp hg
    exact ⟨hsp, hg (.x0, .caller 0 0) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.baseValues]), hg (.x1, .frame 32) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.baseValues]),
      hg (.x2, .caller 2 0) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.baseValues])⟩
  · simp [VG.Proof.Ed25519.AArch64.PublicKey.baseValues, linkRegs]

theorem prune_ct : RelCT isa (VG.Proof.Ed25519.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block prune)
    (VG.Proof.Ed25519.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp (Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (by taint_decide)) ?_ ?_
  · intro t ⟨hc, _⟩
    exact WP.mono (VG.Proof.Ed25519.AArch64.PublicKey.prune_step hc (digest := Spec.Ed25519.bytesAt t.mem (L.E + 192) 64) rfl)
      fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, _⟩
    exact WP.mono (VG.Proof.Ed25519.AArch64.PublicKey.prune_step hc (digest := Spec.Ed25519.bytesAt t.mem (L.E + 192) 64) rfl)
      fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

theorem wipe_ct (hL : L.Ok) : RelCT isa (VG.Proof.Ed25519.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block wipe)
    (VG.Proof.Ed25519.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp (Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (by taint_decide)) ?_ ?_
  · intro t ⟨hc, _⟩; exact WP.mono (VG.Proof.Ed25519.AArch64.PublicKey.wipe_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, _⟩; exact WP.mono (VG.Proof.Ed25519.AArch64.PublicKey.wipe_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

theorem body_ct (v : Whole.Backend) (hL : L.Ok) (ha : VG.Proof.Ed25519.AArch64.PublicKey.Arguments L m₁) (hb : VG.Proof.Ed25519.AArch64.PublicKey.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed25519.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (body v.code v.suffix)
      (VG.Proof.Ed25519.AArch64.PublicKey.Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have i := VG.Proof.Ed25519.AArch64.PublicKey.setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb VG.Proof.Ed25519.AArch64.PublicKey.initValues
    (by decide) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.initValues, Whole.valid]) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.initValues])
    (by simp [VG.Proof.Ed25519.AArch64.PublicKey.initValues, preserved]) (by taint_decide)
  have u := VG.Proof.Ed25519.AArch64.PublicKey.setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb VG.Proof.Ed25519.AArch64.PublicKey.updateValues
    (by decide) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.updateValues, Whole.valid]) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.updateValues])
    (by simp [VG.Proof.Ed25519.AArch64.PublicKey.updateValues, preserved]) (by taint_decide)
  have f := VG.Proof.Ed25519.AArch64.PublicKey.setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb VG.Proof.Ed25519.AArch64.PublicKey.finalizeValues
    (by decide) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.finalizeValues, Whole.valid]) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.finalizeValues])
    (by simp [VG.Proof.Ed25519.AArch64.PublicKey.finalizeValues, preserved]) (by taint_decide)
  have b := VG.Proof.Ed25519.AArch64.PublicKey.setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb VG.Proof.Ed25519.AArch64.PublicKey.baseValues
    (by decide) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.baseValues, Whole.valid]) (by simp [VG.Proof.Ed25519.AArch64.PublicKey.baseValues])
    (by simp [VG.Proof.Ed25519.AArch64.PublicKey.baseValues, preserved]) (by taint_decide)
  exact ((i.seq VG.Proof.Ed25519.AArch64.PublicKey.init_ct).seq ((u.seq (VG.Proof.Ed25519.AArch64.PublicKey.update_ct v hL)).seq (f.seq (VG.Proof.Ed25519.AArch64.PublicKey.finalize_ct v hL)))).seq
    (prune_ct.seq ((b.seq (VG.Proof.Ed25519.AArch64.PublicKey.base_ct hL)).seq (VG.Proof.Ed25519.AArch64.PublicKey.wipe_ct hL)))

theorem lay_eq {s t : State} (hp : pkLocal.pub s t) : VG.Proof.Ed25519.AArch64.PublicKey.lay s = VG.Proof.Ed25519.AArch64.PublicKey.lay t := by
  obtain ⟨sp, h0, h1, h2⟩ := hp
  simp only [VG.Proof.Ed25519.AArch64.PublicKey.lay, Whole.base, sp, h0, h1, h2]

theorem publicKey_ct (v : Whole.Backend) : ConstantTime isa pkLocal.pre pkLocal.pub (code v.code v.suffix) := by
  refine Whole.wrap_ct (fun _ _ hp => hp.1) ?_ ?_
  · intro s hs p hp
    exact WP.mono (VG.Proof.Ed25519.AArch64.PublicKey.body_ok v (VG.Proof.Ed25519.AArch64.PublicKey.entry_ctx hs hp) (VG.Proof.Ed25519.AArch64.PublicKey.lay_ok hs) (VG.Proof.Ed25519.AArch64.PublicKey.entry_args hp)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := VG.Proof.Ed25519.AArch64.PublicKey.lay_eq hp
    have hq : VG.Proof.Ed25519.AArch64.PublicKey.Ctx (VG.Proof.Ed25519.AArch64.PublicKey.lay s) t.gpr t.v q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ VG.Proof.Ed25519.AArch64.PublicKey.entry_ctx ht hqb
    have hqa : VG.Proof.Ed25519.AArch64.PublicKey.Arguments (VG.Proof.Ed25519.AArch64.PublicKey.lay s) q.mem := he ▸ VG.Proof.Ed25519.AArch64.PublicKey.entry_args hqb
    exact ⟨(VG.Proof.Ed25519.AArch64.PublicKey.body_ct v (VG.Proof.Ed25519.AArch64.PublicKey.lay_ok hs) (VG.Proof.Ed25519.AArch64.PublicKey.entry_args hpa) hqa _ _ _ _ _ _
      ⟨⟨VG.Proof.Ed25519.AArch64.PublicKey.entry_ctx hs hpa, trivial⟩, ⟨hq, trivial⟩⟩ ea eb).1, trivial⟩

end VG.Proof.Ed25519.AArch64.PublicKey
end

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey

theorem publicKey_verified (v : Whole.Backend) :
    Verified AArch64.target (code v.code v.suffix) (Spec.Ed25519.publicKeyContract AArch64.abi 352) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => VG.Proof.Ed25519.AArch64.PublicKey.publicKey_ok v h) (VG.Proof.Ed25519.AArch64.PublicKey.publicKey_ct v) (.refl pk_implies.sat_left))
    VG.Proof.Ed25519.AArch64.PublicKey.pk_implies

end VG.Proof.Ed25519.AArch64.PublicKey

end
