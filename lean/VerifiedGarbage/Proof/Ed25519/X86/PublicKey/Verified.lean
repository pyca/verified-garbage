import VerifiedGarbage.Proof.Ed25519.X86.Whole.Wipe
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Impl.Ed25519.X86.PublicKey
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseVerified
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Sha512.X86.Compress
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Layout`. -/
section

namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86

def pkRd (s : State) : List Region := [⟨(VG.X86.arg s 1).setWidth 64, 32⟩, ⟨argAddr s 0, 12⟩]
def pkWr (s : State) : List Region := [⟨(VG.X86.arg s 0).setWidth 64, 32⟩, ⟨(VG.X86.arg s 2).setWidth 64, 8192⟩]

def pkLocal : Contract isa where
  pre s :=
    let out : Region := ⟨(VG.X86.arg s 0).setWidth 64, 32⟩
    let seed : Region := ⟨(VG.X86.arg s 1).setWidth 64, 32⟩
    let scratch : Region := ⟨(VG.X86.arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := below (s.gpr .esp) 280
    s.rd = pkRd s ∧ s.wr = pkWr s ∧ out.Disjoint seed ∧ out.Disjoint scratch ∧
      seed.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ stack.Disjoint out ∧
      stack.Disjoint seed ∧ stack.Disjoint scratch ∧
      (VG.X86.arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (VG.X86.arg s 1).toNat + 32 ≤ 2 ^ 32 ∧
      (VG.X86.arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ (s.gpr .esp).toNat ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s t := Spec.Ed25519.bytesAt t.mem ((VG.X86.arg s 0).setWidth 64) 32 =
    Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem ((VG.X86.arg s 1).setWidth 64) 32)
  pub s t := s.gpr .esp = t.gpr .esp ∧ VG.X86.arg s 0 = VG.X86.arg t 0 ∧ VG.X86.arg s 1 = VG.X86.arg t 1 ∧ VG.X86.arg s 2 = VG.X86.arg t 2

abbrev esp (s : State) : BitVec 32 := s.gpr .esp - BitVec.ofNat 32 256
abbrev Ctx (s t : State) : Prop := Whole.Ctx (VG.Proof.Ed25519.X86.PublicKey.esp s) s.gpr s.mem (pkRd s) (pkWr s) t

structure Bounds (s : State) : Prop where
  out : (VG.X86.arg s 0).toNat + 32 ≤ 2 ^ 32
  seed : (VG.X86.arg s 1).toNat + 32 ≤ 2 ^ 32
  scratch : (VG.X86.arg s 2).toNat + 8192 ≤ 2 ^ 32
  below : 280 ≤ (s.gpr .esp).toNat
  above : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32

theorem bounds {s : State} (h : pkLocal.pre s) : Bounds s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, a, b, c, d, e⟩ := h
  exact ⟨a, b, c, d, e⟩

theorem Bounds.frame {s : State} (h : Bounds s) : (VG.Proof.Ed25519.X86.PublicKey.esp s).toNat + 272 ≤ 2 ^ 32 := by
  rw [sub_toNat (by have := h.below; omega)]
  have := h.above
  omega

theorem Bounds.call {s : State} (h : Bounds s) : 24 ≤ (VG.Proof.Ed25519.X86.PublicKey.esp s).toNat := by
  rw [sub_toNat (by have := h.below; omega)]
  have := h.below
  omega

theorem stack_eq {s : State} (h : Bounds s) : Whole.STK (VG.Proof.Ed25519.X86.PublicKey.esp s) = below (s.gpr .esp) 280 := by
  simp only [Whole.STK, below, VG.Proof.Ed25519.X86.PublicKey.esp]
  rw [Taint.sub_setWidth (by have := h.below; omega : 256 ≤ (s.gpr .esp).toNat),
    Taint.sub_setWidth h.below, BitVec.sub_sub]
  rfl

/-- Pushing the caller-saved EAX allocates locals without changing callee-saved registers. -/
theorem push_ctx {s : State} (h : pkLocal.pre s) :
    VG.Proof.Ed25519.X86.PublicKey.Ctx s (pushed (List.replicate 64 .eax) s) := by
  have hb := bounds h
  have hf := pushed_frame (s := s) (rs := List.replicate 64 .eax) (by simp)
    (by simp only [List.length_replicate]; have := hb.below; omega)
  refine ⟨(pushed_rd _ _).trans h.1, ?_, ?_, fun r _ hn => pushed_gpr _ _ hn, ?_⟩
  · rw [pushed_wr, h.2.1]
    simp only [List.length_replicate]
  · rw [pushed_esp, List.length_replicate]
  · refine Frame.sub hf fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨Whole.STK (VG.Proof.Ed25519.X86.PublicKey.esp s), List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
    rw [stack_eq hb]
    exact below_sub (by simp) hb.below

abbrev OUT (s : State) : Region := ⟨(VG.X86.arg s 0).setWidth 64, 32⟩
abbrev SEED (s : State) : Region := ⟨(VG.X86.arg s 1).setWidth 64, 32⟩
abbrev SCR (s : State) : Region := ⟨(VG.X86.arg s 2).setWidth 64, 8192⟩
abbrev ARGS (s : State) : Region := ⟨argAddr s 0, 12⟩
abbrev RET (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩

structure Facts (s : State) : Prop extends Bounds s where
  os : (OUT s).Disjoint (SEED s)
  oc : (OUT s).Disjoint (SCR s)
  sc : (SEED s).Disjoint (SCR s)
  ao : (VG.Proof.Ed25519.X86.PublicKey.ARGS s).Disjoint (OUT s)
  ac : (VG.Proof.Ed25519.X86.PublicKey.ARGS s).Disjoint (SCR s)
  ro : (RET s).Disjoint (OUT s)
  rc : (RET s).Disjoint (SCR s)
  ko : (Whole.STK (VG.Proof.Ed25519.X86.PublicKey.esp s)).Disjoint (OUT s)
  ks : (Whole.STK (VG.Proof.Ed25519.X86.PublicKey.esp s)).Disjoint (SEED s)
  kc : (Whole.STK (VG.Proof.Ed25519.X86.PublicKey.esp s)).Disjoint (SCR s)

theorem facts {s : State} (h : pkLocal.pre s) : Facts s := by
  have hb := bounds h
  obtain ⟨_, _, os, oc, sc, ao, ac, ro, rc, ko, ks, kc, _⟩ := h
  exact ⟨hb, os, oc, sc, ao, ac, ro, rc, stack_eq hb ▸ ko, stack_eq hb ▸ ks, stack_eq hb ▸ kc⟩

theorem arg_address (s : State) (j : Nat) : addr (VG.Proof.Ed25519.X86.PublicKey.esp s) (260 + 4 * j) = argAddr s j := by
  simp only [addr, VG.Proof.Ed25519.X86.PublicKey.esp, argAddr]
  rw [show 260 + 4 * j = 256 + (4 + 4 * j) by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem arg_address64 {s : State} (h : Bounds s) {j : Nat} (hj : j < 3) :
    argAddr s j = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * j) :=
  addr_eq (by have := h.above; omega)

theorem args_stack {s : State} (h : Bounds s) : (VG.Proof.Ed25519.X86.PublicKey.ARGS s).Disjoint (Whole.STK (VG.Proof.Ed25519.X86.PublicKey.esp s)) := by
  rw [stack_eq h]
  change Region.Disjoint ⟨argAddr s 0, 12⟩ ⟨((s.gpr .esp) - BitVec.ofNat 32 280).setWidth 64, 280⟩
  rw [arg_address64 h (by decide), Taint.sub_setWidth h.below]
  exact (Offset.disjoint_below_above _ (m := 280) (a := 4) (l := 12) (by decide)).symm

theorem args_contains {s : State} (h : Bounds s) {j : Nat} (hj : j < 3) :
    (VG.Proof.Ed25519.X86.PublicKey.ARGS s).Contains (argAddr s j) 4 := by
  change (⟨argAddr s 0, 12⟩ : Region).Contains _ _
  rw [arg_address64 h (by decide), arg_address64 h hj]
  exact Offset.contains _ (by omega) (by omega) (by decide)

theorem original_arg {s t : State} (h : Facts s) (hc : VG.Proof.Ed25519.X86.PublicKey.Ctx s t) {j : Nat} (hj : j < 3) :
    t.mem.readW (addr (VG.Proof.Ed25519.X86.PublicKey.esp s) (260 + 4 * j)) 32 = VG.X86.arg s j := by
  rw [arg_address]
  exact hc.frame.readW (args_contains h.toBounds hj) (by
    simp only [pkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact h.ao
    · exact h.ac
    · exact args_stack h.toBounds) (by decide)

theorem original_arg_readable {s t : State} (h : Facts s) (hc : VG.Proof.Ed25519.X86.PublicKey.Ctx s t) {j : Nat} (hj : j < 3) :
    InRegions (t.rd ++ t.wr) (addr (VG.Proof.Ed25519.X86.PublicKey.esp s) (260 + 4 * j)) 4 := by
  rw [arg_address, hc.rd]
  exact ⟨VG.Proof.Ed25519.X86.PublicKey.ARGS s, List.mem_append_left _ (by simp [pkRd]), args_contains h.toBounds hj⟩

end VG.Proof.Ed25519.X86.PublicKey

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Prune`. -/
section

/-! Merged from `Proof.Ed25519.X86.PublicKey.PruneArithmetic`. -/
section
namespace VG.Proof.Ed25519.X86.PublicKey
open VG

theorem and_sub8 (x k : Nat) (hk : 3 ≤ k) : x &&& (2 ^ k - 8) = 8 * (x / 8 % 2 ^ (k - 3)) := by
  have e : 2 ^ k - 8 = 2 ^ 3 * (2 ^ (k - 3) - 1) := by
    rw [Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, Nat.add_sub_cancel' hk]
    rfl
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
    BitVec.toNat_ofNat, c₁, c₂, c₃, and_sub8 _ 32 (by omega), and_sub8 _ 254 (by omega),
    Nat.and_two_pow_sub_one_eq_mod, or_two_pow (Nat.mod_lt _ (by omega)), or_two_pow (by omega)]
  simp only [show (2 : Nat) ^ (254 - 3) = 2 ^ 251 from rfl, show (2 : Nat) ^ (32 - 3) = 2 ^ 29 from rfl]
  omega

end VG.Proof.Ed25519.X86.PublicKey
end

namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey

def pruneValue (k : Nat) (x : BitVec 32) : BitVec 32 :=
  if k = 0 then x &&& 0xfffffff8
  else if k = 7 then (x &&& 0x3fffffff) ||| 0x40000000 else x

structure Step (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  regs : ∀ r, r ≠ .eax → t.gpr r = s.gpr r

theorem Step.refl (s : State) : Step s s := ⟨rfl, rfl, fun _ _ => rfl⟩
theorem Step.trans {s t u : State} (a : Step s t) (b : Step t u) : Step s u :=
  ⟨b.rd.trans a.rd, b.wr.trans a.wr, fun r h => (b.regs r h).trans (a.regs r h)⟩
theorem Step.esp {s t : State} (h : Step s t) : t.gpr .esp = s.gpr .esp := h.regs _ (by decide)

/-- One pruning word; only EAX, flags and the destination word change. -/
theorem pruneWord_ok {s : State} {E : BitVec 32} {k : Nat} (he : s.gpr .esp = E)
    (hr : InRegions (s.rd ++ s.wr) (addr E (192 + 4 * k)) 4)
    (hw : InRegions s.wr (addr E (32 + 4 * k)) 4) :
    WP isa (.block (pruneWord k)) s fun t => Step s t ∧
      t.mem = s.mem.writeW (addr E (32 + 4 * k))
        (pruneValue k (s.mem.readW (addr E (192 + 4 * k)) 32)) := by
  by_cases h0 : k = 0
  · subst k
    apply WP.of_runBlock
    simp only [pruneWord, pruneValue, at_, ↓reduceIte, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load32,
      State.store32, ea_mk, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
      RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
      RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, reduceCtorEq,
      he, hr, hw, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
    exact ⟨⟨rfl, rfl, fun r h => by simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h, ite_false]⟩, True.intro⟩
  · by_cases h7 : k = 7
    · subst k
      apply WP.of_runBlock
      simp only [pruneWord, pruneValue, at_, ↓reduceIte, List.cons_append, List.nil_append,
        runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load32,
        State.store32, ea_mk, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
        RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
        RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, reduceCtorEq,
        he, hr, hw, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
      exact ⟨⟨rfl, rfl, fun r h => by simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h, ite_false]⟩, True.intro⟩
    · simp only [pruneWord, h0, h7, ↓reduceIte, List.cons_append, List.nil_append, at_]
      refine Wp.wp_ldm he hr fun u hu => ?_
      refine Wp.wp_stm (hu.other _ (by decide) |>.trans he) (hu.wr ▸ hw) fun t ht => WP.block_nil ?_
      refine ⟨⟨ht.rd.trans hu.rd, ht.wr.trans hu.wr, fun r h => by rw [ht.gpr]; exact hu.other r h⟩, ?_⟩
      rw [ht.mem, hu.mem, hu.gpr, pruneValue, ite_eq_right h0, ite_eq_right h7]

/-- The frame bounds supply readable and writable words. -/
theorem frame_word {s : State} {E : BitVec 32} (hf : E.toNat + 256 ≤ 2 ^ 32)
    (hw : (⟨E.setWidth 64, 256⟩ : Region) ∈ s.wr) {d : Nat} (hd : d + 4 ≤ 256) :
    InRegions s.wr (addr E d) 4 := by
  refine ⟨_, hw, ?_⟩
  rw [addr_eq (by omega_using [hf, hd])]
  exact Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd])

structure PruneInv (E : BitVec 32) (s : State) (n : Nat) (t : State) : Prop where
  step : Step s t
  frame : Frame [⟨E.setWidth 64 + BitVec.ofNat 64 32, 32⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (addr E (32 + 4 * j)) 32 =
    pruneValue j (s.mem.readW (addr E (192 + 4 * j)) 32)

theorem prunePrefix_ok {s : State} {E : BitVec 32} (he : s.gpr .esp = E)
    (hf : E.toNat + 256 ≤ 2 ^ 32) (hw : (⟨E.setWidth 64, 256⟩ : Region) ∈ s.wr) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap pruneWord)) s (PruneInv E s n)
  | 0, _ => WP.block_nil ⟨Step.refl s, Frame.refl _ _, fun _ h => by omega_using [h]⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (prunePrefix_ok he hf hw n (by omega_using [hn])) fun u hu => ?_
    have ur : InRegions (u.rd ++ u.wr) (addr E (192 + 4 * n)) 4 := by
      obtain ⟨r, hr, hc⟩ := frame_word hf (hu.step.wr ▸ hw) (d := 192 + 4 * n) (by omega_using [hn])
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    have uw := frame_word hf (hu.step.wr ▸ hw) (d := 32 + 4 * n) (by omega_using [hn])
    refine WP.mono (pruneWord_ok (hu.step.esp.trans he) ur uw) fun t ⟨kt, mt⟩ => ?_
    have a192 : addr E (192 + 4 * n) = E.setWidth 64 + BitVec.ofNat 64 (192 + 4 * n) :=
      addr_eq (by omega_using [hf, hn])
    have a32 : addr E (32 + 4 * n) = E.setWidth 64 + BitVec.ofNat 64 (32 + 4 * n) :=
      addr_eq (by omega_using [hf, hn])
    have same : u.mem.readW (addr E (192 + 4 * n)) 32 = s.mem.readW (addr E (192 + 4 * n)) 32 := by
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
      · rw [Mem.readW_writeW_sep (a := addr E (32 + 4 * j)) (b := addr E (32 + 4 * n)) ?_ (by decide)]
        · exact hu.words j (by omega_using [hj, hjn])
        · rw [a32, addr_eq (by omega_using [hf, hj, hn])]
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
theorem prune_ok {s : State} {E : BitVec 32} (he : s.gpr .esp = E)
    (hf : E.toNat + 256 ≤ 2 ^ 32) (hw : (⟨E.setWidth 64, 256⟩ : Region) ∈ s.wr)
    {digest : List Byte} (hh : Spec.Sha512.bytesAt s.mem (E.setWidth 64 + 192) 64 = digest) :
    WP isa (.block prune) s fun t => Step s t ∧
      Frame [⟨E.setWidth 64 + 32, 32⟩] s.mem t.mem ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem (E.setWidth 64 + 32) 32) =
        Spec.Ed25519.prune digest := by
  refine WP.mono (prunePrefix_ok he hf hw 8 (by decide)) fun t ht => ⟨ht.step, ht.frame, ?_⟩
  have words : ∀ j < 8, t.mem.readW (E.setWidth 64 + BitVec.ofNat 64 (32 + 4 * j)) 32 =
      pruneValue j (s.mem.readW (E.setWidth 64 + BitVec.ofNat 64 (192 + 4 * j)) 32) := by
    intro j hj
    have h := ht.words j hj
    rw [addr_eq (by omega_using [hf, hj]), addr_eq (by omega_using [hf, hj])] at h
    exact h
  have take : (Spec.Sha512.bytesAt s.mem (E.setWidth 64 + 192) 64).take 32 =
      Spec.Ed25519.bytesAt s.mem (E.setWidth 64 + 192) 32 := by
    simp [Spec.Sha512.bytesAt, Spec.Ed25519.bytesAt, ← List.map_take, List.take_range]
  rw [Spec.Ed25519.prune, ← hh, take, decode_words, decode_words]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have w0 := words 0 (by decide)
  have w1 := words 1 (by decide)
  have w2 := words 2 (by decide)
  have w3 := words 3 (by decide)
  have w4 := words 4 (by decide)
  have w5 := words 5 (by decide)
  have w6 := words 6 (by decide)
  have w7 := words 7 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceEqDiff, pruneValue, ↓reduceIte] at w0 w1 w2 w3 w4 w5 w6 w7
  change t.mem.readW (E.setWidth 64 + (32 : BitVec 64)) 32 = _ at w0
  rw [w0, w1, w2, w3, w4, w5, w6, w7]
  exact (prune_words _ _ _ _ _ _ _ _).symm

end VG.Proof.Ed25519.X86.PublicKey

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.PublicKey.CTReady`. -/
section

/-! Merged from `Proof.Ed25519.X86.PublicKey.Setup`. -/
section
namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86
open VG.Impl.Ed25519.X86.Whole (Value setup)

def argValue (s : State) : Value → BitVec 32
  | .const n => BitVec.ofNat 32 n
  | .frame d => esp s + BitVec.ofNat 32 d
  | .caller i d => arg s i + BitVec.ofNat 32 d

theorem setup_ok {s t : State} (h : Facts s) (hc : Ctx s t) {vs : List Value}
    (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 3 v) :
    WP isa (.block (setup 0 vs)) t fun u => Ctx s u ∧
      Frame [⟨(esp s).setWidth 64, 24⟩] t.mem u.mem ∧
      ∀ j (hj : j < vs.length), Whole.slots (esp s) u j = argValue s (vs[j]'hj) := by
  refine WP.mono (Whole.Ctx.setup hc (n := 3) (by have := h.toBounds.frame; omega)
    (fun j hj => original_arg_readable h hc hj) (by omega) hv) fun u ⟨hu, hf, hs⟩ => ⟨hu, hf, ?_⟩
  intro j hj
  have e := hs j hj
  simp only [Nat.zero_add] at e
  rw [addr_eq (by have := h.toBounds.frame; omega)] at e
  rw [Whole.slots, e]
  generalize he : vs[j]'hj = v
  have vv := hv (vs[j]'hj) (List.getElem_mem hj)
  rw [he] at vv
  cases v with
  | const n => rfl
  | frame d => rfl
  | caller i d =>
    exact congrArg (· + BitVec.ofNat 32 d) (original_arg h hc vv)

/-- Setup only writes the outgoing argument area, so unrelated buffers survive. -/
theorem setup_disjoint {s : State} (h : Facts s) :
    (⟨(esp s).setWidth 64, 24⟩ : Region).Disjoint (SCR s) ∧
    (⟨(esp s).setWidth 64, 24⟩ : Region).Disjoint (SEED s) ∧
    (⟨(esp s).setWidth 64, 24⟩ : Region).Disjoint (OUT s) := by
  have sub : Region.Sub ⟨(esp s).setWidth 64, 24⟩ (Whole.STK (esp s)) :=
    fun p hp => Whole.frame_sub (esp s) p (Region.sub_prefix (by decide) p hp)
  exact ⟨h.kc.sub_left sub, h.ks.sub_left sub, h.ko.sub_left sub⟩

end VG.Proof.Ed25519.X86.PublicKey
end

/-! Merged from `Proof.Ed25519.X86.PublicKey.Base`. -/
section
namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86
open VG.Impl.Ed25519.X86 (scalarBase)

def scalarPtr (s : State) : BitVec 32 := esp s + BitVec.ofNat 32 32

theorem scalarPtr_addr {s : State} (h : Bounds s) :
    (scalarPtr s).setWidth 64 = (esp s).setWidth 64 + BitVec.ofNat 64 32 :=
  addr_eq (by have := h.frame; omega)

theorem base_nosp : NoSp scalarBase := NoSp.of_all (by lit_decide)
theorem base_stack : stackUse scalarBase = 0 := by lit_decide

def BaseArgs (s t : State) : Prop :=
  Whole.slots (esp s) t 0 = arg s 0 ∧ Whole.slots (esp s) t 1 = scalarPtr s ∧
    Whole.slots (esp s) t 2 = arg s 2

def baseRd (s : State) : List Region := [⟨(scalarPtr s).setWidth 64, 32⟩, ⟨(esp s).setWidth 64, 12⟩]

/-- The three cdecl argument slots of the base-point multiplication. -/
theorem base_args {s t : State} (h : Facts s) (hc : Ctx s t) (ha : BaseArgs s t) :
    arg t.callEntry 0 = arg s 0 ∧ arg t.callEntry 1 = scalarPtr s ∧ arg t.callEntry 2 = arg s 2 := by
  have e : ∀ j < 64, arg t.callEntry j = Whole.slots (esp s) t j :=
    fun j hj => Whole.call_arg hc.esp h.toBounds.call (by have := h.toBounds.frame; omega) hj
  exact ⟨(e 0 (by decide)).trans ha.1, (e 1 (by decide)).trans ha.2.1,
    (e 2 (by decide)).trans ha.2.2⟩

theorem base_pre {s t : State} (h : Facts s) (hc : Ctx s t) (ha : BaseArgs s t) :
    scalarBaseLocal.pre (t.callEntry.withRegions (baseRd s) (pkWr s)) := by
  obtain ⟨a0, a1, a2⟩ := base_args h hc ha
  have ae : argAddr t.callEntry 0 = (esp s).setWidth 64 := by
    rw [argAddr_callEntry, hc.esp]
    simp
  have fe := h.toBounds.frame
  have be := h.toBounds.call
  have ret : Region.Sub ⟨(esp s - 4).setWidth 64, 4⟩ (Whole.STK (esp s)) :=
    Whole.below_sub_stack be (by decide)
  have args : Region.Sub ⟨(esp s).setWidth 64, 12⟩ (Whole.STK (esp s)) :=
    fun p hp => Whole.frame_sub (esp s) p (Region.sub_prefix (by decide) p hp)
  have scalar : Region.Sub ⟨(scalarPtr s).setWidth 64, 32⟩ (Whole.STK (esp s)) := by
    rw [scalarPtr_addr h.toBounds]
    exact fun p hp => Whole.frame_sub (esp s) p (Offset.sub_base _ (by decide : 32 + 32 ≤ 256) p hp)
  simp only [scalarBaseLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    argAddr_withRegions, State.withRegions_gpr, State.callEntry_esp, hc.esp, a0, a1, a2, ae]
  refine ⟨rfl, rfl, h.oc, h.kc.sub_left scalar, h.ko.sub_left args, h.kc.sub_left args,
    h.ko.sub_left ret, h.kc.sub_left ret, h.out, ?_, h.scratch, ?_⟩
  · change (esp s + BitVec.ofNat 32 32).toNat + 32 ≤ 2 ^ 32
    rw [BitVec.toNat_add, show (BitVec.ofNat 32 32).toNat = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
    omega
  · change (esp s - BitVec.ofNat 32 4).toNat + 16 ≤ 2 ^ 32
    rw [sub_toNat (by omega : 4 ≤ (esp s).toNat)]
    omega

theorem base_call {s t : State} (h : Facts s) (hc : Ctx s t) (ha : BaseArgs s t) :
    WP isa (.call "vg_ed25519_scalar_base" scalarBase) t fun u => Ctx s u ∧
      Spec.Ed25519.bytesAt u.mem ((arg s 0).setWidth 64) 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt t.mem ((scalarPtr s).setWidth 64) 32) := by
  have scalarWithin : Whole.Within ⟨(scalarPtr s).setWidth 64, 32⟩ (Whole.FR (esp s)) :=
    ⟨32, scalarPtr_addr h.toBounds, by change 32 + 32 ≤ 256; decide⟩
  have cov : Covers (baseRd s ++ pkWr s) (pkRd s ++ Whole.FR (esp s) :: pkWr s) := by
    refine Covers.of_sub ?_
    simp only [baseRd, pkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact ⟨Whole.FR (esp s), by simp, scalarWithin⟩
    · exact ⟨Whole.FR (esp s), by simp, 0, by simp, by change 0 + 12 ≤ 256; decide⟩
    · exact ⟨OUT s, by simp, 0, by simp, by change 0 + 32 ≤ 32; decide⟩
    · exact ⟨SCR s, by simp, 0, by simp, by change 0 + 8192 ≤ 8192; decide⟩
  have ws : ∀ r ∈ pkWr s, Whole.Within r (Whole.FR (esp s)) ∨ ∃ R ∈ pkWr s, Whole.Within r R :=
    fun r hr => .inr ⟨r, hr, 0, by simp, by simp⟩
  with_reducible
    refine Whole.call_ok hc h.toBounds.call scalarBase_ok base_nosp (by rw [base_stack]; decide)
      (base_pre h hc ha) cov ws fun u hu _ _ post => ⟨hu, ?_⟩
  obtain ⟨s₂, hm, hg, hp⟩ := post
  obtain ⟨a0, a1, _⟩ := base_args h hc ha
  change Spec.Ed25519.bytesAt s₂.mem ((arg t.callEntry 0).setWidth 64) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt t.callEntry.mem ((arg t.callEntry 1).setWidth 64) 32) at hp
  rw [hm, a0, a1] at hp
  rw [hp]
  refine congrArg Spec.Ed25519.scalarBase ?_
  refine Whole.callEntry_bytes (r := ⟨(scalarPtr s).setWidth 64, 32⟩) ?_ (by change 32 ≤ 2 ^ 64; decide)
  rw [hc.esp, scalarPtr_addr h.toBounds]
  change Region.Disjoint ⟨(esp s).setWidth 64 + BitVec.ofNat 64 32, 32⟩
    ⟨(esp s - BitVec.ofNat 32 4).setWidth 64, 4⟩
  have e : (esp s - BitVec.ofNat 32 4).setWidth 64 = (esp s).setWidth 64 - BitVec.ofNat 64 4 :=
    Taint.sub_setWidth (m := 4) (by have := h.toBounds.call; omega)
  rw [e]
  exact (Offset.disjoint_below_above _ (m := 4) (a := 32) (l := 32) (by decide)).symm

end VG.Proof.Ed25519.X86.PublicKey
end

/-! Merged from `Proof.Ed25519.X86.PublicKey.Hash`. -/
section
namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey

theorem hashSpace {s : State} (h : Facts s) : Whole.HashSpace (esp s) (arg s 2) :=
  ⟨h.toBounds.call, by have := h.toBounds.frame; omega, h.scratch, h.kc⟩

theorem shaWithin (s : State) : Whole.Within (Whole.SHA (arg s 2)) (SCR s) :=
  ⟨0, by simp, by change 0 + 192 ≤ 8192; decide⟩
theorem workWithin {s : State} (h : Facts s) : Whole.Within (Whole.WORK (arg s 2)) (SCR s) :=
  ⟨192, (hashSpace h).work_addr, by change 192 + 272 ≤ 8192; decide⟩
theorem argsWithin (s : State) {n : Nat} (hn : n ≤ 256) :
    Whole.Within (Whole.ARGS (esp s) n) (Whole.FR (esp s)) := ⟨0, by simp, by change 0 + n ≤ 256; omega⟩

theorem hash_covers {s : State} {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r (Whole.FR (esp s)) ∨ Whole.Within r (SCR s) ∨ Whole.Within r (SEED s)) :
    Covers rs (pkRd s ++ Whole.FR (esp s) :: pkWr s) := by
  refine Covers.of_sub fun r hr => ?_
  rcases h r hr with h | h | h
  · exact ⟨_, by simp [pkRd, pkWr], h⟩
  · exact ⟨_, by simp [pkRd, pkWr], h⟩
  · exact ⟨_, by simp [pkRd, pkWr], h⟩

theorem hash_writes {s : State} {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r (Whole.FR (esp s)) ∨ Whole.Within r (SCR s)) :
    ∀ r ∈ rs, Whole.Within r (Whole.FR (esp s)) ∨ ∃ R ∈ pkWr s, Whole.Within r R := by
  intro r hr
  rcases h r hr with h | h
  · exact .inl h
  · exact .inr ⟨_, by simp [pkWr], h⟩

theorem seed_same {s t : State} (h : Facts s) (hc : Ctx s t) :
    Spec.Ed25519.bytesAt t.mem ((arg s 1).setWidth 64) 32 =
      Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32 := by
  apply List.map_congr_left
  intro i hi
  exact hc.frame.bytes (R := SEED s) (by
    simp only [pkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact h.os.symm
    · exact h.sc
    · exact h.ks.symm) (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)

theorem setup_repr {s t u : State} (h : Facts s)
    (hf : Frame [⟨(esp s).setWidth 64, 24⟩] t.mem u.mem) {msg : List Byte}
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem ((arg s 2).setWidth 64) msg) :
    Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem ((arg s 2).setWidth 64) msg := by
  refine Proof.Sha512.Stream.repr_congr (mem := t.mem) ?_ hr
  intro i hi
  exact hf.bytes (R := Whole.SHA (arg s 2)) (by
    rintro r hr; rw [List.mem_singleton.mp hr]
    exact ((setup_disjoint h).1.sub_right Whole.HashSpace.sha_sub).symm) (by change 192 ≤ 2 ^ 64; decide) hi

theorem init_step {s t : State} (h : Facts s) (hc : Ctx s t) :
    WP isa (callWith initArgs Spec.Sha512.init512Api.name (Impl.Sha512.X86.Stream.init Spec.Sha512.H0_512)) t
      fun u => Ctx s u ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem ((arg s 2).setWidth 64) [] := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.PublicKey.setup_ok h hc (vs := [.caller 2 0]) (by decide) (by simp [Whole.valid]))
    fun u ⟨hu, _, hs⟩ => ?_)
  have a0 := hs 0 (by decide)
  change Whole.slots (esp s) u 0 = arg s 2 + 0#32 at a0
  rw [BitVec.add_zero] at a0
  have H := hashSpace h
  have hp := Whole.init_pre hu.esp H a0
  have cov : Covers (Whole.initRd (esp s) ++ Whole.initWr (arg s 2))
      (pkRd s ++ Whole.FR (esp s) :: pkWr s) := hash_covers (by
    simp only [Whole.initRd, Whole.initWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (argsWithin s (by decide))
    · exact .inr (.inl (shaWithin s)))
  have ws := hash_writes (s := s) (rs := Whole.initWr (arg s 2)) (by
    intro r hr; rw [List.mem_singleton.mp hr]; exact .inr (shaWithin s))
  refine WP.mono (Whole.init_call hu H.below hp cov ws
    ((Whole.call_arg hu.esp H.below H.frameFit (by decide)).trans a0)) fun u ⟨hu, _, hr⟩ => ⟨hu, hr⟩

theorem update_step {s t : State} (h : Facts s) (hc : Ctx s t)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem ((arg s 2).setWidth 64) []) :
    WP isa (callWith updateArgs Spec.Sha512.updateScratchApi.name Impl.Sha512.X86.Stream.update) t
      fun u => Ctx s u ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem ((arg s 2).setWidth 64)
        (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.PublicKey.setup_ok h hc
    (vs := [.caller 2 0, .const 0, .const 0, .caller 1 0, .const 32, .caller 2 192])
    (by decide) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  have a3 := hs 3 (by decide)
  have a4 := hs 4 (by decide)
  have a5 := hs 5 (by decide)
  simp only [argValue, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at a0 a1 a2 a3 a4 a5
  have H := hashSpace h
  have hp := Whole.update_pre hu.esp H a0 a3 a4 a5 h.sc
    (h.ks.sub_left (Whole.below_sub_stack H.below (by decide))) h.seed
  have cov : Covers (Whole.updateRd (esp s) (arg s 1) 32 ++ Whole.hashWr (arg s 2))
      (pkRd s ++ Whole.FR (esp s) :: pkWr s) := hash_covers (by
    simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inr (.inr ⟨0, by simp, by change 0 + 32 ≤ 32; decide⟩)
    · exact .inl (argsWithin s (by decide))
    · exact .inr (.inl (shaWithin s))
    · exact .inr (.inl (workWithin h)))
  have ws := hash_writes (s := s) (rs := Whole.hashWr (arg s 2)) (by
    simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (shaWithin s)
    · exact .inr (workWithin h))
  have ce : ∀ j < 64, arg u.callEntry j = Whole.slots (esp s) u j :=
    fun j hj => Whole.call_arg hu.esp H.below H.frameFit hj
  have count : Proof.Sha512.countX86 u.callEntry = BitVec.ofNat 64 ([] : List Byte).length := by
    rw [Proof.Sha512.countX86, ce 1 (by decide), ce 2 (by decide), a1, a2]
    rfl
  refine WP.mono (Whole.update_call hu H.below hp cov ws
    ((ce 0 (by decide)).trans a0) ((ce 3 (by decide)).trans a3) ((ce 4 (by decide)).trans a4) count
    (by rw [hu.esp]; exact (H.below_sha (by decide)).symm)
    (by rw [hu.esp]; exact (h.ks.sub_left (Whole.below_sub_stack H.below (by decide))).symm)
    (setup_repr h hf hr)) fun v ⟨hv, _, hr⟩ => ⟨hv, ?_⟩
  change Spec.Sha512.Repr _ v.mem _ ([] ++ Spec.Ed25519.bytesAt u.mem ((arg s 1).setWidth 64) 32) at hr
  rw [List.nil_append, seed_same h hu] at hr
  exact hr

/-- The frame's digest pointer. -/
def digestPtr (s : State) : BitVec 32 := esp s + BitVec.ofNat 32 192

theorem digest_addr {s : State} (h : Facts s) :
    (digestPtr s).setWidth 64 = (esp s).setWidth 64 + BitVec.ofNat 64 192 :=
  addr_eq (by have := h.toBounds.frame; omega)

theorem finalize_step {s t : State} (h : Facts s) (hc : Ctx s t)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem ((arg s 2).setWidth 64)
      (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)) :
    WP isa (callWith finalizeArgs Spec.Sha512.finalizeScratchApi.name Impl.Sha512.X86.Stream.finalize) t
      fun u => Ctx s u ∧ Spec.Sha512.bytesAt u.mem ((esp s).setWidth 64 + 192) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.PublicKey.setup_ok h hc
    (vs := [.caller 2 0, .const 32, .const 0, .frame 192, .caller 2 192])
    (by decide) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  have a3 := hs 3 (by decide)
  have a4 := hs 4 (by decide)
  simp only [argValue, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at a0 a1 a2 a3 a4
  have H := hashSpace h
  have ds : Whole.Within ⟨(digestPtr s).setWidth 64, 64⟩ (Whole.FR (esp s)) :=
    ⟨192, digest_addr h, by change 192 + 64 ≤ 256; decide⟩
  have dd : Region.Disjoint ⟨(digestPtr s).setWidth 64, 64⟩ (SCR s) :=
    h.kc.sub_left (fun p hp => Whole.frame_sub (esp s) p (ds.sub p hp))
  have db : (below (esp s) 24).Disjoint ⟨(digestPtr s).setWidth 64, 64⟩ := by
    rw [digest_addr h]
    change Region.Disjoint ⟨(esp s - BitVec.ofNat 32 24).setWidth 64, 24⟩ _
    rw [Taint.sub_setWidth H.below]
    exact Offset.disjoint_below_above _ (by decide)
  have da : (Whole.ARGS (esp s) 20).Disjoint ⟨(digestPtr s).setWidth 64, 64⟩ := by
    rw [digest_addr h]
    exact Offset.base_disjoint _ (by decide) (by decide)
  have df : (digestPtr s).toNat + 64 ≤ 2 ^ 32 := by
    change (esp s + BitVec.ofNat 32 192).toNat + 64 ≤ 2 ^ 32
    rw [BitVec.toNat_add, show (BitVec.ofNat 32 192).toNat = 192 from rfl]
    have fe := H.frameFit
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hp := Whole.finalize_pre hu.esp H a0 a3 a4 dd db da df
  have cov : Covers (Whole.finalizeRd (esp s) ++ Whole.finalizeWr (arg s 2) (digestPtr s))
      (pkRd s ++ Whole.FR (esp s) :: pkWr s) := hash_covers (by
    simp only [Whole.finalizeRd, Whole.finalizeWr, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (argsWithin s (by decide))
    · exact .inr (.inl (shaWithin s))
    · exact .inl ds
    · exact .inr (.inl (workWithin h)))
  have ws := hash_writes (s := s) (rs := Whole.finalizeWr (arg s 2) (digestPtr s)) (by
    simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inr (shaWithin s)
    · exact .inl ds
    · exact .inr (workWithin h))
  have ce : ∀ j < 64, arg u.callEntry j = Whole.slots (esp s) u j :=
    fun j hj => Whole.call_arg hu.esp H.below H.frameFit hj
  have len : (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32).length = 32 := by
    simp [Spec.Ed25519.bytesAt]
  have count : Proof.Sha512.countX86 u.callEntry =
      BitVec.ofNat 64 (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32).length := by
    rw [Proof.Sha512.countX86, ce 1 (by decide), ce 2 (by decide), a1, a2, len]
    rfl
  refine WP.mono (Whole.finalize_call hu H.below hp cov ws
    ((ce 0 (by decide)).trans a0) ((ce 3 (by decide)).trans a3) count
    (by rw [hu.esp]; exact (H.below_sha (by decide)).symm)
    (setup_repr h hf hr) (by rw [len]; decide)) fun v ⟨hv, _, hd⟩ => ⟨hv, ?_⟩
  change Spec.Ed25519.bytesAt v.mem ((digestPtr s).setWidth 64) 64 = _ at hd
  rw [digest_addr h] at hd
  exact hd

theorem hash_ok {s t : State} (h : Facts s) (hc : Ctx s t) :
    WP isa hash t fun u => Ctx s u ∧ Spec.Sha512.bytesAt u.mem ((esp s).setWidth 64 + 192) 64 =
      Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32) :=
  WP.seq (WP.mono (init_step h hc) fun _ ⟨hc, hr⟩ =>
    WP.seq (WP.mono (update_step h hc hr) fun _ ⟨hc, hr⟩ => finalize_step h hc hr))

end VG.Proof.Ed25519.X86.PublicKey
end

/-! Merged from `Proof.Ed25519.X86.PublicKey.Correct`. -/
section
namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey

theorem prune_step {s t : State} (h : Facts s) (hc : Ctx s t) {digest : List Byte}
    (hh : Spec.Sha512.bytesAt t.mem ((esp s).setWidth 64 + 192) 64 = digest) :
    WP isa (.block prune) t fun u => Ctx s u ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt u.mem ((scalarPtr s).setWidth 64) 32) =
        Spec.Ed25519.prune digest := by
  refine WP.mono (prune_ok hc.esp (by have := h.toBounds.frame; omega)
    (by rw [hc.wr]; exact List.mem_cons_self) hh) fun u ⟨ku, hf, hs⟩ => ⟨?_, ?_⟩
  · refine hc.of_frame ku.rd ku.wr ku.esp ?_ hf ?_
    · intro r hr _
      apply ku.regs
      rintro rfl
      simp [calleeSaved] at hr
    · rintro r hr
      rw [List.mem_singleton.mp hr]
      exact .inl (Offset.sub_base _ (by decide))
  · rw [scalarPtr_addr h.toBounds]
    exact hs

theorem base_step {s t : State} (h : Facts s) (hc : Ctx s t) {n : Nat}
    (hn : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem ((scalarPtr s).setWidth 64) 32) = n) :
    WP isa (callWith baseArgs "vg_ed25519_scalar_base" Impl.Ed25519.X86.scalarBase) t
      fun u => Ctx s u ∧ Spec.Ed25519.bytesAt u.mem ((arg s 0).setWidth 64) 32 =
        Spec.Ed25519.encodePoint (Spec.Ed25519.pointMul n Spec.Ed25519.basePoint) := by
  refine WP.seq (WP.mono (VG.Proof.Ed25519.X86.PublicKey.setup_ok h hc (vs := [.caller 0 0, .frame 32, .caller 2 0])
    (by decide) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  simp only [argValue, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at a0 a1 a2
  have he : Spec.Ed25519.bytesAt u.mem ((scalarPtr s).setWidth 64) 32 =
      Spec.Ed25519.bytesAt t.mem ((scalarPtr s).setWidth 64) 32 := by
    apply List.map_congr_left
    intro i hi
    exact hf.bytes (R := ⟨(scalarPtr s).setWidth 64, 32⟩) (by
      rintro r hr; rw [List.mem_singleton.mp hr, scalarPtr_addr h.toBounds]
      exact Offset.disjoint_base _ (by decide) (by decide)) (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  refine WP.mono (base_call h hu ⟨a0, a1, a2⟩) fun v ⟨hv, ho⟩ => ⟨hv, ?_⟩
  rw [ho, he, Spec.Ed25519.scalarBase, hn]

theorem body_ok {s t : State} (h : Facts s) (hc : Ctx s t) :
    WP isa body t fun u => Ctx s u ∧ Spec.Ed25519.bytesAt u.mem ((arg s 0).setWidth 64) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32) := by
  refine WP.seq (WP.mono (hash_ok h hc) fun t₁ ⟨hc₁, hh⟩ => ?_)
  refine WP.seq (WP.mono (prune_step h hc₁ hh) fun t₂ ⟨hc₂, hn⟩ => ?_)
  refine WP.seq (WP.mono (base_step h hc₂ hn) fun t₃ ⟨hc₃, ho⟩ => ?_)
  refine WP.mono (Whole.Ctx.zeroWords hc₃ (start := 8) (count := 56)
    (by have := h.toBounds.frame; omega) (by decide)) fun u ⟨hu, hf, _⟩ => ⟨hu, ?_⟩
  have he : Spec.Ed25519.bytesAt u.mem ((arg s 0).setWidth 64) 32 =
      Spec.Ed25519.bytesAt t₃.mem ((arg s 0).setWidth 64) 32 := by
    apply List.map_congr_left
    intro i hi
    exact hf.bytes (R := OUT s) (by
      rintro r hr; rw [List.mem_singleton.mp hr]
      exact (h.ko.sub_left (fun p hp => Whole.frame_sub (esp s) p
        (Offset.sub_base _ (by decide : 4 * 8 + 4 * 56 ≤ 256) p hp))).symm)
      (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rw [he, ho]
  rfl

private theorem noSp_seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact ha i hi
  · exact hb i hi

theorem body_nosp : NoSp body := by
  have ni : NoSp (.block initArgs) := NoSp.of_all (by decide +kernel)
  have nu : NoSp (.block updateArgs) := NoSp.of_all (by decide +kernel)
  have nf : NoSp (.block finalizeArgs) := NoSp.of_all (by decide +kernel)
  have nb : NoSp (.block baseArgs) := NoSp.of_all (by decide +kernel)
  have np : NoSp (.block prune) := NoSp.of_all (by decide +kernel)
  have nw : NoSp (.block wipe) := NoSp.of_all (by decide +kernel)
  exact noSp_seq
    (noSp_seq (noSp_seq ni Whole.init_nosp)
      (noSp_seq (noSp_seq nu Whole.update_nosp) (noSp_seq nf Whole.finalize_nosp)))
    (noSp_seq np (noSp_seq (noSp_seq nb base_nosp) nw))

theorem publicKey_ok {s : State} (h : pkLocal.pre s) :
    WP isa publicKey s fun t => abiPreserved s t ∧ pkLocal.post s t := by
  have hf := facts h
  refine WP.frame (rs := List.replicate 64 .eax) (by simp) (by simp) (by decide)
    (by simp only [List.length_replicate]; have := hf.below; omega) body_nosp
    (WP.mono (body_ok hf (push_ctx h)) fun u ⟨hu, ho⟩ => ?_)
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases he : r = .esp
    · subst r
      rw [popped_esp, hu.esp, List.length_replicate]
      exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ he (by intro e; subst r; simp [calleeSaved] at hr), hu.cs r hr he]
  · rw [popped_mem]
    refine hu.frame.readW (r := RET s) (Region.contains_self _ _) ?_ (by decide)
    simp only [pkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hf.ro
    · exact hf.rc
    · rw [stack_eq hf.toBounds]
      change Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩
        ⟨(s.gpr .esp - BitVec.ofNat 32 280).setWidth 64, 280⟩
      rw [Taint.sub_setWidth hf.below]
      exact (Offset.below_disjoint _ (by decide)).symm
  · change Spec.Ed25519.bytesAt (popped .eax (List.replicate 64 .eax).length u).mem
      ((arg s 0).setWidth 64) 32 = _
    rw [popped_mem]
    exact ho

end VG.Proof.Ed25519.X86.PublicKey
end

namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey
open VG.Impl.Ed25519.X86.Whole (Value)

def Slots (vs : List Value) (s t : State) : Prop :=
  ∀ j (hj : j < vs.length), Whole.slots (esp s) t j = argValue s (vs[j]'hj)

def initValues : List Value := [.caller 2 0]
def updateValues : List Value := [.caller 2 0, .const 0, .const 0, .caller 1 0, .const 32, .caller 2 192]
def finalizeValues : List Value := [.caller 2 0, .const 32, .const 0, .frame 192, .caller 2 192]
def baseValues : List Value := [.caller 0 0, .frame 32, .caller 2 0]

def init_ready {s t : State} (h : Facts s) (hc : Ctx s t) (hs : Slots initValues s t) :
    Whole.CallReady (Proof.Sha512.initX86 Spec.Sha512.H0_512) (esp s) (pkRd s) (pkWr s) t := by
  change ∀ j (hj : j < initValues.length), Whole.slots (esp s) t j = argValue s (initValues[j]'hj) at hs
  unfold initValues at hs
  have a0 := hs 0 (by decide)
  change Whole.slots (esp s) t 0 = arg s 2 + 0#32 at a0
  rw [BitVec.add_zero] at a0
  have H := hashSpace h
  have hp := Whole.init_pre hc.esp H a0
  have cov : Covers (Whole.initRd (esp s) ++ Whole.initWr (arg s 2))
      (pkRd s ++ Whole.FR (esp s) :: pkWr s) := hash_covers (by
    simp only [Whole.initRd, Whole.initWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (argsWithin s (by decide))
    · exact .inr (.inl (shaWithin s)))
  have ws := hash_writes (s := s) (rs := Whole.initWr (arg s 2)) (by
    intro r hr; rw [List.mem_singleton.mp hr]; exact .inr (shaWithin s))
  exact ⟨Whole.initRd (esp s), Whole.initWr (arg s 2), hp, cov, ws⟩

def update_ready {s t : State} (h : Facts s) (hc : Ctx s t) (hs : Slots updateValues s t) :
    Whole.CallReady Proof.Sha512.updateX86 (esp s) (pkRd s) (pkWr s) t := by
  change ∀ j (hj : j < updateValues.length), Whole.slots (esp s) t j = argValue s (updateValues[j]'hj) at hs
  unfold updateValues at hs
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  have a3 := hs 3 (by decide)
  have a4 := hs 4 (by decide)
  have a5 := hs 5 (by decide)
  simp only [argValue, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at a0 a1 a2 a3 a4 a5
  have H := hashSpace h
  have hp := Whole.update_pre hc.esp H a0 a3 a4 a5 h.sc
    (h.ks.sub_left (Whole.below_sub_stack H.below (by decide))) h.seed
  have cov : Covers (Whole.updateRd (esp s) (arg s 1) 32 ++ Whole.hashWr (arg s 2))
      (pkRd s ++ Whole.FR (esp s) :: pkWr s) := hash_covers (by
    simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inr (.inr ⟨0, by simp, by change 0 + 32 ≤ 32; decide⟩)
    · exact .inl (argsWithin s (by decide))
    · exact .inr (.inl (shaWithin s))
    · exact .inr (.inl (workWithin h)))
  have ws := hash_writes (s := s) (rs := Whole.hashWr (arg s 2)) (by
    simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (shaWithin s)
    · exact .inr (workWithin h))
  exact ⟨Whole.updateRd (esp s) (arg s 1) 32, Whole.hashWr (arg s 2), hp, cov, ws⟩

def finalize_ready {s t : State} (h : Facts s) (hc : Ctx s t) (hs : Slots finalizeValues s t) :
    Whole.CallReady Proof.Sha512.finalizeX86 (esp s) (pkRd s) (pkWr s) t := by
  change ∀ j (hj : j < finalizeValues.length), Whole.slots (esp s) t j = argValue s (finalizeValues[j]'hj) at hs
  unfold finalizeValues at hs
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  have a3 := hs 3 (by decide)
  have a4 := hs 4 (by decide)
  simp only [argValue, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at a0 a1 a2 a3 a4
  have H := hashSpace h
  have ds : Whole.Within ⟨(digestPtr s).setWidth 64, 64⟩ (Whole.FR (esp s)) :=
    ⟨192, digest_addr h, by change 192 + 64 ≤ 256; decide⟩
  have dd : Region.Disjoint ⟨(digestPtr s).setWidth 64, 64⟩ (SCR s) :=
    h.kc.sub_left (fun p hp => Whole.frame_sub (esp s) p (ds.sub p hp))
  have db : (below (esp s) 24).Disjoint ⟨(digestPtr s).setWidth 64, 64⟩ := by
    rw [digest_addr h]
    change Region.Disjoint ⟨(esp s - BitVec.ofNat 32 24).setWidth 64, 24⟩ _
    rw [Taint.sub_setWidth H.below]
    exact Offset.disjoint_below_above _ (by decide)
  have da : (Whole.ARGS (esp s) 20).Disjoint ⟨(digestPtr s).setWidth 64, 64⟩ := by
    rw [digest_addr h]
    exact Offset.base_disjoint _ (by decide) (by decide)
  have df : (digestPtr s).toNat + 64 ≤ 2 ^ 32 := by
    change (esp s + BitVec.ofNat 32 192).toNat + 64 ≤ 2 ^ 32
    rw [BitVec.toNat_add, show (BitVec.ofNat 32 192).toNat = 192 from rfl]
    have fe := H.frameFit
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hp := Whole.finalize_pre hc.esp H a0 a3 a4 dd db da df
  have cov : Covers (Whole.finalizeRd (esp s) ++ Whole.finalizeWr (arg s 2) (digestPtr s))
      (pkRd s ++ Whole.FR (esp s) :: pkWr s) := hash_covers (by
    simp only [Whole.finalizeRd, Whole.finalizeWr, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (argsWithin s (by decide))
    · exact .inr (.inl (shaWithin s))
    · exact .inl ds
    · exact .inr (.inl (workWithin h)))
  have ws := hash_writes (s := s) (rs := Whole.finalizeWr (arg s 2) (digestPtr s)) (by
    simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inr (shaWithin s)
    · exact .inl ds
    · exact .inr (workWithin h))
  exact ⟨Whole.finalizeRd (esp s), Whole.finalizeWr (arg s 2) (digestPtr s), hp, cov, ws⟩

def base_ready {s t : State} (h : Facts s) (hc : Ctx s t) (hs : Slots baseValues s t) :
    Whole.CallReady scalarBaseLocal (esp s) (pkRd s) (pkWr s) t := by
  unfold Slots baseValues at hs
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  simp only [argValue, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at a0 a1 a2
  have ha : BaseArgs s t := ⟨a0, a1, a2⟩
  have scalarWithin : Whole.Within ⟨(scalarPtr s).setWidth 64, 32⟩ (Whole.FR (esp s)) :=
    ⟨32, scalarPtr_addr h.toBounds, by change 32 + 32 ≤ 256; decide⟩
  have cov : Covers (baseRd s ++ pkWr s) (pkRd s ++ Whole.FR (esp s) :: pkWr s) := by
    refine Covers.of_sub ?_
    simp only [baseRd, pkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact ⟨Whole.FR (esp s), by simp, scalarWithin⟩
    · exact ⟨Whole.FR (esp s), by simp, 0, by simp, by change 0 + 12 ≤ 256; decide⟩
    · exact ⟨OUT s, by simp, 0, by simp, by change 0 + 32 ≤ 32; decide⟩
    · exact ⟨SCR s, by simp, 0, by simp, by change 0 + 8192 ≤ 8192; decide⟩
  have ws : ∀ r ∈ pkWr s, Whole.Within r (Whole.FR (esp s)) ∨ ∃ R ∈ pkWr s, Whole.Within r R :=
    fun r hr => .inr ⟨r, hr, 0, by simp, by simp⟩
  exact ⟨baseRd s, pkWr s, base_pre h hc ha, cov, ws⟩

end VG.Proof.Ed25519.X86.PublicKey

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Verified`. -/
section

/-! Merged from `Proof.Ed25519.X86.PublicKey.CT`. -/
section
/-! Merged from `Proof.Ed25519.X86.PublicKey.CTCommon`. -/
section
namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey
open VG.Impl.Ed25519.X86.Whole (Value setup)

def Two (s₁ s₂ : State) (P : State → State → Prop) (a b : State) : Prop :=
  Ctx s₁ a ∧ Ctx s₂ b ∧ P s₁ a ∧ P s₂ b

variable {s₁ s₂ : State}

theorem esp_eq (pub : pkLocal.pub s₁ s₂) : esp s₁ = esp s₂ := congrArg (· - BitVec.ofNat 32 256) pub.1

theorem argValue_eq (pub : pkLocal.pub s₁ s₂) {v : Value} (hv : Whole.valid 3 v) : argValue s₁ v = argValue s₂ v := by
  cases v with
  | const _ => rfl
  | frame d => exact congrArg (· + BitVec.ofNat 32 d) (esp_eq pub)
  | caller i d =>
    apply congrArg (· + BitVec.ofNat 32 d)
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by change i < 3 at hv; omega) with rfl | rfl | rfl
    · exact pub.2.1
    · exact pub.2.2.1
    · exact pub.2.2.2

theorem two_esp (pub : pkLocal.pub s₁ s₂) {P : State → State → Prop} {a b : State} (h : Two s₁ s₂ P a b) :
    a.gpr .esp = b.gpr .esp := h.1.esp.trans ((esp_eq pub).trans h.2.1.esp.symm)

theorem two_wp (h₁ : Facts s₁) (h₂ : Facts s₂) {P Q : State → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two s₁ s₂ P) c fun _ _ => True)
    (hw : ∀ s t, Facts s → Ctx s t → P s t → WP isa c t fun u => Ctx s u ∧ Q s u) :
    RelCT isa (Two s₁ s₂ P) c (Two s₁ s₂ Q) :=
  (hct.wp fun a b h => ⟨hw s₁ a h₁ h.1 h.2.2.1, hw s₂ b h₂ h.2.1 h.2.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => ⟨h.2.1.1, h.2.2.1, h.2.1.2, h.2.2.2⟩

theorem setup_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) (vs : List Value) (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 3 v)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (setup 0 vs)) hint).isSome = true) :
    RelCT isa (Two s₁ s₂ fun _ _ => True) (.block (setup 0 vs)) (Two s₁ s₂ (Slots vs)) :=
  two_wp h₁ h₂ (Whole.block_rel (fun _ _ h => two_esp pub h) ht) fun _ _ h hc _ =>
    WP.mono (VG.Proof.Ed25519.X86.PublicKey.setup_ok h hc hn hv) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩

theorem call_args_eq (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) {vs : List Value} (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 3 v)
    {a b : State} (h : Two s₁ s₂ (Slots vs) a b) {j : Nat} (hj : j < vs.length) :
    arg a.callEntry j = arg b.callEntry j := by
  rw [Whole.call_arg h.1.esp h₁.toBounds.call (by have := h₁.toBounds.frame; omega) (by omega),
    Whole.call_arg h.2.1.esp h₂.toBounds.call (by have := h₂.toBounds.frame; omega) (by omega),
    h.2.2.1 j hj, h.2.2.2 j hj]
  exact argValue_eq pub (hv _ (List.getElem_mem hj))

theorem call_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) {vs : List Value} (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 3 v)
    {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (sp : NoSp c) (stack : stackUse c ≤ 20)
    (ready : ∀ {s t : State}, Facts s → Ctx s t → Slots vs s t →
      Whole.CallReady k (esp s) (pkRd s) (pkWr s) t)
    (kp : ∀ (a b : State) ar aw br bw, a.gpr .esp = b.gpr .esp →
      (∀ j < vs.length, arg a.callEntry j = arg b.callEntry j) →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw)) :
    RelCT isa (Two s₁ s₂ (Slots vs)) (.call name c) (Two s₁ s₂ fun _ _ => True) := by
  apply two_wp h₁ h₂
  · refine Whole.callEx correct ct fun a b h => ?_
    let ra := ready h₁ h.1 h.2.2.1
    let rb := ready h₂ h.2.1 h.2.2.2
    obtain ⟨ca, wa⟩ := ra.covers_state h.1
    obtain ⟨cb, wb⟩ := rb.covers_state h.2.1
    exact ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ (two_esp pub h) (fun _ hj => call_args_eq h₁ h₂ pub hn hv h hj),
      ca, wa, cb, wb, two_esp pub h⟩
  · intro s t h hc hs
    exact WP.mono ((ready h hc hs).wp hc correct sp stack h.toBounds.call) fun _ hu => ⟨hu, trivial⟩

end VG.Proof.Ed25519.X86.PublicKey
end

namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey

variable {s₁ s₂ : State}

theorem init_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) :
    RelCT isa (Two s₁ s₂ (Slots initValues))
      (.call Spec.Sha512.init512Api.name (Impl.Sha512.X86.Stream.init Spec.Sha512.H0_512))
      (Two s₁ s₂ fun _ _ => True) := by
  apply call_ct h₁ h₂ pub (by decide : initValues.length ≤ 6) (by simp [initValues, Whole.valid])
    (Proof.Sha512.X86.Stream.init_verified _).1 (Proof.Sha512.X86.Stream.init_verified _).2.1
    Whole.init_nosp (by rw [Whole.init_stack]; decide) init_ready
  intro a b ar aw br bw he hj
  exact ⟨congrArg (· - 4) he, hj 0 (by decide)⟩

theorem update_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) :
    RelCT isa (Two s₁ s₂ (Slots updateValues)) (.call Spec.Sha512.updateScratchApi.name Impl.Sha512.X86.Stream.update)
      (Two s₁ s₂ fun _ _ => True) := by
  apply call_ct h₁ h₂ pub (by decide : updateValues.length ≤ 6) (by simp [updateValues, Whole.valid])
    Proof.Sha512.X86.Stream.Update.update_verified.1 Proof.Sha512.X86.Stream.Update.update_verified.2.1
    Whole.update_nosp (by rw [Whole.update_stack]) update_ready
  intro a b ar aw br bw he hj
  exact ⟨congrArg (· - 4) he, hj⟩

theorem finalize_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) :
    RelCT isa (Two s₁ s₂ (Slots finalizeValues)) (.call Spec.Sha512.finalizeScratchApi.name Impl.Sha512.X86.Stream.finalize)
      (Two s₁ s₂ fun _ _ => True) := by
  apply call_ct h₁ h₂ pub (by decide : finalizeValues.length ≤ 6) (by simp [finalizeValues, Whole.valid])
    Proof.Sha512.X86.Stream.Finalize.finalize_verified.1 Proof.Sha512.X86.Stream.Finalize.finalize_verified.2.1
    Whole.finalize_nosp (by rw [Whole.finalize_stack]) finalize_ready
  intro a b ar aw br bw he hj
  exact ⟨congrArg (· - 4) he, hj⟩

theorem base_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) :
    RelCT isa (Two s₁ s₂ (Slots baseValues)) (.call "vg_ed25519_scalar_base" Impl.Ed25519.X86.scalarBase)
      (Two s₁ s₂ fun _ _ => True) := by
  apply call_ct h₁ h₂ pub (by decide : baseValues.length ≤ 6) (by simp [baseValues, Whole.valid])
    scalarBase_ok scalarBase_ct base_nosp (by rw [base_stack]; decide) base_ready
  intro a b ar aw br bw he hj
  exact ⟨congrArg (· - 4) he, hj 0 (by decide), hj 1 (by decide), hj 2 (by decide)⟩

theorem prune_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) : RelCT isa (Two s₁ s₂ fun _ _ => True) (.block prune) (Two s₁ s₂ fun _ _ => True) := by
  refine two_wp h₁ h₂ (Whole.block_rel (fun _ _ h => two_esp pub h) (by taint_decide)) ?_
  intro s t h hc _
  exact WP.mono (prune_step h hc (digest := Spec.Sha512.bytesAt t.mem ((esp s).setWidth 64 + 192) 64) rfl)
    fun _ hu => ⟨hu.1, trivial⟩

theorem wipe_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) : RelCT isa (Two s₁ s₂ fun _ _ => True) (.block wipe) (Two s₁ s₂ fun _ _ => True) := by
  refine two_wp h₁ h₂ (Whole.block_rel (fun _ _ h => two_esp pub h) (by taint_decide)) ?_
  intro s t h hc _
  exact WP.mono (Whole.Ctx.zeroWords hc (start := 8) (count := 56)
    (by have := h.toBounds.frame; omega) (by decide)) fun _ hu => ⟨hu.1, trivial⟩

theorem body_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) : RelCT isa (Two s₁ s₂ fun _ _ => True) body (Two s₁ s₂ fun _ _ => True) := by
  have i := setup_ct h₁ h₂ pub initValues (by decide) (by simp [initValues, Whole.valid]) (by taint_decide)
  have u := setup_ct h₁ h₂ pub updateValues (by decide) (by simp [updateValues, Whole.valid]) (by taint_decide)
  have f := setup_ct h₁ h₂ pub finalizeValues (by decide) (by simp [finalizeValues, Whole.valid]) (by taint_decide)
  have b := setup_ct h₁ h₂ pub baseValues (by decide) (by simp [baseValues, Whole.valid]) (by taint_decide)
  exact ((i.seq (init_ct h₁ h₂ pub)).seq
    ((u.seq (update_ct h₁ h₂ pub)).seq (f.seq (finalize_ct h₁ h₂ pub)))).seq
    ((prune_ct h₁ h₂ pub).seq ((b.seq (base_ct h₁ h₂ pub)).seq (wipe_ct h₁ h₂ pub)))

theorem publicKey_ct : ConstantTime isa pkLocal.pre pkLocal.pub publicKey := by
  apply RelCT.constantTime
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ h => h.2.2.1) ?_
  rintro a b ta tb a' b' ⟨s₁, s₂, ⟨p₁, p₂, hp⟩, rfl, rfl⟩ ea eb
  exact ⟨(body_ct (facts p₁) (facts p₂) hp _ _ _ _ _ _
    ⟨push_ctx p₁, push_ctx p₂, trivial, trivial⟩ ea eb).1, trivial⟩

end VG.Proof.Ed25519.X86.PublicKey
end

/-! Merged from `Proof.Ed25519.X86.PublicKey.Lit`. -/
section
namespace VG.Impl.Ed25519.X86.PublicKey
materialize_code publicKey
end VG.Impl.Ed25519.X86.PublicKey
end

/-! Merged from `Proof.Ed25519.X86.PublicKey.Contract`. -/
section
namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86

def pkWide : Contract isa := { pkLocal with
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let seed : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩
    s.rd = [seed] ∧ s.wr = [out, scratch, args] ∧ out.Disjoint seed ∧ out.Disjoint scratch ∧
      seed.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ stack.Disjoint out ∧
      stack.Disjoint seed ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ (s.gpr .esp).toNat ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
}

def pkSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x40 else 0

def pkSatState : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := pkSatMem
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩, ⟨0x8004, 12⟩]

theorem pkWide_pre (s : State) (h : pkWide.pre s) :
    pkLocal.pre (s.withRegions (pkRd s) (pkWr s)) := by
  obtain ⟨_, _, os, oc, sc, ao, ac, ro, rc, ko, ks, kc, no, ns, nc, nb, na⟩ := h
  simp only [pkLocal, pkRd, pkWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, below, Taint.sub_setWidth nb]
  exact ⟨True.intro, True.intro, os, oc, sc, ao, ac, ro, rc, ko, ks, kc, no, ns, nc, nb, na⟩

theorem pkWide_implies : pkWide.Implies (Spec.Ed25519.publicKeyContract X86.abi 280) := by
  have a0 : arg pkSatState 0 = 0x1000 := by decide
  have a1 : arg pkSatState 1 = 0x2000 := by decide
  have a2 : arg pkSatState 2 = 0x4000 := by decide
  have e : argAddr pkSatState 0 = 0x8004 := by decide
  have sp : pkSatState.gpr .esp = 0x8000 := rfl
  sig_implies [Spec.Ed25519.publicKeyContract, Spec.Ed25519.publicKeySig,
    Spec.Ed25519.scratchWords, pkWide, pkLocal, below, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, a2, e, sp] using pkSatState

end VG.Proof.Ed25519.X86.PublicKey
end

namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey

theorem publicKey_verified : Verified X86.target publicKey (Spec.Ed25519.publicKeyContract X86.abi 280) := by
  have hsat := pkWide_implies.sat_left
  have satLocal : ∃ s, pkLocal.pre s := hsat.elim fun s h => ⟨_, pkWide_pre s h⟩
  have verifiedLocal : Verified X86.target publicKey pkLocal :=
    Verified.of_correct (fun _ h => publicKey_ok h) publicKey_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal pkRd pkWr pkWide_pre
    ?_ ?_ ?_ ?_ hsat) pkWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simpa only [pkRd, pkWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_assoc, or_left_comm, or_comm] using hr
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [pkWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [pkWide, pkLocal, arg_withRegions, State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [pkWide, pkLocal, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.Ed25519.X86.PublicKey

end
