module

public import VerifiedGarbage.Impl.Blowfish.AArch64
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Blowfish.KeyTable
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Blowfish.AArch64.Batch
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Blowfish.AArch64.EcbMain
import VerifiedGarbage.Proof.Blowfish.AArch64.Exec
public import VerifiedGarbage.Proof.Blowfish.AArch64.ConstantTime
import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Spec.Blowfish.Contract
import VerifiedGarbage.Proof.Blowfish.AArch64.Lit
import VerifiedGarbage.Proof.Blowfish.F

/-! ### `Blowfish.AArch64.KeyMain`, which only this module used -/

section

/-! ### `Blowfish.AArch64.KeySetup`, which only this module used -/

section

/-!
# Key expansion: the initial S-boxes and the keyed P-array

`copyPlanes_run`: the 4096 bytes of the table at `x9` into the schedule at
`x12`, 64 at a time. `keyP_run`: the 18 P-array entries, the table's XORed
with the key's words, cycling through the key bytes.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64
open VG.Spec.Blowfish VG.Proof.Blowfish
open VG.AArch64.Tbl (VOnly)

theorem write16_at (m : Mem) (p : Addr) (x : BitVec 128) {o j : Nat} (ho : o + 16 ≤ 2 ^ 64) (hj : j < 2 ^ 64) :
    m.write (p + BitVec.ofNat 64 o) 16 x (p + BitVec.ofNat 64 j) =
      if o ≤ j ∧ j < o + 16 then vbyte x (j - o) else m (p + BitVec.ofNat 64 j) := by
  simp only [Mem.write, Offset.sub_toNat' p (show o < 2 ^ 64 by omega_arith) hj]
  by_cases h : o ≤ j
  · simp only [h, ite_true, true_and]
    by_cases h' : j < o + 16
    · simp only [show j - o < 16 by omega_arith, h', ite_true]; rfl
    · simp only [show ¬ j - o < 16 by omega_arith, h', ite_false]
  · simp only [h, ite_false, false_and]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]

/-- What `copyPlanes` needs: the table readable at `T`, the schedule
writable at `S`, apart. -/
structure CopyEnv (T S : Addr) (s : State) : Prop where
  rdT : InRegions (s.rd ++ s.wr) T 4168
  wrS : InRegions s.wr S 4168
  sep : (⟨T, 4168⟩ : Region).Disjoint ⟨S, 4168⟩
  fitT : T.toNat + 4168 ≤ 2 ^ 64
  fitS : S.toNat + 4168 ≤ 2 ^ 64

theorem inRegions_off {rs : List Region} {a : Addr} {N o n : Nat} (h : InRegions rs a N) (hon : o + n ≤ N) :
    InRegions rs (a + BitVec.ofNat 64 o) n := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at hc ⊢
  obtain e : a + BitVec.ofNat 64 o - r.base = (a - r.base) + BitVec.ofNat 64 o := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 o),
      ← BitVec.add_assoc]
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := Nat.mod_le ((a - r.base).toNat + o % 2 ^ 64) (2 ^ 64)
  have := Nat.mod_le o (2 ^ 64)
  omega_arith

/-- The loop of `copyPlanes`, from iteration `i`. -/
structure CopyPInv (T S : Addr) (s₀ : State) (i : Nat) (u : State) : Prop where
  le : i ≤ 64
  x9 : u.gpr .x9 = T + BitVec.ofNat 64 (64 * i)
  x12 : u.gpr .x12 = S + BitVec.ofNat 64 (64 * i)
  x11 : u.gpr .x11 = BitVec.ofNat 64 (64 - i)
  copied : ∀ o < 64 * i, u.mem (S + BitVec.ofNat 64 o) = s₀.mem (T + BitVec.ofNat 64 o)
  frame : Frame [⟨S, 4096⟩] s₀.mem u.mem
  gpr : ∀ r, r ≠ .x9 → r ≠ .x11 → r ≠ .x12 → u.gpr r = s₀.gpr r
  rd : u.rd = s₀.rd
  wr : u.wr = s₀.wr
  sp : u.sp = s₀.sp
  v : ∀ r, r ∉ [VReg.v28, .v29, .v30, .v31] → u.v r = s₀.v r

theorem copyBody_eq :
    ((List.range 4).map (fun r => Instr.ldrq (tReg r) .x9 (16 * r)) ++
      (List.range 4).map (fun r => Instr.strq (tReg r) .x12 (16 * r)) ++
      ([.addImm .x .x9 .x9 64, .addImm .x .x12 .x12 64, .subImm .x .x11 .x11 1] : List Instr)) =
    [.ldrq .v28 .x9 0, .ldrq .v29 .x9 16, .ldrq .v30 .x9 32, .ldrq .v31 .x9 48,
     .strq .v28 .x12 0, .strq .v29 .x12 16, .strq .v30 .x12 32, .strq .v31 .x12 48,
     .addImm .x .x9 .x9 64, .addImm .x .x12 .x12 64, .subImm .x .x11 .x11 1] := rfl

theorem copyStep {T S : Addr} {s₀ : State} (E : CopyEnv T S s₀) {i : Nat} (hi : i < 64) {u : State}
    (I : CopyPInv T S s₀ i u) :
    ∃ u', runBlock isa ([.ldrq .v28 .x9 0, .ldrq .v29 .x9 16, .ldrq .v30 .x9 32, .ldrq .v31 .x9 48,
      .strq .v28 .x12 0, .strq .v29 .x12 16, .strq .v30 .x12 32, .strq .v31 .x12 48,
      .addImm .x .x9 .x9 64, .addImm .x .x12 .x12 64, .subImm .x .x11 .x11 1]) u = some u' ∧
      CopyPInv T S s₀ (i + 1) u' := by
  obtain rdT : ∀ r < 4, ∀ {t : State}, t.rd = s₀.rd → t.wr = s₀.wr → t.gpr .x9 = u.gpr .x9 →
      InRegions (t.rd ++ t.wr) (t.gpr .x9 + BitVec.ofNat 64 (16 * r)) 16 := by
    intro r hr t h1 h2 h3
    rw [h1, h2, h3, I.x9, Offset.add_add]
    exact inRegions_off E.rdT (by omega_arith)
  obtain wrS : ∀ r < 4, ∀ {t : State}, t.wr = s₀.wr → t.gpr .x12 = u.gpr .x12 →
      InRegions t.wr (t.gpr .x12 + BitVec.ofNat 64 (16 * r)) 16 := by
    intro r hr t h2 h3
    rw [h2, h3, I.x12, Offset.add_add]
    exact inRegions_off E.wrS (by omega_arith)
  obtain ⟨u₁, r₁, v₁, o₁⟩ := ldrq_run (t := u) .v28 .x9 (off := 16 * 0) (by omega_arith) (rdT 0 (by decide) I.rd I.wr rfl)
  obtain ⟨u₂, r₂, v₂, o₂⟩ := ldrq_run (t := u₁) .v29 .x9 (off := 16 * 1) (by omega_arith)
    (rdT 1 (by decide) (o₁.rd.trans I.rd) (o₁.wr.trans I.wr) (by rw [o₁.gpr]))
  obtain ⟨u₃, r₃, v₃, o₃⟩ := ldrq_run (t := u₂) .v30 .x9 (off := 16 * 2) (by omega_arith)
    (rdT 2 (by decide) (o₂.rd.trans (o₁.rd.trans I.rd)) (o₂.wr.trans (o₁.wr.trans I.wr)) (by rw [o₂.gpr, o₁.gpr]))
  obtain ⟨u₄, r₄, v₄, o₄⟩ := ldrq_run (t := u₃) .v31 .x9 (off := 16 * 3) (by omega_arith)
    (rdT 3 (by decide) (o₃.rd.trans (o₂.rd.trans (o₁.rd.trans I.rd)))
      (o₃.wr.trans (o₂.wr.trans (o₁.wr.trans I.wr))) (by rw [o₃.gpr, o₂.gpr, o₁.gpr]))
  obtain o₁₄ : VOnly [.v28, .v29, .v30, .v31] u u₄ := (((VOnly.mono o₁ (by simp)).trans (VOnly.mono o₂ (by simp))).trans
    (VOnly.mono o₃ (by simp))).trans (VOnly.mono o₄ (by simp))
  -- the values loaded
  have g₄ : u₄.gpr = u.gpr := o₁₄.gpr
  have mm₄ : u₄.mem = u.mem := o₁₄.mem
  obtain ld : ∀ r < 4, u₄.v (tReg r) = u.mem.read (T + BitVec.ofNat 64 (64 * i + 16 * r)) 16 := by
    intro r hr
    obtain a : ∀ q : Nat, u.gpr .x9 + BitVec.ofNat 64 (16 * q) = T + BitVec.ofNat 64 (64 * i + 16 * q) := by
      intro q; rw [I.x9, Offset.add_add]
    rcases (by omega_arith : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl
    · rw [show tReg 0 = .v28 from rfl, o₄.2 _ (by simp), o₃.2 _ (by simp), o₂.2 _ (by simp), v₁, a]
    · rw [show tReg 1 = .v29 from rfl, o₄.2 _ (by simp), o₃.2 _ (by simp), v₂, o₁.mem, o₁.gpr, a]
    · rw [show tReg 2 = .v30 from rfl, o₄.2 _ (by simp), v₃, o₂.mem, o₁.mem, o₂.gpr, o₁.gpr, a]
    · rw [show tReg 3 = .v31 from rfl, v₄, o₃.mem, o₂.mem, o₁.mem, o₃.gpr, o₂.gpr, o₁.gpr, a]
  obtain wr₄ : u₄.wr = s₀.wr := o₁₄.wr.trans I.wr
  obtain ⟨u₅, r₅, m₅, p₅⟩ := strq_run (t := u₄) .v28 .x12 (off := 16 * 0) (by omega_arith) (wrS 0 (by decide) wr₄ (by rw [g₄]))
  obtain ⟨u₆, r₆, m₆, p₆⟩ := strq_run (t := u₅) .v29 .x12 (off := 16 * 1) (by omega_arith)
    (wrS 1 (by decide) (p₅.wr.trans wr₄) (by rw [p₅.gpr, g₄]))
  obtain ⟨u₇, r₇, m₇, p₇⟩ := strq_run (t := u₆) .v30 .x12 (off := 16 * 2) (by omega_arith)
    (wrS 2 (by decide) (p₆.wr.trans (p₅.wr.trans wr₄)) (by rw [p₆.gpr, p₅.gpr, g₄]))
  obtain ⟨u₈, r₈, m₈, p₈⟩ := strq_run (t := u₇) .v31 .x12 (off := 16 * 3) (by omega_arith)
    (wrS 3 (by decide) (p₇.wr.trans (p₆.wr.trans (p₅.wr.trans wr₄))) (by rw [p₇.gpr, p₆.gpr, p₅.gpr, g₄]))
  obtain p₅₈ : MOnly [] u₄ u₈ := ((p₅.trans p₆).trans p₇).trans p₈
  let u₉ := u₈.write .x .x9 (u₈.read .x .x9 + BitVec.ofNat _ 64)
  let u₁₀ := u₉.write .x .x12 (u₉.read .x .x12 + BitVec.ofNat _ 64)
  let u₁₁ := u₁₀.write .x .x11 (u₁₀.read .x .x11 - BitVec.ofNat _ 1)
  obtain r₉ : runBlock isa [.addImm .x .x9 .x9 64, .addImm .x .x12 .x12 64, .subImm .x .x11 .x11 1] u₈ = some u₁₁ := by
    rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide),
      runStep_some, runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil]
  refine ⟨u₁₁, cat_run r₁ (cat_run r₂ (cat_run r₃ (cat_run r₄ (cat_run r₅ (cat_run r₆ (cat_run r₇ (cat_run r₈ r₉))))))),
    ?_⟩
  -- the stored values
  obtain vv : ∀ r < 4, u₇.v (tReg r) = u₄.v (tReg r) := fun r _ => by
    rw [p₇.v _ (List.not_mem_nil), p₆.v _ (List.not_mem_nil), p₅.v _ (List.not_mem_nil)]
  obtain gg : u₇.gpr = u₄.gpr := by rw [p₇.gpr, p₆.gpr, p₅.gpr]
  obtain x12₄ : u₄.gpr .x12 = S + BitVec.ofNat 64 (64 * i) := by rw [g₄, I.x12]
  obtain memS : ∀ o < 64 * (i + 1), u₈.mem (S + BitVec.ofNat 64 o) = s₀.mem (T + BitVec.ofNat 64 o) := by
    intro o ho
    have fS := E.fitS
    rw [m₈, show u₇.gpr = u₄.gpr from gg, x12₄, Offset.add_add, write16_at _ _ _ (by omega_arith) (by omega_arith),
      m₇, show u₆.gpr = u₄.gpr by rw [p₆.gpr, p₅.gpr], x12₄, Offset.add_add,
      write16_at _ _ _ (by omega_arith) (by omega_arith),
      m₆, show u₅.gpr = u₄.gpr by rw [p₅.gpr], x12₄, Offset.add_add, write16_at _ _ _ (by omega_arith) (by omega_arith),
      m₅, x12₄, Offset.add_add, write16_at _ _ _ (by omega_arith) (by omega_arith), mm₄]
    obtain hT : ∀ o' < 4168, u.mem (T + BitVec.ofNat 64 o') = s₀.mem (T + BitVec.ofNat 64 o') := fun o' ho' =>
      I.frame.bytes (R := ⟨T, 4168⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact E.sep.sub_right (Region.sub_prefix (by omega_arith))) (show 4168 ≤ 2 ^ 64 by decide) ho'
    obtain byteAt : ∀ r < 4, ∀ (x : BitVec 128), x = u₄.v (tReg r) → 64 * i + 16 * r ≤ o →
        o < 64 * i + 16 * r + 16 → vbyte x (o - (64 * i + 16 * r)) = s₀.mem (T + BitVec.ofNat 64 o) := by
      intro r hr x hx h1 h2
      rw [hx, ld r hr, vbyte_read16 _ _ (by omega_arith), Offset.add_add,
        show 64 * i + 16 * r + (o - (64 * i + 16 * r)) = o by omega_arith, hT o (by omega_arith)]
    split
    · exact byteAt 3 (by decide) _ (vv 3 (by decide)) (by omega_arith) (by omega_arith)
    · split
      · exact byteAt 2 (by decide) _ (by rw [p₆.v _ (List.not_mem_nil), p₅.v _ (List.not_mem_nil)]; rfl)
          (by omega_arith) (by omega_arith)
      · split
        · exact byteAt 1 (by decide) _ (by rw [p₅.v _ (List.not_mem_nil)]; rfl) (by omega_arith) (by omega_arith)
        · split
          · exact byteAt 0 (by decide) _ rfl (by omega_arith) (by omega_arith)
          · exact I.copied o (by omega_arith)
  obtain g₈ : u₈.gpr = u.gpr := by rw [p₅₈.gpr, g₄]
  have fS := E.fitS
  obtain fr : Frame [⟨S, 4096⟩] s₀.mem u₈.mem := by
    obtain c : ∀ r < 4, (⟨S, 4096⟩ : Region).Contains (S + BitVec.ofNat 64 (64 * i + 16 * r)) 16 :=
      fun r hr => Offset.contains_base _ (by omega_arith) (by omega_arith)
    rw [m₈, m₇, m₆, m₅, show u₇.gpr = u₄.gpr from gg, show u₆.gpr = u₄.gpr by rw [p₆.gpr, p₅.gpr],
      show u₅.gpr = u₄.gpr by rw [p₅.gpr], x12₄, Offset.add_add, Offset.add_add, Offset.add_add,
      Offset.add_add, mm₄]
    exact (((I.frame.write List.mem_cons_self _ (c 0 (by decide))).write List.mem_cons_self _ (c 1 (by decide))).write
      List.mem_cons_self _ (c 2 (by decide))).write List.mem_cons_self _ (c 3 (by decide))
  refine ⟨by omega_arith, ?_, ?_, ?_, fun o ho => memS o ho, fr, fun r a b c => ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · simp only [u₁₁, u₁₀, u₉, State.write, State.read, BitVec.setWidth_eq, reduceCtorEq, ite_false, ite_true]
    rw [g₈, I.x9, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact congrArg _ (congrArg _ (by omega_arith))
  · simp only [u₁₁, u₁₀, State.write, State.read, BitVec.setWidth_eq, reduceCtorEq, ite_false, ite_true]
    rw [show u₉.gpr .x12 = u₈.gpr .x12 from rfl, g₈, I.x12, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact congrArg _ (congrArg _ (by omega_arith))
  · simp only [u₁₁, State.write, State.read, BitVec.setWidth_eq, ite_true]
    rw [show u₁₀.gpr .x11 = u₈.gpr .x11 from rfl, g₈, I.x11, show 64 - i = (64 - (i + 1)) + 1 by omega_arith,
      ← BitVec.ofNat_add_ofNat]
    exact BitVec.add_sub_cancel _ _
  · simp only [u₁₁, u₁₀, u₉, State.write, a, b, c, ite_false]
    rw [g₈, I.gpr r a b c]
  · rw [show u₁₁.rd = u₈.rd from rfl, p₅₈.rd, o₁₄.rd, I.rd]
  · rw [show u₁₁.wr = u₈.wr from rfl, p₅₈.wr, o₁₄.wr, I.wr]
  · rw [show u₁₁.sp = u₈.sp from rfl, p₅₈.sp, show u₄.sp = u.sp by rw [o₁₄.1], I.sp]
  · rw [show u₁₁.v = u₈.v from rfl, p₅₈.v _ (List.not_mem_nil), o₁₄.2 _ hr, I.v _ hr]



theorem copyPlanes_run {s : State} {T S : Addr} (E : CopyEnv T S s) (hx9 : s.gpr .x9 = T)
    (hx12 : s.gpr .x12 = S) :
    WP isa copyPlanes s fun u => ∃ u₀, u₀ = s.write .x .x11 ((64 : BitVec 16).setWidth 64 <<< (16 * 0)) ∧
      CopyPInv T S u₀ 64 u := by
  let s₁ := s.write .x .x11 ((64 : BitVec 16).setWidth 64 <<< (16 * 0))
  obtain E₁ : CopyEnv T S s₁ := ⟨E.rdT, E.wrS, E.sep, E.fitT, E.fitS⟩
  rw [copyPlanes]
  apply WP.seq
  refine WP.of_runBlock ⟨s₁, rfl, ?_⟩
  obtain I₀ : CopyPInv T S s₁ 0 s₁ := ⟨by omega_arith, by simp [s₁, gpr_write, hx9], by simp [s₁, gpr_write, hx12],
    rfl, fun o ho => by omega_arith, Frame.refl _ _, fun _ _ _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  refine WP.mono (WP.loop (M := isa) (Q := CopyPInv T S s₁ 64) (fun m u => ∃ i, i < 64 ∧ m = 64 - i ∧
    CopyPInv T S s₁ i u) ?_ 64 s₁ ⟨0, by omega_arith, rfl, I₀⟩) fun u h => ⟨s₁, rfl, h⟩
  intro m u ⟨i, hi, hm, I⟩
  obtain ⟨u', r, I'⟩ := copyStep E₁ hi I
  refine WP.of_runBlock ⟨u', by rw [copyBody_eq]; exact r, ?_⟩
  obtain flag := eval_nonzero u' .x11 I'.x11 (by omega_arith)
  by_cases h : i + 1 = 64
  · left; exact ⟨by rw [flag]; simp; omega_arith, h ▸ I'⟩
  · right; exact ⟨by rw [flag]; simp; omega_arith, 64 - (i + 1), by omega_arith, i + 1, by omega_arith, rfl, I'⟩

/-! ## The P-array -/

/-- The key's bytes readable at `K`, `L` of them. -/
def KeyIn (s : State) (K : Addr) (L : Nat) : Prop := ∀ c < L, InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 c) 1

/-- The registers `keyByte` writes. -/
abbrev KeyByteRegs (r : Reg) : Prop := r ≠ .x8 ∧ r ≠ .x10 ∧ r ≠ .x13 ∧ r ≠ .x14

theorem keyByte_run {s : State} {K : Addr} {L c : Nat} (hc : c < L) (hL : L < 2 ^ 64)
    (hK : KeyIn s K L) (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 L)
    (h10 : s.gpr .x10 = BitVec.ofNat 64 c) :
    WP isa keyByte s fun s' =>
      (s'.gpr .x8).setWidth 32 = ((s.gpr .x8).setWidth 32 <<< 8) ||| (s.mem (K + BitVec.ofNat 64 c)).zeroExtend 32 ∧
      s'.gpr .x10 = BitVec.ofNat 64 ((c + 1) % L) ∧ (∀ r, KeyByteRegs r → s'.gpr r = s.gpr r) ∧
      s' = { s with gpr := s'.gpr } := by
  rw [keyByte]
  apply WP.seq
  let s₁ := s.write .x .x13 (s.read .x .x0 + s.read .x .x10)
  obtain a₁ : s₁.gpr .x13 + BitVec.ofNat 64 0 = K + BitVec.ofNat 64 c := by
    simp [s₁, gpr_write, State.read, h0, h10]
  obtain hr₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x13 + BitVec.ofNat 64 0) 1 := by
    rw [a₁]; exact hK c hc
  let byte := s.mem (K + BitVec.ofNat 64 c)
  let s₂ := s₁.write .w .x14 ((s₁.mem.read (s₁.gpr .x13 + BitVec.ofNat 64 0) 1).setWidth 32)
  obtain e₂ : exec (.ldrb .x14 .x13 0) s₁ = some s₂ := by
    simp only [exec, addr, show 0 % 1 = 0 from rfl, show 0 < 4096 * 1 by decide, and_self, ite_true,
      Option.bind_some, State.load, hr₁, Option.map_some]
    rfl
  let s₃ := s₂.write .w .x8 (s₂.read .w .x8 <<< 8)
  let s₄ := s₃.write .w .x8 (s₃.read .w .x8 ||| s₃.read .w .x14)
  let s₅ := s₄.write .x .x10 (s₄.read .x .x10 + BitVec.ofNat _ 1)
  let s₆ := s₅.write .x .x13 (s₅.read .x .x10 - s₅.read .x .x1)
  refine WP.of_runBlock ⟨s₆, by
    rw [runBlock_cons, exec_add, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons]
    simp only [exec, show 8 < Size.w.bits by decide, ite_true]
    rw [runStep_some, runBlock_cons, exec_logic, runStep_some, runBlock_cons, exec_addImm_x (by decide),
      runStep_some, runBlock_cons]
    simp only [exec]
    rw [runStep_some, runBlock_nil], ?_⟩
  -- the byte, and the index
  obtain r1 : ∀ (m : Mem) (a : Addr), (m.read a 1).setWidth 32 = (m a).zeroExtend 32 := by
    intro m a
    obtain h := Mem.extractLsb'_read m a (n := 1) (j := 0) (by decide)
    obtain e : (m.read a 1) = (m.read a 1).extractLsb' (8 * 0) 8 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
    rw [e, h, BitVec.add_zero]
  obtain x8₆ : (s₆.gpr .x8).setWidth 32 =
      ((s.gpr .x8).setWidth 32 <<< 8) ||| (s.mem (K + BitVec.ofNat 64 c)).zeroExtend 32 := by
    simp only [s₆, s₅, s₄, s₃, s₂, s₁, State.write, State.read, reduceCtorEq, ite_false, ite_true,
      Size.bits, BitVec.setWidth_eq, BitVec.add_zero, h0, h10, r1]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [hi]
  obtain x10₆ : s₆.gpr .x10 = BitVec.ofNat 64 (c + 1) := by
    simp only [s₆, s₅, State.write, State.read, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
    rw [show s₄.gpr .x10 = s.gpr .x10 by simp [s₄, s₃, s₂, s₁, gpr_write, mem_write], h10, BitVec.ofNat_add_ofNat]
  obtain x13₆ : s₆.gpr .x13 = BitVec.ofNat 64 (c + 1) - BitVec.ofNat 64 L := by
    simp only [s₆, State.write, State.read, ite_true, BitVec.setWidth_eq]
    rw [show s₅.gpr .x10 = s₆.gpr .x10 by simp [s₆, gpr_write], x10₆,
      show s₅.gpr .x1 = s.gpr .x1 by simp [s₅, s₄, s₃, s₂, s₁, gpr_write, mem_write], h1]
  obtain g₆ : ∀ r, KeyByteRegs r → s₆.gpr r = s.gpr r := by
    intro r ⟨a, b, c', d⟩
    simp [s₆, s₅, s₄, s₃, s₂, s₁, gpr_write, mem_write, a, b, c', d]
  obtain zero : isa.eval (.zero .x .x13) s₆ = some (c + 1 == L) := by
    show some (s₆.read .x .x13 == 0) = _
    simp only [State.read, BitVec.setWidth_eq, x13₆]
    congr 1
    by_cases h : c + 1 = L
    · subst h; simp
    · have : BitVec.ofNat 64 (c + 1) - BitVec.ofNat 64 L ≠ 0 := by
        intro e
        obtain e' := congrArg (· + BitVec.ofNat 64 L) e
        simp only [BitVec.sub_add_cancel] at e'
        have := congrArg BitVec.toNat e'
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
        rw [show BitVec.toNat (0 : BitVec 64) = 0 from rfl, Nat.zero_add, Nat.mod_eq_of_lt hL,
          Nat.mod_eq_of_lt hL, Nat.mod_eq_of_lt (by omega_arith)] at this
        omega_arith
      simp only [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h]
  obtain st₆ : s₆ = { s with gpr := s₆.gpr } := rfl
  apply WP.ite _ zero
  · intro h
    obtain hL' : c + 1 = L := by simpa using h
    let s₇ := s₆.write .x .x10 ((0 : BitVec 16).setWidth 64 <<< (16 * 0))
    refine WP.of_runBlock ⟨s₇, rfl, ?_, ?_, fun r hr => ?_, rfl⟩
    · simp only [s₇, State.write, reduceCtorEq, ite_false]; exact x8₆
    · simp [s₇, gpr_write, ← hL']
    · simp only [s₇, State.write, hr.2.1, ite_false]; exact g₆ r hr
  · intro h
    obtain hL' : c + 1 ≠ L := by simpa using h
    exact WP.block_nil ⟨x8₆, by rw [x10₆, Nat.mod_eq_of_lt (by omega_arith)], g₆, st₆⟩

/-- What a P-array entry's code needs. -/
structure KeyWordEnv (T S K : Addr) (L : Nat) (i : Nat) (s : State) : Prop where
  lt : i < 18
  L0 : 0 < L
  L64 : L < 2 ^ 64
  key : KeyIn s K L
  x0 : s.gpr .x0 = K
  x1 : s.gpr .x1 = BitVec.ofNat 64 L
  x10 : s.gpr .x10 = BitVec.ofNat 64 ((4 * i) % L)
  x9 : s.gpr .x9 = T + BitVec.ofNat 64 (4096 + 4 * i)
  x12 : s.gpr .x12 = S + BitVec.ofNat 64 (4096 + 4 * i)
  rdT : InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (4096 + 4 * i)) 4
  wrS : InRegions s.wr (S + BitVec.ofNat 64 (4096 + 4 * i)) 4

/-- The registers an entry's code writes. -/
abbrev KeyWordRegs (r : Reg) : Prop :=
  r ≠ .x8 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x14

theorem keyWord_run {T S K : Addr} {L i : Nat} {s : State} (E : KeyWordEnv T S K L i s) :
    WP isa keyWord s fun s' =>
      s'.mem = s.mem.writeW (S + BitVec.ofNat 64 (4096 + 4 * i))
        (s.mem.readW (T + BitVec.ofNat 64 (4096 + 4 * i)) 32 ^^^ keyWord (bytesAt s.mem K L) i) ∧
      s'.gpr .x10 = BitVec.ofNat 64 ((4 * (i + 1)) % L) ∧
      s'.gpr .x9 = s.gpr .x9 + 4 ∧ s'.gpr .x12 = s.gpr .x12 + 4 ∧ s'.gpr .x11 = s.gpr .x11 - 1 ∧
      (∀ r, KeyWordRegs r → s'.gpr r = s.gpr r) ∧ s' = { s with gpr := s'.gpr, mem := s'.mem } := by
  have hL0 := E.L0
  rw [Impl.Blowfish.AArch64.keyWord]
  apply WP.seq
  let s₀ := s.write .x .x8 ((0 : BitVec 16).setWidth 64 <<< (16 * 0))
  refine WP.of_runBlock ⟨s₀, rfl, ?_⟩
  have k₀ : KeyIn s₀ K L := E.key
  obtain g₀ : ∀ r, r ≠ .x8 → s₀.gpr r = s.gpr r := fun r hr => by simp [s₀, gpr_write, hr]
  obtain x8₀ : (s₀.gpr .x8).setWidth 32 = 0 := by simp [s₀, gpr_write]
  -- the four key bytes
  obtain step : ∀ (t : State) (m : Nat), t = { s with gpr := t.gpr } → t.gpr .x0 = K →
      t.gpr .x1 = BitVec.ofNat 64 L → t.gpr .x10 = BitVec.ofNat 64 ((4 * i + m) % L) →
      ∀ {Q : State → Prop}, (∀ t', (t'.gpr .x8).setWidth 32 = ((t.gpr .x8).setWidth 32 <<< 8) |||
        ((bytesAt s.mem K L).getD ((4 * i + m) % L) 0).zeroExtend 32 →
        t'.gpr .x10 = BitVec.ofNat 64 ((4 * i + (m + 1)) % L) → (∀ r, KeyByteRegs r → t'.gpr r = t.gpr r) →
        t' = { s with gpr := t'.gpr } → Q t') → WP isa keyByte t Q := by
    intro t m ht h0 h1 h10 Q k
    obtain kt : KeyIn t K L := by rw [ht]; exact E.key
    refine WP.mono (keyByte_run (Nat.mod_lt _ hL0) E.L64 kt h0 h1 h10) fun t' ⟨a, b, c, d⟩ => k t' ?_ ?_ c ?_
    · rw [a, bytesAt_getD _ _ (Nat.mod_lt _ hL0), ht]
    · rw [b, mod_succ _ _ hL0, Nat.add_assoc]
    · rw [d, ht]
  obtain e₀ : s₀ = { s with gpr := s₀.gpr } := rfl
  obtain hlen : (bytesAt s.mem K L).length = L := by simp [bytesAt]
  apply WP.seq
  refine step s₀ 0 e₀ (by rw [g₀ _ (by decide), E.x0]) (by rw [g₀ _ (by decide), E.x1])
    (by rw [g₀ _ (by decide), E.x10]; rfl) fun t₁ a₁ b₁ c₁ d₁ => ?_
  apply WP.seq
  refine step t₁ 1 d₁ (by rw [c₁ _ (by decide), g₀ _ (by decide), E.x0])
    (by rw [c₁ _ (by decide), g₀ _ (by decide), E.x1]) b₁ fun t₂ a₂ b₂ c₂ d₂ => ?_
  apply WP.seq
  refine step t₂ 2 d₂ (by rw [c₂ _ (by decide), c₁ _ (by decide), g₀ _ (by decide), E.x0])
    (by rw [c₂ _ (by decide), c₁ _ (by decide), g₀ _ (by decide), E.x1]) b₂ fun t₃ a₃ b₃ c₃ d₃ => ?_
  apply WP.seq
  refine step t₃ 3 d₃ (by rw [c₃ _ (by decide), c₂ _ (by decide), c₁ _ (by decide), g₀ _ (by decide), E.x0])
    (by rw [c₃ _ (by decide), c₂ _ (by decide), c₁ _ (by decide), g₀ _ (by decide), E.x1]) b₃
    fun t₄ a₄ b₄ c₄ d₄ => ?_
  -- the word
  obtain kw : (t₄.gpr .x8).setWidth 32 = keyWord (bytesAt s.mem K L) i := by
    rw [a₄, a₃, a₂, a₁, x8₀, keyWord_eq, hlen]
  obtain g₄ : ∀ r, KeyByteRegs r → r ≠ .x8 → t₄.gpr r = s.gpr r := fun r hr h8 => by
    rw [c₄ r hr, c₃ r hr, c₂ r hr, c₁ r hr, g₀ r h8]
  obtain x9₄ : t₄.gpr .x9 = T + BitVec.ofNat 64 (4096 + 4 * i) :=
    (g₄ _ (by decide) (by decide)).trans E.x9
  obtain x12₄ : t₄.gpr .x12 = S + BitVec.ofNat 64 (4096 + 4 * i) :=
    (g₄ _ (by decide) (by decide)).trans E.x12
  obtain m₄ : t₄.mem = s.mem := by rw [d₄]
  obtain rdT : InRegions (t₄.rd ++ t₄.wr) (t₄.gpr .x9 + BitVec.ofNat 64 0) 4 := by
    obtain h1 : t₄.rd = s.rd := by rw [d₄]
    obtain h2 : t₄.wr = s.wr := by rw [d₄]
    rw [h1, h2, BitVec.add_zero, x9₄]; exact E.rdT
  let t₅ := t₄.write .w .x14 (t₄.mem.readW (t₄.gpr .x9 + BitVec.ofNat 64 0) 32)
  let t₆ := t₅.write .w .x14 (t₅.read .w .x14 ^^^ t₅.read .w .x8)
  obtain wrS : InRegions t₆.wr (t₆.gpr .x12 + BitVec.ofNat 64 0) 4 := by
    obtain h2 : t₆.wr = s.wr := by rw [show t₆.wr = t₄.wr from rfl, d₄]
    obtain h3 : t₆.gpr .x12 = t₄.gpr .x12 := by simp [t₆, t₅, gpr_write]
    rw [h2, h3, BitVec.add_zero, x12₄]; exact E.wrS
  let t₇ : State := { t₆ with mem := t₆.mem.writeW (t₆.gpr .x12 + BitVec.ofNat 64 0) ((t₆.gpr .x14).setWidth 32) }
  let t₈ := t₇.write .x .x9 (t₇.read .x .x9 + BitVec.ofNat _ 4)
  let t₉ := t₈.write .x .x12 (t₈.read .x .x12 + BitVec.ofNat _ 4)
  let t₁₀ := t₉.write .x .x11 (t₉.read .x .x11 - BitVec.ofNat _ 1)
  refine WP.of_runBlock ⟨t₁₀, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_⟩
  · rw [runBlock_cons, exec_ldr_w (by decide) rdT, runStep_some, runBlock_cons, exec_logic, runStep_some,
      runBlock_cons, exec_str_w (by decide) wrS, runStep_some, runBlock_cons, exec_addImm_x (by decide),
      runStep_some, runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_nil]
  · show t₆.mem.writeW _ _ = _
    obtain h14 : (t₆.gpr .x14).setWidth 32 =
        s.mem.readW (T + BitVec.ofNat 64 (4096 + 4 * i)) 32 ^^^ keyWord (bytesAt s.mem K L) i := by
      simp only [t₆, t₅, State.write, State.read, ite_true, reduceCtorEq, ite_false, Size.bits,
        BitVec.add_zero]
      rw [m₄, x9₄, ← kw]
      apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [hj]
    obtain h12 : t₆.gpr .x12 = t₄.gpr .x12 := by simp [t₆, t₅, gpr_write]
    rw [h14, h12, BitVec.add_zero, x12₄, show t₆.mem = s.mem from m₄]
  · simp [t₁₀, t₉, t₈, t₇, t₆, t₅, gpr_write, v_write, mem_write, rd_write, wr_write, sp_write]
    rw [b₄]; rfl
  · simp [t₁₀, t₉, t₈, t₇, t₆, t₅, gpr_write, v_write, mem_write, rd_write, wr_write, sp_write, State.read]
    rw [g₄ _ (by decide) (by decide)]
  · simp [t₁₀, t₉, t₈, t₇, t₆, t₅, gpr_write, v_write, mem_write, rd_write, wr_write, sp_write, State.read]
    rw [g₄ _ (by decide) (by decide)]
  · simp [t₁₀, t₉, t₈, t₇, t₆, t₅, gpr_write, v_write, mem_write, rd_write, wr_write, sp_write, State.read]
    rw [g₄ _ (by decide) (by decide)]
  · obtain ⟨a, b, c, d, e, f, g⟩ := hr
    simp [t₁₀, t₉, t₈, t₇, t₆, t₅, gpr_write, v_write, mem_write, rd_write, wr_write, sp_write, b, d, e, g]
    exact g₄ r ⟨a, c, f, g⟩ a
  · simp only [t₁₀, t₉, t₈, t₇, t₆, t₅, State.write]
    rw [d₄]

/-- What the P-array loop needs, of the state it starts in. -/
structure KeyPEnv (T S K : Addr) (L : Nat) (s : State) : Prop where
  L0 : 0 < L
  L64 : L < 2 ^ 64
  key : KeyIn s K L
  x0 : s.gpr .x0 = K
  x1 : s.gpr .x1 = BitVec.ofNat 64 L
  x9 : s.gpr .x9 = T + BitVec.ofNat 64 4096
  x12 : s.gpr .x12 = S + BitVec.ofNat 64 4096
  rdT : InRegions (s.rd ++ s.wr) T 4168
  wrS : InRegions s.wr S 4168
  sep : (⟨T, 4168⟩ : Region).Disjoint ⟨S, 4168⟩
  keyS : ∀ c < L, ¬ (⟨S, 4168⟩ : Region).Contains (K + BitVec.ofNat 64 c) 1

/-- After `i` entries. -/
structure KeyPInv (T S K : Addr) (L : Nat) (s₀ : State) (i : Nat) (u : State) : Prop where
  le : i ≤ 18
  x10 : u.gpr .x10 = BitVec.ofNat 64 ((4 * i) % L)
  x9 : u.gpr .x9 = T + BitVec.ofNat 64 (4096 + 4 * i)
  x12 : u.gpr .x12 = S + BitVec.ofNat 64 (4096 + 4 * i)
  x11 : u.gpr .x11 = BitVec.ofNat 64 (18 - i)
  done : ∀ j < i, u.mem.readW (S + BitVec.ofNat 64 (4096 + 4 * j)) 32 =
    s₀.mem.readW (T + BitVec.ofNat 64 (4096 + 4 * j)) 32 ^^^ keyWord (bytesAt s₀.mem K L) j
  frame : Frame [⟨S + BitVec.ofNat 64 4096, 4 * i⟩] s₀.mem u.mem
  gpr : ∀ r, KeyWordRegs r → u.gpr r = s₀.gpr r
  eq : u = { s₀ with gpr := u.gpr, mem := u.mem }

theorem keyP_step {T S K : Addr} {L : Nat} {s₀ : State} (E : KeyPEnv T S K L s₀) {i : Nat} (hi : i < 18)
    {u : State} (I : KeyPInv T S K L s₀ i u) :
    WP isa keyWord u (KeyPInv T S K L s₀ (i + 1)) := by
  obtain hrd : u.rd = s₀.rd := by rw [I.eq]
  obtain hwr : u.wr = s₀.wr := by rw [I.eq]
  obtain W : KeyWordEnv T S K L i u := by
    refine ⟨hi, E.L0, E.L64, fun c hc => ?_, (I.gpr _ (by decide)).trans E.x0, (I.gpr _ (by decide)).trans E.x1,
      I.x10, I.x9, I.x12, ?_, ?_⟩
    · rw [hrd, hwr]; exact E.key c hc
    · rw [hrd, hwr]; exact inRegions_off E.rdT (by omega_arith)
    · rw [hwr]; exact inRegions_off E.wrS (by omega_arith)
  refine WP.mono (keyWord_run W) fun u' ⟨m', x10', x9', x12', x11', g', e'⟩ => ?_
  obtain dTS : (⟨T, 4168⟩ : Region).Disjoint ⟨S + BitVec.ofNat 64 4096, 4 * i⟩ :=
    E.sep.sub_right (Offset.sub_base S (d := 4096) (n := 4 * i) (k := 4168) (by omega_arith))
  obtain hT : u.mem.readW (T + BitVec.ofNat 64 (4096 + 4 * i)) 32 =
      s₀.mem.readW (T + BitVec.ofNat 64 (4096 + 4 * i)) 32 :=
    I.frame.readW (r := ⟨T, 4168⟩) (Offset.contains_base T (by omega_arith) (by omega_arith))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dTS) (by decide)
  obtain hB : bytesAt u.mem K L = bytesAt s₀.mem K L :=
    bytesAt_frame I.frame fun c hc r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact E.keyS c hc (Offset.sub_base S (d := 4096) (n := 4 * i) (k := 4168) (by omega_arith) _ hcon)
  refine ⟨by omega_arith, x10', ?_, ?_, ?_, fun j hj => ?_, ?_, fun r hr => (g' r hr).trans (I.gpr r hr), ?_⟩
  · rw [x9', I.x9, BitVec.add_assoc]
    exact congrArg (T + ·) (by apply BitVec.eq_of_toNat_eq; simp; omega_arith)
  · rw [x12', I.x12, BitVec.add_assoc]
    exact congrArg (S + ·) (by apply BitVec.eq_of_toNat_eq; simp; omega_arith)
  · rw [x11', I.x11]
    apply BitVec.eq_of_toNat_eq; simp; omega_arith
  · rw [m', hT, hB]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep S (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
      exact I.done j hj
    · exact Mem.readW_writeW_self32 _ _ _
  · rw [m']
    refine Frame.writeW (Frame.sub I.frame fun r hr => ⟨⟨S + BitVec.ofNat 64 4096, 4 * (i + 1)⟩,
      List.mem_singleton_self _, ?_⟩) (List.mem_singleton_self _) _
      (Offset.contains S (by omega_arith) (by omega_arith) (by omega_arith))
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub S (by omega_arith) (by omega_arith)
  · rw [e']; rw [I.eq]

theorem keyP_run {T S K : Addr} {L : Nat} {s₀ : State} (E : KeyPEnv T S K L s₀) :
    WP isa keyP s₀ (KeyPInv T S K L s₀ 18) := by
  rw [keyP]
  apply WP.seq
  let s₁ := (s₀.write .x .x10 ((0 : BitVec 16).setWidth 64 <<< (16 * 0))).write .x .x11
    ((18 : BitVec 16).setWidth 64 <<< (16 * 0))
  refine WP.of_runBlock ⟨s₁, rfl, ?_⟩
  obtain I₀ : KeyPInv T S K L s₀ 0 s₁ := by
    refine ⟨by omega_arith, by simp [s₁, gpr_write], ?_, ?_, by simp [s₁, gpr_write], fun j hj => by omega_arith,
      Frame.refl _ _, fun r ⟨_, _, h10, h11, _⟩ => by simp [s₁, gpr_write, h10, h11], rfl⟩
    · simp [s₁, gpr_write, E.x9]
    · simp [s₁, gpr_write, E.x12]
  refine WP.loop (M := isa) (fun m u => ∃ i, i < 18 ∧ m = 18 - i ∧ KeyPInv T S K L s₀ i u)
    ?_ 18 s₁ ⟨0, by omega_arith, rfl, I₀⟩
  intro m u ⟨i, hi, hm, I⟩
  refine WP.mono (keyP_step E hi I) fun u' I' => ?_
  obtain flag := eval_nonzero u' .x11 I'.x11 (by omega_arith)
  by_cases h : i + 1 = 18
  · left; exact ⟨by rw [flag]; simp; omega_arith, h ▸ I'⟩
  · right; exact ⟨by rw [flag]; simp; omega_arith, 18 - (i + 1), by omega_arith, i + 1, by omega_arith, rfl, I'⟩

end VG.Proof.Blowfish.AArch64

end

end

/-! ### `Blowfish.AArch64.KeyLoop`, which only this module used -/

section

/-!
# Key expansion: the 521 encryptions

Each encryption runs the batch code's sixteen rounds on lane 0 of `A` and
`B`, under the schedule as written so far, and its output replaces the
next two entries (`replace`): the P-array's, as words, then the S-boxes',
a byte per plane. `encryptions_run`: after the 521, the schedule is
`expandKey`'s.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64
open VG.Spec.Blowfish VG.Proof.Blowfish
open VG.AArch64.Tbl (VOnly)

theorem exec_strb {s : State} {t n : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 1) :
    exec (.strb t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 1 ((s.read .w t).setWidth 8) } := by
  simp only [exec, addr, Nat.mod_one, show off < 4096 * 1 by omega_arith, and_self, ite_true, Option.bind_some,
    State.store, h]

theorem read_write_w (s : State) (r : Reg) (v : BitVec 32) : (s.write .w r v).read .w r = v := by
  simp [State.read, gpr_write, Size.bits]

/-- The bytes of the word in `w` at offsets `e`, `256 + e`, `512 + e` and
`768 + e` of `x14`. -/
theorem storeEntry_run {t : State} {w : Reg} (hw : w ≠ .x13) {e : Nat} (he : e < 2)
    (hW : ∀ b < 4, InRegions t.wr (t.gpr .x14 + BitVec.ofNat 64 (256 * b + e)) 1) :
    ∃ t', runBlock isa (storeEntry w e) t = some t' ∧
      t'.mem = (((t.mem.write (t.gpr .x14 + BitVec.ofNat 64 (256 * 0 + e)) 1
          ((t.read .w w).extractLsb' 0 8)).write
        (t.gpr .x14 + BitVec.ofNat 64 (256 * 1 + e)) 1 ((t.read .w w).extractLsb' 8 8)).write
        (t.gpr .x14 + BitVec.ofNat 64 (256 * 2 + e)) 1 ((t.read .w w).extractLsb' 16 8)).write
        (t.gpr .x14 + BitVec.ofNat 64 (256 * 3 + e)) 1 ((t.read .w w).extractLsb' 24 8) ∧
      (∀ r, r ≠ .x13 → t'.gpr r = t.gpr r) ∧ t' = { t with gpr := t'.gpr, mem := t'.mem } := by
  let W := t.read .w w
  let wb (u : State) (o : Nat) (v : BitVec 8) : State :=
    { u with mem := u.mem.write (u.gpr .x14 + BitVec.ofNat 64 o) 1 v }
  let t₁ := wb t e ((t.read .w w).setWidth 8)
  let t₂ := t₁.write .w .x13 (t₁.read .w w >>> 8)
  let t₃ := wb t₂ (256 + e) ((t₂.read .w .x13).setWidth 8)
  let t₄ := t₃.write .w .x13 (t₃.read .w w >>> 16)
  let t₅ := wb t₄ (512 + e) ((t₄.read .w .x13).setWidth 8)
  let t₆ := t₅.write .w .x13 (t₅.read .w w >>> 24)
  let t₇ := wb t₆ (768 + e) ((t₆.read .w .x13).setWidth 8)
  obtain g₁₄ : ∀ (u : State) (v : BitVec 32), (u.write .w .x13 v).gpr .x14 = u.gpr .x14 := fun u v =>
    gpr_write_of_ne u .w v (by decide)
  obtain rW : ∀ (u : State) (v : BitVec 32), (u.write .w .x13 v).read .w w = u.read .w w := fun u v => by
    simp only [State.read, gpr_write_of_ne u .w v hw]
  refine ⟨t₇, ?_, ?_, fun r hr => ?_, rfl⟩
  · rw [storeEntry, runBlock_cons, exec_strb (by omega_arith) (by simpa using hW 0 (by decide)), runStep_some,
      runBlock_cons, exec_lsr_w (by decide), runStep_some, runBlock_cons,
      exec_strb (by omega_arith) (by exact hW 1 (by decide)), runStep_some,
      runBlock_cons, exec_lsr_w (by decide), runStep_some, runBlock_cons,
      exec_strb (by omega_arith) (by exact hW 2 (by decide)), runStep_some,
      runBlock_cons, exec_lsr_w (by decide), runStep_some, runBlock_cons,
      exec_strb (by omega_arith) (by exact hW 3 (by decide)), runStep_some, runBlock_nil]
  · have hm : ∀ u o v, (wb u o v).mem = u.mem.write (u.gpr .x14 + BitVec.ofNat 64 o) 1 v := fun _ _ _ => rfl
    obtain hg : ∀ u o v, (wb u o v).gpr = u.gpr := fun _ _ _ => rfl
    obtain hr : ∀ u o v sz r, (wb u o v).read sz r = u.read sz r := fun _ _ _ _ _ => rfl
    obtain h8 : ∀ x : BitVec 32, x.setWidth 8 = x.extractLsb' 0 8 := fun x => by
      apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
    simp only [t₇, t₆, t₅, t₄, t₃, t₂, t₁, hm, hg, hr, mem_write, g₁₄, read_write_w, rW,
      Nat.mul_zero, Nat.zero_add, Nat.mul_one, shr_byte]
    rw [h8]
  · simp only [wb, t₇, t₆, t₅, t₄, t₃, t₂, t₁, gpr_write_of_ne _ .w _ hr]

/-! ## Replacing two entries -/

/-- The stores of `replace`. -/
def storeOut : Prog isa :=
  .ite (.nonzero .x .x9)
    (.block [.str .w .x6 .x12 0, .str .w .x8 .x12 4, .addImm .x .x12 .x12 8, .subImm .x .x9 .x9 1])
    (.seq (.block (storeEntry .x6 0 ++ storeEntry .x8 1 ++
        [.addImm .x .x14 .x14 2, .subImm .x .x10 .x10 2]))
      (.ite (.zero .x .x10) (.block [.addImm .x .x14 .x14 768, .movz .x .x10 256 0]) (.block [])))

theorem replace_eq : replace =
    .seq (.block [.umov .w .x6 (bReg 0) 0, .umov .w .x8 (aReg 0) 0])
      (.seq storeOut (.block [.vop (.mov .v0 (aReg 0)), .vop (.mov (aReg 0) (bReg 0)),
        .vop (.mov (bReg 0) .v0), .subImm .x .x15 .x15 1])) := rfl

/-- Where the `j`-th output goes. -/
structure StoreIn (S : Addr) (j : Nat) (t : State) : Prop where
  lt : j < 521
  wr : ∀ off n, off + n ≤ 4168 → InRegions t.wr (S + BitVec.ofNat 64 off) n
  x9 : t.gpr .x9 = BitVec.ofNat 64 (9 - j)
  x12 : t.gpr .x12 = S + BitVec.ofNat 64 (4096 + 8 * min j 9)
  x14 : t.gpr .x14 = S + BitVec.ofNat 64 (1024 * (sDone j / 256) + sDone j % 256)
  x10 : t.gpr .x10 = BitVec.ofNat 64 (256 - sDone j % 256)

/-- The registers `storeOut` writes. -/
abbrev StoreRegs (r : Reg) : Prop := r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x14

structure StoreOut (S : Addr) (j : Nat) (t t' : State) : Prop where
  sched : scheduleAt t'.mem S =
    ((scheduleAt t.mem S).set! (2 * j) (t.read .w .x6)).set! (2 * j + 1) (t.read .w .x8)
  x9 : t'.gpr .x9 = BitVec.ofNat 64 (9 - (j + 1))
  x12 : t'.gpr .x12 = S + BitVec.ofNat 64 (4096 + 8 * min (j + 1) 9)
  x14 : t'.gpr .x14 = S + BitVec.ofNat 64 (1024 * (sDone (j + 1) / 256) + sDone (j + 1) % 256)
  x10 : t'.gpr .x10 = BitVec.ofNat 64 (256 - sDone (j + 1) % 256)
  frame : Frame [⟨S, 4168⟩] t.mem t'.mem
  gpr : ∀ r, StoreRegs r → t'.gpr r = t.gpr r
  eq : t' = { t with gpr := t'.gpr, mem := t'.mem }

theorem ofNat_sub_one {a : Nat} (h : 0 < a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 1 = BitVec.ofNat 64 (a - 1) := by
  apply BitVec.eq_of_toNat_eq; simp; omega_arith

theorem ofNat_sub_two {a : Nat} (h : 2 ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 2 = BitVec.ofNat 64 (a - 2) := by
  apply BitVec.eq_of_toNat_eq; simp; omega_arith

/-- The first nine outputs go to the P-array. -/
theorem storeP_run {S : Addr} {j : Nat} {t : State} (I : StoreIn S j t) (hj : j < 9) :
    WP isa storeOut t (StoreOut S j t) := by
  apply WP.ite true (eval_nonzero t .x9 I.x9 (by omega_arith) |>.trans (by simp; omega_arith)) _ (fun h => nomatch h)
  intro _
  obtain a₀ : t.gpr .x12 + BitVec.ofNat 64 0 = S + BitVec.ofNat 64 (4096 + 4 * (2 * j)) := by
    rw [I.x12, Offset.add_add]; congr 2; omega_arith
  obtain a₄ : t.gpr .x12 + BitVec.ofNat 64 4 = S + BitVec.ofNat 64 (4096 + 4 * (2 * j + 1)) := by
    rw [I.x12, Offset.add_add]; congr 2; omega_arith
  let t₁ : State := { t with mem := t.mem.writeW (t.gpr .x12 + BitVec.ofNat 64 0) ((t.gpr .x6).setWidth 32) }
  let t₂ : State := { t₁ with mem := t₁.mem.writeW (t₁.gpr .x12 + BitVec.ofNat 64 4) ((t₁.gpr .x8).setWidth 32) }
  let t₃ := t₂.write .x .x12 (t₂.read .x .x12 + BitVec.ofNat _ 8)
  let t₄ := t₃.write .x .x9 (t₃.read .x .x9 - BitVec.ofNat _ 1)
  obtain m₄ : t₄.mem = (t.mem.writeW (S + BitVec.ofNat 64 (4096 + 4 * (2 * j))) (t.read .w .x6)).writeW
      (S + BitVec.ofNat 64 (4096 + 4 * (2 * j + 1))) (t.read .w .x8) := by
    show (t.mem.writeW (t.gpr .x12 + BitVec.ofNat 64 0) _).writeW (t.gpr .x12 + BitVec.ofNat 64 4) _ = _
    rw [a₀, a₄]; rfl
  refine WP.of_runBlock ⟨t₄, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl⟩⟩
  · rw [runBlock_cons, exec_str_w (by decide) (by rw [a₀]; exact I.wr _ _ (by omega_arith)), runStep_some,
      runBlock_cons, exec_str_w (by decide) (by show InRegions t.wr (t.gpr .x12 + _) 4; rw [a₄]; exact I.wr _ _ (by omega_arith)),
      runStep_some,
      runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_subImm_x (by decide),
      runStep_some, runBlock_nil]
  · rw [m₄, scheduleAt_writeW_P _ _ (by omega_arith), scheduleAt_writeW_P _ _ (by omega_arith),
      set!_eq_set _ (by omega_arith), set!_eq_set _ (by omega_arith)]
  · simp only [t₄, t₃, gpr_write_self, State.read, BitVec.setWidth_eq,
      gpr_write_of_ne _ .x _ (by decide : Reg.x9 ≠ .x12)]
    show t.gpr .x9 - _ = _
    rw [I.x9, ofNat_sub_one (by omega_arith) (by omega_arith)]; congr 1
  · simp only [t₄, t₃, gpr_write_of_ne _ .x _ (by decide : Reg.x12 ≠ .x9), gpr_write_self, State.read,
      BitVec.setWidth_eq]
    show t.gpr .x12 + _ = _
    rw [I.x12, Offset.add_add]; congr 2; omega_arith
  · simp only [t₄, t₃, gpr_write_of_ne _ .x _ (by decide : Reg.x14 ≠ .x9),
      gpr_write_of_ne _ .x _ (by decide : Reg.x14 ≠ .x12)]
    show t.gpr .x14 = _
    rw [I.x14, sDone, sDone, show j + 1 - 9 = j - 9 by omega_arith]
  · simp only [t₄, t₃, gpr_write_of_ne _ .x _ (by decide : Reg.x10 ≠ .x9),
      gpr_write_of_ne _ .x _ (by decide : Reg.x10 ≠ .x12)]
    show t.gpr .x10 = _
    rw [I.x10, sDone, sDone, show j + 1 - 9 = j - 9 by omega_arith]
  · rw [m₄]
    refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_ |>.writeW (List.mem_singleton_self _) _ ?_
    · exact Offset.contains_base S (by simp only [Size.bits]; omega_arith) (by omega_arith)
    · exact Offset.contains_base S (by simp only [Size.bits]; omega_arith) (by omega_arith)
  · simp only [t₄, t₃, gpr_write_of_ne _ .x _ hr.1, gpr_write_of_ne _ .x _ hr.2.2.1]
    rfl

/-- The other 512 outputs go to the S-boxes, a byte per plane. -/
theorem storeS_run {S : Addr} {j : Nat} {t : State} (I : StoreIn S j t) (hj : 9 ≤ j) :
    WP isa storeOut t (StoreOut S j t) := by
  have hlt := I.lt
  apply WP.ite false (eval_nonzero t .x9 I.x9 (by omega_arith) |>.trans (by simp; omega_arith)) (fun h => nomatch h)
  intro _
  obtain ad : ∀ (u : State), u.gpr .x14 = t.gpr .x14 → ∀ k < 2, ∀ b < 4,
      u.gpr .x14 + BitVec.ofNat 64 (256 * b + k) = S + BitVec.ofNat 64 (entryOff (2 * j + k) b) :=
    fun u hu k hk b hb => by rw [hu, I.x14, Offset.add_add, entryOff_sbox hj hlt k hk]
  obtain inS : ∀ k < 2, ∀ b < 4, entryOff (2 * j + k) b + 1 ≤ 4168 := fun k hk b hb => by
    have := entryOff_lt (i := 2 * j + k) (b := b) (by omega_arith) hb; omega_arith
  obtain W : ∀ (u : State), u.gpr .x14 = t.gpr .x14 → u.wr = t.wr → ∀ k < 2, ∀ b < 4,
      InRegions u.wr (u.gpr .x14 + BitVec.ofNat 64 (256 * b + k)) 1 := fun u hu hw k hk b hb => by
    rw [ad u hu k hk b hb, hw]; exact I.wr _ _ (inS k hk b hb)
  obtain ⟨t₁, r₁, m₁, g₁, e₁⟩ := storeEntry_run (t := t) (w := .x6) (by decide) (e := 0) (by decide)
    (W t rfl rfl 0 (by decide))
  obtain h14₁ : t₁.gpr .x14 = t.gpr .x14 := g₁ _ (by decide)
  obtain wr₁ : t₁.wr = t.wr := by rw [e₁]
  obtain ⟨t₂, r₂, m₂, g₂, e₂⟩ := storeEntry_run (t := t₁) (w := .x8) (by decide) (e := 1) (by decide)
    (W t₁ h14₁ wr₁ 1 (by decide))
  obtain h14₂ : t₂.gpr .x14 = t.gpr .x14 := (g₂ _ (by decide)).trans h14₁
  obtain r8 : t₁.read .w .x8 = t.read .w .x8 := by simp only [State.read, g₁ _ (by decide : Reg.x8 ≠ .x13)]
  -- the memory
  obtain mem₂ : t₂.mem = (((((((t.mem.write (S + BitVec.ofNat 64 (entryOff (2 * j) 0)) 1
        ((t.read .w .x6).extractLsb' 0 8)).write
      (S + BitVec.ofNat 64 (entryOff (2 * j) 1)) 1 ((t.read .w .x6).extractLsb' 8 8)).write
      (S + BitVec.ofNat 64 (entryOff (2 * j) 2)) 1 ((t.read .w .x6).extractLsb' 16 8)).write
      (S + BitVec.ofNat 64 (entryOff (2 * j) 3)) 1 ((t.read .w .x6).extractLsb' 24 8)).write
      (S + BitVec.ofNat 64 (entryOff (2 * j + 1) 0)) 1 ((t.read .w .x8).extractLsb' 0 8)).write
      (S + BitVec.ofNat 64 (entryOff (2 * j + 1) 1)) 1 ((t.read .w .x8).extractLsb' 8 8)).write
      (S + BitVec.ofNat 64 (entryOff (2 * j + 1) 2)) 1 ((t.read .w .x8).extractLsb' 16 8)).write
      (S + BitVec.ofNat 64 (entryOff (2 * j + 1) 3)) 1 ((t.read .w .x8).extractLsb' 24 8) := by
    rw [m₂, m₁, r8, ad t₁ h14₁ 1 (by decide) 0 (by decide), ad t₁ h14₁ 1 (by decide) 1 (by decide),
      ad t₁ h14₁ 1 (by decide) 2 (by decide), ad t₁ h14₁ 1 (by decide) 3 (by decide),
      ad t rfl 0 (by decide) 0 (by decide), ad t rfl 0 (by decide) 1 (by decide),
      ad t rfl 0 (by decide) 2 (by decide), ad t rfl 0 (by decide) 3 (by decide), Nat.add_zero]
  obtain sched₂ : scheduleAt t₂.mem S =
      ((scheduleAt t.mem S).set! (2 * j) (t.read .w .x6)).set! (2 * j + 1) (t.read .w .x8) := by
    rw [mem₂, scheduleAt_write_bytes _ _ (by omega_arith), scheduleAt_write_bytes _ _ (by omega_arith),
      set!_eq_set _ (by omega_arith), set!_eq_set _ (by omega_arith)]
  obtain fr₂ : Frame [⟨S, 4168⟩] t.mem t₂.mem := by
    obtain c : ∀ k < 2, ∀ b < 4, (⟨S, 4168⟩ : Region).Contains (S + BitVec.ofNat 64 (entryOff (2 * j + k) b)) 1 :=
      fun k hk b hb => Offset.contains_base S (inS k hk b hb) (by have := inS k hk b hb; omega_arith)
    obtain mm := List.mem_singleton_self (⟨S, 4168⟩ : Region)
    rw [mem₂]
    exact ((((((((Frame.refl _ _).write mm _ (c 0 (by decide) 0 (by decide))).write mm _
      (c 0 (by decide) 1 (by decide))).write mm _ (c 0 (by decide) 2 (by decide))).write mm _
      (c 0 (by decide) 3 (by decide))).write mm _ (c 1 (by decide) 0 (by decide))).write mm _
      (c 1 (by decide) 1 (by decide))).write mm _ (c 1 (by decide) 2 (by decide))).write mm _
      (c 1 (by decide) 3 (by decide))
  -- the registers
  let t₃ := t₂.write .x .x14 (t₂.read .x .x14 + BitVec.ofNat _ 2)
  let t₄ := t₃.write .x .x10 (t₃.read .x .x10 - BitVec.ofNat _ 2)
  obtain hg₂ : ∀ r, r ≠ .x13 → t₂.gpr r = t.gpr r := fun r hr => (g₂ r hr).trans (g₁ r hr)
  obtain e₂' : t₂ = { t with gpr := t₂.gpr, mem := t₂.mem } := by rw [e₂, e₁]
  obtain hr10 : sDone j % 256 ≤ 254 := by unfold sDone; omega_arith
  obtain x10₄ : t₄.gpr .x10 = BitVec.ofNat 64 (256 - sDone j % 256 - 2) := by
    simp only [t₄, t₃, gpr_write_self, State.read, BitVec.setWidth_eq,
      gpr_write_of_ne _ .x _ (by decide : Reg.x10 ≠ .x14)]
    rw [hg₂ _ (by decide), I.x10, ofNat_sub_two (by omega_arith) (by omega_arith)]
  obtain x14₄ : t₄.gpr .x14 = S + BitVec.ofNat 64 (1024 * (sDone j / 256) + sDone j % 256 + 2) := by
    simp only [t₄, t₃, gpr_write_of_ne _ .x _ (by decide : Reg.x14 ≠ .x10), gpr_write_self, State.read,
      BitVec.setWidth_eq]
    rw [h14₂, I.x14, Offset.add_add]
  obtain g₄' : ∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x10 → t₄.gpr r = t.gpr r := fun r h13 h14 h10 => by
    simp only [t₄, t₃, gpr_write_of_ne _ .x _ h10, gpr_write_of_ne _ .x _ h14]
    exact hg₂ r h13
  obtain g₄ : ∀ r, StoreRegs r → t₄.gpr r = t.gpr r := fun r hr => g₄' r hr.2.2.2.1 hr.2.2.2.2 hr.2.1
  obtain e₄ : t₄ = { t with gpr := t₄.gpr, mem := t₄.mem } := by
    simp only [t₄, t₃, State.write]; rw [e₂']
  obtain x9' : t.gpr .x9 = BitVec.ofNat 64 (9 - (j + 1)) := by rw [I.x9, show 9 - j = 9 - (j + 1) by omega_arith]
  obtain x12' : t.gpr .x12 = S + BitVec.ofNat 64 (4096 + 8 * min (j + 1) 9) := by
    rw [I.x12, show min j 9 = min (j + 1) 9 by omega_arith]
  apply WP.seq
  refine WP.of_runBlock ⟨t₄, ?_, ?_⟩
  · rw [List.append_assoc]
    refine cat_run r₁ (cat_run r₂ ?_)
    rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_subImm_x (by decide),
      runStep_some, runBlock_nil]
  apply WP.ite _ (eval_zero t₄ .x10 x10₄ (by omega_arith))
  · intro hz
    obtain h254 : sDone j % 256 = 254 := by simp at hz; omega_arith
    let t₅ := t₄.write .x .x14 (t₄.read .x .x14 + BitVec.ofNat _ 768)
    let t₆ := t₅.write .x .x10 ((256 : BitVec 16).setWidth 64 <<< (16 * 0))
    refine WP.of_runBlock ⟨t₆, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_⟩⟩
    · rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons]; rfl
    · exact sched₂
    · simp only [t₆, t₅, gpr_write_of_ne _ .x _ (by decide : Reg.x9 ≠ .x10),
        gpr_write_of_ne _ .x _ (by decide : Reg.x9 ≠ .x14)]
      rw [g₄' _ (by decide) (by decide) (by decide)]; exact x9'
    · simp only [t₆, t₅, gpr_write_of_ne _ .x _ (by decide : Reg.x12 ≠ .x10),
        gpr_write_of_ne _ .x _ (by decide : Reg.x12 ≠ .x14)]
      rw [g₄' _ (by decide) (by decide) (by decide)]; exact x12'
    · simp only [t₆, t₅, gpr_write_of_ne _ .x _ (by decide : Reg.x14 ≠ .x10), gpr_write_self, State.read,
        BitVec.setWidth_eq]
      rw [x14₄, Offset.add_add]; congr 2; unfold sDone at h254 ⊢; omega_arith
    · simp only [t₆, gpr_write_self]
      rw [show sDone (j + 1) % 256 = 0 by unfold sDone at h254 ⊢; omega_arith]; rfl
    · exact fr₂
    · simp only [t₆, t₅, gpr_write_of_ne _ .x _ hr.2.1, gpr_write_of_ne _ .x _ hr.2.2.2.2]
      exact g₄ r hr
    · simp only [t₆, t₅, State.write]; rw [e₄]
  · intro hz
    obtain h254 : sDone j % 256 ≠ 254 := by simp at hz; omega_arith
    refine WP.block_nil ⟨sched₂, ?_, ?_, ?_, ?_, fr₂, g₄, e₄⟩
    · rw [g₄' _ (by decide) (by decide) (by decide)]; exact x9'
    · rw [g₄' _ (by decide) (by decide) (by decide)]; exact x12'
    · rw [x14₄]; congr 2; unfold sDone at h254 ⊢; omega_arith
    · rw [x10₄]; congr 1; unfold sDone at h254 ⊢; omega_arith

/-! ## The loop -/

/-- The general-purpose registers the encryptions write. -/
def encGprs : List Reg := [.x5, .x6, .x7, .x8, .x9, .x10, .x12, .x13, .x14, .x15]

/-- What the loop needs of the state it starts in: the schedule at `x2`, writable. -/
structure EncEnv (S : Addr) (s₀ : State) : Prop where
  x2 : s₀.gpr .x2 = S
  wrS : ∀ off n, off + n ≤ 4168 → InRegions s₀.wr (S + BitVec.ofNat 64 off) n
  consts : Consts s₀

/-- After `j` encryptions. -/
structure EncInv (key : List Byte) (S : Addr) (s₀ : State) (j : Nat) (u : State) : Prop where
  le : j ≤ 521
  sched : scheduleAt u.mem S = (ksIter key j).1
  xl : vword (u.v .v4) 0 = (ksIter key j).2.1
  xr : vword (u.v .v8) 0 = (ksIter key j).2.2
  x15 : u.gpr .x15 = BitVec.ofNat 64 (521 - j)
  x9 : u.gpr .x9 = BitVec.ofNat 64 (9 - j)
  x12 : u.gpr .x12 = S + BitVec.ofNat 64 (4096 + 8 * min j 9)
  x14 : u.gpr .x14 = S + BitVec.ofNat 64 (1024 * (sDone j / 256) + sDone j % 256)
  x10 : u.gpr .x10 = BitVec.ofNat 64 (256 - sDone j % 256)
  frame : Frame [⟨S, 4168⟩] s₀.mem u.mem
  gpr : ∀ r, r ∉ encGprs → u.gpr r = s₀.gpr r
  v : ∀ r, r ∉ roundRegs → u.v r = s₀.v r
  eq : u = { s₀ with gpr := u.gpr, v := u.v, mem := u.mem }

theorem enc_step {key : List Byte} {S : Addr} {s₀ : State} (E : EncEnv S s₀) {j : Nat} (hj : j < 521)
    {u : State} (I : EncInv key S s₀ j u) :
    WP isa (.seq (cipher .x2 true) replace) u (EncInv key S s₀ (j + 1)) := by
  obtain hrd : u.rd = s₀.rd := by rw [I.eq]
  obtain hwr : u.wr = s₀.wr := by rw [I.eq]
  obtain x2 : u.gpr .x2 = S := (I.gpr _ (by decide)).trans E.x2
  obtain hS : SchedIn u .x2 := fun off n h => by
    rw [x2, hwr]
    obtain ⟨r, hr, hc⟩ := E.wrS off n h
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain hc : Consts u := ⟨fun e he => by rw [I.v _ c_notin.1]; exact E.consts.1 e he,
    fun e he => by rw [I.v _ c_notin.2]; exact E.consts.2 e he⟩
  apply WP.seq
  refine WP.mono (cipher_run hS hc (by decide) true) fun u₁ ⟨hl, o₁⟩ => ?_
  obtain ⟨hlb, hla⟩ := hl 0 (by decide)
  let K := (ksIter key j).1
  let out := encryptWords K (ksIter key j).2.1 (ksIter key j).2.2
  obtain o8 : vword (u₁.v .v8) 0 = out.1 := by
    have : vword (u₁.v .v8) 0 = (feistel (scheduleAt u.mem (u.gpr .x2)) (order true)
      (vword (u.v .v4) 0) (vword (u.v .v8) 0)).1 := hlb
    rw [this, x2, I.sched, order_true, I.xl, I.xr]; rfl
  obtain o4 : vword (u₁.v .v4) 0 = out.2 := by
    have : vword (u₁.v .v4) 0 = (feistel (scheduleAt u.mem (u.gpr .x2)) (order true)
      (vword (u.v .v4) 0) (vword (u.v .v8) 0)).2 := hla
    rw [this, x2, I.sched, order_true, I.xl, I.xr]; rfl
  rw [replace_eq]
  apply WP.seq
  let u₁' := u₁.write .w .x6 (vword (u₁.v (bReg 0)) 0)
  let u₂ := u₁'.write .w .x8 (vword (u₁'.v (aReg 0)) 0)
  refine WP.of_runBlock ⟨u₂, rfl, ?_⟩
  obtain g₂ : ∀ r, r ∉ encGprs → u₂.gpr r = u.gpr r := fun r hr => by
    simp only [encGprs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [u₂, u₁', gpr_write_of_ne _ .w _ hr.2.2.2.1, gpr_write_of_ne _ .w _ hr.2.1]
    exact o₁.g r (by simp [hr.1, hr.2.1, hr.2.2.1])
  obtain g₂' : ∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → u₂.gpr r = u.gpr r := fun r h5 h6 h7 h8 => by
    simp only [u₂, u₁', gpr_write_of_ne _ .w _ h8, gpr_write_of_ne _ .w _ h6]
    exact o₁.g r (by simp [h5, h6, h7])
  obtain wr₂ : u₂.wr = s₀.wr := by rw [show u₂.wr = u₁.wr from rfl, o₁.wr, hwr]
  have mem₂ : u₂.mem = u.mem := o₁.mem
  obtain SI : StoreIn S j u₂ := by
    refine ⟨hj, fun off n h => by rw [wr₂]; exact E.wrS off n h, ?_, ?_, ?_, ?_⟩
    · rw [g₂' _ (by decide) (by decide) (by decide) (by decide)]; exact I.x9
    · rw [g₂' _ (by decide) (by decide) (by decide) (by decide)]; exact I.x12
    · rw [g₂' _ (by decide) (by decide) (by decide) (by decide)]; exact I.x14
    · rw [g₂' _ (by decide) (by decide) (by decide) (by decide)]; exact I.x10
  obtain st : WP isa storeOut u₂ (StoreOut S j u₂) :=
    if h : j < 9 then storeP_run SI h else storeS_run SI (by omega_arith)
  apply WP.seq
  refine WP.mono st fun u₃ O => ?_
  obtain v₃ : u₃.v = u₁.v := by rw [O.eq]; rfl
  let a := u₃.setV .v0 (u₃.v (aReg 0))
  let b := a.setV (aReg 0) (a.v (bReg 0))
  let c := b.setV (bReg 0) (b.v .v0)
  let u₄ := c.write .x .x15 (c.read .x .x15 - BitVec.ofNat _ 1)
  obtain v₄ : ∀ r, r ≠ .v0 → r ≠ .v4 → r ≠ .v8 → u₄.v r = u₁.v r := fun r h0 h4 h8 => by
    simp only [u₄, c, b, a, v_write, v_setV_of_ne _ _ h0, v_setV_of_ne _ _ h4, v_setV_of_ne _ _ h8,
      show bReg 0 = .v8 from rfl, show aReg 0 = .v4 from rfl, v₃]
  obtain g₄ : ∀ r, r ≠ .x15 → u₄.gpr r = u₃.gpr r := fun r hr => by
    simp only [u₄, gpr_write_of_ne _ .x _ hr]; rfl
  refine WP.of_runBlock ⟨u₄, ?_, ⟨by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_,
    fun r hr => ?_, ?_⟩⟩
  · rw [runBlock_cons, exec_vmov, runStep_some, runBlock_cons, exec_vmov, runStep_some, runBlock_cons,
      exec_vmov, runStep_some, runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil]
  · have r6 : u₂.read .w .x6 = out.1 := by
      have : u₂.gpr .x6 = u₁'.gpr .x6 := gpr_write_of_ne _ .w _ (by decide)
      show (u₂.gpr .x6).setWidth 32 = _
      rw [this]; exact (read_write_w u₁ .x6 _).trans o8
    obtain r8 : u₂.read .w .x8 = out.2 := by rw [read_write_w]; exact o4
    rw [show u₄.mem = u₃.mem from rfl, O.sched, mem₂, I.sched, r6, r8, ksIter_succ]; rfl
  · show vword (u₃.v .v8) 0 = _
    rw [v₃, o8, ksIter_succ]; rfl
  · show vword (u₃.v .v4) 0 = _
    rw [v₃, o4, ksIter_succ]; rfl
  · simp only [u₄, gpr_write_self, State.read, BitVec.setWidth_eq]
    show u₃.gpr .x15 - _ = _
    rw [O.gpr _ (by decide), g₂' _ (by decide) (by decide) (by decide) (by decide), I.x15,
      ofNat_sub_one (by omega_arith) (by omega_arith)]
    congr 1
  · rw [g₄ _ (by decide)]; exact O.x9
  · rw [g₄ _ (by decide)]; exact O.x12
  · rw [g₄ _ (by decide)]; exact O.x14
  · rw [g₄ _ (by decide)]; exact O.x10
  · rw [show u₄.mem = u₃.mem from rfl]
    exact I.frame.trans (mem₂ ▸ O.frame)
  · simp only [encGprs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₄ _ hr.2.2.2.2.2.2.2.2.2, O.gpr _ ⟨hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1⟩, g₂ r (by simp [encGprs]; omega), I.gpr r (by simp [encGprs]; omega)]
  · have h0 : r ≠ .v0 := fun h => hr (h ▸ by decide)
    obtain h4 : r ≠ .v4 := fun h => hr (h ▸ by decide)
    obtain h8 : r ≠ .v8 := fun h => hr (h ▸ by decide)
    rw [v₄ r h0 h4 h8, o₁.v r hr, I.v r hr]
  · rw [show u₄ = { u₃ with gpr := u₄.gpr, v := u₄.v } from rfl, O.eq,
      show u₂ = { u₁ with gpr := u₂.gpr } from rfl, o₁.eq, I.eq]

theorem exec_movi0 (s : State) (d : VReg) : exec (.vop (.movi0 d)) s = some (s.setV d 0) := rfl

theorem exec_movz_x0 (s : State) (d : Reg) (imm : BitVec 16) :
    exec (.movz .x d imm 0) s = some (s.write .x d (imm.setWidth 64 <<< (16 * 0))) := rfl

/-- The 521 encryptions, from the keyed schedule at `x2`. -/
theorem encryptions_run {key : List Byte} {S : Addr} {s₀ : State} (E : EncEnv S s₀)
    (hK : scheduleAt s₀.mem S = keyed key) :
    WP isa encryptions s₀ (EncInv key S s₀ 521) := by
  rw [encryptions]
  apply WP.seq
  let s₁ := ((((((((s₀.setV .v4 0).setV .v8 0).setV .v5 0).setV .v9 0).setV .v6 0).setV .v10 0).setV
    .v7 0).setV .v11 0)
  let s₂ := s₁.write .x .x9 ((9 : BitVec 16).setWidth 64 <<< (16 * 0))
  let s₃ := s₂.write .x .x12 (s₂.read .x .x2 + BitVec.ofNat _ 2048)
  let s₄ := s₃.write .x .x12 (s₃.read .x .x12 + BitVec.ofNat _ 2048)
  let s₅ := s₄.write .x .x14 (s₄.read .x .x2 + BitVec.ofNat _ 0)
  let s₆ := s₅.write .x .x10 ((256 : BitVec 16).setWidth 64 <<< (16 * 0))
  let s₇ := s₆.write .x .x15 ((521 : BitVec 16).setWidth 64 <<< (16 * 0))
  refine WP.of_runBlock ⟨s₇, ?_, ?_⟩
  · rw [show (List.range 4).flatMap (fun k => [Instr.vop (.movi0 (aReg k)), .vop (.movi0 (bReg k))]) =
        [.vop (.movi0 .v4), .vop (.movi0 .v8), .vop (.movi0 .v5), .vop (.movi0 .v9), .vop (.movi0 .v6),
          .vop (.movi0 .v10), .vop (.movi0 .v7), .vop (.movi0 .v11)] from rfl]
    simp only [List.cons_append, List.nil_append]
    rw [runBlock_cons, exec_movi0, runStep_some, runBlock_cons, exec_movi0, runStep_some,
      runBlock_cons, exec_movi0, runStep_some, runBlock_cons, exec_movi0, runStep_some,
      runBlock_cons, exec_movi0, runStep_some, runBlock_cons, exec_movi0, runStep_some,
      runBlock_cons, exec_movi0, runStep_some, runBlock_cons, exec_movi0, runStep_some,
      runBlock_cons, exec_movz_x0, runStep_some, runBlock_cons, exec_addImm_x (by decide), runStep_some,
      runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide),
      runStep_some, runBlock_cons, exec_movz_x0, runStep_some, runBlock_cons, exec_movz_x0, runStep_some,
      runBlock_nil]
  refine WP.loop (M := isa) (fun m u => ∃ j, j < 521 ∧ m = 521 - j ∧ EncInv key S s₀ j u) ?_ 521 s₇
    ⟨0, by omega_arith, rfl, ?_⟩
  · intro m u ⟨j, hj, hm, I⟩
    refine WP.mono (enc_step E hj I) fun u' I' => ?_
    obtain flag := eval_nonzero u' .x15 I'.x15 (by omega_arith)
    by_cases h : j + 1 = 521
    · left; exact ⟨by rw [flag]; simp; omega_arith, h ▸ I'⟩
    · right; exact ⟨by rw [flag]; simp; omega_arith, 521 - (j + 1), by omega_arith, j + 1, by omega_arith, rfl, I'⟩
  · have hm : s₇.mem = s₀.mem := by simp only [s₇, s₆, s₅, s₄, s₃, s₂, s₁, mem_write, mem_setV]
    refine ⟨by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, fun r hr => ?_, ?_⟩
    · rw [hm, hK]; rfl
    · simp only [ksIter_zero]
      simp only [s₇, s₆, s₅, s₄, s₃, s₂, s₁, v_write, v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v11),
        v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v7), v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v10),
        v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v6), v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v9),
        v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v5), v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v8),
        v_setV_self]
      rfl
    · simp only [ksIter_zero]
      simp only [s₇, s₆, s₅, s₄, s₃, s₂, s₁, v_write, v_setV_of_ne _ _ (by decide : VReg.v8 ≠ .v11),
        v_setV_of_ne _ _ (by decide : VReg.v8 ≠ .v7), v_setV_of_ne _ _ (by decide : VReg.v8 ≠ .v10),
        v_setV_of_ne _ _ (by decide : VReg.v8 ≠ .v6), v_setV_of_ne _ _ (by decide : VReg.v8 ≠ .v9),
        v_setV_of_ne _ _ (by decide : VReg.v8 ≠ .v5), v_setV_self]
      rfl
    · simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, gpr_write]
    · simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, gpr_write]
    · simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, gpr_setV, gpr_write, State.read, E.x2, Offset.add_add]
    · simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, gpr_setV, gpr_write, State.read, E.x2, sDone]
    · simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, gpr_write, sDone]
    · rw [hm]; exact Frame.refl _ _
    · simp only [encGprs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, gpr_setV, gpr_write, hr]
    · have : r ∉ halfRegs := fun h => hr (by simp [roundRegs, h])
      simp only [halfRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at this
      simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, v_setV, v_write, this]
    · simp only [s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setV, State.write]

end VG.Proof.Blowfish.AArch64

end

end


/-!
# The key expansion function

`q8`–`q15` are saved in the working space, the constants set, the initial
S-boxes copied from the table, the P-array keyed, the 521 encryptions run
and `q8`–`q15` restored (`expandKey_correct`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64
open VG.Spec.Blowfish VG.Proof.Blowfish
open VG.AArch64.Tbl (VOnly)

/-! ## The table -/

/-! ## Keeping `d8`–`d15` -/

/-- The low half of a vector register. -/
abbrev low (t : State) (r : VReg) : BitVec 64 := (t.v r).extractLsb' 0 64

theorem saveLow_eq : saveLow = [.umov .x .x0 .v8 0, .umov .x .x1 .v9 0, .umov .x .x3 .v10 0,
    .umov .x .x4 .v11 0, .umov .x .x11 .v12 0, .umov .x .x16 .v13 0, .umov .x .x17 .v14 0,
    .vop (.mov .v27 .v15)] := rfl

theorem restoreLow_eq : restoreLow = [.vop (.dup .d2 .v8 .x0), .vop (.dup .d2 .v9 .x1),
    .vop (.dup .d2 .v10 .x3), .vop (.dup .d2 .v11 .x4), .vop (.dup .d2 .v12 .x11),
    .vop (.dup .d2 .v13 .x16), .vop (.dup .d2 .v14 .x17), .vop (.mov .v15 .v27)] := rfl

theorem exec_umov_x0 (s : State) (d : Reg) (n : VReg) :
    exec (.umov .x d n 0) s = some (s.write .x d (low s n)) := rfl

theorem exec_dup_d2 (s : State) (d : VReg) (n : Reg) :
    exec (.vop (.dup .d2 d n)) s = some (s.setV d (ofVDwords (s.gpr n) (s.gpr n))) := rfl

theorem low_ofVDwords (x : BitVec 64) : (ofVDwords x x).extractLsb' 0 64 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [ofVDwords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    Nat.zero_add, ite_true]

/-- The registers `saveLow` writes. -/
def keepGprs : List Reg := [.x0, .x1, .x3, .x4, .x11, .x16, .x17]

theorem saveLow_run (t : State) :
    ∃ t', runBlock isa saveLow t = some t' ∧
      t'.gpr .x0 = low t .v8 ∧ t'.gpr .x1 = low t .v9 ∧ t'.gpr .x3 = low t .v10 ∧
      t'.gpr .x4 = low t .v11 ∧ t'.gpr .x11 = low t .v12 ∧ t'.gpr .x16 = low t .v13 ∧
      t'.gpr .x17 = low t .v14 ∧ t'.v .v27 = t.v .v15 ∧
      (∀ r, r ∉ keepGprs → t'.gpr r = t.gpr r) ∧ (∀ r, r ≠ .v27 → t'.v r = t.v r) ∧
      t' = { t with gpr := t'.gpr, v := t'.v } := by
  let t₁ := t.write .x .x0 (low t .v8)
  let t₂ := t₁.write .x .x1 (low t₁ .v9)
  let t₃ := t₂.write .x .x3 (low t₂ .v10)
  let t₄ := t₃.write .x .x4 (low t₃ .v11)
  let t₅ := t₄.write .x .x11 (low t₄ .v12)
  let t₆ := t₅.write .x .x16 (low t₅ .v13)
  let t₇ := t₆.write .x .x17 (low t₆ .v14)
  let t₈ := t₇.setV .v27 (t₇.v .v15)
  refine ⟨t₈, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, fun r hr => ?_, fun r hr => ?_, rfl⟩
  · rw [saveLow_eq, runBlock_cons, exec_umov_x0, runStep_some, runBlock_cons, exec_umov_x0, runStep_some,
      runBlock_cons, exec_umov_x0, runStep_some, runBlock_cons, exec_umov_x0, runStep_some,
      runBlock_cons, exec_umov_x0, runStep_some, runBlock_cons, exec_umov_x0, runStep_some,
      runBlock_cons, exec_umov_x0, runStep_some, runBlock_cons, exec_vmov, runStep_some, runBlock_nil]
  rotate_right 2
  · simp only [keepGprs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, gpr_setV, gpr_write, hr, ↓reduceIte]
  · simp only [t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, v_setV, v_write, hr, ↓reduceIte]
  all_goals simp only [t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, gpr_setV, gpr_write, v_write, low,
    BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte]

theorem restoreLow_run (t : State) :
    ∃ t', runBlock isa restoreLow t = some t' ∧
      low t' .v8 = t.gpr .x0 ∧ low t' .v9 = t.gpr .x1 ∧ low t' .v10 = t.gpr .x3 ∧
      low t' .v11 = t.gpr .x4 ∧ low t' .v12 = t.gpr .x11 ∧ low t' .v13 = t.gpr .x16 ∧
      low t' .v14 = t.gpr .x17 ∧ t'.v .v15 = t.v .v27 ∧ t' = { t with v := t'.v } := by
  let t₁ := t.setV .v8 (ofVDwords (t.gpr .x0) (t.gpr .x0))
  let t₂ := t₁.setV .v9 (ofVDwords (t₁.gpr .x1) (t₁.gpr .x1))
  let t₃ := t₂.setV .v10 (ofVDwords (t₂.gpr .x3) (t₂.gpr .x3))
  let t₄ := t₃.setV .v11 (ofVDwords (t₃.gpr .x4) (t₃.gpr .x4))
  let t₅ := t₄.setV .v12 (ofVDwords (t₄.gpr .x11) (t₄.gpr .x11))
  let t₆ := t₅.setV .v13 (ofVDwords (t₅.gpr .x16) (t₅.gpr .x16))
  let t₇ := t₆.setV .v14 (ofVDwords (t₆.gpr .x17) (t₆.gpr .x17))
  let t₈ := t₇.setV .v15 (t₇.v .v27)
  refine ⟨t₈, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [restoreLow_eq, runBlock_cons, exec_dup_d2, runStep_some, runBlock_cons, exec_dup_d2, runStep_some,
      runBlock_cons, exec_dup_d2, runStep_some, runBlock_cons, exec_dup_d2, runStep_some,
      runBlock_cons, exec_dup_d2, runStep_some, runBlock_cons, exec_dup_d2, runStep_some,
      runBlock_cons, exec_dup_d2, runStep_some, runBlock_cons, exec_vmov, runStep_some, runBlock_nil]
  rotate_right
  · simp only [t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, State.setV]
  all_goals simp only [low, t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, v_setV, gpr_setV, low_ofVDwords, reduceCtorEq,
    ↓reduceIte]

/-! ## The function -/

/-- What the function may assume: the key and the table readable, the
schedule writable, all apart. -/
structure KeyPre (s : State) : Prop where
  valid : validKey (s.gpr .x1).toNat
  rd : s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ⟨s.syms initSym, 4168⟩]
  wr : s.wr = [⟨s.gpr .x2, 4168⟩]
  keySch : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x2, 4168⟩
  fitS : (s.gpr .x2).toNat + 4168 ≤ 2 ^ 64
  held : ∀ i < 521, s.mem.readW (s.syms initSym + BitVec.ofNat 64 (8 * i)) 64 =
    Impl.Blowfish.initWords.getD i 0
  fitT : (s.syms initSym).toNat + 4168 ≤ 2 ^ 64
  tSch : (⟨s.syms initSym, 4168⟩ : Region).Disjoint ⟨s.gpr .x2, 4168⟩

theorem expandKey_eq' : Impl.Blowfish.AArch64.expandKey =
    .seq (.block (constants ++ ([.adrSym .x9 initSym, .addImm .x .x12 .x2 0] : List Instr)))
      (.seq copyPlanes (.seq keyP (.seq (.block saveLow) (.seq encryptions (.block restoreLow))))) := rfl

theorem contains_self (a : Addr) (n : Nat) : (⟨a, n⟩ : Region).Contains a n := by
  simp [Region.Contains]

/-- The schedule becomes the key's expansion, and the low halves of
`v8`–`v15` are kept. -/
theorem expandKey_correct {s : State} (P : KeyPre s) :
    WP isa Impl.Blowfish.AArch64.expandKey s (fun s' =>
      scheduleAt s'.mem (s.gpr .x2) = Spec.Blowfish.expandKey (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) ∧
      ∀ r ∈ preservedV, low s' r = low s r) := by
  let K := s.gpr .x0
  let L := (s.gpr .x1).toNat
  let S := s.gpr .x2
  let T := s.syms initSym
  have hL := P.valid
  unfold validKey at hL
  obtain schW : (⟨S, 4168⟩ : Region) ∈ s.wr := by rw [P.wr]; exact List.mem_cons_self
  obtain keyR : (⟨K, L⟩ : Region) ∈ s.rd ++ s.wr := by rw [P.rd]; exact List.mem_append_left _ List.mem_cons_self
  obtain tabR : (⟨T, 4168⟩ : Region) ∈ s.rd ++ s.wr := by
    rw [P.rd]; exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain kc : ∀ c < L, (⟨K, L⟩ : Region).Contains (K + BitVec.ofNat 64 c) 1 := fun c hc =>
    Offset.contains_base K (by omega_using [hc]) (by omega_using [hc])
  -- the prologue
  obtain ⟨s₂, r₂, c₂, g₂, m₂, rd₂, wr₂, sp₂, o₂⟩ := constants_run s
  let s₃' := s₂.write .x .x9 (s₂.syms initSym)
  let s₃ := s₃'.write .x .x12 (s₃'.read .x .x2 + BitVec.ofNat _ 0)
  obtain r₃ : runBlock isa [.adrSym .x9 initSym, .addImm .x .x12 .x2 0] s₂ = some s₃ := by
    rw [runBlock_cons, exec_adrSym, runStep_some, runBlock_cons, exec_addImm_x (by decide), runStep_some,
      runBlock_nil]
  obtain sy₂ : s₂.syms = s.syms := by rw [o₂.1]
  obtain g₃ : ∀ r, r ≠ .x6 → r ≠ .x9 → r ≠ .x12 → s₃.gpr r = s.gpr r := fun r h6 h9 h12 => by
    simp only [s₃, s₃', gpr_write_of_ne _ .x _ h12, gpr_write_of_ne _ .x _ h9, g₂ r h6]
  have m₃ : s₃.mem = s.mem := m₂
  obtain rd₃ : s₃.rd = s.rd := by rw [show s₃.rd = s₂.rd from rfl, rd₂]
  obtain wr₃ : s₃.wr = s.wr := by rw [show s₃.wr = s₂.wr from rfl, wr₂]
  obtain v₃ : ∀ r, r ≠ c64 → r ≠ c128 → s₃.v r = s.v r := fun r h1 h2 => by
    rw [show s₃.v = s₂.v from rfl, o₂.2 r (by simp [h1, h2])]
  obtain x9₃ : s₃.gpr .x9 = T := by
    simp only [s₃, s₃', gpr_write_of_ne _ .x _ (by decide : Reg.x9 ≠ .x12), gpr_write_self, sy₂]
    rfl
  obtain x12₃ : s₃.gpr .x12 = S := by
    simp only [s₃, s₃', gpr_write_self, State.read, BitVec.setWidth_eq, BitVec.add_zero,
      gpr_write_of_ne _ .x _ (by decide : Reg.x2 ≠ .x9), g₂ _ (by decide : Reg.x2 ≠ .x6)]
    rfl
  rw [expandKey_eq']
  apply WP.seq
  refine WP.of_runBlock ⟨s₃, cat_run r₂ r₃, ?_⟩
  -- the S-boxes
  obtain CE : CopyEnv T S s₃ := by
    refine ⟨by rw [rd₃, wr₃]; exact ⟨_, tabR, contains_self _ _⟩, by rw [wr₃]; exact ⟨_, schW, contains_self _ _⟩,
      P.tSch, P.fitT, P.fitS⟩
  apply WP.seq
  refine WP.mono (copyPlanes_run CE x9₃ x12₃) fun u ⟨u₀, hu₀, C⟩ => ?_
  obtain m₀ : u₀.mem = s.mem := by rw [hu₀]; exact m₃
  obtain gu : ∀ r, r ≠ .x6 → r ≠ .x9 → r ≠ .x11 → r ≠ .x12 → u.gpr r = s.gpr r := fun r h6 h9 h11 h12 => by
    rw [C.gpr r h9 h11 h12, hu₀, gpr_write_of_ne _ .x _ h11, g₃ r h6 h9 h12]
  obtain rdu : u.rd = s.rd := by rw [C.rd, hu₀]; exact rd₃
  obtain wru : u.wr = s.wr := by rw [C.wr, hu₀]; exact wr₃
  obtain tu : ∀ o < 4168, u.mem (T + BitVec.ofNat 64 o) = s.mem (T + BitVec.ofNat 64 o) := fun o ho => by
    rw [C.frame _ fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      exact P.tSch _ (Offset.contains_base T (by omega_using [ho]) (by omega_using [ho])) (Region.sub_prefix (by omega_using []) _ hc),
      m₀]
  obtain ku : bytesAt u.mem K L = bytesAt s.mem K L := by
    rw [bytesAt_frame C.frame fun c hc r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact P.keySch _ (kc c hc) (Region.sub_prefix (by omega_using []) _ hcon), m₀]
  obtain su : ∀ o < 4096, u.mem (S + BitVec.ofNat 64 o) = Impl.Blowfish.initByte o := fun o ho => by
    rw [C.copied o (by omega_using [ho]), m₀, table_byte P.held (by omega_using [ho])]
  obtain vu : ∀ r ∈ preservedV, u.v r = s.v r := fun r hr => by
    rw [C.v r (by simp [preservedV] at hr ⊢; rcases hr with h | h | h | h | h | h | h | h <;> subst h <;> decide),
      hu₀]
    exact v₃ r (by simp [preservedV] at hr; rcases hr with h | h | h | h | h | h | h | h <;> subst h <;> decide)
      (by simp [preservedV] at hr; rcases hr with h | h | h | h | h | h | h | h <;> subst h <;> decide)
  -- the P-array
  obtain PE : KeyPEnv T S K L u := by
    refine ⟨by omega, by omega_using [], fun c hc => ?_, gu _ (by decide) (by decide) (by decide) (by decide),
      ?_, ?_, ?_, ?_, ?_, P.tSch, fun c hc h => P.keySch _ (kc c hc) h⟩
    · rw [rdu, wru]; exact ⟨_, keyR, kc c hc⟩
    · rw [gu _ (by decide) (by decide) (by decide) (by decide)]; simp [L]
    · rw [C.x9]
    · rw [C.x12]
    · rw [rdu, wru]; exact ⟨_, tabR, contains_self _ _⟩
    · rw [wru]; exact ⟨_, schW, contains_self _ _⟩
  apply WP.seq
  refine WP.mono (keyP_run PE) fun u' KP => ?_
  obtain hK : scheduleAt u'.mem S = keyed (bytesAt u.mem K L) := by
    refine keyed_of_mem (fun o ho => ?_) (fun i hi => ?_)
    · rw [KP.frame _ fun r hr hc => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base S (d := 4096) (n := 4 * 18) (k := 4096) (by omega_using []) (by omega_using []) _ hc
          (Offset.contains_base S (by omega_using [ho]) (by omega_using [ho])), su o ho]
    · rw [KP.done i hi, table_P (fun o ho => (tu o ho).trans (table_byte P.held ho)) hi]
  obtain ev : u'.v = u.v := by rw [KP.eq]
  obtain wru' : u'.wr = s.wr := by rw [KP.eq]; exact wru
  -- keeping `d8`–`d15`
  obtain ⟨w, rw', w0, w1, w3, w4, w11, w16, w17, w27, wg, wv, we⟩ := saveLow_run u'
  apply WP.seq
  refine WP.of_runBlock ⟨w, rw', ?_⟩
  -- the encryptions
  obtain EE : EncEnv S w := by
    refine ⟨?_, fun off n h => by rw [we, wru']; exact ⟨_, schW, Offset.contains_base S h (by omega_using [h])⟩, ?_⟩
    · rw [wg _ (by decide), KP.gpr _ (by decide), gu _ (by decide) (by decide) (by decide) (by decide)]
    obtain cv : ∀ r, r = c64 ∨ r = c128 → w.v r = s₂.v r := fun r hr => by
      rw [wv r (by rcases hr with rfl | rfl <;> decide), ev,
        C.v r (by rcases hr with rfl | rfl <;> decide), hu₀]; rfl
    exact ⟨fun e he => by rw [cv _ (.inl rfl)]; exact c₂.1 e he,
      fun e he => by rw [cv _ (.inr rfl)]; exact c₂.2 e he⟩
  obtain hK' : scheduleAt w.mem S = keyed (bytesAt u.mem K L) := by rw [we]; exact hK
  apply WP.seq
  refine WP.mono (encryptions_run EE hK') fun u'' EI => ?_
  -- the epilogue
  obtain ⟨s', r', l8, l9, l10, l11, l12, l13, l14, l15, e'⟩ := restoreLow_run u''
  refine WP.of_runBlock ⟨s', r', ?_, ?_⟩
  · rw [show s'.mem = u''.mem by rw [e'], EI.sched, ← expandKey_eq, ku]
  · have kg : ∀ r, r ∉ encGprs → u''.gpr r = w.gpr r := EI.gpr
    obtain lv : ∀ r ∈ preservedV, low u' r = low s r := fun r hr => by
      simp only [low]; rw [ev, vu r hr]
    intro r hr
    simp only [preservedV, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [l8, kg _ (by decide), w0]; exact lv .v8 (by decide)
    · rw [l9, kg _ (by decide), w1]; exact lv .v9 (by decide)
    · rw [l10, kg _ (by decide), w3]; exact lv .v10 (by decide)
    · rw [l11, kg _ (by decide), w4]; exact lv .v11 (by decide)
    · rw [l12, kg _ (by decide), w11]; exact lv .v12 (by decide)
    · rw [l13, kg _ (by decide), w16]; exact lv .v13 (by decide)
    · rw [l14, kg _ (by decide), w17]; exact lv .v14 (by decide)
    · simp only [low]
      rw [l15, EI.v _ (by decide), w27, ev, vu _ (by decide)]

end VG.Proof.Blowfish.AArch64

end

end


@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.Impl.Blowfish.AArch64 VG.Spec.Blowfish VG.Proof.Blowfish

theorem initConsts_eq : initConsts = [(initSym, Impl.Blowfish.initWords)] := rfl

theorem initWords_length : Impl.Blowfish.initWords.length = 521 := by simp [Impl.Blowfish.initWords]

/-- Key expansion's contract as the code sees it. -/
def keyC : Contract isa where
  pre s := KeyPre s
  post s s' := scheduleAt s'.mem (s.gpr .x2) =
    Spec.Blowfish.expandKey (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
  pub s₁ s₂ := PublicRegs [.x0, .x1, .x2] s₁ s₂ ∧ s₁.syms initSym = s₂.syms initSym

theorem expandKey_ok (s : State) (hs : keyC.pre s) :
    ∃ t s', Exec isa Impl.Blowfish.AArch64.expandKey s t s' ∧ abiPreserved s s' ∧ keyC.post s s' := by
  obtain ⟨t, s', he, ⟨hk, hv⟩, hg⟩ := WP.gprs (c := Impl.Blowfish.AArch64.expandKey) (expandKey_correct hs)
    (rs := preserved) (by lit_decide) rfl
  exact ⟨t, s', he, ⟨hg, VG.AArch64.Exec.sp he, hv⟩, hk⟩

/-- The memory of the contract's witness: the table at `0x10000` (irreducible: unfolding it in a
definitional check would evaluate the table). -/
@[irreducible] def keySatMem : Mem := constMem 0x10000 Impl.Blowfish.initWords

theorem keySatMem_held : ∀ i < Impl.Blowfish.initWords.length,
    keySatMem.readW (0x10000 + BitVec.ofNat 64 (8 * i)) 64 = Impl.Blowfish.initWords.getD i 0 := by
  unfold keySatMem
  exact constMem_held _ _ (by rw [initWords_length]; omega_using [])

def keySatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 4 | .x2 => 0x3000 | _ => 0
  sp := 0x8000
  mem := keySatMem
  rd := [⟨0x1000, 4⟩, ⟨0x10000, 4168⟩]
  wr := [⟨0x3000, 4168⟩]
  syms _ := 0x10000

/-- The shared contract's precondition, from its facts. -/
theorem key_spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ⟨s.syms initSym, 4168⟩])
    (hw : s.wr = [⟨s.gpr .x2, 4168⟩])
    (ks : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x2, 4168⟩)
    (f0 : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64) (f2 : (s.gpr .x2).toNat + 4168 ≤ 2 ^ 64)
    (valid : validKey (s.gpr .x1).toNat)
    (held : ∀ i < Impl.Blowfish.initWords.length,
      s.mem.readW (s.syms initSym + BitVec.ofNat 64 (8 * i)) 64 = Impl.Blowfish.initWords.getD i 0)
    (fitT : (s.syms initSym).toNat + 4168 ≤ 2 ^ 64)
    (hdw : ∀ r ∈ s.wr, (⟨s.syms initSym, 4168⟩ : Region).Disjoint r) (hal : (s.syms initSym).toNat % 64 = 0) :
    (Spec.Blowfish.expandKeyContract (AArch64.abi.withConsts initConsts)).pre s := by
  sig_pre [Spec.Blowfish.expandKeyContract, Spec.Blowfish.expandKeySig,
    Spec.Blowfish.expandKeyPre, AArch64.abi, AArch64.argRegs, initConsts_eq, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow]
  rw [initWords_length]
  exact ⟨by rw [hrd]; rfl, fun i hi => held i (by rw [initWords_length]; exact hi), fitT, hdw, hal,
    by rw [hrd]; rfl, hw, ks, f0, f2, valid⟩

theorem expandKey_implies :
    keyC.Implies (Spec.Blowfish.expandKeyContract (AArch64.abi.withConsts initConsts)) where
  pre s h := by
    sig_pre [Spec.Blowfish.expandKeyContract, Spec.Blowfish.expandKeySig,
      Spec.Blowfish.expandKeyPre, AArch64.abi, AArch64.argRegs, initConsts_eq, Abi.withConsts,
      Abi.constRegions, Abi.constsHeld, stackBelow] at h
    rw [initWords_length] at h
    obtain ⟨hd, held, fitT, hdw, -, ht, hw, ks, -, fitS, valid⟩ := h
    have tw : ∀ r ∈ s.wr, (⟨s.syms initSym, 4168⟩ : Region).Disjoint r := hdw
    refine ⟨valid, ?_, hw, ks, fitS, held, fitT, tw _ (by rw [hw]; exact List.mem_cons_self)⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post := by
    intro s s' _ h
    sig_post [Spec.Blowfish.expandKeyContract, Spec.Blowfish.expandKeySig,
      Spec.Blowfish.expandKeyPost, AArch64.abi, AArch64.argRegs, initConsts_eq, Abi.withConsts]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Blowfish.expandKeyContract, Spec.Blowfish.expandKeySig,
      AArch64.abi, AArch64.argRegs, initConsts_eq, Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2⟩ := h
    exact ⟨⟨hsp, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2⟩, hsy⟩
  sat := ⟨keySatState, key_spec_pre rfl rfl (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) keySatMem_held (by decide) (fun r hr => by
      simp only [keySatState, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact Region.disjoint_of_sep (by decide)) (by decide)⟩

theorem expandKey_verified : Verified target Impl.Blowfish.AArch64.expandKey
    (Spec.Blowfish.expandKeyContract (AArch64.abi.withConsts initConsts)) :=
  Verified.of_correct expandKey_ok (expandKey_constantTime _) expandKey_implies

end VG.Proof.Blowfish.AArch64
