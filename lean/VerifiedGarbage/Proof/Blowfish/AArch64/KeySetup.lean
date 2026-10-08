import VerifiedGarbage.Proof.Blowfish.AArch64.EcbMain
import VerifiedGarbage.Proof.Blowfish.Table
import VerifiedGarbage.Proof.Blowfish.KeyTable

/-!
# Key expansion: the initial S-boxes and the keyed P-array

`copyPlanes_run`: the 4096 bytes of the table at `x9` into the schedule at
`x12`, 64 at a time. `keyP_run`: the 18 P-array entries, the table's XORed
with the key's words, cycling through the key bytes.
-/

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64
open VG.Spec.Blowfish VG.Proof.Blowfish
open VG.AArch64.Tbl (VOnly)

theorem write16_at (m : Mem) (p : Addr) (x : BitVec 128) {o j : Nat} (ho : o + 16 ≤ 2 ^ 64) (hj : j < 2 ^ 64) :
    m.write (p + BitVec.ofNat 64 o) 16 x (p + BitVec.ofNat 64 j) =
      if o ≤ j ∧ j < o + 16 then vbyte x (j - o) else m (p + BitVec.ofNat 64 j) := by
  simp only [Mem.write, Offset.sub_toNat' p (show o < 2 ^ 64 by omega) hj]
  by_cases h : o ≤ j
  · simp only [h, ite_true, true_and]
    by_cases h' : j < o + 16
    · simp only [show j - o < 16 by omega, h', ite_true]; rfl
    · simp only [show ¬ j - o < 16 by omega, h', ite_false]
  · simp only [h, ite_false, false_and]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

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
  have e : a + BitVec.ofNat 64 o - r.base = (a - r.base) + BitVec.ofNat 64 o := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 o),
      ← BitVec.add_assoc]
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := Nat.mod_le ((a - r.base).toNat + o % 2 ^ 64) (2 ^ 64)
  have := Nat.mod_le o (2 ^ 64)
  omega

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
  have rdT : ∀ r < 4, ∀ {t : State}, t.rd = s₀.rd → t.wr = s₀.wr → t.gpr .x9 = u.gpr .x9 →
      InRegions (t.rd ++ t.wr) (t.gpr .x9 + BitVec.ofNat 64 (16 * r)) 16 := by
    intro r hr t h1 h2 h3
    rw [h1, h2, h3, I.x9, Offset.add_add]
    exact inRegions_off E.rdT (by omega)
  have wrS : ∀ r < 4, ∀ {t : State}, t.wr = s₀.wr → t.gpr .x12 = u.gpr .x12 →
      InRegions t.wr (t.gpr .x12 + BitVec.ofNat 64 (16 * r)) 16 := by
    intro r hr t h2 h3
    rw [h2, h3, I.x12, Offset.add_add]
    exact inRegions_off E.wrS (by omega)
  obtain ⟨u₁, r₁, v₁, o₁⟩ := ldrq_run (t := u) .v28 .x9 (off := 16 * 0) (by omega) (rdT 0 (by decide) I.rd I.wr rfl)
  obtain ⟨u₂, r₂, v₂, o₂⟩ := ldrq_run (t := u₁) .v29 .x9 (off := 16 * 1) (by omega)
    (rdT 1 (by decide) (o₁.rd.trans I.rd) (o₁.wr.trans I.wr) (by rw [o₁.gpr]))
  obtain ⟨u₃, r₃, v₃, o₃⟩ := ldrq_run (t := u₂) .v30 .x9 (off := 16 * 2) (by omega)
    (rdT 2 (by decide) (o₂.rd.trans (o₁.rd.trans I.rd)) (o₂.wr.trans (o₁.wr.trans I.wr)) (by rw [o₂.gpr, o₁.gpr]))
  obtain ⟨u₄, r₄, v₄, o₄⟩ := ldrq_run (t := u₃) .v31 .x9 (off := 16 * 3) (by omega)
    (rdT 3 (by decide) (o₃.rd.trans (o₂.rd.trans (o₁.rd.trans I.rd)))
      (o₃.wr.trans (o₂.wr.trans (o₁.wr.trans I.wr))) (by rw [o₃.gpr, o₂.gpr, o₁.gpr]))
  have o₁₄ : VOnly [.v28, .v29, .v30, .v31] u u₄ := (((VOnly.mono o₁ (by simp)).trans (VOnly.mono o₂ (by simp))).trans
    (VOnly.mono o₃ (by simp))).trans (VOnly.mono o₄ (by simp))
  -- the values loaded
  have g₄ : u₄.gpr = u.gpr := o₁₄.gpr
  have mm₄ : u₄.mem = u.mem := o₁₄.mem
  have ld : ∀ r < 4, u₄.v (tReg r) = u.mem.read (T + BitVec.ofNat 64 (64 * i + 16 * r)) 16 := by
    intro r hr
    have a : ∀ q : Nat, u.gpr .x9 + BitVec.ofNat 64 (16 * q) = T + BitVec.ofNat 64 (64 * i + 16 * q) := by
      intro q; rw [I.x9, Offset.add_add]
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl
    · rw [show tReg 0 = .v28 from rfl, o₄.2 _ (by simp), o₃.2 _ (by simp), o₂.2 _ (by simp), v₁, a]
    · rw [show tReg 1 = .v29 from rfl, o₄.2 _ (by simp), o₃.2 _ (by simp), v₂, o₁.mem, o₁.gpr, a]
    · rw [show tReg 2 = .v30 from rfl, o₄.2 _ (by simp), v₃, o₂.mem, o₁.mem, o₂.gpr, o₁.gpr, a]
    · rw [show tReg 3 = .v31 from rfl, v₄, o₃.mem, o₂.mem, o₁.mem, o₃.gpr, o₂.gpr, o₁.gpr, a]
  have wr₄ : u₄.wr = s₀.wr := o₁₄.wr.trans I.wr
  obtain ⟨u₅, r₅, m₅, p₅⟩ := strq_run (t := u₄) .v28 .x12 (off := 16 * 0) (by omega) (wrS 0 (by decide) wr₄ (by rw [g₄]))
  obtain ⟨u₆, r₆, m₆, p₆⟩ := strq_run (t := u₅) .v29 .x12 (off := 16 * 1) (by omega)
    (wrS 1 (by decide) (p₅.wr.trans wr₄) (by rw [p₅.gpr, g₄]))
  obtain ⟨u₇, r₇, m₇, p₇⟩ := strq_run (t := u₆) .v30 .x12 (off := 16 * 2) (by omega)
    (wrS 2 (by decide) (p₆.wr.trans (p₅.wr.trans wr₄)) (by rw [p₆.gpr, p₅.gpr, g₄]))
  obtain ⟨u₈, r₈, m₈, p₈⟩ := strq_run (t := u₇) .v31 .x12 (off := 16 * 3) (by omega)
    (wrS 3 (by decide) (p₇.wr.trans (p₆.wr.trans (p₅.wr.trans wr₄))) (by rw [p₇.gpr, p₆.gpr, p₅.gpr, g₄]))
  have p₅₈ : MOnly [] u₄ u₈ := ((p₅.trans p₆).trans p₇).trans p₈
  let u₉ := u₈.write .x .x9 (u₈.read .x .x9 + BitVec.ofNat _ 64)
  let u₁₀ := u₉.write .x .x12 (u₉.read .x .x12 + BitVec.ofNat _ 64)
  let u₁₁ := u₁₀.write .x .x11 (u₁₀.read .x .x11 - BitVec.ofNat _ 1)
  have r₉ : runBlock isa [.addImm .x .x9 .x9 64, .addImm .x .x12 .x12 64, .subImm .x .x11 .x11 1] u₈ = some u₁₁ := by
    rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide),
      runStep_some, runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil]
  refine ⟨u₁₁, cat_run r₁ (cat_run r₂ (cat_run r₃ (cat_run r₄ (cat_run r₅ (cat_run r₆ (cat_run r₇ (cat_run r₈ r₉))))))),
    ?_⟩
  -- the stored values
  have vv : ∀ r < 4, u₇.v (tReg r) = u₄.v (tReg r) := fun r _ => by
    rw [p₇.v _ (List.not_mem_nil), p₆.v _ (List.not_mem_nil), p₅.v _ (List.not_mem_nil)]
  have gg : u₇.gpr = u₄.gpr := by rw [p₇.gpr, p₆.gpr, p₅.gpr]
  have x12₄ : u₄.gpr .x12 = S + BitVec.ofNat 64 (64 * i) := by rw [g₄, I.x12]
  have memS : ∀ o < 64 * (i + 1), u₈.mem (S + BitVec.ofNat 64 o) = s₀.mem (T + BitVec.ofNat 64 o) := by
    intro o ho
    have fS := E.fitS
    rw [m₈, show u₇.gpr = u₄.gpr from gg, x12₄, Offset.add_add, write16_at _ _ _ (by omega) (by omega),
      m₇, show u₆.gpr = u₄.gpr by rw [p₆.gpr, p₅.gpr], x12₄, Offset.add_add,
      write16_at _ _ _ (by omega) (by omega),
      m₆, show u₅.gpr = u₄.gpr by rw [p₅.gpr], x12₄, Offset.add_add, write16_at _ _ _ (by omega) (by omega),
      m₅, x12₄, Offset.add_add, write16_at _ _ _ (by omega) (by omega), mm₄]
    have hT : ∀ o' < 4168, u.mem (T + BitVec.ofNat 64 o') = s₀.mem (T + BitVec.ofNat 64 o') := fun o' ho' =>
      I.frame.bytes (R := ⟨T, 4168⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact E.sep.sub_right (Region.sub_prefix (by omega))) (show 4168 ≤ 2 ^ 64 by decide) ho'
    have byteAt : ∀ r < 4, ∀ (x : BitVec 128), x = u₄.v (tReg r) → 64 * i + 16 * r ≤ o →
        o < 64 * i + 16 * r + 16 → vbyte x (o - (64 * i + 16 * r)) = s₀.mem (T + BitVec.ofNat 64 o) := by
      intro r hr x hx h1 h2
      rw [hx, ld r hr, vbyte_read16 _ _ (by omega), Offset.add_add,
        show 64 * i + 16 * r + (o - (64 * i + 16 * r)) = o by omega, hT o (by omega)]
    split
    · exact byteAt 3 (by decide) _ (vv 3 (by decide)) (by omega) (by omega)
    · split
      · exact byteAt 2 (by decide) _ (by rw [p₆.v _ (List.not_mem_nil), p₅.v _ (List.not_mem_nil)]; rfl)
          (by omega) (by omega)
      · split
        · exact byteAt 1 (by decide) _ (by rw [p₅.v _ (List.not_mem_nil)]; rfl) (by omega) (by omega)
        · split
          · exact byteAt 0 (by decide) _ rfl (by omega) (by omega)
          · exact I.copied o (by omega)
  have g₈ : u₈.gpr = u.gpr := by rw [p₅₈.gpr, g₄]
  have fS := E.fitS
  have fr : Frame [⟨S, 4096⟩] s₀.mem u₈.mem := by
    have c : ∀ r < 4, (⟨S, 4096⟩ : Region).Contains (S + BitVec.ofNat 64 (64 * i + 16 * r)) 16 :=
      fun r hr => Offset.contains_base _ (by omega) (by omega)
    rw [m₈, m₇, m₆, m₅, show u₇.gpr = u₄.gpr from gg, show u₆.gpr = u₄.gpr by rw [p₆.gpr, p₅.gpr],
      show u₅.gpr = u₄.gpr by rw [p₅.gpr], x12₄, Offset.add_add, Offset.add_add, Offset.add_add,
      Offset.add_add, mm₄]
    exact (((I.frame.write List.mem_cons_self _ (c 0 (by decide))).write List.mem_cons_self _ (c 1 (by decide))).write
      List.mem_cons_self _ (c 2 (by decide))).write List.mem_cons_self _ (c 3 (by decide))
  refine ⟨by omega, ?_, ?_, ?_, fun o ho => memS o ho, fr, fun r a b c => ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · simp only [u₁₁, u₁₀, u₉, State.write, State.read, BitVec.setWidth_eq, reduceCtorEq, ite_false, ite_true]
    rw [g₈, I.x9, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact congrArg _ (congrArg _ (by omega))
  · simp only [u₁₁, u₁₀, State.write, State.read, BitVec.setWidth_eq, reduceCtorEq, ite_false, ite_true]
    rw [show u₉.gpr .x12 = u₈.gpr .x12 from rfl, g₈, I.x12, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact congrArg _ (congrArg _ (by omega))
  · simp only [u₁₁, State.write, State.read, BitVec.setWidth_eq, ite_true]
    rw [show u₁₀.gpr .x11 = u₈.gpr .x11 from rfl, g₈, I.x11, show 64 - i = (64 - (i + 1)) + 1 by omega,
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
  have E₁ : CopyEnv T S s₁ := ⟨E.rdT, E.wrS, E.sep, E.fitT, E.fitS⟩
  rw [copyPlanes]
  apply WP.seq
  refine WP.of_runBlock ⟨s₁, rfl, ?_⟩
  have I₀ : CopyPInv T S s₁ 0 s₁ := ⟨by omega, by simp [s₁, State.write, hx9], by simp [s₁, State.write, hx12],
    rfl, fun o ho => by omega, Frame.refl _ _, fun _ _ _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  refine WP.mono (WP.loop (M := isa) (Q := CopyPInv T S s₁ 64) (fun m u => ∃ i, i < 64 ∧ m = 64 - i ∧
    CopyPInv T S s₁ i u) ?_ 64 s₁ ⟨0, by omega, rfl, I₀⟩) fun u h => ⟨s₁, rfl, h⟩
  intro m u ⟨i, hi, hm, I⟩
  obtain ⟨u', r, I'⟩ := copyStep E₁ hi I
  refine WP.of_runBlock ⟨u', by rw [copyBody_eq]; exact r, ?_⟩
  have flag := eval_nonzero u' .x11 I'.x11 (by omega)
  by_cases h : i + 1 = 64
  · left; exact ⟨by rw [flag]; simp; omega, h ▸ I'⟩
  · right; exact ⟨by rw [flag]; simp; omega, 64 - (i + 1), by omega, i + 1, by omega, rfl, I'⟩

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
  have a₁ : s₁.gpr .x13 + BitVec.ofNat 64 0 = K + BitVec.ofNat 64 c := by
    simp [s₁, State.write, State.read, h0, h10]
  have hr₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x13 + BitVec.ofNat 64 0) 1 := by
    rw [a₁]; exact hK c hc
  let byte := s.mem (K + BitVec.ofNat 64 c)
  let s₂ := s₁.write .w .x14 ((s₁.mem.read (s₁.gpr .x13 + BitVec.ofNat 64 0) 1).setWidth 32)
  have e₂ : exec (.ldrb .x14 .x13 0) s₁ = some s₂ := by
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
  have r1 : ∀ (m : Mem) (a : Addr), (m.read a 1).setWidth 32 = (m a).zeroExtend 32 := by
    intro m a
    have h := Mem.extractLsb'_read m a (n := 1) (j := 0) (by decide)
    have e : (m.read a 1) = (m.read a 1).extractLsb' (8 * 0) 8 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
    rw [e, h, BitVec.add_zero]
  have x8₆ : (s₆.gpr .x8).setWidth 32 =
      ((s.gpr .x8).setWidth 32 <<< 8) ||| (s.mem (K + BitVec.ofNat 64 c)).zeroExtend 32 := by
    simp only [s₆, s₅, s₄, s₃, s₂, s₁, State.write, State.read, reduceCtorEq, ite_false, ite_true,
      Size.bits, BitVec.setWidth_eq, BitVec.add_zero, h0, h10, r1]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [hi]
  have x10₆ : s₆.gpr .x10 = BitVec.ofNat 64 (c + 1) := by
    simp only [s₆, s₅, State.write, State.read, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
    rw [show s₄.gpr .x10 = s.gpr .x10 by simp [s₄, s₃, s₂, s₁, State.write], h10, BitVec.ofNat_add_ofNat]
  have x13₆ : s₆.gpr .x13 = BitVec.ofNat 64 (c + 1) - BitVec.ofNat 64 L := by
    simp only [s₆, State.write, State.read, ite_true, BitVec.setWidth_eq]
    rw [show s₅.gpr .x10 = s₆.gpr .x10 by simp [s₆, State.write], x10₆,
      show s₅.gpr .x1 = s.gpr .x1 by simp [s₅, s₄, s₃, s₂, s₁, State.write], h1]
  have g₆ : ∀ r, KeyByteRegs r → s₆.gpr r = s.gpr r := by
    intro r ⟨a, b, c', d⟩
    simp [s₆, s₅, s₄, s₃, s₂, s₁, State.write, a, b, c', d]
  have zero : isa.eval (.zero .x .x13) s₆ = some (c + 1 == L) := by
    show some (s₆.read .x .x13 == 0) = _
    simp only [State.read, BitVec.setWidth_eq, x13₆]
    congr 1
    by_cases h : c + 1 = L
    · subst h; simp
    · have : BitVec.ofNat 64 (c + 1) - BitVec.ofNat 64 L ≠ 0 := by
        intro e
        have e' := congrArg (· + BitVec.ofNat 64 L) e
        simp only [BitVec.sub_add_cancel] at e'
        have := congrArg BitVec.toNat e'
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
        rw [show BitVec.toNat (0 : BitVec 64) = 0 from rfl, Nat.zero_add, Nat.mod_eq_of_lt hL,
          Nat.mod_eq_of_lt hL, Nat.mod_eq_of_lt (by omega)] at this
        omega
      simp only [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h]
  have st₆ : s₆ = { s with gpr := s₆.gpr } := rfl
  apply WP.ite _ zero
  · intro h
    have hL' : c + 1 = L := by simpa using h
    let s₇ := s₆.write .x .x10 ((0 : BitVec 16).setWidth 64 <<< (16 * 0))
    refine WP.of_runBlock ⟨s₇, rfl, ?_, ?_, fun r hr => ?_, rfl⟩
    · simp only [s₇, State.write, reduceCtorEq, ite_false]; exact x8₆
    · simp [s₇, State.write, ← hL']
    · simp only [s₇, State.write, hr.2.1, ite_false]; exact g₆ r hr
  · intro h
    have hL' : c + 1 ≠ L := by simpa using h
    exact WP.block_nil ⟨x8₆, by rw [x10₆, Nat.mod_eq_of_lt (by omega)], g₆, st₆⟩

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
  have g₀ : ∀ r, r ≠ .x8 → s₀.gpr r = s.gpr r := fun r hr => by simp [s₀, State.write, hr]
  have x8₀ : (s₀.gpr .x8).setWidth 32 = 0 := by simp [s₀, State.write]
  -- the four key bytes
  have step : ∀ (t : State) (m : Nat), t = { s with gpr := t.gpr } → t.gpr .x0 = K →
      t.gpr .x1 = BitVec.ofNat 64 L → t.gpr .x10 = BitVec.ofNat 64 ((4 * i + m) % L) →
      ∀ {Q : State → Prop}, (∀ t', (t'.gpr .x8).setWidth 32 = ((t.gpr .x8).setWidth 32 <<< 8) |||
        ((bytesAt s.mem K L).getD ((4 * i + m) % L) 0).zeroExtend 32 →
        t'.gpr .x10 = BitVec.ofNat 64 ((4 * i + (m + 1)) % L) → (∀ r, KeyByteRegs r → t'.gpr r = t.gpr r) →
        t' = { s with gpr := t'.gpr } → Q t') → WP isa keyByte t Q := by
    intro t m ht h0 h1 h10 Q k
    have kt : KeyIn t K L := by rw [ht]; exact E.key
    refine WP.mono (keyByte_run (Nat.mod_lt _ hL0) E.L64 kt h0 h1 h10) fun t' ⟨a, b, c, d⟩ => k t' ?_ ?_ c ?_
    · rw [a, bytesAt_getD _ _ (Nat.mod_lt _ hL0), ht]
    · rw [b, mod_succ _ _ hL0, Nat.add_assoc]
    · rw [d, ht]
  have e₀ : s₀ = { s with gpr := s₀.gpr } := rfl
  have hlen : (bytesAt s.mem K L).length = L := by simp [bytesAt]
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
  have kw : (t₄.gpr .x8).setWidth 32 = keyWord (bytesAt s.mem K L) i := by
    rw [a₄, a₃, a₂, a₁, x8₀, keyWord_eq, hlen]
  have g₄ : ∀ r, KeyByteRegs r → r ≠ .x8 → t₄.gpr r = s.gpr r := fun r hr h8 => by
    rw [c₄ r hr, c₃ r hr, c₂ r hr, c₁ r hr, g₀ r h8]
  have x9₄ : t₄.gpr .x9 = T + BitVec.ofNat 64 (4096 + 4 * i) :=
    (g₄ _ (by decide) (by decide)).trans E.x9
  have x12₄ : t₄.gpr .x12 = S + BitVec.ofNat 64 (4096 + 4 * i) :=
    (g₄ _ (by decide) (by decide)).trans E.x12
  have m₄ : t₄.mem = s.mem := by rw [d₄]
  have rdT : InRegions (t₄.rd ++ t₄.wr) (t₄.gpr .x9 + BitVec.ofNat 64 0) 4 := by
    have h1 : t₄.rd = s.rd := by rw [d₄]
    have h2 : t₄.wr = s.wr := by rw [d₄]
    rw [h1, h2, BitVec.add_zero, x9₄]; exact E.rdT
  let t₅ := t₄.write .w .x14 (t₄.mem.readW (t₄.gpr .x9 + BitVec.ofNat 64 0) 32)
  let t₆ := t₅.write .w .x14 (t₅.read .w .x14 ^^^ t₅.read .w .x8)
  have wrS : InRegions t₆.wr (t₆.gpr .x12 + BitVec.ofNat 64 0) 4 := by
    have h2 : t₆.wr = s.wr := by rw [show t₆.wr = t₄.wr from rfl, d₄]
    have h3 : t₆.gpr .x12 = t₄.gpr .x12 := by simp [t₆, t₅, State.write]
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
    have h14 : (t₆.gpr .x14).setWidth 32 =
        s.mem.readW (T + BitVec.ofNat 64 (4096 + 4 * i)) 32 ^^^ keyWord (bytesAt s.mem K L) i := by
      simp only [t₆, t₅, State.write, State.read, ite_true, reduceCtorEq, ite_false, Size.bits,
        BitVec.add_zero]
      rw [m₄, x9₄, ← kw]
      apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [hj]
    have h12 : t₆.gpr .x12 = t₄.gpr .x12 := by simp [t₆, t₅, State.write]
    rw [h14, h12, BitVec.add_zero, x12₄, show t₆.mem = s.mem from m₄]
  · simp [t₁₀, t₉, t₈, t₇, t₆, t₅, State.write]
    rw [b₄]; rfl
  · simp [t₁₀, t₉, t₈, t₇, t₆, t₅, State.write, State.read]
    rw [g₄ _ (by decide) (by decide)]
  · simp [t₁₀, t₉, t₈, t₇, t₆, t₅, State.write, State.read]
    rw [g₄ _ (by decide) (by decide)]
  · simp [t₁₀, t₉, t₈, t₇, t₆, t₅, State.write, State.read]
    rw [g₄ _ (by decide) (by decide)]
  · obtain ⟨a, b, c, d, e, f, g⟩ := hr
    simp [t₁₀, t₉, t₈, t₇, t₆, t₅, State.write, b, d, e, g]
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
  have hrd : u.rd = s₀.rd := by rw [I.eq]
  have hwr : u.wr = s₀.wr := by rw [I.eq]
  have W : KeyWordEnv T S K L i u := by
    refine ⟨hi, E.L0, E.L64, fun c hc => ?_, (I.gpr _ (by decide)).trans E.x0, (I.gpr _ (by decide)).trans E.x1,
      I.x10, I.x9, I.x12, ?_, ?_⟩
    · rw [hrd, hwr]; exact E.key c hc
    · rw [hrd, hwr]; exact inRegions_off E.rdT (by omega)
    · rw [hwr]; exact inRegions_off E.wrS (by omega)
  refine WP.mono (keyWord_run W) fun u' ⟨m', x10', x9', x12', x11', g', e'⟩ => ?_
  have dTS : (⟨T, 4168⟩ : Region).Disjoint ⟨S + BitVec.ofNat 64 4096, 4 * i⟩ :=
    E.sep.sub_right (Offset.sub_base S (d := 4096) (n := 4 * i) (k := 4168) (by omega))
  have hT : u.mem.readW (T + BitVec.ofNat 64 (4096 + 4 * i)) 32 =
      s₀.mem.readW (T + BitVec.ofNat 64 (4096 + 4 * i)) 32 :=
    I.frame.readW (r := ⟨T, 4168⟩) (Offset.contains_base T (by omega) (by omega))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dTS) (by decide)
  have hB : bytesAt u.mem K L = bytesAt s₀.mem K L :=
    bytesAt_frame I.frame fun c hc r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact E.keyS c hc (Offset.sub_base S (d := 4096) (n := 4 * i) (k := 4168) (by omega) _ hcon)
  refine ⟨by omega, x10', ?_, ?_, ?_, fun j hj => ?_, ?_, fun r hr => (g' r hr).trans (I.gpr r hr), ?_⟩
  · rw [x9', I.x9, BitVec.add_assoc]
    exact congrArg (T + ·) (by apply BitVec.eq_of_toNat_eq; simp; omega)
  · rw [x12', I.x12, BitVec.add_assoc]
    exact congrArg (S + ·) (by apply BitVec.eq_of_toNat_eq; simp; omega)
  · rw [x11', I.x11]
    apply BitVec.eq_of_toNat_eq; simp; omega
  · rw [m', hT, hB]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep S (by omega) (by omega) (by omega)) (by decide)]
      exact I.done j hj
    · exact Mem.readW_writeW_self32 _ _ _
  · rw [m']
    refine Frame.writeW (Frame.sub I.frame fun r hr => ⟨⟨S + BitVec.ofNat 64 4096, 4 * (i + 1)⟩,
      List.mem_singleton_self _, ?_⟩) (List.mem_singleton_self _) _
      (Offset.contains S (by omega) (by omega) (by omega))
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub S (by omega) (by omega)
  · rw [e']; rw [I.eq]

theorem keyP_run {T S K : Addr} {L : Nat} {s₀ : State} (E : KeyPEnv T S K L s₀) :
    WP isa keyP s₀ (KeyPInv T S K L s₀ 18) := by
  rw [keyP]
  apply WP.seq
  let s₁ := (s₀.write .x .x10 ((0 : BitVec 16).setWidth 64 <<< (16 * 0))).write .x .x11
    ((18 : BitVec 16).setWidth 64 <<< (16 * 0))
  refine WP.of_runBlock ⟨s₁, rfl, ?_⟩
  have I₀ : KeyPInv T S K L s₀ 0 s₁ := by
    refine ⟨by omega, by simp [s₁, State.write], ?_, ?_, by simp [s₁, State.write], fun j hj => by omega,
      Frame.refl _ _, fun r ⟨_, _, h10, h11, _⟩ => by simp [s₁, State.write, h10, h11], rfl⟩
    · simp [s₁, State.write, E.x9]
    · simp [s₁, State.write, E.x12]
  refine WP.loop (M := isa) (fun m u => ∃ i, i < 18 ∧ m = 18 - i ∧ KeyPInv T S K L s₀ i u)
    ?_ 18 s₁ ⟨0, by omega, rfl, I₀⟩
  intro m u ⟨i, hi, hm, I⟩
  refine WP.mono (keyP_step E hi I) fun u' I' => ?_
  have flag := eval_nonzero u' .x11 I'.x11 (by omega)
  by_cases h : i + 1 = 18
  · left; exact ⟨by rw [flag]; simp; omega, h ▸ I'⟩
  · right; exact ⟨by rw [flag]; simp; omega, 18 - (i + 1), by omega, i + 1, by omega, rfl, I'⟩

end VG.Proof.Blowfish.AArch64
