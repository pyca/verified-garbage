module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Entry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry

/-!
# RSAES-OAEP decryption on PPC64LE: the private operation's arguments

Untrusted: everything here is checked by Lean. In the frame of `privBytes`
bytes below ours (`pb`), `privArgs` writes `vg_rsa_private_checked`'s twelve
stack arguments to its Parameter Save Area (`psa`: `p`, our stack arguments
0 to 8, the rest of `scratch` and its length in words) and sets its
registers (`AtPriv`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_ld wp_std wp_mov wp_li wp_add wp_addi wp_subi wp_addSp wp_nil)

/-- The base of the private operation's frame. -/
abbrev pb (s : State) : Addr := fb s - BitVec.ofNat 64 privBytes

/-- Its stack argument `i`, as `privArgs` writes it. -/
def psa (s : State) : Nat → BitVec 64
  | 0 => s.gpr .r10
  | 10 => Sd s + BitVec.ofNat 64 oRsa
  | 11 => BitVec.ofNat 64 ((stackArg s 14).toNat - 1024)
  | i + 1 => stackArg s i

theorem pb_eq (s : State) : pb s = s.sp - BitVec.ofNat 64 (frameBytes + privBytes) := by
  rw [pb, fb, BitVec.sub_sub, BitVec.ofNat_add]

/-- The region of `pb s + d` within the stack the function uses. -/
theorem pb_base (s : State) :
    pb s = (s.sp - BitVec.ofNat 64 stackBytes) + BitVec.ofNat 64 Impl.Rsa.PPC64LE.Priv.frameBytes := by
  rw [pb, fb, ← Offset.sub_add_eq, ← BitVec.ofNat_add, ← Offset.sub_sub_eq, Offset.ofNat_sub_ofNat (by decide)]; rfl

/-- The region of `pb s + d` within the stack the function uses. -/
theorem pb_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes + privBytes) :
    Region.Sub ⟨pb s + BitVec.ofNat 64 d, n⟩ (kD s) := by
  rw [pb_base, Offset.add_add]; exact Offset.sub_base _ (by unfold stackBytes; omega)

/-- In the private operation's frame, at the call. -/
structure AtPriv (s t : State) : Prop where
  sp : t.sp = pb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨pb s + BitVec.ofNat 64 32, 160⟩ :: fr s :: s.wr
  mem : Frame [kD s] s.mem t.mem
  sv : Spill.Saved (fb s) s.gpr saved t.mem
  ls : t.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr
  hi : ∀ r ∈ hiRegs, t.gpr r = s.gpr r
  r3 : t.gpr .r3 = Sd s
  r4 : t.gpr .r4 = s.gpr .r7
  r5 : t.gpr .r5 = s.gpr .r6
  r6 : t.gpr .r6 = s.gpr .r7
  r7 : t.gpr .r7 = s.gpr .r8
  r8 : t.gpr .r8 = s.gpr .r9
  r9 : t.gpr .r9 = stackArg s 11
  r10 : t.gpr .r10 = s.gpr .r7
  r14 : t.gpr .r14 = Sd s
  r15 : t.gpr .r15 = s.gpr .r7
  r16 : t.gpr .r16 = s.gpr .r3
  r17 : t.gpr .r17 = s.gpr .r5
  r18 : t.gpr .r18 = stackArg s 9
  r19 : t.gpr .r19 = stackArg s 10
  keep : ∀ r ∈ [Reg.r20, .r21, .r22, .r23], t.gpr r = s.gpr r
  psa : ∀ i < 12, t.mem.readW (pb s + BitVec.ofNat 64 (96 + 8 * i)) 64 = psa s i

/-- The state of the copies of our stack arguments: `n` of them done. -/
structure Cp (s t₀ : State) (n : Nat) (t : State) : Prop where
  k : Keep [.r0] t₀ t
  mem : Frame [⟨pb s + BitVec.ofNat 64 104, 72⟩] t₀.mem t.mem
  got : ∀ j < n, t.mem.readW (pb s + BitVec.ofNat 64 (104 + 8 * j)) 64 = stackArg s j

theorem privArgs_eq : privArgs = ([.addSp .r12 0, .store .d .r10 .r12 96] : List Instr) ++
    ((List.range 9).flatMap fun j => [.load .d .r0 .r12 (argP j), .store .d .r0 .r12 (104 + 8 * j)]) ++
    ([.li .r0 oRsa, .add .r0 .r14 .r0, .store .d .r0 .r12 176, .load .d .r11 .r12 (argP 14),
      .subi .r11 .r11 1024, .store .d .r11 .r12 184, .addi .r3 .r14 oEm, Impl.AesGcm.PPC64LE.mov .r4 .r15,
      Impl.AesGcm.PPC64LE.mov .r5 .r6, Impl.AesGcm.PPC64LE.mov .r6 .r15, Impl.AesGcm.PPC64LE.mov .r7 .r8,
      Impl.AesGcm.PPC64LE.mov .r8 .r9, .load .d .r9 .r12 (argP 11), Impl.AesGcm.PPC64LE.mov .r10 .r15] :
      List Instr) := rfl

/-- `pb s + d` in the stack the function uses. -/
theorem pb_contains (s : State) {d n : Nat} (h : d + n ≤ frameBytes + privBytes) :
    (kD s).Contains (pb s + BitVec.ofNat 64 d) n := by
  rw [pb_base, Offset.add_add]
  exact Offset.contains_base _ (by unfold stackBytes; omega)
    (by unfold Impl.Rsa.PPC64LE.Priv.frameBytes frameBytes privBytes at *; omega)

theorem allocP_mem {s t : State} (E : Entered s t) : Frame [kD s] s.mem (allocated privBytes t).mem := by
  have hsp : t.sp = fb s := E.sv.sp
  refine (toD E.mem).write (List.mem_singleton_self _) _ ?_
  rw [hsp, show fb s - BitVec.ofNat 64 privBytes = pb s + BitVec.ofNat 64 0 by rw [BitVec.add_zero]]
  exact pb_contains s (by decide)

theorem sub_ofNat {x : BitVec 64} {a : Nat} (h : a ≤ x.toNat) : x - BitVec.ofNat 64 a = BitVec.ofNat 64 (x.toNat - a) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (a := x.toNat - a) (by omega)]; omega

/-- The private operation's frame. -/
abbrev PB (s : State) : Region := ⟨pb s, privBytes⟩

theorem pb_in (s : State) {d : Nat} (h : d + 8 ≤ privBytes) : (PB s).Contains (pb s + BitVec.ofNat 64 d) 8 :=
  Offset.contains_base _ h (by unfold privBytes at h; omega)

section
variable {s : State} (P : PreD s)
include P

omit P in
theorem psa_in {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ privBytes) :
    InRegions (⟨pb s + BitVec.ofNat 64 32, 160⟩ :: fr s :: s.wr) (pb s + BitVec.ofNat 64 d) 8 :=
  ⟨_, List.mem_cons_self .., Offset.contains _ h₁ (by unfold privBytes at h₂; omega) (by decide)⟩

/-- The copies of our stack arguments 0 to `n - 1`. -/
theorem copies_ok {t₀ : State} (h12 : t₀.gpr .r12 = pb s) (hrd : t₀.rd = s.rd)
    (hwr : t₀.wr = ⟨pb s + BitVec.ofNat 64 32, 160⟩ :: fr s :: s.wr) (hm : Frame [kD s] s.mem t₀.mem) :
    ∀ n ≤ 9, WP isa (.block ((List.range n).flatMap fun j =>
      [.load .d .r0 .r12 (argP j), .store .d .r0 .r12 (104 + 8 * j)])) t₀ (Cp s t₀ n)
  | 0, _ => wp_nil ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (copies_ok h12 hrd hwr hm n (by omega)) fun t ⟨k, fm, got⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hmt : Frame [kD s] s.mem t.mem := hm.trans (fm.sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨kD s, List.mem_singleton_self _, pb_sub s (by unfold frameBytes privBytes; omega)⟩)
    have hb : t.gpr .r12 = fb s - BitVec.ofNat 64 privBytes := by rw [k.get .r12, h12]
    refine wp_argD P (j := n) (o := privBytes) (by omega) hb (k.rd.trans hrd) ?_ (fun t₁ o₁ e₁ => ?_)
      ⟨by unfold arg frameBytes privBytes; omega, by unfold arg frameBytes privBytes; omega⟩
    · exact Frame.mono hmt fun _ h => h
    have hw : InRegions t₁.wr (pb s + BitVec.ofNat 64 (104 + 8 * n)) 8 := by
      rw [o₁.wr, k.wr, hwr]; exact psa_in (by omega) (by unfold privBytes; omega)
    refine wp_std (a := pb s + BitVec.ofNat 64 (104 + 8 * n)) (by rw [o₁.get .r12, hb]) hw (fun t₂ m₂ => wp_nil ?_)
      (by decide) ⟨by omega, by omega⟩
    have k₂ : Keep [.r0] t₀ t₂ := (k.trans (o₁.keep.trans m₂.keep)).mono
    refine ⟨k₂, ?_, fun j hj => ?_⟩
    · rw [m₂.mem, o₁.mem]
      exact fm.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
    · rw [m₂.mem, o₁.mem]
      by_cases hj' : j < n
      · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide), got j hj']
      · rw [show j = n by omega, Mem.readW_writeW_self64, e₁]

theorem privArgs_ok {t : State} (E : Entered s t) : WP isa (.block privArgs) (allocated privBytes t) (AtPriv s) := by
  have hsp : t.sp = fb s := E.sv.sp
  have usp : (allocated privBytes t).sp = pb s := by rw [allocated_sp, hsp]
  have uwr : (allocated privBytes t).wr = ⟨pb s + BitVec.ofNat 64 32, 160⟩ :: fr s :: s.wr := by
    rw [allocated_wr, E.sv.wr, frameR, hsp]; rfl
  have urd : (allocated privBytes t).rd = s.rd := by rw [allocated_rd, E.rd]
  have um : Frame [PB s] t.mem (allocated privBytes t).mem := by
    rw [allocated_mem]
    refine (Frame.refl _ _).write (List.mem_singleton_self _) _ ?_
    rw [hsp, show fb s - BitVec.ofNat 64 privBytes = pb s + BitVec.ofNat 64 0 by rw [BitVec.add_zero]]
    exact pb_in s (by decide)
  have ug : (allocated privBytes t).gpr = t.gpr := rfl
  rw [privArgs_eq, WP.block_append_iff, WP.block_append_iff]
  refine wp_addSp fun u₁ o₁ e₁ => ?_
  rw [usp, BitVec.add_zero] at e₁
  refine wp_std (a := pb s + BitVec.ofNat 64 96) (by rw [e₁]) (by rw [o₁.wr, uwr]; exact psa_in (by decide) (by decide)) fun u₂ m₂ => wp_nil ?_
  have k₂ : Keep [.r12] (allocated privBytes t) u₂ := (o₁.keep.trans m₂.keep).mono
  have f₂ : Frame [PB s] t.mem u₂.mem := by
    rw [m₂.mem, o₁.mem]; exact um.writeW (List.mem_singleton_self _) _ (pb_in s (by decide))
  have r₂ : u₂.mem.readW (pb s + BitVec.ofNat 64 96) 64 = s.gpr .r10 := by
    rw [m₂.mem, Mem.readW_writeW_self64, o₁.get .r10, ug, E.args .r10 (by decide)]
  have hmD : ∀ {x : State}, Frame [PB s] t.mem x.mem → Frame [kD s] s.mem x.mem := fun h =>
    (toD E.mem).trans (h.sub fun r hr => ⟨kD s, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]
      have := pb_sub s (d := 0) (n := privBytes) (by decide); rwa [BitVec.add_zero] at this⟩)
  have g₂ : u₂.gpr .r12 = pb s := by rw [m₂.gpr, e₁]
  refine WP.mono (copies_ok P (t₀ := u₂) g₂ (by rw [k₂.rd, urd]) (by rw [k₂.wr, uwr]) (hmD f₂) 9 (Nat.le_refl 9))
    fun u₃ ⟨k₃, f₃, got⟩ => ?_
  have g₃ : u₃.gpr .r12 = pb s := by rw [k₃.get .r12, g₂]
  have w₃ : u₃.wr = ⟨pb s + BitVec.ofNat 64 32, 160⟩ :: fr s :: s.wr := by rw [k₃.wr, k₂.wr, uwr]
  have f₃' : Frame [PB s] t.mem u₃.mem := f₂.trans (f₃.sub fun r hr => ⟨PB s, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by decide)⟩)
  refine wp_li (by decide) fun u₄ o₄ e₄ => wp_add fun u₅ o₅ e₅ => ?_
  have g₅ : u₅.gpr .r12 = pb s := by rw [o₅.get .r12, o₄.get .r12, g₃]
  refine wp_std (a := pb s + BitVec.ofNat 64 176) (by rw [g₅]) (by rw [o₅.wr, o₄.wr, w₃]; exact psa_in (by decide) (by decide)) fun u₆ m₆ => ?_
  have f₆ : Frame [PB s] t.mem u₆.mem := by
    rw [m₆.mem, o₅.mem, o₄.mem]; exact f₃'.writeW (List.mem_singleton_self _) _ (pb_in s (by decide))
  have rd₆ : u₆.rd = s.rd := by rw [m₆.rd, o₅.rd, o₄.rd, k₃.rd, k₂.rd, urd]
  refine wp_argD P (j := 14) (o := privBytes) (by decide) (by rw [m₆.gpr, g₅]) rd₆ (hmD f₆) fun u₇ o₇ e₇ => ?_
  refine wp_subi fun u₈ o₈ e₈ => ?_
  refine wp_std (a := pb s + BitVec.ofNat 64 184) (by rw [o₈.get .r12, o₇.get .r12, m₆.gpr, g₅])
    (by rw [o₈.wr, o₇.wr, m₆.wr, o₅.wr, o₄.wr, w₃]; exact psa_in (by decide) (by decide)) fun u₉ m₉ => ?_
  have f₉ : Frame [PB s] t.mem u₉.mem := by
    rw [m₉.mem, o₈.mem, o₇.mem]; exact f₆.writeW (List.mem_singleton_self _) _ (pb_in s (by decide))
  refine wp_addi fun u₁₀ o₁₀ e₁₀ => wp_mov fun u₁₁ o₁₁ e₁₁ => wp_mov fun u₁₂ o₁₂ e₁₂ =>
    wp_mov fun u₁₃ o₁₃ e₁₃ => wp_mov fun u₁₄ o₁₄ e₁₄ => wp_mov fun u₁₅ o₁₅ e₁₅ => ?_
  have k₁₅ : Only [.r3, .r4, .r5, .r6, .r7, .r8] u₉ u₁₅ :=
    (o₁₀.trans (o₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans o₁₅))))).mono
  refine wp_argD P (j := 11) (o := privBytes) (by decide) (by rw [k₁₅.get .r12, m₉.gpr, o₈.get .r12, o₇.get .r12,
    m₆.gpr, g₅]) (by rw [k₁₅.rd, m₉.rd, o₈.rd, o₇.rd, rd₆]) (by rw [k₁₅.mem]; exact hmD f₉)
    fun u₁₆ o₁₆ e₁₆ => wp_mov fun w ow ew => wp_nil ?_
  -- What the block keeps.
  have K : Keep [.r12, .r0, .r11, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] (allocated privBytes t) w :=
    (((o₁.keep.trans m₂.keep).trans (k₃.trans ((o₄.keep.trans o₅.keep).trans
      (m₆.keep.trans (o₇.keep.trans (o₈.keep.trans (m₉.keep.trans (k₁₅.keep.trans (o₁₆.keep.trans
      ow.keep)))))))))).mono
  have kt : ∀ r ∉ [Reg.r12, .r0, .r11, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10], w.gpr r = t.gpr r :=
    fun r hr => by rw [K.gpr r hr]; rfl
  have K₉ : Keep [.r12, .r0, .r11] (allocated privBytes t) u₉ :=
    (((o₁.keep.trans m₂.keep).trans (k₃.trans ((o₄.keep.trans o₅.keep).trans
      (m₆.keep.trans (o₇.keep.trans (o₈.keep.trans m₉.keep))))))).mono
  have k9 : ∀ r ∉ [Reg.r12, .r0, .r11], u₉.gpr r = t.gpr r := fun r hr => by rw [K₉.gpr r hr]; rfl
  have hl : 1024 ≤ (stackArg s 14).toNat := by
    have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega
  have v184 : u₈.gpr .r11 = psa s 11 := by
    rw [e₈, e₇]; exact sub_ofNat hl
  have v176 : u₅.gpr .r0 = psa s 10 := by
    rw [e₅, o₄.get .r14, e₄, k₃.get .r14, m₂.gpr, o₁.get .r14, ug, E.r14]; rfl
  have wm : w.mem = (u₆.mem.writeW (pb s + BitVec.ofNat 64 184) (psa s 11)) := by
    rw [ow.mem, o₁₆.mem, k₁₅.mem, m₉.mem, o₈.mem, o₇.mem, v184]
  have m6 : u₆.mem = (u₃.mem.writeW (pb s + BitVec.ofNat 64 176) (psa s 10)) := by
    rw [m₆.mem, o₅.mem, o₄.mem, v176]
  have fw : Frame [PB s] t.mem w.mem := by rw [ow.mem, o₁₆.mem, k₁₅.mem]; exact f₉
  have sl : ∀ {d : Nat}, d + 8 ≤ frameBytes → ∀ r ∈ [PB s], Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r :=
    fun hd r hr => by
      rw [List.mem_singleton.mp hr]
      have h := Offset.disjoint_below_above (fb s) (m := privBytes) (a := 0) (l := frameBytes) (by decide)
      rw [BitVec.add_zero] at h
      exact (h.sub_right (Offset.sub_base _ hd)).symm
  -- The stack arguments.
  have sep : ∀ {a b : Nat}, a + 8 ≤ b ∨ b + 8 ≤ a → a + 8 ≤ privBytes → b + 8 ≤ privBytes →
      Mem.Sep (pb s + BitVec.ofNat 64 a) (64 / 8) (pb s + BitVec.ofNat 64 b) (64 / 8) := fun h ha hb =>
    Offset.sep _ h (by unfold privBytes at ha; omega) (by unfold privBytes at hb; omega)
  have hpsa : ∀ i < 12, w.mem.readW (pb s + BitVec.ofNat 64 (96 + 8 * i)) 64 = psa s i := by
    intro i hi
    rw [wm]
    by_cases h11 : i = 11
    · subst h11; exact Mem.readW_writeW_self64 _ _ _
    rw [Mem.readW_writeW_sep (sep (by omega) (by unfold privBytes; omega) (by decide)) (by decide), m6]
    by_cases h10 : i = 10
    · subst h10; exact Mem.readW_writeW_self64 _ _ _
    rw [Mem.readW_writeW_sep (sep (by omega) (by unfold privBytes; omega) (by decide)) (by decide)]
    by_cases h0 : i = 0
    · subst h0
      rw [f₃.readW (r := ⟨pb s + BitVec.ofNat 64 96, 8⟩) (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))
        (by decide)]
      exact r₂
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [show 96 + 8 * (j + 1) = 104 + 8 * j by omega, got j (by omega)]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  refine ⟨by rw [K.sp, usp], by rw [K.rd, urd], by rw [K.wr, uwr], hmD fw,
    E.sv.sv.frame fw fun p hp r hr => sl (by have := saved_offs p hp; unfold oLr frameBytes at *; omega) r hr,
    by rw [fw.readW (Region.contains_self _ _) (sl (by decide)) (by decide)]; exact E.sv.ls,
    fun r hr => by rw [kt r (by revert r; decide)]; exact E.sv.hi r hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [kt _ (by decide)]; exact E.r14, by rw [kt _ (by decide)]; exact E.r15,
    by rw [kt _ (by decide)]; exact E.r16, by rw [kt _ (by decide)]; exact E.r17,
    by rw [kt _ (by decide)]; exact E.r18, by rw [kt _ (by decide)]; exact E.r19,
    fun r hr => by rw [kt r (by revert r; decide)]; exact E.args r (by revert r; decide), hpsa⟩
  · rw [ow.get .r3, o₁₆.get .r3, o₁₅.get .r3, o₁₄.get .r3, o₁₃.get .r3, o₁₂.get .r3, o₁₁.get .r3, e₁₀,
      k9 .r14 (by decide), E.r14]; exact BitVec.add_zero _
  · rw [ow.get .r4, o₁₆.get .r4, o₁₅.get .r4, o₁₄.get .r4, o₁₃.get .r4, o₁₂.get .r4, e₁₁, o₁₀.get .r15,
      k9 .r15 (by decide), E.r15]
  · rw [ow.get .r5, o₁₆.get .r5, o₁₅.get .r5, o₁₄.get .r5, o₁₃.get .r5, e₁₂, o₁₁.get .r6, o₁₀.get .r6,
      k9 .r6 (by decide), E.args .r6 (by decide)]
  · rw [ow.get .r6, o₁₆.get .r6, o₁₅.get .r6, o₁₄.get .r6, e₁₃, o₁₂.get .r15, o₁₁.get .r15, o₁₀.get .r15,
      k9 .r15 (by decide), E.r15]
  · rw [ow.get .r7, o₁₆.get .r7, o₁₅.get .r7, e₁₄, o₁₃.get .r8, o₁₂.get .r8, o₁₁.get .r8, o₁₀.get .r8,
      k9 .r8 (by decide), E.args .r8 (by decide)]
  · rw [ow.get .r8, o₁₆.get .r8, e₁₅, o₁₄.get .r9, o₁₃.get .r9, o₁₂.get .r9, o₁₁.get .r9, o₁₀.get .r9,
      k9 .r9 (by decide), E.args .r9 (by decide)]
  · rw [ow.get .r9]; exact e₁₆
  · rw [ew, o₁₆.get .r15, k₁₅.get .r15, k9 .r15 (by decide), E.r15]

end

end VG.Proof.RsaOaep.PPC64LE.Dec
