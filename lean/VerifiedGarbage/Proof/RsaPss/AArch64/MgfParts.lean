import VerifiedGarbage.Proof.RsaPss.AArch64.CtHash

/-!
# RSASSA-PSS on AArch64: the steps of MGF1

One counter of `mgfXor`: `Y`'s first `mgfNb` blocks cleared (`clearBlock_ok`),
`H` copied to `Y` (`copyH_ok`), the counter after it (`counter_ok`), and,
after `mgfHash`, the digest XORed into `DB` (`xorOut_ok`) and the next
counter (`nextCtr_ok`).
-/

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_addImm wp_subImm wp_eor wp_lsr wp_ldrb wp_strb
  wp_strx wp_add wp_sub eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp wp_addSp wp_countdown wp_mov setWidth_ofNat16 copy_ok ofNat_succ'
  ite_both)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)

/-! ## Clearing -/

/-- `V` with `n` bytes cleared from `o`. -/
def clr (V : Nat → Byte) (o n : Nat) : Nat → Byte := fun x => if o ≤ x ∧ x < o + n then 0 else V x

theorem clr_zero (V : Nat → Byte) (o : Nat) : clr V o 0 = V := by
  funext x; simp only [clr]; rw [ite_eq_right (by omega)]

theorem Rep.wz {m : Mem} {S : Addr} {V : Nat → Byte} (h : Rep m S V) {o : Nat} (ho : o + 8 ≤ oRsa) :
    Rep (m.writeW (off S o) (0#64)) S (clr V o 8) := by
  have e : m.writeW (off S o) (0#64) = VG.WriteBytes.writeBytes m (off S o) (List.replicate 8 0) := by
    rw [Mem.writeW, write_eq_writeBytes]; rfl
  rw [e]
  refine (h.writeBytes (by simp only [List.length_replicate]; omega)).congr fun x _ => ?_
  simp only [updL, clr, List.length_replicate]
  by_cases hx : o ≤ x ∧ x < o + 8
  · rw [ite_eq_left hx, ite_eq_left hx, List.getD_eq_getElem?_getD, List.getElem?_replicate,
      ite_eq_left (by omega)]
    rfl
  · rw [ite_eq_right hx, ite_eq_right hx]

/-- `n` words of zeros from `x10 = scratch + o`, counted down in `x12`. -/
theorem clearQ_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V) {o n : Nat}
    (hn : 0 < n) (ho : o + 8 * n ≤ oRsa) (h10 : t.gpr .x10 = off S o) (h9 : t.gpr .x9 = 0#64)
    (h12 : t.gpr .x12 = BitVec.ofNat 64 n) :
    WP isa (.loop (.block [.str .x .x9 .x10 0, .addImm .x .x10 .x10 8, .subImm .x .x12 .x12 1])
      (.nonzero .x .x12)) t fun t' => Keep [.x10, .x12] t t' ∧ Frame [⟨S, oRsa⟩] t.mem t'.mem ∧
        Rep t'.mem S (clr V o (8 * n)) := by
  have c6 : oRsa = 8192 := rfl
  refine WP.mono (wp_countdown (cnt := .x12) (by omega) hn (fun j u => Keep [.x10, .x12] t u ∧
      u.gpr .x10 = off S (o + 8 * j) ∧ Frame [⟨S, oRsa⟩] t.mem u.mem ∧ Rep u.mem S (clr V o (8 * j)))
    (fun j hj u ⟨hK, h10', hF, hR⟩ _ => ?_)
    ⟨Keep.refl _ _, by rw [h10, Nat.mul_zero, Nat.add_zero], Frame.refl _ _, by rw [Nat.mul_zero, clr_zero]; exact R⟩
    h12) fun u h => ⟨h.1, h.2.2⟩
  have hj8 : o + 8 * j + 8 ≤ oRsa := by omega
  refine wp_strx (by decide) (by rw [h10', BitVec.add_zero]) (by rw [hK.wr]; exact L.st hj8) fun u₁ m₁ => ?_
  refine wp_addImm (by decide) fun u₂ o₂ e₂ => wp_subImm (by decide) fun u₃ o₃ e₃ => wp_nil ?_
  have hm : u₃.mem = u.mem.writeW (off S (o + 8 * j)) (0#64) := by
    rw [o₃.mem, o₂.mem, m₁.mem, hK.get .x9, h9]
  refine ⟨⟨(hK.trans (m₁.keep.trans (o₂.keep.trans o₃.keep))).mono, ?_, ?_, ?_⟩, ?_⟩
  · rw [o₃.get .x10, e₂, m₁.gpr, h10', off_add, Nat.mul_succ, Nat.add_assoc]
  · rw [hm]
    exact hF.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [hm]
    refine (hR.wz hj8).congr fun x _ => ?_
    simp only [clr]
    by_cases h₁ : o + 8 * j ≤ x ∧ x < o + 8 * j + 8
    · rw [ite_eq_left h₁, ite_eq_left (by rw [Nat.mul_succ]; omega)]
    · rw [ite_eq_right h₁]
      by_cases h₂ : o ≤ x ∧ x < o + 8 * j
      · rw [ite_eq_left h₂, ite_eq_left (by rw [Nat.mul_succ]; omega)]
      · rw [ite_eq_right h₂, ite_eq_right (by rw [Nat.mul_succ]; omega)]
  · rw [e₃, o₂.get .x12, m₁.gpr]

section
variable {H : Hash} (hH : HashOK H)

include hH in
theorem mgfNb_spec : H.D + 4 + 1 + H.P.L ≤ mgfNb H * H.P.B ∧ mgfNb H * H.P.B ≤ 256 ∧
    mgfNb H * H.P.B % 8 = 0 := by
  have hB := hH.sizes.B
  have hpad := hH.sizes.pad
  unfold mgfNb
  have hB0 : 0 < H.P.B := by omega
  have := Nat.lt_div_mul_add (a := H.D + 4 + H.P.L) (b := H.P.B) hB0
  have h1 : (H.D + 4 + H.P.L) / H.P.B ≤ 1 := Nat.div_le_of_le_mul (by omega)
  generalize (H.D + 4 + H.P.L) / H.P.B = q at this h1
  have hq : q = 0 ∨ q = 1 := by omega
  rcases hq with rfl | rfl <;> rcases hB with h | h <;> rw [h] at this ⊢ <;> omega

include hH in
theorem clearBlock_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V) :
    WP isa (clearBlock H) t fun t' => Keep [.x10, .x9, .x12] t t' ∧ Frame [⟨S, oRsa⟩] t.mem t'.mem ∧
      Rep t'.mem S (clr V oY (mgfNb H * H.P.B)) := by
  obtain ⟨_, hnb, h8⟩ := mgfNb_spec hH
  have hpos : 0 < mgfNb H * H.P.B := Nat.mul_pos (Nat.succ_pos _) hH.B_pos
  have e8 : 8 * (mgfNb H * H.P.B / 8) = mgfNb H * H.P.B := by omega
  unfold clearBlock
  refine WP.seq (WP.mono (wp_addImm (by decide) fun u₁ o₁ e₁ => wp_movz fun u₂ o₂ e₂ => wp_movz fun u₃ o₃ e₃ =>
    wp_nil (Q := fun u => Only [.x10, .x9, .x12] t u ∧ u.gpr .x10 = off S oY ∧ u.gpr .x9 = 0#64 ∧
      u.gpr .x12 = BitVec.ofNat 64 (mgfNb H * H.P.B / 8))
      ⟨(o₁.trans (o₂.trans o₃)).mono, by rw [o₃.get .x10, o₂.get .x10, e₁, L.x20],
        by rw [o₃.get .x9, e₂]; rfl, by rw [e₃, setWidth_ofNat16 (by omega)]⟩) fun u ⟨O, h10, h9, h12⟩ => ?_)
  refine WP.mono (clearQ_ok (L.congr O.sp O.wr (O.get .x20)) (O.mem ▸ R) (by omega)
    (by rw [e8]; unfold oY oRsa; omega) h10 h9 h12) fun v ⟨k, f, r⟩ => ⟨(O.keep.trans k).mono, O.mem ▸ f, ?_⟩
  rw [e8] at r; exact r

/-- Where `DB` and `H` are: `DB` the `db` bytes at `scratch + e`, `H` the
`hLen` after them, within `EM`'s place. -/
structure DbAt (D e db : Nat) : Prop where
  e1 : oEm ≤ e
  db1 : 1 ≤ db
  fit : e + db + D ≤ oY

include hH in
theorem copyH_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V) {e db : Nat}
    (hd : DbAt H.D e db) (h24 : t.gpr .x24 = off S e) (h25 : t.gpr .x25 = BitVec.ofNat 64 db) :
    WP isa (copyH H) t fun t' => Keep [.x11, .x14, .x12, .x15] t t' ∧ Frame [⟨S, oRsa⟩] t.mem t'.mem ∧
      Rep t'.mem S (updL V oY ((List.range H.D).map fun i => V (e + db + i))) := by
  have hD := hH.sizes.D0
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  have hfit := hd.fit
  have he1 := hd.e1
  have c1 : oY = 3584 := rfl
  have c6 : oRsa = 8192 := rfl
  have c7 : oEm = 2560 := rfl
  unfold copyH
  refine WP.seq (WP.mono (wp_add fun u₁ o₁ e₁ => wp_addImm (by decide) fun u₂ o₂ e₂ => wp_movz fun u₃ o₃ e₃ =>
    wp_nil (Q := fun u => Only [.x11, .x14, .x12] t u ∧ u.gpr .x11 = off S (e + db) ∧ u.gpr .x14 = off S oY ∧
      u.gpr .x12 = BitVec.ofNat 64 H.D)
      ⟨(o₁.trans (o₂.trans o₃)).mono, by rw [o₃.get .x11, o₂.get .x11, e₁, h24, h25, off_add],
        by rw [o₃.get .x14, e₂, o₁.get .x20, L.x20], by rw [e₃, setWidth_ofNat16 (by omega)]⟩)
      fun u ⟨O, h11, h14, h12⟩ => ?_)
  have Lu := L.congr O.sp O.wr (O.get .x20)
  have Ru : Rep u.mem S V := O.mem ▸ R
  refine WP.mono (copy_ok hD (by omega) h14 h11 h12 (fun j hj => by rw [off_add]; exact Lu.ld (by omega))
    (fun i hi => by rw [off_add]; exact Lu.st (by omega))
    (fun j hj i hi h => by rw [off_add, off_add, off_inj S (by omega) (by omega)] at h; omega))
    fun v ⟨k, hm⟩ => ⟨(O.keep.trans k).mono, ?_, ?_⟩
  · rw [hm, Ru.bytes (by omega), ← O.mem]
    exact writeBytes_frame _ _ _ (Offset.contains_base S
      (by simp only [List.length_map, List.length_range]; omega) (by omega))
  · rw [hm, Ru.bytes (by omega)]
    exact Ru.writeBytes (by simp only [List.length_map, List.length_range]; omega)

/-- A slot of the frame. -/
abbrev slotR (F : Addr) (d : Nat) : Region := ⟨off F d, 8⟩

theorem frame_slot (m : Mem) (F : Addr) (d : Nat) (v : BitVec 64) :
    Frame [slotR F d] m (m.writeW (off F d) v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem Lay.slotS {t : State} {F S : Addr} (L : Lay t F S) {d : Nat} (h : d + 8 ≤ frameBytes) :
    ∀ r ∈ [slotR F d], Region.Disjoint ⟨S, oRsa⟩ r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact (L.dFS.sub_left (Offset.sub_base F h)).symm

/-- `Y` with the counter `c` after `H`. -/
def ctrV (D : Nat) (V : Nat → Byte) (c : Nat) (x : Nat) : Byte :=
  if oY + D ≤ x ∧ x < oY + D + 4 then (Spec.Rsa.i2osp c 4).getD (x - (oY + D)) 0 else V x

theorem byte_shr {c : Nat} (k : Nat) (hc : c < 2 ^ 64) :
    ((BitVec.ofNat 64 c) >>> k).setWidth 8 = BitVec.ofNat 8 (c / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hc]

include hH in
theorem counter_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V) {c : Nat}
    (h28 : t.gpr .x28 = BitVec.ofNat 64 c) (hc : c < 2 ^ 32) :
    WP isa (.block (counter H)) t fun t' => Keep [.x10, .x9, .x22, .x16] t t' ∧
      t'.gpr .x22 = BitVec.ofNat 64 (H.D + 4) ∧ t'.mem.readW (off F sNb) 64 = BitVec.ofNat 64 (mgfNb H) ∧
      Frame [⟨S, oRsa⟩, slotR F sNb] t.mem t'.mem ∧ Rep t'.mem S (ctrV H.D V c) := by
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  obtain ⟨_, hnb, _⟩ := mgfNb_spec hH
  have hmg : mgfNb H ≤ 256 := Nat.le_trans (Nat.le_mul_of_pos_right _ hH.B_pos) hnb
  have c1 : oY = 3584 := rfl
  have c6 : oRsa = 8192 := rfl
  unfold counter st
  simp only [List.cons_append, List.nil_append]
  refine wp_addImm (by omega) fun u₁ o₁ e₁ => wp_lsr (by decide) fun u₂ o₂ e₂ => ?_
  have a₂ : u₂.gpr .x10 = off S (oY + H.D) := by rw [o₂.get .x10, e₁, L.x20]
  have w₂ : u₂.wr = t.wr := by rw [o₂.wr, o₁.wr]
  refine wp_strb (by decide) (by rw [a₂, BitVec.add_zero]) (by rw [w₂]; exact L.st (by omega)) fun u₃ m₃ => ?_
  refine wp_lsr (by decide) fun u₄ o₄ e₄ => ?_
  refine wp_strb (by decide) (by rw [o₄.get .x10, m₃.gpr, a₂, off_add])
    (by rw [o₄.wr, m₃.wr, w₂]; exact L.st (by omega)) fun u₅ m₅ => ?_
  refine wp_lsr (by decide) fun u₆ o₆ e₆ => ?_
  refine wp_strb (by decide) (by rw [o₆.get .x10, m₅.gpr, o₄.get .x10, m₃.gpr, a₂, off_add])
    (by rw [o₆.wr, m₅.wr, o₄.wr, m₃.wr, w₂]; exact L.st (by omega)) fun u₇ m₇ => ?_
  refine wp_strb (by decide) (by rw [m₇.gpr, o₆.get .x10, m₅.gpr, o₄.get .x10, m₃.gpr, a₂, off_add])
    (by rw [m₇.wr, o₆.wr, m₅.wr, o₄.wr, m₃.wr, w₂]; exact L.st (by omega)) fun u₈ m₈ => ?_
  refine wp_movz fun u₉ o₉ e₉ => wp_movz fun u₁₀ o₁₀ e₁₀ => wp_addSp (by decide) fun u₁₁ o₁₁ e₁₁ => ?_
  have sp₁₁ : u₁₀.sp = F := by
    rw [o₁₀.sp, o₉.sp, m₈.sp, m₇.sp, o₆.sp, m₅.sp, o₄.sp, m₃.sp, o₂.sp, o₁.sp, L.sp]
  have wr₁₁ : u₁₁.wr = t.wr := by rw [o₁₁.wr, o₁₀.wr, o₉.wr, m₈.wr, m₇.wr, o₆.wr, m₅.wr, o₄.wr, m₃.wr, w₂]
  refine wp_strx (by decide) (by rw [e₁₁, sp₁₁, BitVec.add_zero]) (by rw [wr₁₁]; exact L.fst (by decide))
    fun u₁₂ m₁₂ => wp_nil ?_
  have x28 : ∀ k, k < 64 → ((t.gpr .x28) >>> k).setWidth 8 = BitVec.ofNat 8 (c / 2 ^ k) := fun k _ => by
    rw [h28]; exact byte_shr k (by omega)
  have b0 : (u₂.gpr .x9).setWidth 8 = BitVec.ofNat 8 (c / 2 ^ 24) := by
    rw [e₂, o₁.get .x28]; exact x28 24 (by decide)
  have b1 : (u₄.gpr .x9).setWidth 8 = BitVec.ofNat 8 (c / 2 ^ 16) := by
    rw [e₄, m₃.gpr, o₂.get .x28, o₁.get .x28]; exact x28 16 (by decide)
  have b2 : (u₆.gpr .x9).setWidth 8 = BitVec.ofNat 8 (c / 2 ^ 8) := by
    rw [e₆, m₅.gpr, o₄.get .x28, m₃.gpr, o₂.get .x28, o₁.get .x28]; exact x28 8 (by decide)
  have b3 : (u₇.gpr .x28).setWidth 8 = BitVec.ofNat 8 c := by
    rw [m₇.gpr, o₆.get .x28, m₅.gpr, o₄.get .x28, m₃.gpr, o₂.get .x28, o₁.get .x28]
    have := x28 0 (by decide)
    rwa [BitVec.ushiftRight_zero, Nat.pow_zero, Nat.div_one] at this
  have hm₈ : u₈.mem = (((t.mem.writeW (off S (oY + H.D)) (BitVec.ofNat 8 (c / 2 ^ 24))).writeW
      (off S (oY + H.D + 1)) (BitVec.ofNat 8 (c / 2 ^ 16))).writeW (off S (oY + H.D + 2))
      (BitVec.ofNat 8 (c / 2 ^ 8))).writeW (off S (oY + H.D + 3)) (BitVec.ofNat 8 c) := by
    rw [m₈.mem, m₇.mem, o₆.mem, m₅.mem, o₄.mem, m₃.mem, o₂.mem, o₁.mem, b0, b1, b2, b3]
  have R₈ := (((R.wb (o := oY + H.D) (by omega) (BitVec.ofNat 8 (c / 2 ^ 24))).wb (o := oY + H.D + 1) (by omega)
    (BitVec.ofNat 8 (c / 2 ^ 16))).wb (o := oY + H.D + 2) (by omega) (BitVec.ofNat 8 (c / 2 ^ 8))).wb
    (o := oY + H.D + 3) (by omega) (BitVec.ofNat 8 c)
  rw [← hm₈] at R₈
  have hm₁₂ : u₁₂.mem = u₈.mem.writeW (off F sNb) (BitVec.ofNat 64 (mgfNb H)) := by
    rw [m₁₂.mem, o₁₁.mem, o₁₀.mem, o₉.mem, o₁₁.get .x9, e₁₀, setWidth_ofNat16 (by omega)]
  have F₈ : Frame [⟨S, oRsa⟩] t.mem u₈.mem := by
    rw [hm₈]
    refine (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
      |>.writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_ <;>
    exact Offset.contains_base S (by omega) (by omega)
  refine ⟨(((o₁.keep.trans (o₂.keep.trans (m₃.keep.trans (o₄.keep.trans (m₅.keep.trans (o₆.keep.trans
    (m₇.keep.trans (m₈.keep.trans (o₉.keep.trans (o₁₀.keep.trans (o₁₁.keep.trans m₁₂.keep)))))))))))).mono),
    ?_, ?_, ?_, ?_⟩
  · rw [m₁₂.gpr, o₁₁.get .x22, o₁₀.get .x22, e₉, setWidth_ofNat16 (by omega)]
  · rw [hm₁₂, Mem.readW_writeW_self64]
  · rw [hm₁₂]
    exact (F₈.mono (by simp)).trans ((frame_slot _ F sNb _).mono (by simp))
  · rw [hm₁₂]
    refine (R₈.frame (frame_slot _ F sNb _) (L.slotS (by decide))).congr fun x _ => ?_
    simp only [upd, ctrV]
    rcases (show x = oY + H.D ∨ x = oY + H.D + 1 ∨ x = oY + H.D + 2 ∨ x = oY + H.D + 3 ∨
        ¬(oY + H.D ≤ x ∧ x < oY + H.D + 4) by omega) with h | h | h | h | h
    · subst h; simp [Spec.Rsa.i2osp]
    · subst h; simp [Spec.Rsa.i2osp]
    · subst h; simp [Spec.Rsa.i2osp]
    · subst h; simp [Spec.Rsa.i2osp]
    · rw [ite_eq_right h, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]

/-! ## The digest into `DB` -/

/-- `V` with the `n` bytes from `a` XORed into those from `b`. -/
def xorV (V : Nat → Byte) (a b n : Nat) (x : Nat) : Byte :=
  if b ≤ x ∧ x < b + n then V x ^^^ V (a + (x - b)) else V x

theorem xorV_zero (V : Nat → Byte) (a b : Nat) : xorV V a b 0 = V := by
  funext x; simp only [xorV]; rw [ite_eq_right (by omega)]

theorem byte_xor (a b : Byte) : (BitVec.setWidth 64 a ^^^ BitVec.setWidth 64 b).setWidth 8 = a ^^^ b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_xor]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by omega), Nat.mod_eq_of_lt (a := b.toNat) (by omega),
    Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (by omega) (by omega))]

theorem borrow_beq {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    ((BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 == 0) = !decide (a < b) := by
  rw [← VG.Proof.RsaPkcs1Sig.AArch64.borrow_ne ha hb]
  simp only [bne, Bool.not_not]

include hH in
theorem xorOut_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V)
    {e db done : Nat} (hd : DbAt H.D e db) (h24 : t.gpr .x24 = off S e) (h25 : t.gpr .x25 = BitVec.ofNat 64 db)
    (h21 : t.gpr .x21 = off S oDig) (hdn : t.mem.readW (off F sDone) 64 = BitVec.ofNat 64 done)
    (hlt : done < db) :
    WP isa (xorOut H) t fun t' => Keep [.x9, .x10, .x11, .x12, .x13, .x14, .x15] t t' ∧
      Frame [⟨S, oRsa⟩] t.mem t'.mem ∧ Rep t'.mem S (xorV V oDig (e + done) (min H.D (db - done))) := by
  have hD := hH.sizes.D0
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  have hfit := hd.fit
  have he1 := hd.e1
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have c3 : oDig = 2304 := rfl
  have c6 : oRsa = 8192 := rfl
  unfold xorOut seqs seqs seqs
  refine WP.seq (WP.mono (wp_ldrSp (by decide) (by rw [L.sp]; exact L.fld (by decide)) fun u₁ o₁ e₁ =>
    wp_add fun u₂ o₂ e₂ => wp_mov fun u₃ o₃ e₃ => wp_sub fun u₄ o₄ e₄ => wp_movz fun u₅ o₅ e₅ =>
    wp_sub fun u₆ o₆ e₆ => wp_lsr (by decide) fun u₇ o₇ e₇ =>
    wp_nil (Q := fun v => Only [.x9, .x10, .x11, .x12, .x13, .x14] t v ∧ v.gpr .x10 = off S (e + done) ∧
      v.gpr .x11 = off S oDig ∧ v.gpr .x12 = BitVec.ofNat 64 (db - done) ∧
      v.gpr .x13 = BitVec.ofNat 64 H.D ∧
      v.gpr .x14 = (BitVec.ofNat 64 (db - done) - BitVec.ofNat 64 H.D) >>> 63)
    ⟨(o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))))).mono, ?_, ?_, ?_, ?_, ?_⟩)
    fun v ⟨O, h10, h11, h12, h13, h14⟩ => ?_)
  · rw [o₇.get .x10, o₆.get .x10, o₅.get .x10, o₄.get .x10, o₃.get .x10, e₂, o₁.get .x24, h24, e₁, L.sp, hdn,
      off_add]
  · rw [o₇.get .x11, o₆.get .x11, o₅.get .x11, o₄.get .x11, e₃, o₂.get .x21, o₁.get .x21, h21]
  · rw [o₇.get .x12, o₆.get .x12, o₅.get .x12, e₄, o₃.get .x25, o₂.get .x25, o₁.get .x25, h25, o₃.get .x9,
      o₂.get .x9, e₁, L.sp, hdn, Offset.ofNat_sub_ofNat (by omega)]
  · rw [o₇.get .x13, o₆.get .x13, e₅, setWidth_ofNat16 (by omega)]
  · rw [e₇, e₆, o₅.get .x12, e₅, setWidth_ofNat16 (by omega), e₄, o₃.get .x25, o₂.get .x25, o₁.get .x25, h25,
      o₃.get .x9, o₂.get .x9, e₁, L.sp, hdn, Offset.ofNat_sub_ofNat (by omega)]
  -- The count, `min(hLen, dbLen - done)`.
  refine WP.seq (WP.mono (Q := fun (w : State) => Keep [.x12] v w ∧ w.mem = v.mem ∧
      w.gpr .x12 = BitVec.ofNat 64 (min H.D (db - done))) ?_ fun w ⟨kw, hmw, h12w⟩ => ?_)
  · have hb := borrow_beq (a := db - done) (b := H.D) (by omega) (by omega)
    rw [← h14] at hb
    refine WP.ite _ (eval_zero _ _) (fun h => ?_) (fun h => ?_)
    · rw [hb, Bool.not_eq_true', decide_eq_false_iff_not] at h
      exact wp_mov fun w o e' => wp_nil ⟨o.keep, o.mem, by rw [e', h13, Nat.min_eq_left (by omega)]⟩
    · rw [hb, Bool.not_eq_false', decide_eq_true_eq] at h
      exact wp_nil ⟨Keep.refl _ _, rfl, by rw [h12, Nat.min_eq_right (by omega)]⟩
  have K : Keep [.x9, .x10, .x11, .x12, .x13, .x14] t w := (O.keep.trans kw).mono
  have Lw : Lay w F S := L.congr K.sp K.wr (K.get .x20)
  have Rw : Rep w.mem S V := by rw [hmw, O.mem]; exact R
  have hn : 0 < min H.D (db - done) := by omega
  refine WP.mono (wp_countdown (cnt := .x12) (by omega) hn (fun j u => Keep [.x9, .x15, .x10, .x11, .x12] w u ∧
      u.gpr .x10 = off S (e + done + j) ∧ u.gpr .x11 = off S (oDig + j) ∧ Frame [⟨S, oRsa⟩] w.mem u.mem ∧
      Rep u.mem S (xorV V oDig (e + done) j))
    (fun j hj u ⟨hK, h10', h11', hF, hR⟩ _ => ?_)
    ⟨Keep.refl _ _, by rw [kw.get .x10, h10, Nat.add_zero], by rw [kw.get .x11, h11, Nat.add_zero],
      Frame.refl _ _, by rw [xorV_zero]; exact Rw⟩ h12w)
    fun u ⟨hK, _, _, hF, hR⟩ => ⟨(K.trans hK).mono, by rw [hmw, O.mem] at hF; exact hF, hR⟩
  have hj := Nat.lt_min.mp hj
  refine wp_ldrb (by decide) (by rw [h11', BitVec.add_zero]) (by rw [hK.rd, hK.wr]; exact Lw.ld (by omega))
    fun u₁ o₁ e₁ => ?_
  refine wp_ldrb (by decide) (by rw [o₁.get .x10, h10', BitVec.add_zero])
    (by rw [o₁.rd, o₁.wr, hK.rd, hK.wr]; exact Lw.ld (by omega)) fun u₂ o₂ e₂ => wp_eor fun u₃ o₃ e₃ => ?_
  have O₃ : Only [.x9, .x15] u u₃ := (o₁.trans (o₂.trans o₃)).mono
  refine wp_strb (by decide) (by rw [O₃.get .x10, h10', BitVec.add_zero]) (by rw [O₃.wr, hK.wr]; exact Lw.st (by omega))
    fun u₄ m₄ => wp_addImm (by decide) fun u₅ o₅ e₅ => wp_addImm (by decide) fun u₆ o₆ e₆ =>
    wp_subImm (by decide) fun u₇ o₇ e₇ => wp_nil ?_
  have hv : (u₃.gpr .x15).setWidth 8 = V (e + done + j) ^^^ V (oDig + j) := by
    rw [e₃, o₂.get .x9, e₁, e₂, o₁.mem, hR _ (by omega), hR _ (by omega), byte_xor]
    simp only [xorV]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have hm : u₇.mem = u.mem.writeW (off S (e + done + j)) (V (e + done + j) ^^^ V (oDig + j)) := by
    rw [o₇.mem, o₆.mem, o₅.mem, m₄.mem, O₃.mem, hv]
  refine ⟨⟨(hK.trans (O₃.keep.trans (m₄.keep.trans (o₅.keep.trans (o₆.keep.trans o₇.keep))))).mono, ?_, ?_, ?_,
    ?_⟩, ?_⟩
  · rw [o₇.get .x10, e₆, o₅.get .x10, m₄.gpr, O₃.get .x10, h10', off_add, Nat.add_assoc]
  · rw [o₇.get .x11, o₆.get .x11, e₅, m₄.gpr, O₃.get .x11, h11', off_add, Nat.add_assoc]
  · rw [hm]
    exact hF.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [hm]
    refine (hR.wb (by omega) _).congr fun x _ => ?_
    simp only [upd, xorV]
    by_cases h₁ : x = e + done + j
    · subst h₁
      rw [ite_eq_left rfl, ite_eq_left ⟨by omega, by omega⟩, show e + done + j - (e + done) = j by omega]
    · rw [ite_eq_right h₁]
      by_cases h₂ : e + done ≤ x ∧ x < e + done + j
      · rw [ite_eq_left h₂, ite_eq_left ⟨h₂.1, by omega⟩]
      · rw [ite_eq_right h₂, ite_eq_right (by omega)]
  · rw [e₇, o₆.get .x12, o₅.get .x12, m₄.gpr, O₃.get .x12]

/-! ## The next counter -/

include hH in
theorem nextCtr_ok {t : State} {F S : Addr} (L : Lay t F S) {c done db : Nat}
    (h28 : t.gpr .x28 = BitVec.ofNat 64 c) (h25 : t.gpr .x25 = BitVec.ofNat 64 db)
    (hdn : t.mem.readW (off F sDone) 64 = BitVec.ofNat 64 done) (hd' : done + H.D < 2 ^ 62)
    (hdb' : db < 2 ^ 62) :
    WP isa (.block (nextCtr H)) t fun t' => Keep [.x28, .x9, .x16, .x10] t t' ∧
      t'.gpr .x28 = BitVec.ofNat 64 (c + 1) ∧ (t'.gpr .x10 != 0) = decide (done + H.D < db) ∧
      t'.mem = t.mem.writeW (off F sDone) (BitVec.ofNat 64 (done + H.D)) := by
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  unfold nextCtr st
  simp only [List.cons_append, List.nil_append]
  refine wp_addImm (by decide) fun u₁ o₁ e₁ => wp_ldrSp (by decide)
    (by rw [o₁.sp, o₁.rd, o₁.wr, L.sp]; exact L.fld (by decide)) fun u₂ o₂ e₂ => ?_
  refine wp_addImm (by omega) fun u₃ o₃ e₃ => wp_addSp (by decide) fun u₄ o₄ e₄ => ?_
  have hsp : u₃.sp = F := by rw [o₃.sp, o₂.sp, o₁.sp, L.sp]
  refine wp_strx (by decide) (by rw [e₄, hsp, BitVec.add_zero])
    (by rw [o₄.wr, o₃.wr, o₂.wr, o₁.wr]; exact L.fst (by decide)) fun u₅ m₅ => ?_
  refine wp_sub fun u₆ o₆ e₆ => wp_lsr (by decide) fun u₇ o₇ e₇ => wp_nil ?_
  have h9 : u₄.gpr .x9 = BitVec.ofNat 64 (done + H.D) := by
    rw [o₄.get .x9, e₃, e₂, o₁.mem, o₁.sp, L.sp, hdn, BitVec.ofNat_add_ofNat]
  refine ⟨(o₁.keep.trans (o₂.keep.trans (o₃.keep.trans (o₄.keep.trans (m₅.keep.trans
    (o₆.keep.trans o₇.keep)))))).mono, ?_, ?_, ?_⟩
  · rw [o₇.get .x28, o₆.get .x28, m₅.gpr, o₄.get .x28, o₃.get .x28, o₂.get .x28, e₁, h28,
      BitVec.ofNat_add_ofNat]
  · rw [e₇, e₆, m₅.gpr, h9, o₄.get .x25, o₃.get .x25, o₂.get .x25, o₁.get .x25, h25]
    exact VG.Proof.RsaPkcs1Sig.AArch64.borrow_ne (by omega) (by omega)
  · rw [o₇.mem, o₆.mem, m₅.mem, h9, o₄.mem, o₃.mem, o₂.mem, o₁.mem]

end

end VG.Proof.RsaPss.AArch64
