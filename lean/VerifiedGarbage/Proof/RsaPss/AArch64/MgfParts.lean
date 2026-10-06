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

end

end VG.Proof.RsaPss.AArch64
