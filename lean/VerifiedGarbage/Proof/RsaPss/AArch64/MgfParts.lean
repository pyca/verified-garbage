module

public import VerifiedGarbage.Proof.RsaPss.AArch64.CtHash
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Encode

/-!
# RSASSA-PSS on AArch64: the steps of MGF1

One counter of `mgfXor`: `Y`'s first `mgfNb` blocks cleared (`clearBlock_ok`),
`H` copied to `Y` (`copyH_ok`), the counter after it (`counter_ok`), and,
after `mgfHash`, the digest XORed into `DB` (`xorOut_ok`) and the next
counter (`nextCtr_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_addImm wp_subImm wp_eor wp_lsr wp_ldrb wp_strb
  wp_strx wp_add wp_sub wp_lsl eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp wp_addSp wp_countdown wp_mov setWidth_ofNat16 copy_ok ofNat_succ'
  ite_both)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)

/-! ## Clearing -/

/-- `V` with `n` bytes cleared from `o`. -/
def clr (V : Nat → Byte) (o n : Nat) : Nat → Byte := fun x => if o ≤ x ∧ x < o + n then 0 else V x

theorem clr_zero (V : Nat → Byte) (o : Nat) : clr V o 0 = V := by
  funext x; simp only [clr]; rw [ite_eq_right (by omega_using [])]

theorem Rep.wz {m : Mem} {S : Addr} {V : Nat → Byte} (h : Rep m S V) {o : Nat} (ho : o + 8 ≤ oRsa) :
    Rep (m.writeW (off S o) (0#64)) S (clr V o 8) := by
  have e : m.writeW (off S o) (0#64) = VG.WriteBytes.writeBytes m (off S o) (List.replicate 8 0) := by
    rw [Mem.writeW, write_eq_writeBytes]; rfl
  rw [e]
  refine (h.writeBytes (by simp only [List.length_replicate]; omega_using [ho])).congr fun x _ => ?_
  simp only [updL, clr, List.length_replicate]
  by_cases hx : o ≤ x ∧ x < o + 8
  · rw [ite_eq_left hx, ite_eq_left hx, List.getD_eq_getElem?_getD, List.getElem?_replicate,
      ite_eq_left (by omega_using [hx])]
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
  refine WP.mono (wp_countdown (cnt := .x12) (by omega_using [ho, c6]) hn (fun j u => Keep [.x10, .x12] t u ∧
      u.gpr .x10 = off S (o + 8 * j) ∧ Frame [⟨S, oRsa⟩] t.mem u.mem ∧ Rep u.mem S (clr V o (8 * j)))
    (fun j hj u ⟨hK, h10', hF, hR⟩ _ => ?_)
    ⟨Keep.refl _ _, by rw [h10, Nat.mul_zero, Nat.add_zero], Frame.refl _ _, by rw [Nat.mul_zero, clr_zero]; exact R⟩
    h12) fun u h => ⟨h.1, h.2.2⟩
  have hj8 : o + 8 * j + 8 ≤ oRsa := by omega_using [ho, hj]
  refine wp_strx (by decide) (by rw [h10', BitVec.add_zero]) (by rw [hK.wr]; exact L.st hj8) fun u₁ m₁ => ?_
  refine wp_addImm (by decide) fun u₂ o₂ e₂ => wp_subImm (by decide) fun u₃ o₃ e₃ => wp_nil ?_
  have hm : u₃.mem = u.mem.writeW (off S (o + 8 * j)) (0#64) := by
    rw [o₃.mem, o₂.mem, m₁.mem, hK.get .x9, h9]
  refine ⟨⟨(hK.trans (m₁.keep.trans (o₂.keep.trans o₃.keep))).mono, ?_, ?_, ?_⟩, ?_⟩
  · rw [o₃.get .x10, e₂, m₁.gpr, h10', off_add, Nat.mul_succ, Nat.add_assoc]
  · rw [hm]
    exact hF.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hj8]) (by omega_using [c6, hj8]))
  · rw [hm]
    refine (hR.wz hj8).congr fun x _ => ?_
    simp only [clr]
    by_cases h₁ : o + 8 * j ≤ x ∧ x < o + 8 * j + 8
    · rw [ite_eq_left h₁, ite_eq_left (by rw [Nat.mul_succ]; omega_using [h₁])]
    · rw [ite_eq_right h₁]
      by_cases h₂ : o ≤ x ∧ x < o + 8 * j
      · rw [ite_eq_left h₂, ite_eq_left (by rw [Nat.mul_succ]; omega_using [h₂])]
      · rw [ite_eq_right h₂, ite_eq_right (by rw [Nat.mul_succ]; omega_using [h₁, h₂])]
  · rw [e₃, o₂.get .x12, m₁.gpr]

section
variable {H : Hash} (hH : HashOK H)

/-- The blocks MGF1 hashes `H ‖ C` in, for a seed `H` of `sd` bytes:
`⌊(sd + 4 + L) / B⌋ + 1`. -/
def nbOf (H : Hash) (sd : Nat) : Nat := (sd + 4 + H.P.L) / H.P.B + 1

include hH in
/-- `B = 2 ^ lgB`, a block of 64 or 128 bytes. -/
theorem lgB_spec : (H.P.B = 64 ∧ lgB H = 6) ∨ (H.P.B = 128 ∧ lgB H = 7) := by
  unfold lgB
  rcases hH.sizes.B with h | h <;> rw [h]
  · exact .inl ⟨rfl, by rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]⟩
  · exact .inr ⟨rfl, by rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]⟩

include hH in
theorem nbOf_spec {sd : Nat} (hsd : sd ≤ 64) : sd + 4 + 1 + H.P.L ≤ nbOf H sd * H.P.B ∧
    nbOf H sd * H.P.B ≤ 256 ∧ nbOf H sd * H.P.B % 8 = 0 := by
  have hL := hH.L
  unfold nbOf
  rcases lgB_spec hH with ⟨hb, -⟩ | ⟨hb, -⟩ <;> rw [hb] <;> omega_using [hL, hsd]

theorem shl_val {x : Nat} {k : Nat} (hx : x * 2 ^ k < 2 ^ 64) :
    BitVec.ofNat 64 x <<< k = BitVec.ofNat 64 (x * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)) hx),
    Nat.mod_eq_of_lt hx]

theorem lsr_val' {x : Nat} (hx : x < 2 ^ 64) {k : Nat} :
    BitVec.ofNat 64 x >>> k = BitVec.ofNat 64 (x / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)]

include hH in
/-- `d := ⌊(x + L) / B⌋ + 1`, from `x` in `r`. -/
theorem blocksOf_ok {t : State} (d r : Reg) {x : Nat} (hr : t.gpr r = BitVec.ofNat 64 x) (hx : x ≤ 2 ^ 32)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t', Only [d] t t' → t'.gpr d = BitVec.ofNat 64 ((x + H.P.L) / H.P.B + 1) → WP isa (.block is) t' Q) :
    WP isa (.block (blocksOf H d r ++ is)) t Q := by
  have hL := hH.L
  have hlg : 2 ^ lgB H = H.P.B ∧ lgB H < 64 := by
    rcases lgB_spec hH with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> decide
  unfold blocksOf
  simp only [List.cons_append, List.nil_append]
  refine wp_addImm (by omega_using [hL]) fun u₂ o₂ e₂ => wp_lsr hlg.2 fun u₃ o₃ e₃ => wp_addImm (by decide)
    fun u₄ o₄ e₄ => k u₄ ((o₂.trans (o₃.trans o₄)).mono fun r hr => by
      simp only [List.mem_append, List.mem_singleton] at hr ⊢; rcases hr with h | h | h <;> exact h) ?_
  rw [e₄, e₃, e₂, hr, BitVec.ofNat_add_ofNat, lsr_val' (by omega_using [hL, hx]), hlg.1, BitVec.ofNat_add_ofNat]

include hH in
theorem clearBlock_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V) {sd : Nat}
    (hsl : t.mem.readW (off F sHLen) 64 = BitVec.ofNat 64 sd) (hsd : sd ≤ 64) :
    WP isa (clearBlock H) t fun t' => Keep [.x10, .x9, .x12] t t' ∧ Frame [⟨S, oRsa⟩] t.mem t'.mem ∧
      Rep t'.mem S (clr V oY (nbOf H sd * H.P.B)) := by
  obtain ⟨_, hnb, h8⟩ := nbOf_spec hH hsd
  have hpos : 0 < nbOf H sd * H.P.B := Nat.mul_pos (Nat.succ_pos _) hH.B_pos
  have e8 : 8 * (nbOf H sd * H.P.B / 8) = nbOf H sd * H.P.B := by omega_using [h8]
  have hsh : nbOf H sd * 2 ^ (lgB H - 3) = nbOf H sd * H.P.B / 8 ∧ lgB H - 3 < 64 := by
    rcases lgB_spec hH with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> exact ⟨by omega_using [], by decide⟩
  unfold clearBlock clearCount
  refine WP.seq (WP.mono (Q := fun (u : State) => Only [.x12, .x10, .x9] t u ∧ u.gpr .x10 = off S oY ∧ u.gpr .x9 = 0#64 ∧
      u.gpr .x12 = BitVec.ofNat 64 (nbOf H sd * H.P.B / 8)) ?_ fun u ⟨O, h10, h9, h12⟩ => ?_)
  · simp only [List.cons_append, List.nil_append]
    refine wp_ldrSp (by decide) (by rw [L.sp]; exact L.fld (by decide)) fun u₀ o₀ e₀ =>
      wp_addImm (by decide) fun u₁ o₁ e₁ => wp_movz fun u₂ o₂ e₂ => wp_addImm (by decide) fun u₂' o₂' e₂' => ?_
    refine blocksOf_ok hH .x12 .x12 (x := sd + 4) (by rw [e₂', o₂.get .x12, o₁.get .x12, e₀, L.sp, hsl,
      BitVec.ofNat_add_ofNat]) (by omega_using [hsd]) fun u₃ o₃ e₃ => wp_lsl hsh.2 fun u₄ o₄ e₄ =>
      wp_nil ⟨(o₀.trans (o₁.trans (o₂.trans (o₂'.trans (o₃.trans o₄))))).mono, ?_, ?_, ?_⟩
    · rw [o₄.get .x10, o₃.get .x10, o₂'.get .x10, o₂.get .x10, e₁, o₀.get .x20, L.x20]
    · rw [o₄.get .x9, o₃.get .x9, o₂'.get .x9, e₂]; rfl
    · rw [e₄, e₃, shl_val (by unfold nbOf at hnb hsh; omega_using [hnb, hsh]), ← hsh.1]; rfl
  refine WP.mono (clearQ_ok (L.congr O.sp O.wr (O.get .x20)) (O.mem ▸ R) (by omega_using [hpos, e8])
    (by rw [e8]; unfold oY oRsa; omega_using [hnb]) h10 h9 h12) fun v ⟨k, f, r⟩ => ⟨(O.keep.trans k).mono, O.mem ▸ f, ?_⟩
  rw [e8] at r; exact r

/-- Where `DB` and `H` are: `DB` the `db` bytes at `scratch + e`, `H` the
`hLen` after them, within `EM`'s place. -/
structure DbAt (D e db : Nat) : Prop where
  e1 : oEm ≤ e
  db1 : 1 ≤ db
  fit : e + db + D ≤ oY

theorem copyH_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V) {sd e db : Nat}
    (hd : DbAt sd e db) (hsd : 0 < sd) (h24 : t.gpr .x24 = off S e) (h25 : t.gpr .x25 = BitVec.ofNat 64 db)
    (hsl : t.mem.readW (off F sHLen) 64 = BitVec.ofNat 64 sd) :
    WP isa copyH t fun t' => Keep [.x11, .x14, .x12, .x15] t t' ∧ Frame [⟨S, oRsa⟩] t.mem t'.mem ∧
      Rep t'.mem S (updL V oY ((List.range sd).map fun i => V (e + db + i))) := by
  have hfit := hd.fit
  have he1 := hd.e1
  have c1 : oY = 3584 := rfl
  have c6 : oRsa = 8192 := rfl
  have c7 : oEm = 2560 := rfl
  unfold copyH
  refine WP.seq (WP.mono (wp_ldrSp (by decide) (by rw [L.sp]; exact L.fld (by decide)) fun u₃ o₃ e₃ =>
    wp_add fun u₁ o₁ e₁ => wp_addImm (by decide) fun u₂ o₂ e₂ =>
    wp_nil (Q := fun u => Only [.x11, .x14, .x12] t u ∧ u.gpr .x11 = off S (e + db) ∧ u.gpr .x14 = off S oY ∧
      u.gpr .x12 = BitVec.ofNat 64 sd)
      ⟨(o₃.trans (o₁.trans o₂)).mono, by rw [o₂.get .x11, e₁, o₃.get .x24, o₃.get .x25, h24, h25, off_add],
        by rw [e₂, o₁.get .x20, o₃.get .x20, L.x20], by rw [o₂.get .x12, o₁.get .x12, e₃, L.sp, hsl]⟩)
      fun u ⟨O, h11, h14, h12⟩ => ?_)
  have Lu := L.congr O.sp O.wr (O.get .x20)
  have Ru : Rep u.mem S V := O.mem ▸ R
  refine WP.mono (copy_ok hsd (by omega_using [hfit, c1]) h14 h11 h12 (fun j hj => by rw [off_add]; exact Lu.ld (by omega_using [hfit, c1, c6, hj]))
    (fun i hi => by rw [off_add]; exact Lu.st (by omega_using [hfit, c1, c6, hi]))
    (fun j hj i hi h => by rw [off_add, off_add, off_inj S (by omega_using [hfit, c1, hj]) (by omega_using [hfit, c1, hi])] at h; omega_using [hfit, hj, h]))
    fun v ⟨k, hm⟩ => ⟨(O.keep.trans k).mono, ?_, ?_⟩
  · rw [hm, Ru.bytes (by omega_using [hfit, c1, c6]), ← O.mem]
    exact writeBytes_frame _ _ _ (Offset.contains_base S
      (by simp only [List.length_map, List.length_range]; omega_using [hfit, c1, c6]) (by omega_using [c1]))
  · rw [hm, Ru.bytes (by omega_using [hfit, c1, c6])]
    exact Ru.writeBytes (by simp only [List.length_map, List.length_range]; omega_using [hfit, c1, c6])

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
theorem counter_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V) {c sd : Nat}
    (h28 : t.gpr .x28 = BitVec.ofNat 64 c) (hc : c < 2 ^ 32)
    (hsl : t.mem.readW (off F sHLen) 64 = BitVec.ofNat 64 sd) (hsd : sd ≤ 64) :
    WP isa (.block (counter H)) t fun t' => Keep [.x10, .x9, .x22, .x16] t t' ∧
      t'.gpr .x22 = BitVec.ofNat 64 (sd + 4) ∧ t'.mem.readW (off F sNb) 64 = BitVec.ofNat 64 (nbOf H sd) ∧
      Frame [⟨S, oRsa⟩, slotR F sNb] t.mem t'.mem ∧ Rep t'.mem S (ctrV sd V c) := by
  have c1 : oY = 3584 := rfl
  have c6 : oRsa = 8192 := rfl
  unfold counter counterRest
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrSp (by decide) (by rw [L.sp]; exact L.fld (by decide)) fun u₀ o₀ e₀ => wp_add fun u₀' o₀' e₀' =>
    wp_addImm (by decide) fun u₁ o₁ e₁ => wp_lsr (by decide) fun u₂ o₂ e₂ => ?_
  have x22₀ : u₀.gpr .x22 = BitVec.ofNat 64 sd := by rw [e₀, L.sp, hsl]
  have a₂ : u₂.gpr .x10 = off S (oY + sd) := by
    rw [o₂.get .x10, e₁, e₀', o₀.get .x20, L.x20, x22₀, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm sd]
  have w₂ : u₂.wr = t.wr := by rw [o₂.wr, o₁.wr, o₀'.wr, o₀.wr]
  have mem₂ : u₂.mem = t.mem := by rw [o₂.mem, o₁.mem, o₀'.mem, o₀.mem]
  have x28₂ : u₂.gpr .x28 = t.gpr .x28 := by rw [o₂.get .x28, o₁.get .x28, o₀'.get .x28, o₀.get .x28]
  have O₂ : Only [.x22, .x10, .x9] t u₂ := (o₀.trans (o₀'.trans (o₁.trans o₂))).mono
  refine wp_strb (by decide) (by rw [a₂, BitVec.add_zero]) (by rw [w₂]; exact L.st (by omega_arith)) fun u₃ m₃ => ?_
  refine wp_lsr (by decide) fun u₄ o₄ e₄ => ?_
  refine wp_strb (by decide) (by rw [o₄.get .x10, m₃.gpr, a₂, off_add])
    (by rw [o₄.wr, m₃.wr, w₂]; exact L.st (by omega_arith)) fun u₅ m₅ => ?_
  refine wp_lsr (by decide) fun u₆ o₆ e₆ => ?_
  refine wp_strb (by decide) (by rw [o₆.get .x10, m₅.gpr, o₄.get .x10, m₃.gpr, a₂, off_add])
    (by rw [o₆.wr, m₅.wr, o₄.wr, m₃.wr, w₂]; exact L.st (by omega_arith)) fun u₇ m₇ => ?_
  refine wp_strb (by decide) (by rw [m₇.gpr, o₆.get .x10, m₅.gpr, o₄.get .x10, m₃.gpr, a₂, off_add])
    (by rw [m₇.wr, o₆.wr, m₅.wr, o₄.wr, m₃.wr, w₂]; exact L.st (by omega_arith)) fun u₈ m₈ => ?_
  refine wp_addImm (by decide) fun u₉ o₉ e₉ => ?_
  have sp₉ : u₉.sp = F := by
    rw [o₉.sp, m₈.sp, m₇.sp, o₆.sp, m₅.sp, o₄.sp, m₃.sp, O₂.sp, L.sp]
  have wr₉ : u₉.wr = t.wr := by rw [o₉.wr, m₈.wr, m₇.wr, o₆.wr, m₅.wr, o₄.wr, m₃.wr, w₂]
  have x28 : ∀ k, k < 64 → ((t.gpr .x28) >>> k).setWidth 8 = BitVec.ofNat 8 (c / 2 ^ k) := fun k _ => by
    rw [h28]; exact byte_shr k (by omega_using [hc])
  have b0 : (u₂.gpr .x9).setWidth 8 = BitVec.ofNat 8 (c / 2 ^ 24) := by
    rw [e₂, o₁.get .x28, o₀'.get .x28, o₀.get .x28]; exact x28 24 (by decide)
  have b1 : (u₄.gpr .x9).setWidth 8 = BitVec.ofNat 8 (c / 2 ^ 16) := by
    rw [e₄, m₃.gpr, x28₂]; exact x28 16 (by decide)
  have b2 : (u₆.gpr .x9).setWidth 8 = BitVec.ofNat 8 (c / 2 ^ 8) := by
    rw [e₆, m₅.gpr, o₄.get .x28, m₃.gpr, x28₂]; exact x28 8 (by decide)
  have b3 : (u₇.gpr .x28).setWidth 8 = BitVec.ofNat 8 c := by
    rw [m₇.gpr, o₆.get .x28, m₅.gpr, o₄.get .x28, m₃.gpr, x28₂]
    have := x28 0 (by decide)
    rwa [BitVec.ushiftRight_zero, Nat.pow_zero, Nat.div_one] at this
  have hm₈ : u₈.mem = (((t.mem.writeW (off S (oY + sd)) (BitVec.ofNat 8 (c / 2 ^ 24))).writeW
      (off S (oY + sd + 1)) (BitVec.ofNat 8 (c / 2 ^ 16))).writeW (off S (oY + sd + 2))
      (BitVec.ofNat 8 (c / 2 ^ 8))).writeW (off S (oY + sd + 3)) (BitVec.ofNat 8 c) := by
    rw [m₈.mem, m₇.mem, o₆.mem, m₅.mem, o₄.mem, m₃.mem, mem₂, b0, b1, b2, b3]
  have R₈ := (((R.wb (o := oY + sd) (by omega_arith) (BitVec.ofNat 8 (c / 2 ^ 24))).wb (o := oY + sd + 1) (by omega_arith)
    (BitVec.ofNat 8 (c / 2 ^ 16))).wb (o := oY + sd + 2) (by omega_arith) (BitVec.ofNat 8 (c / 2 ^ 8))).wb
    (o := oY + sd + 3) (by omega_arith) (BitVec.ofNat 8 c)
  rw [← hm₈] at R₈
  have F₈ : Frame [⟨S, oRsa⟩] t.mem u₈.mem := by
    rw [hm₈]
    refine (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
      |>.writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_ <;>
    exact Offset.contains_base S (by omega_arith) (by omega_arith)
  have L₉ : Lay u₉ F S := ⟨sp₉, by rw [o₉.get .x20, m₈.gpr, m₇.gpr, o₆.get .x20, m₅.gpr, o₄.get .x20, m₃.gpr,
    O₂.get .x20, L.x20], wr₉ ▸ L.fw, wr₉ ▸ L.sw, L.Fw, L.Sw, L.dFS, L.dB⟩
  have x22₉ : u₉.gpr .x22 = BitVec.ofNat 64 (sd + 4) := by
    rw [e₉, m₈.gpr, m₇.gpr, o₆.get .x22, m₅.gpr, o₄.get .x22, m₃.gpr,
      o₂.get .x22, o₁.get .x22, o₀'.get .x22, x22₀, BitVec.ofNat_add_ofNat]
  refine blocksOf_ok hH .x9 .x22 x22₉ (by omega_using [hsd]) fun u₁₀ o₁₀ e₁₀ => ?_
  unfold st
  refine wp_addSp (by decide) fun u₁₁ o₁₁ e₁₁ => ?_
  refine wp_strx (by decide) (by rw [e₁₁, o₁₀.sp, sp₉, BitVec.add_zero])
    (by rw [o₁₁.wr, o₁₀.wr, wr₉]; exact L.fst (by decide)) fun u₁₂ m₁₂ => wp_nil ?_
  have hm₁₂ : u₁₂.mem = u₈.mem.writeW (off F sNb) (BitVec.ofNat 64 (nbOf H sd)) := by
    rw [m₁₂.mem, o₁₁.mem, o₁₀.mem, o₉.mem, o₁₁.get .x9, e₁₀]; rfl
  refine ⟨((O₂.keep.trans (m₃.keep.trans (o₄.keep.trans (m₅.keep.trans (o₆.keep.trans
    (m₇.keep.trans (m₈.keep.trans (o₉.keep.trans (o₁₀.keep.trans (o₁₁.keep.trans m₁₂.keep)))))))))).mono),
    ?_, ?_, ?_, ?_⟩
  · rw [m₁₂.gpr, o₁₁.get .x22, o₁₀.get .x22, x22₉]
  · rw [hm₁₂, Mem.readW_writeW_self64]
  · rw [hm₁₂]
    exact (F₈.mono (by simp)).trans ((frame_slot _ F sNb _).mono (by simp))
  · rw [hm₁₂]
    refine (R₈.frame (frame_slot _ F sNb _) (L.slotS (by decide))).congr fun x _ => ?_
    simp only [upd, ctrV]
    rcases (show x = oY + sd ∨ x = oY + sd + 1 ∨ x = oY + sd + 2 ∨ x = oY + sd + 3 ∨
        ¬(oY + sd ≤ x ∧ x < oY + sd + 4) by omega_using []) with h | h | h | h | h
    · subst h; simp [Spec.Rsa.i2osp]
    · subst h; simp [Spec.Rsa.i2osp]
    · subst h; simp [Spec.Rsa.i2osp]
    · subst h; simp [Spec.Rsa.i2osp]
    · rw [ite_eq_right h, ite_eq_right (by omega_using [h]), ite_eq_right (by omega_using [h]), ite_eq_right (by omega_using [h]),
        ite_eq_right (by omega_using [h])]

/-! ## The digest into `DB` -/
/-! ## The digest into `DB` -/

/-- `V` with the `n` bytes from `a` XORed into those from `b`. -/
def xorV (V : Nat → Byte) (a b n : Nat) (x : Nat) : Byte :=
  if b ≤ x ∧ x < b + n then V x ^^^ V (a + (x - b)) else V x

theorem xorV_zero (V : Nat → Byte) (a b : Nat) : xorV V a b 0 = V := by
  funext x; simp only [xorV]; rw [ite_eq_right (by omega_using [])]

theorem byte_xor (a b : Byte) : (BitVec.setWidth 64 a ^^^ BitVec.setWidth 64 b).setWidth 8 = a ^^^ b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_xor]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by omega_using []), Nat.mod_eq_of_lt (a := b.toNat) (by omega_using []),
    Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (by omega_using []) (by omega_using []))]

theorem borrow_beq {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    ((BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 == 0) = !decide (a < b) := by
  rw [← VG.Proof.RsaPkcs1Sig.AArch64.borrow_ne ha hb]
  simp only [bne, Bool.not_not]

include hH in
theorem xorOut_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V)
    {sd e db done : Nat} (hd : DbAt sd e db) (h24 : t.gpr .x24 = off S e) (h25 : t.gpr .x25 = BitVec.ofNat 64 db)
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
      o₂.get .x9, e₁, L.sp, hdn, Offset.ofNat_sub_ofNat (by omega_using [hlt])]
  · rw [o₇.get .x13, o₆.get .x13, e₅, setWidth_ofNat16 (by omega_using [hfit, c2, hDN, hN])]
  · rw [e₇, e₆, o₅.get .x12, e₅, setWidth_ofNat16 (by omega_using [hfit, c2, hDN, hN]), e₄, o₃.get .x25, o₂.get .x25, o₁.get .x25, h25,
      o₃.get .x9, o₂.get .x9, e₁, L.sp, hdn, Offset.ofNat_sub_ofNat (by omega_using [hlt])]
  -- The count, `min(hLen, dbLen - done)`.
  refine WP.seq (WP.mono (Q := fun (w : State) => Keep [.x12] v w ∧ w.mem = v.mem ∧
      w.gpr .x12 = BitVec.ofNat 64 (min H.D (db - done))) ?_ fun w ⟨kw, hmw, h12w⟩ => ?_)
  · have hb := borrow_beq (a := db - done) (b := H.D) (by omega_using [hfit, c2, hDN, hN]) (by omega_using [hfit, c2, hDN, hN])
    rw [← h14] at hb
    refine WP.ite _ (eval_zero _ _) (fun h => ?_) (fun h => ?_)
    · rw [hb, Bool.not_eq_true', decide_eq_false_iff_not] at h
      exact wp_mov fun w o e' => wp_nil ⟨o.keep, o.mem, by rw [e', h13, Nat.min_eq_left (by omega_using [h])]⟩
    · rw [hb, Bool.not_eq_false', decide_eq_true_eq] at h
      exact wp_nil ⟨Keep.refl _ _, rfl, by rw [h12, Nat.min_eq_right (by omega_using [h])]⟩
  have K : Keep [.x9, .x10, .x11, .x12, .x13, .x14] t w := (O.keep.trans kw).mono
  have Lw : Lay w F S := L.congr K.sp K.wr (K.get .x20)
  have Rw : Rep w.mem S V := by rw [hmw, O.mem]; exact R
  have hn : 0 < min H.D (db - done) := by omega_using [hlt, hD]
  refine WP.mono (wp_countdown (cnt := .x12) (by omega_using [hfit, c2, hDN, hN]) hn (fun j u => Keep [.x9, .x15, .x10, .x11, .x12] w u ∧
      u.gpr .x10 = off S (e + done + j) ∧ u.gpr .x11 = off S (oDig + j) ∧ Frame [⟨S, oRsa⟩] w.mem u.mem ∧
      Rep u.mem S (xorV V oDig (e + done) j))
    (fun j hj u ⟨hK, h10', h11', hF, hR⟩ _ => ?_)
    ⟨Keep.refl _ _, by rw [kw.get .x10, h10, Nat.add_zero], by rw [kw.get .x11, h11, Nat.add_zero],
      Frame.refl _ _, by rw [xorV_zero]; exact Rw⟩ h12w)
    fun u ⟨hK, _, _, hF, hR⟩ => ⟨(K.trans hK).mono, by rw [hmw, O.mem] at hF; exact hF, hR⟩
  have hj := Nat.lt_min.mp hj
  refine wp_ldrb (by decide) (by rw [h11', BitVec.add_zero]) (by rw [hK.rd, hK.wr]; exact Lw.ld (by omega_arith))
    fun u₁ o₁ e₁ => ?_
  refine wp_ldrb (by decide) (by rw [o₁.get .x10, h10', BitVec.add_zero])
    (by rw [o₁.rd, o₁.wr, hK.rd, hK.wr]; exact Lw.ld (by omega_arith)) fun u₂ o₂ e₂ => wp_eor fun u₃ o₃ e₃ => ?_
  have O₃ : Only [.x9, .x15] u u₃ := (o₁.trans (o₂.trans o₃)).mono
  refine wp_strb (by decide) (by rw [O₃.get .x10, h10', BitVec.add_zero]) (by rw [O₃.wr, hK.wr]; exact Lw.st (by omega_arith))
    fun u₄ m₄ => wp_addImm (by decide) fun u₅ o₅ e₅ => wp_addImm (by decide) fun u₆ o₆ e₆ =>
    wp_subImm (by decide) fun u₇ o₇ e₇ => wp_nil ?_
  have hv : (u₃.gpr .x15).setWidth 8 = V (e + done + j) ^^^ V (oDig + j) := by
    rw [e₃, o₂.get .x9, e₁, e₂, o₁.mem, hR _ (by omega_arith), hR _ (by omega_arith), byte_xor]
    simp only [xorV]
    rw [ite_eq_right (by omega_using []), ite_eq_right (by omega_arith)]
  have hm : u₇.mem = u.mem.writeW (off S (e + done + j)) (V (e + done + j) ^^^ V (oDig + j)) := by
    rw [o₇.mem, o₆.mem, o₅.mem, m₄.mem, O₃.mem, hv]
  refine ⟨⟨(hK.trans (O₃.keep.trans (m₄.keep.trans (o₅.keep.trans (o₆.keep.trans o₇.keep))))).mono, ?_, ?_, ?_,
    ?_⟩, ?_⟩
  · rw [o₇.get .x10, e₆, o₅.get .x10, m₄.gpr, O₃.get .x10, h10', off_add, Nat.add_assoc]
  · rw [o₇.get .x11, o₆.get .x11, e₅, m₄.gpr, O₃.get .x11, h11', off_add, Nat.add_assoc]
  · rw [hm]
    exact hF.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  · rw [hm]
    refine (hR.wb (by omega_arith) _).congr fun x _ => ?_
    simp only [upd, xorV]
    by_cases h₁ : x = e + done + j
    · subst h₁
      rw [ite_eq_left rfl, ite_eq_left ⟨by omega_using [], by omega_using []⟩, show e + done + j - (e + done) = j by omega_using []]
    · rw [ite_eq_right h₁]
      by_cases h₂ : e + done ≤ x ∧ x < e + done + j
      · rw [ite_eq_left h₂, ite_eq_left ⟨h₂.1, by omega_using [h₂]⟩]
      · rw [ite_eq_right h₂, ite_eq_right (by omega_using [h₁, h₂])]
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
  refine wp_addImm (by omega_using [hDN, hN]) fun u₃ o₃ e₃ => wp_addSp (by decide) fun u₄ o₄ e₄ => ?_
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
    exact VG.Proof.RsaPkcs1Sig.AArch64.borrow_ne (by omega_using [hd']) (by omega_using [hdb'])
  · rw [o₇.mem, o₆.mem, m₅.mem, h9, o₄.mem, o₃.mem, o₂.mem, o₁.mem]

end

end VG.Proof.RsaPss.AArch64
