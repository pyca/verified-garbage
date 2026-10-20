module
public import VerifiedGarbage.Proof.Dsa.Arm.RandomFrame
public import VerifiedGarbage.Proof.Dsa.RandomBytes

import VerifiedGarbage.Proof.Dsa.Arm.RandomPrepare
import VerifiedGarbage.Proof.Dsa.Arm.RandomScan
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Copying a draw into the nonce (32-bit ARM)

`copy` copies the `width` bytes of a draw from the tape, at `rand + used`,
to their place right-aligned in the `q_len`-byte nonce (`drawPlace`), its
first byte masked (`copied`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp wp_ldrb wp_strb op2_imm op2_reg eval_eq eval_ne
  ofNat_beq_zero)
open VG.Proof.Dsa (maskValue copied)

/-- The draw's place in the frame, and its bytes. -/
abbrev drawPlace (s₀ : State) : Nat := oNonce + ((rQBytes s₀).length - rWidth s₀)
abbrev drawBytes (s₀ : State) (used : Nat) : List Byte := ((rInput s₀).rand.drop used).take (rWidth s₀)

theorem drawPlace_le {s₀ : State} (A : RandomABI s₀) : drawPlace s₀ + rWidth s₀ ≤ oNonce + 32 := by
  have := rQBytes_le A; have := rWidth_le s₀; unfold drawPlace; omega

theorem RReady.draw {s₀ t : State} (A : RandomABI s₀) (h : RReady s₀ t) {used : Nat}
    (hu : used ≤ (rInput s₀).rand.length) (w : Nat) :
    BytesIn t (stackArg s₀ 5 + BitVec.ofNat 32 used) (((rInput s₀).rand.drop used).take w) :=
  ((h.rand A).drop used hu).take w

/-- The copy after its first `k ≥ 1` bytes. `d` is the draw's place in the
frame, `p` its source. -/
structure CopyInv (s₀ t₀ : State) (p : BitVec 32) (d : Nat) (bs : List Byte) (mask : BitVec 32)
    (k : Nat) (t : State) : Prop where
  ready : RReady s₀ t
  r1 : t.gpr .r1 = p + BitVec.ofNat 32 k
  r4 : t.gpr .r4 = t.gpr .r11 + BitVec.ofNat 32 (d + k)
  r2 : t.gpr .r2 = BitVec.ofNat 32 (bs.length - k)
  bytes : ∀ i < k, t.mem (off (rBase s₀) (d + i)) = copied bs mask i
  out : Outside (rBase s₀) d bs.length t₀.mem t.mem
  rest : Rest [.r0, .r1, .r2, .r4, .r7] t₀ t

theorem copyByte_ok {s₀ t₀ t : State} {p : BitVec 32} {d : Nat} {bs : List Byte} {mask : BitVec 32}
    {k : Nat} (hin : BytesIn t p bs) (hd : d + bs.length ≤ frameBytes) (hk : k < bs.length)
    (I : CopyInv s₀ t₀ p d bs mask k t) (hk0 : 1 ≤ k) :
    WP isa (.block copyByte) t fun u => CopyInv s₀ t₀ p d bs mask (k + 1) u ∧
      u.z = decide (bs.length - (k + 1) = 0) := by
  have hfit := hin.fit
  have hrf := I.ready.rf
  have hF : frameBytes = 112 := rfl
  have hlt : bs.length < 2 ^ 32 := by omega
  unfold copyByte
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 k) (by decide)
    (by rw [BitVec.add_zero, I.r1, VG.Arm.addr_add (by omega)]) (hin.rd k hk) fun t₁ u₁ => ?_
  rw [hin.val k hk] at u₁
  refine wp_strb (a := off (rBase s₀) (d + k)) (by decide)
    (by rw [BitVec.add_zero, u₁.other _ (by decide), I.r4]; exact hrf.ea (by omega))
    (by rw [u₁.wr]; exact hrf.write (by omega)) fun t₂ u₂ => ?_
  refine wp_inc fun t₃ u₃ => wp_inc fun t₄ u₄ => wp_dec fun t₅ u₅ z₅ => WP.block_nil ?_
  have m₅ : t₅.mem = t.mem.writeW (off (rBase s₀) (d + k)) bs[k] := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, VG.Proof.Dsa.byte_setWidth, u₁.mem]
  have R : Rest [.r0, .r1, .r2, .r4, .r7] t t₅ := (u₁.rest (by decide)).trans ((u₂.rest _).trans
    ((u₃.rest (by decide)).trans ((u₄.rest (by decide)).trans (u₅.rest (by decide)))))
  have r2 : t₅.gpr .r2 = BitVec.ofNat 32 (bs.length - (k + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), I.r2,
      ofNat_sub_one (by omega), show bs.length - k - 1 = bs.length - (k + 1) by omega]
  have O : Outside (rBase s₀) d bs.length t.mem t₅.mem := by
    rw [m₅]; exact (writeW8_outside _ _ (d := d + k) _ (by omega)).mono (by omega) (by omega)
  refine ⟨⟨I.ready.congr R (by rw [m₅]; exact frame_store s₀ _ (by omega) _), ?_, ?_, r2, fun i hi => ?_,
    I.out.trans O, I.rest.trans R⟩, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), I.r1,
      Offset.add_ofNat_add_one]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), I.r4,
      R.gpr .r11 (by decide), Offset.add_ofNat_add_one, Nat.add_assoc]
  · rw [m₅]
    by_cases hik : i = k
    · subst hik
      rw [writeW8_self]
      simp only [copied, show i ≠ 0 by omega, ite_false, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hk, Option.getD_some]
    · rw [writeW8_outside _ _ (d := d + k) _ (by omega) _ (by rw [ofs_off0 _ (by omega)]; omega)]
      exact I.bytes i (by omega)
  · rw [z₅, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), I.r2,
      ofNat_sub_one (by omega), show bs.length - k - 1 = bs.length - (k + 1) by omega, ofNat_beq_zero (by omega)]

/-- The bytes after the first. -/
theorem copyLoop_ok {s₀ t₀ t : State} {p : BitVec 32} {d : Nat} {bs : List Byte} {mask : BitVec 32}
    {k : Nat} (hin : ∀ u, RReady s₀ u → BytesIn u p bs) (hd : d + bs.length ≤ frameBytes)
    (hk : k < bs.length) (hk0 : 1 ≤ k) (I : CopyInv s₀ t₀ p d bs mask k t) :
    WP isa (.loop (.block copyByte) .ne) t fun u => CopyInv s₀ t₀ p d bs mask bs.length u := by
  refine WP.loop (M := isa) (fun (n : Nat) (u : State) =>
      ∃ j, n = bs.length - j ∧ 1 ≤ j ∧ j < bs.length ∧ CopyInv s₀ t₀ p d bs mask j u)
    (fun n u hu => ?_) (bs.length - k) t ⟨k, rfl, hk0, hk, I⟩
  obtain ⟨j, hn, hj0, hj, J⟩ := hu
  refine WP.mono (copyByte_ok (hin u J.ready) hd hj J hj0) fun v ⟨J', z⟩ => ?_
  by_cases he : bs.length - (j + 1) = 0
  · left
    refine ⟨by rw [eval_ne, z, decide_eq_true he]; rfl, ?_⟩
    rw [show bs.length = j + 1 by omega]; exact J'
  · right
    exact ⟨by rw [eval_ne, z, decide_eq_false he]; rfl, bs.length - (j + 1), by omega, j + 1, rfl, by omega,
      by omega, J'⟩

theorem drawBytes_length {s₀ : State} {used : Nat} (hfull : used + rWidth s₀ ≤ (rInput s₀).rand.length) :
    (drawBytes s₀ used).length = rWidth s₀ := by
  simp only [drawBytes, List.length_take, List.length_drop]; omega

/-- The draw's source, count and place. -/
theorem copyHeader_ok {s₀ t : State} (A : RandomABI s₀) (h : RReady s₀ t) {used : Nat}
    (hu : slot t.mem (rBase s₀) oUsed = BitVec.ofNat 32 used)
    (hw : slot t.mem (rBase s₀) oWidth = BitVec.ofNat 32 (rWidth s₀)) :
    WP isa (.block copyHeader) t fun t₈ => RReady s₀ t₈ ∧ t₈.mem = t.mem ∧ Rest [.r0, .r1, .r2, .r4, .r7] t t₈ ∧
      t₈.gpr .r1 = stackArg s₀ 5 + BitVec.ofNat 32 used ∧ t₈.gpr .r2 = BitVec.ofNat 32 (rWidth s₀) ∧
      t₈.gpr .r4 = t₈.gpr .r11 + BitVec.ofNat 32 (drawPlace s₀) := by
  have hql := rQBytes_le A
  have hqn := rQBytes_length A
  have hwq := rWidth_le s₀
  unfold copyHeader
  refine wp_ldArg A h (j := 5) (by decide) fun t₁ u₁ => wp_ld (h.upd u₁) (by decide) fun t₂ u₂ =>
    wp_dp (op2_reg _ _) fun t₃ u₃ => wp_ld ((h.upd u₁).upd u₂ |>.upd u₃) (by decide) fun t₄ u₄ =>
    wp_dp (op2_imm (by decide)) fun t₅ u₅ => wp_ldArg A ((((h.upd u₁).upd u₂).upd u₃).upd u₄ |>.upd u₅)
      (j := 2) (by decide) fun t₆ u₆ => wp_dp (op2_reg _ _) fun t₇ u₇ => wp_dp (op2_reg _ _) fun t₈ u₈ =>
      WP.block_nil ?_
  have h₈ := (((((((h.upd u₁).upd u₂).upd u₃).upd u₄).upd u₅).upd u₆).upd u₇).upd u₈
  have m₈ : t₈.mem = t.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have R₈ : Rest [.r0, .r1, .r2, .r4, .r7] t t₈ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans
    ((u₃.rest (by decide)).trans ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans ((u₆.rest (by decide)).trans
    ((u₇.rest (by decide)).trans (u₈.rest (by decide))))))))
  refine ⟨h₈, m₈, R₈, ?_, ?_, ?_⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr]
    show t₂.gpr .r1 + t₂.gpr .r0 = _
    rw [u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem, hu]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.mem, u₂.mem, u₁.mem, hw]
  · rw [u₈.gpr]
    show t₇.gpr .r4 - t₇.gpr .r2 = _
    rw [u₇.gpr, u₇.other .r2 (by decide)]
    show t₆.gpr .r4 + t₆.gpr .r0 - t₆.gpr .r2 = _
    rw [u₆.gpr, u₆.other .r4 (by decide), u₆.other .r2 (by decide), u₅.gpr, u₅.other .r2 (by decide),
      R₈.gpr .r11 (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem, hw, u₄.other .r11 (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
    show t.gpr .r11 + BitVec.ofNat 32 oNonce + stackArg s₀ 2 - BitVec.ofNat 32 (rWidth s₀) = _
    rw [show stackArg s₀ 2 = BitVec.ofNat 32 (rQBytes s₀).length by rw [hqn, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      BitVec.add_assoc, BitVec.ofNat_add_ofNat, add_ofNat_sub32 _ (by omega) (by unfold oNonce; omega)]
    unfold drawPlace; congr 2; omega

/-- The draw's source, count and place, and its first byte, masked. -/
theorem copyInit_ok {s₀ t : State} (A : RandomABI s₀) (h : RReady s₀ t) {used : Nat}
    (hu : slot t.mem (rBase s₀) oUsed = BitVec.ofNat 32 used)
    (hw : slot t.mem (rBase s₀) oWidth = BitVec.ofNat 32 (rWidth s₀))
    (hm : slot t.mem (rBase s₀) oMask = maskValue (rLead s₀).toNat)
    (hfull : used + rWidth s₀ ≤ (rInput s₀).rand.length) (hw1 : 1 ≤ rWidth s₀) :
    WP isa (.block copyInit) t fun u => CopyInv s₀ t (stackArg s₀ 5 + BitVec.ofNat 32 used) (drawPlace s₀)
      (drawBytes s₀ used) (maskValue (rLead s₀).toNat) 1 u ∧ u.z = decide (rWidth s₀ - 1 = 0) := by
  have hF : frameBytes = 112 := rfl
  have hql := rQBytes_le A
  have hwq := rWidth_le s₀
  have hdl := drawBytes_length hfull
  have hdp := drawPlace_le A
  have hon : oNonce = 64 := rfl
  have hin := h.draw A (used := used) (by omega) (rWidth s₀)
  have hfit := hin.fit
  rw [hdl] at hfit
  unfold copyInit
  refine VG.Proof.X25519.Arm.WP.append (copyHeader_ok A h hu hw) fun t₈ ⟨h₈, m₈, R₈, r1₈, r2₈, r4₈⟩ => ?_
  unfold copyFirst
  -- The first byte.
  have hb0 : 0 < (drawBytes s₀ used).length := by omega
  refine wp_ldrb (a := State.addr (stackArg s₀ 5 + BitVec.ofNat 32 used) + BitVec.ofNat 64 0) (by decide)
    (by rw [BitVec.add_zero, BitVec.add_zero, r1₈]) (by rw [R₈.rd, R₈.wr]; exact hin.rd 0 hb0) fun t₉ u₉ => ?_
  rw [m₈, hin.val 0 hb0] at u₉
  refine wp_ld (h₈.upd u₉) (by decide) fun t₁₀ u₁₀ => wp_dp (op2_reg _ _) fun t₁₁ u₁₁ => ?_
  refine wp_strb (a := off (rBase s₀) (drawPlace s₀)) (by decide)
    (by rw [BitVec.add_zero, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), r4₈];
        exact h₈.rf.ea (by omega))
    (by rw [u₁₁.wr, u₁₀.wr, u₉.wr]; exact h₈.rf.write (by omega)) fun t₁₂ u₁₂ => ?_
  refine wp_inc fun t₁₃ u₁₃ => wp_inc fun t₁₄ u₁₄ => wp_dec fun t₁₅ u₁₅ z₁₅ => WP.block_nil ?_
  have v₁₁ : t₁₁.gpr .r0 = (drawBytes s₀ used)[0].setWidth 32 &&& maskValue (rLead s₀).toNat := by
    rw [u₁₁.gpr, u₁₀.other _ (by decide), u₁₀.gpr, u₉.gpr, u₉.mem, m₈, hm]; rfl
  have m₁₅ : t₁₅.mem = t.mem.writeW (off (rBase s₀) (drawPlace s₀))
      (((drawBytes s₀ used)[0].setWidth 32 &&& maskValue (rLead s₀).toNat).setWidth 8) := by
    rw [u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, v₁₁, u₁₁.mem, u₁₀.mem, u₉.mem, m₈]
  have R : Rest [.r0, .r1, .r2, .r4, .r7] t t₁₅ := R₈.trans ((u₉.rest (by decide)).trans ((u₁₀.rest (by decide)).trans
    ((u₁₁.rest (by decide)).trans ((u₁₂.rest _).trans ((u₁₃.rest (by decide)).trans ((u₁₄.rest (by decide)).trans
    (u₁₅.rest (by decide))))))))
  have r2 : t₁₄.gpr .r2 = BitVec.ofNat 32 (rWidth s₀) := by
    rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), r2₈]
  refine ⟨⟨h.congr R (by rw [m₁₅]; exact frame_store s₀ _ (by omega) _), ?_, ?_, ?_, fun i hi => ?_, ?_, R⟩, ?_⟩
  · rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.gpr, u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.other _ (by decide), r1₈]
    rfl
  · rw [u₁₅.other _ (by decide), u₁₄.gpr, u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.other _ (by decide), r4₈, R.gpr .r11 (by decide), R₈.gpr .r11 (by decide),
      Offset.add_ofNat_add_one]
  · rw [u₁₅.gpr, r2, hdl, ofNat_sub_one hw1]
  · obtain rfl : i = 0 := by omega
    rw [m₁₅, Nat.add_zero, writeW8_self]
    simp only [copied, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb0, Option.getD_some]
  · rw [m₁₅, hdl]; exact (writeW8_outside _ _ _ (by omega)).mono (by omega) (by omega)
  · rw [z₁₅, r2, ofNat_sub_one hw1, ofNat_beq_zero (by omega)]

theorem copy_ok {s₀ t : State} (A : RandomABI s₀) (h : RReady s₀ t) {used : Nat}
    (hu : slot t.mem (rBase s₀) oUsed = BitVec.ofNat 32 used)
    (hw : slot t.mem (rBase s₀) oWidth = BitVec.ofNat 32 (rWidth s₀))
    (hm : slot t.mem (rBase s₀) oMask = maskValue (rLead s₀).toNat)
    (hfull : used + rWidth s₀ ≤ (rInput s₀).rand.length) (hw1 : 1 ≤ rWidth s₀) :
    WP isa copy t fun u => RReady s₀ u ∧
      (∀ i < rWidth s₀, u.mem (off (rBase s₀) (drawPlace s₀ + i)) =
        copied (drawBytes s₀ used) (maskValue (rLead s₀).toNat) i) ∧
      Outside (rBase s₀) (drawPlace s₀) (rWidth s₀) t.mem u.mem ∧
      Rest [.r0, .r1, .r2, .r4, .r7] t u := by
  have hdl := drawBytes_length hfull
  have hdp := drawPlace_le A
  have hF : frameBytes = 112 := rfl
  have hon : oNonce = 64 := rfl
  unfold copy copyRest
  refine WP.seq (WP.mono (copyInit_ok A h hu hw hm hfull hw1) fun u ⟨I, z⟩ => ?_)
  have fin : ∀ v, CopyInv s₀ t (stackArg s₀ 5 + BitVec.ofNat 32 used) (drawPlace s₀) (drawBytes s₀ used)
      (maskValue (rLead s₀).toNat) (rWidth s₀) v →
      RReady s₀ v ∧ (∀ i < rWidth s₀, v.mem (off (rBase s₀) (drawPlace s₀ + i)) =
        copied (drawBytes s₀ used) (maskValue (rLead s₀).toNat) i) ∧
      Outside (rBase s₀) (drawPlace s₀) (rWidth s₀) t.mem v.mem ∧ Rest [.r0, .r1, .r2, .r4, .r7] t v :=
    fun v J => ⟨J.ready, J.bytes, by rw [← hdl]; exact J.out, J.rest⟩
  by_cases h1 : rWidth s₀ - 1 = 0
  · refine WP.ite false (by rw [eval_ne, z, decide_eq_true h1]; rfl) (fun e => Bool.noConfusion e)
      (fun _ => WP.block_nil (fin u (by rw [show rWidth s₀ = 1 by omega]; exact I)))
  · refine WP.ite true (by rw [eval_ne, z, decide_eq_false h1]; rfl) (fun _ => ?_) (fun e => Bool.noConfusion e)
    refine WP.mono (copyLoop_ok (fun v hv => hv.draw A (by omega) _)
      (show drawPlace s₀ + (drawBytes s₀ used).length ≤ frameBytes by rw [hdl]; omega)
      (show 1 < (drawBytes s₀ used).length by rw [hdl]; omega) (Nat.le_refl _) I)
      fun v J => fin v (by rw [← hdl]; exact J)

end VG.Proof.Dsa.Arm
