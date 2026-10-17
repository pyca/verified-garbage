module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecKdk
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RSAES-PKCS1-v1_5 decryption on ARMv7: the message of an IRPRF block

`I2OSP(i, 2) ‖ label ‖ I2OSP(8 length, 2)` (`msgV`), written byte by byte in
order to `scratch + sMsg` (`MW`, `msgBytes_wp`): the two bytes of `i`, the
label's (`putLabel`), and the bit length's (`clLen` for 256 bytes, `amLen`
for `k`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Dec

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Decrypt VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp wp_strb op2_imm op2_reg op2_lsl op2_lsr dpVal)

variable {P : EP}

/-- The message's place. -/
abbrev msgA (P : EP) : Addr := (sc P sMsg 16).base

/-- The message of block `i`, for the label `lab` and `length` bytes. -/
def msgV (i : Nat) (lab : List Byte) (L : Nat) : List Byte :=
  Spec.Rsa.i2osp i 2 ++ lab ++ Spec.Rsa.i2osp (8 * L) 2

theorem msgV_length (i : Nat) (lab : List Byte) (L : Nat) : (msgV i lab L).length = lab.length + 4 := by
  simp [msgV, VG.Proof.RsaPkcs1Enc.i2osp_length]; omega

/-- The message's first `n` bytes written, memory changed only in its 16
bytes and the registers but `r2` kept. -/
structure MW (P : EP) (σ s₀ : State) (xs : List Byte) (n : Nat) (t : State) : Prop where
  st : S P σ t
  frame : Frame [sc P sMsg 16] s₀.mem t.mem
  regs : ∀ r, r ≠ .r2 → t.gpr r = s₀.gpr r
  bytes : ∀ j < n, t.mem (msgA P + BitVec.ofNat 64 j) = xs.getD j 0

section
variable {σ s₀ t : State} {xs : List Byte} {n : Nat}

theorem MW.start (hs : S P σ s₀) : MW P σ s₀ xs 0 s₀ :=
  ⟨hs, Frame.refl _ _, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem MW.upd (h : MW P σ s₀ xs n t) {t' : State} {v : BitVec 32} (u : Upd t t' .r2 v) : MW P σ s₀ xs n t' :=
  ⟨⟨h.st.1, h.st.2.of_rest (u.rest (ws := [.r2]) (by simp)) u.mem⟩, by rw [u.mem]; exact h.frame,
    fun r hr => by rw [u.other r hr]; exact h.regs r hr, fun j hj => by rw [u.mem]; exact h.bytes j hj⟩

/-- `strb rt, [r0, #n]` of byte `n`. -/
theorem MW.strb (h : MW P σ s₀ xs n t) (hr0 : s₀.gpr .r0 = P.scr + BitVec.ofNat 32 sMsg) (hn : n < 16)
    {rt : Reg} (hb : (t.gpr rt).setWidth 8 = xs.getD n 0) {is : List Instr} {Q : State → Prop}
    (k : ∀ t', MW P σ s₀ xs (n + 1) t' → t'.gpr = t.gpr → WP isa (.block is) t' Q) :
    WP isa (.block (.strb rt .r0 n :: is)) t Q := by
  have hs := h.st
  have ha : State.addr (t.gpr .r0 + BitVec.ofNat 32 n) = msgA P + BitVec.ofNat 64 n := by
    rw [h.regs _ (by decide), hr0, BitVec.add_assoc, BitVec.ofNat_add_ofNat, hs.1.scrA (by simp only [sMsg]; omega)]
    exact (Offset.add_ofNat_add_ofNat _ _ _).symm
  refine wp_strb (by omega) ha (by rw [Offset.add_ofNat_add_ofNat]; exact St.sc_w hs (by simp only [sMsg]; omega))
    fun t' u => k t' ⟨⟨hs.1, ?_⟩, ?_, fun r hr => by rw [u.gpr]; exact h.regs r hr, ?_⟩ u.gpr
  · refine hs.2.write (rs := [sc P sMsg 16]) ?_ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.SCR, by simp, hs.1.sc_sub (by decide)⟩) u.rd u.wr u.sp
    rw [u.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [u.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · intro j hj
    rw [u.mem, WriteBytes.writeW8_apply]
    by_cases e : j = n
    · subst e; simp [hb]
    · simp only [Offset.add_ofNat_ne (msgA P) (by omega) (by omega) e, ↓reduceIte]
      exact h.bytes j (by omega)

theorem setWidth_ofNat8 (v : Nat) : (BitVec.ofNat 32 v).setWidth 8 = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- `putByte n v`: the byte `v` at index `n`. -/
theorem MW.putByte (h : MW P σ s₀ xs n t) (hr0 : s₀.gpr .r0 = P.scr + BitVec.ofNat 32 sMsg) (hn : n < 16)
    {v : Nat} (hv : v < 256) (hb : xs.getD n 0 = BitVec.ofNat 8 v) {is : List Instr} {Q : State → Prop}
    (k : ∀ t', MW P σ s₀ xs (n + 1) t' → WP isa (.block is) t' Q) :
    WP isa (.block (putByte n v ++ is)) t Q :=
  wp_mov (op2_imm (Proof.RsaPkcs1Sig.Arm.encodable_of_lt (by rw [BitVec.toNat_ofNat]; omega))) fun t1 u1 =>
    (h.upd u1).strb hr0 hn (by rw [u1.gpr, setWidth_ofNat8, hb]) fun t2 h2 _ => k t2 h2

/-- `putLabel vs n`: the bytes `vs` from index `n`. -/
theorem MW.putLabel (hr0 : s₀.gpr .r0 = P.scr + BitVec.ofNat 32 sMsg) :
    ∀ (vs : List Nat) {n : Nat} {t : State}, MW P σ s₀ xs n t → n + vs.length ≤ 16 → (∀ v ∈ vs, v < 256) →
      (∀ j < vs.length, xs.getD (n + j) 0 = BitVec.ofNat 8 (vs.getD j 0)) →
      ∀ {is : List Instr} {Q : State → Prop}, (∀ t', MW P σ s₀ xs (n + vs.length) t' → WP isa (.block is) t' Q) →
      WP isa (.block (Impl.RsaPkcs1Enc.Arm.Decrypt.putLabel vs n ++ is)) t Q
  | [], n, t, h, _, _, _, _, _, k => by simpa [Impl.RsaPkcs1Enc.Arm.Decrypt.putLabel] using k t h
  | v :: vs, n, t, h, hn, hv, hb, _, _, k => by
    simp only [Impl.RsaPkcs1Enc.Arm.Decrypt.putLabel, List.append_assoc]
    refine h.putByte hr0 (by simp at hn; omega) (hv v (by simp)) (by simpa using hb 0 (by simp)) fun t1 h1 => ?_
    refine MW.putLabel hr0 vs h1 (by simp at hn; omega) (fun w hw => hv w (by simp [hw]))
      (fun j hj => by rw [show n + 1 + j = n + (j + 1) by omega, hb (j + 1) (by simp; omega)]; rfl)
      fun t2 h2 => k t2 (by simpa [Nat.add_assoc, Nat.add_comm 1] using h2)

end

/-! ## The whole message -/

theorem i2osp_two_lt {i : Nat} (hi : i < 256) : Spec.Rsa.i2osp i 2 = [0, BitVec.ofNat 8 i] := by
  rw [VG.Proof.RsaPkcs1Enc.i2osp_two, Nat.div_eq_of_lt hi]; rfl

/-- The message: its bytes, from the label's bytes `vs` and the code `len`
of the bit length's two bytes. -/
theorem msgBytes_wp {σ s : State} {vs : List Nat} {len : List Instr} {L i : Nat} (hs : S P σ s)
    (hr0 : s.gpr .r0 = P.scr + BitVec.ofNat 32 sMsg) (hr1 : s.gpr .r1 = BitVec.ofNat 32 i) (hi : i < 256)
    (hvs : vs.length + 4 ≤ 16) (hv : ∀ v ∈ vs, v < 256)
    (hlen : ∀ {t : State}, MW P σ s (msgV i (vs.map (BitVec.ofNat 8)) L) (vs.length + 2) t →
      ∀ {Q : State → Prop}, (∀ t', MW P σ s (msgV i (vs.map (BitVec.ofNat 8)) L) (vs.length + 4) t' → Q t') →
      WP isa (.block len) t Q) :
    WP isa (.block (msgBytes vs len)) s fun t =>
      S P σ t ∧ Frame [sc P sMsg 16] s.mem t.mem ∧ (∀ r, r ≠ .r2 → t.gpr r = s.gpr r) ∧
      Spec.Rsa.bytesAt t.mem (sc P sMsg (vs.length + 4)).base (vs.length + 4) = msgV i (vs.map (BitVec.ofNat 8)) L := by
  have hm : (msgV i (vs.map (BitVec.ofNat 8)) L).length = vs.length + 4 := by rw [msgV_length]; simp
  unfold msgBytes
  refine (MW.start (xs := msgV i (vs.map (BitVec.ofNat 8)) L) hs).putByte hr0 (by decide) (v := 0) (by decide)
    (by simp only [msgV, i2osp_two_lt hi]; rfl) fun t1 h1 => ?_
  refine h1.strb hr0 (by decide) (by rw [h1.regs _ (by decide), hr1, setWidth_ofNat8]; simp [msgV, i2osp_two_lt hi])
    fun t2 h2 _ => ?_
  refine MW.putLabel hr0 vs h2 (by omega) hv (fun j hj => ?_) fun t3 h3 => ?_
  · simp only [msgV, i2osp_two_lt hi, List.cons_append, List.nil_append]
    rw [show 0 + 1 + 1 + j = j + 2 by omega, List.getD_cons_succ, List.getD_cons_succ,
      getD_append_left _ _ _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, hj]
  · refine hlen (by simpa [Nat.add_comm] using h3) fun t4 h4 => ⟨h4.st, h4.frame, h4.regs, ?_⟩
    rw [← hm]
    exact bytesAt_eq fun j hj => by rw [hm] at hj; exact h4.bytes j hj

/-- The bit length 2048 (`clLen`), after a label of 6 bytes. -/
theorem clLen_wp {σ s t : State} {lab : List Byte} {i : Nat} (hl : lab.length = 6)
    (hr0 : s.gpr .r0 = P.scr + BitVec.ofNat 32 sMsg) (h : MW P σ s (msgV i lab 256) 8 t) {Q : State → Prop}
    (k : ∀ t', MW P σ s (msgV i lab 256) 10 t' → Q t') : WP isa (.block clLen) t Q := by
  have e8 : (msgV i lab 256).getD 8 0 = BitVec.ofNat 8 0x08 := by
    simp only [msgV]
    rw [getD_append_right _ _ _ (by simp [VG.Proof.RsaPkcs1Enc.i2osp_length, hl])]
    simp [hl, VG.Proof.RsaPkcs1Enc.i2osp_two]
  have e9 : (msgV i lab 256).getD 9 0 = BitVec.ofNat 8 0x00 := by
    simp only [msgV]
    rw [getD_append_right _ _ _ (by simp [VG.Proof.RsaPkcs1Enc.i2osp_length, hl])]
    simp [hl, VG.Proof.RsaPkcs1Enc.i2osp_two]
  have := h.putByte hr0 (by decide) (v := 0x08) (by decide) e8 (is := putByte 9 0) fun t1 h1 =>
    h1.putByte hr0 (by decide) (v := 0) (by decide) e9 (is := []) fun t2 h2 => WP.block_nil (k t2 h2)
  simpa [clLen, putByte] using this

end VG.Proof.RsaPkcs1Enc.Arm.Dec
