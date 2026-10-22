module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecMem
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.RsaPkcs1Enc.Steps
import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSAES-PKCS1-v1_5 decryption on x86: the message of an IRPRF block

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecMsg.lean`):
`I2OSP(i, 2) ‖ label ‖ I2OSP(8 length, 2)` (`msgV`), written byte by byte
in order to `scratch + sMsg` (at `ebx`; `MW`, `msgBytes_wp`): the two bytes
of `i` (in `ecx`), the label's (`putLabel`), and the bit length's (`clLen`
for 256 bytes, `amLen` for `k`, in `edx`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp

variable {P : EP}

/-- The message's place. -/
abbrev msgA (P : EP) : Addr := (sc P sMsg 16).base

/-- The message of block `i`, for the label `lab` and `length` bytes. -/
def msgV (i : Nat) (lab : List Byte) (L : Nat) : List Byte :=
  Spec.Rsa.i2osp i 2 ++ lab ++ Spec.Rsa.i2osp (8 * L) 2

theorem msgV_length (i : Nat) (lab : List Byte) (L : Nat) : (msgV i lab L).length = lab.length + 4 := by
  simp [msgV, VG.Proof.RsaPkcs1Enc.i2osp_length]; omega

/-- The message's first `n` bytes written, memory changed only in its 16
bytes, and the registers but `eax` kept. -/
structure MW (P : EP) (σ s₀ : State) (xs : List Byte) (n : Nat) (t : State) : Prop where
  st : S P σ t
  frame : Frame [sc P sMsg 16] s₀.mem t.mem
  regs : ∀ r, r ≠ .eax → t.gpr r = s₀.gpr r
  bytes : ∀ j < n, t.mem (msgA P + BitVec.ofNat 64 j) = xs.getD j 0

section
variable {σ s₀ t : State} {xs : List Byte} {n : Nat}

theorem MW.start (hs : S P σ s₀) : MW P σ s₀ xs 0 s₀ :=
  ⟨hs, Frame.refl _ _, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem MW.upd (h : MW P σ s₀ xs n t) {t' : State} {v : BitVec 32} (u : Upd t t' .eax v) : MW P σ s₀ xs n t' :=
  ⟨⟨h.st.1, h.st.2.upd u (by decide)⟩, by rw [u.mem]; exact h.frame,
    fun r hr => by rw [u.other r hr]; exact h.regs r hr, fun j hj => by rw [u.mem]; exact h.bytes j hj⟩

/-- `mov byte [ebx + n], r` of byte `n`. -/
theorem MW.st8 (h : MW P σ s₀ xs n t) (hbx : s₀.gpr .ebx = P.scr + BitVec.ofNat 32 sMsg) (hn : n < 16)
    {r : Reg8} (hb : (t.gpr r.reg).setWidth 8 = xs.getD n 0) {is : List Instr} {Q : State → Prop}
    (k : ∀ t', MW P σ s₀ xs (n + 1) t' → t'.gpr = t.gpr → WP isa (.block is) t' Q) :
    WP isa (.block (.store8 (Impl.RsaPkcs1Sig.X86.at_ .ebx n) r :: is)) t Q := by
  have hs := h.st
  have ha : t.ea (Impl.RsaPkcs1Sig.X86.at_ .ebx n) = msgA P + BitVec.ofNat 64 n := by
    show t.ea ⟨.ebx, n⟩ = _
    rw [ea_at, h.regs _ (by decide), hbx, hs.1.addrSc (by simp only [sMsg]; omega)]
    exact (Offset.add_ofNat_add_ofNat _ _ _).symm
  have hc : (sc P sMsg 16).Contains (msgA P + BitVec.ofNat 64 n) 1 := Offset.contains_base _ (by omega) (by omega)
  refine wp_store8 ha (by rw [Offset.add_ofNat_add_ofNat]; exact St.sc_w hs (by simp only [sMsg]; omega))
    fun t' u => k t' ⟨⟨hs.1, ?_⟩, ?_, fun r hr => by rw [u.gpr]; exact h.regs r hr, ?_⟩ u.gpr
  · refine hs.2.write (rs := [sc P sMsg 16]) ?_ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.SCR, by simp, hs.1.sc_sub (by decide)⟩) u.rd u.wr
      (by rw [u.gpr])
    rw [u.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc
  · rw [u.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ hc
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
theorem MW.putByte (h : MW P σ s₀ xs n t) (hbx : s₀.gpr .ebx = P.scr + BitVec.ofNat 32 sMsg) (hn : n < 16)
    {v : Nat} (hb : xs.getD n 0 = BitVec.ofNat 8 v) {is : List Instr} {Q : State → Prop}
    (k : ∀ t', MW P σ s₀ xs (n + 1) t' → WP isa (.block is) t' Q) :
    WP isa (.block (putByte n v ++ is)) t Q :=
  wp_movi fun t1 u1 => (h.upd u1).st8 hbx hn (r := .al) (by rw [show Reg8.al.reg = .eax from rfl, u1.gpr,
    setWidth_ofNat8, hb]) fun t2 h2 _ => k t2 h2

/-- `putLabel vs n`: the bytes `vs` from index `n`. -/
theorem MW.putLabel (hbx : s₀.gpr .ebx = P.scr + BitVec.ofNat 32 sMsg) :
    ∀ (vs : List Nat) {n : Nat} {t : State}, MW P σ s₀ xs n t → n + vs.length ≤ 16 →
      (∀ j < vs.length, xs.getD (n + j) 0 = BitVec.ofNat 8 (vs.getD j 0)) →
      ∀ {is : List Instr} {Q : State → Prop}, (∀ t', MW P σ s₀ xs (n + vs.length) t' → WP isa (.block is) t' Q) →
      WP isa (.block (Impl.RsaPkcs1Enc.X86.Decrypt.putLabel vs n ++ is)) t Q
  | [], n, t, h, _, _, _, _, k => by simpa [Impl.RsaPkcs1Enc.X86.Decrypt.putLabel] using k t h
  | v :: vs, n, t, h, hn, hb, _, _, k => by
    simp only [Impl.RsaPkcs1Enc.X86.Decrypt.putLabel, List.append_assoc]
    refine h.putByte hbx (by simp at hn; omega) (by simpa using hb 0 (by simp)) fun t1 h1 => ?_
    refine MW.putLabel hbx vs h1 (by simp at hn; omega)
      (fun j hj => by rw [show n + 1 + j = n + (j + 1) by omega, hb (j + 1) (by simp; omega)]; rfl)
      fun t2 h2 => k t2 (by simpa [Nat.add_assoc, Nat.add_comm 1] using h2)

end

/-! ## The whole message -/

theorem i2osp_two_lt {i : Nat} (hi : i < 256) : Spec.Rsa.i2osp i 2 = [0, BitVec.ofNat 8 i] := by
  rw [VG.Proof.RsaPkcs1Enc.i2osp_two, Nat.div_eq_of_lt hi]; rfl

/-- The message: its bytes, from the label's bytes `vs` and the code `len`
of the bit length's two bytes. -/
theorem msgBytes_wp {σ s : State} {vs : List Nat} {len : List Instr} {L i : Nat} (hs : S P σ s)
    (hbx : s.gpr .ebx = P.scr + BitVec.ofNat 32 sMsg) (hcx : s.gpr .ecx = BitVec.ofNat 32 i) (hi : i < 256)
    (hvs : vs.length + 4 ≤ 16)
    (hlen : ∀ {t : State}, MW P σ s (msgV i (vs.map (BitVec.ofNat 8)) L) (vs.length + 2) t →
      ∀ {Q : State → Prop}, (∀ t', MW P σ s (msgV i (vs.map (BitVec.ofNat 8)) L) (vs.length + 4) t' → Q t') →
      WP isa (.block len) t Q) :
    WP isa (.block (msgBytes vs len)) s fun t =>
      S P σ t ∧ Frame [sc P sMsg 16] s.mem t.mem ∧ (∀ r, r ≠ .eax → t.gpr r = s.gpr r) ∧
      Spec.Rsa.bytesAt t.mem (sc P sMsg (vs.length + 4)).base (vs.length + 4) =
        msgV i (vs.map (BitVec.ofNat 8)) L := by
  have hm : (msgV i (vs.map (BitVec.ofNat 8)) L).length = vs.length + 4 := by rw [msgV_length]; simp
  unfold msgBytes
  refine (MW.start (xs := msgV i (vs.map (BitVec.ofNat 8)) L) hs).putByte hbx (by decide) (v := 0)
    (by simp only [msgV, i2osp_two_lt hi]; rfl) fun t1 h1 => ?_
  refine h1.st8 hbx (by decide) (r := .cl) (by
      rw [show Reg8.cl.reg = .ecx from rfl, h1.regs _ (by decide), hcx, setWidth_ofNat8]
      simp [msgV, i2osp_two_lt hi])
    fun t2 h2 _ => ?_
  refine MW.putLabel hbx vs h2 (by omega) (fun j hj => ?_) fun t3 h3 => ?_
  · simp only [msgV, i2osp_two_lt hi, List.cons_append, List.nil_append]
    rw [show 0 + 1 + 1 + j = j + 2 by omega, List.getD_cons_succ, List.getD_cons_succ,
      Proof.RsaPkcs1Sig.getD_append_left _ _ _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, hj]
  · refine hlen (by simpa [Nat.add_comm] using h3) fun t4 h4 => ⟨h4.st, h4.frame, h4.regs, ?_⟩
    rw [← hm]
    exact Proof.RsaPkcs1Sig.bytesAt_eq fun j hj => by rw [hm] at hj; exact h4.bytes j hj

/-- The bit length 2048 (`clLen`), after a label of 6 bytes. -/
theorem clLen_wp {σ s t : State} {lab : List Byte} {i : Nat} (hl : lab.length = 6)
    (hbx : s.gpr .ebx = P.scr + BitVec.ofNat 32 sMsg) (h : MW P σ s (msgV i lab 256) 8 t) {Q : State → Prop}
    (k : ∀ t', MW P σ s (msgV i lab 256) 10 t' → Q t') : WP isa (.block clLen) t Q := by
  have e8 : (msgV i lab 256).getD 8 0 = BitVec.ofNat 8 0x08 := by
    simp only [msgV]
    rw [Proof.RsaPkcs1Sig.getD_append_right _ _ _ (by simp [VG.Proof.RsaPkcs1Enc.i2osp_length, hl])]
    simp [hl, VG.Proof.RsaPkcs1Enc.i2osp_two]
  have e9 : (msgV i lab 256).getD 9 0 = BitVec.ofNat 8 0x00 := by
    simp only [msgV]
    rw [Proof.RsaPkcs1Sig.getD_append_right _ _ _ (by simp [VG.Proof.RsaPkcs1Enc.i2osp_length, hl])]
    simp [hl, VG.Proof.RsaPkcs1Enc.i2osp_two]
  have := h.putByte hbx (by decide) (v := 0x08) e8 (is := putByte 9 0) fun t1 h1 =>
    h1.putByte hbx (by decide) (v := 0) e9 (is := []) fun t2 h2 => WP.block_nil (k t2 h2)
  simpa [clLen] using this

theorem shr5 {K : Nat} (hK : K ≤ 1024) : (BitVec.ofNat 32 K >>> 5).setWidth 8 = BitVec.ofNat 8 (8 * K / 256) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

theorem times8 (K : Nat) :
    ((BitVec.ofNat 32 K + BitVec.ofNat 32 K + (BitVec.ofNat 32 K + BitVec.ofNat 32 K)) +
      (BitVec.ofNat 32 K + BitVec.ofNat 32 K + (BitVec.ofNat 32 K + BitVec.ofNat 32 K))).setWidth 8 =
      BitVec.ofNat 8 (8 * K) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The bit length `8 k` (`amLen`), after a label of 7 bytes, from `k` in `edx`. -/
theorem amLen_wp {σ s t : State} {lab : List Byte} {i K : Nat} (hl : lab.length = 7) (hK : K ≤ 1024)
    (hbx : s.gpr .ebx = P.scr + BitVec.ofNat 32 sMsg) (hdx : s.gpr .edx = BitVec.ofNat 32 K)
    (h : MW P σ s (msgV i lab K) 9 t) {Q : State → Prop}
    (k : ∀ t', MW P σ s (msgV i lab K) 11 t' → Q t') : WP isa (.block amLen) t Q := by
  have dx : t.gpr .edx = BitVec.ofNat 32 K := by rw [h.regs _ (by decide), hdx]
  have e9 : (msgV i lab K).getD 9 0 = BitVec.ofNat 8 (8 * K / 256) := by
    simp only [msgV]
    rw [Proof.RsaPkcs1Sig.getD_append_right _ _ _ (by simp [VG.Proof.RsaPkcs1Enc.i2osp_length, hl])]
    simp [hl, VG.Proof.RsaPkcs1Enc.i2osp_two]
  have e10 : (msgV i lab K).getD 10 0 = BitVec.ofNat 8 (8 * K) := by
    simp only [msgV]
    rw [Proof.RsaPkcs1Sig.getD_append_right _ _ _ (by simp [VG.Proof.RsaPkcs1Enc.i2osp_length, hl])]
    simp [hl, VG.Proof.RsaPkcs1Enc.i2osp_two]
  simp only [amLen]
  refine wp_mov fun t1 u1 => ?_
  refine wp_shr (n := 5) (by decide) fun t2 u2 _ => ?_
  refine ((h.upd u1).upd u2).st8 hbx (by decide) (r := .al)
    (by rw [show Reg8.al.reg = .eax from rfl, u2.gpr, u1.gpr, dx, shr5 hK, e9]) fun t3 h3 g3 => ?_
  have dx' : t3.gpr .edx = BitVec.ofNat 32 K := by rw [g3, u2.other _ (by decide), u1.other _ (by decide), dx]
  refine wp_mov fun t4 u4 => ?_
  refine wp_add fun t5 u5 _ => ?_
  refine wp_add fun t6 u6 _ => ?_
  refine wp_add fun t7 u7 _ => ?_
  refine ((((h3.upd u4).upd u5).upd u6).upd u7).st8 hbx (by decide) (r := .al)
    (by rw [show Reg8.al.reg = .eax from rfl, u7.gpr, u6.gpr, u5.gpr, u4.gpr, dx', times8, e10])
    fun t8 h8 _ => WP.block_nil (k t8 h8)

end VG.Proof.RsaPkcs1Enc.X86.Dec
