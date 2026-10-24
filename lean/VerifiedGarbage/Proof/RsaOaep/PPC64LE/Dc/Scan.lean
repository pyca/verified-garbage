module

import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Label
public import VerifiedGarbage.Proof.RsaOaep.Scan
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.PrivCall

/-!
# RSAES-OAEP decryption on PPC64LE: `lHash` and the scan

Untrusted: everything here is checked by Lean. `accLh_ok`: the accumulator
of `EM`'s first byte and `lHash' ⊕ lHash` (`accG`); `scan_ok`: the scan of
`T` (`scanS`, its masks from the top bits of `b - 1` and `(b ⊕ 1) - 1`),
then the accumulator ORed with `looking`. Both read our part of the working
space only, and keep `Base`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep wp_li wp_mov wp_addi wp_subi wp_add wp_sub wp_and wp_or wp_xor wp_lsr
  wp_lbz wp_nil wp_countdown)
open VG.Proof.RsaOaep (scanS accG zM mk zM_zx zM_zx1)
open VG.Proof.Mgf1 (ifp ifn)

/-! ## A byte's masks -/

/-- `(b - 1) >>> 63`: 1 if `b = 0`, 0 if not. -/
theorem zbit (b : Byte) : (b.setWidth 64 - BitVec.ofNat 64 1) >>> 63 = if b = 0 then 1#64 else 0#64 := by
  have hb := b.isLt
  have e : b = BitVec.ofNat 8 b.toNat := (BitVec.ofNat_toNat _ b).trans (BitVec.setWidth_eq _) |>.symm
  generalize b.toNat = n at hb e
  subst e
  revert n; decide +kernel

/-- `((b ⊕ 1) - 1) >>> 63`: 1 if `b = 1`, 0 if not. -/
theorem obit (b : Byte) : ((b.setWidth 64 ^^^ BitVec.ofNat 64 1) - BitVec.ofNat 64 1) >>> 63 =
    if b = 1 then 1#64 else 0#64 := by
  have hb := b.isLt
  have e : b = BitVec.ofNat 8 b.toNat := (BitVec.ofNat_toNat _ b).trans (BitVec.setWidth_eq _) |>.symm
  generalize b.toNat = n at hb e
  subst e
  revert n; decide +kernel

theorem masks (b : Byte) :
    ((if b = 0 then 1#64 else 0#64) ||| (if b = 1 then 1#64 else 0#64)) - BitVec.ofNat 64 1 =
      (zM (b.setWidth 64) ||| zM (b.setWidth 64 ^^^ 1)) ^^^ BitVec.allOnes 64 ∧
    BitVec.ofNat 64 0 - (if b = 1 then 1#64 else 0#64) = zM (b.setWidth 64 ^^^ 1) ∧
    (if b = 1 then 1#64 else 0#64) - BitVec.ofNat 64 1 = zM (b.setWidth 64 ^^^ 1) ^^^ BitVec.allOnes 64 := by
  rw [zM_zx, zM_zx1]
  by_cases h0 : b = 0
  · subst h0; simp only [mk]; decide
  by_cases h1 : b = 1
  · subst h1; simp only [mk]; decide
  simp only [mk, h0, h1, ite_false]; decide

/-! ## The scan's step -/

/-- The scan's registers after `i` bytes of `f`, at `b`. -/
structure ScanI (f : Nat → Byte) (c₀ : BitVec 64) (b : Addr) (i : Nat) (u : State) : Prop where
  r4 : u.gpr .r4 = off b i
  r6 : u.gpr .r6 = BitVec.ofNat 64 i
  r7 : u.gpr .r7 = (scanS f c₀ i).1
  r25 : u.gpr .r25 = (scanS f c₀ i).2.1
  r24 : u.gpr .r24 = (scanS f c₀ i).2.2

theorem scan_step {f : Nat → Byte} {c₀ : BitVec 64} {b : Addr} {i : Nat} {u u' : State} (I : ScanI f c₀ b i u)
    (z₁ o₁ zo : BitVec 64)
    (hz : z₁ = ((f i).setWidth 64 - BitVec.ofNat 64 1) >>> 63)
    (ho : o₁ = (((f i).setWidth 64 ^^^ BitVec.ofNat 64 1) - BitVec.ofNat 64 1) >>> 63)
    (hzo : zo = (z₁ ||| o₁) - BitVec.ofNat 64 1)
    (h24 : u'.gpr .r24 = u.gpr .r24 ||| (zo &&& u.gpr .r7))
    (h25 : u'.gpr .r25 = u.gpr .r25 ||| ((u.gpr .r6 &&& u.gpr .r7) &&& (BitVec.ofNat 64 0 - o₁)))
    (h7 : u'.gpr .r7 = u.gpr .r7 &&& (o₁ - BitVec.ofNat 64 1))
    (h4 : u'.gpr .r4 = u.gpr .r4 + BitVec.ofNat 64 1) (h6 : u'.gpr .r6 = u.gpr .r6 + BitVec.ofNat 64 1) :
    ScanI f c₀ b (i + 1) u' := by
  obtain ⟨m1, m2, m3⟩ := masks (f i)
  rw [zbit] at hz
  rw [obit] at ho
  subst hz ho hzo
  refine ⟨by rw [h4, I.r4]; exact off_off _ _ _, by rw [h6, I.r6, BitVec.ofNat_add], ?_, ?_, ?_⟩
  · rw [h7, m3, I.r7]; rfl
  · rw [h25, m2, I.r25, I.r6, I.r7]; rfl
  · rw [h24, m1, I.r24, I.r7]; rfl

section
variable {s : State} (P : PreD s) {m : Mem} {rc : Nat}
include P

/-- `acc := EM[0] ∨ ⋁ (lHash'[i] ⊕ lHash[i])`, `lHash'` at `1 + D`, `lHash` at
`oDig`. -/
theorem accLh_ok {H : Hash} {D : Nat} (hD : H.D = D) (hD0 : 0 < D) (hD64 : D ≤ 64) (hk : 2 * D + 2 ≤ kk s)
    {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) :
    WP isa (accLh H) t fun t' => Base (SD s) (VD s rc) (withMem s m) t' ∧ t'.mem = t.mem ∧
      (∀ r ∈ Reg.r14 :: fx ++ hiRegs, t'.gpr r = t.gpr r) ∧
      t'.gpr .r24 = accG (view t.mem (Sd s) 0) (fun i => view t.mem (Sd s) (1 + D + i))
        (fun i => view t.mem (Sd s) (oDig + i)) D := by
  obtain ⟨hE, hSt, hDg, hCt, hW, hRs⟩ := offs
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r7).toNat := rfl
  have PF := fitsM (m := m) P
  subst hD
  have rdw : ∀ {u : State}, u.rd = t.rd → u.wr = t.wr → ∀ {o : Nat}, o + 1 ≤ oRsa →
      InRegions (u.rd ++ u.wr) (off (Sd s) o) 1 := fun hr hw _ ho => by
    rw [hr, hw, h.wr]; exact sc_inR PF ho _
  refine WP.seq (wp_addi (h := by unfold oEm; omega) fun t₁ o₁ e₁ => wp_addi fun t₂ o₂ e₂ =>
    wp_lbz (a := off (Sd s) 0) (by rw [o₂.get .r14, o₁.get .r14, h.r14, hE]) (rdw (o₁.rd ▸ o₂.rd) (o₁.wr ▸ o₂.wr)
      (by decide)) fun t₃ o₃ e₃ => wp_li (by omega) fun t₄ o₄ e₄ => wp_nil ?_)
  have k₄ : Only [.r4, .r5, .r24, .r6] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine WP.mono (wp_countdown (cnt := .r6) (N := H.D) (by omega) hD0
    (fun i u => Only [.r4, .r5, .r6, .r7, .r8, .r24] t u ∧ u.gpr .r4 = off (Sd s) (1 + H.D + i) ∧
      u.gpr .r5 = off (Sd s) (oDig + i) ∧ u.gpr .r24 = accG (view t.mem (Sd s) 0)
        (fun i => view t.mem (Sd s) (1 + H.D + i)) (fun i => view t.mem (Sd s) (oDig + i)) i) ?_
    ⟨k₄.mono, by rw [o₄.get .r4, o₃.get .r4, o₂.get .r4, e₁, h.r14, hE]; rfl,
      by rw [o₄.get .r5, o₃.get .r5, e₂, o₁.get .r14, h.r14]; rfl,
      by rw [o₄.get .r24, e₃, o₂.mem, o₁.mem]; rfl⟩ (by rw [e₄]))
    fun u ⟨o, _, _, a⟩ => ⟨h.only PF o, o.mem, fun r hr => o.gpr r (by revert r; decide), a⟩
  intro i hi u ⟨o, r4, r5, a⟩ _
  refine wp_lbz (a := off (Sd s) (1 + H.D + i)) (by rw [r4, BitVec.add_zero])
    (rdw o.rd o.wr (by omega)) fun u₁ p₁ f₁ => ?_
  refine wp_lbz (a := off (Sd s) (oDig + i)) (by rw [p₁.get .r5, r5, BitVec.add_zero])
    (rdw (p₁.rd.trans o.rd) (p₁.wr.trans o.wr) (by omega)) fun u₂ p₂ f₂ => ?_
  refine wp_xor fun u₃ p₃ f₃ => wp_or fun u₄ p₄ f₄ => wp_addi fun u₅ p₅ f₅ => wp_addi fun u₆ p₆ f₆ =>
    wp_subi fun u₇ p₇ f₇ => wp_nil ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (o.trans (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans p₇))))))).mono
  · rw [p₇.get .r4, p₆.get .r4, f₅, p₄.get .r4, p₃.get .r4, p₂.get .r4, p₁.get .r4, r4]
    show off (off (Sd s) (1 + H.D + i)) 1 = off (Sd s) (1 + H.D + i + 1); exact off_off _ _ _
  · rw [p₇.get .r5, f₆, p₅.get .r5, p₄.get .r5, p₃.get .r5, p₂.get .r5, p₁.get .r5, r5]
    show off (off (Sd s) (oDig + i)) 1 = off (Sd s) (oDig + i + 1); exact off_off _ _ _
  · rw [p₇.get .r24, p₆.get .r24, p₅.get .r24, f₄, p₃.get .r24, p₂.get .r24, p₁.get .r24, a, f₃, p₂.get .r7, f₁,
      f₂, p₁.mem, o.mem]; rfl
  · rw [f₇, p₆.get .r6, p₅.get .r6, p₄.get .r6, p₃.get .r6, p₂.get .r6, p₁.get .r6]

/-- The scan of `T` (`k - 2 D - 1` bytes at `1 + 2 D`), then `acc ∨= looking`. -/
theorem scan_ok {H : Hash} {D : Nat} (hD : H.D = D) (hD64 : D ≤ 64) (hk : 2 * D + 2 ≤ kk s)
    {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) :
    WP isa (scan H) t fun t' => Base (SD s) (VD s rc) (withMem s m) t' ∧ t'.mem = t.mem ∧
      (∀ r ∈ Reg.r14 :: fx ++ hiRegs, t'.gpr r = t.gpr r) ∧
      t'.gpr .r24 = (scanS (fun i => view t.mem (Sd s) (1 + 2 * D + i)) (t.gpr .r24) (kk s - (2 * D + 1))).2.2 |||
        (scanS (fun i => view t.mem (Sd s) (1 + 2 * D + i)) (t.gpr .r24) (kk s - (2 * D + 1))).1 ∧
      t'.gpr .r25 = (scanS (fun i => view t.mem (Sd s) (1 + 2 * D + i)) (t.gpr .r24) (kk s - (2 * D + 1))).2.1 := by
  obtain ⟨hE, hSt, hDg, hCt, hW, hRs⟩ := offs
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r7).toNat := rfl
  have PF := fitsM (m := m) P
  subst hD
  refine WP.seq (wp_addi (h := by unfold oEm; omega) fun t₁ o₁ e₁ => wp_subi (h := by omega) fun t₂ o₂ e₂ =>
    wp_li (by decide) fun t₃ o₃ e₃ => wp_li (by decide) fun t₄ o₄ e₄ => wp_subi fun t₅ o₅ e₅ =>
    wp_li (by decide) fun t₆ o₆ e₆ => wp_nil ?_)
  have k₆ : Only [.r4, .r5, .r6, .r7, .r25] t t₆ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans o₆))))).mono
  generalize hf : (fun i => view t.mem (Sd s) (1 + 2 * H.D + i)) = f
  have I0 : ScanI f (t.gpr .r24) (off (Sd s) (1 + 2 * H.D)) 0 t₆ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [o₆.get .r4, o₅.get .r4, o₄.get .r4, o₃.get .r4, o₂.get .r4, e₁, h.r14, hE, Nat.zero_add]
      show _ = off (Sd s) (1 + 2 * H.D) + BitVec.ofNat 64 0
      rw [BitVec.add_zero]
    · rw [o₆.get .r6, o₅.get .r6, o₄.get .r6, e₃]
    · rw [o₆.get .r7, e₅, e₄]; rfl
    · rw [e₆]; rfl
    · rw [k₆.get .r24]; rfl
  refine WP.seq (WP.mono (wp_countdown (cnt := .r5) (N := kk s - (2 * H.D + 1)) (by omega) (by omega)
    (fun i u => ScanI f (t.gpr .r24) (off (Sd s) (1 + 2 * H.D)) i u ∧
      Only [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r24, .r25] t₆ u) ?_
    ⟨I0, Only.refl _ _⟩ (by rw [o₆.get .r5, o₅.get .r5, o₄.get .r5, o₃.get .r5, e₂, o₁.get .r15, Base.r15 h,
      sub_ofNat (by omega)])) fun u ⟨I, o⟩ => ?_)
  · intro i hi u ⟨I, o⟩ _
    refine wp_lbz (a := off (Sd s) (1 + 2 * H.D + i)) (by rw [I.r4, BitVec.add_zero, off_off])
      (by rw [o.rd, o.wr, k₆.rd, k₆.wr, h.wr]; exact sc_inR PF (by omega) _) fun u₁ p₁ f₁ => ?_
    refine wp_subi fun u₂ p₂ f₂ => wp_lsr fun u₃ p₃ f₃ => wp_li (by decide) fun u₄ p₄ f₄ =>
      wp_xor fun u₅ p₅ f₅ => wp_subi fun u₆ p₆ f₆ => wp_lsr fun u₇ p₇ f₇ => wp_or fun u₈ p₈ f₈ =>
      wp_subi fun u₉ p₉ f₉ => wp_and fun u₁₀ p₁₀ f₁₀ => wp_or fun u₁₁ p₁₁ f₁₁ => wp_li (by decide) fun u₁₂ p₁₂ f₁₂ =>
      wp_sub fun u₁₃ p₁₃ f₁₃ => wp_and fun u₁₄ p₁₄ f₁₄ => wp_and fun u₁₅ p₁₅ f₁₅ => wp_or fun u₁₆ p₁₆ f₁₆ =>
      wp_subi fun u₁₇ p₁₇ f₁₇ => wp_and fun u₁₈ p₁₈ f₁₈ => wp_addi fun u₁₉ p₁₉ f₁₉ => wp_addi fun u₂₀ p₂₀ f₂₀ =>
      wp_subi fun u₂₁ p₂₁ f₂₁ => wp_nil ?_
    have q : Only [.r10, .r8, .r9, .r24, .r3, .r25, .r7, .r4, .r6, .r5] u u₂₁ :=
      (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans (p₇.trans (p₈.trans (p₉.trans (p₁₀.trans
        (p₁₁.trans (p₁₂.trans (p₁₃.trans (p₁₄.trans (p₁₅.trans (p₁₆.trans (p₁₇.trans (p₁₈.trans (p₁₉.trans
        (p₂₀.trans p₂₁)))))))))))))))))))).mono
    have hb : u₁.gpr .r10 = (f i).setWidth 64 := by
      rw [f₁, o.mem, k₆.mem, ← hf]; rfl
    have a9 : Only [.r10, .r8, .r9] u u₉ :=
      (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans (p₇.trans (p₈.trans p₉)))))))).mono
    have a7 : Only [.r10, .r8, .r9] u u₇ :=
      (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans p₇)))))).mono
    have b12 : Only [.r8, .r24, .r3] u₇ u₁₂ := (p₈.trans (p₉.trans (p₁₀.trans (p₁₁.trans p₁₂)))).mono
    have b16 : Only [.r8, .r24, .r3, .r25] u₇ u₁₆ :=
      (b12.trans (p₁₃.trans (p₁₄.trans (p₁₅.trans p₁₆)))).mono
    have a15 : Only [.r10, .r8, .r9, .r24, .r3] u u₁₅ :=
      (a9.trans (p₁₀.trans (p₁₁.trans (p₁₂.trans (p₁₃.trans (p₁₄.trans p₁₅)))))).mono
    have a17 : Only [.r10, .r8, .r9, .r24, .r3, .r25] u u₁₇ := (a15.trans (p₁₆.trans p₁₇)).mono
    have c11 : Only [.r5, .r8, .r25, .r9, .r7, .r4, .r6, .r3] u₁₁ u₂₁ :=
      (p₁₂.trans (p₁₃.trans (p₁₄.trans (p₁₅.trans (p₁₆.trans (p₁₇.trans (p₁₈.trans (p₁₉.trans (p₂₀.trans
        p₂₁))))))))).mono
    have c16 : Only [.r9, .r7, .r4, .r6, .r5] u₁₆ u₂₁ :=
      (p₁₇.trans (p₁₈.trans (p₁₉.trans (p₂₀.trans p₂₁)))).mono
    have c18 : Only [.r4, .r6, .r5] u₁₈ u₂₁ := (p₁₉.trans (p₂₀.trans p₂₁)).mono
    have a18 : Only [.r10, .r8, .r9, .r24, .r3, .r25, .r7] u u₁₈ := (a17.trans p₁₈).mono
    have a20 : Only [.r10, .r8, .r9, .r24, .r3, .r25, .r7, .r4, .r6] u u₂₀ := (a18.trans (p₁₉.trans p₂₀)).mono
    refine ⟨⟨scan_step I (u₃.gpr .r8) (u₇.gpr .r9) (u₉.gpr .r8) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, (o.trans q).mono⟩, ?_⟩
    · rw [f₃, f₂, hb]
    · rw [f₇, f₆, f₅, f₄, p₄.get .r10, p₃.get .r10, p₂.get .r10, hb]
    · rw [f₉, f₈, p₇.get .r8, p₆.get .r8, p₅.get .r8, p₄.get .r8]
    · rw [c11.get .r24, f₁₁, f₁₀, p₁₀.get .r24, a9.get .r24, a9.get .r7]
    · rw [c16.get .r25, f₁₆, f₁₅, f₁₄, p₁₄.get .r3, f₁₃, f₁₂, b12.get .r9, a15.get .r25, (a9.trans
        (p₁₀.trans (p₁₁.trans (p₁₂.trans p₁₃)))).get .r6, (a9.trans (p₁₀.trans (p₁₁.trans (p₁₂.trans p₁₃)))).get .r7]
    · rw [c18.get .r7, f₁₈, f₁₇, b16.get .r9, a17.get .r7]
    · rw [p₂₁.get .r4, p₂₀.get .r4, f₁₉, a18.get .r4]
    · rw [p₂₁.get .r6, f₂₀, p₁₉.get .r6, a18.get .r6]
    · rw [f₂₁, a20.get .r5]
  refine wp_or fun w ow ew => wp_nil ?_
  have kk' : Only [.r4, .r5, .r6, .r7, .r25, .r3, .r8, .r9, .r10, .r24] t w := (k₆.trans (o.trans ow)).mono
  refine ⟨h.only PF kk', by rw [kk'.mem], fun r hr => kk'.gpr r (by revert r; decide), ?_, ?_⟩
  · rw [ew, I.r24, I.r7]
  · rw [ow.get .r25]; exact I.r25

end

end VG.Proof.RsaOaep.PPC64LE.Dec
