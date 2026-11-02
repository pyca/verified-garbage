module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Priv
public import VerifiedGarbage.Proof.RsaOaep.Scan
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Main
import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Mgf1.Bytes

/-!
# RSAES-OAEP decryption on RISC-V: the scan

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/Scan.lean`), register for register: `scan_ok`,
the scan of `T` (`scanS`, its masks from the top bits of `b - 1` and
`(b ⊕ 1) - 1`), then the accumulator ORed with `looking`. It reads our part
of the working space only, and keeps `Base`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.Impl.RsaOaep.RISCV64.Dec
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only wp_li wp_mov wp_addi wp_subi wp_add wp_sub wp_and wp_or wp_xor wp_srl
  wp_lbu wp_nil)
open VG.Proof.RsaOaep.RISCV64 (Base Fits view off off_off offs sc_inR sub_k)
open VG.Proof.Bignum.RISCV64 (wp_countdown)
open VG.Proof.RsaOaep (scanS zM mk zM_zx zM_zx1)
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
  a1 : u.gpr .a1 = off b i
  a3 : u.gpr .a3 = BitVec.ofNat 64 i
  a4 : u.gpr .a4 = (scanS f c₀ i).1
  s6 : u.gpr .s6 = (scanS f c₀ i).2.1
  s5 : u.gpr .s5 = (scanS f c₀ i).2.2

theorem scan_step {f : Nat → Byte} {c₀ : BitVec 64} {b : Addr} {i : Nat} {u u' : State} (I : ScanI f c₀ b i u)
    (z₁ o₁ zo : BitVec 64)
    (hz : z₁ = ((f i).setWidth 64 - BitVec.ofNat 64 1) >>> 63)
    (ho : o₁ = (((f i).setWidth 64 ^^^ BitVec.ofNat 64 1) - BitVec.ofNat 64 1) >>> 63)
    (hzo : zo = (z₁ ||| o₁) - BitVec.ofNat 64 1)
    (h24 : u'.gpr .s5 = u.gpr .s5 ||| (zo &&& u.gpr .a4))
    (h25 : u'.gpr .s6 = u.gpr .s6 ||| ((u.gpr .a3 &&& u.gpr .a4) &&& (BitVec.ofNat 64 0 - o₁)))
    (h7 : u'.gpr .a4 = u.gpr .a4 &&& (o₁ - BitVec.ofNat 64 1))
    (h4 : u'.gpr .a1 = u.gpr .a1 + BitVec.ofNat 64 1) (h6 : u'.gpr .a3 = u.gpr .a3 + BitVec.ofNat 64 1) :
    ScanI f c₀ b (i + 1) u' := by
  obtain ⟨m1, m2, m3⟩ := masks (f i)
  rw [zbit] at hz
  rw [obit] at ho
  subst hz ho hzo
  refine ⟨by rw [h4, I.a1]; exact off_off _ _ _, by rw [h6, I.a3, BitVec.ofNat_add], ?_, ?_, ?_⟩
  · rw [h7, m3, I.a4]; rfl
  · rw [h25, m2, I.s6, I.a3, I.a4]; rfl
  · rw [h24, m1, I.s5, I.a4]; rfl

section
variable {s : State} (P : PreD s) {m : Mem} {rc : Nat}
include P

/-- The scan of `T` (`k - 2 D - 1` bytes at `1 + 2 D`), then `acc ∨= looking`. -/
theorem scan_ok {H : Hash} {D : Nat} (hD : H.D = D) (hD64 : D ≤ 64) (hk : 2 * D + 2 ≤ kk s)
    {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) :
    WP isa (scan H) t fun t' => Base (SD s) (VD s rc) (withMem s m) t' ∧ t'.mem = t.mem ∧
      Only [.a1, .a2, .a3, .a4, .s6, .t3, .t1, .t2, .a7, .s5] t t' ∧
      t'.gpr .s5 = (scanS (fun i => view t.mem (Sd s) (1 + 2 * D + i)) (t.gpr .s5) (kk s - (2 * D + 1))).2.2 |||
        (scanS (fun i => view t.mem (Sd s) (1 + 2 * D + i)) (t.gpr .s5) (kk s - (2 * D + 1))).1 ∧
      t'.gpr .s6 = (scanS (fun i => view t.mem (Sd s) (1 + 2 * D + i)) (t.gpr .s5) (kk s - (2 * D + 1))).2.1 := by
  obtain ⟨hE, hSt, hDg, hCt, hRs⟩ := offs
  have hk2 := P.k2
  have ek : kk s = (s.gpr .a4).toNat := rfl
  have PF : Fits (SD s) (withMem s m) := fits P rfl rfl
  subst hD
  unfold scan tArgs
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_addi (imm := oEm + 1 + 2 * H.D) (h := by unfold oEm; omega) fun t₁ o₁ e₁ =>
    wp_subi (imm := 2 * H.D + 1) (h := by omega) fun t₂ o₂ e₂ =>
    wp_li (imm := 0) (by decide) fun t₃ o₃ e₃ => wp_li (imm := 0) (by decide) fun t₄ o₄ e₄ =>
    wp_subi (imm := 1) fun t₅ o₅ e₅ => wp_li (imm := 0) (by decide) fun t₆ o₆ e₆ => wp_nil ?_)
  have k₆ : Only [.a1, .a2, .a3, .a4, .s6] t t₆ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans o₆))))).mono
  generalize hf : (fun i => view t.mem (Sd s) (1 + 2 * H.D + i)) = f
  have I0 : ScanI f (t.gpr .s5) (off (Sd s) (1 + 2 * H.D)) 0 t₆ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [o₆.get .a1, o₅.get .a1, o₄.get .a1, o₃.get .a1, o₂.get .a1, e₁, h.s0, hE, Nat.zero_add]
      show _ = off (Sd s) (1 + 2 * H.D) + BitVec.ofNat 64 0
      rw [BitVec.add_zero]
    · rw [o₆.get .a3, o₅.get .a3, o₄.get .a3, e₃]
    · rw [o₆.get .a4, e₅, e₄]; rfl
    · rw [e₆]; rfl
    · rw [k₆.get .s5]; rfl
  refine WP.seq (WP.mono (wp_countdown (cnt := .a2) (N := kk s - (2 * H.D + 1)) (by omega) (by omega)
    (fun i u => ScanI f (t.gpr .s5) (off (Sd s) (1 + 2 * H.D)) i u ∧
      Only [.t3, .a1, .a2, .a3, .a4, .t1, .t2, .a7, .s5, .s6] t₆ u) ?_
    ⟨I0, Only.refl _ _⟩ (by rw [o₆.get .a2, o₅.get .a2, o₄.get .a2, o₃.get .a2, e₂, o₁.get .s1, Base.dk h,
      sub_k (by omega)])) fun u ⟨I, o⟩ => ?_)
  · intro i hi u ⟨I, o⟩ _
    simp only [scanBody, List.cons_append, List.nil_append]
    refine wp_lbu (a := off (Sd s) (1 + 2 * H.D + i)) (by rw [I.a1, BitVec.add_zero, off_off])
      (by rw [o.rd, o.wr, k₆.rd, k₆.wr, h.wr]; exact sc_inR PF (by omega) _) fun u₁ p₁ f₁ => ?_
    refine wp_subi (imm := 1) fun u₂ p₂ f₂ => wp_srl fun u₃ p₃ f₃ => wp_li (imm := 1) (by decide) fun u₄ p₄ f₄ =>
      wp_xor fun u₅ p₅ f₅ => wp_subi (imm := 1) fun u₆ p₆ f₆ => wp_srl fun u₇ p₇ f₇ => wp_or fun u₈ p₈ f₈ =>
      wp_subi (imm := 1) fun u₉ p₉ f₉ => wp_and fun u₁₀ p₁₀ f₁₀ => wp_or fun u₁₁ p₁₁ f₁₁ =>
      wp_li (imm := 0) (by decide) fun u₁₂ p₁₂ f₁₂ =>
      wp_sub fun u₁₃ p₁₃ f₁₃ => wp_and fun u₁₄ p₁₄ f₁₄ => wp_and fun u₁₅ p₁₅ f₁₅ => wp_or fun u₁₆ p₁₆ f₁₆ =>
      wp_subi (imm := 1) fun u₁₇ p₁₇ f₁₇ => wp_and fun u₁₈ p₁₈ f₁₈ => wp_addi (imm := 1) fun u₁₉ p₁₉ f₁₉ =>
      wp_addi (imm := 1) fun u₂₀ p₂₀ f₂₀ => wp_subi (imm := 1) fun u₂₁ p₂₁ f₂₁ => wp_nil ?_
    have q : Only [.a7, .t1, .t2, .s5, .t3, .s6, .a4, .a1, .a3, .a2] u u₂₁ :=
      (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans (p₇.trans (p₈.trans (p₉.trans (p₁₀.trans
        (p₁₁.trans (p₁₂.trans (p₁₃.trans (p₁₄.trans (p₁₅.trans (p₁₆.trans (p₁₇.trans (p₁₈.trans (p₁₉.trans
        (p₂₀.trans p₂₁)))))))))))))))))))).mono
    have hb : u₁.gpr .a7 = (f i).setWidth 64 := by
      rw [f₁, o.mem, k₆.mem, ← hf]; rfl
    have a9 : Only [.a7, .t1, .t2] u u₉ :=
      (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans (p₇.trans (p₈.trans p₉)))))))).mono
    have a7 : Only [.a7, .t1, .t2] u u₇ :=
      (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans p₇)))))).mono
    have b12 : Only [.t1, .s5, .t3] u₇ u₁₂ := (p₈.trans (p₉.trans (p₁₀.trans (p₁₁.trans p₁₂)))).mono
    have b16 : Only [.t1, .s5, .t3, .s6] u₇ u₁₆ :=
      (b12.trans (p₁₃.trans (p₁₄.trans (p₁₅.trans p₁₆)))).mono
    have a15 : Only [.a7, .t1, .t2, .s5, .t3] u u₁₅ :=
      (a9.trans (p₁₀.trans (p₁₁.trans (p₁₂.trans (p₁₃.trans (p₁₄.trans p₁₅)))))).mono
    have a17 : Only [.a7, .t1, .t2, .s5, .t3, .s6] u u₁₇ := (a15.trans (p₁₆.trans p₁₇)).mono
    have c11 : Only [.a2, .t1, .s6, .t2, .a4, .a1, .a3, .t3] u₁₁ u₂₁ :=
      (p₁₂.trans (p₁₃.trans (p₁₄.trans (p₁₅.trans (p₁₆.trans (p₁₇.trans (p₁₈.trans (p₁₉.trans (p₂₀.trans
        p₂₁))))))))).mono
    have c16 : Only [.t2, .a4, .a1, .a3, .a2] u₁₆ u₂₁ :=
      (p₁₇.trans (p₁₈.trans (p₁₉.trans (p₂₀.trans p₂₁)))).mono
    have c18 : Only [.a1, .a3, .a2] u₁₈ u₂₁ := (p₁₉.trans (p₂₀.trans p₂₁)).mono
    have a18 : Only [.a7, .t1, .t2, .s5, .t3, .s6, .a4] u u₁₈ := (a17.trans p₁₈).mono
    have a20 : Only [.a7, .t1, .t2, .s5, .t3, .s6, .a4, .a1, .a3] u u₂₀ := (a18.trans (p₁₉.trans p₂₀)).mono
    refine ⟨⟨scan_step I (u₃.gpr .t1) (u₇.gpr .t2) (u₉.gpr .t1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, (o.trans q).mono⟩, ?_⟩
    · rw [f₃, f₂, hb]
    · rw [f₇, f₆, f₅, f₄, p₄.get .a7, p₃.get .a7, p₂.get .a7, hb]
    · rw [f₉, f₈, p₇.get .t1, p₆.get .t1, p₅.get .t1, p₄.get .t1]
    · rw [c11.get .s5, f₁₁, f₁₀, p₁₀.get .s5, a9.get .s5, a9.get .a4]
    · rw [c16.get .s6, f₁₆, f₁₅, f₁₄, p₁₄.get .t3, f₁₃, f₁₂, b12.get .t2, a15.get .s6, (a9.trans
        (p₁₀.trans (p₁₁.trans (p₁₂.trans p₁₃)))).get .a3, (a9.trans (p₁₀.trans (p₁₁.trans (p₁₂.trans p₁₃)))).get .a4]
    · rw [c18.get .a4, f₁₈, f₁₇, b16.get .t2, a17.get .a4]
    · rw [p₂₁.get .a1, p₂₀.get .a1, f₁₉, a18.get .a1]
    · rw [p₂₁.get .a3, f₂₀, p₁₉.get .a3, a18.get .a3]
    · rw [f₂₁, a20.get .a2]
  refine wp_or fun w ow ew => wp_nil ?_
  have kk' : Only [.a1, .a2, .a3, .a4, .s6, .t3, .t1, .t2, .a7, .s5] t w := (k₆.trans (o.trans ow)).mono
  refine ⟨h.only PF kk', by rw [kk'.mem], kk'.mono, ?_, ?_⟩
  · rw [ew, I.s5, I.a4]
  · rw [ow.get .s6]; exact I.s6

end

end VG.Proof.RsaOaep.RISCV64.Dec
