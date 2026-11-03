module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Priv
public import VerifiedGarbage.Proof.RsaOaep.Scan
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Label
import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem

/-!
# RSAES-OAEP decryption on RISC-V: the label and `lHash`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/Label.lean`, `Dc/Scan.lean`), with the label and
its length loaded from our stack arguments 9 and 10 (`wp_argB`): its hash to
`scratch + oDig` (`hashLabel_ok`), and the accumulator of `EM`'s first byte
and `lHash' ⊕ lHash` (`accLh_ok`, `accG`), which reads our part of the
working space only.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.Impl.RsaOaep.RISCV64.Dec
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only wp_li wp_addi wp_subi wp_mov wp_xor wp_or wp_ld wp_lbu wp_addSp wp_nil)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC Same view off offs hfits init_ok upd_ok fin_ok bytes_entry sc_in sc_inR
  cR_sub only_pres)
open VG.Proof.Bignum.RISCV64 (wp_countdown)
open VG.Proof.RsaOaep (accG)

section
variable {s : State} (P : PreD s) {m : Mem} {rc : Nat}
include P

/-- A load of our stack argument `j` through `t6`, the entry stack pointer,
in the decoding, whose memory is that after the private operation, `m`. -/
theorem wp_argB (hm : Frame [kD s, scR s] s.mem m) {u : State} {r : Reg} {j : Nat} {is : List Instr}
    {Q : State → Prop} (hj : j < 16) (h6 : u.gpr .t6 = s.sp) (hrd : u.rd = s.rd)
    (hmu : Frame [Proof.RsaOaep.RISCV64.kR s, SC (SD s) s] m u.mem)
    (k : ∀ u', Only [r] u u' → u'.gpr r = stackArg s j → WP isa (.block is) u' Q)
    (ho : 8 * j < 2048 := by decide) :
    WP isa (.block (.load .d r .t6 (8 * j) :: is)) u Q := by
  refine wp_ld (a := stackArgAddr s j) (by rw [h6]; rfl) (arg_al P hj) ?_ (fun u' o e => k u' o ?_) ho
  · rw [hrd, P.hrd]; exact ⟨aR s, by simp, in_aR hj⟩
  · rw [e, stackArg, hmu.readW (in_aR hj) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (P.ka.sub_left kR_sub).symm
        · exact (P.sa.sub_left (sc_sub P)).symm) (by decide),
      hm.readW (in_aR hj) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact P.ka.symm
        · exact P.sa.symm) (by decide)]

theorem hashLabel_ok {H : Hash} (hH : HashOK H) (hF : H.F ≤ 208) (hm : Frame [kD s, scR s] s.mem m) {t : State}
    (h : Base (SD s) (VD s rc) (withMem s m) t) :
    WP isa (Dec.hashLabel H) t fun t' => Base (SD s) (VD s rc) (withMem s m) t' ∧
      (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧ Same (Sd s) t t' [(oSt, H.S), (oDig, H.D)] ∧
      Spec.Rsa.bytesAt t'.mem (off (Sd s) oDig) H.D =
        hH.SH.H.hash (Spec.Rsa.bytesAt m (stackArg s 9) (stackArg s 10).toNat) := by
  have F := hfits hH
  have PF : Fits (SD s) (withMem s m) := fits P rfl rfl
  obtain ⟨_, _, _, _, _⟩ := offs
  have top : ∀ {u : State}, u.sp = fb s → u.sp + BitVec.ofNat 64 frameBytes = s.sp := fun hu => by
    rw [hu, BitVec.sub_add_cancel]
  refine WP.seq (wp_addi (imm := oSt) fun t₁ o₁ e₁ => wp_nil ?_)
  have b₁ := h.only PF o₁
  refine WP.seq (WP.mono (init_ok PF hH hF b₁ (by rw [e₁, h.s0])) fun t₂ ⟨b₂, g₂, s₂, r₂⟩ => ?_)
  unfold argBase
  refine WP.seq (wp_addSp (imm := frameBytes) (fun t₃ o₃ e₃ => wp_addi (imm := oSt) fun t₄ o₄ e₄ =>
    wp_li (imm := 0) (by decide) fun t₅ o₅ e₅ => ?_) (by decide))
  have K₅ : Only [.t6, .a0, .a1] t₂ t₅ := (o₃.trans (o₄.trans o₅)).mono
  have g6 : t₅.gpr .t6 = s.sp := by rw [o₅.get .t6, o₄.get .t6, e₃, top b₂.sv.sp]
  refine wp_argB P hm (j := 9) (by decide) g6 (K₅.rd.trans b₂.rd) (by rw [K₅.mem]; exact b₂.mem)
    fun t₆ o₆ e₆ => wp_argB P hm (j := 10) (by decide) (by rw [o₆.get .t6, g6])
      ((o₆.rd.trans K₅.rd).trans b₂.rd) (by rw [o₆.mem, K₅.mem]; exact b₂.mem) fun t₇ o₇ e₇ => wp_nil ?_
  have k₇ : Only [.t6, .a0, .a1, .a2, .a3] t₂ t₇ := (K₅.trans (o₆.trans o₇)).mono
  have b₇ := b₂.only PF k₇
  have hl : lR s ∈ s.rd := by rw [P.hrd]; simp
  have hb : Spec.Rsa.bytesAt t₇.mem (stackArg s 9) (stackArg s 10).toNat =
      Spec.Rsa.bytesAt m (stackArg s 9) (stackArg s 10).toNat :=
    bytes_entry b₇.mem (P.kl.sub_left kR_sub) ((P.ls.symm).sub_left (sc_sub P)) (by have := P.wl; omega)
  refine WP.seq (WP.mono (upd_ok PF hH hF b₇ (dat := stackArg s 9) (len := (stackArg s 10).toNat)
    (by rw [o₇.get .a0, o₆.get .a0, o₅.get .a0, e₄, o₃.get .s0, b₂.s0])
    (by rw [o₇.get .a2, e₆])
    (by rw [e₇])
    (Covers.left (by rw [b₇.rd]; exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact hl))
    ((P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega)))
    (P.kl.sub_left fun a ha => kR_sub a (cR_sub (withMem s m) a ha))) fun t₈ ⟨b₈, g₈, s₈, r₈⟩ => ?_)
  refine WP.seq (wp_addSp (imm := frameBytes) (fun t₉ o₉ e₉ => wp_addi (imm := oSt) fun t₁₀ o₁₀ e₁₀ => ?_)
    (by decide))
  have g6' : t₁₀.gpr .t6 = s.sp := by rw [o₁₀.get .t6, e₉, top b₈.sv.sp]
  refine wp_argB P hm (j := 10) (by decide) g6' ((o₁₀.rd.trans o₉.rd).trans b₈.rd)
    (by rw [o₁₀.mem, o₉.mem]; exact b₈.mem) fun t₁₁ o₁₁ e₁₁ =>
      wp_addi (imm := oDig) (fun t₁₂ o₁₂ e₁₂ => wp_nil ?_)
  have k₁₂ : Only [.t6, .a0, .a1, .a2] t₈ t₁₂ := (o₉.trans (o₁₀.trans (o₁₁.trans o₁₂))).mono
  have b₁₂ := b₈.only PF k₁₂
  have g1 : t₁₂.gpr .a1 = stackArg s 10 := by rw [o₁₂.get .a1, e₁₁]
  have hr : hH.SH.Repr t₁₂.mem (off (Sd s) oSt) (Spec.Rsa.bytesAt m (stackArg s 9) (stackArg s 10).toNat) := by
    rw [k₁₂.mem, ← hb]
    have := r₈ [] (by rw [k₇.mem]; exact r₂) (by rw [o₇.get .a1, o₆.get .a1, e₅]; rfl)
    simp only [List.nil_append] at this; exact this
  refine WP.mono (fin_ok PF hH hF b₁₂ (by rw [o₁₂.get .a0, o₁₁.get .a0, e₁₀, o₉.get .s0, b₈.s0])
    (by rw [e₁₂, o₁₁.get .s0, o₁₀.get .s0, o₉.get .s0, b₈.s0])) fun t' ⟨b', g', s', r'⟩ =>
      ⟨b', fun r hr' => ?_, ?_, ?_⟩
  · rw [g' r hr', only_pres k₁₂ (by decide) r hr', g₈ r hr', only_pres k₇ (by decide) r hr', g₂ r hr',
      only_pres o₁ (by decide) r hr']
  · have e : ∀ {a b : State}, a.mem = b.mem → ∀ rgs, Same (Sd s) a b rgs := fun e rgs => Same.of_mem e.symm rgs
    exact ((((((e o₁.mem.symm _).trans (s₂.mono (by simp))).trans (e k₇.mem.symm _)).trans
      (s₈.mono (by simp))).trans (e k₁₂.mem.symm _)).trans s')
  · exact r' _ hr (by rw [bytesAt_length]; have := (stackArg s 10).isLt; omega)
      (by rw [g1, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq])

/-- `acc := EM[0] ∨ ⋁ (lHash'[i] ⊕ lHash[i])`, `lHash'` at `1 + D`, `lHash` at
`oDig`. -/
theorem accLh_ok {H : Hash} {D : Nat} (hD : H.D = D) (hD0 : 0 < D) (hD64 : D ≤ 64) (hk : 2 * D + 2 ≤ kk s)
    {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) :
    WP isa (accLh H) t fun t' => Base (SD s) (VD s rc) (withMem s m) t' ∧ t'.mem = t.mem ∧
      Only [.a4, .a5, .a6, .s5, .t1, .t2] t t' ∧
      t'.gpr .s5 = accG (view t.mem (Sd s) 0) (fun i => view t.mem (Sd s) (1 + D + i))
        (fun i => view t.mem (Sd s) (oDig + i)) D := by
  obtain ⟨hE, hSt, hDg, hCt, hRs⟩ := offs
  have hk2 := P.k2
  have ek : kk s = (s.gpr .a4).toNat := rfl
  have PF : Fits (SD s) (withMem s m) := fits P rfl rfl
  subst hD
  have rdw : ∀ {u : State}, u.rd = t.rd → u.wr = t.wr → ∀ {o : Nat}, o + 1 ≤ oRsa →
      InRegions (u.rd ++ u.wr) (off (Sd s) o) 1 := fun hr hw _ ho => by
    rw [hr, hw, h.wr]; exact sc_inR PF ho _
  unfold accLh
  refine WP.seq (wp_addi (imm := oEm + 1 + H.D) (h := by omega) fun t₁ o₁ e₁ =>
    wp_addi (imm := oDig) (h := by omega) fun t₂ o₂ e₂ =>
    wp_lbu (a := off (Sd s) 0) (by rw [o₂.get .s0, o₁.get .s0, h.s0, hE])
      (rdw (o₂.rd.trans o₁.rd) (o₂.wr.trans o₁.wr) (by decide)) fun t₃ o₃ e₃ =>
    wp_li (imm := H.D) (by omega) fun t₄ o₄ e₄ => wp_nil ?_)
  have k₄ : Only [.a4, .a5, .s5, .a6] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine WP.mono (wp_countdown (cnt := .a6) (N := H.D) (by omega) hD0
    (fun i u => Only [.a4, .a5, .a6, .s5, .t1, .t2] t u ∧ u.gpr .a4 = off (Sd s) (1 + H.D + i) ∧
      u.gpr .a5 = off (Sd s) (oDig + i) ∧ u.gpr .s5 = accG (view t.mem (Sd s) 0)
        (fun i => view t.mem (Sd s) (1 + H.D + i)) (fun i => view t.mem (Sd s) (oDig + i)) i) ?_
    ⟨k₄.mono, by rw [o₄.get .a4, o₃.get .a4, o₂.get .a4, e₁, h.s0, hE]; rfl,
      by rw [o₄.get .a5, o₃.get .a5, e₂, o₁.get .s0, h.s0]; rfl,
      by rw [o₄.get .s5, e₃, o₂.mem, o₁.mem]; rfl⟩ (by rw [e₄]))
    fun u ⟨o, _, _, a⟩ => ⟨h.only PF o, o.mem, o, a⟩
  intro i hi u ⟨o, r4, r5, a⟩ _
  simp only [accBody, List.cons_append, List.nil_append]
  refine wp_lbu (a := off (Sd s) (1 + H.D + i)) (by rw [r4, BitVec.add_zero])
    (rdw o.rd o.wr (by omega)) fun u₁ p₁ f₁ => ?_
  refine wp_lbu (a := off (Sd s) (oDig + i)) (by rw [p₁.get .a5, r5, BitVec.add_zero])
    (rdw (p₁.rd.trans o.rd) (p₁.wr.trans o.wr) (by omega)) fun u₂ p₂ f₂ => ?_
  refine wp_xor fun u₃ p₃ f₃ => wp_or fun u₄ p₄ f₄ => wp_addi (imm := 1) fun u₅ p₅ f₅ =>
    wp_addi (imm := 1) fun u₆ p₆ f₆ => wp_subi (imm := 1) fun u₇ p₇ f₇ => wp_nil ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (o.trans (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans p₇))))))).mono
  · rw [p₇.get .a4, p₆.get .a4, f₅, p₄.get .a4, p₃.get .a4, p₂.get .a4, p₁.get .a4, r4]
    show off (off (Sd s) (1 + H.D + i)) 1 = off (Sd s) (1 + H.D + i + 1); exact Proof.RsaOaep.RISCV64.off_off _ _ _
  · rw [p₇.get .a5, f₆, p₅.get .a5, p₄.get .a5, p₃.get .a5, p₂.get .a5, p₁.get .a5, r5]
    show off (off (Sd s) (oDig + i)) 1 = off (Sd s) (oDig + i + 1); exact Proof.RsaOaep.RISCV64.off_off _ _ _
  · rw [p₇.get .s5, p₆.get .s5, p₅.get .s5, f₄, p₃.get .s5, p₂.get .s5, p₁.get .s5, a, f₃, p₂.get .t1, f₁,
      f₂, p₁.mem, o.mem]; rfl
  · rw [f₇, p₆.get .a6, p₅.get .a6, p₄.get .a6, p₃.get .a6, p₂.get .a6, p₁.get .a6]

end

end VG.Proof.RsaOaep.RISCV64.Dec
