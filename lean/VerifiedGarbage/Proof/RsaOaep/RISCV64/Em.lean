module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Pre
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSAES-OAEP encryption on RISC-V: `EM` before masking

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Em.lean`): `encEm_ok`, `encEm` clears `EM`'s place
and writes the seed, `0x01` and the message to it (`EmPart`), keeping
`Base`, with RSASSA-PKCS1-v1_5's loops (`fill_ok`, `copy_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_sb wp_li wp_addi wp_subi wp_add wp_sub wp_mov wp_nil
  eval_nonzero ne_zero_iff fill_ok copy_ok)
open VG.Proof.RsaPkcs1Sig (bytesAt_length writeBytes_out)
open VG.Proof.Mgf1 (ifp ifn)

/-! ## `EM` before masking -/

/-- `EM` before masking, but for `lHash`: `0x00 ‖ seed ‖ 0… ‖ 0x01 ‖ M`. -/
structure EmPart (V : Nat → Byte) (k D : Nat) (sd m : List Byte) (mLen : Nat) : Prop where
  z0 : V 0 = 0
  sd : ∀ i < D, V (1 + i) = sd.getD i 0
  ps : ∀ i, 1 + D ≤ i → i < k - mLen - 1 → V i = 0
  one : V (k - mLen - 1) = 1
  msg : ∀ i < mLen, V (k - mLen + i) = m.getD i 0

theorem getD_replicate0 (n i : Nat) : (List.replicate n (0 : Byte)).getD i 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl

/-- The writes of `encEm`, as `EM` before masking. -/
theorem emPart_of (m₀ : Mem) (S : Addr) {k D mLen : Nat} (hk : 2 * D + 2 + mLen ≤ k) (hk2 : k ≤ 1024)
    {sd msg : List Byte} (hsd : sd.length = D) (hm : msg.length = mLen) :
    EmPart (view (writeBytes ((writeBytes (writeBytes m₀ (off S 0) (List.replicate 1024 0)) (off S 1) sd).writeW
      (off S (k - mLen - 1)) (1 : Byte)) (off S (k - mLen)) msg) S) k D sd msg mLen := by
  have e : ∀ o < 1024, view (writeBytes ((writeBytes (writeBytes m₀ (off S 0) (List.replicate 1024 0)) (off S 1)
      sd).writeW (off S (k - mLen - 1)) (1 : Byte)) (off S (k - mLen)) msg) S o =
      if k - mLen ≤ o ∧ o < k - mLen + mLen then msg.getD (o - (k - mLen)) 0 else
        if o = k - mLen - 1 then 1 else if 1 ≤ o ∧ o < 1 + D then sd.getD (o - 1) 0 else 0 := by
    intro o ho
    have e1 : view (writeBytes m₀ (off S 0) (List.replicate 1024 0)) S o = 0 := by
      rw [view_wb _ _ (by rw [List.length_replicate]; unfold oRsa; omega) (by unfold oRsa; omega),
        List.length_replicate, ifp (by omega), getD_replicate0]
    rw [view_wb _ _ (by rw [hm]; unfold oRsa; omega) (by unfold oRsa; omega), hm,
      view_w8 _ _ (by unfold oRsa; omega) (by unfold oRsa; omega),
      view_wb _ _ (by rw [hsd]; unfold oRsa; omega) (by unfold oRsa; omega), hsd, e1]
  refine ⟨?_, fun i hi => ?_, fun i h₁ h₂ => ?_, ?_, fun i hi => ?_⟩
  · rw [e 0 (by omega), ifn (by omega), ifn (by omega), ifn (by omega)]
  · rw [e (1 + i) (by omega), ifn (by omega), ifn (by omega), ifp (by omega), Nat.add_sub_cancel_left]
  · rw [e i (by omega), ifn (by omega), ifn (by omega), ifn (by omega)]
  · rw [e _ (by omega), ifn (by omega), ifp rfl]
  · rw [e _ (by omega), ifp (by omega), Nat.add_sub_cancel_left]

section
variable {D : Nat} {s : State} (P : PreO D s)
include P

/-- `clearEm`: 1024 zeros at `S`. -/
theorem clear_ok {t : State} (h : Base S vO s t) :
    WP isa clearEm t fun t' => Base S vO s t' ∧ Kept [.a1, .t5, .t0] t t' ∧
      t'.mem = writeBytes t.mem (off (S s) 0) (List.replicate 1024 0) := by
  refine WP.seq (wp_addi (imm := oEm) fun t₁ o₁ e₁ => wp_li (imm := 1024) (by decide) fun t₂ o₂ e₂ =>
    wp_li (imm := 0) (by decide) fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.a1, .t5, .t0] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine WP.mono (fill_ok (p := off (S s) 0) (n := 1024) (b := 0) (by decide) (by decide)
    (by rw [o₃.get .a1, o₂.get .a1, e₁, h.s0]; rfl) (by rw [o₃.get .t5, e₂]) (by rw [e₃]; rfl)
    (sc_w P.fits (by rw [k₃.wr, h.wr]) (d := 0) (by decide))) fun t' ⟨hk, hm⟩ => ?_
  have hK : Kept [.a1, .t5, .t0] t t' := (k₃.keep.trans hk).mono
  have hm' : t'.mem = writeBytes t.mem (off (S s) 0) (List.replicate 1024 0) := by rw [hm, k₃.mem]
  exact ⟨h.wb P.fits hK (by rw [List.length_replicate]; decide) hm', hK, hm'⟩

/-- `copySeed`: the seed's `D` bytes to `S + 1`. -/
theorem seed_ok {H : Impl.Hmac.Stream.RISCV64.Hash} (hD : H.D = D) (hD0 : 0 < D) (hD64 : D ≤ 64) {t : State}
    (h : Base S vO s t) (h4 : t.gpr .t4 = stackArg s 2) :
    WP isa (copySeed H) t fun t' => Base S vO s t' ∧ Kept [.t0, .a4, .a1, .a5] t t' ∧
      t'.mem = writeBytes t.mem (off (S s) 1) (Spec.Rsa.bytesAt s.mem (stackArg s 2) D) := by
  refine WP.seq (wp_mov fun t₁ o₁ e₁ => wp_addi (imm := oEm + 1) fun t₂ o₂ e₂ =>
    wp_li (imm := H.D) (by omega) fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.a4, .a1, .a5] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  have hsd : sdR D s ∈ s.rd := by rw [P.hrd]; simp
  refine WP.mono (copy_ok (q := stackArg s 2) (p := off (S s) 1) (n := D) hD0 (by omega)
    (by rw [o₃.get .a1, e₂, o₁.get .s0, h.s0]; rfl) (by rw [o₃.get .a4, o₂.get .a4, e₁, h4]) (by rw [e₃, hD])
    (rd_in (by rw [k₃.rd, h.rd]) hsd P.wsd (Nat.le_refl _))
    (sc_w P.fits (by rw [k₃.wr, h.wr]) (d := 1) (by unfold oRsa; omega))
    (fun j hj i hi => ne_of_dis P.sds (Offset.contains_base _ (by omega) (by omega))
      (by have := scR_contains P (o := 1 + i) (n := 1) (by unfold oRsa; omega); rwa [← off_off] at this)))
    fun t' ⟨hk, hm⟩ => ?_
  have hK : Kept [.t0, .a4, .a1, .a5] t t' := (k₃.keep.trans hk).mono
  have hb : Spec.Rsa.bytesAt t₃.mem (stackArg s 2) D = Spec.Rsa.bytesAt s.mem (stackArg s 2) D := by
    rw [k₃.mem]; exact bytes_entry h.mem P.ksd ((P.sds.symm).sub_left (sc_sub P)) (by omega)
  have hm' : t'.mem = writeBytes t.mem (off (S s) 1) (Spec.Rsa.bytesAt s.mem (stackArg s 2) D) := by
    rw [hm, hb, k₃.mem]
  exact ⟨h.wb P.fits hK (by rw [bytesAt_length]; unfold oRsa; omega) hm', hK, hm'⟩

/-- `putMsg`: `0x01` at `S + k - mLen - 1`, and the message after it. -/
theorem putMsg_ok {t : State} (h : Base S vO s t) (h2 : t.gpr .t2 = stackArg s 0) (h3 : t.gpr .t3 = stackArg s 1)
    (hk : (stackArg s 1).toNat + 1 ≤ (s.gpr .a3).toNat) :
    WP isa putMsg t fun t' => Base S vO s t' ∧ t'.gpr .s6 = t.gpr .s6 ∧ t'.gpr .s7 = t.gpr .s7 ∧
      t'.mem = writeBytes (t.mem.writeW (off (S s) ((s.gpr .a3).toNat - (stackArg s 1).toNat - 1)) (1 : Byte))
        (off (S s) ((s.gpr .a3).toNat - (stackArg s 1).toNat)) (Spec.Rsa.bytesAt s.mem (stackArg s 0)
          (stackArg s 1).toNat) := by
  have k2 := P.k2
  generalize hK : (s.gpr .a3).toNat = k at hk k2
  generalize hM : (stackArg s 1).toNat = mLen at hk
  refine WP.seq (wp_add fun t₁ o₁ e₁ => wp_sub fun t₂ o₂ e₂ => wp_subi (imm := 1) fun t₃ o₃ e₃ =>
    wp_li (imm := 1) (by decide) fun t₄ o₄ e₄ => ?_)
  have k₄ : Only [.a1, .t1] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  have a₃ : t₃.gpr .a1 = off (S s) (k - mLen - 1) := by
    rw [e₃, e₂, e₁, o₁.get .t3, h.s0, h.s1, h3]
    apply BitVec.eq_of_toNat_eq
    have := (PreO.fits P).wS
    simp only [off, S, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, hK, hM] at this ⊢
    unfold oRsa at this; omega
  have hA : InRegions t₄.wr (t₄.gpr .a1 + BitVec.ofNat 64 0) 1 := by
    rw [o₄.get .a1, a₃, BitVec.add_zero, k₄.wr, h.wr]; exact sc_inW P.fits (by unfold oRsa; omega)
  refine wp_sb rfl hA fun t₅ m₅ => wp_addi (imm := 1) fun t₆ o₆ e₆ => wp_mov fun t₇ o₇ e₇ =>
    wp_mov fun t₈ o₈ e₈ => wp_nil ?_
  have k₈ : Only [.a1, .a4, .a5] t₅ t₈ := (o₆.trans (o₇.trans o₈)).mono
  have hv : (t₄.gpr .t1).setWidth 8 = (1 : Byte) := by rw [e₄]; rfl
  have m₈ : t₈.mem = t.mem.writeW (off (S s) (k - mLen - 1)) (1 : Byte) := by
    rw [k₈.mem, m₅.mem, o₄.get .a1, a₃, BitVec.add_zero, hv, k₄.mem]
  have b₈ : Base S vO s t₈ := (h.only P.fits k₄).keep P.fits (m₅.keep.trans k₈.keep)
    (R := [⟨off (S s) (k - mLen - 1), 1⟩])
    (by rw [m₈, ← k₄.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by unfold oRsa; omega)))
  have a₈ : t₈.gpr .a1 = off (S s) (k - mLen) := by
    rw [o₈.get .a1, o₇.get .a1, e₆, m₅.gpr, o₄.get .a1, a₃]
    show off (off (S s) (k - mLen - 1)) 1 = _
    rw [off_off]; congr 2; omega
  have g5 : t₈.gpr .a5 = stackArg s 1 := by
    rw [e₈, o₇.get .t3, o₆.get .t3, m₅.gpr, k₄.get .t3, h3]
  have g4 : t₈.gpr .a4 = stackArg s 0 := by
    rw [o₈.get .a4, e₇, o₆.get .t2, m₅.gpr, k₄.get .t2, h2]
  have hb : Spec.Rsa.bytesAt t₈.mem (stackArg s 0) mLen = Spec.Rsa.bytesAt s.mem (stackArg s 0) mLen := by
    have := P.wm
    exact bytes_entry b₈.mem (hM ▸ P.km) (hM ▸ (P.ms.symm).sub_left (sc_sub P)) (by omega)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => ?_) (fun hc => ?_)
  · have hm0 : mLen ≠ 0 := by
      intro h0; rw [g5, ne_zero_iff, hM, h0] at hc; simp at hc
    refine WP.mono (copy_ok (q := stackArg s 0) (p := off (S s) (k - mLen)) (n := mLen) (by omega)
      (by omega) a₈ g4 (by rw [g5, ← hM, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (rd_in (s := s) (t := t₈) b₈.rd (R := mR s) (by rw [P.hrd]; simp) P.wm
        (by show mLen ≤ (stackArg s 1).toNat; omega))
      (sc_w P.fits b₈.wr (d := k - mLen) (by unfold oRsa; omega))
      (fun j hj i hi => ne_of_dis P.ms (Offset.contains_base _ (by omega) (by omega))
        (by
          have := scR_contains P (o := k - mLen + i) (n := 1) (by unfold oRsa; omega)
          rwa [← off_off] at this))) fun t' ⟨hk', hm⟩ => ?_
    have hm' : t'.mem = writeBytes (t.mem.writeW (off (S s) (k - mLen - 1)) (1 : Byte)) (off (S s) (k - mLen))
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) mLen) := by rw [hm, hb, m₈]
    exact ⟨b₈.wb P.fits hk' (d := k - mLen) (xs := Spec.Rsa.bytesAt s.mem (stackArg s 0) mLen)
      (by rw [bytesAt_length]; unfold oRsa; omega) (by rw [hm, hb]),
      by rw [hk'.get .s6, k₈.get .s6, m₅.gpr, k₄.get .s6], by rw [hk'.get .s7, k₈.get .s7, m₅.gpr, k₄.get .s7], hm'⟩
  · have hm0 : mLen = 0 := by
      rw [g5, ne_zero_iff, hM] at hc; simpa using hc
    subst hm0
    refine wp_nil ⟨b₈, by rw [k₈.get .s6, m₅.gpr, k₄.get .s6], by rw [k₈.get .s7, m₅.gpr, k₄.get .s7], ?_⟩
    rw [m₈]; simp [Spec.Rsa.bytesAt, writeBytes_nil]

/-- `encEm`: `EM` before masking, but for `lHash`. -/
theorem encEm_ok {H : Impl.Hmac.Stream.RISCV64.Hash} (hD : H.D = D) (hD0 : 0 < D) (hD64 : D ≤ 64) {t : State}
    (E : Entered s t) (hk : 2 * D + 2 + (stackArg s 1).toNat ≤ (s.gpr .a3).toNat) :
    WP isa (encEm H) t fun t' => Base S vO s t' ∧ t'.gpr .s6 = s.gpr .a6 ∧ t'.gpr .s7 = s.gpr .a7 ∧
      EmPart (view t'.mem (S s)) (s.gpr .a3).toNat D (Spec.Rsa.bytesAt s.mem (stackArg s 2) D)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat) (stackArg s 1).toNat := by
  refine WP.seq (WP.mono (clear_ok P E.base) fun t₁ ⟨b₁, k₁, m₁⟩ => WP.seq (WP.mono
    (seed_ok P hD hD0 hD64 b₁ (by rw [k₁.get .t4]; exact E.t4)) fun t₂ ⟨b₂, k₂, m₂⟩ => WP.mono
    (putMsg_ok P b₂ (by rw [k₂.get .t2, k₁.get .t2]; exact E.t2) (by rw [k₂.get .t3, k₁.get .t3]; exact E.t3)
      (by omega)) fun t₃ ⟨b₃, g6, g7, m₃⟩ => ⟨b₃, by rw [g6, k₂.get .s6, k₁.get .s6, E.s6],
        by rw [g7, k₂.get .s7, k₁.get .s7, E.s7], ?_⟩))
  rw [m₃, m₂, m₁]
  exact emPart_of _ _ hk P.k2 (bytesAt_length _ _ _) (bytesAt_length _ _ _)

end

end VG.Proof.RsaOaep.RISCV64
