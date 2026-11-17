module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.MgfT
public import VerifiedGarbage.Proof.RsaOaep.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Pre
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Encode
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `RsaOaep.RISCV64.Label`, which this module and modules that import it used -/

section

/-! ### `RsaOaep.RISCV64.Em`, which this module and modules that import it used -/

section

/-!
# RSAES-OAEP encryption on RISC-V: `EM` before masking

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/Label.lean`): `encEm_ok`, `encEm` clears `EM`'s place
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
      rw [view_wb _ _ (by rw [List.length_replicate]; unfold oRsa; omega_using []) (by unfold oRsa; omega_using [ho]),
        List.length_replicate, ifp (by omega_using [ho]), getD_replicate0]
    rw [view_wb _ _ (by rw [hm]; unfold oRsa; omega_using [hk, hk2]) (by unfold oRsa; omega_using [ho]), hm,
      view_w8 _ _ (by unfold oRsa; omega_using [hk2]) (by unfold oRsa; omega_using [ho]),
      view_wb _ _ (by rw [hsd]; unfold oRsa; omega_using [hk, hk2]) (by unfold oRsa; omega_using [ho]), hsd, e1]
  refine ⟨?_, fun i hi => ?_, fun i h₁ h₂ => ?_, ?_, fun i hi => ?_⟩
  · rw [e 0 (by omega_using []), ifn (by omega_using [hk]), ifn (by omega_using [hk]), ifn (by omega_using [])]
  · rw [e (1 + i) (by omega_using [hk, hk2, hi]), ifn (by omega_using [hk, hi]), ifn (by omega_using [hk, hi]), ifp (by omega_using [hi]), Nat.add_sub_cancel_left]
  · rw [e i (by omega_using [hk2, h₂]), ifn (by omega_using [h₂]), ifn (by omega_using [h₂]), ifn (by omega_using [h₁])]
  · rw [e _ (by omega_using [hk2]), ifn (by omega_using [hk]), ifp rfl]
  · rw [e _ (by omega_using [hk, hk2, hi]), ifp (by omega_using [hi]), Nat.add_sub_cancel_left]

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
    wp_li (imm := H.D) (by omega_using [hD, hD64]) fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.a4, .a1, .a5] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  have hsd : sdR D s ∈ s.rd := by rw [P.hrd]; simp
  refine WP.mono (copy_ok (q := stackArg s 2) (p := off (S s) 1) (n := D) hD0 (by omega_using [hD64])
    (by rw [o₃.get .a1, e₂, o₁.get .s0, h.s0]; rfl) (by rw [o₃.get .a4, o₂.get .a4, e₁, h4]) (by rw [e₃, hD])
    (rd_in (by rw [k₃.rd, h.rd]) hsd P.wsd (Nat.le_refl _))
    (sc_w P.fits (by rw [k₃.wr, h.wr]) (d := 1) (by unfold oRsa; omega_using [hD64]))
    (fun j hj i hi => ne_of_dis P.sds (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hD64, hj]))
      (by have := scR_contains P (o := 1 + i) (n := 1) (by unfold oRsa; omega_using [hD64, hi]); rwa [← off_off] at this)))
    fun t' ⟨hk, hm⟩ => ?_
  have hK : Kept [.t0, .a4, .a1, .a5] t t' := (k₃.keep.trans hk).mono
  have hb : Spec.Rsa.bytesAt t₃.mem (stackArg s 2) D = Spec.Rsa.bytesAt s.mem (stackArg s 2) D := by
    rw [k₃.mem]; exact bytes_entry h.mem P.ksd ((P.sds.symm).sub_left (sc_sub P)) (by omega_using [hD64])
  have hm' : t'.mem = writeBytes t.mem (off (S s) 1) (Spec.Rsa.bytesAt s.mem (stackArg s 2) D) := by
    rw [hm, hb, k₃.mem]
  exact ⟨h.wb P.fits hK (by rw [bytesAt_length]; unfold oRsa; omega_using [hD64]) hm', hK, hm'⟩

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
    unfold oRsa at this; omega_using [hK, hk]
  have hA : InRegions t₄.wr (t₄.gpr .a1 + BitVec.ofNat 64 0) 1 := by
    rw [o₄.get .a1, a₃, BitVec.add_zero, k₄.wr, h.wr]; exact sc_inW P.fits (by unfold oRsa; omega_using [k2])
  refine wp_sb rfl hA fun t₅ m₅ => wp_addi (imm := 1) fun t₆ o₆ e₆ => wp_mov fun t₇ o₇ e₇ =>
    wp_mov fun t₈ o₈ e₈ => wp_nil ?_
  have k₈ : Only [.a1, .a4, .a5] t₅ t₈ := (o₆.trans (o₇.trans o₈)).mono
  have hv : (t₄.gpr .t1).setWidth 8 = (1 : Byte) := by rw [e₄]; rfl
  have m₈ : t₈.mem = t.mem.writeW (off (S s) (k - mLen - 1)) (1 : Byte) := by
    rw [k₈.mem, m₅.mem, o₄.get .a1, a₃, BitVec.add_zero, hv, k₄.mem]
  have b₈ : Base S vO s t₈ := (h.only P.fits k₄).keep P.fits (m₅.keep.trans k₈.keep)
    (R := [⟨off (S s) (k - mLen - 1), 1⟩])
    (by rw [m₈, ← k₄.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by unfold oRsa; omega_using [k2])))
  have a₈ : t₈.gpr .a1 = off (S s) (k - mLen) := by
    rw [o₈.get .a1, o₇.get .a1, e₆, m₅.gpr, o₄.get .a1, a₃]
    show off (off (S s) (k - mLen - 1)) 1 = _
    rw [off_off]; congr 2; omega_using [hk]
  have g5 : t₈.gpr .a5 = stackArg s 1 := by
    rw [e₈, o₇.get .t3, o₆.get .t3, m₅.gpr, k₄.get .t3, h3]
  have g4 : t₈.gpr .a4 = stackArg s 0 := by
    rw [o₈.get .a4, e₇, o₆.get .t2, m₅.gpr, k₄.get .t2, h2]
  have hb : Spec.Rsa.bytesAt t₈.mem (stackArg s 0) mLen = Spec.Rsa.bytesAt s.mem (stackArg s 0) mLen := by
    have := P.wm
    exact bytes_entry b₈.mem (hM ▸ P.km) (hM ▸ (P.ms.symm).sub_left (sc_sub P)) (by omega_using [hM])
  refine WP.ite _ (eval_nonzero _ _) (fun hc => ?_) (fun hc => ?_)
  · have hm0 : mLen ≠ 0 := by
      intro h0; rw [g5, ne_zero_iff, hM, h0] at hc; simp at hc
    refine WP.mono (copy_ok (q := stackArg s 0) (p := off (S s) (k - mLen)) (n := mLen) (by omega_using [hm0])
      (by omega_using [hM]) a₈ g4 (by rw [g5, ← hM, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (rd_in (s := s) (t := t₈) b₈.rd (R := mR s) (by rw [P.hrd]; simp) P.wm
        (by show mLen ≤ (stackArg s 1).toNat; omega_using [hM]))
      (sc_w P.fits b₈.wr (d := k - mLen) (by unfold oRsa; omega_using [k2, hk]))
      (fun j hj i hi => ne_of_dis P.ms (Offset.contains_base _ (by omega_using [hM, hj]) (by omega_using [hM, hj]))
        (by
          have := scR_contains P (o := k - mLen + i) (n := 1) (by unfold oRsa; omega_using [k2, hk, hi])
          rwa [← off_off] at this))) fun t' ⟨hk', hm⟩ => ?_
    have hm' : t'.mem = writeBytes (t.mem.writeW (off (S s) (k - mLen - 1)) (1 : Byte)) (off (S s) (k - mLen))
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) mLen) := by rw [hm, hb, m₈]
    exact ⟨b₈.wb P.fits hk' (d := k - mLen) (xs := Spec.Rsa.bytesAt s.mem (stackArg s 0) mLen)
      (by rw [bytesAt_length]; unfold oRsa; omega_using [k2, hk]) (by rw [hm, hb]),
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
      (by omega_using [hk])) fun t₃ ⟨b₃, g6, g7, m₃⟩ => ⟨b₃, by rw [g6, k₂.get .s6, k₁.get .s6, E.s6],
        by rw [g7, k₂.get .s7, k₁.get .s7, E.s7], ?_⟩))
  rw [m₃, m₂, m₁]
  exact emPart_of _ _ hk P.k2 (bytesAt_length _ _ _) (bytesAt_length _ _ _)

end

end VG.Proof.RsaOaep.RISCV64

end

end

/-!
# RSAES-OAEP encryption on RISC-V: the label's hash

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/Label.lean`): `hashLabelT_ok`, `hashLabelT` writes
`H` of the label (in `s6` and `s7`) to `S + oDig`, for the hash function `H`
of the table that is our stack argument `j`, each call through the table
running as `H`'s (`initT_ok`, `updT_ok`, `finT_ok`); `copyLh_ok`, `copyLh`
copies its `hLen` bytes, `lHash`, to `EM + 1 + hLen`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.WriteBytes
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_addi wp_mov wp_nil copy_ok)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.RsaOaep.RISCV64 (Fns hashLabelT labU labF)

/-- An `Only` step keeps the callee-saved registers it does not write. -/
theorem only_pres {rs : List Reg} {t t' : State} (o : Only rs t t') (hrs : ∀ r ∈ rs, r ∉ preserved := by decide) :
    ∀ r ∈ preserved, t'.gpr r = t.gpr r := fun r hr => o.gpr r fun h => hrs r h hr

section
variable {D : Nat} {s : State} (P : PreO D s)
include P

/-- `hashLabelT`, with the hash function `H` of the table that is our stack
argument `j`: `H` of the label, to `S + oDig`. -/
theorem hashLabelT_ok {H : Hash} (hH : HashOK H) (hF : H.F ≤ 208) {f : Fns} {j : Nat} {p : Addr}
    (T : TabS H f j S s p) {t : State} (h : Base S vO s t) (sy : t.syms = s.syms)
    (h6 : t.gpr .s6 = s.gpr .a6) (h7 : t.gpr .s7 = s.gpr .a7) :
    WP isa (hashLabelT f j labU labF) t fun t' => (Base S vO s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S), (oDig, H.D)] ∧
      Spec.Rsa.bytesAt t'.mem (off (S s) oDig) H.D =
        hH.SH.H.hash (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat)) ∧ t'.syms = s.syms := by
  have F := hfits hH
  obtain ⟨_, _, _, _, _⟩ := offs
  refine WP.seq (WP.of_syms (wp_addi (imm := oSt) fun t₁ o₁ e₁ => wp_nil fun y₁ => ?_))
  have b₁ := h.only P.fits o₁
  refine WP.seq (WP.mono (initT_ok P.fits T hH hF b₁ (y₁.trans sy) (by rw [e₁, h.s0]))
    fun t₂ ⟨⟨b₂, g₂, s₂, r₂⟩, y₂⟩ => ?_)
  refine WP.seq (WP.of_syms (wp_addi (imm := oSt) fun t₃ o₃ e₃ => wp_li (imm := 0) (by decide) fun t₄ o₄ e₄ =>
    wp_mov fun t₅ o₅ e₅ => wp_mov fun t₆ o₆ e₆ => wp_nil fun y₆ => ?_))
  have k₆ : Only [.a0, .a1, .a2, .a3] t₂ t₆ := (o₃.trans (o₄.trans (o₅.trans o₆))).mono
  have b₆ := b₂.only P.fits k₆
  have hl : lR s ∈ s.rd := by rw [P.hrd]; simp
  have hb : Spec.Rsa.bytesAt t₆.mem (s.gpr .a6) (s.gpr .a7).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat :=
    bytes_entry b₆.mem P.kl ((P.ls.symm).sub_left (sc_sub P)) (by have := P.wl; omega_using [])
  have p6 : t₂.gpr .s6 = s.gpr .a6 := by rw [g₂ .s6 (by decide), o₁.get .s6, h6]
  have p7 : t₂.gpr .s7 = s.gpr .a7 := by rw [g₂ .s7 (by decide), o₁.get .s7, h7]
  refine WP.seq (WP.mono (updT_ok P.fits T hH hF b₆ (y₆.trans y₂) (dat := s.gpr .a6) (len := (s.gpr .a7).toNat)
    (by rw [o₆.get .a0, o₅.get .a0, o₄.get .a0, e₃, b₂.s0])
    (by rw [o₆.get .a2, e₅, o₄.get .s6, o₃.get .s6, p6])
    (by rw [e₆, o₅.get .s7, o₄.get .s7, o₃.get .s7, p7])
    (Covers.left (by rw [b₆.rd]; exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact hl))
    ((P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega_arith)))
    (P.kl.sub_left (cR_sub s))) fun t₇ ⟨⟨b₇, g₇, s₇, r₇⟩, y₇⟩ => ?_)
  refine WP.seq (WP.of_syms (wp_addi (imm := oSt) fun t₈ o₈ e₈ => wp_mov fun t₉ o₉ e₉ =>
    wp_addi (imm := oDig) fun t₁₀ o₁₀ e₁₀ => wp_nil fun y₁₀ => ?_))
  have k₁₀ : Only [.a0, .a1, .a2] t₇ t₁₀ := (o₈.trans (o₉.trans o₁₀)).mono
  have b₁₀ := b₇.only P.fits k₁₀
  have g1 : t₁₀.gpr .a1 = s.gpr .a7 := by
    rw [o₁₀.get .a1, e₉, o₈.get .s7, g₇ .s7 (by decide), k₆.get .s7, p7]
  have hr : hH.SH.Repr t₁₀.mem (off (S s) oSt) (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat) := by
    rw [k₁₀.mem, ← hb]
    have := r₇ [] (by rw [k₆.mem]; exact r₂) (by rw [o₆.get .a1, o₅.get .a1, e₄]; rfl)
    simp only [List.nil_append] at this; exact this
  refine WP.mono (finT_ok P.fits T hH hF b₁₀ (y₁₀.trans y₇) (by rw [o₁₀.get .a0, o₉.get .a0, e₈, b₇.s0])
    (by rw [e₁₀, o₉.get .s0, o₈.get .s0, b₇.s0])) fun t' ⟨⟨b', g', s', r'⟩, y'⟩ => ⟨⟨b', fun r hr' => ?_, ?_, ?_⟩, y'⟩
  · rw [g' r hr', only_pres k₁₀ (by decide) r hr', g₇ r hr', only_pres k₆ (by decide) r hr', g₂ r hr',
      only_pres o₁ (by decide) r hr']
  · have e : ∀ {a b : State}, a.mem = b.mem → ∀ rgs, Same (S s) a b rgs := fun e rgs => Same.of_mem e.symm rgs
    exact ((((((e o₁.mem.symm _).trans (s₂.mono (by simp))).trans (e k₆.mem.symm _)).trans
      (s₇.mono (by simp))).trans (e k₁₀.mem.symm _)).trans s')
  · exact r' _ hr (by rw [bytesAt_length]; have := (s.gpr .a7).isLt; omega_using [])
      (by rw [g1, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq])

/-- `copyLh`: the first `hLen` bytes at `S + oDig` to `EM + 1 + hLen`. -/
theorem copyLh_ok {H : Hash} (hH : HashOK H) (hD : H.D = D) {t : State} (h : Base S vO s t) :
    WP isa (copyLh H) t fun t' => Base S vO s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      t'.mem = writeBytes t.mem (off (S s) (1 + D)) (Spec.Rsa.bytesAt t.mem (off (S s) oDig) D) := by
  have F := hfits hH
  obtain ⟨_, _, _, _, _⟩ := offs
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  subst hD
  refine WP.seq (wp_addi (imm := oDig) fun t₁ o₁ e₁ =>
    wp_addi (imm := oEm + 1 + H.D) (h := by unfold oEm; omega_using [F]) fun t₂ o₂ e₂ =>
    wp_li (imm := H.D) (by omega_using [F]) fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.a4, .a1, .a5] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine WP.mono (copy_ok (q := off (S s) oDig) (p := off (S s) (1 + H.D)) (n := H.D) hD0 (by omega_using [F])
    (by rw [o₃.get .a1, e₂, o₁.get .s0, h.s0]; show off (S s) (oEm + 1 + H.D) = _; congr 2)
    (by rw [o₃.get .a4, o₂.get .a4, e₁, h.s0]) (by rw [e₃]) (fun j hj => by
      rw [k₃.rd, k₃.wr, h.wr]
      show InRegions _ (off (off (S s) oDig) j) 1
      rw [off_off]; exact sc_inR P.fits (by omega_arith) _)
    (sc_w P.fits (by rw [k₃.wr, h.wr]) (d := 1 + H.D) (by omega_arith))
    (fun j hj i hi => by
      show off (off (S s) oDig) j ≠ off (off (S s) (1 + H.D)) i
      rw [off_off, off_off]
      exact Offset.add_ofNat_ne _ (by omega_arith) (by omega_using [F, hi]) (by omega_arith))) fun t' ⟨hk, hm⟩ => ?_
  have hK : Kept [.t0, .a4, .a1, .a5] t t' := (k₃.keep.trans hk).mono
  have hm' : t'.mem = writeBytes t.mem (off (S s) (1 + H.D)) (Spec.Rsa.bytesAt t.mem (off (S s) oDig) H.D) := by
    rw [hm, k₃.mem]
  exact ⟨h.wb P.fits hK (by rw [bytesAt_length]; omega_arith) hm', fun r hr => hK.gpr r (by revert r; decide), hm'⟩

end

/-- `EM` before masking, from its part before `lHash` and `lHash` written
after it. -/
theorem emAt_of {V V' : Nat → Byte} {k D mLen : Nat} {sd lh m : List Byte} (hp : EmPart V k D sd m mLen)
    (hk : 2 * D + 2 + mLen ≤ k) (hk2 : k ≤ 1024)
    (hV : ∀ o < 1024, V' o = if 1 + D ≤ o ∧ o < 1 + D + D then lh.getD (o - (1 + D)) 0 else V o) :
    RsaOaep.EmAt V' k D sd lh m mLen where
  z0 := by rw [hV 0 (by omega_using []), ifn (by omega_using [])]; exact hp.z0
  sd i hi := by rw [hV _ (by omega_using [hk, hk2, hi]), ifn (by omega_using [hi])]; exact hp.sd i hi
  lh i hi := by rw [hV _ (by omega_using [hk, hk2, hi]), ifp (by omega_using [hi]), Nat.add_sub_cancel_left]
  ps i h₁ h₂ := by rw [hV _ (by omega_using [hk2, h₂]), ifn (by omega_using [h₁])]; exact hp.ps i (by omega_using [h₁]) h₂
  one := by rw [hV _ (by omega_using [hk2]), ifn (by omega_using [hk])]; exact hp.one
  msg i hi := by rw [hV _ (by omega_using [hk, hk2, hi]), ifn (by omega_using [hk])]; exact hp.msg i hi

end VG.Proof.RsaOaep.RISCV64

end

end

/-!
# RSAES-OAEP encryption on RISC-V: `EM`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Main.lean`): `em_ok`, `EM` before masking (`encEm`,
the label's hash and `copyLh`, as `RsaOaep.EmAt`); `mask_ok`, `DB` masked
with MGF1 of the seed and the seed with MGF1 of `maskedDB`, which leaves
EME-OAEP's encoding at `S` (`RsaOaep.emOf`, by `RsaOaep.em_mask`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.WriteBytes
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_addi wp_subi wp_mov wp_nil)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.RsaOaep (mixV srcB EmAt emOf em_mask)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.RsaOaep.RISCV64 (hashLabelT labU labF)

/-- The seed's and the message's bytes, the label's, and the message's length,
from the entry state. -/
abbrev seedB (D : Nat) (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 2) D
abbrev msgB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat
abbrev labB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat
abbrev kk (s : State) : Nat := (s.gpr .a3).toNat
abbrev mLen (s : State) : Nat := (stackArg s 1).toNat

theorem sub_k {x : BitVec 64} {a : Nat} (h : a ≤ x.toNat) : x - BitVec.ofNat 64 a = BitVec.ofNat 64 (x.toNat - a) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := a) (by omega_using [h]), Nat.mod_eq_of_lt (a := x.toNat - a) (by omega_using [])]; omega_using [h]

section
variable {D : Nat} {s : State} (P : PreO D s)
include P

/-- `EM` before masking: `encEm`, the label's hash and `copyLh`. -/
theorem em_ok {H : Hash} (hH : HashOK H) (hF : H.F ≤ 208) {f : Fns} (TL : TabS H f 8 S s (stackArg s 8))
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hD : H.D = D) {t : State} (E : Entered s t)
    (hsy : t.syms = s.syms) (hk : 2 * D + 2 + mLen s ≤ kk s) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ t', Base S vO s t' → t'.syms = t.syms →
      EmAt (view t'.mem (S s)) (kk s) D (seedB D s) (Hs.hash (labB s)) (msgB s) (mLen s) → WP isa rest t' Q) :
    WP isa (.seq (encEm H) (.seq (hashLabelT f 8 labU labF) (.seq (copyLh H) rest))) t Q := by
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  have F := hfits hH
  obtain ⟨_, hSt, hDg, hCt, hRs⟩ := offs
  refine WP.seq (WP.mono_syms (encEm_ok P hD (by omega) (by omega) E hk) fun t₁ ⟨b₁, g6, g7, hp⟩ y₁ => ?_)
  refine WP.seq (WP.mono (hashLabelT_ok P hH hF TL b₁ (y₁.trans hsy) g6 g7) fun t₂ ⟨⟨b₂, _, s₂, d₂⟩, y₂⟩ => ?_)
  refine WP.seq (WP.mono_syms (copyLh_ok P hH hD b₂) fun t₃ ⟨b₃, _, m₃⟩ y₃ =>
    k t₃ b₃ (y₃.trans (y₂.trans hsy.symm)) ?_)
  have hlh : Spec.Rsa.bytesAt t₂.mem (off (S s) oDig) D = Hs.hash (labB s) := by
    rw [hHh, ← d₂, ← hD]
  refine emAt_of hp hk P.k2 fun o ho => ?_
  rw [m₃, view_wb _ _ (by rw [bytesAt_length]; omega) (by omega_using [hRs, ho]), bytesAt_length, hlh,
    s₂ o (by omega_using [hRs, ho]) (by simp; omega_using [hSt, hDg, ho])]

omit P in
/-- The bytes at `S`, from the view. -/
theorem bytesAt_S (m : Mem) (S : Addr) (n : Nat) :
    Spec.Rsa.bytesAt m (off S 0) n = (List.range n).map (view m S) := by
  rw [bytesAt_view]; simp only [srcB, Nat.zero_add]

/-- `DB` masked with MGF1 of the seed, then the seed with MGF1 of `maskedDB`:
EME-OAEP's encoding at `S`. -/
theorem mask_ok {H G : Hash} (hG : HashOK G) (hF : G.F ≤ 208) {f : Fns}
    (T : TabS G f 9 S s (stackArg s 9)) {Gs : Spec.Mgf1.Hash}
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) (hD : H.D = D)
    (hD0 : 0 < D) (hD64 : D ≤ 64) {sd lh m : List Byte} (hsd : sd.length = D) (hlh : lh.length = D)
    (hm : m.length = mLen s) (hk : 2 * D + 2 + mLen s ≤ kk s) {t : State} (h : Base S vO s t)
    (hsy : t.syms = s.syms) (he : EmAt (view t.mem (S s)) (kk s) D sd lh m (mLen s)) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ t', Base S vO s t' → Spec.Rsa.bytesAt t'.mem (off (S s) 0) (kk s) = emOf Gs D (kk s) (mLen s) sd lh m →
      WP isa rest t' Q) :
    WP isa (.seq (.block (dbArgs H)) (.seq (mgfXorT f 9) (.seq (.block (seedArgs H)) (.seq (mgfXorT f 9) rest)))) t Q :=
    by
  obtain ⟨hE, hSt, hDg, hCt, hRs⟩ := offs
  have hk2 := P.k2
  have ek : kk s = (s.gpr .a3).toNat := rfl
  subst hD
  -- `DB` with MGF1 of the seed.
  refine WP.seq (WP.of_syms (wp_addi (imm := oEm + 1) (h := by omega_using [hE]) fun t₁ o₁ e₁ => wp_li (imm := H.D) (by omega_using [hD64])
    fun t₂ o₂ e₂ => wp_addi (imm := oEm + 1 + H.D) (h := by omega_using [hE, hD64]) fun t₃ o₃ e₃ =>
    wp_subi (imm := H.D + 1) (h := by omega_using [hD64]) fun t₄ o₄ e₄ => wp_nil fun y₄ => ?_))
  have k₄ : Only [.s6, .s7, .s8, .s9] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  have b₄ := h.only P.fits k₄
  refine WP.seq (WP.mono (mgfXorT_ok P.fits hG hF T hGh hGl hGv (src := 1) (srcLen := H.D) (dst := 1 + H.D)
    (dstLen := kk s - H.D - 1) ⟨by omega_using [hD64], by omega_using [hk2, ek, hD64], .inl (by omega_using []), by omega_using [hk]⟩ b₄ (y₄.trans hsy)
    (by rw [o₄.get .s6, o₃.get .s6, o₂.get .s6, e₁, h.s0, hE])
    (by rw [o₄.get .s7, o₃.get .s7, e₂])
    (by rw [o₄.get .s8, e₃, o₂.get .s0, o₁.get .s0, h.s0, hE, Nat.zero_add])
    (by rw [e₄, o₃.get .s1, o₂.get .s1, o₁.get .s1, h.s1, sub_k (by omega_using [ek, hk])]; congr 1))
    fun t₅ ⟨⟨b₅, v₅⟩, y₅⟩ => ?_)
  -- The seed with MGF1 of `maskedDB`.
  refine WP.seq (WP.of_syms (wp_addi (imm := oEm + 1 + H.D) (h := by omega_using [hE, hD64]) fun t₆ o₆ e₆ =>
    wp_subi (imm := H.D + 1) (h := by omega_using [hD64]) fun t₇ o₇ e₇ => wp_addi (imm := oEm + 1) (h := by omega_using [hE])
    fun t₈ o₈ e₈ => wp_li (imm := H.D) (by omega_using [hD64]) fun t₉ o₉ e₉ => wp_nil fun y₉ => ?_))
  have k₉ : Only [.s6, .s7, .s8, .s9] t₅ t₉ := (o₆.trans (o₇.trans (o₈.trans o₉))).mono
  have b₉ := b₅.only P.fits k₉
  refine WP.seq (WP.mono (mgfXorT_ok P.fits hG hF T hGh hGl hGv (src := 1 + H.D) (srcLen := kk s - H.D - 1)
    (dst := 1) (dstLen := H.D) ⟨by omega_using [hk2, ek, hD64], by omega_using [hD64], .inr (by omega_using []), by omega_using [hD0]⟩ b₉ (y₉.trans y₅)
    (by rw [o₉.get .s6, o₈.get .s6, o₇.get .s6, e₆, b₅.s0, hE, Nat.zero_add])
    (by rw [o₉.get .s7, o₈.get .s7, e₇, o₆.get .s1, b₅.s1, sub_k (by omega_using [ek, hk])]; congr 1)
    (by rw [o₉.get .s8, e₈, o₇.get .s0, o₆.get .s0, b₅.s0, hE])
    (by rw [e₉]))
    fun t₁₀ ⟨⟨b₁₀, v₁₀⟩, _⟩ => k t₁₀ b₁₀ ?_)
  -- `EM`.
  have hdb := he.db hlh hm hk
  generalize hDB : lh ++ Spec.RsaOaep.zeros (kk s - mLen s - 2 * H.D - 2) ++ 0x01 :: m = db at hdb
  have hdbl : db.length = kk s - H.D - 1 := by
    rw [← hDB]; simp [Spec.RsaOaep.zeros, hlh, hm]; omega_using [hk]
  have V4 : view t₄.mem (S s) = view t.mem (S s) := by rw [k₄.mem]
  have V9 : view t₉.mem (S s) = view t₅.mem (S s) := by rw [k₉.mem]
  rw [V4] at v₅
  rw [V9] at v₁₀
  have hsrc : srcB (view t₅.mem (S s)) (1 + H.D) (kk s - H.D - 1) =
      srcB (mixV (view t.mem (S s)) (Spec.Mgf1.mgf1 Gs (srcB (view t.mem (S s)) 1 H.D) (kk s - H.D - 1)) (1 + H.D)
        (kk s - H.D - 1)) (1 + H.D) (kk s - H.D - 1) :=
    List.map_congr_left fun i hi => v₅ _ ⟨by have := List.mem_range.mp hi; omega_using [hRs, hk2, ek, this], .inl (by have := List.mem_range.mp hi; omega_using [hSt, hk2, ek, this])⟩
  rw [bytesAt_S]
  refine (List.map_congr_left fun i hi => ?_).trans ((em_mask hGv (by omega_using [hk]) hsd hdbl he.z0 he.sd hdb).trans ?_)
  · have hi := List.mem_range.mp hi
    rw [v₁₀ i ⟨by omega_using [hRs, hk2, ek, hi], .inl (by omega_using [hSt, hk2, ek, hi])⟩, hsrc, mixV, mixV]
    split
    · rw [v₅ i ⟨by omega_arith, .inl (by omega_arith)⟩]
    · rw [v₅ i ⟨by omega_using [hRs, hk2, ek, hi], .inl (by omega_using [hSt, hk2, ek, hi])⟩]
  · rw [← hDB]; rfl

end

end VG.Proof.RsaOaep.RISCV64
