module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.PrivCall
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Calls
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfT
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Proof.RsaOaep.Encode
import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Loops
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `RsaOaep.PPC64LE.Label`, which this module and modules that import it used -/

section

/-! ### `RsaOaep.PPC64LE.Em`, which this module and modules that import it used -/

section

/-!
# RSAES-OAEP encryption on PPC64LE: `EM` before masking

Untrusted: everything here is checked by Lean. `encEm_ok`: `encEm`
clears `EM`'s place and writes the seed, `0x01` and the message to it
(`EmPart`), keeping `Base`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_stb wp_li wp_addi wp_subi wp_add wp_sub wp_mov wp_nil
  eval_nonzero ne_zero_iff)
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
      rw [view_wb _ _ (by rw [List.length_replicate]; unfold oRsa; omega_arith) (by unfold oRsa; omega_arith),
        List.length_replicate, ifp (by omega_arith), getD_replicate0]
    rw [view_wb _ _ (by rw [hm]; unfold oRsa; omega_arith) (by unfold oRsa; omega_arith), hm,
      view_w8 _ _ (by unfold oRsa; omega_arith) (by unfold oRsa; omega_arith),
      view_wb _ _ (by rw [hsd]; unfold oRsa; omega_arith) (by unfold oRsa; omega_arith), hsd, e1]
  refine ⟨?_, fun i hi => ?_, fun i h₁ h₂ => ?_, ?_, fun i hi => ?_⟩
  · rw [e 0 (by omega_arith), ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith)]
  · rw [e (1 + i) (by omega_arith), ifn (by omega_arith), ifn (by omega_arith), ifp (by omega_arith), Nat.add_sub_cancel_left]
  · rw [e i (by omega_arith), ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith)]
  · rw [e _ (by omega_arith), ifn (by omega_arith), ifp rfl]
  · rw [e _ (by omega_arith), ifp (by omega_arith), Nat.add_sub_cancel_left]

section
variable {D : Nat} {s : State} (P : PreO D s)
include P

/-- `clearEm`: 1024 zeros at `S`. -/
theorem clear_ok {t : State} (h : Base S vO s t) :
    WP isa clearEm t fun t' => Base S vO s t' ∧ Keep [.r4, .r5, .r6] t t' ∧
      t'.mem = writeBytes t.mem (off (S s) 0) (List.replicate 1024 0) := by
  refine WP.seq (wp_addi fun t₁ o₁ e₁ => wp_li (by decide) fun t₂ o₂ e₂ => wp_li (by decide) fun t₃ o₃ e₃ =>
    wp_nil ?_)
  have k₃ : Only [.r4, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine WP.mono (zero_ok (p := off (S s) 0) (n := 1024) (b := 0) (by decide) (by decide)
    (by rw [o₃.get .r4, o₂.get .r4, e₁, h.r14]; rfl) (by rw [o₃.get .r5, e₂]) (by rw [e₃]; rfl)
    (sc_w P.fits (by rw [k₃.wr, h.wr]) (d := 0) (by decide))) fun t' ⟨hk, hm⟩ => ?_
  have hK : Keep [.r4, .r5, .r6] t t' := (k₃.keep.trans hk).mono
  have hm' : t'.mem = writeBytes t.mem (off (S s) 0) (List.replicate 1024 0) := by rw [hm, k₃.mem]
  exact ⟨h.wb P.fits hK (by rw [List.length_replicate]; decide) hm', hK, hm'⟩

/-- `copySeed`: the seed's `D` bytes to `S + 1`. -/
theorem seed_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD : H.D = D) (hD0 : 0 < D) (hD64 : D ≤ 64) {t : State}
    (h : Base S vO s t) (h11 : t.gpr .r11 = stackArg s 2) :
    WP isa (copySeed H) t fun t' => Base S vO s t' ∧ Keep [.r4, .r5, .r6, .r7] t t' ∧
      t'.mem = writeBytes t.mem (off (S s) 1) (Spec.Rsa.bytesAt s.mem (stackArg s 2) D) := by
  refine WP.seq (wp_mov fun t₁ o₁ e₁ => wp_addi fun t₂ o₂ e₂ => wp_li (by omega_arith) fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.r4, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  have hsd : sdR D s ∈ s.rd := by rw [P.hrd]; simp
  refine WP.mono (copy_ok (q := stackArg s 2) (p := off (S s) 1) (n := D) hD0 (by omega_arith)
    (by rw [o₃.get .r4, o₂.get .r4, e₁, h11]) (by rw [o₃.get .r5, e₂, o₁.get .r14, h.r14]; rfl) (by rw [e₃, hD])
    (rd_in (by rw [k₃.rd, h.rd]) hsd P.wsd (Nat.le_refl _))
    (sc_w P.fits (by rw [k₃.wr, h.wr]) (d := 1) (by unfold oRsa; omega_arith))
    (fun j hj i hi => ne_of_dis P.sds (Offset.contains_base _ (by omega_arith) (by omega_arith))
      (by have := scR_contains P (o := 1 + i) (n := 1) (by unfold oRsa; omega_arith); rwa [← off_off] at this)))
    fun t' ⟨hk, hm⟩ => ?_
  have hK : Keep [.r4, .r5, .r6, .r7] t t' := (k₃.keep.trans hk).mono
  have hb : Spec.Rsa.bytesAt t₃.mem (stackArg s 2) D = Spec.Rsa.bytesAt s.mem (stackArg s 2) D := by
    rw [k₃.mem]; exact bytes_entry h.mem P.ksd ((P.sds.symm).sub_left (sc_sub P)) (by omega_arith)
  have hm' : t'.mem = writeBytes t.mem (off (S s) 1) (Spec.Rsa.bytesAt s.mem (stackArg s 2) D) := by
    rw [hm, hb, k₃.mem]
  exact ⟨h.wb P.fits hK (by rw [bytesAt_length]; unfold oRsa; omega_arith) hm', hK, hm'⟩

/-- `putMsg`: `0x01` at `S + k - mLen - 1`, and the message after it. -/
theorem putMsg_ok {t : State} (h : Base S vO s t) (h9 : t.gpr .r9 = stackArg s 0) (h10 : t.gpr .r10 = stackArg s 1)
    (hk : (stackArg s 1).toNat + 1 ≤ (s.gpr .r6).toNat) :
    WP isa putMsg t fun t' => Base S vO s t' ∧
      t'.mem = writeBytes (t.mem.writeW (off (S s) ((s.gpr .r6).toNat - (stackArg s 1).toNat - 1)) (1 : Byte))
        (off (S s) ((s.gpr .r6).toNat - (stackArg s 1).toNat)) (Spec.Rsa.bytesAt s.mem (stackArg s 0)
          (stackArg s 1).toNat) := by
  have k2 := P.k2
  generalize hK : (s.gpr .r6).toNat = k at hk k2
  generalize hM : (stackArg s 1).toNat = mLen at hk
  refine WP.seq (wp_add fun t₁ o₁ e₁ => wp_sub fun t₂ o₂ e₂ => wp_subi fun t₃ o₃ e₃ => wp_li (by decide)
    fun t₄ o₄ e₄ => ?_)
  have k₄ : Only [.r5, .r7] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  have a₃ : t₃.gpr .r5 = off (S s) (k - mLen - 1) := by
    rw [e₃, e₂, e₁, o₁.get .r10, h.r14, h.r15, h10]
    apply BitVec.eq_of_toNat_eq
    have := S_fits P.fits
    simp only [off, S, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, hK, hM] at this ⊢
    unfold oRsa at this; omega_arith
  have hA : InRegions t₄.wr (t₄.gpr .r5 + BitVec.ofNat 64 0) 1 := by
    rw [o₄.get .r5, a₃, BitVec.add_zero, k₄.wr, h.wr]; exact sc_inW P.fits (by unfold oRsa; omega_arith)
  refine wp_stb rfl hA fun t₅ m₅ => wp_addi fun t₆ o₆ e₆ => wp_mov fun t₇ o₇ e₇ => wp_mov fun t₈ o₈ e₈ =>
    wp_nil ?_
  have k₈ : Only [.r5, .r4, .r6] t₅ t₈ := (o₆.trans (o₇.trans o₈)).mono
  have hv : (t₄.gpr .r7).setWidth 8 = (1 : Byte) := by rw [e₄]; rfl
  have m₈ : t₈.mem = t.mem.writeW (off (S s) (k - mLen - 1)) (1 : Byte) := by
    rw [k₈.mem, m₅.mem, o₄.get .r5, a₃, BitVec.add_zero, hv, k₄.mem]
  have b₈ : Base S vO s t₈ := (h.only P.fits k₄).keep P.fits (m₅.keep.trans k₈.keep) (R := [⟨off (S s) (k - mLen - 1), 1⟩])
    (by rw [m₈, ← k₄.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by unfold oRsa; omega_arith)))
  have a₈ : t₈.gpr .r5 = off (S s) (k - mLen) := by
    rw [o₈.get .r5, o₇.get .r5, e₆, m₅.gpr, o₄.get .r5, a₃]
    show off (off (S s) (k - mLen - 1)) 1 = _
    rw [off_off]; congr 2; omega_arith
  have g6 : t₈.gpr .r6 = stackArg s 1 := by
    rw [e₈, o₇.get .r10, o₆.get .r10, m₅.gpr, k₄.get .r10, h10]
  have g4 : t₈.gpr .r4 = stackArg s 0 := by
    rw [o₈.get .r4, e₇, o₆.get .r9, m₅.gpr, k₄.get .r9, h9]
  have hb : Spec.Rsa.bytesAt t₈.mem (stackArg s 0) mLen = Spec.Rsa.bytesAt s.mem (stackArg s 0) mLen := by
    have := P.wm
    exact bytes_entry b₈.mem (hM ▸ P.km) (hM ▸ (P.ms.symm).sub_left (sc_sub P)) (by omega_arith)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => ?_) (fun hc => ?_)
  · have hm0 : mLen ≠ 0 := by
      intro h0; rw [g6, ne_zero_iff, hM, h0] at hc; simp at hc
    refine WP.mono (copy_ok (q := stackArg s 0) (p := off (S s) (k - mLen)) (n := mLen) (by omega_arith)
      (by omega_arith) g4 a₈ (by rw [g6, ← hM, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (rd_in (s := s) (t := t₈) b₈.rd (R := mR s) (by rw [P.hrd]; simp) P.wm (by show mLen ≤ (stackArg s 1).toNat; omega_arith))
      (sc_w P.fits b₈.wr (d := k - mLen) (by unfold oRsa; omega_arith))
      (fun j hj i hi => ne_of_dis P.ms (Offset.contains_base _ (by omega_arith) (by omega_arith))
        (by
          have := scR_contains P (o := k - mLen + i) (n := 1) (by unfold oRsa; omega_arith)
          rwa [← off_off] at this))) fun t' ⟨hk', hm⟩ => ?_
    have hm' : t'.mem = writeBytes (t.mem.writeW (off (S s) (k - mLen - 1)) (1 : Byte)) (off (S s) (k - mLen))
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) mLen) := by rw [hm, hb, m₈]
    refine ⟨b₈.wb P.fits hk' (d := k - mLen) (xs := Spec.Rsa.bytesAt s.mem (stackArg s 0) mLen)
      (by rw [bytesAt_length]; unfold oRsa; omega_arith) (by rw [hm, hb]), hm'⟩
  · have hm0 : mLen = 0 := by
      rw [g6, ne_zero_iff, hM] at hc; simpa using hc
    subst hm0
    refine wp_nil ⟨b₈, ?_⟩
    rw [m₈]; simp [Spec.Rsa.bytesAt, writeBytes_nil]

/-- `encEm`: `EM` before masking, but for `lHash`. -/
theorem encEm_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD : H.D = D) (hD0 : 0 < D) (hD64 : D ≤ 64) {t : State}
    (E : Entered s t) (hk : 2 * D + 2 + (stackArg s 1).toNat ≤ (s.gpr .r6).toNat) :
    WP isa (encEm H) t fun t' => Base S vO s t' ∧
      EmPart (view t'.mem (S s)) (s.gpr .r6).toNat D (Spec.Rsa.bytesAt s.mem (stackArg s 2) D)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat) (stackArg s 1).toNat := by
  refine WP.seq (WP.mono (clear_ok P E.base) fun t₁ ⟨b₁, k₁, m₁⟩ => WP.seq (WP.mono
    (seed_ok P hD hD0 hD64 b₁ (by rw [k₁.get .r11]; exact E.r11)) fun t₂ ⟨b₂, k₂, m₂⟩ => WP.mono
    (putMsg_ok P b₂ (by rw [k₂.get .r9, k₁.get .r9]; exact E.r9) (by rw [k₂.get .r10, k₁.get .r10]; exact E.r10)
      (by omega_arith)) fun t₃ ⟨b₃, m₃⟩ => ⟨b₃, ?_⟩))
  rw [m₃, m₂, m₁]
  exact emPart_of _ _ hk P.k2 (bytesAt_length _ _ _) (bytesAt_length _ _ _)

end

end VG.Proof.RsaOaep.PPC64LE

end

end

/-!
# RSAES-OAEP encryption on PPC64LE: the label's hash

Untrusted: everything here is checked by Lean. `hashLabelT_ok`:
`hashLabelT` writes what the streaming `finalize` of the hash function `H`
of the table that is our stack argument `j` writes for the label to
`S + oDig`, each call through the table running as `H`'s (`initT_ok`,
`updT_ok`, `finT_ok`); `copyLh_ok`: `copyLh` copies its first `hLen` bytes, `lHash`,
to `EM + 1 + hLen`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.WriteBytes
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_mov wp_nil)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.RsaOaep.PPC64LE (Fns hashLabelT)

/-- An `Only` step keeps the callee-saved registers it does not write. -/
theorem only_pres {rs : List Reg} {t t' : State} (o : Only rs t t') (hrs : ∀ r ∈ rs, r ∉ preserved := by decide) :
    ∀ r ∈ preserved, t'.gpr r = t.gpr r := fun r hr => o.gpr r fun h => hrs r h hr

section
variable {D : Nat} {s : State} (P : PreO D s)
include P

/-- `hashLabelT`, with the hash function `H` of the table that is our stack
argument `j`: what `finalize` writes for the label, to `S + oDig`. -/
theorem hashLabelT_ok {H : Hash} (hH : HashOK H) {f : Fns} {j : Nat} {p : Addr} (T : TabS H f j S s p) {t : State}
    (h : Base S vO s t) (sy : t.syms = s.syms) :
    WP isa (hashLabelT f j .r19 .r20) t fun t' => (Base S vO s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S), (oDig, H.FD), (oW, H.W)] ∧
      Spec.Rsa.bytesAt t'.mem (off (S s) oDig) H.FD =
        hH.fh (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat)) ∧ t'.syms = s.syms := by
  have F := hfits hH
  obtain ⟨_, _, _, _, _, _⟩ := offs
  refine WP.seq (WP.of_syms (wp_addi fun t₁ o₁ e₁ => wp_nil fun y₁ => ?_))
  have b₁ := h.only P.fits o₁
  refine WP.seq (WP.mono (initT_ok P.fits T hH b₁ (y₁.trans sy) (by rw [e₁, h.r14]))
    fun t₂ ⟨⟨b₂, g₂, s₂, r₂⟩, y₂⟩ => ?_)
  refine WP.seq (WP.of_syms (wp_addi fun t₃ o₃ e₃ => wp_li (by decide) fun t₄ o₄ e₄ => wp_mov fun t₅ o₅ e₅ =>
    wp_mov fun t₆ o₆ e₆ => wp_addi fun t₇ o₇ e₇ => wp_nil fun y₇ => ?_))
  have k₇ : Only [.r3, .r4, .r5, .r6, .r7] t₂ t₇ := (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))).mono
  have b₇ := b₂.only P.fits k₇
  have hl : lR s ∈ s.rd := by rw [P.hrd]; simp
  have hb : Spec.Rsa.bytesAt t₇.mem (s.gpr .r9) (s.gpr .r10).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat :=
    bytes_entry b₇.mem P.kl ((P.ls.symm).sub_left (sc_sub P)) (by have := P.wl; omega_arith)
  refine WP.seq (WP.mono (updT_ok P.fits T hH b₇ (y₇.trans y₂) (dat := s.gpr .r9) (len := (s.gpr .r10).toNat)
    (by rw [o₇.get .r3, o₆.get .r3, o₅.get .r3, o₄.get .r3, e₃, b₂.r14])
    (by rw [o₇.get .r5, o₆.get .r5, e₅, o₄.get .r19, o₃.get .r19, b₂.r19])
    (by rw [o₇.get .r6, e₆, o₅.get .r20, o₄.get .r20, o₃.get .r20, b₂.r20])
    (by rw [e₇, o₆.get .r14, o₅.get .r14, o₄.get .r14, o₃.get .r14, b₂.r14])
    (Covers.left (by rw [b₇.rd]; exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact hl))
    ((P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega_arith)))
    ((P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega_arith)))
    (P.kl.sub_left (cR_sub s))) fun t₈ ⟨⟨b₈, g₈, s₈, r₈⟩, y₈⟩ => ?_)
  refine WP.seq (WP.of_syms (wp_addi fun t₉ o₉ e₉ => wp_mov fun t₁₀ o₁₀ e₁₀ => wp_addi fun t₁₁ o₁₁ e₁₁ =>
    wp_addi fun t₁₂ o₁₂ e₁₂ => wp_nil fun y₁₂ => ?_))
  have k₁₂ : Only [.r3, .r4, .r5, .r6] t₈ t₁₂ := (o₉.trans (o₁₀.trans (o₁₁.trans o₁₂))).mono
  have b₁₂ := b₈.only P.fits k₁₂
  have g4 : t₁₂.gpr .r4 = s.gpr .r10 := by
    rw [o₁₂.get .r4, o₁₁.get .r4, e₁₀, o₉.get .r20, b₈.r20]
  have hr : hH.SH.Repr t₁₂.mem (off (S s) oSt) (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat) := by
    rw [k₁₂.mem, ← hb]
    have := r₈ [] (by rw [k₇.mem]; exact r₂) (by rw [o₇.get .r4, o₆.get .r4, o₅.get .r4, e₄]; rfl)
    simp only [List.nil_append] at this; exact this
  refine WP.mono (finT_ok P.fits T hH b₁₂ (y₁₂.trans y₈) (by rw [o₁₂.get .r3, o₁₁.get .r3, o₁₀.get .r3, e₉, b₈.r14])
    (by rw [o₁₂.get .r5, e₁₁, o₁₀.get .r14, o₉.get .r14, b₈.r14]) (by rw [e₁₂, o₁₁.get .r14, o₁₀.get .r14,
      o₉.get .r14, b₈.r14])) fun t' ⟨⟨b', g', s', r'⟩, y'⟩ => ⟨⟨b', fun r hr' => ?_, ?_, ?_⟩, y'⟩
  · rw [g' r hr', only_pres k₁₂ (by decide) r hr', g₈ r hr', only_pres k₇ (by decide) r hr', g₂ r hr',
      only_pres o₁ (by decide) r hr']
  · have e : ∀ {a b : State}, a.mem = b.mem → ∀ rgs, Same (S s) a b rgs := fun e rgs => Same.of_mem e.symm rgs
    exact ((((((e o₁.mem.symm _).trans (s₂.mono (by simp))).trans (e k₇.mem.symm _)).trans
      (s₈.mono (by simp))).trans (e k₁₂.mem.symm _)).trans s')
  · exact r' _ hr (by rw [bytesAt_length]; have := (s.gpr .r10).isLt; omega_arith)
      (by rw [g4, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq])

/-- `copyLh`: the first `hLen` bytes at `S + oDig` to `EM + 1 + hLen`. -/
theorem copyLh_ok {H : Hash} (hH : HashOK H) (hD : H.D = D) {t : State} (h : Base S vO s t) :
    WP isa (copyLh H) t fun t' => Base S vO s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      t'.mem = writeBytes t.mem (off (S s) (1 + D)) (Spec.Rsa.bytesAt t.mem (off (S s) oDig) D) := by
  have F := hfits hH
  obtain ⟨_, _, _, _, _, _⟩ := offs
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  subst hD
  refine WP.seq (wp_addi fun t₁ o₁ e₁ => wp_addi (h := by unfold oEm; omega_arith) fun t₂ o₂ e₂ =>
    wp_li (by omega_arith) fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.r4, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine WP.mono (copy_ok (q := off (S s) oDig) (p := off (S s) (1 + H.D)) (n := H.D) hD0 (by omega_arith)
    (by rw [o₃.get .r4, o₂.get .r4, e₁, h.r14]) (by rw [o₃.get .r5, e₂, o₁.get .r14, h.r14]; show off (S s) (oEm + 1 + H.D) = _; congr 2)
    (by rw [e₃]) (fun j hj => by
      rw [k₃.rd, k₃.wr, h.wr]
      show InRegions _ (off (off (S s) oDig) j) 1
      rw [off_off]; exact sc_inR P.fits (by omega_arith) _)
    (sc_w P.fits (by rw [k₃.wr, h.wr]) (d := 1 + H.D) (by omega_arith))
    (fun j hj i hi => by
      show off (off (S s) oDig) j ≠ off (off (S s) (1 + H.D)) i
      rw [off_off, off_off]
      exact Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) (by omega_arith))) fun t' ⟨hk, hm⟩ => ?_
  have hK : Keep [.r4, .r5, .r6, .r7] t t' := (k₃.keep.trans hk).mono
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
  z0 := by rw [hV 0 (by omega_arith), ifn (by omega_arith)]; exact hp.z0
  sd i hi := by rw [hV _ (by omega_arith), ifn (by omega_arith)]; exact hp.sd i hi
  lh i hi := by rw [hV _ (by omega_arith), ifp (by omega_arith), Nat.add_sub_cancel_left]
  ps i h₁ h₂ := by rw [hV _ (by omega_arith), ifn (by omega_arith)]; exact hp.ps i (by omega_arith) h₂
  one := by rw [hV _ (by omega_arith), ifn (by omega_arith)]; exact hp.one
  msg i hi := by rw [hV _ (by omega_arith), ifn (by omega_arith)]; exact hp.msg i hi


end VG.Proof.RsaOaep.PPC64LE

end

end

/-!
# RSAES-OAEP decryption on PPC64LE: the label's hash

Untrusted: everything here is checked by Lean. In the decoding, whose
`Base` is relative to the entry state with memory `m` (`withMem s m`),
`hashLabelT_ok`: `init`, `update` with the label (`r18`, `r19`) and
`finalize`, through the table that is our stack argument 15, of the hash
function `H` (`initT_ok`, `updT_ok`, `finT_ok`), write `H(label)`, as
`finalize` writes it, to `scratch + oDig`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep wp_li wp_mov wp_addi wp_nil)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Impl.RsaOaep.PPC64LE (Fns hashLabelT)

section
variable {pc : Bool} {s : State} (P : PreD pc s) {m : Mem} {rc : Nat}
include P

theorem fitsM : Fits (SD s) (withMem s m) := fits P rfl rfl

/-- A buffer the decoding only reads, apart from the stack and `scratch`: as
in `m`. -/
theorem bytes_m {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) {R : Region} (hk : (kD s).Disjoint R)
    (hs : (scR s).Disjoint R) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt m R.base R.len :=
  bytes_entry h.mem (hk.sub_left kR_sub) (hs.sub_left (sc_sub P)) hl

theorem hashLabelT_ok {H : Hash} (hH : HashOK H) {f : Fns} {p : Addr} (T : TabS H f 15 (SD s) (withMem s m) p)
    {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) (sy : t.syms = s.syms) :
    WP isa (hashLabelT f 15 .r18 .r19) t fun t' => (Base (SD s) (VD s rc) (withMem s m) t' ∧
      (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧ Same (Sd s) t t' [(oSt, H.S), (oDig, H.FD), (oW, H.W)] ∧
      Spec.Rsa.bytesAt t'.mem (off (Sd s) oDig) H.FD =
        hH.fh (Spec.Rsa.bytesAt m (stackArg s 9) (stackArg s 10).toNat)) ∧ t'.syms = s.syms := by
  have F := hfits hH
  have PF := fitsM (m := m) P
  obtain ⟨_, _, _, _, _, _⟩ := offs
  refine WP.seq (WP.of_syms (wp_addi fun t₁ o₁ e₁ => wp_nil fun y₁ => ?_))
  have b₁ := h.only PF o₁
  refine WP.seq (WP.mono (initT_ok PF T hH b₁ (y₁.trans sy) (by rw [e₁, h.r14])) fun t₂ ⟨⟨b₂, g₂, s₂, r₂⟩, y₂⟩ => ?_)
  refine WP.seq (WP.of_syms (wp_addi fun t₃ o₃ e₃ => wp_li (by decide) fun t₄ o₄ e₄ => wp_mov fun t₅ o₅ e₅ =>
    wp_mov fun t₆ o₆ e₆ => wp_addi fun t₇ o₇ e₇ => wp_nil fun y₇ => ?_))
  have k₇ : Only [.r3, .r4, .r5, .r6, .r7] t₂ t₇ := (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))).mono
  have b₇ := b₂.only PF k₇
  have hl : lR s ∈ (withMem s m).rd := by show lR s ∈ s.rd; rw [P.hrd]; simp
  have hb : Spec.Rsa.bytesAt t₇.mem (stackArg s 9) (stackArg s 10).toNat =
      Spec.Rsa.bytesAt m (stackArg s 9) (stackArg s 10).toNat :=
    bytes_m P b₇ (R := lR s) P.kl P.ls.symm (by show (stackArg s 10).toNat ≤ _; have := (stackArg s 10).isLt; omega_using [])
  refine WP.seq (WP.mono (updT_ok PF T hH b₇ (y₇.trans y₂) (dat := stackArg s 9) (len := (stackArg s 10).toNat)
    (by rw [o₇.get .r3, o₆.get .r3, o₅.get .r3, o₄.get .r3, e₃, b₂.r14])
    (by rw [o₇.get .r5, o₆.get .r5, e₅, o₄.get .r18, o₃.get .r18, Base.r18 b₂])
    (by rw [o₇.get .r6, e₆, o₅.get .r19, o₄.get .r19, o₃.get .r19, Base.r19 b₂])
    (by rw [e₇, o₆.get .r14, o₅.get .r14, o₄.get .r14, o₃.get .r14, b₂.r14])
    (Covers.left (by rw [b₇.rd]; exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact hl))
    ((P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega_arith)))
    ((P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega_arith)))
    (P.kl.sub_left fun a ha => kR_sub a (cR_sub (withMem s m) a ha))) fun t₈ ⟨⟨b₈, g₈, s₈, r₈⟩, y₈⟩ => ?_)
  refine WP.seq (WP.of_syms (wp_addi fun t₉ o₉ e₉ => wp_mov fun t₁₀ o₁₀ e₁₀ => wp_addi fun t₁₁ o₁₁ e₁₁ =>
    wp_addi fun t₁₂ o₁₂ e₁₂ => wp_nil fun y₁₂ => ?_))
  have k₁₂ : Only [.r3, .r4, .r5, .r6] t₈ t₁₂ := (o₉.trans (o₁₀.trans (o₁₁.trans o₁₂))).mono
  have b₁₂ := b₈.only PF k₁₂
  have g4 : t₁₂.gpr .r4 = stackArg s 10 := by
    rw [o₁₂.get .r4, o₁₁.get .r4, e₁₀, o₉.get .r19, Base.r19 b₈]
  have hr : hH.SH.Repr t₁₂.mem (off (Sd s) oSt) (Spec.Rsa.bytesAt m (stackArg s 9) (stackArg s 10).toNat) := by
    rw [k₁₂.mem, ← hb]
    have := r₈ [] (by rw [k₇.mem]; exact r₂) (by rw [o₇.get .r4, o₆.get .r4, o₅.get .r4, e₄]; rfl)
    simp only [List.nil_append] at this; exact this
  refine WP.mono (finT_ok PF T hH b₁₂ (y₁₂.trans y₈) (by rw [o₁₂.get .r3, o₁₁.get .r3, o₁₀.get .r3, e₉, b₈.r14])
    (by rw [o₁₂.get .r5, e₁₁, o₁₀.get .r14, o₉.get .r14, b₈.r14]) (by rw [e₁₂, o₁₁.get .r14, o₁₀.get .r14,
      o₉.get .r14, b₈.r14])) fun t' ⟨⟨b', g', s', r'⟩, y'⟩ => ⟨⟨b', fun r hr' => ?_, ?_, ?_⟩, y'⟩
  · rw [g' r hr', only_pres k₁₂ (by decide) r hr', g₈ r hr', only_pres k₇ (by decide) r hr', g₂ r hr',
      only_pres o₁ (by decide) r hr']
  · have e : ∀ {a b : State}, a.mem = b.mem → ∀ rgs, Same (Sd s) a b rgs := fun e rgs => Same.of_mem e.symm rgs
    exact ((((((e o₁.mem.symm _).trans (s₂.mono (by simp))).trans (e k₇.mem.symm _)).trans
      (s₈.mono (by simp))).trans (e k₁₂.mem.symm _)).trans s')
  · exact r' _ hr (by rw [bytesAt_length]; have := (stackArg s 10).isLt; omega_using [])
      (by rw [g4, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq])

end

end VG.Proof.RsaOaep.PPC64LE.Dec
