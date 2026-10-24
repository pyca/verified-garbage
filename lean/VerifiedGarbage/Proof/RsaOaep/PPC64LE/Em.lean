module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Loops
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSAES-OAEP encryption on PPC64LE: `EM` before masking

Untrusted: everything here is checked by Lean. Writes to our part of the
working space as its view (`view_wb`, `view_w8`); `encEm_ok`: `encEm`
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

/-! ## Views of writes -/

theorem view_wb (m : Mem) {S : Addr} {d o : Nat} (xs : List Byte)
    (hd : d + xs.length ≤ oRsa) (ho : o < oRsa) :
    view (writeBytes m (off S d) xs) S o = if d ≤ o ∧ o < d + xs.length then xs.getD (o - d) 0 else view m S o := by
  simp only [view, writeBytes]
  rw [Offset.sub_toNat' S (by unfold oRsa at *; omega) (by unfold oRsa at *; omega)]
  by_cases h : d ≤ o
  · rw [ifp h]
    by_cases h' : o - d < xs.length
    · rw [ifp h', ifp ⟨h, by omega⟩]
    · rw [ifn h', ifn (by omega)]
  · rw [ifn h, ifn (by unfold oRsa at *; omega), ifn (by omega)]

theorem view_w8 (m : Mem) {S : Addr} {d o : Nat} (b : Byte) (hd : d < oRsa)
    (ho : o < oRsa) : view (m.writeW (off S d) b) S o = if o = d then b else view m S o := by
  simp only [view]
  rw [writeW8_apply]
  by_cases h : o = d
  · subst h; simp
  · rw [ifn (Offset.add_ofNat_ne S (by unfold oRsa at *; omega) (by unfold oRsa at *; omega) h), ifn h]

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

theorem S_fits : (S s).toNat + oRsa ≤ 2 ^ 64 := by
  show (stackArg s 3).toNat + oRsa ≤ 2 ^ 64
  have := P.wsc; have := scLen P; omega

theorem k_lt : (s.gpr .r6).toNat ≤ 1024 := P.k2

/-- The bytes at `S + d`, `d + n ≤ oRsa`, are writable. -/
theorem sc_w {t : State} (ht : t.wr = fr s :: s.wr) {d n : Nat} (hd : d + n ≤ oRsa) :
    ∀ i < n, InRegions t.wr (off (S s) d + BitVec.ofNat 64 i) 1 := fun i hi => by
  show InRegions t.wr (off (off (S s) d) i) 1
  rw [ht, off_off]; exact sc_inW P (by omega)

omit P in
/-- Bytes of a caller's buffer are readable. -/
theorem rd_in {t : State} (ht : t.rd = s.rd) {R : Region} (hR : R ∈ s.rd) (hw : R.base.toNat + R.len ≤ 2 ^ 64)
    {n : Nat} (hn : n ≤ R.len) : ∀ j < n, InRegions (t.rd ++ t.wr) (R.base + BitVec.ofNat 64 j) 1 := fun j hj => by
  rw [ht]
  exact ⟨R, List.mem_append_left _ hR, Offset.contains_base _ (by omega) (by omega)⟩

omit P in
/-- Bytes of two disjoint regions are at different addresses. -/
theorem ne_of_dis {A B : Region} (h : A.Disjoint B) {a b : Addr} (ha : A.Contains a 1) (hb : B.Contains b 1) :
    a ≠ b := fun e => h a ha (e ▸ hb)

/-- A write of bytes to our part of the working space keeps `Base`. -/
theorem Base.wb {t w : State} {rs : List Reg} (h : Base s t) (o : Keep rs t w) {d : Nat} {xs : List Byte}
    (hd : d + xs.length ≤ oRsa) (hm : w.mem = writeBytes t.mem (off (S s) d) xs)
    (hrs : ∀ r ∈ rs, r ∉ fx ++ hiRegs := by decide) : Base s w :=
  h.keep P o (R := [⟨off (S s) d, xs.length⟩]) (by rw [hm]; exact writeBytes_frame _ _ _ (Region.contains_self _ _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in hd)) hrs

/-- `clearEm`: 1024 zeros at `S`. -/
theorem clear_ok {t : State} (h : Base s t) :
    WP isa clearEm t fun t' => Base s t' ∧ Keep [.r4, .r5, .r6] t t' ∧
      t'.mem = writeBytes t.mem (off (S s) 0) (List.replicate 1024 0) := by
  refine WP.seq (wp_addi fun t₁ o₁ e₁ => wp_li (by decide) fun t₂ o₂ e₂ => wp_li (by decide) fun t₃ o₃ e₃ =>
    wp_nil ?_)
  have k₃ : Only [.r4, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine WP.mono (zero_ok (p := off (S s) 0) (n := 1024) (b := 0) (by decide) (by decide)
    (by rw [o₃.get .r4, o₂.get .r4, e₁, h.r14]; rfl) (by rw [o₃.get .r5, e₂]) (by rw [e₃]; rfl)
    (sc_w P (by rw [k₃.wr, h.wr]) (d := 0) (by decide))) fun t' ⟨hk, hm⟩ => ?_
  have hK : Keep [.r4, .r5, .r6] t t' := (k₃.keep.trans hk).mono
  have hm' : t'.mem = writeBytes t.mem (off (S s) 0) (List.replicate 1024 0) := by rw [hm, k₃.mem]
  exact ⟨h.wb P hK (by rw [List.length_replicate]; decide) hm', hK, hm'⟩

/-- `copySeed`: the seed's `D` bytes to `S + 1`. -/
theorem seed_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD : H.D = D) (hD0 : 0 < D) (hD64 : D ≤ 64) {t : State}
    (h : Base s t) (h11 : t.gpr .r11 = stackArg s 2) :
    WP isa (copySeed H) t fun t' => Base s t' ∧ Keep [.r4, .r5, .r6, .r7] t t' ∧
      t'.mem = writeBytes t.mem (off (S s) 1) (Spec.Rsa.bytesAt s.mem (stackArg s 2) D) := by
  refine WP.seq (wp_mov fun t₁ o₁ e₁ => wp_addi fun t₂ o₂ e₂ => wp_li (by omega) fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.r4, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  have hsd : sdR D s ∈ s.rd := by rw [P.hrd]; simp
  refine WP.mono (copy_ok (q := stackArg s 2) (p := off (S s) 1) (n := D) hD0 (by omega)
    (by rw [o₃.get .r4, o₂.get .r4, e₁, h11]) (by rw [o₃.get .r5, e₂, o₁.get .r14, h.r14]; rfl) (by rw [e₃, hD])
    (rd_in (by rw [k₃.rd, h.rd]) hsd P.wsd (Nat.le_refl _))
    (sc_w P (by rw [k₃.wr, h.wr]) (d := 1) (by unfold oRsa; omega))
    (fun j hj i hi => ne_of_dis P.sds (Offset.contains_base _ (by omega) (by omega))
      (by have := scR_contains P (o := 1 + i) (n := 1) (by unfold oRsa; omega); rwa [← off_off] at this)))
    fun t' ⟨hk, hm⟩ => ?_
  have hK : Keep [.r4, .r5, .r6, .r7] t t' := (k₃.keep.trans hk).mono
  have hb : Spec.Rsa.bytesAt t₃.mem (stackArg s 2) D = Spec.Rsa.bytesAt s.mem (stackArg s 2) D := by
    rw [k₃.mem]; exact bytes_entry h.mem P.ksd ((P.sds.symm).sub_left (sc_sub P)) (by omega)
  have hm' : t'.mem = writeBytes t.mem (off (S s) 1) (Spec.Rsa.bytesAt s.mem (stackArg s 2) D) := by
    rw [hm, hb, k₃.mem]
  exact ⟨h.wb P hK (by rw [bytesAt_length]; unfold oRsa; omega) hm', hK, hm'⟩

/-- `putMsg`: `0x01` at `S + k - mLen - 1`, and the message after it. -/
theorem putMsg_ok {t : State} (h : Base s t) (h9 : t.gpr .r9 = stackArg s 0) (h10 : t.gpr .r10 = stackArg s 1)
    (hk : (stackArg s 1).toNat + 1 ≤ (s.gpr .r6).toNat) :
    WP isa putMsg t fun t' => Base s t' ∧
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
    have := S_fits P
    simp only [off, S, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, hK, hM] at this ⊢
    unfold oRsa at this; omega
  have hA : InRegions t₄.wr (t₄.gpr .r5 + BitVec.ofNat 64 0) 1 := by
    rw [o₄.get .r5, a₃, BitVec.add_zero, k₄.wr, h.wr]; exact sc_inW P (by unfold oRsa; omega)
  refine wp_stb rfl hA fun t₅ m₅ => wp_addi fun t₆ o₆ e₆ => wp_mov fun t₇ o₇ e₇ => wp_mov fun t₈ o₈ e₈ =>
    wp_nil ?_
  have k₈ : Only [.r5, .r4, .r6] t₅ t₈ := (o₆.trans (o₇.trans o₈)).mono
  have hv : (t₄.gpr .r7).setWidth 8 = (1 : Byte) := by rw [e₄]; rfl
  have m₈ : t₈.mem = t.mem.writeW (off (S s) (k - mLen - 1)) (1 : Byte) := by
    rw [k₈.mem, m₅.mem, o₄.get .r5, a₃, BitVec.add_zero, hv, k₄.mem]
  have b₈ : Base s t₈ := (h.only P k₄).keep P (m₅.keep.trans k₈.keep) (R := [⟨off (S s) (k - mLen - 1), 1⟩])
    (by rw [m₈, ← k₄.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by unfold oRsa; omega)))
  have a₈ : t₈.gpr .r5 = off (S s) (k - mLen) := by
    rw [o₈.get .r5, o₇.get .r5, e₆, m₅.gpr, o₄.get .r5, a₃]
    show off (off (S s) (k - mLen - 1)) 1 = _
    rw [off_off]; congr 2; omega
  have g6 : t₈.gpr .r6 = stackArg s 1 := by
    rw [e₈, o₇.get .r10, o₆.get .r10, m₅.gpr, k₄.get .r10, h10]
  have g4 : t₈.gpr .r4 = stackArg s 0 := by
    rw [o₈.get .r4, e₇, o₆.get .r9, m₅.gpr, k₄.get .r9, h9]
  have hb : Spec.Rsa.bytesAt t₈.mem (stackArg s 0) mLen = Spec.Rsa.bytesAt s.mem (stackArg s 0) mLen := by
    have := P.wm
    exact bytes_entry b₈.mem (hM ▸ P.km) (hM ▸ (P.ms.symm).sub_left (sc_sub P)) (by omega)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => ?_) (fun hc => ?_)
  · have hm0 : mLen ≠ 0 := by
      intro h0; rw [g6, ne_zero_iff, hM, h0] at hc; simp at hc
    refine WP.mono (copy_ok (q := stackArg s 0) (p := off (S s) (k - mLen)) (n := mLen) (by omega)
      (by omega) g4 a₈ (by rw [g6, ← hM, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (rd_in (s := s) (t := t₈) b₈.rd (R := mR s) (by rw [P.hrd]; simp) P.wm (by show mLen ≤ (stackArg s 1).toNat; omega))
      (sc_w P b₈.wr (d := k - mLen) (by unfold oRsa; omega))
      (fun j hj i hi => ne_of_dis P.ms (Offset.contains_base _ (by omega) (by omega))
        (by
          have := scR_contains P (o := k - mLen + i) (n := 1) (by unfold oRsa; omega)
          rwa [← off_off] at this))) fun t' ⟨hk', hm⟩ => ?_
    have hm' : t'.mem = writeBytes (t.mem.writeW (off (S s) (k - mLen - 1)) (1 : Byte)) (off (S s) (k - mLen))
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) mLen) := by rw [hm, hb, m₈]
    refine ⟨b₈.wb P hk' (d := k - mLen) (xs := Spec.Rsa.bytesAt s.mem (stackArg s 0) mLen)
      (by rw [bytesAt_length]; unfold oRsa; omega) (by rw [hm, hb]), hm'⟩
  · have hm0 : mLen = 0 := by
      rw [g6, ne_zero_iff, hM] at hc; simpa using hc
    subst hm0
    refine wp_nil ⟨b₈, ?_⟩
    rw [m₈]; simp [Spec.Rsa.bytesAt, writeBytes_nil]

/-- `encEm`: `EM` before masking, but for `lHash`. -/
theorem encEm_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD : H.D = D) (hD0 : 0 < D) (hD64 : D ≤ 64) {t : State}
    (E : Entered s t) (hk : 2 * D + 2 + (stackArg s 1).toNat ≤ (s.gpr .r6).toNat) :
    WP isa (encEm H) t fun t' => Base s t' ∧
      EmPart (view t'.mem (S s)) (s.gpr .r6).toNat D (Spec.Rsa.bytesAt s.mem (stackArg s 2) D)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat) (stackArg s 1).toNat := by
  refine WP.seq (WP.mono (clear_ok P E.base) fun t₁ ⟨b₁, k₁, m₁⟩ => WP.seq (WP.mono
    (seed_ok P hD hD0 hD64 b₁ (by rw [k₁.get .r11]; exact E.r11)) fun t₂ ⟨b₂, k₂, m₂⟩ => WP.mono
    (putMsg_ok P b₂ (by rw [k₂.get .r9, k₁.get .r9]; exact E.r9) (by rw [k₂.get .r10, k₁.get .r10]; exact E.r10)
      (by omega)) fun t₃ ⟨b₃, m₃⟩ => ⟨b₃, ?_⟩))
  rw [m₃, m₂, m₁]
  exact emPart_of _ _ hk P.k2 (bytesAt_length _ _ _) (bytesAt_length _ _ _)

end

end VG.Proof.RsaOaep.PPC64LE
