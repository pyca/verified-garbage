module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.RecoverCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.RecoverMask
import VerifiedGarbage.Proof.RsaPkcs1Sig.Recover
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# `vg_rsa_pkcs1_recover_precomputed` on PPC64LE: correctness

After the call (`AfterCall`), the status is kept in the frame and `encode`
writes to `EM₂` the encoding of the last `out_len` bytes of `EM₁`. If that
fails, `out` is zeroed and the result is 0; if not, those bytes are copied
to `out`, and `out` and the result are masked with whether the encoding is
`EM₁` and the call succeeded (`afterPub_ok`): if `pre` holds the modulus'
values, recovery by encoding (`Proof.RsaPkcs1Sig.recover_eq_recoverEnc`).
As on AArch64 (`Proof/RsaPkcs1Sig/AArch64/RecPcTail.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Rec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.RecoverPrecomputed VG.WriteBytes
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_writeBytes frame_writeBytes ne_of_disjoint bytesAt_drop)

/-! ## The specification -/

/-- The result and `out`, from the entry state `s`: the octets `recover`
returns, or zeros. -/
def Post (s s' : State) : Prop :=
  abiPreserved s s' ∧ (PreOk s → ∀ h, Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .r9).setWidth 32).toNat = some h →
    Spec.Rsa.written s'.mem (s.gpr .r3) (s.gpr .r4).toNat ((s'.gpr .r3).setWidth 32)
      (Spec.RsaPkcs1Sig.recover (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) h
        (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat)))

/-- `EM₁` after the call `t`. -/
abbrev em1 (s t : State) : List Byte := Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .r6).toNat

/-- The encoding of `EM₁`'s last `out_len` bytes. -/
def encOut (s t : State) : Option (List Byte) :=
  encodeId ((s.gpr .r9).setWidth 32) ((em1 s t).drop ((s.gpr .r6).toNat - (s.gpr .r4).toNat)) (s.gpr .r6).toNat

/-- `recover`, by encoding, as the call's result gives it. -/
theorem recover_eq {s t : State} (hp : PreR s) (hsig : stackArg s 0 = s.gpr .r6)
    (hres : Spec.Rsa.written t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .r6).toNat ((t.gpr .r3).setWidth 32)
      (pubOut s)) {h : Spec.RsaPkcs1Sig.Hash} (hh : Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .r9).setWidth 32).toNat = some h) :
    Spec.RsaPkcs1Sig.recover (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) h
        (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat) =
      match pubOut s, encOut s t with
      | some em, some em' => if em = em' then some (em.drop ((s.gpr .r6).toNat - (s.gpr .r4).toNat)) else none
      | _, _ => none := by
  obtain ⟨h', hh', hL⟩ := hp.hh
  rw [hh] at hh'; cases hh'
  rw [Proof.RsaPkcs1Sig.recover_eq_recoverEnc, Proof.RsaPkcs1Sig.recoverEnc, bytesAt_length, bytesAt_length, hsig,
    ite_eq_left rfl]
  unfold encOut encodeId
  rw [hh, ← hL]
  change (match pubOut s with | some em => _ | none => none) = _
  cases hpo : pubOut s with
  | none => rfl
  | some em =>
    rw [hpo] at hres
    have he1 : em1 s t = em := hres.2
    rw [he1]
    dsimp only
    cases he : Spec.RsaPkcs1Sig.encode h (em.drop ((s.gpr .r6).toNat - (s.gpr .r4).toNat)) (s.gpr .r6).toNat with
    | none => simp
    | some em' =>
      by_cases e : em = em'
      · subst e; simp
      · rw [ite_eq_right (fun h => e (Option.some.inj h).symm)]
        exact (ite_eq_right e).symm

theorem written_of {m : Mem} {out : Addr} {L : Nat} {r : BitVec 32} {c : Prop} [Decidable c] {H : List Byte}
    (hr : r = if c then 1 else 0)
    (hb : Spec.Rsa.bytesAt m out L = if c then H else List.replicate L 0) :
    Spec.Rsa.written m out L r (if c then some H else none) := by
  by_cases hc : c
  · rw [ite_eq_left hc] at hr hb ⊢; exact ⟨hr, hb⟩
  · rw [ite_eq_right hc] at hr hb ⊢; exact ⟨hr, hb⟩

/-! ## The steps -/

theorem add_ofNat_sub (a : Addr) {k L : Nat} (h : L ≤ k) :
    a + BitVec.ofNat 64 k - BitVec.ofNat 64 L = a + BitVec.ofNat 64 (k - L) := by
  rw [← Offset.ofNat_sub_ofNat h, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem add_ofNat_ofNat (a : Addr) (d e : Nat) :
    a + BitVec.ofNat 64 d + BitVec.ofNat 64 e = a + BitVec.ofNat 64 (d + e) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- `valPtr`: `r7 := EM₁ + k - out_len`, from `RMid`. -/
theorem valPtr_ok {s t : State} (hp : PreR s) (hm : RMid s t) (h12 : t.gpr .r12 = fb s) :
    WP isa (.block valPtr) t fun w => Only [.r7] t w ∧
      w.gpr .r7 = fb s + BitVec.ofNat 64 (oEM1 + ((s.gpr .r6).toNat - (s.gpr .r4).toNat)) := by
  have hL := hp.len_le; have hk := hp.k1
  refine wp_addi fun w₁ o₁ e₁ => wp_add fun w₂ o₂ e₂ => wp_sub fun w₃ o₃ e₃ => wp_nil ⟨(o₁.trans (o₂.trans o₃)).mono, ?_⟩
  have e6 : BitVec.ofNat 64 (s.gpr .r6).toNat = s.gpr .r6 := by simp
  have e4 : BitVec.ofNat 64 (s.gpr .r4).toNat = s.gpr .r4 := by simp
  rw [e₃, e₂, e₁, o₁.get .r30, o₂.get .r29, o₁.get .r29, hm.r30, hm.r29, h12, ← e6, ← e4, add_ofNat_ofNat,
    add_ofNat_sub _ (by omega),
    show oEM1 + (s.gpr .r6).toNat - (s.gpr .r4).toNat = oEM1 + ((s.gpr .r6).toNat - (s.gpr .r4).toNat) by
      unfold oEM1; omega]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (s.gpr .r6).isLt, Nat.mod_eq_of_lt (s.gpr .r4).isLt]

/-- `zeroOut`: zeros to the `n` bytes at `r4 = p`, counted in `r11`, and 0
returned. -/
theorem zeroOut_ok {y : State} {p : Addr} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64) (h4 : y.gpr .r4 = p)
    (h11 : y.gpr .r11 = BitVec.ofNat 64 n) (hw : ∀ i < n, InRegions y.wr (p + BitVec.ofNat 64 i) 1) :
    WP isa zeroOut y fun z => Keep [.r0, .r4, .r11, .r3] y z ∧
      z.mem = writeBytes y.mem p (List.replicate n 0) ∧ z.gpr .r3 = 0 := by
  unfold zeroOut
  refine WP.seq (wp_li (by decide) fun y₁ o₁ e₁ => wp_nil ?_)
  refine WP.seq (WP.mono (fill_ok (p := p) (n := n) (b := 0) hn hn' (by rw [o₁.get .r4, h4]) (by rw [o₁.get .r11, h11]) (by rw [e₁]; rfl)
    (by rw [o₁.wr]; exact hw)) fun y₂ ⟨k₂, m₂⟩ => ?_)
  unfold ret0
  exact wp_li (by decide) fun y₃ o₃ e₃ => wp_nil ⟨((o₁.keep.trans k₂).trans o₃.keep).mono,
    by rw [o₃.mem, m₂, o₁.mem], by rw [e₃]; rfl⟩

/-- `out` is writable in the frame. -/
theorem out_wr {s : State} (hp : PreR s) {i : Nat} (hi : i < (s.gpr .r4).toNat) :
    InRegions (fr s :: s.wr) (s.gpr .r3 + BitVec.ofNat 64 i) 1 :=
  ⟨oR s, List.mem_cons_of_mem _ (by rw [hp.hwr]; simp),
    Offset.contains_base _ (by omega) (by have := hp.wo; omega)⟩

theorem bytes_written {m : Mem} {q : Addr} {xs : List Byte} {n : Nat} (hl : xs.length = n) (hn : n < 2 ^ 64) :
    Spec.Rsa.bytesAt (writeBytes m q xs) q n = xs := by
  subst hl; exact bytesAt_writeBytes _ _ _ hn

theorem ofNat_r4 (s : State) : s.gpr .r4 = BitVec.ofNat 64 (s.gpr .r4).toNat := by simp

/-- Writes of `out` keep `Saves`. -/
theorem saves_out {s y z : State} {rs : List Reg} (hp : PreR s) (h : Saves s y) (o : Keep rs y z) {xs : List Byte}
    (hl : xs.length = (s.gpr .r4).toNat) (hm : z.mem = writeBytes y.mem (s.gpr .r3) xs)
    (hrs : ∀ r ∈ rs, r ∉ kept := by decide) : Saves s z :=
  h.keep o (R := [oR s]) (by have := frame_writeBytes y.mem (s.gpr .r3) xs; rw [hl] at this; rw [hm]; exact this)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.ko) hrs

/-- The zeros of `zeroKept`, from `RMid`. -/
theorem zeroKept_ok {s w : State} (hp : PreR s) (hm : RMid s w) :
    WP isa zeroKept w fun z => Saves s z ∧ z.gpr .r3 = 0 ∧
      Spec.Rsa.bytesAt z.mem (s.gpr .r3) (s.gpr .r4).toNat = List.replicate (s.gpr .r4).toNat 0 := by
  have hL1 := hp.len_pos; have hL2 := hp.len_le
  unfold zeroKept
  refine WP.seq (wp_mov fun y₁ p₁ f₁ => wp_mov fun y₂ p₂ f₂ => wp_nil ?_)
  have O₂ : Only [.r4, .r11] w y₂ := p₁.trans p₂
  refine WP.mono (zeroOut_ok (p := s.gpr .r3) (n := (s.gpr .r4).toNat) hL1 (by omega)
    (by rw [p₂.get .r4, f₁, hm.r28]) (by rw [f₂, p₁.get .r29, hm.r29, ← ofNat_r4])
    (fun i hi => by rw [O₂.wr, hm.wr]; exact out_wr hp hi)) fun z ⟨kz, mz, rz⟩ => ⟨?_, rz, ?_⟩
  · exact saves_out hp (hm.only O₂).saves kz (by simp) mz
  · rw [mz, bytes_written (by simp) (by omega)]

/-- The hash value's place in `EM₁`. -/
abbrev dig (s : State) : Addr := fb s + BitVec.ofNat 64 (oEM1 + ((s.gpr .r6).toNat - (s.gpr .r4).toNat))

/-- The hash value's place is in the frame. -/
theorem dig_in {s : State} (hp : PreR s) (rd rs : List Region) {j : Nat} (hj : j < (s.gpr .r4).toNat) :
    InRegions (rd ++ fr s :: rs) (dig s + BitVec.ofNat 64 j) 1 := by
  have := hp.k1; have := hp.k2; have := hp.len_le
  rw [add_ofNat_ofNat]; exact in_fr' s _ _ (by unfold oEM1; omega) (by unfold oEM1 frameBytes; omega)

theorem dig_sub {s : State} (hp : PreR s) : Region.Sub ⟨dig s, (s.gpr .r4).toNat⟩ (kR s) := by
  have := hp.k1; have := hp.k2; have := hp.len_le
  exact frame_sub s (by unfold oEM1 frameBytes; omega)

/-- After the comparison, its difference in `r7`: `out` gets the hash
value's bytes `D` if they encode to `EM₁` and the call succeeded (its status
`st`), zeros if not, and the result says which. -/
theorem release_ok {s y : State} {st : BitVec 64} {D : List Byte} (hp : PreR s) (hm : RMid s y)
    (hst : y.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = st)
    (hD : Spec.Rsa.bytesAt y.mem (dig s) (s.gpr .r4).toNat = D) (hlt : (y.gpr .r7).toNat < 256) :
    WP isa release y fun x => Saves s x ∧
      (x.gpr .r3).setWidth 32 = (if y.gpr .r7 = 0 ∧ st.setWidth 32 ≠ 0 then 1 else 0) ∧
      Spec.Rsa.bytesAt x.mem (s.gpr .r3) (s.gpr .r4).toNat =
        if y.gpr .r7 = 0 ∧ st.setWidth 32 ≠ 0 then D else List.replicate (s.gpr .r4).toNat 0 := by
  have hk1 := hp.k1; have hk2 := hp.k2; have hL1 := hp.len_pos; have hL2 := hp.len_le
  have hDl : D.length = (s.gpr .r4).toNat := by rw [← hD, bytesAt_length]
  unfold release maskM
  refine WP.seq (wp_subi fun z₁ q₁ g₁ => wp_lsr fun z₂ q₂ g₂ => wp_addSp fun z₃ q₃ g₃ => ?_)
  rw [q₂.sp, q₁.sp, hm.sp, BitVec.add_zero] at g₃
  refine wp_ld (a := fb s + BitVec.ofNat 64 oSt) (by rw [g₃])
    (by rw [q₃.rd, q₂.rd, q₁.rd, q₃.wr, q₂.wr, q₁.wr, hm.wr]; exact in_fr' s _ _ (by decide) (by decide))
    fun z₄ q₄ g₄ => ?_
  refine wp_lsl fun z₅ q₅ g₅ => wp_lsr fun z₆ q₆ g₆ => wp_li (by decide) fun z₇ q₇ g₇ =>
    wp_sub fun z₈ q₈ g₈ => wp_lsr fun z₉ q₉ g₉ => wp_and fun z₁₀ q₁₀ g₁₀ => wp_sub fun z₁₁ q₁₁ g₁₁ => ?_
  have Q₃ : Only [.r8, .r12] y z₃ := (q₁.trans (q₂.trans q₃)).mono
  have Q₁₁ : Only [.r9, .r10, .r8] z₃ z₁₁ :=
    (q₄.trans (q₅.trans (q₆.trans (q₇.trans (q₈.trans (q₉.trans (q₁₀.trans q₁₁))))))).mono
  have M₁₁ : z₁₁.gpr .r8 = maskOf (y.gpr .r7 = 0 ∧ st.setWidth 32 ≠ 0) := by
    rw [g₁₁, g₁₀, q₁₀.get .r10, q₉.get .r10, q₉.get .r8, g₉, q₈.get .r10, q₈.get .r8, g₈, g₇, q₇.get .r8,
      q₇.get .r9, g₆, q₆.get .r8, g₅, q₅.get .r8, g₄, q₄.get .r8, q₃.get .r8, q₃.mem, q₂.mem, q₁.mem, hst, g₂, g₁]
    exact mask_eq _ _ hlt
  have r12₁₁ : z₁₁.gpr .r12 = fb s := by rw [Q₁₁.get .r12, g₃]
  refine wp_std (a := fb s + BitVec.ofNat 64 oMk) (by rw [r12₁₁])
    (by rw [Q₁₁.wr, Q₃.wr, hm.wr]; exact in_fr s _ (by decide) (by decide)) fun z₁₂ m₁₂ => wp_nil ?_
  have fr₁₂ : Frame [⟨fb s + BitVec.ofNat 64 oMk, 8⟩] z₁₁.mem z₁₂.mem := by
    rw [m₁₂.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have mid₁₂ : RMid s z₁₂ := ((hm.only Q₃).only Q₁₁).frameW1 m₁₂.keep hp.ks (by decide) (by decide) fr₁₂
  have slot₁₂ : z₁₂.mem.readW (fb s + BitVec.ofNat 64 oMk) 64 = maskOf (y.gpr .r7 = 0 ∧ st.setWidth 32 ≠ 0) := by
    rw [m₁₂.mem, Mem.readW_writeW_self64, M₁₁]
  have D₁₂ : Spec.Rsa.bytesAt z₁₂.mem (dig s) (s.gpr .r4).toNat = D := by
    rw [Proof.RsaPkcs1Sig.bytes_apart (R := ⟨dig s, (s.gpr .r4).toNat⟩) fr₁₂
      (Offset.disjoint _ (.inr (by unfold oMk oEM1; omega)) (by unfold oEM1; omega) (by decide)) (by dsimp only; omega),
      Q₁₁.mem, Q₃.mem, hD]
  -- the value to `out`
  refine WP.seq ?_
  unfold copyOut
  refine WP.seq (WP.block_append_iff.mpr (wp_mov fun c₁ r₁ h₁ => wp_mov fun c₂ r₂ h₂ => wp_nil ?_))
  have midc₂ : RMid s c₂ := mid₁₂.only (r₁.trans r₂)
  have r12c₂ : c₂.gpr .r12 = fb s := by rw [r₂.get .r12, r₁.get .r12, m₁₂.gpr, r12₁₁]
  refine WP.mono (valPtr_ok hp midc₂ r12c₂) fun c₃ ⟨oc₃, ec₃⟩ => ?_
  have midc₃ : RMid s c₃ := midc₂.only oc₃
  have Dc₃ : Spec.Rsa.bytesAt c₃.mem (dig s) (s.gpr .r4).toNat = D := by rw [oc₃.mem, r₂.mem, r₁.mem]; exact D₁₂
  refine WP.mono (copy_ok (p := s.gpr .r3) (q := dig s) (n := (s.gpr .r4).toNat) hL1 (by omega)
    (by rw [oc₃.get .r4, r₂.get .r4, h₁, mid₁₂.r28]) ec₃
    (by rw [oc₃.get .r8, h₂, r₁.get .r29, mid₁₂.r29, ← ofNat_r4])
    (fun j hj => by rw [midc₃.rd, midc₃.wr]; exact dig_in hp _ _ hj)
    (fun i hi => by rw [midc₃.wr]; exact out_wr hp hi)
    (fun j hj i hi => ne_of_disjoint (hp.ko.sub_left (dig_sub hp)) (by omega) (by omega) hj hi))
    fun c₄ ⟨kc₄, mc₄⟩ => ?_
  have svc₄ : Saves s c₄ := saves_out hp midc₃.saves kc₄ (bytesAt_length _ _ _) mc₄
  have outc₄ : Spec.Rsa.bytesAt c₄.mem (s.gpr .r3) (s.gpr .r4).toNat = D := by
    rw [mc₄, bytes_written (bytesAt_length _ _ _) (by omega), Dc₃]
  have slotc₄ : c₄.mem.readW (fb s + BitVec.ofNat 64 oMk) 64 = maskOf (y.gpr .r7 = 0 ∧ st.setWidth 32 ≠ 0) := by
    have hf := frame_writeBytes c₃.mem (s.gpr .r3) (Spec.Rsa.bytesAt c₃.mem (dig s) (s.gpr .r4).toNat)
    rw [bytesAt_length] at hf
    rw [mc₄, hf.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.ko.sub_left (frame_sub s (d := oMk) (n := 8) (by decide))) (by decide), oc₃.mem, r₂.mem,
      r₁.mem, slot₁₂]
  -- the mask's registers
  unfold maskArgs
  refine WP.seq (wp_addSp fun d₁ n₁ k₁ => ?_)
  rw [svc₄.sp, BitVec.add_zero] at k₁
  refine wp_ld (a := fb s + BitVec.ofNat 64 oMk) (by rw [k₁])
    (by rw [n₁.rd, n₁.wr, svc₄.wr]; exact in_fr' s _ _ (by decide) (by decide)) fun d₂ n₂ k₂ =>
    wp_mov fun d₃ n₃ k₃ => wp_mov fun d₄ n₄ k₄ => wp_nil ?_
  have N₄ : Only [.r12, .r9, .r11, .r8] c₄ d₄ := n₁.trans (n₂.trans (n₃.trans n₄))
  have svd₄ : Saves s d₄ := svc₄.keep N₄.keep (R := []) (by rw [N₄.mem]; exact Frame.refl _ _)
    (fun r h => nomatch h)
  have r9d₄ : d₄.gpr .r9 = maskOf (y.gpr .r7 = 0 ∧ st.setWidth 32 ≠ 0) := by
    rw [n₄.get .r9, n₃.get .r9, k₂, n₁.mem, slotc₄]
  refine WP.seq (WP.mono (maskLoop_ok (p := s.gpr .r3) (n := (s.gpr .r4).toNat) hL1 (by omega)
    (by rw [n₄.get .r11, k₃, n₂.get .r28, n₁.get .r28, kc₄.get .r28, midc₃.r28])
    (by rw [k₄, n₃.get .r29, n₂.get .r29, n₁.get .r29, kc₄.get .r29, midc₃.r29, ← ofNat_r4])
    (fun i hi => by rw [svd₄.wr]; exact out_wr hp hi)) fun e₁ ⟨ke₁, me₁⟩ => ?_)
  rw [r9d₄, N₄.mem, outc₄, maskOf_bytes, hDl] at me₁
  unfold fin
  refine wp_li (by decide) fun f₁ p₁ h₁ => wp_and fun f₂ p₂ h₂ => wp_nil ⟨?_, ?_, ?_⟩
  · refine saves_out hp svd₄ (ke₁.trans (p₁.keep.trans p₂.keep)) (xs := if y.gpr .r7 = 0 ∧ st.setWidth 32 ≠ 0 then
      D else List.replicate (s.gpr .r4).toNat 0) (by split <;> simp [hDl]) (by rw [p₂.mem, p₁.mem, me₁, N₄.mem])
  · rw [h₂, h₁, p₁.get .r9, ke₁.get .r9, r9d₄, maskOf_fin]
  · rw [p₂.mem, p₁.mem, me₁, bytes_written (by split <;> simp [hDl]) (by omega)]

theorem encodeId_length {x : BitVec 32} {H em : List Byte} {k : Nat} (h : encodeId x H k = some em) :
    em.length = k := by
  unfold encodeId at h
  split at h
  · exact Proof.RsaPkcs1Sig.encode_length h
  · cases h

/-- After the call: the status kept, the encoding, the value to `out` or
zeros, and the restores. -/
theorem afterPub_ok {s t : State} (hp : PreR s) (hsig : stackArg s 0 = s.gpr .r6) (ha : AfterCall s t) :
    WP isa (.seq (.block encArgs) (.seq encode (.seq tail (.block restore)))) t
      fun w => Post s (freed frameBytes w) := by
  have hk1 := hp.k1; have hk2 := hp.k2; have hL1 := hp.len_pos; have hL2 := hp.len_le
  have hfin : ∀ y : State, Saves s y → (PreOk s → ∀ h,
      Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .r9).setWidth 32).toNat = some h →
      Spec.Rsa.written y.mem (s.gpr .r3) (s.gpr .r4).toNat ((y.gpr .r3).setWidth 32)
        (Spec.RsaPkcs1Sig.recover (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) h
          (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat))) →
      WP isa (.block restore) y fun w => Post s (freed frameBytes w) :=
    fun y hy hw => WP.mono (restore_ok hy) fun w ⟨habi, h3, hm⟩ => ⟨habi, fun hc h hh => by
      rw [freed_mem, freed_gpr, hm, h3]; exact hw hc h hh⟩
  unfold encArgs
  refine WP.seq (WP.block_append_iff.mpr (wp_addSp fun u₁ o₁ e₁ => ?_))
  rw [ha.sp, BitVec.add_zero] at e₁
  refine wp_std (a := fb s + BitVec.ofNat 64 oSt) (by rw [e₁])
    (by rw [o₁.wr, ha.wr]; exact in_fr s _ (by decide) (by decide)) fun u₂ m₂ => ?_
  refine wp_addi fun u₃ o₃ e₃ => wp_mov fun u₄ o₄ e₄ => wp_mov fun u₅ o₅ e₅ => wp_mov fun u₆ o₆ e₆ => wp_nil ?_
  have fr₂ : Frame [⟨fb s + BitVec.ofNat 64 oSt, 8⟩] t.mem u₂.mem := by
    rw [m₂.mem, o₁.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have mid₂ : RMid s u₂ := ha.toMid.frameW1 (o₁.keep.trans m₂.keep) hp.ks (by decide) (by decide) fr₂
  have O₆ : Only [.r4, .r5, .r6, .r8] u₂ u₆ := (o₃.trans (o₄.trans (o₅.trans o₆))).mono
  have mid₆ : RMid s u₆ := mid₂.only O₆
  have r12₆ : u₆.gpr .r12 = fb s := by rw [O₆.get .r12, m₂.gpr, e₁]
  refine WP.mono (valPtr_ok hp mid₆ r12₆) fun u₉ ⟨o₉, e₉⟩ => ?_
  have mid₉ : RMid s u₉ := mid₆.only o₉
  have r4₉ : u₉.gpr .r4 = fb s + BitVec.ofNat 64 oEM2 := by
    rw [o₉.get .r4, o₆.get .r4, o₅.get .r4, o₄.get .r4, e₃, m₂.gpr, e₁]
  have r5₉ : u₉.gpr .r5 = s.gpr .r6 := by rw [o₉.get .r5, o₆.get .r5, o₅.get .r5, e₄, o₃.get .r30, mid₂.r30]
  have r6₉ : u₉.gpr .r6 = ((s.gpr .r9).setWidth 32).setWidth 64 := by
    rw [o₉.get .r6, o₆.get .r6, e₅, o₄.get .r31, o₃.get .r31, mid₂.r31]
  have r8₉ : u₉.gpr .r8 = s.gpr .r4 := by rw [o₉.get .r8, e₆, o₅.get .r29, o₄.get .r29, o₃.get .r29, mid₂.r29]
  have slot₂ : u₂.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.gpr .r3 := by
    rw [m₂.mem, Mem.readW_writeW_self64, o₁.get .r3]
  have em1₂ : Spec.Rsa.bytesAt u₂.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .r6).toNat = em1 s t :=
    Proof.RsaPkcs1Sig.bytes_apart (R := em1R s) fr₂
      (Offset.disjoint _ (.inr (by decide)) (by unfold oEM1; omega) (by decide)) (by dsimp only; omega)
  have hpre : EPre u₉ ((s.gpr .r9).setWidth 32) (s.gpr .r6).toNat := {
    r6 := by rw [r6₉, lo32_ext]
    hk := by rw [r5₉]
    kle := hk2
    buf := fun i hi => by
      rw [mid₉.wr, r4₉, add_ofNat_ofNat]
      exact in_fr s _ (by unfold oEM2; omega) (by unfold oEM2 frameBytes; omega)
    rd := fun j hj => by
      rw [r8₉] at hj
      rw [mid₉.rd, mid₉.wr, e₉]; exact dig_in hp _ _ hj
    sep := fun j hj i hi => by
      rw [r8₉] at hj
      rw [e₉, r4₉, add_ofNat_ofNat, add_ofNat_ofNat]
      exact Offset.add_ofNat_ne _ (by unfold oEM1; omega) (by unfold oEM2; omega) (by unfold oEM1 oEM2; omega) }
  have hD₉ : Spec.Rsa.bytesAt u₉.mem (dig s) (s.gpr .r4).toNat =
      (em1 s t).drop ((s.gpr .r6).toNat - (s.gpr .r4).toNat) := by
    rw [o₉.mem, O₆.mem, dig, ← add_ofNat_ofNat, ← bytesAt_drop, Nat.sub_add_cancel (by omega), em1₂]
  have hH : Spec.Rsa.bytesAt u₉.mem (u₉.gpr .r7) (u₉.gpr .r8).toNat =
      (em1 s t).drop ((s.gpr .r6).toNat - (s.gpr .r4).toNat) := by
    rw [e₉, r8₉]; exact hD₉
  refine WP.seq (WP.mono (encode_ok hpre) fun w ⟨hK, hout⟩ => ?_)
  rw [hH] at hout
  change EOut u₉ w (encOut s t) at hout
  refine WP.seq ?_
  unfold tail
  cases heo : encOut s t with
  | none =>
    rw [heo] at hout
    obtain ⟨h0, hme⟩ := hout
    have midw : RMid s w := mid₉.frameW1 hK hp.ks (e := oEM2) (n := 1024) (by decide) (by decide)
      (by rw [hme]; exact Frame.refl _ _)
    refine WP.ite true ((eval_zero w .r3).trans (by rw [h0]; rfl)) (fun _ => WP.mono (zeroKept_ok hp midw)
      fun y ⟨hy, r3y, oy⟩ => hfin y hy fun hc h hh => ?_) (by simp)
    rw [recover_eq hp hsig (ha.res hc) hh, heo, r3y]
    cases pubOut s <;> exact ⟨rfl, oy⟩
  | some em' =>
    rw [heo] at hout
    obtain ⟨h1, hme⟩ := hout
    refine WP.ite false ((eval_zero w .r3).trans (by rw [h1]; rfl)) (by simp) fun _ => ?_
    have hl' : em'.length = (s.gpr .r6).toNat := encodeId_length heo
    have fw : Frame [⟨fb s + BitVec.ofNat 64 oEM2, 1024⟩] u₉.mem w.mem := by
      rw [hme, r4₉]
      exact (frame_writeBytes _ _ _).sub fun r hr => by
        rw [List.mem_singleton.mp hr, hl']; exact ⟨_, List.mem_singleton_self _, Region.sub_prefix hk2⟩
    have midw : RMid s w := mid₉.frameW1 hK hp.ks (by decide) (by decide) fw
    have slotw : w.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.gpr .r3 := by
      rw [fw.readW (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)) (by decide), o₉.mem, O₆.mem, slot₂]
    have hDw : Spec.Rsa.bytesAt w.mem (dig s) (s.gpr .r4).toNat =
        (em1 s t).drop ((s.gpr .r6).toNat - (s.gpr .r4).toNat) := by
      rw [Proof.RsaPkcs1Sig.bytes_apart (R := ⟨dig s, (s.gpr .r4).toNat⟩) fw
        (Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega)) (by unfold oEM1; omega) (by decide))
        (by dsimp only; omega), hD₉]
    unfold cmpArgs
    refine WP.seq (wp_addSp fun v₁ p₁ f₁ => wp_addi fun v₂ p₂ f₂ => wp_addi fun v₃ p₃ f₃ =>
      wp_mov fun v₄ p₄ f₄ => wp_nil ?_)
    rw [midw.sp, BitVec.add_zero] at f₁
    have P₄ : Only [.r12, .r4, .r5, .r6] w v₄ := p₁.trans (p₂.trans (p₃.trans p₄))
    have midv : RMid s v₄ := midw.only P₄
    have x4 : v₄.gpr .r4 = fb s + BitVec.ofNat 64 oEM1 := by rw [p₄.get .r4, p₃.get .r4, f₂, f₁]
    have x5 : v₄.gpr .r5 = fb s + BitVec.ofNat 64 oEM2 := by rw [p₄.get .r5, f₃, p₂.get .r12, f₁]
    have x6 : v₄.gpr .r6 = BitVec.ofNat 64 (s.gpr .r6).toNat := by
      rw [f₄, p₃.get .r30, p₂.get .r30, p₁.get .r30, midw.r30]; simp
    have hin : ∀ {d : Nat}, 32 ≤ d → d + (s.gpr .r6).toNat ≤ frameBytes → ∀ j < (s.gpr .r6).toNat,
        InRegions (v₄.rd ++ v₄.wr) (fb s + BitVec.ofNat 64 d + BitVec.ofNat 64 j) 1 := fun h₀ hd j hj => by
      rw [midv.wr, add_ofNat_ofNat]
      exact in_fr' s _ _ (by omega) (by omega)
    refine WP.seq (WP.mono (compare_ok (s := v₄) (n := (s.gpr .r6).toNat) (by omega) (by omega) x6
      (fun j hj => by rw [x4]; exact hin (by decide) (by unfold oEM1 frameBytes; omega) j hj)
      (fun j hj => by rw [x5]; exact hin (by decide) (by unfold oEM2 frameBytes; omega) j hj))
      fun y ⟨oy, hiff, hlt⟩ => ?_)
    have midy : RMid s y := midv.only oy
    have hb1 : Spec.Rsa.bytesAt v₄.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .r6).toNat = em1 s t := by
      rw [P₄.mem, hme, r4₉, o₉.mem, O₆.mem, ← em1₂]
      refine Proof.RsaPkcs1Sig.bytes_apart (R := em1R s) (frame_writeBytes _ _ _) ?_ (by dsimp only; omega)
      rw [hl']
      exact Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega)) (by unfold oEM1; omega) (by unfold oEM2; omega)
    have hb2 : Spec.Rsa.bytesAt v₄.mem (fb s + BitVec.ofNat 64 oEM2) (s.gpr .r6).toNat = em' := by
      rw [P₄.mem, hme, r4₉, bytes_written hl' (by omega)]
    rw [x4, x5, hb1, hb2] at hiff
    refine WP.mono (release_ok (st := t.gpr .r3)
      (D := (em1 s t).drop ((s.gpr .r6).toNat - (s.gpr .r4).toNat)) hp midy (by rw [oy.mem, P₄.mem, slotw])
      (by rw [oy.mem, P₄.mem, hDw]) hlt) fun x ⟨hx, r3x, outx⟩ => hfin x hx fun hc h hh => ?_
    rw [recover_eq hp hsig (ha.res hc) hh, heo]
    have hres := ha.res hc
    cases hpo : pubOut s with
    | none =>
      rw [hpo] at hres
      have hc' : ¬ (y.gpr .r7 = 0 ∧ (t.gpr .r3).setWidth 32 ≠ 0) := fun h => h.2 hres.1
      rw [ite_eq_right hc'] at r3x outx
      exact ⟨r3x, outx⟩
    | some em =>
      rw [hpo] at hres
      have he1 : em1 s t = em := hres.2
      dsimp only
      by_cases e : em = em'
      · have hc' : y.gpr .r7 = 0 ∧ (t.gpr .r3).setWidth 32 ≠ 0 :=
          ⟨hiff.mpr (by rw [he1]; exact e), by rw [hres.1]; decide⟩
        rw [ite_eq_left hc'] at r3x outx
        rw [ite_eq_left e]
        exact ⟨r3x, by rw [outx, he1]⟩
      · have hc' : ¬ (y.gpr .r7 = 0 ∧ (t.gpr .r3).setWidth 32 ≠ 0) := fun h => e (by rw [← he1]; exact hiff.mp h.1)
        rw [ite_eq_right hc'] at r3x outx
        rw [ite_eq_right e]
        exact ⟨r3x, outx⟩

/-! ## The whole function -/

theorem lenCheck_ok {s : State} (hp : PreR s) :
    WP isa (.block lenCheck) s fun t₁ => Only [.r12, .r11] s t₁ ∧ t₁.gpr .r11 = stackArg s 0 - s.gpr .r6 := by
  refine wp_addSp fun t₀ o₀ e₀ => wp_ld (a := stackArgAddr s 0) (by rw [e₀, BitVec.add_zero, stackArgAddr_in])
    (by rw [o₀.rd, o₀.wr]; exact arg_rd hp _ (by decide)) fun t₁ o₁ e₁ =>
    wp_sub fun t₂ o₂ e₂ => wp_nil ⟨(o₀.trans (o₁.trans o₂)).mono, ?_⟩
  rw [e₂, e₁, o₁.get .r6, o₀.get .r6, o₀.mem]; rfl

theorem eval_len {s t : State} (e : t.gpr .r11 = stackArg s 0 - s.gpr .r6) :
    isa.eval (.nonzero .d .r11) t = some (decide (stackArg s 0 ≠ s.gpr .r6)) := by
  rw [eval_nonzero, e, ne_zero_iff, BitVec.toNat_sub]
  have := (stackArg s 0).isLt; have := (s.gpr .r6).isLt
  refine congrArg some (decide_eq_decide.mpr ⟨fun h e => ?_, fun h e => h ?_⟩)
  · rw [e] at h; omega
  · apply BitVec.eq_of_toNat_eq; omega

theorem recover_len {s : State} (h : stackArg s 0 ≠ s.gpr .r6) (hh : Spec.RsaPkcs1Sig.Hash) :
    Spec.RsaPkcs1Sig.recover (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) hh
      (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat) = none := by
  unfold Spec.RsaPkcs1Sig.recover
  rw [bytesAt_length, bytesAt_length, ite_eq_right fun e => h (BitVec.eq_of_toNat_eq e)]

theorem code_ok {s : State} (hp : PreR s) : WP isa code s (Post s) := by
  have hL1 := hp.len_pos; have hL2 := hp.len_le
  unfold code
  refine WP.seq (WP.mono (lenCheck_ok hp) fun t₁ ⟨o₁, e₁⟩ => ?_)
  have hne := eval_len e₁
  by_cases hsig : stackArg s 0 = s.gpr .r6
  · refine WP.ite false (by rw [hne]; simp [hsig]) (by simp) fun _ => ?_
    refine WP.alloc (by decide) (by rw [o₁.sp]; exact hp.sp1) ?_
    have fr₁ : frameR frameBytes t₁ = fr s := by rw [frameR_eq]; unfold fr fb; rw [o₁.sp]
    unfold body
    refine WP.seq (WP.mono (pubArgs_ok hp (by rw [allocated_sp, o₁.sp]) (by rw [allocated_wr, fr₁, o₁.wr])
      (by rw [allocated_rd, o₁.rd])
      (by rw [allocated_mem, o₁.mem, o₁.sp]
          exact Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ (fb_contains s))
      (fun r hr => by
        rw [allocated_gpr]
        exact o₁.gpr r fun h => hr (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; exact h.symm))
      (by rw [allocated_lr, o₁.lr])) fun t₂ h₂ => ?_)
    exact WP.seq (WP.mono (call_ok hp h₂ hsig) fun t₃ h₃ => afterPub_ok hp hsig h₃)
  · refine WP.ite true (by rw [hne]; simp [hsig]) (fun _ => ?_) (by simp)
    unfold zeroArgs
    refine WP.seq (wp_mov fun y₁ p₁ f₁ => wp_mov fun y₂ p₂ f₂ => wp_nil ?_)
    have O₂ : Only [.r12, .r11, .r11, .r4] s y₂ := o₁.trans (p₁.trans p₂)
    refine WP.mono (zeroOut_ok (p := s.gpr .r3) (n := (s.gpr .r4).toNat) hL1 (by omega)
      (by rw [f₂, p₁.get .r3, o₁.get .r3]) (by rw [p₂.get .r11, f₁, o₁.get .r4, ← ofNat_r4])
      (fun i hi => by
        rw [O₂.wr]
        exact ⟨oR s, by rw [hp.hwr]; simp, Offset.contains_base _ (by omega) (by have := hp.wo; omega)⟩))
      fun w ⟨kw, mw, rw₃⟩ => ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun _ h _ => ?_⟩
    · exact (O₂.keep.trans kw).gpr r (by revert r; decide)
    · rw [kw.sp, O₂.sp]
    · rw [kw.lr, O₂.lr]
    · rw [recover_len hsig, rw₃, mw]
      exact ⟨rfl, bytes_written (by simp) (by omega)⟩

/-- The correctness of `vg_rsa_pkcs1_recover_precomputed`, against its
shared contract. -/
theorem code_correct (s : State) (h : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi frameBytes).pre s) :
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧
      (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi frameBytes).post s s' := by
  obtain ⟨t, s', he, habi, hr⟩ := code_ok (preR_of h)
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq]
  exact hr

end VG.Proof.RsaPkcs1Sig.PPC64LE.Rec
