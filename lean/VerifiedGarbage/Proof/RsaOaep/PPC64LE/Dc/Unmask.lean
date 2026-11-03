module

import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Label
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfT
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfStepsT
public import VerifiedGarbage.Proof.RsaOaep.Mask
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Base
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.PrivCall

/-!
# RSAES-OAEP decryption on PPC64LE: unmasking `EM`

Untrusted: everything here is checked by Lean. `unmask_ok`: the seed
unmasked with MGF1 of `maskedDB`, then `maskedDB` with MGF1 of the seed, in
place (`seedArgs`, `mgfXorT`, `dbArgs`, `mgfXorT`, with MGF1's hash function
the table's), as `decode_eq` takes them.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep wp_li wp_mov wp_addi wp_subi wp_nil)
open VG.Proof.RsaOaep (mixV srcB)

theorem sub_r15 {x : BitVec 64} {a : Nat} (h : a ≤ x.toNat) : x - BitVec.ofNat 64 a = BitVec.ofNat 64 (x.toNat - a) :=
  sub_ofNat h

section
variable {s : State} (P : PreD s) {m : Mem} {rc : Nat}
include P

/-- MGF1's table, in a state with the entry's stack pointer, regions,
statics' addresses and working space, and memory as on entry but for the
stack and the working space. -/
theorem tabS_to {G : Hash} {f : Fns} (T : TabS G f 15 (SD s) s (stackArg s 15)) {S' : State → Addr} {s' : State}
    (hm : Frame [kD s, scR s] s.mem s'.mem) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hsy : s'.syms = s.syms)
    (hS : SC S' s' = SC (SD s) s) : TabS G f 15 S' s' (stackArg s 15) := by
  have hA : Region.Sub ⟨stackArgAddr s 15, 8⟩ (aR s) := by
    rw [stackArgAddr_eq]; exact Offset.sub_base _ (by omega)
  have hT : ∀ k < 5, Region.Sub ⟨stackArg s 15 + BitVec.ofNat 64 (8 * k), 8⟩ (tR s) := fun k hk =>
    Offset.sub_base _ (by show 8 * k + 8 ≤ 5 * (64 / 8); omega)
  refine T.transfer hsp hrd hsy hS hm (fun r hr => ?_) (fun k hk r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (P.ka.sub_right hA).symm
    · exact (P.sa.sub_right hA).symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (P.kt.sub_right (hT k hk)).symm
    · exact (P.st.sub_right (hT k hk)).symm

/-- MGF1's table, for `Base` after the private operation: as on entry, which
wrote only the stack and the working space. -/
theorem tabS_wm {G : Hash} {f : Fns} (T : TabS G f 15 (SD s) s (stackArg s 15))
    (hm : Frame [kD s, scR s] s.mem m) : TabS G f 15 (SD s) (withMem s m) (stackArg s 15) :=
  tabS_to P T hm rfl rfl rfl rfl

/-- EME-OAEP's unmasking, in place. -/
theorem unmask_ok {H G : Hash} (hG : HashOK G) {f : Fns} (T : TabS G f 15 (SD s) (withMem s m) (stackArg s 15))
    {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x)
    (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) {D : Nat} (hD : H.D = D) (hD0 : 0 < D) (hD64 : D ≤ 64)
    (hk : 2 * D + 2 ≤ kk s) {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) (hsy : t.syms = s.syms)
    {rest : Prog isa} {Q : State → Prop}
    (k : ∀ t', Base (SD s) (VD s rc) (withMem s m) t' → t'.syms = s.syms → (∀ x < kk s, view t'.mem (Sd s) x =
        mixV (mixV (view t.mem (Sd s)) (Spec.Mgf1.mgf1 Gs (srcB (view t.mem (Sd s)) (1 + D) (kk s - D - 1)) D) 1 D)
          (Spec.Mgf1.mgf1 Gs (srcB (mixV (view t.mem (Sd s))
            (Spec.Mgf1.mgf1 Gs (srcB (view t.mem (Sd s)) (1 + D) (kk s - D - 1)) D) 1 D) 1 D) (kk s - D - 1))
          (1 + D) (kk s - D - 1) x) → WP isa rest t' Q) :
    WP isa (.seq (.block (seedArgs H)) (.seq (mgfXorT f 15) (.seq (.block (dbArgs H)) (.seq (mgfXorT f 15) rest)))) t Q := by
  obtain ⟨hE, hSt, hDg, hCt, hW, hRs⟩ := offs
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r7).toNat := rfl
  have PF := fitsM (m := m) P
  subst hD
  -- The seed with MGF1 of `maskedDB`.
  refine WP.seq (WP.of_syms (wp_addi (h := by omega) fun t₁ o₁ e₁ => wp_subi (h := by omega) fun t₂ o₂ e₂ =>
    wp_addi (h := by omega) fun t₃ o₃ e₃ => wp_li (by omega) fun t₄ o₄ e₄ => wp_nil fun y₄ => ?_))
  have k₄ : Only [.r24, .r25, .r26, .r27] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  have b₄ := h.only PF k₄
  refine WP.seq (WP.mono (mgfXorT_ok PF hG T hGh hGl hGv (src := 1 + H.D) (srcLen := kk s - H.D - 1) (dst := 1)
    (dstLen := H.D) ⟨by omega, by omega, .inr (by omega), by omega⟩ b₄ (y₄.trans hsy)
    (by rw [o₄.get .r24, o₃.get .r24, o₂.get .r24, e₁, h.r14, hE, Nat.zero_add])
    (by rw [o₄.get .r25, o₃.get .r25, e₂, o₁.get .r15, Base.r15 h, sub_r15 (by omega)]; congr 1)
    (by rw [o₄.get .r26, e₃, o₂.get .r14, o₁.get .r14, h.r14, hE])
    (by rw [e₄]))
    fun t₅ ⟨⟨b₅, v₅⟩, y₅⟩ => ?_)
  -- `maskedDB` with MGF1 of the seed.
  refine WP.seq (WP.of_syms (wp_addi (h := by omega) fun t₆ o₆ e₆ => wp_li (by omega) fun t₇ o₇ e₇ =>
    wp_addi (h := by omega) fun t₈ o₈ e₈ => wp_subi (h := by omega) fun t₉ o₉ e₉ => wp_nil fun y₉ => ?_))
  have k₉ : Only [.r24, .r25, .r26, .r27] t₅ t₉ := (o₆.trans (o₇.trans (o₈.trans o₉))).mono
  have b₉ := b₅.only PF k₉
  refine WP.seq (WP.mono (mgfXorT_ok PF hG T hGh hGl hGv (src := 1) (srcLen := H.D) (dst := 1 + H.D)
    (dstLen := kk s - H.D - 1) ⟨by omega, by omega, .inl (by omega), by omega⟩ b₉ (y₉.trans y₅)
    (by rw [o₉.get .r24, o₈.get .r24, o₇.get .r24, e₆, b₅.r14, hE])
    (by rw [o₉.get .r25, o₈.get .r25, e₇])
    (by rw [o₉.get .r26, e₈, o₇.get .r14, o₆.get .r14, b₅.r14, hE, Nat.zero_add])
    (by rw [e₉, o₈.get .r15, o₇.get .r15, o₆.get .r15, Base.r15 b₅, sub_r15 (by omega)]; congr 1))
    fun t₁₀ ⟨⟨b₁₀, v₁₀⟩, y₁₀⟩ => k t₁₀ b₁₀ y₁₀ fun x hx => ?_)
  have V4 : view t₄.mem (Sd s) = view t.mem (Sd s) := by rw [k₄.mem]
  have V9 : view t₉.mem (Sd s) = view t₅.mem (Sd s) := by rw [k₉.mem]
  rw [V4] at v₅
  rw [V9] at v₁₀
  have hsrc : srcB (view t₅.mem (Sd s)) 1 H.D = srcB (mixV (view t.mem (Sd s))
      (Spec.Mgf1.mgf1 Gs (srcB (view t.mem (Sd s)) (1 + H.D) (kk s - H.D - 1)) H.D) 1 H.D) 1 H.D :=
    List.map_congr_left fun i hi => v₅ _ (by have := List.mem_range.mp hi; omega)
  rw [v₁₀ x (by omega), hsrc, mixV, mixV]
  split
  · rw [v₅ x (by omega)]
  · rw [v₅ x (by omega)]

end

end VG.Proof.RsaOaep.PPC64LE.Dec
