module
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hmac

import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Msg
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Deterministic ECDSA on AArch64: the steps on `K` and `V`

`V = HMAC_K(V)` (`hmacV_ok`); `K = HMAC_K(V ‖ b ‖ d ‖ h)` (or, if two `V`s
make a candidate, `‖ d ‖ 0 0 ‖ digest`), then `V = HMAC_K(V)`
(`rekeyFull_ok`, steps d–g); and `K = HMAC_K(V ‖ 0x00)`,
then `V = HMAC_K(V)` (`rekey_ok`, step h.3). Each changes only `scratch`,
the stack below the frame, and `K` and `V`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

variable {P : RfcHash} {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem}

/-- `K` and `V` (of the hash function's output length) and `h`, in the frame. -/
abbrev kOf (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) : List Byte := keyOf P L m
abbrev vOf (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 80) P.H.D
abbrev hOf (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 P.hB) P.Q

/-- What the steps change: `scratch`, the stack below the frame, `K` and `V`. -/
abbrev KVW {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : List Region := [L.SCR, ⟨L.B, 144⟩]

theorem kvw_of {rs : List Region} (h : ∀ r ∈ rs, Region.Sub r L.SCR ∨ Region.Sub r ⟨L.B, 144⟩) :
    ∀ r ∈ rs, ∃ r' ∈ KVW L, Region.Sub r r' := fun r hr => by
  rcases h r hr with h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨⟨L.B, 144⟩, by simp, h⟩

theorem done_kvw {dst : Nat} (h : dst + P.H.D ≤ 128) :
    ∀ r ∈ [(⟨L.scr, 2256⟩ : Region), ⟨L.B, 16⟩, ⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩],
      ∃ r' ∈ KVW L, Region.Sub r r' :=
  kvw_of fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (Region.sub_prefix (by omega_arith))
    · exact .inr (Region.sub_prefix (by omega_arith))
    · exact .inr (Offset.sub_base _ (by omega_arith))

/-- `V = HMAC_K(V)`. -/
theorem hmacV_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).hmacV t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = kOf P L t.mem ∧ vOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem) := by
  refine WP.mono (hmac_ok (P := P) hL hT hc (da := L.B + BitVec.ofNat 64 (16 + 64)) (len := P.H.D) (dst := 64)
    (fun u hu => fr_ok hL hu (d := .x2) (by decide) (o := 64) (by decide))
    (.inl ⟨80, rfl, by omega_arith, by anums⟩) (by anums) (by anums)) fun t' h =>
    ⟨h.ctx, h.frame.sub (done_kvw (by anums)), bytesAt_frame h.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hL.stk_scr0 (by anums) (by omega_arith)
      · exact Offset.disjoint_base _ (by omega_arith) (by anums)
      · exact Offset.disjoint _ (by anums) (by anums) (by anums)) (by anums), h.mac⟩

/-- `K = HMAC_K(m)`, for the message `m` of `len` bytes at `scratch + 2256`. -/
theorem hmacK_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {len : Nat} (hlen : len ≤ 256) :
    WP isa ((cfgOf P).hmac (Cfg.scr .x2 sMsg) len fK) t fun t' => Ctx L g m₀ t' ∧
      Frame (KVW L) t.mem t'.mem ∧ vOf P L t'.mem = vOf P L t.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len) := by
  refine WP.mono (hmac_ok (P := P) hL hT hc (da := L.scr + BitVec.ofNat 64 2256) (len := len) (dst := 0)
    (fun u hu => scr_ok hL hu (d := .x2) (by decide) (a := 2256) (by decide))
    (.inr ⟨2256, rfl, by omega_arith, by omega_arith⟩) hlen (by anums)) fun t' h =>
    ⟨h.ctx, h.frame.sub (done_kvw (by anums)), bytesAt_frame h.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hL.stk_scr0 (by anums) (by omega_arith)
      · exact Offset.disjoint_base _ (by omega_arith) (by anums)
      · exact Offset.disjoint _ (by anums) (by anums) (by anums)) (by anums), h.mac⟩

/-- What the steps need of the layout: the scalars' bytes, and the table
and the bytes at the frame's top of `P`. -/
def HOk (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : Prop := P.Q ≤ L.q ∧ TabL P L

/-- `h`'s place fits above `K` and `V`, in the frame. -/
theorem hB_fit (hq : HOk P L) : 16 + (P.hB - 16) + P.Q ≤ 240 + L.e := by
  rw [hq.2.2.2]
  cases hw : P.wide
  · have := P.sizesA hw
    have hF := P.hFits hw
    have hh := hHigh_q P hw
    simp only [RfcHash.hB, RfcHash.e, hw, hh, Bool.false_or, Bool.false_eq_true, ite_false] at ⊢
    by_cases h64 : P.Q = 64
    · simp only [h64, decide_true, ite_true]; omega
    · simp only [h64, decide_false, Bool.false_eq_true, ite_false]
      have : P.w ≠ 8 := fun h => h64 (hF.1 h)
      have := hF.2 this; omega
  · simp only [RfcHash.hB, RfcHash.e, hw, Bool.true_or, ite_true]; anums

/-- `K = HMAC_K(m)`, then `V = HMAC_K(V)`, for the message `m = V ‖ b (‖ d ‖ h)`. -/
theorem rekey_gen (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) {b : Nat} {full : Bool}
    {ho : Nat} (hho : full = true → ho = P.hB - 16) {len : Nat}
    (hlen : len = if full then P.H.D + 2 * P.Q + 1 else P.H.D + 1) :
    WP isa (.seq (.block Cfg.msgPtrs) (.seq (.block (Cfg.msg P.w P.Q P.H.D b full ho))
      (.seq ((cfgOf P).hmac (Cfg.scr .x2 sMsg) len fK) (cfgOf P).hmacV))) t
      fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
        kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem else [])) ∧
        vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) := by
  have hT := hq.2
  refine WP.seq (WP.mono (ptrs_ok hL hc) fun p ⟨hcp, hmp, h9, h10, h15⟩ => ?_)
  rw [← hmp]
  have hmsg := msg_ok hL hcp h9 h10 h15 b full (D := P.H.D) (w := P.w) (Q := P.Q) (ho := ho) (by anums) (by anums)
    (fun hf => by
      have := hB_fit hq
      have h8 : (P.hB - 16) % 8 = 0 := by simp only [RfcHash.hB]; split <;> decide
      rw [hho hf]; exact ⟨by anums, by anums, this, h8, hq.1⟩)
  have hh : (if full then Spec.Sha256.bytesAt p.mem L.d P.Q ++
        Spec.Sha256.bytesAt p.mem (L.B + BitVec.ofNat 64 (16 + ho)) P.Q else []) =
      (if full then Spec.Sha256.bytesAt p.mem L.d P.Q ++ hOf P L p.mem else []) := by
    cases full
    · rfl
    · have := hB_ge P
      rw [hho rfl, show 16 + (P.hB - 16) = P.hB by omega]
  rw [hh] at hmsg
  refine WP.seq (WP.mono hmsg fun u ⟨hcu, hfu, hbu⟩ => ?_)
  have hlen' : len ≤ 256 := by
    cases full <;> simp only [hlen, Bool.false_eq_true, ite_true, ite_false] <;> anums
  refine WP.seq (WP.mono (hmacK_ok (P := P) hL hT hcu (len := len) hlen') fun w ⟨hcw, hfw, hvw, hkw⟩ => ?_)
  refine WP.mono (hmacV_ok hL hT hcw) fun t' ⟨hc', hf', hk', hv'⟩ => ⟨hc', ?_, ?_, ?_⟩
  · exact ((hfu.sub (kvw_of fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inl (Offset.sub_base _ (by anums)))).trans hfw).trans hf'
  · have hku : kOf P L u.mem = kOf P L p.mem := bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by anums) (by anums)) (by anums)
    rw [hk', hkw, hku, hlen]
    cases full
    · simp only [Bool.false_eq_true, ite_false] at hbu ⊢; rw [hbu]
    · simp only [ite_true] at hbu ⊢; rw [hbu]
  · have hvu : vOf P L u.mem = vOf P L p.mem := bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by anums) (by anums)) (by anums)
    rw [hv', hk', hvw, hvu]

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
theorem rekeyFull_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) (b : Nat) :
    WP isa ((cfgOf P).rekeyFull b) t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [BitVec.ofNat 8 b] ++
        (Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem)) ∧
      vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) :=
  rekey_gen (full := true) hL hq hc (ho := (cfgOf P).fHo) (fun _ => fHo_eq P) rfl

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
theorem rekey_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).rekey t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [0]) ∧
      vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) :=
  WP.mono (rekey_gen (b := 0) (full := false) hL hq hc (ho := fH) (fun h => absurd h (by decide)) rfl)
    fun _ h => ⟨h.1, h.2.1, by rw [h.2.2.1]; simp, h.2.2.2⟩

end VG.Proof.Ecdsa.Rfc6979.AArch64
