import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.DPart

/-!
# An RSA key from its primes on x86-64: `d` too small

`smallMask`: ZF clear exactly when `d` exists and `d ≤ 2^(64 w)`
(`smallMask_k`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- Word `k` of a number written, from zero. -/
theorem wv_set {m : Mem} {B : Addr} {d N k : Nat} (v : BitVec 64) (hz : word m B (d + 8 * k) = 0)
    (hd : d + 8 * N ≤ 2 ^ 64) (hk : k < N) : ∀ n ≤ N,
    wv (m.writeW (off B (d + 8 * k)) v) B d n = wv m B d n + (if k < n then 2 ^ (64 * k) * v.toNat else 0)
  | 0, _ => by simp [wv]
  | n + 1, hn => by
    rw [wv, wv, wv_set v hz hd hk n (by omega)]
    by_cases hkn : n = k
    · subst hkn; rw [word_writeW_self, hz]; simp
    · rw [(writeW_outside m B v (d := d + 8 * k) (by omega)).word (by omega) (by omega)]
      by_cases hk' : k < n
      · simp [hk', show k < n + 1 by omega]; omega
      · simp [hk', show ¬ k < n + 1 by omega]

/-- `smallMask`: ZF clear iff `kOk` and `[aDd] ≤ 2^(64 w)`, for `W = 2 w`. -/
theorem smallMask_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {w : Nat} (hW : I.W = 2 * w) {ok : Bool}
    (hok : word s.mem I.B (8 * kOk) = mask ok) :
    WP isa (seqs smallMask) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aC] s.mem t.mem ∧
      t.zf = some (!(decide (av I s.mem aDd ≤ 2 ^ (64 * w)) && ok)) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.hZ
  have hw1 : 1 ≤ w := by have := h.ws.w1; omega
  have hw2 := h.ws.w2
  have sC := h.ws.sl (j := aC) (by decide)
  unfold smallMask
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp [constA]) (by simp) (WP.mono (constA_k h 1) fun s₁ ⟨h₁, f₁, c₁, _⟩ => ?_)
  -- Word `w` of `[aC]` set: `[aC] = 2^(64 w) + 1`.
  refine wp_seqs_append (by simp) (by simp [ltA]) ?_
  simp only [seqs]
  refine WP.mono (Q := fun (t : State) => t.mem = s₁.mem.writeW (off I.B (slot I.W aC + 8 * w)) (1 : BitVec 64) ∧
    Keep [.r12, .r9, .rbx, .rax, .rdx] s₁ t) ?_ fun (s₂ : State) ⟨m₂, k₂⟩ => ?_
  · rw [WP.block_append_iff]
    refine WP.mono h₁.ws.ws_ok fun u₁ ⟨h12, h9, mu₁, ku₁⟩ => WP.block_append_iff.mpr ?_
    refine WP.mono (base_ok aC (r := .rbx) (by decide) ((ku₁.gpr (by decide)).trans h₁.ws.rdi) h9)
      fun u₂ ⟨hbx, mu₂, ku₂⟩ => ?_
    have hs₂ := h₁.ws.scr.congr (ku₁.trans ku₂).2.2
    have h12₂ : u₂.gpr .r12 = BitVec.ofNat 64 I.W := (ku₂.gpr (by decide)).trans h12
    refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.mem = s₁.mem.writeW (off I.B (slot I.W aC + 8 * w)) (1 : BitVec 64)) (by
      have ew : BitVec.ofNat 64 I.W >>> 1 = BitVec.ofNat 64 w := by
        rw [ofNat_shr1 (by omega)]; congr 1; omega
      xrun [State.ea, ix, h12₂, ew, addr0 hbx rfl, hs₂.st (d := slot I.W aC + 8 * w) (by omega), mu₂, mu₁]
      rfl) rfl) fun t ⟨hm, k⟩ => ⟨hm, ((ku₁.trans ku₂).trans k).mono (by simp)⟩
  have o₂ := writeW_outside s₁.mem I.B (1 : BitVec 64) (d := slot I.W aC + 8 * w) (by omega)
  rw [← m₂] at o₂
  have f₂ := KF.arr1 (I := I) (j := aC) o₂ (by omega) (by omega)
  have h₂ := h₁.step f₂ (all_mut_arr (by decide)) k₂ (by decide)
  have c₂ : av I s₂.mem aC = 2 ^ (64 * w) + 1 := by
    have hz : word s₁.mem I.B (slot I.W aC + 8 * w) = 0 := by
      have e := VG.Proof.Rsa.X86_64.wv_low (m := s₁.mem) (B := I.B) (e := slot I.W aC) (w := I.W + 2) (by omega)
      rw [c₁] at e
      have h0 : wv s₁.mem I.B (slot I.W aC + 8) (I.W + 2 - 1) = 0 := by
        rcases Nat.eq_zero_or_pos (wv s₁.mem I.B (slot I.W aC + 8) (I.W + 2 - 1)) with h0 | h0
        · exact h0
        · have := Nat.le_mul_of_pos_right (2 ^ 64) h0
          simp only [show (1 : BitVec 32).toNat = 1 from rfl] at e; omega
      have := (wv_eq_zero_iff _ _ _ _).mp h0 (w - 1) (by omega)
      rwa [show slot I.W aC + 8 + 8 * (w - 1) = slot I.W aC + 8 * w by omega] at this
    have hv1 : av I s₁.mem aC = 1 := av_of_full c₁ (two_le_pow h (by decide))
    dsimp only [av] at hv1 ⊢
    rw [m₂, wv_set (1 : BitVec 64) hz (by omega) (by omega) I.W (Nat.le_refl _), hv1, ite_eq_left (by omega)]
    simp; omega
  have vD : av I s₂.mem aDd = av I s.mem aDd := by
    rw [f₂.av (by decide) (by decide) (by decide) hZ, f₁.av (by decide) (by decide) (by decide) hZ]
  refine wp_seqs_append (by simp [ltA]) (by simp) (WP.mono (ltA_k h₂ (a := aDd) (b := aC) (by decide) (by decide))
    fun s₃ ⟨h₃, m₃, hbp, _, _, _, k₃⟩ => ?_)
  rw [vD, c₂] at hbp
  simp only [seqs]
  have hok₃ : word s₃.mem I.B (8 * kOk) = mask ok := by
    rw [m₃, f₂.word (by decide) (by decide) (by decide), f₁.word (by decide) (by decide) (by decide), hok]
  have hld := h₃.ws.scr.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.zf = some (!(decide (av I s.mem aDd ≤ 2 ^ (64 * w)) && ok)) ∧
    t.mem = s₃.mem) (by
      xrun [State.ea, hdr, h₃.ws.rdi, hdrOff, hld, hbp, hok₃, mask_and']
      have hd : decide (av I s.mem aDd < 2 ^ (64 * w) + 1) = decide (av I s.mem aDd ≤ 2 ^ (64 * w)) :=
        decide_eq_decide.mpr Nat.lt_succ_iff
      rw [Bool.and_self, hd]
      cases (decide (av I s.mem aDd ≤ 2 ^ (64 * w)) && ok) <;> decide) rfl) fun t ⟨⟨hz, m⟩, k⟩ => by
    have f₂' : KF I.B I.W [.arr aC] s₁.mem t.mem := by rw [m, m₃]; exact f₂
    exact ⟨h₃.step (cs := []) (by rw [m]; exact KF.refl _ _ _) rfl k (by decide), (f₁.trans f₂').mono (by simp), hz⟩

end VG.Proof.RsaKeyGen.X86_64.Key
