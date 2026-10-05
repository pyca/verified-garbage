import VerifiedGarbage.Proof.Rsa.X86_64.KeyCtx

/-!
# `vg_rsa_check_key` on x86-64: the pieces in the checks' context

Each piece of `main`, from `KCtx`: what it computes, that it keeps `KCtx`,
and what it changes (`Arrays`, or only `sMask`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask)

theorem mask_and' (a b : Bool) : mask a &&& mask b = mask (a && b) := by
  cases a <;> cases b <;> rfl

section
variable {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}

theorem Arrays.mask_eq {m m' : Mem} {js : List Nat} (ha : Arrays B w js m m') (hn : B.toNat + Z ≤ 2 ^ 64)
    (hZ : slot w 8 ≤ Z) : word m' B (8 * sMask) = word m B (8 * sMask) :=
  ha.word_eq (fun j _ => .inl (hdr_lt_slot w j (by decide)))
    (by have := hdr_lt_slot w 8 (show sMask < 32 by decide); omega)

theorem KCtx.word {h : KCtx s t B Z w minv N} {i : Nat} (hi : i < 32) (hi' : i ≠ sMask) :
    word t.mem B (8 * i) = word s.mem B (8 * i) := h.hdr i hi hi'

theorem loadK (h : KCtx s t B Z w minv N) {j : Nat} (hj : j < 8) (hjN : j ≠ aN) (hj1 : j ≠ aOne)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) (hsp' : sp ≠ sMask) (hsl' : sl ≠ sMask) {p : Addr}
    {bs : List Byte} (hp : word s.mem B (8 * sp) = p) (hl : word s.mem B (8 * sl) = BitVec.ofNat 64 bs.length)
    (hsrc : Src s B Z p bs) (hk1 : 1 ≤ bs.length) (hkw : bs.length ≤ 8 * w) :
    WP isa (seqs (loadNum j sp sl)) t fun t' => KCtx s t' B Z w minv N ∧
      wv t'.mem B (slot w j) w = Spec.Rsa.os2ip bs ∧ Arrays B w [j] t.mem t'.mem := by
  refine WP.mono (loadNum_ok h.good h.hZ h.w1 h.w2 hj hsp hsl (by rw [h.hdr sp hsp hsp']; exact hp)
    (by rw [h.hdr sl hsl hsl']; exact hl) (h.src hsrc) hk1 hkw) fun t' ⟨hv, ha, hk⟩ => ⟨?_, hv, ha⟩
  exact h.arr ha (by simpa using hj) (by simpa using Ne.symm hjN) (by simpa using Ne.symm hj1) hk

theorem ltK (h : KCtx s t B Z w minv N) {a b : Nat} (ha : a < 8) (hb : b < 8) :
    WP isa (seqs (ltMask a b)) t fun t' => KCtx s t' B Z w minv N ∧
      word t'.mem B (8 * sMask) = word t.mem B (8 * sMask) &&&
        mask (decide (wv t.mem B (slot w a) w < wv t.mem B (slot w b) w)) ∧
      Outside B (8 * sMask) 8 t.mem t'.mem :=
  WP.mono (ltMask_ok h.good h.hZ h.w1 h.w2 ha hb) fun _ ⟨hv, ho, hk⟩ => ⟨h.msk ho hk, hv, ho⟩

theorem eqOneK (h : KCtx s t B Z w minv N) :
    WP isa (seqs eqOne) t fun t' => KCtx s t' B Z w minv N ∧
      word t'.mem B (8 * sMask) = word t.mem B (8 * sMask) &&&
        mask (decide (wv t.mem B (slot w aR) w = 1)) ∧
      Outside B (8 * sMask) 8 t.mem t'.mem :=
  WP.mono (eqOne_ok h.good h.hZ h.w1 h.w2) fun _ ⟨hv, ho, hk⟩ => ⟨h.msk ho hk, by rw [hv, h.one], ho⟩

theorem decK (h : KCtx s t B Z w minv N) :
    WP isa (seqs decM) t fun t' => KCtx s t' B Z w minv N ∧
      (0 < wv t.mem B (slot w aM) w → wv t'.mem B (slot w aM) w + 1 = wv t.mem B (slot w aM) w) ∧
      Arrays B w [aM] t.mem t'.mem :=
  WP.mono (decM_ok h.good h.hZ h.w1 h.w2) fun _ ⟨hv, ho, hk⟩ =>
    have ha : Arrays B w [aM] t.mem _ := Arrays.of_outside (by simp) ho (Nat.le_refl _) (by omega)
    ⟨h.arr ha (by decide) (by decide) (by decide) hk, hv, ha⟩

theorem mulEK (h : KCtx s t B Z w minv N) :
    WP isa (seqs mulE) t fun t' => KCtx s t' B Z w minv N ∧
      wv t'.mem B (slot w aAcc) (w + 2) = (word s.mem B (8 * sEv)).toNat * wv t.mem B (slot w aX) w ∧
      Arrays B w [aAcc] t.mem t'.mem :=
  WP.mono (mulE_ok h.good h.hZ h.w1 h.w2) fun _ ⟨hv, ha, hk⟩ =>
    ⟨h.arr ha (by decide) (by decide) (by decide) hk, by rw [hv, h.hdr sEv (by decide) (by decide)], ha⟩

theorem mulXRK (h : KCtx s t B Z w minv N) :
    WP isa (seqs mulXR) t fun t' => KCtx s t' B Z w minv N ∧
      wv t'.mem B (slot w aAcc) (2 * w + 2) = wv t.mem B (slot w aX) w * wv t.mem B (slot w aR) w ∧
      Arrays B w [aAcc, aTmp] t.mem t'.mem :=
  WP.mono (mulXR_ok h.good h.hZ h.w1 h.w2) fun _ ⟨hv, ha, hk⟩ =>
    ⟨h.arr ha (by decide) (by decide) (by decide) hk, hv, ha⟩

theorem cntE_ok (t : State) (h : t.gpr .r13 = BitVec.ofNat 64 w) :
    WP isa (.block cntE) t fun t' => t'.gpr .r13 = BitVec.ofNat 64 (w + 2) ∧ t'.mem = t.mem ∧ Keep [.r13] t t' := by
  refine WP.mono (WP.keep [.r13] (Q := fun t' => t'.gpr .r13 = BitVec.ofNat 64 (w + 2) ∧ t'.mem = t.mem) (by
    xrun [cntE, h]
    rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, BitVec.ofNat_add_ofNat]) rfl) fun _ ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩

theorem cntXR_ok (t : State) (h : t.gpr .r13 = BitVec.ofNat 64 w) :
    WP isa (.block cntXR) t fun t' => t'.gpr .r13 = BitVec.ofNat 64 (2 * w + 2) ∧ t'.mem = t.mem ∧
      Keep [.r13] t t' := by
  refine WP.mono (WP.keep [.r13] (Q := fun t' => t'.gpr .r13 = BitVec.ofNat 64 (2 * w + 2) ∧ t'.mem = t.mem) (by
    xrun [cntXR, h]
    rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
    congr 1; omega) rfl) fun _ ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩

theorem reduceEK (h : KCtx s t B Z w minv N) :
    WP isa (seqs (reduce cntE)) t fun t' => KCtx s t' B Z w minv N ∧
      (0 < wv t.mem B (slot w aM) w →
        wv t'.mem B (slot w aR) w = wv t.mem B (slot w aAcc) (w + 2) % wv t.mem B (slot w aM) w) ∧
      Arrays B w [aR, aX, aT] t.mem t'.mem :=
  WP.mono (reduce_ok (fun t ht => cntE_ok t ht) h.good h.hZ h.w1 h.w2 (by omega)
    (by omega)) fun _ ⟨_, hv, ha, hk⟩ => ⟨h.arr ha (by decide) (by decide) (by decide) hk, hv, ha⟩

theorem reduceXRK (h : KCtx s t B Z w minv N) :
    WP isa (seqs (reduce cntXR)) t fun t' => KCtx s t' B Z w minv N ∧
      (0 < wv t.mem B (slot w aM) w →
        wv t'.mem B (slot w aR) w = wv t.mem B (slot w aAcc) (2 * w + 2) % wv t.mem B (slot w aM) w) ∧
      Arrays B w [aR, aX, aT] t.mem t'.mem :=
  WP.mono (reduce_ok (fun t ht => cntXR_ok t ht) h.good h.hZ h.w1 h.w2 (by omega)
    (by omega)) fun _ ⟨_, hv, ha, hk⟩ => ⟨h.arr ha (by decide) (by decide) (by decide) hk, hv, ha⟩

end

end VG.Proof.Rsa.X86_64
