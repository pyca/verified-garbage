module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.CandidateArithmetic
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
public import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Reduce
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Candidate
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close
import VerifiedGarbage.Proof.Rsa.AArch64.Div
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate

/-! ### `Dsa.AArch64.Generation.Double`, which only this module used -/

section

/-! Doubling the subgroup order and the saved generator exponent in native code. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.MlKem.AArch64

theorem doubleArray_ok {s : State} {B : Addr} {Z w dst : Nat}
    (h : Ws s B Z w) (hd : dst < 16)
    (hfit : 2 * wv s.mem B (slot w dst) w < 2 ^ (64 * w)) :
    WP isa (Impl.Dsa.AArch64.Generation.doubleArray dst) s fun t =>
      wv t.mem B (slot w dst) w = 2 * wv s.mem B (slot w dst) w ∧
      Outside B (slot w dst) (8 * w) s.mem t.mem ∧ Keep mmRegs s t := by
  have sd := h.sl hd
  unfold Impl.Dsa.AArch64.Generation.doubleArray
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, hm₁, _⟩, k₁⟩ => ?_))
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x7, .x14, .x3]
    (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 w ∧ t.c = false ∧ t.mem = s₁.mem)
    (by brun [h12]) rfl rfl rfl) fun s₂ ⟨⟨h14, hc, hm₂⟩, k₂⟩ => ?_)
  refine WP.mono (base_ok dst .x16 (((k₁.trans k₂).gpr .x0 (by decide)).trans h.x0)
    ((k₂.gpr .x11 (by decide)).trans h11)) fun s₃ ⟨⟨h16, hm₃, hc₃⟩, k₃⟩ => ?_
  have k := (k₁.trans k₂).trans k₃
  refine WP.mono (shl_ok (h.scr.congr k.wr) h16
    ((k₃.gpr .x14 (by decide)).trans h14) (by have := h.w1; omega_using [this])
    (by have := h.w2; omega_using [this]) (by omega_using [sd])) fun t ⟨hv, _, ho, kt⟩ => ?_
  rw [hc₃, hc, hm₃, hm₂, hm₁] at hv
  rw [hm₃, hm₂, hm₁] at ho
  refine ⟨?_, ho, (k.trans kt).mono (by decide)⟩
  cases he : t.c <;> rw [he] at hv <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hv <;> omega_arith

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.CandidateReduction`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.Reduce`, which only this module used -/

section

/-! # Native remainder subtraction and increment implement p reduction -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/Subtract.lean`, which only this module imported.
section

/-! Reuse RSA's array subtraction for the candidate's division remainder. -/
section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64

theorem subtractRemainder_ok {s : State} {B : Addr} {Z w dst src rem : Nat}
    (h : Ws s B Z w) (hd : dst < 16) (hx : src < 16) (hr : rem < 16)
    (hdx : dst ≠ src) (hdr : dst ≠ rem)
    (hle : wv s.mem B (slot w rem) w ≤ wv s.mem B (slot w src) w) :
    WP isa (seqs (subA dst src rem)) s fun t =>
      wv t.mem B (slot w dst) w = wv s.mem B (slot w src) w - wv s.mem B (slot w rem) w ∧
      Outside B (slot w dst) (8 * w) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (subA_ok h hd hx hr (.inr hdx) hdr) fun t ⟨hv, ho, _, _, _, hk⟩ => ?_
  refine ⟨?_, ho, hk.mono (by decide)⟩
  have hxlt := wv_lt s.mem B (slot w src) w
  have holt := wv_lt t.mem B (slot w dst) w
  cases hc : (!t.c) <;> rw [hc] at hv <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hv <;> omega

end VG.Proof.Dsa.AArch64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/Increment.lean`, which only this module imported.
section

/-! The even candidate difference can be incremented without carry propagation. -/
section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.MlKem.AArch64

private theorem low_word {m : Mem} {B : Addr} {e w : Nat} (hw : 1 ≤ w) :
    wv m B e w = (word m B e).toNat + 2 ^ 64 * wv m B (e + 8) (w - 1) := by
  have h := wv_add m B e 1 (w - 1)
  rw [show 1 + (w - 1) = w by omega] at h
  simpa only [wv, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.pow_zero, Nat.one_mul, Nat.mul_one] using h

theorem incrementEven_ok {s : State} {B : Addr} {Z w dst : Nat}
    (h : Ws s B Z w) (hd : dst < 16) (heven : wv s.mem B (slot w dst) w % 2 = 0) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.incrementEven dst)) s fun t =>
      wv t.mem B (slot w dst) w = wv s.mem B (slot w dst) w + 1 ∧
      Outside B (slot w dst) 8 s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := h.scr.nowrap
  have sd := h.sl hd
  have hw : 1 ≤ w := by have := h.w1; omega
  unfold Impl.Dsa.AArch64.Generation.incrementEven
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨_, h11, hm₁, _⟩, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok dst .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11)
    fun s₂ ⟨⟨h16, hm₂, _⟩, k₂⟩ => ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).wr
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem =
    s.mem.writeW (off B (slot w dst)) (word s.mem B (slot w dst) + 1))
    (by brun [h16, hs₂.ld (d := slot w dst) (by omega), hs₂.st (d := slot w dst) (by omega), hm₂, hm₁]; rfl)
    rfl rfl rfl) fun t ⟨hm, k₃⟩ => ?_
  have ho : Outside B (slot w dst) 8 s.mem t.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by omega)
  refine ⟨?_, ho, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  have e₀ := low_word (m := s.mem) (B := B) (e := slot w dst) hw
  have e₁ := low_word (m := t.mem) (B := B) (e := slot w dst) hw
  have hu := ho.wv (d := slot w dst + 8) (k := w - 1) (Or.inr (by omega)) (by omega)
  have hv : word t.mem B (slot w dst) = word s.mem B (slot w dst) + 1 := by
    rw [hm, word_writeW_self]
  have hlo := (word s.mem B (slot w dst)).isLt
  rw [e₀] at heven
  have hb : (word s.mem B (slot w dst)).toNat + 1 < 2 ^ 64 := by omega
  rw [e₁, hu, hv, BitVec.toNat_add, Nat.mod_eq_of_lt (by simpa using hb), e₀]
  change (word s.mem B (slot w dst)).toNat + 1 + 2 ^ 64 * wv s.mem B (slot w dst + 8) (w - 1) =
    (word s.mem B (slot w dst)).toNat + 2 ^ 64 * wv s.mem B (slot w dst + 8) (w - 1) + 1
  omega_using []

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Dsa.Generation VG.Proof.MlKem.AArch64

private theorem low_of_lt {m : Mem} {B : Addr} {e v w : Nat} (hv : v ≤ w)
    (h : wv m B e w < 2 ^ (64 * v)) : wv m B e v = wv m B e w := by
  have e1 := wv_add m B e v (w - v)
  rw [show v + (w - v) = w by omega_using [hv]] at e1
  have hz : wv m B (e + 8 * v) (w - v) = 0 := by
    rcases Nat.eq_zero_or_pos (wv m B (e + 8 * v) (w - v)) with h0 | h0
    · exact h0
    · exfalso
      have : 2 ^ (64 * v) ≤ 2 ^ (64 * v) * wv m B (e + 8 * v) (w - v) := Nat.le_mul_of_pos_right _ h0
      omega_using [h, e1, this]
  rw [e1, hz]; simp

theorem reduceRemainder_ok {s : State} {B : Addr} {Z w dst src rem x q : Nat}
    (h : Ws s B Z w) (hd : dst < 16) (hx : src < 16) (hr : rem < 16)
    (hdx : dst ≠ src) (hdr : dst ≠ rem)
    (hval : wv s.mem B (slot w src) w = x)
    (hrem : wv s.mem B (slot w rem) (w + 1) = x % (2 * q)) :
    WP isa (.seq (seqs (subA dst src rem))
      (.block (Impl.Dsa.AArch64.Generation.incrementEven dst))) s fun t =>
      wv t.mem B (slot w dst) w = x + 1 - x % (2 * q) ∧
      Outside B (slot w dst) (8 * w) s.mem t.mem ∧
      Keep mmRegs s t := by
  have hmod := Nat.mod_le x (2 * q)
  have hbound : x < 2 ^ (64 * w) := hval ▸ wv_lt s.mem B (slot w src) w
  have hrem' : wv s.mem B (slot w rem) w = x % (2 * q) := by
    rw [low_of_lt (Nat.le_succ w) (by rw [hrem]; omega_using [hmod, hbound]), hrem]
  refine WP.seq (WP.mono (subtractRemainder_ok h hd hx hr hdx hdr
    (by rw [hval, hrem']; exact hmod)) fun u ⟨hu, ho, ku⟩ => ?_)
  rw [hval, hrem'] at hu
  have hf : Frm B [(slot w dst, 8 * w)] s.mem u.mem := Frm.of_outside ho (by simp)
  have hwu := h.congr hf
    (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot w dst (8 * w))
    ku (by decide)
  have he : wv u.mem B (slot w dst) w % 2 = 0 := by
    rw [hu]
    have hm := Nat.mod_add_div x (2 * q)
    have hv : x - x % (2 * q) = 2 * q * (x / (2 * q)) := by omega_using [hm]
    rw [hv]
    simp [Nat.mul_assoc]
  refine WP.mono (incrementEven_ok hwu hd he) fun t ⟨ht, hot, kt⟩ => ?_
  refine ⟨?_, ?_, (ku.trans kt).mono (by decide)⟩
  · rw [ht, hu, pReduction_sub]
  · intro a ha
    rw [hot a (by have := h.w1; omega_using [ha, this]), ho a ha]

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! # Complete native p-candidate reduction, retaining the quotient -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.Bignum VG.Proof.MlKem.AArch64
open VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum.AArch64
open VG.Impl.Rsa.AArch64.Keys VG.Proof.Dsa.Generation VG.Proof.Rsa

theorem reduceCandidate_ok {s : State} {B : Addr} {Z w x q : Nat}
    (h : Ws s B Z w) (hx : wv s.mem B (slot w 0) w = x)
    (hq : wv s.mem B (slot w 2) w = 2 * q) (hqpos : 0 < q) :
    WP isa Impl.Dsa.AArch64.Generation.reduceCandidate s fun t =>
      Ws t B Z w ∧ wv t.mem B (slot w 5) w = x + 1 - x % (2 * q) ∧
      wv t.mem B (slot w 0) w = x / (2 * q) ∧
      Frm B [ar w 4, ar w 0, ar w 1, ar w 3, ar w 5] s.mem t.mem ∧
      Keep mmRegs s t := by
  have hn := h.scr.nowrap
  have hr : ∀ j < 16, slot w j + 8 * w ≤ 2 ^ 64 := by
    intro j hj; have := h.sl hj; omega_using [hn, this]
  unfold Impl.Dsa.AArch64.Generation.reduceCandidate
  refine WP.seq (WP.mono (copyA_ok h (by decide : 4 < 16) (by decide : 0 < 16) (by decide))
    fun u ⟨hu, hou, _, _, ku⟩ => ?_)
  have fu : Frm B [ar w 4] s.mem u.mem :=
    Frm.of_outside (hou.mono (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_using [])) (by simp [ar])
  have wu := h.congr fu (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot w 4 _) ku (by decide)
  have ux : wv u.mem B (slot w 0) w = x := by rw [fu.wv_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r hr; rcases hr with rfl <;> simp only [slot, hdrBytes] <;> omega_using []) (hr 0 (by decide))]; exact hx
  have uq : wv u.mem B (slot w 2) w = 2 * q := by rw [fu.wv_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r hr; rcases hr with rfl <;> simp only [slot, hdrBytes] <;> omega_using []) (hr 2 (by decide))]; exact hq
  refine WP.seq (WP.mono (divmod_ok wu (iQ := 0) (iR := 1) (iD := 2) (iT := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun v ⟨_, fv, kv, hmath⟩ => ?_)
  obtain ⟨vr, vq⟩ := hmath (by rw [uq]; omega_using [hqpos])
  rw [ux, uq] at vr vq
  have wv' := wu.congr fv (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Mut.ofSlot _ _ _) kv (by decide)
  have vx : wv v.mem B (slot w 4) w = x := by
    rw [fv.wv_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r hr; rcases hr with rfl | rfl | rfl <;> simp only [slot, hdrBytes] <;> omega_using []) (hr 4 (by decide)), hu, hx]
  refine WP.mono (reduceRemainder_ok wv' (by decide : 5 < 16) (by decide : 4 < 16)
    (by decide : 1 < 16) (by decide) (by decide) vx vr) fun t ⟨tp, hot, kt⟩ => ?_
  have ft : Frm B [ar w 5] v.mem t.mem :=
    Frm.of_outside (hot.mono (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_using [])) (by simp [ar])
  have wt := wv'.congr ft (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot _ _ _) kt (by decide)
  refine ⟨wt, tp, ?_, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  · rw [ft.wv_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r hr; rcases hr with rfl <;> simp only [slot, hdrBytes] <;> omega_using []) (hr 0 (by decide)), vq]
  · exact (fu.append (fv.append ft)).mono (by simp)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # The byte-to-integer bridge for p-candidate arithmetic -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/ReductionExponent.lean`, which only this module imported.
section

/-! # Candidate reduction also produces the generator exponent -/

section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.Bignum VG.Proof.MlKem.AArch64
open VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.Rsa VG.Proof.Dsa.Generation

theorem reduceExponent_ok {s : State} {B : Addr} {Z w x q : Nat}
    (h : Ws s B Z w) (hx : wv s.mem B (slot w 0) w = x)
    (hq : wv s.mem B (slot w 2) w = 2 * q) (hqpos : 0 < q) :
    WP isa (.seq Impl.Dsa.AArch64.Generation.reduceCandidate
      (Impl.Dsa.AArch64.Generation.doubleArray 0)) s fun t =>
      Ws t B Z w ∧ wv t.mem B (slot w 5) w = x + 1 - x % (2 * q) ∧
      wv t.mem B (slot w 0) w = (x + 1 - x % (2 * q) - 1) / q ∧
      Frm B [ar w 4, ar w 0, ar w 1, ar w 3, ar w 5] s.mem t.mem ∧
      Keep mmRegs s t := by
  have hxlt : x < 2 ^ (64 * w) := hx ▸ wv_lt s.mem B (slot w 0) w
  have he : 2 * (x / (2 * q)) ≤ x := by
    calc
      2 * (x / (2 * q)) ≤ q * (2 * (x / (2 * q))) := Nat.le_mul_of_pos_left _ hqpos
      _ = 2 * q * (x / (2 * q)) := by ac_rfl
      _ ≤ x := Nat.mul_div_le x (2 * q)
  refine WP.seq (WP.mono (reduceCandidate_ok h hx hq hqpos) fun u ⟨hu, hp, hquot, hf, hk⟩ => ?_)
  refine WP.mono (doubleArray_ok hu (by decide : 0 < 16) (by rw [hquot]; omega))
    fun t ⟨ht, ho, kt⟩ => ?_
  have ft : Frm B [ar w 0] u.mem t.mem :=
    Frm.of_outside (ho.mono (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega)) (by simp [ar])
  have wt := hu.congr ft (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot _ _ _) kt (by decide)
  refine ⟨wt, ?_, ?_, ?_, (hk.trans kt).mono (by decide)⟩
  · rw [ft.wv_eq (by
      simp only [List.mem_singleton]; rintro r rfl
      simp only [slot, hdrBytes]; omega) (by have := h.sl (by decide : 5 < 16); have := h.scr.nowrap; omega), hp]
  · rw [ht, hquot, pReduction_generatorExponent x hqpos]
  · exact hf.trans (ft.mono (by simp))

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Rsa

/-- Padded loads preserve the arithmetic header and every other array. -/
theorem loadCandidateArray_ok {s : State} {B p : Addr} {Z w a ptr len : Nat} {bs : List Byte}
    (h : Ws s B Z w) (ha : a < 16) (hptr : ptr < 32) (hlen : len < 32)
    (hp : word s.mem B (8 * ptr) = p) (hl : word s.mem B (8 * len) = BitVec.ofNat 64 bs.length)
    (src : Src s B Z p bs) (hpos : 1 ≤ bs.length) (hfit : bs.length ≤ 8 * w) :
    WP isa (seqs (Impl.Rsa.AArch64.Keys.loadA a ptr len)) s fun t =>
      Ws t B Z w ∧ wv t.mem B (slot w a) w = Spec.Rsa.os2ip bs ∧
      Frm B [ar w a] s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (loadA_ok h ha hptr hlen hp hl src rfl hpos hfit) fun t ⟨hv, ho, _, _, hk⟩ => ?_
  have hf : Frm B [ar w a] s.mem t.mem := Frm.of_outside ho (by simp [ar])
  exact ⟨h.congr hf (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot _ _ _) hk (by decide),
    hv, hf, hk.mono (by decide)⟩

theorem candidateArithmetic_ok {s : State} {B xp qp : Addr} {Z w : Nat} {xb qb : List Byte}
    (h : Ws s B Z w)
    (hxp : word s.mem B 128 = xp) (hxl : word s.mem B 136 = BitVec.ofNat 64 xb.length)
    (hqp : word s.mem B 144 = qp) (hql : word s.mem B 152 = BitVec.ofNat 64 qb.length)
    (sx : Src s B Z xp xb) (sq : Src s B Z qp qb)
    (hxpos : 1 ≤ xb.length) (hxf : xb.length ≤ 8 * w)
    (hqposlen : 1 ≤ qb.length) (hqf : qb.length ≤ 8 * w)
    (hqpos : 0 < Spec.Rsa.os2ip qb) (hqfit : 2 * Spec.Rsa.os2ip qb < 2 ^ (64 * w)) :
    WP isa Impl.Dsa.AArch64.Generation.candidateArithmetic s fun t =>
      Ws t B Z w ∧
      wv t.mem B (slot w 5) w = Spec.Rsa.os2ip xb + 1 - Spec.Rsa.os2ip xb % (2 * Spec.Rsa.os2ip qb) ∧
      wv t.mem B (slot w 0) w =
        (Spec.Rsa.os2ip xb + 1 - Spec.Rsa.os2ip xb % (2 * Spec.Rsa.os2ip qb) - 1) / Spec.Rsa.os2ip qb ∧
      Frm B [ar w 0, ar w 1, ar w 2, ar w 3, ar w 4, ar w 5] s.mem t.mem ∧ Keep mmRegs s t := by
  change WP isa (.seq (seqs (Impl.Rsa.AArch64.Keys.loadA 0 16 17))
    (.seq (seqs (Impl.Rsa.AArch64.Keys.loadA 2 18 19))
      (.seq (Impl.Dsa.AArch64.Generation.doubleArray 2)
        (.seq Impl.Dsa.AArch64.Generation.reduceCandidate (Impl.Dsa.AArch64.Generation.doubleArray 0))))) s _
  refine WP.seq (WP.mono (loadCandidateArray_ok h (by decide : 0 < 16) (by decide : 16 < 32)
    (by decide : 17 < 32) hxp hxl sx hxpos hxf) fun u ⟨hu, ux, fu, ku⟩ => ?_)
  have uh : ∀ d, d + 8 ≤ 256 → word u.mem B d = word s.mem B d := by
    intro d hd
    exact fu.word_eq (by simp only [List.mem_singleton]; rintro r rfl; simp [slot, hdrBytes]; omega_using [hd])
      (by have := h.scr.nowrap; have := h.h256; omega_using [hd])
  have squ : Src u B Z qp qb := sq.congrK (fun a ha => fu a (by
    simp only [List.mem_singleton]; rintro r rfl
    have := h.sl (by decide : 0 < 16)
    dsimp only at *
    omega_using [ha, this])) ku
  refine WP.seq (WP.mono (loadCandidateArray_ok hu (by decide : 2 < 16) (by decide : 18 < 32)
    (by decide : 19 < 32) (by rw [uh 144 (by decide)]; exact hqp)
    (by rw [uh 152 (by decide)]; exact hql) squ hqposlen hqf) fun v ⟨hv, vq, fv, kv⟩ => ?_)
  refine WP.seq (WP.mono (doubleArray_ok hv (by decide : 2 < 16) (by rw [vq]; exact hqfit))
    fun z ⟨zq, ho, kz⟩ => ?_)
  have fz : Frm B [ar w 2] v.mem z.mem :=
    Frm.of_outside (ho.mono (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_using [])) (by simp [ar])
  have hz := hv.congr fz (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot _ _ _) kz (by decide)
  have zx : wv z.mem B (slot w 0) w = Spec.Rsa.os2ip xb := by
    have sep : ∀ r ∈ [ar w 2], slot w 0 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w 0 := by
      simp only [List.mem_singleton]; rintro r rfl; left; simp only [slot, hdrBytes]; omega_using []
    have room : slot w 0 + 8 * w ≤ 2 ^ 64 := by
      have := h.sl (by decide : 0 < 16); have := h.scr.nowrap; omega_arith
    rw [fz.wv_eq sep room, fv.wv_eq sep room, ux]
  change WP isa (.seq Impl.Dsa.AArch64.Generation.reduceCandidate
    (Impl.Dsa.AArch64.Generation.doubleArray 0)) z _
  refine WP.mono (reduceExponent_ok hz zx (by rw [zq, vq]) hqpos) fun t ⟨ht, tp, te, ft, kt⟩ => ?_
  exact ⟨ht, tp, te, (fu.append (fv.append (fz.append ft))).mono (by simp),
    (((ku.trans kv).trans kz).trans kt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation
