module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.CandidateArithmetic
public import VerifiedGarbage.Proof.Rsa.Ranges
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Proof.Bignum.CrtFrame
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Rsa.KeyMath
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Reduce
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import Mathlib.Tactic.Widget.Calc
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Subtract
import VerifiedGarbage.Proof.Rsa.X86_64.Loops

/-! ### `Dsa.X86_64.Generation.CandidateReduction`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Generation.Increment`, which this module and modules that import it used -/

section

/-! # Incrementing the even difference in candidate reduction -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Bignum.X86_64
open VG.Proof.Rsa.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

theorem incrementEven_ok {s : State} {B : Addr} {Z w dst : Nat}
    (h : Ws s B Z w) (hd : dst < 16)
    (heven : wv s.mem B (slot w dst) w % 2 = 0) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.incrementEven dst)) s fun t =>
      wv t.mem B (slot w dst) w = wv s.mem B (slot w dst) w + 1 ∧
      Outside B (slot w dst) 8 s.mem t.mem ∧
      Keep [.r12, .r9, .rbx, .rax] s t := by
  have hn := h.scr.nowrap
  have sd := h.sl hd
  have hw : 1 ≤ w := by have := h.w1; omega_using [this]
  unfold Impl.Dsa.X86_64.Generation.incrementEven
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨_, h9, hm₁, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok dst (r := .rbx) (by decide)
    ((k₁.gpr (by decide)).trans h.rdi) h9) fun s₂ ⟨hbx, hm₂, k₂⟩ => ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).2.2
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem =
      s.mem.writeW (off B (slot w dst)) (word s.mem B (slot w dst) + 1)) (by
    xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₂.ld (d := slot w dst) (by omega_using [sd]), hs₂.st (d := slot w dst) (by omega_using [sd]), hm₂, hm₁]) rfl)
    fun t ⟨hm, k₃⟩ => ?_
  have ho : Outside B (slot w dst) 8 s.mem t.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by omega_using [hn, sd])
  refine ⟨?_, ho, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  have e₀ := wv_low (m := s.mem) (B := B) (e := slot w dst) hw
  have e₁ := wv_low (m := t.mem) (B := B) (e := slot w dst) hw
  have hu := ho.wv (d := slot w dst + 8) (k := w - 1) (Or.inr (by omega_using [])) (by omega_using [hn, sd])
  have hv : word t.mem B (slot w dst) = word s.mem B (slot w dst) + 1 := by
    rw [hm, word_writeW_self]
  have hlo := (word s.mem B (slot w dst)).isLt
  rw [e₀] at heven
  have hb : (word s.mem B (slot w dst)).toNat + 1 < 2 ^ 64 := by omega_using [heven]
  rw [e₁, hu, hv, BitVec.toNat_add, Nat.mod_eq_of_lt (by simpa using hb), e₀]
  change (word s.mem B (slot w dst)).toNat + 1 + 2 ^ 64 * wv s.mem B (slot w dst + 8) (w - 1) =
    (word s.mem B (slot w dst)).toNat + 2 ^ 64 * wv s.mem B (slot w dst + 8) (w - 1) + 1
  omega_using []

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.Double`, which the modules that import this one used -/

section

/-! # Native doubling for the divisor and generator exponent -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Bignum.X86_64
open VG.Proof.Rsa.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

theorem doubleArray_ok {s : State} {B : Addr} {Z w dst : Nat}
    (h : Ws s B Z w) (hd : dst < 16)
    (hfit : 2 * wv s.mem B (slot w dst) w < 2 ^ (64 * w)) :
    WP isa (Impl.Dsa.X86_64.Generation.doubleArray dst) s fun t =>
      wv t.mem B (slot w dst) w = 2 * wv s.mem B (slot w dst) w ∧
      Outside B (slot w dst) (8 * w) s.mem t.mem ∧
      Keep [.r12, .r9, .rbp, .rbx, .rax, .r14] s t := by
  have sd := h.sl hd
  unfold Impl.Dsa.X86_64.Generation.doubleArray
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9, hm, k₁⟩ => ?_))
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.rbp]
      (Q := fun t => t.gpr .rbp = mask false ∧ t.mem = s₁.mem) (by xrun) rfl)
      fun s₂ ⟨⟨hbp, hm₂⟩, k₂⟩ => ?_)
  refine WP.mono (base_ok dst (r := .rbx) (by decide)
    (((k₁.trans k₂).gpr (by decide)).trans h.rdi)
    ((k₂.gpr (by decide)).trans h9)) fun s₃ ⟨hbx, hm₃, k₃⟩ => ?_
  have k := (k₁.trans k₂).trans k₃
  refine WP.mono (shl_ok (h.scr.congr k.2.2) hbx
    (((k₂.trans k₃).gpr (by decide)).trans h12)
    ((k₃.gpr (by decide)).trans hbp)
    (by have := h.w1; omega_using [this]) (by have := h.w2; omega_using [this]) (by omega_using [sd]))
    fun t ⟨c, _, hv, ho, kt⟩ => ?_
  rw [hm₃, hm₂, hm] at hv ho
  refine ⟨?_, ho, (k.trans kt).mono (by decide)⟩
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one,
    Nat.add_zero] at hv <;> omega_arith

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Complete native p-candidate reduction, retaining the quotient -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/Reduce.lean`, which only this module imported.
section

/-! # Native remainder subtraction and increment implement p reduction -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.Bignum
open VG.Proof.Dsa.Generation VG.Proof.MlKem.X86_64

theorem reduceRemainder_ok {s : State} {B : Addr} {Z w dst src rem x q : Nat}
    (h : Ws s B Z w) (hd : dst < 16) (hx : src < 16) (hr : rem < 16)
    (hdx : dst ≠ src) (hdr : dst ≠ rem)
    (hval : wv s.mem B (slot w src) w = x)
    (hrem : wv s.mem B (slot w rem) (w + 1) = x % (2 * q)) :
    WP isa (.seq (Impl.Dsa.X86_64.Generation.subtractRemainder dst src rem)
      (.block (Impl.Dsa.X86_64.Generation.incrementEven dst))) s fun t =>
      wv t.mem B (slot w dst) w = x + 1 - x % (2 * q) ∧
      Outside B (slot w dst) (8 * w) s.mem t.mem ∧
      Keep [.r12, .r9, .rbp, .r8, .r10, .rsi, .rax, .r14, .rbx] s t := by
  have hmod := Nat.mod_le x (2 * q)
  have hbound : x < 2 ^ (64 * w) := hval ▸ wv_lt s.mem B (slot w src) w
  have hrem' : wv s.mem B (slot w rem) w = x % (2 * q) := by
    rw [wv_low_of_lt (Nat.le_succ w) (by rw [hrem]; omega), hrem]
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
    have hv : x - x % (2 * q) = 2 * q * (x / (2 * q)) := by omega
    rw [hv]
    simp [Nat.mul_assoc]
  refine WP.mono (incrementEven_ok hwu hd he) fun t ⟨ht, hot, kt⟩ => ?_
  refine ⟨?_, ?_, (ku.trans kt).mono (by decide)⟩
  · rw [ht, hu, pReduction_sub]
  · intro a ha
    rw [hot a (by have := h.w1; omega), ho a ha]

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.Bignum VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64
open VG.Impl.Rsa.X86_64.Keys VG.Proof.Dsa.Generation VG.Proof.Rsa

theorem reduceCandidate_ok {s : State} {B : Addr} {Z w x q : Nat}
    (h : Ws s B Z w) (hx : wv s.mem B (slot w 0) w = x)
    (hq : wv s.mem B (slot w 2) w = 2 * q) (hqpos : 0 < q) :
    WP isa Impl.Dsa.X86_64.Generation.reduceCandidate s fun t =>
      Ws t B Z w ∧ wv t.mem B (slot w 5) w = x + 1 - x % (2 * q) ∧
      wv t.mem B (slot w 0) w = x / (2 * q) ∧
      Frm B [ar w 4, ar w 0, ar w 1, ar w 3, ar w 5] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have hn := h.scr.nowrap
  have hr : ∀ j < 16, slot w j + 8 * w ≤ 2 ^ 64 := by
    intro j hj; have := h.sl hj; omega_using [hn, this]
  unfold Impl.Dsa.X86_64.Generation.reduceCandidate
  simp only [seqs]
  refine WP.seq (WP.mono (copyA_ok h (by decide : 4 < 16) (by decide : 0 < 16) (by decide))
    fun u ⟨hu, hou, ku⟩ => ?_)
  have fu : Frm B [ar w 4] s.mem u.mem :=
    Frm.of_outside (hou.mono (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_using [])) (by simp [ar])
  have wu := h.congr fu (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot w 4 _) ku (by decide)
  have ux : wv u.mem B (slot w 0) w = x := by rw [fu.wv_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r hr; rcases hr with rfl <;> simp only [slot, hdrBytes] <;> omega_using []) (hr 0 (by decide))]; exact hx
  have uq : wv u.mem B (slot w 2) w = 2 * q := by rw [fu.wv_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r hr; rcases hr with rfl <;> simp only [slot, hdrBytes] <;> omega_using []) (hr 2 (by decide))]; exact hq
  refine WP.seq (WP.mono (candidateDivision_ok wu.scr wu.rdi wu.hw wu.hS
    (by have := wu.w1; omega_using [this]) wu.w2 wu.hZ (iQ := 0) (iR := 1) (iD := 2) (iT := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ux uq hqpos) fun v ⟨_, fv, kv, vr, vq, _⟩ => ?_)
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

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # The byte-to-integer bridge for p-candidate arithmetic -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/ReductionExponent.lean`, which only this module imported.
section

/-! # Candidate reduction also produces the generator exponent -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.Bignum VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64 VG.Proof.Rsa VG.Proof.Dsa.Generation

theorem reduceExponent_ok {s : State} {B : Addr} {Z w x q : Nat}
    (h : Ws s B Z w) (hx : wv s.mem B (slot w 0) w = x)
    (hq : wv s.mem B (slot w 2) w = 2 * q) (hqpos : 0 < q) :
    WP isa (.seq Impl.Dsa.X86_64.Generation.reduceCandidate
      (Impl.Dsa.X86_64.Generation.doubleArray 0)) s fun t =>
      Ws t B Z w ∧ wv t.mem B (slot w 5) w = x + 1 - x % (2 * q) ∧
      wv t.mem B (slot w 0) w = (x + 1 - x % (2 * q) - 1) / q ∧
      Frm B [ar w 4, ar w 0, ar w 1, ar w 3, ar w 5] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
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

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 VG.Impl.Bignum.X86_64 VG.Proof.Rsa

/-- Padded loads preserve the arithmetic header and every other array. -/
theorem loadCandidateArray_ok {s : State} {B p : Addr} {Z w a ptr len : Nat} {bs : List Byte}
    (h : Ws s B Z w) (ha : a < 16) (hptr : ptr < 32) (hlen : len < 32)
    (hp : word s.mem B (8 * ptr) = p) (hl : word s.mem B (8 * len) = BitVec.ofNat 64 bs.length)
    (src : Src s B Z p bs) (hpos : 1 ≤ bs.length) (hfit : bs.length ≤ 8 * w) :
    WP isa (seqs (Impl.Rsa.X86_64.Keys.loadA a ptr len)) s fun t =>
      Ws t B Z w ∧ wv t.mem B (slot w a) w = Spec.Rsa.os2ip bs ∧
      Frm B [ar w a] s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (loadA_ok h ha hptr hlen hp hl src rfl hpos hfit) fun t ⟨hv, ho, hk⟩ => ?_
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
    WP isa Impl.Dsa.X86_64.Generation.candidateArithmetic s fun t =>
      Ws t B Z w ∧
      wv t.mem B (slot w 5) w = Spec.Rsa.os2ip xb + 1 - Spec.Rsa.os2ip xb % (2 * Spec.Rsa.os2ip qb) ∧
      wv t.mem B (slot w 0) w =
        (Spec.Rsa.os2ip xb + 1 - Spec.Rsa.os2ip xb % (2 * Spec.Rsa.os2ip qb) - 1) / Spec.Rsa.os2ip qb ∧
      Frm B [ar w 0, ar w 1, ar w 2, ar w 3, ar w 4, ar w 5] s.mem t.mem ∧ Keep mmRegs s t := by
  change WP isa (.seq (seqs (Impl.Rsa.X86_64.Keys.loadA 0 16 17))
    (.seq (seqs (Impl.Rsa.X86_64.Keys.loadA 2 18 19))
      (.seq (Impl.Dsa.X86_64.Generation.doubleArray 2)
        (.seq Impl.Dsa.X86_64.Generation.reduceCandidate (Impl.Dsa.X86_64.Generation.doubleArray 0))))) s _
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
  change WP isa (.seq Impl.Dsa.X86_64.Generation.reduceCandidate
    (Impl.Dsa.X86_64.Generation.doubleArray 0)) z _
  refine WP.mono (reduceExponent_ok hz zx (by rw [zq, vq]) hqpos) fun t ⟨ht, tp, te, ft, kt⟩ => ?_
  exact ⟨ht, tp, te, (fu.append (fv.append (fz.append ft))).mono (by simp),
    (((ku.trans kv).trans kz).trans kt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
