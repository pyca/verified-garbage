module

public import VerifiedGarbage.Proof.Rsa.X86_64.WordShadowSetup
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Framework.Offset

/-! # Copies into the validation reducer's second workspace -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordValidation

open VG VG.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- A write within the second workspace has a simple original-base frame. -/
theorem widen {B : Addr} {a n d l : Nat} {m m' : Mem} (hf : Outside B d l m m')
    (hd : a ≤ d) (hl : d + l ≤ a + n) : Outside B a n m m' := by
  intro x hx
  apply hf x
  omega_using [hx, hd, hl]

/-- Data-array writes preserve the second workspace's header. -/
theorem ws_after {s t : State} {B : Addr} {Z w d l : Nat} {rs : List Reg}
    (h : VG.Proof.Rsa.X86_64.Ws s (off B (start w)) (span w) w)
    (hn : B.toNat + Z ≤ 2 ^ 64) (hZ : start w + span w ≤ Z)
    (hd : start w + 256 ≤ d) (hf : Outside B d l s.mem t.mem) (hk : Keep rs s t) (hr : .rdi ∉ rs) :
    VG.Proof.Rsa.X86_64.Ws t (off B (start w)) (span w) w := by
  have hh (i : Nat) (hi : i < 32) :
      word t.mem (off B (start w)) (8 * i) = word s.mem (off B (start w)) (8 * i) := by
    rw [word_view, word_view]
    apply hf.word (Or.inl (by omega_using [hi, hd]))
      (by have hs : 256 ≤ span w := by simp only [span, slot, hdrBytes]; omega_arith
          omega_using [hn, hZ, hi, hs])
  exact ⟨h.scr.congr hk.2.2, (hk.gpr hr).trans h.rdi, (hh sW (by decide)).trans h.hw,
    (hh Keys.sStride (by decide)).trans h.hS,
    fun j hj => (hh (sArr j) (by unfold sArr; omega_using [hj])).trans (h.harr j hj), h.hZ, h.w1, h.w2⟩

/-- A pointer-only setup preserves the second workspace invariant. -/
theorem ws_same {s t : State} {B : Addr} {Z w : Nat} {rs : List Reg}
    (h : VG.Proof.Rsa.X86_64.Ws s B Z w) (hm : t.mem = s.mem) (hk : Keep rs s t) (hr : .rdi ∉ rs) :
    VG.Proof.Rsa.X86_64.Ws t B Z w :=
  h.congr (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) hk hr

/-- The generic copy routine, expressed entirely as offsets in the original allocation. -/
theorem copy_ok {s : State} {B : Addr} {Z w eS eD : Nat} (h : Scr s B Z)
    (hsi : s.gpr .rsi = off B eS) (hbx : s.gpr .rbx = off B eD) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hS : eS + 8 * w ≤ Z) (hD : eD + 8 * w ≤ Z)
    (hsep : eS + 8 * w ≤ eD ∨ eD + 8 * w ≤ eS) :
    WP isa copyWords s fun t => wv t.mem B eD w = wv s.mem B eS w ∧
      Outside B eD (8 * w) s.mem t.mem ∧ Keep [.rax, .r14] s t := by
  have hn := h.nowrap
  refine WP.mono (copyWords_ok hsi hbx h12 hw hw' (by omega_using [hn, hD])
    (fun j hj => h.ld (by omega_using [hS, hj])) (fun j hj => h.st (by omega_using [hD, hj]))
    (fun j hj b hb => by
      rw [ofs_off B (by omega_using [hn, hS, hj, hb])]
      omega_using [hsep, hj, hb])) fun _ ⟨hv, _, ho, hk⟩ => ⟨hv, ho, hk⟩

/-- The modulus source remains pinned while its destination is computed. -/
theorem modulusSetup_ok {s : State} {B : Addr} {w : Nat}
    (hdi : s.gpr .rdi = off B (start w)) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (h10 : s.gpr .r10 = off B (slot w CheckKey.aM)) :
    WP isa (.block WordValidation.modulusSetup) s fun t =>
      t.gpr .rsi = off B (slot w CheckKey.aM) ∧
      t.gpr .rbx = off (off B (start w)) (slot w WordDivide.aM) ∧ t.mem = s.mem ∧ Keep [.rsi, .rbx] s t := by
  unfold WordValidation.modulusSetup
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rsi] (Q := fun t => t.gpr .rsi = off B (slot w CheckKey.aM) ∧ t.mem = s.mem)
    (by xrun [h10]) rfl) fun t₁ ⟨⟨hsi, m₁⟩, k₁⟩ => ?_
  refine WP.mono (VG.Proof.Rsa.X86_64.base_ok WordDivide.aM (r := .rbx) (by decide)
    ((k₁.gpr (by decide)).trans hdi) ((k₁.gpr (by decide)).trans h9)) fun t ⟨hbx, m₂, k₂⟩ => ?_
  exact ⟨(k₂.gpr (by decide)).trans hsi, hbx, m₂.trans m₁, (k₁.trans k₂).mono (by decide)⟩

end VG.Proof.Rsa.X86_64.WordValidation
