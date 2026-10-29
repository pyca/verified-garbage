module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Reduce
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Proof.Rsa.X86_64.Div
import VerifiedGarbage.Proof.Rsa.X86_64.Loops

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
  have hw : 1 ≤ w := by have := h.w1; omega
  unfold Impl.Dsa.X86_64.Generation.incrementEven
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨_, h9, hm₁, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok dst (r := .rbx) (by decide)
    ((k₁.gpr (by decide)).trans h.rdi) h9) fun s₂ ⟨hbx, hm₂, k₂⟩ => ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).2.2
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem =
      s.mem.writeW (off B (slot w dst)) (word s.mem B (slot w dst) + 1)) (by
    xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₂.ld (d := slot w dst) (by omega), hs₂.st (d := slot w dst) (by omega), hm₂, hm₁]) rfl)
    fun t ⟨hm, k₃⟩ => ?_
  have ho : Outside B (slot w dst) 8 s.mem t.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by omega)
  refine ⟨?_, ho, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  have e₀ := wv_low (m := s.mem) (B := B) (e := slot w dst) hw
  have e₁ := wv_low (m := t.mem) (B := B) (e := slot w dst) hw
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

end VG.Proof.Dsa.X86_64.Generation
