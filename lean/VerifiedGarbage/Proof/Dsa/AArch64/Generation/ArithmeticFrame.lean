module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Double
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Increment
public import VerifiedGarbage.Proof.Rsa.AArch64.Div
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base

/-! Arithmetic instructions preserve the workspace even when a result overflows. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64 VG.Proof.MlKem.AArch64

theorem doubleArray_ws {s : State} {B : Addr} {Z w dst : Nat}
    (h : VG.Proof.Rsa.AArch64.Ws s B Z w) (hd : dst < 16) :
    WP isa (Impl.Dsa.AArch64.Generation.doubleArray dst) s fun t => VG.Proof.Rsa.AArch64.Ws t B Z w := by
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
    ((k₃.gpr .x14 (by decide)).trans h14) (by have := h.w1; omega)
    (by have := h.w2; omega) (by omega)) fun t ⟨_, _, ho, kt⟩ => ?_
  rw [hm₃, hm₂, hm₁] at ho
  exact h.congr' (Frm.of_outside ho (List.mem_singleton_self _))
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact KMut.ofSlot _ _ _)
    (k.trans kt) (by decide)

theorem copyArray_ws {s : State} {B : Addr} {Z w o a : Nat} (h : VG.Proof.Rsa.AArch64.Ws s B Z w)
    (ho : o < 16) (ha : a < 16) (hoa : o ≠ a) :
    WP isa (copyA o a) s fun t => VG.Proof.Rsa.AArch64.Ws t B Z w := by
  refine WP.mono (copyA_ok h ho ha hoa) fun t ⟨_, out, _, _, hk⟩ => ?_
  exact h.congr' (Frm.of_outside out (List.mem_singleton_self _))
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact KMut.ofSlot _ _ _) hk (by decide)

theorem divideArray_ws {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.AArch64.Ws s B Z w) :
    WP isa (divmod 0 1 2 3) s fun t => VG.Proof.Rsa.AArch64.Ws t B Z w := by
  refine WP.mono (divmod_ok h (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun t ⟨_, hf, hk, _⟩ => ?_
  exact h.congr' hf (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact KMut.ofSlot _ _ _) hk (by decide)

theorem subtractArray_ws {s : State} {B : Addr} {Z w : Nat} (h : VG.Proof.Rsa.AArch64.Ws s B Z w) :
    WP isa (seqs (subA 5 4 1)) s fun t => VG.Proof.Rsa.AArch64.Ws t B Z w := by
  refine WP.mono (subA_ok h (by decide) (by decide) (by decide) (Or.inr (by decide)) (by decide))
    fun t ⟨_, out, _, _, _, hk⟩ => ?_
  exact h.congr' (Frm.of_outside out (List.mem_singleton_self _))
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact KMut.ofSlot _ _ _) hk (by decide)

theorem incrementEven_ws {s : State} {B : Addr} {Z w dst : Nat}
    (h : VG.Proof.Rsa.AArch64.Ws s B Z w) (hd : dst < 16) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.incrementEven dst)) s fun t => VG.Proof.Rsa.AArch64.Ws t B Z w := by
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
  exact h.congr' (Frm.of_outside ho (List.mem_singleton_self _))
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact KMut.ofSlot _ _ _)
    ((k₁.trans k₂).trans k₃) (by decide)

end VG.Proof.Dsa.AArch64.Generation
