module
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.Front

import VerifiedGarbage.Proof.Ffdh.X86_64.R2
import VerifiedGarbage.Proof.Ffdh.X86_64.Scan
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH public-key validation on x86-64: subgroup membership -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPublic

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave)
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Ffdh VG.Proof.MlKem.X86_64

/-- With q: its first nonzero octet, `R² mod p`, `y^q mod p` and whether it is 1. -/
theorem cpQ_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {u : State} {B : Addr} {Z k : Nat} {mi : BitVec 64}
    {m₀ : Mem} {dp yp : Addr}
    (hc : SubMem u B Z (inner ((k + 7) / 8)) ((k + 7) / 8) ((k + 7) / 8) mi)
    (hv : XVals u B (inner ((k + 7) / 8)) ((k + 7) / 8) mi (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ dp k)))
    (hval : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ dp k)) k = true) (hk1 : 64 ≤ k)
    (hk2 : k ≤ 1024) (hZ : 128 * k + 256 ≤ Z) (h0 : u.gpr .rdi = B)
    (hWs : word u.mem B (8 * sWs) = off B (inner ((k + 7) / 8))) (hK : word u.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hQ : word u.mem B (8 * sQ) = dp + BitVec.ofNat 64 (2 * k)) (hY : word u.mem B (8 * sY) = yp)
    (hdom : Src u B Z dp (Spec.Rsa.bytesAt m₀ dp (3 * k)))
    (hy : Src u B Z yp (Spec.Rsa.bytesAt m₀ yp k)) :
    WP isa (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.subgroup M.mm E.code (.seq (.block r2Head) R.code))) u fun t =>
      t.gpr .rax = bit (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ yp k) ^
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k) %
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ dp k) = 1) ∧ t.gpr .rdi = B ∧ InScr B Z u.mem t.mem ∧ (∀ i < 6, word t.mem B (8 * i) = word u.mem B (8 * i)) ∧ Keep (.rdi :: mmRegs) u t := by
  have hroom := room_k hk1 hZ
  have hO : Outer u B Z ((k + 7) / 8) := Outer.of_mem hc h0 hroom (by omega_arith) (by omega_arith)
  have hq := src_slice (off := 2 * k) (len := k) hdom (by omega_arith)
  have hql : (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k).length = k := bytesAt_length _ _ _
  have hne : Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k ≠ [] := by
    intro h; rw [h] at hql; simp at hql; omega_arith
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckPublic.subgroup
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- The first nonzero octet of q.
  refine wp_seqs_append (by simp [scan]) (by simp) (WP.mono (scan_ok hO (show sQ < 32 by decide) hQ
    (by rw [hql]; exact hK) hne (by omega_arith) hq) fun u₁ ⟨hEp, hEl, _, f₁, k₁⟩ => ?_)
  have hr₁ : ∀ r ∈ [(8 * sEp, 8), (8 * sEl, 8)], 8 * 16 ≤ r.1 ∧ r.1 + r.2 ≤ 256 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [sEp, sEl, sFn] <;> omega_arith
  have hc₁ := hc.of_parent f₁ hr₁ k₁.2.2
  have hv₁ := hv.of_parent hc f₁ (fun r hr => (hr₁ r hr).2)
  have hO₁ : Outer u₁ B Z ((k + 7) / 8) := Outer.of_mem hc₁ ((k₁.gpr (by decide)).trans h0) hroom (by omega_arith)
    (by omega_arith)
  have hs₁ : ∀ i < 32, i ≠ sEp → i ≠ sEl → word u₁.mem B (8 * i) = word u.mem B (8 * i) := fun i hi h1 h2 =>
    f₁.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> unfold sEp sEl sFn at * <;> omega_arith) (by omega_arith)
  have i₁ : InScr B Z u.mem u₁.mem := InScr.of_frm f₁ fun r hr => by
    have := (hr₁ r hr).2; have := hroom; unfold inner slot hdrBytes at this; omega_arith
  -- Into the inner workspace, and `R² mod p`.
  have hWs₁ : word u₁.mem B (8 * sWs) = off B (inner ((k + 7) / 8)) := by
    rw [hs₁ _ (by decide) (by decide) (by decide)]; exact hWs
  refine wp_seqs_cons (by simp) (WP.mono (enter_ok hO₁ hWs₁) fun u₂ ⟨h0₂, hm₂, k₂⟩ => ?_)
  have hc₂ : SubCtx u₂ B Z (inner ((k + 7) / 8)) ((k + 7) / 8) ((k + 7) / 8) mi :=
    ⟨hc₁.scr.congr k₂.2.2, h0₂, by rw [hm₂]; exact hc₁.hdr, by rw [hm₂]; exact hc₁.link, by rw [hm₂]; exact hc₁.nw,
      by rw [hm₂]; exact hc₁.narr, hc₁.lo, hc₁.hi⟩
  have hv₂ : XVals u₂ B (inner ((k + 7) / 8)) ((k + 7) / 8) mi (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ dp k)) :=
    ⟨by rw [hm₂]; exact hv₁.n, by rw [hm₂]; exact hv₁.inv, by rw [hm₂]; exact hv₁.one⟩
  refine wp_seqs_cons (by simp [pow, Crt.loadArr]) (WP.mono (r2_ctx M R hc₂ hv₂ hval hk1 hk2 hZ)
    fun u₃ ⟨hm₃, f₃, k₃⟩ => ?_)
  -- The power and its comparison with 1.
  have hlead := lead_lt hne
  rw [hql] at hlead
  obtain ⟨hb₃, hi₃⟩ := child_frm hc₂ (by have := hroom; unfold inner at this ⊢; omega_arith) f₃ (fun r hr => by
    have := r2Ranges_le ((k + 7) / 8) r hr; unfold tabBytes; omega_arith)
  have hw₃ : ∀ i < 32, i ≠ sEp → i ≠ sEl → word u₃.mem B (8 * i) = word u.mem B (8 * i) := fun i hi h1 h2 => by
    rw [hb₃ i hi, hm₂, hs₁ i hi h1 h2]
  have hs₃ : InScr B Z u.mem u₃.mem := (i₁.trans (by rw [hm₂]; exact InScr.refl _ _ _)).trans hi₃
  have K₃ : Keep (.rdi :: mmRegs) u u₃ :=
    keep_trans (keep_trans (k₁.mono (by decide)) (k₂.mono (by decide))) (k₃.mono (by decide))
  have heS := src_slice (off := lead (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k))
    (len := k - lead (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k)) hq (by omega_arith)
  rw [← List.append_assoc]
  refine wp_seqs_append (by simp [pow, Crt.loadArr]) (by simp) (WP.mono (powOne_ok M E hm₃ (bp := sY) (bl := sK)
    (ep := sEp) (el := sEl) (by decide) (by decide) (by decide) (by decide)
    (by rw [hw₃ _ (by decide) (by decide) (by decide)]; exact hY)
    (by rw [hw₃ _ (by decide) (by decide) (by decide), bytesAt_length]; exact hK)
    (hy.congrK hs₃ K₃) (by rw [bytesAt_length]; omega_arith) (by rw [bytesAt_length])
    (by rw [hb₃ _ (by decide), hm₂]; exact hEp)
    (by rw [hb₃ _ (by decide), hm₂, bytesAt_length, hEl, hql])
    (heS.congrK hs₃ K₃) (by rw [bytesAt_length]; omega_arith) (by rw [bytesAt_length]; omega_arith))
    fun u₄ ⟨hc₄, h9₄, f₄, k₄⟩ => ?_)
  obtain ⟨hb₄, hi₄⟩ := child_frm hm₃.sub hm₃.wide f₄ (fun r hr => (powRanges_ok _ r hr).2)
  refine WP.mono (leave_ok hc₄.sub) fun t ⟨hdi, hm, k₅⟩ => ⟨?_, hdi, ?_, ?_, ?_⟩
  · rw [(k₅.gpr (by decide) : t.gpr .rax = u₄.gpr .rax), h9₄]
    have e : Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k) +
        BitVec.ofNat 64 (lead (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k)))
        (k - lead (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k))) =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k) := by
      rw [← VG.Proof.Dsa.bytesAt_slice m₀ _ (show lead _ + (k - lead _) ≤ k by omega_arith)]
      generalize Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k = L at hql ⊢
      rw [List.take_of_length_le (by simp; omega_arith), os2ip_drop_lead]
    rw [e]
  · rw [hm]; exact hs₃.trans hi₄
  · intro i hi
    rw [hm, hb₄ i (by omega), hw₃ i (by omega) (by unfold sEp sFn; omega) (by unfold sEl sFn; omega)]
  · exact keep_trans (keep_trans K₃ (k₄.mono (by decide))) (k₅.mono (by decide))


end VG.Proof.Ffdh.X86_64.CheckPublic
