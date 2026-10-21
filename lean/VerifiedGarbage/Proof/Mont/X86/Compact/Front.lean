module

import VerifiedGarbage.Proof.Mont.X86.Compact.Zero
import VerifiedGarbage.Proof.Mont.X86.Compact.Product
public import VerifiedGarbage.Proof.Mont.X86.Compact.Bounds
public import VerifiedGarbage.Proof.Mont.X86.Compact.Metadata
public import VerifiedGarbage.Proof.Mont.X86.Compact.Args

/-! # Prepared multiplication through the complete paired-word product -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem front_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32}
    (hw : Ws s W L) (ha : Args s W L A) (base : (A 0).toNat = W.toNat)
    {N S mo a b : Nat} (V : Metadata s.mem W A N S mo a b) (hL : Lay L N S mo a b)
    (hN : 0 < N) (hN32 : 4 * N < 2 ^ 32)
    (hinv : (val32 s.mem W mo N * w32 s.mem W 56 + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem W b N < val32 s.mem W mo N) :
    WP isa (.seq (.block Compact.scratchPtr) (.seq Compact.zeroAcc Compact.rows)) s fun u =>
      Outside W S (8 * N + 28) s.mem u.mem ∧
      PtrAt u W .ebp (S + Compact.accOff + 4 * N) ∧
      val32 u.mem W (S + Compact.accOff + 4 * N) (N + 1) < 2 * val32 s.mem W mo N ∧
      (∃ U, 2 ^ (32 * N) * val32 u.mem W (S + Compact.accOff + 4 * N) (N + 1) =
        val32 s.mem W a N * val32 s.mem W b N + U * val32 s.mem W mo N) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s u := by
  have nowrap := hw.nowrap
  have scratchFit := hL.scr
  have header := hL.header
  have acc : Compact.accOff = 24 := rfl
  have mult : Rt.multOff = 20 := rfl
  unfold Compact.scratchPtr
  refine WP.seq (WP.mono (arrayPtr_ok hw ha base (r := .edi) (j := 2) (by omega))
    fun p ⟨P, M, K⟩ => ?_)
  have hp := hw.of_keeps K
  have ap := ha.of_keeps K (by decide) (by rw [M]; exact Outs.refl _ _ _)
  have edi : PtrAt p W .edi S := by rw [PtrAt, P]; exact V.scratch
  refine WP.seq (WP.mono (zero_ok (N := N) hp ap base (by rw [M]; exact V.width) (by omega) (by omega) edi)
    fun z ⟨Z, O, Kz⟩ => ?_)
  have O₀ : Outside W S (8 * N + 28) s.mem z.mem := by
    rw [← M]
    exact O.mono (by omega) (by omega)
  have az := ap.of_keeps Kz (by decide)
    (Outs.of_outside (O.mono (by omega) (by omega)) (List.mem_singleton_self _))
  have hz := hp.of_keeps Kz
  have vz := V.keep O₀ (by omega)
  have ediZ : PtrAt z W .edi S := by rw [PtrAt, Kz.1 .edi (by decide)]; exact edi
  have modulus : val32 z.mem W mo N = val32 s.mem W mo N :=
    O₀.val32 hL.smo (by have := hL.mo_le; omega)
  have right : val32 z.mem W b N = val32 s.mem W b N :=
    O₀.val32 hL.sb (by have := hL.b_le; omega)
  have left : val32 z.mem W a N = val32 s.mem W a N :=
    O₀.val32 hL.sa (by have := hL.a_le; omega)
  have inverse : w32 z.mem W 56 = w32 s.mem W 56 := O₀.w32 (by omega) (by decide)
  refine WP.mono (rowsAll_ok hz az base vz hL hN hN32 ediZ modulus
    (by rw [inverse]; exact hinv) (by rw [right]; exact hB) Z) ?_
  rintro u ⟨q, Kq, Mq, I⟩
  have O₁ : Outside W S (8 * N + 28) z.mem u.mem := by
    rw [← Mq]
    intro x hx
    exact I.out x fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega
  refine ⟨O₀.trans O₁, I.ebp, ?_, ?_, ?_⟩
  · simpa only [show 2 * N + 1 - N = N + 1 by omega] using I.lt
  · obtain ⟨U, H⟩ := I.cong
    refine ⟨U, ?_⟩
    rw [show 2 * N + 1 - N = N + 1 by omega, Mq, left, right] at H
    exact H
  · exact ((K.mono (by decide)).trans (Kz.mono (by decide))).trans
      ((Kq.mono (by decide)).trans (I.keeps.mono (by decide)))

end VG.Proof.Mont.X86.Compact
