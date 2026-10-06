import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Next

/-! An invariant for all modulus blocks above the eight cancellation words. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

structure MiddleInv (s₀ : State) (B : Addr) (Z w e i : Nat) (mi : BitVec 64) (s : State) : Prop where
  scr : Scr s B Z
  hdr : Hdr s.mem B w mi
  rdi : s.gpr .rdi = B
  rcx : s.gpr .rcx = off B e
  rbp : s.gpr .rbp = off B (slot w aN + 64 * (i + 1))
  rsi : s.gpr .rsi = off B (e + 64 * (i + 1))
  keep : Keep mmRegs s₀ s
  out : BlockOut B (e - 8) (e + 64) (64 * i) s₀.mem s.mem
  val : wv s.mem B (e + 64) (8 * i) + 2 ^ (512 * i) * (cols s + (word s.mem B (e - 8)).toNat) =
    cols s₀ + (word s₀.mem B (e - 8)).toNat + wv s₀.mem B (e + 64) (8 * i) +
      wv s₀.mem B e 8 * wv s₀.mem B (slot w aN + 64) (8 * i)

theorem middleStep_ok {s₀ s : State} {B : Addr} {Z w e n i : Nat} {mi : BitVec 64}
    (hZ : slot w 8 ≤ Z) (hw : w = 8 * (n + 1)) (hi : i < n)
    (he : hdrBytes + 16 ≤ e) (heZ : e + 8 * (w + 8) ≤ Z)
    (hsep : slot w aN + 8 * w ≤ e - 8) (h : MiddleInv s₀ B Z w e i mi s) :
    WP isa AdxRotate8.middle s fun t =>
      t.zf = some (decide (i + 1 = n)) ∧ MiddleInv s₀ B Z w e (i + 1) mi t := by
  have hn := h.scr.nowrap
  have hNs := slot_le (w := w) (show aN < 8 by decide)
  unfold AdxRotate8.middle
  refine WP.seq (WP.mono (middleBody_ok h.scr h.rcx h.rbp h.rsi (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)) fun a ⟨va, _, oa, ka⟩ => ?_)
  have hha : Hdr a.mem B w mi := h.hdr.of_outside
    (oa.outside (a := e - 8) (b := 64 * (i + 2) + 8) (by omega) (by omega) (by omega) (by omega)) (by omega)
  have haP : a.gpr .rbp = off B (slot w aN + 8 * (8 * (i + 1))) := by
    rw [ka.gpr (by decide), h.rbp]; congr 1; omega
  have haO : a.gpr .rsi = off B (e + 8 * (8 * (i + 1))) := by
    rw [ka.gpr (by decide), h.rsi]; congr 1; omega
  refine WP.mono (nextBlock_ok (h.scr.congr ka.2.2) ((ka.gpr (by decide)).trans h.rdi)
    hha hZ (by omega) haP haO) fun t ⟨hp, ho, hz, hm, kt⟩ => ?_
  have oall : BlockOut B (e - 8) (e + 64) (64 * (i + 1)) s₀.mem a.mem :=
    (h.out.mono (by omega) (by omega)).trans (oa.mono (by omega) (by omega))
  have vT : wv s.mem B (e + 64 * (i + 1)) 8 = wv s₀.mem B (e + 64 * (i + 1)) 8 :=
    h.out.wv (by omega) (by omega) (by omega)
  have vU : wv s.mem B e 8 = wv s₀.mem B e 8 := h.out.wv (by omega) (by omega) (by omega)
  have vN : wv s.mem B (slot w aN + 64 * (i + 1)) 8 = wv s₀.mem B (slot w aN + 64 * (i + 1)) 8 :=
    h.out.wv (by omega) (by omega) (by omega)
  have vp : wv a.mem B (e + 64) (8 * i) = wv s.mem B (e + 64) (8 * i) :=
    oa.wv (by omega) (by omega) (by omega)
  rw [vT, vU, vN] at va
  refine ⟨?_, ⟨h.scr.congr ((ka.trans kt).2.2), hm ▸ hha,
    ((ka.trans kt).gpr (by decide)).trans h.rdi,
    ((ka.trans kt).gpr (by decide)).trans h.rcx, ?_, ?_,
    (h.keep.trans (ka.trans kt)).mono (by decide), ?_, ?_⟩⟩
  · rw [hz]; exact congrArg some (decide_eq_decide.mpr (by omega))
  · rw [hp]; congr 1; omega
  · rw [ho]; congr 1; omega
  · rw [hm]; exact oall
  · rw [hm, cols_keep kt (by decide)]
    rw [show 8 * (i + 1) = 8 * i + 8 by omega, wv_add, wv_add, wv_add, vp,
      show e + 64 + 8 * (8 * i) = e + 64 * (i + 1) by omega,
      show slot w aN + 64 + 8 * (8 * i) = slot w aN + 64 * (i + 1) by omega,
      show 64 * (8 * i) = 512 * i by omega,
      show 512 * (i + 1) = 512 * i + 512 by omega, Nat.pow_add]
    exact extend_blocks h.val va
end VG.Proof.Bignum.X86_64.AdxRotate8
