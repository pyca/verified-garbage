module

public import VerifiedGarbage.Impl.Bignum.AArch64.FastFinish
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FastFinish
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure SelTileInv (s₀ : State) (B : Addr) (Z eA eT eo : Nat) (lt : Bool) (j k : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x5, .x6, .x14, .x16] s₀ t
  x16 : t.gpr .x16 = off B (eA+8*j)
  x6 : t.gpr .x6 = off B (eT+8*j)
  x5 : t.gpr .x5 = off B (eo+8*j)
  c : t.c = !lt
  out : Outside B eo (8*(j+k)) s₀.mem t.mem
  val : wv t.mem B eo (j+k) = if lt then wv s₀.mem B eA (j+k) else wv s₀.mem B eT (j+k)

theorem selWord_ok {s₀ : State} {B : Addr} {Z w eA eT eo j k : Nat} {lt : Bool}
    (hA : eA+8*w ≤ Z) (hT : eT+8*w ≤ Z) (ho : eo+8*w ≤ Z)
    (sA : eo+8*w ≤ eA ∨ eA+8*w ≤ eo) (sT : eo+8*w ≤ eT ∨ eT+8*w ≤ eo)
    (hk : k < 4) (hj : j+k < w) {t : State} (hI : SelTileInv s₀ B Z eA eT eo lt j k t) :
    WP isa (.block (VG.Impl.Bignum.AArch64.FastFinish.selWord k)) t fun t' =>
      SelTileInv s₀ B Z eA eT eo lt j (k+1) t' := by
  have hn := hI.scr.nowrap
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun u =>
    u.mem = t.mem.writeW (off B (eo+8*(j+k)))
      (if t.c then word t.mem B (eT+8*(j+k)) else word t.mem B (eA+8*(j+k))) ∧ u.c = t.c)
    ?_ rfl rfl rfl) fun u ⟨⟨hm, hc⟩, ku⟩ => ?_
  · unfold VG.Impl.Bignum.AArch64.FastFinish.selWord
    have enc : (8*k) % 8 = 0 ∧ 8*k < 32768 := by omega
    have eAEq : eA+8*j+8*k = eA+8*(j+k) := by omega
    have eTEq : eT+8*j+8*k = eT+8*(j+k) := by omega
    have eoEq : eo+8*j+8*k = eo+8*(j+k) := by omega
    brun [hI.x16, hI.x6, hI.x5, enc,
      hI.scr.ld (show eA+8*j+8*k+8 ≤ Z by omega),
      hI.scr.ld (show eT+8*j+8*k+8 ≤ Z by omega),
      hI.scr.st (show eo+8*j+8*k+8 ≤ Z by omega)]
    all_goals simp only [eAEq, eTEq, eoEq]
  have hx : word t.mem B (eA+8*(j+k)) = word s₀.mem B (eA+8*(j+k)) :=
    hI.out.word (by omega) (by omega)
  have hy : word t.mem B (eT+8*(j+k)) = word s₀.mem B (eT+8*(j+k)) :=
    hI.out.word (by omega) (by omega)
  refine ⟨hI.scr.congr ku.wr, (hI.keep.trans ku).mono (by decide),
    (ku.gpr .x16 (by decide)).trans hI.x16, (ku.gpr .x6 (by decide)).trans hI.x6,
    (ku.gpr .x5 (by decide)).trans hI.x5, hc.trans hI.c, ?_, ?_⟩
  · rw [hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [show j+(k+1) = (j+k)+1 by omega, hm, wv_writeW_top _ _ _ _ _ (by omega),
      hI.val, hI.c, hx, hy]
    cases lt <;> simp [wv]

end VG.Proof.Bignum.AArch64.FastFinish
