import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Frame

/-! A tile in the existing Montgomery working space, for every valid array pair. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

theorem tileAt_ok {s : State} {B : Addr} {Z w i j : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hi : i+8 ≤ w) (hj : j+8 ≤ w)
    {a b : Nat} (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hidx : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i)
    (hjdx : word s.mem B (8*sFn 13) = BitVec.ofNat 64 j) :
    let e := slot w aAcc+16+8*(i+j)
    WP isa (AdxRect8.tileAt a b) s fun t =>
      wv t.mem B e 16 + 2^1024 * (word t.mem B carryOffset).toNat =
        wv s.mem B e 16 + wv s.mem B (slot w a+8*i) 8 * wv s.mem B (slot w b+8*j) 8 +
          2^512 * (word s.mem B carryOffset).toNat ∧
      (word t.mem B carryOffset).toNat ≤ 2 ∧
      ((word s.mem B carryOffset).toNat ≤ 1 → (word t.mem B carryOffset).toNat ≤ 1) ∧
      Hdr t.mem B w mi ∧ Frm B [(e,128),(carryOffset,8)] s.mem t.mem ∧ Keep mmRegs s t := by
  dsimp only
  unfold AdxRect8.tileAt
  have ar := tile_ranges hi hj ha ha1 ha2
  have br := tile_ranges hj hi hb hb1 hb2
  have cb : carryOffset+8 ≤ slot w aAcc+16+8*(i+j) := by
    unfold carryOffset sFn slot hdrBytes aAcc; omega
  refine WP.seq (WP.mono (setup_ok hs hd hh hZ ha hb hidx hjdx)
    fun u ⟨ua,ub,uo,um,ku⟩ => ?_)
  refine WP.mono (tile_ok (hs.congr ku.2.2) ((ku.gpr (by decide)).trans hd) ua ub uo
    (by omega) (by omega) (by omega) ar.2.2 (by omega) cb)
    fun t ⟨eq,bd,one,fr,kt⟩ => ?_
  rw [um] at eq one fr
  have fr' : Frm B [(slot w aAcc+16+8*(i+j),128),(carryOffset,8),(8*sFn 13,8)] s.mem t.mem :=
    fr.mono (by simp)
  exact ⟨eq,bd,one,frame_hdr hh (by unfold slot; omega) fr',fr,
    (ku.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.X86_64.AdxRect8
