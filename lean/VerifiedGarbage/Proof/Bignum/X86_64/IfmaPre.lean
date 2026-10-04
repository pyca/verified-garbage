import VerifiedGarbage.Proof.Bignum.X86_64.CrtUnit
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow

/-!
# RSA with AVX512_IFMA on x86-64: the bases in the primes' workspaces

`pre` computes `G` once in `n`'s workspace and, for each prime `X`, enters
its workspace and reduces (`enterRedc_ok`): `R_X` into `aY` (from `G`)
and `x R_X` into `aXc` (from `x G`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- Into a prime's workspace (`rdi := [sl]`), and `aXc := [aY] R^-K mod X`. -/
theorem enterRedc_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {X : Nat}
    {sl o wx : Nat} (hg : Good s B Z w minv) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (hwx2 : 2 ≤ wx) (hwx : wx ≤ w) (hsl : sl < 32)
    (hslv : word s.mem B (8 * sl) = off B o) (hws : WsAt s.mem B o wx mx) (hX : XVals s B o wx mx X)
    (hX1 : 1 < X) :
    WP isa (seqs (([.block [.mov .rdi (.mem (hdr sl))]] : List (Prog isa)) ++ redc M.mm Public.aY)) s fun t =>
      SubCtx t B Z o w wx mx ∧ XVals t B o wx mx X ∧ wv t.mem (off B o) (slot wx aXc) wx < X ∧
      wv t.mem (off B o) (slot wx aXc) wx * 2 ^ (64 * wx * nChunks w wx) % X =
        wv s.mem B (slot w Public.aY) w % X ∧
      Frm B [xRange o wx] s.mem t.mem ∧ Keep (mmRegs ++ [.rdi]) s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have ho64 : o < 2 ^ 64 := by omega
  have hoL : o + slot wx 8 ≤ 2 ^ 64 := by omega
  refine wp_seqs_append (by simp) (by simp [redc]) ?_
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off B o ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sl) (by omega), hslv]) rfl)
    fun s₂ ⟨⟨hdi₂, hm₂⟩, k₂⟩ => ?_
  have hc₂ : SubCtx s₂ B Z o w wx mx :=
    SubCtx.mk' (hs.congr k₂.2.2) (by rw [hm₂]; exact hg.hdr) (by rw [hm₂]; exact hws) hdi₂ hlo hhi
  have hX₂ : XVals s₂ B o wx mx X := by
    rw [show s₂ = { s₂ with mem := s.mem } by rw [← hm₂]] ; exact ⟨hX.n, hX.inv, hX.one⟩
  refine WP.mono (redc_ok M hc₂ hX₂ hwx2 hwx (by omega) hX1 (j := Public.aY) (by decide))
    fun s₃ ⟨hc₃, hX₃, hlt₃, hv₃, f₃, k₃⟩ => ⟨hc₃, hX₃, hlt₃, by rw [← hm₂]; exact hv₃, ?_, ?_⟩
  · rw [← hm₂]; exact f₃.to_x (redcRanges_ok wx) hoL (List.mem_singleton_self _)
  · exact (k₂.trans k₃).mono (by simp [mmRegs])


/-- Back to `n`'s workspace, whose header the prime's phase kept. -/
theorem leaveBack_ok {s₀ t : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {o wx : Nat}
    (hg : Good s₀ B Z w minv) (hc : SubCtx t B Z o w wx mx) (hf : Frm B [xRange o wx] s₀.mem t.mem)
    (hlo : slot w 8 ≤ o) :
    WP isa (.block [leave]) t fun t' => Good t' B Z w minv ∧ t'.mem = t.mem ∧ Keep [.rdi] t t' := by
  have hn := hc.scr.nowrap
  have hhi := hc.hi
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have ho64 : o < 2 ^ 64 := by omega
  have hl : InRegions (t.rd ++ t.wr) (off (off B o) (8 * sLink)) 8 :=
    hc.good.scr.ld (by unfold sLink sFn; omega)
  refine WP.mono (WP.keep [.rdi] (Q := fun t' => t'.gpr .rdi = B ∧ t'.mem = t.mem)
    (by xrun [leave, State.ea, hdr, hc.rdi, hdrOff, hl, hc.link]) rfl) fun t' ⟨⟨hdi, hm⟩, k⟩ => ?_
  have hb : ∀ d, d + 8 ≤ o → word t'.mem B d = word s₀.mem B d := fun d hd => by
    rw [hm]; exact hf.x_below hd ho64
  have hH := hg.hdr
  exact ⟨⟨hc.scr.congr k.2.2, hdi, (hb _ (by unfold sW; omega)).trans hH.hw,
    (hb _ (by unfold sMinv; omega)).trans hH.hminv,
    fun j hj => (hb _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega); omega)).trans
      (hH.harr j hj)⟩, hm, k⟩

end VG.Proof.Bignum.X86_64
