module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtUnit
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrontPc
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# `vg_rsa_private_crt_precomputed` on x86-64: a prime's `R_X mod X`

The start of a prime's phase with `pre` (`unitPhasePc_ok`): `G` as before,
then the prime's `Y` from word `d` of `pre`, which `po` computes; right if
`pre` holds `R_X mod X` there.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

theorem unitPhasePc_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {N X : Nat} {ok : Prop}
    {sl o wx : Nat} {P : Addr} {W d : Nat} {po : List Instr} (hg : Good s B Z w minv) (hw : 8 ≤ w)
    (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + wsTab wx ≤ Z) (hwx2 : 2 ≤ wx) (hwx : wx ≤ w) (hsl : sl < 32) (hsl1 : sl ≠ Crt.sD)
    (hsl2 : sl ≠ Public.sCnt) (hslv : word s.mem B (8 * sl) = off B o) (hws : WsAt s.mem B o wx mx)
    (hN : NVals s B w minv N ok) (hodd : N % 2 = 1) (hN1 : 1 < N) (hX : XVals s B o wx mx X) (hX1 : 1 < X)
    (hpre : PreSrc s B Z P W) (hdW : d + wx ≤ W)
    (hpo : ∀ t : State, t.gpr .rdi = off B o → t.rd = s.rd → t.wr = s.wr →
      word t.mem (off B o) (8 * sLink) = B → Frm B (gRanges w ++ [xRange o wx]) s.mem t.mem →
      WP isa (.block po) t fun t' => t'.gpr .rax = BitVec.ofNat 64 d ∧ t'.mem = t.mem ∧ Keep [.rax, .rdx] t t') :
    WP isa (seqs (Crt.gPow M.mm sl ++ ([.block [.mov .rdi (.mem (hdr sl))]] : List (Prog isa)) ++
        Crt.loadPre Public.aY po ++ ([.block [leave]] : List (Prog isa)))) s fun t =>
      Good t B Z w minv ∧ WsAt t.mem B o wx mx ∧ XVals t B o wx mx X ∧
      wv t.mem B (slot w Public.aY) w < N ∧
      (ok → wv t.mem B (slot w Public.aY) w % N = 2 ^ (64 * wx * (nChunks w wx + 1)) % N) ∧
      wv t.mem (off B o) (slot wx Public.aY) wx < X ∧
      (wv s.mem P (8 * d) wx = 2 ^ (64 * wx) % X → X ∣ N →
        wv t.mem (off B o) (slot wx Public.aY) wx % X = 2 ^ (64 * wx) % X) ∧
      word t.mem (off B o) (8 * sMaskX) = word s.mem (off B o) (8 * sMaskX) ∧
      Frm B (gRanges w ++ [xRange o wx]) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have hoL : o + slot wx 8 ≤ 2 ^ 64 := by omega
  have hT := tabBytes_le_wsTab wx
  refine unitWith_ok M (step := Crt.loadPre Public.aY po) (by simp [Crt.loadPre]) hg hw hw28 hlo hhi hwx2 hwx
    hsl hsl1 hsl2 hslv hws hN hodd hN1 hX fun s₂ hc₂ hX₂ k₂ f₂ _ => ?_
  have hp₂ := hpre.congrK (InScr.of_frm f₂ fun r hr => (gRanges_le w r hr).trans (by omega)) k₂ (by decide)
  have hg₂ := hc₂.good
  have hY := slot_le (w := wx) (show Public.aY < 8 by decide)
  have hY0 := hdr_lt_slot wx Public.aY (show 31 < 32 by decide)
  -- A byte outside the working space is past the prime's arrays.
  have hfar : ∀ x : Addr, Z ≤ ofs B x → slot wx Public.aY + 8 * (wx + 2) ≤ ofs (off B o) x := fun x hx => by
    rcases ofs_rebase B x (o := o) (by omega) with ⟨_, e⟩ | ⟨h, _⟩
    · rw [e]; omega
    · omega
  refine WP.mono (loadPre_ok hg₂ (Nat.le_refl _) (by omega) (by omega) (by decide) (by decide) hp₂.arg hp₂.val
    (d := d) (fun t hm kt => hpo t ((kt.gpr (by decide)).trans hc₂.rdi) (kt.2.1.trans k₂.2.1) (kt.2.2.trans k₂.2.2)
      (by rw [hm]; exact hc₂.link) (by rw [hm]; exact f₂.mono fun r hr => List.mem_append_left _ hr))
    (fun i hi => by rw [show 8 * d + 8 * i = 8 * (d + i) by omega]; exact hp₂.rd _ (by omega))
    (fun i hi b hb => .inr (hfar _ (by
      have := hp₂.out (d + i) (by omega) b hb; rwa [show 8 * (d + i) = 8 * d + 8 * i by omega] at this))))
    fun t ⟨hv, ho, kt⟩ => ?_
  rw [hpre.wv_eq (InScr.of_frm f₂ fun r hr => (gRanges_le w r hr).trans (by omega)) hdW, hX₂.n] at hv
  have hc := hc₂.of_frm (rs := [(slot wx Public.aY, 8 * (wx + 2))]) (Frm.of_outside ho (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega) kt.2.2 (kt.gpr (by decide))
  refine ⟨hc, hX₂.of_outside ho (by decide) (by decide) (by decide) (Nat.le_refl _) (by have := hg₂.scr.nowrap; omega),
    by rw [hv]; split <;> omega, fun hok _ => ?_, ho.to_x (by decide) hoL (List.mem_singleton_self _),
    ho.word (.inl (by have := hdr_lt_slot wx Public.aY (show sMaskX < 32 by decide); omega))
      (by unfold sMaskX sFn; omega), kt⟩
  have hlt : 2 ^ (64 * wx) % X < X := Nat.mod_lt _ (by omega)
  rw [hv, hok]; simp only [hlt, ↓reduceIte, Nat.mod_mod]

/-- `offP`: `2 w`, `R_p mod p`'s offset in `pre`, from a prime's workspace. -/
theorem offP_ok {t : State} {B : Addr} {o w : Nat} (hdi : t.gpr .rdi = off B o)
    (hl1 : InRegions (t.rd ++ t.wr) (off (off B o) (8 * sLink)) 8) (hlk : word t.mem (off B o) (8 * sLink) = B)
    (hl2 : InRegions (t.rd ++ t.wr) (off B (8 * sW)) 8) (hw : word t.mem B (8 * sW) = BitVec.ofNat 64 w) :
    WP isa (.block Crt.offP) t fun t' =>
      t'.gpr .rax = BitVec.ofNat 64 (2 * w) ∧ t'.mem = t.mem ∧ Keep [.rax, .rdx] t t' :=
  WP.keep [.rax] (Q := fun t' => t'.gpr .rax = BitVec.ofNat 64 (2 * w) ∧ t'.mem = t.mem)
    (by xrun [Crt.offP, State.ea, hdr, ws, hdi, hdrOff, hl1, hlk, hl2, hw, Nat.two_mul, BitVec.ofNat_add]) rfl |>.mono
      fun _ ⟨⟨a, b⟩, c⟩ => ⟨a, b, c.mono (by decide)⟩

/-- `offQ`: `2 w + w_p`, `R_q mod q`'s offset in `pre`, from a prime's
workspace. -/
theorem offQ_ok {t : State} {B : Addr} {o op w wp : Nat} (hdi : t.gpr .rdi = off B o)
    (hl1 : InRegions (t.rd ++ t.wr) (off (off B o) (8 * sLink)) 8) (hlk : word t.mem (off B o) (8 * sLink) = B)
    (hl2 : InRegions (t.rd ++ t.wr) (off B (8 * sW)) 8) (hw : word t.mem B (8 * sW) = BitVec.ofNat 64 w)
    (hl3 : InRegions (t.rd ++ t.wr) (off B (8 * sWsP)) 8) (hp : word t.mem B (8 * sWsP) = off B op)
    (hl4 : InRegions (t.rd ++ t.wr) (off (off B op) (8 * sW)) 8)
    (hwp : word t.mem (off B op) (8 * sW) = BitVec.ofNat 64 wp) :
    WP isa (.block Crt.offQ) t fun t' =>
      t'.gpr .rax = BitVec.ofNat 64 (2 * w + wp) ∧ t'.mem = t.mem ∧ Keep [.rax, .rdx] t t' :=
  WP.keep [.rax, .rdx] (Q := fun t' => t'.gpr .rax = BitVec.ofNat 64 (2 * w + wp) ∧ t'.mem = t.mem)
    (by xrun [Crt.offQ, Crt.offP, List.cons_append, List.nil_append, State.ea, hdr, ws, hdi, hdrOff, hl1, hlk, hl2, hw, hl3, hp, hl4, hwp, Nat.two_mul,
      BitVec.ofNat_add]) rfl |>.mono fun _ ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩

end VG.Proof.Bignum.X86_64
