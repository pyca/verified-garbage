import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8CtMiddle
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Tail

/-! Each tile accesses memory and branches using public pointers and sizes. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

theorem tail_fw (L : TileLayout) (s : State) (h : TileReady L (L.n + 1) s) :
    WP isa AdxRotate8.tailCore s (TileGood L) := by
  obtain ⟨mi, hm⟩ := h.good.hdr
  have he := L.he; have heZ := L.heZ; have hw := L.hw
  refine WP.mono (tailCore_ok h.good.scr h.good.rcx h.rsi (by omega) (by omega) (by omega))
    fun t ⟨_, _, ot, kt⟩ => ?_
  exact ⟨h.good.scr.congr kt.2.2, (kt.gpr (by decide)).trans h.good.rdi,
    (kt.gpr (by decide)).trans h.good.rcx, mi, hm.of_outside ot (by omega)⟩

theorem tile_ct : RelCT isa (Two TileGood) AdxRotate8.tile (fun _ _ => True) := by
  unfold AdxRotate8.tile AdxRotate8.tileCompute
  refine RelCT.seq (RelCT.seq front_ct (RelCT.seq middles_ct ?_))
    (two_taint [.rdi, .rcx] tile_pins (by taint_decide))
  exact two_piece [.rdi, .rcx, .rbp, .rsi]
    (fun L s t hs ht => ready_pins (L.n + 1) L s t hs ht) (by taint_decide) tail_fw
end VG.Proof.Bignum.X86_64.AdxRotate8
