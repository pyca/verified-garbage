import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8CtTile
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Tile

/-! The outer iteration count and each tile's workspace are public. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

structure W8 where
  ws : Ws
  n : Nat
  hw : ws.w = 8 * n
  hn : 0 < n

def RW (L : W8) (i : Nat) (s : State) : Prop :=
  GoodW L.ws s ∧ s.gpr .rcx = off L.ws.B (slot L.ws.w aAcc + 16 + 64 * i)

def tileLayout (L : W8) (i : Nat) (hi : i < L.n) (hZ : slot L.ws.w 8 ≤ L.ws.Z) : TileLayout :=
  { B := L.ws.B, Z := L.ws.Z, w := L.ws.w, e := slot L.ws.w aAcc + 16 + 64 * i, n := L.n - 1
    hZ := hZ
    hw := by have := L.hw; have := L.hn; omega
    he := by unfold slot; omega
    heZ := by have := L.hw; unfold slot aAcc at *; omega
    sep := by unfold slot aN aAcc; omega }

theorem outer_body_ct : RelCT isa
    (Two fun p : W8 × Nat => fun s => p.2 < p.1.n ∧ RW p.1 p.2 s)
    AdxRotate8.tile (fun _ _ => True) := by
  apply tile_ct.mono ?_ (fun _ _ h => h)
  rintro s t ⟨⟨L, i⟩, ⟨hi, ⟨⟨mi, hs, hZ⟩, hc⟩⟩, ⟨_, ⟨⟨mj, ht, _⟩, hd⟩⟩⟩
  exact ⟨tileLayout L i hi hZ, ⟨hs.scr, hs.rdi, hc, mi, hs.hdr⟩,
    ⟨ht.scr, ht.rdi, hd, mj, ht.hdr⟩⟩

theorem outer_fw (L : W8) (i : Nat) (s : State) (hi : i < L.n) (h : RW L i s) :
    WP isa AdxRotate8.tile s fun t => isa.eval .ne t = some (decide (i + 1 < L.n)) ∧
      (i + 1 < L.n → RW L (i + 1) t) ∧ (i + 1 = L.n → RW L L.n t) := by
  obtain ⟨⟨mi, hg, hZ⟩, hc⟩ := h
  let T := tileLayout L i hi hZ
  have hw := L.hw
  refine WP.mono (tile_ok (L := L.ws.w + 8) hg.scr hg.rdi hg.hdr hZ T.hw hc
    T.he T.heZ (by omega) T.sep) fun t ⟨_, ct, zt, ot, kt⟩ => ?_
  have hr : RW L (i + 1) t := ⟨⟨mi, ⟨hg.scr.congr kt.2.2,
    (kt.gpr (by decide)).trans hg.rdi, hg.hdr.of_outside ot (by
      have := T.he; change hdrBytes + 16 ≤ slot L.ws.w aAcc + 16 + 64 * i at this; omega)⟩, hZ⟩,
    by rw [ct]; exact congrArg (off L.ws.B) (by omega)⟩
  refine ⟨?_, fun _ => hr, fun he => he ▸ hr⟩
  simp only [eval, zt, Option.map_some]
  have he : (slot L.ws.w aAcc + 16 + 64 * i + 64 = slot L.ws.w aTmp) ↔ i + 1 = L.n := by
    unfold slot aAcc aTmp; omega
  simp only [he]
  by_cases heq : i + 1 = L.n
  · simp [heq]
  · simp [heq]; omega

theorem outer_ct : RelCT isa (Two fun L s => RW L 0 s)
    (.loop AdxRotate8.tile .ne) (Two fun L s => RW L L.n s) := by
  refine (two_loop (fun L : W8 => L.n) (Φ := RW) outer_body_ct outer_fw).mono ?_ (fun _ _ h => h)
  rintro s t ⟨L, hs, ht⟩
  exact ⟨L, ⟨L.hn, hs⟩, L.hn, ht⟩
end VG.Proof.Bignum.X86_64.AdxRotate8
