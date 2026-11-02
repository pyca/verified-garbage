module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Fn
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Fn
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Minv32

/-!
# The Miller–Rabin round on PPC64LE: constant time

As `Proof/Bignum/PPC64LE/PubCT.lean`: two runs are related by `Two` at each
step. The taint analysis checks the saving of the registers and `setup` from
the working space's address and the scratch buffer's, and, after `setup`,
everything else from the registers it fixes, which depend only on the public
data (`FD`): array 0's base, `2 w`, the arrays' size, the working space and
the scratch buffer. Nothing branches on memory: the loops count `w`, the
16 windows of a word and the 16 entries of the table.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE
open VG.Proof.Bignum (slot)
open VG.Proof.Rsa.Mont (wOf)
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint)

/-- The public data of a run. -/
structure FD where
  B : Addr
  n : BitVec 64
  S : Addr
  w : Nat

def fdOf (s : State) : FD := ⟨s.gpr .r3, s.gpr .r4, s.gpr .r5, wOf s.mem (s.gpr .r3)⟩

def C0 (d : FD) (s : State) : Prop := fnContract.pre s ∧ fdOf s = d

/-- After `setup`. -/
def C1 (d : FD) (s : State) : Prop :=
  s.gpr .r10 = off d.B (slot d.w 0) ∧ s.gpr .r11 = BitVec.ofNat 64 (2 * d.w) ∧
    s.gpr .r29 = BitVec.ofNat 64 (8 * (d.w + 2)) ∧ s.gpr .r31 = d.B ∧ s.gpr .r21 = d.S

theorem pins_C0 : Pins C0 [.r3, .r5] := by
  rintro d s₁ s₂ ⟨-, h₁⟩ ⟨-, h₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (congrArg FD.B h₁).trans (congrArg FD.B h₂).symm
  · exact (congrArg FD.S h₁).trans (congrArg FD.S h₂).symm

theorem pins_C1 : Pins C1 [.r10, .r11, .r21, .r29, .r31] := by
  rintro d s₁ s₂ ⟨a10, a11, a29, a31, a21⟩ ⟨b10, b11, b29, b31, b21⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a21, b21]
  · rw [a29, b29]
  · rw [a31, b31]

theorem front_C1 {d : FD} {s : State} (h : C0 d s) : WP isa (.block (Impl.MillerRabin.PPC64LE.save ++ setup)) s (C1 d) := by
  obtain ⟨⟨-, hwr, hdis, hnw, hL, hp⟩, rfl⟩ := h
  have hsin : Save.savR (s.gpr .r5) ∈ s.wr := by rw [hwr]; simp
  dsimp only [Proof.MillerRabin.Round.Layout, Proof.MillerRabin.Round.compact] at hL
  obtain ⟨-, ⟨-, -, -, -⟩, h4, h128, hspace, -⟩ := hL
  dsimp only [Proof.MillerRabin.Round.Prepared, Proof.MillerRabin.Round.compact] at hp
  obtain ⟨-, -, hinv, -⟩ := hp
  simp only [wsR] at hdis
  simp only [fdOf]
  generalize hBd : s.gpr .r3 = B at hdis hnw hspace h4 h128 hinv
  generalize hZd : (s.gpr .r4).toNat * 8 = Z at hdis hnw
  generalize hwd : wOf s.mem B = w at hspace h4 h128 hinv
  have hZ : slot w 28 ≤ Z := by
    rw [← hZd]; change slot w 28 ≤ 8 * (s.gpr .r4).toNat at hspace; omega
  have hs : Scr s B Z := Scr.of_mem (by rw [hwr, ← hBd, ← hZd]; simp) hnw
  have h0 := slot_lt (w := w) (show 0 < 28 by decide)
  have h0' : slot w 0 = 256 := by simp [slot, Impl.Bignum.hdrBytes]
  rw [WP.block_append_iff]
  refine WP.mono (Save.save_ok s hsin) fun s₁ hS => ?_
  have hout₁ := frame_outside (B := B) (Z := Z) hS.frame hdis
  have wd₁ : ∀ {d}, d + 8 ≤ Z → s₁.mem.readW (off B d) 64 = s.mem.readW (off B d) 64 :=
    fun hd => hout₁.word (by omega) (by omega)
  refine WP.mono (setup_ok (hs.congr hS.keep.wr) (by rw [hS.keep.gpr .r3 (by decide), hBd])
    (by rw [wd₁ (by omega), ← hwd]; simp [wOf, VG.Proof.Rsa.Mont.wordAt, Proof.Rsa.Mont.wWord])
    h4 h128 hZ (by
      rw [w32_eq_mod, w32_eq_mod]
      simp only [VG.Proof.Bignum.word]
      rw [wd₁ (by omega), wd₁ (by omega)]
      exact VG.Proof.Bignum.Minv32.minv_low hinv)) fun s₂ ⟨⟨hm2, _⟩, k2⟩ => ?_
  exact ⟨hm2.h10, hm2.h11, hm2.h29, hm2.h31, (k2.gpr .r21 (by decide)).trans hS.r21⟩

theorem fn_rel : RelCT isa (Two C0) Impl.MillerRabin.PPC64LE.round fun _ _ => True := by
  unfold Impl.MillerRabin.PPC64LE.round
  exact RelCT.seq (two_post (two_taint _ pins_C0 (by taint_decide)) fun _ _ h => front_C1 h)
    (two_taint _ pins_C1 (by taint_decide))

theorem fn_ct : ConstantTime isa fnContract.pre fnContract.pub Impl.MillerRabin.PPC64LE.round :=
  RelCT.constantTime (fn_rel.mono (fun s t ⟨hs, ht, hsp, h3, h4, h5, hw⟩ =>
    ⟨fdOf s, ⟨hs, rfl⟩, ⟨ht, by simp only [fdOf]; rw [h3, h4, h5, ← h3, hw, h3]⟩, hsp⟩) fun _ _ h => h)

end VG.Proof.MillerRabin.PPC64LE
