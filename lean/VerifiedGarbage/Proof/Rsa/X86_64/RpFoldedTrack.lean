module

public import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedMasks
public import VerifiedGarbage.Proof.Rsa.RecoverFolded
public import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame

/-! # The captured root and its flags in the recovery workspace -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Impl.Rsa.X86_64.Keys.Recover VG.Impl.Rsa.X86_64.Keys.Recover.Folded
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

abbrev Track := VG.Proof.Rsa.RecoveryFolded.Track

def advance (enable : Bool) (N y : Nat) (v : Track) : Track :=
  if enable then VG.Proof.Rsa.RecoveryFolded.square N y v else v

theorem advance_root (enable : Bool) (N y : Nat) (v : Track) :
    (advance enable N y v).root =
      if !v.stopped && enable && decide (y * y % N = 1) then y else v.root := by
  cases enable <;> cases v with | mk root stopped found =>
    cases stopped <;> cases found <;> cases h1 : decide (y * y % N = 1) <;>
      simp [advance, VG.Proof.Rsa.RecoveryFolded.square, h1]

theorem advance_active (enable : Bool) (N y : Nat) (v : Track) :
    (!(advance enable N y v).stopped) =
      (!v.stopped && !(enable && (decide (y * y % N = 1) || decide (y * y % N = N - 1)))) := by
  cases enable <;> cases v with | mk root stopped found =>
    cases stopped <;> cases found <;> cases h1 : decide (y * y % N = 1) <;>
      cases hm : decide (y * y % N = N - 1) <;>
      simp [advance, VG.Proof.Rsa.RecoveryFolded.square, h1, hm]

theorem advance_found (enable : Bool) (N y : Nat) (v : Track) :
    (advance enable N y v).found =
      (v.found || (!v.stopped && enable && decide (y * y % N = 1))) := by
  cases enable <;> cases v with | mk root stopped found =>
    cases stopped <;> cases found <;> cases h1 : decide (y * y % N = 1) <;>
      simp [advance, VG.Proof.Rsa.RecoveryFolded.square, h1]

structure TrackRep (m : Mem) (B : Addr) (w N : Nat) (v : Track) : Prop where
  root : wv m B (slot w aRoot) w = v.root * 2 ^ (64 * w) % N
  rootlt : v.root < N
  active : word m B (flagsAt w) = mask (!v.stopped)
  found : word m B (flagsAt w + 8) = mask v.found

theorem TrackRep.congr {m m' : Mem} {B : Addr} {w N : Nat} {v : Track} (h : TrackRep m B w N v)
    {js hs : List Nat} (hf : Frm B (rg w js hs) m m') (hZ : slot w 16 ≤ 2 ^ 64)
    (hh : ∀ i ∈ hs, i < 32) (hr : aRoot ∉ js) : TrackRep m' B w N v := by
  have ev := hf.rg_wv hZ hh (by decide) hr (n := w) (by omega)
  have ea := hf.rg_wordA hZ hh (by decide) hr (i := w) (by omega)
  have ef := hf.rg_wordA hZ hh (by decide) hr (i := w + 1) (by omega)
  have en : flagsAt w + 8 = slot w aRoot + 8 * (w + 1) := by unfold flagsAt; omega
  refine ⟨by rw [ev]; exact h.root, h.rootlt, ?_, ?_⟩
  · rw [flagsAt, ea]; exact h.active
  · rw [en, ef, ← en]; exact h.found

theorem flags_write {m : Mem} {B : Addr} {w : Nat} (hZ : slot w 16 ≤ 2 ^ 64) (a f : BitVec 64) :
    let m' := (m.writeW (off B (flagsAt w + 8)) f).writeW (off B (flagsAt w)) a
    Frm B (rg w [aRoot] []) m m' ∧
      wv m' B (slot w aRoot) w = wv m B (slot w aRoot) w ∧
      word m' B (flagsAt w) = a ∧ word m' B (flagsAt w + 8) = f := by
  have he : flagsAt w + 16 = slot w 16 := by unfold flagsAt slot aRoot; omega
  have haZ : flagsAt w + 8 ≤ 2 ^ 64 := by omega
  have hfZ : flagsAt w + 8 + 8 ≤ 2 ^ 64 := by omega
  have hrZ : slot w aRoot + 8 * w ≤ 2 ^ 64 := by unfold flagsAt at he; omega
  dsimp only
  refine ⟨?_, ?_, word_writeW_self _ _ _ _, ?_⟩
  · intro x hx
    have hh := hx _ (rg_mem_arr (w := w) (j := aRoot) [] (by simp))
    dsimp only at hh
    rw [(writeW_outside _ B a haZ) x (by unfold flagsAt; omega),
      (writeW_outside _ B f hfZ) x (by unfold flagsAt; omega)]
  · rw [(writeW_outside _ B a haZ).wv (Or.inl (by unfold flagsAt; omega)) hrZ,
      (writeW_outside _ B f hfZ).wv (Or.inl (by unfold flagsAt; omega)) hrZ]
  · rw [(writeW_outside _ B a haZ).word (Or.inr (Nat.le_refl _)) hfZ, word_writeW_self]

end VG.Proof.Rsa.X86_64.RecoveryFolded
