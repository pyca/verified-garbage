module

public import VerifiedGarbage.Impl.Bignum.AArch64.WideLoops
public import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WideLoops
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def zeroPrefix (n : Nat) : List Instr := (List.range n).map fun i => st .x7 .x16 (8 * i)

/-- Clear a short block without moving its base pointer. -/
theorem zeroPrefix_ok {s : State} {B : Addr} {Z e n : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e) (h7 : s.gpr .x7 = 0)
    (he : e + 8 * n ≤ Z) (hn : n ≤ 8) :
    WP isa (.block (zeroPrefix n)) s fun t =>
      wv t.mem B e n = 0 ∧ Outside B e (8 * n) s.mem t.mem ∧ Keep [] s t := by
  induction n with
  | zero => exact WP.block_nil ⟨rfl, Outside.refl _ _ _ _, Keep.refl _ _⟩
  | succ n ih =>
    rewrite [zeroPrefix, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    apply WP.block_append
    refine WP.mono (ih (by omega) (by omega)) fun t ⟨hv, ho, kt⟩ => ?_
    have hptr := (kt.gpr .x16 (by decide)).trans h16
    have hz := (kt.gpr .x7 (by decide)).trans h7
    have enc : (8 * n) % 8 = 0 ∧ 8 * n < 32768 := ⟨by omega, by omega⟩
    have hwrap := hs.nowrap
    refine WP.mono (WP.keep [] (Q := fun u =>
      u.mem = t.mem.writeW (off B (e + 8 * n)) (0 : BitVec 64))
      (by brun [hptr, hz, enc, (hs.congr kt.wr).st (show e + 8 * n + 8 ≤ Z by omega)])
      rfl rfl rfl) fun u ⟨hum, ku⟩ => ?_
    refine ⟨?_, ?_, (kt.trans ku).mono (by decide)⟩
    · rw [hum, wv_writeW_top _ _ _ _ _ (by omega), hv]
      rfl
    · have hx := writeW_outside t.mem B (0 : BitVec 64) (d := e + 8 * n) (by omega)
      have hu : Outside B (e + 8 * n) 8 t.mem u.mem := by
        intro x h
        exact (congrArg (fun m : Mem => m x) hum).trans (hx x h)
      exact (ho.mono (by omega) (by omega)).trans (hu.mono (by omega) (by omega))

theorem advance_ok {s : State} {B : Addr} {e : Nat} (h16 : s.gpr .x16 = off B e) :
    WP isa (.block [.addImm .x .x16 .x16 64]) s fun t =>
      (t.gpr .x16 = off B (e + 64) ∧ t.mem = s.mem) ∧ Keep [.x16] s t := by
  refine WP.keep [.x16] ?_ rfl rfl rfl
  brun [h16]

/-- Clear eight limbs and advance by their actual byte length. -/
theorem zeroTile_ok {s : State} {B : Addr} {Z e : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e) (h7 : s.gpr .x7 = 0)
    (he : e + 64 ≤ Z) :
    WP isa (.block (zeroPrefix 8 ++ ([.addImm .x .x16 .x16 64] : List Instr))) s fun t =>
      wv t.mem B e 8 = 0 ∧ t.gpr .x16 = off B (e + 64) ∧
        Outside B e 64 s.mem t.mem ∧ Keep [.x16] s t := by
  apply WP.block_append
  refine WP.mono (zeroPrefix_ok hs h16 h7 he (Nat.le_refl 8)) fun u ⟨hv, ho, ku⟩ => ?_
  refine WP.mono (advance_ok ((ku.gpr .x16 (by decide)).trans h16)) fun t ⟨⟨ht16, htm⟩, kt⟩ => ?_
  refine ⟨?_, ht16, ?_, (ku.trans kt).mono (by decide)⟩
  · exact (congrArg (fun m : Mem => wv m B e 8) htm).trans hv
  · intro x hx
    exact (congrArg (fun m : Mem => m x) htm).trans (ho x hx)

theorem zeroBlockStep_ok {s t : State} {B : Addr} {Z e j n : Nat}
    (h7 : s.gpr .x7 = 0) (he : e + 64 * n ≤ Z) (hj : j < n)
    (hI : ZeroInv s B Z e (8 * j) t) :
    WP isa (.block ((zeroPrefix 8 ++ ([.addImm .x .x16 .x16 64] : List Instr)) ++
      ([.subImm .x .x14 .x14 1] : List Instr))) t fun u =>
      ZeroInv s B Z e (8 * (j + 1)) u ∧
        u.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  apply WP.block_append
  refine WP.mono (zeroTile_ok hI.scr hI.x16
    ((hI.keep.gpr .x7 (by decide)).trans h7) (by omega))
    fun a ⟨hav, ha16, hao, ka⟩ => ?_
  refine WP.mono (dec_ok a .x14) fun u ⟨⟨hu14, hum, _⟩, ku⟩ => ?_
  refine ⟨⟨hI.scr.congr (ku.wr.trans ka.wr),
    ((hI.keep.trans ka).trans ku).mono (by decide), ?_, ?_, ?_⟩,
    hu14.trans (congrArg (· - BitVec.ofNat 64 1) (ka.gpr .x14 (by decide)))⟩
  · exact ((ku.gpr .x16 (by decide)).trans ha16).trans (congrArg (off B) (by omega))
  · have ho : Outside B (e + 8 * (8 * j)) 64 t.mem u.mem := by
      intro x hx
      exact (congrArg (fun m : Mem => m x) hum).trans (hao x hx)
    exact (hI.out.mono (by omega) (by omega)).trans (ho.mono (by omega) (by omega))
  · have hp := hao.wv (d := e) (k := 8 * j) (by omega) (by omega)
    rw [hum, show 8 * (j + 1) = 8 * j + 8 by omega, wv_add, hp, hI.val, hav]
    rfl

/-- Clear any positive public number of eight-word blocks. -/
theorem zeroBlocks_ok {s : State} {B : Addr} {Z e n : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e) (h7 : s.gpr .x7 = 0)
    (h14 : s.gpr .x14 = BitVec.ofNat 64 n)
    (he : e + 64 * n ≤ Z) (hn : 0 < n) (hn' : n < 2 ^ 64) :
    WP isa (countLoop .x14 (zeroPrefix 8 ++ ([.addImm .x .x16 .x16 64] : List Instr))) s
      (ZeroInv s B Z e (8 * n)) := by
  have h0 : ZeroInv s B Z e (8 * 0) s :=
    ⟨hs, Keep.refl _ _, h16, Outside.refl _ _ _ _, rfl⟩
  unfold countLoop
  exact wp_countdown hn' hn (fun j => ZeroInv s B Z e (8 * j))
    (fun j hj t hI _ => zeroBlockStep_ok h7 he hj hI) h0 h14

/-- The measured eight-store clear, including its two padding limbs. -/
theorem zero_ok {s : State} {B : Addr} {Z e k : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B e) (h7 : s.gpr .x7 = 0)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 (8 * k))
    (he : e + 8 * (16 * k + 2) ≤ Z) (hk : 0 < k) (hk' : k < 2 ^ 56) :
    WP isa VG.Impl.Bignum.AArch64.WideLoops.zero s fun t =>
      wv t.mem B e (16 * k + 2) = 0 ∧ Outside B e (8 * (16 * k + 2)) s.mem t.mem ∧
        Keep [.x14, .x16] s t := by
  have hn := hs.nowrap
  unfold VG.Impl.Bignum.AArch64.WideLoops.zero
  refine WP.seq (WP.mono (WP.keep [.x14, .x16]
    (Q := fun u => u.gpr .x16 = off B e ∧ u.gpr .x14 = BitVec.ofNat 64 (2 * k) ∧ u.mem = s.mem)
    (by
      brun [h8, h12, ofNat_add_ofNat, Square.shr3_ofNat (show 8 * k + 8 * k < 2 ^ 64 by omega)]
      congr 1
      omega) rfl rfl rfl) fun u ⟨⟨hu16, hu14, hum⟩, ku⟩ => ?_)
  refine WP.seq (WP.mono (zeroBlocks_ok (hs.congr ku.wr) hu16
    ((ku.gpr .x7 (by decide)).trans h7) hu14 (by omega) (by omega) (by omega))
    fun a hI => ?_)
  change WP isa (.block (zeroPrefix 2)) a _
  refine WP.mono (zeroPrefix_ok hI.scr hI.x16
    ((hI.keep.gpr .x7 (by decide)).trans ((ku.gpr .x7 (by decide)).trans h7))
    (by omega) (by decide)) fun t ⟨htv, hto, kt⟩ => ?_
  refine ⟨?_, ?_, ((ku.trans hI.keep).trans kt).mono (by decide)⟩
  · have hp := hto.wv (d := e) (k := 16 * k) (by omega) (by omega)
    rw [wv_add, hp, show 16 * k = 8 * (2 * k) by omega, hI.val, htv]
    rfl
  · have ho : Outside B e (8 * (8 * (2 * k))) s.mem a.mem := by
      intro x hx
      exact (hI.out x hx).trans (congrArg (fun m : Mem => m x) hum)
    exact (ho.mono (by omega) (by omega)).trans (hto.mono (by omega) (by omega))

end VG.Proof.Bignum.AArch64.WideLoops
