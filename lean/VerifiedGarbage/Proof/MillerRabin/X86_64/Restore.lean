module

public import VerifiedGarbage.Impl.MillerRabin.X86_64.Round
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # Restore one saved bookkeeping word -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.MillerRabin.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.MlKem.X86_64

theorem restorePair_ok {s : State} {B S : Addr} {Z j d : Nat} {v : BitVec 64}
    (h : Scr s B Z) (hZ : 256 ≤ Z) (hB : s.gpr .rdi = B) (hS : s.gpr .rsp = S)
    (hj : j < 32) (hL : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 d) 8)
    (hv : s.mem.readW (S + BitVec.ofNat 64 d) 64 = v) :
    WP isa (.block (restorePair j d)) s fun t =>
      t.mem = s.mem.writeW (off B (8 * j)) v ∧ Keep [.r11] s t := by
  have hW : InRegions s.wr (off B (8 * j)) 8 := h.st (by omega_arith)
  exact WP.keep [.r11] (by
    xrun [restorePair, State.ea, hB, hS, hdr, hdrOff, BitVec.ofInt_natCast, hL, hv, hW]) rfl

/-- Restore a list of slots; header stores keep every saved stack word. -/
theorem restorePairs_ok {s : State} {B S : Addr} {Z : Nat}
    (h : Scr s B Z) (hZ : 256 ≤ Z) : ∀ (ps : List (Nat × Nat)) (t : State),
    (∀ p ∈ ps, p.1 < 32 ∧ InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 p.2) 8 ∧
      ∀ m', Outside B 0 256 s.mem m' →
        m'.readW (S + BitVec.ofNat 64 p.2) 64 = s.mem.readW (S + BitVec.ofNat 64 p.2) 64) →
    t.gpr .rdi = B → t.gpr .rsp = S → t.rd = s.rd → t.wr = s.wr → Outside B 0 256 s.mem t.mem →
    WP isa (.block (restorePairs ps)) t fun u =>
      u.mem = ps.foldl (fun m p => m.writeW (off B (8 * p.1))
        (s.mem.readW (S + BitVec.ofNat 64 p.2) 64)) t.mem ∧ Keep [.r11] t u
  | [], t, _, _, _, _, _, _ => WP.block_nil ⟨rfl, Keep.refl _ _⟩
  | p :: ps, t, hp, hB, hS, hrd, hwr, ho => by
    obtain ⟨hj, hL, hsrc⟩ := hp p List.mem_cons_self
    rw [show restorePairs (p :: ps) = restorePair p.1 p.2 ++ restorePairs ps from rfl, WP.block_append_iff]
    refine WP.mono (restorePair_ok (h.congr hwr) hZ hB hS hj (by rw [hrd, hwr]; exact hL) (hsrc _ ho))
      fun u ⟨hm, hk⟩ => ?_
    refine WP.mono (restorePairs_ok h hZ ps u (fun p' hp' => hp p' (List.mem_cons_of_mem _ hp'))
      ((hk.gpr (by decide)).trans hB) ((hk.gpr (by decide)).trans hS)
      (hk.2.1.trans hrd) (hk.2.2.trans hwr) (by
        rw [hm]
        exact ho.store_hdr (by omega_arith) (by decide) _)) fun v ⟨hv, k⟩ => ?_
    refine ⟨?_, (hk.trans k).mono (by decide)⟩
    rw [hv, hm]
    rfl

def restoredMem (m : Mem) (B S : Addr) : Mem :=
  restoreSlots.foldl (fun m' p => m'.writeW (off B (8 * p.1))
    (m.readW (S + BitVec.ofNat 64 p.2) 64)) m

private theorem fold_word (B : Addr) (j : Nat) (hj : j < 32)
    (v : Nat × Nat → BitVec 64) : ∀ (ps : List (Nat × Nat)) (m : Mem),
    (∀ p ∈ ps, p.1 < 32) → (∀ p ∈ ps, p.1 ≠ j) →
    word (ps.foldl (fun m p => m.writeW (off B (8 * p.1)) (v p)) m) B (8 * j) = word m B (8 * j)
  | [], _, _, _ => rfl
  | p :: ps, m, hps, hne => by
    rw [List.foldl_cons, fold_word B j hj v ps _ (fun q hq => hps q (List.mem_cons_of_mem _ hq))
      (fun q hq => hne q (List.mem_cons_of_mem _ hq))]
    exact hdrStore_hdr m B (v p) (hps p List.mem_cons_self) hj (hne p List.mem_cons_self)

theorem restored_header (m : Mem) (B S : Addr) {j : Nat} (hj : j < 16 ∨ j = kFlag) :
    word (restoredMem m B S) B (8 * j) = word m B (8 * j) := by
  apply fold_word B j (by rcases hj with hj | rfl; omega_arith; decide)
  · simp only [restoreSlots, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide
  · simp only [restoreSlots, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals
      rcases hj with hj | rfl
      all_goals simp only [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kE, kI, kElen, kUsed, kFlag, kPlen, VG.Impl.Bignum.sFn] at *; omega_arith

theorem restored_values (m : Mem) (B S : Addr) : ∀ p ∈ restoreSlots,
    word (restoredMem m B S) B (8 * p.1) = m.readW (S + BitVec.ofNat 64 p.2) 64 := by
  simp only [restoreSlots, List.mem_cons, List.not_mem_nil, or_false]
  rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals
    simp only [restoredMem, restoreSlots, List.foldl_cons, List.foldl_nil]
    repeat first
      | rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]
      | rw [word_writeW_self]

private theorem fold_byte (B x : Addr) (v : Nat × Nat → BitVec 64) :
    ∀ (ps : List (Nat × Nat)) (m : Mem), (∀ p ∈ ps, p.1 < 32) →
      (∀ p ∈ ps, ofs B x < 8 * p.1 ∨ 8 * p.1 + 8 ≤ ofs B x) →
      (ps.foldl (fun m p => m.writeW (off B (8 * p.1)) (v p)) m) x = m x
  | [], _, _, _ => rfl
  | p :: ps, m, hp, hx => by
    have hj := hp p List.mem_cons_self
    exact (fold_byte B x v ps _ (fun q hq => hp q (List.mem_cons_of_mem _ hq))
      (fun q hq => hx q (List.mem_cons_of_mem _ hq))).trans
      (writeW_outside m B (v p) (d := 8 * p.1) (by omega_arith) x (hx p List.mem_cons_self))

theorem restored_byte (m : Mem) (B S x : Addr)
    (hx : ∀ p ∈ restoreSlots, ofs B x < 8 * p.1 ∨ 8 * p.1 + 8 ≤ ofs B x) :
    restoredMem m B S x = m x := by
  apply fold_byte B x _ restoreSlots m ?_ hx
  simp only [restoreSlots, List.mem_cons, List.not_mem_nil, or_false]
  rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

private theorem fold_outside (B : Addr) (v : Nat × Nat → BitVec 64) :
    ∀ (ps : List (Nat × Nat)) (m : Mem), (∀ p ∈ ps, p.1 < 32) →
      Outside B 0 256 m (ps.foldl (fun m p => m.writeW (off B (8 * p.1)) (v p)) m)
  | [], m, _ => Outside.refl _ _ _ _
  | p :: ps, m, hp => by
    have hj := hp p List.mem_cons_self
    exact ((writeW_outside m B (v p) (d := 8 * p.1) (by omega_arith)).mono
      (Nat.zero_le _) (by omega_arith)).trans
      (fold_outside B v ps _ (fun q hq => hp q (List.mem_cons_of_mem _ hq)))

theorem restored_outside (m : Mem) (B S : Addr) : Outside B 0 256 m (restoredMem m B S) := by
  apply fold_outside
  simp only [restoreSlots, List.mem_cons, List.not_mem_nil, or_false]
  rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

private theorem outside_frame {B : Addr} {m m' : Mem} (h : Outside B 0 256 m m') :
    Frame [⟨B, 256⟩] m m' := by
  intro x hx
  apply h
  right
  have := hx ⟨B, 256⟩ (List.mem_singleton_self _)
  simp only [Region.Contains, ofs] at *
  omega_arith

theorem restored_stack (m : Mem) {B S : Addr} {Z d : Nat} (hZ : 256 ≤ Z)
    (hd : Region.Disjoint ⟨B, Z⟩ ⟨S, 112⟩) (hread : d + 8 ≤ 112) :
    (restoredMem m B S).readW (S + BitVec.ofNat 64 d) 64 = m.readW (S + BitVec.ofNat 64 d) 64 := by
  apply (outside_frame (restored_outside m B S)).readW (r := ⟨S, 112⟩)
  · exact Offset.contains_base S hread (by omega_arith)
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact (hd.sub_left (Region.sub_prefix hZ)).symm
  · decide

theorem restoreBookkeeping_ok {s : State} {B S : Addr} {Z : Nat}
    (h : Scr s B Z) (hZ : 256 ≤ Z) (hB : s.gpr .rdi = B) (hS : s.gpr .rsp = S)
    (hd : Region.Disjoint ⟨B, Z⟩ ⟨S, 112⟩)
    (hl : ∀ d, 8 ≤ d → d + 8 ≤ 112 → InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 d) 8) :
    WP isa (.block restoreBookkeeping) s fun t => t.mem = restoredMem s.mem B S ∧ Keep [.r11] s t := by
  apply restorePairs_ok h hZ restoreSlots s
  · simp only [restoreSlots, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals
      refine ⟨by decide, hl _ (by decide) (by decide), fun m' ho => ?_⟩
      apply (outside_frame ho).readW (r := ⟨S, 112⟩)
      · exact Offset.contains_base S (by decide) (by decide)
      · intro r hr
        simp only [List.mem_singleton] at hr
        subst hr
        exact (hd.sub_left (Region.sub_prefix hZ)).symm
      · decide
  · exact hB
  · exact hS
  · rfl
  · rfl
  · exact Outside.refl _ _ _ _

end VG.Proof.MillerRabin.X86_64
