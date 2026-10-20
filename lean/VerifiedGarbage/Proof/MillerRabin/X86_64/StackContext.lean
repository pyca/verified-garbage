module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Stack
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # Entering the fixed frame preserves the prepared workspace -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.MillerRabin.X86_64

theorem entered_word {s : State} {B : Addr} {Z d : Nat}
    (hs : 120 ≤ (s.gpr .rsp).toNat) (hn : B.toNat + Z ≤ 2 ^ 64)
    (hd : Region.Disjoint ⟨s.gpr .rsp - 112#64, 112⟩ ⟨B, Z⟩) (hread : d + 8 ≤ Z) :
    word (entered s).mem B d = word s.mem B d := by
  apply (entered_frame s hs).readW (r := ⟨B, Z⟩)
  · exact Offset.contains_base B hread (by omega_arith)
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact hd.symm
  · decide

theorem entered_wv {s : State} {B : Addr} {Z d k : Nat}
    (hs : 120 ≤ (s.gpr .rsp).toNat) (hn : B.toNat + Z ≤ 2 ^ 64)
    (hd : Region.Disjoint ⟨s.gpr .rsp - 112#64, 112⟩ ⟨B, Z⟩) (hread : d + 8 * k ≤ Z) :
    wv (entered s).mem B d k = wv s.mem B d k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [wv, wv, ih (by omega_arith), entered_word hs hn hd (by omega_arith)]

theorem entered_good {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (h : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hs : 120 ≤ (s.gpr .rsp).toNat)
    (hd : Region.Disjoint ⟨s.gpr .rsp - 112#64, 112⟩ ⟨B, Z⟩) :
    Good (entered s) B Z w mi := by
  have hr : ∀ i < 16, word (entered s).mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    entered_word hs h.scr.nowrap hd (by have := hdr_lt_slot w 8 (by omega_arith : i < 32); omega_arith)
  have hscr : Scr (entered s) B Z := by
    obtain ⟨⟨B₀, o, L, hm, hb, he, hL⟩, hn⟩ := h.scr
    refine ⟨⟨B₀, o, L, ?_, hb, he, hL⟩, hn⟩
    rw [entered_wr]
    exact List.mem_append_right _ hm
  refine ⟨hscr, (entered_gpr s (by decide)).trans h.rdi, ?_, ?_, ?_⟩
  · rw [hr sW (by decide)]; exact h.hdr.hw
  · rw [hr sMinv (by decide)]; exact h.hdr.hminv
  · intro j hj
    rw [hr (sArr j) (by unfold sArr; omega_arith)]
    exact h.hdr.harr j hj

end VG.Proof.MillerRabin.X86_64
