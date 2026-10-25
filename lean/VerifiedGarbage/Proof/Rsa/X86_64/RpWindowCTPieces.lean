module

import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowLoop
public import VerifiedGarbage.Proof.Rsa.X86_64.RpCT5
import VerifiedGarbage.Proof.Rsa.X86_64.RpCT4
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowLoop
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpCT5
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpCT4
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowPowers
import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowBase

/-! # Recovery windows: constant time of selection and arithmetic -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt)
open Rp

namespace RecoveryWindow

/-- Bounds needed within a window, without making any exponent digit public. -/
def WT (hx : Bool) (p : RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N r t g : Nat), Cst s p.B p.Z (wk p.k) minv N p.el r t ∧
    Powers s.mem p.B (wk p.k) N g ∧ wv s.mem p.B (slot (wk p.k) aY) (wk p.k) < N ∧
    (hx = true → wv s.mem p.B (slot (wk p.k) aXm) (wk p.k) < N)

theorem WT.ws {hx : Bool} {p : RpP} {s : State} (h : WT hx p s) : Ws s p.B p.Z (wk p.k) := by
  obtain ⟨_, _, _, _, _, hc, -⟩ := h
  exact hc.ws

theorem WT.pins (hx : Bool) : Pins (WT hx) [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]

theorem pickBound_ok {p : RpP} {s : State} {a j : Nat} (ha : a ∈ [aG, aE, aD]) (hj : j < 4)
    (h : WT true p s) : WP isa (windowPick a j) s (WT true p) := by
  obtain ⟨minv, N, r, t, g, hc, hp, hy, hx⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  have ha16 : a < 16 := by rcases ha with rfl | rfl | rfl <;> decide
  have hne : aXm ≠ a := by rcases ha with rfl | rfl | rfl <;> decide
  have hbound : wv s.mem p.B (slot (wk p.k) a) (wk p.k) < N := by
    rcases ha with rfl | rfl | rfl
    · exact hp.g1lt
    · exact hp.g2lt
    · exact hp.g3lt
  refine WP.mono (pick_ok hc.ws ha16 hne hj (V := (word s.mem p.B (8 * sC2)).toNat)
    (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]) (BitVec.isLt _)) fun u ⟨hf, k, hu⟩ => ?_
  refine ⟨minv, N, r, t, g, hc.congr hf (by decide) (by simp) k (by decide),
    hp.congr hf hc.hZ16 (by simp) (by decide) (by decide) (by decide), ?_, fun _ => ?_⟩
  · rw [hf.rg_wv hc.hZ16 (by simp) (by decide) (by decide) (by omega)]; exact hy
  · rw [hu]; split
    · exact hx rfl
    · exact hbound

def pickVal (a : Nat) (p : RpP) : Reg → BitVec 64
  | .rdi => p.B
  | .r8 => off p.B (slot (wk p.k) aXm)
  | .rsi => off p.B (slot (wk p.k) a)
  | .r12 => BitVec.ofNat 64 (wk p.k)
  | _ => 0

/-- Each table address is pinned independently of the masked digit. -/
theorem pick_ct (a j : Nat) (ha : a ∈ [aG, aE, aD]) (hj : j < 4)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block (ws ++ base aXm .r8 ++ base a .rsi ++
      ([.mov .rax (.mem (hdr sC2)), .shift .shr .rax 62,
        .alu .xor .rax (.imm (BitVec.ofNat 32 j)), .alu .cmp .rax (.imm 1),
        .alu .sbb .rbp (.reg .rbp), .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))] : List Instr))) hint).isSome = true) :
    RelCT isa (Two (WT true)) (windowPick a j) (Two (WT true)) := by
  unfold windowPick
  refine pin_ct [.rdi] [.rdi, .r8, .rsi, .r12] (pickVal a) (WT.pins true) ht
    (fun p s h => ?_) (by taint_decide) (fun p s h => pickBound_ok ha hj h)
  refine WP.mono (pickRegs_ok h.ws hj (V := (word s.mem p.B (8 * sC2)).toNat)
    (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]) (BitVec.isLt _))
    fun u ⟨h8, hsi, h12, _, _, k⟩ rr hrr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrr
  rcases hrr with rfl | rfl | rfl | rfl
  · exact (k.gpr (by decide)).trans h.ws.rdi
  · exact h8
  · exact hsi
  · exact h12

theorem select_ct : RelCT isa (Two (WT false)) windowSelect (Two (WT true)) := by
  simp only [windowSelect, seqs]
  refine RelCT.seq (copyA_gct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) (by taint_decide)
    fun p s h => ?_) (RelCT.seq (pick_ct aG 1 (by decide) (by decide) (by taint_decide))
      (RelCT.seq (pick_ct aE 2 (by decide) (by decide) (by taint_decide))
        (pick_ct aD 3 (by decide) (by decide) (by taint_decide))))
  obtain ⟨minv, N, r, t, g, hc, hp, hy, -⟩ := h
  have hn : 0 < N := by have := hc.n1; omega
  refine WP.mono (copy_ok hc (o := aXm) (a := aO) (by decide) (by decide) (by decide) (by decide))
    fun u ⟨hc', hf, k, hx⟩ => ?_
  exact ⟨minv, N, r, t, g, hc', hp.congr hf hc.hZ16 (by simp) (by decide) (by decide) (by decide),
    by rw [hf.rg_wv hc.hZ16 (by simp) (by decide) (by decide) (by omega)]; exact hy,
    fun _ => by rw [hx, hc.ho]; exact Nat.mod_lt _ hn⟩

/-- A square or the multiplication by the selected power. -/
theorem mul_ct (M : Mont) (sqr : Bool) : RelCT isa (Two (WT true))
    (M.mm aY aY (if sqr then aY else aXm)) (Two (WT true)) := by
  have hb8 : (if sqr then aY else aXm) < 8 := by cases sqr <;> decide
  have hb1 : (if sqr then aY else aXm) ≠ aAcc := by cases sqr <;> decide
  have hb2 : (if sqr then aY else aXm) ≠ aTmp := by cases sqr <;> decide
  refine mm_gct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) M
    (by cases sqr <;> unfold MmUse <;> decide) fun p s h => ?_
  obtain ⟨minv, N, r, t, g, hc, hp, hy, hx⟩ := h
  refine WP.mono (mul_ok M hc (a := aY) (b := if sqr then aY else aXm)
    (by decide) hb8 (by decide) (by decide) hb1 hb2 (by cases sqr; exact hx rfl; exact hy))
    fun u ⟨hc', hf, k, hy', _⟩ => ?_
  exact ⟨minv, N, r, t, g, hc', hp.congr hf hc.hZ16 (by simp) (by decide) (by decide) (by decide),
    hy', fun _ => by rw [hf.rg_wv hc.hZ16 (by simp) (by decide) (by decide) (by omega)]; exact hx rfl⟩

theorem body_ct (M : Mont) : RelCT isa (Two (WT false)) (windowBody M.mm) fun _ _ => True := by
  simp only [windowBody, seqs]
  exact RelCT.seq select_ct (RelCT.seq (mul_ct M true) (RelCT.seq (mul_ct M true)
    (RelCT.seq (mul_ct M false) (two_taint [.rdi] (WT.pins true) (by taint_decide)))))

end RecoveryWindow
end VG.Proof.Rsa.X86_64
