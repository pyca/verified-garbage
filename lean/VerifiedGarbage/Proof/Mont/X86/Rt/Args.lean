module

import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.ArgFar
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Mont.X86.MulRt
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Impl.Mont.X86.MulRt
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The arguments of the run-time width multiplication

The nine arguments, read from the stack (`Args`): they lie past the working
space, so its changes keep them (`Args.keep`). A pointer is the working
space's address plus an offset argument (`ptr_ok`); a length, `8 n` times a
power of two (`lenTimes_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Rt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Dynamic (ArgFar readSrc_keep readSrc_upd)

/-- The arguments `A i` on the stack, past the working space. -/
structure Args (s : State) (W : Addr) (L : Nat) (A : Nat → BitVec 32) : Prop where
  read : ∀ i < 9, readSrc s (.mem (Rt.arg i)) = some (A i)
  far : ∀ i < 9, ArgFar s W L (Rt.arg i)

/-- Changes within the working space, with `esp` and the permissions as they
were, keep the arguments. -/
theorem Args.keep {s t : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (h : Args s W L A)
    (O : Outs W [(0, L)] s.mem t.mem) (hsp : t.gpr .esp = s.gpr .esp) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) : Args t W L A :=
  ⟨fun i hi => (readSrc_keep (h.far i hi) O (by simp) hsp hrd hwr).trans (h.read i hi),
    fun i hi => (h.far i hi).keep hsp⟩

theorem Args.of_keeps {s t : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (h : Args s W L A)
    {rs : List Reg} (K : Keeps rs s t) (hsp : .esp ∉ rs) (O : Outs W [(0, L)] s.mem t.mem) :
    Args t W L A := h.keep O (K.1 _ hsp) K.2.1 K.2.2

theorem Args.of_upd {s t : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (h : Args s W L A)
    {d : Reg} {v : BitVec 32} (u : Upd s t d v) (hd : d ≠ .esp) : Args t W L A :=
  h.of_keeps u.keeps (by simpa using hd.symm) (by rw [u.mem]; exact Outs.refl _ _ _)

/-- `r = ws + ` the argument `i`, through `t`. -/
theorem ptr_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (ha : Args s W L A)
    {r t : Reg} {i : Nat} (hi : i < 9) (hr : r ≠ .esp) (hrt : r ≠ t) :
    WP isa (.block (ptr r (Rt.arg i) t)) s fun u =>
      u.gpr r = A 0 + A i ∧ u.gpr t = A i ∧ u.mem = s.mem ∧ Keeps [r, t] s u := by
  simp only [ptr]
  refine wp_movS (ha.read 0 (by decide)) fun s₀ u₀ _ => ?_
  refine wp_movS (by rw [readSrc_upd u₀ (by simp only [Rt.arg, at_]; exact Ne.symm hr)]; exact ha.read i hi)
    fun s₁ u₁ _ => ?_
  refine wp_addS rfl fun s₂ u₂ _ => WP.block_nil ?_
  have K : Keeps [r, t] s s₂ := ⟨fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      rw [u₂.other _ hq.1, u₁.other _ hq.2, u₀.other _ hq.1],
    by rw [u₂.rd, u₁.rd, u₀.rd], by rw [u₂.wr, u₁.wr, u₀.wr]⟩
  exact ⟨by rw [u₂.gpr, u₁.other _ hrt, u₀.gpr, u₁.gpr], by rw [u₂.other _ (Ne.symm hrt), u₁.gpr],
    by rw [u₂.mem, u₁.mem, u₀.mem], K⟩

/-- `r = 8 n · 2^k`, modulo `2³²`, for the argument `n`. -/
theorem lenTimes_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (ha : Args s W L A)
    {r : Reg} (k : Nat) :
    WP isa (.block (lenTimes r k)) s fun u =>
      (u.gpr r).toNat = (A 2).toNat * 2 ^ (3 + k) % 2 ^ 32 ∧ u.mem = s.mem ∧ Keeps [r] s u := by
  simp only [lenTimes]
  refine wp_movS (ha.read 2 (by decide)) fun s₀ u₀ _ => ?_
  suffices ∀ c j (t : State), (t.gpr r).toNat = (A 2).toNat * 2 ^ j % 2 ^ 32 → t.mem = s.mem →
      Keeps [r] s t → WP isa (.block (List.replicate c (.alu .add r (.reg r)))) t fun u =>
        (u.gpr r).toNat = (A 2).toNat * 2 ^ (j + c) % 2 ^ 32 ∧ u.mem = s.mem ∧ Keeps [r] s u by
    have := this (3 + k) 0 s₀ (by rw [u₀.gpr]; simp [Nat.mod_eq_of_lt (A 2).isLt]) u₀.mem u₀.keeps
    rwa [Nat.zero_add] at this
  intro c
  induction c with
  | zero => intro j t h1 h2 h3; exact WP.block_nil ⟨by rw [h1, Nat.add_zero], h2, h3⟩
  | succ c ih =>
    intro j t h1 h2 h3
    rw [List.replicate_succ]
    refine wp_addS rfl fun t' u' _ => ?_
    refine (ih (j + 1) t' ?_ (by rw [u'.mem, h2]) (h3.trans (u'.keeps.mono (by simp)))).mono
      (fun u h => by rwa [show j + 1 + c = j + (c + 1) by omega] at h)
    rw [u'.gpr, BitVec.toNat_add, h1,
      show (A 2).toNat * 2 ^ (j + 1) = (A 2).toNat * 2 ^ j * 2 by rw [Nat.pow_succ, Nat.mul_assoc]]
    generalize (A 2).toNat * 2 ^ j = a
    omega

end VG.Proof.Mont.X86.Rt
