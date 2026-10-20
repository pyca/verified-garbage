module

import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Enc
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.SetupFin
import VerifiedGarbage.Proof.Gcm.Split
import VerifiedGarbage.Proof.Gcm.StreamTo
public import VerifiedGarbage.Proof.Gcm.Ctr
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Loop
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# The 256-bit loop in one pass over a source and then in place

Untrusted: everything here is checked by Lean. `StitchR.encN` runs the
out-of-place loop over the `nb` blocks at `src` (`StitchTo`, from a state
`s₀` meeting `SPreTo`), then the in-place loop (`Stitch`) over the blocks at
`dst` after them, `N` in all, as one loop: the in-place one goes on from the
group the out-of-place one encrypted last.

The in-place loop's lemmas are about a state `s₀'` it starts from; here that
is `nState s₀ N`: `s₀` with the data at `dst` (`r8`), `N` blocks (`r9`), and
the memory `nMem s₀` in which `dst` holds the plaintext at `src` in place of
its first `nb` blocks. Its ciphertext, counter, `Y` and powers are the
out-of-place loop's for those blocks, which it leaves where `nMem s₀` has
them, and the blocks after them, which it does not write, are where `s₀`
has them (`switch_ok`); the in-place loop then ends as from `s₀'`
(`Stitch.loopE_from_ok`, `Stitch.final_ok`), which is the contract
(`NPost`) for `s₀` (`NPost.of_ePost`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchR

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreTo EPost CtxMode sp op sR oR nb nr kp cp yp pp cb ciph sch hk y₀ dp
  dR pR cR yR kR bAddr blk ctb EInv AInv loopE_from_ok final_ok)
open VG.Proof.Gcm.X86_64.Stitch renaming sch_frame → sch_frame'
open VG.Proof.Gcm.X86_64.StitchTo (EInvTo AInvTo)
open VG.Proof.Gcm.X86_64.StitchZTo (dst sAddr pblk ctbT oAddr)
open VG.Proof.Gcm.X86_64.Pclmul (toNat_ofNat_lt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

section
variable (s₀ : State) (N : Nat)

/-- The output of `N` blocks. -/
abbrev nR : Region := ⟨op s₀, 16 * N⟩

/-- `s₀`'s memory with the plaintext at `src` in place of the first `nb`
blocks at `dst`. -/
def nMem : Mem := fun a =>
  if (a - op s₀).toNat < 16 * nb s₀ then s₀.mem (sp s₀ + (a - op s₀)) else s₀.mem a

/-- The state the in-place loop goes on as if from: the data at `dst`, `N`
blocks of it, in `nMem s₀`. -/
def nState : State := { (s₀.setReg .r8 (op s₀)).setReg .r9 (BitVec.ofNat 64 N) with mem := nMem s₀ }

end

/-- What `encN` needs besides `SPreTo`: `N` blocks at `dst`, a multiple of 16
from `nb` on, with `dst` in `rbx` and `N - nb` in `rbp`, and the output's
regions for all of them. -/
structure NPre (M : CtxMode) (s₀ : State) (N : Nat) : Prop where
  le : nb s₀ ≤ N
  m16 : N % 16 = 0
  rbx : s₀.gpr .rbx = op s₀
  rbp : s₀.gpr .rbp = BitVec.ofNat 64 (N - nb s₀)
  o_in : InRegions s₀.wr (op s₀) (16 * N)
  k_o : (⟨kp s₀, M.len⟩ : Region).Disjoint (nR s₀ N)
  o_c : (nR s₀ N).Disjoint (cR s₀)
  o_y : (nR s₀ N).Disjoint (yR s₀)
  o_p : (nR s₀ N).Disjoint (pR s₀)
  wrap : (op s₀).toNat + 16 * N ≤ 2 ^ 64

/-- What `encN` leaves: the `N` blocks, the plaintext at `src` and then the
blocks at `dst` after it, encrypted at `dst`, the counter advanced, `Y`
continued over the ciphertext, nothing else written but the working space. -/
structure NPost (s₀ : State) (N : Nat) (s : State) : Prop where
  data : blocksAt s.mem (op s₀) N = Spec.Gcm.ctr32 (ciph s₀) (cb s₀)
    (blocksAt s₀.mem (sp s₀) (nb s₀) ++ blocksAt s₀.mem (oAddr s₀ (nb s₀)) (N - nb s₀))
  ctr : blockAt s.mem (cp s₀) = Nat.repeat inc32 N (cb s₀)
  y : blockAt s.mem (yp s₀) = ghashFrom (hk s₀) (y₀ s₀) (blocksAt s.mem (op s₀) N)
  frame : Frame [cR s₀, yR s₀, nR s₀ N, pR s₀] s₀.mem s.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-! ## The memory -/

/-- `nMem s₀` is `s₀`'s memory outside the first `nb` blocks at `dst`. -/
theorem nMem_frame (s₀ : State) : Frame [oR s₀] s₀.mem (nMem s₀) := fun x hx => by
  have h := hx (oR s₀) List.mem_cons_self
  simp only [Region.Contains] at h
  simp only [nMem, show ¬ (x - op s₀).toNat < 16 * nb s₀ by omega, ite_false]

theorem toNat_oAddr_sub {s₀ : State} (hw : (op s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64) {k i : Nat} (hk : k < nb s₀)
    (hi : i < 16) : (oAddr s₀ k + BitVec.ofNat 64 i - op s₀).toNat = 16 * k + i := by
  rw [BitVec.add_assoc, Offset.add_sub_cancel_left, ← BitVec.ofNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]

/-- The first `nb` blocks at `dst` in `nMem s₀` are the plaintext's. -/
theorem blockAt_nMem_lo {s₀ : State} (hw : (op s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64) {k : Nat} (hk : k < nb s₀) :
    blockAt (nMem s₀) (oAddr s₀ k) = pblk s₀ k := by
  simp only [pblk, blockAt, Spec.Aes.bytesAt]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hi' : i < 16 := List.mem_range.mp hi
  simp only [nMem, toNat_oAddr_sub hw hk hi', show 16 * k + i < 16 * nb s₀ by omega, ite_true]
  rw [BitVec.add_assoc, Offset.add_sub_cancel_left, ← BitVec.add_assoc]

/-- The blocks at `dst` after them are `s₀`'s. -/
theorem blockAt_nMem_hi {s₀ : State} {N : Nat} (hwN : (op s₀).toNat + 16 * N ≤ 2 ^ 64) {k : Nat}
    (hk : nb s₀ ≤ k) (hkN : k < N) : blockAt (nMem s₀) (oAddr s₀ k) = blockAt s₀.mem (oAddr s₀ k) :=
  VG.Proof.Aes.X86_64.AesNi.blockAt_frame (nMem_frame s₀) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base _ (by omega) (by omega)

/-- The `16 N` bytes at `dst` in `nMem s₀`: the plaintext at `src`, then
`s₀`'s at `dst` after its first `nb` blocks. -/
theorem bytesAt_nMem {s₀ : State} {N : Nat} (hwN : (op s₀).toNat + 16 * N ≤ 2 ^ 64) (hle : nb s₀ ≤ N) :
    Spec.Aes.bytesAt (nMem s₀) (op s₀) (16 * N) = Spec.Aes.bytesAt s₀.mem (sp s₀) (16 * nb s₀) ++
      Spec.Aes.bytesAt s₀.mem (oAddr s₀ (nb s₀)) (16 * (N - nb s₀)) := by
  rw [show 16 * N = 16 * nb s₀ + 16 * (N - nb s₀) by omega]
  simp only [Spec.Aes.bytesAt, List.range_add, List.map_append, List.map_map]
  have hsub : ∀ i, i < 16 * N → (op s₀ + BitVec.ofNat 64 i - op s₀).toNat = i := fun i hi => by
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    have e : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [nMem, Offset.add_sub_cancel_left, e, hi', ↓reduceIte]
  · refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    have e := hsub (16 * nb s₀ + i) (by omega)
    simp only [Function.comp_apply, nMem, oAddr, BitVec.add_assoc, ← BitVec.ofNat_add, e,
      show ¬ 16 * nb s₀ + i < 16 * nb s₀ by omega, ↓reduceIte]

/-- The `N` blocks at `dst` in `nMem s₀`. -/
theorem blocksAt_nMem {s₀ : State} {N : Nat} (hw : (op s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64)
    (hwN : (op s₀).toNat + 16 * N ≤ 2 ^ 64) (hle : nb s₀ ≤ N) : blocksAt (nMem s₀) (op s₀) N =
      blocksAt s₀.mem (sp s₀) (nb s₀) ++ blocksAt s₀.mem (oAddr s₀ (nb s₀)) (N - nb s₀) := by
  rw [show N = nb s₀ + (N - nb s₀) by omega, Proof.Gcm.blocksAt_add, Nat.add_sub_cancel_left]
  congr 1
  · simp only [blocksAt]
    exact List.map_congr_left fun i hi => blockAt_nMem_lo hw (List.mem_range.mp hi)
  · simp only [blocksAt]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [show oAddr s₀ (nb s₀) + BitVec.ofNat 64 (16 * i) = oAddr s₀ (nb s₀ + i) by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add]]
    exact blockAt_nMem_hi hwN (by omega) (by omega)

/-! ## The in-place view -/

section
variable {s₀ : State} {N : Nat}

theorem nState_gpr {r : Reg} (h8 : r ≠ .r8) (h9 : r ≠ .r9) : (nState s₀ N).gpr r = s₀.gpr r := by
  simp [nState, State.setReg, h8, h9]

theorem nState_r8 : (nState s₀ N).gpr .r8 = op s₀ := by simp [nState, State.setReg]
theorem nState_r9 : (nState s₀ N).gpr .r9 = BitVec.ofNat 64 N := by simp [nState, State.setReg]
theorem nState_mem : (nState s₀ N).mem = nMem s₀ := rfl
theorem nState_rd : (nState s₀ N).rd = s₀.rd := rfl
theorem nState_wr : (nState s₀ N).wr = s₀.wr := rfl

theorem nb_nState (h : N < 2 ^ 64) : nb (nState s₀ N) = N := by
  simp only [nb, nState_r9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The memory of `nState s₀ N` against `s₀`'s, as the in-place view of the
out-of-place start sees it. -/
theorem nMem_frameD (s₀ : State) : Frame [dR (dst s₀), pR (dst s₀)] s₀.mem (nMem s₀) :=
  (nMem_frame s₀).mono fun r hr => by simp at hr ⊢; exact Or.inl hr

variable {M : CtxMode} (hp : SPreTo M s₀)
include hp

theorem sch_nState : sch (nState s₀ N) = sch s₀ := by
  have := sch_frame' hp.toD (nMem_frameD s₀)
  simpa only [sch, nr, kp, nState_mem, nState_gpr (r := .rdi) (by decide) (by decide),
    nState_gpr (r := .rsi) (by decide) (by decide), StitchZTo.dst_gpr_ne s₀ (r := .rdi) (by decide),
    StitchZTo.dst_gpr_ne s₀ (r := .rsi) (by decide), StitchZTo.dst_mem] using this

theorem ciph_nState : ciph (nState s₀ N) = ciph s₀ := by
  simp only [ciph, sch_nState hp, nr, nState_gpr (r := .rsi) (by decide) (by decide)]

theorem cb_nState : cb (nState s₀ N) = cb s₀ := by
  have hw := hp.wrap_o
  simp only [cb, cp, nState_mem, nState_gpr (r := .rdx) (by decide) (by decide)]
  exact VG.Proof.Aes.X86_64.AesNi.blockAt_frame (nMem_frame s₀) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.o_c.symm

theorem hk_nState : hk (nState s₀ N) = hk s₀ := by
  have hw := hp.wrap_k
  have hge := M.ge
  simp only [hk, kp, nState_mem, nState_gpr (r := .rdi) (by decide) (by decide)]
  exact VG.Proof.Aes.X86_64.AesNi.blockAt_frame (nMem_frame s₀) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.k_o.sub_left (Offset.sub_base _ (by omega))

theorem y₀_nState : y₀ (nState s₀ N) = y₀ s₀ := by
  simp only [y₀, yp, nState_mem, nState_gpr (r := .rcx) (by decide) (by decide)]
  exact VG.Proof.Aes.X86_64.AesNi.blockAt_frame (nMem_frame s₀) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.o_y.symm

/-- Block `k` of `nState s₀ N`'s data: the plaintext's, and then `s₀`'s at
`dst`. -/
theorem blk_nState (hwN : (op s₀).toNat + 16 * N ≤ 2 ^ 64) {k : Nat} (hk : k < N) :
    blk (nState s₀ N) k = if k < nb s₀ then pblk s₀ k else blockAt s₀.mem (oAddr s₀ k) := by
  simp only [blk, bAddr, dp, nState_r8, nState_mem]
  split
  · exact blockAt_nMem_lo hp.wrap_o (by omega)
  · exact blockAt_nMem_hi hwN (by omega) hk

theorem ctb_nState (hwN : (op s₀).toNat + 16 * N ≤ 2 ^ 64) {k : Nat} (hk : k < nb s₀) (hkN : k < N) :
    ctb (nState s₀ N) k = ctbT s₀ k := by
  simp only [ctb, blk_nState hp hwN hkN, hk, ite_true, ciph_nState hp, cb_nState hp]

/-- The in-place loop's start. -/
theorem NPre.sPre (hn : NPre M s₀ N) : SPre (nState s₀ N) := by
  have d := hp.toD
  have hN : N < 2 ^ 64 := by have := hn.wrap; have := hp.nb16; have := hn.le; omega
  have g : ∀ r, r ≠ .r8 → r ≠ .r9 → (nState s₀ N).gpr r = (dst s₀).gpr r := fun r h8 h9 => by
    rw [nState_gpr h8 h9, StitchZTo.dst_gpr_ne s₀ h8]
  have hk : kp (nState s₀ N) = kp (dst s₀) := g .rdi (by decide) (by decide)
  have hr : (nState s₀ N).gpr .rsi = (dst s₀).gpr .rsi := g .rsi (by decide) (by decide)
  have hc : cp (nState s₀ N) = cp (dst s₀) := g .rdx (by decide) (by decide)
  have hy : yp (nState s₀ N) = yp (dst s₀) := g .rcx (by decide) (by decide)
  have hpp : pp (nState s₀ N) = pp (dst s₀) := g .r11 (by decide) (by decide)
  have hd : dR (nState s₀ N) = nR s₀ N := by simp only [dR, dp, nState_r8, nb_nState hN]
  have hge := M.ge
  have kD : (nR s₀ N).Disjoint (kR (dst s₀)) := hn.k_o.symm.sub_right (Region.sub_prefix hge)
  exact {
    rounds := by simp only [nr, hr]; exact d.rounds
    nb16 := by rw [nb_nState hN]; have := hp.nb16; have := hn.le; omega
    k_in := by rw [nState_rd, nState_wr, hk]; exact d.k_in
    c_in := by rw [nState_wr, hc]; exact d.c_in
    y_in := by rw [nState_wr, hy]; exact d.y_in
    d_in := by rw [nState_wr, dp, nState_r8, nb_nState hN]; exact hn.o_in
    p_in := by rw [nState_wr, hpp]; exact d.p_in
    d_k := by rw [hd, kR, hk]; exact kD
    d_c := by rw [hd, cR, hc]; exact hn.o_c
    d_y := by rw [hd, yR, hy]; exact hn.o_y
    d_p := by rw [hd, pR, hpp]; exact hn.o_p
    p_k := by rw [pR, kR, hpp, hk]; exact d.p_k
    p_c := by rw [pR, cR, hpp, hc]; exact d.p_c
    p_y := by rw [pR, yR, hpp, hy]; exact d.p_y
    c_y := by rw [cR, yR, hc, hy]; exact d.c_y
    c_k := by rw [cR, kR, hc, hk]; exact d.c_k
    y_k := by rw [yR, kR, hy, hk]; exact d.y_k
    wrap_d := by rw [dp, nState_r8, nb_nState hN]; exact hn.wrap
    wrap_k := by rw [hk]; exact d.wrap_k
    wrap_p := by rw [hpp]; exact d.wrap_p }

/-- A state with `r8 ← rbx` and `r9 += rbp` from one the out-of-place loop
left after its last group `e` is one the in-place loop reaches from
`nState s₀ N` after group `e`. -/
theorem NPre.eInv (hn : NPre M s₀ N) {P : Nat → Nat → Block} {e : Nat} (he : nb s₀ = 16 * e) {s : State}
    (hI : EInvTo s₀ P e s) {t : State} (g8 : t.gpr .r8 = s.gpr .rbx) (g9 : t.gpr .r9 = s.gpr .r9 + s.gpr .rbp)
    (g : ∀ r, r ≠ .r8 → r ≠ .r9 → t.gpr r = s.gpr r) (hm : t.mem = s.mem) (hx : t.xmm = s.xmm)
    (hy : t.ymmHi = s.ymmHi) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : EInv (nState s₀ N) P e t := by
  have hN : N < 2 ^ 64 := by have := hn.wrap; have := hp.nb16; have := hn.le; omega
  have hw := hp.wrap_o
  have hwN := hn.wrap
  have hle := hn.le
  have hl : ∀ r l, t.lane r l = s.lane r l := fun r l => by simp only [State.lane, hx, hy]
  have h1 := hI.one
  have hA := hI.a
  have hg : ∀ r, r ≠ .r8 → r ≠ .r9 → (nState s₀ N).gpr r = s₀.gpr r := fun r h8 h9 => nState_gpr h8 h9
  have fr : Frame [dR (nState s₀ N), pR (nState s₀ N)] (nState s₀ N).mem t.mem := fun x hx' => by
    have h₁ := hx' _ List.mem_cons_self
    have h₂ := hx' _ (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [dp, nState_r8, nb_nState hN, pp, hg .r11 (by decide) (by decide), Region.Contains] at h₁ h₂
    rw [hm, nState_mem, hA.frame x (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [Region.Contains]; omega
      · simp only [Region.Contains]; exact h₂), nMem_frame s₀ x (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only [Region.Contains]; omega)]
  have bl : ∀ k < nb (nState s₀ N), blockAt t.mem (bAddr (nState s₀ N) k) =
      if k < 16 * e then ctb (nState s₀ N) k else blk (nState s₀ N) k := fun k hk => by
    rw [nb_nState hN] at hk
    rw [show bAddr (nState s₀ N) k = oAddr s₀ k by simp only [bAddr, dp, nState_r8], hm]
    by_cases hlo : k < 16 * e
    · simp only [hlo, ↓reduceIte, ctb_nState hp hwN (by omega) hk]
      exact hA.blocks k (by omega)
    · simp only [hlo, ↓reduceIte, blk_nState hp hwN hk, show ¬ k < nb s₀ by omega]
      refine VG.Proof.Aes.X86_64.AesNi.blockAt_frame hA.frame fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base _ (by omega) (by omega)
      · exact hn.o_p.sub_left (Offset.sub_base _ (by omega))
  have rbp : s.gpr .rbp = BitVec.ofNat 64 (N - nb s₀) := by
    rw [hI.gpr .rbp (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hn.rbp
  exact {
    a := {
      le := by rw [nb_nState hN]; omega
      ctr := fun l hl' => by rw [hl, cb_nState hp]; exact hA.ctr l hl'
      msk := fun l hl' => by rw [hl]; exact hA.msk l hl'
      inc := fun l hl' => by rw [hl]; exact hA.inc l hl'
      rdi := by rw [g .rdi (by decide) (by decide), hA.rdi]; exact (hg .rdi (by decide) (by decide)).symm
      rsi := by rw [g .rsi (by decide) (by decide), hA.rsi, hg .rsi (by decide) (by decide)]
      r10 := by
        rw [g .r10 (by decide) (by decide), hA.r10]
        simp only [kp, nr, hg .rdi (by decide) (by decide), hg .rsi (by decide) (by decide)]
      frame := fr
      blocks := bl
      rd := by rw [hrd, hA.rd]; rfl
      wr := by rw [hwr, hA.wr]; rfl }
    one := h1
    rdx := by rw [g .rdx (by decide) (by decide), hI.rdx, dp, nState_r8]
    r9 := by
      rw [g9, hI.r9, rbp, nb_nState hN, ← BitVec.ofNat_add]
      congr 1; omega
    rax := by rw [g .rax (by decide) (by decide), hI.rax]; exact (hg .rdx (by decide) (by decide)).symm
    gpr := fun r ha hd h9 h10 => by
      by_cases h8 : r = .r8
      · subst h8
        rw [g8, hI.gpr .rbx (by decide) (by decide) (by decide) (by decide) (by decide), hn.rbx, nState_r8]
      · rw [g r h8 h9, hI.gpr r ha hd h8 h9 h10, hg r h8 h9]
    pw := fun k hk l hl' => by
      rw [hm, pp, hg .r11 (by decide) (by decide)]; exact hI.pw k hk l hl'
    m1 := fun l hl' => by rw [hl]; exact hI.m1 l hl'
    y := by
      rw [hl, hI.y, hk_nState hp, y₀_nState hp]
      congr 1
      refine List.map_congr_left fun k hk => ?_
      have := List.mem_range.mp hk
      exact (ctb_nState hp hwN (by omega) (by omega)).symm
    y1 := by rw [hl]; exact hI.y1 }

/-- `r8 ← rbx`, `r9 += rbp` and `cmp r9, 32` after the out-of-place loop. -/
theorem switch_ok (hn : NPre M s₀ N) {P : Nat → Nat → Block} {e : Nat} (he : nb s₀ = 16 * e) {s : State}
    (hI : EInvTo s₀ P e s) :
    WP isa (.block [.mov .r8 (.reg .rbx), .alu .add .r9 (.reg .rbp), .alu .cmp .r9 (.imm 32)]) s fun t =>
      EInv (nState s₀ N) P e t ∧ t.cf = some (decide (nb (nState s₀ N) - 16 * (e - 1) < 32)) := by
  rw [show ([.mov .r8 (.reg .rbx), .alu .add .r9 (.reg .rbp), .alu .cmp .r9 (.imm 32)] : List Instr) =
    [.mov .r8 (.reg .rbx), .alu .add .r9 (.reg .rbp)] ++ [.alu .cmp .r9 (.imm 32)] from rfl, WP.block_append_iff]
  refine WP.mono (Q := fun t => EInv (nState s₀ N) P e t) ?_ fun t hI' => Stitch.cmpE_ok hI'
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, isa, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact hn.eInv hp he hI (by simp [RegUpd.gpr_setReg])
    (by simp [RegUpd.gpr_setReg])
    (fun r h8 h9 => by simp [RegUpd.gpr_setReg, h8, h9]) rfl rfl rfl rfl rfl

/-- What the in-place loop leaves from `nState s₀ N` is the contract for
`s₀`. -/
theorem NPost.of_ePost (hn : NPre M s₀ N) {s : State} (h : EPost (nState s₀ N) s) : NPost s₀ N s := by
  have hN : N < 2 ^ 64 := by have := hn.wrap; have := hp.nb16; have := hn.le; omega
  have hw := hp.wrap_o
  have hwN := hn.wrap
  have hle := hn.le
  have hg : ∀ r, r ≠ .r8 → r ≠ .r9 → (nState s₀ N).gpr r = s₀.gpr r := fun r h8 h9 => nState_gpr h8 h9
  have hd : dp (nState s₀ N) = op s₀ := nState_r8
  have hc : cp (nState s₀ N) = cp s₀ := hg .rdx (by decide) (by decide)
  have hy : yp (nState s₀ N) = yp s₀ := hg .rcx (by decide) (by decide)
  have hpp : pp (nState s₀ N) = pp s₀ := hg .r11 (by decide) (by decide)
  have src := blocksAt_nMem hw hwN hle
  exact {
    data := by
      have := h.data
      rwa [hd, nb_nState hN, ciph_nState hp, cb_nState hp, nState_mem, src] at this
    ctr := by have := h.ctr; rwa [hc, nb_nState hN, cb_nState hp] at this
    y := by have := h.y; rwa [hy, hk_nState hp, y₀_nState hp, hd, nb_nState hN] at this
    frame := fun x hx => by
      have h₃ := hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      simp only [Region.Contains] at h₃
      rw [h.frame x (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [cR, hc]; exact hx _ List.mem_cons_self
        · rw [yR, hy]; exact hx _ (List.mem_cons_of_mem _ List.mem_cons_self)
        · simp only [hd, nb_nState hN, Region.Contains]; exact h₃
        · rw [pR, hpp]; exact hx _ (by simp)), nState_mem, nMem_frame s₀ x (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; simp only [Region.Contains]; omega)]
    gpr := fun r ha hd' h8 h9 h10 => by rw [h.gpr r ha hd' h9 h10, hg r h8 h9]
    rd := h.rd
    wr := h.wr }

/-- `NPost`'s ciphertext, as bytes: the plaintext at `src` and then at `dst`
after it, with the keystream from the counter block. -/
theorem NPost.bytes (hn : NPre M s₀ N) {s : State} (h : NPost s₀ N s) :
    Spec.Aes.bytesAt s.mem (op s₀) (16 * N) = Proof.Gcm.xorKs (ciph s₀) (cb s₀) 0
      (Spec.Aes.bytesAt s₀.mem (sp s₀) (16 * nb s₀) ++ Spec.Aes.bytesAt s₀.mem (oAddr s₀ (nb s₀)) (16 * (N - nb s₀))) := by
  have hcb : blockAt (nMem s₀) (cp s₀) = cb s₀ :=
    VG.Proof.Aes.X86_64.AesNi.blockAt_frame (nMem_frame s₀) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.o_c.symm
  have hd : blocksAt s.mem (op s₀) N = Spec.Gcm.ctr32 (ciph s₀) (blockAt (nMem s₀) (cp s₀))
      (blocksAt (nMem s₀) (op s₀) N) := by
    rw [hcb, blocksAt_nMem hp.wrap_o hn.wrap hn.le]; exact h.data
  rw [← bytesAt_nMem hn.wrap hn.le]
  exact (Proof.Gcm.ctr_wholeTo (m := nMem s₀) (m' := s.mem) (cb := cp s₀) (ks := cp s₀) (sp := op s₀)
    (dp := op s₀) (ciph := ciph s₀) (icb := cb s₀) (n := 0) (nb := N) ⟨by rw [hcb]; rfl, fun h => (h rfl).elim⟩
    rfl hd (by rw [hcb]; exact h.ctr)).1

end

/-- `encN` meets its contract. -/
theorem encN_ok (hS : SetupFin) {s₀ : State} (hp : SPreTo CtxMode.prepared s₀) (hm : nb s₀ % 16 = 0) {N : Nat}
    (hn : NPre CtxMode.prepared s₀ N) : WP isa Impl.Gcm.X86_64.StitchR.encN s₀ (NPost s₀ N) := by
  have hN : N < 2 ^ 64 := by have := hn.wrap; have := hp.nb16; have := hn.le; omega
  have hp' := hn.sPre hp
  refine WP.seq (WP.mono (hS hp) fun s₁ ⟨P, hR, hf⟩ => ?_)
  refine WP.seq (WP.mono (StitchTo.firstTo_ok hp hR) fun s₂ hI₂ => ?_)
  refine WP.seq (WP.mono (StitchTo.cmpE_ok hI₂) fun s₃ ⟨hI₃, hcf⟩ => ?_)
  refine WP.seq (WP.mono (StitchTo.loopE_ok hp hm hf hI₃ hcf) fun s₄ ⟨e, he, hI₄⟩ => ?_)
  refine WP.seq (WP.mono (switch_ok hp hn he hI₄) fun s₅ ⟨hI₅, hcf₅⟩ => ?_)
  have hf' : Stitch.FinOk Impl.Gcm.X86_64.Stitch.ordE (hk (nState s₀ N)) P := by
    rw [hk_nState hp]; exact hf
  have hm' : nb (nState s₀ N) % 16 = 0 := by rw [nb_nState hN]; exact hn.m16
  refine WP.seq (WP.mono (loopE_from_ok hm' hp' hf' hI₅ hcf₅) fun s₆ ⟨e', he', hI₆⟩ => ?_)
  exact WP.mono (final_ok hp' hf' he' hI₆) fun _ h => NPost.of_ePost hp hn h

end VG.Proof.Gcm.X86_64.StitchR
