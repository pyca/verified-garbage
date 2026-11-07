module

import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitched
public import VerifiedGarbage.Proof.ChaCha20.AArch64.XorContract
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Spec.ChaCha20.Contract
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitched
public import VerifiedGarbage.Spec.ChaCha20
public import VerifiedGarbage.TCB.Artifact

/-!
# Implementations of `vg_chacha20_xor` on AArch64

An `XorImpl` is what a function that calls `vg_chacha20_xor` needs of it, so
that its proof holds for every implementation: each is a variant of the
interface `ChaCha20Xor` on AArch64 (`Variants/ChaCha20Xor/AArch64/`), and
each caller (in `Generic/ChaCha20Xor/AArch64/`) is emitted once for each of
them. Every implementation has the contract `xorAArch64`.

A caller sets up a call's arguments (`XorArgs`): `XorImpl.call_to` gives the
effect of a call from the source (`x1`) to the destination (`x4`),
`XorImpl.call` that of `XorCallee.inPlace` (the destination set to the source
first), and `XorImpl.rel_to` and `XorImpl.rel` that they are constant time
when two runs pass the same arguments.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64

open VG VG.AArch64

/-- A verified stream backend, shared by the public stream and every AEAD caller. -/
structure XorImpl where
  callee : Impl.ChaCha20.AArch64.XorCallee
  features : List String
  ok : ∀ s, xorAArch64.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ xorAArch64.post s s'
  ct : ConstantTime isa xorAArch64.pre xorAArch64.pub callee.code
  noFrames : callee.code.noFrames = true
  /-- Whether ChaCha20-Poly1305 absorbs the data inside the eight-block kernel
  (`Impl/ChaCha20Poly1305/AArch64/Stitched.lean`), calling the backend for the
  rest, rather than calling it for all of the data. -/
  stitched : Bool
  /-- ChaCha20-Poly1305's code up to the tag is constant time (the rest,
  `sealTail` and `openTail`, does not depend on the backend); `open`'s from
  its destination (`x8`) and the destination's distance from the data
  (`x28`) too. -/
  sealTaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7])
    (Impl.ChaCha20Poly1305.AArch64.sealMainCode callee stitched) h).isSome = true
  openTaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x28])
    (Impl.ChaCha20Poly1305.AArch64.openMainCode callee stitched) h).isSome = true

/-- A call's arguments, but the destination's register (`x4`): the state at
`St`, the `n` bytes of the source at `S`, the destination at `T` and `buf` at
`B`, with the regions the callee may read and write. -/
structure XorArgs (s : State) (St S T B : Addr) (n : Nat) : Prop where
  x0 : s.gpr .x0 = St
  x1 : s.gpr .x1 = S
  x2 : s.gpr .x2 = BitVec.ofNat 64 n
  x3 : s.gpr .x3 = B
  n_lt : n < 2 ^ 64
  st_s : (⟨St, 64⟩ : Region).Disjoint ⟨S, n⟩
  st_t : (⟨St, 64⟩ : Region).Disjoint ⟨T, n⟩
  st_b : (⟨St, 64⟩ : Region).Disjoint ⟨B, 320⟩
  s_b : (⟨S, n⟩ : Region).Disjoint ⟨B, 320⟩
  t_b : (⟨T, n⟩ : Region).Disjoint ⟨B, 320⟩
  /-- In place, or apart. -/
  alias : T = S ∨ (⟨S, n⟩ : Region).Disjoint ⟨T, n⟩
  s_wrap : S.toNat + n ≤ 2 ^ 64
  t_wrap : T.toNat + n ≤ 2 ^ 64
  cov : Covers ([⟨S, n⟩] ++ [⟨St, 64⟩, ⟨T, n⟩, ⟨B, 320⟩]) (s.rd ++ s.wr)
  covw : Covers [⟨St, 64⟩, ⟨T, n⟩, ⟨B, 320⟩] s.wr

/-- The arguments of a call in place, from those of the old in-place contract. -/
theorem XorArgs.inPlace {s : State} {St S B : Addr} {n : Nat} (hx0 : s.gpr .x0 = St)
    (hx1 : s.gpr .x1 = S) (hx2 : s.gpr .x2 = BitVec.ofNat 64 n) (hx3 : s.gpr .x3 = B)
    (hn : n < 2 ^ 64) (hSD : (⟨St, 64⟩ : Region).Disjoint ⟨S, n⟩)
    (hSB : (⟨St, 64⟩ : Region).Disjoint ⟨B, 320⟩) (hDB : (⟨S, n⟩ : Region).Disjoint ⟨B, 320⟩)
    (hwrap : S.toNat + n ≤ 2 ^ 64) (hw : Covers [⟨St, 64⟩, ⟨S, n⟩, ⟨B, 320⟩] s.wr) :
    XorArgs s St S S B n :=
  ⟨hx0, hx1, hx2, hx3, hn, hSD, hSD, hSB, hDB, hDB, .inl rfl, hwrap, hwrap,
    Covers.append_left (Covers.right ((Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp).trans hw)) (Covers.right hw), hw⟩

namespace XorArgs

variable {s : State} {St S T B : Addr} {n : Nat} (h : XorArgs s St S T B n)
include h

theorem toNat_n : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h.n_lt

/-- The callee's precondition, with the destination in `x4`. -/
theorem pre (hx4 : s.gpr .x4 = T) :
    Proof.ChaCha20.xorAArch64.pre
      (s.callEntry.withRegions [⟨S, n⟩] [⟨St, 64⟩, ⟨T, n⟩, ⟨B, 320⟩]) := by
  simp only [Proof.ChaCha20.xorAArch64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.x1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.x3 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.x4 ∉ linkRegs),
    h.x0, h.x1, h.x2, h.x3, hx4, h.toNat_n]
  exact ⟨trivial, trivial, h.st_s, h.st_t, h.st_b, h.s_b, h.t_b, h.alias, h.s_wrap, h.t_wrap⟩

end XorArgs

namespace XorImpl

variable {s : State} {St S T B : Addr} {n : Nat}

/-- A call of an implementation: the source XORed with the keystream into the
destination; the memory changes only in the state, the destination and
`buf`. -/
theorem call_to (v : XorImpl) (h : XorArgs s St S T B n) (hx4 : s.gpr .x4 = T) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [⟨St, 64⟩, ⟨T, n⟩, ⟨B, 320⟩] s.mem s'.mem →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) →
      Spec.ChaCha20.bytesAt s'.mem T n =
        List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt s.mem S n)
          (Spec.ChaCha20.keystream (Spec.ChaCha20.stateAt s.mem St) n) → Q s') :
    WP isa (.call v.callee.name v.callee.code) s Q := by
  refine WP.callV (k := Proof.ChaCha20.xorAArch64) v.ok
    (rd := [⟨S, n⟩]) (wr := [⟨St, 64⟩, ⟨T, n⟩, ⟨B, 320⟩]) (h.pre hx4) h.cov h.covw ?_ v.noFrames
  intro s' hrd hwr hsp hf hcs _ hvec hpost
  refine hQ s' hrd hwr hsp hf hcs hvec ?_
  simpa only [Proof.ChaCha20.xorAArch64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.x1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.x4 ∉ linkRegs), h.x0, h.x1, h.x2, hx4, h.toNat_n] using hpost

/-- A call of an implementation in place (`XorCallee.inPlace`: the
destination, `x4`, set to the source first). -/
theorem call (v : XorImpl) (h : XorArgs s St S S B n) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [⟨St, 64⟩, ⟨S, n⟩, ⟨B, 320⟩] s.mem s'.mem →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) →
      Spec.ChaCha20.bytesAt s'.mem S n =
        List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt s.mem S n)
          (Spec.ChaCha20.keystream (Spec.ChaCha20.stateAt s.mem St) n) → Q s') :
    WP isa v.callee.inPlace s Q := by
  refine WP.seq (Xor.wp_movS fun u hu husp huv => WP.block_nil ?_)
  have hg : ∀ r, r ≠ .x4 → u.gpr r = s.gpr r := hu.other
  have h' : XorArgs u St S S B n :=
    ⟨by rw [hg _ (by decide)]; exact h.x0, by rw [hg _ (by decide)]; exact h.x1,
      by rw [hg _ (by decide)]; exact h.x2, by rw [hg _ (by decide)]; exact h.x3, h.n_lt, h.st_s,
      h.st_t, h.st_b, h.s_b, h.t_b, h.alias, h.s_wrap, h.t_wrap, by rw [hu.rd, hu.wr]; exact h.cov,
      by rw [hu.wr]; exact h.covw⟩
  refine v.call_to h' (by rw [hu.gpr]; exact h.x1) fun s' hrd hwr hsp hf hcs hvec hpost => ?_
  refine hQ s' (hrd.trans hu.rd) (hwr.trans hu.wr) (hsp.trans husp) (by rwa [hu.mem] at hf)
    (fun r hr h30 => (hcs r hr h30).trans (hg r (by intro he; subst he; simp [preserved] at hr)))
    (fun r hr => by rw [hvec r hr, huv]) (by rwa [hu.mem] at hpost)

/-- Two runs that make the call with the same arguments make it in constant time. -/
theorem rel_to (v : XorImpl) {P : State → State → Prop}
    (hP : ∀ x y, P x y → XorArgs x St S T B n ∧ x.gpr .x4 = T ∧ XorArgs y St S T B n ∧
      y.gpr .x4 = T ∧ x.sp = y.sp) :
    RelCT isa P (.call v.callee.name v.callee.code) fun _ _ => True := by
  refine RelCT.call v.ok v.ct [⟨S, n⟩] [⟨St, 64⟩, ⟨T, n⟩, ⟨B, 320⟩] fun x y hxy => ?_
  obtain ⟨hx, x4, hy, y4, hsp⟩ := hP x y hxy
  refine ⟨hx.pre x4, hy.pre y4, ?_, hx.cov, hx.covw, hy.cov, hy.covw⟩
  simp only [Proof.ChaCha20.xorAArch64, State.withRegions_gpr, State.withRegions_sp,
    State.callEntry_sp, State.callEntry_gpr x (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr x (by decide : Reg.x1 ∉ linkRegs), State.callEntry_gpr x (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr x (by decide : Reg.x3 ∉ linkRegs), State.callEntry_gpr x (by decide : Reg.x4 ∉ linkRegs),
    State.callEntry_gpr y (by decide : Reg.x0 ∉ linkRegs), State.callEntry_gpr y (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr y (by decide : Reg.x2 ∉ linkRegs), State.callEntry_gpr y (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr y (by decide : Reg.x4 ∉ linkRegs), hx.x0, hx.x1, hx.x2, hx.x3, x4, hy.x0, hy.x1,
    hy.x2, hy.x3, y4, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- `rel_to`, in place. -/
theorem rel (v : XorImpl) {P : State → State → Prop}
    (hP : ∀ x y, P x y → XorArgs x St S S B n ∧ XorArgs y St S S B n ∧ x.sp = y.sp) :
    RelCT isa P v.callee.inPlace fun _ _ => True := by
  have hmov : ∀ x, XorArgs x St S S B n → WP isa (.block [Impl.ChaCha20.AArch64.Xor.mov .x4 .x1]) x
      fun u => XorArgs u St S S B n ∧ u.gpr .x4 = S ∧ u.sp = x.sp := fun x hx =>
    Xor.wp_movS fun u hu husp _ => WP.block_nil
      ⟨⟨by rw [hu.other _ (by decide)]; exact hx.x0, by rw [hu.other _ (by decide)]; exact hx.x1,
        by rw [hu.other _ (by decide)]; exact hx.x2, by rw [hu.other _ (by decide)]; exact hx.x3,
        hx.n_lt, hx.st_s, hx.st_t, hx.st_b, hx.s_b, hx.t_b, hx.alias, hx.s_wrap, hx.t_wrap,
        by rw [hu.rd, hu.wr]; exact hx.cov, by rw [hu.wr]; exact hx.covw⟩,
        by rw [hu.gpr]; exact hx.x1, husp⟩
  have h₁ := RelCT.wpDep (P := P) (c := .block [Impl.ChaCha20.AArch64.Xor.mov .x4 .x1])
    (F := fun (x u : State) => XorArgs u St S S B n ∧ u.gpr .x4 = S ∧ u.sp = x.sp)
    (RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun x y hxy => ⟨(hP x y hxy).2.2, fun r hr => by simp at hr⟩) (by taint_decide))
    fun x y hxy => ⟨hmov x (hP x y hxy).1, hmov y (hP x y hxy).2.1⟩
  refine RelCT.seq h₁ (v.rel_to (St := St) (S := S) (T := S) (B := B) (n := n) fun x y hxy => ?_)
  obtain ⟨_, σ₁, σ₂, hσ, ⟨hx, x4, xsp⟩, ⟨hy, y4, ysp⟩⟩ := hxy
  exact ⟨hx, x4, hy, y4, by rw [xsp, ysp]; exact (hP σ₁ σ₂ hσ).2.2⟩

end XorImpl

end VG.Proof.ChaCha20.AArch64
