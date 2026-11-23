module

public import VerifiedGarbage.Proof.Sha3.AArch64.Variant
public import VerifiedGarbage.Impl.Sha3.AArch64.ViaD8
import VerifiedGarbage.Proof.Sha3.AArch64.Call
import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Steps

-- separate module: the bodies that call the permutation by `d8` need it without `Entry.lean`'s callWipe framework

/-!
# SHA-3 on AArch64: calling the permutation by the address in `d8`

`callD8_ok` is `call_ok` for `Callee.viaD8`: where `d8` holds the
permutation's address, the indirect call runs as its call, from the state
with that address in `x16`, which no register the calling convention
preserves is.
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64

open VG VG.AArch64 VG.Impl.Sha3.AArch64
open VG.Spec.Sha3 (stateAt keccakF)

/-- `d8` holds the address of the function `n`. -/
def D8 (n : String) (s : State) : Prop := (s.v .v8).extractLsb' 0 64 = s.syms n

/-- `d8` holds `n`'s address in a later state that keeps the low halves of
the preserved vector registers and the addresses of statics. -/
theorem D8.of {n : String} {s t : State} (h : D8 n s)
    (hv : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64)
    (hy : t.syms = s.syms) : D8 n t := by
  unfold D8 at h ⊢; rw [hv .v8 (by decide), hy]; exact h

/-- The contract `k` of code that calls the function `n` by the address in
`d8`: from states where `d8` holds it, and for runs that agree on it. -/
def Contract.d8 (n : String) (k : Contract isa) : Contract isa :=
  ⟨fun s => k.pre s ∧ D8 n s, k.post, fun s t => k.pub s t ∧ s.syms n = t.syms n⟩

/-- A state where `d8` holds `n`'s address: `s` with it in `v8`. -/
theorem D8.setV (n : String) (s : State) : D8 n (s.setV .v8 ((s.syms n).setWidth 128)) := by
  unfold D8
  rw [RegUpd.v_setV_self]
  change ((s.syms n).setWidth 128).extractLsb' 0 64 = s.syms n
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb', BitVec.toNat_setWidth]
  omega

/-- `Contract.d8` is satisfiable where `k` is, in a state with `n`'s address in `d8`. -/
theorem Contract.d8_sat {n : String} {k : Contract isa} {s : State}
    (h : k.pre (s.setV .v8 ((s.syms n).setWidth 128))) : ∃ s, (Contract.d8 n k).pre s :=
  ⟨_, h, D8.setV n s⟩

theorem callD8_ok (v : Permutation) {s : State} {st scr : Addr} (h0 : s.gpr .x0 = st)
    (h1 : s.gpr .x1 = scr) (hd : D8 v.callee.name s)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨scr, 512⟩)
    (hw : Covers [⟨st, 200⟩, ⟨scr, 512⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) →
      Frame [⟨st, 200⟩, ⟨scr, 512⟩] s.mem s'.mem →
      stateAt s'.mem st = keccakF (stateAt s.mem st) → Q s') :
    WP isa v.callee.viaD8 s Q := by
  unfold Callee.viaD8
  refine WP.seq (WP.cons (exec_umov (s := s) (r := .x16) (v := .v8) (by decide)) (WP.block_nil ?_))
  generalize hs' : s.write .x .x16 (laneOf s .v8 0) = s'
  have e : s'.gpr .x16 = s.syms v.callee.name := by
    rw [← hs', RegUpd.gpr_write_self]; exact hd
  have hy : s'.syms = s.syms := by rw [← hs']; rfl
  have hg : ∀ r, r ≠ .x16 → s'.gpr r = s.gpr r := fun r hr => by
    rw [← hs']; exact RegUpd.gpr_write_of_ne _ _ _ hr
  refine WP.icalls_of_call (M := isa) (s := s') (a := s.syms v.callee.name) (n := v.callee.name)
    (c := v.callee.code) (by show some (s'.gpr .x16) = _; rw [e])
    (by simp [icallTarget, isa, hy]) ?_
  refine call_ok v (by rw [hg _ (by decide)]; exact h0) (by rw [hg _ (by decide)]; exact h1) d₁
    (by rw [← hs']; exact hw) fun t rd wr sp cs vc fr eq => ?_
  have hm : s'.mem = s.mem := by rw [← hs']; rfl
  have hv : s'.v = s.v := by rw [← hs']; rfl
  refine hQ t (by rw [rd, ← hs']; rfl) (by rw [wr, ← hs']; rfl) (by rw [sp, ← hs']; rfl)
    (fun r hr h30 => ?_) (by rw [← hv]; exact vc) (by rw [← hm]; exact fr) (by rw [eq, hm])
  rw [cs r hr h30, hg r (fun h => by subst h; exact absurd hr (by decide))]

end VG.Proof.Sha3.AArch64
