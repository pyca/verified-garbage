module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Call
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Entry
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.ZeroBuffer
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-! # The search's leaves (ARMv7): its terminal states, and zeros at `out` -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Search
open VG.Spec.RsaKeyGen (primeSearch primeEntropy PrimeSearchResult)

/-- Through code that keeps `r4`–`r7`, the regions and the stack pointer,
and writes only within `rs`, which the search may write and which are apart
from its saved registers. -/
theorem SearchBase.step {p : SearchPublic} {o s t : State} (h : SearchBase p o s) {ws : List Reg}
    (k : Rest ws s t) (hws : ∀ r ∈ [Reg.r4, .r5, .r6, .r7], r ∉ ws := by decide) {rs : List Region}
    (hf : Frame rs s.mem t.mem) (hsub : ∀ r ∈ rs, ∃ q ∈ changes o, Region.Sub r q)
    (happ : ∀ r ∈ rs, Region.Disjoint ⟨State.addr p.S1 + BitVec.ofNat 64 0, 40 - 0⟩ r) : SearchBase p o t :=
  ⟨h.input, k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp,
    (k.gpr .r4 (hws _ (by simp))).trans h.r4, (k.gpr .r5 (hws _ (by simp))).trans h.r5,
    (k.gpr .r6 (hws _ (by simp))).trans h.r6, (k.gpr .r7 (hws _ (by simp))).trans h.r7,
    Spill.Saved.frame h.saved (lo := 0) (hi := 40) (by decide) hf happ, h.frame.trans (hf.sub hsub)⟩

theorem SearchBase.keep {p : SearchPublic} {o s t : State} (h : SearchBase p o s) {ws : List Reg}
    (k : Rest ws s t) (hm : t.mem = s.mem) (hws : ∀ r ∈ [Reg.r4, .r5, .r6, .r7], r ∉ ws := by decide) :
    SearchBase p o t :=
  h.step k hws (rs := []) (by rw [hm]; exact Frame.refl _ _) (fun _ h => nomatch h) (fun _ h => nomatch h)

/-- `out` is a region the search may write, apart from its saved registers. -/
theorem out_changes {p : SearchPublic} {o : State} (h : SearchInput p o) :
    ∀ r ∈ [rO p], ∃ q ∈ changes o, Region.Sub r q := by
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨inOut o, by simp [changes, inWrites], by rw [h.regions.1]; exact fun _ h => h⟩

theorem out_apart {p : SearchPublic} {o : State} (h : SearchInput p o) :
    ∀ r ∈ [rO p], Region.Disjoint ⟨State.addr p.S1 + BitVec.ofNat 64 0, 40 - 0⟩ r := by
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact saved_apart h (k := 0) (by decide) _ (by simp [callWr])

/-! ## Zeros at `out` -/

theorem zeroOut_ok {p : SearchPublic} {o s : State} (h : SearchBase p o s) :
    WP isa zeroOut s fun t =>
      (Spec.Rsa.bytesAt t.mem (State.addr p.op) p.len = List.replicate p.len 0 ∧
        Frame [rO p] s.mem t.mem) ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  have hi := h.input
  have f := hi.facts
  have hl := f.valid
  unfold Spec.RsaKeyGen.primeLenValid at hl
  unfold zeroOut
  refine WP.seq (WP.mono (withRest_all (c := .block [.mov .r0 (.reg .r4), .mov .lr (.reg .r5), .mov .r2 (.imm 0)])
    [.r0, .r2, .lr] (Q := fun t => t.gpr .r0 = p.op ∧ t.gpr .lr = BitVec.ofNat 32 p.len ∧ t.gpr .r2 = 0 ∧
      t.mem = s.mem) (by ffrun [h.r4, h.r5]) (by rfl) (by rfl)) fun u ⟨⟨h0, hlr, h2, hm⟩, k⟩ => ?_)
  have write : InRegions u.wr (State.addr p.op) p.len := by
    refine ⟨rO p, ?_, by
      simpa using Offset.contains_base (State.addr p.op) (d := 0) (n := p.len) (k := p.len) (by omega) (by decide)⟩
    rw [k.wr, h.wr, hi.wr, ← hi.regions.1]; simp [inWrites]
  refine WP.mono (VG.Proof.Ffdh.Arm.zeroBuffer_ok false u (src := u.gpr .r1) (by omega) (by omega) f.nO write h2
    rfl h0 hlr) fun t ⟨hz, _, _, hf, kt⟩ => ⟨⟨hz, by rw [← hm]; exact hf⟩, (k.mono (by decide)).trans (kt.mono (by decide))⟩

end VG.Proof.RsaKeyGen.Arm.Search
