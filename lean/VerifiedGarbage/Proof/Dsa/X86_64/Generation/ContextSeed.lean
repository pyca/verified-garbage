module

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedSearch
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Dsa.X86_64.Generation.SeedArguments`, which this module and modules that import it used -/

section

/-! # Bind each complete seed to q hashing without resetting witness consumption -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def seedWords (W : Nat → BitVec 64) (len : Nat) : Nat → BitVec 64 :=
  upd (upd (upd W 0 (off (W 5) q)) 27 (W 1)) 28 (BitVec.ofNat 64 len)

theorem seedArguments_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {len : Nat} (hl : len < 2 ^ 32) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.seedArguments len)) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (seedWords W len) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.rax] s t := by
  have cast : (BitVec.ofNat 32 len).setWidth 64 = BitVec.ofNat 64 len := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl]
  have read : (s.mem.writeW (off F 0) (off (W 5) q)).readW (off F 8) 64 = W 1 := by
    exact (R.wf L.geo (by decide : 0 < nW) _).slot (d := 8) (k := 1) rfl (by decide) (by simp [upd])
  have st0 : InRegions s.wr F 8 := by simpa [off] using L.st (d := 0) (by decide)
  have read0 : (s.mem.writeW F (off (W 5) q)).readW (off F 8) 64 = W 1 := by simpa [off] using read
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = ((s.mem.writeW (off F 0) (off (W 5) q)).writeW (off F 216) (W 1)).writeW
        (off F 224) (BitVec.ofNat 64 len)) (by
    xrun [Impl.Dsa.X86_64.Generation.seedArguments, ea_sp, L.rsp,
      L.ld (d := 40) (by decide), R.slot (d := 40) (k := 5) rfl (by decide) rfl,
      L.ld (d := 8) (by decide), st0, L.st (d := 216) (by decide),
      L.st (d := 224) (by decide), sx_ofNat (by decide : q < 2 ^ 31), cast, read0]) rfl)
    fun t ⟨hm, kt⟩ => ?_
  have Rt : Rep t.mem F S V (seedWords W len) := by
    rw [hm]
    exact ((R.wf L.geo (by decide : 0 < nW) _).wf L.geo (by decide : 27 < nW) _).wf L.geo (by decide : 28 < nW) _
  refine ⟨lay_of_rep L R Rt (by simp [seedWords, upd]) (kt.gpr (by decide)) kt.2.2, Rt, ?_, kt⟩
  have ff : Outside F 0 frameBytes s.mem t.mem := by
    rw [hm]
    exact (((writeW_outside _ F _ (d := 0) (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ F _ (d := 216) (by decide)).mono (by decide) (by decide))).trans
      ((writeW_outside _ F _ (d := 224) (by decide)).mono (by decide) (by decide))
  intro a ha
  apply ff a
  right
  have hn := ha ⟨F, frameBytes⟩ (by simp)
  change ¬ ofs F a < frameBytes at hn
  omega_using [hn]

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Prepare q hashing while retaining all persistent search inputs -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem prepareSeed_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.seedArguments p.geo.qLen)) s fun t =>
      GenerationMemory p (seedWords W p.geo.qLen) t ∧ Frame p.changed s.mem t.mem ∧ Keep [.rax] s t := by
  obtain ⟨V, R⟩ := h.rep
  refine WP.mono (seedArguments_ok h.layout R (by rcases p.geo.qWidth with hh | hh <;> omega_using [hh]))
    fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  have ff := GenerationContext.frame_single (p := p) ft
  refine ⟨h.frame Lt ⟨V, Rt⟩ ?_ ff kt.2.1 kt.2.2, ff, kt⟩
  intro k hk
  simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rfl
    | simpa [seedWords, upd] using ((h.slots 28 (by simp [generationSlots])).trans p.hashLenSlot).symm

end VG.Proof.Dsa.X86_64.Generation
