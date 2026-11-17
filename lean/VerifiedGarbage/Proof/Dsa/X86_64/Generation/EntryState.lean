module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
public import Mathlib.Algebra.Group.Nat.Defs
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf

/-! ### `Dsa.X86_64.Generation.FrameStore`, which this module and modules that import it used -/

section

/-! # Initialize frame words before the search scratch pointer has been stored -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

theorem frameWord_write {F : Addr} {k : Nat} (hk : k < nW) (m : Mem) (v : BitVec 64) :
    Frame [⟨F, frameBytes⟩] m (m.writeW (off F (8 * k)) v) :=
  (Frame.refl _ _).writeW (r := ⟨F, frameBytes⟩) (by simp) _
    (Offset.contains_base _ (by unfold nW frameBytes at *; omega_using [hk]) (by unfold nW frameBytes at *; omega_using [hk]))

theorem initialRep (m : Mem) (F S : Addr) :
    Rep m F S (fun i => m (off S i)) (fun k => word m F (8 * k)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.FrameDerived`, which only this module used -/

section

/-! # Initialize workspace pointers and cursors in the native generation frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

theorem frameDerived_ok {s : State} {F S B : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.gpr .rsp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr) (hbase : W 5 = B)
    {k offset : Nat} (hk : k < nW) (hd : offset < 2 ^ 31) :
    WP isa (.block [.mov .rax (.mem (sp 40)), .alu .add .rax (.imm (BitVec.ofNat 32 offset)),
      .store (sp (8 * k)) .rax]) s fun t =>
      Rep t.mem F S V (upd W k (off B offset)) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.rax] s t := by
  have hw : InRegions s.wr (off F (8 * k)) 8 :=
    ⟨_, hfr, Offset.contains_base _ (by unfold nW frameBytes at *; omega_using [hk]) (by unfold nW frameBytes at *; omega_using [hk])⟩
  have hr : InRegions (s.rd ++ s.wr) (off F 40) 8 :=
    ⟨⟨F, frameBytes⟩, List.mem_append_right _ hfr, Offset.contains_base _ (by decide) (by decide)⟩
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off F (8 * k)) (off B offset))
    (by xrun [ea_sp, hsp, hr, hw, R.slot (d := 40) (k := 5) rfl (by decide) hbase, sx_ofNat hd]) rfl)
    fun t ⟨hm, kt⟩ => ?_
  exact ⟨hm ▸ R.wf G hk _, hm ▸ frameWord_write hk s.mem _, kt⟩

theorem frameZero_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.gpr .rsp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr) {k : Nat} (hk : k < nW) :
    WP isa (.block [.mov32 .rax (.imm 0), .store (sp (8 * k)) .rax]) s fun t =>
      Rep t.mem F S V (upd W k 0) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.rax] s t := by
  have hw : InRegions s.wr (off F (8 * k)) 8 :=
    ⟨_, hfr, Offset.contains_base _ (by unfold nW frameBytes at *; omega_using [hk]) (by unfold nW frameBytes at *; omega_using [hk])⟩
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off F (8 * k)) (0 : BitVec 64))
    (by xrun [ea_sp, hsp, hw]; rfl) rfl) fun t ⟨hm, kt⟩ => ?_
  exact ⟨hm ▸ R.wf G hk _, hm ▸ frameWord_write hk s.mem _, kt⟩

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # ABI arguments and writable regions required to initialize the native search -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/FrameDerivations.lean`, which only this module imported.
section

/-! # Derive several arena pointers from the preserved scratch base -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

def derivedWords (slots : List (Nat × Nat)) (B : Addr) (W : Nat → BitVec 64) : Nat → BitVec 64 :=
  slots.foldl (fun words slot => upd words slot.1 (off B slot.2)) W

theorem frameDerivations_ok (slots : List (Nat × Nat))
    (bounds : ∀ slot ∈ slots, slot.1 < nW ∧ slot.1 ≠ 5 ∧ slot.2 < 2 ^ 31)
    {s : State} {F S B : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.gpr .rsp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr) (hbase : W 5 = B) :
    WP isa (.block (slots.flatMap fun slot => [.mov .rax (.mem (sp 40)),
      .alu .add .rax (.imm (BitVec.ofNat 32 slot.2)), .store (sp (8 * slot.1)) .rax])) s fun t =>
      Rep t.mem F S V (derivedWords slots B W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.rax] s t := by
  induction slots generalizing s W with
  | nil => exact WP.block_nil ⟨R, Frame.refl _ _, Keep.refl _ _⟩
  | cons slot slots ih =>
    change WP isa (.block (_ ++ _)) s _
    apply WP.block_append
    have bound := bounds slot (by simp)
    refine WP.mono (frameDerived_ok G R hsp hfr hbase bound.1 bound.2.2) fun u ⟨Ru, fu, ku⟩ => ?_
    refine WP.mono (ih (fun x hx => bounds x (by simp [hx])) Ru
      ((ku.gpr (by decide)).trans hsp) (by rw [ku.2.2]; exact hfr)
      (by simpa [upd, Ne.symm bound.2.1] using hbase)) fun t ⟨Rt, ft, kt⟩ => ?_
    exact ⟨Rt, fu.trans ft, (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/EntryDerived.lean`, which only this module imported.
section

/-! # Initialize the three workspace pointers and the witness cursor -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def workspaceSlots : List (Nat × Nat) := [(3, wrappedSeed), (4, hashes), (14, VG.Impl.Dsa.Generation.Layout.hash)]

def workspaceWords (B : Addr) (W : Nat → BitVec 64) : Nat → BitVec 64 :=
  upd (derivedWords workspaceSlots B W) 16 0

theorem entryDerived_ok {s : State} {F S B : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.gpr .rsp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr) (hbase : W 5 = B) :
    WP isa (.block Impl.Dsa.X86_64.Generation.entryDerived) s fun t =>
      Rep t.mem F S V (workspaceWords B W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.rax] s t := by
  unfold Impl.Dsa.X86_64.Generation.entryDerived
  apply WP.block_append
  refine WP.mono (frameDerivations_ok workspaceSlots (by
    intro slot hs
    simp only [workspaceSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> decide) G R hsp hfr hbase) fun u ⟨Ru, fu, ku⟩ => ?_
  refine WP.mono (frameZero_ok G Ru ((ku.gpr (by decide)).trans hsp)
    (by rw [ku.2.2]; exact hfr) (by decide : 16 < nW)) fun t ⟨Rt, ft, kt⟩ => ?_
  exact ⟨Rt, fu.trans ft, (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
end

end
