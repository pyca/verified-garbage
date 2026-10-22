module

public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.Steps
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Weave
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ok
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Interleave
public import VerifiedGarbage.Proof.Framework.AArch64.InterleaveFootprints
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import all Init.Data.Nat.Bitwise.Basic

/-!
# AES-GCM-SIV on AArch64, eight blocks at a time: the loops

Untrusted: everything here is checked by Lean. From a context `σ` meeting
`KPre`:

* `ghLoop_ok`: `ghLoop` leaves in `Y` GHASH of the `8 nb` blocks of the data
  (as numbers, POLYVAL's blocks) from the `Y` it starts from, and writes no
  memory;
* `ctrLoop_ok`: `ctrLoop nr` XORs the data with the keystream (`DataInv`);
* `openLoop_ok`: `openLoop nr` does both, GHASH of the data as XORed
  (`blockC`, the blocks of `mDec`): batch `i + 1` XORed while batch `i` is
  hashed, woven (`parts_ok`, the parts independent, checked once).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.AArch64.Stitch

open VG VG.AArch64
open VG.AArch64.RegUpd (v_setV_self v_setV_of_ne gpr_setV mem_setV rd_setV wr_setV sp_setV v_write
  gpr_write gpr_write_self gpr_write_of_ne mem_write rd_write wr_write sp_write)
open VG.Proof.Aes.AArch64 (DataInv)
open VG.Proof.Aes.AArch64.Aese (Fr vbyte_readW inRegions_wr exec_strq eval_zero eval_nonzero)
open VG.Proof.Gcm.AArch64.Pmull (ext8 VOnly)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok fuse_flatten flatten_singles ghV)
open VG.Spec.Gcm (Block ghashFrom)
open VG.Impl.AesGcmSiv.AArch64.Stitch
open VG.Impl.Gcm.AArch64.Stitch (breg Y C stores byRounds)

/-! ## The data XORed with the keystream -/

namespace Ctx
variable (σ : Ctx)

/-- The memory with the data XORed with the keystream. -/
def mDec : Mem := fun a =>
  σ.m₀ a ^^^ (if (a - σ.D).toNat < 16 * (8 * σ.nb) then σ.ks (a - σ.D).toNat else 0)

/-- Block `i` of the data XORed, as a number. -/
abbrev blockC (i : Nat) : Block := σ.mDec.readW (σ.D + BitVec.ofNat 64 (16 * i)) 128

end Ctx

theorem readW_of_dataInv {σ : Ctx} (hn : 128 * σ.nb < 2 ^ 64) {m : Mem} {k : Nat}
    (h : DataInv σ.m₀ m σ.D (8 * σ.nb) k σ.ks) {i : Nat} (hi : i < k) (hk : k ≤ 8 * σ.nb) :
    m.readW (σ.D + BitVec.ofNat 64 (16 * i)) 128 = σ.blockC i := by
  refine Mem.readW_congr fun t ht => ?_
  rw [Offset.add_add, h _ (by omega), ite_eq_left (by omega), Ctx.mDec, Offset.add_sub_cancel_left,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ite_eq_left (by omega)]

theorem readW_of_dataInv' {σ : Ctx} {m : Mem} {k : Nat}
    (h : DataInv σ.m₀ m σ.D (8 * σ.nb) k σ.ks) {i : Nat} (hi : k ≤ i) (hn' : i < 8 * σ.nb) :
    m.readW (σ.D + BitVec.ofNat 64 (16 * i)) 128 = σ.blockO i := by
  refine Mem.readW_congr fun t ht => ?_
  rw [Offset.add_add, h _ (by omega), ite_eq_right (by omega)]
  exact BitVec.xor_zero

/-! ## The number of rounds -/

theorem byRounds_ok {nr : Nat} (hR : nr = 10 ∨ nr = 12 ∨ nr = 14) {f : Nat → Prog isa} {P Q : State → Prop}
    {s : State} (hx22 : s.gpr .x22 = BitVec.ofNat 64 nr)
    (hst : ∀ s', (∀ r, r ≠ .x13 → r ≠ .x14 → s'.gpr r = s.gpr r) → s'.v = s.v → s'.mem = s.mem →
      s'.sp = s.sp → s'.rd = s.rd → s'.wr = s.wr → P s')
    (hf : ∀ s, P s → WP isa (f nr) s Q) :
    WP isa (byRounds f) s Q := by
  rw [byRounds, WP.seq_iff, WP.block_cons_iff]
  refine ⟨_, exec_subImm_x (imm := 10) (by decide), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_subImm_x (imm := 12) (by decide), WP.block_nil ?_⟩
  have hP' := hst ((s.write .x .x13 (s.read .x .x22 - BitVec.ofNat 64 10)).write .x .x14
      ((s.write .x .x13 (s.read .x .x22 - BitVec.ofNat 64 10)).read .x .x22 - BitVec.ofNat 64 12))
    (fun r h13 h14 => by rw [gpr_write_of_ne _ _ _ h14, gpr_write_of_ne _ _ _ h13]) rfl rfl rfl rfl rfl
  have e13 : ((s.write .x .x13 (s.read .x .x22 - BitVec.ofNat 64 10)).write .x .x14
      ((s.write .x .x13 (s.read .x .x22 - BitVec.ofNat 64 10)).read .x .x22 - BitVec.ofNat 64 12)).gpr .x13 =
      BitVec.ofNat 64 (nr - 10) := by
    simp only [gpr_write_of_ne _ _ _ (show Reg.x13 ≠ Reg.x14 by decide), gpr_write_self, State.read,
      BitVec.setWidth_eq, hx22, Size.bits]
    rw [Offset.ofNat_sub_ofNat (by omega)]
  refine WP.ite _ (eval_zero e13 (by omega)) (fun h => ?_) (fun h => ?_)
  · have h10 : nr = 10 := by simp only [decide_eq_true_eq] at h; omega
    have e := hf _ hP'
    rw [h10] at e; exact e
  · have hge : 12 ≤ nr := by simp only [decide_eq_false_iff_not] at h; omega
    have e14 : ((s.write .x .x13 (s.read .x .x22 - BitVec.ofNat 64 10)).write .x .x14
        ((s.write .x .x13 (s.read .x .x22 - BitVec.ofNat 64 10)).read .x .x22 - BitVec.ofNat 64 12)).gpr .x14 =
        BitVec.ofNat 64 (nr - 12) := by
      simp only [gpr_write_self, State.read, BitVec.setWidth_eq,
        gpr_write_of_ne _ _ _ (show Reg.x22 ≠ Reg.x13 by decide), hx22, Size.bits]
      rw [Offset.ofNat_sub_ofNat (by omega)]
    refine WP.ite _ (eval_zero e14 (by omega)) (fun h' => ?_) (fun h' => ?_)
    · have h12 : nr = 12 := by simp only [decide_eq_true_eq] at h'; omega
      have e := hf _ hP'
      rw [h12] at e; exact e
    · have h14 : nr = 14 := by simp only [decide_eq_false_iff_not] at h'; omega
      have e := hf _ hP'
      rw [h14] at e; exact e

/-! ## POLYVAL of the batches -/

/-- After `h` batches hashed, from `s₀`. -/
structure GInv (σ : Ctx) (y : Block) (s₀ : State) (h : Nat) (s : State) : Prop where
  le : h ≤ σ.nb
  x9 : s.gpr .x9 = σ.D + BitVec.ofNat 64 (128 * h)
  x11 : s.gpr .x11 = BitVec.ofNat 64 (σ.nb - h)
  gpr : ∀ r, r ≠ .x9 → r ≠ .x11 → s.gpr r = s₀.gpr r
  y : s.v Y = ext8 (yh σ.H y σ.blockO (8 * h)) (yh σ.H y σ.blockO (8 * h))
  cr : s.v C = ofVDwords Impl.Gcm.AArch64.Pmull.poly Impl.Gcm.AArch64.Pmull.poly
  mem : s.mem = σ.m₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem ghLoop_ok {σ : Ctx} (hp : KPre σ) (gh : Gh8Ok) {y : Block} {s₀ : State}
    (hx19 : s₀.gpr .x19 = σ.W) (hrdwr : s₀.rd ++ s₀.wr = σ.rd ++ σ.wr) (hI : GInv σ y s₀ 0 s₀) :
    WP isa ghLoop s₀ (GInv σ y s₀ σ.nb) := by
  have hn := hp.n16
  have h1 := hp.nb1
  let I : Nat → State → Prop := fun m s => ∃ h, m = σ.nb - h ∧ h < σ.nb ∧ GInv σ y s₀ h s
  have hstep : ∀ m s, I m s → WP isa (.block (ghPart ++ adv)) s (fun s' =>
      (AArch64.eval (.nonzero .x .x11) s' = some false ∧ GInv σ y s₀ σ.nb s') ∨
      (AArch64.eval (.nonzero .x .x11) s' = some true ∧ ∃ m' < m, I m' s')) := by
    rintro m s ⟨h, rfl, hh, hI⟩
    rw [WP.block_append_iff]
    refine WP.mono (ghStep hp gh (y := y) (hb := σ.blockO) (h := h) hI.y hI.cr hI.x9 hh
      (by rw [hI.gpr _ (by decide) (by decide), hx19]) (by rw [hI.rd, hI.wr, hrdwr])
      (by rw [hI.mem]; exact Frame.refl _ _) (fun j hj => by rw [hI.mem])) fun u ⟨hy, ou⟩ => ?_
    refine WP.mono (adv_ok (D := σ.D) (h := h) hh (by rw [ou.gpr, hI.x9]) (by rw [ou.gpr, hI.x11]))
      fun u' ⟨x9', x11', g', v', m', sp', rd', wr'⟩ => ?_
    have hI' : GInv σ y s₀ (h + 1) u' := {
      le := by omega
      x9 := x9'
      x11 := by rw [x11', show σ.nb - (h + 1) = σ.nb - (h + 1) from rfl]
      gpr := fun r h9 h11 => by rw [g' r h9 h11, ou.gpr, hI.gpr r h9 h11]
      y := by rw [v', hy]
      cr := by rw [v', ou.v C (by decide), hI.cr]
      mem := by rw [m', ou.mem, hI.mem]
      sp := by rw [sp', ou.sp, hI.sp]
      rd := by rw [rd', ou.rd, hI.rd]
      wr := by rw [wr', ou.wr, hI.wr] }
    rw [eval_nonzero hI'.x11 (by omega)]
    by_cases hl : σ.nb - (h + 1) = 0
    · have e : h + 1 = σ.nb := by omega
      exact .inl ⟨by simp [hl], by rw [← e]; exact hI'⟩
    · exact .inr ⟨by simp [hl], σ.nb - (h + 1), by omega, h + 1, rfl, by omega, hI'⟩
  exact WP.loop (M := isa) I hstep _ _ ⟨0, rfl, by omega, hI⟩

/-! ## Counter mode of the batches -/

/-- The registers the counter-mode loops write. -/
abbrev kRegs : List Reg := [.x9, .x10, .x11, .x12, .x13, .x14]

/-- After `c` batches XORed, from `s₀`, with `x9` at batch `p`. -/
structure CInv (σ : Ctx) (s₀ : State) (c p : Nat) (s : State) : Prop where
  le : c ≤ σ.nb
  x9 : s.gpr .x9 = σ.D + BitVec.ofNat 64 (128 * p)
  x10 : s.read .w .x10 = σ.c0 + BitVec.ofNat 32 (8 * c)
  x11 : s.gpr .x11 = BitVec.ofNat 64 (σ.nb - c)
  gpr : ∀ r, r ∉ kRegs → s.gpr r = s₀.gpr r
  data : DataInv σ.m₀ s.mem σ.D (8 * σ.nb) (8 * c) σ.ks
  frame : Frame [σ.dR] σ.m₀ s.mem
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem CInv.of_x1314 {σ : Ctx} {s₀ : State} {c p : Nat} {s s' : State} (hI : CInv σ s₀ c p s)
    (hg : ∀ r, r ≠ .x13 → r ≠ .x14 → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem)
    (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : CInv σ s₀ c p s' where
  le := hI.le
  x9 := by rw [hg _ (by decide) (by decide), hI.x9]
  x10 := by simp only [State.read]; rw [hg _ (by decide) (by decide)]; exact hI.x10
  x11 := by rw [hg _ (by decide) (by decide), hI.x11]
  gpr r hr := by rw [hg r (fun h => hr (by simp [h])) (fun h => hr (by simp [h])), hI.gpr r hr]
  data := by rw [hm]; exact hI.data
  frame := by rw [hm]; exact hI.frame
  sp := by rw [hsp, hI.sp]
  rd := by rw [hrd, hI.rd]
  wr := by rw [hwr, hI.wr]

theorem ctrLoop_ok {σ : Ctx} (hp : KPre σ) {s₀ : State}
    (hx19 : s₀.gpr .x19 = σ.W) (hx15 : s₀.gpr .x15 = σ.K) (hrdwr : s₀.rd ++ s₀.wr = σ.rd ++ σ.wr)
    (hwr : s₀.wr = σ.wr) {s : State} (hI : CInv σ s₀ 0 0 s) :
    WP isa (ctrLoop σ.nr) s (CInv σ s₀ σ.nb σ.nb) := by
  have hn := hp.n16
  have h1 := hp.nb1
  let I : Nat → State → Prop := fun m s => ∃ c, m = σ.nb - c ∧ c < σ.nb ∧ CInv σ s₀ c c s
  have hstep : ∀ m s, I m s → WP isa (.block (aesPart σ.nr 0 ++ stores 0 ++ adv)) s (fun s' =>
      (AArch64.eval (.nonzero .x .x11) s' = some false ∧ CInv σ s₀ σ.nb σ.nb s') ∨
      (AArch64.eval (.nonzero .x .x11) s' = some true ∧ ∃ m' < m, I m' s')) := by
    rintro m s ⟨c, rfl, hc, hI⟩
    rw [List.append_assoc, WP.block_append_iff]
    have hx9 : ∀ j, s.gpr .x9 + BitVec.ofNat 64 (0 + 16 * j) = σ.D + BitVec.ofNat 64 (16 * (8 * c + j)) :=
      fun j => by rw [hI.x9, Offset.add_add_eq _ (show 128 * c + (0 + 16 * j) = 16 * (8 * c + j) by omega)]
    refine WP.mono (aesStep hp hc (by decide) (by decide) hx9 hI.x10 (by rw [hI.gpr _ (by decide), hx19])
      (by rw [hI.gpr _ (by decide), hx15]) (by rw [hI.rd, hI.wr, hrdwr]) hI.frame hI.data)
      fun t ⟨hv, x10t, frt⟩ => ?_
    have gt : ∀ r, r ≠ .x10 → r ≠ .x12 → t.gpr r = s.gpr r := fun r h1 h2 => frt.gpr r (by simp [h1, h2])
    rw [WP.block_append_iff]
    refine WP.mono (stores_ok hp hc (by decide) (by decide) t
      (by rw [gt _ (by decide) (by decide), hI.x9, BitVec.add_zero]) (by rw [frt.mem]; exact hI.data)
      (by rw [frt.wr, hI.wr, hwr]) hv) fun u ⟨d₁, f₁, g₁, v₁, sp₁, rd₁, wr₁⟩ => ?_
    refine WP.mono (adv_ok (D := σ.D) (h := c) hc (by rw [g₁, gt _ (by decide) (by decide), hI.x9])
      (by rw [g₁, gt _ (by decide) (by decide), hI.x11])) fun u' ⟨x9', x11', g', v', m', sp', rd', wr'⟩ => ?_
    have gall : ∀ r, r ≠ .x9 → r ≠ .x11 → u'.gpr r = t.gpr r := fun r h9 h11 => by rw [g' r h9 h11, g₁]
    have hI' : CInv σ s₀ (c + 1) (c + 1) u' := {
      le := by omega
      x9 := x9'
      x10 := by
        simp only [State.read] at x10t ⊢
        rw [gall _ (by decide) (by decide)]; exact x10t
      x11 := x11'
      gpr := fun r hr => by
        simp only [kRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [gall r hr.1 hr.2.2.1, gt r hr.2.1 hr.2.2.2.1, hI.gpr r (by simp [kRegs, hr.1, hr.2.1, hr.2.2.1,
          hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])]
      data := by rw [m']; exact d₁
      frame := by
        rw [m']
        have : s.mem = t.mem := frt.mem.symm
        exact hI.frame.trans (this ▸ f₁)
      sp := by rw [sp', sp₁, frt.sp, hI.sp]
      rd := by rw [rd', rd₁, frt.rd, hI.rd]
      wr := by rw [wr', wr₁, frt.wr, hI.wr] }
    rw [eval_nonzero hI'.x11 (by omega)]
    by_cases hl : σ.nb - (c + 1) = 0
    · have e : c + 1 = σ.nb := by omega
      exact .inl ⟨by simp [hl], by rw [← e]; exact hI'⟩
    · exact .inr ⟨by simp [hl], σ.nb - (c + 1), by omega, c + 1, rfl, by omega, hI'⟩
  exact WP.loop (M := isa) I hstep _ _ ⟨0, rfl, by omega, hI⟩

/-! ## `open`'s loop -/

/-- The footprints of the parts' code; neither stores, so the base register
does not matter. -/
abbrev fps : VG.Interleave.Footprints isa := VG.AArch64.Interleave.footprints .x0

theorem parts_check : ∀ nr ∈ [10, 12, 14],
    ((fps.blockFp (aesPart nr 128)).bind fun A => (fps.blockFp ghPart).map fun B => fps.indep A B) = some true := by
  decide +kernel

/-- The parts, woven, run as `aesPart` and then `ghPart`. -/
theorem parts_ok {nr : Nat} (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) {s : State}
    {Q : State → Prop} (h : WP isa (.block (aesPart nr 128)) s fun t => WP isa (.block ghPart) t Q) :
    WP isa (.block (parts nr 128)) s Q := by
  unfold parts
  refine VG.Interleave.WP.weaveG (P := fps.Inv) ?_ trivial ?_
  · rw [fuse_flatten, flatten_singles]
    exact fps.indeps_of_check (parts_check nr (by rcases hnr with rfl | rfl | rfl <;> decide))
  · rw [fuse_flatten, flatten_singles]; exact h

/-- After `c` batches XORed and `h` hashed, from `s₀`: `x9` at batch `h`. -/
structure OInv (σ : Ctx) (y : Block) (s₀ : State) (c h : Nat) (s : State) : Prop where
  ci : CInv σ s₀ c h s
  y : s.v Y = ext8 (yh σ.H y σ.blockC (8 * h)) (yh σ.H y σ.blockC (8 * h))
  cr : s.v C = ofVDwords Impl.Gcm.AArch64.Pmull.poly Impl.Gcm.AArch64.Pmull.poly

section
variable {σ : Ctx} (hp : KPre σ) (gh : Gh8Ok) {y : Block} {s₀ : State}
    (hx19 : s₀.gpr .x19 = σ.W) (hx15 : s₀.gpr .x15 = σ.K) (hrdwr : s₀.rd ++ s₀.wr = σ.rd ++ σ.wr)
    (hwr : s₀.wr = σ.wr)
include hp gh hx19 hx15 hrdwr hwr

/-- One iteration of `open`'s loop: batch `h + 1` XORed while batch `h` is
hashed, then stored. -/
theorem openBody_ok {h : Nat} (hh : h + 1 < σ.nb) {s : State} (hI : OInv σ y s₀ (h + 1) h s) :
    WP isa (.block (parts σ.nr 128 ++ stores 128 ++ adv)) s (OInv σ y s₀ (h + 2) (h + 1)) := by
  have hn := hp.n16
  have hct : ∀ j < 8, s.mem.readW (σ.D + BitVec.ofNat 64 (16 * (8 * h + j))) 128 = σ.blockC (8 * h + j) :=
    fun j hj => readW_of_dataInv hn hI.ci.data (by omega) (by have := hI.ci.le; omega)
  rw [List.append_assoc, WP.block_append_iff]
  refine parts_ok hp.rounds ?_
  have hx9 : ∀ j, s.gpr .x9 + BitVec.ofNat 64 (128 + 16 * j) = σ.D + BitVec.ofNat 64 (16 * (8 * (h + 1) + j)) :=
    fun j => by rw [hI.ci.x9, Offset.add_add_eq _ (show 128 * h + (128 + 16 * j) = 16 * (8 * (h + 1) + j) by omega)]
  refine WP.mono (aesStep hp hh (by decide) (by decide) hx9 hI.ci.x10 (by rw [hI.ci.gpr _ (by decide), hx19])
    (by rw [hI.ci.gpr _ (by decide), hx15]) (by rw [hI.ci.rd, hI.ci.wr, hrdwr]) hI.ci.frame hI.ci.data)
    fun t ⟨hv, x10t, frt⟩ => ?_
  have gt : ∀ r, r ≠ .x10 → r ≠ .x12 → t.gpr r = s.gpr r := fun r h1 h2 => frt.gpr r (by simp [h1, h2])
  refine WP.mono (ghStep hp gh (y := y) (hb := σ.blockC) (h := h) (t := t) (by rw [frt.v _ (by decide), hI.y])
    (by rw [frt.v _ (by decide), hI.cr]) (by rw [gt _ (by decide) (by decide), hI.ci.x9]) (by omega)
    (by rw [gt _ (by decide) (by decide), hI.ci.gpr _ (by decide), hx19])
    (by rw [frt.rd, frt.wr, hI.ci.rd, hI.ci.wr, hrdwr]) (by rw [frt.mem]; exact hI.ci.frame)
    (fun j hj => by rw [frt.mem]; exact hct j hj)) fun u ⟨hy, ou⟩ => ?_
  rw [WP.block_append_iff]
  have gu : ∀ r, r ≠ .x10 → r ≠ .x12 → u.gpr r = s.gpr r := fun r h1 h2 => by rw [ou.gpr, gt r h1 h2]
  refine WP.mono (stores_ok hp hh (by decide) (by decide) u (by rw [gu _ (by decide) (by decide), hI.ci.x9,
      Offset.add_add_eq _ (show 128 * h + 128 = 128 * (h + 1) by omega)]) (by rw [ou.mem, frt.mem]; exact hI.ci.data)
    (by rw [ou.wr, frt.wr, hI.ci.wr, hwr])
    (fun j hj tt htt => by rw [ou.v _ (by unfold breg; split <;> decide)]; exact hv j hj tt htt))
    fun u₁ ⟨d₁, f₁, g₁, v₁, sp₁, rd₁, wr₁⟩ => ?_
  refine WP.mono (adv_ok (D := σ.D) (h := h) (c := h + 1) hh (by rw [g₁, gu _ (by decide) (by decide), hI.ci.x9])
    (by rw [g₁, gu _ (by decide) (by decide), hI.ci.x11])) fun u' ⟨x9', x11', g', v', m', sp', rd', wr'⟩ => ?_
  have gall : ∀ r, r ≠ .x9 → r ≠ .x11 → u'.gpr r = u.gpr r := fun r h9 h11 => by rw [g' r h9 h11, g₁]
  refine ⟨⟨by omega, x9', ?_, by rw [x11'], fun r hr => ?_, by rw [m']; exact d₁, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [State.read] at x10t ⊢
    rw [gall _ (by decide) (by decide), ou.gpr]; exact x10t
  · simp only [kRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gall r hr.1 hr.2.2.1, gu r hr.2.1 hr.2.2.2.1, hI.ci.gpr r (by simp [kRegs, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])]
  · rw [m']
    have : s.mem = u.mem := by rw [ou.mem, frt.mem]
    exact hI.ci.frame.trans (this ▸ f₁)
  · rw [sp', sp₁, ou.sp, frt.sp, hI.ci.sp]
  · rw [rd', rd₁, ou.rd, frt.rd, hI.ci.rd]
  · rw [wr', wr₁, ou.wr, frt.wr, hI.ci.wr]
  · rw [v', v₁, hy]
  · rw [v', v₁, ou.v C (by decide), frt.v C (by decide), hI.cr]

theorem openLoop_ok {s : State} (hI : CInv σ s₀ 0 0 s)
    (hy : s.v Y = ext8 y y) (hc : s.v C = ofVDwords Impl.Gcm.AArch64.Pmull.poly Impl.Gcm.AArch64.Pmull.poly) :
    WP isa (openLoop σ.nr) s (OInv σ y s₀ σ.nb σ.nb) := by
  have hn := hp.n16
  have h1 := hp.nb1
  unfold openLoop
  refine WP.seq ?_
  -- The first batch.
  rw [WP.block_append_iff, WP.block_append_iff]
  have hx9₀ : ∀ j, s.gpr .x9 + BitVec.ofNat 64 (0 + 16 * j) = σ.D + BitVec.ofNat 64 (16 * (8 * 0 + j)) :=
    fun j => by rw [hI.x9, Offset.add_add_eq _ (show 128 * 0 + (0 + 16 * j) = 16 * (8 * 0 + j) by omega)]
  refine WP.mono (aesStep hp (c := 0) h1 (by decide) (by decide) hx9₀ hI.x10 (by rw [hI.gpr _ (by decide), hx19])
    (by rw [hI.gpr _ (by decide), hx15]) (by rw [hI.rd, hI.wr, hrdwr]) hI.frame hI.data)
    fun t ⟨hv, x10t, frt⟩ => ?_
  have gt : ∀ r, r ≠ .x10 → r ≠ .x12 → t.gpr r = s.gpr r := fun r h1 h2 => frt.gpr r (by simp [h1, h2])
  refine WP.mono (stores_ok hp (c := 0) (by omega) (by decide) (by decide) t
    (by rw [gt _ (by decide) (by decide), hI.x9]; exact BitVec.add_zero _) (by rw [frt.mem]; exact hI.data)
    (by rw [frt.wr, hI.wr, hwr]) hv) fun u ⟨d₁, f₁, g₁, v₁, sp₁, rd₁, wr₁⟩ => ?_
  rw [WP.block_cons_iff]
  refine ⟨_, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  have hI₁ : OInv σ y s₀ 1 0 (u.write .x .x11 (u.read .x .x11 - BitVec.ofNat 64 1)) := {
    ci := {
      le := h1
      x9 := by rw [gpr_write_of_ne _ _ _ (by decide), g₁, gt _ (by decide) (by decide), hI.x9]
      x10 := by
        simp only [State.read] at x10t ⊢
        rw [gpr_write_of_ne _ _ _ (by decide), g₁]; exact x10t
      x11 := by
        simp only [gpr_write_self, State.read, BitVec.setWidth_eq]
        rw [g₁, gt .x11 (by decide) (by decide), hI.x11, Nat.sub_zero, Offset.ofNat_sub_ofNat (by omega)]
      gpr := fun r hr => by
        simp only [kRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [gpr_write_of_ne _ _ _ hr.2.2.1, g₁, gt r hr.2.1 hr.2.2.2.1, hI.gpr r (by simp [kRegs, hr.1, hr.2.1,
          hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])]
      data := by rw [mem_write]; exact d₁
      frame := by rw [mem_write]; exact hI.frame.trans (frt.mem ▸ f₁)
      sp := by rw [sp_write, sp₁, frt.sp, hI.sp]
      rd := by rw [rd_write, rd₁, frt.rd, hI.rd]
      wr := by rw [wr_write, wr₁, frt.wr, hI.wr] }
    y := by rw [v_write, v₁, frt.v _ (by decide), hy]; rfl
    cr := by rw [v_write, v₁, frt.v _ (by decide), hc] }
  -- The loop, then the last batch hashed.
  refine WP.seq (WP.mono (Q := OInv σ y s₀ σ.nb (σ.nb - 1)) ?_ fun s₂ hI₂ => ?_)
  · refine WP.ite (decide (σ.nb - 1 = 0)) (eval_zero hI₁.ci.x11 (by omega)) (fun h => ?_) (fun h => ?_)
    · have : σ.nb = 1 := by simp at h; omega
      exact WP.block_nil (by rw [this]; exact hI₁)
    · let I : Nat → State → Prop := fun m s => ∃ h, m = σ.nb - (h + 1) ∧ h + 1 < σ.nb ∧ OInv σ y s₀ (h + 1) h s
      have hstep : ∀ m s, I m s → WP isa (.block (parts σ.nr 128 ++ stores 128 ++ adv)) s (fun s' =>
          (AArch64.eval (.nonzero .x .x11) s' = some false ∧ OInv σ y s₀ σ.nb (σ.nb - 1) s') ∨
          (AArch64.eval (.nonzero .x .x11) s' = some true ∧ ∃ m' < m, I m' s')) := by
        rintro m s ⟨h, rfl, hh, hI⟩
        refine WP.mono (openBody_ok hp gh hx19 hx15 hrdwr hwr hh hI) fun s' hI' => ?_
        rw [eval_nonzero hI'.ci.x11 (by omega)]
        by_cases hl : σ.nb - (h + 2) = 0
        · have e : h + 2 = σ.nb := by omega
          exact .inl ⟨by simp [hl], by rw [← e, show h + 2 - 1 = h + 1 by omega]; exact hI'⟩
        · exact .inr ⟨by simp [hl], σ.nb - (h + 2), by omega, h + 1, rfl, by omega, hI'⟩
      exact WP.loop (M := isa) I hstep _ _ ⟨0, rfl, by simp at h; omega, hI₁⟩
  · rw [WP.block_append_iff]
    have hct : ∀ j < 8, s₂.mem.readW (σ.D + BitVec.ofNat 64 (16 * (8 * (σ.nb - 1) + j))) 128 =
        σ.blockC (8 * (σ.nb - 1) + j) :=
      fun j hj => readW_of_dataInv hn hI₂.ci.data (by omega) (by omega)
    refine WP.mono (ghStep hp gh (y := y) (hb := σ.blockC) (h := σ.nb - 1) hI₂.y hI₂.cr hI₂.ci.x9 (by omega)
      (by rw [hI₂.ci.gpr _ (by decide), hx19]) (by rw [hI₂.ci.rd, hI₂.ci.wr, hrdwr]) hI₂.ci.frame hct)
      fun u ⟨hy, ou⟩ => ?_
    rw [WP.block_cons_iff]
    refine ⟨_, exec_addImm_x (imm := 128) (by decide), WP.block_nil ?_⟩
    have e : σ.nb - 1 + 1 = σ.nb := by omega
    exact {
      ci := {
        le := Nat.le_refl _
        x9 := by
          simp only [gpr_write_self, State.read, BitVec.setWidth_eq, ou.gpr, hI₂.ci.x9]
          rw [Offset.add_add_eq _ (show 128 * (σ.nb - 1) + 128 = 128 * σ.nb by omega)]
        x10 := by
          simp only [State.read, gpr_write_of_ne _ _ _ (show Reg.x10 ≠ Reg.x9 by decide), ou.gpr]; exact hI₂.ci.x10
        x11 := by rw [gpr_write_of_ne _ _ _ (by decide), ou.gpr, hI₂.ci.x11]
        gpr := fun r hr => by
          rw [gpr_write_of_ne _ _ _ (fun h => hr (by simp [h, kRegs])), ou.gpr, hI₂.ci.gpr r hr]
        data := by rw [mem_write, ou.mem]; exact hI₂.ci.data
        frame := by rw [mem_write, ou.mem]; exact hI₂.ci.frame
        sp := by rw [sp_write, ou.sp, hI₂.ci.sp]
        rd := by rw [rd_write, ou.rd, hI₂.ci.rd]
        wr := by rw [wr_write, ou.wr, hI₂.ci.wr] }
      y := by rw [v_write, hy, e]
      cr := by rw [v_write, ou.v C (by decide), hI₂.cr] }

end

end VG.Proof.AesGcmSiv.AArch64.Stitch
