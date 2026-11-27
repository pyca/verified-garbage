module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Sm4.X86.Prologue
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Sm4.X86.LayersLit
import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Sm4.Common
import VerifiedGarbage.Proof.Sm4.X86.Copy
import VerifiedGarbage.Proof.Sm4.X86.Crypt8
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Sm4.X86.Group`, which this module and modules that import it used -/

section

/-!
# Pieces of SM4 ECB on x86 (32-bit)

What ECB's groups (`Proof/Sm4/X86/EcbCall.lean`) and the key expansion
share: the count of a group's blocks (`countR_wp`), addresses of the scratch
buffer's slots and what a frame keeps of them (`slot_keep`), and what each
block becomes (`outF`).
-/

@[expose] public section

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Sm4.X86
open VG.Proof.Sm4 (DInv quads ofBlock outBlock not_contains_off blockAt_getD)
open VG.Impl.Aes.X86 (sb slotAt movS st movR addI subI subR movI)

/-! ## Small blocks -/

/-- `ecx := min(ebp, 8)`. -/
theorem countR_wp {s : State} {v : Nat} (hn : s.gpr .ebp = BitVec.ofNat 32 v) (hv : v < 2 ^ 32) :
    WP isa countR s fun s' => s'.gpr .ecx = BitVec.ofNat 32 (min v 8) ∧
      (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁, -, -⟩ := movR_ok s .ecx .ebp
  let s₂ := arithFlags s₁ (s₁.gpr .ebp - 8) ((s₁.gpr .ebp).toNat < (8 : BitVec 32).toNat)
    (subOverflow (s₁.gpr .ebp) 8 (s₁.gpr .ebp - 8))
  obtain e₂ : runBlock isa [movR .ecx .ebp, .alu .cmp .ebp (.imm 8)] s = some s₂ := by
    rw [show ([movR .ecx .ebp, .alu .cmp .ebp (.imm 8)] : List Instr) =
      [movR .ecx .ebp] ++ [.alu .cmp .ebp (.imm 8)] from rfl, runBlock_app, e₁, Option.bind_some]
    rfl
  obtain ebp₂ : s₂.gpr .ebp = BitVec.ofNat 32 v := by rw [RegUpd.gpr_arithFlags, o₁ _ (by decide), hn]
  obtain cf₂ : s₂.cf = some (decide (v < 8)) := by
    rw [RegUpd.cf_arithFlags, o₁ _ (by decide), hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]; rfl
  obtain o₂ : ∀ r, r ≠ .ecx → s₂.gpr r = s.gpr r := fun r hr => by rw [RegUpd.gpr_arithFlags, o₁ r hr]
  obtain m₂ : s₂.mem = s.mem := by rw [RegUpd.mem_arithFlags, m₁]
  obtain rd₂ : s₂.rd = s.rd := by rw [RegUpd.rd_arithFlags, rd₁]
  obtain wr₂ : s₂.wr = s.wr := by rw [RegUpd.wr_arithFlags, wr₁]
  unfold countR
  refine WP.seq (WP.of_runBlock ⟨s₂, e₂, ?_⟩)
  refine WP.ite (decide (v < 8)) ((eval_b s₂).trans cf₂) (fun h => ?_) (fun h => ?_)
  · refine WP.block_nil ⟨?_, o₂, m₂, rd₂, wr₂⟩
    rw [RegUpd.gpr_arithFlags, r₁, hn, Nat.min_eq_left (by simp at h; omega_using [h])]
  · obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movI_ok s₂ .ecx 8
    refine WP.of_runBlock ⟨s₃, e₃, ?_, fun r hr => by rw [o₃ r hr, o₂ r hr], by rw [m₃, m₂],
      by rw [rd₃, rd₂], by rw [wr₃, wr₂]⟩
    rw [r₃, Nat.min_eq_right (by simp at h; omega_using [h])]; rfl

theorem toNat_add32 (D : BitVec 32) {d : Nat} (h : D.toNat + d < 2 ^ 32) :
    (D + BitVec.ofNat 32 d).toNat = D.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h] : d < 2 ^ 32), Nat.mod_eq_of_lt h]

theorem setWidth_add {D : BitVec 32} {d : Nat} (h : D.toNat + d < 2 ^ 32) :
    (D + BitVec.ofNat 32 d).setWidth 64 = D.setWidth 64 + BitVec.ofNat 64 d := addr_eq h

/-! ## The scratch buffer's contents -/

/-- The slots `lo … hi - 1` of the scratch buffer at `b`. -/
abbrev slotsRegion (b : BitVec 32) (lo hi : Nat) : Region :=
  ⟨b.setWidth 64 + BitVec.ofNat 64 (4 * lo), 4 * (hi - lo)⟩

/-- A slot outside a frame. -/
theorem slot_keep {rs : List Region} {m m' : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32)
    {lo hi : Nat} (hhi : hi ≤ slots) (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotsRegion b lo hi).Disjoint r)
    {k : Nat} (hk1 : lo ≤ k) (hk2 : k < hi) :
    m'.readW (wordAddr b k) 32 = m.readW (wordAddr b k) 32 := by
  rw [slots_eq] at hfit hhi
  rw [slot_addr (by omega_using [hfit, hhi, hk2])]
  exact hf.readW (VG.Offset.contains _ (by omega_using [hk1]) (by omega_using [hk2]) (by omega_using [hhi, hk1, hk2])) hd (by decide)

/-! ## The data loop -/

/-- Each block, transformed: the output of the 32 rounds with the round keys `E`. -/
def outF (m₀ : Mem) (D : Addr) (E : Nat → Spec.Sm4.Word) (j : Nat) : Spec.Sm4.Block :=
  outBlock (quads .enc E 8 (ofBlock (Spec.Sm4.blockAt m₀ (D + BitVec.ofNat 64 (16 * j)))))

end VG.Proof.Sm4.X86

end

end

/-!
# SM4 ECB on x86 (32-bit): the direction and the arguments

The specification's direction (`specDirX86`), what each block becomes in it
(`outF_spec`), and loads of the stack arguments (`argSlot_ok`).
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG VG.X86 VG.Impl.Sm4.X86

/-- The specification's direction. -/
def specDirX86 : Dir → Spec.Sm4.Direction
  | .encrypt => .encrypt
  | .decrypt => .decrypt

end VG.Proof.Sm4

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Sm4.X86
open VG.Impl.Aes.X86 (sb slotAt st argOp at_)
open VG.Proof.Sm4 (DInv blocksAt_of_dinv ecb_eq blockFn specDirX86 crypt_eq quads ofBlock outBlock)

theorem outF_spec (dir : Dir) (m : Mem) (sch : Spec.Sm4.Schedule) (D : Addr) (j : Nat) :
    outF m D (dirKeys dir sch) j =
      blockFn sch (specDirX86 dir) (Spec.Sm4.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  cases dir
  · simp only [outF, blockFn, specDirX86, Spec.Sm4.encryptBlock, crypt_eq]; rfl
  · simp only [outF, blockFn, specDirX86, Spec.Sm4.decryptBlock, crypt_eq]; rfl

/-! ## The arguments -/

theorem ea_arg {s₀ s : State} (h : s.gpr .esp = s₀.gpr .esp) (i : Nat) : s.ea (argOp i) = argAddr s₀ i := by
  show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = _
  rw [h]; rfl

/-- Argument `i` is in the arguments' region. -/
theorem arg_contains (s : State) (hfit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) {i : Nat} (hi : i < 4) :
    (⟨argAddr s 0, 16⟩ : Region).Contains (argAddr s i) 4 := by
  obtain hs := setWidth_toNat (s.gpr .esp)
  rw [show argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) from addr_eq (by omega_using [hfit, hi]),
    show argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 from addr_eq (by omega_using [hfit])]
  exact VG.Offset.contains _ (by omega_using []) (by omega_using [hi]) (by omega_using [])

/-- `mov eax, [esp + 4 + 4 i]; mov [edi + 4 k], eax`. -/
theorem argSlot_ok (s : State) {b : BitVec 32} {i k : Nat} (hb : s.gpr .edi = b) (hk : k < slots)
    (hw : ScrIn s.wr b) (ha : InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4) :
    ∃ s', runBlock isa [.mov .eax (.mem (argOp i)), .store (slotAt .edi k) .eax] s = some s' ∧
      s'.gpr .eax = s.mem.readW (s.ea (argOp i)) 32 ∧ (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW (wordAddr b k) (s.mem.readW (s.ea (argOp i)) 32) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨wordAddr b k, 4⟩] s.mem s'.mem := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s .eax i ha
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, -, -, f₂⟩ := stSlot_ok s₁ .eax .edi (k := k) (by rw [o₁ _ (by decide), hb]) hk
    (by rw [wr₁]; exact hw)
  refine ⟨s₂, ?_, by rw [g₂, v₁], fun r hr => by rw [g₂, o₁ r hr], by rw [m₂, v₁, m₁], by rw [rd₂, rd₁],
    by rw [wr₂, wr₁], by rw [← m₁]; exact f₂⟩
  rw [show ([.mov .eax (.mem (argOp i)), .store (slotAt .edi k) .eax] : List Instr) =
    [.mov .eax (.mem (argOp i))] ++ [.store (slotAt .edi k) .eax] from rfl, runBlock_app, e₁, Option.bind_some, e₂]

end VG.Proof.Sm4.X86
