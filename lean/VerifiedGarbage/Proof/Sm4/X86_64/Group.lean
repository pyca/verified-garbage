module

public import VerifiedGarbage.Proof.Sm4.X86_64.Prologue
public import VerifiedGarbage.Proof.Sm4.Common
public import VerifiedGarbage.Proof.Sm4.X86_64.Core
public import VerifiedGarbage.Impl.Sm4.X86_64.Ecb
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Sm4.X86_64.Keys
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Sm4.X86_64.LayersLit

/-! ### `Sm4.X86_64.Copy`, which only this module used -/

section

/-!
# Copying blocks on x86-64

`copyBlocks_wp`: the loop `copyBlocks` copies `c ≥ 1` blocks of 16 bytes
from `rax` to `rbx` (areas that do not overlap), through `rbp`, counting
down `rcx`, and changes nothing else in memory.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.Impl.Sm4.X86_64
open VG.Proof.Sm4 (writeW_readW_apply off_sub_toNat off_sub_not not_in_of_disjoint ofInt_nat)
open VG.Impl.Aes.X86_64 (at_)

/-- `mov rbp, [rax + d]; mov [rbx + d], rbp`. -/
theorem copyWord_ok (s : State) (d : Nat) (hr : InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofNat 64 d) 8)
    (hw : InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa [.mov .rbp (.mem (at_ .rax d)), .store (at_ .rbx d) .rbp] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .rbx + BitVec.ofNat 64 d) (s.mem.readW (s.gpr .rax + BitVec.ofNat 64 d) 64) ∧
      (∀ r, r ≠ .rbp → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let v := s.mem.readW (s.gpr .rax + BitVec.ofNat 64 d) 64
  refine ⟨{ s.setReg .rbp v with mem := s.mem.writeW (s.gpr .rbx + BitVec.ofNat 64 d) v }, ?_, rfl,
    fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl⟩
  simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, State.store64,
    State.ea, ofInt_nat, hr, ite_true, Option.map_some, RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne _ _ (show Reg.rbx ≠ .rbp by decide), RegUpd.wr_setReg, hw]
  rfl

/-- Copying, after `j` of `c` blocks. -/
structure CopyInv (A B : Addr) (c : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  rax : s.gpr .rax = A + BitVec.ofNat 64 (16 * j)
  rbx : s.gpr .rbx = B + BitVec.ofNat 64 (16 * j)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (c - j)
  copied : ∀ t < 16 * j, s.mem (B + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t)
  frame : Frame [⟨B, 16 * c⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem copyBlocks_wp {A B : Addr} {c : Nat} {s₀ : State} (hc : 0 < c) (hc16 : c ≤ 16)
    (hA : ∀ t < 2 * c, InRegions (s₀.rd ++ s₀.wr) (A + BitVec.ofNat 64 (8 * t)) 8)
    (hB : ∀ t < 2 * c, InRegions s₀.wr (B + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨A, 16 * c⟩ ⟨B, 16 * c⟩) (hs : CopyInv A B c s₀ 0 s₀) :
    WP isa copyBlocks s₀ (CopyInv A B c s₀ c) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = c - j ∧ j < c ∧ CopyInv A B c s₀ j s)
    (fun n s hs => ?_) c s₀ ⟨0, by omega_using [], hc, hs⟩
  obtain ⟨j, rfl, hj, hi⟩ := hs
  have hA0 := hA (2 * j) (by omega_using [hj])
  have hA1 := hA (2 * j + 1) (by omega_using [hj])
  have hB0 := hB (2 * j) (by omega_using [hj])
  have hB1 := hB (2 * j + 1) (by omega_using [hj])
  have hfA : Frame [⟨B, 16 * c⟩] s₀.mem s.mem := hi.frame
  have hAs : ∀ t < 16 * c, s.mem (A + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t) := fun t ht =>
    hfA.bytes (R := ⟨A, 16 * c⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
      (by simp only; omega_using [hc16]) ht
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := copyWord_ok s 0
    (by rw [hi.rd, hi.wr, hi.rax, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega_using []]; exact hA0)
    (by rw [hi.wr, hi.rbx, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega_using []]; exact hB0)
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := copyWord_ok s₁ 8
    (by rw [rd₁, wr₁, hi.rd, hi.wr, g₁ _ (by decide), hi.rax, addr_add,
      show 16 * j + 8 = 8 * (2 * j + 1) by omega_using []]; exact hA1)
    (by rw [wr₁, hi.wr, g₁ _ (by decide), hi.rbx, addr_add, show 16 * j + 8 = 8 * (2 * j + 1) by omega_using []]; exact hB1)
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := addImm_ok s₂ .rax 16
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := addImm_ok s₃ .rbx 16
  obtain ⟨s₅, e₅, c₅, z₅, o₅, m₅, rd₅, wr₅⟩ := subImm_ok s₄ .rcx 1
  refine WP.of_runBlock ⟨s₅, by
    rw [show ([Instr.mov .rbp (.mem (at_ .rax 0)), .store (at_ .rbx 0) .rbp,
      .mov .rbp (.mem (at_ .rax 8)), .store (at_ .rbx 8) .rbp,
      .alu .add .rax (.imm 16), .alu .add .rbx (.imm 16), .alu .sub .rcx (.imm 1)] : List Instr) =
      [.mov .rbp (.mem (at_ .rax 0)), .store (at_ .rbx 0) .rbp] ++
      ([.mov .rbp (.mem (at_ .rax 8)), .store (at_ .rbx 8) .rbp] ++
      ([.alu .add .rax (.imm 16)] ++ ([.alu .add .rbx (.imm 16)] ++ [.alu .sub .rcx (.imm 1)]))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, e₅], ?_⟩
  have hn : 16 * c < 2 ^ 64 := by omega_using [hc16]
  have r1 : s₁.gpr .rbx = B + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide), hi.rbx]
  have a1 : s₁.gpr .rax = A + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide), hi.rax]
  have hm : s₅.mem = (s₁.mem.writeW (B + BitVec.ofNat 64 (16 * j + 8))
      (s₁.mem.readW (A + BitVec.ofNat 64 (16 * j + 8)) 64)) := by
    rw [m₅, m₄, m₃, m₂, r1, a1, addr_add, addr_add]
  have hm₁ : s₁.mem = s.mem.writeW (B + BitVec.ofNat 64 (16 * j))
      (s.mem.readW (A + BitVec.ofNat 64 (16 * j)) 64) := by
    rw [m₁, hi.rbx, hi.rax, addr_add, addr_add, Nat.add_zero]
  -- `s₁` and `s` agree on `A`'s area.
  have hA₁ : ∀ t < 16 * c, s₁.mem (A + BitVec.ofNat 64 t) = s.mem (A + BitVec.ofNat 64 t) := fun t ht => by
    rw [hm₁, writeW_readW_apply, ite_eq_right (not_in_of_disjoint hsep ht (by omega_using [hj]) hn)]
  have hinv : CopyInv A B c s₀ (j + 1) s₅ := by
    refine ⟨?_, ?_, ?_, fun t ht => ?_, hi.frame.trans fun x hx => ?_, fun r h1 h2 h3 h4 => ?_,
      by rw [rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr]⟩
    · rw [o₅ _ (by decide), o₄ _ (by decide), a₃, g₂ _ (by decide), a1,
        show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega_using []]
    · rw [o₅ _ (by decide), a₄, o₃ _ (by decide), g₂ _ (by decide), r1,
        show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega_using []]
    · rw [c₅, o₄ _ (by decide), o₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.rcx,
        show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega_using [hj]),
        show c - j - 1 = c - (j + 1) by omega_using []]
    · rw [hm, writeW_readW_apply]
      by_cases h8 : 16 * j + 8 ≤ t
      · rw [ite_eq_left (by rw [off_sub_toNat B h8 (by omega_using [hc16, hj, ht])]; omega_using [ht]), off_sub_toNat B h8 (by omega_using [hc16, hj, ht]), addr_add,
          show 16 * j + 8 + (t - (16 * j + 8)) = t by omega_using [h8], hA₁ t (by omega_using [hj, ht]), hAs t (by omega_using [hj, ht])]
      · rw [ite_eq_right (off_sub_not B (Or.inl (by omega_using [h8])) (by omega_using [hc16, hj, ht]) (by omega_using []) (by omega_using [hc16, hj])), hm₁,
          writeW_readW_apply]
        by_cases h0 : 16 * j ≤ t
        · rw [ite_eq_left (by rw [off_sub_toNat B h0 (by omega_using [hc16, hj, ht])]; omega_using [h8]), off_sub_toNat B h0 (by omega_using [hc16, hj, ht]), addr_add,
            show 16 * j + (t - 16 * j) = t by omega_using [h0], hAs t (by omega_using [hj, ht])]
        · rw [ite_eq_right (off_sub_not B (Or.inl (by omega_using [h0])) (by omega_using [hc16, hj, ht]) (by omega_using []) (by omega_using [hc16, hj]))]
          exact hi.copied t (by omega_using [h0])
    · have hout : ∀ e, e + 8 ≤ 16 * c → ¬ (x - (B + BitVec.ofNat 64 e)).toNat < 8 := fun e he h =>
        hx _ (List.mem_singleton_self _) (VG.Offset.sub_base B he _ (by simp only [Region.Contains]; omega_using [h]))
      rw [hm, writeW_readW_apply, ite_eq_right (hout _ (by omega_using [hj])), hm₁, writeW_readW_apply,
        ite_eq_right (hout _ (by omega_using [hj]))]
    · rw [o₅ r h3, o₄ r h2, o₃ r h1, g₂ r h4, g₁ r h4, hi.regs r h1 h2 h3 h4]
  have hz : s₅.zf = some (decide (c - (j + 1) = 0)) := by
    rw [z₅, o₄ _ (by decide), o₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.rcx,
      show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat_beq (by omega_using [hc16]) (by decide)]
    simp only [Option.some.injEq, decide_eq_decide]; omega_using [hj]
  by_cases hl : j + 1 = c
  · refine .inl ⟨by simp [X86_64.eval, hz, hl], by rw [show j + 1 = c from hl] at hinv; exact hinv⟩
  · exact .inr ⟨by simp [X86_64.eval, hz]; omega_using [hj, hl], c - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, hl], hinv⟩

end VG.Proof.Sm4.X86_64

end

end


/-!
# A group of blocks of SM4 ECB on x86-64

`dataGroup_wp`: one iteration of the data loop copies the group's blocks
(sixteen, or the last one to fifteen) to the tail buffer, transforms the
tail buffer (`crypt16_wp`), copies the blocks back and steps to the next
group.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Sm4.X86_64
open VG.Proof.Sm4 (DInv ofInt_nat quads ofBlock outBlock)
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR movS st at_)


/-! ## Small blocks -/

theorem cmpImm_ok (s : State) (r : Reg) (k : BitVec 32) {v K : Nat} (hr : s.gpr r = BitVec.ofNat 64 v)
    (hv : v < 2 ^ 64) (hk : (k.signExtend 64).toNat = K) :
    ∃ s', runBlock isa [.alu .cmp r (.imm k)] s = some s' ∧ s'.cf = some (decide (v < K)) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨arithFlags s (s.gpr r - k.signExtend 64) (decide ((s.gpr r).toNat < (k.signExtend 64).toNat))
    (subOverflow (s.gpr r) (k.signExtend 64) (s.gpr r - k.signExtend 64)), ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
  · simp [arithFlags, State.setFlags, hr, hk]; rw [Nat.mod_eq_of_lt (by simpa using hv)]

theorem movR_ok (s : State) (d r : Reg) :
    ∃ s', runBlock isa [movR d r] s = some s' ∧ s'.gpr d = s.gpr r ∧
      (∀ r', r' ≠ d → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.setReg d (s.gpr r), ?_, by simp only [RegUpd.gpr_setReg_self],
    fun r' hr => by simp only [RegUpd.gpr_setReg_of_ne _ _ hr], rfl, rfl, rfl⟩
  simp only [movR, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]

theorem subSelf_ok (s : State) (r : Reg) :
    ∃ s', runBlock isa [.alu .sub r (.reg r)] s = some s' ∧ s'.zf = some true ∧
      (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨(arithFlags s (s.gpr r - s.gpr r) ((s.gpr r).toNat < (s.gpr r).toNat)
    (subOverflow (s.gpr r) (s.gpr r) (s.gpr r - s.gpr r))).setReg r (s.gpr r - s.gpr r), ?_, ?_,
    fun r' hr => ?_, rfl, rfl, rfl⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
  · simp only [RegUpd.zf_setReg, RegUpd.zf_arithFlags, BitVec.sub_self]; rfl
  · simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- `rcx := min(r8, 16)`. -/
theorem groupCount_wp {s : State} {v : Nat} (hr : s.gpr .r8 = BitVec.ofNat 64 v) (hv : v < 2 ^ 64) :
    WP isa groupCount s fun s' => s'.gpr .rcx = BitVec.ofNat 64 (min v 16) ∧
      (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, c₁, o₁, m₁, rd₁, wr₁⟩ := movImm_ok s .rcx 16
  obtain ⟨s₂, e₂, f₂, g₂, m₂, rd₂, wr₂⟩ := cmpImm_ok s₁ .r8 16 (v := v) (by rw [o₁ _ (by decide), hr]) hv rfl
  unfold groupCount
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [show ([Instr.movImm64 .rcx 16, .alu .cmp .r8 (.imm 16)] : List Instr) =
      [.movImm64 .rcx 16] ++ [.alu .cmp .r8 (.imm 16)] from rfl, runBlock_app, e₁, Option.bind_some, e₂], ?_⟩)
  refine WP.ite (decide (v < 16)) (by simp [X86_64.eval, f₂]) (fun h => ?_) (fun h => ?_)
  · obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ .rcx .r8
    refine WP.of_runBlock ⟨s₃, e₃, ?_, fun r hr => ?_, by rw [m₃, m₂, m₁], by rw [rd₃, rd₂, rd₁],
      by rw [wr₃, wr₂, wr₁]⟩
    · rw [r₃, g₂, o₁ _ (by decide), hr, Nat.min_eq_left (by simp at h; omega_using [h])]
    · rw [o₃ r hr, g₂, o₁ r hr]
  · refine WP.of_runBlock ⟨s₂, rfl, ?_, fun r hr => ?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    · rw [g₂, c₁, Nat.min_eq_right (by simp at h; omega_using [h])]; rfl
    · rw [g₂, o₁ r hr]

/-- `mov [sb + 8 k], r`. -/
theorem stReg_ok {s : State} {b : Addr} {k : Nat} (r : Reg) (hb : s.gpr sb = b)
    (hw : InRegions s.wr (wordAddr b k) 8) :
    ∃ s', runBlock isa [st k r] s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) (s.gpr r) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hw' : InRegions s.wr (b + BitVec.ofNat 64 (8 * k)) 8 := hw
  refine ⟨{ s with mem := s.mem.writeW (wordAddr b k) (s.gpr r) }, ?_, rfl, rfl, rfl, rfl⟩
  simp only [st, Impl.Aes.X86_64.slotAt, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.store64, State.ea, ofInt_nat, hb, hw', ite_true]

/-- `mov d, [sb + 8 k]`. -/
theorem movS_ok {s : State} {b : Addr} {k : Nat} (d : Reg) (hb : s.gpr sb = b)
    (hr : InRegions (s.rd ++ s.wr) (wordAddr b k) 8) :
    ∃ s', runBlock isa [movS d k] s = some s' ∧ s'.gpr d = slotW s k ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hr' : InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 (8 * k)) 8 := hr
  refine ⟨s.setReg d (slotW s k), ?_, by simp only [RegUpd.gpr_setReg_self],
    fun r h => by simp only [RegUpd.gpr_setReg_of_ne _ _ h], rfl, rfl, rfl⟩
  simp only [movS, Impl.Aes.X86_64.slotAt, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, State.ea, ofInt_nat, hb, hr', ite_true, Option.map_some, slotW, wordAddr]

theorem readW_slot_write {m : Mem} {b : Addr} {j k : Nat} (v : BitVec 64) (hj : j < slots) (hk : k < slots) :
    (m.writeW (wordAddr b k) v).readW (wordAddr b j) 64 = if j = k then v else m.readW (wordAddr b j) 64 := by
  rw [slots_eq] at hj hk
  split
  · rename_i h; subst h; exact Mem.readW_writeW_self64 _ _ _
  · rename_i h; exact Mem.readW_writeW_sep (slot_sep b (by omega_using [hj]) (by omega_using [hk]) h) (by decide)

/-! ## The scratch buffer's contents -/

/-- The masks, in the memory at `b`. -/
def MasksAt (m : Mem) (b : Addr) : Prop := ∀ kv ∈ keyMasks, m.readW (wordAddr b kv.1) 64 = kv.2

theorem MasksOk.at {s : State} {b : Addr} (h : MasksOk s) (hb : s.gpr sb = b) : MasksAt s.mem b :=
  fun kv hkv => by rw [← hb]; exact h kv hkv

theorem MasksAt.ok {s : State} {b : Addr} (h : MasksAt s.mem b) (hb : s.gpr sb = b) : MasksOk s :=
  fun kv hkv => by show s.mem.readW (wordAddr (s.gpr sb) kv.1) 64 = kv.2; rw [hb]; exact h kv hkv

/-- What the data loop keeps in the scratch buffer: the masks, the table and
the saved registers. -/
structure ScrOk (s₀ : State) (b : Addr) (E : Nat → Spec.Sm4.Word) (m : Mem) : Prop where
  masks : MasksAt m b
  keys : ∀ e < 32, VG.Proof.Sm4.WordRel (entryW m b e) fun _ => E e
  saved : Saved s₀ b m

/-- The slots `ScrOk` reads: 48–50, the table (128–383) and 384–389. -/
abbrev scrRegions (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 (8 * 48), 24⟩, ⟨b + BitVec.ofNat 64 (8 * tableSlot), 8 * 256⟩,
    ⟨b + BitVec.ofNat 64 (8 * savedSlot), 48⟩]

theorem mask_range {kv : Nat × BitVec 64} (hkv : kv ∈ keyMasks) : 48 ≤ kv.1 ∧ kv.1 < 51 := by
  simp [keyMasks] at hkv; rcases hkv with h | h | h <;> subst h <;> simp [evenSlot, oddSlot, grpSlot]

theorem ScrOk.frame {s₀ : State} {b : Addr} {E : Nat → Spec.Sm4.Word} {m m' : Mem}
    (h : ScrOk s₀ b E m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ t ∈ scrRegions b, ∀ r ∈ rs, Region.Disjoint t r) :
    ScrOk s₀ b E m' := by
  have hR : ∀ t ∈ scrRegions b, ∀ d, Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ t →
      m'.readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 := fun t ht d hs =>
    hf.readW (Region.contains_self _ _) (fun r hr => (hd _ ht r hr).sub_left hs) (by decide)
  refine ⟨fun kv hkv => ?_, fun i hi => (h.keys i hi).congr fun j hj => ?_, fun i hi => ?_⟩
  · have hk := mask_range hkv
    rw [← h.masks kv hkv]
    exact hR _ List.mem_cons_self (8 * kv.1) (VG.Offset.sub b (by omega_using [hk]) (by omega_using [hk]))
  · exact hR _ (List.mem_cons_of_mem _ List.mem_cons_self) (8 * tableSlot + 64 * i + 8 * j)
      (VG.Offset.sub b (by omega_using []) (by rw [tableSlot_eq]; omega_using [hi, hj]))
  · rw [← h.saved i hi]
    exact hR _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (8 * (savedSlot + i))
      (VG.Offset.sub b (by omega_using []) (by omega_using [hi]))

theorem ScrOk.frame2 {s₀ : State} {b : Addr} {E : Nat → Spec.Sm4.Word} {m m' : Mem}
    (h : ScrOk s₀ b E m) {rs : List Region} (hf : Frame rs m m') (hm : MasksAt m' b)
    (hd : ∀ t ∈ (scrRegions b).tail, ∀ r ∈ rs, Region.Disjoint t r) : ScrOk s₀ b E m' := by
  have hR : ∀ t ∈ (scrRegions b).tail, ∀ d, Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ t →
      m'.readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 := fun t ht d hs =>
    hf.readW (Region.contains_self _ _) (fun r hr => (hd _ ht r hr).sub_left hs) (by decide)
  refine ⟨hm, fun i hi => (h.keys i hi).congr fun j hj => ?_, fun i hi => ?_⟩
  · exact hR _ List.mem_cons_self (8 * tableSlot + 64 * i + 8 * j)
      (VG.Offset.sub b (by omega_using []) (by rw [tableSlot_eq]; omega_using [hi, hj]))
  · rw [← h.saved i hi]
    exact hR _ (List.mem_cons_of_mem _ List.mem_cons_self) (8 * (savedSlot + i))
      (VG.Offset.sub b (by omega_using []) (by omega_using [hi]))

/-! ## The data loop -/

/-- Each block, transformed: the output of the 32 rounds with the round keys `E`. -/
def outF (m₀ : Mem) (D : Addr) (E : Nat → Spec.Sm4.Word) (j : Nat) : Spec.Sm4.Block :=
  outBlock (quads .enc E 8 (ofBlock (Spec.Sm4.blockAt m₀ (D + BitVec.ofNat 64 (16 * j)))))

/-- The scratch buffer at `b` and the `n` blocks at `D`. -/
structure GPre (s₀ : State) (b D : Addr) (n : Nat) : Prop where
  scr : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 8 * slots⟩
  fit : b.toNat + 8 * slots ≤ 2 ^ 64
  fitD : D.toNat + 16 * n ≤ 2 ^ 64

/-- `copyBlocks` from `rax` to `rbx`, `rcx` blocks, set up. -/
theorem copy_wp {s : State} {X Y : Addr} {c : Nat} (hc : 0 < c) (hc16 : c ≤ 16)
    (hx : s.gpr .rax = X) (hy : s.gpr .rbx = Y) (hcx : s.gpr .rcx = BitVec.ofNat 64 c)
    (hX : ∀ t < 2 * c, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (8 * t)) 8)
    (hY : ∀ t < 2 * c, InRegions s.wr (Y + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨X, 16 * c⟩ ⟨Y, 16 * c⟩) :
    WP isa copyBlocks s fun s' => (∀ t < 16 * c, s'.mem (Y + BitVec.ofNat 64 t) = s.mem (X + BitVec.ofNat 64 t)) ∧
      Frame [⟨Y, 16 * c⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.mono (copyBlocks_wp hc hc16 hX hY hsep ⟨by rw [hx]; simp, by rw [hy]; simp, by rw [hcx, Nat.sub_zero],
    fun t ht => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩)
    fun s' h => ⟨h.copied, h.frame, h.regs, h.rd, h.wr⟩

/-- The data loop, before group `k`. -/
structure GInv (s₀ : State) (b D : Addr) (n : Nat) (E : Nat → Spec.Sm4.Word) (k : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rdx : s.gpr .rdx = D + BitVec.ofNat 64 (256 * k)
  r8 : s.gpr .r8 = BitVec.ofNat 64 (n - 16 * k)
  lt : 16 * k < n
  rdi : s.gpr .rdi = b + BitVec.ofNat 64 (8 * tableEnd)
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem D n (16 * k) (outF s₀.mem D E)
  frame : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure GDone (s₀ : State) (b D : Addr) (n : Nat) (E : Nat → Spec.Sm4.Word) (s : State) : Prop where
  base : s.gpr sb = b
  rsp : s.gpr .rsp = s₀.gpr .rsp
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem D n n (outF s₀.mem D E)
  frame : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem inRd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

end VG.Proof.Sm4.X86_64
