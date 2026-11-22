module

public import VerifiedGarbage.Proof.Framework.TacticTemplate

public import VerifiedGarbage.Proof.Sm4.X86.CryptSum
meta import VerifiedGarbage.Proof.Sm4.X86.CryptSum
public import VerifiedGarbage.Proof.Sm4.X86.Lit
meta import VerifiedGarbage.Proof.Sm4.X86.Lit
public import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Inline
meta import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Impl.Sm4.X86.Modes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Sm4.X86.Copy
public import VerifiedGarbage.Proof.Sm4.X86.Crypt8
import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Impl.Sm4.X86.Modes
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Sm4.Layout
meta import VerifiedGarbage.Proof.Sm4.X86.Copy
meta import VerifiedGarbage.Proof.Sm4.X86.Crypt8
meta import VerifiedGarbage.Spec.Ctr.Contract
public import VerifiedGarbage.Proof.Sm4.X86.Ecb
meta import VerifiedGarbage.Proof.Sm4.X86.Ecb
public import VerifiedGarbage.Proof.Sm4.X86.ModeCore
meta import VerifiedGarbage.Proof.Sm4.X86.ModeCore
import VerifiedGarbage.Proof.Sm4.CtrCipher
meta import VerifiedGarbage.Proof.Sm4.CtrCipher

/-!
# SM4 ECB on x86 (32-bit) meets its contracts

`ecb_wp`: with the working space as an argument (`ecbX86`, the modes' 368
slots), `ecb dir` saves the callee-saved registers after the slots of the
prepared functions (`entryE_ok`), builds the table of round keys in the
order `dir` uses them (`keys_wp`), keeps the data pointer and the count in
the modes' slots, transforms the blocks a group at a time (`dataLoop_wp`:
each group copied to the tail buffer, transformed there by
`vg_sm4_crypt_prepared`, `crypt_wp`, and copied back) and restores the
registers.

`ecb_verified`: `ecb dir` is correct (`ecb_wp`) and constant time, by the
taint analysis, which starts with `esp` public and knows which argument
words are the base addresses of the data and the scratch buffer, and the 20
bytes below `esp` that the calls of `vg_sm4_crypt_prepared` use as apart
from them: the pointers, `n` and what the code computes from them are
public, in registers or in the scratch buffer's slots, which the code stores
again after each store through another pointer. The check uses the summary
of the call (`CryptSum.lean`). `ecb_framed` runs it with its working space
on the stack, zeroed on return: 1492 bytes, the 1472 of the scratch buffer,
the copies of the three argument slots, the buffer's address and the return
address of the call of the code, which uses 20 bytes below them.
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG VG.X86 VG.Impl.Sm4.X86

/-- ECB on x86 with its working space as the fourth argument: the modes'
368 slots, and 20 bytes of stack below `esp` for the calls. -/
def ecbX86 (dir : Dir) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 128⟩
    let data : Region := ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 8 * 184⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack := below (s.gpr .esp) 20
    s.rd = [sched, args] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    stack.Disjoint data ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 16 * (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 8 * 184 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat
  post s s' :=
    Spec.Sm4.blocksAt s'.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
      Spec.Sm4.ecb (Spec.Sm4.scheduleAt s.mem ((arg s 0).setWidth 64)) (specDirX86 dir)
        (Spec.Sm4.blocksAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

end VG.Proof.Sm4

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Sm4.X86
open VG.Proof.Sm4 (DInv quads ofBlock outBlock not_contains_off blockAt_getD blocksAt_of_dinv ecb_eq blockFn
  specDirX86 ecbX86 bytesAt_eq_blockAt)
open VG.Impl.Aes.X86 (sb slotAt movS st movR addI subI subR movI argOp at_)
open VG.Proof.Modes.X86 (stkRegion)

/-! ## ECB's Impl.Sm4.X86.slots after the functions' -/

/-- ECB's scratch buffer at `b`, of the modes' 368 Impl.Sm4.X86.slots, in the regions `rs`. -/
structure EIn (rs : List Region) (b : BitVec 32) : Prop where
  mem : (⟨b.setWidth 64, 4 * 368⟩ : Region) ∈ rs
  fit : b.toNat + 4 * 368 ≤ 2 ^ 32

theorem EIn.scr {rs : List Region} {b : BitVec 32} (h : EIn rs b) : ScrIn rs b :=
  ⟨⟨368, by decide, h.fit, h.mem⟩, by have := h.fit; rw [slots_eq]; omega_using [this]⟩

theorem EIn.fit' {rs : List Region} {b : BitVec 32} (h : EIn rs b) : b.toNat + 4 * Impl.Sm4.X86.slots ≤ 2 ^ 32 := by
  have := h.fit; rw [slots_eq]; omega_using [this]

/-- `mov d, [n + 4 k]`, a slot of ECB's buffer. -/
theorem ldE_ok (s : State) (d n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : k < 368)
    (hw : EIn s.wr b) :
    ∃ s', runBlock isa [.mov d (.mem (slotAt n k))] s = some s' ∧ s'.gpr d = s.mem.readW (wordAddr b k) 32 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧
      s'.cf = s.cf := by
  have he : s.ea (slotAt n k) = wordAddr b k := by rw [slotAt, ea_mk, hn]
  refine ⟨s.setReg d (s.mem.readW (wordAddr b k) 32), ?_, RegUpd.gpr_setReg_self _ _ _,
    fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl, rfl⟩
  rw [runBlock_cons, show exec (.mov d (.mem (slotAt n k))) s = some (s.setReg d (s.mem.readW (wordAddr b k) 32)) by
    simp [exec, readSrc, State.load32, he, inRd (slot_in hw.mem hw.fit hk)], runStep_some, runBlock_nil]

/-- `mov [n + 4 k], t`, a slot of ECB's buffer. -/
theorem stE_ok (s : State) (t n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : k < 368)
    (hw : EIn s.wr b) :
    ∃ s', runBlock isa [.store (slotAt n k) t] s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) (s.gpr t) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧ s'.cf = s.cf ∧
      Frame [⟨wordAddr b k, 4⟩] s.mem s'.mem := by
  have he : s.ea (slotAt n k) = wordAddr b k := by rw [slotAt, ea_mk, hn]
  refine ⟨{ s with mem := s.mem.writeW (wordAddr b k) (s.gpr t) }, ?_, rfl, rfl, rfl, rfl, rfl, rfl,
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)⟩
  rw [runBlock_cons]
  simp only [exec, State.store32, he, slot_in hw.mem hw.fit hk, ↓reduceIte, runStep_some, runBlock_nil]

/-- A slot is inside ECB's buffer. -/
theorem slotE_sub {b : BitVec 32} (hfit : b.toNat + 4 * 368 ≤ 2 ^ 32) {k : Nat} (hk : k < 368) :
    Region.Sub ⟨wordAddr b k, 4⟩ ⟨b.setWidth 64, 4 * 368⟩ := by
  rw [slot_addr (by omega_using [hfit, hk])]
  exact VG.Offset.sub_base _ (by omega_using [hk])

/-- A slot after a store to a slot. -/
theorem readW_slotE_write {m : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * 368 ≤ 2 ^ 32) {j k : Nat}
    (v : BitVec 32) (hj : j < 368) (hk : k < 368) :
    (m.writeW (wordAddr b k) v).readW (wordAddr b j) 32 = if j = k then v else m.readW (wordAddr b j) 32 := by
  split
  · rename_i h; subst h; exact Mem.readW_writeW_self32 _ _ _
  · rename_i h; exact Mem.readW_writeW_sep (slot_sep b (by omega_using [hfit, hj]) (by omega_using [hfit, hk]) h) (by decide)

/-- A slot of ECB's buffer outside a frame. -/
theorem slotE_keep {rs : List Region} {m m' : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * 368 ≤ 2 ^ 32)
    {lo hi : Nat} (hhi : hi ≤ 368) (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotsRegion b lo hi).Disjoint r)
    {k : Nat} (hk1 : lo ≤ k) (hk2 : k < hi) :
    m'.readW (wordAddr b k) 32 = m.readW (wordAddr b k) 32 := by
  rw [slot_addr (by omega_using [hfit, hhi, hk2])]
  exact hf.readW (VG.Offset.contains _ (by omega_using [hk1]) (by omega_using [hk2]) (by omega_using [hhi, hk1, hk2])) hd (by decide)

theorem modeDSlot_lt : modeDSlot < 368 := by decide
theorem modeNSlot_lt : modeNSlot < 368 := by decide

/-- The data pointer and the blocks left from their Impl.Sm4.X86.slots to `esi` and
`ebp`, and `ecx := min(ebp, 8)`. -/
theorem groupCount_wp {s : State} {b A : BitVec 32} {v : Nat} (hb : s.gpr .edi = b) (hw : EIn s.wr b)
    (hd : s.mem.readW (wordAddr b modeDSlot) 32 = A) (hn : s.mem.readW (wordAddr b modeNSlot) 32 = BitVec.ofNat 32 v)
    (hv : v < 2 ^ 32) :
    WP isa groupCount s fun s' => s'.gpr .esi = A ∧ s'.gpr .ebp = BitVec.ofNat 32 v ∧
      s'.gpr .ecx = BitVec.ofNat 32 (min v 8) ∧
      (∀ r, r ≠ .esi → r ≠ .ebp → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁, -, -⟩ := ldE_ok s .esi .edi (k := modeDSlot) hb modeDSlot_lt hw
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, -, -⟩ := ldE_ok s₁ .ebp .edi (k := modeNSlot)
    (by rw [o₁ _ (by decide), hb]) modeNSlot_lt (by rw [wr₁]; exact hw)
  unfold groupCount
  refine WP.seq (WP.of_runBlock ⟨s₂, ?_, WP.mono (countR_wp (by rw [r₂, m₁, hn]) hv)
    fun s₃ ⟨c₃, o₃, m₃, rd₃, wr₃⟩ => ?_⟩)
  · rw [show ([movS .esi modeDSlot, movS .ebp modeNSlot] : List Instr) =
      [.mov .esi (.mem (slotAt .edi modeDSlot))] ++ [.mov .ebp (.mem (slotAt .edi modeNSlot))] from rfl,
      runBlock_app, e₁, Option.bind_some, e₂]
  · exact ⟨by rw [o₃ _ (by decide), o₂ _ (by decide), r₁, hd], by rw [o₃ _ (by decide), r₂, m₁, hn], c₃,
      fun r h1 h2 h3 => by rw [o₃ r h3, o₂ r h2, o₁ r h1], by rw [m₃, m₂, m₁], by rw [rd₃, rd₂, rd₁],
      by rw [wr₃, wr₂, wr₁]⟩

/-- `st modeDSlot, esi; st modeNSlot, ebp`. -/
theorem stDN_ok (s : State) {b : BitVec 32} (hb : s.gpr .edi = b) (hw : EIn s.wr b) :
    ∃ s', runBlock isa [st modeDSlot .esi, st modeNSlot .ebp] s = some s' ∧
      s'.mem.readW (wordAddr b modeDSlot) 32 = s.gpr .esi ∧ s'.mem.readW (wordAddr b modeNSlot) 32 = s.gpr .ebp ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧
      Frame [⟨wordAddr b modeDSlot, 4⟩, ⟨wordAddr b modeNSlot, 4⟩] s.mem s'.mem := by
  have hfit := hw.fit
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁, z₁, -, f₁⟩ := stE_ok s .esi .edi (k := modeDSlot) hb modeDSlot_lt hw
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, z₂, -, f₂⟩ := stE_ok s₁ .ebp .edi (k := modeNSlot) (by rw [g₁, hb])
    modeNSlot_lt (by rw [wr₁]; exact hw)
  refine ⟨s₂, ?_, ?_, ?_, by rw [g₂, g₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [z₂, z₁],
    (f₁.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (f₂.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)⟩
  · rw [show ([st modeDSlot .esi, st modeNSlot .ebp] : List Instr) =
      [.store (slotAt .edi modeDSlot) .esi] ++ [.store (slotAt .edi modeNSlot) .ebp] from rfl, runBlock_app, e₁,
      Option.bind_some, e₂]
  · rw [m₂, readW_slotE_write hfit _ modeDSlot_lt modeNSlot_lt, ite_eq_right (by decide), m₁,
      readW_slotE_write hfit _ modeDSlot_lt modeDSlot_lt, ite_eq_left rfl]
  · rw [m₂, readW_slotE_write hfit _ modeNSlot_lt modeNSlot_lt, ite_eq_left rfl, g₁]

/-! ## Saving and restoring the callee-saved registers -/

/-- The saved registers are in ECB's Impl.Sm4.X86.slots. -/
def ESaved (s₀ : State) (b : BitVec 32) (m : Mem) : Prop :=
  ∀ i < 4, m.readW (wordAddr b (Impl.Sm4.X86.slots + i)) 32 = s₀.gpr (sreg i)

theorem entryE_ok {s : State} {b : BitVec 32} (hw : EIn s.wr b)
    (ha : InRegions (s.rd ++ s.wr) (s.ea (argOp 3)) 4) (hb : s.mem.readW (s.ea (argOp 3)) 32 = b) :
    ∃ s', runBlock isa ecbEntry s = some s' ∧ s'.gpr .edi = b ∧
      (∀ r, r ≠ .eax → r ≠ .edi → s'.gpr r = s.gpr r) ∧ ESaved s b s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b.setWidth 64, 4 * 368⟩] s.mem s'.mem := by
  have hfit := hw.fit
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s .eax 3 ha
  rw [hb] at v₁
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, -, -, f₂⟩ := stE_ok s₁ .ebx .eax (k := Impl.Sm4.X86.slots) v₁ (by decide)
    (by rw [wr₁]; exact hw)
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃, -, -, f₃⟩ := stE_ok s₂ .esi .eax (k := Impl.Sm4.X86.slots + 1) (by rw [g₂, v₁])
    (by decide) (by rw [wr₂, wr₁]; exact hw)
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄, -, -, f₄⟩ := stE_ok s₃ .edi .eax (k := Impl.Sm4.X86.slots + 2) (by rw [g₃, g₂, v₁])
    (by decide) (by rw [wr₃, wr₂, wr₁]; exact hw)
  obtain ⟨s₅, e₅, m₅, g₅, rd₅, wr₅, -, -, f₅⟩ := stE_ok s₄ .ebp .eax (k := Impl.Sm4.X86.slots + 3) (by rw [g₄, g₃, g₂, v₁])
    (by decide) (by rw [wr₄, wr₃, wr₂, wr₁]; exact hw)
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆, -, -⟩ := movR_ok s₅ .edi .eax
  obtain g₂₅ : s₅.gpr = s₁.gpr := by rw [g₅, g₄, g₃, g₂]
  refine ⟨s₆, ?_, by rw [r₆, g₂₅, v₁], fun r h0 h7 => by rw [o₆ r h7, g₂₅, o₁ r h0], fun i hi => ?_,
    by rw [rd₆, rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁], ?_⟩
  · rw [show ecbEntry = [.mov .eax (.mem (argOp 3))] ++ ([.store (slotAt .eax Impl.Sm4.X86.slots) .ebx] ++
        ([.store (slotAt .eax (Impl.Sm4.X86.slots + 1)) .esi] ++ ([.store (slotAt .eax (Impl.Sm4.X86.slots + 2)) .edi] ++
          ([.store (slotAt .eax (Impl.Sm4.X86.slots + 3)) .ebp] ++ [movR .edi .eax])))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some,
      runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some, e₆]
  · obtain hs : ∀ r, r ≠ .eax → s₁.gpr r = s.gpr r := o₁
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_using [hi]) with rfl | rfl | rfl | rfl
    · rw [m₆, m₅, readW_slotE_write hfit _ (by decide) (by decide), ite_eq_right (by decide), m₄,
        readW_slotE_write hfit _ (by decide) (by decide), ite_eq_right (by decide), m₃,
        readW_slotE_write hfit _ (by decide) (by decide), ite_eq_right (by decide), m₂,
        readW_slotE_write hfit _ (by decide) (by decide), ite_eq_left (show Impl.Sm4.X86.slots + 0 = Impl.Sm4.X86.slots from rfl), hs _ (by decide)]; rfl
    · rw [m₆, m₅, readW_slotE_write hfit _ (by decide) (by decide), ite_eq_right (by decide), m₄,
        readW_slotE_write hfit _ (by decide) (by decide), ite_eq_right (by decide), m₃,
        readW_slotE_write hfit _ (by decide) (by decide), ite_eq_left rfl, g₂, hs _ (by decide)]; rfl
    · rw [m₆, m₅, readW_slotE_write hfit _ (by decide) (by decide), ite_eq_right (by decide), m₄,
        readW_slotE_write hfit _ (by decide) (by decide), ite_eq_left rfl, g₃, g₂, hs _ (by decide)]; rfl
    · rw [m₆, m₅, readW_slotE_write hfit _ (by decide) (by decide), ite_eq_left rfl, g₄, g₃, g₂,
        hs _ (by decide)]; rfl
  · have sub : ∀ k < 368, ∀ r ∈ [(⟨wordAddr b k, 4⟩ : Region)], ∃ R ∈ [(⟨b.setWidth 64, 4 * 368⟩ : Region)],
        Region.Sub r R := fun k hk r hr => ⟨_, List.mem_singleton_self _, by
          simp only [List.mem_singleton] at hr; subst hr; exact slotE_sub hfit hk⟩
    rw [m₆, ← m₁]
    exact (f₂.sub (sub _ (by decide))).trans ((f₃.sub (sub _ (by decide))).trans
      ((f₄.sub (sub _ (by decide))).trans (f₅.sub (sub _ (by decide)))))

theorem restoreE_ok {s₀ s : State} {b : BitVec 32} (hw : EIn s.wr b) (hb : s.gpr .edi = b)
    (hs : ESaved s₀ b s.mem) :
    ∃ s', runBlock isa ecbRestore s = some s' ∧ (∀ i < 4, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 4, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, -, wr₁, -, -⟩ := ldE_ok s .ebx .edi (k := Impl.Sm4.X86.slots) hb (by decide) hw
  obtain ⟨s₂, e₂, v₂, o₂, m₂, -, wr₂, -, -⟩ := ldE_ok s₁ .esi .edi (k := Impl.Sm4.X86.slots + 1)
    (by rw [o₁ _ (by decide), hb]) (by decide) (by rw [wr₁]; exact hw)
  obtain ⟨s₃, e₃, v₃, o₃, m₃, -, wr₃, -, -⟩ := ldE_ok s₂ .ebp .edi (k := Impl.Sm4.X86.slots + 3)
    (by rw [o₂ _ (by decide), o₁ _ (by decide), hb]) (by decide) (by rw [wr₂, wr₁]; exact hw)
  obtain ⟨s₄, e₄, v₄, o₄, m₄, -, -, -, -⟩ := ldE_ok s₃ .edi .edi (k := Impl.Sm4.X86.slots + 2)
    (by rw [o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide), hb]) (by decide) (by rw [wr₃, wr₂, wr₁]; exact hw)
  refine ⟨s₄, ?_, fun i hi => ?_, fun r hr => ?_, by rw [m₄, m₃, m₂, m₁]⟩
  · rw [show ecbRestore = [.mov .ebx (.mem (slotAt .edi Impl.Sm4.X86.slots))] ++ ([.mov .esi (.mem (slotAt .edi (Impl.Sm4.X86.slots + 1)))] ++
        ([.mov .ebp (.mem (slotAt .edi (Impl.Sm4.X86.slots + 3)))] ++ [.mov .edi (.mem (slotAt .edi (Impl.Sm4.X86.slots + 2)))])) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_using [hi]) with rfl | rfl | rfl | rfl
    · show s₄.gpr .ebx = _
      rw [o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), v₁]; exact hs 0 (by decide)
    · show s₄.gpr .esi = _
      rw [o₄ _ (by decide), o₃ _ (by decide), v₂, m₁]; exact hs 1 (by decide)
    · show s₄.gpr .edi = _
      rw [v₄, m₃, m₂, m₁]; exact hs 2 (by decide)
    · show s₄.gpr .ebp = _
      rw [o₄ _ (by decide), v₃, m₂, m₁]; exact hs 3 (by decide)
  · rw [o₄ r (hr 2 (by decide)), o₃ r (hr 3 (by decide)), o₂ r (hr 1 (by decide)), o₁ r (hr 0 (by decide))]

/-! ## The scratch buffer's contents -/

/-- What the data loop keeps in the scratch buffer: the table and the saved
registers. -/
structure ScrOkE (s₀ : State) (b : BitVec 32) (E : Nat → Spec.Sm4.Word) (m : Mem) : Prop where
  keys : ∀ e < 32, W32.WordRel (entryW m b e) fun _ => E e
  saved : ESaved s₀ b m

/-- The table's Impl.Sm4.X86.slots, and the saved registers'. -/
abbrev keyR (b : BitVec 32) : Region := slotsRegion b tableSlot tableEnd
abbrev savR (b : BitVec 32) : Region := slotsRegion b Impl.Sm4.X86.slots (Impl.Sm4.X86.slots + 4)

theorem ScrOkE.frame {s₀ : State} {b : BitVec 32} {E : Nat → Spec.Sm4.Word} {m m' : Mem}
    (h : ScrOkE s₀ b E m) (hfit : b.toNat + 4 * 368 ≤ 2 ^ 32) {rs : List Region}
    (hf : Frame rs m m') (hk : ∀ r ∈ rs, (keyR b).Disjoint r) (hs : ∀ r ∈ rs, (savR b).Disjoint r) :
    ScrOkE s₀ b E m' := by
  refine ⟨fun e he => (h.keys e he).congr fun j hj => ?_, fun i hi => ?_⟩
  · exact slotE_keep hfit (by decide) hf hk (by omega_using []) (by rw [tableEnd_eq, tableSlot_eq]; omega_using [he, hj])
  · rw [← h.saved i hi]
    exact slotE_keep hfit (by decide) hf hs (by omega_using []) (by omega_using [hi])

/-- The regions within the Impl.Sm4.X86.slots from the tail buffer to the table's start,
or after the saved registers, keep the table and the saved registers. -/
theorem keyR_disj {b : BitVec 32} {lo hi : Nat} (hlh : lo ≤ hi) (hhi : hi ≤ 368)
    (h : hi ≤ tableSlot ∨ (Impl.Sm4.X86.slots + 4 ≤ lo)) : (keyR b).Disjoint (slotsRegion b lo hi) ∧ (savR b).Disjoint (slotsRegion b lo hi) := by
  rw [tableSlot_eq, slots_eq] at h
  refine ⟨VG.Offset.disjoint _ (by simp only [tableSlot_eq, tableEnd_eq]; omega_using [h, hlh])
    (by simp only [tableSlot_eq, tableEnd_eq]; omega_using []) (by omega_using [hhi, hlh]), ?_⟩
  exact VG.Offset.disjoint _ (by simp only [slots_eq]; omega_using [h, hlh]) (by simp only [slots_eq]; omega_using [])
    (by omega_using [hhi, hlh])

theorem dnE_sub {b : BitVec 32} (hfit : b.toNat + 4 * 368 ≤ 2 ^ 32) :
    ∀ r ∈ [(⟨wordAddr b modeDSlot, 4⟩ : Region), ⟨wordAddr b modeNSlot, 4⟩],
      Region.Sub r ⟨b.setWidth 64, 4 * 368⟩ := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact slotE_sub hfit modeDSlot_lt
  · exact slotE_sub hfit modeNSlot_lt

theorem dnE_disj {b : BitVec 32} (hfit : b.toNat + 4 * 368 ≤ 2 ^ 32) :
    (∀ r ∈ [(⟨wordAddr b modeDSlot, 4⟩ : Region), ⟨wordAddr b modeNSlot, 4⟩], (keyR b).Disjoint r) ∧
    (∀ r ∈ [(⟨wordAddr b modeDSlot, 4⟩ : Region), ⟨wordAddr b modeNSlot, 4⟩], (savR b).Disjoint r) := by
  obtain ⟨k₁, s₁⟩ := keyR_disj (b := b) (lo := modeDSlot) (hi := modeDSlot + 1) (by decide) (by decide) (.inr (by decide))
  obtain ⟨k₂, s₂⟩ := keyR_disj (b := b) (lo := modeNSlot) (hi := modeNSlot + 1) (by decide) (by decide) (.inr (by decide))
  have eD : (⟨wordAddr b modeDSlot, 4⟩ : Region) = slotsRegion b modeDSlot (modeDSlot + 1) := by
    rw [slot_addr (by rw [modeDSlot_eq]; omega_arith)]; rfl
  have eN : (⟨wordAddr b modeNSlot, 4⟩ : Region) = slotsRegion b modeNSlot (modeNSlot + 1) := by
    rw [slot_addr (by rw [modeNSlot_eq]; omega_arith)]; rfl
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩ <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hr <;>
    rcases hr with rfl | rfl
  · rw [eD]; exact k₁
  · rw [eN]; exact k₂
  · rw [eD]; exact s₁
  · rw [eN]; exact s₂

/-! ## A batch -/

/-- `vg_sm4_crypt_prepared` on the tail buffer of ECB's working space, under
the table of the round keys `K` in `d`'s order. -/
theorem cryptE_wp (d : Dir) {s : State} {b : BitVec 32} {K : Spec.Sm4.Schedule} (hb : s.gpr .edi = b)
    (hw : EIn s.wr b) (hk : ∀ e < 32, W32.WordRel (entryW s.mem b e) fun _ => dirKeys d K e)
    (hstk : Region.Disjoint (stkRegion (s.gpr .esp) 20) ⟨b.setWidth 64, 4 * 368⟩) (hlo : 20 ≤ (s.gpr .esp).toNat) :
    WP isa cryptCall s fun s' => s'.gpr .edi = b ∧ s'.gpr .esp = s.gpr .esp ∧
      (∀ e < 32, W32.WordRel (entryW s'.mem b e) fun _ => dirKeys d K e) ∧
      Frame [⟨b.setWidth 64, 4 * Impl.Sm4.X86.slots⟩, stkRegion (s.gpr .esp) 20] s.mem s'.mem ∧
      (∀ j < 8, tailBlock s' j = outBlock (quads .enc (dirKeys d K) 8 (ofBlock (tailBlock s j)))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.mono (crypt_wp d (B := b) (k := K) hb ⟨hw.mem, hw.fit⟩ ⟨hk, hw.fit, hstk⟩ hlo)
    fun s' ⟨b', e', ⟨r', _, _⟩, f', h', rd', wr'⟩ => ⟨b', e', r', f', fun j hj => ?_, rd', wr'⟩
  have := h' j hj
  rw [show 4 * (dirCore d).bw = 16 from rfl, dirCipher_bytes, bytesAt_eq_blockAt] at this
  have e := Vector.toList_inj.mp this
  have ea : ∀ t : State, t.gpr sb = b →
      (t.gpr sb).setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + 16 * j) = Proof.Modes.X86.blkAddr (dirCore d) b j :=
    fun t ht => by
      rw [ht]; simp only [Proof.Modes.X86.blkAddr, Proof.Modes.X86.slotA, dirCore, VG.Offset.add_add]
  simp only [tailBlock]
  rw [ea s' b', ea s hb]
  exact e

/-! ## The data loop -/

/-- The scratch buffer at `b`, the `n` blocks at `D`, and the stack below
`esp` the calls use. -/
structure GPre (s₀ : State) (b D : BitVec 32) (n : Nat) : Prop where
  scr : EIn s₀.wr b
  dat : (⟨D.setWidth 64, 16 * n⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨D.setWidth 64, 16 * n⟩ ⟨b.setWidth 64, 4 * 368⟩
  fitD : D.toNat + 16 * n ≤ 2 ^ 32
  stkS : Region.Disjoint (stkRegion (s₀.gpr .esp) 20) ⟨b.setWidth 64, 4 * 368⟩
  stkD : Region.Disjoint (stkRegion (s₀.gpr .esp) 20) ⟨D.setWidth 64, 16 * n⟩
  lo : 20 ≤ (s₀.gpr .esp).toNat

/-- The data loop, before group `k`. -/
structure GInv (s₀ : State) (b D : BitVec 32) (n : Nat) (E : Nat → Spec.Sm4.Word) (k : Nat) (s : State) :
    Prop where
  base : s.gpr .edi = b
  esp : s.gpr .esp = s₀.gpr .esp
  dp : s.mem.readW (wordAddr b modeDSlot) 32 = D + BitVec.ofNat 32 (128 * k)
  np : s.mem.readW (wordAddr b modeNSlot) 32 = BitVec.ofNat 32 (n - 8 * k)
  lt : 8 * k < n
  scr : ScrOkE s₀ b E s.mem
  data : DInv s₀.mem s.mem (D.setWidth 64) n (8 * k) (outF s₀.mem (D.setWidth 64) E)
  frame : Frame [⟨b.setWidth 64, 4 * 368⟩, ⟨D.setWidth 64, 16 * n⟩, stkRegion (s₀.gpr .esp) 20] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure GDone (s₀ : State) (b D : BitVec 32) (n : Nat) (E : Nat → Spec.Sm4.Word) (s : State) : Prop where
  base : s.gpr .edi = b
  esp : s.gpr .esp = s₀.gpr .esp
  scr : ScrOkE s₀ b E s.mem
  data : DInv s₀.mem s.mem (D.setWidth 64) n n (outF s₀.mem (D.setWidth 64) E)
  frame : Frame [⟨b.setWidth 64, 4 * 368⟩, ⟨D.setWidth 64, 16 * n⟩, stkRegion (s₀.gpr .esp) 20] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem dataGroup_wp (dir : Dir) {K : Spec.Sm4.Schedule} {s₀ : State} {b D : BitVec 32} {n : Nat}
    (hp : GPre s₀ b D n) {k : Nat} {s : State} (hi : GInv s₀ b D n (dirKeys dir K) k s) :
    WP isa group s fun s' => (s'.zf = some true ∧ GDone s₀ b D n (dirKeys dir K) s') ∨
      (s'.zf = some false ∧ GInv s₀ b D n (dirKeys dir K) (k + 1) s') := by
  let E := dirKeys dir K
  have hfit : b.toNat + 4 * 368 ≤ 2 ^ 32 := hp.scr.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  obtain hb := setWidth_toNat b
  obtain hfit' : b.toNat + 4 * Impl.Sm4.X86.slots ≤ 2 ^ 32 := hp.scr.fit'
  let v := n - 8 * k
  let c := min v 8
  obtain hv : v < 2 ^ 32 := by omega_arith
  obtain hc0 : 0 < c := by omega_arith
  obtain hc8 : c ≤ 8 := by omega_arith
  obtain hkc : 128 * k + 16 * c ≤ 16 * n := by omega_arith
  let A := D + BitVec.ofNat 32 (128 * k)
  let T := b + BitVec.ofNat 32 (4 * tailSlot)
  obtain hA : A.setWidth 64 = D.setWidth 64 + BitVec.ofNat 64 (128 * k) := setWidth_add (by omega_arith)
  obtain hT : T.setWidth 64 = b.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot) :=
    setWidth_add (by rw [tailSlot_eq]; omega_arith)
  obtain hAn : A.toNat + 16 * c ≤ 2 ^ 32 := by rw [toNat_add32 _ (by omega_arith)]; omega_arith
  obtain hTn : T.toNat + 16 * c ≤ 2 ^ 32 := by rw [toNat_add32 _ (by rw [tailSlot_eq]; omega_arith), tailSlot_eq]; omega_arith
  obtain hwE : EIn s.wr b := by rw [hi.wr]; exact hp.scr
  obtain hwS : ScrIn s.wr b := hwE.scr
  obtain hwD : (⟨D.setWidth 64, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  obtain inT : ∀ t < 16 * c, t % 4 = 0 → InRegions s.wr (T.setWidth 64 + BitVec.ofNat 64 t) 4 := by
    intro t ht h4
    refine ⟨_, hwE.mem, ?_⟩
    rw [hT, VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by rw [tailSlot_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  obtain inA : ∀ t < 16 * c, t % 4 = 0 → InRegions s.wr (A.setWidth 64 + BitVec.ofNat 64 t) 4 := by
    intro t ht h4
    refine ⟨_, hwD, ?_⟩
    rw [hA, VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain subA : Region.Sub ⟨A.setWidth 64, 16 * c⟩ ⟨D.setWidth 64, 16 * n⟩ := by
    rw [hA]; exact VG.Offset.sub_base _ (by omega_arith)
  obtain subT : Region.Sub ⟨T.setWidth 64, 16 * c⟩ ⟨b.setWidth 64, 4 * 368⟩ := by
    rw [hT]; exact VG.Offset.sub_base _ (by rw [tailSlot_eq]; omega_arith)
  obtain sepAT : Region.Disjoint ⟨A.setWidth 64, 16 * c⟩ ⟨T.setWidth 64, 16 * c⟩ :=
    (hp.sep.sub_left subA).sub_right subT
  -- The regions the steps write keep the table and the saved registers.
  obtain subK : (keyR b).Sub ⟨b.setWidth 64, 4 * 368⟩ :=
    VG.Offset.sub_base _ (by simp only [tableSlot_eq, tableEnd_eq]; omega_arith)
  obtain subS : (savR b).Sub ⟨b.setWidth 64, 4 * 368⟩ :=
    VG.Offset.sub_base _ (by simp only [slots_eq]; omega_arith)
  obtain ⟨dTk, dTs⟩ : (keyR b).Disjoint ⟨T.setWidth 64, 16 * c⟩ ∧ (savR b).Disjoint ⟨T.setWidth 64, 16 * c⟩ := by
    obtain ⟨h1, h2⟩ := keyR_disj (b := b) (lo := tailSlot) (hi := tailSlot + 32) (by decide) (by decide) (.inl (by decide))
    obtain sT : Region.Sub ⟨T.setWidth 64, 16 * c⟩ (slotsRegion b tailSlot (tailSlot + 32)) := by
      rw [hT]; exact VG.Offset.sub _ (Nat.le_refl _) (by omega_arith)
    exact ⟨h1.sub_right sT, h2.sub_right sT⟩
  obtain dAk : (keyR b).Disjoint ⟨A.setWidth 64, 16 * c⟩ := ((hp.sep.sub_left subA).sub_right subK).symm
  obtain dAs : (savR b).Disjoint ⟨A.setWidth 64, 16 * c⟩ := ((hp.sep.sub_left subA).sub_right subS).symm
  obtain dD : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨b.setWidth 64, 4 * 368⟩) →
      ∀ r ∈ rs, Region.Disjoint ⟨D.setWidth 64, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
  obtain hsub := dnE_sub hfit
  obtain ⟨dsK, dsS⟩ := dnE_disj hfit
  unfold group copyIn
  -- The group's blocks to the tail buffer.
  refine WP.seq (WP.seq (WP.mono (groupCount_wp hi.base hwE hi.dp hi.np hv)
    fun s₁ ⟨esi₁, ebp₁, ecx₁, o₁, m₁, rd₁, wr₁⟩ => ?_))
  obtain ⟨s₂a, e₂a, r₂a, o₂a, m₂a, rd₂a, wr₂a, -, -⟩ := movR_ok s₁ .edx .esi
  obtain ⟨s₂b, e₂b, r₂b, o₂b, m₂b, rd₂b, wr₂b, -, -⟩ := movR_ok s₂a .ebx .edi
  obtain ⟨s₂, e₂, r₂, -, o₂, m₂, rd₂, wr₂⟩ := addI_ok s₂b .ebx (BitVec.ofNat 32 (4 * tailSlot))
  obtain rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₂b, rd₂a, rd₁]
  obtain wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₂b, wr₂a, wr₁]
  obtain mem₂ : s₂.mem = s.mem := by rw [m₂, m₂b, m₂a, m₁]
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [tailAddr, show ([movR .edx .esi] ++ [movR .ebx .edi, addI .ebx (BitVec.ofNat 32 (4 * tailSlot))] :
        List Instr) = [movR .edx .esi] ++ ([movR .ebx .edi] ++ [addI .ebx (BitVec.ofNat 32 (4 * tailSlot))])
        from rfl, runBlock_app, e₂a, Option.bind_some, runBlock_app, e₂b, Option.bind_some, e₂], ?_⟩)
  refine WP.seq (WP.mono (copyBlocks_wp (A := A) (B := T) hc0 hc8 hAn hTn
    (fun t ht h4 => by rw [rd₂', wr₂']; exact inRd (inA t ht h4))
    (fun t ht h4 => by rw [wr₂']; exact inT t ht h4) sepAT
    ⟨by rw [o₂ _ (by decide), o₂b _ (by decide), r₂a, esi₁]; simp [A],
      by rw [r₂, r₂b, o₂a _ (by decide), o₁ _ (by decide) (by decide) (by decide), hi.base]; simp [T],
      by rw [o₂ _ (by decide), o₂b _ (by decide), o₂a _ (by decide), ecx₁, Nat.sub_zero],
      ⟨fun t ht => by omega_arith, Frame.refl _ _⟩, fun _ _ _ _ _ => rfl, rfl, rfl⟩) fun s₃ h₃ => ?_)
  obtain f₃ : Frame [⟨T.setWidth 64, 16 * c⟩] s.mem s₃.mem := by rw [← mem₂]; exact h₃.cp.frame
  obtain g₃ : ∀ r, r ≠ .edx → r ≠ .ebx → r ≠ .ecx → r ≠ .eax → s₃.gpr r = s₁.gpr r :=
    fun r h0 h1 h2 h3 => by rw [h₃.regs r h0 h1 h2 h3, o₂ r h1, o₂b r h1, o₂a r h0]
  obtain base₃ : s₃.gpr .edi = b := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide), o₁ _ (by decide) (by decide) (by decide), hi.base]
  obtain esp₃ : s₃.gpr .esp = s₀.gpr .esp := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide), o₁ _ (by decide) (by decide) (by decide), hi.esp]
  obtain sc₃ : ScrOkE s₀ b E s₃.mem := hi.scr.frame hfit f₃
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dTk)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dTs)
  obtain wr₃ : s₃.wr = s.wr := by rw [h₃.wr, wr₂']
  obtain rd₃ : s₃.rd = s.rd := by rw [h₃.rd, rd₂']
  obtain hwE₃ : EIn s₃.wr b := by rw [wr₃]; exact hwE
  -- The data pointer and the blocks left back to their Impl.Sm4.X86.slots.
  obtain ⟨s₄, e₄, dp₄, np₄, g₄, rd₄, wr₄, -, fs⟩ := stDN_ok s₃ base₃ hwE₃
  refine WP.of_runBlock ⟨s₄, e₄, ?_⟩
  obtain esi₃ : s₃.gpr .esi = A := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), esi₁]
  obtain ebp₃ : s₃.gpr .ebp = BitVec.ofNat 32 v := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide), ebp₁]
  rw [esi₃] at dp₄
  rw [ebp₃] at np₄
  obtain sc₄ : ScrOkE s₀ b E s₄.mem := sc₃.frame hfit fs dsK dsS
  obtain base₄ : s₄.gpr .edi = b := by rw [g₄]; exact base₃
  obtain esp₄ : s₄.gpr .esp = s₀.gpr .esp := by rw [g₄]; exact esp₃
  obtain wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃]
  -- The eight blocks.
  refine WP.seq (WP.mono (cryptE_wp dir (K := K) base₄ (by rw [wr₄']; exact hwE) sc₄.keys
    (by rw [esp₄]; exact hp.stkS) (by rw [esp₄]; exact hp.lo))
    fun s₅ ⟨base₅, esp₅, keys₅, f₅, b₅, rd₅', wr₅'⟩ => ?_)
  rw [esp₄] at f₅
  obtain dCore : (savR b).Disjoint ⟨b.setWidth 64, 4 * Impl.Sm4.X86.slots⟩ :=
    VG.Offset.disjoint_base _ (by omega_arith) (by simp only [slots_eq]; omega_arith)
  obtain f₅k : ∀ r ∈ [(⟨b.setWidth 64, 4 * Impl.Sm4.X86.slots⟩ : Region), stkRegion (s₀.gpr .esp) 20],
      Region.Disjoint ⟨wordAddr b modeDSlot, 8⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [slot_addr (by rw [modeDSlot_eq]; omega_arith)]
    rcases hr with rfl | rfl
    · exact VG.Offset.disjoint_base _ (by rw [modeDSlot_eq, slots_eq]; omega_arith) (by rw [modeDSlot_eq]; omega_arith)
    · exact (hp.stkS.sub_right (VG.Offset.sub_base _ (by rw [modeDSlot_eq]; omega_arith))).symm
  obtain keep₅ : ∀ j, modeDSlot ≤ j → j < modeDSlot + 2 →
      s₅.mem.readW (wordAddr b j) 32 = s₄.mem.readW (wordAddr b j) 32 :=
    fun j h1 h2 => slotE_keep hfit (lo := modeDSlot) (hi := modeDSlot + 2) (by decide) f₅ (fun r hr => by
      have := f₅k r hr
      rwa [slot_addr (by rw [modeDSlot_eq]; omega_arith)] at this) h1 h2
  obtain sc₅ : ScrOkE s₀ b E s₅.mem := ⟨keys₅, fun i hi' => by
    rw [← sc₄.saved i hi']
    refine slotE_keep hfit (lo := Impl.Sm4.X86.slots) (hi := Impl.Sm4.X86.slots + 4) (by decide) f₅ (fun r hr => ?_) (by omega_using [])
      (by omega_using [hi'])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dCore
    · exact (hp.stkS.sub_right subS).symm⟩
  obtain wr₅ : s₅.wr = s.wr := by rw [wr₅', wr₄']
  obtain rd₅ : s₅.rd = s.rd := by rw [rd₅', rd₄, rd₃]
  obtain hwE₅ : EIn s₅.wr b := by rw [wr₅]; exact hwE
  obtain hwS₅ : ScrIn s₅.wr b := hwE₅.scr
  -- The tail buffer back to the group's blocks.
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp (A := A) base₅ hwE₅
    (by rw [keep₅ _ (Nat.le_refl _) (by omega_using [])]; exact dp₄)
    (by rw [keep₅ _ (by decide) (by decide)]; exact np₄) hv)
    fun s₆ ⟨esi₆, ebp₆, ecx₆, o₆, m₆, rd₆, wr₆⟩ => ?_))
  obtain ⟨s₇a, e₇a, r₇a, o₇a, m₇a, rd₇a, wr₇a, -, -⟩ := movR_ok s₆ .edx .edi
  obtain ⟨s₇b, e₇b, r₇b, -, o₇b, m₇b, rd₇b, wr₇b⟩ := addI_ok s₇a .edx (BitVec.ofNat 32 (4 * tailSlot))
  obtain ⟨s₇, e₇, r₇, o₇, m₇, rd₇, wr₇, -, -⟩ := movR_ok s₇b .ebx .esi
  obtain mem₇ : s₇.mem = s₅.mem := by rw [m₇, m₇b, m₇a, m₆]
  obtain rd₇' : s₇.rd = s.rd := by rw [rd₇, rd₇b, rd₇a, rd₆, rd₅]
  obtain wr₇' : s₇.wr = s.wr := by rw [wr₇, wr₇b, wr₇a, wr₆, wr₅]
  refine WP.seq (WP.of_runBlock ⟨s₇, by
    rw [tailAddr, show ([movR .edx .edi, addI .edx (BitVec.ofNat 32 (4 * tailSlot))] ++ [movR .ebx .esi] :
        List Instr) = [movR .edx .edi] ++ ([addI .edx (BitVec.ofNat 32 (4 * tailSlot))] ++ [movR .ebx .esi])
        from rfl, runBlock_app, e₇a, Option.bind_some, runBlock_app, e₇b, Option.bind_some, e₇], ?_⟩)
  refine WP.mono (copyBlocks_wp (A := T) (B := A) hc0 hc8 hTn hAn
    (fun t ht h4 => by rw [rd₇', wr₇']; exact inRd (inT t ht h4))
    (fun t ht h4 => by rw [wr₇']; exact inA t ht h4) sepAT.symm
    ⟨by rw [o₇ _ (by decide), r₇b, r₇a, o₆ _ (by decide) (by decide) (by decide), base₅]; simp [T],
      by rw [r₇, o₇b _ (by decide), o₇a _ (by decide), esi₆]; simp [A],
      by rw [o₇ _ (by decide), o₇b _ (by decide), o₇a _ (by decide), ecx₆, Nat.sub_zero],
      ⟨fun t ht => by omega_arith, Frame.refl _ _⟩, fun _ _ _ _ _ => rfl, rfl, rfl⟩) fun s₈ h₈ => ?_
  obtain f₈ : Frame [⟨A.setWidth 64, 16 * c⟩] s₅.mem s₈.mem := by rw [← mem₇]; exact h₈.cp.frame
  obtain g₈ : ∀ r, r ≠ .edx → r ≠ .ebx → r ≠ .ecx → r ≠ .eax → s₈.gpr r = s₆.gpr r :=
    fun r h0 h1 h2 h3 => by rw [h₈.regs r h0 h1 h2 h3, o₇ r h1, o₇b r h0, o₇a r h0]
  obtain sc₈ : ScrOkE s₀ b E s₈.mem := sc₅.frame hfit f₈
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dAk)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dAs)
  obtain wr₈ : s₈.wr = s.wr := by rw [h₈.wr, wr₇']
  obtain rd₈ : s₈.rd = s.rd := by rw [h₈.rd, rd₇']
  -- The blocks the batch read are the group's, as on entry.
  obtain hblk : ∀ j < c, tailBlock s₄ j =
      Spec.Sm4.blockAt s₀.mem (D.setWidth 64 + BitVec.ofNat 64 (16 * (8 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [tailBlock, Spec.Sm4.blockAt, Vector.getElem_ofFn]
    have := h₃.cp.copied (16 * j + u) (by omega_arith)
    rw [hT, VG.Offset.add_add, hA, VG.Offset.add_add] at this
    obtain hout : ∀ r ∈ [(⟨wordAddr b modeDSlot, 4⟩ : Region), ⟨wordAddr b modeNSlot, 4⟩],
        ¬ r.Contains (b.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + (16 * j + u))) 1 := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> rw [slot_addr (by (try simp only [modeDSlot_eq, modeNSlot_eq]); omega_arith)] <;>
        exact not_contains_off _ (by (try simp only [tailSlot_eq, modeDSlot_eq, modeNSlot_eq]); omega_arith)
          (by rw [tailSlot_eq]; omega_arith) (by omega_arith) (by (try simp only [modeDSlot_eq, modeNSlot_eq]); omega_arith)
    rw [show s₄.gpr sb = b from base₄, VG.Offset.add_add, show 4 * tailSlot + 16 * j + u = 4 * tailSlot + (16 * j + u) by omega_arith,
      fs _ hout, this, mem₂, hi.data _ (by omega_arith), ite_eq_right (by omega_arith), VG.Offset.add_add,
      show 128 * k + (16 * j + u) = 16 * (8 * k + j) + u by omega_arith]
  obtain hdata : DInv s₀.mem s₈.mem (D.setWidth 64) n (8 * k + c) (outF s₀.mem (D.setWidth 64) E) := by
    intro i hin
    by_cases hin1 : 128 * k ≤ i ∧ i < 128 * k + 16 * c
    · have e1 : D.setWidth 64 + BitVec.ofNat 64 i = A.setWidth 64 + BitVec.ofNat 64 (i - 128 * k) := by
        rw [hA, VG.Offset.add_add, show 128 * k + (i - 128 * k) = i by omega_arith]
      rw [e1, h₈.cp.copied _ (by omega_arith), mem₇, ite_eq_left (show i < 16 * (8 * k + c) by omega_arith),
        show i / 16 = 8 * k + (i - 128 * k) / 16 by omega_arith, show i % 16 = (i - 128 * k) % 16 by omega_arith]
      obtain hj : (i - 128 * k) / 16 < c := by omega_arith
      obtain eT : T.setWidth 64 + BitVec.ofNat 64 (i - 128 * k) =
          (s₅.gpr sb).setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + 16 * ((i - 128 * k) / 16)) +
            BitVec.ofNat 64 ((i - 128 * k) % 16) := by
        rw [show s₅.gpr sb = b from base₅, hT, VG.Offset.add_add, VG.Offset.add_add,
          show 4 * tailSlot + 16 * ((i - 128 * k) / 16) + (i - 128 * k) % 16 = 4 * tailSlot + (i - 128 * k) by omega_arith]
      rw [eT, ← blockAt_getD s₅.mem _ (Nat.mod_lt _ (by decide))]
      show (tailBlock s₅ _).getD _ 0 = _
      rw [b₅ _ (by omega_arith), hblk _ hj]
      rfl
    · have hout : ∀ r ∈ [(⟨A.setWidth 64, 16 * c⟩ : Region)],
          ¬ r.Contains (D.setWidth 64 + BitVec.ofNat 64 i) 1 := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hA]
        exact not_contains_off _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      rw [f₈ _ hout,
        f₅.bytes (R := ⟨D.setWidth 64, 16 * n⟩) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hp.sep.sub_right (Region.sub_prefix (by rw [slots_eq]; omega_arith))
          · exact hp.stkD.symm) (by simp only; omega_arith) hin,
        fs.bytes (R := ⟨D.setWidth 64, 16 * n⟩) (dD hsub) (by simp only; omega_arith) hin,
        f₃.bytes (R := ⟨D.setWidth 64, 16 * n⟩) (dD fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subT) (by simp only; omega_arith) hin,
        hi.data i hin]
      by_cases h2 : i < 128 * k
      · rw [ite_eq_left (show i < 16 * (8 * k) by omega_arith), ite_eq_left (show i < 16 * (8 * k + c) by omega_arith)]
      · rw [ite_eq_right (show ¬ i < 16 * (8 * k) by omega_arith), ite_eq_right (show ¬ i < 16 * (8 * k + c) by omega_arith)]
  -- On to the next group.
  obtain esi₈ : s₈.gpr .esi = A := by rw [g₈ _ (by decide) (by decide) (by decide) (by decide), esi₆]
  obtain ebp₈ : s₈.gpr .ebp = BitVec.ofNat 32 v := by
    rw [g₈ _ (by decide) (by decide) (by decide) (by decide), ebp₆]
  unfold advance
  refine WP.seq (WP.mono (countR_wp ebp₈ hv) fun s₉ ⟨ecx₉, o₉, m₉, rd₉, wr₉⟩ => ?_)
  obtain ⟨s₁₀a, e₁₀a, r₁₀a, -, o₁₀a, m₁₀a, rd₁₀a, wr₁₀a⟩ := addI_ok s₉ .esi 128
  obtain ⟨s₁₀b, e₁₀b, r₁₀b, z₁₀b, o₁₀b, m₁₀b, rd₁₀b, wr₁₀b⟩ := subI_ok s₁₀a .ebp (s₁₀a.gpr .ecx)
  obtain base₁₀b : s₁₀b.gpr .edi = b := by
    rw [o₁₀b _ (by decide), o₁₀a _ (by decide), o₉ _ (by decide),
      g₈ _ (by decide) (by decide) (by decide) (by decide), o₆ _ (by decide) (by decide) (by decide), base₅]
  obtain esp₁₀b : s₁₀b.gpr .esp = s₀.gpr .esp := by
    rw [o₁₀b _ (by decide), o₁₀a _ (by decide), o₉ _ (by decide),
      g₈ _ (by decide) (by decide) (by decide) (by decide), o₆ _ (by decide) (by decide) (by decide), esp₅, esp₄]
  obtain wr₁₀b' : s₁₀b.wr = s.wr := by rw [wr₁₀b, wr₁₀a, wr₉, wr₈]
  obtain ⟨s₁₀, e₁₀, dp₁₀, np₁₀, g₁₀, rd₁₀, wr₁₀, z₁₀, fa⟩ := stDN_ok s₁₀b base₁₀b (by rw [wr₁₀b']; exact hwE)
  refine WP.of_runBlock ⟨s₁₀, by
    rw [show ([addI .esi 128, subR .ebp .ecx, st modeDSlot .esi, st modeNSlot .ebp] : List Instr) =
      [addI .esi 128] ++ ([subR .ebp .ecx] ++ [st modeDSlot .esi, st modeNSlot .ebp]) from rfl,
      runBlock_app, e₁₀a, Option.bind_some, runBlock_app,
      show runBlock isa [subR .ebp .ecx] s₁₀a = runBlock isa [subI .ebp (s₁₀a.gpr .ecx)] s₁₀a from rfl,
      e₁₀b, Option.bind_some, e₁₀], ?_⟩
  obtain ecx₁₀a : s₁₀a.gpr .ecx = BitVec.ofNat 32 c := by rw [o₁₀a _ (by decide), ecx₉]
  obtain ebp₁₀a : s₁₀a.gpr .ebp = BitVec.ofNat 32 v := by rw [o₁₀a _ (by decide), o₉ _ (by decide), ebp₈]
  obtain zz : s₁₀.zf = some (decide (v = c)) := by
    rw [z₁₀, z₁₀b, ebp₁₀a, ecx₁₀a, ofNat32_sub_beq (by omega_arith) (by omega_arith)]
  obtain hmem : ∀ i < 16 * n, s₁₀.mem (D.setWidth 64 + BitVec.ofNat 64 i) = s₈.mem (D.setWidth 64 + BitVec.ofNat 64 i) :=
    fun i hi' => by
      rw [fa.bytes (R := ⟨D.setWidth 64, 16 * n⟩) (dD hsub) (by simp only; omega_arith) hi', m₁₀b, m₁₀a, m₉]
  obtain hdata' : DInv s₀.mem s₁₀.mem (D.setWidth 64) n (8 * k + c) (outF s₀.mem (D.setWidth 64) E) :=
    fun i hi' => by rw [hmem i hi']; exact hdata i hi'
  obtain mem₉' : s₁₀b.mem = s₈.mem := by rw [m₁₀b, m₁₀a, m₉]
  obtain sc₁₀ : ScrOkE s₀ b E s₁₀.mem := (mem₉' ▸ sc₈).frame hfit fa dsK dsS
  obtain base₁₀ : s₁₀.gpr .edi = b := by rw [g₁₀]; exact base₁₀b
  obtain esp₁₀ : s₁₀.gpr .esp = s₀.gpr .esp := by rw [g₁₀]; exact esp₁₀b
  obtain rd₁₀' : s₁₀.rd = s₀.rd := by rw [rd₁₀, rd₁₀b, rd₁₀a, rd₉, rd₈, hi.rd]
  obtain wr₁₀' : s₁₀.wr = s₀.wr := by rw [wr₁₀, wr₁₀b', hi.wr]
  obtain fr : Frame [⟨b.setWidth 64, 4 * 368⟩, ⟨D.setWidth 64, 16 * n⟩, stkRegion (s₀.gpr .esp) 20]
      s₀.mem s₁₀.mem := by
    refine hi.frame.trans ((f₃.sub fun r hr => ⟨⟨b.setWidth 64, 4 * 368⟩, List.mem_cons_self, ?_⟩).trans
      ((fs.sub fun r hr => ⟨⟨b.setWidth 64, 4 * 368⟩, List.mem_cons_self, hsub r hr⟩).trans
      ((f₅.sub fun r hr => ?_).trans
      ((f₈.sub fun r hr => ⟨⟨D.setWidth 64, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩).trans
      (mem₉' ▸ fa.sub fun r hr => ⟨⟨b.setWidth 64, 4 * 368⟩, List.mem_cons_self, hsub r hr⟩)))))
    · simp only [List.mem_singleton] at hr; subst hr; exact subT
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by rw [slots_eq]; omega_arith)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact subA
  by_cases hlt : v ≤ 8
  · have hn : 8 * k + c = n := by omega_arith
    refine .inl ⟨by rw [zz]; simp; omega_arith, base₁₀, esp₁₀, sc₁₀, by have := hdata'; rw [hn] at this; exact this, fr, rd₁₀', wr₁₀'⟩
  · have hc : c = 8 := by omega_arith
    refine .inr ⟨by rw [zz]; simp; omega_arith, base₁₀, esp₁₀, ?_, ?_, by omega_arith, sc₁₀,
      by rw [show 8 * (k + 1) = 8 * k + c by omega_arith]; exact hdata', fr, rd₁₀', wr₁₀'⟩
    · rw [dp₁₀, o₁₀b _ (by decide), r₁₀a, o₉ _ (by decide), esi₈]
      simp only [A]
      rw [show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, VG.Offset.add_add,
        show 128 * k + 128 = 128 * (k + 1) by omega_arith]
    · rw [np₁₀, r₁₀b, ebp₁₀a, ecx₁₀a, VG.Offset.ofNat_sub_ofNat (by omega_arith), show v - c = n - 8 * (k + 1) by omega_arith]

/-- The data loop. -/
theorem dataLoop_wp (dir : Dir) {K : Spec.Sm4.Schedule} {s₀ : State} {b D : BitVec 32} {n : Nat}
    (hp : GPre s₀ b D n) {s : State} (hi : GInv s₀ b D n (dirKeys dir K) 0 s) :
    WP isa (.loop group .ne) s (GDone s₀ b D n (dirKeys dir K)) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - 8 * k ∧ GInv s₀ b D n (dirKeys dir K) k s) (fun m s hs => ?_) n s
    ⟨0, by omega_using [], hi⟩
  obtain ⟨k, rfl, hk⟩ := hs
  refine WP.mono (dataGroup_wp dir hp hk) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨(eval_ne s').trans (by rw [z]; rfl), d⟩
  · exact .inr ⟨(eval_ne s').trans (by rw [z]; rfl), n - 8 * (k + 1),
      by have := d.lt; have := hk.lt; omega_arith, k + 1, rfl, d⟩

/-! ## The function -/

/-- `mov eax, [esp + 4 + 4 i]; mov [edi + 4 k], eax`, a slot of ECB's buffer. -/
theorem argSlotE_ok (s : State) {b : BitVec 32} {i k : Nat} (hb : s.gpr .edi = b) (hk : k < 368)
    (hw : EIn s.wr b) (ha : InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4) :
    ∃ s', runBlock isa [.mov .eax (.mem (argOp i)), .store (slotAt .edi k) .eax] s = some s' ∧
      s'.gpr .eax = s.mem.readW (s.ea (argOp i)) 32 ∧ (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW (wordAddr b k) (s.mem.readW (s.ea (argOp i)) 32) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨wordAddr b k, 4⟩] s.mem s'.mem := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s .eax i ha
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, -, -, f₂⟩ := stE_ok s₁ .eax .edi (k := k) (by rw [o₁ _ (by decide), hb]) hk
    (by rw [wr₁]; exact hw)
  refine ⟨s₂, ?_, by rw [g₂, v₁], fun r hr => by rw [g₂, o₁ r hr], by rw [m₂, v₁, m₁], by rw [rd₂, rd₁],
    by rw [wr₂, wr₁], by rw [← m₁]; exact f₂⟩
  rw [show ([.mov .eax (.mem (argOp i)), .store (slotAt .edi k) .eax] : List Instr) =
    [.mov .eax (.mem (argOp i))] ++ [.store (slotAt .edi k) .eax] from rfl, runBlock_app, e₁, Option.bind_some, e₂]

/-- The stack the calls use is below the return address. -/
theorem stk_ret {E : BitVec 32} (hlo : 20 ≤ E.toNat) :
    Region.Disjoint (stkRegion E 20) ⟨E.setWidth 64, 4⟩ := by
  have e : (E - BitVec.ofNat 32 20).setWidth 64 = E.setWidth 64 - BitVec.ofNat 64 20 :=
    VG.X86.Taint.sub_setWidth hlo
  show Region.Disjoint ⟨(E - BitVec.ofNat 32 20).setWidth 64, 20⟩ _
  have := VG.Offset.disjoint_below_above (E.setWidth 64) (m := 20) (a := 0) (l := 4) (by decide)
  rw [BitVec.add_zero] at this
  rw [e]; exact this

theorem ecb_wp (dir : Dir) {s₀ : State} (hp : (ecbX86 dir).pre s₀) :
    WP isa (ecb dir) s₀ fun s' => abiPreserved s₀ s' ∧ (ecbX86 dir).post s₀ s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dDS, dAD, dAS, dRD, dRS, dSD, dSS, fitK, fitD, fitB, fitE, fitLo⟩ := hp
  let sched := arg s₀ 0
  let D := arg s₀ 1
  let n := (arg s₀ 2).toNat
  let b := arg s₀ 3
  have hfit : b.toNat + 4 * 368 ≤ 2 ^ 32 := fitB
  have hfit' : b.toNat + 4 * Impl.Sm4.X86.slots ≤ 2 ^ 32 := by rw [slots_eq]; omega_using [hfit]
  obtain hwE : EIn s₀.wr b := ⟨by rw [hwr]; simp [b], hfit⟩
  obtain hwS : ScrIn s₀.wr b := hwE.scr
  have dKS' : Region.Disjoint ⟨sched.setWidth 64, 128⟩ ⟨b.setWidth 64, 4 * 368⟩ := dKS
  have dDS' : Region.Disjoint ⟨D.setWidth 64, 16 * n⟩ ⟨b.setWidth 64, 4 * 368⟩ := dDS
  have dAS' : Region.Disjoint ⟨argAddr s₀ 0, 16⟩ ⟨b.setWidth 64, 4 * 368⟩ := dAS
  have dRS' : Region.Disjoint ⟨(s₀.gpr .esp).setWidth 64, 4⟩ ⟨b.setWidth 64, 4 * 368⟩ := dRS
  have dSS' : Region.Disjoint (stkRegion (s₀.gpr .esp) 20) ⟨b.setWidth 64, 4 * 368⟩ := dSS
  have dSD' : Region.Disjoint (stkRegion (s₀.gpr .esp) 20) ⟨D.setWidth 64, 16 * n⟩ := dSD
  obtain hwD : (⟨D.setWidth 64, 16 * n⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [D, n]
  obtain hrK : (⟨sched.setWidth 64, 128⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [sched]
  obtain hrA : (⟨argAddr s₀ 0, 16⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  -- The arguments, through writes of the scratch buffer.
  obtain argR : ∀ {m : Mem}, Frame [⟨b.setWidth 64, 4 * 368⟩] s₀.mem m → ∀ i < 4,
      m.readW (argAddr s₀ i) 32 = arg s₀ i := fun hf i hi =>
    hf.readW (arg_contains s₀ fitE hi) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dAS') (by decide)
  obtain argIn : ∀ {s : State}, s.rd = s₀.rd → s.wr = s₀.wr → s.gpr .esp = s₀.gpr .esp → ∀ i < 4,
      InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4 := fun h1 h2 h3 i hi => by
    rw [h1, h2, ea_arg h3]; exact ⟨_, List.mem_append_left _ hrA, arg_contains s₀ fitE hi⟩
  unfold ecb
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, rd₁, wr₁, f₁⟩ := entryE_ok hwE (argIn rfl rfl rfl 3 (by decide))
    (by rw [ea_arg rfl]; rfl)
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  obtain esp₁ : s₁.gpr .esp = s₀.gpr .esp := g₁ _ (by decide) (by decide)
  obtain hk₁ : SchedPre s₁ b sched :=
    ⟨b₁, by rw [wr₁]; exact hwS, List.mem_append_left _ (by rw [rd₁]; exact hrK), fitK,
      dKS'.sub_right (Region.sub_prefix (by rw [slots_eq]; omega_using []))⟩
  -- The table.
  refine WP.seq (WP.mono (keys_wp dir hk₁ (argIn rd₁ wr₁ esp₁ 0 (by decide))
    (by rw [ea_arg esp₁]; exact argR f₁ 0 (by decide))) fun s₂ k₂ => ?_)
  let K : Spec.Sm4.Schedule := Spec.Sm4.scheduleAt s₀.mem (sched.setWidth 64)
  let E : Nat → Spec.Sm4.Word := dirKeys dir K
  obtain hsch : Spec.Sm4.scheduleAt s₁.mem (sched.setWidth 64) = K := by
    have hb : ∀ k < 128, s₁.mem (sched.setWidth 64 + BitVec.ofNat 64 k) = s₀.mem (sched.setWidth 64 + BitVec.ofNat 64 k) :=
      fun k hk => f₁.bytes (R := ⟨sched.setWidth 64, 128⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dKS') (by show 128 ≤ 2 ^ 64; omega_arith) hk
    apply Vector.ext
    intro i hi
    simp only [K, Spec.Sm4.scheduleAt, Vector.getElem_ofFn, List.range, List.range.loop, List.foldl]
    rw [hb (4 * i + 0) (by omega_arith), hb (4 * i + 1) (by omega_arith), hb (4 * i + 2) (by omega_arith),
      hb (4 * i + 3) (by omega_arith)]
  obtain f₀₂ : Frame [⟨b.setWidth 64, 4 * 368⟩] s₀.mem s₂.mem :=
    f₁.trans (k₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [tableEnd_eq]; omega_using [])⟩)
  have base₂ : s₂.gpr sb = b := k₂.pre.base
  have base₂' : s₂.gpr .edi = b := base₂
  obtain esp₂ : s₂.gpr .esp = s₀.gpr .esp := by
    rw [k₂.regs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), esp₁]
  obtain sc₂ : ScrOkE s₀ b E s₂.mem := by
    refine ⟨fun e he => ?_, fun i hi => ?_⟩
    · have := k₂.key.keys e he
      rw [base₂, hsch] at this
      exact this
    · rw [← sv₁ i hi]
      exact slotE_keep hfit (lo := Impl.Sm4.X86.slots) (hi := Impl.Sm4.X86.slots + 4) (by decide) k₂.frame
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact VG.Offset.disjoint_base _ (by rw [tableEnd_eq, slots_eq]; omega_using [])
            (by rw [slots_eq]; omega_using []))
        (by omega_using []) (by omega_using [hi])
  obtain rd₂ : s₂.rd = s₀.rd := by rw [k₂.rd, rd₁]
  obtain wr₂ : s₂.wr = s₀.wr := by rw [k₂.wr, wr₁]
  -- The data pointer and the count to their Impl.Sm4.X86.slots.
  obtain ⟨s₃a, e₃a, a₃a, o₃a, m₃a, rd₃a, wr₃a, f₃a⟩ := argSlotE_ok s₂ (i := 1) (k := modeDSlot) base₂'
    modeDSlot_lt (by rw [wr₂]; exact hwE) (argIn rd₂ wr₂ esp₂ 1 (by decide))
  obtain f₀₃a : Frame [⟨b.setWidth 64, 4 * 368⟩] s₀.mem s₃a.mem :=
    f₀₂.trans (f₃a.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact slotE_sub hfit modeDSlot_lt⟩)
  obtain esp₃a : s₃a.gpr .esp = s₀.gpr .esp := by rw [o₃a _ (by decide), esp₂]
  obtain ⟨s₃b, e₃b, a₃b, o₃b, m₃b, rd₃b, wr₃b, f₃b⟩ := argSlotE_ok s₃a (i := 2) (k := modeNSlot)
    ((o₃a _ (by decide)).trans base₂') modeNSlot_lt (by rw [wr₃a, wr₂]; exact hwE)
    (argIn (by rw [rd₃a, rd₂]) (by rw [wr₃a, wr₂]) esp₃a 2 (by decide))
  let s₃ := arithFlags s₃b (s₃b.gpr .eax &&& s₃b.gpr .eax) false false
  obtain e₃ : runBlock isa [.mov .eax (.mem (argOp 1)), st modeDSlot .eax, .mov .eax (.mem (argOp 2)),
      st modeNSlot .eax, .alu .test .eax (.reg .eax)] s₂ = some s₃ := by
    rw [show ([.mov .eax (.mem (argOp 1)), st modeDSlot .eax, .mov .eax (.mem (argOp 2)), st modeNSlot .eax,
        .alu .test .eax (.reg .eax)] : List Instr) =
      [.mov .eax (.mem (argOp 1)), .store (slotAt .edi modeDSlot) .eax] ++
        ([.mov .eax (.mem (argOp 2)), .store (slotAt .edi modeNSlot) .eax] ++ [.alu .test .eax (.reg .eax)]) from rfl,
      runBlock_app, e₃a, Option.bind_some, runBlock_app, e₃b, Option.bind_some]
    rfl
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  obtain eax₃ : s₃b.gpr .eax = arg s₀ 2 := by
    rw [a₃b, ea_arg esp₃a]; exact argR f₀₃a 2 (by decide)
  obtain dp₃ : s₃.mem.readW (wordAddr b modeDSlot) 32 = D := by
    show s₃b.mem.readW _ 32 = _
    rw [m₃b, readW_slotE_write hfit (j := modeDSlot) (k := modeNSlot) _ modeDSlot_lt modeNSlot_lt,
      ite_eq_right (by decide), m₃a, readW_slotE_write hfit (j := modeDSlot) (k := modeDSlot) _ modeDSlot_lt
      modeDSlot_lt, ite_eq_left rfl, ea_arg esp₂]
    exact argR f₀₂ 1 (by decide)
  obtain np₃ : s₃.mem.readW (wordAddr b modeNSlot) 32 = BitVec.ofNat 32 n := by
    show s₃b.mem.readW _ 32 = _
    rw [m₃b, readW_slotE_write hfit (j := modeNSlot) (k := modeNSlot) _ modeNSlot_lt modeNSlot_lt, ite_eq_left rfl,
      ← a₃b, eax₃]
    simp only [n, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain f₃ : Frame [(⟨wordAddr b modeDSlot, 4⟩ : Region), ⟨wordAddr b modeNSlot, 4⟩] s₂.mem s₃.mem :=
    (f₃a.sub fun r hr => ⟨r, by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self, fun _ h => h⟩).trans
      (f₃b.sub fun r hr => ⟨r, by
        rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩)
  obtain ⟨dsK, dsS⟩ := dnE_disj hfit
  obtain sc₃ : ScrOkE s₀ b E s₃.mem := sc₂.frame hfit f₃ dsK dsS
  obtain f₀₃ : Frame [⟨b.setWidth 64, 4 * 368⟩] s₀.mem s₃.mem :=
    f₀₂.trans (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, dnE_sub hfit r hr⟩)
  obtain data₃ : ∀ i < 16 * n, s₃.mem (D.setWidth 64 + BitVec.ofNat 64 i) = s₀.mem (D.setWidth 64 + BitVec.ofNat 64 i) :=
    fun i hi => f₀₃.bytes (R := ⟨D.setWidth 64, 16 * n⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS') (by simp only; omega_using []) hi
  obtain fr₃ : Frame [⟨b.setWidth 64, 4 * 368⟩, ⟨D.setWidth 64, 16 * n⟩, stkRegion (s₀.gpr .esp) 20]
      s₀.mem s₃.mem :=
    f₀₃.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  obtain g₃ : ∀ r, r ≠ .eax → s₃.gpr r = s₂.gpr r := fun r hr => by
    show s₃b.gpr r = _; rw [o₃b r hr, o₃a r hr]
  obtain base₃ : s₃.gpr .edi = b := by rw [g₃ _ (by decide)]; exact base₂
  obtain esp₃ : s₃.gpr .esp = s₀.gpr .esp := by rw [g₃ _ (by decide), esp₂]
  obtain rd₃ : s₃.rd = s₀.rd := by show s₃b.rd = _; rw [rd₃b, rd₃a, rd₂]
  obtain wr₃ : s₃.wr = s₀.wr := by show s₃b.wr = _; rw [wr₃b, wr₃a, wr₂]
  obtain hz₃ : s₃.zf = some (decide (n = 0)) := by
    rw [RegUpd.zf_arithFlags, eax₃, BitVec.and_self]
    refine congrArg some (Bool.eq_iff_iff.mpr ?_)
    rw [beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by simp only [n, h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
  -- The groups.
  refine WP.seq (WP.mono (M := isa) (Q := GDone s₀ b D n E)
    (WP.ite (decide (n = 0)) ((eval_e s₃).trans hz₃) (fun h0 => ?_) (fun h0 => ?_)) fun s₅ d₅ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨base₃, esp₃, sc₃, fun i hi => by omega, fr₃, rd₃, wr₃⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine dataLoop_wp dir (K := K) ⟨hwE, hwD, dDS', fitD, dSS', dSD', fitLo⟩ ⟨base₃, esp₃, by rw [dp₃]; simp,
      by rw [np₃, Nat.mul_zero, Nat.sub_zero], by omega_using [hn0], sc₃, fun i hi => ?_, fr₃, rd₃, wr₃⟩
    rw [data₃ i hi, ite_eq_right (by omega_using [])]
  -- The epilogue.
  obtain ⟨s₆, e₆, rg₆, o₆, m₆⟩ := restoreE_ok (s₀ := s₀) (b := b) (by rw [d₅.wr]; exact hwE) d₅.base
    d₅.scr.saved
  refine WP.of_runBlock ⟨s₆, e₆, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rg₆ 0 (by decide)
    · exact rg₆ 1 (by decide)
    · exact rg₆ 2 (by decide)
    · exact rg₆ 3 (by decide)
    · rw [o₆ _ (fun i hi => by revert i; decide), d₅.esp]
  · rw [m₆]
    exact d₅.frame.readW (r := ⟨(s₀.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact dRS'
      · exact dRD
      · exact (stk_ret fitLo).symm) (by decide)
  · have hd₆ : DInv s₀.mem s₆.mem (D.setWidth 64) n n (outF s₀.mem (D.setWidth 64) E) := fun i hi => by
      rw [m₆]; exact d₅.data i hi
    show Spec.Sm4.blocksAt s₆.mem (D.setWidth 64) n = _
    rw [blocksAt_of_dinv hd₆, ecb_eq]
    simp only [Spec.Sm4.blocksAt, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    exact outF_spec dir s₀.mem _ _ j

end VG.Proof.Sm4.X86


namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.Impl.Sm4.X86
open VG.Proof.Sm4 (specDirX86 ecbX86)

/-- `ecbX86.pre`, by name. -/
structure EPre (s : State) : Prop where
  rd : s.rd = [⟨(arg s 0).setWidth 64, 128⟩, ⟨argAddr s 0, 16⟩]
  wr : s.wr = [⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩, ⟨(arg s 3).setWidth 64, 8 * 184⟩]
  dDB : Region.Disjoint ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩ ⟨(arg s 3).setWidth 64, 8 * 184⟩
  aD : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩
  aB : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨(arg s 3).setWidth 64, 8 * 184⟩
  rD : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩
  rB : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 3).setWidth 64, 8 * 184⟩
  sD : Region.Disjoint (below (s.gpr .esp) 20) ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩
  sB : Region.Disjoint (below (s.gpr .esp) 20) ⟨(arg s 3).setWidth 64, 8 * 184⟩
  fD : (arg s 1).toNat + 16 * (arg s 2).toNat ≤ 2 ^ 32
  fB : (arg s 3).toNat + 8 * 184 ≤ 2 ^ 32
  fSp : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  lo : 20 ≤ (s.gpr .esp).toNat

theorem EPre.of {dir : Dir} {s : State} (h : (ecbX86 dir).pre s) : EPre s := by
  obtain ⟨h1, h2, -, -, h5, h6, h7, h8, h9, h10, h11, -, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h5, h6, h7, h8, h9, h10, h11, h13, h14, h15, h16⟩

/-- The initial taint: `esp` public, the words holding `data` and `scratch`
known to be the base addresses of the writable regions, and the 20 bytes
below `esp` apart from them. -/
def ecbTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 8 * 184], argLen := 20,
    argBases := [(8, 0), (16, 1)], room := 20 }

theorem ecbTaint_wf {s : State} (hp : EPre s) : VG.X86.Taint.Wf ecbTaint s := by
  have hD := hp.fD; have hB := hp.fB; have hs := hp.fSp
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [ecbTaint]; omega_using [hs], ?_⟩, ?_⟩ ?_
  · rw [hp.wr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨hp.dDB, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [setWidth_toNat] <;> omega_arith
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [hs]) hp.rD hp.aD
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [hs]) hp.rB hp.aB
  · intro p hp'
    simp only [ecbTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]
  · intro _
    refine ⟨hp.lo, ?_⟩
    intro r hr
    have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 20 =
        (s.gpr .esp - BitVec.ofNat 32 20).setWidth 64 := (VG.X86.Taint.sub_setWidth hp.lo).symm
    change (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 20, 20⟩ : Region).Disjoint r
    rw [e]
    simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.sD
    · exact hp.sB

theorem ecbTaint_agree (dir : Dir) {s₁ s₂ : State} (h₁ : (ecbX86 dir).pre s₁) (h₂ : (ecbX86 dir).pre s₂)
    (hpub : (ecbX86 dir).pub s₁ s₂) : VG.X86.Taint.Agree ecbTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := EPre.of h₁; have hp₂ := EPre.of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, ecbTaint_wf hp₁, ecbTaint_wf hp₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [ecbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr, ha 1 (by omega_using []), ha 2 (by omega_using []), ha 3 (by omega_using [])]
  · simp only [ecbTaint] at hk
    rw [show VG.X86.Taint.depth ecbTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 20) hp₁.fSp h4 hk, VG.X86.Taint.argByte_eq (n := 20) hp₂.fSp h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_using [])), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_using []))]
    exact congrArg _ (ha _ (by omega_using [hk]))

theorem ecb_ct (dir : Dir) : ConstantTime isa (ecbX86 dir).pre (ecbX86 dir).pub (ecb dir) := by
  cases dir
  · exact VG.Taint.constantTime_of_exists (A := VG.X86.taint) ecbTaint
      (fun _ _ h₁ h₂ hp => ecbTaint_agree _ h₁ h₂ hp) (by taint_decide_sum [cryptSumEcb])
  · exact VG.Taint.constantTime_of_exists (A := VG.X86.taint) ecbTaint
      (fun _ _ h₁ h₂ hp => ecbTaint_agree _ h₁ h₂ hp) (by taint_decide_sum [cryptSumEcb])

theorem ecb_correct (dir : Dir) (s : State) (hs : (ecbX86 dir).pre s) :
    ∃ t s', Exec isa (ecb dir) s t s' ∧ abiPreserved s s' ∧ (ecbX86 dir).post s s' :=
  ecb_wp dir hs

/-- `ecbX86` with the argument slots writable, as the signature's contract has
them; the code reads them only (`ecb_verified` narrows to `ecbX86`). -/
def wideContract (dir : Dir) : Contract isa :=
  { ecbX86 dir with
    pre := fun s =>
      let sched : Region := ⟨(arg s 0).setWidth 64, 128⟩
      let data : Region := ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩
      let scratch : Region := ⟨(arg s 3).setWidth 64, 8 * 184⟩
      let args : Region := ⟨argAddr s 0, 16⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack := below (s.gpr .esp) 20
      s.rd = [sched] ∧ s.wr = [data, scratch, args] ∧
      sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
      args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
      stack.Disjoint data ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 16 * (arg s 2).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 8 * 184 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat }

def narrowRd (s : State) : List Region := [⟨(arg s 0).setWidth 64, 128⟩, ⟨argAddr s 0, 16⟩]
def narrowWr (s : State) : List Region :=
  [⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩, ⟨(arg s 3).setWidth 64, 8 * 184⟩]

tactic_template "sm4_ecb_narrow" : tactic =>
  `(tactic| simp only [VG.Proof.Sm4.ecbX86, VG.Proof.Sm4.X86.wideContract,
                     VG.Proof.Sm4.X86.narrowRd, VG.Proof.Sm4.X86.narrowWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr])

tactic_template "sm4_ecb_narrow" loc:Lean.Parser.Tactic.location : tactic =>
  `(tactic| simp only [VG.Proof.Sm4.ecbX86, VG.Proof.Sm4.X86.wideContract,
                     VG.Proof.Sm4.X86.narrowRd, VG.Proof.Sm4.X86.narrowWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $loc)

theorem wide_pre (dir : Dir) (s : State) (h : (wideContract dir).pre s) :
    (ecbX86 dir).pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  obtain ⟨_, _, h⟩ := h
  sm4_ecb_narrow
  exact ⟨trivial, trivial, h⟩

/-- Memory holding the arguments `0x1000, 0x3000, 0, 0x4000` at `0x8004`. -/
def satState : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x30 else if a = 0x8011 then 0x40 else 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 1472⟩, ⟨0x8004, 16⟩]

theorem wide_implies (dir : Dir) :
    (wideContract dir).Implies (Proof.Sm4.ecbScratchContract X86.abi (specDirX86 dir) 184 20) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Sm4.ecbScratchContract, Proof.Sm4.ecbScratchSig, Spec.Sm4.ecbPost, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, wideContract, ecbX86, below] at h
    sig_split h
    sig_reduce [Proof.Sm4.ecbScratchContract, Proof.Sm4.ecbScratchSig, Spec.Sm4.ecbPost, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, wideContract, ecbX86, below]
    sig_simp [Proof.Sm4.ecbScratchContract, Proof.Sm4.ecbScratchSig, Spec.Sm4.ecbPost, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, wideContract, ecbX86, below] []
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [VG.X86.Taint.sub_setWidth (by omega_arith)]; try simp only [Nat.mul_comm] at *
         first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Sm4.ecbScratchContract, Proof.Sm4.ecbScratchSig, Spec.Sm4.ecbPost, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, wideContract, ecbX86, below, specDirX86]
  · sig_implies_pub [Proof.Sm4.ecbScratchContract, Proof.Sm4.ecbScratchSig, Spec.Sm4.ecbPost, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, wideContract, ecbX86, below]
  · sig_implies_sat [Proof.Sm4.ecbScratchContract, Proof.Sm4.ecbScratchSig, Spec.Sm4.ecbPost, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, wideContract, ecbX86, below]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem ecb_verified (dir : Dir) :
    Verified X86.target (ecb dir) (Proof.Sm4.ecbScratchContract X86.abi (specDirX86 dir) 184 20) := by
  have hsat := (wide_implies dir).sat_left
  have narrowSat : ∃ s, (ecbX86 dir).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wide_pre dir s hs⟩
  apply Verified.of_implies _ (wide_implies dir)
  refine Verified.narrowTo
    (Verified.of_correct (ecb_correct dir) (ecb_ct dir) (.refl narrowSat))
    narrowRd narrowWr (wide_pre dir) ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp_all only [or_true, true_or]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp_all only [or_true, true_or]
  · intro s s' _ h
    sm4_ecb_narrow at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    sm4_ecb_narrow
    exact h

/-- A state satisfying the ECB functions' precondition: the schedule at
`0x1000` and no blocks at `0x2000`, as stack arguments at `0x8004`, which
are writable. -/
def ecbFrameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x8004, 12⟩]

theorem ecbFrameSat_pre (d : Spec.Sm4.Direction) : ∃ s, (Spec.Sm4.ecbContract X86.abi d 1512).pre s := by
  implies_sat [Spec.Sm4.ecbContract, Spec.Sm4.ecbSig, Spec.Sm4.ecbPost, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] [ecbFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using ecbFrameSat

/-- ECB in the direction `dir`, with its working space on the stack. -/
theorem ecb_framed (dir : Dir) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 1492 3 368 (ecb dir))
      (Spec.Sm4.ecbContract X86.abi (specDirX86 dir) 1512) :=
  X86.Verified.stackScratchWiped (sig := Spec.Sm4.ecbSig) (nm := "scratch") (e := .u64)
    (n := 184) (post := Spec.Sm4.ecbPost (specDirX86 dir) X86.abi.ptrBits) (wa := true) (stack := 20)
    (bytes := 1492) (ecb_verified dir) (by decide) (by cases dir <;> lit_decide)
    (by cases dir <;> lit_decide) (by decide) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sm4.ecbPost_local _ _) (Proof.Sm4.ecbPostOut_local _ _) (ecbFrameSat_pre _)

end VG.Proof.Sm4.X86
