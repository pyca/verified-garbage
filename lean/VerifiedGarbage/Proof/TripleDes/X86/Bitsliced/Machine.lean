module

public import VerifiedGarbage.Proof.Framework.Bitslice.Vars
public import VerifiedGarbage.Proof.Framework.X86.Straight
public import VerifiedGarbage.Impl.TripleDes.X86.Bitsliced
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.Reduce
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# The machine state of the bitsliced Triple DES code on x86 (32-bit)

As on ARMv7 (`Proof/TripleDes/Arm/Bitsliced/Machine.lean`): the code keeps
everything in its working space at `ebp` (`fw s k`, the word at
`ebp + 4k`); its 64 state words are the words from `spills` on (`words`).
`Room` says that the working space is writable and does not wrap around.
Blocks that only move and XOR words between registers and the state words
are checked by evaluation over the variable domain (`Bitslice.vars`):
`varsRun` runs one, its variables being the state words (variable `k < 64`)
and some registers (variable `64 + i`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86.Bitsliced

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.TripleDes.X86.Bitslice

/-- Word `k` of the working space. -/
def fw (s : State) (k : Nat) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .ebp) k) 32

/-- The 64 state words. -/
def words (s : State) (j : Nat) : BitVec 32 := fw s (spills + j)

/-- The working space. -/
def frameR (s : State) : Region := ⟨(s.gpr .ebp).setWidth 64, 4 * wsWords⟩

/-- The working space is a writable region and does not wrap around. -/
structure Room (s : State) : Prop where
  frame : frameR s ∈ s.wr
  fit : (s.gpr .ebp).toNat + 4 * wsWords ≤ 2 ^ 32

theorem Room.congr {s s' : State} (h : Room s) (hb : s'.gpr .ebp = s.gpr .ebp) (hw : s'.wr = s.wr) :
    Room s' where
  frame := by rw [frameR, hb, hw]; exact h.frame
  fit := by rw [hb]; exact h.fit

/-- A word of the working space. -/
theorem slot_in {s : State} (h : Room s) {k : Nat} (hk : k < wsWords) :
    InRegions s.wr (wordAddr (s.gpr .ebp) k) 4 :=
  ⟨_, h.frame, slot_contains _ hk h.fit⟩

theorem slot_rd {s : State} (h : Room s) {k : Nat} (hk : k < wsWords) :
    InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .ebp) k) 4 :=
  let ⟨r, hr, hc⟩ := slot_in h hk; ⟨r, List.mem_append_right _ hr, hc⟩

/-- The words of the working space from its base are accessible. -/
theorem Room.ok {s : State} (h : Room s) {c : Cfg} (hb : c.base = .ebp) (hs : c.slots ≤ wsWords)
    (he : c.exts = 0) : Ok c s where
  slotIn k hk := by rw [hb]; exact slot_in h (by omega_using [hk, hs])
  extIn k hk := by omega
  fit := by rw [hb]; have := h.fit; omega_using [hs, this]
  sep k _ j hj := by omega

/-- The first `4 n` bytes of the working space. -/
def headR (s : State) (n : Nat) : Region := ⟨(s.gpr .ebp).setWidth 64, 4 * n⟩

/-- The circuits' words and the state words. -/
def stR (s : State) : Region := headR s (spills + 64)

theorem headR_congr {s s' : State} (hb : s'.gpr .ebp = s.gpr .ebp) (n : Nat) : headR s' n = headR s n := by
  simp only [headR, hb]

theorem stR_congr {s s' : State} (hb : s'.gpr .ebp = s.gpr .ebp) : stR s' = stR s := headR_congr hb _

/-- A word of the working space past the first `n` is not in them. -/
theorem fw_frame {s : State} (h : Room s) {m : Mem} {n k : Nat} (hf : Frame [headR s n] s.mem m)
    (hn : n ≤ k) (hk : k < wsWords) :
    m.readW (wordAddr (s.gpr .ebp) k) 32 = s.mem.readW (wordAddr (s.gpr .ebp) k) 32 := by
  have fit := h.fit
  refine hf.readW (Region.contains_self _ 4) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  rw [wordAddr, addr_eq (by unfold wsWords at fit hk; omega_using [fit, hk])]
  exact Offset.disjoint_base ((s.gpr .ebp).setWidth 64) (d := 4 * k) (n := 4) (k := 4 * n)
    (by omega_using [hn]) (by unfold wsWords at hk; omega_using [hk])

/-! ## Words of the working space, loaded and stored -/

/-- `s` with word `k` of the working space set to `v`. -/
def stFw (s : State) (k : Nat) (v : BitVec 32) : State :=
  { s with mem := s.mem.writeW (wordAddr (s.gpr .ebp) k) v }

theorem exec_ld {s : State} {t b : Reg} {off : Nat}
    (hin : InRegions (s.rd ++ s.wr) (addr (s.gpr b) off) 4) :
    exec (.mov t (.mem ⟨b, off⟩)) s = some (s.setReg t (s.mem.readW (addr (s.gpr b) off) 32)) := by
  simp [reduceExec, Wp.readSrc_mem rfl hin]

theorem exec_st {s : State} {r b : Reg} {off : Nat} (hout : InRegions s.wr (addr (s.gpr b) off) 4) :
    exec (.store ⟨b, off⟩ r) s = some { s with mem := s.mem.writeW (addr (s.gpr b) off) (s.gpr r) } := by
  simp [reduceExec, State.store32, ea_mk, hout]

theorem exec_ldFw {s : State} (h : Room s) {t : Reg} (k : Nat) (hlt : k < wsWords) :
    exec (.mov t (.mem (ws k))) s = some (s.setReg t (fw s k)) :=
  exec_ld (slot_rd h hlt)

theorem exec_stFw {s : State} (h : Room s) {t : Reg} (k : Nat) (hlt : k < wsWords) :
    exec (.store (ws k) t) s = some (stFw s k (s.gpr t)) :=
  exec_st (slot_in h hlt)

theorem fw_stFw {s : State} (h : Room s) {k j : Nat} (hk : k < wsWords) (hj : j < wsWords) (v : BitVec 32) :
    fw (stFw s k v) j = if j = k then v else fw s j := by
  have fit := h.fit
  show (s.mem.writeW (wordAddr (s.gpr .ebp) k) v).readW (wordAddr (s.gpr .ebp) j) 32 = _
  split
  · rename_i e; subst e; exact Mem.readW_writeW_self32 _ _ _
  · rename_i e
    exact Mem.readW_writeW_sep (w := 32) (w' := 32)
      (slot_sep _ (by omega_using [fit, hj]) (by omega_using [fit, hk]) e) (by decide)

theorem gpr_stFw (s : State) (k : Nat) (v : BitVec 32) (r : Reg) : (stFw s k v).gpr r = s.gpr r := rfl
theorem rd_stFw (s : State) (k : Nat) (v : BitVec 32) : (stFw s k v).rd = s.rd := rfl
theorem wr_stFw (s : State) (k : Nat) (v : BitVec 32) : (stFw s k v).wr = s.wr := rfl

theorem fw_setReg (s : State) {r : Reg} (hr : r ≠ .ebp) (x : BitVec 32) (k : Nat) :
    fw (s.setReg r x) k = fw s k := by
  rw [fw, fw, RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hr)]; rfl

theorem Room.stFw {s : State} (h : Room s) (k : Nat) (v : BitVec 32) : Room (stFw s k v) :=
  h.congr rfl rfl

theorem stFw_frame {s : State} (h : Room s) {k n : Nat} (hk : k < n) (hn : n ≤ wsWords) (v : BitVec 32) :
    Frame [headR s n] s.mem (stFw s k v).mem :=
  (Frame.refl [headR s n] s.mem).writeW (List.mem_singleton_self _) v
    (slot_contains _ hk (by have := h.fit; omega_using [hn, this]))

theorem words_stFw {s : State} (h : Room s) {k x : Nat} (hk : spills + 64 ≤ k) (hk' : k < wsWords)
    (hx : x < 64) (v : BitVec 32) : words (stFw s k v) x = words s x := by
  rw [words, fw_stFw h hk' (by unfold spills wsWords; omega_using [hx]),
    ite_eq_right (by omega_using [hk, hx])]
  rfl

/-- A frame within the first `n` words of the working space is one within more. -/
theorem headR_mono {s : State} {n n' : Nat} (hn : n ≤ n') {m m' : Mem} (hf : Frame [headR s n] m m') :
    Frame [headR s n'] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_using [hn])⟩

/-- A word of the working space past the first `n`, in a later state. -/
theorem fw_of_frame {s s' : State} (h : Room s) (hb : s'.gpr .ebp = s.gpr .ebp) {n k : Nat}
    (hf : Frame [headR s n] s.mem s'.mem) (hn : n ≤ k) (hk : k < wsWords) : fw s' k = fw s k := by
  rw [fw, hb]; exact fw_frame h hf hn hk

theorem runBlock_cat_some {a b : List Instr} {s s₁ s₂ : State} (h₁ : runBlock isa a s = some s₁)
    (h₂ : runBlock isa b s₁ = some s₂) : runBlock isa (a ++ b) s = some s₂ := by
  rw [VG.Interleave.runBlock_append, h₁, Option.bind_some, h₂]

/-! ## Blocks over the variable domain -/

/-- The circuits' words and the state words, `[ebp + 4k]`, `k < spills + 64`. -/
def varsCfg : Cfg := { base := .ebp, slots := spills + 64, ext := .ebp, exts := 0 }

/-- State word `k` is variable `k`; register `regs[i]` is variable `64 + i`. -/
def varEnv (regs : List Reg) : Env Nat :=
  { reg := fun r => (regs.idxOf? r).map fun i => 2 ^ (64 + i),
    slot := fun k => if spills ≤ k ∧ k < spills + 64 then some (2 ^ (k - spills)) else none }

/-- The values of the variables. -/
def varVals (s : State) (regs : List Reg) (v : Nat) : BitVec 32 :=
  if v < 64 then words s v else s.gpr (regs.getD (v - 64) .eax)

def varN (regs : List Reg) : Nat := 64 + regs.length

theorem varEnv_rel {s : State} (regs : List Reg) :
    Rel (VarRel (varVals s regs) (varN regs)) varsCfg (fun _ => none) (varEnv regs) s where
  reg r a h := by
    simp only [varEnv, Option.map_eq_some_iff] at h
    obtain ⟨i, hi, rfl⟩ := h
    obtain ⟨hlt, heq, -⟩ := List.idxOf?_eq_some_iff.mp hi
    simp only [VarRel, varN]
    rw [xorSet_two_pow _ (by omega_using [hlt])]
    simp only [varVals, show ¬ 64 + i < 64 by omega_using [], ite_false, Nat.add_sub_cancel_left]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, heq]
  slot k a hk h := by
    simp only [varEnv] at h
    split at h
    · rename_i hk'
      cases h
      simp only [VarRel, varN]
      rw [xorSet_two_pow _ (by omega_using [hk'])]
      simp only [varVals, show k - spills < 64 by omega_using [hk'], ite_true, words, fw, varsCfg]
      rw [show spills + (k - spills) = k by omega_using [hk']]
    · cases h
  ext _ _ hk := by simp [varsCfg] at hk

theorem varsCfg_ok {s : State} (h : Room s) : Ok varsCfg s := h.ok rfl (by decide) rfl

/-- Run a block that the variable domain accepts. -/
theorem varsRun {is : List Instr} (regs : List Reg) {post : Env Nat → Bool}
    (hchk : check (vars 32) varsCfg (fun _ => none) is (varEnv regs) post = true)
    {s : State} (h : Room s) :
    ∃ e' s', post e' = true ∧ runBlock isa is s = some s' ∧
      Post (VarRel (varVals s regs) (varN regs)) varsCfg (fun _ => none) e' s s'
        (fun r => (is.all fun i => i.dst != some r) = false) := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  obtain ⟨s', hs', p⟩ := run (vars_sound _ _) (varsCfg_ok h) (varEnv_rel regs) he
  exact ⟨e', s', hpost, hs', p⟩

/-- A state word after a block, from its abstract value. -/
theorem varRel_word {V : Nat → BitVec 32} {N : Nat} {e : Env Nat} {s : State}
    (hrel : Rel (VarRel V N) varsCfg (fun _ => none) e s) {k a : Nat} (hk : k < 64)
    (ha : e.slot (spills + k) = some a) : words s k = xorSet V a N :=
  hrel.slot (spills + k) a (by simp only [varsCfg]; omega_using [hk]) ha

theorem xorSet_two_pow_xor {V : Nat → BitVec 32} {a b N : Nat} (ha : a < N) (hb : b < N) :
    xorSet V (2 ^ a ^^^ 2 ^ b) N = V a ^^^ V b := by
  rw [xorSet_xor, xorSet_two_pow _ ha, xorSet_two_pow _ hb]

theorem slotRegion_vars (s : State) : slotRegion varsCfg s = stR s := rfl

end VG.Proof.TripleDes.X86.Bitsliced
