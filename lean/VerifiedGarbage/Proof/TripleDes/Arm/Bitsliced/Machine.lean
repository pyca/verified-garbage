module

public import VerifiedGarbage.Proof.Framework.Bitslice.Vars
public import VerifiedGarbage.Proof.Framework.Arm.Straight
public import VerifiedGarbage.Impl.TripleDes.Arm.Bitsliced
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Reduce
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# The machine state of the bitsliced ECB code on ARMv7

The code keeps everything in its working space at `r3` (`fw s k`, the word
at `r3 + 4k`); its 64 state words are the words from `spills` on (`words`).
`Room` says that the working space is writable and does not wrap around.
Blocks that only move and XOR words between registers and the state words
are checked by evaluation over the variable domain (`Bitslice.vars`):
`varsRun` runs one, its variables being the state words (variable `k < 64`)
and some registers (variable `64 + i`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.Arm.Bitsliced

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.TripleDes.Arm.Bitslice
open VG.Proof.X25519.Arm (dpVal)

/-- Word `k` of the working space. -/
def fw (s : State) (k : Nat) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .r3) k) 32

/-- The 64 state words. -/
def words (s : State) (j : Nat) : BitVec 32 := fw s (spills + j)

/-- The working space. -/
def frameR (s : State) : Region := ⟨State.addr (s.gpr .r3), 1024⟩

/-- The working space is a writable region and does not wrap around. -/
structure Room (s : State) : Prop where
  frame : frameR s ∈ s.wr
  fit : (s.gpr .r3).toNat + 1024 ≤ 2 ^ 32

theorem Room.congr {s s' : State} (h : Room s) (hb : s'.gpr .r3 = s.gpr .r3) (hw : s'.wr = s.wr) :
    Room s' where
  frame := by rw [frameR, hb, hw]; exact h.frame
  fit := by rw [hb]; exact h.fit

/-- Four bytes of the working space, at an offset. -/
theorem slot_in {s : State} (h : Room s) {off : Nat} (ho : off + 4 ≤ 1024) :
    InRegions s.wr (State.addr (s.gpr .r3 + BitVec.ofNat 32 off)) 4 :=
  in_off h.frame h.fit ho (by decide)

theorem slot_rd {s : State} (h : Room s) {off : Nat} (ho : off + 4 ≤ 1024) :
    InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r3 + BitVec.ofNat 32 off)) 4 :=
  let ⟨r, hr, hc⟩ := slot_in h ho; ⟨r, List.mem_append_right _ hr, hc⟩

/-- The words of the working space from its base are accessible. -/
theorem Room.ok {s : State} (h : Room s) {c : Cfg} (hb : c.base = .r3) (hs : 4 * c.slots ≤ 1024)
    (he : c.exts = 0) : Ok c s :=
  Ok.of_off h.frame h.fit (off := 0) (by rw [hb]; exact (BitVec.add_zero _).symm)
    (by omega_using [hs]) he

/-- The first `4 n` bytes of the working space. -/
def headR (s : State) (n : Nat) : Region := ⟨State.addr (s.gpr .r3), 4 * n⟩

/-- The spilled words and the state words. -/
def stR (s : State) : Region := headR s (spills + 64)

theorem headR_congr {s s' : State} (hb : s'.gpr .r3 = s.gpr .r3) (n : Nat) : headR s' n = headR s n := by
  simp only [headR, hb]

theorem stR_congr {s s' : State} (hb : s'.gpr .r3 = s.gpr .r3) : stR s' = stR s := headR_congr hb _

/-- A word of the working space past the first `n` is not in them. -/
theorem fw_frame {s : State} (h : Room s) {m : Mem} {n k : Nat} (hf : Frame [headR s n] s.mem m)
    (hn : n ≤ k) (hk : k < 256) :
    m.readW (wordAddr (s.gpr .r3) k) 32 = s.mem.readW (wordAddr (s.gpr .r3) k) 32 := by
  have fit := h.fit
  refine hf.readW (Region.contains_self _ 4) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  rw [wordAddr, addr_add (by omega_using [fit, hk])]
  have := toNat_addr (s.gpr .r3)
  exact Offset.disjoint_base (State.addr (s.gpr .r3)) (d := 4 * k) (n := 4) (k := 4 * n)
    (by omega_using [hn]) (by omega_using [fit, hk, this])

/-! ## Words of the working space, loaded and stored -/

/-- `s` with word `k` of the working space set to `v`. -/
def stFw (s : State) (k : Nat) (v : BitVec 32) : State :=
  { s with mem := s.mem.writeW (wordAddr (s.gpr .r3) k) v }

theorem exec_ldrFw {s : State} (h : Room s) {t : Reg} {off : Nat} (k : Nat) (hk : off = 4 * k)
    (hlt : k < 256) : exec (.ldr t .r3 off) s = some (s.setReg t (fw s k)) := by
  subst hk
  exact exec_ldr (by omega_using [hlt]) (slot_rd h (by omega_using [hlt]))

theorem exec_strFw {s : State} (h : Room s) {t : Reg} {off : Nat} (k : Nat) (hk : off = 4 * k)
    (hlt : k < 256) : exec (.str t .r3 off) s = some (stFw s k (s.gpr t)) := by
  subst hk
  exact exec_str (by omega_using [hlt]) (slot_in h (by omega_using [hlt]))

theorem fw_stFw {s : State} (h : Room s) {k j : Nat} (hk : k < 256) (hj : j < 256) (v : BitVec 32) :
    fw (stFw s k v) j = if j = k then v else fw s j := by
  have fit := h.fit
  show (s.mem.writeW (wordAddr (s.gpr .r3) k) v).readW (wordAddr (s.gpr .r3) j) 32 = _
  split
  · rename_i e; subst e; exact Mem.readW_writeW_self32 _ _ _
  · rename_i e
    exact Mem.readW_writeW_sep (w := 32) (w' := 32)
      (slot_sep _ (by omega_using [fit, hj]) (by omega_using [fit, hk]) e) (by decide)

theorem gpr_stFw (s : State) (k : Nat) (v : BitVec 32) (r : Reg) : (stFw s k v).gpr r = s.gpr r := rfl
theorem rd_stFw (s : State) (k : Nat) (v : BitVec 32) : (stFw s k v).rd = s.rd := rfl
theorem wr_stFw (s : State) (k : Nat) (v : BitVec 32) : (stFw s k v).wr = s.wr := rfl
theorem sp_stFw (s : State) (k : Nat) (v : BitVec 32) : (stFw s k v).sp = s.sp := rfl
theorem z_stFw (s : State) (k : Nat) (v : BitVec 32) : (stFw s k v).z = s.z := rfl

theorem fw_setReg (s : State) {r : Reg} (hr : r ≠ .r3) (x : BitVec 32) (k : Nat) :
    fw (s.setReg r x) k = fw s k := by
  rw [fw, fw, RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hr)]; rfl

theorem Room.stFw {s : State} (h : Room s) (k : Nat) (v : BitVec 32) : Room (stFw s k v) :=
  h.congr rfl rfl

theorem stFw_frame {s : State} (h : Room s) {k n : Nat} (hk : k < n) (hn : n ≤ 256) (v : BitVec 32) :
    Frame [headR s n] s.mem (stFw s k v).mem :=
  (Frame.refl [headR s n] s.mem).writeW (List.mem_singleton_self _) v
    (slot_contains _ hk (by have := h.fit; omega_using [hn, this]))

theorem words_stFw {s : State} (h : Room s) {k x : Nat} (hk : spills + 64 ≤ k) (hk' : k < 256)
    (hx : x < 64) (v : BitVec 32) : words (stFw s k v) x = words s x := by
  rw [words, fw_stFw h hk' (by unfold spills; omega_using [hx]),
    ite_eq_right (by omega_using [hk, hx])]
  rfl

/-- A frame within the first `n` words of the working space is one within more. -/
theorem headR_mono {s : State} {n n' : Nat} (hn : n ≤ n') {m m' : Mem} (hf : Frame [headR s n] m m') :
    Frame [headR s n'] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_using [hn])⟩

/-- A word of the working space past the first `n`, in a later state. -/
theorem fw_of_frame {s s' : State} (h : Room s) (hb : s'.gpr .r3 = s.gpr .r3) {n k : Nat}
    (hf : Frame [headR s n] s.mem s'.mem) (hn : n ≤ k) (hk : k < 256) : fw s' k = fw s k := by
  rw [fw, hb]; exact fw_frame h hf hn hk

/-! ## One instruction -/

theorem exec_dp {s : State} {op : DpOp} {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y) :
    exec (.dp op d n o) s = some (s.setReg d (dpVal op (s.gpr n) y)) := by
  cases op <;> simp only [reduceExec, ho, Option.map_some, dpVal]

theorem exec_mov {s : State} {d : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y) :
    exec (.mov d o) s = some (s.setReg d y) := by
  simp only [reduceExec, ho, Option.map_some]

theorem exec_subs {s : State} {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y) :
    exec (.subs d n o) s = some ((subFlags s (s.gpr n) y).setReg d (s.gpr n - y)) := by
  simp only [reduceExec, ho, Option.map_some]

theorem exec_cmp {s : State} {n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y) :
    exec (.cmp n o) s = some (subFlags s (s.gpr n) y) := by
  simp only [reduceExec, ho, Option.map_some]

theorem runBlock_cat_some {a b : List Instr} {s s₁ s₂ : State} (h₁ : runBlock isa a s = some s₁)
    (h₂ : runBlock isa b s₁ = some s₂) : runBlock isa (a ++ b) s = some s₂ := by
  rw [VG.Interleave.runBlock_append, h₁, Option.bind_some, h₂]

/-! ## Blocks over the variable domain -/

/-- The spilled words and the state words, `[r3 + 4k]`, `k < spills + 64`. -/
def varsCfg : Cfg := { base := .r3, slots := spills + 64, ext := .r3, exts := 0 }

/-- State word `k` is variable `k`; register `regs[i]` is variable `64 + i`. -/
def varEnv (regs : List Reg) : Env Nat :=
  { reg := fun r => (regs.idxOf? r).map fun i => 2 ^ (64 + i),
    slot := fun k => if spills ≤ k ∧ k < spills + 64 then some (2 ^ (k - spills)) else none }

/-- The values of the variables. -/
def varVals (s : State) (regs : List Reg) (v : Nat) : BitVec 32 :=
  if v < 64 then words s v else s.gpr (regs.getD (v - 64) .r0)

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
  cst _ _ h := by cases h

theorem varsCfg_ok {s : State} (h : Room s) : Ok varsCfg s := h.ok rfl (by decide) rfl

/-- Run a block that the variable domain accepts. -/
theorem varsRun {is : List Instr} (regs : List Reg) {post : Env Nat → Bool}
    (hchk : check (vars 32) varsCfg (fun _ => none) is (varEnv regs) post = true)
    {s : State} (h : Room s) :
    ∃ e' s', post e' = true ∧ runBlock isa is s = some s' ∧
      Post (VarRel (varVals s regs) (varN regs)) varsCfg (fun _ => none) e' s s'
        (fun r => (is.all fun i => !clobbers i r) = false) := by
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

end VG.Proof.TripleDes.Arm.Bitsliced
