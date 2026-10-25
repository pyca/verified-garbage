module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Pass
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd

/-!
# The three passes of a block

`blockBody_ok`: the loop of the three passes, from a word in the halves'
registers (`WordState`) and the schedules' copy in the frame (`Ready`), to
the block function's core on it (`blockCore`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.RegUpd VG.Impl.TripleDes.RISCV64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (desCore roundPrefix roundKey)

/-- A DES word held as two zero-extended 32-bit Feistel registers. -/
structure WordState (x : BitVec 64) (s : State) : Prop where
  left : s.gpr lReg = ((x >>> 32).setWidth 32).setWidth 64
  right : s.gpr rReg = (x.setWidth 32).setWidth 64

theorem PassPost.wordState {keys : DesSchedule} {direction : Direction} {origin s : State}
    {x : BitVec 64} {n : Nat}
    (hs : PassPost keys direction origin ((x >>> 32).setWidth 32, x.setWidth 32) n s) :
    WordState (desCore keys direction x) s := by
  have hcore := VG.Proof.TripleDes.desCore_roundPrefix keys direction x
  let halves := roundPrefix keys direction 16 ((x >>> 32).setWidth 32, x.setWidth 32)
  have hleft : ((desCore keys direction x >>> 32).setWidth 32).setWidth 64 = halves.2.setWidth 64 :=
    (congrArg (fun v : BitVec 64 => ((v >>> 32).setWidth 32).setWidth 64) hcore).trans
      (congrArg (BitVec.setWidth 64) (VG.Proof.TripleDes.appended_left halves.2 halves.1))
  have hright : ((desCore keys direction x).setWidth 32).setWidth 64 = halves.1.setWidth 64 :=
    (congrArg (fun v : BitVec 64 => (v.setWidth 32).setWidth 64) hcore).trans
      (congrArg (BitVec.setWidth 64) (VG.Proof.TripleDes.appended_right halves.2 halves.1))
  exact ⟨hs.left.trans hleft.symm, hs.right.trans hright.symm⟩

def componentBase (base : Addr) (component : Nat) : Addr :=
  base + BitVec.ofNat 64 (128 * component)

/-- The three schedules `keys` in the frame, from `base` (`sb + keyOff`) on. -/
structure Ready (keys : Nat → DesSchedule) (base : Addr) (s : State) : Prop where
  spills : Ok sboxCfg s
  baseReg : s.gpr sb + BitVec.ofNat 64 keyOff = base
  keys : ∀ c < 3, ∀ d : Direction, KeysAt (keys c) d (componentBase base c) s

theorem KeysAt.congr {keys : DesSchedule} {d : Direction} {base : Addr} {s t : State}
    (hs : KeysAt keys d base s) (hbase : t.gpr sb = s.gpr sb) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hf : Frame [spillRegion s] s.mem t.mem) : KeysAt keys d base t := by
  have hwork : spillRegion t = spillRegion s := by simp only [spillRegion, hbase]
  refine ⟨?_, hs.al, ?_, ?_⟩
  · rw [hrd, hwr]; exact hs.read
  · rw [hwork]; exact hs.sep
  · intro j hj
    have hmem := hf.readW (a := keyAddr base d j) (w := 64)
      (r := ⟨keyAddr base d j, 8⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hs.sep j hj) (by decide)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hs.keys j hj)

theorem Ready.congr {keys : Nat → DesSchedule} {base : Addr} {s t : State}
    (hs : Ready keys base s) (hbase : t.gpr sb = s.gpr sb) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hf : Frame [spillRegion s] s.mem t.mem) : Ready keys base t :=
  ⟨hs.spills.congr hbase hbase hrd hwr, by rw [hbase]; exact hs.baseReg,
    fun c hc d => (hs.keys c hc d).congr hbase hrd hwr hf⟩

theorem passPointer (b : Addr) (c : Nat) (d : Direction) :
    b + BitVec.ofNat 64 (passOffset c d) =
      keyAddr (componentBase (b + BitVec.ofNat 64 keyOff) c) d 0 := by
  simp only [passOffset, keyAddr, componentBase, Offset.add_ofNat_add_ofNat]
  cases d <;> simp only [reduceCtorEq, ite_true, ite_false, Nat.add_zero, Nat.mul_zero] <;>
    rw [Offset.add_ofNat_add_ofNat] <;> rfl

structure Stable (origin s : State) : Prop where
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ passKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem

theorem Stable.refl (s : State) : Stable s s :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩

theorem Stable.trans {s t u : State} (hs : Stable s t) (ht : Stable t u) : Stable s u := by
  have hwork : spillRegion t = spillRegion s := by
    simp only [spillRegion, hs.regs sb (by decide)]
  have hf := ht.frame
  rw [hwork] at hf
  exact ⟨ht.rd.trans hs.rd, ht.wr.trans hs.wr, ht.sp.trans hs.sp,
    fun q hq => (ht.regs q hq).trans (hs.regs q hq), hs.frame.trans hf⟩

theorem pass_word_ok (keys : Nat → DesSchedule) (base : Addr) (s : State) (x : BitVec 64)
    (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3)
    (hready : Ready keys base s) (hword : WordState x s)
    (hpasses : s.gpr passes = BitVec.ofNat 64 p) :
    WP isa (pass d) s (fun t =>
      WordState (desCore (keys (passOf d p).1) (passOf d p).2 x) t ∧
      Ready keys base t ∧ Stable s t ∧
      t.gpr passes = BitVec.ofNat 64 (p - 1) ∧
      isa.eval (.nonzero passes) t = some (decide (p ≠ 1))) := by
  have hc := passOf_lt d p
  have hptr : s.gpr sb + BitVec.ofNat 64 (passOffset (passOf d p).1 (passOf d p).2) =
      keyAddr (componentBase base (passOf d p).1) (passOf d p).2 0 := by
    rw [← hready.baseReg]
    exact passPointer _ _ _
  apply WP.mono (pass_ok d hp (keys (passOf d p).1) (componentBase base (passOf d p).1) s
    ((x >>> 32).setWidth 32, x.setWidth 32) hready.spills hword.left hword.right
    hpasses hptr (hready.keys _ hc _))
  intro t ht
  exact ⟨ht.wordState,
    hready.congr (ht.regs sb (by decide)) ht.rd ht.wr ht.frame,
    ⟨ht.rd, ht.wr, ht.sp, ht.regs, ht.frame⟩, ht.pcount, ht.zf⟩

/-- The word after the first `k` passes of the block. -/
def passesDone (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) :
    Nat → BitVec 64
  | 0 => x
  | k + 1 => desCore (keys (passOf direction (3 - k)).1) (passOf direction (3 - k)).2
      (passesDone keys direction x k)

def blockCore (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) : BitVec 64 :=
  match direction with
  | .encrypt => desCore (keys 2) .encrypt (desCore (keys 1) .decrypt (desCore (keys 0) .encrypt x))
  | .decrypt => desCore (keys 0) .decrypt (desCore (keys 1) .encrypt (desCore (keys 2) .decrypt x))

theorem blockCore_passesDone (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) :
    blockCore keys direction x = passesDone keys direction x 3 := by
  cases direction <;> rfl

/-- The loop's invariant, with `m` passes left. -/
structure BodyInv (keys : Nat → DesSchedule) (base : Addr) (direction : Direction)
    (x : BitVec 64) (origin : State) (m : Nat) (s : State) : Prop where
  pos : 1 ≤ m
  le : m ≤ 3
  pcount : s.gpr passes = BitVec.ofNat 64 m
  word : WordState (passesDone keys direction x (3 - m)) s
  ready : Ready keys base s
  stable : Stable origin s

theorem blockBody_ok (keys : Nat → DesSchedule) (base : Addr) (s : State) (x : BitVec 64)
    (direction : Direction) (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (blockBody direction) s
      (fun t => WordState (blockCore keys direction x) t ∧ Ready keys base t ∧ Stable s t) := by
  let s₁ := s.write passes (BitVec.ofInt 64 3)
  have hregs : ∀ r, r ≠ passes → s₁.gpr r = s.gpr r := fun r h => gpr_write_of_ne _ _ h
  have hframe : Frame [spillRegion s] s.mem s₁.mem := Frame.refl _ _
  have hstable : Stable s s₁ := ⟨rfl, rfl, rfl,
    fun q hq => hregs q (by revert hq; cases q <;> decide), hframe⟩
  apply WP.seq
  refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
  · rw [runBlock_cons, exec_li (by decide), runStep_some, runBlock_nil]
  refine WP.loop (M := isa) (BodyInv keys base direction x s) ?_ 3 s₁
    ⟨by decide, by decide, gpr_write_self _ _ _, ?_,
      hready.congr (hregs sb (by decide)) rfl rfl hframe, hstable⟩
  · rintro m t ⟨hpos, hle, hpasses, hw, hr, hst⟩
    refine WP.mono (pass_word_ok keys base t _ direction ⟨hpos, hle⟩ hr hw hpasses)
      fun u ⟨hwu, hru, hsu, hpu, hzu⟩ => ?_
    have hdone : desCore (keys (passOf direction m).1) (passOf direction m).2
        (passesDone keys direction x (3 - m)) = passesDone keys direction x (3 - (m - 1)) := by
      rw [show 3 - (m - 1) = 3 - m + 1 by omega, passesDone, show 3 - (3 - m) = m by omega]
    rw [hdone] at hwu
    by_cases hlast : m = 1
    · subst m
      refine Or.inl ⟨by rw [hzu]; rfl, ?_, hru, hst.trans hsu⟩
      rw [blockCore_passesDone]
      exact hwu
    · refine Or.inr ⟨by rw [hzu]; simp [hlast], m - 1, by omega,
        ⟨by omega, by omega, hpu, hwu, hru, hst.trans hsu⟩⟩
  · exact ⟨(hregs lReg (by decide)).trans hword.left, (hregs rReg (by decide)).trans hword.right⟩

end VG.Proof.TripleDes.RISCV64
