import Batteries.Logic
import VerifiedGarbage.Proof.TripleDes.X86.Key.Component
import VerifiedGarbage.Proof.Rc2.X86.RoundSteps
import VerifiedGarbage.Proof.TripleDes.X86.CorrectBlock
import VerifiedGarbage.Proof.TripleDes.KeyMemory
import VerifiedGarbage.Proof.TripleDes.X86.ConstantTime

/-! ## `Copy` -/

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.RegUpd VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (Keep addr32)

def copyWord (a b : Nat) : List Instr :=
  [.mov .eax (.mem (memOp .edx a)), .store (memOp .edx b) .eax]

theorem copyWord_ok (s : State) (a b : Nat)
    (hr : InRegions (s.rd ++ s.wr) (addr (s.gpr .edx) a) 4)
    (hw : InRegions s.wr (addr (s.gpr .edx) b) 4) :
    ∃ s', runBlock isa (copyWord a b) s = some s' ∧
      Keep [.eax] {s with
        mem := (s.mem.writeW (addr (s.gpr .edx) b)
          (s.mem.readW (addr (s.gpr .edx) a) 32))} s' := by
  simp only [addr] at hr hw
  refine ⟨_, by
    simp only [copyWord, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load32, State.store32, State.ea, memOp, hr, hw, ite_true,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, reduceCtorEq, ite_false]
    rfl, ?_⟩
  refine ⟨?_, rfl, rfl, rfl⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [gpr_setReg, hr, ite_false]

structure CopyPost (base : Addr) (s : State) (n : Nat) (s' : State) : Prop where
  words : ∀ i < n, s'.mem.readW (base + BitVec.ofNat 64 (256 + 4 * i)) 32 =
    s.mem.readW (base + BitVec.ofNat 64 (4 * i)) 32
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r
  frame : Frame [⟨base + BitVec.ofNat 64 256, 128⟩] s.mem s'.mem

theorem copy_ok (s : State) (n : Nat) (hn : n ≤ 32)
    (fit : (s.gpr .edx).toNat + 384 ≤ 2 ^ 32)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (addr (s.gpr .edx) (4 * i)) 4)
    (hw : ∀ i < 32, InRegions s.wr (addr (s.gpr .edx) (256 + 4 * i)) 4) :
    WP isa (.block (Impl.TripleDes.X86.Key.copyWords n)) s (CopyPost (addr32 (s.gpr .edx)) s n) := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ hi => by omega_arith, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [Impl.TripleDes.X86.Key.copyWords, List.range_succ, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, WP.block_append_iff]
    apply WP.mono (ih (by omega_arith))
    intro s₁ h₁
    have base₁ : s₁.gpr .edx = s.gpr .edx := h₁.reg .edx (by decide)
    have readable : InRegions (s₁.rd ++ s₁.wr) (addr (s₁.gpr .edx) (4 * n)) 4 := by
      rw [h₁.rd, h₁.wr, base₁]; exact hr n (by omega_arith)
    have writable : InRegions s₁.wr (addr (s₁.gpr .edx) (256 + 4 * n)) 4 := by
      rw [h₁.wr, base₁]; exact hw n (by omega_arith)
    obtain ⟨s₂, run₂, keep₂⟩ := copyWord_ok s₁ (4 * n) (256 + 4 * n) readable writable
    have source : s₁.mem.readW (addr32 (s.gpr .edx) + BitVec.ofNat 64 (4 * n)) 32 =
        s.mem.readW (addr32 (s.gpr .edx) + BitVec.ofNat 64 (4 * n)) 32 := by
      apply h₁.frame.readW (r := ⟨addr32 (s.gpr .edx) + BitVec.ofNat 64 (4 * n), 4⟩)
        (Region.contains_self _ _) _ (by decide)
      intro r h
      obtain rfl := List.mem_singleton.mp h
      exact Offset.disjoint (addr32 (s.gpr .edx)) (by omega_arith) (by omega_arith) (by decide)
    have mem₂ : s₂.mem = s₁.mem.writeW (addr32 (s.gpr .edx) + BitVec.ofNat 64 (256 + 4 * n))
        (s.mem.readW (addr32 (s.gpr .edx) + BitVec.ofNat 64 (4 * n)) 32) := by
      have hm := keep₂.mem
      rw [base₁, addr_eq (by omega_arith : (s.gpr .edx).toNat + (256 + 4 * n) < 2 ^ 32),
        addr_eq (by omega_arith : (s.gpr .edx).toNat + 4 * n < 2 ^ 32)] at hm
      change s₂.mem = s₁.mem.writeW (addr32 (s.gpr .edx) + BitVec.ofNat 64 (256 + 4 * n))
        (s₁.mem.readW (addr32 (s.gpr .edx) + BitVec.ofNat 64 (4 * n)) 32) at hm
      rw [source] at hm
      exact hm
    refine WP.of_runBlock ⟨s₂, run₂, ⟨?_, keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr,
      fun r hr => (keep₂.reg r (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hr)).trans
        (h₁.reg r hr), ?_⟩⟩
    · intro i hi
      rw [mem₂]
      by_cases he : i = n
      · subst i; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep (addr32 (s.gpr .edx)) (by omega_arith) (by omega_arith)
          (by omega_arith)) (by decide)]
        exact h₁.words i (by omega_arith)
    · rw [mem₂]
      apply h₁.frame.writeW (List.mem_singleton_self _) _
      have hc := Offset.contains_base (addr32 (s.gpr .edx) + BitVec.ofNat 64 256)
        (d := 4 * n) (n := 4) (k := 128) (by omega_arith) (by omega_arith)
      rw [Offset.add_ofNat_add_ofNat] at hc
      exact hc

structure CopySchedulePost (s s' : State) : Prop where
  keys : ∀ i < 16, s'.mem.readW (addr32 (scheduleArg s) + BitVec.ofNat 64 (256 + 8 * i)) 64 =
    s.mem.readW (addr32 (scheduleArg s) + BitVec.ofNat 64 (8 * i)) 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .eax → r ≠ .edx → s'.gpr r = s.gpr r
  frame : Frame [⟨addr32 (scheduleArg s) + BitVec.ofNat 64 256, 128⟩] s.mem s'.mem

theorem copyThird_ok (s : State) (fit : (scheduleArg s).toNat + 384 ≤ 2 ^ 32)
    (harg : InRegions (s.rd ++ s.wr) (VG.X86.Straight.wordAddr (s.gpr .esp) 3) 4)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (addr (scheduleArg s) (4 * i)) 4)
    (hw : ∀ i < 32, InRegions s.wr (addr (scheduleArg s) (256 + 4 * i)) 4) :
    WP isa (.block Impl.TripleDes.X86.Key.copyThird) s (CopySchedulePost s) := by
  rw [Impl.TripleDes.X86.Key.copyThird, WP.block_append_iff]
  let s₀ := s.setReg .edx (scheduleArg s)
  have he : exec (.mov .edx (.mem (memOp .esp 12))) s = some s₀ := by
    simp only [exec, readSrc, State.load32, State.ea, memOp]
    change (if InRegions (s.rd ++ s.wr) (VG.X86.Straight.wordAddr (s.gpr .esp) 3) 4 then
      some (scheduleArg s) else none).map (s.setReg .edx) = some s₀
    rw [ite_eq_left harg, Option.map_some]
  refine WP.of_runBlock ⟨s₀, by simp only [runBlock_cons, he, runStep_some, runBlock_nil], ?_⟩
  have ptr₀ : s₀.gpr .edx = scheduleArg s := gpr_setReg_self _ _ _
  apply WP.mono (copy_ok s₀ 32 (by decide) (by rw [ptr₀]; exact fit)
    (by rw [ptr₀]; exact hr) (by rw [ptr₀]; exact hw))
  intro s₁ h₁
  refine ⟨?_, h₁.rd, h₁.wr, ?_, ?_⟩
  · intro i hi
    let p := addr32 (scheduleArg s)
    have h0 := h₁.words (2 * i) (by omega_arith)
    have h1 := h₁.words (2 * i + 1) (by omega_arith)
    rw [ptr₀] at h0 h1
    change s₁.mem.readW (p + BitVec.ofNat 64 (256 + 8 * i)) 64 =
      s.mem.readW (p + BitVec.ofNat 64 (8 * i)) 64
    rw [← readW_pair, ← readW_pair]
    have d0 : 256 + 4 * (2 * i) = 256 + 8 * i := by omega_arith
    have d1 : 256 + 4 * (2 * i + 1) = 256 + 8 * i + 4 := by omega_arith
    have a0 : 4 * (2 * i) = 8 * i := by omega_arith
    have a1 : 4 * (2 * i + 1) = 8 * i + 4 := by omega_arith
    rw [d0, a0] at h0
    rw [d1, a1, ← Offset.add_ofNat_add_ofNat (addr32 (scheduleArg s)) (256 + 8 * i) 4,
      ← Offset.add_ofNat_add_ofNat (addr32 (scheduleArg s)) (8 * i) 4] at h1
    change s₁.mem.readW ((p + BitVec.ofNat 64 (256 + 8 * i)) + 4) 32 =
      s.mem.readW ((p + BitVec.ofNat 64 (8 * i)) + 4) 32 at h1
    change s₁.mem.readW (p + BitVec.ofNat 64 (256 + 8 * i)) 32 =
      s.mem.readW (p + BitVec.ofNat 64 (8 * i)) 32 at h0
    exact congrArg₂ (fun (hi lo : BitVec 32) => hi ++ lo) h1 h0
  · intro r ha hd
    exact (h₁.reg r ha).trans (gpr_setReg_of_ne s _ hd)
  · have hf := h₁.frame
    rw [ptr₀] at hf
    exact hf

end VG.Proof.TripleDes.X86.Key

end

/-! ## `Composition` -/

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.Straight
open VG.Proof.Rc2.X86 (addr32)
open VG.Proof.TripleDes (componentKeys componentOffset)

def keyLength (s : State) : Nat := (arg s 1).toNat
abbrev keyR (s : State) : Region := ⟨addr32 (keyArg s), keyLength s⟩
abbrev outputR (s : State) : Region := ⟨addr32 (scheduleArg s), 384⟩
def slot (base : Addr) (c j : Nat) : Addr := base + BitVec.ofNat 64 (128 * c + 8 * j)

structure Components (origin s : State) (done : Nat) : Prop where
  keys : ∀ c < done, ∀ j < 16, s.mem.readW (slot (addr32 (scheduleArg origin)) c j) 64 =
    ((componentKeys origin.mem (addr32 (keyArg origin)) (keyLength origin) c).getD j 0).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  bp : s.gpr .ebp = origin.gpr .ebp
  sp : s.gpr .esp = origin.gpr .esp
  args : ∀ i < 4, arg s i = arg origin i
  frame : Frame [outputR origin, workRegion origin] origin.mem s.mem

structure Permissions (s : State) : Prop where
  ok : Ok sboxCfg s
  reads : ∀ offset, offset + 4 ≤ keyLength s →
    InRegions (s.rd ++ s.wr) (addr32 (keyArg s) + BitVec.ofNat 64 offset) 4
  writes : ∀ offset, offset + 4 ≤ 384 →
    InRegions s.wr (addr32 (scheduleArg s) + BitVec.ofNat 64 offset) 4
  argRead : ∀ i ∈ [1, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4
  argOutput : (⟨argAddr s 0, 16⟩ : Region).Disjoint (outputR s)
  argWork : (⟨argAddr s 0, 16⟩ : Region).Disjoint (workRegion s)
  keyOutput : (keyR s).Disjoint (outputR s)
  keyWork : (keyR s).Disjoint (workRegion s)
  outputWork : (outputR s).Disjoint (workRegion s)
  valid : Spec.TripleDes.validKey (keyLength s)
  keyFit : (keyArg s).toNat + keyLength s ≤ 2 ^ 32
  outputFit : (scheduleArg s).toNat + 384 ≤ 2 ^ 32
  spFit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32

theorem Components.keyArg {origin s : State} {done : Nat} (h : Components origin s done) :
    keyArg s = keyArg origin := by
  change s.mem.readW (wordAddr (s.gpr .esp) 1) 32 = _
  rw [← argument_word s 0, h.args 0 (by decide), argument_word origin 0]
  rfl

theorem Components.scheduleArg {origin s : State} {done : Nat} (h : Components origin s done) :
    scheduleArg s = Key.scheduleArg origin := by
  change s.mem.readW (wordAddr (s.gpr .esp) 3) 32 = _
  rw [← argument_word s 2, h.args 2 (by decide), argument_word origin 2]
  rfl

theorem Permissions.congr {s t : State} (hp : Permissions s)
    (args : ∀ i < 4, arg t i = arg s i) (bp : t.gpr .ebp = s.gpr .ebp)
    (sp : t.gpr .esp = s.gpr .esp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Permissions t := by
  have key : keyArg t = keyArg s := by
    change t.mem.readW (wordAddr (t.gpr .esp) 1) 32 = _
    rw [← argument_word t 0, args 0 (by decide), argument_word s 0]
    rfl
  have output : scheduleArg t = scheduleArg s := by
    change t.mem.readW (wordAddr (t.gpr .esp) 3) 32 = _
    rw [← argument_word t 2, args 2 (by decide), argument_word s 2]
    rfl
  have len : keyLength t = keyLength s := by unfold keyLength; rw [args 1 (by decide)]
  have work : workRegion t = workRegion s := by unfold workRegion; rw [bp]
  have argBase : argAddr t 0 = argAddr s 0 := by unfold argAddr; rw [sp]
  refine ⟨hp.ok.congr bp bp rd wr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro off ho; rw [rd, wr, key]; exact hp.reads off (by rwa [len] at ho)
  · intro off ho; rw [wr, output]; exact hp.writes off ho
  · intro i hi; rw [rd, wr, sp]; exact hp.argRead i hi
  · rw [argBase, outputR, output]; exact hp.argOutput
  · rw [argBase, work]; exact hp.argWork
  · rw [keyR, key, len, outputR, output]; exact hp.keyOutput
  · rw [keyR, key, len, work]; exact hp.keyWork
  · rw [outputR, output, work]; exact hp.outputWork
  · rw [len]; exact hp.valid
  · rw [key, len]; exact hp.keyFit
  · rw [output]; exact hp.outputFit
  · rw [sp]; exact hp.spFit

theorem componentStep_ok (origin s : State) (c : Nat) (hc : c < 3)
    (hp : Permissions origin) (hs : Components origin s c)
    (hoff : componentOffset (keyLength origin) c = 8 * c) :
    WP isa (Impl.TripleDes.X86.Key.component (8 * c) c) s (Components origin · (c + 1)) := by
  have offBound := VG.Proof.TripleDes.componentOffset_bound _ c hp.valid hc
  rw [hoff] at offBound
  have hok : Ok sboxCfg s := hp.ok.congr hs.bp hs.bp hs.rd hs.wr
  have kfit : (keyArg s).toNat + 8 * c + 8 ≤ 2 ^ 32 := by
    rw [hs.keyArg]; omega_using [hp.keyFit, offBound]
  have sfit : (scheduleArg s + BitVec.ofNat 32 (128 * c)).toNat + 128 ≤ 2 ^ 32 := by
    rw [hs.scheduleArg, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hc] : 128 * c < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega_using [hp.outputFit, hc] : (Key.scheduleArg origin).toNat + 128 * c < 2 ^ 32)]
    omega_using [hp.outputFit, hc]
  have args : ∀ i ∈ [1, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4 := by
    rw [hs.rd, hs.wr, hs.sp]; exact hp.argRead
  have reads : ∀ t < 2, InRegions (s.rd ++ s.wr) (keyAddr s (8 * c + 4 * t)) 4 := by
    intro t ht
    change InRegions (s.rd ++ s.wr) (addr32 (keyArg s + BitVec.ofNat 32 (8 * c + 4 * t))) 4
    rw [hs.keyArg, VG.Proof.Rc2.X86.addr_add (by omega_using [hp.keyFit, offBound, ht]), hs.rd, hs.wr]
    exact hp.reads _ (by omega_using [offBound, ht])
  have writes : ∀ j < 16, ∀ t < 2, InRegions s.wr
      (addr32 (scheduleArg s + BitVec.ofNat 32 (128 * c)) + BitVec.ofNat 64 (8 * j + 4 * t)) 4 := by
    intro j hj t ht
    rw [hs.scheduleArg, VG.Proof.Rc2.X86.addr_add (by omega_using [hp.outputFit, hc]),
      Offset.add_ofNat_add_ofNat, hs.wr]
    exact hp.writes _ (by omega_using [hc, hj, ht])
  have componentSub : Region.Sub
      (scheduleRegion (scheduleArg s + BitVec.ofNat 32 (128 * c))) (outputR origin) := by
    rw [scheduleRegion, hs.scheduleArg, VG.Proof.Rc2.X86.addr_add (by omega_using [hp.outputFit, hc])]
    exact Offset.sub_base _ (by omega_using [hc])
  have work : workRegion s = workRegion origin := by unfold workRegion; rw [hs.bp]
  have dis : (scheduleRegion (scheduleArg s + BitVec.ofNat 32 (128 * c))).Disjoint (workRegion s) := by
    rw [work]; exact hp.outputWork.sub_left componentSub
  apply WP.mono (component_ok s (8 * c) c hok kfit sfit args reads writes dis)
  intro t ht
  have frame : Frame [⟨addr32 (Key.scheduleArg origin) + BitVec.ofNat 64 (128 * c), 128⟩,
      workRegion origin] s.mem t.mem := by
    have h := ht.frame
    rw [work, scheduleRegion, hs.scheduleArg,
      VG.Proof.Rc2.X86.addr_add (by omega_using [hp.outputFit, hc])] at h
    exact h
  have targs := VG.Proof.Rc2.X86.arguments_frame 4 ht.frame ht.sp
    (by rw [hs.sp]; exact hp.spFit) (by
      intro r hr
      rw [List.mem_cons, List.mem_singleton] at hr
      have a : argAddr s 0 = argAddr origin 0 := by unfold argAddr; rw [hs.sp]
      rw [a]
      rcases hr with rfl | rfl
      · exact hp.argOutput.sub_right componentSub
      · rw [work]; exact hp.argWork)
  have key : Spec.TripleDes.blockAt s.mem (keyAddr s (8 * c)) =
      Spec.TripleDes.blockAt origin.mem (addr32 (Key.keyArg origin) + BitVec.ofNat 64 (8 * c)) := by
    change Spec.TripleDes.blockAt s.mem (addr32 (keyArg s + BitVec.ofNat 32 (8 * c))) = _
    rw [hs.keyArg, VG.Proof.Rc2.X86.addr_add (by omega_using [hp.keyFit, offBound])]
    apply VG.Proof.TripleDes.blockAt_eq_of_frame _ hs.frame
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hp.keyOutput.sub_left (Offset.sub_base _ offBound)
    · obtain rfl := List.mem_singleton.mp hr
      exact hp.keyWork.sub_left (Offset.sub_base _ offBound)
  refine ⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr, ht.bp.trans hs.bp, ht.sp.trans hs.sp,
    fun i hi => (targs i hi).trans (hs.args i hi), hs.frame.trans (ht.frame.sub ?_)⟩
  · intro k hk j hj
    by_cases he : k = c
    · subst k
      have h := ht.keys j hj
      rw [hs.scheduleArg, VG.Proof.Rc2.X86.addr_add (by omega_using [hp.outputFit, hc]),
        Offset.add_ofNat_add_ofNat, key] at h
      unfold componentKeys
      rw [hoff]
      exact h
    · have before : k < c := by omega_using [hk, he]
      have keySub : Region.Sub ⟨slot (addr32 (Key.scheduleArg origin)) k j, 8⟩ (outputR origin) :=
        Offset.sub_base _ (by omega_using [before, hc, hj])
      have hmem := frame.readW (a := slot (addr32 (Key.scheduleArg origin)) k j) (w := 64)
        (r := ⟨slot (addr32 (Key.scheduleArg origin)) k j, 8⟩) (Region.contains_self _ _) (by
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact Offset.disjoint _ (by omega_using [before, hj])
              (by omega_using [before, hc, hj]) (by omega_using [hc])
          · obtain rfl := List.mem_singleton.mp hr
            exact hp.outputWork.sub_left keySub) (by decide)
      exact hmem.trans (hs.keys k before j hj)
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨outputR origin, by simp, componentSub⟩
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨workRegion origin, by simp, by rw [work]; exact fun _ h => h⟩

theorem copyThirdStep_ok (origin s : State) (hp : Permissions origin)
    (hs : Components origin s 2) (hn : keyLength origin = 16) :
    WP isa (.block Impl.TripleDes.X86.Key.copyThird) s (Components origin · 3) := by
  have fit : (scheduleArg s).toNat + 384 ≤ 2 ^ 32 := by rw [hs.scheduleArg]; exact hp.outputFit
  have reads : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.X86.addr (scheduleArg s) (4 * i)) 4 := by
    intro i hi
    rw [hs.scheduleArg, addr_eq (by omega_using [hp.outputFit, hi]), hs.rd, hs.wr]
    obtain ⟨r, hr, hc⟩ := hp.writes (4 * i) (by omega_using [hi])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have writes : ∀ i < 32, InRegions s.wr (VG.X86.addr (scheduleArg s) (256 + 4 * i)) 4 := by
    intro i hi
    rw [hs.scheduleArg, addr_eq (by omega_using [hp.outputFit, hi]), hs.wr]
    exact hp.writes _ (by omega_using [hi])
  have ar : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 3) 4 := by
    rw [hs.rd, hs.wr, hs.sp]; exact hp.argRead 3 (by decide)
  apply WP.mono (copyThird_ok s fit ar reads writes)
  intro t ht
  have frame : Frame [⟨addr32 (Key.scheduleArg origin) + BitVec.ofNat 64 256, 128⟩] s.mem t.mem := by
    have h := ht.frame; rw [hs.scheduleArg] at h; exact h
  have sub : Region.Sub ⟨addr32 (Key.scheduleArg origin) + BitVec.ofNat 64 256, 128⟩ (outputR origin) :=
    Offset.sub_base _ (by decide)
  have sp : t.gpr .esp = s.gpr .esp := ht.reg .esp (by decide) (by decide)
  have targs := VG.Proof.Rc2.X86.arguments_frame 4 frame sp
    (by rw [hs.sp]; exact hp.spFit) (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      have a : argAddr s 0 = argAddr origin 0 := by unfold argAddr; rw [hs.sp]
      rw [a]; exact hp.argOutput.sub_right sub)
  refine ⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    (ht.reg .ebp (by decide) (by decide)).trans hs.bp, sp.trans hs.sp,
    fun i hi => (targs i hi).trans (hs.args i hi), hs.frame.trans (frame.sub ?_)⟩
  · intro c hc j hj
    by_cases he : c = 2
    · subst c
      have hRepeat : componentKeys origin.mem (addr32 (Key.keyArg origin)) (keyLength origin) 2 =
          componentKeys origin.mem (addr32 (Key.keyArg origin)) (keyLength origin) 0 := by rw [hn]; rfl
      have h := ht.keys j hj
      rw [hs.scheduleArg] at h
      change t.mem.readW (addr32 (Key.scheduleArg origin) + BitVec.ofNat 64 (256 + 8 * j)) 64 = _
      rw [hRepeat]
      have first := hs.keys 0 (by decide) j hj
      simp only [slot, Nat.mul_zero, Nat.zero_add] at first
      exact h.trans first
    · have before : c < 2 := by omega_using [hc, he]
      have hm := frame.readW (a := slot (addr32 (Key.scheduleArg origin)) c j) (w := 64)
        (r := ⟨slot (addr32 (Key.scheduleArg origin)) c j, 8⟩) (Region.contains_self _ _) (by
          intro r hr; obtain rfl := List.mem_singleton.mp hr
          exact Offset.disjoint _ (by omega_using [before, hj])
            (by omega_using [before, hj]) (by decide)) (by decide)
      exact hm.trans (hs.keys c before j hj)
  · intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨outputR origin, by simp, sub⟩

def componentIndex (i : Nat) : Nat := if i < 16 then 0 else if i < 32 then 1 else 2

theorem index_partition : ∀ i < 48, componentIndex i < 3 ∧ i % 16 < 16 ∧
    8 * i = 128 * componentIndex i + 8 * (i % 16) := by decide

theorem Components.schedule {origin s : State} (h : Components origin s 3) :
    Spec.TripleDes.scheduleAt s.mem (addr32 (Key.scheduleArg origin)) =
      VG.Proof.TripleDes.expandedMemory origin.mem (addr32 (Key.keyArg origin)) (keyLength origin) := by
  apply Vector.ext
  intro i hi
  have fact := index_partition i hi
  have keys := h.keys (componentIndex i) fact.1 (i % 16) fact.2.1
  rw [slot, ← fact.2.2] at keys
  rw [VG.Proof.TripleDes.scheduleAt_readW s.mem (addr32 (Key.scheduleArg origin)) i hi]
  simp only [VG.Proof.TripleDes.expandedMemory, Vector.getElem_ofFn]
  by_cases h16 : i < 16
  · simpa only [componentIndex, h16, ite_true] using keys
  · by_cases h32 : i < 32
    · simpa only [componentIndex, h16, h32, ite_false, ite_true] using keys
    · simpa only [componentIndex, h16, h32, ite_false] using keys

end VG.Proof.TripleDes.X86.Key

end

/-! ## `Body` -/

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (Keep)

theorem lengthCompare (x : BitVec 32) : ((x - 16) == 0) = decide (x.toNat = 16) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have h' : x = 16 := by bv_omega_using [h]
    rw [h']; rfl
  · intro h
    have h' : x = 16 := BitVec.eq_of_toNat_eq h
    rw [h']; rfl

theorem cmpLength_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 2) 4) :
    ∃ s', runBlock isa [.mov .eax (.mem (memOp .esp 8)), .alu .cmp .eax (.imm 16)] s = some s' ∧
      isa.eval .e s' = some (decide (keyLength s = 16)) ∧ Keep [.eax] s s' := by
  simp only [wordAddr, addr] at hr
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      State.load32, State.ea, memOp, hr, ite_true, Option.bind_some, Option.map_some,
      gpr_setReg, ite_true]
    rfl, ?_, ?_⟩
  · change some ((s.mem.readW (wordAddr (s.gpr .esp) 2) 32 - 16) == 0) = _
    rw [← argument_word s 1]
    exact congrArg some (lengthCompare (arg s 1))
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [gpr_arithFlags, gpr_setReg, hr, ite_false]

theorem Components.keep {origin s t : State} {n : Nat} (hs : Components origin s n)
    (ht : Keep [.eax] s t) : Components origin t n := by
  have sp : t.gpr .esp = s.gpr .esp := ht.reg .esp (by decide)
  refine ⟨fun c hc j hj => by rw [ht.mem]; exact hs.keys c hc j hj,
    ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    (ht.reg .ebp (by decide)).trans hs.bp, sp.trans hs.sp, ?_, ?_⟩
  · intro i hi
    unfold arg argAddr
    rw [sp, ht.mem]
    exact hs.args i hi
  · rw [ht.mem]; exact hs.frame

theorem body_ok (origin s : State) (hp : Permissions origin) (hs : Components origin s 0)
    (lenRead : InRegions (origin.rd ++ origin.wr) (wordAddr (origin.gpr .esp) 2) 4)
    (Q : State → Prop)
    (finish : ∀ t, Components origin t 3 → WP isa (.block Impl.TripleDes.X86.Key.restore) t Q) :
    WP isa (.seq (Impl.TripleDes.X86.Key.component 0 0)
      (.seq (Impl.TripleDes.X86.Key.component 8 1)
        (.seq (.block [.mov .eax (.mem (memOp .esp 8)), .alu .cmp .eax (.imm 16)])
          (.seq (.ite .e (.block Impl.TripleDes.X86.Key.copyThird)
            (Impl.TripleDes.X86.Key.component 16 2)) (.block Impl.TripleDes.X86.Key.restore))))) s Q := by
  apply WP.seq
  apply WP.mono (componentStep_ok origin s 0 (by decide) hp hs (by rfl))
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (componentStep_ok origin s₁ 1 (by decide) hp hs₁ (by rfl))
  intro s₂ hs₂
  apply WP.seq
  obtain ⟨s₃, run₃, flag₃, keep₃⟩ := cmpLength_ok s₂
    (by rw [hs₂.rd, hs₂.wr, hs₂.sp]; exact lenRead)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have hs₃ := hs₂.keep keep₃
  apply WP.seq
  apply WP.mono (Q := (Components origin · 3)) ?_
  · intro t ht; exact finish t ht
  have flag : isa.eval .e s₃ = some (decide (keyLength origin = 16)) := by
    rw [flag₃, keyLength, hs₂.args 1 (by decide)]
    rfl
  by_cases h16 : keyLength origin = 16
  · apply WP.ite true (by simpa only [h16, decide_true] using flag)
    · intro _; exact copyThirdStep_ok origin s₃ hp hs₃ h16
    · simp
  · apply WP.ite false (by simpa only [h16, decide_false] using flag)
    · simp
    · intro _
      exact componentStep_ok origin s₃ 2 (by decide) hp hs₃
        (by simp only [VG.Proof.TripleDes.componentOffset, h16, and_false, ite_false])

end VG.Proof.TripleDes.X86.Key

end

/-! ## `Entry` -/

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.Straight VG.X86.RegUpd
open VG.Proof.Rc2.X86 (addr32)

def preparedKey (s : State) : State := s.setReg .ebp (scratchArg s 4)
abbrev scratchR (s : State) : Region := ⟨addr32 (scratchArg s 4), 512⟩
abbrev savedR (s : State) : Region := ⟨addr32 (scratchArg s 4), 16⟩

structure HeadPre (s : State) : Prop where
  permissions : Permissions (preparedKey s)
  scratchFit : (scratchArg s 4).toNat + 512 ≤ 2 ^ 32
  argRead : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 4) 4
  lenRead : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 2) 4
  saveWrites : ∀ i < 4, InRegions s.wr (addr32 (scratchArg s 4) + BitVec.ofNat 64 (4 * i)) 4
  argsSave : (⟨argAddr s 0, 16⟩ : Region).Disjoint (savedR s)
  keyScratch : (keyR s).Disjoint (scratchR s)
  outputScratch : (outputR s).Disjoint (scratchR s)

structure ExpandPost (original s : State) : Prop where
  result : Spec.TripleDes.scheduleAt s.mem (addr32 (scheduleArg original)) =
    Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt original.mem (addr32 (keyArg original)) (keyLength original))
  saved : ∀ r ∈ VG.Impl.TripleDes.X86.savedRegs, s.gpr r = original.gpr r
  sp : s.gpr .esp = original.gpr .esp
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  frame : Frame [outputR original, scratchR original] original.mem s.mem

theorem expandKey_ok (s : State) (hp : HeadPre s) :
    WP isa Impl.TripleDes.X86.Key.expandKey s (ExpandPost s) := by
  rw [Impl.TripleDes.X86.Key.expandKey]
  apply WP.seq
  apply WP.mono (saveWithArg_ok s 4 hp.argRead hp.scratchFit hp.saveWrites)
  intro s₁ h₁
  have sp₁ : s₁.gpr .esp = s.gpr .esp := h₁.reg .esp (by decide) (by decide)
  have ghostSP : (preparedKey s).gpr .esp = s.gpr .esp := gpr_setReg_of_ne s _ (by decide)
  have args₁ := VG.Proof.Rc2.X86.arguments_frame 4 h₁.frame sp₁
    (by have h := hp.permissions.spFit; rw [ghostSP] at h; exact h)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact hp.argsSave)
  have ghostArgs : ∀ i, arg (preparedKey s) i = arg s i := by
    intro i; unfold arg argAddr; rw [ghostSP]; rfl
  have permissions₁ : Permissions s₁ := hp.permissions.congr
    (fun i hi => (args₁ i hi).trans (ghostArgs i).symm)
    (by rw [preparedKey, gpr_setReg_self]; exact h₁.bp)
    (sp₁.trans ghostSP.symm) h₁.rd h₁.wr
  have init : Components s₁ s₁ 0 :=
    ⟨fun _ h => by omega_arith, rfl, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  apply body_ok s₁ s₁ permissions₁ init
    (by rw [h₁.rd, h₁.wr, sp₁]; exact hp.lenRead)
  intro s₂ h₂
  have bp₂ : s₂.gpr .ebp = scratchArg s 4 := h₂.bp.trans h₁.bp
  have args₂ (i : Nat) (hi : i < 4) : arg s₂ i = arg s i :=
    (h₂.args i hi).trans (args₁ i hi)
  have output₁ : outputR s₁ = outputR s := by
    unfold outputR
    change Region.mk (addr32 (s₁.mem.readW (wordAddr (s₁.gpr .esp) 3) 32)) 384 = _
    rw [← argument_word s₁ 2, args₁ 2 (by decide), argument_word s 2]; rfl
  have outputArg₁ : scheduleArg s₁ = scheduleArg s := by
    change s₁.mem.readW (wordAddr (s₁.gpr .esp) 3) 32 = _
    rw [← argument_word s₁ 2, args₁ 2 (by decide), argument_word s 2]; rfl
  have keyArg₁ : keyArg s₁ = keyArg s := by
    change s₁.mem.readW (wordAddr (s₁.gpr .esp) 1) 32 = _
    rw [← argument_word s₁ 0, args₁ 0 (by decide), argument_word s 0]; rfl
  have len₁ : keyLength s₁ = keyLength s := by unfold keyLength; rw [args₁ 1 (by decide)]
  have scratchSub (i : Nat) (hi : i < 4) :
      Region.Sub ⟨addr32 (scratchArg s 4) + BitVec.ofNat 64 (4 * i), 4⟩ (scratchR s) :=
    Offset.sub_base _ (by omega_using [hi])
  have saved₂ : Saved s s₂ := by
    intro i hi
    rw [bp₂]
    have hm := h₂.frame.readW (a := addr32 (scratchArg s 4) + BitVec.ofNat 64 (4 * i)) (w := 32)
      (r := ⟨addr32 (scratchArg s 4) + BitVec.ofNat 64 (4 * i), 4⟩)
      (Region.contains_self _ _) (by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · rw [output₁]; exact (hp.outputScratch.sub_right (scratchSub i hi)).symm
        · obtain rfl := List.mem_singleton.mp hr
          have sep := savedSlot_work_disjoint s₁ i hi
          rw [h₁.bp] at sep
          exact sep) (by decide)
    have saved₁ := h₁.saved i hi
    rw [h₁.bp] at saved₁
    exact hm.trans saved₁
  have reads₂ : ∀ i < 4, InRegions (s₂.rd ++ s₂.wr)
      (addr32 (s₂.gpr .ebp) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, bp₂]
    obtain ⟨r, hr, hc⟩ := hp.saveWrites i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.mono (blockRestore_ok s s₂ saved₂ (by rw [bp₂]; exact hp.scratchFit) reads₂)
  intro s₃ h₃
  have initialBytes := VG.Proof.TripleDes.bytesAt_eq_of_frame (addr32 (keyArg s)) (keyLength s)
    h₁.frame (by
      have fit := permissions₁.keyFit
      rw [keyArg₁, len₁] at fit
      have bound := (keyArg s).isLt
      omega_using [fit, bound]) (by
        intro r hr; obtain rfl := List.mem_singleton.mp hr
        exact hp.keyScratch.sub_right (Region.sub_prefix (by decide)))
  have result := h₂.schedule
  rw [outputArg₁, keyArg₁, len₁] at result
  rw [← VG.Proof.TripleDes.expandKey_memory s₁.mem (addr32 (keyArg s)) (keyLength s)
    (by have valid := permissions₁.valid; rw [len₁] at valid; exact valid), initialBytes] at result
  refine ⟨?_, h₃.saved, h₃.sp.trans (h₂.sp.trans sp₁), h₃.rd.trans (h₂.rd.trans h₁.rd),
    h₃.wr.trans (h₂.wr.trans h₁.wr), ?_⟩
  · rw [h₃.mem]; exact result
  · rw [h₃.mem]
    have first : Frame [outputR s, scratchR s] s.mem s₁.mem := h₁.frame.sub (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ⟨scratchR s, by simp, Region.sub_prefix (by decide)⟩)
    exact first.trans (h₂.frame.sub (by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [output₁]; exact ⟨outputR s, by simp, fun _ h => h⟩
      · obtain rfl := List.mem_singleton.mp hr
        refine ⟨scratchR s, by simp, ?_⟩
        rw [workRegion, h₁.bp]
        exact Offset.sub_base _ (by decide)))

end VG.Proof.TripleDes.X86.Key

end

/-! ## `Contract` -/

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)

def contract : Contract isa where
  pre s :=
    let key : Region := ⟨addr32 (arg s 0), (arg s 1).toNat⟩
    let output : Region := ⟨addr32 (arg s 2), 384⟩
    let scratch : Region := ⟨addr32 (arg s 3), 512⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨addr32 (s.gpr .esp), 4⟩
    s.rd = [key, args] ∧ s.wr = [output, scratch] ∧ key.Disjoint output ∧
      key.Disjoint scratch ∧ output.Disjoint scratch ∧ args.Disjoint output ∧
      args.Disjoint scratch ∧ ret.Disjoint output ∧ ret.Disjoint scratch ∧
      Spec.TripleDes.validKey (arg s 1).toNat ∧ (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 384 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 512 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' := Spec.TripleDes.scheduleAt s'.mem (addr32 (arg s 2)) =
    Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (addr32 (arg s 0)) (arg s 1).toNat)
  pub s t := s.gpr .esp = t.gpr .esp ∧ ∀ i < 4, arg s i = arg t i

end VG.Proof.TripleDes.X86.Key

end

/-! ## `Pre` -/

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.Straight VG.X86.RegUpd
open VG.Proof.Rc2.X86 (addr32 argContainsCount)

theorem key_argument (s : State) : keyArg s = arg s 0 := (argument_word s 0).symm
 theorem output_argument (s : State) : scheduleArg s = arg s 2 := (argument_word s 2).symm
 theorem scratch_argument (s : State) : scratchArg s 4 = arg s 3 := (argument_word s 3).symm

theorem headPre_of_contract (s : State) (hs : contract.pre s) : HeadPre s := by
  obtain ⟨rd, wr, keyOut, keyScratch, outScratch, argsOut, argsScratch, _, _,
    valid, keyFit, outputFit, scratchFit, spFit⟩ := hs
  have bp : (preparedKey s).gpr .ebp = arg s 3 := by rw [preparedKey, gpr_setReg_self, scratch_argument]
  have sp : (preparedKey s).gpr .esp = s.gpr .esp := gpr_setReg_of_ne s _ (by decide)
  have args (i : Nat) : arg (preparedKey s) i = arg s i := by unfold arg argAddr; rw [sp]; rfl
  have key : keyArg (preparedKey s) = arg s 0 := by rw [key_argument, args]
  have output : scheduleArg (preparedKey s) = arg s 2 := by rw [output_argument, args]
  have len : keyLength (preparedKey s) = (arg s 1).toNat := by unfold keyLength; rw [args]
  have argBase : argAddr (preparedKey s) 0 = argAddr s 0 := by unfold argAddr; rw [sp]
  have workSub : Region.Sub (workRegion (preparedKey s)) ⟨addr32 (arg s 3), 512⟩ := by
    rw [workRegion, bp]; exact Offset.sub_base _ (by decide)
  have saveSub : Region.Sub (savedR s) ⟨addr32 (arg s 3), 512⟩ := by
    rw [savedR, scratch_argument]; exact Region.sub_prefix (by decide)
  have contains : ∀ i, 1 ≤ i → i ≤ 4 → (⟨argAddr s 0, 16⟩ : Region).Contains
      (wordAddr (s.gpr .esp) i) 4 := by
    intro i hlo hhi
    rw [wordAddr, addr_eq (by omega_using [spFit, hhi])]
    have h := argContainsCount s 4 spFit (i - 1) (by omega_using [hlo, hhi])
    rw [show 4 + 4 * (i - 1) = 4 * i by omega_using [hlo]] at h
    exact h
  have readArg : ∀ i, 1 ≤ i → i ≤ 4 → InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4 := by
    intro i hlo hhi
    rw [rd, wr]
    exact ⟨⟨argAddr s 0, 16⟩, by simp, contains i hlo hhi⟩
  have slots : ∀ i < 128, InRegions (preparedKey s).wr (wordAddr ((preparedKey s).gpr .ebp) i) 4 := by
    intro i hi
    rw [bp, wordAddr, addr_eq (by omega_using [scratchFit, hi])]
    change InRegions s.wr _ 4
    rw [wr]
    exact ⟨⟨addr32 (arg s 3), 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  have ok : Ok sboxCfg (preparedKey s) := by
    refine ⟨slots, ?_, ?_, ?_⟩
    · intro k hk; change k < 0 at hk; omega_arith
    · change ((preparedKey s).gpr .ebp).toNat + 512 ≤ 2 ^ 32; rw [bp]; exact scratchFit
    · intro k hk j hj; change j < 0 at hj; omega_arith
  refine ⟨?_, ?_, readArg 4 (by decide) (by decide), readArg 2 (by decide) (by decide), ?_,
    argsScratch.sub_right saveSub, ?_, ?_⟩
  · refine ⟨ok, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro off ho
      rw [len] at ho
      rw [key]
      change InRegions (s.rd ++ s.wr) _ 4
      rw [rd, wr]
      exact ⟨⟨addr32 (arg s 0), (arg s 1).toNat⟩, by simp,
        Offset.contains_base _ ho (by omega_using [ho, keyFit])⟩
    · intro off ho
      rw [output]
      change InRegions s.wr _ 4
      rw [wr]
      exact ⟨⟨addr32 (arg s 2), 384⟩, by simp, Offset.contains_base _ ho (by omega_using [ho])⟩
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      change InRegions (s.rd ++ s.wr) (wordAddr ((preparedKey s).gpr .esp) i) 4
      rw [sp]
      rcases hi with rfl | rfl
      · exact readArg 1 (by decide) (by decide)
      · exact readArg 3 (by decide) (by decide)
    · rw [argBase, outputR, output]; exact argsOut
    · rw [argBase]; exact argsScratch.sub_right workSub
    · rw [keyR, key, len, outputR, output]; exact keyOut
    · rw [keyR, key, len]; exact keyScratch.sub_right workSub
    · rw [outputR, output]; exact outScratch.sub_right workSub
    · rw [len]; exact valid
    · rw [key, len]; exact keyFit
    · rw [output]; exact outputFit
    · rw [sp]; exact spFit
  · rw [scratch_argument]; exact scratchFit
  · intro i hi
    rw [scratch_argument, wr]
    exact ⟨⟨addr32 (arg s 3), 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  · rw [keyR, key_argument, keyLength, scratchR, scratch_argument]; exact keyScratch
  · rw [outputR, output_argument, scratchR, scratch_argument]; exact outScratch

end VG.Proof.TripleDes.X86.Key

end

/-! ## `Correct` -/

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)

theorem expand_correct (s : State) (hs : contract.pre s) :
    WP isa Impl.TripleDes.X86.Key.expandKey s (fun s' => abiPreserved s s' ∧ contract.post s s') := by
  have hp := headPre_of_contract s hs
  obtain ⟨_, _, _, _, _, _, _, retOutput, retScratch, _⟩ := hs
  apply WP.mono (expandKey_ok s hp)
  intro s' hpost
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    have regs : ∀ r ∈ calleeSaved, r ∈ Impl.TripleDes.X86.savedRegs ∨ r = .esp := by decide
    rcases regs r hr with saved | rfl
    · exact hpost.saved r saved
    · exact hpost.sp
  · apply hpost.frame.readW (r := ⟨addr32 (s.gpr .esp), 4⟩) (Region.contains_self _ _) _ (by decide)
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · rw [outputR, output_argument]; exact retOutput
    · obtain rfl := List.mem_singleton.mp hr
      rw [scratchR, scratch_argument]; exact retScratch
  · have result := hpost.result
    rw [output_argument, key_argument, keyLength] at result
    exact result

end VG.Proof.TripleDes.X86.Key

end

/-! ## `ConstantTime` -/

section

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)

theorem keyTaint_wf {s : State} (hs : contract.pre s) : VG.X86.Taint.Wf keyTaint s := by
  obtain ⟨_, hwr, _, _, dataSep, argsData, argsScratch, retData, retScratch, _, _, dataFit, scratchFit, spFit⟩ := hs
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨spFit, ?_⟩, ?_⟩
  · rw [hwr]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨dataSep, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr32, BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_arith) retData argsData
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_arith) retScratch argsScratch
  · intro p hp
    simp only [keyTaint, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, addr32, arg, argAddr]

theorem keyTaint_agree {s t : State} (hs : contract.pre s)
    (ht : contract.pre t) (hp : contract.pub s t) :
    VG.X86.Taint.Agree keyTaint s t := by
  obtain ⟨sp, args⟩ := hp
  have fit : ∀ s, contract.pre s → (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 := by
    intro s hs; obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := hs; exact h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, keyTaint_wf hs,
    keyTaint_wf ht, VG.X86.Taint.slotsOk_empty,
    VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [keyTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [hs.2.1, ht.2.1, args 2 (by decide), args 3 (by decide)]
  · simp only [keyTaint] at hk
    rw [show VG.X86.Taint.depth keyTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (fit _ hs) h4 hk, VG.X86.Taint.argByte_eq (fit _ ht) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega_arith))

end VG.Proof.TripleDes.X86.Key

end
