module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Key.Steps
public import VerifiedGarbage.Proof.TripleDes.KeySchedule
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.TripleDes.KeyMemory
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.Mem

/-! ### `TripleDes.RISCV64.Key.Loop`, which only this module used -/

section

/-!
# One component's schedule

`loop_ok`: the sixteen rounds of a component key's expansion, storing the
round keys from `base` on; `component_ok`: with the key's load.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Key

open VG VG.RISCV64
open VG.Proof.TripleDes (keyPrefix keyInitial keyStep keyPrefix_succ)

structure LoopState (key : BitVec 64) (base : Addr) (origin : State) (j : Nat) (s : State) :
    Prop where
  c : s.gpr .a3 = (keyPrefix key j).1.setWidth 64
  d : s.gpr .a4 = (keyPrefix key j).2.1.setWidth 64
  counter : s.gpr .a6 = BitVec.ofNat 64 j
  pointer : s.gpr .a5 = base + BitVec.ofNat 64 (8 * j)
  keys : ∀ i < j, ∀ hi : i < 16, s.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64 =
    ((keyPrefix key j).2.2[i]'hi).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  reg : ∀ r ∈ keyKept, s.gpr r = origin.gpr r
  frame : Frame [⟨base, 128⟩] origin.mem s.mem

def LoopInv (key : BitVec 64) (base : Addr) (origin : State) (n : Nat) (s : State) : Prop :=
  1 ≤ n ∧ n ≤ 16 ∧ LoopState key base origin (16 - n) s

theorem loopBody_ok (key : BitVec 64) (base : Addr) (origin : State)
    (hw : ∀ j < 16, InRegions origin.wr (base + BitVec.ofNat 64 (8 * j)) 8)
    (j : Nat) (hj : j < 16) (s : State) (hs : LoopState key base origin j s) :
    WP isa (.seq Impl.TripleDes.RISCV64.Key.rotation (.block Impl.TripleDes.RISCV64.Key.storeRound)) s
      (fun s' => isa.eval (.nonzero .t0) s' = some (decide (j ≠ 15)) ∧
        LoopState key base origin (j + 1) s') := by
  apply WP.seq
  apply WP.mono (rotation_ok s _ _ j hj hs.c hs.d hs.counter)
  intro s₁ h₁
  have reg₁ : ∀ r ∈ (keyKept ++ [.a6, .a5]), s₁.gpr r = s.gpr r := by
    intro r hr
    exact h₁.only.reg r (by revert hr; cases r <;> decide)
  have write₁ : InRegions s₁.wr (s₁.gpr .a5) 8 := by
    rw [h₁.only.wr, hs.wr, reg₁ .a5 (by decide), hs.pointer]
    exact hw j hj
  apply WP.mono (storeRound_ok s₁ _ _ j hj h₁.c h₁.d
    ((reg₁ .a6 (by decide)).trans hs.counter) write₁)
  intro s₂ h₂
  have hmem : s₂.mem = s.mem.writeW (base + BitVec.ofNat 64 (8 * j))
      ((Spec.TripleDes.permute Spec.TripleDes.pc2
        ((keyPrefix key j).1.rotateLeft (Spec.TripleDes.rotations.getD j 0) ++
          (keyPrefix key j).2.1.rotateLeft (Spec.TripleDes.rotations.getD j 0))).setWidth 64) := by
    rw [h₂.mem, h₁.only.mem, reg₁ .a5 (by decide), hs.pointer]
  refine ⟨h₂.flag, ⟨?_, ?_, h₂.counter, ?_, ?_, h₂.rd.trans (h₁.only.rd.trans hs.rd),
    h₂.wr.trans (h₁.only.wr.trans hs.wr), h₂.sp.trans (h₁.only.sp.trans hs.sp), ?_, ?_⟩⟩
  · rw [keyPrefix_succ]
    exact (h₂.reg .a3 (by decide)).trans h₁.c
  · rw [keyPrefix_succ]
    exact (h₂.reg .a4 (by decide)).trans h₁.d
  · rw [h₂.ptr, reg₁ .a5 (by decide), hs.pointer]
    change base + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 8 = _
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun n => base + BitVec.ofNat 64 n) (by omega_using [])
  · intro i hi hi16
    rw [hmem, keyPrefix_succ]
    by_cases he : i = j
    · subst i
      rw [Mem.readW_writeW_self64]
      exact congrArg (BitVec.setWidth 64) (Vector.getElem_set!_self hj).symm
    · rw [Mem.readW_writeW_sep (Offset.sep base (by omega_using [hi, he])
        (by omega_using [hi16]) (by omega_using [hj])) (by decide), hs.keys i (by omega_using [hi, he]) hi16]
      exact congrArg (BitVec.setWidth 64) (Vector.getElem_set!_ne hi16 (Ne.symm he)).symm
  · intro r hr
    exact (h₂.reg r (by revert hr; cases r <;> decide)).trans
      ((reg₁ r (by revert hr; cases r <;> decide)).trans (hs.reg r hr))
  · rw [hmem]
    exact hs.frame.writeW (List.mem_singleton_self _) _
      (Offset.contains_base base (by omega_using [hj]) (by omega_using [hj]))

theorem loopStep (key : BitVec 64) (base : Addr) (origin : State)
    (hw : ∀ j < 16, InRegions origin.wr (base + BitVec.ofNat 64 (8 * j)) 8)
    (n : Nat) (s : State) (hs : LoopInv key base origin n s) :
    WP isa (.seq Impl.TripleDes.RISCV64.Key.rotation (.block Impl.TripleDes.RISCV64.Key.storeRound)) s
      (fun s' => (isa.eval (.nonzero .t0) s' = some false ∧ LoopState key base origin 16 s') ∨
        (isa.eval (.nonzero .t0) s' = some true ∧ ∃ m < n, LoopInv key base origin m s')) := by
  apply WP.mono (loopBody_ok key base origin hw (16 - n) (by omega_using [hs.1]) s hs.2.2)
  intro s' h
  by_cases last : n = 1
  · left
    have idx : 16 - n = 15 := by omega_using [last]
    refine ⟨?_, ?_⟩
    · simpa only [idx, ne_eq, not_true_eq_false, decide_false] using h.1
    · simpa only [idx] using h.2
  · right
    have idx : ¬16 - n = 15 := by omega_using [hs.1, hs.2.1, last]
    refine ⟨?_, n - 1, by omega_using [hs.1], ?_⟩
    · simpa only [idx, ne_eq, not_false_eq_true, decide_true] using h.1
    · refine ⟨by omega_using [hs.1, last], by omega_using [hs.2.1], ?_⟩
      have eq : 16 - n + 1 = 16 - (n - 1) := by omega_using [hs.1, hs.2.1]
      rw [← eq]
      exact h.2

theorem loop_ok (key : BitVec 64) (base : Addr) (s : State)
    (hw : ∀ j < 16, InRegions s.wr (base + BitVec.ofNat 64 (8 * j)) 8)
    (hc : s.gpr .a3 = (keyInitial key).1.setWidth 64)
    (hd : s.gpr .a4 = (keyInitial key).2.1.setWidth 64)
    (hcount : s.gpr .a6 = 0) (hptr : s.gpr .a5 = base) :
    WP isa (.loop (.seq Impl.TripleDes.RISCV64.Key.rotation
      (.block Impl.TripleDes.RISCV64.Key.storeRound)) (.nonzero .t0)) s (LoopState key base s 16) := by
  apply WP.loop (M := isa) (body := .seq Impl.TripleDes.RISCV64.Key.rotation
      (.block Impl.TripleDes.RISCV64.Key.storeRound)) (c := .nonzero .t0)
    (Q := LoopState key base s 16) (LoopInv key base s) (loopStep key base s hw) 16 s
  refine ⟨by decide, by decide, hc, hd, hcount, ?_, ?_, rfl, rfl, rfl, fun _ _ => rfl,
    Frame.refl _ _⟩
  · exact hptr.trans (BitVec.add_zero base).symm
  · intro i hi
    omega

structure ComponentPost (keys : Spec.TripleDes.DesSchedule) (base : Addr) (s s' : State) :
    Prop where
  keys : ∀ i < 16, s'.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64 = (keys.getD i 0).setWidth 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  reg : ∀ r ∈ keyKept, s'.gpr r = s.gpr r
  frame : Frame [⟨base, 128⟩] s.mem s'.mem

theorem component_ok (s : State) (offset component : Nat) (hc : component < 3)
    (ho : offset ≤ 16)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 offset) 8)
    (hw : ∀ j < 16, InRegions s.wr
      (s.gpr .a2 + BitVec.ofNat 64 (128 * component) + BitVec.ofNat 64 (8 * j)) 8) :
    WP isa (Impl.TripleDes.RISCV64.Key.component offset component) s
      (ComponentPost (Spec.TripleDes.expandDesKey (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (s.gpr .a0 + BitVec.ofNat 64 offset))))
        (s.gpr .a2 + BitVec.ofNat 64 (128 * component)) s) := by
  rw [Impl.TripleDes.RISCV64.Key.component]
  apply WP.seq
  apply WP.mono (load_ok s offset component hc ho hr)
  intro s₁ h₁
  have writes : ∀ j < 16, InRegions s₁.wr
      (s.gpr .a2 + BitVec.ofNat 64 (128 * component) + BitVec.ofNat 64 (8 * j)) 8 := by
    rw [h₁.wr]; exact hw
  apply WP.mono (loop_ok _ _ s₁ writes h₁.c h₁.d h₁.counter h₁.ptr)
  intro s₂ h₂
  refine ⟨?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp,
    fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), ?_⟩
  · intro i hi
    rw [VG.Proof.TripleDes.expandDesKey_prefix, VG.Proof.TripleDes.vector_getD _ i hi 0]
    exact h₂.keys i hi hi
  · rw [← h₁.mem]
    exact h₂.frame

end VG.Proof.TripleDes.RISCV64.Key

end

end


/-!
# The three components

`body_ok`: key expansion writes the three components' schedules, the third
a copy of the first for a 16-byte key (`Components … 3`), and
`Components.schedule`: they are the expanded key.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Key

open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Proof.TripleDes (componentKeys componentOffset)

abbrev keyR (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
abbrev outputR (s : State) : Region := ⟨s.gpr .a2, 384⟩

def slot (base : Addr) (c j : Nat) : Addr := base + BitVec.ofNat 64 (128 * c + 8 * j)

structure Components (origin s : State) (done : Nat) : Prop where
  keys : ∀ c < done, ∀ j < 16, s.mem.readW (slot (origin.gpr .a2) c j) 64 =
    ((componentKeys origin.mem (origin.gpr .a0) (origin.gpr .a1).toNat c).getD j 0).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  reg : ∀ r ∈ keyKept, s.gpr r = origin.gpr r
  frame : Frame [outputR origin] origin.mem s.mem

structure Permissions (s : State) : Prop where
  reads : ∀ offset, offset + 8 ≤ (s.gpr .a1).toNat →
    InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 offset) 8
  writes : ∀ offset, offset + 8 ≤ 384 → InRegions s.wr (s.gpr .a2 + BitVec.ofNat 64 offset) 8
  keyOutput : (keyR s).Disjoint (outputR s)
  valid : Spec.TripleDes.validKey (s.gpr .a1).toNat

theorem componentStep_ok (origin s : State) (c : Nat) (hc : c < 3)
    (hp : Permissions origin) (hs : Components origin s c)
    (hoff : componentOffset (origin.gpr .a1).toNat c = 8 * c) :
    WP isa (Impl.TripleDes.RISCV64.Key.component (8 * c) c) s
      (Components origin · (c + 1)) := by
  have offsetBound := VG.Proof.TripleDes.componentOffset_bound _ c hp.valid hc
  rw [hoff] at offsetBound
  have read : InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 (8 * c)) 8 := by
    rw [hs.rd, hs.wr, hs.reg .a0 (by decide)]
    exact hp.reads _ offsetBound
  have write : ∀ j < 16, InRegions s.wr
      (s.gpr .a2 + BitVec.ofNat 64 (128 * c) + BitVec.ofNat 64 (8 * j)) 8 := by
    intro j hj
    rw [hs.wr, hs.reg .a2 (by decide), Offset.add_ofNat_add_ofNat]
    exact hp.writes _ (by omega_using [hc, hj])
  apply WP.mono (component_ok s (8 * c) c hc (by omega_using [hc]) read write)
  intro t ht
  have frame : Frame [⟨origin.gpr .a2 + BitVec.ofNat 64 (128 * c), 128⟩] s.mem t.mem := by
    have hf := ht.frame
    rw [hs.reg .a2 (by decide)] at hf
    exact hf
  have key : Spec.TripleDes.blockAt s.mem (s.gpr .a0 + BitVec.ofNat 64 (8 * c)) =
      Spec.TripleDes.blockAt origin.mem (origin.gpr .a0 + BitVec.ofNat 64 (8 * c)) := by
    rw [hs.reg .a0 (by decide)]
    apply VG.Proof.TripleDes.blockAt_eq_of_frame _ hs.frame
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hp.keyOutput.sub_left (Offset.sub_base _ offsetBound)
  refine ⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr, ht.sp.trans hs.sp,
    fun r hr => (ht.reg r hr).trans (hs.reg r hr), hs.frame.trans (frame.sub ?_)⟩
  · intro k hk j hj
    by_cases he : k = c
    · subst k
      have h := ht.keys j hj
      rw [key, hs.reg .a2 (by decide), Offset.add_ofNat_add_ofNat] at h
      unfold componentKeys
      rw [hoff]
      exact h
    · have before : k < c := by omega_using [hk, he]
      have sep : (Region.mk (slot (origin.gpr .a2) k j) 8).Disjoint
          ⟨origin.gpr .a2 + BitVec.ofNat 64 (128 * c), 128⟩ :=
        Offset.disjoint _ (by omega_using [before, hj])
          (by omega_using [hk, hc, hj]) (by omega_using [hc])
      have hmem := frame.readW (a := slot (origin.gpr .a2) k j) (w := 64)
        (r := ⟨slot (origin.gpr .a2) k j, 8⟩)
        (Region.contains_self _ _) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sep)
        (by decide)
      exact hmem.trans (hs.keys k before j hj)
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨outputR origin, by simp, Offset.sub_base _ (by omega_using [hc])⟩

theorem WP.and_sp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.sp he⟩

theorem copyThird_ok (origin s : State) (hp : Permissions origin)
    (hs : Components origin s 2) (hn : (origin.gpr .a1).toNat = 16) :
    WP isa Impl.TripleDes.RISCV64.Key.copyThird s (Components origin · 3) := by
  have hB := hs.reg .a2 (by decide)
  rw [Impl.TripleDes.RISCV64.Key.copyThird]
  apply WP.seq
  refine wp_mv fun u₁ h₁ => wp_addi (by decide) fun u₂ h₂ => wp_li (imm := 128) (by decide)
    fun u₃ h₃ => WP.block_nil ?_
  have src₃ : u₃.gpr .t0 = origin.gpr .a2 := by
    rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, hB]
  have dst₃ : u₃.gpr .t1 = origin.gpr .a2 + BitVec.ofNat 64 256 := by
    rw [h₃.other _ (by decide), h₂.gpr, h₁.other _ (by decide), hB]
  have rd₃ : u₃.rd = origin.rd := by rw [h₃.rd, h₂.rd, h₁.rd, hs.rd]
  have wr₃ : u₃.wr = origin.wr := by rw [h₃.wr, h₂.wr, h₁.wr, hs.wr]
  have mem₃ : u₃.mem = s.mem := by rw [h₃.mem, h₂.mem, h₁.mem]
  refine WP.mono (WP.and_sp (copyLoop_ok (tmp := .t3) (src := .t0) (dst := .t1) (cnt := .t2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) u₃ (N := 128)
    (by decide) (by decide) h₃.gpr (fun i hi => by
      rw [rd₃, wr₃, src₃]
      obtain ⟨r, hr, hc⟩ := CallLay.inRegions_sub (hp.writes (8 * (i / 8)) (by omega_using [hi]))
        (off := i % 8) (l := 1) (by omega_using []) (by decide)
      refine ⟨r, List.mem_append_right _ hr, ?_⟩
      rwa [Offset.add_ofNat_add_ofNat, show 8 * (i / 8) + i % 8 = i by omega_using []] at hc) (fun i hi => by
      rw [wr₃, dst₃, Offset.add_ofNat_add_ofNat]
      have h := CallLay.inRegions_sub (hp.writes (8 * ((256 + i) / 8)) (by omega_using [hi]))
        (off := (256 + i) % 8) (l := 1) (by omega_using []) (by decide)
      rwa [Offset.add_ofNat_add_ofNat, show 8 * ((256 + i) / 8) + (256 + i) % 8 = 256 + i by omega_using []]
        at h) (by
      rw [dst₃, src₃]
      exact fun x h₁ h₂ => Offset.sep (origin.gpr .a2) (d := 256) (n := 128) (e := 0) (k := 128)
        (by decide) (by decide) (by decide) x (by simpa using h₁) (by simpa using h₂))))
    fun t ⟨⟨hcopy, hframe, hkeep⟩, hsp⟩ => ?_
  rw [mem₃, dst₃, src₃] at hcopy
  rw [mem₃, dst₃] at hframe
  refine ⟨?_, hkeep.2.1.trans rd₃, hkeep.2.2.trans wr₃,
    hsp.trans (by rw [h₃.sp, h₂.sp, h₁.sp, hs.sp]), fun r hr => ?_,
    hs.frame.trans (hframe.sub ?_)⟩
  · intro c hc j hj
    by_cases he : c = 2
    · subst c
      have hRepeat : componentKeys origin.mem (origin.gpr .a0) (origin.gpr .a1).toNat 2 =
          componentKeys origin.mem (origin.gpr .a0) (origin.gpr .a1).toNat 0 := by
        rw [hn]; rfl
      rw [hRepeat]
      have first := hs.keys 0 (by decide) j hj
      refine Eq.trans (Bytes.dword_ext fun i hi => ?_) first
      rw [Bytes.readW64_byte _ _ hi, Bytes.readW64_byte _ _ hi]
      have h := hcopy (8 * j + i) (by omega_using [hj, hi])
      rw [Offset.add_ofNat_add_ofNat] at h
      simp only [slot, Offset.add_ofNat_add_ofNat]
      rw [show 128 * 2 + 8 * j + i = 256 + (8 * j + i) by omega_using [],
        show 128 * 0 + 8 * j + i = 8 * j + i by omega_using [], h]
    · have before : c < 2 := by omega_using [hc, he]
      have sep : (Region.mk (slot (origin.gpr .a2) c j) 8).Disjoint
          ⟨origin.gpr .a2 + BitVec.ofNat 64 256, 128⟩ :=
        Offset.disjoint _ (by omega_using [before, hj])
          (by omega_using [before, hj]) (by decide)
      have hmem := hframe.readW (a := slot (origin.gpr .a2) c j) (w := 64)
        (r := ⟨slot (origin.gpr .a2) c j, 8⟩)
        (Region.contains_self _ _) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sep)
        (by decide)
      exact hmem.trans (hs.keys c before j hj)
  · rw [hkeep.gpr (by revert hr; cases r <;> decide)]
    have h' : r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 := by revert hr; cases r <;> decide
    rw [h₃.other _ h'.2.2, h₂.other _ h'.2.1, h₁.other _ h'.1, hs.reg r hr]
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨outputR origin, by simp, Offset.sub_base _ (by decide)⟩

theorem Components.keep {origin s t : State} {n : Nat} (hs : Components origin s n)
    (ht : Only [.t0] s t) : Components origin t n :=
  ⟨fun c hc j hj => by rw [ht.mem]; exact hs.keys c hc j hj,
    ht.rd.trans hs.rd, ht.wr.trans hs.wr, ht.sp.trans hs.sp,
    fun r hr => (ht.reg r (by revert hr; cases r <;> decide)).trans (hs.reg r hr),
    by rw [ht.mem]; exact hs.frame⟩

theorem beq16_toNat (x : BitVec 64) : (x - BitVec.ofNat 64 16 == 0) = decide (x.toNat = 16) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor <;> intro h <;> bv_omega

theorem body_ok (origin s : State) (hp : Permissions origin) (hs : Components origin s 0) :
    WP isa Impl.TripleDes.RISCV64.Key.expandKey s (Components origin · 3) := by
  rw [Impl.TripleDes.RISCV64.Key.expandKey]
  apply WP.seq
  apply WP.mono (componentStep_ok origin s 0 (by decide) hp hs (by rfl))
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (componentStep_ok origin s₁ 1 (by decide) hp hs₁ (by rfl))
  intro s₂ hs₂
  apply WP.seq
  refine wp_subi (by decide) fun s₃ h₃ => WP.block_nil ?_
  have hs₃ := hs₂.keep ⟨fun r hr => h₃.other r (by simpa using hr), h₃.mem, h₃.rd, h₃.wr, h₃.sp⟩
  have flag : isa.eval (.zero .t0) s₃ = some (decide ((origin.gpr .a1).toNat = 16)) := by
    rw [eval_zero, h₃.gpr, hs₂.reg .a1 (by decide), beq16_toNat]
  by_cases h16 : (origin.gpr .a1).toNat = 16
  · apply WP.ite true (by simpa only [h16, decide_true] using flag)
    · intro _; exact copyThird_ok origin s₃ hp hs₃ h16
    · simp
  · apply WP.ite false (by simpa only [h16, decide_false] using flag)
    · simp
    · intro _
      exact componentStep_ok origin s₃ 2 (by decide) hp hs₃
        (by simp only [VG.Proof.TripleDes.componentOffset, h16, and_false, ite_false])

def componentIndex (i : Nat) : Nat := if i < 16 then 0 else if i < 32 then 1 else 2

theorem index_partition : ∀ i < 48, componentIndex i < 3 ∧ i % 16 < 16 ∧
    8 * i = 128 * componentIndex i + 8 * (i % 16) := by decide

theorem Components.schedule {origin s : State} (h : Components origin s 3) :
    Spec.TripleDes.scheduleAt s.mem (origin.gpr .a2) =
      VG.Proof.TripleDes.expandedMemory origin.mem (origin.gpr .a0) (origin.gpr .a1).toNat := by
  apply Vector.ext
  intro i hi
  have fact := index_partition i hi
  have keys := h.keys (componentIndex i) fact.1 (i % 16) fact.2.1
  rw [slot, ← fact.2.2] at keys
  rw [VG.Proof.TripleDes.scheduleAt_readW s.mem (origin.gpr .a2) i hi]
  simp only [VG.Proof.TripleDes.expandedMemory, Vector.getElem_ofFn]
  by_cases h16 : i < 16
  · simpa only [componentIndex, h16, ite_true] using keys
  · by_cases h32 : i < 32
    · simpa only [componentIndex, h16, h32, ite_false, ite_true] using keys
    · simpa only [componentIndex, h16, h32, ite_false] using keys

end VG.Proof.TripleDes.RISCV64.Key
