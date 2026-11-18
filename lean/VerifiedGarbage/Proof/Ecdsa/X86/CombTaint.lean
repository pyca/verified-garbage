module

public import VerifiedGarbage.Proof.Ecdsa.X86.Stages
public import VerifiedGarbage.Proof.Ecdsa.X86.CombLays
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Ecdsa.X86.Main
import VerifiedGarbage.Proof.Framework.X86.RelCT

/-!
# ECDSA on x86 (32-bit): the taints of the stages around a fixed-base comb

A function that multiplies `G` by a comb is constant time stage by stage
(`RelCT`): the comb reads its tables' address from the working space, where
no analysis of the whole function still knows it to be public after the
stores at computed addresses of the stages before, so each stage is analysed
from a taint that the functional invariant of the stage before gives again.
Here are those taints, for any curve: the comb's (`combτAt`: the working space
and its word holding the tables' address), the stages' (`argτ`,
`scratchArgτ`: the arguments on the stack), what the comb's constant time is
for the stages (`GMulRel`), and what the stages' invariants give of them.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

def combRegion (scratchSecond : Bool) : Nat := if scratchSecond then 1 else 0

def combτAt (scratchSecond : Bool) : VG.X86.Taint.T :=
  { regs := .ofList [.esi, .edi, .esp], flags := false,
    lens := if scratchSecond then [0, 8192] else [8192],
    bases := [(.edi, combRegion scratchSecond, 0)],
    slots := [(combRegion scratchSecond, 60, 4)], room := 20 }

abbrev combτ := combτAt true

variable {scratchSecond : Bool}

/-- The loop's taint well-formedness only needs the scratch base and the
unchanged region metadata. -/
theorem combWf_keep {s t : State} (h : VG.X86.Taint.Wf (combτAt scratchSecond) s)
    (hw : t.wr = s.wr) (he : t.gpr .edi = s.gpr .edi) (hsp : t.gpr .esp = s.gpr .esp) :
    VG.X86.Taint.Wf (combτAt scratchSecond) t := by
  have hroom : 0 < (combτAt scratchSecond).room → (combτAt scratchSecond).room ≤ (t.gpr .esp).toNat ∧
      ∀ r ∈ t.wr, Region.Disjoint ⟨(t.gpr .esp).setWidth 64 - BitVec.ofNat 64 (combτAt scratchSecond).room,
        (combτAt scratchSecond).room⟩ r := fun hpos => by
    have := h.room hpos
    simp only [combτAt, VG.X86.Taint.depth, VG.X86.Taint.nframes, List.drop_zero, VG.X86.Taint.argByte,
      Nat.add_zero, BitVec.add_zero] at this ⊢
    rw [hw, hsp]; exact this
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨?_, ?_, ?_, ?_, ?_⟩ hroom
  · intro hn
    rw [hw]; exact h.lens hn
  · intro p hp
    have : p = (.edi, combRegion scratchSecond, 0) := List.mem_singleton.mp hp
    subst p
    simp only [VG.X86.Taint.region, hw, he]
    exact h.bases _ (List.mem_singleton_self _)
  · intro p hp; cases hp
  · intro hp; cases hp
  · intro p hp; cases hp

/-- Re-establish the public table word from the functional invariant. -/
theorem combAgree {s t : State} (hs : VG.X86.Taint.Wf (combτAt scratchSecond) s) (ht : VG.X86.Taint.Wf (combτAt scratchSecond) t)
    (hw : s.wr = t.wr) (hi : s.gpr .esi = t.gpr .esi) (hd : s.gpr .edi = t.gpr .edi)
    (hsp : s.gpr .esp = t.gpr .esp)
    (hp : s.mem.readW (VG.X86.Taint.byteAddr s (combRegion scratchSecond) 60) 32 =
      t.mem.readW (VG.X86.Taint.byteAddr t (combRegion scratchSecond) 60) 32) : VG.X86.Taint.Agree (combτAt scratchSecond) s t := by
  refine ⟨⟨?_, fun h => by cases h⟩, fun _ => hw, hs, ht, ?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [combτAt, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hi
    · exact hd
    · exact hsp
  · refine VG.X86.Taint.slotsOk_of_list rfl fun p hp => ?_
    have : p = (combRegion scratchSecond, 60, 4) := List.mem_singleton.mp hp
    subst p; cases scratchSecond <;> decide
  · intro i k hk
    rw [show (combτAt scratchSecond).slots = VG.Slots.ofList [(combRegion scratchSecond, 60, 4)] from rfl,
      VG.Slots.has_ofList] at hk
    obtain ⟨p, hmem, rfl, hlo, hhi⟩ := hk
    have : p = (combRegion scratchSecond, 60, 4) := List.mem_singleton.mp hmem
    subst p
    have hk : k < 64 ∧ 60 ≤ k := by exact ⟨hhi, hlo⟩
    have e : ∀ u : State, VG.X86.Taint.byteAddr u (combRegion scratchSecond) k =
        VG.X86.Taint.byteAddr u (combRegion scratchSecond) 60 + BitVec.ofNat 64 (k - 60) := by
      intro u
      unfold VG.X86.Taint.byteAddr
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_of_le hk.2]
    rw [e s, e t, Mem.readW_byte s.mem _ (by omega_arith), Mem.readW_byte t.mem _ (by omega_arith), hp]
  · intro h; cases h
  · intro k hlo hhi; have : k < 0 := hhi; omega_arith


def combStartτAt (scratchSecond : Bool) : VG.X86.Taint.T :=
  { combτAt scratchSecond with regs := .ofList [.edi, .esp] }

/-- Re-establish the public table word from the functional invariant. -/
theorem combStartAgree {s t : State} (hs : VG.X86.Taint.Wf (combτAt scratchSecond) s) (ht : VG.X86.Taint.Wf (combτAt scratchSecond) t)
    (hw : s.wr = t.wr) (hd : s.gpr .edi = t.gpr .edi) (hsp : s.gpr .esp = t.gpr .esp)
    (hp : s.mem.readW (VG.X86.Taint.byteAddr s (combRegion scratchSecond) 60) 32 =
      t.mem.readW (VG.X86.Taint.byteAddr t (combRegion scratchSecond) 60) 32) : VG.X86.Taint.Agree (combStartτAt scratchSecond) s t := by
  refine ⟨⟨?_, fun h => by cases h⟩, fun _ => hw, ⟨hs.lens, hs.bases, hs.wbases, hs.args, hs.argBases, hs.stk, hs.frames, hs.room⟩,
    ⟨ht.lens, ht.bases, ht.wbases, ht.args, ht.argBases, ht.stk, ht.frames, ht.room⟩, ?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [combStartτAt, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd
    · exact hsp
  · refine VG.X86.Taint.slotsOk_of_list rfl fun p hp => ?_
    have : p = (combRegion scratchSecond, 60, 4) := List.mem_singleton.mp hp
    subst p; cases scratchSecond <;> decide
  · intro i k hk
    rw [show (combStartτAt scratchSecond).slots = VG.Slots.ofList [(combRegion scratchSecond, 60, 4)] from rfl,
      VG.Slots.has_ofList] at hk
    obtain ⟨p, hmem, rfl, hlo, hhi⟩ := hk
    have : p = (combRegion scratchSecond, 60, 4) := List.mem_singleton.mp hmem
    subst p
    have hk : k < 64 ∧ 60 ≤ k := by exact ⟨hhi, hlo⟩
    have e : ∀ u : State, VG.X86.Taint.byteAddr u (combRegion scratchSecond) k =
        VG.X86.Taint.byteAddr u (combRegion scratchSecond) 60 + BitVec.ofNat 64 (k - 60) := by
      intro u
      unfold VG.X86.Taint.byteAddr
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_of_le hk.2]
    rw [e s, e t, Mem.readW_byte s.mem _ (by omega_arith), Mem.readW_byte t.mem _ (by omega_arith), hp]
  · intro h; cases h
  · intro k hlo hhi; have : k < 0 := hhi; omega_arith


/-- Widening 32-bit words is injective. -/
theorem widen32_inj {x y : BitVec 32} (h : x.setWidth 64 = y.setWidth 64) : x = y := by
  have h' := congrArg (BitVec.setWidth 32) h
  simpa only [BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_eq] using h'

/-- That `[k]G` by the comb `d` of `c` leaks the same in two runs whose working space, tables
and stack are where the other's are, whatever their scalars: what the stages of a function
that multiplies `G` take of the comb's constant time (`gMul_rel` for the comb with Booth's
digits, `gMulRcb_rel` for the comb by complete additions). -/
def GMulRel (c : Cfg) (d : CombData) (scratchSecond : Bool) : Prop :=
  ∀ {base : Addr} {g₁ g₂ : Reg → BitVec 32} {s₀ t₀ : State} {k₁ k₂ : Nat},
    Scr s₀ base size → Scr t₀ base size →
    Fixed c base g₁ s₀.mem → Fixed c base g₂ t₀.mem →
    k₁ < 2 ^ (64 * c.n) → k₂ < 2 ^ (64 * c.n) →
    (∀ t < 64 * c.n, s₀.mem (off base (bitsAt c.n 0 + t)) = if k₁.testBit t then 1 else 0) →
    (∀ t < 64 * c.n, t₀.mem (off base (bitsAt c.n 0 + t)) = if k₂.testBit t then 1 else 0) →
    TblMem s₀ ((g₁ .eax).setWidth 64) (c.combWords d) →
    TblMem t₀ ((g₂ .eax).setWidth 64) (c.combWords d) →
    (∀ i < (c.combWords d).length, ∀ b < 8,
      size ≤ ofs base ((g₁ .eax).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) →
    (∀ r ∈ s₀.wr ++ [below (s₀.gpr .esp) 20],
      Region.Disjoint ⟨(g₁ .eax).setWidth 64, 8 * (c.combWords d).length⟩ r) →
    (∀ r ∈ t₀.wr ++ [below (t₀.gpr .esp) 20],
      Region.Disjoint ⟨(g₂ .eax).setWidth 64, 8 * (c.combWords d).length⟩ r) →
    20 ≤ (s₀.gpr .esp).toNat → 20 ≤ (t₀.gpr .esp).toNat → g₁ .eax = g₂ .eax →
    VG.X86.Taint.Wf (combτAt scratchSecond) s₀ → VG.X86.Taint.Wf (combτAt scratchSecond) t₀ →
    s₀.wr = t₀.wr → s₀.gpr .esp = t₀.gpr .esp →
    RelCT isa (fun s t => s = s₀ ∧ t = t₀) c.gMul (fun _ _ => True)

/-- The scalar stages use public scratch and argument addresses. -/
def argτ (rs : List Reg) (n : Nat := 5) (room : Nat := 20) : VG.X86.Taint.T :=
  { regs := .ofList rs, flags := false, argLen := 4 + 4 * n, room := room }

/-- Public scratch addresses let fixed loop counters survive memory stores. -/
def scratchArgτ (n : Nat) (second : Bool := true) (room : Nat := 20) : VG.X86.Taint.T :=
  { argτ [.esp, .edi] n room with lens := (combτAt second).lens, bases := (combτAt second).bases }

/-- Writes within scratch leave all cdecl argument words unchanged. -/
theorem Keep.arg {c : Cfg} {s₀ s : State} {extra : List Region}
    (hp : Pre c s₀ extra) (h : Keep c s₀ (ptr s₀ 4) s) {j : Nat} (hj : j < 5) :
    arg s j = arg s₀ j := by
  have he : argAddr s j = argAddr s₀ j := by simp only [argAddr, h.esp]
  change s.mem.readW (argAddr s j) 32 = _
  rw [he]
  exact hp.frame_readW h.whole (hp.args_out.sub_left (arg_sub hp.sp_fit hj))
    (hp.args_sc.sub_left (arg_sub hp.sp_fit hj))
    ((below_disjoint_args hp.sp_lo (k := 20) (by have := hp.sp_fit; omega_using [this]) (by decide)).symm.sub_left
      (arg_sub hp.sp_fit hj))

/-- The public argument area is disjoint from every writable buffer. -/
theorem argWf {c : Cfg} {s₀ s : State} {extra : List Region} (rs : List Reg)
    (hp : Pre c s₀ extra) (he : s.gpr .esp = s₀.gpr .esp) (hw : s.wr = s₀.wr) :
    VG.X86.Taint.Wf (argτ rs 5 c.stk) s := by
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨?_, ?_, ?_, ?_, ?_⟩ fun _ => ⟨by rw [he]; exact hp.sp_lo, ?_⟩
  rotate_right
  · rw [he, hw, hp.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.stk_out
    · exact hp.stk_sc
  · intro h; cases h rfl
  · intro p h; cases h
  · intro p h; cases h
  · intro _
    rw [he, hw, hp.wr]
    refine ⟨hp.sp_fit, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by have := hp.sp_fit; omega_using [this]) hp.ret_out hp.args_out
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by have := hp.sp_fit; omega_using [this]) hp.ret_sc hp.args_sc
  · intro p h; cases h

/-- Equal pointers and stack arguments establish a taint agreement. -/
theorem argAgree {rs : List Reg} {n room : Nat} {s t : State}
    (ws : VG.X86.Taint.Wf (argτ rs n room) s) (wt : VG.X86.Taint.Wf (argτ rs n room) t)
    (hr : ∀ r ∈ rs, s.gpr r = t.gpr r) (he : s.gpr .esp = t.gpr .esp)
    (ha : ∀ j < n, arg s j = arg t j) : VG.X86.Taint.Agree (argτ rs n room) s t := by
  refine ⟨⟨fun r h => hr r (by simpa only [argτ, RegSet.mem_ofList] using h),
    fun h => by cases h⟩, fun h => False.elim (h rfl), ws, wt,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => he, ?_⟩
  intro k hlo hhi
  have hs := (ws.args (show 0 < 4 + 4 * n by omega_using [])).1
  have ht := (wt.args (show 0 < 4 + 4 * n by omega_using [])).1
  change 4 ≤ k at hlo
  change k < 4 + 4 * n at hhi
  rw [show VG.X86.Taint.depth (argτ rs n room).stk = 0 from rfl, Nat.zero_add]
  change (s.gpr .esp).toNat + 0 + (4 + 4 * n) ≤ 2 ^ 32 at hs
  change (t.gpr .esp).toNat + 0 + (4 + 4 * n) ≤ 2 ^ 32 at ht
  rw [VG.X86.Taint.argByte_eq (by omega_using [hs]) hlo hhi,
    VG.X86.Taint.argByte_eq (by omega_using [ht]) hlo hhi,
    Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)),
    Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
  exact congrArg _ (ha ((k - 4) / 4) (by omega_using [hlo, hhi]))

theorem scratchArgWf {n room : Nat} {second : Bool} {s : State}
    (a : VG.X86.Taint.Wf (argτ [.esp, .edi] n room) s) (b : VG.X86.Taint.Wf (combτAt second) s) :
    VG.X86.Taint.Wf (scratchArgτ n second room) s :=
  ⟨b.lens, b.bases, fun _ h => (List.not_mem_nil h).elim, a.args, a.argBases, a.stk, a.frames, a.room⟩

theorem scratchArgAgree {n room : Nat} {second : Bool} {s t : State}
    (a : VG.X86.Taint.Agree (argτ [.esp, .edi] n room) s t)
    (ws : VG.X86.Taint.Wf (combτAt second) s) (wt : VG.X86.Taint.Wf (combτAt second) t)
    (hw : s.wr = t.wr) : VG.X86.Taint.Agree (scratchArgτ n second room) s t :=
  ⟨a.rf, fun _ => hw, scratchArgWf a.wf₁ ws, scratchArgWf a.wf₂ wt, (VG.X86.Taint.slotsOk_empty), a.slots, a.sp, a.argMem⟩

/-- The functional stage invariant restores public cdecl arguments. -/
theorem keepArgAgree {c : Cfg} {s₀ t₀ s t : State} {extra₁ extra₂ : List Region}
    (hp : Pre c s₀ extra₁) (hq : Pre c t₀ extra₂)
    (ks : Keep c s₀ (ptr s₀ 4) s) (kt : Keep c t₀ (ptr t₀ 4) t)
    (he : s₀.gpr .esp = t₀.gpr .esp) (ha : ∀ j < 5, arg s₀ j = arg t₀ j) :
    VG.X86.Taint.Agree (argτ [.esp, .edi] 5 c.stk) s t := by
  have esp : s.gpr .esp = t.gpr .esp := ks.esp.trans (he.trans kt.esp.symm)
  have edi : s.gpr .edi = t.gpr .edi := widen32_inj (ks.scr.edi.trans
    ((congrArg (BitVec.setWidth 64) (ha 4 (by decide))).trans kt.scr.edi.symm))
  refine argAgree (argWf _ hp ks.esp ks.wr) (argWf _ hq kt.esp kt.wr) ?_ esp ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact esp
    · exact edi
  · intro j hj
    rw [ks.arg hp hj, kt.arg hq hj, ha j hj]

/-- The 20 bytes of stack the comb's calls use are among those the function may use. -/
theorem stk20_sub {sp : BitVec 32} {z : Nat} (hz : 20 ≤ z) (hsp : z ≤ sp.toNat) :
    Region.Sub ⟨sp.setWidth 64 - BitVec.ofNat 64 20, 20⟩ ⟨sp.setWidth 64 - BitVec.ofNat 64 z, z⟩ := by
  have h := below_le_sub (sp := sp) hz hsp
  unfold below at h
  rwa [VG.X86.Taint.sub_setWidth (Nat.le_trans hz hsp), VG.X86.Taint.sub_setWidth hsp] at h

/-- The static-table scan's scratch region is the second writable argument. -/
theorem keepCombWf {c : Cfg} {s₀ s : State} {extra : List Region} (hp : Pre c s₀ extra)
    (ks : Keep c s₀ (ptr s₀ 4) s) : VG.X86.Taint.Wf combτ s := by
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨?_, ?_, ?_, ?_, ?_⟩ fun _ => ⟨?_, ?_⟩
  rotate_right 2
  · rw [ks.esp]; exact Nat.le_trans (Cfg.stk_ge c) hp.sp_lo
  · rw [ks.esp, ks.wr, hp.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.stk_out.sub_left (stk20_sub (Cfg.stk_ge c) hp.sp_lo)
    · exact hp.stk_sc.sub_left (stk20_sub (Cfg.stk_ge c) hp.sp_lo)
  · intro _
    rw [ks.wr, hp.wr]
    refine ⟨by simp [combτ, combτAt, outR, scR, size], ?_, ?_⟩
    · simpa using hp.out_sc
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · simp only [ptr, BitVec.toNat_setWidth]; omega_using [hp.out_fit]
      · simp only [ptr, BitVec.toNat_setWidth]; omega_using [hp.sc_fit]
  · intro p h
    rw [List.mem_singleton.mp h]
    change addr (s.gpr .edi) 0 = (VG.X86.Taint.region s 1).base
    simp only [VG.X86.Taint.region, ks.wr, hp.wr, List.getD_cons_succ, List.getD_cons_zero,
      addr, BitVec.add_zero]
    exact ks.scr.edi
  · intro p h; cases h
  · intro h; cases h
  · intro p h; cases h

theorem keepScratchAgree {c : Cfg} {s₀ t₀ s t : State} {extra₁ extra₂ : List Region}
    (hp : Pre c s₀ extra₁) (hq : Pre c t₀ extra₂)
    (ks : Keep c s₀ (ptr s₀ 4) s) (kt : Keep c t₀ (ptr t₀ 4) t)
    (he : s₀.gpr .esp = t₀.gpr .esp) (ha : ∀ j < 5, arg s₀ j = arg t₀ j) :
    VG.X86.Taint.Agree (scratchArgτ 5 true c.stk) s t := by
  refine scratchArgAgree (keepArgAgree hp hq ks kt he ha) (keepCombWf hp ks) (keepCombWf hq kt) ?_
  rw [ks.wr, kt.wr, hp.wr, hq.wr]
  simp only [outR, scR, ptr, ha 4 (by decide), ha 0 (by decide)]

end VG.Proof.Ecdsa.X86
