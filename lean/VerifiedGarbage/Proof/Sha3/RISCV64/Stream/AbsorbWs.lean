module

-- separate module: as `Absorb`, `Pad` and `Squeeze`, whose proofs cost more than their imports,
-- apart from `Verified`, which composes them
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Sha3.Lanes
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp
public import VerifiedGarbage.Proof.Framework.RISCV64.Words64
public import VerifiedGarbage.Proof.Sha3.RISCV64.Contract
public import VerifiedGarbage.Proof.Sha3.Stream
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Spec.Sha3.Contract
import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Impl.Sha3.RISCV64.Stream
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.Sha3.RISCV64.Permute

/-! ### `Sha3.RISCV64.Stream.Absorb`, which this module and modules that import it used -/

section

/-! ### `Sha3.RISCV64.Stream.Common`, which this module and modules that import it used -/

section

/-! ### `Sha3.RISCV64.Call`, which this module and modules that import it used -/

section

/-!
# SHA-3 on RISC-V: calling the permutation

The streaming functions call `vg_keccak_f1600` (which allocates a frame of
its own, `WP.callAny`) on the state at `s2`, with a frame of 512 bytes
allocated around the call as its scratch space (`permuteAt_ok`).
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64

open VG VG.RISCV64 VG.RISCV64.Wp VG.Impl.Sha3.RISCV64.Stream
open VG.Spec.Sha3 (stateAt keccakF)

theorem permute_sdepth : sdepth Impl.Sha3.RISCV64.permute = 608 := by decide +kernel

/-- Calling `vg_keccak_f1600` on the state at `a0`, with scratch space at
`a1`, the stack pointer: the callee-saved registers are kept, and memory
changes only in the state, the scratch space and the 608 bytes below. -/
theorem call_ok {s : State} {st : Addr} (h0 : s.gpr .a0 = st) (h1 : s.gpr .a1 = s.sp)
    (hal : s.sp.toNat % 16 = 0) (hsp : 608 ≤ s.sp.toNat)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨s.sp, 512⟩) (d₂ : Region.Disjoint ⟨s.sp - 608, 608⟩ ⟨st, 200⟩)
    (hw : Covers [⟨st, 200⟩, ⟨s.sp, 512⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨s.sp, 512⟩, ⟨s.sp - 608, 608⟩] s.mem s'.mem →
      stateAt s'.mem st = keccakF (stateAt s.mem st) → Q s') :
    WP isa (.call "vg_keccak_f1600" Impl.Sha3.RISCV64.permute) s Q := by
  have c0 : s.callEntry.gpr .a0 = st := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .a1 = s.sp := (State.callEntry_gpr _ (by decide)).trans h1
  refine WP.callAny (k := Proof.Sha3.permuteRISCV64) permute_correct
    (rd := []) (wr := [⟨st, 200⟩, ⟨s.sp, 512⟩]) ?_ ?_ hw ?_ (by rw [permute_sdepth]; decide)
  · simp only [Proof.Sha3.permuteRISCV64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, c0, c1]
    exact ⟨trivial, trivial, d₁, hal, hsp, d₂,
      Offset.base_disjoint_below s.sp (n := 608) (k := 512) (by omega_using []) |>.symm⟩
  · intro a n h
    obtain ⟨r, hr, hc⟩ := hw a n (by simpa using h)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · intro s' hrd hwr hsp' hf hcs hpost
    simp only [Proof.Sha3.permuteRISCV64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0] at hpost
    rw [permute_sdepth] at hf
    exact hQ s' hrd hwr hsp' hcs (by simpa using hf) hpost

theorem preserved_a0_a1 : ∀ r ∈ preserved, r ≠ .a0 ∧ r ≠ .a1 := by decide

/-- The writable regions with a frame pushed: the state is still in them. -/
theorem covers_push {wr : List Region} {st f : Addr} (hw : Covers [⟨st, 200⟩] wr) :
    Covers [⟨st, 200⟩, ⟨f, 512⟩] (⟨f, 512⟩ :: wr) := by
  intro a n ⟨r, hr, hc⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · obtain ⟨r', hr', hc'⟩ := hw a n ⟨_, List.mem_singleton_self _, hc⟩
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩
  · exact ⟨_, List.mem_cons_self .., hc⟩

/-- The scratch frame of 512 bytes below `sp`, and the permutation's 608
below it. -/
theorem scratch_sp {sp : Addr} (hal : sp.toNat % 16 = 0) (hsp : 1120 ≤ sp.toNat) :
    (sp - BitVec.ofNat 64 512).toNat % 16 = 0 ∧ 608 ≤ (sp - BitVec.ofNat 64 512).toNat ∧
      sp - BitVec.ofNat 64 512 - 608 = sp - BitVec.ofNat 64 1120 := by
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hsp]),
    BitVec.toNat_ofNat]
  refine ⟨by omega_using [hal, hsp], by omega_using [hsp], ?_⟩
  rw [BitVec.sub_sub]; rfl

/-- A call in a frame of 512 bytes of scratch space: what holds after it,
from what the call ensures. -/
theorem scratch_post {s s' : State} {st : Addr} {m : Mem} {u : Nat → BitVec 64}
    (wr₂ : s'.wr = ⟨s.sp - BitVec.ofNat 64 512, 512⟩ :: s.wr) (sp₂ : s'.sp = s.sp - BitVec.ofNat 64 512)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨s.sp - BitVec.ofNat 64 512, 512⟩)
    (f' : Frame [⟨st, 200⟩, ⟨s.sp - BitVec.ofNat 64 512, 512⟩, ⟨s.sp - BitVec.ofNat 64 1120, 608⟩]
      s.mem s'.mem)
    (fl : Frame [⟨s.sp - BitVec.ofNat 64 512, 512⟩] s'.mem m) :
    let t : State := { freed 512 s' with mem := m, unknowns := u }
    t.rd = s'.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr = s'.gpr ∧
      Frame [⟨st, 200⟩, ⟨s.sp - BitVec.ofNat 64 512, 512⟩, ⟨s.sp - BitVec.ofNat 64 1120, 608⟩] s.mem t.mem ∧
      stateAt t.mem st = stateAt s'.mem st := by
  intro t
  refine ⟨by simp only [t, freed], ?_, ?_, by simp only [t, freed], ?_, ?_⟩
  · simp only [t, freed, wr₂, List.tail_cons]
  · simp only [t, freed, sp₂, BitVec.sub_add_cancel]
  · exact f'.trans (fl.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · exact Proof.Sha3.stateAt_congr fun i hi => lost_byte fl d₁ hi

/-- `permuteAt`: calling `vg_keccak_f1600` on the state at `s2`, with scratch
space in a frame of its own, the 512 bytes below the stack pointer. -/
theorem permuteAt_ok {s : State} {st : Addr} (h1 : s.gpr .s2 = st)
    (hal : s.sp.toNat % 16 = 0) (hsp : 1120 ≤ s.sp.toNat)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨s.sp - BitVec.ofNat 64 512, 512⟩)
    (d₂ : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 1120, 608⟩ ⟨st, 200⟩)
    (hw : Covers [⟨st, 200⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨s.sp - BitVec.ofNat 64 512, 512⟩, ⟨s.sp - BitVec.ofNat 64 1120, 608⟩]
        s.mem s'.mem →
      stateAt s'.mem st = keccakF (stateAt s.mem st) → Q s') :
    WP isa permuteAt s Q := by
  obtain ⟨al', sp', e'⟩ := scratch_sp hal hsp
  unfold permuteAt scratchBytes mov
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by omega_using [hsp]) ?_
  refine WP.seq (wp_mv fun s₁ u₁ => wp_addSp (by decide) fun s₂ u₂ => WP.block_nil ?_)
  obtain sp₂ : s₂.sp = s.sp - BitVec.ofNat 64 512 := by rw [u₂.sp, u₁.sp]; rfl
  obtain hm : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]; rfl
  obtain wr₂ : s₂.wr = ⟨s.sp - BitVec.ofNat 64 512, 512⟩ :: s.wr := by rw [u₂.wr, u₁.wr]; rfl
  obtain rd₂ : s₂.rd = s.rd := by rw [u₂.rd, u₁.rd]; rfl
  refine call_ok (st := st) (by rw [u₂.other _ (by decide), u₁.gpr]; exact h1)
    (by rw [u₂.gpr, sp₂, u₁.sp]; exact BitVec.add_zero _) (by rw [sp₂]; exact al')
    (by rw [sp₂]; exact sp') (by rw [sp₂]; exact d₁) (by rw [sp₂, e']; exact d₂)
    (by rw [sp₂, wr₂]; exact covers_push hw) fun s' rd' wr' sp'' cs' f' e'' => ?_
  intro m u fl
  rw [sp₂, e', hm] at f'
  obtain ⟨hr', hw', hs', hg', hf', hst⟩ := scratch_post (u := u) (wr'.trans wr₂) (sp''.trans sp₂) d₁ f' fl
  refine hQ _ (hr'.trans (rd'.trans rd₂)) hw' hs' (fun r hr => ?_) hf' (by rw [hst, e'', hm])
  rw [hg']
  exact (cs' r hr).trans ((u₂.other _ (preserved_a0_a1 r hr).2).trans (u₁.other _ (preserved_a0_a1 r hr).1))

/-- Calling `vg_keccak_f1600` on the state at `a0`, with scratch space at
`a1`, anywhere apart from the state and the 608 bytes below the stack
pointer: as `call_ok`. -/
theorem callWs_ok {s : State} {st w : Addr} (h0 : s.gpr .a0 = st) (h1 : s.gpr .a1 = w)
    (hal : s.sp.toNat % 16 = 0) (hsp : 608 ≤ s.sp.toNat)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨w, 512⟩) (d₂ : Region.Disjoint ⟨s.sp - 608, 608⟩ ⟨st, 200⟩)
    (d₃ : Region.Disjoint ⟨s.sp - 608, 608⟩ ⟨w, 512⟩)
    (hw : Covers [⟨st, 200⟩, ⟨w, 512⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨w, 512⟩, ⟨s.sp - 608, 608⟩] s.mem s'.mem →
      stateAt s'.mem st = keccakF (stateAt s.mem st) → Q s') :
    WP isa (.call "vg_keccak_f1600" Impl.Sha3.RISCV64.permute) s Q := by
  have c0 : s.callEntry.gpr .a0 = st := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .a1 = w := (State.callEntry_gpr _ (by decide)).trans h1
  refine WP.callAny (k := Proof.Sha3.permuteRISCV64) permute_correct
    (rd := []) (wr := [⟨st, 200⟩, ⟨w, 512⟩]) ?_ ?_ hw ?_ (by rw [permute_sdepth]; decide)
  · simp only [Proof.Sha3.permuteRISCV64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, c0, c1]
    exact ⟨trivial, trivial, d₁, hal, hsp, d₂, d₃⟩
  · intro a n h
    obtain ⟨r, hr, hc⟩ := hw a n (by simpa using h)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · intro s' hrd hwr hsp' hf hcs hpost
    simp only [Proof.Sha3.permuteRISCV64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0] at hpost
    rw [permute_sdepth] at hf
    exact hQ s' hrd hwr hsp' hcs (by simpa using hf) hpost

/-- `permuteAtWs`: calling `vg_keccak_f1600` on the state at `s2`, with
scratch space at `s7`. -/
theorem permuteAtWs_ok {s : State} {st w : Addr} (h2 : s.gpr .s2 = st) (h7 : s.gpr .s7 = w)
    (hal : s.sp.toNat % 16 = 0) (hsp : 608 ≤ s.sp.toNat)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨w, 512⟩) (d₂ : Region.Disjoint ⟨s.sp - 608, 608⟩ ⟨st, 200⟩)
    (d₃ : Region.Disjoint ⟨s.sp - 608, 608⟩ ⟨w, 512⟩)
    (hw : Covers [⟨st, 200⟩, ⟨w, 512⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨w, 512⟩, ⟨s.sp - 608, 608⟩] s.mem s'.mem →
      stateAt s'.mem st = keccakF (stateAt s.mem st) → Q s') :
    WP isa permuteAtWs s Q := by
  unfold permuteAtWs mov
  refine WP.seq (wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => WP.block_nil ?_)
  have sp₂ : s₂.sp = s.sp := by rw [u₂.sp, u₁.sp]
  have hm : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine callWs_ok (st := st) (w := w) (by rw [u₂.other _ (by decide), u₁.gpr, h2])
    (by rw [u₂.gpr, u₁.other _ (by decide), h7]) (by rw [sp₂]; exact hal)
    (by rw [sp₂]; exact hsp) d₁ (by rw [sp₂]; exact d₂) (by rw [sp₂]; exact d₃)
    (by rw [u₂.wr, u₁.wr]; exact hw) fun s' rd' wr' sp' cs' f' e' => ?_
  refine hQ s' (by rw [rd', u₂.rd, u₁.rd]) (by rw [wr', u₂.wr, u₁.wr]) (by rw [sp', sp₂])
    (fun r hr => ?_) (by rw [← hm, ← sp₂]; exact f') (by rw [e', hm])
  rw [cs' r hr, u₂.other _ (preserved_a0_a1 r hr).2, u₁.other _ (preserved_a0_a1 r hr).1]

end VG.Proof.Sha3.RISCV64

end

end

/-!
# The SHA-3 sponge on RISC-V: the frame of `absorb` and `squeeze`

`absorb` and `squeeze` run in a frame of 48 bytes (`withLoop`): the saved
return address and `s2`–`s6`. Below it, the permutation's scratch space is a
frame of 512 bytes around its call (`permuteAt`), and below that the
permutation's own frame: they use the 1168 bytes below the stack pointer
(`K`). `setup_ok` saves the registers, `Saved` says the frame still holds
them, and `epilogue_ok` returns the position and restores them.
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64.Stream

open VG VG.RISCV64 VG.RISCV64.Wp VG.Impl.Sha3.RISCV64.Stream

section
variable (s₀ : State)

/-- The stack below the stack pointer that the function and the permutation use. -/
abbrev K : Addr := s₀.sp - BitVec.ofNat 64 1168
abbrev KR : Region := ⟨K s₀, 1168⟩
/-- The frame's base. -/
abbrev B : Addr := s₀.sp - BitVec.ofNat 64 48
/-- The frame's region. -/
abbrev BR : Region := ⟨B s₀, 48⟩

end

/-- The stack pointer: aligned, with room for the frames. -/
structure Stk (s₀ : State) : Prop where
  al : s₀.sp.toNat % 16 = 0
  sp : 1168 ≤ s₀.sp.toNat

/-- The parts of the stack used. -/
theorem sub_K (s₀ : State) {d n : Nat} (h : d + n ≤ 1168) :
    Region.Sub ⟨K s₀ + BitVec.ofNat 64 d, n⟩ (KR s₀) :=
  Offset.sub_base _ h

namespace Stk
variable {s₀ : State} (hk : Stk s₀)
include hk

theorem B_eq : B s₀ = K s₀ + BitVec.ofNat 64 1120 := by
  have := hk.sp
  simp only [B, K]; bv_omega

theorem B_toNat : (B s₀).toNat = s₀.sp.toNat - 48 := by
  have := hk.sp
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [this]), BitVec.toNat_ofNat]

theorem B_al : (B s₀).toNat % 16 = 0 := by
  rw [hk.B_toNat]; have := hk.al; have := hk.sp; omega_arith

theorem B_1120 : 1120 ≤ (B s₀).toNat := by rw [hk.B_toNat]; have := hk.sp; omega_using [this]

theorem below_eq : B s₀ - BitVec.ofNat 64 1120 = K s₀ := by
  rw [hk.B_eq]; exact BitVec.add_sub_cancel _ _

theorem B_off (d : Nat) : B s₀ + BitVec.ofNat 64 d = K s₀ + BitVec.ofNat 64 (1120 + d) := by
  rw [hk.B_eq, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem scr_eq : B s₀ - BitVec.ofNat 64 512 = K s₀ + BitVec.ofNat 64 608 := by
  have := hk.sp
  simp only [B, K]; bv_omega

theorem scr_sub : Region.Sub ⟨B s₀ - BitVec.ofNat 64 512, 512⟩ (KR s₀) := by
  rw [hk.scr_eq]; exact sub_K s₀ (by omega_using [])

theorem below_sub : Region.Sub ⟨B s₀ - BitVec.ofNat 64 1120, 608⟩ (KR s₀) := by
  rw [hk.below_eq]; simpa using sub_K s₀ (d := 0) (n := 608) (by omega_using [])

/-- A slot of the saved registers. -/
theorem slot_sub {d : Nat} (h' : d + 8 ≤ 48) :
    Region.Sub ⟨B s₀ + BitVec.ofNat 64 d, 8⟩ (KR s₀) := by
  rw [hk.B_off]; exact sub_K s₀ (by omega)

/-- The slots of the saved registers are not in the permutation's scratch
space. -/
theorem slot_scr {d : Nat} (h' : d + 8 ≤ 48) :
    Region.Disjoint ⟨B s₀ + BitVec.ofNat 64 d, 8⟩ ⟨B s₀ - BitVec.ofNat 64 512, 512⟩ := by
  rw [hk.scr_eq, hk.B_off]; exact Offset.disjoint _ (.inr (by omega_using [])) (by omega_using [h']) (by omega_using [])

theorem slot_below {d : Nat} (h' : d + 8 ≤ 48) :
    Region.Disjoint ⟨B s₀ + BitVec.ofNat 64 d, 8⟩ ⟨B s₀ - BitVec.ofNat 64 1120, 608⟩ := by
  rw [hk.below_eq, hk.B_off]; exact Offset.disjoint_base _ (by omega) (by omega_using [h'])

end Stk

/-! ## Saving the registers -/

theorem saved_bound : ∀ p ∈ saved, p.2 + 8 ≤ 48 ∧ p.2 % 8 = 0 := by decide

/-- The frame at `b` holds the caller's registers `g`. -/
def Saved (b : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  ∀ p ∈ saved, m.readW (b + BitVec.ofNat 64 p.2) 64 = g p.1

/-- Writes outside the slots keep them. -/
theorem Saved.frame {b : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Saved b g m) {rs : List Region}
    (hd : ∀ d, d + 8 ≤ 48 → ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 d, 8⟩ r)
    (hf : Frame rs m m') : Saved b g m' := fun p hp => by
  have := saved_bound p hp
  rw [hf.readW (Region.contains_self _ _) (hd _ this.1) (by decide)]
  exact h p hp

theorem readW_writeW_off (m : Mem) (b : Addr) (v : BitVec 64) {d e : Nat}
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d < 2 ^ 32) (he : e < 2 ^ 32) :
    (m.writeW (b + BitVec.ofNat 64 e) v).readW (b + BitVec.ofNat 64 d) 64 =
      m.readW (b + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by omega_using [hd]) (by omega_using [he])) (by decide)

theorem save_eq : save = [.addSp .t0 0, .store .d .ra .t0 0, .store .d .s2 .t0 8,
    .store .d .s3 .t0 16, .store .d .s4 .t0 24, .store .d .s5 .t0 32, .store .d .s6 .t0 40] := rfl

/-- Saving the registers in the frame at the stack pointer. -/
theorem save_ok {rest : List Instr} {s : State} {Q : State → Prop} (hal : s.sp.toNat % 16 = 0)
    (hin : ∀ d, d + 8 ≤ 48 → InRegions s.wr (s.sp + BitVec.ofNat 64 d) 8)
    (k : ∀ s', (∀ r, r ≠ .t0 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Saved s.sp s.gpr s'.mem → Frame [⟨s.sp, 48⟩] s.mem s'.mem →
      WP isa (.block rest) s' Q) :
    WP isa (.block (save ++ rest)) s Q := by
  rw [save_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp (by decide) fun s₀ u₀ => ?_
  obtain g0 : s₀.gpr .t0 = s.sp := by rw [u₀.gpr]; exact BitVec.add_zero _
  have o : ∀ r, r ≠ .t0 → s₀.gpr r = s.gpr r := u₀.other
  obtain st : ∀ d, d % 8 = 0 → d + 8 ≤ 48 → ∀ s' : State, s'.gpr .t0 = s.sp →
      s'.wr = s.wr →
      s'.gpr .t0 + BitVec.ofNat 64 d = s.sp + BitVec.ofNat 64 d ∧
      (s.sp + BitVec.ofNat 64 d).toNat % 8 = 0 ∧ InRegions s'.wr (s.sp + BitVec.ofNat 64 d) 8 :=
    fun d hd h₂ s' h₀ hw => ⟨by rw [h₀], al8 hal hd (by omega_using [h₂]), by rw [hw]; exact hin d h₂⟩
  obtain hc : ∀ d, d + 8 ≤ 48 →
      (⟨s.sp, 48⟩ : Region).Contains (s.sp + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h₂ => Offset.contains_base _ h₂ (by omega_using [h₂])
  obtain ⟨a1, l1, i1⟩ := st 0 (by decide) (by omega_using []) s₀ g0 u₀.wr
  refine wp_sd (by decide) a1 l1 i1 fun s₁ g₁ => ?_
  obtain ⟨a2, l2, i2⟩ := st 8 (by decide) (by omega_using []) s₁ (by rw [g₁.gpr, g0])
    (by rw [g₁.wr, u₀.wr])
  refine wp_sd (by decide) a2 l2 i2 fun s₂ g₂ => ?_
  obtain ⟨a3, l3, i3⟩ := st 16 (by decide) (by omega_using []) s₂ (by rw [g₂.gpr, g₁.gpr, g0])
    (by rw [g₂.wr, g₁.wr, u₀.wr])
  refine wp_sd (by decide) a3 l3 i3 fun s₃ g₃ => ?_
  obtain ⟨a4, l4, i4⟩ := st 24 (by decide) (by omega_using []) s₃
    (by rw [g₃.gpr, g₂.gpr, g₁.gpr, g0]) (by rw [g₃.wr, g₂.wr, g₁.wr, u₀.wr])
  refine wp_sd (by decide) a4 l4 i4 fun s₄ g₄ => ?_
  obtain ⟨a5, l5, i5⟩ := st 32 (by decide) (by omega_using []) s₄
    (by rw [g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr, g0]) (by rw [g₄.wr, g₃.wr, g₂.wr, g₁.wr, u₀.wr])
  refine wp_sd (by decide) a5 l5 i5 fun s₅ g₅ => ?_
  obtain ⟨a6, l6, i6⟩ := st 40 (by decide) (by omega_using []) s₅
    (by rw [g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr, g0])
    (by rw [g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr, u₀.wr])
  refine wp_sd (by decide) a6 l6 i6 fun s₆ g₆ => ?_
  obtain gg : s₆.gpr = s₀.gpr := by rw [g₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr]
  obtain hm : s₆.mem = (((((s.mem.writeW (s.sp + BitVec.ofNat 64 0) (s.gpr .ra)).writeW
      (s.sp + BitVec.ofNat 64 8) (s.gpr .s2)).writeW (s.sp + BitVec.ofNat 64 16) (s.gpr .s3)).writeW
      (s.sp + BitVec.ofNat 64 24) (s.gpr .s4)).writeW (s.sp + BitVec.ofNat 64 32) (s.gpr .s5)).writeW
      (s.sp + BitVec.ofNat 64 40) (s.gpr .s6) := by
    rw [g₆.mem, g₅.mem, g₄.mem, g₃.mem, g₂.mem, g₁.mem, u₀.mem, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr,
      g₁.gpr, o _ (by decide), o _ (by decide), o _ (by decide), o _ (by decide), o _ (by decide),
      o _ (by decide)]
  refine k s₆ (fun r hr => by rw [gg, o r hr])
    (by rw [g₆.rd, g₅.rd, g₄.rd, g₃.rd, g₂.rd, g₁.rd, u₀.rd])
    (by rw [g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr, u₀.wr])
    (by rw [g₆.sp, g₅.sp, g₄.sp, g₃.sp, g₂.sp, g₁.sp, u₀.sp]) (fun p hp => ?_) ?_
  · rw [hm]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := omega_using []) only [Mem.readW_writeW_self64, readW_writeW_off]
  · rw [hm]
    exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hc 0 (by omega_using []))).writeW
      (List.mem_singleton_self _) _ (hc 8 (by omega_using []))).writeW (List.mem_singleton_self _) _
      (hc 16 (by omega_using []))).writeW (List.mem_singleton_self _) _
      (hc 24 (by omega_using []))).writeW (List.mem_singleton_self _) _
      (hc 32 (by omega_using []))).writeW (List.mem_singleton_self _) _ (hc 40 (by omega_using []))

theorem restore_eq : restore = [.addSp .t0 0, .load .d .ra .t0 0, .load .d .s2 .t0 8,
    .load .d .s3 .t0 16, .load .d .s4 .t0 24, .load .d .s5 .t0 32, .load .d .s6 .t0 40] := rfl

/-- Returning the position and restoring the registers from the frame at the
stack pointer. -/
theorem epilogue_ok {s : State} {g : Reg → BitVec 64} (hal : s.sp.toNat % 16 = 0)
    (hin : ∀ d, d + 8 ≤ 48 → InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 d) 8)
    (hsv : Saved s.sp g s.mem) {Q : State → Prop}
    (k : ∀ s', s'.gpr .a0 = s.gpr .s4 → (∀ p ∈ saved, s'.gpr p.1 = g p.1) →
      (∀ r, r ∉ saved.map Prod.fst → r ≠ .a0 → r ≠ .t0 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block (mov .a0 .s4 :: restore)) s Q := by
  refine wp_mv fun s₀ u₀ => ?_
  rw [restore_eq]
  refine wp_addSp (by decide) fun s₁ u₁ => ?_
  obtain g1 : s₁.gpr .t0 = s.sp := by rw [u₁.gpr, u₀.sp]; exact BitVec.add_zero _
  obtain v : ∀ r d, (r, d) ∈ saved → s.mem.readW (s.sp + BitVec.ofNat 64 d) 64 = g r :=
    fun r d h => hsv (r, d) h
  obtain ld : ∀ d, d % 8 = 0 → d + 8 ≤ 48 → ∀ s' : State, s'.gpr .t0 = s.sp →
      s'.rd = s.rd → s'.wr = s.wr →
      s'.gpr .t0 + BitVec.ofNat 64 d = s.sp + BitVec.ofNat 64 d ∧
      (s.sp + BitVec.ofNat 64 d).toNat % 8 = 0 ∧ InRegions (s'.rd ++ s'.wr) (s.sp + BitVec.ofNat 64 d) 8 :=
    fun d hd h₂ s' h₀ hr hw => ⟨by rw [h₀], al8 hal hd (by omega_using [h₂]), by rw [hr, hw]; exact hin d h₂⟩
  obtain rd₁ : s₁.rd = s.rd := by rw [u₁.rd, u₀.rd]
  obtain wr₁ : s₁.wr = s.wr := by rw [u₁.wr, u₀.wr]
  obtain m₁ : s₁.mem = s.mem := by rw [u₁.mem, u₀.mem]
  obtain ⟨a1, l1, i1⟩ := ld 0 (by decide) (by omega_using []) s₁ g1 rd₁ wr₁
  refine wp_ld (by decide) a1 l1 i1 fun s₂ u₂ => ?_
  obtain ⟨a2, l2, i2⟩ := ld 8 (by decide) (by omega_using []) s₂
    (by rw [u₂.other _ (by decide), g1]) (by rw [u₂.rd, rd₁]) (by rw [u₂.wr, wr₁])
  refine wp_ld (by decide) a2 l2 i2 fun s₃ u₃ => ?_
  obtain ⟨a3, l3, i3⟩ := ld 16 (by decide) (by omega_using []) s₃
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), g1]) (by rw [u₃.rd, u₂.rd, rd₁])
    (by rw [u₃.wr, u₂.wr, wr₁])
  refine wp_ld (by decide) a3 l3 i3 fun s₄ u₄ => ?_
  obtain ⟨a4, l4, i4⟩ := ld 24 (by decide) (by omega_using []) s₄
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g1])
    (by rw [u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁])
  refine wp_ld (by decide) a4 l4 i4 fun s₅ u₅ => ?_
  obtain ⟨a5, l5, i5⟩ := ld 32 (by decide) (by omega_using []) s₅
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g1])
    (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
  refine wp_ld (by decide) a5 l5 i5 fun s₆ u₆ => ?_
  obtain ⟨a6, l6, i6⟩ := ld 40 (by decide) (by omega_using []) s₆
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g1])
    (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
  refine wp_ld (by decide) a6 l6 i6 fun s₇ u₇ => WP.block_nil ?_
  obtain mm : ∀ (x : State), x.mem = s₁.mem → x.mem = s.mem := fun x h => h.trans m₁
  obtain m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  refine k s₇ ?_ (fun p hp => ?_) (fun r hr h0 ht => ?_) m₇
    (by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁])
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
    (by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, u₀.sp])
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      u₀.gpr]
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, m₁, v .ra 0 (by simp [saved])]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.gpr, u₂.mem, m₁, v .s2 8 (by simp [saved])]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem,
        u₂.mem, m₁, v .s3 16 (by simp [saved])]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, m₁,
        v .s4 24 (by simp [saved])]
    · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁,
        v .s5 32 (by simp [saved])]
    · rw [u₇.gpr, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁, v .s6 40 (by simp [saved])]
  · simp only [saved, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
    rw [u₇.other _ h6, u₆.other _ h5, u₅.other _ h4, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1,
      u₁.other _ ht, u₀.other _ h0]

/-! ## The test for a lane -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

private theorem wp_or {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

private theorem wp_andi7 {d n : Reg} (k : ∀ s', Upd s s' d (s.gpr n &&& 7) → WP isa (.block is) s' Q) :
    WP isa (.block (.logicImm .and d n 7 :: is)) s Q :=
  WP.cons (exec_logicImm (by decide)) (k _ (Upd.write _ _ _))

private theorem wp_sltu {d n m : Reg}
    (k : ∀ s', Upd s s' d (if s.gpr n < s.gpr m then 1 else 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.sltu d n m :: is)) s Q :=
  WP.cons exec_sltu (k _ (Upd.write _ _ _))

end

private theorem and7_eq_zero {x : BitVec 64} (h : x &&& 7 = 0) : x.toNat % 8 = 0 := by
  obtain h' := congrArg BitVec.toNat h
  rwa [BitVec.toNat_and, show (7 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod] at h'

/-- `laneCheck`, from `s2` = `st`, `s4` = `j` and `s6` = `n`: it changes only
`t1`–`t4`, leaves `st + j` in `t2`, leaves `t1 = 0` only if `j` and `st + j`
are multiples of 8 and `n ≥ 8`, and `t4 = 0` only if `s5` is a multiple of 8. -/
theorem laneCheck_ok {s : State} {st : Addr} {j n : Nat} (h2 : s.gpr .s2 = st)
    (h4 : s.gpr .s4 = BitVec.ofNat 64 j) (h6 : s.gpr .s6 = BitVec.ofNat 64 n) (hj : j < 2 ^ 64)
    (hn : n < 2 ^ 64) :
    WP isa (.block laneCheck) s fun s' =>
      (∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → s'.gpr r = s.gpr r) ∧
      s'.gpr .t2 = st + BitVec.ofNat 64 j ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧
      (s'.gpr .t1 = 0 → j % 8 = 0 ∧ (st + BitVec.ofNat 64 j).toNat % 8 = 0 ∧ 8 ≤ n) ∧
      (s'.gpr .t4 = 0 → (s.gpr .s5).toNat % 8 = 0) := by
  unfold laneCheck
  refine wp_add fun s₁ u₁ => wp_or fun s₂ u₂ => wp_andi7 fun s₃ u₃ =>
    wp_li (by decide) fun s₄ u₄ => wp_sltu fun s₅ u₅ => wp_or fun s₆ u₆ =>
    wp_andi7 fun s₇ u₇ => WP.block_nil ?_
  obtain g : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → s₇.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => by
      rw [u₇.other r h4, u₆.other r h1, u₅.other r h3, u₄.other r h4, u₃.other r h1,
        u₂.other r h1, u₁.other r h2]
  obtain ht2 : s₇.gpr .t2 = st + BitVec.ofNat 64 j := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h2, h4]
  refine ⟨g, ht2, by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem],
    by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp], fun hz => ?_, fun hz => ?_⟩
  · have e6 : s₄.gpr .s6 = BitVec.ofNat 64 n := by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), h6]
    obtain e4 : s₁.gpr .s4 = BitVec.ofNat 64 j := by rw [u₁.other _ (by decide), h4]
    obtain e2 : s₁.gpr .t2 = st + BitVec.ofNat 64 j := by rw [u₁.gpr, h2, h4]
    rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₅.gpr, u₄.gpr,
      u₄.other _ (by decide), u₃.gpr, u₂.gpr, e6, e4, e2] at hz
    obtain ⟨ha, hb⟩ := BitVec.or_eq_zero_iff.mp hz
    rw [BitVec.and_or_distrib_right] at ha
    obtain ⟨h₁, h₃⟩ := BitVec.or_eq_zero_iff.mp ha
    obtain h₃' := and7_eq_zero h₃
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj] at h₃'
    refine ⟨h₃', and7_eq_zero h₁, ?_⟩
    by_cases hl : BitVec.ofNat 64 n < 8#64
    · rw [ite_eq_left hl] at hb; exact absurd hb (by decide)
    · rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at hl
      exact Nat.le_of_not_lt hl
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)] at hz
    exact and7_eq_zero hz

/-- `loadData`: the lane at `a` (`s5`) into `t1`, changing only `t1`, `t3` and
`t4`. -/
theorem loadData_ok {al : Bool} {rest : List Instr} {s : State} {Q : State → Prop} {a : Addr}
    (h5 : s.gpr .s5 = a) (hal : al = true → a.toNat % 8 = 0) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Words64.Upd3 s s' .t1 .t3 .t4 (s.mem.readW a 64) → WP isa (.block rest) s' Q) :
    WP isa (.block (loadData al ++ rest)) s Q := by
  cases al
  · rw [loadData, ite_eq_right (by decide), WP.block_append_iff]
    obtain ea : s.gpr .s5 + BitVec.ofNat 64 0 = a := by rw [h5]; simp
    refine WP.mono (Words64.loadLE64_ok (d := .t1) (tmp := .t3) (tmp2 := .t4) (n := .s5) (off := 0)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [ea]; exact hin)) fun s' u => k s' ?_
    rw [ea] at u; exact u
  · rw [loadData, ite_eq_left rfl]
    exact wp_ld (a := a) (by decide) (by rw [h5]; simp) (hal rfl) hin fun s' u =>
      k s' ⟨u.gpr, fun r h1 _ _ => u.other r h1, u.mem, u.rd, u.wr, u.sp⟩

/-- `storeData`: `t1` to the lane at `a` (`s5`), changing only `t3` and `t4`. -/
theorem storeData_ok {al : Bool} {rest : List Instr} {s : State} {Q : State → Prop} {a : Addr}
    (h5 : s.gpr .s5 = a) (hal : al = true → a.toNat % 8 = 0) (hout : InRegions s.wr a 8)
    (k : ∀ s', (∀ r, r ≠ .t3 → r ≠ .t4 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem.writeW a (s.gpr .t1) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      WP isa (.block rest) s' Q) :
    WP isa (.block (storeData al ++ rest)) s Q := by
  cases al
  · rw [storeData, ite_eq_right (by decide), WP.block_append_iff]
    obtain ea : s.gpr .s5 + BitVec.ofNat 64 0 = a := by rw [h5]; simp
    refine WP.mono (Words64.storeLE64_ok (v := .t1) (tmp := .t3) (tmp2 := .t4) (n := .s5) (off := 0)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [ea]; exact hout))
      fun s' ⟨g, m, rd, wr, sp⟩ => k s' g (by rw [m, ea]) rd wr sp
  · rw [storeData, ite_eq_left rfl]
    exact wp_sd (a := a) (by decide) (by rw [h5]; simp) (hal rfl) hout fun s' u =>
      k s' (fun r _ _ => by rw [u.gpr]) u.mem u.rd u.wr u.sp

end VG.Proof.Sha3.RISCV64.Stream

end

end

/-!
# The SHA-3 sponge on RISC-V: `absorb`

The structure of the PPC64LE proof (`Proof/Sha3/PPC64LE/Stream/Absorb.lean`),
a lane (`body_word`) or a byte (`body_byte`) at a time, in the frame of
`Stream/Common.lean`.
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64.Stream.Absorb

open VG VG.RISCV64 VG.RISCV64.Wp VG.Impl.Sha3.RISCV64.Stream
open VG.Proof.Sha3.RISCV64 VG.Proof.Sha3.RISCV64.Stream
open VG.Proof.Sha3 (Rep rep_append xorByte stateAt_xorByte ofNat_beq_zero sub_beq_zero sub_ofNat
  xor_setWidth writeW8_apply bytesAt_succ bytesAt_length toNat_ofNat_lt xorAt xorAt_single byteOf_xorAt
  byteOf_stateAt writeW64_byte)
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .a0
abbrev rt : Nat := (s₀.gpr .a1).toNat
abbrev pos : Nat := (s₀.gpr .a2).toNat
abbrev dp : Addr := s₀.gpr .a3
abbrev len : Nat := (s₀.gpr .a4).toNat
abbrev stR : Region := ⟨st s₀, 200⟩
abbrev dR : Region := ⟨dp s₀, len s₀⟩
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := bytesAt s₀.mem (dp s₀) c

/-- The messages the initial state and position represent. -/
def Msg (msg : List Byte) : Prop :=
  stateAt s₀.mem (st s₀) = Rep (rt s₀) msg ∧ pos s₀ = msg.length % rt s₀

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [stR s₀]
  d_st : (dR s₀).Disjoint (stR s₀)
  stk : Stk s₀
  k_st : (KR s₀).Disjoint (stR s₀)
  k_d : (KR s₀).Disjoint (dR s₀)
  rate : rt s₀ ∈ rates
  pos_lt : pos s₀ < rt s₀

theorem pre_of {s₀ : State} (h : Proof.Sha3.absorbRISCV64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, ⟨h4, h5⟩, h6, h7, h8, h9⟩

theorem Pre.rt_pos {s₀ : State} (hp : Pre s₀) : 0 < rt s₀ ∧ rt s₀ ≤ 168 := by
  obtain h := Proof.Sha3.rate_bounds hp.rate
  omega_using [h]

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 64 := (s₀.gpr .a4).isLt

/-- The callee-saved registers our code never writes. -/
abbrev untouched : List Reg := [.s0, .s1, .s7, .s8, .s9, .s10, .s11]

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = [dR s₀]
  wr : s.wr = [BR s₀, stR s₀]
  sp : s.sp = B s₀
  s2 : s.gpr .s2 = st s₀
  s3 : s.gpr .s3 = s₀.gpr .a1
  s5 : s.gpr .s5 = dp s₀ + BitVec.ofNat 64 c
  s6 : s.gpr .s6 = BitVec.ofNat 64 (len s₀ - c)
  frame : Frame [stR s₀, KR s₀] s₀.mem s.mem
  saved : Saved (B s₀) s₀.gpr s.mem
  untouched : ∀ r ∈ untouched, s.gpr r = s₀.gpr r

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv (s₀ : State) (c : Nat) (s : State) : Prop extends Common s₀ c s where
  s4 : s.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀)
  repr : ∀ msg, Msg s₀ msg → stateAt s.mem (st s₀) = Rep (rt s₀) (msg ++ D s₀ c)

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Common s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dp s₀ + BitVec.ofNat 64 i) = s₀.mem (dp s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.k_d.symm⟩) (Nat.le_of_lt (len_lt s₀)) hi

/-! ## The prologue -/

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block setup) (allocd 48 s₀) (Inv s₀ 0) := by
  have hk := hp.stk
  unfold setup
  refine save_ok (s := allocd 48 s₀) hk.B_al (fun d hd₂ => ⟨BR s₀, List.mem_cons_self ..,
      Offset.contains_base _ (by omega_using [hd₂]) (by omega_using [hd₂])⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ sv₁ f₁ => ?_
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ =>
    wp_mv fun s₆ u₆ => WP.block_nil ?_
  obtain hm : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  obtain f₁' : Frame [stR s₀, KR s₀] s₀.mem s₁.mem :=
    f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨KR s₀, by simp, by
        rw [show (allocd 48 s₀).sp = B s₀ from rfl, hk.B_eq]; exact sub_K s₀ (by omega_using [])⟩
  obtain g : ∀ r, r ≠ .t0 → s₁.gpr r = s₀.gpr r := fun r h => g₁ r h
  refine ⟨⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hm]; exact f₁', by rw [hm]; exact sv₁,
      fun r hr => ?_⟩, ?_, fun msg ⟨hs, _⟩ => ?_⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]; exact hp.rd
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]; simp only [allocd, hp.wr]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]; rfl
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, g _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), g _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g _ (by decide)]; simp
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g _ (by decide), Nat.sub_zero]; simp [len]
  · have : r ≠ .s2 ∧ r ≠ .s3 ∧ r ≠ .s4 ∧ r ≠ .s5 ∧ r ≠ .s6 ∧ r ≠ .t0 := by revert r; decide
    rw [u₆.other _ this.2.2.2.2.1, u₅.other _ this.2.2.2.1, u₄.other _ this.2.2.1,
      u₃.other _ this.2.1, u₂.other _ this.1, g _ this.2.2.2.2.2]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), g _ (by decide), Nat.add_zero,
      Nat.mod_eq_of_lt hp.pos_lt]
    simp [pos]
  · rw [hm, show D s₀ 0 = [] by simp [bytesAt], List.append_nil, ← hs]
    exact Proof.Sha3.stateAt_congr fun i hi =>
      f₁.bytes (R := stR s₀) (by
        simpa using (hp.k_st.sub_left (by
          rw [show (allocd 48 s₀).sp = B s₀ from rfl, hk.B_eq]; exact sub_K s₀ (by omega_using []))).symm)
        (by show 200 ≤ 2 ^ 64; decide) hi

/-! ## One iteration -/

/-- The byte at position `j` XORed in. -/
theorem body_byte {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State}
    (hI : Inv s₀ c s) :
    WP isa (.block absorbByte) s fun s' =>
      Common s₀ (c + 1) s' ∧ s'.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + 1) ∧
      stateAt s'.mem (st s₀) = xorByte (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (s₀.mem (dp s₀ + BitVec.ofNat 64 c)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain hl := len_lt s₀
  obtain hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  generalize hjd : (pos s₀ + c) % rt s₀ = j at hj ⊢
  obtain hr3 : s.gpr .s4 = BitVec.ofNat 64 j := by rw [hI.s4, hjd]
  obtain hsin : ∀ rs : List Region, stR s₀ ∈ rs → InRegions rs (st s₀ + BitVec.ofNat 64 j) 1 :=
    fun rs h => ⟨stR s₀, h, Offset.contains_base _ (by omega_using [hr₁, hj]) (by omega_using [hr₁, hj])⟩
  refine wp_lbu (t := .t1) (a := dp s₀ + BitVec.ofNat 64 c) (by decide) (by rw [hI.s5]; simp)
    ⟨dR s₀, by simp [hI.rd], Offset.contains_base _ (by omega_using [hc]) (by omega_using [hc, hl])⟩ fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ => ?_
  obtain ea : s₂.gpr .t2 + BitVec.ofNat 64 0 = st s₀ + BitVec.ofNat 64 j := by
    rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), hI.s2, hr3]; simp
  refine wp_lbu (t := .t3) (a := st s₀ + BitVec.ofNat 64 j) (by decide) ea
    (hsin _ (by simp [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hI.rd, hI.wr])) fun s₃ u₃ => ?_
  refine wp_xor fun s₄ u₄ => ?_
  refine wp_sb (a := st s₀ + BitVec.ofNat 64 j) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide)]; exact ea)
    (hsin _ (by simp [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr])) fun s₅ g₅ => ?_
  refine wp_addi (by decide) fun s₆ u₆ => wp_addi (by decide) fun s₇ u₇ =>
    wp_subi (imm := 1) (by decide) fun s₈ u₈ => WP.block_nil ?_
  obtain hv : (s₄.gpr .t1).setWidth 8 =
      s₀.mem (dp s₀ + BitVec.ofNat 64 c) ^^^ s.mem (st s₀ + BitVec.ofNat 64 j) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, u₃.gpr, u₂.mem, u₁.mem,
      xor_setWidth, hI.data hp hc]
  obtain hm₈ : s₈.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 j)
      (s₀.mem (dp s₀ + BitVec.ofNat 64 c) ^^^ s.mem (st s₀ + BitVec.ofNat 64 j)) := by
    rw [u₈.mem, u₇.mem, u₆.mem, g₅.mem, hv, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain hf : Frame [stR s₀] s.mem s₈.mem := by
    rw [hm₈]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using [hr₁, hj]) (by omega_using [hr₁, hj]))
  obtain g : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .s5 → r ≠ .s4 → r ≠ .s6 →
      s₈.gpr r = s.gpr r := fun r h1 h2 h3 h4 h33 h5 => by
    rw [u₈.other r h5, u₇.other r h33, u₆.other r h4, g₅.gpr, u₄.other r h1, u₃.other r h3,
      u₂.other r h2, u₁.other r h1]
  obtain h3 : s₈.gpr .s4 = BitVec.ofNat 64 (j + 1) := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hr3, ← BitVec.ofNat_add]
  refine ⟨⟨by omega_using [hc], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩, h3, ?_⟩
  · rw [u₈.rd, u₇.rd, u₆.rd, g₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₈.wr, u₇.wr, u₆.wr, g₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [u₈.sp, u₇.sp, u₆.sp, g₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp]
  · rw [g .s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.s2]
  · rw [g .s3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.s3]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.s5, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.s6, sub_ofNat (by omega_using [hc]), Nat.sub_sub]
  · exact hI.frame.trans (hf.mono (by simp))
  · exact hI.saved.frame (fun d h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.k_st.sub_left (hp.stk.slot_sub h₂)) hf
  · have hne : r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t3 ∧ r ≠ .s5 ∧ r ≠ .s4 ∧ r ≠ .s6 := by revert r; decide
    rw [g r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2]
    exact hI.untouched r hr
  · refine stateAt_xorByte (by omega_using [hr₁, hj]) ?_ fun i hi hij => ?_
    · rw [hm₈, writeW8_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl), BitVec.xor_comm]
    · rw [hm₈, writeW8_apply, ite_eq_right_of_eq_false _ _
        (eq_false (VG.Proof.Sha3.ne_of_lt200 hi (by omega_using [hr₁, hj]) hij))]

/-- The bytes `c … c + n - 1` of the data follow the first `c`. -/
theorem bytesAt_add (m : Mem) (p : Addr) (c : Nat) :
    ∀ n, bytesAt m p (c + n) = bytesAt m p c ++ bytesAt m (p + BitVec.ofNat 64 c) n
  | 0 => by simp [bytesAt]
  | n + 1 => by
    rw [← Nat.add_assoc, bytesAt_succ, bytesAt_add m p c n, bytesAt_succ, List.append_assoc,
      BitVec.add_assoc, ← BitVec.ofNat_add]

theorem rate_mod8 {r : Nat} (h : r ∈ rates) : r % 8 = 0 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- A lane of a state in memory written: its 8 bytes XORed with `bs`. -/
theorem stateAt_write_lane {m : Mem} {p : Addr} {j : Nat} (hj : j + 8 ≤ 200) {v : BitVec 64}
    {bs : List Byte} (hbs : bs.length = 8)
    (hv : ∀ d < 8, v.extractLsb' (8 * d) 8 = m (p + BitVec.ofNat 64 (j + d)) ^^^ bs.getD d 0) :
    stateAt (m.writeW (p + BitVec.ofNat 64 j) v) p = xorAt (stateAt m p) j bs :=
  Proof.Sha3.ext_bytes fun i hi => by
    rw [byteOf_xorAt _ _ _ hi, byteOf_stateAt _ _ hi, byteOf_stateAt _ _ hi, hbs]
    by_cases c : j ≤ i ∧ i < j + 8
    · rw [ite_eq_left c, show p + BitVec.ofNat 64 i = p + BitVec.ofNat 64 j + BitVec.ofNat 64 (i - j) by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' c.1],
        writeW64_byte _ _ _ (by omega_using [c]), hv _ (by omega_using [c]), Nat.add_sub_cancel' c.1,
        show p + BitVec.ofNat 64 j + BitVec.ofNat 64 (i - j) = p + BitVec.ofNat 64 i by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' c.1]]
    · rw [ite_eq_right c, Mem.writeW, Mem.write_apply]
      rw [Offset.sub_toNat' _ (by omega_using [hj]) (by omega_using [hi])]
      split <;> omega_arith

/-- The lane of data at `c` XORed into the lane at position `j`, both
aligned. -/
theorem body_word {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c + 8 ≤ len s₀) {s : State}
    (hI : Inv s₀ c s) (hj8 : (pos s₀ + c) % rt s₀ % 8 = 0)
    (ht2 : s.gpr .t2 = st s₀ + BitVec.ofNat 64 ((pos s₀ + c) % rt s₀))
    (hal : (st s₀ + BitVec.ofNat 64 ((pos s₀ + c) % rt s₀)).toNat % 8 = 0)
    {al : Bool} (hdal : al = true → (dp s₀ + BitVec.ofNat 64 c).toNat % 8 = 0) :
    WP isa (.block (absorbLane al)) s fun s' =>
      Common s₀ (c + 8) s' ∧ s'.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + 8) ∧
      stateAt s'.mem (st s₀) = xorAt (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) 8) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hl := len_lt s₀
  have h8 := rate_mod8 hp.rate
  have hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  generalize hjd : (pos s₀ + c) % rt s₀ = j at hj hj8 ht2 hal ⊢
  have hj' : j + 8 ≤ rt s₀ := by omega_using [h8, hj, hj8]
  have hr3 : s.gpr .s4 = BitVec.ofNat 64 j := by rw [hI.s4, hjd]
  have hsin : ∀ rs : List Region, stR s₀ ∈ rs → InRegions rs (st s₀ + BitVec.ofNat 64 j) 8 :=
    fun rs h => ⟨stR s₀, h, Offset.contains_base _ (by omega_using [hr₁, hj]) (by omega_using [hr₁, hj])⟩
  unfold absorbLane
  refine loadData_ok (a := dp s₀ + BitVec.ofNat 64 c) (by rw [hI.s5]) hdal
    ⟨dR s₀, by simp [hI.rd], Offset.contains_base _ (by omega_using [hc]) (by omega_using [hc, hl])⟩ fun s₁ u₁ => ?_
  refine wp_ld (t := .t3) (a := st s₀ + BitVec.ofNat 64 j) (by decide)
    (by rw [u₁.other _ (by decide) (by decide) (by decide), ht2]; simp) hal
    (hsin _ (by simp [u₁.rd, u₁.wr, hI.rd, hI.wr])) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_sd (a := st s₀ + BitVec.ofNat 64 j) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide) (by decide) (by decide), ht2]; simp) hal
    (hsin _ (by simp [u₃.wr, u₂.wr, u₁.wr, hI.wr])) fun s₄ g₄ => ?_
  refine wp_addi (by decide) fun s₅ u₅ => wp_addi (by decide) fun s₆ u₆ =>
    wp_subi (imm := 8) (by decide) fun s₇ u₇ => WP.block_nil ?_
  have hv : s₃.gpr .t1 = s.mem.readW (dp s₀ + BitVec.ofNat 64 c) 64 ^^^
      s.mem.readW (st s₀ + BitVec.ofNat 64 j) 64 := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem]
  have hm₇ : s₇.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 j) (s₃.gpr .t1) := by
    rw [u₇.mem, u₆.mem, u₅.mem, g₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hf : Frame [stR s₀] s.mem s₇.mem := by
    rw [hm₇]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using [hr₁, hj]) (by omega_using [hr₁, hj]))
  have g : ∀ r, r ≠ .t1 → r ≠ .t3 → r ≠ .s5 → r ≠ .s4 → r ≠ .s6 → r ≠ .t4 →
      s₇.gpr r = s.gpr r := fun r h1 h3 h4 h33 h5 h6 => by
    rw [u₇.other r h5, u₆.other r h33, u₅.other r h4, g₄.gpr, u₃.other r h1, u₂.other r h3,
      u₁.other r h1 h3 h6]
  have h3 : s₇.gpr .s4 = BitVec.ofNat 64 (j + 8) := by
    rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide) (by decide) (by decide), hr3,
      ← BitVec.ofNat_add]
  refine ⟨⟨by omega_using [hc], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩, h3, ?_⟩
  · rw [u₇.rd, u₆.rd, u₅.rd, g₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [u₇.sp, u₆.sp, u₅.sp, g₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp]
  · rw [g .s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.s2]
  · rw [g .s3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.s3]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide) (by decide) (by decide), hI.s5,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide) (by decide) (by decide), hI.s6,
      sub_ofNat (by omega_using [hc]), Nat.sub_sub]
  · exact hI.frame.trans (hf.mono (by simp))
  · exact hI.saved.frame (fun d h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.k_st.sub_left (hp.stk.slot_sub h₂)) hf
  · have hne : r ≠ .t1 ∧ r ≠ .t3 ∧ r ≠ .s5 ∧ r ≠ .s4 ∧ r ≠ .s6 ∧ r ≠ .t4 := by revert r; decide
    rw [g r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2]
    exact hI.untouched r hr
  · rw [hm₇]
    refine stateAt_write_lane (by omega_using [hr₁, hj]) (bytesAt_length _ _ _) fun d hd => ?_
    rw [hv, BitVec.extractLsb'_xor, Mem.readW, Mem.readW, BitVec.setWidth_eq, BitVec.setWidth_eq,
      Mem.extractLsb'_read _ _ (show d < 64 / 8 by omega_using [hd]),
      Mem.extractLsb'_read _ _ (show d < 64 / 8 by omega_using [hd]),
      BitVec.xor_comm, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 1
    simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hd,
      Option.map_some, Option.getD_some]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hI.data hp (by omega_using [hc, hd])]

theorem keep_preserved : ∀ r ∈ untouched, r ∈ preserved := by decide

/-- The permutation if the block is complete, after `n` bytes of data that
fit in it. -/
theorem full_ok {s₀ : State} (hp : Pre s₀) {c n : Nat} (hn : 0 < n)
    (hfit : (pos s₀ + c) % rt s₀ + n ≤ rt s₀) {s s₁ : State}
    (hI : Inv s₀ c s) (hC : Common s₀ (c + n) s₁)
    (h3 : s₁.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + n))
    (hst : stateAt s₁.mem (st s₀) = xorAt (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) n)) :
    WP isa permuteIfFull s₁ (Inv s₀ (c + n)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hk := hp.stk
  obtain hlen : ∀ msg, Msg s₀ msg → (msg ++ D s₀ c).length % rt s₀ = (pos s₀ + c) % rt s₀ :=
    fun msg ⟨_, hpm⟩ => by rw [List.length_append, bytesAt_length, hpm, Nat.mod_add_mod]
  obtain hrep : ∀ msg, Msg s₀ msg → Rep (rt s₀) (msg ++ D s₀ (c + n)) =
      if (pos s₀ + c) % rt s₀ + n = rt s₀ then keccakF (stateAt s₁.mem (st s₀))
      else stateAt s₁.mem (st s₀) := fun msg hm => by
    rw [D, bytesAt_add, ← List.append_assoc, rep_append hr₀ (by omega_using [hr₁]) _ _
      (by rw [bytesAt_length]; exact hn) (by rw [bytesAt_length, hlen msg hm]; exact hfit),
      hlen msg hm, bytesAt_length, hst, hI.repr msg hm]
  obtain hpc : (pos s₀ + (c + n)) % rt s₀ = if (pos s₀ + c) % rt s₀ + n = rt s₀ then 0
      else (pos s₀ + c) % rt s₀ + n := by
    obtain e := Nat.div_add_mod (pos s₀ + c) (rt s₀)
    rw [show pos s₀ + (c + n) = (pos s₀ + c) + n by omega_using []]
    generalize (pos s₀ + c) % rt s₀ = j at e hfit ⊢
    generalize (pos s₀ + c) / rt s₀ = q at e
    rw [← e]
    split
    · rw [Nat.add_assoc, ‹j + n = rt s₀›, ← Nat.mul_succ, Nat.mul_mod_right]
    · rw [Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega_arith)]
  unfold permuteIfFull
  refine WP.seq (wp_sub fun s₂ u₂ => WP.block_nil ?_)
  obtain hC₂ : Common s₀ (c + n) s₂ :=
    { hC with rd := u₂.rd.trans hC.rd, wr := u₂.wr.trans hC.wr, sp := u₂.sp.trans hC.sp
              s2 := (u₂.other _ (by decide)).trans hC.s2, s3 := (u₂.other _ (by decide)).trans hC.s3
              s5 := (u₂.other _ (by decide)).trans hC.s5, s6 := (u₂.other _ (by decide)).trans hC.s6
              frame := u₂.mem ▸ hC.frame, saved := u₂.mem ▸ hC.saved
              untouched := fun r hr => (u₂.other r (by revert r; decide)).trans (hC.untouched r hr) }
  obtain hz : isa.eval (.zero .t1) s₂ = some (decide ((pos s₀ + c) % rt s₀ + n = rt s₀)) := by
    show eval (.zero .t1) s₂ = _
    rw [eval_zero, u₂.gpr, h3, hC.s3, sub_beq_zero (by have := (s₀.gpr .a1).isLt; omega_using [hfit, hr₁])]
  refine WP.ite (decide ((pos s₀ + c) % rt s₀ + n = rt s₀)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.seq (wp_li (by decide) fun s₃ u₃ => WP.block_nil ?_)
    obtain sp₃ : s₃.sp = B s₀ := by rw [u₃.sp, hC₂.sp]
    refine permuteAt_ok (st := st s₀) (by rw [u₃.other _ (by decide), hC₂.s2])
      (by rw [sp₃]; exact hk.B_al) (by rw [sp₃]; exact hk.B_1120)
      (by rw [sp₃]; exact (hp.k_st.sub_left hk.scr_sub).symm)
      (by rw [sp₃]; exact hp.k_st.sub_left hk.below_sub)
      (by
        rw [u₃.wr, hC₂.wr]
        apply Covers.of_sub
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr
        exact ⟨stR s₀, by simp, 0, by simp, by simp⟩)
      fun s₄ rd₄ wr₄ sp₄ cs₄ f₄ e₄ => ?_
    rw [sp₃] at f₄
    have hm₃ : s₃.mem = s₂.mem := u₃.mem
    refine ⟨⟨hC₂.c_le, by rw [rd₄, u₃.rd, hC₂.rd], by rw [wr₄, u₃.wr, hC₂.wr], by rw [sp₄, sp₃],
      by rw [cs₄ _ (by decide), u₃.other _ (by decide), hC₂.s2],
      by rw [cs₄ _ (by decide), u₃.other _ (by decide), hC₂.s3],
      by rw [cs₄ _ (by decide), u₃.other _ (by decide), hC₂.s5],
      by rw [cs₄ _ (by decide), u₃.other _ (by decide), hC₂.s6], ?_, ?_,
      fun r hr => by rw [cs₄ _ (keep_preserved r hr), u₃.other _ (by revert r; decide),
        hC₂.untouched r hr]⟩, ?_, fun msg hm => ?_⟩
    · rw [hm₃] at f₄
      exact hC₂.frame.trans (f₄.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨stR s₀, by simp, fun _ h => h⟩
        · exact ⟨KR s₀, by simp, hk.scr_sub⟩
        · exact ⟨KR s₀, by simp, hk.below_sub⟩)
    · rw [hm₃] at f₄
      refine hC₂.saved.frame (fun d h₂ r hr => ?_) f₄
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.k_st.sub_left (hk.slot_sub h₂)
      · exact hk.slot_scr h₂
      · exact hk.slot_below h₂
    · rw [cs₄ _ (by decide), u₃.gpr, hpc, ite_eq_left_of_eq_true _ _ (eq_true hb)]
    · rw [e₄, hm₃, u₂.mem, hrep msg hm, ite_eq_left_of_eq_true _ _ (eq_true hb)]
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.block_nil { hC₂ with s4 := ?_, repr := fun msg hm => ?_ }
    · rw [u₂.other _ (by decide), h3, hpc, ite_eq_right_of_eq_false _ _ (eq_false hb)]
    · rw [u₂.mem, hrep msg hm, ite_eq_right_of_eq_false _ _ (eq_false hb)]

theorem body_ok {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State}
    (hI : Inv s₀ c s) :
    WP isa absorbBody s fun s' => ∃ c', c < c' ∧ c' ≤ len s₀ ∧ Inv s₀ c' s' := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain h8 := rate_mod8 hp.rate
  obtain hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  obtain hl := len_lt s₀
  unfold absorbBody
  refine WP.seq (WP.mono (laneCheck_ok hI.s2 hI.s4 hI.s6 (by omega_using [hr₁, hj]) (by omega_using [hl]))
    fun s₇ ⟨oth, ht2, m₇, rd₇, wr₇, sp₇, hz, hd⟩ => ?_)
  obtain o : ∀ r, r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t3 ∧ r ≠ .t4 → s₇.gpr r = s.gpr r :=
    fun r h => oth r h.1 h.2.1 h.2.2.1 h.2.2.2
  obtain hI₇ : Inv s₀ c s₇ :=
    { c_le := hI.c_le, rd := rd₇.trans hI.rd, wr := wr₇.trans hI.wr, sp := sp₇.trans hI.sp
      s2 := (o _ (by decide)).trans hI.s2, s3 := (o _ (by decide)).trans hI.s3
      s5 := (o _ (by decide)).trans hI.s5, s6 := (o _ (by decide)).trans hI.s6
      frame := m₇ ▸ hI.frame, saved := m₇ ▸ hI.saved
      untouched := fun r hr => (o r (by revert r; decide)).trans (hI.untouched r hr)
      s4 := (o _ (by decide)).trans hI.s4
      repr := fun msg hm => by rw [m₇]; exact hI.repr msg hm }
  refine WP.seq (WP.mono (Q := fun (s₁ : State) => ∃ n, 0 < n ∧ (pos s₀ + c) % rt s₀ + n ≤ rt s₀ ∧
      c + n ≤ len s₀ ∧ Common s₀ (c + n) s₁ ∧
      s₁.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + n) ∧
      stateAt s₁.mem (st s₀) = xorAt (stateAt s₇.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) n)) ?_
    fun s₁ ⟨n, hn, hfit, hcn, hC, h3, hst⟩ => WP.mono (full_ok hp hn hfit hI₇ hC h3 hst)
      fun s' h => ⟨c + n, by omega_using [hn], hcn, h⟩)
  unfold step
  refine WP.ite (s₇.gpr .t1 == 0) (by show eval (.zero .t1) s₇ = _; rw [eval_zero])
    (fun hb => ?_) (fun _ => ?_)
  · obtain ⟨m8, al, l8⟩ := hz (by simpa using hb)
    obtain lane : ∀ b : Bool, (b = true → (dp s₀ + BitVec.ofNat 64 c).toNat % 8 = 0) →
        WP isa (.block (absorbLane b)) s₇ fun s₁ => ∃ n, 0 < n ∧ (pos s₀ + c) % rt s₀ + n ≤ rt s₀ ∧
          c + n ≤ len s₀ ∧ Common s₀ (c + n) s₁ ∧
          s₁.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + n) ∧
          stateAt s₁.mem (st s₀) = xorAt (stateAt s₇.mem (st s₀)) ((pos s₀ + c) % rt s₀)
            (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) n) := fun b hb =>
      WP.mono (body_word hp (by omega_using [l8]) hI₇ m8 ht2 al hb)
        fun s₁ ⟨hC, h3, hst⟩ => ⟨8, by decide, by omega_using [h8, hj, m8], by omega_using [l8], hC, h3, hst⟩
    refine WP.ite (s₇.gpr .t4 == 0) (by show eval (.zero .t4) s₇ = _; rw [eval_zero])
      (fun hb4 => lane true fun _ => ?_) (fun _ => lane false fun h => absurd h (by decide))
    rw [← hI.s5]; exact hd (by simpa using hb4)
  · refine WP.mono (body_byte hp hc hI₇) fun s₁ ⟨hC, h3, hst⟩ =>
      ⟨1, by decide, by omega_using [hj], by omega_using [hc], hC, h3, ?_⟩
    rw [hst]
    simp [bytesAt, xorAt_single]

/-! ## The whole function -/

theorem preserved_split : ∀ r ∈ preserved, r ∈ saved.map Prod.fst ∨ r ∈ untouched := by decide

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa absorb s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha3.absorbRISCV64.post s₀ s' := by
  have hk := hp.stk
  obtain hl := len_lt s₀
  have ⟨hr₀, _⟩ := hp.rt_pos
  unfold absorb withLoop frameBytes
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have := hk.sp; omega_using [this]) ?_
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ hI => ?_)
  refine WP.seq (WP.mono (Q := Inv s₀ (len s₀)) ?_ fun s₂ hI₂ => ?_)
  · refine WP.ite (decide (len s₀ = 0))
      (by show eval (.zero .s6) s₁ = _
          rw [eval_zero, hI.s6, Nat.sub_zero, ofNat_beq_zero (by omega_using [hl])])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      exact WP.block_nil (hb ▸ hI)
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.loop (M := isa) (fun n s => ∃ c, n = len s₀ - c ∧ c < len s₀ ∧ Inv s₀ c s) ?_
        (len s₀) s₁ ⟨0, rfl, by omega_using [hb], hI⟩
      rintro n s ⟨c, rfl, hcl, hI⟩
      refine WP.mono (body_ok hp hcl hI) fun s' ⟨c', hcc, hcl', hI'⟩ => ?_
      obtain hz : isa.eval (.nonzero .s6) s' = some (decide (len s₀ - c' ≠ 0)) := by
        show eval (.nonzero .s6) s' = _
        rw [eval_nonzero, hI'.s6, bne, ofNat_beq_zero (by omega_using [hl])]
        simp
      by_cases he : len s₀ - c' = 0
      · refine .inl ⟨by rw [hz]; simp [he], ?_⟩
        rwa [show c' = len s₀ by omega_using [hcl', he]] at hI'
      · exact .inr ⟨by rw [hz]; simp [he], len s₀ - c', by omega_using [hcl, hcc], c', rfl, by omega_using [he], hI'⟩
  · refine epilogue_ok (g := s₀.gpr) (by rw [hI₂.sp]; exact hk.B_al)
      (fun d hd₂ => by
        rw [hI₂.rd, hI₂.wr, hI₂.sp]
        exact ⟨BR s₀, by simp, Offset.contains_base _ (by omega_using [hd₂]) (by omega_using [hd₂])⟩)
      (by rw [hI₂.sp]; exact hI₂.saved) fun s' h0 hsv hother hm hrd hwr hsp mL _ fl => ?_
    refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun msg hR hpm => ?_, ?_⟩
    · show s'.gpr r = _
      rcases preserved_split r hr with h | h
      · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp h
        exact hsv p hp'
      · rw [hother r (by revert r; decide) (by revert r; decide) (by revert r; decide)]
        exact hI₂.untouched r h
    · show s'.sp + BitVec.ofNat 64 48 = s₀.sp
      rw [hsp, hI₂.sp, BitVec.sub_add_cancel]
    · exact hsv (.ra, 0) (by decide)
    · -- The `free` loses the frame's bytes, which lie apart from the state.
      rw [Proof.Sha3.repr_iff, Proof.Sha3.stateAt_congr (m := s'.mem) fun i hi =>
        lost_byte fl (R := stR s₀) (hp.k_st.symm.sub_right (Offset.sub_below _ (by decide) (by decide))) hi, hm]
      exact hI₂.repr msg ⟨hR, hpm⟩
    · simp only [freed]
      rw [h0, hI₂.s4, toNat_ofNat_lt (by have := Nat.mod_lt (pos s₀ + len s₀) hr₀; omega_arith)]

end VG.Proof.Sha3.RISCV64.Stream.Absorb

end

end

/-!
# The SHA-3 sponge on RISC-V: `absorbWs`

`absorb` (`Absorb.lean`) with its working space passed in `scratch` (`a5`)
rather than in a frame on the stack: the same loop, a lane (`body_word`) or
a byte (`body_byte`) at a time, with the registers saved in `scratch`
(`Spill`) and the permutation's scratch space at its start (`permuteAtWs`).
The stack it uses is the permutation's frame, the 608 bytes below the stack
pointer.
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64.Stream.AbsorbWs

open VG VG.RISCV64 VG.RISCV64.Wp VG.Impl.Sha3.RISCV64.Stream
open VG.Proof.Sha3.RISCV64 VG.Proof.Sha3.RISCV64.Stream
open VG.Proof.Sha3.RISCV64.Stream.Absorb (st rt pos dp len stR dR D Msg len_lt bytesAt_add rate_mod8
  stateAt_write_lane)
open VG.Proof.Sha3 (Rep rep_append xorByte stateAt_xorByte ofNat_beq_zero sub_beq_zero sub_ofNat
  xor_setWidth writeW8_apply bytesAt_succ bytesAt_length toNat_ofNat_lt xorAt xorAt_single byteOf_xorAt
  byteOf_stateAt writeW64_byte)
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)

/-! ## The precondition -/

section
variable (s₀ : State)

/-- The working space. -/
abbrev ws : Addr := s₀.gpr .a5
abbrev wsR : Region := ⟨ws s₀, 640⟩
/-- Its first 512 bytes, the permutation's scratch space. -/
abbrev scrR : Region := ⟨ws s₀, 512⟩
/-- The slots of the saved registers in it. -/
abbrev slotR : Region := ⟨ws s₀ + BitVec.ofNat 64 512, 56⟩
/-- The permutation's frame, below the stack pointer. -/
abbrev PR : Region := ⟨s₀.sp - 608, 608⟩

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [stR s₀, wsR s₀]
  st_ws : (stR s₀).Disjoint (wsR s₀)
  d_st : (dR s₀).Disjoint (stR s₀)
  d_ws : (dR s₀).Disjoint (wsR s₀)
  ws_al : (ws s₀).toNat % 8 = 0
  ws_fit : (ws s₀).toNat + 640 ≤ 2 ^ 64
  sp_al : s₀.sp.toNat % 16 = 0
  sp : 608 ≤ s₀.sp.toNat
  p_st : (PR s₀).Disjoint (stR s₀)
  p_d : (PR s₀).Disjoint (dR s₀)
  p_ws : (PR s₀).Disjoint (wsR s₀)
  rate : rt s₀ ∈ rates
  pos_lt : pos s₀ < rt s₀

theorem pre_of {s₀ : State} (h : Proof.Sha3.absorbWsRISCV64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem Pre.rt_pos {s₀ : State} (hp : Pre s₀) : 0 < rt s₀ ∧ rt s₀ ≤ 168 := by
  obtain h := Proof.Sha3.rate_bounds hp.rate
  omega_using [h]

theorem savedWs_fits : Spill.Fits savedWs := by decide

theorem savedWs_bound : ∀ p ∈ savedWs, 512 ≤ p.2 ∧ p.2 + 8 ≤ 512 + 56 := by decide

theorem slot_ws (s₀ : State) : Region.Sub (slotR s₀) (wsR s₀) := Offset.sub_base _ (by omega_using [])

theorem scr_ws (s₀ : State) : Region.Sub (scrR s₀) (wsR s₀) := Region.sub_prefix (by omega_using [])

theorem slot_scr (s₀ : State) : (slotR s₀).Disjoint (scrR s₀) :=
  Offset.disjoint_base _ (by omega_using []) (by omega_using [])

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem slot_st : (slotR s₀).Disjoint (stR s₀) := hp.st_ws.symm.sub_left (slot_ws s₀)

theorem slot_p : (slotR s₀).Disjoint (PR s₀) := hp.p_ws.symm.sub_left (slot_ws s₀)

theorem st_scr : (stR s₀).Disjoint (scrR s₀) := (hp.st_ws.symm.sub_left (scr_ws s₀)).symm

theorem p_scr : (PR s₀).Disjoint (scrR s₀) := (hp.p_ws.symm.sub_left (scr_ws s₀)).symm

end Pre

/-- The callee-saved registers our code never writes. -/
abbrev untouched : List Reg := [.s0, .s1, .s8, .s9, .s10, .s11]

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = [dR s₀]
  wr : s.wr = [stR s₀, wsR s₀]
  sp : s.sp = s₀.sp
  s2 : s.gpr .s2 = st s₀
  s3 : s.gpr .s3 = s₀.gpr .a1
  s5 : s.gpr .s5 = dp s₀ + BitVec.ofNat 64 c
  s6 : s.gpr .s6 = BitVec.ofNat 64 (len s₀ - c)
  s7 : s.gpr .s7 = ws s₀
  frame : Frame [stR s₀, wsR s₀, PR s₀] s₀.mem s.mem
  saved : Spill.Saved (ws s₀) s₀.gpr savedWs s.mem
  untouched : ∀ r ∈ untouched, s.gpr r = s₀.gpr r

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv (s₀ : State) (c : Nat) (s : State) : Prop extends Common s₀ c s where
  s4 : s.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀)
  repr : ∀ msg, Msg s₀ msg → stateAt s.mem (st s₀) = Rep (rt s₀) (msg ++ Absorb.D s₀ c)

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Common s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dp s₀ + BitVec.ofNat 64 i) = s₀.mem (dp s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_ws, hp.p_d.symm⟩)
    (Nat.le_of_lt (len_lt s₀)) hi

/-- A write within the state keeps the saved registers. -/
theorem Common.saved_st {s₀ : State} (hp : Pre s₀) {m m' : Mem}
    (h : Spill.Saved (ws s₀) s₀.gpr savedWs m) (hf : Frame [stR s₀] m m') :
    Spill.Saved (ws s₀) s₀.gpr savedWs m' :=
  h.frame_in savedWs_bound hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.slot_st

/-! ## The prologue -/

theorem setupWs_eq : setupWs = mov .t0 .a5 :: (Spill.saveCode .t0 savedWs ++
    [mov .s2 .a0, mov .s3 .a1, mov .s4 .a2, mov .s5 .a3, mov .s6 .a4, mov .s7 .a5]) := rfl

theorem savedWs_ne_t0 : ∀ p ∈ savedWs, p.1 ≠ .t0 := by decide

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block setupWs) s₀ (Inv s₀ 0) := by
  rw [setupWs_eq]
  refine wp_mv fun s₁ u₁ => ?_
  have g1 : s₁.gpr .t0 = ws s₀ := u₁.gpr
  refine Spill.save_ok (b := .t0) (by rw [g1]; exact hp.ws_al) (fun p hp' => savedWs_fits.1 p hp')
    (fun p hp' => ?_) ?_
  · have := savedWs_bound p hp'
    rw [u₁.wr, hp.wr, g1]
    exact ⟨wsR s₀, by simp, Offset.contains_base _ (by omega_using [this]) (by omega_using [this])⟩
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ =>
    wp_mv fun s₆ u₆ => wp_mv fun s₇ u₇ => WP.block_nil ?_
  obtain hm : s₇.mem = Spill.saveMem s₀.mem (ws s₀) s₁.gpr savedWs := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, g1, u₁.mem]
  obtain hf : Frame [slotR s₀] s₀.mem s₇.mem := by
    rw [hm]; exact Spill.saveMem_frame savedWs_bound (by omega_using [hp.ws_fit]) _ _ _
  obtain hs : Spill.Saved (ws s₀) s₀.gpr savedWs s₇.mem := fun p hp' => by
    rw [hm, Spill.saveMem_saved savedWs_fits _ _ _ p hp', u₁.other _ (savedWs_ne_t0 p hp')]
  obtain o : ∀ r, r ≠ .t0 →
      ({ s₁ with mem := Spill.saveMem s₁.mem (s₁.gpr .t0) s₁.gpr savedWs } : State).gpr r = s₀.gpr r :=
    u₁.other
  refine ⟨⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hf.sub fun r hr => ⟨wsR s₀, by simp, by simp only [List.mem_singleton] at hr; subst hr; exact slot_ws s₀⟩,
      hs, fun r hr => ?_⟩, ?_, fun msg ⟨hst, _⟩ => ?_⟩
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]; exact hp.rd
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hp.wr
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, o _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), o _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), o _ (by decide)]; simp
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), o _ (by decide), Nat.sub_zero]; simp [len]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), o _ (by decide)]
  · have : r ≠ .s2 ∧ r ≠ .s3 ∧ r ≠ .s4 ∧ r ≠ .s5 ∧ r ≠ .s6 ∧ r ≠ .s7 ∧ r ≠ .t0 := by
      revert r; decide
    rw [u₇.other _ this.2.2.2.2.2.1, u₆.other _ this.2.2.2.2.1, u₅.other _ this.2.2.2.1,
      u₄.other _ this.2.2.1, u₃.other _ this.2.1, u₂.other _ this.1, o _ this.2.2.2.2.2.2]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), o _ (by decide), Nat.add_zero,
      Nat.mod_eq_of_lt hp.pos_lt]
    simp [pos]
  · rw [show Absorb.D s₀ 0 = [] by simp [Absorb.D, bytesAt], List.append_nil, ← hst]
    exact Proof.Sha3.stateAt_congr fun i hi =>
      hf.bytes (R := stR s₀) (by simpa using hp.slot_st.symm) (by show 200 ≤ 2 ^ 64; decide) hi

/-! ## One iteration -/

/-- The byte at position `j` XORed in. -/
theorem body_byte {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State}
    (hI : Inv s₀ c s) :
    WP isa (.block absorbByte) s fun s' =>
      Common s₀ (c + 1) s' ∧ s'.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + 1) ∧
      stateAt s'.mem (st s₀) = xorByte (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (s₀.mem (dp s₀ + BitVec.ofNat 64 c)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain hl := len_lt s₀
  obtain hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  generalize hjd : (pos s₀ + c) % rt s₀ = j at hj ⊢
  obtain hr3 : s.gpr .s4 = BitVec.ofNat 64 j := by rw [hI.s4, hjd]
  obtain hsin : ∀ rs : List Region, stR s₀ ∈ rs → InRegions rs (st s₀ + BitVec.ofNat 64 j) 1 :=
    fun rs h => ⟨stR s₀, h, Offset.contains_base _ (by omega_using [hr₁, hj]) (by omega_using [hr₁, hj])⟩
  refine wp_lbu (t := .t1) (a := dp s₀ + BitVec.ofNat 64 c) (by decide) (by rw [hI.s5]; simp)
    ⟨dR s₀, by simp [hI.rd], Offset.contains_base _ (by omega_using [hc]) (by omega_using [hc, hl])⟩ fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ => ?_
  obtain ea : s₂.gpr .t2 + BitVec.ofNat 64 0 = st s₀ + BitVec.ofNat 64 j := by
    rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), hI.s2, hr3]; simp
  refine wp_lbu (t := .t3) (a := st s₀ + BitVec.ofNat 64 j) (by decide) ea
    (hsin _ (by simp [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hI.rd, hI.wr])) fun s₃ u₃ => ?_
  refine wp_xor fun s₄ u₄ => ?_
  refine wp_sb (a := st s₀ + BitVec.ofNat 64 j) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide)]; exact ea)
    (hsin _ (by simp [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr])) fun s₅ g₅ => ?_
  refine wp_addi (by decide) fun s₆ u₆ => wp_addi (by decide) fun s₇ u₇ =>
    wp_subi (imm := 1) (by decide) fun s₈ u₈ => WP.block_nil ?_
  obtain hv : (s₄.gpr .t1).setWidth 8 =
      s₀.mem (dp s₀ + BitVec.ofNat 64 c) ^^^ s.mem (st s₀ + BitVec.ofNat 64 j) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, u₃.gpr, u₂.mem, u₁.mem,
      xor_setWidth, hI.data hp hc]
  obtain hm₈ : s₈.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 j)
      (s₀.mem (dp s₀ + BitVec.ofNat 64 c) ^^^ s.mem (st s₀ + BitVec.ofNat 64 j)) := by
    rw [u₈.mem, u₇.mem, u₆.mem, g₅.mem, hv, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain hf : Frame [stR s₀] s.mem s₈.mem := by
    rw [hm₈]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using [hr₁, hj]) (by omega_using [hr₁, hj]))
  obtain g : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .s5 → r ≠ .s4 → r ≠ .s6 →
      s₈.gpr r = s.gpr r := fun r h1 h2 h3 h4 h33 h5 => by
    rw [u₈.other r h5, u₇.other r h33, u₆.other r h4, g₅.gpr, u₄.other r h1, u₃.other r h3,
      u₂.other r h2, u₁.other r h1]
  obtain h3 : s₈.gpr .s4 = BitVec.ofNat 64 (j + 1) := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hr3, ← BitVec.ofNat_add]
  refine ⟨⟨by omega_using [hc], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩, h3, ?_⟩
  · rw [u₈.rd, u₇.rd, u₆.rd, g₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₈.wr, u₇.wr, u₆.wr, g₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [u₈.sp, u₇.sp, u₆.sp, g₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp]
  · rw [g .s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.s2]
  · rw [g .s3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.s3]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.s5, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.s6, sub_ofNat (by omega_using [hc]), Nat.sub_sub]
  · rw [g .s7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.s7]
  · exact hI.frame.trans (hf.mono (by simp))
  · exact Common.saved_st hp hI.saved hf
  · have hne : r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t3 ∧ r ≠ .s5 ∧ r ≠ .s4 ∧ r ≠ .s6 := by revert r; decide
    rw [g r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2]
    exact hI.untouched r hr
  · refine stateAt_xorByte (by omega_using [hr₁, hj]) ?_ fun i hi hij => ?_
    · rw [hm₈, writeW8_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl), BitVec.xor_comm]
    · rw [hm₈, writeW8_apply, ite_eq_right_of_eq_false _ _
        (eq_false (VG.Proof.Sha3.ne_of_lt200 hi (by omega_using [hr₁, hj]) hij))]

/-- The lane of data at `c` XORed into the lane at position `j`, both
aligned. -/
theorem body_word {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c + 8 ≤ len s₀) {s : State}
    (hI : Inv s₀ c s) (hj8 : (pos s₀ + c) % rt s₀ % 8 = 0)
    (ht2 : s.gpr .t2 = st s₀ + BitVec.ofNat 64 ((pos s₀ + c) % rt s₀))
    (hal : (st s₀ + BitVec.ofNat 64 ((pos s₀ + c) % rt s₀)).toNat % 8 = 0)
    {al : Bool} (hdal : al = true → (dp s₀ + BitVec.ofNat 64 c).toNat % 8 = 0) :
    WP isa (.block (absorbLane al)) s fun s' =>
      Common s₀ (c + 8) s' ∧ s'.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + 8) ∧
      stateAt s'.mem (st s₀) = xorAt (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) 8) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hl := len_lt s₀
  have h8 := rate_mod8 hp.rate
  have hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  generalize hjd : (pos s₀ + c) % rt s₀ = j at hj hj8 ht2 hal ⊢
  have hj' : j + 8 ≤ rt s₀ := by omega_using [h8, hj, hj8]
  have hr3 : s.gpr .s4 = BitVec.ofNat 64 j := by rw [hI.s4, hjd]
  have hsin : ∀ rs : List Region, stR s₀ ∈ rs → InRegions rs (st s₀ + BitVec.ofNat 64 j) 8 :=
    fun rs h => ⟨stR s₀, h, Offset.contains_base _ (by omega_using [hr₁, hj]) (by omega_using [hr₁, hj])⟩
  unfold absorbLane
  refine loadData_ok (a := dp s₀ + BitVec.ofNat 64 c) (by rw [hI.s5]) hdal
    ⟨dR s₀, by simp [hI.rd], Offset.contains_base _ (by omega_using [hc]) (by omega_using [hc, hl])⟩ fun s₁ u₁ => ?_
  refine wp_ld (t := .t3) (a := st s₀ + BitVec.ofNat 64 j) (by decide)
    (by rw [u₁.other _ (by decide) (by decide) (by decide), ht2]; simp) hal
    (hsin _ (by simp [u₁.rd, u₁.wr, hI.rd, hI.wr])) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_sd (a := st s₀ + BitVec.ofNat 64 j) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide) (by decide) (by decide), ht2]; simp) hal
    (hsin _ (by simp [u₃.wr, u₂.wr, u₁.wr, hI.wr])) fun s₄ g₄ => ?_
  refine wp_addi (by decide) fun s₅ u₅ => wp_addi (by decide) fun s₆ u₆ =>
    wp_subi (imm := 8) (by decide) fun s₇ u₇ => WP.block_nil ?_
  have hv : s₃.gpr .t1 = s.mem.readW (dp s₀ + BitVec.ofNat 64 c) 64 ^^^
      s.mem.readW (st s₀ + BitVec.ofNat 64 j) 64 := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem]
  have hm₇ : s₇.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 j) (s₃.gpr .t1) := by
    rw [u₇.mem, u₆.mem, u₅.mem, g₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hf : Frame [stR s₀] s.mem s₇.mem := by
    rw [hm₇]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using [hr₁, hj]) (by omega_using [hr₁, hj]))
  have g : ∀ r, r ≠ .t1 → r ≠ .t3 → r ≠ .s5 → r ≠ .s4 → r ≠ .s6 → r ≠ .t4 →
      s₇.gpr r = s.gpr r := fun r h1 h3 h4 h33 h5 h6 => by
    rw [u₇.other r h5, u₆.other r h33, u₅.other r h4, g₄.gpr, u₃.other r h1, u₂.other r h3,
      u₁.other r h1 h3 h6]
  have h3 : s₇.gpr .s4 = BitVec.ofNat 64 (j + 8) := by
    rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide) (by decide) (by decide), hr3,
      ← BitVec.ofNat_add]
  refine ⟨⟨by omega_using [hc], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩, h3, ?_⟩
  · rw [u₇.rd, u₆.rd, u₅.rd, g₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [u₇.sp, u₆.sp, u₅.sp, g₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp]
  · rw [g .s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.s2]
  · rw [g .s3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.s3]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide) (by decide) (by decide), hI.s5,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide) (by decide) (by decide), hI.s6,
      sub_ofNat (by omega_using [hc]), Nat.sub_sub]
  · rw [g .s7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.s7]
  · exact hI.frame.trans (hf.mono (by simp))
  · exact Common.saved_st hp hI.saved hf
  · have hne : r ≠ .t1 ∧ r ≠ .t3 ∧ r ≠ .s5 ∧ r ≠ .s4 ∧ r ≠ .s6 ∧ r ≠ .t4 := by revert r; decide
    rw [g r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2]
    exact hI.untouched r hr
  · rw [hm₇]
    refine stateAt_write_lane (by omega_using [hr₁, hj]) (bytesAt_length _ _ _) fun d hd => ?_
    rw [hv, BitVec.extractLsb'_xor, Mem.readW, Mem.readW, BitVec.setWidth_eq, BitVec.setWidth_eq,
      Mem.extractLsb'_read _ _ (show d < 64 / 8 by omega_using [hd]),
      Mem.extractLsb'_read _ _ (show d < 64 / 8 by omega_using [hd]),
      BitVec.xor_comm, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 1
    simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hd,
      Option.map_some, Option.getD_some]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hI.data hp (by omega_using [hc, hd])]

theorem keep_preserved : ∀ r ∈ untouched, r ∈ preserved := by decide

theorem s7_preserved : Reg.s7 ∈ preserved := by decide

/-- The permutation if the block is complete, after `n` bytes of data that
fit in it. -/
theorem full_ok {s₀ : State} (hp : Pre s₀) {c n : Nat} (hn : 0 < n)
    (hfit : (pos s₀ + c) % rt s₀ + n ≤ rt s₀) {s s₁ : State}
    (hI : Inv s₀ c s) (hC : Common s₀ (c + n) s₁)
    (h3 : s₁.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + n))
    (hst : stateAt s₁.mem (st s₀) = xorAt (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) n)) :
    WP isa permuteIfFullWs s₁ (Inv s₀ (c + n)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain hlen : ∀ msg, Msg s₀ msg → (msg ++ Absorb.D s₀ c).length % rt s₀ = (pos s₀ + c) % rt s₀ :=
    fun msg ⟨_, hpm⟩ => by rw [List.length_append, bytesAt_length, hpm, Nat.mod_add_mod]
  obtain hrep : ∀ msg, Msg s₀ msg → Rep (rt s₀) (msg ++ Absorb.D s₀ (c + n)) =
      if (pos s₀ + c) % rt s₀ + n = rt s₀ then keccakF (stateAt s₁.mem (st s₀))
      else stateAt s₁.mem (st s₀) := fun msg hm => by
    rw [Absorb.D, bytesAt_add, ← List.append_assoc, rep_append hr₀ (by omega_using [hr₁]) _ _
      (by rw [bytesAt_length]; exact hn) (by rw [bytesAt_length, hlen msg hm]; exact hfit),
      hlen msg hm, bytesAt_length, hst, hI.repr msg hm]
  obtain hpc : (pos s₀ + (c + n)) % rt s₀ = if (pos s₀ + c) % rt s₀ + n = rt s₀ then 0
      else (pos s₀ + c) % rt s₀ + n := by
    obtain e := Nat.div_add_mod (pos s₀ + c) (rt s₀)
    rw [show pos s₀ + (c + n) = (pos s₀ + c) + n by omega_using []]
    generalize (pos s₀ + c) % rt s₀ = j at e hfit ⊢
    generalize (pos s₀ + c) / rt s₀ = q at e
    rw [← e]
    split
    · rw [Nat.add_assoc, ‹j + n = rt s₀›, ← Nat.mul_succ, Nat.mul_mod_right]
    · rw [Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega_arith)]
  unfold permuteIfFullWs
  refine WP.seq (wp_sub fun s₂ u₂ => WP.block_nil ?_)
  obtain hC₂ : Common s₀ (c + n) s₂ :=
    { hC with rd := u₂.rd.trans hC.rd, wr := u₂.wr.trans hC.wr, sp := u₂.sp.trans hC.sp
              s2 := (u₂.other _ (by decide)).trans hC.s2, s3 := (u₂.other _ (by decide)).trans hC.s3
              s5 := (u₂.other _ (by decide)).trans hC.s5, s6 := (u₂.other _ (by decide)).trans hC.s6
              s7 := (u₂.other _ (by decide)).trans hC.s7
              frame := u₂.mem ▸ hC.frame, saved := u₂.mem ▸ hC.saved
              untouched := fun r hr => (u₂.other r (by revert r; decide)).trans (hC.untouched r hr) }
  obtain hz : isa.eval (.zero .t1) s₂ = some (decide ((pos s₀ + c) % rt s₀ + n = rt s₀)) := by
    show eval (.zero .t1) s₂ = _
    rw [eval_zero, u₂.gpr, h3, hC.s3, sub_beq_zero (by have := (s₀.gpr .a1).isLt; omega_using [hfit, hr₁])]
  refine WP.ite (decide ((pos s₀ + c) % rt s₀ + n = rt s₀)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.seq (wp_li (by decide) fun s₃ u₃ => WP.block_nil ?_)
    obtain sp₃ : s₃.sp = s₀.sp := by rw [u₃.sp, hC₂.sp]
    refine permuteAtWs_ok (st := st s₀) (w := ws s₀) (by rw [u₃.other _ (by decide), hC₂.s2])
      (by rw [u₃.other _ (by decide), hC₂.s7])
      (by rw [sp₃]; exact hp.sp_al) (by rw [sp₃]; exact hp.sp) hp.st_scr
      (by rw [sp₃]; exact hp.p_st) (by rw [sp₃]; exact hp.p_scr)
      (by
        rw [u₃.wr, hC₂.wr]
        apply Covers.of_sub
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
        · exact ⟨wsR s₀, by simp, 0, by simp, by simp⟩)
      fun s₄ rd₄ wr₄ sp₄ cs₄ f₄ e₄ => ?_
    rw [sp₃] at f₄
    have hm₃ : s₃.mem = s₂.mem := u₃.mem
    rw [hm₃] at f₄
    refine ⟨⟨hC₂.c_le, by rw [rd₄, u₃.rd, hC₂.rd], by rw [wr₄, u₃.wr, hC₂.wr], by rw [sp₄, sp₃],
      by rw [cs₄ _ (by decide), u₃.other _ (by decide), hC₂.s2],
      by rw [cs₄ _ (by decide), u₃.other _ (by decide), hC₂.s3],
      by rw [cs₄ _ (by decide), u₃.other _ (by decide), hC₂.s5],
      by rw [cs₄ _ (by decide), u₃.other _ (by decide), hC₂.s6],
      by rw [cs₄ _ s7_preserved, u₃.other _ (by decide), hC₂.s7], ?_, ?_,
      fun r hr => by rw [cs₄ _ (keep_preserved r hr), u₃.other _ (by revert r; decide),
        hC₂.untouched r hr]⟩, ?_, fun msg hm => ?_⟩
    · exact hC₂.frame.trans (f₄.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨stR s₀, by simp, fun _ h => h⟩
        · exact ⟨wsR s₀, by simp, scr_ws s₀⟩
        · exact ⟨PR s₀, by simp, fun _ h => h⟩)
    · refine hC₂.saved.frame_in savedWs_bound f₄ fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.slot_st
      · exact slot_scr s₀
      · exact hp.slot_p
    · rw [cs₄ _ (by decide), u₃.gpr, hpc, ite_eq_left_of_eq_true _ _ (eq_true hb)]
    · rw [e₄, hm₃, u₂.mem, hrep msg hm, ite_eq_left_of_eq_true _ _ (eq_true hb)]
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.block_nil { hC₂ with s4 := ?_, repr := fun msg hm => ?_ }
    · rw [u₂.other _ (by decide), h3, hpc, ite_eq_right_of_eq_false _ _ (eq_false hb)]
    · rw [u₂.mem, hrep msg hm, ite_eq_right_of_eq_false _ _ (eq_false hb)]

theorem body_ok {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State}
    (hI : Inv s₀ c s) :
    WP isa absorbWsBody s fun s' => ∃ c', c < c' ∧ c' ≤ len s₀ ∧ Inv s₀ c' s' := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain h8 := rate_mod8 hp.rate
  obtain hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  obtain hl := len_lt s₀
  unfold absorbWsBody
  refine WP.seq (WP.mono (laneCheck_ok hI.s2 hI.s4 hI.s6 (by omega_using [hr₁, hj]) (by omega_using [hl]))
    fun s₇ ⟨oth, ht2, m₇, rd₇, wr₇, sp₇, hz, hd⟩ => ?_)
  obtain o : ∀ r, r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t3 ∧ r ≠ .t4 → s₇.gpr r = s.gpr r :=
    fun r h => oth r h.1 h.2.1 h.2.2.1 h.2.2.2
  obtain hI₇ : Inv s₀ c s₇ :=
    { c_le := hI.c_le, rd := rd₇.trans hI.rd, wr := wr₇.trans hI.wr, sp := sp₇.trans hI.sp
      s2 := (o _ (by decide)).trans hI.s2, s3 := (o _ (by decide)).trans hI.s3
      s5 := (o _ (by decide)).trans hI.s5, s6 := (o _ (by decide)).trans hI.s6
      s7 := (o _ (by decide)).trans hI.s7
      frame := m₇ ▸ hI.frame, saved := m₇ ▸ hI.saved
      untouched := fun r hr => (o r (by revert r; decide)).trans (hI.untouched r hr)
      s4 := (o _ (by decide)).trans hI.s4
      repr := fun msg hm => by rw [m₇]; exact hI.repr msg hm }
  refine WP.seq (WP.mono (Q := fun (s₁ : State) => ∃ n, 0 < n ∧ (pos s₀ + c) % rt s₀ + n ≤ rt s₀ ∧
      c + n ≤ len s₀ ∧ Common s₀ (c + n) s₁ ∧
      s₁.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + n) ∧
      stateAt s₁.mem (st s₀) = xorAt (stateAt s₇.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) n)) ?_
    fun s₁ ⟨n, hn, hfit, hcn, hC, h3, hst⟩ => WP.mono (full_ok hp hn hfit hI₇ hC h3 hst)
      fun s' h => ⟨c + n, by omega_using [hn], hcn, h⟩)
  unfold step
  refine WP.ite (s₇.gpr .t1 == 0) (by show eval (.zero .t1) s₇ = _; rw [eval_zero])
    (fun hb => ?_) (fun _ => ?_)
  · obtain ⟨m8, al, l8⟩ := hz (by simpa using hb)
    obtain lane : ∀ b : Bool, (b = true → (dp s₀ + BitVec.ofNat 64 c).toNat % 8 = 0) →
        WP isa (.block (absorbLane b)) s₇ fun s₁ => ∃ n, 0 < n ∧ (pos s₀ + c) % rt s₀ + n ≤ rt s₀ ∧
          c + n ≤ len s₀ ∧ Common s₀ (c + n) s₁ ∧
          s₁.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + n) ∧
          stateAt s₁.mem (st s₀) = xorAt (stateAt s₇.mem (st s₀)) ((pos s₀ + c) % rt s₀)
            (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) n) := fun b hb =>
      WP.mono (body_word hp (by omega_using [l8]) hI₇ m8 ht2 al hb)
        fun s₁ ⟨hC, h3, hst⟩ => ⟨8, by decide, by omega_using [h8, hj, m8], by omega_using [l8], hC, h3, hst⟩
    refine WP.ite (s₇.gpr .t4 == 0) (by show eval (.zero .t4) s₇ = _; rw [eval_zero])
      (fun hb4 => lane true fun _ => ?_) (fun _ => lane false fun h => absurd h (by decide))
    rw [← hI.s5]; exact hd (by simpa using hb4)
  · refine WP.mono (body_byte hp hc hI₇) fun s₁ ⟨hC, h3, hst⟩ =>
      ⟨1, by decide, by omega_using [hj], by omega_using [hc], hC, h3, ?_⟩
    rw [hst]
    simp [bytesAt, xorAt_single]

/-! ## The whole function -/

theorem preserved_split : ∀ r ∈ preserved, r ∈ savedWs.map Prod.fst ∨ r ∈ untouched := by decide

theorem restoreWs_eq : restoreWs = mov .t0 .s7 :: Spill.restoreCode .t0 savedWs := rfl

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa absorbWs s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha3.absorbWsRISCV64.post s₀ s' := by
  obtain hl := len_lt s₀
  have ⟨hr₀, _⟩ := hp.rt_pos
  unfold absorbWs
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ hI => ?_)
  refine WP.seq (WP.mono (Q := Inv s₀ (len s₀)) ?_ fun s₂ hI₂ => ?_)
  · refine WP.ite (decide (len s₀ = 0))
      (by show eval (.zero .s6) s₁ = _
          rw [eval_zero, hI.s6, Nat.sub_zero, ofNat_beq_zero (by omega_using [hl])])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      exact WP.block_nil (hb ▸ hI)
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.loop (M := isa) (fun n s => ∃ c, n = len s₀ - c ∧ c < len s₀ ∧ Inv s₀ c s) ?_
        (len s₀) s₁ ⟨0, rfl, by omega_using [hb], hI⟩
      rintro n s ⟨c, rfl, hcl, hI⟩
      refine WP.mono (body_ok hp hcl hI) fun s' ⟨c', hcc, hcl', hI'⟩ => ?_
      obtain hz : isa.eval (.nonzero .s6) s' = some (decide (len s₀ - c' ≠ 0)) := by
        show eval (.nonzero .s6) s' = _
        rw [eval_nonzero, hI'.s6, bne, ofNat_beq_zero (by omega_using [hl])]
        simp
      by_cases he : len s₀ - c' = 0
      · refine .inl ⟨by rw [hz]; simp [he], ?_⟩
        rwa [show c' = len s₀ by omega_using [hcl', he]] at hI'
      · exact .inr ⟨by rw [hz]; simp [he], len s₀ - c', by omega_using [hcl, hcc], c', rfl, by omega_using [he], hI'⟩
  · rw [restoreWs_eq]
    refine wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => ?_
    obtain g4 : s₄.gpr .t0 = ws s₀ := by rw [u₄.gpr, u₃.other _ (by decide), hI₂.s7]
    obtain m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
    refine WP.mono (Spill.restore_wp (B := ws s₀) hp.ws_al g4
      (fun p hp' => savedWs_fits.1 p hp') (by decide) (fun p hp' => ?_)
      (by rw [m₄]; exact hI₂.saved)) fun s' hR => ?_
    · have := savedWs_bound p hp'
      rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, hI₂.rd, hI₂.wr]
      exact ⟨wsR s₀, by simp, Offset.contains_base _ (by omega_using [this]) (by omega_using [this])⟩
    obtain a0 : s'.gpr .a0 = s₂.gpr .s4 := by
      rw [hR.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
    refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun msg hRp hpm => ?_, ?_⟩
    · rcases preserved_split r hr with h | h
      · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp h
        exact hR.gpr p hp'
      · have hne : r ∉ savedWs.map Prod.fst ∧ r ≠ .t0 ∧ r ≠ .a0 := by revert r; decide
        rw [hR.other r hne.1, u₄.other _ hne.2.1, u₃.other _ hne.2.2]
        exact hI₂.untouched r h
    · rw [hR.sp, u₄.sp, u₃.sp, hI₂.sp]
    · exact hR.gpr (.ra, 512) (by decide)
    · rw [Proof.Sha3.repr_iff, hR.mem, m₄]
      exact hI₂.repr msg ⟨hRp, hpm⟩
    · rw [a0, hI₂.s4, toNat_ofNat_lt (by have := Nat.mod_lt (pos s₀ + len s₀) hr₀; omega_arith)]

end VG.Proof.Sha3.RISCV64.Stream.AbsorbWs
