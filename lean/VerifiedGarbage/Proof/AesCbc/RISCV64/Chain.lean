module

public import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
public import VerifiedGarbage.Proof.Aes.RISCV64.ChainVerified
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
meta import VerifiedGarbage.Proof.Aes.RISCV64.ChainVerified
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Cmac.Frame

/-!
# AES on RISC-V: a call of a chain

`vg_aes_cbc_encrypt`, `vg_cmac_aes_update`, AES-CFB128 encryption, AES-OFB
and AES-CFB8 save the return address and `s1` at `sv` (`Spill.save_ok`),
keep the scratch buffer in `s1`, call a chain (`Impl.Aes.RISCV64.chain`,
`cfbChain`, `ofbChain`, `cfb8Chain`, as `chainWrap`) on their own arguments
and the first 2048 bytes of the scratch buffer, and restore the registers.

A chain `c` with the contract `k` (`ChainK out len k c`: its precondition
`framePre out len`'s, its data `len n` bytes, and its postcondition reading
only the arguments and the memory they point to) is proven once for all of
them. `wrap_wp`: from the callers' precondition (`WPre out len`, the
chain's with the scratch buffer of 2176 bytes), this meets `k` (through
`WP.call`), and keeps the callee-saved registers and the return address.
`wrap_ct`: it is constant time, the code around the call by taint tracking
(from the arguments, and then from `s1`) and the call by the chain's
`ChainK.ct`. `chain_k`: `chain out` is such a chain.
-/

@[expose] public section

namespace VG.Proof.AesCbc.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Align VG.Impl.AesCbc.RISCV64
open VG.Spec.Aes (bytesAt)

/-- The chain `c` called as `name`, with the return address and `s1` saved. -/
abbrev chainWrap (name : String) (c : Prog isa) : Prog isa :=
  .seq (.block encSave) (.seq (.call name c) (.block encRestore))

/-- The data: `len n` bytes, for the `n` in `a4`. -/
abbrev dataL (len : Nat → Nat) (s₀ : State) : Region := ⟨Dp s₀, len (N s₀)⟩

/-- The regions the chain reads: the schedule, and the data unless it writes them. -/
abbrev rdOf (out : Bool) (len : Nat → Nat) (s₀ : State) : List Region :=
  if out then [schR s₀] else [schR s₀, dataL len s₀]

/-- The regions the chain writes: the chaining value, the data if `out`, and `scr`. -/
abbrev wrOf (out : Bool) (len : Nat → Nat) (s₀ : State) (scr : Region) : List Region :=
  if out then [ivR s₀, dataL len s₀, scr] else [ivR s₀, scr]

/-- The callers' precondition: the chain's (`Proof.Aes.RISCV64.framePre out len`), with the
scratch buffer of 2176 bytes. -/
structure WPre (out : Bool) (len : Nat → Nat) (s₀ : State) : Prop where
  rd : s₀.rd = rdOf out len s₀
  wr : s₀.wr = wrOf out len s₀ (scrR s₀)
  sch_iv : (schR s₀).Disjoint (ivR s₀)
  sch_scr : (schR s₀).Disjoint (scrR s₀)
  data_iv : (dataL len s₀).Disjoint (ivR s₀)
  data_scr : (dataL len s₀).Disjoint (scrR s₀)
  iv_scr : (ivR s₀).Disjoint (scrR s₀)
  iv_wrap : (Iv s₀).toNat + 16 ≤ 2 ^ 64
  data_wrap : (Dp s₀).toNat + len (N s₀) ≤ 2 ^ 64
  scr_wrap : (S s₀).toNat + 2176 ≤ 2 ^ 64
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

/-- The public part of the chains' arguments: all of them, and the stack pointer. -/
abbrev ChPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.sp = s₂.sp

/-- The registers saved, and their offsets from `sv`. -/
abbrev chSaved : List (Reg × Nat) := [(.ra, 16), (.s1, 24)]

/-- The memory after saving them. -/
abbrev chMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (sv s₀) (saveG s₀) chSaved

/-- Their slots. -/
abbrev chSlots (s₀ : State) : Region := ⟨sv s₀ + BitVec.ofNat 64 16, 16⟩

/-- A chain `c` with the contract `k`, whose precondition is
`framePre out len`'s and whose postcondition reads only the arguments, the
memory they point to (the schedule, the chaining value and the data) and
the memory on exit: what a call of it with `WPre` needs. -/
structure ChainK (out : Bool) (len : Nat → Nat) (k : Contract isa) (c : Prog isa) : Prop where
  pre : ∀ s, Proof.Aes.RISCV64.framePre out len s → k.pre s
  pub_of : ∀ s₁ s₂, ChPub s₁ s₂ → k.pub s₁ s₂
  correct : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s'
  ct : ConstantTime isa k.pre k.pub c
  noFrames : c.noFrames = true
  post : ∀ {s₀ s t t' : State}, WPre out len s₀ →
    (∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4], s.gpr r = s₀.gpr r) → s.mem = chMem s₀ → t'.mem = t.mem →
    k.post s t → k.post s₀ t'

theorem preserved_ne {r : Reg} (hr : r ∈ preserved) : r ≠ .t0 := by
  revert hr; cases r <;> decide

theorem chSaved_bound : ∀ p ∈ chSaved, 16 ≤ p.2 ∧ p.2 + 8 ≤ 32 := by decide

theorem chMem_frame (s₀ : State) : Frame [chSlots s₀] s₀.mem (chMem s₀) :=
  Spill.saveMem_frame (lo := 16) (n := 16) chSaved_bound (by decide) _ _ _

theorem chSlots_scr (s₀ : State) : Region.Sub (chSlots s₀) (scrR s₀) := by
  have := q_lt s₀
  rw [chSlots, sv_add]; exact UPre.scr_sub (by omega)

theorem slot_scr (s₀ : State) {p : Reg × Nat} (hp : p ∈ chSaved) :
    Region.Sub ⟨sv s₀ + BitVec.ofNat 64 p.2, 8⟩ (scrR s₀) := by
  have := q_lt s₀
  have := chSaved_bound p hp
  rw [sv_add]; exact UPre.scr_sub (by omega)

theorem slot_ws {s₀ : State} {p : Reg × Nat} (hp : p ∈ chSaved) :
    Region.Disjoint ⟨sv s₀ + BitVec.ofNat 64 p.2, 8⟩ (wsR s₀) := by
  have := q_lt s₀
  have := chSaved_bound p hp
  rw [sv_add]; exact Offset.disjoint_base _ (by omega) (by omega)

/-- The blocks at `p`, unchanged by writes elsewhere. -/
theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) :
    Spec.Cmac.blocksAt m' p 16 n = Spec.Cmac.blocksAt m p 16 n := by
  simp only [Spec.Cmac.blocksAt]
  refine List.map_congr_left fun i hi => Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega)
  rw [List.mem_range] at hi
  exact (hd r hr).sub_left (Offset.sub_base _ (by omega))

theorem cov_self {r : Region} {rs : List Region} (h : r ∈ rs) :
    ∃ r' ∈ rs, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len :=
  ⟨r, h, 0, by simp, by simp⟩

theorem cov_ws {s₀ : State} {rs : List Region} (h : scrR s₀ ∈ rs) :
    ∃ r' ∈ rs, ∃ off, (wsR s₀).base = r'.base + BitVec.ofNat 64 off ∧ off + (wsR s₀).len ≤ r'.len :=
  ⟨_, h, 0, by simp, by simp⟩

section
variable {out : Bool} {len : Nat → Nat} {s₀ : State} (h : WPre out len s₀)
include h

theorem WPre.scr_mem : scrR s₀ ∈ s₀.wr := by rw [h.wr]; cases out <;> simp [wrOf]

/-- What the chain writes, outside the slots. -/
theorem WPre.slots_disj {p : Reg × Nat} (hp : p ∈ chSaved) :
    ∀ r ∈ wrOf out len s₀ (wsR s₀), Region.Disjoint ⟨sv s₀ + BitVec.ofNat 64 p.2, 8⟩ r := by
  have hi := h.iv_scr.symm.sub_left (slot_scr s₀ hp)
  have hd := h.data_scr.symm.sub_left (slot_scr s₀ hp)
  have hs := slot_ws (s₀ := s₀) hp
  intro r hr
  cases out <;> simp only [wrOf, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil,
    or_false] at hr <;> rcases hr with rfl | rfl | rfl <;> with_reducible assumption

/-- The chain's regions, within the caller's. -/
theorem WPre.covers : Covers (rdOf out len s₀ ++ wrOf out len s₀ (wsR s₀)) (s₀.rd ++ s₀.wr) := by
  rw [h.rd, h.wr]
  refine Covers.of_sub fun r hr => ?_
  cases out <;>
    simp only [rdOf, wrOf, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr <;>
    rcases hr with rfl | rfl | rfl | rfl <;> first
      | (refine cov_self ?_; simp [rdOf, wrOf]; done)
      | (refine cov_ws ?_; simp [rdOf, wrOf]; done)

theorem WPre.covers_wr : Covers (wrOf out len s₀ (wsR s₀)) s₀.wr := by
  rw [h.wr]
  refine Covers.of_sub fun r hr => ?_
  cases out <;>
    simp only [wrOf, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hr <;>
    rcases hr with rfl | rfl | rfl <;> first
      | (refine cov_self ?_; simp [wrOf]; done)
      | (refine cov_ws ?_; simp [wrOf]; done)

/-- The schedule, unchanged by the saves. -/
theorem WPre.sch_eq : bytesAt (chMem s₀) (s₀.gpr .a0) (16 * ((s₀.gpr .a1).toNat + 1)) =
    bytesAt s₀.mem (s₀.gpr .a0) (16 * ((s₀.gpr .a1).toNat + 1)) := by
  have hRb : 16 * ((s₀.gpr .a1).toNat + 1) ≤ 240 := by
    have hr : (s₀.gpr .a1).toNat = 10 ∨ (s₀.gpr .a1).toNat = 12 ∨ (s₀.gpr .a1).toNat = 14 := h.rounds
    omega
  exact Proof.Cmac.bytesAt_frame (chMem_frame s₀) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.sch_scr.sub_right (chSlots_scr s₀)).sub_left (Region.sub_prefix hRb)) (by omega)

/-- The chaining value, unchanged by the saves. -/
theorem WPre.iv_eq : bytesAt (chMem s₀) (s₀.gpr .a2) 16 = bytesAt s₀.mem (s₀.gpr .a2) 16 :=
  Proof.Cmac.bytesAt_frame (chMem_frame s₀) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.iv_scr.sub_right (chSlots_scr s₀)) (by omega)

/-- The data, unchanged by the saves. -/
theorem WPre.data_eq : bytesAt (chMem s₀) (s₀.gpr .a3) (len (s₀.gpr .a4).toNat) =
    bytesAt s₀.mem (s₀.gpr .a3) (len (s₀.gpr .a4).toNat) :=
  Proof.Cmac.bytesAt_frame (chMem_frame s₀) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.data_scr.sub_right (chSlots_scr s₀)) (by
      have : (s₀.gpr .a3).toNat + len (s₀.gpr .a4).toNat ≤ 2 ^ 64 := h.data_wrap
      omega)

end

/-- The data blocks, unchanged by the saves. -/
theorem WPre.blocks_eq {out : Bool} {s₀ : State} (h : WPre out (16 * ·) s₀) :
    Spec.Cmac.blocksAt (chMem s₀) (s₀.gpr .a3) 16 (s₀.gpr .a4).toNat =
      Spec.Cmac.blocksAt s₀.mem (s₀.gpr .a3) 16 (s₀.gpr .a4).toNat :=
  blocksAt_frame (chMem_frame s₀) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.data_scr.sub_right (chSlots_scr s₀)

/-- What saving the registers leaves. -/
structure WMid (s₀ s : State) : Prop where
  a0 : s.gpr .a0 = s₀.gpr .a0
  a1 : s.gpr .a1 = s₀.gpr .a1
  a2 : s.gpr .a2 = s₀.gpr .a2
  a3 : s.gpr .a3 = s₀.gpr .a3
  a4 : s.gpr .a4 = s₀.gpr .a4
  a5 : s.gpr .a5 = s₀.gpr .a5
  s1 : s.gpr .s1 = S s₀
  keep : ∀ r ∈ preserved, r ≠ .s1 → s.gpr r = s₀.gpr r
  mem : s.mem = chMem s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem save_wp {out : Bool} {len : Nat → Nat} {s₀ : State} (h : WPre out len s₀) :
    WP isa (.block encSave) s₀ (WMid s₀) := by
  rw [show encSave = savePtr .a5 ++ (Spill.saveCode .t0 chSaved ++ [mov .s1 .a5]) from rfl,
    WP.block_append_iff]
  refine WP.mono (savePtr_ok .a5) fun s₁ e => ?_
  subst e
  have t₀ : (s₀.write .t0 (sv s₀)).gpr .t0 = sv s₀ := RegUpd.gpr_write_self _ _ _
  have g₀ (r : Reg) (hr : r ≠ .t0) : (s₀.write .t0 (sv s₀)).gpr r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine Spill.save_ok (b := .t0) (l := chSaved) (by rw [t₀]; exact align_al _) (by decide)
    (fun p hp => ?_) ?_
  · rw [t₀]
    show InRegions s₀.wr _ 8
    have := q_lt s₀
    have := chSaved_bound p hp
    have := h.scr_wrap
    exact in_rw h.scr_mem (by rw [sv_add]; exact Offset.contains_base _ (by omega) (by omega))
  generalize ht : ({ (s₀.write .t0 (sv s₀)) with
    mem := Spill.saveMem (s₀.write .t0 (sv s₀)).mem ((s₀.write .t0 (sv s₀)).gpr .t0)
      (s₀.write .t0 (sv s₀)).gpr chSaved } : State) = t
  have memt : t.mem = chMem s₀ := by
    rw [← ht]; show Spill.saveMem _ _ _ _ = _; rw [t₀, RegUpd.mem_write]
  have gt (r : Reg) (hr : r ≠ .t0) : t.gpr r = s₀.gpr r := by rw [← ht]; exact g₀ r hr
  have rdt : t.rd = s₀.rd := by rw [← ht]; rfl
  have wrt : t.wr = s₀.wr := by rw [← ht]; rfl
  have spt : t.sp = s₀.sp := by rw [← ht]; rfl
  unfold mov
  refine wp_mv fun s₂ u₂ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr h1 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₂.other _ (by decide), gt _ (by decide)]
  · rw [u₂.other _ (by decide), gt _ (by decide)]
  · rw [u₂.other _ (by decide), gt _ (by decide)]
  · rw [u₂.other _ (by decide), gt _ (by decide)]
  · rw [u₂.other _ (by decide), gt _ (by decide)]
  · rw [u₂.other _ (by decide), gt _ (by decide)]
  · rw [u₂.gpr, gt _ (by decide)]
  · rw [u₂.other _ h1, gt _ (preserved_ne hr)]
  · rw [u₂.mem, memt]
  · rw [u₂.rd, rdt]
  · rw [u₂.wr, wrt]
  · rw [u₂.sp, spt]

/-- The chain's precondition, on entry to the call with its regions. -/
theorem WMid.chain_pre {out : Bool} {len : Nat → Nat} {s₀ s : State} (h : WPre out len s₀)
    (hm : WMid s₀ s) :
    Proof.Aes.RISCV64.framePre out len
      (s.callEntry.withRegions (rdOf out len s₀) (wrOf out len s₀ (wsR s₀))) := by
  simp only [Proof.Aes.RISCV64.framePre, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a4 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a5 ∉ linkRegs),
    hm.a0, hm.a1, hm.a2, hm.a3, hm.a4, hm.a5]
  refine ⟨?_, h.sch_iv, h.sch_scr.sub_right wsR_sub, h.data_iv, h.data_scr.sub_right wsR_sub,
    h.iv_scr.sub_right wsR_sub, h.iv_wrap, h.data_wrap, h.rounds⟩
  cases out
  · exact And.intro rfl rfl
  · exact And.intro rfl rfl

section
variable {out : Bool} {len : Nat → Nat} {k : Contract isa} {c : Prog isa} (hk : ChainK out len k c)
include hk

theorem wrap_call {name : String} {s₀ s : State} (h : WPre out len s₀) (hm : WMid s₀ s) :
    WP isa (.call name c) s fun s' =>
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      Frame (wrOf out len s₀ (wsR s₀)) s.mem s'.mem ∧
      k.post (s.callEntry.withRegions (rdOf out len s₀) (wrOf out len s₀ (wsR s₀)))
        (s'.withRegions (rdOf out len s₀) (wrOf out len s₀ (wsR s₀))) := by
  refine WP.call (k := k) hk.correct (hk.pre _ (hm.chain_pre h)) (by rw [hm.rd, hm.wr]; exact h.covers)
    (by rw [hm.wr]; exact h.covers_wr) ?_ hk.noFrames
  intro s' hrd hwr hsp hf hcs _ hpost
  exact ⟨hrd, hwr, hsp, hcs, hf, hpost⟩

theorem wrap_wp {name : String} {s₀ : State} (h : WPre out len s₀) :
    WP isa (chainWrap name c) s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.gpr .ra = s₀.gpr .ra ∧ s'.sp = s₀.sp ∧ k.post s₀ s' := by
  refine WP.seq (WP.mono (save_wp h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (wrap_call hk (name := name) h h₁) fun s₂ ⟨rd₂, wr₂, sp₂, cs₂, f₂, hpost⟩ => ?_)
  have hsv : Spill.Saved (sv s₀) (saveG s₀) chSaved s₂.mem :=
    (Spill.saveMem_saved (by decide) s₀.mem (sv s₀) _).frame (by have := f₂; rw [h₁.mem] at this; exact this)
      fun p hp r hr => h.slots_disj hp r hr
  have s1₂ : s₂.gpr .s1 = S s₀ := by rw [cs₂ _ (by decide), h₁.s1]
  have rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [rd₂, wr₂, h₁.rd, h₁.wr]
  rw [show encRestore = savePtr .s1 ++ Spill.restoreCode .t0 chSaved from rfl, WP.block_append_iff]
  refine WP.mono (savePtr_ok .s1) fun s₃ e => ?_
  subst e
  rw [s1₂]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := chSaved) (B := sv s₀) (align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp => ?_) hsv) fun s₄ r₄ => ?_
  · show InRegions (s₂.rd ++ s₂.wr) _ 8
    rw [rdwr₂]
    have := q_lt s₀
    have := chSaved_bound p hp
    have := h.scr_wrap
    exact in_rw (List.mem_append_right _ h.scr_mem)
      (by rw [sv_add]; exact Offset.contains_base _ (by omega) (by omega))
  have g₀ (r : Reg) (hr : r ≠ .t0) : saveG s₀ r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · have h0 := preserved_ne hr
    rw [r₄.gpr_of (r := r) ?_, g₀ r h0]
    by_cases h1 : r = .s1
    · left; subst h1; decide
    · right; rw [RegUpd.gpr_write_of_ne _ _ h0, cs₂ r hr, h₁.keep r hr h1, g₀ r h0]
  · rw [r₄.gpr (.ra, 16) (by decide), g₀ .ra (by decide)]
  · rw [r₄.sp, RegUpd.sp_write, sp₂, h₁.sp]
  -- The chain's postcondition, from the memory after the saves to the memory on entry.
  have m₄ : s₄.mem = s₂.mem := by rw [r₄.mem, RegUpd.mem_write]
  refine hk.post h (fun r hr => ?_) (by rw [State.withRegions_mem, State.callEntry_mem, h₁.mem])
    (by rw [m₄, State.withRegions_mem]) hpost
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [State.withRegions_gpr, State.callEntry_gpr s₁ (by decide : Reg.a0 ∉ linkRegs), h₁.a0]
  · rw [State.withRegions_gpr, State.callEntry_gpr s₁ (by decide : Reg.a1 ∉ linkRegs), h₁.a1]
  · rw [State.withRegions_gpr, State.callEntry_gpr s₁ (by decide : Reg.a2 ∉ linkRegs), h₁.a2]
  · rw [State.withRegions_gpr, State.callEntry_gpr s₁ (by decide : Reg.a3 ∉ linkRegs), h₁.a3]
  · rw [State.withRegions_gpr, State.callEntry_gpr s₁ (by decide : Reg.a4 ∉ linkRegs), h₁.a4]

/-! ## Constant time -/

theorem wrap_rel (name : String) {s₀ s₀' : State} (h0 : WPre out len s₀) (h0' : WPre out len s₀')
    (hq : ChPub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (chainWrap name c) fun _ _ => True := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6⟩ := hq
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) (.block encSave) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.s1]) (.block encRestore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.a0, .a1, .a2, .a3, .a4, .a5]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨q6, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := WMid s₀) (F₂ := WMid s₀') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨save_wp h0, save_wp h0'⟩
  have er : rdOf out len s₀' = rdOf out len s₀ := by simp only [rdOf, schR, dataL, W, Dp, N, q0, q3, q4]
  have ew : wrOf out len s₀' (wsR s₀') = wrOf out len s₀ (wsR s₀) := by
    simp only [wrOf, ivR, dataL, wsR, Iv, Dp, N, S, q2, q3, q4, q5]
  have c := (RelCT.call (n := name) hk.correct hk.ct
    (P := fun s₁ s₂ => WMid s₀ s₁ ∧ WMid s₀' s₂) (rdOf out len s₀) (wrOf out len s₀ (wsR s₀)) fun s₁ s₂ hm => by
      have p₂ := hk.pre _ (hm.2.chain_pre h0')
      have c₂ := h0'.covers
      have w₂ := h0'.covers_wr
      rw [er, ew] at p₂ c₂
      rw [ew] at w₂
      refine ⟨hk.pre _ (hm.1.chain_pre h0), p₂, hk.pub_of _ _ ?_, by rw [hm.1.rd, hm.1.wr]; exact h0.covers,
        by rw [hm.1.wr]; exact h0.covers_wr, by rw [hm.2.rd, hm.2.wr]; exact c₂, by rw [hm.2.wr]; exact w₂⟩
      simp only [ChPub, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
        State.callEntry_gpr _ (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a1 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a3 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.a4 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a5 ∉ linkRegs),
        hm.1.a0, hm.1.a1, hm.1.a2, hm.1.a3, hm.1.a4, hm.1.a5, hm.2.a0, hm.2.a1, hm.2.a2, hm.2.a3, hm.2.a4,
        hm.2.a5, hm.1.sp, hm.2.sp]
      exact ⟨q0, q1, q2, q3, q4, q5, q6⟩).wp
    (F₁ := fun (s : State) => s.gpr .s1 = S s₀ ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .s1 = S s₀' ∧ s.sp = s₀'.sp) fun s₁ s₂ hm =>
      ⟨WP.mono (wrap_call hk (name := name) h0 hm.1) fun _ hc =>
        ⟨by rw [hc.2.2.2.1 .s1 (by decide), hm.1.s1], by rw [hc.2.2.1, hm.1.sp]⟩,
       WP.mono (wrap_call hk (name := name) h0' hm.2) fun _ hc =>
        ⟨by rw [hc.2.2.2.1 .s1 (by decide), hm.2.s1], by rw [hc.2.2.1, hm.2.sp]⟩⟩
  have b := taintRegs
    (P := fun s₁ s₂ => (s₁.gpr .s1 = S s₀ ∧ s₁.sp = s₀.sp) ∧ (s₂.gpr .s1 = S s₀' ∧ s₂.sp = s₀'.sp))
    [.s1] (fun s₁ s₂ h => ⟨by rw [h.1.2, h.2.2, q6], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.1, h.2.1, S, S, q5]⟩) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem wrap_ct (name : String) : ConstantTime isa (WPre out len) ChPub (chainWrap name c) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (wrap_rel hk name h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end

/-- The chain, as such a chain. -/
theorem chain_k (out : Bool) :
    ChainK out (16 * ·) (Proof.Aes.chainRISCV64 out) (Impl.Aes.RISCV64.chain out) where
  pre _ h := h
  pub_of _ _ h := h
  correct := Proof.Aes.RISCV64.chain_correct out
  ct := Proof.Aes.RISCV64.chain_ct out
  noFrames := by cases out <;> rfl
  post {s₀ s t t'} h hg hm ht hp := by
    have g0 := hg .a0 (by simp)
    have g1 := hg .a1 (by simp)
    have g2 := hg .a2 (by simp)
    have g3 := hg .a3 (by simp)
    have g4 := hg .a4 (by simp)
    have edata' : Spec.Cbc.blocksAt (chMem s₀) (s₀.gpr .a3) (s₀.gpr .a4).toNat =
        Spec.Cbc.blocksAt s₀.mem (s₀.gpr .a3) (s₀.gpr .a4).toNat := h.blocks_eq
    simp only [Proof.Aes.chainRISCV64, g0, g1, g2, g3, g4, hm, ht] at hp ⊢
    rw [h.sch_eq, h.iv_eq, h.blocks_eq, edata'] at hp
    exact hp

/-! ## CBC encryption -/

/-- The chaining value after CBC encryption, the last ciphertext block, is
the CBC-MAC chain's. -/
theorem next_encrypt (ciph : Spec.Cmac.Cipher) :
    ∀ (xs : List (List Byte)) (c : List Byte),
      Spec.Cbc.next c (Spec.Cbc.encrypt ciph c xs) = Spec.Cmac.chain ciph c xs
  | [], _ => rfl
  | x :: xs, c => by
    rw [Spec.Cbc.encrypt, next_cons, next_encrypt ciph xs]
    simp only [Spec.Cmac.chain, List.foldl_cons, Proof.Aes.RISCV64.cbcXor_comm]

end VG.Proof.AesCbc.RISCV64
