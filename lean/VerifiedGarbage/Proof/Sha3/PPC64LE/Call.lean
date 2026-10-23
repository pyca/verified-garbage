module

public import VerifiedGarbage.Proof.Sha3.PPC64LE.Contract
public import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Sha3.PPC64LE.Permute
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MdStream.PPC64LE.Common

@[expose] public section

/-!
# SHA-3 on PPC64LE: calling the permutation, and saving registers
-/

namespace VG.Proof.Sha3.PPC64LE

open VG VG.PPC64LE VG.Impl.Sha3.PPC64LE.Stream
open VG.Spec.Sha3 (stateAt keccakF)

/-- Calling `vg_keccak_f1600` on the state at `r3`, with scratch space at
`r4`: the callee-saved registers are kept. -/
theorem call_ok {s : State} {st scr : Addr} (h3 : s.gpr .r3 = st) (h4 : s.gpr .r4 = scr)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨scr, 512⟩)
    (hw : PPC64LE.Covers [⟨st, 200⟩, ⟨scr, 512⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨scr, 512⟩] s.mem s'.mem →
      stateAt s'.mem st = keccakF (stateAt s.mem st) → Q s') :
    WP isa (.call "vg_keccak_f1600" Impl.Sha3.PPC64LE.permute) s Q := by
  have c3 : s.callEntry.gpr .r3 = st := (State.callEntry_gpr _ (by decide)).trans h3
  have c4 : s.callEntry.gpr .r4 = scr := (State.callEntry_gpr _ (by decide)).trans h4
  refine WP.call (k := Proof.Sha3.permutePPC64LE) permute_correct
    (rd := []) (wr := [⟨st, 200⟩, ⟨scr, 512⟩]) ?_ ?_ hw ?_ permute_noFrames
  · simp only [Proof.Sha3.permutePPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c3, c4]
    exact ⟨trivial, trivial, d₁⟩
  · intro a n h
    obtain ⟨r, hr, hc⟩ := hw a n (by simpa using h)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [Proof.Sha3.permutePPC64LE, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c3] at hpost
    exact hQ s' hrd hwr hsp hcs hf hpost

theorem preserved_r3_r4 : ∀ r ∈ preserved, r ≠ .r3 ∧ r ≠ .r4 := by decide

/-- `permuteAt`: calling `vg_keccak_f1600` on the state at `r26`, with
scratch space at `r27`. -/
theorem permuteAt_ok {s : State} {st scr : Addr} (h26 : s.gpr .r26 = st) (h27 : s.gpr .r27 = scr)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨scr, 512⟩)
    (hw : PPC64LE.Covers [⟨st, 200⟩, ⟨scr, 512⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨scr, 512⟩] s.mem s'.mem →
      stateAt s'.mem st = keccakF (stateAt s.mem st) → Q s') :
    WP isa permuteAt s Q := by
  unfold permuteAt mov
  refine WP.seq (MdStream.PPC64LE.wp_addi (by decide) fun s₁ u₁ =>
    MdStream.PPC64LE.wp_addi (by decide) fun s₂ u₂ => WP.block_nil ?_)
  have g : ∀ r, r ≠ .r3 → r ≠ .r4 → s₂.gpr r = s.gpr r := fun r h3 h4 => by
    rw [u₂.other r h4, u₁.other r h3]
  refine call_ok (st := st) (scr := scr)
    (by rw [u₂.other _ (by decide), u₁.gpr, h26]; exact BitVec.add_zero _)
    (by rw [u₂.gpr, u₁.other _ (by decide), h27]; exact BitVec.add_zero _)
    d₁ (by rw [u₂.wr, u₁.wr]; exact hw) fun s' rd' wr' sp' cs' f' e' => ?_
  have hm : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine hQ s' (by rw [rd', u₂.rd, u₁.rd]) (by rw [wr', u₂.wr, u₁.wr]) (by rw [sp', u₂.sp, u₁.sp])
    (fun r hr => ?_) (hm ▸ f') (by rw [e', hm])
  rw [cs' r hr, g r (preserved_r3_r4 r hr).1 (preserved_r3_r4 r hr).2]

end VG.Proof.Sha3.PPC64LE

namespace VG.Proof.Sha3.PPC64LE.Stream

open VG VG.PPC64LE VG.Impl.Sha3.PPC64LE.Stream

/-! ## Saving the caller's registers -/

/-- The caller's callee-saved registers `g` are saved in the scratch space at `b`. -/
abbrev Saved (b : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop := Spill.Saved b g saved m

/-- The memory after saving `r26`–`r31` (values `g`) at `b + 512 …`. -/
abbrev saveMem (m : Mem) (b : Addr) (g : Reg → BitVec 64) : Mem := Spill.saveMem m b g saved

theorem saved_off : ∀ p ∈ saved, 512 ≤ p.2 ∧ p.2 + 8 ≤ 560 := by decide

theorem saveMem_saved (m : Mem) (b : Addr) (g : Reg → BitVec 64) : Saved b g (saveMem m b g) :=
  Spill.saveMem_saved (by decide) m b g

theorem saveMem_frame (m : Mem) (b : Addr) (g : Reg → BitVec 64) :
    Frame [⟨b + BitVec.ofNat 64 512, 48⟩] m (saveMem m b g) :=
  Spill.saveMem_frame (by decide) (by decide) m b g

/-- Saving `r26`–`r31` with the scratch pointer in `b`. -/
theorem save_ok {b : Reg} {rest : List Instr} {s : State} {Q : State → Prop} (hb : b ≠ .r0)
    (hin : ∀ d, 512 ≤ d → d + 8 ≤ 560 → InRegions s.wr (s.gpr b + BitVec.ofNat 64 d) 8)
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = saveMem s.mem (s.gpr b) s.gpr → WP isa (.block rest) s' Q) :
    WP isa (.block (save b ++ rest)) s Q :=
  Spill.save_ok (l := saved) hb (by decide) (fun p hp => hin _ (by revert p; decide) (by revert p; decide))
    (k _ rfl rfl rfl rfl rfl)

/-- `restore`, `r27` (the base) last. -/
abbrev restored : List (Reg × Nat) :=
  [(.r26, 512), (.r28, 528), (.r29, 536), (.r30, 544), (.r31, 552), (.r27, 520)]

/-- Restoring `r26`–`r31` from the save area at `scr`. -/
theorem restore_ok {s : State} {scr : Addr} (h27 : s.gpr .r27 = scr)
    (hin : ∀ d, 512 ≤ d → d + 8 ≤ 560 → InRegions (s.rd ++ s.wr) (scr + BitVec.ofNat 64 d) 8)
    (g : Reg → BitVec 64) (hsv : Saved scr g s.mem) {Q : State → Prop}
    (k : ∀ s', (∀ p ∈ saved, s'.gpr p.1 = g p.1) →
      (∀ r, r ∉ saved.map Prod.fst → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block restore) s Q :=
  WP.mono (Spill.restore_wp (l := restored) (by decide) h27 (by decide) (by decide)
    (fun p hp => hin _ (by revert p; decide) (by revert p; decide)) (hsv.sub (by decide)))
    fun s' h => have h := h.perm (l' := saved) (by decide) (by decide)
      k s' h.gpr h.other h.mem h.rd h.wr h.sp

/-- Writes to the state and to the permutation's scratch space keep the
saved registers. -/
theorem Saved.permute {st scr : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Saved scr g m)
    (hd : Region.Disjoint ⟨st, 200⟩ ⟨scr, 640⟩) (hf : Frame [⟨st, 200⟩, ⟨scr, 512⟩] m m') :
    Saved scr g m' :=
  Spill.Saved.frame h hf fun p hp' r hr => by
    have hoff := saved_off p hp'
    have hsub : Region.Sub ⟨scr + BitVec.ofNat 64 p.2, 8⟩ ⟨scr, 640⟩ := Offset.sub_base _ (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd.symm.sub_left hsub
    · exact Offset.disjoint_base _ (by omega) (by omega)

/-- Writes to a region disjoint from the scratch space keep the saved
registers. -/
theorem Saved.disjoint {R : Region} {scr : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Saved scr g m)
    (hd : R.Disjoint ⟨scr, 640⟩) (hf : Frame [R] m m') : Saved scr g m' :=
  Spill.Saved.frame h hf fun p hp' r hr => by
    have hoff := saved_off p hp'
    simp only [List.mem_singleton] at hr
    subst hr
    exact hd.symm.sub_left (Offset.sub_base _ (by omega))

/-- Writes to the state keep the saved registers. -/
theorem Saved.state {st scr : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Saved scr g m)
    (hd : Region.Disjoint ⟨st, 200⟩ ⟨scr, 640⟩) (hf : Frame [⟨st, 200⟩] m m') :
    Saved scr g m' :=
  h.permute hd (hf.mono (by simp))

/-- The callee-saved registers our code never touches. -/
abbrev untouched : List Reg :=
  [.r2, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25]

theorem notU {r : Reg} (hr : r ∈ untouched) (x : Reg) (hx : x ∉ untouched := by decide) : r ≠ x :=
  fun h => hx (h ▸ hr)

theorem preserved_split : ∀ r ∈ preserved, r ∈ saved.map Prod.fst ∨ r ∈ untouched := by decide

/-- The callee-saved registers are the caller's again once `restore` has run
and `untouched` were never written. -/
theorem preserved_of {s₀ s' : State} (hsv : ∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1)
    (hu : ∀ r ∈ untouched, s'.gpr r = s₀.gpr r) : ∀ r ∈ preserved, s'.gpr r = s₀.gpr r := by
  intro r hr
  rcases preserved_split r hr with h | h
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    exact hsv p hp
  · exact hu r h

theorem untouched_preserved : ∀ r ∈ untouched, r ∈ preserved := by decide

end VG.Proof.Sha3.PPC64LE.Stream
