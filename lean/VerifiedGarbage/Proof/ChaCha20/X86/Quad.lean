import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.ChaCha20.Spec
import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Impl.ChaCha20.X86.Xor
import VerifiedGarbage.Proof.ChaCha20.X86.Vqr

/-!
# ChaCha20 on x86 (32-bit): four blocks at once with SSE2

Doubleword `l` of each slot of `buf` (and of each register) holds a word of
block `l`; each quarter round of the code is the specification's on each of
the four blocks.
-/

namespace VG.Proof.ChaCha20.X86.Quad

open VG VG.X86 VG.Impl.ChaCha20.X86 VG.Impl.ChaCha20.X86.Xor
open VG.Spec.ChaCha20 (Word quarterRound qround innerBlock)
open VG.Proof.ChaCha20

/-! ## The slots -/

/-- `buf`, as far as the four-block code uses it. -/
abbrev bufR (buf : Addr) : Region := ⟨buf, 320⟩

/-- The slots of the sixteen words, `buf[0, 256)`. -/
abbrev slotsR (buf : Addr) : Region := ⟨buf, 256⟩

/-- The four states `vs 0, …, vs 3` are in the slots: word `k` of state `l`
in doubleword `l` of slot `k`. -/
def Holds4 (buf : Addr) (vs : Nat → CState) (m : Mem) : Prop :=
  ∀ k (hk : k < 16) l, l < 4 → m.readW (buf + BitVec.ofNat 64 (16 * k + 4 * l)) 32 = (vs l)[k]

theorem ea_setXmm (s : State) (r : XReg) (v : BitVec 128) (m : MemOp) : (s.setXmm r v).ea m = s.ea m := rfl

theorem ea_withMem (s : State) (m : Mem) (o : MemOp) : ({ s with mem := m } : State).ea o = s.ea o := rfl

theorem ea_gpr {s s' : State} (h : s'.gpr = s.gpr) (m : MemOp) : s'.ea m = s.ea m := by
  simp only [State.ea, h]

theorem in_buf {rs ws : List Region} {buf : Addr} (hw : bufR buf ∈ ws) {d n : Nat} (h : d + n ≤ 320) :
    InRegions (rs ++ ws) (buf + BitVec.ofNat 64 d) n :=
  ⟨bufR buf, List.mem_append_right _ hw, Offset.contains_base buf h (by lit_omega)⟩

theorem out_buf {ws : List Region} {buf : Addr} (hw : bufR buf ∈ ws) {d n : Nat} (h : d + n ≤ 320) :
    InRegions ws (buf + BitVec.ofNat 64 d) n :=
  ⟨bufR buf, hw, Offset.contains_base buf h (by lit_omega)⟩

theorem lane_load (m : Mem) (buf : Addr) (d : Nat) {l : Nat} (hl : l < 4) :
    dword (m.readW (buf + BitVec.ofNat 64 d) 128) l = m.readW (buf + BitVec.ofNat 64 (d + 4 * l)) 32 := by
  rw [dword_readW _ _ hl, Offset.add_add]

theorem lane_write_self (m : Mem) (buf : Addr) (v : BitVec 128) (d : Nat) {l : Nat} (hl : l < 4) :
    (m.writeW (buf + BitVec.ofNat 64 d) v).readW (buf + BitVec.ofNat 64 (d + 4 * l)) 32 = dword v l := by
  rw [← Offset.add_add, readW_writeW128 _ _ _ hl]

theorem lane_write_other (m : Mem) (buf : Addr) (v : BitVec 128) {d e : Nat} (hd : d + 4 ≤ 2 ^ 32)
    (he : e + 16 ≤ 2 ^ 32) (h : d + 4 ≤ e ∨ e + 16 ≤ d) :
    (m.writeW (buf + BitVec.ofNat 64 e) v).readW (buf + BitVec.ofNat 64 d) 32 =
      m.readW (buf + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (Offset.sep buf h (by lit_omega) (by lit_omega)) (by decide)

theorem slots_frame_write {rs : List Region} {m m' : Mem} {buf : Addr} (h : Frame rs m m')
    (hr : slotsR buf ∈ rs) (v : BitVec 128) {k : Nat} (hk : k < 16) :
    Frame rs m (m'.writeW (buf + BitVec.ofNat 64 (slot k)) v) :=
  h.writeW hr _ (Offset.contains_base buf (by simp only [slot]; omega) (by simp only [slot]; lit_omega))

/-! ## One quarter round on the four states -/

theorem lane_qr {m : Mem} {buf : Addr} {vs : Nat → CState} (h : Holds4 buf vs m) {x : Nat}
    (hx : x < 16) {l : Nat} (hl : l < 4) :
    dword (m.readW (buf + BitVec.ofNat 64 (slot x)) 128) l = (vs l)[x] := by
  rw [lane_load _ _ _ hl]; exact h x hx l hl

/-- Reading lane `l` of slot `k` after writing slot `k'`. -/
theorem lane_other (m : Mem) (buf : Addr) (v : BitVec 128) {k k' l : Nat} (hk : k < 16)
    (hk' : k' < 16) (hl : l < 4) (h : k' ≠ k) :
    (m.writeW (buf + BitVec.ofNat 64 (slot k')) v).readW (buf + BitVec.ofNat 64 (16 * k + 4 * l)) 32 =
      m.readW (buf + BitVec.ofNat 64 (16 * k + 4 * l)) 32 :=
  lane_write_other _ _ _ (by lit_omega) (by simp only [slot]; omega) (by simp only [slot]; omega)

theorem lane_self (m : Mem) (buf : Addr) (v : BitVec 128) (k : Nat) {l : Nat} (hl : l < 4) :
    (m.writeW (buf + BitVec.ofNat 64 (slot k)) v).readW (buf + BitVec.ofNat 64 (16 * k + 4 * l)) 32 =
      dword v l :=
  lane_write_self _ _ _ _ hl

theorem quarter4_ok {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16) (hw : w < 16)
    (hd : [x, y, z, w].Nodup) {buf : Addr} {vs : Nat → CState} {s : State}
    (hb : ∀ d, d < 320 → s.ea (at_ .edi d) = buf + BitVec.ofNat 64 d) (hwb : bufR buf ∈ s.wr)
    (h : Holds4 buf vs s.mem) :
    WP isa (quarter4 x y z w) s fun s' =>
      Holds4 buf (fun l => qround (vs l) ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s'.mem ∧
      Frame [slotsR buf] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have nd : (x ≠ y ∧ x ≠ z ∧ x ≠ w) ∧ (y ≠ z ∧ y ≠ w) ∧ z ≠ w := by simpa using hd
  obtain ⟨⟨nxy, nxz, nxw⟩, ⟨nyz, nyw⟩, nzw⟩ := nd
  have ex := hb (slot x) (by simp only [slot]; omega)
  have ey := hb (slot y) (by simp only [slot]; omega)
  have ez := hb (slot z) (by simp only [slot]; omega)
  have ew := hb (slot w) (by simp only [slot]; omega)
  have ix := in_buf (rs := s.rd) hwb (d := slot x) (n := 16) (by simp only [slot]; omega)
  have iy := in_buf (rs := s.rd) hwb (d := slot y) (n := 16) (by simp only [slot]; omega)
  have iz := in_buf (rs := s.rd) hwb (d := slot z) (n := 16) (by simp only [slot]; omega)
  have iw := in_buf (rs := s.rd) hwb (d := slot w) (n := 16) (by simp only [slot]; omega)
  unfold quarter4
  rw [WP.block_append_iff, WP.block_append_iff]
  -- The loads.
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, ea_setXmm, ex, ey, ez, ew, ix, iy,
    iz, iw, ite_true, RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine WP.mono (vqr_ok _) fun s₁ ⟨hv, _, hg, hm, hr, hwr⟩ => ?_
  simp only [RegUpd.gpr_setXmm, RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm] at hg hm hr hwr
  -- The stores.
  have o : ∀ k, k < 16 → InRegions s₁.wr (buf + BitVec.ofNat 64 (slot k)) 16 := fun k hk => by
    rw [hwr]; exact out_buf hwb (by simp only [slot]; omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store128, ea_withMem, ea_gpr hg, ex, ey, ez,
    ew, o x hx, o y hy, o z hz, o w hw, ite_true, Option.some.injEq, exists_eq_left', hm]
  refine ⟨fun k hk l hl => ?_, ?_, hg, hr, hwr⟩
  · obtain ⟨ha, hb', hc, hd'⟩ := hv l hl
    simp only [dw, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true,
      lane_qr h hx hl, lane_qr h hy hl, lane_qr h hz hl, lane_qr h hw hl] at ha hb' hc hd'
    rw [qround_get _ _ _ _ _ k hk]
    simp only
    by_cases e4 : w = k
    · subst e4; simp only [ite_true]
      rw [lane_self _ _ _ _ hl]; exact hd'
    by_cases e3 : z = k
    · subst e3; simp only [ite_true, e4, ite_false]
      rw [lane_other _ _ _ hz hw hl e4, lane_self _ _ _ _ hl]; exact hc
    by_cases e2 : y = k
    · subst e2; simp only [ite_true, e4, e3, ite_false]
      rw [lane_other _ _ _ hy hw hl e4, lane_other _ _ _ hy hz hl e3, lane_self _ _ _ _ hl]; exact hb'
    by_cases e1 : x = k
    · subst e1; simp only [ite_true, e4, e3, e2, ite_false]
      rw [lane_other _ _ _ hx hw hl e4, lane_other _ _ _ hx hz hl e3, lane_other _ _ _ hx hy hl e2,
        lane_self _ _ _ _ hl]; exact ha
    simp only [e4, e3, e2, e1, ite_false]
    rw [lane_other _ _ _ hk hw hl e4, lane_other _ _ _ hk hz hl e3, lane_other _ _ _ hk hy hl e2,
      lane_other _ _ _ hk hx hl e1]
    exact h k hk l hl
  · exact slots_frame_write (slots_frame_write (slots_frame_write (slots_frame_write (Frame.refl _ _)
      (List.mem_singleton_self _) _ hx) (List.mem_singleton_self _) _ hy) (List.mem_singleton_self _) _ hz)
      (List.mem_singleton_self _) _ hw

/-! ## Double rounds -/

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI4 (buf : Addr) (vs : Nat → CState) (s₀ s : State) : Prop where
  holds : Holds4 buf vs s.mem
  frame : Frame [slotsR buf] s₀.mem s.mem
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

section
variable {buf : Addr} {s₀ : State} (hb : ∀ d, d < 320 → s₀.ea (at_ .edi d) = buf + BitVec.ofNat 64 d)
  (hwb : bufR buf ∈ s₀.wr)
include hb hwb

theorem quarter4_step {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16) (hw : w < 16)
    (hd : [x, y, z, w].Nodup) {vs : Nat → CState} {s : State} (h : RI4 buf vs s₀ s) :
    WP isa (quarter4 x y z w) s
      (RI4 buf (fun l => qround (vs l) ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s₀) :=
  WP.mono (quarter4_ok hx hy hz hw hd (fun d hd => (ea_gpr h.gpr _).trans (hb d hd)) (h.wr ▸ hwb)
    h.holds)
    fun _ ⟨hh, hf, hg, hr, hw'⟩ => ⟨hh, h.frame.trans hf, hg.trans h.gpr, hr.trans h.rd, hw'.trans h.wr⟩

theorem doubleRound4_ok {vs : Nat → CState} {s : State} (h : RI4 buf vs s₀ s) :
    WP isa doubleRound4 s (RI4 buf (fun l => innerBlock (vs l)) s₀) := by
  unfold doubleRound4
  refine WP.seq (WP.mono (quarter4_step hb hwb (x := 0) (y := 4) (z := 8) (w := 12) (by decide)
    (by decide) (by decide) (by decide) (by decide) h) fun _ h1 => ?_)
  refine WP.seq (WP.mono (quarter4_step hb hwb (x := 1) (y := 5) (z := 9) (w := 13) (by decide)
    (by decide) (by decide) (by decide) (by decide) h1) fun _ h2 => ?_)
  refine WP.seq (WP.mono (quarter4_step hb hwb (x := 2) (y := 6) (z := 10) (w := 14) (by decide)
    (by decide) (by decide) (by decide) (by decide) h2) fun _ h3 => ?_)
  refine WP.seq (WP.mono (quarter4_step hb hwb (x := 3) (y := 7) (z := 11) (w := 15) (by decide)
    (by decide) (by decide) (by decide) (by decide) h3) fun _ h4 => ?_)
  refine WP.seq (WP.mono (quarter4_step hb hwb (x := 0) (y := 5) (z := 10) (w := 15) (by decide)
    (by decide) (by decide) (by decide) (by decide) h4) fun _ h5 => ?_)
  refine WP.seq (WP.mono (quarter4_step hb hwb (x := 1) (y := 6) (z := 11) (w := 12) (by decide)
    (by decide) (by decide) (by decide) (by decide) h5) fun _ h6 => ?_)
  refine WP.seq (WP.mono (quarter4_step hb hwb (x := 2) (y := 7) (z := 8) (w := 13) (by decide)
    (by decide) (by decide) (by decide) (by decide) h6) fun _ h7 => ?_)
  exact quarter4_step hb hwb (x := 3) (y := 4) (z := 9) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) h7

theorem rounds4_ok {vs : Nat → CState} (h : Holds4 buf vs s₀.mem) :
    ∀ n, WP isa (rounds4 n) s₀ (RI4 buf (fun l => Nat.repeat innerBlock n (vs l)) s₀)
  | 0 => WP.block_nil ⟨h, Frame.refl _ _, rfl, rfl, rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds4_ok h n) fun _ h' => doubleRound4_ok hb hwb h')

end

/-! ## The context -/

open VG.Spec.ChaCha20 (stateAt serialize)

/-- The state, 64 bytes at `st`. -/
abbrev stR (st : Addr) : Region := ⟨st, 64⟩

/-- Where `ebx` and `edi` point (`state` and `buf`), and what the code may
access there. -/
structure Ctx (st buf : Addr) (s : State) : Prop where
  eaS : ∀ d, d < 64 → s.ea (at_ .ebx d) = st + BitVec.ofNat 64 d
  eaB : ∀ d, d < 320 → s.ea (at_ .edi d) = buf + BitVec.ofNat 64 d
  wst : stR st ∈ s.wr
  wb : bufR buf ∈ s.wr
  sb : (stR st).Disjoint (bufR buf)

theorem Ctx.of {st buf : Addr} {s s' : State} (h : Ctx st buf s) (hg : s'.gpr = s.gpr)
    (hw : s'.wr = s.wr) : Ctx st buf s' :=
  ⟨fun d hd => (ea_gpr hg _).trans (h.eaS d hd), fun d hd => (ea_gpr hg _).trans (h.eaB d hd),
    hw ▸ h.wst, hw ▸ h.wb, h.sb⟩

theorem in_st {rs ws : List Region} {st : Addr} (hw : stR st ∈ ws) {d n : Nat} (h : d + n ≤ 64) :
    InRegions (rs ++ ws) (st + BitVec.ofNat 64 d) n :=
  ⟨stR st, List.mem_append_right _ hw, Offset.contains_base st h (by lit_omega)⟩

theorem out_st {ws : List Region} {st : Addr} (hw : stR st ∈ ws) {d n : Nat} (h : d + n ≤ 64) :
    InRegions ws (st + BitVec.ofNat 64 d) n :=
  ⟨stR st, hw, Offset.contains_base st h (by lit_omega)⟩

/-- A state in memory outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (stR p).Disjoint r) : stateAt m' p = stateAt m p := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn]
  exact hf.readW (Offset.contains_base p (by lit_omega) (by lit_omega)) hd (by decide)

/-- Doubleword `i` of row `r` of a state in memory. -/
theorem row_lane (m : Mem) (st : Addr) {r i : Nat} (hr : r < 4) (hi : i < 4) :
    dword (m.readW (st + BitVec.ofNat 64 (16 * r)) 128) i = (stateAt m st)[4 * r + i]'(by omega) := by
  rw [lane_load _ _ _ hi]
  simp only [stateAt, Vector.getElem_ofFn]
  exact congrArg (fun d => m.readW (st + BitVec.ofNat 64 d) 32) (by omega)

theorem ctr_get (S : CState) (j : Nat) {k : Nat} (hk : k < 16) :
    (ctr S j)[k] = if k = 12 then S[12] + BitVec.ofNat 32 j else S[k] := by
  simp only [ctr, Vector.getElem_set]
  by_cases h : k = 12
  · subst h; simp
  · simp [h, Ne.symm h]

/-! ## The setup -/

/-- The words below `n` of the four states `vs` are in their slots, and only
the slots have been written since `s₀`. -/
structure Done (buf : Addr) (vs : Nat → CState) (n : Nat) (s₀ s : State) : Prop where
  done : ∀ k (hk : k < 16), k < n → ∀ l, l < 4 →
    s.mem.readW (buf + BitVec.ofNat 64 (16 * k + 4 * l)) 32 = (vs l)[k]
  frame : Frame [slotsR buf] s₀.mem s.mem
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- Row `r` of the state `C`, in `xmm4`. -/
def Row4 (C : CState) (r : Nat) (s : State) : Prop :=
  ∀ i (hi : i < 4) (hr : r < 4), dword (s.xmm .xmm4) i = C[4 * r + i]'(by omega)

section
variable {st buf : Addr} {s₀ : State} (hc : Ctx st buf s₀)
include hc

theorem setupWord_ok {r i : Nat} (hr : r < 4) (hi : i < 4) {s : State}
    (h : Done buf (fun _ => stateAt s₀.mem st) (4 * r + i) s₀ s)
    (hx : Row4 (stateAt s₀.mem st) r s) :
    WP isa (.block [bcast .xmm0 .xmm4 i, .movdquStore (at_ .edi (slot (4 * r + i))) .xmm0]) s
      fun s' => Done buf (fun _ => stateAt s₀.mem st) (4 * r + (i + 1)) s₀ s' ∧
        Row4 (stateAt s₀.mem st) r s' := by
  have e := (ea_gpr h.gpr _).trans (hc.eaB (slot (4 * r + i)) (by simp only [slot]; omega))
  have o : InRegions s.wr (buf + BitVec.ofNat 64 (slot (4 * r + i))) 16 := by
    rw [h.wr]; exact out_buf hc.wb (by simp only [slot]; omega)
  apply WP.of_runBlock
  simp only [bcast, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, State.store128,
    ea_setXmm, e, RegUpd.wr_setXmm, o, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun k hk hkn l hl => ?_, ?_, ?_, ?_, ?_⟩, fun j hj hr' => ?_⟩
  · simp only [RegUpd.mem_setXmm]
    by_cases hke : k = 4 * r + i
    · subst hke
      rw [lane_self _ _ _ _ hl, RegUpd.xmm_setXmm_self, dword_shufDwords_bcast _ hi hl,
        hx i hi hr]
    · rw [lane_other _ _ _ hk (by omega) hl (Ne.symm hke)]
      exact h.done k hk (by omega) l hl
  · exact slots_frame_write h.frame (List.mem_singleton_self _) _ (by omega)
  · exact h.gpr
  · exact h.rd
  · exact h.wr
  · simp only [RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true]; exact hx j hj hr'

theorem setupRow_ok {r : Nat} (hr : r < 4) {s : State}
    (h : Done buf (fun _ => stateAt s₀.mem st) (4 * r) s₀ s) :
    WP isa (.block (setupRow r)) s (Done buf (fun _ => stateAt s₀.mem st) (4 * r + 4) s₀) := by
  have e := (ea_gpr h.gpr _).trans (hc.eaS (16 * r) (by omega))
  have i : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 (16 * r)) 16 := by
    rw [h.wr]; exact in_st hc.wst (by omega)
  have hS : stateAt s.mem st = stateAt s₀.mem st := stateAt_frame h.frame (by
    simp only [List.mem_singleton, forall_eq]
    exact hc.sb.sub_right (Region.sub_prefix (by lit_omega)))
  rw [setupRow, ← List.singleton_append, WP.block_append_iff]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, e, i, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  have h₀ : Done buf (fun _ => stateAt s₀.mem st) (4 * r + 0) s₀
      (s.setXmm .xmm4 (s.mem.readW (st + BitVec.ofNat 64 (16 * r)) 128)) ∧
      Row4 (stateAt s₀.mem st) r (s.setXmm .xmm4 (s.mem.readW (st + BitVec.ofNat 64 (16 * r)) 128)) :=
    ⟨⟨fun k hk hkn l hl => h.done k hk hkn l hl, h.frame, h.gpr, h.rd, h.wr⟩, fun j hj hr' => by
      rw [RegUpd.xmm_setXmm_self, row_lane _ _ hr' hj, hS]⟩
  exact WP.mono (wp_range_flatMap (M := isa)
    (fun i s => Done buf (fun _ => stateAt s₀.mem st) (4 * r + i) s₀ s ∧ Row4 (stateAt s₀.mem st) r s)
    (fun i s hi hs => setupWord_ok hc hr hi hs.1 hs.2) 4 (Nat.le_refl _) _ h₀) fun _ h' => h'.1

/-- The counters `c + l` (from word 12 of `C`) at `ctrOff`. -/
def Ctrs (buf : Addr) (C : CState) (n : Nat) (m : Mem) : Prop :=
  ∀ l, l < n → m.readW (buf + BitVec.ofNat 64 (ctrOff + 4 * l)) 32 = C[12] + BitVec.ofNat 32 l

/-- `buf[272, 288)`, the counters. -/
abbrev ctrR (buf : Addr) : Region := ⟨buf + BitVec.ofNat 64 ctrOff, 16⟩

/-- Before lane `n` of the counters. -/
structure CI (buf : Addr) (C : CState) (n : Nat) (s₀ s : State) : Prop where
  slots : ∀ k (hk : k < 16) l, l < 4 → (k ≠ 12 ∨ l < n) →
    s.mem.readW (buf + BitVec.ofNat 64 (16 * k + 4 * l)) 32 = (ctr C l)[k]
  ctrs : Ctrs buf C n s.mem
  eax : s.gpr .eax = C[12] + BitVec.ofNat 32 n
  frame : Frame [slotsR buf, ctrR buf] s₀.mem s.mem
  keep : ∀ r, r ≠ .eax → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

omit hc in
theorem w32_other (m : Mem) (buf : Addr) (v : BitVec 32) {d e : Nat} (hd : d + 4 ≤ 2 ^ 32)
    (he : e + 4 ≤ 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (buf + BitVec.ofNat 64 e) v).readW (buf + BitVec.ofNat 64 d) 32 =
      m.readW (buf + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (Offset.sep buf h (by lit_omega) (by lit_omega)) (by decide)

theorem ctrLane_ok {C : CState} {l : Nat} (hl : l < 4) {s : State} (h : CI buf C l s₀ s) :
    WP isa (.block (ctrLane l)) s (CI buf C (l + 1) s₀) := by
  have hdi : s.gpr .edi = s₀.gpr .edi := h.keep _ (by decide)
  have e₁ : addr (s₀.gpr .edi) (slot 12 + 4 * l) = buf + BitVec.ofNat 64 (16 * 12 + 4 * l) :=
    hc.eaB _ (by simp only [slot]; omega)
  have e₂ : addr (s₀.gpr .edi) (ctrOff + 4 * l) = buf + BitVec.ofNat 64 (ctrOff + 4 * l) :=
    hc.eaB _ (by simp only [ctrOff]; omega)
  have o₁ : InRegions s.wr (addr (s₀.gpr .edi) (slot 12 + 4 * l)) 4 := by
    rw [e₁, h.wr]; exact out_buf hc.wb (by omega)
  refine Wp.wp_stm hdi o₁ fun s₁ u₁ => ?_
  have o₂ : InRegions s₁.wr (addr (s₀.gpr .edi) (ctrOff + 4 * l)) 4 := by
    rw [e₂, u₁.wr, h.wr]; exact out_buf hc.wb (by simp only [ctrOff]; omega)
  refine Wp.wp_stm (by rw [u₁.gpr, hdi]) o₂ fun s₂ u₂ => ?_
  refine Wp.wp_addi fun s₃ u₃ => WP.block_nil ?_
  have hm : s₃.mem = (s.mem.writeW (buf + BitVec.ofNat 64 (16 * 12 + 4 * l)) (s.gpr .eax)).writeW
      (buf + BitVec.ofNat 64 (ctrOff + 4 * l)) (s.gpr .eax) := by
    rw [u₃.mem, u₂.mem, u₁.mem, u₁.gpr, e₁, e₂]
  refine ⟨fun k hk l' hl' hkl => ?_, fun l' hl' => ?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [hm, w32_other (d := 16 * k + 4 * l') (e := ctrOff + 4 * l) _ _ _ (by lit_omega) (by simp only [ctrOff]; lit_omega)
      (by simp only [ctrOff]; omega)]
    by_cases he : k = 12 ∧ l' = l
    · obtain ⟨rfl, rfl⟩ := he
      rw [Mem.readW_writeW_self32, h.eax, ctr_get _ _ hk, ite_eq_left rfl]
    · rw [w32_other (d := 16 * k + 4 * l') (e := 16 * 12 + 4 * l) _ _ _ (by lit_omega) (by lit_omega) (by omega)]
      exact h.slots k hk l' hl' (by omega)
  · rw [hm]
    by_cases he : l' = l
    · subst he; rw [Mem.readW_writeW_self32, h.eax]
    · rw [w32_other (d := ctrOff + 4 * l') (e := ctrOff + 4 * l) _ _ _ (by simp only [ctrOff]; lit_omega) (by simp only [ctrOff]; lit_omega)
        (by simp only [ctrOff]; omega),
        w32_other (d := ctrOff + 4 * l') (e := 16 * 12 + 4 * l) _ _ _ (by simp only [ctrOff]; lit_omega) (by lit_omega)
        (by simp only [ctrOff]; omega)]
      exact h.ctrs l' (by omega)
  · rw [u₃.gpr, u₂.gpr, u₁.gpr, h.eax, Offset.add_ofNat_add_one]
  · rw [hm]
    refine (h.frame.writeW (List.mem_cons_self ..) _ (Offset.contains_base buf (by omega) (by lit_omega))).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ ?_
    exact Offset.contains buf (by omega) (by omega) (by simp only [ctrOff]; lit_omega)
  · rw [u₃.other r hr, u₂.gpr, u₁.gpr, h.keep r hr]
  · rw [u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr, h.wr]

/-- What the setup leaves: the four states in the slots, the counters at
`ctrOff`, and everything else as it was (but `eax`). -/
structure SPost (buf : Addr) (C : CState) (s₀ s : State) : Prop where
  holds : Holds4 buf (fun l => ctr C l) s.mem
  ctrs : Ctrs buf C 4 s.mem
  frame : Frame [slotsR buf, ctrR buf] s₀.mem s.mem
  keep : ∀ r, r ≠ .eax → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem setup4_ok : WP isa (.block setup4) s₀ (SPost buf (stateAt s₀.mem st) s₀) := by
  rw [setup4, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (fun r s => Done buf (fun _ => stateAt s₀.mem st) (4 * r) s₀ s)
    (fun r s hr hs => setupRow_ok hc hr hs) 4 (Nat.le_refl _) s₀
    ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, rfl, rfl, rfl⟩) fun s h => ?_
  have hb : s.gpr .ebx = s₀.gpr .ebx := by rw [h.gpr]
  have e : addr (s₀.gpr .ebx) 48 = st + BitVec.ofNat 64 48 := hc.eaS 48 (by decide)
  have hS : stateAt s.mem st = stateAt s₀.mem st := stateAt_frame h.frame (by
    simp only [List.mem_singleton, forall_eq]
    exact hc.sb.sub_right (Region.sub_prefix (by lit_omega)))
  have v : s.mem.readW (st + BitVec.ofNat 64 48) 32 = (stateAt s₀.mem st)[12] := by
    rw [← hS]; simp [stateAt]
  rw [setupCtr, ← List.singleton_append]
  refine Wp.wp_ldm hb (by rw [e, h.rd, h.wr]; exact in_st hc.wst (by decide)) fun s₁ u₁ => ?_
  rw [e, v] at u₁
  have c₀ : CI buf (stateAt s₀.mem st) 0 s₀ s₁ :=
    ⟨fun k hk l hl hkl => by
      have hk12 : k ≠ 12 := by omega
      rw [u₁.mem, h.done k hk (by omega) l hl, ctr_get _ _ hk, ite_eq_right hk12],
      fun _ h => absurd h (Nat.not_lt_zero _), by rw [u₁.gpr]; simp,
      by rw [u₁.mem]; exact h.frame.mono (by simp), fun r hr => by rw [u₁.other r hr, h.gpr],
      by rw [u₁.rd, h.rd], by rw [u₁.wr, h.wr]⟩
  refine WP.mono (wp_range_flatMap (M := isa) (fun l s => CI buf (stateAt s₀.mem st) l s₀ s)
    (fun l s hl hs => ctrLane_ok hc hl hs) 4 (Nat.le_refl _) s₁ c₀) fun s' h' => ?_
  exact ⟨fun k hk l hl => h'.slots k hk l hl (by omega), h'.ctrs, h'.frame, h'.keep, h'.rd, h'.wr⟩

end

/-! ## The output: loading a row -/

theorem xr_ne : ∀ i, i < 4 → ∀ j, j < 4 → i ≠ j → xr i ≠ xr j := by decide
theorem xr_ne45 : ∀ i, i < 4 → xr i ≠ .xmm4 ∧ xr i ≠ .xmm5 := by decide

theorem loadRow_ok {st buf : Addr} {r : Nat} (hr : r < 4) {vs : Nat → CState} {s : State}
    (hc : Ctx st buf s) (hh : Holds4 buf vs s.mem) :
    WP isa (.block (loadRow r)) s fun s' =>
      (∀ i (hi : i < 4) l, l < 4 → dword (s'.xmm (xr i)) l = (vs l)[4 * r + i]) ∧
      Row4 (stateAt s.mem st) r s' ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e0 := hc.eaB (slot (4 * r)) (by simp only [slot]; omega)
  have e1 := hc.eaB (slot (4 * r + 1)) (by simp only [slot]; omega)
  have e2 := hc.eaB (slot (4 * r + 2)) (by simp only [slot]; omega)
  have e3 := hc.eaB (slot (4 * r + 3)) (by simp only [slot]; omega)
  have e4 := hc.eaS (16 * r) (by omega)
  have i0 := in_buf (rs := s.rd) hc.wb (d := slot (4 * r)) (n := 16) (by simp only [slot]; omega)
  have i1 := in_buf (rs := s.rd) hc.wb (d := slot (4 * r + 1)) (n := 16) (by simp only [slot]; omega)
  have i2 := in_buf (rs := s.rd) hc.wb (d := slot (4 * r + 2)) (n := 16) (by simp only [slot]; omega)
  have i3 := in_buf (rs := s.rd) hc.wb (d := slot (4 * r + 3)) (n := 16) (by simp only [slot]; omega)
  have i4 := in_st (rs := s.rd) hc.wst (d := 16 * r) (n := 16) (by omega)
  apply WP.of_runBlock
  simp only [loadRow, runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, ea_setXmm,
    e0, e1, e2, e3, e4, i0, i1, i2, i3, i4, ite_true, RegUpd.mem_setXmm, RegUpd.rd_setXmm,
    RegUpd.wr_setXmm, RegUpd.gpr_setXmm, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun i hi l hl => ?_, fun j hj hr' => ?_, trivial, trivial, trivial, trivial⟩
  · rcases cases4 hi with rfl | rfl | rfl | rfl <;>
      simp only [xr, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true]
    · rw [lane_qr hh (by omega) hl]; rfl
    · rw [lane_qr hh (by omega) hl]
    · rw [lane_qr hh (by omega) hl]
    · rw [lane_qr hh (by omega) hl]
  · simp only [RegUpd.xmm_setXmm_self]; exact row_lane _ _ hr' hj

/-! ## Adding the input states -/

/-- While adding the input states to row `r`: `xr j` holds words `4 r + j`
of the four states `vs`, plus those of the input states `ctr C l` if
`j < i`; `xmm4` holds row `r` of `C`; nothing else has changed since `s₁`
(but XMM registers). -/
structure AW (vs : Nat → CState) (C : CState) (r i : Nat) (s₁ s : State) : Prop where
  regs : ∀ j (hj : j < 4) (hr : r < 4) l, l < 4 → dword (s.xmm (xr j)) l =
    if j < i then (vs l)[4 * r + j] + (ctr C l)[4 * r + j] else (vs l)[4 * r + j]
  row : Row4 C r s
  mem : s.mem = s₁.mem
  gpr : s.gpr = s₁.gpr
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr

theorem addWord_ok {st buf : Addr} {vs : Nat → CState} {C : CState} {r i : Nat} (hr : r < 4)
    (hi : i < 4) {s₁ s : State} (hc : Ctx st buf s₁) (hct : Ctrs buf C 4 s₁.mem)
    (h : AW vs C r i s₁ s) : WP isa (.block (addWord4 r i)) s (AW vs C r (i + 1) s₁) := by
  -- The value added to `xr i`: word `4 r + i` of the input states.
  suffices hadd : WP isa (.block (addWord4 r i)) s fun s' =>
      (∀ l, l < 4 → dword (s'.xmm (xr i)) l = dword (s.xmm (xr i)) l + (ctr C l)[4 * r + i]) ∧
      (∀ x, x ≠ xr i → x ≠ .xmm5 → s'.xmm x = s.xmm x) ∧
      s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr by
    refine WP.mono hadd fun s' ⟨ha, ho, hm, hg, hrd, hwr⟩ => ⟨fun j hj _ l hl => ?_, fun j hj hr' => ?_,
      hm.trans h.mem, hg.trans h.gpr, hrd.trans h.rd, hwr.trans h.wr⟩
    · by_cases hji : j = i
      · subst hji
        rw [ha l hl, h.regs j hj hr l hl, ite_eq_right (Nat.lt_irrefl j), ite_eq_left (Nat.lt_succ_self j)]
      · rw [ho _ (xr_ne j hj i hi hji) (xr_ne45 j hj).2, h.regs j hj hr l hl]
        by_cases hj' : j < i
        · rw [ite_eq_left hj', ite_eq_left (by omega)]
        · rw [ite_eq_right hj', ite_eq_right (by omega)]
    · rw [ho _ (xr_ne45 i hi).1.symm (by decide)]; exact h.row j hj hr'
  have hgx := xr_ne45 i hi
  by_cases h3 : r = 3 ∧ i = 0
  · obtain ⟨rfl, rfl⟩ := h3
    have e := (ea_gpr h.gpr _).trans (hc.eaB ctrOff (by decide))
    have i5 : InRegions (s.rd ++ s.wr) (buf + BitVec.ofNat 64 ctrOff) 16 := by
      rw [h.rd, h.wr]; exact in_buf hc.wb (by decide)
    rw [show addWord4 3 0 = [.movdquLoad .xmm5 (at_ .edi ctrOff), xb .paddd .xmm0 .xmm5] from rfl]
    apply WP.of_runBlock
    simp only [xb, xr, runBlock_cons, runStep_some, runBlock_nil, exec,
      XOp.exec, State.load128, e, i5, ite_true, RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
      RegUpd.gpr_setXmm, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun l hl => ?_, fun x h0 h5 => ?_, trivial, trivial, trivial, trivial⟩
    · simp only [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true,
        dword_paddd _ _ hl]
      rw [lane_load _ _ _ hl, h.mem, hct l hl, ctr_get _ _ (by decide), ite_eq_left rfl]
    · simp only [RegUpd.xmm_setXmm_of_ne, h0, h5, not_false_eq_true]
  · apply WP.of_runBlock
    simp only [addWord4, h3, ite_false, xb, bcast, runBlock_cons, runStep_some, runBlock_nil, exec,
      XOp.exec, RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.gpr_setXmm,
      Option.some.injEq, exists_eq_left']
    refine ⟨fun l hl => ?_, fun x h0 h5 => ?_, trivial, trivial, trivial, trivial⟩
    · rw [RegUpd.xmm_setXmm_self, dword_paddd _ _ hl, RegUpd.xmm_setXmm_of_ne _ _ hgx.2,
        RegUpd.xmm_setXmm_self, dword_shufDwords_bcast _ hi hl, h.row i hi hr,
        ctr_get _ _ (by omega), ite_eq_right (by omega)]
    · rw [RegUpd.xmm_setXmm_of_ne _ _ h0, RegUpd.xmm_setXmm_of_ne _ _ h5]

/-! ## Transposing -/

theorem transpose_ok (s : State) :
    WP isa (.block transpose) s fun s' =>
      (∀ l, l < 4 → ∀ j, j < 4 → dword (s'.xmm (outReg l)) j = dword (s.xmm (xr j)) l) ∧
      s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [transpose, xb, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.gpr_setXmm,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl j hj => ?_, trivial, trivial, trivial, trivial⟩
  rcases cases4 hl with rfl | rfl | rfl | rfl <;>
    simp only [outReg, xr, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq,
      not_false_eq_true, eval_movdqa, punpcklqdq_eq, punpckhqdq_eq, punpckldq_eq, punpckhdq_eq,
      dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3] <;>
    rcases cases4 hj with rfl | rfl | rfl | rfl <;>
    simp only [dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]

/-! ## XORing 16 bytes into the data -/

/-- The 256 bytes of data of one iteration. -/
abbrev dW (a : Addr) : Region := ⟨a, 256⟩

/-- Where `esi` points (the data of the iteration), and that the code may
write it. -/
structure DCtx (a : Addr) (s : State) : Prop where
  eaD : ∀ d, d < 256 → s.ea (at_ .esi d) = a + BitVec.ofNat 64 d
  wd : ∀ off n, off + n ≤ 256 → InRegions s.wr (a + BitVec.ofNat 64 off) n

theorem DCtx.of {a : Addr} {s s' : State} (h : DCtx a s) (hg : s'.gpr = s.gpr) (hw : s'.wr = s.wr) :
    DCtx a s' :=
  ⟨fun d hd => (ea_gpr hg _).trans (h.eaD d hd), fun off n h' => hw ▸ h.wd off n h'⟩

/-- A byte of the data after a 16-byte write at offset `off`. -/
theorem byte_write16 (m : Mem) (a : Addr) (v : BitVec 128) {off k : Nat} (ho : off + 16 ≤ 256)
    (hk : k < 256) : (m.writeW (a + BitVec.ofNat 64 off) v) (a + BitVec.ofNat 64 k) =
      if off ≤ k ∧ k < off + 16 then v.extractLsb' (8 * (k - off)) 8 else m (a + BitVec.ofNat 64 k) := by
  by_cases h : off ≤ k ∧ k < off + 16
  · rw [ite_eq_left h, show a + BitVec.ofNat 64 k = a + BitVec.ofNat 64 off + BitVec.ofNat 64 (k - off) by
      rw [Offset.add_add, Nat.add_sub_cancel' h.1]]
    exact writeW_byte _ _ _ (by omega) (by lit_omega)
  · rw [ite_eq_right h]
    refine writeW_byte_off _ _ _ _ ?_
    rw [Offset.sub_toNat' a (by lit_omega) (by lit_omega)]
    split <;> omega

theorem xor16_ok {x : XReg} (hx : x ≠ .xmm6) {off : Nat} (ho : off + 16 ≤ 256) {a : Addr}
    {s : State} (hd : DCtx a s) :
    WP isa (.block (xor16 x off)) s fun s' =>
      (∀ k, k < 256 → s'.mem (a + BitVec.ofNat 64 k) = if off ≤ k ∧ k < off + 16 then
        s.mem (a + BitVec.ofNat 64 k) ^^^ (s.xmm x).extractLsb' (8 * (k - off)) 8
        else s.mem (a + BitVec.ofNat 64 k)) ∧
      Frame [dW a] s.mem s'.mem ∧ (∀ r, r ≠ .xmm6 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := hd.eaD off (by omega)
  have o : InRegions s.wr (a + BitVec.ofNat 64 off) 16 := hd.wd off 16 ho
  have i : InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 off) 16 :=
    let ⟨r, hr, hc⟩ := o; ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.of_runBlock
  simp only [xor16, xb, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, State.load128,
    State.store128, ea_setXmm, e, i, RegUpd.wr_setXmm, o, ite_true, RegUpd.mem_setXmm,
    RegUpd.gpr_setXmm, RegUpd.rd_setXmm, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun k hk => ?_, (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains_base a ho (by lit_omega)), fun r hr => ?_, trivial, trivial, trivial⟩
  · rw [byte_write16 _ _ _ ho hk]
    by_cases h : off ≤ k ∧ k < off + 16
    · rw [ite_eq_left h, ite_eq_left h]
      simp only [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ hx, XBinOp.eval]
      rw [BitVec.extractLsb'_xor, byte_readW _ _ (by omega), Offset.add_add, Nat.add_sub_cancel' h.1]
    · rw [ite_eq_right h, ite_eq_right h]
  · rw [RegUpd.xmm_setXmm_of_ne _ _ hr, RegUpd.xmm_setXmm_of_ne _ _ hr]

/-! ## XORing a row of the four blocks -/

theorem outReg_ne6 : ∀ l, l < 4 → outReg l ≠ .xmm6 := by decide

/-- Byte `k % 64` of a serialized state, in row `r`. -/
theorem serialize_row (S : CState) {k r : Nat} (hk : k % 64 / 16 = r) :
    (serialize S).getD (k % 64) 0 =
      (S[4 * r + k % 16 / 4]'(by omega)).extractLsb' (8 * (k % 16 % 4)) 8 := by
  rw [serialize_getD _ (Nat.mod_lt _ (by decide)), getElem_congr_idx (show k % 64 / 4 = 4 * r + k % 16 / 4 by omega),
    show k % 64 % 4 = k % 16 % 4 by omega]

/-- While XORing row `r` of the four blocks `B`: the blocks below `l` are
done, the registers `outReg l'` hold row `r` of the blocks, and only the
data has been written since `s₁`. -/
structure XO (a : Addr) (B : Nat → CState) (r l : Nat) (s₁ s : State) : Prop where
  data : ∀ k, k < 256 → s.mem (a + BitVec.ofNat 64 k) =
    if k % 64 / 16 = r ∧ k / 64 < l then
      s₁.mem (a + BitVec.ofNat 64 k) ^^^ (serialize (B (k / 64))).getD (k % 64) 0
    else s₁.mem (a + BitVec.ofNat 64 k)
  regs : ∀ l', l' < 4 → ∀ j (hj : j < 4) (hr : r < 4), dword (s.xmm (outReg l')) j = (B l')[4 * r + j]
  frame : Frame [dW a] s₁.mem s.mem
  gpr : s.gpr = s₁.gpr
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr

theorem xorOut_ok {a : Addr} {B : Nat → CState} {r l : Nat} (hr : r < 4) (hl : l < 4) {s₁ s : State}
    (hd : DCtx a s₁) (h : XO a B r l s₁ s) :
    WP isa (.block (xor16 (outReg l) (64 * l + 16 * r))) s (XO a B r (l + 1) s₁) := by
  refine WP.mono (xor16_ok (outReg_ne6 l hl) (off := 64 * l + 16 * r) (by omega) (hd.of h.gpr h.wr))
    fun s' ⟨hm, hf, hx, hg, hrd, hwr⟩ => ⟨fun k hk => ?_, fun l' hl' j hj hr' => ?_, h.frame.trans hf,
      hg.trans h.gpr, hrd.trans h.rd, hwr.trans h.wr⟩
  · rw [hm k hk, h.data k hk]
    by_cases hin : 64 * l + 16 * r ≤ k ∧ k < 64 * l + 16 * r + 16
    · have c₁ : ¬ (k % 64 / 16 = r ∧ k / 64 < l) := by omega
      have c₂ : k % 64 / 16 = r ∧ k / 64 < l + 1 := by omega
      rw [ite_eq_left hin, ite_eq_right c₁, ite_eq_left c₂, show k / 64 = l by omega,
        serialize_row _ c₂.1, show k - (64 * l + 16 * r) = k % 16 by omega, byte_dword,
        h.regs l hl _ (by omega) hr]
    · rw [ite_eq_right hin]
      by_cases c : k % 64 / 16 = r ∧ k / 64 < l
      · rw [ite_eq_left c, ite_eq_left (by omega)]
      · rw [ite_eq_right c, ite_eq_right (by omega)]
  · rw [hx _ (outReg_ne6 l' hl')]; exact h.regs l' hl' j hj hr'

/-! ## The whole output -/

/-- Block `l` of the four: the rounds' result `vs l` plus the input state `ctr C l`. -/
abbrev blk (vs : Nat → CState) (C : CState) (l : Nat) : CState :=
  Vector.zipWith (· + ·) (vs l) (ctr C l)

/-- After rows below `r`: those rows of the four blocks are XORed into the
data, and only the data has been written since `s₀`. -/
structure FI (a : Addr) (B : Nat → CState) (r : Nat) (s₀ s : State) : Prop where
  data : ∀ k, k < 256 → s.mem (a + BitVec.ofNat 64 k) =
    if k % 64 / 16 < r then
      s₀.mem (a + BitVec.ofNat 64 k) ^^^ (serialize (B (k / 64))).getD (k % 64) 0
    else s₀.mem (a + BitVec.ofNat 64 k)
  frame : Frame [dW a] s₀.mem s.mem
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

section
variable {st buf a : Addr} {vs : Nat → CState} {C : CState} {s₀ : State} (hc : Ctx st buf s₀)
  (hd : DCtx a s₀) (hh : Holds4 buf vs s₀.mem) (hct : Ctrs buf C 4 s₀.mem)
  (hC : stateAt s₀.mem st = C) (db : (dW a).Disjoint (bufR buf)) (ds : (dW a).Disjoint (stR st))
include hc hd hh hct hC db ds

theorem finishRow_ok {r : Nat} (hr : r < 4) {s : State} (h : FI a (blk vs C) r s₀ s) :
    WP isa (.block (finishRow r)) s (FI a (blk vs C) (r + 1) s₀) := by
  have dbuf : ∀ r' ∈ [dW a], (bufR buf).Disjoint r' := by
    simp only [List.mem_singleton, forall_eq]; exact db.symm
  have hh' : Holds4 buf vs s.mem := fun k hk l hl => by
    rw [h.frame.readW (r := bufR buf) (Offset.contains_base buf (by omega) (by lit_omega)) dbuf
      (by decide)]
    exact hh k hk l hl
  have hct' : Ctrs buf C 4 s.mem := fun l hl => by
    rw [h.frame.readW (r := bufR buf) (Offset.contains_base buf (by simp only [ctrOff]; omega)
      (by simp only [ctrOff]; lit_omega)) dbuf (by decide)]
    exact hct l hl
  have hC' : stateAt s.mem st = C := (stateAt_frame h.frame (by
    simp only [List.mem_singleton, forall_eq]; exact ds.symm)).trans hC
  have hcs := hc.of h.gpr h.wr
  rw [finishRow, WP.block_append_iff]
  refine WP.mono (loadRow_ok hr hcs hh') fun s₁ ⟨hreg, hrow, hm₁, hg₁, hrd₁, hwr₁⟩ => ?_
  rw [WP.block_append_iff]
  have aw₀ : AW vs C r 0 s₁ s₁ :=
    ⟨fun j hj _ l hl => by rw [ite_eq_right (Nat.not_lt_zero _)]; exact hreg j hj l hl,
      by rw [hC'] at hrow; exact hrow, rfl, rfl, rfl, rfl⟩
  refine WP.mono (wp_range_flatMap (M := isa) (fun i s => AW vs C r i s₁ s)
    (fun i s hi hs => addWord_ok hr hi (hcs.of hg₁ hwr₁) (hm₁ ▸ hct') hs) 4 (Nat.le_refl _) s₁ aw₀)
    fun s₂ h₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (transpose_ok s₂) fun s₃ ⟨ht, hm₃, hg₃, hrd₃, hwr₃⟩ => ?_
  have xo₀ : XO a (blk vs C) r 0 s₃ s₃ :=
    ⟨fun k _ => by rw [ite_eq_right (by omega)], fun l' hl' j hj hr' => by
      rw [ht l' hl' j hj, h₂.regs j hj hr' l' hl', ite_eq_left hj, Vector.getElem_zipWith],
      Frame.refl _ _, rfl, rfl, rfl⟩
  have hd₃ : DCtx a s₃ := (hd.of h.gpr h.wr).of (by rw [hg₃, h₂.gpr, hg₁]) (by rw [hwr₃, h₂.wr, hwr₁])
  refine WP.mono (wp_range_flatMap (M := isa) (fun l s => XO a (blk vs C) r l s₃ s)
    (fun l s hl hs => xorOut_ok hr hl hd₃ hs) 4 (Nat.le_refl _) s₃ xo₀) fun s₄ h₄ => ?_
  have hm : s₃.mem = s.mem := by rw [hm₃, h₂.mem, hm₁]
  refine ⟨fun k hk => ?_, ?_, ?_, ?_, ?_⟩
  · rw [h₄.data k hk, hm, h.data k hk]
    by_cases c : k % 64 / 16 = r
    · rw [ite_eq_left ⟨c, by omega⟩, ite_eq_right (by omega), ite_eq_left (by omega)]
    · rw [ite_eq_right (by omega)]
      by_cases c' : k % 64 / 16 < r
      · rw [ite_eq_left c', ite_eq_left (by omega)]
      · rw [ite_eq_right c', ite_eq_right (by omega)]
  · exact h.frame.trans (hm ▸ h₄.frame)
  · rw [h₄.gpr, hg₃, h₂.gpr, hg₁, h.gpr]
  · rw [h₄.rd, hrd₃, h₂.rd, hrd₁, h.rd]
  · rw [h₄.wr, hwr₃, h₂.wr, hwr₁, h.wr]

theorem finish4_ok : WP isa (.block finish4) s₀ (FI a (blk vs C) 4 s₀) :=
  wp_range_flatMap (M := isa) (fun r s => FI a (blk vs C) r s₀ s)
    (fun r s hr hs => finishRow_ok hc hd hh hct hC db ds hr hs) 4 (Nat.le_refl _) s₀
    ⟨fun k _ => by rw [ite_eq_right (Nat.not_lt_zero _)], Frame.refl _ _, rfl, rfl, rfl⟩

end

end VG.Proof.ChaCha20.X86.Quad
