import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Setup
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Layout

/-!
# Ed448's complete operations on AArch64: the state in the frame's body

An `Env` is where a complete operation's buffers are: the frame's base `E`,
the regions it reads (`ins`, with the saved arguments) and writes (`outs`),
and the words kept in its locals (`ls`). `WCtx` is `Whole.Ctx` with the kept
words in place. A call (`wcall`) or a block (`WCtx.of_frame`) that writes
only regions disjoint from the kept words keeps `WCtx`; `wsetup` sets a
call's arguments.
-/

namespace VG.Proof.Ed448.AArch64.Whole

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Whole
open VG.Proof.Ed25519.AArch64.Whole (Within FR ARGS CK)

structure Env where
  E : Addr
  ins : List Region
  outs : List Region
  ls : List (Nat × BitVec 64)

/-- A kept word's region. -/
abbrev slot (E : Addr) (d : Nat) : Region := ⟨E + BitVec.ofNat 64 d, 8⟩

/-- What the layout guarantees. -/
structure Env.Ok (V : Env) : Prop where
  args : ARGS V.E ∈ V.ins
  ls : ∀ p ∈ V.ls, p.1 % 8 = 0 ∧ p.1 + 8 ≤ 256
  fo : ∀ R ∈ V.outs, (FR V.E).Disjoint R
  co : ∀ R ∈ V.outs, (CK V.E).Disjoint R
  e16 : 16 ≤ V.E.toNat

abbrev WCtx (V : Env) (g : Reg → Addr) (vec : VReg → BitVec 128) (m₀ : Mem) (t : State) : Prop :=
  VG.Proof.Ed25519.AArch64.Whole.Ctx V.E g vec m₀ V.ins V.outs t ∧ Kept V.E t.mem V.ls

variable {V : Env} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t u : State}

theorem slot_sub_fr (E : Addr) {d : Nat} (h : d + 8 ≤ 256) : Region.Sub (slot E d) (FR E) :=
  Offset.sub_base _ h

theorem slot_ck (E : Addr) {d : Nat} (h : d + 8 ≤ 256) : (slot E d).Disjoint (CK E) :=
  ((Offset.below_disjoint E (m := 16) (l := 256) (by decide)).sub_right (slot_sub_fr E h)).symm

/-- A region within the locals, apart from the kept words. -/
def Apart (V : Env) (r : Region) : Prop := Within r (FR V.E) ∧ ∀ p ∈ V.ls, (slot V.E p.1).Disjoint r

/-- Writes within `outs`, the locals apart from the kept words, and the frame of a callee. -/
theorem kept_frame (hV : V.Ok) {m m' : Mem} (h : Kept V.E m V.ls) {ws : List Region}
    (hf : Frame (ws ++ [CK V.E]) m m') (hw : ∀ r ∈ ws, Apart V r ∨ ∃ R ∈ V.outs, Within r R) :
    Kept V.E m' V.ls := by
  refine h.frame hf fun p hp r hr => ?_
  have hl := hV.ls p hp
  rcases List.mem_append.mp hr with hr | hr
  · rcases hw r hr with ⟨_, hd⟩ | ⟨R, hR, hs⟩
    · exact hd p hp
    · exact ((hV.fo R hR).sub_left (slot_sub_fr _ hl.2)).sub_right hs.sub
  · rw [List.mem_singleton.mp hr]
    exact slot_ck _ hl.2

theorem WCtx.of_frame (hV : V.Ok) (h : WCtx V g vec m₀ t)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hsp : u.sp = t.sp)
    (hcs : ∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r)
    (hvs : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64)
    {ws : List Region} (hf : Frame ws t.mem u.mem)
    (hw : ∀ r ∈ ws, Apart V r ∨ ∃ R ∈ V.outs, Within r R) : WCtx V g vec m₀ u := by
  refine ⟨h.1.of_frame hrd hwr hsp hcs hvs hf fun r hr => ?_, kept_frame hV h.2
    (hf.mono fun r hr => List.mem_append_left _ hr) hw⟩
  rcases hw r hr with ⟨hf, _⟩ | ⟨R, hR, hs⟩
  · exact .inl hf.sub
  · exact .inr ⟨R, hR, hs.sub⟩

theorem WCtx.regs (h : WCtx V g vec m₀ t)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hsp : u.sp = t.sp)
    (hcs : ∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r)
    (hvs : u.v = t.v) (hm : u.mem = t.mem) : WCtx V g vec m₀ u :=
  ⟨h.1.regs hrd hwr hsp hcs hvs hm, hm ▸ h.2⟩

/-- A call's arguments, from the saved arguments, the kept words and `x0`. -/
theorem wsetup_ok (hV : V.Ok) (hc : WCtx V g vec m₀ t) {args : List (Reg × Src)}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, srcValid p.2) (hret : retOk args = true)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (setupS args)) t fun u => WCtx V g vec m₀ u ∧ u.mem = t.mem ∧
      ∀ p ∈ args, u.gpr p.1 = srcValue V.E t.mem (t.gpr .x0) p.2 := by
  refine WP.mono (setupS_ok hc.1.sp hn hv hret ?_ ?_) fun u ⟨ht, hvals⟩ => ?_
  · intro j hj
    rw [hc.1.rd, hc.1.wr]
    refine ⟨ARGS V.E, List.mem_append_left _ hV.args, ?_⟩
    have ha : V.E + BitVec.ofNat 64 (256 + 8 * j) = V.E + 256 + BitVec.ofNat 64 (8 * j) := by
      rw [BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    rw [ha]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
  · intro d _ hd
    exact hc.1.readable_frame (Offset.contains_base _ hd (by omega))
  refine ⟨hc.regs ht.rd ht.wr ht.sp ?_ ht.vec ht.mem, ht.mem, hvals⟩
  intro r hpres _
  apply ht.regs
  intro hm
  obtain ⟨p, hp, heq⟩ := List.mem_map.mp hm
  exact hr p hp (heq ▸ hpres)

/-- A call of verified code with at most one frame. -/
theorem wcall (hV : V.Ok) (h : WCtx V g vec m₀ t)
    {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ trace s', Exec isa c s trace s' ∧ abiPreserved s s' ∧ k.post s s')
    (hd : c.aarch64Depth ≤ 1)
    {rd' wr' : List Region} (hpre : k.pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (V.ins ++ FR V.E :: V.outs))
    (hw : ∀ r ∈ wr', Apart V r ∨ ∃ R ∈ V.outs, Within r R)
    {Q : State → Prop}
    (hQ : ∀ u, WCtx V g vec m₀ u → Frame (wr' ++ [CK V.E]) t.mem u.mem →
      k.post (t.callEntry.withRegions rd' wr') (u.withRegions rd' wr') → Q u) :
    WP isa (.call name c) t Q :=
  VG.Proof.Ed25519.AArch64.Whole.call_okF h.1 hv hd hpre hcov
    (fun r hr => (hw r hr).imp And.left id) fun u hu hf hp =>
      hQ u ⟨hu, kept_frame hV h.2 hf hw⟩ hf hp

theorem covers_of {E : Addr} {ins outs rs : List Region}
    (h : ∀ r ∈ rs, Within r (FR E) ∨ ∃ R ∈ ins ++ outs, Within r R) :
    Covers rs (ins ++ FR E :: outs) := by
  apply Covers.of_sub
  intro r hr
  rcases h r hr with hf | ⟨R, hR, hsub⟩
  · exact ⟨FR E, List.mem_append_right _ List.mem_cons_self, hf⟩
  · refine ⟨R, ?_, hsub⟩
    rcases List.mem_append.mp hR with hi | ho
    · exact List.mem_append_left _ hi
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ ho)

end VG.Proof.Ed448.AArch64.Whole
