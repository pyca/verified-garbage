import VerifiedGarbage.Impl.Ed448.AArch64.Whole
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ed448.AArch64.ScalarVerified
import VerifiedGarbage.Proof.Ed448.AArch64.BaseContract
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyVerified
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.Sha3
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Spec.Ed448.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.Whole.Setup`. -/
section

/-!
# Ed448's complete operations on AArch64: a call's arguments

`setupS args` sets each register to its `Src`'s value (`srcValue`): as
`Whole.setup` does, a word of the locals plus an offset, or `x0` as it was
before (`retOk`: nothing before a `ret` writes `x0`). The locals hold words
the function keeps there (`Kept`), which a write elsewhere leaves
(`Kept.frame`).
-/

namespace VG.Proof.Ed448.AArch64.Whole

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Whole
open VG.Impl.Ed25519.AArch64.Whole (Value setArg)
open VG.Proof.Ed25519.AArch64.Whole (SetupStep)

/-- The value `setSrc` sets, from the frame's base `E`, the memory, and `x0`. -/
def srcValue (E : Addr) (m : Mem) (x0 : BitVec 64) : VG.Impl.Ed448.AArch64.Whole.Src → BitVec 64
  | .val v => VG.Proof.Ed25519.AArch64.Whole.value E m v
  | .loc d o => m.read (E + BitVec.ofNat 64 d) 8 + BitVec.ofNat 64 o
  | .ret => x0

def srcValid : VG.Impl.Ed448.AArch64.Whole.Src → Prop
  | .val v => VG.Proof.Ed25519.AArch64.Whole.valid v
  | .loc d o => d % 8 = 0 ∧ d + 8 ≤ 256 ∧ o < 4096
  | .ret => True

def noRet : VG.Impl.Ed448.AArch64.Whole.Src → Bool
  | .ret => false
  | _ => true

/-- Nothing before a `ret` writes `x0`. -/
def retOk : List (Reg × VG.Impl.Ed448.AArch64.Whole.Src) → Bool
  | [] => true
  | (r, _) :: ps => (r != .x0 || ps.all fun p => VG.Proof.Ed448.AArch64.Whole.noRet p.2) && VG.Proof.Ed448.AArch64.Whole.retOk ps

theorem srcValue_noRet {E : Addr} {m : Mem} {a b : BitVec 64} {v : VG.Impl.Ed448.AArch64.Whole.Src} (h : VG.Proof.Ed448.AArch64.Whole.noRet v = true) :
    VG.Proof.Ed448.AArch64.Whole.srcValue E m a v = VG.Proof.Ed448.AArch64.Whole.srcValue E m b v := by
  cases v <;> first | rfl | simp [VG.Proof.Ed448.AArch64.Whole.noRet] at h

theorem setSrc_ok {s : State} {E : Addr} {r : Reg} {v : VG.Impl.Ed448.AArch64.Whole.Src} (he : s.sp = E) (hv : VG.Proof.Ed448.AArch64.Whole.srcValid v)
    (hr : ∀ j d, v = .val (.caller j d) → InRegions (s.rd ++ s.wr) (E + BitVec.ofNat 64 (256 + 8 * j)) 8)
    (hl : ∀ d o, v = .loc d o → InRegions (s.rd ++ s.wr) (E + BitVec.ofNat 64 d) 8) :
    WP isa (.block (setSrc r v)) s fun t => SetupStep [r] s t ∧ t.gpr r = VG.Proof.Ed448.AArch64.Whole.srcValue E s.mem (s.gpr .x0) v := by
  cases v with
  | val v =>
    exact WP.mono (VG.Proof.Ed25519.AArch64.Whole.setArg_ok he hv (fun j d h => hr j d (by rw [h])))
      fun t ⟨h1, h2⟩ => ⟨h1, h2⟩
  | loc d o =>
    obtain ⟨hd8, hdl, ho⟩ := hv
    have ha : d % 8 = 0 ∧ d < 32768 := ⟨hd8, by omega⟩
    have hr' := hl d o rfl
    apply WP.of_runBlock
    simp only [setSrc, VG.Proof.Ed448.AArch64.Whole.srcValue, runBlock_cons, runStep_some, runBlock_nil, exec,
      ha.1, ha.2, and_self, ho, ite_true, he, State.load, hr', Option.map_some, State.read,
      Size.bits, BitVec.setWidth_eq, RegUpd.gpr_write_self,
      Option.some.injEq, exists_eq_left']
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, ?_⟩, ?_⟩
    · intro q hq
      have hqr : q ≠ r := by simpa using hq
      rw [RegUpd.gpr_write_of_ne _ _ _ hqr, RegUpd.gpr_write_of_ne _ _ _ hqr]
    · exact True.intro
  | ret =>
    apply WP.of_runBlock
    simp only [setSrc, VG.Proof.Ed448.AArch64.Whole.srcValue, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
      Nat.reduceLT, ite_true, BitVec.setWidth_eq, BitVec.add_zero, RegUpd.gpr_write_self,
      Option.some.injEq, exists_eq_left']
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, ?_⟩, trivial⟩
    intro q hq
    exact RegUpd.gpr_write_of_ne s .x _ (by simpa using hq)

/-- The arguments set, from the frame `E` and the memory and `x0` before. -/
theorem setupS_ok {s : State} {E : Addr} {args : List (Reg × VG.Impl.Ed448.AArch64.Whole.Src)}
    (he : s.sp = E) (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, VG.Proof.Ed448.AArch64.Whole.srcValid p.2)
    (hret : VG.Proof.Ed448.AArch64.Whole.retOk args = true)
    (hr : ∀ j < 6, InRegions (s.rd ++ s.wr) (E + BitVec.ofNat 64 (256 + 8 * j)) 8)
    (hl : ∀ d, d % 8 = 0 → d + 8 ≤ 256 → InRegions (s.rd ++ s.wr) (E + BitVec.ofNat 64 d) 8) :
    WP isa (.block (setupS args)) s fun t => SetupStep (args.map Prod.fst) s t ∧
      ∀ p ∈ args, t.gpr p.1 = VG.Proof.Ed448.AArch64.Whole.srcValue E s.mem (s.gpr .x0) p.2 := by
  induction args generalizing s with
  | nil => exact WP.block_nil ⟨SetupStep.refl s, fun _ h => by cases h⟩
  | cons p ps ih =>
    obtain ⟨r, v⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [VG.Proof.Ed448.AArch64.Whole.retOk, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hret
    rw [setupS, List.flatMap_cons, WP.block_append_iff]
    have hv0 := hv (r, v) List.mem_cons_self
    refine WP.mono (VG.Proof.Ed448.AArch64.Whole.setSrc_ok he hv0 ?_ ?_) fun u ⟨hu, hval⟩ => ?_
    · intro j d h
      subst v
      exact hr j hv0.1
    · intro d o h
      subst v
      exact hl d hv0.1 hv0.2.1
    refine WP.mono (ih (hu.sp.trans he) hn.2
      (fun p hp => hv p (List.mem_cons_of_mem _ hp)) hret.2 ?_ ?_) fun t ⟨ht, hvals⟩ => ?_
    · intro j hj
      rw [hu.rd, hu.wr]
      exact hr j hj
    · intro d hd hdl
      rw [hu.rd, hu.wr]
      exact hl d hd hdl
    refine ⟨hu.trans ht, ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact (ht.regs _ hn.1).trans hval
    · rw [hvals p hp, hu.mem]
      rcases hret.1 with h0 | hall
      · rw [hu.regs .x0 (by simpa using fun h => h0 h.symm)]
      · exact VG.Proof.Ed448.AArch64.Whole.srcValue_noRet (List.all_eq_true.mp hall p hp)

/-! ## Words kept in the locals -/

/-- The locals hold the words `ls` (offset, value). -/
def Kept (E : Addr) (m : Mem) (ls : List (Nat × BitVec 64)) : Prop :=
  ∀ p ∈ ls, m.read (E + BitVec.ofNat 64 p.1) 8 = p.2

/-- Writes that miss the kept words leave them. -/
theorem Kept.frame {E : Addr} {m m' : Mem} {ls : List (Nat × BitVec 64)} (h : VG.Proof.Ed448.AArch64.Whole.Kept E m ls)
    {ws : List Region} (hf : VG.Frame ws m m')
    (hd : ∀ p ∈ ls, ∀ r ∈ ws, Region.Disjoint ⟨E + BitVec.ofNat 64 p.1, 8⟩ r) : VG.Proof.Ed448.AArch64.Whole.Kept E m' ls :=
  fun p hp => (hf.read (Region.contains_self _ _) (hd p hp) (by decide)).trans (h p hp)

/-- A kept word, as a `loc` argument. -/
theorem srcValue_loc {E : Addr} {m : Mem} {x0 : BitVec 64} {ls : List (Nat × BitVec 64)} (h : VG.Proof.Ed448.AArch64.Whole.Kept E m ls)
    {d : Nat} {w : BitVec 64} (hm : (d, w) ∈ ls) (o : Nat) :
    VG.Proof.Ed448.AArch64.Whole.srcValue E m x0 (.loc d o) = w + BitVec.ofNat 64 o := by
  simp only [VG.Proof.Ed448.AArch64.Whole.srcValue]
  rw [h _ hm]

end VG.Proof.Ed448.AArch64.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.Whole.Ctx`. -/
section

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
structure Env.Ok (V : VG.Proof.Ed448.AArch64.Whole.Env) : Prop where
  args : ARGS V.E ∈ V.ins
  ls : ∀ p ∈ V.ls, p.1 % 8 = 0 ∧ p.1 + 8 ≤ 256
  fo : ∀ R ∈ V.outs, (FR V.E).Disjoint R
  co : ∀ R ∈ V.outs, (CK V.E).Disjoint R
  e16 : 16 ≤ V.E.toNat

abbrev WCtx (V : VG.Proof.Ed448.AArch64.Whole.Env) (g : Reg → Addr) (vec : VReg → BitVec 128) (m₀ : Mem) (t : State) : Prop :=
  VG.Proof.Ed25519.AArch64.Whole.Ctx V.E g vec m₀ V.ins V.outs t ∧ VG.Proof.Ed448.AArch64.Whole.Kept V.E t.mem V.ls

variable {V : VG.Proof.Ed448.AArch64.Whole.Env} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t u : State}

theorem slot_sub_fr (E : Addr) {d : Nat} (h : d + 8 ≤ 256) : Region.Sub (VG.Proof.Ed448.AArch64.Whole.slot E d) (FR E) :=
  Offset.sub_base _ h

theorem slot_ck (E : Addr) {d : Nat} (h : d + 8 ≤ 256) : (VG.Proof.Ed448.AArch64.Whole.slot E d).Disjoint (CK E) :=
  ((Offset.below_disjoint E (m := 16) (l := 256) (by decide)).sub_right (VG.Proof.Ed448.AArch64.Whole.slot_sub_fr E h)).symm

/-- A region within the locals, apart from the kept words. -/
def Apart (V : VG.Proof.Ed448.AArch64.Whole.Env) (r : Region) : Prop := VG.Proof.Ed25519.AArch64.Whole.Within r (FR V.E) ∧ ∀ p ∈ V.ls, (VG.Proof.Ed448.AArch64.Whole.slot V.E p.1).Disjoint r

/-- Writes within `outs`, the locals apart from the kept words, and the frame of a callee. -/
theorem kept_frame (hV : V.Ok) {m m' : Mem} (h : VG.Proof.Ed448.AArch64.Whole.Kept V.E m V.ls) {ws : List Region}
    (hf : VG.Frame (ws ++ [CK V.E]) m m') (hw : ∀ r ∈ ws, VG.Proof.Ed448.AArch64.Whole.Apart V r ∨ ∃ R ∈ V.outs, VG.Proof.Ed25519.AArch64.Whole.Within r R) :
    VG.Proof.Ed448.AArch64.Whole.Kept V.E m' V.ls := by
  refine h.frame hf fun p hp r hr => ?_
  have hl := hV.ls p hp
  rcases List.mem_append.mp hr with hr | hr
  · rcases hw r hr with ⟨_, hd⟩ | ⟨R, hR, hs⟩
    · exact hd p hp
    · exact ((hV.fo R hR).sub_left (VG.Proof.Ed448.AArch64.Whole.slot_sub_fr _ hl.2)).sub_right hs.sub
  · rw [List.mem_singleton.mp hr]
    exact VG.Proof.Ed448.AArch64.Whole.slot_ck _ hl.2

theorem WCtx.of_frame (hV : V.Ok) (h : VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ t)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hsp : u.sp = t.sp)
    (hcs : ∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r)
    (hvs : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64)
    {ws : List Region} (hf : VG.Frame ws t.mem u.mem)
    (hw : ∀ r ∈ ws, VG.Proof.Ed448.AArch64.Whole.Apart V r ∨ ∃ R ∈ V.outs, VG.Proof.Ed25519.AArch64.Whole.Within r R) : VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ u := by
  refine ⟨h.1.of_frame hrd hwr hsp hcs hvs hf fun r hr => ?_, VG.Proof.Ed448.AArch64.Whole.kept_frame hV h.2
    (hf.mono fun r hr => List.mem_append_left _ hr) hw⟩
  rcases hw r hr with ⟨hf, _⟩ | ⟨R, hR, hs⟩
  · exact .inl hf.sub
  · exact .inr ⟨R, hR, hs.sub⟩

theorem WCtx.regs (h : VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ t)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hsp : u.sp = t.sp)
    (hcs : ∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r)
    (hvs : u.v = t.v) (hm : u.mem = t.mem) : VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ u :=
  ⟨h.1.regs hrd hwr hsp hcs hvs hm, hm ▸ h.2⟩

/-- A call's arguments, from the saved arguments, the kept words and `x0`. -/
theorem wsetup_ok (hV : V.Ok) (hc : VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ t) {args : List (Reg × VG.Impl.Ed448.AArch64.Whole.Src)}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, VG.Proof.Ed448.AArch64.Whole.srcValid p.2) (hret : VG.Proof.Ed448.AArch64.Whole.retOk args = true)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (setupS args)) t fun u => VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ u ∧ u.mem = t.mem ∧
      ∀ p ∈ args, u.gpr p.1 = VG.Proof.Ed448.AArch64.Whole.srcValue V.E t.mem (t.gpr .x0) p.2 := by
  refine WP.mono (VG.Proof.Ed448.AArch64.Whole.setupS_ok hc.1.sp hn hv hret ?_ ?_) fun u ⟨ht, hvals⟩ => ?_
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
theorem wcall (hV : V.Ok) (h : VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ t)
    {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ trace s', Exec isa c s trace s' ∧ abiPreserved s s' ∧ k.post s s')
    (hd : c.aarch64Depth ≤ 1)
    {rd' wr' : List Region} (hpre : k.pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (V.ins ++ FR V.E :: V.outs))
    (hw : ∀ r ∈ wr', VG.Proof.Ed448.AArch64.Whole.Apart V r ∨ ∃ R ∈ V.outs, VG.Proof.Ed25519.AArch64.Whole.Within r R)
    {Q : State → Prop}
    (hQ : ∀ u, VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ u → VG.Frame (wr' ++ [CK V.E]) t.mem u.mem →
      k.post (t.callEntry.withRegions rd' wr') (u.withRegions rd' wr') → Q u) :
    WP isa (.call name c) t Q :=
  VG.Proof.Ed25519.AArch64.Whole.call_okF h.1 hv hd hpre hcov
    (fun r hr => (hw r hr).imp And.left id) fun u hu hf hp =>
      hQ u ⟨hu, VG.Proof.Ed448.AArch64.Whole.kept_frame hV h.2 hf hw⟩ hf hp

theorem covers_of {E : Addr} {ins outs rs : List Region}
    (h : ∀ r ∈ rs, VG.Proof.Ed25519.AArch64.Whole.Within r (FR E) ∨ ∃ R ∈ ins ++ outs, VG.Proof.Ed25519.AArch64.Whole.Within r R) :
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

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.Whole.Calls`. -/
section

/-!
# Ed448's complete operations on AArch64: calls of the Ed448 primitives

`vg_ed448_scalar_reduce`, `vg_ed448_scalar_base`, `vg_ed448_scalar_mul_add` and
`vg_ed448_verify_equation`, called from the frame's body with their arguments
in their registers: the callee's precondition (`*_pre`), and its
postcondition after the call (`*_call`), which keeps `WCtx`.
-/

namespace VG.Proof.Ed448.AArch64.Whole

open VG VG.AArch64
open VG.Proof.Ed25519.AArch64.Whole (Within FR CK)

variable {V : Env} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {u : State}

/-- A region the body may read: within the locals, or a buffer. -/
abbrev Readable (V : Env) (r : Region) : Prop := Within r (FR V.E) ∨ ∃ R ∈ V.ins ++ V.outs, Within r R

/-- A region the body may write: within the locals but the kept words, or a written buffer. -/
abbrev Writable (V : Env) (r : Region) : Prop := Apart V r ∨ ∃ R ∈ V.outs, Within r R

theorem Writable.readable {r : Region} (h : Writable V r) : Readable V r := by
  rcases h with ⟨h, _⟩ | ⟨R, hR, hs⟩
  · exact .inl h
  · exact .inr ⟨R, List.mem_append_right _ hR, hs⟩

theorem covers_rw {rd wr : List Region} (hr : ∀ r ∈ rd, Readable V r) (hw : ∀ r ∈ wr, Writable V r) :
    Covers (rd ++ wr) (V.ins ++ FR V.E :: V.outs) :=
  covers_of fun r h => by
    rcases List.mem_append.mp h with h | h
    · exact hr r h
    · exact (hw r h).readable

theorem noFrames_depth {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth ≤ 1 :=
  VG.Proof.Ed25519.AArch64.Whole.depth_of_noFrames h

theorem reduce_noFrames : Impl.Ed448.AArch64.scalarReduce.noFrames = true := by lit_decide
theorem base_noFrames : Impl.Ed448.AArch64.scalarBase.noFrames = true :=
  Proof.Ed448.AArch64.scalarBase_noFrames
theorem mulAdd_noFrames : Impl.Ed448.AArch64.scalarMulAdd.noFrames = true := by lit_decide
theorem equation_noFrames : Impl.Ed448.AArch64.verifyEquation.noFrames = true :=
  Proof.Ed448.AArch64.verifyEquation_noFrames

/-! ## `vg_ed448_scalar_reduce(out, wide, scratch)` -/

theorem reduce_pre {op wp scr : Addr} (h0 : u.gpr .x0 = op) (h1 : u.gpr .x1 = wp) (h2 : u.gpr .x2 = scr)
    (hd : Region.Disjoint ⟨wp, 114⟩ ⟨scr, 8192⟩) :
    Proof.Ed448.AArch64.scalarReduceLocal.pre
      (u.callEntry.withRegions [⟨wp, 114⟩] [⟨op, 57⟩, ⟨scr, 8192⟩]) := by
  simp only [Proof.Ed448.AArch64.scalarReduceLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h0, h1, h2]
  exact ⟨trivial, trivial, hd⟩

theorem reduce_call (hV : V.Ok) (hu : WCtx V g vec m₀ u) {op wp scr : Addr}
    (h0 : u.gpr .x0 = op) (h1 : u.gpr .x1 = wp) (h2 : u.gpr .x2 = scr)
    (hd : Region.Disjoint ⟨wp, 114⟩ ⟨scr, 8192⟩) (hr : Readable V ⟨wp, 114⟩)
    (hwo : Writable V ⟨op, 57⟩) (hws : Writable V ⟨scr, 8192⟩) :
    WP isa (.call "vg_ed448_scalar_reduce" Impl.Ed448.AArch64.scalarReduce) u fun w =>
      WCtx V g vec m₀ w ∧ Frame ([⟨op, 57⟩, ⟨scr, 8192⟩] ++ [CK V.E]) u.mem w.mem ∧
      Spec.Ed448.bytesAt w.mem op 57 = Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt u.mem wp 114) := by
  have hw : ∀ r ∈ [(⟨op, 57⟩ : Region), ⟨scr, 8192⟩], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [hwo, hws]
  refine wcall hV hu Proof.Ed448.AArch64.scalarReduce_ok (noFrames_depth reduce_noFrames)
    (reduce_pre h0 h1 h2 hd) (covers_rw (by simpa using hr) hw) hw fun w hw' hf hp => ⟨hw', hf, ?_⟩
  change Spec.Ed448.bytesAt w.mem (u.callEntry.gpr .x0) 57 =
    Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x1) 114) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), h0, h1] at hp
  exact hp

/-! ## `vg_ed448_scalar_base(out, scalar, scratch)` -/

theorem base_pre {op sp scr : Addr} (h0 : u.gpr .x0 = op) (h1 : u.gpr .x1 = sp) (h2 : u.gpr .x2 = scr)
    (hos : Region.Disjoint ⟨op, 57⟩ ⟨scr, 8192⟩) (hss : Region.Disjoint ⟨sp, 57⟩ ⟨scr, 8192⟩)
    (hn : scr.toNat + 8192 ≤ 2 ^ 64) :
    Proof.Ed448.AArch64.scalarBaseLocal.pre (u.callEntry.withRegions [⟨sp, 57⟩] [⟨op, 57⟩, ⟨scr, 8192⟩]) := by
  simp only [Proof.Ed448.AArch64.scalarBaseLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h0, h1, h2]
  exact ⟨trivial, trivial, hos, hss, hn⟩

theorem base_call (hb : Proof.Ed448.AArch64.BaseOk) (hV : V.Ok) (hu : WCtx V g vec m₀ u) {op sp scr : Addr}
    (h0 : u.gpr .x0 = op) (h1 : u.gpr .x1 = sp) (h2 : u.gpr .x2 = scr)
    (hos : Region.Disjoint ⟨op, 57⟩ ⟨scr, 8192⟩) (hss : Region.Disjoint ⟨sp, 57⟩ ⟨scr, 8192⟩)
    (hn : scr.toNat + 8192 ≤ 2 ^ 64) (hr : Readable V ⟨sp, 57⟩)
    (hwo : Writable V ⟨op, 57⟩) (hws : Writable V ⟨scr, 8192⟩) :
    WP isa (.call "vg_ed448_scalar_base" Impl.Ed448.AArch64.scalarBase) u fun w =>
      WCtx V g vec m₀ w ∧ Frame ([⟨op, 57⟩, ⟨scr, 8192⟩] ++ [CK V.E]) u.mem w.mem ∧
      Spec.Ed448.bytesAt w.mem op 57 = Spec.Ed448.scalarBase (Spec.Ed448.bytesAt u.mem sp 57) := by
  have hw : ∀ r ∈ [(⟨op, 57⟩ : Region), ⟨scr, 8192⟩], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [hwo, hws]
  refine wcall hV hu hb.ok (noFrames_depth base_noFrames)
    (base_pre h0 h1 h2 hos hss hn) (covers_rw (by simpa using hr) hw) hw fun w hw' hf hp => ⟨hw', hf, ?_⟩
  change Spec.Ed448.bytesAt w.mem (u.callEntry.gpr .x0) 57 =
    Spec.Ed448.scalarBase (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x1) 57) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), h0, h1] at hp
  exact hp

/-! ## `vg_ed448_scalar_mul_add(out, r, k, s, scratch)` -/

theorem mulAdd_pre {op rp kp sp scr : Addr} (h0 : u.gpr .x0 = op) (h1 : u.gpr .x1 = rp)
    (h2 : u.gpr .x2 = kp) (h3 : u.gpr .x3 = sp) (h4 : u.gpr .x4 = scr)
    (hr : Region.Disjoint ⟨rp, 57⟩ ⟨scr, 8192⟩) (hk : Region.Disjoint ⟨kp, 57⟩ ⟨scr, 8192⟩)
    (hs : Region.Disjoint ⟨sp, 57⟩ ⟨scr, 8192⟩) :
    Proof.Ed448.AArch64.scalarMulAddLocal.pre
      (u.callEntry.withRegions [⟨rp, 57⟩, ⟨kp, 57⟩, ⟨sp, 57⟩] [⟨op, 57⟩, ⟨scr, 8192⟩]) := by
  simp only [Proof.Ed448.AArch64.scalarMulAddLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), h0, h1, h2, h3, h4]
  exact ⟨trivial, trivial, hr, hk, hs⟩

theorem mulAdd_call (hV : V.Ok) (hu : WCtx V g vec m₀ u) {op rp kp sp scr : Addr}
    (h0 : u.gpr .x0 = op) (h1 : u.gpr .x1 = rp) (h2 : u.gpr .x2 = kp) (h3 : u.gpr .x3 = sp)
    (h4 : u.gpr .x4 = scr)
    (hdr : Region.Disjoint ⟨rp, 57⟩ ⟨scr, 8192⟩) (hdk : Region.Disjoint ⟨kp, 57⟩ ⟨scr, 8192⟩)
    (hds : Region.Disjoint ⟨sp, 57⟩ ⟨scr, 8192⟩)
    (hrr : Readable V ⟨rp, 57⟩) (hrk : Readable V ⟨kp, 57⟩) (hrs : Readable V ⟨sp, 57⟩)
    (hwo : Writable V ⟨op, 57⟩) (hws : Writable V ⟨scr, 8192⟩) :
    WP isa (.call "vg_ed448_scalar_mul_add" Impl.Ed448.AArch64.scalarMulAdd) u fun w =>
      WCtx V g vec m₀ w ∧ Frame ([⟨op, 57⟩, ⟨scr, 8192⟩] ++ [CK V.E]) u.mem w.mem ∧
      Spec.Ed448.bytesAt w.mem op 57 = Spec.Ed448.scalarMulAdd (Spec.Ed448.bytesAt u.mem rp 57)
        (Spec.Ed448.bytesAt u.mem kp 57) (Spec.Ed448.bytesAt u.mem sp 57) := by
  have hw : ∀ r ∈ [(⟨op, 57⟩ : Region), ⟨scr, 8192⟩], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [hwo, hws]
  have hrd : ∀ r ∈ [(⟨rp, 57⟩ : Region), ⟨kp, 57⟩, ⟨sp, 57⟩], Readable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [hrr, hrk, hrs]
  refine wcall hV hu Proof.Ed448.AArch64.scalarMulAdd_ok (noFrames_depth mulAdd_noFrames)
    (mulAdd_pre h0 h1 h2 h3 h4 hdr hdk hds) (covers_rw hrd hw) hw fun w hw' hf hp => ⟨hw', hf, ?_⟩
  change Spec.Ed448.bytesAt w.mem (u.callEntry.gpr .x0) 57 =
    Spec.Ed448.scalarMulAdd (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x1) 57)
      (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x2) 57) (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x3) 57) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), h0, h1, h2, h3] at hp
  exact hp

/-! ## `vg_ed448_verify_equation(pk, signature, challenge, scratch)` -/

theorem equation_pre {pk sig ch scr : Addr} (h0 : u.gpr .x0 = pk) (h1 : u.gpr .x1 = sig)
    (h2 : u.gpr .x2 = ch) (h3 : u.gpr .x3 = scr)
    (hp : Region.Disjoint ⟨pk, 57⟩ ⟨scr, 8192⟩) (hs : Region.Disjoint ⟨sig, 114⟩ ⟨scr, 8192⟩)
    (hc : Region.Disjoint ⟨ch, 57⟩ ⟨scr, 8192⟩) (hn : scr.toNat + 8192 ≤ 2 ^ 64) :
    Proof.Ed448.AArch64.verifyEquationLocal.pre
      (u.callEntry.withRegions [⟨pk, 57⟩, ⟨sig, 114⟩, ⟨ch, 57⟩] [⟨scr, 8192⟩]) := by
  simp only [Proof.Ed448.AArch64.verifyEquationLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), h0, h1, h2, h3]
  exact ⟨trivial, trivial, hp, hs, hc, hn⟩

theorem equation_call (hQ : Proof.Ed448.AArch64.EqOk) (hV : V.Ok)
    (hu : WCtx V g vec m₀ u) {pk sig ch scr : Addr}
    (h0 : u.gpr .x0 = pk) (h1 : u.gpr .x1 = sig) (h2 : u.gpr .x2 = ch) (h3 : u.gpr .x3 = scr)
    (hdp : Region.Disjoint ⟨pk, 57⟩ ⟨scr, 8192⟩) (hds : Region.Disjoint ⟨sig, 114⟩ ⟨scr, 8192⟩)
    (hdc : Region.Disjoint ⟨ch, 57⟩ ⟨scr, 8192⟩) (hn : scr.toNat + 8192 ≤ 2 ^ 64)
    (hrp : Readable V ⟨pk, 57⟩) (hrs : Readable V ⟨sig, 114⟩) (hrc : Readable V ⟨ch, 57⟩)
    (hws : Writable V ⟨scr, 8192⟩) :
    WP isa (.call "vg_ed448_verify_equation" Impl.Ed448.AArch64.verifyEquation) u fun w =>
      WCtx V g vec m₀ w ∧ Frame ([⟨scr, 8192⟩] ++ [CK V.E]) u.mem w.mem ∧
      w.gpr .x0 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt u.mem pk 57)
        (Spec.Ed448.bytesAt u.mem sig 114) (Spec.Ed448.bytesAt u.mem ch 57) then 1 else 0 := by
  have hw : ∀ r ∈ [(⟨scr, 8192⟩ : Region)], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl; exact hws
  have hrd : ∀ r ∈ [(⟨pk, 57⟩ : Region), ⟨sig, 114⟩, ⟨ch, 57⟩], Readable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [hrp, hrs, hrc]
  refine wcall hV hu (hQ.ok) (noFrames_depth equation_noFrames)
    (equation_pre h0 h1 h2 h3 hdp hds hdc hn) (covers_rw hrd hw) hw fun w hw' hf hp => ⟨hw', hf, ?_⟩
  change w.gpr .x0 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x0) 57)
    (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x1) 114)
    (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x2) 57) then 1 else 0 at hp
  rw [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h0, h1, h2] at hp
  exact hp

end VG.Proof.Ed448.AArch64.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.Whole.CT`. -/
section

/-!
# Ed448's complete operations on AArch64: constant time in the frame's body

Two runs whose public data agree have the same `Env`, so in the frame's body
they are related by `Two`: both satisfy `WCtx` with it (and a predicate `P`
of what the next piece needs), whatever their secrets. The facts about one
run (`M`: what the saved arguments are, from the run's initial memory) hold
in both. A block addresses only the stack (`block_ct`); a call's arguments
(`setupS_ct`) have the same values `val` in both runs, which `callS_ct`
passes to constant-time code whose public data they are (`Whole.callEx`).
-/

namespace VG.Proof.Ed448.AArch64.Whole

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Whole
open VG.Proof.Ed25519.AArch64.Whole (Within FR CK)

/-- Two runs, each in the frame's body with `V`, and `P`. -/
abbrev Two (V : VG.Proof.Ed448.AArch64.Whole.Env) (g₁ g₂ : Reg → Addr) (v₁ v₂ : VReg → BitVec 128) (m₁ m₂ : Mem)
    (P : State → Prop) (a b : State) : Prop :=
  (VG.Proof.Ed448.AArch64.Whole.WCtx V g₁ v₁ m₁ a ∧ P a) ∧ (VG.Proof.Ed448.AArch64.Whole.WCtx V g₂ v₂ m₂ b ∧ P b)

/-- The argument registers hold `val`. -/
abbrev Regs (args : List (Reg × Src)) (val : Reg → Addr) (t : State) : Prop :=
  ∀ p ∈ args, t.gpr p.1 = val p.1

variable {V : VG.Proof.Ed448.AArch64.Whole.Env} {g₁ g₂ : Reg → Addr} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem two_sp {P : State → Prop} {a b : State} (h : VG.Proof.Ed448.AArch64.Whole.Two V g₁ g₂ v₁ v₂ m₁ m₂ P a b) : a.sp = b.sp :=
  h.1.1.1.sp.trans h.2.1.1.sp.symm

/-- A block addressed through the stack pointer, with its effect in each run. -/
theorem block_ct {M : Mem → Prop} (h₁ : M m₁) (h₂ : M m₂) {P Q : State → Prop} {is : List Instr}
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block is) hint).isSome = true)
    (hok : ∀ {g vec m₀ t}, M m₀ → VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ t → P t →
      WP isa (.block is) t fun u => VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ u ∧ Q u) :
    RelCT isa (VG.Proof.Ed448.AArch64.Whole.Two V g₁ g₂ v₁ v₂ m₁ m₂ P) (.block is) (VG.Proof.Ed448.AArch64.Whole.Two V g₁ g₂ v₁ v₂ m₁ m₂ Q) :=
  VG.Proof.Ed25519.AArch64.Whole.rel_wp
    (VG.Proof.Ed25519.AArch64.Whole.block_rel (fun _ _ h => VG.Proof.Ed448.AArch64.Whole.two_sp h) ht)
    (fun _ h => hok h₁ h.1 h.2) (fun _ h => hok h₂ h.1 h.2)

/-- A call's arguments, the same values `val` in both runs. -/
theorem setupS_ct (hV : V.Ok) {M : Mem → Prop} (h₁ : M m₁) (h₂ : M m₂) {args : List (Reg × Src)}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, VG.Proof.Ed448.AArch64.Whole.srcValid p.2) (hret : VG.Proof.Ed448.AArch64.Whole.retOk args = true)
    (hr : ∀ p ∈ args, p.1 ∉ preserved)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS args)) hint).isSome = true)
    {P : State → Prop} (val : Reg → Addr)
    (hval : ∀ {g vec m₀ t}, M m₀ → VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ t → P t →
      ∀ p ∈ args, VG.Proof.Ed448.AArch64.Whole.srcValue V.E t.mem (t.gpr .x0) p.2 = val p.1) :
    RelCT isa (VG.Proof.Ed448.AArch64.Whole.Two V g₁ g₂ v₁ v₂ m₁ m₂ P) (.block (setupS args))
      (VG.Proof.Ed448.AArch64.Whole.Two V g₁ g₂ v₁ v₂ m₁ m₂ (VG.Proof.Ed448.AArch64.Whole.Regs args val)) :=
  VG.Proof.Ed448.AArch64.Whole.block_ct h₁ h₂ ht fun hm hc hp => WP.mono (VG.Proof.Ed448.AArch64.Whole.wsetup_ok hV hc hn hv hret hr) fun _ ⟨hu, _, hs⟩ =>
    ⟨hu, fun p hq => (hs p hq).trans (hval hm hc hp p hq)⟩

/-- A call, its arguments the same values in both runs, and its effect in each run. -/
theorem callS_ct (hV : V.Ok) {M : Mem → Prop} (h₁ : M m₁) (h₂ : M m₂) {args : List (Reg × Src)}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, VG.Proof.Ed448.AArch64.Whole.srcValid p.2) (hret : VG.Proof.Ed448.AArch64.Whole.retOk args = true)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) (hl : ∀ p ∈ args, p.1 ∉ linkRegs)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS args)) hint).isSome = true)
    {P : State → Prop} (val : Reg → Addr)
    (hval : ∀ {g vec m₀ t}, M m₀ → VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ t → P t →
      ∀ p ∈ args, VG.Proof.Ed448.AArch64.Whole.srcValue V.E t.mem (t.gpr .x0) p.2 = val p.1)
    {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) {rd wr : List Region}
    (pre : ∀ {g vec m₀ t}, VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ t → VG.Proof.Ed448.AArch64.Whole.Regs args val t →
      k.pre (t.callEntry.withRegions rd wr))
    (hcov : Covers (rd ++ wr) (V.ins ++ FR V.E :: V.outs)) (hw : ∀ r ∈ wr, VG.Proof.Ed448.AArch64.Whole.Writable V r)
    (kp : ∀ a b : State, a.sp = b.sp → (∀ p ∈ args, a.callEntry.gpr p.1 = b.callEntry.gpr p.1) →
      k.pub (a.callEntry.withRegions rd wr) (b.callEntry.withRegions rd wr))
    {Q : State → Prop}
    (hok : ∀ {g vec m₀ t}, M m₀ → VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ t → P t →
      WP isa (callS args name c) t fun u => VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ u ∧ Q u) :
    RelCT isa (VG.Proof.Ed448.AArch64.Whole.Two V g₁ g₂ v₁ v₂ m₁ m₂ P) (callS args name c) (VG.Proof.Ed448.AArch64.Whole.Two V g₁ g₂ v₁ v₂ m₁ m₂ Q) := by
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp ?_ (fun _ h => hok h₁ h.1 h.2) (fun _ h => hok h₂ h.1 h.2)
  refine (VG.Proof.Ed448.AArch64.Whole.setupS_ct hV h₁ h₂ hn hv hret hr ht val hval).seq
    (VG.Proof.Ed25519.AArch64.Whole.callEx correct ct fun a b h => ?_)
  let ready : ∀ {g vec m₀ t}, VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ t → VG.Proof.Ed448.AArch64.Whole.Regs args val t →
      VG.Proof.Ed25519.AArch64.Whole.CallReady k V.E V.ins V.outs t := fun hc hs =>
    ⟨rd, wr, pre hc hs, hcov, fun r hr => (hw r hr).imp And.left id⟩
  obtain ⟨ca, wa⟩ := (ready h.1.1 h.1.2).covers_state h.1.1.1
  obtain ⟨cb, wb⟩ := (ready h.2.1 h.2.2).covers_state h.2.1.1
  refine ⟨rd, wr, rd, wr, pre h.1.1 h.1.2, pre h.2.1 h.2.2, kp a b (VG.Proof.Ed448.AArch64.Whole.two_sp h) fun p hp => ?_, ca, wa, cb, wb⟩
  rw [State.callEntry_gpr _ (hl p hp), State.callEntry_gpr _ (hl p hp), h.1.2 p hp, h.2.2 p hp]

end VG.Proof.Ed448.AArch64.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.Whole.Zero`. -/
section

/-!
# Ed448's complete operations on AArch64: the Keccak state zeroed

`zeroStores`, with `x15` the state's address: the 25 words zeroed
(`zstores_ok`), so the state is `Spec.Sha3.zero` (`zero_state`).
-/

namespace VG.Proof.Ed448.AArch64.Whole

open VG VG.AArch64
open VG.Spec.Sha3 (stateAt)

theorem movz14_ok (s : State) :
    WP isa (.block [.movz .x .x14 0 0]) s fun t => t.gpr .x14 = 0 ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v ∧ ∀ r, r ≠ .x14 → t.gpr r = s.gpr r := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩

/-- After the first `n` stores of zero. -/
structure ZInv (scr : Addr) (s : State) (n : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  v : t.v = s.v
  gpr : t.gpr = s.gpr
  frame : VG.Frame [⟨scr, 200⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (scr + BitVec.ofNat 64 (8 * j)) 64 = 0

theorem zstores_ok {s : State} {scr : Addr} (h15 : s.gpr .x15 = scr) (h14 : s.gpr .x14 = 0)
    (hw : (⟨scr, 8192⟩ : Region) ∈ s.wr) :
    ∀ n ≤ 25, WP isa (.block ((List.range n).map fun k => Instr.str .x .x14 .x15 (8 * k))) s (VG.Proof.Ed448.AArch64.Whole.ZInv scr s n)
  | 0, _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => by omega⟩
  | n + 1, hn => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed448.AArch64.Whole.zstores_ok h15 h14 hw n (by omega)) fun u hu => ?_
    have dest : InRegions u.wr (u.gpr .x15 + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [hu.gpr, hu.wr, h15]
      exact ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩
    apply WP.of_runBlock
    have e15 : u.gpr .x15 = scr := by rw [hu.gpr, h15]
    have e14 : u.gpr .x14 = 0 := by rw [hu.gpr, h14]
    simp only [runBlock_cons]
    rw [exec_str_x ⟨by omega, by omega⟩ dest]
    simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
    rw [e15, e14]
    refine ⟨hu.rd, hu.wr, hu.sp, hu.v, hu.gpr, ?_, fun j hj => ?_⟩
    · exact hu.frame.writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by omega) (by omega))
    · show (u.mem.writeW (scr + BitVec.ofNat 64 (8 * n)) (0 : BitVec 64)).readW
        (scr + BitVec.ofNat 64 (8 * j)) 64 = 0
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        exact hu.words j (by omega)

theorem zero_state {m : Mem} {p : Addr} (h : ∀ j < 25, m.readW (p + BitVec.ofNat 64 (8 * j)) 64 = 0) :
    VG.Spec.Sha3.stateAt m p = Spec.Sha3.zero := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Sha3.stateAt, Spec.Sha3.zero, Vector.getElem_ofFn, Vector.getElem_replicate]
  exact h i hi

end VG.Proof.Ed448.AArch64.Whole

namespace VG.Proof.Ed448.AArch64.Whole

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Whole
open VG.Spec.Sha3 (stateAt)

/-- `zeroStores`, with `x15` the state's address. -/
theorem zeroStores_run {s : State} {scr : Addr} (h15 : s.gpr .x15 = scr)
    (hw : (⟨scr, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block zeroStores) s fun t => t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v ∧
      (∀ r, r ≠ .x14 → t.gpr r = s.gpr r) ∧ VG.Frame [⟨scr, 200⟩] s.mem t.mem ∧
      VG.Spec.Sha3.stateAt t.mem scr = Spec.Sha3.zero := by
  rw [zeroStores, show ∀ (i : Instr) is, i :: is = [i] ++ is from fun _ _ => rfl, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.Whole.movz14_ok s) fun w ⟨w14, wm, wrd, wwr, wsp, wv, wg⟩ => ?_
  refine WP.mono (VG.Proof.Ed448.AArch64.Whole.zstores_ok ((wg _ (by decide)).trans h15) w14 (by rw [wwr]; exact hw) 25 (by omega))
    fun x hx => ⟨hx.rd.trans wrd, hx.wr.trans wwr, hx.sp.trans wsp, hx.v.trans wv,
      fun r hr => by rw [hx.gpr]; exact wg r hr, by rw [← wm]; exact hx.frame, VG.Proof.Ed448.AArch64.Whole.zero_state hx.words⟩

end VG.Proof.Ed448.AArch64.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.Whole.Sponge`. -/
section

/-!
# Ed448's complete operations on AArch64: the sponge's calls

With `scratch` kept in the locals at `d` (`ScrOk`), and any implementation
`v` of the Keccak permutation: the state zeroed (`zeroSt_ok`), a buffer
absorbed (`kabs_ok`: its bytes appended to the represented message, and the
new position in `x0`), the padding absorbed (`kpad_ok`) and 114 bytes
squeezed (`ksqz_ok`).
-/

namespace VG.Proof.Ed448.AArch64.Whole

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Whole
open VG.Proof.Ed25519.AArch64.Whole (Within FR CK)
open VG.Spec.Sha3 (stateAt)

/-- `scratch` is kept in the locals at `d`, and written. -/
structure ScrOk (V : VG.Proof.Ed448.AArch64.Whole.Env) (d : Nat) (scr : Addr) : Prop where
  kept : (d, scr) ∈ V.ls
  out : (⟨scr, 8192⟩ : Region) ∈ V.outs
  nc : scr.toNat + 8192 ≤ 2 ^ 64

abbrev ST (scr : Addr) : Region := ⟨scr, 200⟩
abbrev KS (scr : Addr) : Region := ⟨scr + BitVec.ofNat 64 256, 640⟩

theorem st_ks (scr : Addr) : (VG.Proof.Ed448.AArch64.Whole.ST scr).Disjoint (VG.Proof.Ed448.AArch64.Whole.KS scr) := Offset.base_disjoint _ (by decide) (by decide)

variable {V : VG.Proof.Ed448.AArch64.Whole.Env} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State} {d : Nat} {scr : Addr}

theorem st_within (scr : Addr) : VG.Proof.Ed25519.AArch64.Whole.Within (VG.Proof.Ed448.AArch64.Whole.ST scr) ⟨scr, 8192⟩ :=
  ⟨0, (BitVec.add_zero _).symm, by show 0 + 200 ≤ 8192; decide⟩
theorem ks_within (scr : Addr) : VG.Proof.Ed25519.AArch64.Whole.Within (VG.Proof.Ed448.AArch64.Whole.KS scr) ⟨scr, 8192⟩ := ⟨256, rfl, by show 256 + 640 ≤ 8192; decide⟩

theorem ScrOk.ck_st (hV : V.Ok) (h : VG.Proof.Ed448.AArch64.Whole.ScrOk V d scr) : (CK V.E).Disjoint (VG.Proof.Ed448.AArch64.Whole.ST scr) :=
  (hV.co _ h.out).sub_right (VG.Proof.Ed448.AArch64.Whole.st_within scr).sub
theorem ScrOk.ck_ks (hV : V.Ok) (h : VG.Proof.Ed448.AArch64.Whole.ScrOk V d scr) : (CK V.E).Disjoint (VG.Proof.Ed448.AArch64.Whole.KS scr) :=
  (hV.co _ h.out).sub_right (VG.Proof.Ed448.AArch64.Whole.ks_within scr).sub

theorem ScrOk.sponge_writes (h : VG.Proof.Ed448.AArch64.Whole.ScrOk V d scr) :
    ∀ r ∈ [VG.Proof.Ed448.AArch64.Whole.ST scr, VG.Proof.Ed448.AArch64.Whole.KS scr], VG.Proof.Ed448.AArch64.Whole.Apart V r ∨ ∃ R ∈ V.outs, VG.Proof.Ed25519.AArch64.Whole.Within r R := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inr ⟨_, h.out, VG.Proof.Ed448.AArch64.Whole.st_within scr⟩
  · exact .inr ⟨_, h.out, VG.Proof.Ed448.AArch64.Whole.ks_within scr⟩

theorem ScrOk.loc (hc : VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ t) (h : VG.Proof.Ed448.AArch64.Whole.ScrOk V d scr) (x0 : BitVec 64) (o : Nat) :
    VG.Proof.Ed448.AArch64.Whole.srcValue V.E t.mem x0 (.loc d o) = scr + BitVec.ofNat 64 o :=
  VG.Proof.Ed448.AArch64.Whole.srcValue_loc hc.2 h.kept o

theorem toNat_ofNat64 {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-! ## The state zeroed -/

theorem zeroSt_ok (hV : V.Ok) (hs : VG.Proof.Ed448.AArch64.Whole.ScrOk V d scr) (hc : VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ t) :
    WP isa (zeroSt d) t fun u => VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ u ∧ Frame [VG.Proof.Ed448.AArch64.Whole.ST scr] t.mem u.mem ∧
      VG.Spec.Sha3.stateAt u.mem scr = Spec.Sha3.zero := by
  have hd := hV.ls _ hs.kept
  simp only at hd
  rw [zeroSt, WP.seq_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.Whole.wsetup_ok hV hc (args := [(.x15, .loc d 0)]) (by simp)
    (by simp [VG.Proof.Ed448.AArch64.Whole.srcValid, hd.1]; omega) rfl (by simp [preserved])) fun u ⟨hu, hm, hvs⟩ => ?_
  have h15 : u.gpr .x15 = scr := by
    rw [hvs _ List.mem_cons_self, hs.loc hc, BitVec.add_zero]
  have hw : (⟨scr, 8192⟩ : Region) ∈ u.wr := by
    rw [hu.1.wr]; exact List.mem_cons_of_mem _ hs.out
  refine WP.mono (VG.Proof.Ed448.AArch64.Whole.zeroStores_run h15 hw) fun x ⟨xrd, xwr, xsp, xv, xg, xf, xz⟩ => ⟨?_, ?_, xz⟩
  · refine hu.of_frame hV xrd xwr xsp (fun r hr _ => xg r (by rintro rfl; simp [preserved] at hr))
      (fun r _ => by rw [xv]) xf ?_
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact .inr ⟨_, hs.out, VG.Proof.Ed448.AArch64.Whole.st_within scr⟩
  · rw [← hm]; exact xf

/-! ## Absorbing -/

/-- The arguments of `vg_keccak_absorb_scratch`. -/
abbrev absArgs (d : Nat) (src len pos : VG.Impl.Ed448.AArch64.Whole.Src) : List (Reg × VG.Impl.Ed448.AArch64.Whole.Src) :=
  [(.x2, pos), (.x0, .loc d 0), (.x1, .val (.const 136)), (.x3, src), (.x4, len), (.x5, .loc d 256)]

theorem absorb_pre (hV : V.Ok) (hs : VG.Proof.Ed448.AArch64.Whole.ScrOk V d scr) {u : State} (hsp : u.sp = V.E) {dp : Addr} {n q : Nat}
    (h0 : u.gpr .x0 = scr) (h1 : u.gpr .x1 = BitVec.ofNat 64 136) (h2 : u.gpr .x2 = BitVec.ofNat 64 q)
    (h3 : u.gpr .x3 = dp) (h4 : u.gpr .x4 = BitVec.ofNat 64 n) (h5 : u.gpr .x5 = scr + BitVec.ofNat 64 256)
    (hql : q < 136) (hnl : n < 2 ^ 64)
    (dS : Region.Disjoint ⟨dp, n⟩ (VG.Proof.Ed448.AArch64.Whole.ST scr)) (dK : Region.Disjoint ⟨dp, n⟩ (VG.Proof.Ed448.AArch64.Whole.KS scr))
    (kD : (CK V.E).Disjoint ⟨dp, n⟩) :
    Proof.Sha3.absorbAArch64.pre (u.callEntry.withRegions [⟨dp, n⟩] [VG.Proof.Ed448.AArch64.Whole.ST scr, VG.Proof.Ed448.AArch64.Whole.KS scr]) := by
  have hn' := VG.Proof.Ed448.AArch64.Whole.toNat_ofNat64 hnl
  have hq' := VG.Proof.Ed448.AArch64.Whole.toNat_ofNat64 (show q < 2 ^ 64 by omega)
  simp only [Proof.Sha3.absorbAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x5 ∉ linkRegs), h0, h1, h2, h3, h4, h5, hsp, hn', hq']
  exact ⟨trivial, trivial, VG.Proof.Ed448.AArch64.Whole.st_ks scr, dS, dK, hV.e16, hs.ck_st hV, kD, hs.ck_ks hV, by decide, hql⟩

theorem kabs_ok (v : Proof.Sha3.AArch64.Permutation) (hV : V.Ok) (hs : VG.Proof.Ed448.AArch64.Whole.ScrOk V d scr)
    (hc : VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ t) {src len pos : VG.Impl.Ed448.AArch64.Whole.Src} (hvs : VG.Proof.Ed448.AArch64.Whole.srcValid src) (hvl : VG.Proof.Ed448.AArch64.Whole.srcValid len)
    (hvp : VG.Proof.Ed448.AArch64.Whole.srcValid pos) (hrs : VG.Proof.Ed448.AArch64.Whole.noRet src = true) (hrl : VG.Proof.Ed448.AArch64.Whole.noRet len = true)
    {dp : Addr} {n q : Nat} (hdp : VG.Proof.Ed448.AArch64.Whole.srcValue V.E t.mem (t.gpr .x0) src = dp)
    (hn : VG.Proof.Ed448.AArch64.Whole.srcValue V.E t.mem (t.gpr .x0) len = BitVec.ofNat 64 n)
    (hq : VG.Proof.Ed448.AArch64.Whole.srcValue V.E t.mem (t.gpr .x0) pos = BitVec.ofNat 64 q) (hql : q < 136) (hnl : n < 2 ^ 64)
    (hin : VG.Proof.Ed25519.AArch64.Whole.Within ⟨dp, n⟩ (FR V.E) ∨ ∃ R ∈ V.ins ++ V.outs, VG.Proof.Ed25519.AArch64.Whole.Within ⟨dp, n⟩ R)
    (dS : Region.Disjoint ⟨dp, n⟩ (VG.Proof.Ed448.AArch64.Whole.ST scr)) (dK : Region.Disjoint ⟨dp, n⟩ (VG.Proof.Ed448.AArch64.Whole.KS scr))
    (kD : (CK V.E).Disjoint ⟨dp, n⟩) :
    WP isa (kabs v.callee d src len pos) t fun u => VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ u ∧
      Frame [VG.Proof.Ed448.AArch64.Whole.ST scr, VG.Proof.Ed448.AArch64.Whole.KS scr, CK V.E] t.mem u.mem ∧
      (∀ msg, Spec.Sha3.Repr t.mem scr 136 msg → q = msg.length % 136 →
        Spec.Sha3.Repr u.mem scr 136 (msg ++ Spec.Sha3.bytesAt t.mem dp n)) ∧
      (u.gpr .x0).toNat = (q + n) % 136 := by
  have hd := hV.ls _ hs.kept
  simp only at hd
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.Whole.wsetup_ok hV hc (args := VG.Proof.Ed448.AArch64.Whole.absArgs d src len pos)
    (by simp) (fun p hp => by
      simp only [VG.Proof.Ed448.AArch64.Whole.absArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hvp
      · exact ⟨hd.1, hd.2, by decide⟩
      · show (136 : Nat) < 65536; decide
      · exact hvs
      · exact hvl
      · exact ⟨hd.1, hd.2, by decide⟩)
    (by simp only [VG.Proof.Ed448.AArch64.Whole.retOk, List.all_cons, List.all_nil, hrs, hrl]; rfl) (by simp [preserved]))
    fun u ⟨hu, hm, hv⟩ => ?_)
  have h0 := hv (.x0, .loc d 0) (by simp)
  have h1 := hv (.x1, .val (.const 136)) (by simp)
  have h2 := hv (.x2, pos) (by simp)
  have h3 := hv (.x3, src) (by simp)
  have h4 := hv (.x4, len) (by simp)
  have h5 := hv (.x5, .loc d 256) (by simp)
  rw [hs.loc hc, BitVec.add_zero] at h0
  rw [hs.loc hc] at h5
  rw [hq] at h2
  rw [hdp] at h3
  rw [hn] at h4
  simp only [VG.Proof.Ed448.AArch64.Whole.srcValue, VG.Proof.Ed25519.AArch64.Whole.value] at h1
  have hn' := VG.Proof.Ed448.AArch64.Whole.toNat_ofNat64 hnl
  have hq' := VG.Proof.Ed448.AArch64.Whole.toNat_ofNat64 (show q < 2 ^ 64 by omega)
  have hpre := VG.Proof.Ed448.AArch64.Whole.absorb_pre hV hs hu.1.sp h0 h1 h2 h3 h4 h5 hql hnl dS dK kD
  refine VG.Proof.Ed448.AArch64.Whole.wcall hV hu (Proof.Sha3.AArch64.Stream.Absorb.absorb_correct v) (Nat.le_of_eq v.absorb_depth)
    hpre (VG.Proof.Ed448.AArch64.Whole.covers_of fun r hr => ?_) hs.sponge_writes fun w hw hf hp => ⟨hw, ?_, fun msg hr hpos => ?_, ?_⟩
  · rcases List.mem_append.mp hr with hr | hr
    · rw [List.mem_singleton.mp hr]
      rcases hin with h | ⟨R, hR, hs⟩
      · exact .inl h
      · exact .inr ⟨R, hR, hs⟩
    · rcases hs.sponge_writes r hr with ⟨h, _⟩ | ⟨R, hR, hs⟩
      · exact .inl h
      · exact .inr ⟨R, List.mem_append_right _ hR, hs⟩
  · rw [← hm]
    exact hf.mono fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact hr
  · have hh := hp.1 msg (by
      simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
        State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), h0, h1, hm, VG.Proof.Ed448.AArch64.Whole.toNat_ofNat64 (show 136 < 2 ^ 64 by decide)]
      exact hr) (by
      simp only [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h1, h2, hq',
        VG.Proof.Ed448.AArch64.Whole.toNat_ofNat64 (show 136 < 2 ^ 64 by decide)]
      exact hpos)
    simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), h0, h1, h3, h4, hn', hm,
      VG.Proof.Ed448.AArch64.Whole.toNat_ofNat64 (show 136 < 2 ^ 64 by decide)] at hh
    exact hh
  · have hh := hp.2
    simp only [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), h1, h2, h4, hn', hq',
      VG.Proof.Ed448.AArch64.Whole.toNat_ofNat64 (show 136 < 2 ^ 64 by decide)] at hh
    exact hh

/-! ## Padding -/

abbrev padArgs (d : Nat) (pos : VG.Impl.Ed448.AArch64.Whole.Src) : List (Reg × VG.Impl.Ed448.AArch64.Whole.Src) :=
  [(.x2, pos), (.x0, .loc d 0), (.x1, .val (.const 136)), (.x3, .val (.const 0x1f)), (.x4, .loc d 256)]

theorem pad_pre (hV : V.Ok) (hs : VG.Proof.Ed448.AArch64.Whole.ScrOk V d scr) {u : State} (hsp : u.sp = V.E) {q : Nat}
    (h0 : u.gpr .x0 = scr) (h1 : u.gpr .x1 = BitVec.ofNat 64 136) (h2 : u.gpr .x2 = BitVec.ofNat 64 q)
    (h4 : u.gpr .x4 = scr + BitVec.ofNat 64 256) (hql : q < 136) :
    Proof.Sha3.padAArch64.pre (u.callEntry.withRegions [] [VG.Proof.Ed448.AArch64.Whole.ST scr, VG.Proof.Ed448.AArch64.Whole.KS scr]) := by
  have hq' := VG.Proof.Ed448.AArch64.Whole.toNat_ofNat64 (show q < 2 ^ 64 by omega)
  simp only [Proof.Sha3.padAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), h0, h1, h2, h4, hsp, hq']
  exact ⟨trivial, trivial, VG.Proof.Ed448.AArch64.Whole.st_ks scr, hV.e16, hs.ck_st hV, hs.ck_ks hV, by decide, hql⟩

theorem kpad_ok (v : Proof.Sha3.AArch64.Permutation) (hV : V.Ok) (hs : VG.Proof.Ed448.AArch64.Whole.ScrOk V d scr)
    (hc : VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ t) {pos : VG.Impl.Ed448.AArch64.Whole.Src} (hvp : VG.Proof.Ed448.AArch64.Whole.srcValid pos) {q : Nat}
    (hq : VG.Proof.Ed448.AArch64.Whole.srcValue V.E t.mem (t.gpr .x0) pos = BitVec.ofNat 64 q) (hql : q < 136) :
    WP isa (kpad v.callee d pos) t fun u => VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ u ∧
      Frame [VG.Proof.Ed448.AArch64.Whole.ST scr, VG.Proof.Ed448.AArch64.Whole.KS scr, CK V.E] t.mem u.mem ∧
      (∀ msg, Spec.Sha3.Repr t.mem scr 136 msg → q = msg.length % 136 →
        VG.Spec.Sha3.stateAt u.mem scr = Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix msg)) := by
  have hd := hV.ls _ hs.kept
  simp only at hd
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.Whole.wsetup_ok hV hc (args := VG.Proof.Ed448.AArch64.Whole.padArgs d pos)
    (by simp) (fun p hp => by
      simp only [VG.Proof.Ed448.AArch64.Whole.padArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact hvp
      · exact ⟨hd.1, hd.2, by decide⟩
      · show (136 : Nat) < 65536; decide
      · show (0x1f : Nat) < 65536; decide
      · exact ⟨hd.1, hd.2, by decide⟩)
    (by simp only [VG.Proof.Ed448.AArch64.Whole.retOk, List.all_cons, List.all_nil]; rfl) (by simp [preserved]))
    fun u ⟨hu, hm, hv⟩ => ?_)
  have h0 := hv (.x0, .loc d 0) (by simp)
  have h1 := hv (.x1, .val (.const 136)) (by simp)
  have h2 := hv (.x2, pos) (by simp)
  have h3 := hv (.x3, .val (.const 0x1f)) (by simp)
  have h4 := hv (.x4, .loc d 256) (by simp)
  rw [hs.loc hc, BitVec.add_zero] at h0
  rw [hs.loc hc] at h4
  rw [hq] at h2
  simp only [VG.Proof.Ed448.AArch64.Whole.srcValue, VG.Proof.Ed25519.AArch64.Whole.value] at h1 h3
  have hq' := VG.Proof.Ed448.AArch64.Whole.toNat_ofNat64 (show q < 2 ^ 64 by omega)
  have hpre := VG.Proof.Ed448.AArch64.Whole.pad_pre hV hs hu.1.sp h0 h1 h2 h4 hql
  refine VG.Proof.Ed448.AArch64.Whole.wcall hV hu (Proof.Sha3.AArch64.Stream.Pad.pad_correct v) (Nat.le_of_eq v.pad_depth)
    hpre (VG.Proof.Ed448.AArch64.Whole.covers_of fun r hr => ?_) hs.sponge_writes fun w hw hf hp => ⟨hw, ?_, fun msg hr hpos => ?_⟩
  · rcases hs.sponge_writes r (by simpa using hr) with ⟨h, _⟩ | ⟨R, hR, hs⟩
    · exact .inl h
    · exact .inr ⟨R, List.mem_append_right _ hR, hs⟩
  · rw [← hm]
    exact hf.mono fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact hr
  · have hh := hp msg (by
      simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
        State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), h0, h1, hm,
        VG.Proof.Ed448.AArch64.Whole.toNat_ofNat64 (show 136 < 2 ^ 64 by decide)]
      exact hr) (by
      simp only [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h1, h2, hq',
        VG.Proof.Ed448.AArch64.Whole.toNat_ofNat64 (show 136 < 2 ^ 64 by decide)]
      exact hpos)
    simp only [State.withRegions_mem, State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), h0, h1, h3,
      VG.Proof.Ed448.AArch64.Whole.toNat_ofNat64 (show 136 < 2 ^ 64 by decide)] at hh
    exact hh

/-! ## Squeezing -/

abbrev sqzArgs (d : Nat) (out : VG.Impl.Ed448.AArch64.Whole.Src) : List (Reg × VG.Impl.Ed448.AArch64.Whole.Src) :=
  [(.x0, .loc d 0), (.x1, .val (.const 136)), (.x2, .val (.const 0)), (.x3, out), (.x4, .val (.const 114)),
    (.x5, .loc d 256)]

theorem squeeze_pre (hV : V.Ok) (hs : VG.Proof.Ed448.AArch64.Whole.ScrOk V d scr) {u : State} (hsp : u.sp = V.E) {op : Addr}
    (h0 : u.gpr .x0 = scr) (h1 : u.gpr .x1 = BitVec.ofNat 64 136) (h2 : u.gpr .x2 = BitVec.ofNat 64 0)
    (h3 : u.gpr .x3 = op) (h4 : u.gpr .x4 = BitVec.ofNat 64 114) (h5 : u.gpr .x5 = scr + BitVec.ofNat 64 256)
    (dS : Region.Disjoint ⟨op, 114⟩ (VG.Proof.Ed448.AArch64.Whole.ST scr)) (dK : Region.Disjoint ⟨op, 114⟩ (VG.Proof.Ed448.AArch64.Whole.KS scr))
    (kD : (CK V.E).Disjoint ⟨op, 114⟩) :
    Proof.Sha3.squeezeAArch64.pre (u.callEntry.withRegions [] [VG.Proof.Ed448.AArch64.Whole.ST scr, ⟨op, 114⟩, VG.Proof.Ed448.AArch64.Whole.KS scr]) := by
  simp only [Proof.Sha3.squeezeAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x5 ∉ linkRegs), h0, h1, h2, h3, h4, h5, hsp,
    VG.Proof.Ed448.AArch64.Whole.toNat_ofNat64 (show 114 < 2 ^ 64 by decide)]
  exact ⟨trivial, trivial, dS.symm, VG.Proof.Ed448.AArch64.Whole.st_ks scr, dK, hV.e16, hs.ck_st hV, kD, hs.ck_ks hV, by decide,
    by decide⟩

theorem ksqz_ok (v : Proof.Sha3.AArch64.Permutation) (hV : V.Ok) (hs : VG.Proof.Ed448.AArch64.Whole.ScrOk V d scr)
    (hc : VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ t) {out : VG.Impl.Ed448.AArch64.Whole.Src} (hvo : VG.Proof.Ed448.AArch64.Whole.srcValid out) (hro : VG.Proof.Ed448.AArch64.Whole.noRet out = true) {op : Addr}
    (hop : VG.Proof.Ed448.AArch64.Whole.srcValue V.E t.mem (t.gpr .x0) out = op)
    (hw : VG.Proof.Ed448.AArch64.Whole.Apart V ⟨op, 114⟩ ∨ ∃ R ∈ V.outs, VG.Proof.Ed25519.AArch64.Whole.Within ⟨op, 114⟩ R)
    (dS : Region.Disjoint ⟨op, 114⟩ (VG.Proof.Ed448.AArch64.Whole.ST scr)) (dK : Region.Disjoint ⟨op, 114⟩ (VG.Proof.Ed448.AArch64.Whole.KS scr))
    (kD : (CK V.E).Disjoint ⟨op, 114⟩) :
    WP isa (ksqz v.callee d out) t fun u => VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ u ∧
      Frame [VG.Proof.Ed448.AArch64.Whole.ST scr, ⟨op, 114⟩, VG.Proof.Ed448.AArch64.Whole.KS scr, CK V.E] t.mem u.mem ∧
      Spec.Sha3.bytesAt u.mem op 114 = Spec.Sha3.squeezeFrom 136 (VG.Spec.Sha3.stateAt t.mem scr) 0 114 := by
  have hd := hV.ls _ hs.kept
  simp only at hd
  refine WP.seq (WP.mono (VG.Proof.Ed448.AArch64.Whole.wsetup_ok hV hc (args := VG.Proof.Ed448.AArch64.Whole.sqzArgs d out)
    (by simp) (fun p hp => by
      simp only [VG.Proof.Ed448.AArch64.Whole.sqzArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨hd.1, hd.2, by decide⟩
      · show (136 : Nat) < 65536; decide
      · show (0 : Nat) < 65536; decide
      · exact hvo
      · show (114 : Nat) < 65536; decide
      · exact ⟨hd.1, hd.2, by decide⟩)
    (by simp only [VG.Proof.Ed448.AArch64.Whole.retOk, List.all_cons, List.all_nil, hro]; rfl) (by simp [preserved]))
    fun u ⟨hu, hm, hv⟩ => ?_)
  have h0 := hv (.x0, .loc d 0) (by simp)
  have h1 := hv (.x1, .val (.const 136)) (by simp)
  have h2 := hv (.x2, .val (.const 0)) (by simp)
  have h3 := hv (.x3, out) (by simp)
  have h4 := hv (.x4, .val (.const 114)) (by simp)
  have h5 := hv (.x5, .loc d 256) (by simp)
  rw [hs.loc hc, BitVec.add_zero] at h0
  rw [hs.loc hc] at h5
  rw [hop] at h3
  simp only [VG.Proof.Ed448.AArch64.Whole.srcValue, VG.Proof.Ed25519.AArch64.Whole.value] at h1 h2 h4
  have hws : ∀ r ∈ [VG.Proof.Ed448.AArch64.Whole.ST scr, ⟨op, 114⟩, VG.Proof.Ed448.AArch64.Whole.KS scr], VG.Proof.Ed448.AArch64.Whole.Apart V r ∨ ∃ R ∈ V.outs, VG.Proof.Ed25519.AArch64.Whole.Within r R := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inr ⟨_, hs.out, VG.Proof.Ed448.AArch64.Whole.st_within scr⟩
    · exact hw
    · exact .inr ⟨_, hs.out, VG.Proof.Ed448.AArch64.Whole.ks_within scr⟩
  have hpre := VG.Proof.Ed448.AArch64.Whole.squeeze_pre hV hs hu.1.sp h0 h1 h2 h3 h4 h5 dS dK kD
  refine VG.Proof.Ed448.AArch64.Whole.wcall hV hu (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_correct v) (Nat.le_of_eq v.squeeze_depth)
    hpre (VG.Proof.Ed448.AArch64.Whole.covers_of fun r hr => ?_) hws fun w hw' hf hp => ⟨hw', ?_, ?_⟩
  · rcases hws r (by simpa using hr) with ⟨h, _⟩ | ⟨R, hR, hs⟩
    · exact .inl h
    · exact .inr ⟨R, List.mem_append_right _ hR, hs⟩
  · rw [← hm]
    exact hf.mono fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact hr
  · have hh := hp.1
    simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), h0, h1, h2, h3, h4, hm,
      VG.Proof.Ed448.AArch64.Whole.toNat_ofNat64 (show 136 < 2 ^ 64 by decide), VG.Proof.Ed448.AArch64.Whole.toNat_ofNat64 (show 114 < 2 ^ 64 by decide),
      VG.Proof.Ed448.AArch64.Whole.toNat_ofNat64 (show 0 < 2 ^ 64 by decide)] at hh
    exact hh

/-! ## Chained absorptions -/

theorem repr_nil {mem : Mem} {p : Addr} {rate : Nat} (h : VG.Spec.Sha3.stateAt mem p = Spec.Sha3.zero) :
    Spec.Sha3.Repr mem p rate [] := by
  show VG.Spec.Sha3.stateAt mem p = Proof.Sha3.Rep rate []
  rw [Proof.Sha3.rep_nil, h]

theorem sha3_bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Sha3.bytesAt m p n).length = n := by
  simp [Spec.Sha3.bytesAt]

/-- `kabs_ok` after earlier absorptions of `msg`: the position in `x0` is that
of the message with the buffer appended. -/
theorem kabs_chain (v : Proof.Sha3.AArch64.Permutation) (hV : V.Ok) (hs : VG.Proof.Ed448.AArch64.Whole.ScrOk V d scr)
    (hc : VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ t) {src len pos : VG.Impl.Ed448.AArch64.Whole.Src} (hvs : VG.Proof.Ed448.AArch64.Whole.srcValid src) (hvl : VG.Proof.Ed448.AArch64.Whole.srcValid len)
    (hvp : VG.Proof.Ed448.AArch64.Whole.srcValid pos) (hrs : VG.Proof.Ed448.AArch64.Whole.noRet src = true) (hrl : VG.Proof.Ed448.AArch64.Whole.noRet len = true)
    {dp : Addr} {n : Nat} {msg : List Byte} (hdp : VG.Proof.Ed448.AArch64.Whole.srcValue V.E t.mem (t.gpr .x0) src = dp)
    (hn : VG.Proof.Ed448.AArch64.Whole.srcValue V.E t.mem (t.gpr .x0) len = BitVec.ofNat 64 n)
    (hq : VG.Proof.Ed448.AArch64.Whole.srcValue V.E t.mem (t.gpr .x0) pos = BitVec.ofNat 64 (msg.length % 136)) (hnl : n < 2 ^ 64)
    (hin : VG.Proof.Ed25519.AArch64.Whole.Within ⟨dp, n⟩ (FR V.E) ∨ ∃ R ∈ V.ins ++ V.outs, VG.Proof.Ed25519.AArch64.Whole.Within ⟨dp, n⟩ R)
    (dS : Region.Disjoint ⟨dp, n⟩ (VG.Proof.Ed448.AArch64.Whole.ST scr)) (dK : Region.Disjoint ⟨dp, n⟩ (VG.Proof.Ed448.AArch64.Whole.KS scr))
    (kD : (CK V.E).Disjoint ⟨dp, n⟩) (hr : Spec.Sha3.Repr t.mem scr 136 msg) :
    WP isa (kabs v.callee d src len pos) t fun u => VG.Proof.Ed448.AArch64.Whole.WCtx V g vec m₀ u ∧
      Frame [VG.Proof.Ed448.AArch64.Whole.ST scr, VG.Proof.Ed448.AArch64.Whole.KS scr, CK V.E] t.mem u.mem ∧
      Spec.Sha3.Repr u.mem scr 136 (msg ++ Spec.Sha3.bytesAt t.mem dp n) ∧
      u.gpr .x0 = BitVec.ofNat 64 ((msg ++ Spec.Sha3.bytesAt t.mem dp n).length % 136) := by
  refine WP.mono (VG.Proof.Ed448.AArch64.Whole.kabs_ok v hV hs hc hvs hvl hvp hrs hrl hdp hn hq (Nat.mod_lt _ (by decide)) hnl hin dS dK kD)
    fun u ⟨hu, hf, hp, hx⟩ => ⟨hu, hf, hp msg hr rfl, ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [hx, VG.Proof.Ed448.AArch64.Whole.toNat_ofNat64 (by omega), List.length_append, VG.Proof.Ed448.AArch64.Whole.sha3_bytesAt_length, Nat.mod_add_mod]

theorem shake256_eq (m : List Byte) (d : Nat) :
    Spec.Sha3.shake256 m d =
      Spec.Sha3.squeezeFrom 136 (Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix m)) 0 d := by
  simp only [Spec.Sha3.squeezeFrom, Nat.zero_add, List.drop_zero]
  rfl

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

end VG.Proof.Ed448.AArch64.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.Whole.CallsCT`. -/
section

/-!
# Ed448's complete operations on AArch64: each call in constant time

The sponge's pieces (`zeroSt_ct`, `kabs_ct`, `kpad_ct`, `ksqz_ct`) and the
calls of the Ed448 primitives (`reduce_ct`, `base_ct`, `mulAdd_ct`,
`equation_ct`), related by `Two`: their arguments have values that agree in
both runs (`val`, or the sponge's positions), which are the callee's public
data, and each run has the effect its correctness lemma gives (`hok`).
-/

namespace VG.Proof.Ed448.AArch64.Whole

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Whole
open VG.Proof.Ed25519.AArch64.Whole (Within FR CK)

variable {V : Env} {g₁ g₂ : Reg → Addr} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}
  {M : Mem → Prop} {d : Nat} {scr : Addr}

theorem regs_get {args : List (Reg × Src)} {val : Reg → Addr} {t : State} (h : Regs args val t) {r : Reg}
    (hr : r ∈ args.map Prod.fst) : t.gpr r = val r := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  exact h p hp

theorem entry_eq {args : List (Reg × Src)} {a b : State}
    (h : ∀ p ∈ args, a.callEntry.gpr p.1 = b.callEntry.gpr p.1) {r : Reg}
    (hr : r ∈ args.map Prod.fst) : a.callEntry.gpr r = b.callEntry.gpr r := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  exact h p hp

/-! ## The sponge -/

theorem zeroSt_ct (hV : V.Ok) (hs : ScrOk V d scr) (h₁ : M m₁) (h₂ : M m₂) {P : State → Prop}
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS [(.x15, .loc d 0)])) hint).isSome = true) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P) (zeroSt d) (Two V g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hd := hV.ls _ hs.kept
  simp only at hd
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp ?_
    (fun _ h => WP.mono (zeroSt_ok hV hs h.1) fun _ hu => ⟨hu.1, trivial⟩)
    (fun _ h => WP.mono (zeroSt_ok hV hs h.1) fun _ hu => ⟨hu.1, trivial⟩)
  refine (setupS_ct hV h₁ h₂ (args := [(.x15, .loc d 0)]) (by simp) (by simp [srcValid, hd.1]; omega) rfl
    (by simp [preserved]) ht (fun _ => scr) fun _ hc _ p hp => ?_).seq ?_
  · rw [List.mem_singleton.mp hp, hs.loc hc, BitVec.add_zero]
  · refine RelCT.taint (A := taint) (Taint.ofRegs [.x15]) (fun a b h => ⟨two_sp h, fun r hr => ?_⟩)
      (by taint_decide)
    simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
    subst hr
    exact (h.1.2 _ List.mem_cons_self).trans (h.2.2 _ List.mem_cons_self).symm

/-- What `absArgs` puts in the registers. -/
def absVal (scr dp : Addr) (n q : Nat) : Reg → Addr
  | .x0 => scr
  | .x1 => BitVec.ofNat 64 136
  | .x2 => BitVec.ofNat 64 q
  | .x3 => dp
  | .x4 => BitVec.ofNat 64 n
  | _ => scr + BitVec.ofNat 64 256

theorem kabs_ct (v : Proof.Sha3.AArch64.Permutation) (hV : V.Ok) (hs : ScrOk V d scr)
    (h₁ : M m₁) (h₂ : M m₂) {src len pos : Src} (hvs : srcValid src) (hvl : srcValid len)
    (hvp : srcValid pos) (hrs : noRet src = true) (hrl : noRet len = true)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS (absArgs d src len pos))) hint).isSome = true)
    {P : State → Prop} {dp : Addr} {n q : Nat}
    (hdp : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t → srcValue V.E t.mem (t.gpr .x0) src = dp)
    (hn : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      srcValue V.E t.mem (t.gpr .x0) len = BitVec.ofNat 64 n)
    (hq : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      srcValue V.E t.mem (t.gpr .x0) pos = BitVec.ofNat 64 q)
    (hql : q < 136) (hnl : n < 2 ^ 64)
    (hin : Within ⟨dp, n⟩ (FR V.E) ∨ ∃ R ∈ V.ins ++ V.outs, Within ⟨dp, n⟩ R)
    (dS : Region.Disjoint ⟨dp, n⟩ (ST scr)) (dK : Region.Disjoint ⟨dp, n⟩ (KS scr))
    (kD : (CK V.E).Disjoint ⟨dp, n⟩) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P) (kabs v.callee d src len pos)
      (Two V g₁ g₂ v₁ v₂ m₁ m₂ fun u => u.gpr .x0 = BitVec.ofNat 64 ((q + n) % 136)) := by
  have hd := hV.ls _ hs.kept
  simp only at hd
  refine callS_ct hV h₁ h₂ (by simp) (fun p hp => by
      simp only [absArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hvp
      · exact ⟨hd.1, hd.2, by decide⟩
      · show (136 : Nat) < 65536; decide
      · exact hvs
      · exact hvl
      · exact ⟨hd.1, hd.2, by decide⟩)
    (by simp only [retOk, List.all_cons, List.all_nil, hrs, hrl]; rfl) (by simp [preserved])
    (by simp [linkRegs]) ht (absVal scr dp n q) (fun hm hc hp p hp' => ?_)
    (Proof.Sha3.AArch64.Stream.Absorb.absorb_correct v) (Proof.Sha3.AArch64.Stream.Absorb.absorb_ct v)
    (fun hc hr => absorb_pre hV hs hc.1.sp (hr (.x0, .loc d 0) (by simp)) (hr (.x1, .val (.const 136)) (by simp))
      (hr (.x2, pos) (by simp)) (hr (.x3, src) (by simp)) (hr (.x4, len) (by simp)) (hr (.x5, .loc d 256) (by simp))
      hql hnl dS dK kD)
    (covers_rw (fun r hr => by rw [List.mem_singleton.mp hr]; exact hin) hs.sponge_writes) hs.sponge_writes
    (fun _ _ hsp hg => ⟨hg (.x0, .loc d 0) (by simp), hg (.x1, .val (.const 136)) (by simp), hg (.x2, pos) (by simp),
      hg (.x3, src) (by simp), hg (.x4, len) (by simp), hg (.x5, .loc d 256) (by simp), hsp⟩)
    (fun hm hc hp => WP.mono (kabs_ok v hV hs hc hvs hvl hvp hrs hrl (hdp hm hc hp) (hn hm hc hp)
      (hq hm hc hp) hql hnl hin dS dK kD) fun _ ⟨hu, _, _, hx⟩ =>
        ⟨hu, BitVec.eq_of_toNat_eq (by rw [hx, toNat_ofNat64 (by omega)])⟩)
  simp only [absArgs, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hq hm hc hp
  · exact (hs.loc hc _ 0).trans (BitVec.add_zero _)
  · rfl
  · exact hdp hm hc hp
  · exact hn hm hc hp
  · exact hs.loc hc _ 256

/-- What `padArgs` puts in the registers. -/
def padVal (scr : Addr) (q : Nat) : Reg → Addr
  | .x0 => scr
  | .x1 => BitVec.ofNat 64 136
  | .x2 => BitVec.ofNat 64 q
  | .x3 => BitVec.ofNat 64 0x1f
  | _ => scr + BitVec.ofNat 64 256

theorem kpad_ct (v : Proof.Sha3.AArch64.Permutation) (hV : V.Ok) (hs : ScrOk V d scr)
    (h₁ : M m₁) (h₂ : M m₂) {pos : Src} (hvp : srcValid pos)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS (padArgs d pos))) hint).isSome = true)
    {P : State → Prop} {q : Nat}
    (hq : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      srcValue V.E t.mem (t.gpr .x0) pos = BitVec.ofNat 64 q)
    (hql : q < 136) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P) (kpad v.callee d pos) (Two V g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hd := hV.ls _ hs.kept
  simp only at hd
  refine callS_ct hV h₁ h₂ (by simp) (fun p hp => by
      simp only [padArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact hvp
      · exact ⟨hd.1, hd.2, by decide⟩
      · show (136 : Nat) < 65536; decide
      · show (0x1f : Nat) < 65536; decide
      · exact ⟨hd.1, hd.2, by decide⟩)
    (by simp only [retOk, List.all_cons, List.all_nil]; rfl) (by simp [preserved])
    (by simp [linkRegs]) ht (padVal scr q) (fun hm hc hp p hp' => ?_)
    (Proof.Sha3.AArch64.Stream.Pad.pad_correct v) (Proof.Sha3.AArch64.Stream.Pad.pad_ct v)
    (fun hc hr => pad_pre hV hs hc.1.sp (hr (.x0, .loc d 0) (by simp)) (hr (.x1, .val (.const 136)) (by simp))
      (hr (.x2, pos) (by simp)) (hr (.x4, .loc d 256) (by simp)) hql)
    (covers_rw (by simp) hs.sponge_writes) hs.sponge_writes
    (fun _ _ hsp hg => ⟨hg (.x0, .loc d 0) (by simp), hg (.x1, .val (.const 136)) (by simp), hg (.x2, pos) (by simp),
      hg (.x4, .loc d 256) (by simp), hsp⟩)
    (fun hm hc hp => WP.mono (kpad_ok v hV hs hc hvp (hq hm hc hp) hql) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩)
  simp only [padArgs, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl
  · exact hq hm hc hp
  · exact (hs.loc hc _ 0).trans (BitVec.add_zero _)
  · rfl
  · rfl
  · exact hs.loc hc _ 256

/-- What `sqzArgs` puts in the registers. -/
def sqzVal (scr op : Addr) : Reg → Addr
  | .x0 => scr
  | .x1 => BitVec.ofNat 64 136
  | .x2 => BitVec.ofNat 64 0
  | .x3 => op
  | .x4 => BitVec.ofNat 64 114
  | _ => scr + BitVec.ofNat 64 256

theorem ksqz_ct (v : Proof.Sha3.AArch64.Permutation) (hV : V.Ok) (hs : ScrOk V d scr)
    (h₁ : M m₁) (h₂ : M m₂) {out : Src} (hvo : srcValid out) (hro : noRet out = true)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS (sqzArgs d out))) hint).isSome = true)
    {P : State → Prop} {op : Addr}
    (hop : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t → srcValue V.E t.mem (t.gpr .x0) out = op)
    (hw : Apart V ⟨op, 114⟩ ∨ ∃ R ∈ V.outs, Within ⟨op, 114⟩ R)
    (dS : Region.Disjoint ⟨op, 114⟩ (ST scr)) (dK : Region.Disjoint ⟨op, 114⟩ (KS scr))
    (kD : (CK V.E).Disjoint ⟨op, 114⟩) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P) (ksqz v.callee d out) (Two V g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hd := hV.ls _ hs.kept
  simp only at hd
  have hws : ∀ r ∈ [ST scr, ⟨op, 114⟩, KS scr], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inr ⟨_, hs.out, st_within scr⟩
    · exact hw
    · exact .inr ⟨_, hs.out, ks_within scr⟩
  refine callS_ct hV h₁ h₂ (by simp) (fun p hp => by
      simp only [sqzArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨hd.1, hd.2, by decide⟩
      · show (136 : Nat) < 65536; decide
      · show (0 : Nat) < 65536; decide
      · exact hvo
      · show (114 : Nat) < 65536; decide
      · exact ⟨hd.1, hd.2, by decide⟩)
    (by simp only [retOk, List.all_cons, List.all_nil, hro]; rfl) (by simp [preserved])
    (by simp [linkRegs]) ht (sqzVal scr op) (fun hm hc hp p hp' => ?_)
    (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_correct v) (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_ct v)
    (fun hc hr => squeeze_pre hV hs hc.1.sp (hr (.x0, .loc d 0) (by simp)) (hr (.x1, .val (.const 136)) (by simp))
      (hr (.x2, .val (.const 0)) (by simp)) (hr (.x3, out) (by simp)) (hr (.x4, .val (.const 114)) (by simp)) (hr (.x5, .loc d 256) (by simp))
      dS dK kD)
    (covers_rw (by simp) hws) hws
    (fun _ _ hsp hg => ⟨hg (.x0, .loc d 0) (by simp), hg (.x1, .val (.const 136)) (by simp), hg (.x2, .val (.const 0)) (by simp),
      hg (.x3, out) (by simp), hg (.x4, .val (.const 114)) (by simp), hg (.x5, .loc d 256) (by simp), hsp⟩)
    (fun hm hc hp => WP.mono (ksqz_ok v hV hs hc hvo hro (hop hm hc hp) hw dS dK kD)
      fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩)
  simp only [sqzArgs, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hs.loc hc _ 0).trans (BitVec.add_zero _)
  · rfl
  · rfl
  · exact hop hm hc hp
  · rfl
  · exact hs.loc hc _ 256

/-! ## The Ed448 primitives -/

theorem reduce_ct (hV : V.Ok) (h₁ : M m₁) (h₂ : M m₂) {args : List (Reg × Src)}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, srcValid p.2) (hret : retOk args = true)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) (hl : ∀ p ∈ args, p.1 ∉ linkRegs)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS args)) hint).isSome = true)
    {P : State → Prop} (val : Reg → Addr)
    (hval : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      ∀ p ∈ args, srcValue V.E t.mem (t.gpr .x0) p.2 = val p.1)
    (hm : ∀ r ∈ [Reg.x0, .x1, .x2], r ∈ args.map Prod.fst)
    (hd : Region.Disjoint ⟨val .x1, 114⟩ ⟨val .x2, 8192⟩) (hrd : Readable V ⟨val .x1, 114⟩)
    (hwo : Writable V ⟨val .x0, 57⟩) (hws : Writable V ⟨val .x2, 8192⟩) {Q : State → Prop}
    (hok : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t → WP isa
      (callS args "vg_ed448_scalar_reduce" Impl.Ed448.AArch64.scalarReduce) t
      fun u => WCtx V g vec m₀ u ∧ Q u) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P)
      (callS args "vg_ed448_scalar_reduce" Impl.Ed448.AArch64.scalarReduce) (Two V g₁ g₂ v₁ v₂ m₁ m₂ Q) := by
  have hw : ∀ r ∈ [(⟨val .x0, 57⟩ : Region), ⟨val .x2, 8192⟩], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [hwo, hws]
  exact callS_ct hV h₁ h₂ hn hv hret hr hl ht val hval Proof.Ed448.AArch64.scalarReduce_ok
    Proof.Ed448.AArch64.scalarReduce_ct
    (fun _ hs => reduce_pre (regs_get hs (hm .x0 (by simp))) (regs_get hs (hm .x1 (by simp)))
      (regs_get hs (hm .x2 (by simp))) hd)
    (covers_rw (fun r hr => by rw [List.mem_singleton.mp hr]; exact hrd) hw) hw
    (fun _ _ hsp hg => ⟨hsp, entry_eq hg (hm .x0 (by simp)), entry_eq hg (hm .x1 (by simp)),
      entry_eq hg (hm .x2 (by simp))⟩) hok

theorem base_ct (hb : Proof.Ed448.AArch64.BaseOk) (hV : V.Ok) (h₁ : M m₁) (h₂ : M m₂)
    {args : List (Reg × Src)}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, srcValid p.2) (hret : retOk args = true)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) (hl : ∀ p ∈ args, p.1 ∉ linkRegs)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS args)) hint).isSome = true)
    {P : State → Prop} (val : Reg → Addr)
    (hval : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      ∀ p ∈ args, srcValue V.E t.mem (t.gpr .x0) p.2 = val p.1)
    (hm : ∀ r ∈ [Reg.x0, .x1, .x2], r ∈ args.map Prod.fst)
    (hos : Region.Disjoint ⟨val .x0, 57⟩ ⟨val .x2, 8192⟩) (hss : Region.Disjoint ⟨val .x1, 57⟩ ⟨val .x2, 8192⟩)
    (hnc : (val .x2).toNat + 8192 ≤ 2 ^ 64) (hrd : Readable V ⟨val .x1, 57⟩)
    (hwo : Writable V ⟨val .x0, 57⟩) (hws : Writable V ⟨val .x2, 8192⟩) {Q : State → Prop}
    (hok : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t → WP isa
      (callS args "vg_ed448_scalar_base" Impl.Ed448.AArch64.scalarBase) t
      fun u => WCtx V g vec m₀ u ∧ Q u) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P)
      (callS args "vg_ed448_scalar_base" Impl.Ed448.AArch64.scalarBase) (Two V g₁ g₂ v₁ v₂ m₁ m₂ Q) := by
  have hw : ∀ r ∈ [(⟨val .x0, 57⟩ : Region), ⟨val .x2, 8192⟩], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [hwo, hws]
  exact callS_ct hV h₁ h₂ hn hv hret hr hl ht val hval hb.ok
    hb.ct
    (fun _ hs => base_pre (regs_get hs (hm .x0 (by simp))) (regs_get hs (hm .x1 (by simp)))
      (regs_get hs (hm .x2 (by simp))) hos hss hnc)
    (covers_rw (fun r hr => by rw [List.mem_singleton.mp hr]; exact hrd) hw) hw
    (fun _ _ hsp hg => ⟨hsp, entry_eq hg (hm .x0 (by simp)), entry_eq hg (hm .x1 (by simp)),
      entry_eq hg (hm .x2 (by simp))⟩) hok

theorem mulAdd_ct (hV : V.Ok) (h₁ : M m₁) (h₂ : M m₂) {args : List (Reg × Src)}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, srcValid p.2) (hret : retOk args = true)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) (hl : ∀ p ∈ args, p.1 ∉ linkRegs)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS args)) hint).isSome = true)
    {P : State → Prop} (val : Reg → Addr)
    (hval : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      ∀ p ∈ args, srcValue V.E t.mem (t.gpr .x0) p.2 = val p.1)
    (hm : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4], r ∈ args.map Prod.fst)
    (hdr : Region.Disjoint ⟨val .x1, 57⟩ ⟨val .x4, 8192⟩) (hdk : Region.Disjoint ⟨val .x2, 57⟩ ⟨val .x4, 8192⟩)
    (hds : Region.Disjoint ⟨val .x3, 57⟩ ⟨val .x4, 8192⟩)
    (hrr : Readable V ⟨val .x1, 57⟩) (hrk : Readable V ⟨val .x2, 57⟩) (hrs : Readable V ⟨val .x3, 57⟩)
    (hwo : Writable V ⟨val .x0, 57⟩) (hws : Writable V ⟨val .x4, 8192⟩) {Q : State → Prop}
    (hok : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t → WP isa
      (callS args "vg_ed448_scalar_mul_add" Impl.Ed448.AArch64.scalarMulAdd) t
      fun u => WCtx V g vec m₀ u ∧ Q u) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P)
      (callS args "vg_ed448_scalar_mul_add" Impl.Ed448.AArch64.scalarMulAdd) (Two V g₁ g₂ v₁ v₂ m₁ m₂ Q) := by
  have hw : ∀ r ∈ [(⟨val .x0, 57⟩ : Region), ⟨val .x4, 8192⟩], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [hwo, hws]
  have hrd : ∀ r ∈ [(⟨val .x1, 57⟩ : Region), ⟨val .x2, 57⟩, ⟨val .x3, 57⟩], Readable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [hrr, hrk, hrs]
  exact callS_ct hV h₁ h₂ hn hv hret hr hl ht val hval Proof.Ed448.AArch64.scalarMulAdd_ok
    Proof.Ed448.AArch64.scalarMulAdd_ct
    (fun _ hs => mulAdd_pre (regs_get hs (hm .x0 (by simp))) (regs_get hs (hm .x1 (by simp)))
      (regs_get hs (hm .x2 (by simp))) (regs_get hs (hm .x3 (by simp))) (regs_get hs (hm .x4 (by simp)))
      hdr hdk hds)
    (covers_rw hrd hw) hw
    (fun _ _ hsp hg => ⟨hsp, entry_eq hg (hm .x0 (by simp)), entry_eq hg (hm .x1 (by simp)),
      entry_eq hg (hm .x2 (by simp)), entry_eq hg (hm .x3 (by simp)), entry_eq hg (hm .x4 (by simp))⟩) hok

theorem equation_ct (hQ : Proof.Ed448.AArch64.EqOk) (hV : V.Ok)
    (h₁ : M m₁) (h₂ : M m₂) {args : List (Reg × Src)}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, srcValid p.2) (hret : retOk args = true)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) (hl : ∀ p ∈ args, p.1 ∉ linkRegs)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS args)) hint).isSome = true)
    {P : State → Prop} (val : Reg → Addr)
    (hval : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      ∀ p ∈ args, srcValue V.E t.mem (t.gpr .x0) p.2 = val p.1)
    (hm : ∀ r ∈ [Reg.x0, .x1, .x2, .x3], r ∈ args.map Prod.fst)
    (hdp : Region.Disjoint ⟨val .x0, 57⟩ ⟨val .x3, 8192⟩) (hds : Region.Disjoint ⟨val .x1, 114⟩ ⟨val .x3, 8192⟩)
    (hdc : Region.Disjoint ⟨val .x2, 57⟩ ⟨val .x3, 8192⟩) (hnc : (val .x3).toNat + 8192 ≤ 2 ^ 64)
    (hrp : Readable V ⟨val .x0, 57⟩) (hrs : Readable V ⟨val .x1, 114⟩) (hrc : Readable V ⟨val .x2, 57⟩)
    (hws : Writable V ⟨val .x3, 8192⟩) {Q : State → Prop}
    (hok : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t → WP isa
      (callS args "vg_ed448_verify_equation" Impl.Ed448.AArch64.verifyEquation) t
      fun u => WCtx V g vec m₀ u ∧ Q u) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P)
      (callS args "vg_ed448_verify_equation" Impl.Ed448.AArch64.verifyEquation)
      (Two V g₁ g₂ v₁ v₂ m₁ m₂ Q) := by
  have hw : ∀ r ∈ [(⟨val .x3, 8192⟩ : Region)], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl
    exact hws
  have hrd : ∀ r ∈ [(⟨val .x0, 57⟩ : Region), ⟨val .x1, 114⟩, ⟨val .x2, 57⟩], Readable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [hrp, hrs, hrc]
  exact callS_ct hV h₁ h₂ hn hv hret hr hl ht val hval (hQ.ok)
    hQ.ct
    (fun _ hs => equation_pre (regs_get hs (hm .x0 (by simp))) (regs_get hs (hm .x1 (by simp)))
      (regs_get hs (hm .x2 (by simp))) (regs_get hs (hm .x3 (by simp))) hdp hds hdc hnc)
    (covers_rw hrd hw) hw
    (fun _ _ hsp hg => ⟨hsp, entry_eq hg (hm .x0 (by simp)), entry_eq hg (hm .x1 (by simp)),
      entry_eq hg (hm .x2 (by simp)), entry_eq hg (hm .x3 (by simp))⟩) hok

end VG.Proof.Ed448.AArch64.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.Whole.Entry`. -/
section

/-!
# Ed448's complete operations on AArch64: words kept in the locals

`keep r d` stores `r` in the locals (`keep_ok`); `hdr d ctxlen` stores the
first ten bytes of `dom4(0, context)` there (`hdr_ok`, `hdr_bytes`).
-/

namespace VG.Proof.Ed448.AArch64.Whole

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Whole
open VG.Impl.Ed25519.AArch64.Whole (Value setArg)

/-- `"SigEd448"`, as a little-endian word. -/
def sigWord : BitVec 64 := 0x3834346445676953

/-- Registers but `x9`, `x15`; the rest of the state but memory. -/
structure Keeps915 (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  v : t.v = s.v
  regs : ∀ r, r ≠ .x9 → r ≠ .x15 → t.gpr r = s.gpr r

theorem Keeps915.trans {s t u : State} (h : VG.Proof.Ed448.AArch64.Whole.Keeps915 s t) (h' : VG.Proof.Ed448.AArch64.Whole.Keeps915 t u) : VG.Proof.Ed448.AArch64.Whole.Keeps915 s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp, h'.v.trans h.v,
    fun r h9 h15 => (h'.regs r h9 h15).trans (h.regs r h9 h15)⟩

/-- `x15 := sp + d`, then `[x15] := r`. -/
theorem keep_ok {s : State} {r : Reg} {d : Nat} (hd : d < 4096)
    (hw : InRegions s.wr (s.sp + BitVec.ofNat 64 d) 8) :
    WP isa (.block (VG.Impl.Ed448.AArch64.Whole.keep r d)) s fun t => VG.Proof.Ed448.AArch64.Whole.Keeps915 s t ∧ t.gpr .x15 = s.sp + BitVec.ofNat 64 d ∧
      t.mem = s.mem.writeW (s.sp + BitVec.ofNat 64 d) ((s.write .x .x15 (s.sp + BitVec.ofNat 64 d)).gpr r) := by
  have ha : exec (.addSp .x15 d) s = some (s.write .x .x15 (s.sp + BitVec.ofNat 64 d)) := by
    simp only [exec, hd, ite_true]
  apply WP.of_runBlock
  simp only [VG.Impl.Ed448.AArch64.Whole.keep, runBlock_cons, runStep_some, ha]
  rw [exec_str_x ⟨by decide, by decide⟩ (by
    simpa only [RegUpd.wr_write, RegUpd.gpr_write, ite_true, BitVec.setWidth_eq, BitVec.add_zero] using hw)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left', RegUpd.gpr_write,
    ite_true, BitVec.setWidth_eq, BitVec.add_zero, RegUpd.mem_write]
  exact ⟨⟨rfl, rfl, rfl, rfl, fun q _ h15 => RegUpd.gpr_write_of_ne _ _ _ h15⟩, trivial, trivial⟩

/-- `x9 := "SigEd448"`. -/
theorem sig_ok (s : State) :
    WP isa (.block [.movz .x .x9 0x6953 0, .movk .x .x9 0x4567 1, .movk .x .x9 0x3464 2,
      .movk .x .x9 0x3834 3]) s fun t => VG.Proof.Ed448.AArch64.Whole.Keeps915 s t ∧ t.gpr .x9 = VG.Proof.Ed448.AArch64.Whole.sigWord ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, RegUpd.gpr_write, RegUpd.mem_write, BitVec.setWidth_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨rfl, rfl, rfl, rfl, fun r h9 _ => ?_⟩, by decide, trivial⟩
  simp only [RegUpd.gpr_write, h9, ite_false]

/-- `x9 := x9 << 8`, then `[x15 + 8] := x9`. -/
theorem shiftStore_ok {s : State} (hw : InRegions s.wr (s.gpr .x15 + BitVec.ofNat 64 8) 8) :
    WP isa (.block [.lsl .x .x9 .x9 8, .str .x .x9 .x15 8]) s fun t => VG.Proof.Ed448.AArch64.Whole.Keeps915 s t ∧
      t.mem = s.mem.writeW (s.gpr .x15 + BitVec.ofNat 64 8) (s.gpr .x9 <<< 8) := by
  have hl : exec (.lsl .x .x9 .x9 8) s = some (s.write .x .x9 (s.gpr .x9 <<< 8)) := by
    simp only [exec, Size.bits, Nat.reduceLT, ite_true, State.read, BitVec.setWidth_eq]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, hl]
  rw [exec_str_x ⟨by decide, by decide⟩ (by
    simpa only [RegUpd.wr_write, RegUpd.gpr_write, reduceCtorEq, ite_false] using hw)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left', RegUpd.gpr_write,
    reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, RegUpd.mem_write]
  exact ⟨⟨rfl, rfl, rfl, rfl, fun q h9 _ => RegUpd.gpr_write_of_ne _ _ _ h9⟩, trivial⟩

/-- The header: `"SigEd448"` at `sp + d`, and the saved argument `j` (`ctxlen`)
shifted by 8 at `sp + d + 8`. -/
theorem hdr_ok {s : State} {d j : Nat} (hd : d + 16 ≤ 256) (hj : j < 6)
    (hw : (⟨s.sp, 256⟩ : Region) ∈ s.wr)
    (hr : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (256 + 8 * j)) 8) :
    WP isa (.block (hdr d (.caller j 0))) s fun t => VG.Proof.Ed448.AArch64.Whole.Keeps915 s t ∧
      t.mem = (s.mem.writeW (s.sp + BitVec.ofNat 64 d) VG.Proof.Ed448.AArch64.Whole.sigWord).writeW (s.sp + BitVec.ofNat 64 (d + 8))
        (s.mem.read (s.sp + BitVec.ofNat 64 (256 + 8 * j)) 8 <<< 8) := by
  rw [hdr, show ([.movz .x .x9 0x6953 0, .movk .x .x9 0x4567 1, .movk .x .x9 0x3464 2, .movk .x .x9 0x3834 3,
      .addSp .x15 d, .str .x .x9 .x15 0] : List Instr) = [.movz .x .x9 0x6953 0, .movk .x .x9 0x4567 1,
      .movk .x .x9 0x3464 2, .movk .x .x9 0x3834 3] ++ VG.Impl.Ed448.AArch64.Whole.keep .x9 d from rfl]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.Whole.sig_ok s) fun a ⟨ka, a9, am⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.Whole.keep_ok (r := .x9) (d := d) (by omega)
    (by rw [ka.wr, ka.sp]; exact ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩))
    fun b ⟨kb, b15, bm⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.Whole.setArg_ok (r := .x9) (v := .caller j 0) rfl
    (show j < 6 ∧ 0 < 4096 from ⟨hj, by decide⟩) (fun j' d' h => by
      cases h; rw [kb.rd, kb.wr, kb.sp, ka.rd, ka.wr, ka.sp]; exact hr)) fun c ⟨kc, c9⟩ => ?_
  have c15 : c.gpr .x15 = s.sp + BitVec.ofNat 64 d := by
    rw [kc.regs _ (by decide), b15, ka.sp]
  refine WP.mono (VG.Proof.Ed448.AArch64.Whole.shiftStore_ok (by
    rw [c15, kc.wr, kb.wr, ka.wr, Offset.add_add]
    exact ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩)) fun t ⟨kt, tm⟩ => ⟨?_, ?_⟩
  · exact ((ka.trans kb).trans ⟨kc.rd, kc.wr, kc.sp, kc.vec, fun r h9 _ => kc.regs r (by simpa using h9)⟩).trans kt
  · have ebm : b.mem = s.mem.writeW (s.sp + BitVec.ofNat 64 d) VG.Proof.Ed448.AArch64.Whole.sigWord := by
      rw [bm, RegUpd.gpr_write_of_ne _ _ _ (by decide : Reg.x9 ≠ .x15), a9, am, ka.sp]
    have ebsp : b.sp = s.sp := kb.sp.trans ka.sp
    have hread : b.mem.read (s.sp + BitVec.ofNat 64 (256 + 8 * j)) 8 =
        s.mem.read (s.sp + BitVec.ofNat 64 (256 + 8 * j)) 8 := by
      rw [ebm]
      simp only [Mem.writeW]
      exact Mem.read_write_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)
    rw [tm, c15, c9, kc.mem]
    simp only [VG.Proof.Ed25519.AArch64.Whole.value, BitVec.add_zero]
    rw [ebsp, hread, ebm, Offset.add_add]

theorem readW_eq_read (m : Mem) (p : Addr) : m.readW p 64 = m.read p 8 := by
  simp only [Mem.readW]; rfl

/-- `"SigEd448" ‖ 0 ‖ c`, the bytes of the header's two words. -/
theorem hdr_bytes (m : Mem) (p : Addr) (c : BitVec 64) (hc : c.toNat < 256) (h0 : m.read p 8 = VG.Proof.Ed448.AArch64.Whole.sigWord)
    (h1 : m.read (p + BitVec.ofNat 64 8) 8 = c <<< 8) :
    Spec.Sha3.bytesAt m p 10 =
      "SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) ++ [BitVec.ofNat 8 0, BitVec.ofNat 8 c.toNat] := by
  have hw : (c <<< 8).toNat = c.toNat * 256 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have e10 : Spec.Sha3.bytesAt m p 10 =
      Spec.Sha3.bytesAt m p 8 ++ (Spec.Sha3.bytesAt m (p + BitVec.ofNat 64 8) 8).take 2 := by
    have a := Proof.X25519.bytesAt_add m p 8 2
    have b := Proof.X25519.bytesAt_add m (p + BitVec.ofNat 64 8) 2 6
    have l := Proof.X25519.length_bytesAt m (p + BitVec.ofNat 64 8) 2
    change Spec.X25519.bytesAt m p 10 = Spec.X25519.bytesAt m p 8 ++
      (Spec.X25519.bytesAt m (p + BitVec.ofNat 64 8) 8).take 2
    rw [a, show (8 : Nat) = 2 + 6 from rfl, b, List.take_left' l]
  have b8 : ∀ q, Spec.Sha3.bytesAt m q 8 = Proof.X25519.leBytes 8 (m.readW q 64).toNat :=
    fun q => Proof.X25519.bytesAt_leBytes_64 m q
  rw [e10, b8, b8, VG.Proof.Ed448.AArch64.Whole.readW_eq_read, VG.Proof.Ed448.AArch64.Whole.readW_eq_read, h0, h1, hw, show Proof.X25519.leBytes 8 sigWord.toNat =
    "SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) by decide]
  refine congrArg (List.append _) ?_
  simp only [Proof.X25519.leBytes_succ, List.take_succ_cons, List.take_zero]
  have e1 : BitVec.ofNat 8 (c.toNat * 256) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, show (0 : BitVec 8).toNat = 0 from rfl]; omega
  have e2 : c.toNat * 256 / 256 = c.toNat := by omega
  rw [e1, e2]
  rfl

theorem read_writeW_self (m : Mem) (a : Addr) (v : BitVec 64) : (m.writeW a v).read a 8 = v := by
  rw [← VG.Proof.Ed448.AArch64.Whole.readW_eq_read]; exact Mem.readW_writeW_self64 _ _ _

theorem read_writeW_sep {m : Mem} {a b : Addr} {v : BitVec 64} (h : Mem.Sep a 8 b 8) :
    (m.writeW b v).read a 8 = m.read a 8 := by
  rw [← VG.Proof.Ed448.AArch64.Whole.readW_eq_read, ← VG.Proof.Ed448.AArch64.Whole.readW_eq_read]; exact Mem.readW_writeW_sep h (by decide)

end VG.Proof.Ed448.AArch64.Whole

end
