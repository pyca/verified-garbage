module

public import VerifiedGarbage.Impl.Ed448.AArch64.Whole
public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Setup
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Impl.X448.AArch64.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow

/-! ### `Ed448.AArch64.Whole.Setup`, which only this module used -/

section

/-!
# Ed448's complete operations on AArch64: a call's arguments

`setupS args` sets each register to its `Src`'s value (`srcValue`): as
`Whole.setup` does, a word of the locals plus an offset, or `x0` as it was
before (`retOk`: nothing before a `ret` writes `x0`). The locals hold words
the function keeps there (`Kept`), which a write elsewhere leaves
(`Kept.frame`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Whole

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Whole
open VG.Impl.Ed25519.AArch64.Whole (Value setArg)
open VG.Proof.Ed25519.AArch64.Whole (SetupStep)

/-- The value `setSrc` sets, from the frame's base `E`, the memory, and `x0`. -/
def srcValue (E : Addr) (m : Mem) (x0 : BitVec 64) : Src → BitVec 64
  | .val v => VG.Proof.Ed25519.AArch64.Whole.value E m v
  | .loc d o => m.read (E + BitVec.ofNat 64 d) 8 + BitVec.ofNat 64 o
  | .ret => x0

def srcValid : Src → Prop
  | .val v => VG.Proof.Ed25519.AArch64.Whole.valid v
  | .loc d o => d % 8 = 0 ∧ d + 8 ≤ 256 ∧ o < 4096
  | .ret => True

def noRet : Src → Bool
  | .ret => false
  | _ => true

/-- Nothing before a `ret` writes `x0`. -/
def retOk : List (Reg × Src) → Bool
  | [] => true
  | (r, _) :: ps => (r != .x0 || ps.all fun p => noRet p.2) && retOk ps

theorem srcValue_noRet {E : Addr} {m : Mem} {a b : BitVec 64} {v : Src} (h : noRet v = true) :
    srcValue E m a v = srcValue E m b v := by
  cases v <;> first | rfl | simp [noRet] at h

theorem setSrc_ok {s : State} {E : Addr} {r : Reg} {v : Src} (he : s.sp = E) (hv : srcValid v)
    (hr : ∀ j d, v = .val (.caller j d) → InRegions (s.rd ++ s.wr) (E + BitVec.ofNat 64 (256 + 8 * j)) 8)
    (hl : ∀ d o, v = .loc d o → InRegions (s.rd ++ s.wr) (E + BitVec.ofNat 64 d) 8) :
    WP isa (.block (setSrc r v)) s fun t => SetupStep [r] s t ∧ t.gpr r = srcValue E s.mem (s.gpr .x0) v := by
  cases v with
  | val v =>
    exact WP.mono (VG.Proof.Ed25519.AArch64.Whole.setArg_ok he hv (fun j d h => hr j d (by rw [h])))
      fun t ⟨h1, h2⟩ => ⟨h1, h2⟩
  | loc d o =>
    obtain ⟨hd8, hdl, ho⟩ := hv
    have ha : d % 8 = 0 ∧ d < 32768 := ⟨hd8, by omega_using [hdl]⟩
    have hr' := hl d o rfl
    apply WP.of_runBlock
    simp only [setSrc, srcValue, runBlock_cons, runStep_some, runBlock_nil, exec,
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
    simp only [setSrc, srcValue, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
      Nat.reduceLT, ite_true, BitVec.setWidth_eq, BitVec.add_zero, RegUpd.gpr_write_self,
      Option.some.injEq, exists_eq_left']
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, ?_⟩, trivial⟩
    intro q hq
    exact RegUpd.gpr_write_of_ne s .x _ (by simpa using hq)

/-- The arguments set, from the frame `E` and the memory and `x0` before. -/
theorem setupS_ok {s : State} {E : Addr} {args : List (Reg × Src)}
    (he : s.sp = E) (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, srcValid p.2)
    (hret : retOk args = true)
    (hr : ∀ j < 6, InRegions (s.rd ++ s.wr) (E + BitVec.ofNat 64 (256 + 8 * j)) 8)
    (hl : ∀ d, d % 8 = 0 → d + 8 ≤ 256 → InRegions (s.rd ++ s.wr) (E + BitVec.ofNat 64 d) 8) :
    WP isa (.block (setupS args)) s fun t => SetupStep (args.map Prod.fst) s t ∧
      ∀ p ∈ args, t.gpr p.1 = srcValue E s.mem (s.gpr .x0) p.2 := by
  induction args generalizing s with
  | nil => exact WP.block_nil ⟨SetupStep.refl s, fun _ h => by cases h⟩
  | cons p ps ih =>
    obtain ⟨r, v⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [retOk, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hret
    rw [setupS, List.flatMap_cons, WP.block_append_iff]
    have hv0 := hv (r, v) List.mem_cons_self
    refine WP.mono (setSrc_ok he hv0 ?_ ?_) fun u ⟨hu, hval⟩ => ?_
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
      · exact srcValue_noRet (List.all_eq_true.mp hall p hp)

/-! ## Words kept in the locals -/

/-- The locals hold the words `ls` (offset, value). -/
def Kept (E : Addr) (m : Mem) (ls : List (Nat × BitVec 64)) : Prop :=
  ∀ p ∈ ls, m.read (E + BitVec.ofNat 64 p.1) 8 = p.2

/-- Writes that miss the kept words leave them. -/
theorem Kept.frame {E : Addr} {m m' : Mem} {ls : List (Nat × BitVec 64)} (h : Kept E m ls)
    {ws : List Region} (hf : Frame ws m m')
    (hd : ∀ p ∈ ls, ∀ r ∈ ws, Region.Disjoint ⟨E + BitVec.ofNat 64 p.1, 8⟩ r) : Kept E m' ls :=
  fun p hp => (hf.read (Region.contains_self _ _) (hd p hp) (by decide)).trans (h p hp)

/-- A kept word, as a `loc` argument. -/
theorem srcValue_loc {E : Addr} {m : Mem} {x0 : BitVec 64} {ls : List (Nat × BitVec 64)} (h : Kept E m ls)
    {d : Nat} {w : BitVec 64} (hm : (d, w) ∈ ls) (o : Nat) :
    srcValue E m x0 (.loc d o) = w + BitVec.ofNat 64 o := by
  simp only [srcValue]
  rw [h _ hm]

end VG.Proof.Ed448.AArch64.Whole

end

end


/-!
# Ed448's complete operations on AArch64: the state in the frame's body

An `Env` is where a complete operation's buffers are: the frame's base `E`,
the regions it reads (`ins`, with the saved arguments and the comb's tables)
and writes (`outs`), the words kept in its locals (`ls`), and the address of
the comb's tables (`T`, the static `combSym`, which `vg_ed448_scalar_base` and
`vg_ed448_verify_equation` read). `WCtx` is `Whole.Ctx` with the kept words in
place and the static at `T`. A call (`wcall`) or a block (`WCtx.of_frame`) that writes
only regions disjoint from the kept words keeps `WCtx`; `wsetup` sets a
call's arguments.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Whole

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Whole
open VG.Proof.Ed25519.AArch64.Whole (Within FR ARGS CK)

structure Env where
  E : Addr
  ins : List Region
  outs : List Region
  ls : List (Nat × BitVec 64)
  T : Addr
  sym : String := VG.Impl.X448.AArch64.Base.combSym
  words : List (BitVec 64) := VG.Impl.X448.AArch64.Base.combWords

open VG.Impl.X448.AArch64.Base (combSym combWords)

/-- The comb's tables at `T`. -/
abbrev TBL (T : Addr) (words:List (BitVec 64):=combWords) : Region := ⟨T,8*words.length⟩

/-- The comb's words at `T` in `m`. -/
def TblWords (T : Addr) (m : Mem) (words:List (BitVec 64):=combWords) : Prop :=
  ∀ i < words.length,m.readW (T+BitVec.ofNat 64 (8*i)) 64=words.getD i 0

/-- A kept word's region. -/
abbrev slot (E : Addr) (d : Nat) : Region := ⟨E + BitVec.ofNat 64 d, 8⟩

/-- What the layout guarantees. -/
structure Env.Ok (V : Env) : Prop where
  args : ARGS V.E ∈ V.ins
  ls : ∀ p ∈ V.ls, p.1 % 8 = 0 ∧ p.1 + 8 ≤ 256
  fo : ∀ R ∈ V.outs, (FR V.E).Disjoint R
  co : ∀ R ∈ V.outs, (CK V.E).Disjoint R
  e16 : 16 ≤ V.E.toNat
  tin : TBL V.T V.words ∈ V.ins
  tfr : (TBL V.T V.words).Disjoint (FR V.E)
  tck : (TBL V.T V.words).Disjoint (CK V.E)
  tout : ∀ R ∈ V.outs, (TBL V.T V.words).Disjoint R
  tfit : V.T.toNat + 8 * V.words.length ≤ 2 ^ 64

abbrev WCtx (V : Env) (g : Reg → Addr) (vec : VReg → BitVec 128) (m₀ : Mem) (t : State) : Prop :=
  VG.Proof.Ed25519.AArch64.Whole.Ctx V.E g vec m₀ V.ins V.outs t ∧ Kept V.E t.mem V.ls ∧
    t.syms V.sym = V.T

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
    (hw : ∀ r ∈ ws, Apart V r ∨ ∃ R ∈ V.outs, Within r R) (hsy : u.syms = t.syms) :
    WCtx V g vec m₀ u := by
  refine ⟨h.1.of_frame hrd hwr hsp hcs hvs hf fun r hr => ?_, kept_frame hV h.2.1
    (hf.mono fun r hr => List.mem_append_left _ hr) hw, by rw [hsy]; exact h.2.2⟩
  rcases hw r hr with ⟨hf, _⟩ | ⟨R, hR, hs⟩
  · exact .inl hf.sub
  · exact .inr ⟨R, hR, hs.sub⟩

theorem WCtx.regs (h : WCtx V g vec m₀ t)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hsp : u.sp = t.sp)
    (hcs : ∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r)
    (hvs : u.v = t.v) (hm : u.mem = t.mem) (hsy : u.syms = t.syms) : WCtx V g vec m₀ u :=
  ⟨h.1.regs hrd hwr hsp hcs hvs hm, hm ▸ h.2.1, by rw [hsy]; exact h.2.2⟩

/-- The comb's words, as on entry: no write reaches them. -/
theorem WCtx.tbl (hV : V.Ok) (h : WCtx V g vec m₀ t) (hm : TblWords V.T m₀ V.words) : TblWords V.T t.mem V.words :=
  fun i hi => by
    have := hV.tfit
    rw [← hm i hi]
    refine h.1.frame.readW (r := TBL V.T V.words) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, this])) ?_ (by decide)
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hV.tout r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [hV.tfr, hV.tck]

/-- A call's arguments, from the saved arguments, the kept words and `x0`. -/
theorem wsetup_ok (hV : V.Ok) (hc : WCtx V g vec m₀ t) {args : List (Reg × Src)}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, srcValid p.2) (hret : retOk args = true)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (setupS args)) t fun u => WCtx V g vec m₀ u ∧ u.mem = t.mem ∧
      ∀ p ∈ args, u.gpr p.1 = srcValue V.E t.mem (t.gpr .x0) p.2 := by
  refine WP.mono_syms (setupS_ok hc.1.sp hn hv hret ?_ ?_) fun u ⟨ht, hvals⟩ hsy => ?_
  · intro j hj
    rw [hc.1.rd, hc.1.wr]
    refine ⟨ARGS V.E, List.mem_append_left _ hV.args, ?_⟩
    have ha : V.E + BitVec.ofNat 64 (256 + 8 * j) = V.E + 256 + BitVec.ofNat 64 (8 * j) := by
      rw [BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    rw [ha]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
  · intro d _ hd
    exact hc.1.readable_frame (Offset.contains_base _ hd (by omega_using [hd]))
  refine ⟨hc.regs ht.rd ht.wr ht.sp ?_ ht.vec ht.mem hsy, ht.mem, hvals⟩
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
  WP.mono_syms (VG.Proof.Ed25519.AArch64.Whole.call_okF h.1 hv hd hpre hcov
    (fun r hr => (hw r hr).imp And.left id) fun u hu hf hp =>
      fun hsy => hQ u ⟨hu, kept_frame hV h.2.1 hf hw, by rw [hsy]; exact h.2.2⟩ hf hp)
    fun _ hq hsy => hq hsy

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
