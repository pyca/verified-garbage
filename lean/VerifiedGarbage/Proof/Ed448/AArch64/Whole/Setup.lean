import VerifiedGarbage.Impl.Ed448.AArch64.Whole
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Setup
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega

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
    have ha : d % 8 = 0 ∧ d < 32768 := ⟨hd8, by omega⟩
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
