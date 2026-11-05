module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Ctl
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Entry
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyBytes
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl

-- separate module: the result's writes outside `scratch` (its own stage `FS`), apart from the controller and
-- the seed's parts, so that a change to either rebuilds only what states the search

/-! # DSA parameter search on RISC-V: the result

`finish_vp`: from the end of the controller's last iteration (`midCfg` at
`lastPos`), `finish` writes `out` (the parameters, or zeros), `used` and the
state's words 0 and 3, and returns the protocol's status: the stage `Fin`,
which is the contract's postcondition once `restore` (`restore_ok'`) gives
back our caller's registers. The last iteration's words say how the search
ended (`mid_end`): with parameters (status 1), with no seeds left (3), or
with a tape that ran out (0), where the tape from the seed's start exhausts
the search if it holds the budget and otherwise sets the next request
(`ranOutResult`).

The writes outside `scratch` end the stage `SS`: `FS` keeps the header (our
caller's registers, the fixed words and the words `W`), the state's words 1
and 2, and the octets of `out`, with memory changed only in the call's
writable regions and the stack below the stack pointer.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Impl.Dsa.RISCV64.ParameterSearch
open VG.Proof.Dsa.Generation (attemptAt iters step pos resAt stAt)

/-- The search's result for the call's parameters. -/
abbrev resG (G : GP) : Spec.Dsa.ParameterSearchResult := Spec.Dsa.parameterSearch G.pLen G.left G.randB

/-- The octets `out` holds at the end. -/
def outB (G : GP) : List Byte :=
  match (resG G).outcome with
  | .accepted a => Spec.Dsa.encodeParams G.pLen G.qLen a
  | _ => List.replicate G.outLen 0

/-- After `finish`: what `restore` needs, the status, `out`, `used`, the
state's words, and the regions written. -/
structure Fin (G : GP) (σ t : State) : Prop where
  pre : CIn STK0 σ
  hG : mkG σ = G
  s6 : t.gpr .s6 = G.scr
  sp : t.sp = σ.sp
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  saved : ∀ i < 12, fw t.mem G (fSave + 8 * i) = σ.gpr (saved.getD i .s0)
  ra : fw t.mem G fRA = σ.gpr .ra
  status : ((t.gpr .a0).setWidth 32).toNat = (resG G).status
  out : Spec.Rsa.bytesAt t.mem G.out G.outLen = outB G
  used : Spec.Rsa.wordsAt t.mem G.used 1 = [BitVec.ofNat 64 (resG G).used]
  state : Spec.Rsa.wordsAt t.mem G.state 4 = [BitVec.ofNat 64 (resG G).remaining, BitVec.ofNat 64 G.pLen,
    BitVec.ofNat 64 (Spec.Dsa.parameterEntropy G.pLen), BitVec.ofNat 64 (resG G).requested]
  frame : Frame [G.rOut, G.rUsed, G.rScr, G.rState, rBelow σ STK0] σ.mem t.mem

/-! ## The stage after the first write outside `scratch` -/

/-- Header words of `scratch` the stage keeps. -/
abbrev WOk (W : List (Nat × BitVec 64)) : Prop := ∀ p ∈ W, p.1 + 8 ≤ hEnd ∧ p.1 % 8 = 0

structure FS (G : GP) (W : List (Nat × BitVec 64)) (ob : List Byte) (σ t : State) : Prop where
  pre : CIn STK0 σ
  hG : mkG σ = G
  sp : t.sp = σ.sp
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  s6 : t.gpr .s6 = G.scr
  saved : ∀ i < 12, fw t.mem G (fSave + 8 * i) = σ.gpr (saved.getD i .s0)
  ra : fw t.mem G fRA = σ.gpr .ra
  fixed : ∀ p ∈ fixedWords G, fw t.mem G p.1 = p.2
  words : ∀ p ∈ W, fw t.mem G p.1 = p.2
  wok : WOk W
  frame : Frame [G.rOut, G.rUsed, G.rScr, G.rState, rBelow σ STK0] σ.mem t.mem
  st8 : t.mem.readW (G.state + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 G.pLen
  st16 : t.mem.readW (G.state + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 (Spec.Dsa.parameterEntropy G.pLen)
  out : Spec.Rsa.bytesAt t.mem G.out G.outLen = ob

section
variable {G : GP} {W : List (Nat × BitVec 64)} {ob : List Byte} {σ s t : State}

theorem FS.pub (h : FS G W ob σ s) : s.gpr .s6 = G.scr ∧ s.sp = G.sp :=
  ⟨h.s6, by rw [h.sp, ← h.hG]; rfl⟩

theorem FS.of_keep {ws : List Reg} (h : FS G W ob σ s) (r : Keep ws s t) (m : t.mem = s.mem)
    (sp : t.sp = s.sp) (h6 : .s6 ∉ ws := by decide) : FS G W ob σ t :=
  ⟨h.pre, h.hG, sp.trans h.sp, r.2.1.trans h.rd, r.2.2.trans h.wr, (r.gpr h6).trans h.s6,
    by rw [m]; exact h.saved, by rw [m]; exact h.ra, by rw [m]; exact h.fixed, by rw [m]; exact h.words, h.wok,
    by rw [m]; exact h.frame, by rw [m]; exact h.st8, by rw [m]; exact h.st16, by rw [m]; exact h.out⟩

theorem FS.of_upd {r : Reg} {v : BitVec 64} (h : FS G W ob σ s) (u : Upd s t r v) (h6 : r ≠ .s6) :
    FS G W ob σ t :=
  h.of_keep (ws := [r]) ⟨fun r' hr' => u.other r' (by simpa using hr'), u.rd, u.wr⟩ u.mem u.sp
    (by simpa using h6.symm)

theorem FS.scrFit (h : FS G W ob σ s) : G.scr.toNat + G.scrLen * 8 ≤ 2 ^ 64 := by
  have := h.pre.nC; rw [← h.hG]; exact this

theorem FS.hEnd_le (h : FS G W ob σ s) : hEnd ≤ G.scrLen * 8 := by
  have := h.pre.scrLen; rw [h.hG] at this
  simp only [Spec.Dsa.generationScratchWords, hEnd, fSave] at this ⊢; omega

/-- A load of a header word whose value is known. -/
theorem FS.ldK (h : FS G W ob σ s) {o : Nat} (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) {v : BitVec 64}
    (hv : fw s.mem G o = v) {r : Reg} (hr : r ≠ .s6) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', FS G W ob σ s' → Upd s s' r v → WP isa (.block rest) s' Q) :
    WP isa (.block (ld r o :: rest)) s Q := by
  have hE := h.hEnd_le
  have fit := h.scrFit
  have hal : G.scr.toNat % 8 = 0 := by have := h.pre.alC; rw [← h.hG]; exact this
  have hal' : (G.scr + BitVec.ofNat 64 o).toNat % 8 = 0 := by
    have e : (G.scr + BitVec.ofNat 64 o).toNat = G.scr.toNat + o := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [e]; omega
  have hin : InRegions (s.rd ++ s.wr) (G.scr + BitVec.ofNat 64 o) 8 :=
    ⟨G.rScr, List.mem_append_right _ (by rw [h.wr, h.pre.wr, h.hG]; simp),
      Offset.contains_base _ (by omega) (by omega)⟩
  refine wp_ld (by simp only [hEnd, fSave] at ho; omega) (by rw [h.s6]) hal' hin fun s' u => ?_
  have u' : Upd s s' r v := by rw [← hv]; exact u
  exact k s' (h.of_upd u' hr) u'

/-- Memory changed only in regions apart from `scratch`, the state's words 1 and
2, and `out` (or `out` alone, to `ob'`) keeps the stage. -/
theorem FS.of_frame {ob' : List Byte} {rs : List Region} (h : FS G W ob σ s) {t : State} (r : Keep [] s t)
    (sp : t.sp = s.sp) (f : Frame rs s.mem t.mem)
    (hsub : ∀ x ∈ rs, ∃ y ∈ [G.rOut, G.rUsed, G.rScr, G.rState, rBelow σ STK0], Region.Sub x y)
    (hdS : ∀ x ∈ rs, G.rScr.Disjoint x)
    (hd8 : ∀ x ∈ rs, (⟨G.state + BitVec.ofNat 64 8, 16⟩ : Region).Disjoint x)
    (hout : Spec.Rsa.bytesAt t.mem G.out G.outLen = ob') : FS G W ob' σ t := by
  have hE := h.hEnd_le
  have fit := h.scrFit
  have hw : ∀ {o : Nat}, o + 8 ≤ hEnd → fw t.mem G o = fw s.mem G o := fun {o} ho =>
    f.readW (r := G.rs o 8) (Region.contains_self _ _) (fun x hx => (hdS x hx).sub_left (sw G (by omega)))
      (by decide)
  have fT := h.pre.nT
  have e7 : (σ.gpr .a7) = G.state := by rw [← h.hG]; rfl
  refine ⟨h.pre, h.hG, sp.trans h.sp, r.2.1.trans h.rd, r.2.2.trans h.wr, (r.gpr (by simp)).trans h.s6,
    fun i hi => by rw [hw (by simp only [hEnd]; omega)]; exact h.saved i hi, by rw [hw (by decide)]; exact h.ra,
    fun p hp => by rw [hw (by have := (fixed_ok G p hp).1; simp only [hEnd]; omega)]; exact h.fixed p hp,
    fun p hp => by rw [hw (h.wok p hp).1]; exact h.words p hp, h.wok, h.frame.trans (f.sub hsub), ?_, ?_, hout⟩
  · rw [f.readW (r := ⟨G.state + BitVec.ofNat 64 8, 16⟩) (by simp [Region.Contains]) hd8 (by decide)]
    exact h.st8
  · rw [f.readW (r := ⟨G.state + BitVec.ofNat 64 8, 16⟩) (by
      simp only [Region.Contains]
      rw [show G.state + BitVec.ofNat 64 16 = (G.state + BitVec.ofNat 64 8) + BitVec.ofNat 64 8 by
        rw [BitVec.add_assoc]; rfl, Offset.add_sub_cancel_left]
      decide) hd8 (by decide)]
    exact h.st16

end

/-! ## How the last iteration ended -/

/-- The end of an iteration at `p` that did not reject: its words, and the
result of the whole search from `p` for each status. -/
theorem mid_end {G : GP} {cl0 : Claims} (p : Nat × Nat) (hst : stAt G.pLen G.randB p ≠ 2)
    (hRL : G.randB.length = G.randLen) (hw : 0 < G.pLen) :
    ∃ u extra, midCfg G cl0 p =
        (endCfg cl0 (stAt G.pLen G.randB p) p.1 p.2 u extra).setV fStatus
          (BitVec.ofNat 64 (stAt G.pLen G.randB p)) ∧
      (stAt G.pLen G.randB p = 1 → ∃ a, extra = [(sPacked, Spec.Dsa.encodeParams G.pLen G.qLen a)] ∧
        resAt G.pLen G.randB p = ⟨.accepted a, u, []⟩) ∧
      (stAt G.pLen G.randB p = 3 → resAt G.pLen G.randB p = ⟨.exhausted, p.2, []⟩) ∧
      (stAt G.pLen G.randB p = 0 →
        resAt G.pLen G.randB p = VG.Proof.Dsa.Generation.ranOutResult G.pLen p.1 (G.randLen - p.2) p.2) := by
  obtain ⟨k, c⟩ := p
  cases k with
  | zero =>
    refine ⟨0, [], by simp [midCfg, midBase, stAt], fun h => by simp [stAt] at h, fun _ => ?_,
      fun h => by simp [stAt] at h⟩
    exact VG.Proof.Dsa.Generation.search_zero _ _ _
  | succ k =>
    by_cases hs : G.randB.length - c < G.qLen
    · have h0 : stAt G.pLen G.randB (k + 1, c) = 0 := by simp [stAt, hs]
      refine ⟨0, [], by simp [midCfg, midBase, h0, hs], fun h => absurd h (by omega), fun h => absurd h (by omega), fun _ => ?_⟩
      rw [← hRL]; exact VG.Proof.Dsa.Generation.search_short hs
    · have hq0 : 0 < G.qLen := by simp only [GP.qLen, Spec.Dsa.generationQLen]; split <;> omega
      have hcq : c + G.qLen ≤ G.randB.length := by omega
      rcases e : attemptAt G.pLen G.randB c with _ | ⟨_ | a, r⟩
      · have h0 : stAt G.pLen G.randB (k + 1, c) = 0 := by simp [stAt, hs, e]
        refine ⟨0, [], by simp [midCfg, midBase, h0, hs, e, attCfg], fun h => absurd h (by omega), fun h => absurd h (by omega),
          fun _ => ?_⟩
        rw [← hRL]; exact VG.Proof.Dsa.Generation.search_attemptNone hw hcq e
      · exact absurd (by simp [stAt, hs, e]) hst
      · have h1 : stAt G.pLen G.randB (k + 1, c) = 1 := by simp [stAt, hs, e]
        obtain ⟨hr, hu⟩ := VG.Proof.Dsa.Generation.rest_drop hcq e
        refine ⟨G.randLen - r.length, [(sPacked, Spec.Dsa.encodeParams G.pLen G.qLen a)],
          by simp [midCfg, midBase, h1, hs, e, attCfg], fun _ => ⟨a, rfl, ?_⟩, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
        rw [hr] at e
        rw [← hRL]
        exact VG.Proof.Dsa.Generation.search_accepted hw hcq (by omega) e

/-! ## Into the stage, and the stores through pointers -/

section
variable {G : GP} {W : List (Nat × BitVec 64)} {ob : List Byte} {σ s t : State}

/-- The call's disjoint regions, in terms of its parameters. -/
theorem CIn.disj (pre : CIn STK0 σ) (hG : mkG σ = G) :
    G.rOut.Disjoint G.rUsed ∧ G.rOut.Disjoint G.rScr ∧ G.rOut.Disjoint G.rState ∧ G.rUsed.Disjoint G.rScr ∧
      G.rUsed.Disjoint G.rState ∧ G.rScr.Disjoint G.rState ∧ (rBelow σ STK0).Disjoint G.rState ∧
      G.out.toNat + G.outLen ≤ 2 ^ 64 ∧ G.used.toNat + 8 ≤ 2 ^ 64 ∧ G.state.toNat + 32 ≤ 2 ^ 64 ∧
      G.used.toNat % 8 = 0 ∧ G.state.toNat % 8 = 0 := by
  subst hG
  exact ⟨pre.oU, pre.oC, pre.oT, pre.uC, pre.uT, pre.cT, pre.bT, pre.nO, pre.nU, pre.nT, pre.alU, pre.alT⟩

/-- The state's word 1 and 2 on entry. -/
theorem CIn.st8 (_pre : CIn STK0 σ) (hG : mkG σ = G) :
    σ.mem.readW (G.state + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 G.pLen := by
  subst hG; show _ = BitVec.ofNat 64 (σ.mem.readW (σ.gpr .a7 + 8) 64).toNat
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl

theorem CIn.st16 (pre : CIn STK0 σ) (hG : mkG σ = G) :
    σ.mem.readW (G.state + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 (Spec.Dsa.parameterEntropy G.pLen) := by
  subst hG; exact pre.budget

theorem in16 (a : Addr) :
    Region.Sub ⟨a + BitVec.ofNat 64 8, 16⟩ ⟨a, 32⟩ := Offset.sub_base _ (by decide)

/-- A stage of the search, through a write to `out` alone, as the stage after it. -/
theorem FS.of_SS {c : Cfg} {ws : List Reg} (h : SS G STK0 σ c s) (W : List (Nat × BitVec 64))
    (hW : ∀ p ∈ W, p.1 ∈ c.LS ∧ c.V p.1 = p.2) (hWok : WOk W) (r : Keep ws s t) (h6 : .s6 ∉ ws)
    (sp : t.sp = s.sp) (f : Frame [G.rOut] s.mem t.mem)
    (hout : Spec.Rsa.bytesAt t.mem G.out G.outLen = ob) : FS G W ob σ t := by
  have gi := h.gi
  obtain ⟨dOU, dOC, dOT, dUC, dUT, dCT, dBT, nO, nU, nT, aU, aT⟩ := gi.pre.disj gi.hG
  have hE := gi.hEnd_le
  have fit := gi.scrFit
  have hw : ∀ {o : Nat}, o + 8 ≤ hEnd → fw t.mem G o = fw s.mem G o := fun {o} ho =>
    f.readW (r := G.rs o 8) (Region.contains_self _ _)
      (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact (dOC.symm.sub_left (sw G (by omega))))
      (by decide)
  have s16 : ∀ x ∈ [G.rScr, rBelow σ STK0, G.rOut], (⟨G.state + BitVec.ofNat 64 8, 16⟩ : Region).Disjoint x :=
    fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact dCT.symm.sub_left (in16 _)
      · exact dBT.symm.sub_left (in16 _)
      · exact dOT.symm.sub_left (in16 _)
  have f2 : Frame [G.rScr, rBelow σ STK0, G.rOut] σ.mem t.mem :=
    (gi.frame.mono (by simp)).trans (f.mono (by simp))
  have r16 : ∀ {d : Nat}, (d = 8 ∨ d = 16) →
      t.mem.readW (G.state + BitVec.ofNat 64 d) 64 = σ.mem.readW (G.state + BitVec.ofNat 64 d) 64 :=
    fun {d} hd => f2.readW (r := ⟨G.state + BitVec.ofNat 64 8, 16⟩) (by
      rcases hd with rfl | rfl
      · simp [Region.Contains]
      · simp only [Region.Contains]
        rw [show G.state + BitVec.ofNat 64 16 = (G.state + BitVec.ofNat 64 8) + BitVec.ofNat 64 8 by
          rw [BitVec.add_assoc]; rfl, Offset.add_sub_cancel_left]
        decide) s16 (by decide)
  refine ⟨gi.pre, gi.hG, sp.trans gi.sp, r.2.1.trans gi.rd, r.2.2.trans gi.wr, (r.gpr h6).trans gi.s6,
    fun i hi => by rw [hw (by simp only [hEnd]; omega)]; exact gi.saved i hi, by rw [hw (by decide)]; exact gi.ra,
    fun p hp => by rw [hw (by have := (fixed_ok G p hp).1; simp only [hEnd]; omega)]; exact gi.fixed p hp,
    fun p hp => by rw [hw (hWok p hp).1, gi.slotV (hW p hp).1, (hW p hp).2], hWok,
    f2.mono (by simp), by rw [r16 (.inl rfl)]; exact gi.pre.st8 gi.hG,
    by rw [r16 (.inr rfl)]; exact gi.pre.st16 gi.hG, hout⟩

/-- A store of a register to `used`. -/
theorem FS.sdUsed (h : FS G W ob σ s) {r b : Reg} (hb : s.gpr b = G.used) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ t, FS G W ob σ t → Mupd s t (s.mem.writeW G.used (s.gpr r)) → WP isa (.block rest) t Q) :
    WP isa (.block (.store .d r b 0 :: rest)) s Q := by
  obtain ⟨dOU, dOC, dOT, dUC, dUT, dCT, dBT, nO, nU, nT, aU, aT⟩ := h.pre.disj h.hG
  have hin : InRegions s.wr G.used 8 := ⟨G.rUsed, by rw [h.wr, h.pre.wr, h.hG]; simp, Region.contains_self _ _⟩
  refine wp_sd (by decide) (by rw [hb, BitVec.add_zero]) aU hin fun t m => k t ?_ m
  have f : Frame [G.rUsed] s.mem t.mem := by
    rw [m.mem]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  refine h.of_frame ⟨fun _ _ => by rw [m.gpr], m.rd, m.wr⟩ m.sp f
    (fun x hx => ⟨G.rUsed, by simp, by simp only [List.mem_singleton] at hx; subst hx; exact fun _ h => h⟩)
    (by simpa using dUC.symm)
    (by simpa using (dUT.symm.sub_left (in16 _))) ?_
  rw [VG.Proof.Dsa.Generation.frame_bytesAt f (by simpa using dOU) (by omega)]; exact h.out

/-- A store of a register to the state's word `d / 8`, for `d` 0 or 24. -/
theorem FS.sdState (h : FS G W ob σ s) {r b : Reg} (hb : s.gpr b = G.state) {d : Nat} (hd : d = 0 ∨ d = 24)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, FS G W ob σ t → Mupd s t (s.mem.writeW (G.state + BitVec.ofNat 64 d) (s.gpr r)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (.store .d r b d :: rest)) s Q := by
  obtain ⟨dOU, dOC, dOT, dUC, dUT, dCT, dBT, nO, nU, nT, aU, aT⟩ := h.pre.disj h.hG
  have hc : G.rState.Contains (G.state + BitVec.ofNat 64 d) 8 := Offset.contains_base _ (by omega) (by omega)
  have hin : InRegions s.wr (G.state + BitVec.ofNat 64 d) 8 := ⟨G.rState, by rw [h.wr, h.pre.wr, h.hG]; simp, hc⟩
  have hal : (G.state + BitVec.ofNat 64 d).toNat % 8 = 0 := al_add aT (by omega) nT (by omega)
  refine wp_sd (by omega) (by rw [hb]) hal hin fun t m => k t ?_ m
  have sub : Region.Sub ⟨G.state + BitVec.ofNat 64 d, 8⟩ G.rState := Offset.sub_base _ (by omega)
  have f : Frame [⟨G.state + BitVec.ofNat 64 d, 8⟩] s.mem t.mem := by
    rw [m.mem]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  refine h.of_frame ⟨fun _ _ => by rw [m.gpr], m.rd, m.wr⟩ m.sp f
    (fun x hx => ⟨G.rState, by simp, by simp only [List.mem_singleton] at hx; subst hx; exact sub⟩)
    (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact dCT.sub_right sub)
    (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact Offset.disjoint _ (by omega) (by decide) (by omega)) ?_
  rw [VG.Proof.Dsa.Generation.frame_bytesAt f (by simpa using dOT.sub_right sub) (by omega)]; exact h.out

end

/-! ## `used` and the state's words -/

section
variable {G : GP} {W : List (Nat × BitVec 64)} {ob : List Byte}

theorem state_sep (G : GP) :
    Mem.Sep G.state (64 / 8) (G.state + BitVec.ofNat 64 24) (64 / 8) := by
  have := Offset.disjoint G.state (d := 0) (n := 8) (e := 24) (k := 8) (by omega) (by decide) (by decide)
  rw [BitVec.add_zero] at this
  exact sep_of_disjoint this

/-- `words o`: `used := ` the header word `o`, the state's words 0 and 3 :=
`t4` and `t5`. -/
theorem words_vp {o : Nat} {v x4 x5 : BitVec 64} (ho : (o, v) ∈ W) {F : State → State → Prop}
    (hF : ∀ σ s, F σ s → FS G W ob σ s ∧ s.gpr .t4 = x4 ∧ s.gpr .t5 = x5) :
    VP F (Geo.words o) (fun σ t => FS G W ob σ t ∧ t.mem.readW G.used 64 = v ∧ t.mem.readW G.state 64 = x4 ∧
      t.mem.readW (G.state + BitVec.ofNat 64 24) 64 = x5) := by
  simp only [Geo.words, Impl.Rsa.RISCV64.Keys.seqs]
  refine VP.seq (G := fun σ t => FS G W ob σ t ∧ t.gpr .t2 = v ∧ t.gpr .t3 = G.used ∧ t.gpr .t4 = x4 ∧
    t.gpr .t5 = x5) ?_ (VP.seq (G := fun σ t => FS G W ob σ t ∧ t.mem.readW G.used 64 = v ∧ t.gpr .t4 = x4 ∧
    t.gpr .t5 = x5) ?_ (VP.seq (G := fun σ t => (FS G W ob σ t ∧ t.mem.readW G.used 64 = v ∧ t.gpr .t4 = x4 ∧
    t.gpr .t5 = x5) ∧ t.gpr .t3 = G.state) ?_ ?_))
  · refine VP.pub (G := G) (fun σ s h => (hF σ s h).1.pub) []
      ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block [ld .t2 o, ld .t3 fUsedArg]),
        by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
    obtain ⟨h, h4, h5⟩ := hF σ s hs
    refine h.ldK (h.wok _ ho).1 (h.wok _ ho).2 (h.words _ ho) (r := .t2) (by decide) fun s₁ h₁ u₁ => ?_
    refine h₁.ldK (o := fUsedArg) (by decide) (by decide) (h₁.fixed (fUsedArg, G.used) (by simp [fixedWords])) (r := .t3)
      (by decide) fun s₂ h₂ u₂ => WP.block_nil ⟨h₂, ?_, u₂.gpr, ?_, ?_⟩
    · rw [u₂.other _ (by decide), u₁.gpr]
    · rw [u₂.other _ (by decide), u₁.other _ (by decide), h4]
    · rw [u₂.other _ (by decide), u₁.other _ (by decide), h5]
  · refine VP.pub (G := G) (fun σ s h => h.1.pub) [.t3]
      ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .t3]) (.block [.store .d .t2 .t3 0]),
        by kernel_rfl⟩ (fun _ _ _ _ h₁ h₂ r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.1, h₂.2.2.1]) fun σ s ⟨h, h2, h3, h4, h5⟩ => ?_
    refine h.sdUsed h3 fun t ht m => WP.block_nil ⟨ht, ?_, by rw [m.gpr, h4], by rw [m.gpr, h5]⟩
    rw [m.mem, Mem.readW_writeW_self64, h2]
  · refine VP.pub (G := G) (fun σ s h => h.1.pub) []
      ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block [ld .t3 fState]),
        by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, hu, h4, h5⟩ => ?_
    refine h.ldK (o := fState) (by decide) (by decide) (h.fixed (fState, G.state) (by simp [fixedWords])) (r := .t3)
      (by decide) fun s₁ h₁ u₁ => WP.block_nil ⟨⟨h₁, by rw [u₁.mem, hu], ?_, ?_⟩, u₁.gpr⟩
    · rw [u₁.other _ (by decide), h4]
    · rw [u₁.other _ (by decide), h5]
  · refine VP.pub (G := G) (fun σ s h => h.1.1.pub) [.t3]
      ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .t3])
        (.block [.store .d .t4 .t3 0, .store .d .t5 .t3 24]), by kernel_rfl⟩ (fun _ _ _ _ h₁ h₂ r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]) fun σ s ⟨⟨h, hu, h4, h5⟩, h3⟩ => ?_
    obtain ⟨dOU, dOC, dOT, dUC, dUT, dCT, dBT, nO, nU, nT, aU, aT⟩ := h.pre.disj h.hG
    refine h.sdState (d := 0) h3 (.inl rfl) fun t ht m => ?_
    refine ht.sdState (d := 24) (by rw [m.gpr, h3]) (.inr rfl) fun t' ht' m' => WP.block_nil ⟨ht', ?_, ?_, ?_⟩
    · have hd : Region.Disjoint ⟨G.used, 8⟩ ⟨G.state + BitVec.ofNat 64 24, 8⟩ :=
        dUT.sub_right (Offset.sub_base _ (by decide))
      have hd0 : Region.Disjoint ⟨G.used, 8⟩ ⟨G.state + BitVec.ofNat 64 0, 8⟩ :=
        dUT.sub_right (Offset.sub_base _ (by decide))
      rw [m'.mem, Mem.readW_writeW_sep (sep_of_disjoint hd) (by decide), m.mem,
        Mem.readW_writeW_sep (sep_of_disjoint hd0) (by decide), hu]
    · rw [m'.mem, Mem.readW_writeW_sep (state_sep G) (by decide), m.mem, BitVec.add_zero,
        Mem.readW_writeW_self64, h4]
    · rw [m'.mem, Mem.readW_writeW_self64, m.gpr, h5]

end

/-! ## The tail of every case -/

/-- After the words and the status: `out` holds `ob`, the status `r`, `used`
`v`, the state's words 0 and 3 `x4` and `x5`. -/
def Done (G : GP) (ob : List Byte) (r : Nat) (v x4 x5 : BitVec 64) (σ t : State) : Prop :=
  ∃ W, FS G W ob σ t ∧ t.gpr .a0 = BitVec.ofNat 64 r ∧ t.mem.readW G.used 64 = v ∧
    t.mem.readW G.state 64 = x4 ∧ t.mem.readW (G.state + BitVec.ofNat 64 24) 64 = x5

section
variable {G : GP} {W : List (Nat × BitVec 64)} {ob : List Byte}

/-- `t4 := 0`, `t5 := 0`. -/
theorem zero45_vp {F : State → State → Prop} (hF : ∀ σ s, F σ s → FS G W ob σ s) :
    VP F (.block [.li .t4 0, .li .t5 0])
      (fun σ t => FS G W ob σ t ∧ t.gpr .t4 = BitVec.ofNat 64 0 ∧ t.gpr .t5 = BitVec.ofNat 64 0) := by
  refine VP.pub (G := G) (fun σ s h => (hF σ s h).pub) []
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block [.li .t4 0, .li .t5 0]),
      by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  refine wp_li (imm := 0) (by decide) fun s₁ u₁ => wp_li (imm := 0) (by decide) fun s₂ u₂ => WP.block_nil
    ⟨((hF σ s hs).of_upd u₁ (by decide)).of_upd u₂ (by decide), by rw [u₂.other _ (by decide), u₁.gpr], u₂.gpr⟩

/-- `words o` and the status `r`. -/
theorem tail_vp {o r : Nat} {v x4 x5 : BitVec 64} (hr : r < 2048) (ho : (o, v) ∈ W) {F : State → State → Prop}
    (hF : ∀ σ s, F σ s → FS G W ob σ s ∧ s.gpr .t4 = x4 ∧ s.gpr .t5 = x5) :
    VP F (.seq (Geo.words o) (.block [.li .a0 r])) (Done G ob r v x4 x5) := by
  refine VP.seq (words_vp ho hF) ?_
  refine VP.pub (G := G) (fun σ s h => h.1.pub) []
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block [.li .a0 r]),
      by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, hu, h4, h5⟩ => ?_
  refine wp_li hr fun t u => WP.block_nil ⟨W, h.of_upd u (by decide), u.gpr, by rw [u.mem, hu], by rw [u.mem, h4],
    by rw [u.mem, h5]⟩

theorem setWidth_ofNat_small {r : Nat} (hr : r < 2 ^ 32) : ((BitVec.ofNat 64 r).setWidth 32).toNat = r := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show r < 2 ^ 64 by omega), Nat.mod_eq_of_lt hr]

/-- `Done` with the search's result is `Fin`. -/
theorem fin_of_done {σ t : State}
    (h : Done G (outB G) (resG G).status (BitVec.ofNat 64 (resG G).used) (BitVec.ofNat 64 (resG G).remaining)
      (BitVec.ofNat 64 (resG G).requested) σ t) : Fin G σ t := by
  obtain ⟨W, f, a0, hu, h0, h24⟩ := h
  have hs : (resG G).status < 4 := by
    simp only [Spec.Entropy.Result.status]; cases (resG G).outcome <;> simp [Spec.Entropy.Outcome.status]
  refine ⟨f.pre, f.hG, f.s6, f.sp, f.rd, f.wr, f.saved, f.ra, by rw [a0, setWidth_ofNat_small (by omega)], f.out,
    ?_, ?_, f.frame⟩
  · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
    rw [hu]
  · simp only [Spec.Rsa.wordsAt]
    show [t.mem.readW (G.state + BitVec.ofNat 64 0) 64, t.mem.readW (G.state + BitVec.ofNat 64 8) 64,
      t.mem.readW (G.state + BitVec.ofNat 64 16) 64, t.mem.readW (G.state + BitVec.ofNat 64 24) 64] = _
    rw [show G.state + BitVec.ofNat 64 0 = G.state by simp, h0, f.st8, f.st16, h24]

end

/-! ## `out`: the parameters, or zeros -/

section
variable {G : GP}

/-- The claim of `n` octets at `sPacked` (`p || q || g`) copied to `out`. -/
theorem copyOut_vp {F : State → State → Prop} {c : Cfg} {bs : List Byte} {n : Nat}
    (hF : ∀ σ s, F σ s → SS G STK0 σ c s) (hb : (sPacked, bs) ∈ c.cl) (hbl : bs.length = n)
    (hn : n = G.outLen) (hn0 : 0 < G.outLen) (hn2 : G.outLen < 2048)
    (W : List (Nat × BitVec 64)) (hW : ∀ p ∈ W, p.1 ∈ c.LS ∧ c.V p.1 = p.2) (hWok : WOk W) :
    VP F (copyN (scrB .a0 sPacked) [ld .a1 fOut] n) (FS G W bs) := by
  subst hn
  let M : State → State → Prop := fun σ t => SS G STK0 σ c t ∧
    t.gpr .a0 = G.sa sPacked ∧ t.gpr .a1 = G.out ∧ t.gpr .a2 = BitVec.ofNat 64 G.outLen
  refine VP.seq (G := M) (VP.pub (SS.pub hF) []
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6])
      (.block (scrB .a0 sPacked ++ ([ld .a1 fOut] : List Instr) ++ ([.li .a2 G.outLen] : List Instr))), by kernel_rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s hs => WP.mono (pro_big_ld hF (o := sPacked) (f := fOut) (P := G.out) (by decide) (by decide)
      (by decide) (by decide) (fun σ s hs => (hF σ s hs).gi.fixedV (by simp [fixedWords])) hn2 σ s hs)
      fun t ⟨K, m, sp, a0, a1, a2⟩ => ⟨(hF σ s hs).of_keep K m sp, a0, a1, a2⟩) ?_
  refine VP.pub (G := G) (fun σ t h => ⟨h.1.gi.s6, by rw [h.1.gi.sp, ← h.1.gi.hG]; rfl⟩) [.a0, .a1, .a2]
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .a0, .a1, .a2])
      (Impl.Words.RISCV64.copyLoop .a3 .a0 .a1 .a2), by kernel_rfl⟩
    (fun σ₁ σ₂ s₁ s₂ ⟨_, a0, a1, a2⟩ ⟨_, b0, b1, b2⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a0, b0]
      · rw [a1, b1]
      · rw [a2, b2]) fun σ t ⟨h, t0, t1, t2⟩ => ?_
  have gi := h.gi
  have fit := gi.scrFit
  obtain ⟨dOU, dOC, dOT, dUC, dUT, dCT, dBT, nO, nU, nT, aU, aT⟩ := gi.pre.disj gi.hG
  have oE : sPacked + G.outLen ≤ G.scrLen * 8 := by have := (h.clOk _ hb).2.2; rw [← hbl]; exact this
  have sb : Spec.Rsa.bytesAt t.mem (G.sa sPacked) G.outLen = bs := by have := h.sb _ hb; rw [← hbl]; exact this
  refine WP.sp_eq (WP.mono (copyLoop_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) t
    hn0 (by omega) t2 (fun i hi => by rw [t0, GP.sa_add]; exact gi.inRdWr (o := sPacked + i) (n := 1) (by omega))
    (fun i hi => by
      rw [t1]
      exact ⟨G.rOut, by rw [gi.wr, gi.pre.wr, gi.hG]; simp, Offset.contains_base _ (by omega) (by omega)⟩)
    (by rw [t0, t1]; exact sep_of_disjoint (dOC.sub_right (sw G oE))))
    fun u ⟨cp, f, kp⟩ spu => ?_)
  refine FS.of_SS h W hW hWok kp (by decide) spu (by rw [t1] at f; exact f) ?_
  rw [← sb]
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  rw [← t1, cp i hi', t0]

/-- `out` zeroed. -/
theorem zeroOut_vp {F : State → State → Prop} {c : Cfg} {n : Nat}
    (hF : ∀ σ s, F σ s → SS G STK0 σ c s) (hn : n = G.outLen) (hn0 : 0 < G.outLen) (hn2 : G.outLen < 2048)
    (W : List (Nat × BitVec 64)) (hW : ∀ p ∈ W, p.1 ∈ c.LS ∧ c.V p.1 = p.2) (hWok : WOk W) :
    VP F (.seq (.block [ld .a0 fOut, .li .a1 n]) (Impl.Rsa.RISCV64.Keys.zeroBytes .a0 .a1))
      (FS G W (List.replicate G.outLen 0)) := by
  subst hn
  let M : State → State → Prop := fun σ t => SS G STK0 σ c t ∧
    t.gpr .a0 = G.out ∧ t.gpr .a1 = BitVec.ofNat 64 G.outLen
  refine VP.seq (G := M) (VP.pub (SS.pub hF) []
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block [ld .a0 fOut, .li .a1 G.outLen]),
      by kernel_rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s hs => (hF σ s hs).ldK (o := fOut) (by decide) (by decide)
      ((hF σ s hs).gi.fixedV (o := fOut) (v := G.out) (by simp [fixedWords])) (t := .a0) (by decide) fun s₁ h₁ u₁ =>
      wp_li hn2 fun t u => WP.block_nil ⟨h₁.of_upd u (by decide), by rw [u.other _ (by decide), u₁.gpr], u.gpr⟩) ?_
  refine VP.pub (G := G) (fun σ t h => ⟨h.1.gi.s6, by rw [h.1.gi.sp, ← h.1.gi.hG]; rfl⟩) [.a0, .a1]
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .a0, .a1])
      (Impl.Rsa.RISCV64.Keys.zeroBytes .a0 .a1), by kernel_rfl⟩
    (fun σ₁ σ₂ s₁ s₂ ⟨_, a0, a1⟩ ⟨_, b0, b1⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a0, b0]
      · rw [a1, b1]) fun σ t ⟨h, t0, t1⟩ => ?_
  have gi := h.gi
  obtain ⟨dOU, dOC, dOT, dUC, dUT, dCT, dBT, nO, nU, nT, aU, aT⟩ := gi.pre.disj gi.hG
  refine WP.sp_eq (WP.mono (VG.Proof.Rsa.RISCV64.Keys.zeroBytes_ok t0 t1 (by decide) (by omega) (by omega)
    (fun i hi => ⟨G.rOut, by rw [gi.wr, gi.pre.wr, gi.hG]; simp, Offset.contains_base _ (by omega) (by omega)⟩) nO)
    fun u ⟨hz, ho, kp⟩ spu => ?_)
  have f : Frame [G.rOut] t.mem u.mem := fun x hx => ho x (Or.inr (by
    have := hx _ (List.mem_singleton_self _)
    simp only [Region.Contains] at this
    change 0 + G.outLen ≤ (x - G.out).toNat
    omega))
  refine FS.of_SS h W hW hWok kp (by decide) spu f ?_
  simp only [Spec.Rsa.bytesAt]
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
  exact hz i (by simpa using h₁)

end

/-! ## Blocks on the stage, and `ranOut`'s arithmetic -/

theorem shl_ofNat (P k : Nat) : BitVec.ofNat 64 P <<< k = BitVec.ofNat 64 (P * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mul_mod]

theorem sub_ofNat {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show a - b < 2 ^ 64 by omega)]
  omega

section
variable {G : GP} {W : List (Nat × BitVec 64)} {ob : List Byte} {σ s : State}

theorem FS.pLen (h : FS G W ob σ s) : 0 < G.pLen ∧ G.pLen ≤ 384 := by
  have := h.pre.lens; rw [h.hG] at this
  simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_true, beq_iff_eq] at this
  omega

/-- A block analysed with `s6` alone public. -/
theorem FS.blk {F Q : State → State → Prop} {is : List Instr} (hF : ∀ σ s, F σ s → FS G W ob σ s)
    (cert : (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s6]) (.block is)
      (VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block is))).isSome = true)
    (h : ∀ σ s, F σ s → WP isa (.block is) s (Q σ)) : VP F (.block is) Q :=
  VP.pub (G := G) (fun σ s hs => (hF σ s hs).pub) [] ⟨_, cert⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) h

/-- `cmpF` on the stage: the word `o` of `W` against `v`. -/
theorem FS.cmpF_vp {P Q : State → State → Prop} (hF : ∀ σ s, P σ s → FS G W ob σ s) {o v : Nat}
    {x : BitVec 64} (ho : (o, x) ∈ W) (hv : v ≤ 2048)
    (k : ∀ σ t, FS G W ob σ t → isa.eval (.zero .t2) t = some (x == BitVec.ofNat 64 v) → Q σ t) :
    VP P (.block (cmpF o v)) Q :=
  FS.blk hF (by kernel_rfl) fun σ s hs => by
    have h := hF σ s hs
    refine h.ldK (h.wok _ ho).1 (h.wok _ ho).2 (h.words _ ho) (r := .t2) (by decide) fun s₁ h₁ u₁ => ?_
    refine wp_subi hv fun t u => WP.block_nil ?_
    refine k σ t (h₁.of_upd u (by decide)) ?_
    rw [eval_zero, u.gpr, u₁.gpr, sub_beq_zero]

/-- The stage with `t3`, `t4` and `t5` known. -/
abbrev R3 (G : GP) (W : List (Nat × BitVec 64)) (ob : List Byte) (x3 x4 x5 : Nat) (σ s : State) : Prop :=
  FS G W ob σ s ∧ s.gpr .t3 = BitVec.ofNat 64 x3 ∧ s.gpr .t4 = BitVec.ofNat 64 x4 ∧
    s.gpr .t5 = BitVec.ofNat 64 x5

theorem ltu_of {a b : Reg} {xa xb : Nat} {s : State}
    (ha : s.gpr a = BitVec.ofNat 64 xa) (hb : s.gpr b = BitVec.ofNat 64 xb) (hxa : xa < 2 ^ 64)
    (hxb : xb < 2 ^ 64) : isa.eval (.ltu a b) s = some (decide (xa < xb)) := by
  rw [eval_ltu, ha, hb]; exact congrArg some (decide_eq_decide.mpr (ofNat_lt_iff hxa hxb))

/-- `ranOut`'s first block: the octets from the seed's start and the budget. -/
theorem ro1_vp {F : State → State → Prop} {c : Nat} (hc : (fStart, BitVec.ofNat 64 c) ∈ W)
    (hcl : c ≤ G.randLen) (hF : ∀ σ s, F σ s → FS G W ob σ s) :
    VP F (.block (([ld .t4 fWitLen, ld .t3 fStart, .sub .t4 .t4 .t3] : List Instr) ++
        ([.li .t5 G.pLen, .shift .sll .d .t5 .t5 15, .addi .t5 .t5 G.pLen] : List Instr)))
      (R3 G W ob c (G.randLen - c) (Spec.Dsa.parameterEntropy G.pLen)) :=
  FS.blk hF (by kernel_rfl) fun σ s hs => by
    have h := hF σ s hs
    have hp := h.pLen
    have hr : G.randLen < 2 ^ 64 := by rw [← h.hG]; exact BitVec.isLt _
    simp only [List.cons_append, List.nil_append]
    refine h.ldK (o := fWitLen) (by decide) (by decide) (h.fixed (fWitLen, BitVec.ofNat 64 G.randLen)
      (by simp [fixedWords])) (r := .t4) (by decide) fun s₁ h₁ u₁ => ?_
    refine h₁.ldK (h₁.wok _ hc).1 (h₁.wok _ hc).2 (h₁.words _ hc) (r := .t3) (by decide) fun s₂ h₂ u₂ => ?_
    refine wp_sub fun s₃ u₃ => wp_li (show G.pLen < 2048 by omega) fun s₄ u₄ =>
      wp_sll (by decide) fun s₅ u₅ => wp_addi (show G.pLen < 2048 by omega) fun t u => WP.block_nil ?_
    refine ⟨((((h₂.of_upd u₃ (by decide)).of_upd u₄ (by decide)).of_upd u₅ (by decide)).of_upd u (by decide)),
      by rw [u.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr],
      ?_, ?_⟩
    · rw [u.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
        u₁.gpr, u₂.gpr, sub_ofNat hcl hr]
    · rw [u.gpr, u₅.gpr, u₄.gpr, shl_ofNat, ← BitVec.ofNat_add, Spec.Dsa.parameterEntropy,
        show G.pLen * 2 ^ 15 + G.pLen = 32769 * G.pLen by omega]

/-- `t3 := 256 pLen`. -/
theorem t3_vp {x3 x4 x5 : Nat} :
    VP (R3 G W ob x3 x4 x5) (.block [.li .t3 G.pLen, .shift .sll .d .t3 .t3 8]) (R3 G W ob (256 * G.pLen) x4 x5) :=
  FS.blk (fun _ _ h => h.1) (by kernel_rfl) fun σ s ⟨h, _, a4, a5⟩ => by
    have hp := h.pLen
    refine wp_li (show G.pLen < 2048 by omega) fun s₁ u₁ => wp_sll (by decide) fun t u => WP.block_nil ?_
    refine ⟨(h.of_upd u₁ (by decide)).of_upd u (by decide), ?_, by rw [u.other _ (by decide), u₁.other _ (by decide), a4],
      by rw [u.other _ (by decide), u₁.other _ (by decide), a5]⟩
    rw [u.gpr, u₁.gpr, shl_ofNat, show G.pLen * 2 ^ 8 = 256 * G.pLen by omega]

/-- `t4 := max t4 t3`. -/
theorem max_vp {x3 x4 x5 : Nat} (h3 : x3 < 2 ^ 64) (h4 : x4 < 2 ^ 64) :
    VP (R3 G W ob x3 x4 x5) (.ite (.ltu .t4 .t3) (.block [.addi .t4 .t3 0]) (.block []))
      (R3 G W ob x3 (max x4 x3) x5) := by
  refine VP.ite (fun _ _ s₁ s₂ h₁ h₂ => by rw [ltu_of h₁.2.2.1 h₁.2.1 h4 h3, ltu_of h₂.2.2.1 h₂.2.1 h4 h3]) ?_ ?_
  · refine FS.blk (fun _ _ h => h.1.1) (by kernel_rfl) fun σ s ⟨hs, e⟩ => ?_
    obtain ⟨h, a3, a4, a5⟩ := hs
    rw [ltu_of a4 a3 h4 h3] at e
    have hl : x4 < x3 := of_decide_eq_true (Option.some.inj e)
    refine wp_addi (imm := 0) (by decide) fun t u => WP.block_nil ⟨h.of_upd u (by decide),
      by rw [u.other _ (by decide), a3], ?_, by rw [u.other _ (by decide), a5]⟩
    rw [u.gpr, a3, BitVec.add_zero, Nat.max_eq_right (Nat.le_of_lt hl)]
  · refine VP.block_nil fun σ s ⟨hs, e⟩ => ?_
    obtain ⟨h, a3, a4, a5⟩ := hs
    rw [ltu_of a4 a3 h4 h3] at e
    have hl : ¬ x4 < x3 := of_decide_eq_false (Option.some.inj e)
    exact ⟨h, a3, by rw [a4, Nat.max_eq_left (by omega)], a5⟩

/-- `t5 := min t4 t5`. -/
theorem min_vp {x3 x4 x5 : Nat} (h4 : x4 < 2 ^ 64) (h5 : x5 < 2 ^ 64) :
    VP (R3 G W ob x3 x4 x5) (.ite (.ltu .t4 .t5) (.block [.addi .t5 .t4 0]) (.block []))
      (R3 G W ob x3 x4 (min x4 x5)) := by
  refine VP.ite (fun _ _ s₁ s₂ h₁ h₂ => by rw [ltu_of h₁.2.2.1 h₁.2.2.2 h4 h5, ltu_of h₂.2.2.1 h₂.2.2.2 h4 h5]) ?_ ?_
  · refine FS.blk (fun _ _ h => h.1.1) (by kernel_rfl) fun σ s ⟨hs, e⟩ => ?_
    obtain ⟨h, a3, a4, a5⟩ := hs
    rw [ltu_of a4 a5 h4 h5] at e
    have hl : x4 < x5 := of_decide_eq_true (Option.some.inj e)
    refine wp_addi (imm := 0) (by decide) fun t u => WP.block_nil ⟨h.of_upd u (by decide),
      by rw [u.other _ (by decide), a3], by rw [u.other _ (by decide), a4], ?_⟩
    rw [u.gpr, a4, BitVec.add_zero, Nat.min_eq_left (Nat.le_of_lt hl)]
  · refine VP.block_nil fun σ s ⟨hs, e⟩ => ?_
    obtain ⟨h, a3, a4, a5⟩ := hs
    rw [ltu_of a4 a5 h4 h5] at e
    have hl : ¬ x4 < x5 := of_decide_eq_false (Option.some.inj e)
    exact ⟨h, a3, a4, by rw [a5, Nat.min_eq_right (by omega)]⟩

/-- `t4 := 2 t4`. -/
theorem dbl_vp {x3 x4 x5 : Nat} :
    VP (R3 G W ob x3 x4 x5) (.block [.add .t4 .t4 .t4]) (R3 G W ob x3 (2 * x4) x5) :=
  FS.blk (fun _ _ h => h.1) (by kernel_rfl) fun σ s ⟨h, a3, a4, a5⟩ =>
    wp_add fun t u => WP.block_nil ⟨h.of_upd u (by decide), by rw [u.other _ (by decide), a3],
      by rw [u.gpr, a4, ← BitVec.ofNat_add, Nat.two_mul], by rw [u.other _ (by decide), a5]⟩

/-- `t4 :=` the word `fLeft`. -/
theorem left_vp {x3 x4 x5 k : Nat} (hk : (fLeft, BitVec.ofNat 64 k) ∈ W) :
    VP (R3 G W ob x3 x4 x5) (.block [ld .t4 fLeft])
      (fun σ t => FS G W ob σ t ∧ t.gpr .t4 = BitVec.ofNat 64 k ∧ t.gpr .t5 = BitVec.ofNat 64 x5) :=
  FS.blk (fun _ _ h => h.1) (by kernel_rfl) fun σ s ⟨h, _, _, a5⟩ =>
    h.ldK (h.wok _ hk).1 (h.wok _ hk).2 (h.words _ hk) (r := .t4) (by decide) fun t ht u =>
      WP.block_nil ⟨ht, u.gpr, by rw [u.other _ (by decide), a5]⟩

end

/-! ## `ranOut`, and the whole of `finish` -/

/-- `Done` with a result's words. -/
abbrev DoneR (G : GP) (ob : List Byte) (R : Spec.Dsa.ParameterSearchResult) : State → State → Prop :=
  Done G ob R.status (BitVec.ofNat 64 R.used) (BitVec.ofNat 64 R.remaining) (BitVec.ofNat 64 R.requested)

theorem fin_of {G : GP} {σ t : State} {ob : List Byte} {R : Spec.Dsa.ParameterSearchResult} (h : DoneR G ob R σ t)
    (hR : resG G = R) (hob : ob = outB G) : Fin G σ t := by
  subst hR hob; exact fin_of_done h

section
variable {G : GP} {W : List (Nat × BitVec 64)} {ob : List Byte}

/-- A seed that ran out, at the seed's start `c` with `k` seeds left. -/
theorem ranOut_vp (g : Geo) (hgp : g.pLen = G.pLen) {F : State → State → Prop} {c k : Nat}
    (hc : (fStart, BitVec.ofNat 64 c) ∈ W) (hk : (fLeft, BitVec.ofNat 64 k) ∈ W) (hcl : c ≤ G.randLen)
    (hF : ∀ σ s, F σ s → FS G W ob σ s) :
    VP F g.ranOut (DoneR G ob (VG.Proof.Dsa.Generation.ranOutResult G.pLen k (G.randLen - c) c)) := by
  by_cases hp : 0 < G.pLen ∧ G.pLen ≤ 384
  swap; · exact VP.of_false fun σ s h => hp (hF σ s h).pLen
  by_cases hb : G.randLen ≤ Spec.Dsa.parameterEntropy G.pLen
  swap; · exact VP.of_false fun σ s h => hb (by have := (hF σ s h).pre.randLen; rw [(hF σ s h).hG] at this; exact this)
  have hB : Spec.Dsa.parameterEntropy G.pLen < 2 ^ 64 := by simp only [Spec.Dsa.parameterEntropy]; omega
  have hA : G.randLen - c < 2 ^ 64 := by omega
  have hBv : Spec.Dsa.parameterEntropy G.pLen = 32769 * G.pLen := rfl
  simp only [Geo.ranOut, Geo.budget, hgp]
  refine VP.seq (ro1_vp hc hcl hF) (VP.ite (fun _ _ _ _ h₁ h₂ => by
    rw [ltu_of h₁.2.2.1 h₁.2.2.2 hA hB, ltu_of h₂.2.2.1 h₂.2.2.2 hA hB]) ?_ ?_)
  · by_cases hAB : G.randLen - c < Spec.Dsa.parameterEntropy G.pLen
    swap; · exact VP.of_false fun σ s ⟨h, e⟩ => hAB (of_decide_eq_true (Option.some.inj
        ((ltu_of h.2.2.1 h.2.2.2 hA hB).symm.trans e)))
    simp only [Impl.Rsa.RISCV64.Keys.seqs]
    refine VP.seq (t3_vp.mono (fun _ _ h => h.1) fun _ _ h => h) (VP.seq (max_vp (by omega) hA)
      (VP.seq dbl_vp (VP.seq (min_vp (by omega) hB) (VP.seq (left_vp hk)
      ((tail_vp (r := 0) (by decide) hc fun _ _ h => h).mono (fun _ _ h => h) fun σ t h => ?_)))))
    have e : VG.Proof.Dsa.Generation.ranOutResult G.pLen k (G.randLen - c) c =
        ⟨.entropy k (min (2 * max (G.randLen - c) (256 * G.pLen)) (Spec.Dsa.parameterEntropy G.pLen)), c, []⟩ := by
      simp only [VG.Proof.Dsa.Generation.ranOutResult, Spec.Dsa.parameterRequest, Spec.Entropy.request,
        Nat.not_le.mpr hAB, ↓reduceIte]
    rw [DoneR, e]; exact h
  · by_cases hAB : G.randLen - c < Spec.Dsa.parameterEntropy G.pLen
    · exact VP.of_false fun σ s ⟨h, e⟩ => by
        have := (ltu_of h.2.2.1 h.2.2.2 hA hB).symm.trans e
        simp only [Option.some.injEq, decide_eq_false_iff_not] at this; exact this hAB
    simp only [Geo.exhausted, Impl.Rsa.RISCV64.Keys.seqs]
    refine VP.seq (zero45_vp fun _ _ h => h.1.1) ((tail_vp (r := 3) (by decide) hc fun _ _ h => h).mono
      (fun _ _ h => h) fun σ t h => ?_)
    have e : VG.Proof.Dsa.Generation.ranOutResult G.pLen k (G.randLen - c) c = ⟨.exhausted, c, []⟩ := by
      simp only [VG.Proof.Dsa.Generation.ranOutResult, Nat.not_lt.mp hAB, ↓reduceIte]
    rw [DoneR, e]; exact h

end

theorem ev_ne {s : State} {c : Cond} {a b : Bool} (h₁ : isa.eval c s = some a) (h₂ : isa.eval c s = some b)
    (h : a ≠ b) : False := h (Option.some.inj (h₁.symm.trans h₂))

/-- From the end of the controller's last iteration, `finish`. -/
theorem finish_vp {G : GP} (g : Geo) (hgp : g.pLen = G.pLen) (hgq : g.qLen = G.qLen) {cl0 : Claims}
    {X : State → Prop} (hst : stAt G.pLen G.randB (lastPos G) ≠ 2) :
    VP (St G (midCfg G cl0 (lastPos G)) X) g.finish (Fin G) := by
  by_cases hp : 0 < G.pLen ∧ G.pLen ≤ 384
  swap; · exact VP.of_false fun σ s h => hp (by
      have := h.1.gi.pre.lens; rw [h.1.gi.hG] at this
      simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_true, beq_iff_eq] at this; omega)
  by_cases hRL : G.randB.length = G.randLen
  swap; · exact VP.of_false fun σ s h => hRL (by rw [← h.1.gi.hG]; simp [mkG, Spec.Rsa.bytesAt])
  by_cases hOL : G.outLen = 2 * G.pLen + G.qLen
  swap; · exact VP.of_false fun σ s h => hOL (by have := h.1.gi.pre.outLen; rw [h.1.gi.hG] at this; exact this)
  have hq : G.qLen ≤ 32 := by simp only [GP.qLen, Spec.Dsa.generationQLen]; split <;> omega
  have hres : resAt G.pLen G.randB (lastPos G) = resG G := VG.Proof.Dsa.Generation.res_pos hp.1 _ _ _
  have hcl : (lastPos G).2 ≤ G.randLen := hRL ▸ VG.Proof.Dsa.Generation.pos_le _ _ _ _
  have hle := VG.Proof.Dsa.Generation.stAt_le G.pLen G.randB (lastPos G)
  obtain ⟨u, extra, hmid, h1, h3, h0⟩ := mid_end (cl0 := cl0) (lastPos G) hst hRL hp.1
  rw [hmid]
  generalize stAt G.pLen G.randB (lastPos G) = st at hst h1 h3 h0 hle ⊢
  simp only [Geo.finish, Impl.Rsa.RISCV64.Keys.seqs, hgp, hgq]
  have hx : ∀ σ s, St G ((endCfg cl0 st (lastPos G).1 (lastPos G).2 u extra).setV fStatus
      (BitVec.ofNat 64 st)) X σ s → fw s.mem G fStatus = BitVec.ofNat 64 st := fun σ s h =>
    (h.1.gi.slotV List.mem_cons_self).trans
      (upd_self (endCfg cl0 st (lastPos G).1 (lastPos G).2 u extra).V fStatus _)
  refine VP.seq (cmpF_vp (fun σ s h => h.1) (by decide) (by decide) (v := 1) (by decide) hx
    (Q := fun σ t => St G ((endCfg cl0 st (lastPos G).1 (lastPos G).2 u extra).setV fStatus
      (BitVec.ofNat 64 st)) X σ t ∧ isa.eval (.zero .t2) t = some (BitVec.ofNat 64 st == BitVec.ofNat 64 1))
    fun σ s t hs ht _ e => ⟨⟨ht, hs.2⟩, e⟩) (VP.ite (fun _ _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_)
  · -- status 1: the parameters
    by_cases h1' : st = 1
    swap; · exact VP.of_false fun σ s ⟨⟨_, e₁⟩, e₂⟩ => ev_ne e₁ e₂ (by
        rw [ofNat_beq (by omega) (by decide)]; simpa using h1')
    subst h1'
    obtain ⟨a, rfl, hr⟩ := h1 rfl
    have hR : resG G = ⟨.accepted a, u, []⟩ := hres ▸ hr
    have hbl := VG.Proof.Dsa.Generation.encodeParams_length G.pLen G.qLen a
    refine VP.seq (copyOut_vp (fun σ s h => h.1.1.1) (by simp [endCfg]) hbl hOL.symm (by omega) (by omega)
      [(fUsed, BitVec.ofNat 64 u)] (fun p hp => by
        simp only [List.mem_singleton] at hp; subst hp
        simp [endCfg, upd, fStatus, fLeft, fStart, fUsed]) (by simp [WOk, fUsed, hEnd, fSave]))
      (VP.seq (zero45_vp fun _ _ h => h) ((tail_vp (r := 1) (by decide) List.mem_cons_self fun _ _ h => h).mono
        (fun _ _ h => h) fun σ t h => fin_of (R := ⟨.accepted a, u, []⟩) h hR (by simp [outB, hR])))
  · -- otherwise `out` zeroed
    by_cases h1' : st = 1
    · subst h1'; exact VP.of_false fun σ s ⟨⟨_, e₁⟩, e₂⟩ => ev_ne e₁ e₂ (by decide)
    have hW : ∀ p ∈ [(fStatus, BitVec.ofNat 64 st), (fLeft, BitVec.ofNat 64 (lastPos G).1),
        (fStart, BitVec.ofNat 64 (lastPos G).2)],
        p.1 ∈ ((endCfg cl0 st (lastPos G).1 (lastPos G).2 u extra).setV fStatus (BitVec.ofNat 64 st)).LS ∧
        ((endCfg cl0 st (lastPos G).1 (lastPos G).2 u extra).setV fStatus (BitVec.ofNat 64 st)).V p.1 = p.2 := by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp [endCfg, upd, fStatus, fLeft, fStart, fUsed, h1', hst]
    refine VP.assoc (VP.seq (zeroOut_vp (fun σ s h => h.1.1.1) hOL.symm (by omega) (by omega) _ hW
      (by simp [WOk, fStatus, fLeft, fStart, hEnd, fSave])) (VP.seq (FS.cmpF_vp (fun _ _ h => h) List.mem_cons_self
      (v := 3) (by decide) (Q := fun σ t => FS G _ _ σ t ∧
        isa.eval (.zero .t2) t = some (BitVec.ofNat 64 st == BitVec.ofNat 64 3)) fun σ t ht e => ⟨ht, e⟩)
      (VP.ite (fun _ _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_)))
    · -- status 3: exhausted
      by_cases h3' : st = 3
      swap; · exact VP.of_false fun σ s ⟨⟨_, e₁⟩, e₂⟩ => ev_ne e₁ e₂ (by
          rw [ofNat_beq (by omega) (by decide)]; simpa using h3')
      subst h3'
      have hR : resG G = ⟨.exhausted, (lastPos G).2, []⟩ := hres ▸ h3 rfl
      simp only [Geo.exhausted, Impl.Rsa.RISCV64.Keys.seqs]
      refine VP.seq (zero45_vp fun _ _ h => h.1.1) ((tail_vp (r := 3) (by decide) (by simp) fun _ _ h => h).mono
        (fun _ _ h => h) fun σ t h => fin_of (R := ⟨.exhausted, (lastPos G).2, []⟩) h hR (by simp [outB, hR]))
    · -- status 0: the tape ran out
      by_cases h3' : st = 3
      · subst h3'; exact VP.of_false fun σ s ⟨⟨_, e₁⟩, e₂⟩ => ev_ne e₁ e₂ (by decide)
      have h0' : st = 0 := by omega
      subst h0'
      have hR := hres ▸ h0 rfl
      refine (ranOut_vp g hgp (by simp) (by simp) hcl fun _ _ h => h.1.1).mono (fun _ _ h => h) fun σ t h =>
        fin_of h hR ?_
      by_cases hE : Spec.Dsa.parameterEntropy G.pLen ≤ G.randLen - (lastPos G).2 <;>
        simp [outB, hR, VG.Proof.Dsa.Generation.ranOutResult, hE]

end VG.Proof.Dsa.RISCV64.PSearch
