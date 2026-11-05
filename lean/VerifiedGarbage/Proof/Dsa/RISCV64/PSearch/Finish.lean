module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Ctl
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Entry
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyBytes
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl

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

end VG.Proof.Dsa.RISCV64.PSearch
