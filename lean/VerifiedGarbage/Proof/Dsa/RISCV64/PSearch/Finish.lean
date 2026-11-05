module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Ctl
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

end VG.Proof.Dsa.RISCV64.PSearch
