import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Init
import VerifiedGarbage.Proof.Sha512.AArch64.ScalarBackend
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Spec.Sha512.Contract
import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Setup
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Wipe
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Entry

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Layout`. -/
section

/-! Shared frame and call invariants for complete AArch64 Ed25519. -/
namespace VG.Proof.Ed25519.AArch64.Whole
open VG VG.AArch64

def Within (r R : Region) : Prop :=
  ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem Within.sub {r R : Region} (h : VG.Proof.Ed25519.AArch64.Whole.Within r R) : Region.Sub r R := by
  obtain ⟨off, hb, hl⟩ := h
  obtain ⟨b, n⟩ := r
  simp only at hb hl
  subst hb
  exact Offset.sub_base _ hl

abbrev FR (E : Addr) : Region := ⟨E, 256⟩
abbrev ARGS (E : Addr) : Region := ⟨E + 256, 48⟩
/-- The 16 bytes below the locals: the frame of a callee saving `x30`. -/
abbrev CK (E : Addr) : Region := below E 16

/-- The baseline memory is the state after the incoming arguments have been
saved. The body cannot write those saved arguments; its callees' frames are
below the locals. -/
structure Ctx (E : Addr) (g : Reg → BitVec 64) (v : VReg → BitVec 128)
    (m₀ : Mem) (R W : List Region) (t : State) : Prop where
  rd : t.rd = R
  wr : t.wr = VG.Proof.Ed25519.AArch64.Whole.FR E :: W
  sp : t.sp = E
  cs : ∀ r ∈ preserved, r ≠ .x30 → t.gpr r = g r
  vs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (v r).extractLsb' 0 64
  frame : Frame (W ++ [VG.Proof.Ed25519.AArch64.Whole.FR E, VG.Proof.Ed25519.AArch64.Whole.CK E]) m₀ t.mem

namespace Ctx
variable {E : Addr} {g : Reg → BitVec 64} {v : VReg → BitVec 128}
  {m₀ : Mem} {rd wr : List Region} {t u : State}

theorem of_frame (h : VG.Proof.Ed25519.AArch64.Whole.Ctx E g v m₀ rd wr t)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hsp : u.sp = t.sp)
    (hcs : ∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r)
    (hvs : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64)
    {ws : List Region} (hf : Frame ws t.mem u.mem)
    (hw : ∀ r ∈ ws, Region.Sub r (VG.Proof.Ed25519.AArch64.Whole.FR E) ∨ ∃ R ∈ wr, Region.Sub r R) :
    VG.Proof.Ed25519.AArch64.Whole.Ctx E g v m₀ rd wr u := by
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp,
    fun r hr hn => (hcs r hr hn).trans (h.cs r hr hn),
    fun r hr => (hvs r hr).trans (h.vs r hr), h.frame.trans ?_⟩
  refine Frame.sub hf fun r hr => ?_
  rcases hw r hr with hf | ⟨R, hR, hs⟩
  · exact ⟨VG.Proof.Ed25519.AArch64.Whole.FR E, List.mem_append_right _ List.mem_cons_self, hf⟩
  · exact ⟨R, List.mem_append_left _ hR, hs⟩

/-- `of_frame`, for a callee that may also have changed its frame. -/
theorem of_frameCK (h : VG.Proof.Ed25519.AArch64.Whole.Ctx E g v m₀ rd wr t)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hsp : u.sp = t.sp)
    (hcs : ∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r)
    (hvs : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64)
    {ws : List Region} (hf : Frame (ws ++ [VG.Proof.Ed25519.AArch64.Whole.CK E]) t.mem u.mem)
    (hw : ∀ r ∈ ws, Region.Sub r (VG.Proof.Ed25519.AArch64.Whole.FR E) ∨ ∃ R ∈ wr, Region.Sub r R) :
    VG.Proof.Ed25519.AArch64.Whole.Ctx E g v m₀ rd wr u := by
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp,
    fun r hr hn => (hcs r hr hn).trans (h.cs r hr hn),
    fun r hr => (hvs r hr).trans (h.vs r hr), h.frame.trans ?_⟩
  refine Frame.sub hf fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rcases hw r hr with hf | ⟨R, hR, hs⟩
    · exact ⟨VG.Proof.Ed25519.AArch64.Whole.FR E, List.mem_append_right _ List.mem_cons_self, hf⟩
    · exact ⟨R, List.mem_append_left _ hR, hs⟩
  · rw [List.mem_singleton.mp hr]
    exact ⟨VG.Proof.Ed25519.AArch64.Whole.CK E, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩

theorem regs (h : VG.Proof.Ed25519.AArch64.Whole.Ctx E g v m₀ rd wr t)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hsp : u.sp = t.sp)
    (hcs : ∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r)
    (hvs : u.v = t.v) (hm : u.mem = t.mem) : VG.Proof.Ed25519.AArch64.Whole.Ctx E g v m₀ rd wr u := by
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp,
    fun r hr hn => (hcs r hr hn).trans (h.cs r hr hn), ?_, hm ▸ h.frame⟩
  intro r hr
  rw [hvs]
  exact h.vs r hr

theorem readable_frame (h : VG.Proof.Ed25519.AArch64.Whole.Ctx E g v m₀ rd wr t) {a : Addr} {n : Nat}
    (hc : (VG.Proof.Ed25519.AArch64.Whole.FR E).Contains a n) : InRegions (t.rd ++ t.wr) a n := by
  rw [h.rd, h.wr]
  exact ⟨VG.Proof.Ed25519.AArch64.Whole.FR E, List.mem_append_right _ List.mem_cons_self, hc⟩

theorem writable_frame (h : VG.Proof.Ed25519.AArch64.Whole.Ctx E g v m₀ rd wr t) {a : Addr} {n : Nat}
    (hc : (VG.Proof.Ed25519.AArch64.Whole.FR E).Contains a n) : InRegions t.wr a n := by
  rw [h.wr]
  exact ⟨VG.Proof.Ed25519.AArch64.Whole.FR E, List.mem_cons_self, hc⟩
end Ctx

theorem call_ok {E : Addr} {g : Reg → BitVec 64} {v : VReg → BitVec 128}
    {m₀ : Mem} {rd wr : List Region} {t : State} (h : VG.Proof.Ed25519.AArch64.Whole.Ctx E g v m₀ rd wr t)
    {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ trace s', Exec isa c s trace s' ∧ abiPreserved s s' ∧ k.post s s')
    (hn : c.noFrames = true)
    {rd' wr' : List Region} (hpre : k.pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ VG.Proof.Ed25519.AArch64.Whole.FR E :: wr))
    (hw : ∀ r ∈ wr', VG.Proof.Ed25519.AArch64.Whole.Within r (VG.Proof.Ed25519.AArch64.Whole.FR E) ∨ ∃ R ∈ wr, VG.Proof.Ed25519.AArch64.Whole.Within r R)
    {Q : State → Prop}
    (hQ : ∀ u, VG.Proof.Ed25519.AArch64.Whole.Ctx E g v m₀ rd wr u → Frame wr' t.mem u.mem →
      k.post (t.callEntry.withRegions rd' wr') (u.withRegions rd' wr') → Q u) :
    WP isa (.call name c) t Q := by
  have hcw : Covers wr' t.wr := by
    refine Covers.of_sub fun r hr => ?_
    rw [h.wr]
    rcases hw r hr with hf | ⟨R, hR, hs⟩
    · exact ⟨VG.Proof.Ed25519.AArch64.Whole.FR E, List.mem_cons_self, hf⟩
    · exact ⟨R, List.mem_cons_of_mem _ hR, hs⟩
  have hcr : Covers (rd' ++ wr') (t.rd ++ t.wr) := by rw [h.rd, h.wr]; exact hcov
  refine WP.callV hv hpre hcr hcw (fun u hrd hwr hsp hf hcs _ hvs hp => ?_) hn
  refine hQ u (h.of_frame hrd hwr hsp hcs hvs hf ?_) hf hp
  intro r hr
  rcases hw r hr with hf | ⟨R, hR, hs⟩
  · exact .inl hf.sub
  · exact .inr ⟨R, hR, hs.sub⟩

/-- The callee's frame is below the locals. -/
theorem ck_frame {E : Addr} {d n : Nat} (h : d + n ≤ 304) : (VG.Proof.Ed25519.AArch64.Whole.CK E).Disjoint ⟨E + BitVec.ofNat 64 d, n⟩ :=
  (Offset.below_disjoint E (m := 16) (l := 304) (by decide)).sub_right (Offset.sub_base _ h)

/-- Code without frames uses no stack. -/
theorem depth_zero_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth = 0 := by
  induction c with
  | block _ => rfl
  | seq a b iha ihb =>
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [Code.aarch64Depth, iha h.1, ihb h.2, Nat.max_self]
  | ite _ t e iht ihe =>
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [Code.aarch64Depth, iht h.1, ihe h.2, Nat.max_self]
  | loop b _ ih => exact ih h
  | call _ b ih => exact ih h
  | frame _ _ _ => simp [Code.noFrames] at h

theorem depth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth ≤ 1 := by
  rw [VG.Proof.Ed25519.AArch64.Whole.depth_zero_of_noFrames h]; decide

/-- `call_ok` for a callee with at most one frame (below the locals, `CK E`). -/
theorem call_okF {E : Addr} {g : Reg → BitVec 64} {v : VReg → BitVec 128}
    {m₀ : Mem} {rd wr : List Region} {t : State} (h : VG.Proof.Ed25519.AArch64.Whole.Ctx E g v m₀ rd wr t)
    {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ trace s', Exec isa c s trace s' ∧ abiPreserved s s' ∧ k.post s s')
    (hd : c.aarch64Depth ≤ 1)
    {rd' wr' : List Region} (hpre : k.pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ VG.Proof.Ed25519.AArch64.Whole.FR E :: wr))
    (hw : ∀ r ∈ wr', VG.Proof.Ed25519.AArch64.Whole.Within r (VG.Proof.Ed25519.AArch64.Whole.FR E) ∨ ∃ R ∈ wr, VG.Proof.Ed25519.AArch64.Whole.Within r R)
    {Q : State → Prop}
    (hQ : ∀ u, VG.Proof.Ed25519.AArch64.Whole.Ctx E g v m₀ rd wr u → Frame (wr' ++ [VG.Proof.Ed25519.AArch64.Whole.CK E]) t.mem u.mem →
      k.post (t.callEntry.withRegions rd' wr') (u.withRegions rd' wr') → Q u) :
    WP isa (.call name c) t Q := by
  have hcw : Covers wr' t.wr := by
    refine Covers.of_sub fun r hr => ?_
    rw [h.wr]
    rcases hw r hr with hf | ⟨R, hR, hs⟩
    · exact ⟨VG.Proof.Ed25519.AArch64.Whole.FR E, List.mem_cons_self, hf⟩
    · exact ⟨R, List.mem_cons_of_mem _ hR, hs⟩
  have hcr : Covers (rd' ++ wr') (t.rd ++ t.wr) := by rw [h.rd, h.wr]; exact hcov
  refine WP.callFV hv hpre hcr hcw (fun u hrd hwr hsp hf hcs hvs hp => ?_) (by omega)
  have hf' : Frame (wr' ++ [VG.Proof.Ed25519.AArch64.Whole.CK E]) t.mem u.mem := by
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · rw [List.mem_singleton.mp hr, h.sp]
      exact ⟨VG.Proof.Ed25519.AArch64.Whole.CK E, List.mem_append_right _ (List.mem_singleton_self _), below_sub (by omega) (by decide)⟩
  refine hQ u (h.of_frameCK hrd hwr hsp hcs hvs hf' ?_) hf' hp
  intro r hr
  rcases hw r hr with hf | ⟨R, hR, hs⟩
  · exact .inl hf.sub
  · exact .inr ⟨R, hR, hs.sub⟩

end VG.Proof.Ed25519.AArch64.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.Whole.BlocksCT`. -/
section
/-! Equal traces for straight-line helpers addressed through the public SP. -/
namespace VG.Proof.Ed25519.AArch64.Whole
open VG VG.AArch64

theorem block_rel {P : State → State → Prop} {is : List Instr}
    (he : ∀ a b, P a b → a.sp = b.sp)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (VG.AArch64.Taint.ofRegs []) (.block is) hint).isSome = true) :
    RelCT isa P (.block is) fun _ _ => True :=
  RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs [])
    (fun a b h => ⟨he a b h, fun r hr => by simp at hr⟩) ht

theorem rel_wp {F F' G G' : State → Prop} {c : Prog isa}
    (hct : RelCT isa (fun a b => F a ∧ F' b) c fun _ _ => True)
    (ha : ∀ a, F a → WP isa c a G) (hb : ∀ b, F' b → WP isa c b G') :
    RelCT isa (fun a b => F a ∧ F' b) c fun a b => G a ∧ G' b :=
  (hct.wp fun a b h => ⟨ha a h.1, hb b h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

end VG.Proof.Ed25519.AArch64.Whole
end

namespace VG.Proof.Ed25519.AArch64.Whole
open VG VG.AArch64

structure CallReady (k : Contract isa) (E : BitVec 64) (rd wr : List Region) (t : State) where
  reads : List Region
  writes : List Region
  pre : k.pre (t.callEntry.withRegions reads writes)
  covers : Covers (reads ++ writes) (rd ++ VG.Proof.Ed25519.AArch64.Whole.FR E :: wr)
  writable : ∀ r ∈ writes, VG.Proof.Ed25519.AArch64.Whole.Within r (VG.Proof.Ed25519.AArch64.Whole.FR E) ∨ ∃ R ∈ wr, VG.Proof.Ed25519.AArch64.Whole.Within r R

theorem CallReady.covers_state {k : Contract isa} {E : BitVec 64} {g : Reg → BitVec 64}
    {v : VReg → BitVec 128} {m : Mem} {rd wr : List Region} {t : State} (hc : VG.Proof.Ed25519.AArch64.Whole.Ctx E g v m rd wr t)
    (h : VG.Proof.Ed25519.AArch64.Whole.CallReady k E rd wr t) :
    Covers (h.reads ++ h.writes) (t.rd ++ t.wr) ∧ Covers h.writes t.wr := by
  refine ⟨by rw [hc.rd, hc.wr]; exact h.covers, Covers.of_sub fun r hr => ?_⟩
  rw [hc.wr]
  rcases h.writable r hr with h | ⟨R, hr, h⟩
  · exact ⟨VG.Proof.Ed25519.AArch64.Whole.FR E, List.mem_cons_self, h⟩
  · exact ⟨R, List.mem_cons_of_mem _ hr, h⟩

theorem CallReady.wp {k : Contract isa} {E : BitVec 64} {g : Reg → BitVec 64}
    {v : VReg → BitVec 128} {m : Mem} {rd wr : List Region} {t : State} (hc : VG.Proof.Ed25519.AArch64.Whole.Ctx E g v m rd wr t)
    (h : VG.Proof.Ed25519.AArch64.Whole.CallReady k E rd wr t) {c : Prog isa} {name : String}
    (hv : ∀ s, k.pre s → ∃ trace s', Exec isa c s trace s' ∧ abiPreserved s s' ∧ k.post s s')
    (hn : c.noFrames = true) :
    WP isa (.call name c) t (VG.Proof.Ed25519.AArch64.Whole.Ctx E g v m rd wr) :=
  VG.Proof.Ed25519.AArch64.Whole.call_ok hc hv hn h.pre h.covers h.writable fun _ hc _ _ => hc

theorem CallReady.wpF {k : Contract isa} {E : BitVec 64} {g : Reg → BitVec 64}
    {v : VReg → BitVec 128} {m : Mem} {rd wr : List Region} {t : State} (hc : VG.Proof.Ed25519.AArch64.Whole.Ctx E g v m rd wr t)
    (h : VG.Proof.Ed25519.AArch64.Whole.CallReady k E rd wr t) {c : Prog isa} {name : String}
    (hv : ∀ s, k.pre s → ∃ trace s', Exec isa c s trace s' ∧ abiPreserved s s' ∧ k.post s s')
    (hd : c.aarch64Depth ≤ 1) :
    WP isa (.call name c) t (VG.Proof.Ed25519.AArch64.Whole.Ctx E g v m rd wr) :=
  VG.Proof.Ed25519.AArch64.Whole.call_okF hc hv hd h.pre h.covers h.writable fun _ hc _ _ => hc

/-- Independent permission narrowing in each run leaves call traces unchanged. -/
theorem callEx {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop}
    (hP : ∀ a b, P a b → ∃ ar aw br bw,
      k.pre (a.callEntry.withRegions ar aw) ∧ k.pre (b.callEntry.withRegions br bw) ∧
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw) ∧
      Covers (ar ++ aw) (a.rd ++ a.wr) ∧ Covers aw a.wr ∧
      Covers (br ++ bw) (b.rd ++ b.wr) ∧ Covers bw b.wr) :
    RelCT isa P (.call n c) fun _ _ => True := by
  intro a b ta tb a' b' hp ea eb
  obtain ⟨ar, aw, br, bw, pa, pb, pub, ca, wa, cb, wb⟩ := hP a b hp
  cases ea with
  | call ha xa ra =>
    cases eb with
    | call hb xb rb =>
      rw [call_callEntry, Option.some.injEq] at ha hb
      subst ha hb
      obtain ⟨_, na⟩ := trace_narrow hv pa (by simpa using ca) (by simpa using wa) xa
      obtain ⟨_, nb⟩ := trace_narrow hv pb (by simpa using cb) (by simpa using wb) xb
      have ht := hct _ _ _ _ _ _ pa pb pub na nb
      exact ⟨by simp only [ht], trivial⟩

end VG.Proof.Ed25519.AArch64.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.Whole.HashPre`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.Whole.Hash`. -/
section
/-! SHA-512 calls parameterized by the verified compression backend. -/
namespace VG.Proof.Ed25519.AArch64.Whole
open VG VG.AArch64
open VG.Impl.Sha512.AArch64.Stream (init)

abbrev Backend := Proof.Sha512.AArch64.Compress

theorem update_depth (v : VG.Proof.Ed25519.AArch64.Whole.Backend) : v.update.aarch64Depth ≤ 1 := Nat.le_of_eq v.update_depth

theorem finalize_depth (v : VG.Proof.Ed25519.AArch64.Whole.Backend) : v.finalize.aarch64Depth ≤ 1 := Nat.le_of_eq v.finalize_depth

variable {E : Addr} {g : Reg → BitVec 64} {vec : VReg → BitVec 128}
  {m₀ : Mem} {rd wr : List Region} {t : State}

theorem init_call (hc : VG.Proof.Ed25519.AArch64.Whole.Ctx E g vec m₀ rd wr t)
    {rd' wr' : List Region}
    (hp : (Proof.Sha512.initAArch64 Spec.Sha512.H0_512).pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ VG.Proof.Ed25519.AArch64.Whole.FR E :: wr))
    (hw : ∀ r ∈ wr', VG.Proof.Ed25519.AArch64.Whole.Within r (VG.Proof.Ed25519.AArch64.Whole.FR E) ∨ ∃ R ∈ wr, VG.Proof.Ed25519.AArch64.Whole.Within r R)
    {scr : Addr} (ha : t.gpr .x0 = scr) :
    WP isa (.call Spec.Sha512.init512Api.name (init Spec.Sha512.H0_512)) t fun u =>
      VG.Proof.Ed25519.AArch64.Whole.Ctx E g vec m₀ rd wr u ∧ Frame wr' t.mem u.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem scr [] := by
  refine VG.Proof.Ed25519.AArch64.Whole.call_ok hc (Proof.Sha512.AArch64.Stream.init_verified _).1 rfl hp hcov hw
    fun u hu hf hpost => ⟨hu, hf, ?_⟩
  change Spec.Sha512.Repr _ u.mem (t.callEntry.gpr .x0) [] at hpost
  rw [State.callEntry_gpr _ (by decide), ha] at hpost
  exact hpost

theorem update_call (v : VG.Proof.Ed25519.AArch64.Whole.Backend) (hc : VG.Proof.Ed25519.AArch64.Whole.Ctx E g vec m₀ rd wr t)
    {rd' wr' : List Region}
    (hp : Proof.Sha512.updateAArch64.pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ VG.Proof.Ed25519.AArch64.Whole.FR E :: wr))
    (hw : ∀ r ∈ wr', VG.Proof.Ed25519.AArch64.Whole.Within r (VG.Proof.Ed25519.AArch64.Whole.FR E) ∨ ∃ R ∈ wr, VG.Proof.Ed25519.AArch64.Whole.Within r R)
    {scr p len : Addr} {prev : List Byte}
    (h0 : t.gpr .x0 = scr) (h2 : t.gpr .x2 = p) (h3 : t.gpr .x3 = len)
    (hcount : t.gpr .x1 = BitVec.ofNat 64 prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem scr prev) :
    WP isa (.call (Spec.Sha512.updateScratchApi.name ++ v.suffix) v.update) t fun u =>
      VG.Proof.Ed25519.AArch64.Whole.Ctx E g vec m₀ rd wr u ∧ Frame (wr' ++ [VG.Proof.Ed25519.AArch64.Whole.CK E]) t.mem u.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem scr
        (prev ++ Spec.Ed25519.bytesAt t.mem p len.toNat) := by
  refine VG.Proof.Ed25519.AArch64.Whole.call_okF hc v.update_verified.1 (VG.Proof.Ed25519.AArch64.Whole.update_depth v) hp hcov hw
    fun u hu hf hpost => ⟨hu, hf, ?_⟩
  have h0' : (t.callEntry.withRegions rd' wr').gpr .x0 = scr := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h0]
  have h1' : (t.callEntry.withRegions rd' wr').gpr .x1 = BitVec.ofNat 64 prev.length := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), hcount]
  have hh := hpost Spec.Sha512.H0_512 prev (by rw [h0']; exact hr) h1'
  change Spec.Sha512.Repr _ u.mem (t.callEntry.gpr .x0)
    (prev ++ Spec.Ed25519.bytesAt t.mem (t.callEntry.gpr .x2) (t.callEntry.gpr .x3).toNat) at hh
  rw [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), h0, h2, h3] at hh
  exact hh

theorem finalize_call (v : VG.Proof.Ed25519.AArch64.Whole.Backend) (hc : VG.Proof.Ed25519.AArch64.Whole.Ctx E g vec m₀ rd wr t)
    {rd' wr' : List Region}
    (hp : Proof.Sha512.finalizeAArch64.pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ VG.Proof.Ed25519.AArch64.Whole.FR E :: wr))
    (hw : ∀ r ∈ wr', VG.Proof.Ed25519.AArch64.Whole.Within r (VG.Proof.Ed25519.AArch64.Whole.FR E) ∨ ∃ R ∈ wr, VG.Proof.Ed25519.AArch64.Whole.Within r R)
    {scr out : Addr} {msg : List Byte}
    (h0 : t.gpr .x0 = scr) (h2 : t.gpr .x2 = out)
    (hcount : t.gpr .x1 = BitVec.ofNat 64 msg.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem scr msg) (hlen : msg.length < 2 ^ 64) :
    WP isa (.call (Spec.Sha512.finalizeScratchApi.name ++ v.suffix) v.finalize) t fun u =>
      VG.Proof.Ed25519.AArch64.Whole.Ctx E g vec m₀ rd wr u ∧ Frame (wr' ++ [VG.Proof.Ed25519.AArch64.Whole.CK E]) t.mem u.mem ∧
      Spec.Ed25519.bytesAt u.mem out 64 = Spec.Sha512.finalHash Spec.Sha512.H0_512 msg := by
  refine VG.Proof.Ed25519.AArch64.Whole.call_okF hc v.finalize_verified.1 (VG.Proof.Ed25519.AArch64.Whole.finalize_depth v) hp hcov hw
    fun u hu hf hpost => ⟨hu, hf, ?_⟩
  have h0' : (t.callEntry.withRegions rd' wr').gpr .x0 = scr := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h0]
  have h1' : (t.callEntry.withRegions rd' wr').gpr .x1 = BitVec.ofNat 64 msg.length := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), hcount]
  have hh := hpost Spec.Sha512.H0_512 msg (by rw [h0']; exact hr) hlen h1'
  change Spec.Ed25519.bytesAt u.mem (t.callEntry.gpr .x2) 64 = _ at hh
  rw [State.callEntry_gpr _ (by decide), h2] at hh
  exact hh

end VG.Proof.Ed25519.AArch64.Whole
end

namespace VG.Proof.Ed25519.AArch64.Whole
open VG VG.AArch64

abbrev SHA (scr : Addr) : Region := ⟨scr, 192⟩
abbrev WORK (scr : Addr) : Region := ⟨scr + 192, 688⟩
def initWr (scr : Addr) : List Region := [VG.Proof.Ed25519.AArch64.Whole.SHA scr]
def updateRd (p len : Addr) : List Region := [⟨p, len.toNat⟩]
def hashWr (scr : Addr) : List Region := [VG.Proof.Ed25519.AArch64.Whole.SHA scr, VG.Proof.Ed25519.AArch64.Whole.WORK scr]
def finalizeWr (scr out : Addr) : List Region := [VG.Proof.Ed25519.AArch64.Whole.SHA scr, ⟨out, 64⟩, VG.Proof.Ed25519.AArch64.Whole.WORK scr]

theorem sha_sub (scr : Addr) : Region.Sub (VG.Proof.Ed25519.AArch64.Whole.SHA scr) ⟨scr, 8192⟩ := Region.sub_prefix (by decide)
theorem work_sub (scr : Addr) : Region.Sub (VG.Proof.Ed25519.AArch64.Whole.WORK scr) ⟨scr, 8192⟩ :=
  Offset.sub_base _ (by decide)
theorem sha_work (scr : Addr) : (VG.Proof.Ed25519.AArch64.Whole.SHA scr).Disjoint (VG.Proof.Ed25519.AArch64.Whole.WORK scr) :=
  Offset.base_disjoint _ (by decide) (by decide)

theorem init_pre {t : State} {scr : Addr} (ha : t.gpr .x0 = scr) :
    (Proof.Sha512.initAArch64 Spec.Sha512.H0_512).pre
      (t.callEntry.withRegions [] (VG.Proof.Ed25519.AArch64.Whole.initWr scr)) := by
  simp only [Proof.Sha512.initAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), ha]
  exact ⟨True.intro, rfl⟩

theorem update_pre {t : State} {scr p len : Addr}
    (h0 : t.gpr .x0 = scr) (h2 : t.gpr .x2 = p) (h3 : t.gpr .x3 = len)
    (h4 : t.gpr .x4 = scr + 192)
    (hd : Region.Disjoint ⟨p, len.toNat⟩ ⟨scr, 8192⟩) (hsp : 16 ≤ t.sp.toNat)
    (hks : (VG.Proof.Ed25519.AArch64.Whole.CK t.sp).Disjoint ⟨scr, 8192⟩) (hkp : (VG.Proof.Ed25519.AArch64.Whole.CK t.sp).Disjoint ⟨p, len.toNat⟩) :
    Proof.Sha512.updateAArch64.pre
      (t.callEntry.withRegions (VG.Proof.Ed25519.AArch64.Whole.updateRd p len) (VG.Proof.Ed25519.AArch64.Whole.hashWr scr)) := by
  simp only [Proof.Sha512.updateAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), h0, h2, h3, h4]
  exact ⟨rfl, rfl, VG.Proof.Ed25519.AArch64.Whole.sha_work scr, hd.sub_right (VG.Proof.Ed25519.AArch64.Whole.sha_sub scr), hd.sub_right (VG.Proof.Ed25519.AArch64.Whole.work_sub scr), hsp,
    hks.sub_right (VG.Proof.Ed25519.AArch64.Whole.sha_sub scr), hkp, hks.sub_right (VG.Proof.Ed25519.AArch64.Whole.work_sub scr)⟩

theorem finalize_pre {t : State} {scr out : Addr}
    (h0 : t.gpr .x0 = scr) (h2 : t.gpr .x2 = out) (h3 : t.gpr .x3 = scr + 192)
    (hd : Region.Disjoint ⟨out, 64⟩ ⟨scr, 8192⟩) (hsp : 16 ≤ t.sp.toNat)
    (hks : (VG.Proof.Ed25519.AArch64.Whole.CK t.sp).Disjoint ⟨scr, 8192⟩) (hko : (VG.Proof.Ed25519.AArch64.Whole.CK t.sp).Disjoint ⟨out, 64⟩) :
    Proof.Sha512.finalizeAArch64.pre
      (t.callEntry.withRegions [] (VG.Proof.Ed25519.AArch64.Whole.finalizeWr scr out)) := by
  simp only [Proof.Sha512.finalizeAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), h0, h2, h3]
  exact ⟨True.intro, rfl, (hd.sub_right (VG.Proof.Ed25519.AArch64.Whole.sha_sub scr)).symm, VG.Proof.Ed25519.AArch64.Whole.sha_work scr, hd.sub_right (VG.Proof.Ed25519.AArch64.Whole.work_sub scr), hsp,
    hks.sub_right (VG.Proof.Ed25519.AArch64.Whole.sha_sub scr), hko, hks.sub_right (VG.Proof.Ed25519.AArch64.Whole.work_sub scr)⟩

/-- The SHA state and temporary workspace are prefixes of the outer scratch. -/
theorem hash_writes {E scr : Addr} {wr : List Region} (hs : (⟨scr,8192⟩ : Region) ∈ wr) :
    ∀ r ∈ VG.Proof.Ed25519.AArch64.Whole.hashWr scr, VG.Proof.Ed25519.AArch64.Whole.Within r (VG.Proof.Ed25519.AArch64.Whole.FR E) ∨ ∃ R ∈ wr, VG.Proof.Ed25519.AArch64.Whole.Within r R := by
  intro r hr
  simp only [VG.Proof.Ed25519.AArch64.Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inr ⟨_, hs, 0, (BitVec.add_zero scr).symm, by change 0+192≤8192; decide⟩
  · exact .inr ⟨_, hs, 192, rfl, by change 192+688≤8192; decide⟩

theorem init_writes {E scr : Addr} {wr : List Region} (hs : (⟨scr,8192⟩ : Region) ∈ wr) :
    ∀ r ∈ VG.Proof.Ed25519.AArch64.Whole.initWr scr, VG.Proof.Ed25519.AArch64.Whole.Within r (VG.Proof.Ed25519.AArch64.Whole.FR E) ∨ ∃ R ∈ wr, VG.Proof.Ed25519.AArch64.Whole.Within r R := by
  intro r hr
  simp only [VG.Proof.Ed25519.AArch64.Whole.initWr, List.mem_singleton] at hr
  subst r
  exact .inr ⟨_, hs, 0, (BitVec.add_zero scr).symm, by change 0+192≤8192; decide⟩

theorem covers_writes {E : Addr} {rd wr ws : List Region}
    (hw : ∀ r ∈ ws, VG.Proof.Ed25519.AArch64.Whole.Within r (VG.Proof.Ed25519.AArch64.Whole.FR E) ∨ ∃ R ∈ wr, VG.Proof.Ed25519.AArch64.Whole.Within r R) :
    Covers ws (rd ++ VG.Proof.Ed25519.AArch64.Whole.FR E :: wr) := by
  refine Covers.of_sub fun r hr => ?_
  rcases hw r hr with hf | ⟨R, hR, hs⟩
  · exact ⟨VG.Proof.Ed25519.AArch64.Whole.FR E, List.mem_append_right _ List.mem_cons_self, hf⟩
  · exact ⟨R, List.mem_append_right _ (List.mem_cons_of_mem _ hR), hs⟩

end VG.Proof.Ed25519.AArch64.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Setup`. -/
section

namespace VG.Proof.Ed25519.AArch64.Whole
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

def value (E : Addr) (m : Mem) : Value → BitVec 64
  | .const n => BitVec.ofNat 64 n
  | .frame d => E + BitVec.ofNat 64 d
  | .caller j d => m.read (E + BitVec.ofNat 64 (256 + 8 * j)) 8 + BitVec.ofNat 64 d

def valid : Value → Prop
  | .const n => n < 65536
  | .frame d => d < 4096
  | .caller j d => j < 6 ∧ d < 4096

structure SetupStep (rs : List Reg) (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = s.mem
  vec : t.v = s.v
  regs : ∀ r, r ∉ rs → t.gpr r = s.gpr r

theorem SetupStep.refl (s : State) : VG.Proof.Ed25519.AArch64.Whole.SetupStep [] s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem SetupStep.trans {rs rs' : List Reg} {s t u : State}
    (h : VG.Proof.Ed25519.AArch64.Whole.SetupStep rs s t) (h' : VG.Proof.Ed25519.AArch64.Whole.SetupStep rs' t u) : VG.Proof.Ed25519.AArch64.Whole.SetupStep (rs ++ rs') s u := by
  refine ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp,
    h'.mem.trans h.mem, h'.vec.trans h.vec, ?_⟩
  intro r hr
  exact (h'.regs r (fun hmem => hr (List.mem_append_right _ hmem))).trans
    (h.regs r (fun hmem => hr (List.mem_append_left _ hmem)))

theorem setArg_ok {s : State} {E : Addr} {r : Reg} {v : Value}
    (he : s.sp = E) (hv : VG.Proof.Ed25519.AArch64.Whole.valid v)
    (hr : ∀ j d, v = .caller j d → InRegions (s.rd ++ s.wr) (E + BitVec.ofNat 64 (256 + 8 * j)) 8) :
    WP isa (.block (setArg r v)) s fun t => VG.Proof.Ed25519.AArch64.Whole.SetupStep [r] s t ∧ t.gpr r = VG.Proof.Ed25519.AArch64.Whole.value E s.mem v := by
  cases v with
  | const n =>
    change n < 65536 at hv
    have hn : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
    apply WP.of_runBlock
    simp only [setArg, VG.Proof.Ed25519.AArch64.Whole.value, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, Nat.mul_zero, Nat.zero_lt_succ, ite_true, BitVec.shiftLeft_zero,
      hn, Option.some.injEq, exists_eq_left']
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, ?_⟩, ?_⟩
    · intro q hq
      exact RegUpd.gpr_write_of_ne s .x _ (by simpa using hq)
    · simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq]
  | frame d =>
    change d < 4096 at hv
    apply WP.of_runBlock
    simp only [setArg, VG.Proof.Ed25519.AArch64.Whole.value, runBlock_cons, runStep_some, runBlock_nil, exec,
      hv, ite_true, he, Option.some.injEq, exists_eq_left']
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, ?_⟩, ?_⟩
    · intro q hq
      exact RegUpd.gpr_write_of_ne s .x _ (by simpa using hq)
    · simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq]
  | caller j d =>
    obtain ⟨hj, hd⟩ := hv
    have ha : (256 + 8 * j) % 8 = 0 ∧ 256 + 8 * j < 32768 := by omega
    have hr' := hr j d rfl
    apply WP.of_runBlock
    simp only [setArg, VG.Proof.Ed25519.AArch64.Whole.value, runBlock_cons, runStep_some, runBlock_nil, exec,
      ha.1, ha.2, and_self, hd, ite_true, he, State.load, hr', Option.map_some, State.read,
      Size.bits, BitVec.setWidth_eq, RegUpd.gpr_write_self,
      Option.some.injEq, exists_eq_left']
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, ?_⟩, ?_⟩
    · intro q hq
      have hqr : q ≠ r := by simpa using hq
      rw [RegUpd.gpr_write_of_ne _ _ _ hqr, RegUpd.gpr_write_of_ne _ _ _ hqr]
    · exact True.intro

/-- Setup does not touch memory and writes each destination exactly once. -/
theorem setup_ok {s : State} {E : Addr} {args : List (Reg × Value)}
    (he : s.sp = E) (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, VG.Proof.Ed25519.AArch64.Whole.valid p.2)
    (hr : ∀ j < 6, InRegions (s.rd ++ s.wr) (E + BitVec.ofNat 64 (256 + 8 * j)) 8) :
    WP isa (.block (VG.Impl.Ed25519.AArch64.Whole.setup args)) s fun t => VG.Proof.Ed25519.AArch64.Whole.SetupStep (args.map Prod.fst) s t ∧
      ∀ p ∈ args, t.gpr p.1 = VG.Proof.Ed25519.AArch64.Whole.value E s.mem p.2 := by
  induction args generalizing s with
  | nil => exact WP.block_nil ⟨SetupStep.refl s, fun _ h => by cases h⟩
  | cons p ps ih =>
    obtain ⟨r, v⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hn
    rw [VG.Impl.Ed25519.AArch64.Whole.setup, List.flatMap_cons, WP.block_append_iff]
    have hv0 := hv (r,v) List.mem_cons_self
    refine WP.mono (VG.Proof.Ed25519.AArch64.Whole.setArg_ok he hv0 ?_) fun u ⟨hu, hval⟩ => ?_
    · intro j d h
      subst v
      exact hr j hv0.1
    refine WP.mono (ih (hu.sp.trans he) hn.2
      (fun p hp => hv p (List.mem_cons_of_mem _ hp)) ?_) fun t ⟨ht, hvals⟩ => ?_
    · intro j hj
      rw [hu.rd, hu.wr]
      exact hr j hj
    refine ⟨hu.trans ht, ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact (ht.regs r hn.1).trans hval
    · rw [hvals p hp, hu.mem]

theorem Ctx.setup {E : Addr} {g : Reg → BitVec 64} {v : VReg → BitVec 128}
    {m₀ : Mem} {rd wr : List Region} {s : State} (hc : VG.Proof.Ed25519.AArch64.Whole.Ctx E g v m₀ rd wr s)
    {args : List (Reg × Value)} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, VG.Proof.Ed25519.AArch64.Whole.valid p.2)
    (hr : VG.Proof.Ed25519.AArch64.Whole.ARGS E ∈ rd)
    (hregs : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (VG.Impl.Ed25519.AArch64.Whole.setup args)) s fun t => VG.Proof.Ed25519.AArch64.Whole.Ctx E g v m₀ rd wr t ∧
      t.mem = s.mem ∧ ∀ p ∈ args, t.gpr p.1 = VG.Proof.Ed25519.AArch64.Whole.value E s.mem p.2 := by
  refine WP.mono (VG.Proof.Ed25519.AArch64.Whole.setup_ok hc.sp hn hv ?_) fun t ⟨ht, hvals⟩ => ?_
  · intro j hj
    rw [hc.rd, hc.wr]
    refine ⟨VG.Proof.Ed25519.AArch64.Whole.ARGS E, List.mem_append_left _ hr, ?_⟩
    have ha : E + BitVec.ofNat 64 (256 + 8 * j) =
        E + 256 + BitVec.ofNat 64 (8 * j) := by
      rw [BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    rw [ha]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
  refine ⟨hc.regs ht.rd ht.wr ht.sp ?_ ht.vec ht.mem, ht.mem, hvals⟩
  intro r hpres _
  apply ht.regs
  intro hm
  obtain ⟨p, hp, heq⟩ := List.mem_map.mp hm
  exact hregs p hp (heq ▸ hpres)

end VG.Proof.Ed25519.AArch64.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wipe`. -/
section

namespace VG.Proof.Ed25519.AArch64.Whole
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

structure WipeStep (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  vec : t.v = s.v
  regs : ∀ r, r ≠ .x14 → r ≠ .x15 → t.gpr r = s.gpr r

theorem WipeStep.trans {s t u : State} (h : VG.Proof.Ed25519.AArch64.Whole.WipeStep s t) (h' : VG.Proof.Ed25519.AArch64.Whole.WipeStep t u) : VG.Proof.Ed25519.AArch64.Whole.WipeStep s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp, h'.vec.trans h.vec,
    fun r h0 h15 => (h'.regs r h0 h15).trans (h.regs r h0 h15)⟩

theorem zeroWord_ok {s : State} {E : Addr} (he : s.sp = E)
    (hr : (⟨E, 256⟩ : Region) ∈ s.wr) {k : Nat} (hk : k < 32) :
    WP isa (.block (zeroWord k)) s fun t => VG.Proof.Ed25519.AArch64.Whole.WipeStep s t ∧
      t.mem = s.mem.writeW (E + BitVec.ofNat 64 (8 * k)) (0 : BitVec 64) := by
  have dest : InRegions s.wr (E + BitVec.ofNat 64 (8 * k)) 8 :=
    ⟨⟨E, 256⟩, hr, Offset.contains_base E (by omega) (by omega)⟩
  have ha {t : State} : exec (.addSp .x15 0) t = some (t.write .x .x15 t.sp) := by
    simp only [exec, show 0 < 4096 from by decide, ite_true, BitVec.add_zero]
  have hz {t : State} : exec (.movz .x .x14 0 0) t = some (t.write .x .x14 0) := by
    simp only [exec, Size.bits, show 16 * 0 < 64 from by decide, ite_true]
    rfl
  apply WP.of_runBlock
  simp only [zeroWord, runBlock_cons, runStep_some, ha, hz]
  rw [exec_str_x ⟨by omega, by omega⟩ (by
    simpa only [RegUpd.wr_write, RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true,
      BitVec.setWidth_eq, he] using dest)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨⟨rfl, rfl, rfl, rfl, ?_⟩, ?_⟩
  · intro r h14 h15
    simp only [RegUpd.gpr_write, h14, h15, ite_false]
  · simp only [RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
      BitVec.setWidth_eq, he]

structure WipeInv (E : Addr) (s : State) (start n : Nat) (t : State) : Prop where
  step : VG.Proof.Ed25519.AArch64.Whole.WipeStep s t
  frame : Frame [⟨E + BitVec.ofNat 64 (8 * start), 8 * n⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (E + BitVec.ofNat 64 (8 * (start + j))) 64 = 0

theorem zeroWords_ok {s : State} {E : Addr} (he : s.sp = E)
    (hw : (⟨E, 256⟩ : Region) ∈ s.wr) (start : Nat) :
    ∀ n, start + n ≤ 32 → WP isa (.block (VG.Impl.Ed25519.AArch64.Whole.zeroWords start n)) s (VG.Proof.Ed25519.AArch64.Whole.WipeInv E s start n)
  | 0, _ => WP.block_nil ⟨⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩, Frame.refl _ _, fun _ h => by omega⟩
  | n + 1, hn => by
    rw [VG.Impl.Ed25519.AArch64.Whole.zeroWords, List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed25519.AArch64.Whole.zeroWords_ok he hw start n (by omega)) fun u hu => ?_
    refine WP.mono (VG.Proof.Ed25519.AArch64.Whole.zeroWord_ok (hu.step.sp.trans he) (hu.step.wr ▸ hw) (by omega : start + n < 32))
      fun t ⟨kt, mt⟩ => ?_
    refine ⟨hu.step.trans kt, ?_, fun j hj => ?_⟩
    · rw [mt]
      have old : Frame [⟨E + BitVec.ofNat 64 (8 * start), 8 * (n + 1)⟩] s.mem u.mem :=
        Frame.sub hu.frame fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
      exact old.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega) (by omega) (by omega))
    · rw [mt]
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (a := E + BitVec.ofNat 64 (8 * (start + j)))
          (b := E + BitVec.ofNat 64 (8 * (start + n))) ?_ (by decide)]
        · exact hu.words j (by omega)
        · exact Offset.sep _ (by omega) (by omega) (by omega)

theorem Ctx.zeroWords {E : Addr} {g : Reg → BitVec 64} {v : VReg → BitVec 128}
    {m₀ : Mem} {rd wr : List Region} {s : State} (hc : VG.Proof.Ed25519.AArch64.Whole.Ctx E g v m₀ rd wr s)
    {start count : Nat} (hn : start + count ≤ 32) :
    WP isa (.block (VG.Impl.Ed25519.AArch64.Whole.zeroWords start count)) s fun t => VG.Proof.Ed25519.AArch64.Whole.Ctx E g v m₀ rd wr t ∧
      Frame [⟨E + BitVec.ofNat 64 (8 * start), 8 * count⟩] s.mem t.mem ∧
      ∀ j < count, t.mem.readW (E + BitVec.ofNat 64 (8 * (start + j))) 64 = 0 := by
  refine WP.mono (VG.Proof.Ed25519.AArch64.Whole.zeroWords_ok hc.sp (by rw [hc.wr]; exact List.mem_cons_self) start count hn)
    fun t ht => ⟨?_, ht.frame, ht.words⟩
  refine hc.of_frame ht.step.rd ht.step.wr ht.step.sp ?_ ?_ ht.frame ?_
  · intro r hr _
    apply ht.step.regs
    · rintro rfl; simp [preserved] at hr
    · rintro rfl; simp [preserved] at hr
  · intro r _; rw [ht.step.vec]
  · intro r hr; rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ (by omega))

end VG.Proof.Ed25519.AArch64.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wrap`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.Whole.Entry`. -/
section
namespace VG.Proof.Ed25519.AArch64.Whole
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

structure EntryStep (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  v : t.v = s.v
  regs : ∀ r, r ≠ .x15 → t.gpr r = s.gpr r

theorem EntryStep.refl (s : State) : VG.Proof.Ed25519.AArch64.Whole.EntryStep s s := ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
theorem EntryStep.trans {s t u : State} (h : VG.Proof.Ed25519.AArch64.Whole.EntryStep s t) (h' : VG.Proof.Ed25519.AArch64.Whole.EntryStep t u) : VG.Proof.Ed25519.AArch64.Whole.EntryStep s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp, h'.v.trans h.v,
    fun r hn => (h'.regs r hn).trans (h.regs r hn)⟩

theorem argReg_ne15 (j : Nat) : argReg j ≠ .x15 := by
  unfold argReg
  split <;> decide

theorem saveWord_ok {s : State} {j : Nat} (hj : j < 6)
    (hw : InRegions s.wr (s.sp + BitVec.ofNat 64 (256 + 8 * j)) 8) :
    WP isa (.block (saveWord j)) s fun t => VG.Proof.Ed25519.AArch64.Whole.EntryStep s t ∧
      t.mem = s.mem.writeW (s.sp + BitVec.ofNat 64 (256 + 8 * j)) (s.gpr (argReg j)) := by
  have hs : 256 + 8 * j < 4096 := by omega
  apply WP.of_runBlock
  simp only [saveWord, runBlock_cons, runStep_some, runBlock_nil, exec, State.store, Size.bits,
    Size.bytes, State.read, addr, hs, RegUpd.gpr_write, RegUpd.wr_write,
    RegUpd.mem_write, RegUpd.sp_write, VG.Proof.Ed25519.AArch64.Whole.argReg_ne15, BitVec.setWidth_eq,
    Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, ite_true, ite_false,
    Option.bind_some, hw, BitVec.add_zero, Mem.writeW, Option.some.injEq, exists_eq_left']
  refine ⟨⟨rfl, rfl, rfl, rfl, ?_⟩, True.intro⟩
  intro r hn
  simp only [RegUpd.gpr_write, hn, ite_false]

structure Saved (s : State) (n : Nat) (t : State) : Prop where
  step : VG.Proof.Ed25519.AArch64.Whole.EntryStep s t
  frame : Frame [⟨s.sp + 256, 48⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (s.sp + BitVec.ofNat 64 (256 + 8 * j)) 64 = s.gpr (argReg j)

theorem savePrefix_ok {s : State} (hw : (⟨s.sp, 320⟩ : Region) ∈ s.wr) :
    ∀ n ≤ 6, WP isa (.block ((List.range n).flatMap saveWord)) s (VG.Proof.Ed25519.AArch64.Whole.Saved s n)
  | 0, _ => WP.block_nil ⟨.refl s, Frame.refl _ _, fun _ h => by omega⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed25519.AArch64.Whole.savePrefix_ok hw n (by omega)) fun u hu => ?_
    have uw : InRegions u.wr (u.sp + BitVec.ofNat 64 (256 + 8 * n)) 8 := by
      rw [hu.step.sp, hu.step.wr]
      exact ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩
    refine WP.mono (VG.Proof.Ed25519.AArch64.Whole.saveWord_ok (by omega) uw) fun t ⟨ht, mt⟩ => ?_
    rw [hu.step.sp, hu.step.regs _ (VG.Proof.Ed25519.AArch64.Whole.argReg_ne15 n)] at mt
    refine ⟨hu.step.trans ht, ?_, fun j hj => ?_⟩
    · rw [mt]
      exact hu.frame.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (e := 256) (k := 48) (by omega) (by omega) (by decide))
    · rw [mt]
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep ?_ (by decide)]
        · exact hu.words j (by omega)
        · exact Offset.sep _ (by omega) (by omega) (by omega)

theorem saveArgs_ok {s : State} (hw : (⟨s.sp, 320⟩ : Region) ∈ s.wr) :
    WP isa (.block saveArgs) s (VG.Proof.Ed25519.AArch64.Whole.Saved s 6) := VG.Proof.Ed25519.AArch64.Whole.savePrefix_ok hw 6 (by decide)

end VG.Proof.Ed25519.AArch64.Whole
end

namespace VG.Proof.Ed25519.AArch64.Whole
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

abbrev base (s : State) : Addr := s.sp - 336
abbrev entered (s : State) : State := allocated 320 (pushed .x30 s)
abbrev bodyRd (s : State) : List Region := s.rd ++ [VG.Proof.Ed25519.AArch64.Whole.ARGS (VG.Proof.Ed25519.AArch64.Whole.base s)]
abbrev bodyWr (s : State) : List Region := VG.Proof.Ed25519.AArch64.Whole.FR (VG.Proof.Ed25519.AArch64.Whole.base s) :: s.wr

theorem entered_sp (s : State) : (VG.Proof.Ed25519.AArch64.Whole.entered s).sp = VG.Proof.Ed25519.AArch64.Whole.base s := by
  change s.sp - 16 - 320#64 = s.sp - 336
  rw [BitVec.sub_sub]
  rfl

theorem base_lr (s : State) : VG.Proof.Ed25519.AArch64.Whole.base s + 320 = s.sp - 16 := by
  change s.sp - 336#64 + 320#64 = s.sp - 16#64
  rw [show (336#64) = 16#64 + 320#64 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem base_return (s : State) : VG.Proof.Ed25519.AArch64.Whole.base s + 320 + 16 = s.sp := by
  rw [VG.Proof.Ed25519.AArch64.Whole.base_lr, BitVec.sub_add_cancel]

theorem entered_wr (s : State) : (VG.Proof.Ed25519.AArch64.Whole.entered s).wr = ⟨VG.Proof.Ed25519.AArch64.Whole.base s, 320⟩ :: ⟨s.sp - 16, 16⟩ :: s.wr := by
  change ⟨(VG.Proof.Ed25519.AArch64.Whole.entered s).sp, 320⟩ :: ⟨s.sp - 16, 16⟩ :: s.wr = _
  rw [VG.Proof.Ed25519.AArch64.Whole.entered_sp]

/-- The frame of a callee of the body is in the 352 bytes below the stack pointer. -/
theorem ck_sub (s : State) : Region.Sub (VG.Proof.Ed25519.AArch64.Whole.CK (VG.Proof.Ed25519.AArch64.Whole.base s)) (below s.sp 352) := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  have e : s.sp - BitVec.ofNat 64 336 - BitVec.ofNat 64 16 = s.sp - BitVec.ofNat 64 352 :=
    Offset.sub_sub_ofNat _ _ _
  change (x - (s.sp - BitVec.ofNat 64 336 - BitVec.ofNat 64 16)).toNat + 1 ≤ 16 at hx
  rw [e] at hx
  omega

theorem stk_sub (s : State) : Region.Sub ⟨VG.Proof.Ed25519.AArch64.Whole.base s, 336⟩ (below s.sp 352) :=
  below_sub (by decide) (by decide)

theorem base_16 {s : State} (h : 352 ≤ s.sp.toNat) : 16 ≤ (VG.Proof.Ed25519.AArch64.Whole.base s).toNat := by
  change 16 ≤ (s.sp - 336#64).toNat
  rw [BitVec.toNat_sub_of_le (by change 336 ≤ s.sp.toNat; omega)]
  change 16 ≤ s.sp.toNat - 336
  omega

theorem saved_ctx {s p : State} (hs : VG.Proof.Ed25519.AArch64.Whole.Saved (VG.Proof.Ed25519.AArch64.Whole.entered s) 6 p) :
    VG.Proof.Ed25519.AArch64.Whole.Ctx (VG.Proof.Ed25519.AArch64.Whole.base s) s.gpr s.v p.mem (VG.Proof.Ed25519.AArch64.Whole.bodyRd s) s.wr (p.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd s) (VG.Proof.Ed25519.AArch64.Whole.bodyWr s)) := by
  refine ⟨rfl, rfl, hs.step.sp.trans (VG.Proof.Ed25519.AArch64.Whole.entered_sp s), ?_, ?_, Frame.refl _ _⟩
  · intro r hr _
    exact hs.step.regs r (by intro h; subst r; simp [preserved] at hr)
  · intro r _
    change (p.v r).extractLsb' 0 64 = _
    rw [hs.step.v]
    rfl

theorem saved_frame {s p : State} (hs : VG.Proof.Ed25519.AArch64.Whole.Saved (VG.Proof.Ed25519.AArch64.Whole.entered s) 6 p) :
    Frame [below s.sp 336] s.mem p.mem := by
  have hp : Frame [below s.sp 336] s.mem (VG.Proof.Ed25519.AArch64.Whole.entered s).mem := by
    exact Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _
      (below_frame_contains s.sp 320 (by decide))
  refine hp.trans (Frame.sub hs.frame fun r hr => ?_)
  rw [List.mem_singleton.mp hr, VG.Proof.Ed25519.AArch64.Whole.entered_sp]
  exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide : 256 + 48 ≤ 336)⟩

theorem saved_words {s p : State} (hs : VG.Proof.Ed25519.AArch64.Whole.Saved (VG.Proof.Ed25519.AArch64.Whole.entered s) 6 p) {j : Nat} (hj : j < 6) :
    p.mem.readW (VG.Proof.Ed25519.AArch64.Whole.base s + BitVec.ofNat 64 (256 + 8 * j)) 64 = s.gpr (argReg j) := by
  have h := hs.words j hj
  rw [VG.Proof.Ed25519.AArch64.Whole.entered_sp] at h
  exact h

/-- The complete operations share one LR save and a 320-byte allocation.
Their body sees writable locals and readonly saved arguments, and its
callees' frames take 16 more bytes below them. -/
theorem wrap_ok {body : Prog isa} (hn : body.aarch64Depth ≤ 1) {s : State}
    (hsp : 352 ≤ s.sp.toNat)
    (hw : ∀ r ∈ s.wr, (below s.sp 352).Disjoint r)
    {P : Mem → Mem → BitVec 64 → Prop}
    (hb : ∀ p, VG.Proof.Ed25519.AArch64.Whole.Saved (VG.Proof.Ed25519.AArch64.Whole.entered s) 6 p →
      WP isa body (p.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd s) (VG.Proof.Ed25519.AArch64.Whole.bodyWr s)) fun u =>
        VG.Proof.Ed25519.AArch64.Whole.Ctx (VG.Proof.Ed25519.AArch64.Whole.base s) s.gpr s.v p.mem (VG.Proof.Ed25519.AArch64.Whole.bodyRd s) s.wr u ∧ P p.mem u.mem (u.gpr .x0)) :
    WP isa (wrap body) s fun t => abiPreserved s t ∧
      ∃ m, Frame [below s.sp 336] s.mem m ∧ P m t.mem (t.gpr .x0) := by
  refine WP.frame (by omega) (WP.alloc (by decide) ?_ ?_)
  · change 320 ≤ (s.sp - 16).toNat
    rw [BitVec.toNat_sub_of_le (by change 16 ≤ s.sp.toNat; omega)]
    change 320 ≤ s.sp.toNat - 16
    omega
  · refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.Whole.saveArgs_ok (s := VG.Proof.Ed25519.AArch64.Whole.entered s) (by simp [VG.Proof.Ed25519.AArch64.Whole.entered_wr, VG.Proof.Ed25519.AArch64.Whole.entered_sp])) fun p hp => ?_)
    refine WP.narrowF (hb p hp) ?_ ?_ ?_ (by omega)
    · refine Covers.of_sub fun r hr => ?_
      simp only [VG.Proof.Ed25519.AArch64.Whole.bodyRd, VG.Proof.Ed25519.AArch64.Whole.bodyWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [hp.step.rd, hp.step.wr, VG.Proof.Ed25519.AArch64.Whole.entered_wr]
      rcases hr with (hr | rfl) | (rfl | hr)
      · exact ⟨r, List.mem_append_left _ hr, 0, by simp⟩
      · exact ⟨⟨VG.Proof.Ed25519.AArch64.Whole.base s, 320⟩, List.mem_append_right _ List.mem_cons_self, 256, rfl, by change 256 + 48 ≤ 320; decide⟩
      · exact ⟨⟨VG.Proof.Ed25519.AArch64.Whole.base s, 320⟩, List.mem_append_right _ List.mem_cons_self, 0, by simp⟩
      · exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)), 0, by simp⟩
    · refine Covers.of_sub fun r hr => ?_
      rw [hp.step.wr, VG.Proof.Ed25519.AArch64.Whole.entered_wr]
      simp only [VG.Proof.Ed25519.AArch64.Whole.bodyWr, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨⟨VG.Proof.Ed25519.AArch64.Whole.base s, 320⟩, List.mem_cons_self, 0, by simp⟩
      · exact ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), 0, by simp⟩
    · intro u _ _ hsu hf ⟨hc, ho⟩
      have usp : u.sp = VG.Proof.Ed25519.AArch64.Whole.base s := hc.sp
      have lr_sep : ∀ r ∈ VG.Proof.Ed25519.AArch64.Whole.bodyWr s ++ [below p.sp (16 * body.aarch64Depth)],
          (⟨s.sp - 16, 16⟩ : Region).Disjoint r := by
        intro r hr
        simp only [VG.Proof.Ed25519.AArch64.Whole.bodyWr, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | hr | rfl
        · rw [← VG.Proof.Ed25519.AArch64.Whole.base_lr]
          exact Offset.disjoint_base _ (by decide) (by decide)
        · exact (hw r hr).sub_left (below_sub (by decide : 16 ≤ 352) (by decide))
        · rw [hp.step.sp, VG.Proof.Ed25519.AArch64.Whole.entered_sp, ← VG.Proof.Ed25519.AArch64.Whole.base_lr]
          exact (Offset.below_disjoint (VG.Proof.Ed25519.AArch64.Whole.base s) (m := 16 * body.aarch64Depth) (l := 336) (by omega)).symm.sub_left
            (Offset.sub_base _ (by decide : 320 + 16 ≤ 336))
      have lr : u.mem.read (VG.Proof.Ed25519.AArch64.Whole.base s + 320) 8 = s.gpr .x30 := by
        rw [VG.Proof.Ed25519.AArch64.Whole.base_lr, hf.read (r := ⟨s.sp - 16, 16⟩) (by simp [Region.Contains]) lr_sep (by decide)]
        rw [hp.frame.read (r := ⟨s.sp - 16, 16⟩) (by simp [Region.Contains]) ?_ (by decide)]
        · exact read_write_self _ _ _
        · rintro r hr
          rw [List.mem_singleton.mp hr, VG.Proof.Ed25519.AArch64.Whole.entered_sp, ← VG.Proof.Ed25519.AArch64.Whole.base_lr]
          exact Offset.disjoint _ (d := 320) (e := 256) (by decide) (by decide) (by decide)
      refine ⟨⟨?_, ?_, ?_⟩, p.mem, VG.Proof.Ed25519.AArch64.Whole.saved_frame hp, ?_⟩
      · intro r hr
        change ((freed 320 u).write .x .x30 (u.mem.read (u.sp + 320#64) 8)).gpr r = _
        rw [usp]
        change ((freed 320 u).write .x .x30 (u.mem.read (VG.Proof.Ed25519.AArch64.Whole.base s + (320 : BitVec 64)) 8)).gpr r = _
        rw [lr, RegUpd.gpr_write]
        by_cases h30 : r = .x30
        · subst r; simp only [ite_true, BitVec.setWidth_eq]
        · simp only [h30, ite_false]
          exact hc.cs r hr h30
      · change u.sp + 320#64 + 16 = s.sp
        rw [usp]
        exact VG.Proof.Ed25519.AArch64.Whole.base_return s
      · intro r hr
        change (((freed 320 u).write .x .x30 (u.mem.read (u.sp + 320#64) 8)).v r).extractLsb' 0 64 = _
        rw [RegUpd.v_write]
        exact hc.vs r hr
      · change P p.mem ((freed 320 u).write .x .x30 (u.mem.read (u.sp + 320#64) 8)).mem
          (((freed 320 u).write .x .x30 (u.mem.read (u.sp + 320#64) 8)).gpr .x0)
        rw [RegUpd.mem_write, RegUpd.gpr_write_of_ne _ _ _ (by decide)]
        exact ho

end VG.Proof.Ed25519.AArch64.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT`. -/
section

namespace VG.Proof.Ed25519.AArch64.Whole
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

/-- Relational rule for a register-saving frame. -/
theorem frame_ct {r r' : Reg} {body : Prog isa} {P R : State → State → Prop}
    (hsp : ∀ a b, P a b → a.sp = b.sp)
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = pushed r s ∧ b = pushed r t) body R) :
    RelCT isa P (.frame (.push r) body (.pop r')) fun _ _ => True := by
  intro s t ts tt s' t' hp es et
  have push_eq : ∀ {a b : State}, isa.push (.push r) a = some b → b = pushed r a := by
    intro a b h
    simp only [isa, push] at h
    split at h <;> cases h
    rfl
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have ea := push_eq ps
      have eb := push_eq pt
      subst ea eb
      obtain ⟨rfl, _⟩ := hb _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ bs bt
      have sp₁ := (Exec.rdwr bs).2.2
      have sp₂ := (Exec.rdwr bt).2.2
      have he := hsp s t hp
      refine ⟨?_, trivial⟩
      simp only [addrs, sp₁, sp₂, pushed, he]

/-- Allocating and freeing a buffer emits no data-address leakage. -/
theorem alloc_ct {bytes : Nat} {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = allocated bytes s ∧ b = allocated bytes t) body R) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s t ts tt s' t' hp es et
  have alloc_eq : ∀ {a b : State}, isa.push (.alloc bytes) a = some b → b = allocated bytes a := by
    intro a b h
    simp only [isa, push] at h
    split at h <;> cases h
    rfl
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have ea := alloc_eq ps
      have eb := alloc_eq pt
      subst ea eb
      obtain ⟨rfl, _⟩ := hb _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ bs bt
      exact ⟨rfl, trivial⟩

/-- The trace from wider permissions is determined by any terminating
execution with the narrowed body permissions. -/
theorem body_trace {c : Prog isa} {s : State} {rd wr : List Region} {P : State → Prop}
    (hb : WP isa c (s.withRegions rd wr) P)
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr)
    {trace : List Leak} {t : State} (he : Exec isa c s trace t) :
    ∃ u, Exec isa c (s.withRegions rd wr) trace u := by
  obtain ⟨tr, u, hu, _⟩ := hb
  have hw' := Exec.widen hu (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions, State.withRegions_self] at hw'
  obtain ⟨rfl, _⟩ := Exec.det he hw'
  exact ⟨_, hu⟩

theorem saved_covers {s p : State} (hp : VG.Proof.Ed25519.AArch64.Whole.Saved (VG.Proof.Ed25519.AArch64.Whole.entered s) 6 p) :
    Covers (VG.Proof.Ed25519.AArch64.Whole.bodyRd s ++ VG.Proof.Ed25519.AArch64.Whole.bodyWr s) (p.rd ++ p.wr) ∧ Covers (VG.Proof.Ed25519.AArch64.Whole.bodyWr s) p.wr := by
  constructor
  · refine Covers.of_sub fun r hr => ?_
    simp only [VG.Proof.Ed25519.AArch64.Whole.bodyRd, VG.Proof.Ed25519.AArch64.Whole.bodyWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hp.step.rd, hp.step.wr, VG.Proof.Ed25519.AArch64.Whole.entered_wr]
    rcases hr with (hr | rfl) | (rfl | hr)
    · exact ⟨r, List.mem_append_left _ hr, 0, by simp⟩
    · exact ⟨⟨VG.Proof.Ed25519.AArch64.Whole.base s, 320⟩, List.mem_append_right _ List.mem_cons_self, 256, rfl, by change 256 + 48 ≤ 320; decide⟩
    · exact ⟨⟨VG.Proof.Ed25519.AArch64.Whole.base s, 320⟩, List.mem_append_right _ List.mem_cons_self, 0, by simp⟩
    · exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)), 0, by simp⟩
  · refine Covers.of_sub fun r hr => ?_
    rw [hp.step.wr, VG.Proof.Ed25519.AArch64.Whole.entered_wr]
    simp only [VG.Proof.Ed25519.AArch64.Whole.bodyWr, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨⟨VG.Proof.Ed25519.AArch64.Whole.base s, 320⟩, List.mem_cons_self, 0, by simp⟩
    · exact ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), 0, by simp⟩

theorem saveArgs_ct : RelCT isa (fun s t => s.sp = t.sp) (.block saveArgs) (fun _ _ => True) := by
  refine (RelCT.taint (A := taint) (Taint.ofRegs []) (fun s t h => ?_) (by taint_decide))
  exact ⟨h, fun _ hr => False.elim (by simp at hr)⟩

/-- The saved-argument prologue and both frames preserve body constant time. -/
theorem wrap_ct {body : Prog isa} {Pre : State → Prop} {Pub : State → State → Prop}
    (hsp : ∀ s t, Pub s t → s.sp = t.sp)
    (hb : ∀ s, Pre s → ∀ p, VG.Proof.Ed25519.AArch64.Whole.Saved (VG.Proof.Ed25519.AArch64.Whole.entered s) 6 p →
      WP isa body (p.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd s) (VG.Proof.Ed25519.AArch64.Whole.bodyWr s)) (fun _ => True))
    (hct : ∀ s t, Pre s → Pre t → Pub s t → RelCT isa
      (fun a b => ∃ p q, VG.Proof.Ed25519.AArch64.Whole.Saved (VG.Proof.Ed25519.AArch64.Whole.entered s) 6 p ∧ VG.Proof.Ed25519.AArch64.Whole.Saved (VG.Proof.Ed25519.AArch64.Whole.entered t) 6 q ∧
        a = p.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd s) (VG.Proof.Ed25519.AArch64.Whole.bodyWr s) ∧ b = q.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd t) (VG.Proof.Ed25519.AArch64.Whole.bodyWr t))
      body (fun _ _ => True)) : ConstantTime isa Pre Pub (wrap body) := by
  apply RelCT.constantTime
  refine VG.Proof.Ed25519.AArch64.Whole.frame_ct (fun s t h => hsp s t h.2.2) (VG.Proof.Ed25519.AArch64.Whole.alloc_ct (R := fun _ _ => True) ?_)
  rintro a b ta tb a' b' ⟨p, q, ⟨s, t, ⟨ps, pt, pub⟩, rfl, rfl⟩, rfl, rfl⟩ ea eb
  cases ea with
  | seq esa eba =>
    cases eb with
    | seq esb ebb =>
      obtain ⟨_, pa, exa, hpa⟩ := VG.Proof.Ed25519.AArch64.Whole.saveArgs_ok (s := VG.Proof.Ed25519.AArch64.Whole.entered s) (by rw [VG.Proof.Ed25519.AArch64.Whole.entered_wr, VG.Proof.Ed25519.AArch64.Whole.entered_sp]; exact List.mem_cons_self)
      obtain ⟨_, pb, exb, hpb⟩ := VG.Proof.Ed25519.AArch64.Whole.saveArgs_ok (s := VG.Proof.Ed25519.AArch64.Whole.entered t) (by rw [VG.Proof.Ed25519.AArch64.Whole.entered_wr, VG.Proof.Ed25519.AArch64.Whole.entered_sp]; exact List.mem_cons_self)
      obtain ⟨_, rfl⟩ := Exec.det esa exa
      obtain ⟨_, rfl⟩ := Exec.det esb exb
      have trsave := (VG.Proof.Ed25519.AArch64.Whole.saveArgs_ct _ _ _ _ _ _ (by
        change (VG.Proof.Ed25519.AArch64.Whole.entered s).sp = (VG.Proof.Ed25519.AArch64.Whole.entered t).sp
        rw [VG.Proof.Ed25519.AArch64.Whole.entered_sp, VG.Proof.Ed25519.AArch64.Whole.entered_sp]
        exact congrArg (fun x : Addr => x - 336) (hsp s t pub)) esa esb).1
      obtain ⟨ua, eua⟩ := VG.Proof.Ed25519.AArch64.Whole.body_trace (hb s ps _ hpa) (VG.Proof.Ed25519.AArch64.Whole.saved_covers hpa).1 (VG.Proof.Ed25519.AArch64.Whole.saved_covers hpa).2 eba
      obtain ⟨ub, eub⟩ := VG.Proof.Ed25519.AArch64.Whole.body_trace (hb t pt _ hpb) (VG.Proof.Ed25519.AArch64.Whole.saved_covers hpb).1 (VG.Proof.Ed25519.AArch64.Whole.saved_covers hpb).2 ebb
      have trbody := (hct s t ps pt pub _ _ _ _ _ _ ⟨_, _, hpa, hpb, rfl, rfl⟩ eua eub).1
      exact ⟨by rw [trsave, trbody], trivial⟩

end VG.Proof.Ed25519.AArch64.Whole

end
