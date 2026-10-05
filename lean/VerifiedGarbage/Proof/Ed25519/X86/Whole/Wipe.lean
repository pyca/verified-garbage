import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Impl.Ed25519.X86.Whole.Setup
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
import VerifiedGarbage.Proof.Sha512.X86.Stream.Finalize
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Spec.Sha512.Contract
import VerifiedGarbage.Proof.Ed25519.X86.ScalarVerified
import VerifiedGarbage.Impl.Ed25519.X86.Whole.Wipe

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.Whole.BlocksCT`. -/
section

/-! Blocks whose memory addresses depend only on ESP, and functional facts
retained while composing their equal-leakage proofs. -/
namespace VG.Proof.Ed25519.X86.Whole
open VG VG.X86

theorem block_rel {P : State → State → Prop} {is : List Instr}
    (he : ∀ a b, P a b → a.gpr .esp = b.gpr .esp)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block is) hint).isSome = true) :
    RelCT isa P (.block is) fun _ _ => True :=
  RelCT.taint (A := taint) (τr [.esp]) (fun a b h => agree_regs fun r hr => by
    rw [List.mem_singleton.mp hr]; exact he a b h) ht

theorem rel_wp {F F' G G' : State → Prop} {c : Prog isa}
    (hct : RelCT isa (fun a b => F a ∧ F' b) c fun _ _ => True)
    (ha : ∀ a, F a → WP isa c a G) (hb : ∀ b, F' b → WP isa c b G') :
    RelCT isa (fun a b => F a ∧ F' b) c fun a b => G a ∧ G' b :=
  (hct.wp fun a b h => ⟨ha a h.1, hb b h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

end VG.Proof.Ed25519.X86.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.Whole.Layout`. -/
section

/-! Shared frame and call invariants for complete Ed25519 operations on x86. -/
namespace VG.Proof.Ed25519.X86.Whole
open VG VG.X86

def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem Within.sub {r R : Region} (h : VG.Proof.Ed25519.X86.Whole.Within r R) : Region.Sub r R := by
  obtain ⟨off, hb, hl⟩ := h
  obtain ⟨b, n⟩ := r
  simp only at hb hl
  subst hb
  exact Offset.sub_base _ hl

abbrev FR (E : BitVec 32) : Region := ⟨E.setWidth 64, 256⟩
abbrev STK (E : BitVec 32) : Region := ⟨E.setWidth 64 - 24, 280⟩

theorem frame_sub (E : BitVec 32) : Region.Sub (VG.Proof.Ed25519.X86.Whole.FR E) (VG.Proof.Ed25519.X86.Whole.STK E) := by
  have h := Offset.sub_base (E.setWidth 64 - 24) (d := 24) (n := 256) (k := 280) (by decide)
  change Region.Sub ⟨E.setWidth 64 - 24 + 24, 256⟩ (VG.Proof.Ed25519.X86.Whole.STK E) at h
  rw [BitVec.sub_add_cancel] at h
  exact h

theorem below_sub_stack {E : BitVec 32} (hE : 24 ≤ E.toNat) {n : Nat} (hn : n ≤ 24) :
    Region.Sub (below E n) (VG.Proof.Ed25519.X86.Whole.STK E) := by
  have h := below_sub hn hE
  refine fun p hp => ?_
  have h' := h p hp
  simp only [below, Taint.sub_setWidth hE] at h'
  exact Region.sub_prefix (by decide : 24 ≤ 280) p h'

/-- Outer read/write regions exclude the frame. The entry arguments remain in
read-only memory above it. Secret buffers and outgoing cdecl arguments occupy
its 256 bytes; calls use at most 24 more bytes below it. -/
structure Ctx (E : BitVec 32) (g : Reg → BitVec 32) (m₀ : Mem)
    (R W : List Region) (t : State) : Prop where
  rd : t.rd = R
  wr : t.wr = VG.Proof.Ed25519.X86.Whole.FR E :: W
  esp : t.gpr .esp = E
  cs : ∀ r ∈ calleeSaved, r ≠ .esp → t.gpr r = g r
  frame : Frame (W ++ [VG.Proof.Ed25519.X86.Whole.STK E]) m₀ t.mem

namespace Ctx
variable {E : BitVec 32} {g : Reg → BitVec 32} {m₀ : Mem} {rd wr : List Region} {t u : State}

theorem of_frame (h : VG.Proof.Ed25519.X86.Whole.Ctx E g m₀ rd wr t)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hesp : u.gpr .esp = t.gpr .esp)
    (hcs : ∀ r ∈ calleeSaved, r ≠ .esp → u.gpr r = t.gpr r)
    {ws : List Region} (hf : Frame ws t.mem u.mem)
    (hw : ∀ r ∈ ws, Region.Sub r (VG.Proof.Ed25519.X86.Whole.FR E) ∨ ∃ R ∈ wr, Region.Sub r R) :
    VG.Proof.Ed25519.X86.Whole.Ctx E g m₀ rd wr u := by
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hesp.trans h.esp,
    fun r hr hn => (hcs r hr hn).trans (h.cs r hr hn), h.frame.trans ?_⟩
  refine Frame.sub hf fun r hr => ?_
  rcases hw r hr with hf | ⟨R, hR, hs⟩
  · exact ⟨VG.Proof.Ed25519.X86.Whole.STK E, List.mem_append_right _ (List.mem_singleton_self _), fun p hp => VG.Proof.Ed25519.X86.Whole.frame_sub E p (hf p hp)⟩
  · exact ⟨R, List.mem_append_left _ hR, hs⟩

theorem regs (h : VG.Proof.Ed25519.X86.Whole.Ctx E g m₀ rd wr t)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hesp : u.gpr .esp = t.gpr .esp)
    (hcs : ∀ r ∈ calleeSaved, r ≠ .esp → u.gpr r = t.gpr r) (hm : u.mem = t.mem) :
    VG.Proof.Ed25519.X86.Whole.Ctx E g m₀ rd wr u :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hesp.trans h.esp,
    fun r hr hn => (hcs r hr hn).trans (h.cs r hr hn), hm ▸ h.frame⟩

theorem readable_frame (h : VG.Proof.Ed25519.X86.Whole.Ctx E g m₀ rd wr t) {a : Addr} {n : Nat}
    (hc : (VG.Proof.Ed25519.X86.Whole.FR E).Contains a n) : InRegions (t.rd ++ t.wr) a n := by
  rw [h.rd, h.wr]
  exact ⟨VG.Proof.Ed25519.X86.Whole.FR E, List.mem_append_right _ (List.mem_cons_self), hc⟩

theorem writable_frame (h : VG.Proof.Ed25519.X86.Whole.Ctx E g m₀ rd wr t) {a : Addr} {n : Nat}
    (hc : (VG.Proof.Ed25519.X86.Whole.FR E).Contains a n) : InRegions t.wr a n := by
  rw [h.wr]; exact ⟨VG.Proof.Ed25519.X86.Whole.FR E, List.mem_cons_self, hc⟩

end Ctx

/-- Invoke a verified cdecl callee from the shared outgoing argument area.
The precise write frame remains available for retaining other local buffers. -/
theorem call_ok {E : BitVec 32} {g : Reg → BitVec 32} {m₀ : Mem} {rd wr : List Region}
    {t : State} (h : VG.Proof.Ed25519.X86.Whole.Ctx E g m₀ rd wr t) (hE : 24 ≤ E.toNat)
    {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ trace s', Exec isa c s trace s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hstack : stackUse c ≤ 20)
    {rd' wr' : List Region} (hpre : k.pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ VG.Proof.Ed25519.X86.Whole.FR E :: wr))
    (hw : ∀ r ∈ wr', VG.Proof.Ed25519.X86.Whole.Within r (VG.Proof.Ed25519.X86.Whole.FR E) ∨ ∃ R ∈ wr, VG.Proof.Ed25519.X86.Whole.Within r R)
    {Q : State → Prop}
    (hQ : ∀ u, VG.Proof.Ed25519.X86.Whole.Ctx E g m₀ rd wr u → Frame (wr' ++ [below E 24]) t.mem u.mem →
      (∀ r, (∀ i ∈ VG.instrs c, Taint.clobbers i r = false) → u.gpr r = t.gpr r) →
      (∃ s₂ : State, s₂.mem = u.mem ∧ (∀ r, r ≠ .esp → s₂.gpr r = u.gpr r) ∧
        k.post (t.callEntry.withRegions rd' wr') s₂) → Q u) :
    WP isa (.call name c) t Q := by
  have hcw : Covers wr' t.wr := by
    refine Covers.of_sub fun r hr => ?_
    rw [h.wr]
    rcases hw r hr with hf | ⟨R, hR, hs⟩
    · exact ⟨VG.Proof.Ed25519.X86.Whole.FR E, List.mem_cons_self, hf⟩
    · exact ⟨R, List.mem_cons_of_mem _ hR, hs⟩
  have hcr : Covers (rd' ++ wr') (t.rd ++ t.wr) := by rw [h.rd, h.wr]; exact hcov
  refine WP.call hv hsp (by rw [h.esp]; omega) hpre hcr hcw fun u hrd hwr hcs hf hg hp => ?_
  have hf' : Frame (wr' ++ [below E 24]) t.mem u.mem := by
    rw [h.esp] at hf
    exact Frame.below_mono hf (by omega) hE
  refine hQ u ⟨hrd.trans h.rd, hwr.trans h.wr, (hcs .esp (by simp [calleeSaved])).trans h.esp,
    fun r hr hn => (hcs r hr).trans (h.cs r hr hn), h.frame.trans ?_⟩ hf' hg hp
  refine Frame.sub hf' fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rcases hw r hr with hf | ⟨R, hR, hs⟩
    · exact ⟨VG.Proof.Ed25519.X86.Whole.STK E, List.mem_append_right _ (List.mem_singleton_self _), fun p hp => VG.Proof.Ed25519.X86.Whole.frame_sub E p (hf.sub p hp)⟩
    · exact ⟨R, List.mem_append_left _ hR, hs.sub⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.Ed25519.X86.Whole.STK E, List.mem_append_right _ (List.mem_singleton_self _), VG.Proof.Ed25519.X86.Whole.below_sub_stack hE (by decide)⟩

end VG.Proof.Ed25519.X86.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.Whole.CallCT`. -/
section

namespace VG.Proof.Ed25519.X86.Whole
open VG VG.X86

structure CallReady (k : Contract isa) (E : BitVec 32) (rd wr : List Region) (t : State) where
  reads : List Region
  writes : List Region
  pre : k.pre (t.callEntry.withRegions reads writes)
  covers : Covers (reads ++ writes) (rd ++ VG.Proof.Ed25519.X86.Whole.FR E :: wr)
  writable : ∀ r ∈ writes, VG.Proof.Ed25519.X86.Whole.Within r (VG.Proof.Ed25519.X86.Whole.FR E) ∨ ∃ R ∈ wr, VG.Proof.Ed25519.X86.Whole.Within r R

theorem CallReady.covers_state {k : Contract isa} {E : BitVec 32} {g : Reg → BitVec 32}
    {m : Mem} {rd wr : List Region} {t : State} (hc : VG.Proof.Ed25519.X86.Whole.Ctx E g m rd wr t)
    (h : VG.Proof.Ed25519.X86.Whole.CallReady k E rd wr t) :
    Covers (h.reads ++ h.writes) (t.rd ++ t.wr) ∧ Covers h.writes t.wr := by
  refine ⟨by rw [hc.rd, hc.wr]; exact h.covers, Covers.of_sub fun r hr => ?_⟩
  rw [hc.wr]
  rcases h.writable r hr with h | ⟨R, hr, h⟩
  · exact ⟨VG.Proof.Ed25519.X86.Whole.FR E, List.mem_cons_self, h⟩
  · exact ⟨R, List.mem_cons_of_mem _ hr, h⟩

theorem CallReady.wp {k : Contract isa} {E : BitVec 32} {g : Reg → BitVec 32}
    {m : Mem} {rd wr : List Region} {t : State} (hc : VG.Proof.Ed25519.X86.Whole.Ctx E g m rd wr t)
    (h : VG.Proof.Ed25519.X86.Whole.CallReady k E rd wr t) {c : Prog isa} {name : String}
    (hv : ∀ s, k.pre s → ∃ trace s', Exec isa c s trace s' ∧ abiPreserved s s' ∧ k.post s s')
    (hs : NoSp c) (hb : stackUse c ≤ 20) (he : 24 ≤ E.toNat) :
    WP isa (.call name c) t (VG.Proof.Ed25519.X86.Whole.Ctx E g m rd wr) :=
  VG.Proof.Ed25519.X86.Whole.call_ok hc he hv hs hb h.pre h.covers h.writable fun _ hc _ _ _ => hc

/-- Independent permission narrowing in each run leaves call traces unchanged. -/
theorem callEx {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop}
    (hP : ∀ a b, P a b → ∃ ar aw br bw,
      k.pre (a.callEntry.withRegions ar aw) ∧ k.pre (b.callEntry.withRegions br bw) ∧
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw) ∧
      Covers (ar ++ aw) (a.rd ++ a.wr) ∧ Covers aw a.wr ∧
      Covers (br ++ bw) (b.rd ++ b.wr) ∧ Covers bw b.wr ∧ a.gpr .esp = b.gpr .esp) :
    RelCT isa P (.call n c) fun _ _ => True := by
  intro a b ta tb a' b' hp ea eb
  obtain ⟨ar, aw, br, bw, pa, pb, pub, ca, wa, cb, wb, sp⟩ := hP a b hp
  cases ea with
  | call ha xa ra =>
    cases eb with
    | call hb xb rb =>
      rw [call_callEntry, Option.some.injEq] at ha hb
      subst ha hb
      obtain ⟨_, na⟩ := trace_narrow hv pa (by simpa using ca) (by simpa using wa) xa
      obtain ⟨_, nb⟩ := trace_narrow hv pb (by simpa using cb) (by simpa using wb) xb
      have ht := hct _ _ _ _ _ _ pa pb pub na nb
      have ga := (ret_gpr ra .esp).1
      have gb := (ret_gpr rb .esp).1
      simp only [State.callEntry_esp] at ga gb
      exact ⟨by simp only [ga, gb, sp, ht], trivial⟩

end VG.Proof.Ed25519.X86.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.Whole.Setup`. -/
section

namespace VG.Proof.Ed25519.X86.Whole
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

def value (E : BitVec 32) (m : Mem) : Value → BitVec 32
  | .const n => BitVec.ofNat 32 n
  | .frame d => E + BitVec.ofNat 32 d
  | .caller i d => m.readW (addr E (260 + 4 * i)) 32 + BitVec.ofNat 32 d

def valid (n : Nat) : Value → Prop
  | .caller i _ => i < n
  | _ => True

structure SetupStep (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  regs : ∀ r, r ≠ .eax → t.gpr r = s.gpr r

theorem SetupStep.refl (s : State) : VG.Proof.Ed25519.X86.Whole.SetupStep s s := ⟨rfl, rfl, fun _ _ => rfl⟩
theorem SetupStep.trans {s t u : State} (h : VG.Proof.Ed25519.X86.Whole.SetupStep s t) (h' : VG.Proof.Ed25519.X86.Whole.SetupStep t u) : VG.Proof.Ed25519.X86.Whole.SetupStep s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, fun r hr => (h'.regs r hr).trans (h.regs r hr)⟩
theorem SetupStep.esp {s t : State} (h : VG.Proof.Ed25519.X86.Whole.SetupStep s t) : t.gpr .esp = s.gpr .esp := h.regs _ (by decide)

theorem put_ok {s : State} {E : BitVec 32} {slot : Nat} {v : Value}
    (he : s.gpr .esp = E)
    (hr : ∀ i d, v = .caller i d → InRegions (s.rd ++ s.wr) (addr E (260 + 4 * i)) 4)
    (hw : InRegions s.wr (addr E (4 * slot)) 4) :
    WP isa (.block (put slot v)) s fun t => VG.Proof.Ed25519.X86.Whole.SetupStep s t ∧
      t.mem = s.mem.writeW (addr E (4 * slot)) (VG.Proof.Ed25519.X86.Whole.value E s.mem v) := by
  cases v with
  | const n =>
    apply WP.of_runBlock
    simp only [put, VG.Impl.Ed25519.X86.Whole.load, VG.Proof.Ed25519.X86.Whole.value, VG.Impl.Ed25519.X86.Whole.at_, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.store32, ea_mk,
      RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
      reduceCtorEq, ite_false, ite_true, he, hw, Option.map_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨⟨rfl, rfl, fun r h => by simp only [RegUpd.gpr_setReg, h, ite_false]⟩, True.intro⟩
  | frame d =>
    apply WP.of_runBlock
    simp only [put, VG.Impl.Ed25519.X86.Whole.load, VG.Proof.Ed25519.X86.Whole.value, VG.Impl.Ed25519.X86.Whole.at_, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.store32, ea_mk,
      RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
      RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
      reduceCtorEq, ite_false, ite_true, he, hw, Option.map_some, Option.bind_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨⟨rfl, rfl, fun r h => by
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h, ite_false]⟩, True.intro⟩
  | caller i d =>
    have hr' := hr i d rfl
    apply WP.of_runBlock
    simp only [put, VG.Impl.Ed25519.X86.Whole.load, VG.Proof.Ed25519.X86.Whole.value, VG.Impl.Ed25519.X86.Whole.at_, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.store32, State.load32, ea_mk,
      RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
      RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
      reduceCtorEq, ite_false, ite_true, he, hw, hr', Option.map_some, Option.bind_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨⟨rfl, rfl, fun r h => by
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h, ite_false]⟩, True.intro⟩

theorem frame_word {s : State} {E : BitVec 32} (hf : E.toNat + 256 ≤ 2 ^ 32)
    (hw : VG.Proof.Ed25519.X86.Whole.FR E ∈ s.wr) {d : Nat} (hd : d + 4 ≤ 256) : InRegions s.wr (addr E d) 4 := by
  refine ⟨_, hw, ?_⟩
  rw [addr_eq (by omega_using [hf, hd])]
  exact Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd])

theorem value_congr {E : BitVec 32} {m m' : Mem} {v : Value} {n : Nat}
    (hf : E.toNat + 260 + 4 * n ≤ 2 ^ 32) (hv : VG.Proof.Ed25519.X86.Whole.valid n v)
    (hm : Frame [⟨E.setWidth 64, 24⟩] m m') : VG.Proof.Ed25519.X86.Whole.value E m' v = VG.Proof.Ed25519.X86.Whole.value E m v := by
  cases v with
  | const => rfl
  | frame => rfl
  | caller i d =>
    change i < n at hv
    unfold VG.Proof.Ed25519.X86.Whole.value
    apply congrArg (· + BitVec.ofNat 32 d)
    rw [addr_eq (by omega_using [hf, hv])]
    refine hm.readW (Region.contains_self _ _) ?_ (by decide)
    rintro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base _ (by omega_using [hv]) (by omega_using [hf, hv])

/-- Set consecutive outgoing argument words. Each instruction shape is checked
once, and the list is composed without repeating symbolic execution. -/
theorem setup_ok {s : State} {E : BitVec 32} {n start : Nat} {vs : List Value}
    (he : s.gpr .esp = E) (hf : E.toNat + 260 + 4 * n ≤ 2 ^ 32)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (addr E (260 + 4 * i)) 4)
    (hw : VG.Proof.Ed25519.X86.Whole.FR E ∈ s.wr) (hlen : start + vs.length ≤ 6)
    (hv : ∀ v ∈ vs, VG.Proof.Ed25519.X86.Whole.valid n v) :
    WP isa (.block (VG.Impl.Ed25519.X86.Whole.setup start vs)) s fun t => VG.Proof.Ed25519.X86.Whole.SetupStep s t ∧
      Frame [⟨E.setWidth 64 + BitVec.ofNat 64 (4 * start), 4 * vs.length⟩] s.mem t.mem ∧
      ∀ j (hj : j < vs.length), t.mem.readW (addr E (4 * (start + j))) 32 =
        VG.Proof.Ed25519.X86.Whole.value E s.mem (vs[j]'hj) := by
  induction vs generalizing s start with
  | nil =>
    exact WP.block_nil ⟨SetupStep.refl s, Frame.refl _ _, fun _ h => by cases h⟩
  | cons v vs ih =>
    rw [VG.Impl.Ed25519.X86.Whole.setup, WP.block_append_iff]
    have fit : E.toNat + 256 ≤ 2 ^ 32 := by omega_using [hf]
    have hs : start < 6 := by simp only [List.length_cons] at hlen; omega_using [hlen]
    have av : VG.Proof.Ed25519.X86.Whole.valid n v := hv v List.mem_cons_self
    refine WP.mono (VG.Proof.Ed25519.X86.Whole.put_ok he (fun i d h => by subst v; exact hr i av)
      (VG.Proof.Ed25519.X86.Whole.frame_word fit hw (by omega_using [hs]))) fun u ⟨hu, hm⟩ => ?_
    have hf24 : Frame [⟨E.setWidth 64, 24⟩] s.mem u.mem := by
      rw [hm, addr_eq (by omega_using [hf, hs])]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by omega_using [hs]) (by omega_using [hs]))
    refine WP.mono (ih (hu.esp.trans he) (by rw [hu.rd, hu.wr]; exact hr)
      (hu.wr ▸ hw) (by simp only [List.length_cons] at hlen; omega_using [hlen])
      (fun v hv' => hv v (List.mem_cons_of_mem _ hv'))) fun t ⟨ht, ft, vt⟩ => ?_
    refine ⟨hu.trans ht, ?_, ?_⟩
    · have fs : Frame [⟨E.setWidth 64 + BitVec.ofNat 64 (4 * start), 4 * (v :: vs).length⟩] s.mem u.mem := by
        rw [hm, addr_eq (by omega_using [hf, hs])]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, List.length_cons]; omega)
      refine fs.trans (Frame.sub ft ?_)
      rintro r hr'
      simp only [List.mem_singleton] at hr'; subst hr'
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      exact Offset.sub _ (by omega) (by simp; omega)
    · intro j hj
      cases j with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        have keep : t.mem.readW (addr E (4 * start)) 32 = u.mem.readW (addr E (4 * start)) 32 := by
          rw [addr_eq (by omega_using [hf, hs])]
          refine ft.readW (Region.contains_self _ _) ?_ (by decide)
          rintro r hr'
          simp only [List.mem_singleton] at hr'; subst hr'
          exact Offset.disjoint _ (by omega) (by simp only [List.length_cons] at hlen; omega_using [hlen])
            (by simp only [List.length_cons] at hlen; omega_using [hlen])
        rw [keep, hm, Mem.readW_writeW_self32]
      | succ j =>
        have hj' : j < vs.length := by simpa using hj
        have e : start + (j + 1) = start + 1 + j := by omega
        rw [e, vt j hj']
        exact VG.Proof.Ed25519.X86.Whole.value_congr hf (hv _ (List.mem_cons_of_mem _ (List.getElem_mem _))) hf24

theorem Ctx.setup {E : BitVec 32} {g : Reg → BitVec 32} {m₀ : Mem} {rd wr : List Region}
    {s : State} (hc : VG.Proof.Ed25519.X86.Whole.Ctx E g m₀ rd wr s) {n start : Nat} {vs : List Value}
    (hf : E.toNat + 260 + 4 * n ≤ 2 ^ 32)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (addr E (260 + 4 * i)) 4)
    (hlen : start + vs.length ≤ 6) (hv : ∀ v ∈ vs, VG.Proof.Ed25519.X86.Whole.valid n v) :
    WP isa (.block (VG.Impl.Ed25519.X86.Whole.setup start vs)) s fun t => VG.Proof.Ed25519.X86.Whole.Ctx E g m₀ rd wr t ∧
      Frame [⟨E.setWidth 64, 24⟩] s.mem t.mem ∧
      ∀ j (hj : j < vs.length), t.mem.readW (addr E (4 * (start + j))) 32 =
        VG.Proof.Ed25519.X86.Whole.value E s.mem (vs[j]'hj) := by
  refine WP.mono (VG.Proof.Ed25519.X86.Whole.setup_ok hc.esp hf hr (by rw [hc.wr]; exact List.mem_cons_self) hlen hv)
    fun t ⟨ht, hft, hvals⟩ => ?_
  have hf24 : Frame [⟨E.setWidth 64, 24⟩] s.mem t.mem :=
    hft.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by omega_using [hlen])⟩
  refine ⟨hc.of_frame ht.rd ht.wr ht.esp ?_ hf24 ?_, hf24, hvals⟩
  · intro r hr _
    apply ht.regs
    rintro rfl
    simp [calleeSaved] at hr
  · intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact .inl (Region.sub_prefix (by decide))

end VG.Proof.Ed25519.X86.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.Whole.Count`. -/
section

/-! The message length is 32 bits; the SHA-512 byte count is a 64-bit pair. -/
namespace VG.Proof.Ed25519.X86.Whole
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

def countHigh (x : BitVec 32) (n : Nat) : BitVec 32 :=
  (BitVec.ofBool (decide (2 ^ 32 ≤ x.toNat + (BitVec.ofNat 32 n).toNat))).setWidth 32

theorem count_pair (x : BitVec 32) (n : Nat) (hn : n < 2 ^ 32) :
    VG.Proof.Ed25519.X86.Whole.countHigh x n ++ (x + BitVec.ofNat 32 n) = BitVec.ofNat 64 (x.toNat + n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (x + BitVec.ofNat 32 n).isLt,
    Nat.shiftLeft_eq]
  have hx := x.isLt
  simp only [VG.Proof.Ed25519.X86.Whole.countHigh, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  by_cases h : 2 ^ 32 ≤ x.toNat + n
  · simp only [h, decide_true, BitVec.ofBool_true]
    change 1 * 2 ^ 32 + (x.toNat + n) % 2 ^ 32 = (x.toNat + n) % 2 ^ 64
    omega
  · simp only [h, decide_false, BitVec.ofBool_false]
    change 0 * 2 ^ 32 + (x.toNat + n) % 2 ^ 32 = (x.toNat + n) % 2 ^ 64
    omega

theorem countArgs_run {s : State} {E : BitVec 32} {index n : Nat}
    (he : s.gpr .esp = E)
    (hr : InRegions (s.rd ++ s.wr) (addr E (260 + 4 * index)) 4)
    (hw1 : InRegions s.wr (addr E 4) 4) (hw2 : InRegions s.wr (addr E 8) 4) :
    WP isa (.block (countArgs index n)) s fun t => t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ .eax → r ≠ .edx → t.gpr r = s.gpr r) ∧
      t.mem = (s.mem.writeW (addr E 4)
        (s.mem.readW (addr E (260 + 4 * index)) 32 + BitVec.ofNat 32 n)).writeW (addr E 8)
        (VG.Proof.Ed25519.X86.Whole.countHigh (s.mem.readW (addr E (260 + 4 * index)) 32) n) := by
  apply WP.of_runBlock
  simp only [countArgs, VG.Impl.Ed25519.X86.Whole.at_, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, State.load32, State.store32, ea_mk, RegUpd.gpr_setReg,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    RegUpd.cf_setReg, RegUpd.cf_arithFlags, reduceCtorEq, ite_true, ite_false,
    he, hr, hw1, hw2, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, fun r h1 h2 => by simp only [h1, h2, ite_false], ?_⟩
  apply congrArg (fun v => (s.mem.writeW (addr E 4)
    (s.mem.readW (addr E (260 + 4 * index)) 32 + BitVec.ofNat 32 n)).writeW (addr E 8) v)
  change (0#32) + VG.Proof.Ed25519.X86.Whole.countHigh (s.mem.readW (addr E (260 + 4 * index)) 32) n = _
  exact BitVec.zero_add _

theorem Ctx.count {E : BitVec 32} {g : Reg → BitVec 32} {m₀ : Mem} {rd wr : List Region}
    {s : State} (hc : VG.Proof.Ed25519.X86.Whole.Ctx E g m₀ rd wr s) {index n : Nat}
    (hf : E.toNat + 256 ≤ 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) (addr E (260 + 4 * index)) 4)
    {x : BitVec 32} (hx : s.mem.readW (addr E (260 + 4 * index)) 32 = x) :
    WP isa (.block (countArgs index n)) s fun t => VG.Proof.Ed25519.X86.Whole.Ctx E g m₀ rd wr t ∧
      Frame [⟨E.setWidth 64 + 4, 8⟩] s.mem t.mem ∧
      t.mem.readW (E.setWidth 64 + 4) 32 = x + BitVec.ofNat 32 n ∧
      t.mem.readW (E.setWidth 64 + 8) 32 = VG.Proof.Ed25519.X86.Whole.countHigh x n := by
  have hw : VG.Proof.Ed25519.X86.Whole.FR E ∈ s.wr := by rw [hc.wr]; exact List.mem_cons_self
  refine WP.mono (VG.Proof.Ed25519.X86.Whole.countArgs_run hc.esp hr (VG.Proof.Ed25519.X86.Whole.frame_word hf hw (by decide))
    (VG.Proof.Ed25519.X86.Whole.frame_word hf hw (by decide))) fun t ⟨htd, htw, htg, htm⟩ => ?_
  rw [hx, addr_eq (x := E) (k := 4) (by omega_using [hf]),
    addr_eq (x := E) (k := 8) (by omega_using [hf])] at htm
  change t.mem = (s.mem.writeW (E.setWidth 64 + (4 : BitVec 64)) (x + BitVec.ofNat 32 n)).writeW (E.setWidth 64 + (8 : BitVec 64)) (VG.Proof.Ed25519.X86.Whole.countHigh x n) at htm
  have hfr : Frame [⟨E.setWidth 64 + 4, 8⟩] s.mem t.mem := by
    rw [htm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (by simp [Region.Contains])).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (e := 4) (k := 8) (d := 8) (n := 4) (by decide) (by decide) (by decide))
  refine ⟨hc.of_frame htd htw (htg _ (by decide) (by decide)) ?_ hfr ?_, hfr, ?_, ?_⟩
  · intro r hr _
    apply htg
    · rintro rfl; simp [calleeSaved] at hr
    · rintro rfl; simp [calleeSaved] at hr
  · intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact .inl (Offset.sub_base _ (d := 4) (by decide))
  · rw [htm, Mem.readW_writeW_sep (w := 32) (w' := 32) (a := E.setWidth 64 + 4) (b := E.setWidth 64 + 8)
      (Offset.sep _ (d := 4) (n := 4) (e := 8) (k := 4) (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32]
  · rw [htm, Mem.readW_writeW_self32]

end VG.Proof.Ed25519.X86.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.Whole.Hash`. -/
section

/-! Reusable verified SHA-512 calls within the complete-operation frame. -/
namespace VG.Proof.Ed25519.X86.Whole
open VG VG.X86
open VG.Impl.Sha512.X86.Stream

abbrev slots (E : BitVec 32) (t : State) (j : Nat) : BitVec 32 :=
  t.mem.readW (E.setWidth 64 + BitVec.ofNat 64 (4 * j)) 32

theorem call_arg {E : BitVec 32} {t : State} (he : t.gpr .esp = E)
    (hE : 24 ≤ E.toNat) (hF : E.toNat + 256 ≤ 2 ^ 32) {j : Nat} (hj : j < 64) :
    arg t.callEntry j = VG.Proof.Ed25519.X86.Whole.slots E t j := by
  rw [arg_callEntry (by rw [he]; omega) (by rw [he]; omega), he]
  change t.mem.readW (addr E (4 * j)) 32 = VG.Proof.Ed25519.X86.Whole.slots E t j
  rw [addr_eq (x := E) (k := 4 * j) (by omega)]

theorem callEntry_frame (t : State) : Frame [below (t.gpr .esp) 4] t.mem t.callEntry.mem := by
  rw [State.callEntry_mem]
  exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem callEntry_bytes {t : State} {r : Region}
    (hd : r.Disjoint (below (t.gpr .esp) 4)) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt t.callEntry.mem r.base r.len = Spec.Ed25519.bytesAt t.mem r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  exact Frame.bytes (VG.Proof.Ed25519.X86.Whole.callEntry_frame t) (by simpa only [List.mem_singleton] using fun R (h : R = below (t.gpr .esp) 4) => h ▸ hd)
    hn (List.mem_range.mp hi)

theorem callEntry_repr {t : State} {p : Addr} {iv : Spec.Sha512.HashValue} {m : List Byte}
    (hd : Region.Disjoint ⟨p, 192⟩ (below (t.gpr .esp) 4))
    (hr : Spec.Sha512.Repr iv t.mem p m) : Spec.Sha512.Repr iv t.callEntry.mem p m := by
  refine Proof.Sha512.Stream.repr_congr (mem := t.mem) ?_ hr
  intro i hi
  exact Frame.bytes (R := ⟨p, 192⟩) (VG.Proof.Ed25519.X86.Whole.callEntry_frame t)
    (by intro R h; simp only [List.mem_singleton] at h; subst h; exact hd)
    (by change 192 ≤ 2 ^ 64; decide) hi

theorem init_nosp : NoSp (VG.Impl.Sha512.X86.Stream.init Spec.Sha512.H0_512) := NoSp.of_all (by decide +kernel)
theorem init_stack : stackUse (VG.Impl.Sha512.X86.Stream.init Spec.Sha512.H0_512) = 0 := rfl
theorem update_nosp : NoSp update := NoSp.of_all (by lit_decide)
theorem update_stack : stackUse update = 20 := by lit_decide
theorem finalize_nosp : NoSp finalize := NoSp.of_all (by lit_decide)
theorem finalize_stack : stackUse finalize = 20 := by lit_decide

variable {E : BitVec 32} {g : Reg → BitVec 32} {m₀ : Mem} {rd wr : List Region} {t : State}

/-- Initialize SHA-512 while retaining the shared frame context. -/
theorem init_call (hc : VG.Proof.Ed25519.X86.Whole.Ctx E g m₀ rd wr t) (hE : 24 ≤ E.toNat)
    {rd' wr' : List Region}
    (hp : (Proof.Sha512.initX86 Spec.Sha512.H0_512).pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ VG.Proof.Ed25519.X86.Whole.FR E :: wr))
    (hw : ∀ r ∈ wr', VG.Proof.Ed25519.X86.Whole.Within r (VG.Proof.Ed25519.X86.Whole.FR E) ∨ ∃ R ∈ wr, VG.Proof.Ed25519.X86.Whole.Within r R)
    {scr : BitVec 32} (ha : arg t.callEntry 0 = scr) :
    WP isa (.call Spec.Sha512.init512Api.name (VG.Impl.Sha512.X86.Stream.init Spec.Sha512.H0_512)) t fun u =>
      VG.Proof.Ed25519.X86.Whole.Ctx E g m₀ rd wr u ∧ Frame (wr' ++ [below E 24]) t.mem u.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem (scr.setWidth 64) [] := by
  refine VG.Proof.Ed25519.X86.Whole.call_ok hc hE (Proof.Sha512.X86.Stream.init_verified _).1 VG.Proof.Ed25519.X86.Whole.init_nosp
    (by rw [VG.Proof.Ed25519.X86.Whole.init_stack]; decide) hp hcov hw fun u hu hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hu, hf, ?_⟩
  change Spec.Sha512.Repr Spec.Sha512.H0_512 s₂.mem ((arg t.callEntry 0).setWidth 64) [] at hpost
  rw [hm, ha] at hpost
  exact hpost

/-- Append an arbitrary byte string; the count is the full 64-bit cdecl pair. -/
theorem update_call (hc : VG.Proof.Ed25519.X86.Whole.Ctx E g m₀ rd wr t) (hE : 24 ≤ E.toNat)
    {rd' wr' : List Region} (hp : Proof.Sha512.updateX86.pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ VG.Proof.Ed25519.X86.Whole.FR E :: wr))
    (hw : ∀ r ∈ wr', VG.Proof.Ed25519.X86.Whole.Within r (VG.Proof.Ed25519.X86.Whole.FR E) ∨ ∃ R ∈ wr, VG.Proof.Ed25519.X86.Whole.Within r R)
    {scr p len : BitVec 32} {prev : List Byte}
    (h0 : arg t.callEntry 0 = scr) (h3 : arg t.callEntry 3 = p) (h4 : arg t.callEntry 4 = len)
    (hcount : Proof.Sha512.countX86 t.callEntry = BitVec.ofNat 64 prev.length)
    (hs : Region.Disjoint ⟨scr.setWidth 64, 192⟩ (below (t.gpr .esp) 4))
    (hd : Region.Disjoint ⟨p.setWidth 64, len.toNat⟩ (below (t.gpr .esp) 4))
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (scr.setWidth 64) prev) :
    WP isa (.call Spec.Sha512.updateScratchApi.name update) t fun u =>
      VG.Proof.Ed25519.X86.Whole.Ctx E g m₀ rd wr u ∧ Frame (wr' ++ [below E 24]) t.mem u.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem (scr.setWidth 64)
        (prev ++ Spec.Ed25519.bytesAt t.mem (p.setWidth 64) len.toNat) := by
  refine VG.Proof.Ed25519.X86.Whole.call_ok hc hE Proof.Sha512.X86.Stream.Update.update_verified.1 VG.Proof.Ed25519.X86.Whole.update_nosp
    (by rw [VG.Proof.Ed25519.X86.Whole.update_stack]) hp hcov hw fun u hu hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hu, hf, ?_⟩
  have h := hpost Spec.Sha512.H0_512 prev
    (by change Spec.Sha512.Repr _ t.callEntry.mem _ _; rw [arg_withRegions, h0]; exact VG.Proof.Ed25519.X86.Whole.callEntry_repr hs hr) hcount
  change Spec.Sha512.Repr _ s₂.mem ((arg t.callEntry 0).setWidth 64)
    (prev ++ Spec.Ed25519.bytesAt t.callEntry.mem ((arg t.callEntry 3).setWidth 64) (arg t.callEntry 4).toNat) at h
  rw [hm, h0, h3, h4, VG.Proof.Ed25519.X86.Whole.callEntry_bytes hd (by change len.toNat ≤ 2 ^ 64; have := len.isLt; omega)] at h
  exact h

/-- Finalize into any separate 64-byte buffer, including the frame's digest. -/
theorem finalize_call (hc : VG.Proof.Ed25519.X86.Whole.Ctx E g m₀ rd wr t) (hE : 24 ≤ E.toNat)
    {rd' wr' : List Region} (hp : Proof.Sha512.finalizeX86.pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ VG.Proof.Ed25519.X86.Whole.FR E :: wr))
    (hw : ∀ r ∈ wr', VG.Proof.Ed25519.X86.Whole.Within r (VG.Proof.Ed25519.X86.Whole.FR E) ∨ ∃ R ∈ wr, VG.Proof.Ed25519.X86.Whole.Within r R)
    {scr out : BitVec 32} {msg : List Byte}
    (h0 : arg t.callEntry 0 = scr) (h3 : arg t.callEntry 3 = out)
    (hcount : Proof.Sha512.countX86 t.callEntry = BitVec.ofNat 64 msg.length)
    (hs : Region.Disjoint ⟨scr.setWidth 64, 192⟩ (below (t.gpr .esp) 4))
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (scr.setWidth 64) msg) (hlen : msg.length < 2 ^ 64) :
    WP isa (.call Spec.Sha512.finalizeScratchApi.name finalize) t fun u =>
      VG.Proof.Ed25519.X86.Whole.Ctx E g m₀ rd wr u ∧ Frame (wr' ++ [below E 24]) t.mem u.mem ∧
      Spec.Ed25519.bytesAt u.mem (out.setWidth 64) 64 = Spec.Sha512.finalHash Spec.Sha512.H0_512 msg := by
  refine VG.Proof.Ed25519.X86.Whole.call_ok hc hE Proof.Sha512.X86.Stream.Finalize.finalize_verified.1 VG.Proof.Ed25519.X86.Whole.finalize_nosp
    (by rw [VG.Proof.Ed25519.X86.Whole.finalize_stack]) hp hcov hw fun u hu hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hu, hf, ?_⟩
  have h := hpost Spec.Sha512.H0_512 msg
    (by change Spec.Sha512.Repr _ t.callEntry.mem _ _; rw [arg_withRegions, h0]; exact VG.Proof.Ed25519.X86.Whole.callEntry_repr hs hr) hlen hcount
  change Spec.Ed25519.bytesAt s₂.mem ((arg t.callEntry 3).setWidth 64) 64 = _ at h
  rw [hm, h3] at h
  exact h

end VG.Proof.Ed25519.X86.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.Whole.HashPre`. -/
section

/-! Spatial preconditions for calls of the x86 streaming SHA-512 functions. -/
namespace VG.Proof.Ed25519.X86.Whole
open VG VG.X86

abbrev SHA (scr : BitVec 32) : Region := ⟨scr.setWidth 64, 192⟩
abbrev WORK (scr : BitVec 32) : Region := ⟨(scr + 192).setWidth 64, 272⟩
abbrev ARGS (E : BitVec 32) (n : Nat) : Region := ⟨E.setWidth 64, n⟩

structure HashSpace (E scr : BitVec 32) : Prop where
  below : 24 ≤ E.toNat
  frameFit : E.toNat + 256 ≤ 2 ^ 32
  scratchFit : scr.toNat + 8192 ≤ 2 ^ 32
  sep : (VG.Proof.Ed25519.X86.Whole.STK E).Disjoint ⟨scr.setWidth 64, 8192⟩

namespace HashSpace
variable {E scr : BitVec 32} (h : VG.Proof.Ed25519.X86.Whole.HashSpace E scr)
include h

theorem work_addr : (scr + 192).setWidth 64 = scr.setWidth 64 + BitVec.ofNat 64 192 := by
  have hs := h.scratchFit
  exact addr_eq (x := scr) (k := 192) (by omega)

theorem work_fit : (scr + 192).toNat + 272 ≤ 2 ^ 32 := by
  have hs := h.scratchFit
  rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl, Nat.mod_eq_of_lt (by omega)]
  omega

omit h in
theorem sha_sub : Region.Sub (VG.Proof.Ed25519.X86.Whole.SHA scr) ⟨scr.setWidth 64, 8192⟩ := Region.sub_prefix (by decide)
theorem work_sub : Region.Sub (VG.Proof.Ed25519.X86.Whole.WORK scr) ⟨scr.setWidth 64, 8192⟩ := by
  rw [show VG.Proof.Ed25519.X86.Whole.WORK scr = ⟨scr.setWidth 64 + BitVec.ofNat 64 192, 272⟩ by rw [VG.Proof.Ed25519.X86.Whole.WORK, h.work_addr]]
  exact Offset.sub_base _ (by decide)

theorem sha_work : (VG.Proof.Ed25519.X86.Whole.SHA scr).Disjoint (VG.Proof.Ed25519.X86.Whole.WORK scr) := by
  change Region.Disjoint ⟨scr.setWidth 64, 192⟩ ⟨(scr + 192).setWidth 64, 272⟩
  rw [h.work_addr]
  exact Offset.base_disjoint _ (by decide) (by decide)

omit h in
theorem args_sub {n : Nat} (hn : n ≤ 256) : Region.Sub (VG.Proof.Ed25519.X86.Whole.ARGS E n) (VG.Proof.Ed25519.X86.Whole.STK E) :=
  fun p hp => VG.Proof.Ed25519.X86.Whole.frame_sub E p (Region.sub_prefix hn p hp)

theorem args_sha {n : Nat} (hn : n ≤ 256) : (VG.Proof.Ed25519.X86.Whole.ARGS E n).Disjoint (VG.Proof.Ed25519.X86.Whole.SHA scr) :=
  (h.sep.sub_left (VG.Proof.Ed25519.X86.Whole.HashSpace.args_sub (E := E) hn)).sub_right (HashSpace.sha_sub (scr := scr))

theorem args_work {n : Nat} (hn : n ≤ 256) : (VG.Proof.Ed25519.X86.Whole.ARGS E n).Disjoint (VG.Proof.Ed25519.X86.Whole.WORK scr) :=
  (h.sep.sub_left (VG.Proof.Ed25519.X86.Whole.HashSpace.args_sub (E := E) hn)).sub_right h.work_sub

theorem below_sha {n : Nat} (hn : n ≤ 24) : (VG.X86.below E n).Disjoint (VG.Proof.Ed25519.X86.Whole.SHA scr) :=
  (h.sep.sub_left (VG.Proof.Ed25519.X86.Whole.below_sub_stack h.below hn)).sub_right (HashSpace.sha_sub (scr := scr))

theorem below_work {n : Nat} (hn : n ≤ 24) : (VG.X86.below E n).Disjoint (VG.Proof.Ed25519.X86.Whole.WORK scr) :=
  (h.sep.sub_left (VG.Proof.Ed25519.X86.Whole.below_sub_stack h.below hn)).sub_right h.work_sub

theorem inner_base : (E - 4).setWidth 64 - 20 = E.setWidth 64 - 24 := by
  have he := h.below
  have e : (E - 4).setWidth 64 = E.setWidth 64 - 4 := Taint.sub_setWidth (m := 4) (by omega)
  rw [e, BitVec.sub_sub]
  rfl

theorem inner_sub : Region.Sub ⟨(E - 4).setWidth 64 - 20, 20⟩ (VG.X86.below E 24) := by
  rw [h.inner_base]
  change Region.Sub ⟨E.setWidth 64 - 24, 20⟩ ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩
  rw [Taint.sub_setWidth h.below]
  exact Region.sub_prefix (by decide)

end HashSpace

variable {E scr : BitVec 32} {t : State}

theorem arg_base (he : t.gpr .esp = E) (rd wr : List Region) :
    argAddr (t.callEntry.withRegions rd wr) 0 = E.setWidth 64 := by
  rw [argAddr_withRegions, argAddr_callEntry, he]
  change (E + 0).setWidth 64 = E.setWidth 64
  exact congrArg (fun x : BitVec 32 => x.setWidth 64) (BitVec.add_zero E)

def initRd (E : BitVec 32) : List Region := [VG.Proof.Ed25519.X86.Whole.ARGS E 4]
def initWr (scr : BitVec 32) : List Region := [VG.Proof.Ed25519.X86.Whole.SHA scr]
def updateRd (E p len : BitVec 32) : List Region := [⟨p.setWidth 64, len.toNat⟩, VG.Proof.Ed25519.X86.Whole.ARGS E 24]
def hashWr (scr : BitVec 32) : List Region := [VG.Proof.Ed25519.X86.Whole.SHA scr, VG.Proof.Ed25519.X86.Whole.WORK scr]
def finalizeRd (E : BitVec 32) : List Region := [VG.Proof.Ed25519.X86.Whole.ARGS E 20]
def finalizeWr (scr out : BitVec 32) : List Region := [VG.Proof.Ed25519.X86.Whole.SHA scr, ⟨out.setWidth 64, 64⟩, VG.Proof.Ed25519.X86.Whole.WORK scr]

theorem init_pre (he : t.gpr .esp = E) (h : VG.Proof.Ed25519.X86.Whole.HashSpace E scr) (ha : VG.Proof.Ed25519.X86.Whole.slots E t 0 = scr) :
    (Proof.Sha512.initX86 Spec.Sha512.H0_512).pre
      (t.callEntry.withRegions (VG.Proof.Ed25519.X86.Whole.initRd E) (VG.Proof.Ed25519.X86.Whole.initWr scr)) := by
  have a0 := (VG.Proof.Ed25519.X86.Whole.call_arg he h.below h.frameFit (j := 0) (by decide)).trans ha
  simp only [Proof.Sha512.initX86, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_esp, arg_withRegions, a0, VG.Proof.Ed25519.X86.Whole.arg_base he, he, VG.Proof.Ed25519.X86.Whole.initRd, VG.Proof.Ed25519.X86.Whole.initWr]
  have hb := h.below
  have hf := h.frameFit
  have hs := h.scratchFit
  refine ⟨trivial, trivial, h.args_sha (by decide), h.below_sha (by decide), by omega, ?_⟩
  have he4 : (E - 4).toNat = E.toNat - 4 := sub_toNat (k := 4) (by omega)
  omega

theorem update_pre (he : t.gpr .esp = E) (h : VG.Proof.Ed25519.X86.Whole.HashSpace E scr) {p len : BitVec 32}
    (ha0 : VG.Proof.Ed25519.X86.Whole.slots E t 0 = scr) (ha3 : VG.Proof.Ed25519.X86.Whole.slots E t 3 = p) (ha4 : VG.Proof.Ed25519.X86.Whole.slots E t 4 = len)
    (ha5 : VG.Proof.Ed25519.X86.Whole.slots E t 5 = scr + 192)
    (hd : Region.Disjoint ⟨p.setWidth 64, len.toNat⟩ ⟨scr.setWidth 64, 8192⟩)
    (hb : (VG.X86.below E 24).Disjoint ⟨p.setWidth 64, len.toNat⟩)
    (hfit : p.toNat + len.toNat ≤ 2 ^ 32) :
    Proof.Sha512.updateX86.pre
      (t.callEntry.withRegions (VG.Proof.Ed25519.X86.Whole.updateRd E p len) (VG.Proof.Ed25519.X86.Whole.hashWr scr)) := by
  have a0 := (VG.Proof.Ed25519.X86.Whole.call_arg he h.below h.frameFit (j := 0) (by decide)).trans ha0
  have a3 := (VG.Proof.Ed25519.X86.Whole.call_arg he h.below h.frameFit (j := 3) (by decide)).trans ha3
  have a4 := (VG.Proof.Ed25519.X86.Whole.call_arg he h.below h.frameFit (j := 4) (by decide)).trans ha4
  have a5 := (VG.Proof.Ed25519.X86.Whole.call_arg he h.below h.frameFit (j := 5) (by decide)).trans ha5
  simp only [Proof.Sha512.updateX86, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_esp, arg_withRegions, a0, a3, a4, a5, VG.Proof.Ed25519.X86.Whole.arg_base he, he, VG.Proof.Ed25519.X86.Whole.updateRd, VG.Proof.Ed25519.X86.Whole.hashWr]
  have he0 := h.below
  have he1 := h.frameFit
  have hs := h.scratchFit
  have he4 : (E - 4).toNat = E.toNat - 4 := sub_toNat (k := 4) (by omega)
  refine ⟨trivial, trivial, h.sha_work, hd.sub_right (HashSpace.sha_sub (scr := scr)), hd.sub_right h.work_sub,
    h.args_sha (by decide), h.args_work (by decide), h.below_sha (by decide), h.below_work (by decide),
    (h.below_sha (n := 24) (by decide)).sub_left h.inner_sub,
    (h.below_work (n := 24) (by decide)).sub_left h.inner_sub,
    hb.sub_left h.inner_sub, by omega, hfit, h.work_fit, ?_, ?_⟩ <;> omega

theorem finalize_pre (he : t.gpr .esp = E) (h : VG.Proof.Ed25519.X86.Whole.HashSpace E scr) {out : BitVec 32}
    (ha0 : VG.Proof.Ed25519.X86.Whole.slots E t 0 = scr) (ha3 : VG.Proof.Ed25519.X86.Whole.slots E t 3 = out) (ha4 : VG.Proof.Ed25519.X86.Whole.slots E t 4 = scr + 192)
    (hd : Region.Disjoint ⟨out.setWidth 64, 64⟩ ⟨scr.setWidth 64, 8192⟩)
    (hb : (VG.X86.below E 24).Disjoint ⟨out.setWidth 64, 64⟩)
    (ha : (VG.Proof.Ed25519.X86.Whole.ARGS E 20).Disjoint ⟨out.setWidth 64, 64⟩)
    (hfit : out.toNat + 64 ≤ 2 ^ 32) :
    Proof.Sha512.finalizeX86.pre
      (t.callEntry.withRegions (VG.Proof.Ed25519.X86.Whole.finalizeRd E) (VG.Proof.Ed25519.X86.Whole.finalizeWr scr out)) := by
  have a0 := (VG.Proof.Ed25519.X86.Whole.call_arg he h.below h.frameFit (j := 0) (by decide)).trans ha0
  have a3 := (VG.Proof.Ed25519.X86.Whole.call_arg he h.below h.frameFit (j := 3) (by decide)).trans ha3
  have a4 := (VG.Proof.Ed25519.X86.Whole.call_arg he h.below h.frameFit (j := 4) (by decide)).trans ha4
  simp only [Proof.Sha512.finalizeX86, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_esp, arg_withRegions, a0, a3, a4, VG.Proof.Ed25519.X86.Whole.arg_base he, he, VG.Proof.Ed25519.X86.Whole.finalizeRd, VG.Proof.Ed25519.X86.Whole.finalizeWr]
  have he0 := h.below
  have he1 := h.frameFit
  have hs := h.scratchFit
  have he4 : (E - 4).toNat = E.toNat - 4 := sub_toNat (k := 4) (by omega)
  refine ⟨trivial, trivial, (hd.sub_right (HashSpace.sha_sub (scr := scr))).symm, h.sha_work, hd.sub_right h.work_sub,
    h.args_sha (by decide), ha, h.args_work (by decide), h.below_sha (by decide),
    hb.sub_left (below_sub (by decide) h.below), h.below_work (by decide),
    (h.below_sha (n := 24) (by decide)).sub_left h.inner_sub, hb.sub_left h.inner_sub,
    (h.below_work (n := 24) (by decide)).sub_left h.inner_sub,
    by omega, hfit, h.work_fit, ?_, ?_⟩ <;> omega

end VG.Proof.Ed25519.X86.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.Whole.Reduce`. -/
section

namespace VG.Proof.Ed25519.X86.Whole
open VG VG.X86 VG.Impl.Ed25519.X86

theorem frame_addr {E : BitVec 32} {d : Nat} (hf : E.toNat + 256 ≤ 2 ^ 32) (hd : d < 256) :
    (E + BitVec.ofNat 32 d).setWidth 64 = E.setWidth 64 + BitVec.ofNat 64 d := addr_eq (by omega)

theorem frame_fit {E : BitVec 32} {d n : Nat} (hf : E.toNat + 256 ≤ 2 ^ 32)
    (hd : d < 256) (hn : d + n ≤ 256) : (E + BitVec.ofNat 32 d).toNat + n ≤ 2 ^ 32 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem frame_below {E : BitVec 32} {d n : Nat} (he : 24 ≤ E.toNat)
    (hf : E.toNat + 256 ≤ 2 ^ 32) (hd : d < 256) (hn : d + n ≤ 256) :
    (below E 4).Disjoint ⟨(E + BitVec.ofNat 32 d).setWidth 64, n⟩ := by
  change Region.Disjoint ⟨(E - BitVec.ofNat 32 4).setWidth 64, 4⟩ _
  rw [Taint.sub_setWidth (by omega : 4 ≤ E.toNat), VG.Proof.Ed25519.X86.Whole.frame_addr hf hd]
  exact Offset.disjoint_below_above _ (by omega)

theorem reduce_nosp : NoSp scalarReduce := NoSp.of_all (by lit_decide)
theorem reduce_stack : stackUse scalarReduce = 0 := by lit_decide

def reduceRd (E : BitVec 32) : List Region :=
  [⟨(E + 192).setWidth 64, 64⟩, ⟨E.setWidth 64, 12⟩]
def reduceWr (E scr : BitVec 32) (d : Nat) : List Region :=
  [⟨(E + BitVec.ofNat 32 d).setWidth 64, 32⟩, ⟨scr.setWidth 64, 8192⟩]

variable {E scr : BitVec 32} {g : Reg → BitVec 32} {m₀ : Mem} {rd wr : List Region}
    {s : State} {d : Nat}

theorem reduce_pre (hc : VG.Proof.Ed25519.X86.Whole.Ctx E g m₀ rd wr s) (H : VG.Proof.Ed25519.X86.Whole.HashSpace E scr)
    (hd : 24 ≤ d) (hd' : d + 32 ≤ 256)
    (a0 : VG.Proof.Ed25519.X86.Whole.slots E s 0 = E + BitVec.ofNat 32 d)
    (a1 : VG.Proof.Ed25519.X86.Whole.slots E s 1 = E + 192) (a2 : VG.Proof.Ed25519.X86.Whole.slots E s 2 = scr) :
    scalarReduceLocal.pre (s.callEntry.withRegions (VG.Proof.Ed25519.X86.Whole.reduceRd E) (VG.Proof.Ed25519.X86.Whole.reduceWr E scr d)) := by
  have ca {j : Nat} (hj : j < 64) := VG.Proof.Ed25519.X86.Whole.call_arg hc.esp H.below H.frameFit hj
  have e0 := (ca (j := 0) (by decide)).trans a0
  have e1 := (ca (j := 1) (by decide)).trans a1
  have e2 := (ca (j := 2) (by decide)).trans a2
  have outSub : Region.Sub ⟨(E + BitVec.ofNat 32 d).setWidth 64, 32⟩ (VG.Proof.Ed25519.X86.Whole.STK E) := by
    rw [VG.Proof.Ed25519.X86.Whole.frame_addr H.frameFit (by omega)]
    exact fun p hp => VG.Proof.Ed25519.X86.Whole.frame_sub E p (Offset.sub_base _ hd' p hp)
  have digSub : Region.Sub ⟨(E + 192).setWidth 64, 64⟩ (VG.Proof.Ed25519.X86.Whole.STK E) := by
    have e : (E + 192).setWidth 64 = E.setWidth 64 + 192 := VG.Proof.Ed25519.X86.Whole.frame_addr H.frameFit (by decide : 192 < 256)
    rw [e]
    exact fun p hp => VG.Proof.Ed25519.X86.Whole.frame_sub E p (Offset.sub_base _ (by decide : 192 + 64 ≤ 256) p hp)
  have argSub : Region.Sub ⟨E.setWidth 64, 12⟩ (VG.Proof.Ed25519.X86.Whole.STK E) :=
    fun p hp => VG.Proof.Ed25519.X86.Whole.frame_sub E p (Region.sub_prefix (by decide) p hp)
  have ab := VG.Proof.Ed25519.X86.Whole.arg_base hc.esp (VG.Proof.Ed25519.X86.Whole.reduceRd E) (VG.Proof.Ed25519.X86.Whole.reduceWr E scr d)
  simp only [scalarReduceLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hc.esp, e0, e1, e2, ab]
  refine ⟨rfl, rfl, H.sep.sub_left outSub, H.sep.sub_left digSub, ?_, H.sep.sub_left argSub,
    VG.Proof.Ed25519.X86.Whole.frame_below H.below H.frameFit (by omega) hd', H.sep.sub_left (VG.Proof.Ed25519.X86.Whole.below_sub_stack H.below (by decide)),
    VG.Proof.Ed25519.X86.Whole.frame_fit H.frameFit (by omega) hd', VG.Proof.Ed25519.X86.Whole.frame_fit H.frameFit (by decide) (by decide), H.scratchFit, ?_⟩
  · rw [VG.Proof.Ed25519.X86.Whole.frame_addr H.frameFit (by omega)]
    exact Offset.base_disjoint _ (by omega) (by omega)
  · have e : (E - 4).toNat = E.toNat - 4 := sub_toNat (k := 4) (by have := H.below; omega)
    rw [e]
    have := H.frameFit; omega

theorem reduce_call (hc : VG.Proof.Ed25519.X86.Whole.Ctx E g m₀ rd wr s) (H : VG.Proof.Ed25519.X86.Whole.HashSpace E scr)
    (hscr : (⟨scr.setWidth 64, 8192⟩ : Region) ∈ wr)
    (hd : 24 ≤ d) (hd' : d + 32 ≤ 256)
    (a0 : VG.Proof.Ed25519.X86.Whole.slots E s 0 = E + BitVec.ofNat 32 d)
    (a1 : VG.Proof.Ed25519.X86.Whole.slots E s 1 = E + 192) (a2 : VG.Proof.Ed25519.X86.Whole.slots E s 2 = scr) :
    WP isa (.call "vg_ed25519_scalar_reduce" scalarReduce) s fun t => VG.Proof.Ed25519.X86.Whole.Ctx E g m₀ rd wr t ∧
      Frame (VG.Proof.Ed25519.X86.Whole.reduceWr E scr d ++ [below E 24]) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem ((E + BitVec.ofNat 32 d).setWidth 64) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem ((E + 192).setWidth 64) 64) := by
  have wd : VG.Proof.Ed25519.X86.Whole.Within ⟨(E + 192).setWidth 64, 64⟩ (VG.Proof.Ed25519.X86.Whole.FR E) :=
    ⟨192, VG.Proof.Ed25519.X86.Whole.frame_addr H.frameFit (by decide), by change 192 + 64 ≤ 256; decide⟩
  have wo : VG.Proof.Ed25519.X86.Whole.Within ⟨(E + BitVec.ofNat 32 d).setWidth 64, 32⟩ (VG.Proof.Ed25519.X86.Whole.FR E) :=
    ⟨d, VG.Proof.Ed25519.X86.Whole.frame_addr H.frameFit (by omega), hd'⟩
  have cov : Covers (VG.Proof.Ed25519.X86.Whole.reduceRd E ++ VG.Proof.Ed25519.X86.Whole.reduceWr E scr d) (rd ++ VG.Proof.Ed25519.X86.Whole.FR E :: wr) := by
    refine Covers.of_sub ?_
    simp only [VG.Proof.Ed25519.X86.Whole.reduceRd, VG.Proof.Ed25519.X86.Whole.reduceWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact ⟨VG.Proof.Ed25519.X86.Whole.FR E, by simp, wd⟩
    · exact ⟨VG.Proof.Ed25519.X86.Whole.FR E, by simp, 0, by simp, by change 0 + 12 ≤ 256; decide⟩
    · exact ⟨VG.Proof.Ed25519.X86.Whole.FR E, by simp, wo⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ hscr), 0, by simp, by simp⟩
  have ws : ∀ r ∈ VG.Proof.Ed25519.X86.Whole.reduceWr E scr d, VG.Proof.Ed25519.X86.Whole.Within r (VG.Proof.Ed25519.X86.Whole.FR E) ∨ ∃ R ∈ wr, VG.Proof.Ed25519.X86.Whole.Within r R := by
    simp only [VG.Proof.Ed25519.X86.Whole.reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl wo
    · exact .inr ⟨_, hscr, 0, by simp, by simp⟩
  with_reducible
    refine VG.Proof.Ed25519.X86.Whole.call_ok hc H.below scalarReduce_ok VG.Proof.Ed25519.X86.Whole.reduce_nosp (by rw [VG.Proof.Ed25519.X86.Whole.reduce_stack]; decide)
      (VG.Proof.Ed25519.X86.Whole.reduce_pre hc H hd hd' a0 a1 a2) cov ws fun t ht hf _ post => ⟨ht, hf, ?_⟩
  obtain ⟨t₂, hm, _, hp⟩ := post
  have ca {j : Nat} (hj : j < 64) := VG.Proof.Ed25519.X86.Whole.call_arg hc.esp H.below H.frameFit hj
  change Spec.Ed25519.bytesAt t₂.mem ((arg s.callEntry 0).setWidth 64) 32 =
    Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.callEntry.mem ((arg s.callEntry 1).setWidth 64) 64) at hp
  rw [hm, (ca (j := 0) (by decide)).trans a0, (ca (j := 1) (by decide)).trans a1] at hp
  rw [hp]
  refine congrArg Spec.Ed25519.scalarReduce ?_
  apply VG.Proof.Ed25519.X86.Whole.callEntry_bytes (r := ⟨(E + 192).setWidth 64, 64⟩) ?_ (by change 64 ≤ 2 ^ 64; decide)
  rw [hc.esp]
  exact (VG.Proof.Ed25519.X86.Whole.frame_below H.below H.frameFit (by decide : 192 < 256) (by decide : 192 + 64 ≤ 256)).symm

end VG.Proof.Ed25519.X86.Whole

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.X86.Whole.Wipe`. -/
section

namespace VG.Proof.Ed25519.X86.Whole
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

theorem zeroWords_ok {s : State} {E : BitVec 32} {start count : Nat}
    (he : s.gpr .esp = E) (hf : E.toNat + 256 ≤ 2 ^ 32)
    (hw : VG.Proof.Ed25519.X86.Whole.FR E ∈ s.wr) (hlen : start + count ≤ 64) :
    WP isa (.block (VG.Impl.Ed25519.X86.Whole.zeroWords start count)) s fun t => VG.Proof.Ed25519.X86.Whole.SetupStep s t ∧
      Frame [⟨E.setWidth 64 + BitVec.ofNat 64 (4 * start), 4 * count⟩] s.mem t.mem ∧
      ∀ j < count, t.mem.readW (addr E (4 * (start + j))) 32 = 0 := by
  induction count generalizing s start with
  | zero =>
    exact WP.block_nil ⟨SetupStep.refl s, Frame.refl _ _, fun _ h => by omega⟩
  | succ count ih =>
    rw [VG.Impl.Ed25519.X86.Whole.zeroWords, List.replicate_succ, VG.Impl.Ed25519.X86.Whole.setup, WP.block_append_iff]
    have hs : start < 64 := by omega
    refine WP.mono (VG.Proof.Ed25519.X86.Whole.put_ok (v := .const 0) he (fun _ _ h => by cases h)
      (VG.Proof.Ed25519.X86.Whole.frame_word hf hw (by omega))) fun u ⟨hu, hm⟩ => ?_
    refine WP.mono (ih (hu.esp.trans he) (hu.wr ▸ hw) (by omega)) fun t ⟨ht, ft, vt⟩ => ?_
    refine ⟨hu.trans ht, ?_, ?_⟩
    · have fs : Frame [⟨E.setWidth 64 + BitVec.ofNat 64 (4 * start), 4 * (count + 1)⟩] s.mem u.mem := by
        rw [hm, addr_eq (by omega)]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
      refine fs.trans (Frame.sub ft ?_)
      rintro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega) (by omega)⟩
    · intro j hj
      cases j with
      | zero =>
        simp only [Nat.add_zero]
        have keep : t.mem.readW (addr E (4 * start)) 32 = u.mem.readW (addr E (4 * start)) 32 := by
          rw [addr_eq (by omega)]
          refine ft.readW (Region.contains_self _ _) ?_ (by decide)
          rintro r hr
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)
        rw [keep, hm, Mem.readW_writeW_self32]
        rfl
      | succ j =>
        rw [show start + (j + 1) = start + 1 + j by omega]
        exact vt j (by omega)

theorem Ctx.zeroWords {E : BitVec 32} {g : Reg → BitVec 32} {m₀ : Mem} {rd wr : List Region}
    {s : State} (hc : VG.Proof.Ed25519.X86.Whole.Ctx E g m₀ rd wr s) {start count : Nat}
    (hf : E.toNat + 256 ≤ 2 ^ 32) (hlen : start + count ≤ 64) :
    WP isa (.block (VG.Impl.Ed25519.X86.Whole.zeroWords start count)) s fun t => VG.Proof.Ed25519.X86.Whole.Ctx E g m₀ rd wr t ∧
      Frame [⟨E.setWidth 64 + BitVec.ofNat 64 (4 * start), 4 * count⟩] s.mem t.mem ∧
      ∀ j < count, t.mem.readW (addr E (4 * (start + j))) 32 = 0 := by
  refine WP.mono (VG.Proof.Ed25519.X86.Whole.zeroWords_ok hc.esp hf (by rw [hc.wr]; exact List.mem_cons_self) hlen)
    fun t ⟨ht, hft, hz⟩ => ⟨hc.of_frame ht.rd ht.wr ht.esp ?_ hft ?_, hft, hz⟩
  · intro r hr _
    apply ht.regs
    rintro rfl
    simp [calleeSaved] at hr
  · rintro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact .inl (Offset.sub_base _ (by omega))

end VG.Proof.Ed25519.X86.Whole

end
