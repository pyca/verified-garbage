import VerifiedGarbage.Proof.Rsa.AArch64.PrivLay
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# `vg_rsa_private_checked` on AArch64: between the frames' pushes and pops

`Ctx` is what holds there: the permissions, `sp = B`, the callee-saved
registers, our return address in its frame, and that memory changed only in
`out`, `scratch` and the stack. `Slots` is the arguments the code keeps in
the inner frame's slots. `entered` is the state the inner frame's body
starts in.
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked

theorem add_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem read8 (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

/-- A 64-bit `write` is a `writeW`. -/
theorem write8 (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

/-- The state between the frames' pushes and pops: `g` and `vv` are the
registers on entry, `m₀` the memory. -/
structure Ctx (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (t : State) :
    Prop where
  rd : t.rd = [L.N, L.E, L.IN, L.P, L.Q, L.DP, L.DQ, L.QI, L.ARGS]
  wr : t.wr = [L.FR, L.LR, L.OUT, L.SC]
  sp : t.sp = L.B
  cs : ∀ r ∈ preserved, r ≠ .x30 → t.gpr r = g r
  vs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (vv r).extractLsb' 0 64
  lr : t.mem.readW (L.B + BitVec.ofNat 64 frameBytes) 64 = g .x30
  frame : Frame [L.OUT, L.SC, L.STK] m₀ t.mem

/-- The arguments kept in the inner frame's slots. -/
structure Slots (L : Lay) (m : Mem) : Prop where
  out : m.readW (L.B + BitVec.ofNat 64 oOut) 64 = L.out
  n : m.readW (L.B + BitVec.ofNat 64 oN) 64 = L.n
  k : m.readW (L.B + BitVec.ofNat 64 oK) 64 = L.k
  e : m.readW (L.B + BitVec.ofNat 64 oE) 64 = L.e
  el : m.readW (L.B + BitVec.ofNat 64 oEl) 64 = L.el
  inp : m.readW (L.B + BitVec.ofNat 64 oIn) 64 = L.inp

/-- Slots survive changes to memory that miss them. -/
theorem Slots.frame {L : Lay} {m m' : Mem} {rs : List Region} (hk : Slots L m) (hf : Frame rs m m')
    (hd : ∀ R ∈ rs, Region.Disjoint ⟨L.B + BitVec.ofNat 64 oOut, 48⟩ R) (_hB : L.B.toNat + 128 ≤ 2 ^ 64) :
    Slots L m' := by
  have k : ∀ d, oOut ≤ d → d + 8 ≤ oOut + 48 →
      m'.readW (L.B + BitVec.ofNat 64 d) 64 = m.readW (L.B + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    hf.readW (r := ⟨L.B + BitVec.ofNat 64 oOut, 48⟩)
      (Offset.contains _ h₁ (by simpa [oOut] using h₂) (by simp only [oOut]; omega)) hd (by decide)
  exact ⟨(k oOut (by decide) (by decide)).trans hk.out, (k oN (by decide) (by decide)).trans hk.n,
    (k oK (by decide) (by decide)).trans hk.k, (k oE (by decide) (by decide)).trans hk.e,
    (k oEl (by decide) (by decide)).trans hk.el, (k oIn (by decide) (by decide)).trans hk.inp⟩

theorem Lay.Ok.args_contains {L : Lay} (hL : L.Ok) {j : Nat} (hj : j < 12) :
    L.ARGS.Contains (L.B + BitVec.ofNat 64 (arg j)) 8 := by
  have hnB := hL.nB
  refine Offset.contains _ ?_ ?_ ?_ <;> simp only [arg, stackBytes, frameBytes] <;> omega

namespace Ctx

variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t t' : State}
  (hc : Ctx L g vv m₀ t)
include hc

/-- A range in the inner frame may be read. -/
theorem inFr (hL : L.Ok) {d n : Nat} (h : d + n ≤ frameBytes) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h (by have := hL.nB; unfold frameBytes at h; omega)⟩

/-- A range in the inner frame may be written. -/
theorem inFrW (hL : L.Ok) {d n : Nat} (h : d + n ≤ frameBytes) :
    InRegions t.wr (L.B + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains_base _ h (by have := hL.nB; unfold frameBytes at h; omega)⟩

/-- Our stack argument `j` may be read. -/
theorem inArgs (hL : L.Ok) {j : Nat} (hj : j < 12) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 (arg j)) 8 :=
  ⟨L.ARGS, by rw [hc.rd, hc.wr]; simp, hL.args_contains hj⟩

/-- Our stack argument `j`, read in the frames: what it was on entry. -/
theorem argW (hL : L.Ok) {j : Nat} (hj : j < 12) :
    t.mem.readW (L.B + BitVec.ofNat 64 (arg j)) 64 = m₀.readW (L.B + BitVec.ofNat 64 (arg j)) 64 := by
  have hnB := hL.nB
  refine hc.frame.readW (r := L.ARGS) (hL.args_contains hj) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.oa.symm
  · exact hL.sca.symm
  · exact Offset.disjoint_base _ (Nat.le_refl _) (by simp only [stackBytes]; omega)

/-- Code that writes only registers other than the callee-saved ones and
the vector registers. -/
theorem regs (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) (hm : t'.mem = t.mem)
    (hv : t'.v = t.v) (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) : Ctx L g vv m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r hr hr' => (hg r hr hr').trans (hc.cs r hr hr'),
    fun r hr => by rw [hv]; exact hc.vs r hr, by rw [hm]; exact hc.lr, by rw [hm]; exact hc.frame⟩

/-- Code that also writes the inner frame. -/
theorem store (hL : L.Ok) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hv : t'.v = t.v) (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r)
    (hf : Frame [L.FR] t.mem t'.mem) : Ctx L g vv m₀ t' := by
  have hnB := hL.nB
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp,
    fun r hr hr' => (hg r hr hr').trans (hc.cs r hr hr'), fun r hr => by rw [hv]; exact hc.vs r hr,
    ?_, hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  · have hlr : L.LR.Contains (L.B + BitVec.ofNat 64 frameBytes) (64 / 8) := by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
    rw [hf.readW (r := L.LR) hlr (fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR
      exact Offset.disjoint_base _ (Nat.le_refl _) (by simp only [frameBytes]; omega)) (by decide)]
    exact hc.lr
  · simp only [List.mem_singleton] at hr; subst hr
    have := Offset.sub_base L.B (d := 0) (n := frameBytes) (k := stackBytes) (by decide)
    exact ⟨L.STK, by simp, by simpa using this⟩

end Ctx

/-! ## Entering the frames -/

/-- The state in which the inner frame's body starts. -/
def entered (s : State) : State := allocated frameBytes (pushed .x30 s)

@[simp] theorem entered_rd (s : State) : (entered s).rd = s.rd := rfl
@[simp] theorem entered_gpr (s : State) : (entered s).gpr = s.gpr := rfl
@[simp] theorem entered_v (s : State) : (entered s).v = s.v := rfl

theorem entered_sp (s : State) : (entered s).sp = (lay s).B := by
  show s.sp - 16 - BitVec.ofNat 64 frameBytes = s.sp - BitVec.ofNat 64 stackBytes
  simp only [frameBytes, stackBytes]
  bv_omega

theorem lr_slot (s : State) : s.sp - 16 = (lay s).B + BitVec.ofNat 64 frameBytes := by
  show s.sp - 16 = s.sp - BitVec.ofNat 64 stackBytes + BitVec.ofNat 64 frameBytes
  simp only [frameBytes, stackBytes]
  bv_omega

theorem entered_wr (s : State) : (entered s).wr = (lay s).FR :: (lay s).LR :: s.wr := by
  show (⟨s.sp - 16 - BitVec.ofNat 64 frameBytes, frameBytes⟩ : Region) :: ⟨s.sp - 16, 16⟩ :: s.wr = _
  rw [show s.sp - 16 - BitVec.ofNat 64 frameBytes = (lay s).B from entered_sp s, lr_slot]

theorem entered_mem (s : State) :
    (entered s).mem = s.mem.writeW ((lay s).B + BitVec.ofNat 64 frameBytes) (s.gpr .x30) := by
  show s.mem.write (s.sp - 16) 8 (s.gpr .x30) = _
  rw [lr_slot, write8]

theorem arg_slot (s : State) (j : Nat) (hj : j < 12) :
    stackArgAddr s j = (lay s).B + BitVec.ofNat 64 (arg j) := by
  simp only [stackArgAddr, lay, arg, frameBytes, stackBytes]
  have : 8 * j < 2 ^ 64 := by omega
  bv_omega

/-- `Ctx` on entry to the inner frame's body. -/
theorem entered_ctx {s : State} (h : chkA.pre s) : Ctx (lay s) s.gpr s.v s.mem (entered s) := by
  have hL := lay_ok h
  have hnB := hL.nB
  refine ⟨?_, ?_, entered_sp s, fun _ _ _ => rfl, fun _ _ => rfl, ?_, ?_⟩
  · simp only [entered_rd]; rw [h.2.2.1, ← lay_args]; rfl
  · rw [entered_wr, h.2.2.2.1]; rfl
  · rw [entered_mem]; exact Mem.readW_writeW_self64 _ _ _
  · rw [entered_mem]
    exact Frame.writeW (Frame.refl _ _) (r := (lay s).STK) (by simp) _
      (Offset.contains_base _ (by simp only [frameBytes, stackBytes]; omega) (by decide))

/-- The stack arguments on entry, at their place above the frames. -/
theorem arg_m₀ {s : State} (j : Nat) (hj : j < 12) :
    s.mem.readW ((lay s).B + BitVec.ofNat 64 (arg j)) 64 = stackArg s j := by
  rw [stackArg, arg_slot s j hj]

/-- Our stack argument `j`, by the layout. -/
def Lay.argv (L : Lay) : Nat → BitVec 64
  | 0 => L.p | 1 => L.pl | 2 => L.q | 3 => L.ql | 4 => L.dp | 5 => L.dpl | 6 => L.dq | 7 => L.dql
  | 8 => L.qi | 9 => L.qil | 10 => L.scr | 11 => L.sl | _ => 0

/-- Our stack arguments, in memory `m` above the frames. -/
def ArgsAt (L : Lay) (m : Mem) : Prop :=
  ∀ j < 12, m.readW (L.B + BitVec.ofNat 64 (arg j)) 64 = L.argv j

theorem argsAt_entry (s : State) : ArgsAt (lay s) s.mem := by
  intro j hj
  rw [arg_m₀ j hj]
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ => rfl

end VG.Proof.Rsa.AArch64
