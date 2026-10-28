module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessRt
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessChecks
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedDataGap
import VerifiedGarbage.Proof.RsaKeyGen.X86.CmpCarry
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The witness loop's counters, entropy check and advance at the run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.WitnessRt

theorem fits {g : Geometry} (v : g.Valid) :
    g.array 6 + 4 * g.words ≤ g.L ∧ g.array 0 + 4 * g.words ≤ g.array 6 ∧ 8 ≤ g.words ∧ g.words = 2 * g.w :=
  ⟨v.arrayFit (by decide), g.arrayBefore (by decide), by have := v.minWidth; unfold Geometry.words; omega, rfl⟩

/-- One of the first eight arrays' pointers, a load that leaves `edx`. -/
theorem ptr_short {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) (j : Nat) (index : j < 8)
    (r : Reg) :
    WP isa (.block (VG.Impl.MillerRabin.X86.ptr r j)) s fun t =>
      PtrAt t g.W r (g.array j) ∧ t.mem = s.mem ∧ Keeps [r] s t := by
  have head := v.headerFit
  unfold VG.Impl.MillerRabin.X86.ptr
  simp only [index, ↓reduceIte]
  refine wp_movS (readSrc_ptr C.ws C.base (d := 64 + 8 * j) (by omega)) fun t T _ => WP.block_nil ⟨?_, T.mem, T.keeps⟩
  rw [PtrAt, T.gpr, Nat.zero_add]
  exact C.pointers j index

theorem draw_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) :
    WP isa (.block draw) s fun t =>
      t.gpr .edx = BitVec.ofNat 32 (8 * g.w) ∧ t.mem = s.mem ∧ Keeps [.edx] s t := by
  have head := v.headerFit
  have bound := v.maxWidth
  have width := C.width
  unfold draw
  refine wp_movS (readSrc_ptr C.ws C.base (d := 48) (by omega)) fun a A _ => wp_addS rfl fun b B _ =>
    wp_addS rfl fun c C _ => wp_addS rfl fun t T _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    have wv : (s.mem.readW (off g.W 48) 32).toNat = g.w := width
    rw [T.gpr, C.gpr, B.gpr, A.gpr, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, wv, BitVec.toNat_ofNat]
    omega
  · rw [T.mem, C.mem, B.mem, A.mem]
  · exact ((A.keeps.trans B.keeps).trans C.keeps).trans T.keeps

/-- The required tests as `checks` computes them: three, and one more
below each of five widths, nineteen more below five. -/
def formula (w : Nat) : Nat :=
  3 + (if w < 59 then 1 else 0) + (if w < 22 then 1 else 0) + (if w < 8 then 1 else 0) +
    (if w < 7 then 1 else 0) + (if w < 6 then 1 else 0) + (if w < 5 then 19 else 0)

theorem formula_eq : ∀ w ≤ 128, formula w = VG.Impl.RsaKeyGen.X86.WitnessChecks.checks w := by decide

theorem mask_value (x : Bool) (m : BitVec 32) :
    (0#32 - (BitVec.ofBool x).setWidth 32) &&& m = if x then m else 0#32 := by
  cases x
  · exact BitVec.zero_and
  · change BitVec.allOnes 32 &&& m = m
    exact BitVec.allOnes_and

theorem term_ok {g : Geometry} (v : g.Valid) {s : State} (S : Scr s g.W g.L) (width : w32 s.mem g.W 48 = g.w)
    (c m : Nat) (hc : c < 2 ^ 32) :
    WP isa (.block (term c m)) s fun t =>
      t.gpr .ecx = s.gpr .ecx + BitVec.ofNat 32 (if g.w < c then m else 0) ∧ t.mem = s.mem ∧
        Keeps [.eax, .ecx] s t := by
  have head := v.headerFit
  unfold term
  refine wp_movS (readSrc_sc S (d := 48) (by omega)) fun a A _ => wp_cmpCarry rfl fun b B carry =>
    wp_sbbS rfl carry fun d D _ => wp_andi fun e E => wp_addS rfl fun t T _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · have less : (a.gpr .eax).toNat < (BitVec.ofNat 32 c).toNat ↔ g.w < c := by
      rw [A.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]
      exact Iff.of_eq (congrArg (· < c) width)
    rw [T.gpr, E.other .ecx (by decide), D.other .ecx (by decide), B.gpr, A.other .ecx (by decide), E.gpr, D.gpr,
      B.gpr, BitVec.sub_self, mask_value]
    by_cases h : g.w < c
    · simp only [decide_eq_true (less.mpr h), h, ↓reduceIte]
    · simp only [decide_eq_false (fun H => h (less.mp H)), h, ↓reduceIte, Bool.false_eq_true]
  · rw [T.mem, E.mem, D.mem, B.mem, A.mem]
  · exact ((((A.keeps.mono (by decide)).widen (B.keeps [])).widen D.keeps).widen E.keeps).trans
      (T.keeps.mono (by decide))

theorem term_chain {g : Geometry} (v : g.Valid) {s : State} (S : Scr s g.W g.L) (width : w32 s.mem g.W 48 = g.w)
    {c m : Nat} (hc : c < 2 ^ 32) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .ecx = s.gpr .ecx + BitVec.ofNat 32 (if g.w < c then m else 0) → t.mem = s.mem →
      Keeps [.eax, .ecx] s t → WP isa (.block rest) t Q) :
    WP isa (.block (term c m ++ rest)) s Q :=
  WP.block_append (WP.mono (term_ok v S width c m hc) fun t ⟨E, M, K⟩ => k t E M K)

theorem checks_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Prepare.Data g c capacity p s) :
    WP isa (.block checks) s fun t =>
      Prepare.Data g c capacity p t ∧ w32 t.mem g.W 176 = 0 ∧ w32 t.mem g.W 192 = 0 ∧
      w32 t.mem g.W 200 = VG.Impl.RsaKeyGen.X86.WitnessChecks.checks g.w ∧
      Outs g.W WitnessChecks.ranges s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
  have head := v.headerFit
  have bound := v.maxWidth
  unfold checks
  simp only [List.append_assoc]
  refine WP.block_append ?_
  refine wp_movS rfl fun a A _ => ?_
  have Sa := S.ready.scratch.of_keeps A.keeps (by decide)
  refine wp_storeS (Sa.ea (by omega)) (Sa.write (by omega)) fun b B => ?_
  have Kb := A.keeps.widen (B.keeps [])
  have Sb := S.ready.scratch.of_keeps Kb (by decide)
  refine wp_storeS (Sb.ea (by omega)) (Sb.write (by omega)) fun d D => wp_movS rfl fun e E _ => WP.block_nil ?_
  have Ke : Keeps [.eax, .ecx] s e := ((Kb.widen (D.keeps [])).mono (by decide)).widen E.keeps
  have Ob : Outside g.W 176 4 s.mem b.mem := by
    rw [B.mem, A.mem]
    exact writeW32_outside _ _ _ (by decide)
  have Od : Outside g.W 192 4 b.mem d.mem := by
    rw [D.mem]
    exact writeW32_outside _ _ _ (by decide)
  have Me : e.mem = d.mem := E.mem
  have widthE : w32 e.mem g.W 48 = g.w := by
    rw [Me, Od.w32 (by decide) (by decide), Ob.w32 (by decide) (by decide)]
    exact S.ready.context.width
  have Se := S.ready.scratch.of_keeps Ke (by decide)
  have ecxE : e.gpr .ecx = BitVec.ofNat 32 3 := E.gpr
  refine term_chain v Se widthE (by decide) fun f F Mf Kf => ?_
  have Sf := Se.of_keeps Kf (by decide)
  refine term_chain v Sf (by rw [Mf]; exact widthE) (by decide) fun h H Mh Kh => ?_
  have Sh := Sf.of_keeps Kh (by decide)
  refine term_chain v Sh (by rw [Mh, Mf]; exact widthE) (by decide) fun i I Mi Ki => ?_
  have Si := Sh.of_keeps Ki (by decide)
  refine term_chain v Si (by rw [Mi, Mh, Mf]; exact widthE) (by decide) fun j J Mj Kj => ?_
  have Sj := Si.of_keeps Kj (by decide)
  refine term_chain v Sj (by rw [Mj, Mi, Mh, Mf]; exact widthE) (by decide) fun l Lr Ml Kl => ?_
  have Sl := Sj.of_keeps Kl (by decide)
  refine term_chain v Sl (by rw [Ml, Mj, Mi, Mh, Mf]; exact widthE) (by decide) fun n N Mn Kn => ?_
  have Sn := Sl.of_keeps Kn (by decide)
  refine wp_storeS (Sn.ea (by omega)) (Sn.write (by omega)) fun t T => WP.block_nil ?_
  have Mn' : n.mem = d.mem := by rw [Mn, Ml, Mj, Mi, Mh, Mf, Me]
  have Ot : Outside g.W 200 4 d.mem t.mem := by
    rw [T.mem, Mn']
    exact writeW32_outside _ _ _ (by decide)
  have gap : Outside g.W 128 96 s.mem t.mem :=
    ((Ob.mono (by decide) (by decide)).trans (Od.mono (by decide) (by decide))).trans (Ot.mono (by decide) (by decide))
  have K : Keeps [.eax, .ecx] s t :=
    ((((((Ke.trans Kf).trans Kh).trans Ki).trans Kj).trans Kl).trans Kn).widen (T.keeps [])
  refine ⟨S.keepHeader v (by decide) (by decide) gap K (by decide) (by decide), ?_, ?_, ?_, ?_, K⟩
  · rw [Ot.w32 (by decide) (by decide), Od.w32 (by decide) (by decide), B.mem, w32_write_self, A.gpr]
    rfl
  · rw [Ot.w32 (by decide) (by decide), D.mem, w32_write_self, B.gpr, A.gpr]
    rfl
  · rw [T.mem, w32_write_self, N, Lr, J, I, H, F, ecxE, ← BitVec.ofNat_add, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add, ← BitVec.ofNat_add, BitVec.toNat_ofNat, ← formula_eq g.w bound]
    unfold formula
    split <;> split <;> split <;> split <;> split <;> split <;> omega
  · exact ((Outs.of_outside Ob (by simp [WitnessChecks.ranges])).trans
      (Outs.of_outside Od (by simp [WitnessChecks.ranges]))).trans (Outs.of_outside Ot (by simp [WitnessChecks.ranges]))

theorem available_ok {g : Geometry} (v : g.Valid) {s : State} {remaining used : Nat}
    (S : Scr s g.W g.L) (C : Context g s)
    (length : w32 s.mem g.W 32 = remaining) (consumed : w32 s.mem g.W 152 = used)
    (bound : used ≤ remaining) :
    WP isa (.block available) s fun t =>
      t.cf = some (decide (remaining - used < 8 * g.w)) ∧ t.mem = s.mem ∧ Keeps [.eax, .edx] s t := by
  have head := v.headerFit
  have wb := v.maxWidth
  unfold available
  refine WP.block_append (WP.mono (draw_ok v C) fun a ⟨D, Ma, Ka⟩ => ?_)
  have Sa := S.of_keeps Ka (by decide)
  refine wp_movS (readSrc_sc Sa (d := 32) (by omega)) fun b B _ => ?_
  have Sb := Sa.of_keeps B.keeps (by decide)
  refine wp_subS (readSrc_sc Sb (d := 152) (by omega)) fun d Dd _ => ?_
  refine wp_cmpCarry rfl fun t T carry => WP.block_nil ⟨?_, by rw [T.mem, Dd.mem, B.mem, Ma], ?_⟩
  · have value : (d.gpr .eax).toNat = remaining - used := by
      rw [Dd.gpr, B.gpr, B.mem, Ma, BitVec.toNat_sub_of_le (by
        rw [BitVec.le_def]; change w32 s.mem g.W 152 ≤ w32 s.mem g.W 32; rw [length, consumed]; exact bound)]
      change w32 s.mem g.W 32 - w32 s.mem g.W 152 = _
      rw [length, consumed]
    have edx : d.gpr .edx = BitVec.ofNat 32 (8 * g.w) := by
      rw [Dd.other .edx (by decide), B.other .edx (by decide)]; exact D
    rw [carry, value, edx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · exact ((Ka.mono (by decide)).widen B.keeps).widen Dd.keeps |>.widen (T.keeps [])

theorem advance_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity used : Nat} {p rand : BitVec 32}
    (S : Prepare.Data g c capacity p s)
    (source : s.mem.readW (off g.W 28) 32 = rand)
    (consumed : w32 s.mem g.W 152 = used) (fit : used + 8 * g.w < 2 ^ 32) :
    WP isa (.block advance) s fun t =>
      Prepare.Data g c capacity p t ∧ t.gpr .esi = rand + BitVec.ofNat 32 used ∧
      w32 t.mem g.W 152 = used + 8 * g.w ∧
      Outside g.W 152 4 s.mem t.mem ∧ Keeps [.eax, .esi, .edx] s t := by
  have head := v.headerFit
  unfold advance
  refine WP.block_append (WP.mono (draw_ok v S.ready.context) fun a0 ⟨D, M0, K0⟩ => ?_)
  have S0 := S.ready.scratch.of_keeps K0 (by decide)
  refine wp_movS (readSrc_sc S0 (by omega)) fun a A _ => ?_
  have Sa := S0.of_keeps A.keeps (by decide)
  refine wp_movS (readSrc_sc Sa (d := 152) (by omega)) fun b B _ =>
    wp_addS rfl fun d Dd _ => wp_addS rfl fun e E _ => ?_
  have K : Keeps [.eax, .esi, .edx] s e :=
    ((((K0.mono (by decide)).widen A.keeps).widen B.keeps).widen Dd.keeps).widen E.keeps
  have Se := S.ready.scratch.of_keeps K (by decide)
  refine wp_storeS (Se.ea (by omega)) (Se.write (by omega)) fun t T => WP.block_nil ?_
  have Ot : Outside g.W 152 4 s.mem t.mem := by
    rw [T.mem, E.mem, Dd.mem, B.mem, A.mem, M0]
    exact writeW32_outside _ _ _ (by decide)
  have Kt := K.widen (T.keeps [])
  refine ⟨S.keepGap v (by decide) (by decide) Ot Kt (by decide) (by decide), ?_, ?_, Ot, Kt⟩
  · rw [T.gpr, E.other .esi (by decide), Dd.gpr, B.other .esi (by decide), A.gpr, M0, source,
      B.gpr, A.mem, M0]
    have wordEq : s.mem.readW (off g.W 152) 32 = BitVec.ofNat 32 used := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, ← consumed, Nat.mod_eq_of_lt (by change w32 s.mem g.W 152 < 2 ^ 32; exact (s.mem.readW _ 32).isLt)]
    rw [wordEq]
  · have edxD : d.gpr .edx = BitVec.ofNat 32 (8 * g.w) := by
      rw [Dd.other .edx (by decide), B.other .edx (by decide), A.other .edx (by decide)]; exact D
    rw [T.mem, w32_write_self, E.gpr, Dd.other .eax (by decide), B.gpr, A.mem, M0, edxD,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    change (w32 s.mem g.W 152 + (8 * g.w) % 2 ^ 32) % 2 ^ 32 = _
    rw [consumed, Nat.mod_eq_of_lt (a := 8 * g.w) (by omega), Nat.mod_eq_of_lt fit]

end VG.Proof.RsaKeyGen.X86.WitnessRt
