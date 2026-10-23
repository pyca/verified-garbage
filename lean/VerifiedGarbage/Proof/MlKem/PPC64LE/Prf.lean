module

public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Calls
public import VerifiedGarbage.Proof.MlKem.PPC64LE.KemLay
import VerifiedGarbage.Proof.MlKem.PPC64LE.HashTop
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on PPC64LE: sampling with `PRF` and `SamplePolyCBD`

As on 32-bit ARM (`Proof/MlKem/Arm/Prf.lean`). `K.prfLoop withNtt N₀ N₁`
writes `SamplePolyCBD₂(PRF₂(σ, N))` (its NTT if `withNtt`) to polynomial
`k + N` for `N₀ ≤ N < N₁` (`prfLoop_ok`), with `σ` at offset 952 of
`scratch`, and changes only the regions of `prfW`.
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt squeezeFrom rates)

/-! ## What changes, but for some callee-saved registers -/

/-- `s'` differs from `s` only in memory within `rs`, in registers that are
not callee-saved, and in the callee-saved registers `xs`. -/
structure KeptX (xs : List Reg) (rs : List Region) (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, r ∉ xs → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame rs s.mem s'.mem

theorem Kept.x {rs : List Region} {s s' : State} (h : Kept rs s s') (xs : List Reg) : KeptX xs rs s s' :=
  ⟨fun r hr _ => h.cs r hr, h.sp, h.rd, h.wr, h.frame⟩

theorem KeptX.trans {xs : List Reg} {rs : List Region} {s₁ s₂ s₃ : State} (h₁ : KeptX xs rs s₁ s₂)
    (h₂ : KeptX xs rs s₂ s₃) : KeptX xs rs s₁ s₃ :=
  ⟨fun r hr hx => by rw [h₂.cs r hr hx, h₁.cs r hr hx], by rw [h₂.sp, h₁.sp], by rw [h₂.rd, h₁.rd],
    by rw [h₂.wr, h₁.wr], h₁.frame.trans h₂.frame⟩

theorem KeptX.sub {xs : List Reg} {rs rs' : List Region} {s s' : State} (h : KeptX xs rs s s')
    (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : KeptX xs rs' s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, h.frame.sub hs⟩

theorem KeptX.mono {xs : List Reg} {rs rs' : List Region} {s s' : State} (h : KeptX xs rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs') : KeptX xs rs' s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, h.frame.mono hs⟩

theorem KeptX.weaken {xs ys : List Reg} {rs : List Region} {s s' : State} (h : KeptX xs rs s s')
    (hx : ∀ x ∈ xs, x ∈ ys) : KeptX ys rs s s' :=
  ⟨fun r hr hy => h.cs r hr fun hm => hy (hx r hm), h.sp, h.rd, h.wr, h.frame⟩

theorem KeptX.monoL {L : Lay} {xs : List Reg} {W W' : List (Nat × Nat × Nat)} {s s' : State}
    (h : KeptX xs (L.RL W) s s') (hs : ∀ w ∈ W, w ∈ W') : KeptX xs (L.RL W') s s' :=
  h.mono fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact List.mem_map.mpr ⟨w, hs w hw, rfl⟩

theorem Only.x {s s' : State} (h : Only s s') (xs : List Reg) (rs : List Region) : KeptX xs rs s s' :=
  (h.kept rs).x xs

theorem KeptX.ctx {L : Lay} {xs : List Reg} {rs : List Region} {s s' : State} (h : KeptX xs rs s s')
    (h31 : Reg.r31 ∉ xs) (hc : Ctx L s) : Ctx L s' :=
  ⟨hc.ok, hc.sz0, hc.sz1, hc.len, by rw [h.cs .r31 (by decide) h31, hc.r31], by rw [h.sp]; exact hc.sp48,
    by rw [h.sp]; exact hc.sp, by rw [h.wr]; exact hc.cw⟩

/-- A region of `scratch` apart from the region `w` of `scratch` or of the stack. -/
def sep0 (o l : Nat) (w : Nat × Nat × Nat) : Bool :=
  (w.1 == 0 && decide (w.2.1 + w.2.2 ≤ 32768) && (decide (o + l ≤ w.2.1) || decide (w.2.1 + w.2.2 ≤ o))) ||
    (w.1 == 1 && decide (w.2.1 + w.2.2 ≤ 48))

theorem Ctx.sepAll0 {L : Lay} {s : State} (hc : Ctx L s) {o l : Nat} (hl : o + l ≤ 32768)
    {W : List (Nat × Nat × Nat)} (h : W.all (sep0 o l) = true) : sepAll L.sizes (0, o, l) W = true := by
  refine List.all_eq_true.mpr fun w hw => ?_
  have h' := List.all_eq_true.mp h w hw
  obtain ⟨i, a, b⟩ := w
  simp only [sep0, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h'
  rcases h' with ⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h2⟩
  · subst h1; exact hc.sep00 hl h2 h3
  · subst h1; exact hc.sep01 hl h2

/-- A part of a buffer inside a bigger one. -/
theorem Lay.R_sub_R (L : Lay) {i a l b l' : Nat} (h₁ : b ≤ a) (h₂ : a + l ≤ b + l') :
    Region.Sub (L.R i a l) (L.R i b l') :=
  Offset.sub _ h₁ h₂

/-- A part of `scratch` inside a bigger one. -/
theorem Ctx.sub0 {L : Lay} {s : State} (_hc : Ctx L s) {a l b l' : Nat} (h₁ : b ≤ a) (h₂ : a + l ≤ b + l')
    (_h₃ : b + l' ≤ 32768) : Region.Sub (L.R 0 a l) (L.R 0 b l') :=
  Lay.R_sub_R L h₁ h₂

/-- A separation decided with a `scratch` of 32 KiB holds for a bigger one. -/
theorem sepB_scr {r : List Nat} {s : Nat} {a b : Nat × Nat × Nat} (h : sepB (32768 :: r) a b = true)
    (hs : 32768 ≤ s) : sepB (s :: r) a b = true := by
  obtain ⟨i, o, l⟩ := a
  obtain ⟨j, o', l'⟩ := b
  simp only [sepB, List.length_cons, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨⟨⟨⟨h1, h2⟩, ?_⟩, ?_⟩, h5⟩
  · cases i <;> simp only [List.getD_cons_zero, List.getD_cons_succ] at h3 ⊢ <;> omega
  · cases j <;> simp only [List.getD_cons_zero, List.getD_cons_succ] at h4 ⊢ <;> omega

theorem sepAll_scr {r : List Nat} {s : Nat} {a : Nat × Nat × Nat} {W : List (Nat × Nat × Nat)}
    (h : sepAll (32768 :: r) a W = true) (hs : 32768 ≤ s) : sepAll (s :: r) a W = true :=
  List.all_eq_true.mpr fun w hw => sepB_scr (List.all_eq_true.mp h w hw) hs

/-- `w` inside `w'`, a region of `scratch` or of the stack. -/
def subB0 (w w' : Nat × Nat × Nat) : Bool :=
  w.1 == w'.1 && decide (w'.2.1 ≤ w.2.1) && decide (w.2.1 + w.2.2 ≤ w'.2.1 + w'.2.2) &&
    ((w'.1 == 0 && decide (w'.2.1 + w'.2.2 ≤ 32768)) || (w'.1 == 1 && decide (w'.2.1 + w'.2.2 ≤ 48)))

theorem Ctx.subL {L : Lay} {s : State} (_hc : Ctx L s) {W W' : List (Nat × Nat × Nat)}
    (h : W.all (fun w => W'.any (subB0 w)) = true) : ∀ r ∈ L.RL W, ∃ r' ∈ L.RL W', Region.Sub r r' := by
  intro r hr
  obtain ⟨⟨i, a, l⟩, hw, rfl⟩ := List.mem_map.mp hr
  obtain ⟨⟨i', b, l'⟩, hw', hs⟩ := List.any_eq_true.mp (List.all_eq_true.mp h _ hw)
  simp only [subB0, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨e, h₁⟩, h₂⟩, -⟩ := hs
  subst e
  exact ⟨L.R i b l', List.mem_map.mpr ⟨_, hw', rfl⟩, Lay.R_sub_R L h₁ h₂⟩

theorem KeptX.subL {L : Lay} {xs : List Reg} {W W' : List (Nat × Nat × Nat)} {s₀ s s' : State} (hc : Ctx L s₀)
    (h : KeptX xs (L.RL W) s s') (hb : W.all (fun w => W'.any (subB0 w)) = true) : KeptX xs (L.RL W') s s' :=
  h.sub (hc.subL hb)

/-! ## Addresses -/

/-- `w` inside `w'`. -/
def inB (w w' : Nat × Nat × Nat) : Bool :=
  w.1 == w'.1 && decide (w'.2.1 ≤ w.2.1) && decide (w.2.1 + w.2.2 ≤ w'.2.1 + w'.2.2)

/-- Arithmetic on the offsets in `scratch`, with the bounds on `k` of the
`KemLay.WF` in the context, if any. -/
tactic_template "offs" : tactic => `(tactic| (
                   (try have := (‹KemLay.WF _›).k1)
                   (try have := (‹KemLay.WF _›).k4)
                   (try have := (‹KemLay.WF _›).du)
                   (try have := (‹KemLay.WF _›).dv)
                   (try simp only [oPoly, oPrf, KemLay.oNtt, oSeed, oSigma, KemLay.oAcc, KemLay.oTmp, KemLay.oAhat, KemLay.oSample,
                     oK, oKbar, oMsg, oHek, KemLay.oCt, oWork, oSave, oExtra, oG, oCin, KemLay.ekLen, KemLay.ctLen, KemLay.uLen,
                     KemLay.vLen])
                   omega))

/-- Decides a fact about offsets and regions: by evaluation, or, for one that
depends on the parameter set (of the `KemLay.WF` in the context), by `omega`
on the offsets. -/
tactic_template "kdecide" : tactic => `(tactic| first
                   | decide
                   | (
                   (try have := (‹KemLay.WF _›).k1)
                   (try have := (‹KemLay.WF _›).k4)
                   (try have := (‹KemLay.WF _›).du)
                   (try have := (‹KemLay.WF _›).dv)
                   (try simp only [List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.all_append, List.any_append, sep0,
                     subB0, inB, sepB, sepAll, List.length_cons, List.length_nil, List.getD_cons_zero, List.getD_cons_succ,
                     oPoly, oPrf, KemLay.oNtt, oSeed, oSigma, KemLay.oAcc, KemLay.oTmp, KemLay.oAhat, KemLay.oSample, oK,
                     oKbar, oMsg, oHek, KemLay.oCt, oWork, oSave, oExtra, oG, oCin, KemLay.ekLen, KemLay.ctLen, KemLay.uLen,
                     KemLay.vLen, KemLay.dkLen, Bool.and_true, Bool.or_false,
                     Bool.true_and, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
                     decide_eq_true_eq, true_and, and_true, not_true_eq_false, not_false_eq_true, false_or, or_false, true_or,
                     or_true])
                   omega))

theorem slot_eq (p : BitVec 64) {N off : Nat} (_h : off + 1024 * N < 2 ^ 64) :
    p + BitVec.ofNat 64 N <<< 10 + BitVec.ofNat 64 off = p + BitVec.ofNat 64 (off + 1024 * N) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem setWidth8_ofNat {N : Nat} (h : N < 2 ^ 64) : (BitVec.ofNat 64 N).setWidth 8 = BitVec.ofNat 8 N := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- `a - b` is nonzero exactly when `a ≠ b`. -/
theorem ofNat_sub_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b != 0) = decide (a ≠ b) := by
  by_cases h : a = b
  · subst h; simp
  · have hne : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun e => h (by
      have := congrArg BitVec.toNat e
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this)
    have : BitVec.ofNat 64 a - BitVec.ofNat 64 b ≠ 0 := fun e => hne (by
      have := BitVec.sub_add_cancel (BitVec.ofNat 64 a) (BitVec.ofNat 64 b)
      rw [e] at this; simpa using this.symm)
    rw [bne_iff_ne.mpr this]; simp [h]

/-! ## Counters -/

theorem count_ok {s : State} {c : Reg} {n k : Nat} (hc : c ∈ preserved) (hk : k + 1 < 2 ^ 64)
    (hn : n < 32768) (h : s.gpr c = BitVec.ofNat 64 k) :
    WP isa (.block (count c n)) s fun s' =>
      KeptX [c] [] s s' ∧ s'.gpr c = BitVec.ofNat 64 (k + 1) ∧ (s'.gpr .r0 != 0) = decide (k + 1 ≠ n) := by
  obtain ⟨n0, -⟩ := pres_ne hc
  prun [count, hn, h, n0, Ne.symm n0]
  refine ⟨⟨fun r hr hx => ?_, rfl, rfl, rfl, Frame.refl _ _⟩, by rw [← BitVec.ofNat_add], ?_⟩
  · have hr0 : r ≠ .r0 := (pres_ne hr).1
    have hrc : r ≠ c := fun e => hx (by rw [e]; exact List.mem_singleton_self _)
    simp only [RegUpd.gpr_write_of_ne _ _ hr0, RegUpd.gpr_write_of_ne _ _ hrc]
  · rw [← BitVec.ofNat_add]; exact ofNat_sub_ne hk (by omega)

/-! ## One `PRF` -/

/-- Polynomial `k + N`: `SamplePolyCBD₂(PRF₂(σ, N))`, or its NTT. -/
def prfOut (withNtt : Bool) (σ : List Byte) (N : Nat) : Poly :=
  if withNtt then ntt (VG.Proof.MlKem.cbd σ N) else VG.Proof.MlKem.cbd σ N

/-- What one `PRF` changes. -/
abbrev prfW (K : KemLay) (N : Nat) : List (Nat × Nat × Nat) :=
  [(0, 0, 200), (0, 200, 640), (1, 0, 48), (0, 984, 1), (0, 1056, 128), (0, oPoly (K.k + N), 1024),
    (0, K.oNtt, 1024)]

theorem bytes_one (m : Mem) (p : Addr) : bytesAt m p 1 = [m p] := by
  simp [bytesAt]

theorem stb26_ok {L : Lay} {s : State} (hc : Ctx L s) {N : Nat} (hN : N < 2 ^ 64)
    (h26 : s.gpr .r26 = BitVec.ofNat 64 N) :
    WP isa (.block [.stb .r26 .r31 (oSigma + 32)]) s fun s₁ =>
      KeptX [] (L.RL [(0, 984, 1)]) s s₁ ∧ s₁.mem = s.mem.writeW (L.A 0 984) (BitVec.ofNat 8 N) := by
  have e31 := hc.r31
  have i952 : InRegions s.wr (L.ptr 0 + BitVec.ofNat 64 984) 1 :=
    hc.cs (o := 984) (l := 1) (by decide) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [show oSigma + 32 = 984 from rfl]
  prun [exec_stb, e31, i952, h26, setWidth8_ofNat hN]
  refine ⟨⟨fun _ _ _ => rfl, rfl, rfl, rfl, ?_⟩, rfl⟩
  show Frame [L.R 0 984 1] s.mem (s.mem.writeW (L.ptr 0 + BitVec.ofNat 64 984) (BitVec.ofNat 8 N))
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem rate136 : 136 ∈ rates := by decide

section
variable {K : KemLay} (hK : K.WF)
include hK

theorem cbdArgs_ok {s : State} {P : BitVec 64} {N : Nat} (h31 : s.gpr .r31 = P)
    (h26 : s.gpr .r26 = BitVec.ofNat 64 N) :
    WP isa (.block (.addi .r3 .r31 oPrf :: slotAt .r4 .r26 (oPoly K.k))) s fun s' => Only s s' ∧
      s'.gpr .r3 = P + BitVec.ofNat 64 oPrf ∧
      s'.gpr .r4 = P + BitVec.ofNat 64 N <<< 10 + BitVec.ofNat 64 (oPoly K.k) := by
  have e1 : oPrf < 32768 := by decide
  have e2 : oPoly K.k < 32768 := by offs
  prun [slotAt, e1, e2, h31, h26]
  exact ⟨Only.of_writes rfl rfl rfl rfl (by pres_tac), trivial⟩

theorem nttArgs_ok {s : State} {P : BitVec 64} {N : Nat} (h31 : s.gpr .r31 = P)
    (h26 : s.gpr .r26 = BitVec.ofNat 64 N) :
    WP isa (.block (slotAt .r3 .r26 (oPoly K.k) ++ [.addi .r4 .r31 K.oNtt])) s fun s' => Only s s' ∧
      s'.gpr .r3 = P + BitVec.ofNat 64 N <<< 10 + BitVec.ofNat 64 (oPoly K.k) ∧
      s'.gpr .r4 = P + BitVec.ofNat 64 K.oNtt := by
  have e1 : K.oNtt < 32768 := by offs
  have e2 : oPoly K.k < 32768 := by offs
  prun [slotAt, List.cons_append, List.nil_append, e1, e2, h31, h26]
  exact ⟨Only.of_writes rfl rfl rfl rfl (by pres_tac), trivial⟩

theorem prfBody_ok {L : Lay} {s : State} (hc : Ctx L s) (withNtt : Bool) {N₁ N : Nat} (hN : N < N₁)
    (hN₁ : N₁ ≤ 2 * K.k + 1) (h26 : s.gpr .r26 = BitVec.ofNat 64 N) {σ : List Byte}
    (hσ : bytesAt s.mem (L.A 0 oSigma) 32 = σ) :
    WP isa (K.prfBody withNtt N₁) s fun s' => KeptX [.r26] (L.RL (prfW K N)) s s' ∧
      s'.gpr .r26 = BitVec.ofNat 64 (N + 1) ∧ (s'.gpr .r0 != 0) = decide (N + 1 ≠ N₁) ∧
      PolyIs s'.mem (L.A 0 (oPoly (K.k + N))) (prfOut withNtt σ N) := by
  have hL := hc.ok
  have k4 := hK.k4
  have eo : oPoly (K.k + N) = oPoly K.k + 1024 * N := by unfold oPoly; omega
  refine WP.seq (WP.mono (stb26_ok hc (by omega) h26) fun s₁ ⟨k₁, m₁⟩ => ?_)
  have hc₁ := k₁.ctx (by decide) hc
  have g26₁ : s₁.gpr .r26 = BitVec.ofNat 64 N := by rw [k₁.cs .r26 (by decide) (by decide), h26]
  have bσ : bytesAt s₁.mem (L.A 0 oSigma) 33 = σ ++ [BitVec.ofNat 8 N] := by
    show bytesAt s₁.mem (L.ptr 0 + BitVec.ofNat 64 952) (32 + 1) = _
    rw [bytesAt_add, bytes_one, ptr_add]
    congr 1
    · rw [← hσ]
      exact Lay.bytes_keep hL k₁.frame (hc.sepAll0 (by decide) (by decide)) (by decide)
    · rw [m₁, writeW8_apply, ite_eq_left rfl]
  have hin : ∀ p ∈ [(⟨.r31, oSigma, 33⟩ : Piece)], PieceOk L (fun _ => 0) s₁ false p := by
    intro p hp; rw [List.mem_singleton] at hp; subst hp
    exact ⟨by decide, hc₁.r31, by decide, by decide, by decide, hc₁.sepAll0 (by decide) (by decide),
      mem_rd_wr hc₁.cw⟩
  have hout : ∀ p ∈ [(⟨.r31, oPrf, 128⟩ : Piece)], PieceOk L (fun _ => 0) s₁ true p := by
    intro p hp; rw [List.mem_singleton] at hp; subst hp
    exact ⟨by decide, hc₁.r31, by decide, by decide, by decide, hc₁.sepAll0 (by decide) (by decide), hc₁.cw⟩
  refine WP.seq (WP.mono (hash_ok (idx := fun _ => 0) rate136 (by decide) hc₁
    (List.cons_ne_nil _ _) hin hout (List.pairwise_singleton _ _)) fun s₂ ⟨k₂, o₂⟩ => ?_)
  have hc₂ := hc₁.kept k₂
  have g26₂ : s₂.gpr .r26 = BitVec.ofNat 64 N := by rw [k₂.cs .r26 (by decide), g26₁]
  have prfB : bytesAt s₂.mem (L.A 0 oPrf) 128 = prf 2 σ (BitVec.ofNat 8 N) := by
    have := o₂.1
    simp only [Lay.pb, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at this
    rw [bσ] at this
    rw [this, VG.Proof.MlKem.prf_eq]; rfl
  refine WP.seq (WP.mono (cbdArgs_ok hK hc₂.r31 g26₂) fun s₃ ⟨o₃, g3, g4⟩ => ?_)
  rw [slot_eq _ (by offs), ← eo] at g4
  have hc₃ := hc₂.only o₃
  refine WP.seq (cbd2L hL g3 g4 (hc.sep00 (by offs) (by offs) (by offs))
    (mem_rd_wr hc₃.cw) hc₃.cw fun s₄ k₄ p₄ => ?_)
  rw [o₃.mem, prfB] at p₄
  have hc₄ := hc₃.kept k₄
  have g26₄ : s₄.gpr .r26 = BitVec.ofNat 64 N := by
    rw [k₄.cs .r26 (by decide), o₃.cs .r26 (by decide), g26₂]
  have fin : ∀ s₅, KeptX [.r26] (L.RL [(0, oPoly (K.k + N), 1024), (0, K.oNtt, 1024)]) s₄ s₅ →
      s₅.gpr .r26 = BitVec.ofNat 64 N → PolyIs s₅.mem (L.A 0 (oPoly (K.k + N))) (prfOut withNtt σ N) →
      WP isa (.block (count .r26 N₁)) s₅ fun s' => KeptX [.r26] (L.RL (prfW K N)) s s' ∧
        s'.gpr .r26 = BitVec.ofNat 64 (N + 1) ∧ (s'.gpr .r0 != 0) = decide (N + 1 ≠ N₁) ∧
        PolyIs s'.mem (L.A 0 (oPoly (K.k + N))) (prfOut withNtt σ N) := fun s₅ k₅ g26₅ p₅ =>
    WP.mono (count_ok (by decide) (by omega) (by omega) g26₅) fun s' ⟨k', g', z'⟩ => ⟨by
      exact ((k₁.weaken (by simp)).monoL (W' := prfW K N) (by simp)).trans (((k₂.x _).monoL (by simp)).trans
        ((o₃.x _ _).trans (((k₄.x _).monoL (by simp)).trans ((k₅.monoL (by simp)).trans
          (k'.mono (fun _ h => absurd h List.not_mem_nil)))))),
      g', z', polyIs_frame k'.frame (fun _ h => absurd h List.not_mem_nil) p₅⟩
  cases withNtt
  · refine WP.seq (WP.block_nil ?_)
    exact fin s₄ ((Kept.refl _ _).x _) g26₄ p₄
  · refine WP.seq (WP.seq (WP.mono (nttArgs_ok hK hc₄.r31 g26₄) fun s₅ ⟨o₅, g3', g4'⟩ => ?_))
    rw [slot_eq _ (by offs), ← eo] at g3'
    have hc₅ := hc₄.only o₅
    refine nttL hL g3' g4' (hc.sep00 (by offs) (by offs) (by offs)) hc₅.cw hc₅.cw (by rw [o₅.mem]; exact p₄)
      fun s₆ k₆ p₆ => fin s₆ (((o₅.kept _).trans k₆).x _) ?_ p₆
    rw [k₆.cs .r26 (by decide), o₅.cs .r26 (by decide), g26₄]

end

/-! ## The loop -/

/-- What the loop changes: the regions of `prfW`, with all its polynomials. -/
abbrev prfLW (K : KemLay) (N₀ N₁ : Nat) : List (Nat × Nat × Nat) :=
  [(0, 0, 200), (0, 200, 640), (1, 0, 48), (0, 984, 1), (0, 1056, 128), (0, oPoly (K.k + N₀), 1024 * (N₁ - N₀)),
    (0, K.oNtt, 1024)]

structure PrfInv (K : KemLay) (L : Lay) (withNtt : Bool) (σ : List Byte) (N₀ N₁ : Nat) (s₀ : State) (t : Nat)
    (s : State) : Prop where
  kx : KeptX [.r26] (L.RL (prfLW K N₀ N₁)) s₀ s
  r26 : s.gpr .r26 = BitVec.ofNat 64 (N₀ + t)
  sig : bytesAt s.mem (L.A 0 oSigma) 32 = σ
  slots : ∀ N, N₀ ≤ N → N < N₀ + t → PolyIs s.mem (L.A 0 (oPoly (K.k + N))) (prfOut withNtt σ N)

theorem prfW_sig {K : KemLay} (hK : K.WF) : ∀ N < 2 * K.k + 1, (prfW K N).all (sep0 oSigma 32) = true := by
  have := hK.k4
  intro N hN
  simp only [prfW, List.all_cons, List.all_nil, sep0, oPoly, KemLay.oNtt, oSigma, Bool.and_true, Bool.and_eq_true,
    Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, true_and]
  omega

theorem prfW_slot {K : KemLay} (hK : K.WF) {N N' : Nat} (hN : N < 2 * K.k + 1) (hN' : N' < 2 * K.k + 1)
    (h : N' ≠ N) : (prfW K N).all (sep0 (oPoly (K.k + N')) 1024) = true := by
  have := hK.k4
  simp only [prfW, List.all_cons, List.all_nil, sep0, oPoly, KemLay.oNtt, Bool.and_true, Bool.and_eq_true,
    Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, true_and]
  omega

theorem li26_ok {s : State} {N : Nat} (he : N < 32768) :
    WP isa (.block [.li .r26 N]) s fun s' =>
      KeptX [.r26] [] s s' ∧ s'.gpr .r26 = BitVec.ofNat 64 N ∧ s'.mem = s.mem := by
  prun [he]
  refine ⟨⟨fun r _ hx => ?_, rfl, rfl, rfl, Frame.refl _ _⟩, trivial⟩
  exact RegUpd.gpr_write_of_ne _ _ fun e => hx (by rw [e]; exact List.mem_singleton_self _)

section
variable {K : KemLay} (hK : K.WF)
include hK

theorem prfStep_ok {L : Lay} {s₀ : State} (hc : Ctx L s₀) (withNtt : Bool) {N₀ N₁ : Nat}
    (hN₁ : N₁ ≤ 2 * K.k + 1) {σ : List Byte} {t : Nat} (ht : t < N₁ - N₀) {s : State}
    (h : PrfInv K L withNtt σ N₀ N₁ s₀ t s) :
    WP isa (K.prfBody withNtt N₁) s fun s' =>
      PrfInv K L withNtt σ N₀ N₁ s₀ (t + 1) s' ∧ (s'.gpr .r0 != 0) = decide (t + 1 ≠ N₁ - N₀) := by
  have hL := hc.ok
  have k4 := hK.k4
  have hcs := h.kx.ctx (by decide) hc
  refine WP.mono (prfBody_ok hK hcs withNtt (N := N₀ + t) (by omega) hN₁ h.r26 h.sig) fun s' ⟨k', g', z', p'⟩ =>
    ⟨⟨h.kx.trans (k'.sub fun r hr => ?_), by rw [g', Nat.add_assoc], ?_, fun N h1 h2 => ?_⟩, ?_⟩
  · simp only [Lay.RL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.R 0 0 200, by simp, fun _ h => h⟩
    · exact ⟨L.R 0 200 640, by simp, fun _ h => h⟩
    · exact ⟨L.R 1 0 48, by simp, fun _ h => h⟩
    · exact ⟨L.R 0 984 1, by simp, fun _ h => h⟩
    · exact ⟨L.R 0 1056 128, by simp, fun _ h => h⟩
    · exact ⟨L.R 0 (oPoly (K.k + N₀)) (1024 * (N₁ - N₀)), by simp, hc.sub0 (by offs) (by offs) (by offs)⟩
    · exact ⟨L.R 0 K.oNtt 1024, by simp, fun _ h => h⟩
  · rw [← h.sig]
    exact Lay.bytes_keep hL k'.frame (hc.sepAll0 (by decide) (prfW_sig hK _ (by omega))) (by decide)
  · by_cases e : N = N₀ + t
    · subst e; exact p'
    · exact Lay.polyIs_keep hL k'.frame (hc.sepAll0 (by offs) (prfW_slot hK (by omega) (by omega) e))
        (h.slots N h1 (by omega))
  · rw [z']; simp only [decide_eq_decide]; omega

theorem prfLoop_ok {L : Lay} {s₀ : State} (hc : Ctx L s₀) (withNtt : Bool) {N₀ N₁ : Nat} (h01 : N₀ < N₁)
    (hN₁ : N₁ ≤ 2 * K.k + 1) {σ : List Byte} (hσ : bytesAt s₀.mem (L.A 0 oSigma) 32 = σ) :
    WP isa (K.prfLoop withNtt N₀ N₁) s₀ fun s => KeptX [.r26] (L.RL (prfLW K N₀ N₁)) s₀ s ∧
      ∀ N, N₀ ≤ N → N < N₁ → PolyIs s.mem (L.A 0 (oPoly (K.k + N))) (prfOut withNtt σ N) := by
  have k4 := hK.k4
  refine WP.seq (WP.mono (li26_ok (by omega)) fun s₁ ⟨k₁, g₁, m₁⟩ => ?_)
  exact wp_loop_nz (PrfInv K L withNtt σ N₀ N₁ s₀) (N := N₁ - N₀) (by omega)
    (fun t ht s h => prfStep_ok hK hc withNtt hN₁ ht h)
    (fun s h => ⟨h.kx, fun N h1 h2 => h.slots N h1 (by omega)⟩)
    ⟨k₁.mono (fun _ h => absurd h List.not_mem_nil), by rw [g₁, Nat.add_zero], by rw [m₁]; exact hσ,
      fun N h1 h2 => absurd h2 (by omega)⟩

end

end VG.Proof.MlKem.PPC64LE
