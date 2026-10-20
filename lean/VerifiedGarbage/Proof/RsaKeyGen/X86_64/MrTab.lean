module
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWin

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Copy
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks

/-!
# A candidate on x86-64: Miller–Rabin's table

`tabBuild_ok`: from `b R mod c` in `aXm`, the table `T_j = b^j R mod c`
(`TabOK`) and `y := 1`: `T_1` and `y` from `aXm`, `T_0` from `R mod c`,
then `y := y T_1` into each entry from 2 to 15 (`TabStep`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen

/-- What the table changes. -/
def tabRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w 8, tabBytes w), (slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2)),
    (8 * kV, 8), (8 * kBits, 8)]

/-- `tabRanges`'s ranges, in the header and in the arrays. -/
theorem tabRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [(208, 8), (224, 8)]
    [(8, 16), (2, 1), (3, 1), (6, 1)] (tabRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false,
    tabRanges, Public.aAcc, Public.aTmp, Public.aY, aAcc, aTmp, aY, VG.Proof.Bignum.tabBytes, kT0, sFn, kV, kBits, kT2] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr ⟨(8, 16), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(2, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(3, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(6, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inl (by decide)
  · exact .inl (by decide)

theorem powMod_succ' (b e c : Nat) :
    Spec.Rsa.powMod b (e + 1) c = Spec.Rsa.powMod b e c * Spec.Rsa.powMod b 1 c % c := by
  rw [VG.Proof.Bignum.powMod_eq, VG.Proof.Bignum.powMod_eq, VG.Proof.Bignum.powMod_eq, ← Nat.mul_mod, Nat.pow_succ,
    Nat.pow_one]

theorem tab_end (w : Nat) : slot w 8 + tabBytes w = slot w aE := by
  rw [show aE = 8 + 16 from rfl, slot_add_mul]; rfl

theorem tabRanges_lt (w : Nat) : ∀ r ∈ tabRanges w, r.1 + r.2 ≤ slot w aE := by
  have h0 := tab_end w
  have h8 := slot_mono w (show 8 ≤ aE by decide)
  have h1 := slot_le (w := w) (show aAcc < 8 by decide)
  have h2 := slot_le (w := w) (show aTmp < 8 by decide)
  have h3 := slot_le (w := w) (show aY < 8 by decide)
  have h4 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  simp only [tabRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [kV, kT0, kBits, kT2, sFn] at * <;> omega_arith

/-- `MrCtx` with a new witness in `aB`, after changes to the table and the
working arrays. -/
theorem MrCtx.of_tab {s t : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm bm' : Nat}
    (hc : MrCtx s B Z w mi c bm) (hd : MrDims B Z w) (hf : Frm B (tabRanges w) s.mem t.mem) (hs : Scr t B Z)
    (hdi : t.gpr .rdi = B) (hb : wv t.mem B (slot w aB) w = bm') : MrCtx t B Z w mi c bm' := by
  have hn := hc.good.scr.nowrap
  have hx := hd.x
  have hE1 := slot_mono w (show aE ≤ aR1 by decide)
  have h1 := slot_succ w aR1
  have hRm := slot_mono w (show aE ≤ aRm1 by decide)
  have hN := slot_le (w := w) (show aN < 8 by decide)
  have h8R := slot_mono w (show 8 ≤ aRm1 by decide)
  have h1R := slot_mono w (show aR1 ≤ aRm1 by decide)
  have hdN : ∀ r ∈ tabRanges w, slot w aN + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aN := by
    simp only [tabRanges]; rng_disj
  have hlt := tabRanges_lt w
  refine ⟨⟨hs, hdi, Hdr.of_frm hc.good.hdr hf (by simp only [tabRanges]; rng_le)⟩, ?_, ?_, hb, ?_, ?_⟩
  · rw [hf.word_eq (d := slot w aN) (fun r hr => by have := hdN r hr; have := hd.w4; omega_arith) (by omega_arith)]; exact hc.inv
  · rw [hf.wv_eq hdN (by omega_arith)]; exact hc.n
  · rw [hf.wv_eq (d := slot w aR1) (fun r hr => Or.inr (by have := hlt r hr; omega_arith)) (by omega_arith)]
    exact hc.r1
  · rw [hf.wv_eq (d := slot w aRm1) (fun r hr => Or.inr (by have := hlt r hr; omega_arith)) (by omega_arith)]
    exact hc.rm1

/-- `[d] := [a]` for two of the eight arrays. -/
theorem copyArr_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {a d : Nat} (ha : a < 8) (hd : d < 8) (had : a ≠ d) :
    WP isa (seqs [.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr a))), .mov .rbx (.mem (hdr (sArr d)))],
      copyWords]) s fun t => wv t.mem B (slot w d) w = wv s.mem B (slot w a) w ∧
      Outside B (slot w d) (8 * w) s.mem t.mem ∧ Keep [.rax, .rbx, .rsi, .r12, .r14] s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  have sA := slot_le (w := w) ha
  have sD := slot_le (w := w) hd
  have hsep := slot_sep (w := w) had
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r12, .rsi, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rsi = off B (slot w a) ∧ t.gpr .rbx = off B (slot w d) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr a) (by unfold sArr; omega_arith),
      hl (sArr d) (by unfold sArr; omega_arith), hg.hdr.hw, hg.hdr.harr a ha, hg.hdr.harr d hd]) rfl)
    fun s₁ ⟨⟨h12, hsi, hbx, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (copyB_ok (hg.scr.congr k₁.2.2) hsi hbx h12 hw hw' (by omega_arith) (by omega_arith) (by omega_arith))
    fun t ⟨hv, ho, k⟩ => ⟨by rw [hv, hm₁], by rw [hm₁] at ho; exact ho, (k₁.trans k).mono (by decide)⟩

/-- `[aT0] := [aR1]`, between two extra arrays. -/
theorem copyT0_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi)
    (hd : MrDims B Z w) :
    WP isa (seqs [.block (([.mov .r12 (.mem (hdr sW))] : List Instr) ++ extBase aR1 .rsi ++ extBase aT0 .rbx),
      copyWords]) s fun t => wv t.mem B (slot w aT0) w = wv s.mem B (slot w aR1) w ∧
      Outside B (slot w aT0) (8 * w) s.mem t.mem ∧ Keep [.rax, .rbx, .rsi, .r12, .r14] s t := by
  have hn := hg.scr.nowrap
  have hZ := hd.z
  have hw' : w < 2 ^ 31 := by have := hd.w128; omega_arith
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  have h1 := slot_succ w aR1
  have h0R := slot_mono w (show aT0 + 1 ≤ aR1 by decide)
  have h0s := slot_succ w aT0
  have hRm := slot_mono w (show aR1 + 1 ≤ aRm1 by decide)
  have hx := hd.x
  simp only [seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hg.hdr.hw]) rfl) fun s₁ ⟨⟨h12, hm₁⟩, k₁⟩ => ?_
  have hg₁ : Good s₁ B Z w mi := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, by rw [hm₁]; exact hg.hdr⟩
  refine WP.mono (extBase_ok hg₁ hZ hw' (j := aR1) (by decide) (r := .rsi) (by decide) rfl rfl)
    fun s₂ ⟨hsi, hm₂, k₂⟩ => ?_
  have hg₂ : Good s₂ B Z w mi := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, by rw [hm₂]; exact hg₁.hdr⟩
  refine WP.mono (extBase_ok hg₂ hZ hw' (j := aT0) (by decide) (r := .rbx) (by decide) rfl rfl)
    fun s₃ ⟨hbx, hm₃, k₃⟩ => ?_
  refine WP.mono (copyB_ok (hg₂.scr.congr k₃.2.2) ((k₃.gpr (by decide)).trans hsi) hbx
    ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12)) (by have := hd.w4; omega_arith) hw' (by omega_arith) (by omega_arith)
    (Or.inl (by omega_arith))) fun t ⟨hv, ho, k⟩ => ⟨by rw [hv, hm₃, hm₂, hm₁], by rw [hm₃, hm₂, hm₁] at ho; exact ho,
      (((k₁.trans k₂).trans k₃).trans k).mono (by decide)⟩

/-- After `i` entries of the table's loop, from `s₀`: entries `0` to `i + 1`,
`y = T_(i+1)`, the entry `i + 2` in `kV`, `14 − i` in `kBits`. -/
structure TabI (B : Addr) (Z w : Nat) (mi : BitVec 64) (c bm b : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  ctx : MrCtx s B Z w mi c bm
  ent : ∀ e < i + 2, wv s.mem B (slot w (8 + e)) w = Spec.Rsa.powMod b e c * 2 ^ (64 * w) % c
  y : wv s.mem B (slot w aY) w = Spec.Rsa.powMod b (i + 1) c * 2 ^ (64 * w) % c
  xm : wv s.mem B (slot w aXm) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c
  v : word s.mem B (8 * kV) = off B (slot w (8 + (i + 2)))
  bits : word s.mem B (8 * kBits) = BitVec.ofNat 64 (14 - i)
  frm : Frm B (tabRanges w) s₀.mem s.mem
  keep : Keep mmRegs s₀ s

theorem tabStep_eq (mul : Nat → Nat → Nat → Prog isa) : seqs [mul aY aY aXm,
    .block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aY))), .mov .rbx (.mem (hdr kV))], copyWords,
    .block [.mov .rax (.mem (hdr kV)), .mov .rdx (.mem (hdr sW)), .alu .add .rdx (.imm 2), .alu .add .rdx (.reg .rdx),
      .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rax (.reg .rdx), .store (hdr kV) .rax,
      .mov .rax (.mem (hdr kBits)), .alu .sub .rax (.imm 1), .store (hdr kBits) .rax]] =
    .seq (mul aY aY aXm) (.seq (.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aY))),
      .mov .rbx (.mem (hdr kV))]) (.seq copyWords (.block [.mov .rax (.mem (hdr kV)), .mov .rdx (.mem (hdr sW)),
      .alu .add .rdx (.imm 2), .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx),
      .alu .add .rax (.reg .rdx), .store (hdr kV) .rax, .mov .rax (.mem (hdr kBits)), .alu .sub .rax (.imm 1),
      .store (hdr kBits) .rax]))) := rfl

theorem tabRanges_hdr (w : Nat) {i : Nat} (hi : i = kV ∨ i = kBits) : (8 * i, 8) ∈ tabRanges w := by
  rcases hi with rfl | rfl <;> simp [tabRanges]

theorem ent_in_tab (w : Nat) {e : Nat} (he : e < 16) :
    slot w 8 ≤ slot w (8 + e) ∧ slot w (8 + e) + 8 * (w + 2) ≤ slot w 8 + tabBytes w :=
  ⟨slot_mono w (by omega_arith), ent_le w he⟩

/-- One entry of the table. -/
theorem tabStep_ok (M : Mont) {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm b : Nat} {s₀ s : State}
    (hd : MrDims B Z w) (hodd : c % 2 = 1) (hc1 : 1 < c) {i : Nat} (hi : i < 14)
    (hI : TabI B Z w mi c bm b s₀ i s) :
    WP isa (seqs [M.mm aY aY aXm,
      .block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aY))), .mov .rbx (.mem (hdr kV))], copyWords,
      .block [.mov .rax (.mem (hdr kV)), .mov .rdx (.mem (hdr sW)), .alu .add .rdx (.imm 2), .alu .add .rdx (.reg .rdx),
        .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rax (.reg .rdx), .store (hdr kV) .rax,
        .mov .rax (.mem (hdr kBits)), .alu .sub .rax (.imm 1), .store (hdr kBits) .rax]]) s fun t =>
      t.zf = some (decide (i + 1 = 14)) ∧ TabI B Z w mi c bm b s₀ (i + 1) t := by
  have hg := hI.ctx.good
  have hZ := hd.z
  have hx := hd.x
  have hw4 := hd.w4
  have hw' : w < 2 ^ 31 := by have := hd.w128; omega_arith
  have hn := hg.scr.nowrap
  have hR : Nat.Coprime (2 ^ (64 * w)) c := VG.Proof.Bignum.coprime_pow2 hodd _
  have hc0 : 0 < c := by omega_arith
  have hTZ : slot w 8 + tabBytes w ≤ Z := by
    rw [tab_end]; have := slot_mono w (show aE + 1 ≤ aRm1 by decide); rw [slot_succ] at this; omega_arith
  have hT8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hY8 := slot_le (w := w) (show aY < 8 by decide)
  have hX8 := slot_le (w := w) (show aXm < 8 by decide)
  rw [tabStep_eq]
  -- `y := y T_1`.
  refine WP.seq (WP.mono (M.mm_ok hg hZ (by omega_arith) hw' (o := aY) (a := aY) (b := aXm) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hI.ctx.inv
    (by rw [hI.xm, hI.ctx.n]; exact Nat.mod_lt _ hc0)) fun s₁ ⟨hg₁, hlt₁, hy₁, ha₁, k₁⟩ => ?_)
  rw [hI.ctx.n] at hlt₁ hy₁
  rw [hI.y, hI.xm] at hy₁
  have hY₁ : wv s₁.mem B (slot w aY) w = Spec.Rsa.powMod b (i + 2) c * 2 ^ (64 * w) % c := by
    rw [mont_val hR hlt₁ hy₁ rfl rfl, ← powMod_succ']
  have hf₁ : Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2))] s.mem s₁.mem :=
    Frm.of_arrays ha₁ (by simp)
  have hc₁ : MrCtx s₁ B Z w mi c bm := hI.ctx.of_frm hd hf₁ hg₁.scr hg₁.rdi (VG.Proof.RsaKeyGen.HdrShapeC.geD rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
  have hlo : ∀ e < 16, ∀ m m' : Mem, Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)),
      (slot w aY, 8 * (w + 2))] m m' → wv m' B (slot w (8 + e)) w = wv m B (slot w (8 + e)) w := fun e he m m' hf => by
    have := ent_in_tab w he
    exact hf.wv_eq (fun r hr => by
      have h1 := slot_le (w := w) (show aAcc < 8 by decide)
      have h2 := slot_le (w := w) (show aTmp < 8 by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> right <;> simp only <;> omega_arith) (by omega_arith)
  -- The entry's base and `y`.
  have hl : ∀ (t : State), Scr t B Z → ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun t hs i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  have hst : ∀ (t : State), Scr t B Z → ∀ i < 32, InRegions t.wr (off B (8 * i)) 8 := fun t hs i hi =>
    hs.st (by have := hdr_lt_slot w 8 hi; omega_arith)
  have hV₁ : word s₁.mem B (8 * kV) = off B (slot w (8 + (i + 2))) := by
    rw [hf₁.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by unfold kV kT0 sFn; omega_arith)]; exact hI.v
  refine WP.seq (WP.mono (WP.keep [.r12, .rsi, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rsi = off B (slot w aY) ∧ t.gpr .rbx = off B (slot w (8 + (i + 2))) ∧ t.mem = s₁.mem) (by
    xrun [State.ea, hdr, hg₁.rdi, hdrOff, hl s₁ hg₁.scr sW (by decide), hl s₁ hg₁.scr (sArr aY) (by decide),
      hl s₁ hg₁.scr kV (by decide), hg₁.hdr.hw, hg₁.hdr.harr aY (by decide), hV₁]) rfl)
    fun s₂ ⟨⟨h12, hsi, hbx, hm₂⟩, k₂⟩ => ?_)
  have hE := ent_in_tab w (e := i + 2) (by omega_arith)
  refine WP.seq (WP.mono (copyB_ok (hg₁.scr.congr k₂.2.2) hsi hbx h12 (by omega_arith) hw' (by omega_arith)
    (by omega_arith) (Or.inr (by omega_arith))) fun s₃ ⟨hv₃, ho₃, k₃⟩ => ?_)
  rw [hm₂] at hv₃ ho₃
  have hf₃ : Frm B [(slot w 8, tabBytes w)] s₁.mem s₃.mem :=
    Frm.of_outside (ho₃.mono (o' := slot w 8) (n' := tabBytes w) hE.1 (by omega_arith)) (by simp)
  have hg₃ : Good s₃ B Z w mi := ⟨(hg₁.scr.congr k₂.2.2).congr k₃.2.2,
    (k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hg₁.rdi), Hdr.of_frm hg₁.hdr hf₃ (by simp; omega_arith)⟩
  -- `kV` and `kBits`.
  have hV₃ : word s₃.mem B (8 * kV) = off B (slot w (8 + (i + 2))) := by
    rw [ho₃.word (Or.inl (by have := hdr_lt_slot w (8 + (i + 2)) (show kV < 32 by decide); omega_arith))
      (by unfold kV kT0 sFn; omega_arith), hV₁]
  have hB₃ : word s₃.mem B (8 * kBits) = BitVec.ofNat 64 (14 - i) := by
    rw [ho₃.word (Or.inl (by have := hdr_lt_slot w (8 + (i + 2)) (show kBits < 32 by decide); omega_arith))
      (by unfold kBits kT2 sFn; omega_arith), hf₁.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by unfold kBits kT2 sFn; omega_arith)]
    exact hI.bits
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.mem = (s₃.mem.writeW (off B (8 * kV))
      (off B (slot w (8 + (i + 2)) + 8 * (w + 2)))).writeW (off B (8 * kBits)) (BitVec.ofNat 64 (14 - i - 1)) ∧
      t.zf = some (decide (14 - i - 1 = 0))) (by
    xrun [State.ea, hdr, hg₃.rdi, hdrOff, hl s₃ hg₃.scr kV (by decide), hl s₃ hg₃.scr sW (by decide),
      hl s₃ hg₃.scr kBits (by decide), hst s₃ hg₃.scr kV (by decide), hst s₃ hg₃.scr kBits (by decide), hV₃,
      hg₃.hdr.hw, entStep,
      fun X => (hdrStore_hdr s₃.mem B X (show kV < 32 by decide) (show kBits < 32 by decide) (by decide)).trans hB₃,
      ofNat64_pred (show 1 ≤ 14 - i by omega_arith) (by omega_arith),
      ofNat64_beq_zero (show 14 - i - 1 < 2 ^ 64 by omega_arith)]) rfl) fun t ⟨⟨hm, hz⟩, k⟩ => ⟨?_, ?_⟩
  · rw [hz]; exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  have hft : Frm B (tabRanges w) s₃.mem t.mem := by
    rw [hm]
    exact (Frm.of_outside (writeW_outside _ B _ (d := 8 * kV) (by unfold kV kT0 sFn; omega_arith))
      (tabRanges_hdr w (Or.inl rfl))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kBits)
        (by unfold kBits kT2 sFn; omega_arith)) (tabRanges_hdr w (Or.inr rfl)))
  have hf1t : Frm B (tabRanges w) s.mem t.mem :=
    ((hf₁.mono (by simp [tabRanges])).trans (hf₃.mono (by simp [tabRanges]))).trans hft
  have hgt : Good t B Z w mi := ⟨hg₃.scr.congr k.2.2, (k.gpr (by decide)).trans hg₃.rdi,
    Hdr.of_frm hg₃.hdr hft (by simp only [tabRanges]; rng_le)⟩
  -- The arrays through the header writes.
  have hwv : ∀ j ≤ 24, wv t.mem B (slot w j) w = wv s₃.mem B (slot w j) w := fun j hj => by
    have := slot_lt24 w hj
    have h1 := hdr_lt_slot w j (show kV < 32 by decide)
    have h2 := hdr_lt_slot w j (show kBits < 32 by decide)
    rw [hm, (writeW_outside _ B _ (d := 8 * kBits) (by unfold kBits kT2 sFn; omega_arith)).wv (Or.inr h2)
      (by omega_arith), (writeW_outside _ B _ (d := 8 * kV) (by unfold kV kT0 sFn; omega_arith)).wv (Or.inr h1)
      (by omega_arith)]
  -- What the copy keeps: the arrays other than entry `i + 2`.
  have hcp : ∀ j ≤ 24, j ≠ 8 + (i + 2) → wv s₃.mem B (slot w j) w = wv s₁.mem B (slot w j) w := fun j hj hne => by
    have := slot_lt24 w hj
    rcases slot_sep (w := w) hne with h | h
    · exact ho₃.wv (Or.inl (by omega_arith)) (by omega_arith)
    · exact ho₃.wv (Or.inr (by omega_arith)) (by omega_arith)
  have hBt : wv t.mem B (slot w aB) w = wv s.mem B (slot w aB) w := by
    rw [hwv aB (by decide), hcp aB (by decide) (by show 9 ≠ 8 + (i + 2); omega_arith)]
    exact hlo 1 (by decide) s.mem s₁.mem hf₁
  refine ⟨hI.ctx.of_tab hd hf1t hgt.scr hgt.rdi (hBt.trans hI.ctx.b), fun e he => ?_, ?_, ?_, ?_, ?_,
    hI.frm.trans hf1t, (((hI.keep.trans k₁).trans k₂).trans (k₃.trans k)).mono (by decide)⟩
  · rw [hwv (8 + e) (by omega_arith)]
    by_cases hei : e = i + 2
    · subst hei; rw [hv₃, hY₁]
    · rw [hcp (8 + e) (by omega_arith) (by omega_arith), hlo e (by omega_arith) s.mem s₁.mem hf₁]
      exact hI.ent e (by omega_arith)
  · rw [hwv aY (by decide), hcp aY (by decide) (by unfold aY; omega_arith), hY₁]
  · rw [hwv aXm (by decide), hcp aXm (by decide) (by unfold aXm; omega_arith),
      hf₁.wv_eq (d := slot w aXm) (k := w) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (by omega_arith)]
    exact hI.xm
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self, ← slot_succ,
      show 8 + (i + 2) + 1 = 8 + (i + 1 + 2) by omega_arith]
  · rw [hm, word_writeW_self, show 14 - i - 1 = 14 - (i + 1) by omega_arith]

/-- The bases of the table's start, and the entry pointer and the count. -/
theorem tabBases_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi) (hd : MrDims B Z w) :
    WP isa (.block (([.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aXm))), .mov .r10 (.mem (hdr (sArr aY)))] :
      List Instr) ++ extBase aB .r9 ++ extBase aR1 .r11 ++ extBase aT0 .r13 ++ extBase (aT0 + 2) .rcx ++
      ([.store (hdr kV) .rcx, .mov32 .rax (.imm 14), .store (hdr kBits) .rax] : List Instr))) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r8 = off B (slot w aXm) ∧ t.gpr .r10 = off B (slot w aY) ∧
      t.gpr .r9 = off B (slot w aB) ∧ t.gpr .r11 = off B (slot w aR1) ∧ t.gpr .r13 = off B (slot w aT0) ∧
      t.mem = (s.mem.writeW (off B (8 * kV)) (off B (slot w (8 + (0 + 2))))).writeW (off B (8 * kBits))
        (BitVec.ofNat 64 (14 - 0)) ∧ Keep [.rax, .rcx, .r8, .r9, .r10, .r11, .r12, .r13] s t := by
  have hn := hg.scr.nowrap
  have hZ := hd.z
  have hw' : w < 2 ^ 31 := by have := hd.w128; omega_arith
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r12, .r8, .r10] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r8 = off B (slot w aXm) ∧ t.gpr .r10 = off B (slot w aY) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aXm) (by decide), hl (sArr aY) (by decide),
      hg.hdr.hw, hg.hdr.harr aXm (by decide), hg.hdr.harr aY (by decide)]) rfl) fun s₁ ⟨⟨h12, h8, h10, hm₁⟩, k₁⟩ => ?_
  have hg₁ : Good s₁ B Z w mi := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, by rw [hm₁]; exact hg.hdr⟩
  refine WP.mono (extBase_ok hg₁ hZ hw' (j := aB) (by decide) (r := .r9) (by decide) rfl rfl) fun s₂ ⟨h9, hm₂, k₂⟩ => ?_
  have hg₂ : Good s₂ B Z w mi := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, by rw [hm₂]; exact hg₁.hdr⟩
  refine WP.mono (extBase_ok hg₂ hZ hw' (j := aR1) (by decide) (r := .r11) (by decide) rfl rfl)
    fun s₃ ⟨h11, hm₃, k₃⟩ => ?_
  have hg₃ : Good s₃ B Z w mi := ⟨hg₂.scr.congr k₃.2.2, (k₃.gpr (by decide)).trans hg₂.rdi, by rw [hm₃]; exact hg₂.hdr⟩
  refine WP.mono (extBase_ok hg₃ hZ hw' (j := aT0) (by decide) (r := .r13) (by decide) rfl rfl)
    fun s₄ ⟨h13, hm₄, k₄⟩ => ?_
  have hg₄ : Good s₄ B Z w mi := ⟨hg₃.scr.congr k₄.2.2, (k₄.gpr (by decide)).trans hg₃.rdi, by rw [hm₄]; exact hg₃.hdr⟩
  refine WP.mono (extBase_ok hg₄ hZ hw' (j := aT0 + 2) (by decide) (r := .rcx) (by decide) rfl rfl)
    fun s₅ ⟨hcx, hm₅, k₅⟩ => ?_
  have hst : ∀ i < 32, InRegions s₅.wr (off B (8 * i)) 8 := fun i hi => by
    rw [k₅.2.2, k₄.2.2, k₃.2.2, k₂.2.2, k₁.2.2]; exact hg.scr.st (by have := hdr_lt_slot w 8 hi; omega_arith)
  have hdi₅ : s₅.gpr .rdi = B := (k₅.gpr (by decide)).trans hg₄.rdi
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = (s.mem.writeW (off B (8 * kV))
      (off B (slot w (8 + (0 + 2))))).writeW (off B (8 * kBits)) (BitVec.ofNat 64 (14 - 0))) (by
    xrun [State.ea, hdr, hdi₅, hdrOff, hst kV (by decide), hst kBits (by decide), hcx, hm₅, hm₄, hm₃, hm₂, hm₁]
    rfl) rfl) fun t ⟨hm, k⟩ => ?_
  have kA := (((k₁.trans k₂).trans k₃).trans k₄).trans k₅
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hm, (kA.trans k).mono (by decide)⟩
  · rw [k.gpr (by decide), k₅.gpr (by decide), k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide)]; exact h12
  · rw [k.gpr (by decide), k₅.gpr (by decide), k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide)]; exact h8
  · rw [k.gpr (by decide), k₅.gpr (by decide), k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide)]; exact h10
  · rw [k.gpr (by decide), k₅.gpr (by decide), k₄.gpr (by decide), k₃.gpr (by decide)]; exact h9
  · rw [k.gpr (by decide), k₅.gpr (by decide), k₄.gpr (by decide)]; exact h11
  · rw [k.gpr (by decide), k₅.gpr (by decide)]; exact h13

/-- `[d] := [a]` for bases already in `rsi` and `rbx`. -/
theorem copyRegs_ok {s : State} {B : Addr} {Z w eS eD : Nat} {rS rD : Reg} (hs : Scr s B Z) (hS : s.gpr rS = off B eS)
    (hD : s.gpr rD = off B eD) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hSZ : eS + 8 * w ≤ Z) (hDZ : eD + 8 * w ≤ Z) (hsep : eD + 8 * w ≤ eS ∨ eS + 8 * w ≤ eD)
    (hne : rD ≠ .rsi := by decide) :
    WP isa (seqs [.block [.mov .rsi (.reg rS), .mov .rbx (.reg rD)], copyWords]) s fun t =>
      wv t.mem B eD w = wv s.mem B eS w ∧ Outside B eD (8 * w) s.mem t.mem ∧ Keep [.rax, .rbx, .rsi, .r14] s t := by
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rsi, .rbx] (Q := fun t => t.gpr .rsi = off B eS ∧ t.gpr .rbx = off B eD ∧
      t.mem = s.mem) (by xrun [hS, hD, hne]) rfl) fun s₁ ⟨⟨hsi, hbx, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (copyB_ok (hs.congr k₁.2.2) hsi hbx ((k₁.gpr (by decide)).trans h12) hw hw' hSZ hDZ hsep)
    fun t ⟨hv, ho, k⟩ => ⟨by rw [hv, hm₁], by rw [← hm₁]; exact ho, (k₁.trans k).mono (by decide)⟩

/-- The table's start: `TabI` at the start of its loop. -/
theorem tabHead_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm b : Nat}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm) (hc1 : 1 < c)
    (hX : wv s.mem B (slot w aXm) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c) :
    WP isa (seqs tabHead) s fun t =>
      TabI B Z w mi c (Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c) b t 0 t ∧ Frm B (tabRanges w) s.mem t.mem ∧
      Keep mmRegs s t := by
  have hg := hc.good
  have hZ := hd.z
  have hx := hd.x
  have hw4 := hd.w4
  have hw' : w < 2 ^ 31 := by have := hd.w128; omega_arith
  have hn := hg.scr.nowrap
  have hY8 := slot_le (w := w) (show aY < 8 by decide)
  have hX8 := slot_le (w := w) (show aXm < 8 by decide)
  have hB := ent_in_tab w (e := 1) (by decide)
  have hR1 := slot_mono w (show aR1 + 1 ≤ aRm1 by decide)
  have hR1s := slot_succ w aR1
  have hER := slot_mono w (show aE ≤ aR1 by decide)
  have hte := tab_end w
  have hBs : slot w aB = slot w 8 + 8 * (w + 2) := slot_succ w 8
  have hT0s : slot w aT0 = slot w 8 := rfl
  have htb : tabBytes w = 128 * (w + 2) := by unfold tabBytes; omega_arith
  unfold tabHead
  simp only [seqs]
  refine WP.seq (WP.mono (tabBases_ok hg hd) fun s₁ ⟨h12, h8, h10, h9, h11, h13, hm₁, k₁⟩ => ?_)
  have hf₁ : Frm B (tabRanges w) s.mem s₁.mem := by
    rw [hm₁]
    exact (Frm.of_outside (writeW_outside _ B _ (d := 8 * kV) (by unfold kV kT0 sFn; omega_arith))
      (tabRanges_hdr w (Or.inl rfl))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kBits)
        (by unfold kBits kT2 sFn; omega_arith)) (tabRanges_hdr w (Or.inr rfl)))
  have hs₁ := hg.scr.congr k₁.2.2
  have hwv1 : ∀ j ≤ 26, wv s₁.mem B (slot w j) w = wv s.mem B (slot w j) w := fun j hj => by
    have := slot_lt27 w (show j ≤ 27 by omega_arith)
    have h1 := hdr_lt_slot w j (show kV < 32 by decide)
    have h2 := hdr_lt_slot w j (show kBits < 32 by decide)
    rw [hm₁, (writeW_outside _ B _ (d := 8 * kBits) (by unfold kBits kT2 sFn; omega_arith)).wv (Or.inr h2)
      (by omega_arith), (writeW_outside _ B _ (d := 8 * kV) (by unfold kV kT0 sFn; omega_arith)).wv (Or.inr h1)
      (by omega_arith)]
  -- `T_1 := b R mod c`.
  refine WP.seq (WP.mono (copyRegs_ok hs₁ h8 h9 h12 (by omega_arith) hw' (by omega_arith) (by omega_arith)
    (Or.inr (by omega_arith))) fun s₂ ⟨hv₂, ho₂, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.2.2
  -- `y := T_1`.
  refine WP.seq (WP.mono (copyRegs_ok hs₂ ((k₂.gpr (by decide)).trans h8) ((k₂.gpr (by decide)).trans h10)
    ((k₂.gpr (by decide)).trans h12) (by omega_arith) hw' (by omega_arith) (by omega_arith)
    (by rcases slot_sep (w := w) (show aY ≠ aXm by decide) with h | h
        exacts [Or.inl (by omega_arith), Or.inr (by omega_arith)])) fun s₃ ⟨hv₃, ho₃, k₃⟩ => ?_)
  have hs₃ := hs₂.congr k₃.2.2
  -- `T_0 := R mod c`.
  refine WP.mono (copyRegs_ok hs₃ ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h11))
    ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h13)) ((k₃.gpr (by decide)).trans
    ((k₂.gpr (by decide)).trans h12)) (by omega_arith) hw' (by omega_arith) (by omega_arith) (Or.inl (by omega_arith)))
    fun t ⟨hv, ho, k⟩ => ?_
  have hf : Frm B (tabRanges w) s.mem t.mem := by
    refine hf₁.trans (((Frm.of_outside (ho₂.mono (o' := slot w 8) (n' := tabBytes w) hB.1 (by omega_arith))
      (by simp [tabRanges])).trans (Frm.of_outside (ho₃.mono (o' := slot w aY) (n' := 8 * (w + 2)) (Nat.le_refl _)
        (by omega_arith)) (by simp [tabRanges]))).trans (Frm.of_outside (ho.mono (o' := slot w 8) (n' := tabBytes w)
          (by omega_arith) (by omega_arith)) (by simp [tabRanges])))
  have hgt : Good t B Z w mi := ⟨hs₃.congr k.2.2, (k.gpr (by decide)).trans ((k₃.gpr (by decide)).trans
    ((k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi))), Hdr.of_frm hg.hdr hf (by simp only [tabRanges]; rng_le)⟩
  have hXt : wv t.mem B (slot w aXm) w = wv s.mem B (slot w aXm) w := by
    rw [ho.wv (Or.inl (by omega_arith)) (by omega_arith),
      ho₃.wv (by rcases slot_sep (w := w) (show aY ≠ aXm by decide) with h | h
                 exacts [Or.inr (by omega_arith), Or.inl (by omega_arith)]) (by omega_arith),
      ho₂.wv (Or.inl (by omega_arith)) (by omega_arith), hwv1 aXm (by decide)]
  have hBt : wv t.mem B (slot w aB) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c := by
    rw [ho.wv (Or.inr (by omega_arith)) (by omega_arith), ho₃.wv (Or.inr (by omega_arith)) (by omega_arith), hv₂,
      hwv1 aXm (by decide), hX]
  refine ⟨⟨hc.of_tab hd hf hgt.scr hgt.rdi hBt, fun e he => ?_, ?_, ?_, ?_, ?_, Frm.refl _ _ _, Keep.refl _ _⟩, hf,
    ((k₁.trans k₂).trans (k₃.trans k)).mono (by decide)⟩
  · rcases (by omega_arith : e = 0 ∨ e = 1) with rfl | rfl
    · rw [show 8 + 0 = aT0 from rfl, hv, ho₃.wv (Or.inr (by omega_arith)) (by omega_arith),
        ho₂.wv (Or.inr (by omega_arith)) (by omega_arith), hwv1 aR1 (by decide), hc.r1, powMod_zero' hc1, Nat.one_mul]
    · exact hBt
  · rw [ho.wv (Or.inl (by omega_arith)) (by omega_arith), hv₃, ho₂.wv (Or.inl (by omega_arith)) (by omega_arith),
      hwv1 aXm (by decide), hX]
  · rw [hXt, hX]
  all_goals
    have a1 := hdr_lt_slot w aT0 (show kV < 32 by decide)
    have a2 := hdr_lt_slot w aY (show kV < 32 by decide)
    have a3 := hdr_lt_slot w aB (show kV < 32 by decide)
    have b1 := hdr_lt_slot w aT0 (show kBits < 32 by decide)
    have b2 := hdr_lt_slot w aY (show kBits < 32 by decide)
    have b3 := hdr_lt_slot w aB (show kBits < 32 by decide)
  · rw [ho.word (Or.inl a1) (by unfold kV kT0 sFn; omega_arith), ho₃.word (Or.inl a2) (by unfold kV kT0 sFn; omega_arith),
      ho₂.word (Or.inl a3) (by unfold kV kT0 sFn; omega_arith), hm₁,
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [ho.word (Or.inl b1) (by unfold kBits kT2 sFn; omega_arith),
      ho₃.word (Or.inl b2) (by unfold kBits kT2 sFn; omega_arith),
      ho₂.word (Or.inl b3) (by unfold kBits kT2 sFn; omega_arith), hm₁, word_writeW_self]

theorem tabBuild_eq (mul : Nat → Nat → Nat → Prog isa) : tabBuild mul =
    ([seqs tabHead] : List (Prog isa)) ++ (([.loop (seqs [mul aY aY aXm,
      .block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aY))), .mov .rbx (.mem (hdr kV))], copyWords,
      .block [.mov .rax (.mem (hdr kV)), .mov .rdx (.mem (hdr sW)), .alu .add .rdx (.imm 2),
        .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rax (.reg .rdx),
        .store (hdr kV) .rax, .mov .rax (.mem (hdr kBits)), .alu .sub .rax (.imm 1), .store (hdr kBits) .rax]]) .ne] : List (Prog isa)) ++
    ([.block (([.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aY)))] : List Instr) ++ extBase aR1 .rsi),
      copyWords] : List (Prog isa))) := rfl

/-- The table, from `b R mod c` in `aXm`: `TabOK`, and `y := 1`. -/
theorem tabBuild_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm b : Nat}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hX : wv s.mem B (slot w aXm) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c) :
    WP isa (seqs (tabBuild M.mm)) s fun t =>
      MrCtx t B Z w mi c (Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c) ∧ TabOK t.mem B w c b ∧
      wv t.mem B (slot w aY) w = 2 ^ (64 * w) % c ∧ Frm B (tabRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hZ := hd.z
  have hx := hd.x
  have hw' : w < 2 ^ 31 := by have := hd.w128; omega_arith
  have hn := hc.good.scr.nowrap
  have hY8 := slot_le (w := w) (show aY < 8 by decide)
  have hR1 := slot_mono w (show aR1 + 1 ≤ aRm1 by decide)
  have hR1s := slot_succ w aR1
  have hER := slot_mono w (show aE ≤ aR1 by decide)
  have hte := tab_end w
  have hBs : slot w aB = slot w 8 + 8 * (w + 2) := slot_succ w 8
  have htb : tabBytes w = 128 * (w + 2) := by unfold tabBytes; omega_arith
  rw [tabBuild_eq]
  refine wp_seqs_append (by simp) (by simp) ?_
  simp only [seqs]
  refine WP.mono (tabHead_ok hd hc hc1 hX) fun s₄ ⟨hI0, hf₄, k₄⟩ => ?_
  refine wp_seqs_append (by simp) (by simp) ?_
  simp only [seqs]
  refine WP.mono (wp_upto (a := 0) (N := 14) (by decide) (TabI B Z w mi c _ b s₄)
    (fun i _ hi t hI => tabStep_ok M hd hodd hc1 hi hI) (fun t h => h) hI0) fun s₅ hI => ?_
  -- `y := 1`.
  refine WP.mono (copyFromExt_ok hI.ctx.good hZ (by have := hd.w4; omega_arith) hw' (a := aY) (d := aR1) (by decide)
    (by decide) (by omega_arith)) fun t ⟨hv, ho, k⟩ => ?_
  have hft : Frm B (tabRanges w) s₅.mem t.mem :=
    Frm.of_outside (ho.mono (o' := slot w aY) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_arith)) (by simp [tabRanges])
  have hf : Frm B (tabRanges w) s.mem t.mem := (hf₄.trans hI.frm).trans hft
  have hgt : Good t B Z w mi := ⟨hI.ctx.good.scr.congr k.2.2, (k.gpr (by decide)).trans hI.ctx.good.rdi,
    Hdr.of_frm hc.good.hdr hf (by simp only [tabRanges]; rng_le)⟩
  refine ⟨hc.of_tab hd hf hgt.scr hgt.rdi ?_, fun j hj => ?_, by rw [hv, hI.ctx.r1], hf,
    ((k₄.trans hI.keep).trans k).mono (by decide)⟩
  · rw [ho.wv (Or.inr (by omega_arith)) (by omega_arith)]; exact hI.ctx.b
  · have := ent_in_tab w hj
    rw [ho.wv (Or.inr (by omega_arith)) (by omega_arith)]
    exact hI.ent j (by omega_arith)

end VG.Proof.RsaKeyGen.X86_64
