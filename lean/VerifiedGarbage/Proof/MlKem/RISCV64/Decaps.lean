module

public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlKem.RISCV64.Encrypt
public import VerifiedGarbage.Proof.MlKem.RISCV64.HashTop
public import VerifiedGarbage.Proof.MlKem.RISCV64.TopSave
import VerifiedGarbage.Proof.MlKem.RISCV64.CmpSel
import VerifiedGarbage.Proof.MlKem.RISCV64.Loops
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
import VerifiedGarbage.Proof.MlKem.RISCV64.RowSum
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on RISC-V: decapsulation, correctness

As on PPC64LE (`Proof/MlKem/PPC64LE/Decaps.lean`): `K.decaps` for any
parameter set `K` (`KemLay.WF`).

The buffers of the function (`lay`): `scratch`, the 1168 bytes below the stack
pointer, `dk` and `key`; `c`, which may overlap `dk`, is only read by its
copy into `scratch`, with a layout of its own (`layC`). What every phase
keeps (`DEnv`), and the phases: the setup, `c` copied, K-PKE.Decrypt into
`m'`, `G(m' ‖ h)` into `K' ‖ r'`, `J(z ‖ c)` into `K̄`, the re-encryption
`c'` (`Enc.encrypt_ok`), the comparison of `c` and `c'`, and the selection
of `K'` or `K̄` into `key`.
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64.Decaps

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.RISCV64.Wp
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.RISCV64.Enc
open VG.Impl.Sha3.RISCV64.Stream (mov)

section
variable (s₀ : State)

abbrev pDk : Addr := s₀.gpr .a0
abbrev pC : Addr := s₀.gpr .a1
abbrev pKey : Addr := s₀.gpr .a2
abbrev pScr : Addr := s₀.gpr .a3

/-- The buffers: `scratch`, the 1168 bytes below the stack pointer, `dk` and `key`. -/
def lay (K : KemLay) : Lay :=
  ⟨fun i => [pScr s₀, s₀.sp - BitVec.ofNat 64 1168, pDk s₀, pKey s₀].getD i 0,
    [K.scratch, 1168, K.dkLen, 32]⟩

/-- The buffers of the copy of `c`: `scratch`, the stack and `c`. -/
def layC (K : KemLay) : Lay :=
  ⟨fun i => [pScr s₀, s₀.sp - BitVec.ofNat 64 1168, pC s₀].getD i 0, [K.scratch, 1168, K.ctLen]⟩

end

/-- The sizes of the buffers. -/
abbrev dSz (K : KemLay) : List Nat := [K.scratch, 1168, K.dkLen, 32]

theorem lay_sizes (K : KemLay) (s₀ : State) : (lay s₀ K).sizes = dSz K := rfl
theorem layC_sizes (K : KemLay) (s₀ : State) : (layC s₀ K).sizes = [K.scratch, 1168, K.ctLen] := rfl
theorem lay_ptr0 (K : KemLay) (s₀ : State) : (lay s₀ K).ptr 0 = pScr s₀ := rfl
theorem layC_ptr0 (K : KemLay) (s₀ : State) : (layC s₀ K).ptr 0 = pScr s₀ := rfl

/-- The precondition of the contract. -/
structure Pre (K : KemLay) (s : State) : Prop where
  wf : K.WF
  calls : K.CallsOk
  al : s.sp.toNat % 16 = 0
  sp1168 : 1168 ≤ s.sp.toNat
  rd : s.rd = [⟨pDk s, K.dkLen⟩, ⟨pC s, K.ctLen⟩]
  wr : s.wr = [⟨pKey s, 32⟩, ⟨pScr s, K.scratch⟩]
  d_dk_key : (⟨pDk s, K.dkLen⟩ : Region).Disjoint ⟨pKey s, 32⟩
  d_dk_scr : (⟨pDk s, K.dkLen⟩ : Region).Disjoint ⟨pScr s, K.scratch⟩
  d_c_key : (⟨pC s, K.ctLen⟩ : Region).Disjoint ⟨pKey s, 32⟩
  d_c_scr : (⟨pC s, K.ctLen⟩ : Region).Disjoint ⟨pScr s, K.scratch⟩
  d_key_scr : (⟨pKey s, 32⟩ : Region).Disjoint ⟨pScr s, K.scratch⟩
  b_dk : (below s.sp 1168).Disjoint ⟨pDk s, K.dkLen⟩
  b_c : (below s.sp 1168).Disjoint ⟨pC s, K.ctLen⟩
  b_key : (below s.sp 1168).Disjoint ⟨pKey s, 32⟩
  b_scr : (below s.sp 1168).Disjoint ⟨pScr s, K.scratch⟩
  f_dk : (pDk s).toNat + K.dkLen ≤ 2 ^ 64
  f_c : (pC s).toNat + K.ctLen ≤ 2 ^ 64
  f_key : (pKey s).toNat + 32 ≤ 2 ^ 64
  f_scr : (pScr s).toNat + K.scratch ≤ 2 ^ 64
  alS : (pScr s).toNat % 8 = 0

section
variable {K : KemLay} {s₀ : State} (hp : Pre K s₀)
include hp

theorem stack_fit : (s₀.sp - BitVec.ofNat 64 1168).toNat + 1168 ≤ 2 ^ 64 := by
  have := hp.sp1168
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]
  have := s₀.sp.isLt; omega

theorem lay_ok : (lay s₀ K).Ok := by
  refine Lay.ok_of (fun i hi => ?_) (fun i hi j hj hij => ?_)
  · simp only [lay, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · exact hp.f_scr
    · exact stack_fit hp
    · exact hp.f_dk
    · exact hp.f_key
  · simp only [lay, List.length_cons, List.length_nil] at hi hj
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
    rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl <;>
    simp only [lay, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first | omega | skip
    · exact hp.b_scr.symm
    · exact hp.d_dk_scr.symm
    · exact hp.d_key_scr.symm
    · exact hp.b_dk
    · exact hp.b_key
    · exact hp.d_dk_key

theorem layC_ok : (layC s₀ K).Ok := by
  refine Lay.ok_of (fun i hi => ?_) (fun i hi j hj hij => ?_)
  · simp only [layC, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact hp.f_scr
    · exact stack_fit hp
    · exact hp.f_c
  · simp only [layC, List.length_cons, List.length_nil] at hi hj
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
    rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl <;>
    simp only [layC, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first | omega | skip
    · exact hp.b_scr.symm
    · exact hp.d_c_scr.symm
    · exact hp.b_c

end

/-- What every phase keeps: `scratch`, our caller's registers in `scratch`,
the pointer `key` in `s3`, and `dk`. -/
structure DEnv (K : KemLay) (s₀ s : State) : Prop where
  ctx : Ctx (lay s₀ K) s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cs : ∀ r ∈ preserved, r ∉ savedTop → s.gpr r = s₀.gpr r
  sav : TopSaved s.mem (pScr s₀) s₀
  key : s.gpr .s3 = pKey s₀
  dk : bytesAt s.mem ((lay s₀ K).A 2 0) K.dkLen = bytesAt s₀.mem ((lay s₀ K).A 2 0) K.dkLen

/-! ### The facts on the offsets, once for any parameter set

They depend on the parameter set only through `k`, the size of `scratch`, and
the length of `c`: each is decided for every `k ≤ 4` with a `scratch` of
32 KiB (`kOf`) and the longest `c` that fits (8192 bytes from `oCin`), and
holds for a bigger `scratch` (`sepB_scr`) and a shorter `c` (`sepB_mono`). -/

/-- What a phase may change, with the sizes `sz` of the buffers: apart from
the saved registers and `dk`. -/
abbrev okWm (K : KemLay) (sz : List Nat) (w : Nat × Nat × Nat) : Bool :=
  sepB sz (0, 1288, 80) w && sepB sz (2, 0, K.dkLen) w

/-- A region the phases may change. -/
def okW (K : KemLay) (w : Nat × Nat × Nat) : Bool := okWm K (dSz K) w

/-- A region decryption may change: also apart from the copy of `c`. -/
def okD (K : KemLay) (w : Nat × Nat × Nat) : Bool := okW K w && sepB (dSz K) (0, oCin, K.ctLen) w

/-- `okD`, with the sizes `sz` of the buffers and the longest `c`. -/
abbrev okDm (K : KemLay) (sz : List Nat) (w : Nat × Nat × Nat) : Bool :=
  okWm K sz w && sepB sz (0, oCin, 8192) w

theorem inB_len {i o n l : Nat} (h : n ≤ l) : inB (i, o, n) (i, o, l) = true := by
  simp only [inB, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]; omega

theorem ct_le {K : KemLay} (hK : K.WF) : K.ctLen ≤ 8192 := by
  have := hK.cin; simp only [oCin, oPoly] at this; omega

theorem ct_lt {K : KemLay} (hK : K.WF) : K.ctLen < 2048 := by
  have h1 : K.du * K.k ≤ 11 * 4 := Nat.mul_le_mul hK.du hK.k4
  have h2 := hK.dv
  simp only [KemLay.ctLen, KemLay.uLen, KemLay.vLen, Nat.mul_assoc]; omega

theorem ct_pos {K : KemLay} (hK : K.WF) : 0 < K.ctLen := by
  have h1 := hK.du1
  have h2 := hK.k1
  have : 0 < K.uLen * K.k := Nat.mul_pos (by simp only [KemLay.uLen]; omega) (by omega)
  simp only [KemLay.ctLen]; omega

theorem okW_of {K : KemLay} (hK : K.WF) {w : Nat × Nat × Nat} (h : okWm K (dSz (kOf K.k)) w = true) :
    okW K w = true := by
  simp only [okWm, okW, Bool.and_eq_true] at h ⊢
  exact ⟨sepB_scr h.1 hK.scr, sepB_scr h.2 hK.scr⟩

theorem allOkW_of {K : KemLay} (hK : K.WF) {W : List (Nat × Nat × Nat)}
    (h : W.all (okWm K (dSz (kOf K.k))) = true) : W.all (okW K) = true :=
  List.all_eq_true.mpr fun w hw => okW_of hK (List.all_eq_true.mp h w hw)

theorem allOkD_of {K : KemLay} (hK : K.WF) {W : List (Nat × Nat × Nat)}
    (h : W.all (okDm K (dSz (kOf K.k))) = true) : W.all (okD K) = true :=
  List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp h w hw
    rw [okDm, Bool.and_eq_true] at this
    rw [okD, Bool.and_eq_true]
    exact ⟨okW_of hK this.1, sepB_mono (sepB_scr this.2 hK.scr) (inB_len (ct_le hK)) (inB_refl w)⟩


/-! ### The offsets the phases use, proven in a small context -/

theorem ctLen_split (K : KemLay) : K.ctLen = K.uLen * K.k + 32 * K.dv := rfl

section
variable {K : KemLay} (hK : K.WF)
include hK

theorem oAcc_fit : K.oAcc + 1024 ≤ 32768 := by offs
theorem oNtt_fit : K.oNtt + 1024 ≤ 32768 := by offs
theorem oP3_fit : oPoly (3 * K.k) + 1024 ≤ 32768 := by offs
theorem oAcc_le_oNtt : K.oAcc + 1024 ≤ K.oNtt := by offs
theorem oP3_le_oAcc : oPoly (3 * K.k) + 1024 ≤ K.oAcc := by offs
theorem oP3_le_cin : oPoly (3 * K.k) + 1024 ≤ oCin := by offs
theorem oMsg_le_oP3 : oMsg + 32 ≤ oPoly (3 * K.k) := by offs
theorem oCt_lt : K.oCt < 32768 := by offs

theorem vIn_fit : oCin + K.uLen * K.k + 32 * K.dv ≤ 32768 := by
  have h := hK.cin
  rw [ctLen_split, ← Nat.add_assoc] at h
  exact h

end

/-- The buffer of each pointer register. -/
def didx : Reg → Nat
  | .s10 => 2 | _ => 0

/-- Decides a fact about the offsets in the buffers. -/
tactic_template "ddecide" : tactic => `(tactic| first
                   | decide
                   | ((try have := (‹Pre _ _›).wf)
                      (try simp only [lay_sizes, layC_sizes, dSz, okW, okD, okWm, okDm, didx, kRegs,
                         List.all_cons, List.all_nil, List.all_append, List.map_cons, List.map_nil, trip,
                         Bool.and_true])
                      (try have := (‹KemLay.WF _›).scr)
                      (try (have hcin := (‹KemLay.WF _›).cin
                            have hct := (‹KemLay.WF _›).ct
                            simp only [oCin, KemLay.ctLen, KemLay.uLen, KemLay.vLen, KemLay.oCt, oPoly]
                              at hcin hct))
                      kdecide))

theorem saveR_eq (K : KemLay) (s₀ : State) : saveR (pScr s₀) = (lay s₀ K).R 0 1288 80 := rfl

theorem DEnv.keep {K : KemLay} {s₀ s s' : State} (hp : Pre K s₀) (h : DEnv K s₀ s) {xs : List Reg}
    {W : List (Nat × Nat × Nat)} (hk : KeptX xs ((lay s₀ K).RL W) s s')
    (hx : ∀ x ∈ xs, x ∈ savedTop ∧ x ≠ .s11 ∧ x ≠ .s3) (hW : W.all (okW K) = true) : DEnv K s₀ s' := by
  have hL := lay_ok hp
  have hK := hp.wf
  have h1 : sepAll (lay s₀ K).sizes (0, 1288, 80) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw
      simp only [okW, okWm, Bool.and_eq_true] at this; exact this.1
  have h3 : sepAll (lay s₀ K).sizes (2, 0, K.dkLen) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw
      simp only [okW, okWm, Bool.and_eq_true] at this; exact this.2
  have n31 : Reg.s11 ∉ xs := fun hm => (hx _ hm).2.1 rfl
  have n3 : Reg.s3 ∉ xs := fun hm => (hx _ hm).2.2 rfl
  refine ⟨hk.ctx n31 h.ctx, hk.rd.trans h.rd, hk.wr.trans h.wr, hk.sp.trans h.sp, fun r hr hs => ?_,
    h.sav.keep hk.frame (by rw [saveR_eq K]; exact Lay.disjAll hL h1), ?_, ?_⟩
  · rw [hk.cs r hr (fun hm => hs (hx r hm).1), h.cs r hr hs]
  · rw [hk.cs .s3 (by decide) n3]; exact h.key
  · rw [Lay.bytes_keep hL hk.frame h3 (by have := hK.k4; simp only [KemLay.dkLen]; omega)]; exact h.dk

theorem buf_wr {K : KemLay} {s₀ : State} (hp : Pre K s₀) :
    (lay s₀ K).buf 0 ∈ s₀.wr ∧ (lay s₀ K).buf 3 ∈ s₀.wr ∧ (lay s₀ K).buf 2 ∈ s₀.rd ++ s₀.wr ∧
      (layC s₀ K).buf 2 ∈ s₀.rd ++ s₀.wr ∧ (layC s₀ K).buf 0 ∈ s₀.wr := by
  rw [hp.wr, hp.rd]; simp [Lay.buf, lay, layC]

/-! ## The setup -/

theorem setup_ok {K : KemLay} {s₀ : State} (hp : Pre K s₀) :
    WP isa (.block decapsSetup) s₀ fun s => DEnv K s₀ s ∧ s.gpr .s10 = pDk s₀ ∧ s.gpr .s8 = pC s₀ ∧
      bytesAt s.mem ((layC s₀ K).A 2 0) K.ctLen = bytesAt s₀.mem ((layC s₀ K).A 2 0) K.ctLen := by
  have hL := lay_ok hp
  have hK := hp.wf
  have scr := hK.scr
  obtain ⟨w0, -, -, -, -⟩ := buf_wr hp
  have wS : ∀ {o n : Nat}, o + n ≤ 32768 → InRegions s₀.wr (pScr s₀ + BitVec.ofNat 64 o) n := fun h =>
    Lay.covers w0 (by simp only [lay, Lay.size, List.getD_cons_zero]; omega) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [decapsSetup, WP.block_append_iff]
  refine WP.mono (topSave_ok rfl hp.alS fun o _ h₂ => wS (by omega))
    fun s₁ ⟨sav, fr, g₁, rd₁, wr₁, sp₁⟩ => ?_
  have hmv : WP isa (.block [mov .s3 .a2, mov .s10 .a0, mov .s8 .a1, mov .s11 .a3]) s₁
      fun s => s.gpr .s3 = pKey s₀ ∧ s.gpr .s10 = pDk s₀ ∧ s.gpr .s8 = pC s₀ ∧ s.gpr .s11 = pScr s₀ ∧
      (∀ r ∈ preserved, r ∉ savedTop → s.gpr r = s₁.gpr r) ∧ s.mem = s₁.mem ∧
      s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.sp = s₁.sp :=
    wp_mv fun u₁ h₁ => wp_mv fun u₂ h₂ => wp_mv fun u₃ h₃ => wp_mv fun u₄ h₄ => WP.block_nil
      ⟨by simp only [h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g₁],
        by simp only [h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g₁],
        by simp only [h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g₁],
        by simp only [h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g₁],
        fun r hr hs => by
          simp only [savedTop, List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
          obtain ⟨a3, -, -, -, -, a8, -, a10, a11⟩ := hs
          simp only [h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, a3, a8, a10, a11, ↓reduceIte],
        by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem], by rw [h₄.rd, h₃.rd, h₂.rd, h₁.rd],
        by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr], by rw [h₄.sp, h₃.sp, h₂.sp, h₁.sp]⟩
  refine WP.mono hmv fun s ⟨g3, g30, g28, g31, cs, m, rd, wr, sp⟩ => ?_
  have fr' : Frame ((lay s₀ K).RL [(0, 1288, 80)]) s₀.mem s.mem := by
    rw [m]; exact fr.mono (fun r hr => by rw [List.mem_singleton] at hr; subst hr; simp [saveR_eq K])
  have dkf : K.dkLen ≤ 2 ^ 64 := by have := hK.k4; simp only [KemLay.dkLen]; omega
  refine ⟨⟨⟨hL, scr, rfl, by simp [lay], g31, by rw [sp, sp₁]; exact hp.sp1168, by rw [sp, sp₁]; exact hp.al,
    hp.alS, by rw [sp, sp₁]; rfl, by rw [wr, wr₁, hp.wr]; simp [lay]⟩, rd.trans rd₁, wr.trans wr₁, sp.trans sp₁,
    fun r hr hs => ?_, by rw [m]; exact sav, g3, ?_⟩, g30, g28, ?_⟩
  · rw [cs r hr hs, g₁]
  · exact Lay.bytes_keep hL fr' (by ddecide) dkf
  · have frC : Frame ((layC s₀ K).RL [(0, 1288, 80)]) s₀.mem s.mem := by
      simpa only [Lay.RL, List.map_cons, List.map_nil, Lay.R, lay_ptr0, layC_ptr0] using fr'
    exact Lay.bytes_keep (layC_ok hp) frC (by rw [layC_sizes]; ddecide) (by
      have := ct_le hK; omega)

/-! ## `c` copied -/

/-- `dk`. -/
abbrev DK (K : KemLay) (s₀ : State) : List Byte := bytesAt s₀.mem ((lay s₀ K).A 2 0) K.dkLen

/-- `c`. -/
abbrev CT (K : KemLay) (s₀ : State) : List Byte := bytesAt s₀.mem ((layC s₀ K).A 2 0) K.ctLen

theorem layA0 (K : KemLay) (s₀ : State) (o : Nat) : (layC s₀ K).A 0 o = (lay s₀ K).A 0 o := rfl

theorem copyC_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : DEnv K s₀ s)
    (h28 : s.gpr .s8 = pC s₀) (hc : bytesAt s.mem ((layC s₀ K).A 2 0) K.ctLen = CT K s₀) :
    WP isa (copy .s8 0 .s11 oCin K.ctLen) s fun s' => DEnv K s₀ s' ∧ s'.gpr .s10 = s.gpr .s10 ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oCin) K.ctLen = CT K s₀ := by
  have hK := hp.wf
  obtain ⟨-, -, -, wC, wC0⟩ := buf_wr hp
  refine WP.mono (copyL (layC_ok hp) (i := 2) (j := 0) (by decide) (by decide) h28
    (by rw [h.ctx.s11, lay_ptr0, layC_ptr0]) (by decide) (by decide) (ct_lt hK)
    (ct_pos hK) (by rw [layC_sizes]; ddecide) (by rw [h.rd, h.wr]; exact wC)
    (by rw [h.wr]; exact wC0)) fun s' ⟨k, e⟩ => ⟨?_, k.cs .s10 (by decide), ?_⟩
  · have k' : Kept ((lay s₀ K).RL [(0, oCin, K.ctLen)]) s s' := by
      simpa only [Lay.RL, List.map_cons, List.map_nil, Lay.R, lay_ptr0, layC_ptr0] using k
    exact h.keep hp (k'.x []) (by simp) (by ddecide)
  · rw [← layA0, e, hc]

theorem ptr28_ok {s : State} :
    WP isa (.block (addrOf .s8 .s11 oCin)) s fun s' =>
      KeptX [.s8] [] s s' ∧ s'.gpr .s8 = s.gpr .s11 + BitVec.ofNat 64 oCin ∧ s'.mem = s.mem := by
  rw [← List.append_nil (addrOf .s8 .s11 oCin)]
  exact wp_addrOf (by decide) (by decide) fun s' h => WP.block_nil
    ⟨⟨fun r _ hx => h.other r fun e => hx (by rw [e]; exact List.mem_singleton_self _), h.sp, h.rd, h.wr,
      by rw [h.mem]; exact Frame.refl _ _⟩, h.gpr, h.mem⟩

/-- What decryption keeps: `DEnv`, `dk` in `s10`, and the copy of `c` in `s8`. -/
structure DD (K : KemLay) (s₀ s : State) : Prop where
  env : DEnv K s₀ s
  s10 : s.gpr .s10 = pDk s₀
  s8 : s.gpr .s8 = (lay s₀ K).A 0 oCin
  c : bytesAt s.mem ((lay s₀ K).A 0 oCin) K.ctLen = CT K s₀

theorem DD.keep {K : KemLay} {s₀ s s' : State} (hp : Pre K s₀) (h : DD K s₀ s) {xs : List Reg}
    {W : List (Nat × Nat × Nat)} (hk : KeptX xs ((lay s₀ K).RL W) s s')
    (hx : ∀ x ∈ xs, x ∈ savedTop ∧ x ≠ .s10 ∧ x ≠ .s8 ∧ x ≠ .s11 ∧ x ≠ .s3) (hW : W.all (okD K) = true) :
    DD K s₀ s' := by
  have hK := hp.wf
  have w1 : W.all (okW K) = true := List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp hW w hw; simp only [okD, Bool.and_eq_true] at this; exact this.1
  have w2 : sepAll (lay s₀ K).sizes (0, oCin, K.ctLen) W = true := List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp hW w hw; simp only [okD, Bool.and_eq_true] at this; exact this.2
  have nx : ∀ r, r = .s10 ∨ r = .s8 ∨ r = .s11 → r ∉ xs := fun r hr hm => by
    obtain ⟨-, a, b, c, -⟩ := hx r hm
    rcases hr with rfl | rfl | rfl <;> simp_all
  refine ⟨h.env.keep hp hk (fun x hm => ⟨(hx x hm).1, (hx x hm).2.2.2.1, (hx x hm).2.2.2.2⟩) w1, ?_, ?_, ?_⟩
  · rw [hk.cs .s10 (by decide) (nx _ (by simp)), h.s10]
  · rw [hk.cs .s8 (by decide) (nx _ (by simp)), h.s8]
  · rw [Lay.bytes_keep (lay_ok hp) hk.frame w2 (by have := ct_le hK; omega)]; exact h.c

/-! ## `û` -/

theorem uArgs_ok {K : KemLay} (hK : K.WF) {s : State} {P C : Addr} {j : Nat} (hj : j < K.k)
    (h11 : s.gpr .s11 = P) (h8 : s.gpr .s8 = C) (h6 : s.gpr .s6 = BitVec.ofNat 64 j) :
    WP isa (.block (atMul .a0 .s8 .s6 K.uLen ++ [.li .a1 K.uLen, .li .a2 K.du] ++ slotAt .a3 .s6 K.k)) s
      fun s' => Only s s' ∧
      s'.gpr .a0 = C + BitVec.ofNat 64 (K.uLen * j) ∧ s'.gpr .a1 = BitVec.ofNat 64 (32 * K.du) ∧
      s'.gpr .a2 = BitVec.ofNat 64 K.du ∧
      s'.gpr .a3 = P + BitVec.ofNat 64 (oPoly K.k + 1024 * j) := by
  have k4 := hK.k4
  have e1 : K.uLen < 2048 := by have := hK.du; simp only [KemLay.uLen]; omega
  have e2 : K.du < 2048 := by have := hK.du; omega
  rw [← List.append_nil (slotAt .a3 .s6 K.k)]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_atMul e1 (by decide) (by decide) fun s₁ u₁ => wp_li e1 fun s₂ h₂ => wp_li e2 fun s₃ h₃ =>
    wp_slotAt (i := j) (by omega) (by omega) (by decide)
      (by rw [h₃.other _ (by decide), h₂.other _ (by decide), u₁.other _ (by decide) (by decide), h6])
      fun s₄ h₄ => WP.block_nil ⟨⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨n0, n1, n2, n3, n4, -⟩ := pres_ne hr
    rw [h₄.other _ n4, h₃.other _ n3, h₂.other _ n2, u₁.other _ n1 n0]
  · rw [h₄.mem, h₃.mem, h₂.mem, u₁.mem]
  · rw [h₄.rd, h₃.rd, h₂.rd, u₁.rd]
  · rw [h₄.wr, h₃.wr, h₂.wr, u₁.wr]
  · rw [h₄.sp, h₃.sp, h₂.sp, u₁.sp]
  · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), u₁.gpr, h8, h6, mul_eq]
  · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr]
  · rw [h₄.other _ (by decide), h₃.gpr]
  · rw [h₄.gpr, h₃.other _ (by decide), h₂.other _ (by decide), u₁.other _ (by decide) (by decide), h11]

/-- `û` for the first `j` rows, from `s₁`. -/
structure UInv (K : KemLay) (s₀ s₁ : State) (j : Nat) (s : State) : Prop where
  kx : KeptX [.s6] ((lay s₀ K).RL [(0, oPoly K.k, 1024 * K.k), (0, K.oNtt, 1024)]) s₁ s
  s6 : s.gpr .s6 = BitVec.ofNat 64 j
  u : ∀ i < j, PolyIs s.mem ((lay s₀ K).A 0 (oPoly (K.k + i)))
    (ntt (VG.Proof.MlKem.KPke.dcU K.p (CT K s₀) i))

/-- In row `j` of `û`, from `s`, after the decompression. -/
structure UB (K : KemLay) (s₀ : State) (j : Nat) (s : State) (s' : State) : Prop where
  kx : KeptX [] ((lay s₀ K).RL [(0, oPoly (K.k + j), 1024)]) s s'
  p : PolyIs s'.mem ((lay s₀ K).A 0 (oPoly (K.k + j))) (VG.Proof.MlKem.KPke.dcU K.p (CT K s₀) j)

/-- In row `j` of `û`, from `s`, after the NTT. -/
structure UD (K : KemLay) (s₀ : State) (j : Nat) (s : State) (s' : State) : Prop where
  kx : KeptX [] ((lay s₀ K).RL [(0, oPoly (K.k + j), 1024), (0, K.oNtt, 1024)]) s s'
  p : PolyIs s'.mem ((lay s₀ K).A 0 (oPoly (K.k + j)))
    (ntt (VG.Proof.MlKem.KPke.dcU K.p (CT K s₀) j))

/-- Polynomial `k + j` of `û` is in what the decoding of `û` writes, apart from the others. -/
abbrev USlots (K : KemLay) : Prop := ∀ j < K.k,
    [((0 : Nat), oPoly (K.k + j), (1024 : Nat)), (0, K.oNtt, 1024)].all
      (fun w => [(0, oPoly K.k, 1024 * K.k), (0, K.oNtt, 1024)].any (subB0 w)) = true ∧
    (∀ i < K.k, i ≠ j → [((0 : Nat), oPoly (K.k + j), (1024 : Nat)), (0, K.oNtt, 1024)].all
      (sep0 (oPoly (K.k + i)) 1024) = true)

theorem u_facts {K : KemLay} (hK : K.WF) {j : Nat} (hj : j < K.k) :
    [((0 : Nat), oPoly (K.k + j), (1024 : Nat)), (0, K.oNtt, 1024)].all
      (fun w => [(0, oPoly K.k, 1024 * K.k), (0, K.oNtt, 1024)].any (subB0 w)) = true ∧
    (∀ i < K.k, i ≠ j → [((0 : Nat), oPoly (K.k + j), (1024 : Nat)), (0, K.oNtt, 1024)].all
      (sep0 (oPoly (K.k + i)) 1024) = true) ∧
    [((0 : Nat), oPoly K.k, 1024 * K.k), (0, K.oNtt, 1024)].all (sep0 oCin K.ctLen) = true := by
  have hcin := hK.cin
  have u : USlots K := (by decide : ∀ k < 5, USlots (kOf k)) K.k (by have := hK.k4; omega)
  exact ⟨(u j hj).1, (u j hj).2, by
    simp only [oCin] at hcin
    kdecide⟩

section
variable {K : KemLay} {s₀ : State} (hp : Pre K s₀) {s₁ : State} (h₁ : DD K s₀ s₁) {j : Nat}
  (hj : j < K.k) {s : State} (h : UInv K s₀ s₁ j s)
include hp h₁ hj h

theorem u1_ok : WP isa (.block (atMul .a0 .s8 .s6 K.uLen ++ [.li .a1 K.uLen, .li .a2 K.du] ++
      slotAt .a3 .s6 K.k)) s fun s' =>
      Only s s' ∧ s'.gpr .a0 = (lay s₀ K).A 0 (oCin + K.uLen * j) ∧
      s'.gpr .a1 = BitVec.ofNat 64 (32 * K.du) ∧ s'.gpr .a2 = BitVec.ofNat 64 K.du ∧
      s'.gpr .a3 = (lay s₀ K).A 0 (oPoly (K.k + j)) := by
  have hK := hp.wf
  have hc := h.kx.ctx (by decide) h₁.env.ctx
  have g28 : s.gpr .s8 = (lay s₀ K).A 0 oCin := by
    rw [h.kx.cs .s8 (by decide) (by decide), h₁.s8]
  refine WP.mono (uArgs_ok hK hj hc.s11 g28 h.s6) fun s' ⟨o, a3, a4, a5, a6⟩ => ⟨o, ?_, a4, a5, ?_⟩
  · rw [a3]; exact ptr_add _ _ _
  · rw [a6, show oPoly K.k + 1024 * j = oPoly (K.k + j) by offs]

theorem u2_ok {s' : State} (o : Only s s')
    (a3 : s'.gpr .a0 = (lay s₀ K).A 0 (oCin + K.uLen * j))
    (a4 : s'.gpr .a1 = BitVec.ofNat 64 (32 * K.du)) (a5 : s'.gpr .a2 = BitVec.ofNat 64 K.du)
    (a6 : s'.gpr .a3 = (lay s₀ K).A 0 (oPoly (K.k + j))) : WP isa K.callDU s' (UB K s₀ j s) := by
  have hL := lay_ok hp
  have hK := hp.wf
  have hc := (h.kx.ctx (by decide) h₁.env.ctx).only o
  obtain ⟨-, -, c3⟩ := u_facts hK hj
  have u1 := Enc.uSlot (K := K) hj
  have hcin := hK.cin
  have hcb : bytesAt s'.mem ((lay s₀ K).A 0 (oCin + K.uLen * j)) (32 * K.du) =
      (((CT K s₀).drop (K.uLen * j)).take K.uLen) := by
    rw [o.mem, ← h₁.c, ← Lay.bytes_keep hL h.kx.frame
      (h₁.env.ctx.sepAll0 (by simp only [oCin] at hcin ⊢; omega) c3)
      (by simp only [oCin] at hcin; omega), bytesAt_slice _ _ u1, ptr_add]
  refine hp.calls.du hL a3 a4 a5 a6 (.inl rfl)
    (hc.sep00 (by simp only [oCin, KemLay.uLen] at hcin u1 ⊢; omega) (by offs)
      (by have := hK.k4; simp only [oCin, oPoly]; omega))
    (mem_rd_wr hc.cw) hc.cw (hc.alP _) fun s'' k p => ⟨(o.x _ _).trans (k.x _), ?_⟩
  rw [hcb] at p; exact p

theorem u3_ok {s₂ : State} (r : UB K s₀ j s s₂) :
    WP isa (.block (slotAt .a0 .s6 K.k ++ polyAddr .a1 K.jNtt)) s₂
      fun s₃ => UB K s₀ j s s₃ ∧ s₃.gpr .a0 = (lay s₀ K).A 0 (oPoly (K.k + j)) ∧
        s₃.gpr .a1 = (lay s₀ K).A 0 K.oNtt := by
  have hK := hp.wf
  have hc₂ := r.kx.ctx (by decide) (h.kx.ctx (by decide) h₁.env.ctx)
  have g26 : s₂.gpr .s6 = BitVec.ofNat 64 j := by
    rw [r.kx.cs .s6 (by decide) (by simp), h.s6]
  exact WP.mono (nttArgs_ok hK (by omega) hc₂.s11 g26) fun s₃ ⟨o, a3, a4⟩ =>
    ⟨⟨r.kx.trans (o.x _ _), by rw [o.mem]; exact r.p⟩, a3, a4⟩

theorem u4_ok {s₃ : State} (r : UB K s₀ j s s₃)
    (a3 : s₃.gpr .a0 = (lay s₀ K).A 0 (oPoly (K.k + j)))
    (a4 : s₃.gpr .a1 = (lay s₀ K).A 0 K.oNtt) : WP isa callNtt s₃ (UD K s₀ j s) := by
  have hK := hp.wf
  have hc₃ := r.kx.ctx (by decide) (h.kx.ctx (by decide) h₁.env.ctx)
  exact nttL (lay_ok hp) a3 a4 (hc₃.sep00 (by offs) (by offs) (by kdecide)) hc₃.cw hc₃.cw r.p
    (hc₃.alP _) (hc₃.alP _) fun s₄ k p => ⟨(r.kx.monoL (by simp)).trans (k.x _), p⟩

theorem u5_ok {s₄ : State} (r : UD K s₀ j s s₄) :
    WP isa (.block (count .s6 K.k)) s₄ fun s' =>
      UInv K s₀ s₁ (j + 1) s' ∧ (s'.gpr .t0 != 0) = decide (j + 1 ≠ K.k) := by
  have hK := hp.wf
  have k4 := hK.k4
  obtain ⟨c1, c2, -⟩ := u_facts hK hj
  have g26 : s₄.gpr .s6 = BitVec.ofNat 64 j := by
    rw [r.kx.cs .s6 (by decide) (by simp), h.s6]
  refine WP.mono (count_ok (by decide) (by omega) (by omega) g26) fun s' ⟨k', g', z'⟩ =>
    ⟨⟨?_, g', fun i hi => ?_⟩, z'⟩
  · exact h.kx.trans (((r.kx.weaken (by simp)).trans
      (k'.mono (fun _ h => absurd h List.not_mem_nil))).subL h₁.env.ctx c1)
  · by_cases e : i = j
    · subst e
      exact polyIs_frame k'.frame (fun _ h => absurd h List.not_mem_nil) r.p
    · exact polyIs_frame k'.frame (fun _ h => absurd h List.not_mem_nil)
        (Lay.polyIs_keep (lay_ok hp) r.kx.frame
          (h₁.env.ctx.sepAll0 (by offs) (c2 i (by omega) e)) (h.u i (by omega)))

theorem decU_step : WP isa K.decUBody s fun s' =>
    UInv K s₀ s₁ (j + 1) s' ∧ (s'.gpr .t0 != 0) = decide (j + 1 ≠ K.k) :=
  WP.seq (WP.mono (u1_ok hp h₁ hj h) fun _ ⟨o, a3, a4, a5, a6⟩ =>
    WP.seq (WP.mono (u2_ok hp h₁ hj h o a3 a4 a5 a6) fun _ r₂ =>
    WP.seq (WP.mono (u3_ok hp h₁ hj h r₂) fun _ ⟨r₃, b3, b4⟩ =>
    WP.seq (WP.mono (u4_ok hp h₁ hj h r₃ b3 b4) fun _ r₄ => u5_ok hp h₁ hj h r₄))))

end

/-! ## The rest of K-PKE.Decrypt -/

/-- The regions decryption changes, apart from what `DD` keeps. -/
abbrev DecF (K : KemLay) (sz : List Nat) : Prop :=
  [((0 : Nat), oPoly K.k, 1024 * K.k), (0, K.oNtt, 1024)].all (okDm K sz) = true ∧
  [((0 : Nat), (2048 : Nat), 1024 * K.k)].all (okDm K sz) = true ∧ (dotW K).all (okDm K sz) = true ∧
  [((0 : Nat), K.oAcc, (1024 : Nat)), (0, K.oNtt, 1024)].all (okDm K sz) = true ∧
  [((0 : Nat), oPoly (3 * K.k), (1024 : Nat))].all (okDm K sz) = true ∧
  [((0 : Nat), oMsg, 32 * 1)].all (okDm K sz) = true

theorem dec_f {K : KemLay} (hK : K.WF) :
    [((0 : Nat), oPoly K.k, 1024 * K.k), (0, K.oNtt, 1024)].all (okD K) = true ∧
    [((0 : Nat), (2048 : Nat), 1024 * K.k)].all (okD K) = true ∧ (dotW K).all (okD K) = true ∧
    [((0 : Nat), K.oAcc, (1024 : Nat)), (0, K.oNtt, 1024)].all (okD K) = true ∧
    [((0 : Nat), oPoly (3 * K.k), (1024 : Nat))].all (okD K) = true ∧
    [((0 : Nat), oMsg, 32 * 1)].all (okD K) = true := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ :=
    (by decide : ∀ k < 5, DecF (kOf k) (dSz (kOf k))) K.k (by have := hK.k4; omega)
  exact ⟨allOkD_of hK f1, allOkD_of hK f2, allOkD_of hK f3, allOkD_of hK f4, allOkD_of hK f5,
    allOkD_of hK f6⟩

section
variable {K : KemLay} {s₀ : State} (hp : Pre K s₀)
include hp

omit hp in
theorem dU_init {s₁ : State} : WP isa (.block [.li .s6 0]) s₁ (UInv K s₀ s₁ 0) :=
  WP.mono (li_ok .s6 (N := 0) (by decide)) fun _ ⟨k, g, _⟩ =>
    ⟨k.mono (fun _ h => absurd h List.not_mem_nil), g, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩

theorem dU_done {s₁ s : State} (h₁ : DD K s₀ s₁) (h : UInv K s₀ s₁ K.k s) : DD K s₀ s :=
  h₁.keep hp h.kx (by decide) (dec_f hp.wf).1

theorem dT_pre {s : State} (h : DD K s₀ s) :
    Ctx (lay s₀ K) s ∧ s.gpr .s10 = (lay s₀ K).A 2 0 ∧
      sepAll (lay s₀ K).sizes (2, 0, 384 * K.k) [(0, 2048, 1024 * K.k)] = true ∧
      (lay s₀ K).buf 2 ∈ s.rd ++ s.wr := by
  have hK := hp.wf
  obtain ⟨-, -, w2, -, -⟩ := buf_wr hp
  exact ⟨h.env.ctx, by rw [h.s10]; exact (BitVec.add_zero _).symm, by ddecide,
    by rw [h.env.rd, h.env.wr]; exact w2⟩

/-- `ŝ` of `dk`. -/
abbrev sHat (K : KemLay) (s₀ : State) : Nat → Poly :=
  VG.Proof.MlKem.dcS (VG.Proof.MlKem.KPke.dkPke K.p (DK K s₀))

/-- `NTT(u')` of `c`. -/
abbrev uHat (K : KemLay) (s₀ : State) (i : Nat) : Poly := ntt (VG.Proof.MlKem.KPke.dcU K.p (CT K s₀) i)

theorem dT_done {s₂ s : State} (h₂ : DD K s₀ s₂)
    (hu : ∀ i < K.k, PolyIs s₂.mem ((lay s₀ K).A 0 (oPoly (K.k + i))) (uHat K s₀ i))
    (h : DecInv K (lay s₀ K) 2 0 s₂ K.k s) :
    DD K s₀ s ∧ (∀ k < K.k, PolyIs s.mem ((lay s₀ K).A 0 (oPoly k)) (sHat K s₀ k)) ∧
      ∀ i < K.k, PolyIs s.mem ((lay s₀ K).A 0 (oPoly (K.k + i))) (uHat K s₀ i) := by
  have hL := lay_ok hp
  have hK := hp.wf
  refine ⟨h₂.keep hp h.kx (by decide) (dec_f hp.wf).2.1, fun k hk => ?_, fun i hi => ?_⟩
  · have ht := h.t k hk
    have e : bytesAt s₂.mem ((lay s₀ K).A 2 (0 + 384 * k)) 384 = ((DK K s₀).drop (384 * k)).take 384 := by
      have dk : bytesAt s₂.mem ((lay s₀ K).A 2 0) K.dkLen = DK K s₀ := h₂.env.dk
      rw [← dk, bytesAt_slice _ _ (by have := hK.k4; simp only [KemLay.dkLen]; omega), ptr_add]
    rw [e] at ht
    show PolyIs _ _ (decode12 ((((DK K s₀).take (384 * K.k)).drop (384 * k)).take 384))
    rw [VG.Proof.MlKem.slice_take _ (by omega)]; exact ht
  · exact Lay.polyIs_keep hL h.kx.frame (h₂.env.ctx.sepAll0 (by offs) (by kdecide)) (hu i hi)

/-- After `dot`, with the sum `f`. -/
abbrev DV (K : KemLay) (s₀ : State) (f : Poly) (s : State) : Prop :=
  DD K s₀ s ∧ PolyIs s.mem ((lay s₀ K).A 0 K.oAcc) f

theorem dDot_ok {s : State} (h : DD K s₀ s)
    (hs : ∀ k < K.k, PolyIs s.mem ((lay s₀ K).A 0 (oPoly k)) (sHat K s₀ k))
    (hu : ∀ i < K.k, PolyIs s.mem ((lay s₀ K).A 0 (oPoly (K.k + i))) (uHat K s₀ i)) :
    WP isa K.dot s (DV K s₀ (VG.Proof.MlKem.KPke.dotK (sHat K s₀) (uHat K s₀) K.k)) := by
  have hK := hp.wf
  exact WP.mono (dot_ok hK h.env.ctx hs hu) fun _ ⟨k, p⟩ =>
    ⟨h.keep hp k (by decide) (dec_f hp.wf).2.2.1, p⟩

theorem dArgs_ok {s : State} {f : Poly} (h : DV K s₀ f s) {j j' : Nat} (hj : j + 2 < 2048)
    (hj' : j' + 2 < 2048) :
    WP isa (.block (polyAddr .a0 j ++ polyAddr .a1 j')) s fun s' =>
      (DV K s₀ f s' ∧ s'.mem = s.mem) ∧ s'.gpr .a0 = (lay s₀ K).A 0 (oPoly j) ∧
      s'.gpr .a1 = (lay s₀ K).A 0 (oPoly j') :=
  WP.mono (addr2_ok hj hj' (by decide) (by decide) (by decide) h.1.env.ctx.s11) fun _ ⟨o₁, a3, a4⟩ =>
    ⟨⟨⟨h.1.keep hp (xs := []) (W := []) (o₁.x _ _) (by simp) rfl, by rw [o₁.mem]; exact h.2⟩,
      o₁.mem⟩, a3, a4⟩

theorem dInv_ok {s : State} {f : Poly} (h : DV K s₀ f s)
    (a3 : s.gpr .a0 = (lay s₀ K).A 0 K.oAcc) (a4 : s.gpr .a1 = (lay s₀ K).A 0 K.oNtt) :
    WP isa callNttInv s (DV K s₀ (nttInv f)) := by
  have hK := hp.wf
  have hc := h.1.env.ctx
  have hw := (dec_f hK).2.2.2.1
  exact nttInvL (lay_ok hp) a3 a4 (hc.sep00 (oAcc_fit hK) (oNtt_fit hK) (.inl (oAcc_le_oNtt hK)))
    hc.cw hc.cw h.2 (hc.alP _) (hc.alP _) fun s' k p => ⟨h.1.keep hp (k.x []) (by simp) hw, p⟩

omit hp in
theorem vDArgs_ok (hK : K.WF) {s : State} {P C : Addr} (h11 : s.gpr .s11 = P) (h8 : s.gpr .s8 = C) :
    WP isa (.block ([.addi .a0 .s8 (K.uLen * K.k), .li .a1 K.vLen, .li .a2 K.dv] ++ polyAddr .a3 (3 * K.k))) s
      fun s' => Only s s' ∧
      s'.gpr .a0 = C + BitVec.ofNat 64 (K.uLen * K.k) ∧ s'.gpr .a1 = BitVec.ofNat 64 (32 * K.dv) ∧
      s'.gpr .a2 = BitVec.ofNat 64 K.dv ∧ s'.gpr .a3 = P + BitVec.ofNat 64 (oPoly (3 * K.k)) := by
  have k4 := hK.k4
  have e1 : K.uLen * K.k < 2048 := by
    have := hK.du
    have : K.uLen ≤ 352 := by simp only [KemLay.uLen]; omega
    calc K.uLen * K.k ≤ 352 * 4 := Nat.mul_le_mul this (by omega)
      _ < 2048 := by omega
  have e2 : K.vLen < 2048 := by have := hK.dv; simp only [KemLay.vLen]; omega
  have e3 : K.dv < 2048 := by have := hK.dv; omega
  rw [← List.append_nil (polyAddr .a3 (3 * K.k))]
  simp only [List.cons_append, List.nil_append]
  refine wp_addi e1 fun s₁ h₁ => wp_li e2 fun s₂ h₂ => wp_li e3 fun s₃ h₃ =>
    wp_polyAddr (by omega) (by decide) fun s₄ h₄ => WP.block_nil
      ⟨(updOnly h₁ (by decide)).trans ((updOnly h₂ (by decide)).trans ((updOnly h₃ (by decide)).trans
        (updOnly h₄ (by decide)))), ?_, ?_, ?_, ?_⟩
  · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, h8]
  · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr]
  · rw [h₄.other _ (by decide), h₃.gpr]
  · rw [h₄.gpr, h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide), h11]

theorem dV1_ok {s : State} {f : Poly} (h : DV K s₀ f s) :
    WP isa (.block ([.addi .a0 .s8 (K.uLen * K.k), .li .a1 K.vLen, .li .a2 K.dv] ++ polyAddr .a3 (3 * K.k))) s
      fun s' => DV K s₀ f s' ∧
      s'.gpr .a0 = (lay s₀ K).A 0 (oCin + K.uLen * K.k) ∧
      s'.gpr .a1 = BitVec.ofNat 64 (32 * K.dv) ∧ s'.gpr .a2 = BitVec.ofNat 64 K.dv ∧
      s'.gpr .a3 = (lay s₀ K).A 0 (oPoly (3 * K.k)) :=
  WP.mono (vDArgs_ok hp.wf h.1.env.ctx.s11 h.1.s8) fun _ ⟨o, a3, a4, a5, a6⟩ =>
    ⟨⟨h.1.keep hp (xs := []) (W := []) (o.x _ _) (by simp) rfl, by rw [o.mem]; exact h.2⟩,
      by rw [a3]; exact ptr_add _ _ _, a4, a5, a6⟩

theorem dV2_ok {s : State} {f : Poly} (h : DV K s₀ f s)
    (a3 : s.gpr .a0 = (lay s₀ K).A 0 (oCin + K.uLen * K.k))
    (a4 : s.gpr .a1 = BitVec.ofNat 64 (32 * K.dv)) (a5 : s.gpr .a2 = BitVec.ofNat 64 K.dv)
    (a6 : s.gpr .a3 = (lay s₀ K).A 0 (oPoly (3 * K.k))) :
    WP isa K.callDU s fun s' => DV K s₀ f s' ∧
      PolyIs s'.mem ((lay s₀ K).A 0 (oPoly (3 * K.k))) (VG.Proof.MlKem.KPke.dcV K.p (CT K s₀)) := by
  have hK := hp.wf
  have hc := h.1.env.ctx
  have hcin := hK.cin
  have ect : K.ctLen = K.uLen * K.k + 32 * K.dv := rfl
  have hcb : bytesAt s.mem ((lay s₀ K).A 0 (oCin + K.uLen * K.k)) (32 * K.dv) =
      ((CT K s₀).drop (K.uLen * K.k)).take (32 * K.dv) := by
    rw [← h.1.c, bytesAt_slice _ _ (Nat.le_of_eq (ctLen_split K).symm), ptr_add]
  refine hp.calls.du (lay_ok hp) a3 a4 a5 a6 (.inr rfl)
    (hc.sep00 (vIn_fit hK) (oP3_fit hK)
      (.inr (Nat.le_trans (oP3_le_cin hK) (Nat.le_add_right _ _))))
    (mem_rd_wr hc.cw) hc.cw (hc.alP _) fun s' k p => ⟨⟨h.1.keep hp (k.x []) (by simp) (dec_f hK).2.2.2.2.1, ?_⟩, ?_⟩
  · exact Lay.polyIs_keep (lay_ok hp) k.frame
      (hc.sepAll0 (oAcc_fit hK) (by have := hK.k4; kdecide)) h.2
  · rw [hcb] at p; exact p

theorem dV4_ok {s : State} {f : Poly} (h : DV K s₀ f s)
    (hv : PolyIs s.mem ((lay s₀ K).A 0 (oPoly (3 * K.k))) (VG.Proof.MlKem.KPke.dcV K.p (CT K s₀)))
    (a3 : s.gpr .a0 = (lay s₀ K).A 0 (oPoly (3 * K.k)))
    (a4 : s.gpr .a1 = (lay s₀ K).A 0 K.oAcc) :
    WP isa callSub s fun s' => DD K s₀ s' ∧
      PolyIs s'.mem ((lay s₀ K).A 0 (oPoly (3 * K.k)))
        (sub (VG.Proof.MlKem.KPke.dcV K.p (CT K s₀)) f) := by
  have hK := hp.wf
  have hc := h.1.env.ctx
  exact subL (lay_ok hp) a3 a4 (hc.sep00 (oP3_fit hK) (oAcc_fit hK) (.inl (oP3_le_oAcc hK))) hc.cw
    (mem_rd_wr hc.cw)
    hv h.2 (hc.alP _) (hc.alP _) fun s' k p => ⟨h.1.keep hp (k.x []) (by simp) (dec_f hK).2.2.2.2.1, p⟩

omit hp in
theorem mArgs_ok (hK : K.WF) {s : State} {P : Addr} (h11 : s.gpr .s11 = P) :
    WP isa (.block (polyAddr .a0 (3 * K.k) ++ [.li .a1 1, .addi .a2 .s11 oMsg, .li .a3 32])) s fun s' =>
      Only s s' ∧ s'.gpr .a0 = P + BitVec.ofNat 64 (oPoly (3 * K.k)) ∧
      s'.gpr .a1 = BitVec.ofNat 64 1 ∧ s'.gpr .a2 = P + BitVec.ofNat 64 oMsg ∧
      s'.gpr .a3 = BitVec.ofNat 64 (32 * 1) := by
  have k4 := hK.k4
  refine wp_polyAddr (by omega) (by decide) fun s₁ h₁ => wp_li (by decide) fun s₂ h₂ =>
    wp_addi (by decide) fun s₃ h₃ => wp_li (by decide) fun s₄ h₄ => WP.block_nil
      ⟨(updOnly h₁ (by decide)).trans ((updOnly h₂ (by decide)).trans ((updOnly h₃ (by decide)).trans
        (updOnly h₄ (by decide)))), ?_, ?_, ?_, ?_⟩
  · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, h11]
  · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr]
  · rw [h₄.other _ (by decide), h₃.gpr, h₂.other _ (by decide), h₁.other _ (by decide), h11]
  · rw [h₄.gpr]

theorem dM1_ok {s : State} {g : Poly} (h : DD K s₀ s)
    (hg : PolyIs s.mem ((lay s₀ K).A 0 (oPoly (3 * K.k))) g) :
    WP isa (.block (polyAddr .a0 (3 * K.k) ++ [.li .a1 1, .addi .a2 .s11 oMsg, .li .a3 32])) s fun s' =>
      (DD K s₀ s' ∧ PolyIs s'.mem ((lay s₀ K).A 0 (oPoly (3 * K.k))) g) ∧
      s'.gpr .a0 = (lay s₀ K).A 0 (oPoly (3 * K.k)) ∧ s'.gpr .a1 = BitVec.ofNat 64 1 ∧
      s'.gpr .a2 = (lay s₀ K).A 0 oMsg ∧ s'.gpr .a3 = BitVec.ofNat 64 (32 * 1) :=
  WP.mono (mArgs_ok hp.wf h.env.ctx.s11) fun _ ⟨o, a3, a4, a5, a6⟩ =>
    ⟨⟨h.keep hp (xs := []) (W := []) (o.x _ _) (by simp) rfl, by rw [o.mem]; exact hg⟩, a3, a4, a5, a6⟩

theorem dM2_ok {s : State} {g : Poly}
    (h : DD K s₀ s ∧ PolyIs s.mem ((lay s₀ K).A 0 (oPoly (3 * K.k))) g)
    (a3 : s.gpr .a0 = (lay s₀ K).A 0 (oPoly (3 * K.k))) (a4 : s.gpr .a1 = BitVec.ofNat 64 1)
    (a5 : s.gpr .a2 = (lay s₀ K).A 0 oMsg) (a6 : s.gpr .a3 = BitVec.ofNat 64 (32 * 1)) :
    WP isa callCompress s fun s' => DD K s₀ s' ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oMsg) 32 = compressEncode 1 g := by
  have hK := hp.wf
  have hc := h.1.env.ctx
  exact compressL (lay_ok hp) a3 a4 a5 a6 (by decide)
    (hc.sep00 (oP3_fit hK) (by decide) (.inr (oMsg_le_oP3 hK)))
    (mem_rd_wr hc.cw) hc.cw h.2 (hc.alP _) fun s' k p =>
    ⟨h.1.keep hp (k.x []) (by simp) (dec_f hK).2.2.2.2.2, p⟩

end

/-- `m'`. -/
abbrev MM (K : KemLay) (s₀ : State) : List Byte := VG.Proof.MlKem.KPke.decM K.p (DK K s₀) (CT K s₀)

theorem decrypt_ok {K : KemLay} {s₀ s₁ : State} (hp : Pre K s₀) (h₁ : DD K s₀ s₁) :
    WP isa K.decrypt s₁ fun s => DD K s₀ s ∧ bytesAt s.mem ((lay s₀ K).A 0 oMsg) 32 = MM K s₀ := by
  have hK := hp.wf
  refine WP.seq (WP.mono (dU_init (K := K) (s₀ := s₀) (s₁ := s₁)) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (wp_loop_nz (UInv K s₀ s₁) (N := K.k) (by have := hK.k1; omega)
    (fun j hj s h => decU_step hp h₁ hj h) (fun _ h => h) h₂) fun s₃ h₃ => ?_)
  have d₃ := dU_done hp h₁ h₃
  obtain ⟨hc₃, g30, hs₃, hr₃⟩ := dT_pre hp d₃
  refine WP.seq (WP.mono (decT_init (K := K) (L := lay s₀ K) (i := 2) (o := 0)) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (decT_loop hK hc₃ g30 hs₃ hr₃ h₄) fun s₅ h₅ => ?_)
  obtain ⟨d₅, ŝ₅, û₅⟩ := dT_done hp d₃ h₃.u h₅
  refine WP.seq (WP.mono (dDot_ok hp d₅ ŝ₅ û₅) fun s₆ h₆ => ?_)
  have k4 := hK.k4
  refine WP.seq (WP.mono (dArgs_ok hp h₆ (j := K.jAcc) (j' := K.jNtt) (by offs) (by offs))
    fun s₇ ⟨h₇, a3, a4⟩ => ?_)
  refine WP.seq (WP.mono (dInv_ok hp h₇.1 a3 a4) fun s₈ h₈ => ?_)
  refine WP.seq (WP.mono (dV1_ok hp h₈) fun s₉ ⟨h₉, b3, b4, b5, b6⟩ => ?_)
  refine WP.seq (WP.mono (dV2_ok hp h₉ b3 b4 b5 b6) fun s₁₀ ⟨h₁₀, v₁₀⟩ => ?_)
  refine WP.seq (WP.mono (dArgs_ok hp h₁₀ (j := 3 * K.k) (j' := K.jAcc) (by offs)
    (by offs)) fun s₁₁ ⟨h₁₁, c3, c4⟩ => ?_)
  have v₁₁ : PolyIs s₁₁.mem ((lay s₀ K).A 0 (oPoly (3 * K.k)))
      (VG.Proof.MlKem.KPke.dcV K.p (CT K s₀)) := by rw [h₁₁.2]; exact v₁₀
  refine WP.seq (WP.mono (dV4_ok hp h₁₁.1 v₁₁ c3 c4) fun s₁₂ ⟨h₁₂, w₁₂⟩ => ?_)
  refine WP.seq (WP.mono (dM1_ok hp h₁₂ w₁₂) fun s₁₃ ⟨h₁₃, e3, e4, e5, e6⟩ => ?_)
  refine WP.mono (dM2_ok hp h₁₃ e3 e4 e5 e6) fun s ⟨h, m⟩ => ⟨h, m.trans ?_⟩
  show _ = kpkeDecrypt K.p (VG.Proof.MlKem.KPke.dkPke K.p (DK K s₀)) (CT K s₀)
  rw [VG.Proof.MlKem.KPke.kpkeDecrypt_eq]

/-! ## The hashes -/

theorem pieceD {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : DD K s₀ s) {p : Piece} {w : Bool}
    (hb : p.base = .s10 ∨ p.base = .s11) (hw : w = true → p.base = .s11)
    (hoe : p.off < 32768) (hle : p.len < 2048) (hpos : 0 < p.len)
    (hsep : sepAll (dSz K) (didx p.base, p.off, p.len) kRegs = true) :
    PieceOk (lay s₀ K) didx s w p := by
  obtain ⟨w0, -, w2, -, -⟩ := buf_wr hp
  rw [← h.env.wr] at w0
  rw [← h.env.wr, ← h.env.rd] at w2
  refine ⟨?_, ?_, hoe, hle, hpos, hsep, ?_⟩
  · rcases hb with e | e <;> rw [e] <;> decide
  · rcases hb with e | e <;> rw [e]
    · exact h.s10
    · exact h.env.ctx.s11
  · cases w
    · simp only [Bool.false_eq_true, ite_false]
      rcases hb with e | e <;> rw [e]
      · exact w2
      · exact mem_rd_wr w0
    · simp only [ite_true]
      rw [hw rfl]; exact w0

section
variable (K : KemLay) (s₀ : State)

/-- `h`, `z` and `ek` of `dk`. -/
abbrev hH : List Byte := VG.Proof.MlKem.KPke.dkH K.p (DK K s₀)
abbrev zZ : List Byte := VG.Proof.MlKem.KPke.dkZ K.p (DK K s₀)
abbrev eK : List Byte := VG.Proof.MlKem.KPke.dkEk K.p (DK K s₀)

/-- `K'` and `r'`, the outputs of `G(m' ‖ h)`, and `K̄ = J(z ‖ c)`. -/
abbrev K1 : List Byte := (G (MM K s₀ ++ hH K s₀)).1
abbrev R1 : List Byte := (G (MM K s₀ ++ hH K s₀)).2
abbrev KB : List Byte := J (zZ K s₀ ++ CT K s₀)

end

theorem dk_slice {K : KemLay} {s₀ s : State} (h : DD K s₀ s) {k : Nat} (hk : k + 32 ≤ K.dkLen) :
    bytesAt s.mem ((lay s₀ K).A 2 k) 32 = ((DK K s₀).drop k).take 32 := by
  have dk : bytesAt s.mem ((lay s₀ K).A 2 0) K.dkLen = DK K s₀ := h.env.dk
  rw [← dk, bytesAt_slice _ _ hk, ptr_add, Nat.zero_add]

/-- The pieces of the hashes, and the regions they change. -/
abbrev HashF (K : KemLay) (sz : List Nat) : Prop :=
  sepAll sz (0, oMsg, 32) kRegs = true ∧ sepAll sz (2, 768 * K.k + 32, 32) kRegs = true ∧
  sepAll sz (0, oG, 64) kRegs = true ∧ sepAll sz (2, 768 * K.k + 64, 32) kRegs = true ∧
  sepAll sz (0, oCin, 8192) kRegs = true ∧ sepAll sz (0, oKbar, 32) kRegs = true ∧
  (kRegs ++ [((0 : Nat), oG, (64 : Nat))]).all (okDm K sz) = true ∧
  (kRegs ++ [((0 : Nat), oKbar, (32 : Nat))]).all (okDm K sz) = true ∧
  sepAll sz (0, oMsg, 32) (kRegs ++ [((0 : Nat), oKbar, (32 : Nat))]) = true ∧
  sepAll sz (0, oMsg, 32) (kRegs ++ [((0 : Nat), oG, (64 : Nat))]) = true ∧
  sepAll sz (0, oG, 32) (kRegs ++ [((0 : Nat), oKbar, (32 : Nat))]) = true ∧
  sepAll sz (0, oSigma, 32) (kRegs ++ [((0 : Nat), oKbar, (32 : Nat))]) = true ∧
  sepB sz (0, oG, 32) (3, 0, 32) = true ∧ sepB sz (0, oKbar, 32) (3, 0, 32) = true ∧
  [((3 : Nat), (0 : Nat), (32 : Nat))].all (okWm K sz) = true

theorem hash_f {K : KemLay} (hK : K.WF) :
    sepAll (dSz K) (0, oMsg, 32) kRegs = true ∧ sepAll (dSz K) (2, 768 * K.k + 32, 32) kRegs = true ∧
    sepAll (dSz K) (0, oG, 64) kRegs = true ∧ sepAll (dSz K) (2, 768 * K.k + 64, 32) kRegs = true ∧
    sepAll (dSz K) (0, oCin, K.ctLen) kRegs = true ∧ sepAll (dSz K) (0, oKbar, 32) kRegs = true ∧
    (kRegs ++ [((0 : Nat), oG, (64 : Nat))]).all (okD K) = true ∧
    (kRegs ++ [((0 : Nat), oKbar, (32 : Nat))]).all (okD K) = true ∧
    sepAll (dSz K) (0, oMsg, 32) (kRegs ++ [((0 : Nat), oKbar, (32 : Nat))]) = true ∧
    sepAll (dSz K) (0, oMsg, 32) (kRegs ++ [((0 : Nat), oG, (64 : Nat))]) = true ∧
    sepAll (dSz K) (0, oG, 32) (kRegs ++ [((0 : Nat), oKbar, (32 : Nat))]) = true ∧
    sepAll (dSz K) (0, oSigma, 32) (kRegs ++ [((0 : Nat), oKbar, (32 : Nat))]) = true ∧
    sepB (dSz K) (0, oG, 32) (3, 0, 32) = true ∧ sepB (dSz K) (0, oKbar, 32) (3, 0, 32) = true ∧
    [((3 : Nat), (0 : Nat), (32 : Nat))].all (okW K) = true := by
  have sc := hK.scr
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ :=
    (by decide : ∀ k < 5, HashF (kOf k) (dSz (kOf k))) K.k (by have := hK.k4; omega)
  exact ⟨sepAll_scr f1 sc, sepAll_scr f2 sc, sepAll_scr f3 sc, sepAll_scr f4 sc,
    sepAll_left (sepAll_scr f5 sc) (inB_len (ct_le hK)), sepAll_scr f6 sc, allOkD_of hK f7,
    allOkD_of hK f8, sepAll_scr f9 sc, sepAll_scr f10 sc, sepAll_scr f11 sc, sepAll_scr f12 sc,
    sepB_scr f13 sc, sepB_scr f14 sc, allOkW_of hK f15⟩

theorem hashG_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : DD K s₀ s)
    (hm : bytesAt s.mem ((lay s₀ K).A 0 oMsg) 32 = MM K s₀) :
    WP isa (hash 72 0x06 [⟨.s11, oMsg, 32⟩, ⟨.s10, 768 * K.k + 32, 32⟩] [⟨.s11, oG, 64⟩]) s
      fun s' => DD K s₀ s' ∧ Frame ((lay s₀ K).RL (kRegs ++ [(0, oG, 64)])) s.mem s'.mem ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oG) 32 = K1 K s₀ ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oSigma) 32 = R1 K s₀ := by
  have hK := hp.wf
  have hk4 := hK.k4
  obtain ⟨p1, p2, p3, -, -, -, w7, -, -, -, -, -, -, -, -⟩ := hash_f hK
  have hin : ∀ p ∈ [(⟨.s11, oMsg, 32⟩ : Piece), ⟨.s10, 768 * K.k + 32, 32⟩],
      PieceOk (lay s₀ K) didx s false p := by
    intro p hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · exact pieceD hp h (.inr rfl) (by simp) (by show oMsg < 32768; decide)
        (by show (32 : Nat) < 2048; decide) (by show 0 < (32 : Nat); decide) p1
    · exact pieceD hp h (.inl rfl) (by simp) (by show 768 * K.k + 32 < 32768; omega)
        (by show (32 : Nat) < 2048; decide) (by show 0 < (32 : Nat); decide) p2
  have hout : ∀ p ∈ [(⟨.s11, oG, 64⟩ : Piece)], PieceOk (lay s₀ K) didx s true p := by
    intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
    exact pieceD hp h (.inr rfl) (fun _ => rfl) (by show oG < 32768; decide)
      (by show (64 : Nat) < 2048; decide) (by show 0 < (64 : Nat); decide) p3
  have hin' : (List.map ((lay s₀ K).pb didx s.mem) [⟨.s11, oMsg, 32⟩, ⟨.s10, 768 * K.k + 32, 32⟩]).flatten =
      MM K s₀ ++ hH K s₀ := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    show bytesAt s.mem ((lay s₀ K).A 0 oMsg) 32 ++ bytesAt s.mem ((lay s₀ K).A 2 (768 * K.k + 32)) 32 = _
    rw [hm, dk_slice h (by simp only [KemLay.dkLen]; omega)]; rfl
  refine WP.mono (hash_ok (idx := didx) VG.Proof.MlKem.rate72 (by decide) h.env.ctx
    (List.cons_ne_nil _ _) hin hout (List.pairwise_singleton _ _)) fun s' ⟨k', o'⟩ =>
    ⟨h.keep hp (k'.x []) (by simp) w7, k'.frame, ?_⟩
  have e1 := o'.1
  rw [hin'] at e1
  have e2 : bytesAt s'.mem ((lay s₀ K).A 0 oG) 64 =
      (G (MM K s₀ ++ hH K s₀)).1 ++ (G (MM K s₀ ++ hH K s₀)).2 := e1.trans (G_split _)
  rw [show (64 : Nat) = 32 + 32 from rfl, bytesAt_add] at e2
  have l1 : (bytesAt s'.mem ((lay s₀ K).A 0 oG) 32).length = (G (MM K s₀ ++ hH K s₀)).1.length := by
    rw [bytesAt_length, VG.Proof.MlKem.G_fst_length]
  obtain ⟨r1, r2⟩ := List.append_inj e2 l1
  refine ⟨r1, ?_⟩
  show bytesAt s'.mem ((lay s₀ K).ptr 0 + BitVec.ofNat 64 (920 + 32)) 32 = _
  rw [← ptr_add]; exact r2

theorem hashJ_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : DD K s₀ s) :
    WP isa (hash 136 0x1f [⟨.s10, 768 * K.k + 64, 32⟩, ⟨.s11, oCin, K.ctLen⟩] [⟨.s11, oKbar, 32⟩]) s
      fun s' => DD K s₀ s' ∧ Frame ((lay s₀ K).RL (kRegs ++ [(0, oKbar, 32)])) s.mem s'.mem ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oKbar) 32 = KB K s₀ := by
  have hK := hp.wf
  have hk4 := hK.k4
  obtain ⟨-, -, -, p4, p5, p6, -, w8, -, -, -, -, -, -, -⟩ := hash_f hK
  have hin : ∀ p ∈ [(⟨.s10, 768 * K.k + 64, 32⟩ : Piece), ⟨.s11, oCin, K.ctLen⟩],
      PieceOk (lay s₀ K) didx s false p := by
    intro p hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · exact pieceD hp h (.inl rfl) (by simp) (by show 768 * K.k + 64 < 32768; omega)
        (by show (32 : Nat) < 2048; decide) (by show 0 < (32 : Nat); decide) p4
    · exact pieceD hp h (.inr rfl) (by simp) (by show oCin < 32768; decide)
        (by show K.ctLen < 2048; exact ct_lt hK) (by show 0 < K.ctLen; exact ct_pos hK) p5
  have hout : ∀ p ∈ [(⟨.s11, oKbar, 32⟩ : Piece)], PieceOk (lay s₀ K) didx s true p := by
    intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
    exact pieceD hp h (.inr rfl) (fun _ => rfl) (by show oKbar < 32768; decide)
      (by show (32 : Nat) < 2048; decide) (by show 0 < (32 : Nat); decide) p6
  have hin' : (List.map ((lay s₀ K).pb didx s.mem)
      [⟨.s10, 768 * K.k + 64, 32⟩, ⟨.s11, oCin, K.ctLen⟩]).flatten = zZ K s₀ ++ CT K s₀ := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    show bytesAt s.mem ((lay s₀ K).A 2 (768 * K.k + 64)) 32 ++
      bytesAt s.mem ((lay s₀ K).A 0 oCin) K.ctLen = _
    rw [dk_slice h (by simp only [KemLay.dkLen]; omega), h.c]; rfl
  refine WP.mono (hash_ok (idx := didx) VG.Proof.MlKem.rate136 (by decide) h.env.ctx
    (List.cons_ne_nil _ _) hin hout (List.pairwise_singleton _ _)) fun s' ⟨k', o'⟩ =>
    ⟨h.keep hp (k'.x []) (by simp) w8, k'.frame, ?_⟩
  have e1 := o'.1
  rw [hin'] at e1
  refine e1.trans ?_
  show _ = J (zZ K s₀ ++ CT K s₀)
  rw [VG.Proof.MlKem.J_eq]; rfl

/-! ## The re-encryption -/

theorem ptrs_ok {K : KemLay} (hK : K.WF) {s : State} :
    WP isa (.block ([.addi .s10 .s10 (384 * K.k), .addi .s9 .s11 oMsg] ++ polyAddr .s7 K.jCt)) s
      fun s' => KeptX [.s10, .s9, .s7] [] s s' ∧
      s'.gpr .s10 = s.gpr .s10 + BitVec.ofNat 64 (384 * K.k) ∧
      s'.gpr .s9 = s.gpr .s11 + BitVec.ofNat 64 oMsg ∧
      s'.gpr .s7 = s.gpr .s11 + BitVec.ofNat 64 K.oCt ∧ s'.mem = s.mem := by
  have k4 := hK.k4
  rw [← List.append_nil (polyAddr .s7 K.jCt)]
  simp only [List.cons_append, List.nil_append]
  refine wp_addi (imm := 384 * K.k) (by omega) fun s₁ h₁ => wp_addi (by decide) fun s₂ h₂ =>
    wp_polyAddr (by offs) (by decide) fun s₃ h₃ => WP.block_nil
      ⟨⟨fun r _ hx => ?_, by rw [h₃.sp, h₂.sp, h₁.sp], by rw [h₃.rd, h₂.rd, h₁.rd], by rw [h₃.wr, h₂.wr, h₁.wr],
        by rw [h₃.mem, h₂.mem, h₁.mem]; exact Frame.refl _ _⟩, ?_, ?_, ?_, by rw [h₃.mem, h₂.mem, h₁.mem]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨a30, a29, a27⟩ := hx
    rw [h₃.other _ a27, h₂.other _ a29, h₁.other _ a30]
  · rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr]
  · rw [h₃.other _ (by decide), h₂.gpr, h₁.other _ (by decide)]
  · rw [h₃.gpr, h₂.other _ (by decide), h₁.other _ (by decide)]

/-- Before the re-encryption. -/
structure DP (K : KemLay) (s₀ s : State) : Prop where
  env : DEnv K s₀ s
  s10 : s.gpr .s10 = (lay s₀ K).A 2 (384 * K.k)
  s9 : s.gpr .s9 = (lay s₀ K).A 0 oMsg
  s8 : s.gpr .s8 = (lay s₀ K).A 0 oCin
  s7 : s.gpr .s7 = (lay s₀ K).A 0 K.oCt
  c : bytesAt s.mem ((lay s₀ K).A 0 oCin) K.ctLen = CT K s₀
  m : bytesAt s.mem ((lay s₀ K).A 0 oMsg) 32 = MM K s₀
  k1 : bytesAt s.mem ((lay s₀ K).A 0 oG) 32 = K1 K s₀
  r1 : bytesAt s.mem ((lay s₀ K).A 0 oSigma) 32 = R1 K s₀
  kb : bytesAt s.mem ((lay s₀ K).A 0 oKbar) 32 = KB K s₀

theorem ptrs_dp {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : DD K s₀ s)
    (hm : bytesAt s.mem ((lay s₀ K).A 0 oMsg) 32 = MM K s₀)
    (hk : bytesAt s.mem ((lay s₀ K).A 0 oG) 32 = K1 K s₀)
    (hr : bytesAt s.mem ((lay s₀ K).A 0 oSigma) 32 = R1 K s₀)
    (hb : bytesAt s.mem ((lay s₀ K).A 0 oKbar) 32 = KB K s₀) :
    WP isa (.block ([.addi .s10 .s10 (384 * K.k), .addi .s9 .s11 oMsg] ++ polyAddr .s7 K.jCt)) s
      (DP K s₀) :=
  WP.mono (ptrs_ok hp.wf) fun _ ⟨k, g30, g29, g27, m⟩ =>
    ⟨h.env.keep hp (W := []) k (by decide) rfl, by rw [g30, h.s10]; rfl, by rw [g29, h.env.ctx.s11],
      by rw [k.cs .s8 (by decide) (by decide), h.s8], by rw [g27, h.env.ctx.s11],
      by rw [m]; exact h.c, by rw [m]; exact hm, by rw [m]; exact hk, by rw [m]; exact hr,
      by rw [m]; exact hb⟩

/-- The buffers of `encrypt`: `ek` in `dk`, `m'` and `c'` in `scratch`. -/
abbrev db (K : KemLay) : EB := ⟨2, 384 * K.k, 0, oMsg, 0, K.oCt⟩

/-- The facts on the buffers of the re-encryption, with the sizes `sz` and the longest `c'`. -/
abbrev EncF (K : KemLay) (sz : List Nat) : Prop :=
  (encW0 K ++ [((0 : Nat), K.oCt, oCin - K.oCt)]).all (okWm K sz) = true ∧
  [((0 : Nat), oCin, (8192 : Nat)), (0, oG, 32), (0, oKbar, 32)].all
    (fun w => sepAll sz w (encW0 K ++ [((0 : Nat), K.oCt, oCin - K.oCt)])) = true ∧
  sepAll sz (2, 384 * K.k, K.ekLen) (encW0 K) = true ∧ sepAll sz (0, oMsg, 32) (encW0 K) = true ∧
  sepAll sz (0, K.oCt, oCin - K.oCt) (encW0 K) = true

theorem enc_f {K : KemLay} (hK : K.WF) : (encW K (db K)).all (okW K) = true ∧
    [((0 : Nat), oCin, (K.ctLen : Nat)), (0, oG, 32), (0, oKbar, 32)].all
      (fun w => sepAll (dSz K) w (encW K (db K))) = true ∧
    sepAll (dSz K) (2, 384 * K.k, K.ekLen) (encW0 K) = true ∧
    sepAll (dSz K) (0, oMsg, 32) (encW0 K) = true ∧
    sepAll (dSz K) (0, K.oCt, K.ctLen) (encW0 K) = true := by
  have sc := hK.scr
  have hct : K.ctLen ≤ oCin - K.oCt := Nat.le_sub_of_add_le' hK.ct
  obtain ⟨e1, e2, e3, e4, e5⟩ :=
    (by decide : ∀ k < 5, EncF (kOf k) (dSz (kOf k))) K.k (by have := hK.k4; omega)
  have hW : (encW0 K ++ [((0 : Nat), K.oCt, K.ctLen)]).all
      (fun x => (encW0 K ++ [((0 : Nat), K.oCt, oCin - K.oCt)]).any (inB x)) = true := by
    rw [List.all_append, Bool.and_eq_true]
    refine ⟨List.all_eq_true.mpr fun x hx =>
      List.any_eq_true.mpr ⟨x, List.mem_append_left _ hx, inB_refl x⟩, ?_⟩
    rw [List.all_cons, List.all_nil, Bool.and_true]
    exact List.any_eq_true.mpr ⟨_, List.mem_append_right _ (List.mem_singleton_self _), inB_len hct⟩
  refine ⟨?_, ?_, sepAll_scr e3 sc, sepAll_scr e4 sc, sepAll_left (sepAll_scr e5 sc) (inB_len hct)⟩
  · show (encW0 K ++ [((0 : Nat), K.oCt, K.ctLen)]).all (okW K) = true
    rw [List.all_append, Bool.and_eq_true] at e1 ⊢
    refine ⟨allOkW_of hK e1.1, ?_⟩
    have e := e1.2
    rw [List.all_cons, List.all_nil, Bool.and_true] at e ⊢
    simp only [okWm, okW, Bool.and_eq_true] at e ⊢
    exact ⟨sepB_mono (sepB_scr e.1 sc) (inB_refl _) (inB_len hct),
      sepB_mono (sepB_scr e.2 sc) (inB_refl _) (inB_len hct)⟩
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at e2 ⊢
    exact ⟨sepAll_mono (sepAll_scr e2.1 sc) (inB_len (ct_le hK)) hW,
      sepAll_mono (sepAll_scr e2.2.1 sc) (inB_refl _) hW,
      sepAll_mono (sepAll_scr e2.2.2 sc) (inB_refl _) hW⟩

theorem encPre {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : DP K s₀ s) :
    EncPre K (lay s₀ K) (db K) s := by
  have hK := hp.wf
  obtain ⟨w0, -, w2, -, -⟩ := buf_wr hp
  obtain ⟨-, -, f3, f4, f5⟩ := enc_f hK
  exact ⟨hK, hp.calls, h.env.ctx, h.s10, h.s9, h.s7, f3, f4, f5,
    by rw [h.env.rd, h.env.wr]; exact w2, by rw [h.env.rd, h.env.wr]; exact mem_rd_wr w0,
    by rw [h.env.wr]; exact w0⟩

/-- `ρ` of `dk`. -/
abbrev ρD (K : KemLay) (s₀ : State) : List Byte := ekRho K.p (eK K s₀)

/-- `c'`. -/
abbrev C2 (K : KemLay) (s₀ : State) : List Byte :=
  VG.Proof.MlKem.KPke.ct K.p (aEnc (ρD K s₀) (R1 K s₀)) (eK K s₀) (MM K s₀) (R1 K s₀)

/-- After the re-encryption. -/
structure DQ (K : KemLay) (s₀ s : State) : Prop where
  env : DEnv K s₀ s
  s8 : s.gpr .s8 = (lay s₀ K).A 0 oCin
  s7 : s.gpr .s7 = (lay s₀ K).A 0 K.oCt
  s4 : s.gpr .s4 = if okEnc K.k (ρD K s₀) K.k then 1 else 0
  c : bytesAt s.mem ((lay s₀ K).A 0 oCin) K.ctLen = CT K s₀
  c2 : bytesAt s.mem ((lay s₀ K).A 0 K.oCt) K.ctLen = C2 K s₀
  k1 : bytesAt s.mem ((lay s₀ K).A 0 oG) 32 = K1 K s₀
  kb : bytesAt s.mem ((lay s₀ K).A 0 oKbar) 32 = KB K s₀

theorem ek_of {K : KemLay} {s₀ s : State} (hK : K.WF) (h : DP K s₀ s) :
    bytesAt s.mem ((lay s₀ K).A 2 (384 * K.k)) K.ekLen = eK K s₀ := by
  have hk4 := hK.k4
  have dk : bytesAt s.mem ((lay s₀ K).A 2 0) K.dkLen = DK K s₀ := h.env.dk
  rw [show (lay s₀ K).A 2 (384 * K.k) = (lay s₀ K).A 2 0 + BitVec.ofNat 64 (384 * K.k) by
      rw [ptr_add, Nat.zero_add],
    ← bytesAt_slice _ _ (by simp only [KemLay.ekLen, KemLay.dkLen]; omega :
      384 * K.k + K.ekLen ≤ K.dkLen), dk]
  rfl

theorem reenc_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : DP K s₀ s) :
    WP isa K.encrypt s (DQ K s₀) := by
  have hL := lay_ok hp
  have hK := hp.wf
  have e1 : ekB K (lay s₀ K) (db K) s = eK K s₀ := ek_of hK h
  have eρ : ρE K (lay s₀ K) (db K) s = ρD K s₀ := congrArg (ekRho K.p) e1
  have e2 : mB (lay s₀ K) (db K) s = MM K s₀ := h.m
  have er : rB (lay s₀ K) s = R1 K s₀ := h.r1
  obtain ⟨c1, c2, -, -, -⟩ := enc_f hK
  have sep : ∀ {o l : Nat},
      ((0 : Nat), o, l) ∈ [((0 : Nat), oCin, (K.ctLen : Nat)), (0, oG, 32), (0, oKbar, 32)] →
      sepAll (lay s₀ K).sizes (0, o, l) (encW K (db K)) = true := fun hm =>
    List.all_eq_true.mp c2 _ hm
  refine WP.mono (encrypt_ok (encPre hp h)) fun s' ⟨kp, s4, ct⟩ =>
    ⟨h.env.keep hp kp (by decide) c1, by rw [kp.cs .s8 (by decide) (by decide), h.s8],
      by rw [kp.cs .s7 (by decide) (by decide), h.s7], ?_,
      (Lay.bytes_keep hL kp.frame (sep (by simp)) (by have := ct_le hK; omega)).trans h.c, ?_,
      (Lay.bytes_keep hL kp.frame (sep (by simp)) (by decide)).trans h.k1,
      (Lay.bytes_keep hL kp.frame (sep (by simp)) (by decide)).trans h.kb⟩
  · rw [s4]
    show (if okEnc K.k (ρE K (lay s₀ K) (db K) s) K.k = true then _ else _) = _
    rw [eρ]
  · rw [e1, e2] at ct
    show _ = VG.Proof.MlKem.KPke.ct K.p (aEnc (ρD K s₀) (R1 K s₀)) (eK K s₀) (MM K s₀) (R1 K s₀)
    rw [← eρ, ← er]; exact ct

/-! ## The comparison and the selection -/

theorem covers2 {L : Lay} {s : State} (hc : Ctx L s) {o o' l l' : Nat} (h : o + l ≤ 32768)
    (h' : o' + l' ≤ 32768) : Covers [L.R 0 o l, L.R 0 o' l'] (s.rd ++ s.wr) :=
  fun a n ⟨r, hr, hcn⟩ => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact mem_rd_wr' (hc.cs h _ _ ⟨_, List.mem_singleton_self _, hcn⟩)
    · exact mem_rd_wr' (hc.cs h' _ _ ⟨_, List.mem_singleton_self _, hcn⟩)

/-- After the comparison. -/
structure DR (K : KemLay) (s₀ s : State) : Prop where
  q : DQ K s₀ s
  lt : (s.gpr .t2).toNat < 256
  eq : s.gpr .t2 = 0 ↔ CT K s₀ = C2 K s₀

theorem kept_of {s s' : State} {x : Reg} {W : List Region}
    (cs : ∀ r ∈ preserved, r ≠ x → s'.gpr r = s.gpr r) (sp : s'.sp = s.sp) (rd : s'.rd = s.rd)
    (wr : s'.wr = s.wr) (fr : Frame W s.mem s'.mem) : KeptX [x] W s s' :=
  ⟨fun r hr hx => cs r hr fun e => hx (by rw [e]; exact List.mem_singleton_self _), sp, rd, wr, fr⟩

theorem cmp_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : DQ K s₀ s) :
    WP isa K.compare s (DR K s₀) := by
  have hc := h.env.ctx
  have hK := hp.wf
  have hct : K.oCt + K.ctLen ≤ 32768 := Nat.le_trans hK.ct (by decide)
  have hcin : oCin + K.ctLen ≤ 32768 := hK.cin
  refine WP.mono (compare_ok hK h.s8 h.s7
    (covers2 hc hcin hct)) fun s' ⟨cs, m, rd, wr, sp, lt, eq⟩ => ?_
  have k : KeptX [.s6] ((lay s₀ K).RL []) s s' :=
    kept_of cs sp rd wr (by rw [m]; exact Frame.refl _ _)
  refine ⟨⟨h.env.keep hp k (by decide) rfl, by rw [cs .s8 (by decide) (by decide), h.s8],
    by rw [cs .s7 (by decide) (by decide), h.s7], by rw [cs .s4 (by decide) (by decide), h.s4], by rw [m]; exact h.c, by rw [m]; exact h.c2,
    by rw [m]; exact h.k1, by rw [m]; exact h.kb⟩, lt, ?_⟩
  rw [eq]
  show bytesAt s.mem ((lay s₀ K).A 0 oCin) K.ctLen = bytesAt s.mem ((lay s₀ K).A 0 K.oCt) K.ctLen ↔ _
  rw [h.c, h.c2]

/-- After the mask. -/
structure DS (K : KemLay) (s₀ s : State) : Prop where
  q : DQ K s₀ s
  a0 : s.gpr .a0 = (lay s₀ K).A 0 oG
  a1 : s.gpr .a1 = (lay s₀ K).A 0 oKbar
  a2 : s.gpr .a2 = pKey s₀
  s6 : s.gpr .s6 = BitVec.ofNat 64 32
  t2 : s.gpr .t2 = if decide (CT K s₀ = C2 K s₀) then BitVec.allOnes 64 else 0

theorem mask_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : DR K s₀ s) :
    WP isa (.block selSetup) s (DS K s₀) := by
  have hc := h.q.env.ctx
  refine WP.mono (selSetup_ok (P := (lay s₀ K).ptr 0) (KP := pKey s₀) hc.s11 h.lt h.q.env.key)
    fun s' ⟨g12, g3, g4, g5, g26, cs, m, rd, wr, sp⟩ => ?_
  have k : KeptX [.s6] ((lay s₀ K).RL []) s s' :=
    kept_of cs sp rd wr (by rw [m]; exact Frame.refl _ _)
  refine ⟨⟨h.q.env.keep hp k (by decide) rfl, by rw [cs .s8 (by decide) (by decide), h.q.s8],
    by rw [cs .s7 (by decide) (by decide), h.q.s7], by rw [cs .s4 (by decide) (by decide), h.q.s4], by rw [m]; exact h.q.c,
    by rw [m]; exact h.q.c2, by rw [m]; exact h.q.k1, by rw [m]; exact h.q.kb⟩, g3, g4, g5, g26, ?_⟩
  rw [g12]
  simp only [h.eq, decide_eq_true_eq]

theorem sel_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : DS K s₀ s) :
    WP isa (.loop (.block selBody) (.nonzero .s6)) s fun s' => DEnv K s₀ s' ∧
      s'.gpr .s4 = (if okEnc K.k (ρD K s₀) K.k then 1 else 0) ∧
      bytesAt s'.mem (pKey s₀) 32 = if CT K s₀ = C2 K s₀ then K1 K s₀ else KB K s₀ := by
  have hL := lay_ok hp
  have hK := hp.wf
  have hc := h.q.env.ctx
  obtain ⟨-, w3, -, -, -⟩ := buf_wr hp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, d1, d2, wk⟩ := hash_f hK
  have eZ : (⟨pKey s₀, 32⟩ : Region) = (lay s₀ K).R 3 0 32 := by
    simp only [Lay.R, BitVec.add_zero]; rfl
  refine WP.mono (select_ok (e := decide (CT K s₀ = C2 K s₀))
    (by rw [eZ]; exact Lay.disj hL d1) (by rw [eZ]; exact Lay.disj hL d2)
    (covers2 hc (by decide) (by decide))
    (by rw [eZ, h.q.env.wr]; exact Lay.covers w3 (Nat.le_refl 32))
    h.a0 h.a1 h.a2 h.s6 h.t2) fun s' ⟨cs, rd, wr, sp, fr, b⟩ => ⟨?_, ?_, ?_⟩
  · have eRL : (lay s₀ K).RL [(3, 0, 32)] = [(⟨pKey s₀, 32⟩ : Region)] := by rw [eZ]; rfl
    have k : KeptX [.s6] ((lay s₀ K).RL [(3, 0, 32)]) s s' :=
      kept_of cs sp rd wr (by rw [eRL]; exact fr)
    exact h.q.env.keep hp k (by decide) wk
  · rw [cs .s4 (by decide) (by decide), h.q.s4]
  · rw [b, h.q.k1, h.q.kb]
    by_cases e : CT K s₀ = C2 K s₀ <;> simp [e]

/-! ## The whole function -/

theorem end_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : DEnv K s₀ s) :
    WP isa (.block topEnd) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      s'.gpr .a0 = s.gpr .s4 ∧ s'.mem = s.mem ∧ s'.sp = s₀.sp := by
  obtain ⟨w0, -, -, -, -⟩ := buf_wr hp
  have hK := hp.wf
  refine WP.mono (topEnd_ok h.ctx.s11 hp.alS h.sav (fun o h₁ h₂ => ?_) h.cs)
    fun s' ⟨pr, lr, a0, m, sp, _, _⟩ => ⟨pr, lr, a0, m, sp.trans h.sp⟩
  rw [h.rd, h.wr]
  have scr := hK.scr
  have hb : o + 8 ≤ (lay s₀ K).size 0 := by simp only [lay, Lay.size, List.getD_cons_zero]; omega
  exact mem_rd_wr' (Lay.covers w0 hb _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)

theorem dd_of {K : KemLay} {s₀ s₂ s₃ : State} (hp : Pre K s₀) (h₂ : DEnv K s₀ s₂)
    (g30 : s₂.gpr .s10 = pDk s₀)
    (c₂ : bytesAt s₂.mem ((lay s₀ K).A 0 oCin) K.ctLen = CT K s₀)
    (h₃ : KeptX [.s8] [] s₂ s₃ ∧ s₃.gpr .s8 = s₂.gpr .s11 + BitVec.ofNat 64 oCin ∧
      s₃.mem = s₂.mem) : DD K s₀ s₃ :=
  ⟨h₂.keep hp (W := []) h₃.1 (by decide) rfl,
    by rw [h₃.1.cs .s10 (by decide) (by decide), g30], by rw [h₃.2.1, h₂.ctx.s11],
    by rw [h₃.2.2]; exact c₂⟩

theorem correct {K : KemLay} {s₀ : State} (hp : Pre K s₀) :
    WP isa K.decaps s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      s.gpr .ra = s₀.gpr .ra ∧ s.gpr .a0 = (if okEnc K.k (ρD K s₀) K.k then 1 else 0) ∧
      bytesAt s.mem (pKey s₀) 32 = if CT K s₀ = C2 K s₀ then K1 K s₀ else KB K s₀ := by
  have hL := lay_ok hp
  have hK := hp.wf
  obtain ⟨-, -, -, -, -, -, -, -, m1, m2, k2, r2, -, -, -⟩ := hash_f hK
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨h₁, g30, g28, c₁⟩ => ?_)
  refine WP.seq (WP.mono (copyC_ok hp h₁ g28 c₁) fun s₂ ⟨h₂, g30₂, c₂⟩ => ?_)
  refine WP.seq (WP.mono ptr28_ok fun s₃ h₃ => ?_)
  have d₃ := dd_of hp h₂ (by rw [g30₂, g30]) c₂ h₃
  refine WP.seq (WP.mono (decrypt_ok hp d₃) fun s₄ ⟨d₄, m₄⟩ => ?_)
  refine WP.seq (WP.mono (hashG_ok hp d₄ m₄) fun s₅ ⟨d₅, f₅, k₅, r₅⟩ => ?_)
  refine WP.seq (WP.mono (hashJ_ok hp d₅) fun s₆ ⟨d₆, f₆, kb₆⟩ => ?_)
  have m₆ := (Lay.bytes_keep hL f₆ m1 (by decide)).trans
    ((Lay.bytes_keep hL f₅ m2 (by decide)).trans m₄)
  have k₆ := (Lay.bytes_keep hL f₆ k2 (by decide)).trans k₅
  have r₆ := (Lay.bytes_keep hL f₆ r2 (by decide)).trans r₅
  refine WP.seq (WP.mono (ptrs_dp hp d₆ m₆ k₆ r₆ kb₆) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (reenc_ok hp h₇) fun s₈ h₈ => ?_)
  refine WP.seq (WP.mono (cmp_ok hp h₈) fun s₉ h₉ => ?_)
  refine WP.seq (WP.mono (mask_ok hp h₉) fun s₁₀ h₁₀ => ?_)
  refine WP.seq (WP.mono (sel_ok hp h₁₀) fun s₁₁ ⟨h₁₁, s4, key⟩ => ?_)
  exact WP.mono (end_ok hp h₁₁) fun s ⟨pr, lr, a0, m', sp'⟩ =>
    ⟨pr, sp', lr, by rw [a0, s4], by rw [m']; exact key⟩

end VG.Proof.MlKem.RISCV64.Decaps
