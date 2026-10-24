module

public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Encrypt
public import VerifiedGarbage.Proof.MlKem.PPC64LE.HashTop
public import VerifiedGarbage.Proof.MlKem.PPC64LE.TopSave
import VerifiedGarbage.Proof.MlKem.PPC64LE.CmpSel
import VerifiedGarbage.Proof.MlKem.PPC64LE.Loops
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.PPC64LE.RowSum
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# ML-KEM on PPC64LE: decapsulation, correctness

As on 32-bit ARM (`Proof/MlKem/Arm/Decaps.lean`): `K.decaps` for any
parameter set `K` (`KemLay.WF`).

The buffers of the function (`lay`): `scratch`, the 48 bytes below the stack
pointer, `dk` and `key`; `c`, which may overlap `dk`, is only read by its
copy into `scratch`, with a layout of its own (`layC`). What every phase
keeps (`DEnv`), and the phases: the setup, `c` copied, K-PKE.Decrypt into
`m'`, `G(m' ‖ h)` into `K' ‖ r'`, `J(z ‖ c)` into `K̄`, the re-encryption
`c'` (`Enc.encrypt_ok`), the comparison of `c` and `c'`, and the selection
of `K'` or `K̄` into `key`.
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE.Decaps

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.PPC64LE.Enc
open VG.Impl.Sha3.PPC64LE.Stream (mov)

section
variable (s₀ : State)

abbrev pDk : Addr := s₀.gpr .r3
abbrev pC : Addr := s₀.gpr .r4
abbrev pKey : Addr := s₀.gpr .r5
abbrev pScr : Addr := s₀.gpr .r6

/-- The buffers: `scratch`, the 48 bytes below the stack pointer, `dk` and `key`. -/
def lay (K : KemLay) : Lay :=
  ⟨fun i => [pScr s₀, s₀.sp - BitVec.ofNat 64 48, pDk s₀, pKey s₀].getD i 0,
    [K.scratch, 48, K.dkLen, 32]⟩

/-- The buffers of the copy of `c`: `scratch`, the stack and `c`. -/
def layC (K : KemLay) : Lay :=
  ⟨fun i => [pScr s₀, s₀.sp - BitVec.ofNat 64 48, pC s₀].getD i 0, [K.scratch, 48, K.ctLen]⟩

end

/-- The sizes of the buffers. -/
abbrev dSz (K : KemLay) : List Nat := [K.scratch, 48, K.dkLen, 32]

theorem lay_sizes (K : KemLay) (s₀ : State) : (lay s₀ K).sizes = dSz K := rfl
theorem layC_sizes (K : KemLay) (s₀ : State) : (layC s₀ K).sizes = [K.scratch, 48, K.ctLen] := rfl
theorem lay_ptr0 (K : KemLay) (s₀ : State) : (lay s₀ K).ptr 0 = pScr s₀ := rfl
theorem layC_ptr0 (K : KemLay) (s₀ : State) : (layC s₀ K).ptr 0 = pScr s₀ := rfl

/-- The precondition of the contract. -/
structure Pre (K : KemLay) (s : State) : Prop where
  wf : K.WF
  calls : K.CallsOk
  sp48 : 48 ≤ s.sp.toNat
  rd : s.rd = [⟨pDk s, K.dkLen⟩, ⟨pC s, K.ctLen⟩]
  wr : s.wr = [⟨pKey s, 32⟩, ⟨pScr s, K.scratch⟩]
  d_dk_key : (⟨pDk s, K.dkLen⟩ : Region).Disjoint ⟨pKey s, 32⟩
  d_dk_scr : (⟨pDk s, K.dkLen⟩ : Region).Disjoint ⟨pScr s, K.scratch⟩
  d_c_key : (⟨pC s, K.ctLen⟩ : Region).Disjoint ⟨pKey s, 32⟩
  d_c_scr : (⟨pC s, K.ctLen⟩ : Region).Disjoint ⟨pScr s, K.scratch⟩
  d_key_scr : (⟨pKey s, 32⟩ : Region).Disjoint ⟨pScr s, K.scratch⟩
  b_dk : (below s.sp 48).Disjoint ⟨pDk s, K.dkLen⟩
  b_c : (below s.sp 48).Disjoint ⟨pC s, K.ctLen⟩
  b_key : (below s.sp 48).Disjoint ⟨pKey s, 32⟩
  b_scr : (below s.sp 48).Disjoint ⟨pScr s, K.scratch⟩
  f_dk : (pDk s).toNat + K.dkLen ≤ 2 ^ 64
  f_c : (pC s).toNat + K.ctLen ≤ 2 ^ 64
  f_key : (pKey s).toNat + 32 ≤ 2 ^ 64
  f_scr : (pScr s).toNat + K.scratch ≤ 2 ^ 64

section
variable {K : KemLay} {s₀ : State} (hp : Pre K s₀)
include hp

theorem stack_fit : (s₀.sp - BitVec.ofNat 64 48).toNat + 48 ≤ 2 ^ 64 := by
  have := hp.sp48
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

/-- What every phase keeps: `scratch`, our caller's registers and the pointer
`key` in `scratch`, and `dk`. -/
structure DEnv (K : KemLay) (s₀ s : State) : Prop where
  ctx : Ctx (lay s₀ K) s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cs : ∀ r ∈ preserved, r ∉ savedTop → s.gpr r = s₀.gpr r
  sav : TopSaved s.mem (pScr s₀) s₀
  key : s.mem.readW ((lay s₀ K).A 0 oExtra) 64 = pKey s₀
  dk : bytesAt s.mem ((lay s₀ K).A 2 0) K.dkLen = bytesAt s₀.mem ((lay s₀ K).A 2 0) K.dkLen

/-! ### The facts on the offsets, once for any parameter set

They depend on the parameter set only through `k`, the size of `scratch`, and
the length of `c`: each is decided for every `k ≤ 4` with a `scratch` of
32 KiB (`kOf`) and the longest `c` that fits (8192 bytes from `oCin`), and
holds for a bigger `scratch` (`sepB_scr`) and a shorter `c` (`sepB_mono`). -/

/-- What a phase may change, with the sizes `sz` of the buffers: apart from
the saved registers, the pointer `key` and `dk`. -/
abbrev okWm (K : KemLay) (sz : List Nat) (w : Nat × Nat × Nat) : Bool :=
  sepB sz (0, 840, 72) w && (sepB sz (0, oExtra, 8) w && sepB sz (2, 0, K.dkLen) w)

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
  have := hK.cin; simp only [oCin] at this; omega

theorem ct_pos {K : KemLay} (hK : K.WF) : 0 < K.ctLen := by
  have h1 := hK.du1
  have h2 := hK.k1
  have : 0 < K.uLen * K.k := Nat.mul_pos (by simp only [KemLay.uLen]; omega) (by omega)
  simp only [KemLay.ctLen]; omega

theorem okW_of {K : KemLay} (hK : K.WF) {w : Nat × Nat × Nat} (h : okWm K (dSz (kOf K.k)) w = true) :
    okW K w = true := by
  simp only [okWm, okW, Bool.and_eq_true] at h ⊢
  exact ⟨sepB_scr h.1 hK.scr, sepB_scr h.2.1 hK.scr, sepB_scr h.2.2 hK.scr⟩

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

theorem vIn_fit : oCin + K.uLen * K.k + 32 * K.dv ≤ 32768 := by
  have h := hK.cin
  rw [ctLen_split, ← Nat.add_assoc] at h
  exact h

end

/-- The buffer of each pointer register. -/
def didx : Reg → Nat
  | .r30 => 2 | _ => 0

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

theorem saveR_eq (K : KemLay) (s₀ : State) : saveR (pScr s₀) = (lay s₀ K).R 0 840 72 := rfl

theorem DEnv.keep {K : KemLay} {s₀ s s' : State} (hp : Pre K s₀) (h : DEnv K s₀ s) {xs : List Reg}
    {W : List (Nat × Nat × Nat)} (hk : KeptX xs ((lay s₀ K).RL W) s s')
    (hx : ∀ x ∈ xs, x ∈ savedTop ∧ x ≠ .r31) (hW : W.all (okW K) = true) : DEnv K s₀ s' := by
  have hL := lay_ok hp
  have hK := hp.wf
  have h1 : sepAll (lay s₀ K).sizes (0, 840, 72) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw
      simp only [okW, okWm, Bool.and_eq_true] at this; exact this.1
  have h2 : sepAll (lay s₀ K).sizes (0, oExtra, 8) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw
      simp only [okW, okWm, Bool.and_eq_true] at this; exact this.2.1
  have h3 : sepAll (lay s₀ K).sizes (2, 0, K.dkLen) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw
      simp only [okW, okWm, Bool.and_eq_true] at this; exact this.2.2
  have n31 : Reg.r31 ∉ xs := fun hm => (hx _ hm).2 rfl
  refine ⟨hk.ctx n31 h.ctx, hk.rd.trans h.rd, hk.wr.trans h.wr, hk.sp.trans h.sp, fun r hr hs => ?_,
    h.sav.keep hk.frame (by rw [saveR_eq K]; exact Lay.disjAll hL h1), ?_, ?_⟩
  · rw [hk.cs r hr (fun hm => hs (hx r hm).1), h.cs r hr hs]
  · rw [hk.frame.readW (r := (lay s₀ K).R 0 oExtra 8) (Region.contains_self _ _)
      (Lay.disjAll hL h2) (by decide)]
    exact h.key
  · rw [Lay.bytes_keep hL hk.frame h3 (by have := hK.k4; simp only [KemLay.dkLen]; omega)]; exact h.dk

theorem buf_wr {K : KemLay} {s₀ : State} (hp : Pre K s₀) :
    (lay s₀ K).buf 0 ∈ s₀.wr ∧ (lay s₀ K).buf 3 ∈ s₀.wr ∧ (lay s₀ K).buf 2 ∈ s₀.rd ++ s₀.wr ∧
      (layC s₀ K).buf 2 ∈ s₀.rd ++ s₀.wr ∧ (layC s₀ K).buf 0 ∈ s₀.wr := by
  rw [hp.wr, hp.rd]; simp [Lay.buf, lay, layC]

/-! ## The setup -/

theorem setup_ok {K : KemLay} {s₀ : State} (hp : Pre K s₀) :
    WP isa (.block decapsSetup) s₀ fun s => DEnv K s₀ s ∧ s.gpr .r30 = pDk s₀ ∧ s.gpr .r28 = pC s₀ ∧
      bytesAt s.mem ((layC s₀ K).A 2 0) K.ctLen = bytesAt s₀.mem ((layC s₀ K).A 2 0) K.ctLen := by
  have hL := lay_ok hp
  have hK := hp.wf
  have scr := hK.scr
  obtain ⟨w0, -, -, -, -⟩ := buf_wr hp
  have wS : ∀ {o n : Nat}, o + n ≤ 32768 → InRegions s₀.wr (pScr s₀ + BitVec.ofNat 64 o) n := fun h =>
    Lay.covers w0 (by simp only [lay, Lay.size, List.getD_cons_zero]; omega) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [decapsSetup, WP.block_append_iff]
  refine WP.mono (topSave_ok (.inl rfl) rfl fun o _ h₂ => wS (by omega))
    fun s₁ ⟨sav, fr, g₁, lr₁, rd₁, wr₁, sp₁⟩ => ?_
  have g3 : s₁.gpr .r3 = pDk s₀ := g₁ _ (by decide)
  have g4 : s₁.gpr .r4 = pC s₀ := g₁ _ (by decide)
  have g5 : s₁.gpr .r5 = pKey s₀ := g₁ _ (by decide)
  have g6 : s₁.gpr .r6 = pScr s₀ := g₁ _ (by decide)
  have o1 : oExtra % 8 = 0 ∧ oExtra < 32768 := by decide
  have i912 : InRegions s₁.wr (pScr s₀ + BitVec.ofNat 64 oExtra) 8 := by rw [wr₁]; exact wS (by decide)
  have hmv : WP isa (.block [.store .d .r5 .r6 oExtra, mov .r30 .r3, mov .r28 .r4, mov .r31 .r6]) s₁
      fun s => s.gpr .r30 = pDk s₀ ∧ s.gpr .r28 = pC s₀ ∧ s.gpr .r31 = pScr s₀ ∧
      (∀ r ∈ preserved, r ∉ savedTop → s.gpr r = s₁.gpr r) ∧
      s.mem = s₁.mem.writeW (pScr s₀ + BitVec.ofNat 64 oExtra) (pKey s₀) ∧
      s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.sp = s₁.sp := by
    prun [exec_std, o1, g3, g4, g5, g6, i912]
    and_intros
    all_goals first
      | exact trivial
      | rfl
      | (intro r hr hs
         simp only [savedTop, List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
         obtain ⟨a24, a25, a26, a27, a28, a29, a30, a31⟩ := hs
         simp only [RegUpd.gpr_write, a28, a30, a31, ite_false])
  refine WP.mono hmv fun s ⟨g30, g28, g31, cs, m, rd, wr, sp⟩ => ?_
  have c912 : ((lay s₀ K).R 0 oExtra 8).Contains ((lay s₀ K).A 0 oExtra) (64 / 8) :=
    Region.contains_self _ _
  have fr' : Frame ((lay s₀ K).RL [(0, 840, 72), (0, oExtra, 8)]) s₀.mem s.mem := by
    rw [m]
    exact (fr.mono (fun r hr => by rw [List.mem_singleton] at hr; subst hr; simp [saveR_eq K])).writeW
      (by simp) _ c912
  have dkf : K.dkLen ≤ 2 ^ 64 := by have := hK.k4; simp only [KemLay.dkLen]; omega
  refine ⟨⟨⟨hL, scr, rfl, by simp [lay], g31, by rw [sp, sp₁]; exact hp.sp48, by rw [sp, sp₁]; rfl,
    by rw [wr, wr₁, hp.wr]; simp [lay]⟩, rd.trans rd₁, wr.trans wr₁, sp.trans sp₁, fun r hr hs => ?_,
    ?_, ?_, ?_⟩, g30, g28, ?_⟩
  · rw [cs r hr hs]; exact g₁ r (by rintro rfl; simp [preserved] at hr)
  · rw [m]
    exact sav.keep ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c912) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [saveR_eq K]; exact Lay.disj hL (by ddecide))
  · rw [m]; exact Mem.readW_writeW_self64 _ _ _
  · exact Lay.bytes_keep hL fr' (by ddecide) dkf
  · have frC : Frame ((layC s₀ K).RL [(0, 840, 72), (0, oExtra, 8)]) s₀.mem s.mem := by
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
    (h28 : s.gpr .r28 = pC s₀) (hc : bytesAt s.mem ((layC s₀ K).A 2 0) K.ctLen = CT K s₀) :
    WP isa (copy .r28 0 .r31 oCin K.ctLen) s fun s' => DEnv K s₀ s' ∧ s'.gpr .r30 = s.gpr .r30 ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oCin) K.ctLen = CT K s₀ := by
  have hK := hp.wf
  obtain ⟨-, -, -, wC, wC0⟩ := buf_wr hp
  refine WP.mono (copyL (layC_ok hp) (i := 2) (j := 0) (by decide) (by decide) h28
    (by rw [h.ctx.r31, lay_ptr0, layC_ptr0]) (by decide) (by decide) (by have := ct_le hK; omega)
    (ct_pos hK) (by rw [layC_sizes]; ddecide) (by rw [h.rd, h.wr]; exact wC)
    (by rw [h.wr]; exact wC0)) fun s' ⟨k, e⟩ => ⟨?_, k.cs .r30 (by decide), ?_⟩
  · have k' : Kept ((lay s₀ K).RL [(0, oCin, K.ctLen)]) s s' := by
      simpa only [Lay.RL, List.map_cons, List.map_nil, Lay.R, lay_ptr0, layC_ptr0] using k
    exact h.keep hp (k'.x []) (by simp) (by ddecide)
  · rw [← layA0, e, hc]

theorem ptr28_ok {s : State} :
    WP isa (.block [.addi .r28 .r31 oCin]) s fun s' =>
      KeptX [.r28] [] s s' ∧ s'.gpr .r28 = s.gpr .r31 + BitVec.ofNat 64 oCin ∧ s'.mem = s.mem := by
  have e1 : oCin < 32768 := by decide
  prun [e1]
  refine ⟨⟨fun r _ hx => ?_, rfl, rfl, rfl, Frame.refl _ _⟩, trivial⟩
  exact RegUpd.gpr_write_of_ne _ _ fun e => hx (by rw [e]; exact List.mem_singleton_self _)

/-- What decryption keeps: `DEnv`, `dk` in `r30`, and the copy of `c` in `r28`. -/
structure DD (K : KemLay) (s₀ s : State) : Prop where
  env : DEnv K s₀ s
  r30 : s.gpr .r30 = pDk s₀
  r28 : s.gpr .r28 = (lay s₀ K).A 0 oCin
  c : bytesAt s.mem ((lay s₀ K).A 0 oCin) K.ctLen = CT K s₀

theorem DD.keep {K : KemLay} {s₀ s s' : State} (hp : Pre K s₀) (h : DD K s₀ s) {xs : List Reg}
    {W : List (Nat × Nat × Nat)} (hk : KeptX xs ((lay s₀ K).RL W) s s')
    (hx : ∀ x ∈ xs, x ∈ savedTop ∧ x ≠ .r30 ∧ x ≠ .r28 ∧ x ≠ .r31) (hW : W.all (okD K) = true) :
    DD K s₀ s' := by
  have hK := hp.wf
  have w1 : W.all (okW K) = true := List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp hW w hw; simp only [okD, Bool.and_eq_true] at this; exact this.1
  have w2 : sepAll (lay s₀ K).sizes (0, oCin, K.ctLen) W = true := List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp hW w hw; simp only [okD, Bool.and_eq_true] at this; exact this.2
  have nx : ∀ r, r = .r30 ∨ r = .r28 ∨ r = .r31 → r ∉ xs := fun r hr hm => by
    obtain ⟨-, a, b, c⟩ := hx r hm
    rcases hr with rfl | rfl | rfl <;> simp_all
  refine ⟨h.env.keep hp hk (fun x hm => ⟨(hx x hm).1, (hx x hm).2.2.2⟩) w1, ?_, ?_, ?_⟩
  · rw [hk.cs .r30 (by decide) (nx _ (by simp)), h.r30]
  · rw [hk.cs .r28 (by decide) (nx _ (by simp)), h.r28]
  · rw [Lay.bytes_keep (lay_ok hp) hk.frame w2 (by have := ct_le hK; omega)]; exact h.c

/-! ## `û` -/

theorem uArgs_ok {K : KemLay} (hK : K.WF) {s : State} {P C : Addr} {j : Nat} (h31 : s.gpr .r31 = P)
    (h28 : s.gpr .r28 = C) (h26 : s.gpr .r26 = BitVec.ofNat 64 j) :
    WP isa (.block (atMul .r3 .r28 .r26 K.uLen ++ ([.li .r4 K.uLen, .li .r5 K.du] : List Instr) ++
      slotAt .r6 .r26 (oPoly K.k))) s fun s' => Only s s' ∧
      s'.gpr .r3 = C + BitVec.ofNat 64 (K.uLen * j) ∧ s'.gpr .r4 = BitVec.ofNat 64 (32 * K.du) ∧
      s'.gpr .r5 = BitVec.ofNat 64 K.du ∧
      s'.gpr .r6 = P + BitVec.ofNat 64 j <<< 10 + BitVec.ofNat 64 (oPoly K.k) := by
  have e1 : K.uLen < 32768 := by have := hK.du; simp only [KemLay.uLen]; omega
  have e2 : K.du < 32768 := by have := hK.du; omega
  have e3 : oPoly K.k < 32768 := by offs
  have e4 : K.uLen = 32 * K.du := rfl
  prun [atMul, slotAt, exec_mul, List.cons_append, List.nil_append, e1, e2, e3, e4, h31, h28, h26,
    mul_eq]
  exact ⟨Only.of_writes rfl rfl rfl rfl (by pres_tac), trivial⟩

/-- `û` for the first `j` rows, from `s₁`. -/
structure UInv (K : KemLay) (s₀ s₁ : State) (j : Nat) (s : State) : Prop where
  kx : KeptX [.r26] ((lay s₀ K).RL [(0, oPoly K.k, 1024 * K.k), (0, K.oNtt, 1024)]) s₁ s
  r26 : s.gpr .r26 = BitVec.ofNat 64 j
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

theorem u1_ok : WP isa (.block (atMul .r3 .r28 .r26 K.uLen ++
      ([.li .r4 K.uLen, .li .r5 K.du] : List Instr) ++ slotAt .r6 .r26 (oPoly K.k))) s fun s' =>
      Only s s' ∧ s'.gpr .r3 = (lay s₀ K).A 0 (oCin + K.uLen * j) ∧
      s'.gpr .r4 = BitVec.ofNat 64 (32 * K.du) ∧ s'.gpr .r5 = BitVec.ofNat 64 K.du ∧
      s'.gpr .r6 = (lay s₀ K).A 0 (oPoly (K.k + j)) := by
  have hK := hp.wf
  have hc := h.kx.ctx (by decide) h₁.env.ctx
  have g28 : s.gpr .r28 = (lay s₀ K).A 0 oCin := by
    rw [h.kx.cs .r28 (by decide) (by decide), h₁.r28]
  refine WP.mono (uArgs_ok hK hc.r31 g28 h.r26) fun s' ⟨o, a3, a4, a5, a6⟩ => ⟨o, ?_, a4, a5, ?_⟩
  · rw [a3]; exact ptr_add _ _ _
  · rw [a6, slot_eq _ (by offs), show oPoly K.k + 1024 * j = oPoly (K.k + j) by offs]

theorem u2_ok {s' : State} (o : Only s s')
    (a3 : s'.gpr .r3 = (lay s₀ K).A 0 (oCin + K.uLen * j))
    (a4 : s'.gpr .r4 = BitVec.ofNat 64 (32 * K.du)) (a5 : s'.gpr .r5 = BitVec.ofNat 64 K.du)
    (a6 : s'.gpr .r6 = (lay s₀ K).A 0 (oPoly (K.k + j))) : WP isa K.callDU s' (UB K s₀ j s) := by
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
      (by have := hK.ct; simp only [oCin, KemLay.uLen, KemLay.oCt, oPoly] at hcin u1 this ⊢; omega))
    (mem_rd_wr hc.cw) hc.cw fun s'' k p => ⟨(o.x _ _).trans (k.x _), ?_⟩
  rw [hcb] at p; exact p

theorem u3_ok {s₂ : State} (r : UB K s₀ j s s₂) :
    WP isa (.block (slotAt .r3 .r26 (oPoly K.k) ++ ([.addi .r4 .r31 K.oNtt] : List Instr))) s₂
      fun s₃ => UB K s₀ j s s₃ ∧ s₃.gpr .r3 = (lay s₀ K).A 0 (oPoly (K.k + j)) ∧
        s₃.gpr .r4 = (lay s₀ K).A 0 K.oNtt := by
  have hK := hp.wf
  have hc₂ := r.kx.ctx (by decide) (h.kx.ctx (by decide) h₁.env.ctx)
  have g26 : s₂.gpr .r26 = BitVec.ofNat 64 j := by
    rw [r.kx.cs .r26 (by decide) (by simp), h.r26]
  refine WP.mono (nttArgs_ok hK hc₂.r31 g26) fun s₃ ⟨o, a3, a4⟩ =>
    ⟨⟨r.kx.trans (o.x _ _), by rw [o.mem]; exact r.p⟩, ?_, a4⟩
  rw [a3, slot_eq _ (by offs), show oPoly K.k + 1024 * j = oPoly (K.k + j) by offs]

theorem u4_ok {s₃ : State} (r : UB K s₀ j s s₃)
    (a3 : s₃.gpr .r3 = (lay s₀ K).A 0 (oPoly (K.k + j)))
    (a4 : s₃.gpr .r4 = (lay s₀ K).A 0 K.oNtt) : WP isa callNtt s₃ (UD K s₀ j s) := by
  have hK := hp.wf
  have hc₃ := r.kx.ctx (by decide) (h.kx.ctx (by decide) h₁.env.ctx)
  exact nttL (lay_ok hp) a3 a4 (hc₃.sep00 (by offs) (by offs) (by kdecide)) hc₃.cw hc₃.cw r.p
    fun s₄ k p => ⟨(r.kx.monoL (by simp)).trans (k.x _), p⟩

theorem u5_ok {s₄ : State} (r : UD K s₀ j s s₄) :
    WP isa (.block (count .r26 K.k)) s₄ fun s' =>
      UInv K s₀ s₁ (j + 1) s' ∧ (s'.gpr .r0 != 0) = decide (j + 1 ≠ K.k) := by
  have hK := hp.wf
  have k4 := hK.k4
  obtain ⟨c1, c2, -⟩ := u_facts hK hj
  have g26 : s₄.gpr .r26 = BitVec.ofNat 64 j := by
    rw [r.kx.cs .r26 (by decide) (by simp), h.r26]
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
    UInv K s₀ s₁ (j + 1) s' ∧ (s'.gpr .r0 != 0) = decide (j + 1 ≠ K.k) :=
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
theorem dU_init {s₁ : State} : WP isa (.block [.li .r26 0]) s₁ (UInv K s₀ s₁ 0) :=
  WP.mono (li_ok .r26 (N := 0) (by decide)) fun _ ⟨k, g, _⟩ =>
    ⟨k.mono (fun _ h => absurd h List.not_mem_nil), g, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩

theorem dU_done {s₁ s : State} (h₁ : DD K s₀ s₁) (h : UInv K s₀ s₁ K.k s) : DD K s₀ s :=
  h₁.keep hp h.kx (by decide) (dec_f hp.wf).1

theorem dT_pre {s : State} (h : DD K s₀ s) :
    Ctx (lay s₀ K) s ∧ s.gpr .r30 = (lay s₀ K).A 2 0 ∧
      sepAll (lay s₀ K).sizes (2, 0, 384 * K.k) [(0, 2048, 1024 * K.k)] = true ∧
      (lay s₀ K).buf 2 ∈ s.rd ++ s.wr := by
  have hK := hp.wf
  obtain ⟨-, -, w2, -, -⟩ := buf_wr hp
  exact ⟨h.env.ctx, by rw [h.r30]; exact (BitVec.add_zero _).symm, by ddecide,
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

theorem dArgs_ok {s : State} {f : Poly} (h : DV K s₀ f s) {o o' : Nat} (he : o < 32768)
    (he' : o' < 32768) :
    WP isa (.block [.addi .r3 .r31 o, .addi .r4 .r31 o']) s fun s' =>
      (DV K s₀ f s' ∧ s'.mem = s.mem) ∧ s'.gpr .r3 = (lay s₀ K).A 0 o ∧
      s'.gpr .r4 = (lay s₀ K).A 0 o' :=
  WP.mono (accArgs_ok h.1.env.ctx.r31 he he') fun _ ⟨o₁, a3, a4⟩ =>
    ⟨⟨⟨h.1.keep hp (xs := []) (W := []) (o₁.x _ _) (by simp) rfl, by rw [o₁.mem]; exact h.2⟩,
      o₁.mem⟩, a3, a4⟩

theorem dInv_ok {s : State} {f : Poly} (h : DV K s₀ f s)
    (a3 : s.gpr .r3 = (lay s₀ K).A 0 K.oAcc) (a4 : s.gpr .r4 = (lay s₀ K).A 0 K.oNtt) :
    WP isa callNttInv s (DV K s₀ (nttInv f)) := by
  have hK := hp.wf
  have hc := h.1.env.ctx
  have hw := (dec_f hK).2.2.2.1
  exact nttInvL (lay_ok hp) a3 a4 (hc.sep00 (oAcc_fit hK) (oNtt_fit hK) (.inl (oAcc_le_oNtt hK)))
    hc.cw hc.cw h.2 fun s' k p => ⟨h.1.keep hp (k.x []) (by simp) hw, p⟩

omit hp in
theorem vDArgs_ok (hK : K.WF) {s : State} {P C : Addr} (h31 : s.gpr .r31 = P) (h28 : s.gpr .r28 = C) :
    WP isa (.block [.addi .r3 .r28 (K.uLen * K.k), .li .r4 K.vLen, .li .r5 K.dv,
      .addi .r6 .r31 (oPoly (3 * K.k))]) s fun s' => Only s s' ∧
      s'.gpr .r3 = C + BitVec.ofNat 64 (K.uLen * K.k) ∧ s'.gpr .r4 = BitVec.ofNat 64 (32 * K.dv) ∧
      s'.gpr .r5 = BitVec.ofNat 64 K.dv ∧ s'.gpr .r6 = P + BitVec.ofNat 64 (oPoly (3 * K.k)) := by
  have e1 : K.uLen * K.k < 32768 := by
    have := hK.du; have := hK.k4
    have : K.uLen ≤ 352 := by simp only [KemLay.uLen]; omega
    calc K.uLen * K.k ≤ 352 * 4 := Nat.mul_le_mul this (by omega)
      _ < 32768 := by omega
  have e2 : K.vLen < 32768 := by have := hK.dv; simp only [KemLay.vLen]; omega
  have e3 : K.dv < 32768 := by have := hK.dv; omega
  have e4 : oPoly (3 * K.k) < 32768 := by offs
  have e5 : K.vLen = 32 * K.dv := rfl
  prun [e1, e2, e3, e4, e5, h31, h28]
  exact ⟨Only.of_writes rfl rfl rfl rfl (by pres_tac), trivial⟩

theorem dV1_ok {s : State} {f : Poly} (h : DV K s₀ f s) :
    WP isa (.block [.addi .r3 .r28 (K.uLen * K.k), .li .r4 K.vLen, .li .r5 K.dv,
      .addi .r6 .r31 (oPoly (3 * K.k))]) s fun s' => DV K s₀ f s' ∧
      s'.gpr .r3 = (lay s₀ K).A 0 (oCin + K.uLen * K.k) ∧
      s'.gpr .r4 = BitVec.ofNat 64 (32 * K.dv) ∧ s'.gpr .r5 = BitVec.ofNat 64 K.dv ∧
      s'.gpr .r6 = (lay s₀ K).A 0 (oPoly (3 * K.k)) :=
  WP.mono (vDArgs_ok hp.wf h.1.env.ctx.r31 h.1.r28) fun _ ⟨o, a3, a4, a5, a6⟩ =>
    ⟨⟨h.1.keep hp (xs := []) (W := []) (o.x _ _) (by simp) rfl, by rw [o.mem]; exact h.2⟩,
      by rw [a3]; exact ptr_add _ _ _, a4, a5, a6⟩

theorem dV2_ok {s : State} {f : Poly} (h : DV K s₀ f s)
    (a3 : s.gpr .r3 = (lay s₀ K).A 0 (oCin + K.uLen * K.k))
    (a4 : s.gpr .r4 = BitVec.ofNat 64 (32 * K.dv)) (a5 : s.gpr .r5 = BitVec.ofNat 64 K.dv)
    (a6 : s.gpr .r6 = (lay s₀ K).A 0 (oPoly (3 * K.k))) :
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
    (mem_rd_wr hc.cw) hc.cw fun s' k p => ⟨⟨h.1.keep hp (k.x []) (by simp) (dec_f hK).2.2.2.2.1, ?_⟩, ?_⟩
  · exact Lay.polyIs_keep (lay_ok hp) k.frame
      (hc.sepAll0 (oAcc_fit hK) (by have := hK.k4; kdecide)) h.2
  · rw [hcb] at p; exact p

theorem dV4_ok {s : State} {f : Poly} (h : DV K s₀ f s)
    (hv : PolyIs s.mem ((lay s₀ K).A 0 (oPoly (3 * K.k))) (VG.Proof.MlKem.KPke.dcV K.p (CT K s₀)))
    (a3 : s.gpr .r3 = (lay s₀ K).A 0 (oPoly (3 * K.k)))
    (a4 : s.gpr .r4 = (lay s₀ K).A 0 K.oAcc) :
    WP isa callSub s fun s' => DD K s₀ s' ∧
      PolyIs s'.mem ((lay s₀ K).A 0 (oPoly (3 * K.k)))
        (sub (VG.Proof.MlKem.KPke.dcV K.p (CT K s₀)) f) := by
  have hK := hp.wf
  have hc := h.1.env.ctx
  exact subL (lay_ok hp) a3 a4 (hc.sep00 (oP3_fit hK) (oAcc_fit hK) (.inl (oP3_le_oAcc hK))) hc.cw
    (mem_rd_wr hc.cw)
    hv h.2 fun s' k p => ⟨h.1.keep hp (k.x []) (by simp) (dec_f hK).2.2.2.2.1, p⟩

omit hp in
theorem mArgs_ok (hK : K.WF) {s : State} {P : Addr} (h31 : s.gpr .r31 = P) :
    WP isa (.block [.addi .r3 .r31 (oPoly (3 * K.k)), .li .r4 1, .addi .r5 .r31 oMsg,
      .li .r6 32]) s fun s' => Only s s' ∧ s'.gpr .r3 = P + BitVec.ofNat 64 (oPoly (3 * K.k)) ∧
      s'.gpr .r4 = BitVec.ofNat 64 1 ∧ s'.gpr .r5 = P + BitVec.ofNat 64 oMsg ∧
      s'.gpr .r6 = BitVec.ofNat 64 (32 * 1) := by
  have e1 : oPoly (3 * K.k) < 32768 := by offs
  have e2 : oMsg < 32768 := by decide
  prun [e1, e2, h31]
  exact ⟨Only.of_writes rfl rfl rfl rfl (by pres_tac), trivial⟩

theorem dM1_ok {s : State} {g : Poly} (h : DD K s₀ s)
    (hg : PolyIs s.mem ((lay s₀ K).A 0 (oPoly (3 * K.k))) g) :
    WP isa (.block [.addi .r3 .r31 (oPoly (3 * K.k)), .li .r4 1, .addi .r5 .r31 oMsg,
      .li .r6 32]) s fun s' => (DD K s₀ s' ∧ PolyIs s'.mem ((lay s₀ K).A 0 (oPoly (3 * K.k))) g) ∧
      s'.gpr .r3 = (lay s₀ K).A 0 (oPoly (3 * K.k)) ∧ s'.gpr .r4 = BitVec.ofNat 64 1 ∧
      s'.gpr .r5 = (lay s₀ K).A 0 oMsg ∧ s'.gpr .r6 = BitVec.ofNat 64 (32 * 1) :=
  WP.mono (mArgs_ok hp.wf h.env.ctx.r31) fun _ ⟨o, a3, a4, a5, a6⟩ =>
    ⟨⟨h.keep hp (xs := []) (W := []) (o.x _ _) (by simp) rfl, by rw [o.mem]; exact hg⟩, a3, a4, a5, a6⟩

theorem dM2_ok {s : State} {g : Poly}
    (h : DD K s₀ s ∧ PolyIs s.mem ((lay s₀ K).A 0 (oPoly (3 * K.k))) g)
    (a3 : s.gpr .r3 = (lay s₀ K).A 0 (oPoly (3 * K.k))) (a4 : s.gpr .r4 = BitVec.ofNat 64 1)
    (a5 : s.gpr .r5 = (lay s₀ K).A 0 oMsg) (a6 : s.gpr .r6 = BitVec.ofNat 64 (32 * 1)) :
    WP isa callCompress s fun s' => DD K s₀ s' ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oMsg) 32 = compressEncode 1 g := by
  have hK := hp.wf
  have hc := h.1.env.ctx
  exact compressL (lay_ok hp) a3 a4 a5 a6 (by decide)
    (hc.sep00 (oP3_fit hK) (by decide) (.inr (oMsg_le_oP3 hK)))
    (mem_rd_wr hc.cw) hc.cw h.2 fun s' k p =>
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
  refine WP.seq (WP.mono (dArgs_ok hp h₆ (o := K.oAcc) (o' := K.oNtt) (by offs) (by offs))
    fun s₇ ⟨h₇, a3, a4⟩ => ?_)
  refine WP.seq (WP.mono (dInv_ok hp h₇.1 a3 a4) fun s₈ h₈ => ?_)
  refine WP.seq (WP.mono (dV1_ok hp h₈) fun s₉ ⟨h₉, b3, b4, b5, b6⟩ => ?_)
  refine WP.seq (WP.mono (dV2_ok hp h₉ b3 b4 b5 b6) fun s₁₀ ⟨h₁₀, v₁₀⟩ => ?_)
  refine WP.seq (WP.mono (dArgs_ok hp h₁₀ (o := oPoly (3 * K.k)) (o' := K.oAcc) (by offs)
    (by offs)) fun s₁₁ ⟨h₁₁, c3, c4⟩ => ?_)
  have v₁₁ : PolyIs s₁₁.mem ((lay s₀ K).A 0 (oPoly (3 * K.k)))
      (VG.Proof.MlKem.KPke.dcV K.p (CT K s₀)) := by rw [h₁₁.2]; exact v₁₀
  refine WP.seq (WP.mono (dV4_ok hp h₁₁.1 v₁₁ c3 c4) fun s₁₂ ⟨h₁₂, w₁₂⟩ => ?_)
  refine WP.seq (WP.mono (dM1_ok hp h₁₂ w₁₂) fun s₁₃ ⟨h₁₃, e3, e4, e5, e6⟩ => ?_)
  refine WP.mono (dM2_ok hp h₁₃ e3 e4 e5 e6) fun s ⟨h, m⟩ => ⟨h, m.trans ?_⟩
  show _ = kpkeDecrypt K.p (VG.Proof.MlKem.KPke.dkPke K.p (DK K s₀)) (CT K s₀)
  rw [VG.Proof.MlKem.KPke.kpkeDecrypt_eq]

end VG.Proof.MlKem.PPC64LE.Decaps
