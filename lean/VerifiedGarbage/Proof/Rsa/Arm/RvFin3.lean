module

public import VerifiedGarbage.Proof.Rsa.Arm.RvFin2
public import VerifiedGarbage.Proof.Rsa.Arm.KeyDiv
import VerifiedGarbage.Proof.Rsa.Arm.CvDivN
import VerifiedGarbage.Proof.Rsa.Arm.DivCT
import VerifiedGarbage.Proof.Rsa.Arm.RvTaint4
import VerifiedGarbage.Proof.Rsa.Arm.RvOps2

/-! # `vg_rsa_recover_primes` on ARMv7: `q = n / p` (`div_vp`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa (b2n)

/-- `clrW j`: the word above the `w` of `[j]` cleared. -/
theorem clrW_ok {s : State} {B : BitVec 32} {Z w N j : Nat} (h : Ws s B Z w N)
    (hj : j < N) (hN : N ≤ 256) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → Keep B w [j] [] s.mem t.mem → num t.mem B w j = num s.mem B w j →
      w32 t.mem (State.addr B) (arr w j + 4 * w) = 0 → Rest opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (clrW j ++ rest)) s Q := by
  have fit := h.arr_fit hj
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  have wl := h.wle
  unfold clrW
  rw [List.append_assoc]
  refine ptr_ok h (by decide) (by omega_arith) fun s1 p1 r1 m1 h1 => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_dp (op2_lsl (by decide)) fun s2 u2 => ?_
  have e2 : s2.gpr .r0 = B + BitVec.ofNat 32 (arr w j + 4 * w) := by
    rw [u2.gpr, dpVal, p1, h1.r9]
    have : BitVec.ofNat 32 w <<< 2 = BitVec.ofNat 32 (4 * w) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_arith
    rw [this, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  have h3 : Ws s3 B Z w N := (h1.of_upd u2 (by decide) (by decide) (by decide)).of_upd u3 (by decide) (by decide)
    (by decide)
  have a0 : State.addr (s3.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr w j + 4 * w) := by
    rw [u3.other _ (by decide), e2, BitVec.add_zero]; exact h.addr (by omega_arith)
  refine wp_str (by decide) a0 (h3.write (by omega_arith)) fun t u4 => ?_
  have mt : t.mem = s.mem.writeW (off (State.addr B) (arr w j + 4 * w)) (0 : BitVec 32) := by
    rw [u4.mem, u3.gpr, u3.mem, u2.mem, m1]
  have o1 := writeW32_outside s.mem (State.addr B) (d := arr w j + 4 * w) (0 : BitVec 32) (by omega_arith)
  rw [← mt] at o1
  refine k t (h3.of_mupd u4) (Keep.of_arr (d := 4 * w) o1 (by omega_arith) (by simp)) ?_ ?_
    ((r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest _))))
  · exact o1.val32 (by omega_arith) (by omega_arith)
  · simp only [w32]; rw [mt, Mem.readW_writeW_self32]; rfl

section
variable {P : RP} {σ s t : State} {A : Nat → Nat} {live : List Nat} {AW : Nat → Nat} {liveW : List Nat}
  {V : Nat → Nat} {ls : List Nat}

/-- A step that writes array `o` but not its number. -/
theorem KS.same1 {o : Nat} (h : KS P σ A live AW liveW V ls s) (k : Keep P.B P.w [o] [] s.mem t.mem)
    (ho : o < nArr) (e : num t.mem P.B P.w o = num s.mem P.B P.w o) (hlW : ∀ j ∈ liveW, o / 2 ≠ j)
    (r8 : t.gpr .r8 = P.B) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) :
    KS P σ A live AW liveW V ls t := by
  have sz := h.sizes
  refine h.core k (by simpa using fitZ_w sz ho) (by simp) r8 sp rd wr (fun j hj => ?_) h.live_lt
    (h.arrsW_w k (fun j hj i hi => by simp at hi; subst hi; exact hlW j hj) (by simp)) h.liveW_lt
    (h.sl_keep k (by simp)) h.ls_ok
  by_cases ej : j = o
  · subst ej; rw [e]; exact h.arrs _ hj
  · rw [k.num (fun i hi ei => ej (by simp only [List.mem_singleton] at hi; rw [← ei, hi])) (by simp)
      (fit_w sz (h.live_lt j hj))]
    exact h.arrs j hj

end

/-- The divisor `p`. -/
abbrev qF (P : RP) (σ : State) (F : FinishInputs P := legacyFinish P) : Nat := P.n / pF (F := F) P σ

/-- The header words after `p`. -/
abbrev VM (P : RP) (σ : State) (F : FinishInputs P := legacyFinish P) : Nat → Nat := upd (fun _ => 0) sMask (b2n (okF (F := F) P σ))

/-- The division's start. -/
abbrev Fd (P : RP) (E : State → Prop) (σ s : State) (F : FinishInputs P := legacyFinish P) : Prop :=
  Sk P E (fun σ => upd (upd (upd (upd (fun _ => 0) aN P.n) 1 (pF (F := F) P σ)) aQ P.n) aDv (pF (F := F) P σ)) [aDv, aQ, 1, aN]
    (fun _ _ => 0) [] (VM (F := F) P) [sMask] P.w nArr σ s ∧
    DivHdr s.mem P.B P.w aQ aRm aDv aDt ∧ w32 s.mem (State.addr P.B) (arr P.w aDv + 4 * P.w) = 0

section
variable {P : RP}

/-- The division set up. -/
theorem divSet_vp {E : State → Prop} (F : FinishInputs P := legacyFinish P) : VP (Fp (F := F) P E) divSet (Fd (F := F) P E) := by
  simp only [divSet, seqs]
  refine VP.seq (Sk.pcopy qN_taint (o := aQ) (a := aN) (by decide) (by decide) (by decide) (by decide)) ?_
  refine VP.seq (Sk.pcopy dvP_taint (o := aDv) (a := 1) (by decide) (by decide) (by decide) (by decide)) ?_
  refine VP.ctx divHdr_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  have sz := h.sizes
  refine clrW_ok hw (j := aDv) (by decide) (by decide) fun s1 hw1 k1 n1 z1 r1 => ?_
  have h1 := h.same1 k1 (by decide) n1 (by simp) (h.r8_of r1) r1.sp r1.rd r1.wr
  have c1 : s1.mem.readW (off (State.addr P.B) 16) 32 = BitVec.ofNat 32 P.w := h1.cnt
  rw [← List.append_nil (VG.Impl.Rsa.Arm.CrtValues.divHdr _ _ _ _)]
  refine VG.Proof.Rsa.Arm.CrtValues.divHdr_ok hw1 (by decide) (by decide) (by decide) (by decide) c1
    fun t hwt k2 d2 r2 => WP.block_nil ⟨⟨e, ?_, hwt⟩, d2, ?_⟩
  · have hds : ∀ d ∈ ([0, 4, 8, 12] : List Nat), SlotOk d := by decide
    have hls : ∀ d ∈ [sMask], ∀ e ∈ ([0, 4, 8, 12] : List Nat), d + 4 ≤ e ∨ e + 4 ≤ d := by decide
    exact h1.core k2 (by simp) hds (h1.r8_of r2) r2.sp r2.rd r2.wr (h1.arrs_w k2 (by simp) hds) h1.live_lt
      (fun j hj => by simp at hj) (by simp) (h1.sl_keep k2 hls) h1.ls_ok
  · have fD := fit_w sz (show aDv < nArr by decide)
    have hS : S P.w = 4 * (P.w + 2) := rfl
    rw [k2.word (by omega_arith) (by simp) (by decide) fD, z1]

/-- After `q = n / p`. -/
abbrev Fq (P : RP) (E : State → Prop) (σ s : State) (F : FinishInputs P := legacyFinish P) : Prop :=
  E σ ∧ KS P σ (upd (upd (upd (fun _ => 0) aN P.n) 1 (pF (F := F) P σ)) aQ (qF (F := F) P σ)) [aQ, 1, aN] (fun _ => 0) [] (VM (F := F) P σ)
    [sMask] s

/-- `q = n / p`. -/
theorem div_vp (hn0 : 0 < P.n) {E : State → Prop} (F : FinishInputs P := legacyFinish P) : VP (Fd (F := F) P E) VG.Impl.Rsa.Arm.Div.code (Fq (F := F) P E) := by
  refine VP.of_ct (fun σ₁ σ₂ => (VG.Proof.Rsa.Arm.Div.code_ct (g := divGeom P.B P.Z P.w aQ aRm aDv aDt)).mono
    (fun s t h => ⟨divGeom_ctx h.1.1.2.2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) h.1.2.1,
      divGeom_ctx h.2.1.2.2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) h.2.2.1⟩) fun _ _ _ => trivial) fun σ s ⟨⟨e, h, hw⟩, hh, top⟩ => ?_
  have sz := h.sizes
  refine WP.mono (div_ok hw (q := aQ) (r := aRm) (d := aDv) (t := aDt) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hh top)
    fun t ⟨k, r, v⟩ => ⟨e, ?_⟩
  have g : ∀ j ∈ [aDv, aQ, 1, aN], num s.mem P.B P.w j =
      upd (upd (upd (upd (fun _ => 0) aN P.n) 1 (pF (F := F) P σ)) aQ P.n) aDv (pF (F := F) P σ) j := fun j hj => h.arrs j hj
  have vD : num s.mem P.B P.w aDv = pF (F := F) P σ := by rw [g aDv (by simp)]; simp [upd]
  have vQ : num s.mem P.B P.w aQ = P.n := by rw [g aQ (by simp)]; simp [upd, aQ, aDv]
  have hp : 0 < pF (F := F) P σ := Nat.gcd_pos_of_pos_right _ hn0
  have hq := (v (by rw [vD]; exact hp)).2
  rw [vQ, vD] at hq
  have hjs : ∀ j ∈ ([aQ, aRm, aDt] : List Nat), arr P.w j + S P.w ≤ P.Z := fun j hj => fitZ_w sz (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl | rfl <;> decide)
  refine h.core k hjs (by simp) (by rw [r.gpr _ (by decide), h.r8]) r.sp r.rd r.wr (fun j hj => ?_) (by decide)
    (fun j hj => by simp at hj) (by simp) (h.sl_keep k (by simp)) h.ls_ok
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl
  · rw [hq]; simp [upd]
  · rw [k.num (by decide) (by simp) (fit_w sz (by decide)), g 1 (by simp)]; simp [upd, aDv, aQ]
  · rw [k.num (by decide) (by simp) (fit_w sz (by decide)), g aN (by simp)]; simp [upd, aDv, aQ, aN]

end

end VG.Proof.Rsa.Arm.Recover
