module
-- separate module: the proof of Appendix C.2's body is split in a chain of modules, so that a change rebuilds only the modules after it
public import VerifiedGarbage.Proof.Rsa.Arm.RdGcd
public import VerifiedGarbage.Proof.Rsa.Arm.KeyDiv

import VerifiedGarbage.Proof.Rsa.Arm.RvFin3
import VerifiedGarbage.Proof.Rsa.Arm.CvDivN
import VerifiedGarbage.Proof.Rsa.Arm.DivCT
import VerifiedGarbage.Proof.Rsa.Arm.RvCtx
import VerifiedGarbage.Proof.Rsa.Arm.KcStart
import VerifiedGarbage.Proof.Rsa.Arm.RvOps
import VerifiedGarbage.Proof.Rsa.Arm.RvOps2
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rsa.Arm.RvViews

/-! # `vg_rsa_recover_primes_det` on ARMv7: the divisions

The division on the wide arrays reads its count, `W`, from the header word
16, which holds `w` at every other stage (`KS`): between the header and the
count's restoration the stage is `KSW`, with `W` there.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.Keys hiding aT1 aT2 aT3 aT4
open VG.Proof.X25519.Arm

/-- A stage of the key working space with `W` in the header word 16. -/
structure KSW (P : RP) (σ : State) (A : Nat → Nat) (live : List Nat) (AW : Nat → Nat) (liveW : List Nat)
    (V : Nat → Nat) (ls : List Nat) (s : State) : Prop where
  bs : Bs P σ s
  r8 : s.gpr .r8 = P.B
  cnt : s.mem.readW (off (State.addr P.B) 16) 32 = BitVec.ofNat 32 P.W
  arrs : Arrs s.mem P.B P.w A live
  arrsW : Arrs s.mem P.B P.W AW liveW
  sl : ∀ d ∈ ls, slot s.mem P.B d = V d
  live_lt : ∀ j ∈ live, j < VG.Impl.Rsa.Arm.Recover.nArr
  liveW_lt : ∀ j ∈ liveW, j < 22
  ls_ok : ∀ d ∈ ls, SlotOk d

section
variable {P : RP} {σ s t : State} {A : Nat → Nat} {live : List Nat} {AW : Nat → Nat} {liveW : List Nat}
  {V : Nat → Nat} {ls : List Nat}

/-- `str r9, [r8, #16]` with `W` in `r9`. -/
theorem KS.toKSW (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.W 22) {rest : List Instr}
    {Q : State → Prop} (k : ∀ t, KSW P σ A live AW liveW V ls t → Ws t P.B P.Z P.W 22 →
      Keep P.B P.w [] [16] s.mem t.mem → WP isa (.block rest) t Q) :
    WP isa (.block (.str .r9 .r8 16 :: rest)) s Q := by
  have sz := h.sizes
  have kt : ∀ t : State, t.mem = s.mem.writeW (off (State.addr P.B) 16) (s.gpr .r9) →
      Keep P.B P.w [] [16] s.mem t.mem := fun t e => by rw [e]; exact keep_write _ _ (by simp) (by decide)
  refine wp_strSlot hv (d := 16) (by decide) fun t u => k t ?_ (hv.of_mupd u) (kt t u.mem)
  have kt := kt t u.mem
  have hs : ∀ d ∈ ls, ∀ e ∈ [16], d + 4 ≤ e ∨ e + 4 ≤ d := fun d hd e he => by
    simp only [List.mem_singleton] at he; subst he; have := (h.ls_ok d hd).2.1; omega
  refine ⟨h.bs.of_frame (kt.frameS (by simp) (by decide) (hdr_Z sz)) u.sp u.rd u.wr, by rw [u.gpr, h.r8], ?_,
    h.arrs.keepOf kt (by simp) (by decide) fun j hj => fit_w sz (h.live_lt j hj),
    h.arrsW.keepOf kt.toW (by simp) (by decide) fun j hj => fit_W sz (h.liveW_lt j hj),
    h.sl_keep kt hs, h.live_lt, h.liveW_lt, h.ls_ok⟩
  rw [u.mem, Mem.readW_writeW_self32, hv.r9]

theorem KSW.sizes (h : KSW P σ A live AW liveW V ls s) : Sizes P := h.bs.pre.sizes

/-- A step with `W` words that writes the arrays `js` and the header words `ds` below 16. -/
theorem KSW.core {js ds : List Nat} (h : KSW P σ A live AW liveW V ls s)
    (k : Keep P.B P.W js ds s.mem t.mem) (hjs : ∀ j ∈ js, j < 22) (hds : ∀ d ∈ ds, d + 4 ≤ 16)
    (r8 : t.gpr .r8 = P.B) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (hl : ∀ j ∈ live, ∀ i ∈ js, j / 2 ≠ i) (hls : ∀ d ∈ ls, 16 ≤ d)
    {AW' : Nat → Nat} {liveW' : List Nat} (haW : Arrs t.mem P.B P.W AW' liveW') (hlW : ∀ j ∈ liveW', j < 22) :
    KSW P σ A live AW' liveW' V ls t := by
  have sz := h.sizes
  refine ⟨h.bs.of_frame (k.frameS (fun j hj => fitZ_W sz (hjs j hj)) (fun d hd => by
      have := hds d hd; simp only [hdr]; omega)
      (hdr_Z sz)) sp rd wr, r8, ?_, ?_, haW, ?_, h.live_lt, hlW, h.ls_ok⟩
  · refine (BitVec.eq_of_toNat_eq ?_).trans h.cnt
    exact k.slot (e := 16) (by decide) fun d hd => by have := hds d hd; omega
  · exact h.arrs.keepOf k.ofW (fun j hj i hi => by
      simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hi
      obtain ⟨i', hi', e⟩ := hi
      have := hl j hj i' hi'
      rcases e with rfl | rfl <;> omega) (fun d hd => by have := hds d hd; simp only [hdr]; omega)
      fun j hj => fit_w sz (h.live_lt j hj)
  · intro d hd
    rw [k.slot (h.ls_ok d hd).1 (fun e he => by have := hds e he; have := hls d hd; omega), h.sl d hd]

/-- The arrays read with `W` that a step does not write. -/
theorem KSW.arrsW_W {js ds : List Nat} (h : KSW P σ A live AW liveW V ls s) (k : Keep P.B P.W js ds s.mem t.mem)
    (hl : ∀ j ∈ liveW, ∀ i ∈ js, i ≠ j) (hds : ∀ d ∈ ds, d + 4 ≤ 16) : Arrs t.mem P.B P.W AW liveW :=
  h.arrsW.keepOf k hl (fun d hd => by have := hds d hd; simp only [hdr]; omega)
    fun j hj => fit_W h.sizes (h.liveW_lt j hj)

/-- `restoreW`: `w` back in the header word 16, and the narrow context. -/
theorem KSW.restore (h : KSW P σ A live AW liveW V ls s) :
    WP isa (.block VG.Impl.Rsa.Arm.RecoverDet.restoreW) s fun t =>
      KS P σ A live AW liveW V ls t ∧ Ws t P.B P.Z P.w VG.Impl.Rsa.Arm.Recover.nArr := by
  have sz := h.sizes
  have wl := sz.wle; have Wl := sz.Wle
  have hz := hdr_Z sz
  have hf := h.bs.pre.fS
  unfold VG.Impl.Rsa.Arm.RecoverDet.restoreW
  simp only [List.cons_append, List.nil_append]
  refine wp_ldr (a := off (State.addr P.B) 16) (by decide) (by rw [h.r8]; exact addr_add (by simp only [hdr] at hz; omega))
    ⟨P.rS, List.mem_append_right _ h.bs.rS_mem, Offset.contains_base _ (by simp only [hdr] at hz; omega)
      (by decide)⟩ fun s1 u1 => ?_
  rw [h.cnt] at u1
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s3 u3 => ?_
  have e9 : s3.gpr .r9 = BitVec.ofNat 32 P.w := by
    rw [u3.gpr, u2.gpr, dpVal, u1.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, show (2 : BitVec 32).toNat = 2 from rfl]
    simp only [RP.W]
    omega
  have r8' : s3.gpr .r8 = P.B := by rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), h.r8]
  have wr3 : s3.wr = s.wr := by rw [u3.wr, u2.wr, u1.wr]
  have hin : InRegions s3.wr (State.addr (s3.gpr .r8 + BitVec.ofNat 32 16)) 4 := by
    rw [r8', addr_add (by simp only [hdr] at hz; omega), wr3]
    exact ⟨P.rS, h.bs.rS_mem, Offset.contains_base _ (by simp only [hdr] at hz; omega) (by decide)⟩
  refine wp_str (by decide) rfl hin fun s4 u4 => ?_
  refine VG.Proof.Rsa.Arm.KeyCheck.stride_ok (w := P.w) (by omega) (by rw [u4.gpr, e9]) fun t h7 r m => WP.block_nil ?_
  have mt : t.mem = s.mem.writeW (off (State.addr P.B) 16) (BitVec.ofNat 32 P.w) := by
    rw [m, u4.mem, e9, r8', addr_add (by simp only [hdr] at hz; omega), u3.mem, u2.mem, u1.mem]
  have kt : Keep P.B P.w [] [16] s.mem t.mem := by rw [mt]; exact keep_write _ _ (by simp) (by decide)
  have hs : ∀ d ∈ ls, ∀ e ∈ [16], d + 4 ≤ e ∨ e + 4 ≤ d := fun d hd e he => by
    simp only [List.mem_singleton] at he; subst he; have := (h.ls_ok d hd).2.1; omega
  have rt : Rest [.r9, .r7] s t := ((u1.rest (by simp)).trans ((u2.rest (by simp)).trans (u3.rest (by simp)))).trans
    ((u4.rest _).trans (r.mono (by simp)))
  refine ⟨⟨h.bs.of_frame (kt.frameS (by simp) (by decide) hz) rt.sp rt.rd rt.wr,
    by rw [rt.gpr _ (by decide), h.r8], by rw [mt, Mem.readW_writeW_self32],
    h.arrs.keepOf kt (by simp) (by decide) fun j hj => fit_w sz (h.live_lt j hj),
    h.arrsW.keepOf kt.toW (by simp) (by decide) fun j hj => fit_W sz (h.liveW_lt j hj),
    fun d hd => by rw [kt.slot (h.ls_ok d hd).1 (hs d hd), h.sl d hd], h.live_lt, h.liveW_lt, h.ls_ok⟩,
    ⟨hf, by rw [rt.wr]; exact h.bs.rS_mem, sz.fits, by show 0 < 2 * P.w6 + 2; omega, by omega, h7,
      by rw [rt.gpr _ (by decide), h.r8], by rw [r.gpr _ (by decide), u4.gpr, e9]⟩⟩

/-- `clrW j` with `W` words: the word above `[j]` cleared. -/
theorem KS.clrW_W {j : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.W 22)
    (hj : j ∈ liveW) (hl : ∀ i ∈ live, i / 2 ≠ j) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live AW liveW V ls t → Ws t P.B P.Z P.W 22 →
      w32 t.mem (State.addr P.B) (arr P.W j + 4 * P.W) = 0 → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.Rsa.Arm.Recover.clrW j ++ rest)) s Q := by
  have sz := h.sizes
  have hj22 := h.liveW_lt j hj
  refine clrW_ok hv hj22 (by decide) fun t ht kt e z r => k t ?_ ht z
  refine h.core kt (by simpa using fitZ_W sz hj22) (by simp) (h.r8_of r) r.sp r.rd r.wr
    (h.arrs_W kt (fun i hi o ho => by simp only [List.mem_singleton] at ho; subst ho; exact hl i hi) (by simp))
    h.live_lt (fun i hi => ?_) h.liveW_lt (h.sl_keep kt (by simp)) h.ls_ok
  by_cases ei : i = j
  · subst ei; rw [e, h.arrsW i hi]
  · rw [kt.num (by simp only [List.mem_singleton]; rintro _ rfl e; exact ei e.symm) (by simp)
      (fit_W sz (h.liveW_lt i hi))]
    exact h.arrsW i hi

end

end VG.Proof.Rsa.Arm.Recover

namespace VG.Proof.Rsa.Arm.RecoverDet
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Recover
open VG.Impl.Rsa.Arm.Keys hiding aT1 aT2 aT3 aT4
open VG.Proof.X25519.Arm
open VG.Impl.Rsa.Arm.RecoverDet
open VG.Impl.Rsa.Arm.Recover (nArr aW clrW ctxw)
open VG.Proof.Rsa (sub32 b2n)

section
variable {P : RP}

/-- The product `a`. -/
abbrev aV (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat :=
  (pr g (AG P f σ aG) (AWG P f σ wX3) (32 * P.w)).2.2

/-- The narrow constants and `n`. -/
def AB (P : RP) : Nat → Nat := upd (upd (upd (fun _ => 0) aOneN 1) aZN 0) aN P.n
abbrev LB : List Nat := [aN, aZN, aOneN]

def AWA1 (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (upd (upd (upd (fun _ => 0) wZ 0) wOne 1) wA (aV P f g σ)) wN P.n
def AWA2 (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (upd (AWA1 P f g σ) wA (aV P f g σ / P.n)) wR (aV P f g σ % P.n)
abbrev LWA : List Nat := [wR, wA, wN, wOne, wZ]

/-- Ready for the wide division. -/
def DA1 (P : RP) (E : State → Prop) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ s : State) : Prop :=
  E σ ∧ KSW P σ (AB P) LB (AWA1 P f g σ) [wN, wA, wOne, wZ] (VG' P σ) [sOkDE] s ∧ Ws s P.B P.Z P.W 22 ∧
    DivHdr s.mem P.B P.W wA wR wN wDt ∧ w32 s.mem (State.addr P.B) (arr P.W wN + 4 * P.W) = 0

theorem divAPre_vp {f g : Nat × Nat × Nat → Nat × Nat × Nat} {E : State → Prop} :
    VP (fun σ s => E σ ∧ PI P g aG wX3 wA (AG P f) LG (AWG P f) LWT (VG' P) [sOkDE] (32 * P.w) σ s) divAPre
      (DA1 P E f g) := by
  refine VP.dctx divAPre_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h0, hv⟩ => ?_
  have sz := h0.sizes
  have h := h0.mono (A' := AB P) (live' := LB) (AW' := upd (upd (upd (fun _ => 0) wZ 0) wOne 1) wA (aV P f g σ))
    (liveW' := [wA, wOne, wZ]) (V' := VG' P σ) (ls' := [sOkDE])
    (fun j hj => by
      simp only [LB, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;> simp only [AB, AG] <;> rd_ev)
    (fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;> simp only [AWG, aV] <;> rd_ev)
    (fun d hd => by
      simp only [List.mem_singleton] at hd; subst hd; exact ⟨by decide, by rd_up⟩)
  simp only [divAPre, seqs]
  refine WP.seq (h.toW hv fun s1 h1 hv1 _ => WP.block_nil ?_)
  refine WP.seq (WP.mono (h1.copy_W hv1 (o := wN) (a := wZ) (by decide) (by decide) (by decide) (by decide))
    fun s2 ⟨h2, hv2, _⟩ => ?_)
  refine WP.seq (h2.toN hv2 fun s3 h3 hv3 _ => WP.block_nil ?_)
  have z3 : num s3.mem P.B P.W wN = 0 := by rw [h3.arrsW wN (by decide)]; rd_up
  have h3' := h3.mono (A' := AB P) (live' := LB)
    (AW' := upd (upd (upd (fun _ => 0) wZ 0) wOne 1) wA (aV P f g σ)) (liveW' := [wA, wOne, wZ])
    (V' := VG' P σ) (ls' := [sOkDE]) (fun j hj => ⟨hj, rfl⟩)
    (fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> exact ⟨by decide, by rd_up⟩) (fun d hd => ⟨hd, rfl⟩)
  refine WP.seq (WP.mono (h3'.widen hv3 (j := wN) (a := aN) (by decide) z3 (by decide) (by decide) (by decide)
    (by decide)) fun s4 ⟨h4, hv4⟩ => ?_)
  rw [List.append_assoc]
  refine h4.toW hv4 fun s5 h5 hv5 _ => ?_
  refine h5.clrW_W hv5 (j := wN) (by decide) (by decide) fun s6 h6 hv6 top6 => ?_
  refine h6.toKSW hv6 fun s7 h7 hv7 k7 => ?_
  have c7 : s7.mem.readW (off (State.addr P.B) 16) 32 = BitVec.ofNat 32 P.W := h7.cnt
  rw [← List.append_nil (VG.Impl.Rsa.Arm.CrtValues.divHdr _ _ _ _)]
  refine VG.Proof.Rsa.Arm.CrtValues.divHdr_ok hv7 (by decide) (by decide) (by decide) (by decide) c7
    fun t hvt kt dt rt => WP.block_nil ⟨e, ?_, hvt, dt, ?_⟩
  · refine h7.core kt (by simp) (by decide) (by rw [rt.gpr _ (by decide), h7.r8]) rt.sp rt.rd rt.wr (by simp)
      (by decide) (fun j hj => ?_) h7.liveW_lt
    rw [h7.arrsW_W kt (by simp) (by decide) j hj]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> simp only [AWA1, AB] <;> rd_ev
  · have fN := fit_W sz (show wN < 22 by decide)
    have hS : S P.W = 4 * (P.W + 2) := rfl
    rw [kt.word (j := wN) (i := P.W) (by omega) (by simp) (by decide) fN,
      k7.toW.word (j := wN) (i := P.W) (by simp only [S, RP.W]; omega) (by simp) (by decide) fN, top6]

/-- After the wide division. -/
def DA2 (P : RP) (E : State → Prop) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ s : State) : Prop :=
  E σ ∧ KSW P σ (AB P) LB (AWA2 P f g σ) LWA (VG' P σ) [sOkDE] s

theorem divAMid_vp (hn0 : 0 < P.n) {f g : Nat × Nat × Nat → Nat × Nat × Nat} {E : State → Prop} :
    VP (DA1 P E f g) VG.Impl.Rsa.Arm.Div.code (DA2 P E f g) := by
  refine VP.of_ct (fun σ₁ σ₂ => (VG.Proof.Rsa.Arm.Div.code_ct (g := divGeom P.B P.Z P.W wA wR wN wDt)).mono
    (fun s t h => ⟨divGeom_ctx h.1.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) h.1.2.2.2.1,
      divGeom_ctx h.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) h.2.2.2.2.1⟩) fun _ _ _ => trivial)
    fun σ s ⟨e, h, hv, hh, top⟩ => ?_
  have sz := h.sizes
  refine WP.mono (div_ok hv (q := wA) (r := wR) (d := wN) (t := wDt) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hh top)
    fun t ⟨k, r, v⟩ => ⟨e, ?_⟩
  have vD : num s.mem P.B P.W wN = P.n := by rw [h.arrsW wN (by decide)]; simp only [AWA1]; rd_up
  have vQ : num s.mem P.B P.W wA = aV P f g σ := by rw [h.arrsW wA (by decide)]; simp only [AWA1]; rd_up
  obtain ⟨vr, vq⟩ := v (by rw [vD]; exact hn0)
  rw [vD, vQ] at vr vq
  refine h.core k (by decide) (by simp) (by rw [r.gpr _ (by decide), h.r8]) r.sp r.rd r.wr (by decide)
    (by decide) (fun j hj => ?_) (by decide)
  simp only [LWA, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · rw [vr]; simp only [AWA2]; rd_up
  · rw [vq]; simp only [AWA2]; rd_up
  all_goals
    rw [k.num (by decide) (by simp) (fit_W sz (by decide)), h.arrsW _ (by decide)]
    simp only [AWA2]; rd_up

/-- After the wide division and `m < n`. -/
def VA (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (VG' P σ) sLt (b2n (decide (aV P f g σ / P.n < P.n)))

theorem divA_vp (hn0 : 0 < P.n) {f g : Nat × Nat × Nat → Nat × Nat × Nat} {E : State → Prop} :
    VP (fun σ s => E σ ∧ PI P g aG wX3 wA (AG P f) LG (AWG P f) LWT (VG' P) [sOkDE] (32 * P.w) σ s) divA
      (Dk P E (fun _ => AB P) LB (AWA2 P f g) LWA (VA P f g) [sLt, sOkDE] P.w nArr) := by
  simp only [divA, seqs]
  refine divAPre_vp.seq ((divAMid_vp hn0).seq (VP.seq (G := Dk P E (fun _ => AB P) LB (AWA2 P f g) LWA (VG' P)
    [sOkDE] P.w nArr) (VP.taint [.r8] restoreW_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_)
      fun σ s ⟨e, h⟩ => WP.mono h.restore fun t ⟨ht, hvt⟩ => ⟨e, ht, hvt⟩) ?_))
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.r8, h₂.2.r8]
  refine VP.dctx divAPost_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_
  simp only [divAPost, seqs]
  refine WP.seq (h.toW hv fun s1 h1 hv1 _ => WP.block_nil ?_)
  refine WP.seq (WP.mono (h1.sub_W hv1 (o := wT1) (a := wA) (b := wN) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s2 ⟨h2, hv2, _, c2⟩ => ?_)
  refine h2.brw hv2 (d := sLt) (by decide) fun s3 h3 hv3 _ => ?_
  refine h3.toN hv3 fun t ht hvt _ => WP.block_nil ⟨e, ?_, hvt⟩
  rw [c2] at ht
  refine ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨List.mem_cons_of_mem _ hj, ?_⟩) (fun d hd => ?_)
  · simp only [LWA, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> rd_up
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · refine ⟨by decide, ?_⟩
      rw [upd_self]; simp only [VA, upd_self, AWA2, AWA1]; rd_up
    · exact ⟨by decide, by simp only [VA]; rd_up⟩

/-- `m mod 2^(32 w) + 1` modulo `2^(32 w)` (1 where that is zero), `n - r mod 2^(32 w)`, and their
quotient and remainder. -/
abbrev m1R (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat :=
  sub32 P.w (aV P f g σ / P.n % 2 ^ (32 * P.w)) (sub32 P.w 0 1)
abbrev m1V (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat :=
  if m1R P f g σ = 0 then 1 else m1R P f g σ
abbrev dV (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat :=
  sub32 P.w P.n (aV P f g σ % P.n % 2 ^ (32 * P.w))
abbrev qV (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat := dV P f g σ / m1V P f g σ
abbrev remV (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat := dV P f g σ % m1V P f g σ

def ABd (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (upd (AB P) aM1 (m1V P f g σ)) aD (dV P f g σ)
def AWB (P : RP) : Nat → Nat := upd (upd (upd (fun _ => 0) wZ 0) wOne 1) wN P.n
abbrev LWB : List Nat := [wN, wOne, wZ]

/-- Ready for the narrow division. -/
def DB1 (P : RP) (E : State → Prop) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ s : State) : Prop :=
  Dk P E (ABd P f g) [aD, aM1, aN, aZN, aOneN] (fun _ => AWB P) LWB (VA P f g) [sLt, sOkDE] P.w nArr σ s ∧
    DivHdr s.mem P.B P.w aD aRem aM1 aDt ∧ w32 s.mem (State.addr P.B) (arr P.w aM1 + 4 * P.w) = 0

theorem divBPre_vp {f g : Nat × Nat × Nat → Nat × Nat × Nat} {E : State → Prop} :
    VP (Dk P E (fun _ => AB P) LB (AWA2 P f g) LWA (VA P f g) [sLt, sOkDE] P.w nArr) divBPre (DB1 P E f g) := by
  refine VP.dctx divBPre_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h0, hv⟩ => ?_
  have sz := h0.sizes
  have h1 := h0.narrow (j := wA) (by decide) (by decide)
  rw [show 2 * wA = aMlo from rfl] at h1
  have h2 := h1.narrow (j := wR) (by decide) (by decide)
  rw [show 2 * wR = aRlo from rfl] at h2
  simp only [divBPre, seqs]
  refine WP.seq (WP.mono (h2.sub_w hv (o := aT2) (a := aZN) (b := aOneN) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s1 ⟨h3, hv3, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h3.sub_w hv3 (o := aT1) (a := aMlo) (b := aT2) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s2 ⟨h4, hv4, _, _⟩ => ?_)
  have h4' := h4.mono (A' := upd (upd (upd (AB P) aT1 (m1R P f g σ)) aRlo (aV P f g σ % P.n % 2 ^ (32 * P.w)))
      aN P.n)
    (live' := [aT1, aRlo, aN, aZN, aOneN]) (AW' := AWA2 P f g σ) (liveW' := LWA) (V' := VA P f g σ)
    (ls' := [sLt, sOkDE])
    (fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      refine ⟨by rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide, ?_⟩
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp only [AWA2, AWA1, AB] <;> rd_ev)
    (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  refine WP.seq (WP.mono (h4'.eqS_w hv4 (d := sM0) (a := aT1) (b := aZN) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s3 ⟨h5, hv5, _⟩ => ?_)
  refine WP.seq (WP.mono (h5.sel_w hv5 (o := aM1) (a := aT1) (b := aOneN) (sl := sM0) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rd_up; split <;> omega) (by decide))
    fun s4 ⟨h6, hv6, _⟩ => ?_)
  refine WP.seq (WP.mono (h6.sub_w hv6 (o := aD) (a := aN) (b := aRlo) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s5 ⟨h7, hv7, _, _⟩ => ?_)
  refine clrW_ok hv7 (j := aM1) (by decide) (by decide) fun s6 hv8 k8 n8 top8 r8 => ?_
  have h8 := h7.same1 k8 (by decide) n8 (by decide) (h7.r8_of r8) r8.sp r8.rd r8.wr
  rw [← List.append_nil (VG.Impl.Rsa.Arm.CrtValues.divHdr _ _ _ _)]
  refine VG.Proof.Rsa.Arm.CrtValues.divHdr_ok hv8 (by decide) (by decide) (by decide) (by decide) h8.cnt
    fun t hvt kt dt rt => WP.block_nil ⟨⟨e, ?_, hvt⟩, dt, ?_⟩
  · have hds : ∀ d ∈ ([0, 4, 8, 12] : List Nat), SlotOk d := by decide
    have h9 := h8.core kt (by simp) hds (h8.r8_of rt) rt.sp rt.rd rt.wr (h8.arrs_w kt (by simp) hds) h8.live_lt
      (h8.arrsW_w kt (by simp) hds) h8.liveW_lt (h8.sl_keep kt (by decide)) h8.ls_ok
    refine h9.mono (fun j hj => ?_) (fun j hj => ?_) (fun d hd => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      refine ⟨by rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide, ?_⟩
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp only [ABd, AB, m1V] <;> rd_ev
    · simp only [LWB, List.mem_cons, List.not_mem_nil, or_false] at hj
      refine ⟨by rcases hj with rfl | rfl | rfl <;> decide, ?_⟩
      rcases hj with rfl | rfl | rfl <;> simp only [AWB, AWA2, AWA1] <;> rd_ev
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      refine ⟨by rcases hd with rfl | rfl <;> decide, ?_⟩
      rcases hd with rfl | rfl <;> rd_up
  · have fD := fit_w sz (show aM1 < nArr by decide)
    have hS : S P.w = 4 * (P.w + 2) := rfl
    rw [kt.word (by omega) (by simp) (by decide) fD, top8]

def ABq (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (upd (AB P) aD (qV P f g σ)) aRem (remV P f g σ)
def VB (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (VA P f g σ) sExact (if remV P f g σ = 0 then 1 else 0)

theorem divB_vp {f g : Nat × Nat × Nat → Nat × Nat × Nat} {E : State → Prop} :
    VP (Dk P E (fun _ => AB P) LB (AWA2 P f g) LWA (VA P f g) [sLt, sOkDE] P.w nArr) divB
      (Dk P E (fun σ => upd (AB P) aD (qV P f g σ)) [aD, aN, aZN, aOneN] (fun _ => AWB P) LWB (VB P f g)
        [sExact, sLt, sOkDE] P.w nArr) := by
  simp only [divB, seqs]
  let D2 := fun σ s => E σ ∧ KS P σ (ABq P f g σ) [aRem, aD, aN, aZN, aOneN] (AWB P) LWB (VA P f g σ) [sLt, sOkDE] s
  refine divBPre_vp.seq (VP.seq (G := D2) ?_ (VP.seq (G := Dk P E (ABq P f g) [aRem, aD, aN, aZN, aOneN]
    (fun _ => AWB P) LWB (VA P f g) [sLt, sOkDE] P.w nArr) ?_ ?_))
  · refine VP.of_ct (fun σ₁ σ₂ => (VG.Proof.Rsa.Arm.Div.code_ct (g := divGeom P.B P.Z P.w aD aRem aM1 aDt)).mono
      (fun s t h => ⟨divGeom_ctx h.1.1.2.2 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) h.1.2.1,
        divGeom_ctx h.2.1.2.2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) h.2.2.1⟩) fun _ _ _ => trivial)
      fun σ s ⟨⟨e, h, hv⟩, hh, top⟩ => ?_
    have sz := h.sizes
    refine WP.mono (div_ok hv (q := aD) (r := aRem) (d := aM1) (t := aDt) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hh top)
      fun t ⟨k, r, v⟩ => ⟨e, ?_⟩
    have vD : num s.mem P.B P.w aM1 = m1V P f g σ := by rw [h.arrs aM1 (by decide)]; simp only [ABd]; rd_up
    have vQ : num s.mem P.B P.w aD = dV P f g σ := by rw [h.arrs aD (by decide)]; simp only [ABd]; rd_up
    obtain ⟨vr, vq⟩ := v (by rw [vD]; simp only [m1V]; split <;> omega)
    rw [vD, vQ] at vr vq
    have hjs : ∀ j ∈ ([aD, aRem, aDt] : List Nat), arr P.w j + S P.w ≤ P.Z := fun j hj => fitZ_w sz (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl | rfl <;> decide)
    refine h.core k hjs (by simp) (by rw [r.gpr _ (by decide), h.r8]) r.sp r.rd r.wr (fun j hj => ?_) (by decide)
      (h.arrsW_w k (by decide) (by simp)) h.liveW_lt (h.sl_keep k (by simp)) h.ls_ok
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl
    · rw [vr]; simp only [ABq]; rd_up
    · rw [vq]; simp only [ABq]; rd_up
    all_goals
      rw [k.num (by decide) (by simp) (fit_w sz (by decide)), h.arrs _ (by decide)]
      simp only [ABq, ABd]; rd_up
  · refine VP.taint [.r8] ctxw_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s ⟨e, h⟩ => ?_
    · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.r8, h₂.2.r8]
    exact WP.mono (ctxw_ok h.bs h.r8 h.cnt) fun t ⟨hvt, r, m⟩ => ⟨e, h.of_rest r m (by decide), hvt⟩
  · refine VP.dctx eqExact_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_
    refine WP.mono (h.eqS_w hv (d := sExact) (a := aRem) (b := aZN) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)) fun t ⟨ht, hvt, _⟩ => ⟨e, ?_, hvt⟩
    refine ht.mono (fun j hj => ?_) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      refine ⟨by rcases hj with rfl | rfl | rfl | rfl <;> decide, ?_⟩
      rcases hj with rfl | rfl | rfl | rfl <;> simp only [ABq] <;> rd_up
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      refine ⟨by rcases hd with rfl | rfl | rfl <;> decide, ?_⟩
      rcases hd with rfl | rfl | rfl <;> simp only [VB, ABq, AB] <;> rd_ev

end

end VG.Proof.Rsa.Arm.RecoverDet
