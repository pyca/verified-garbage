module
-- separate module: the proof of Appendix C.2's body is split in a chain of modules, so that a change rebuilds only the modules after it
public import VerifiedGarbage.Proof.Rsa.Arm.RdRows
public import VerifiedGarbage.Proof.Rsa.Arm.KeyDiv

import VerifiedGarbage.Proof.Rsa.Arm.Stage.Div
import VerifiedGarbage.Proof.Rsa.Arm.CvDivN
import VerifiedGarbage.Proof.Rsa.Arm.DivCT
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ctx
import VerifiedGarbage.Proof.Rsa.Arm.KcStart
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops2
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Views
import VerifiedGarbage.Proof.Bignum.Arm.CopyWords
import VerifiedGarbage.Proof.Rsa.Arm.KdNorm
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Slots
import VerifiedGarbage.Proof.Rsa.Arm.KeyEq
import VerifiedGarbage.Proof.Rsa.Arm.RdTwos

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

/-- A step with `W` words that writes the arrays `js` and header words `ds` apart from those
recorded and from 16. -/
theorem KSW.core2 {js ds : List Nat} (h : KSW P σ A live AW liveW V ls s)
    (k : Keep P.B P.W js ds s.mem t.mem) (hjs : ∀ j ∈ js, j < 22) (hds : ∀ d ∈ ds, SlotOk d)
    (r8 : t.gpr .r8 = P.B) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (hl : ∀ j ∈ live, ∀ i ∈ js, j / 2 ≠ i) (hls : ∀ d ∈ ls, ∀ e ∈ ds, d + 4 ≤ e ∨ e + 4 ≤ d)
    {AW' : Nat → Nat} {liveW' : List Nat} (haW : Arrs t.mem P.B P.W AW' liveW') (hlW : ∀ j ∈ liveW', j < 22) :
    KSW P σ A live AW' liveW' V ls t := by
  have sz := h.sizes
  refine ⟨h.bs.of_frame (k.frameS (fun j hj => fitZ_W sz (hjs j hj)) (fun d hd => (hds d hd).1)
      (hdr_Z sz)) sp rd wr, r8, ?_, ?_, haW, ?_, h.live_lt, hlW, h.ls_ok⟩
  · refine (BitVec.eq_of_toNat_eq ?_).trans h.cnt
    exact k.slot (e := 16) (by decide) fun d hd => by have := (hds d hd).2.1; omega
  · exact h.arrs.keepOf k.ofW (fun j hj i hi => by
      simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hi
      obtain ⟨i', hi', e⟩ := hi
      have := hl j hj i' hi'
      rcases e with rfl | rfl <;> omega) (fun d hd => (hds d hd).1)
      fun j hj => fit_w sz (h.live_lt j hj)
  · intro d hd
    rw [k.slot (h.ls_ok d hd).1 (hls d hd), h.sl d hd]

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

/-- `eqS d a b t` with `W` words: the header word `d := [a] = [b]`, `[t]` (not live) its scratch. -/
theorem KS.eqS_W {d a b t : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.W 22)
    (ha : a ∈ liveW) (hb : b ∈ liveW) (hd : SlotOk d) (ht : t < 22) (htW : t ∉ liveW) (hl : ∀ j ∈ live, j / 2 ≠ t)
    (hls : ∀ e ∈ ls, e + 4 ≤ sT ∨ sT + 4 ≤ e) (hdT : d ≠ sT) :
    WP isa (eqS d a b t) s fun u =>
      KS P σ A live AW liveW (upd V d (if AW a = AW b then 1 else 0)) (d :: ls) u ∧
      Ws u P.B P.Z P.W 22 ∧ Rest opRegs s u := by
  have sz := h.sizes
  have hta : t ≠ a := fun e => htW (e ▸ ha)
  have htb : t ≠ b := fun e => htW (e ▸ hb)
  have hT : SlotOk sT := by decide
  have hds : ∀ x ∈ [sT, d], SlotOk x := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro x (rfl | rfl) <;> with_reducible assumption
  refine WP.mono (VG.Proof.Rsa.Arm.Keys.eqS_ok hv (t := t) ht (h.liveW_lt a ha) (h.liveW_lt b hb) (by decide)
    hta htb hd.1) fun u ⟨hu, k, e, r⟩ => ⟨?_, hu, r⟩
  refine h.core k (by simpa using fitZ_W sz ht) hds (h.r8_of r) r.sp r.rd r.wr
    (h.arrs_W k (fun j hj i hi => by simp at hi; subst hi; exact hl j hj) hds) h.live_lt
    (h.arrsW.keepOf k (fun j hj i hi => by simp at hi; subst hi; exact fun e => htW (e ▸ hj))
      (fun x hx => (hds x hx).1) fun j hj => fit_W sz (h.liveW_lt j hj))
    h.liveW_lt (fun x hx => ?_) (fun x hx => ?_)
  · by_cases e' : x = d
    · subst e'; rw [upd_self, e, h.arrsW a ha, h.arrsW b hb]
    · have hx' := (List.mem_cons.mp hx).resolve_left e'
      have a1 := h.ls_ok x hx'
      rw [upd_ne _ _ e', k.slot a1.1 (fun y hy => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact hls x hx'
        · have := a1.2.2; have := hd.2.2; omega), h.sl x hx']
  · rcases List.mem_cons.mp hx with rfl | hx'
    · exact hd
    · exact h.ls_ok x hx'

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
open VG.Proof.Bignum.Arm (SubCtx copyWords_ok)

section
variable {P : RP}

/-! ## Shifts by the words of the shift `s = W / 2 - ⌈n_len / 4⌉` -/

/-- The shift in words. -/
abbrev sA (P : RP) : Nat := P.W / 2 - (P.K + 3) / 4

theorem sA_facts (sz : Sizes P) : 3 ≤ sA P ∧ sA P + (P.K + 3) / 4 = P.W / 2 ∧ P.W = 2 * (P.W / 2) := by
  have := sz.kw; have := sz.wle
  have : 18 ≤ P.w := by have := sz.w6a; simp only [RP.w]; omega
  simp only [sA, RP.W]; omega

/-- `shiftUpBN a`: from `[o]`'s address in `r0`, `4 sh` in `r1` and `n` in `lr`, `[a]`'s low `n - sh`
words into `[o]` from word `sh`. -/
theorem shiftUpBN_ok {s : State} {B : BitVec 32} {Z W N o a sh n : Nat} (h : Ws s B Z W N) (ho : o < N)
    (ha : a < N) (hN : N ≤ 256) (hoa : o ≠ a) (hsh : sh < n) (hnW : n ≤ W)
    (h0 : s.gpr .r0 = B + BitVec.ofNat 32 (arr W o)) (h1 : s.gpr .r1 = BitVec.ofNat 32 (4 * sh))
    (hlr : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa (shiftUpBN a) s fun t => Ws t B Z W N ∧
      Outside (State.addr B) (arr W o + 4 * sh) (4 * (n - sh)) s.mem t.mem ∧
      val32 t.mem (State.addr B) (arr W o + 4 * sh) (n - sh) = val32 s.mem (State.addr B) (arr W a) (n - sh) ∧
      Rest opRegs s t := by
  have := h.wle
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have da := arr_disj (w := W) hoa
  simp only [S] at fo fa da
  rw [shiftUpBN, WP.seq_iff]
  simp only [List.cons_append, List.nil_append]
  refine wp_dp (op2_reg _ _) fun s1 u1 => ?_
  have h1' : Ws s1 B Z W N := h.of_upd u1 (by decide) (by decide) (by decide)
  refine ptr_ok h1' (r := .r10) (by decide) (j := a) (by omega) fun s2 p2 r2 m2 h2 => ?_
  refine wp_mov (op2_reg _ _) fun s3 u3 => ?_
  refine wp_dp (op2_lsr (by decide)) fun s5 u5 => ?_
  refine wp_mov (op2_imm (by decide)) fun x u6 => WP.block_nil ?_
  have hx : Ws x B Z W N :=
    (((h2.of_upd u3 (by decide) (by decide) (by decide)).of_upd u5
      (by decide) (by decide) (by decide)).of_upd u6 (by decide) (by decide) (by decide))
  have mx : x.mem = s.mem := u6.mem.trans (u5.mem.trans (u3.mem.trans (m2.trans u1.mem)))
  have restX : Rest opRegs s x :=
    ((u1.rest (by simp)).trans ((r2.mono (by simp)).trans (u3.rest (by simp)))).trans
      ((u5.rest (by simp)).trans (u6.rest (by simp)))
  have p0 : x.gpr .r0 = B + BitVec.ofNat 32 (arr W o + 4 * sh) := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u3.other _ (by decide),
      r2.gpr _ (by decide), u1.gpr, dpVal, h0, h1, VG.Proof.Rsa.Arm.KeyDiv.add_ofNat_assoc]
  have p10 : x.gpr .r10 = B + BitVec.ofNat 32 (arr W a) := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u3.other _ (by decide), p2]
  have p12 : x.gpr .r12 = B + BitVec.ofNat 32 (arr W a) := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u3.gpr, p2]
  have plr : x.gpr .lr = BitVec.ofNat 32 (n - sh) := by
    rw [u6.other _ (by decide), u5.gpr, dpVal, u3.other .lr (by decide), r2.gpr .lr (by decide),
      u1.other .lr (by decide), hlr, u3.other .r1 (by decide), r2.gpr .r1 (by decide), u1.other .r1 (by decide), h1,
      VG.Proof.Rsa.Arm.KeyDiv.shr2_val (by omega), BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
  have sc : SubCtx x B Z (arr W o + 4 * sh) (arr W a) (arr W a) (n - sh) :=
    ⟨h.nowrap, by omega, by omega, by omega, by omega, by omega, by rw [restX.wr]; exact h.writable⟩
  refine WP.mono (copyWords_ok x sc (by omega) p0 p10 p12 plr) fun t inv => ?_
  have v := inv.value
  rw [mx, u6.gpr] at v
  refine ⟨hx.rest inv.rest, by simpa only [mx] using inv.outside, by simpa using v,
    restX.trans (inv.rest.mono (by simp))⟩

/-- `shiftUpB a`: from `[o]`'s address in `r0` and `4 sh` in `r1`, `[a]`'s low `W - sh` words
into `[o]` from word `sh`. -/
theorem shiftUpB_ok {s : State} {B : BitVec 32} {Z W N o a sh : Nat} (h : Ws s B Z W N) (ho : o < N) (ha : a < N)
    (hN : N ≤ 256) (hoa : o ≠ a) (hsh : sh < W) (h0 : s.gpr .r0 = B + BitVec.ofNat 32 (arr W o))
    (h1 : s.gpr .r1 = BitVec.ofNat 32 (4 * sh)) :
    WP isa (shiftUpB a) s fun t => Ws t B Z W N ∧ Outside (State.addr B) (arr W o + 4 * sh) (4 * (W - sh)) s.mem t.mem ∧
      val32 t.mem (State.addr B) (arr W o + 4 * sh) (W - sh) = val32 s.mem (State.addr B) (arr W a) (W - sh) ∧
      Rest opRegs s t := by
  rw [shiftUpB, WP.seq_iff]
  refine wp_mov (op2_reg _ _) fun s1 u1 => WP.block_nil ?_
  refine WP.mono (shiftUpBN_ok (h.of_upd u1 (by decide) (by decide) (by decide)) ho ha hN hoa hsh
    (Nat.le_refl _) (by rw [u1.other _ (by decide), h0]) (by rw [u1.other _ (by decide), h1])
    (by rw [u1.gpr, h.r9])) fun t ⟨ht, O, v, R⟩ => ?_
  rw [u1.mem] at O v
  exact ⟨ht, O, v, (u1.rest (by simp)).trans R⟩

/-- `shiftDownB o`: from `[a]`'s address in `r10` and `4 sh` in `r1`, `[a]`'s words from `sh`
into `[o]`'s low `W - sh`. -/
theorem shiftDownB_ok {s : State} {B : BitVec 32} {Z W N o a sh : Nat} (h : Ws s B Z W N) (ho : o < N) (ha : a < N)
    (hN : N ≤ 256) (hoa : o ≠ a) (hsh : sh < W) (h10 : s.gpr .r10 = B + BitVec.ofNat 32 (arr W a))
    (h1 : s.gpr .r1 = BitVec.ofNat 32 (4 * sh)) :
    WP isa (shiftDownB o) s fun t => Ws t B Z W N ∧ Outside (State.addr B) (arr W o) (4 * (W - sh)) s.mem t.mem ∧
      val32 t.mem (State.addr B) (arr W o) (W - sh) = val32 s.mem (State.addr B) (arr W a + 4 * sh) (W - sh) ∧
      Rest opRegs s t := by
  have := h.wle
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have da := arr_disj (w := W) hoa
  simp only [S] at fo fa da
  rw [shiftDownB, WP.seq_iff]
  simp only [List.cons_append, List.nil_append]
  refine wp_dp (op2_reg _ _) fun s1 u1 => ?_
  refine wp_mov (op2_reg _ _) fun s2 u2 => ?_
  have h2' : Ws s2 B Z W N := (h.of_upd u1 (by decide) (by decide) (by decide)).of_upd u2 (by decide) (by decide)
    (by decide)
  refine ptr_ok h2' (r := .r0) (by decide) (j := o) (by omega) fun s3 p3 r3 m3 h3 => ?_
  refine wp_mov (op2_reg _ _) fun s4 u4 => ?_
  refine wp_dp (op2_lsr (by decide)) fun s5 u5 => ?_
  refine wp_mov (op2_imm (by decide)) fun x u6 => WP.block_nil ?_
  have hx : Ws x B Z W N :=
    (((h3.of_upd u4 (by decide) (by decide) (by decide)).of_upd u5 (by decide) (by decide) (by decide)).of_upd u6
      (by decide) (by decide) (by decide))
  have mx : x.mem = s.mem := u6.mem.trans (u5.mem.trans (u4.mem.trans (m3.trans (u2.mem.trans u1.mem))))
  have restX : Rest opRegs s x :=
    ((u1.rest (by simp)).trans ((u2.rest (by simp)).trans (r3.mono (by simp)))).trans
      ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans (u6.rest (by simp))))
  have q10 : s1.gpr .r10 = B + BitVec.ofNat 32 (arr W a + 4 * sh) := by
    rw [u1.gpr, dpVal, h10, h1, VG.Proof.Rsa.Arm.KeyDiv.add_ofNat_assoc]
  have p0 : x.gpr .r0 = B + BitVec.ofNat 32 (arr W o) := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), p3]
  have p10 : x.gpr .r10 = B + BitVec.ofNat 32 (arr W a + 4 * sh) := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), r3.gpr _ (by decide),
      u2.other _ (by decide), q10]
  have p12 : x.gpr .r12 = B + BitVec.ofNat 32 (arr W a + 4 * sh) := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), r3.gpr _ (by decide), u2.gpr, q10]
  have plr : x.gpr .lr = BitVec.ofNat 32 (W - sh) := by
    rw [u6.other _ (by decide), u5.gpr, dpVal, u4.gpr, h3.r9, u4.other _ (by decide), r3.gpr _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide), h1, VG.Proof.Rsa.Arm.KeyDiv.shr2_val (by omega),
      BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
  have sc : SubCtx x B Z (arr W o) (arr W a + 4 * sh) (arr W a + 4 * sh) (W - sh) :=
    ⟨h.nowrap, by omega, by omega, by omega, by omega, by omega, by rw [restX.wr]; exact h.writable⟩
  refine WP.mono (copyWords_ok x sc (by omega) p0 p10 p12 plr) fun t inv => ?_
  have v := inv.value
  rw [mx, u6.gpr] at v
  refine ⟨hx.rest inv.rest, by simpa only [mx] using inv.outside, by simpa using v,
    restX.trans (inv.rest.mono (by simp))⟩

/-- A number of `W` words from its parts at word `sh`. -/
theorem numW_at (m : Mem) (B : BitVec 32) (W o sh : Nat) (hsh : sh ≤ W) :
    num m B W o = val32 m (State.addr B) (arr W o) sh +
      2 ^ (32 * sh) * val32 m (State.addr B) (arr W o + 4 * sh) (W - sh) := by
  have := val32_append m (State.addr B) (arr W o) sh (W - sh)
  rwa [Nat.add_sub_cancel' hsh] at this

/-- `shiftUpBy d o a`: `[o] := ([a] mod 2^(32 (W - sh))) 2^(32 sh)`, wide, for `4 sh` at `d`. -/
theorem shiftUpBy_vp {d sh o a : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (hsh : sh < P.W) (ho : o < 22) (ha : a ∈ LW) (hoa : o ≠ a) (hz : wZ ∈ LW) (hoz : o ≠ wZ)
    (hL : ∀ j ∈ L, j / 2 ≠ o) (hS : d ∈ LS) (z0 : ∀ σ, E σ → AW σ wZ = 0) (vS : ∀ σ, E σ → V σ d = 4 * sh)
    (certC : DCert (copy o wZ)) (certA : DCert (.block (ptr .r0 o ++ ([.ldr .r1 .r8 d] : List Instr))))
    (certB : ShiftCert .r0 (shiftUpB a)) :
    VP (Dk P E A L AW LW V LS P.W 22) (shiftUpBy d o a)
      (Dk P E A L (fun σ => upd (AW σ) o (AW σ a % 2 ^ (32 * (P.W - sh)) * 2 ^ (32 * sh))) (o :: LW) V LS
        P.W 22) := by
  simp only [shiftUpBy, seqs]
  refine VP.seq (G := Dk P E A L (fun σ => upd (AW σ) o 0) (o :: LW) V LS P.W 22)
    (VP.dctx certC (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_) ?_
  · refine WP.mono (h.copy_W hv (o := o) (a := wZ) ho hz hoz hL) fun t ⟨ht, hvt, _⟩ => ⟨e, ?_, hvt⟩
    rwa [z0 σ e] at ht
  refine VP.seq (G := fun σ t => Dk P E A L (fun σ => upd (AW σ) o 0) (o :: LW) V LS P.W 22 σ t ∧
      t.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W o) ∧ t.gpr .r1 = BitVec.ofNat 32 (4 * sh))
    (VP.dctx certA (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_)
    (VP.taint _ certB (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s ⟨⟨e, h, hv⟩, p0, p1⟩ => ?_)
  · refine ptr_ok hv (r := .r0) (by decide) (j := o) (by omega) fun s1 p1 r1 m1 hv1 => ?_
    have h1 := h.of_rest r1 m1 (by decide)
    refine h1.ldrSlot hv1 (d := d) hS (r := .r1) (by decide) fun t ht hvt U => WP.block_nil ⟨⟨e, ht, hvt⟩, ?_, ?_⟩
    · rw [U.other _ (by decide), p1]
    · rw [U.gpr, vS σ e]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]
    · rw [h₁.1.2.2.r7, h₂.1.2.2.r7]
    · rw [h₁.1.2.2.r8, h₂.1.2.2.r8]
    · rw [h₁.1.2.2.r9, h₂.1.2.2.r9]
  · have sz := h.sizes
    have Wl := sz.Wle
    have ha22 := h.liveW_lt a (List.mem_cons_of_mem _ ha)
    refine WP.mono (shiftUpB_ok hv ho ha22 (by decide) hoa hsh p0 p1) fun t ⟨hvt, O, V', R⟩ => ⟨e, ?_, hvt⟩
    have fo := fit_W sz ho
    simp only [S] at fo
    have k : Keep P.B P.W [o] [] s.mem t.mem := Keep.of_arr (d := 4 * sh) O (by simp only [S]; omega) (by simp)
    have v0 := h.arrsW o (List.mem_cons_self ..)
    simp only [upd_self] at v0
    rw [numW_at _ _ _ _ sh (by omega)] at v0
    have l0 : val32 s.mem (State.addr P.B) (arr P.W o) sh = 0 := by omega
    have va := h.arrsW a (List.mem_cons_of_mem _ ha)
    simp only [upd_ne _ _ (Ne.symm hoa)] at va
    have ev' : num t.mem P.B P.W o = AW σ a % 2 ^ (32 * (P.W - sh)) * 2 ^ (32 * sh) := by
      rw [numW_at _ _ _ _ sh (by omega), O.val32 (Or.inl (by omega)) (by omega), l0, V', ← va,
        val32_lo _ _ _ (show P.W - sh ≤ P.W by omega), Nat.zero_add, Nat.mul_comm]
    have h' := h.write_W k ho (by simp) (h.r8_of R) R.sp R.rd R.wr ev' hL (by simp)
    refine h'.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨List.mem_cons_of_mem _ hj, ?_⟩) (fun d hd => ⟨hd, rfl⟩)
    simp only [upd]; split <;> rfl

/-- `shiftUp o a`: `[o] := ([a] mod 2^(32 (W - s))) 2^(32 s)`, wide. -/
theorem shiftUp_vp {o a : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (ho : o < 22) (ha : a ∈ LW) (hoa : o ≠ a) (hz : wZ ∈ LW) (hoz : o ≠ wZ)
    (hL : ∀ j ∈ L, j / 2 ≠ o) (hS : sS ∈ LS) (z0 : ∀ σ, E σ → AW σ wZ = 0) (vS : ∀ σ, E σ → V σ sS = 4 * sA P)
    (certC : DCert (copy o wZ)) (certA : DCert (.block (ptr .r0 o ++ ([.ldr .r1 .r8 sS] : List Instr))))
    (certB : ShiftCert .r0 (shiftUpB a)) :
    VP (Dk P E A L AW LW V LS P.W 22) (shiftUp o a)
      (Dk P E A L (fun σ => upd (AW σ) o (AW σ a % 2 ^ (32 * (P.W - sA P)) * 2 ^ (32 * sA P))) (o :: LW) V LS
        P.W 22) :=
  VP.of_imp (p := sA P < P.W) (fun _ _ h => by
      obtain ⟨s3, sAW, ev⟩ := sA_facts h.2.1.sizes; omega)
    fun hsh => shiftUpBy_vp hsh ho ha hoa hz hoz hL hS z0 vS certC certA certB

/-- `shiftDownBy wZ d o a`: `[o] := ⌊[a] / 2^(32 sh)⌋`, wide, for `4 sh` at `d`. -/
theorem shiftDownBy_vp {d sh o a : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (hsh : sh < P.W) (ho : o < 22) (ha : a ∈ LW) (hoa : o ≠ a) (hz : wZ ∈ LW) (hoz : o ≠ wZ) (hL : ∀ j ∈ L, j / 2 ≠ o)
    (hS : d ∈ LS) (z0 : ∀ σ, E σ → AW σ wZ = 0) (vS : ∀ σ, E σ → V σ d = 4 * sh)
    (certC : DCert (copy o wZ)) (certA : DCert (.block (ptr .r10 a ++ ([.ldr .r1 .r8 d] : List Instr))))
    (certB : ShiftCert .r10 (shiftDownB o)) :
    VP (Dk P E A L AW LW V LS P.W 22) (shiftDownBy wZ d o a)
      (Dk P E A L (fun σ => upd (AW σ) o (AW σ a / 2 ^ (32 * sh))) (o :: LW) V LS P.W 22) := by
  simp only [shiftDownBy, seqs]
  refine VP.seq (G := Dk P E A L (fun σ => upd (AW σ) o 0) (o :: LW) V LS P.W 22)
    (VP.dctx certC (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_) ?_
  · refine WP.mono (h.copy_W hv (o := o) (a := wZ) ho hz hoz hL) fun t ⟨ht, hvt, _⟩ => ⟨e, ?_, hvt⟩
    rwa [z0 σ e] at ht
  refine VP.seq (G := fun σ t => Dk P E A L (fun σ => upd (AW σ) o 0) (o :: LW) V LS P.W 22 σ t ∧
      t.gpr .r10 = P.B + BitVec.ofNat 32 (arr P.W a) ∧ t.gpr .r1 = BitVec.ofNat 32 (4 * sh))
    (VP.dctx certA (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_)
    (VP.taint _ certB (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s ⟨⟨e, h, hv⟩, p10, p1⟩ => ?_)
  · have ha22 := h.liveW_lt a (List.mem_cons_of_mem _ ha)
    refine ptr_ok hv (r := .r10) (by decide) (j := a) (by omega) fun s1 p1 r1 m1 hv1 => ?_
    have h1 := h.of_rest r1 m1 (by decide)
    refine h1.ldrSlot hv1 (d := d) hS (r := .r1) (by decide) fun t ht hvt U => WP.block_nil ⟨⟨e, ht, hvt⟩, ?_, ?_⟩
    · rw [U.other _ (by decide), p1]
    · rw [U.gpr, vS σ e]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]
    · rw [h₁.1.2.2.r7, h₂.1.2.2.r7]
    · rw [h₁.1.2.2.r8, h₂.1.2.2.r8]
    · rw [h₁.1.2.2.r9, h₂.1.2.2.r9]
  · have sz := h.sizes
    have Wl := sz.Wle
    have ha22 := h.liveW_lt a (List.mem_cons_of_mem _ ha)
    refine WP.mono (shiftDownB_ok hv ho ha22 (by decide) hoa (by omega) p10 p1) fun t ⟨hvt, O, V', R⟩ =>
      ⟨e, ?_, hvt⟩
    have fo := fit_W sz ho
    have fa := fit_W sz ha22
    simp only [S] at fo fa
    have k : Keep P.B P.W [o] [] s.mem t.mem := Keep.of_arr (d := 0) (by simpa using O) (by simp only [S]; omega)
      (by simp)
    have v0 := h.arrsW o (List.mem_cons_self ..)
    simp only [upd_self] at v0
    rw [numW_at _ _ _ _ (P.W - sh) (by omega)] at v0
    have h0 : val32 s.mem (State.addr P.B) (arr P.W o + 4 * (P.W - sh)) (P.W - (P.W - sh)) = 0 := by
      have := Nat.two_pow_pos (32 * (P.W - sh))
      rcases Nat.eq_zero_or_pos (val32 s.mem (State.addr P.B) (arr P.W o + 4 * (P.W - sh)) (P.W - (P.W - sh)))
        with c | c
      · exact c
      · have := Nat.mul_pos this c; omega
    have va := h.arrsW a (List.mem_cons_of_mem _ ha)
    simp only [upd_ne _ _ (Ne.symm hoa)] at va
    rw [numW_at _ _ _ _ (sh) (by omega)] at va
    have ev' : num t.mem P.B P.W o = AW σ a / 2 ^ (32 * sh) := by
      rw [numW_at _ _ _ _ (P.W - sh) (by omega),
        O.val32 (d := arr P.W o + 4 * (P.W - sh)) (k := P.W - (P.W - sh)) (Or.inr (by omega)) (by omega), h0,
        V', ← va,
        Nat.mul_zero, Nat.add_zero, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
        Nat.div_eq_of_lt (val32_lt _ _ _ _), Nat.zero_add]
    have h' := h.write_W k ho (by simp) (h.r8_of R) R.sp R.rd R.wr ev' hL (by simp)
    refine h'.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨List.mem_cons_of_mem _ hj, ?_⟩) (fun d hd => ⟨hd, rfl⟩)
    simp only [upd]; split <;> rfl

/-- `shiftDown o a`: `[o] := ⌊[a] / 2^(32 s)⌋`, wide. -/
theorem shiftDown_vp {o a : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (ho : o < 22) (ha : a ∈ LW) (hoa : o ≠ a) (hz : wZ ∈ LW) (hoz : o ≠ wZ) (hL : ∀ j ∈ L, j / 2 ≠ o)
    (hS : sS ∈ LS) (z0 : ∀ σ, E σ → AW σ wZ = 0) (vS : ∀ σ, E σ → V σ sS = 4 * sA P)
    (certC : DCert (copy o wZ)) (certA : DCert (.block (ptr .r10 a ++ ([.ldr .r1 .r8 sS] : List Instr))))
    (certB : ShiftCert .r10 (shiftDownB o)) :
    VP (Dk P E A L AW LW V LS P.W 22) (shiftDown o a)
      (Dk P E A L (fun σ => upd (AW σ) o (AW σ a / 2 ^ (32 * sA P))) (o :: LW) V LS P.W 22) :=
  VP.of_imp (p := sA P < P.W) (fun _ _ h => by
      obtain ⟨s3, sAW, ev⟩ := sA_facts h.2.1.sizes; omega)
    fun hsh => shiftDownBy_vp hsh ho ha hoa hz hoz hL hS z0 vS certC certA certB

/-- The product `a`. -/
abbrev aV (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat :=
  (pr g (AG P f σ aG) (AWG P f σ wX3) (32 * P.w)).2.2

/-- The narrow constants and `n`. -/
def AB (P : RP) : Nat → Nat := upd (upd (upd (fun _ => 0) aOneN 1) aZN 0) aN P.n
abbrev LB : List Nat := [aN, aZN, aOneN]

/-- `a` modulo `2^(32 (W - s))`, the words the shifted division keeps, and `m` and `r` from it:
`⌊a / n⌋` and `a mod n` where `a` is below `2^(32 (W - s))`, which `m < n` needs. -/
abbrev a0V (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat :=
  aV P f g σ % 2 ^ (32 * (P.W - sA P))
abbrev mV (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat := a0V P f g σ / P.n
abbrev rV (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat := a0V P f g σ % P.n

def AWA1 (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (upd (upd (upd (fun _ => 0) wZ 0) wOne 1) wA (aV P f g σ)) wN P.n
def AWA2 (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (upd (AWA1 P f g σ) wA (mV P f g σ)) wR (rV P f g σ)
abbrev LWA : List Nat := [wR, wA, wN, wOne, wZ, 0]

/-- Ready for the shifts. -/
abbrev DA1 (P : RP) (E : State → Prop) (f g : Nat × Nat × Nat → Nat × Nat × Nat) : State → State → Prop :=
  Dk P E (fun _ => AB P) LB (AWA1 P f g) [wN, wA, wOne, wZ] (VG' P) [sOkDE] P.W 22

theorem divAPre_vp {f g : Nat × Nat × Nat → Nat × Nat × Nat} (hg : ProdF P g) {E : State → Prop} :
    VP (fun σ s => E σ ∧ RI P aG wX3 wA (AG P f) LG (AWG P f) LWT (VG' P) [sOkDE] σ s) divAPre
      (DA1 P E f g) := by
  refine VP.dctx divAPre_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h0, hv⟩ => ?_
  have sz := h0.sizes
  have av : aV P f g σ = AG P f σ aG % 2 ^ (32 * P.w) * AWG P f σ wX3 % 2 ^ (32 * P.W) := by
    have := h0.lt_W (j := wX3) (by decide)
    rw [upd_ne _ _ (by decide)] at this
    exact pr_rows hg this _
  have h := h0.mono (A' := AB P) (live' := LB) (AW' := upd (upd (upd (fun _ => 0) wZ 0) wOne 1) wA (aV P f g σ))
    (liveW' := [wA, wOne, wZ]) (V' := VG' P σ) (ls' := [sOkDE])
    (fun j hj => by
      simp only [LB, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;> simp only [AB, AG] <;> rd_ev)
    (fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;> simp only [AWG, av] <;> rd_ev)
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
  rw [← List.append_nil toW]
  refine h4.toW hv4 fun t ht hvt _ => WP.block_nil ⟨e, ?_, hvt⟩
  refine ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, ?_⟩) (fun d hd => ⟨hd, rfl⟩)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl <;> simp only [AWA1, AB] <;> rd_ev

/-- `shiftAmt`: `4 s` into `sS`, from `n_len`. -/
theorem shiftAmt_vp {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat} :
    VP (Dk P E A L AW LW V LS P.W 22) shiftAmt (Dk P E A L AW LW (fun σ => upd (V σ) sS (4 * sA P)) (sS :: LS) P.W 22) := by
  refine VP.seq (G := fun σ s => Dk P E A L AW LW V LS P.W 22 σ s ∧ s.gpr .r1 = BitVec.ofNat 32 P.K)
    (VP.ldrSp (c := [(.r1, VG.Impl.Rsa.Arm.Recover.aoK)]) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, hv⟩ => ?_)
    (VP.taint _ shiftAmtB_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s ⟨⟨e, h, hv⟩, p1⟩ => ?_)
  · rw [h₁.2.1.bs.sp, h₁.2.1.bs.pre.sp, h₂.2.1.bs.sp, h₂.2.1.bs.pre.sp]
  · refine h.bs.ldrSp (o := VG.Impl.Rsa.Arm.Recover.aoK) (by decide) (by decide) (by decide) fun t u => WP.block_nil ?_
    obtain ⟨ht, hvt⟩ := h.reg hv (u.rest (ws := [.r1]) (by simp)) u.mem
    exact ⟨⟨e, ht, hvt⟩, by rw [u.gpr, h.bs.pre.aK]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.2, h₂.2]
    · rw [h₁.1.2.2.r7, h₂.1.2.2.r7]
    · rw [h₁.1.2.2.r8, h₂.1.2.2.r8]
    · rw [h₁.1.2.2.r9, h₂.1.2.2.r9]
  · have sz := h.sizes
    obtain ⟨s3, sAW, ev⟩ := sA_facts sz
    have kw := sz.kw
    have Wl := sz.Wle
    unfold shiftAmtB
    refine wp_dp (op2_imm (by decide)) fun s1 u1 => ?_
    refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
    refine wp_mov (op2_lsl (by decide)) fun s3 u3 => ?_
    refine wp_dp (op2_lsl (by decide)) fun s4 u4 => ?_
    have mm : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
    obtain ⟨h4, hv4⟩ := h.reg hv (((u1.rest (ws := [.r0, .r1]) (by simp)).trans (u2.rest (by simp))).trans
      ((u3.rest (by simp)).trans (u4.rest (by simp)))) mm
    refine h4.strSlot hv4 (d := sS) (r := .r0) (by decide) fun t ht hvt _ _ => WP.block_nil ⟨e, ?_, hvt⟩
    have e0 : (s4.gpr .r0).toNat = 4 * sA P := by
      rw [u4.gpr, dpVal, u3.gpr, u3.other .r1 (by decide), u2.gpr, u2.other .r9 (by decide), u1.gpr,
        u1.other .r9 (by decide), hv.r9, dpVal, p1]
      rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
        BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
        Nat.shiftRight_eq_div_pow, show (3 : BitVec 32).toNat = 3 from rfl]
      have := sz.wle
      simp only [sA] at sAW ⊢
      omega
    rwa [e0] at ht

/-- A word `k` of a number between `2^(32 k)` and `2^(32 (k + 1))`, not zero. -/
theorem top_pos {m : Mem} {B : BitVec 32} {W j k M : Nat} (hk : k < W) (hM : num m B W j = M)
    (hlo : 2 ^ (32 * k) ≤ M) (hhi : M < 2 ^ (32 * (k + 1))) :
    0 < w32 m (State.addr B) (arr W j + 4 * k) := by
  rw [numW_at _ _ _ _ k (by omega)] at hM
  have e : val32 m (State.addr B) (arr W j + 4 * k) (W - k) =
      w32 m (State.addr B) (arr W j + 4 * k) + 2 ^ 32 * val32 m (State.addr B) (arr W j + 4 * k + 4) (W - k - 1) := by
    rw [show W - k = W - k - 1 + 1 by omega, val32]; rfl
  rw [e] at hM
  have hl := val32_lt m (State.addr B) (arr W j) k
  rcases Nat.eq_zero_or_pos (w32 m (State.addr B) (arr W j + 4 * k)) with c | c
  · rw [c, Nat.zero_add] at hM
    rcases Nat.eq_zero_or_pos (val32 m (State.addr B) (arr W j + 4 * k + 4) (W - k - 1)) with d | d
    · rw [d, Nat.mul_zero, Nat.mul_zero, Nat.add_zero] at hM; omega
    · have p : 2 ^ (32 * (k + 1)) ≤ 2 ^ (32 * k) * (2 ^ 32 * val32 m (State.addr B) (arr W j + 4 * k + 4) (W - k - 1)) := by
        rw [Nat.mul_succ, Nat.pow_add]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ d)
      omega
  · exact c

/-- The header's `W`, `divW a r m t nm u` with the quotient into `q`, and `w` back:
`q := ⌊[a] / [m]⌋`, `r := [a] mod [m]`, for `[m]` of `W / 2` words with its top word not zero,
`[0]` and `[q]` zero. -/
theorem divMid_vp {a r m t nm u q : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (T : VG.Proof.Rsa.Arm.KeyDiv.DivTaint a r m t nm u none (some q))
    (hq : VG.Proof.Rsa.Arm.KeyDiv.QArr 22 r m t nm u (some q))
    (hidx : a < 22 ∧ r < 22 ∧ m < 22 ∧ t < 22 ∧ nm < 22 ∧ u < 22)
    (hne : r ≠ a ∧ r ≠ t ∧ r ≠ u ∧ t ≠ u ∧ m ≠ r ∧ m ≠ t ∧ m ≠ u ∧ nm ≠ r ∧ t ≠ nm ∧ nm ≠ u ∧ nm ≠ m ∧ r ≠ 0 ∧
      t ≠ 0 ∧ u ≠ 0 ∧ nm ≠ 0)
    (ha : a ∈ LW) (hm : m ∈ LW) (h0 : 0 ∈ LW) (hA : q ∈ LW)
    (hLW : ∀ j ∈ LW, j ≠ r ∧ j ≠ t ∧ j ≠ u ∧ j ≠ nm)
    (hL : ∀ j ∈ L, j / 2 ≠ r ∧ j / 2 ≠ t ∧ j / 2 ≠ u ∧ j / 2 ≠ nm ∧ j / 2 ≠ q)
    (hLS : ∀ d ∈ LS, ∀ e ∈ VG.Proof.Rsa.Arm.KeyDiv.divSlots, d + 4 ≤ e ∨ e + 4 ≤ d)
    (z0 : ∀ σ, E σ → AW σ 0 = 0) (zA : ∀ σ, E σ → AW σ q = 0)
    (hM : ∀ σ, E σ → 2 ^ (32 * (P.W / 2 - 1)) ≤ AW σ m ∧ AW σ m < 2 ^ (32 * (P.W / 2))) :
    VP (Dk P E A L AW LW V LS P.W 22)
      (seqs [.block [.str .r9 .r8 16], VG.Impl.Rsa.Arm.KeyDiv.divW a r m t nm u none (some q), .block restoreW])
      (Dk P E A L (fun σ => upd (upd (AW σ) q (AW σ a / AW σ m)) r (AW σ a % AW σ m)) (r :: q :: LW) V LS
        P.w nArr) := by
  obtain ⟨ia, ir, im, it, inm, iu⟩ := hidx
  obtain ⟨hra, hrt, hru, htu, hmr, hmt, hmu, hnr, htn, hnu, hnm', hr0, ht0, hu0, hn0⟩ := hne
  have hqr : q ≠ r := hq.2.1
  have hq22 : q < 22 := hq.1
  simp only [seqs]
  let K1 := fun σ t => E σ ∧ KSW P σ (A σ) L (AW σ) LW (V σ) LS t ∧ Ws t P.B P.Z P.W 22
  let AW' := fun σ => upd (upd (AW σ) q (AW σ a / AW σ m)) r (AW σ a % AW σ m)
  have pre : ∀ σ s, K1 σ s → VG.Proof.Rsa.Arm.KeyDiv.DivPre P.B P.Z P.W 22 m s a none ∧
      VG.Proof.Rsa.Arm.KeyDiv.QZ s.mem P.B P.W (some q) := fun σ s ⟨e, h, hv⟩ => by
    have sz := h.sizes
    have Wl := sz.Wle
    have ws : 6 ≤ P.W := by have := sz.w6a; simp only [RP.W, RP.w]; omega
    obtain ⟨mlo, mhi⟩ := hM σ e
    refine ⟨⟨hv, ?_, by rw [h.arrsW m hm]; exact mhi, top_pos (k := P.W / 2 - 1) (by omega) (h.arrsW m hm) mlo
      (by rwa [show P.W / 2 - 1 + 1 = P.W / 2 by omega]), by rw [h.arrsW 0 h0]; exact z0 σ e, trivial⟩, ?_⟩
    · simp only [slot, w32]; rw [h.cnt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · show num s.mem P.B P.W q = 0
      rw [h.arrsW q hA]; exact zA σ e
  refine VP.seq (G := K1) (VP.dctx hdrW_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_) (VP.seq
    (G := fun σ t => E σ ∧ KSW P σ (A σ) L (AW' σ) (r :: q :: LW) (V σ) LS t)
    (VP.of_ct (fun σ₁ σ₂ => (VG.Proof.Rsa.Arm.KeyDiv.divWG_ct T hq ia ir im it inm iu (by decide) hra hrt hru htu
      hmr hmt hmu hnr htn hnu hnm' hr0 ht0 hu0 hn0 (w := P.W) (B := P.B) (Z := P.Z) (N := 22)
      (by simp only [RP.W, RP.w]; omega)).mono
      (fun s t h => ⟨pre σ₁ s h.1, pre σ₂ t h.2⟩) fun _ _ _ => trivial) fun σ s hs => ?_)
    (VP.taint [.r8] restoreW_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_)
      fun σ s ⟨e, h⟩ => WP.mono h.restore fun t ⟨ht, hvt⟩ => ⟨e, ht, hvt⟩))
  · rw [← List.append_nil [Instr.str .r9 .r8 16]]
    exact h.toKSW hv fun t ht hvt _ => WP.block_nil ⟨e, ht, hvt⟩
  · obtain ⟨e, h, hv⟩ := hs
    obtain ⟨⟨_, h16, hMl, hT0, hz, _⟩, hq0⟩ := pre σ s ⟨e, h, hv⟩
    have sz := h.sizes
    have ws : 6 ≤ P.W := by have := sz.w6a; simp only [RP.W, RP.w]; omega
    rw [h.arrsW m hm] at hMl
    refine WP.mono (VG.Proof.Rsa.Arm.KeyDiv.divWG_ok (a := a) (r := r) (m := m) (t := t) (nm := nm) (u := u) hv
      ia ir im it inm iu (by decide) hra hrt hru htu hmr hmt hmu hnr htn hnu hnm' hr0 ht0 hu0 hn0
      ws h16 (h.arrsW m hm) hMl hT0 hz (top := none) trivial (qo := some q) hq hq0)
      fun t ⟨hvt, vr, _, k, vq, r'⟩ => ⟨e, ?_⟩
    simp only [VG.Proof.Rsa.Arm.KeyDiv.QV, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mul_one] at vq
    rw [h.arrsW a ha] at vr vq
    refine h.core2 k (by
        simp only [VG.Proof.Rsa.Arm.KeyDiv.qList, List.cons_append, List.nil_append, List.mem_cons,
          List.not_mem_nil, or_false]
        rintro x (rfl | rfl | rfl | rfl | rfl) <;> with_reducible assumption) (by decide)
      (by rw [r'.gpr _ (by decide), h.r8]) r'.sp r'.rd r'.wr
      (fun j hj i hi => by
        have := hL j hj
        simp only [VG.Proof.Rsa.Arm.KeyDiv.qList, List.cons_append, List.nil_append, List.mem_cons,
          List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl <;> omega)
      (fun d hd e he => hLS d hd e he) (fun j hj => ?_) (fun j hj => ?_)
    · rcases List.mem_cons.mp hj with rfl | hj
      · simp only [AW', upd_self]; exact vr
      rcases List.mem_cons.mp hj with rfl | hj
      · simp only [AW', upd_ne _ _ hqr, upd_self]; exact vq
      · have ⟨ar, at', au, anm⟩ := hLW j hj
        by_cases ja : j = q
        · subst ja; simp only [AW', upd_ne _ _ hqr, upd_self]; exact vq
        · simp only [AW', upd_ne _ _ ar, upd_ne _ _ ja]
          rw [k.num (by
            simp only [VG.Proof.Rsa.Arm.KeyDiv.qList, List.cons_append, List.nil_append, List.mem_cons,
              List.not_mem_nil, or_false]
            rintro x (rfl | rfl | rfl | rfl | rfl) <;> omega) (by decide) (fit_W sz (h.liveW_lt j hj))]
          exact h.arrsW j hj
    · rcases List.mem_cons.mp hj with rfl | hj
      · exact ir
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hq22
      · exact h.liveW_lt j hj
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.r8, h₂.2.r8]

/-- `divMid_vp` for the first division. -/
theorem divAMid_vp {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (h3 : 3 ∈ LW) (h15 : 15 ∈ LW) (h0 : 0 ∈ LW) (hA : wA ∈ LW)
    (hLW : ∀ j ∈ LW, j ≠ 12 ∧ j ≠ 18 ∧ j ≠ 11 ∧ j ≠ 10)
    (hL : ∀ j ∈ L, j / 2 ≠ 12 ∧ j / 2 ≠ 18 ∧ j / 2 ≠ 11 ∧ j / 2 ≠ 10 ∧ j / 2 ≠ wA)
    (hLS : ∀ d ∈ LS, ∀ e ∈ VG.Proof.Rsa.Arm.KeyDiv.divSlots, d + 4 ≤ e ∨ e + 4 ≤ d)
    (z0 : ∀ σ, E σ → AW σ 0 = 0) (zA : ∀ σ, E σ → AW σ wA = 0)
    (hM : ∀ σ, E σ → 2 ^ (32 * (P.W / 2 - 1)) ≤ AW σ 15 ∧ AW σ 15 < 2 ^ (32 * (P.W / 2))) :
    VP (Dk P E A L AW LW V LS P.W 22)
      (seqs [.block [.str .r9 .r8 16], VG.Impl.Rsa.Arm.KeyDiv.divW 3 12 15 18 10 11 none (some wA), .block restoreW])
      (Dk P E A L (fun σ => upd (upd (AW σ) wA (AW σ 3 / AW σ 15)) 12 (AW σ 3 % AW σ 15)) (12 :: wA :: LW) V LS
        P.w nArr) :=
  divMid_vp divAW_taint (by simp only [VG.Proof.Rsa.Arm.KeyDiv.QArr]; decide) (by decide) (by decide) h3 h15 h0 hA
    (fun j hj => by have := hLW j hj; omega) hL hLS z0 zA hM

/-- What the shifted division needs of `n`: below `2^(32 ⌈n_len / 4⌉)`, its top word there not
zero, and `n²` below `2^(32 (W - s))`. -/
theorem n_facts (sz : Sizes P) (hlo : 256 ^ (P.K - 1) ≤ P.n) (hhi : P.n < 2 ^ (8 * P.K)) :
    2 ^ (32 * (P.W / 2 - 1)) ≤ P.n * 2 ^ (32 * sA P) ∧ P.n * 2 ^ (32 * sA P) < 2 ^ (32 * (P.W / 2)) ∧
      P.n * P.n ≤ 2 ^ (32 * (P.W - sA P)) ∧ P.n < 2 ^ (32 * (P.W - sA P)) := by
  obtain ⟨s3, sAW, ev⟩ := sA_facts sz
  have kw := sz.kw
  have k1 : 1 ≤ P.K := by
    rcases Nat.eq_zero_or_pos P.K with h | h
    · rw [h] at hlo hhi; simp at hlo hhi; omega
    · exact h
  have hi : P.n < 2 ^ (32 * ((P.K + 3) / 4)) :=
    Nat.lt_of_lt_of_le hhi (Nat.pow_le_pow_right (by decide) (by omega))
  have lo : 2 ^ (32 * ((P.K + 3) / 4 - 1)) ≤ P.n := by
    have e : (256 : Nat) ^ (P.K - 1) = 2 ^ (8 * (P.K - 1)) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
    rw [e] at hlo
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hlo
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show 32 * (P.W / 2 - 1) = 32 * ((P.K + 3) / 4 - 1) + 32 * sA P by omega, Nat.pow_add]
    exact Nat.mul_le_mul_right _ lo
  · rw [show 32 * (P.W / 2) = 32 * ((P.K + 3) / 4) + 32 * sA P by omega, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right hi (Nat.two_pow_pos _)
  · refine Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt hi) (Nat.le_of_lt hi)) ?_
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  · exact Nat.lt_of_lt_of_le hi (Nat.pow_le_pow_right (by decide) (by omega))

/-- `m < n` from the shifted division: `a` below `2^(32 (W - s))`, or else `m ≥ n` anyway. -/
theorem lt_flag {a n Q : Nat} (hn : 0 < n) (hQ : n * n ≤ Q) :
    (if b2n (decide (a % Q / n < n)) = 1 ∧ (if a = a % Q then 1 else 0) = 1 then 1 else 0) =
      b2n (decide (a / n < n)) := by
  have hQ0 : 0 < Q := Nat.lt_of_lt_of_le (Nat.mul_pos hn hn) hQ
  by_cases ha : a < Q
  · rw [Nat.mod_eq_of_lt ha]
    unfold b2n
    by_cases c : a / n < n <;> simp [c]
  · have e : a ≠ a % Q := fun e => ha (e ▸ Nat.mod_lt _ hQ0)
    have : n ≤ a / n := (Nat.le_div_iff_mul_le hn).mpr (by omega)
    simp only [e, ite_false, show ¬ (0 : Nat) = 1 by decide, and_false]
    unfold b2n
    simp [Nat.not_lt.mpr this]

/-! ## Pieces on the wide arrays -/

theorem toW_vp {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat} :
    VP (Dk P E A L AW LW V LS P.w nArr) (.block toW) (Dk P E A L AW LW V LS P.W 22) :=
  VP.dctx toW_taint (fun _ _ h => h.2.2) fun _ _ ⟨e, h, hv⟩ => by
    rw [← List.append_nil toW]; exact h.toW hv fun t ht hvt _ => WP.block_nil ⟨e, ht, hvt⟩

theorem copyW_vp {o a : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (ho : o < 22) (ha : a ∈ LW) (hoa : o ≠ a) (hL : ∀ j ∈ L, j / 2 ≠ o) (cert : DCert (copy o a)) :
    VP (Dk P E A L AW LW V LS P.W 22) (copy o a)
      (Dk P E A L (fun σ => upd (AW σ) o (AW σ a)) (o :: LW) V LS P.W 22) :=
  VP.dctx cert (fun _ _ h => h.2.2) fun _ _ ⟨e, h, hv⟩ =>
    WP.mono (h.copy_W hv ho ha hoa hL) fun _ ⟨ht, hvt, _⟩ => ⟨e, ht, hvt⟩

theorem eqSW_vp {d a b t : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (ha : a ∈ LW) (hb : b ∈ LW) (hd : SlotOk d) (ht : t < 22) (htW : t ∉ LW) (hl : ∀ j ∈ L, j / 2 ≠ t)
    (hls : ∀ e ∈ LS, e + 4 ≤ sT ∨ sT + 4 ≤ e) (hdT : d ≠ sT) (cert : DCert (eqS d a b t)) :
    VP (Dk P E A L AW LW V LS P.W 22) (eqS d a b t)
      (Dk P E A L AW LW (fun σ => upd (V σ) d (if AW σ a = AW σ b then 1 else 0)) (d :: LS) P.W 22) :=
  VP.dctx cert (fun _ _ h => h.2.2) fun _ _ ⟨e, h, hv⟩ =>
    WP.mono (h.eqS_W hv ha hb hd ht htW hl hls hdT) fun _ ⟨ht', hvt, _⟩ => ⟨e, ht', hvt⟩

theorem subW_vp {o a b : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (ho : o < 22) (ha : a ∈ LW) (hb : b ∈ LW) (hoa : o ≠ a) (hob : o ≠ b) (hl : ∀ j ∈ L, j / 2 ≠ o)
    (cert : DCert (sub3 o a b)) :
    VP (Dk P E A L AW LW V LS P.W 22) (sub3 o a b)
      (fun σ s => Dk P E A L (fun σ => upd (AW σ) o (sub32 P.W (AW σ a) (AW σ b))) (o :: LW) V LS P.W 22 σ s ∧
        (s.gpr .r11).toNat = b2n (decide (AW σ a < AW σ b))) :=
  VP.dctx cert (fun _ _ h => h.2.2) fun _ _ ⟨e, h, hv⟩ =>
    WP.mono (h.sub_W hv ho ha hb hoa hob hl) fun _ ⟨ht, hvt, _, c⟩ => ⟨⟨e, ht, hvt⟩, c⟩

/-- After the wide division and `m < n`. -/
def VA (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (VG' P σ) sLt (b2n (decide (aV P f g σ / P.n < P.n)))

/-- The division's values from the shifted ones. -/
theorem shifted_vals {a n Pw : Nat} (hP : 0 < Pw) :
    a * Pw / Pw = a ∧ a * Pw / (n * Pw) = a / n ∧ a * Pw % (n * Pw) / Pw = a % n :=
  ⟨Nat.mul_div_cancel _ hP, Nat.mul_div_mul_right _ _ hP, by rw [Nat.mul_mod_mul_right, Nat.mul_div_cancel _ hP]⟩

theorem divA_vp {f g : Nat × Nat × Nat → Nat × Nat × Nat} (hg : ProdF P g) {E : State → Prop}
    (hn : ∀ σ, E σ → Sizes P ∧ 256 ^ (P.K - 1) ≤ P.n ∧ P.n < 2 ^ (8 * P.K)) (hn0 : 0 < P.n) :
    VP (fun σ s => E σ ∧ RI P aG wX3 wA (AG P f) LG (AWG P f) LWT (VG' P) [sOkDE] σ s) divA
      (Dk P E (fun _ => AB P) LB (AWA2 P f g) LWA (VA P f g) [sLt, sOkDE] P.w nArr) := by
  simp only [divA, divAW, divAPost, seqs]
  refine (divAPre_vp hg).seq (VP.seq (shiftAmt_vp.seq
    ((shiftUp_vp (o := 3) (a := wA) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (fun σ _ => by simp only [AWA1]; rd_up) (fun σ _ => by rd_up) copy3_taint upA3_taint
      upBA_taint).seq
    ((shiftDown_vp (o := 12) (a := 3) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun σ _ => by simp only [AWA1]; rd_up) (fun σ _ => by rd_up) copy12_taint downA3_taint
      downB12_taint).seq
    ((eqSW_vp (d := sAok) (a := wA) (b := 12) (t := 18) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) eqAok_taint).seq
    ((shiftUp_vp (o := 15) (a := wN) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (fun σ _ => by simp only [AWA1]; rd_up) (fun σ _ => by rd_up) copy15_taint upA15_taint
      upBN_taint).seq
    ((copyW_vp (o := 0) (a := wZ) (by decide) (by decide) (by decide) (by decide) copy0_taint).seq
    ((copyW_vp (o := wA) (a := wZ) (by decide) (by decide) (by decide) (by decide) copyA_taint).seq
    ((divAMid_vp (LW := [wA, 0, 15, 3, wN, wOne, wZ]) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (fun σ _ => by simp only [AWA1]; rd_up)
      (fun σ _ => by simp only [AWA1]; rd_up) (fun σ e => by
        obtain ⟨sz, h1, h2⟩ := hn σ e
        obtain ⟨lo, hi, -, nW⟩ := n_facts sz h1 h2
        simp only [AWA1]; rd_up
        rw [Nat.mod_eq_of_lt nW]
        exact ⟨lo, hi⟩)).mono (fun σ s ⟨e, h, hv⟩ => ⟨e, h.mono (fun j hj => ⟨hj, rfl⟩)
        (fun j hj => ⟨by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega, rfl⟩)
        (fun d hd => ⟨hd, rfl⟩), hv⟩) fun _ _ h => h)))))))) ?_)
  refine toW_vp.seq ((shiftDown_vp (o := wR) (a := 12) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun σ _ => by simp only [AWA1]; rd_up) (fun σ _ => by rd_up) copyR_taint downA12_taint
    downBR_taint).seq ((subW_vp (o := wT1) (a := wA) (b := wN) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) subLt_taint).seq ?_))
  refine VP.dctx ltAok_taint (fun _ _ h => h.1.2.2) fun σ s ⟨⟨e, h, hv⟩, c⟩ => ?_
  obtain ⟨sz, h1, h2⟩ := hn σ e
  obtain ⟨-, -, nn, nW⟩ := n_facts sz h1 h2
  have hP := Nat.two_pow_pos (32 * sA P)
  obtain ⟨d1, -, d3⟩ := shifted_vals (a := aV P f g σ % 2 ^ (32 * (P.W - sA P))) (n := P.n) hP
  have d2 := (shifted_vals (a := aV P f g σ % 2 ^ (32 * (P.W - sA P))) (n := P.n) hP).2.1
  rw [List.append_assoc]
  refine h.brw hv (d := sLt) (by decide) fun s1 h1 hv1 _ => ?_
  refine h1.andS hv1 (d := sLt) (a := sLt) (b := sAok) (by simp) (by simp) ?_ ?_ (by decide) fun s2 h2 hv2 => ?_
  · rw [upd_self, c]; exact b2n_lt_one _
  · rd_up; split <;> omega
  rw [← List.append_nil toN]
  refine h2.toN hv2 fun t ht hvt _ => WP.block_nil ⟨e, ?_, hvt⟩
  refine ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ?_) (fun d hd => ?_)
  · simp only [LWA, List.mem_cons, List.not_mem_nil, or_false] at hj
    refine ⟨by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> decide, ?_⟩
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [AWA2, AWA1] <;> rd_up
    · rw [Nat.mod_eq_of_lt nW, d3]
    · rw [Nat.mod_eq_of_lt nW, d2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    refine ⟨by rcases hd with rfl | rfl <;> decide, ?_⟩
    rcases hd with rfl | rfl
    · simp only [VA, AWA1]; rd_up
      rw [c, d1]; simp only [AWA1]; rd_up
      rw [Nat.mod_eq_of_lt nW, d2]
      exact lt_flag hn0 nn
    · simp only [VA]; rd_up

/-- `m mod 2^(32 w) + 1` modulo `2^(32 w)` (1 where that is zero), `n - r mod 2^(32 w)`, and their
quotient and remainder. -/
abbrev m1R (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat :=
  sub32 P.w (mV P f g σ % 2 ^ (32 * P.w)) (sub32 P.w 0 1)
abbrev m1V (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat :=
  if m1R P f g σ = 0 then 1 else m1R P f g σ
abbrev dV (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat :=
  sub32 P.w P.n (rV P f g σ % 2 ^ (32 * P.w))
abbrev qV (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat := dV P f g σ / m1V P f g σ
abbrev remV (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat := dV P f g σ % m1V P f g σ

def ABd (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (upd (AB P) aM1 (m1V P f g σ)) aD (dV P f g σ)
def AWB (P : RP) : Nat → Nat := upd (upd (upd (fun _ => 0) wZ 0) wOne 1) wN P.n
abbrev LWB : List Nat := [wN, wOne, wZ]
/-- With the wide array `0`, zero, which the division by words needs. -/
abbrev LWB0 : List Nat := [wN, wOne, wZ, 0]

/-- Ready for the narrow division. -/
abbrev DB1 (P : RP) (E : State → Prop) (f g : Nat × Nat × Nat → Nat × Nat × Nat) : State → State → Prop :=
  Dk P E (ABd P f g) [aD, aM1, aN, aZN, aOneN] (fun _ => AWB P) LWB0 (VA P f g) [sLt, sOkDE] P.w nArr

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
  have h4' := h4.mono (A' := upd (upd (upd (AB P) aT1 (m1R P f g σ)) aRlo (rV P f g σ % 2 ^ (32 * P.w)))
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
  refine WP.mono (h6.sub_w hv6 (o := aD) (a := aN) (b := aRlo) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t ⟨h7, hv7, _, _⟩ => ⟨e, ?_, hv7⟩
  refine h7.mono (fun j hj => ?_) (fun j hj => ?_) (fun d hd => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    refine ⟨by rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide, ?_⟩
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp only [ABd, AB, m1V] <;> rd_ev
  · simp only [LWB0, List.mem_cons, List.not_mem_nil, or_false] at hj
    refine ⟨by rcases hj with rfl | rfl | rfl | rfl <;> decide, ?_⟩
    rcases hj with rfl | rfl | rfl | rfl <;> simp only [AWB, AWA2, AWA1] <;> rd_ev
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    refine ⟨by rcases hd with rfl | rfl <;> decide, ?_⟩
    rcases hd with rfl | rfl <;> rd_up

def VB (P : RP) (f g : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat → Nat :=
  upd (VA P f g σ) sExact (if remV P f g σ = 0 then 1 else 0)

end

end VG.Proof.Rsa.Arm.RecoverDet
