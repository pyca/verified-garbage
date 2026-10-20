module
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
public import VerifiedGarbage.Proof.Rsa.Arm.RvMM
public import VerifiedGarbage.Proof.Rsa.Arm.RvKS

import VerifiedGarbage.Proof.Rsa.Arm.RvMmul2
import VerifiedGarbage.Proof.Rsa.Arm.RvSlots
import VerifiedGarbage.Proof.Rsa.Arm.RvOps2
import VerifiedGarbage.Proof.Rsa.Arm.RvOps
import VerifiedGarbage.Proof.Rsa.Arm.RvViews
import VerifiedGarbage.Proof.Rsa.Arm.KeyEq
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # `vg_rsa_recover_primes` on ARMv7: steps that keep Montgomery multiplication ready

The steps of the stages of the candidates: each keeps the stage `KS` as
`RvOps2.lean`'s do, and `MM`, since it writes none of the key arrays 16–20.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

section
variable {P : RP} {σ s : State} {A : Nat → Nat} {live : List Nat} {AW : Nat → Nat} {liveW : List Nat}
  {V : Nat → Nat} {ls : List Nat}

theorem MM.of_keep1 {t : State} (hm : MM P s) (hb : Bs P σ s) {o : Nat} {ds : List Nat}
    (k : Keep P.B P.w [o] ds s.mem t.mem) (ho : o < nArr) (hoM : mBase < o) (hds : ∀ d ∈ ds, SlotOk d)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : MM P t :=
  hm.of_keep hb k (by simp only [List.mem_singleton]; rintro j rfl; exact .inr ⟨hoM, ho⟩)
    (fun d hd => (hds d hd).1) sp rd wr

theorem MM.of_keepW {t : State} (hm : MM P s) (hb : Bs P σ s) {o : Nat} {ds : List Nat}
    (k : Keep P.B P.W [o] ds s.mem t.mem) (ho : o < 22) (hoM : 10 < o) (hds : ∀ d ∈ ds, SlotOk d)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : MM P t :=
  hm.of_keep hb k.ofW (by
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.not_mem_nil, or_false]
      rintro j (rfl | rfl) <;> exact .inr ⟨by simp only [mBase]; omega, by simp only [nArr]; omega⟩)
    (fun d hd => (hds d hd).1) sp rd wr

theorem MM.of_slot {t : State} {v : Nat} (hm : MM P s) (hb : Bs P σ s) {d : Nat}
    (k : Keep P.B v [] [d] s.mem t.mem) (hd : SlotOk d)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : MM P t :=
  hm.of_keep (js := []) (ds := [d]) hb (fun y hy => k y fun r hr => hy r (by simpa [ranges] using hr)) (by simp)
    (by simp only [List.mem_singleton]; rintro e rfl; exact hd.1) sp rd wr

theorem KS.copy_m {o a : Nat} (h : KS P σ A live AW liveW V ls s) (hm : MM P s) (hv : Ws s P.B P.Z P.w nArr)
    (ho : o < nArr) (hoM : mBase < o) (ha : a ∈ live) (hoa : o ≠ a) (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (copy o a) s fun t => KS P σ (upd A o (A a)) (o :: live) AW liveW V ls t ∧ MM P t ∧
      Ws t P.B P.Z P.w nArr ∧ Rest opRegs s t :=
  WP.mono (Keys.copy_ok hv ho (h.live_lt a ha) (by decide) hoa) fun _ ⟨ht, k, e, r, _⟩ =>
    ⟨h.write_w k ho (by simp) (h.r8_of r) r.sp r.rd r.wr (e.trans (h.arrs a ha)) hlW (by simp),
      hm.of_keep1 h.bs k ho hoM (by simp) r.sp r.rd r.wr, ht, r⟩

theorem KS.sel_m {o a b sl : Nat} (h : KS P σ A live AW liveW V ls s) (hm : MM P s)
    (hv : Ws s P.B P.Z P.w nArr) (ho : o < nArr) (hoM : mBase < o) (ha : a ∈ live) (hb : b ∈ live)
    (hoa : o ≠ a) (hob : o ≠ b) (hsl : sl ∈ ls) (bit : V sl ≤ 1) (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (sel o a b sl) s fun t =>
      KS P σ (upd A o (if V sl = 0 then A a else A b)) (o :: live) AW liveW V ls t ∧ MM P t ∧
      Ws t P.B P.Z P.w nArr ∧ Rest opRegs s t := by
  have hs := h.sl sl hsl
  refine WP.mono (Keys.sel_ok hv ho (h.live_lt a ha) (h.live_lt b hb) (by decide) hoa hob
    (h.ls_ok sl hsl).1 (by rw [hs]; exact bit)) fun _ ⟨ht, k, e, r⟩ => ?_
  refine ⟨h.write_w k ho (by simp) (h.r8_of r) r.sp r.rd r.wr ?_ hlW (by simp),
    hm.of_keep1 h.bs k ho hoM (by simp) r.sp r.rd r.wr, ht, r⟩
  rw [e, hs, h.arrs a ha, h.arrs b hb]

theorem KS.sub3_m {o a b : Nat} (h : KS P σ A live AW liveW V ls s) (hm : MM P s) (hv : Ws s P.B P.Z P.w nArr)
    (ho : o < nArr) (hoM : mBase < o) (ha : a ∈ live) (hb : b ∈ live) (hoa : o ≠ a) (hob : o ≠ b)
    (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (sub3 o a b) s fun t => ∃ X, KS P σ (upd A o X) (o :: live) AW liveW V ls t ∧ MM P t ∧
      Ws t P.B P.Z P.w nArr ∧ Rest opRegs s t ∧
      X + A b = A a + 2 ^ (32 * P.w) * (t.gpr .r11).toNat ∧ (t.gpr .r11).toNat ≤ 1 :=
  WP.mono (Keys.sub3_ok hv ho (h.live_lt a ha) (h.live_lt b hb) (by decide) hoa hob)
    fun t ⟨ht, k, e, b1, r⟩ => ⟨num t.mem P.B P.w o,
      h.write_w k ho (by simp) (h.r8_of r) r.sp r.rd r.wr rfl hlW (by simp),
      hm.of_keep1 h.bs k ho hoM (by simp) r.sp r.rd r.wr, ht, r,
      by rw [← h.arrs a ha, ← h.arrs b hb]; exact e, b1⟩

/-- `eqS d a b aW` keeping `MM`. -/
theorem KS.eqS_m {d a b : Nat} (h : KS P σ A live AW liveW V ls s) (hm : MM P s) (hv : Ws s P.B P.Z P.w nArr)
    (ha : a ∈ live) (hb : b ∈ live) (hd : SlotOk d) (hW : aW ∉ live) (hlW : ∀ j ∈ liveW, aW / 2 ≠ j)
    (hls : ∀ e ∈ ls, e + 4 ≤ sT ∨ sT + 4 ≤ e) (hdT : d ≠ sT) :
    WP isa (eqS d a b aW) s fun t =>
      KS P σ A live AW liveW (upd V d (if A a = A b then 1 else 0)) (d :: ls) t ∧ MM P t ∧
      Ws t P.B P.Z P.w nArr ∧ Rest opRegs s t := by
  have hWa : aW ≠ a := fun e => hW (e ▸ ha)
  have hWb : aW ≠ b := fun e => hW (e ▸ hb)
  have e0 := h.eqS_w hv ha hb hd hW hlW hls hdT
  refine WP.mono (WP.and e0 (Keys.eqS_ok hv (t := aW) (by decide) (h.live_lt a ha) (h.live_lt b hb) (by decide)
    hWa hWb hd.1)) fun t ⟨⟨ht, hwt, r⟩, _, k, _, _⟩ => ⟨ht, ?_, hwt, r⟩
  exact hm.of_keep h.bs k (by simp only [List.mem_singleton]; rintro j rfl; exact .inr ⟨by decide, by decide⟩)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro e (rfl | rfl)
        · decide
        · exact hd.1) r.sp r.rd r.wr

theorem KS.copy_Wm {o a : Nat} (h : KS P σ A live AW liveW V ls s) (hm : MM P s) (hv : Ws s P.B P.Z P.W 22)
    (ho : o < 22) (hoM : 10 < o) (ha : a ∈ liveW) (hoa : o ≠ a) (hl : ∀ j ∈ live, j / 2 ≠ o) :
    WP isa (copy o a) s fun t => KS P σ A live (upd AW o (AW a)) (o :: liveW) V ls t ∧ MM P t ∧
      Ws t P.B P.Z P.W 22 ∧ Rest opRegs s t :=
  WP.mono (Keys.copy_ok hv ho (h.liveW_lt a ha) (by decide) hoa) fun _ ⟨ht, k, e, r, _⟩ =>
    ⟨h.write_W k ho (by simp) (h.r8_of r) r.sp r.rd r.wr (e.trans (h.arrsW a ha)) hl (by simp),
      hm.of_keepW h.bs k ho hoM (by simp) r.sp r.rd r.wr, ht, r⟩

theorem KS.half_Wm {j : Nat} (h : KS P σ A live AW liveW V ls s) (hm : MM P s) (hv : Ws s P.B P.Z P.W 22)
    (hj : j ∈ liveW) (hjM : 10 < j) (r11 : (s.gpr .r11).toNat = 0) (hl : ∀ i ∈ live, i / 2 ≠ j) :
    WP isa (half j) s fun t => KS P σ A live (upd AW j (AW j / 2)) (j :: liveW) V ls t ∧ MM P t ∧
      Ws t P.B P.Z P.W 22 ∧ Rest opRegs s t :=
  WP.mono (Keys.half_ok hv (h.liveW_lt j hj) (by decide) (by omega)) fun _ ⟨ht, k, e, r⟩ =>
    ⟨h.write_W k (h.liveW_lt j hj) (by simp) (h.r8_of r) r.sp r.rd r.wr
      (by rw [e, r11, Nat.mul_zero, Nat.add_zero, h.arrsW j hj]) hl (by simp),
      hm.of_keepW h.bs k (h.liveW_lt j hj) hjM (by simp) r.sp r.rd r.wr, ht, r⟩

theorem KS.bitOf_Wm {j sl : Nat} (h : KS P σ A live AW liveW V ls s) (hm : MM P s) (hv : Ws s P.B P.Z P.W 22)
    (hj : j ∈ liveW) (hsl : SlotOk sl) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live AW liveW (upd V sl (AW j % 2)) (sl :: ls) t → MM P t → Ws t P.B P.Z P.W 22 →
      Rest opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (bitOf sl j ++ rest)) s Q :=
  Keys.bitOf_ok hv (h.liveW_lt j hj) (by decide) hsl.1 fun t ht kt e r =>
    k t (h.slot1 kt hsl (h.r8_of r) r.sp r.rd r.wr (by rw [e, h.arrsW j hj]))
      (hm.of_slot h.bs kt hsl r.sp r.rd r.wr) ht r

/-- `str r, [r8, #d]` keeping `MM`. -/
theorem KS.strSlot_m {d : Nat} {r : Reg} {v N : Nat} (h : KS P σ A live AW liveW V ls s) (hm : MM P s)
    (hv : Ws s P.B P.Z v N) (hd : SlotOk d) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live AW liveW (upd V d (s.gpr r).toNat) (d :: ls) t → MM P t → Ws t P.B P.Z v N →
      t.gpr = s.gpr → t.z = s.z → WP isa (.block rest) t Q) :
    WP isa (.block (.str r .r8 d :: rest)) s Q := by
  have hz := hdr_Z h.sizes
  have hin : InRegions s.wr (State.addr (s.gpr .r8 + BitVec.ofNat 32 d)) 4 := by
    rw [slot_addr hv (by have := hd.1; omega)]; exact hv.write (by have := hd.1; omega)
  refine WP.cons (exec_str (by have := hd.1; simp only [hdr] at this; omega) hin) ?_
  have u : Mupd s { s with mem := s.mem.writeW (State.addr (s.gpr .r8 + BitVec.ofNat 32 d)) (s.gpr r) }
      (s.mem.writeW (off (State.addr P.B) d) (s.gpr r)) :=
    ⟨rfl, by rw [slot_addr hv (by have := hd.1; omega)], rfl, rfl, rfl⟩
  have kt : Keep P.B v [] [d] s.mem (s.mem.writeW (off (State.addr P.B) d) (s.gpr r)) :=
    keep_write _ _ (by simp) (by have := hd.1; simp only [hdr] at this; omega)
  rw [← u.mem] at kt
  exact k _ (h.slot1 kt hd (by rw [u.gpr, h.r8]) u.sp u.rd u.wr (by rw [u.mem, slot_write_self]))
    (hm.of_slot h.bs kt hd u.sp u.rd u.wr) (hv.of_mupd u) u.gpr rfl

/-- `cntNext` keeping `MM`. -/
theorem KS.cntNext_m {v N : Nat} (h : KS P σ A live AW liveW V ls s) (hm : MM P s) (hv : Ws s P.B P.Z v N)
    (hc : sCnt ∈ ls) (h1 : 1 ≤ V sCnt) (h2 : V sCnt < 2 ^ 32) :
    WP isa (.block cntNext) s fun t => KS P σ A live AW liveW (upd V sCnt (V sCnt - 1)) (sCnt :: ls) t ∧
      MM P t ∧ Ws t P.B P.Z v N ∧ t.z = decide (V sCnt - 1 = 0) := by
  unfold VG.Impl.Rsa.Arm.Recover.cntNext
  refine h.ldrSlot hv hc (r := .r1) (by decide) fun s1 h1' hv1 u1 => ?_
  have m1 := hm.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem
  refine wp_subs (op2_imm (by decide)) fun s2 u2 z2 => ?_
  obtain ⟨h2', hv2⟩ := h1'.reg hv1 (u2.rest (ws := [.r1]) (by simp)) u2.mem
  have m2 := m1.of_rest (u2.rest (ws := [.r1]) (by simp)) u2.mem
  refine h2'.strSlot_m m2 hv2 (d := sCnt) (r := .r1) (by decide) fun t ht mt hvt gt zt =>
    WP.block_nil ⟨?_, mt, hvt, ?_⟩
  · have e : (s2.gpr .r1).toNat = V sCnt - 1 := by
      rw [u2.gpr, u1.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [e] at ht; exact ht
  · rw [zt, z2, u1.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
    rfl

end

end VG.Proof.Rsa.Arm.Recover
