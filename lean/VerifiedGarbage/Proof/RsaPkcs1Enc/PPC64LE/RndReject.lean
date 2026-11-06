module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.RndScan
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Encode
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on PPC64LE: rejecting

With fewer than `psLen` nonzero octets in the tape: `out` zeroed
(`zero_ok`), the octets drawn wiped (`wipe_ok`), and the tape and the status
for the budget (`budget_ok`, `reject_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Rnd

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Random VG.Proof.RsaPkcs1Sig.PPC64LE
open VG.WriteBytes (writeBytes writeBytes_frame)
open VG.Impl.RsaPkcs1Sig.PPC64LE (fillLoop)

/-! ## Rejecting -/

/-- The registers the rejecting path writes. -/
abbrev rjRegs : List Reg := [.r0, .r3, .r4, .r10, .r11, .r12]

/-- On the rejecting path, from `u`: the frame, `r5` and `r30` kept, memory
changed only in the stack, `out` and the tape, and the saves in their
slots. -/
structure Rj (s u : State) (c : Nat) (x : State) : Prop extends Fy s x where
  keep : Keep rjRegs u x
  fr : Frame [kR s, outR s, tapeR s] s.mem x.mem
  sv : Spill.Saved (fb s) s.gpr saved x.mem
  ls : x.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr

theorem r7_bv (s : State) : s.gpr .r7 = BitVec.ofNat 64 (kOf s) := by simp [kOf]

theorem shift_ne {d : Nat} (hd : d < 2 ^ 63) :
    ((BitVec.ofNat 64 d - BitVec.ofNat 64 129) >>> 63 != 0) = decide (d < 129) := by
  rw [ne_zero_iff, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow]
  by_cases h : d < 129 <;> simp only [h, decide_true, decide_false, decide_eq_true_eq, decide_eq_false_iff_not,
    Decidable.not_not] <;> omega

theorem slK (s : State) : Region.Sub (slR s) (kR s) := frame_sub s (by decide)

/-- `out` zeroed. -/
theorem zero_ok {s : State} (hp : RPre s) {M : Mem} (hM : Mm s M) {i : Nat} {u : State} (hI : At s M i u) :
    WP isa (.seq (.block zeroArgs) fillLoop) u fun x => Rj s u (kept s i).length x ∧
      x.mem = writeBytes u.mem (s.gpr .r3) (List.replicate (kOf s) 0) ∧ x.gpr .r0 = 0 ∧
      x.gpr .r10 = BitVec.ofNat 64 i := by
  have hk := hp.k1
  have hk2 := hp.k2
  have wO := hp.wO
  have hok := hp.hok
  have hMu : Mm s u.mem := by rw [hI.mem]; exact hM.buf _ (by have := hp.ps; have := hI.hc; omega)
  unfold zeroArgs
  refine WP.seq (wp_mov fun z₀ o₀ e₀ => wp_mov fun z₁ o₁ e₁ => wp_mov fun z₂ o₂ e₂ =>
    wp_li (by decide) fun z o₃ e₃ => wp_nil ?_)
  have k : Keep [.r10, .r4, .r11, .r0] u z := (o₀.keep.trans (o₁.keep.trans (o₂.keep.trans o₃.keep))).mono
  refine WP.mono (fill_ok (n := kOf s) (p := s.gpr .r3) (b := 0) (by unfold kOf; omega) (by unfold kOf; omega)
    (by rw [o₃.get .r4, o₂.get .r4, e₁, o₀.get .r31, hI.r31])
    (by rw [o₃.get .r11, e₂, o₁.get .r29, o₀.get .r29, hI.r29, r7_bv])
    (by rw [e₃]; rfl) fun j hj => ?_) fun x ⟨kx, mx⟩ => ?_
  · rw [k.wr, hI.wr, hp.hwr]
    exact ⟨outR s, by simp, Offset.contains_base _ (by unfold kOf at hj; omega) (by unfold kOf at hj; omega)⟩
  · have K : Keep rjRegs u x := (k.trans kx).mono
    have zm : z.mem = u.mem := by rw [o₃.mem, o₂.mem, o₁.mem, o₀.mem]
    have hf : Frame [outR s] u.mem x.mem := by
      rw [mx, zm]
      exact writeBytes_frame _ _ _ (by
        rw [List.length_replicate]; exact Region.contains_self' (by unfold kOf; omega))
    refine ⟨⟨hI.toFx.fy.keep K, K, (hMu.fr.mono (by simp)).trans (hf.mono (by simp)),
      hMu.sv.frame hf fun p hp' r hr => by
        rw [List.mem_singleton.mp hr]; exact (hp.dKo.sub_left (slK s)).sub_left (slot_sub s hp'),
      by rw [hf.readW (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact (hp.dKo.sub_left (slK s)).sub_left (lr_sub s)) (by decide)]
         exact hMu.ls⟩, by rw [mx, zm], by rw [kx.get .r0, e₃]; rfl,
      by rw [kx.get .r10, o₃.get .r10, o₂.get .r10, o₁.get .r10, e₀, hI.r4]⟩

/-- The octets drawn wiped. -/
theorem wipe_ok {s : State} {u v : State} {c : Nat} (hc : c ≤ 1021) (R : Rj s u c v)
    (h5 : v.gpr .r5 = BitVec.ofNat 64 c) (h0 : v.gpr .r0 = 0) :
    WP isa (.seq (.block wipeArgs) (.ite (.nonzero .d .r11) fillLoop (.block []))) v fun x =>
      Rj s u c x ∧ Frame [⟨pb s, c⟩] v.mem x.mem ∧ x.gpr .r10 = v.gpr .r10 := by
  unfold wipeArgs
  refine WP.seq (wp_addSp fun z₁ o₁ e₁ => wp_addi fun z₂ o₂ e₂ => wp_mov fun z o₃ e₃ => wp_nil ?_)
  have k : Keep [.r12, .r4, .r11] v z := (o₁.keep.trans (o₂.keep.trans o₃.keep)).mono
  have zm : z.mem = v.mem := by rw [o₃.mem, o₂.mem, o₁.mem]
  have z11 : z.gpr .r11 = BitVec.ofNat 64 c := by rw [e₃, o₂.get .r5, o₁.get .r5, h5]
  have Rz : Rj s u c z := ⟨R.toFy.keep k, (R.keep.trans k).mono, zm ▸ R.fr, zm ▸ R.sv, zm ▸ R.ls⟩
  have ev : isa.eval (.nonzero .d .r11) z = some (decide (c ≠ 0)) := by
    rw [eval_nonzero, z11, ne_zero_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases h : c = 0
  · refine WP.ite false (by rw [ev, decide_eq_false (by omega)]) (fun h => absurd h (by decide))
      fun _ => wp_nil ⟨Rz, by rw [zm]; exact Frame.refl _ _, k.get .r10⟩
  · refine WP.ite true (by rw [ev, decide_eq_true h]) (fun _ => ?_) (fun h => absurd h (by decide))
    have zw : z.wr = fr s :: s.wr := k.wr.trans R.wr
    refine WP.mono (fill_ok (n := c) (p := pb s) (b := 0) (by omega) (by omega)
      (by rw [o₃.get .r4, e₂, e₁, BitVec.add_zero, R.sp]) z11 (by rw [k.get .r0, h0]; rfl)
      (in_ps s z zw (by omega))) fun x ⟨kx, mx⟩ => ?_
    have hf : Frame [⟨pb s, c⟩] z.mem x.mem := by rw [mx]; exact wipe_frame s _ _
    have slD : (slR s).Disjoint ⟨pb s, c⟩ := slR_buf s (by omega)
    refine ⟨⟨Rz.toFy.keep kx, (Rz.keep.trans kx).mono,
      Rz.fr.trans (hf.sub fun r hr => by
        rw [List.mem_singleton.mp hr]; exact ⟨kR s, by simp, buf_sub s (by omega)⟩),
      Rz.sv.frame hf fun p hp' r hr => by rw [List.mem_singleton.mp hr]; exact slD.sub_left (slot_sub s hp'),
      by rw [hf.readW (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact slD.sub_left (lr_sub s)) (by decide)]; exact Rz.ls⟩, by rw [← zm]; exact hf,
      by rw [kx.get .r10, k.get .r10]⟩

theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q := by
  obtain ⟨t, s', he, hq⟩ := h
  cases he with
  | seq h12 h3 => cases h12 with
    | seq h1 h2 => exact ⟨_, _, .seq h1 (.seq h2 h3), hq⟩

/-- The tape and the status for the budget. -/
theorem budget_ok {s u v : State} (hp : RPre s) {c : Nat} (hc : c < psLen s) (hcl : c ≤ rl s) (R : Rj s u c v)
    (h5 : v.gpr .r5 = BitVec.ofNat 64 c) (h30 : v.gpr .r30 = s.gpr .r5) (h10 : v.gpr .r10 = BitVec.ofNat 64 (rl s)) :
    WP isa (.seq (.block budget) (.ite (.zero .d .r0) (.block exhausted) request)) v fun x =>
      Rj s u c x ∧ Frame [tapeR s] v.mem x.mem ∧
      (Spec.RsaPkcs1Enc.padEntropy (psLen s) ≤ rl s → x.mem.readW (s.gpr .r5) 64 = BitVec.ofNat 64 (rl s) ∧
        x.mem.readW (s.gpr .r5 + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 0 ∧ (x.gpr .r3).setWidth 32 = 3) ∧
      (rl s < Spec.RsaPkcs1Enc.padEntropy (psLen s) → ∃ req, x.mem.readW (s.gpr .r5) 64 = BitVec.ofNat 64 0 ∧
        x.mem.readW (s.gpr .r5 + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 req ∧ rl s < req ∧
        req ≤ Spec.RsaPkcs1Enc.padEntropy (psLen s) ∧ (x.gpr .r3).setWidth 32 = 0) := by
  have hP := hp.ps
  have hrl := hp.rl
  have hcap : Spec.RsaPkcs1Enc.padEntropy (psLen s) = psLen s + 128 := rfl
  unfold budget
  refine WP.seq (wp_addi fun v₃ o₃ e₃ => wp_sub fun w o₄ e₄ => wp_nil ?_)
  have kw : Keep [.r12, .r0] v w := (o₃.keep.trans o₄.keep).mono
  have wm : w.mem = v.mem := by rw [o₄.mem, o₃.mem]
  have w11 : w.gpr .r10 = BitVec.ofNat 64 (rl s) := by rw [kw.get .r10, h10]
  have w12 : w.gpr .r12 = BitVec.ofNat 64 (psLen s + 128) := by
    rw [o₄.get .r12, e₃, R.r28, BitVec.ofNat_add_ofNat]
  have w0 : w.gpr .r0 = BitVec.ofNat 64 (psLen s + 128) - BitVec.ofNat 64 (rl s) := by
    rw [e₄, e₃, o₃.get .r10, R.r28, BitVec.ofNat_add_ofNat, h10]
  have w30 : w.gpr .r30 = s.gpr .r5 := by rw [kw.get .r30, h30]
  have w5 : w.gpr .r5 = BitVec.ofNat 64 c := by rw [kw.get .r5, h5]
  have Rw : Rj s u c w := ⟨R.toFy.keep kw, (R.keep.trans kw).mono, wm ▸ R.fr, wm ▸ R.sv, wm ▸ R.ls⟩
  have ev : isa.eval (.zero .d .r0) w = some (decide (psLen s + 128 = rl s)) := by
    rw [eval_zero, w0, sub_beq (by omega) (by have := rl_lt s; omega)]
  have ww : w.wr = fr s :: s.wr := Rw.wr
  have T0 := in_tape hp w ww (tape_c0 s)
  have T1 := in_tape hp w ww (tape_c8 s)
  -- the tape's writes keep `Rj`
  have key : ∀ r ∈ [Reg.r0, .r3, .r4], r ∉ Reg.r28 :: hiRegs := by decide
  have key' : ∀ r ∈ [Reg.r0, .r3, .r4], r ∈ rjRegs := by decide
  have tapeRj : ∀ {x : State} {rs : List Reg}, Keep rs w x → (∀ r ∈ rs, r ∈ [Reg.r0, .r3, .r4]) →
      Frame [tapeR s] w.mem x.mem → Rj s u c x ∧ Frame [tapeR s] v.mem x.mem := fun kx hrs hf =>
    have slD : (slR s).Disjoint (tapeR s) := hp.dKt.sub_left (slK s)
    ⟨⟨Rw.toFy.keep kx (fun r hr => key r (hrs r hr)), (Rw.keep.trans kx).mono (fun r hr => by
        simp only [List.mem_append] at hr; rcases hr with h | h; exact h; exact key' r (hrs r h)),
      Rw.fr.trans (hf.mono (by simp)),
      Rw.sv.frame hf fun p hp' r hr => by rw [List.mem_singleton.mp hr]; exact slD.sub_left (slot_sub s hp'),
      by rw [hf.readW (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact slD.sub_left (lr_sub s)) (by decide)]; exact Rw.ls⟩,
      wm ▸ hf⟩
  have tf : ∀ (m : Mem) (a b : BitVec 64), Frame [tapeR s] m ((m.writeW (s.gpr .r5) a).writeW
      (s.gpr .r5 + BitVec.ofNat 64 8) b) := fun m a b =>
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (tape_c0 s)).writeW (List.mem_singleton_self _) _
      (tape_c8 s)
  by_cases hex : psLen s + 128 = rl s
  · refine WP.ite true (by rw [ev, decide_eq_true hex]) (fun _ => ?_) (fun h => absurd h (by decide))
    unfold exhausted
    refine wp_std (a := s.gpr .r5) (by rw [w30, BitVec.add_zero]) T0 fun x₁ m₁ => wp_li (by decide)
      fun x₂ o₂' e₂' => wp_std (a := s.gpr .r5 + BitVec.ofNat 64 8) (by rw [o₂'.get .r30, m₁.gpr, w30])
      (by rw [o₂'.wr, m₁.wr]; exact T1) fun x₃ m₃ => wp_li (by decide) fun x o₄' e₄' => wp_nil ?_
    have kx : Keep [.r0, .r3] w x := (m₁.keep.trans (o₂'.keep.trans (m₃.keep.trans o₄'.keep))).mono
    have xm : x.mem = (w.mem.writeW (s.gpr .r5) (BitVec.ofNat 64 (rl s))).writeW (s.gpr .r5 + BitVec.ofNat 64 8)
        (BitVec.ofNat 64 0) := by
      rw [o₄'.mem, m₃.mem, e₂', o₂'.mem, m₁.mem, w11]
    obtain ⟨Rx, fx⟩ := tapeRj kx (by decide) (by rw [xm]; exact tf _ _ _)
    refine ⟨Rx, fx, fun _ => ⟨by rw [xm, rd_t80, Mem.readW_writeW_self64], by rw [xm, Mem.readW_writeW_self64],
      by rw [e₄']; rfl⟩, fun h => absurd h (by rw [hcap]; omega)⟩
  · refine WP.ite false (by rw [ev, decide_eq_false hex]) (fun h => absurd h (by decide)) fun _ => ?_
    have hlt : rl s < psLen s + 128 := by omega
    unfold request reqHead
    refine WP.seq (wp_li (by decide) fun x₁ o₁' e₁' => wp_std (a := s.gpr .r5) (by rw [o₁'.get .r30, w30,
      BitVec.add_zero]) (by rw [o₁'.wr]; exact T0) fun x₂ m₂ => wp_sub fun x₃ o₃' e₃' => wp_subi
      fun x₄ o₄' e₄' => wp_lsr fun y o₅' e₅' => wp_nil ?_)
    have ky : Keep [.r0, .r4] w y := (o₁'.keep.trans (m₂.keep.trans (o₃'.keep.trans (o₄'.keep.trans o₅'.keep)))).mono
    have ym : y.mem = w.mem.writeW (s.gpr .r5) (BitVec.ofNat 64 0) := by
      rw [o₅'.mem, o₄'.mem, o₃'.mem, m₂.mem, e₁', o₁'.mem]
    have hd : rl s - c < 2 ^ 63 := by omega
    have y4 : y.gpr .r4 = (BitVec.ofNat 64 (rl s - c) - BitVec.ofNat 64 129) >>> 63 := by
      rw [e₅', e₄', e₃', m₂.gpr, o₁'.get .r10, o₁'.get .r5, w11, w5, sub_ofNat hcl (rl_lt s)]
    have ev' : isa.eval (.nonzero .d .r4) y = some (decide (rl s - c < 129)) := by
      rw [eval_nonzero, y4, shift_ne hd]
    have tail : ∀ (z : State) (req : Nat), Keep [.r0] y z → z.mem = y.mem → z.gpr .r0 = BitVec.ofNat 64 req →
        rl s < req → req ≤ psLen s + 128 →
        WP isa (.block [.store .d .r0 .r30 8, .li .r3 0]) z fun x =>
          Rj s u c x ∧ Frame [tapeR s] v.mem x.mem ∧
          (Spec.RsaPkcs1Enc.padEntropy (psLen s) ≤ rl s → x.mem.readW (s.gpr .r5) 64 = BitVec.ofNat 64 (rl s) ∧
            x.mem.readW (s.gpr .r5 + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 0 ∧ (x.gpr .r3).setWidth 32 = 3) ∧
          (rl s < Spec.RsaPkcs1Enc.padEntropy (psLen s) → ∃ req, x.mem.readW (s.gpr .r5) 64 = BitVec.ofNat 64 0 ∧
            x.mem.readW (s.gpr .r5 + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 req ∧ rl s < req ∧
            req ≤ Spec.RsaPkcs1Enc.padEntropy (psLen s) ∧ (x.gpr .r3).setWidth 32 = 0) := by
      intro z req kz zm z0 h1 h2
      refine wp_std (a := s.gpr .r5 + BitVec.ofNat 64 8) (by rw [kz.get .r30, ky.get .r30, w30])
        (by rw [kz.wr, ky.wr]; exact T1) fun x₁ m₁ => wp_li (by decide) fun x o₂ e₂ => wp_nil ?_
      have kx : Keep [.r0, .r3, .r4] w x := ((ky.trans kz).trans (m₁.keep.trans o₂.keep)).mono
      have xm : x.mem = (w.mem.writeW (s.gpr .r5) (BitVec.ofNat 64 0)).writeW (s.gpr .r5 + BitVec.ofNat 64 8)
          (BitVec.ofNat 64 req) := by rw [o₂.mem, m₁.mem, z0, zm, ym]
      obtain ⟨Rx, fx⟩ := tapeRj kx (by decide) (by rw [xm]; exact tf _ _ _)
      exact ⟨Rx, fx, fun h => absurd h (by rw [hcap]; omega), fun _ => ⟨req,
        by rw [xm, rd_t80, Mem.readW_writeW_self64], by rw [xm, Mem.readW_writeW_self64], h1, h2,
        by rw [e₂]; rfl⟩⟩
    by_cases hs : rl s - c < 129
    · refine WP.seq (WP.ite true (by rw [ev', decide_eq_true hs]) (fun _ => wp_add fun z₁ o₁'' e₁'' =>
        wp_sub fun z o₂'' e₂'' => wp_nil ?_) (fun h => absurd h (by decide)))
      refine tail z (psLen s + rl s - c) (o₁''.keep.trans o₂''.keep).mono (by rw [o₂''.mem, o₁''.mem]) ?_
        (by omega) (by omega)
      rw [e₂'', o₁''.get .r5, e₁'', ky.get .r28, ky.get .r10, ky.get .r5, Rw.r28, w11, w5,
        BitVec.ofNat_add_ofNat, sub_ofNat (by omega) (by omega)]
    · refine WP.seq (WP.ite false (by rw [ev', decide_eq_false hs]) (fun h => absurd h (by decide))
        fun _ => wp_mov fun z o₁'' e₁'' => wp_nil ?_)
      exact tail z (psLen s + 128) o₁''.keep (by rw [o₁''.mem]) (by rw [e₁'', ky.get .r12, w12]) hlt (by omega)

theorem reject_ok {s : State} (hp : RPre s) {M : Mem} (hM : Mm s M) {u : State} (hI : At s M (rl s) u)
    (hc : (kept s (rl s)).length < psLen s) : WP isa reject u (Fin s) := by
  have hP := hp.ps
  have hk2 := hp.k2
  have hcl := hI.hc
  have hcr : (kept s (rl s)).length ≤ rl s := by
    have := VG.Proof.RsaPkcs1Enc.nz_length_le ((randB s).take (rl s))
    simp only [List.length_take, randB_length] at this; simp only [kept]; omega
  unfold reject
  refine seq_assoc (WP.seq (WP.mono (zero_ok hp hM hI) fun v ⟨R, hm, h0, h10⟩ => ?_))
  have h5 : v.gpr .r5 = BitVec.ofNat 64 (kept s (rl s)).length := by rw [R.keep.get .r5, hI.r5]
  refine seq_assoc (WP.seq (WP.mono (wipe_ok (by omega) R h5 h0) fun w ⟨R', hf', h10'⟩ => ?_))
  refine WP.mono (budget_ok hp hc hcr R' (by rw [R'.keep.get .r5, hI.r5]) (by rw [R'.keep.get .r30, hI.r30])
    (by rw [h10', h10]))
    fun x ⟨Rx, fx, hex, hen⟩ => ⟨⟨Rx.sp, Rx.wr, Rx.hi, Rx.sv, Rx.ls⟩, Rx.rd, ?_⟩
  -- `out`
  have bs := buf_sub s (n := (kept s (rl s)).length) (by omega)
  have outZ : Spec.Rsa.bytesAt x.mem (s.gpr .r3) (kOf s) = List.replicate (kOf s) 0 := by
    have e : (⟨s.gpr .r3, kOf s⟩ : Region) = outR s := by simp only [outR, kOf, hp.hok]
    rw [bytes_frame fx (fun r hr => by rw [List.mem_singleton.mp hr, e]; exact hp.dOt) (by unfold kOf; omega),
      bytes_frame hf' (fun r hr => by rw [List.mem_singleton.mp hr, e]; exact hp.dKo.symm.sub_right bs)
        (by unfold kOf; omega), hm]
    have := bytesAt_writeBytes u.mem (s.gpr .r3) (List.replicate (kOf s) 0) (by simp; unfold kOf; omega)
    rwa [List.length_replicate] at this
  have hnz : (VG.Proof.RsaPkcs1Enc.nz (randB s)).length < psLen s := by rw [← kept_all]; exact hc
  show (∃ req, _ ∧ _ ∧ _) ∧ _
  unfold Spec.Entropy.Result.Requests
  by_cases hge : Spec.RsaPkcs1Enc.padEntropy (psLen s) ≤ rl s
  · obtain ⟨ho, hu⟩ := VG.Proof.RsaPkcs1Enc.padSearch_exhausted hnz (by rw [randB_length]; exact hge)
    obtain ⟨h0, h1, hr⟩ := hex hge
    rw [ho, hu, randB_length]
    exact ⟨⟨0, h0, h1, rfl⟩, hr, outZ⟩
  · obtain ⟨ho, hu⟩ := VG.Proof.RsaPkcs1Enc.padSearch_entropy hnz (by rw [randB_length]; omega)
    obtain ⟨req, h0, h1, hr1, hr2, hr⟩ := hen (by omega)
    rw [ho, hu]
    exact ⟨⟨req, h0, h1, by rw [randB_length]; exact ⟨hr1, hr2⟩⟩, hr, outZ⟩

end VG.Proof.RsaPkcs1Enc.PPC64LE.Rnd
