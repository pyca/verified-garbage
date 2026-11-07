module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.RndScan
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.RndCalls
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.RndTaint
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.EncVerified
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on RISC-V: correctness and constant time

The contract's postcondition by name (`post`): the scan's two outcomes lead
to the call (`accept_ok`) or to the request for more entropy (`reject_ok`),
and together they give `post` (`code_ok`).

The public data by name (`PubR`). Two runs with the same public data
(`Two E`) scan the same number of octets, and each of them is zero in one
run exactly when it is in the other, so they keep the same number of
octets at each step (`keptLen_eq`) and take the same branches (`scan_ct`);
the call of `vg_rsa_pkcs1_encrypt_precomputed` gets the same public data
in both (`call_ct`, by its contract); the rest is checked by the taint
analysis, from registers that correctness pins (`code_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Rnd

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64 VG.Proof.RsaPkcs1Sig.RISCV64 VG.WriteBytes
open VG.Impl.RsaPkcs1Enc.RISCV64.Random
open VG.Proof.RsaPkcs1Enc (nz)

/-! ## Correctness -/

theorem ready_of {s t₀ u : State} (hp : RPre s) (hb : Before s t₀) {i : Nat} (hI : At s t₀ i u)
    (hf : (kept s i).length = psLen s) : Ready s u i (kept s i) := by
  have hF : InF s u := hb.toInF.step hI.keep (R := [⟨psA s, (kept s i).length⟩])
    (by rw [hI.mem]; exact Proof.RsaPkcs1Sig.frame_writeBytes _ _ _)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact wok_ps hp hf)
  have hl := psLen_le hp
  refine { hF with
    g := fun r hr => ?_
    s1 := by rw [hI.keep.get .s1, hb.s1]
    t1 := by rw [hI.keep.get .t1, hb.t1]
    t2 := hI.t2
    buf := by rw [hI.mem, ← hf]; exact Proof.RsaPkcs1Sig.bytesAt_writeBytes _ _ _ (by omega)
    len := hf }
  have : r ∉ [Reg.t6, .t2, .t0, .t5] := by
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [hI.keep.gpr r this, hb.g r hr]


/-- The contract's postcondition, by name. -/
def post (s u : State) : Prop :=
  let res := Spec.RsaPkcs1Enc.padSearch (psLen s) (randB s)
  (∃ req, u.mem.readW (s.gpr .a2) 64 = BitVec.ofNat 64 res.used ∧
    u.mem.readW (s.gpr .a2 + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 req ∧
    res.Requests (Spec.RsaPkcs1Enc.padEntropy (psLen s)) req) ∧
  match res.outcome with
  | .accepted ps => PreOk s →
      Spec.RsaPkcs1Enc.writtenRandom u.mem (s.gpr .a0) (s.gpr .a4).toNat ((u.gpr .a0).setWidth 32)
        (Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) ps)
  | .entropy .. => (u.gpr .a0).setWidth 32 = 0 ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .a0) (s.gpr .a4).toNat = List.replicate (s.gpr .a4).toNat 0
  | .exhausted => (u.gpr .a0).setWidth 32 = 3 ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .a0) (s.gpr .a4).toNat = List.replicate (s.gpr .a4).toNat 0

theorem accept_ok {s t₀ u : State} (hp : RPre s) (hb : Before s t₀) {i : Nat}
    (hI : At s t₀ i u) (hf : (kept s i).length = psLen s)
    (hpre : Spec.RsaPkcs1Enc.nonzeroPrefix (psLen s) (randB s) = some (kept s i, i)) :
    WP isa accept u fun x => abiPreserved s (freed frameBytes x) ∧ post s x := by
  refine WP.seq (WP.mono (callRegs_ok hp (ready_of hp hb hI hf)) fun z hz => ?_)
  refine WP.seq (WP.mono (call_ok hp hz) fun u' hac => ?_)
  refine WP.mono (accTail_ok hp hac) fun x ⟨habi, ht0, ht1, hres⟩ => ⟨habi, ?_⟩
  obtain ⟨ho, hu⟩ := VG.Proof.RsaPkcs1Enc.padSearch_accepted hpre
  show (∃ req, _ ∧ _ ∧ _) ∧ _
  rw [ho, hu]
  refine ⟨⟨0, ht0, ht1, ?_⟩, hres⟩
  unfold Spec.Entropy.Result.Requests
  rw [ho]

theorem kept_all (s : State) : kept s (stackArg s 2).toNat = VG.Proof.RsaPkcs1Enc.nz (randB s) := by
  simp only [kept]; rw [← randB_length, List.take_length]

theorem reject_ok {s t₀ u : State} (hp : RPre s) (hb : Before s t₀) (hI : At s t₀ (stackArg s 2).toNat u)
    (hc : (kept s (stackArg s 2).toNat).length < psLen s) :
    WP isa reject u fun x => abiPreserved s (freed frameBytes x) ∧ post s x := by
  have hP := psLen_le hp
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hrl := hp.rl
  have hcl : (kept s (stackArg s 2).toNat).length ≤ (stackArg s 2).toNat := by
    have := VG.Proof.RsaPkcs1Enc.nz_length_le ((randB s).take (stackArg s 2).toNat)
    simp only [List.length_take, randB_length, Nat.min_self] at this; exact this
  generalize hcd : (kept s (stackArg s 2).toNat).length = c at hc hcl
  have hF : InF s u := hb.toInF.step hI.keep (R := [⟨psA s, (kept s (stackArg s 2).toNat).length⟩])
    (by rw [hI.mem]; exact Proof.RsaPkcs1Sig.frame_writeBytes _ _ _)
    (fun r hr => by
      rw [List.mem_singleton.mp hr, hcd]
      exact wok_frame s (by decide) (by unfold oEM1 frameBytes; omega))
  have g : ∀ r ∈ argRegs, u.gpr r = s.gpr r := fun r hr => by
    have : r ∉ [Reg.t6, .t2, .t0, .t5] := by
      simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hI.keep.gpr r this, hb.g r hr]
  have t4u : u.gpr .t4 = stackArg s 2 := by rw [hI.keep.get .t4, hb.t4]
  have s1u : u.gpr .s1 = BitVec.ofNat 64 (psLen s) := by rw [hI.keep.get .s1, hb.s1]
  have t5u : u.gpr .t5 = BitVec.ofNat 64 c := by rw [hI.t5, hcd]
  have hoS : Region.Sub ⟨s.gpr .a0, (s.gpr .a4).toNat⟩ (oR s) := by rw [oR_eq hp]; exact fun _ h => h
  have hoW : Wok s ⟨s.gpr .a0, (s.gpr .a4).toNat⟩ :=
    ⟨⟨oR s, by simp, hoS⟩, o'_dis hp ((k_dis hp.ko).sub_left (svR_sub s)).symm |>.symm⟩
  unfold reject zeroOut
  refine WP.seq (WP.seq (wp_mov fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ => wp_mov fun u₃ o₃ e₃ =>
    wp_li (imm := 0) (by decide) fun u₄ o₄ e₄ => wp_nil ?_))
  have O₄ : Only [.t3, .a1, .t5, .t0] u u₄ := o₁.trans (o₂.trans (o₃.trans o₄))
  have hF₄ : InF s u₄ := hF.only O₄
  refine WP.mono (fill_ok (p := s.gpr .a0) (n := (s.gpr .a4).toNat) (b := 0) (by omega) (by omega)
    (by rw [o₄.get .a1, o₃.get .a1, e₂, o₁.get .a0, g .a0 (by decide)])
    (by rw [o₄.get .t5, e₃, o₂.get .a4, o₁.get .a4, g .a4 (by decide), ofNat_toNat])
    (by rw [e₄]; rfl)
    (fun j hj => by
      rw [hF₄.wr, hp.hwr]
      exact ⟨oR s, by simp, Offset.contains_base _ (by rw [hp.ok]; omega) (by omega)⟩)) fun w ⟨kw, mw⟩ => ?_
  have hl : (List.replicate (s.gpr .a4).toNat (0 : Byte)).length = (s.gpr .a4).toNat := List.length_replicate ..
  have hFw : InF s w := hF₄.step kw (R := [⟨s.gpr .a0, (List.replicate (s.gpr .a4).toNat (0 : Byte)).length⟩])
    (by rw [mw]; exact Proof.RsaPkcs1Sig.frame_writeBytes _ _ _)
    (fun r hr => by rw [List.mem_singleton.mp hr, hl]; exact hoW)
  have outw : Spec.Rsa.bytesAt w.mem (s.gpr .a0) (s.gpr .a4).toNat = List.replicate (s.gpr .a4).toNat 0 := by
    have := Proof.RsaPkcs1Sig.bytesAt_writeBytes u₄.mem (s.gpr .a0) (List.replicate (s.gpr .a4).toNat 0)
      (by rw [hl]; omega)
    rw [hl] at this; rw [mw]; exact this
  have Kw : Kept ([Reg.t3, .a1, .t5, .t0] ++ [.a1, .t5]) u w := O₄.keep.trans kw
  have t3w : w.gpr .t3 = BitVec.ofNat 64 c := by rw [kw.get .t3, o₄.get .t3, o₃.get .t3, o₂.get .t3, e₁, t5u]
  -- the rest, from the state after the octets drawn are wiped
  have rest : ∀ y : State, InF s y → y.gpr .a2 = s.gpr .a2 → y.gpr .t4 = stackArg s 2 →
      y.gpr .s1 = BitVec.ofNat 64 (psLen s) → y.gpr .t3 = BitVec.ofNat 64 c →
      Spec.Rsa.bytesAt y.mem (s.gpr .a0) (s.gpr .a4).toNat = List.replicate (s.gpr .a4).toNat 0 →
      WP isa (.seq (.block [.addi .t0 .s1 128]) (.seq (.ite (.ltu .t4 .t0) request (.block exhausted))
        (.block restore))) y fun x => abiPreserved s (freed frameBytes x) ∧ post s x := by
    intro y hFy a2y t4y s1y t3y outy
    refine WP.mono (budget_ok hp hFy a2y t4y s1y t3y hc hcl) fun x ⟨habi, frx, hex, hen⟩ => ⟨habi, ?_⟩
    have outZ : Spec.Rsa.bytesAt x.mem (s.gpr .a0) (s.gpr .a4).toNat = List.replicate (s.gpr .a4).toNat 0 := by
      rw [Proof.RsaPkcs1Sig.bytes_apart (R := oR' s) frx (o'_dis hp hp.ot)
        (by have := hp.wo; rw [hp.ok] at this; show (s.gpr .a4).toNat ≤ 2 ^ 64; omega)]
      exact outy
    have hnz : (VG.Proof.RsaPkcs1Enc.nz (randB s)).length < psLen s := by rw [← kept_all, hcd]; exact hc
    show (∃ req, _ ∧ _ ∧ _) ∧ _
    unfold Spec.Entropy.Result.Requests
    by_cases hge : Spec.RsaPkcs1Enc.padEntropy (psLen s) ≤ (stackArg s 2).toNat
    · obtain ⟨ho, hu⟩ := VG.Proof.RsaPkcs1Enc.padSearch_exhausted hnz (by rw [randB_length]; exact hge)
      obtain ⟨h0, h1, hr⟩ := hex hge
      rw [ho, hu, randB_length]
      exact ⟨⟨0, by rw [h0, ofNat_toNat], h1, rfl⟩, hr, outZ⟩
    · obtain ⟨ho, hu⟩ := VG.Proof.RsaPkcs1Enc.padSearch_entropy hnz (by rw [randB_length]; omega)
      obtain ⟨h0, h1, hr⟩ := hen (by omega)
      rw [ho, hu]
      refine ⟨⟨_, h0, h1, ?_⟩, hr, outZ⟩
      rw [randB_length]
      unfold Spec.RsaPkcs1Enc.padEntropy at *
      constructor
      · simp only [Nat.lt_min]; constructor <;> omega
      · exact Nat.min_le_left _ _
  have a2w : w.gpr .a2 = s.gpr .a2 := by rw [Kw.get .a2, g .a2 (by decide)]
  have t4w : w.gpr .t4 = stackArg s 2 := by rw [Kw.get .t4, t4u]
  have s1w : w.gpr .s1 = BitVec.ofNat 64 (psLen s) := by rw [Kw.get .s1, s1u]
  unfold wipeDrawn
  have hev : isa.eval (.nonzero .t3) w = some (decide (c ≠ 0)) := by
    have := sub_ne_zero (a := c) (b := 0) (by omega) (by decide)
    rw [BitVec.sub_zero] at this
    rw [eval_nonzero, t3w, this]
  by_cases hc0 : c = 0
  · refine WP.seq (WP.ite false (by rw [hev, decide_eq_false (fun h => h hc0)]) (fun h => absurd h (by decide))
      fun _ => wp_nil ?_)
    exact rest w hFw a2w t4w s1w t3w outw
  · refine WP.seq (WP.ite true (by rw [hev, decide_eq_true hc0]) (fun _ => ?_) (fun h => absurd h (by decide)))
    refine WP.seq (wp_addSp fun v₁ p₁ f₁ => wp_addi (imm := oPS) fun v₂ p₂ f₂ => wp_mov fun v₃ p₃ f₃ =>
      wp_li (imm := 0) (by decide) fun v₄ p₄ f₄ => wp_nil ?_)
    have P₄ : Only [.t0, .a1, .t5, .t0] w v₄ := p₁.trans (p₂.trans (p₃.trans p₄))
    have hF₄' : InF s v₄ := hFw.only P₄
    refine WP.mono (fill_ok (p := psA s) (n := c) (b := 0) (by omega) (by omega)
      (by rw [p₄.get .a1, p₃.get .a1, f₂, f₁, hFw.sp, BitVec.add_zero]; rfl)
      (by rw [p₄.get .t5, f₃, p₂.get .t3, p₁.get .t3, t3w]) (by rw [f₄]; rfl)
      (fun j hj => by rw [hF₄'.wr]; exact in_ps hp _ (by omega) hj)) fun y ⟨ky, my⟩ => ?_
    have hly : (List.replicate c (0 : Byte)).length = c := List.length_replicate ..
    have hFy : InF s y := hF₄'.step ky (R := [⟨psA s, (List.replicate c (0 : Byte)).length⟩])
      (by rw [my]; exact Proof.RsaPkcs1Sig.frame_writeBytes _ _ _)
      (fun r hr => by
        rw [List.mem_singleton.mp hr, hly]
        exact wok_frame s (by decide) (by unfold oEM1 frameBytes; omega))
    have Ky : Kept ([Reg.t0, .a1, .t5, .t0] ++ [.a1, .t5]) w y := P₄.keep.trans ky
    refine rest y hFy (by rw [Ky.get .a2, a2w]) (by rw [Ky.get .t4, t4w]) (by rw [Ky.get .s1, s1w])
      (by rw [Ky.get .t3, t3w]) ?_
    rw [my, P₄.mem, bytes_wb (R := oR' s) (by
        rw [hly]; exact (o'_dis hp (ps_dis hp hp.ko).symm).sub_right (Region.sub_prefix (by omega)))
      (by have := hp.wo; rw [hp.ok] at this; show (s.gpr .a4).toNat ≤ 2 ^ 64; omega)]
    exact outw

theorem body_ok {s : State} (hp : RPre s) :
    WP isa body (allocd frameBytes s) fun x => abiPreserved s (freed frameBytes x) ∧ post s x := by
  refine WP.seq (WP.mono (setup_ok hp rfl rfl rfl (Frame.refl _ _) (fun _ => rfl)) fun t₁ ⟨hb, h2, h5⟩ => ?_)
  refine WP.seq (WP.mono (scan_ok hp hb h2 h5) fun u ⟨i, hI, hres⟩ => ?_)
  have hP := psLen_le hp
  have hev : isa.eval (.eq .t5 .s1) u = some (decide ((kept s i).length = psLen s)) := by
    show some (u.gpr .t5 == u.gpr .s1) = _
    rw [hI.t5, hI.keep.get .s1, hb.s1, beq_ofNat (by have := hI.hc; omega) (by omega)]
  rcases hres with ⟨hf, hpre⟩ | ⟨hi, hc⟩
  · exact WP.ite true (by rw [hev, decide_eq_true hf]) (fun _ => accept_ok hp hb hI hf hpre)
      (fun h => absurd h (by decide))
  · subst hi
    exact WP.ite false (by rw [hev, decide_eq_false (by omega)]) (fun h => absurd h (by decide))
      fun _ => reject_ok hp hb hI hc

theorem post_freed {s x : State} (n : Nat) (h : post s x) : post s (freed n x) := by
  have hm : (freed n x).mem = x.mem := rfl
  have hg : (freed n x).gpr = x.gpr := rfl
  unfold post; rw [hm, hg]; exact h

theorem code_ok {s : State} (hp : RPre s) : WP isa code s fun s' => abiPreserved s s' ∧ post s s' := by
  unfold code
  exact WP.allocLe (by decide) (sp1' hp) (WP.mono (body_ok hp) fun x h => ⟨h.1, post_freed _ h.2⟩)


/-! ## The public data -/

/-- The trace of drawing `PS`. -/
abbrev trace (s : State) : List Nat := (Spec.RsaPkcs1Enc.padSearch (psLen s) (randB s)).trace

/-- The public data of an entry state `s` is the anchor `a`'s. -/
structure PubR (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ argRegs, s.gpr r = a.gpr r
  args : ∀ j < 7, stackArg s j = stackArg a j
  n : nB s = nB a
  e : eB s = eB a
  w : preW s = preW a
  tr : trace s = trace a

theorem pubR_of {s₁ s₂ : State} (h : (Spec.RsaPkcs1Enc.encryptRandomContract abi rndStack).pub s₁ s₂) :
    PubR s₁ s₂ := by
  sig_pub [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig, abi, argRegs,
    stackArgs_seven, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, x0, x1, x2, x3, x4, x5, x6, x7, a0, a1, a2, a3, a4, a5, a6⟩ := h
  have hl' : (List.map BitVec.toNat (nB s₁ ++ eB s₁) ++ List.map BitVec.toNat (preW s₁)) ++ trace s₁ =
      (List.map BitVec.toNat (nB s₂ ++ eB s₂) ++ List.map BitVec.toNat (preW s₂)) ++ trace s₂ := hl
  have hl1 : (List.map BitVec.toNat (nB s₁ ++ eB s₁)).length = (List.map BitVec.toNat (nB s₂ ++ eB s₂)).length := by
    simp [nB, eB, Spec.Rsa.bytesAt, x4, x6]
  have hl2 : (List.map BitVec.toNat (preW s₁)).length = (List.map BitVec.toNat (preW s₂)).length := by
    simp [preW, Spec.Rsa.wordsAt, a6]
  obtain ⟨h12, h3⟩ := List.append_inj hl' (by simp only [List.length_append, hl1, hl2])
  obtain ⟨h1, h2⟩ := List.append_inj h12 hl1
  have inj : ∀ {w : Nat} {l₁ l₂ : List (BitVec w)}, l₁.map BitVec.toNat = l₂.map BitVec.toNat → l₁ = l₂ :=
    fun h => (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
  obtain ⟨hn, he⟩ := List.append_inj (inj h1) (by simp [nB, Spec.Rsa.bytesAt, x4])
  refine ⟨hsp.symm, fun r hr => ?_, fun j hj => ?_, hn.symm, he.symm, (inj h2).symm, h3.symm⟩
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [x0.symm, x1.symm, x2.symm, x3.symm, x4.symm, x5.symm, x6.symm, x7.symm]
  · match j, hj with
    | 0, _ => exact a0.symm | 1, _ => exact a1.symm | 2, _ => exact a2.symm | 3, _ => exact a3.symm
    | 4, _ => exact a4.symm | 5, _ => exact a5.symm | 6, _ => exact a6.symm

/-- An entry state with the anchor's public data. -/
def E (a s : State) : Prop := RPre s ∧ PubR a s

/-! ## What two runs share -/

section
variable {a s₁ s₂ : State} (h₁ : E a s₁) (h₂ : E a s₂)
include h₁ h₂

theorem sp_eq : s₁.sp = s₂.sp := h₁.2.sp.trans h₂.2.sp.symm

theorem fb_eq : fb s₁ = fb s₂ := by simp only [fb, sp_eq h₁ h₂]

theorem g_eq {r : Reg} (hr : r ∈ argRegs := by decide) : s₁.gpr r = s₂.gpr r :=
  (h₁.2.g r hr).trans (h₂.2.g r hr).symm

theorem arg_eq {j : Nat} (hj : j < 7 := by decide) : stackArg s₁ j = stackArg s₂ j :=
  (h₁.2.args j hj).trans (h₂.2.args j hj).symm

theorem psLen_same : psLen s₁ = psLen s₂ := by unfold psLen; rw [g_eq h₁ h₂ (r := .a4), arg_eq h₁ h₂ (j := 0)]

theorem psA_eq : psA s₁ = psA s₂ := by rw [psA, psA, fb_eq h₁ h₂]

theorem trace_eq' : (Spec.RsaPkcs1Enc.padSearch (psLen s₁) (randB s₁)).trace =
    (Spec.RsaPkcs1Enc.padSearch (psLen s₁) (randB s₂)).trace := by
  have := h₁.2.tr.trans h₂.2.tr.symm
  unfold trace at this; rw [← psLen_same h₁ h₂] at this; exact this

theorem scanLen_eq' : VG.Proof.RsaPkcs1Enc.scanLen (psLen s₁) (randB s₁) =
    VG.Proof.RsaPkcs1Enc.scanLen (psLen s₂) (randB s₂) := by
  rw [← psLen_same h₁ h₂]; exact VG.Proof.RsaPkcs1Enc.scanLen_eq (trace_eq' h₁ h₂)

end

theorem nz_len_of_mask : ∀ {xs ys : List Byte}, Spec.RsaPkcs1Enc.zeroMask xs = Spec.RsaPkcs1Enc.zeroMask ys →
    (nz xs).length = (nz ys).length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [Spec.RsaPkcs1Enc.zeroMask] at h
  | _ :: _, [], h => by simp [Spec.RsaPkcs1Enc.zeroMask] at h
  | x :: xs, y :: ys, h => by
    simp only [Spec.RsaPkcs1Enc.zeroMask, List.map_cons, List.cons.injEq] at h
    obtain ⟨hh, ht⟩ := h
    have ih := nz_len_of_mask (xs := xs) (ys := ys) ht
    by_cases hx : x = 0 <;> by_cases hy : y = 0
    · subst hx hy; rw [VG.Proof.RsaPkcs1Enc.nz_cons_zero, VG.Proof.RsaPkcs1Enc.nz_cons_zero, ih]
    · rw [ite_eq_left hx, ite_eq_right hy] at hh; exact absurd hh (by decide)
    · rw [ite_eq_right hx, ite_eq_left hy] at hh; exact absurd hh (by decide)
    · rw [VG.Proof.RsaPkcs1Enc.nz_cons_ne hx, VG.Proof.RsaPkcs1Enc.nz_cons_ne hy, List.length_cons,
        List.length_cons, ih]

/-- Two runs keep the same number of octets up to the end of their scans. -/
theorem keptLen_eq {a s₁ s₂ : State} (h₁ : E a s₁) (h₂ : E a s₂) {i : Nat}
    (hi : i ≤ VG.Proof.RsaPkcs1Enc.scanLen (psLen s₁) (randB s₁)) : (kept s₁ i).length = (kept s₂ i).length := by
  have ht := trace_eq' h₁ h₂
  have hL := VG.Proof.RsaPkcs1Enc.scanLen_eq ht
  rw [VG.Proof.RsaPkcs1Enc.trace_eq, VG.Proof.RsaPkcs1Enc.trace_eq, ← hL] at ht
  have hm : Spec.RsaPkcs1Enc.zeroMask ((randB s₁).take i) = Spec.RsaPkcs1Enc.zeroMask ((randB s₂).take i) := by
    have := congrArg (List.take i) ht
    simp only [Spec.RsaPkcs1Enc.zeroMask, ← List.map_take, List.take_take, Nat.min_eq_left hi] at this
    exact this
  exact nz_len_of_mask hm

theorem zero_eq {a s₁ s₂ : State} (h₁ : E a s₁) (h₂ : E a s₂) {i : Nat}
    (hi : i < VG.Proof.RsaPkcs1Enc.scanLen (psLen s₁) (randB s₁)) :
    ((randB s₁).getD i 0 = 0 ↔ (randB s₂).getD i 0 = 0) :=
  VG.Proof.RsaPkcs1Enc.zero_iff (trace_eq' h₁ h₂) hi

theorem lt_scan {s : State} {i : Nat} (hi : i < (stackArg s 2).toNat) (hc : (kept s i).length < psLen s) :
    i < VG.Proof.RsaPkcs1Enc.scanLen (psLen s) (randB s) :=
  VG.Proof.RsaPkcs1Enc.lt_scanLen hc (by rw [randB_length]; exact hi)

/-! ## The scan -/

/-- In the loop, at octet `i`, from the anchor `a`: `P` of the state, with
`n` octets left. -/
def LoopAt (P : State → State → Nat → State → Prop) (n : Nat) (a u : State) : Prop :=
  ∃ s t₀ i, E a s ∧ Before s t₀ ∧ n = (stackArg a 2).toNat - i ∧ i < (stackArg s 2).toNat ∧
    (kept s i).length < psLen s ∧ P s t₀ i u

theorem loop_i {a s₁ s₂ : State} (h₁ : E a s₁) (h₂ : E a s₂) {n i₁ i₂ : Nat} (hn₁ : n = (stackArg a 2).toNat - i₁)
    (hn₂ : n = (stackArg a 2).toNat - i₂) (hi₁ : i₁ < (stackArg s₁ 2).toNat) (hi₂ : i₂ < (stackArg s₂ 2).toNat) :
    i₁ = i₂ := by
  rw [h₁.2.args 2 (by decide)] at hi₁; rw [h₂.2.args 2 (by decide)] at hi₂; omega

/-- After the step. -/
def More (s t₀ : State) (i : Nat) (u : State) : Prop :=
  At s t₀ (i + 1) u ∧
    (u.gpr .t0 != 0) = !decide ((kept s (i + 1)).length = psLen s ∨ i + 1 = (stackArg s 2).toNat)

theorem step_ct (n : Nat) : RelCT isa (Two (LoopAt At n)) step (Two (LoopAt More n)) := by
  rw [step_eq]
  refine RelCT.seq (two_post (Ψ := LoopAt Loaded n) (load_taint fun a u₁ u₂ h₁ h₂ => ?_)
    fun a u ⟨s, t₀, i, hE, hb, hn, hi, hc, hI⟩ => WP.mono (load_ok hE.1 hb hI hi)
      fun v hv => ⟨s, t₀, i, hE, hb, hn, hi, hc, hv⟩) ?_
  · obtain ⟨s₁, t₁, i₁, e₁, b₁, n₁, j₁, _, I₁⟩ := h₁
    obtain ⟨s₂, t₂, i₂, e₂, b₂, n₂, j₂, _, I₂⟩ := h₂
    have := loop_i e₁ e₂ n₁ n₂ j₁ j₂; subst this
    refine ⟨by rw [I₁.keep.sp, b₁.sp, I₂.keep.sp, b₂.sp, fb_eq e₁ e₂], fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [I₁.keep.get .t3, b₁.t3, I₂.keep.get .t3, b₂.t3, arg_eq e₁ e₂]
    · rw [I₁.t2, I₂.t2]
  refine RelCT.seq (two_post (Ψ := LoopAt Placed n) ?_
    fun a v ⟨s, t₀, i, hE, hb, hn, hi, hc, hv⟩ => WP.mono (keep_ok hE.1 hb hv hi hc)
      fun x hx => ⟨s, t₀, i, hE, hb, hn, hi, hc, hx⟩) ?_
  · have hev : ∀ {s t₀ v : State} {i : Nat}, Loaded s t₀ i v →
        isa.eval (.nonzero .t6) v = some (!decide ((randB s).getD i 0 = 0)) := fun hL => by
      rw [eval_nonzero, hL.t6, nz_setWidth]
    unfold keepB
    refine two_ite (fun a v₁ v₂ ⟨s₁, t₁, i₁, e₁, b₁, n₁, j₁, c₁, L₁⟩ ⟨s₂, t₂, i₂, e₂, b₂, n₂, j₂, c₂, L₂⟩ => ?_)
      (store_taint fun a v₁ v₂ ⟨⟨s₁, t₁, i₁, e₁, b₁, n₁, j₁, c₁, L₁⟩, _⟩ ⟨⟨s₂, t₂, i₂, e₂, b₂, n₂, j₂, c₂, L₂⟩, _⟩ =>
        ?_) (nil_taint fun a v₁ v₂ ⟨⟨s₁, t₁, i₁, e₁, b₁, n₁, j₁, c₁, L₁⟩, _⟩ ⟨⟨s₂, t₂, i₂, e₂, b₂, n₂, j₂, c₂, L₂⟩, _⟩ =>
        ⟨by rw [L₁.keep.sp, b₁.sp, L₂.keep.sp, b₂.sp, fb_eq e₁ e₂], fun _ h => absurd h List.not_mem_nil⟩)
    · have := loop_i e₁ e₂ n₁ n₂ j₁ j₂; subst this
      rw [hev L₁, hev L₂, decide_eq_decide.mpr (zero_eq e₁ e₂ (lt_scan j₁ c₁))]
    · have := loop_i e₁ e₂ n₁ n₂ j₁ j₂; subst this
      refine ⟨by rw [L₁.keep.sp, b₁.sp, L₂.keep.sp, b₂.sp, fb_eq e₁ e₂], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [L₁.keep.get .t1, b₁.t1, L₂.keep.get .t1, b₂.t1, psA_eq e₁ e₂]
      · rw [L₁.t5, L₂.t5, keptLen_eq e₁ e₂ (Nat.le_of_lt (lt_scan j₁ c₁))]
  refine two_post (Ψ := LoopAt More n) ?_
    fun a x ⟨s, t₀, i, hE, hb, hn, hi, hc, hx⟩ => WP.mono (more_ok hE.1 hb hx hi)
      fun u hu => ⟨s, t₀, i, hE, hb, hn, hi, hc, hu⟩
  have pin : ∀ {a x₁ x₂ : State}, LoopAt Placed n a x₁ → LoopAt Placed n a x₂ → x₁.sp = x₂.sp :=
    fun ⟨s₁, t₁, i₁, e₁, b₁, n₁, j₁, c₁, P₁⟩ ⟨s₂, t₂, i₂, e₂, b₂, n₂, j₂, c₂, P₂⟩ => by
      rw [P₁.keep.sp, b₁.sp, P₂.keep.sp, b₂.sp, fb_eq e₁ e₂]
  unfold moreB
  refine two_ite (fun a x₁ x₂ ⟨s₁, t₁, i₁, e₁, b₁, n₁, j₁, c₁, P₁⟩ ⟨s₂, t₂, i₂, e₂, b₂, n₂, j₂, c₂, P₂⟩ => ?_)
    (li_taint fun a x₁ x₂ h₁ h₂ => ⟨pin h₁.1 h₂.1, fun _ h => absurd h List.not_mem_nil⟩)
    (sub_taint fun a x₁ x₂ h₁ h₂ => ⟨pin h₁.1 h₂.1, fun _ h => absurd h List.not_mem_nil⟩)
  have := loop_i e₁ e₂ n₁ n₂ j₁ j₂; subst this
  show some (x₁.gpr .t5 == x₁.gpr .s1) = some (x₂.gpr .t5 == x₂.gpr .s1)
  rw [P₁.t5, P₂.t5, P₁.keep.get .s1, b₁.s1, P₂.keep.get .s1, b₂.s1, psLen_same e₁ e₂,
    keptLen_eq e₁ e₂ (lt_scan j₁ c₁)]

theorem loop_ct (n : Nat) :
    RelCT isa (Two (LoopAt At n)) (.loop step (.nonzero .t0)) fun _ _ => True := by
  refine RelCT.loop (fun n => Two (LoopAt At n)) (fun n => (step_ct n).mono (fun _ _ h => h) ?_) n
  rintro u₁ u₂ ⟨a, ⟨s₁, t₁, i₁, e₁, b₁, n₁, j₁, c₁, A₁, z₁⟩, ⟨s₂, t₂, i₂, e₂, b₂, n₂, j₂, c₂, A₂, z₂⟩⟩
  have := loop_i e₁ e₂ n₁ n₂ j₁ j₂; subst this
  have hk := keptLen_eq e₁ e₂ (lt_scan j₁ c₁)
  have hd : decide ((kept s₁ (i₁ + 1)).length = psLen s₁ ∨ i₁ + 1 = (stackArg s₁ 2).toNat) =
      decide ((kept s₂ (i₁ + 1)).length = psLen s₂ ∨ i₁ + 1 = (stackArg s₂ 2).toNat) := by
    rw [hk, psLen_same e₁ e₂, arg_eq e₁ e₂ (j := 2)]
  refine ⟨by rw [eval_nonzero, eval_nonzero, z₁, z₂, hd], fun _ => trivial, fun ht => ?_⟩
  rw [eval_nonzero, z₁] at ht
  have hstop : ¬((kept s₁ (i₁ + 1)).length = psLen s₁ ∨ i₁ + 1 = (stackArg s₁ 2).toNat) := by
    intro h; rw [decide_eq_true h] at ht; exact absurd ht (by decide)
  have hstop₂ : ¬((kept s₂ (i₁ + 1)).length = psLen s₂ ∨ i₁ + 1 = (stackArg s₂ 2).toNat) :=
    of_decide_eq_false (hd ▸ decide_eq_false hstop)
  have hp₁ := A₁.hc; have hp₂ := A₂.hc
  have ha : (stackArg s₁ 2).toNat = (stackArg a 2).toNat := by rw [e₁.2.args 2 (by decide)]
  refine ⟨(stackArg a 2).toNat - (i₁ + 1), by omega, a, ⟨s₁, t₁, i₁ + 1, e₁, b₁, rfl, by omega, by omega, A₁⟩,
    ⟨s₂, t₂, i₁ + 1, e₂, b₂, rfl, by omega, by omega, A₂⟩⟩

/-- Before the scan. -/
def ScanΦ (a t : State) : Prop := ∃ s, E a s ∧ Before s t ∧ t.gpr .t2 = 0 ∧ t.gpr .t5 = 0

theorem at_zero {s t : State} (h2 : t.gpr .t2 = 0) (h5 : t.gpr .t5 = 0) : At s t 0 t :=
  ⟨Kept.refl _ _, by rw [kept_zero, writeBytes_nil], h2, by rw [h5, kept_zero]; rfl, Nat.zero_le _,
    by rw [kept_zero]; simp⟩

theorem scan_ct : RelCT isa (Two ScanΦ) scan fun _ _ => True := by
  unfold scan
  refine two_ite (fun a t₁ t₂ ⟨s₁, e₁, b₁, _, _⟩ ⟨s₂, e₂, b₂, _, _⟩ => by
      rw [eval_nonzero, eval_nonzero, b₁.t4, b₂.t4, arg_eq e₁ e₂]) ?_
    (nil_taint fun a t₁ t₂ ⟨⟨s₁, e₁, b₁, _, _⟩, _⟩ ⟨⟨s₂, e₂, b₂, _, _⟩, _⟩ =>
      ⟨by rw [b₁.sp, b₂.sp, fb_eq e₁ e₂], fun _ h => absurd h List.not_mem_nil⟩)
  have conv : ∀ {a t : State}, ScanΦ a t → isa.eval (.nonzero .t4) t = some true →
      LoopAt At ((stackArg a 2).toNat - 0) a t := fun {a} {t} ⟨s, e, b, h2, h5⟩ ht => by
    have hP := psLen_pos e.1
    rw [eval_nonzero, b.t4] at ht
    have hl : 0 < (stackArg s 2).toNat := by
      rcases Nat.eq_zero_or_pos (stackArg s 2).toNat with h | h
      · have : stackArg s 2 = 0 := BitVec.eq_of_toNat_eq (by rw [h]; rfl)
        rw [this] at ht; exact absurd ht (by decide)
      · exact h
    exact ⟨s, t, 0, e, b, rfl, hl, by rw [kept_zero]; simp; omega, at_zero h2 h5⟩
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨a, ⟨h₁, c₁⟩, ⟨h₂, c₂⟩⟩ x₁ x₂
  exact loop_ct ((stackArg a 2).toNat - 0) _ _ _ _ _ _ ⟨a, conv h₁ c₁, conv h₂ c₂⟩ x₁ x₂

/-! ## The call -/

/-- At the call's frame. -/
def CallΦ (a z : State) : Prop := ∃ s i ps, E a s ∧ Pre s z i ps

theorem callArg_eq {a s₁ s₂ : State} (h₁ : E a s₁) (h₂ : E a s₂) (j : Nat) : callArg s₁ j = callArg s₂ j := by
  match j with
  | 0 => exact psA_eq h₁ h₂
  | 1 => show BitVec.ofNat 64 _ = BitVec.ofNat 64 _; rw [psLen_same h₁ h₂]
  | 2 => exact arg_eq h₁ h₂
  | 3 => exact arg_eq h₁ h₂
  | 4 => exact arg_eq h₁ h₂
  | _ + 5 => exact arg_eq h₁ h₂

theorem encPub {a s₁ s₂ w₁ w₂ : State} (h₁ : E a s₁) (h₂ : E a s₂) {i₁ i₂ : Nat} {ps₁ ps₂ : List Byte}
    (hw₁ : Args s₁ w₁ i₁ ps₁) (hw₂ : Args s₂ w₂ i₂ ps₂) :
    (Proof.RsaPkcs1Enc.encryptPrecomputedContract abi frameBytes).pub
      (w₁.callEntry.withRegions (callRd s₁) (callWr s₁)) (w₂.callEntry.withRegions (callRd s₂) (callWr s₂)) := by
  have hp₁ := h₁.1; have hp₂ := h₂.1
  have mem : ∀ {w : State} {rd wr : List Region}, (w.callEntry.withRegions rd wr).mem = w.mem := rfl
  have sp : ∀ {w : State} {rd wr : List Region}, (w.callEntry.withRegions rd wr).sp = w.sp := rfl
  have cg : ∀ {w : State} {rd wr : List Region} {r : Reg}, r ∉ linkRegs →
      (w.callEntry.withRegions rd wr).gpr r = w.gpr r := fun h => State.callEntry_gpr _ h
  have nE : ∀ {s w : State} {i : Nat} {ps : List Byte}, RPre s → Args s w i ps →
      Spec.Rsa.bytesAt w.mem (s.gpr .a3) (s.gpr .a4).toNat = nB s := fun {s} {_} {_} {_} hp hw =>
    bytes_mem (R := nR s) hw.fr (k_dis hp.kn) hp.tn hp.on hp.ns.symm (low_dis hp.kn)
      (by have := hp.wn; show (s.gpr .a4).toNat ≤ 2 ^ 64; omega)
  have eE : ∀ {s w : State} {i : Nat} {ps : List Byte}, RPre s → Args s w i ps →
      Spec.Rsa.bytesAt w.mem (s.gpr .a5) (s.gpr .a6).toNat = eB s := fun {s} {_} {_} {_} hp hw =>
    bytes_mem (R := eR s) hw.fr (k_dis hp.ke) hp.te hp.oe hp.es.symm (low_dis hp.ke)
      (by have := hp.we; show (s.gpr .a6).toNat ≤ 2 ^ 64; omega)
  have qE : ∀ {s w : State} {i : Nat} {ps : List Byte}, RPre s → Args s w i ps →
      Spec.Rsa.wordsAt w.mem (stackArg s 5) (stackArg s 6).toNat = preW s := fun {s} {_} {_} {_} hp hw =>
    words_mem hw.fr (k_dis hp.kp) hp.tp hp.op hp.sp (low_dis hp.kp) hp.wp
  sig_pub [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi, argRegs,
    Enc.stackArgs_six, List.append_eq]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  simp only [entry_arg hw₁ _ _ (j := 0) (by decide), entry_arg hw₁ _ _ (j := 1) (by decide),
    entry_arg hw₁ _ _ (j := 2) (by decide), entry_arg hw₁ _ _ (j := 3) (by decide),
    entry_arg hw₁ _ _ (j := 4) (by decide), entry_arg hw₁ _ _ (j := 5) (by decide),
    entry_arg hw₂ _ _ (j := 0) (by decide), entry_arg hw₂ _ _ (j := 1) (by decide),
    entry_arg hw₂ _ _ (j := 2) (by decide), entry_arg hw₂ _ _ (j := 3) (by decide),
    entry_arg hw₂ _ _ (j := 4) (by decide), entry_arg hw₂ _ _ (j := 5) (by decide),
    hw₁.a0, hw₁.a1, hw₁.a2, hw₁.a3, hw₁.a4, hw₁.a5, hw₁.a6, hw₁.a7,
    hw₂.a0, hw₂.a1, hw₂.a2, hw₂.a3, hw₂.a4, hw₂.a5, hw₂.a6, hw₂.a7, hw₁.sp, hw₂.sp]
  rw [show callArg s₁ 4 = stackArg s₁ 5 from rfl, show callArg s₁ 5 = stackArg s₁ 6 from rfl,
    show callArg s₂ 4 = stackArg s₂ 5 from rfl, show callArg s₂ 5 = stackArg s₂ 6 from rfl,
    nE hp₁ hw₁, nE hp₂ hw₂, eE hp₁ hw₁, eE hp₂ hw₂, qE hp₁ hw₁, qE hp₂ hw₂, h₁.2.n, h₂.2.n, h₁.2.e, h₂.2.e,
    h₁.2.w, h₂.2.w]
  exact ⟨by rw [fb_eq h₁ h₂], rfl, g_eq h₁ h₂, g_eq h₁ h₂, g_eq h₁ h₂, g_eq h₁ h₂, g_eq h₁ h₂, g_eq h₁ h₂,
    g_eq h₁ h₂, arg_eq h₁ h₂, callArg_eq h₁ h₂ 0, callArg_eq h₁ h₂ 1, callArg_eq h₁ h₂ 2, callArg_eq h₁ h₂ 3,
    callArg_eq h₁ h₂ 4, callArg_eq h₁ h₂ 5⟩

theorem call_ct : RelCT isa (Two CallΦ) Impl.RsaPkcs1Enc.RISCV64.Random.call fun _ _ => True := by
  unfold Impl.RsaPkcs1Enc.RISCV64.Random.call
  refine two_alloc (R := fun _ _ => True) ?_
  refine RelCT.seq (two_post (Ψ := fun a w => ∃ s i ps, E a s ∧ Args s w i ps)
    (callStack_taint fun a u₁ u₂ ⟨z₁, ⟨s₁, i₁, ps₁, e₁, p₁⟩, hu₁⟩ ⟨z₂, ⟨s₂, i₂, ps₂, e₂, p₂⟩, hu₂⟩ => by
      subst hu₁ hu₂
      exact ⟨by show z₁.sp - _ = z₂.sp - _; rw [p₁.sp, p₂.sp, fb_eq e₁ e₂], fun _ h => absurd h List.not_mem_nil⟩)
    fun a u ⟨z, ⟨s, i, ps, e, hz⟩, hu⟩ => by
      subst hu; exact WP.mono (stack_ok e.1 hz) fun w hw => ⟨s, i, ps, e, hw⟩) ?_
  refine RelCT.callEx Enc.code_correct Enc.code_constantTime
    fun w₁ w₂ ⟨a, ⟨s₁, i₁, ps₁, e₁, hw₁⟩, ⟨s₂, i₂, ps₂, e₂, hw₂⟩⟩ => ?_
  obtain ⟨c₁, d₁⟩ := call_covers e₁.1 hw₁
  obtain ⟨c₂, d₂⟩ := call_covers e₂.1 hw₂
  exact ⟨callRd s₁, callWr s₁, callRd s₂, callWr s₂, encPre_of (preE_c e₁.1 hw₁), encPre_of (preE_c e₂.1 hw₂),
    encPub e₁ e₂ hw₁ hw₂, c₁, d₁, c₂, d₂⟩

/-! ## The two ends -/

/-- `PS` full. -/
def AccΦ (a u : State) : Prop :=
  ∃ s t₀ i, E a s ∧ Before s t₀ ∧ At s t₀ i u ∧ (kept s i).length = psLen s ∧
    Spec.RsaPkcs1Enc.nonzeroPrefix (psLen s) (randB s) = some (kept s i, i)

theorem accept_ct : RelCT isa (Two AccΦ) accept fun _ _ => True := by
  unfold accept
  refine RelCT.seq (two_post (Ψ := CallΦ)
    (callRegs_taint fun a u₁ u₂ ⟨s₁, t₁, i₁, e₁, b₁, I₁, _, _⟩ ⟨s₂, t₂, i₂, e₂, b₂, I₂, _, _⟩ => ⟨by
      rw [I₁.keep.sp, b₁.sp, I₂.keep.sp, b₂.sp, fb_eq e₁ e₂], fun r hr => by
      rw [List.mem_singleton.mp hr, I₁.keep.get .a2, b₁.g .a2 (by decide), I₂.keep.get .a2,
        b₂.g .a2 (by decide), g_eq e₁ e₂]⟩)
    fun a u ⟨s, t₀, i, e, b, hI, hf, _⟩ => WP.mono (callRegs_ok e.1 (ready_of e.1 b hI hf))
      fun z hz => ⟨s, i, _, e, hz⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s i ps, E a s ∧ AfterCall s u i ps) call_ct
    fun a z ⟨s, i, ps, e, hz⟩ => WP.mono (call_ok e.1 hz) fun u hu => ⟨s, i, ps, e, hu⟩) ?_
  exact accTail_taint fun a u₁ u₂ ⟨s₁, i₁, ps₁, e₁, A₁⟩ ⟨s₂, i₂, ps₂, e₂, A₂⟩ =>
    ⟨by rw [A₁.sp, A₂.sp, fb_eq e₁ e₂], fun r hr => by
      rw [List.mem_singleton.mp hr, A₁.s1, A₂.s1, psLen_same e₁ e₂]⟩

/-- `PS` not full. -/
def RejΦ (a u : State) : Prop :=
  ∃ s t₀, E a s ∧ Before s t₀ ∧ At s t₀ (stackArg s 2).toNat u ∧ (kept s (stackArg s 2).toNat).length < psLen s

theorem scan_all {s : State} (hc : (kept s (stackArg s 2).toNat).length < psLen s) :
    VG.Proof.RsaPkcs1Enc.scanLen (psLen s) (randB s) = (stackArg s 2).toNat := by
  rw [kept_all] at hc; rw [VG.Proof.RsaPkcs1Enc.scanLen_all hc, randB_length]

theorem reject_ct : RelCT isa (Two RejΦ) reject fun _ _ => True := by
  refine reject_taint fun a u₁ u₂ ⟨s₁, t₁, e₁, b₁, I₁, c₁⟩ ⟨s₂, t₂, e₂, b₂, I₂, c₂⟩ => ⟨by
    rw [I₁.keep.sp, b₁.sp, I₂.keep.sp, b₂.sp, fb_eq e₁ e₂], fun r hr => ?_⟩
  have ga : ∀ {s t₀ u : State} {i : Nat}, Before s t₀ → At s t₀ i u → ∀ r ∈ argRegs, u.gpr r = s.gpr r :=
    fun b I r hr => by
      have : r ∉ [Reg.t6, .t2, .t0, .t5] := by
        simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [I.keep.gpr r this, b.g r hr]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [I₁.t5, I₂.t5, arg_eq e₁ e₂ (j := 2), keptLen_eq e₁ e₂ (by rw [scan_all c₁, arg_eq e₁ e₂ (j := 2)])]
  · rw [ga b₁ I₁ .a0 (by decide), ga b₂ I₂ .a0 (by decide), g_eq e₁ e₂]
  · rw [ga b₁ I₁ .a4 (by decide), ga b₂ I₂ .a4 (by decide), g_eq e₁ e₂]
  · rw [I₁.keep.get .s1, b₁.s1, I₂.keep.get .s1, b₂.s1, psLen_same e₁ e₂]
  · rw [I₁.keep.get .t4, b₁.t4, I₂.keep.get .t4, b₂.t4, arg_eq e₁ e₂]
  · rw [ga b₁ I₁ .a2 (by decide), ga b₂ I₂ .a2 (by decide), g_eq e₁ e₂]

/-- After the scan. -/
def DoneΦ (a u : State) : Prop := ∃ s t₀, E a s ∧ Before s t₀ ∧ Done s t₀ u

theorem done_i {s : State} {i : Nat} (h : ((kept s i).length = psLen s ∧
      Spec.RsaPkcs1Enc.nonzeroPrefix (psLen s) (randB s) = some (kept s i, i)) ∨
    (i = (stackArg s 2).toNat ∧ (kept s i).length < psLen s)) :
    i = VG.Proof.RsaPkcs1Enc.scanLen (psLen s) (randB s) := by
  rcases h with ⟨-, hp⟩ | ⟨rfl, hc⟩
  · exact VG.Proof.RsaPkcs1Enc.used_eq hp
  · exact (scan_all hc).symm

theorem tail_ct : RelCT isa (Two DoneΦ) (.ite (.eq .t5 .s1) accept reject) fun _ _ => True := by
  have hev : ∀ {s t₀ u : State} {i : Nat}, RPre s → Before s t₀ → At s t₀ i u →
      isa.eval (.eq .t5 .s1) u = some (decide ((kept s i).length = psLen s)) := fun {s} {t₀} {u} {i} hp b I => by
    have := I.hc; have := psLen_le hp
    show some (u.gpr .t5 == u.gpr .s1) = _
    rw [I.t5, I.keep.get .s1, b.s1, beq_ofNat (by omega) (by omega)]
  refine two_ite (fun a u₁ u₂ ⟨s₁, t₁, e₁, b₁, i₁, I₁, d₁⟩ ⟨s₂, t₂, e₂, b₂, i₂, I₂, d₂⟩ => ?_)
    (accept_ct.mono (fun u₁ u₂ ⟨a, ⟨⟨s₁, t₁, e₁, b₁, i₁, I₁, d₁⟩, c₁⟩, ⟨⟨s₂, t₂, e₂, b₂, i₂, I₂, d₂⟩, c₂⟩⟩ => ?_)
      fun _ _ h => h)
    (reject_ct.mono (fun u₁ u₂ ⟨a, ⟨⟨s₁, t₁, e₁, b₁, i₁, I₁, d₁⟩, c₁⟩, ⟨⟨s₂, t₂, e₂, b₂, i₂, I₂, d₂⟩, c₂⟩⟩ => ?_)
      fun _ _ h => h)
  · rw [hev e₁.1 b₁ I₁, hev e₂.1 b₂ I₂, done_i d₁, done_i d₂, ← scanLen_eq' e₁ e₂,
      keptLen_eq e₁ e₂ (Nat.le_refl _), psLen_same e₁ e₂]
  · rw [hev e₁.1 b₁ I₁] at c₁; rw [hev e₂.1 b₂ I₂] at c₂
    have f₁ : (kept s₁ i₁).length = psLen s₁ := of_decide_eq_true (Option.some.inj c₁)
    have f₂ : (kept s₂ i₂).length = psLen s₂ := of_decide_eq_true (Option.some.inj c₂)
    have p₁ := d₁.resolve_right fun ⟨_, h⟩ => by omega
    have p₂ := d₂.resolve_right fun ⟨_, h⟩ => by omega
    exact ⟨a, ⟨s₁, t₁, i₁, e₁, b₁, I₁, f₁, p₁.2⟩, ⟨s₂, t₂, i₂, e₂, b₂, I₂, f₂, p₂.2⟩⟩
  · rw [hev e₁.1 b₁ I₁] at c₁; rw [hev e₂.1 b₂ I₂] at c₂
    have f₁ : ¬(kept s₁ i₁).length = psLen s₁ := of_decide_eq_false (Option.some.inj c₁)
    have f₂ : ¬(kept s₂ i₂).length = psLen s₂ := of_decide_eq_false (Option.some.inj c₂)
    obtain ⟨rfl, h₁⟩ := d₁.resolve_left fun ⟨h, _⟩ => f₁ h
    obtain ⟨rfl, h₂⟩ := d₂.resolve_left fun ⟨h, _⟩ => f₂ h
    exact ⟨a, ⟨s₁, t₁, e₁, b₁, I₁, h₁⟩, ⟨s₂, t₂, e₂, b₂, I₂, h₂⟩⟩

/-! ## The whole function -/

theorem code_ct : RelCT isa (Two E) code fun _ _ => True := by
  unfold code
  refine two_alloc (R := fun _ _ => True) ?_
  unfold body
  refine RelCT.seq (two_post (Ψ := ScanΦ)
    (setup_taint fun _ _ _ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ =>
      ⟨by rw [e₁, e₂]; show s₁.sp - _ = s₂.sp - _; rw [sp_eq h₁ h₂], fun _ h => absurd h List.not_mem_nil⟩)
    fun a u ⟨s, h, hu⟩ => by
      subst hu
      exact WP.mono (setup_ok h.1 rfl rfl rfl (Frame.refl _ _) (fun _ => rfl))
        fun w ⟨hb, h2, h5⟩ => ⟨s, h, hb, h2, h5⟩) ?_
  refine RelCT.seq (two_post (Ψ := DoneΦ) scan_ct
    fun a t ⟨s, h, hb, h2, h5⟩ => WP.mono (scan_ok h.1 hb h2 h5) fun u hu => ⟨s, t, h, hb, hu⟩) ?_
  exact tail_ct

theorem code_constantTime :
    ConstantTime isa (Spec.RsaPkcs1Enc.encryptRandomContract abi rndStack).pre
      (Spec.RsaPkcs1Enc.encryptRandomContract abi rndStack).pub code :=
  RelCT.constantTime (code_ct.mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨rPre_of h₁, ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩, rPre_of h₂, pubR_of hp⟩)
    fun _ _ h => h)

end VG.Proof.RsaPkcs1Enc.RISCV64.Rnd
