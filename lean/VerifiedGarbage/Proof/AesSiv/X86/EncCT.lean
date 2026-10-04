import VerifiedGarbage.Proof.AesSiv.X86.Dec

/-!
# AES-SIV on x86: `encrypt` and `decrypt` are constant time

Untrusted: everything here is checked by Lean. Two runs with the same
public arguments and the same descriptors of the components (`ETop`) leak
the same. The entry's block reads the stack arguments, which are public;
between the pieces, the correctness lemmas give each run the next piece's
invariant (from `Kept` since the entry); `decrypt` compares the IVs and
masks the data without a branch, so nothing it does depends on the result.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot restore)
open VG.Proof.AesGcm.X86 (CT w64 slotv argA argsR argA_contains and_self_beq32)

/-- The entry, with the components' addresses and lengths `ca`, `cl`. -/
structure ETop (C W SP A D : BitVec 32) (R N n : Nat) (ca : Nat → BitVec 32) (cl : Nat → Nat) (s : State) :
    Prop where
  pre : EPre C W SP A D R N n s
  comps : ∀ j < N, compA s.mem A j = ca j ∧ compL s.mem A j = cl j

theorem sivEntry_ct {I : State → Prop} {W SP : BitVec 32}
    (h : ∀ s, I s → s.gpr .esp = SP ∧ arg s 6 = W ∧ Covers [argsR SP 7] (s.rd ++ s.wr) ∧
      SP.toNat + 4 + 4 * 7 ≤ 2 ^ 32) : CT I sivEntry := by
  refine CT.seq (J := fun s => s.gpr .eax = W ∧ s.gpr .esp = SP)
    (CT.taint [.esp] (pin1 fun s h' => (h s h').1) (by taint_decide)) (fun s hs => ?_)
    (CT.taint [.eax, .esp] (pin2 fun _ h => h) (by taint_decide))
  obtain ⟨hSP, hW, rA, fa⟩ := h s hs
  have i₀ : InRegions (s.rd ++ s.wr) (argA SP 6) 4 := rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) fa⟩
  refine WP.of_runBlock ⟨_, by crun [hSP, i₀], ?_, ?_⟩
  · rw [gpr_setReg_self, ← hSP]; exact hW
  · rw [gpr_setReg_of_ne _ _ (by decide), hSP]

theorem dataStr_ct {I : State → Prop} {W : BitVec 32} (h : ∀ s, I s → s.gpr .ebp = W) :
    CT I (.block [.mov .eax (slot dataO), .store (at_ .ebp strO) .eax, .mov .eax (slot lenO),
      .store (at_ .ebp slenO) .eax]) :=
  CT.taint [.ebp] (pin_ebp h) (by taint_decide)

/-- `encS2v` is constant time. -/
theorem encS2v_ct (v : Ctr32Impl) {C W SP A D : BitVec 32} {R N n : Nat} {ca : Nat → BitVec 32} {cl : Nat → Nat}
    (L : Lay C W SP) (hR : R = 10 ∨ R = 12 ∨ R = 14) (hN : N < 2 ^ 32) (hcl : ∀ j < N, cl j < 2 ^ 32) :
    CT (ETop C W SP A D R N n ca cl) (encS2v v.callee v.suffix) := by
  refine CT.seq (J := fun s₁ => ∃ s, ETop C W SP A D R N n ca cl s ∧ Entered s W s₁)
    (sivEntry_ct fun s hs => ⟨hs.pre.sp, hs.pre.a6, hs.pre.rA, hs.pre.fa⟩)
    (fun s hs => WP.mono (entry_wp hs.pre) fun s₁ en => ⟨s, hs, en⟩) ?_
  refine CT.seq (J := fun s₂ => ∃ s, ETop C W SP A D R N n ca cl s ∧ AInv s C W SP A R N D n 0 s₂)
    ((start_ct v L hR).mono fun s₁ ⟨s, hs, en⟩ =>
      let K := (kept_of_entered hs.pre en).1
      ⟨K.env, K.slots.ctx, K.slots.rounds⟩)
    (fun s₁ ⟨s, hs, en⟩ => WP.mono (start_wp v hs.pre en) fun s₂ I => ⟨s, hs, I⟩) ?_
  refine CT.seq (J := fun s₃ => ∃ s, ETop C W SP A D R N n ca cl s ∧ AInv s C W SP A R N D n N s₃)
    ((s2vAds_ct v L hR hN hcl).mono fun s₂ ⟨s, hs, I⟩ => ⟨s, D, n, hs.pre.ads, hs.comps, I⟩)
    (fun s₂ ⟨s, hs, I⟩ => WP.mono (s2vAds_ok v hs.pre.ads I) fun s₃ I' => ⟨s, hs, I'⟩) ?_
  exact dataStr_ct fun s₃ ⟨_, _, I⟩ => I.kept.env.ebp

/-- After `encS2v`. -/
abbrev EOut (C W SP A D : BitVec 32) (R N n : Nat) (ca : Nat → BitVec 32) (cl : Nat → Nat) (s : State) : Prop :=
  ∃ s₀, ETop C W SP A D R N n ca cl s₀ ∧ S2vOut C W SP A D R N n s₀ s

theorem encS2v_wp (v : Ctr32Impl) {C W SP A D : BitVec 32} {R N n : Nat} {ca : Nat → BitVec 32} {cl : Nat → Nat}
    {s : State} (h : ETop C W SP A D R N n ca cl s) :
    WP isa (encS2v v.callee v.suffix) s (EOut C W SP A D R N n ca cl) :=
  WP.mono (encS2v_ok v h.pre) fun _ O => ⟨s, h, O⟩

/-- The pieces after `encS2v`: `Kept` since an entry, with the regions
`ext`. -/
abbrev EKept (C W SP A D : BitVec 32) (R N n : Nat) (ca : Nat → BitVec 32) (cl : Nat → Nat) (ext : List Region)
    (s : State) : Prop :=
  ∃ s₀, ETop C W SP A D R N n ca cl s₀ ∧ Kept s₀ C W SP R D n ext s

theorem EKept.ctrPre {C W SP A D : BitVec 32} {R N n : Nat} {ca : Nat → BitVec 32} {cl : Nat → Nat}
    {ext : List Region} {s : State} (h : EKept C W SP A D R N n ca cl ext s) : CtrPre C W SP R D n s :=
  let ⟨_, T, K⟩ := h
  ⟨K.env, T.pre.data.of_eq K.rd K.wr, T.pre.n32, K.slots.ctx, K.slots.rounds, K.slots.data, K.slots.len⟩

theorem counter_ct {I : State → Prop} {W : BitVec 32} (h : ∀ s, I s → s.gpr .ebp = W) :
    CT I (.block (counter 0)) :=
  CT.taint [.ebp] (pin_ebp h) (by taint_decide)

/-- The counter `Q` from the IV, and `Kept`: what CTR starts from. -/
theorem counter_wp {C W SP A D : BitVec 32} {R N n : Nat} {ca : Nat → BitVec 32} {cl : Nat → Nat}
    {ext : List Region} (hext : ∀ r ∈ ext, r.Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩) {s : State}
    (h : EKept C W SP A D R N n ca cl ext s) :
    WP isa (.block (counter 0)) s fun s' => EKept C W SP A D R N n ca cl ext s' ∧
      Spec.Siv.beNat (bytesAt s'.mem (w64 W + BitVec.ofNat 64 cbOff) 16) % 2 ^ 32 < 2 ^ 31 := by
  obtain ⟨s₀, T, K⟩ := h
  have L := T.pre.ads.lay
  obtain ⟨s₃, run₃, m₃, bp₃, sp₃, rd₃, wr₃⟩ := counter_ok L K.env
  have E₃ : Env C W SP s₃ := ⟨bp₃, sp₃, K.env.perm.of_eq rd₃ wr₃⟩
  have f₃ : Frame [⟨w64 W + BitVec.ofNat 64 cbOff, 16⟩] s.mem s₃.mem := by
    rw [m₃]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  refine WP.of_runBlock ⟨s₃, run₃, ⟨s₀, T, K.step L hext E₃ rd₃ wr₃ f₃ counter_wR⟩, ?_⟩
  rw [m₃, counter_bytes]
  exact counter_low _

/-- `vg_aes_siv_encrypt` is constant time. -/
theorem encrypt_top_ct (v : Ctr32Impl) {C W SP A D : BitVec 32} {R N n : Nat} {ca : Nat → BitVec 32}
    {cl : Nat → Nat} (z : State) (Tz : ETop C W SP A D R N n ca cl z) :
    CT (ETop C W SP A D R N n ca cl) (encrypt v.callee v.suffix) := by
  have L := Tz.pre.ads.lay
  have hR := Tz.pre.ads.rounds
  have hcl : ∀ j < N, cl j < 2 ^ 32 := fun j hj => by rw [← (Tz.comps j hj).2]; exact BitVec.isLt _
  have hW16 : (⟨w64 W, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ := by
    simpa using Lay.w_w (W := W) (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
  have hext : ∀ r ∈ [(⟨w64 W, 16⟩ : Region)], r.Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hW16
  refine CT.seq (J := EOut C W SP A D R N n ca cl) (encS2v_ct v L hR Tz.pre.ads.N32 hcl)
    (fun s hs => encS2v_wp v hs) ?_
  refine CT.seq (J := EKept C W SP A D R N n ca cl [⟨w64 W, 16⟩])
    ((finish_ct v L hR Tz.pre.n32 (.inl rfl)).mono fun s ⟨_, _, O⟩ => O.pre)
    (fun s ⟨s₀, T, O⟩ => WP.mono (finish_ok v L hR O.pre (out := 0) (.inl rfl)) fun s₂ F =>
      ⟨s₀, T, (O.kept.widen _).step L (fun r hr => by
        simp only [List.nil_append, List.mem_singleton] at hr; subst hr; exact hW16)
        F.env F.rd F.wr F.frame (finR_wR (.inl ⟨rfl, by simp⟩))⟩) ?_
  refine CT.seq (J := fun s => EKept C W SP A D R N n ca cl [⟨w64 W, 16⟩] s ∧
      Spec.Siv.beNat (bytesAt s.mem (w64 W + BitVec.ofNat 64 cbOff) 16) % 2 ^ 32 < 2 ^ 31)
    (counter_ct fun s ⟨_, _, K⟩ => K.env.ebp) (fun s hs => counter_wp hext hs) ?_
  refine CT.seq (J := fun s => s.gpr .ebp = W)
    ((ctr_ct v L hR).mono fun s ⟨h, low⟩ => ⟨h.ctrPre, low⟩)
    (fun s ⟨h, low⟩ => let P := h.ctrPre
      WP.mono (ctr_ok v L hR P.env P.dat P.n32 P.ctx P.rounds P.data P.len rfl low) fun _ ⟨E, _⟩ => E.ebp) ?_
  exact CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)

/-! ## `decrypt` -/

theorem maskTest_ok {C W SP : BitVec 32} {s : State} (L : Lay C W SP) (E : Env C W SP s) {n : Nat}
    (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) (hn32 : n < 2 ^ 32) :
    ∃ s₁, runBlock isa [.mov .ecx (slot lenO), .alu .test .ecx (.reg .ecx)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .ecx = BitVec.ofNat 32 n ∧ s₁.zf = some (decide (n = 0)) ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hlen], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · cregs [hlen]
  · cmems [hlen]; rw [and_self_beq32 hn32]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

theorem maskArgs_ok {C W SP : BitVec 32} {s₁ : State} (L : Lay C W SP) (E₁ : Env C W SP s₁) {D : BitVec 32} {n : Nat}
    (hd₁ : slotv s₁.mem W dataO = D) (cx₁ : s₁.gpr .ecx = BitVec.ofNat 32 n) :
    ∃ s₂, runBlock isa [.mov .ebx (imm 0), .alu .sub .ebx (slot okO), .mov .edi (slot dataO)] s₁ = some s₂ ∧
      s₂.gpr .edi = D ∧ s₂.gpr .ecx = BitVec.ofNat 32 n := by
  refine ⟨_, by crun [E₁.ebp, L.aW, E₁.perm.wR, hd₁], ?_, ?_⟩
  · cregs [hd₁]
  · cregs [cx₁]

theorem mask_ct {C W SP : BitVec 32} (L : Lay C W SP) {D : BitVec 32} {n : Nat} (hn32 : n < 2 ^ 32)
    {I : State → Prop}
    (h : ∀ s, I s → Env C W SP s ∧ slotv s.mem W dataO = D ∧ slotv s.mem W lenO = BitVec.ofNat 32 n) :
    CT I mask := by
  refine CT.block_seq [.ebp] (pin_ebp fun s hs => (h s hs).1.ebp) (by taint_decide)
    (fun s hs => maskTest_ok L (h s hs).1 (h s hs).2.2 hn32) ?_
  refine CT.ite (decide (n = 0)) (fun _ ⟨_, _, _, _, hzf, _⟩ => eval_e hzf) (fun _ => CT.nil) fun _ => ?_
  refine CT.block_seq [.ebp] (pin_ebp fun _ ⟨_, _, _, _, _, hbp, _⟩ => hbp) (by taint_decide)
    (fun s₁ ⟨s, hs, m₁, cx₁, _, bp₁, sp₁, rd₁, wr₁⟩ => maskArgs_ok L
      ⟨bp₁, sp₁, (h s hs).1.perm.of_eq rd₁ wr₁⟩ (by rw [m₁]; exact (h s hs).2.1) cx₁) ?_
  exact CT.taint [.edi, .ecx] (pin2 fun _ ⟨_, _, hdi, hcx⟩ => ⟨hdi, hcx⟩) (by taint_decide)

theorem compare_ct {I : State → Prop} {W : BitVec 32} (h : ∀ s, I s → s.gpr .ebp = W) :
    CT I (.block compare) :=
  CT.taint [.ebp] (pin_ebp h) (by taint_decide)

/-- `vg_aes_siv_decrypt` is constant time. -/
theorem decrypt_top_ct (v : Ctr32Impl) {C W SP A D : BitVec 32} {R N n : Nat} {ca : Nat → BitVec 32}
    {cl : Nat → Nat} (z : State) (Tz : ETop C W SP A D R N n ca cl z) :
    CT (ETop C W SP A D R N n ca cl) (decrypt v.callee v.suffix) := by
  have L := Tz.pre.ads.lay
  have hR := Tz.pre.ads.rounds
  have hcl : ∀ j < N, cl j < 2 ^ 32 := fun j hj => by rw [← (Tz.comps j hj).2]; exact BitVec.isLt _
  have hDw : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ :=
    Tz.pre.data.buf.w.sub_right (Lay.wSub (by decide))
  have hextD : ∀ r ∈ [(⟨w64 D, n⟩ : Region)], r.Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hDw
  refine CT.seq (J := EOut C W SP A D R N n ca cl) (encS2v_ct v L hR Tz.pre.ads.N32 hcl)
    (fun s hs => encS2v_wp v hs) ?_
  -- CTR.
  refine CT.seq (J := fun s => EKept C W SP A D R N n ca cl [] s ∧
      Spec.Siv.beNat (bytesAt s.mem (w64 W + BitVec.ofNat 64 cbOff) 16) % 2 ^ 32 < 2 ^ 31)
    (counter_ct fun s ⟨_, _, O⟩ => O.kept.env.ebp)
    (fun s ⟨s₀, T, O⟩ => counter_wp (by simp) ⟨s₀, T, O.kept⟩) ?_
  refine CT.seq (J := EKept C W SP A D R N n ca cl [⟨w64 D, n⟩])
    ((ctr_ct v L hR).mono fun s ⟨h, low⟩ => ⟨h.ctrPre, low⟩)
    (fun s ⟨⟨s₀, T, K⟩, low⟩ => let P := (show EKept C W SP A D R N n ca cl [] s from ⟨s₀, T, K⟩).ctrPre
      WP.mono (ctr_ok v L hR P.env P.dat P.n32 P.ctx P.rounds P.data P.len rfl low)
        fun _ ⟨E, rd, wr, f, _⟩ => ⟨s₀, T, (K.widen _).step L hextD E rd wr f (ctrR_wR (by simp))⟩) ?_
  -- S2V's end with the plaintext.
  refine CT.seq (J := fun s => EKept C W SP A D R N n ca cl [⟨w64 D, n⟩] s ∧ CmacPre C W SP R D n s)
    (dataStr_ct fun s ⟨_, _, K⟩ => K.env.ebp)
    (fun s ⟨s₀, T, K⟩ => by
      obtain ⟨s₄, run₄, P₄, K₄, _⟩ := dataStr_pre L K hextD (T.pre.data.buf.of_eq K.rd K.wr) T.pre.n32
      exact WP.of_runBlock ⟨s₄, run₄, ⟨s₀, T, K₄⟩, P₄⟩) ?_
  refine CT.seq (J := EKept C W SP A D R N n ca cl [⟨w64 D, n⟩])
    ((finish_ct v L hR Tz.pre.n32 (.inr rfl)).mono fun s h => h.2)
    (fun s ⟨⟨s₀, T, K⟩, P⟩ => WP.mono (finish_ok v L hR P (out := tOff) (.inr rfl)) fun _ F =>
      ⟨s₀, T, K.step L hextD F.env F.rd F.wr F.frame (finR_wR (.inr rfl))⟩) ?_
  -- The comparison and the mask.
  refine CT.seq (J := fun s => EKept C W SP A D R N n ca cl [⟨w64 D, n⟩] s ∧
      ∃ c : Bool, slotv s.mem W okO = if c then 1 else 0)
    (compare_ct fun s ⟨_, _, K⟩ => K.env.ebp)
    (fun s ⟨s₀, T, K⟩ => by
      obtain ⟨s₆, run₆, m₆, g₆, rd₆, wr₆⟩ := compare_ok L K.env
      have E₆ : Env C W SP s₆ := K.env.keep (g₆ _ (by decide) (by decide)) (g₆ _ (by decide) (by decide)) rd₆ wr₆
      have f₆ : Frame [⟨w64 W + BitVec.ofNat 64 okO, 4⟩] s.mem s₆.mem := by
        rw [m₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
      refine WP.of_runBlock ⟨s₆, run₆, ⟨s₀, T, K.step L hextD E₆ rd₆ wr₆ f₆ fun r hr => ?_⟩,
        decide (bytesAt s.mem (w64 W) 16 = bytesAt s.mem (w64 W + BitVec.ofNat 64 tOff) 16), ?_⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact .inl ⟨wS W, by simp, sub_wS (by decide) (by decide)⟩
      · rw [m₆, ← okVal_eq]; exact Mem.readW_writeW_self32 _ _ _) ?_
  refine CT.seq (J := fun s => s.gpr .ebp = W)
    (mask_ct L Tz.pre.n32 fun s ⟨⟨_, _, K⟩, _⟩ => ⟨K.env, K.slots.data, K.slots.len⟩)
    (fun s ⟨⟨s₀, T, K⟩, c, hc⟩ => WP.mono (mask_ok L K.env K.slots.data K.slots.len T.pre.n32
      (T.pre.data.buf.of_eq K.rd K.wr) (by rw [K.wr]; exact T.pre.data.wr) hc) fun _ ⟨E, _⟩ => E.ebp) ?_
  exact CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)

end VG.Proof.AesSiv.X86
