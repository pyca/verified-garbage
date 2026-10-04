import VerifiedGarbage.Proof.AesCcm.X86.TopCT
import VerifiedGarbage.Proof.AesCcm.X86.Open

/-!
# AES-CCM on x86: `vg_aes_ccm_open` is constant time

Untrusted: everything here is checked by Lean. After the pieces `seal` also
has (`SealCT.lean`), `open` compares the tags without a branch (AES-GCM's
`recv` and `cmp`, `cmp96_ct`), keeps the result and masks the data with it,
looping over the data's length alone (`mask_ct`): `open_top_ct`, `open_ct`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 copyLoop cmp recv restore tglO tpO rO vO)
open VG.Proof.AesGcm.X86 (CT w64 slotv slotv_eq WEnv cmp_ok recv_ct length_bytesAt and_self_beq32 readW_writeW_off)

/-- `cmp 96` (AES-GCM's `cmp_ct`, for CCM's offset of the computed tag). -/
theorem cmp96_ct {I : State → Prop} {W : BitVec 32} {t : Nat}
    (h : ∀ s, I s → WEnv W s ∧ slotv s.mem W tglO = BitVec.ofNat 32 t) : CT I (cmp uO) := by
  have hb : CT I (.block (zero4 vO ++ [.mov .edi (.reg .ebp), .alu .add .edi (imm uO), .mov .edx (.reg .ebp),
      .alu .add .edx (imm vO), .mov .ecx (slot tglO)])) :=
    CT.taint [.ebp] (pin1 fun s hs => (h s hs).1.ebp) (by taint_decide)
  refine CT.seq (J := fun s => s.gpr .edi = W + BitVec.ofNat 32 uO ∧ s.gpr .edx = W + BitVec.ofNat 32 vO ∧
      s.gpr .ecx = BitVec.ofNat 32 t ∧ s.gpr .ebp = W) hb
    (fun s hs => ?_) (CT.taint [.edi, .edx, .ecx, .ebp] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide))
  obtain ⟨he, hv⟩ := h s hs
  have aW : ∀ {o}, o < 2560 → w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o := fun ho => he.aW ho
  have wIn : ∀ {o}, o + 4 ≤ 2560 → InRegions s.wr (w64 W + BitVec.ofNat 64 o) 4 := fun ho => he.wIn ho
  have rIn : ∀ {o}, o + 4 ≤ 2560 → InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 o) 4 := fun ho => he.wIn' ho
  rw [slotv_eq] at hv
  simp only [tglO] at hv
  exact WP.of_runBlock ⟨_, by xrun [zero4, he.ebp, aW, wIn, rIn, readW_writeW_off, hv], by regs [he.ebp],
    by regs [he.ebp], by regs [], by regs [he.ebp]⟩

/-! ## Masking the data -/

theorem maskTest_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {n : Nat}
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

theorem maskArgs_ok {K W SP : BitVec 32} {s₁ : State} (L : Lay K W SP) (E₁ : Env K W SP s₁) {D : BitVec 32} {n : Nat}
    (hd₁ : slotv s₁.mem W dataO = D) (cx₁ : s₁.gpr .ecx = BitVec.ofNat 32 n) :
    ∃ s₂, runBlock isa [.mov .ebx (imm 0), .alu .sub .ebx (slot okO), .mov .edi (slot dataO)] s₁ = some s₂ ∧
      s₂.gpr .edi = D ∧ s₂.gpr .ecx = BitVec.ofNat 32 n := by
  refine ⟨_, by crun [E₁.ebp, L.aW, E₁.perm.wR, hd₁], ?_, ?_⟩
  · cregs [hd₁]
  · cregs [cx₁]

theorem mask_ct {K W SP : BitVec 32} (L : Lay K W SP) {D : BitVec 32} {n : Nat} (hn32 : n < 2 ^ 32)
    {I : State → Prop}
    (h : ∀ s, I s → Env K W SP s ∧ slotv s.mem W dataO = D ∧ slotv s.mem W lenO = BitVec.ofNat 32 n) :
    CT I mask := by
  refine CT.block_seq [.ebp] (pin_ebp fun s hs => (h s hs).1.ebp) (by taint_decide)
    (fun s hs => maskTest_ok L (h s hs).1 (h s hs).2.2 hn32) ?_
  refine CT.ite (decide (n = 0)) (fun _ ⟨_, _, _, _, hzf, _⟩ => eval_e hzf) (fun _ => CT.nil) fun _ => ?_
  refine CT.block_seq [.ebp] (pin_ebp fun _ ⟨_, _, _, _, _, hbp, _⟩ => hbp) (by taint_decide)
    (fun s₁ ⟨s, hs, m₁, cx₁, _, bp₁, sp₁, rd₁, wr₁⟩ => maskArgs_ok L
      ⟨bp₁, sp₁, (h s hs).1.perm.of_eq rd₁ wr₁⟩ (by rw [m₁]; exact (h s hs).2.1) cx₁) ?_
  exact CT.taint [.edi, .ecx] (pin2 fun _ ⟨_, _, hdi, hcx⟩ => ⟨hdi, hcx⟩) (by taint_decide)

/-! ## `open` -/

theorem okStore_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) :
    ∃ s', runBlock isa [.store (at_ .ebp okO) .eax] s = some s' ∧
      s'.mem = s.mem.writeW (w64 W + BitVec.ofNat 64 okO) (s.gpr .eax) ∧ Env K W SP s' ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wW], ?_, E.keep (by cregs []) (by cregs []) (by cmems []) (by cmems []), ?_, ?_⟩
  all_goals cmems []

theorem open_top_ct (v : Ctr32Impl) {K W SP N A D : BitVec 32} {R nl al n tl : Nat} (z : State)
    (Tz : Top K W SP N A D R nl al n tl z) :
    CT (Top K W SP N A D R nl al n tl) («open» v.callee v.suffix) := by
  have Ar := Tz.args
  have L := Ar.lay
  have h7' : ∀ m : Mem, 7 ≤ (bytesAt m (w64 N) nl).length := fun m => by rw [length_bytesAt]; exact Ar.h7
  have h13' : ∀ m : Mem, (bytesAt m (w64 N) nl).length ≤ 13 := fun m => by rw [length_bytesAt]; exact Ar.h13
  have c0W : ∀ {d k : Nat}, (64 ≤ d ∨ d + k ≤ 48) → d + k ≤ 2560 →
      (⟨w64 W + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ := fun h₁ h₂ =>
    Lay.w_w (by omega) (by decide) h₂
  refine RelCT.assoc (CT.seq (J := fun s => ∃ s₀, Top K W SP N A D R nl al n tl s₀ ∧ Run s₀ K W SP N A D R nl al n tl s)
    (start_ct L Ar.h13) (fun s hs => WP.mono (start_ok hs.args hs.sp hs.a0 hs.a1 hs.a2 hs.a3 hs.a4 hs.a5 hs.a6 hs.a7
      hs.a8 hs.a9) fun _ St => ⟨s, hs, Run.of_started St⟩) ?_)
  -- Counter mode.
  refine CT.seq (J := fun s => ∃ s₀, Top K W SP N A D R nl al n tl s₀ ∧ Run s₀ K W SP N A D R nl al n tl s)
    ((ctr_ct v L Ar.rounds Ar.n32).mono fun s ⟨_, T, h⟩ => h.ctr_pre T.args)
    (fun s ⟨s₀, T, h⟩ => by
      obtain ⟨E, hK, hRo, hDp, hlen, nonce, C⟩ := h.ctr_pre T.args
      exact WP.mono (ctr_ok v C E hK hRo hDp hlen) fun _ ⟨E', rd, wr, f, _⟩ => ⟨s₀, T, h.ctr T.args E' rd wr f⟩) ?_
  -- The MAC.
  refine CT.seq (J := fun s => ∃ s₀, Top K W SP N A D R nl al n tl s₀ ∧ Run s₀ K W SP N A D R nl al n tl s)
    ((mac_ct v L Ar.rounds Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.al32 Ar.hn Ar.n32 (.inr rfl)).mono
      fun s ⟨_, T, h⟩ => h.mac_pre T.args)
    (fun s ⟨s₀, T, h⟩ => WP.mono (mac_ok v L h.env Ar.rounds (h.slots T.args) (length_bytesAt _ _ _) Ar.h7 Ar.h13
      Ar.t4 Ar.t16 Ar.te Ar.al32 Ar.hn Ar.n32 h.c0 (.inr rfl) (T.args.aad.of_eq h.rd h.wr)
      (T.args.data.of_eq h.rd h.wr)) fun _ A' => ⟨s₀, T, h.mac T.args (.inr rfl) A'⟩) ?_
  -- The tag.
  refine CT.seq (J := fun s => ∃ s₀, Top K W SP N A D R nl al n tl s₀ ∧ Run s₀ K W SP N A D R nl al n tl s)
    ((tag_ct v L Ar.rounds (.inr rfl)).mono fun s ⟨_, T, h⟩ => h.tag_pre T.args)
    (fun s ⟨s₀, T, h⟩ => WP.mono (tag_ok v L h.env Ar.rounds (h.slots T.args).ctx (h.slots T.args).rounds (h7' _)
      (h13' _) h.c0 (.inr rfl)) fun _ ⟨E, rd, wr, f, _⟩ => ⟨s₀, T, h.tag T.args (.inr rfl) E rd wr f⟩) ?_
  -- The received tag.
  refine CT.seq (J := fun s => ∃ s₀, Top K W SP N A D R nl al n tl s₀ ∧ Run s₀ K W SP N A D R nl al n tl s)
    (recv_ct (W := W) (T := W) (t := tl) fun s ⟨_, T, h⟩ =>
      ⟨⟨h.env.ebp, h.env.perm.w, L.fw⟩, (h.slots T.args).tl, (h.slots T.args).tp⟩)
    (fun s ⟨s₀, T, h⟩ => WP.mono (recvW_ok L h.env (h.slots T.args).tl (h.slots T.args).tp (by have := Ar.t4; omega)
      Ar.t16) fun _ ⟨_, f, E, rd, wr⟩ => ⟨s₀, T, h.step E rd wr f
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨wT W, by simp, fun _ h => h⟩)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact c0W (.inl (by decide)) (by decide))⟩) ?_
  -- The comparison.
  refine CT.seq (J := fun s => (∃ s₀, Top K W SP N A D R nl al n tl s₀ ∧ Run s₀ K W SP N A D R nl al n tl s) ∧
      ∃ c : Bool, s.gpr .eax = if c then 1 else 0)
    (cmp96_ct (W := W) (t := tl) fun s ⟨_, T, h⟩ => ⟨⟨h.env.ebp, h.env.perm.w, L.fw⟩, (h.slots T.args).tl⟩)
    (fun s ⟨s₀, T, h⟩ => WP.mono (cmp_ok (o := uO) ⟨h.env.ebp, h.env.perm.w, L.fw⟩ (h.slots T.args).tl
      (by have := Ar.t4; omega) Ar.t16 (by decide)) fun s' ⟨ax, f, bp, _, sp, rd, wr⟩ =>
        ⟨⟨s₀, T, h.step ⟨by rw [bp, h.env.ebp], by rw [sp, h.env.esp], h.env.perm.of_eq rd wr⟩ rd wr f
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩)
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact c0W (.inl (by decide)) (by decide))⟩,
          _, by rw [ax, ofNat_ite]⟩) ?_
  -- `ok` kept.
  refine CT.seq (J := fun s => (∃ s₀, Top K W SP N A D R nl al n tl s₀ ∧ Run s₀ K W SP N A D R nl al n tl s) ∧
      ∃ c : Bool, slotv s.mem W okO = if c then 1 else 0)
    (CT.taint [.ebp] (pin_ebp fun _ ⟨⟨_, _, h⟩, _⟩ => h.env.ebp) (by taint_decide))
    (fun s ⟨⟨s₀, T, h⟩, c, hc⟩ => by
      obtain ⟨s', run, hm, E', rd, wr⟩ := okStore_ok L h.env
      refine WP.of_runBlock ⟨s', run, ⟨s₀, T, h.step E' rd wr (rs := [wO W]) ?_ ?_ ?_⟩, c, ?_⟩
      · rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
      · intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact ⟨wO W, by simp, fun _ h => h⟩
      · intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact c0W (.inl (by decide)) (by decide)
      · rw [hm, ← hc]; exact Mem.readW_writeW_self32 _ _ _) ?_
  -- The data masked.
  refine CT.seq (J := fun s => ∃ s₀, Top K W SP N A D R nl al n tl s₀ ∧ Run s₀ K W SP N A D R nl al n tl s)
    (mask_ct L Ar.n32 fun s ⟨⟨_, T, h⟩, _⟩ => ⟨h.env, (h.slots T.args).data, (h.slots T.args).len⟩)
    (fun s ⟨⟨s₀, T, h⟩, c, hc⟩ => WP.mono (mask_ok L h.env (h.slots T.args).data (h.slots T.args).len Ar.n32
      (T.args.data.of_eq h.rd h.wr) (by rw [h.wr]; exact T.args.dw) hc) fun s' ⟨E, rd, wr, hm⟩ =>
        ⟨s₀, T, h.step E rd wr (rs := [⟨w64 D, n⟩])
          (by rw [hm]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _))
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (T.args.data.w.sub_right (Lay.wSub (by decide))).symm)⟩) ?_
  -- `ok` returned, and the exit.
  refine CT.seq (J := fun s => s.gpr .ebp = W)
    (CT.taint [.ebp] (pin_ebp fun _ ⟨_, _, h⟩ => h.env.ebp) (by taint_decide))
    (fun s ⟨_, _, h⟩ => WP.of_runBlock ⟨_, by crun [h.env.ebp, L.aW, h.env.perm.wR], by cregs [h.env.ebp]⟩)
    (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide))

theorem open_ct (v : Ctr32Impl) : ConstantTime isa openX86.pre openX86.pub («open» v.callee v.suffix) :=
  CT.constantTime pubOf (fun _ _ _ _ h => pubOf_eq h.1) fun p => by
    by_cases hex : ∃ s, openX86.pre s ∧ pubOf s = p
    · obtain ⟨z, hz, hp⟩ := hex
      exact (open_top_ct v z (top_of hz hp)).mono fun s hs => top_of hs.1 hs.2
    · intro s₁ _ _ _ _ _ h
      exact (hex ⟨s₁, h.1⟩).elim

end VG.Proof.AesCcm.X86
