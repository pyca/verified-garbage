module

public import VerifiedGarbage.Proof.RsaPss.X86_64.VSteps
import VerifiedGarbage.Proof.RsaOaep.X86_64.DecLoops
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS verification on x86-64: the frame's shape through `verifyMain`

Each piece of `verifyMain` leads from one `VS` to the next, by its
correctness lemma, of which only the frame's shape, the slots it sets and the
registers the next piece reads are kept: what the constant-time proof needs
of one run between the pieces.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr sScrLen sN sK sE sEl sCtr sHD oEm oSt oDig oLh oBuf oW oRsa scr lay)
open VG.Impl.Mgf1.X86_64 (sp seqs mgfXor)
open VG.Proof.RsaOaep.X86_64 (encStack stkR fb frR frame_sub ret_sub Lay Rep upd nW inR inR_cons inR_nil regs
  retR Good wp_good block_good keep_cs3 cs_disj lenOf tw Here Fns sizes scr_ok mW mW_args mW_other StepW Geo
  ea_sp off_plus cpV mgfXor_ok MFit MArgs retR_disjoint_F cS)
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Proof.Rsa.X86_64 (PublicImpl)
open VG.Proof.HashFns (StreamingOK)

variable {s : State}

/-- The frame's slots that `VS` fixes. -/
def VKey (k : Nat) : Prop := k ∈ vKs ∨ k = 33 ∨ k = 44

theorem vkey_ne {k j : Nat} (hk : VKey k) (hj : j < 14 ∨ (14 < j ∧ j < 21) ∨ j = 32 ∨ (33 < j ∧ j < 37)) :
    k ≠ j := by
  rcases hk with hk | rfl | rfl
  · have := vKs_iff hk; omega
  · omega
  · omega

theorem upd_key {W : Nat → BitVec 64} {j : Nat} (hj : j < 14 ∨ (14 < j ∧ j < 21) ∨ j = 32 ∨ (33 < j ∧ j < 37))
    (v : BitVec 64) {k : Nat} (hk : VKey k) : upd W j v k = W k := ifn (vkey_ne hk hj) _ _

theorem vkey_mW {k : Nat} (hk : VKey k) : k < 15 ∨ 18 < k := by
  rcases hk with hk | rfl | rfl
  · have := vKs_iff hk; omega
  · omega
  · omega

theorem vkey_lt {k : Nat} (hk : VKey k) : k < nW := by
  rcases hk with hk | rfl | rfl
  · have := vKs_iff hk; unfold nW frameBytes; omega
  · decide
  · decide

/-- What a piece leaves of `VS`, from what it leaves of the frame's words. -/
theorem vs_step {P P' : State → (Nat → BitVec 64) → Prop} {c : Prog isa} (hc : Good c) {rs : List Reg}
    (hrs : rs.all (fun r => !calleeSaved.contains r) = true) {X : State → Prop} {t : State} (h : VS P s t)
    (hw : ∀ V W, Rep t.mem (fb s) (stackArg s 4) V W → ArgsV s W → W 33 = off (stackArg s 4) (vE s) →
      W 44 = BitVec.ofNat 64 (vDb s) → P s W → WP isa c t fun t' => Lay t' (fb s) (stackArg s 4) ∧
        Keep rs t t' ∧ (∃ V' W', Rep t'.mem (fb s) (stackArg s 4) V' W' ∧ (∀ k, VKey k → W' k = W k) ∧
          P' s W') ∧ X t') :
    WP isa c t fun t' => VS P' s t' ∧ X t' := by
  obtain ⟨he, -, ⟨V, W, R, hA, h33, h44, hP⟩, hf⟩ := h
  refine WP.mono (wp_good hc (hw V W R hA h33 h44 hP))
    fun t' ⟨⟨L', k', ⟨V', W', R', hW, hP'⟩, hx⟩, sp', mx', f'⟩ => ?_
  exact ⟨⟨he.step k'.2.1 k'.2.2 sp' (keep_cs3 k' hrs) mx' f', L', ⟨V', W', R',
    fun k hk => (hW k (.inl hk)).trans (hA k hk), (hW 33 (.inr (.inl rfl))).trans h33,
    (hW 44 (.inr (.inr rfl))).trans h44, hP'⟩, hf⟩, hx⟩

/-- A piece that keeps the memory. -/
theorem vs_stepM {P : State → (Nat → BitVec 64) → Prop} {c : Prog isa} (hc : Good c) {rs : List Reg}
    (hrs : rs.all (fun r => !calleeSaved.contains r) = true) (hsp : Reg.rsp ∉ rs) {X : State → Prop} {t : State}
    (h : VS P s t)
    (hw : ∀ V W, Rep t.mem (fb s) (stackArg s 4) V W → ArgsV s W → W 33 = off (stackArg s 4) (vE s) →
      W 44 = BitVec.ofNat 64 (vDb s) → P s W → WP isa c t fun t' => t'.mem = t.mem ∧ Keep rs t t' ∧ X t') :
    WP isa c t fun t' => VS P s t' ∧ X t' :=
  vs_step hc hrs h fun V W R hA h33 h44 hP => WP.mono (hw V W R hA h33 h44 hP) fun _ ⟨hm, k, x⟩ =>
    ⟨h.2.1.congr (k.gpr hsp) k.2.2 (by rw [hm]), k, ⟨V, W, hm ▸ R, fun _ _ => rfl, hP⟩, x⟩

/-- A piece that keeps the frame's words. -/
theorem vs_stepW {P : State → (Nat → BitVec 64) → Prop} {c : Prog isa} (hc : Good c) {rs : List Reg}
    (hrs : rs.all (fun r => !calleeSaved.contains r) = true) {X : State → Prop} {t : State}
    (h : VS P s t)
    (hw : ∀ V W, Rep t.mem (fb s) (stackArg s 4) V W → ArgsV s W → W 33 = off (stackArg s 4) (vE s) →
      W 44 = BitVec.ofNat 64 (vDb s) → P s W → WP isa c t fun t' => Lay t' (fb s) (stackArg s 4) ∧
        Keep rs t t' ∧ (∃ V', Rep t'.mem (fb s) (stackArg s 4) V' W) ∧ X t') :
    WP isa c t fun t' => VS P s t' ∧ X t' :=
  vs_step hc hrs h fun V W R hA h33 h44 hP => WP.mono (hw V W R hA h33 h44 hP) fun _ ⟨L', k, ⟨V', R'⟩, x⟩ =>
    ⟨L', k, ⟨V', W, R', fun _ _ => rfl, hP⟩, x⟩

/-- The sizes the checks give. -/
theorem VFit.sizes (hp : VPre s) (hf : VFit s) :
    1 ≤ vDb s ∧ vE s + vDb s + vD s ≤ oBuf ∧ 16 ≤ vD s ∧ vD s ≤ 64 ∧ vE s ≤ 1 ∧ vsl s + 1 ≤ vDb s ∧
      vDb s ≤ 1007 := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hlo := loV_le (n0v s)
  have hD : 16 ≤ lenOf (vselH s) ∧ lenOf (vselH s) ≤ 64 := by
    have h := hp.iH
    simp only [Spec.RsaPss.hashIds, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h <;> rw [h] <;> decide
  have := hf.2
  simp only [vDb, vE, vD, vk, oEm, oBuf] at *
  omega

/-! ## The slots of `DB` and the public operation -/

/-- After the checks. -/
def JM (s t : State) : Prop :=
  VEnv s t ∧ Lay t (fb s) (stackArg s 4) ∧ Rep t.mem (fb s) (stackArg s 4) (v0 s) (vcW s) ∧
    t.gpr .rax = BitVec.ofNat 64 (vk s - loV (n0v s) - (lenOf (vselH s) + 2)) ∧ VFit s

/-- Nothing more. -/
def PT (_ : State) (_ : Nat → BitVec 64) : Prop := True

theorem vdb_step {t : State} (h : JM s t) : WP isa (.block dbSlots) t (VS PT s) := by
  obtain ⟨he, L, R, hax, hf⟩ := h
  have hA0 : ArgsV s (vcW s) := fun _ _ => rfl
  refine WP.mono (wp_good (block_good _ rfl rfl) (dbSlots_ok L R hA0.w.2.2.2.2.2.2.2.2.2.2 hax))
    fun t1 ⟨⟨L1, k1, R1⟩, sp1, mx1, f1⟩ => ?_
  exact ⟨he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1, L1, ⟨_, _, R1,
    (hA0.upd' (j := 44) (by omega) _).upd' (j := 33) (by omega) _, by simp [upd], by simp [upd], trivial⟩, hf⟩

/-- The stack arguments of the public operation. -/
def PC (s : State) (W : Nat → BitVec 64) : Prop :=
  W 0 = stackArg s 0 ∧ W 1 = s.gpr .rsi ∧ W 2 = off (stackArg s 4) oRsa ∧ W 3 = stackArg s 5 - 1024

/-- Its register arguments. -/
def RC (s t : State) : Prop :=
  t.gpr .rdi = off (stackArg s 4) oEm ∧ t.gpr .rsi = s.gpr .rsi ∧ t.gpr .rdx = stackArg s 6 ∧
    t.gpr .rcx = stackArg s 7 ∧ t.gpr .r8 = s.gpr .rdx ∧ t.gpr .r9 = s.gpr .rcx

theorem vpub_step (hp : VPre s) {t : State} (h : VS PT s t) :
    WP isa (.block pubArgs) t fun t' => VS PC s t' ∧ RC s t' :=
  vs_step (block_good _ rfl rfl) (rs := [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9]) (by decide) h
    fun V W R hA _ _ _ => by
    obtain ⟨w21, -, w23, w24, w25, w26, -⟩ := hA.w
    exact WP.mono (pubArgsV_ok hp h.2.1 h.1.rd h.1.fr R w21 w23 w24 w25 w26)
      fun t' ⟨L', k', R', a, b, c, d, e, f⟩ => ⟨L', k', ⟨V, _, R', fun k hk => by
        rw [upd_key (j := 3) (by omega) _ hk, upd_key (j := 2) (by omega) _ hk, upd_key (j := 1) (by omega) _ hk,
          upd_key (j := 0) (by omega) _ hk],
        by simp [upd], by simp [upd], by simp [upd], by simp [upd]⟩, a, b, c, d, e, f⟩

theorem vcall_step (v : PublicImpl) (hp : VPre s) {t : State} (h : VS PC s t) (hr : RC s t) :
    WP isa (.call v.name v.code) t (VS PT s) := by
  obtain ⟨he, L, ⟨V, W, R, hA, h33, h44, ⟨w0, w1, w2, w3⟩⟩, hf⟩ := h
  obtain ⟨hdi, hsi, hdx, hcx, h8, h9⟩ := hr
  have hk2 := hp.k2
  refine WP.mono (callV_ok v hp L R he.rd he.wr he.fr w0 w1 w2 w3 hdi hsi hdx hcx h8 h9)
    fun t3 ⟨_, rd3, wr3, cs3, mx3, f3, fr3⟩ => ?_
  have he3 := he.step rd3 wr3 (cs3 .rsp (by decide)) (fun r hr _ => cs3 r hr) mx3 f3
  have G' := L.geo
  have ⟨r1, r2⟩ := rsaV_toNat hp
  have hsl' := hp.hsl'
  have hfr3 : Frame (regs (stackArg s 4) [(oEm, vk s)] ++ [rsaRV s] ++ [retR (fb s)]) t.mem t3.mem :=
    fr3.sub fun r hr => by
      simp only [callWrV, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨off (stackArg s 4) oEm, vk s⟩, by simp [regs], by simp only [emRV]; exact fun _ h => h⟩
      · exact ⟨rsaRV s, by simp, fun _ h => h⟩
      · exact ⟨retR (fb s), by simp,
          Offset.sub_below (fb s) (a := 8) (n := 8) (b := 16) (m := 16) (by decide) (by decide)⟩
  have hx : ∀ r ∈ [rsaRV s], Region.Disjoint r ⟨fb s, frameBytes⟩ ∧ Region.Disjoint r ⟨stackArg s 4, oRsa⟩ :=
    fun r hr => by
      rw [List.mem_singleton.mp hr]
      refine ⟨(hp.dKS.symm.sub_left (rsaV_sub hp)).sub_right (frame_sub s), ?_⟩
      have := Offset.disjoint (stackArg s 4) (d := oRsa) (n := (stackArg s 5 - 1024).toNat * 8) (e := 0) (k := oRsa)
        (.inr (by omega)) (by rw [r1]; have := hp.wS; unfold oRsa; omega) (by decide)
      rwa [BitVec.add_zero] at this
  have R3 := Rep.frameX G' R (rgs := [(oEm, vk s)]) (fun p hp' => by rw [List.mem_singleton.mp hp']; show oEm + vk s ≤ oRsa; unfold vk oEm oRsa; omega) hx hfr3
  have L3 : Lay t3 (fb s) (stackArg s 4) := L.congr (cs3 .rsp (by decide)) wr3 (by
    rw [VG.Proof.RsaOaep.X86_64.slot_eq sScr 14 rfl, VG.Proof.RsaOaep.X86_64.slot_eq sScr 14 rfl,
      R3.fr 14 (by decide), R.fr 14 (by decide)])
  exact ⟨he3, L3, ⟨_, W, R3, hA, h33, h44, trivial⟩, hf⟩

/-! ## The accumulator, MGF1 and the scan -/

theorem vacc_step (hp : VPre s) {t : State} (h : VS PT s t) : WP isa (.block acc0) t (VS PT s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hlo := loV_le (n0v s)
  have hc8 := maskV_byte (show n0v s < 256 from (s.mem (s.gpr .rdi)).isLt)
  refine WP.mono (vs_step (X := fun _ => True) (block_good _ rfl rfl) (rs := [.rcx, .rdi, .rax, .r9, .r11, .r10])
    (by decide) h fun V W R hA h33 _ _ => ?_)
    fun _ h => h.1
  obtain ⟨-, -, w23, -, -, -, -, -, -, w30, w31⟩ := hA.w
  exact WP.mono (acc0_ok h.2.1 R (k := vk s) (lo := loV (n0v s)) (c := (maskV (n0v s)).setWidth 8)
      (by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) h33 (by rw [w30]; exact hc8) w31 (by unfold vk; omega)
      (by unfold vk; omega) (by unfold vk; omega))
    fun t' ⟨L', k', R'⟩ => ⟨L', k', ⟨_, _, R', fun k hk => upd_key (by omega) _ hk, trivial⟩, trivial⟩

/-- MGF1's slots, to mask `DB` with `H`. -/
def PM (s : State) (W : Nat → BitVec 64) : Prop :=
  MArgs W (stackArg s 4) (vE s + vDb s) (vD s) (vE s) (vDb s)

theorem vmgfArgs_step {t : State} (h : VS PT s t) : WP isa (.block mgfArgs) t (VS PM s) :=
  WP.mono (vs_step (X := fun _ => True) (block_good _ rfl rfl) (rs := [.rax, .rdx, .rcx, .r9]) (by decide) h
    fun V W R hA h33 h44 _ =>
    WP.mono (mgfArgs_ok h.2.1 R h33 h44 hA.sel.1) fun t' ⟨L', k', R'⟩ =>
      ⟨L', k', ⟨_, _, R', fun k hk => mW_other (vkey_mW hk), mW_args _ _ _ _ _ _⟩, trivial⟩)
    fun _ h => h.1

variable {TG : Spec.HashFns.Streaming} {Gh : Spec.Mgf1.Hash} (hTG : StreamingOK TG Gh)

include hTG in
theorem vmgf_step (hp : VPre s) (fG : VFns s TG 11) (eG : Spec.HashId.mgf1 (vselG s) = some Gh) {t : State}
    (h : VS PM s t) : WP isa (mgfXor lay) t (VS PT s) := by
  have hDG : TG.S.digestBytes = lenOf (vselG s) := VG.Proof.RsaOaep.X86_64.lenOf_eq hTG eG
  obtain ⟨he, L, ⟨V, W, R, hA, h33, h44, hM⟩, hf⟩ := h
  obtain ⟨d1, d2, -, -, -, -, -⟩ := hf.sizes hp
  refine WP.mono (wp_good VG.Proof.RsaOaep.X86_64.mgfXor_good (mgfXor_ok hTG fG (Gs := Gh)
      (fun x => by rw [hTG.hash]) hTG.len hTG.valid he.here L R
      ⟨by unfold oBuf oSt at *; omega, by unfold oBuf oSt at *; omega, .inr (Nat.le_refl _), d1, by unfold oBuf at d2; omega⟩ hM
      hA.sel.2.2.2 (by rw [hA.sel.2.1, hDG])))
    fun t' ⟨⟨L', _, rd', wr', cs', V', W', R', hW', _⟩, sp', mx', f'⟩ => ?_
  have hk : ∀ k, VKey k → W' k = W k := fun k hk =>
    hW' k (vkey_lt hk) (vkey_ne hk (by omega)) (vkey_ne hk (by omega))
  exact ⟨he.step rd' wr' sp' (fun r hr _ => cs' r hr) mx' f', L', ⟨V', W', R', fun k hk' => (hk k (.inl hk')).trans
    (hA k hk'), (hk 33 (.inr (.inl rfl))).trans h33, (hk 44 (.inr (.inr rfl))).trans h44, trivial⟩, hf⟩

theorem vclear_step (hp : VPre s) {t : State} (h : VS PT s t) : WP isa (.block clearTop) t (VS PT s) := by
  have hc8 := maskV_byte (show n0v s < 256 from (s.mem (s.gpr .rdi)).isLt)
  have := (h.2.2.2.sizes hp).2.2.2.2.1
  refine WP.mono (vs_stepW (X := fun _ => True) (block_good _ rfl rfl) (rs := [.rdi, .rax]) (by decide) h fun V W R hA h33 _ _ => ?_)
    fun _ h => h.1
  obtain ⟨-, -, -, -, -, -, -, -, -, w30, -⟩ := hA.w
  exact WP.mono (clearTop_ok h.2.1 R (c := (maskV (n0v s)).setWidth 8) h33 (by rw [w30]; exact hc8)
    (by unfold oRsa; omega)) fun t' ⟨L', k', R'⟩ => ⟨L', k', ⟨_, R'⟩, trivial⟩

/-- `pos`, the first nonzero byte's index in `DB`, in its slot. -/
def PP (s : State) (W : Nat → BitVec 64) : Prop := ∃ pos, W 32 = BitVec.ofNat 64 pos ∧ pos < vDb s

theorem vscan_step (hp : VPre s) {t : State} (h : VS PT s t) : WP isa (.seq posScan posCheck) t (VS PP s) := by
  obtain ⟨d1, d2, -⟩ := h.2.2.2.sizes hp
  refine WP.mono (vs_step (X := fun _ => True) (VG.Proof.RsaOaep.X86_64.Good.seq posScan_good posCheck_good)
    (rs := [.rdi, .r10, .r8, .rdx, .rsi, .r11, .rax, .r9, .rcx] ++ [.r11, .rdx, .rax, .rcx, .r9]) (by decide) h
    fun V W R hA h33 h44 _ => ?_) fun _ h => h.1
  obtain ⟨-, -, -, -, -, -, -, x28, -, -, -⟩ := hA.w
  refine WP.seq (WP.mono (posScan_ok h.2.1 R h33 h44 d1 (by unfold oBuf oRsa at *; omega))
    fun t8 ⟨k8, hm8, hdx8, hsi8, h118⟩ => ?_)
  have L8 : Lay t8 (fb s) (stackArg s 4) := h.2.1.congr (k8.gpr (by decide)) k8.2.2 (by rw [hm8])
  have hpos := fnz_getD_lt (fun i => V (vE s + i)) d1
  refine WP.mono (posCheck_ok L8 (hm8 ▸ R) (fixed := vfixed s) h44 x28 hpos hdx8 hsi8 h118)
    fun t9 ⟨L9, k9, R9⟩ => ⟨L9, k8.trans k9,
      ⟨_, _, R9, fun k hk => by
        rw [upd_key (j := 5) (by omega) _ hk, upd_key (j := 4) (by omega) _ hk, upd_key (j := 32) (by omega) _ hk],
        _, by simp [upd], hpos⟩, trivial⟩

/-- The test of `saltBack`: ZF set if the salt's length is given. -/
theorem vany_step {P : State → (Nat → BitVec 64) → Prop} {t : State} (h : VS P s t) :
    WP isa (.block [.mov .rax (.mem (sp sAny)), .alu .test .rax (.reg .rax)]) t
      fun t' => VS P s t' ∧ t'.zf = some (vfixed s) :=
  vs_stepM (block_good _ rfl rfl) (rs := [.rax]) (by decide) (by decide) h fun V W R hA _ _ _ => by
    obtain ⟨-, -, -, -, -, -, -, x28, -, -, -⟩ := hA.w
    refine WP.mono (WP.keep [.rax] (Q := fun v => v.zf = some (vfixed s) ∧ v.mem = t.mem) ?_ rfl)
      fun v ⟨⟨hz, hm⟩, k⟩ => ⟨hm, k, hz⟩
    xrun [ea_sp, h.2.1.rsp, h.2.1.ld (d := sAny) (by decide), R.rd (d := sAny) 28 rfl (by decide), x28]
    generalize vfixed s = b
    cases b <;> decide

end VG.Proof.RsaPss.X86_64
