module

import VerifiedGarbage.Proof.MlKem.X86_64.FragCall
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.S4Base
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragCall
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Base
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.M4Squeeze
import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.MlKem.X86_64.ArithOk
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.M4Squeeze
meta import VerifiedGarbage.Proof.MlDsa.Arith.Mem
meta import VerifiedGarbage.Proof.MlKem.X86_64.ArithOk
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `MlDsa.X86_64.Sample.M4CT`, which only this module used -/

section

/-! ### `MlDsa.X86_64.Sample.M4Top`, which only this module used -/

section

/-!
# ML-DSA on x86-64: `vg_mldsa_expand_mask_poly4_avx2`, correctness

Untrusted: everything here is checked by Lean. The pieces, in order: the
prologue, the round constants and the padded seeds (`M4Absorb.lean`), five
squeezes (`M4Squeeze.lean`), which leave the first 680 bytes of SHAKE256 of
each seed in its buffer, the branch on `γ₁`, the four unpackings, each the
loop of `vg_mldsa_expand_mask_poly` (`emBody_ok`) on the output of a seed
(`unpack_ok`), and the epilogue.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Mask4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlDsa.X86_64.Sample.Mask4
open VG.Impl.MlKem.X86_64.Sample4 (oRc oBuf)
open VG.Impl.MlDsa.X86_64.Sample (emBody)
open VG.Proof.MlKem.X86_64
open VG.Proof.MlDsa.X86_64.Sample (GPre emBody_ok emOk emV gOf)
open VG.Proof.MlDsa.Sample (emC emC_eq expandMask_getElem polyIs_of_coeffAt)
open VG.Spec.MlDsa (H)
open VG.Proof.MlDsa (coeffAt)
open VG.Proof.MlDsa.Sample (coeffAddr)
open VG.Proof.Sha3.X86_64.X4 (la)

/-- The first 640 bytes of SHAKE256 of seed `k`. -/
abbrev X (σ : State) (k : Nat) : List Byte := H (B σ k) 640

/-- After the squeezes, and the unpackings of the first `K` seeds, `c` bits a coefficient. -/
structure UI (σ : State) (c K : Nat) (s : State) : Prop where
  env : Env σ s
  buf : ∀ k < 4, ∀ p < 680, s.mem (at' σ (oBuf + 680 * k + p)) = hByte (B σ k) p
  st : ∀ k < K, ∀ i < 256, coeffAt s.mem (poly4 (aP σ) k) i = emV (X σ k) c i

/-- During the unpacking of seed `K`: `g` groups of four. -/
structure EI (σ : State) (c K g : Nat) (s : State) : Prop where
  ui : UI σ c K s
  rsi : s.gpr .rsi = at' σ (oBuf + 680 * K) + BitVec.ofNat 64 (c / 2 * g)
  rdi : s.gpr .rdi = poly4 (aP σ) K + BitVec.ofNat 64 (16 * g)
  cur : ∀ i < 4 * g, coeffAt s.mem (poly4 (aP σ) K) i = emV (X σ K) c i

section
variable {σ : State} (hp : Pre σ)
include hp

/-- The prologue, the round constants and the padded seeds. -/
theorem start_ok : WP isa (.block (pro ++ Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) ++ absorb4)) σ (SqInv σ 0) := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (pro_ok hp) fun s₁ h₁ => WP.mono (rc_ok hp h₁) fun s₂ h₂ => ?_
  have he₂ : Env σ s₂ := Env.low h₁ (rs := [⟨at' σ oRc, 768⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by simp only [oRc, oSave]; omega_using []))
    h₂.frame h₂.keep.2.1 h₂.keep.2.2 fun r hr => h₂.keep.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine WP.mono (absorb_ok hp (m₁ := s₂.mem) ⟨he₂, Frame.refl _ _⟩)
    fun s₃ ⟨a₃, b₃⟩ => ⟨a₃.env, fun r hr k hk => ?_, lanes_A0 b₃, fun _ _ p hp' => absurd hp' (by omega_using [])⟩
  rw [a₃.frame.readW (Region.contains_self _ _) (by
    simpa using Offset.disjoint_base (scr σ) (k := 800) (d := 32 * (50 + r) + 8 * k) (n := 8) (by omega_using []) (by omega_using [hr, hk]))
    (by decide)]
  exact h₂.rc r hr k hk

/-- `Env` after writes to polynomial `K`. -/
theorem Env.poly {K : Nat} (hK : K < 4) {s s' : State} (he : Env σ s)
    (hf : Frame [⟨poly4 (aP σ) K, 1024⟩] s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .r14, .rsp, .r15], s'.gpr r = s.gpr r) : Env σ s' := by
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hg .rbx (by simp), he.rbx], by rw [hg .r12 (by simp), he.r12],
    by rw [hg .r13 (by simp), he.r13], by rw [hg .r14 (by simp), he.r14], by rw [hg .rsp (by simp), he.rsp],
    by rw [hg .r15 (by simp), he.r15], fun i hi => ?_, ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (by
        simpa using ((hp.a_scr.sub_left (sub_poly hK)).sub_right (sub_scr (σ := σ) (a := oSave + 8 * i) (n := 8)
          (by simp only [oSave]; omega_using [hi]))).symm) (by decide)]
    exact he.saved i hi
  · exact he.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨aR σ, by simp, sub_poly hK⟩)

/-- The facts a group of the unpacking of seed `K` needs. -/
theorem gpre {c K g : Nat} (hK : K < 4) (hg : g < 64) {s : State} (h : EI σ c K g s) :
    GPre c (X σ K) (at' σ (oBuf + 680 * K)) (poly4 (aP σ) K) g s := by
  refine ⟨h.rsi, h.rdi, hg, fun j hj => ?_, fun j hj => ?_, fun i hi => ?_, fun j hj hc => ?_⟩
  · rw [at', Offset.add_add, ← at', h.ui.buf K hK j (by omega_using [hj])]; exact (H_getD _ hj).symm
  · rw [at', Offset.add_add, ← at']
    exact in_scr' hp h.ui.env.rd h.ui.env.wr (by simp only [oBuf]; omega_using [hK, hj])
  · rw [h.ui.env.wr, hp.wr]
    refine ⟨aR σ, by simp, ?_⟩
    rw [coeffAddr, poly4, Offset.add_add]
    exact Offset.contains_base _ (by omega_using [hK, hi]) (by omega_using [hK, hi])
  · rw [at', Offset.add_add] at hc
    exact (hp.a_scr.sub_left (sub_poly hK)) _ hc
      (Offset.contains_base _ (by simp only [oBuf]; omega_using [hK, hj]) (by simp only [oBuf]; omega_using [hK, hj]))

/-- An iteration of the unpacking of seed `K`. -/
theorem ei_step {c K g : Nat} (hc : emOk c) (hK : K < 4) (hg : g < 64) {s : State} (h : EI σ c K g s) :
    WP isa (.block (emBody c)) s fun s' => EI σ c K (g + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) := by
  refine WP.mono (emBody_ok hc (gpre hp hK hg h)) fun s' ⟨hk, hf, hst, hsame, hsi, hdi, hcx, hz⟩ => ?_
  refine ⟨⟨⟨Env.poly hp hK h.ui.env hf hk.2.1 hk.2.2 fun r hr => hk.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide), fun k hk' p hp' => ?_, fun k hk' i hi => ?_⟩,
    hsi, hdi, fun i hi => ?_⟩, hcx, hz⟩
  · rw [buf_frame (by simpa using ((hp.a_scr.sub_left (sub_poly hK)).sub_right (sub_scr (σ := σ) (a := oBuf)
        (n := 2720) (by simp only [oBuf]; omega_using []))).symm) hf hk' hp']
    exact h.ui.buf k hk' p hp'
  · rw [show coeffAt s'.mem (poly4 (aP σ) k) i = coeffAt s.mem (poly4 (aP σ) k) i from
      hf.readW (VG.Proof.MlDsa.Sample.coeff_contains _ hi) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have hd := Offset.disjoint (aP σ) (d := 1024 * k) (n := 1024) (e := 1024 * K) (k := 1024) (by omega_using [hk'])
          (by omega_using [hK, hk']) (by omega_using [hK])
        simpa [poly4] using hd) (by decide)]
    exact h.ui.st k hk' i hi
  · by_cases hlo : i < 4 * g
    · rw [hsame i (by omega_using [hg, hi]) (.inl hlo)]; exact h.cur i hlo
    · have := hst (i - 4 * g) (by omega_using [hi])
      rwa [show 4 * g + (i - 4 * g) = i by omega_using [hlo]] at this

/-- The unpacking of seed `K`. -/
theorem unpack_ok {c K : Nat} (hc : emOk c) (hK : K < 4) {s : State} (h : UI σ c K s) :
    WP isa (unpack c K) s (UI σ c (K + 1)) := by
  unfold unpack
  refine WP.seq (WP.mono (WP.keep [.rsi, .rdi, .rcx] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rsi = at' σ (oBuf + 680 * K) ∧ s'.gpr .rdi = poly4 (aP σ) K ∧ s'.gpr .rcx = BitVec.ofNat 64 64)
    (by xrun [h.env.rbx, h.env.r13, sx_ofNat (show oBuf + 680 * K < 2 ^ 31 by simp only [oBuf]; omega_using [hK]),
      sx_ofNat (show 1024 * K < 2 ^ 31 by omega_using [hK])]) (by rfl)) fun s1 ⟨⟨hm1, hsi1, hdi1, hcx1⟩, k1⟩ => ?_)
  have he1 : Env σ s1 := Env.low h.env (rs := []) (by simp) (by rw [hm1]; exact Frame.refl _ _) k1.2.1 k1.2.2
    fun r hr => k1.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine wp_countdown (N := 64) (by decide) (by decide) (EI σ c K) (fun g hg s hI _ =>
    WP.mono (ei_step hp hc hK hg hI) fun s' ⟨hI', hc', hz⟩ => ⟨hI', hc', hz⟩) (fun s' hI =>
      ⟨hI.ui.env, hI.ui.buf, fun k hk i hi => ?_⟩)
    ⟨⟨he1, fun k hk p hp' => by rw [hm1]; exact h.buf k hk p hp', fun k hk i hi => by rw [hm1]; exact h.st k hk i hi⟩,
      by rw [hsi1]; simp, by rw [hdi1]; simp, fun i hi => absurd hi (by omega_using [])⟩ hcx1
  by_cases e : k = K
  · subst e; exact hI.cur i (by omega_using [hi])
  · exact hI.ui.st k (by omega_using [hk, e]) i hi

/-- The four unpackings. -/
theorem unpack4_ok {c : Nat} (hc : emOk c) {s : State} (h : UI σ c 0 s) : WP isa (unpack4 c) s (UI σ c 4) :=
  WP.seq (WP.mono (unpack_ok hp hc (by decide) h) fun _ h₁ => WP.seq (WP.mono (unpack_ok hp hc (by decide) h₁)
    fun _ h₂ => WP.seq (WP.mono (unpack_ok hp hc (by decide) h₂) fun _ h₃ => unpack_ok hp hc (by decide) h₃)))

/-- The branch on `γ₁`, and the unpackings for it. -/
theorem sel_ok {s : State} (h : SqInv σ 5 s) {Q : State → Prop} (kont : ∀ s', UI σ (emC (gOf σ)) 4 s' →
    WP isa (.block epi) s' Q) :
    WP isa (.seq (.block [.vop .vzeroupper, .alu32 .cmp .r14 (.imm 0x20000)])
      (.seq (.ite .e (unpack4 18) (unpack4 20)) (.block epi))) s Q := by
  refine WP.seq (WP.mono (WP.keep [.r14] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r14 = s.gpr .r14 ∧
      s'.zf = some (BitVec.setWidth 32 (s.gpr .r14) - 0x20000 == 0)) (by xrun; exact ⟨rfl, rfl, rfl⟩) (by decide))
    fun s1 ⟨⟨hm1, h14, hz1⟩, k1'⟩ => ?_)
  have k1 : Keep [] s s1 := ⟨fun r _ => by
    by_cases e : r = .r14
    · subst e; exact h14
    · exact k1'.gpr (by simp [e]), k1'.2⟩
  have hr14 : BitVec.setWidth 32 (s.gpr .r14) = BitVec.ofNat 32 (gOf σ) := by
    rw [h.env.r14, gOf, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hU : ∀ c, UI σ c 0 s1 := fun c => ⟨Env.low h.env (rs := []) (by simp) (by rw [hm1]; exact Frame.refl _ _)
      k1.2.1 k1.2.2 fun r _ => k1.gpr (List.not_mem_nil),
    fun k hk p hp' => by rw [hm1]; exact h.buf k hk p (by omega_using [hp']), fun _ hk => absurd hk (by omega_using [])⟩
  refine WP.seq (WP.mono (?_ : WP isa (.ite .e (unpack4 18) (unpack4 20)) s1 (UI σ (emC (gOf σ)) 4)) kont)
  rcases hp.gamma with he | he
  · refine WP.ite true (by show s1.zf = _; rw [hz1, hr14, he]; rfl) (fun _ => ?_) (fun hb => absurd hb (by decide))
    rw [show emC (gOf σ) = 18 by rw [he]; rfl]; exact unpack4_ok hp (.inl rfl) (hU 18)
  · refine WP.ite false (by show s1.zf = _; rw [hz1, hr14, he]; rfl) (fun hb => absurd hb (by decide)) (fun _ => ?_)
    rw [show emC (gOf σ) = 20 by rw [he]; rfl]; exact unpack4_ok hp (.inr rfl) (hU 20)

omit hp in
theorem epi_eq : epi = [.mov .r14 (.mem (at_ .rbx 5120)), .mov .r13 (.mem (at_ .rbx 5112)),
    .mov .r12 (.mem (at_ .rbx 5104)), .mov .rbp (.mem (at_ .rbx 5096)), .mov .rbx (.mem (at_ .rbx 5088))] := rfl

/-- The postcondition, and the callee-saved registers restored. -/
theorem end_ok {s : State} (h : UI σ (emC (gOf σ)) 4 s) :
    WP isa (.block epi) s fun s' => em4K.post σ s' ∧ gprPreserved σ s' := by
  have hin : ∀ i < 5, InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oSave + 8 * i)) 8 := fun i hi =>
    in_scr' hp h.env.rd h.env.wr (by simp only [oSave]; omega_using [hi])
  rw [epi_eq]
  refine WP.mono (WP.keep [.r14, .r13, .r12, .rbp, .rbx] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .r14 = s.mem.readW (at' σ (oSave + 8 * 4)) 64 ∧ s'.gpr .r13 = s.mem.readW (at' σ (oSave + 8 * 3)) 64 ∧
      s'.gpr .r12 = s.mem.readW (at' σ (oSave + 8 * 2)) 64 ∧ s'.gpr .rbp = s.mem.readW (at' σ (oSave + 8 * 1)) 64 ∧
      s'.gpr .rbx = s.mem.readW (at' σ (oSave + 8 * 0)) 64)
    (by
      have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
      have h3 := hin 3 (by decide); have h4 := hin 4 (by decide)
      simp only [oSave, Nat.reduceMul, Nat.reduceAdd] at h0 h1 h2 h3 h4
      xrun [h0, h1, h2, h3, h4, h.env.rbx]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (by decide)) fun s' ⟨⟨hm, h14, h13, h12, hbp, hbx⟩, k⟩ => ?_
  obtain ⟨_, _, hγ⟩ := emC_eq hp.gamma
  refine ⟨fun K hK => polyIs_of_coeffAt fun i hi => ?_, fun r hr => ?_, ?_⟩
  · rw [expandMask_getElem _ hp.gamma hi, hm, h.st K hK i (by omega)]
    simp only [emV]
    congr 3
    rw [← hγ]
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hbx]; exact h.env.saved 0 (by decide)
    · rw [hbp]; exact h.env.saved 1 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.rsp
    · rw [h12]; exact h.env.saved 2 (by decide)
    · rw [h13]; exact h.env.saved 3 (by decide)
    · rw [h14]; exact h.env.saved 4 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.r15
  · rw [hm]
    exact h.env.frame.readW (Region.contains_self _ _) (by
      simpa using ⟨hp.ret_a, hp.ret_scr, Offset.base_disjoint_below (σ.gpr .rsp) (n := 24) (k := 8) (by omega_using [])⟩)
      (by decide)

end

theorem correct {fast : Bool} (σ : State) (hs : em4K.pre σ) :
    ∃ t s', Exec isa (expandMask4Avx2 fast) σ t s' ∧ abiPreserved σ s' ∧ em4K.post σ s' := by
  have hp := pre_of hs
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (start_ok hp) fun _ h₀ =>
    WP.seq (WP.mono (sqs_ok (fast := fast) hp h₀) fun _ h₅ => sel_ok hp h₅ fun _ hu => end_ok hp hu))
  exact ⟨t, s', he, abiPreserved_of_exec (by cases fast <;> decide +kernel) he hF.2, hF.1⟩

end VG.Proof.MlDsa.X86_64.Mask4

end

end

/-!
# ML-DSA on x86-64: `vg_mldsa_expand_mask_poly4_avx2`, constant time

Untrusted: everything here is checked by Lean. Two runs whose pointers and
`γ₁` agree (the declared public data) leak the same. The taint analysis
proves each piece from the pointers (the prologue, the absorption and the
squeezes, from the arguments and then `rbx`; the unpackings, from `rbx`,
`r13` and `rsp`); the two runs take the same branch on `γ₁` (`cmp_ok`), as
their `γ₁` agree.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Mask4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlDsa.X86_64.Sample.Mask4
open VG.Impl.MlKem.X86_64.Sample4 (oRc)
open VG.Proof.MlKem.X86_64
open VG.Proof.MlDsa.X86_64.Sample (emOk gOf)
open VG.Proof.MlDsa.Sample (emC)

/-- Two runs related by `I`, from entry states that agree on what is public. -/
abbrev R (I : State → State → Prop) : State → State → Prop := Rel2 em4K.pre em4K.pub I

theorem env_rbx {σ₁ σ₂ s₁ s₂ : State} (hq : em4K.pub σ₁ σ₂) (e₁ : Env σ₁ s₁) (e₂ : Env σ₂ s₂) :
    s₁.gpr .rbx = s₂.gpr .rbx := by rw [e₁.rbx, e₂.rbx, scr, scr, hq.2.2.2.1]

theorem env_r13 {σ₁ σ₂ s₁ s₂ : State} (hq : em4K.pub σ₁ σ₂) (e₁ : Env σ₁ s₁) (e₂ : Env σ₂ s₂) :
    s₁.gpr .r13 = s₂.gpr .r13 := by rw [e₁.r13, e₂.r13, aP, aP, hq.2.2.1]

theorem env_rsp {σ₁ σ₂ s₁ s₂ : State} (hq : em4K.pub σ₁ σ₂) (e₁ : Env σ₁ s₁) (e₂ : Env σ₂ s₂) :
    s₁.gpr .rsp = s₂.gpr .rsp := by rw [e₁.rsp, e₂.rsp, hq.2.2.2.2]

/-- `squeezes`, given its taint analysis. -/
theorem sq_ct {fast : Bool}
    (c : ∃ hc : VG.Taint.Hint X86_64.Taint.T, (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeezes fast) hc).isSome = true) :
    RelCT isa (R fun σ s => SqInv σ 0 s) (squeezes fast) (R fun σ s => SqInv σ 5 s) := by
  obtain ⟨_, c⟩ := c
  exact relInv (fun σ s hp h => sqs_ok (fast := fast) (pre_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) c)

/-- The branch on `γ₁`'s comparison, and what it keeps. -/
theorem cmp_ok {σ : State} {s : State} (h : SqInv σ 5 s) :
    WP isa (.block [.vop .vzeroupper, .alu32 .cmp .r14 (.imm 0x20000)]) s fun s' =>
      (∀ c, UI σ c 0 s') ∧ s'.zf = some (BitVec.setWidth 32 (σ.gpr .rsi) - 0x20000 == 0) := by
  refine WP.mono (WP.keep [.r14] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r14 = s.gpr .r14 ∧
      s'.zf = some (BitVec.setWidth 32 (s.gpr .r14) - 0x20000 == 0)) (by xrun; exact ⟨rfl, rfl, rfl⟩) (by decide))
    fun s1 ⟨⟨hm1, h14, hz1⟩, k1'⟩ => ⟨fun c => ⟨Env.low h.env (rs := []) (by simp)
      (by rw [hm1]; exact Frame.refl _ _) k1'.2.1 k1'.2.2 fun r _ => by
        by_cases e : r = .r14
        · subst e; exact h14
        · exact k1'.gpr (by simp [e]),
      fun k hk p hp' => by rw [hm1]; exact h.buf k hk p (by omega_using [hp']), fun _ hk => absurd hk (by omega_using [])⟩,
    by rw [hz1, h.env.r14]⟩

/-- The comparison of `γ₁`, as `γ₁ = 2¹⁷`. -/
theorem zf_gamma (σ : State) :
    (BitVec.setWidth 32 (σ.gpr .rsi) - 0x20000 == 0) = decide (gOf σ = 2 ^ 17) := by
  by_cases e : gOf σ = 2 ^ 17
  · rw [show BitVec.setWidth 32 (σ.gpr .rsi) = 0x20000 from BitVec.eq_of_toNat_eq (by rw [← gOf, e]; rfl),
      decide_eq_true e]
    rfl
  · rw [decide_eq_false e, beq_eq_false_iff_ne]
    intro h
    apply e
    rw [gOf, show BitVec.setWidth 32 (σ.gpr .rsi) = 0x20000 by
      rw [← BitVec.sub_add_cancel (BitVec.setWidth 32 (σ.gpr .rsi)) 0x20000, h]; rfl]
    rfl

/-- A piece that takes each run from `I` to `I'`, keeping a fact `C` of the entry states. -/
theorem relInvC {I I' : State → State → Prop} {C : State → Prop} {c : Prog isa}
    (hw : ∀ σ s, em4K.pre σ → I σ s → WP isa c s (I' σ)) (ht : RelCT isa (R I) c fun _ _ => True) :
    RelCT isa (R fun σ s => I σ s ∧ C σ) c (R fun σ s => I' σ s ∧ C σ) :=
  relInv (fun σ s hp hs => WP.mono (hw σ s hp hs.1) fun _ h => ⟨h, hs.2⟩)
    (RelCT.mono ht (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, i₁.1, i₂.1⟩) fun _ _ h => h)

/-- The unpackings for `c`, from states with the same pointers, keeping a fact `C` of the entry states. -/
theorem unpack4_ct {c : Nat} (hc : emOk c) {C : State → Prop} {hh : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx, .r13, .rsp]) (unpack4 c) hh).isSome = true) :
    RelCT isa (R fun σ s => UI σ c 0 s ∧ C σ) (unpack4 c) (R fun σ s => UI σ c 4 s ∧ C σ) :=
  relInvC (fun σ s hp h => unpack4_ok (pre_of hp) hc h)
    (taintRel [.rbx, .r13, .rsp] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [env_rbx hq h₁.env h₂.env, env_r13 hq h₁.env h₂.env, env_rsp hq h₁.env h₂.env]) ht)

theorem gOf_pub {σ₁ σ₂ : State} (hq : em4K.pub σ₁ σ₂) : gOf σ₁ = gOf σ₂ := by rw [gOf, gOf, hq.2.1]

/-- The branch on `γ₁`. -/
theorem sel_ct : RelCT isa (R fun σ s => (∀ c, UI σ c 0 s) ∧
      s.zf = some (BitVec.setWidth 32 (σ.gpr .rsi) - 0x20000 == 0))
    (.ite .e (unpack4 18) (unpack4 20)) (R fun σ s => UI σ (emC (gOf σ)) 4 s) := by
  refine RelCT.ite (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ => by
      show x.zf = y.zf; rw [h₁.2, h₂.2, hq.2.1]) ?_ ?_
  · refine RelCT.mono (unpack4_ct (C := fun σ => emC (gOf σ) = 18) (.inl rfl) (by taint_decide))
      (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩, hb⟩ => ?_)
      fun x y ⟨σ₁, σ₂, p₁, p₂, hq, ⟨u₁, c₁⟩, ⟨u₂, c₂⟩⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, by show UI σ₁ _ 4 x; rw [c₁]; exact u₁,
        by show UI σ₂ _ 4 y; rw [c₂]; exact u₂⟩
    have hb' : x.zf = some true := hb
    rw [h₁.2, zf_gamma, Option.some.injEq, decide_eq_true_iff] at hb'
    exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁.1 18, by rw [hb']; rfl⟩, ⟨h₂.1 18, by rw [← gOf_pub hq, hb']; rfl⟩⟩
  · refine RelCT.mono (unpack4_ct (C := fun σ => emC (gOf σ) = 20) (.inr rfl) (by taint_decide))
      (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩, hb⟩ => ?_)
      fun x y ⟨σ₁, σ₂, p₁, p₂, hq, ⟨u₁, c₁⟩, ⟨u₂, c₂⟩⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, by show UI σ₁ _ 4 x; rw [c₁]; exact u₁,
        by show UI σ₂ _ 4 y; rw [c₂]; exact u₂⟩
    have hb' : x.zf = some false := hb
    rw [h₁.2, zf_gamma, Option.some.injEq, decide_eq_false_iff_not] at hb'
    have e₁ : gOf σ₁ = 2 ^ 19 := (pre_of p₁).gamma.resolve_left hb'
    exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁.1 20, by rw [e₁]; rfl⟩, ⟨h₂.1 20, by rw [← gOf_pub hq, e₁]; rfl⟩⟩

theorem ct {fast : Bool} : ConstantTime isa em4K.pre em4K.pub (expandMask4Avx2 fast) := by
  unfold expandMask4Avx2
  refine relStart (Q := fun _ _ => True) (RelCT.seq (relInv (I' := fun σ s => SqInv σ 0 s)
    (fun σ s hp h => by subst h; exact start_ok (pre_of hp))
    (taintRel [.rdi, .rdx, .rcx, .rsp] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hq.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2]) (by taint_decide))) ?_)
  refine RelCT.seq (sq_ct (fast := fast) (by cases fast <;> exact ⟨_, by taint_decide⟩)) ?_
  refine RelCT.seq (relInv (fun σ s _ h => cmp_ok h) (taintRel [] (fun _ _ _ _ hr => absurd hr List.not_mem_nil)
    (by taint_decide))) (RelCT.seq sel_ct ?_)
  exact taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide)

end VG.Proof.MlDsa.X86_64.Mask4

end

end

/-! ### `MlDsa.X86_64.Sample.M4Scalar`, which only this module used -/

section

/-!
# ML-DSA on x86-64: `vg_mldsa_expand_mask_poly4`

Untrusted: everything here is checked by Lean. The baseline implementation
calls `vg_mldsa_expand_mask_poly` on each seed, between the prologue and the
epilogue of the one for AVX2: after the call on seed `K`, polynomial `K` is
`ExpandMask`'s for the seed (`PC`), as in `vg_mldsa_rej_ntt_poly4`
(`Rej4Scalar.lean`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Mask4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlDsa.X86_64.Sample.Mask4
open VG.Proof.MlKem.X86_64
open VG.Proof.MlDsa.X86_64.Sample (emK gOf expandMask_correct expandMask_ct)
open VG.Proof.MlDsa.Arith (polyIs_frame)
open VG.Spec.MlDsa (H toRq bitUnpack bitlen)
open VG.Proof.MlDsa (PolyIs seed66)
open VG.Spec.Sha3 (bytesAt)

theorem em_nosp : NoSp Impl.MlDsa.X86_64.Sample.expandMask := nosp_of (by decide +kernel)

theorem em_depth : Impl.MlDsa.X86_64.Sample.expandMask.depth = 2 := by decide +kernel

/-- `ExpandMask`'s polynomial for seed `k`. -/
abbrev P (σ : State) (k : Nat) : Spec.MlDsa.Poly :=
  toRq (bitUnpack (H (B σ k) (32 * (1 + bitlen (gOf σ - 1)))) (gOf σ - 1) (gOf σ))

/-- Before the call on seed `K`. -/
structure PC (σ : State) (K : Nat) (s : State) : Prop where
  env : Env σ s
  polys : ∀ k < K, PolyIs s.mem (poly4 (aP σ) k) (P σ k)

/-- The regions of `vg_mldsa_expand_mask_poly`'s call for seed `K`. -/
abbrev cRd (σ : State) (K : Nat) : List Region := [⟨sd σ + BitVec.ofNat 64 (66 * K), 66⟩]
abbrev cWr (σ : State) (K : Nat) : List Region := [pR (poly4 (aP σ) K), ⟨at' σ oScalar, 2048⟩]

section
variable {σ : State} (hp : Pre σ)
include hp

omit hp in
theorem c_sub {K : Nat} (hK : K < 4) : ∀ r ∈ cWr σ K ++ [stkR σ],
    (∃ R ∈ [aR σ, scrR σ, stkR σ], Region.Sub r R) := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl
  · exact ⟨aR σ, by simp, sub_poly hK⟩
  · exact ⟨scrR σ, by simp, sub_scr (by simp only [oScalar]; omega_using [])⟩
  · exact ⟨stkR σ, by simp, fun _ h => h⟩

/-- A region the call writes is apart from `⟨at' σ a, n⟩` in the scratch space below 6144. -/
theorem c_disj {K : Nat} (hK : K < 4) {a n : Nat} (h : a + n ≤ oScalar) :
    ∀ r ∈ cWr σ K ++ [stkR σ], Region.Disjoint ⟨at' σ a, n⟩ r := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl
  · exact (hp.a_scr.symm.sub_left (sub_scr (by simp only [oScalar] at h; omega_using [h]))).sub_right (sub_poly hK)
  · exact Offset.disjoint _ (.inl h) (by simp only [oScalar] at h; omega_using [h]) (by simp only [oScalar]; omega_using [])
  · exact (hp.stk_scr.sub_right (sub_scr (by simp only [oScalar] at h; omega_using [h]))).symm

theorem seed_bytes {K : Nat} (hK : K < 4) {m : Mem} (hf : Frame [aR σ, scrR σ, stkR σ] σ.mem m) :
    bytesAt m (sd σ + BitVec.ofNat 64 (66 * K)) 66 = B σ K := by
  rw [MlKem.bytesAt_frame hf (by simpa using ⟨hp.sd_a.sub_left (Offset.sub_base _ (by omega_using [hK])),
    hp.sd_scr.sub_left (Offset.sub_base _ (by omega_using [hK])), (hp.stk_sd.sub_right (Offset.sub_base _ (by omega_using [hK]))).symm⟩)
    (by decide)]
  rfl

theorem scr6144_lt : (at' σ oScalar).toNat + 2048 ≤ 2 ^ 64 := by
  have := hp.scr_lt
  rw [at', Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (show oScalar < 2 ^ 64 by decide),
    Nat.mod_eq_of_lt (by simp only [oScalar]; omega_using [this])]
  simp only [oScalar]; omega_using [this]

theorem regs {s : State} (he : Env σ s) : s.rd ++ s.wr = [sdR σ, aR σ, scrR σ] := by
  rw [he.rd, he.wr, hp.rd, hp.wr]; rfl

theorem cov {s : State} (he : Env σ s) {K : Nat} (hK : K < 4) :
    Covers (cRd σ K ++ cWr σ K) (s.rd ++ s.wr) ∧ Covers (cWr σ K) s.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · rw [regs hp he]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨sdR σ, by simp, 66 * K, rfl, by simp only; omega_using [hK]⟩
    · exact ⟨aR σ, by simp, 1024 * K, rfl, by simp only; omega_using [hK]⟩
    · exact ⟨scrR σ, by simp, oScalar, rfl, by simp only [oScalar]; omega_using []⟩
  · rw [he.wr, hp.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨aR σ, by simp, 1024 * K, rfl, by simp only; omega_using [hK]⟩
    · exact ⟨scrR σ, by simp, oScalar, rfl, by simp only [oScalar]; omega_using []⟩

/-- `PC` after the call. -/
theorem PC.call {K : Nat} (hK : K < 4) {s s' : State} (h : PC σ K s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .r14, .rsp, .r15], s'.gpr r = s.gpr r)
    (hf : Frame (cWr σ K ++ [stkR σ]) s.mem s'.mem) : PC σ K s' := by
  refine ⟨⟨hrd.trans h.env.rd, hwr.trans h.env.wr, by rw [hg .rbx (by simp), h.env.rbx],
      by rw [hg .r12 (by simp), h.env.r12], by rw [hg .r13 (by simp), h.env.r13], by rw [hg .r14 (by simp), h.env.r14],
      by rw [hg .rsp (by simp), h.env.rsp], by rw [hg .r15 (by simp), h.env.r15], fun i hi => ?_,
      h.env.frame.trans (hf.sub (c_sub (σ := σ) hK))⟩, fun k hk => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (c_disj hp hK (by simp only [oSave, oScalar]; omega_using [hi])) (by decide)]
    exact h.env.saved i hi
  · refine polyIs_frame hf (fun r hr => ?_) (h.polys k hk)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · have hd := Offset.disjoint (aP σ) (d := 1024 * k) (n := 1024) (e := 1024 * K) (k := 1024) (by omega_using [hk]) (by omega_using [hK, hk])
        (by omega_using [hK])
      simpa [poly4] using hd
    · exact (hp.a_scr.sub_left (sub_poly (by omega_using [hK, hk]))).sub_right (sub_scr (by simp only [oScalar]; omega_using []))
    · exact (hp.stk_a.sub_right (sub_poly (by omega_using [hK, hk]))).symm

/-- The arguments of the call on seed `K`. -/
structure ArgI (σ : State) (K : Nat) (s : State) : Prop where
  pinv : PC σ K s
  rdi : s.gpr .rdi = sd σ + BitVec.ofNat 64 (66 * K)
  rsi : s.gpr .rsi = σ.gpr .rsi
  rdx : s.gpr .rdx = poly4 (aP σ) K
  rcx : s.gpr .rcx = at' σ oScalar

omit hp in
theorem sx6144 : BitVec.signExtend 64 (BitVec.ofNat 32 oScalar) = BitVec.ofNat 64 6144 := by decide

omit hp in
theorem argsK_ok {K : Nat} (hK : K < 4) {s : State} (h : PC σ K s) :
    WP isa (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (66 * K))), .mov .rsi (.reg .r14),
      .mov .rdx (.reg .r13), .alu .add .rdx (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rcx (.reg .rbx),
      .alu .add .rcx (.imm (BitVec.ofNat 32 oScalar))]) s (ArgI σ K) :=
  WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rdi = sd σ + BitVec.ofNat 64 (66 * K) ∧ s'.gpr .rsi = σ.gpr .rsi ∧ s'.gpr .rdx = poly4 (aP σ) K ∧
      s'.gpr .rcx = at' σ oScalar)
    (by xrun [h.env.r12, h.env.r13, h.env.r14, h.env.rbx, sx_ofNat (show 66 * K < 2 ^ 31 by omega_using [hK]),
      sx_ofNat (show 1024 * K < 2 ^ 31 by omega_using [hK]), sx6144]; rfl) (by rfl))
    fun _ ⟨⟨hm₂, hdi, hsi, hdx, hcx⟩, k₂⟩ => ⟨⟨h.env.keep hm₂ k₂ (by decide), by rw [hm₂]; exact h.polys⟩,
      hdi, hsi, hdx, hcx⟩

theorem argK_kS {K : Nat} (hK : K < 4) {s : State} (h : ArgI σ K s) :
    (below (s.gpr .rsp) 24).Disjoint ⟨sd σ + BitVec.ofNat 64 (66 * K), 66⟩ := by
  rw [h.pinv.env.rsp]; exact hp.stk_sd.sub_right (Offset.sub_base (sd σ) (d := 66 * K) (n := 66) (by omega_using [hK]))

theorem argK_pre {K : Nat} (hK : K < 4) {s : State} (h : ArgI σ K s) :
    emK.pre (s.callEntry.withRegions (cRd σ K) (cWr σ K)) := by
  have hsp : s.gpr .rsp = σ.gpr .rsp := h.pinv.env.rsp
  have kS := argK_kS hp hK h
  have kA : (below (s.gpr .rsp) 24).Disjoint (pR (poly4 (aP σ) K)) := by
    rw [hsp]; exact hp.stk_a.sub_right (sub_poly (σ := σ) hK)
  have kZ : (below (s.gpr .rsp) 24).Disjoint ⟨at' σ oScalar, 2048⟩ := by
    rw [hsp]; exact hp.stk_scr.sub_right (sub_scr (σ := σ) (a := oScalar) (n := 2048) (by simp only [oScalar]; omega_using []))
  simp only [emK, gOf, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce_gpr' s (by decide : Reg.rdi ≠ .rsp), ce_gpr' s (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s (by decide : Reg.rdx ≠ .rsp), ce_gpr' s (by decide : Reg.rcx ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx]
  exact ⟨trivial, trivial,
    (hp.sd_a.sub_left (Offset.sub_base _ (by omega_using [hK]))).sub_right (sub_poly hK),
    (hp.sd_scr.sub_left (Offset.sub_base _ (by omega_using [hK]))).sub_right (sub_scr (by simp only [oScalar]; omega_using [])),
    (hp.a_scr.sub_left (sub_poly hK)).sub_right (sub_scr (by simp only [oScalar]; omega_using [])),
    ret_disj24 s kS, ret_disj24 s kA, ret_disj24 s kZ, stk_disj24' s kS, stk_disj24' s kA, stk_disj24' s kZ,
    scr6144_lt hp, hp.gamma⟩

theorem callK_ok {K : Nat} (hK : K < 4) {s : State} (h : ArgI σ K s) :
    WP isa (.call "vg_mldsa_expand_mask_poly" Impl.MlDsa.X86_64.Sample.expandMask) s (PC σ (K + 1)) := by
  have hcv := cov hp h.pinv.env hK
  refine WP.call expandMask_correct em_nosp (by rw [em_depth]; decide) (argK_pre hp hK h) hcv.1 hcv.2
    fun s₃ hrd hwr hcs hf _ ⟨s₃', hm₃, _, hpost⟩ => ?_
  rw [em_depth, h.pinv.env.rsp] at hf
  have h₃ : PC σ K s₃ := h.pinv.call hp hK hrd hwr (fun r hr => hcs r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hf
  simp only [emK, gOf, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s (by decide : Reg.rsi ≠ .rsp), ce_gpr' s (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, h.rdx, hm₃,
    ce_bytesAt24 s (n := 66) (by decide) (argK_kS hp hK h), seed_bytes hp hK h.pinv.env.frame] at hpost
  refine ⟨h₃.env, fun k hk => ?_⟩
  by_cases e : k = K
  · subst e; exact hpost
  · exact h₃.polys k (by omega_using [hk, e])

theorem callK_ok' {K : Nat} (hK : K < 4) {s : State} (h : PC σ K s) : WP isa (callK K) s (PC σ (K + 1)) :=
  WP.seq (WP.mono (argsK_ok hK h) fun _ h₂ => callK_ok hp hK h₂)

omit hp in
theorem epi_eq' : epi = [.mov .r14 (.mem (at_ .rbx 5120)), .mov .r13 (.mem (at_ .rbx 5112)),
    .mov .r12 (.mem (at_ .rbx 5104)), .mov .rbp (.mem (at_ .rbx 5096)), .mov .rbx (.mem (at_ .rbx 5088))] := rfl

/-- The postcondition, and the callee-saved registers restored. -/
theorem endS_ok {s : State} (h : PC σ 4 s) :
    WP isa (.block epi) s fun s' => em4K.post σ s' ∧ gprPreserved σ s' := by
  have hin : ∀ i < 5, InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oSave + 8 * i)) 8 := fun i hi =>
    in_scr' hp h.env.rd h.env.wr (by simp only [oSave]; omega_using [hi])
  rw [epi_eq']
  refine WP.mono (WP.keep [.r14, .r13, .r12, .rbp, .rbx] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .r14 = s.mem.readW (at' σ (oSave + 8 * 4)) 64 ∧ s'.gpr .r13 = s.mem.readW (at' σ (oSave + 8 * 3)) 64 ∧
      s'.gpr .r12 = s.mem.readW (at' σ (oSave + 8 * 2)) 64 ∧ s'.gpr .rbp = s.mem.readW (at' σ (oSave + 8 * 1)) 64 ∧
      s'.gpr .rbx = s.mem.readW (at' σ (oSave + 8 * 0)) 64)
    (by
      have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
      have h3 := hin 3 (by decide); have h4 := hin 4 (by decide)
      simp only [oSave, Nat.reduceMul, Nat.reduceAdd] at h0 h1 h2 h3 h4
      xrun [h0, h1, h2, h3, h4, h.env.rbx]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (by decide)) fun s' ⟨⟨hm, h14, h13, h12, hbp, hbx⟩, k⟩ => ?_
  refine ⟨fun K hK => by rw [hm]; exact h.polys K hK, fun r hr => ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hbx]; exact h.env.saved 0 (by decide)
    · rw [hbp]; exact h.env.saved 1 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.rsp
    · rw [h12]; exact h.env.saved 2 (by decide)
    · rw [h13]; exact h.env.saved 3 (by decide)
    · rw [h14]; exact h.env.saved 4 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.r15
  · rw [hm]
    exact h.env.frame.readW (Region.contains_self _ _) (by
      simpa using ⟨hp.ret_a, hp.ret_scr, Offset.base_disjoint_below (σ.gpr .rsp) (n := 24) (k := 8) (by omega_using [])⟩)
      (by decide)

end

theorem correct_scalar (σ : State) (hs : em4K.pre σ) :
    ∃ t s', Exec isa expandMask4 σ t s' ∧ abiPreserved σ s' ∧ em4K.post σ s' := by
  have hp := pre_of hs
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok hp) fun _ h =>
    WP.seq (WP.mono (callK_ok' hp (by decide) (⟨h, fun _ h' => absurd h' (by omega_using [])⟩ : PC σ 0 _)) fun _ p₁ =>
      WP.seq (WP.mono (callK_ok' hp (by decide) p₁) fun _ p₂ => WP.seq (WP.mono (callK_ok' hp (by decide) p₂)
        fun _ p₃ => WP.seq (WP.mono (callK_ok' hp (by decide) p₃) fun _ p₄ => endS_ok hp p₄)))))
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

end VG.Proof.MlDsa.X86_64.Mask4

end

end

/-!
# ML-DSA on x86-64: `vg_mldsa_expand_mask_poly4` and `vg_mldsa_expand_mask_poly4_avx2`, verified

Untrusted: everything here is checked by Lean. The baseline implementation
is constant time as the calls are (`expandMask_ct`, from their pointers and
`γ₁`), and the contract of the proofs (`em4K`) is the shared one of `Spec/`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Mask4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlDsa.X86_64.Sample.Mask4
open VG.Proof.MlKem.X86_64
open VG.Proof.MlDsa.X86_64.Sample (emK gOf expandMask_correct expandMask_ct)

/-- The call on seed `K`. -/
theorem call_ct {K : Nat} (hK : K < 4) :
    RelCT isa (R fun σ s => ArgI σ K s) (.call "vg_mldsa_expand_mask_poly" Impl.MlDsa.X86_64.Sample.expandMask)
      (R fun σ s => PC σ (K + 1) s) :=
  relInv (fun σ s hp h => callK_ok (pre_of hp) hK h) (RelCT.callEx expandMask_correct expandMask_ct
    fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => by
      have hsp : s₁.gpr .rsp = s₂.gpr .rsp := by rw [h₁.pinv.env.rsp, h₂.pinv.env.rsp, hq.2.2.2.2]
      refine ⟨_, _, _, _, argK_pre (pre_of p₁) hK h₁, argK_pre (pre_of p₂) hK h₂, ?_,
        (cov (pre_of p₁) h₁.pinv.env hK).1, (cov (pre_of p₁) h₁.pinv.env hK).2,
        (cov (pre_of p₂) h₂.pinv.env hK).1, (cov (pre_of p₂) h₂.pinv.env hK).2, hsp⟩
      simp only [emK, State.withRegions_gpr, State.callEntry_rsp,
        ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), ce_gpr' _ (by decide : Reg.rcx ≠ .rsp), h₁.rdi, h₂.rdi, h₁.rsi, h₂.rsi,
        h₁.rdx, h₂.rdx, h₁.rcx, h₂.rcx]
      simp only [sd, aP, at', scr, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hsp, and_self])

/-- The call on seed `K`, given the taint analysis of its arguments. -/
theorem callK_ct {K : Nat} (hK : K < 4) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.r12, .r13, .rbx])
      (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (66 * K))), .mov .rsi (.reg .r14),
        .mov .rdx (.reg .r13), .alu .add .rdx (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rcx (.reg .rbx),
        .alu .add .rcx (.imm (BitVec.ofNat 32 oScalar))]) hc).isSome = true) :
    RelCT isa (R fun σ s => PC σ K s) (callK K) (R fun σ s => PC σ (K + 1) s) :=
  RelCT.seq (relInv (fun σ s _ h => argsK_ok hK h) (taintRel [.r12, .r13, .rbx]
      (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.env.r12, h₂.env.r12, sd, sd, hq.1]
        · exact env_r13 hq h₁.env h₂.env
        · exact env_rbx hq h₁.env h₂.env) c))
    (call_ct hK)

theorem ct_scalar : ConstantTime isa em4K.pre em4K.pub expandMask4 := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq (relInv (I' := fun σ s => PC σ 0 s)
    (fun σ s hp h => by
      subst h
      exact WP.mono (pro_ok (pre_of hp)) fun _ h => ⟨h, fun _ h => absurd h (by omega_using [])⟩)
    (taintRel [.rdi, .rdx, .rcx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hq.1, hq.2.2.1, hq.2.2.2.1]) (by taint_decide))) ?_)
  refine RelCT.seq (callK_ct (K := 0) (by decide) (by taint_decide)) (RelCT.seq (callK_ct (K := 1) (by decide)
    (by taint_decide)) (RelCT.seq (callK_ct (K := 2) (by decide) (by taint_decide))
      (RelCT.seq (callK_ct (K := 3) (by decide) (by taint_decide)) ?_)))
  exact taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide)

/-- A state satisfying the precondition. -/
def em4Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x20000 | .rdx => 0x2000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 264⟩]
  wr := [⟨0x2000, 4096⟩, ⟨0x4000, 8192⟩]

theorem em4_verified (c : Prog isa)
    (hc : ∀ σ, em4K.pre σ → ∃ t s', Exec isa c σ t s' ∧ abiPreserved σ s' ∧ em4K.post σ s')
    (ht : ConstantTime isa em4K.pre em4K.pub c) :
    Verified X86_64.target c (Proof.MlDsa.expandMask4Contract X86_64.abi 24) :=
  Verified.of_correct hc ht
    { pre := by sig_implies_pre [Proof.MlDsa.expandMask4Contract, Proof.MlDsa.expandMask4Sig, em4K, X86_64.abi,
        X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Proof.MlDsa.expandMask4Contract, Proof.MlDsa.expandMask4Sig, em4K, X86_64.abi, X86_64.argRegs]
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.MlDsa.expandMask4Contract, Proof.MlDsa.expandMask4Sig, em4K, X86_64.abi, X86_64.argRegs] at h
        obtain ⟨hsp, hdi, hsi, hdx, hcx⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, hsp⟩
      sat := by sig_implies_sat [Proof.MlDsa.expandMask4Contract, Proof.MlDsa.expandMask4Sig, em4K, X86_64.abi,
        X86_64.argRegs] [em4Sat] using em4Sat }

theorem expandMask4Avx2_verified {fast : Bool} : Verified X86_64.target (expandMask4Avx2 fast)
    (Proof.MlDsa.expandMask4Contract X86_64.abi 24) := em4_verified _ (correct (fast := fast)) ct

theorem expandMask4_verified : Verified X86_64.target expandMask4
    (Proof.MlDsa.expandMask4Contract X86_64.abi 24) := em4_verified _ correct_scalar ct_scalar

end VG.Proof.MlDsa.X86_64.Mask4
