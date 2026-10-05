import VerifiedGarbage.Proof.MlKem.X86_64.SampleCT
import VerifiedGarbage.Proof.MlKem.X86_64.AddSub
import VerifiedGarbage.Proof.MlKem.X86_64.Mul
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.X86_64.Cbd
import VerifiedGarbage.Proof.MlKem.X86_64.Encode12
import VerifiedGarbage.Proof.MlKem.X86_64.Decode12
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MlKem.X86_64.MulAvx2
import VerifiedGarbage.Impl.MlKem.X86_64.NttAvx2

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.Ntt`. -/
section

/-!
# ML-KEM on x86-64: `vg_mlkem_ntt`

`withMxcsr` runs its code from any MXCSR and keeps what it does
(`withMxcsr_ok`); the prologue leaves the table of zetas and `f` as words in
`scratch` (`vpro_ok`), each layer is `nttLayer` (`vlay_ok`, `vlay4_ok`,
`vlay2_ok`), and the seven layers are `NTT` (`ntt_eq_layers`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- `vg_mlkem_ntt(f = rdi, scratch = rsi)` and `vg_mlkem_inv_ntt`: `f`
becomes `t f`. -/
def inPlaceK (t : VG.Spec.MlKem.Poly → VG.Spec.MlKem.Poly) : Contract isa where
  pre s :=
    s.rd = [] ∧ s.wr = [pR (s.gpr .rdi), pR (s.gpr .rsi)] ∧ (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧
    (VG.Proof.MlKem.X86_64.retR s).Disjoint (pR (s.gpr .rdi)) ∧ (VG.Proof.MlKem.X86_64.retR s).Disjoint (pR (s.gpr .rsi)) ∧ Reduced s.mem (s.gpr .rdi)
  post s s' := PolyIs s'.mem (s.gpr .rdi) (t (polyAt s.mem (s.gpr .rdi)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-! ## The prologue and the epilogue -/

/-- The table of zetas at `scratch`, `f` as words in `S`, and the constants. -/
theorem vpro_ok {fP sP : Addr} {F : VG.Spec.MlKem.Poly} {s : State} (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hF : PolyIs s.mem fP F) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) (hd : (pR fP).Disjoint (pR sP)) :
    WP isa vpro s fun s' => S16 s'.mem (spW sP) F ∧ T16 s'.mem sP ∧ VConsts s' ∧
      Frame [pR sP] s.mem s'.mem ∧ Keep [.rax, .rcx, .rdx, .r9] s s' := by
  simp only [vpro, List.append_assoc]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (wordTab_ok hsi hw) fun s1 ⟨hT, hf1, k1, _, _⟩ => ?_
  have hsi1 : s1.gpr .rsi = sP := by rw [k1.gpr (by decide), hsi]
  have hdi1 : s1.gpr .rdi = fP := by rw [k1.gpr (by decide), hdi]
  refine WP.mono (Q := fun (s2 : State) => VConsts s2 ∧ s2.gpr .r9 = fP ∧ s2.gpr .rdx = spW sP ∧
      s2.mem = s1.mem ∧ Keep [.rax, .r9, .rdx] s1 s2)
    (by
      simp only [vconsts, leaR, oS]
      vrunm [hsi1, hdi1, sx_ofNat (show 256 < 2 ^ 31 by decide)]
      refine ⟨⟨?_, ?_⟩, ⟨fun r hr => ?_, rfl, rfl⟩⟩
      · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags, xmm_setXmm, ite_true]; decide
      · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags, xmm_setXmm, ite_true, ite_false,
          reduceCtorEq]; decide
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_setXmm, hr, ite_false]) fun s2 ⟨hc, h9, hdx, hm2, k2⟩ => ?_
  have k12 := k1.trans k2
  have hF2 : PolyIs s2.mem fP F := by
    rw [hm2]
    exact polyIs_frame hf1 (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd.sub_right (pR_sub_tab sP)) hF
  have hwf2 : pR fP ∈ s2.rd ++ s2.wr := by rw [k12.2.2]; exact List.mem_append_right _ hwf
  have hw2 : pR sP ∈ s2.wr := by rw [k12.2.2]; exact hw
  refine WP.mono (vpack_ok hc hF2 h9 hdx hwf2 hw2 hd) fun s3 ⟨hS, hf3, hc3, k3, _⟩ =>
    ⟨hS, (hm2 ▸ hT).frame hf3, hc3, ?_, (k12.trans k3).mono (by simp)⟩
  refine (hf1.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
    (hm2 ▸ hf3.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
  · rw [List.mem_singleton.mp hr]; exact pR_sub_tab sP
  · rw [List.mem_singleton.mp hr]; exact pR_sub_S sP

/-- `S` unpacked into `f`. -/
theorem vepi_ok {fP sP : Addr} {F : VG.Spec.MlKem.Poly} {s : State} (hc : VConsts s) (hS : S16 s.mem (spW sP) F)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR fP).Disjoint (pR sP)) :
    WP isa vepi s fun s' => PolyIs s'.mem fP F ∧ Frame [pR fP] s.mem s'.mem ∧ Keep [.rcx, .rdx, .r9] s s' := by
  simp only [vepi]
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .r9 = fP ∧ s1.gpr .rdx = spW sP ∧
      s1.mem = s.mem ∧ s1.xmm = s.xmm ∧ Keep [.r9, .rdx] s s1)
    (by
      simp only [leaR, oS]
      vrunm [hsi, hdi, sx_ofNat (show 256 < 2 ^ 31 by decide)]
      refine ⟨fun r hr => ?_, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h9, hdx, hm, hx, k1⟩ => ?_)
  have hc1 : VConsts s1 := ⟨by rw [hx]; exact hc.q, by rw [hx]; exact hc.qinv⟩
  refine WP.mono (vunpack_ok hc1 (by rw [hm]; exact hS) h9 hdx (by rw [k1.2.2]; exact hwf)
    (by rw [k1.2.2]; exact hw) hd) fun s2 ⟨hP, hf, _, k2, _⟩ =>
      ⟨hP, hm ▸ hf, (k1.trans k2).mono (by decide)⟩

/-! ## The layers -/

/-- Between the layers: `S` holds `F`, and the table and the constants are
in place. -/
structure LI (sP : Addr) (s₀ : State) (F : VG.Spec.MlKem.Poly) (s : State) : Prop where
  S : S16 s.mem (spW sP) F
  T : T16 s.mem sP
  c : VConsts s
  keep : Keep [.rax, .rcx, .rdx, .r8] s₀ s
  frame : Frame [sR (spW sP)] s₀.mem s.mem

/-- A layer, then `c`. -/
theorem LI.seq {sP : Addr} {s₀ : State} (hsi : s₀.gpr .rsi = sP) (hw : pR sP ∈ s₀.wr) {l c : Prog isa}
    {F F' : VG.Spec.MlKem.Poly} {Q : State → Prop}
    (hl : ∀ s, VConsts s → s.gpr .rsi = sP → S16 s.mem (spW sP) F → T16 s.mem sP → pR sP ∈ s.wr →
      WP isa l s fun s' => S16 s'.mem (spW sP) F' ∧ BInv sP s s')
    (hc : ∀ s, VG.Proof.MlKem.X86_64.LI sP s₀ F' s → WP isa c s Q) {s : State} (hI : VG.Proof.MlKem.X86_64.LI sP s₀ F s) :
    WP isa (.seq l c) s Q :=
  WP.seq (WP.mono (hl s hI.c (by rw [hI.keep.gpr (by decide), hsi]) hI.S hI.T (by rw [hI.keep.2.2]; exact hw))
    fun s' ⟨hS, hb⟩ => hc s' ⟨hS, hI.T.frame hb.frame, hb.consts,
      (hI.keep.trans hb.keep).mono (by decide), hI.frame.trans hb.frame⟩)

theorem wAddr_fwd (p : Addr) (a d : Nat) {dz : BitVec 32}
    (h : BitVec.signExtend 64 dz = BitVec.ofNat 64 (2 * d)) :
    wAddr p a + BitVec.signExtend 64 dz = wAddr p (a + d) := by
  rw [h, wAddr_add]

theorem wAddr_bwd (p : Addr) (a d : Nat) {dz : BitVec 32}
    (h : BitVec.ofNat 64 (2 * d) + BitVec.signExtend 64 dz = 0) :
    wAddr p (a + d) + BitVec.signExtend 64 dz = wAddr p a := by
  rw [← wAddr_add, BitVec.add_assoc, h]; exact BitVec.add_zero _

/-- A step of `wAddr` at a zeta index going up by `d`. -/
theorem step_fwd (p : Addr) {zi : Nat → Nat} (d : Nat) {dz : BitVec 32}
    (h : BitVec.signExtend 64 dz = BitVec.ofNat 64 (2 * d)) (hz : ∀ c, zi (c + 1) = zi c + d) (c : Nat) :
    wAddr p (zi c) + BitVec.signExtend 64 dz = wAddr p (zi (c + 1)) := by
  rw [VG.Proof.MlKem.X86_64.wAddr_fwd p _ d h, hz]

/-- A step of `wAddr` at a zeta index going down by `d`. -/
theorem step_bwd (p : Addr) {zi : Nat → Nat} (d : Nat) {dz : BitVec 32}
    (h : BitVec.ofNat 64 (2 * d) + BitVec.signExtend 64 dz = 0) {c : Nat} (hz : zi c = zi (c + 1) + d) :
    wAddr p (zi c) + BitVec.signExtend 64 dz = wAddr p (zi (c + 1)) := by
  rw [hz, VG.Proof.MlKem.X86_64.wAddr_bwd p _ d h]

theorem nttLayer_eq (F : VG.Spec.MlKem.Poly) (len : Nat) :
    nttLayer F len = layF nttBlockN F len (fun c => 128 / len + c) (128 / len) := rfl

/-- A layer of `NTT` with `len ≥ 8`, whose first zeta is `zeta k`. -/
theorem fwdLay_ok {sP : Addr} (len k : Nat) (hlen : len ∈ [8, 16, 32, 64, 128]) (hk : 128 / len = k)
    {F : VG.Spec.MlKem.Poly} (s : State) (hc : VConsts s) (hsi : s.gpr .rsi = sP) (hS : S16 s.mem (spW sP) F)
    (hT : T16 s.mem sP) (hw : pR sP ∈ s.wr) :
    WP isa (vlay vbfly len k 2) s fun s' => S16 s'.mem (spW sP) (nttLayer F len) ∧ BInv sP s s' := by
  rw [VG.Proof.MlKem.X86_64.nttLayer_eq]
  exact vlay_ok vbfly_spec nttBlk_ok hlen 2 (fun c => 128 / len + c) (by rw [hk]; rfl)
    (fun c hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
      rcases hlen with rfl | rfl | rfl | rfl | rfl <;> omega)
    (fun c _ => VG.Proof.MlKem.X86_64.step_fwd (zi := fun c => 128 / len + c) (dz := 2) _ 1 (by decide) (fun _ => by omega) c)
    hc hsi hS hT hw

theorem fwdLay4_ok {sP : Addr} {F : VG.Spec.MlKem.Poly} (s : State) (hc : VConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hT : T16 s.mem sP) (hw : pR sP ∈ s.wr) :
    WP isa (vlay4 vbfly 32 0x50 4) s fun s' => S16 s'.mem (spW sP) (nttLayer F 4) ∧ BInv sP s s' := by
  rw [VG.Proof.MlKem.X86_64.nttLayer_eq, show 128 / 4 = 32 from rfl]
  exact vlay4_ok vbfly_spec nttBlk_ok 32 0x50 4 (fun c => 32 + c) (fun i => 32 + 2 * i) rfl (by decide)
    (by decide) (fun i _ => VG.Proof.MlKem.X86_64.step_fwd (zi := fun i => 32 + 2 * i) (dz := 4) _ 2 (by decide) (fun _ => by omega) i)
    hc hsi hS hT hw

theorem fwdLay2_ok {sP : Addr} {F : VG.Spec.MlKem.Poly} (s : State) (hc : VConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hT : T16 s.mem sP) (hw : pR sP ∈ s.wr) :
    WP isa (vlay2 vbfly 64 0xE4 8) s fun s' => S16 s'.mem (spW sP) (nttLayer F 2) ∧ BInv sP s s' := by
  rw [VG.Proof.MlKem.X86_64.nttLayer_eq, show 128 / 2 = 64 from rfl]
  exact vlay2_ok vbfly_spec nttBlk_ok 64 0xE4 8 (fun c => 64 + c) (fun i => 64 + 4 * i) rfl (by decide)
    (by decide) (fun i _ => VG.Proof.MlKem.X86_64.step_fwd (zi := fun i => 64 + 4 * i) (dz := 8) _ 4 (by decide) (fun _ => by omega) i)
    hc hsi hS hT hw

theorem ntt_correct (s : State) (hs : (VG.Proof.MlKem.X86_64.inPlaceK ntt).pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.ntt s t s' ∧ abiPreserved s s' ∧ (VG.Proof.MlKem.X86_64.inPlaceK ntt).post s s' := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwf : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hW : WP isa Impl.MlKem.X86_64.ntt s fun s' => ∃ s2,
      (PolyIs s2.mem (s.gpr .rdi) (ntt (polyAt s.mem (s.gpr .rdi))) ∧
        Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s2.mem) ∧ Frame [mxR (s.gpr .rsi)] s2.mem s'.mem ∧
      Keep [] s2 s' := by
    unfold Impl.MlKem.X86_64.ntt
    refine withMxcsr_ok (by decide) [.rax, .rcx, .rdx, .r8, .r9] (by decide) rfl hw ?_ fun s1 k1 f1 => ?_
    · decide +kernel
    have hdi1 : s1.gpr .rdi = s.gpr .rdi := k1.gpr (by decide)
    have hsi1 : s1.gpr .rsi = s.gpr .rsi := k1.gpr (by decide)
    have hF1 : PolyIs s1.mem (s.gpr .rdi) (polyAt s.mem (s.gpr .rdi)) :=
      polyIs_frame f1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub _))
        ⟨hs.2.2.2.2.2, rfl⟩
    refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.vpro_ok hdi1 hsi1 hF1 (by rw [k1.2.2]; exact hwf) (by rw [k1.2.2]; exact hw) hd)
      fun s2 ⟨hS, hT, hc, hf2, k2⟩ => ?_)
    have hsi2 : s2.gpr .rsi = s.gpr .rsi := by rw [k2.gpr (by decide), hsi1]
    have hw2 : pR (s.gpr .rsi) ∈ s2.wr := by rw [k2.2.2, k1.2.2]; exact hw
    refine LI.seq hsi2 hw2 (VG.Proof.MlKem.X86_64.fwdLay_ok 128 1 (by decide) (by decide)) ?_ ⟨hS, hT, hc, Keep.refl _ _, Frame.refl _ _⟩
    refine fun _ hI => LI.seq hsi2 hw2 (VG.Proof.MlKem.X86_64.fwdLay_ok 64 2 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (VG.Proof.MlKem.X86_64.fwdLay_ok 32 4 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (VG.Proof.MlKem.X86_64.fwdLay_ok 16 8 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (VG.Proof.MlKem.X86_64.fwdLay_ok 8 16 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 VG.Proof.MlKem.X86_64.fwdLay4_ok ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 VG.Proof.MlKem.X86_64.fwdLay2_ok ?_ hI
    intro s3 hI
    refine WP.mono (VG.Proof.MlKem.X86_64.vepi_ok hI.c hI.S (by rw [hI.keep.gpr (by decide), k2.gpr (by decide), hdi1])
      (by rw [hI.keep.gpr (by decide), hsi2]) (by rw [hI.keep.2.2, k2.2.2, k1.2.2]; exact hwf)
      (by rw [hI.keep.2.2]; exact hw2) hd) fun s4 ⟨hP, hf4, _⟩ => ⟨?_, ?_⟩
    · rw [ntt_eq_layers]
      simp only [nttLens, List.foldl_cons, List.foldl_nil]
      exact hP
    · refine (frame_fs f1 ?_).trans ((frame_fs hf2 ?_).trans ((frame_fs hI.frame ?_).trans (frame_fs hf4 ?_))) <;>
        intro r hr <;> simp only [List.mem_singleton] at hr <;> subst hr
      exacts [.inr (mx_sub _), .inr fun _ h => h, .inr (pR_sub_S _), .inl fun _ h => h]
  obtain ⟨t, s', he, ⟨s2, ⟨hP, hf⟩, hf', -⟩, hk⟩ :=
    WP.keep [.rax, .rcx, .rdx, .r8, .r9, .r11] hW (by decide +kernel)
  refine ⟨t, s', he, abiPreserved_of_ctl (by decide +kernel) he (gprPreserved_of hk (by decide)
    (hf.trans (hf'.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩))
    (by simpa using ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩)), ?_⟩
  · rw [List.mem_singleton.mp hr]; exact mx_sub _
  · exact polyIs_frame hf' (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub _)) hP

theorem ntt_ct : ConstantTime isa (VG.Proof.MlKem.X86_64.inPlaceK ntt).pre (VG.Proof.MlKem.X86_64.inPlaceK ntt).pub Impl.MlKem.X86_64.ntt :=
  VG.Taint.constantTime (A := VG.X86_64.taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2])
    (by taint_decide)

/-- A state satisfying the precondition. -/
def inPlaceSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

theorem ntt_verified :
    Verified X86_64.target Impl.MlKem.X86_64.ntt (Spec.MlKem.nttContract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlKem.X86_64.ntt_correct VG.Proof.MlKem.X86_64.ntt_ct (by
    mlkem_implies [Spec.MlKem.nttContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, VG.Proof.MlKem.X86_64.inPlaceK,
      X86_64.abi, X86_64.argRegs] [inPlaceSat] using VG.Proof.MlKem.X86_64.inPlaceSat)

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.NttInv`. -/
section

/-!
# ML-KEM on x86-64: `vg_mlkem_inv_ntt`

As `vg_mlkem_ntt` (`Ntt.lean`): each layer is `nttInvLayer`, the seven layers
are those of `NTT⁻¹` (`nttInv_eq_layers`), and the last pass multiplies each
coefficient by 3303 (`vscale_ok`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem nttInvLayer_eq (F : VG.Spec.MlKem.Poly) (len : Nat) :
    nttInvLayer F len = layF nttInvBlockN F len (fun c => 256 / len - 1 - c) (128 / len) := rfl

/-- A layer of `NTT⁻¹` with `len ≥ 8`, whose first zeta is `zeta k`. -/
theorem invLay_ok {sP : Addr} (len k : Nat) (hlen : len ∈ [8, 16, 32, 64, 128]) (hk : 256 / len - 1 = k)
    {F : VG.Spec.MlKem.Poly} (s : State) (hc : VConsts s) (hsi : s.gpr .rsi = sP) (hS : S16 s.mem (spW sP) F)
    (hT : T16 s.mem sP) (hw : pR sP ∈ s.wr) :
    WP isa (vlay vibfly len k (-2)) s fun s' => S16 s'.mem (spW sP) (nttInvLayer F len) ∧ BInv sP s s' := by
  have hl : 128 / len ≥ 1 ∧ 256 / len = 2 * (128 / len) ∧ 256 / len ≤ 32 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl | rfl <;> decide
  rw [VG.Proof.MlKem.X86_64.nttInvLayer_eq]
  exact vlay_ok vibfly_spec nttInvBlk_ok hlen (-2) (fun c => 256 / len - 1 - c) (by rw [hk]; rfl)
    (fun c _ => by omega)
    (fun c hc' => VG.Proof.MlKem.X86_64.step_bwd (zi := fun c => 256 / len - 1 - c) (dz := -2) _ 1 (by decide) (by omega))
    hc hsi hS hT hw

theorem invLay4_ok {sP : Addr} {F : VG.Spec.MlKem.Poly} (s : State) (hc : VConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hT : T16 s.mem sP) (hw : pR sP ∈ s.wr) :
    WP isa (vlay4 vibfly 62 0x05 (-4)) s fun s' => S16 s'.mem (spW sP) (nttInvLayer F 4) ∧ BInv sP s s' := by
  rw [VG.Proof.MlKem.X86_64.nttInvLayer_eq, show 256 / 4 - 1 = 63 from rfl, show 128 / 4 = 32 from rfl]
  exact vlay4_ok vibfly_spec nttInvBlk_ok 62 0x05 (-4) (fun c => 63 - c) (fun i => 62 - 2 * i) rfl (by decide)
    (by decide)
    (fun i hi => VG.Proof.MlKem.X86_64.step_bwd (zi := fun i => 62 - 2 * i) (dz := -4) _ 2 (by decide) (by omega))
    hc hsi hS hT hw

theorem invLay2_ok {sP : Addr} {F : VG.Spec.MlKem.Poly} (s : State) (hc : VConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hT : T16 s.mem sP) (hw : pR sP ∈ s.wr) :
    WP isa (vlay2 vibfly 124 0x1B (-8)) s fun s' => S16 s'.mem (spW sP) (nttInvLayer F 2) ∧ BInv sP s s' := by
  rw [VG.Proof.MlKem.X86_64.nttInvLayer_eq, show 256 / 2 - 1 = 127 from rfl, show 128 / 2 = 64 from rfl]
  exact vlay2_ok vibfly_spec nttInvBlk_ok 124 0x1B (-8) (fun c => 127 - c) (fun i => 124 - 4 * i) rfl
    (by decide) (by decide)
    (fun i hi => VG.Proof.MlKem.X86_64.step_bwd (zi := fun i => 124 - 4 * i) (dz := -8) _ 4 (by decide) (by omega))
    hc hsi hS hT hw

theorem nttInv_correct (s : State) (hs : (VG.Proof.MlKem.X86_64.inPlaceK nttInv).pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.nttInv s t s' ∧ abiPreserved s s' ∧ (VG.Proof.MlKem.X86_64.inPlaceK nttInv).post s s' := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwf : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hW : WP isa Impl.MlKem.X86_64.nttInv s fun s' => ∃ s2,
      (PolyIs s2.mem (s.gpr .rdi) (nttInv (polyAt s.mem (s.gpr .rdi))) ∧
        Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s2.mem) ∧ Frame [mxR (s.gpr .rsi)] s2.mem s'.mem ∧
      Keep [] s2 s' := by
    unfold Impl.MlKem.X86_64.nttInv
    refine withMxcsr_ok (by decide) [.rax, .rcx, .rdx, .r8, .r9] (by decide) rfl hw ?_ fun s1 k1 f1 => ?_
    · decide +kernel
    have hdi1 : s1.gpr .rdi = s.gpr .rdi := k1.gpr (by decide)
    have hsi1 : s1.gpr .rsi = s.gpr .rsi := k1.gpr (by decide)
    have hF1 : PolyIs s1.mem (s.gpr .rdi) (polyAt s.mem (s.gpr .rdi)) :=
      polyIs_frame f1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub _))
        ⟨hs.2.2.2.2.2, rfl⟩
    refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.vpro_ok hdi1 hsi1 hF1 (by rw [k1.2.2]; exact hwf) (by rw [k1.2.2]; exact hw) hd)
      fun s2 ⟨hS, hT, hc, hf2, k2⟩ => ?_)
    have hsi2 : s2.gpr .rsi = s.gpr .rsi := by rw [k2.gpr (by decide), hsi1]
    have hw2 : pR (s.gpr .rsi) ∈ s2.wr := by rw [k2.2.2, k1.2.2]; exact hw
    refine LI.seq hsi2 hw2 VG.Proof.MlKem.X86_64.invLay2_ok ?_ ⟨hS, hT, hc, Keep.refl _ _, Frame.refl _ _⟩
    refine fun _ hI => LI.seq hsi2 hw2 VG.Proof.MlKem.X86_64.invLay4_ok ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (VG.Proof.MlKem.X86_64.invLay_ok 8 31 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (VG.Proof.MlKem.X86_64.invLay_ok 16 15 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (VG.Proof.MlKem.X86_64.invLay_ok 32 7 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (VG.Proof.MlKem.X86_64.invLay_ok 64 3 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (VG.Proof.MlKem.X86_64.invLay_ok 128 1 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LI.seq hsi2 hw2 (fun _ hc hsi hS _ hw => vscale_ok hc hsi hS hw) ?_ hI
    intro s3 hI
    refine WP.mono (VG.Proof.MlKem.X86_64.vepi_ok hI.c hI.S (by rw [hI.keep.gpr (by decide), k2.gpr (by decide), hdi1])
      (by rw [hI.keep.gpr (by decide), hsi2]) (by rw [hI.keep.2.2, k2.2.2, k1.2.2]; exact hwf)
      (by rw [hI.keep.2.2]; exact hw2) hd) fun s4 ⟨hP, hf4, _⟩ => ⟨?_, ?_⟩
    · rw [nttInv_eq_layers]
      simp only [nttInvLens, List.foldl_cons, List.foldl_nil]
      exact hP
    · refine (frame_fs f1 ?_).trans ((frame_fs hf2 ?_).trans ((frame_fs hI.frame ?_).trans (frame_fs hf4 ?_))) <;>
        intro r hr <;> simp only [List.mem_singleton] at hr <;> subst hr
      exacts [.inr (mx_sub _), .inr fun _ h => h, .inr (pR_sub_S _), .inl fun _ h => h]
  obtain ⟨t, s', he, ⟨s2, ⟨hP, hf⟩, hf', -⟩, hk⟩ :=
    WP.keep [.rax, .rcx, .rdx, .r8, .r9, .r11] hW (by decide +kernel)
  refine ⟨t, s', he, abiPreserved_of_ctl (by decide +kernel) he (gprPreserved_of hk (by decide)
    (hf.trans (hf'.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩))
    (by simpa using ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩)), ?_⟩
  · rw [List.mem_singleton.mp hr]; exact mx_sub _
  · exact polyIs_frame hf' (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub _)) hP

theorem nttInv_ct : ConstantTime isa (VG.Proof.MlKem.X86_64.inPlaceK nttInv).pre (VG.Proof.MlKem.X86_64.inPlaceK nttInv).pub Impl.MlKem.X86_64.nttInv :=
  VG.Taint.constantTime (A := VG.X86_64.taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2])
    (by taint_decide)

theorem nttInv_verified :
    Verified X86_64.target Impl.MlKem.X86_64.nttInv (Spec.MlKem.nttInvContract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlKem.X86_64.nttInv_correct VG.Proof.MlKem.X86_64.nttInv_ct (by
    mlkem_implies [Spec.MlKem.nttInvContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, VG.Proof.MlKem.X86_64.inPlaceK,
      X86_64.abi, X86_64.argRegs] [inPlaceSat] using VG.Proof.MlKem.X86_64.inPlaceSat)

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.FragCall`. -/
section

/-!
# ML-KEM-768 on x86-64: the calls of the top-level functions

A call, with the moves of its arguments before it (`glueCall_ok`), leaves the
permissions and the callee-saved registers as they were, and changes memory
only within the buffers it writes and the 32 bytes of stack below `rsp`
(`Post`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- What a piece leaves: the permissions and the callee-saved registers,
and memory changed only within `W` and the stack. -/
structure Post (s s' : State) (W : List Region) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame (W ++ [below (s.gpr .rsp) 32]) s.mem s'.mem

theorem Post.rsp {s s' : State} {W : List Region} (h : VG.Proof.MlKem.X86_64.Post s s' W) : s'.gpr .rsp = s.gpr .rsp :=
  h.cs .rsp (by decide)

/-- The registers the moves of arguments write. -/
abbrev argRegs : List Reg := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9]

theorem argRegs_cs : ∀ r ∈ calleeSaved, r ∉ VG.Proof.MlKem.X86_64.argRegs := by decide

/-- The moves of the arguments, then a call of verified code. -/
theorem glueCall_ok {glue : List Instr} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 3) {s : State} {V : State → Prop}
    (hg : WP isa (.block glue) s fun s1 => (V s1 ∧ s1.mem = s.mem) ∧ Keep VG.Proof.MlKem.X86_64.argRegs s s1)
    {rd wr : List Region} (hpre : ∀ s1, V s1 → s1.mem = s.mem → Keep VG.Proof.MlKem.X86_64.argRegs s s1 →
      k.pre (s1.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (.seq (.block glue) (.call n c)) s fun s' => VG.Proof.MlKem.X86_64.Post s s' wr ∧
      ∃ s1, V s1 ∧ s1.mem = s.mem ∧ Keep VG.Proof.MlKem.X86_64.argRegs s s1 ∧ ∃ s₂ : State, s₂.mem = s'.mem ∧
        (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧ k.post (s1.callEntry.withRegions rd wr) s₂ := by
  refine WP.seq (WP.mono hg fun s1 ⟨⟨hV, hm⟩, k1⟩ => ?_)
  refine WP.call hv hsp (by omega) (hpre s1 hV hm k1) (by rw [k1.2.1, k1.2.2]; exact hc)
    (by rw [k1.2.2]; exact hw) fun s' hrd hwr hcs hf _ hpost => ⟨⟨hrd.trans k1.2.1, hwr.trans k1.2.2,
      fun r hr => by rw [hcs r hr, k1.gpr (VG.Proof.MlKem.X86_64.argRegs_cs r hr)], ?_⟩, s1, hV, hm, k1, hpost⟩
  have hsp1 : s1.gpr .rsp = s.gpr .rsp := k1.gpr (by decide)
  rw [hm, hsp1] at hf
  exact Frame.below_mono hf (by omega) (by omega)

/-- The trace of the moves then a call, from two runs where the moves are
the same and the callee's public data agree. -/
theorem glueCall_tr {glue : List Instr} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop} {V : State → State → Prop}
    (hgt : RelCT isa P (.block glue) fun _ _ => True)
    (hg : ∀ x y, P x y → WP isa (.block glue) x (V x) ∧ WP isa (.block glue) y (V y))
    (hP : ∀ x y x1 y1, P x y → V x x1 → V y y1 → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (x1.callEntry.withRegions rd₁ wr₁) ∧ k.pre (y1.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (x1.callEntry.withRegions rd₁ wr₁) (y1.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (x1.rd ++ x1.wr) ∧ Covers wr₁ x1.wr ∧
      Covers (rd₂ ++ wr₂) (y1.rd ++ y1.wr) ∧ Covers wr₂ y1.wr ∧ x1.gpr .rsp = y1.gpr .rsp) :
    RelCT isa P (.seq (.block glue) (.call n c)) fun _ _ => True :=
  RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, P x y ∧ V x x1 ∧ V y y1) hgt hg
      fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩)
    (RelCT.callEx hv hct fun x1 y1 ⟨x, y, hp, h1, h2⟩ => hP x y x1 y1 hp h1 h2)

/-! ## Regions on entry to a callee -/

theorem ce_gpr' (s : State) {r : Reg} (h : r ≠ .rsp) : s.callEntry.gpr r = s.gpr r := State.callEntry_gpr _ h

/-- The return address of a call is apart from a region apart from the stack. -/
theorem ret_disj (s : State) {R : Region} (h : (below (s.gpr .rsp) 32).Disjoint R) :
    (retR s.callEntry).Disjoint R := by
  refine h.sub_left ?_
  simp only [retR, State.callEntry_rsp]
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [show x - (s.gpr .rsp - BitVec.ofNat 64 32) = (x - (s.gpr .rsp - 8)) + 24 by bv_omega, BitVec.toNat_add]
  have : (24 : BitVec 64).toNat = 24 := rfl
  omega

/-- The stack a callee's own calls use (16 bytes below its return address). -/
theorem stk_disj (s : State) {R : Region} (h : (below (s.gpr .rsp) 32).Disjoint R) :
    (below (s.callEntry.gpr .rsp) 16).Disjoint R := by
  refine h.sub_left ?_
  simp only [State.callEntry_rsp]
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [show x - (s.gpr .rsp - BitVec.ofNat 64 32) = (x - (s.gpr .rsp - 8 - BitVec.ofNat 64 16)) + 8 by bv_omega,
    BitVec.toNat_add]
  have : (8 : BitVec 64).toNat = 8 := rfl
  omega

/-- The stack a callee's own calls use, for one that uses 24 bytes below its return address. -/
theorem stk_disj24 (s : State) {R : Region} (h : (below (s.gpr .rsp) 32).Disjoint R) :
    (below (s.callEntry.gpr .rsp) 24).Disjoint R := by
  refine h.sub_left ?_
  simp only [State.callEntry_rsp]
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [show x - (s.gpr .rsp - BitVec.ofNat 64 32) = x - (s.gpr .rsp - 8 - BitVec.ofNat 64 24) by bv_omega]
  omega

/-- `ret_disj` for a caller with 24 bytes of stack. -/
theorem ret_disj24 (s : State) {R : Region} (h : (below (s.gpr .rsp) 24).Disjoint R) :
    (retR s.callEntry).Disjoint R := by
  refine h.sub_left ?_
  simp only [retR, State.callEntry_rsp]
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [show x - (s.gpr .rsp - BitVec.ofNat 64 24) = (x - (s.gpr .rsp - 8)) + 16 by bv_omega, BitVec.toNat_add]
  have : (16 : BitVec 64).toNat = 16 := rfl
  omega

/-- `stk_disj` for a caller with 24 bytes of stack. -/
theorem stk_disj24' (s : State) {R : Region} (h : (below (s.gpr .rsp) 24).Disjoint R) :
    (below (s.callEntry.gpr .rsp) 16).Disjoint R := by
  refine h.sub_left ?_
  simp only [State.callEntry_rsp]
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [show x - (s.gpr .rsp - BitVec.ofNat 64 24) = x - (s.gpr .rsp - 8 - BitVec.ofNat 64 16) by bv_omega]
  omega

theorem k16_24 (s : State) {R : Region} (h : (below (s.gpr .rsp) 24).Disjoint R) : (below (s.gpr .rsp) 16).Disjoint R :=
  h.sub_left (below_sub (by omega) (by omega))

theorem ce_bytesAt24 (s : State) {p : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (h : (below (s.gpr .rsp) 24).Disjoint ⟨p, n⟩) : bytesAt s.callEntry.mem p n = bytesAt s.mem p n :=
  callEntry_bytesAt s hn (VG.Proof.MlKem.X86_64.k16_24 s h)

theorem k16 (s : State) {R : Region} (h : (below (s.gpr .rsp) 32).Disjoint R) : (below (s.gpr .rsp) 16).Disjoint R :=
  h.sub_left (below_sub (by omega) (by omega))

/-- A polynomial apart from the stack reads the same on entry to a callee. -/
theorem ce_polyAt (s : State) {p : Addr} (h : (below (s.gpr .rsp) 32).Disjoint (pR p)) :
    polyAt s.callEntry.mem p = polyAt s.mem p :=
  polyAt_congr fun _ hi => callEntry_bytes s (R := pR p) (VG.Proof.MlKem.X86_64.k16 s h) (by simp) hi

theorem ce_reduced (s : State) {p : Addr} (h : (below (s.gpr .rsp) 32).Disjoint (pR p)) :
    Reduced s.callEntry.mem p ↔ Reduced s.mem p :=
  ⟨reduced_congr fun _ hi => (callEntry_bytes s (R := pR p) (VG.Proof.MlKem.X86_64.k16 s h) (by simp) hi).symm,
    reduced_congr fun _ hi => callEntry_bytes s (R := pR p) (VG.Proof.MlKem.X86_64.k16 s h) (by simp) hi⟩

theorem ce_bytesAt (s : State) {p : Addr} {n : Nat} (hn : n < 2 ^ 64) (h : (below (s.gpr .rsp) 32).Disjoint ⟨p, n⟩) :
    bytesAt s.callEntry.mem p n = bytesAt s.mem p n := callEntry_bytesAt s hn (VG.Proof.MlKem.X86_64.k16 s h)

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.YNtt`. -/
section

/-!
# ML-KEM on x86-64: the NTT and its inverse on AVX2 registers, the pieces

The layers' result coefficient by coefficient (`layF_get`); the table of
zetas, in whatever order (`TZ`); polynomials as words loaded into and stored
from both lanes of a register (`lanes_loadY`, `s16_write2Y`); and the zetas
the loads of `NttAvx2.lean` leave in the lanes of `ymm13` (`yzeta1_ok`,
`yzetaS_ok`, `yzeta8_ok`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## A layer, coefficient by coefficient -/

section
variable {op : Zq → Zq → Zq → Zq × Zq} {blk : VG.Spec.MlKem.Poly → Nat → Nat → Nat → Nat → VG.Spec.MlKem.Poly} (hblk : BlkOk blk op)
include hblk

/-- Each coefficient after the first `b` blocks of the layer with `len`. -/
theorem layF_get (F : VG.Spec.MlKem.Poly) {len : Nat} (hl : 0 < len) (zi : Nat → Nat) {b : Nat} (hb : 2 * len * b ≤ 256)
    {j : Nat} (hj : j < 256) :
    (layF blk F len zi b)[j]! = if j < 2 * len * b then
      (if j % (2 * len) < len then (op F[j]! F[j + len]! (zeta (zi (j / (2 * len))))).1
        else (op F[j - len]! F[j]! (zeta (zi (j / (2 * len))))).2) else F[j]! := by
  induction b generalizing j with
  | zero => rw [ite_eq_right (by bdd_omega)]; rfl
  | succ b ih =>
    have hb' : 2 * len * b + 2 * len ≤ 256 := by rw [Nat.mul_succ] at hb; exact hb
    rw [layF, foldl_range_succ, ← layF,
      hblk.get _ len _ _ len hl (Nat.le_refl _) (by rw [n_eq]; omega) j (by rw [n_eq]; exact hj)]
    have hd : ∀ i, 2 * len * b ≤ i → i < 2 * len * b + 2 * len → i / (2 * len) = b ∧
        i % (2 * len) = i - 2 * len * b := fun i h1 h2 => by
      have e1 : i / (2 * len) = b := by
        apply Nat.div_eq_of_lt_le
        · rw [Nat.mul_comm]; exact h1
        · rw [Nat.succ_mul, Nat.mul_comm b]; exact h2
      refine ⟨e1, ?_⟩
      have := Nat.div_add_mod i (2 * len)
      rw [e1] at this; omega
    by_cases h1 : 2 * len * b ≤ j ∧ j < 2 * len * b + len
    · obtain ⟨d1, d2⟩ := hd j h1.1 (by bdd_omega)
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ih (by bdd_omega) hj, ih (by bdd_omega) (by bdd_omega), d1,
        ite_eq_left_of_eq_true _ _ (eq_true (show j < 2 * len * (b + 1) by rw [Nat.mul_succ]; omega)),
        ite_eq_left_of_eq_true _ _ (eq_true (show j % (2 * len) < len by bdd_omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j < 2 * len * b by bdd_omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j + len < 2 * len * b by bdd_omega))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      by_cases h2 : 2 * len * b + len ≤ j ∧ j < 2 * len * b + len + len
      · obtain ⟨d1, d2⟩ := hd j (by bdd_omega) (by bdd_omega)
        rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ih (by bdd_omega) (by bdd_omega), ih (by bdd_omega) hj, d1,
          ite_eq_left_of_eq_true _ _ (eq_true (show j < 2 * len * (b + 1) by rw [Nat.mul_succ]; omega)),
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j % (2 * len) < len by bdd_omega)),
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j - len < 2 * len * b by bdd_omega)),
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j < 2 * len * b by bdd_omega))]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ih (by bdd_omega) hj]
        by_cases h3 : j < 2 * len * b
        · rw [ite_eq_left_of_eq_true _ _ (eq_true h3),
            ite_eq_left_of_eq_true _ _ (eq_true (show j < 2 * len * (b + 1) by rw [Nat.mul_succ]; omega))]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h3),
            ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j < 2 * len * (b + 1) by rw [Nat.mul_succ]; omega))]

end

/-! ## The table of zetas -/

/-- The 128 words `z k · 2¹⁶ mod q` at `p`. -/
def TZ (m : Mem) (p : Addr) (z : Nat → Zq) : Prop := ∀ k < 128, (wordAt m p k).toNat = (z k).val * 65536 % 3329

/-- Writes to the polynomial's words, 256 bytes above the table, keep it. -/
theorem TZ.frame {m m' : Mem} {p : Addr} {z : Nat → Zq} (h : VG.Proof.MlKem.X86_64.TZ m p z) (hf : Frame [sR (p + BitVec.ofNat 64 256)] m m') :
    VG.Proof.MlKem.X86_64.TZ m' p z := fun k hk => by
  rw [wordAt, hf.readW (r := ⟨p, 256⟩) (Offset.contains_base p (by bdd_omega) (by bdd_omega))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.base_disjoint p (by bdd_omega) (by bdd_omega))
    (by decide)]
  exact h k hk

/-- The zetas that `vpunpcklwd` and `vpshufd` with `o` leave in a lane, from the words at `wAddr zP k`. -/
theorem zeta_lanesZ (o : BitVec 8) {zP : Addr} {k : Nat} {z : Nat → Zq} (hk : ∀ j < 4, k + sel o j < 128) {m : Mem}
    (ht : VG.Proof.MlKem.X86_64.TZ m zP z) :
    ZLanes (shufDwords (XBinOp.eval .punpcklwd (m.readW (wAddr zP k) 128) (m.readW (wAddr zP k) 128)) o)
      (fun i => z (k + sel o (i / 2))) := fun i hi => by
  dsimp only
  have hs := sel_lt o (i / 2)
  have hk' := hk (i / 2) (by bdd_omega)
  rw [word_shufDwords _ _ hi]
  generalize sel o (i / 2) = t at *
  rw [word_punpcklwd _ _ (by bdd_omega), ite_self, show (2 * t + i % 2) / 2 = t by bdd_omega,
    word_readW _ _ (by bdd_omega), wAddr_add]
  exact ht _ hk'

/-! ## Words in both lanes -/

/-- Lane `l` of a 256-bit load of the words of a polynomial. -/
theorem lanes_loadY {m : Mem} {p : Addr} {F : VG.Spec.MlKem.Poly} (h : S16 m p F) {j : Nat} (hj : j + 16 ≤ 256) {l : Nat}
    (hl : l < 2) : VG.Proof.MlKem.X86_64.Lanes (m.readW (wAddr p j + BitVec.ofNat 64 (16 * l)) 128) (fun e => F[j + 8 * l + e]!) := by
  rw [show 16 * l = 2 * (8 * l) by bdd_omega, wAddr_add]
  exact lanes_load h (by bdd_omega)

/-- Word `e` of a 256-bit register, as stored. -/
theorem word_ymm (s : State) (r : XReg) {e : Nat} (he : e < 16) :
    (s.ymm r).extractLsb' (8 * (2 * e)) (8 * 2) = word (s.lane r (e / 8)) (e % 8) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [State.ymm, State.lane, word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    decide_eq_true hj, Bool.true_and]
  by_cases h : e < 8
  · simp only [show 8 * (2 * e) + j < 128 by bdd_omega, ite_true, show e / 8 = 0 by bdd_omega]
    exact congrArg _ (by bdd_omega)
  · simp only [show ¬ 8 * (2 * e) + j < 128 by bdd_omega, ite_false, show e / 8 = 1 by bdd_omega, Nat.one_ne_zero]
    exact congrArg _ (by bdd_omega)

/-- Word `i` after storing `x` (256 bits) at word `j`. -/
theorem wordAt_write256 (m : Mem) (p : Addr) {j : Nat} (hj : j + 16 ≤ 256) (x : BitVec 256) {i : Nat}
    (hi : i < 256) :
    wordAt (m.writeW (wAddr p j) x) p i =
      if j ≤ i ∧ i < j + 16 then x.extractLsb' (8 * (2 * (i - j))) (8 * 2) else wordAt m p i := by
  split
  · rename_i h
    rw [wordAt, show wAddr p i = wAddr p j + BitVec.ofNat 64 (2 * (i - j)) by
      rw [wAddr_add, show j + (i - j) = i by bdd_omega]]
    exact readW_writeW_inside (k := 2 * (i - j)) (n := 2) _ _ _ (by bdd_omega) (by decide)
  · exact Mem.readW_writeW_sep (Offset.sep p (by bdd_omega) (by bdd_omega) (by bdd_omega)) (by decide)

/-- Two registers stored into the words of a polynomial, with the lanes `a` and `b`. -/
theorem s16_write2Y {m : Mem} {p : Addr} {P R : VG.Spec.MlKem.Poly} (hP : S16 m p P) {j j' : Nat}
    (hj : j + 16 ≤ 256) (hj' : j' + 16 ≤ 256) (hsep : j + 16 ≤ j' ∨ j' + 16 ≤ j) {s : State} {x y : XReg}
    {a b : Nat → Zq} (hx : ∀ l < 2, VG.Proof.MlKem.X86_64.Lanes (s.lane x l) (fun e => a (8 * l + e)))
    (hy : ∀ l < 2, VG.Proof.MlKem.X86_64.Lanes (s.lane y l) (fun e => b (8 * l + e)))
    (hR : ∀ i < 256, R[i]! = if j ≤ i ∧ i < j + 16 then a (i - j)
      else if j' ≤ i ∧ i < j' + 16 then b (i - j') else P[i]!) :
    S16 ((m.writeW (wAddr p j) (s.ymm x)).writeW (wAddr p j') (s.ymm y)) p R := fun i hi => by
  rw [VG.Proof.MlKem.X86_64.wordAt_write256 _ _ hj' _ hi, VG.Proof.MlKem.X86_64.wordAt_write256 _ _ hj _ hi, hR i hi]
  by_cases h1 : j' ≤ i ∧ i < j' + 16
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_right_of_eq_false _ _ (eq_false (by bdd_omega)),
      ite_eq_left_of_eq_true _ _ (eq_true h1), VG.Proof.MlKem.X86_64.word_ymm _ _ (by bdd_omega)]
    have := hy ((i - j') / 8) (by bdd_omega) ((i - j') % 8) (Nat.mod_lt _ (by bdd_omega))
    rw [this]; exact congrArg _ (congrArg _ (by bdd_omega))
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
    by_cases h2 : j ≤ i ∧ i < j + 16
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true h2), VG.Proof.MlKem.X86_64.word_ymm _ _ (by bdd_omega)]
      have := hx ((i - j) / 8) (by bdd_omega) ((i - j) % 8) (Nat.mod_lt _ (by bdd_omega))
      rw [this]; exact congrArg _ (congrArg _ (by bdd_omega))
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false h2),
        ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact hP i hi

theorem sR_containsY (p : Addr) {j : Nat} (hj : j + 16 ≤ 256) : (sR p).Contains (wAddr p j) 32 :=
  Offset.contains_base p (by bdd_omega) (by bdd_omega)

theorem frame_write2Y {m m' : Mem} {p : Addr} (hf : Frame [sR p] m m') {j j' : Nat} (hj : j + 16 ≤ 256)
    (hj' : j' + 16 ≤ 256) (x y : BitVec 256) :
    Frame [sR p] m ((m'.writeW (wAddr p j) x).writeW (wAddr p j') y) :=
  (hf.writeW (List.mem_singleton_self _) x (VG.Proof.MlKem.X86_64.sR_containsY p hj)).writeW (List.mem_singleton_self _) y
    (VG.Proof.MlKem.X86_64.sR_containsY p hj')

/-! ## Across lanes -/

/-- `vperm2i128`. -/
theorem yperm_ok {d a b : XReg} {n : BitVec 8} (s : State) :
    WP isa (.block [.vop (.vperm2i128 d a b n)]) s fun s' =>
      (∀ l < 2, s'.lane d l = perm2Lanes (s.lane a) (s.lane b) n l) ∧ YOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun r hr l hl => ?_⟩⟩
  · rw [State.lane_setV256, ifp rfl]; rcases lane01 hl with rfl | rfl <;> rfl
  · rw [State.lane_setV256, ifn (by simpa using hr)]

theorem perm20 (a b : Nat → BitVec 128) {l : Nat} (hl : l < 2) :
    perm2Lanes a b 0x20 l = if l = 0 then a 0 else b 0 := by
  rcases lane01 hl with rfl | rfl <;> rfl

theorem perm31 (a b : Nat → BitVec 128) {l : Nat} (hl : l < 2) :
    perm2Lanes a b 0x31 l = if l = 0 then a 1 else b 1 := by
  rcases lane01 hl with rfl | rfl <;> rfl

theorem q256lo (a b : BitVec 128) {i : Nat} (hi : i < 2) : qword256 (b ++ a) i = qword a i :=
  BitVec.extractLsb'_append_eq_of_add_le (by bdd_omega)

theorem q256hi (a b : BitVec 128) (i : Nat) : qword256 (b ++ a) (2 + i) = qword b i := by
  rw [qword256, BitVec.extractLsb'_append_eq_of_le (by bdd_omega), show 64 * (2 + i) - 128 = 64 * i by bdd_omega]; rfl

theorem lo4 (w x y z : BitVec 64) : (w ++ x ++ y ++ z).extractLsb' 0 128 = y ++ z := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and, Nat.zero_add]
  by_cases h : i < 64
  · simp only [h, ite_true]
  · simp only [h, ite_false, show i - 64 < 64 by bdd_omega, ite_true]

theorem hi4 (w x y z : BitVec 64) : (w ++ x ++ y ++ z).extractLsb' 128 128 = w ++ x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    show ¬ 128 + i < 64 by bdd_omega, ite_false, show ¬ 128 + i - 64 < 64 by bdd_omega]
  by_cases h : i < 64
  · simp only [h, ite_true, show 128 + i - 64 - 64 < 64 by bdd_omega]; exact congrArg _ (by bdd_omega)
  · simp only [h, ite_false, show ¬ 128 + i - 64 - 64 < 64 by bdd_omega]; exact congrArg _ (by bdd_omega)

theorem permD8 (a b : BitVec 128) :
    permQwords (b ++ a) 0xD8 = qword256 (b ++ a) (2 + 1) ++ qword256 (b ++ a) 1 ++
      qword256 (b ++ a) (2 + 0) ++ qword256 (b ++ a) 0 := rfl

/-- `vpermq` with `0xD8`: lane 0 is `punpcklqdq` of the two lanes. -/
theorem permD8_lo (a b : BitVec 128) :
    (permQwords (b ++ a) 0xD8).extractLsb' 0 128 = XBinOp.eval .punpcklqdq a b := by
  rw [VG.Proof.MlKem.X86_64.permD8, VG.Proof.MlKem.X86_64.q256hi, VG.Proof.MlKem.X86_64.q256hi, VG.Proof.MlKem.X86_64.q256lo _ _ (by decide), VG.Proof.MlKem.X86_64.q256lo _ _ (by decide), VG.Proof.MlKem.X86_64.lo4]; rfl

/-- `vpermq` with `0xD8`: lane 1 is `punpckhqdq` of the two lanes. -/
theorem permD8_hi (a b : BitVec 128) :
    (permQwords (b ++ a) 0xD8).extractLsb' 128 128 = XBinOp.eval .punpckhqdq a b := by
  rw [VG.Proof.MlKem.X86_64.permD8, VG.Proof.MlKem.X86_64.q256hi, VG.Proof.MlKem.X86_64.q256hi, VG.Proof.MlKem.X86_64.q256lo _ _ (by decide), VG.Proof.MlKem.X86_64.q256lo _ _ (by decide), VG.Proof.MlKem.X86_64.hi4]; rfl

/-- `vpermq d, r, 0xD8`. -/
theorem ypermq_ok {d r : XReg} (s : State) :
    WP isa (.block [.vop (.vpermq d r 0xD8)]) s fun s' =>
      s'.lane d 0 = XBinOp.eval .punpcklqdq (s.lane r 0) (s.lane r 1) ∧
      s'.lane d 1 = XBinOp.eval .punpckhqdq (s.lane r 0) (s.lane r 1) ∧ YOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun r' hr l hl => ?_⟩⟩
  · rw [State.lane_setV256, ifp rfl, ifp rfl, State.ymm_eq, VG.Proof.MlKem.X86_64.permD8_lo]
  · rw [State.lane_setV256, ifp rfl, ifn (by decide), State.ymm_eq, VG.Proof.MlKem.X86_64.permD8_hi]
  · rw [State.lane_setV256, ifn (by simpa using hr)]

/-! ## The zetas -/

theorem wp_cons_iff {i : Instr} {l : List Instr} {s : State} {Q : State → Prop} :
    WP isa (.block (i :: l)) s Q ↔ WP isa (.block [i]) s fun s1 => WP isa (.block l) s1 Q := by
  rw [← WP.block_append_iff]; rfl

/-- A 128-bit load into both lanes. -/
theorem ybcast_ok {s : State} {p : Reg} {off : Nat} {d : XReg}
    (h : InRegions (s.rd ++ s.wr) (s.gpr p + BitVec.ofNat 64 off) 16) :
    WP isa (.block [.vbroadcasti128 d (VG.Impl.MlKem.X86_64.at_ p off)]) s fun s' =>
      (∀ l < 2, s'.lane d l = s.mem.readW (s.gpr p + BitVec.ofNat 64 off) 128) ∧ YOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, VG.Proof.MlKem.X86_64.ea_at, h, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun r hr l hl => ?_⟩⟩
  · rw [State.lane_setV256, ifp rfl]; rcases lane01 hl with rfl | rfl <;> rfl
  · rw [State.lane_setV256, ifn (by simpa using hr)]

theorem blend0 (a b : BitVec 128) : blendDwords a b (BitVec.extractLsb' 0 4 (0xF0 : BitVec 8)) = a :=
  ext_dword (by simp [blendDwords]) (by simp [blendDwords]) (by simp [blendDwords]) (by simp [blendDwords])

theorem blendF (a b : BitVec 128) : blendDwords a b (BitVec.extractLsb' 4 4 (0xF0 : BitVec 8)) = b :=
  ext_dword (by simp [blendDwords]) (by simp [blendDwords]) (by simp [blendDwords]) (by simp [blendDwords])

/-- `vpblendd d, a, b, 0xF0`: lane 0 of `a` and lane 1 of `b`. -/
theorem yblend_ok {d a b : XReg} (s : State) :
    WP isa (.block [.vop (.vpblendd .l256 d a b 0xF0)]) s fun s' =>
      s'.lane d 0 = s.lane a 0 ∧ s'.lane d 1 = s.lane b 1 ∧ YOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun r hr l hl => ?_⟩⟩
  · rw [State.lane_setV256, ifp rfl, ifp rfl, VG.Proof.MlKem.X86_64.blend0]
  · rw [State.lane_setV256, ifp rfl, ifn (by decide), VG.Proof.MlKem.X86_64.blendF]
  · rw [State.lane_setV256, ifn (by simpa using hr)]

/-- `vzeta 0`'s shuffles (`Ntt.lean`). -/
theorem zsse1_ok (t : State) :
    WP isa (.block [xb .punpcklwd .xmm13 .xmm13, .xop (.pshufd .xmm13 .xmm13 0)]) t fun t' =>
      t'.xmm .xmm13 = shufDwords (XBinOp.eval .punpcklwd (t.xmm .xmm13) (t.xmm .xmm13)) 0 ∧ XOnly [.xmm13] t t' := by
  simp only [xb]
  vrun
  exact ⟨by first | trivial | simp, by xonly⟩

theorem yzeta1_ok {zP : Addr} {k : Nat} {z : Nat → Zq} (hk : k < 128) {s : State} (h8 : s.gpr .r8 = wAddr zP k)
    (hin : InRegions (s.rd ++ s.wr) (wAddr zP k) 16) (ht : VG.Proof.MlKem.X86_64.TZ s.mem zP z) :
    WP isa (.block yzeta1) s fun s' => (∀ l < 2, ZLanes (s'.lane .xmm13 l) (fun _ => z k)) ∧ YOnly [.xmm13] s s' := by
  rw [yzeta1, VG.Proof.MlKem.X86_64.wp_cons_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.ybcast_ok (by rw [h8, add_ofNat_zero]; exact hin)) fun s1 ⟨b1, o1⟩ => ?_
  refine WP.mono (ylanes (by decide) (P := fun l t => t.xmm .xmm13 =
      shufDwords (XBinOp.eval .punpcklwd (s1.lane .xmm13 l) (s1.lane .xmm13 l)) 0)
    fun l _ => VG.Proof.MlKem.X86_64.zsse1_ok (s1.proj l)) fun s2 ⟨l2, o2⟩ => ⟨fun l hl => ?_, (o1.trans o2).mono (by simp)⟩
  have e : s2.lane .xmm13 l = _ := l2 l hl
  rw [e, b1 l hl, h8, add_ofNat_zero]
  intro i hi
  rw [VG.Proof.MlKem.X86_64.zeta_lanesZ 0 (k := k) (fun j _ => by rw [sel_zero]; omega) ht i hi]
  dsimp only; rw [sel_zero, Nat.add_zero]

/-- `yzetaS`'s shuffles in each lane. -/
theorem zsseS_ok (o₀ o₁ : BitVec 8) (t : State) :
    WP isa (.block [xb .punpcklwd .xmm13 .xmm13, .xop (.pshufd .xmm2 .xmm13 o₁), .xop (.pshufd .xmm13 .xmm13 o₀)]) t
      fun t' => (t'.xmm .xmm13 = shufDwords (XBinOp.eval .punpcklwd (t.xmm .xmm13) (t.xmm .xmm13)) o₀ ∧
        t'.xmm .xmm2 = shufDwords (XBinOp.eval .punpcklwd (t.xmm .xmm13) (t.xmm .xmm13)) o₁) ∧
        XOnly [.xmm13, .xmm2] t t' := by
  simp only [xb]
  vrun
  exact ⟨by first | trivial | simp, by xonly⟩

theorem yzetaS_ok (o₀ o₁ : BitVec 8) {zP : Addr} {k : Nat} {z : Nat → Zq} (hk0 : ∀ j < 4, k + sel o₀ j < 128)
    (hk1 : ∀ j < 4, k + sel o₁ j < 128) {s : State} (h8 : s.gpr .r8 = wAddr zP k)
    (hin : InRegions (s.rd ++ s.wr) (wAddr zP k) 16) (ht : VG.Proof.MlKem.X86_64.TZ s.mem zP z) :
    WP isa (.block (yzetaS o₀ o₁)) s fun s' => ZLanes (s'.lane .xmm13 0) (fun i => z (k + sel o₀ (i / 2))) ∧
      ZLanes (s'.lane .xmm13 1) (fun i => z (k + sel o₁ (i / 2))) ∧ YOnly [.xmm13, .xmm2] s s' := by
  rw [yzetaS, WP.block_append_iff, VG.Proof.MlKem.X86_64.wp_cons_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.ybcast_ok (by rw [h8, add_ofNat_zero]; exact hin)) fun s1 ⟨b1, o1⟩ => ?_
  refine WP.mono (ylanes (by rfl) (P := fun l t =>
      t.xmm .xmm13 = shufDwords (XBinOp.eval .punpcklwd (s1.lane .xmm13 l) (s1.lane .xmm13 l)) o₀ ∧
      t.xmm .xmm2 = shufDwords (XBinOp.eval .punpcklwd (s1.lane .xmm13 l) (s1.lane .xmm13 l)) o₁)
    fun l _ => VG.Proof.MlKem.X86_64.zsseS_ok o₀ o₁ (s1.proj l)) fun s2 ⟨l2, o2⟩ => ?_
  refine WP.mono (VG.Proof.MlKem.X86_64.yblend_ok s2) fun s3 ⟨e0, e1, o3⟩ => ⟨?_, ?_, ((o1.trans o2).trans o3).mono (by simp)⟩
  · have e : s2.lane .xmm13 0 = _ := (l2 0 (by decide)).1
    rw [e0, e, b1 0 (by decide), h8, add_ofNat_zero]
    exact VG.Proof.MlKem.X86_64.zeta_lanesZ o₀ hk0 ht
  · have e : s2.lane .xmm2 1 = _ := (l2 1 (by decide)).2
    rw [e1, e, b1 1 (by decide), h8, add_ofNat_zero]
    exact VG.Proof.MlKem.X86_64.zeta_lanesZ o₁ hk1 ht

/-- `yzeta8`'s shuffles in each lane. -/
theorem zsse8_ok (t : State) :
    WP isa (.block [xmov .xmm1 .xmm2, xb .punpcklwd .xmm1 .xmm2, xb .punpckhwd .xmm2 .xmm2, xmov .xmm13 .xmm1,
      xb .punpcklqdq .xmm13 .xmm2, xb .punpckhqdq .xmm1 .xmm2]) t
      fun t' => (t'.xmm .xmm13 = XBinOp.eval .punpcklqdq (XBinOp.eval .punpcklwd (t.xmm .xmm2) (t.xmm .xmm2))
          (XBinOp.eval .punpckhwd (t.xmm .xmm2) (t.xmm .xmm2)) ∧
        t'.xmm .xmm1 = XBinOp.eval .punpckhqdq (XBinOp.eval .punpcklwd (t.xmm .xmm2) (t.xmm .xmm2))
          (XBinOp.eval .punpckhwd (t.xmm .xmm2) (t.xmm .xmm2))) ∧
        XOnly [.xmm1, .xmm2, .xmm13] t t' := by
  simp only [xb, xmov]
  vrun [eval_movdqa]
  exact ⟨by first | trivial | simp, by xonly⟩

/-- The word `yzeta8` leaves at `i` of lane `l`, of the eight loaded words `x`. -/
theorem word_z8 (x : BitVec 128) {l i : Nat} (hl : l < 2) (hi : i < 8) :
    word ((if l = 0 then XBinOp.eval .punpcklqdq else XBinOp.eval .punpckhqdq)
      (XBinOp.eval .punpcklwd x x) (XBinOp.eval .punpckhwd x x)) i = word x (2 * l + i / 2 + 2 * (i / 4)) := by
  rcases lane01 hl with rfl | rfl
  · simp only [ite_true]
    rw [word_punpcklqdq _ _ hi]
    split
    · rw [word_punpcklwd _ _ (by bdd_omega), ite_self]; congr 1; omega
    · rw [word_punpckhwd _ _ (by bdd_omega), ite_self]; congr 1; omega
  · simp only [Nat.one_ne_zero, ite_false]
    rw [word_punpckhqdq _ _ hi]
    split
    · rw [word_punpcklwd _ _ (by bdd_omega), ite_self]; congr 1; omega
    · rw [word_punpckhwd _ _ (by bdd_omega), ite_self]; congr 1; omega

theorem yzeta8_ok {zP : Addr} {k : Nat} {z : Nat → Zq} (hk : k + 8 ≤ 128) {s : State} (h8 : s.gpr .r8 = wAddr zP k)
    (hin : InRegions (s.rd ++ s.wr) (wAddr zP k) 16) (ht : VG.Proof.MlKem.X86_64.TZ s.mem zP z) :
    WP isa (.block yzeta8) s fun s' =>
      (∀ l < 2, ZLanes (s'.lane .xmm13 l) (fun i => z (k + (2 * l + i / 2 + 2 * (i / 4))))) ∧
        YOnly [.xmm2, .xmm1, .xmm13] s s' := by
  rw [yzeta8, WP.block_append_iff, VG.Proof.MlKem.X86_64.wp_cons_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.ybcast_ok (by rw [h8, add_ofNat_zero]; exact hin)) fun s1 ⟨b1, o1⟩ => ?_
  refine WP.mono (ylanes (by decide) (P := fun l t =>
      t.xmm .xmm13 = XBinOp.eval .punpcklqdq (XBinOp.eval .punpcklwd (s1.lane .xmm2 l) (s1.lane .xmm2 l))
          (XBinOp.eval .punpckhwd (s1.lane .xmm2 l) (s1.lane .xmm2 l)) ∧
        t.xmm .xmm1 = XBinOp.eval .punpckhqdq (XBinOp.eval .punpcklwd (s1.lane .xmm2 l) (s1.lane .xmm2 l))
          (XBinOp.eval .punpckhwd (s1.lane .xmm2 l) (s1.lane .xmm2 l)))
    fun l _ => VG.Proof.MlKem.X86_64.zsse8_ok (s1.proj l)) fun s2 ⟨l2, o2⟩ => ?_
  refine WP.mono (VG.Proof.MlKem.X86_64.yblend_ok s2) fun s3 ⟨e0, e1, o3⟩ => ⟨fun l hl i hi => ?_, ((o1.trans o2).trans o3).mono (by simp)⟩
  have hx : s1.lane .xmm2 l = s.mem.readW (wAddr zP k) 128 := by rw [b1 l hl, h8, add_ofNat_zero]
  have hw : s3.lane .xmm13 l = (if l = 0 then XBinOp.eval .punpcklqdq else XBinOp.eval .punpckhqdq)
      (XBinOp.eval .punpcklwd (s.mem.readW (wAddr zP k) 128) (s.mem.readW (wAddr zP k) 128))
      (XBinOp.eval .punpckhwd (s.mem.readW (wAddr zP k) 128) (s.mem.readW (wAddr zP k) 128)) := by
    rcases lane01 hl with rfl | rfl
    · rw [e0, ← hx]; exact (l2 0 (by decide)).1
    · rw [e1, ← hx]; exact (l2 1 (by decide)).2
  rw [hw, VG.Proof.MlKem.X86_64.word_z8 _ hl hi, word_readW _ _ (by bdd_omega), wAddr_add]
  exact ht _ (by bdd_omega)

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.YNttLay`. -/
section

/-!
# ML-KEM on x86-64: the layers of the NTT and its inverse with `len ≥ 8` on AVX2 registers

For any butterfly code `bf` that does what `op` does to the words of two SSE
registers (`VBflyOk`) and whose AVX2 form does it in each lane (`laneSseBlock
(toY bf) = some bf`), and any block of the specification whose butterflies do
`op` (`BlkOk`): sixteen butterflies of a block (`ystep`), the `len / 16` of
them of a block (`yblock_ok`), and the `128 / len` blocks of a layer with `len
≥ 16` (`ylay_ok`); and the layer with `len = 8`, two blocks at a time
(`ylay8_ok`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- The facts a piece of a layer keeps. -/
structure BInvY (sP : Addr) (s₀ s : State) : Prop where
  keep : Keep [.r8, .rcx, .rdx, .rax] s₀ s
  frame : Frame [sR (spW sP)] s₀.mem s.mem
  consts : YConsts s
  mxcsr : s.mxcsr = s₀.mxcsr

theorem BInvY.trans {sP : Addr} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.MlKem.X86_64.BInvY sP s₁ s₂) (h₂ : VG.Proof.MlKem.X86_64.BInvY sP s₂ s₃) : VG.Proof.MlKem.X86_64.BInvY sP s₁ s₃ :=
  ⟨(h₁.keep.trans h₂.keep).mono (by simp), h₁.frame.trans h₂.frame, h₂.consts, h₂.mxcsr.trans h₁.mxcsr⟩

theorem sp_inY {rs : List Region} {sP : Addr} (hw : pR sP ∈ rs) {j : Nat} (hj : j + 16 ≤ 256) :
    InRegions rs (wAddr (spW sP) j) 32 := by
  refine ⟨_, hw, ?_⟩
  rw [wAddr, spW, Offset.add_add]
  exact Offset.contains_base sP (by bdd_omega) (by bdd_omega)

theorem lane_gpr {s s' : State} (h : ∀ r l, s'.lane r l = s.lane r l) {rs : List XReg} {s₀ : State}
    (o : YOnly rs s₀ s) {r : XReg} (hr : r ∉ rs) {l : Nat} (hl : l < 2) : s'.lane r l = s₀.lane r l := by
  rw [h, o.lane r hr l hl]

/-- `GOnly` keeps the lanes of the vector registers if it keeps their upper halves. -/
theorem GOnly.lane {rs : List Reg} {s s' : State} (h : GOnly rs s s') (hy : s'.ymmHi = s.ymmHi) (r : XReg) (l : Nat) :
    s'.lane r l = s.lane r l := by
  simp only [State.lane]; rw [h.xmm, hy]

theorem Lanes.congr {x : BitVec 128} {f g : Nat → Zq} (h : VG.Proof.MlKem.X86_64.Lanes x f) (e : ∀ i < 8, f i = g i) : VG.Proof.MlKem.X86_64.Lanes x g :=
  fun i hi => by rw [h i hi, e i hi]

theorem ZLanes.congr {x : BitVec 128} {f g : Nat → Zq} (h : ZLanes x f) (e : ∀ i < 8, f i = g i) : ZLanes x g :=
  fun i hi => by rw [h i hi, e i hi]

/-- `add r, v`. -/
theorem addR_ok (r : Reg) (v : BitVec 32) (s : State) :
    WP isa (.block [.alu .add r (.imm v)]) s fun s' =>
      s'.gpr r = s.gpr r + BitVec.signExtend 64 v ∧ GOnly [r] s s' ∧ s'.ymmHi = s.ymmHi := by
  vrunm [RegUpd.ymmHi_setReg]
  exact ⟨by gonly, rfl⟩

theorem sel_55 {j : Nat} (hj : j < 4) : sel 0x55 j = 1 := by
  rcases (by bdd_omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} (hbf : VBflyOk bf op)
  (hY : laneSseBlock (toY bf) = some bf)
  {blk : VG.Spec.MlKem.Poly → Nat → Nat → Nat → Nat → VG.Spec.MlKem.Poly} (hblk : BlkOk blk op)
include hbf hY

/-- The butterflies of `bf` in each lane, from the words `x` and `y` of the
lanes of `ymm0` and `ymm1` and the zetas `ζ` of those of `ymm13`. -/
theorem ybf_ok {s : State} (hc : YConsts s) {x y ζ : Nat → Nat → Zq} (hx : ∀ l < 2, VG.Proof.MlKem.X86_64.Lanes (s.lane .xmm0 l) (x l))
    (hy : ∀ l < 2, VG.Proof.MlKem.X86_64.Lanes (s.lane .xmm1 l) (y l)) (hz : ∀ l < 2, ZLanes (s.lane .xmm13 l) (ζ l)) :
    WP isa (.block (toY bf)) s fun s' =>
      (∀ l < 2, VG.Proof.MlKem.X86_64.Lanes (s'.lane .xmm0 l) (fun i => (op (x l i) (y l i) (ζ l i)).1) ∧
        VG.Proof.MlKem.X86_64.Lanes (s'.lane .xmm3 l) (fun i => (op (x l i) (y l i) (ζ l i)).2)) ∧
      YOnly [.xmm1, .xmm2, .xmm0, .xmm3] s s' :=
  ylanes hY (P := fun l t => VG.Proof.MlKem.X86_64.Lanes (t.xmm .xmm0) (fun i => (op (x l i) (y l i) (ζ l i)).1) ∧
      VG.Proof.MlKem.X86_64.Lanes (t.xmm .xmm3) (fun i => (op (x l i) (y l i) (ζ l i)).2))
    fun l hl => WP.mono (hbf _ (hc l hl) _ _ _ (hx l hl) (hy l hl) (hz l hl)) fun _ ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩

include hblk

/-- The body of the loop over the vectors of a block. -/
abbrev ybody (bf : List Instr) (len : Nat) : List Instr :=
  ([.vmovdquLoad .l256 .xmm0 (VG.Impl.MlKem.X86_64.at_ .rdx 0), .vmovdquLoad .l256 .xmm1 (VG.Impl.MlKem.X86_64.at_ .rdx (2 * len))] : List Instr) ++ toY bf ++
    ([.vmovdquStore .l256 (VG.Impl.MlKem.X86_64.at_ .rdx 0) .xmm0, .vmovdquStore .l256 (VG.Impl.MlKem.X86_64.at_ .rdx (2 * len)) .xmm3,
      .alu .add .rdx (.imm 32)] : List Instr) ++ ([.alu .sub .rcx (.imm 1)] : List Instr)

theorem ystep {Sp : Addr} {len st u k : Nat} (hl : 16 ≤ len) (hl' : len ≤ 128) (hs : st + 2 * len ≤ 256)
    (hu : 16 * u + 16 ≤ len) {G : VG.Spec.MlKem.Poly} {s : State} (hc : YConsts s)
    (hz : ∀ l < 2, ZLanes (s.lane .xmm13 l) (fun _ => zeta k))
    (hdx : s.gpr .rdx = wAddr Sp (st + 16 * u)) (hS : S16 s.mem Sp (blk G len k st (16 * u)))
    (hin : ∀ j, j + 16 ≤ 256 → InRegions s.wr (wAddr Sp j) 32) :
    WP isa (.block (VG.Proof.MlKem.X86_64.ybody bf len)) s fun s' =>
      S16 s'.mem Sp (blk G len k st (16 * (u + 1))) ∧ s'.gpr .rdx = wAddr Sp (st + 16 * (u + 1)) ∧
        Frame [sR Sp] s.mem s'.mem ∧ YConsts s' ∧ (∀ l < 2, s'.lane .xmm13 l = s.lane .xmm13 l) ∧
        Keep [.rdx, .rcx] s s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧
        s'.mxcsr = s.mxcsr := by
  have j0 : st + 16 * u + 16 ≤ 256 := by bdd_omega
  have j1 : st + 16 * u + len + 16 ≤ 256 := by bdd_omega
  have a1 : wAddr Sp (st + 16 * u) + BitVec.ofNat 64 (2 * len) = wAddr Sp (st + 16 * u + len) := wAddr_add _ _ _
  have r0 : InRegions (s.rd ++ s.wr) (wAddr Sp (st + 16 * u) + BitVec.ofNat 64 0) 32 := by
    obtain ⟨r, hr, hc⟩ := hin _ j0; exact ⟨r, List.mem_append_right _ hr, by rw [add_ofNat_zero]; exact hc⟩
  have r1 : InRegions (s.rd ++ s.wr) (wAddr Sp (st + 16 * u) + BitVec.ofNat 64 (2 * len)) 32 := by
    obtain ⟨r, hr, hc⟩ := hin _ j1; exact ⟨r, List.mem_append_right _ hr, by rw [a1]; exact hc⟩
  rw [VG.Proof.MlKem.X86_64.ybody, List.append_assoc, List.append_assoc, WP.block_append_iff,
    show ∀ a b : Instr, [a, b] = [a] ++ [b] from fun _ _ => rfl, WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [hdx]; exact r0)) fun s1 ⟨L1, o1⟩ => ?_
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr, hdx]; exact r1)) fun s2 ⟨L2, o2⟩ => ?_
  rw [WP.block_append_iff]
  have o12 := o1.trans o2
  generalize hP : blk G len k st (16 * u) = P at hS
  refine WP.mono (VG.Proof.MlKem.X86_64.ybf_ok hbf hY (o12.consts hc (by decide) (by decide))
    (x := fun l e => P[st + 16 * u + 8 * l + e]!) (y := fun l e => P[st + 16 * u + len + 8 * l + e]!)
    (ζ := fun _ _ => zeta k)
    (fun l hl => by
      rw [o2.lane _ (by decide) l hl, L1 l hl, hdx, add_ofNat_zero]; exact VG.Proof.MlKem.X86_64.lanes_loadY hS j0 hl)
    (fun l hl => by
      rw [L2 l hl, o1.gpr, o1.mem, hdx, a1]; exact VG.Proof.MlKem.X86_64.lanes_loadY hS j1 hl)
    (fun l hl => by rw [o12.lane _ (by decide) l hl]; exact hz l hl)) fun s3 ⟨B3, o3⟩ => ?_
  have o13 := o12.trans o3
  have w0 : InRegions s3.wr (s3.gpr .rdx) 32 := by rw [o13.wr, o13.gpr, hdx]; exact hin _ j0
  have w1 : InRegions s3.wr (s3.gpr .rdx + BitVec.ofNat 64 (2 * len)) 32 := by
    rw [o13.wr, o13.gpr, hdx, a1]; exact hin _ j1
  vrunm [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd, State.setMem_ymm,
    State.setMem_setMem, w0, w1, sx32]
  have g3 : s3.gpr .rdx = wAddr Sp (st + 16 * u) := by rw [o13.gpr, hdx]
  rw [g3, a1, o13.mem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · refine VG.Proof.MlKem.X86_64.s16_write2Y (s := s3) hS j0 j1 (by bdd_omega)
      (a := fun e => (op P[st + 16 * u + e]! P[st + 16 * u + len + e]! (zeta k)).1)
      (b := fun e => (op P[st + 16 * u + e]! P[st + 16 * u + len + e]! (zeta k)).2)
      (fun l hl i hi => by
        rw [(B3 l hl).1 i hi]; dsimp only
        rw [show st + 16 * u + 8 * l + i = st + 16 * u + (8 * l + i) by bdd_omega,
          show st + 16 * u + len + 8 * l + i = st + 16 * u + len + (8 * l + i) by bdd_omega])
      (fun l hl i hi => by
        rw [(B3 l hl).2 i hi]; dsimp only
        rw [show st + 16 * u + 8 * l + i = st + 16 * u + (8 * l + i) by bdd_omega,
          show st + 16 * u + len + 8 * l + i = st + 16 * u + len + (8 * l + i) by bdd_omega]) fun i hi => ?_
    rw [← hP, show 16 * (u + 1) = 16 * u + 16 by bdd_omega, hblk.add, hblk.get _ _ _ _ _ (by bdd_omega) (by bdd_omega)
      (by rw [n_eq]; omega) _ (by rw [n_eq]; exact hi)]
    rw [hP]
    by_cases c1 : st + 16 * u ≤ i ∧ i < st + 16 * u + 16
    · rw [ite_eq_left_of_eq_true _ _ (eq_true c1), ite_eq_left_of_eq_true _ _ (eq_true c1),
        show st + 16 * u + (i - (st + 16 * u)) = i by bdd_omega,
        show st + 16 * u + len + (i - (st + 16 * u)) = i + len by bdd_omega]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false c1), ite_eq_right_of_eq_false _ _ (eq_false c1)]
      by_cases c2 : st + 16 * u + len ≤ i ∧ i < st + 16 * u + len + 16
      · rw [ite_eq_left_of_eq_true _ _ (eq_true c2), ite_eq_left_of_eq_true _ _ (eq_true (by bdd_omega)),
          show st + 16 * u + (i - (st + 16 * u + len)) = i - len by bdd_omega,
          show st + 16 * u + len + (i - (st + 16 * u + len)) = i by bdd_omega]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false c2), ite_eq_right_of_eq_false _ _ (eq_false (by bdd_omega))]
  · rw [show (32 : BitVec 64) = BitVec.ofNat 64 (2 * 16) from rfl, wAddr_add,
      show st + 16 * u + 16 = st + 16 * (u + 1) by bdd_omega]
  · exact VG.Proof.MlKem.X86_64.frame_write2Y (Frame.refl _ _) j0 j1 _ _
  · exact lanes_gpr (s := s3) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o13 hc
      (by decide) (by decide)
  · intro l hl; simp only [lane_setReg, lane_setFlags, State.setMem_lane]; exact o13.lane _ (by decide) l hl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false, State.setMem_gpr]
    rw [o13.gpr]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o13.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o13.wr]
  · rw [o13.gpr]
  · rw [o13.gpr]
  · exact o13.mxcsr

/-- The code of a block of a layer with `len ≥ 16`. -/
abbrev yblk (bf : List Instr) (len : Nat) : Prog isa :=
  .seq (.block (yzeta1 ++ ([.alu .add .r8 (.imm 2)] : List Instr)))
    (.seq (rcxLoop (len / 16) (([.vmovdquLoad .l256 .xmm0 (VG.Impl.MlKem.X86_64.at_ .rdx 0),
        .vmovdquLoad .l256 .xmm1 (VG.Impl.MlKem.X86_64.at_ .rdx (2 * len))] : List Instr) ++ toY bf ++
        ([.vmovdquStore .l256 (VG.Impl.MlKem.X86_64.at_ .rdx 0) .xmm0, .vmovdquStore .l256 (VG.Impl.MlKem.X86_64.at_ .rdx (2 * len)) .xmm3,
          .alu .add .rdx (.imm 32)] : List Instr)))
      (.block [.alu .add .rdx (.imm (BitVec.ofNat 32 (2 * len))), .alu .sub .rax (.imm 1)]))

theorem yblock_ok {sP : Addr} {len st kz k : Nat} (h16 : 16 ≤ len) (hl16 : len % 16 = 0) (hl : len ≤ 128)
    (hs : st + 2 * len ≤ 256) (hkz : kz < 128) {z : Nat → Zq} (hzk : z kz = zeta k) {G : VG.Spec.MlKem.Poly} {s : State}
    (hc : YConsts s) (hdx : s.gpr .rdx = wAddr (spW sP) st) (h8r : s.gpr .r8 = wAddr sP kz)
    (hS : S16 s.mem (spW sP) G) (hT : VG.Proof.MlKem.X86_64.TZ s.mem sP z) (hw : pR sP ∈ s.wr) :
    WP isa (VG.Proof.MlKem.X86_64.yblk bf len) s fun s' => S16 s'.mem (spW sP) (blk G len k st len) ∧
      s'.gpr .rdx = wAddr (spW sP) (st + 2 * len) ∧ s'.gpr .r8 = wAddr sP (kz + 1) ∧
      s'.gpr .rax = s.gpr .rax - 1 ∧ s'.zf = some (s.gpr .rax - 1 == 0) ∧ VG.Proof.MlKem.X86_64.BInvY sP s s' := by
  -- the zeta
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.yzeta1_ok hkz h8r (tab_in (List.mem_append_right _ hw) (by bdd_omega)) hT) fun s1 ⟨z1, o1⟩ => ?_
  have g1 : s1.gpr = s.gpr := o1.gpr
  refine WP.mono (Q := fun (s2 : State) => s2.gpr .r8 = wAddr sP (kz + 1) ∧ GOnly [.r8] s1 s2 ∧ s2.ymmHi = s1.ymmHi)
    (by
      vrunm [g1, h8r, RegUpd.ymmHi_setReg]
      refine ⟨?_, by gonly, rfl⟩
      rw [show BitVec.signExtend 64 (2 : BitVec 32) = BitVec.ofNat 64 (2 * 1) from rfl, wAddr_add])
    fun s2 ⟨h82, o2, y2⟩ => ?_
  have l2 := GOnly.lane o2 y2
  have c2 : YConsts s2 := lanes_gpr (s := s1) l2 o1 hc (by decide) (by decide)
  have z2 : ∀ l < 2, ZLanes (s2.lane .xmm13 l) (fun _ => zeta k) := fun l hl => by
    rw [l2]; intro i hi; rw [z1 l hl i hi, hzk]
  have dx2 : s2.gpr .rdx = wAddr (spW sP) st := by rw [o2.keep.gpr (by decide), g1, hdx]
  have hw2 : pR sP ∈ s2.wr := by rw [o2.keep.2.2, o1.wr]; exact hw
  have m2 : s2.mem = s.mem := by rw [o2.mem, o1.mem]
  refine WP.seq (WP.mono (wp_rcxLoopY (N := len / 16) (by bdd_omega) (by bdd_omega)
    (fun u w => S16 w.mem (spW sP) (blk G len k st (16 * u)) ∧ w.gpr .rdx = wAddr (spW sP) (st + 16 * u) ∧
      YConsts w ∧ (∀ l < 2, w.lane .xmm13 l = s2.lane .xmm13 l) ∧ Keep [.rcx, .rdx] s2 w ∧
      Frame [sR (spW sP)] s2.mem w.mem ∧ w.mxcsr = s2.mxcsr)
    (fun w o hy _ => ⟨by rw [hblk.zero, o.mem, m2]; exact hS, by rw [o.keep.gpr (by decide), dx2]; rfl,
      lanes_gpr (s := s2) (GOnly.lane o hy) (YOnly.refl [] s2) c2 (by decide) (by decide),
      fun l _ => GOnly.lane o hy _ l, o.keep.mono (by simp), by rw [o.mem]; exact Frame.refl _ _, o.mxcsr⟩)
    (fun u hu w ⟨hS', hdx', hc', hz', hk', hf', hx'⟩ => WP.mono (VG.Proof.MlKem.X86_64.ystep hbf hY hblk h16 hl hs (by
        have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hl16); omega) hc'
        (fun l hl => by rw [hz' l hl]; exact z2 l hl) hdx' hS'
        (fun j hj => VG.Proof.MlKem.X86_64.sp_inY (by rw [hk'.2.2]; exact hw2) hj))
      fun w' ⟨hS'', hdx'', hf'', hc'', hz'', hk'', hcx, hzf, hx''⟩ =>
        ⟨⟨hS'', hdx'', hc'', fun l hl => by rw [hz'' l hl, hz' l hl], (hk'.trans hk'').mono (by simp),
          hf'.trans hf'', by rw [hx'', hx']⟩, hcx, hzf⟩)) fun w ⟨hS3, hdx3, hc3, _, hk3, hf3, hx3⟩ => ?_)
  rw [show 16 * (len / 16) = len from Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hl16)] at hS3 hdx3
  have hax : w.gpr .rax = s.gpr .rax := by rw [hk3.gpr (by decide), o2.keep.gpr (by decide), g1]
  have h8w : w.gpr .r8 = wAddr sP (kz + 1) := by rw [hk3.gpr (by decide), h82]
  vrunm [hdx3, sx_ofNat (show 2 * len < 2 ^ 31 by bdd_omega), hax, h8w]
  refine ⟨hS3, by rw [wAddr_add, show st + len + len = st + 2 * len by bdd_omega], ?_⟩
  have k1 : Keep [.r8, .rcx, .rdx, .rax] s w :=
    (Keep.trans (⟨fun r _ => by rw [g1], o1.rd, o1.wr⟩ : Keep [] s s1) (o2.keep.trans hk3)).mono (by simp)
  refine ⟨⟨fun r hr => ?_, k1.2.1, k1.2.2⟩, by rw [← m2]; exact hf3,
    lanes_gpr (s := w) (fun r l => by simp only [lane_setReg, lane_setFlags]) (YOnly.refl [] w) hc3
      (by decide) (by decide),
    by simp only [RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]; rw [hx3, o2.mxcsr, o1.mxcsr]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]
  exact k1.gpr (by simp [hr])

/-! ## A layer with `len ≥ 16` -/

theorem ylay_ok {sP : Addr} {len t : Nat} (hlen : len ∈ [16, 32, 64, 128]) (zi : Nat → Nat) {z : Nat → Zq}
    (hzi : ∀ c < 128 / len, t + c < 128 ∧ z (t + c) = zeta (zi c))
    {F : VG.Spec.MlKem.Poly} {s : State} (hc : YConsts s) (hsi : s.gpr .rsi = sP) (hS : S16 s.mem (spW sP) F)
    (hT : VG.Proof.MlKem.X86_64.TZ s.mem sP z) (hw : pR sP ∈ s.wr) :
    WP isa (ylay bf len t) s fun s' => S16 s'.mem (spW sP) (layF blk F len zi (128 / len)) ∧
      VG.Proof.MlKem.X86_64.BInvY sP s s' := by
  have hl : 16 ≤ len ∧ len % 16 = 0 ∧ len ≤ 128 ∧ 2 * len * (128 / len) = 256 ∧ 0 < 128 / len ∧
      128 / len ≤ 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl <;> decide
  obtain ⟨h16, hl16, hl128, hcov, hpos, h8⟩ := hl
  have ht : t < 128 := by have := (hzi 0 hpos).1; omega
  refine WP.seq (WP.mono (Q := fun (w : State) => w.gpr .rdx = spW sP ∧ w.gpr .r8 = wAddr sP t ∧
      w.gpr .rax = BitVec.ofNat 64 (128 / len) ∧ GOnly [.rdx, .r8, .rax] s w ∧ w.ymmHi = s.ymmHi)
    (by
      simp only [leaR, oS]
      vrunm [sx_ofNat (show 256 < 2 ^ 31 by decide), sx_ofNat (show 2 * t < 2 ^ 31 by bdd_omega), hsi,
        RegUpd.ymmHi_setReg, RegUpd.ymmHi_setFlags]
      refine ⟨?_, by gonly⟩
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega) fun w ⟨hdx, h8r, hax, o, hy⟩ => ?_)
  have hw' : pR sP ∈ w.wr := by rw [o.keep.2.2]; exact hw
  have cw : YConsts w := lanes_gpr (s := s) (GOnly.lane o hy) (YOnly.refl [] s) hc (by decide) (by decide)
  refine WP.mono (wp_countdown (cnt := .rax) (N := 128 / len) (by bdd_omega) hpos
    (fun c u => S16 u.mem (spW sP) (layF blk F len zi c) ∧ u.gpr .rdx = wAddr (spW sP) (2 * len * c) ∧
      u.gpr .r8 = wAddr sP (t + c) ∧ VG.Proof.MlKem.X86_64.BInvY sP w u ∧ VG.Proof.MlKem.X86_64.TZ u.mem sP z)
    (fun c hc u ⟨hS', hdx', h8', hb', hT'⟩ _ => ?_) (fun u h => h)
    ⟨by rw [o.mem]; exact hS, by rw [hdx, wAddr, Nat.mul_zero, Nat.mul_zero, add_ofNat_zero],
      by rw [h8r, Nat.add_zero], ⟨Keep.refl _ _, Frame.refl _ _, cw, rfl⟩, by rw [o.mem]; exact hT⟩ hax)
    fun u ⟨hS', _, _, hb', _⟩ => ⟨hS', ⟨(o.keep.trans hb'.keep).mono (by simp),
      by rw [← o.mem]; exact hb'.frame, hb'.consts, by rw [hb'.mxcsr, o.mxcsr]⟩⟩
  have hs : 2 * len * c + 2 * len ≤ 256 := by
    have : 2 * len * (c + 1) ≤ 2 * len * (128 / len) := Nat.mul_le_mul_left _ (by bdd_omega)
    rw [Nat.mul_succ] at this; omega
  refine WP.mono (VG.Proof.MlKem.X86_64.yblock_ok hbf hY hblk h16 hl16 hl128 hs (hzi c hc).1 (hzi c hc).2 hb'.consts hdx' h8' hS' hT'
    (by rw [hb'.keep.2.2]; exact hw')) fun u' ⟨hS'', hdx'', h8'', hax'', hzf'', hb''⟩ =>
      ⟨⟨by rw [layF, foldl_range_succ]; exact hS'', by rw [hdx'', Nat.mul_succ],
        by rw [h8'', Nat.add_assoc], hb'.trans hb'', hT'.frame hb''.frame⟩, hax'', hzf''⟩

/-! ## The layer with `len = 8` -/

/-- The body of the layer with `len = 8`. -/
abbrev ybody8 (bf : List Instr) : List Instr :=
  ([.vmovdquLoad .l256 .xmm4 (VG.Impl.MlKem.X86_64.at_ .rdx 0)] : List Instr) ++ (([.vmovdquLoad .l256 .xmm5 (VG.Impl.MlKem.X86_64.at_ .rdx 32)] : List Instr) ++ (yzeta2 ++
    (([.alu .add .r8 (.imm 4)] : List Instr) ++ (([.vop (.vperm2i128 .xmm0 .xmm4 .xmm5 0x20)] : List Instr) ++
    (([.vop (.vperm2i128 .xmm1 .xmm4 .xmm5 0x31)] : List Instr) ++ (toY bf ++ (([.vop (.vperm2i128 .xmm4 .xmm0 .xmm3 0x20)] : List Instr) ++
    (([.vop (.vperm2i128 .xmm5 .xmm0 .xmm3 0x31)] : List Instr) ++
    ([.vmovdquStore .l256 (VG.Impl.MlKem.X86_64.at_ .rdx 0) .xmm4, .vmovdquStore .l256 (VG.Impl.MlKem.X86_64.at_ .rdx 32) .xmm5, .alu .add .rdx (.imm 64),
      .alu .sub .rcx (.imm 1)] : List Instr)))))))))

theorem ystep8 {sP : Addr} {m t : Nat} (hm : m < 8) (zi : Nat → Nat) {z : Nat → Zq}
    (hz : ∀ c < 16, t + c < 128 ∧ z (t + c) = zeta (zi c)) {F : VG.Spec.MlKem.Poly} {s : State} (hc : YConsts s)
    (hdx : s.gpr .rdx = wAddr (spW sP) (32 * m)) (h8 : s.gpr .r8 = wAddr sP (t + 2 * m))
    (hS : S16 s.mem (spW sP) (layF blk F 8 zi (2 * m))) (hT : VG.Proof.MlKem.X86_64.TZ s.mem sP z) (hw : pR sP ∈ s.wr) :
    WP isa (.block (VG.Proof.MlKem.X86_64.ybody8 bf)) s fun s' =>
      S16 s'.mem (spW sP) (layF blk F 8 zi (2 * (m + 1))) ∧ s'.gpr .rdx = wAddr (spW sP) (32 * (m + 1)) ∧
      s'.gpr .r8 = wAddr sP (t + 2 * (m + 1)) ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ VG.Proof.MlKem.X86_64.BInvY sP s s' := by
  have j0 : 32 * m + 16 ≤ 256 := by bdd_omega
  have j1 : 32 * m + 16 + 16 ≤ 256 := by bdd_omega
  have a1 : wAddr (spW sP) (32 * m) + BitVec.ofNat 64 32 = wAddr (spW sP) (32 * m + 16) := wAddr_add _ _ 16
  have r0 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 0) 32 := by
    rw [hdx, add_ofNat_zero]; exact VG.Proof.MlKem.X86_64.sp_inY (List.mem_append_right s.rd hw) j0
  have r1 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 32) 32 := by
    rw [hdx, a1]; exact VG.Proof.MlKem.X86_64.sp_inY (List.mem_append_right s.rd hw) j1
  generalize hP : layF blk F 8 zi (2 * m) = P at hS
  -- the loads
  rw [VG.Proof.MlKem.X86_64.ybody8, WP.block_append_iff]
  refine WP.mono (yld_ok r0) fun s1 ⟨L4, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr]; exact r1)) fun s2 ⟨L5, o2⟩ => ?_
  have o12 := o1.trans o2
  -- the zetas
  rw [WP.block_append_iff]
  have hk0 := hz (2 * m) (by bdd_omega)
  have hk1 := hz (2 * m + 1) (by bdd_omega)
  refine WP.mono (VG.Proof.MlKem.X86_64.yzetaS_ok 0x00 0x55 (zP := sP) (z := z) (k := t + 2 * m) (fun j _ => by rw [sel_zero]; omega)
    (fun j hj => by rw [VG.Proof.MlKem.X86_64.sel_55 hj]; omega) (by rw [o12.gpr, h8])
    (by rw [o12.rd, o12.wr]; exact tab_in (List.mem_append_right _ hw) (by bdd_omega)) (by rw [o12.mem]; exact hT))
    fun s3 ⟨Z0, Z1, o3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.addR_ok .r8 4 s3) fun s4 ⟨h84, g4, y4⟩ => ?_
  have l4 := GOnly.lane g4 y4
  -- the lower and upper halves
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.yperm_ok s4) fun s5 ⟨P5, o5⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.yperm_ok s5) fun s6 ⟨P6, o6⟩ => ?_
  have c6 : YConsts s6 := (o5.trans o6).consts (lanes_gpr (s := s3) l4 (o12.trans o3) hc (by decide) (by decide))
    (by decide) (by decide)
  have m3 : s3.mem = s.mem := (o12.trans o3).mem
  have q4 : ∀ l < 2, s4.lane .xmm4 l = s.mem.readW (wAddr (spW sP) (32 * m) + BitVec.ofNat 64 (16 * l)) 128 :=
    fun l hl => by rw [l4, o3.lane _ (by decide) l hl, o2.lane _ (by decide) l hl, L4 l hl, hdx, add_ofNat_zero]
  have q5 : ∀ l < 2, s4.lane .xmm5 l = s.mem.readW (wAddr (spW sP) (32 * m + 16) + BitVec.ofNat 64 (16 * l)) 128 :=
    fun l hl => by rw [l4, o3.lane _ (by decide) l hl, L5 l hl, o1.gpr, o1.mem, hdx, a1]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.ybf_ok hbf hY c6 (x := fun l e => P[32 * m + 16 * l + e]!)
    (y := fun l e => P[32 * m + 16 * l + 8 + e]!) (ζ := fun l _ => zeta (zi (2 * m + l)))
    (fun l hl => by
      rw [o6.lane _ (by decide) l hl, P5 l hl, VG.Proof.MlKem.X86_64.perm20 _ _ hl]
      rcases lane01 hl with rfl | rfl
      · rw [ifp rfl, q4 0 (by decide)]
        exact (VG.Proof.MlKem.X86_64.lanes_loadY hS j0 (by decide)).congr fun e _ => rfl
      · rw [ifn (by decide), q5 0 (by decide)]
        exact (VG.Proof.MlKem.X86_64.lanes_loadY hS j1 (by decide)).congr fun e _ => by congr 2)
    (fun l hl => by
      rw [P6 l hl, VG.Proof.MlKem.X86_64.perm31 _ _ hl, o5.lane .xmm4 (by decide) 1 (by decide), o5.lane .xmm5 (by decide) 1 (by decide)]
      rcases lane01 hl with rfl | rfl
      · rw [ifp rfl, q4 1 (by decide)]
        exact (VG.Proof.MlKem.X86_64.lanes_loadY hS j0 (by decide)).congr fun e _ => by congr 2
      · rw [ifn (by decide), q5 1 (by decide)]
        exact (VG.Proof.MlKem.X86_64.lanes_loadY hS j1 (by decide)).congr fun e _ => by congr 2)
    (fun l hl => by
      rw [(o5.trans o6).lane _ (by decide) l hl, l4]
      rcases lane01 hl with rfl | rfl
      · exact Z0.congr fun i _ => by rw [sel_zero, Nat.add_zero, hk0.2, Nat.add_zero]
      · exact Z1.congr fun i hi => by rw [VG.Proof.MlKem.X86_64.sel_55 (by bdd_omega), Nat.add_assoc, hk1.2]))
    fun s7 ⟨B7, o7⟩ => ?_
  -- the blocks back
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.yperm_ok s7) fun s8 ⟨P8, o8⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.yperm_ok s8) fun s9 ⟨P9, o9⟩ => ?_
  have o39 := (o5.trans o6).trans (o7.trans (o8.trans o9))
  have w0 : InRegions s9.wr (s9.gpr .rdx) 32 := by
    rw [o39.wr, o39.gpr, g4.keep.2.2, g4.keep.gpr (by decide), o3.wr, o3.gpr, o12.wr, o12.gpr, hdx]
    exact VG.Proof.MlKem.X86_64.sp_inY hw j0
  have w1 : InRegions s9.wr (s9.gpr .rdx + BitVec.ofNat 64 32) 32 := by
    rw [o39.wr, o39.gpr, g4.keep.2.2, g4.keep.gpr (by decide), o3.wr, o3.gpr, o12.wr, o12.gpr, hdx, a1]
    exact VG.Proof.MlKem.X86_64.sp_inY hw j1
  vrunm [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd, State.setMem_ymm,
    State.setMem_setMem, w0, w1, sx_ofNat (show 64 < 2 ^ 31 by decide)]
  have g9 : s9.gpr = s4.gpr := o39.gpr
  have m9 : s9.mem = s.mem := by rw [o39.mem, g4.mem, m3]
  have dx9 : s9.gpr .rdx = wAddr (spW sP) (32 * m) := by
    rw [g9, g4.keep.gpr (by decide), o3.gpr, o12.gpr, hdx]
  rw [dx9, a1, m9]
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩⟩
  · -- the words stored
    have v0 : ∀ l < 2, ∀ e < 8, (P[32 * m + 16 * l + e]! : Zq) = P[32 * m + 16 * l + e]! := fun _ _ _ _ => rfl
    refine VG.Proof.MlKem.X86_64.s16_write2Y (s := s9) hS j0 j1 (by bdd_omega)
      (a := fun e => if e < 8 then (op P[32 * m + e]! P[32 * m + 8 + e]! (zeta (zi (2 * m)))).1
        else (op P[32 * m + (e - 8)]! P[32 * m + 8 + (e - 8)]! (zeta (zi (2 * m)))).2)
      (b := fun e => if e < 8 then (op P[32 * m + 16 + e]! P[32 * m + 16 + 8 + e]! (zeta (zi (2 * m + 1)))).1
        else (op P[32 * m + 16 + (e - 8)]! P[32 * m + 16 + 8 + (e - 8)]! (zeta (zi (2 * m + 1)))).2)
      (fun l hl i hi => ?_) (fun l hl i hi => ?_) (fun i hi => ?_)
    · rw [o9.lane .xmm4 (by decide) l hl, P8 l hl, VG.Proof.MlKem.X86_64.perm20 _ _ hl]
      rcases lane01 hl with rfl | rfl
      · rw [ifp rfl, (B7 0 (by decide)).1 i hi]; dsimp only; rw [ite_eq_left_of_eq_true _ _ (eq_true (by bdd_omega))]
        try simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add]
      · rw [ifn (by decide), (B7 0 (by decide)).2 i hi]; dsimp only
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by bdd_omega)), show 8 * 1 + i - 8 = i by bdd_omega]
        try simp only [Nat.mul_zero, Nat.add_zero]
    · rw [P9 l hl, VG.Proof.MlKem.X86_64.perm31 _ _ hl, o8.lane .xmm0 (by decide) 1 (by decide), o8.lane .xmm3 (by decide) 1 (by decide)]
      rcases lane01 hl with rfl | rfl
      · rw [ifp rfl, (B7 1 (by decide)).1 i hi]; dsimp only; rw [ite_eq_left_of_eq_true _ _ (eq_true (by bdd_omega))]
        try simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one]
      · rw [ifn (by decide), (B7 1 (by decide)).2 i hi]; dsimp only
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by bdd_omega)), show 8 * 1 + i - 8 = i by bdd_omega]
        try simp only [Nat.mul_one]
    · -- the specification: two blocks
      rw [← hP, VG.Proof.MlKem.X86_64.layF_get hblk F (by decide) zi (by bdd_omega) hi]
      have hF : ∀ j, 32 * m ≤ j → j < 256 → (layF blk F 8 zi (2 * m))[j]! = F[j]! := fun j h1 h2 => by
        rw [VG.Proof.MlKem.X86_64.layF_get hblk F (by decide) zi (by bdd_omega) h2, ite_eq_right_of_eq_false _ _ (eq_false (by bdd_omega))]
      by_cases h1 : 32 * m ≤ i ∧ i < 32 * m + 16
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (by bdd_omega)), ite_eq_left_of_eq_true _ _ (eq_true h1),
          show i / (2 * 8) = 2 * m by bdd_omega]
        by_cases h2 : i - 32 * m < 8
        · rw [ite_eq_left_of_eq_true _ _ (eq_true (by bdd_omega)), ite_eq_left_of_eq_true _ _ (eq_true h2),
            hF _ (by bdd_omega) (by bdd_omega), hF _ (by bdd_omega) (by bdd_omega), show 32 * m + (i - 32 * m) = i by bdd_omega,
            show 32 * m + 8 + (i - 32 * m) = i + 8 by bdd_omega]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by bdd_omega)), ite_eq_right_of_eq_false _ _ (eq_false h2),
            hF _ (by bdd_omega) (by bdd_omega), hF _ (by bdd_omega) (by bdd_omega), show 32 * m + (i - 32 * m - 8) = i - 8 by bdd_omega,
            show 32 * m + 8 + (i - 32 * m - 8) = i by bdd_omega]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
        by_cases h1' : 32 * m + 16 ≤ i ∧ i < 32 * m + 16 + 16
        · rw [ite_eq_left_of_eq_true _ _ (eq_true (by bdd_omega)), ite_eq_left_of_eq_true _ _ (eq_true h1'),
            show i / (2 * 8) = 2 * m + 1 by bdd_omega]
          by_cases h2 : i - (32 * m + 16) < 8
          · rw [ite_eq_left_of_eq_true _ _ (eq_true (by bdd_omega)), ite_eq_left_of_eq_true _ _ (eq_true h2),
              hF _ (by bdd_omega) (by bdd_omega), hF _ (by bdd_omega) (by bdd_omega),
              show 32 * m + 16 + (i - (32 * m + 16)) = i by bdd_omega,
              show 32 * m + 16 + 8 + (i - (32 * m + 16)) = i + 8 by bdd_omega]
          · rw [ite_eq_right_of_eq_false _ _ (eq_false (by bdd_omega)), ite_eq_right_of_eq_false _ _ (eq_false h2),
              hF _ (by bdd_omega) (by bdd_omega), hF _ (by bdd_omega) (by bdd_omega),
              show 32 * m + 16 + (i - (32 * m + 16) - 8) = i - 8 by bdd_omega,
              show 32 * m + 16 + 8 + (i - (32 * m + 16) - 8) = i by bdd_omega]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h1'), VG.Proof.MlKem.X86_64.layF_get hblk F (by decide) zi (b := 2 * m) (by bdd_omega) hi]
          by_cases h3 : i < 32 * m
          · rw [ite_eq_left_of_eq_true _ _ (eq_true (show i < 2 * 8 * (2 * (m + 1)) by bdd_omega)),
              ite_eq_left_of_eq_true _ _ (eq_true (show i < 2 * 8 * (2 * m) by bdd_omega))]
          · rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ i < 2 * 8 * (2 * (m + 1)) by bdd_omega)),
              ite_eq_right_of_eq_false _ _ (eq_false (show ¬ i < 2 * 8 * (2 * m) by bdd_omega))]
  · rw [show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 (2 * 32) by decide, wAddr_add, Nat.mul_succ]
  · have e3 : s3.gpr .r8 = wAddr sP (t + 2 * m) := by rw [o3.gpr, o12.gpr, h8]
    try simp only [g9, h84]
    rw [e3, show BitVec.signExtend 64 (4 : BitVec 32) = BitVec.ofNat 64 (2 * 2) by decide, wAddr_add,
      show t + 2 * m + 2 = t + 2 * (m + 1) by bdd_omega]
  · rw [g9, g4.keep.gpr (by decide), o3.gpr, o12.gpr]
  · rw [g9, g4.keep.gpr (by decide), o3.gpr, o12.gpr]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false, State.setMem_gpr]
    rw [g9, g4.keep.gpr (by simp [hr]), o3.gpr, o12.gpr]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]
    rw [o39.rd, g4.keep.2.1, o3.rd, o12.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]
    rw [o39.wr, g4.keep.2.2, o3.wr, o12.wr]
  · exact VG.Proof.MlKem.X86_64.frame_write2Y (Frame.refl _ _) j0 j1 _ _
  · exact lanes_gpr (s := s9) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane])
      o39 (lanes_gpr (s := s3) l4 (o12.trans o3) hc (by decide) (by decide)) (by decide) (by decide)
  · exact (o39.mxcsr.trans (g4.mxcsr.trans ((o12.trans o3).mxcsr)))

omit hbf hY hblk in
/-- The prologue of the layers with `len` = 8, 4 and 2. -/
theorem ypre_ok {sP : Addr} (t : Nat) (ht : t < 128) {s : State} (hsi : s.gpr .rsi = sP) :
    WP isa (.block (leaR .rdx .rsi oS ++ leaR .r8 .rsi (2 * t))) s fun w =>
      w.gpr .rdx = spW sP ∧ w.gpr .r8 = wAddr sP t ∧ GOnly [.rdx, .r8] s w ∧ w.ymmHi = s.ymmHi := by
  simp only [leaR, oS]
  vrunm [sx_ofNat (show 256 < 2 ^ 31 by decide), sx_ofNat (show 2 * t < 2 ^ 31 by bdd_omega), hsi,
    RegUpd.ymmHi_setReg]
  exact ⟨by gonly, rfl⟩

theorem ylay8_ok {sP : Addr} {t : Nat} (zi : Nat → Nat) {z : Nat → Zq}
    (hz : ∀ c < 16, t + c < 128 ∧ z (t + c) = zeta (zi c))
    {F : VG.Spec.MlKem.Poly} {s : State} (hc : YConsts s) (hsi : s.gpr .rsi = sP) (hS : S16 s.mem (spW sP) F)
    (hT : VG.Proof.MlKem.X86_64.TZ s.mem sP z) (hw : pR sP ∈ s.wr) :
    WP isa (ylay8 bf t) s fun s' => S16 s'.mem (spW sP) (layF blk F 8 zi 16) ∧ VG.Proof.MlKem.X86_64.BInvY sP s s' := by
  have ht : t < 128 := by have := (hz 0 (by decide)).1; omega
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.ypre_ok t ht hsi) fun w ⟨hdx, h8, og, hy⟩ => ?_)
  have cw : YConsts w := lanes_gpr (s := s) (GOnly.lane og hy) (YOnly.refl [] s) hc (by decide) (by decide)
  refine WP.mono (wp_rcxLoopY (N := 8) (by decide) (by decide)
    (fun i u => S16 u.mem (spW sP) (layF blk F 8 zi (2 * i)) ∧ u.gpr .rdx = wAddr (spW sP) (32 * i) ∧
      u.gpr .r8 = wAddr sP (t + 2 * i) ∧ VG.Proof.MlKem.X86_64.BInvY sP w u)
    (fun u ou hu _ => ⟨by rw [ou.mem, og.mem]; exact hS,
      by rw [ou.keep.gpr (by decide), hdx, Nat.mul_zero, wAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [ou.keep.gpr (by decide), h8, Nat.mul_zero, Nat.add_zero], ⟨ou.keep.mono (by simp),
        by rw [ou.mem]; exact Frame.refl _ _,
        lanes_gpr (s := w) (GOnly.lane ou hu) (YOnly.refl [] w) cw (by decide) (by decide), ou.mxcsr⟩⟩)
    (fun i hi u ⟨hS', hdx', h8', hb'⟩ => ?_)) fun u ⟨hS', _, _, hb'⟩ =>
      ⟨hS', ⟨(og.keep.trans hb'.keep).mono (by simp), by rw [← og.mem]; exact hb'.frame, hb'.consts,
        by rw [hb'.mxcsr, og.mxcsr]⟩⟩
  have hT' : VG.Proof.MlKem.X86_64.TZ u.mem sP z := (by rw [og.mem]; exact hT : TZ w.mem sP z).frame hb'.frame
  have hw' : pR sP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hw
  rw [show ([.vmovdquLoad .l256 .xmm4 (VG.Impl.MlKem.X86_64.at_ .rdx 0), .vmovdquLoad .l256 .xmm5 (VG.Impl.MlKem.X86_64.at_ .rdx 32)] : List Instr) ++ yzeta2 ++
      ([.alu .add .r8 (.imm 4), .vop (.vperm2i128 .xmm0 .xmm4 .xmm5 0x20), .vop (.vperm2i128 .xmm1 .xmm4 .xmm5 0x31)] : List Instr) ++
      toY bf ++ ([.vop (.vperm2i128 .xmm4 .xmm0 .xmm3 0x20), .vop (.vperm2i128 .xmm5 .xmm0 .xmm3 0x31),
        .vmovdquStore .l256 (VG.Impl.MlKem.X86_64.at_ .rdx 0) .xmm4, .vmovdquStore .l256 (VG.Impl.MlKem.X86_64.at_ .rdx 32) .xmm5, .alu .add .rdx (.imm 64)] : List Instr) ++
      ([.alu .sub .rcx (.imm 1)] : List Instr) = VG.Proof.MlKem.X86_64.ybody8 bf by simp [List.append_assoc]]
  exact WP.mono (VG.Proof.MlKem.X86_64.ystep8 hbf hY hblk hi zi hz hb'.consts hdx' h8' hS' hT' hw')
    fun u' ⟨hS'', hdx'', h8'', hcx, hzf, hb''⟩ => ⟨⟨hS'', hdx'', h8'', hb'.trans hb''⟩, hcx, hzf⟩

end

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.YNttLay42`. -/
section

/-!
# ML-KEM on x86-64: the layers of the NTT and its inverse with `len` = 4 and 2 on AVX2 registers

Each iteration of these layers loads 32 words, from `j`, into `ymm0` and
`ymm4`, and in each lane `l` runs `vlay4`'s or `vlay2`'s gathering,
butterflies and interleaving back (`Ntt.lean`) on the eight words from `j +
8l` and the eight from `j + 16 + 8l` (`core4_ok`, `core2_ok`), with the zetas
of their blocks in lane `l` of `ymm13` (`yzetaS_ok`, `yzeta8_ok`); `ystep42`
is an iteration for any such code, and `ylay4_ok` and `ylay2_ok` the layers.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- The body of the loop of `ylay42`. -/
abbrev ybody42 (core zeta : List Instr) (dz : BitVec 32) : List Instr :=
  ([.vmovdquLoad .l256 .xmm0 (VG.Impl.MlKem.X86_64.at_ .rdx 0)] : List Instr) ++ (([.vmovdquLoad .l256 .xmm4 (VG.Impl.MlKem.X86_64.at_ .rdx 32)] : List Instr) ++ (zeta ++
    (([.alu .add .r8 (.imm dz)] : List Instr) ++ (toY core ++
    ([.vmovdquStore .l256 (VG.Impl.MlKem.X86_64.at_ .rdx 0) .xmm0, .vmovdquStore .l256 (VG.Impl.MlKem.X86_64.at_ .rdx 32) .xmm1, .alu .add .rdx (.imm 64),
      .alu .sub .rcx (.imm 1)] : List Instr)))))

/-- An iteration of a layer with `len` = 4 or 2: the 32 words of `G` from `j`,
in lane `l` the eight from `j + 8l` and the eight from `j + 16 + 8l`, become
those of `R`, with the zetas `ζ l` that `zeta` leaves in the lanes of `ymm13`. -/
theorem ystep42 {core zeta : List Instr} {dz : BitVec 32} (hY : laneSseBlock (toY core) = some core)
    {sP : Addr} {j : Nat} (hj : j + 32 ≤ 256) {G R : VG.Spec.MlKem.Poly} {ζ : Nat → Nat → Zq} {s : State} (hc : YConsts s)
    (hdx : s.gpr .rdx = wAddr (spW sP) j) (hS : S16 s.mem (spW sP) G) (hw : pR sP ∈ s.wr)
    (hz : ∀ s', XKeep s s' →
      WP isa (.block zeta) s' fun s'' => (∀ l < 2, ZLanes (s''.lane .xmm13 l) (ζ l)) ∧
        YOnly [.xmm13, .xmm2, .xmm1] s' s'')
    (hcore : ∀ l < 2, ∀ t : State, VConsts t → VG.Proof.MlKem.X86_64.Lanes (t.xmm .xmm0) (fun e => G[j + 8 * l + e]!) →
      VG.Proof.MlKem.X86_64.Lanes (t.xmm .xmm4) (fun e => G[j + 16 + 8 * l + e]!) → ZLanes (t.xmm .xmm13) (ζ l) →
      WP isa (.block core) t fun t' => (VG.Proof.MlKem.X86_64.Lanes (t'.xmm .xmm0) (fun e => R[j + 8 * l + e]!) ∧
        VG.Proof.MlKem.X86_64.Lanes (t'.xmm .xmm1) (fun e => R[j + 16 + 8 * l + e]!)) ∧ XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4] t t')
    (hR : ∀ i < 256, i < j ∨ j + 32 ≤ i → R[i]! = G[i]!) :
    WP isa (.block (VG.Proof.MlKem.X86_64.ybody42 core zeta dz)) s fun s' =>
      S16 s'.mem (spW sP) R ∧ s'.gpr .rdx = wAddr (spW sP) (j + 32) ∧
      s'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ VG.Proof.MlKem.X86_64.BInvY sP s s' := by
  have j0 : j + 16 ≤ 256 := by bdd_omega 256
  have j1 : j + 16 + 16 ≤ 256 := by bdd_omega 256
  have a1 : wAddr (spW sP) j + BitVec.ofNat 64 32 = wAddr (spW sP) (j + 16) := wAddr_add _ _ 16
  have r0 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 0) 32 := by
    rw [hdx, add_ofNat_zero]; exact VG.Proof.MlKem.X86_64.sp_inY (List.mem_append_right s.rd hw) j0
  have r1 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 32) 32 := by
    rw [hdx, a1]; exact VG.Proof.MlKem.X86_64.sp_inY (List.mem_append_right s.rd hw) j1
  rw [VG.Proof.MlKem.X86_64.ybody42, WP.block_append_iff]
  refine WP.mono (yld_ok r0) fun s1 ⟨L0, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr]; exact r1)) fun s2 ⟨L4, o2⟩ => ?_
  have o12 := o1.trans o2
  rw [WP.block_append_iff]
  refine WP.mono (hz s2 o12.toXKeep) fun s3 ⟨Z3, o3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.addR_ok .r8 dz s3) fun s4 ⟨h84, g4, y4⟩ => ?_
  have l4 := GOnly.lane g4 y4
  have c4 : YConsts s4 := lanes_gpr (s := s3) l4 (o12.trans o3) hc (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ylanes hY (P := fun l t => VG.Proof.MlKem.X86_64.Lanes (t.xmm .xmm0) (fun e => R[j + 8 * l + e]!) ∧
      VG.Proof.MlKem.X86_64.Lanes (t.xmm .xmm1) (fun e => R[j + 16 + 8 * l + e]!))
    fun l hl => hcore l hl _ (c4 l hl)
      (by rw [State.proj_xmm, l4, o3.lane _ (by decide) l hl, o2.lane _ (by decide) l hl, L0 l hl, hdx,
        add_ofNat_zero]; exact (VG.Proof.MlKem.X86_64.lanes_loadY hS j0 hl).congr fun _ _ => rfl)
      (by rw [State.proj_xmm, l4, o3.lane _ (by decide) l hl, L4 l hl, o1.gpr, o1.mem, hdx, a1]
          exact (VG.Proof.MlKem.X86_64.lanes_loadY hS j1 hl).congr fun _ _ => rfl)
      (by rw [State.proj_xmm, l4]; exact Z3 l hl)) fun s5 ⟨C5, o5⟩ => ?_
  have m5 : s5.mem = s.mem := by rw [o5.mem, g4.mem, o3.mem, o12.mem]
  have g5 : s5.gpr = s4.gpr := o5.gpr
  have dx5 : s5.gpr .rdx = wAddr (spW sP) j := by rw [g5, g4.keep.gpr (by decide), o3.gpr, o12.gpr, hdx]
  have k5 : s5.rd = s.rd ∧ s5.wr = s.wr := ⟨by rw [o5.rd, g4.keep.2.1, o3.rd, o12.rd],
    by rw [o5.wr, g4.keep.2.2, o3.wr, o12.wr]⟩
  have w0 : InRegions s5.wr (s5.gpr .rdx) 32 := by rw [k5.2, dx5]; exact VG.Proof.MlKem.X86_64.sp_inY hw j0
  have w1 : InRegions s5.wr (s5.gpr .rdx + BitVec.ofNat 64 32) 32 := by rw [k5.2, dx5, a1]; exact VG.Proof.MlKem.X86_64.sp_inY hw j1
  vrunm [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd, State.setMem_ymm,
    State.setMem_setMem, w0, w1]
  rw [dx5, a1, m5]
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩⟩
  · refine VG.Proof.MlKem.X86_64.s16_write2Y (s := s5) hS j0 j1 (by bdd_omega 256) (a := fun e => R[j + e]!) (b := fun e => R[j + 16 + e]!)
      (fun l hl => ((C5 l hl).1).congr fun e _ => by rw [show j + 8 * l + e = j + (8 * l + e) by bdd_omega 256])
      (fun l hl => ((C5 l hl).2).congr fun e _ => by
        rw [show j + 16 + 8 * l + e = j + 16 + (8 * l + e) by bdd_omega 256]) fun i hi => ?_
    by_cases h1 : j ≤ i ∧ i < j + 16
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), show j + (i - j) = i by bdd_omega 256]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      by_cases h2 : j + 16 ≤ i ∧ i < j + 16 + 16
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), show j + 16 + (i - (j + 16)) = i by bdd_omega 256]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h2)]; exact hR i hi (by bdd_omega 256)
  · rw [show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 (2 * 32) by decide, wAddr_add]
  · rw [g5, h84, o3.gpr, o12.gpr]
  · rw [g5, g4.keep.gpr (by decide), o3.gpr, o12.gpr]
  · rw [g5, g4.keep.gpr (by decide), o3.gpr, o12.gpr]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false, State.setMem_gpr]
    rw [g5, g4.keep.gpr (by simp [hr]), o3.gpr, o12.gpr]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; exact k5.1
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; exact k5.2
  · exact VG.Proof.MlKem.X86_64.frame_write2Y (Frame.refl _ _) j0 j1 _ _
  · exact lanes_gpr (s := s5) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o5 c4
      (by decide) (by decide)
  · exact o5.mxcsr.trans (g4.mxcsr.trans (o12.trans o3).mxcsr)

/-! ## The gatherings, the butterflies and the interleavings back of a lane -/

theorem gath4_ok (t : State) :
    WP isa (.block gath4) t fun t' => (t'.xmm .xmm0 = XBinOp.eval .punpcklqdq (t.xmm .xmm0) (t.xmm .xmm4) ∧
      t'.xmm .xmm1 = XBinOp.eval .punpckhqdq (t.xmm .xmm0) (t.xmm .xmm4)) ∧ XOnly [.xmm1, .xmm0] t t' := by
  simp only [gath4, xmov, xb]
  vrun [eval_movdqa]
  exact ⟨by first | trivial | simp, by xonly⟩

theorem scat4_ok (t : State) :
    WP isa (.block scat4) t fun t' => (t'.xmm .xmm0 = XBinOp.eval .punpcklqdq (t.xmm .xmm0) (t.xmm .xmm3) ∧
      t'.xmm .xmm1 = XBinOp.eval .punpckhqdq (t.xmm .xmm0) (t.xmm .xmm3)) ∧ XOnly [.xmm1, .xmm0] t t' := by
  simp only [scat4, xmov, xb]
  vrun [eval_movdqa]
  exact ⟨by first | trivial | simp, by xonly⟩

theorem gath2_ok (t : State) :
    WP isa (.block gath2) t fun t' =>
      (t'.xmm .xmm0 = XBinOp.eval .punpcklqdq (shufDwords (t.xmm .xmm0) 0xD8) (shufDwords (t.xmm .xmm4) 0xD8) ∧
      t'.xmm .xmm1 = XBinOp.eval .punpckhqdq (shufDwords (t.xmm .xmm0) 0xD8) (shufDwords (t.xmm .xmm4) 0xD8)) ∧
        XOnly [.xmm0, .xmm4, .xmm1] t t' := by
  simp only [gath2, xmov, xb]
  vrun [eval_movdqa]
  exact ⟨by first | trivial | simp, by xonly⟩

theorem scat2_ok (t : State) :
    WP isa (.block scat2) t fun t' => (t'.xmm .xmm0 = XBinOp.eval .punpckldq (t.xmm .xmm0) (t.xmm .xmm3) ∧
      t'.xmm .xmm1 = XBinOp.eval .punpckhdq (t.xmm .xmm0) (t.xmm .xmm3)) ∧ XOnly [.xmm1, .xmm0] t t' := by
  simp only [scat2, xmov, xb]
  vrun [eval_movdqa]
  exact ⟨by first | trivial | simp, by xonly⟩

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} (hbf : VBflyOk bf op)
include hbf

/-- `vlay4`'s work on the words `A` of `xmm0` and `B` of `xmm4`: the blocks
`A` and `B` of `len = 4`, with the zetas `ζ` (the first four words for the
lower halves, the last four for the upper halves). -/
theorem core4_ok {t : State} (hc : VConsts t) {A B ζ : Nat → Zq} (hA : VG.Proof.MlKem.X86_64.Lanes (t.xmm .xmm0) A)
    (hB : VG.Proof.MlKem.X86_64.Lanes (t.xmm .xmm4) B) (hz : ZLanes (t.xmm .xmm13) ζ) :
    WP isa (.block (gath4 ++ bf ++ scat4)) t fun t' =>
      (VG.Proof.MlKem.X86_64.Lanes (t'.xmm .xmm0) (fun e => if e < 4 then (op (A e) (A (4 + e)) (ζ e)).1
          else (op (A (e - 4)) (A e) (ζ (e - 4))).2) ∧
        VG.Proof.MlKem.X86_64.Lanes (t'.xmm .xmm1) (fun e => if e < 4 then (op (B e) (B (4 + e)) (ζ (4 + e))).1
          else (op (B (e - 4)) (B e) (ζ e)).2)) ∧ XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4] t t' := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.gath4_ok t) fun t1 ⟨⟨e0, e1⟩, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hbf _ (o1.consts hc (by decide) (by decide))
    (fun e => if e < 4 then A e else B (e - 4)) (fun e => if e < 4 then A (4 + e) else B e) ζ
    (fun e he => by
      dsimp only; rw [e0, word_punpcklqdq _ _ he]
      by_cases h : e < 4 <;> simp only [h, ite_true, ite_false]
      · exact hA e he
      · exact hB (e - 4) (by bdd_omega 256))
    (fun e he => by
      dsimp only; rw [e1, word_punpckhqdq _ _ he]
      by_cases h : e < 4 <;> simp only [h, ite_true, ite_false]
      · exact hA (4 + e) (by bdd_omega 256)
      · exact hB e he)
    (by rw [o1.xmm _ (by decide)]; exact hz)) fun t2 ⟨X, Y, o2⟩ => ?_
  refine WP.mono (VG.Proof.MlKem.X86_64.scat4_ok t2) fun t3 ⟨⟨f0, f1⟩, o3⟩ => ⟨⟨fun e he => ?_, fun e he => ?_⟩, ?_⟩
  · rw [f0, word_punpcklqdq _ _ he]
    split
    · rw [X e he]; dsimp only
      rw [ite_eq_left_of_eq_true _ _ (eq_true ‹e < 4›), ite_eq_left_of_eq_true _ _ (eq_true ‹e < 4›),
        ite_eq_left_of_eq_true _ _ (eq_true ‹e < 4›)]
    · rw [Y (e - 4) (by bdd_omega 256)]; dsimp only
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show e - 4 < 4 by bdd_omega 256)),
        ite_eq_left_of_eq_true _ _ (eq_true (show e - 4 < 4 by bdd_omega 256)),
        ite_eq_right_of_eq_false _ _ (eq_false ‹¬ e < 4›), show 4 + (e - 4) = e by bdd_omega 256]
  · rw [f1, word_punpckhqdq _ _ he]
    split
    · rw [X (4 + e) (by bdd_omega 256)]; dsimp only
      rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 4 + e < 4 by bdd_omega 256)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 4 + e < 4 by bdd_omega 256)),
        ite_eq_left_of_eq_true _ _ (eq_true ‹e < 4›), show 4 + e - 4 = e by bdd_omega 256]
    · rw [Y e he]; dsimp only
      rw [ite_eq_right_of_eq_false _ _ (eq_false ‹¬ e < 4›), ite_eq_right_of_eq_false _ _ (eq_false ‹¬ e < 4›),
        ite_eq_right_of_eq_false _ _ (eq_false ‹¬ e < 4›)]
  · exact ((o1.trans o2).trans o3).mono (by simp)

/-- `vlay2`'s work on the words `A` of `xmm0` and `B` of `xmm4`: the blocks
`A` and `B` of `len = 2`, with the zetas `ζ` (by doubleword, of the blocks
`A₀₋₃`, `A₄₋₇`, `B₀₋₃`, `B₄₋₇`). -/
theorem core2_ok {t : State} (hc : VConsts t) {A B ζ : Nat → Zq} (hA : VG.Proof.MlKem.X86_64.Lanes (t.xmm .xmm0) A)
    (hB : VG.Proof.MlKem.X86_64.Lanes (t.xmm .xmm4) B) (hz : ZLanes (t.xmm .xmm13) ζ) :
    WP isa (.block (gath2 ++ bf ++ scat2)) t fun t' =>
      (VG.Proof.MlKem.X86_64.Lanes (t'.xmm .xmm0) (fun i => if i % 4 < 2 then (op (A i) (A (i + 2)) (ζ (2 * (i / 4) + i % 2))).1
          else (op (A (i - 2)) (A i) (ζ (2 * (i / 4) + i % 2))).2) ∧
        VG.Proof.MlKem.X86_64.Lanes (t'.xmm .xmm1) (fun i => if i % 4 < 2 then (op (B i) (B (i + 2)) (ζ (4 + 2 * (i / 4) + i % 2))).1
          else (op (B (i - 2)) (B i) (ζ (4 + 2 * (i / 4) + i % 2))).2)) ∧
      XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4] t t' := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.gath2_ok t) fun t1 ⟨⟨e0, e1⟩, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hbf _ (o1.consts hc (by decide) (by decide))
    (fun e => if e < 4 then A (4 * (e / 2) + e % 2) else B (4 * ((e - 4) / 2) + e % 2))
    (fun e => if e < 4 then A (4 * (e / 2) + 2 + e % 2) else B (4 * ((e - 4) / 2) + 2 + e % 2)) ζ
    (fun e he => by
      dsimp only; rw [e0, word_punpcklqdq _ _ he]
      by_cases h : e < 4 <;> simp only [h, ite_true, ite_false]
      · rw [word_d8 _ (by bdd_omega 256), ite_eq_left_of_eq_true _ _ (eq_true h)]; exact hA _ (by bdd_omega 256)
      · rw [word_d8 _ (by bdd_omega 256), ite_eq_left_of_eq_true _ _ (eq_true (show e - 4 < 4 by bdd_omega 256)),
          show (e - 4) / 2 = (e - 4) / 2 by rfl, show (e - 4) % 2 = e % 2 by bdd_omega 256]
        exact hB _ (by bdd_omega 256))
    (fun e he => by
      dsimp only; rw [e1, word_punpckhqdq _ _ he]
      by_cases h : e < 4 <;> simp only [h, ite_true, ite_false]
      · rw [word_d8 _ (by bdd_omega 256), ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 4 + e < 4 by bdd_omega 256)),
          show (4 + e - 4) / 2 = e / 2 by bdd_omega 256, show (4 + e) % 2 = e % 2 by bdd_omega 256]
        exact hA _ (by bdd_omega 256)
      · rw [word_d8 _ (by bdd_omega 256), ite_eq_right_of_eq_false _ _ (eq_false h)]; exact hB _ (by bdd_omega 256))
    (by rw [o1.xmm _ (by decide)]; exact hz)) fun t2 ⟨X, Y, o2⟩ => ?_
  refine WP.mono (VG.Proof.MlKem.X86_64.scat2_ok t2) fun t3 ⟨⟨f0, f1⟩, o3⟩ => ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, ?_⟩
  · rw [f0, word_punpckldq _ _ hi]
    have hw : 2 * (i / 4) + i % 2 < 8 := by bdd_omega 256
    by_cases h : i % 4 < 2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (show i / 2 % 2 = 0 by bdd_omega 256)), X _ hw]; dsimp only
      rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true (show 2 * (i / 4) + i % 2 < 4 by bdd_omega 256)),
        ite_eq_left_of_eq_true _ _ (eq_true (show 2 * (i / 4) + i % 2 < 4 by bdd_omega 256)),
        show 4 * ((2 * (i / 4) + i % 2) / 2) + (2 * (i / 4) + i % 2) % 2 = i by bdd_omega 256,
        show 4 * ((2 * (i / 4) + i % 2) / 2) + 2 + (2 * (i / 4) + i % 2) % 2 = i + 2 by bdd_omega 256]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ i / 2 % 2 = 0 by bdd_omega 256)), Y _ hw]; dsimp only
      rw [ite_eq_right_of_eq_false _ _ (eq_false h),
        ite_eq_left_of_eq_true _ _ (eq_true (show 2 * (i / 4) + i % 2 < 4 by bdd_omega 256)),
        ite_eq_left_of_eq_true _ _ (eq_true (show 2 * (i / 4) + i % 2 < 4 by bdd_omega 256)),
        show 4 * ((2 * (i / 4) + i % 2) / 2) + (2 * (i / 4) + i % 2) % 2 = i - 2 by bdd_omega 256,
        show 4 * ((2 * (i / 4) + i % 2) / 2) + 2 + (2 * (i / 4) + i % 2) % 2 = i by bdd_omega 256]
  · rw [f1, word_punpckhdq _ _ hi]
    have hw : 4 + 2 * (i / 4) + i % 2 < 8 := by bdd_omega 256
    by_cases h : i % 4 < 2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (show i / 2 % 2 = 0 by bdd_omega 256)), X _ hw]; dsimp only
      rw [ite_eq_left_of_eq_true _ _ (eq_true h),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 4 + 2 * (i / 4) + i % 2 < 4 by bdd_omega 256)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 4 + 2 * (i / 4) + i % 2 < 4 by bdd_omega 256)),
        show 4 * ((4 + 2 * (i / 4) + i % 2 - 4) / 2) + (4 + 2 * (i / 4) + i % 2) % 2 = i by bdd_omega 256,
        show 4 * ((4 + 2 * (i / 4) + i % 2 - 4) / 2) + 2 + (4 + 2 * (i / 4) + i % 2) % 2 = i + 2 by bdd_omega 256]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ i / 2 % 2 = 0 by bdd_omega 256)), Y _ hw]; dsimp only
      rw [ite_eq_right_of_eq_false _ _ (eq_false h),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 4 + 2 * (i / 4) + i % 2 < 4 by bdd_omega 256)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 4 + 2 * (i / 4) + i % 2 < 4 by bdd_omega 256)),
        show 4 * ((4 + 2 * (i / 4) + i % 2 - 4) / 2) + (4 + 2 * (i / 4) + i % 2) % 2 = i - 2 by bdd_omega 256,
        show 4 * ((4 + 2 * (i / 4) + i % 2 - 4) / 2) + 2 + (4 + 2 * (i / 4) + i % 2) % 2 = i by bdd_omega 256]
  · exact ((o1.trans o2).trans o3).mono (by simp)

end

/-! ## The layers -/

/-- A layer of eight iterations of `ystep42`, iteration `m` turning `Gs m`
into `Gs (m + 1)`, with `r8` at word `t + c m` of the table. -/
theorem ylay42_loop {bf gath scat zeta : List Instr} {dz : BitVec 32}
    (hY : laneSseBlock (toY (gath ++ bf ++ scat)) = some (gath ++ bf ++ scat)) {sP : Addr} {t : Nat} (ht : t < 128)
    (c : Nat → Nat) (hc0 : c 0 = 0) (hdz : ∀ m < 8, wAddr sP (t + c m) + BitVec.signExtend 64 dz = wAddr sP (t + c (m + 1)))
    {z : Nat → Zq} (Gs : Nat → VG.Spec.MlKem.Poly) (ζ : Nat → Nat → Nat → Zq)
    (hz : ∀ m < 8, ∀ s' : State, s'.gpr .r8 = wAddr sP (t + c m) → VG.Proof.MlKem.X86_64.TZ s'.mem sP z → pR sP ∈ s'.wr →
      WP isa (.block zeta) s' fun s'' => (∀ l < 2, ZLanes (s''.lane .xmm13 l) (ζ m l)) ∧
        YOnly [.xmm13, .xmm2, .xmm1] s' s'')
    (hcore : ∀ m < 8, ∀ l < 2, ∀ t' : State, VConsts t' → VG.Proof.MlKem.X86_64.Lanes (t'.xmm .xmm0) (fun e => (Gs m)[32 * m + 8 * l + e]!) →
      VG.Proof.MlKem.X86_64.Lanes (t'.xmm .xmm4) (fun e => (Gs m)[32 * m + 16 + 8 * l + e]!) → ZLanes (t'.xmm .xmm13) (ζ m l) →
      WP isa (.block (gath ++ bf ++ scat)) t' fun t'' =>
        (VG.Proof.MlKem.X86_64.Lanes (t''.xmm .xmm0) (fun e => (Gs (m + 1))[32 * m + 8 * l + e]!) ∧
          VG.Proof.MlKem.X86_64.Lanes (t''.xmm .xmm1) (fun e => (Gs (m + 1))[32 * m + 16 + 8 * l + e]!)) ∧
        XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4] t' t'')
    (hR : ∀ m < 8, ∀ i < 256, i < 32 * m ∨ 32 * m + 32 ≤ i → (Gs (m + 1))[i]! = (Gs m)[i]!)
    {s : State} (hc : YConsts s) (hsi : s.gpr .rsi = sP) (hS : S16 s.mem (spW sP) (Gs 0))
    (hT : VG.Proof.MlKem.X86_64.TZ s.mem sP z) (hw : pR sP ∈ s.wr) :
    WP isa (ylay42 bf gath scat zeta dz t) s fun s' => S16 s'.mem (spW sP) (Gs 8) ∧ VG.Proof.MlKem.X86_64.BInvY sP s s' := by
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.ypre_ok t ht hsi) fun w ⟨hdx, h8, og, hy⟩ => ?_)
  have cw : YConsts w := lanes_gpr (s := s) (GOnly.lane og hy) (YOnly.refl [] s) hc (by decide) (by decide)
  refine WP.mono (wp_rcxLoopY (N := 8) (by decide) (by decide)
    (fun i u => S16 u.mem (spW sP) (Gs i) ∧ u.gpr .rdx = wAddr (spW sP) (32 * i) ∧
      u.gpr .r8 = wAddr sP (t + c i) ∧ VG.Proof.MlKem.X86_64.BInvY sP w u)
    (fun u ou hu _ => ⟨by rw [ou.mem, og.mem]; exact hS,
      by rw [ou.keep.gpr (by decide), hdx, Nat.mul_zero, wAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [ou.keep.gpr (by decide), h8, hc0, Nat.add_zero], ⟨ou.keep.mono (by simp),
        by rw [ou.mem]; exact Frame.refl _ _,
        lanes_gpr (s := w) (GOnly.lane ou hu) (YOnly.refl [] w) cw (by decide) (by decide), ou.mxcsr⟩⟩)
    (fun i hi u ⟨hS', hdx', h8', hb'⟩ => ?_)) fun u ⟨hS', _, _, hb'⟩ =>
      ⟨hS', ⟨(og.keep.trans hb'.keep).mono (by simp), by rw [← og.mem]; exact hb'.frame, hb'.consts,
        by rw [hb'.mxcsr, og.mxcsr]⟩⟩
  have hT' : VG.Proof.MlKem.X86_64.TZ u.mem sP z := (by rw [og.mem]; exact hT : TZ w.mem sP z).frame hb'.frame
  have hw' : pR sP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hw
  rw [show ([.vmovdquLoad .l256 .xmm0 (VG.Impl.MlKem.X86_64.at_ .rdx 0), .vmovdquLoad .l256 .xmm4 (VG.Impl.MlKem.X86_64.at_ .rdx 32)] : List Instr) ++ zeta ++
      ([.alu .add .r8 (.imm dz)] : List Instr) ++ toY (gath ++ bf ++ scat) ++
      ([.vmovdquStore .l256 (VG.Impl.MlKem.X86_64.at_ .rdx 0) .xmm0, .vmovdquStore .l256 (VG.Impl.MlKem.X86_64.at_ .rdx 32) .xmm1, .alu .add .rdx (.imm 64)] : List Instr) ++
      ([.alu .sub .rcx (.imm 1)] : List Instr) = VG.Proof.MlKem.X86_64.ybody42 (gath ++ bf ++ scat) zeta dz by simp [List.append_assoc]]
  refine WP.mono (VG.Proof.MlKem.X86_64.ystep42 hY (j := 32 * i) (by bdd_omega 256) hb'.consts hdx' hS' hw'
    (fun s' k => hz i hi s' (by rw [k.gpr, h8']) (by rw [k.mem]; exact hT') (by rw [k.wr]; exact hw'))
    (hcore i hi) (hR i hi))
    fun u' ⟨hS'', hdx'', h8'', hcx, hzf, hb''⟩ => ⟨⟨hS'', by rw [hdx'', Nat.mul_succ],
      by rw [h8'', h8', hdz i hi], hb'.trans hb''⟩, hcx, hzf⟩

theorem sel_A0 {j : Nat} (hj : j < 4) : sel 0xA0 j = 2 * (j / 2) := by
  rcases (by bdd_omega 256 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide

theorem sel_F5 {j : Nat} (hj : j < 4) : sel 0xF5 j = 1 + 2 * (j / 2) := by
  rcases (by bdd_omega 256 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} (hbf : VBflyOk bf op)
  {blk : VG.Spec.MlKem.Poly → Nat → Nat → Nat → Nat → VG.Spec.MlKem.Poly} (hblk : BlkOk blk op)
include hbf hblk

theorem ylay4_ok (hY : laneSseBlock (toY (gath4 ++ bf ++ scat4)) = some (gath4 ++ bf ++ scat4))
    {sP : Addr} {t : Nat} (zi : Nat → Nat) {z : Nat → Zq}
    (hz : ∀ c < 32, t + c < 128 ∧ z (t + c) = zeta (zi c))
    {F : VG.Spec.MlKem.Poly} {s : State} (hc : YConsts s) (hsi : s.gpr .rsi = sP) (hS : S16 s.mem (spW sP) F)
    (hT : VG.Proof.MlKem.X86_64.TZ s.mem sP z) (hw : pR sP ∈ s.wr) :
    WP isa (ylay4 bf t) s fun s' => S16 s'.mem (spW sP) (layF blk F 4 zi 32) ∧ VG.Proof.MlKem.X86_64.BInvY sP s s' := by
  have ht : t < 128 := by have := (hz 0 (by decide)).1; omega
  have hF : ∀ m, m ≤ 8 → ∀ j, 32 * m ≤ j → j < 256 → (layF blk F 4 zi (4 * m))[j]! = F[j]! := fun m hm j h1 h2 => by
    rw [VG.Proof.MlKem.X86_64.layF_get hblk F (by decide) zi (by bdd_omega 256) h2, ite_eq_right_of_eq_false _ _ (eq_false (by bdd_omega 256))]
  refine VG.Proof.MlKem.X86_64.ylay42_loop hY ht (fun m => 4 * m) rfl (fun m _ => by
      rw [show BitVec.signExtend 64 (8 : BitVec 32) = BitVec.ofNat 64 (2 * 4) by decide, wAddr_add,
        show t + 4 * m + 4 = t + 4 * (m + 1) by bdd_omega 256])
    (fun m => layF blk F 4 zi (4 * m)) (fun m l e => zeta (zi (4 * m + l + 2 * (e / 4))))
    (fun m hm s' h8 hT' hw' => WP.mono (VG.Proof.MlKem.X86_64.yzetaS_ok 0xA0 0xF5 (zP := sP) (z := z) (k := t + 4 * m)
        (fun j hj => by rw [VG.Proof.MlKem.X86_64.sel_A0 hj]; have := (hz (4 * m + 3) (by bdd_omega 256)).1; omega)
        (fun j hj => by rw [VG.Proof.MlKem.X86_64.sel_F5 hj]; have := (hz (4 * m + 3) (by bdd_omega 256)).1; omega) h8
        (tab_in (List.mem_append_right _ hw') (by bdd_omega 256)) hT')
      fun s'' ⟨Z0, Z1, o⟩ => ⟨fun l hl => ?_, o.mono (by simp)⟩) (fun m hm l hl t' hc' hA hB hZ => ?_) ?_ hc hsi
    hS hT hw
  · rcases lane01 hl with rfl | rfl
    · exact Z0.congr fun i hi => by
        rw [VG.Proof.MlKem.X86_64.sel_A0 (by bdd_omega 256), show t + 4 * m + 2 * (i / 2 / 2) = t + (4 * m + 0 + 2 * (i / 4)) by bdd_omega 256,
          (hz _ (by bdd_omega 256)).2]
    · exact Z1.congr fun i hi => by
        rw [VG.Proof.MlKem.X86_64.sel_F5 (by bdd_omega 256), show t + 4 * m + (1 + 2 * (i / 2 / 2)) = t + (4 * m + 1 + 2 * (i / 4)) by bdd_omega 256,
          (hz _ (by bdd_omega 256)).2]
  · refine WP.mono (VG.Proof.MlKem.X86_64.core4_ok hbf hc' hA hB hZ) fun t'' ⟨⟨a, b⟩, o⟩ => ⟨⟨a.congr fun e he => ?_, b.congr fun e he => ?_⟩, o⟩
    · have hR := VG.Proof.MlKem.X86_64.layF_get hblk F (len := 4) (by decide) zi (b := 4 * (m + 1)) (by bdd_omega 256) (show 32 * m + 8 * l + e < 256 by bdd_omega 256)
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 32 * m + 8 * l + e < 2 * 4 * (4 * (m + 1)) by bdd_omega 256)),
        show (32 * m + 8 * l + e) / (2 * 4) = 4 * m + l by bdd_omega 256] at hR
      rw [hR]
      by_cases h : e < 4
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h),
          ite_eq_left_of_eq_true _ _ (eq_true (show (32 * m + 8 * l + e) % (2 * 4) < 4 by bdd_omega 256)),
          hF m (by bdd_omega 256) (32 * m + 8 * l + e) (by bdd_omega 256) (by bdd_omega 256),
          hF m (by bdd_omega 256) (32 * m + 8 * l + (4 + e)) (by bdd_omega 256) (by bdd_omega 256),
          show 32 * m + 8 * l + (4 + e) = 32 * m + 8 * l + e + 4 by bdd_omega 256, show 4 * m + l + 2 * (e / 4) = 4 * m + l by bdd_omega 256]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h),
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (32 * m + 8 * l + e) % (2 * 4) < 4 by bdd_omega 256)),
          hF m (by bdd_omega 256) (32 * m + 8 * l + (e - 4)) (by bdd_omega 256) (by bdd_omega 256),
          hF m (by bdd_omega 256) (32 * m + 8 * l + e) (by bdd_omega 256) (by bdd_omega 256),
          show 32 * m + 8 * l + (e - 4) = 32 * m + 8 * l + e - 4 by bdd_omega 256,
          show 4 * m + l + 2 * ((e - 4) / 4) = 4 * m + l by bdd_omega 256]
    · have hR := VG.Proof.MlKem.X86_64.layF_get hblk F (len := 4) (by decide) zi (b := 4 * (m + 1)) (by bdd_omega 256)
        (show 32 * m + 16 + 8 * l + e < 256 by bdd_omega 256)
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 32 * m + 16 + 8 * l + e < 2 * 4 * (4 * (m + 1)) by bdd_omega 256)),
        show (32 * m + 16 + 8 * l + e) / (2 * 4) = 4 * m + l + 2 by bdd_omega 256] at hR
      rw [hR]
      by_cases h : e < 4
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h),
          ite_eq_left_of_eq_true _ _ (eq_true (show (32 * m + 16 + 8 * l + e) % (2 * 4) < 4 by bdd_omega 256)),
          hF m (by bdd_omega 256) (32 * m + 16 + 8 * l + e) (by bdd_omega 256) (by bdd_omega 256),
          hF m (by bdd_omega 256) (32 * m + 16 + 8 * l + (4 + e)) (by bdd_omega 256) (by bdd_omega 256),
          show 32 * m + 16 + 8 * l + (4 + e) = 32 * m + 16 + 8 * l + e + 4 by bdd_omega 256,
          show 4 * m + l + 2 * ((4 + e) / 4) = 4 * m + l + 2 by bdd_omega 256]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h),
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (32 * m + 16 + 8 * l + e) % (2 * 4) < 4 by bdd_omega 256)),
          hF m (by bdd_omega 256) (32 * m + 16 + 8 * l + (e - 4)) (by bdd_omega 256) (by bdd_omega 256),
          hF m (by bdd_omega 256) (32 * m + 16 + 8 * l + e) (by bdd_omega 256) (by bdd_omega 256),
          show 32 * m + 16 + 8 * l + (e - 4) = 32 * m + 16 + 8 * l + e - 4 by bdd_omega 256,
          show 4 * m + l + 2 * (e / 4) = 4 * m + l + 2 by bdd_omega 256]
  · intro m hm i hi h
    rw [VG.Proof.MlKem.X86_64.layF_get hblk F (by decide) zi (by bdd_omega 256) hi, VG.Proof.MlKem.X86_64.layF_get hblk F (by decide) zi (by bdd_omega 256) hi]
    rcases h with h | h
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (show i < 2 * 4 * (4 * (m + 1)) by bdd_omega 256)),
        ite_eq_left_of_eq_true _ _ (eq_true (show i < 2 * 4 * (4 * m) by bdd_omega 256))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ i < 2 * 4 * (4 * (m + 1)) by bdd_omega 256)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ i < 2 * 4 * (4 * m) by bdd_omega 256))]

theorem ylay2_ok (hY : laneSseBlock (toY (gath2 ++ bf ++ scat2)) = some (gath2 ++ bf ++ scat2))
    {sP : Addr} {t : Nat} (zi : Nat → Nat) {z : Nat → Zq}
    (hz : ∀ c < 64, t + c < 128 ∧ z (t + c) = zeta (zi c))
    {F : VG.Spec.MlKem.Poly} {s : State} (hc : YConsts s) (hsi : s.gpr .rsi = sP) (hS : S16 s.mem (spW sP) F)
    (hT : VG.Proof.MlKem.X86_64.TZ s.mem sP z) (hw : pR sP ∈ s.wr) :
    WP isa (ylay2 bf t) s fun s' => S16 s'.mem (spW sP) (layF blk F 2 zi 64) ∧ VG.Proof.MlKem.X86_64.BInvY sP s s' := by
  have ht : t < 128 := by have := (hz 0 (by decide)).1; omega
  have hF : ∀ m, m ≤ 8 → ∀ j, 32 * m ≤ j → j < 256 → (layF blk F 2 zi (8 * m))[j]! = F[j]! := fun m hm j h1 h2 => by
    rw [VG.Proof.MlKem.X86_64.layF_get hblk F (by decide) zi (by bdd_omega 256) h2, ite_eq_right_of_eq_false _ _ (eq_false (by bdd_omega 256))]
  refine VG.Proof.MlKem.X86_64.ylay42_loop hY ht (fun m => 8 * m) rfl (fun m _ => by
      rw [show BitVec.signExtend 64 (16 : BitVec 32) = BitVec.ofNat 64 (2 * 8) by decide, wAddr_add,
        show t + 8 * m + 8 = t + 8 * (m + 1) by bdd_omega 256])
    (fun m => layF blk F 2 zi (8 * m)) (fun m l e => zeta (zi (8 * m + (2 * l + e / 2 + 2 * (e / 4)))))
    (fun m hm s' h8 hT' hw' => WP.mono (VG.Proof.MlKem.X86_64.yzeta8_ok (zP := sP) (z := z) (k := t + 8 * m)
        (by have := (hz (8 * m + 7) (by bdd_omega 256)).1; omega) h8 (tab_in (List.mem_append_right _ hw') (by bdd_omega 256)) hT')
      fun s'' ⟨Z, o⟩ => ⟨fun l hl => (Z l hl).congr fun i hi => by
        rw [Nat.add_assoc, (hz _ (by bdd_omega 256)).2], o.mono (by simp)⟩)
    (fun m hm l hl t' hc' hA hB hZ => ?_) ?_ hc hsi hS hT hw
  · refine WP.mono (VG.Proof.MlKem.X86_64.core2_ok hbf hc' hA hB hZ) fun t'' ⟨⟨a, b⟩, o⟩ => ⟨⟨a.congr fun e he => ?_, b.congr fun e he => ?_⟩, o⟩
    · have hR := VG.Proof.MlKem.X86_64.layF_get hblk F (len := 2) (by decide) zi (b := 8 * (m + 1)) (by bdd_omega 256)
        (show 32 * m + 8 * l + e < 256 by bdd_omega 256)
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 32 * m + 8 * l + e < 2 * 2 * (8 * (m + 1)) by bdd_omega 256)),
        show (32 * m + 8 * l + e) / (2 * 2) = 8 * m + (2 * l + (2 * (e / 4) + e % 2) / 2 +
          2 * ((2 * (e / 4) + e % 2) / 4)) by bdd_omega 256] at hR
      rw [hR]
      by_cases h : e % 4 < 2
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h),
          ite_eq_left_of_eq_true _ _ (eq_true (show (32 * m + 8 * l + e) % (2 * 2) < 2 by bdd_omega 256)),
          hF m (by bdd_omega 256) (32 * m + 8 * l + e) (by bdd_omega 256) (by bdd_omega 256),
          hF m (by bdd_omega 256) (32 * m + 8 * l + (e + 2)) (by bdd_omega 256) (by bdd_omega 256),
          show 32 * m + 8 * l + (e + 2) = 32 * m + 8 * l + e + 2 by bdd_omega 256]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h),
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (32 * m + 8 * l + e) % (2 * 2) < 2 by bdd_omega 256)),
          hF m (by bdd_omega 256) (32 * m + 8 * l + (e - 2)) (by bdd_omega 256) (by bdd_omega 256),
          hF m (by bdd_omega 256) (32 * m + 8 * l + e) (by bdd_omega 256) (by bdd_omega 256),
          show 32 * m + 8 * l + (e - 2) = 32 * m + 8 * l + e - 2 by bdd_omega 256]
    · have hR := VG.Proof.MlKem.X86_64.layF_get hblk F (len := 2) (by decide) zi (b := 8 * (m + 1)) (by bdd_omega 256)
        (show 32 * m + 16 + 8 * l + e < 256 by bdd_omega 256)
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 32 * m + 16 + 8 * l + e < 2 * 2 * (8 * (m + 1)) by bdd_omega 256)),
        show (32 * m + 16 + 8 * l + e) / (2 * 2) = 8 * m + (2 * l + (4 + 2 * (e / 4) + e % 2) / 2 +
          2 * ((4 + 2 * (e / 4) + e % 2) / 4)) by bdd_omega 256] at hR
      rw [hR]
      by_cases h : e % 4 < 2
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h),
          ite_eq_left_of_eq_true _ _ (eq_true (show (32 * m + 16 + 8 * l + e) % (2 * 2) < 2 by bdd_omega 256)),
          hF m (by bdd_omega 256) (32 * m + 16 + 8 * l + e) (by bdd_omega 256) (by bdd_omega 256),
          hF m (by bdd_omega 256) (32 * m + 16 + 8 * l + (e + 2)) (by bdd_omega 256) (by bdd_omega 256),
          show 32 * m + 16 + 8 * l + (e + 2) = 32 * m + 16 + 8 * l + e + 2 by bdd_omega 256]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h),
          ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (32 * m + 16 + 8 * l + e) % (2 * 2) < 2 by bdd_omega 256)),
          hF m (by bdd_omega 256) (32 * m + 16 + 8 * l + (e - 2)) (by bdd_omega 256) (by bdd_omega 256),
          hF m (by bdd_omega 256) (32 * m + 16 + 8 * l + e) (by bdd_omega 256) (by bdd_omega 256),
          show 32 * m + 16 + 8 * l + (e - 2) = 32 * m + 16 + 8 * l + e - 2 by bdd_omega 256]
  · intro m hm i hi h
    rw [VG.Proof.MlKem.X86_64.layF_get hblk F (by decide) zi (by bdd_omega 256) hi, VG.Proof.MlKem.X86_64.layF_get hblk F (by decide) zi (by bdd_omega 256) hi]
    rcases h with h | h
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (show i < 2 * 2 * (8 * (m + 1)) by bdd_omega 256)),
        ite_eq_left_of_eq_true _ _ (eq_true (show i < 2 * 2 * (8 * m) by bdd_omega 256))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ i < 2 * 2 * (8 * (m + 1)) by bdd_omega 256)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ i < 2 * 2 * (8 * m) by bdd_omega 256))]

end

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.YNttPack`. -/
section

/-!
# ML-KEM on x86-64: the NTT and its inverse on AVX2 registers, before and after the layers

The packing of the 256 `u32`s of `f` into the words of `S`, sixteen at a time
(`ypack_ok`), their unpacking back (`yunpack_ok`), the multiplication by
`3303` of `NTT⁻¹` (`yscale_ok`), and the prologue and epilogue around them
(`ypro_ok`, `yepi_ok`); and the facts kept between the layers (`LIY`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## Packing -/

/-- The eight coefficients of a reduced polynomial, four at `coeffAddr p j`
and four at `coeffAddr p j'`, as the words `packssdw` makes of them. -/
theorem lanes_pack2 {m : Mem} {p : Addr} {F : VG.Spec.MlKem.Poly} (hF : PolyIs m p F) {j j' : Nat} (hj : j + 4 ≤ 256)
    (hj' : j' + 4 ≤ 256) :
    VG.Proof.MlKem.X86_64.Lanes (XBinOp.eval .packssdw (m.readW (coeffAddr p j) 128) (m.readW (coeffAddr p j') 128))
      (fun e => if e < 4 then F[j + e]! else F[j' + (e - 4)]!) := fun e he => by
  have hc : ∀ k, k < 256 → (coeffAt m p k).toNat = (F[k]!).val := fun k hk =>
    polyIs_toNat hF (by rw [n_eq]; exact hk)
  rw [word_packssdw_small _ _ he (fun k hk => by
      rw [dword_readW _ _ hk, coeffAddr_off, ← coeffAt_eq, hc _ (by bdd_omega)]; have := val_lt F[j + k]!; omega)
    (fun k hk => by
      rw [dword_readW _ _ hk, coeffAddr_off, ← coeffAt_eq, hc _ (by bdd_omega)]; have := val_lt F[j' + k]!; omega)]
  split
  · rw [dword_readW _ _ (by bdd_omega), coeffAddr_off, ← coeffAt_eq, hc _ (by bdd_omega)]; dsimp only; rw [ifp ‹_›]
  · rw [dword_readW _ _ (by bdd_omega), coeffAddr_off, ← coeffAt_eq, hc _ (by bdd_omega)]; dsimp only; rw [ifn ‹_›]

/-- `vpackssdw ymm0, ymm0, ymm1` in each lane. -/
theorem zpack_ok (t : State) :
    WP isa (.block [xb .packssdw .xmm0 .xmm1]) t
      fun t' => t'.xmm .xmm0 = XBinOp.eval .packssdw (t.xmm .xmm0) (t.xmm .xmm1) ∧ XOnly [.xmm0] t t' := by
  simp only [xb]
  vrun
  exact ⟨trivial, by xonly⟩

theorem ypack_ok {fP sP : Addr} {F : VG.Spec.MlKem.Poly} {s : State} (hc : YConsts s) (hF : PolyIs s.mem fP F)
    (h9 : s.gpr .r9 = fP) (hdx : s.gpr .rdx = spW sP) (hrf : pR fP ∈ s.rd ++ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR fP).Disjoint (pR sP)) :
    WP isa ypack s fun s' => S16 s'.mem (spW sP) F ∧ Frame [sR (spW sP)] s.mem s'.mem ∧ YConsts s' ∧
      Keep [.r9, .rdx, .rcx] s s' ∧ s'.mxcsr = s.mxcsr := by
  have hsub : Region.Sub (sR (spW sP)) (pR sP) := Offset.sub_base sP (by bdd_omega)
  refine WP.mono (wp_rcxLoopY (N := 16) (by decide) (by decide)
    (fun u w => S16p w.mem (spW sP) F (16 * u) ∧ w.gpr .r9 = coeffAddr fP (16 * u) ∧
      w.gpr .rdx = wAddr (spW sP) (16 * u) ∧ Frame [sR (spW sP)] s.mem w.mem ∧ YConsts w ∧
      Keep [.r9, .rdx, .rcx] s w ∧ w.mxcsr = s.mxcsr)
    (fun w o hy hcx => ⟨fun _ h => absurd h (by bdd_omega), by rw [o.keep.gpr (by decide), h9, coeffAddr]; simp,
      by rw [o.keep.gpr (by decide), hdx, wAddr]; simp, by rw [o.mem]; exact Frame.refl _ _,
      lanes_gpr (s := s) (GOnly.lane o hy) (YOnly.refl [] s) hc (by decide) (by decide),
      o.keep.mono (by simp), o.mxcsr⟩)
    (fun u hu w ⟨hP, h9', hdx', hf, hc', hk', hx'⟩ => ?_))
    fun w ⟨hP, _, _, hf, hc', hk', hx'⟩ => ⟨hP, hf, hc', hk', hx'⟩
  have hF' : PolyIs w.mem fP F := polyIs_frame hf (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hd.sub_right hsub) hF
  have hrf' : pR fP ∈ w.rd ++ w.wr := by rw [hk'.2.1, hk'.2.2]; exact hrf
  have hw' : pR sP ∈ w.wr := by rw [hk'.2.2]; exact hw
  have a1 : coeffAddr fP (16 * u) + BitVec.ofNat 64 32 = coeffAddr fP (16 * u + 8) := coeffAddr_off _ _ 8
  have r0 : InRegions (w.rd ++ w.wr) (w.gpr .r9 + BitVec.ofNat 64 0) 32 :=
    ⟨_, hrf', by rw [h9', add_ofNat_zero]; exact Offset.contains_base fP (by bdd_omega) (by bdd_omega)⟩
  have r1 : InRegions (w.rd ++ w.wr) (w.gpr .r9 + BitVec.ofNat 64 32) 32 :=
    ⟨_, hrf', by rw [h9', a1]; exact Offset.contains_base fP (by bdd_omega) (by bdd_omega)⟩
  rw [show ∀ a b c d e f g : Instr, [a, b, c, d, e, f, g] ++ ([.alu .sub .rcx (.imm 1)] : List Instr) =
      [a] ++ ([b] ++ ([c] ++ ([d] ++ [e, f, g, .alu .sub .rcx (.imm 1)]))) from fun _ _ _ _ _ _ _ => rfl,
    WP.block_append_iff]
  refine WP.mono (yld_ok r0) fun s1 ⟨L0, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr]; exact r1)) fun s2 ⟨L1, o2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes (vs := [yb .vpackssdw .xmm0 .xmm0 .xmm1]) (by decide)
    (P := fun l t => t.xmm .xmm0 = XBinOp.eval .packssdw (s2.lane .xmm0 l) (s2.lane .xmm1 l))
    fun l _ => VG.Proof.MlKem.X86_64.zpack_ok (s2.proj l)) fun s3 ⟨P3, o3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.ypermq_ok s3) fun s4 ⟨Q0, Q1, o4⟩ => ?_
  have o14 := ((o1.trans o2).trans o3).trans o4
  have w0 : InRegions s4.wr (s4.gpr .rdx) 32 := by rw [o14.wr, o14.gpr, hdx']; exact VG.Proof.MlKem.X86_64.sp_inY hw' (by bdd_omega)
  vrunm [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd, State.setMem_ymm,
    State.setMem_setMem, w0, sx32, sx_ofNat (show 64 < 2 ^ 31 by decide)]
  -- the words of lane `l` of `ymm0`
  have lane0 : ∀ l < 2, s2.lane .xmm0 l = w.mem.readW (coeffAddr fP (16 * u + 4 * l)) 128 := fun l hl => by
    rw [o2.lane _ (by decide) l hl, L0 l hl, h9', add_ofNat_zero, show 16 * l = 4 * (4 * l) by bdd_omega, coeffAddr_off]
  have lane1 : ∀ l < 2, s2.lane .xmm1 l = w.mem.readW (coeffAddr fP (16 * u + 8 + 4 * l)) 128 := fun l hl => by
    rw [L1 l hl, o1.gpr, o1.mem, h9', a1, show 16 * l = 4 * (4 * l) by bdd_omega, coeffAddr_off]
  have pk : ∀ l < 2, VG.Proof.MlKem.X86_64.Lanes (s3.lane .xmm0 l) (fun e => if e < 4 then F[16 * u + 4 * l + e]!
      else F[16 * u + 8 + 4 * l + (e - 4)]!) := fun l hl => by
    have e : s3.lane .xmm0 l = _ := P3 l hl
    rw [e, lane0 l hl, lane1 l hl]; exact VG.Proof.MlKem.X86_64.lanes_pack2 hF' (by bdd_omega) (by bdd_omega)
  have Y : ∀ l < 2, VG.Proof.MlKem.X86_64.Lanes (s4.lane .xmm0 l) (fun e => F[16 * u + 8 * l + e]!) := fun l hl => by
    rcases lane01 hl with rfl | rfl
    · rw [Q0]; intro e he; rw [word_punpcklqdq _ _ he]
      split
      · rw [pk 0 (by decide) e he]; dsimp only; rw [ite_eq_left_of_eq_true _ _ (eq_true ‹e < 4›)]
      · rw [pk 1 (by decide) (e - 4) (by bdd_omega)]; dsimp only
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show e - 4 < 4 by bdd_omega))]
        exact congrArg _ (congrArg _ (by bdd_omega))
    · rw [Q1]; intro e he; rw [word_punpckhqdq _ _ he]
      split
      · rw [pk 0 (by decide) (4 + e) (by bdd_omega)]; dsimp only
        rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 4 + e < 4 by bdd_omega))]
        exact congrArg _ (congrArg _ (by bdd_omega))
      · rw [pk 1 (by decide) e he]; dsimp only
        rw [ite_eq_right_of_eq_false _ _ (eq_false ‹¬ e < 4›)]
        exact congrArg _ (congrArg _ (by bdd_omega))
  have dx4 : s4.gpr .rdx = wAddr (spW sP) (16 * u) := by rw [o14.gpr, hdx']
  have r94 : s4.gpr .r9 = coeffAddr fP (16 * u) := by rw [o14.gpr, h9']
  rw [dx4, r94, o14.mem]
  refine ⟨⟨fun j hj => ?_, by rw [show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 (4 * 16) by decide,
      coeffAddr_off, Nat.mul_succ], by rw [show (32 : BitVec 64) = BitVec.ofNat 64 (2 * 16) from rfl, wAddr_add,
      Nat.mul_succ], ?_, ?_, ?_, ?_⟩, by rw [o14.gpr], by rw [o14.gpr]⟩
  · rw [VG.Proof.MlKem.X86_64.wordAt_write256 _ _ (by bdd_omega) _ (by bdd_omega)]
    split
    · rw [VG.Proof.MlKem.X86_64.word_ymm _ _ (by bdd_omega), Y _ (by bdd_omega) _ (Nat.mod_lt _ (by bdd_omega))]
      exact congrArg _ (congrArg _ (by bdd_omega))
    · exact hP j (by bdd_omega)
  · exact hf.trans ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.MlKem.X86_64.sR_containsY _ (by bdd_omega)))
  · exact lanes_gpr (s := s4) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o14 hc'
      (by decide) (by decide)
  · refine ⟨fun r hr => ?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o14.rd]; exact hk'.2.1,
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o14.wr]; exact hk'.2.2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, State.setMem_gpr, hr, ite_false]
    rw [o14.gpr]; exact hk'.gpr (by simp [hr])
  · exact o14.mxcsr.trans hx'

/-! ## Unpacking -/

/-- Doubleword `q` of a 256-bit register, as stored. -/
theorem dword_ymm (s : State) (r : XReg) {q : Nat} (hq : q < 8) :
    (s.ymm r).extractLsb' (8 * (4 * q)) (8 * 4) = dword (s.lane r (q / 4)) (q % 4) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [State.ymm, State.lane, dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    decide_eq_true hj, Bool.true_and]
  by_cases h : q < 4
  · simp only [show 8 * (4 * q) + j < 128 by bdd_omega, ite_true, show q / 4 = 0 by bdd_omega]
    exact congrArg _ (by bdd_omega)
  · simp only [show ¬ 8 * (4 * q) + j < 128 by bdd_omega, ite_false, show q / 4 = 1 by bdd_omega, Nat.one_ne_zero]
    exact congrArg _ (by bdd_omega)

/-- `vpxor ymm4, ymm4, ymm4` in each lane. -/
theorem zxor_ok (t : State) :
    WP isa (.block [xb .pxor .xmm4 .xmm4]) t fun t' => t'.xmm .xmm4 = 0 ∧ XOnly [.xmm4] t t' := by
  simp only [xb]
  vrun
  exact ⟨by simp only [XBinOp.eval, BitVec.xor_self]; rfl, by xonly⟩

/-- `vpunpckhwd ymm1, ymm0, ymm4` and `vpunpcklwd ymm0, ymm0, ymm4` in each lane. -/
theorem zunpk_ok (t : State) :
    WP isa (.block [xb .movdqa .xmm1 .xmm0, xb .punpckhwd .xmm1 .xmm4, xb .punpcklwd .xmm0 .xmm4]) t fun t' =>
      (t'.xmm .xmm1 = XBinOp.eval .punpckhwd (t.xmm .xmm0) (t.xmm .xmm4) ∧
        t'.xmm .xmm0 = XBinOp.eval .punpcklwd (t.xmm .xmm0) (t.xmm .xmm4)) ∧ XOnly [.xmm1, .xmm0] t t' := by
  simp only [xb]
  vrun
  exact ⟨⟨rfl, trivial⟩, by xonly⟩

theorem yunpack_ok {fP sP : Addr} {F : VG.Spec.MlKem.Poly} {s : State} (hc : YConsts s) (hS : S16 s.mem (spW sP) F)
    (h9 : s.gpr .r9 = fP) (hdx : s.gpr .rdx = spW sP) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR fP).Disjoint (pR sP)) :
    WP isa yunpack s fun s' => PolyIs s'.mem fP F ∧ Frame [pR fP] s.mem s'.mem ∧ YConsts s' ∧
      Keep [.r9, .rdx, .rcx] s s' ∧ s'.mxcsr = s.mxcsr := by
  have hsub : Region.Sub (sR (spW sP)) (pR sP) := Offset.sub_base sP (by bdd_omega)
  refine WP.seq (WP.mono (ylanes (vs := [yb .vpxor .xmm4 .xmm4 .xmm4]) (by decide)
    (P := fun _ t => t.xmm .xmm4 = 0) fun l _ => VG.Proof.MlKem.X86_64.zxor_ok (s.proj l)) fun w0 ⟨hz, o0⟩ => ?_)
  refine WP.mono (wp_rcxLoopY (N := 16) (by decide) (by decide)
    (fun u w => PolyP w.mem fP F (16 * u) ∧ w.gpr .r9 = coeffAddr fP (16 * u) ∧
      w.gpr .rdx = wAddr (spW sP) (16 * u) ∧ Frame [pR fP] s.mem w.mem ∧ YConsts w ∧
      (∀ l < 2, w.lane .xmm4 l = 0) ∧ Keep [.r9, .rdx, .rcx] s w ∧ w.mxcsr = s.mxcsr)
    (fun w o hy hcx => ⟨fun _ h => absurd h (by bdd_omega),
      by rw [o.keep.gpr (by decide), o0.gpr, h9, coeffAddr]; simp,
      by rw [o.keep.gpr (by decide), o0.gpr, hdx, wAddr]; simp, by rw [o.mem, o0.mem]; exact Frame.refl _ _,
      lanes_gpr (s := w0) (GOnly.lane o hy) o0 hc (by decide) (by decide),
      fun l hl => by rw [GOnly.lane o hy]; exact hz l hl,
      Keep.trans (⟨fun r _ => by rw [o0.gpr], o0.rd, o0.wr⟩ : Keep [] s w0) (o.keep) |>.mono (by simp),
      by rw [o.mxcsr, o0.mxcsr]⟩)
    (fun u hu w ⟨hP, h9', hdx', hf, hc', hz', hk', hx'⟩ => ?_))
    fun w ⟨hP, _, _, hf, hc', _, hk', hx'⟩ => ⟨polyIs_of_toNat fun i hi => hP i (by rw [n_eq] at hi; omega),
      hf, hc', hk', hx'⟩
  have hS' : S16 w.mem (spW sP) F := hS.frame hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact (hd.sub_right hsub).symm
  have hwf' : pR fP ∈ w.wr := by rw [hk'.2.2]; exact hwf
  have r0 : InRegions (w.rd ++ w.wr) (w.gpr .rdx + BitVec.ofNat 64 0) 32 := by
    rw [hdx', add_ofNat_zero]; exact VG.Proof.MlKem.X86_64.sp_inY (List.mem_append_right _ (by rw [hk'.2.2]; exact hw)) (by bdd_omega)
  have a1 : coeffAddr fP (16 * u) + BitVec.ofNat 64 32 = coeffAddr fP (16 * u + 8) := coeffAddr_off _ _ 8
  rw [show ∀ a b c d e f g h : Instr, [a, b, c, d, e, f, g, h] ++ ([.alu .sub .rcx (.imm 1)] : List Instr) =
      [a] ++ ([b] ++ ([c, d] ++ [e, f, g, h, .alu .sub .rcx (.imm 1)])) from fun _ _ _ _ _ _ _ _ => rfl,
    WP.block_append_iff]
  refine WP.mono (yld_ok r0) fun s1 ⟨L0, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.ypermq_ok s1) fun s2 ⟨Q0, Q1, o2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes (vs := [yb .vpunpckhwd .xmm1 .xmm0 .xmm4, yb .vpunpcklwd .xmm0 .xmm0 .xmm4]) (by decide)
    (P := fun l t => t.xmm .xmm1 = XBinOp.eval .punpckhwd (s2.lane .xmm0 l) (s2.lane .xmm4 l) ∧
      t.xmm .xmm0 = XBinOp.eval .punpcklwd (s2.lane .xmm0 l) (s2.lane .xmm4 l))
    fun l _ => VG.Proof.MlKem.X86_64.zunpk_ok (s2.proj l)) fun s3 ⟨P3, o3⟩ => ?_
  have o13 := (o1.trans o2).trans o3
  have w0' : InRegions s3.wr (s3.gpr .r9) 32 := by
    rw [o13.wr, o13.gpr, h9']; exact ⟨_, hwf', Offset.contains_base fP (by bdd_omega) (by bdd_omega)⟩
  have w1' : InRegions s3.wr (s3.gpr .r9 + 32#64) 32 := by
    rw [o13.wr, o13.gpr, h9', a1]; exact ⟨_, hwf', Offset.contains_base fP (by bdd_omega) (by bdd_omega)⟩
  vrunm [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd, State.setMem_ymm,
    State.setMem_setMem, w0', w1', sx32, sx_ofNat (show 64 < 2 ^ 31 by decide)]
  have r93 : s3.gpr .r9 = coeffAddr fP (16 * u) := by rw [o13.gpr, h9']
  have dx3 : s3.gpr .rdx = wAddr (spW sP) (16 * u) := by rw [o13.gpr, hdx']
  have LA : ∀ l < 2, VG.Proof.MlKem.X86_64.Lanes (s1.lane .xmm0 l) (fun e => F[16 * u + 8 * l + e]!) := fun l hl => by
    rw [L0 l hl, hdx', add_ofNat_zero]; exact VG.Proof.MlKem.X86_64.lanes_loadY hS' (by bdd_omega) hl
  have Wlo : ∀ l < 2, ∀ e < 4, (word (s2.lane .xmm0 l) e).toNat = (F[16 * u + 4 * l + e]!).val := fun l hl e he => by
    rcases lane01 hl with rfl | rfl
    · rw [Q0, word_punpcklqdq _ _ (show e < 8 by bdd_omega), ifp he, LA 0 (by decide) e (by bdd_omega)]
    · rw [Q1, word_punpckhqdq _ _ (show e < 8 by bdd_omega), ifp he, LA 0 (by decide) _ (by bdd_omega)]
      exact congrArg _ (congrArg _ (by bdd_omega))
  have Whi : ∀ l < 2, ∀ e < 4, (word (s2.lane .xmm0 l) (4 + e)).toNat = (F[16 * u + 8 + 4 * l + e]!).val :=
    fun l hl e he => by
    rcases lane01 hl with rfl | rfl
    · rw [Q0, word_punpcklqdq _ _ (show 4 + e < 8 by bdd_omega), ifn (show ¬ 4 + e < 4 by bdd_omega), LA 1 (by decide) _ (by bdd_omega)]
      exact congrArg _ (congrArg _ (by bdd_omega))
    · rw [Q1, word_punpckhqdq _ _ (show 4 + e < 8 by bdd_omega), ifn (show ¬ 4 + e < 4 by bdd_omega), LA 1 (by decide) _ (by bdd_omega)]
      exact congrArg _ (congrArg _ (by bdd_omega))
  have Z2 : ∀ l < 2, s2.lane .xmm4 l = 0 := fun l hl => by
    rw [(o1.trans o2).lane _ (by decide) l hl]; exact hz' l hl
  have Y4 : ∀ l < 2, s3.lane .xmm4 l = 0 := fun l hl => by
    rw [o13.lane _ (by decide) l hl]; exact hz' l hl
  have Y0 : ∀ l < 2, s3.lane .xmm0 l = XBinOp.eval .punpcklwd (s2.lane .xmm0 l) 0 := fun l hl => by
    have e := (P3 l hl).2; rw [State.proj_xmm, Z2 l hl] at e; exact e
  have Y1 : ∀ l < 2, s3.lane .xmm1 l = XBinOp.eval .punpckhwd (s2.lane .xmm0 l) 0 := fun l hl => by
    have e := (P3 l hl).1; rw [State.proj_xmm, Z2 l hl] at e; exact e
  refine ⟨⟨fun j hj => ?_, by rw [r93, show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 (4 * 16) by decide,
      coeffAddr_off, Nat.mul_succ], by rw [dx3, show (32 : BitVec 64) = BitVec.ofNat 64 (2 * 16) from rfl, wAddr_add,
      Nat.mul_succ], ?_, ?_, ?_, ?_, ?_⟩, by rw [o13.gpr], by rw [o13.gpr]⟩
  · rw [r93, a1, coeffAt_write256 _ _ (by bdd_omega) _ (by bdd_omega), coeffAt_write256 _ _ (by bdd_omega) _ (by bdd_omega)]
    split
    · rw [VG.Proof.MlKem.X86_64.dword_ymm _ _ (by bdd_omega), Y1 _ (by bdd_omega), dword_punpckhwd0 _ (by bdd_omega), Whi _ (by bdd_omega) _ (by bdd_omega)]
      exact congrArg _ (congrArg _ (by bdd_omega))
    · split
      · rw [VG.Proof.MlKem.X86_64.dword_ymm _ _ (by bdd_omega), Y0 _ (by bdd_omega), dword_punpcklwd0 _ (by bdd_omega), Wlo _ (by bdd_omega) _ (by bdd_omega)]
        exact congrArg _ (congrArg _ (by bdd_omega))
      · rw [o13.mem]; exact hP j (by bdd_omega)
  · rw [r93, a1, o13.mem]
    exact hf.trans (((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (show (pR fP).Contains (coeffAddr fP (16 * u)) (256 / 8) from Offset.contains_base fP (by bdd_omega)
        (by bdd_omega))).writeW (List.mem_singleton_self _) _
      (show (pR fP).Contains (coeffAddr fP (16 * u + 8)) (256 / 8) from Offset.contains_base fP (by bdd_omega)
        (by bdd_omega)))
  · exact lanes_gpr (s := s3) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o13 hc'
      (by decide) (by decide)
  · intro l hl; simp only [lane_setReg, lane_setFlags, State.setMem_lane]; exact Y4 l hl
  · refine ⟨fun r hr => ?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o13.rd]; exact hk'.2.1,
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o13.wr]; exact hk'.2.2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, State.setMem_gpr, hr, ite_false]
    rw [o13.gpr]; exact hk'.gpr (by simp [hr])
  · exact o13.mxcsr.trans hx'

/-! ## The multiplication by 3303 -/

theorem lane_vmulc : laneSseBlock (toY (vmont .xmm3 .xmm13 .xmm2 ++ vcadd .xmm3 .xmm2)) =
    some (vmont .xmm3 .xmm13 .xmm2 ++ vcadd .xmm3 .xmm2) := by decide +kernel

/-- `3303 · 2¹⁶ mod q = 512` in every word, as `yscale` makes it. -/
theorem zlanes_512Y : ZLanes (ofDwords 0x02000200 0x02000200 0x02000200 0x02000200) fun _ => (3303 : Zq) :=
  fun i hi => by
  rcases (by bdd_omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem yscale_ok {sP : Addr} {F : VG.Spec.MlKem.Poly} {s : State} (hc : YConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hw : pR sP ∈ s.wr) :
    WP isa yscale s fun s' => S16 s'.mem (spW sP) (F.map (· * 3303)) ∧ VG.Proof.MlKem.X86_64.BInvY sP s s' := by
  simp only [yscale]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (w : State) => w.gpr .rdx = spW sP ∧ GOnly [.rdx] s w ∧ w.ymmHi = s.ymmHi)
    (by
      simp only [leaR, oS]
      vrunm [sx_ofNat (show 256 < 2 ^ 31 by decide), hsi, RegUpd.ymmHi_setReg]
      exact ⟨by gonly, rfl⟩) fun w1 ⟨hdx1, og, hy⟩ => ?_
  refine WP.mono (yconst_ok .xmm13 _ w1) fun w2 ⟨q2, k2, m2, x2, o2⟩ => ?_
  have hl1 := GOnly.lane og hy
  have cw2 : YConsts w2 := fun l hl => by
    have h15 := (hc l hl).q; have h14 := (hc l hl).qinv
    rw [State.proj_xmm] at h15 h14
    exact ⟨by rw [State.proj_xmm, o2 _ (by decide) l hl, hl1]; exact h15,
      by rw [State.proj_xmm, o2 _ (by decide) l hl, hl1]; exact h14⟩
  have kw2 : Keep [.r8, .rcx, .rdx, .rax] s w2 := (og.keep.trans k2).mono (by simp)
  have hdx2 : w2.gpr .rdx = spW sP := by rw [k2.gpr (by decide), hdx1]
  have mw2 : w2.mem = s.mem := by rw [m2, og.mem]
  have xw2 : w2.mxcsr = s.mxcsr := by rw [x2, og.mxcsr]
  refine WP.mono (wp_rcxLoopY (N := 16) (by decide) (by decide)
    (fun u v => (∀ j < 256, (wordAt v.mem (spW sP) j).toNat = (if j < 16 * u then F[j]! * 3303 else F[j]!).val) ∧
      v.gpr .rdx = wAddr (spW sP) (16 * u) ∧ (∀ l < 2, v.lane .xmm13 l = ofDwords 0x02000200 0x02000200 0x02000200 0x02000200) ∧
      VG.Proof.MlKem.X86_64.BInvY sP s v)
    (fun v o hy' _ => ⟨fun j hj => by rw [ite_eq_right (by bdd_omega), o.mem, mw2]; exact hS j hj,
      by rw [o.keep.gpr (by decide), hdx2, wAddr]; simp,
      fun l hl => by rw [GOnly.lane o hy']; exact q2 l hl,
      ⟨(kw2.trans o.keep).mono (by simp), by rw [o.mem, mw2]; exact Frame.refl _ _,
        lanes_gpr (s := w2) (GOnly.lane o hy') (YOnly.refl [] w2) cw2 (by decide) (by decide),
        by rw [o.mxcsr, xw2]⟩⟩)
    (fun u hu v ⟨hP, hdx', hz', hb⟩ => ?_))
    fun v ⟨hP, _, _, hb⟩ => ⟨fun j hj => by
      rw [hP j hj, ite_eq_left (by bdd_omega), map_mul_get _ (by rw [n_eq]; exact hj)], hb⟩
  have hw' : pR sP ∈ v.wr := by rw [hb.keep.2.2]; exact hw
  have r0 : InRegions (v.rd ++ v.wr) (v.gpr .rdx + BitVec.ofNat 64 0) 32 := by
    rw [hdx', add_ofNat_zero]; exact VG.Proof.MlKem.X86_64.sp_inY (List.mem_append_right _ hw') (by bdd_omega)
  rw [show ∀ (a : Instr) (b : List Instr) (c d : Instr), [a] ++ b ++ [c, d] ++ ([.alu .sub .rcx (.imm 1)] : List Instr) =
      [a] ++ (b ++ [c, d, .alu .sub .rcx (.imm 1)]) from fun _ _ _ _ => by simp,
    WP.block_append_iff]
  refine WP.mono (yld_ok r0) fun s1 ⟨L1, o1⟩ => ?_
  rw [WP.block_append_iff]
  have c1 : YConsts s1 := o1.consts hb.consts (by decide) (by decide)
  refine WP.mono (ylanes VG.Proof.MlKem.X86_64.lane_vmulc (P := fun l t => VG.Proof.MlKem.X86_64.Lanes (t.xmm .xmm3) (fun e => 3303 * F[16 * u + 8 * l + e]!))
    fun l hl => vmulc_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (c1 l hl)
      (fun e he => by
        rw [State.proj_xmm, L1 l hl, hdx', add_ofNat_zero, show 16 * l = 2 * (8 * l) by bdd_omega, wAddr_add,
          word_readW _ _ he, wAddr_add, ← wordAt, hP _ (by bdd_omega), ite_eq_right (by bdd_omega)])
      (by rw [State.proj_xmm, o1.lane _ (by decide) l hl, hz' l hl]; exact VG.Proof.MlKem.X86_64.zlanes_512Y)) fun s2 ⟨l2, o2⟩ => ?_
  have o12 := o1.trans o2
  have w0 : InRegions s2.wr (s2.gpr .rdx) 32 := by rw [o12.wr, o12.gpr, hdx']; exact VG.Proof.MlKem.X86_64.sp_inY hw' (by bdd_omega)
  vrunm [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd, State.setMem_ymm,
    w0, sx32]
  have dx2 : s2.gpr .rdx = wAddr (spW sP) (16 * u) := by rw [o12.gpr, hdx']
  have l2' : ∀ l < 2, VG.Proof.MlKem.X86_64.Lanes (s2.lane .xmm3 l) (fun e => 3303 * F[16 * u + 8 * l + e]!) := fun l hl => by
    have := l2 l hl; rwa [State.proj_xmm] at this
  rw [dx2, o12.mem]
  refine ⟨⟨fun j hj => ?_, by rw [show (32 : BitVec 64) = BitVec.ofNat 64 (2 * 16) from rfl, wAddr_add, Nat.mul_succ],
    fun l hl => ?_, hb.trans ⟨⟨fun r hr => ?_, by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd, o12.rd],
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr, o12.wr]⟩,
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.MlKem.X86_64.sR_containsY _ (by bdd_omega)), ?_,
      by simp only [RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]; exact o12.mxcsr⟩⟩,
    by rw [o12.gpr], by rw [o12.gpr]⟩
  · rw [VG.Proof.MlKem.X86_64.wordAt_write256 _ _ (by bdd_omega) _ hj]
    split
    · rw [VG.Proof.MlKem.X86_64.word_ymm _ _ (by bdd_omega), l2' _ (by bdd_omega) _ (Nat.mod_lt _ (by bdd_omega)), ite_eq_left (by bdd_omega),
        Fin.mul_comm]
      dsimp only; rw [show 16 * u + 8 * ((j - 16 * u) / 8) + (j - 16 * u) % 8 = j by bdd_omega]
    · rw [hP j hj]
      by_cases h : j < 16 * u
      · rw [ite_eq_left h, ite_eq_left (by bdd_omega)]
      · rw [ite_eq_right h, ite_eq_right (by bdd_omega)]
  · simp only [lane_setReg, lane_setFlags, State.setMem_lane]
    rw [o12.lane _ (by decide) l hl]; exact hz' l hl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, State.setMem_gpr, hr, ite_false]
    rw [o12.gpr]
  · exact lanes_gpr (s := s2) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o12
      hb.consts (by decide) (by decide)

/-! ## The prologue and the epilogue -/

theorem yconsts_ok (s : State) :
    WP isa (.block yconsts) s fun s' => YConsts s' ∧ s'.mem = s.mem ∧ Keep [.rax] s s' := by
  simp only [yconsts]
  rw [WP.block_append_iff]
  refine WP.mono (yconst_ok .xmm15 _ s) fun s1 ⟨q1, k1, m1, _, _⟩ => ?_
  refine WP.mono (yconst_ok .xmm14 _ s1) fun s2 ⟨q2, k2, m2, _, o2⟩ => ?_
  refine ⟨fun l hl => ⟨?_, ?_⟩, by rw [m2, m1], (k1.trans k2).mono (by simp)⟩
  · rw [State.proj_xmm, o2 _ (by decide) l hl, q1 l hl]; decide
  · rw [State.proj_xmm, q2 l hl]; decide

/-- The table `tab` of the zetas `z` at `scratch`, `f` as words in `S`, and the constants. -/
theorem ypro_ok (tab : Nat → Nat) {z : Nat → Zq} (htab : ∀ k, tab k = (z k).val * 65536 % 3329)
    {fP sP : Addr} {F : VG.Spec.MlKem.Poly} {s : State} (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hF : PolyIs s.mem fP F) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) (hd : (pR fP).Disjoint (pR sP)) :
    WP isa (ypro tab) s fun s' => S16 s'.mem (spW sP) F ∧ VG.Proof.MlKem.X86_64.TZ s'.mem sP z ∧ YConsts s' ∧
      Frame [pR sP] s.mem s'.mem ∧ Keep [.rax, .rcx, .rdx, .r9] s s' := by
  simp only [ypro, List.append_assoc]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have htl : ∀ k, tab k < 65536 := fun k => by
    rw [htab k]; have := Nat.mod_lt ((z k).val * 65536) (show 3329 > 0 by decide); omega
  refine WP.mono (wordTab_gen tab htl (by decide) hsi hw) fun s1 ⟨hT, hf1, k1, _, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.yconsts_ok s1) fun s2 ⟨hc2, hm2, k2⟩ => ?_
  have k12 := k1.trans k2
  have hsi2 : s2.gpr .rsi = sP := by rw [k12.gpr (by decide), hsi]
  have hdi2 : s2.gpr .rdi = fP := by rw [k12.gpr (by decide), hdi]
  refine WP.mono (Q := fun (s3 : State) => s3.gpr .r9 = fP ∧ s3.gpr .rdx = spW sP ∧ GOnly [.r9, .rdx] s2 s3 ∧
      s3.ymmHi = s2.ymmHi)
    (by
      simp only [leaR, oS]
      vrunm [hsi2, hdi2, sx_ofNat (show 256 < 2 ^ 31 by decide), RegUpd.ymmHi_setReg]
      exact ⟨by gonly, rfl⟩) fun s3 ⟨h9, hdx, og, hy⟩ => ?_
  have k13 := k12.trans og.keep
  have hF3 : PolyIs s3.mem fP F := by
    rw [og.mem, hm2]
    exact polyIs_frame hf1 (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd.sub_right (pR_sub_tab sP)) hF
  have hT3 : VG.Proof.MlKem.X86_64.TZ s3.mem sP z := fun k hk => by rw [og.mem, hm2, hT k hk, htab]
  refine WP.mono (VG.Proof.MlKem.X86_64.ypack_ok (lanes_gpr (s := s2) (GOnly.lane og hy) (YOnly.refl [] s2) hc2 (by decide) (by decide))
    hF3 h9 hdx (by rw [k13.2.2]; exact List.mem_append_right _ hwf) (by rw [k13.2.2]; exact hw) hd)
    fun s4 ⟨hS, hf4, hc4, k4, _⟩ => ⟨hS, hT3.frame hf4, hc4, ?_, (k13.trans k4).mono (by simp)⟩
  refine (hf1.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
    ((og.mem.trans hm2) ▸ hf4.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
  · rw [List.mem_singleton.mp hr]; exact pR_sub_tab sP
  · rw [List.mem_singleton.mp hr]; exact pR_sub_S sP

/-- `S` unpacked into `f`, and the upper halves cleared. -/
theorem yepi_ok {fP sP : Addr} {F : VG.Spec.MlKem.Poly} {s : State} (hc : YConsts s) (hS : S16 s.mem (spW sP) F)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR fP).Disjoint (pR sP)) :
    WP isa yepi s fun s' => PolyIs s'.mem fP F ∧ Frame [pR fP] s.mem s'.mem := by
  simp only [yepi]
  refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .r9 = fP ∧ s1.gpr .rdx = spW sP ∧
      GOnly [.r9, .rdx] s s1 ∧ s1.ymmHi = s.ymmHi)
    (by
      simp only [leaR, oS]
      vrunm [hsi, hdi, sx_ofNat (show 256 < 2 ^ 31 by decide), RegUpd.ymmHi_setReg]
      exact ⟨by gonly, rfl⟩) fun s1 ⟨h9, hdx, og, hy⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.yunpack_ok (F := F) (lanes_gpr (s := s) (GOnly.lane og hy) (YOnly.refl [] s) hc (by decide)
    (by decide)) (by rw [og.mem]; exact hS) h9 hdx (by rw [og.keep.2.2]; exact hwf) (by rw [og.keep.2.2]; exact hw)
    hd) fun s2 ⟨hP, hf, _, _, _⟩ => ?_)
  vrunm
  exact ⟨hP, og.mem ▸ hf⟩

/-! ## Between the layers -/

/-- Between the layers: `S` holds `F`, and the table of `z` and the
constants are in place. -/
structure LIY (sP : Addr) (s₀ : State) (z : Nat → Zq) (F : VG.Spec.MlKem.Poly) (s : State) : Prop where
  S : S16 s.mem (spW sP) F
  T : VG.Proof.MlKem.X86_64.TZ s.mem sP z
  c : YConsts s
  keep : Keep [.rax, .rcx, .rdx, .r8] s₀ s
  frame : Frame [sR (spW sP)] s₀.mem s.mem

/-- A layer, then `c`. -/
theorem LIY.seq {sP : Addr} {s₀ : State} {z : Nat → Zq} (hsi : s₀.gpr .rsi = sP) (hw : pR sP ∈ s₀.wr)
    {l c : Prog isa} {F F' : VG.Spec.MlKem.Poly} {Q : State → Prop}
    (hl : ∀ s, YConsts s → s.gpr .rsi = sP → S16 s.mem (spW sP) F → VG.Proof.MlKem.X86_64.TZ s.mem sP z → pR sP ∈ s.wr →
      WP isa l s fun s' => S16 s'.mem (spW sP) F' ∧ VG.Proof.MlKem.X86_64.BInvY sP s s')
    (hc : ∀ s, VG.Proof.MlKem.X86_64.LIY sP s₀ z F' s → WP isa c s Q) {s : State} (hI : VG.Proof.MlKem.X86_64.LIY sP s₀ z F s) :
    WP isa (.seq l c) s Q :=
  WP.seq (WP.mono (hl s hI.c (by rw [hI.keep.gpr (by decide), hsi]) hI.S hI.T (by rw [hI.keep.2.2]; exact hw))
    fun s' ⟨hS, hb⟩ => hc s' ⟨hS, hI.T.frame hb.frame, hb.consts,
      (hI.keep.trans hb.keep).mono (by decide), hI.frame.trans hb.frame⟩)

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.NttAvx2`. -/
section

/-!
# ML-KEM on x86-64: `vg_mlkem_ntt_avx2` and `vg_mlkem_inv_ntt_avx2`

As `vg_mlkem_ntt` and `vg_mlkem_inv_ntt` (`Ntt.lean`, `NttInv.lean`), on
sixteen words at a time: the prologue leaves the table of zetas (in the order
the layers read it) and `f` as words in `scratch` (`ypro_ok`), each layer is
`nttLayer` or `nttInvLayer` (`ylay_ok`, `ylay8_ok`, `ylay4_ok`, `ylay2_ok`),
and the epilogue unpacks `S` into `f` (`yepi_ok`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## The butterflies in each lane -/

theorem lane_vbfly : laneSseBlock (toY vbfly) = some vbfly := by decide +kernel
theorem lane_vibfly : laneSseBlock (toY vibfly) = some vibfly := by decide +kernel
theorem lane_vbfly4 : laneSseBlock (toY (gath4 ++ vbfly ++ scat4)) = some (gath4 ++ vbfly ++ scat4) := by
  decide +kernel
theorem lane_vibfly4 : laneSseBlock (toY (gath4 ++ vibfly ++ scat4)) = some (gath4 ++ vibfly ++ scat4) := by
  decide +kernel
theorem lane_vbfly2 : laneSseBlock (toY (gath2 ++ vbfly ++ scat2)) = some (gath2 ++ vbfly ++ scat2) := by
  decide +kernel
theorem lane_vibfly2 : laneSseBlock (toY (gath2 ++ vibfly ++ scat2)) = some (gath2 ++ vibfly ++ scat2) := by
  decide +kernel

/-! ## The layers of `NTT` -/

/-- A layer of `NTT` with `len ≥ 16`, whose first zeta is `zeta t`. -/
theorem fwdLayY_ok {sP : Addr} (len t : Nat) (hlen : len ∈ [16, 32, 64, 128]) (ht : 128 / len = t)
    {F : VG.Spec.MlKem.Poly} (s : State) (hc : YConsts s) (hsi : s.gpr .rsi = sP) (hS : S16 s.mem (spW sP) F)
    (hT : VG.Proof.MlKem.X86_64.TZ s.mem sP zeta) (hw : pR sP ∈ s.wr) :
    WP isa (ylay vbfly len t) s fun s' => S16 s'.mem (spW sP) (nttLayer F len) ∧ VG.Proof.MlKem.X86_64.BInvY sP s s' := by
  subst ht
  have h8 : 128 / len ≤ 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl <;> decide
  rw [VG.Proof.MlKem.X86_64.nttLayer_eq]
  exact VG.Proof.MlKem.X86_64.ylay_ok vbfly_spec VG.Proof.MlKem.X86_64.lane_vbfly nttBlk_ok hlen (fun c => 128 / len + c) (fun c _ => ⟨by omega, rfl⟩)
    hc hsi hS hT hw

theorem fwdLay8Y_ok {sP : Addr} {F : VG.Spec.MlKem.Poly} (s : State) (hc : YConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hT : VG.Proof.MlKem.X86_64.TZ s.mem sP zeta) (hw : pR sP ∈ s.wr) :
    WP isa (ylay8 vbfly 16) s fun s' => S16 s'.mem (spW sP) (nttLayer F 8) ∧ VG.Proof.MlKem.X86_64.BInvY sP s s' := by
  rw [VG.Proof.MlKem.X86_64.nttLayer_eq]
  exact VG.Proof.MlKem.X86_64.ylay8_ok vbfly_spec VG.Proof.MlKem.X86_64.lane_vbfly nttBlk_ok (fun c => 16 + c) (fun c hc' => ⟨by omega, rfl⟩) hc hsi hS hT hw

theorem fwdLay4Y_ok {sP : Addr} {F : VG.Spec.MlKem.Poly} (s : State) (hc : YConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hT : VG.Proof.MlKem.X86_64.TZ s.mem sP zeta) (hw : pR sP ∈ s.wr) :
    WP isa (ylay4 vbfly 32) s fun s' => S16 s'.mem (spW sP) (nttLayer F 4) ∧ VG.Proof.MlKem.X86_64.BInvY sP s s' := by
  rw [VG.Proof.MlKem.X86_64.nttLayer_eq]
  exact VG.Proof.MlKem.X86_64.ylay4_ok vbfly_spec nttBlk_ok VG.Proof.MlKem.X86_64.lane_vbfly4 (fun c => 32 + c) (fun c hc' => ⟨by omega, rfl⟩) hc hsi hS hT hw

theorem fwdLay2Y_ok {sP : Addr} {F : VG.Spec.MlKem.Poly} (s : State) (hc : YConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hT : VG.Proof.MlKem.X86_64.TZ s.mem sP zeta) (hw : pR sP ∈ s.wr) :
    WP isa (ylay2 vbfly 64) s fun s' => S16 s'.mem (spW sP) (nttLayer F 2) ∧ VG.Proof.MlKem.X86_64.BInvY sP s s' := by
  rw [VG.Proof.MlKem.X86_64.nttLayer_eq]
  exact VG.Proof.MlKem.X86_64.ylay2_ok vbfly_spec nttBlk_ok VG.Proof.MlKem.X86_64.lane_vbfly2 (fun c => 64 + c) (fun c hc' => ⟨by omega, rfl⟩) hc hsi hS hT hw

/-! ## The layers of `NTT⁻¹` -/

/-- The zetas of `NTT⁻¹` in the order its layers read them. -/
abbrev zInv (k : Nat) : Zq := zeta (127 - k)

theorem zmTabInv_eq (k : Nat) : zmTabInv k = (VG.Proof.MlKem.X86_64.zInv k).val * 65536 % 3329 := zmTab_eq _

/-- A layer of `NTT⁻¹` with `len ≥ 16`, whose zetas start at entry `t` of
the table. -/
theorem invLayY_ok {sP : Addr} (len t : Nat) (hlen : len ∈ [16, 32, 64, 128])
    (ht : ∀ c < 128 / len, t + c < 128 ∧ 127 - (t + c) = 256 / len - 1 - c)
    {F : VG.Spec.MlKem.Poly} (s : State) (hc : YConsts s) (hsi : s.gpr .rsi = sP) (hS : S16 s.mem (spW sP) F)
    (hT : VG.Proof.MlKem.X86_64.TZ s.mem sP VG.Proof.MlKem.X86_64.zInv) (hw : pR sP ∈ s.wr) :
    WP isa (ylay vibfly len t) s fun s' => S16 s'.mem (spW sP) (nttInvLayer F len) ∧ VG.Proof.MlKem.X86_64.BInvY sP s s' := by
  rw [VG.Proof.MlKem.X86_64.nttInvLayer_eq]
  exact VG.Proof.MlKem.X86_64.ylay_ok vibfly_spec VG.Proof.MlKem.X86_64.lane_vibfly nttInvBlk_ok hlen (fun c => 256 / len - 1 - c) (z := VG.Proof.MlKem.X86_64.zInv)
    (fun c hc' => ⟨(ht c hc').1, congrArg zeta (ht c hc').2⟩) hc hsi hS hT hw

theorem invLay8Y_ok {sP : Addr} {F : VG.Spec.MlKem.Poly} (s : State) (hc : YConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hT : VG.Proof.MlKem.X86_64.TZ s.mem sP VG.Proof.MlKem.X86_64.zInv) (hw : pR sP ∈ s.wr) :
    WP isa (ylay8 vibfly 96) s fun s' => S16 s'.mem (spW sP) (nttInvLayer F 8) ∧ VG.Proof.MlKem.X86_64.BInvY sP s s' := by
  rw [VG.Proof.MlKem.X86_64.nttInvLayer_eq]
  exact VG.Proof.MlKem.X86_64.ylay8_ok vibfly_spec VG.Proof.MlKem.X86_64.lane_vibfly nttInvBlk_ok (fun c => 31 - c) (z := VG.Proof.MlKem.X86_64.zInv)
    (fun c hc' => ⟨by omega, congrArg zeta (by omega)⟩) hc hsi hS hT hw

theorem invLay4Y_ok {sP : Addr} {F : VG.Spec.MlKem.Poly} (s : State) (hc : YConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hT : VG.Proof.MlKem.X86_64.TZ s.mem sP VG.Proof.MlKem.X86_64.zInv) (hw : pR sP ∈ s.wr) :
    WP isa (ylay4 vibfly 64) s fun s' => S16 s'.mem (spW sP) (nttInvLayer F 4) ∧ VG.Proof.MlKem.X86_64.BInvY sP s s' := by
  rw [VG.Proof.MlKem.X86_64.nttInvLayer_eq]
  exact VG.Proof.MlKem.X86_64.ylay4_ok vibfly_spec nttInvBlk_ok VG.Proof.MlKem.X86_64.lane_vibfly4 (fun c => 63 - c) (z := VG.Proof.MlKem.X86_64.zInv)
    (fun c hc' => ⟨by omega, congrArg zeta (by omega)⟩) hc hsi hS hT hw

theorem invLay2Y_ok {sP : Addr} {F : VG.Spec.MlKem.Poly} (s : State) (hc : YConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hT : VG.Proof.MlKem.X86_64.TZ s.mem sP VG.Proof.MlKem.X86_64.zInv) (hw : pR sP ∈ s.wr) :
    WP isa (ylay2 vibfly 0) s fun s' => S16 s'.mem (spW sP) (nttInvLayer F 2) ∧ VG.Proof.MlKem.X86_64.BInvY sP s s' := by
  rw [VG.Proof.MlKem.X86_64.nttInvLayer_eq]
  exact VG.Proof.MlKem.X86_64.ylay2_ok vibfly_spec nttInvBlk_ok VG.Proof.MlKem.X86_64.lane_vibfly2 (fun c => 127 - c) (z := VG.Proof.MlKem.X86_64.zInv)
    (fun c hc' => ⟨by omega, congrArg zeta (by omega)⟩) hc hsi hS hT hw

/-! ## `vg_mlkem_ntt_avx2` -/

theorem nttY_correct (s : State) (hs : (VG.Proof.MlKem.X86_64.inPlaceK ntt).pre s) :
    ∃ t s', Exec isa nttAvx2 s t s' ∧ abiPreserved s s' ∧ (VG.Proof.MlKem.X86_64.inPlaceK ntt).post s s' := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwf : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hW : WP isa nttAvx2 s fun s' => ∃ s2,
      (PolyIs s2.mem (s.gpr .rdi) (ntt (polyAt s.mem (s.gpr .rdi))) ∧
        Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s2.mem) ∧ Frame [mxR (s.gpr .rsi)] s2.mem s'.mem ∧
      Keep [] s2 s' := by
    unfold nttAvx2
    refine withMxcsr_ok (by decide) [.rax, .rcx, .rdx, .r8, .r9] (by decide) rfl hw ?_ fun s1 k1 f1 => ?_
    · decide +kernel
    have hdi1 : s1.gpr .rdi = s.gpr .rdi := k1.gpr (by decide)
    have hsi1 : s1.gpr .rsi = s.gpr .rsi := k1.gpr (by decide)
    have hF1 : PolyIs s1.mem (s.gpr .rdi) (polyAt s.mem (s.gpr .rdi)) :=
      polyIs_frame f1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub _))
        ⟨hs.2.2.2.2.2, rfl⟩
    refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.ypro_ok zmTab zmTab_eq hdi1 hsi1 hF1 (by rw [k1.2.2]; exact hwf)
      (by rw [k1.2.2]; exact hw) hd) fun s2 ⟨hS, hT, hc, hf2, k2⟩ => ?_)
    have hsi2 : s2.gpr .rsi = s.gpr .rsi := by rw [k2.gpr (by decide), hsi1]
    have hw2 : pR (s.gpr .rsi) ∈ s2.wr := by rw [k2.2.2, k1.2.2]; exact hw
    refine LIY.seq hsi2 hw2 (VG.Proof.MlKem.X86_64.fwdLayY_ok 128 1 (by decide) (by decide)) ?_
      ⟨hS, hT, hc, Keep.refl _ _, Frame.refl _ _⟩
    refine fun _ hI => LIY.seq hsi2 hw2 (VG.Proof.MlKem.X86_64.fwdLayY_ok 64 2 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 (VG.Proof.MlKem.X86_64.fwdLayY_ok 32 4 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 (VG.Proof.MlKem.X86_64.fwdLayY_ok 16 8 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 VG.Proof.MlKem.X86_64.fwdLay8Y_ok ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 VG.Proof.MlKem.X86_64.fwdLay4Y_ok ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 VG.Proof.MlKem.X86_64.fwdLay2Y_ok ?_ hI
    intro s3 hI
    refine WP.mono (VG.Proof.MlKem.X86_64.yepi_ok hI.c hI.S (by rw [hI.keep.gpr (by decide), k2.gpr (by decide), hdi1])
      (by rw [hI.keep.gpr (by decide), hsi2]) (by rw [hI.keep.2.2, k2.2.2, k1.2.2]; exact hwf)
      (by rw [hI.keep.2.2]; exact hw2) hd) fun s4 ⟨hP, hf4⟩ => ⟨?_, ?_⟩
    · rw [ntt_eq_layers]
      simp only [nttLens, List.foldl_cons, List.foldl_nil]
      exact hP
    · refine (frame_fs f1 ?_).trans ((frame_fs hf2 ?_).trans ((frame_fs hI.frame ?_).trans (frame_fs hf4 ?_))) <;>
        intro r hr <;> simp only [List.mem_singleton] at hr <;> subst hr
      exacts [.inr (mx_sub _), .inr fun _ h => h, .inr (pR_sub_S _), .inl fun _ h => h]
  obtain ⟨t, s', he, ⟨s2, ⟨hP, hf⟩, hf', -⟩, hk⟩ :=
    WP.keep [.rax, .rcx, .rdx, .r8, .r9, .r11] hW (by decide +kernel)
  refine ⟨t, s', he, abiPreserved_of_ctl (by decide +kernel) he (gprPreserved_of hk (by decide)
    (hf.trans (hf'.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩))
    (by simpa using ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩)), ?_⟩
  · rw [List.mem_singleton.mp hr]; exact mx_sub _
  · exact polyIs_frame hf' (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub _)) hP

theorem nttY_ct : ConstantTime isa (VG.Proof.MlKem.X86_64.inPlaceK ntt).pre (VG.Proof.MlKem.X86_64.inPlaceK ntt).pub nttAvx2 :=
  VG.Taint.constantTime (A := VG.X86_64.taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2])
    (by taint_decide)

theorem nttY_verified : Verified X86_64.target nttAvx2 (Spec.MlKem.nttContract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlKem.X86_64.nttY_correct VG.Proof.MlKem.X86_64.nttY_ct (by
    mlkem_implies [Spec.MlKem.nttContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, VG.Proof.MlKem.X86_64.inPlaceK,
      X86_64.abi, X86_64.argRegs] [inPlaceSat] using VG.Proof.MlKem.X86_64.inPlaceSat)

/-! ## `vg_mlkem_inv_ntt_avx2` -/

theorem nttInvY_correct (s : State) (hs : (VG.Proof.MlKem.X86_64.inPlaceK nttInv).pre s) :
    ∃ t s', Exec isa nttInvAvx2 s t s' ∧ abiPreserved s s' ∧ (VG.Proof.MlKem.X86_64.inPlaceK nttInv).post s s' := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwf : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hW : WP isa nttInvAvx2 s fun s' => ∃ s2,
      (PolyIs s2.mem (s.gpr .rdi) (nttInv (polyAt s.mem (s.gpr .rdi))) ∧
        Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s2.mem) ∧ Frame [mxR (s.gpr .rsi)] s2.mem s'.mem ∧
      Keep [] s2 s' := by
    unfold nttInvAvx2
    refine withMxcsr_ok (by decide) [.rax, .rcx, .rdx, .r8, .r9] (by decide) rfl hw ?_ fun s1 k1 f1 => ?_
    · decide +kernel
    have hdi1 : s1.gpr .rdi = s.gpr .rdi := k1.gpr (by decide)
    have hsi1 : s1.gpr .rsi = s.gpr .rsi := k1.gpr (by decide)
    have hF1 : PolyIs s1.mem (s.gpr .rdi) (polyAt s.mem (s.gpr .rdi)) :=
      polyIs_frame f1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub _))
        ⟨hs.2.2.2.2.2, rfl⟩
    refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.ypro_ok zmTabInv VG.Proof.MlKem.X86_64.zmTabInv_eq hdi1 hsi1 hF1 (by rw [k1.2.2]; exact hwf)
      (by rw [k1.2.2]; exact hw) hd) fun s2 ⟨hS, hT, hc, hf2, k2⟩ => ?_)
    have hsi2 : s2.gpr .rsi = s.gpr .rsi := by rw [k2.gpr (by decide), hsi1]
    have hw2 : pR (s.gpr .rsi) ∈ s2.wr := by rw [k2.2.2, k1.2.2]; exact hw
    refine LIY.seq hsi2 hw2 VG.Proof.MlKem.X86_64.invLay2Y_ok ?_ ⟨hS, hT, hc, Keep.refl _ _, Frame.refl _ _⟩
    refine fun _ hI => LIY.seq hsi2 hw2 VG.Proof.MlKem.X86_64.invLay4Y_ok ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 VG.Proof.MlKem.X86_64.invLay8Y_ok ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 (VG.Proof.MlKem.X86_64.invLayY_ok 16 112 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 (VG.Proof.MlKem.X86_64.invLayY_ok 32 120 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 (VG.Proof.MlKem.X86_64.invLayY_ok 64 124 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 (VG.Proof.MlKem.X86_64.invLayY_ok 128 126 (by decide) (by decide)) ?_ hI
    refine fun _ hI => LIY.seq hsi2 hw2 (fun _ hc hsi hS _ hw => VG.Proof.MlKem.X86_64.yscale_ok hc hsi hS hw) ?_ hI
    intro s3 hI
    refine WP.mono (VG.Proof.MlKem.X86_64.yepi_ok hI.c hI.S (by rw [hI.keep.gpr (by decide), k2.gpr (by decide), hdi1])
      (by rw [hI.keep.gpr (by decide), hsi2]) (by rw [hI.keep.2.2, k2.2.2, k1.2.2]; exact hwf)
      (by rw [hI.keep.2.2]; exact hw2) hd) fun s4 ⟨hP, hf4⟩ => ⟨?_, ?_⟩
    · rw [nttInv_eq_layers]
      simp only [nttInvLens, List.foldl_cons, List.foldl_nil]
      exact hP
    · refine (frame_fs f1 ?_).trans ((frame_fs hf2 ?_).trans ((frame_fs hI.frame ?_).trans (frame_fs hf4 ?_))) <;>
        intro r hr <;> simp only [List.mem_singleton] at hr <;> subst hr
      exacts [.inr (mx_sub _), .inr fun _ h => h, .inr (pR_sub_S _), .inl fun _ h => h]
  obtain ⟨t, s', he, ⟨s2, ⟨hP, hf⟩, hf', -⟩, hk⟩ :=
    WP.keep [.rax, .rcx, .rdx, .r8, .r9, .r11] hW (by decide +kernel)
  refine ⟨t, s', he, abiPreserved_of_ctl (by decide +kernel) he (gprPreserved_of hk (by decide)
    (hf.trans (hf'.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩))
    (by simpa using ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩)), ?_⟩
  · rw [List.mem_singleton.mp hr]; exact mx_sub _
  · exact polyIs_frame hf' (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub _)) hP

theorem nttInvY_ct : ConstantTime isa (VG.Proof.MlKem.X86_64.inPlaceK nttInv).pre (VG.Proof.MlKem.X86_64.inPlaceK nttInv).pub nttInvAvx2 :=
  VG.Taint.constantTime (A := VG.X86_64.taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2])
    (by taint_decide)

theorem nttInvY_verified : Verified X86_64.target nttInvAvx2 (Spec.MlKem.nttInvContract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlKem.X86_64.nttInvY_correct VG.Proof.MlKem.X86_64.nttInvY_ct (by
    mlkem_implies [Spec.MlKem.nttInvContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, VG.Proof.MlKem.X86_64.inPlaceK,
      X86_64.abi, X86_64.argRegs] [inPlaceSat] using VG.Proof.MlKem.X86_64.inPlaceSat)

end VG.Proof.MlKem.X86_64

end
