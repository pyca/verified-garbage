module

public import VerifiedGarbage.Proof.MlDsa.Arith.Representation
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Backend
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.MlDsa.Sample.Rej4
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.AddSub
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mul
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Bits
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.MakeHint
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.NormLt
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.UseHint
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.M4Verified
public import VerifiedGarbage.Proof.MlKem.X86_64.ArithOk
public import VerifiedGarbage.Proof.Framework.X86_64.InstrBits
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Top
import VerifiedGarbage.Proof.MlKem.X86_64.S4Verified
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4CT
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mxcsr
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.DotCore
import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VMem
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.MlKem.X86_64.VLay
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.DotCore
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mul
meta import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VMem
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
meta import VerifiedGarbage.Proof.MlKem.X86_64.VLay
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.MontgomeryCore
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.MontgomeryCore
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Ntt
public import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Basic
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLanes
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttShort
public import VerifiedGarbage.Proof.MlKem.X86_64.S4CT
import VerifiedGarbage.Proof.MlKem.X86_64.FragCall
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttShortCT
import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Top
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttShort
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4CT
meta import VerifiedGarbage.Proof.MlDsa.Arith.Mem
meta import VerifiedGarbage.Proof.MlKem.X86_64.ArithOk
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragCall
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttShortCT
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! ### `MlDsa.X86_64.Sample.Rej4Scalar`, which only this module used -/

section

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly4`

The baseline implementation calls `vg_mldsa_rej_ntt_poly` on each seed,
between the prologue and the epilogue of the one for AVX2 (`Rej4Top.lean`):
after the call on seed `K`, polynomial `K` is the seed's `RejNTTPoly` if it
has 256 coefficients, and `r14` records whether the first `K + 1` do (`PC`),
as in `vg_mlkem_sample_ntt4` (`MlKem/X86_64/S4Scalar.lean`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Rej4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (rejNTT4)
open VG.Proof.MlKem.X86_64 (Keep sample4K relInv taintRel relStart Rel2 pR ret_disj24 stk_disj24'
  ce_bytesAt24 ce_gpr' WP.keep nosp_of)
open VG.Proof.MlKem.X86_64.S4 (R4 Pre aP at' sd scr aR scrR stkR sdR pre_of pub_scr pub_aP pub_B pub_sd pub_sp
  env_rbx pro_ok I0 sub_scr sub_poly seed_bytes cov scr6144_lt sx34 sx1024 sx6144 c_sub c_disj and14_ok epi_eq
  cRd cWr in_scr')
open VG.Proof.MlDsa.X86_64.Sample (rnK nil_regs)
open VG.Proof.MlDsa.Sample (rnFold toPoly)
open VG.Proof.MlDsa.Arith (polyIs_frame)
open VG.Spec.MlDsa (G)
open VG.Proof.MlDsa (PolyIs)

theorem rn_nosp : NoSp Impl.MlDsa.X86_64.Sample.rejNTTShort := nosp_of (by decide +kernel)

theorem rn_depth : Impl.MlDsa.X86_64.Sample.rejNTTShort.depth = 2 := by decide +kernel

/-- Before the call on seed `K`. -/
structure PC (σ : State) (K : Nat) (s : State) : Prop where
  env : EnvK σ s
  r14 : s.gpr .r14 = BitVec.ofNat 64 (okN σ K)
  polys : ∀ k < K, (Lt σ k 336).length = 256 → PolyIs s.mem (Proof.MlKem.poly4 (aP σ) k) (toPoly (Lt σ k 336))

section
variable {σ : State} (hp : Pre σ)
include hp

omit hp in
/-- `PC` after code that writes no memory and keeps its registers. -/
theorem PC.keep {K : Nat} {s s' : State} (h : PC σ K s) (hm : s'.mem = s.mem) {rs : List Reg}
    (hk : Keep rs s s') (hrs : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], r ∉ rs) : PC σ K s' :=
  ⟨h.env.keep hm hk fun r hr => hrs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h | h <;> simp [h]),
    by rw [hk.gpr (hrs .r14 (by simp)), h.r14], by rw [hm]; exact h.polys⟩

/-- `PC` after the call. -/
theorem PC.call {K : Nat} (hK : K < 4) {s s' : State} (h : PC σ K s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], s'.gpr r = s.gpr r)
    (hf : Frame (cWr σ K ++ [stkR σ]) s.mem s'.mem) : PC σ K s' := by
  refine ⟨⟨hrd.trans h.env.rd, hwr.trans h.env.wr, by rw [hg .rbx (by simp), h.env.rbx],
      by rw [hg .r12 (by simp), h.env.r12], by rw [hg .r13 (by simp), h.env.r13], by rw [hg .rsp (by simp), h.env.rsp],
      by rw [hg .r15 (by simp), h.env.r15], fun i hi => ?_, h.env.frame.trans (hf.sub (c_sub (σ := σ) hK))⟩,
    by rw [hg .r14 (by simp), h.r14], fun k hk e => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (c_disj hp hK (by simp only [oSave, oScalar]; omega_using [hi])) (by decide)]
    exact h.env.saved i hi
  · refine polyIs_frame hf (fun r hr => ?_) (h.polys k hk e)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · have hd := Offset.disjoint (aP σ) (d := 1024 * k) (n := 1024) (e := 1024 * K) (k := 1024) (by omega_using [hk]) (by omega_using [hK, hk])
        (by omega_using [hK])
      simpa [Proof.MlKem.poly4] using hd
    · exact (hp.a_scr.sub_left (sub_poly (by omega_using [hK, hk]))).sub_right (sub_scr (by simp only [oScalar]; omega_using []))
    · exact (hp.stk_a.sub_right (sub_poly (by omega_using [hK, hk]))).symm

/-- The arguments of the call on seed `K`. -/
structure ArgI (σ : State) (K : Nat) (s : State) : Prop where
  pinv : PC σ K s
  rdi : s.gpr .rdi = sd σ + BitVec.ofNat 64 (34 * K)
  rsi : s.gpr .rsi = Proof.MlKem.poly4 (aP σ) K
  rdx : s.gpr .rdx = at' σ oScalar

omit hp in
theorem argsK_ok {K : Nat} (hK : K < 4) {s : State} (h : PC σ K s) :
    WP isa (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * K))),
      .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rdx (.reg .rbx),
      .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))]) s (ArgI σ K) :=
  WP.mono (WP.keep [.rdi, .rsi, .rdx] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rdi = sd σ + BitVec.ofNat 64 (34 * K) ∧ s'.gpr .rsi = Proof.MlKem.poly4 (aP σ) K ∧ s'.gpr .rdx = at' σ oScalar)
    (by xrun [h.env.r12, h.env.r13, h.env.rbx, sx34 hK, sx1024 hK, sx6144]; exact ⟨rfl, rfl⟩) rfl)
    fun _ ⟨⟨hm₂, hdi, hsi, hdx⟩, k₂⟩ => ⟨h.keep hm₂ k₂ (by decide), hdi, hsi, hdx⟩

theorem argK_kS {K : Nat} (hK : K < 4) {s : State} (h : ArgI σ K s) :
    (below (s.gpr .rsp) 24).Disjoint ⟨sd σ + BitVec.ofNat 64 (34 * K), 34⟩ := by
  rw [h.pinv.env.rsp]; exact hp.stk_sd.sub_right (Offset.sub_base (sd σ) (d := 34 * K) (n := 34) (by omega_using [hK]))

theorem argK_pre {K : Nat} (hK : K < 4) {s : State} (h : ArgI σ K s) :
    rnK.pre (s.callEntry.withRegions (cRd σ K) (cWr σ K)) := by
  have hsp : s.gpr .rsp = σ.gpr .rsp := h.pinv.env.rsp
  have kS := argK_kS hp hK h
  have kA : (below (s.gpr .rsp) 24).Disjoint (pR (Proof.MlKem.poly4 (aP σ) K)) := by
    rw [hsp]; exact hp.stk_a.sub_right (sub_poly (σ := σ) hK)
  have kZ : (below (s.gpr .rsp) 24).Disjoint ⟨at' σ oScalar, 2048⟩ := by
    rw [hsp]; exact hp.stk_scr.sub_right (sub_scr (σ := σ) (a := oScalar) (n := 2048) (by simp only [oScalar]; omega_using []))
  simp only [rnK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce_gpr' s (by decide : Reg.rdi ≠ .rsp), ce_gpr' s (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, h.rdx]
  exact ⟨trivial, trivial,
    (hp.sd_a.sub_left (Offset.sub_base _ (by omega_using [hK]))).sub_right (sub_poly hK),
    (hp.sd_scr.sub_left (Offset.sub_base _ (by omega_using [hK]))).sub_right (sub_scr (by simp only [oScalar]; omega_using [])),
    (hp.a_scr.sub_left (sub_poly hK)).sub_right (sub_scr (by simp only [oScalar]; omega_using [])),
    ret_disj24 s kS, ret_disj24 s kA, ret_disj24 s kZ, stk_disj24' s kS, stk_disj24' s kA, stk_disj24' s kZ,
    scr6144_lt hp⟩

/-- After the call on seed `K`. -/
structure CallI (σ : State) (K : Nat) (s : State) : Prop where
  pinv : PC σ K s
  rax : (s.gpr .rax).setWidth 32 = if (Lt σ K 336).length = 256 then 1 else 0
  poly : (Lt σ K 336).length = 256 → PolyIs s.mem (Proof.MlKem.poly4 (aP σ) K) (toPoly (Lt σ K 336))

theorem callK_ok {K : Nat} (hK : K < 4) {s : State} (h : ArgI σ K s) :
    WP isa (.call "vg_mldsa_rej_ntt_poly" Impl.MlDsa.X86_64.Sample.rejNTTShort) s (CallI σ K) := by
  have hcv := cov hp h.pinv.env hK
  refine WP.call VG.Proof.MlDsa.X86_64.Sample.RejNttShort.correct rn_nosp (by rw [rn_depth]; decide) (argK_pre hp hK h) hcv.1 hcv.2
    fun s₃ hrd hwr hcs hf _ ⟨s₃', hm₃, hg₃, hpost⟩ => ?_
  rw [rn_depth, h.pinv.env.rsp] at hf
  have h₃ : PC σ K s₃ := h.pinv.call hp hK hrd hwr (fun r hr => hcs r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hf
  simp only [rnK, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s (by decide : Reg.rsi ≠ .rsp), h.rdi, h.rsi, hm₃, ce_bytesAt24 s (n := 34) (by decide) (argK_kS hp hK h),
    seed_bytes hp hK h.pinv.env.frame] at hpost
  rw [hg₃ .rax (by decide)] at hpost
  simp only [← Lt_336] at hpost
  exact ⟨h₃, hpost.1, hpost.2⟩

omit hp in
theorem okN_succ' (K : Nat) : BitVec.setWidth 64 ((BitVec.ofNat 64 (okN σ K)).setWidth 32 &&&
    (if (Lt σ K 336).length = 256 then 1 else 0)) = BitVec.ofNat 64 (okN σ (K + 1)) := by
  simp only [okN, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
  by_cases e : (Lt σ K 336).length = 256
  · rw [ite_eq_left e, show ((Lt σ K 336).length == 256) = true by simpa using e]
    cases (List.range K).all fun k => (Lt σ k 336).length == 256 <;> rfl
  · rw [ite_eq_right e, show ((Lt σ K 336).length == 256) = false by simpa using e]
    cases (List.range K).all fun k => (Lt σ k 336).length == 256 <;> rfl

omit hp in
theorem andK_ok {K : Nat} {s : State} (h : CallI σ K s) :
    WP isa (.block [.alu32 .and .r14 (.reg .rax)]) s (PC σ (K + 1)) := by
  refine WP.mono (and14_ok s) fun s₄ ⟨⟨h14, hm₄⟩, k₄⟩ => ?_
  refine ⟨h.pinv.env.keep hm₄ k₄ (by decide), by rw [h14, h.pinv.r14, h.rax, okN_succ'], fun k hk e => ?_⟩
  rw [hm₄]
  by_cases ek : k = K
  · subst ek; exact h.poly e
  · exact h.pinv.polys k (by omega_using [hk, ek]) e

theorem callK_ok' {K : Nat} (hK : K < 4) {s : State} (h : PC σ K s) : WP isa (Impl.MlDsa.X86_64.Sample.Rej4.callK K) s (PC σ (K + 1)) :=
  WP.seq (WP.mono (argsK_ok hK h) fun _ h₂ => WP.seq (WP.mono (callK_ok hp hK h₂) fun _ h₃ => andK_ok h₃))

/-- The return value, and the callee-saved registers restored. -/
theorem endS_ok {s : State} (h : PC σ 4 s) :
    WP isa (.block epi) s fun s' => r4K.post σ s' ∧ gprPreserved σ s' := by
  have hin : ∀ i < 5, InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oSave + 8 * i)) 8 := fun i hi =>
    in_scr' hp h.env.rd h.env.wr (by simp only [oSave]; omega_using [hi])
  rw [epi_eq]
  refine WP.mono (WP.keep [.rax, .r14, .r13, .r12, .rbp, .rbx] (Q := fun s' => s'.mem = s.mem ∧
      (s'.gpr .rax).setWidth 32 = (s.gpr .r14).setWidth 32 ∧
      s'.gpr .r14 = s.mem.readW (at' σ (oSave + 8 * 4)) 64 ∧ s'.gpr .r13 = s.mem.readW (at' σ (oSave + 8 * 3)) 64 ∧
      s'.gpr .r12 = s.mem.readW (at' σ (oSave + 8 * 2)) 64 ∧ s'.gpr .rbp = s.mem.readW (at' σ (oSave + 8 * 1)) 64 ∧
      s'.gpr .rbx = s.mem.readW (at' σ (oSave + 8 * 0)) 64)
    (by
      have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
      have h3 := hin 3 (by decide); have h4 := hin 4 (by decide)
      simp only [oSave, Nat.reduceMul, Nat.reduceAdd] at h0 h1 h2 h3 h4
      xrun [h0, h1, h2, h3, h4, h.env.rbx]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (by decide)) fun s' ⟨⟨hm, hax, h14, h13, h12, hbp, hbx⟩, k⟩ => ?_
  refine ⟨⟨?_, fun k hk e => ?_⟩, fun r hr => ?_, ?_⟩
  · rw [hax, h.r14, okN]
    simp only [Lt_336]
    split <;> rfl
  · rw [hm, ← Lt_336]
    rw [← Lt_336] at e
    exact h.polys k hk e
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

theorem scalar_body_ok {s : State} (h : I0 σ s) :
    WP isa (.seq (Impl.MlDsa.X86_64.Sample.Rej4.callK 0) (.seq (Impl.MlDsa.X86_64.Sample.Rej4.callK 1)
      (.seq (Impl.MlDsa.X86_64.Sample.Rej4.callK 2) (.seq (Impl.MlDsa.X86_64.Sample.Rej4.callK 3) (.block epi)))))
      s fun s' =>
      r4K.post σ s' ∧ gprPreserved σ s' := by
  have p₀ : PC σ 0 s := ⟨h.env, by rw [h.r14]; rfl, fun _ h _ => absurd h (by omega_using [])⟩
  exact WP.seq (WP.mono (callK_ok' hp (by decide) p₀) fun _ p₁ => WP.seq (WP.mono (callK_ok' hp (by decide) p₁)
    fun _ p₂ => WP.seq (WP.mono (callK_ok' hp (by decide) p₂) fun _ p₃ =>
      WP.seq (WP.mono (callK_ok' hp (by decide) p₃) fun _ p₄ => endS_ok hp p₄))))

end

theorem correct_scalar (σ : State) (hs : r4K.pre σ) :
    ∃ t s', Exec isa rejNTT4 σ t s' ∧ abiPreserved σ s' ∧ r4K.post σ s' := by
  have hp := pre_of (by dsimp only [r4K] at hs; exact hs)
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok hp) fun _ h => scalar_body_ok hp h)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

/-! ## Constant time -/

/-- The call on seed `K`. -/
theorem call_ct {K : Nat} (hK : K < 4) :
    RelCT isa (R4 fun σ s => ArgI σ K s) (.call "vg_mldsa_rej_ntt_poly" Impl.MlDsa.X86_64.Sample.rejNTTShort)
      (R4 fun σ s => CallI σ K s) :=
  relInv (fun σ s hp h => callK_ok (pre_of hp) hK h) (RelCT.callEx VG.Proof.MlDsa.X86_64.Sample.RejNttShort.correct VG.Proof.MlDsa.X86_64.Sample.RejNttShort.ct
    fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => by
      have hsp : s₁.gpr .rsp = s₂.gpr .rsp := by rw [h₁.pinv.env.rsp, h₂.pinv.env.rsp, pub_sp hq]
      refine ⟨_, _, _, _, argK_pre (pre_of p₁) hK h₁, argK_pre (pre_of p₂) hK h₂, ?_,
        (cov (pre_of p₁) h₁.pinv.env hK).1, (cov (pre_of p₁) h₁.pinv.env hK).2,
        (cov (pre_of p₂) h₂.pinv.env hK).1, (cov (pre_of p₂) h₂.pinv.env hK).2, hsp⟩
      simp only [rnK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_rsp,
        ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), h₁.rdi, h₂.rdi, h₁.rsi, h₂.rsi, h₁.rdx, h₂.rdx]
      rw [ce_bytesAt24 s₁ (n := 34) (by decide) (argK_kS (pre_of p₁) hK h₁),
        ce_bytesAt24 s₂ (n := 34) (by decide) (argK_kS (pre_of p₂) hK h₂),
        seed_bytes (pre_of p₁) hK h₁.pinv.env.frame, seed_bytes (pre_of p₂) hK h₂.pinv.env.frame, pub_B hq hK]
      simp only [pub_sd hq, pub_aP hq, at', pub_scr hq, hsp, and_self])

/-- The call on seed `K`, given the taint analysis of its arguments. -/
theorem callK_ct {K : Nat} (hK : K < 4) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.r12, .r13, .rbx])
      (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * K))),
        .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rdx (.reg .rbx),
        .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))]) hc).isSome = true) :
    RelCT isa (R4 fun σ s => PC σ K s) (Impl.MlDsa.X86_64.Sample.Rej4.callK K) (R4 fun σ s => PC σ (K + 1) s) :=
  RelCT.seq (relInv (fun σ s _ h => argsK_ok hK h) (taintRel [.r12, .r13, .rbx]
      (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.env.r12, h₂.env.r12, pub_sd hq]
        · rw [h₁.env.r13, h₂.env.r13, pub_aP hq]
        · exact env_rbx hq h₁.env h₂.env) c))
    (RelCT.seq (call_ct hK) (relInv (fun σ s _ h => andK_ok h) (taintRel [] nil_regs (by taint_decide))))

theorem ct_scalar : ConstantTime isa r4K.pre r4K.pub rejNTT4 := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq (RelCT.mono (relInv (I' := fun σ s => PC σ 0 s)
    (fun σ s hp h => by
      subst h
      exact WP.mono (pro_ok (pre_of hp)) fun _ h => ⟨h.env, by rw [h.r14]; rfl, fun _ h _ => absurd h (by omega_using [])⟩)
    (taintRel [.rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hq.1, hq.2.1, hq.2.2.1]) (by taint_decide))) (fun _ _ h => h) fun _ _ h => h) ?_)
  refine RelCT.seq (callK_ct (K := 0) (by decide) (by taint_decide)) (RelCT.seq (callK_ct (K := 1) (by decide)
    (by taint_decide)) (RelCT.seq (callK_ct (K := 2) (by decide) (by taint_decide))
      (RelCT.seq (callK_ct (K := 3) (by decide) (by taint_decide)) ?_)))
  exact taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide)

end VG.Proof.MlDsa.X86_64.Rej4

end

end

/-! ### `MlDsa.X86_64.Arith.Dot`, which only this module used -/

section

/-!
# ML-DSA on x86-64: `vg_mldsa_dot_inverse{c}`

As `vg_mldsa_dot_inverse{c}_avx2` (`YDot.lean`) on four coefficients at a
time in SSE2 registers: each of the 64 iterations sums the `c` products in
quadwords (`macs_ok`) and reduces them (`dot_lane`) to the sum times `2⁻³²`,
which `dotPlain` multiplies by `2³²` (`plain_dw`), storing the sums modulo `q`
(`step`); then the inverse NTT (`invBody_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Arith.DotS

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.X86_64.Arith
open VG.Proof.MlKem.X86_64 (writesIn writesOnly_of Keep XOnly WP.keep writesOnly gprPreserved_of ifp ifn GOnly
  wp_rcxLoop add_ofNat_zero mxR xmm_setXmm)
open VG.Impl.MlKem.X86_64 (xb xmov rcxLoop)
open VG.Spec.MlDsa (q n Poly Zq)
open VG.Proof.MlDsa (coeffAt polyAt Reduced PolyIs montgomeryRInv)

/-- A 128-bit load. -/
theorem xld_ok {s : State} {p : Reg} {off : Nat} {d : XReg}
    (h : InRegions (s.rd ++ s.wr) (s.gpr p + BitVec.ofNat 64 off) 16) :
    WP isa (.block [.movdquLoad d (at_ p off)]) s fun s' =>
      s'.xmm d = s.mem.readW (s.gpr p + BitVec.ofNat 64 off) 128 ∧ XOnly [d] s s' := by
  vrund [h]
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun r hr => ?_⟩
  rw [xmm_setXmm, ifn (by simpa using hr)]

/-- The sums of the first `n` products of the four coefficients `Av j t`,
`Bv j t` (`t < 4`) in the quadwords of `xmm5` (even `t`) and `xmm6` (odd). -/
def AccS (s : State) (Av Bv : Nat → Nat → Nat) (n : Nat) : Prop :=
  ∀ k < 2,
    (qword (s.xmm .xmm5) k).toNat = dsum (fun j => Av j (2 * k)) (fun j => Bv j (2 * k)) n ∧
    (qword (s.xmm .xmm6) k).toNat = dsum (fun j => Av j (2 * k + 1)) (fun j => Bv j (2 * k + 1)) n

/-- The first `n` products. -/
theorem macs_ok {c : Nat} (hc : c ≤ 7) {Av Bv : Nat → Nat → Nat} (hA : ∀ j < c, ∀ t < 4, Av j t < 3 * q)
    (hB : ∀ j < c, ∀ t < 4, Bv j t < 3 * q) {s : State}
    (hr : ∀ j < c, InRegions (s.rd ++ s.wr) (s.gpr .r10 + BitVec.ofNat 64 (1024 * j)) 16)
    (hr' : ∀ j < c, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (1024 * j)) 16)
    (ha : ∀ j < c, ∀ e < 4,
      (dword (s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (1024 * j)) 128) e).toNat = Av j e)
    (hb : ∀ j < c, ∀ e < 4,
      (dword (s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 (1024 * j)) 128) e).toNat = Bv j e)
    (h0 : AccS s Av Bv 0) :
    ∀ n ≤ c, WP isa (.block ((List.range n).flatMap fun j => dotLoadsS j ++ dotMac)) s fun s' =>
      AccS s' Av Bv n ∧ XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm5, .xmm6] s s'
  | 0, _ => by
    simp only [List.range_zero, List.flatMap_nil]
    vrund
    exact ⟨h0, XOnly.refl _ s⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (macs_ok hc hA hB hr hr' ha hb h0 n (by omega_using [hn])) fun s1 ⟨A1, o1⟩ => ?_
    rw [dotLoadsS, show ∀ (x y : Instr) (l : List Instr), [x, y] ++ l = [x] ++ ([y] ++ l) from fun _ _ _ => rfl,
      WP.block_append_iff]
    refine WP.mono (xld_ok (by rw [o1.rd, o1.wr, o1.gpr]; exact hr n (by omega_using [hn]))) fun s2 ⟨L2, o2⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (xld_ok (by rw [o2.rd, o2.wr, o2.gpr, o1.rd, o1.wr, o1.gpr]; exact hr' n (by omega_using [hn])))
      fun s3 ⟨L3, o3⟩ => ?_
    refine WP.mono (dotMac_ok s3) fun s4 ⟨M5, M6, o4⟩ => ⟨fun k hk => ?_, (((o1.trans o2).trans o3).trans o4).mono (by simp)⟩
    have x0 : s3.xmm .xmm0 = s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (1024 * n)) 128 := by
      rw [o3.xmm _ (by decide), L2, o1.mem, o1.gpr]
    have x1 : s3.xmm .xmm1 = s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 (1024 * n)) 128 := by
      rw [L3, o2.mem, o2.gpr, o1.mem, o1.gpr]
    have x5 : s3.xmm .xmm5 = s1.xmm .xmm5 := by rw [o3.xmm _ (by decide), o2.xmm _ (by decide)]
    have x6 : s3.xmm .xmm6 = s1.xmm .xmm6 := by rw [o3.xmm _ (by decide), o2.xmm _ (by decide)]
    have a0 := ha n (by omega_using [hn]) (2 * k) (by omega_using [hk])
    have a1 := ha n (by omega_using [hn]) (2 * k + 1) (by omega_using [hk])
    have b0 := hb n (by omega_using [hn]) (2 * k) (by omega_using [hk])
    have b1 := hb n (by omega_using [hn]) (2 * k + 1) (by omega_using [hk])
    rw [← x0] at a0 a1
    rw [← x1] at b0 b1
    refine ⟨?_, ?_⟩
    · rw [M5, qword_macE hk (by rw [x5, (A1 k hk).1, a0, b0]; exact prod_bound hc hA hB (by omega_using [hn]) (by omega_using [hk])), x5,
        (A1 k hk).1, a0, b0]
      rfl
    · rw [M6, qword_macO hk (by rw [x6, (A1 k hk).2, a1, b1]; exact prod_bound hc hA hB (by omega_using [hn]) (by omega_using [hk])), x6,
        (A1 k hk).2, a1, b1]
      rfl

theorem dotPlain_ok {s : State} (hc : VConsts s) :
    WP isa (.block dotPlain) s fun s' => s'.xmm .xmm5 = csubV (montV (s.xmm .xmm5) (s.xmm .xmm11) (s.xmm .xmm11)) ∧
      XOnly [.xmm2, .xmm4, .xmm5] s s' := by
  simp only [dotPlain, vmont, vredc, vcsub, vcadd, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  rw [hc.q, hc.qinv]
  exact ⟨rfl, by xonly⟩

/-- The sum times `2⁻³²`, times `2⁶⁴` times `2⁻³²`: the sum modulo `q`. -/
theorem plain_dw {x : BitVec 128} {P : Nat} {e : Nat} (he : e < 4)
    (hx : (dword x e).toNat = (Fin.ofNat q P * montgomeryRInv).val) :
    (dword (csubV (montV x r2V r2V)) e).toNat = (Fin.ofNat q P : Zq).val := by
  have hzo : ∀ j < 2, dword r2V (2 * j) = dword r2V (2 * j + 1) := fun j hj => by
    rw [dword_r2V (by omega_using [hj]), dword_r2V (by omega_using [hj])]
  have hb : ∀ i < 4, (dword x i).toNat * (dword r2V i).toNat < q * 2 ^ 32 := fun i hi => by
    rw [dword_r2V hi]
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (dword x i).isLt (Nat.le_refl _) (by decide)) (by decide)
  have hm := dword_montV hzo hb he
  rw [dword_csubV _ he, csubL_toNat (by rw [hm]; exact mont_lt (hb e he)), hm, condSub_mont (hb e he), mont_inverse,
    dword_r2V he, hx]
  have h3 : ∀ (z : Zq) (a b : Nat), a < q → b < q → (z.val * a * b) % q = (z * Fin.ofNat q a * Fin.ofNat q b).val :=
    fun z a b ha hb => by
      rw [Fin.val_mul, Fin.val_mul, Fin.val_ofNat, Fin.val_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
        Nat.mod_mul_mod]
  rw [show (2365951#32).toNat = 2365951 from rfl, h3 _ _ _ (by decide) (by decide), Fin.mul_assoc, Fin.mul_assoc,
    show montgomeryRInv * (Fin.ofNat q 2365951 * Fin.ofNat q 8265825) = 1 by decide, Fin.mul_one]

/-- Coefficient `k` of the sum of the products. -/
def dotP (m : VG.Mem) (a b : Addr) (c k : Nat) : Zq :=
  Fin.ofNat q (dsum (fun j => famV m a j k) (fun j => famV m b j k) c)

/-- After `i` iterations of the loop, from `s₀`. -/
structure DI (o a b : Addr) (c : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  r8 : s.gpr .r8 = coeffAddr o (4 * i)
  r10 : s.gpr .r10 = coeffAddr a (4 * i)
  rdx : s.gpr .rdx = coeffAddr b (4 * i)
  keep : Keep [.r8, .r10, .rdx, .rcx, .rax] s₀ s
  vc : VConsts s
  x11 : s.xmm .xmm11 = r2V
  frame : Frame [pR o] s₀.mem s.mem
  done : ∀ k < 4 * i, (coeffAt s.mem o k).toNat = (dotP s₀.mem a b c k).val

section
variable {o a b : Addr} {c : Nat} {s₀ : State} (hc7 : c ≤ 7) (hwo : pR o ∈ s₀.wr)
  (hra : ∀ j < c, ∀ k, k + 4 ≤ 256 → InRegions (s₀.rd ++ s₀.wr) (coeffAddr (a + BitVec.ofNat 64 (1024 * j)) k) 16)
  (hrb : ∀ j < c, ∀ k, k + 4 ≤ 256 → InRegions (s₀.rd ++ s₀.wr) (coeffAddr (b + BitVec.ofNat 64 (1024 * j)) k) 16)
  (hda : ∀ j < c, (pR (a + BitVec.ofNat 64 (1024 * j))).Disjoint (pR o))
  (hdb : ∀ j < c, (pR (b + BitVec.ofNat 64 (1024 * j))).Disjoint (pR o))
  (hA : ∀ j < c, ∀ k < 256, famV s₀.mem a j k < 3 * q) (hB : ∀ j < c, ∀ k < 256, famV s₀.mem b j k < 3 * q)
include hc7 hwo hra hrb hda hdb hA hB

theorem step {i : Nat} (hi : i < 64) {s : State} (hI : DI o a b c s₀ i s) :
    WP isa (.block (dotBodyS c ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      DI o a b c s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have j0 : 4 * i + 4 ≤ 256 := by omega_using [hi]
  have hv : ∀ (p : Addr), (∀ j < c, (pR (p + BitVec.ofNat 64 (1024 * j))).Disjoint (pR o)) → ∀ j < c,
      ∀ e < 4, (dword (s.mem.readW (coeffAddr p (4 * i) + BitVec.ofNat 64 (1024 * j)) 128) e).toNat =
        famV s₀.mem p j (4 * i + e) := fun p hd j hj e he => by
    rw [addr_fam, dword_readW _ _ he, coeffAddr_add, ← coeffAt_eq, famV,
      coeffAt_frame hI.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd j hj) (by rw [n_eq]; omega_using [hi, he])]
  simp only [dotBodyS, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (dotZero_ok s) fun s1 ⟨z5, z6, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (macs_ok hc7 (Av := fun j t => famV s₀.mem a j (4 * i + t)) (Bv := fun j t => famV s₀.mem b j (4 * i + t))
    (fun j hj t ht => hA j hj _ (by omega_using [hi, ht])) (fun j hj t ht => hB j hj _ (by omega_using [hi, ht]))
    (fun j hj => by
      rw [o1.rd, o1.wr, o1.gpr, hI.r10, hI.keep.2.1, hI.keep.2.2, addr_fam]; exact hra j hj _ j0)
    (fun j hj => by
      rw [o1.rd, o1.wr, o1.gpr, hI.rdx, hI.keep.2.1, hI.keep.2.2, addr_fam]; exact hrb j hj _ j0)
    (fun j hj e he => by rw [o1.mem, o1.gpr, hI.r10]; exact hv a hda j hj e he)
    (fun j hj e he => by rw [o1.mem, o1.gpr, hI.rdx]; exact hv b hdb j hj e he)
    (fun k hk => by rw [z5, z6]; exact ⟨by simp [qword, dsum], by simp [qword, dsum]⟩) c (Nat.le_refl _))
    fun s2 ⟨A2, o2⟩ => ?_
  have o12 := o1.trans o2
  rw [WP.block_append_iff]
  refine WP.mono (dotRed_ok (xonly_vconsts o12 hI.vc (by decide) (by decide))) fun s3 ⟨R3, o3⟩ => ?_
  have o13 := o12.trans o3
  rw [WP.block_append_iff]
  refine WP.mono (dotPlain_ok (xonly_vconsts o13 hI.vc (by decide) (by decide))) fun s4 ⟨P4, o4⟩ => ?_
  have o14 := o13.trans o4
  have x11 : s3.xmm .xmm11 = r2V := by rw [o13.xmm _ (by decide), hI.x11]
  have hres : ∀ e < 4, (dword (s4.xmm .xmm5) e).toNat = (dotP s₀.mem a b c (4 * i + e)).val := by
    intro e he
    rw [P4, x11]
    refine plain_dw he ?_
    rw [R3, dot_lane (A := fun j t => famV s₀.mem a j (4 * i + t)) (B := fun j t => famV s₀.mem b j (4 * i + t)) hc7
      (fun j hj t ht => hA j hj _ (by omega_using [hi, ht])) (fun j hj t ht => hB j hj _ (by omega_using [hi, ht]))
      (fun k hk => (A2 k hk).1) (fun k hk => (A2 k hk).2) he]
  have g4 : s4.gpr .r8 = coeffAddr o (4 * i) := by rw [o14.gpr, hI.r8]
  have w0 : InRegions s4.wr (coeffAddr o (4 * i)) 16 := by rw [o14.wr, hI.keep.2.2]; exact f_in hwo j0
  vrund [g4, w0]
  rw [o14.mem]
  have p16 : ∀ p : Addr, coeffAddr p (4 * i) + 16 = coeffAddr p (4 * (i + 1)) := fun p => by
    rw [show (16 : BitVec 64) = BitVec.ofNat 64 (4 * 4) from rfl, coeffAddr_add, show 4 * i + 4 = 4 * (i + 1) by omega_using []]
  refine ⟨⟨?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_, fun k hk => ?_⟩, by rw [o14.gpr], by rw [o14.gpr]⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    exact p16 o
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [o14.gpr, hI.r10]; exact p16 a
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [o14.gpr, hI.rdx]; exact p16 b
  · have hr0 := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, ite_false]
    rw [o14.gpr, hI.keep.1 r hr0]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; rw [o14.rd, hI.keep.2.1]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; rw [o14.wr, hI.keep.2.2]
  · exact ⟨by simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags]; rw [o14.xmm _ (by decide)]; exact hI.vc.q,
      by simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags]; rw [o14.xmm _ (by decide)]; exact hI.vc.qinv⟩
  · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags]; rw [o14.xmm _ (by decide), hI.x11]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    exact hI.frame.writeW (List.mem_singleton_self _) _ (pR_contains o j0)
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    rw [coeffAt_write128 _ _ j0 _ (by omega_using [hi, hk])]
    split
    · rw [hres _ (by omega_using [hk]), show 4 * i + (k - 4 * i) = k by omega_arith]
    · exact hI.done k (by omega_arith)


/-- The loop, from the constants and the pointers, in `s₀`. -/
theorem pass_ok (h8 : s₀.gpr .r8 = o) (h10 : s₀.gpr .r10 = a) (hdx : s₀.gpr .rdx = b) (hc : VConsts s₀)
    (h11 : s₀.xmm .xmm11 = r2V) :
    WP isa (rcxLoop 64 (dotBodyS c)) s₀ fun s' => PolyIs s'.mem o (Vector.ofFn fun k => dotP s₀.mem a b c k.val) ∧
      Keep [.r8, .r10, .rdx, .rcx, .rax] s₀ s' ∧ Frame [pR o] s₀.mem s'.mem := by
  refine WP.mono (wp_rcxLoop (N := 64) (by decide) (by decide) (DI o a b c s₀)
    (fun u og _ => ⟨by rw [og.keep.gpr (by decide), h8, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [og.keep.gpr (by decide), h10, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [og.keep.gpr (by decide), hdx, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      og.keep.mono (by simp), ⟨by rw [og.xmm]; exact hc.q, by rw [og.xmm]; exact hc.qinv⟩,
      by rw [og.xmm]; exact h11, by rw [og.mem]; exact Frame.refl _ _, fun k hk => absurd hk (by omega_using [])⟩)
    (fun i hi u hI => step hc7 hwo hra hrb hda hdb hA hB hi hI)) fun u hI => ⟨⟨fun k hk => ?_, ?_⟩, hI.keep, hI.frame⟩
  · rw [n_eq] at hk
    rw [hI.done k (by omega_using [hk])]; exact (dotP s₀.mem a b c k).isLt
  · apply Vector.ext; intro k hk
    rw [polyAt, Vector.getElem_ofFn, Vector.getElem_ofFn]
    apply Fin.ext
    rw [Fin.val_ofNat, hI.done k (by rw [n_eq] at hk; omega_using [hk]), Nat.mod_eq_of_lt (dotP s₀.mem a b c k).isLt]

end

/-! ## The function -/

/-- The result: the sums. -/
theorem dotP_eq {m m' : VG.Mem} {a b : Addr} {c : Nat}
    (ha : ∀ j < c, ∀ k < 256, coeffAt m' (a + BitVec.ofNat 64 (1024 * j)) k = coeffAt m (a + BitVec.ofNat 64 (1024 * j)) k)
    (hb : ∀ j < c, ∀ k < 256, coeffAt m' (b + BitVec.ofNat 64 (1024 * j)) k = coeffAt m (b + BitVec.ofNat 64 (1024 * j)) k) :
    (Vector.ofFn fun k => dotP m' a b c k.val) = Proof.MlDsa.dotNTT
      (fun j => polyAt m (a + BitVec.ofNat 64 (1024 * j))) (fun j => polyAt m (b + BitVec.ofNat 64 (1024 * j))) c := by
  apply Vector.ext; intro k hk
  rw [Vector.getElem_ofFn, ← getElem!_pos (Proof.MlDsa.dotNTT _ _ c) k hk,
    dotNTT_get (A := fun j => famV m' a j k) (B := fun j => famV m' b j k) hk
    (fun j hj => by rw [polyAt_get _ _ hk, famV, ha j hj k hk]) (fun j hj => by rw [polyAt_get _ _ hk, famV, hb j hj k hk])]
  rfl

theorem correct {c : Nat} (hc7 : c ≤ 7)
    (hk : Code.allInstrs (writesIn [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11, .rsi]) (dotInvSse2 c) = true)
    (hctl : ctlOk (dotInvSse2 c) = true) (s : State) (hs : (dotK c).pre s) :
    ∃ t s', Exec isa (dotInvSse2 c) s t s' ∧ abiPreserved s s' ∧ (dotK c).post s s' := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, r1, r2, pa, pb⟩ := hs
  have hwo : pR (s.gpr .rdi) ∈ s.wr := by rw [hwr]; simp
  have hws : pR (s.gpr .rcx) ∈ s.wr := by rw [hwr]; simp
  have hW : WP isa (dotInvSse2 c) s fun s' => PolyIs s'.mem (s.gpr .rdi) (Spec.MlDsa.nttInv (Proof.MlDsa.dotNTT
      (fun j => polyAt s.mem (s.gpr .rsi + BitVec.ofNat 64 (1024 * j)))
      (fun j => polyAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (1024 * j))) c)) ∧
      Frame [pR (s.gpr .rdi), pR (s.gpr .rcx)] s.mem s'.mem := by
    refine WP.seq (WP.mono (Q := fun (w : State) => w.gpr .r10 = s.gpr .rsi ∧ w.gpr .rsi = s.gpr .rcx ∧
        GOnly [.r10, .rsi] s w)
      (by vrund; gonlyd) fun w ⟨h10, hsi, og⟩ => ?_)
    refine WP.mono (noMx_ok (sP := s.gpr .rcx) (Q := fun u => PolyIs u.mem (s.gpr .rdi) (Spec.MlDsa.nttInv
        (Proof.MlDsa.dotNTT (fun j => polyAt s.mem (s.gpr .rsi + BitVec.ofNat 64 (1024 * j)))
          (fun j => polyAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (1024 * j))) c)) ∧
        Frame [pR (s.gpr .rdi), pR (s.gpr .rcx)] s.mem u.mem) (fun s1 k1 f1 => ?_))
      fun s' ⟨s2, ⟨hP, hf⟩, hf', _⟩ => ⟨?_, ?_⟩
    rotate_left
    · exact polyIs_frame hf' (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact d3.sub_right (mx_sub' _)) hP
    · exact hf.trans (frame_fs hf' fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inr (mx_sub' _))
    have hdi1 : s1.gpr .rdi = s.gpr .rdi := by rw [k1.gpr (by decide), og.keep.gpr (by decide)]
    have hsi1 : s1.gpr .rsi = s.gpr .rcx := by rw [k1.gpr (by decide), hsi]
    have h101 : s1.gpr .r10 = s.gpr .rsi := by rw [k1.gpr (by decide), h10]
    have hdx1 : s1.gpr .rdx = s.gpr .rdx := by rw [k1.gpr (by decide), og.keep.gpr (by decide)]
    have wr1 : s1.wr = s.wr := by rw [k1.2.2, og.keep.2.2]
    have rd1 : s1.rd = s.rd := by rw [k1.2.1, og.keep.2.1]
    have hm : ∀ p : Addr, (pR (s.gpr .rcx)).Disjoint (famR p c) → ∀ j < c, ∀ k < 256,
        coeffAt s1.mem (p + BitVec.ofNat 64 (1024 * j)) k = coeffAt s.mem (p + BitVec.ofNat 64 (1024 * j)) k :=
      fun p hd j hj k hk => by
        rw [coeffAt_frame f1 (fun r hr => by
          rw [List.mem_singleton.mp hr]; exact (hd.sub_right (fam_sub p hj)).symm.sub_right (mx_sub' _))
          (by rw [n_eq]; exact hk), og.mem]
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (mulPro_ok s1) fun s2 ⟨c2, x2, _, k2, m2⟩ => ?_
    have hdi2 : s2.gpr .rdi = s.gpr .rdi := by rw [k2.gpr (by decide), hdi1]
    refine WP.mono (Q := fun (s3 : State) => s3.gpr .r8 = s.gpr .rdi ∧ GOnly [.r8] s2 s3)
      (by vrund [hdi2]; gonlyd) fun s3 ⟨h8, og3⟩ => ?_
    have c3 : VConsts s3 := ⟨by rw [og3.xmm]; exact c2.q, by rw [og3.xmm]; exact c2.qinv⟩
    have x3 : s3.xmm .xmm11 = r2V := by rw [og3.xmm]; exact x2
    have k13 : Keep [.rax, .r8] s1 s3 := (k2.trans og3.keep).mono (by simp)
    have m3 : s3.mem = s1.mem := by rw [og3.mem, m2]
    have hr : ∀ p : Addr, famR p c ∈ s.rd → ∀ j < c, ∀ k, k + 4 ≤ 256 →
        InRegions (s3.rd ++ s3.wr) (coeffAddr (p + BitVec.ofNat 64 (1024 * j)) k) 16 := fun p hp j hj k hk =>
      ⟨famR p c, by rw [k13.2.1, rd1]; exact List.mem_append_left _ hp, by
        rw [coeffAddr, VG.Offset.add_add]; exact VG.Offset.contains_base _ (by omega_using [hj, hk]) (by omega_using [hc7, hj, hk])⟩
    refine WP.seq (WP.mono (pass_ok (s₀ := s3) hc7 (by rw [k13.2.2, wr1]; exact hwo)
      (hr _ (by rw [hrd]; simp)) (hr _ (by rw [hrd]; simp))
      (fun j hj => (d1.sub_right (fam_sub _ hj)).symm) (fun j hj => (d2.sub_right (fam_sub _ hj)).symm)
      (fun j hj k hk => by rw [famV, m3, hm _ d4 j hj k hk]; exact pa j hj k (by rw [n_eq]; exact hk))
      (fun j hj k hk => by rw [famV, m3, hm _ d5 j hj k hk]; exact pb j hj k (by rw [n_eq]; exact hk))
      h8 (by rw [k13.gpr (by decide), h101]) (by rw [k13.gpr (by decide), hdx1]) c3 x3) fun u ⟨hP, ku, fu⟩ => ?_)
    refine WP.mono (invBody_ok (by rw [ku.gpr (by decide), k13.gpr (by decide), hdi1])
      (by rw [ku.gpr (by decide), k13.gpr (by decide), hsi1]) hP
      (by rw [ku.2.2, k13.2.2, wr1]; exact hwo) (by rw [ku.2.2, k13.2.2, wr1]; exact hws) d3) fun v ⟨hv, fv⟩ => ⟨?_, ?_⟩
    · rw [dotP_eq (m := s.mem) (fun j hj k hk => by rw [m3, hm _ d4 j hj k hk])
        (fun j hj k hk => by rw [m3, hm _ d5 j hj k hk])] at hv
      exact hv
    · have f1' : Frame [pR (s.gpr .rdi), pR (s.gpr .rcx)] s.mem s1.mem := by
        rw [← og.mem]; exact frame_fs f1 fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact .inr (mx_sub' _)
      have fu' : Frame [pR (s.gpr .rdi), pR (s.gpr .rcx)] s1.mem u.mem := by
        rw [← m3]; exact frame_fs fu fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact .inl fun _ h => h
      exact (f1'.trans fu').trans fv
  obtain ⟨tr, s', he, ⟨hP, hf⟩, hk2⟩ := WP.keep [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11, .rsi] hW (writesOnly_of hk)
  exact ⟨tr, s', he, abiPreserved_of_ctl hctl he (gprPreserved_of hk2 (by decide) hf (by simpa using ⟨r1, r2⟩)), hP⟩

theorem ct4 : ConstantTime isa (dotK 4).pre (dotK 4).pub (dotInvSse2 4) :=
  VG.Taint.constantTime (A := taint) dotτ (dot_agree 4) (by taint_decide)

theorem verified4 : Verified X86_64.target (dotInvSse2 4) (Proof.MlDsa.dotInverseContract 4 X86_64.abi) :=
  Verified.of_correct (correct (by decide) (by decide +kernel) (by decide +kernel)) ct4
    (by dot_implies dotSat 4)

theorem ct5 : ConstantTime isa (dotK 5).pre (dotK 5).pub (dotInvSse2 5) :=
  VG.Taint.constantTime (A := taint) dotτ (dot_agree 5) (by taint_decide)

theorem verified5 : Verified X86_64.target (dotInvSse2 5) (Proof.MlDsa.dotInverseContract 5 X86_64.abi) :=
  Verified.of_correct (correct (by decide) (by decide +kernel) (by decide +kernel)) ct5
    (by dot_implies dotSat 5)

theorem ct7 : ConstantTime isa (dotK 7).pre (dotK 7).pub (dotInvSse2 7) :=
  VG.Taint.constantTime (A := taint) dotτ (dot_agree 7) (by taint_decide)

theorem verified7 : Verified X86_64.target (dotInvSse2 7) (Proof.MlDsa.dotInverseContract 7 X86_64.abi) :=
  Verified.of_correct (correct (by decide) (by decide +kernel) (by decide +kernel)) ct7
    (by dot_implies dotSat 7)

end VG.Proof.MlDsa.X86_64.Arith.DotS

end

end

/-! ### `MlDsa.X86_64.Sample.Rej4Verified`, which this module and modules that import it used -/

section

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly4` and `vg_mldsa_rej_ntt_poly4_avx2`, verified

The contract of the proofs (`r4K`) implies the shared one of `Spec/`: a seed
with 256 coefficients in the 1008 bytes both implementations sample from has
them within those bounds (`rejNTT_some`), and one without has none within the
least bound (`rejNTT_none`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Rej4

open VG VG.X86_64
open VG.Proof.MlDsa.Sample (rnFold rejNTT_some rejNTT_none)
open VG.Proof.MlDsa.X86_64.Sample (leakBytes_inj)
open VG.Spec.MlDsa (G)
open VG.Spec.Sha3 (bytesAt)

theorem seed4_eq : Proof.MlDsa.seed4 = Proof.MlKem.seed4 := rfl
theorem poly4_eq : Proof.MlDsa.poly4 = Proof.MlKem.poly4 := rfl

theorem r4_post {s s' : State} (h : r4K.post s s') :
    let r := (s'.gpr .rax).setWidth 32
    (r = 1 → ∀ k < 4, Proof.MlDsa.Reduced s'.mem (Proof.MlDsa.poly4 (s.gpr .rsi) k)) ∧
      ((r = 1 ∧ ∀ k < 4, ∃ b : Spec.MlDsa.Bounds, Spec.MlDsa.rejNTTPoly b.rejNTT
          (Proof.MlDsa.seed4 s.mem (s.gpr .rdi) k) = some (Proof.MlDsa.polyAt s'.mem (Proof.MlDsa.poly4 (s.gpr .rsi) k))) ∨
        (r = 0 ∧ ∃ k < 4, Spec.MlDsa.rejNTTPoly Spec.MlDsa.minBounds.rejNTT
          (Proof.MlDsa.seed4 s.mem (s.gpr .rdi) k) = none)) := by
  obtain ⟨hr, hp⟩ := h
  intro r
  simp only [seed4_eq, poly4_eq]
  by_cases hall : ((List.range 4).all fun k =>
      (rnFold [] (G (Proof.MlKem.seed4 s.mem (s.gpr .rdi) k) 1008)).length == 256) = true
  · rw [ite_eq_left hall] at hr
    have hs : ∀ k < 4, (rnFold [] (G (Proof.MlKem.seed4 s.mem (s.gpr .rdi) k) 1008)).length = 256 := fun k hk => by
      simpa using List.all_eq_true.mp hall k (List.mem_range.mpr hk)
    refine ⟨fun _ k hk => (hp k hk (hs k hk)).1, .inl ⟨hr, fun k hk => ⟨{ Spec.MlDsa.minBounds with rejNTT := 1008 }, ?_⟩⟩⟩
    show Spec.MlDsa.rejNTTPoly 1008 _ = _
    rw [rejNTT_some (hs k hk), (hp k hk (hs k hk)).2]
  · rw [ite_eq_right hall] at hr
    refine ⟨fun h1 => absurd (hr.symm.trans h1) (by decide), .inr ⟨hr, ?_⟩⟩
    simp only [List.all_eq_true, List.mem_range, Classical.not_forall, beq_iff_eq] at hall
    obtain ⟨k, hk, hk'⟩ := hall
    exact ⟨k, hk, rejNTT_none (B := 1008) (by decide) (by decide) hk'⟩

theorem r4_pre (s : State) (h : (Proof.MlDsa.rejNTT4Contract X86_64.abi 24).pre s) : r4K.pre s := by
  revert s h
  sig_implies_pre [Proof.MlDsa.rejNTT4Contract, Proof.MlDsa.rejNTT4Sig, r4K, MlKem.X86_64.sample4K, X86_64.abi,
    X86_64.argRegs]

export VG.Proof.MlDsa.Sample (rej4Res seed4_of136 rej4Res_congr rej4Res_max)

/-- The public data of two calls include their seeds. -/
theorem r4_pub {S : Nat} (s₁ s₂ : State) (h : (Proof.MlDsa.rejNTT4Contract X86_64.abi S).pub s₁ s₂) :
    bytesAt s₁.mem (s₁.gpr .rdi) 136 = bytesAt s₂.mem (s₂.gpr .rdi) 136 := by
  sig_pub [Proof.MlDsa.rejNTT4Contract, Proof.MlDsa.rejNTT4Sig, X86_64.abi, X86_64.argRegs] at h
  obtain ⟨_, hb, _⟩ := h
  exact leakBytes_inj hb

/-- The result of code that meets `r4K`. -/
theorem rej4_ret {c : Prog isa}
    (hc : ∀ σ, r4K.pre σ → ∃ t s', Exec isa c σ t s' ∧ abiPreserved σ s' ∧ r4K.post σ s') {s s' : State}
    {t : List Leak} (h : (Proof.MlDsa.rejNTT4Contract X86_64.abi 24).pre s) (e : Exec isa c s t s') :
    (s'.gpr .rax).setWidth 32 = rej4Res s.mem (s.gpr .rdi) := by
  obtain ⟨_, _, e', _, hq⟩ := hc s (r4_pre s h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact hq.1

theorem rej4_verified (c : Prog isa) (hc : ∀ σ, r4K.pre σ → ∃ t s', Exec isa c σ t s' ∧ abiPreserved σ s' ∧ r4K.post σ s')
    (ht : ConstantTime isa r4K.pre r4K.pub c) : Verified X86_64.target c (Proof.MlDsa.rejNTT4Contract X86_64.abi 24) :=
  Verified.of_correct hc ht
    { pre := r4_pre
      post := by
        intro s s' _ h
        sig_post [Proof.MlDsa.rejNTT4Contract, Proof.MlDsa.rejNTT4Sig, r4K, X86_64.abi, X86_64.argRegs]
        exact r4_post h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.MlDsa.rejNTT4Contract, Proof.MlDsa.rejNTT4Sig, r4K, MlKem.X86_64.sample4K, X86_64.abi,
          X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.MlDsa.rejNTT4Contract, Proof.MlDsa.rejNTT4Sig, r4K, MlKem.X86_64.sample4K, X86_64.abi,
          X86_64.argRegs]
        sig_simp [Proof.MlDsa.rejNTT4Contract, Proof.MlDsa.rejNTT4Sig, r4K, MlKem.X86_64.sample4K, X86_64.abi,
          X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals first | with_reducible assumption | exact leakBytes_inj ‹_›
      sat := by
        sig_implies_sat [Proof.MlDsa.rejNTT4Contract, Proof.MlDsa.rejNTT4Sig, r4K, MlKem.X86_64.sample4K, X86_64.abi,
          X86_64.argRegs] [MlKem.X86_64.sample4Sat] using MlKem.X86_64.sample4Sat }

theorem rejNTT4_verified : Verified X86_64.target Impl.MlDsa.X86_64.Sample.Rej4.rejNTT4
    (Proof.MlDsa.rejNTT4Contract X86_64.abi 24) := rej4_verified _ correct_scalar ct_scalar

theorem rejNTT4_ret {s s' : State} {t : List Leak} (h : (Proof.MlDsa.rejNTT4Contract X86_64.abi 24).pre s)
    (e : Exec isa Impl.MlDsa.X86_64.Sample.Rej4.rejNTT4 s t s') :
    (s'.gpr .rax).setWidth 32 = rej4Res s.mem (s.gpr .rdi) := rej4_ret correct_scalar h e

end VG.Proof.MlDsa.X86_64.Rej4

end

end

/-!
# ML-DSA on x86-64: what the callers of the polynomial arithmetic need of it

An `ArithImpl` is an implementation of the polynomial arithmetic
(`Impl.MlDsa.X86_64.Arith.Backend`) with what key generation, signing and
verification need of each of its functions (`FnOk`): it meets its contract
without using the stack, never writes `rsp`, calls no deeper than twice, and
loads MXCSR only to restore it. Each is a variant of the interface `MlDsaArith`
on x86-64 (`Variants/MlDsaArith/X86_64/`), and the functions that call it are
proven once for all of them (`Generic/MlDsaArith/X86_64/`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith

/-- What a caller needs of a function with the contract `k` (given the
stack its calls use) and the code `c`. -/
structure FnOk (k : Nat → Contract isa) (c : Prog isa) : Prop where
  ver : Verified X86_64.target c (k 0)
  nosp : NoSp c
  mx : c.allInstrs (fun i => !touchesMxcsr i) = true
  depth : c.depth ≤ 2
  ctl : ctlOk c = true
  sp : c.all (fun i => !isa.writesSp i) = true

/-- What a caller needs of `vg_mldsa_rej_ntt_poly4`, which calls three deep
and takes 24 bytes of stack. -/
structure Rej4Ok (c : Prog isa) : Prop where
  ver : Verified X86_64.target c (Proof.MlDsa.rejNTT4Contract X86_64.abi 24)
  nosp : NoSp c
  mx : c.allInstrs (fun i => !touchesMxcsr i) = true
  depth : c.depth ≤ 3
  ctl : ctlOk c = true
  sp : c.all (fun i => !isa.writesSp i) = true
  /-- Its result is whether each seed has 256 coefficients in its first 1008 bytes of output, as
  both implementations', which signing branches on. -/
  ret : ∀ s t s', (Proof.MlDsa.rejNTT4Contract X86_64.abi 24).pre s → Exec isa c s t s' →
    (s'.gpr .rax).setWidth 32 = Rej4.rej4Res s.mem (s.gpr .rdi)

/-- What a caller needs of `vg_mldsa_expand_mask_poly4`, which calls three
deep and takes 24 bytes of stack. -/
structure Mask4Ok (c : Prog isa) : Prop where
  ver : Verified X86_64.target c (Proof.MlDsa.expandMask4Contract X86_64.abi 24)
  nosp : NoSp c
  mx : c.allInstrs (fun i => !touchesMxcsr i) = true
  depth : c.depth ≤ 3
  ctl : ctlOk c = true
  sp : c.all (fun i => !isa.writesSp i) = true

/-- Each function of the backend `B` meets its contract, and is safe to call. -/
structure BackendOk (B : Backend) : Prop where
  ntt : FnOk (fun S => Proof.MlDsa.nttContract X86_64.abi S) B.ntt
  invNtt : FnOk (fun S => Proof.MlDsa.Arith.Representation.inverseContract B.montgomery X86_64.abi S) B.invNtt
  mul : FnOk (fun S => Proof.MlDsa.Arith.Representation.productContract B.montgomery X86_64.abi S) B.mul
  mulAdd : FnOk (fun S => Proof.MlDsa.Arith.Representation.accumulateContract B.montgomery X86_64.abi S) B.mulAdd
  add : FnOk (fun S => Proof.MlDsa.addContract X86_64.abi S) B.add
  sub : FnOk (fun S => Proof.MlDsa.subContract X86_64.abi S) B.sub
  highBits : FnOk (fun S => Proof.MlDsa.highBitsContract X86_64.abi S) B.highBits
  lowBits : FnOk (fun S => Proof.MlDsa.lowBitsContract X86_64.abi S) B.lowBits
  normLt : FnOk (fun S => Proof.MlDsa.normLtContract X86_64.abi S) B.normLt
  makeHint : FnOk (fun S => Proof.MlDsa.makeHintContract X86_64.abi S) B.makeHint
  useHint : FnOk (fun S => Proof.MlDsa.useHintContract X86_64.abi S) B.useHint
  rej4 : Rej4Ok B.rej4
  expandMask4 : Mask4Ok B.expandMask4
  dotInv : ∀ c, c = 4 ∨ c = 5 ∨ c = 7 → FnOk (fun S => Proof.MlDsa.dotInverseContract c X86_64.abi S) (B.dotInv c)

/-- An implementation of the polynomial arithmetic on x86-64. -/
structure ArithImpl where
  code : Backend
  ok : BackendOk code
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String

/-- `FnOk` of code verified without stack, from evaluating it. -/
theorem FnOk.of {k : Nat → Contract isa} {c : Prog isa} (h : Verified X86_64.target c (k 0))
    (hn : c.allInstrs (fun i => !Taint.clobbers i .rsp && !touchesMxcsr i) = true) (hd : c.depth ≤ 2)
    (hc : ctlOk c = true) (hs : c.allInstrs (fun i => !isa.writesSp i) = true) : FnOk k c :=
  ⟨h, (Proof.MlKem.X86_64.nospMx_of hn).1, (Proof.MlKem.X86_64.nospMx_of hn).2, hd, hc, Code.all_of_allInstrs hs⟩

/-- The tests of code that calls no deeper than `d`, for the kernel: one walk
of the code for the two tests of `rsp` and that of MXCSR, with one match for each instruction
(`Proof/Framework/X86_64/InstrBits.lean`). -/
noncomputable def fnOkB (d : Nat) (c : Prog isa) : Bool :=
  c.allInstrs (hasBits (bMx + bSp + bNs)) && Nat.ble c.depth d && ctlOk c

theorem fnOkB_spec {d : Nat} {c : Prog isa} (h : fnOkB d c = true) :
    NoSp c ∧ c.allInstrs (fun i => !touchesMxcsr i) = true ∧ c.depth ≤ d ∧ ctlOk c = true ∧
      c.all (fun i => !isa.writesSp i) = true := by
  simp only [fnOkB, Bool.and_eq_true, Nat.ble_eq] at h
  exact ⟨Proof.MlKem.X86_64.nosp_of (Code.noRsp_of_bits (m := bMx + bSp + bNs) rfl h.1.1),
    Code.noTouchMx_of_bits (m := bMx + bSp + bNs) rfl h.1.1, h.1.2, h.2,
    Code.spSafe_of_bits (m := bMx + bSp + bNs) rfl h.1.1⟩

/-- `FnOk` of code verified without stack, from `fnOkB`. -/
theorem FnOk.of_bits {k : Nat → Contract isa} {c : Prog isa} (h : Verified X86_64.target c (k 0))
    (hb : fnOkB 2 c = true) : FnOk k c :=
  have h' := fnOkB_spec hb
  ⟨h, h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩

/-- The tests of the SSE2 code's functions, in one declaration: sixteen
functions, of four tests each. -/
theorem sse2_checks :
    fnOkB 2 Backend.sse2.ntt = true ∧ fnOkB 2 Backend.sse2.invNtt = true ∧ fnOkB 2 Backend.sse2.mul = true ∧
    fnOkB 2 Backend.sse2.mulAdd = true ∧ fnOkB 2 Backend.sse2.add = true ∧ fnOkB 2 Backend.sse2.sub = true ∧
    fnOkB 2 Backend.sse2.highBits = true ∧ fnOkB 2 Backend.sse2.lowBits = true ∧
    fnOkB 2 Backend.sse2.normLt = true ∧ fnOkB 2 Backend.sse2.makeHint = true ∧
    fnOkB 2 Backend.sse2.useHint = true ∧ fnOkB 3 Backend.sse2.rej4 = true ∧
    fnOkB 3 Backend.sse2.expandMask4 = true ∧ fnOkB 2 (Backend.sse2.dotInv 4) = true ∧
    fnOkB 2 (Backend.sse2.dotInv 5) = true ∧ fnOkB 2 (Backend.sse2.dotInv 7) = true := by
  decide +kernel

/-- The SSE2 code. -/
def ArithImpl.sse2 : ArithImpl where
  code := .sse2
  ok :=
    { ntt := FnOk.of_bits Arith.ntt_verified sse2_checks.1
      invNtt := FnOk.of_bits Arith.nttInv_verified sse2_checks.2.1
      mul := FnOk.of_bits Arith.mul_verified sse2_checks.2.2.1
      mulAdd := FnOk.of_bits Arith.mulAdd_verified sse2_checks.2.2.2.1
      add := FnOk.of_bits Arith.add_verified sse2_checks.2.2.2.2.1
      sub := FnOk.of_bits Arith.sub_verified sse2_checks.2.2.2.2.2.1
      highBits := FnOk.of_bits Round.highBits_verified sse2_checks.2.2.2.2.2.2.1
      lowBits := FnOk.of_bits Round.lowBits_verified sse2_checks.2.2.2.2.2.2.2.1
      normLt := FnOk.of_bits Round.normLt_verified sse2_checks.2.2.2.2.2.2.2.2.1
      makeHint := FnOk.of_bits Round.makeHint_verified sse2_checks.2.2.2.2.2.2.2.2.2.1
      useHint := FnOk.of_bits Round.useHint_verified sse2_checks.2.2.2.2.2.2.2.2.2.2.1
      rej4 :=
        have h := fnOkB_spec sse2_checks.2.2.2.2.2.2.2.2.2.2.2.1
        ⟨Rej4.rejNTT4_verified, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, fun _ _ _ => Rej4.rejNTT4_ret⟩
      expandMask4 :=
        have h := fnOkB_spec sse2_checks.2.2.2.2.2.2.2.2.2.2.2.2.1
        ⟨Mask4.expandMask4_verified, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
      dotInv := fun c hc => by
        rcases hc with rfl | rfl | rfl
        · exact FnOk.of_bits Arith.DotS.verified4 sse2_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        · exact FnOk.of_bits Arith.DotS.verified5 sse2_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        · exact FnOk.of_bits Arith.DotS.verified7 sse2_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }
  features := []

end VG.Proof.MlDsa.X86_64
