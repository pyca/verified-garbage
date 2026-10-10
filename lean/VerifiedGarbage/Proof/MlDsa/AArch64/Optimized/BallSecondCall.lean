import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallSave
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallFrame

/-! ## From `BallArgs.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64 (mov)
open VG.Proof.MlDsa.AArch64.Sample.RejNtt (movQ_ok q_eq)
open VG.Impl.MlDsa.AArch64.Sample (movQ)

abbrev args : List Instr := [mov .x2 .x0,mov .x0 .x25,.movz .x .x1 136 0,.addImm .x .x3 .x25 840,
 .movz .x .x4 136 0,.addImm .x .x5 .x25 200]

structure SqueezeArgs (p : Addr) (pos : Nat) (s : State) : Prop where
  x0 : s.gpr .x0=p
  x1 : (s.gpr .x1).toNat=136
  x2 : (s.gpr .x2).toNat=pos
  x3 : s.gpr .x3=p+840
  x4 : (s.gpr .x4).toNat=136
  x5 : s.gpr .x5=p+200

theorem args_ok {p : Addr} {s : State} (h25 : s.gpr .x25=p) :
    WP isa (.block args) s fun u => Only [.x0,.x1,.x2,.x3,.x4,.x5] s u ∧
      SqueezeArgs p (s.gpr .x0).toNat u := by
  refine wp_mov fun s₁ h₁ e₁ => wp_mov fun s₂ h₂ e₂ => wp_movz fun s₃ h₃ e₃ =>
    wp_addImm (by decide) fun s₄ h₄ e₄ => wp_movz fun s₅ h₅ e₅ =>
    wp_addImm (by decide) fun u hu eu => wp_nil ?_
  refine ⟨(((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans hu).mono (by decide),?_,?_,?_,?_,?_,?_⟩
  · rw [hu.get .x0,h₅.get .x0,h₄.get .x0,h₃.get .x0,e₂,h₁.get .x25,h25]
  · rw [hu.get .x1,h₅.get .x1,h₄.get .x1,e₃]; rfl
  · rw [hu.get .x2,h₅.get .x2,h₄.get .x2,h₃.get .x2,h₂.get .x2,e₁]
  · rw [hu.get .x3,h₅.get .x3,e₄,h₃.get .x25,h₂.get .x25,h₁.get .x25,h25]; rfl
  · rw [hu.get .x4,e₅]; rfl
  · rw [eu,h₅.get .x25,h₄.get .x25,h₃.get .x25,h₂.get .x25,h₁.get .x25,h25]; rfl

abbrev restore : List Instr := [.ldr .x .x9 .x25 1800,.ldr .x .x10 .x25 1808,.ldr .x .x11 .x25 1816,
 .addImm .x .x2 .x25 840,.movz .x .x5 136 0] ++ movQ .x12 ++
 [.subImm .x .x12 .x12 2,.movz .x .x15 1 0]

structure Restored (p : Addr) (w9 w10 w11 : BitVec 64) (s : State) : Prop where
  x9 : s.gpr .x9=w9
  x10 : s.gpr .x10=w10
  x11 : s.gpr .x11=w11
  x2 : s.gpr .x2=p+840
  x5 : (s.gpr .x5).toNat=136
  x12 : (s.gpr .x12).toNat=Spec.MlDsa.q-2
  x15 : (s.gpr .x15).toNat=1

theorem restore_ok {p : Addr} {w9 w10 w11 : BitVec 64} {s : State} (h25 : s.gpr .x25=p)
    (hs : Saved p w9 w10 w11 s)
    (hin : ∀ d∈[1800,1808,1816],InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 d) 8) :
    WP isa (.block restore) s fun u => Only [.x9,.x10,.x11,.x2,.x5,.x12,.x15] s u ∧ Restored p w9 w10 w11 u := by
  unfold restore movQ
  simp only [List.cons_append,List.nil_append]
  refine wp_ldrx (a := p+1800) (by decide) (by rw [h25]; rfl) (hin _ (by simp)) fun s₁ h₁ e₁ =>
    wp_ldrx (a := p+1808) (by decide) (by rw [h₁.get .x25,h25]; rfl)
      (by rw [h₁.rd,h₁.wr]; exact hin _ (by simp)) fun s₂ h₂ e₂ =>
    wp_ldrx (a := p+1816) (by decide) (by rw [h₂.get .x25,h₁.get .x25,h25]; rfl)
      (by rw [h₂.rd,h₂.wr,h₁.rd,h₁.wr]; exact hin _ (by simp)) fun s₃ h₃ e₃ =>
    wp_addImm (by decide) fun s₄ h₄ e₄ => wp_movz fun s₅ h₅ e₅ =>
    movQ_ok fun s₆ h₆ e₆ => wp_subImm (by decide) fun s₇ h₇ e₇ => wp_movz fun u hu eu => wp_nil ?_
  refine ⟨(((((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).trans hu).mono (by decide),
    ?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hu.get .x9,h₇.get .x9,h₆.get .x9,h₅.get .x9,h₄.get .x9,h₃.get .x9,h₂.get .x9,e₁,hs.r9]
  · rw [hu.get .x10,h₇.get .x10,h₆.get .x10,h₅.get .x10,h₄.get .x10,h₃.get .x10,e₂,h₁.mem,hs.r10]
  · rw [hu.get .x11,h₇.get .x11,h₆.get .x11,h₅.get .x11,h₄.get .x11,e₃,h₂.mem,h₁.mem,hs.r11]
  · rw [hu.get .x2,h₇.get .x2,h₆.get .x2,h₅.get .x2,e₄,h₃.get .x25,h₂.get .x25,h₁.get .x25,h25]; rfl
  · rw [hu.get .x5,h₇.get .x5,h₆.get .x5,e₅]; rfl
  · rw [hu.get .x12,e₇,toNat_sub_n (by rw [e₆,q_eq]; decide),e₆,q_eq]; rfl
  · rw [eu]; rfl
end VG.Proof.MlDsa.AArch64.Optimized.Ball

end

/-! ## From `BallSecondCall.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample (polyR)
open VG.Spec.Sha3 (bytesAt stateAt)
open VG.Proof.MlDsa.AArch64.Sample.Ball (CStored)

/-- The resumed squeeze keeps the parser's spilled registers and its polynomial. -/
theorem resume_call_ok (v : Proof.Sha3.AArch64.Permutation) {P : Sp} {σ s : State}
    {c : Spec.MlDsa.IPoly} {w9 w10 w11 : BitVec 64} {pos : Nat} {Y : List Byte}
    (hp : SpOk P σ) (he : Env P σ s) (ha : SqueezeArgs P.scr pos s) (hpos : pos≤136)
    (hn : Spec.Sha3.squeezeFrom 136 (stateAt s.mem P.scr) pos 136=Y)
    (hs : Saved P.scr w9 w10 w11 s) (hc : CStored s.mem P.a c) :
    WP isa (.call ("vg_keccak_squeeze_scratch"++v.callee.suffix)
      (Impl.Sha3.AArch64.Stream.squeezeWith v.callee)) s fun u =>
      Env P σ u ∧ Saved P.scr w9 w10 w11 u ∧ CStored u.mem P.a c ∧
      bytesAt u.mem (P.at' 840) 136=Y := by
  have cw : Covers [⟨P.scr,200⟩,⟨P.at' 840,136⟩,⟨P.at' 200,640⟩] s.wr :=
    cov_scr hp he.wr fun r hr => by
      rcases mem3 hr with rfl|rfl|rfl
      · exact ⟨0,(at_zero).symm,by simp⟩
      · exact ⟨840,rfl,by simp⟩
      · exact ⟨200,rfl,by simp⟩
  refine squeeze_callWith v (st := P.scr) (out := P.at' 840) (sc := P.at' 200)
    (rate := 136) (pos := pos) (len := 136) ha.x0 ha.x1 ha.x2 ha.x3 ha.x4 ha.x5 (by decide) hpos
    (by rw [← at_zero (P := P)]; exact disj_scr (.inl (by omega)) (by omega) (by omega))
    (by rw [← at_zero (P := P)]; exact disj_scr (.inl (by omega)) (by omega) (by omega))
    (disj_scr (.inr (by omega)) (by omega) (by omega))
    (by rw [he.sp]; exact hp.sp16) (by rw [stk,he.sp]; exact hp.stk_scr.sub_right (sub_scr0 (by omega)))
    (by rw [stk,he.sp]; exact stk_scr' hp (by omega)) (by rw [stk,he.sp]; exact stk_scr' hp (by omega))
    (cov_rd cw) cw fun u hk hout _ _ => ?_
  refine ⟨he.call hp hk ?_,hs.keep hk.frame ?_,stored_frame hc hk.frame ?_,hout.trans hn⟩
  · intro r hr
    rcases mem4 hr with rfl|rfl|rfl|rfl
    · exact .inl ⟨0,200,by rw [at_zero],by decide⟩
    · exact .inl ⟨840,136,rfl,by decide⟩
    · exact .inl ⟨200,640,rfl,by decide⟩
    · exact .inr rfl
  · intro d hd r hr
    have hd0 : 1800≤d ∧ d≤1816 := by
      rcases mem3 hd with rfl | rfl | rfl <;> omega
    rcases mem4 hr with rfl|rfl|rfl|rfl
    · simpa only [at_zero] using (disj_scr (P := P) (a := d) (n := 8) (b := 0) (m := 200) (.inr (by omega)) (by omega) (by omega))
    · exact disj_scr (P := P) (a := d) (n := 8) (b := 840) (m := 136) (.inr (by omega)) (by omega) (by omega)
    · exact disj_scr (P := P) (a := d) (n := 8) (b := 200) (m := 640) (.inr (by omega)) (by omega) (by omega)
    · rw [he.sp]; exact (stk_scr' hp (a := d) (n := 8) (by omega)).symm
  · intro r hr
    rcases mem4 hr with rfl|rfl|rfl|rfl
    · exact hp.a_scr.sub_right (sub_scr0 (by decide))
    · exact a_scr' hp (by decide)
    · exact a_scr' hp (by decide)
    · rw [he.sp]; exact hp.stk_a.symm
end VG.Proof.MlDsa.AArch64.Optimized.Ball

end
