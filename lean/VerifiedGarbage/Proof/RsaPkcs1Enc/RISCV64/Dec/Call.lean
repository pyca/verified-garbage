module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Frame
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivPre
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCall
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivVerified
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: the setup and the private-key operation

Untrusted: everything here is checked by Lean. As for signing
(`Proof/RsaPkcs1Sig/RISCV64/Sign/Call.lean`): the saves, the values kept in
`s0`–`s6`, the call's twelve stack arguments copied from ours and its
arguments in registers (`setup_ok`, into `AtCall`); the regions the call is
narrowed to (`callRd`, `callWr`) and its precondition (`preP_entry`); and
what it writes (`call_ok`, into `AtRet`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64

/-! ## Our stack arguments -/

theorem arg_frame {s : State} (h : DPre s) {m : Mem} (hm : Frame [kR s] s.mem m) {j : Nat} (hj : j < 15) :
    m.readW (stackArgAddr s j) 64 = stackArg s j :=
  hm.readW (in_aR hj) (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.ka.symm) (by decide)

theorem arg_in {s t : State} (h : DPre s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 15) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 := by
  rw [hrd, h.hrd]
  exact ⟨_, List.mem_append_left _ (by simp), in_aR hj⟩

theorem arg_al {s : State} (h : DPre s) (j : Nat) : (stackArgAddr s j).toNat % 8 = 0 := by
  simp only [stackArgAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := s.sp.isLt; have := h.sp16
  omega

/-! ## The setup -/

/-- The call's stack arguments. -/
abbrev psaR (s : State) : Region := ⟨fb s, 96⟩

/-- At the call of `vg_rsa_private_checked`. -/
structure AtCall (s t : State) : Prop extends Mid [] s t where
  a0 : t.gpr .a0 = s.gpr .a0
  a1 : t.gpr .a1 = s.gpr .a4
  a2 : t.gpr .a2 = s.gpr .a3
  a3 : t.gpr .a3 = s.gpr .a4
  a4 : t.gpr .a4 = s.gpr .a5
  a5 : t.gpr .a5 = s.gpr .a6
  a6 : t.gpr .a6 = stackArg s 1
  a7 : t.gpr .a7 = s.gpr .a4
  psa : ∀ i < 12, t.mem.readW (fb s + BitVec.ofNat 64 (8 * i)) 64 = stackArg s (3 + i)

/-- After copying the first `n` stack arguments, from `w`. -/
structure CI (s w : State) (n : Nat) (t : State) : Prop where
  keep : Kept [.t1] w t
  mem : Frame [psaR s] w.mem t.mem
  psa : ∀ i < n, t.mem.readW (fb s + BitVec.ofNat 64 (8 * i)) 64 = stackArg s (3 + i)

theorem psa_sub (s : State) : Region.Sub (psaR s) (kR s) := by
  have := frame_sub s (d := 0) (n := 96) (by decide)
  rwa [BitVec.add_zero] at this

theorem copy_step {s w : State} (h : DPre s) (hw0 : w.gpr .t0 = fb s) (hw6 : w.gpr .t6 = stackArgAddr s 0)
    (hrd : w.rd = s.rd) (hwr : w.wr = frR s :: s.wr) (hm : Frame [kR s] s.mem w.mem) {n : Nat} (hn : n < 12)
    {t : State} (hc : CI s w n t) : WP isa (.block (copyArg n)) t (CI s w (n + 1)) := by
  have hmt : Frame [kR s] s.mem t.mem := hm.trans (hc.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, psa_sub s⟩)
  unfold copyArg
  refine wp_ld (a := stackArgAddr s (3 + n)) (by rw [hc.keep.get .t6, hw6, ← stackArgAddr_eq]) (arg_al h _)
    (arg_in h (hc.keep.rd.trans hrd) (by omega)) (fun t₁ o₁ e₁ => ?_) (by omega)
  refine wp_sd (a := fb s + BitVec.ofNat 64 (8 * n)) (by rw [o₁.get .t0, hc.keep.get .t0, hw0])
    (fb_al8 h (by omega)) (by rw [o₁.wr, hc.keep.wr, hwr]; exact in_fr s _ (by unfold frameBytes; omega))
    (fun t₂ m₂ => wp_nil ?_) (by omega)
  rw [arg_frame h hmt (by omega)] at e₁
  rw [e₁] at m₂
  refine ⟨(hc.keep.trans (o₁.keep.trans m₂.keep)).mono, ?_, fun i hi => ?_⟩
  · rw [m₂.mem, o₁.mem]
    exact hc.mem.writeW (List.mem_singleton_self _) _ (Offset.contains_base (fb s) (d := 8 * n) (n := 8) (k := 96)
      (by omega) (by omega))
  · rw [m₂.mem, o₁.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide)]
      exact hc.psa i hi
    · rw [Mem.readW_writeW_self64]

theorem copies_ok {s w : State} (h : DPre s) (hw0 : w.gpr .t0 = fb s) (hw6 : w.gpr .t6 = stackArgAddr s 0)
    (hrd : w.rd = s.rd) (hwr : w.wr = frR s :: s.wr) (hm : Frame [kR s] s.mem w.mem) :
    WP isa (.block ((List.range 12).flatMap copyArg)) w (CI s w 12) :=
  wp_range_flatMap (M := isa) (CI s w) (fun _ _ hn hc => copy_step h hw0 hw6 hrd hwr hm hn hc) 12
    (Nat.le_refl _) w ⟨Kept.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem setup_ok {s : State} (h : DPre s) :
    WP isa (.block setup) (allocd frameBytes s) (AtCall s) := by
  have hfa := fb_al h
  have e : setup = spill ++ (keeps ++ (List.range 12).flatMap copyArg ++ privRegs) := by
    simp only [setup, save_eq, List.append_assoc]
  rw [e]
  refine save_ok (s := s) (u := allocd frameBytes s) rfl rfl (by omega) (Frame.refl _ _) (fun _ _ => rfl)
    fun v kv v0 fv sv => ?_
  have gv : ∀ r, r ∉ [Reg.t0] → v.gpr r = s.gpr r := fun r hr => kv.gpr r hr
  have rdv : v.rd = s.rd := kv.rd
  have wrv : v.wr = frR s :: s.wr := kv.wr
  have spv : v.sp = fb s := kv.sp
  rw [List.append_assoc]
  simp only [keeps, argBase, List.cons_append, List.nil_append]
  refine wp_addSp (imm := frameBytes) (fun v₁ o₁ e₁ => wp_mov fun v₂ o₂ e₂ => wp_mov fun v₃ o₃ e₃ =>
    wp_mov fun v₄ o₄ e₄ => wp_mov fun v₅ o₅ e₅ => ?_) (by decide)
  have P₅ : Only [.t6, .s1, .s2, .s3, .s4] v v₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
  have t6₅ : v₅.gpr .t6 = stackArgAddr s 0 := by
    rw [o₅.get .t6, o₄.get .t6, o₃.get .t6, o₂.get .t6, e₁, spv, stackArgAddr_fb]; rfl
  refine wp_ld (a := stackArgAddr s 0) (by rw [t6₅, BitVec.add_zero]) (arg_al h 0)
    (arg_in h (P₅.rd.trans rdv) (j := 0) (by decide)) fun v₆ o₆ e₆ => ?_
  refine wp_ld (a := stackArgAddr s 1) (by rw [o₆.get .t6, t6₅]; exact (stackArgAddr_eq s 1).symm) (arg_al h 1)
    (arg_in h (o₆.rd.trans (P₅.rd.trans rdv)) (j := 1) (by decide)) fun v₇ o₇ e₇ => ?_
  refine wp_ld (a := stackArgAddr s 13) (by rw [o₇.get .t6, o₆.get .t6, t6₅]; exact (stackArgAddr_eq s 13).symm) (arg_al h 13)
    (arg_in h (o₇.rd.trans (o₆.rd.trans (P₅.rd.trans rdv))) (j := 13) (by decide)) (fun w o₈ e₈ => ?_)
    (by decide)
  have P : Only [.t6, .s1, .s2, .s3, .s4, .s5, .s6, .s0] v w := (P₅.trans (o₆.trans (o₇.trans o₈))).mono
  rw [P₅.mem, arg_frame h fv (j := 0) (by decide)] at e₆
  rw [o₆.mem, P₅.mem, arg_frame h fv (j := 1) (by decide)] at e₇
  rw [o₇.mem, o₆.mem, P₅.mem, arg_frame h fv (j := 13) (by decide)] at e₈
  have M : Mid [] s w := {
    sp := by rw [P.sp, spv]
    rd := by rw [P.rd, rdv]
    wr := by rw [P.wr, wrv]
    s0 := e₈
    s1 := by
      rw [o₈.get .s1, o₇.get .s1, o₆.get .s1, o₅.get .s1, o₄.get .s1, o₃.get .s1, e₂, o₁.get .a4,
        gv .a4 (by decide)]
    s2 := by
      rw [o₈.get .s2, o₇.get .s2, o₆.get .s2, o₅.get .s2, o₄.get .s2, e₃, o₂.get .a0, o₁.get .a0,
        gv .a0 (by decide)]
    s3 := by
      rw [o₈.get .s3, o₇.get .s3, o₆.get .s3, o₅.get .s3, e₄, o₃.get .a2, o₂.get .a2, o₁.get .a2,
        gv .a2 (by decide)]
    s4 := by
      rw [o₈.get .s4, o₇.get .s4, o₆.get .s4, e₅, o₄.get .a7, o₃.get .a7, o₂.get .a7, o₁.get .a7,
        gv .a7 (by decide)]
    s5 := by rw [o₈.get .s5, o₇.get .s5, e₆]
    s6 := by rw [o₈.get .s6, e₇]
    hi := fun r hr => by rw [P.gpr r (by revert r; decide), gv r (by revert r; decide)]
    mem := by rw [P.mem]; exact fv
    sv := by rw [P.mem]; exact sv }
  have w0 : w.gpr .t0 = fb s := by rw [P.get .t0, v0]
  have w6 : w.gpr .t6 = stackArgAddr s 0 := by rw [o₈.get .t6, o₇.get .t6, o₆.get .t6, t6₅]
  rw [WP.block_append_iff]
  refine WP.mono (copies_ok h w0 w6 M.rd M.wr M.mem) fun x hc => ?_
  have hf := M.frameMem (f := 0) (n := 96) (.inr (by decide)) (by decide)
    (by rw [BitVec.add_zero]; exact hc.mem)
  have M' : Mid [] s x := M.keep hc.keep hf.1 hf.2
  have gw : ∀ r ∈ [Reg.a0, .a3, .a5, .a6], x.gpr r = s.gpr r := fun r hr => by
    rw [hc.keep.gpr r (by revert r; decide), P.gpr r (by revert r; decide), gv r (by revert r; decide)]
  unfold privRegs
  refine wp_mov fun x₁ q₁ f₁ => wp_mov fun x₂ q₂ f₂ => wp_mov fun x₃ q₃ f₃ => wp_mov fun x₄ q₄ f₄ =>
    wp_mov fun x₅ q₅ f₅ => wp_mov fun x₆ q₆ f₆ => wp_mov fun x₇ q₇ f₇ => wp_nil ?_
  have O : Only [.a1, .a2, .a3, .a4, .a5, .a6, .a7] x x₇ :=
    (q₁.trans (q₂.trans (q₃.trans (q₄.trans (q₅.trans (q₆.trans q₇)))))).mono
  exact {
    toMid := M'.only O
    a0 := by rw [O.get .a0, gw .a0 (by decide)]
    a1 := by rw [q₇.get .a1, q₆.get .a1, q₅.get .a1, q₄.get .a1, q₃.get .a1, q₂.get .a1, f₁, M'.s1]
    a2 := by rw [q₇.get .a2, q₆.get .a2, q₅.get .a2, q₄.get .a2, q₃.get .a2, f₂, q₁.get .a3, gw .a3 (by decide)]
    a3 := by rw [q₇.get .a3, q₆.get .a3, q₅.get .a3, q₄.get .a3, f₃, q₂.get .s1, q₁.get .s1, M'.s1]
    a4 := by rw [q₇.get .a4, q₆.get .a4, q₅.get .a4, f₄, q₃.get .a5, q₂.get .a5, q₁.get .a5, gw .a5 (by decide)]
    a5 := by rw [q₇.get .a5, q₆.get .a5, f₅, q₄.get .a6, q₃.get .a6, q₂.get .a6, q₁.get .a6, gw .a6 (by decide)]
    a6 := by
      rw [q₇.get .a6, f₆, q₅.get .s6, q₄.get .s6, q₃.get .s6, q₂.get .s6, q₁.get .s6, M'.s6]
    a7 := by
      rw [f₇, q₆.get .s1, q₅.get .s1, q₄.get .s1, q₃.get .s1, q₂.get .s1, q₁.get .s1, M'.s1]
    psa := fun i hi => by rw [O.mem]; exact hc.psa i hi }

/-! ## The call -/

/-- The regions the call reads and writes. -/
abbrev callRd (s : State) : List Region := [nR s, eR s, iR s, pR s, qR s, dpR s, dqR s, qiR s, psaR s]

abbrev callWr (s : State) : List Region := [oR s, sR s]

/-- The call's narrowed entry state. -/
abbrev callE (s t : State) : State := t.callEntry.withRegions (callRd s) (callWr s)

theorem callE_gpr (s t : State) {r : Reg} (hr : r ∉ linkRegs := by decide) : (callE s t).gpr r = t.gpr r :=
  State.callEntry_gpr t hr

theorem callE_stackArg {s t : State} (A : AtCall s t) {i : Nat} (hi : i < 12) :
    stackArg (callE s t) i = stackArg s (3 + i) := by
  show t.mem.readW (stackArgAddr (callE s t) i) 64 = _
  rw [stackArgAddr, show (callE s t).sp = fb s from A.sp]
  exact A.psa i hi

theorem preP_entry {s t : State} (h : DPre s) (A : AtCall s t) : Rsa.RISCV64.Priv.PreP (callE s t) := by
  have hk := h.k2
  have fbt := fb_toNat h
  have kbt := kb_toNat h
  unfold stackBytes frameBytes Impl.Rsa.RISCV64.Priv.frameBytes at kbt
  unfold frameBytes at fbt
  have sa := fun i hi => callE_stackArg A (i := i) hi
  have hsp : (callE s t).sp = fb s := A.sp
  have cs := callee_sub s
  have ps := psa_sub s
  have hK : Rsa.RISCV64.Priv.kR (callE s t) = ⟨kb s, Impl.Rsa.RISCV64.Priv.frameBytes⟩ := by
    simp only [Rsa.RISCV64.Priv.kR, Rsa.RISCV64.Priv.fb, hsp, fb_eq, BitVec.add_sub_cancel]
  have ka : Region.Disjoint ⟨kb s, Impl.Rsa.RISCV64.Priv.frameBytes⟩ (psaR s) := by
    show Region.Disjoint _ ⟨fb s, 96⟩
    rw [fb_eq]
    exact (Offset.disjoint_base _ (by unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega)
      (by unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega)).symm
  have cs' : Region.Sub ⟨kb s, Impl.Rsa.RISCV64.Priv.frameBytes⟩ (kR s) := by
    have := cs; rwa [fb_eq, BitVec.add_sub_cancel] at this
  have g0 : (callE s t).gpr .a0 = s.gpr .a0 := (callE_gpr s t).trans A.a0
  have g1 : (callE s t).gpr .a1 = s.gpr .a4 := (callE_gpr s t).trans A.a1
  have g2 : (callE s t).gpr .a2 = s.gpr .a3 := (callE_gpr s t).trans A.a2
  have g3 : (callE s t).gpr .a3 = s.gpr .a4 := (callE_gpr s t).trans A.a3
  have g4 : (callE s t).gpr .a4 = s.gpr .a5 := (callE_gpr s t).trans A.a4
  have g5 : (callE s t).gpr .a5 = s.gpr .a6 := (callE_gpr s t).trans A.a5
  have g6 : (callE s t).gpr .a6 = stackArg s 1 := (callE_gpr s t).trans A.a6
  have g7 : (callE s t).gpr .a7 = s.gpr .a4 := (callE_gpr s t).trans A.a7
  have hO : Rsa.RISCV64.Priv.oR (callE s t) = oR s := by simp only [Rsa.RISCV64.Priv.oR, g0, g1, oR, h.h1]
  have hN : Rsa.RISCV64.Priv.nR (callE s t) = nR s := by simp only [Rsa.RISCV64.Priv.nR, g2, g3]
  have hE : Rsa.RISCV64.Priv.eR (callE s t) = eR s := by simp only [Rsa.RISCV64.Priv.eR, g4, g5]
  have hI : Rsa.RISCV64.Priv.iR (callE s t) = iR s := by simp only [Rsa.RISCV64.Priv.iR, g6, g7, iR, h.hi]
  have hP : Rsa.RISCV64.Priv.pR (callE s t) = pR s := by
    simp only [Rsa.RISCV64.Priv.pR, sa 0 (by decide), sa 1 (by decide)]
  have hQ : Rsa.RISCV64.Priv.qR (callE s t) = qR s := by
    simp only [Rsa.RISCV64.Priv.qR, sa 2 (by decide), sa 3 (by decide)]
  have hDP : Rsa.RISCV64.Priv.dpR (callE s t) = dpR s := by
    simp only [Rsa.RISCV64.Priv.dpR, sa 4 (by decide), sa 5 (by decide)]
  have hDQ : Rsa.RISCV64.Priv.dqR (callE s t) = dqR s := by
    simp only [Rsa.RISCV64.Priv.dqR, sa 6 (by decide), sa 7 (by decide)]
  have hQI : Rsa.RISCV64.Priv.qiR (callE s t) = qiR s := by
    simp only [Rsa.RISCV64.Priv.qiR, sa 8 (by decide), sa 9 (by decide)]
  have hS : Rsa.RISCV64.Priv.sR (callE s t) = sR s := by
    simp only [Rsa.RISCV64.Priv.sR, sa 10 (by decide), sa 11 (by decide)]
  have hA : Rsa.RISCV64.Priv.aR (callE s t) = psaR s := by
    simp only [Rsa.RISCV64.Priv.aR, stackArgAddr, hsp, Nat.mul_zero, BitVec.add_zero]
  have s0 := sa 0 (by decide)
  have s1 := sa 1 (by decide)
  have s2 := sa 2 (by decide)
  have s3 := sa 3 (by decide)
  have s4 := sa 4 (by decide)
  have s5 := sa 5 (by decide)
  have s6 := sa 6 (by decide)
  have s7 := sa 7 (by decide)
  have s8 := sa 8 (by decide)
  have s9 := sa 9 (by decide)
  have s10 := sa 10 (by decide)
  have s11 := sa 11 (by decide)
  have wo' : (s.gpr .a0).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 := h.h1 ▸ h.wo
  have wi' : (stackArg s 1).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 := h.hi ▸ h.wi
  have fa := fb_al h
  refine ⟨by rw [hsp]; exact fa, by rw [hsp]; unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega,
    by rw [hsp]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hN, hE, hI, hP, hQ, hDP, hDQ, hQI, hA]; rfl
  · rw [hO, hS]; rfl
  · rw [hO, hN]; exact h.on
  · rw [hO, hE]; exact h.oe
  · rw [hO, hI]; exact h.oi
  · rw [hO, hP]; exact h.op
  · rw [hO, hQ]; exact h.oq
  · rw [hO, hDP]; exact h.odp
  · rw [hO, hDQ]; exact h.odq
  · rw [hO, hQI]; exact h.oqi
  · rw [hO, hS]; exact h.os
  · rw [hO, hA]; exact (h.ko.sub_left ps).symm
  · rw [hN, hS]; exact h.ns
  · rw [hE, hS]; exact h.es
  · rw [hI, hS]; exact h.is
  · rw [hP, hS]; exact h.ps
  · rw [hQ, hS]; exact h.qs
  · rw [hDP, hS]; exact h.dps
  · rw [hDQ, hS]; exact h.dqs
  · rw [hQI, hS]; exact h.qis
  · rw [hS, hA]; exact (h.ks.sub_left ps).symm
  · rw [hK, hO]; exact h.ko.sub_left cs'
  · rw [hK, hN]; exact h.kn.sub_left cs'
  · rw [hK, hE]; exact h.ke.sub_left cs'
  · rw [hK, hI]; exact h.ki.sub_left cs'
  · rw [hK, hP]; exact h.kp.sub_left cs'
  · rw [hK, hQ]; exact h.kq.sub_left cs'
  · rw [hK, hDP]; exact h.kdp.sub_left cs'
  · rw [hK, hDQ]; exact h.kdq.sub_left cs'
  · rw [hK, hQI]; exact h.kqi.sub_left cs'
  · rw [hK, hS]; exact h.ks.sub_left cs'
  · rw [hK, hA]; exact ka
  · rw [g0, g1]; exact wo'
  · rw [g2, g3]; exact h.wn
  · rw [g4, g5]; exact h.we
  · rw [g6, g7]; exact wi'
  · rw [s0, s1]; exact h.wp
  · rw [s2, s3]; exact h.wq
  · rw [s4, s5]; exact h.wdp
  · rw [s6, s7]; exact h.wdq
  · rw [s8, s9]; exact h.wqi
  · rw [s10, s11]; exact h.ws
  · rw [g3]; exact h.k1
  · rw [g3]; exact h.k2
  · rw [g1, g3]
  · rw [g7, g3]
  · rw [g5]; exact h.e1
  · rw [g5, g3]; exact h.e2
  · rw [s1]; exact h.p1
  · rw [s1, g3]; exact h.p2
  · rw [s3]; exact h.q1
  · rw [s3, g3]; exact h.q2
  · rw [s5, s1]; exact h.h8
  · rw [s9, s1]; exact h.h12
  · rw [s7, s3]; exact h.h10
  · rw [g3, s11]; exact h.hs
  · rw [s10]; exact h.al

/-- The outcome of `vg_rsa_private_checked` of the input, from the caller's
buffers. -/
abbrev privOut (s u : State) : Prop :=
  Spec.Rsa.writtenOutcome u.mem (s.gpr .a0) (s.gpr .a4).toNat ((u.gpr .a0).setWidth 32)
    (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .a4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat))

/-- After the call. -/
structure AtRet (s u : State) : Prop extends Mid [oR s, sR s] s u where
  out : privOut s u

theorem call_covers {s t : State} (h : DPre s) (A : AtCall s t) :
    Covers (callRd s ++ callWr s) (t.rd ++ t.wr) ∧ Covers (callWr s) t.wr := by
  have hw : Covers (callWr s) t.wr := by
    rw [A.wr, h.hwr]
    exact Covers.of_mem fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right hw), hw⟩
  rw [A.rd, A.wr, h.hrd]
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · have := in_fr s s.wr (d := 0) (n := 96) (by decide)
    rw [BitVec.add_zero] at this
    exact Covers.right (Covers.one this)

theorem priv_sdepth : sdepth Impl.Rsa.RISCV64.Priv.code = Impl.Rsa.RISCV64.Priv.frameBytes := by decide +kernel

theorem call_ok {s t : State} (h : DPre s) (A : AtCall s t) {Q : State → Prop}
    (hQ : ∀ u, AtRet s u → Q u) : WP isa privCall t Q := by
  obtain ⟨hc, hw⟩ := call_covers h A
  have cs := callee_sub s
  unfold privCall
  refine WP.callAny (k := Rsa.RISCV64.Priv.fnContract) Rsa.RISCV64.Priv.code_correct
    (Rsa.RISCV64.Priv.pre_of_preP (preP_entry h A)) hc hw
    (fun u hrd hwr hsp hf hpres hpost => hQ u ?_) (by rw [priv_sdepth]; decide)
  have hb : below t.sp (sdepth Impl.Rsa.RISCV64.Priv.code) =
      ⟨fb s - BitVec.ofNat 64 Impl.Rsa.RISCV64.Priv.frameBytes, Impl.Rsa.RISCV64.Priv.frameBytes⟩ := by
    rw [priv_sdepth, A.sp]
  rw [hb] at hf
  simp only [callWr, List.cons_append, List.nil_append] at hf
  have hp : ∀ r ∈ preserved, u.gpr r = t.gpr r := hpres
  have ap : ∀ {d : Nat}, d + 8 ≤ frameBytes → ∀ r ∈ [oR s, sR s, (⟨fb s - BitVec.ofNat 64
      Impl.Rsa.RISCV64.Priv.frameBytes, Impl.Rsa.RISCV64.Priv.frameBytes⟩ : Region)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r := by
    intro d hd r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.ko.sub_left (frame_sub s hd)
    · exact h.ks.sub_left (frame_sub s hd)
    · rw [fb_eq, BitVec.add_sub_cancel, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact Offset.disjoint_base _ (by omega) (by unfold frameBytes Impl.Rsa.RISCV64.Priv.frameBytes at *; omega)
  have g : ∀ r ∈ kept, u.gpr r = t.gpr r := fun r hr => hp r (by revert r; decide)
  refine ⟨A.toMid.of g (hsp.trans rfl) hrd hwr ?_ (A.sv.frame hf fun p hp' r hr =>
      ap (by have := saved_offs p hp'; unfold oEnd frameBytes at *; omega) r hr), ?_⟩
  · refine A.mem.sub (fun r hr => ?_) |>.trans (hf.sub fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self .., cs⟩
  · have sa := fun i hi => callE_stackArg A (i := i) hi
    simp only [Rsa.RISCV64.Priv.fnContract, Rsa.RISCV64.Priv.fnPost, State.withRegions_mem,
      State.withRegions_gpr, State.callEntry_mem, callE_gpr s t (r := .a0), callE_gpr s t (r := .a2),
      callE_gpr s t (r := .a3), callE_gpr s t (r := .a4), callE_gpr s t (r := .a5), callE_gpr s t (r := .a6),
      A.a0, A.a2, A.a3, A.a4, A.a5, A.a6, sa 0 (by decide), sa 1 (by decide), sa 2 (by decide), sa 3 (by decide),
      sa 4 (by decide), sa 6 (by decide), sa 8 (by decide), Nat.reduceAdd] at hpost
    have hb := fun {p : Addr} {len : Nat} (hd : Region.Disjoint ⟨p, len⟩ (kR s)) (hl : len ≤ 2 ^ 64) =>
      bytes_of_frame (s := s) (rs := [kR s]) A.mem (p := p) (len := len)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hl
    have di : Region.Disjoint ⟨stackArg s 1, (s.gpr .a4).toNat⟩ (kR s) := by
      have := h.ki.symm; simp only [iR, h.hi] at this; exact this
    rw [hb h.kn.symm (by have := h.wn; omega), hb h.ke.symm (by have := h.we; omega),
      hb di (by have := h.wi; have := h.hi; omega), hb h.kp.symm (by have := h.wp; omega),
      hb h.kq.symm (by have := h.wq; omega),
      hb (h.h8 ▸ h.kdp.symm) (by have := h.wdp; omega), hb (h.h10 ▸ h.kdq.symm) (by have := h.wdq; omega),
      hb (h.h12 ▸ h.kqi.symm) (by have := h.wqi; omega)] at hpost
    exact hpost

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec
