module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
public import VerifiedGarbage.Spec.Gcm
public import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.Proof.AesGcm.RISCV64.Ghash1
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Ghash1
public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM on RISCV64: `ghash1`, `absorb`, `flush` and `lens` are constant time

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/CTAbsorb.lean`): the invariants fix the context, the
state, `W` (`EnvC`), the stack pointer, the data's address and length and
the number of bytes absorbed so far modulo 16, and leave the rest
existential.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- An environment with the context, the state and `W` at `c`, `st` and `w`. -/
def EnvC (c st w sp : Addr) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ Env V sp s

theorem EnvC.of {V : Reg → BitVec 64} {sp : Addr} {s : State} (he : Env V sp s) :
    EnvC (V .s2) (V .s1) (V .s0) sp s := ⟨V, rfl, rfl, rfl, he⟩

theorem EnvC.pin {c st w sp : Addr} {s₁ s₂ : State} (h₁ : EnvC c st w sp s₁) (h₂ : EnvC c st w sp s₂)
    {r : Reg} (hr : r = .s2 ∨ r = .s1 ∨ r = .s0) : s₁.gpr r = s₂.gpr r := by
  obtain ⟨V₁, a₁, b₁, c₁, e₁⟩ := h₁
  obtain ⟨V₂, a₂, b₂, c₂, e₂⟩ := h₂
  rcases hr with rfl | rfl | rfl
  · rw [e₁.s2, e₂.s2, a₁, a₂]
  · rw [e₁.s1, e₂.s1, b₁, b₂]
  · rw [e₁.s0, e₂.s0, c₁, c₂]

theorem EnvC.sp {c st w sp : Addr} {s : State} (h : EnvC c st w sp s) : s.sp = sp := by
  obtain ⟨_, _, _, _, e⟩ := h; exact e.sp

/-- Before `ghash1 yo b o`, for the block at `P`. -/
structure GhIn (c st w sp : Addr) (b : Reg) (o : Nat) (P : Addr) (s : State) : Prop where
  env : EnvC c st w sp s
  hP : s.gpr b + BitVec.ofNat 64 o = P
  hpr : Covers [⟨P, 16⟩] (s.rd ++ s.wr)

section
variable {c st w sp : Addr} (L : Lay c st w)
include L

theorem ghash1_ct {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {b : Reg} {o : Nat}
    (hbo : (b = .s1 ∧ o = 32) ∨ (b = .s0 ∧ o = 96)) {P : Addr}
    (hpy : (⟨st + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨P, 16⟩)
    (hpw : (⟨P, 16⟩ : Region).Disjoint ⟨w + BitVec.ofNat 64 512, 256⟩) :
    CT (GhIn c st w sp b o P) (ghash1 yo b o) := by
  have hb : b = .s1 ∨ b = .s0 := by rcases hbo with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have ho : o < 2048 := by rcases hbo with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  refine CT.seq (J := fun s => GhCall s (c + BitVec.ofNat 64 240) (st + BitVec.ofNat 64 yo) P
    (w + BitVec.ofNat 64 512) 1 ∧ s.sp = sp) ?_ (fun s ⟨⟨V, h29, h30, h31, he⟩, hP, hpr⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s2, .s1, .s0])
        (.block [.addi .a0 .s2 240, .addi .a1 .s1 yo, .addi .a2 b o, .li .a3 1, .addi .a4 .s0 scrO])
        h).isSome = true := by
      rcases hyo with rfl | rfl <;> rcases hbo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ h₁ h₂ => ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr =>
      h₁.env.pin h₂.env (by simpa using hr)⟩) hc
  · refine WP.mono (ghArgs_ok hyo he b o hb ho hP) fun s₁ ⟨h3, h4, h5, h6, h7, hkeep, hk⟩ => ?_
    have he₁ : Env V sp s₁ := he.keep (fun r hr => hkeep r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide)) hk.sp hk.rd hk.wr
    have L' := L.v h29 h30 h31
    have hk' := he.stk'
    have hpk : (⟨P, 16 * 1⟩ : Region).Disjoint (below s₁.sp 2048) := by
      rw [he₁.sp]
      rcases hbo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [← hP, he.s1]; exact hk'.st.sub_left (Lay.stSub (by decide))
      · rw [← hP, he.s0]; exact hk'.w.sub_left (Lay.wSub (by decide))
    have hpf : P.toNat + 16 * 1 ≤ 2 ^ 64 := by
      rcases hbo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [← hP, he.s1]; exact L'.st_fit (d := 32) (by decide) (by decide)
      · rw [← hP, he.s0]; exact L'.w_fit (d := 96) (by decide) (by decide)
    have g := ghCall_mk L' hyo he₁ h3 h4 h5 h6 h7 (by decide)
      (by rw [h30]; simpa using hpy) (by rw [h31]; simpa using hpw) hpk hpf (by rw [hk.rd, hk.wr]; simpa using hpr)
    rw [h29, h30, h31] at g
    exact ⟨g, he₁.sp⟩
  · exact CT.gh fun s₁ s₂ h₁ h₂ => ⟨_, _, _, _, _, h₁.1, h₂.1, h₁.2.trans h₂.2.symm⟩

end

/-- Before `absorb yo`: `q` bytes in the buffer. -/
def AbsI (c st w sp : Addr) (yo : Nat) (D : Addr) (n q : Nat) (s : State) : Prop :=
  ∃ V H x, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ x.length % 16 = q ∧ AbsIn V sp yo H x D n s

/-- Part of the way, `j` bytes absorbed. -/
def MidI (c st w sp : Addr) (yo : Nat) (D : Addr) (n q j : Nat) (s : State) : Prop :=
  ∃ V H x m₀, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ x.length % 16 = q ∧ AbsMid V sp yo H x D n m₀ j s

section
variable {c st w sp : Addr} (L : Lay c st w) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

theorem absorbHead_ct {D : Addr} {n q : Nat} (hn : n ≠ 0) (hq : q ≠ 0) :
    CT (AbsI c st w sp yo D n q) (absorbHead yo) := by
  let J : State → Prop := fun s => ∃ V H x m₀ k, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧
    x.length % 16 = q ∧ HeadMid V sp yo H x D n m₀ k s
  refine CT.seq (J := J) ?_ (fun s ⟨V, H, x, h29, h30, h31, hx, hs⟩ =>
    WP.mono (headPre_ok (L.v h29 h30 h31) hyo hs hn (by omega_arith)) fun s' ⟨k, hm⟩ =>
      ⟨V, H, x, s.mem, k, h29, h30, h31, hx, hm⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s4, .s5, .s6, .s1]) headPre
        h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨V₁, _, x₁, _, b₁, _, hx₁, h₁⟩ ⟨V₂, _, x₂, _, b₂, _, hx₂, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.s4, h₂.s4]
    · rw [h₁.s5, h₂.s5]
    · rw [h₁.s6, h₂.s6, hx₁, hx₂]
    · rw [h₁.env.s1, h₂.env.s1, b₁, b₂]
  · refine CT.ite (decide (q + min (16 - q) n = 16)) (fun s ⟨_, _, _, _, _, _, _, _, hx, hm⟩ => by
      have := eval_sub16 hm.a3 hm.k16; rw [hm.kmin, hx] at this; exact this) (fun _ => ?_) (fun _ => CT.skip)
    refine (ghash1_ct L hyo (.inl ⟨rfl, rfl⟩) (P := st + BitVec.ofNat 64 32) ?_ ?_).mono
      fun s ⟨V, _, _, _, _, h29, h30, h31, _, hm⟩ => ⟨⟨V, h29, h30, h31, hm.env⟩, by rw [hm.env.s1, h30], ?_⟩
    · exact Lay.st_st (.inl (by omega_arith)) (by omega_arith) (by decide)
    · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
    · rw [← h30]; exact covers_left (hm.env.perm.stC (by decide))

theorem absorbFill_ct {D : Addr} {n q : Nat} (hn : n ≠ 0) (_hq : q < 16) :
    CT (AbsI c st w sp yo D n q) (absorbFill yo) :=
  CT.ite (decide (q = 0)) (fun s ⟨_, _, x, _, _, _, hx, hs⟩ => by
      have := eval_zero hs.s6 (by omega_arith); rw [hx] at this; exact this)
    (fun _ => CT.skip) fun hb => absorbHead_ct L hyo hn (by simpa using hb)

omit L in
/-- `absorbWhole`'s arguments of the call of `vg_ghash`. -/
theorem wholeArgs_ok {V : Reg → BitVec 64} {s : State} (he : Env V sp s) :
    WP isa (.block [.addi .a0 .s2 240, .addi .a1 .s1 yo, .addi .a4 .s0 scrO]) s
      (fun s₂ : State => s₂.gpr .a0 = V .s2 + BitVec.ofNat 64 240 ∧
        s₂.gpr .a1 = V .s1 + BitVec.ofNat 64 yo ∧ s₂.gpr .a4 = V .s0 + BitVec.ofNat 64 512 ∧
        (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a4 → s₂.gpr r = s.gpr r) ∧ Keeps s s₂) := by
  have h29 := he.s2; have h30 := he.s1; have h31 := he.s0
  refine Steps.wp_addi (by decide) fun s₁ u₁ => Steps.wp_addi (by omega) fun s₂ u₂ =>
    Steps.wp_addi (imm := scrO) (by decide) fun s₃ u₃ => WP.block_nil ?_
  refine ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h29],
    by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h30],
    by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h31, scrO],
    fun r a b d => by rw [u₃.other _ d, u₂.other _ b, u₁.other _ a],
    ⟨by rw [u₃.mem, u₂.mem, u₁.mem], by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr],
      by rw [u₃.sp, u₂.sp, u₁.sp]⟩⟩

theorem absorbWhole_ct {D : Addr} {n q j : Nat} : CT (MidI c st w sp yo D n q j) (absorbWhole yo) := by
  let nb := (n - j) / 16
  let J₁ : State → Prop := fun s => ∃ V, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ Env V sp s ∧
    DataOk (V .s1) (V .s0) s D n ∧ j ≤ n ∧
    s.gpr .a2 = D + BitVec.ofNat 64 j ∧ s.gpr .a3 = BitVec.ofNat 64 nb
  refine CT.seq (J := J₁) ?_ (fun s ⟨V, H, x, m₀, h29, h30, h31, hx, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s4, .s5]) (.block splitWhole)
        h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, _, _, _, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.s4, h₂.s4]
    · rw [h₁.s5, h₂.s5]
  · refine WP.mono (split_ok hs.le hs.data.lt hs.s4 hs.s5) fun s₁ ⟨h5, h6, _, _, hg₁, hk₁⟩ => ?_
    exact ⟨V, h29, h30, h31, hs.env.keep (fun r hr => hg₁ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide)) hk₁.sp hk₁.rd hk₁.wr, hs.data.of_eq hk₁.rd hk₁.wr hk₁.sp, hs.le, h5, h6⟩
  · refine CT.ite (decide (nb = 0)) (fun s ⟨_, _, _, _, _, hd, _, _, h6⟩ => eval_zero h6 (by
      have := hd.lt; omega_arith)) (fun _ => CT.skip) fun hb => ?_
    have h0 : nb ≠ 0 := by simpa using hb
    let J₂ : State → Prop := fun s => ∃ V, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ Env V sp s ∧
      DataOk (V .s1) (V .s0) s D n ∧ j ≤ n ∧
      s.gpr .a0 = V .s2 + BitVec.ofNat 64 240 ∧ s.gpr .a1 = V .s1 + BitVec.ofNat 64 yo ∧
      s.gpr .a2 = D + BitVec.ofNat 64 j ∧ s.gpr .a3 = BitVec.ofNat 64 nb ∧
      s.gpr .a4 = V .s0 + BitVec.ofNat 64 512
    refine CT.seq (J := J₂) ?_ (fun s ⟨V, h29, h30, h31, he, hd, hj, h5, h6⟩ => ?_) ?_
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s2, .s1, .s0])
          (.block [.addi .a0 .s2 240, .addi .a1 .s1 yo, .addi .a4 .s0 scrO]) h).isSome = true := by
        rcases hyo with rfl | rfl <;> exact ⟨_, by taint_decide⟩
      exact CT.taint _ (fun s₁ s₂ ⟨V₁, a₁, b₁, c₁, e₁, _⟩ ⟨V₂, a₂, b₂, c₂, e₂, _⟩ =>
        ⟨e₁.sp.trans e₂.sp.symm, fun r hr => (EnvC.pin ⟨V₁, a₁, b₁, c₁, e₁⟩ ⟨V₂, a₂, b₂, c₂, e₂⟩
          (by simpa using hr))⟩) hc
    · refine WP.mono (wholeArgs_ok hyo he) fun s₂ ⟨h3, h4, h7, hg₂, hk₂⟩ => ?_
      exact ⟨V, h29, h30, h31, he.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
        (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr, hd.of_eq hk₂.rd hk₂.wr hk₂.sp, hj, h3, h4,
        by rw [hg₂ _ (by decide) (by decide) (by decide), h5],
        by rw [hg₂ _ (by decide) (by decide) (by decide), h6], h7⟩
    · refine CT.gh fun s₁ s₂ ⟨V₁, a₁, b₁, c₁, he₁, hd₁, hj₁, a3, a4, a5, a6, a7⟩
        ⟨V₂, a₂, b₂, c₂, he₂, hd₂, hj₂, b3, b4, b5, b6, b7⟩ => ?_
      have hdj₁ := hd₁.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith)
      have hdj₂ := hd₂.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith)
      have g₁ := ghCall_mk (L.v a₁ b₁ c₁) hyo he₁ a3 a4 a5 a6 a7 (by have := hd₁.lt; omega_arith)
        (hdj₁.st.sub_right (Lay.stSub (by omega_arith))).symm (hdj₁.w.sub_right (Lay.wSub (by decide))) hdj₁.sk
        hdj₁.fit hdj₁.rd
      have g₂ := ghCall_mk (L.v a₂ b₂ c₂) hyo he₂ b3 b4 b5 b6 b7 (by have := hd₂.lt; omega_arith)
        (hdj₂.st.sub_right (Lay.stSub (by omega_arith))).symm (hdj₂.w.sub_right (Lay.wSub (by decide))) hdj₂.sk
        hdj₂.fit hdj₂.rd
      rw [a₁, b₁, c₁] at g₁
      rw [a₂, b₂, c₂] at g₂
      exact ⟨_, _, _, _, _, g₁, g₂, he₁.sp.trans he₂.sp.symm⟩

omit L hyo in
theorem absorbTail_ct {D : Addr} {n q j : Nat} : CT (MidI c st w sp yo D n q j) absorbTail := by
  obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s4, .s5, .s1]) absorbTail
      h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, b₁, _, _, h₁⟩ ⟨_, _, _, _, _, b₂, _, _, h₂⟩ =>
    ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h₁.s4, h₂.s4]
  · rw [h₁.s5, h₂.s5]
  · rw [h₁.env.s1, h₂.env.s1, b₁, b₂]

theorem absorb_ct {D : Addr} {n q : Nat} (hq : q < 16) : CT (AbsI c st w sp yo D n q) (absorb yo) := by
  refine CT.ite (decide (n = 0)) (fun s ⟨_, _, _, _, _, _, _, hs⟩ => eval_zero hs.s5 hs.data.lt)
    (fun _ => CT.skip) fun hb => ?_
  have h0 : n ≠ 0 := by simpa using hb
  let j₁ := if q = 0 then 0 else min (16 - q) n
  refine CT.seq (J := MidI c st w sp yo D n q j₁) (absorbFill_ct L hyo h0 hq)
    (fun s ⟨V, H, x, h29, h30, h31, hx, hs⟩ => WP.mono (absorbFill_ok (L.v h29 h30 h31) hyo hs h0)
      fun s' ⟨j, hj, hm⟩ => ⟨V, H, x, s.mem, h29, h30, h31, hx, by rw [hj, hx] at hm; exact hm⟩) ?_
  refine CT.seq (J := MidI c st w sp yo D n q (j₁ + 16 * ((n - j₁) / 16))) (absorbWhole_ct L hyo)
    (fun s ⟨V, H, x, m₀, h29, h30, h31, hx, hs⟩ => WP.mono (whole_ok (L.v h29 h30 h31) hyo hs
      (hs.data_eq hyo)) fun s' ⟨j, hj, hm, _⟩ => ⟨V, H, x, m₀, h29, h30, h31, hx, by rw [hj] at hm; exact hm⟩)
    absorbTail_ct

/-- `ghash1 yo .s0 96`, of `T`. -/
theorem ghT_ct : CT (GhIn c st w sp .s0 96 (w + BitVec.ofNat 64 96)) (ghash1 yo .s0 tO) :=
  ghash1_ct L hyo (.inr ⟨rfl, rfl⟩) (L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩))
    (Lay.w_w (.inl (by decide)) (by decide) (by decide))

omit L hyo in
theorem ghIn_T {s : State} (he : EnvC c st w sp s) : GhIn c st w sp .s0 96 (w + BitVec.ofNat 64 96) s := by
  obtain ⟨V, h29, h30, h31, he'⟩ := he
  exact ⟨⟨V, h29, h30, h31, he'⟩, by rw [he'.s0, h31],
    by rw [← h31]; exact covers_left (he'.perm.wC (by decide))⟩

/-- Before `flush yo`: `q` buffered bytes. -/
theorem flush_ct {q : Nat} (hq : q < 16) :
    CT (fun s => EnvC c st w sp s ∧ s.gpr .s6 = BitVec.ofNat 64 q) (flush yo) := by
  refine CT.ite (decide (q = 0)) (fun s ⟨_, h26⟩ => eval_zero h26 (by omega_arith)) (fun _ => CT.skip) fun hb => ?_
  have h0 : q ≠ 0 := by simpa using hb
  refine CT.seq (J := GhIn c st w sp .s0 96 (w + BitVec.ofNat 64 96)) ?_ (fun s ⟨⟨V, h29, h30, h31, he⟩, h26⟩ =>
    WP.mono (flushCopy_ok (L.v h29 h30 h31) hyo (H := blockAt s.mem (V .s2 + BitVec.ofNat 64 240))
      ⟨he, rfl⟩ h26 hq h0) fun s' hm => ghIn_T ⟨V, h29, h30, h31, hm.env⟩) (ghT_ct L hyo)
  obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s6, .s1, .s0])
      (.seq (.block flushPre) copyLoop) h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.taint _ (fun s₁ s₂ ⟨h₁, a₁⟩ ⟨h₂, a₂⟩ => ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a₁, a₂]
  · exact h₁.pin h₂ (by simp)
  · exact h₁.pin h₂ (by simp)

/-- `lens yo`: the lengths are not needed, only `W`. -/
theorem lens_ct : CT (EnvC c st w sp) (lens yo) := by
  refine CT.seq (J := GhIn c st w sp .s0 96 (w + BitVec.ofNat 64 96)) ?_ (fun s ⟨V, h29, h30, h31, he⟩ =>
    WP.mono (lensStore_ok he) fun s' ⟨_, hg, hk⟩ => ghIn_T ⟨V, h29, h30, h31,
      he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide) (by revert r; decide)) hk.sp hk.rd hk.wr⟩) (ghT_ct L hyo)
  obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s0])
      (.block Impl.AesGcm.RISCV64.lensBlock) h).isSome = true := ⟨_, by taint_decide⟩
  exact CT.taint _ (fun s₁ s₂ h₁ h₂ => ⟨h₁.sp.trans h₂.sp.symm, fun r hr => h₁.pin h₂ (by simp at hr; simp [hr])⟩) hc

end

end VG.Proof.AesGcm.RISCV64
