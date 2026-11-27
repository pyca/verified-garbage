module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Crypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTAbsorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Crypt
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTAbsorb
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.StreamFinish
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Impl.Sm4Gcm.RISCV64
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.Sm4Gcm.RISCV64

/-! ### `Sm4Gcm.RISCV64.CTCrypt`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on RISC-V: `crypt` is constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/RISCV64/CTSeal.lean`): the invariants fix the context, the
state, `W`, the stack pointer, the data's address and length, and the length
of the text so far modulo 16; SM4's counter mode is constant time by its own
proof (`CT.sctr`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (mov cryptFill splitCtr xorLoop)
open VG.Proof.AesGcm.RISCV64 (CT Env Lay DataW eval_zero)

/-- Before `crypt`. -/
def CrI (c st w sp : Addr) (D : Addr) (n q : Nat) (s : State) : Prop :=
  ∃ V icb P, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ P % 16 = q ∧ CrIn V sp icb P D n s

/-- Part of the way: `j` bytes done. -/
def CrM (c st w sp : Addr) (D : Addr) (n q j : Nat) (s : State) : Prop :=
  ∃ V icb P m₀, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ P % 16 = q ∧ CrMid V sp icb P D n m₀ j s

/-- Environments that agree on `s0` to `s2` agree in those registers. -/
theorem pinK {V₁ V₂ : Reg → BitVec 64} {sp : Addr} {s₁ s₂ : State} (e₁ : Env V₁ sp s₁) (e₂ : Env V₂ sp s₂)
    (h29 : V₁ .s2 = V₂ .s2) (h30 : V₁ .s1 = V₂ .s1) (h31 : V₁ .s0 = V₂ .s0)
    {r : Reg} (hr : r ∈ [Reg.s2, .s1, .s0]) : s₁.gpr r = s₂.gpr r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [e₁.s2, e₂.s2, h29]
  · rw [e₁.s1, e₂.s1, h30]
  · rw [e₁.s0, e₂.s0, h31]

section
variable {c st w sp : Addr} (L : Lay c st w)
include L

theorem cryptWhole_ct {D : Addr} {n q j : Nat} :
    CT (CrM c st w sp D n q j) cryptWhole := by
  obtain ⟨nb, hnb⟩ : ∃ nb, nb = (n - j) / 16 := ⟨_, rfl⟩
  let J₁ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧
    Env V sp s ∧ DataW (V .s2) (V .s1) (V .s0) s D n ∧ j ≤ n ∧ Big V sp ∧
    (below sp 3248).Disjoint ⟨D, n⟩ ∧ s.gpr .a3 = D + BitVec.ofNat 64 j ∧ s.gpr .a4 = BitVec.ofNat 64 nb
  refine CT.seq (J := J₁) ?_ (fun s ⟨V, icb, P, m₀, h29, h30, h31, hP, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s4, .s5]) (.block splitCtr)
        h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, _, _, _, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.s4, h₂.s4]
    · rw [h₁.s5, h₂.s5]
  · refine WP.mono (splitCtr_ok hs.le hs.data.ok.lt hs.s4 hs.s5) fun s₁ ⟨h6, h7, _, _, hg₁, hk₁⟩ => ?_
    exact ⟨V, h29, h30, h31, hs.env.keep (fun r hr => hg₁ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide)) hk₁.sp hk₁.rd hk₁.wr, hs.data.of_eq hk₁.rd hk₁.wr hk₁.sp, hs.le, hs.big, hs.bd, h6,
      by rw [h7, hnb]⟩
  · refine CT.ite (decide (nb = 0)) (fun s ⟨_, _, _, _, _, hd, _, _, _, _, h7⟩ =>
      eval_zero h7 (by have := hd.ok.lt; omega_arith)) (fun _ => CT.skip) fun hb => ?_
    have h0 : nb ≠ 0 := by simpa using hb
    let J₂ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧
      Env V sp s ∧ DataW (V .s2) (V .s1) (V .s0) s D n ∧ j ≤ n ∧ Big V sp ∧
      (below sp 3248).Disjoint ⟨D, n⟩ ∧
      s.gpr .a0 = V .s2 ∧ s.gpr .a1 = V .s1 + BitVec.ofNat 64 48 ∧
      s.gpr .a2 = D + BitVec.ofNat 64 j ∧ s.gpr .a3 = BitVec.ofNat 64 nb
    refine CT.seq (J := J₂) ?_ (fun s ⟨V, h29, h30, h31, he, hd, hj, hbg, hbd, h6, h7⟩ => ?_) ?_
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s2, .s1, .s0])
          (.block (ctrArgs 48)) h).isSome = true := ⟨_, by taint_decide⟩
      exact CT.taint _ (fun s₁ s₂ ⟨_, a29, a30, a31, e₁, _⟩ ⟨_, b29, b30, b31, e₂, _⟩ =>
        ⟨e₁.sp.trans e₂.sp.symm, fun r hr => pinK e₁ e₂ (a29.trans b29.symm)
          (a30.trans b30.symm) (a31.trans b31.symm) hr⟩) hc
    · refine WP.mono (ctrArgs_ok he) fun s₂ ⟨a3, a4, a5, a6, hg₂, hk₂⟩ => ?_
      exact ⟨V, h29, h30, h31, he.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
        (by revert r; decide) (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr, hd.of_eq hk₂.rd hk₂.wr hk₂.sp, hj, hbg,
        hbd, a3, a4, by rw [a5, h6], by rw [a6, h7]⟩
    · refine CT.sctr fun s₁ s₂ ⟨V₁, a29, a30, a31, he₁, hd₁, hj₁, hb₁, hbd₁, a3, a4, a5, a6⟩
        ⟨V₂, b29, b30, b31, he₂, hd₂, _, hb₂, hbd₂, b3, b4, b5, b6⟩ => ?_
      have hn₁ := hd₁.ok.lt
      have g₁ := ctrWhole_mk (L.v a29 a30 a31) hb₁ he₁ a3 a4 a5 a6 (by omega_arith)
        (hd₁.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith))
        (hbd₁.sub_right (Offset.sub_base _ (by omega_arith)))
      have g₂ := ctrWhole_mk (L.v b29 b30 b31) hb₂ he₂ b3 b4 b5 b6 (by omega_arith)
        (hd₂.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith))
        (hbd₂.sub_right (Offset.sub_base _ (by omega_arith)))
      rw [a29, a30] at g₁
      rw [b29, b30] at g₂
      exact ⟨_, _, _, _, g₁, g₂, he₁.sp.trans he₂.sp.symm⟩

theorem cryptTail_ct {D : Addr} {n q j : Nat} :
    CT (CrM c st w sp D n q j) cryptTail := by
  refine CT.ite (decide (n - j = 0)) (fun s ⟨_, _, _, _, _, _, _, _, hs⟩ =>
    eval_zero hs.s5 (by have := hs.data.ok.lt; omega_arith)) (fun _ => CT.skip) fun _ => ?_
  let J₁ : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧
    Env V sp s ∧ Big V sp ∧ s.gpr .a0 = V .s2 ∧
    s.gpr .a1 = V .s1 + BitVec.ofNat 64 48 ∧ s.gpr .a2 = V .s1 + BitVec.ofNat 64 64 ∧
    s.gpr .a3 = BitVec.ofNat 64 1
  let J₂ : State → Prop := fun s => ∃ V icb P m₀ s₀, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧
    TailKs V sp icb P D n m₀ j s₀ s
  refine CT.seq (J := J₂) (CT.seq (J := J₁) ?_ (fun s ⟨V, icb, P, m₀, h29, h30, h31, hP, hs⟩ => ?_) ?_)
    (fun s ⟨V, icb, P, m₀, h29, h30, h31, hP, hs⟩ =>
      WP.mono (tailKs_ok (L.v h29 h30 h31) hs (hs.ciph (L.v h29 h30 h31))) fun s' h =>
        ⟨V, icb, P, m₀, s, h29, h30, h31, h⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s2, .s1, .s0])
        (.block tailArgs) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, a29, a30, a31, _, h₁⟩ ⟨_, _, _, _, b29, b30, b31, _, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => pinK h₁.env h₂.env
        (a29.trans b29.symm) (a30.trans b30.symm) (a31.trans b31.symm) hr⟩) hc
  · refine WP.mono (tailArgs_ok (L.v h29 h30 h31) hs.env) fun s₂ ⟨_, a3, a4, a5, a6, hg₂, hk₂⟩ => ?_
    exact ⟨V, h29, h30, h31, hs.env.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide))
      hk₂.sp hk₂.rd hk₂.wr, hs.big, a3, a4, a5, a6⟩
  · exact CT.sctr fun s₁ s₂ ⟨V₁, a29, a30, a31, he₁, hb₁, a3, a4, a5, a6⟩
      ⟨V₂, b29, b30, b31, he₂, hb₂, b3, b4, b5, b6⟩ => by
      have g₁ := ctrTail_mk (L.v a29 a30 a31) hb₁ he₁ a3 a4 a5 a6
      have g₂ := ctrTail_mk (L.v b29 b30 b31) hb₂ he₂ b3 b4 b5 b6
      rw [a29, a30] at g₁
      rw [b29, b30] at g₂
      exact ⟨_, _, _, _, g₁, g₂, he₁.sp.trans he₂.sp.symm⟩
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s4, .s5, .s1])
        (.seq (.block [.addi .a0 .s1 64, mov .a1 .s4, mov .a2 .s5]) xorLoop) h).isSome = true :=
      ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, a30, _, h₁⟩ ⟨_, _, _, _, _, _, b30, _, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.s4, h₂.s4]
    · rw [h₁.s5, h₂.s5]
    · rw [h₁.env.s1, h₂.env.s1, a30, b30]

theorem crypt_ct {D : Addr} {n q : Nat} :
    CT (CrI c st w sp D n q) crypt := by
  refine CT.ite (decide (n = 0)) (fun s ⟨_, _, _, _, _, _, _, hs⟩ => eval_zero hs.s5 hs.data.ok.lt)
    (fun _ => CT.skip) fun hb => ?_
  have h0 : n ≠ 0 := by simpa using hb
  let j₁ := if q = 0 then 0 else min (16 - q) n
  refine CT.seq (J := CrM c st w sp D n q j₁) ?_
    (fun s ⟨V, icb, P, h29, h30, h31, hP, hs⟩ => WP.mono (cryptFill_ok hs h0) fun s' ⟨j, hj, hm⟩ =>
      ⟨V, icb, P, s.mem, h29, h30, h31, hP, by subst hj; rw [hP] at hm; exact hm⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s4, .s5, .s6, .s1]) cryptFill
        h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, a30, _, hP₁, h₁⟩ ⟨_, _, _, _, b30, _, hP₂, h₂⟩ =>
      ⟨h₁.env.sp.trans h₂.env.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.s4, h₂.s4]
    · rw [h₁.s5, h₂.s5]
    · rw [h₁.s6, h₂.s6, hP₁, hP₂]
    · rw [h₁.env.s1, h₂.env.s1, a30, b30]
  refine CT.seq (J := CrM c st w sp D n q (j₁ + 16 * ((n - j₁) / 16))) (cryptWhole_ct L)
    (fun s ⟨V, icb, P, m₀, h29, h30, h31, hP, hs⟩ =>
      WP.mono (cryptWhole_ok (L.v h29 h30 h31) hs (hs.ciph (L.v h29 h30 h31))) fun s' ⟨j, hj, hm, _⟩ =>
        ⟨V, icb, P, m₀, h29, h30, h31, hP, by subst hj; exact hm⟩) (cryptTail_ct L)

end

end VG.Proof.Sm4Gcm.RISCV64

end

end

/-!
# SM4-GCM on RISC-V: `tag`, `finTag` and `vg_sm4_gcm_stream_finish` are constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/RISCV64/CTSeal.lean`): the invariants fix the context, the
state, `W`, the stack pointer, the lengths of the additional data (`s10`)
and of the text (`s11`), and the tag's address (`s9`), all held in registers
the environment pins.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (mov lens flush tagOut restore)
open VG.Proof.AesGcm.RISCV64 (CT ct_of CT.taintEq Env Lay EnvC eval_zero lens_ct lens_ok flush_ct flush_ok
  and15 tagOut_ok restore_taint Keeps covers_mem)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- An environment whose registers are apart from the stack below `sp`. -/
def EnvB (c st w sp : Addr) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ Env V sp s ∧ Big V sp

/-- Before `finTag`: also `aad_len` (`A`) and `text_len` (`T`) in `s10` and `s11`. -/
def FTI (c st w sp : Addr) (A T : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s10 = A ∧
    V .s11 = T ∧ Env V sp s ∧ Big V sp

section
variable {c st w sp : Addr} (L : Lay c st w)
include L

theorem tag_ct [VG.Proof.Gcm.RISCV64.GhashLaw] {o : Nat} (ho : o = 0 ∨ o = 112) :
    CT (EnvB c st w sp) (tag o) := by
  refine CT.seq (J := EnvB c st w sp)
    ((lens_ct L (yo := 16) (.inr rfl)).mono fun s ⟨V, a, b, d, he, _⟩ => ⟨V, a, b, d, he⟩)
    (fun s ⟨V, a, b, d, he, hb⟩ => WP.mono (lens_ok (L.v a b d) (.inr rfl) he rfl) fun s' h =>
      ⟨V, a, b, d, h.1, hb⟩) ?_
  let J : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧
    Env V sp s ∧ Big V sp ∧ s.gpr .a0 = V .s2 ∧ s.gpr .a1 = V .s1 ∧
    s.gpr .a2 = V .s0 + BitVec.ofNat 64 o ∧ s.gpr .a3 = BitVec.ofNat 64 1
  refine CT.seq (J := J) ?_ (fun s ⟨V, a, b, d, he, hb⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s2, .s1, .s0])
        (.block (tagArgs o)) h).isSome = true := by rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, a₁, b₁, d₁, h₁, _⟩ ⟨_, a₂, b₂, d₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => pinK h₁ h₂ (a₁.trans a₂.symm)
        (b₁.trans b₂.symm) (d₁.trans d₂.symm) hr⟩) hc
  · refine WP.mono (tagArgs_ok (L.v a b d) (o := o) ho he)
      fun s' ⟨_, a3, a4, a5, a6, hg, hk⟩ => ⟨V, a, b, d, he.keep (fun r hr => hg r (by revert r; decide)
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide))
        hk.sp hk.rd hk.wr, hb, a3, a4, a5, a6⟩
  · exact CT.sctr fun s₁ s₂ ⟨V₁, a₁, b₁, d₁, e₁, x₁, a3, a4, a5, a6⟩
      ⟨V₂, a₂, b₂, d₂, e₂, x₂, b3, b4, b5, b6⟩ => by
      have g₁ := ctrTag_mk (L.v a₁ b₁ d₁) x₁ ho e₁ a3 a4 a5 a6
      have g₂ := ctrTag_mk (L.v a₂ b₂ d₂) x₂ ho e₂ b3 b4 b5 b6
      rw [a₁, b₁, d₁] at g₁
      rw [a₂, b₂, d₂] at g₂
      exact ⟨_, _, _, _, g₁, g₂, e₁.sp.trans e₂.sp.symm⟩

/-- The number of buffered bytes `finTag` pads: of the text if there is any,
else of the additional data. -/
abbrev finQ (A T : BitVec 64) : Nat := if T.toNat = 0 then A.toNat % 16 else T.toNat % 16

theorem finTag_ct [VG.Proof.Gcm.RISCV64.GhashLaw] {o : Nat} (ho : o = 0 ∨ o = 112) {A T : BitVec 64} :
    CT (FTI c st w sp A T) (finTag o) := by
  have hq : finQ A T < 16 := by simp only [finQ]; split <;> exact Nat.mod_lt _ (by decide)
  let J : State → Prop := fun s => FTI c st w sp A T s ∧ s.gpr .s6 = BitVec.ofNat 64 (finQ A T)
  refine CT.seq (J := J) ?_ (fun s ⟨V, a, b, d, f, g, he, hb⟩ => ?_) ?_
  · refine CT.ite (decide (T.toNat = 0)) (fun s ⟨_, _, _, _, _, g, he, _⟩ =>
      eval_zero (by rw [he.ofNat (r := .s11) (by decide), g]) T.isLt) (fun _ => ?_) (fun _ => ?_)
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s10])
          (.block [.logicImm .and .s6 .s10 15]) h).isSome = true := ⟨_, by taint_decide⟩
      refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, f₁, _, h₁, _⟩ ⟨_, _, _, _, f₂, _, h₂, _⟩ =>
        ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
      simp only [List.mem_singleton] at hr; subst hr
      rw [h₁.fr _ (by decide), h₂.fr _ (by decide), f₁, f₂]
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s11])
          (.block [.logicImm .and .s6 .s11 15]) h).isSome = true := ⟨_, by taint_decide⟩
      refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, g₁, h₁, _⟩ ⟨_, _, _, _, _, g₂, h₂, _⟩ =>
        ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
      simp only [List.mem_singleton] at hr; subst hr
      rw [h₁.fr _ (by decide), h₂.fr _ (by decide), g₁, g₂]
  · have h22 := he.fr .s10 (by decide)
    have h23 := he.fr .s11 (by decide)
    refine WP.ite (decide (T.toNat = 0)) (eval_zero (by rw [he.ofNat (r := .s11) (by decide), g]) T.isLt)
      (fun ht => ?_) (fun hf => ?_)
    · have hand := and15 (V .s10)
      have hQ : finQ A T = (V .s10).toNat % 16 := by simp only [finQ, f]; simp at ht; simp [ht]
      have h₃ : WP isa (.block [.logicImm .and .s6 .s10 15]) s fun s₃ =>
          s₃.gpr .s6 = BitVec.ofNat 64 ((V .s10).toNat % 16) ∧
            (∀ r, r ≠ .s6 → s₃.gpr r = s.gpr r) ∧ Keeps s s₃ := by
        crun [Int.reduceNatCast', h22, hand]
        exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
      exact WP.mono h₃ fun s₃ ⟨h26, hg, hk⟩ => ⟨⟨V, a, b, d, f, g, he.keep (fun r hr => hg r
        (by revert r; decide)) hk.sp hk.rd hk.wr, hb⟩, by rw [h26, hQ]⟩
    · have hand := and15 (V .s11)
      have hQ : finQ A T = (V .s11).toNat % 16 := by simp only [finQ, g]; simp at hf; simp [hf]
      have h₃ : WP isa (.block [.logicImm .and .s6 .s11 15]) s fun s₃ =>
          s₃.gpr .s6 = BitVec.ofNat 64 ((V .s11).toNat % 16) ∧
            (∀ r, r ≠ .s6 → s₃.gpr r = s.gpr r) ∧ Keeps s s₃ := by
        crun [Int.reduceNatCast', h23, hand]
        exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
      exact WP.mono h₃ fun s₃ ⟨h26, hg, hk⟩ => ⟨⟨V, a, b, d, f, g, he.keep (fun r hr => hg r
        (by revert r; decide)) hk.sp hk.rd hk.wr, hb⟩, by rw [h26, hQ]⟩
  refine CT.seq (J := FTI c st w sp A T)
    ((flush_ct L (yo := 16) (.inr rfl) hq).mono fun s ⟨⟨V, a, b, d, _, _, he, _⟩, h26⟩ => ⟨⟨V, a, b, d, he⟩, h26⟩)
    (fun s ⟨⟨V, a, b, d, f, g, he, hb⟩, h26⟩ => WP.mono (flush_ok (L.v a b d) (yo := 16) (.inr rfl)
      (x := List.replicate (finQ A T) 0) ⟨he, rfl⟩ (by simp [h26, Nat.mod_eq_of_lt hq])) fun s' fl =>
        ⟨V, a, b, d, f, g, fl.env, hb⟩) ?_
  refine CT.seq (J := EnvB c st w sp) ?_ (fun s ⟨V, a, b, d, f, g, he, hb⟩ => ?_)
    ((tag_ct L ho).mono fun _ h => h)
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s10, .s11])
        (.block [mov .s4 .s10, mov .s6 .s11]) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, f₁, g₁, h₁, _⟩ ⟨_, _, _, _, f₂, g₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), f₁, f₂]
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), g₁, g₂]
  · have h₅ : WP isa (.block [mov .s4 .s10, mov .s6 .s11]) s fun s₅ =>
        (∀ r, r ≠ .s4 → r ≠ .s6 → s₅.gpr r = s.gpr r) ∧ Keeps s s₅ := by
      crun [Int.reduceNatCast', mov]
      exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl⟩⟩
    exact WP.mono h₅ fun s₅ ⟨hg, hk⟩ => ⟨V, a, b, d, he.keep (fun r hr => hg r (by revert r; decide)
      (by revert r; decide)) hk.sp hk.rd hk.wr, hb⟩

end

/-- In `finish`, after the entry: also the tag's address `Tp` in `s9`, which
the state may write. -/
def FinI (c st w sp : Addr) (A T Tp : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s10 = A ∧
    V .s11 = T ∧ V .s9 = Tp ∧ Env V sp s ∧ Big V sp ∧ Covers [⟨Tp, 16⟩] s.wr

theorem finEntry_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) (.block finEntry) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem tagOut_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s9, .s0]) (.block tagOut)
    h).isSome = true := ⟨_, by taint_decide⟩

theorem streamFinish_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : ConstantTime isa streamFinishRISCV64.pre streamFinishRISCV64.pub streamFinish := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, q8, qsp⟩ := hq
  have h₁' : finPre σ₁ := h₁
  have L := finLay h₁'
  have dtw : (⟨σ₁.gpr .a4, 16⟩ : Region).Disjoint ⟨σ₁.gpr .a5, 16⟩ := by
    obtain ⟨-, -, -, -, -, -, -, dtw, -⟩ := h₁'
    exact dtw.sub_right (Region.sub_prefix (by decide))
  let I₀ : State → Prop := fun s => finPre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧ s.gpr .a1 = σ₁.gpr .a1 ∧
    s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧ s.gpr .a5 = σ₁.gpr .a5 ∧
    s.sp = σ₁.sp
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm,
    q8.symm, qsp.symm⟩, ?_⟩
  let FI := FinI (σ₁.gpr .a0) (σ₁.gpr .a1) (σ₁.gpr .a5) σ₁.sp (σ₁.gpr .a2) (σ₁.gpr .a3) (σ₁.gpr .a4)
  refine CT.seq (J := FI) ?_ (fun s ⟨hs, e3, e4, e5, e6, e7, e8, esp⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := finEntry_taint
    exact CT.taintEq (I := I₀) _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8]⟩) hc
  · refine WP.mono (fin1_wp (fin_W hs) (fin_al hs)) fun s₁ h1 => ?_
    have hT : Covers [⟨s.gpr .a4, 16⟩] s₁.wr := by
      rw [h1.en.keeps.wr, hs.2.1]; exact covers_mem (by simp)
    refine ⟨s₁.gpr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h1.s2, e3]
    · rw [h1.s1, e4]
    · rw [h1.s0, e8]
    · rw [h1.s10, e5]
    · rw [h1.s11, e6]
    · rw [h1.s9, e7]
    · rw [← esp]; exact fin_env hs h1
    · rw [← esp]; exact fin_big hs h1.s2 h1.s1 h1.s0
    · rw [← e7]; exact hT
  refine CT.seq (J := FI)
    ((finTag_ct L (o := 0) (.inl rfl)).mono fun s ⟨V, a, b, d, f, g, _, he, hb, _⟩ => ⟨V, a, b, d, f, g, he, hb⟩)
    (fun s ⟨V, a, b, d, f, g, i, he, hb, hT⟩ => WP.mono (Proof.AesGcm.RISCV64.WP.with_rdwr
      (finTag_ok (L.v a b d) hb (o := 0) (.inl rfl)
      (a := List.replicate ((σ₁.gpr .a2).toNat % 16) 0) (ct := List.replicate (σ₁.gpr .a3).toNat 0) he rfl
      (by simp [f]) (by simp [g]))) fun s' ⟨fo, _, wr, _⟩ =>
        ⟨V, a, b, d, f, g, i, fo.env, hb, by rw [wr]; exact hT⟩) ?_
  refine CT.seq (J := fun s => s.gpr .s0 = σ₁.gpr .a5 ∧ s.sp = σ₁.sp) ?_
    (fun s ⟨V, a, b, d, f, g, i, he, hb, hT⟩ => WP.mono (tagOut_ok he (by rw [i]; exact hT)
      (by rw [i, d]; exact dtw)) fun s' ⟨_, _, hg, hk⟩ =>
        ⟨by rw [hg _ (by decide), he.s0, d], by rw [hk.sp, he.sp]⟩) ?_
  · obtain ⟨_, hc⟩ := tagOut_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, d₁, _, _, i₁, h₁, _⟩ ⟨_, _, _, d₂, _, _, i₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
    · rw [h₁.s0, h₂.s0, d₁, d₂]
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .a5) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.Sm4Gcm.RISCV64
