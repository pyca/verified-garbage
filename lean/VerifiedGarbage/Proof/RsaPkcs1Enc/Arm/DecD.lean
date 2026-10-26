module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecPriv
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecMem
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Bignum.Arm.CopyRegion
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rc2.Memory
import Mathlib.Tactic.Conv

/-!
# RSAES-PKCS1-v1_5 decryption on ARMv7: `D = I2OSP(d, k)`

From here on the call's result stays in `out` and in its slot (`Base`), as
long as memory changes only in `scratch`, the frame's other words and the
stack below (`Base.frame`). `D`, `k` bytes in `scratch`: zeros
(`dZero_wp`, `zero_wp`), then `d` copied to its end (`dCopy_wp`,
`copy_wp`): `d` after `k - d_len` zeros (`Dfull`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Dec

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Decrypt VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp op2_imm op2_reg dpVal)

variable {P : EP}

/-- The call's result, in `out` and in its slot. -/
def Base (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ ∃ rc, Priv P σ s.mem rc ∧ s.mem.readW (P.lay.fr oR) 32 = rc

/-- What the frame's slots and the stack below may change. -/
def Safe (P : EP) (r : Region) : Prop := P.OUT.Disjoint r ∧ Region.Disjoint ⟨P.lay.fr oR, 4⟩ r

theorem writtenOutcome_congr {m m' : Mem} {a : Addr} {K : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (hb : Spec.Rsa.bytesAt m' a K = Spec.Rsa.bytesAt m a K) (h : Spec.Rsa.writtenOutcome m a K r o) :
    Spec.Rsa.writtenOutcome m' a K r o := by
  cases o with
  | ok y => exact ⟨h.1, hb.trans h.2⟩
  | invalid => exact ⟨h.1, hb.trans h.2⟩
  | fault => exact ⟨h.1, hb.trans h.2⟩

theorem Base.frame {σ s t : State} (h : Base P σ s) (st : P.lay.St σ t) {rs : List Region}
    (hf : Frame rs s.mem t.mem) (hs : ∀ r ∈ rs, Safe P r) : Base P σ t := by
  obtain ⟨hS, rc, pr, sl⟩ := h
  have hK := hS.1.k1024
  refine ⟨⟨hS.1, st⟩, rc, writtenOutcome_congr (bytesAt_frame hf (fun r hr => (hs r hr).1) (by omega_arith)) pr, ?_⟩
  rw [hf.readW (r := ⟨P.lay.fr oR, 4⟩) (Region.contains_self _ _) (fun r hr => (hs r hr).2) (by decide)]
  exact sl

/-! ## Safe regions -/

namespace In

variable {σ : State} (h : In P σ)
include h

theorem safe_sc {o n : Nat} (hn : o + n ≤ 8448) : Safe P (sc P o n) :=
  ⟨(h.sc_out hn).symm, h.fr_sc (by simp only [oR, frameBytes]; decide) hn⟩

theorem safe_low : Safe P P.lay.LOW :=
  ⟨(h.ok.low_buf (R := P.OUT) (.inr (by simp))).symm, Lay.fr_low (by simp only [oR]; decide)⟩

theorem safe_fr {d n : Nat} (hd : d + n ≤ frameBytes) (ho : d + n ≤ oR ∨ oR + 4 ≤ d) :
    Safe P ⟨P.lay.fr d, n⟩ :=
  ⟨(h.ok.stk_fr (R := P.OUT) (.inr (by simp)) (by show d + n ≤ frameBytes + 56; omega_arith)).symm,
    Lay.fr_sep (by omega_arith) (by simp only [oR]; decide) (by simp only [frameBytes] at hd; omega_arith)⟩

end In

theorem add_sub_ofNat (x : BitVec 32) {a b : Nat} (h : b ≤ a) :
    x + BitVec.ofNat 32 a - BitVec.ofNat 32 b = x + BitVec.ofNat 32 (a - b) := by
  conv_lhs => rw [show a = (a - b) + b by omega_arith, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- `D = I2OSP(d, k)`: `d` after zeros. -/
abbrev Dfull (P : EP) (σ : State) : List Byte := List.replicate (P.K - P.dl) 0 ++ dB P σ

/-- Before the zeros of `D`. -/
def D1 (P : EP) (σ s : State) : Prop :=
  Base P σ s ∧ s.gpr .r0 = P.scr + BitVec.ofNat 32 sD ∧ s.gpr .lr = BitVec.ofNat 32 P.K ∧ s.gpr .r2 = 0

/-- `D` zeros. -/
def D2 (P : EP) (σ s : State) : Prop := Base P σ s ∧ Spec.Rsa.bytesAt s.mem (sc P sD P.K).base P.K = List.replicate P.K 0

/-- Before the copy of `d`. -/
def D3 (P : EP) (σ s : State) : Prop :=
  D2 P σ s ∧ s.gpr .r0 = P.scr + BitVec.ofNat 32 (sD + (P.K - P.dl)) ∧ s.gpr .r1 = P.d ∧
    s.gpr .lr = BitVec.ofNat 32 P.dl

/-- `D` built. -/
def D4 (P : EP) (σ s : State) : Prop := Base P σ s ∧ Spec.Rsa.bytesAt s.mem (sc P sD P.K).base P.K = Dfull P σ

theorem dZero_wp {σ s : State} (h : R2 P σ s) : WP isa (.block dZero) s (D1 P σ) := by
  obtain ⟨hs, pr⟩ := h
  have hK := hs.1.k1024
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_strFr (d := oR) (by show oR + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u1.gpr, hs.2.sp, BitVec.add_zero]) fun t2 s2 m2 => ?_
  refine s2.wp_arg (j := 21) (by simp) (by dsimp only; decide) fun t3 s3 u3 => ?_
  refine wp_dp (op2_imm (by decide)) fun t4 u4 => ?_
  have s4 : P.lay.St σ t4 := s3.of_rest (u4.rest (ws := [.r0]) (by simp)) u4.mem
  refine s4.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t5 s5 u5 => ?_
  refine wp_mov (op2_imm (by decide)) fun t6 u6 => WP.block_nil ?_
  have s6 : P.lay.St σ t6 := s5.of_rest (u6.rest (ws := [.r2]) (by simp)) u6.mem
  have mm : t6.mem = t1.mem.writeW (P.lay.fr oR) (t1.gpr .r0) := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, m2.mem]
  refine ⟨⟨⟨hs.1, s6⟩, s.gpr .r0, ?_, ?_⟩, ?_, ?_, u6.gpr⟩
  · rw [mm, u1.mem]
    refine writtenOutcome_congr (bytesAt_frame
      ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) (fun r hr => ?_)
      (by omega_arith)) pr
    simp only [List.mem_singleton] at hr; subst hr
    exact (hs.1.ok.stk_fr (R := P.OUT) (.inr (by simp)) (by simp only [oR, frameBytes]; decide)).symm
  · rw [mm, Mem.readW_writeW_self32, u1.other _ (by decide)]
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, dpVal, u3.gpr]; rfl
  · rw [u6.other _ (by decide), u5.gpr]; rfl

theorem zero_wp {σ s : State} (h : D1 P σ s) : WP isa Impl.Bignum.Arm.maskBytes s (D2 P σ) := by
  obtain ⟨hb, r0, lr, r2⟩ := h
  have hs := hb.1
  have hK := hs.1.k1024
  have hsD : State.addr (P.scr + BitVec.ofNat 32 sD) = State.addr P.scr + BitVec.ofNat 64 sD :=
    hs.1.scrA (by decide)
  refine WP.mono (Bignum.Arm.maskBuffer_ok s (dst := P.scr + BitVec.ofNat 32 sD) (n := P.K)
    (by have := hs.1.k64; omega_arith) (by omega_arith) (hs.1.fit_sc (by simp only [sD]; omega_arith) (by decide))
    (by rw [hsD]; exact St.sc_w hs (by simp only [sD]; omega_arith)) r0 lr) fun t ⟨hz, fr, rst⟩ => ?_
  rw [hsD] at hz fr
  have hsub : Region.Sub (sc P sD P.K) P.SCR := hs.1.sc_sub (by simp only [sD]; omega_arith)
  have st : P.lay.St σ t := hs.2.write fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.SCR, by simp, hsub⟩) rst.rd rst.wr rst.sp
  refine ⟨hb.frame st fr fun r hr => ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.safe_sc (by simp only [sD]; omega_arith)
  · rw [hz, r2]
    apply List.ext_getElem (by simp [bytesAt_length])
    intro i h₁ h₂
    simp

theorem dCopy_wp {σ s : State} (h : D2 P σ s) : WP isa (.block dCopy) s (D3 P σ) := by
  have hs := h.1.1
  have hdl := hs.1.dlK
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_arg (j := 21) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  have s3 : P.lay.St σ t3 := s2.of_rest (u3.rest (ws := [.r0]) (by simp)) u3.mem
  refine s3.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t4 s4 u4 => ?_
  refine wp_dp (op2_reg _ _) fun t5 u5 => ?_
  have s5 : P.lay.St σ t5 := s4.of_rest (u5.rest (ws := [.r0]) (by simp)) u5.mem
  refine s5.wp_arg (j := 8) (by simp) (by dsimp only; decide) fun t6 s6 u6 => ?_
  refine wp_dp (op2_reg _ _) fun t7 u7 => ?_
  have s7 : P.lay.St σ t7 := s6.of_rest (u7.rest (ws := [.r0]) (by simp)) u7.mem
  refine s7.wp_arg (j := 7) (by simp) (by dsimp only; decide) fun t8 s8 u8 => WP.block_nil ?_
  have mm : t8.mem = s.mem := by rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨⟨⟨⟨hs.1, s8⟩, ?_⟩, by rw [mm]; exact h.2⟩, ?_, ?_, ?_⟩
  · obtain ⟨rc, pr, sl⟩ := h.1.2
    exact ⟨rc, by rw [Priv, mm]; exact pr, by rw [mm]; exact sl⟩
  · rw [u8.other _ (by decide), u7.gpr, dpVal, u6.other _ (by decide), u5.gpr, dpVal, u4.other _ (by decide),
      u3.gpr, dpVal, u2.gpr, u6.gpr, u4.gpr]
    change P.scr + BitVec.ofNat 32 sD + BitVec.ofNat 32 P.K - BitVec.ofNat 32 P.dl = _
    rw [add_sub_ofNat _ hdl, Offset.add_ofNat_add_ofNat]
  · rw [u8.gpr]; rfl
  · rw [u8.other _ (by decide), u7.other _ (by decide), u6.gpr]; rfl

theorem copy_wp {σ s : State} (h : D3 P σ s) : WP isa Impl.Bignum.Arm.copyBytes s (D4 P σ) := by
  obtain ⟨⟨hb, hz⟩, r0, r1, lr⟩ := h
  have hs := hb.1
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have hdl := hs.1.dlK
  have hfd := ok.fits P.D (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hfd
  have hdst : State.addr (P.scr + BitVec.ofNat 32 (sD + (P.K - P.dl))) =
      State.addr P.scr + BitVec.ofNat 64 (sD + (P.K - P.dl)) := hs.1.scrA (by simp only [sD]; omega_arith)
  have ctx := Bignum.Arm.copyCtx_of_regions s P.d (P.scr + BitVec.ofNat 32 (sD + (P.K - P.dl))) (n := P.dl)
    (by omega_arith) hfd (hs.1.fit_sc (by simp only [sD]; omega_arith) (by simp only [sD]; omega_arith))
    ⟨P.D, List.mem_append_left _ (by rw [hs.2.rd, ok.rd]; simp), Region.contains_self _ _⟩
    (by rw [hdst]; exact St.sc_w hs (by simp only [sD]; omega_arith))
    (by rw [hdst]; exact (hs.1.sc_ro (by simp only [sD]; omega_arith) (R := P.D) (by simp)).symm)
  refine WP.mono (Bignum.Arm.copyBytes_ok s ctx (by have := hs.1.dl1; omega_arith) r1 r0 lr) fun t ht => ?_
  have fr := ht.frame (hs.1.fit_sc (by simp only [sD]; omega_arith) (by simp only [sD]; omega_arith))
  rw [hdst] at fr
  have hsub : Region.Sub (sc P (sD + (P.K - P.dl)) P.dl) P.SCR := hs.1.sc_sub (by simp only [sD]; omega_arith)
  have st : P.lay.St σ t := hs.2.write fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.SCR, by simp, hsub⟩) ht.rest.rd ht.rest.wr ht.rest.sp
  refine ⟨hb.frame st fr fun r hr => ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.safe_sc (by simp only [sD]; omega_arith)
  · have hl : (Dfull P σ).length = P.K := by simp [bytesAt_length]; omega_arith
    rw [show P.K = (Dfull P σ).length from hl.symm]
    refine bytesAt_eq fun i hi => ?_
    rw [hl] at hi
    rcases (by omega_arith : i < P.K - P.dl ∨ P.K - P.dl ≤ i) with hi' | hi'
    · have e := ht.outside (State.addr P.scr + BitVec.ofNat 64 (sD + i)) fun j hj he => by
        rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, hs.1.scrA (by simp only [sD]; omega_arith)] at he
        exact Offset.add_ofNat_ne _ (by simp only [sD]; omega_arith) (by simp only [sD]; omega_arith) (by omega_arith) he
      have := congrArg (fun l => l.getD i 0) hz
      simp only at this
      rw [bytesAt_getD (by omega_arith), Offset.add_ofNat_add_ofNat] at this
      rw [Offset.add_ofNat_add_ofNat, e, this, getD_append_left _ _ _ (by simp; omega_arith)]
      simp [List.getD_eq_getElem?_getD, hi', show i < P.K by omega_arith]
    · obtain ⟨j, rfl⟩ : ∃ j, i = P.K - P.dl + j := ⟨i - (P.K - P.dl), by omega_arith⟩
      have hj : j < P.dl := by omega_arith
      have e1 := ht.copied j hj
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, hs.1.scrA (by simp only [sD]; omega_arith)] at e1
      rw [Offset.add_ofNat_add_ofNat, show sD + (P.K - P.dl + j) = sD + (P.K - P.dl) + j by omega_arith, e1,
        getD_append_right _ _ _ (by simp), List.length_replicate, Nat.add_sub_cancel_left,
        addr_add (by omega_arith), bytesAt_getD hj]
      have := congrArg (fun l => l.getD j 0) (hs.2.ro (R := P.D) (by simp))
      simp only at this
      rw [bytesAt_getD hj, bytesAt_getD hj] at this
      exact this

end VG.Proof.RsaPkcs1Enc.Arm.Dec
