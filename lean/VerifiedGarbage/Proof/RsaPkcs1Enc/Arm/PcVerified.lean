module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.PcBuild
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Bignum.Arm.CopyRegion
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
public import VerifiedGarbage.Proof.Rsa.Contract
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.PcTaint
import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.CopyBytesCT
public import VerifiedGarbage.Proof.Framework.Contract

/-! ### `RsaPkcs1Enc.Arm.PcBody`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.Arm.PcCall`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.Arm.PcPieces`, which only this module used -/

section

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on ARMv7: `EM`, correct

The stages up to the call (`G1` … `G6`) and the correctness of the pieces
between them; their constant time is in `PcPiecesCT.lean`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Pc

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Precomputed VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp wp_ldrb wp_strb wp_subs wp_cmp op2_imm op2_reg op2_lsr dpVal)

variable {P : EP}

/-- After `start`. -/
def G1 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 oEM ∧ s.gpr .r1 = P.ps ∧ s.gpr .lr = BitVec.ofNat 32 P.pl

/-- `PS` with `k` of its bytes left: `EM`'s first `2 + (pl - k)` bytes. -/
def PsI (P : EP) (k : Nat) (σ s : State) : Prop :=
  S P σ s ∧ k ≤ P.pl ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 (oEM + (2 + (P.pl - k))) ∧
    s.gpr .r1 = P.ps + BitVec.ofNat 32 (P.pl - k) ∧ s.gpr .lr = BitVec.ofNat 32 k ∧
    s.gpr .r3 = zf (Spec.Rsa.bytesAt σ.mem (State.addr P.ps) (P.pl - k)) ∧ EMok P σ s (2 + (P.pl - k))

/-- After the separator. -/
def G4 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 (oEM + (3 + P.pl)) ∧ s.gpr .r3 = zf (psB P σ) ∧
    EMok P σ s (3 + P.pl)

/-- The zero test in its slot. -/
abbrev Zs (P : EP) (σ s : State) : Prop := s.mem.readW (P.lay.fr oZ) 32 = zf (psB P σ)

/-- Before `M`. -/
def G5 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 (oEM + (3 + P.pl)) ∧ s.gpr .r1 = P.msg ∧
    s.gpr .lr = BitVec.ofNat 32 P.ml ∧ Zs P σ s ∧ EMok P σ s (3 + P.pl)

/-- `EM` written. -/
def G6 (P : EP) (σ s : State) : Prop := S P σ s ∧ Zs P σ s ∧ EMok P σ s P.K

theorem start_wp {σ s : State} (hs : S P σ s) : WP isa (.block start) s (G1 P σ) := by
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  refine wp_dp (op2_imm (by decide)) fun t2 u2 => ?_
  obtain h2 : P.lay.St σ t2 :=
    (hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem).of_rest (u2.rest (ws := [.r0]) (by simp)) u2.mem
  refine h2.wp_arg (j := 8) (by simp) (by dsimp only; decide) fun t3 s3 u3 => ?_
  refine s3.wp_arg (j := 9) (by simp) (by dsimp only; decide) fun t4 s4 u4 => WP.block_nil ⟨⟨hs.1, s4⟩, ?_, ?_, ?_⟩
  · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, dpVal, u1.gpr, hs.2.sp, BitVec.add_zero]
  · rw [u4.other _ (by decide), u3.gpr]; rfl
  · rw [u4.gpr]; rfl

theorem head_wp {σ s : State} (h : G1 P σ s) : WP isa (.block head) s (PsI P P.pl σ) := by
  obtain ⟨hs, r0, r1, lr⟩ := h
  have hk := hs.1.k64
  refine wp_mov (op2_imm (by decide)) fun t1 u1 => ?_
  obtain s1 : S P σ t1 := ⟨hs.1, hs.2.of_rest (u1.rest (ws := [.r2]) (by simp)) u1.mem⟩
  refine wp_strbEM s1 (off := 0) (n := 0) (by decide) (by omega_arith)
    (by rw [u1.other _ (by decide), r0]; simp) fun t2 s2 g2 m2 => ?_
  refine wp_mov (op2_imm (by decide)) fun t3 u3 => ?_
  obtain s3 : S P σ t3 := ⟨hs.1, s2.2.of_rest (u3.rest (ws := [.r2]) (by simp)) u3.mem⟩
  refine wp_strbEM s3 (off := 1) (n := 1) (by decide) (by omega_arith)
    (by rw [u3.other _ (by decide), g2, u1.other _ (by decide), r0, Offset.add_ofNat_add_ofNat])
    fun t4 s4 g4 m4 => ?_
  refine wp_dp (op2_imm (by decide)) fun t5 u5 => ?_
  refine wp_mov (op2_imm (by decide)) fun t6 u6 => WP.block_nil ⟨⟨hs.1, ?_⟩, Nat.le_refl _, ?_, ?_, ?_, ?_, ?_⟩
  · exact (s4.2.of_rest (u5.rest (ws := [.r0]) (by simp)) u5.mem).of_rest (u6.rest (ws := [.r3]) (by simp)) u6.mem
  · rw [u6.other _ (by decide), u5.gpr, dpVal, g4, u3.other _ (by decide), g2, u1.other _ (by decide), r0,
      Nat.sub_self]
    exact Offset.add_ofNat_add_ofNat _ _ 2
  · rw [u6.other _ (by decide), u5.other _ (by decide), g4, u3.other _ (by decide), g2, u1.other _ (by decide),
      r1, Nat.sub_self]; simp
  · rw [u6.other _ (by decide), u5.other _ (by decide), g4, u3.other _ (by decide), g2, u1.other _ (by decide), lr]
  · rw [u6.gpr, Nat.sub_self]; rfl
  · rw [Nat.sub_self]
    obtain e2 := EMok.store (EMok.zero (P := P) (σ := σ) (s := t1)) (by decide) (m := t2.mem)
      (by rw [m2, u1.gpr]; rfl)
    obtain e4 := EMok.store (n := 1) (s := t3) (fun i hi => by rw [u3.mem]; exact e2 i hi) (by decide)
      (m := t4.mem) (by rw [m4, u3.gpr]; rfl)
    intro i hi
    rw [u6.mem, u5.mem]
    exact e4 i hi

/-- One byte of `PS`, `k + 1` of them left. -/
theorem psBody_wp {σ s : State} {k : Nat} (h : PsI P (k + 1) σ s) :
    WP isa (.block psBody) s fun t =>
      isa.eval .ne t = some (decide (0 < k)) ∧ (k = 0 → PsI P 0 σ t) ∧ (0 < k → PsI P k σ t) := by
  obtain ⟨hs, hk, r0, r1, lr, r3, em⟩ := h
  have hK := hs.1.k1024
  have hpl := hs.1.em_len
  obtain hfp := hs.1.ok.fits P.PS (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hfp
  -- The byte of `PS`.
  obtain hpsA : State.addr (P.ps + BitVec.ofNat 32 (P.pl - (k + 1))) = State.addr P.ps +
      BitVec.ofNat 64 (P.pl - (k + 1)) := addr_add (by omega_arith)
  obtain hbyte : s.mem (State.addr P.ps + BitVec.ofNat 64 (P.pl - (k + 1))) =
      σ.mem (State.addr P.ps + BitVec.ofNat 64 (P.pl - (k + 1))) := by
    have := congrArg (fun l => l.getD (P.pl - (k + 1)) 0) (hs.2.ro (R := P.PS) (by simp))
    simp only at this
    rwa [bytesAt_getD (by omega_arith), bytesAt_getD (by omega_arith)] at this
  refine wp_ldrb (by decide) (a := State.addr P.ps + BitVec.ofNat 64 (P.pl - (k + 1)))
    (by rw [r1, BitVec.add_zero, hpsA])
    ⟨P.PS, List.mem_append_left _ (by rw [hs.2.rd, hs.2.ok.rd]; simp),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩ fun t1 u1 => ?_
  obtain s1 : S P σ t1 := ⟨hs.1, hs.2.of_rest (u1.rest (ws := [.r2]) (by simp)) u1.mem⟩
  refine wp_strbEM s1 (off := 0) (n := 2 + (P.pl - (k + 1))) (by decide) (by omega_arith)
    (by rw [u1.other _ (by decide), r0, BitVec.add_zero]) fun t2 s2 g2 m2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  refine wp_dp (op2_lsr (by decide)) fun t4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun t5 u5 => ?_
  refine wp_dp (op2_imm (by decide)) fun t6 u6 => ?_
  refine wp_subs (op2_imm (by decide)) fun t7 u7 z7 => WP.block_nil ?_
  obtain s7 : S P σ t7 := ⟨hs.1, ((((s2.2.of_rest (u3.rest (ws := [.r2]) (by simp)) u3.mem).of_rest
    (u4.rest (ws := [.r3]) (by simp)) u4.mem).of_rest (u5.rest (ws := [.r0]) (by simp)) u5.mem).of_rest
    (u6.rest (ws := [.r1]) (by simp)) u6.mem).of_rest (u7.rest (ws := [.lr]) (by simp)) u7.mem⟩
  obtain lr7 : t7.gpr .lr = BitVec.ofNat 32 k := by
    rw [u7.gpr, u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      g2, u1.other _ (by decide), lr]
    exact sub_one_ofNat (by omega_arith)
  obtain inv : PsI P k σ t7 := by
    refine ⟨s7, by omega_arith, ?_, ?_, lr7, ?_, ?_⟩
    · rw [u7.other _ (by decide), u6.other _ (by decide), u5.gpr, dpVal, u4.other _ (by decide),
        u3.other _ (by decide), g2, u1.other _ (by decide), r0, Offset.add_ofNat_add_one]
      congr 2; omega_arith
    · rw [u7.other _ (by decide), u6.gpr, dpVal, u5.other _ (by decide), u4.other _ (by decide),
        u3.other _ (by decide), g2, u1.other _ (by decide), r1, Offset.add_ofNat_add_one]
      congr 2; omega_arith
    · rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.gpr, dpVal,
        u3.other _ (by decide), g2, u1.other _ (by decide), r3, u3.gpr, dpVal, g2, u1.gpr, hbyte,
        show P.pl - k = P.pl - (k + 1) + 1 by omega_arith, bytesAt_succ, zf_snoc]
    · rw [show 2 + (P.pl - k) = 2 + (P.pl - (k + 1)) + 1 by omega_arith]
      obtain e := EMok.store em (by omega_arith) (m := t2.mem) (by
        rw [m2, u1.gpr, u1.mem, setWidth_byte, hbyte, show 2 + (P.pl - (k + 1)) = 2 + (P.pl - (k + 1)) from rfl,
          enc_getD_ps P σ (by omega_arith)])
      intro i hi
      rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem]
      exact e i hi
  refine ⟨?_, fun h0 => h0 ▸ inv, fun _ => inv⟩
  rw [Proof.X25519.Arm.eval_ne, z7, u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
    u3.other _ (by decide), g2, u1.other _ (by decide), lr, ne_counter (by omega_arith)]

theorem sep_wp {σ s : State} (h : PsI P 0 σ s) : WP isa (.block sep) s (G4 P σ) := by
  obtain ⟨hs, -, r0, -, -, r3, em⟩ := h
  have hpl := hs.1.em_len
  have hK := hs.1.k1024
  rw [Nat.sub_zero] at r0 r3 em
  refine wp_mov (op2_imm (by decide)) fun t1 u1 => ?_
  obtain s1 : S P σ t1 := ⟨hs.1, hs.2.of_rest (u1.rest (ws := [.r2]) (by simp)) u1.mem⟩
  refine wp_strbEM s1 (off := 0) (n := 2 + P.pl) (by decide) (by omega_arith)
    (by rw [u1.other _ (by decide), r0, BitVec.add_zero]) fun t2 s2 g2 m2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => WP.block_nil ⟨⟨hs.1, s2.2.of_rest (u3.rest (ws := [.r0])
    (by simp)) u3.mem⟩, ?_, ?_, ?_⟩
  · rw [u3.gpr, dpVal, g2, u1.other _ (by decide), r0, Offset.add_ofNat_add_one]
    congr 2; omega_arith
  · rw [u3.other _ (by decide), g2, u1.other _ (by decide), r3]
  · have e := EMok.store em (by omega_arith) (m := t2.mem) (by rw [m2, u1.gpr, u1.mem, enc_getD_sep]; rfl)
    intro i hi
    rw [u3.mem]
    exact e i (by omega_arith)

theorem msgArgs_wp {σ s : State} (h : G4 P σ s) : WP isa (.block msgArgs) s (G5 P σ) := by
  obtain ⟨hs, r0, r3, em⟩ := h
  have hK := hs.1.k1024
  have hpl := hs.1.em_len
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  obtain s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_strFr (d := oZ) (by show oZ + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u1.gpr, hs.2.sp, BitVec.add_zero]) fun t2 s2 m2 => ?_
  refine s2.wp_arg (j := 6) (by simp) (by dsimp only; decide) fun t3 s3 u3 => ?_
  refine s3.wp_arg (j := 7) (by simp) (by dsimp only; decide) fun t4 s4 u4 => WP.block_nil
    ⟨⟨hs.1, s4⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u4.other _ (by decide), u3.other _ (by decide), m2.gpr, u1.other _ (by decide), r0]
  · rw [u4.other _ (by decide), u3.gpr]; rfl
  · rw [u4.gpr]; rfl
  · rw [Zs, u4.mem, u3.mem, m2.mem, Mem.readW_writeW_self32, u1.other _ (by decide), r3]
  · refine EMok.frame em (rs := [⟨P.lay.fr oZ, 4⟩]) ?_ fun i hi r hr => ?_
    · rw [u4.mem, u3.mem, m2.mem, u1.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Lay.fr_sep (by simp only [oEM, oZ]; omega_arith) (by simp only [oEM]; omega_arith) (by simp only [oZ]; omega_arith)

theorem cmp_wp {σ s : State} (h : G5 P σ s) :
    WP isa (.block [.cmp .lr (.imm 0)]) s fun t => G5 P σ t ∧ t.z = decide (P.ml = 0) := by
  obtain ⟨hs, r0, r1, lr, zs, em⟩ := h
  have hK := hs.1.k1024
  have hml := hs.1.mlK
  refine wp_cmp (op2_imm (by decide)) fun t1 u1 z1 => WP.block_nil ⟨⟨⟨hs.1, hs.2.of_rest (u1.rest []) u1.mem⟩,
    by rw [u1.gpr, r0], by rw [u1.gpr, r1], by rw [u1.gpr, lr], by rw [Zs, u1.mem]; exact zs,
    EMok.frame em (Frame.refl [] _ |>.trans (by rw [u1.mem]; exact Frame.refl _ _)) (fun _ _ _ h => absurd h List.not_mem_nil)⟩, ?_⟩
  obtain e : BitVec.ofNat 32 P.ml - 0 = BitVec.ofNat 32 P.ml := by simp
  rw [z1, lr, e, Proof.X25519.Arm.ofNat_beq_zero (by omega_arith)]

theorem skip_g6 {σ s : State} (h : G5 P σ s) (h0 : P.ml = 0) : G6 P σ s := by
  obtain ⟨hs, -, -, -, zs, em⟩ := h
  exact ⟨hs, zs, em.mono (by have := hs.1.em_len; omega_arith)⟩

theorem copy_wp {σ s : State} (h : G5 P σ s) (h0 : P.ml ≠ 0) : WP isa Impl.Bignum.Arm.copyBytes s (G6 P σ) := by
  obtain ⟨hs, r0, r1, lr, zs, em⟩ := h
  have hK := hs.1.k1024
  have hpl := hs.1.em_len
  obtain hfm := hs.1.ok.fits P.MSG (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hfm
  have hfit := hs.2.ok.fit
  have hB : P.lay.B = P.B := rfl
  obtain hdst : State.addr (P.B + BitVec.ofNat 32 (oEM + (3 + P.pl))) = P.lay.fr (oEM + (3 + P.pl)) :=
    hs.2.ok.addrB (by show _ < frameBytes + 56 + 40; simp only [oEM, frameBytes]; omega_arith)
  obtain hsep : Region.Disjoint ⟨State.addr P.msg, P.ml⟩ ⟨State.addr (P.B + BitVec.ofNat 32 (oEM + (3 + P.pl))), P.ml⟩ := by
    rw [hdst]
    refine ((hs.2.ok.stk P.MSG (by simp)).sub_left (Lay.sub_stk ?_)).symm
    show oEM + (3 + P.pl) + P.ml ≤ frameBytes + 56; simp only [oEM, frameBytes]; omega_arith
  have hb : P.B.toNat + frameBytes + 56 + 40 ≤ 2 ^ 32 := hfit
  obtain hoff : oEM + (3 + P.pl) < 2 ^ 32 := by simp only [oEM]; omega_arith
  obtain hlt : P.B.toNat + (BitVec.ofNat 32 (oEM + (3 + P.pl))).toNat < 2 ^ 32 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff]; simp only [oEM, frameBytes] at hb ⊢; omega_arith
  obtain hdn : (P.B + BitVec.ofNat 32 (oEM + (3 + P.pl))).toNat = P.B.toNat + (oEM + (3 + P.pl)) := by
    rw [Proof.X25519.Arm.toNat_add_lt hlt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff]
  obtain ctx := Bignum.Arm.copyCtx_of_regions s P.msg (P.B + BitVec.ofNat 32 (oEM + (3 + P.pl))) (n := P.ml)
    (by omega_arith) hfm (by rw [hdn]; simp only [oEM, frameBytes] at hb ⊢; omega_arith)
    ⟨P.MSG, List.mem_append_left _ (by rw [hs.2.rd, hs.2.ok.rd]; simp), Region.contains_self _ _⟩
    (by rw [hdst]; exact hs.2.inFr (by show oEM + (3 + P.pl) + P.ml ≤ frameBytes; simp only [oEM, frameBytes]; omega_arith))
    hsep
  refine WP.mono (Bignum.Arm.copyBytes_ok s ctx (Nat.pos_of_ne_zero h0) r1 r0 lr) fun t ht => ?_
  obtain hdj : ∀ j < P.ml, State.addr (P.B + BitVec.ofNat 32 (oEM + (3 + P.pl)) + BitVec.ofNat 32 j) =
      P.lay.fr (oEM + (3 + P.pl) + j) := fun j hj => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact hs.2.ok.addrB (by show _ < frameBytes + 56 + 40; simp only [oEM, frameBytes]; omega_arith)
  obtain hF : Frame [⟨P.lay.fr (oEM + (3 + P.pl)), P.ml⟩] s.mem t.mem := fun x hx => by
    refine ht.outside x fun j hj e => hx _ (List.mem_singleton_self _) ?_
    rw [e, hdj j hj]
    exact Offset.contains _ (by omega_arith) (by omega_arith) (by simp only [oEM]; omega_arith)
  obtain st : P.lay.St σ t := hs.2.frameW (by show oEM + (3 + P.pl) + P.ml ≤ frameBytes; simp only [oEM, frameBytes]; omega_arith)
    hF ht.rest.rd ht.rest.wr ht.rest.sp
  refine ⟨⟨hs.1, st⟩, ?_, fun i hi => ?_⟩
  · rw [Zs, hF.readW (r := ⟨P.lay.fr oZ, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.fr_sep (by simp only [oEM, oZ]; omega_arith) (by simp only [oZ]; omega_arith) (by simp only [oEM]; omega_arith))
      (by decide)]
    exact zs
  · rcases (by omega_arith : i < 3 + P.pl ∨ 3 + P.pl ≤ i) with hi' | hi'
    · rw [hF.byte1 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Lay.fr_sep (by omega_arith) (by simp only [oEM]; omega_arith) (by simp only [oEM]; omega_arith))]
      exact em i hi'
    · obtain ⟨j, rfl⟩ : ∃ j, i = 3 + P.pl + j := ⟨i - (3 + P.pl), by omega_arith⟩
      obtain hj : j < P.ml := by omega_arith
      rw [show oEM + (3 + P.pl + j) = oEM + (3 + P.pl) + j by omega_arith, ← hdj j hj, ht.copied j hj,
        addr_add (by omega_arith), enc_getD_msg P σ hj]
      have := congrArg (fun l => l.getD j 0) (hs.2.ro (R := P.MSG) (by simp))
      simp only at this
      rwa [bytesAt_getD hj, bytesAt_getD hj] at this

end VG.Proof.RsaPkcs1Enc.Arm.Pc

end

end


/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on ARMv7: the call and the masks

The call's arguments (`callArgs_wp`), the call of
`vg_rsa_public_precomputed_checked` (`call_vp`, correct and constant time:
its arguments and the public data it reads are the same in two runs), and
the masks of the result and of `out` by the zero test, and the wipe of `EM`
(`maskArgs_wp` … `wipe_wp`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Pc

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Precomputed VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp op2_imm op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

/-- The call's stack arguments. -/
abbrev outv (P : EP) : List (BitVec 32) :=
  [P.e, BitVec.ofNat 32 P.el, P.B + BitVec.ofNat 32 oEM, BitVec.ofNat 32 P.K, P.scr, BitVec.ofNat 32 P.sl]

def OutA (P : EP) (s : State) : Prop := ∀ i < 6, s.mem.readW (P.lay.fr (4 * i)) 32 = (outv P).getD i 0

/-- Before the call. -/
def G7 (P : EP) (σ s : State) : Prop :=
  G6 P σ s ∧ OutA P s ∧ s.gpr .r0 = P.out ∧ s.gpr .r1 = BitVec.ofNat 32 P.K ∧ s.gpr .r2 = P.pre ∧
    s.gpr .r3 = BitVec.ofNat 32 P.rl

/-- What the call writes and returns. -/
def CR (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  ∀ nB : List Byte, nB.length = P.K → Spec.Rsa.publicPrecompute nB = some P.pw →
    Spec.Rsa.written m (State.addr P.out) P.K r (Spec.Rsa.publicOpChecked nB P.eB (enc P σ))

/-- After the call. -/
def G8 (P : EP) (σ s : State) : Prop := S P σ s ∧ Zs P σ s ∧ EMok P σ s P.K ∧ CR P σ s.mem (s.gpr .r0)

/-- What the function writes and returns. -/
def Res (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  ∀ nB : List Byte, nB.length = P.K → Spec.Rsa.publicPrecompute nB = some P.pw →
    Spec.Rsa.written m (State.addr P.out) P.K r
      (if zf (psB P σ) = 0 then Spec.Rsa.publicOpChecked nB P.eB (enc P σ) else none)

/-! ## The call's arguments -/

theorem G6.frame6 {σ s t : State} (h : G6 P σ s) (ht : P.lay.St σ t) {d : Nat} (hd : d + 4 ≤ 24)
    (v : BitVec 32) (hm : t.mem = s.mem.writeW (P.lay.fr d) v) : G6 P σ t := by
  obtain ⟨hs, zs, em⟩ := h
  refine ⟨⟨hs.1, ht⟩, ?_, fun i hi => ?_⟩
  · rw [Zs, hm, Lay.readW_fr_other _ _ _ (by simp only [oZ]; omega_arith) (by simp only [oZ]; omega_arith) (by omega_arith)]
    exact zs
  · have hK := hs.1.k1024
    rw [hm, Lay.byte_fr_other _ _ _ (by simp only [oEM]; omega_arith) (by simp only [oEM]; omega_arith) (by omega_arith)]
    exact em i hi

theorem callArgs_wp {σ s : State} (h : G6 P σ s) : WP isa (.block callArgs) s (G7 P σ) := by
  have hs := h.1
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t0 u0 => ?_
  obtain h0 : G6 P σ t0 := ⟨⟨hs.1, hs.2.of_rest (u0.rest (ws := [.r12]) (by simp)) u0.mem⟩,
    by rw [Zs, u0.mem]; exact h.2.1, fun i hi => by rw [u0.mem]; exact h.2.2 i hi⟩
  obtain r12 : t0.gpr .r12 = P.B := by rw [u0.gpr, hs.2.sp, BitVec.add_zero]
  refine h0.1.2.wp_copyArg (j := 4) (d := 0) r12 (by simp) (by dsimp only; decide) (by dsimp only; decide)
    (by decide) (by decide) fun t1 s1 v1 g1 m1 => ?_
  obtain h1 := h0.frame6 s1 (by decide) _ m1
  refine s1.wp_copyArg (j := 5) (d := 4) (by rw [g1 _ (by decide), r12]) (by simp) (by dsimp only; decide)
    (by dsimp only; decide) (by decide) (by decide) fun t2 s2 v2 g2 m2 => ?_
  obtain h2 := h1.frame6 s2 (by decide) _ m2
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  obtain s3 : P.lay.St σ t3 := s2.of_rest (u3.rest (ws := [.r0]) (by simp)) u3.mem
  obtain h3 : G6 P σ t3 := ⟨⟨hs.1, s3⟩, by rw [Zs, u3.mem]; exact h2.2.1, fun i hi => by rw [u3.mem]; exact h2.2.2 i hi⟩
  obtain r12' : t3.gpr .r12 = P.B := by rw [u3.other _ (by decide), g2 _ (by decide), g1 _ (by decide), r12]
  refine s3.wp_strFr (d := 8) (by dsimp only; decide) (by decide) r12' fun t4 s4 m4 => ?_
  obtain h4 := h3.frame6 s4 (by decide) _ m4.mem
  refine s4.wp_copyArg (j := 3) (d := 12) (by rw [m4.gpr, r12']) (by simp) (by dsimp only; decide)
    (by dsimp only; decide) (by decide) (by decide) fun t5 s5 v5 g5 m5 => ?_
  obtain h5 := h4.frame6 s5 (by decide) _ m5
  refine s5.wp_copyArg (j := 10) (d := 16) (by rw [g5 _ (by decide), m4.gpr, r12']) (by simp)
    (by dsimp only; decide) (by dsimp only; decide) (by decide) (by decide) fun t6 s6 v6 g6 m6 => ?_
  obtain h6 := h5.frame6 s6 (by decide) _ m6
  refine s6.wp_copyArg (j := 11) (d := 20) (by rw [g6 _ (by decide), g5 _ (by decide), m4.gpr, r12'])
    (by simp) (by dsimp only; decide) (by dsimp only; decide) (by decide) (by decide) fun t7 s7 v7 g7 m7 => ?_
  obtain h7 := h6.frame6 s7 (by decide) _ m7
  refine s7.wp_arg (j := 0) (by simp) (by dsimp only; decide) fun t8 s8 u8 => ?_
  refine s8.wp_arg (j := 3) (by simp) (by dsimp only; decide) fun t9 s9 u9 => ?_
  refine s9.wp_arg (j := 12) (by simp) (by dsimp only; decide) fun t10 s10 u10 => ?_
  refine s10.wp_arg (j := 13) (by simp) (by dsimp only; decide) fun t11 s11 u11 => WP.block_nil ?_
  obtain mm : t11.mem = t7.mem := by rw [u11.mem, u10.mem, u9.mem, u8.mem]
  refine ⟨⟨⟨hs.1, s11⟩, by rw [Zs, mm]; exact h7.2.1, fun i hi => by rw [mm]; exact h7.2.2 i hi⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [mm, m7]
    obtain w : ∀ (m : Mem) (d e : Nat) (v : BitVec 32), d + 4 ≤ e ∨ e + 4 ≤ d → d + 4 ≤ 24 → e + 4 ≤ 24 →
        (m.writeW (P.lay.fr e) v).readW (P.lay.fr d) 32 = m.readW (P.lay.fr d) 32 :=
      fun m d e v h hd he => Lay.readW_fr_other _ _ _ h (by omega_arith) (by omega_arith)
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [w _ _ _ _ (by decide) (by decide) (by decide), m6, w _ _ _ _ (by decide) (by decide) (by decide), m5,
        w _ _ _ _ (by decide) (by decide) (by decide), m4.mem, w _ _ _ _ (by decide) (by decide) (by decide),
        u3.mem, m2, w _ _ _ _ (by decide) (by decide) (by decide), m1]
      exact Mem.readW_writeW_self32 _ _ _
    · rw [w _ _ _ _ (by decide) (by decide) (by decide), m6, w _ _ _ _ (by decide) (by decide) (by decide), m5,
        w _ _ _ _ (by decide) (by decide) (by decide), m4.mem, w _ _ _ _ (by decide) (by decide) (by decide),
        u3.mem, m2]
      exact Mem.readW_writeW_self32 _ _ _
    · rw [w _ _ _ _ (by decide) (by decide) (by decide), m6, w _ _ _ _ (by decide) (by decide) (by decide), m5,
        w _ _ _ _ (by decide) (by decide) (by decide), m4.mem, Mem.readW_writeW_self32, u3.gpr, dpVal, g2 _ (by decide),
        g1 _ (by decide), r12]
      rfl
    · rw [w _ _ _ _ (by decide) (by decide) (by decide), m6, w _ _ _ _ (by decide) (by decide) (by decide), m5]
      exact Mem.readW_writeW_self32 _ _ _
    · rw [w _ _ _ _ (by decide) (by decide) (by decide), m6]
      exact Mem.readW_writeW_self32 _ _ _
    · exact Mem.readW_writeW_self32 _ _ _
  · rw [u11.other _ (by decide), u10.other _ (by decide), u9.other _ (by decide), u8.gpr]; rfl
  · rw [u11.other _ (by decide), u10.other _ (by decide), u9.gpr]; rfl
  · rw [u11.other _ (by decide), u10.gpr]; rfl
  · rw [u11.gpr]; rfl

end VG.Proof.RsaPkcs1Enc.Arm.Pc

namespace VG.Proof.RsaPkcs1Enc.Arm.Pc

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Precomputed VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp op2_imm op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

theorem G7.pdArgs {σ s : State} (h : G7 P σ s) :
    PdArgs s P.out P.pre P.e (P.B + BitVec.ofNat 32 oEM) P.scr P.K P.el P.rl P.sl := by
  obtain ⟨⟨hs, -, -⟩, oa, r0, r1, r2, r3⟩ := h
  obtain a : ∀ i < 6, stackArg s i = (outv P).getD i 0 := fun i hi => by
    rw [← oa i hi]
    simp only [stackArg, stackArgAddr, hs.2.sp]
    rw [hs.2.ok.addrB (by show 4 * i < frameBytes + 56 + 40; simp only [frameBytes]; omega_arith)]
  have h1 := hs.1
  exact ⟨r0, r1, r2, r3, a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide),
    a 5 (by decide), h1.kv, h1.rlK, h1.el1, h1.elK, h1.slK,
    by have := hs.1.ok.fits P.SCR (by simp); simp only [Proof.X25519.Arm.addr_toNat] at this; omega_arith⟩

/-- `EM`, as the call reads it. -/
theorem inpA (P : EP) {σ : State} (h : In P σ) : State.addr (P.B + BitVec.ofNat 32 oEM) = P.lay.fr oEM :=
  h.ok.addrB (by show oEM < frameBytes + 56 + 40; decide)

theorem call_pre {σ s : State} (h : G7 P σ s) :
    (Proof.Rsa.publicPrecomputedCheckedContract abi 56).pre
      (s.callEntry.withRegions (pdRd P.B P.pre P.e (P.B + BitVec.ofNat 32 oEM) P.K P.el P.rl)
        (pdWr P.out P.scr P.K P.sl)) := by
  have hs := h.1.1
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have fit := ok.fit
  have hB := ok.B56
  obtain e := inpA P hs.1
  obtain hfr : ∀ {R : Region}, R ∈ P.lay.ro ∨ R ∈ P.lay.rw → ∀ {d n : Nat}, d + n ≤ frameBytes + 56 →
      Region.Disjoint ⟨P.lay.fr d, n⟩ R := fun hR _ _ hd => ok.stk_fr hR hd
  obtain fs := fun {R : Region} (hR : R ∈ P.lay.ro ++ P.lay.rw) => ok.fits R hR
  obtain q0 : State.addr P.B = P.lay.fr 0 := by simp
  refine pd_pre h.pdArgs hs.2.sp (by omega_arith) (by simp only [frameBytes] at fit; omega_arith)
    (by have := fs (R := P.OUT) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this)
    (by have := fs (R := P.PRE) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this)
    (by have := fs (R := P.E) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this)
    (by rw [show (P.B + BitVec.ofNat 32 oEM).toNat = P.B.toNat + oEM from
          Proof.X25519.Arm.toNat_add_lt (by simp only [oEM, frameBytes] at fit ⊢; rw [BitVec.toNat_ofNat]; omega_arith) |>.trans
          (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)])]
        simp only [oEM, frameBytes] at fit ⊢; omega_arith)
    (by have := fs (R := P.SCR) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this)
    (ok.rw_ro (by simp) (by simp)) (ok.rw_ro (by simp) (by simp))
    (by rw [e]; exact (hfr (R := P.OUT) (.inr (by simp)) (by simp only [oEM, frameBytes]; omega_arith)).symm)
    (List.pairwise_pair.mp ok.wrw)
    (by rw [q0]; exact (hfr (R := P.OUT) (.inr (by simp)) (by decide)).symm)
    (ok.rw_ro (by simp) (by simp)).symm (ok.rw_ro (by simp) (by simp)).symm
    (by rw [e]; exact hfr (R := P.SCR) (.inr (by simp)) (by simp only [oEM, frameBytes]; omega_arith))
    (by rw [q0]; exact (hfr (R := P.SCR) (.inr (by simp)) (by decide)).symm) ?_
  intro r hr
  have low : (⟨State.addr P.B - BitVec.ofNat 64 56, 56⟩ : Region) = P.lay.LOW := rfl
  rw [low]
  simp only [pdRd, pdWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ok.low_buf (R := P.PRE) (.inl (by simp))
  · exact ok.low_buf (R := P.E) (.inl (by simp))
  · rw [e]; exact (Lay.fr_low (by simp only [oEM]; omega_arith)).symm
  · rw [q0]; exact (Lay.fr_low (by decide)).symm
  · exact ok.low_buf (R := P.OUT) (.inr (by simp))
  · exact ok.low_buf (R := P.SCR) (.inr (by simp))

theorem S.eB {σ s : State} (hs : S P σ s) : Spec.Rsa.bytesAt s.mem (State.addr P.e) P.el = P.eB :=
  (hs.2.ro (R := P.E) (by simp)).trans hs.1.eB

theorem S.pw {σ s : State} (hs : S P σ s) : Spec.Rsa.wordsAt s.mem (State.addr P.pre) P.rl = P.pw :=
  (hs.2.ro_words (R := P.PRE) (by simp) rfl).trans hs.1.pw

theorem EMok.bytes {σ s : State} (h : EMok P σ s P.K) (hK : P.pl + P.ml + 3 = P.K) :
    Spec.Rsa.bytesAt s.mem (P.lay.fr oEM) P.K = enc P σ := by
  obtain hl := enc_length P σ
  rw [show P.K = (enc P σ).length by omega_arith]
  exact bytesAt_eq fun i hi => by rw [Offset.add_ofNat_add_ofNat]; exact h i (by omega_arith)

theorem call_vp (c : PdImpl) : VP (G7 P) (.call c.name c.code) (G8 P) := by
  refine VP.callF c.verified c.stack (pdRd P.B P.pre P.e (P.B + BitVec.ofNat 32 oEM) P.K P.el P.rl)
    (pdWr P.out P.scr P.K P.sl) (fun _ _ h => call_pre h) (fun σ s h => ?_) (fun σ s h => ?_)
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) (fun σ s s' h rd wr sp fr _ po => ?_)
  · have hs := h.1.1
    have ok := hs.1.ok
    have hK := hs.1.k1024
    obtain e := inpA P hs.1
    obtain q0 : State.addr P.B = P.lay.fr 0 := by simp
    obtain hro : ∀ R ∈ P.lay.ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.2.rd, ok.rd]; exact List.mem_append_left _ hR)
    obtain hrw : ∀ R ∈ P.lay.rw, Covers [R] s.wr := fun R hR =>
      Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.2.wr, ok.wr]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hR)
    obtain wr : Covers (pdWr P.out P.scr P.K P.sl) s.wr :=
      (hrw P.OUT (by simp)).cons (hrw P.SCR (by simp))
    refine ⟨Covers.append_left ((hro P.PRE (by simp)).cons ((hro P.E (by simp)).cons ?_)) wr.right, wr⟩
    refine Covers.cons ?_ (Covers.cons ?_ Covers.nil)
    · rw [e]; exact (Covers.one (hs.2.inFr (by show oEM + P.K ≤ frameBytes; simp only [oEM, frameBytes]; omega_arith))).right
    · rw [q0]; exact (Covers.one (hs.2.inFr (by show 0 + 24 ≤ frameBytes; decide))).right
  · rw [h.1.1.2.sp]; exact h.1.1.1.ok.B56
  · exact pd_pub h₁.pdArgs h₂.pdArgs (by rw [h₁.1.1.2.sp, h₂.1.1.2.sp]) (by rw [h₁.1.1.pw, h₂.1.1.pw])
      (by rw [h₁.1.1.eB, h₂.1.1.eB]) _ _
  · have hh := h
    obtain ⟨⟨hs, zs, em⟩, -, -⟩ := h
    have ok := hs.1.ok
    have hK := hs.1.k1024
    have hpl := hs.1.em_len
    obtain low : FrameStack.belowA s.sp 56 = P.lay.LOW := by rw [hs.2.sp]; exact ok.low_eq
    rw [low] at fr
    have fr' : Frame [P.OUT, P.SCR, P.lay.LOW] s.mem s'.mem := fr
    obtain st : P.lay.St σ s' := hs.2.write fr' (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨P.OUT, by simp, fun _ h => h⟩
      · exact ⟨P.SCR, by simp, fun _ h => h⟩
      · exact ⟨P.lay.LOW, by simp, fun _ h => h⟩) rd wr sp
    obtain apart : ∀ {d n : Nat}, d + n ≤ frameBytes → ∀ r ∈ [P.OUT, P.SCR, P.lay.LOW],
        Region.Disjoint ⟨P.lay.fr d, n⟩ r := fun hd r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ok.stk_fr (.inr (by simp)) (by show _ ≤ frameBytes + 56; omega_arith)
      · exact ok.stk_fr (.inr (by simp)) (by show _ ≤ frameBytes + 56; omega_arith)
      · exact Lay.fr_low (by simp only [frameBytes] at hd; omega_arith)
    refine ⟨⟨hs.1, st⟩, ?_, fun i hi => ?_, fun nB hn hp => ?_⟩
    · rw [Zs, fr'.readW (r := ⟨P.lay.fr oZ, 4⟩) (Region.contains_self _ _) (apart (by decide)) (by decide)]
      exact zs
    · rw [fr'.byte1 (apart (by simp only [oEM, frameBytes]; omega_arith))]
      exact em i hi
    · have := pd_post hh.pdArgs po nB hn (by rw [hs.pw]; exact hp)
      rw [hs.eB, inpA P hs.1, em.bytes hpl] at this
      exact this

/-! ## The masks -/

theorem zf_cases (bs : List Byte) : zf bs = 0 ∨ zf bs = 1 := by
  unfold zf; split <;> simp

theorem masked {m m' : Mem} {a : Addr} {K : Nat} {r z : BitVec 32} {o : Option (List Byte)}
    (hz : z = 0 ∨ z = 1) (hw : Spec.Rsa.written m a K r o)
    (hb : Spec.Rsa.bytesAt m' a K = (Spec.Rsa.bytesAt m a K).map (· &&& (z - 1).setWidth 8)) :
    Spec.Rsa.written m' a K (r &&& (z - 1)) (if z = 0 then o else none) := by
  rcases hz with rfl | rfl
  · simp only [ite_true]
    obtain e1 : (0 : BitVec 32) - 1 = BitVec.allOnes 32 := by decide
    obtain e8 : (BitVec.allOnes 32).setWidth 8 = BitVec.allOnes 8 := by decide
    obtain hb' : Spec.Rsa.bytesAt m' a K = Spec.Rsa.bytesAt m a K := by
      rw [hb, e1, e8]
      exact (List.map_congr_left (g := id) fun x _ => BitVec.and_allOnes).trans (List.map_id _)
    rw [e1, BitVec.and_allOnes]
    cases o with
    | some y => exact ⟨hw.1, hb'.trans hw.2⟩
    | none => exact ⟨hw.1, hb'.trans hw.2⟩
  · simp only [show (1 : BitVec 32) = 0 ↔ False by decide, ite_false]
    obtain e1 : (1 : BitVec 32) - 1 = 0 := by decide
    obtain e0 : r &&& (0 : BitVec 32) = 0 := by simp
    rw [e1, e0]
    refine ⟨rfl, ?_⟩
    rw [hb, e1]
    apply List.ext_getElem (by simp [bytesAt_length])
    intro i h₁ h₂
    simp

/-- Before the mask of `out`. -/
def G9 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ EMok P σ s P.K ∧ ∃ rc, CR P σ s.mem rc ∧ s.gpr .r3 = rc &&& (zf (psB P σ) - 1) ∧
    s.gpr .r2 = zf (psB P σ) - 1 ∧ s.gpr .r0 = P.out ∧ s.gpr .lr = BitVec.ofNat 32 P.K

/-- `out` masked. -/
def G10 (P : EP) (σ s : State) : Prop := S P σ s ∧ EMok P σ s P.K ∧ Res P σ s.mem (s.gpr .r3)

/-- Before the wipe of `EM`. -/
def G11 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ Res P σ s.mem (s.gpr .r3) ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 oEM ∧
    s.gpr .lr = BitVec.ofNat 32 P.K ∧ s.gpr .r2 = 0

/-- `EM` wiped. -/
def G12 (P : EP) (σ s : State) : Prop := S P σ s ∧ Res P σ s.mem (s.gpr .r3)

/-- The end of the body. -/
def G13 (P : EP) (σ s : State) : Prop := S P σ s ∧ Res P σ s.mem (s.gpr .r0)

theorem maskArgs_wp {σ s : State} (h : G8 P σ s) : WP isa (.block maskArgs) s (G9 P σ) := by
  obtain ⟨hs, zs, em, cr⟩ := h
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  obtain s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_slot (d := oZ) (by show oZ + 4 ≤ frameBytes; decide) (by decide) fun t2 s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  refine wp_dp (op2_reg _ _) fun t4 u4 => ?_
  obtain s4 : P.lay.St σ t4 := (s2.of_rest (u3.rest (ws := [.r2]) (by simp)) u3.mem).of_rest
    (u4.rest (ws := [.r3]) (by simp)) u4.mem
  refine s4.wp_arg (j := 0) (by simp) (by dsimp only; decide) fun t5 s5 u5 => ?_
  refine s5.wp_arg (j := 3) (by simp) (by dsimp only; decide) fun t6 s6 u6 => WP.block_nil ?_
  obtain mm : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  obtain z2 : t2.gpr .r3 = zf (psB P σ) := by rw [u2.gpr, u1.mem]; exact zs
  refine ⟨⟨hs.1, s6⟩, fun i hi => by rw [mm]; exact em i hi, s.gpr .r0, by rw [mm]; exact cr, ?_, ?_, ?_, ?_⟩
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, dpVal, u3.other _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide), u3.gpr, dpVal, z2]
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr, dpVal, z2]
  · rw [u6.other _ (by decide), u5.gpr]; rfl
  · rw [u6.gpr]; rfl

theorem maskOut_wp {σ s : State} (h : G9 P σ s) : WP isa Impl.Bignum.Arm.maskBytes s (G10 P σ) := by
  obtain ⟨hs, em, rc, cr, r3, r2, r0, lr⟩ := h
  have ok := hs.1.ok
  have hK := hs.1.k64
  obtain hfo := ok.fits P.OUT (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hfo
  refine WP.mono (Bignum.Arm.maskBuffer_ok s (dst := P.out) (n := P.K) (by omega_arith) (by have := hs.1.k1024; omega_arith)
    hfo ⟨P.OUT, by rw [hs.2.wr, ok.wr]; simp, Region.contains_self _ _⟩ r0 lr) fun t ⟨hb, fr, rest⟩ => ?_
  obtain st : P.lay.St σ t := hs.2.write fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.OUT, by simp, fun _ h => h⟩) rest.rd rest.wr rest.sp
  refine ⟨⟨hs.1, st⟩, fun i hi => ?_, fun nB hn hp => ?_⟩
  · rw [fr.byte1 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ok.stk_fr (.inr (by simp)) (by show _ ≤ frameBytes + 56; simp only [oEM, frameBytes]; have := hs.1.k1024; omega_arith))]
    exact em i hi
  · rw [rest.gpr .r3 (by decide), r3]
    rw [r2] at hb
    exact masked (zf_cases _) (cr nB hn hp) hb

theorem wipeArgs_wp {σ s : State} (h : G10 P σ s) : WP isa (.block wipeArgs) s (G11 P σ) := by
  obtain ⟨hs, -, res⟩ := h
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  refine wp_dp (op2_imm (by decide)) fun t2 u2 => ?_
  obtain s2 : P.lay.St σ t2 := (hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem).of_rest
    (u2.rest (ws := [.r0]) (by simp)) u2.mem
  refine s2.wp_arg (j := 3) (by simp) (by dsimp only; decide) fun t3 s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun t4 u4 => WP.block_nil ⟨⟨hs.1, s3.of_rest (u4.rest (ws := [.r2])
    (by simp)) u4.mem⟩, ?_, ?_, ?_, u4.gpr⟩
  · rw [u4.mem, u3.mem, u2.mem, u1.mem, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide)]
    exact res
  · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, dpVal, u1.gpr, hs.2.sp, BitVec.add_zero]
  · rw [u4.other _ (by decide), u3.gpr]; rfl

theorem wipe_wp {σ s : State} (h : G11 P σ s) : WP isa Impl.Bignum.Arm.maskBytes s (G12 P σ) := by
  obtain ⟨hs, res, r0, lr, -⟩ := h
  have ok := hs.1.ok
  have hK := hs.1.k1024
  obtain e := inpA P hs.1
  have fit := ok.fit
  refine WP.mono (Bignum.Arm.maskBuffer_ok s (dst := P.B + BitVec.ofNat 32 oEM) (n := P.K) (by have := hs.1.k64; omega_arith)
    (by omega_arith) (by
      rw [Proof.X25519.Arm.toNat_add_lt (by rw [BitVec.toNat_ofNat]; simp only [oEM, frameBytes] at fit ⊢; omega_arith),
        BitVec.toNat_ofNat]
      simp only [oEM, frameBytes] at fit ⊢; omega_arith)
    (by rw [e]; exact hs.2.inFr (by show oEM + P.K ≤ frameBytes; simp only [oEM, frameBytes]; omega_arith)) r0 lr)
    fun t ⟨_, fr, rest⟩ => ?_
  rw [e] at fr
  obtain st : P.lay.St σ t := hs.2.frameW (by show oEM + P.K ≤ frameBytes; simp only [oEM, frameBytes]; omega_arith) fr
    rest.rd rest.wr rest.sp
  refine ⟨⟨hs.1, st⟩, fun nB hn hp => ?_⟩
  obtain hb : Spec.Rsa.bytesAt t.mem (State.addr P.out) P.K = Spec.Rsa.bytesAt s.mem (State.addr P.out) P.K :=
    bytesAt_frame fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (ok.stk_fr (.inr (by simp)) (by show _ ≤ frameBytes + 56; simp only [oEM, frameBytes]; omega_arith)).symm)
      (by omega_arith)
  obtain w := res nB hn hp
  rw [rest.gpr .r3 (by decide)]
  revert w
  generalize (if zf (psB P σ) = 0 then Spec.Rsa.publicOpChecked nB P.eB (enc P σ) else none) = o
  intro w
  cases o with
  | some y => exact ⟨w.1, hb.trans w.2⟩
  | none => exact ⟨w.1, hb.trans w.2⟩

theorem fin_wp {σ s : State} (h : G12 P σ s) : WP isa (.block [.mov .r0 (.reg .r3)]) s (G13 P σ) :=
  wp_mov (op2_reg _ _) fun t u => WP.block_nil ⟨⟨h.1.1, h.1.2.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem⟩,
    by rw [u.mem, u.gpr]; exact h.2⟩

end VG.Proof.RsaPkcs1Enc.Arm.Pc

end

end


/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on ARMv7: the body

The pieces as `VP`s, correct and constant time at once, put together
(`body_vp`): from the state the body starts from, it ends with the result
(`G13`), and two runs with the same public data leak the same trace.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Pc

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Precomputed VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

/-- Two states of the body have the same stack pointer. -/
theorem S_sp {σ₁ σ₂ s₁ s₂ : State} (h₁ : S P σ₁ s₁) (h₂ : S P σ₂ s₂) : s₁.sp = s₂.sp := by
  rw [h₁.2.sp, h₂.2.sp]

theorem start_vp : VP (S P) (.block start) (G1 P) :=
  VP.stk (code := [_, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁ h₂) fun _ _ h => start_wp h

theorem head_vp : VP (G1 P) (.block head) (PsI P P.pl) :=
  VP.taint [.r0] head_taint (fun _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) fun _ _ h => head_wp h

theorem psLoop_vp : VP (PsI P P.pl) psLoop (PsI P 0) := by
  refine (VP.loop (I := fun k => PsI P k) (fun n => VP.taint [.r0, .r1, .lr] psBody_taint
    (fun _ _ _ _ h₁ h₂ r hr => ?_) fun _ _ h => psBody_wp h) (P.pl - 1)).mono (fun σ s h => ?_) fun _ _ h => h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  · rw [show P.pl - 1 + 1 = P.pl by have := h.1.1.pl8; omega_using [this]]; exact h

theorem sep_vp : VP (PsI P 0) (.block sep) (G4 P) :=
  VP.taint [.r0] sep_taint (fun _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.1, h₂.2.2.1]) fun _ _ h => sep_wp h

theorem msgArgs_vp : VP (G4 P) (.block msgArgs) (G5 P) :=
  VP.stk (code := [_, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1 h₂.1) fun _ _ h => msgArgs_wp h

theorem msgCopy_vp : VP (G5 P) msgCopy (G6 P) := by
  refine VP.seq (G := fun σ s => G5 P σ s ∧ s.z = decide (P.ml = 0))
    (VP.taint [.lr] cmp_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.2.1, h₂.2.2.2.1]) fun _ _ h => cmp_wp h) ?_
  refine VP.ite (fun _ _ _ _ h₁ h₂ => by rw [Proof.X25519.Arm.eval_eq, Proof.X25519.Arm.eval_eq, h₁.2, h₂.2])
    (VP.block_nil fun _ _ h => skip_g6 h.1.1 (by have := h.2; rw [Proof.X25519.Arm.eval_eq, h.1.2] at this; simpa using this))
    (VP.ct Bignum.Arm.copyBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.1.1.2.1, h₂.1.1.2.1], by rw [h₁.1.1.2.2.1, h₂.1.1.2.2.1],
      by rw [h₁.1.1.2.2.2.1, h₂.1.1.2.2.2.1]⟩)
      fun _ _ h => copy_wp h.1.1 (by have := h.2; rw [Proof.X25519.Arm.eval_eq, h.1.2] at this; simpa using this))

theorem callArgs_vp : VP (G6 P) (.block callArgs) (G7 P) :=
  VP.stk (code := [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _]) (by decide) (by decide)
    (fun _ _ _ _ h₁ h₂ => S_sp h₁.1 h₂.1) fun _ _ h => callArgs_wp h

theorem maskArgs_vp : VP (G8 P) (.block maskArgs) (G9 P) :=
  VP.stk (code := [_, _, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1 h₂.1)
    fun _ _ h => maskArgs_wp h

theorem maskOut_vp : VP (G9 P) Impl.Bignum.Arm.maskBytes (G10 P) :=
  VP.ct Bignum.Arm.maskBytes_ct (fun _ _ _ _ h₁ h₂ => by
    obtain ⟨_, _, _, _, _, _, r0₁, lr₁⟩ := h₁
    obtain ⟨_, _, _, _, _, _, r0₂, lr₂⟩ := h₂
    exact ⟨by rw [r0₁, r0₂], by rw [lr₁, lr₂]⟩) fun _ _ h => maskOut_wp h

theorem wipeArgs_vp : VP (G10 P) (.block wipeArgs) (G11 P) :=
  VP.stk (code := [_, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1 h₂.1)
    fun _ _ h => wipeArgs_wp h

theorem wipe_vp : VP (G11 P) Impl.Bignum.Arm.maskBytes (G12 P) :=
  VP.ct Bignum.Arm.maskBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.2.2.1, h₂.2.2.1], by rw [h₁.2.2.2.1, h₂.2.2.2.1]⟩)
    fun _ _ h => wipe_wp h

theorem fin_vp : VP (G12 P) (.block [.mov .r0 (.reg .r3)]) (G13 P) :=
  VP.taint [] fin_taint (fun _ _ _ _ _ _ _ h => absurd h List.not_mem_nil) fun _ _ h => fin_wp h

theorem body_vp (c : PdImpl) : VP (S P) (body c.name c.code) (G13 P) :=
  start_vp.seq (head_vp.seq (psLoop_vp.seq (sep_vp.seq (msgArgs_vp.seq (msgCopy_vp.seq (callArgs_vp.seq
    ((call_vp c).seq (maskArgs_vp.seq (maskOut_vp.seq (wipeArgs_vp.seq (wipe_vp.seq fin_vp)))))))))))

end VG.Proof.RsaPkcs1Enc.Arm.Pc

end

end


/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on ARMv7: verified

The frames around the body (`wrap_ok`, `wrap_ct`), the result as the shared
contract states it (`res_post`), and a state that meets it (`sat`):
`vg_rsa_pkcs1_encrypt_precomputed`, calling any implementation `c` of
`vg_rsa_public_precomputed_checked`, is verified (`code_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Pc

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Precomputed VG.Proof.RsaPkcs1Sig.Arm

/-- Encryption, once the lengths are as the contract has them. -/
theorem encrypt_eq {nB eB M PS : List Byte} (hM : M.length + 11 ≤ nB.length)
    (hPS : PS.length = nB.length - M.length - 3) :
    Spec.RsaPkcs1Enc.encrypt nB eB M PS =
      if zf PS = 0 then Spec.Rsa.publicOpChecked nB eB (Spec.RsaPkcs1Enc.encode M PS) else none := by
  simp only [Spec.RsaPkcs1Enc.encrypt, hM, hPS, true_and, zf]
  split <;> simp_all

theorem entered_state {s : State} (h : spec.pre s) :
    S (ep s) (entered frameBytes s) (entered frameBytes s) :=
  ⟨in_of_pre h, ⟨(in_of_pre h).ok, (in_of_pre h).ok.sp, rfl, rfl, Frame.refl _ _⟩⟩

theorem spec_sp {s : State} (h : spec.pre s) : stackBytes ≤ s.sp.toNat := by
  sig_pre [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi,
    argRegs, reduceClassify, Loc.val] at h
  exact h.1

theorem code_ok (c : PdImpl) {s : State} (h : spec.pre s) :
    WP isa (code c.name c.code) s fun t => abiPreserved s t ∧ spec.post s t := by
  obtain hs := spec_sp h
  obtain hin := in_of_pre h
  obtain st := entered_state h
  obtain hsp : 56 + frameBytes ≤ s.sp.toNat := by simp only [stackBytes] at hs; omega_using [hs]
  refine WP.mono (wrap_ok (by decide) (by omega_using [hsp]) (W := (ep s).lay.W)
    (Q := fun r m => Res (ep s) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono ((body_vp c).wp _ _ st) fun u hu => ⟨hu.1.2.frame, hu.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · rw [pushRegion_eq (F := frameBytes) (A := 40) (argv := (ep s).argv)
      (ro := [(ep s).N, (ep s).E, (ep s).MSG, (ep s).PS, (ep s).PRE]) (rw := [(ep s).OUT, (ep s).SCR]) hsp]
    exact hin.ok.push_apart r hr
  · sig_post [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi,
      argRegs, reduceClassify, Loc.val]
    rw [BitVec.setWidth_append_eq_right]
    intro hp
    obtain hn : (Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 (s.gpr .r2)) (s.gpr .r3).toNat).length =
        (s.gpr .r3).toNat := bytesAt_length _ _ _
    obtain w := res _ hn hp
    obtain ro := fun {R : Region} (hR : R ∈ [(ep s).N, (ep s).E, (ep s).MSG, (ep s).PS, (ep s).PRE]) =>
      entered_ro (F := frameBytes) (A := 40) (argv := (ep s).argv) (rw := [(ep s).OUT, (ep s).SCR]) hin.ok hsp hR
    obtain hM : msgB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2))
        (stackArg s 3).toNat := ro (R := (ep s).MSG) (by simp)
    obtain hP : psB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 4))
        (stackArg s 5).toNat := ro (R := (ep s).PS) (by simp)
    have hml := hin.mlK
    have hpl := hin.plK
    rw [encrypt_eq (by simp only [bytesAt_length]; exact hml) (by simp only [bytesAt_length]; exact hpl)]
    simp only [enc] at w
    rw [hM, hP] at w
    exact w

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (h : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h

/-- Two entry states with the same public data have the same public parameters. -/
theorem ep_eq {s₁ s₂ : State} (hp : spec.pub s₁ s₂) : ep s₁ = ep s₂ := by
  sig_pub [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi,
    argRegs, reduceClassify, Loc.val] at hp
  obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hp
  obtain ⟨hab, hc⟩ := List.append_inj hl (by simp [bytesAt_length, h3, a1])
  obtain ⟨-, he⟩ := List.append_inj (map_toNat_inj hab) (by simp [bytesAt_length, h3])
  obtain hw := map_toNat_inj hc
  simp only [ep]
  rw [hsp, h0, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
  rw [a0, a1] at he
  rw [a8, a9] at hw
  rw [show State.addr (stackArg s₂ 0) = BitVec.setWidth 64 (stackArg s₂ 0) from rfl, he,
    show State.addr (stackArg s₂ 8) = BitVec.setWidth 64 (stackArg s₂ 8) from rfl, hw]

theorem code_ct (c : PdImpl) : ConstantTime isa spec.pre spec.pub (code c.name c.code) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain hep := ep_eq hp
  obtain hsp : s₁.sp = s₂.sp := by
    sig_pub [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi,
      argRegs, reduceClassify, Loc.val] at hp
    exact hp.1
  refine (wrap_ct (F := frameBytes) (by decide) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp)
    (fun a b h => by rw [h.1]; have := spec_sp h₁; simp only [stackBytes] at this; omega_using [this]) ?_
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp (P := ep s₁) c).ct.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨_, _, entered_state h₁, by rw [hep]; exact entered_state h₂⟩

/-- A state that meets the shared contract: a modulus of 64 bytes, `e` of one,
an empty message, the padding string of 61 bytes, and the stack arguments
at `0x8000`. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x21 else
    if a = 0x8004 then 1 else
    if a = 0x8009 then 0x30 else
    if a = 0x8011 then 0x31 else
    if a = 0x8014 then 0x3d else
    if a = 0x8019 then 0x40 else
    if a = 0x801c then 0x20 else
    if a = 0x801d then 4 else
    if a = 0x8021 then 0x70 else
    if a = 0x8024 then 0x10 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3000, 0⟩, ⟨0x3100, 61⟩, ⟨0x7000, 128⟩, ⟨0x8000, 40⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 8448⟩]

theorem sat : ∃ s, spec.pre s := by
  sig_implies_sat [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi,
    argRegs, reduceClassify, Loc.val, State.addr]
    [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid, Spec.Rsa.scratchWords,
      Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] using satState

/-- `vg_rsa_pkcs1_encrypt_precomputed`, calling `c`, meets the shared contract. -/
theorem code_verified (c : PdImpl) : Verified target (code c.name c.code) spec :=
  ⟨fun _ h => let ⟨t, s', he, hq⟩ := code_ok c h; ⟨t, s', he, hq.1, hq.2⟩, code_ct c, sat⟩

end VG.Proof.RsaPkcs1Enc.Arm.Pc
