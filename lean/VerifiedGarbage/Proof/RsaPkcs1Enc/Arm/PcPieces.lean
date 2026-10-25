module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.PcBuild
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Bignum.Arm.CopyRegion
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

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
  have h2 : P.lay.St σ t2 :=
    (hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem).of_rest (u2.rest (ws := [.r0]) (by simp)) u2.mem
  refine h2.wp_arg (j := 8) (by simp) (by dsimp only; decide) fun t3 s3 u3 => ?_
  refine s3.wp_arg (j := 9) (by simp) (by dsimp only; decide) fun t4 s4 u4 => WP.block_nil ⟨⟨hs.1, s4⟩, ?_, ?_, ?_⟩
  · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, dpVal, u1.gpr, hs.2.sp, BitVec.add_zero]
  · rw [u4.other _ (by decide), u3.gpr]; rfl
  · rw [u4.gpr]; rfl

theorem enc0 (P : EP) (σ : State) : (enc P σ).getD 0 0 = 0 := rfl
theorem enc1 (P : EP) (σ : State) : (enc P σ).getD 1 0 = 2 := rfl

theorem head_wp {σ s : State} (h : G1 P σ s) : WP isa (.block head) s (PsI P P.pl σ) := by
  obtain ⟨hs, r0, r1, lr⟩ := h
  have hk := hs.1.k64
  refine wp_mov (op2_imm (by decide)) fun t1 u1 => ?_
  have s1 : S P σ t1 := ⟨hs.1, hs.2.of_rest (u1.rest (ws := [.r2]) (by simp)) u1.mem⟩
  refine wp_strbEM s1 (off := 0) (n := 0) (by decide) (by omega_arith)
    (by rw [u1.other _ (by decide), r0]; simp) fun t2 s2 g2 m2 => ?_
  refine wp_mov (op2_imm (by decide)) fun t3 u3 => ?_
  have s3 : S P σ t3 := ⟨hs.1, s2.2.of_rest (u3.rest (ws := [.r2]) (by simp)) u3.mem⟩
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
    have e2 := EMok.store (EMok.zero (P := P) (σ := σ) (s := t1)) (by decide) (m := t2.mem)
      (by rw [m2, u1.gpr]; rfl)
    have e4 := EMok.store (n := 1) (s := t3) (fun i hi => by rw [u3.mem]; exact e2 i hi) (by decide)
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
  have hfp := hs.1.ok.fits P.PS (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hfp
  -- The byte of `PS`.
  have hpsA : State.addr (P.ps + BitVec.ofNat 32 (P.pl - (k + 1))) = State.addr P.ps +
      BitVec.ofNat 64 (P.pl - (k + 1)) := addr_add (by omega_arith)
  have hbyte : s.mem (State.addr P.ps + BitVec.ofNat 64 (P.pl - (k + 1))) =
      σ.mem (State.addr P.ps + BitVec.ofNat 64 (P.pl - (k + 1))) := by
    have := congrArg (fun l => l.getD (P.pl - (k + 1)) 0) (hs.2.ro (R := P.PS) (by simp))
    simp only at this
    rwa [bytesAt_getD (by omega_arith), bytesAt_getD (by omega_arith)] at this
  refine wp_ldrb (by decide) (a := State.addr P.ps + BitVec.ofNat 64 (P.pl - (k + 1)))
    (by rw [r1, BitVec.add_zero, hpsA])
    ⟨P.PS, List.mem_append_left _ (by rw [hs.2.rd, hs.2.ok.rd]; simp),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩ fun t1 u1 => ?_
  have s1 : S P σ t1 := ⟨hs.1, hs.2.of_rest (u1.rest (ws := [.r2]) (by simp)) u1.mem⟩
  refine wp_strbEM s1 (off := 0) (n := 2 + (P.pl - (k + 1))) (by decide) (by omega_arith)
    (by rw [u1.other _ (by decide), r0, BitVec.add_zero]) fun t2 s2 g2 m2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  refine wp_dp (op2_lsr (by decide)) fun t4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun t5 u5 => ?_
  refine wp_dp (op2_imm (by decide)) fun t6 u6 => ?_
  refine wp_subs (op2_imm (by decide)) fun t7 u7 z7 => WP.block_nil ?_
  have s7 : S P σ t7 := ⟨hs.1, ((((s2.2.of_rest (u3.rest (ws := [.r2]) (by simp)) u3.mem).of_rest
    (u4.rest (ws := [.r3]) (by simp)) u4.mem).of_rest (u5.rest (ws := [.r0]) (by simp)) u5.mem).of_rest
    (u6.rest (ws := [.r1]) (by simp)) u6.mem).of_rest (u7.rest (ws := [.lr]) (by simp)) u7.mem⟩
  have lr7 : t7.gpr .lr = BitVec.ofNat 32 k := by
    rw [u7.gpr, u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      g2, u1.other _ (by decide), lr]
    exact sub_one_ofNat (by omega_arith)
  have inv : PsI P k σ t7 := by
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
      have e := EMok.store em (by omega_arith) (m := t2.mem) (by
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
  have s1 : S P σ t1 := ⟨hs.1, hs.2.of_rest (u1.rest (ws := [.r2]) (by simp)) u1.mem⟩
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
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
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
  have e : BitVec.ofNat 32 P.ml - 0 = BitVec.ofNat 32 P.ml := by simp
  rw [z1, lr, e, Proof.X25519.Arm.ofNat_beq_zero (by omega_arith)]

theorem skip_g6 {σ s : State} (h : G5 P σ s) (h0 : P.ml = 0) : G6 P σ s := by
  obtain ⟨hs, -, -, -, zs, em⟩ := h
  exact ⟨hs, zs, em.mono (by have := hs.1.em_len; omega_arith)⟩

theorem copy_wp {σ s : State} (h : G5 P σ s) (h0 : P.ml ≠ 0) : WP isa Impl.Bignum.Arm.copyBytes s (G6 P σ) := by
  obtain ⟨hs, r0, r1, lr, zs, em⟩ := h
  have hK := hs.1.k1024
  have hpl := hs.1.em_len
  have hfm := hs.1.ok.fits P.MSG (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hfm
  have hfit := hs.2.ok.fit
  have hB : P.lay.B = P.B := rfl
  have hdst : State.addr (P.B + BitVec.ofNat 32 (oEM + (3 + P.pl))) = P.lay.fr (oEM + (3 + P.pl)) :=
    hs.2.ok.addrB (by show _ < frameBytes + 56 + 40; simp only [oEM, frameBytes]; omega_arith)
  have hsep : Region.Disjoint ⟨State.addr P.msg, P.ml⟩ ⟨State.addr (P.B + BitVec.ofNat 32 (oEM + (3 + P.pl))), P.ml⟩ := by
    rw [hdst]
    refine ((hs.2.ok.stk P.MSG (by simp)).sub_left (Lay.sub_stk ?_)).symm
    show oEM + (3 + P.pl) + P.ml ≤ frameBytes + 56; simp only [oEM, frameBytes]; omega_arith
  have hb : P.B.toNat + frameBytes + 56 + 40 ≤ 2 ^ 32 := hfit
  have hoff : oEM + (3 + P.pl) < 2 ^ 32 := by simp only [oEM]; omega_arith
  have hlt : P.B.toNat + (BitVec.ofNat 32 (oEM + (3 + P.pl))).toNat < 2 ^ 32 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff]; simp only [oEM, frameBytes] at hb ⊢; omega_arith
  have hdn : (P.B + BitVec.ofNat 32 (oEM + (3 + P.pl))).toNat = P.B.toNat + (oEM + (3 + P.pl)) := by
    rw [Proof.X25519.Arm.toNat_add_lt hlt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff]
  have ctx := Bignum.Arm.copyCtx_of_regions s P.msg (P.B + BitVec.ofNat 32 (oEM + (3 + P.pl))) (n := P.ml)
    (by omega_arith) hfm (by rw [hdn]; simp only [oEM, frameBytes] at hb ⊢; omega_arith)
    ⟨P.MSG, List.mem_append_left _ (by rw [hs.2.rd, hs.2.ok.rd]; simp), Region.contains_self _ _⟩
    (by rw [hdst]; exact hs.2.inFr (by show oEM + (3 + P.pl) + P.ml ≤ frameBytes; simp only [oEM, frameBytes]; omega_arith))
    hsep
  refine WP.mono (Bignum.Arm.copyBytes_ok s ctx (Nat.pos_of_ne_zero h0) r1 r0 lr) fun t ht => ?_
  have hdj : ∀ j < P.ml, State.addr (P.B + BitVec.ofNat 32 (oEM + (3 + P.pl)) + BitVec.ofNat 32 j) =
      P.lay.fr (oEM + (3 + P.pl) + j) := fun j hj => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact hs.2.ok.addrB (by show _ < frameBytes + 56 + 40; simp only [oEM, frameBytes]; omega_arith)
  have hF : Frame [⟨P.lay.fr (oEM + (3 + P.pl)), P.ml⟩] s.mem t.mem := fun x hx => by
    refine ht.outside x fun j hj e => hx _ (List.mem_singleton_self _) ?_
    rw [e, hdj j hj]
    exact Offset.contains _ (by omega_arith) (by omega_arith) (by simp only [oEM]; omega_arith)
  have st : P.lay.St σ t := hs.2.frameW (by show oEM + (3 + P.pl) + P.ml ≤ frameBytes; simp only [oEM, frameBytes]; omega_arith)
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
      have hj : j < P.ml := by omega_arith
      rw [show oEM + (3 + P.pl + j) = oEM + (3 + P.pl) + j by omega_arith, ← hdj j hj, ht.copied j hj,
        addr_add (by omega_arith), enc_getD_msg P σ hj]
      have := congrArg (fun l => l.getD j 0) (hs.2.ro (R := P.MSG) (by simp))
      simp only at this
      rwa [bytesAt_getD hj, bytesAt_getD hj] at this

end VG.Proof.RsaPkcs1Enc.Arm.Pc
