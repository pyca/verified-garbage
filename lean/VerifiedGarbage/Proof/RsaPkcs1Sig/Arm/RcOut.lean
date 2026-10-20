module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.RcPost
import VerifiedGarbage.Proof.Bignum.Arm.CopyRegion
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSASSA-PKCS1-v1_5 recovery with a precomputed public key on ARMv7: the value

The last `out_len` bytes of `EM₁` copied to `out` (`copyArgs_wp`,
`copy_wp`), and `out` masked with `0 - r` for the result `r`
(`maskArgs_wp`, `mask_wp`, `masked`), which is returned (`fin_wp`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Rc

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.RecoverPrecomputed
open VG.Impl.RsaPkcs1Sig.Arm.Precomputed (frameBytes oSt oOk oEM1 oEM2 ret0)
open VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp op2_imm op2_reg dpVal)

variable {P : EP}

/-- The result and `out`. -/
def RO (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  RR P σ r (Spec.Rsa.bytesAt m (State.addr P.out) P.ol)

/-- Before the copy. -/
def C8 (P : EP) (σ s : State) : Prop :=
  C0 P σ s ∧ RR P σ (s.gpr .r3) (Tail P s.mem) ∧ s.gpr .r0 = P.out ∧
    s.gpr .r1 = P.B + BitVec.ofNat 32 (oEM1 + (P.K - P.ol)) ∧ s.gpr .lr = BitVec.ofNat 32 P.ol

/-- After the copy. -/
def C9 (P : EP) (σ s : State) : Prop := C0 P σ s ∧ RO P σ s.mem (s.gpr .r3)

/-- Before the mask. -/
def C10 (P : EP) (σ s : State) : Prop :=
  C0 P σ s ∧ RO P σ s.mem (s.gpr .r3) ∧ s.gpr .r2 = 0 - s.gpr .r3 ∧ s.gpr .r0 = P.out ∧
    s.gpr .lr = BitVec.ofNat 32 P.ol

/-- After the mask. -/
def C11 (P : EP) (σ s : State) : Prop := C0 P σ s ∧ Res P σ s.mem (s.gpr .r3)

theorem copyArgs_wp {σ s : State} (h : C7 P σ s) : WP isa (.block copyArgs) s (C8 P σ) := by
  obtain ⟨⟨hs, hgl⟩, rr⟩ := h
  have hol : P.ol ≤ P.K := by have := hs.1.ol64; have := hs.1.k64; omega
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_arg (j := 0) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  have s3 : P.lay.St σ t3 := s2.of_rest (u3.rest (ws := [.r1]) (by simp)) u3.mem
  refine s3.wp_arg (j := 3) (by simp) (by dsimp only; decide) fun t4 s4 u4 => ?_
  refine wp_dp (op2_reg _ _) fun t5 u5 => ?_
  have s5 : P.lay.St σ t5 := s4.of_rest (u5.rest (ws := [.r1]) (by simp)) u5.mem
  refine s5.wp_arg (j := 1) (by simp) (by dsimp only; decide) fun t6 s6 u6 => ?_
  refine wp_dp (op2_reg _ _) fun t7 u7 => WP.block_nil ?_
  have mm : t7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have r3 : t7.gpr .r3 = s.gpr .r3 := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)]
  refine ⟨⟨⟨hs.1, s6.of_rest (u7.rest (ws := [.r1]) (by simp)) u7.mem⟩, hgl⟩, by rw [r3, mm]; exact rr, ?_, ?_, ?_⟩
  · rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.gpr]; rfl
  · rw [u7.gpr, dpVal, u6.other .r1 (by decide), u6.gpr, u5.gpr, dpVal, u4.other .r1 (by decide), u4.gpr,
      u3.gpr, dpVal, u2.other .r12 (by decide), u1.gpr, hs.2.sp, BitVec.add_zero]
    change P.B + BitVec.ofNat 32 oEM1 + BitVec.ofNat 32 P.K - BitVec.ofNat 32 P.ol = _
    rw [add_sub_ofNat _ hol, Offset.add_ofNat_add_ofNat]
  · rw [u7.other _ (by decide), u6.gpr]; rfl

theorem copy_wp {σ s : State} (h : C8 P σ s) : WP isa Impl.Bignum.Arm.copyBytes s (C9 P σ) := by
  obtain ⟨⟨hs, hgl⟩, rr, r0, r1, lr⟩ := h
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have h64 := hs.1.ol64
  have hol : P.ol ≤ P.K := by have := hs.1.k64; omega
  have fit := ok.fit
  have hfo := ok.fits P.OUT (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hfo
  have e1 : State.addr (P.B + BitVec.ofNat 32 (oEM1 + (P.K - P.ol))) = P.lay.fr (oEM1 + (P.K - P.ol)) :=
    ok.addrB (by show _ < frameBytes + 56 + 36; simp only [oEM1, frameBytes]; omega)
  have hsrc : (P.B + BitVec.ofNat 32 (oEM1 + (P.K - P.ol))).toNat + P.ol ≤ 2 ^ 32 := by
    rw [Proof.X25519.Arm.toNat_add_lt (by rw [BitVec.toNat_ofNat]; simp only [oEM1, frameBytes] at fit ⊢; omega),
      BitVec.toNat_ofNat]
    simp only [oEM1, frameBytes] at fit ⊢; omega
  have ctx := Bignum.Arm.copyCtx_of_regions s (P.B + BitVec.ofNat 32 (oEM1 + (P.K - P.ol))) P.out (n := P.ol)
    (by omega) hsrc hfo
    (by rw [e1]; exact hs.2.inFrR (by show oEM1 + (P.K - P.ol) + P.ol ≤ frameBytes; simp only [oEM1, frameBytes]; omega))
    ⟨P.OUT, by rw [hs.2.wr, ok.wr]; simp, Region.contains_self _ _⟩
    (by rw [e1]; exact ok.stk_fr (R := P.OUT) (.inr (by simp)) (by simp only [oEM1, frameBytes]; omega))
  refine WP.mono (Bignum.Arm.copyBytes_ok s ctx hs.1.ol_pos r1 r0 lr) fun t ht => ?_
  have fr := ht.frame hfo
  have st : P.lay.St σ t := hs.2.write fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.OUT, by simp, fun _ h => h⟩)
    ht.rest.rd ht.rest.wr ht.rest.sp
  refine ⟨⟨⟨hs.1, st⟩, hgl⟩, ?_⟩
  have hb : Spec.Rsa.bytesAt t.mem (State.addr P.out) P.ol = Tail P s.mem := by
    rw [bytesAt_of_read (ht.read hsrc hfo), e1]
    have hd := VG.Proof.RsaPkcs1Sig.bytesAt_drop s.mem (P.lay.fr oEM1) (P.K - P.ol) P.ol
    rw [show P.K - P.ol + P.ol = P.K by omega, Offset.add_ofNat_add_ofNat] at hd
    exact hd.symm
  rw [RO, hb, ht.rest.gpr .r3 (by decide)]
  exact rr

theorem maskArgs_wp {σ s : State} (h : C9 P σ s) : WP isa (.block maskArgs) s (C10 P σ) := by
  obtain ⟨⟨hs, hgl⟩, ro⟩ := h
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  refine wp_mov (op2_imm (by decide)) fun t2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun t3 u3 => ?_
  have s3 : P.lay.St σ t3 := ((hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem).of_rest
    (u2.rest (ws := [.r2]) (by simp)) u2.mem).of_rest (u3.rest (ws := [.r2]) (by simp)) u3.mem
  refine s3.wp_arg (j := 0) (by simp) (by dsimp only; decide) fun t4 s4 u4 => ?_
  refine s4.wp_arg (j := 1) (by simp) (by dsimp only; decide) fun t5 s5 u5 => WP.block_nil ?_
  have mm : t5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have r3 : t5.gpr .r3 = s.gpr .r3 := by
    rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide)]
  refine ⟨⟨⟨hs.1, s5⟩, hgl⟩, by rw [mm, r3]; exact ro, ?_, ?_, ?_⟩
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, dpVal, u2.gpr, u2.other _ (by decide), r3,
      u1.other _ (by decide)]
  · rw [u5.other _ (by decide), u4.gpr]; rfl
  · rw [u5.gpr]; rfl

/-- `out` masked with `0 - r`. -/
theorem masked {o : Option (List Byte)} {r : BitVec 32} {v : List Byte} {m' : Mem} {a : Addr} {n : Nat}
    (h : Rv o r v) (hl : v.length = n)
    (hb : Spec.Rsa.bytesAt m' a n = v.map (· &&& (0 - r).setWidth 8)) : Spec.Rsa.written m' a n r o := by
  unfold Rv at h
  cases o with
  | some y =>
    obtain ⟨rfl, rfl⟩ := h
    have e : ((0 : BitVec 32) - 1).setWidth 8 = BitVec.allOnes 8 := by decide
    rw [e] at hb
    refine ⟨rfl, hb.trans ?_⟩
    exact (List.map_congr_left (g := id) fun x _ => BitVec.and_allOnes).trans (List.map_id _)
  | none =>
    subst h
    have e : ((0 : BitVec 32) - 0).setWidth 8 = 0 := by decide
    rw [e] at hb
    refine ⟨rfl, hb.trans ?_⟩
    apply List.ext_getElem (by simp [hl])
    intro i h₁ h₂
    simp

theorem mask_wp {σ s : State} (h : C10 P σ s) : WP isa Impl.Bignum.Arm.maskBytes s (C11 P σ) := by
  obtain ⟨⟨hs, hgl⟩, ro, r2, r0, lr⟩ := h
  have ok := hs.1.ok
  have hfo := ok.fits P.OUT (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hfo
  have h64 := hs.1.ol64
  refine WP.mono (Bignum.Arm.maskBuffer_ok s (dst := P.out) (n := P.ol) hs.1.ol_pos (by omega)
    hfo ⟨P.OUT, by rw [hs.2.wr, ok.wr]; simp, Region.contains_self _ _⟩ r0 lr) fun t ⟨hb, fr, rst⟩ => ?_
  have st : P.lay.St σ t := hs.2.write fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.OUT, by simp, fun _ h => h⟩) rst.rd rst.wr rst.sp
  refine ⟨⟨⟨hs.1, st⟩, hgl⟩, fun nB hn hp h hh => ?_⟩
  rw [rst.gpr .r3 (by decide)]
  rw [r2] at hb
  exact masked (ro nB hn hp h hh) (bytesAt_length _ _ _) hb

theorem fin_wp {σ s : State} (h : C11 P σ s) : WP isa (.block [.mov .r0 (.reg .r3)]) s (Fin P σ) :=
  wp_mov (op2_reg _ _) fun t u => WP.block_nil ⟨⟨h.1.1.1, h.1.1.2.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem⟩,
    by rw [u.mem, u.gpr]; exact h.2⟩

end VG.Proof.RsaPkcs1Sig.Arm.Rc
