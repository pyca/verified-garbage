module

-- separate module: its proofs (the ends of both paths) build in parallel with `RndInvoke`'s, which `RndVerified` also imports

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.RndScan
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on ARMv7: the ends of the two paths

What the function leaves (`Res`, as the shared contract states it): after
the call, the status `2 - r` and `PS` wiped (`status_wp` … `fin_wp`); with
`PS` not full, `out` zeroed, the drawn octets wiped, and `tape` and the
status for the budget (`zeroArgs_wp` … `request_wp`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Rnd

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Random VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_str wp_cmp op2_imm op2_reg op2_lsr dpVal)

/-! ## The result -/

/-- What the function writes and returns, as the shared contract states it. -/
def Res (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  (∃ req, Spec.Rsa.wordsAt m (State.addr P.tape) 2 =
      [BitVec.ofNat 64 (Spec.RsaPkcs1Enc.padSearch P.pl (randB P σ)).used, BitVec.ofNat 64 req] ∧
    (Spec.RsaPkcs1Enc.padSearch P.pl (randB P σ)).Requests (Spec.RsaPkcs1Enc.padEntropy P.pl) req) ∧
  match (Spec.RsaPkcs1Enc.padSearch P.pl (randB P σ)).outcome with
  | .accepted ps =>
    Spec.Rsa.publicPrecompute P.nB = some P.pw →
      Spec.RsaPkcs1Enc.writtenRandom m (State.addr P.out) P.K r (Spec.RsaPkcs1Enc.encrypt P.nB P.eB (msgB P σ) ps)
  | .entropy .. => r = 0 ∧ Spec.Rsa.bytesAt m (State.addr P.out) P.K = List.replicate P.K 0
  | .exhausted => r = 3 ∧ Spec.Rsa.bytesAt m (State.addr P.out) P.K = List.replicate P.K 0

/-- The end of the body. -/
def Fin (P : EP) (σ s : State) : Prop := S P σ s ∧ Res P σ s.mem (s.gpr .r0)

theorem written_random {m : Mem} {out : Addr} {k : Nat} {r : BitVec 32} {res : Option (List Byte)}
    (h : Spec.Rsa.written m out k r res) : Spec.RsaPkcs1Enc.writtenRandom m out k (2 - r) res := by
  cases res with
  | some C => obtain ⟨h1, h2⟩ := h; subst h1; exact ⟨rfl, h2⟩
  | none => obtain ⟨h1, h2⟩ := h; subst h1; exact ⟨rfl, h2⟩

theorem written_mem {m m' : Mem} {out : Addr} {k : Nat} {r : BitVec 32} {res : Option (List Byte)}
    (h : Spec.Rsa.written m out k r res) (hb : Spec.Rsa.bytesAt m' out k = Spec.Rsa.bytesAt m out k) :
    Spec.Rsa.written m' out k r res := by
  cases res with
  | some C => exact ⟨h.1, hb.trans h.2⟩
  | none => exact ⟨h.1, hb.trans h.2⟩

theorem map_and_zero (l : List Byte) : l.map (· &&& (0 : BitVec 32).setWidth 8) = List.replicate l.length 0 := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp

/-- `min` without a branch, for values below `2 ^ 31`. -/
theorem shr31 {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    (BitVec.ofNat 32 b - BitVec.ofNat 32 a) >>> 31 = if a ≤ b then 0 else 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [Proof.X25519.Arm.toNat_shr, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (a := b) (by omega)]
  split
  · rename_i h
    show _ = 0
    rw [show 2 ^ 32 - a + b = (b - a) + 2 ^ 32 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    exact Nat.div_eq_of_lt (by omega)
  · rename_i h
    show _ = 1
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

theorem minSel {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    ((BitVec.ofNat 32 a - BitVec.ofNat 32 b) &&& ((BitVec.ofNat 32 b - BitVec.ofNat 32 a) >>> 31 - 1)) +
      BitVec.ofNat 32 b = BitVec.ofNat 32 (min a b) := by
  rw [shr31 ha hb]
  split
  · rename_i h
    rw [show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes, BitVec.sub_add_cancel,
      Nat.min_eq_left h]
  · rename_i h
    rw [show (1 : BitVec 32) - 1 = 0 by decide,
      show (BitVec.ofNat 32 a - BitVec.ofNat 32 b &&& 0) = 0 from BitVec.and_zero,
      show (0 : BitVec 32) + BitVec.ofNat 32 b = BitVec.ofNat 32 b from BitVec.zero_add _,
      Nat.min_eq_right (by omega)]

variable {P : EP}

section

variable {σ s : State}

theorem S.out_fit (hs : S P σ s) : P.out.toNat + P.K ≤ 2 ^ 32 := by
  have := hs.1.ok.fits P.OUT (by simp)
  simpa [Proof.X25519.Arm.addr_toNat] using this

theorem S.e40 (hs : S P σ s) : State.addr (P.B + BitVec.ofNat 32 oBuf) = P.lay.fr oBuf :=
  hs.2.ok.addrB (by show oBuf < frameBytes + 56 + 44; decide)

theorem S.bufFit (hs : S P σ s) {n : Nat} (hn : oBuf + n ≤ frameBytes) :
    (P.B + BitVec.ofNat 32 oBuf).toNat + n ≤ 2 ^ 32 := by
  have fit := hs.2.ok.fit
  rw [Proof.X25519.Arm.toNat_add_lt (by simp only [oBuf, frameBytes] at fit ⊢; rw [BitVec.toNat_ofNat]; omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]
  simp only [oBuf, frameBytes] at fit hn ⊢; omega

/-- `out` apart from the frame. -/
theorem S.outFr (hs : S P σ s) {d n : Nat} (hd : d + n ≤ frameBytes) :
    Region.Disjoint ⟨P.lay.fr d, n⟩ P.OUT :=
  hs.2.ok.stk_fr (.inr (by simp)) (by show d + n ≤ frameBytes + 56; omega)

theorem S.outBytesFr {t : State} (hs : S P σ s) {d n : Nat} (hd : d + n ≤ frameBytes)
    (hf : Frame [⟨P.lay.fr d, n⟩] s.mem t.mem) :
    Spec.Rsa.bytesAt t.mem (State.addr P.out) P.K = Spec.Rsa.bytesAt s.mem (State.addr P.out) P.K :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hs.outFr hd).symm)
    (by have := hs.1.k1024; omega)

end

/-! ## After the call -/

/-- The status in `r4`. -/
def D1 (P : EP) (σ s : State) : Prop := K1 P σ s ∧ ∃ rc, CR P σ s.mem rc ∧ s.gpr .r4 = 2 - rc

/-- Before the wipe of `PS`. -/
def D2 (P : EP) (σ s : State) : Prop :=
  D1 P σ s ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 oBuf ∧ s.gpr .lr = BitVec.ofNat 32 P.pl ∧ s.gpr .r2 = 0

/-- `PS` wiped. -/
def D3 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ cnt P σ (N P) = P.pl ∧ TapeW P s.mem (BitVec.ofNat 32 (N P)) 0 ∧
    ∃ rc, CR P σ s.mem rc ∧ s.gpr .r4 = 2 - rc

section

variable {σ s : State}

theorem K1.of_rest {ws : List Reg} {t : State} (h : K1 P σ s) (r : Rest ws s t) (m : t.mem = s.mem) : K1 P σ t :=
  ⟨⟨h.1.1, h.1.2.of_rest r m⟩, h.2.1, fun j hj => by rw [m]; exact h.2.2.1 j hj, by rw [m]; exact h.2.2.2⟩

theorem status_wp (h : C3 P σ s) : WP isa (.block status) s (D1 P σ) := by
  refine wp_mov (op2_imm (by decide)) fun t1 u1 => ?_
  refine wp_dp (op2_reg _ _) fun t2 u2 => WP.block_nil ⟨(h.1.of_rest (u1.rest (ws := [.r4]) (by simp)) u1.mem).of_rest
    (u2.rest (ws := [.r4]) (by simp)) u2.mem, s.gpr .r0, by rw [u2.mem, u1.mem]; exact h.2, ?_⟩
  rw [u2.gpr, dpVal, u1.gpr, u1.other _ (by decide)]

theorem wipeArgs_wp (h : D1 P σ s) : WP isa (.block wipeArgs) s (D2 P σ) := by
  obtain ⟨k1, rc, cr, r4⟩ := h
  have hs := k1.1
  have hK := hs.1.k1024
  have hml := hs.1.mlK
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  refine wp_dp (op2_imm (by decide)) fun t2 u2 => ?_
  have s2 : P.lay.St σ t2 := (hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem).of_rest
    (u2.rest (ws := [.r0]) (by simp)) u2.mem
  refine s2.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t3 s3 u3 => ?_
  refine s3.wp_arg (j := 8) (by simp) (by dsimp only; decide) fun t4 s4 u4 => ?_
  refine wp_dp (op2_reg _ _) fun t5 u5 => ?_
  refine wp_dp (op2_imm (by decide)) fun t6 u6 => ?_
  refine wp_mov (op2_imm (by decide)) fun t7 u7 => WP.block_nil ⟨⟨⟨⟨hs.1, ?_⟩, k1.2.1, ?_, ?_⟩, rc, ?_, ?_⟩, ?_, ?_,
    u7.gpr⟩
  · exact ((s4.of_rest (u5.rest (ws := [.lr]) (by simp)) u5.mem).of_rest (u6.rest (ws := [.lr]) (by simp))
      u6.mem).of_rest (u7.rest (ws := [.r2]) (by simp)) u7.mem
  · intro j hj
    rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]; exact k1.2.2.1 j hj
  · rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]; exact k1.2.2.2
  · rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]; exact cr
  · rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), r4]
  · rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.gpr, dpVal, u1.gpr, hs.2.sp, BitVec.add_zero]
  · rw [u7.other _ (by decide), u6.gpr, dpVal, u5.gpr, dpVal, u4.other _ (by decide), u3.gpr, u4.gpr]
    exact sub3 hml hK

theorem wipe_wp (h : D2 P σ s) : WP isa Impl.Bignum.Arm.maskBytes s (D3 P σ) := by
  obtain ⟨⟨k1, rc, cr, r4⟩, r0, lr, -⟩ := h
  have hs := k1.1
  have hpl := hs.1.pl_le
  have h8 := hs.1.pl8
  have hF : oBuf + P.pl ≤ frameBytes := by simp only [oBuf, frameBytes]; omega
  refine WP.mono (Bignum.Arm.maskBuffer_ok s (dst := P.B + BitVec.ofNat 32 oBuf) (n := P.pl) (by omega) (by omega)
    (hs.bufFit hF) (by rw [hs.e40]; exact hs.2.inFr hF) r0 lr) fun t ⟨_, fr, rest⟩ => ?_
  rw [hs.e40] at fr
  have st : P.lay.St σ t := hs.2.frameW hF fr rest.rd rest.wr rest.sp
  refine ⟨⟨hs.1, st⟩, k1.2.1, k1.2.2.2.frame fr fun r hr => ?_, rc, fun hq => written_mem (cr hq) (hs.outBytesFr hF fr),
    by rw [rest.gpr .r4 (by decide), r4]⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact hs.1.tapeFr (by simp only [oBuf, frameBytes] at hF ⊢; omega)

/-- With `PS` full: the outcome. -/
theorem In.accepted (h : In P σ) (hc : cnt P σ (N P) = P.pl) :
    (Spec.RsaPkcs1Enc.padSearch P.pl (randB P σ)).outcome = .accepted (kept P σ (N P)) ∧
      (Spec.RsaPkcs1Enc.padSearch P.pl (randB P σ)).used = N P :=
  VG.Proof.RsaPkcs1Enc.padSearch_accepted (accept_of h hc)

theorem fin_wp (h : D3 P σ s) : WP isa (.block [.mov .r0 (.reg .r4)]) s (Fin P σ) := by
  obtain ⟨hs, hf, tw, rc, cr, r4⟩ := h
  have hN := hs.1.N_le
  have hrl := hs.1.rl_le
  have hpl := hs.1.pl_le
  obtain ⟨ho, hu⟩ := hs.1.accepted hf
  refine wp_mov (op2_reg _ _) fun t u => WP.block_nil ⟨⟨hs.1, hs.2.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem⟩,
    ⟨0, ?_, ?_⟩, ?_⟩
  · rw [u.mem, hu]; exact wordsAt_tape (by omega) (by decide) tw
  · simp only [Spec.Entropy.Result.Requests, ho]
  · rw [ho, u.mem, u.gpr, r4]
    exact fun hq => written_random (cr hq)

end

/-! ## Without `PS` full -/

/-- The scan ended without `PS` full. -/
def RJ (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ cnt P σ (N P) ≠ P.pl ∧ s.gpr .r3 = BitVec.ofNat 32 P.pl ∧
    s.gpr .r5 = BitVec.ofNat 32 (cnt P σ (N P)) ∧ s.gpr .r8 = BitVec.ofNat 32 P.rl

/-- `out` zeroed. -/
abbrev Zout (P : EP) (s : State) : Prop :=
  Spec.Rsa.bytesAt s.mem (State.addr P.out) P.K = List.replicate P.K 0

/-- Before zeroing `out`. -/
def R1 (P : EP) (σ s : State) : Prop :=
  RJ P σ s ∧ s.gpr .r0 = P.out ∧ s.gpr .lr = BitVec.ofNat 32 P.K ∧ s.gpr .r2 = 0

/-- `out` zeroed, the mask still 0. -/
def R2 (P : EP) (σ s : State) : Prop := RJ P σ s ∧ Zout P s ∧ s.gpr .r2 = 0

/-- Before wiping the drawn octets. -/
def R2d (P : EP) (σ s : State) : Prop :=
  R2 P σ s ∧ 0 < cnt P σ (N P) ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 oBuf ∧
    s.gpr .lr = BitVec.ofNat 32 (cnt P σ (N P))

/-- With `tape` in `r7`. -/
def R4 (P : EP) (σ s : State) : Prop := R2 P σ s ∧ s.gpr .r7 = P.tape

/-- With the budget in `r6` and whether `rand_len` is it in Z. -/
def R5 (P : EP) (σ s : State) : Prop :=
  R4 P σ s ∧ s.gpr .r6 = BitVec.ofNat 32 (P.pl + 128) ∧ s.z = decide (P.rl = P.pl + 128)

section

variable {σ s : State}

theorem RJ.of_rest {ws : List Reg} {t : State} (h : RJ P σ s) (r : Rest ws s t)
    (h3 : Reg.r3 ∉ ws) (h5 : Reg.r5 ∉ ws) (h8 : Reg.r8 ∉ ws) (m : P.lay.St σ t) : RJ P σ t :=
  ⟨⟨h.1.1, m⟩, h.2.1, by rw [r.gpr _ h3]; exact h.2.2.1, by rw [r.gpr _ h5]; exact h.2.2.2.1,
    by rw [r.gpr _ h8]; exact h.2.2.2.2⟩

theorem rj_of (h : Done P σ s) (hc : cnt P σ (N P) ≠ P.pl) : RJ P σ s := ⟨h.st, hc, h.r3, h.r5, h.r8⟩

theorem zeroArgs_wp (h : RJ P σ s) : WP isa (.block zeroArgs) s (R1 P σ) := by
  have hs := h.1
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_arg (j := 0) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine s2.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t3 s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun t4 u4 => WP.block_nil ⟨?_, ?_, ?_, u4.gpr⟩
  · exact h.of_rest (((((u1.rest (ws := [.r12, .r0, .lr, .r2]) (by simp))).trans (u2.rest (by simp))).trans
      (u3.rest (by simp))).trans (u4.rest (by simp))) (by decide) (by decide) (by decide)
      (s3.of_rest (u4.rest (ws := [.r2]) (by simp)) u4.mem)
  · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr]; rfl
  · rw [u4.other _ (by decide), u3.gpr]; rfl

theorem zeroOut_wp (h : R1 P σ s) : WP isa Impl.Bignum.Arm.maskBytes s (R2 P σ) := by
  obtain ⟨rj, r0, lr, r2⟩ := h
  have hs := rj.1
  have ok := hs.1.ok
  have hK := hs.1.k64
  have hK' := hs.1.k1024
  refine WP.mono (Bignum.Arm.maskBuffer_ok s (dst := P.out) (n := P.K) (by omega) (by omega)
    hs.out_fit ⟨P.OUT, by rw [hs.2.wr, ok.wr]; simp, Region.contains_self _ _⟩ r0 lr) fun t ⟨hb, fr, rest⟩ => ?_
  have st : P.lay.St σ t := hs.2.write fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨P.OUT, by simp, fun _ h => h⟩) rest.rd rest.wr rest.sp
  refine ⟨rj.of_rest rest (by decide) (by decide) (by decide) st, ?_, by rw [rest.gpr .r2 (by decide), r2]⟩
  show Spec.Rsa.bytesAt t.mem (State.addr P.out) P.K = _
  rw [hb, r2, map_and_zero, bytesAt_length]

theorem cmp50_wp (h : R2 P σ s) :
    WP isa (.block [.cmp .r5 (.imm 0)]) s fun t => R2 P σ t ∧ t.z = decide (cnt P σ (N P) = 0) := by
  have hc := h.1.1.1.pl_le
  have hN : cnt P σ (N P) ≤ P.pl := by
    have := reject_of h.1.1.1 h.1.2.1; omega
  refine wp_cmp (op2_imm (by decide)) fun t u z => WP.block_nil ⟨⟨h.1.of_rest (u.rest []) (by simp) (by simp)
    (by simp) (h.1.1.2.of_rest (u.rest []) u.mem), by rw [Zout, u.mem]; exact h.2.1, by rw [u.gpr]; exact h.2.2⟩, ?_⟩
  rw [z, h.1.2.2.2.1, show BitVec.ofNat 32 (cnt P σ (N P)) - 0 = BitVec.ofNat 32 (cnt P σ (N P)) from
    BitVec.sub_zero _, Proof.X25519.Arm.ofNat_beq_zero (by omega)]

theorem drawnArgs_wp (h : R2 P σ s) (hc : cnt P σ (N P) ≠ 0) :
    WP isa (.block [.addSp .r12 0, .dp .add .r0 .r12 (.imm (BitVec.ofNat 32 oBuf)), .mov .lr (.reg .r5)]) s
      (R2d P σ) := by
  obtain ⟨rj, z, r2⟩ := h
  have hs := rj.1
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  refine wp_dp (op2_imm (by decide)) fun t2 u2 => ?_
  refine wp_mov (op2_reg _ _) fun t3 u3 => WP.block_nil ⟨⟨?_, ?_, ?_⟩, Nat.pos_of_ne_zero hc, ?_, ?_⟩
  · have r := ((u1.rest (ws := [.r12, .r0, .lr]) (by simp)).trans (u2.rest (by simp))).trans (u3.rest (by simp))
    exact rj.of_rest r (by decide) (by decide) (by decide) (((hs.2.of_rest (u1.rest (ws := [.r12]) (by simp))
      u1.mem).of_rest (u2.rest (ws := [.r0]) (by simp)) u2.mem).of_rest (u3.rest (ws := [.lr]) (by simp)) u3.mem)
  · rw [Zout, u3.mem, u2.mem, u1.mem]; exact z
  · rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), r2]
  · rw [u3.other _ (by decide), u2.gpr, dpVal, u1.gpr, hs.2.sp, BitVec.add_zero]
  · rw [u3.gpr, u2.other _ (by decide), u1.other _ (by decide), rj.2.2.2.1]

theorem drawn_wp (h : R2d P σ s) : WP isa Impl.Bignum.Arm.maskBytes s (R2 P σ) := by
  obtain ⟨⟨rj, z, r2⟩, hpos, r0, lr⟩ := h
  have hs := rj.1
  have hpl := hs.1.pl_le
  have hN : cnt P σ (N P) < P.pl := (reject_of hs.1 rj.2.1).2.2
  have hF : oBuf + cnt P σ (N P) ≤ frameBytes := by simp only [oBuf, frameBytes]; omega
  refine WP.mono (Bignum.Arm.maskBuffer_ok s (dst := P.B + BitVec.ofNat 32 oBuf) (n := cnt P σ (N P)) hpos
    (by omega) (hs.bufFit hF) (by rw [hs.e40]; exact hs.2.inFr hF) r0 lr) fun t ⟨_, fr, rest⟩ => ?_
  rw [hs.e40] at fr
  have st : P.lay.St σ t := hs.2.frameW hF fr rest.rd rest.wr rest.sp
  exact ⟨rj.of_rest rest (by decide) (by decide) (by decide) st, by rw [Zout, hs.outBytesFr hF fr]; exact z,
    by rw [rest.gpr .r2 (by decide), r2]⟩

theorem tapeLoad'_wp (h : R2 P σ s) : WP isa (.block tapeLoad) s (R4 P σ) :=
  h.1.1.2.wp_arg (j := 2) (by simp) (by dsimp only; decide) fun t st u => WP.block_nil
    ⟨⟨h.1.of_rest (u.rest (ws := [.r7]) (by simp)) (by decide) (by decide) (by decide) st,
      by rw [Zout, u.mem]; exact h.2.1, by rw [u.other _ (by decide)]; exact h.2.2⟩, u.gpr⟩

theorem budget_wp (h : R4 P σ s) : WP isa (.block budget) s (R5 P σ) := by
  have hpl := h.1.1.1.1.pl_le
  have hrl := h.1.1.1.1.rl_le
  refine wp_dp (op2_imm (by decide)) fun t1 u1 => ?_
  refine wp_cmp (op2_reg _ _) fun t2 u2 z2 => WP.block_nil ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · exact h.1.1.of_rest ((u1.rest (ws := [.r6]) (by simp)).trans (u2.rest _)) (by decide) (by decide) (by decide)
      ((h.1.1.1.2.of_rest (u1.rest (ws := [.r6]) (by simp)) u1.mem).of_rest (u2.rest []) u2.mem)
  · rw [Zout, u2.mem, u1.mem]; exact h.1.2.1
  · rw [u2.gpr, u1.other _ (by decide)]; exact h.1.2.2
  · rw [u2.gpr, u1.other _ (by decide)]; exact h.2
  · rw [u2.gpr, u1.gpr, dpVal, h.1.1.2.2.1]
    apply BitVec.eq_of_toNat_eq
    have e : (128 : BitVec 32).toNat = 128 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, e]
    omega
  · rw [z2, u1.other _ (by decide), h.1.1.2.2.2.2, u1.gpr, dpVal, h.1.1.2.2.1]
    rw [show BitVec.ofNat 32 P.pl + 128 = BitVec.ofNat 32 (P.pl + 128) by
      apply BitVec.eq_of_toNat_eq
      have e : (128 : BitVec 32).toNat = 128 := rfl
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, e]
      omega, ofNat_sub_beq (by omega) (by omega)]

end

end VG.Proof.RsaPkcs1Enc.Arm.Rnd


namespace VG.Proof.RsaPkcs1Enc.Arm.Rnd

/-! ## The budget

Without `PS` full: with `rand_len` the budget, status 3 and `tape` is
`[rand_len, 0]` (`exhausted_wp`); otherwise status 0 and `tape` is
`[0, min(cap, psLen + rand_len - c)]` (`request_wp`).
-/

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Random VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_str wp_cmp op2_imm op2_reg op2_lsr dpVal)

variable {P : EP} {σ s : State}

theorem tape_frame {m : Mem} {a b c d : BitVec 32} (hs : S P σ s)
    (hm : m = (((s.mem.writeW (State.addr P.tape + BitVec.ofNat 64 0) (a : BitVec 32)).writeW
      (State.addr P.tape + BitVec.ofNat 64 4) (b : BitVec 32)).writeW (State.addr P.tape + BitVec.ofNat 64 8)
      (c : BitVec 32)).writeW (State.addr P.tape + BitVec.ofNat 64 12) (d : BitVec 32)) :
    Spec.Rsa.bytesAt m (State.addr P.out) P.K = Spec.Rsa.bytesAt s.mem (State.addr P.out) P.K := by
  have fr : Frame [P.TAPE] s.mem m := by
    rw [hm]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by decide) (by decide))
  exact bytesAt_frame fr (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.1.dOT)
    (by have := hs.1.k1024; omega)

theorem In.rejected (h : In P σ) (hc : cnt P σ (N P) ≠ P.pl) :
    (VG.Proof.RsaPkcs1Enc.nz (randB P σ)).length < P.pl := (reject_of h hc).1

theorem exhausted_wp (h : R5 P σ s) (he : P.rl = P.pl + 128) : WP isa (.block exhausted) s (Fin P σ) := by
  obtain ⟨⟨⟨rj, z, -⟩, r7⟩, -, -⟩ := h
  have hs := rj.1
  have hrl := hs.1.rl_le
  have hpl := hs.1.pl_le
  obtain ⟨ho, hu⟩ := VG.Proof.RsaPkcs1Enc.padSearch_exhausted (hs.1.rejected rj.2.1)
    (n := P.pl) (rand := randB P σ) (by rw [randB_length]; simp only [Spec.RsaPkcs1Enc.padEntropy]; omega)
  refine wp_mov (op2_imm (by decide)) fun t1 u1 => ?_
  have s1 : S P σ t1 := ⟨hs.1, hs.2.of_rest (u1.rest (ws := [.r9]) (by simp)) u1.mem⟩
  have g1 : ∀ r, r ≠ .r9 → t1.gpr r = s.gpr r := u1.other
  refine wp_strT s1 (by rw [g1 _ (by decide), r7]) (d := 0) (by decide) fun t2 s2 m2 => ?_
  refine wp_strT s2 (by rw [m2.gpr, g1 _ (by decide), r7]) (d := 4) (by decide) fun t3 s3 m3 => ?_
  refine wp_strT s3 (by rw [m3.gpr, m2.gpr, g1 _ (by decide), r7]) (d := 8) (by decide) fun t4 s4 m4 => ?_
  refine wp_strT s4 (by rw [m4.gpr, m3.gpr, m2.gpr, g1 _ (by decide), r7]) (d := 12) (by decide)
    fun t5 s5 m5 => ?_
  refine wp_mov (op2_imm (by decide)) fun t6 u6 => WP.block_nil ⟨⟨hs.1, s5.2.of_rest (u6.rest (ws := [.r0])
    (by simp)) u6.mem⟩, ⟨0, ?_, ?_⟩, ?_⟩
  · have e := tape4 s.mem (State.addr P.tape) (s.gpr .r8) 0 0 0
    have v9 : t1.gpr .r9 = 0 := u1.gpr
    rw [u6.mem, m5.mem, m4.mem, m3.mem, m2.mem, u1.mem, m4.gpr, m3.gpr, m2.gpr, v9, g1 _ (by decide), hu,
      randB_length]
    obtain ⟨e0, e1, e2, e3⟩ := e
    exact wordsAt_tape (by omega) (by decide) ⟨e0.trans rj.2.2.2.2, e1, e2, e3⟩
  · simp only [Spec.Entropy.Result.Requests, ho]
  · rw [ho]
    refine ⟨u6.gpr, ?_⟩
    rw [u6.mem, tape_frame hs (by rw [m5.mem, m4.mem, m3.mem, m2.mem, u1.mem])]
    exact z

theorem ofNat_add_sub {a b c : Nat} (hc : c ≤ a) (ha : a + b < 2 ^ 32) :
    BitVec.ofNat 32 a + BitVec.ofNat 32 b - BitVec.ofNat 32 c = BitVec.ofNat 32 (a + b - c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem request_wp (h : R5 P σ s) (he : P.rl ≠ P.pl + 128) : WP isa (.block request) s (Fin P σ) := by
  obtain ⟨⟨⟨rj, z, -⟩, r7⟩, r6, -⟩ := h
  have hs := rj.1
  have hrl := hs.1.rl_le
  have hpl := hs.1.pl_le
  have hc := (reject_of hs.1 rj.2.1).2.2
  obtain ⟨ho, hu⟩ := VG.Proof.RsaPkcs1Enc.padSearch_entropy (hs.1.rejected rj.2.1)
    (n := P.pl) (rand := randB P σ) (by rw [randB_length]; simp only [Spec.RsaPkcs1Enc.padEntropy]; omega)
  have r3 := rj.2.2.1
  have r5 := rj.2.2.2.1
  have r8 := rj.2.2.2.2
  refine wp_dp (op2_reg _ _) fun t1 u1 => ?_
  refine wp_dp (op2_reg _ _) fun t2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun t3 u3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun t5 u5 => ?_
  refine wp_dp (op2_reg _ _) fun t6 u6 => ?_
  refine wp_dp (op2_reg _ _) fun t7 u7 => ?_
  refine wp_dp (op2_reg _ _) fun t8 u8 => ?_
  refine wp_mov (op2_imm (by decide)) fun t9 u9 => ?_
  have r := (((((((((u1.rest (ws := [.r9, .r10, .r11]) (by simp)).trans (u2.rest (by simp))).trans
    (u3.rest (by simp))).trans (u4.rest (by simp))).trans (u5.rest (by simp))).trans (u6.rest (by simp))).trans
    (u7.rest (by simp))).trans (u8.rest (by simp))).trans (u9.rest (by simp)))
  have m9 : t9.mem = s.mem := by
    rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have s9 : S P σ t9 := ⟨hs.1, hs.2.of_rest r m9⟩
  have q9 : t9.gpr .r9 = BitVec.ofNat 32 (P.pl + P.rl - cnt P σ (N P)) := by
    rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr, dpVal, u1.gpr, dpVal,
      u1.other _ (by decide), r3, r8, r5]
    exact ofNat_add_sub (by omega) (by omega)
  have v2 : t2.gpr .r9 = BitVec.ofNat 32 (P.pl + P.rl - cnt P σ (N P)) := by
    rw [u2.gpr, dpVal, u1.gpr, dpVal, u1.other _ (by decide), r3, r8, r5]
    exact ofNat_add_sub (by omega) (by omega)
  have c2 : t2.gpr .r6 = BitVec.ofNat 32 (P.pl + 128) := by rw [u2.other _ (by decide), u1.other _ (by decide), r6]
  have c5 : t5.gpr .r6 = BitVec.ofNat 32 (P.pl + 128) := by
    rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), c2]
  have c7 : t7.gpr .r6 = BitVec.ofNat 32 (P.pl + 128) := by
    rw [u7.other _ (by decide), u6.other _ (by decide), c5]
  have v5 : t5.gpr .r10 = (BitVec.ofNat 32 (P.pl + 128) - BitVec.ofNat 32 (P.pl + P.rl - cnt P σ (N P))) >>> 31 - 1 := by
    rw [u5.gpr, dpVal, u4.gpr, u3.gpr, dpVal, c2, v2]
  have v6 : t6.gpr .r11 = BitVec.ofNat 32 (P.pl + P.rl - cnt P σ (N P)) - BitVec.ofNat 32 (P.pl + 128) := by
    rw [u6.gpr, dpVal, u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), v2, c5]
  have q11 : t9.gpr .r11 = BitVec.ofNat 32 (min (P.pl + P.rl - cnt P σ (N P)) (P.pl + 128)) := by
    rw [u9.other _ (by decide), u8.gpr, dpVal, u7.gpr, dpVal, v6, u6.other _ (by decide), v5, c7]
    exact minSel (by omega) (by omega)
  have q10 : t9.gpr .r10 = 0 := u9.gpr
  have g9 : ∀ x : Reg, x ∉ [Reg.r9, .r10, .r11] → t9.gpr x = s.gpr x := r.gpr
  refine wp_strT s9 (by rw [g9 _ (by decide), r7]) (d := 0) (by decide) fun ta sa ma => ?_
  refine wp_strT sa (by rw [ma.gpr, g9 _ (by decide), r7]) (d := 4) (by decide) fun tb sb mb => ?_
  refine wp_strT sb (by rw [mb.gpr, ma.gpr, g9 _ (by decide), r7]) (d := 8) (by decide) fun tc sc mc => ?_
  refine wp_strT sc (by rw [mc.gpr, mb.gpr, ma.gpr, g9 _ (by decide), r7]) (d := 12) (by decide)
    fun td sd md => ?_
  refine wp_mov (op2_imm (by decide)) fun te ue => WP.block_nil ⟨⟨hs.1, sd.2.of_rest (ue.rest (ws := [.r0])
    (by simp)) ue.mem⟩, ⟨min (P.pl + P.rl - cnt P σ (N P)) (P.pl + 128), ?_, ?_⟩, ?_⟩
  · have e := tape4 t9.mem (State.addr P.tape) 0 0 (t9.gpr .r11) 0
    rw [ue.mem, md.mem, mc.mem, mb.mem, ma.mem, mc.gpr, mb.gpr, ma.gpr, q10, hu]
    obtain ⟨e0, e1, e2, e3⟩ := e
    exact wordsAt_tape (by decide) (by omega) ⟨e0, e1, e2.trans q11, e3⟩
  · simp only [Spec.Entropy.Result.Requests, ho, Spec.Entropy.RequestValid, randB_length,
      Spec.RsaPkcs1Enc.padEntropy]
    omega
  · rw [ho]
    refine ⟨ue.gpr, ?_⟩
    rw [ue.mem, tape_frame hs (by rw [md.mem, mc.mem, mb.mem, ma.mem, mc.gpr, mb.gpr, ma.gpr, m9])]
    exact z

end VG.Proof.RsaPkcs1Enc.Arm.Rnd
