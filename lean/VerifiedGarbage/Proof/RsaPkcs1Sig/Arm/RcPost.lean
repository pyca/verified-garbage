module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.RcCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.VfPost
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Bignum.Arm.CompareBuffer
import VerifiedGarbage.Proof.Rsa.Arm.PrivMask
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rsa.ZeroTest32

/-!
# RSASSA-PKCS1-v1_5 recovery with a precomputed public key on ARMv7: the encoding and the comparison

The status to its word and the encoding of the last `out_len` bytes of
`EM₁` to `EM₂` (`encArgs_wp`, `encode_wp`), the comparison of `EM₁` and
`EM₂` (`cmpArgs_wp`, `compare_wp`) and the result (`result_wp`, from
`recover_result`), as in verification (`Proof/RsaPkcs1Sig/Arm/VfPost.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Rc

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.RecoverPrecomputed
open VG.Impl.RsaPkcs1Sig.Arm.Precomputed (frameBytes oSt oOk oEM1 oEM2 ret0)
open VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.RsaPkcs1Sig.Arm.Vf (EncR EncR.congr written_congr and_zero' zero_and')
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp op2_imm op2_reg op2_lsr dpVal)

variable {P : EP}

/-! ## The result -/

/-- What the result and the value are: the value is the last `out_len`
bytes of `EM₁`, and the result is 1 exactly when there is one. -/
def Rv (o : Option (List Byte)) (r : BitVec 32) (v : List Byte) : Prop :=
  match o with
  | some y => r = 1 ∧ v = y
  | none => r = 0

theorem recover_result {nB eB sig : List Byte} {h : Spec.RsaPkcs1Sig.Hash} {id K ol : Nat} {m : Mem}
    {a₁ a₂ : Addr} {rc ok : BitVec 32} {eq : Bool} (hn : nB.length = K) (hs : sig.length = K)
    (hh : Spec.RsaPkcs1Sig.Hash.ofId id = some h) (hol : ol = h.len)
    (w : Spec.Rsa.written m a₁ K rc (Spec.Rsa.publicOpChecked nB eB sig))
    (e : EncR id ((Spec.Rsa.bytesAt m a₁ K).drop (K - ol)) K m a₂ ok)
    (he : eq = true ↔ Spec.Rsa.bytesAt m a₁ K = Spec.Rsa.bytesAt m a₂ K) :
    Rv (recoverEnc nB eB h sig) (rc &&& ok &&& BitVec.ofNat 32 eq.toNat)
      ((Spec.Rsa.bytesAt m a₁ K).drop (K - ol)) := by
  unfold recoverEnc
  rw [ite_eq_left (hs.trans hn.symm), hn, ← hol]
  unfold EncR encOut at e
  simp only [hh] at e
  cases hp : Spec.Rsa.publicOpChecked nB eB sig with
  | none =>
    rw [hp] at w
    show _ = _
    rw [w.1, zero_and', zero_and']
  | some y =>
    rw [hp] at w
    simp only
    rw [w.2] at e ⊢
    cases hE : Spec.RsaPkcs1Sig.encode h (y.drop (K - ol)) K with
    | none =>
      simp only [hE] at e
      simp only [reduceCtorEq, ↓reduceIte]
      show _ = _
      rw [e, and_zero', zero_and']
    | some em =>
      simp only [hE] at e
      rw [w.1, e.1]
      have h11 : (1 : BitVec 32) &&& 1 = 1 := by decide
      rw [h11]
      by_cases hy : em = y
      · subst hy
        have heq : eq = true := he.2 (w.2.trans e.2.symm)
        simp only [↓reduceIte]
        rw [heq]
        exact ⟨rfl, rfl⟩
      · have heq : eq = false := by
          cases eq
          · rfl
          · exact absurd (((he.1 rfl).symm.trans w.2).symm.trans e.2).symm hy
        simp only [Option.some.injEq, hy, ↓reduceIte]
        show _ = _
        rw [heq]; rfl

/-! ## The stages -/

/-- A word of the frame kept. -/
abbrev Slot (P : EP) (m : Mem) (d : Nat) (v : BitVec 32) : Prop := m.readW (P.lay.fr d) 32 = v

/-- The last `out_len` bytes of `EM₁`. -/
abbrev Tail (P : EP) (m : Mem) : List Byte := (Spec.Rsa.bytesAt m (P.lay.fr oEM1) P.K).drop (P.K - P.ol)

/-- The encoding of the last `out_len` bytes of `EM₁`. -/
abbrev ER (P : EP) (m : Mem) (ok : BitVec 32) : Prop := EncR P.hash.toNat (Tail P m) P.K m (P.lay.fr oEM2) ok

/-- The status in its word. -/
def St1 (P : EP) (σ : State) (m : Mem) : Prop := ∃ rc, CR P σ m rc ∧ Slot P m oSt rc

/-- The encoding's success in its word. -/
def Ok1 (P : EP) (m : Mem) : Prop := ∃ ok, ER P m ok ∧ Slot P m oOk ok

/-- Before `encode`. -/
def C3 (P : EP) (σ s : State) : Prop :=
  C0 P σ s ∧ St1 P σ s.mem ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 oEM2 ∧
    s.gpr .r1 = P.B + BitVec.ofNat 32 (oEM1 + (P.K - P.ol)) ∧ s.gpr .r2 = P.hash ∧
    s.gpr .r3 = BitVec.ofNat 32 P.K ∧ s.gpr .lr = BitVec.ofNat 32 P.ol

/-- After `encode`. -/
def C4 (P : EP) (σ s : State) : Prop := C0 P σ s ∧ St1 P σ s.mem ∧ ER P s.mem (s.gpr .r3)

/-- Before the comparison. -/
def C5 (P : EP) (σ s : State) : Prop :=
  C0 P σ s ∧ St1 P σ s.mem ∧ Ok1 P s.mem ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 oEM1 ∧
    s.gpr .r1 = P.B + BitVec.ofNat 32 oEM2 ∧ s.gpr .lr = BitVec.ofNat 32 P.K ∧ s.gpr .r2 = 0

/-- After the comparison. -/
def C6 (P : EP) (σ s : State) : Prop :=
  C0 P σ s ∧ St1 P σ s.mem ∧ Ok1 P s.mem ∧
    (s.gpr .r2 = 0 ↔ Spec.Rsa.bytesAt s.mem (P.lay.fr oEM1) P.K = Spec.Rsa.bytesAt s.mem (P.lay.fr oEM2) P.K)

/-- The result and the value, for every modulus whose precomputed values are
`pre`'s and the hash function `hash` names. -/
def RR (P : EP) (σ : State) (r : BitVec 32) (v : List Byte) : Prop :=
  ∀ nB : List Byte, nB.length = P.K → Spec.Rsa.publicPrecompute nB = some P.pw →
    ∀ h, Spec.RsaPkcs1Sig.Hash.ofId P.hash.toNat = some h → Rv (recoverEnc nB P.eB h (sigB P σ)) r v

/-- After the result. -/
def C7 (P : EP) (σ s : State) : Prop := C0 P σ s ∧ RR P σ (s.gpr .r3) (Tail P s.mem)

/-! ## Memory kept -/

theorem slot_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨P.lay.fr d, 4⟩ r) : m'.readW (P.lay.fr d) 32 = m.readW (P.lay.fr d) 32 :=
  hf.readW (Region.contains_self _ _) hd (by decide)

theorem CR.frame {σ : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {r : BitVec 32}
    (hd : ∀ x ∈ rs, Region.Disjoint ⟨P.lay.fr oEM1, P.K⟩ x) (hK : P.K ≤ 1024) (h : CR P σ m r) : CR P σ m' r :=
  fun nB hn hp => written_congr (bytesAt_frame hf hd (by omega_arith)) (h nB hn hp)

theorem ER.frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {ok : BitVec 32}
    (hd : ∀ x ∈ rs, Region.Disjoint ⟨P.lay.fr oEM1, P.K⟩ x ∧ Region.Disjoint ⟨P.lay.fr oEM2, P.K⟩ x)
    (hK : P.K ≤ 1024) (h : ER P m ok) : ER P m' ok := by
  have e1 : Tail P m' = Tail P m := by
    simp only [Tail]; rw [bytesAt_frame hf (fun x hx => (hd x hx).1) (by omega_arith)]
  simp only [ER] at h ⊢
  rw [e1]
  exact EncR.congr (bytesAt_frame hf (fun x hx => (hd x hx).2) (by omega_arith)) h

theorem St1.frame {σ : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hK : P.K ≤ 1024)
    (hd : ∀ x ∈ rs, Region.Disjoint ⟨P.lay.fr oEM1, P.K⟩ x ∧ Region.Disjoint ⟨P.lay.fr oSt, 4⟩ x)
    (h : St1 P σ m) : St1 P σ m' :=
  let ⟨rc, cr, sl⟩ := h
  ⟨rc, cr.frame hf (fun x hx => (hd x hx).1) hK, (slot_frame hf fun x hx => (hd x hx).2).trans sl⟩

theorem frame1 {m : Mem} {d : Nat} {v : BitVec 32} :
    Frame [⟨P.lay.fr d, 4⟩] m (m.writeW (P.lay.fr d) v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem add_sub_ofNat (x : BitVec 32) {a b : Nat} (h : b ≤ a) :
    x + BitVec.ofNat 32 a - BitVec.ofNat 32 b = x + BitVec.ofNat 32 (a - b) := by
  conv_lhs => rw [show a = (a - b) + b by omega_arith, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-! ## The pieces -/

theorem encArgs_wp {σ s : State} (h : C2 P σ s) : WP isa (.block encArgs) s (C3 P σ) := by
  obtain ⟨⟨hs, hgl⟩, cr⟩ := h
  have hK := hs.1.k1024
  have hol : P.ol ≤ P.K := by have := hs.1.ol64; have := hs.1.k64; omega_arith
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  have r12 : t1.gpr .r12 = P.B := by rw [u1.gpr, hs.2.sp, BitVec.add_zero]
  refine s1.wp_strFr (d := oSt) (by show oSt + 4 ≤ frameBytes; decide) (by decide) r12 fun t2 s2 m2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  have s3 : P.lay.St σ t3 := s2.of_rest (u3.rest (ws := [.r0]) (by simp)) u3.mem
  refine s3.wp_arg (j := 3) (by simp) (by dsimp only; decide) fun t4 s4 u4 => ?_
  refine s4.wp_arg (j := 1) (by simp) (by dsimp only; decide) fun t5 s5 u5 => ?_
  refine wp_dp (op2_imm (by decide)) fun t6 u6 => ?_
  refine wp_dp (op2_reg _ _) fun t7 u7 => ?_
  refine wp_dp (op2_reg _ _) fun t8 u8 => ?_
  have s8 : P.lay.St σ t8 := ((s5.of_rest (u6.rest (ws := [.r1]) (by simp)) u6.mem).of_rest
    (u7.rest (ws := [.r1]) (by simp)) u7.mem).of_rest (u8.rest (ws := [.r1]) (by simp)) u8.mem
  refine s8.wp_arg (j := 6) (by simp) (by dsimp only; decide) fun t9 s9 u9 => WP.block_nil ?_
  have mm : t9.mem = t1.mem.writeW (P.lay.fr oSt) (t1.gpr .r0) := by
    rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, m2.mem]
  have r12' : t5.gpr .r12 = P.B := by
    rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), m2.gpr, r12]
  refine ⟨⟨⟨hs.1, s9⟩, hgl⟩, ⟨s.gpr .r0, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mm, u1.mem]
    refine cr.frame frame1 (fun x hx => ?_) hK
    simp only [List.mem_singleton] at hx; subst hx
    exact Lay.fr_sep (by simp only [oEM1, oSt]; omega_arith) (by simp only [oEM1]; omega_arith) (by simp only [oSt]; omega_arith)
  · rw [Slot, mm, Mem.readW_writeW_self32, u1.other _ (by decide)]
  · rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.other _ (by decide), u3.gpr, dpVal, m2.gpr, r12]
  · rw [u9.other _ (by decide), u8.gpr, dpVal, u7.gpr, dpVal, u6.gpr, dpVal, r12', u7.other .lr (by decide),
      u6.other .r3 (by decide), u6.other .lr (by decide), u5.gpr, u5.other .r3 (by decide), u4.gpr]
    change P.B + BitVec.ofNat 32 oEM1 + BitVec.ofNat 32 P.K - BitVec.ofNat 32 P.ol = _
    rw [add_sub_ofNat _ hol, Offset.add_ofNat_add_ofNat]
  · rw [u9.gpr]; rfl
  · rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.gpr]; rfl
  · rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.gpr]
    rfl

theorem encode_wp {σ s : State} (h : C3 P σ s) : WP isa Impl.RsaPkcs1Sig.Arm.encode s (C4 P σ) := by
  obtain ⟨⟨hs, hgl⟩, st, r0, r1, r2, r3, lr⟩ := h
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have h64 := hs.1.ol64
  have hol : P.ol ≤ P.K := by have := hs.1.k64; omega_arith
  have fit := ok.fit
  have e2 : State.addr (P.B + BitVec.ofNat 32 oEM2) = P.lay.fr oEM2 :=
    ok.addrB (by show oEM2 < frameBytes + 56 + 36; decide)
  have e1 : State.addr (P.B + BitVec.ofNat 32 (oEM1 + (P.K - P.ol))) = P.lay.fr (oEM1 + (P.K - P.ol)) :=
    ok.addrB (by show _ < frameBytes + 56 + 36; simp only [oEM1, frameBytes]; omega_arith)
  have f : ∀ d, d < 2 ^ 32 → d + P.K ≤ frameBytes → (P.B + BitVec.ofNat 32 d).toNat + P.K ≤ 2 ^ 32 := by
    intro d hd hdK
    rw [Proof.X25519.Arm.toNat_add_lt (by rw [BitVec.toNat_ofNat]; simp only [frameBytes] at fit hdK ⊢; omega_arith),
      BitVec.toNat_ofNat]
    simp only [frameBytes] at fit hdK ⊢; omega_arith
  have hin : EncIn s (P.B + BitVec.ofNat 32 oEM2) (P.B + BitVec.ofNat 32 (oEM1 + (P.K - P.ol))) P.hash P.K P.ol :=
    { r0 := r0, r1 := r1, r2 := r2, r3 := r3, lr := lr
      k64 := hs.1.k64, k1024 := hK, dl32 := by omega_arith
      dstFit := f _ (by decide) (by simp only [oEM2, frameBytes]; omega_arith)
      srcFit := by
        have := f (oEM1 + (P.K - P.ol)) (by simp only [oEM1]; omega_arith) (by simp only [oEM1, frameBytes]; omega_arith)
        omega_arith
      write := by rw [e2]; exact hs.2.inFr (by show oEM2 + P.K ≤ frameBytes; simp only [oEM2, frameBytes]; omega_arith)
      read := by
        rw [e1]
        exact hs.2.inFrR (by show oEM1 + (P.K - P.ol) + P.ol ≤ frameBytes; simp only [oEM1, frameBytes]; omega_arith)
      sep := by
        rw [e1, e2]
        exact Lay.fr_sep (by simp only [oEM1, oEM2]; omega_arith) (by simp only [oEM1]; omega_arith) (by simp only [oEM2]; omega_arith) }
  refine WP.mono (encode_ok hin) fun t ⟨fr, rest, res⟩ => ?_
  rw [e2] at fr
  have st' : P.lay.St σ t := hs.2.frameW (by show oEM2 + P.K ≤ frameBytes; simp only [oEM2, frameBytes]; omega_arith)
    fr rest.rd rest.wr rest.sp
  have d1 : Region.Disjoint ⟨P.lay.fr oEM1, P.K⟩ ⟨P.lay.fr oEM2, P.K⟩ :=
    Lay.fr_sep (by simp only [oEM1, oEM2]; omega_arith) (by simp only [oEM1]; omega_arith) (by simp only [oEM2]; omega_arith)
  refine ⟨⟨⟨hs.1, st'⟩, hgl⟩, st.frame fr hK fun x hx => ?_, ?_⟩
  · simp only [List.mem_singleton] at hx; subst hx
    exact ⟨d1, Lay.fr_sep (by simp only [oSt, oEM2]; omega_arith) (by simp only [oSt]; omega_arith) (by simp only [oEM2]; omega_arith)⟩
  · have ht : Tail P t.mem = Spec.Rsa.bytesAt s.mem (P.lay.fr (oEM1 + (P.K - P.ol))) P.ol := by
      simp only [Tail]
      have hd := VG.Proof.RsaPkcs1Sig.bytesAt_drop s.mem (P.lay.fr oEM1) (P.K - P.ol) P.ol
      rw [show P.K - P.ol + P.ol = P.K by omega_arith, Offset.add_ofNat_add_ofNat] at hd
      rw [bytesAt_frame fr (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact d1) (by omega_arith), hd]
    rw [e1, e2, ← ht] at res
    simp only [ER, EncR]
    revert res
    cases encOut P.hash.toNat (Tail P t.mem) P.K with
    | some em => exact fun r => r
    | none => exact fun r => r

theorem cmpArgs_wp {σ s : State} (h : C4 P σ s) : WP isa (.block cmpArgs) s (C5 P σ) := by
  obtain ⟨⟨hs, hgl⟩, st, er⟩ := h
  have hK := hs.1.k1024
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_strFr (d := oOk) (by show oOk + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u1.gpr, hs.2.sp, BitVec.add_zero]) fun t2 s2 m2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  refine wp_dp (op2_imm (by decide)) fun t4 u4 => ?_
  have s4 : P.lay.St σ t4 := (s2.of_rest (u3.rest (ws := [.r0]) (by simp)) u3.mem).of_rest
    (u4.rest (ws := [.r1]) (by simp)) u4.mem
  refine s4.wp_arg (j := 3) (by simp) (by dsimp only; decide) fun t5 s5 u5 => ?_
  refine wp_mov (op2_imm (by decide)) fun t6 u6 => WP.block_nil ?_
  have mm : t6.mem = t1.mem.writeW (P.lay.fr oOk) (t1.gpr .r3) := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, m2.mem]
  have r12 : t2.gpr .r12 = P.B := by rw [m2.gpr, u1.gpr, hs.2.sp, BitVec.add_zero]
  refine ⟨⟨⟨hs.1, s5.of_rest (u6.rest (ws := [.r2]) (by simp)) u6.mem⟩, hgl⟩, ?_, ⟨s.gpr .r3, ?_, ?_⟩, ?_, ?_, ?_,
    u6.gpr⟩
  · rw [mm, u1.mem]
    refine st.frame frame1 hK fun x hx => ?_
    simp only [List.mem_singleton] at hx; subst hx
    exact ⟨Lay.fr_sep (by simp only [oEM1, oOk]; omega_arith) (by simp only [oEM1]; omega_arith) (by simp only [oOk]; omega_arith),
      Lay.fr_sep (by simp only [oSt, oOk]; omega_arith) (by simp only [oSt]; omega_arith) (by simp only [oOk]; omega_arith)⟩
  · rw [mm, u1.mem]
    refine er.frame frame1 (fun x hx => ?_) hK
    simp only [List.mem_singleton] at hx; subst hx
    exact ⟨Lay.fr_sep (by simp only [oEM1, oOk]; omega_arith) (by simp only [oEM1]; omega_arith) (by simp only [oOk]; omega_arith),
      Lay.fr_sep (by simp only [oEM2, oOk]; omega_arith) (by simp only [oEM2]; omega_arith) (by simp only [oOk]; omega_arith)⟩
  · rw [Slot, mm, Mem.readW_writeW_self32, u1.other _ (by decide)]
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr, dpVal, r12]
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, dpVal, u3.other _ (by decide), r12]
  · rw [u6.other _ (by decide), u5.gpr]; rfl

theorem compare_wp {σ s : State} (h : C5 P σ s) : WP isa Impl.Bignum.Arm.compareBytes s (C6 P σ) := by
  obtain ⟨⟨hs, hgl⟩, st, ok1, r0, r1, lr, r2⟩ := h
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have fit := ok.fit
  have e1 : State.addr (P.B + BitVec.ofNat 32 oEM1) = P.lay.fr oEM1 :=
    ok.addrB (by show oEM1 < frameBytes + 56 + 36; decide)
  have e2 : State.addr (P.B + BitVec.ofNat 32 oEM2) = P.lay.fr oEM2 :=
    ok.addrB (by show oEM2 < frameBytes + 56 + 36; decide)
  have f : ∀ d, d < 2 ^ 32 → d + P.K ≤ frameBytes → (P.B + BitVec.ofNat 32 d).toNat + P.K ≤ 2 ^ 32 := by
    intro d hd hdK
    rw [Proof.X25519.Arm.toNat_add_lt (by rw [BitVec.toNat_ofNat]; simp only [frameBytes] at fit hdK ⊢; omega_arith),
      BitVec.toNat_ofNat]
    simp only [frameBytes] at fit hdK ⊢; omega_arith
  refine WP.mono (Bignum.Arm.compareBuffer_ok s (a := P.B + BitVec.ofNat 32 oEM1) (b := P.B + BitVec.ofNat 32 oEM2)
    (n := P.K) (by have := hs.1.k64; omega_arith) (by omega_arith) (f _ (by decide) (by simp only [oEM1, frameBytes]; omega_arith))
    (f _ (by decide) (by simp only [oEM2, frameBytes]; omega_arith))
    (by rw [e1]; exact hs.2.inFrR (by show oEM1 + P.K ≤ frameBytes; simp only [oEM1, frameBytes]; omega_arith))
    (by rw [e2]; exact hs.2.inFrR (by show oEM2 + P.K ≤ frameBytes; simp only [oEM2, frameBytes]; omega_arith))
    r0 r1 lr r2) fun t ⟨eq, mem, rest⟩ => ?_
  refine ⟨⟨⟨hs.1, hs.2.of_rest rest mem⟩, hgl⟩, by rw [mem]; exact st, by rw [mem]; exact ok1, ?_⟩
  rw [mem, ← e1, ← e2]
  exact eq

theorem result_wp {σ s : State} (h : C6 P σ s) : WP isa (.block result) s (C7 P σ) := by
  obtain ⟨⟨hs, hgl⟩, ⟨rc, cr, slR⟩, ⟨okv, er, slO⟩, eq⟩ := h
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_slot (d := oSt) (by show oSt + 4 ≤ frameBytes; decide) (by decide) fun t2 s2 u2 => ?_
  refine s2.wp_slot (d := oOk) (by show oOk + 4 ≤ frameBytes; decide) (by decide) fun t3 s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun t4 u4 => ?_
  refine wp_dp (op2_reg _ _) fun t5 u5 => ?_
  refine wp_dp (op2_reg _ _) fun t6 u6 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t7 u7 => ?_
  refine wp_mov (op2_imm (by decide)) fun t8 u8 => ?_
  refine wp_dp (op2_reg _ _) fun t9 u9 => ?_
  refine wp_dp (op2_reg _ _) fun t10 u10 => ?_
  refine wp_dp (op2_reg _ _) fun t11 u11 => WP.block_nil ?_
  have s11 : P.lay.St σ t11 := (((((((s3.of_rest (u4.rest (ws := [.r1]) (by simp)) u4.mem).of_rest
    (u5.rest (ws := [.r1]) (by simp)) u5.mem).of_rest (u6.rest (ws := [.r1]) (by simp)) u6.mem).of_rest
    (u7.rest (ws := [.r1]) (by simp)) u7.mem).of_rest (u8.rest (ws := [.r2]) (by simp)) u8.mem).of_rest
    (u9.rest (ws := [.r1]) (by simp)) u9.mem).of_rest (u10.rest (ws := [.r0]) (by simp)) u10.mem).of_rest
    (u11.rest (ws := [.r3]) (by simp)) u11.mem
  have mm : t11.mem = s.mem := by
    rw [u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨⟨⟨hs.1, s11⟩, hgl⟩, fun nB hn hp h hh => ?_⟩
  have r2_3 : t3.gpr .r2 = s.gpr .r2 := by
    rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)]
  have eqb : t9.gpr .r1 = BitVec.ofNat 32 (decide (s.gpr .r2 = 0#32)).toNat := by
    rw [u9.gpr, dpVal, u8.gpr, u8.other _ (by decide), u7.gpr, u6.gpr, dpVal, u5.gpr, dpVal, u4.gpr,
      u4.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), r2_3]
    exact VG.Proof.Rsa.Arm.zero_test32 _
  have r0_10 : t10.gpr .r0 = rc &&& okv := by
    rw [u10.gpr, dpVal, u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
      u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr,
      u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.other _ (by decide), u3.gpr, u2.mem, u1.mem, slR, slO]
  rw [u11.gpr, dpVal, r0_10, u10.other _ (by decide), eqb, mm]
  have hsg : (sigB P σ).length = P.K := by rw [bytesAt_length, hgl]
  obtain ⟨h', hh', hol⟩ := hs.1.hh
  rw [hh] at hh'
  cases hh'
  refine recover_result hn hsg hh hol (cr nB hn hp) er ?_
  rw [decide_eq_true_iff]
  exact eq

end VG.Proof.RsaPkcs1Sig.Arm.Rc
