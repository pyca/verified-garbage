module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.VfCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Encode
import VerifiedGarbage.Proof.Bignum.Arm.CompareBuffer
import VerifiedGarbage.Proof.Rsa.Arm.PrivMask
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Rsa.ZeroTest32

/-!
# RSASSA-PKCS1-v1_5 verification with a precomputed public key on ARMv7: after the call

The status to its word and the encoding of the hash value to `EM₂`
(`encArgs_wp`, `encode_wp`, `ER`), the comparison of `EM₁` and `EM₂`
(`cmpArgs_wp`, `compare_wp`) and the result (`result_wp`, from
`verify_result`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Vf

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.Precomputed VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp op2_imm op2_reg op2_lsr dpVal)

variable {P : EP}

/-! ## The result -/

theorem written_congr {m m' : Mem} {a : Addr} {K : Nat} {r : BitVec 32} {o : Option (List Byte)}
    (hb : Spec.Rsa.bytesAt m' a K = Spec.Rsa.bytesAt m a K) (h : Spec.Rsa.written m a K r o) :
    Spec.Rsa.written m' a K r o := by
  cases o with
  | some y => exact ⟨h.1, hb.trans h.2⟩
  | none => exact ⟨h.1, hb.trans h.2⟩

/-- What `encode` wrote to the bytes at `a` and returned (`ok`). -/
def EncR (id : Nat) (D : List Byte) (K : Nat) (m : Mem) (a : Addr) (ok : BitVec 32) : Prop :=
  match encOut id D K with
  | some em => ok = 1 ∧ Spec.Rsa.bytesAt m a K = em
  | none => ok = 0

theorem EncR.congr {id : Nat} {D : List Byte} {K : Nat} {m m' : Mem} {a : Addr} {ok : BitVec 32}
    (hb : Spec.Rsa.bytesAt m' a K = Spec.Rsa.bytesAt m a K) (h : EncR id D K m a ok) : EncR id D K m' a ok := by
  unfold EncR at h ⊢
  split at h
  · exact ⟨h.1, hb.trans h.2⟩
  · exact h

theorem and_zero' (x : BitVec 32) : x &&& 0 = 0 := by simp
theorem zero_and' (x : BitVec 32) : 0 &&& x = 0 := by simp

/-- The result: the status, masked with the encoding's success and with
whether `EM₁` and `EM₂` are equal. -/
theorem verify_result {nB eB D sig : List Byte} {id K : Nat} {m : Mem} {a₁ a₂ : Addr} {rc ok : BitVec 32}
    {eq : Bool} (hn : nB.length = K) (hs : sig.length = K)
    (w : Spec.Rsa.written m a₁ K rc (Spec.Rsa.publicOpChecked nB eB sig)) (e : EncR id D K m a₂ ok)
    (he : eq = true ↔ Spec.Rsa.bytesAt m a₁ K = Spec.Rsa.bytesAt m a₂ K) :
    rc &&& ok &&& BitVec.ofNat 32 eq.toNat =
      if Spec.RsaPkcs1Sig.verifyId nB eB id D sig then 1 else 0 := by
  unfold Spec.RsaPkcs1Sig.verifyId
  unfold EncR encOut at e
  cases hh : Spec.RsaPkcs1Sig.Hash.ofId id with
  | none =>
    simp only [hh] at e
    rw [e, and_zero', zero_and']; rfl
  | some h =>
    simp only [hh] at e ⊢
    have hv := VG.Proof.RsaPkcs1Sig.verify_iff_publicOpChecked nB eB h D sig
    cases hp : Spec.Rsa.publicOpChecked nB eB sig with
    | none =>
      rw [hp] at w
      have hf : Spec.RsaPkcs1Sig.verify nB eB h D sig = false := by
        rw [← Bool.not_eq_true, hv]; simp [hp]
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
      rw [w.1, zero_and', zero_and']
    | some y =>
      rw [hp] at w
      cases hE : Spec.RsaPkcs1Sig.encode h D nB.length with
      | none =>
        rw [hn] at hE
        simp only [hE] at e
        have hf : Spec.RsaPkcs1Sig.verify nB eB h D sig = false := by
          rw [← Bool.not_eq_true, hv, hn]; simp [hE]
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        rw [e, and_zero', zero_and']
      | some em =>
        rw [hn] at hE
        simp only [hE] at e
        rw [w.1, e.1]
        have h11 : (1 : BitVec 32) &&& 1 = 1 := by decide
        rw [h11]
        by_cases hy : y = em
        · subst hy
          have ht : Spec.RsaPkcs1Sig.verify nB eB h D sig = true := by
            rw [hv, hn]; exact ⟨hs.trans hn.symm |>.trans hn, y, hE, hp⟩
          have heq : eq = true := he.2 (w.2.trans e.2.symm)
          simp only [ht, ↓reduceIte]
          rw [heq]; rfl
        · have hf : Spec.RsaPkcs1Sig.verify nB eB h D sig = false := by
            rw [← Bool.not_eq_true, hv, hn]
            rintro ⟨-, em', h1, h2⟩
            rw [hE] at h1
            rw [hp] at h2
            exact hy ((Option.some.inj h2).trans (Option.some.inj h1).symm)
          have heq : eq = false := by
            cases eq
            · rfl
            · exact absurd (w.2.symm.trans ((he.1 rfl).trans e.2)) hy
          simp only [hf, Bool.false_eq_true, ↓reduceIte]
          rw [heq]; rfl

/-! ## The stages -/

/-- A word of the frame kept. -/
abbrev Slot (P : EP) (m : Mem) (d : Nat) (v : BitVec 32) : Prop := m.readW (P.lay.fr d) 32 = v

/-- The encoding of the hash value. -/
abbrev ER (P : EP) (σ : State) (m : Mem) (ok : BitVec 32) : Prop :=
  EncR P.hash.toNat (digB P σ) P.K m (P.lay.fr oEM2) ok

/-- The status in its word. -/
def St1 (P : EP) (σ : State) (m : Mem) : Prop := ∃ rc, CR P σ m rc ∧ Slot P m oSt rc

/-- The encoding's success in its word. -/
def Ok1 (P : EP) (σ : State) (m : Mem) : Prop := ∃ ok, ER P σ m ok ∧ Slot P m oOk ok

/-- Before `encode`. -/
def C3 (P : EP) (σ s : State) : Prop :=
  C0 P σ s ∧ St1 P σ s.mem ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 oEM2 ∧ s.gpr .r1 = P.dig ∧
    s.gpr .r2 = P.hash ∧ s.gpr .r3 = BitVec.ofNat 32 P.K ∧ s.gpr .lr = BitVec.ofNat 32 P.dl

/-- After `encode`. -/
def C4 (P : EP) (σ s : State) : Prop := C0 P σ s ∧ St1 P σ s.mem ∧ ER P σ s.mem (s.gpr .r3)

/-- Before the comparison. -/
def C5 (P : EP) (σ s : State) : Prop :=
  C0 P σ s ∧ St1 P σ s.mem ∧ Ok1 P σ s.mem ∧ s.gpr .r0 = P.B + BitVec.ofNat 32 oEM1 ∧
    s.gpr .r1 = P.B + BitVec.ofNat 32 oEM2 ∧ s.gpr .lr = BitVec.ofNat 32 P.K ∧ s.gpr .r2 = 0

/-- After the comparison. -/
def C6 (P : EP) (σ s : State) : Prop :=
  C0 P σ s ∧ St1 P σ s.mem ∧ Ok1 P σ s.mem ∧
    (s.gpr .r2 = 0 ↔ Spec.Rsa.bytesAt s.mem (P.lay.fr oEM1) P.K = Spec.Rsa.bytesAt s.mem (P.lay.fr oEM2) P.K)

/-! ## Memory kept -/

theorem slot_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨P.lay.fr d, 4⟩ r) : m'.readW (P.lay.fr d) 32 = m.readW (P.lay.fr d) 32 :=
  hf.readW (Region.contains_self _ _) hd (by decide)

theorem CR.frame {σ : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {r : BitVec 32}
    (hd : ∀ x ∈ rs, Region.Disjoint ⟨P.lay.fr oEM1, P.K⟩ x) (hK : P.K ≤ 1024) (h : CR P σ m r) : CR P σ m' r :=
  fun nB hn hp => written_congr (bytesAt_frame hf hd (by omega)) (h nB hn hp)

theorem ER.frame {σ : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {ok : BitVec 32}
    (hd : ∀ x ∈ rs, Region.Disjoint ⟨P.lay.fr oEM2, P.K⟩ x) (hK : P.K ≤ 1024) (h : ER P σ m ok) : ER P σ m' ok :=
  EncR.congr (bytesAt_frame hf hd (by omega)) h

/-- A store to a word of the frame below `EM₁`. -/
theorem St1.frame {σ : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hK : P.K ≤ 1024)
    (hd : ∀ x ∈ rs, Region.Disjoint ⟨P.lay.fr oEM1, P.K⟩ x ∧ Region.Disjoint ⟨P.lay.fr oSt, 4⟩ x)
    (h : St1 P σ m) : St1 P σ m' :=
  let ⟨rc, cr, sl⟩ := h
  ⟨rc, cr.frame hf (fun x hx => (hd x hx).1) hK, (slot_frame hf fun x hx => (hd x hx).2).trans sl⟩

theorem Ok1.frame {σ : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hK : P.K ≤ 1024)
    (hd : ∀ x ∈ rs, Region.Disjoint ⟨P.lay.fr oEM2, P.K⟩ x ∧ Region.Disjoint ⟨P.lay.fr oOk, 4⟩ x)
    (h : Ok1 P σ m) : Ok1 P σ m' :=
  let ⟨ok, er, sl⟩ := h
  ⟨ok, er.frame hf (fun x hx => (hd x hx).1) hK, (slot_frame hf fun x hx => (hd x hx).2).trans sl⟩

theorem frame1 {m : Mem} {d : Nat} {v : BitVec 32} :
    Frame [⟨P.lay.fr d, 4⟩] m (m.writeW (P.lay.fr d) v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-! ## The pieces -/

theorem encArgs_wp {σ s : State} (h : C2 P σ s) : WP isa (.block encArgs) s (C3 P σ) := by
  obtain ⟨⟨hs, hgl⟩, cr⟩ := h
  have hK := hs.1.k1024
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_strFr (d := oSt) (by show oSt + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u1.gpr, hs.2.sp, BitVec.add_zero]) fun t2 s2 m2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  have s3 : P.lay.St σ t3 := s2.of_rest (u3.rest (ws := [.r0]) (by simp)) u3.mem
  refine s3.wp_arg (j := 5) (by simp) (by dsimp only; decide) fun t4 s4 u4 => ?_
  refine s4.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t5 s5 u5 => ?_
  refine s5.wp_arg (j := 1) (by simp) (by dsimp only; decide) fun t6 s6 u6 => ?_
  refine s6.wp_arg (j := 6) (by simp) (by dsimp only; decide) fun t7 s7 u7 => WP.block_nil ?_
  have mm : t7.mem = t1.mem.writeW (P.lay.fr oSt) (t1.gpr .r0) := by
    rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, m2.mem]
  refine ⟨⟨⟨hs.1, s7⟩, hgl⟩, ⟨s.gpr .r0, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mm, u1.mem]
    refine cr.frame frame1 (fun x hx => ?_) hK
    simp only [List.mem_singleton] at hx; subst hx
    exact Lay.fr_sep (by simp only [oEM1, oSt]; omega) (by simp only [oEM1]; omega) (by simp only [oSt]; omega)
  · rw [Slot, mm, Mem.readW_writeW_self32, u1.other _ (by decide)]
  · rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr,
      dpVal, m2.gpr, u1.gpr, hs.2.sp, BitVec.add_zero]
  · rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.gpr]; rfl
  · rw [u7.other _ (by decide), u6.other _ (by decide), u5.gpr]; rfl
  · rw [u7.other _ (by decide), u6.gpr]; rfl
  · rw [u7.gpr]; rfl

theorem encode_wp {σ s : State} (h : C3 P σ s) : WP isa Impl.RsaPkcs1Sig.Arm.encode s (C4 P σ) := by
  obtain ⟨⟨hs, hgl⟩, st, r0, r1, r2, r3, lr⟩ := h
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have fit := ok.fit
  have e2 : State.addr (P.B + BitVec.ofNat 32 oEM2) = P.lay.fr oEM2 :=
    ok.addrB (by show oEM2 < frameBytes + 56 + 36; decide)
  have hfd := ok.fits P.DIG (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hfd
  have hin : EncIn s (P.B + BitVec.ofNat 32 oEM2) P.dig P.hash P.K P.dl :=
    { r0 := r0, r1 := r1, r2 := r2, r3 := r3, lr := lr
      k64 := hs.1.k64, k1024 := hK, dl32 := hs.1.dl32
      dstFit := by
        rw [Proof.X25519.Arm.toNat_add_lt (by rw [BitVec.toNat_ofNat]; simp only [oEM2, frameBytes] at fit ⊢; omega),
          BitVec.toNat_ofNat]
        simp only [oEM2, frameBytes] at fit ⊢; omega
      srcFit := hfd
      write := by rw [e2]; exact hs.2.inFr (by show oEM2 + P.K ≤ frameBytes; simp only [oEM2, frameBytes]; omega)
      read := ⟨P.DIG, List.mem_append_left _ (by rw [hs.2.rd, ok.rd]; simp), Region.contains_self _ _⟩
      sep := by
        rw [e2]
        exact (ok.stk_fr (R := P.DIG) (.inl (by simp)) (by simp only [oEM2, frameBytes]; omega)).symm }
  refine WP.mono (encode_ok hin) fun t ⟨fr, rest, res⟩ => ?_
  rw [e2] at fr
  have st' : P.lay.St σ t := hs.2.frameW (by show oEM2 + P.K ≤ frameBytes; simp only [oEM2, frameBytes]; omega)
    fr rest.rd rest.wr rest.sp
  refine ⟨⟨⟨hs.1, st'⟩, hgl⟩, st.frame fr hK fun x hx => ?_, ?_⟩
  · simp only [List.mem_singleton] at hx; subst hx
    exact ⟨Lay.fr_sep (by simp only [oEM1, oEM2]; omega) (by simp only [oEM1]; omega) (by simp only [oEM2]; omega),
      Lay.fr_sep (by simp only [oSt, oEM2]; omega) (by simp only [oSt]; omega) (by simp only [oEM2]; omega)⟩
  · have hd : Spec.Rsa.bytesAt s.mem (State.addr P.dig) P.dl = digB P σ := hs.2.ro (R := P.DIG) (by simp)
    rw [hd, e2] at res
    unfold ER EncR
    revert res
    cases encOut P.hash.toNat (digB P σ) P.K with
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
  refine s4.wp_arg (j := 1) (by simp) (by dsimp only; decide) fun t5 s5 u5 => ?_
  refine wp_mov (op2_imm (by decide)) fun t6 u6 => WP.block_nil ?_
  have mm : t6.mem = t1.mem.writeW (P.lay.fr oOk) (t1.gpr .r3) := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, m2.mem]
  have r12 : t2.gpr .r12 = P.B := by rw [m2.gpr, u1.gpr, hs.2.sp, BitVec.add_zero]
  refine ⟨⟨⟨hs.1, s5.of_rest (u6.rest (ws := [.r2]) (by simp)) u6.mem⟩, hgl⟩, ?_, ⟨s.gpr .r3, ?_, ?_⟩, ?_, ?_, ?_,
    u6.gpr⟩
  · rw [mm, u1.mem]
    refine st.frame frame1 hK fun x hx => ?_
    simp only [List.mem_singleton] at hx; subst hx
    exact ⟨Lay.fr_sep (by simp only [oEM1, oOk]; omega) (by simp only [oEM1]; omega) (by simp only [oOk]; omega),
      Lay.fr_sep (by simp only [oSt, oOk]; omega) (by simp only [oSt]; omega) (by simp only [oOk]; omega)⟩
  · rw [mm, u1.mem]
    refine er.frame frame1 (fun x hx => ?_) hK
    simp only [List.mem_singleton] at hx; subst hx
    exact Lay.fr_sep (by simp only [oEM2, oOk]; omega) (by simp only [oEM2]; omega) (by simp only [oOk]; omega)
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
    rw [Proof.X25519.Arm.toNat_add_lt (by rw [BitVec.toNat_ofNat]; simp only [frameBytes] at fit hdK ⊢; omega),
      BitVec.toNat_ofNat]
    simp only [frameBytes] at fit hdK ⊢; omega
  refine WP.mono (Bignum.Arm.compareBuffer_ok s (a := P.B + BitVec.ofNat 32 oEM1) (b := P.B + BitVec.ofNat 32 oEM2)
    (n := P.K) (by have := hs.1.k64; omega) (by omega) (f _ (by decide) (by simp only [oEM1, frameBytes]; omega))
    (f _ (by decide) (by simp only [oEM2, frameBytes]; omega))
    (by rw [e1]; exact hs.2.inFrR (by show oEM1 + P.K ≤ frameBytes; simp only [oEM1, frameBytes]; omega))
    (by rw [e2]; exact hs.2.inFrR (by show oEM2 + P.K ≤ frameBytes; simp only [oEM2, frameBytes]; omega))
    r0 r1 lr r2) fun t ⟨eq, mem, rest⟩ => ?_
  refine ⟨⟨⟨hs.1, hs.2.of_rest rest mem⟩, hgl⟩, by rw [mem]; exact st, by rw [mem]; exact ok1, ?_⟩
  rw [mem, ← e1, ← e2]
  exact eq

theorem result_wp {σ s : State} (h : C6 P σ s) : WP isa (.block result) s (Fin P σ) := by
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
    (u11.rest (ws := [.r0]) (by simp)) u11.mem
  refine ⟨⟨hs.1, s11⟩, fun nB hn hp => ?_⟩
  have r2_3 : t3.gpr .r2 = s.gpr .r2 := by
    rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)]
  have eqb : t9.gpr .r1 = BitVec.ofNat 32 (decide (s.gpr .r2 = 0#32)).toNat := by
    rw [u9.gpr, dpVal, u8.gpr, u8.other _ (by decide), u7.gpr, u6.gpr, dpVal, u5.gpr, dpVal, u4.gpr,
      u4.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), r2_3]
    exact VG.Proof.Rsa.Arm.zero_test32 _
  have mm : t3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  have r0_10 : t10.gpr .r0 = rc &&& okv := by
    rw [u10.gpr, dpVal, u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
      u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr,
      u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.other _ (by decide), u3.gpr, u2.mem, u1.mem, slR, slO]
  rw [u11.gpr, dpVal, r0_10, u10.other _ (by decide), eqb]
  have hsg : (sigB P σ).length = P.K := by rw [bytesAt_length, hgl]
  have hd : Spec.Rsa.bytesAt s.mem (State.addr P.dig) P.dl = digB P σ := hs.2.ro (R := P.DIG) (by simp)
  refine verify_result hn hsg (cr nB hn hp) er ?_
  rw [decide_eq_true_iff]
  exact eq

end VG.Proof.RsaPkcs1Sig.Arm.Vf
