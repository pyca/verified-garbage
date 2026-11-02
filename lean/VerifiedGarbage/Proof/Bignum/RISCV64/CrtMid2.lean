module

public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtMid1
public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtRecomb
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore
import VerifiedGarbage.Proof.Bignum.CrtNatural
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The RSA private-key operation on RISC-V: the recombination

`mid2_ok`: from the powers (`M1`), `m₂`'s bytes into `X`, `h = (m₁ - m₂)
qInv mod p` in `p`'s working space, `q h + m₂` in `X`, and it written to
`out` under the mask.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Crt

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot Arrays Frm)
open VG.Impl.Bignum.RISCV64.PublicChecked (output)

theorem off_off' (S : Addr) (a i : Nat) : Mont.off (Mont.off S a) i = Mont.off S (a + i) := by
  simp only [Mont.off, BitVec.add_assoc, BitVec.ofNat_add]

/-- `h` and the result. -/
abbrev vh (s₀ : State) : Nat := (vm1 s₀ + mP s₀ - vm2 s₀ % mP s₀) % mP s₀ * mQI s₀ % mP s₀
abbrev vr (s₀ : State) : Nat := if cb s₀ then mQ s₀ * vh s₀ + vm2 s₀ else 0

theorem mid2_ok {s₀ s t : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀) (hF : Front s₀ s)
    (M : M1 s₀ s t)
    (hc : ∀ u, Spec.Rsa.bytesAt u.mem (s₀.gpr .a0) (ck s₀) = Spec.Rsa.i2osp (vr s₀) (ck s₀) →
      u.gpr .a0 = BitVec.ofNat 64 (if cb s₀ then 1 else 0) →
      (∀ i < 13, u.mem.readW (Mont.off (savW (cS s₀)) (8 * i)) 64 = s₀.gpr (Crt.saved i)) →
      u.gpr .s6 = cS s₀ → u.wr = s₀.wr → WP isa c u Q) :
    WP isa (.seq exportM2 (.seq (.block (setupP oBP oPLen)) (.seq recombineP (.seq recombineX
      (.seq (.block [.addi .a7 .s6 hdrBytes, .addi .s5 .s11 0, .load .d .s10 .s6 oOut, .load .d .s11 .s6 oNLen,
        .load .d .s9 .s6 oMask]) (.seq output c)))))) t Q := by
  have hn := hP.nw
  have room := hP.room
  have k64 := hP.k64; have k1024 := hP.k1024; have p1 := hP.p1; have pk := hP.pk; have q1 := hP.q1
  have qk := hP.qk
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eX0 := e (cwX s₀) 0; have eX1 := e (cwX s₀) 1; have eX4 := e (cwX s₀) 4; have eX5 := e (cwX s₀) 5
  have eX6 := e (cwX s₀) 6; have eX7 := e (cwX s₀) 7; have eX8 := e (cwX s₀) 8; have eX2 := e (cwX s₀) 2
  have eP0 := e (cwP s₀) 0; have eP1 := e (cwP s₀) 1; have eP4 := e (cwP s₀) 4; have eP8 := e (cwP s₀) 8
  have eP24 := e (cwP s₀) 24
  have eQ0 := e (cwQ s₀) 0; have eQ4 := e (cwQ s₀) 4; have eQ8 := e (cwQ s₀) 8; have eQ24 := e (cwQ s₀) 24
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  have fP8 := e (wordsOf (cpL s₀)) 8; have fQ8 := e (wordsOf (cqL s₀)) 8
  have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
  have dP : cwP s₀ = wordsOf (cpL s₀) := rfl
  have dQ : cwQ s₀ = wordsOf (cqL s₀) := rfl
  have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl
  have room' : oPa s₀ + slot (cwP s₀) 24 + slot (cwQ s₀) 24 ≤ cZ s₀ := room
  have hwP2 : 2 ≤ cwP s₀ := two_le_wordsOf
  have hwQ2 : 2 ≤ cwQ s₀ := two_le_wordsOf
  have hwPK : cwP s₀ ≤ (ck s₀ + 7) / 8 := wordsOf_le_of (Nat.le_of_lt pk) (by omega_arith)
  have hwQK : cwQ s₀ ≤ (ck s₀ + 7) / 8 := wordsOf_le_of (Nat.le_of_lt qk) (by omega_arith)
  have hpw : cpL s₀ ≤ 8 * cwP s₀ := by have := wordsOf_ge (l := cpL s₀); omega_arith
  have hqw : cqL s₀ ≤ 8 * cwQ s₀ := by have := wordsOf_ge (l := cqL s₀); omega_arith
  have hwX : cwX s₀ < 2 ^ 31 := by omega_arith
  have hZ256 : 256 ≤ cZ s₀ := by omega_arith
  have hm : oMask = 88 := rfl
  obtain ⟨mP1, mPo, mQ1, mQo, mPb, mQb, mQIP, mQIb⟩ := masked_facts hP
  have k0 := hF.keep
  have hd : ∀ d, d + 8 ≤ oMask ∨ (oMask + 8 ≤ d ∧ d + 8 ≤ 256) → Mont.word t.mem (cS s₀) d = Mont.word s.mem (cS s₀) d :=
    fun d hd => hdr_mid M.fr hZ256 hd
  have hm2b : vm2 s₀ < 256 ^ cqL s₀ := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega_arith)) (Nat.le_of_lt mQb)
  have hS : Scr t (cS s₀) (cZ s₀) := hF.scr.congr M.keep.2.2
  -- `m₂`'s bytes into `X`'s array 1.
  refine WP.seq (WP.mono (exportM2_ok (L := cqL s₀)
    (Scr.sub hS (show oQa s₀ + slot (cwQ s₀) 24 ≤ cZ s₀ by omega_arith)
      (by have := slot_al (cwX s₀) 8; have := slot_al (cwP s₀) 24; omega_arith) (by omega_arith))
    (Scr.le hS (show slot (cwX s₀) 8 ≤ cZ s₀ by omega_arith)) M.a7 M.s5 M.s6 M.s11
    ((hd _ (by unfold oQLen; omega_arith)).trans hF.hQL) q1 hqw (by omega_arith) (Nat.le_refl _) (Nat.le_refl _)
    (sepXB (by omega_arith) (by omega_arith) (by omega_arith)))
    fun t₁ ⟨⟨hb, O1⟩, k1⟩ => ?_)
  have hbytes : Spec.Rsa.os2ip (Spec.Rsa.bytesAt t₁.mem (Mont.off (cS s₀) (slot (cwX s₀) 1)) (cqL s₀)) = vm2 s₀ := by
    rw [Pub.out_bytes (B := Mont.off (cS s₀) (oQa s₀)) (d := slot (cwQ s₀) 4) hqw
      (by rw [← Pre.wordsVal_eq_wv]; exact M.q4) hm2b
      (fun i hi => by
        show t₁.mem (Mont.off (Mont.off (cS s₀) (slot (cwX s₀) 1)) i) = _
        rw [off_off']; exact hb i hi),
      VG.Proof.Rsa.os2ip_i2osp, Nat.mod_eq_of_lt hm2b]
  have hd1 : ∀ d, d + 8 ≤ oMask ∨ (oMask + 8 ≤ d ∧ d + 8 ≤ 256) → Mont.word t₁.mem (cS s₀) d = Mont.word s.mem (cS s₀) d :=
    fun d h' => by rw [Mont.Outside.word O1 (Or.inl (by omega_arith)) (by omega_arith)]; exact hd d h'
  have k01 := M.keep.trans k1
  -- `p`'s working space again.
  refine WP.seq (WP.mono (setupP_ok (l := cpL s₀) (Bp := Mont.off (cS s₀) (oPa s₀)) (hF.scr.congr k01.2.2)
    (by rw [k1.gpr (by decide), M.s6]; exact z0 _) (by unfold oBP; omega_arith) (by decide) (by decide)
    (by unfold oPLen; omega_arith) (by decide) (by decide) (by rw [hd1 _ (by unfold oBP; omega_arith)]; exact hF.hBP)
    (by rw [hd1 _ (by unfold oPLen; omega_arith)]; exact hF.hPL) p1 (by omega_arith))
    fun t₂ ⟨⟨p7, pra, p5, p0', _, m2⟩, k2⟩ => ?_)
  have k02 := k01.trans k2
  have hS2 : Scr t₂ (cS s₀) (cZ s₀) := hF.scr.congr k02.2.2
  -- The prime's words and `m₁` are still there, `m₂`'s bytes apart.
  have pv : ∀ j, j + 1 ≤ 24 → wordsVal t₂.mem (Mont.off (cS s₀) (oPa s₀)) (slot (cwP s₀) j) (cwP s₀) =
      wordsVal t.mem (Mont.off (cS s₀) (oPa s₀)) (slot (cwP s₀) j) (cwP s₀) := fun j hj => by
    have := Win.slot_lt (w := cwP s₀) (show j < 24 by omega_arith)
    rw [m2, wordsVal_off, wordsVal_off, Mont.Outside.wordsVal O1 (Or.inr (by omega_arith)) (by omega_arith)]
  -- `h`.
  refine WP.seq (WP.mono (recombineP_ok (Pv := mP s₀) (m1 := vm1 s₀) (QI := mQI s₀) (L := cqL s₀)
    (Scr.sub hS2 (show oPa s₀ + slot (cwP s₀) 24 ≤ cZ s₀ by omega_arith) (slot_al _ _) (by omega_arith))
    (Scr.le hS2 (show slot (cwX s₀) 8 ≤ cZ s₀ by omega_arith))
    (sepXB (Nat.le_refl _) (by omega_arith) (by omega_arith)) (Nat.le_refl _) (Nat.le_refl _) (by omega_arith) hwP2
    (by omega_arith) p7 pra p5 p0' ((k02.gpr (by decide)).trans hF.s6) ((k02.gpr (by decide)).trans hF.s11)
    (by rw [m2, hd1 _ (by unfold oQLen; omega_arith)]; exact hF.hQL) q1 (by omega_arith)
    (by rw [pv 0 (by decide)]; exact M.p0) mP1 mPo (by rw [pv 4 (by decide)]; exact M.p4)
    (Nat.mod_lt _ (by omega_arith))
    (wordsVal_trunc (by rw [m2, Mont.Outside.wordsVal O1 (d := slot (cwX s₀) 7) (k := cwX s₀)
        (Or.inr (by omega_arith)) (by omega_arith)]; exact M.x7)
      (Nat.lt_of_lt_of_le mQIb (pow256_le hpw)) (by omega_arith)) mQIP)
    fun t₃ ⟨⟨h4, O3, _⟩, k3⟩ => ?_)
  rw [m2, hbytes] at h4
  have k03 := k02.trans k3
  have O3' : Mont.Outside (cS s₀) (oPa s₀ + slot (cwP s₀) 1) (23 * (8 * (cwP s₀ + 2))) t₂.mem t₃.mem :=
    out_reb O3 (by omega_arith) (by omega_arith)
  rw [m2] at O3'
  have hd3 : ∀ d, d + 8 ≤ oMask ∨ (oMask + 8 ≤ d ∧ d + 8 ≤ 256) → Mont.word t₃.mem (cS s₀) d = Mont.word s.mem (cS s₀) d :=
    fun d h' => by rw [Mont.Outside.word O3' (Or.inl (by omega_arith)) (by omega_arith)]; exact hd1 d h'
  have xv3 : ∀ j, j < 8 → j ≠ 1 → wordsVal t₃.mem (cS s₀) (slot (cwX s₀) j) (cwX s₀) =
      wordsVal t.mem (cS s₀) (slot (cwX s₀) j) (cwX s₀) := fun j hj h1 => by
    have := VG.Proof.Bignum.slot_le (w := cwX s₀) hj
    have := VG.Proof.Bignum.slot_sep (w := cwX s₀) h1
    rw [Mont.Outside.wordsVal O3' (Or.inl (by omega_arith)) (by omega_arith),
      Mont.Outside.wordsVal O1 (by omega_arith) (by omega_arith)]
  have q43 : wordsVal t₃.mem (Mont.off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 4) (cwQ s₀) = vm2 s₀ := by
    rw [wordsVal_off, Mont.Outside.wordsVal O3' (Or.inr (by omega_arith)) (by omega_arith),
      Mont.Outside.wordsVal O1 (Or.inr (by omega_arith)) (by omega_arith), ← wordsVal_off]
    exact M.q4
  have hS3 : Scr t₃ (cS s₀) (cZ s₀) := hF.scr.congr k03.2.2
  have hvh : vh s₀ < mP s₀ := Nat.mod_lt _ (by omega_arith)
  have hm2Q : vm2 s₀ < mQ s₀ := Nat.mod_lt _ (by omega_arith)
  have hPQ : mQ s₀ * mP s₀ < 2 ^ (64 * cwX s₀) - 1 := by
    rw [Nat.mul_comm]; exact pq_lt mPb mQb pk qk (by omega_arith)
  have hlt : mQ s₀ * vh s₀ + vm2 s₀ < mQ s₀ * mP s₀ := by
    have := Nat.mul_le_mul_left (mQ s₀) (show vh s₀ + 1 ≤ mP s₀ by omega_arith)
    rw [Nat.mul_succ] at this; omega_arith
  have hvP : vh s₀ < mQ s₀ * mP s₀ := Nat.lt_of_lt_of_le hvh (Nat.le_mul_of_pos_left _ (by omega_arith))
  -- `q h + m₂`.
  refine WP.seq (WP.mono (recombineX_ok (lp := cpL s₀) (lq := cqL s₀) (qv := mQ s₀)
    (Scr.le hS3 (show slot (cwX s₀) 8 ≤ cZ s₀ by omega_arith))
    (Scr.sub hS3 (show oPa s₀ + slot (cwP s₀) 24 ≤ cZ s₀ by omega_arith) (slot_al _ _) (by omega_arith))
    (Scr.sub hS3 (show oQa s₀ + slot (cwQ s₀) 24 ≤ cZ s₀ by omega_arith)
      (by have := slot_al (cwX s₀) 8; have := slot_al (cwP s₀) 24; omega_arith) (by omega_arith))
    (sepBX (Nat.le_refl _) (by omega_arith) (by omega_arith)) (sepBX (by omega_arith) (by omega_arith) (by omega_arith))
    ((k03.gpr (by decide)).trans hF.s6) ((k03.gpr (by decide)).trans hF.s11) (Nat.le_refl _) (by omega_arith) hwX
    ((hd3 _ (by unfold oBP; omega_arith)).trans hF.hBP) ((hd3 _ (by unfold oPLen; omega_arith)).trans hF.hPL)
    ((hd3 _ (by unfold oBQ; omega_arith)).trans hF.hBQ) ((hd3 _ (by unfold oQLen; omega_arith)).trans hF.hQL)
    p1 (by omega_arith) q1 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by rw [xv3 0 (by decide) (by decide)]; exact M.x0) (by rw [xv3 5 (by decide) (by decide)]; exact M.x5)
    (by
      have e1 : wordsVal t₃.mem (Mont.off (cS s₀) (oPa s₀)) (slot (wordsOf (cpL s₀)) 4) (wordsOf (cpL s₀)) = vh s₀ := h4
      rw [e1]; omega_arith)
    (by
      have e1 : wordsVal t₃.mem (Mont.off (cS s₀) (oPa s₀)) (slot (wordsOf (cpL s₀)) 4) (wordsOf (cpL s₀)) = vh s₀ := h4
      have e2 : wordsVal t₃.mem (Mont.off (cS s₀) (oQa s₀)) (slot (wordsOf (cqL s₀)) 4) (wordsOf (cqL s₀)) =
        vm2 s₀ := q43
      rw [e1, e2]; omega_arith))
    fun t₄ ⟨⟨x4, A4⟩, k4⟩ => ?_)
  rw [h4, q43] at x4
  have k04 := k03.trans k4
  have hS4 : Scr t₄ (cS s₀) (cZ s₀) := hF.scr.congr k04.2.2
  have hd4 : ∀ d, d + 8 ≤ oMask ∨ (oMask + 8 ≤ d ∧ d + 8 ≤ 256) → Mont.word t₄.mem (cS s₀) d = Mont.word s.mem (cS s₀) d :=
    fun d h' => by
      rw [show Mont.word t₄.mem (cS s₀) d = Mont.word t₃.mem (cS s₀) d from A4.word_eq (fun j hj => Or.inl (by
        have := VG.Proof.Bignum.hdr_lt_slot (cwX s₀) j (i := 31) (by decide); omega_arith)) (by omega_arith)]
      exact hd3 d h'
  have hmsk : Mont.word t₄.mem (cS s₀) oMask = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if cb s₀ then 1 else 0) := by
    rw [show Mont.word t₄.mem (cS s₀) oMask = Mont.word t₃.mem (cS s₀) oMask from A4.word_eq (fun j hj => Or.inl (by
        have := VG.Proof.Bignum.hdr_lt_slot (cwX s₀) j (i := 11) (by decide); omega_arith)) (by omega_arith),
      Mont.Outside.word O3' (Or.inl (by omega_arith)) (by omega_arith),
      Mont.Outside.word O1 (Or.inl (by omega_arith)) (by omega_arith)]
    exact M.msk
  -- The result, written under the mask.
  refine wp_reassoc2 (WP.seq (WP.mono (final_ok (O := s₀.gpr .a0) (k := ck s₀) (b := cb s₀)
    (Scr.le hS4 (show slot (cwX s₀) 8 ≤ cZ s₀ by omega_arith)) (by rw [(k0.trans k04).2.2]; exact hP.out) hP.nwO
    ((k04.gpr (by decide)).trans hF.s6) ((k04.gpr (by decide)).trans hF.s11)
    ((hd4 _ (by unfold oOut; omega_arith)).trans hF.hOut) ((hd4 _ (by unfold oNLen; omega_arith)).trans hF.hNL) hmsk
    (by omega_arith) (by omega_arith) (Nat.le_refl _) (fun x hx => by have := hP.sepO x hx; omega_arith))
    fun t₅ ⟨⟨ob, O5, a0₅⟩, k5⟩ => ?_))
  have k05 := k04.trans k5
  have w5 : ∀ d, d + 8 ≤ 256 → Mont.word t₅.mem (cS s₀) d = Mont.word t₄.mem (cS s₀) d := fun d hd =>
    (Mem.readW_congr fun j hj => (O5 _ (Or.inr (by
      by_contra hc
      have h1 : Mont.ofs (cS s₀) (Mont.off (cS s₀) d + BitVec.ofNat 64 j) = d + j :=
        Mont.ofs_off _ (by omega_arith)
      have h2 : cZ s₀ ≤ Mont.ofs (cS s₀) (Mont.off (cS s₀) d + BitVec.ofNat 64 j) :=
        hP.sepO _ (by change Mont.ofs (s₀.gpr .a0) _ < ck s₀; omega_arith)
      omega_arith))).symm).symm
  refine hc t₅ ?_ a0₅ (fun i hi => ?_) ((k05.gpr (by decide)).trans hF.s6) (k0.trans k05).2.2
  · cases hb : cb s₀
    · rw [show vr s₀ = 0 by simp [vr, hb], VG.Proof.Bignum.i2osp_zero']
      exact Pub.zero_bytes fun i hi => by rw [ob i hi]; simp [hb]
    · have hvk : mQ s₀ * vh s₀ + vm2 s₀ < 256 ^ ck s₀ := by
        obtain ⟨_, _, _, hpq', hp1', _, hq1', _⟩ := mask_true hP.k64
          (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.pk) (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.qk) hb
        have hN := os2ip_lt' (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .a2) (ck s₀)) (VG.Proof.Bignum.bytesAt_length _ _ _)
        unfold vh vm1 vm2 mQ mP mQI
        simp only [hb, ↓reduceIte]
        have := VG.Proof.Bignum.crt_recombine_bound (p := vP s₀) (q := vQ s₀) (mp := vC s₀ ^ vDP s₀ % vP s₀)
          (mq := vC s₀ ^ vDQ s₀ % vQ s₀) (qi := vQI s₀) (Nat.lt_trans Nat.zero_lt_one hp1')
          (Nat.mod_lt _ (Nat.lt_trans Nat.zero_lt_one hq1'))
        rw [hpq'] at this
        omega_arith
      rw [show vr s₀ = mQ s₀ * vh s₀ + vm2 s₀ by simp [vr, hb]]
      exact Pub.out_bytes (B := cS s₀) (d := slot (cwX s₀) 4) (w := cwX s₀) (by omega_arith)
        (by rw [← Pre.wordsVal_eq_wv]; exact x4) hvk fun i hi => by rw [ob i hi]; simp [hb]
  · have e : Mont.off (savW (cS s₀)) (8 * i) = Mont.off (cS s₀) (112 + 8 * i) := off_off' _ _ _
    have := hF.sav i hi
    rw [e] at this ⊢
    change Mont.word t₅.mem (cS s₀) (112 + 8 * i) = _
    rw [w5 _ (by omega_arith), hd4 _ (by unfold oMask; omega_arith)]
    exact this

end VG.Proof.Bignum.RISCV64.Crt
