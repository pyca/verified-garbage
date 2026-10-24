module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.CrtFrame
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtMid1
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPhaseE
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecP1
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPhaseD
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtVals
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecX1
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecX
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.CrtNatural
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The RSA private-key operation on PPC64LE: the recombination

`mid2_ok`: from the powers, `h` (`phaseD_ok`), then `q h + m₂` written to
`out` under the mask (`phaseE_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- `m₁`, `m₂`, `h` and the result. -/
abbrev vm1 (s₀ : State) : Nat := vC s₀ ^ vDP s₀ % mP s₀
abbrev vm2 (s₀ : State) : Nat := vC s₀ ^ vDQ s₀ % mQ s₀
abbrev vh (s₀ : State) : Nat := (vm1 s₀ + mP s₀ - vm2 s₀ % mP s₀) % mP s₀ * mQI s₀ % mP s₀
abbrev vr (s₀ : State) : Nat := if cb s₀ then mQ s₀ * vh s₀ + vm2 s₀ else 0

theorem frame_of_out {m m' : Mem} {B : Addr} {o n : Nat} (h : Outside B o n m m') (hn : o + n ≤ 2 ^ 64)
    (hn0 : 0 < n) :
    Frame [⟨off B o, n⟩] m m' := by
  intro x hx
  refine h x ?_
  have hc := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hc
  have e := ofs_rebase B x (o := o) (by omega)
  change ¬ ofs (off B o) x + 1 ≤ n at hc
  change ofs B x < o ∨ o + n ≤ ofs B x
  rcases e with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega

/-- The registers of `mid2`. -/
def mid2Regs : List Reg := [.r0, .r15, .r16, .r17, .r3, .r4, .r11, .r21, .r29] ++ recRegs ++
  (recXRegs ++ [.r0, .r3, .r15, .r16, .r17, .r27, .r28])

/-- What the working spaces hold after `h`. -/
structure XR (s₀ s u : State) : Prop where
  r26 : u.gpr .r26 = bmask (cb s₀)
  v0 : Mont.val32 u.mem (cS s₀) (slot (cwX s₀) 0) (2 * cwX s₀) = 2 ^ (64 * cwX s₀) - 1
  w0 : word u.mem (cS s₀) (slot (cwX s₀) 0) = BitVec.allOnes 64
  v5 : Mont.val32 u.mem (cS s₀) (slot (cwX s₀) 5) (2 * cwX s₀) = mQ s₀
  h4 : Mont.val32 u.mem (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 4) (2 * cwP s₀) = vh s₀
  q4 : Mont.val32 u.mem (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 4) (2 * cwQ s₀) = vm2 s₀
  out : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem u.mem

/-- `exportM2`, `setupP` and `recombineP`: `h`. -/
theorem mid2A_ok {s₀ s t : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀) (hF : Front s₀ s)
    (t26 : t.gpr .r26 = bmask (cb s₀))
    (v0 : Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 0) (2 * cwX s₀) = 2 ^ (64 * cwX s₀) - 1)
    (w0 : word t.mem (cS s₀) (slot (cwX s₀) 0) = BitVec.allOnes 64)
    (v5 : Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 5) (2 * cwX s₀) = mQ s₀)
    (v7 : Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 7) (2 * cwX s₀) = mQI s₀)
    (p0 : Mont.val32 t.mem (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0) (2 * cwP s₀) = mP s₀)
    (p4 : Mont.val32 t.mem (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 4) (2 * cwP s₀) = vm1 s₀)
    (q4 : Mont.val32 t.mem (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 4) (2 * cwQ s₀) = vm2 s₀)
    (t10 : t.gpr .r10 = off (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 0))
    (t29 : t.gpr .r29 = BitVec.ofNat 64 (8 * (cwQ s₀ + 2)))
    (O1 : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t.mem) (k1 : Keep mid1Regs s t)
    (hc : ∀ u, XR s₀ s u →
      Keep (mid1Regs ++ (([.r0, .r15, .r16, .r17, .r3, .r4, .r11, .r21, .r29] : List Reg) ++ recRegs)) s u → WP isa c u Q) :
    WP isa (.seq exportM2 (.seq (.block (setupP oBP oPLen)) (.seq recombineP c))) t Q := by
  have hn := hP.nw
  have room := hP.room
  have pq := hP.pq
  have k64 := hP.k64; have k1024 := hP.k1024; have p1 := hP.p1; have pk := hP.pk; have q1 := hP.q1
  have qk := hP.qk
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eX0 := e (cwX s₀) 0; have eX1 := e (cwX s₀) 1; have eX2 := e (cwX s₀) 2; have eX5 := e (cwX s₀) 5
  have eX8 := e (cwX s₀) 8
  have eP0 := e (cwP s₀) 0; have eP4 := e (cwP s₀) 4; have eP8 := e (cwP s₀) 8
  have eQ4 := e (cwQ s₀) 4; have eQ8 := e (cwQ s₀) 8
  have dZ : cZ s₀ = (stackArg s₀ 9).toNat * 8 := rfl
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  have dk : ck s₀ = (s₀.gpr .r6).toNat := rfl
  have dp : cpL s₀ = (s₀.gpr .r10).toNat := rfl
  have dq : cqL s₀ = (stackArg s₀ 1).toNat := rfl
  have dP : cwP s₀ = wsWords (cpL s₀) := rfl
  have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
  have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
  have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 8 := rfl
  have fP8 := e (wsWords (cpL s₀)) 8; have fQ8 := e (wsWords (cqL s₀)) 8
  have hwX : cwX s₀ < 2 ^ 31 := by unfold cwX ck; omega
  have hqw : cqL s₀ ≤ 8 * cwQ s₀ := by unfold cwQ wsWords; omega
  obtain ⟨mP1, mPo, mQ1, mQo, mPb, mQb, mQle, mQIP, mQIb⟩ := masked_facts hP
  have hdt : ∀ d, d + 8 ≤ 256 → word t.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
    O1.word (Or.inl hd) (by omega)
  have hm2b : vm2 s₀ < 256 ^ cqL s₀ := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) mQle
  -- `h`.
  refine wp_reassoc3 (WP.seq (WP.mono (phaseD_ok (oP := oPa s₀) (oQ := oQa s₀) (wX := cwX s₀) (pL := cpL s₀)
    (qL := cqL s₀) (Pv := mP s₀) (m1 := vm1 s₀) (M2 := vm2 s₀) (QI := mQI s₀) (hF.scr.congr k1.wr) (by omega)
    (Nat.le_refl _) (by omega) (by omega) (by omega) (by omega) (by omega) hwX t10 t29
    ((k1.gpr _ (by decide)).trans hF.r23) ((k1.gpr _ (by decide)).trans hF.r27)
    ((k1.gpr _ (by decide)).trans hF.r28) (by rw [hdt _ (by decide)]; exact hF.hBP)
    (by rw [hdt _ (by decide)]; exact hF.hPL) (by rw [hdt _ (by decide)]; exact hF.hQL) p1 (by omega) q1
    (by omega) p0 (by omega) mPo p4 (Nat.mod_lt _ (by omega)) q4 hm2b v7 mQIb mQIP)
    fun t₂ ⟨⟨h4, OD⟩, k2⟩ => ?_))
  have k12 := k1.trans k2
  have FD : Frm (cS s₀) [(slot (cwX s₀) 1, cqL s₀), (oPa s₀, slot (cwP s₀) 8)] t.mem t₂.mem := fun x hx => OD x hx
  have fr : ∀ {d n : Nat}, d + n ≤ slot (cwX s₀) 1 ∨ (slot (cwX s₀) 2 ≤ d ∧ d + n ≤ oPa s₀) ∨ oQa s₀ ≤ d →
      ∀ r ∈ [(slot (cwX s₀) 1, cqL s₀), (oPa s₀, slot (cwP s₀) 8)], d + n ≤ r.1 ∨ r.1 + r.2 ≤ d := by
    intro d n hd r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega
  have hd2 : ∀ d, d + 8 ≤ 256 → word t₂.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd => by
    rw [FD.word_eq (fr (Or.inl (by omega))) (by omega)]; exact hdt d hd
  have xv : ∀ {d : Nat}, d + 8 * cwX s₀ ≤ slot (cwX s₀) 1 ∨ (slot (cwX s₀) 2 ≤ d ∧ d + 8 * cwX s₀ ≤ oPa s₀) →
      Mont.val32 t₂.mem (cS s₀) d (2 * cwX s₀) = Mont.val32 t.mem (cS s₀) d (2 * cwX s₀) := fun hd => by
    rw [Pre.val32_eq_wv, Pre.val32_eq_wv, FD.wv_eq (fr (by omega)) (by omega)]
  have hq4 : Mont.val32 t₂.mem (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 4) (2 * cwQ s₀) = vm2 s₀ := by
    rw [Pre.val32_eq_wv, wv_off, FD.wv_eq (fr (Or.inr (Or.inr (by omega)))) (by omega), ← wv_off,
      ← Pre.val32_eq_wv]; exact q4
  have OT : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t₂.mem := by
    refine O1.trans fun x hx => FD x fun r hr => ?_
    change ofs (cS s₀) x < 256 ∨ 256 + (cZ s₀ - 256) ≤ ofs (cS s₀) x at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega
  exact hc t₂ ⟨(k2.gpr _ (by decide)).trans t26, by rw [xv (Or.inl (by omega))]; exact v0,
    by rw [FD.word_eq (fr (Or.inl (by omega))) (by omega)]; exact w0,
    by rw [xv (Or.inr ⟨by omega, by omega⟩)]; exact v5, h4, hq4, OT⟩ k12

theorem mid2_ok {s₀ s t : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀) (hF : Front s₀ s)
    (t26 : t.gpr .r26 = bmask (cb s₀))
    (v0 : Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 0) (2 * cwX s₀) = 2 ^ (64 * cwX s₀) - 1)
    (w0 : word t.mem (cS s₀) (slot (cwX s₀) 0) = BitVec.allOnes 64)
    (v5 : Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 5) (2 * cwX s₀) = mQ s₀)
    (v7 : Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 7) (2 * cwX s₀) = mQI s₀)
    (p0 : Mont.val32 t.mem (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0) (2 * cwP s₀) = mP s₀)
    (p4 : Mont.val32 t.mem (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 4) (2 * cwP s₀) = vm1 s₀)
    (q4 : Mont.val32 t.mem (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 4) (2 * cwQ s₀) = vm2 s₀)
    (t10 : t.gpr .r10 = off (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 0))
    (t29 : t.gpr .r29 = BitVec.ofNat 64 (8 * (cwQ s₀ + 2)))
    (O1 : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t.mem) (k1 : Keep mid1Regs s t)
    (hc : ∀ u, Spec.Rsa.bytesAt u.mem (s₀.gpr .r3) (ck s₀) = Spec.Rsa.i2osp (vr s₀) (ck s₀) →
      u.gpr .r3 = BitVec.ofNat 64 (if cb s₀ then 1 else 0) →
      Frame [⟨off (cS s₀) 256, cZ s₀ - 256⟩, ⟨s₀.gpr .r3, ck s₀⟩] s.mem u.mem →
      Keep (mid1Regs ++ mid2Regs) s u → WP isa c u Q) :
    WP isa (.seq exportM2 (.seq (.block (setupP oBP oPLen)) (.seq recombineP (.seq recombineX
      (.seq (.block [.addi .r10 .r27 0, .addi .r29 .r28 0, .load .d .r27 .r23 oOut, .load .d .r28 .r23 oNLen])
      (.seq PublicChecked.output c)))))) t Q := by
  have hn := hP.nw
  have room := hP.room
  have pq := hP.pq
  have k64 := hP.k64; have k1024 := hP.k1024; have p1 := hP.p1; have pk := hP.pk; have q1 := hP.q1
  have qk := hP.qk
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eX0 := e (cwX s₀) 0; have eX1 := e (cwX s₀) 1; have eX2 := e (cwX s₀) 2; have eX5 := e (cwX s₀) 5
  have eX8 := e (cwX s₀) 8
  have eP0 := e (cwP s₀) 0; have eP4 := e (cwP s₀) 4; have eP8 := e (cwP s₀) 8
  have eQ4 := e (cwQ s₀) 4; have eQ8 := e (cwQ s₀) 8
  have dZ : cZ s₀ = (stackArg s₀ 9).toNat * 8 := rfl
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  have dk : ck s₀ = (s₀.gpr .r6).toNat := rfl
  have dp : cpL s₀ = (s₀.gpr .r10).toNat := rfl
  have dq : cqL s₀ = (stackArg s₀ 1).toNat := rfl
  have dP : cwP s₀ = wsWords (cpL s₀) := rfl
  have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
  have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
  have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 8 := rfl
  have fP8 := e (wsWords (cpL s₀)) 8; have fQ8 := e (wsWords (cqL s₀)) 8
  have hwX : cwX s₀ < 2 ^ 31 := by unfold cwX ck; omega
  have hqw : cqL s₀ ≤ 8 * cwQ s₀ := by unfold cwQ wsWords; omega
  obtain ⟨mP1, mPo, mQ1, mQo, mPb, mQb, mQle, mQIP, mQIb⟩ := masked_facts hP
  have hdt : ∀ d, d + 8 ≤ 256 → word t.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
    O1.word (Or.inl hd) (by omega)
  have hm2b : vm2 s₀ < 256 ^ cqL s₀ := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) mQle
  refine mid2A_ok hP hF t26 v0 w0 v5 v7 p0 p4 q4 t10 t29 O1 k1 fun t₂ R k12 => ?_
  have hdR : ∀ d, d + 8 ≤ 256 → word t₂.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
    R.out.word (Or.inl hd) (by omega)
  have hv : cb s₀ = true → mQ s₀ * vh s₀ + vm2 s₀ < 256 ^ ck s₀ := fun hb => by
    obtain ⟨_, _, _, hpq', hp1', _, hq1', _⟩ := mask_true hP.k64
      (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.pk) (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.qk) hb
    have hN := os2ip_lt' (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r5) (ck s₀)) (VG.Proof.Bignum.bytesAt_length _ _ _)
    unfold vh vm1 vm2 mQ mP mQI
    simp only [hb, ↓reduceIte]
    have := VG.Proof.Bignum.crt_recombine_bound (p := vP s₀) (q := vQ s₀) (mp := vC s₀ ^ vDP s₀ % vP s₀)
      (mq := vC s₀ ^ vDQ s₀ % vQ s₀) (qi := vQI s₀) (Nat.lt_trans Nat.zero_lt_one hp1')
      (Nat.mod_lt _ (Nat.lt_trans Nat.zero_lt_one hq1'))
    rw [hpq'] at this
    omega
  -- `q h + m₂`, written out.
  refine wp_reassoc3 (WP.seq (WP.mono (phaseE_ok (O := s₀.gpr .r3) (k := ck s₀) (b := cb s₀) (Qv := mQ s₀)
    (H := vh s₀) (M2 := vm2 s₀) (oP := oPa s₀) (oQ := oQa s₀) (hF.scr.congr k12.wr) (by omega) (Nat.le_refl _)
    (by omega) (by omega) pq hwX ((k12.gpr _ (by decide)).trans hF.r23) ((k12.gpr _ (by decide)).trans hF.r27)
    ((k12.gpr _ (by decide)).trans hF.r28) (by rw [hdR _ (by decide)]; exact hF.hBP)
    (by rw [hdR _ (by decide)]; exact hF.hPL) (by rw [hdR _ (by decide)]; exact hF.hBQ)
    (by rw [hdR _ (by decide)]; exact hF.hQL) p1 (by omega) q1 (by omega)
    R.v0 R.w0 R.v5 mQb R.h4 R.q4
    (by rw [hdR _ (by decide)]; exact hF.hOut) (by rw [hdR _ (by decide)]; exact hF.hNL) (by omega) (by omega)
    (hP.out.congr ((hF.keep.trans k12).wr)) hP.sepO R.r26 hv)
    fun u ⟨⟨ub, u3, uF⟩, k3⟩ => ?_))
  refine hc u ub u3 ?_ (by have := k12.trans k3; rwa [List.append_assoc] at this)
  exact ((frame_of_out R.out (by omega) (by omega)).mono (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp)).trans uF

end VG.Proof.Bignum.PPC64LE.Crt
