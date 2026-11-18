module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont1
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.St
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont7
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont5
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont2
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont4
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint6
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Dsa.Arm.Prime.Mont9`, which the modules that import this one used -/

section

/-! # A candidate on ARMv7: the Montgomery forms of 1 and −1 (`montB_vp`)

`St.pctxClr`: after a multiplication, the context and the top words of its
result's key array cleared; `montB`: `R mod c` (from `1 · R²`) into the key
arrays `mBase + 1` and `mBase + 9`, and `c − R mod c` into `mBase + 10`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)
open VG.Proof.Rsa.Arm.Recover (VP sub32)

section
variable {P : CP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- After a multiplication into array `j`: the context, and `[mBase + j]`'s
top words cleared, so that its key number is Montgomery multiplication's. -/
theorem St.pctxClr {j : Nat} (cert : Cert (.block (clrTop (mBase + j)))) (hj : j < 8) (hjM : MOk (mBase + j))
    {x : State → Nat} :
    VP (fun σ s => (E σ ∧ KS P σ (A σ) L (V σ) LS s) ∧ MS P σ s ∧ numAt s.mem (State.addr P.M0) P.w j = x σ)
      (.block (ctx ++ clrTop (mBase + j)))
      (fun σ s => St P E (fun σ => upd (A σ) (mBase + j) (x σ)) ((mBase + j) :: L) V LS σ s ∧ MS P σ s) := by
  rw [show ctx ++ clrTop (mBase + j) = [.ldrSp .r8 aoS] ++ (ctxW ++ clrTop (mBase + j)) from rfl]
  refine VP.block_append (G := fun σ s => ((E σ ∧ KS P σ (A σ) L (V σ) LS s) ∧ MS P σ s ∧
    numAt s.mem (State.addr P.M0) P.w j = x σ) ∧ s.gpr .r8 = P.B) ?_ ?_
  · show VP _ (.block ([(Reg.r8, aoS)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, k⟩, m, n⟩ => ?_
    · rw [h₁.1.2.sp, h₁.1.2.pre.sp, h₂.1.2.sp, h₂.1.2.pre.sp]
    refine k.ldrSp (o := aoS) (by decide) fun t u => WP.block_nil ⟨⟨⟨e, k.of_rest (u.rest (ws := [.r8])
      (by simp)) u.mem⟩, ⟨m.toMSp.of_same u.mem u.sp u.rd u.wr, by rw [u.mem]; exact m.stride⟩,
      by rw [u.mem]; exact n⟩, by rw [u.gpr, k.pre.aS]⟩
  refine VP.block_append (G := fun σ s => (((E σ ∧ KS P σ (A σ) L (V σ) LS s) ∧ MS P σ s ∧
    numAt s.mem (State.addr P.M0) P.w j = x σ) ∧ Ws s P.B P.Z P.W nArr) ∧ s.gpr .r8 = P.B) ?_ ?_
  · refine VP.taint [.r8] ctxW_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s ⟨⟨⟨e, k⟩, m, n⟩, r8⟩ => ?_
    · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]
    have pre := k.pre
    have hz := pre.hdr_Z
    have hf := pre.fS
    have ea : State.addr (s.gpr .r8 + BitVec.ofNat 32 16) = off (State.addr P.B) 16 := by
      rw [r8]; exact addr_add (by simp only [hdr] at hz; omega_using [hz, hf])
    have rd : InRegions (s.rd ++ s.wr) (off (State.addr P.B) 16) 4 :=
      ⟨P.rS, List.mem_append_right _ (by rw [k.wr]; exact pre.rS_mem),
        Offset.contains_base _ (by simp only [hdr] at hz; omega_using [hz]) (by omega_using [])⟩
    simp only [ctxW, stride, List.cons_append, List.nil_append]
    refine wp_ldr (by decide) ea rd fun s2 u2 => ?_
    refine wp_dp (op2_imm (by decide)) fun s3 u3 => wp_mov (op2_lsl (by decide)) fun s4 u4 => WP.block_nil ?_
    have m4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem]
    have r4 : Rest [.r7, .r9] s s4 := (u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest (by simp)))
    have wl := pre.wle
    have e9 : s4.gpr .r9 = BitVec.ofNat 32 P.W := by
      rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr]
      apply BitVec.eq_of_toNat_eq
      have := k.cnt
      simp only [slot, w32] at this
      rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [wl])]
    have e7 : s4.gpr .r7 = BitVec.ofNat 32 (S P.W) := by
      rw [u4.gpr, u3.gpr, dpVal, u2.gpr]
      apply BitVec.eq_of_toNat_eq
      have := k.cnt
      simp only [slot, w32] at this
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, this, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      simp only [show (2 : BitVec 32).toNat = 2 from rfl, S]
      omega_using []
    have e8 : s4.gpr .r8 = P.B := by rw [r4.gpr _ (by decide), r8]
    have k4 := k.of_rest r4 m4
    exact ⟨⟨⟨⟨e, k4⟩, ⟨m.toMSp.of_same m4 r4.sp r4.rd r4.wr, by rw [m4]; exact m.stride⟩, by rw [m4]; exact n⟩,
      k4.ws e7 e8 e9⟩, e8⟩
  · refine VP.kv cert (fun _ _ h => h.1.2) fun σ s ⟨⟨⟨⟨e, k⟩, m, n⟩, hw⟩, _⟩ => ?_
    have pre := k.pre
    have hW := pre.W_eq
    rw [← List.append_nil (clrTop (mBase + j))]
    refine clrTopO_ok hw (by simp only [mBase, nArr]; omega_using [hj]) (by decide) (by omega_using [hW]) fun t ht out nt rest => WP.block_nil ?_
    have hS := pre.S_eq
    have fit := pre.fitZ (j := mBase + j) (by simp only [mBase, nArr]; omega_using [hj])
    have kp : Keep P.B P.W [mBase + j] [] s.mem t.mem :=
      Keep.of_arr (d := 4 * (P.W - 2)) out (by simp only [S]; omega_using []) (by simp)
    have v : num t.mem P.B P.W (mBase + j) = x σ := by
      rw [nt, ← pre.numAt_val32, n]
    exact ⟨⟨e, k.write1 kp (by simp only [mBase, nArr]; omega_using [hj]) (by simp) rest.sp rest.rd rest.wr v (by simp), ht⟩,
      m.of_keep pre kp (by simp only [List.mem_singleton]; rintro _ rfl; exact hjM) (by simp) rest.sp rest.rd rest.wr
        (k.sp.trans pre.sp)⟩

end

end VG.Proof.Dsa.Arm.Prime

end

end

/-! # A candidate on ARMv7: Montgomery multiplications as pieces

`St.pmont0`: the base into `r0`; `St.pmontOp`: a Montgomery multiplication
modulo `c`, which keeps `MS` and the key arrays but its own two and its
result's; `St.pctxClr`: the context, and the top words of the result's key
array cleared.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)
open VG.Proof.Rsa.Arm.Recover (VP)

section
variable {P : CP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

theorem MS.ready {σ s : State} (h : MS P σ s) (pre : In P σ) (r0 : s.gpr .r0 = P.M0) :
    ArithmeticReady P.M0 P.lenM P.w s :=
  ⟨h.workspace, h.layout, h.width, r0, h.inverse, by rw [h.n0]; exact cv_gt pre, h.stackRead, h.stackSep, h.saved⟩

/-- A Montgomery multiplication's frame keeps `MS`. -/
theorem MS.of_keeps {σ s t : State} (pre : In P σ) (h : MS P σ s) {o : Nat} (ho : o < 8) (ho0 : o ≠ 0)
    (ho4 : o ≠ 4) (k : Keeps (State.addr P.M0) P.lenM P.w o s.mem t.mem) (fr : Frame [P.rM] s.mem t.mem)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : MS P σ t := by
  have hw := pre.w4
  have a : ∀ j, arrAt P.w j = 256 + j * (8 * (P.w + 2)) := fun j => rfl
  have kb : ∀ i, i < 8 * P.lenM → (i < arrAt P.w 1 ∨ arrAt P.w 4 ≤ i ∧ i < arrAt P.w 4 + 8 * P.w) →
      t.mem (State.addr P.M0 + BitVec.ofNat 64 i) = s.mem (State.addr P.M0 + BitVec.ofNat 64 i) := by
    intro i hi hr
    refine k i hi fun j hj => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    have e1 := a 1; have e2 := a 2; have e3 := a 3; have e4 := a 4; have e5 := a 5; have eo := a o
    have m1 : o * (8 * (P.w + 2)) ≥ 1 * (8 * (P.w + 2)) := Nat.mul_le_mul_right _ (by omega)
    rcases hj with hj | hj | hj <;> rw [hj]
    · simp only [Proof.Rsa.Mont.aAcc]; omega_using [hr, e1, e2, e4]
    · simp only [Proof.Rsa.Mont.aTmp]; omega_using [hr, e1, e3, e4]
    · rcases (by omega_using [ho4] : o < 4 ∨ 4 < o) with c | c
      · have : (o + 1) * (8 * (P.w + 2)) ≤ 4 * (8 * (P.w + 2)) := Nat.mul_le_mul_right _ (by omega_using [c])
        rw [Nat.add_mul] at this; omega_using [hr, e1, e4, eo, m1, this]
      · have : 5 * (8 * (P.w + 2)) ≤ o * (8 * (P.w + 2)) := Nat.mul_le_mul_right _ (by omega_using [c])
        omega_using [hr, e1, e4, eo, this]
  have lm : arrAt P.w 8 = 8 * P.lenM := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes, CP.lenM]; omega_using []
  have a28 : arrAt P.w 4 + 8 * P.w ≤ arrAt P.w 8 := by simp only [arrAt]; omega_using []
  refine h.of_read (fun d n hd => ?_) ?_ ?_ sp rd wr
  · have hb : d + n ≤ arrAt P.w 1 := by
      have : 232 ≤ arrAt P.w 0 := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using []
      rcases hd with (h1 | ⟨_, h1⟩) | ⟨_, h1⟩ <;> simp only [mHd, arrAt] at * <;> omega_arith
    refine Mem.read_congr fun i hi => ?_
    simp only [off]; rw [Offset.add_add]
    exact kb _ (by simp only [arrAt] at *; omega_using [lm, hb, hi]) (.inl (by simp only [arrAt] at *; omega_using [hb, hi]))
  · unfold numAt
    exact congrArg BitVec.toNat (Mem.read_congr fun i hi => by
      rw [Offset.add_add]; exact kb _ (by omega_using [lm, a28, hi]) (.inr ⟨by omega_using [], by omega_using [hi]⟩))
  · rw [sp]
    have hc : (⟨State.addr s.sp, 4⟩ : Region).Contains (State.addr s.sp) (32 / 8) := by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
    refine fr.readW hc (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr; exact h.stackSep

/-- `mont0`: the base into `r0`. -/
theorem St.pmont0 :
    VP (fun σ s => St P E A L V LS σ s ∧ MS P σ s) (.block mont0)
      (fun σ s => (St P E A L V LS σ s ∧ MS P σ s) ∧ s.gpr .r0 = P.M0) := by
  show VP _ (.block ([(Reg.r0, 0)].map fun p => Instr.ldrSp p.1 p.2)) _
  refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, h, hw⟩, x⟩ => ?_
  · rw [h₁.1.2.1.sp, h₁.1.2.1.pre.sp, h₂.1.2.1.sp, h₂.1.2.1.pre.sp]
  have sp : s.sp = P.sp := h.sp.trans h.pre.sp
  refine h.bk.ldrSpV (o := 0) (by decide) (by decide) (x.toMSp.fw0 sp) fun t u => WP.block_nil ?_
  have r := u.rest (ws := [.r0]) (by simp)
  exact ⟨⟨⟨e, h.of_rest r u.mem, hw.of_upd u (by decide) (by decide) (by decide)⟩,
    ⟨x.toMSp.of_same u.mem u.sp u.rd u.wr, by rw [u.mem]; exact x.stride⟩⟩, u.gpr⟩

/-- A Montgomery multiplication modulo `c`, `[o] := [a] [b] R⁻¹` in its arrays. -/
theorem St.pmontOp {o a b : Nat} (ho : Operand o) (ha : Operand a) (hb : Operand b) (ho0 : o ≠ 0) (ho4 : o ≠ 4)
    {na nb : State → Nat}
    (hn : ∀ σ s, St P E A L V LS σ s → MS P σ s →
      numAt s.mem (State.addr P.M0) P.w a = na σ ∧ numAt s.mem (State.addr P.M0) P.w b = nb σ)
    (hnb : ∀ σ, E σ → In P σ → nb σ < cv P σ) {L' : List Nat}
    (hL' : ∀ j ∈ L', j ∈ L ∧ j ≠ mBase + 2 ∧ j ≠ mBase + 3 ∧ j ≠ mBase + o) :
    VP (fun σ s => (St P E A L V LS σ s ∧ MS P σ s) ∧ s.gpr .r0 = P.M0) (VG.Impl.Bignum.Arm.montOp o a b)
      (fun σ s => (E σ ∧ KS P σ (A σ) L' (V σ) LS s) ∧ MS P σ s ∧
        numAt s.mem (State.addr P.M0) P.w o < cv P σ ∧
        numAt s.mem (State.addr P.M0) P.w o * 2 ^ (64 * P.w) % cv P σ = na σ * nb σ % cv P σ) := by
  have fitM : arrAt P.w 3 + 32 ≤ 8 * P.lenM := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes, CP.lenM]; omega_using []
  refine VP.of_ct (fun σ₁ σ₂ => (montOp_ct (base := P.M0) (len := P.lenM) (w := P.w) ho ha hb fitM).mono
    (fun s t ⟨⟨⟨⟨e₁, h₁, w₁⟩, m₁⟩, r₁⟩, ⟨⟨⟨e₂, h₂, w₂⟩, m₂⟩, r₂⟩⟩ => ⟨⟨m₁.ready h₁.pre r₁, ?_⟩, ⟨m₂.ready h₂.pre r₂, ?_⟩,
      by rw [h₁.sp, h₁.pre.sp, h₂.sp, h₂.pre.sp]⟩) fun _ _ _ => trivial) fun σ s ⟨⟨⟨e, h, hw⟩, m⟩, r0⟩ => ?_
  · rw [(hn σ₁ s ⟨e₁, h₁, w₁⟩ m₁).2, m₁.n0]; exact hnb σ₁ e₁ h₁.pre
  · rw [(hn σ₂ t ⟨e₂, h₂, w₂⟩ m₂).2, m₂.n0]; exact hnb σ₂ e₂ h₂.pre
  have pre := h.pre
  obtain ⟨va, vb⟩ := hn σ s ⟨e, h, hw⟩ m
  refine WP.mono (montOp_ok s (m.ready pre r0) ho ha hb ho0 (by rw [vb, m.n0]; exact hnb σ e pre))
    fun t ⟨ar, n0, lt, val, keeps, fr, rest⟩ => ⟨⟨e, ?_⟩, ?_, by rw [← m.n0]; exact lt,
      by rw [← m.n0, ← va, ← vb]; exact val⟩
  · have kp := keep_of_mont pre keeps fr
    have hjs : ∀ j ∈ [mBase + 2, mBase + 3, mBase + o], j < nArr := by
      have := ho.1; simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro j (rfl | rfl | rfl) <;>
        simp only [mBase, nArr] <;> omega_arith
    refine h.core kp hjs (by simp) rest.sp rest.rd rest.wr (fun j hj => ?_) (h.sl_keep kp (by simp) (by simp))
      (fun j hj => h.live_lt j (hL' j hj).1) h.ls_ok
    obtain ⟨hjL, h2, h3, ho'⟩ := hL' j hj
    rw [kp.num (fun i hi e' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> simp_all) (by simp) (pre.fit (h.live_lt j hjL))]
    exact h.arrs j hjL
  · exact m.of_keeps pre ho.1 ho0 ho4 keeps fr rest.sp rest.rd rest.wr

end

end VG.Proof.Dsa.Arm.Prime
