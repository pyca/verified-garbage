module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mr3
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mr2
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint7
import VerifiedGarbage.Proof.Dsa.Arm.Prime.TaintD
import VerifiedGarbage.Proof.Dsa.Generation.WitnessSlice
import VerifiedGarbage.Proof.Dsa.Generation.Primality
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Seqs
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Math
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Words
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.St
import VerifiedGarbage.Proof.Rsa.Arm.KeyWord
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Vals

/-! # A candidate on ARMv7: the witness (`witnessFix_vp`)

From its octets `x` in `[aX]`: `sU := 2 ≤ x < c − 1`, and the witness into
`[aH1]`, `x` if `sU` is set, else `x` with bit 1 set and its top bit cleared
(`witness_arm`). The operations keeping `MS` on the way (`St.pltSM`, …).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)
open VG.Proof.Rsa.Arm.Recover (VP sub32 sub32_of)
open VG.Proof.RsaKeyGen (goS shapeOf itersOf)
open VG.Proof.Dsa.Generation (DMrAt dmrS dwit dres)
open VG.Proof.Rsa (b2n)
open VG.Impl.RsaKeyGen.Arm.Key (andNotS)
open VG.Proof.RsaKeyGen.Arm.Key (b2n_xor b2n_and b2n_lt)

/-- The stage after the witness's octets. -/
abbrev AW (P : CP) (k : Nat) (σ : State) : Nat → Nat := upd (AB2 P σ) aX (xw P σ k)
abbrev VW (P : CP) (k : Nat) (σ : State) : Nat → Nat := upd (VI P k σ) sUsed (P.D * k + P.D)
abbrev LSW : List Nat := sUsed :: LSI

/-- The witness of iteration `k`, and whether it was uniform. -/
abbrev wf (P : CP) (σ : State) (k : Nat) : Nat × Bool := dwit (cv P σ) P.D (rB P σ) (P.D * k)

/-- The witness from `x < 2^bits`, for `c − 1` of `bits` bits. -/
theorem witness_dsa {c x bits : Nat} (hb : Spec.RsaKeyGen.bitLength (c - 1) = bits) (hx : x < 2 ^ bits) :
    Spec.RsaKeyGen.witness (c - 1) x =
      (if (!decide (x < 2) && decide (x < c - 1)) = true then x else (x ||| 2) % 2 ^ (bits - 1),
        !decide (x < 2) && decide (x < c - 1)) := by
  unfold Spec.RsaKeyGen.witness
  simp only [hb, Nat.mod_eq_of_lt hx]
  by_cases h1 : x < 2 <;> by_cases h2 : x < c - 1 <;> simp [h1, h2] <;> omega

/-- `c − 1` has `8 len` bits. -/
theorem In.cm1_bits {P : CP} {σ : State} (pre : In P σ) : Spec.RsaKeyGen.bitLength (cv P σ - 1) = 8 * P.len := by
  have sz := pre.sizes
  rw [VG.Proof.Dsa.Generation.predecessor_bits (n := P.bits) (by omega) pre.odd pre.bl]
  omega

/-- The witness is that of the loaded octets, the last `len` of its draw. -/
theorem wf_eq {P : CP} {σ : State} (pre : In P σ) {k : Nat} (hu : P.D * k + P.D ≤ P.rl) :
    wf P σ k = Spec.RsaKeyGen.witness (cv P σ - 1) (xw P σ k) := by
  have sz := pre.sizes
  unfold wf dwit xw
  exact VG.Proof.Dsa.Generation.witness_slice (by omega) (by rw [rB_length]; exact hu) pre.cm1_bits

section
variable {P : CP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- A step writing one array `j` that Montgomery multiplication leaves alone keeps `MS`. -/
theorem MS.of_k1 {σ s t : State} (m : MS P σ s) {A' : Nat → Nat} {L' : List Nat} {V' : Nat → Nat}
    {LS' : List Nat} (h : KS P σ A' L' V' LS' s) {j : Nat} (hj : MOk j) (k : Keep P.B P.W [j] [] s.mem t.mem)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : MS P σ t :=
  m.of_keep h.pre k (by simpa using hj) (by simp) sp rd wr (h.sp.trans h.pre.sp)

/-- `St.pltS`, keeping `MS`. -/
theorem St.pltSM {d a b : Nat} (cert : Cert (seqs (ltS d a b))) (ha : a ∈ L) (hb : b ∈ L) (hTa : aTmp ≠ a)
    (hTb : aTmp ≠ b) (hd : LsOk d) :
    VP (fun σ s => St P E A L V LS σ s ∧ MS P σ s) (seqs (ltS d a b))
      (fun σ s => St P E (fun σ => upd (A σ) aTmp (sub32 P.W (A σ a) (A σ b))) (aTmp :: L)
        (fun σ => upd (V σ) d (b2n (decide (A σ a < A σ b)))) (d :: LS) σ s ∧ MS P σ s) :=
  VP.kv cert (fun _ _ h => h.1.2.2) fun σ s ⟨⟨e, h, hw⟩, m⟩ => by
    simp only [ltS, seqs]
    rw [WP.seq_iff]
    refine WP.mono (sub3_ok hw (by decide) (h.live_lt a ha) (h.live_lt b hb) (by decide) hTa hTb)
      fun t ⟨ht, k, v, bo, r⟩ => ?_
    obtain ⟨e1, e2⟩ := sub32_of (val32_lt _ _ _ _) (val32_lt _ _ _ _) v bo
    have ea : val32 s.mem (State.addr P.B) (arr P.W a) P.W = A σ a := h.arrs a ha
    have eb : val32 s.mem (State.addr P.B) (arr P.W b) P.W = A σ b := h.arrs b hb
    simp only [num, ea, eb] at e1 e2
    have h1 := h.write1 k (by decide) (by simp) r.sp r.rd r.wr e1 (by simp)
    have m1 := m.of_k1 h (j := aTmp) (by decide) k r.sp r.rd r.wr
    exact h1.strM m1 ht hd fun u hu hwu mu _ => WP.block_nil ⟨⟨e, by rw [e2] at hu; exact hu, hwu⟩, mu⟩

/-- `St.pandNotS`, keeping `MS`. -/
theorem St.pandNotSM {d a b : Nat} {X Y : State → Bool} (cert : Cert (.block (andNotS d a b))) (ha : a ∈ LS)
    (hb : b ∈ LS) (hd : LsOk d) (hX : ∀ σ, E σ → V σ a = b2n (X σ)) (hY : ∀ σ, E σ → V σ b = b2n (Y σ)) :
    VP (fun σ s => St P E A L V LS σ s ∧ MS P σ s) (.block (andNotS d a b))
      (fun σ s => St P E A L (fun σ => upd (V σ) d (b2n (!X σ && Y σ))) (d :: LS) σ s ∧ MS P σ s) :=
  VP.kv cert (fun _ _ h => h.1.2.2) fun σ s ⟨⟨e, h, hw⟩, m⟩ => by
    unfold andNotS
    refine h.ldrM m hw ha (r := .r1) (by decide) fun s1 h1 hw1 m1 u1 => ?_
    refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
    have h2 := h1.of_rest (u2.rest (ws := [.r1]) (by simp)) u2.mem
    have hw2 := hw1.of_upd u2 (by decide) (by decide) (by decide)
    refine h2.ldrM (m1.of_upd u2) hw2 hb (r := .r2) (by decide) fun s3 h3 hw3 m3 u3 => ?_
    refine wp_dp (op2_reg _ _) fun s4 u4 => ?_
    have h4 := h3.of_rest (u4.rest (ws := [.r1]) (by simp)) u4.mem
    have hw4 := hw3.of_upd u4 (by decide) (by decide) (by decide)
    refine h4.strM (m3.of_upd u4) hw4 hd fun t ht hwt mt _ => WP.block_nil ⟨⟨e, ?_, hwt⟩, mt⟩
    have x1 : s3.gpr .r1 = BitVec.ofNat 32 (b2n (!X σ)) := by
      rw [u3.other _ (by decide), u2.gpr, dpVal, u1.gpr, hX σ e]
      apply BitVec.eq_of_toNat_eq; rw [b2n_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (b2n_lt _)]
    rwa [u4.gpr, dpVal, u3.gpr, x1, hY σ e, b2n_and] at ht

/-- `St.porTwo`, keeping `MS`. -/
theorem St.porTwoM {j : Nat} (cert : Cert (.block (orTwo j))) (hj : j ∈ L) (hM : MOk j) :
    VP (fun σ s => St P E A L V LS σ s ∧ MS P σ s) (.block (orTwo j))
      (fun σ s => St P E (fun σ => upd (A σ) j (A σ j ||| 2)) (j :: L) V LS σ s ∧ MS P σ s) :=
  VP.kv cert (fun _ _ h => h.1.2.2) fun σ s ⟨⟨e, h, hw⟩, m⟩ => by
    unfold orTwo
    rw [← List.append_nil (ptr .r0 j ++ _), List.append_assoc]
    have hj' := h.live_lt j hj
    refine lowOp_ok (ops := [.dp .orr .r1 .r1 (.imm 2)]) (f := fun x => x ||| 2) hw hj' (by decide)
      (fun u R k' => wp_dp (op2_imm (by decide)) fun u' up => WP.block_nil (k' u' up))
      fun t ht k v r _ => WP.block_nil ⟨⟨e, h.write1 k hj' (by simp) r.sp r.rd r.wr ?_ (by simp), ht⟩,
        m.of_k1 h hM k r.sp r.rd r.wr⟩
    rw [v, h.arrs j hj, or_low (b := 2) (by decide), BitVec.toNat_or, BitVec.toNat_ofNat, Nat.mod_mod]
    rfl

/-- `St.phiOp`, keeping `MS`. -/
theorem St.phiOpM {j c : Nat} {i : CP → Nat} {ops : List Instr} {f : BitVec 32 → BitVec 32} {g : State → Nat}
    (cert : Cert (.block (ptr .r0 j ++ .dp .add .r0 .r0 (.shifted .r9 .lsl 2) ::
      .dp .sub .r0 .r0 (.imm (BitVec.ofNat 32 c)) :: .ldr .r1 .r0 0 :: (ops ++ ([.str .r1 .r0 0] : List Instr)))))
    (hj : j ∈ L) (hM : MOk j) (hc : encodable (BitVec.ofNat 32 c) = true)
    (hi : ∀ σ, E σ → In P σ → P.W * 4 = 4 * i P + c ∧ i P < P.W)
    (hops : ∀ u : State, ∀ R : State → Prop, (∀ u', Upd u u' .r1 (f (u.gpr .r1)) → R u') →
      WP isa (.block ops) u R)
    (hg : ∀ σ, E σ → In P σ → A σ j % 2 ^ (32 * i P) +
        2 ^ (32 * i P) * (f (BitVec.ofNat 32 (A σ j / 2 ^ (32 * i P) % 2 ^ 32))).toNat +
        2 ^ (32 * (i P + 1)) * (A σ j / 2 ^ (32 * (i P + 1))) = g σ) :
    VP (fun σ s => St P E A L V LS σ s ∧ MS P σ s) (.block (ptr .r0 j ++ .dp .add .r0 .r0 (.shifted .r9 .lsl 2) ::
      .dp .sub .r0 .r0 (.imm (BitVec.ofNat 32 c)) :: .ldr .r1 .r0 0 :: (ops ++ ([.str .r1 .r0 0] : List Instr))))
      (fun σ s => St P E (fun σ => upd (A σ) j (g σ)) (j :: L) V LS σ s ∧ MS P σ s) :=
  VP.kv cert (fun _ _ h => h.1.2.2) fun σ s ⟨⟨e, h, hw⟩, m⟩ => by
    have hj' := h.live_lt j hj
    obtain ⟨i1, i2⟩ := hi σ e h.pre
    exact hiOp_ok hw hj' (by decide) hc i1 i2 hops fun t ht k v r => WP.block_nil
      ⟨⟨e, h.write1 k hj' (by simp) r.sp r.rd r.wr (by rw [v, h.arrs j hj]; exact hg σ e h.pre) (by simp), ht⟩,
        m.of_k1 h hM k r.sp r.rd r.wr⟩

/-- `St.phiOpM` with the word's offset in `r2`. -/
theorem St.phiOpRM {j : Nat} {i : CP → Nat} {ops : List Instr} {f : BitVec 32 → BitVec 32} {g : State → Nat}
    (cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r2, .r7, .r8, .r9]) (.block (ptr .r0 j ++
      .dp .add .r0 .r0 (.reg .r2) :: .dp .sub .r0 .r0 (.imm 4) :: .ldr .r1 .r0 0 ::
      (ops ++ ([.str .r1 .r0 0] : List Instr)))) hc).isSome = true)
    (hj : j ∈ L) (hM : MOk j) (hi : ∀ σ, E σ → In P σ → i P < P.W)
    (hops : ∀ u : State, ∀ R : State → Prop, (∀ u', Upd u u' .r1 (f (u.gpr .r1)) → R u') →
      WP isa (.block ops) u R)
    (hg : ∀ σ, E σ → In P σ → A σ j % 2 ^ (32 * i P) +
        2 ^ (32 * i P) * (f (BitVec.ofNat 32 (A σ j / 2 ^ (32 * i P) % 2 ^ 32))).toNat +
        2 ^ (32 * (i P + 1)) * (A σ j / 2 ^ (32 * (i P + 1))) = g σ)
    (hl : ∀ σ, E σ → In P σ → P.len = 4 * (i P + 1)) :
    VP (fun σ s => (St P E A L V LS σ s ∧ MS P σ s) ∧ s.gpr .r2 = BitVec.ofNat 32 P.len)
      (.block (ptr .r0 j ++ .dp .add .r0 .r0 (.reg .r2) ::
      .dp .sub .r0 .r0 (.imm 4) :: .ldr .r1 .r0 0 :: (ops ++ ([.str .r1 .r0 0] : List Instr))))
      (fun σ s => St P E (fun σ => upd (A σ) j (g σ)) (j :: L) V LS σ s ∧ MS P σ s) :=
  VP.taint [.r2, .r7, .r8, .r9] cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · rw [h₁.2, h₂.2]
    · rw [h₁.1.1.2.2.r7, h₂.1.1.2.2.r7]
    · rw [h₁.1.1.2.2.r8, h₂.1.1.2.2.r8]
    · rw [h₁.1.1.2.2.r9, h₂.1.1.2.2.r9]) fun σ s ⟨⟨⟨e, h, hw⟩, m⟩, r2⟩ => by
    have hj' := h.live_lt j hj
    have i2 := hi σ e h.pre
    rw [hl σ e h.pre] at r2
    exact hiOpR_ok hw hj' (by decide) r2 i2 hops fun t ht k v r => WP.block_nil
      ⟨⟨e, h.write1 k hj' (by simp) r.sp r.rd r.wr (by rw [v, h.arrs j hj]; exact hg σ e h.pre) (by simp), ht⟩,
        m.of_k1 h hM k r.sp r.rd r.wr⟩

/-- `St.psel`, keeping `MS`. -/
theorem St.pselM {o a b sl : Nat} (cert : Cert (sel o a b sl)) (ho : o < nArr) (ha : a ∈ L) (hb : b ∈ L)
    (hoa : o ≠ a) (hob : o ≠ b) (hsl : sl ∈ LS) (bit : ∀ σ, E σ → V σ sl ≤ 1) (hM : MOk o) :
    VP (fun σ s => St P E A L V LS σ s ∧ MS P σ s) (sel o a b sl)
      (fun σ s => St P E (fun σ => upd (A σ) o (if V σ sl = 0 then A σ a else A σ b)) (o :: L) V LS σ s ∧
        MS P σ s) :=
  VP.kv cert (fun _ _ h => h.1.2.2) fun σ _ ⟨⟨e, h, hw⟩, m⟩ => by
    have hs := h.sl sl hsl
    refine WP.mono (sel_ok hw ho (h.live_lt a ha) (h.live_lt b hb) (by decide) hoa hob (h.ls_ok sl hsl).1
      (by rw [hs]; exact bit σ e)) fun _ ⟨ht, k, v, r⟩ =>
        ⟨⟨e, h.write1 k ho (by simp) r.sp r.rd r.wr ?_ (by simp), ht⟩, m.of_k1 h hM k r.sp r.rd r.wr⟩
    rw [v, hs, h.arrs a ha, h.arrs b hb]

/-- `ldr r2, [sp, #aoEl]`: the candidate's bytes into `r2`. -/
theorem St.plenM : VP (fun σ s => St P E A L V LS σ s ∧ MS P σ s)
      (.block ([(Reg.r2, aoEl)].map fun p => Instr.ldrSp p.1 p.2))
      (fun σ s => (St P E A L V LS σ s ∧ MS P σ s) ∧ s.gpr .r2 = BitVec.ofNat 32 P.len) := by
  refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, h, hw⟩, m⟩ => ?_
  · rw [h₁.1.2.1.sp, h₁.1.2.1.pre.sp, h₂.1.2.1.sp, h₂.1.2.1.pre.sp]
  · refine h.ldrSp (o := aoEl) (by decide) fun t u => WP.block_nil ?_
    have r := u.rest (ws := [.r2]) (by simp)
    exact ⟨⟨⟨e, h.of_rest r u.mem, hw.rest r⟩, m.of_upd u⟩, by rw [u.gpr, h.pre.aEl]⟩

theorem witnessFix_eq : Impl.Dsa.Arm.ProbablePrime.witnessFix = ltS sA aX aTwo ++ (ltS sBb aX aCm1 ++
    ([.block (andNotS sU sA sBb), copy aXf aX, .block (orTwo aXf ++
      (([(Reg.r2, aoEl)].map fun p => Instr.ldrSp p.1 p.2) ++ (ptr .r0 aXf ++ .dp .add .r0 .r0 (.reg .r2) ::
      .dp .sub .r0 .r0 (.imm 4) :: .ldr .r1 .r0 0 ::
      (([.mov .r1 (.shifted .r1 .lsl 1), .mov .r1 (.shifted .r1 .lsr 1)] : List Instr) ++
        ([.str .r1 .r0 0] : List Instr))))),
    sel aH1 aXf aX sU] : List (Prog isa))) := rfl

/-- The witness into `[aH1]`, and whether it was uniform into `sU`. -/
theorem witnessFix_vp {k : Nat} (hE : ∀ σ, E σ → P.D * k + P.D ≤ P.rl) :
    VP (fun σ s => St P E (AW P k) (aX :: LB2) (VW P k) LSW σ s ∧ MS P σ s)
      (seqs Impl.Dsa.Arm.ProbablePrime.witnessFix)
      (fun σ s => St P E (fun σ => upd (AW P k σ) aH1 (wf P σ k).1) (aH1 :: aX :: LB2)
        (fun σ => upd (VW P k σ) sU (b2n (wf P σ k).2)) (sU :: LSW) σ s ∧ MS P σ s) := by
  rw [witnessFix_eq]
  refine VP.seqs_app (by simp [ltS]) (by simp [ltS]) (St.pltSM ltA_taint (by simp) (by simp) (by decide) (by decide)
    (by decide)) (VP.seqs_app (by simp [ltS]) (by simp) (St.pltSM ltB_taint (by simp) (by simp) (by decide)
    (by decide) (by decide)) ?_)
  simp only [seqs]
  refine VP.seq (St.pandNotSM (X := fun σ => decide (xw P σ k < 2)) (Y := fun σ => decide (xw P σ k < cv P σ - 1))
    andNotU_taint (by simp) (by simp) (by decide) (fun σ _ => ?_) (fun σ _ => ?_)) ?_
  · simp (config := {decide := true}) only [upd, ↓reduceIte, AW, AB2, AX, A3, A0]
  · simp (config := {decide := true}) only [upd, ↓reduceIte, AW, AB2, AX, A3]
  refine VP.seq (VP.withMS (St.pcopy copyXf_taint (by decide) (by simp) (by decide)) (fun σ s h => h.inSp)
    (copy_keepM (by decide) (by simp) (by decide) (by decide))) ?_
  refine VP.seq (VP.block_append (St.porTwoM orTwoXf_taint (by simp) (by decide))
    (VP.block_append St.plenM
    (St.phiOpRM (i := fun P => P.len / 4 - 1) (f := fun x => (x <<< 1) >>> 1)
      (g := fun σ => (xw P σ k ||| 2) % 2 ^ (8 * P.len - 1))
      clrBitXf_taint (by simp) (by decide)
      (fun σ _ pre => by have := pre.wge; have := pre.sizes; have := pre.W_eq; have := pre.L_eq; omega)
      (fun u R k' => wp_mov (op2_lsl (by decide)) fun u1 v1 => wp_mov (op2_lsr (by decide)) fun u2 v2 =>
        WP.block_nil (k' u2 ⟨by rw [v2.gpr, v1.gpr], fun r hr => by rw [v2.other r hr, v1.other r hr],
          v2.mem.trans v1.mem, v2.rd.trans v1.rd, v2.wr.trans v1.wr, v2.sp.trans v1.sp⟩))
      (fun σ _ pre => ?_) (fun σ _ pre => by have := pre.sizes; omega)))) ?_
  · have sz := pre.sizes
    simp (config := {decide := true}) only [upd, ↓reduceIte]
    rw [show 8 * P.len - 1 = 32 * (P.len / 4 - 1) + 31 by omega]
    refine clrTop_val ?_
    rw [show 32 * (P.len / 4 - 1) + 32 = 8 * P.len by omega]
    exact Nat.or_lt_two_pow (xw_lt P σ k) (Nat.lt_of_lt_of_le (show 2 < 2 ^ 2 by decide)
      (Nat.pow_le_pow_right (by decide) (show 2 ≤ 8 * P.len by omega)))
  refine (St.pselM selX_taint (by decide) (by simp) (by simp) (by decide) (by decide) (by simp)
    (fun σ _ => ?_) (by decide)).mono (fun _ _ h => h) fun σ s ⟨h, m⟩ =>
      ⟨h.mono (fun j hj => ⟨by mem_sub, ?_⟩) (fun d hd => ⟨by revert hd; revert d; decide, ?_⟩), m⟩
  · simp (config := {decide := true}) only [upd, ↓reduceIte]
    exact VG.Proof.Rsa.b2n_le _
  · have pre := h.2.1.pre
    have ew := wf_eq pre (k := k) (hE σ h.1)
    have hx : xw P σ k < 2 ^ (8 * P.len) := xw_lt P σ k
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [upd, ↓reduceIte, AW]
    rw [ew, witness_dsa pre.cm1_bits hx]
    cases (!decide (xw P σ k < 2) && decide (xw P σ k < cv P σ - 1)) <;> rfl
  · have pre := h.2.1.pre
    have ew := wf_eq pre (k := k) (hE σ h.1)
    have hx : xw P σ k < 2 ^ (8 * P.len) := xw_lt P σ k
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [upd, ↓reduceIte]
    rw [ew, witness_dsa pre.cm1_bits hx]

end

end VG.Proof.Dsa.Arm.Prime
