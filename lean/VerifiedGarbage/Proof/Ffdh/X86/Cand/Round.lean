module

public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Prep
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.WindowPower
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.StageR
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The FFDH candidate on i686: a Miller–Rabin round

`round`: for the witness `a` in wide slot 13 and the prepared modulus `w`
(`w − 1 = 2^s d`), `z = a^d mod w` by the window power, then its `s − 1`
squarings, the header's hit mask or'ing `z = 1` and each `z^(2^j) = w − 1`:
`mrRound w a` (`round_ok`, through `hits`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86
open VG.Impl.Ffdh.X86.Candidate

/-- A round's hits after `i` squarings of `z`: `z = 1`, or `z^(2^j) = w − 1` for a `j ≤ i`. -/
def hits (w z i : Nat) : Bool :=
  decide (z % w = 1) || (List.range (i + 1)).any fun j => decide (z ^ 2 ^ j % w = w - 1)

theorem hits_zero {w z : Nat} (hz : z < w) : hits w z 0 = (decide (z = 1) || decide (z = w - 1)) := by
  simp [hits, Nat.mod_eq_of_lt hz]

theorem hits_succ (w z i : Nat) : hits w z (i + 1) = (hits w z i || decide (z ^ 2 ^ (i + 1) % w = w - 1)) := by
  simp only [hits, List.range_succ (n := i + 1), List.any_append, List.any_cons, List.any_nil, Bool.or_false,
    Bool.or_assoc]

theorem sq_pow (z w i : Nat) : (z ^ 2 ^ i % w) * (z ^ 2 ^ i % w) % w = z ^ 2 ^ (i + 1) % w := by
  rw [← Nat.mul_mod, Nat.pow_succ, Nat.pow_mul, Nat.pow_two]

/-- The round is its hits after `s − 1` squarings of `a^d`. -/
theorem mrRound_hits {w a : Nat} (h1 : 1 ≤ (Spec.Rsa.splitTwos (w - 1)).1) :
    Spec.Ffdh.mrRound w a =
      hits w (a ^ (Spec.Rsa.splitTwos (w - 1)).2 % w) ((Spec.Rsa.splitTwos (w - 1)).1 - 1) := by
  unfold Spec.Ffdh.mrRound hits
  generalize Spec.Rsa.splitTwos (w - 1) = p at *
  obtain ⟨s, d⟩ := p
  dsimp only at h1 ⊢
  rw [Nat.sub_add_cancel h1]
  simp only [VG.Proof.Bignum.powMod_eq, Nat.mod_mod]
  rfl

theorem splitTwos_pos {w : Nat} (hw3 : 3 ≤ w) (hodd : w % 2 = 1) : 1 ≤ (Spec.Rsa.splitTwos (w - 1)).1 := by
  rw [VG.Proof.Rsa.splitTwos_even (by omega) (by omega)]
  omega

theorem hdr_hit : Hdr hitOff := ⟨.inr ⟨by decide, by decide⟩, by decide⟩
theorem hdr_j : Hdr jOff := ⟨.inr ⟨by decide, by decide⟩, by decide⟩

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- A prepared modulus stays prepared through a ready context and kept slots and words. -/
theorem Prepped.keep {w : Nat} (P : Prepped Ex base bytes len args w s) {t : State}
    (R : Ready Ex base bytes len args w t) {js ds : List Nat} (k : Kept base len js ds s.mem t.mem)
    (hd : twoOff ∉ ds) (hj : 11 ∉ js ∧ 14 ∉ js ∧ 15 ∉ js := by decide) : Prepped Ex base bytes len args w t :=
  ⟨R, by rw [k.slot_eq ⟨by decide, by decide, hj.2.1⟩]; exact P.one14,
    by rw [k.slot_eq ⟨by decide, by decide, hj.2.2⟩]; exact P.m1,
    by rw [k.slot_eq ⟨by decide, by decide, hj.1⟩]; exact P.exp,
    by rw [k.word_eq ⟨by decide, by decide, by decide, hd⟩]; exact P.two⟩

/-- An exponentiation keeps slot 4. -/
theorem pwR_sv4 (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (pwR len .wide)) m m') (R : CallRoom sp base bytes) :
    sv m' base len .wide 4 = sv m base len .wide 4 := by
  have nw := h.scratch.nowrap
  have f8 := h.slot_fit .wide (j := 8) (by decide)
  have bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have T := h.table_fit .wide
  have t0 : te len .wide 0 = lo len (.slot .wide 20) := by simp [te]
  have e20 := lo_wide len 20
  have e1 := lo_wide len 1
  have e4 := lo_wide len 4
  have e5 := lo_wide len 5
  have e6 := lo_wide len 6
  have e7 := lo_wide len 7
  have e8 := lo_wide len 8
  have nb : numBase = 3336 := rfl
  refine frameR_val32 F R nw (by omega) ?_ (pwR_fit h .wide)
  intro p hp
  simp only [pwR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [winOff] <;> omega

/-- `a^d mod w` into slot 6, for the witness in slot 13 and the exponent in slot 11. -/
theorem pw_ok {w : Nat} (P : Prepped Ex base bytes len args w s) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ u, Step Ex base bytes len args s u → Prepped Ex base bytes len args w u →
      sv u.mem base len .wide 6 = sv s.mem base len .wide 13 ^ sv s.mem base len .wide 11 % w →
      Kept base len [] [] s.mem u.mem → WP isa rest u Q) :
    WP isa (.seq (copy (.slot .wide 13) (.slot .wide 5) (one .wide))
      (.seq (copy (.slot .wide 11) (.slot .wide 8) (one .wide)) (.seq (windowPower .wide) rest))) s Q := by
  have C₀ := P.ctx
  have h := C₀.inp
  have bl := h.bytes_lt
  have f8 := h.slot_fit .wide (j := 8) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e5 := lo_wide len 5
  have e8 := lo_wide len 8
  have nb : numBase = 3336 := rfl
  refine WP.seq (WP.mono (copyIn_ok h (j := 13) (d := 5) (by decide) (by decide) (by decide)) fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
  have h₂ := h.keep K₂ (by decide) (by decide) (O₂.mono (Nat.zero_le _) (by omega))
  refine WP.seq (WP.mono (copyIn_ok h₂ (j := 11) (d := 8) (by decide) (by decide) (by decide)) fun u₃ ⟨O₃, V₃, K₃⟩ => ?_)
  have sp₂ : u₂.gpr .esp = s.gpr .esp := K₂.1 _ (by decide)
  have sp₃ : u₃.gpr .esp = s.gpr .esp := (K₃.1 _ (by decide)).trans sp₂
  have G₂ : Frame (frameR base (s.gpr .esp) (stR len 0)) s.mem u₂.mem :=
    stR_of_outside h (by decide) O₂ ⟨_, by simp, slot_in h .wide (j := 5) (by decide)⟩
  have G₃ : Frame (frameR base (s.gpr .esp) (stR len 0)) u₂.mem u₃.mem :=
    stR_of_outside h (by decide) O₃ ⟨_, by simp, slot_in h .wide (j := 8) (by decide)⟩
  have C₃ : CtxOk Ex base bytes len args .wide w u₃ := by
    refine C₀.keepF (regs := [.eax, .ebx, .ecx, .edx, .ebp]) (K₂.trans K₃) (by decide) (by decide)
      (ws := [(lo len (.slot .wide 5), bc len .wide), (lo len (.slot .wide 8), bc len .wide)])
      ((frameR_of_outside O₂ (by omega) (by simp)).trans (frameR_of_outside O₃ (by omega) (by simp))) ?_ ?_
    · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> omega
    · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> omega
  have B₃ : sv u₃.mem base len .wide 5 = sv s.mem base len .wide 13 := by
    rw [slotKeep h₂ (by decide) (by decide) O₃, V₂]
  have E₃ : sv u₃.mem base len .wide 8 = sv s.mem base len .wide 11 := by
    rw [V₃, slotKeep h (by decide) (by decide) O₂]
  have one₃ : sv u₃.mem base len .wide 3 = 1 := by
    rw [slotKeep h₂ (by decide) (by decide) O₃, slotKeep h (by decide) (by decide) O₂, P.one]
  have R₃ : sv u₃.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % w := by
    rw [slotKeep h₂ (by decide) (by decide) O₃, slotKeep h (by decide) (by decide) O₂, P.r2]
  refine WP.seq (WP.mono (windowPower_ok C₃ one₃ R₃) fun u ⟨C, F, K, Y⟩ => ?_)
  rw [B₃, E₃] at Y
  have room : CallRoom (u₃.gpr .esp) base bytes := C₃.inp.room
  rw [sp₃] at F room
  have G := stR_widen F (pwR_in C₃.inp .wide 0)
  have kt : Kept base len [] [] s.mem u.mem :=
    ((kept_ops h G₂ h.room).trans (kept_ops h G₃ h.room)).trans (kept_ops h G h.room)
  have R : Ready Ex base bytes len args w u :=
    ⟨C, by rw [pwR_sv3 C₃.inp F room, one₃], by rw [pwR_sv4 C₃.inp F room, R₃]⟩
  refine k u (Step.ops h ((G₂.trans G₃).trans G)
    (((K₂.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₂).trans (K₃.mono (by decide))).trans K))
    (P.keep R kt (by decide)) Y kt

/-- A square of slot 6 modulo the ready modulus, through `R² mod w` in slot 4. -/
theorem sqr_ok {w : Nat} (R : Ready Ex base bytes len args w s) {z : Nat} (hz : sv s.mem base len .wide 6 = z)
    (hzw : z < w) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ u, Step Ex base bytes len args s u → Ready Ex base bytes len args w u →
      sv u.mem base len .wide 6 = z * z % w → Kept base len [] [] s.mem u.mem → WP isa rest u Q) :
    WP isa (.seq (mul .wide 6 6 6) (.seq (mul .wide 6 6 4) rest)) s Q := by
  have C := R.ctx
  have h := C.inp
  have hM := C.gt
  have RR : 2 ^ (16 * bc len .wide) = 2 ^ (8 * bc len .wide) * 2 ^ (8 * bc len .wide) := by
    rw [← Nat.pow_add]; congr 1; omega
  refine WP.seq (WP.mono (cmul_ok C (o := 6) (a := 6) (b := 6) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [hz]; exact hzw)) fun u₁ ⟨C₁, K₁, F₁, L₁, V₁⟩ => ?_)
  have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  have s3₁ : sv u₁.mem base len .wide 3 = sv s.mem base len .wide 3 :=
    mulR_sv h F₁ h.room (by decide) (by decide) (by decide) (by decide) (by decide)
  have s4₁ : sv u₁.mem base len .wide 4 = sv s.mem base len .wide 4 :=
    mulR_sv h F₁ h.room (by decide) (by decide) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (cmul_ok C₁ (o := 6) (a := 6) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [s4₁, R.r2]; exact Nat.mod_lt _ (by omega))) fun u ⟨C₂, K₂, F₂, L₂, V₂⟩ => ?_)
  rw [sp₁] at F₂
  have s3 : sv u.mem base len .wide 3 = sv u₁.mem base len .wide 3 :=
    mulR_sv h F₂ h.room (by decide) (by decide) (by decide) (by decide) (by decide)
  have s4 : sv u.mem base len .wide 4 = sv u₁.mem base len .wide 4 :=
    mulR_sv h F₂ h.room (by decide) (by decide) (by decide) (by decide) (by decide)
  have G₁ := stR_widen F₁ (mulR_in h .wide (by decide) 0)
  have G₂ := stR_widen F₂ (mulR_in h .wide (by decide) 0)
  rw [hz] at V₁
  rw [s4₁, R.r2, RR] at V₂
  have e : sv u.mem base len .wide 6 * 2 ^ (8 * bc len .wide) % w = z * z * 2 ^ (8 * bc len .wide) % w := by
    rw [V₂, Nat.mul_mod_mod, ← Nat.mul_assoc, ← Nat.mod_mul_mod, V₁, Nat.mod_mul_mod]
  have v := VG.Proof.Bignum.mont_cancel C.coprime e
  rw [Nat.mod_eq_of_lt L₂] at v
  exact k u (Step.ops h (G₁.trans G₂) (K₁.trans K₂))
    ⟨C₂, by rw [s3, s3₁, R.one], by rw [s4, s4₁, R.r2]⟩ v
    ((kept_ops h G₁ h.room).trans (kept_ops h G₂ h.room))

theorem cmask_or_hit (a b : Bool) : cmask b ||| cmask a = cmask (a || b) := by
  cases a <;> cases b <;> decide

/-- The hit mask or'ed with `c` (in `ecx`), and the count in word `d`, less one, into the
squarings' count. -/
theorem tally_ok {w : Nat} (P : Prepped Ex base bytes len args w s) {d : Nat} (hd : Hdr d) (hdh : d ≠ hitOff)
    {n : Nat} (hn : w32 s.mem base d = n) (hn1 : 1 ≤ n) {c old : Bool}
    (hold : w32 s.mem base hitOff = (cmask old).toNat) (hc : s.gpr .ecx = cmask c) :
    WP isa (.block [.alu .or .ecx (.mem (sc hitOff)), .store (sc hitOff) .ecx, .mov .eax (.mem (sc d)),
      .alu .sub .eax (.imm 1), .store (sc jOff) .eax]) s fun u =>
      Step Ex base bytes len args s u ∧ Prepped Ex base bytes len args w u ∧
      w32 u.mem base hitOff = (cmask (old || c)).toNat ∧ w32 u.mem base jOff = n - 1 ∧
      u.zf = some (decide (n = 1)) ∧ Kept base len [] [hitOff, jOff] s.mem u.mem ∧
      sv u.mem base len .wide 6 = sv s.mem base len .wide 6 := by
  have h := P.ctx.inp
  have nl : n < 2 ^ 32 := by rw [← hn]; exact BitVec.isLt _
  refine wp_orS (hdr_read h hdr_hit) fun v₁ U₁ => ?_
  refine hdr_store (h.regs U₁.keeps U₁.mem) hdr_hit fun v₂ S₂ W₂ k₂ O₂ _ _ _ => ?_
  refine wp_movS (hdr_read S₂.inp hd) fun v₃ U₃ _ => wp_subi fun v₄ U₄ _ z₄ => ?_
  refine hdr_store (S₂.inp.regs (U₃.keeps.trans U₄.keeps) (by rw [U₄.mem, U₃.mem])) hdr_j
    fun v₅ S₅ W₅ k₅ O₅ _ _ z₅ => WP.block_nil ?_
  have dn : w32 v₂.mem base d = n := by
    rw [← hn, k₂.word_eq ⟨by rcases hd.1 with e | e <;> omega, by rcases hd.1 with e | e <;> simp only [numBase] <;> omega,
      hd.2, by simp only [List.mem_singleton]; exact hdh⟩, U₁.mem]
  have e₄ : v₄.gpr .eax = BitVec.ofNat 32 n - 1 := by rw [U₄.gpr, U₃.gpr, dn]
  have S₁ : Step Ex base bytes len args s v₁ := Step.regs h U₁.mem U₁.keeps
  have S₄ : Step Ex base bytes len args v₂ v₄ :=
    Step.regs S₂.inp (by rw [U₄.mem, U₃.mem]) (U₃.keeps.trans U₄.keeps)
  have kt : Kept base len [] [hitOff, jOff] s.mem v₅.mem :=
    ((by rw [U₁.mem]; exact (Kept.refl _).mono : Kept base len [] [hitOff, jOff] s.mem v₁.mem).trans
      (k₂.mono.trans ((by rw [U₄.mem, U₃.mem]; exact (Kept.refl _).mono :
        Kept base len [] [hitOff, jOff] v₂.mem v₄.mem).trans k₅.mono)))
  have R : Ready Ex base bytes len args w v₅ :=
    ((((P.toReady.regs U₁.keeps (by decide) (by decide) U₁.mem).hdr hdr_hit S₂.keeps (by decide) (by decide) O₂).regs
      (U₃.keeps.trans U₄.keeps) (by decide) (by decide) (by rw [U₄.mem, U₃.mem])).hdr hdr_j S₅.keeps (by decide)
      (by decide) O₅)
  have e6 := lo_wide len 6
  have nb : numBase = 3336 := rfl
  have bl := h.bytes_lt
  have f6 := slot_fit1 h (j := 6) (by decide)
  rw [cb1] at f6
  have bw := bc_eq_cwc len .wide
  have s6 : sv v₅.mem base len .wide 6 = sv s.mem base len .wide 6 := by
    show val32 _ _ _ _ = val32 _ _ _ _
    rw [O₅.val32 (.inr (by simp only [jOff]; omega)) (by omega), U₄.mem, U₃.mem,
      O₂.val32 (.inr (by simp only [hitOff]; omega)) (by omega), U₁.mem]
  refine ⟨S₁.trans (S₂.trans (S₄.trans S₅)), P.keep R kt (by decide), ?_, ?_, ?_, kt, s6⟩
  · rw [k₅.word_eq, U₄.mem, U₃.mem, W₂, U₁.gpr, hc, hold, BitVec.ofNat_toNat, BitVec.setWidth_eq, cmask_or_hit]
  · rw [W₅, e₄]
    have h1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, h1]
    omega
  · have e₃ : v₃.gpr .eax = BitVec.ofNat 32 n := by rw [U₃.gpr, dn]
    rw [z₅, z₄, e₃, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq nl (by decide)]

/-- A round after `i` squarings of `z`: slot 6 `z^(2^i) mod w`, the hit mask its hits. -/
structure RoundAt (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat)
    (args : Nat → BitVec 32) (s : State) (w z i : Nat) (t : State) : Prop where
  step : Step Ex base bytes len args s t
  prep : Prepped Ex base bytes len args w t
  z6 : sv t.mem base len .wide 6 = z ^ 2 ^ i % w
  hit : w32 t.mem base hitOff = (cmask (hits w z i)).toNat
  kept : Kept base len [] [hitOff, jOff] s.mem t.mem

/-- One squaring of the round, the squarings' count `n` down one. -/
theorem squareStep_ok {w z i n : Nat} {t : State} (A : RoundAt Ex base bytes len args s w z i t)
    (hj : w32 t.mem base jOff = n) (hn1 : 1 ≤ n) :
    WP isa squareStep t fun u => RoundAt Ex base bytes len args s w z (i + 1) u ∧
      w32 u.mem base jOff = n - 1 ∧ u.zf = some (decide (n = 1)) := by
  have hM := A.prep.ctx.gt
  unfold squareStep
  refine sqr_ok A.prep.toReady A.z6 (Nat.mod_lt _ (by omega)) fun u₁ S₁ R₁ Z₁ k₁ => ?_
  rw [sq_pow] at Z₁
  have P₁ := A.prep.keep R₁ k₁ (by decide)
  refine WP.seq (WP.mono (eqW_ok S₁.inp (a := 6) (b := 15) (by decide) (by decide)) fun u₂ ⟨m₂, e₂, K₂⟩ => ?_)
  rw [Z₁, P₁.m1] at e₂
  have P₂ := P₁.keep (P₁.toReady.regs K₂ (by decide) (by decide) m₂) (ds := []) (by rw [m₂]; exact Kept.refl _)
    (by decide)
  refine WP.mono (tally_ok P₂ hdr_j (by decide) (n := n) (by rw [m₂, k₁.word_eq, hj]) hn1
    (old := hits w z i) (by rw [m₂, k₁.word_eq, A.hit]) e₂) fun u ⟨S, P, H, J, Z, k, s6⟩ => ?_
  refine ⟨⟨A.step.trans (S₁.trans ((Step.regs S₁.inp m₂ K₂).trans S)), P, by rw [s6, m₂, Z₁], ?_, ?_⟩, J, Z⟩
  · rw [H, hits_succ]
  · exact A.kept.trans (k₁.mono.trans ((by rw [m₂]; exact (Kept.refl _).mono :
      Kept base len [] [hitOff, jOff] u₁.mem u₂.mem).trans k))

/-- A Miller–Rabin round of the witness `a` in slot 13 for the prepared modulus `w`: its hit mask
in the header. -/
theorem round_ok {w a : Nat} (P : Prepped Ex base bytes len args w s) (ha : sv s.mem base len .wide 13 = a)
    (hw3 : 3 ≤ w) (hodd : w % 2 = 1) :
    WP isa round s fun u => Step Ex base bytes len args s u ∧ Prepped Ex base bytes len args w u ∧
      w32 u.mem base hitOff = (cmask (Spec.Ffdh.mrRound w a)).toNat ∧
      Kept base len [] [hitOff, jOff] s.mem u.mem := by
  have s1 := splitTwos_pos hw3 hodd
  rw [mrRound_hits s1]
  generalize hz : a ^ (Spec.Rsa.splitTwos (w - 1)).2 % w = z
  have zw : z < w := by rw [← hz]; exact Nat.mod_lt _ (by omega)
  unfold round
  refine pw_ok P fun u₁ S₁ P₁ Z₁ k₁ => ?_
  rw [ha, P.exp, hz] at Z₁
  refine WP.seq (WP.mono (eqW_ok S₁.inp (a := 6) (b := 3) (by decide) (by decide)) fun u₂ ⟨m₂, e₂, K₂⟩ => ?_)
  rw [Z₁, P₁.one] at e₂
  have S₂ : Step Ex base bytes len args u₁ u₂ := Step.regs S₁.inp m₂ K₂
  refine WP.seq (hdr_store (S₂.inp) hdr_hit fun u₃ S₃ W₃ k₃ O₃ _ _ _ => WP.block_nil ?_)
  have P₃ : Prepped Ex base bytes len args w u₃ :=
    P₁.keep (((P₁.toReady.regs K₂ (by decide) (by decide) m₂).hdr hdr_hit S₃.keeps (by decide) (by decide) O₃))
      ((by rw [m₂]; exact (Kept.refl _).mono : Kept base len [] [hitOff] u₁.mem u₂.mem).trans k₃)
      (by decide)
  have h₂ := S₂.inp
  have bl := h₂.bytes_lt
  have e6 := lo_wide len 6
  have nb : numBase = 3336 := rfl
  have f6 := slot_fit1 h₂ (j := 6) (by decide)
  rw [cb1] at f6
  have bw := bc_eq_cwc len .wide
  have z₃ : sv u₃.mem base len .wide 6 = z := by
    show val32 _ _ _ _ = _
    rw [O₃.val32 (.inr (by simp only [hitOff]; omega)) (by omega), m₂]; exact Z₁
  refine WP.seq (WP.mono (eqW_ok S₃.inp (a := 6) (b := 15) (by decide) (by decide)) fun u₄ ⟨m₄, e₄, K₄⟩ => ?_)
  rw [z₃, P₃.m1] at e₄
  have P₄ := P₃.keep (P₃.toReady.regs K₄ (by decide) (by decide) m₄) (ds := []) (by rw [m₄]; exact Kept.refl _)
    (by decide)
  refine WP.seq (WP.mono (tally_ok P₄ hdr_two (by decide) (n := (Spec.Rsa.splitTwos (w - 1)).1)
    (by rw [m₄]; exact P₃.two) s1 (old := decide (z = 1)) (by rw [m₄, W₃, e₂]) e₄)
    fun u₅ ⟨S₅, P₅, H₅, J₅, Z₅, k₅, s6₅⟩ => ?_)
  have A : RoundAt Ex base bytes len args s w z 0 u₅ := by
    refine ⟨S₁.trans (S₂.trans (S₃.trans ((Step.regs S₃.inp m₄ K₄).trans S₅))), P₅, ?_, ?_, ?_⟩
    · rw [s6₅, m₄, z₃, Nat.pow_zero, Nat.pow_one, Nat.mod_eq_of_lt zw]
    · rw [H₅, hits_zero zw]
    · exact k₁.mono.trans ((by rw [m₂]; exact (Kept.refl _).mono : Kept base len [] [hitOff, jOff] u₁.mem u₂.mem).trans
        (k₃.mono.trans ((by rw [m₄]; exact (Kept.refl _).mono : Kept base len [] [hitOff, jOff] u₃.mem u₄.mem).trans
          k₅)))
  generalize (Spec.Rsa.splitTwos (w - 1)).1 = sn at s1 J₅ Z₅ ⊢
  have fin : ∀ u, RoundAt Ex base bytes len args s w z (sn - 1) u →
      Step Ex base bytes len args s u ∧ Prepped Ex base bytes len args w u ∧
      w32 u.mem base hitOff = (cmask (hits w z (sn - 1))).toNat ∧
      Kept base len [] [hitOff, jOff] s.mem u.mem := fun u A => ⟨A.step, A.prep, A.hit, A.kept⟩
  refine WP.ite (decide (sn = 1)) Z₅ (fun e => WP.block_nil (fin _ ?_)) fun e => ?_
  · rw [show sn = 1 by simpa using e]; exact A
  have sn2 : 2 ≤ sn := by simp at e; omega
  refine WP.loop (M := isa) (fun n t => ∃ i, n = sn - 1 - i ∧ i < sn - 1 ∧ RoundAt Ex base bytes len args s w z i t ∧
    w32 t.mem base jOff = sn - 1 - i) ?_ (sn - 1) u₅ ⟨0, by omega, by omega, A, by rw [J₅, Nat.sub_zero]⟩
  rintro n t ⟨i, rfl, hi, At, Jt⟩
  refine WP.mono (squareStep_ok At Jt (by omega)) fun u ⟨Au, Ju, Zu⟩ => ?_
  by_cases last : i + 1 = sn - 1
  · refine .inl ⟨by show u.zf.map (!·) = _; rw [Zu]; simp; omega, fin u (last ▸ Au)⟩
  · refine .inr ⟨by show u.zf.map (!·) = _; rw [Zu]; simp; omega, sn - 1 - (i + 1), by omega, i + 1, rfl, by omega,
      Au, by rw [Ju]; omega⟩

end VG.Proof.Ffdh.X86.Cand
