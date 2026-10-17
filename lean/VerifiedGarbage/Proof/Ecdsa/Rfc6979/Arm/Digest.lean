module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Wide
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Reduce
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Weierstrass.Words
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Deterministic ECDSA on 32-bit ARM: the digest's integer in the frame

`dgCopy o e` (`dgCopy_ok`): the 68 bytes at `r8 + o` cleared (`zeros_ok`),
then the digest's first `m = min(D, e)` bytes copied to `r8 + o + e - m`,
`m` computed without branches from `D` (`minE_ok`), by a loop over the words
(`copyLoop_ok`). For `e = Q`, the `Q` bytes are the digest's integer as
`bits2int` gives it.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.X25519.Arm (Rest Upd wp_ldr wp_str wp_dp wp_mov wp_subs op2_reg op2_imm dpVal)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## A loop over words -/

theorem add4 (x : Nat) : BitVec.ofNat 32 x + 4 = BitVec.ofNat 32 (x + 4) := by
  rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.ofNat_add_ofNat]

theorem sub4 {n : Nat} (h : 1 ≤ n) (h' : n ≤ 16) : BitVec.ofNat 32 (4 * n) - 4 = BitVec.ofNat 32 (4 * (n - 1)) := by
  rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem ne4 {n : Nat} (h : 2 ≤ n) (h' : n ≤ 16) : BitVec.ofNat 32 (4 * n) - 4 ≠ 0 := by
  rw [sub4 (by omega) h']
  intro e
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat] at this
  rw [show (0 : BitVec 32).toNat = 0 from rfl] at this
  omega

/-- Before the loop's iteration with `n` words left, of `K`. -/
structure CopyInv (s : State) (S Dd : BitVec 32) (K n : Nat) (u : State) : Prop where
  le : n ≤ K
  pos : 0 < n
  r1 : u.gpr .r1 = S + BitVec.ofNat 32 (4 * (K - n))
  r2 : u.gpr .r2 = Dd + BitVec.ofNat 32 (4 * (K - n))
  r3 : u.gpr .r3 = BitVec.ofNat 32 (4 * n)
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  sp : u.sp = s.sp
  other : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → u.gpr r = s.gpr r
  frame : Frame [⟨State.addr Dd, 4 * K⟩] s.mem u.mem
  bytes : Spec.Sha256.bytesAt u.mem (State.addr Dd) (4 * (K - n)) =
    Spec.Sha256.bytesAt s.mem (State.addr S) (4 * (K - n))

/-- `copyLoop`: the `4 K` bytes (`0 < K ≤ 16`) at `r1` to `r2`, `r3 = 4 K`. -/
theorem copyLoop_ok {s : State} {S Dd : BitVec 32} {K : Nat} (hK : 0 < K) (hK16 : K ≤ 16)
    (h1 : s.gpr .r1 = S) (h2 : s.gpr .r2 = Dd) (h3 : s.gpr .r3 = BitVec.ofNat 32 (4 * K))
    (hsn : S.toNat + 4 * K ≤ 2 ^ 32) (hdn : Dd.toNat + 4 * K ≤ 2 ^ 32)
    (hr : ∀ j < K, InRegions (s.rd ++ s.wr) (State.addr S + BitVec.ofNat 64 (4 * j)) 4)
    (hw : ∀ j < K, InRegions s.wr (State.addr Dd + BitVec.ofNat 64 (4 * j)) 4)
    (hsep : Region.Disjoint ⟨State.addr S, 4 * K⟩ ⟨State.addr Dd, 4 * K⟩) :
    WP isa Cfg.copyLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧
      Frame [⟨State.addr Dd, 4 * K⟩] s.mem s'.mem ∧
      Spec.Sha256.bytesAt s'.mem (State.addr Dd) (4 * K) = Spec.Sha256.bytesAt s.mem (State.addr S) (4 * K) := by
  refine WP.loop (M := isa) (CopyInv s S Dd K) (fun n u h => ?_) K s
    ⟨Nat.le_refl _, hK, by rw [h1, Nat.sub_self, Nat.mul_zero, BitVec.add_zero],
      by rw [h2, Nat.sub_self, Nat.mul_zero, BitVec.add_zero], h3, rfl, rfl, rfl, fun _ _ _ _ _ => rfl,
      Frame.refl _ _, by rw [Nat.sub_self, Nat.mul_zero]; rfl⟩
  have hn := h.le; have hp := h.pos
  have eS : State.addr (S + BitVec.ofNat 32 (4 * (K - n)) + BitVec.ofNat 32 0) =
      State.addr S + BitVec.ofNat 64 (4 * (K - n)) := by
    rw [BitVec.add_zero, addr_add (by omega_arith)]
  have eD : State.addr (Dd + BitVec.ofNat 32 (4 * (K - n)) + BitVec.ofNat 32 0) =
      State.addr Dd + BitVec.ofNat 64 (4 * (K - n)) := by
    rw [BitVec.add_zero, addr_add (by omega_arith)]
  show WP isa (.block ([.ldr .r0 .r1 0, .str .r0 .r2 0] ++
    [.dp .add .r1 .r1 (.imm 4), .dp .add .r2 .r2 (.imm 4), .subs .r3 .r3 (.imm 4)])) u _
  rw [WP.block_append_iff]
  refine WP.mono (copyW_ok (u := u) h.r1 h.r2 (by decide) (by decide) eS eD
    (by rw [h.rd, h.wr]; exact hr _ (by omega_arith)) (by rw [h.wr]; exact hw _ (by omega_arith)) (by decide))
    fun u₁ ⟨hrd₁, hwr₁, hsp₁, hg₁, hm₁⟩ => ?_
  refine wp_dp (op2_imm (by decide)) fun u₂ v₂ => wp_dp (op2_imm (by decide)) fun u₃ v₃ => ?_
  refine wp_subs (op2_imm (by decide)) fun u₄ v₄ z₄ => WP.block_nil ?_
  have r1₄ : u₄.gpr .r1 = S + BitVec.ofNat 32 (4 * (K - (n - 1))) := by
    rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, dpVal, hg₁ _ (by decide), h.r1, BitVec.add_assoc,
      add4, show 4 * (K - n) + 4 = 4 * (K - (n - 1)) by omega_arith]
  have r2₄ : u₄.gpr .r2 = Dd + BitVec.ofNat 32 (4 * (K - (n - 1))) := by
    rw [v₄.other _ (by decide), v₃.gpr, dpVal, v₂.other _ (by decide), hg₁ _ (by decide), h.r2, BitVec.add_assoc,
      add4, show 4 * (K - n) + 4 = 4 * (K - (n - 1)) by omega_arith]
  have r3₄ : u₄.gpr .r3 = BitVec.ofNat 32 (4 * (n - 1)) := by
    rw [v₄.gpr, v₃.other _ (by decide), v₂.other _ (by decide), hg₁ _ (by decide), h.r3]
    exact sub4 hp (by omega_arith)
  have hm₄ : u₄.mem = u.mem.writeW (State.addr Dd + BitVec.ofNat 64 (4 * (K - n)))
      (u.mem.readW (State.addr S + BitVec.ofNat 64 (4 * (K - n))) 32) := by
    rw [v₄.mem, v₃.mem, v₂.mem, hm₁]
  have hf₄ : Frame [⟨State.addr Dd, 4 * K⟩] u.mem u₄.mem := by
    rw [hm₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_arith) (by omega_arith))
  -- The word read is the source's on entry: the loop writes only the destination.
  have hsrc : Spec.Sha256.bytesAt u.mem (State.addr S + BitVec.ofNat 64 (4 * (K - n))) 4 =
      Spec.Sha256.bytesAt s.mem (State.addr S + BitVec.ofNat 64 (4 * (K - n))) 4 :=
    bytesAt_frame h.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hsep.sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith)
  have hb₄ : Spec.Sha256.bytesAt u₄.mem (State.addr Dd) (4 * (K - (n - 1))) =
      Spec.Sha256.bytesAt s.mem (State.addr S) (4 * (K - (n - 1))) := by
    rw [show 4 * (K - (n - 1)) = 4 * (K - n) + 4 by omega_arith, Proof.Hmac.Common.bytesAt_add,
      Proof.Hmac.Common.bytesAt_add, ← hsrc, ← h.bytes]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · exact bytesAt_frame (hm₄ ▸ (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Region.contains_self _ _) : Frame [⟨State.addr Dd + BitVec.ofNat 64 (4 * (K - n)), 4⟩] u.mem u₄.mem)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)) (by omega_arith)
    · rw [hm₄]; exact bytesAt_copied _ _ _
  have hz : isa.eval .ne u₄ = some (decide (n ≠ 1)) := by
    show some (!u₄.z) = _
    rw [z₄, v₃.other _ (by decide), v₂.other _ (by decide), hg₁ _ (by decide), h.r3]
    congr 1
    rcases (by omega_arith : n = 1 ∨ 2 ≤ n) with rfl | hn2
    · decide
    · have : BitVec.ofNat 32 (4 * n) - 4 ≠ 0 := ne4 hn2 (by omega_arith)
      simp only [show n ≠ 1 by omega_arith, ne_eq, not_false_eq_true, decide_true, Bool.not_eq_eq_eq_not,
        Bool.not_true, beq_eq_false_iff_ne]
      exact this
  have K₄ : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → u₄.gpr r = s.gpr r := fun r a b c d => by
    rw [v₄.other _ d, v₃.other _ c, v₂.other _ b, hg₁ _ a, h.other r a b c d]
  rcases (by omega_arith : n = 1 ∨ 2 ≤ n) with rfl | hn2
  · refine .inl ⟨by rw [hz]; rfl, by rw [v₄.rd, v₃.rd, v₂.rd, hrd₁, h.rd], by rw [v₄.wr, v₃.wr, v₂.wr, hwr₁, h.wr],
      by rw [v₄.sp, v₃.sp, v₂.sp, hsp₁, h.sp], K₄, h.frame.trans hf₄, ?_⟩
    have := hb₄; rwa [Nat.sub_self, Nat.sub_zero] at this
  · refine .inr ⟨by rw [hz, decide_eq_true (by omega_arith)], n - 1, by omega_arith,
      ⟨by omega_arith, by omega_arith, r1₄, r2₄, r3₄, by rw [v₄.rd, v₃.rd, v₂.rd, hrd₁, h.rd],
        by rw [v₄.wr, v₃.wr, v₂.wr, hwr₁, h.wr], by rw [v₄.sp, v₃.sp, v₂.sp, hsp₁, h.sp], K₄,
        h.frame.trans hf₄, hb₄⟩⟩

/-! ## Zeros -/

/-- The bytes of a zero word. -/
theorem bytesAt_writeW_zero (m : Mem) (p : Addr) {k : Nat} (hk : k ≤ 4) :
    Spec.Sha256.bytesAt (m.writeW p (0 : BitVec 32)) p k = List.replicate k 0 := by
  rw [List.eq_replicate_iff]
  refine ⟨by simp [Spec.Sha256.bytesAt], fun b hb => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  have hi := List.mem_range.mp hi
  have e : (p + BitVec.ofNat 64 i - p).toNat = i := by
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  simp only [Mem.writeW, Mem.write, e, show i < 32 / 8 by omega_arith, ite_true]
  apply BitVec.eq_of_toNat_eq; simp

/-- `k` zero words at `r8 + o`, from `r0`. -/
theorem zeros_ok (hL : L.Ok) {o : Nat} (ho : o + 68 ≤ 396) :
    ∀ k ≤ 17, ∀ {u : State}, Ctx L g m₀ u → u.gpr .r0 = 0 →
    WP isa (.block ((List.range k).map fun j => .str .r0 .r8 (o + 4 * j))) u fun u' =>
      Ctx L g m₀ u' ∧ u'.gpr = u.gpr ∧ Frame [⟨L.B + BitVec.ofNat 64 (24 + o), 68⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (24 + o)) (4 * k) = List.replicate (4 * k) 0
  | 0, _, u, hc, _ => WP.block_nil ⟨hc, rfl, Frame.refl _ _, rfl⟩
  | k + 1, hk, u, hc, h0 => by
    have hb := hL.B_fit
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zeros_ok hL ho k (by omega_arith) hc h0) fun u₁ ⟨hc₁, hg₁, hf₁, hb₁⟩ => ?_
    have e : State.addr (L.fp + BitVec.ofNat 32 (o + 4 * k)) = L.B + BitVec.ofNat 64 (24 + o + 4 * k) := by
      rw [hL.fpA (by omega_arith), Nat.add_assoc]
    refine wp_str (a := L.B + BitVec.ofNat 64 (24 + o + 4 * k)) (by omega_arith) (by rw [hc₁.r8]; exact e)
      (hc₁.inFrW (by omega_arith) (by omega_arith)) fun u₂ v₂ => WP.block_nil ?_
    have hm₂ : u₂.mem = u₁.mem.writeW (L.B + BitVec.ofNat 64 (24 + o + 4 * k)) (0 : BitVec 32) := by
      rw [v₂.mem, hg₁, h0]
    have hf₂ : Frame [⟨L.B + BitVec.ofNat 64 (24 + o + 4 * k), 4⟩] u₁.mem u₂.mem := by
      rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    refine ⟨hc₁.keep hL v₂.rd v₂.wr v₂.sp (fun r _ => by rw [v₂.gpr]) hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega_arith)),
      by rw [v₂.gpr, hg₁], hf₁.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr
        rw [show 24 + o + 4 * k = (24 + o) + 4 * k from rfl]; exact Offset.sub _ (by omega_arith) (by omega_arith)⟩), ?_⟩
    rw [show 4 * (k + 1) = 4 * k + 4 by omega_arith, Proof.Hmac.Common.bytesAt_add, Offset.add_add,
      ← List.replicate_append_replicate]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · rw [← hb₁]
      exact bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)
    · rw [hm₂]; exact bytesAt_writeW_zero _ _ (Nat.le_refl _)

/-! ## `min(D, e)` -/

theorem toNat_ofNat_lt {x : Nat} (h : x < 2 ^ 32) : (BitVec.ofNat 32 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The branch-free minimum: `D - ((D - e) & -(D ≥ e))`. -/
theorem minE_val (D e : Nat) (hD : D < 2 ^ 32) (he : e < 2 ^ 32) :
    BitVec.ofNat 32 D - ((BitVec.ofNat 32 D - BitVec.ofNat 32 e) &&&
      ((0 : BitVec 32) - (0 + 0 + (if decide ((BitVec.ofNat 32 e).toNat ≤ (BitVec.ofNat 32 D).toNat) = true
        then 1 else 0)))) = BitVec.ofNat 32 (min D e) := by
  rw [toNat_ofNat_lt hD, toNat_ofNat_lt he]
  by_cases h : e ≤ D
  · simp only [decide_eq_true h, ↓reduceIte]
    rw [show (0 : BitVec 32) + 0 + 1 = 1 from rfl,
      show (0 : BitVec 32) - 1 = BitVec.allOnes 32 from rfl, BitVec.and_allOnes, Nat.min_eq_right h]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_arith
  · simp only [decide_eq_false h, Bool.false_eq_true, ↓reduceIte]
    rw [Nat.min_eq_left (by omega_arith)]
    simp

/-- The registers of the copy: the digest (`r1`), the destination
`r8 + o + e - m` (`r2`) and its `m = min(D, e)` bytes (`r3`). -/
theorem minE_ok (hq : HOk P L) {u : State} (hc : Ctx L g m₀ u) {o e : Nat} (he : e ≤ 66)
    (heo : encodable (BitVec.ofNat 32 o) = true) :
    WP isa (.block (Cfg.dOut .r3 ++
      ([.subs .r0 .r3 (.imm (BitVec.ofNat 32 e)), .mov .r1 (.imm 0), .adc .r1 .r1 (.imm 0), .mov .r2 (.imm 0),
        .dp .sub .r1 .r2 (.reg .r1), .dp .and .r0 .r0 (.reg .r1), .dp .sub .r3 .r3 (.reg .r0),
        .dp .add .r2 .r8 (.imm (BitVec.ofNat 32 o)), .dp .add .r2 .r2 (.imm (BitVec.ofNat 32 e)),
        .dp .sub .r2 .r2 (.reg .r3), .mov .r1 (.reg .r10)] : List Instr))) u fun u' =>
      Ctx L g m₀ u' ∧ u'.mem = u.mem ∧ u'.gpr .r1 = u.gpr .r10 ∧
      u'.gpr .r2 = L.fp + BitVec.ofNat 32 (o + e - min P.F.H.D e) ∧
      u'.gpr .r3 = BitVec.ofNat 32 (min P.F.H.D e) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → u'.gpr r = u.gpr r) := by
  have hD := P.sizes
  have hee : encodable (BitVec.ofNat 32 e) = true := by revert e; decide
  refine dOut_ok hq hc (d := .r3) (by decide) fun u₁ c₁ m₁ v₁ k₁ => ?_
  refine wp_subsC (op2_imm hee) fun u₂ v₂ c₂ => wp_movC (op2_imm (by decide)) fun u₃ v₃ c₃ => ?_
  refine wp_adc (op2_imm (by decide)) fun u₄ v₄ => wp_mov (op2_imm (by decide)) fun u₅ v₅ => ?_
  refine wp_dp (op2_reg _ _) fun u₆ v₆ => wp_dp (op2_reg _ _) fun u₇ v₇ => wp_dp (op2_reg _ _) fun u₈ v₈ => ?_
  have c₈ : Ctx L g m₀ u₈ := ((((((c₁.upd v₂ (by decide)).upd v₃ (by decide)).upd v₄ (by decide)).upd v₅
    (by decide)).upd v₆ (by decide)).upd v₇ (by decide)).upd v₈ (by decide)
  have r3₈ : u₈.gpr .r3 = BitVec.ofNat 32 (min P.F.H.D e) := by
    rw [v₈.gpr, dpVal, v₇.gpr, dpVal, v₇.other _ (by decide), v₆.gpr, dpVal, v₆.other _ (by decide),
      v₆.other _ (by decide), v₅.gpr, v₅.other _ (by decide), v₅.other _ (by decide), v₅.other _ (by decide),
      v₄.gpr, v₄.other _ (by decide), v₄.other _ (by decide), v₃.gpr, v₃.other _ (by decide), v₃.other _ (by decide),
      v₂.gpr, v₂.other _ (by decide), c₃, c₂, v₁]
    exact minE_val _ _ (by anums) (by omega_arith)
  have h10₈ : u₈.gpr .r10 = u.gpr .r10 := by
    rw [v₈.other _ (by decide), v₇.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide),
      v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), k₁ _ (by decide)]
  refine wp_dp (op2_imm heo) fun u₉ v₉ => wp_dp (op2_imm hee) fun u₁₀ v₁₀ => ?_
  refine wp_dp (op2_reg _ _) fun u₁₁ v₁₁ => wp_mov (op2_reg _ _) fun u₁₂ v₁₂ => WP.block_nil ?_
  have hc₁₂ : Ctx L g m₀ u₁₂ := ((((c₈.upd v₉ (by decide)).upd v₁₀ (by decide)).upd v₁₁ (by decide)).upd v₁₂
    (by decide))
  have hm : u₁₂.mem = u.mem := by
    rw [v₁₂.mem, v₁₁.mem, v₁₀.mem, v₉.mem, v₈.mem, v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, m₁]
  have h10 : u₁₁.gpr .r10 = u.gpr .r10 := by
    rw [v₁₁.other _ (by decide), v₁₀.other _ (by decide), v₉.other _ (by decide), h10₈]
  have r3₁₀ : u₁₀.gpr .r3 = BitVec.ofNat 32 (min P.F.H.D e) := by
    rw [v₁₀.other _ (by decide), v₉.other _ (by decide), r3₈]
  refine ⟨hc₁₂, hm, by rw [v₁₂.gpr, h10], ?_, ?_, fun r a b c d => by
    rw [v₁₂.other _ b, v₁₁.other _ c, v₁₀.other _ c, v₉.other _ c, v₈.other _ d, v₇.other _ a, v₆.other _ b,
      v₅.other _ c, v₄.other _ b, v₃.other _ b, v₂.other _ a, k₁ _ d]⟩
  · have hm' : min P.F.H.D e ≤ e := Nat.min_le_right _ _
    rw [v₁₂.other _ (by decide), v₁₁.gpr, dpVal, v₁₀.gpr, dpVal, v₉.gpr, dpVal, r3₁₀, c₈.r8,
      BitVec.add_assoc, BitVec.ofNat_add_ofNat,
      show o + e = (o + e - min P.F.H.D e) + min P.F.H.D e by omega_arith, ← BitVec.ofNat_add_ofNat,
      ← BitVec.add_assoc, BitVec.add_sub_cancel, show o + e - min P.F.H.D e + min P.F.H.D e - min P.F.H.D e =
        o + e - min P.F.H.D e by omega_arith]
  · rw [v₁₂.other _ (by decide), v₁₁.other _ (by decide), r3₁₀]

/-! ## The copy -/

theorem Ctx.dgBytes' (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {n : Nat} (hn : n ≤ dn) :
    Spec.Sha256.bytesAt t.mem (State.addr L.dg) n = Spec.Sha256.bytesAt m₀ (State.addr L.dg) n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hc.dg_byte hL (by have := List.mem_range.mp hi; omega)

/-- Bytes within bytes. -/
theorem bytesAt_slice (m : Mem) (p : Addr) {a n k : Nat} (h : a + n ≤ k) :
    Spec.Sha256.bytesAt m (p + BitVec.ofNat 64 a) n = ((Spec.Sha256.bytesAt m p k).drop a).take n := by
  rw [show k = a + (n + (k - a - n)) by omega, Proof.Hmac.Common.bytesAt_add, Proof.Hmac.Common.bytesAt_add,
    List.drop_left' (Proof.Hmac.Common.bytesAt_length _ _ _), List.take_left' (Proof.Hmac.Common.bytesAt_length _ _ _)]

theorem length_bytesAt' (m : Mem) (p : Addr) (n : Nat) : (Spec.Sha256.bytesAt m p n).length = n := by
  simp [Spec.Sha256.bytesAt]

/-- Zeros with `X` copied over the bytes from `e - m` to `e`. -/
theorem zeros_copy {u u' : Mem} {base : Addr} {e m : Nat} {X : List Byte}
    (hz : Spec.Sha256.bytesAt u base 68 = List.replicate 68 0)
    (hf : Frame [⟨base + BitVec.ofNat 64 (e - m), m⟩] u u')
    (hb : Spec.Sha256.bytesAt u' (base + BitVec.ofNat 64 (e - m)) m = X) (hx : X.length = m) (hm : m ≤ e)
    (he : e ≤ 68) :
    Spec.Sha256.bytesAt u' base 68 = List.replicate (e - m) 0 ++ X ++ List.replicate (68 - e) 0 := by
  have hz' : ∀ a n, a + n ≤ 68 → Spec.Sha256.bytesAt u (base + BitVec.ofNat 64 a) n = List.replicate n 0 :=
    fun a n h => by
      rw [bytesAt_slice _ _ (k := 68) h, hz, List.drop_replicate, List.take_replicate, Nat.min_eq_left (by omega)]
  rw [show (68 : Nat) = (e - m) + (m + (68 - e)) by omega, Proof.Hmac.Common.bytesAt_add,
    Proof.Hmac.Common.bytesAt_add, Offset.add_add, List.append_assoc, show (e - m) + (m + (68 - e)) - e = 68 - e by omega]
  refine congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) hb ?_)
  · rw [bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)) (by omega)]
    have := hz' 0 (e - m) (by omega)
    rwa [BitVec.add_zero] at this
  · rw [bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) (by omega)]
    exact hz' _ _ (by omega)

/-- `dgCopy o e`: the 68 bytes at `r8 + o` are `e - m` zeros, the digest's
first `m = min(D, e)` bytes, and zeros. -/
theorem dgCopy_ok (hL : L.Ok) (hq : HOk P L) (hdn : P.F.H.D ≤ dn) {t : State} (hc : Ctx L g m₀ t)
    (h10 : t.gpr .r10 = L.dg) {o e : Nat} (ho : o + 68 ≤ 396) (he : e ≤ 66)
    (heo : encodable (BitVec.ofNat 32 o) = true) (hm4 : min P.F.H.D e % 4 = 0) (hm : 4 ≤ min P.F.H.D e) :
    WP isa (Cfg.dgCopy o e) t fun t' => Ctx L g m₀ t' ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → t'.gpr r = t.gpr r) ∧
      Frame [⟨L.B + BitVec.ofNat 64 (24 + o), 68⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (24 + o)) 68 =
        List.replicate (e - min P.F.H.D e) 0 ++ Spec.Sha256.bytesAt m₀ (State.addr L.dg) (min P.F.H.D e) ++
          List.replicate (68 - e) 0 := by
  have hD := P.sizes
  have hb := hL.B_fit
  have hng := hL.ng
  have hfp := fp_fit hL
  refine WP.seq ?_
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_mov (op2_imm (by decide)) fun u₁ v₁ => ?_
  have hc₁ := hc.upd v₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zeros_ok hL ho 17 (Nat.le_refl _) hc₁ v₁.gpr) fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  refine WP.mono (minE_ok hq hc₂ he (o := o) heo)
    fun u₃ ⟨hc₃, hm₃, h1₃, h2₃, h3₃, hg₃⟩ => ?_
  have hdg₃ : u₃.gpr .r1 = L.dg := by rw [h1₃, hg₂, v₁.other _ (by decide), h10]
  have eD : State.addr (L.fp + BitVec.ofNat 32 (o + e - min P.F.H.D e)) = L.B + BitVec.ofNat 64 (24 + o + (e - min P.F.H.D e)) := by
    rw [hL.fpA (by omega_arith), show 24 + (o + e - min P.F.H.D e) = 24 + o + (e - min P.F.H.D e) by omega_arith]
  have hdst : (L.fp + BitVec.ofNat 32 (o + e - min P.F.H.D e)).toNat + 4 * (min P.F.H.D e / 4) ≤ 2 ^ 32 := by
    rw [fp_toNat hL (by omega_arith)]; have := L.sp.isLt; have := hL.nA; have := hL.nB; omega_arith
  refine WP.mono (copyLoop_ok (K := min P.F.H.D e / 4) (by omega_arith) (by omega_arith) hdg₃ h2₃
    (by rw [h3₃, show 4 * (min P.F.H.D e / 4) = min P.F.H.D e by omega_arith]) (by omega_arith) hdst
    (fun j hj => by
      have : 4 * j + 4 ≤ min P.F.H.D e := by omega
      exact hc₃.inDg (o := 4 * j) (n := 4) (by omega) (by omega))
    (fun j hj => by rw [eD, Offset.add_add]; exact hc₃.inFrW (by omega_arith) (by omega_arith))
    (by rw [eD]; exact ((hL.kg.sub_left (Offset.sub_base _ (by omega_arith))).symm.sub_left
      (Region.sub_prefix (by omega_arith)))))
    fun u₄ ⟨hrd₄, hwr₄, hsp₄, hg₄, hf₄, hb₄⟩ => ?_
  rw [eD, show 4 * (min P.F.H.D e / 4) = min P.F.H.D e by omega_arith] at hf₄ hb₄
  have hc₄ : Ctx L g m₀ u₄ := hc₃.keep hL hrd₄ hwr₄ hsp₄ (fun r hr => hg₄ r (by revert hr r; decide)
      (by revert hr r; decide) (by revert hr r; decide) (by revert hr r; decide)) hf₄
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega_arith))
  refine ⟨hc₄, fun r a b c d => ?_, ?_, ?_⟩
  · rw [hg₄ r a b c d, hg₃ r a b c d, hg₂, v₁.other _ a]
  · rw [hm₃] at hf₄
    have hf₂' : Frame [⟨L.B + BitVec.ofNat 64 (24 + o), 68⟩] t.mem u₂.mem := by rw [← v₁.mem]; exact hf₂
    exact hf₂'.trans (hf₄.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)⟩)
  · have hf₄' : Frame [⟨L.B + BitVec.ofNat 64 (24 + o) + BitVec.ofNat 64 (e - min P.F.H.D e), min P.F.H.D e⟩]
        u₂.mem u₄.mem := by rw [Offset.add_add, ← hm₃]; exact hf₄
    rw [← Offset.add_add, hc₃.dgBytes' hL (by omega_arith)] at hb₄
    rw [← List.append_assoc]
    exact zeros_copy (by rw [show 68 = 4 * 17 from rfl]; exact hb₂) hf₄' hb₄ (length_bytesAt' _ _ _)
      (Nat.min_le_right _ _) (by omega_arith)

/-! ## The digest's integer, `h` and `core`'s digest -/

/-- `bits2int` of a hash of `D` bytes, for a curve whose `n` has `8 Q` bits:
the number of its first `min(D, Q)` bytes. -/
theorem hashToInt_min {C : Spec.Weierstrass.Curve} {Q D : Nat} (hq : Spec.Ecdsa.nBits C = 8 * Q) (hn : C.n ≠ 0)
    {h : List Byte} (hl : h.length = D) :
    Spec.Ecdsa.hashToInt C h = Spec.Weierstrass.ofBytes (h.take (min D Q)) := by
  by_cases hDQ : Q ≤ D
  · rw [Nat.min_eq_right hDQ]; exact hashToInt_takeQ hq (by omega)
  · rw [Nat.min_eq_left (by omega), List.take_of_length_le (by omega)]
    exact (hashToInt_short (by omega) hn).1

theorem take_zeros (a c : Nat) {X : List Byte} {b : Nat} (hx : X.length = b) :
    (List.replicate a 0 ++ X ++ List.replicate c 0).take (a + b) = List.replicate a 0 ++ X := by
  rw [List.append_assoc, List.take_append, List.length_replicate, List.take_of_length_le (by simp),
    Nat.add_sub_cancel_left, List.take_append, hx, Nat.sub_self, List.take_zero, List.append_nil,
    List.take_of_length_le (by omega)]

/-- `core`'s digest: `h`, or, if `wide`, the digest shifted (at `r8 + fX`). -/
abbrev dgAddr (P : RfcHash) {dn : Nat} (L : Lay dn) : Addr :=
  if P.R.wide then L.B + BitVec.ofNat 64 352 else L.B + BitVec.ofNat 64 152

/-- The digest. -/
abbrev hBOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m₀ : Mem) : List Byte :=
  Spec.Sha256.bytesAt m₀ (State.addr L.dg) P.F.H.D

/-- The digest's integer. -/
abbrev eOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m₀ : Mem) : Nat := Spec.Ecdsa.hashToInt P.R.E.C (hBOf P L m₀)

/-- `core`'s digest is the digest's integer, modulo `n` (as `signWith` takes it). -/
def DgOk (P : RfcHash) {dn : Nat} (L : Lay dn) (m₀ m : Mem) : Prop :=
  Spec.Ecdsa.hashToInt P.R.E.C (Spec.Sha256.bytesAt m (dgAddr P L) P.Q) % P.R.E.C.n = eOf P L m₀ % P.R.E.C.n

theorem sh_zero (P : RfcHash) : (cfgOf P).sh = 0 ↔ P.R.wide = false := by
  have := P.R.nBits_len
  show P.R.sh = 0 ↔ _
  cases hw : P.R.wide
  · have := P.R.sizesA hw; simp only [iff_true]; omega
  · have := P.R.sizesW hw; simp only [Bool.true_eq_false, iff_false]; omega

/-- After step 1: `h` and `core`'s digest. -/
theorem digest_ok (hL : L.Ok) (hq : HOk P L) (hdn : P.F.H.D = dn) {t : State} (hc : Ctx L g m₀ t)
    (h10 : t.gpr .r10 = L.dg) :
    WP isa (cfgOf P).digest t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 24, 396⟩, ⟨State.addr L.scr + BitVec.ofNat 64 2560, 72⟩] t.mem u.mem ∧
      hOf L P.Q u.mem = Spec.Ecdsa.Rfc6979.bits2octets P.R.E.C (hBOf P L m₀) ∧ DgOk P L m₀ u.mem := by
  have hD := P.sizes
  have hQ := P.wsizes
  have hb := hL.B_fit
  have hnb := P.R.nBits_len
  have hlen : (hBOf P L m₀).length = P.F.H.D := length_bytesAt' _ _ _
  refine WP.seq (WP.mono (dgCopy_ok (o := fH) (e := P.Q) hL hq (by omega) hc h10 (by decide) (by omega)
    (by decide) ?_ (by omega)) fun u ⟨hcu, hgu, hfu, hbu⟩ => ?_)
  · cases hw : P.R.wide
    · have := (P.sizesA hw).1; omega
    · have := P.sizesW hw; omega
  have hbu' : Spec.Sha256.bytesAt u.mem (hA L) P.Q =
      List.replicate (P.Q - min P.F.H.D P.Q) 0 ++ Spec.Sha256.bytesAt m₀ (State.addr L.dg) (min P.F.H.D P.Q) := by
    have := take_zeros (P.Q - min P.F.H.D P.Q) (68 - P.Q) (length_bytesAt' m₀ (State.addr L.dg) (min P.F.H.D P.Q))
    rw [show P.Q - min P.F.H.D P.Q + min P.F.H.D P.Q = P.Q by omega] at this
    rw [hA, bytesAt_take _ _ (show P.Q ≤ 68 by omega), show (152 : Nat) = 24 + fH from rfl, hbu, this]
  have hdg : Spec.Sha256.bytesAt m₀ (State.addr L.dg) (min P.F.H.D P.Q) = (hBOf P L m₀).take (min P.F.H.D P.Q) :=
    bytesAt_take _ _ (Nat.min_le_left _ _)
  have h10u : u.gpr .r10 = L.dg := by rw [hgu _ (by decide) (by decide) (by decide) (by decide), h10]
  cases hw : P.R.wide
  · -- `h = X mod n`, and `core` reads `h`.
    have hsh : (cfgOf P).sh = 0 := (sh_zero P).mpr hw
    obtain ⟨hn8, -, hnb8, h2n⟩ := P.R.sizesA hw
    have e8 : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := hnb8
    have hQk : P.Q = 4 * P.k32 := (P.sizesA hw).1
    simp only [hsh, ite_true]
    refine WP.mono (reduce_ok hw hL hcu) fun u' ⟨hcu', hfu', hbu''⟩ => ⟨hcu', ?_, ?_, ?_⟩
    · refine (hfu.sub fun r hr => ⟨_, List.mem_cons_self, ?_⟩).trans (hfu'.sub fun r hr => ⟨_, List.mem_cons_self, ?_⟩)
      · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by decide) (by decide)
      · simp only [HW, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.sub _ (by decide) (by decide)
        · exact Offset.sub _ (by decide) (by omega)
    · -- `h`'s number is the digest's integer modulo `n`.
      have hX : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (hA L) P.Q) = eOf P L m₀ := by
        rw [hbu', ofBytes_zeros, hdg, eOf, hashToInt_min e8 P.R.n_ne hlen]
      rw [← hQk] at hbu''
      rw [hX] at hbu''
      have hl' : (Spec.Sha256.bytesAt u'.mem (hA L) P.Q).length = P.Q := length_bytesAt' _ _ _
      rw [hOf, ← hA, ← toBytes_ofBytes (Spec.Sha256.bytesAt u'.mem (hA L) P.Q), hl', hbu'',
        Spec.Ecdsa.Rfc6979.bits2octets, Spec.Ecdsa.Rfc6979.int2octets, Spec.Ecdsa.Rfc6979.bits2int, rlenQ e8]
    · have hX : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (hA L) P.Q) = eOf P L m₀ := by
        rw [hbu', ofBytes_zeros, hdg, eOf, hashToInt_min e8 P.R.n_ne hlen]
      rw [← hQk, hX] at hbu''
      unfold DgOk
      simp only [dgAddr, hw, Bool.false_eq_true, ite_false]
      rw [hashToInt_takeQ e8 (by rw [length_bytesAt']), List.take_of_length_le (by rw [length_bytesAt']),
        ← hA, hbu'', Nat.mod_mod]
  · -- P-521: `h` is the digest's integer; `core`'s digest, it shifted left by `sh`.
    have hsh : (cfgOf P).sh ≠ 0 := fun h => by rw [(sh_zero P).mp h] at hw; exact absurd hw (by decide)
    obtain ⟨hw9, hQ66, hnb521⟩ := P.R.sizesW hw
    have hsh7 : (cfgOf P).sh = 7 := by show P.R.sh = 7; have := P.R.nBits_len; omega
    have hQ' : P.Q = 66 := hQ66
    have hfX : fX = 328 := rfl
    have hmD : min P.F.H.D P.Q = P.F.H.D := Nat.min_eq_left (by omega)
    have hmX : min P.F.H.D (P.Q - 1) = P.F.H.D := Nat.min_eq_left (by omega)
    simp only [hsh, ite_false]
    rw [show (cfgOf P).len = P.Q from rfl, hsh7]
    refine WP.seq (WP.mono (dgCopy_ok (o := fX) (e := P.Q - 1) hL hq (by omega) hcu h10u (by decide) (by omega)
      (by decide) (by rw [hmX]; omega) (by rw [hmX]; omega)) fun u₂ ⟨hc₂, _, hf₂, hb₂⟩ => ?_)
    refine WP.mono (conv_ok hL hw hc₂ (o := fX) (s := 8 - 7) (by decide) (by decide) (by decide) (by decide))
      fun u₃ ⟨hc₃, _, hf₃, hb₃⟩ => ⟨hc₃, ?_, ?_, ?_⟩
    · refine (hfu.sub fun r hr => ⟨_, List.mem_cons_self, ?_⟩).trans
        ((hf₂.sub fun r hr => ⟨_, List.mem_cons_self, ?_⟩).trans (hf₃.sub fun r hr => ?_))
      · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by decide) (by decide)
      · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by decide) (by decide)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, sub_refl _⟩
        · exact ⟨_, List.mem_cons_self, Offset.sub _ (by decide) (by omega)⟩
    · -- `h` is the digest after zeros, kept by the second copy and the shift.
      have hH : hOf L P.Q u₃.mem = hOf L P.Q u.mem := by
        refine (bytesAt_frame hf₃ (fun r hr => ?_) (by omega)).trans (bytesAt_frame hf₂ (fun r hr => ?_) (by omega))
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hL.stk_scr (by omega) (by omega)
          · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
        · simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
      rw [hH, hOf, ← hA, hbu', hmD, bits2octets_short (R := P.Q) (by omega) (by omega) (by rw [hlen]; omega)
        P.R.n_ne, hlen]
    · -- `core`'s digest: the digest's integer `x`, times `2^8`, shifted right by 1.
      have hx := ofBytes_lt (hBOf P L m₀)
      rw [hlen] at hx
      have hX : Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (24 + fX)) P.Q =
          List.replicate (P.Q - 1 - P.F.H.D) 0 ++ hBOf P L m₀ ++ List.replicate 1 0 := by
        have := take_zeros (P.Q - 1 - P.F.H.D) (68 - (P.Q - 1)) (length_bytesAt' m₀ (State.addr L.dg) P.F.H.D)
        rw [bytesAt_take _ _ (show P.Q ≤ 68 by omega), hb₂, hmX]
        rw [show P.Q = (P.Q - 1 - P.F.H.D + P.F.H.D) + 1 by omega, List.append_assoc,
          show 68 - (P.Q - 1 - P.F.H.D + P.F.H.D + 1 - 1) = 1 + (68 - P.Q) by omega,
          ← List.replicate_append_replicate, ← List.append_assoc, ← List.append_assoc, List.take_append,
          List.take_of_length_le (by simp [length_bytesAt']; omega),
          show P.Q - 1 - P.F.H.D + P.F.H.D + 1 - 1 - P.F.H.D = P.Q - 1 - P.F.H.D by omega]
        simp [length_bytesAt']
        omega
      have hv : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (24 + fX)) P.Q) >>>
          (8 - 7) = Spec.Weierstrass.ofBytes (hBOf P L m₀) * 2 ^ 7 := by
        rw [hX, ofBytes_append_zeros, ofBytes_zeros, Nat.shiftRight_eq_div_pow,
          show 8 * 1 = 7 + 1 from rfl, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by decide)]
      unfold DgOk
      simp only [dgAddr, hw, ite_true]
      rw [show (352 : Nat) = 24 + fX from rfl, hb₃, hv, hashToInt_takeR (R := P.Q) (by omega)
        (by simp [Spec.Weierstrass.toBytes]), List.take_of_length_le (by simp [Spec.Weierstrass.toBytes]),
        ofBytes_toBytes _ _ (by
          calc _ < 2 ^ (8 * P.F.H.D) * 2 ^ 7 := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos _)
            _ ≤ 2 ^ (8 * P.Q) := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)),
        show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = 7 by omega, Nat.shiftRight_eq_div_pow,
        Nat.mul_div_cancel _ (Nat.two_pow_pos _), eOf, (hashToInt_short (by rw [hlen]; omega) P.R.n_ne).1]

end VG.Proof.Ecdsa.Rfc6979.Arm
