module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.PointOps
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Basic
import VerifiedGarbage.Proof.Ed25519.RISCV64.Freeze
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Power
public import VerifiedGarbage.Proof.X25519.Invert
import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.X25519.RISCV64.Invert
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointTable
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointPowers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldVerified
import VerifiedGarbage.Proof.Ed25519.RISCV64.SpecConv
import VerifiedGarbage.Proof.Ed25519.RISCV64.Base
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Freeze
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Field
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline

/-!
# Ed25519 on RISCV64: inversion and encoding

A call of `vg_gf25519_r32_pow250` (`power250_ok`), the inversion of slot 2
into slot 15 (`invert_ok`: the chain, five squarings, a product), the
affine coordinates (`pointAffine_ok`), and the encoding of the point at
`FR` (`pointEncode_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Proof.X25519
open VG.Spec.X25519 (P)
open VG.Proof.X25519 (pw sqn)
open VG.Proof.X448.RISCV64.R64 (clob64)

/-- A slot's element from the residue of its value. -/
theorem env_of_val {m m' : Mem} {b : Addr} {i j : Slot} {e : Nat}
    (h : V m' b (offset i) % P = V m b (offset j) ^ e % P) : env m' b i = pw (env m b j) e := by
  apply Fin.ext
  simp only [env, FS, Proof.X25519.toFe_val, pw, Fin.val_ofNat]
  rw [h, ← Nat.pow_mod]

/-- The slots below `pow250`'s results keep their elements. -/
theorem env_keeps₂ {b : Addr} {m m' : Mem} (h : Spec.X25519.Field32.Keeps₂ b m m') {i : Slot} (hi : i.val < 14) :
    env m' b i = env m b i := by
  have hs := slot_range i
  unfold env FS
  rw [← read_V, ← read_V]
  refine congrArg (fun v : BitVec (8 * 32) => Proof.X25519.toFe v.toNat) (Mem.read_congr fun j hj => ?_)
  have ho : offset i = 64 + 32 * i.val := rfl
  rw [Offset.add_add]
  exact h (offset i + j) (by simp only [Spec.X25519.Field32.wsBytes]; omega_arith)
    (by simp only [Spec.X25519.Field32.eAt]; omega_arith)

/-- `vg_gf25519_r32_pow250` never writes `a0`. -/
theorem pow250Fn_a0 : ∀ i ∈ instrs pow250Fn, dstOf i ≠ some Reg.a0 := by
  have nw : ((instrs pow250Fn).all fun i => dstOf i != some Reg.a0) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp nw i hi

/-- **A call of `vg_gf25519_r32_pow250`**: slot 15 `z^(2^250 - 1)` and slot 14 `z^11`, for `z` in
slot 2; slots 0–13 kept. -/
theorem power250_ok {b : Addr} {s : State} (hc : Ctx8 b s) :
    WP isa power250 s fun t => Keep b s t ∧
      env t.mem b 15 = pw (env s.mem b 2) (2 ^ 250 - 1) ∧ env t.mem b 14 = pw (env s.mem b 2) 11 ∧
      ∀ i : Slot, i.val < 14 → env t.mem b i = env s.mem b i := by
  unfold power250
  refine WP.seq (wp_mv fun s1 u1 => WP.block_nil ?_)
  have e0 : s1.gpr .a0 = b := by rw [u1.gpr, hc.a3]
  have hr1 : Rest [.a0] s s1 := u1.rest (by decide)
  have g : ∀ q, q ∉ linkRegs → (s1.callEntry.withRegions [] [⟨b, 4096⟩]).gpr q = s1.gpr q :=
    fun q hq => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  have hw1 : Covers [⟨b, 4096⟩] s1.wr := hc.ws.of_rest hr1
  refine WP.seq (WP.call (k := powRV) pow_ok' (rd := []) (wr := [⟨b, 4096⟩])
    ⟨rfl, by rw [g _ (by decide), e0]; rfl,
      by rw [g _ (by decide), e0]; exact hc.al⟩
    (by rw [List.nil_append]; exact hw1.right) hw1 ?_ (by decide +kernel))
  intro t hrd hwr hsp hfr hpres hg ⟨h15, h14, hks⟩
  have c0 : (s1.callEntry.withRegions [] [⟨b, 4096⟩]).gpr .a0 = b := by rw [g _ (by decide), e0]
  simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr] at h15 h14 hks
  rw [show (s1.callEntry.gpr .a0) = b from c0, u1.mem] at h15 h14 hks
  have ha0 : t.gpr .a0 = b := by rw [hg .a0 (by decide) pow250Fn_a0, e0]
  -- The elements, as the contract reads them.
  have hv : ∀ i : Slot, ∀ {m : Mem}, Spec.X25519.Field32.valAt m b (BitVec.ofNat 32 (offset i)) = V m b (offset i) :=
    fun i m => valAt_ofNat m b i
  refine wp_mv fun t1 v1 => WP.block_nil ⟨⟨⟨fun q hq => ?_, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
  · by_cases h3 : q = .a3
    · subst h3
      rw [v1.gpr, ha0, hc.a3]
    · rw [v1.other _ h3, hpres q (by revert hq h3; cases q <;> decide), hr1.gpr q (by revert hq; cases q <;> decide)]
  · rw [v1.rd, hrd, u1.rd]
  · rw [v1.wr, hwr, u1.wr]
  · rw [v1.sp, hsp, u1.sp]
  · rw [v1.mem]
    intro x hx
    have hnf := hx _ (List.mem_singleton_self _)
    by_cases hw : (⟨b, 4096⟩ : Region).Contains x 1
    · have hi : (x - b).toNat + 1 ≤ 4096 := hw
      have hx' : x = b + BitVec.ofNat 64 (x - b).toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      have hlo : (x - b).toNat < 64 ∨ 1024 ≤ (x - b).toNat := by
        by_contra hc
        refine hnf ?_
        rw [hx']
        exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)
      rw [hx']
      exact hks _ (by simp only [Spec.X25519.Field32.wsBytes]; omega_arith)
        (by simp only [Spec.X25519.Field32.eAt, Spec.X25519.Field32.ownEnd]; omega_arith)
    · rw [← u1.mem]
      exact hfr x fun r hr => by rw [List.mem_singleton.mp hr]; exact hw
  · rw [v1.mem]
    rw [show Spec.X25519.Field32.oAt = offset 15 from rfl, show Spec.X25519.Field32.aAt = offset 2 from rfl,
      hv, hv] at h15
    exact env_of_val h15
  · rw [v1.mem]
    rw [show Spec.X25519.Field32.eAt = offset 14 from rfl, show Spec.X25519.Field32.aAt = offset 2 from rfl,
      hv, hv] at h14
    exact env_of_val h14
  · intro i hi
    rw [v1.mem]; exact env_keeps₂ hks hi

/-- `sqnLoop o n`: slot `o` squared `n` times. -/
theorem sqnLoop_ok {b : Addr} {s : State} (hc : Ctx b s) (o : Slot) (ho : 14 ≤ o.val) {n : Nat} (hn : 1 ≤ n)
    (hn' : n < 2048) :
    WP isa (sqnLoop o n) s fun t =>
      Rest (.t1 :: clob64) s t ∧ Frame [PR b] s.mem t.mem ∧
      env t.mem b = Function.update (env s.mem b) o (sqn (env s.mem b o) n) := by
  unfold sqnLoop
  refine WP.seq (wp_li (by omega_arith) fun s1 u1 => WP.block_nil ?_)
  refine sqLoop_ok hc o ho (env s.mem b o) n hn' n s1 hn (Nat.le_refl _) (u1.rest (by decide))
    (by rw [u1.mem]; exact Frame.refl _ _) u1.gpr ?_
  rw [u1.mem, Nat.sub_self]
  exact (Function.update_eq_self _ _).symm

theorem inv_exp : (2 ^ 250 - 1) * 2 ^ 5 + 11 = P - 2 := by decide

/-- **The inverse of slot 2**, into slot 15; slots 0–13 kept. -/
theorem invert_ok {b : Addr} {s : State} (hc : Ctx8 b s) :
    WP isa Impl.Ed25519.RISCV64.invert s fun t => Keep b s t ∧
      env t.mem b 15 = Spec.X25519.pow (env s.mem b 2) (P - 2) ∧
      ∀ i : Slot, i.val < 14 → env t.mem b i = env s.mem b i := by
  unfold Impl.Ed25519.RISCV64.invert
  refine WP.seq (WP.mono (power250_ok hc) fun t1 ⟨k1, e15, e14, ek⟩ => ?_)
  have hc1 : Ctx8 b t1 := hc.of_keep k1
  refine WP.seq (WP.mono (sqnLoop_ok hc1.ctx 15 (by decide) (n := 5) (by decide) (by decide))
    fun t2 ⟨r2, f2, e2⟩ => ?_)
  have hc2 : Ctx8 b t2 := hc1.of_rest r2 (by decide)
  refine WP.mono (mulCall_ok hc2.ctx hc2.ws 15 15 14) fun t3 ⟨k3, e3⟩ => ⟨?_, ?_, fun i hi => ?_⟩
  · refine k1.trans (Keep.trans ⟨r2.mono (by decide), f2.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩⟩ k3)
    rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
  · rw [e3, Function.update_self, e2, Function.update_self, Function.update_of_ne (by decide), e15, e14,
      Proof.X25519.sqn_pw, Proof.X25519.pw_mul, inv_exp, Proof.X25519.pow_pw]
  · have h15 : i ≠ 15 := fun h => by subst h; exact absurd hi (by decide)
    rw [e3, Function.update_of_ne h15, e2, Function.update_of_ne h15, ek i hi]

theorem affine_eval (e : Env) :
    evalOps affineOps e 0 = e 0 * e 15 ∧ evalOps affineOps e 1 = e 1 * e 15 := ⟨rfl, rfl⟩

/-- **The affine coordinates** `x = X/Z`, `y = Y/Z` into slots 0 and 1. -/
theorem pointAffine_ok {b : Addr} {s : State} (hc : Ctx8 b s) :
    WP isa pointAffine s fun t => Keep b s t ∧
      env t.mem b 0 = env s.mem b 0 * Spec.X25519.pow (env s.mem b 2) (P - 2) ∧
      env t.mem b 1 = env s.mem b 1 * Spec.X25519.pow (env s.mem b 2) (P - 2) := by
  unfold pointAffine
  refine WP.seq (WP.mono (invert_ok hc) fun t ⟨kt, e15, ek⟩ => ?_)
  refine WP.mono (fieldCode_ok affineOps (hc.of_keep kt).ctx (hc.of_keep kt).ws) fun u ⟨ku, eu⟩ => ⟨kt.trans ku, ?_, ?_⟩
  · rw [eu, (affine_eval _).1, ek 0 (by decide), e15]
  · rw [eu, (affine_eval _).2, ek 1 (by decide), e15]

theorem V_mod2 (m : Mem) (b : Addr) (o : Nat) : V m b o % 2 = limb m b o 0 % 2 := by
  unfold V
  have h : ∀ n, val32 (limb m b o) (n + 1) % 2 = limb m b o 0 % 2 := by
    intro n
    induction n with
    | zero => simp [val32]
    | succ n ih =>
      rw [val32_succ, show 2 ^ (32 * (n + 1)) * limb m b o (n + 1) = 2 * (2 ^ (32 * n + 31) * limb m b o (n + 1)) by
        rw [← Nat.mul_assoc, ← Nat.pow_succ']; congr 2, Nat.add_mul_mod_self_left, ih]
  exact h 7

section
variable {b : Addr}

/-- The parity of the element at `FR` at bit 31 of `t6`. -/
theorem pointSign_ok {s : State} (hc : Ctx b s) :
    WP isa (.block pointSign) s fun t => Rest [.a4, .t6] s t ∧ t.mem = s.mem ∧
      (t.gpr .t6).toNat = (V s.mem b FR % 2) * 2 ^ 31 := by
  have hF := FR_eq
  unfold pointSign
  refine lw0_ok hc (d := FR) (by omega_arith) (by omega_arith) fun s1 u1 => wp_sll (by decide) fun s2 u2 => wp_srl (by decide) fun s3 u3 =>
    WP.block_nil ⟨(u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide))),
      by rw [u3.mem, u2.mem, u1.mem], ?_⟩
  have e7 : (s1.gpr .a4).toNat = limb s.mem b FR 0 := by rw [u1.gpr, toNat_ext32]; rfl
  have hl := limb_lt s.mem b FR 0
  rw [u3.gpr, toNat_shr, u2.gpr, toNat_shl, e7, V_mod2,
    show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from rfl, Nat.mul_mod_mul_right,
    show (2 : Nat) ^ 63 = 2 ^ 31 * 2 ^ 32 from rfl, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by decide)]

/-- The parity added at bit 255 of the element at `FR`, below `2^255`. -/
theorem encodeSign_ok {s : State} (hc : Ctx b s) {y x : Nat} (hy : y < 2 ^ 255) (hv : V s.mem b FR = y)
    (hs : (s.gpr .t6).toNat = (x % 2) * 2 ^ 31) :
    WP isa (.block encodeSign) s fun t => Rest [.a4] s t ∧ Frame [⟨b + BitVec.ofNat 64 (FR + 28), 4⟩] s.mem t.mem ∧
      V t.mem b FR = y + (x % 2) * 2 ^ 255 := by
  have hF := FR_eq
  have h7 : limb s.mem b FR 7 < 2 ^ 31 := by
    have hv7 : val32 (limb s.mem b FR) 7 + 2 ^ 224 * limb s.mem b FR 7 = y := by rw [← hv]; rfl
    by_contra h
    have : 2 ^ 224 * 2 ^ 31 ≤ 2 ^ 224 * limb s.mem b FR 7 := Nat.mul_le_mul_left _ (by omega)
    omega_arith
  unfold encodeSign
  refine lw0_ok hc (d := FR + 28) (by omega_arith) (by omega_arith) fun s1 u1 => wp_add fun s2 u2 => ?_
  have e2 : (s2.gpr .a4).toNat = limb s.mem b FR 7 + (x % 2) * 2 ^ 31 := by
    have e1 : (s1.gpr .a4).toNat = limb s.mem b FR 7 := by rw [u1.gpr, toNat_ext32]; rfl
    have hx := Nat.mod_lt x (show 0 < 2 by decide)
    rw [u2.gpr, u1.other .t6 (by decide), toNat_add_lt (by rw [e1, hs]; omega_arith), e1, hs]
  have hr2 : Rest [.a4] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  refine sw0_ok (hc.of_rest hr2 (by decide)) (d := FR + 28) (by omega_arith) (by omega_arith) fun s3 u3 => WP.block_nil ⟨?_, ?_, ?_⟩
  · exact hr2.trans (u3.rest _)
  · rw [u3.mem, u2.mem, u1.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (d := FR + 28) (n := 32 / 8) (Nat.le_refl _) (by omega_arith) (by omega_arith))
  · have hm : s3.mem = s.mem.writeW (b + BitVec.ofNat 64 (FR + 28)) ((s2.gpr .a4).setWidth 32) := by
      rw [u3.mem, u2.mem, u1.mem]
    have hl : ∀ k < 8, limb s3.mem b FR k = if k = 7 then limb s.mem b FR 7 + (x % 2) * 2 ^ 31 else limb s.mem b FR k := by
      intro k hk
      rw [limb, hm]
      by_cases h : k = 7
      · subst h
        have hx := Nat.mod_lt x (show 0 < 2 by decide)
        rw [iteT rfl, wd_write_self, toNat_lo32, e2, Nat.mod_eq_of_lt (by omega_arith)]
      · rw [iteF h, wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]; rfl
    rw [V, val32_congr hl, ← hv, V]
    simp only [val32, ite_true, show (0 : Nat) ≠ 7 by decide, show (1 : Nat) ≠ 7 by decide,
      show (2 : Nat) ≠ 7 by decide, show (3 : Nat) ≠ 7 by decide, show (4 : Nat) ≠ 7 by decide,
      show (5 : Nat) ≠ 7 by decide, show (6 : Nat) ≠ 7 by decide, ite_false]
    omega_arith

/-- The number `encodePoint` encodes. -/
def encodeNum (p : Spec.Ed25519.Point) : Nat :=
  (p.Y * Spec.X25519.pow p.Z (P - 2)).val + ((p.X * Spec.X25519.pow p.Z (P - 2)).val % 2) * 2 ^ 255

theorem encodePoint_eq (p : Spec.Ed25519.Point) : Spec.Ed25519.encodePoint p = Spec.Ed25519.encodeLE 32 (encodeNum p) :=
  rfl

theorem env_val (m : Mem) (i : Slot) : (env m b i).val = V m b (offset i) % P := rfl

/-- **The encoding** of the point of slots 0–3, at `FR`. -/
theorem pointEncode_ok {s : State} (hc : Ctx8 b s) :
    WP isa pointEncode s fun t => Rest (.t6 :: fclob) s t ∧ Frame [FA b] s.mem t.mem ∧
      V t.mem b FR = encodeNum (point (env s.mem b) 0 1 2 3) := by
  have hF := FR_eq
  unfold pointEncode
  refine WP.seq (WP.mono (pointAffine_ok hc) fun t1 ⟨k1, e0, e1⟩ => ?_)
  have hc1 : Ctx b t1 := (hc.of_keep k1).ctx
  simp only [List.append_assoc]
  refine WP.append (freeze_ok hc1 0) fun t2 ⟨r2, f2, _, v2⟩ => ?_
  have hc2 : Ctx b t2 := hc1.of_rest r2 (by decide)
  refine WP.append (pointSign_ok hc2) fun t3 ⟨r3, m3, e17⟩ => ?_
  have hc3 : Ctx b t3 := hc2.of_rest r3 (by decide)
  refine WP.append (freeze_ok hc3 1) fun t4 ⟨r4, f4, _, v4⟩ => ?_
  have hc4 : Ctx b t4 := hc3.of_rest r4 (by decide)
  obtain ⟨y, hy⟩ : ∃ y, y = (point (env s.mem b) 0 1 2 3).Y * Spec.X25519.pow (point (env s.mem b) 0 1 2 3).Z (P - 2) :=
    ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, x = (point (env s.mem b) 0 1 2 3).X * Spec.X25519.pow (point (env s.mem b) 0 1 2 3).Z (P - 2) :=
    ⟨_, rfl⟩
  have hv4 : V t4.mem b FR = y.val := by
    rw [v4, m3, ← env_val, env_keep f2 1 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by simp only [offset]; omega_arith)) (by simp only [offset]; omega_arith) (by omega_arith),
      e1, hy]
    rfl
  have hs4 : (t4.gpr .t6).toNat = (x.val % 2) * 2 ^ 31 := by
    rw [r4.gpr _ (by decide), e17, v2, ← env_val, e0, hx]; rfl
  refine WP.mono (encodeSign_ok hc4 (y := y.val) (x := x.val) (Nat.lt_trans y.isLt (by decide)) hv4 hs4)
    fun t5 ⟨r5, f5, v5⟩ => ⟨?_, ?_, ?_⟩
  · exact (k1.rest.mono (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
      ((r4.mono (by decide)).trans (r5.mono (by decide)))))
  · have hs : ∀ d n, d + n ≤ 1024 → 64 ≤ d → ∀ r ∈ ([⟨b + BitVec.ofNat 64 d, n⟩] : List Region),
        ∃ r' ∈ [FA b], r.Sub r' := fun d n h1 h2 r hr =>
      ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)⟩
    refine k1.frame.trans ((f2.sub (hs FR 64 (by omega_arith) (by omega_arith))).trans ?_)
    rw [← m3]
    exact (f4.sub (hs FR 64 (by omega_arith) (by omega_arith))).trans (f5.sub (hs (FR + 28) 4 (by omega_arith) (by omega_arith)))
  · rw [v5, encodeNum, ← hx, ← hy]

end

end VG.Proof.Ed25519.RISCV64
