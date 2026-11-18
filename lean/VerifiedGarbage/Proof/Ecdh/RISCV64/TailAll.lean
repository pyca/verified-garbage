module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.MulContract
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
public import VerifiedGarbage.Proof.Ecdh.Exchange
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.Mont.Read

/-!
# ECDH and public keys on RISC-V: the check and `tail`, for every curve

What the proofs of `Proof/Ecdh/RISCV64/` share, once for every curve: the
slots' arithmetic, ranges of offsets, the saves, calls on the working space
and bytes apart from it (`Kit`); and, for a curve's `TKit` (its
configuration, its field's multiplication, the strings of its contracts),
the check of a point (`TKit.check_rv`) and what follows the point's setup in
both functions (`TKit.tail_ok`, `TKit.tailWith_ok`: the range of `d` into the
flag, the multiplication's call, `Z^(p-2)` by the chain, `x` out of
Montgomery's form). Each `<Curve>/Tail.lean` is the curve's `TKit`, its
chain of `p - 2` and its multiplication's contract, and the statements about
the curve that other modules use.
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.X25519.RISCV64 (Rest wp_and)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt)
open VG.WriteBytes (writeBytes)

namespace Kit

/-- The number at slot `i`. -/
abbrev sv (c : Cfg) (base : Addr) (s : State) (i : Nat) : Nat := wordsVal s.mem base (c.sl i) c.n

/-- `vg_<curve>_check_point(ws = a0)`. -/
def checkRVc (CC : Impl.Weierstrass.CheckPoint.Curve) : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .a0, 8192⟩] ∧ (s.gpr .a0).toNat + 8192 ≤ 2 ^ 64 ∧
    (s.gpr .a0).toNat % 8 = 0 ∧ CC.pre (s.gpr .a0) s.mem
  post s s' := CC.post (s.gpr .a0) s.mem s'.mem
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0

/-! ## Slots -/

theorem sl8 (c : Cfg) (i : Nat) : c.sl i % 8 = 0 := by
  simp only [Cfg.sl, slot, Nat.mul_assoc]; omega

theorem sl_lo (c : Cfg) (i : Nat) : 64 ≤ c.sl i := Nat.le_add_right _ _

theorem sl_le (c : Cfg) {i j : Nat} (h : i < j) : c.sl i + 8 * c.n ≤ c.sl j := by
  have := Nat.mul_le_mul_left (8 * c.n) (Nat.succ_le_of_lt h)
  rw [Nat.mul_succ] at this
  simp only [Cfg.sl, slot]; omega

theorem sl_sep (c : Cfg) {i j : Nat} (h : i ≠ j) : c.sl i + 8 * c.n ≤ c.sl j ∨ c.sl j + 8 * c.n ≤ c.sl i :=
  (Nat.lt_or_gt_of_ne h).imp (sl_le c) (sl_le c)

theorem sl_top {c : Cfg} (n9 : c.n ≤ 9) {i : Nat} (hi : i ≤ 55) : c.sl i + 8 * c.n ≤ 4096 := by
  have := Nat.mul_le_mul (Nat.mul_le_mul_left 8 n9) (Nat.succ_le_succ hi)
  rw [Nat.mul_succ] at this
  simp only [Cfg.sl, slot]; omega

/-! ## Ranges of offsets -/

theorem all_app {P : Nat × Nat → Prop} {W W' : List (Nat × Nat)} (h : ∀ w ∈ W, P w) (h' : ∀ w ∈ W', P w) :
    ∀ w ∈ W ++ W', P w :=
  fun w hw => (List.mem_append.mp hw).elim (h w) (h' w)

theorem all_one {P : Nat × Nat → Prop} {a : Nat × Nat} (h : P a) : ∀ w ∈ [a], P w :=
  fun _ hw => List.mem_singleton.mp hw ▸ h

/-- The constants' slots. -/
abbrev cslots : List Nat := [MP, MN, ZERO, ONE, ONEP, AP, B3P, GX, GY, EXPP, R2P, BP]

theorem consts_fst (c : Cfg) : (consts c).map Prod.fst = cslots := rfl

theorem consts_len (c : Cfg) : (consts c).length = 12 := rfl

theorem mem_cslots {c : Cfg} {e : Nat × Nat} (he : e ∈ consts c) : e.1 ∈ cslots := by
  rw [← consts_fst c]; exact List.mem_map_of_mem he

theorem consts_nodup (c : Cfg) : ((consts c).map Prod.fst).Nodup := by rw [consts_fst]; decide

/-- The constants, as the kit's `consts_ok` takes them. -/
theorem constCode_eq (c : Cfg) : constCode c = (consts c).flatMap fun e => setConst c.n (c.sl e.1) e.2 := rfl

/-- A slot that is not a constant's is apart from the constants. -/
theorem apart_consts (c : Cfg) {i : Nat} (hi : ∀ j ∈ cslots, i ≠ j) :
    ∀ w ∈ (consts c).map (fun e => (c.sl e.1, 8 * c.n)), c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  fun w hw => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hw
    exact sl_sep c (hi _ (mem_cslots he))

/-- The flag is apart from the constants. -/
theorem flag_consts (c : Cfg) :
    ∀ w ∈ (consts c).map (fun e => (c.sl e.1, 8 * c.n)), c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG :=
  fun w hw => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hw
    exact .inr (sl_le c ((by decide : ∀ j ∈ cslots, j < FLAG) _ (mem_cslots he)))

theorem lo_consts (c : Cfg) : ∀ w ∈ (consts c).map (fun e => (c.sl e.1, 8 * c.n)), 40 ≤ w.1 :=
  fun w hw => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hw
    exact Nat.le_trans (by decide) (sl_lo c e.1)

/-! ## What does not depend on the curve -/

theorem maskOf_and (a b : Bool) : maskOf a &&& maskOf b = maskOf (a && b) := by
  cases a <;> cases b <;> decide

theorem not_mask (b : Bool) : maskOf b ^^^ BitVec.ofInt 64 (-1) = maskOf (!b) := by cases b <;> decide

theorem and_one (b : Bool) : maskOf b &&& BitVec.ofInt 64 1 = if b then 1 else 0 := by cases b <;> decide

/-- A byte of a region apart from the working space. -/
theorem out_of_disj {p base : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) (hn : p.toNat + n ≤ 2 ^ 64)
    {off i : Nat} (hi : off + i < n) : ¬ (⟨base, 8192⟩ : Region).Contains (p + BitVec.ofNat 64 (off + i)) 1 :=
  hd _ (Offset.contains_base p (by omega_using [hi]) (by omega_using [hn, hi]))

/-- Bytes of a region apart from the working space, from an offset. -/
theorem sep_at' {p base : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) (hn : p.toNat + n ≤ 2 ^ 64)
    {off k : Nat} (hk : off + k ≤ n) :
    ∀ i < k, ¬ (⟨base, 8192⟩ : Region).Contains (p + BitVec.ofNat 64 off + BitVec.ofNat 64 i) 1 := fun i hi => by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact out_of_disj hd hn (by omega_using [hk, hi])

/-- Bytes apart from the working space survive changes within it. -/
theorem bytesAt_unch {base q : Addr} {W : List (Nat × Nat)} {n : Nat} {m m' : Mem} (U : Unch base W m m')
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ 8192)
    (hsep : ∀ i < n, ¬ (⟨base, 8192⟩ : Region).Contains (q + BitVec.ofNat 64 i) 1) :
    bytesAt m' q n = bytesAt m q n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have := hsep i hi
  simp only [Region.Contains] at this
  exact U _ fun w hw => .inr (by have := hW w hw; simp only [ofs]; omega_arith)

/-- The bytes just written. -/
theorem bytesAt_writeBytes (m : Mem) (q : Addr) (xs : List Byte) (h : xs.length ≤ 2 ^ 64) :
    bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro i h₁ h₂
    have hi : i < xs.length := h₂
    simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes,
      Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hi h), hi,
      ite_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- A call on the working space, then `s0` from `s3`. -/
theorem wsCallR_ok {f : String} {body : Prog isa} (hn : body.noFrames = true) {K : Contract isa}
    (hK : Meets body K) {s : State} {base : Addr} (hw : WsReg s base) (h3 : s.gpr .s3 = base)
    (hpre : ∀ t : State, t.rd = [] → t.wr = [⟨base, 8192⟩] → t.gpr .a0 = base → t.mem = s.mem → K.pre t)
    {Q : State → Prop}
    (hQ : ∀ s' s'' : State, Kp s s'' → s''.mem = s'.mem → ∀ t : State, t.gpr .a0 = base → t.mem = s.mem →
      K.post t (s'.withRegions [] [⟨base, 8192⟩]) → Q s'') :
    WP isa (Cfg.wsCall f body) s Q := by
  rw [Cfg.wsCall]
  refine WP.seq (wsCall_ok hn hK hw hpre fun s' K' t a m hp => wp_mv fun s'' u => WP.block_nil ?_)
  refine hQ s' s'' ⟨fun r hr => ?_, by rw [u.rd, K'.rd], by rw [u.wr, K'.wr], by rw [u.sp, K'.sp]⟩ u.mem t a m hp
  by_cases h : r = .s0
  · subst h; rw [u.gpr, K'.gpr _ (by decide), h3, hw.s0]
  · rw [u.other _ h, K'.gpr _ hr]

theorem mask_eq (P : Prop) [Decidable P] : Impl.Weierstrass.CheckPoint.Curve.mask P = maskOf (decide P) := by
  unfold Impl.Weierstrass.CheckPoint.Curve.mask maskOf; by_cases h : P <;> simp [h]

/-- The check's validity is the specification's, but for the first byte. -/
theorem valid_iff_of {CC : Impl.Weierstrass.CheckPoint.Curve} {C : Curve} (hC : CC.W = C) (x y : Nat) :
    CC.Valid x y ↔ x < C.p ∧ y < C.p ∧ VG.Proof.Ecdh.OnCurveF C x y := by
  subst hC
  unfold Impl.Weierstrass.CheckPoint.Curve.Valid
  constructor
  · rintro ⟨hx, hy, h⟩
    refine ⟨hx, hy, (VG.Proof.Ecdh.onCurve_iff hx hy).mp ?_⟩
    rw [VG.Proof.EcKey.fe_eq hx rfl, VG.Proof.EcKey.fe_eq hy rfl] at h; exact h
  · rintro ⟨hx, hy, h⟩
    refine ⟨hx, hy, ?_⟩
    have := (VG.Proof.Ecdh.onCurve_iff hx hy).mpr h
    show Spec.Weierstrass.onCurve CC.W (.affine (Fin.ofNat CC.W.p x) (Fin.ofNat CC.W.p y)) = true
    rw [VG.Proof.EcKey.fe_eq hx rfl, VG.Proof.EcKey.fe_eq hy rfl]; exact this

/-- A valid point is on the curve. -/
theorem valid_on {CC : Impl.Weierstrass.CheckPoint.Curve} {C : Curve} (hC : CC.W = C) {x y : Nat}
    (h : CC.Valid x y) : Spec.Weierstrass.onCurve C (.affine (Fin.ofNat C.p x) (Fin.ofNat C.p y)) = true := by
  subst hC; exact h.2.2

theorem toBytes_zero (L : Nat) : toBytes L 0 = List.replicate L 0 := by
  rw [List.eq_replicate_iff]
  simp [toBytes]

/-- A word below the ranges that changed. -/
theorem lo_word {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (U : Unch base W m m')
    (hW : ∀ w ∈ W, 40 ≤ w.1) {d : Nat} (hd : d + 8 ≤ 40) : word m' base d = word m base d :=
  U.word (fun w hw => .inl (by have := hW w hw; omega_using [hd, this])) (by omega_using [hd])

/-- Eight bytes of a region. -/
theorem in_rd8 {rs : List Region} {p : Addr} {n : Nat} (hr : (⟨p, n⟩ : Region) ∈ rs) {off : Nat} (ho : off + 8 ≤ n)
    (hn : n ≤ 8192 := by decide) :
    InRegions rs (p + BitVec.ofNat 64 off) 8 :=
  ⟨_, hr, Offset.contains_base p ho (by omega_using [ho, hn])⟩

/-- `toM` is injective on numbers below `m`. -/
theorem toM_inj {m R : Nat} [NeZero m] (hR : UnitMod m R) {x y : Nat} (hx : x < m) (hy : y < m)
    (h : toM m R x = toM m R y) : x = y := by
  obtain e := congrArg (· * Fin.ofNat m R) h
  simp only [toM] at e
  rw [Lean.Grind.Semiring.mul_assoc, Lean.Grind.Semiring.mul_assoc, Lean.Grind.CommSemiring.mul_comm (rinv m R),
    mul_rinv hR, Lean.Grind.Semiring.mul_one, Lean.Grind.Semiring.mul_one] at e
  have := (ofNat_eq_ofNat (m := m)).mp e
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

/-- A Montgomery multiplication by `R² mod m` gives `x R mod m`. -/
theorem mont_eq {m R : Nat} [NeZero m] (hR : UnitMod m R) {r x : Nat} (hr : r < m)
    (h : r * R % m = x * (R * R % m) % m) : r = x * R % m :=
  toM_inj hR hr (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))) ((toM_r2 hR h).trans (toM_mont hR).symm)

theorem rep_of_represents {C : Curve} {X Y Z : Fe C} {P : Point C}
    (h : Impl.Weierstrass.MulBase.Represents X Y Z P) : Rep C X Y Z P := by
  cases P <;> exact h

/-- A block keeps the symbols' addresses and changes memory only in the
writable regions. -/
theorem wp_syms_frame {is : List Instr} {s : State} {R : State → Prop}
    (h : WP isa (.block is) s fun s' => s'.syms = s.syms → Frame s.wr s.mem s'.mem → R s') :
    WP isa (.block is) s R := by
  obtain ⟨t, s', he, hr⟩ := h
  have hf := Exec.frameAny he (by simp [sdepth])
  refine ⟨t, s', he, hr (Exec.syms he) fun x hx => hf x fun r hr' => ?_⟩
  rcases List.mem_append.mp hr' with h | h
  · exact hx r h
  · simp only [List.mem_singleton] at h; subst h
    simp only [sdepth, Region.Contains]
    omega_using []

/-- The own working space of the field's functions is past every slot. -/
theorem own_ge {c : Cfg} (n9 : c.n ≤ 9) : c.sl 45 + 8 ≤ own c.n := by
  obtain h := rvOwn_cases c.n
  simp only [Cfg.sl, slot, own]
  omega_using [h, n9]

end Kit

/-! ## The functions' pieces, for any configuration -/

namespace TKit

open Kit

/-- `sd t, d(r)` at the working space's base, in `r`. -/
theorem sd_reg {s : State} {base : Addr} {is : List Instr} {Q : State → Prop} {r : Reg} (h0 : s.gpr r = base)
    (hwr : (⟨base, 8192⟩ : Region) ∈ s.wr) (hal : base.toNat % 8 = 0)
    {t : Reg} {d : Nat} (hd : d + 8 ≤ 2048) (hd8 : d % 8 = 0)
    (k : ∀ s', Mupd s s' (s.mem.writeW (off base d) (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t r d :: is)) s Q :=
  wp_sd (by omega_using [hd]) (by rw [h0]) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hal, hd8])
    ⟨_, hwr, Offset.contains_base base (by omega_using [hd]) (by omega_using [hd])⟩ k

/-- The saves, `s0 = s3 = r` and `s2 = a0`. -/
theorem save_ok {s : State} {r : Reg} {base : Addr} (h0 : s.gpr r = base)
    (hwr : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) (hal : base.toNat % 8 = 0) :
    WP isa (.block (saveCode r)) s fun s' => WsReg s' base ∧ s'.gpr .s3 = base ∧ s'.gpr .s2 = s.gpr .a0 ∧
      (∀ x, x ≠ .s0 → x ≠ .s2 → x ≠ .s3 → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ Unch base [(0, 40)] s.mem s'.mem ∧
      word s'.mem base 0 = s.gpr .s0 ∧ word s'.mem base 8 = s.gpr .s1 ∧ word s'.mem base 16 = s.gpr .s2 ∧
      word s'.mem base 24 = s.gpr .ra ∧ word s'.mem base 32 = s.gpr .s3 := by
  rw [saveCode]
  refine sd_reg h0 hwr hal (d := 0) (by decide) (by decide) fun s₁ u₁ => ?_
  refine sd_reg (by rw [u₁.gpr]; exact h0) (by rw [u₁.wr]; exact hwr) hal (d := 8) (by decide) (by decide)
    fun s₂ u₂ => ?_
  refine sd_reg (by rw [u₂.gpr, u₁.gpr]; exact h0) (by rw [u₂.wr, u₁.wr]; exact hwr) hal (d := 16) (by decide)
    (by decide) fun s₃ u₃ => ?_
  refine sd_reg (by rw [u₃.gpr, u₂.gpr, u₁.gpr]; exact h0) (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hwr) hal (d := 24)
    (by decide) (by decide) fun s₄ u₄ => ?_
  refine sd_reg (by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]; exact h0) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hwr)
    hal (d := 32) (by decide) (by decide) fun s₅ u₅ =>
    wp_mv fun s₆ u₆ => wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ => WP.block_nil ?_
  obtain g₅ : ∀ x, s₅.gpr x = s.gpr x := fun x => by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  obtain m₅ : s₅.mem = ((((s.mem.writeW (off base 0) (s.gpr .s0)).writeW (off base 8) (s.gpr .s1)).writeW
      (off base 16) (s.gpr .s2)).writeW (off base 24) (s.gpr .ra)).writeW (off base 32) (s.gpr .s3) := by
    simp only [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  obtain m₈ : s₈.mem = s₅.mem := by rw [u₈.mem, u₇.mem, u₆.mem]
  obtain O : ∀ {d} {m : Mem} {v : BitVec 64}, d ≤ 32 → Outside base d 8 m (m.writeW (off base d) v) :=
    fun h => writeW_outside _ _ _ (by omega_using [h])
  obtain hw₈ : WsReg s₈ base := by
    refine ⟨by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅, h0], ?_, hn, hal⟩
    rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hwr
  obtain w0 : ∀ {d e} {m : Mem} {v : BitVec 64}, d ≤ 32 → e ≤ 32 → d + 8 ≤ e ∨ e + 8 ≤ d →
      word (m.writeW (off base e) v) base d = word m base d :=
    fun hd he h => (O he).word h (by omega_using [hd])
  obtain e₆ : s₆.gpr r = s₅.gpr r := by
    by_cases h : r = .s0
    · subst h; exact u₆.gpr
    · exact u₆.other _ h
  refine ⟨hw₈, by rw [u₈.other _ (by decide), u₇.gpr, e₆, g₅, h0],
    by rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅], fun x h1 h2 h3 => by
      rw [u₈.other _ h2, u₇.other _ h3, u₆.other _ h1, g₅],
    by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr],
    by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m₈, m₅]
    exact (((((O (by decide)).unch.trans (O (by decide)).unch).trans (O (by decide)).unch).trans
      (O (by decide)).unch).trans (O (by decide)).unch).cover (by decide)
  · rw [m₈, m₅, w0 (by decide) (by decide) (by decide), w0 (by decide) (by decide) (by decide),
      w0 (by decide) (by decide) (by decide), w0 (by decide) (by decide) (by decide), word_writeW_self]
  · rw [m₈, m₅, w0 (by decide) (by decide) (by decide), w0 (by decide) (by decide) (by decide),
      w0 (by decide) (by decide) (by decide), word_writeW_self]
  · rw [m₈, m₅, w0 (by decide) (by decide) (by decide), w0 (by decide) (by decide) (by decide), word_writeW_self]
  · rw [m₈, m₅, w0 (by decide) (by decide) (by decide), word_writeW_self]
  · rw [m₈, m₅, word_writeW_self]

/-- The flag `&=` the mask `a7`. -/
theorem andFlag_ok (c : Cfg) (h9 : c.n ≤ 9) {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block (Cfg.andFlag c)) s fun s' =>
      word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) &&& s.gpr .a7 ∧ Rest [.t0] s s' ∧
        Outside base (c.sl FLAG) 8 s.mem s'.mem := by
  obtain hf : c.sl FLAG + 8 ≤ 4095 := by simp only [Cfg.sl, slot, FLAG]; omega_using [h9]
  rw [Cfg.andFlag, ← List.append_nil (sdAt .t0 wb (c.sl FLAG))]
  simp only [List.append_assoc, List.singleton_append]
  refine ldAt_ws hw (d := c.sl FLAG) (by omega_using [hf]) (sl8 _ _) fun s₁ u₁ => wp_and fun s₂ u₂ => ?_
  obtain r₂ : Rest [.t0] s s₂ := (u₁.rest (by decide)).trans (u₂.rest (by decide))
  refine sdAt_ws (hw.of_rest r₂) (by decide) (d := c.sl FLAG) (by omega_using [hf]) (sl8 _ _) fun s₃ u₃ =>
    WP.block_nil ⟨?_, r₂.trans (u₃.rest _), ?_⟩
  · rw [u₃.mem, word_writeW_self, u₂.gpr, u₁.gpr, u₁.other .a7 (by decide)]
  · rw [u₃.mem, u₂.mem, u₁.mem]; exact writeW_outside _ _ _ (by omega_using [hf])

/-- The masks of `x < p` and `y < p` into the flag. -/
theorem masks_ok (c : Cfg) (h9 : c.n ≤ 9) {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block (ltMask c.n (c.sl CX) (c.sl MP) ++ Cfg.andFlag c ++ ltMask c.n (c.sl CY) (c.sl MP) ++
      Cfg.andFlag c)) s fun s' =>
      Kp s s' ∧ Outside base (c.sl FLAG) 8 s.mem s'.mem ∧
      word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) &&&
        maskOf (decide (sv c base s CX < sv c base s MP)) &&& maskOf (decide (sv c base s CY < sv c base s MP)) := by
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (ltMask_ok hw (n := c.n) (a := c.sl CX) (m := c.sl MP) (sl8 _ _)
    (sl8 _ _) (sl_top h9 (by decide)) (sl_top h9 (by decide))) fun s₁ ⟨r₁, m₁, g₁⟩ => ?_)
  obtain hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono (andFlag_ok c h9 hw₁) fun s₂ ⟨f₂, r₂, O₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  refine WP.block_append (WP.mono (ltMask_ok hw₂ (n := c.n) (a := c.sl CY) (m := c.sl MP) (sl8 _ _)
    (sl8 _ _) (sl_top h9 (by decide)) (sl_top h9 (by decide))) fun s₃ ⟨r₃, m₃, g₃⟩ => ?_)
  obtain hw₃ := hw₂.of_rest r₃
  refine WP.mono (andFlag_ok c h9 hw₃) fun s₄ ⟨f₄, r₄, O₄⟩ => ⟨?_, ?_, ?_⟩
  · exact (Kp.of_rest r₁).trans ((Kp.of_rest r₂).trans ((Kp.of_rest r₃).trans (Kp.of_rest r₄)))
  · rw [← m₁]; exact O₂.trans (by rw [← m₃]; exact O₄)
  · have e : ∀ i, i < 44 → sv c base s₂ i = sv c base s i := fun i hi => by
      show wordsVal s₂.mem _ _ _ = _
      rw [O₂.wordsVal (.inl (sl_le c hi)) (Nat.le_trans (sl_top h9 (by omega_using [hi])) (by decide)), m₁]
    rw [f₄, m₃, g₃, f₂, m₁, g₁]
    simp only [sv] at e ⊢
    rw [show wordsVal s₂.mem base (c.sl CY) c.n = _ from e CY (by decide),
      show wordsVal s₂.mem base (c.sl MP) c.n = _ from e MP (by decide)]

/-- Constants to slots, each its own. -/
theorem consts_ok (c : Cfg) (h9 : c.n ≤ 9) : ∀ (L : List (Nat × Nat)) {s : State} {base : Addr}, WsReg s base →
    (∀ e ∈ L, e.1 ≤ 55) → (L.map Prod.fst).Nodup →
    WP isa (.block (L.flatMap fun e => setConst c.n (c.sl e.1) e.2)) s fun s' =>
      Rest [.t0, .t1] s s' ∧ Unch base (L.map fun e => (c.sl e.1, 8 * c.n)) s.mem s'.mem ∧
      ∀ e ∈ L, sv c base s' e.1 = e.2 % 2 ^ (64 * c.n)
  | [], s, _, _, _, _ => WP.block_nil ⟨Rest.refl _ _, Unch.refl _ _ _, by simp⟩
  | (i, x) :: L, s, base, hw, hlt, hnd => by
    simp only [List.mem_cons, forall_eq_or_imp] at hlt
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rw [List.flatMap_cons]
    refine WP.block_append (WP.mono (setConst_ok c.n hw (o := c.sl i) (x := x) (sl8 _ _) (sl_top h9 hlt.1))
      fun s₁ ⟨r₁, O₁, e₁⟩ => ?_)
    refine WP.mono (consts_ok c h9 L (hw.of_rest r₁) hlt.2 hnd.2) fun s₂ ⟨r₂, U₂, e₂⟩ => ⟨r₁.trans r₂, ?_, ?_⟩
    · exact O₁.unch.trans U₂
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · show wordsVal _ _ _ _ = _
        rw [U₂.wordsVal (fun w hw => by
          simp only [List.mem_map] at hw
          obtain ⟨e', he', rfl⟩ := hw
          exact sl_sep c fun h => hnd.1 ⟨e', he', h.symm⟩) (Nat.le_trans (sl_top h9 hlt.1) (by decide))]
        exact e₁
      · exact e₂ e he

/-- The masks of `x < n` and `x ≠ 0` into the flag, for `x` at slot `i`. -/
theorem rangeOf_ok (c : Cfg) (h9 : c.n ≤ 9) {i : Nat} (hi : i < 44) {s : State} {base : Addr}
    (hw : WsReg s base) :
    WP isa (.block (rangeOf c i)) s fun s' =>
      Kp s s' ∧ Outside base (c.sl FLAG) 8 s.mem s'.mem ∧
      word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) &&&
        maskOf (decide (sv c base s i < sv c base s MN)) &&& maskOf (!decide (sv c base s i = 0)) := by
  obtain a8 := sl8 c i
  obtain a2 : c.sl i + 8 * c.n ≤ 4096 := sl_top h9 (by omega_using [hi])
  obtain aF : c.sl i + 8 * c.n ≤ c.sl FLAG := sl_le c hi
  rw [rangeOf]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (ltMask_ok hw (n := c.n) (a := c.sl i) (m := c.sl MN) a8
    (sl8 _ _) a2 (sl_top h9 (by decide))) fun s₁ ⟨r₁, m₁, g₁⟩ => ?_)
  obtain hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono (andFlag_ok c h9 hw₁) fun s₂ ⟨f₂, r₂, O₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  refine WP.block_append (WP.mono (zeroMask_ok hw₂ (n := c.n) (a := c.sl i) a8 a2) fun s₃ ⟨r₃, m₃, g₃⟩ => ?_)
  refine WP.cons (exec_logicImm (by decide)) ?_
  obtain hw₃' := (hw₂.of_rest r₃).of_kp (Kp.of_upd (Upd.write s₃ .a7 (s₃.gpr .a7 ^^^ BitVec.ofInt 64 (-1))))
  refine WP.mono (andFlag_ok c h9 hw₃') fun s₄ ⟨f₄, r₄, O₄⟩ => ⟨?_, ?_, ?_⟩
  · exact (Kp.of_rest r₁).trans ((Kp.of_rest r₂).trans ((Kp.of_rest r₃).trans
      ((Kp.of_upd (Upd.write s₃ .a7 _)).trans (Kp.of_rest r₄))))
  · rw [← m₁]; exact O₂.trans (by rw [← m₃]; exact O₄)
  · have k₂ : sv c base s₂ i = sv c base s i := by
      show wordsVal _ _ _ _ = _
      rw [O₂.wordsVal (.inl aF) (Nat.le_trans a2 (by decide)), m₁]
    rw [f₄]
    simp only [State.write, ↓reduceIte]
    rw [m₃, f₂, m₁, g₁, g₃, not_mask]
    simp only [sv] at k₂
    rw [k₂]

/-- The masks of `d < n` and `d ≠ 0` into the flag. -/
theorem range_ok (c : Cfg) (h9 : c.n ≤ 9) {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block (rangeCode c)) s fun s' =>
      Kp s s' ∧ Outside base (c.sl FLAG) 8 s.mem s'.mem ∧
      word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) &&&
        maskOf (decide (sv c base s K < sv c base s MN)) &&& maskOf (!decide (sv c base s K = 0)) :=
  rangeOf_ok c h9 (by decide) hw

/-- The constants `tail` reads. -/
structure Consts (c : Cfg) (base : Addr) (s : State) : Prop where
  mp : sv c base s MP = c.C.p
  mn : sv c base s MN = c.C.n
  zero : sv c base s ZERO = 0
  one : sv c base s ONE = 1
  onep : sv c base s ONEP = 1 * 2 ^ (64 * c.n) % c.C.p
  ap : sv c base s AP = c.C.a * 2 ^ (64 * c.n) % c.C.p
  b3p : sv c base s B3P = 3 * c.C.b * 2 ^ (64 * c.n) % c.C.p
  expp : sv c base s EXPP = c.C.p - 2

theorem Consts.of_unch {c : Cfg} (h9 : c.n ≤ 9) {base : Addr} {s s' : State} {W' : List (Nat × Nat)}
    (h : Consts c base s) (U : Unch base W' s.mem s'.mem)
    (hW : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP], ∀ w ∈ W', c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i) :
    Consts c base s' := by
  obtain e : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP], sv c base s' i = sv c base s i := fun i hi =>
    U.wordsVal (hW i hi) (Nat.le_trans (sl_top h9 ((by decide : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP],
      i ≤ 55) i hi)) (by decide))
  exact ⟨(e MP (by decide)).trans h.mp, (e MN (by decide)).trans h.mn, (e ZERO (by decide)).trans h.zero,
    (e ONE (by decide)).trans h.one, (e ONEP (by decide)).trans h.onep, (e AP (by decide)).trans h.ap,
    (e B3P (by decide)).trans h.b3p, (e EXPP (by decide)).trans h.expp⟩

/-! ## The field's functions, for `k` words modulo `p` -/

/-- `mulCall_ok`, for a field of `k` words modulo `p`. -/
theorem mulCall_kit {F : Field} (hF : FieldOk F) {k p : Nat} (hk : F.S.k = k) (hm : F.S.m = p) {s : State}
    {base : Addr} (hw : WsReg s base) {o a b : Nat}
    (ho : o + 8 * k ≤ own k) (ha : a + 8 * k ≤ own k) (hb : b + 8 * k ≤ own k)
    (ho' : o < 4095) (ha' : a < 4095) (hb' : b < 4095) (hB : wordsVal s.mem base b k < p) :
    WP isa (mulCall F o a b) s fun s' => CallKeep k base o s s' ∧
      wordsVal s'.mem base o k < p ∧
      wordsVal s'.mem base o k * 2 ^ (64 * k) % p = wordsVal s.mem base a k * wordsVal s.mem base b k % p := by
  subst hk hm; exact mulCall_ok hF hw ho ha hb ho' ha' hb' hB

/-- `chainPow_ok`, for a field of `k` words modulo `p`. -/
theorem chainPow_kit {F : Field} {P : ChainCfg} (hF : FieldOk F) {k p : Nat} [NeZero p] (hk : F.S.k = k)
    (hm : F.S.m = p) (hL : ChainLayR P k) (hU : UnitMod p (2 ^ (64 * k)))
    {base : Addr} {s : State} {e one : Nat} (hs : WsReg s base) (hone : one + 8 * k ≤ own k)
    (hone' : one < 4095) (hO : wordsVal s.mem base one k = 2 ^ (64 * k) % p) (hC : ChainOkR P e) :
    WP isa (chainPow P one F) s fun s' => Kc s s' ∧ Unch base (chainWx P k) s.mem s'.mem ∧
      wordsVal s'.mem base P.acc k < p ∧
      toM p (2 ^ (64 * k)) (wordsVal s'.mem base P.acc k) =
        toM p (2 ^ (64 * k)) (wordsVal s.mem base P.base k) ^ e := by
  subst hk hm; exact chainPow_ok hF hL hU hs hone hone' hO hC

/-! ## The layout -/

/-- What `vg_<curve>_mul` may write, as ranges of offsets: the result, its
own slots, and everything from the table of bits on. -/
abbrev mulKW (c : Cfg) : List (Nat × Nat) :=
  [(c.sl 14, 24 * c.n), (c.sl 17, 112 * c.n), (c.sl 2, 8 * c.n), (c.sl 40, 8 * c.n), (c.sl 45, 2 ^ 64)]

theorem chainP_acc (c : Cfg) : (chainP c).acc = c.sl ACC := rfl
theorem chainP_base (c : Cfg) : (chainP c).base = c.sl RZ := rfl
theorem chainP_tbl (c : Cfg) : (chainP c).tbl = c.sl TB := rfl

/-- What `tail` writes. -/
abbrev tailW (c : Cfg) : List (Nat × Nat) :=
  [(c.sl FLAG, 8)] ++ mulKW c ++ chainWx (chainP c) c.n ++
    [(c.sl XM, 8 * c.n), (own c.n, 64 * c.n), (c.sl XO, 8 * c.n), (own c.n, 64 * c.n)]

/-- The writes of the check: its own working space or its results. -/
abbrev chkW (c : Cfg) : List (Nat × Nat) :=
  ((([(c.sl TMP, 8), (c.sl TMP + 8, 8)] ++ [(c.sl FLAG, 8)]) ++ [(c.sl CXM, 8 * c.n), (own c.n, 64 * c.n)]) ++
      [(c.sl CYM, 8 * c.n), (own c.n, 64 * c.n)]) ++
    (((Cfg.curveOps c).map FOp.out).map (fun w => (w, 8 * c.n)) ++ [(own c.n, 64 * c.n)]) ++
    [(c.sl FLAG, 8), (c.sl CPX, 8 * c.n), (c.sl CPY, 8 * c.n)]

/-- What `vg_<curve>_check_point` may write, as ranges of offsets. -/
abbrev checkKW (c : Cfg) : List (Nat × Nat) :=
  [(c.sl 2, 8 * c.n), (c.sl 37, 8 * c.n), (c.sl 41, 8 * c.n), (c.sl 42, 8 * c.n), (own c.n, 64 * c.n),
    (c.sl 34, 8 * c.n), (c.sl 35, 8 * c.n), (c.sl 38, 8 * c.n), (c.sl 43, 8 * c.n), (c.sl FLAG, 8), (8192, 2 ^ 64)]

/-- Layout facts: slots given by number against ranges given as lists, unfolded to arithmetic in the
words' count, with its bound `h9` and the place of the field's own working space `hown`. -/
local macro "kit_layout" "[" hs:term,* "]" : tactic => `(tactic| (
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq,
    mulKW, tailW, chkW, checkKW, chainWx, chainP_acc, chainP_tbl, Cfg.curveOps, List.map_cons, List.map_nil, FOp.out,
    Cfg.sl, slot, MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP, K, RX, RY, RZ, ACC, TB, XM, XO, FLAG, TMP, CX, CY, CXM,
    CYM, W0, W1, W2, CPX, CPY, R2P, BP, GX, GY]
  omega_using [$hs,*]))

/-- The chain's slots. -/
theorem chainLay (c : Cfg) (h1 : 1 ≤ c.n) (h9 : c.n ≤ 9) : ChainLayR (chainP c) c.n := by
  obtain hown : 64 + 8 * c.n * 45 + 8 ≤ own c.n := own_ge h9
  obtain h := rvOwn_cases c.n
  refine ⟨rfl, h1, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, sl8 _ _, sl8 _ _, sl8 _ _, ?_, ?_, ?_⟩ <;>
    simp only [chainP_acc, chainP_base, chainP_tbl, Cfg.sl, slot, ACC, RZ, TB, own] <;> omega_using [h9, h]

/-! ## What the proofs need of a curve -/

/-- What the proofs need of a curve: its configuration, the names of its
contracts' curves, its field's functions, and its prime. -/
structure _root_.VG.Proof.Ecdh.RISCV64.TKit where
  c : Cfg
  /-- The contracts' names of the curve. -/
  name : String
  cdesc : String
  mdesc : String
  n4 : 4 ≤ c.n
  n9 : c.n ≤ 9
  p1 : 1 < c.C.p
  field_ok : FieldOk c.FP
  FPk : c.FP.S.k = c.n
  FPm : c.FP.S.m = c.C.p
  unit : UnitMod c.C.p (2 ^ (64 * c.n))

variable (T : TKit)

/-- The curve of the multiplication's contract (`Proof/Weierstrass/MulContract.lean`). -/
abbrev MC : Impl.Weierstrass.Mul.Curve :=
  { W := T.c.C, curve := T.name, k := T.c.n, desc := T.mdesc, tmp := 2, tail := true, inRange := true }

/-- `vg_<curve>_mul(ws = a0)`. -/
def mulRVc (MC : Impl.Weierstrass.Mul.Curve) : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .a0, 8192⟩] ∧ (s.gpr .a0).toNat + 8192 ≤ 2 ^ 64 ∧
    (s.gpr .a0).toNat % 8 = 0 ∧ MC.ConstsOk (s.gpr .a0) s.mem ∧ MC.PointOk (s.gpr .a0) s.mem
  post s s' := MC.ResultInRange (MC.scalar (s.gpr .a0) s.mem) (MC.point (s.gpr .a0) s.mem) (s.gpr .a0) s.mem s'.mem
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0

/-- The coordinate `[o] = [a] Z^(p-2)` out of Montgomery's form, `Z^(p-2) R` in `ACC`. -/
theorem affine_ok {s : State} {base : Addr} (hw : WsReg s base) {t o a : Nat} (ht : t < 44) (ho : o < 44)
    (ha : a < 44) (htm : t ≠ ONE ∧ t ≠ ACC) (hacc : sv T.c base s ACC < T.c.C.p) (hone : sv T.c base s ONE = 1) :
    WP isa (affineCoord T.c t o a) s fun s' =>
      Kp s s' ∧ Unch base [(T.c.sl t, 8 * T.c.n), (own T.c.n, 64 * T.c.n), (T.c.sl o, 8 * T.c.n),
        (own T.c.n, 64 * T.c.n)] s.mem s'.mem ∧
      sv T.c base s' o < T.c.C.p ∧
      Fin.ofNat T.c.C.p (sv T.c base s' o) =
        toM T.c.C.p (2 ^ (64 * T.c.n)) (sv T.c base s a) * toM T.c.C.p (2 ^ (64 * T.c.n)) (sv T.c base s ACC) := by
  obtain h9 := T.n9
  obtain h1 : 1 ≤ T.c.n := Nat.le_trans (by decide) T.n4
  obtain hown := own_ge h9
  obtain hl : ∀ i, i < 44 → T.c.sl i + 8 * T.c.n ≤ own T.c.n := fun i hi => by
    have : T.c.sl i + 8 * T.c.n ≤ T.c.sl 45 := sl_le T.c (Nat.lt_succ_of_lt hi)
    omega_using [this, hown]
  obtain hs : ∀ i, i < 44 → T.c.sl i < 4095 := fun i hi => by
    have := sl_top h9 (i := i) (by omega_using [hi])
    omega_using [this, h1]
  rw [affineCoord]
  refine WP.seq (WP.mono (mulCall_kit T.field_ok T.FPk T.FPm hw (o := T.c.sl t) (a := T.c.sl a) (b := T.c.sl ACC)
    (hl t ht) (hl a ha) (hl ACC (by decide)) (hs t ht) (hs a ha) (hs ACC (by decide)) hacc)
    fun s₁ ⟨C₁, lt₁, e₁⟩ => ?_)
  obtain one₁ : sv T.c base s₁ ONE = 1 := by
    rw [← hone]
    exact Unch.wordsVal (C₁.mem : Unch _ _ _ _) (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact sl_sep _ (Ne.symm htm.1)
      · exact .inl (hl ONE (by decide))) (Nat.le_trans (sl_top h9 (by decide)) (by decide))
  refine WP.mono (mulCall_kit T.field_ok T.FPk T.FPm (hw.of_kp C₁.kp) (o := T.c.sl o) (a := T.c.sl t)
    (b := T.c.sl ONE) (hl o ho) (hl t ht) (hl ONE (by decide)) (hs o ho) (hs t ht) (hs ONE (by decide))
    (by show sv T.c base s₁ ONE < T.c.C.p; rw [one₁]; exact T.p1)) fun s₂ ⟨C₂, lt₂, e₂⟩ => ⟨C₁.kp.trans C₂.kp,
      Unch.trans (C₁.mem : Unch _ _ _ _) (C₂.mem : Unch _ _ _ _), lt₂, ?_⟩
  obtain e₂' : sv T.c base s₂ o * 2 ^ (64 * T.c.n) % T.c.C.p = sv T.c base s₁ t * 1 % T.c.C.p := by
    rw [← one₁]; exact e₂
  rw [toM_one_mul T.unit e₂']
  exact toM_mul T.unit e₁

/-- The coordinate at an offset below `2³²` is the number `wordsVal` reads. -/
theorem coordAt_eq (m : Mem) (ws : Addr) {o : Nat} (ho : o < 2 ^ 32) :
    T.MC.toPoint.coordAt m ws o = wordsVal m ws o T.c.n := by
  unfold Impl.Weierstrass.Point.Curve.coordAt
  rw [Impl.Weierstrass.Mont.numAt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
  exact read_eq_wordsVal m ws T.c.n o

/-- The coordinates the multiplication's contract decodes. -/
theorem dq (hL : Law T.c.C) (x : Nat) : T.MC.toPoint.dec x = toM T.c.C.p (2 ^ (64 * T.c.n)) x :=
  VG.Proof.Weierstrass.Point.dec_eq T.MC.toPoint hL.one_ne_zero (VG.Proof.Weierstrass.Point.fermat_of_law hL)
    T.unit x

theorem coord_sv (m : Mem) (base : Addr) (i : Nat) (hi : i < 100) :
    T.MC.toPoint.coordAt m base (T.c.sl i) = wordsVal m base (T.c.sl i) T.c.n :=
  T.coordAt_eq m base (by
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 8 T.n9) (Nat.le_of_lt_succ hi)
    simp only [Cfg.sl, slot]; omega_using [this])

/-- Where the result's `y` and `z` are. -/
theorem pAt_y : T.MC.pAt + 8 * T.c.n = T.c.sl RY := by
  simp only [Impl.Weierstrass.Mul.Curve.pAt, Impl.Weierstrass.Mul.Curve.slot, Cfg.sl, slot, RY]; omega_using []

theorem pAt_z : T.MC.pAt + 2 * (8 * T.c.n) = T.c.sl RZ := by
  simp only [Impl.Weierstrass.Mul.Curve.pAt, Impl.Weierstrass.Mul.Curve.slot, Cfg.sl, slot, RZ]; omega_using []

/-- The point the multiplication's contract reads. -/
theorem point_eq (hL : Law T.c.C) (m : Mem) (base : Addr) :
    T.MC.point base m = .affine (toM T.c.C.p (2 ^ (64 * T.c.n)) (wordsVal m base (T.c.sl RX) T.c.n))
      (toM T.c.C.p (2 ^ (64 * T.c.n)) (wordsVal m base (T.c.sl RY) T.c.n)) := by
  unfold Impl.Weierstrass.Mul.Curve.point
  rw [T.dq hL, T.dq hL]
  show Point.affine (toM _ _ (T.MC.toPoint.coordAt m base (T.c.sl RX)))
    (toM _ _ (T.MC.toPoint.coordAt m base (T.MC.pAt + 8 * T.c.n))) = _
  rw [T.pAt_y, T.coord_sv _ _ RX (by decide), T.coord_sv _ _ RY (by decide)]

theorem unch_of_mulKeeps {base : Addr} {m m' : Mem} (h : T.MC.Keeps base m m') : Unch base (mulKW T.c) m m' := by
  obtain h9 := T.n9
  intro x hx
  obtain e := fun w hw => hx w hw
  simp only [mulKW, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Cfg.sl, slot] at e
  obtain hb : ofs base x < 2 ^ 64 := (x - base).isLt
  obtain hlt : ofs base x < 64 + 8 * T.c.n * 45 := by omega_using [e, hb]
  obtain ex : x = base + BitVec.ofNat 64 (ofs base x) := by
    simp only [ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rw [BitVec.add_comm, BitVec.sub_add_cancel]
  rw [ex]
  refine h _ (by show _ < 8192; omega_using [hlt, h9]) ?_ ?_
  · simp only [Impl.Weierstrass.Mul.Curve.Own, Impl.Weierstrass.Mul.Curve.slot, Impl.Weierstrass.Mul.Curve.tmpAt,
      Impl.Weierstrass.Mul.Curve.bitsAt, true_and]
    omega_using [e, hb]
  · simp only [Impl.Weierstrass.Mul.Curve.pAt, Impl.Weierstrass.Mul.Curve.ptBytes, Impl.Weierstrass.Mul.Curve.slot]
    omega_using [e]

/-- What `tail` leaves. -/
abbrev TailPost (c : Cfg) (base : Addr) (s s' : State) : Prop :=
  Kc s s' ∧ Unch base (tailW c) s.mem s'.mem ∧
  word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) &&& maskOf (decide (sv c base s K < c.C.n)) &&&
    maskOf (!decide (sv c base s K = 0)) ∧
  (1 ≤ sv c base s K → sv c base s K < c.C.n →
    Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (sv c base s' RX)) (toM c.C.p (2 ^ (64 * c.n)) (sv c base s' RY))
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s' RZ))
      (Spec.Weierstrass.mul (sv c base s K) (.affine (toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX))
        (toM c.C.p (2 ^ (64 * c.n)) (sv c base s RY)))) ∧
    sv c base s' RX < c.C.p ∧ sv c base s' RY < c.C.p ∧ sv c base s' RZ < c.C.p) ∧
  sv c base s' XO < c.C.p ∧
  Fin.ofNat c.C.p (sv c base s' XO) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s' RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s' RZ) ^ (c.C.p - 2) ∧
  sv c base s' ACC < c.C.p ∧
  toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) = toM c.C.p (2 ^ (64 * c.n)) (sv c base s' RZ) ^ (c.C.p - 2)

/-- `tail` with a call of `mulName`, whose code is `mulCode`, that computes
`R = [d]P` as `vg_<curve>_mul`'s contract says (`hcall`, from the state after
the range's masks, which changes only the flag): the range of `d` into the
flag, `R = [d]P`, `Z^(p-2)`, and `x`. -/
theorem tailWith_ok (hC : ChainOkR (chainP T.c) (T.c.C.p - 2)) (hL : Law T.c.C) {mulName : String}
    {mulCode : Prog isa} {s : State} {base : Addr} (hw : WsReg s base)
    (h3 : s.gpr .s3 = base) (hc : Consts T.c base s)
    (hcall : ∀ s₁ : State, WsReg s₁ base → s₁.gpr .s3 = base → Kp s s₁ →
      Unch base [(T.c.sl FLAG, 8)] s.mem s₁.mem → s₁.syms = s.syms →
      WP isa (Cfg.wsCall mulName mulCode) s₁ fun s₂ => Kp s₁ s₂ ∧
        T.MC.ResultInRange (T.MC.scalar base s₁.mem) (T.MC.point base s₁.mem) base s₁.mem s₂.mem) :
    WP isa (tail T.c mulName mulCode) s fun s' => TailPost T.c base s s' := by
  obtain h9 := T.n9
  obtain h1 : 1 ≤ T.c.n := Nat.le_trans (by decide) T.n4
  obtain hown : 64 + 8 * T.c.n * 45 + 8 ≤ own T.c.n := own_ge h9
  obtain fit : ∀ {i}, i ≤ 55 → T.c.sl i + 8 * T.c.n ≤ 2 ^ 64 := fun hi => Nat.le_trans (sl_top h9 hi) (by decide)
  rw [tail]
  -- The range.
  refine WP.seq (WP.mono (show WP isa _ s fun s' => _ ∧ s'.syms = s.syms from
    let ⟨t, s', he, hq⟩ := range_ok T.c h9 hw; ⟨t, s', he, hq, Exec.syms he⟩) fun s₁ ⟨⟨K₁, O₁, f₁⟩, sy₁⟩ => ?_)
  obtain hw₁ := hw.of_kp K₁
  have U₁ := O₁.unch
  obtain e₁ : ∀ i, i < 44 → sv T.c base s₁ i = sv T.c base s i := fun i hi =>
    U₁.wordsVal (all_one (.inl (sl_le _ hi))) (fit (by omega_using [hi]))
  obtain hc₁ := hc.of_unch h9 U₁ (by kit_layout [h9, h1, hown])
  rw [hc.mn] at f₁
  -- The multiplication.
  refine WP.seq (WP.mono (hcall s₁ hw₁ (by rw [K₁.gpr _ (by decide)]; exact h3) K₁ U₁ sy₁)
    fun s₂ ⟨K₂, hp₂'⟩ => ?_)
  obtain ⟨hR, hK⟩ := hp₂'
  obtain U₂ : Unch base (mulKW T.c) s₁.mem s₂.mem := T.unch_of_mulKeeps hK
  obtain hw₂ := hw₁.of_kp K₂
  obtain hc₂ := hc₁.of_unch h9 U₂ (by kit_layout [h9, h1, hown])
  -- `Z^(p-2)`.
  refine WP.seq (WP.mono (chainPow_kit (P := chainP T.c) T.field_ok T.FPk T.FPm (chainLay T.c h1 h9) T.unit hw₂
    (one := T.c.sl ONEP) (by kit_layout [h9, h1, hown]) (by kit_layout [h9, h1, hown])
    (by show sv T.c base s₂ ONEP = _; rw [hc₂.onep, Nat.one_mul]) hC) fun s₃ ⟨K₃, U₃, lt₃, v₃⟩ => ?_)
  obtain hw₃ := hw₂.of_kc K₃
  obtain hc₃ := hc₂.of_unch h9 U₃ (by kit_layout [h9, h1, hown])
  -- `x`.
  refine WP.mono (T.affine_ok hw₃ (t := XM) (o := XO) (a := RX) (by decide) (by decide) (by decide) (by decide)
    lt₃ hc₃.one) fun s₄ ⟨K₄, U₄, lt₄, v₄⟩ => ?_
  obtain U₃₄ := U₃.trans U₄
  obtain e₄ : ∀ i ∈ [RX, RY, RZ], sv T.c base s₄ i = sv T.c base s₂ i := fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> exact U₃₄.wordsVal (by kit_layout [h9, h1, hown]) (fit (by decide))
  obtain fl₄ : word s₄.mem base (T.c.sl FLAG) = word s₁.mem base (T.c.sl FLAG) :=
    ((U₂.trans U₃).trans U₄).word (by kit_layout [h9, h1, hown]) (by kit_layout [h9, h1, hown])
  obtain k₁ : T.MC.scalar base s₁.mem = sv T.c base s K := by
    rw [← e₁ K (by decide)]; exact T.coord_sv _ _ K (by decide)
  obtain acc₄ : sv T.c base s₄ ACC = sv T.c base s₃ ACC := U₄.wordsVal (by kit_layout [h9, h1, hown]) (fit (by decide))
  have v₃' : toM T.c.C.p (2 ^ (64 * T.c.n)) (sv T.c base s₃ ACC) =
    toM T.c.C.p (2 ^ (64 * T.c.n)) (sv T.c base s₂ RZ) ^ (T.c.C.p - 2) := v₃
  refine ⟨K₁.kc.trans (K₂.kc.trans (K₃.trans K₄.kc)), ((U₁.trans U₂).trans U₃).trans U₄, by rw [fl₄, f₁], ?_, lt₄,
    ?_, by rw [acc₄]; exact lt₃, by rw [acc₄, v₃', e₄ RZ (by simp)]⟩
  · intro h1 hn
    rw [k₁, T.point_eq hL] at hR
    obtain ⟨⟨bx, by', bz⟩, hrep⟩ := hR h1 hn
    simp only [Impl.Weierstrass.Point.Curve.pointAt] at bx by' bz hrep
    obtain c0 : T.MC.toPoint.coordAt s₂.mem base T.MC.pAt = sv T.c base s₂ RX := T.coord_sv _ _ RX (by decide)
    obtain c1 : T.MC.toPoint.coordAt s₂.mem base (T.MC.pAt + Impl.Weierstrass.Point.elemBytes T.MC.toPoint.k) =
      sv T.c base s₂ RY := by
      rw [show T.MC.pAt + Impl.Weierstrass.Point.elemBytes T.MC.toPoint.k = T.c.sl RY from T.pAt_y]
      exact T.coord_sv _ _ RY (by decide)
    obtain c2 : T.MC.toPoint.coordAt s₂.mem base (T.MC.pAt + 2 * Impl.Weierstrass.Point.elemBytes T.MC.toPoint.k) =
      sv T.c base s₂ RZ := by
      rw [show T.MC.pAt + 2 * Impl.Weierstrass.Point.elemBytes T.MC.toPoint.k = T.c.sl RZ from T.pAt_z]
      exact T.coord_sv _ _ RZ (by decide)
    rw [c0, c1, c2] at hrep
    rw [c0] at bx; rw [c1] at by'; rw [c2] at bz
    rw [T.dq hL, T.dq hL, T.dq hL] at hrep
    rw [e₄ RX (by simp), e₄ RY (by simp), e₄ RZ (by simp), ← e₁ RX (by decide), ← e₁ RY (by decide)]
    exact ⟨rep_of_represents hrep, bx, by', bz⟩
  · rw [v₄, v₃', e₄ RX (by simp), e₄ RZ (by simp),
      show sv T.c base s₃ RX = sv T.c base s₂ RX from U₃.wordsVal (by kit_layout [h9, h1, hown]) (fit (by decide))]

/-- `tail` with the curve's multiplication, whose code `mulC` meets its contract. -/
theorem tail_ok (hC : ChainOkR (chainP T.c) (T.c.C.p - 2)) {mulN : String} {mulC : Prog isa}
    (hNF : mulC.noFrames = true) (hmul : Meets mulC (mulRVc T.MC)) (hL : Law T.c.C) {s : State} {base : Addr}
    (hw : WsReg s base) (h3 : s.gpr .s3 = base) (hc : Consts T.c base s) (hx : sv T.c base s RX < T.c.C.p)
    (hy : sv T.c base s RY < T.c.C.p)
    (hon : Spec.Weierstrass.onCurve T.c.C (.affine (toM T.c.C.p (2 ^ (64 * T.c.n)) (sv T.c base s RX))
      (toM T.c.C.p (2 ^ (64 * T.c.n)) (sv T.c base s RY))) = true) :
    WP isa (tail T.c mulN mulC) s fun s' => TailPost T.c base s s' := by
  obtain h9 := T.n9
  obtain h1 : 1 ≤ T.c.n := Nat.le_trans (by decide) T.n4
  obtain hown : 64 + 8 * T.c.n * 45 + 8 ≤ own T.c.n := own_ge h9
  refine T.tailWith_ok hC hL hw h3 hc fun s₁ hw₁ h3₁ K₁ U₁ _ => ?_
  obtain hc₁ := hc.of_unch h9 U₁ (by kit_layout [h9, h1, hown])
  obtain e₁ : ∀ i, i < 44 → sv T.c base s₁ i = sv T.c base s i := fun i hi =>
    U₁.wordsVal (all_one (.inl (sl_le _ hi))) (Nat.le_trans (sl_top h9 (by omega_using [hi])) (by decide))
  refine wsCallR_ok hNF hmul hw₁ h3₁ (fun t r w a m => ?_) fun s₂' s₂ K₂ mm₂ t a₂ m₂ hp₂ => ⟨K₂, ?_⟩
  · refine ⟨r, by rw [w, a], by rw [a]; exact hw₁.nowrap, by rw [a]; exact hw₁.al, ?_, ?_⟩
    · rw [a, m]
      refine ⟨(T.coord_sv _ _ MP (by decide)).trans hc₁.mp, (T.coord_sv _ _ ZERO (by decide)).trans hc₁.zero,
        (T.coord_sv _ _ ONEP (by decide)).trans hc₁.onep, (T.coord_sv _ _ AP (by decide)).trans hc₁.ap,
        (T.coord_sv _ _ B3P (by decide)).trans hc₁.b3p⟩
    · rw [a, m]
      refine ⟨?_, ?_, ?_⟩
      · show T.MC.toPoint.coordAt s₁.mem base (T.c.sl RX) < T.c.C.p
        rw [T.coord_sv _ _ RX (by decide)]; exact Nat.lt_of_le_of_lt (Nat.le_of_eq (e₁ RX (by decide))) hx
      · show T.MC.toPoint.coordAt s₁.mem base (T.MC.pAt + 8 * T.c.n) < T.c.C.p
        rw [T.pAt_y, T.coord_sv _ _ RY (by decide)]; exact Nat.lt_of_le_of_lt (Nat.le_of_eq (e₁ RY (by decide))) hy
      rw [T.point_eq hL]
      show Spec.Weierstrass.onCurve T.c.C (.affine (toM _ _ (sv T.c base s₁ RX)) (toM _ _ (sv T.c base s₁ RY))) = true
      rw [e₁ RX (by decide), e₁ RY (by decide)]; exact hon
  · have := hp₂
    simp only [mulRVc, State.withRegions_mem] at this
    rw [a₂, m₂, ← mm₂] at this
    exact this

/-! ## The check of a public point -/

/-- The curve of the check's contract (`Proof/Weierstrass/CheckPointContract.lean`), with the field
functions' own working space where RISC-V's are. -/
abbrev CC : Impl.Weierstrass.CheckPoint.Curve :=
  { W := T.c.C, curve := T.name, k := T.c.n, desc := T.cdesc, montOwn := own T.c.n, montOwnEnd := rvOwnEnd T.c.n }

/-- `fprog_ok`, for a field modulo `p`. -/
theorem fprog_kit {M : Mod} {base : Addr} {F : Field} {p : Nat} [NeZero p] (hF : FieldOk F) (hm : F.S.m = p)
    (hk : F.S.k = M.n) {Sl : Nat → Prop} (hL : Lay M (own M.n) Sl) (hS2 : Short Sl)
    (hU : UnitMod p (2 ^ (64 * M.n))) (ops : List FOp) {V : List Nat} {E : Nat → Fin p} {s : State}
    (hI : Inv M.n base p Sl V E s) (hS : ∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x) (hR : readsOk ops V = true) :
    WP isa (fprog F ops) s fun s' => KeepR M.n base (ops.map FOp.out) s s' ∧
      Inv M.n base p Sl (validAfter ops V) (runOps ops E) s' := by
  subst hm; exact fprog_ok hF hk hL hS2 hU ops hI hS hR

theorem sl_inj (c : Cfg) (h1 : 1 ≤ c.n) {i j : Nat} (h : c.sl i = c.sl j) : i = j := by
  simp only [Cfg.sl, slot] at h
  exact Nat.eq_of_mul_eq_mul_left (by omega_using [h1] : 0 < 8 * c.n) (by omega_using [h])

/-- The slots of the curve's equation, by number, and its operations on them. -/
abbrev curveIdx : List Nat := [AP, BP, CXM, CYM, W0, W1, W2, CPX]

abbrev curveOpsI : List FOp :=
  [.mul W0 CYM CYM, .mul W1 CXM CXM, .mul W2 W1 CXM, .mul W1 AP CXM, .add CPX W2 W1, .add W2 CPX BP,
    .sub W1 W0 W2]

theorem curveOps_eq (c : Cfg) : Cfg.curveOps c = curveOpsI.map (FOp.rename c.sl) := rfl

/-- The slots of the curve's equation. -/
abbrev curveSlots (c : Cfg) : List Nat := curveIdx.map c.sl

theorem rename_slots (σ : Nat → Nat) (op : FOp) :
    (op.rename σ).out :: (op.rename σ).ins = (op.out :: op.ins).map σ := by cases op <;> rfl

theorem curveLay (c : Cfg) (h9 : c.n ≤ 9) : Lay c.MP' (own c.n) (· ∈ curveSlots c) := by
  obtain hown := own_ge h9
  refine ⟨fun x hx => ?_, fun x y hx hy hne => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have : c.sl i + 8 * c.n ≤ c.sl 45 := sl_le c ((by decide : ∀ i ∈ curveIdx, i < 45) i hi)
    show c.sl i + 8 * c.n ≤ own c.n
    omega_using [this, hown]
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
    exact sl_sep c fun h => hne (congrArg c.sl h)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact sl_sep c ((by decide : ∀ i ∈ curveIdx, i ≠ MP) i hi)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact sl_sep c ((by decide : ∀ i ∈ curveIdx, i ≠ TMP) i hi)

theorem curveShort (c : Cfg) (h1 : 1 ≤ c.n) (h9 : c.n ≤ 9) : Short (· ∈ curveSlots c) := fun x hx => by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  have := sl_top h9 (i := i) ((by decide : ∀ i ∈ curveIdx, i ≤ 55) i hi)
  omega_using [this, h1]

theorem curve_run (c : Cfg) (h1 : 1 ≤ c.n) {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps (Cfg.curveOps c) e (c.sl W1) =
      e (c.sl CYM) * e (c.sl CYM) - ((e (c.sl CXM) * e (c.sl CXM) * e (c.sl CXM) +
        e (c.sl AP) * e (c.sl CXM)) + e (c.sl BP)) := by
  have h := congrFun (runOps_rename c.sl curveOpsI e fun _ _ _ hy => sl_inj c h1 hy) W1
  rw [curveOps_eq]
  refine h.trans ?_
  simp only [curveOpsI, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [W0, W1, W2, CYM, CXM, AP, BP, CPX, Nat.reduceEqDiff, ↓reduceIte]

/-- `y² - (x³ + a x + b)` to `W1`. -/
theorem curve_ok {s : State} {base : Addr} (hw : WsReg s base)
    (hlt : ∀ x ∈ [CXM, CYM, AP, BP], sv T.c base s x < T.c.C.p) :
    WP isa (fprog T.c.FP (Cfg.curveOps T.c)) s fun s' =>
      KeepR T.c.n base ((Cfg.curveOps T.c).map FOp.out) s s' ∧
      sv T.c base s' W1 < T.c.C.p ∧
      toM T.c.C.p (2 ^ (64 * T.c.n)) (sv T.c base s' W1) =
        toM T.c.C.p (2 ^ (64 * T.c.n)) (sv T.c base s CYM) * toM T.c.C.p (2 ^ (64 * T.c.n)) (sv T.c base s CYM) -
          ((toM T.c.C.p (2 ^ (64 * T.c.n)) (sv T.c base s CXM) * toM T.c.C.p (2 ^ (64 * T.c.n)) (sv T.c base s CXM) *
            toM T.c.C.p (2 ^ (64 * T.c.n)) (sv T.c base s CXM) + toM T.c.C.p (2 ^ (64 * T.c.n)) (sv T.c base s AP) *
            toM T.c.C.p (2 ^ (64 * T.c.n)) (sv T.c base s CXM)) + toM T.c.C.p (2 ^ (64 * T.c.n)) (sv T.c base s BP)) := by
  obtain h1 : 1 ≤ T.c.n := Nat.le_trans (by decide) T.n4
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt
  obtain hW1 : T.c.sl W1 ∈ validAfter (Cfg.curveOps T.c) [T.c.sl CXM, T.c.sl CYM, T.c.sl AP, T.c.sl BP] :=
    (mem_validAfter _ _).mpr (.inr (by
      rw [curveOps_eq, List.map_map]
      exact List.mem_map.mpr ⟨.sub W1 W0 W2, List.getElem_mem (show 6 < curveOpsI.length by decide), rfl⟩))
  refine WP.mono (fprog_kit (M := T.c.MP') (F := T.c.FP) T.field_ok T.FPm T.FPk (curveLay T.c T.n9)
    (curveShort T.c h1 T.n9) T.unit
    (Cfg.curveOps T.c) (V := [T.c.sl CXM, T.c.sl CYM, T.c.sl AP, T.c.sl BP])
    (E := fun x => toM T.c.C.p (2 ^ (64 * T.c.n)) (wordsVal s.mem base x T.c.n))
    ⟨hw, fun x hx => ?_, fun x hx => ?_, fun _ _ => rfl⟩ (fun op hop x hx => ?_) ?_)
    fun s' ⟨K, I⟩ => ⟨K, I.lt _ hW1, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (show x ∈ ([CXM, CYM, AP, BP] : List Nat).map T.c.sl from hx)
    exact List.mem_map_of_mem ((by decide : ∀ i ∈ ([CXM, CYM, AP, BP] : List Nat), i ∈ curveIdx) i hi)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hlt.1
    · exact hlt.2.1
    · exact hlt.2.2.1
    · exact hlt.2.2.2
  · rw [curveOps_eq] at hop
    obtain ⟨op', hop', rfl⟩ := List.mem_map.mp hop
    rw [rename_slots] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact List.mem_map_of_mem ((by decide : ∀ op ∈ curveOpsI, ∀ y ∈ op.out :: op.ins, y ∈ curveIdx) op' hop' y hy)
  · rw [curveOps_eq]
    exact readsOk_rename T.c.sl (V := [CXM, CYM, AP, BP]) (by decide)
  · have v := I.val (T.c.sl W1) hW1
    exact v.trans (curve_run T.c h1 (F := Fe T.c.C) _)

theorem num_eq (m : Mem) (ws : Addr) (i : Nat) (hi : i < 100) :
    T.CC.num ws m (T.CC.slot i) = wordsVal m ws (T.c.sl i) T.c.n := by
  unfold Impl.Weierstrass.CheckPoint.Curve.num
  rw [Impl.Weierstrass.Mont.numAt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 8 T.n9) (Nat.le_of_lt_succ hi)
    simp only [Impl.Weierstrass.CheckPoint.Curve.slot]; omega_using [this])]
  exact read_eq_wordsVal m ws T.c.n _

theorem flag_eq (m : Mem) (ws : Addr) : T.CC.flag ws m = word m ws (T.c.sl FLAG) := by
  unfold Impl.Weierstrass.CheckPoint.Curve.flag
  simp only [word, off, Mem.readW]
  rfl

theorem keeps_of_unch {ws : Addr} {m m' : Mem} (hu : Unch ws (chkW T.c) m m') : T.CC.Keeps ws m m' := by
  obtain h9 := T.n9
  obtain h4 := T.n4
  obtain hown : 64 + 8 * T.c.n * 45 + 8 ≤ own T.c.n := own_ge h9
  obtain hcs : (T.c.n ≤ 6 ∧ own T.c.n = 4096 - 64 * T.c.n ∧ rvOwnEnd T.c.n = 4096) ∨
      (6 < T.c.n ∧ own T.c.n = 8192 - 64 * T.c.n ∧ rvOwnEnd T.c.n = 8192) := rvOwn_cases T.c.n
  intro i hi hown' hout
  have h8 : Impl.Weierstrass.Mont.wsBytes = 8192 := rfl
  refine hu _ ?_
  rw [show ws + BitVec.ofNat 64 i = off ws i from rfl, ofs_off0 ws (by omega_using [hi, h8])]
  simp only [Impl.Weierstrass.CheckPoint.Curve.Own, Impl.Weierstrass.CheckPoint.Curve.Out,
    Impl.Weierstrass.CheckPoint.Curve.slot, Impl.Weierstrass.CheckPoint.Curve.flagAt,
    List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, not_or] at hown' hout
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq,
    chkW, Cfg.curveOps, List.map_cons, List.map_nil, FOp.out, Cfg.sl, slot, FLAG, TMP, CXM, CYM, W0, W1, W2,
    CPX, CPY]
  omega_using [hown', hout, h9, h4, hown, hcs]

/-- The validity the masks compute. -/
theorem masks_valid {x y w1 xm ym : Nat} (hw1 : w1 < T.c.C.p)
    (hxm : xm = x * 2 ^ (64 * T.c.n) % T.c.C.p) (hym : ym = y * 2 ^ (64 * T.c.n) % T.c.C.p)
    (hv : toM T.c.C.p (2 ^ (64 * T.c.n)) w1 =
      toM T.c.C.p (2 ^ (64 * T.c.n)) ym * toM T.c.C.p (2 ^ (64 * T.c.n)) ym -
      ((toM T.c.C.p (2 ^ (64 * T.c.n)) xm * toM T.c.C.p (2 ^ (64 * T.c.n)) xm * toM T.c.C.p (2 ^ (64 * T.c.n)) xm +
        Fin.ofNat T.c.C.p T.c.C.a * toM T.c.C.p (2 ^ (64 * T.c.n)) xm) + Fin.ofNat T.c.C.p T.c.C.b)) :
    maskOf (decide (x < T.c.C.p)) &&& maskOf (decide (y < T.c.C.p)) &&& maskOf (decide (w1 = 0)) =
      Impl.Weierstrass.CheckPoint.Curve.mask (T.CC.Valid x y) := by
  rw [hxm, hym, toM_mont T.unit, toM_mont T.unit] at hv
  unfold Impl.Weierstrass.CheckPoint.Curve.mask Impl.Weierstrass.CheckPoint.Curve.Valid
  show _ = if x < T.c.C.p ∧ y < T.c.C.p ∧
      Spec.Weierstrass.onCurve T.c.C (.affine (Fin.ofNat T.c.C.p x) (Fin.ofNat T.c.C.p y)) = true
    then BitVec.allOnes 64 else 0
  by_cases hx : x < T.c.C.p
  · by_cases hy : y < T.c.C.p
    · have e : w1 = 0 ↔ VG.Proof.Ecdh.OnCurveF T.c.C x y := by
        rw [← toM_eq_zero_iff T.unit hw1, hv]
      obtain ex : (Fin.ofNat T.c.C.p x : Fe T.c.C) = ⟨x, hx⟩ := VG.Proof.EcKey.fe_eq hx rfl
      obtain ey : (Fin.ofNat T.c.C.p y : Fe T.c.C) = ⟨y, hy⟩ := VG.Proof.EcKey.fe_eq hy rfl
      obtain hc : Spec.Weierstrass.onCurve T.c.C (.affine (Fin.ofNat T.c.C.p x) (Fin.ofNat T.c.C.p y)) = true ↔
          w1 = 0 := by
        rw [ex, ey, VG.Proof.Ecdh.onCurve_iff hx hy, ← e]
      by_cases h0 : w1 = 0 <;> simp [hx, hy, h0, hc, maskOf]
    · simp [hy, maskOf]
  · simp [hx, maskOf]

theorem unch_of_checkKeeps {base : Addr} {m m' : Mem} (h : T.CC.Keeps base m m') :
    Unch base (checkKW T.c) m m' := by
  obtain h9 := T.n9
  obtain hcs : (T.c.n ≤ 6 ∧ own T.c.n = 4096 - 64 * T.c.n ∧ rvOwnEnd T.c.n = 4096) ∨
      (6 < T.c.n ∧ own T.c.n = 8192 - 64 * T.c.n ∧ rvOwnEnd T.c.n = 8192) := rvOwn_cases T.c.n
  intro x hx
  obtain e := fun w hw => hx w hw
  simp only [checkKW, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Cfg.sl, slot,
    FLAG] at e
  obtain hb : ofs base x < 2 ^ 64 := (x - base).isLt
  obtain hlt : ofs base x < 8192 := by omega_using [e, hb]
  obtain ex : x = base + BitVec.ofNat 64 (ofs base x) := by
    simp only [ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rw [BitVec.add_comm, BitVec.sub_add_cancel]
  rw [ex]
  refine h _ hlt ?_ ?_
  · simp only [Impl.Weierstrass.CheckPoint.Curve.Own, Impl.Weierstrass.CheckPoint.Curve.slot,
      List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, not_or]
    omega_using [e, hcs, h9]
  · simp only [Impl.Weierstrass.CheckPoint.Curve.Out, Impl.Weierstrass.CheckPoint.Curve.slot,
      Impl.Weierstrass.CheckPoint.Curve.flagAt,
      List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, not_or]
    omega_using [e]

/-- `vg_<curve>_check_point` meets its contract. -/
theorem check_rv (s : State) (hs : (checkRVc T.CC).pre s) :
    ∃ t s', Exec isa (Cfg.checkFn T.c) s t s' ∧ abiPreserved s s' ∧ (checkRVc T.CC).post s s' := by
  obtain h9 := T.n9
  obtain h4 := T.n4
  obtain h1 : 1 ≤ T.c.n := Nat.le_trans (by decide) T.n4
  obtain hown : 64 + 8 * T.c.n * 45 + 8 ≤ own T.c.n := own_ge h9
  obtain hp0 : 0 < T.c.C.p := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain fit : ∀ {i}, i ≤ 55 → T.c.sl i + 8 * T.c.n ≤ 2 ^ 64 := fun hi => Nat.le_trans (sl_top h9 hi) (by decide)
  obtain hl : ∀ i, i < 45 → T.c.sl i + 8 * T.c.n ≤ own T.c.n := fun i hi => by
    have : T.c.sl i + 8 * T.c.n ≤ T.c.sl 45 := sl_le T.c hi
    omega_using [this, own_ge h9]
  obtain hs4 : ∀ i, i < 45 → T.c.sl i < 4095 := fun i hi => by
    have := sl_top h9 (i := i) (by omega_using [hi])
    omega_using [this, h1]
  obtain ⟨-, hwr, hfit, hal, ⟨hp, hr2, ha, hb, hf⟩⟩ := hs
  generalize hb0 : s.gpr .a0 = base at hwr hfit hal hp hr2 ha hb hf
  obtain hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_singleton_self _
  suffices h : WP isa (Cfg.checkFn T.c) s fun s' => abiPreserved s s' ∧ (checkRVc T.CC).post s s' by
    obtain ⟨t, s', he, h⟩ := h; exact ⟨t, s', he, h⟩
  obtain t8 := sl8 T.c TMP
  rw [Cfg.checkFn, show Cfg.checkSave T.c = T.c.sl TMP from rfl]
  refine WP.seq (sd_a0 hb0 hwr' hal (d := T.c.sl TMP) (by kit_layout [h9]) t8 fun s₁ u₁ => ?_)
  refine sd_a0 (by rw [u₁.gpr]; exact hb0) (by rw [u₁.wr]; exact hwr') hal (d := T.c.sl TMP + 8)
    (by kit_layout [h9]) (by omega_using [t8]) fun s₂ u₂ => wp_mv fun s₃ u₃ => WP.block_nil ?_
  obtain g₃ : ∀ r, r ≠ .s0 → s₃.gpr r = s.gpr r := fun r hr => by rw [u₃.other r hr, u₂.gpr, u₁.gpr]
  obtain hw₃ : WsReg s₃ base := ⟨by rw [u₃.gpr, u₂.gpr, u₁.gpr, hb0], by rw [u₃.wr, u₂.wr, u₁.wr]; exact hwr',
    hfit, hal⟩
  obtain m₃ : s₃.mem = (s.mem.writeW (off base (T.c.sl TMP)) (s.gpr .s0)).writeW (off base (T.c.sl TMP + 8))
      (s.gpr .ra) := by
    simp only [u₃.mem, u₂.mem, u₁.mem, u₁.gpr]
  obtain U₃ : Unch base [(T.c.sl TMP, 8), (T.c.sl TMP + 8, 8)] s.mem s₃.mem := by
    rw [m₃]
    exact (writeW_outside _ _ _ (by kit_layout [h9])).unch.trans (writeW_outside _ _ _ (by kit_layout [h9])).unch
  -- The masks.
  refine WP.seq (WP.mono (masks_ok T.c h9 hw₃) fun s₄ ⟨K₄, O₄, f₄⟩ => ?_)
  obtain hw₄ := hw₃.of_kp K₄
  obtain U₄ := U₃.trans O₄.unch
  -- `x R` and `y R`.
  obtain hr2' : sv T.c base s₄ R2P = 2 ^ (64 * T.c.n) * 2 ^ (64 * T.c.n) % T.c.C.p := by
    rw [show sv T.c base s₄ R2P = sv T.c base s R2P from
      U₄.wordsVal (by kit_layout [h9, h4, hown]) (fit (by decide))]
    exact (T.num_eq s.mem base R2P (by decide)).symm.trans hr2
  refine WP.seq (WP.mono (mulCall_kit T.field_ok T.FPk T.FPm hw₄ (o := T.c.sl CXM) (a := T.c.sl CX)
    (b := T.c.sl R2P) (hl _ (by decide)) (hl _ (by decide)) (hl _ (by decide)) (hs4 _ (by decide))
    (hs4 _ (by decide)) (hs4 _ (by decide))
    (by show sv T.c base s₄ R2P < T.c.C.p; rw [hr2']; exact Nat.mod_lt _ hp0))
    fun s₅ ⟨C₅, lt₅, e₅⟩ => ?_)
  obtain hw₅ := hw₄.of_kp C₅.kp
  have U₅ : Unch base [(T.c.sl CXM, 8 * T.c.n), (own T.c.n, 64 * T.c.n)] s₄.mem s₅.mem := C₅.mem
  obtain r2₅ : sv T.c base s₅ R2P = sv T.c base s₄ R2P := U₅.wordsVal (by kit_layout [h9, h4, hown]) (fit (by decide))
  refine WP.seq (WP.mono (mulCall_kit T.field_ok T.FPk T.FPm hw₅ (o := T.c.sl CYM) (a := T.c.sl CY)
    (b := T.c.sl R2P) (hl _ (by decide)) (hl _ (by decide)) (hl _ (by decide)) (hs4 _ (by decide))
    (hs4 _ (by decide)) (hs4 _ (by decide))
    (by show sv T.c base s₅ R2P < T.c.C.p; rw [r2₅, hr2']; exact Nat.mod_lt _ hp0))
    fun s₆ ⟨C₆, lt₆, e₆⟩ => ?_)
  obtain hw₆ := hw₅.of_kp C₆.kp
  have U₆ : Unch base [(T.c.sl CYM, 8 * T.c.n), (own T.c.n, 64 * T.c.n)] s₅.mem s₆.mem := C₆.mem
  -- The values so far, from the contract's.
  obtain x₄ : sv T.c base s₄ CX = T.CC.num base s.mem T.CC.xAt := by
    rw [show sv T.c base s₄ CX = sv T.c base s CX from U₄.wordsVal (by kit_layout [h9, h4, hown]) (fit (by decide))]
    exact (T.num_eq s.mem base CX (by decide)).symm
  obtain y₅ : sv T.c base s₅ CY = T.CC.num base s.mem T.CC.yAt := by
    rw [show sv T.c base s₅ CY = sv T.c base s CY from
      (U₄.trans U₅).wordsVal (by kit_layout [h9, h4, hown]) (fit (by decide))]
    exact (T.num_eq s.mem base CY (by decide)).symm
  obtain xm₆ : sv T.c base s₆ CXM = T.CC.num base s.mem T.CC.xAt * 2 ^ (64 * T.c.n) % T.c.C.p := by
    rw [show sv T.c base s₆ CXM = sv T.c base s₅ CXM from
      U₆.wordsVal (by kit_layout [h9, h4, hown]) (fit (by decide)), ← x₄]
    refine mont_eq T.unit lt₅ (e₅.trans ?_)
    show sv T.c base s₄ CX * sv T.c base s₄ R2P % T.c.C.p = _
    rw [hr2']
  obtain ym₆ : sv T.c base s₆ CYM = T.CC.num base s.mem T.CC.yAt * 2 ^ (64 * T.c.n) % T.c.C.p := by
    rw [← y₅]
    refine mont_eq T.unit lt₆ (e₆.trans ?_)
    show sv T.c base s₅ CY * sv T.c base s₅ R2P % T.c.C.p = _
    rw [r2₅, hr2']
  obtain ap₆ : sv T.c base s₆ AP = T.c.C.a * 2 ^ (64 * T.c.n) % T.c.C.p := by
    rw [show sv T.c base s₆ AP = sv T.c base s AP from
      ((U₄.trans U₅).trans U₆).wordsVal (by kit_layout [h9, h4, hown]) (fit (by decide))]
    exact (T.num_eq s.mem base AP (by decide)).symm.trans ha
  obtain bp₆ : sv T.c base s₆ BP = T.c.C.b * 2 ^ (64 * T.c.n) % T.c.C.p := by
    rw [show sv T.c base s₆ BP = sv T.c base s BP from
      ((U₄.trans U₅).trans U₆).wordsVal (by kit_layout [h9, h4, hown]) (fit (by decide))]
    exact (T.num_eq s.mem base BP (by decide)).symm.trans hb
  -- The curve's equation.
  refine WP.seq (WP.mono (T.curve_ok hw₆ (fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rw [xm₆]; exact Nat.mod_lt _ hp0
    · rw [ym₆]; exact Nat.mod_lt _ hp0
    · rw [ap₆]; exact Nat.mod_lt _ hp0
    · rw [bp₆]; exact Nat.mod_lt _ hp0)) fun s₇ ⟨K₇, lt₇, v₇⟩ => ?_)
  obtain hw₇ := hw₆.of_kp K₇.kp
  have U₇ : Unch base (((Cfg.curveOps T.c).map FOp.out).map (fun w => (w, 8 * T.c.n)) ++
      [(own T.c.n, 64 * T.c.n)]) s₆.mem s₇.mem := K₇.mem
  -- The mask of the equation, and the flag.
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (zeroMask_ok hw₇ (n := T.c.n) (a := T.c.sl W1) (sl8 _ _)
    (sl_top h9 (by decide))) fun s₈ ⟨r₈, m₈, g₈⟩ => ?_)
  obtain hw₈ := hw₇.of_rest r₈
  refine WP.block_append (WP.mono (andFlag_ok T.c h9 hw₈) fun s₉ ⟨f₉, r₉, O₉⟩ => ?_)
  obtain hw₉ := hw₈.of_rest r₉
  refine ldAt_ws hw₉ (d := T.c.sl FLAG) (by kit_layout [h9]) (sl8 _ _) fun s₁₀ u₁₀ => ?_
  obtain hw₁₀ := hw₉.of_kp (Kp.of_upd u₁₀)
  -- The flag's value.
  obtain U₃₇ := ((U₄.trans U₅).trans U₆).trans U₇
  obtain fl₇ : word s₇.mem base (T.c.sl FLAG) = word s₄.mem base (T.c.sl FLAG) :=
    ((U₅.trans U₆).trans U₇).word (by kit_layout [h9, h4, hown]) (by kit_layout [h9])
  obtain fl₃ : word s₃.mem base (T.c.sl FLAG) = word s.mem base (T.c.sl FLAG) :=
    U₃.word (by kit_layout [h9, h4, hown]) (by kit_layout [h9])
  obtain e₃ : ∀ i ∈ [CX, CY, MP], sv T.c base s₃ i = sv T.c base s i := fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> exact U₃.wordsVal (by kit_layout [h9, h4, hown]) (fit (by decide))
  obtain hpw : sv T.c base s MP = T.c.C.p := (T.num_eq s.mem base MP (by decide)).symm.trans hp
  rw [e₃ CX (by decide), e₃ CY (by decide), e₃ MP (by decide), hpw, fl₃] at f₄
  obtain hxv : sv T.c base s CX = T.CC.num base s.mem T.CC.xAt := (T.num_eq s.mem base CX (by decide)).symm
  obtain hyv : sv T.c base s CY = T.CC.num base s.mem T.CC.yAt := (T.num_eq s.mem base CY (by decide)).symm
  rw [hxv, hyv] at f₄
  obtain hv := T.masks_valid lt₇ xm₆ ym₆ (by rw [v₇, ap₆, bp₆, toM_mont T.unit, toM_mont T.unit])
  generalize hx : T.CC.num base s.mem T.CC.xAt = x at *
  generalize hy : T.CC.num base s.mem T.CC.yAt = y at *
  obtain hF : word s₉.mem base (T.c.sl FLAG) =
      T.CC.flag base s.mem &&& Impl.Weierstrass.CheckPoint.Curve.mask (T.CC.Valid x y) := by
    rw [f₉, m₈, g₈, fl₇, f₄, T.flag_eq, ← hv]; simp only [BitVec.and_assoc]
  generalize hFv : T.CC.flag base s.mem &&& Impl.Weierstrass.CheckPoint.Curve.mask (T.CC.Valid x y) = F at hF
  obtain hFm : F = if decide (F ≠ 0) then BitVec.allOnes 64 else 0 := by
    rw [← hFv]
    unfold Impl.Weierstrass.CheckPoint.Curve.mask
    rcases hf with h | h <;> rw [h] <;> split <;> decide
  obtain a₁₀ : s₁₀.gpr .a7 = if decide (F ≠ 0) then BitVec.allOnes 64 else 0 := by
    rw [u₁₀.gpr]; exact hF.trans hFm
  -- The point.
  refine WP.block_append (WP.mono (sel_ok (decide (F ≠ 0)) T.c.n hw₁₀ a₁₀ (o := T.c.sl CPX) (a := T.c.sl GX)
    (b := T.c.sl CXM) (sl8 _ _) (sl8 _ _) (sl8 _ _) (sl_top h9 (by decide)) (sl_top h9 (by decide))
    (sl_top h9 (by decide)) (.inr (sl_le _ (by decide))) (.inr (sl_le _ (by decide))))
    fun s₁₁ ⟨e₁₁, r₁₁, O₁₁⟩ => ?_)
  obtain hw₁₁ := hw₁₀.of_rest r₁₁
  obtain a₁₁ : s₁₁.gpr .a7 = if decide (F ≠ 0) then BitVec.allOnes 64 else 0 := by
    rw [r₁₁.gpr _ (by decide), a₁₀]
  refine WP.block_append (WP.mono (sel_ok (decide (F ≠ 0)) T.c.n hw₁₁ a₁₁ (o := T.c.sl CPY) (a := T.c.sl GY)
    (b := T.c.sl CYM) (sl8 _ _) (sl8 _ _) (sl8 _ _) (sl_top h9 (by decide)) (sl_top h9 (by decide))
    (sl_top h9 (by decide)) (.inr (sl_le _ (by decide))) (.inr (sl_le _ (by decide))))
    fun s₁₂ ⟨e₁₂, r₁₂, O₁₂⟩ => ?_)
  obtain hw₁₂ := hw₁₁.of_rest r₁₂
  -- What changed.
  obtain U₉ : Unch base [(T.c.sl FLAG, 8)] s₇.mem s₉.mem := by rw [← m₈]; exact O₉.unch
  have m₁₀ : s₁₀.mem = s₉.mem := u₁₀.mem
  obtain Uend : Unch base [(T.c.sl FLAG, 8), (T.c.sl CPX, 8 * T.c.n), (T.c.sl CPY, 8 * T.c.n)] s₇.mem s₁₂.mem := by
    have := (U₉.trans (by rw [← m₁₀]; exact O₁₁.unch)).trans O₁₂.unch
    exact this
  obtain U₆₁₂ := U₇.trans Uend
  obtain Uall : Unch base (chkW T.c) s.mem s₁₂.mem := U₃₇.trans Uend
  -- The loads.
  obtain U₄₁₂ := ((((O₄.unch.trans U₅).trans U₆).trans U₇).trans Uend)
  obtain w36 : word s₁₂.mem base (T.c.sl TMP + 8) = s.gpr .ra := by
    rw [U₄₁₂.word (by kit_layout [h9, h4, hown]) (by kit_layout [h9]), m₃, word_writeW_self]
  obtain w28 : word s₁₂.mem base (T.c.sl TMP) = s.gpr .s0 := by
    rw [U₄₁₂.word (by kit_layout [h9, h4, hown]) (by kit_layout [h9]), m₃,
      (writeW_outside (d := T.c.sl TMP + 8) _ base _ (by kit_layout [h9])).word (by omega_using [])
        (by kit_layout [h9]), word_writeW_self]
  obtain Kp₁₂ : Kp s₃ s₁₂ := K₄.trans (C₅.kp.trans (C₆.kp.trans (K₇.kp.trans ((Kp.of_rest r₈).trans
    ((Kp.of_rest r₉).trans ((Kp.of_upd u₁₀).trans ((Kp.of_rest r₁₁).trans (Kp.of_rest r₁₂))))))))
  refine ld_ws hw₁₂ (d := T.c.sl TMP + 8) (by kit_layout [h9]) (by omega_using [t8]) fun s₁₃ u₁₃ => ?_
  obtain hw₁₃ := hw₁₂.of_kp (Kp.of_upd u₁₃)
  refine ld_ws hw₁₃ (d := T.c.sl TMP) (by kit_layout [h9]) t8 fun s₁₄ u₁₄ =>
    WP.block_nil ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · by_cases h0 : r = .s0
    · subst h0; rw [u₁₄.gpr, u₁₃.mem, w28]
    rw [u₁₄.other _ h0, u₁₃.other _ (fun e => by subst e; revert hr; decide), Kp₁₂.gpr r hr, g₃ r h0]
  · rw [u₁₄.sp, u₁₃.sp, Kp₁₂.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₁₄.other _ (by decide), u₁₃.gpr, w36]
  · have m₁₄ : s₁₄.mem = s₁₂.mem := by rw [u₁₄.mem, u₁₃.mem]
    show T.CC.post (s.gpr .a0) s.mem s₁₄.mem
    rw [hb0, m₁₄]
    obtain xm : sv T.c base s₁₂ CXM = x * 2 ^ (64 * T.c.n) % T.c.C.p := by
      rw [show sv T.c base s₁₂ CXM = sv T.c base s₆ CXM from
        U₆₁₂.wordsVal (by kit_layout [h9, h4, hown]) (fit (by decide)), xm₆]
    obtain ym : sv T.c base s₁₂ CYM = y * 2 ^ (64 * T.c.n) % T.c.C.p := by
      rw [show sv T.c base s₁₂ CYM = sv T.c base s₆ CYM from
        U₆₁₂.wordsVal (by kit_layout [h9, h4, hown]) (fit (by decide)), ym₆]
    refine ⟨?_, ?_, ?_, ?_, ?_, T.keeps_of_unch Uall⟩
    · have U' : Unch base ([(T.c.sl CPX, 8 * T.c.n)] ++ [(T.c.sl CPY, 8 * T.c.n)]) s₉.mem s₁₂.mem := by
        rw [← m₁₀]; exact O₁₁.unch.trans O₁₂.unch
      rw [T.flag_eq, U'.word (by kit_layout [h9, h4, hown]) (by kit_layout [h9]), hF, hx, hy, hFv]
    · rw [hx]
      refine (T.num_eq _ _ CXM (by decide)).trans (xm.trans ?_)
      rfl
    · rw [hy]
      refine (T.num_eq _ _ CYM (by decide)).trans (ym.trans ?_)
      rfl
    · have U' : Unch base ([(T.c.sl CPX, 8 * T.c.n)] ++ [(T.c.sl CPY, 8 * T.c.n)]) s₁₀.mem s₁₂.mem :=
        O₁₁.unch.trans O₁₂.unch
      obtain U'' := U₃₇.trans U₉
      rw [← m₁₀] at U''
      obtain h1' : sv T.c base s₁₂ CPX = sv T.c base s₁₁ CPX :=
        O₁₂.unch.wordsVal (by kit_layout [h9, h4, hown]) (fit (by decide))
      obtain h2 : sv T.c base s₁₀ CXM = sv T.c base s₁₂ CXM :=
        (U'.wordsVal (by kit_layout [h9, h4, hown]) (fit (by decide))).symm
      obtain h3 : sv T.c base s₁₀ GX = sv T.c base s GX :=
        U''.wordsVal (by kit_layout [h9, h4, hown]) (fit (by decide))
      rw [hx, hy, hFv, show T.CC.pxAt = T.CC.slot CPX from rfl, show T.CC.gxAt = T.CC.slot GX from rfl,
        T.num_eq _ _ CPX (by decide), T.num_eq _ _ GX (by decide)]
      show sv T.c base s₁₂ CPX = if F = 0 then sv T.c base s GX else _
      rw [h1']; show wordsVal s₁₁.mem _ _ _ = _; rw [e₁₁]
      show (if decide (F ≠ 0) = true then sv T.c base s₁₀ CXM else sv T.c base s₁₀ GX) = _
      rw [h2, h3, xm]
      by_cases h : F = 0 <;> simp [h] <;> rfl
    · have O' := O₁₁
      rw [m₁₀] at O'
      obtain U'' := (U₃₇.trans U₉).trans O'.unch
      obtain h2 : sv T.c base s₁₁ CYM = sv T.c base s₁₂ CYM :=
        (O₁₂.unch.wordsVal (by kit_layout [h9, h4, hown]) (fit (by decide))).symm
      obtain h3 : sv T.c base s₁₁ GY = sv T.c base s GY :=
        U''.wordsVal (by kit_layout [h9, h4, hown]) (fit (by decide))
      rw [hx, hy, hFv, show T.CC.pyAt = T.CC.slot CPY from rfl, show T.CC.gyAt = T.CC.slot GY from rfl,
        T.num_eq _ _ CPY (by decide), T.num_eq _ _ GY (by decide)]
      show wordsVal s₁₂.mem _ _ _ = if F = 0 then sv T.c base s GY else _
      rw [e₁₂]
      show (if decide (F ≠ 0) = true then sv T.c base s₁₁ CYM else sv T.c base s₁₁ GY) = _
      rw [h2, h3, ym]
      by_cases h : F = 0 <;> simp [h] <;> rfl

/-! ## Layout facts of what the check and `tail` write -/

theorem checkKW_lo (c : Cfg) (h9 : c.n ≤ 9) : ∀ w ∈ checkKW c, 40 ≤ w.1 := by
  obtain hown : 64 + 8 * c.n * 45 + 8 ≤ own c.n := own_ge h9
  kit_layout [h9, hown]

/-- The check keeps the constants `tail` reads, and `d`. -/
theorem checkKW_keep (c : Cfg) (h9 : c.n ≤ 9) :
    ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP, K], ∀ w ∈ checkKW c,
      c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  obtain hown : 64 + 8 * c.n * 45 + 8 ≤ own c.n := own_ge h9
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> kit_layout [h9, hown]

theorem tailW_lo (c : Cfg) (h9 : c.n ≤ 9) : ∀ w ∈ tailW c, 40 ≤ w.1 := by
  obtain hown : 64 + 8 * c.n * 45 + 8 ≤ own c.n := own_ge h9
  kit_layout [h9, hown]

/-- `tail` keeps one. -/
theorem tailW_one (c : Cfg) (h9 : c.n ≤ 9) :
    ∀ w ∈ tailW c, c.sl ONE + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl ONE := by
  obtain hown : 64 + 8 * c.n * 45 + 8 ≤ own c.n := own_ge h9
  kit_layout [h9, hown]

/-- The constants' slots. -/
theorem consts_le (c : Cfg) : ∀ e ∈ consts c, e.1 ≤ 55 := fun e he =>
  (by decide : ∀ i ∈ cslots, i ≤ 55) _ (mem_cslots he)

end TKit

end VG.Proof.Ecdh.RISCV64
