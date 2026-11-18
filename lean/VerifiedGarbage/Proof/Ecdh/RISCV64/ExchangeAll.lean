module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
import VerifiedGarbage.Proof.Ecdh.RISCV64.Masks
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
public import VerifiedGarbage.Proof.Ecdh.Exchange
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Weierstrass.Words

/-!
# ECDH on RISC-V: correctness, for every curve

`vg_ecdh_<curve>` meets its contract by register, given the group law
(`Kit.ecdh_ok`), once for every curve: what the proof needs of a curve is its
`Kit`: the code's configuration, the bytes of its numbers, how the code reads
and writes them (`load`, `store`: whole words, or a top word of fewer bytes),
the check of the peer's point and what follows the point's setup
(`<Curve>/Tail.lean`), and the layout facts of its working space.

The proof is the setup (`setup_ok`: the saves, `d`, the peer's `x` and `y`
and the mask of its first byte, the constants), the check of the peer's
point (`check_ok`, by its call), the point (or `G`) to `R`'s first two
slots, the kit's `tail_ok`, and the result under the flag (`fin_ok`); the
specification's shared secret is `exchange_eq`'s (`Proof/Ecdh/Exchange.lean`).
Each `<Curve>/Exchange.lean` is the curve's kit, and the statements about it
that other modules use.
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.X25519.RISCV64 (Rest)
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

/-- The peer's key: `04`, `x` and `y`. -/
theorem peer_bytes (m : Mem) (p : Addr) (L : Nat) :
    bytesAt m p (1 + 2 * L) = m p :: (bytesAt m (p + BitVec.ofNat 64 1) L ++
      bytesAt m (p + BitVec.ofNat 64 (1 + L)) L) := by
  obtain h1 : bytesAt m p 1 = [m p] := by
    simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero]
  rw [show 1 + 2 * L = 1 + (L + L) by omega_using [], VG.Proof.Weierstrass.bytesAt_add,
    VG.Proof.Weierstrass.bytesAt_add, h1, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rfl

theorem exchange_none {C : Curve} {d : Nat} (bs : List Byte) (h : ¬ (1 ≤ d ∧ d < C.n)) :
    Spec.Ecdh.exchange C d bs = none := by
  unfold Spec.Ecdh.exchange; simp only [h, ↓reduceIte]

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

/-! ## Numbers of whole words, and of a top word of fewer bytes -/

/-- `loadLen`, as a kit's `load_ok`. -/
theorem loadLen_kit {c : Cfg} (n9 : c.n ≤ 9) {L : Nat} (hL : (L + 7) / 8 = c.n) {s : State} {base : Addr}
    {i : Nat} {p : Reg} {off R : Nat} (hw : WsReg s base) (hi : i < 45) (hp : p ∉ [Reg.t0, .t1])
    (hoff : off + L ≤ R) (hR : R ≤ 2048) (hrd : (⟨s.gpr p, R⟩ : Region) ∈ s.rd ++ s.wr)
    (hsep : ∀ j < L, ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr p + BitVec.ofNat 64 (off + j)) 1) :
    WP isa (.block (loadLen L (c.sl i) p off)) s fun s' =>
      Rest [.t0, .t1] s s' ∧ Outside base (c.sl i) (8 * c.n) s.mem s'.mem ∧
      wordsVal s'.mem base (c.sl i) c.n = ofBytes (bytesAt s.mem (s.gpr p + BitVec.ofNat 64 off) L) := by
  have h := loadLen_ok L hw hp (sl8 c i) (by rw [hL]; exact sl_top n9 (by omega_using [hi])) hoff hR hrd hsep
  rwa [hL] at h

/-- `loadNum`, as a kit's `load_ok`. -/
theorem loadNum_kit {c : Cfg} (n9 : c.n ≤ 9) {s : State} {base : Addr}
    {i : Nat} {p : Reg} {off R : Nat} (hw : WsReg s base) (hi : i < 45) (hp : p ∉ [Reg.t0, .t1])
    (hoff : off + 8 * c.n ≤ R) (hR : R ≤ 2048) (hrd : (⟨s.gpr p, R⟩ : Region) ∈ s.rd ++ s.wr)
    (hsep : ∀ j < 8 * c.n, ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr p + BitVec.ofNat 64 (off + j)) 1) :
    WP isa (.block (loadNum c.n (c.sl i) p off)) s fun s' =>
      Rest [.t0, .t1] s s' ∧ Outside base (c.sl i) (8 * c.n) s.mem s'.mem ∧
      wordsVal s'.mem base (c.sl i) c.n = ofBytes (bytesAt s.mem (s.gpr p + BitVec.ofNat 64 off) (8 * c.n)) := by
  rw [← loadLen_mul]
  exact loadLen_kit n9 (by omega_using []) hw hi hp hoff hR hrd hsep

/-- `storeLen`, as a kit's `store_ok`. -/
theorem storeLen_kit {c : Cfg} (n9 : c.n ≤ 9) {L : Nat} (hL : (L + 7) / 8 = c.n) (b : Bool) {s : State}
    {base : Addr} {i : Nat} {q : Reg} {off : Nat} (hw : WsReg s base) (hc : s.gpr .a7 = maskOf b) (hi : i < 45)
    (hq : q ∉ [Reg.t0, .t1]) (hoff : off + L ≤ 2048)
    (hout : ∀ j < L, InRegions s.wr (s.gpr q + BitVec.ofNat 64 (off + j)) 1)
    (hsep : ∀ j < L, ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr q + BitVec.ofNat 64 (off + j)) 1) :
    WP isa (.block (storeLen L (c.sl i) q off)) s fun s' =>
      Rest [.t0, .t1] s s' ∧ s'.mem = writeBytes s.mem (s.gpr q + BitVec.ofNat 64 off)
        (toBytes L (if b then wordsVal s.mem base (c.sl i) c.n else 0)) := by
  have h := storeLen_ok b L hw hc hq (sl8 c i) (by rw [hL]; exact sl_top n9 (by omega_using [hi])) hoff hout hsep
  rwa [hL] at h

/-- `storeNum`, as a kit's `store_ok`. -/
theorem storeNum_kit {c : Cfg} (n9 : c.n ≤ 9) (b : Bool) {s : State}
    {base : Addr} {i : Nat} {q : Reg} {off : Nat} (hw : WsReg s base) (hc : s.gpr .a7 = maskOf b) (hi : i < 45)
    (hq : q ∉ [Reg.t0, .t1]) (hoff : off + 8 * c.n ≤ 2048)
    (hout : ∀ j < 8 * c.n, InRegions s.wr (s.gpr q + BitVec.ofNat 64 (off + j)) 1)
    (hsep : ∀ j < 8 * c.n, ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr q + BitVec.ofNat 64 (off + j)) 1) :
    WP isa (.block (storeNum c.n (c.sl i) q off)) s fun s' =>
      Rest [.t0, .t1] s s' ∧ s'.mem = writeBytes s.mem (s.gpr q + BitVec.ofNat 64 off)
        (toBytes (8 * c.n) (if b then wordsVal s.mem base (c.sl i) c.n else 0)) := by
  rw [← storeLen_mul]
  exact storeLen_kit n9 (by omega_using []) b hw hc hi hq hoff hout hsep

end Kit

/-! ## The kit -/

/-- What the proof needs of a curve. -/
structure Kit where
  c : Cfg
  /-- The bytes of a number. -/
  L : Nat
  len : c.C.len = L
  n9 : c.n ≤ 9
  Ln : L ≤ 8 * c.n
  unit : UnitMod c.C.p (2 ^ (64 * c.n))
  onG : Spec.Weierstrass.onCurve c.C (Spec.Weierstrass.G c.C) = true
  /-- A number read from `L` bytes to a slot, and written from one. -/
  load : Nat → Reg → Nat → List Instr
  store : Nat → Reg → Nat → List Instr
  load_ok : ∀ {s : State} {base : Addr} {i : Nat} {p : Reg} {off R : Nat}, WsReg s base → i < 45 →
    p ∉ [Reg.t0, .t1] → off + L ≤ R → R ≤ 2048 → (⟨s.gpr p, R⟩ : Region) ∈ s.rd ++ s.wr →
    (∀ j < L, ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr p + BitVec.ofNat 64 (off + j)) 1) →
    WP isa (.block (load (c.sl i) p off)) s fun s' =>
      Rest [.t0, .t1] s s' ∧ Outside base (c.sl i) (8 * c.n) s.mem s'.mem ∧
      wordsVal s'.mem base (c.sl i) c.n = ofBytes (bytesAt s.mem (s.gpr p + BitVec.ofNat 64 off) L)
  store_ok : ∀ (b : Bool) {s : State} {base : Addr} {i : Nat} {q : Reg} {off : Nat}, WsReg s base →
    s.gpr .a7 = maskOf b → i < 45 → q ∉ [Reg.t0, .t1] → off + L ≤ 2048 →
    (∀ j < L, InRegions s.wr (s.gpr q + BitVec.ofNat 64 (off + j)) 1) →
    (∀ j < L, ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr q + BitVec.ofNat 64 (off + j)) 1) →
    WP isa (.block (store (c.sl i) q off)) s fun s' =>
      Rest [.t0, .t1] s s' ∧ s'.mem = writeBytes s.mem (s.gpr q + BitVec.ofNat 64 off)
        (toBytes L (if b then wordsVal s.mem base (c.sl i) c.n else 0))
  /-- The check of the peer's point. -/
  CC : Impl.Weierstrass.CheckPoint.Curve
  CCW : CC.W = c.C
  CCk : CC.k = c.n
  checkN : String
  checkC : Prog isa
  checkNF : checkC.noFrames = true
  check_rv : Meets checkC (Kit.checkRVc CC)
  num_eq : ∀ (m : Mem) (ws : Addr) (i : Nat), i < 100 → CC.num ws m (CC.slot i) = wordsVal m ws (c.sl i) c.n
  flag_eq : ∀ (m : Mem) (ws : Addr), CC.flag ws m = word m ws (c.sl FLAG)
  /-- What the check may write. -/
  checkKW : List (Nat × Nat)
  check_unch : ∀ {base : Addr} {m m' : Mem}, CC.Keeps base m m' → Unch base checkKW m m'
  check_lo : ∀ w ∈ checkKW, 40 ≤ w.1
  check_keep : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP, K], ∀ w ∈ checkKW,
    c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i
  /-- What follows the point's setup. -/
  mulN : String
  mulC : Prog isa
  tailW : List (Nat × Nat)
  tail_lo : ∀ w ∈ tailW, 40 ≤ w.1
  tail_ok : Law c.C → ∀ {s : State} {base : Addr}, WsReg s base → s.gpr .s3 = base →
    Kit.sv c base s MP = c.C.p → Kit.sv c base s MN = c.C.n → Kit.sv c base s ZERO = 0 → Kit.sv c base s ONE = 1 →
    Kit.sv c base s ONEP = 1 * 2 ^ (64 * c.n) % c.C.p → Kit.sv c base s AP = c.C.a * 2 ^ (64 * c.n) % c.C.p →
    Kit.sv c base s B3P = 3 * c.C.b * 2 ^ (64 * c.n) % c.C.p → Kit.sv c base s EXPP = c.C.p - 2 →
    Kit.sv c base s RX < c.C.p → Kit.sv c base s RY < c.C.p →
    Spec.Weierstrass.onCurve c.C (.affine (toM c.C.p (2 ^ (64 * c.n)) (Kit.sv c base s RX))
      (toM c.C.p (2 ^ (64 * c.n)) (Kit.sv c base s RY))) = true →
    WP isa (tail c mulN mulC) s fun s' =>
      Kc s s' ∧ Unch base tailW s.mem s'.mem ∧
      word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) &&& maskOf (decide (Kit.sv c base s K < c.C.n)) &&&
        maskOf (!decide (Kit.sv c base s K = 0)) ∧
      (1 ≤ Kit.sv c base s K → Kit.sv c base s K < c.C.n →
        Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (Kit.sv c base s' RX)) (toM c.C.p (2 ^ (64 * c.n)) (Kit.sv c base s' RY))
          (toM c.C.p (2 ^ (64 * c.n)) (Kit.sv c base s' RZ))
          (Spec.Weierstrass.mul (Kit.sv c base s K) (.affine (toM c.C.p (2 ^ (64 * c.n)) (Kit.sv c base s RX))
            (toM c.C.p (2 ^ (64 * c.n)) (Kit.sv c base s RY)))) ∧
        Kit.sv c base s' RX < c.C.p ∧ Kit.sv c base s' RY < c.C.p ∧ Kit.sv c base s' RZ < c.C.p) ∧
      Kit.sv c base s' XO < c.C.p ∧
      Fin.ofNat c.C.p (Kit.sv c base s' XO) =
        toM c.C.p (2 ^ (64 * c.n)) (Kit.sv c base s' RX) * toM c.C.p (2 ^ (64 * c.n)) (Kit.sv c base s' RZ) ^ (c.C.p - 2) ∧
      Kit.sv c base s' ACC < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (Kit.sv c base s' ACC) = toM c.C.p (2 ^ (64 * c.n)) (Kit.sv c base s' RZ) ^ (c.C.p - 2)
  /-- The flag `&=` the mask `a7`. -/
  andFlag_ok : ∀ {s : State} {base : Addr}, WsReg s base →
    WP isa (.block (Cfg.andFlag c)) s fun s' =>
      word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) &&& s.gpr .a7 ∧ Rest [.t0] s s' ∧
        Outside base (c.sl FLAG) 8 s.mem s'.mem
  /-- The saves, `s0 = s3 = r` and `s2 = a0`. -/
  save_ok : ∀ {s : State} {r : Reg} {base : Addr}, s.gpr r = base → (⟨base, 8192⟩ : Region) ∈ s.wr →
    base.toNat + 8192 ≤ 2 ^ 64 → base.toNat % 8 = 0 →
    WP isa (.block (saveCode r)) s fun s' => WsReg s' base ∧ s'.gpr .s3 = base ∧ s'.gpr .s2 = s.gpr .a0 ∧
      (∀ x, x ≠ .s0 → x ≠ .s2 → x ≠ .s3 → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ Unch base [(0, 40)] s.mem s'.mem ∧
      word s'.mem base 0 = s.gpr .s0 ∧ word s'.mem base 8 = s.gpr .s1 ∧ word s'.mem base 16 = s.gpr .s2 ∧
      word s'.mem base 24 = s.gpr .ra ∧ word s'.mem base 32 = s.gpr .s3
  /-- The constants: slots below `cs`, each its own. -/
  cs : Nat
  consts_ok : ∀ (l : List (Nat × Nat)) {s : State} {base : Addr}, WsReg s base → (∀ e ∈ l, e.1 < cs) →
    (l.map Prod.fst).Nodup →
    WP isa (.block (l.flatMap fun e => setConst c.n (c.sl e.1) e.2)) s fun s' =>
      Rest [.t0, .t1] s s' ∧ Unch base (l.map fun e => (c.sl e.1, 8 * c.n)) s.mem s'.mem ∧
      ∀ e ∈ l, Kit.sv c base s' e.1 = e.2 % 2 ^ (64 * c.n)
  consts_slots : ∀ e ∈ consts c, e.1 < cs
  consts_lt : ∀ e ∈ consts c, e.2 < 2 ^ (64 * c.n)

namespace Kit

variable (E : Kit)

/-- Slot arithmetic: the offsets of slots given by number, with the kit's bound on the words. -/
local macro "kit_slots" E:term : tactic => `(tactic| (
  simp only [Cfg.sl, slot, MP, MN, ZERO, ONE, ONEP, AP, B3P, GX, GY, EXPP, R2P, BP, K, CX, CY, CPX, CPY, FLAG, RX,
    RY, RZ, XO]
  omega_using [Kit.n9 $E]))

/-- `∀ w ∈ W, P w` for ranges `W` given as a list of lists: `t` proves it of each. -/
local macro "kit_ranges" t:tacticSeq : tactic =>
  `(tactic| ((repeat' first | apply all_app | apply all_one); all_goals ($t)))

/-- A slot apart from ranges that are other slots, the flag or the constants. -/
local macro "kit_apart" : tactic =>
  `(tactic| kit_ranges (first
    | exact sl_sep _ (by decide)
    | exact Or.inl (sl_le _ (by decide))
    | exact apart_consts _ (by decide)))

/-- The value of a constant's slot. -/
theorem const_at {base : Addr} {s : State} (hc : ∀ e ∈ consts E.c, sv E.c base s e.1 = e.2) (k : Nat)
    (hk : k < 12 := by decide) :
    sv E.c base s ((consts E.c)[k]'(by rw [consts_len]; exact hk)).1 =
      ((consts E.c)[k]'(by rw [consts_len]; exact hk)).2 :=
  hc _ (List.getElem_mem _)

theorem CCR : E.CC.R = 2 ^ (64 * E.c.n) := by rw [Impl.Weierstrass.CheckPoint.Curve.R, E.CCk]

/-- The shared secret of the private key at `d` and the public key at
`peer`, as the specification computes it. -/
abbrev ex (m : Mem) (d peer : Addr) : Option (List Byte) :=
  Spec.Ecdh.exchange E.c.C (ofBytes (bytesAt m d E.L)) (bytesAt m peer (1 + 2 * E.L))

/-- What the peer's point's setup writes. -/
abbrev peerW : List (Nat × Nat) :=
  [(E.c.sl CX, 8 * E.c.n)] ++ [(E.c.sl CY, 8 * E.c.n)] ++ [(E.c.sl FLAG, 8)] ++
    (consts E.c).map fun e => (E.c.sl e.1, 8 * E.c.n)

/-- The peer's point read from `[q]` (`x` and `y` to the check's slots), the
flag set to the mask of its first byte being `04`, and the constants. -/
theorem peerLoad_ok {s : State} {base : Addr} {q : Reg} (hw : WsReg s base) (hq : q ∉ [Reg.t0, .t1, .a7])
    (hrd : (⟨s.gpr q, 1 + 2 * E.L⟩ : Region) ∈ s.rd ++ s.wr)
    (hdis : (⟨s.gpr q, 1 + 2 * E.L⟩ : Region).Disjoint ⟨base, 8192⟩)
    (hfit : (s.gpr q).toNat + (1 + 2 * E.L) ≤ 2 ^ 64) :
    WP isa (.block (E.load (E.c.sl CX) q 1 ++ E.load (E.c.sl CY) q (1 + E.L) ++
      leadMask q ++ sdAt .a7 wb (E.c.sl FLAG) ++ constCode E.c)) s fun s' =>
      WsReg s' base ∧ Rest [.t0, .t1, .a7] s s' ∧ Unch base E.peerW s.mem s'.mem ∧
      sv E.c base s' CX = ofBytes (bytesAt s.mem (s.gpr q + BitVec.ofNat 64 1) E.L) ∧
      sv E.c base s' CY = ofBytes (bytesAt s.mem (s.gpr q + BitVec.ofNat 64 (1 + E.L)) E.L) ∧
      word s'.mem base (E.c.sl FLAG) = maskOf (decide (s.mem (s.gpr q) = 4)) ∧
      ∀ e ∈ consts E.c, sv E.c base s' e.1 = e.2 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  obtain hq2 : q ∉ [Reg.t0, .t1] := by simp [hq.1, hq.2.1]
  obtain hL := E.Ln
  obtain h9 := E.n9
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (E.load_ok (i := CX) (p := q) (off := 1) (R := 1 + 2 * E.L) hw (by decide) hq2
    (by omega_using []) (by omega_using [hL, h9]) hrd
    (fun j hj => out_of_disj hdis hfit (by omega_using [hj])))
    fun s₃ ⟨r₃, O₃, e₃⟩ => ?_)
  obtain hw₃ := hw.of_rest r₃
  obtain q₃ : s₃.gpr q = s.gpr q := r₃.gpr _ hq2
  refine WP.block_append (WP.mono (E.load_ok (i := CY) (p := q) (off := 1 + E.L) (R := 1 + 2 * E.L) hw₃ (by decide)
    hq2 (by omega_using []) (by omega_using [hL, h9]) (by rw [q₃, r₃.rd, r₃.wr]; exact hrd)
    (fun j hj => by rw [q₃]; exact out_of_disj hdis hfit (by omega_using [hj])))
    fun s₄ ⟨r₄, O₄, e₄⟩ => ?_)
  obtain hw₄ := hw₃.of_rest r₄
  obtain r₃₄ := r₃.trans r₄
  obtain q₄ : s₄.gpr q = s.gpr q := r₃₄.gpr _ hq2
  -- The first byte, and the flag.
  refine WP.block_append (WP.mono (leadMask_ok (s := s₄) (q := q) (by
      rw [r₃₄.rd, r₃₄.wr, q₄]
      have := Offset.contains_base (s.gpr q) (d := 0) (n := 1) (k := 1 + 2 * E.L) (by omega_using []) (by decide)
      exact ⟨_, hrd, by simpa using this⟩))
    fun s₅ ⟨r₅, m₅, g₅⟩ => ?_)
  obtain hw₅ := hw₄.of_rest r₅
  refine sdAt_ws hw₅ (by decide) (d := E.c.sl FLAG) (by kit_slots E) (sl8 _ _) fun s₆ u₆ => ?_
  obtain hw₆ := hw₅.of_kp (Kp.of_mupd u₆)
  -- The constants.
  rw [constCode_eq]
  refine WP.mono (E.consts_ok _ hw₆ E.consts_slots (consts_nodup E.c)) fun s₇ ⟨r₇, U₇, e₇⟩ => ?_
  obtain O₆ : Outside base (E.c.sl FLAG) 8 s₅.mem s₆.mem := by
    rw [u₆.mem]; exact writeW_outside _ _ _ (by kit_slots E)
  obtain m₄₆ : Unch base [(E.c.sl FLAG, 8)] s₄.mem s₆.mem := by rw [← m₅]; exact O₆.unch
  obtain U₄₇ := m₄₆.trans U₇
  obtain U₃₇ := O₄.unch.trans U₄₇
  obtain r₇' : Rest [.t0, .t1, .a7] s s₇ :=
    ((r₃₄.mono (by decide)).trans r₅).trans ((u₆.rest _).trans (r₇.mono (by decide)))
  refine ⟨hw₆.of_rest r₇, r₇', ((O₃.unch.trans O₄.unch).trans m₄₆).trans U₇, ?_, ?_, ?_, ?_⟩
  · show wordsVal _ _ _ _ = _
    rw [U₃₇.wordsVal (by kit_apart) (by kit_slots E), e₃]
  · show wordsVal _ _ _ _ = _
    rw [U₄₇.wordsVal (by kit_apart) (by kit_slots E), e₄, q₃,
      bytesAt_unch O₃.unch (all_one (by kit_slots E)) (sep_at' hdis hfit (off := 1 + E.L) (k := E.L) (by omega_using []))]
  · rw [U₇.word (flag_consts _) (by kit_slots E), u₆.mem, word_writeW_self, g₅, q₄]
    obtain h1 := bytesAt_unch (O₃.unch.trans O₄.unch) (q := s.gpr q) (n := 1) (by kit_ranges kit_slots E)
      (by simpa using sep_at' hdis hfit (off := 0) (k := 1) (by omega_using []))
    simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h1
    simp only [BitVec.add_zero] at h1
    rw [h1]
  · intro e he
    rw [e₇ e he, Nat.mod_eq_of_lt (E.consts_lt e he)]

/-- What the contract gives, by register. -/
structure EPre (E : Kit) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a1, E.L⟩, ⟨s.gpr .a2, 1 + 2 * E.L⟩]
  wr : s.wr = [⟨s.gpr .a0, E.L⟩, ⟨s.gpr .a3, 8192⟩]
  out : (⟨s.gpr .a0, E.L⟩ : Region).Disjoint ⟨s.gpr .a3, 8192⟩
  d : (⟨s.gpr .a1, E.L⟩ : Region).Disjoint ⟨s.gpr .a3, 8192⟩
  peer : (⟨s.gpr .a2, 1 + 2 * E.L⟩ : Region).Disjoint ⟨s.gpr .a3, 8192⟩
  fo : (s.gpr .a0).toNat + E.L ≤ 2 ^ 64
  fd : (s.gpr .a1).toNat + E.L ≤ 2 ^ 64
  fp : (s.gpr .a2).toNat + (1 + 2 * E.L) ≤ 2 ^ 64
  fs : (s.gpr .a3).toNat + 8192 ≤ 2 ^ 64
  al : (s.gpr .a3).toNat % 8 = 0

/-- What the setup leaves. -/
structure SetupPost (E : Kit) (s s' : State) : Prop where
  ws : WsReg s' (s.gpr .a3)
  s2 : s'.gpr .s2 = s.gpr .a0
  s3 : s'.gpr .s3 = s.gpr .a3
  regs : ∀ x, x ≠ .s0 → x ≠ .s2 → x ≠ .s3 → x ∈ preserved → s'.gpr x = s.gpr x
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  sv0 : word s'.mem (s.gpr .a3) 0 = s.gpr .s0
  sv1 : word s'.mem (s.gpr .a3) 8 = s.gpr .s1
  sv2 : word s'.mem (s.gpr .a3) 16 = s.gpr .s2
  sv3 : word s'.mem (s.gpr .a3) 24 = s.gpr .ra
  sv4 : word s'.mem (s.gpr .a3) 32 = s.gpr .s3
  k : sv E.c (s.gpr .a3) s' K = ofBytes (bytesAt s.mem (s.gpr .a1) E.L)
  x : sv E.c (s.gpr .a3) s' CX = ofBytes (bytesAt s.mem (s.gpr .a2 + BitVec.ofNat 64 1) E.L)
  y : sv E.c (s.gpr .a3) s' CY = ofBytes (bytesAt s.mem (s.gpr .a2 + BitVec.ofNat 64 (1 + E.L)) E.L)
  flag : word s'.mem (s.gpr .a3) (E.c.sl FLAG) = maskOf (decide (s.mem (s.gpr .a2) = 4))
  consts : ∀ e ∈ consts E.c, sv E.c (s.gpr .a3) s' e.1 = e.2

theorem setup_ok {s : State} (hs : E.EPre s) :
    WP isa (.block (saveCode .a3 ++ E.load (E.c.sl K) .a1 0 ++ E.load (E.c.sl CX) .a2 1 ++
      E.load (E.c.sl CY) .a2 (1 + E.L) ++ leadMask .a2 ++ sdAt .a7 wb (E.c.sl FLAG) ++
      constCode E.c)) s fun s' => E.SetupPost s s' := by
  obtain hL := E.Ln
  obtain h9 := E.n9
  generalize hb : s.gpr .a3 = base
  obtain hwr : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hs.wr, ← hb]; simp
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (E.save_ok hb hwr (by rw [← hb]; exact hs.fs) (by rw [← hb]; exact hs.al))
    fun s₁ ⟨hw₁, h3₁, o₁, g₁, rd₁, wr₁, sp₁, U₁, w0, w1, w2, w3, w4⟩ => ?_)
  obtain a1 : s₁.gpr .a1 = s.gpr .a1 := g₁ _ (by decide) (by decide) (by decide)
  obtain a2 : s₁.gpr .a2 = s.gpr .a2 := g₁ _ (by decide) (by decide) (by decide)
  obtain rd1 : (⟨s.gpr .a1, E.L⟩ : Region) ∈ s₁.rd ++ s₁.wr := by rw [rd₁, hs.rd]; simp
  obtain rd2 : (⟨s.gpr .a2, 1 + 2 * E.L⟩ : Region) ∈ s₁.rd ++ s₁.wr := by rw [rd₁, hs.rd]; simp
  -- `d`.
  refine WP.block_append (WP.mono (E.load_ok (i := K) (p := .a1) (off := 0) (R := E.L) hw₁ (by decide) (by decide)
    (by omega_using []) (by omega_using [hL, h9]) (by rw [a1]; exact rd1)
    (fun i hi => by rw [a1]; exact out_of_disj (hb ▸ hs.d) hs.fd (by omega_using [hi])))
    fun s₂ ⟨r₂, O₂, e₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  obtain a2' : s₂.gpr .a2 = s.gpr .a2 := by rw [r₂.gpr _ (by decide), a2]
  -- The peer's point, the flag and the constants.
  simp only [← List.append_assoc]
  refine WP.mono (E.peerLoad_ok hw₂ (q := .a2) (by decide) (by rw [r₂.rd, r₂.wr, a2']; exact rd2)
    (by rw [a2']; exact hb ▸ hs.peer) (by rw [a2']; exact hs.fp)) fun s₇ ⟨hw₇, r₇, U₂₇, x₇, y₇, f₇, c₇⟩ => ?_
  obtain U₁₇ := O₂.unch.trans U₂₇
  obtain m₂₁ : Unch base _ s.mem s₂.mem := U₁.trans O₂.unch
  obtain hpres : ∀ x ∈ preserved, x ∉ [Reg.t0, .t1, .a7] := by decide
  obtain hpres2 : ∀ x ∈ preserved, x ∉ [Reg.t0, .t1] := by decide
  obtain gp : ∀ x ∈ preserved, s₇.gpr x = s₁.gpr x := fun x hx => by
    rw [r₇.gpr _ (hpres x hx), r₂.gpr _ (hpres2 x hx)]
  obtain a1' : s₁.gpr .a1 + BitVec.ofNat 64 0 = s.gpr .a1 := by rw [a1]; simp
  obtain lo : ∀ w ∈ [(E.c.sl K, 8 * E.c.n)] ++ E.peerW, 40 ≤ w.1 := by
    kit_ranges (first | exact lo_consts _ | exact Nat.le_trans (by decide) (sl_lo _ _))
  obtain in₂₁ : ∀ w ∈ [(0, 40)] ++ [(E.c.sl K, 8 * E.c.n)], w.1 + w.2 ≤ 8192 := by
    kit_ranges (first | decide | kit_slots E)
  subst hb
  refine ⟨hw₇, ?_, ?_, fun x h0 h2 h3 hx => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gp _ (by decide), o₁]
  · rw [gp _ (by decide), h3₁]
  · rw [gp _ hx, g₁ _ h0 h2 h3]
  · rw [r₇.rd, r₂.rd, rd₁]
  · rw [r₇.wr, r₂.wr, wr₁]
  · rw [r₇.sp, r₂.sp, sp₁]
  · rw [lo_word U₁₇ lo (by decide)]; exact w0
  · rw [lo_word U₁₇ lo (by decide)]; exact w1
  · rw [lo_word U₁₇ lo (by decide)]; exact w2
  · rw [lo_word U₁₇ lo (by decide)]; exact w3
  · rw [lo_word U₁₇ lo (by decide)]; exact w4
  · show wordsVal _ _ _ _ = _
    rw [U₂₇.wordsVal (by kit_apart) (by kit_slots E), e₂, a1',
      bytesAt_unch U₁ (by decide) (by simpa using sep_at' hs.d hs.fd (off := 0) (k := E.L) (by omega_using []))]
  · rw [x₇, a2', bytesAt_unch m₂₁ in₂₁ (sep_at' hs.peer hs.fp (off := 1) (k := E.L) (by omega_using []))]
  · rw [y₇, a2', bytesAt_unch m₂₁ in₂₁ (sep_at' hs.peer hs.fp (off := 1 + E.L) (k := E.L) (by omega_using []))]
  · rw [f₇, a2']
    obtain h1 := bytesAt_unch m₂₁ (q := s.gpr .a2) (n := 1) in₂₁
      (by simpa using sep_at' hs.peer hs.fp (off := 0) (k := 1) (by omega_using []))
    simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h1
    simp only [BitVec.add_zero] at h1
    rw [h1]
  · exact c₇

/-- The check of the peer's point, by its call. -/
theorem check_ok {s : State} {base : Addr} (hw : WsReg s base) (h3 : s.gpr .s3 = base)
    (hc : ∀ e ∈ consts E.c, sv E.c base s e.1 = e.2)
    (hf : word s.mem base (E.c.sl FLAG) = 0 ∨ word s.mem base (E.c.sl FLAG) = BitVec.allOnes 64) :
    WP isa (wsCall E.checkN E.checkC) s fun s' =>
      Kp s s' ∧ Unch base E.checkKW s.mem s'.mem ∧
      word s'.mem base (E.c.sl FLAG) = word s.mem base (E.c.sl FLAG) &&&
        Impl.Weierstrass.CheckPoint.Curve.mask (E.CC.Valid (sv E.c base s CX) (sv E.c base s CY)) ∧
      sv E.c base s' CPX = (if word s'.mem base (E.c.sl FLAG) = 0 then sv E.c base s GX
        else sv E.c base s CX * 2 ^ (64 * E.c.n) % E.c.C.p) ∧
      sv E.c base s' CPY = (if word s'.mem base (E.c.sl FLAG) = 0 then sv E.c base s GY
        else sv E.c base s CY * 2 ^ (64 * E.c.n) % E.c.C.p) := by
  refine wsCallR_ok E.checkNF E.check_rv hw h3 (fun t r w a m => ?_) fun s₀ s' K' mm t a m hp => ?_
  · refine ⟨r, by rw [w, a], by rw [a]; exact hw.nowrap, by rw [a]; exact hw.al, ?_⟩
    rw [a, m]
    unfold Impl.Weierstrass.CheckPoint.Curve.pre
    rw [E.CCR, E.CCW]
    refine ⟨(E.num_eq _ _ MP (by decide)).trans (E.const_at hc 0),
      (E.num_eq _ _ R2P (by decide)).trans (E.const_at hc 10),
      (E.num_eq _ _ AP (by decide)).trans (E.const_at hc 5),
      (E.num_eq _ _ BP (by decide)).trans (E.const_at hc 11), ?_⟩
    rw [E.flag_eq]; exact hf
  · have hp' : E.CC.post base s.mem s'.mem := by
      have := hp
      simp only [checkRVc, State.withRegions_mem] at this
      rw [a, m, ← mm] at this
      exact this
    obtain ⟨hF, -, -, hx, hy, hK⟩ := hp'
    obtain ex : E.CC.num base s.mem E.CC.xAt = sv E.c base s CX := E.num_eq _ _ CX (by decide)
    obtain ey : E.CC.num base s.mem E.CC.yAt = sv E.c base s CY := E.num_eq _ _ CY (by decide)
    obtain egx : E.CC.num base s.mem E.CC.gxAt = sv E.c base s GX := E.num_eq _ _ GX (by decide)
    obtain egy : E.CC.num base s.mem E.CC.gyAt = sv E.c base s GY := E.num_eq _ _ GY (by decide)
    obtain epx : E.CC.num base s'.mem E.CC.pxAt = sv E.c base s' CPX := E.num_eq _ _ CPX (by decide)
    obtain epy : E.CC.num base s'.mem E.CC.pyAt = sv E.c base s' CPY := E.num_eq _ _ CPY (by decide)
    rw [E.flag_eq, E.flag_eq, ex, ey] at hF
    rw [ex, ey, egx, E.flag_eq, epx, ← hF, E.CCR, E.CCW] at hx
    rw [ex, ey, egy, E.flag_eq, epy, ← hF, E.CCR, E.CCW] at hy
    exact ⟨K', E.check_unch hK, hF, hx, hy⟩

/-- The end: the flag `&=` the mask of `Z ≠ 0`, `x` (or zeros) to `out`, the
flag's low bit to `a0`, and the saved registers restored. -/
theorem fin_ok {s : State} {base out : Addr} (hw : WsReg s base) (h2 : s.gpr .s2 = out)
    (hout : ∀ i < E.L, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < E.L, ¬ (⟨base, 8192⟩ : Region).Contains (out + BitVec.ofNat 64 i) 1)
    {b : Bool} (hF : word s.mem base (E.c.sl FLAG) = maskOf b) :
    WP isa (.block (zCode E.c ++ E.store (E.c.sl XO) .s2 0 ++ retCode E.c)) s fun s' =>
      s'.gpr .a0 = (if b && !decide (sv E.c base s RZ = 0) then 1 else 0) ∧
      bytesAt s'.mem out E.L = toBytes E.L (if b && !decide (sv E.c base s RZ = 0) then sv E.c base s XO else 0) ∧
      s'.gpr .s0 = word s.mem base 0 ∧ s'.gpr .s1 = word s.mem base 8 ∧ s'.gpr .s2 = word s.mem base 16 ∧
      s'.gpr .ra = word s.mem base 24 ∧ s'.gpr .s3 = word s.mem base 32 ∧
      (∀ r ∈ preserved, r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp := by
  obtain hL := E.Ln
  obtain h9 := E.n9
  obtain hfl := sl_lo E.c FLAG
  rw [zCode, retCode, restoreCode]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (zeroMask_ok hw (n := E.c.n) (a := E.c.sl RZ) (sl8 _ _) (sl_top h9 (by decide)))
    fun s₁ ⟨r₁, m₁, g₁⟩ => ?_)
  rw [List.singleton_append]
  refine WP.cons (exec_logicImm (by decide)) ?_
  obtain r₁' := r₁.trans ((Upd.write s₁ .a7 (s₁.gpr .a7 ^^^ BitVec.ofInt 64 (-1))).rest (ws := [.t3, .t4, .a7])
    (by decide))
  obtain hw₁ := hw.of_rest r₁'
  refine WP.block_append (WP.mono (E.andFlag_ok hw₁) fun s₂ ⟨f₂, r₂, O₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  refine ldAt_ws hw₂ (d := E.c.sl FLAG) (by kit_slots E) (sl8 _ _) fun s₃ u₃ => ?_
  obtain hw₃ := hw₂.of_kp (Kp.of_upd u₃)
  -- The flag.
  obtain hb : word s₂.mem base (E.c.sl FLAG) = maskOf (b && !decide (sv E.c base s RZ = 0)) := by
    rw [f₂]
    simp only [State.write, ↓reduceIte]
    rw [m₁, hF, g₁, not_mask, maskOf_and]
  obtain a₃ : s₃.gpr .a7 = maskOf (b && !decide (sv E.c base s RZ = 0)) := by rw [u₃.gpr]; exact hb
  obtain xo : wordsVal s₃.mem base (E.c.sl XO) E.c.n = sv E.c base s XO := by
    rw [u₃.mem, O₂.wordsVal (.inl (sl_le _ (by decide))) (by kit_slots E)]
    show wordsVal (s₁.write _ _).mem _ _ _ = _
    simp only [State.write]; rw [m₁]
  obtain q₃ : s₃.gpr .s2 = out := by
    rw [u₃.other _ (by decide), r₂.gpr _ (by decide), r₁'.gpr _ (by decide), h2]
  refine WP.block_append (WP.mono (E.store_ok _ (i := XO) (q := .s2) (off := 0) hw₃ a₃ (by decide) (by decide)
    (by omega_using [hL, h9])
    (fun i hi => by rw [q₃, Nat.zero_add, u₃.wr, r₂.wr, r₁'.wr]; exact hout i hi)
    (fun i hi => by rw [q₃, Nat.zero_add]; exact hsep i hi)) fun s₄ ⟨r₄, m₄⟩ => ?_)
  obtain hw₄ := hw₃.of_rest r₄
  obtain U₄ : Unch base [(8192, 2 ^ 64)] s₃.mem s₄.mem := by
    rw [m₄]; exact writeBytes_unch _ fun i hi => by
      rw [q₃, BitVec.add_zero]
      exact hsep i (by simpa [VG.Proof.Weierstrass.length_toBytes] using hi)
  obtain wd : ∀ d, d + 8 ≤ 40 → word s₄.mem base d = word s.mem base d := fun d hd => by
    rw [U₄.word (by simp; omega_using [hd]) (by omega_using [hd]), u₃.mem,
      O₂.word (.inl (by omega_using [hd, hfl])) (by omega_using [hd])]
    show word (s₁.write _ _).mem _ _ = _
    simp only [State.write]; rw [m₁]
  -- The return value and the restores.
  refine ldAt_ws hw₄ (d := E.c.sl FLAG) (by kit_slots E) (sl8 _ _) fun s₅ u₅ => ?_
  refine WP.cons (exec_logicImm (by decide)) ?_
  obtain u₅' := Upd.write s₅ .a0 (s₅.gpr .a0 &&& BitVec.ofInt 64 1)
  obtain hw₅ := (hw₄.of_kp (Kp.of_upd u₅)).of_kp (Kp.of_upd u₅')
  refine ld_ws hw₅ (d := 24) (by decide) (by decide) fun s₆ u₆ => ?_
  obtain hw₆ := hw₅.of_kp (Kp.of_upd u₆)
  refine ld_ws hw₆ (d := 16) (by decide) (by decide) fun s₇ u₇ => ?_
  obtain hw₇ : WsReg s₇ base := ⟨by rw [u₇.other _ (by decide)]; exact hw₆.s0, by rw [u₇.wr]; exact hw₆.wr,
    hw₆.nowrap, hw₆.al⟩
  refine ld_ws hw₇ (d := 8) (by decide) (by decide) fun s₈ u₈ => ?_
  obtain hw₈ : WsReg s₈ base := ⟨by rw [u₈.other _ (by decide)]; exact hw₇.s0, by rw [u₈.wr]; exact hw₇.wr,
    hw₇.nowrap, hw₇.al⟩
  refine ld_ws hw₈ (d := 32) (by decide) (by decide) fun s₈' u₈' => ?_
  obtain hw₈' : WsReg s₈' base := ⟨by rw [u₈'.other _ (by decide)]; exact hw₈.s0, by rw [u₈'.wr]; exact hw₈.wr,
    hw₈.nowrap, hw₈.al⟩
  refine ld_ws hw₈' (d := 0) (by decide) (by decide) fun s₉ u₉ => WP.block_nil ?_
  obtain m₉ : s₉.mem = s₄.mem := by rw [u₉.mem, u₈'.mem, u₈.mem, u₇.mem, u₆.mem, u₅'.mem, u₅.mem]
  obtain fl₄ : word s₄.mem base (E.c.sl FLAG) = maskOf (b && !decide (sv E.c base s RZ = 0)) := by
    rw [U₄.word (all_one (.inl (by kit_slots E))) (by kit_slots E), u₃.mem, hb]
  obtain np : ∀ r ∈ preserved, r ∉ [Reg.t0, .t1, .t3, .t4, .a7, .a0, .ra] := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₉.other _ (by decide), u₈'.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅'.gpr, u₅.gpr, fl₄, and_one]
  · have hl : (toBytes E.L (if (b && !decide (sv E.c base s RZ = 0)) = true then sv E.c base s XO else 0)).length =
        E.L := VG.Proof.Weierstrass.length_toBytes _ _
    rw [m₉, m₄, q₃, BitVec.add_zero, xo]
    have := bytesAt_writeBytes s₃.mem out _ (by rw [hl]; omega_using [hL, h9])
    rwa [hl] at this
  · rw [u₉.gpr, u₈'.mem, u₈.mem, u₇.mem, u₆.mem, u₅'.mem, u₅.mem, wd 0 (by decide)]
  · rw [u₉.other _ (by decide), u₈'.other _ (by decide), u₈.gpr, u₇.mem, u₆.mem, u₅'.mem, u₅.mem, wd 8 (by decide)]
  · rw [u₉.other _ (by decide), u₈'.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.mem, u₅'.mem, u₅.mem,
      wd 16 (by decide)]
  · rw [u₉.other _ (by decide), u₈'.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr,
      u₅'.mem, u₅.mem, wd 24 (by decide)]
  · rw [u₉.other _ (by decide), u₈'.gpr, u₈.mem, u₇.mem, u₆.mem, u₅'.mem, u₅.mem, wd 32 (by decide)]
  · intro r hr h0 h1 h2' h3'
    obtain hn := np r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rw [u₉.other _ h0, u₈'.other _ h3', u₈.other _ h1, u₇.other _ h2', u₆.other _ hn.2.2.2.2.2.2,
      u₅'.other _ hn.2.2.2.2.2.1, u₅.other _ hn.2.2.2.2.2.1, r₄.gpr _ (by simp [hn.1, hn.2.1]),
      u₃.other _ hn.2.2.2.2.1, r₂.gpr _ (by simp [hn.1]), r₁'.gpr _ (by simp [hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1])]
  · rw [u₉.sp, u₈'.sp, u₈.sp, u₇.sp, u₆.sp, u₅'.sp, u₅.sp, r₄.sp, u₃.sp, r₂.sp, r₁'.sp]

/-- `vg_ecdh_<curve>`, as the kit reads and writes its numbers. -/
def prog : Prog isa :=
  .seq (.block (saveCode .a3 ++ E.load (E.c.sl K) .a1 0 ++ E.load (E.c.sl CX) .a2 1 ++
    E.load (E.c.sl CY) .a2 (1 + E.L) ++ leadMask .a2 ++ sdAt .a7 wb (E.c.sl FLAG) ++ constCode E.c)) <|
  .seq (wsCall E.checkN E.checkC) <|
  .seq (.block (copy E.c.n (E.c.sl RX) (E.c.sl CPX) ++ copy E.c.n (E.c.sl RY) (E.c.sl CPY))) <|
  .seq (tail E.c E.mulN E.mulC) <|
  .block (zCode E.c ++ E.store (E.c.sl XO) .s2 0 ++ retCode E.c)

/-- What `vg_ecdh_<curve>` returns. -/
def post (s s' : State) : Prop :=
  match E.ex s.mem (s.gpr .a1) (s.gpr .a2) with
  | some z => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) E.L = z
  | none => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) E.L = List.replicate E.L 0

/-- `vg_ecdh_<curve>` by register. -/
theorem ecdh_ok (hL : Law E.c.C) {s : State} (hs : E.EPre s) :
    WP isa E.prog s fun s' => abiPreserved s s' ∧ E.post s s' := by
  obtain hp0 : 0 < E.c.C.p := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain h9 := E.n9
  obtain hLn := E.Ln
  rw [prog]
  refine WP.seq (WP.mono (E.setup_ok hs) fun s₁ S => ?_)
  obtain ⟨hw₁, S2, S3, Sregs, Srd, Swr, Ssp, Ssv0, Ssv1, Ssv2, Ssv3, Ssv4, Sk, Sx, Sy, Sflag, Scs⟩ := S
  generalize hb : s.gpr .a3 = base at hw₁ S3 Ssv0 Ssv1 Ssv2 Ssv3 Ssv4 Sk Sx Sy Sflag Scs
  -- The check.
  obtain hf₁ : word s₁.mem base (E.c.sl FLAG) = 0 ∨ word s₁.mem base (E.c.sl FLAG) = BitVec.allOnes 64 := by
    rw [Sflag]; unfold maskOf; split <;> simp
  refine WP.seq (WP.mono (E.check_ok hw₁ S3 Scs hf₁) fun s₂ ⟨K₂, U₂, f₂, px₂, py₂⟩ => ?_)
  obtain hw₂ := hw₁.of_kp K₂
  -- The point to `R`.
  refine WP.seq (WP.block_append (WP.mono (copy_ok E.c.n hw₂ (o := E.c.sl RX) (a := E.c.sl CPX) (sl8 _ _)
    (sl8 _ _) (sl_top h9 (by decide)) (sl_top h9 (by decide)) (.inl (by kit_slots E))) fun s₃ ⟨v₃, r₃, O₃⟩ =>
    WP.mono (copy_ok E.c.n (hw₂.of_rest r₃) (o := E.c.sl RY) (a := E.c.sl CPY) (sl8 _ _) (sl8 _ _)
    (sl_top h9 (by decide)) (sl_top h9 (by decide)) (.inl (by kit_slots E))) fun s₄ ⟨v₄, r₄, O₄⟩ => ?_))
  obtain hw₄ := (hw₂.of_rest r₃).of_rest r₄
  obtain U₁₄ := (U₂.trans O₃.unch).trans O₄.unch
  obtain keep : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP, K], sv E.c base s₄ i = sv E.c base s₁ i :=
    fun i hi => by
      obtain ⟨hx, hy, h55⟩ := (by decide : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP, K],
        i ≠ RX ∧ i ≠ RY ∧ i ≤ 55) i hi
      exact U₁₄.wordsVal (all_app (all_app (E.check_keep i hi) (all_one (sl_sep _ hx))) (all_one (sl_sep _ hy)))
        (Nat.le_trans (sl_top h9 h55) (by decide))
  obtain gx₁ : sv E.c base s₁ GX = E.c.C.gx * 2 ^ (64 * E.c.n) % E.c.C.p := E.const_at Scs 7
  obtain gy₁ : sv E.c base s₁ GY = E.c.C.gy * 2 ^ (64 * E.c.n) % E.c.C.p := E.const_at Scs 8
  obtain rx₄ : sv E.c base s₄ RX = sv E.c base s₂ CPX := by
    show wordsVal _ _ _ _ = _
    rw [O₄.wordsVal (.inl (sl_le _ (by decide))) (by kit_slots E)]; exact v₃
  obtain ry₄ : sv E.c base s₄ RY = sv E.c base s₂ CPY := by
    show wordsVal _ _ _ _ = _
    rw [v₄, O₃.wordsVal (.inr (sl_le _ (by decide))) (by kit_slots E)]
  generalize hF : word s₂.mem base (E.c.sl FLAG) = F at px₂ py₂ f₂
  generalize hx : sv E.c base s₁ CX = x at Sx px₂ py₂ f₂
  generalize hy : sv E.c base s₁ CY = y at Sy px₂ py₂ f₂
  obtain hval : F ≠ 0 → E.CC.Valid x y := fun h0 => by
    by_contra h
    apply h0
    rw [f₂, mask_eq, decide_eq_false h]
    exact BitVec.and_zero
  obtain lt_rx : sv E.c base s₄ RX < E.c.C.p := by
    rw [rx₄, px₂]; split
    · rw [gx₁]; exact Nat.mod_lt _ hp0
    · exact Nat.mod_lt _ hp0
  obtain lt_ry : sv E.c base s₄ RY < E.c.C.p := by
    rw [ry₄, py₂]; split
    · rw [gy₁]; exact Nat.mod_lt _ hp0
    · exact Nat.mod_lt _ hp0
  obtain hon : Spec.Weierstrass.onCurve E.c.C (.affine (toM E.c.C.p (2 ^ (64 * E.c.n)) (sv E.c base s₄ RX))
      (toM E.c.C.p (2 ^ (64 * E.c.n)) (sv E.c base s₄ RY))) = true := by
    rw [rx₄, ry₄, px₂, py₂]
    by_cases h0 : F = 0
    · rw [ite_eq_left h0, ite_eq_left h0, gx₁, gy₁, toM_mont E.unit, toM_mont E.unit]
      exact E.onG
    · rw [ite_eq_right h0, ite_eq_right h0, toM_mont E.unit, toM_mont E.unit]
      exact valid_on E.CCW (hval h0)
  obtain h3₄ : s₄.gpr .s3 = base := by
    rw [r₄.gpr _ (by decide), r₃.gpr _ (by decide), K₂.gpr _ (by decide), S3]
  refine WP.seq (WP.mono (E.tail_ok hL hw₄ h3₄ ((keep MP (by decide)).trans (E.const_at Scs 0))
    ((keep MN (by decide)).trans (E.const_at Scs 1)) ((keep ZERO (by decide)).trans (E.const_at Scs 2))
    ((keep ONE (by decide)).trans (E.const_at Scs 3)) ((keep ONEP (by decide)).trans (E.const_at Scs 4))
    ((keep AP (by decide)).trans (E.const_at Scs 5)) ((keep B3P (by decide)).trans (E.const_at Scs 6))
    ((keep EXPP (by decide)).trans (E.const_at Scs 9)) lt_rx lt_ry hon)
    fun s₅ ⟨Kc₅, U₅, f₅, rep₅, xolt, xoeq, _, _⟩ => ?_)
  obtain hw₅ := hw₄.of_kc Kc₅
  obtain h2 : s₅.gpr .s2 = s.gpr .a0 := by
    rw [Kc₅.gpr _ (by decide) (by decide), r₄.gpr _ (by decide), r₃.gpr _ (by decide), K₂.gpr _ (by decide), S2]
  obtain wr₅ : s₅.wr = s.wr := by rw [Kc₅.wr, r₄.wr, r₃.wr, K₂.wr, Swr]
  obtain fl₄ : word s₄.mem base (E.c.sl FLAG) = F := by
    rw [O₄.word (.inr (sl_le _ (by decide))) (by kit_slots E), O₃.word (.inr (sl_le _ (by decide))) (by kit_slots E),
      hF]
  obtain k₄ : sv E.c base s₄ K = ofBytes (bytesAt s.mem (s.gpr .a1) E.L) := (keep K (by decide)).trans Sk
  refine WP.mono (E.fin_ok hw₅ h2 (fun i hi => by
      rw [wr₅, hs.wr]
      exact ⟨_, List.mem_cons_self .., Offset.contains_base (s.gpr .a0) (d := i) (n := 1) (k := E.L)
        (by omega_using [hi]) (by omega_using [hi, hLn, h9])⟩)
    (fun i hi => by
      have := out_of_disj (hb ▸ hs.out) hs.fo (off := 0) (i := i) (by omega_using [hi]); rwa [Nat.zero_add] at this)
    (b := (((decide (s.mem (s.gpr .a2) = 4) && decide (E.CC.Valid x y)) &&
      decide (ofBytes (bytesAt s.mem (s.gpr .a1) E.L) < E.c.C.n)) &&
      !decide (ofBytes (bytesAt s.mem (s.gpr .a1) E.L) = 0)))
    (by rw [f₅, fl₄, f₂, Sflag, mask_eq, k₄, maskOf_and, maskOf_and, maskOf_and]))
    fun s' ⟨a0', bytes', s0', s1', s2', ra', s3', regs', sp'⟩ => ?_
  obtain U₁₅ := U₁₄.trans U₅
  obtain lo : ∀ w ∈ ((E.checkKW ++ [(E.c.sl RX, 8 * E.c.n)]) ++ [(E.c.sl RY, 8 * E.c.n)]) ++ E.tailW, 40 ≤ w.1 := by
    kit_ranges (first | exact E.check_lo | exact E.tail_lo | exact Nat.le_trans (by decide) (sl_lo _ _))
  -- The registers.
  refine ⟨⟨fun r hr => ?_, by rw [sp', Kc₅.sp, r₄.sp, r₃.sp, K₂.sp, Ssp],
    by rw [ra', lo_word U₁₅ lo (d := 24) (by decide), Ssv3]⟩, ?_⟩
  · by_cases h0 : r = .s0
    · subst h0; rw [s0', lo_word U₁₅ lo (d := 0) (by decide), Ssv0]
    by_cases h1 : r = .s1
    · subst h1; rw [s1', lo_word U₁₅ lo (d := 8) (by decide), Ssv1]
    by_cases h2' : r = .s2
    · subst h2'; rw [s2', lo_word U₁₅ lo (d := 16) (by decide), Ssv2]
    by_cases h3' : r = .s3
    · subst h3'; rw [s3', lo_word U₁₅ lo (d := 32) (by decide), Ssv4]
    obtain ht : r ∉ [Reg.t0] := by rintro h; simp only [List.mem_singleton] at h; subst h; exact absurd hr (by decide)
    rw [regs' r hr h0 h1 h2' h3', Kc₅.gpr r hr h1, r₄.gpr r ht, r₃.gpr r ht, K₂.gpr r hr, Sregs r h0 h2' h3' hr]
  -- The specification.
  generalize hD : ofBytes (bytesAt s.mem (s.gpr .a1) E.L) = D at k₄ a0' bytes'
  generalize hb0 : s.mem (s.gpr .a2) = b0 at a0' bytes' Sflag
  rw [k₄] at rep₅
  obtain hlen : (bytesAt s.mem (s.gpr .a2) (1 + 2 * E.L)).length = 2 * E.c.C.len + 1 := by
    rw [VG.Proof.Weierstrass.length_bytesAt, E.len]; omega_using []
  obtain hpb := peer_bytes s.mem (s.gpr .a2) E.L
  obtain hhd : (bytesAt s.mem (s.gpr .a2) (1 + 2 * E.L)).head? = some b0 := by rw [hpb, ← hb0]; rfl
  obtain hxv : ofBytes (((bytesAt s.mem (s.gpr .a2) (1 + 2 * E.L)).drop 1).take E.c.C.len) = x := by
    rw [E.len, hpb, List.drop_one, List.tail_cons,
      List.take_left' (VG.Proof.Weierstrass.length_bytesAt _ _ _)]; exact Sx.symm
  obtain hyv : ofBytes ((bytesAt s.mem (s.gpr .a2) (1 + 2 * E.L)).drop (E.c.C.len + 1)) = y := by
    rw [E.len, hpb, List.drop_succ_cons, List.drop_left' (VG.Proof.Weierstrass.length_bytesAt _ _ _)]
    exact Sy.symm
  obtain hex : E.ex s.mem (s.gpr .a1) (s.gpr .a2) =
      Spec.Ecdh.exchange E.c.C D (bytesAt s.mem (s.gpr .a2) (1 + 2 * E.L)) := by
    rw [← hD]
  unfold post
  rw [hex]
  by_cases hd : 1 ≤ D ∧ D < E.c.C.n
  · obtain ⟨hR, -, -, rzlt⟩ := rep₅ hd.1 hd.2
    obtain hP : ∀ h : VG.Proof.Ecdh.Valid E.c.C b0 x y,
        Point.affine (toM E.c.C.p (2 ^ (64 * E.c.n)) (sv E.c base s₄ RX))
          (toM E.c.C.p (2 ^ (64 * E.c.n)) (sv E.c base s₄ RY)) = .affine ⟨x, h.2.1⟩ ⟨y, h.2.2.1⟩ := fun h => by
      obtain hv : E.CC.Valid x y := (valid_iff_of E.CCW x y).mpr h.2
      obtain hF0 : F ≠ 0 := by
        rw [f₂, Sflag, mask_eq, decide_eq_true h.1, decide_eq_true hv]; decide
      rw [rx₄, ry₄, px₂, py₂, ite_eq_right hF0, ite_eq_right hF0, toM_mont E.unit, toM_mont E.unit,
        VG.Proof.EcKey.fe_eq h.2.1 rfl, VG.Proof.EcKey.fe_eq h.2.2.1 rfl]
    rw [VG.Proof.Ecdh.exchange_eq hL hlen hhd hxv hyv hP hR xolt xoeq, E.len]
    obtain key : ((((decide (b0 = 4) && decide (E.CC.Valid x y)) && decide (D < E.c.C.n)) && !decide (D = 0)) &&
        !decide (sv E.c base s₅ RZ = 0)) = true ↔
        (1 ≤ D ∧ D < E.c.C.n) ∧ VG.Proof.Ecdh.Valid E.c.C b0 x y ∧
          toM E.c.C.p (2 ^ (64 * E.c.n)) (sv E.c base s₅ RZ) ≠ 0 := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
      rw [ne_eq, toM_eq_zero_iff E.unit rzlt, valid_iff_of E.CCW]
      unfold VG.Proof.Ecdh.Valid
      constructor
      · rintro ⟨⟨⟨⟨h4, hv⟩, hn⟩, hz⟩, hr⟩; exact ⟨⟨by omega_using [hd], hn⟩, ⟨h4, hv⟩, hr⟩
      · rintro ⟨⟨h1, hn⟩, ⟨h4, hv⟩, hr⟩; exact ⟨⟨⟨⟨h4, hv⟩, hn⟩, by omega_using [hd]⟩, hr⟩
    by_cases hc : (1 ≤ D ∧ D < E.c.C.n) ∧ VG.Proof.Ecdh.Valid E.c.C b0 x y ∧
        toM E.c.C.p (2 ^ (64 * E.c.n)) (sv E.c base s₅ RZ) ≠ 0
    · have hb := key.mpr hc
      rw [ite_eq_left hc]
      rw [hb] at a0' bytes'
      exact ⟨a0', bytes'⟩
    · have hb : ((((decide (b0 = 4) && decide (E.CC.Valid x y)) && decide (D < E.c.C.n)) && !decide (D = 0)) &&
          !decide (sv E.c base s₅ RZ = 0)) = false := by
        cases h : ((((decide (b0 = 4) && decide (E.CC.Valid x y)) && decide (D < E.c.C.n)) && !decide (D = 0)) &&
          !decide (sv E.c base s₅ RZ = 0))
        · rfl
        · exact absurd (key.mp h) hc
      rw [ite_eq_right hc]
      rw [hb] at a0' bytes'
      exact ⟨a0', bytes'.trans (by rw [ite_eq_right Bool.false_ne_true]; exact toBytes_zero _)⟩
  · rw [exchange_none _ hd]
    obtain hb : ((((decide (b0 = 4) && decide (E.CC.Valid x y)) && decide (D < E.c.C.n)) && !decide (D = 0)) &&
        !decide (sv E.c base s₅ RZ = 0)) = false := by
      by_cases hn : D < E.c.C.n
      · have : D = 0 := by omega_using [hd, hn]
        simp [this]
      · simp [hn]
    rw [hb] at a0' bytes'
    exact ⟨a0', bytes'.trans (by rw [ite_eq_right Bool.false_ne_true]; exact toBytes_zero _)⟩

end Kit

end VG.Proof.Ecdh.RISCV64
