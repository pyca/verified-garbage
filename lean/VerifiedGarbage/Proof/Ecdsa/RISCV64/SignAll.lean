module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.ExchangeAll
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Sign
public import VerifiedGarbage.Spec.Ecdsa
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Weierstrass.Words

/-!
# ECDSA signatures on RISC-V: correctness, for every curve

`vg_ecdsa_<curve>_sign` meets its contract by register, given the group law
(`Kit.sign_ok`), once for every curve whose numbers are whole bytes of the
order's bits: what the proof needs of a curve is its `Kit`, which is ECDH's
(`Proof/Ecdh/RISCV64/ExchangeAll.lean`: the configuration, the layout, how the
code reads and writes a number) and the functions modulo the order `n`, with
its chain of `n - 2`.

The proof is the setup (`setup_ok`: the saves, `k`, `d` and the digest, the
flag, the constants, `d`'s range and `G` to `R`), ECDH's `tail` (`k`'s range,
`R = [k]G`, `x`), which `sign_ok` takes as a hypothesis, since a curve
multiplies `G` by its comb or by its window (`signTail_ok` is the latter), the
values modulo `n` (`nback_ok`), and the end (`finish_ok`: the checks of `r`
and `s`, and the signature under the flag); the specification's signature is
`signWith_eq`'s (`Proof/Ecdsa/Sign.lean`). Each `<Curve>/Sign.lean` is the
curve's kit, its contract, and the statements about it that other modules use.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.SignAll

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg VG.Impl.Ecdsa.RISCV64.Sign
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt hashToInt)
open VG.WriteBytes (writeBytes)
open VG.Proof.Ecdh.RISCV64 (TKit)
open VG.Proof.Ecdh.RISCV64.Kit (sv sl8 sl_lo sl_le sl_sep sl_top all_app all_one consts_nodup constCode_eq
  apart_consts flag_consts lo_consts maskOf_and not_mask and_one out_of_disj sep_at' bytesAt_unch
  bytesAt_writeBytes lo_word own_ge wp_syms_frame toBytes_zero)

/-! ## Slots -/

theorem le55 {i : Nat} (h : i < 45) : i ≤ 55 := Nat.le_trans (Nat.le_of_lt h) (by decide)

/-- A slot is in the working space. -/
theorem sl_64 {c : Cfg} (h9 : c.n ≤ 9) {i : Nat} (hi : i ≤ 55) : c.sl i + 8 * c.n ≤ 2 ^ 64 :=
  Nat.le_trans (sl_top h9 hi) (by decide)

/-- A slot's offset is one `ldAt` and `sdAt` reach. -/
theorem sl_lt {c : Cfg} (h1 : 1 ≤ c.n) (h9 : c.n ≤ 9) {i : Nat} (hi : i ≤ 55) : c.sl i < 4095 := by
  have := sl_top h9 hi
  omega

/-- The flag's word is in the working space. -/
theorem flag_top {c : Cfg} (h1 : 1 ≤ c.n) (h9 : c.n ≤ 9) : c.sl FLAG + 8 ≤ 4096 := by
  have := sl_top h9 (i := FLAG) (by decide)
  omega

theorem flag_64 {c : Cfg} (h1 : 1 ≤ c.n) (h9 : c.n ≤ 9) : c.sl FLAG + 8 ≤ 2 ^ 64 :=
  Nat.le_trans (flag_top h1 h9) (by decide)

/-- A slot below the flag's is below the own working space of the field's functions. -/
theorem below_own {c : Cfg} (h9 : c.n ≤ 9) {i : Nat} (hi : i < 45) : c.sl i + 8 * c.n ≤ own c.n :=
  Nat.le_trans (sl_le c hi) (Nat.le_trans (Nat.le_add_right _ _) (own_ge h9))

/-- The flag is below it too. -/
theorem flag_own {c : Cfg} (h9 : c.n ≤ 9) : c.sl FLAG + 8 ≤ own c.n :=
  Nat.le_trans (Nat.add_le_add_right (Nat.le_trans (Nat.le_add_right _ _) (sl_le c (by decide : FLAG < 45))) 8)
    (own_ge h9)

theorem all_cons {P : Nat × Nat → Prop} {a : Nat × Nat} {W : List (Nat × Nat)} (h : P a) (h' : ∀ w ∈ W, P w) :
    ∀ w ∈ a :: W, P w := fun w hw => by
  rcases List.mem_cons.mp hw with rfl | hw
  exacts [h, h' w hw]

/-- A slot apart from what changed. -/
theorem sv_unch {c : Cfg} (h9 : c.n ≤ 9) {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (U : Unch base W m m')
    (i : Nat) (h : ∀ w ∈ W, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i) (hi : i ≤ 55 := by decide) :
    wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n :=
  U.wordsVal h (sl_64 h9 hi)

/-! ## What a call of a function modulo `n` writes -/

/-- What a call writes: its result and the field's own working space. -/
abbrev cw (c : Cfg) (o : Nat) : List (Nat × Nat) := [(c.sl o, 8 * c.n), (own c.n, 64 * c.n)]

/-- A call keeps the other slots. -/
theorem cw_keep {c : Cfg} (h9 : c.n ≤ 9) {i o : Nat} (hio : i ≠ o) (hi : i < 45) :
    ∀ w ∈ cw c o, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  all_cons (sl_sep c hio) (all_one (.inl (below_own h9 hi)))

/-- A call that writes a slot below the flag's keeps the flag. -/
theorem cw_flag {c : Cfg} (h9 : c.n ≤ 9) {o : Nat} (ho : o < FLAG) :
    ∀ w ∈ cw c o, c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG :=
  all_cons (.inr (sl_le c ho)) (all_one (.inl (flag_own h9)))

/-- A call keeps the saved registers. -/
theorem cw_lo {c : Cfg} (h9 : c.n ≤ 9) (o : Nat) : ∀ w ∈ cw c o, 40 ≤ w.1 :=
  all_cons (Nat.le_trans (by decide) (sl_lo c o))
    (all_one (Nat.le_trans (Nat.le_trans (by decide) (sl_lo c FLAG)) (Nat.le_trans (Nat.le_add_right _ _) (flag_own h9))))

/-! ## The chain of `n - 2` -/

theorem chainN_acc (c : Cfg) : (Cfg.chainN c).acc = c.sl ACC := rfl
theorem chainN_base (c : Cfg) : (Cfg.chainN c).base = c.sl KM := rfl
theorem chainN_tbl (c : Cfg) : (Cfg.chainN c).tbl = c.sl TB := rfl

/-- The chain's slots. -/
theorem chainNLay (c : Cfg) (h1 : 1 ≤ c.n) (h9 : c.n ≤ 9) : ChainLayR (Cfg.chainN c) c.n := by
  obtain h := rvOwn_cases c.n
  refine ⟨rfl, h1, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, sl8 _ _, sl8 _ _, sl8 _ _, ?_, ?_, ?_⟩ <;>
    simp only [chainN_acc, chainN_base, chainN_tbl, Cfg.sl, slot, ACC, KM, TB, own] <;> omega_using [h9, h]

/-- What the chain writes. -/
theorem chainN_wx (c : Cfg) :
    chainWx (Cfg.chainN c) c.n = [(c.sl ACC, 8 * c.n), (c.sl TB, 9 * (8 * c.n)), (own c.n, 64 * c.n)] := rfl

/-- The chain keeps the slots below the flag's, but its result. -/
theorem chainN_keep {c : Cfg} (h9 : c.n ≤ 9) {i : Nat} (hi : i < 45) (ha : i ≠ ACC) :
    ∀ w ∈ chainWx (Cfg.chainN c) c.n, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  rw [chainN_wx]
  exact all_cons (sl_sep c ha) (all_cons (.inl (sl_le c (Nat.lt_trans hi (by decide))))
    (all_one (.inl (below_own h9 hi))))

theorem chainN_flag {c : Cfg} (h1 : 1 ≤ c.n) (h9 : c.n ≤ 9) :
    ∀ w ∈ chainWx (Cfg.chainN c) c.n, c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := by
  rw [chainN_wx]
  refine all_cons (.inr (sl_le c (by decide))) (all_cons (.inl ?_) (all_one (.inl (flag_own h9))))
  have := sl_le c (by decide : FLAG < TB)
  omega

theorem chainN_lo {c : Cfg} (h9 : c.n ≤ 9) : ∀ w ∈ chainWx (Cfg.chainN c) c.n, 40 ≤ w.1 := by
  rw [chainN_wx]
  exact all_cons (Nat.le_trans (by decide) (sl_lo c _)) (all_cons (Nat.le_trans (by decide) (sl_lo c _))
    (all_one (Nat.le_trans (Nat.le_trans (by decide) (sl_lo c FLAG))
      (Nat.le_trans (Nat.le_add_right _ _) (flag_own h9)))))

/-! ## The constants modulo `n` -/

theorem nconsts_fst (c : Cfg) : (Cfg.nConsts c).map Prod.fst = [R2N, ONEN, EXPN] := rfl

theorem nconsts_nodup (c : Cfg) : ((Cfg.nConsts c).map Prod.fst).Nodup := by rw [nconsts_fst]; decide

theorem mem_nslots {c : Cfg} {e : Nat × Nat} (he : e ∈ Cfg.nConsts c) : e.1 ∈ [R2N, ONEN, EXPN] := by
  rw [← nconsts_fst c]; exact List.mem_map.mpr ⟨e, he, rfl⟩

theorem nconsts_le (c : Cfg) : ∀ e ∈ Cfg.nConsts c, e.1 ≤ 55 := fun _ he =>
  (by decide : ∀ i ∈ [R2N, ONEN, EXPN], i ≤ 55) _ (mem_nslots he)

/-- A slot that is not one of them is apart from the constants modulo `n`. -/
theorem apart_nconsts (c : Cfg) {i : Nat} (hi : ∀ j ∈ [R2N, ONEN, EXPN], i ≠ j) :
    ∀ w ∈ (Cfg.nConsts c).map (fun e => (c.sl e.1, 8 * c.n)), c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  fun w hw => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hw
    exact sl_sep c (hi _ (mem_nslots he))

theorem flag_nconsts (c : Cfg) :
    ∀ w ∈ (Cfg.nConsts c).map (fun e => (c.sl e.1, 8 * c.n)), c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG :=
  fun w hw => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hw
    exact .inr (sl_le c ((by decide : ∀ i ∈ [R2N, ONEN, EXPN], i < FLAG) _ (mem_nslots he)))

theorem lo_nconsts (c : Cfg) : ∀ w ∈ (Cfg.nConsts c).map (fun e => (c.sl e.1, 8 * c.n)), 40 ≤ w.1 :=
  fun w hw => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hw
    exact Nat.le_trans (by decide) (sl_lo c _)

/-! ## The field's functions, for `k` words modulo `p` -/

/-- `addCall_ok`, for a field of `k` words modulo `p`. -/
theorem addCall_kit {F : Field} (hF : FieldOk F) {k p : Nat} (hk : F.S.k = k) (hm : F.S.m = p) {s : State}
    {base : Addr} (hw : WsReg s base) {o a b : Nat}
    (ho : o + 8 * k ≤ own k) (ha : a + 8 * k ≤ own k) (hb : b + 8 * k ≤ own k)
    (ho' : o < 4095) (ha' : a < 4095) (hb' : b < 4095)
    (hAB : wordsVal s.mem base a k + wordsVal s.mem base b k < 2 * p) :
    WP isa (addCall F o a b) s fun s' => CallKeep k base o s s' ∧
      wordsVal s'.mem base o k = (wordsVal s.mem base a k + wordsVal s.mem base b k) % p := by
  subst hk hm; exact addCall_ok hF hw ho ha hb ho' ha' hb' hAB

/-! ## What `tail` and the values modulo `n` write -/

/-- A slot apart from a run of `k` slots from slot `j`, of `b` bytes. -/
theorem run_apart (c : Cfg) {i j k b : Nat} (hb : b = 8 * c.n * k) (h : i < j ∨ j + k ≤ i) :
    c.sl i + 8 * c.n ≤ c.sl j ∨ c.sl j + b ≤ c.sl i := by
  rcases h with h | h
  · exact .inl (sl_le c h)
  · have := Nat.mul_le_mul_left (8 * c.n) h
    rw [Nat.mul_add] at this
    subst hb
    simp only [Cfg.sl, slot]; omega

/-- `tail` keeps what the values modulo `n` read. -/
theorem tailW_keep (c : Cfg) (h9 : c.n ≤ 9) : ∀ i ∈ [ZERO, ONE, K, DD, EE, R2N, ONEN, EXPN], ∀ w ∈ TKit.tailW c,
    c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro i hi
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := (by decide : ∀ i ∈ [ZERO, ONE, K, DD, EE, R2N, ONEN, EXPN],
    i < FLAG ∧ (i < 14 ∨ 14 + 3 ≤ i) ∧ (i < 17 ∨ 17 + 14 ≤ i) ∧ i ≠ 2 ∧ i ≠ 40 ∧ i ≠ ACC ∧ i ≠ XM ∧ i ≠ XO) i hi
  obtain h45 : i < 45 := Nat.lt_trans h1 (by decide)
  obtain hown := below_own h9 h45
  exact all_app (all_app (all_app (all_one (.inl (sl_le c h1)))
      (all_cons (run_apart c (by omega) h2) (all_cons (run_apart c (by omega) h3) (all_cons (sl_sep c h4)
        (all_cons (sl_sep c h5) (all_one (.inl (sl_le c h45))))))))
      (chainN_keep h9 h45 h6))
    (all_cons (sl_sep c h7) (all_cons (.inl hown) (all_cons (sl_sep c h8) (all_one (.inl hown)))))

/-- What the values modulo `n` write. -/
abbrev backW (c : Cfg) : List (Nat × Nat) :=
  cw c RR ++ cw c KM ++ chainWx (Cfg.chainN c) c.n ++ cw c EM ++ cw c RM ++ cw c DM ++ cw c TT ++ cw c SU ++
    cw c SMM ++ cw c SS

theorem backW_lo (c : Cfg) (h9 : c.n ≤ 9) : ∀ w ∈ backW c, 40 ≤ w.1 := by
  repeat' with_reducible apply all_app
  all_goals first | exact cw_lo h9 _ | exact chainN_lo h9

theorem backW_flag (c : Cfg) (h1 : 1 ≤ c.n) (h9 : c.n ≤ 9) :
    ∀ w ∈ backW c, c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := by
  repeat' with_reducible apply all_app
  all_goals first | exact cw_flag h9 (by decide) | exact chainN_flag h1 h9

/-! ## The flag's checks -/

/-- The flag `&=` the mask of the number at slot `i` being nonzero. -/
theorem nzFlag_ok (c : Cfg) (h9 : c.n ≤ 9) {i : Nat} (hi : i < 45) {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block (Cfg.nonzeroFlag c i)) s fun s' =>
      Rest [.t0, .t3, .t4, .a7] s s' ∧ Outside base (c.sl FLAG) 8 s.mem s'.mem ∧
      word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) &&& maskOf (!decide (sv c base s i = 0)) := by
  rw [Cfg.nonzeroFlag]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (zeroMask_ok hw (n := c.n) (a := c.sl i) (sl8 _ _) (sl_top h9 (le55 hi)))
    fun s₁ ⟨r₁, m₁, g₁⟩ => ?_)
  rw [List.singleton_append]
  refine WP.cons (exec_logicImm (by decide)) ?_
  obtain r₁' := r₁.trans ((Upd.write s₁ .a7 (s₁.gpr .a7 ^^^ BitVec.ofInt 64 (-1))).rest (ws := [.t3, .t4, .a7])
    (by decide))
  refine WP.mono (TKit.andFlag_ok c h9 (hw.of_rest r₁')) fun s₂ ⟨f₂, r₂, O₂⟩ => ⟨(r₁'.mono (by decide)).trans
    (r₂.mono (by decide)), by
      have : Outside base (c.sl FLAG) 8 s.mem (s₁.write .a7 (s₁.gpr .a7 ^^^ BitVec.ofInt 64 (-1))).mem := by
        show Outside base (c.sl FLAG) 8 s.mem s₁.mem; rw [m₁]; exact Outside.refl _ _ _ _
      exact this.trans O₂, ?_⟩
  rw [f₂]
  simp only [State.write, ↓reduceIte]
  rw [m₁, g₁, not_mask]

theorem signWith_none {C : Curve} {d e k : Nat} (h : ¬ (1 ≤ k ∧ k < C.n)) : Spec.Ecdsa.signWith C d e k = none := by
  unfold Spec.Ecdsa.signWith
  rw [ite_eq_right_iff.mpr]
  intro h'; exact absurd ⟨h'.2.2.1, h'.2.2.2⟩ h

/-! ## The kit -/

/-- What the proof needs of a curve, beside ECDH's kit: the functions modulo the order `n`. -/
structure Kit extends VG.Proof.Ecdh.RISCV64.Kit where
  /-- The functions modulo `n`, which meet their contracts, for numbers of the curve's words. -/
  FN : Field
  order_ok : FieldOk FN
  FNk : FN.S.k = c.n
  FNm : FN.S.m = c.C.n
  /-- `n` is odd, and more than half of `p`: `x mod n` is one subtraction. -/
  n_odd : c.C.n % 2 = 1
  pn : c.C.p < 2 * c.C.n
  /-- The bits of `n` are the bytes of a number: a digest of as many bytes is its integer. -/
  nBits : Spec.Ecdsa.nBits c.C = 8 * L
  /-- The chain of `n - 2`. -/
  chainN_ok : ChainOkR (Cfg.chainN c) (c.C.n - 2)
  /-- The constants modulo `n` are below `2^(64 n)`. -/
  nconsts_lt : ∀ e ∈ Cfg.nConsts c, e.2 < 2 ^ (64 * c.n)

instance (Kt : Kit) : NeZero Kt.c.C.n :=
  ⟨fun h => by have := Kt.n_odd; rw [h] at this; exact absurd this (by decide)⟩

namespace Kit

variable (Kt : Kit)

theorem n1 : 1 ≤ Kt.c.n := Nat.le_trans (by decide) Kt.n4

theorem unitN : UnitMod Kt.c.C.n (2 ^ (64 * Kt.c.n)) := unitMod_pow_two Kt.n_odd _

/-- The integer of a digest of a number's bytes is its number. -/
theorem hash_eq (m : Mem) (q : Addr) : hashToInt Kt.c.C (bytesAt m q Kt.L) = ofBytes (bytesAt m q Kt.L) := by
  rw [hashToInt, ite_eq_left (by rw [VG.Proof.Weierstrass.length_bytesAt, Kt.nBits])]

/-! ## The setup -/

/-- What the contract gives, by register: the private key, the digest and the secret number are
readable, the signature and the working space writable. -/
structure Pre (s : State) : Prop where
  d : (⟨s.gpr .a1, Kt.L⟩ : Region) ∈ s.rd
  e : (⟨s.gpr .a2, Kt.L⟩ : Region) ∈ s.rd
  k : (⟨s.gpr .a3, Kt.L⟩ : Region) ∈ s.rd
  wr : s.wr = [⟨s.gpr .a0, 2 * Kt.L⟩, ⟨s.gpr .a4, 8192⟩]
  od : (⟨s.gpr .a0, 2 * Kt.L⟩ : Region).Disjoint ⟨s.gpr .a4, 8192⟩
  dd : (⟨s.gpr .a1, Kt.L⟩ : Region).Disjoint ⟨s.gpr .a4, 8192⟩
  ed : (⟨s.gpr .a2, Kt.L⟩ : Region).Disjoint ⟨s.gpr .a4, 8192⟩
  kd : (⟨s.gpr .a3, Kt.L⟩ : Region).Disjoint ⟨s.gpr .a4, 8192⟩
  fo : (s.gpr .a0).toNat + 2 * Kt.L ≤ 2 ^ 64
  fd : (s.gpr .a1).toNat + Kt.L ≤ 2 ^ 64
  fe : (s.gpr .a2).toNat + Kt.L ≤ 2 ^ 64
  fk : (s.gpr .a3).toNat + Kt.L ≤ 2 ^ 64
  fs : (s.gpr .a4).toNat + 8192 ≤ 2 ^ 64
  al : (s.gpr .a4).toNat % 8 = 0

/-- What the setup leaves, from `s`, with `base` the working space. -/
structure SetupS (base : Addr) (s s' : State) : Prop where
  ws : WsReg s' base
  s2 : s'.gpr .s2 = s.gpr .a0
  s3 : s'.gpr .s3 = base
  regs : ∀ x, x ≠ .s0 → x ≠ .s2 → x ≠ .s3 → x ∈ preserved → s'.gpr x = s.gpr x
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  sv0 : word s'.mem base 0 = s.gpr .s0
  sv1 : word s'.mem base 8 = s.gpr .s1
  sv2 : word s'.mem base 16 = s.gpr .s2
  sv3 : word s'.mem base 24 = s.gpr .ra
  sv4 : word s'.mem base 32 = s.gpr .s3
  k : sv Kt.c base s' K = ofBytes (bytesAt s.mem (s.gpr .a3) Kt.L)
  d : sv Kt.c base s' DD = ofBytes (bytesAt s.mem (s.gpr .a1) Kt.L)
  e : sv Kt.c base s' EE = ofBytes (bytesAt s.mem (s.gpr .a2) Kt.L)
  tc : TKit.Consts Kt.c base s'
  r2n : sv Kt.c base s' R2N = 2 ^ (64 * Kt.c.n) * 2 ^ (64 * Kt.c.n) % Kt.c.C.n
  onen : sv Kt.c base s' ONEN = 2 ^ (64 * Kt.c.n) % Kt.c.C.n
  expn : sv Kt.c base s' EXPN = Kt.c.C.n - 2
  bp : sv Kt.c base s' BP = Kt.c.C.b * 2 ^ (64 * Kt.c.n) % Kt.c.C.p
  rx : sv Kt.c base s' RX = Kt.c.C.gx * 2 ^ (64 * Kt.c.n) % Kt.c.C.p
  ry : sv Kt.c base s' RY = Kt.c.C.gy * 2 ^ (64 * Kt.c.n) % Kt.c.C.p
  flag : word s'.mem base (Kt.c.sl FLAG) =
    maskOf ((true && decide (ofBytes (bytesAt s.mem (s.gpr .a1) Kt.L) < Kt.c.C.n)) &&
      !decide (ofBytes (bytesAt s.mem (s.gpr .a1) Kt.L) = 0))

/-- The registers saved, the arguments read, the flag set, the constants stored, the mask of `d` in
`[1, n-1]`, and `G` to `R`'s first two slots: `Sign.Cfg.setup`, as the kit reads its numbers. -/
def setup : List Instr :=
  saveCode .a4 ++ Kt.load (Kt.c.sl K) .a3 0 ++ Kt.load (Kt.c.sl DD) .a1 0 ++
    Kt.load (Kt.c.sl EE) .a2 0 ++ [.li .t0 0, .addi .t0 .t0 (-1)] ++ sdAt .t0 wb (Kt.c.sl FLAG) ++
    constCode Kt.c ++ (Cfg.nConsts Kt.c).flatMap (fun (i, x) => setConst Kt.c.n (Kt.c.sl i) x) ++
    rangeOf Kt.c DD ++ copy Kt.c.n (Kt.c.sl RX) (Kt.c.sl GX) ++ copy Kt.c.n (Kt.c.sl RY) (Kt.c.sl GY)

/-- `setup`: the saves, `k`, `d` and the digest, the flag set, the
constants, the mask of `d` in `[1, n-1]`, and `G` to `R`'s first two slots. -/
theorem setup_ok {s : State} (hs : Kt.Pre s) : WP isa (.block Kt.setup) s (Kt.SetupS (s.gpr .a4) s) := by
  obtain ⟨hrdd, hrde, hrdk, hwr, hod, hdd, hed, hkd, hfo, hfd, hfe, hfk, hfs, hal⟩ := hs
  obtain hL := Kt.Ln
  obtain h9 := Kt.n9
  obtain h1 := Kt.n1
  rw [setup]
  simp only [List.append_assoc]
  generalize hb : s.gpr .a4 = base at hwr hod hdd hed hkd hfs hal
  obtain hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  refine WP.block_append (WP.mono (TKit.save_ok hb hwr' hfs hal)
    fun s₁ ⟨hw₁, h3₁, o₁, g₁, rd₁, wr₁, sp₁, U₁, w0, w1, w2, w3, w4⟩ => ?_)
  obtain a1 : s₁.gpr .a1 = s.gpr .a1 := g₁ _ (by decide) (by decide) (by decide)
  obtain a2 : s₁.gpr .a2 = s.gpr .a2 := g₁ _ (by decide) (by decide) (by decide)
  obtain a3 : s₁.gpr .a3 = s.gpr .a3 := g₁ _ (by decide) (by decide) (by decide)
  obtain rdd : (⟨s.gpr .a1, Kt.L⟩ : Region) ∈ s₁.rd ++ s₁.wr := by rw [rd₁]; exact List.mem_append_left _ hrdd
  obtain rde : (⟨s.gpr .a2, Kt.L⟩ : Region) ∈ s₁.rd ++ s₁.wr := by rw [rd₁]; exact List.mem_append_left _ hrde
  obtain rdk : (⟨s.gpr .a3, Kt.L⟩ : Region) ∈ s₁.rd ++ s₁.wr := by rw [rd₁]; exact List.mem_append_left _ hrdk
  -- `k`, `d` and the digest.
  refine WP.block_append (WP.mono (Kt.load_ok (i := K) (p := .a3) (off := 0) (R := Kt.L) hw₁ (by decide) (by decide)
    (by omega_using []) (by omega_using [hL, h9]) (by rw [a3]; exact rdk)
    (fun j hj => by rw [a3]; exact out_of_disj hkd hfk (by omega_using [hj])))
    fun s₂ ⟨r₂, O₂, e₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  refine WP.block_append (WP.mono (Kt.load_ok (i := DD) (p := .a1) (off := 0) (R := Kt.L) hw₂ (by decide) (by decide)
    (by omega_using []) (by omega_using [hL, h9]) (by rw [r₂.gpr _ (by decide), a1, r₂.rd, r₂.wr]; exact rdd)
    (fun j hj => by rw [r₂.gpr _ (by decide), a1]; exact out_of_disj hdd hfd (by omega_using [hj])))
    fun s₃ ⟨r₃, O₃, e₃⟩ => ?_)
  obtain hw₃ := hw₂.of_rest r₃
  obtain r₂₃ := r₂.trans r₃
  refine WP.block_append (WP.mono (Kt.load_ok (i := EE) (p := .a2) (off := 0) (R := Kt.L) hw₃ (by decide) (by decide)
    (by omega_using []) (by omega_using [hL, h9]) (by rw [r₂₃.gpr _ (by decide), a2, r₂₃.rd, r₂₃.wr]; exact rde)
    (fun j hj => by rw [r₂₃.gpr _ (by decide), a2]; exact out_of_disj hed hfe (by omega_using [hj])))
    fun s₄ ⟨r₄, O₄, e₄⟩ => ?_)
  obtain hw₄ := hw₃.of_rest r₄
  obtain r₂₄ := r₂₃.trans r₄
  -- The flag.
  rw [List.cons_append, List.cons_append, List.nil_append]
  refine wp_li (imm := 0) (by decide) fun s₄a u₄a => ?_
  refine WP.cons (exec_addi (by decide)) ?_
  obtain u₄b := Upd.write s₄a .t0 (s₄a.gpr .t0 + BitVec.ofInt 64 (-1))
  obtain hw₄b := (hw₄.of_kp (Kp.of_upd u₄a)).of_kp (Kp.of_upd u₄b)
  refine sdAt_ws hw₄b (by decide) (d := Kt.c.sl FLAG) (sl_lt h1 h9 (by decide)) (sl8 _ _) fun s₅ u₅ => ?_
  obtain hw₅ := hw₄b.of_kp (Kp.of_mupd u₅)
  obtain fl₅ : word s₅.mem base (Kt.c.sl FLAG) = maskOf true := by
    rw [u₅.mem, word_writeW_self, u₄b.gpr, u₄a.gpr]; decide
  -- The constants.
  rw [constCode_eq]
  refine WP.block_append (WP.mono (TKit.consts_ok Kt.c h9 _ hw₅ (TKit.consts_le Kt.c) (consts_nodup Kt.c))
    fun s₆ ⟨r₆, U₆, e₆⟩ => ?_)
  obtain hw₆ := hw₅.of_rest r₆
  refine WP.block_append (WP.mono (TKit.consts_ok Kt.c h9 _ hw₆ (nconsts_le Kt.c) (nconsts_nodup Kt.c))
    fun s₇ ⟨r₇, U₇, e₇⟩ => ?_)
  obtain hw₇ := hw₆.of_rest r₇
  -- `d`'s range.
  refine WP.block_append (WP.mono (TKit.rangeOf_ok Kt.c h9 (i := DD) (by decide) hw₇) fun s₈ ⟨K₈, O₈, f₈⟩ => ?_)
  obtain hw₈ := hw₇.of_kp K₈
  -- `G` to `R`.
  refine WP.block_append (WP.mono (copy_ok Kt.c.n hw₈ (o := Kt.c.sl RX) (a := Kt.c.sl GX) (sl8 _ _) (sl8 _ _)
    (sl_top h9 (by decide)) (sl_top h9 (by decide)) (.inr (sl_le _ (by decide)))) fun s₉ ⟨v₉, r₉, O₉⟩ => ?_)
  obtain hw₉ := hw₈.of_rest r₉
  refine WP.mono (copy_ok Kt.c.n hw₉ (o := Kt.c.sl RY) (a := Kt.c.sl GY) (sl8 _ _) (sl8 _ _)
    (sl_top h9 (by decide)) (sl_top h9 (by decide)) (.inr (sl_le _ (by decide)))) fun s₁₀ ⟨v₁₀, r₁₀, O₁₀⟩ => ?_
  obtain hw₁₀ := hw₉.of_rest r₁₀
  -- What each step leaves.
  obtain O₅ : Unch base [(Kt.c.sl FLAG, 8)] s₄.mem s₅.mem := by
    rw [u₅.mem, u₄b.mem, u₄a.mem]; exact (writeW_outside _ _ _ (flag_64 h1 h9)).unch
  obtain U₂₄ := (O₂.unch.trans O₃.unch).trans O₄.unch
  obtain U₅₇ := (O₅.trans U₆).trans U₇
  obtain U₈₁₀ := (O₈.unch.trans O₉.unch).trans O₁₀.unch
  obtain U₂₁₀ := (U₂₄.trans U₅₇).trans U₈₁₀
  obtain lo : ∀ w ∈ (([(Kt.c.sl K, 8 * Kt.c.n)] ++ [(Kt.c.sl DD, 8 * Kt.c.n)] ++ [(Kt.c.sl EE, 8 * Kt.c.n)]) ++
      (([(Kt.c.sl FLAG, 8)] ++ (consts Kt.c).map fun e => (Kt.c.sl e.1, 8 * Kt.c.n)) ++
        (Cfg.nConsts Kt.c).map fun e => (Kt.c.sl e.1, 8 * Kt.c.n))) ++
      (([(Kt.c.sl FLAG, 8)] ++ [(Kt.c.sl RX, 8 * Kt.c.n)]) ++ [(Kt.c.sl RY, 8 * Kt.c.n)]), 40 ≤ w.1 := by
    repeat' first | with_reducible apply all_app | with_reducible apply all_one
    all_goals first
      | exact Nat.le_trans (by decide) (sl_lo _ _)
      | exact lo_consts _
      | exact lo_nconsts _
  obtain sp0 : ∀ {q : Reg} {n : Nat}, (⟨s.gpr q, n⟩ : Region).Disjoint ⟨base, 8192⟩ → (s.gpr q).toNat + n ≤ 2 ^ 64 →
      ∀ i < n, ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr q + BitVec.ofNat 64 i) 1 := fun hd hf i hi => by
    simpa using sep_at' hd hf (off := 0) (k := _) (by omega_using []) i hi
  obtain bk : ∀ {q : Reg} {n : Nat}, (⟨s.gpr q, n⟩ : Region).Disjoint ⟨base, 8192⟩ → (s.gpr q).toNat + n ≤ 2 ^ 64 →
      bytesAt s₁.mem (s.gpr q) n = bytesAt s.mem (s.gpr q) n := fun hd hf =>
    bytesAt_unch U₁ (by decide) (sp0 hd hf)
  obtain cs₆ : ∀ e ∈ consts Kt.c, sv Kt.c base s₆ e.1 = e.2 := fun e he => by
    rw [e₆ e he, Nat.mod_eq_of_lt (Kt.consts_lt e he)]
  obtain cs₇ : ∀ e ∈ Cfg.nConsts Kt.c, sv Kt.c base s₇ e.1 = e.2 := fun e he => by
    rw [e₇ e he, Nat.mod_eq_of_lt (Kt.nconsts_lt e he)]
  obtain tc₆ : TKit.Consts Kt.c base s₆ := ⟨Kt.toKit.const_at cs₆ 0, Kt.toKit.const_at cs₆ 1, Kt.toKit.const_at cs₆ 2,
    Kt.toKit.const_at cs₆ 3, Kt.toKit.const_at cs₆ 4, Kt.toKit.const_at cs₆ 5, Kt.toKit.const_at cs₆ 6,
    Kt.toKit.const_at cs₆ 9⟩
  obtain K₁₀ : ∀ r ∈ preserved, s₁₀.gpr r = s₁.gpr r := fun r hr => by
    obtain h0 : r ∉ [Reg.t0] := fun h => by simp only [List.mem_singleton] at h; subst h; exact absurd hr (by decide)
    obtain h1 : r ∉ [Reg.t0, .t1] := fun h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> exact absurd hr (by decide)
    rw [r₁₀.gpr _ h0, r₉.gpr _ h0, K₈.gpr _ hr, r₇.gpr _ h1, r₆.gpr _ h1, u₅.gpr,
      u₄b.other _ (by rintro rfl; exact absurd hr (by decide)),
      u₄a.other _ (by rintro rfl; exact absurd hr (by decide)), r₂₄.gpr _ h1]
  obtain sv₁₀ : ∀ i, i < 45 → i ≠ RX → i ≠ RY → sv Kt.c base s₁₀ i = sv Kt.c base s₈ i := fun i hi h1 h2 => by
    show wordsVal _ _ _ _ = _
    rw [O₁₀.wordsVal (sl_sep _ h2) (sl_64 h9 (le55 hi)), O₉.wordsVal (sl_sep _ h1) (sl_64 h9 (le55 hi))]
  obtain sv₈ : ∀ i, i < FLAG → sv Kt.c base s₈ i = sv Kt.c base s₇ i := fun i hi =>
    O₈.wordsVal (.inl (sl_le _ hi)) (sl_64 h9 (le55 (Nat.lt_trans hi (by decide))))
  obtain sv₂₇ : ∀ i ∈ [K, DD, EE], sv Kt.c base s₇ i = sv Kt.c base s₄ i := fun i hi => by
    obtain ⟨h1, h2, h3, h4⟩ := (by decide : ∀ i ∈ [K, DD, EE],
      i < FLAG ∧ (∀ j ∈ VG.Proof.Ecdh.RISCV64.Kit.cslots, i ≠ j) ∧ (∀ j ∈ [R2N, ONEN, EXPN], i ≠ j) ∧ i ≤ 55) i hi
    exact sv_unch h9 U₅₇ i (all_app (all_app (all_one (.inl (sl_le _ h1))) (apart_consts _ h2))
      (apart_nconsts _ h3)) h4
  obtain dv : sv Kt.c base s₇ DD = ofBytes (bytesAt s.mem (s.gpr .a1) Kt.L) := by
    rw [sv₂₇ DD (by decide)]
    show wordsVal _ _ _ _ = _
    rw [O₄.wordsVal (.inl (sl_le _ (by decide))) (sl_64 h9 (by decide)), e₃, r₂.gpr _ (by decide), a1,
      BitVec.add_zero, bytesAt_unch O₂.unch (all_one (Nat.le_trans (sl_top h9 (by decide)) (by decide)))
        (sp0 hdd hfd), bk hdd hfd]
  refine ⟨hw₁₀, by rw [K₁₀ _ (by decide), o₁], by rw [K₁₀ _ (by decide), h3₁],
    fun x h0 h2 h3 hx => by rw [K₁₀ x hx, g₁ x h0 h2 h3], ?_, ?_, ?_,
    by rw [lo_word U₂₁₀ lo (d := 0) (by decide), w0], by rw [lo_word U₂₁₀ lo (d := 8) (by decide), w1],
    by rw [lo_word U₂₁₀ lo (d := 16) (by decide), w2], by rw [lo_word U₂₁₀ lo (d := 24) (by decide), w3],
    by rw [lo_word U₂₁₀ lo (d := 32) (by decide), w4], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r₁₀.rd, r₉.rd, K₈.rd, r₇.rd, r₆.rd, u₅.rd, u₄b.rd, u₄a.rd, r₂₄.rd, rd₁]
  · rw [r₁₀.wr, r₉.wr, K₈.wr, r₇.wr, r₆.wr, u₅.wr, u₄b.wr, u₄a.wr, r₂₄.wr, wr₁]
  · rw [r₁₀.sp, r₉.sp, K₈.sp, r₇.sp, r₆.sp, u₅.sp, u₄b.sp, u₄a.sp, r₂₄.sp, sp₁]
  · rw [sv₁₀ K (by decide) (by decide) (by decide), sv₈ K (by decide), sv₂₇ K (by decide)]
    show wordsVal _ _ _ _ = _
    rw [O₄.wordsVal (.inl (sl_le _ (by decide))) (sl_64 h9 (by decide)),
      O₃.wordsVal (.inl (sl_le _ (by decide))) (sl_64 h9 (by decide)), e₂, a3, BitVec.add_zero, bk hkd hfk]
  · rw [sv₁₀ DD (by decide) (by decide) (by decide), sv₈ DD (by decide), dv]
  · rw [sv₁₀ EE (by decide) (by decide) (by decide), sv₈ EE (by decide), sv₂₇ EE (by decide)]
    show wordsVal _ _ _ _ = _
    rw [e₄, r₂₃.gpr _ (by decide), a2, BitVec.add_zero,
      bytesAt_unch (O₂.unch.trans O₃.unch) (all_app (all_one (Nat.le_trans (sl_top h9 (by decide)) (by decide)))
        (all_one (Nat.le_trans (sl_top h9 (by decide)) (by decide)))) (sp0 hed hfe), bk hed hfe]
  · refine (tc₆.of_unch h9 U₇ fun i hi => apart_nconsts _ ((by decide : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP],
      ∀ j ∈ [R2N, ONEN, EXPN], i ≠ j) i hi)).of_unch h9 U₈₁₀ fun i hi => ?_
    obtain ⟨h1, h2, h3⟩ := (by decide : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP],
      i < FLAG ∧ i ≠ RX ∧ i ≠ RY) i hi
    exact all_app (all_app (all_one (.inl (sl_le _ h1))) (all_one (sl_sep _ h2))) (all_one (sl_sep _ h3))
  · rw [sv₁₀ R2N (by decide) (by decide) (by decide), sv₈ R2N (by decide)]
    exact cs₇ (R2N, _) (List.Mem.head _)
  · rw [sv₁₀ ONEN (by decide) (by decide) (by decide), sv₈ ONEN (by decide)]
    exact cs₇ (ONEN, _) (List.Mem.tail _ (List.Mem.head _))
  · rw [sv₁₀ EXPN (by decide) (by decide) (by decide), sv₈ EXPN (by decide)]
    exact cs₇ (EXPN, _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  · rw [sv₁₀ BP (by decide) (by decide) (by decide), sv₈ BP (by decide),
      show sv Kt.c base s₇ BP = sv Kt.c base s₆ BP from sv_unch h9 U₇ BP (apart_nconsts _ (by decide))]
    exact Kt.toKit.const_at cs₆ 11
  · show wordsVal _ _ _ _ = _
    rw [O₁₀.wordsVal (.inl (sl_le _ (by decide))) (sl_64 h9 (by decide)), v₉,
      show wordsVal s₈.mem base (Kt.c.sl GX) Kt.c.n = sv Kt.c base s₈ GX from rfl, sv₈ GX (by decide),
      show sv Kt.c base s₇ GX = sv Kt.c base s₆ GX from sv_unch h9 U₇ GX (apart_nconsts _ (by decide))]
    exact Kt.toKit.const_at cs₆ 7
  · show wordsVal _ _ _ _ = _
    rw [v₁₀, O₉.wordsVal (.inl (sl_le _ (by decide))) (sl_64 h9 (by decide)),
      show wordsVal s₈.mem base (Kt.c.sl GY) Kt.c.n = sv Kt.c base s₈ GY from rfl, sv₈ GY (by decide),
      show sv Kt.c base s₇ GY = sv Kt.c base s₆ GY from sv_unch h9 U₇ GY (apart_nconsts _ (by decide))]
    exact Kt.toKit.const_at cs₆ 8
  · have mn₇ : sv Kt.c base s₇ MN = Kt.c.C.n := (sv_unch h9 U₇ MN (apart_nconsts _ (by decide))).trans tc₆.mn
    rw [(O₉.unch.trans O₁₀.unch).word (all_app (all_one (.inr (sl_le _ (by decide))))
        (all_one (.inr (sl_le _ (by decide))))) (flag_64 h1 h9), f₈,
      (U₆.trans U₇).word (all_app (flag_consts _) (flag_nconsts _)) (flag_64 h1 h9), fl₅, dv, mn₇, maskOf_and,
      maskOf_and]

/-! ## The values modulo `n` -/

/-- The slots `nback_ok` reads, with what they hold. -/
structure BackPre (base : Addr) (s : State) (k d e x : Nat) : Prop where
  ws : WsReg s base
  xv : sv Kt.c base s XO = x
  xlt : x < Kt.c.C.p
  zero : sv Kt.c base s ZERO = 0
  one : sv Kt.c base s ONE = 1
  kv : sv Kt.c base s K = k
  dv : sv Kt.c base s DD = d
  ev : sv Kt.c base s EE = e
  r2n : sv Kt.c base s R2N = 2 ^ (64 * Kt.c.n) * 2 ^ (64 * Kt.c.n) % Kt.c.C.n
  onen : sv Kt.c base s ONEN = 2 ^ (64 * Kt.c.n) % Kt.c.C.n

/-- `r = x mod n`, then `s = k^(n-2) (e + r d) mod n`. -/
theorem nback_ok {base : Addr} {s : State} {k d e x : Nat} (hb : Kt.BackPre base s k d e x) :
    WP isa (.seq (addCall Kt.FN (Kt.c.sl RR) (Kt.c.sl XO) (Kt.c.sl ZERO)) (Cfg.scalars Kt.c Kt.FN)) s
      fun s' => Kc s s' ∧ Unch base (backW Kt.c) s.mem s'.mem ∧
        sv Kt.c base s' RR = x % Kt.c.C.n ∧ sv Kt.c base s' SS < Kt.c.C.n ∧
        Fin.ofNat Kt.c.C.n (sv Kt.c base s' SS) = Fin.ofNat Kt.c.C.n k ^ (Kt.c.C.n - 2) *
          (Fin.ofNat Kt.c.C.n e + Fin.ofNat Kt.c.C.n (x % Kt.c.C.n) * Fin.ofNat Kt.c.C.n d) := by
  obtain h9 := Kt.n9
  obtain hk := Kt.FNk
  obtain hm := Kt.FNm
  obtain hF := Kt.order_ok
  obtain hU := Kt.unitN
  obtain hn0 : 0 < Kt.c.C.n := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain hl : ∀ {i : Nat}, i < 45 → Kt.c.sl i + 8 * Kt.c.n ≤ own Kt.c.n := fun hi => below_own h9 hi
  obtain hs : ∀ {i : Nat}, i ≤ 55 → Kt.c.sl i < 4095 := fun hi => sl_lt Kt.n1 h9 hi
  obtain kp : ∀ {i o : Nat}, i ≠ o → i < 45 →
      ∀ w ∈ cw Kt.c o, Kt.c.sl i + 8 * Kt.c.n ≤ w.1 ∨ w.1 + w.2 ≤ Kt.c.sl i := fun hio hi => cw_keep h9 hio hi
  have hw := hb.ws
  -- `r`.
  refine WP.seq (WP.mono (addCall_kit hF hk hm hw (o := Kt.c.sl RR) (a := Kt.c.sl XO) (b := Kt.c.sl ZERO)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv Kt.c base s XO + sv Kt.c base s ZERO < 2 * Kt.c.C.n
        rw [hb.xv, hb.zero]; have := hb.xlt; have hpn := Kt.pn
        omega_using [this, hpn]))
    fun s₁ ⟨C₁, v₁⟩ => ?_)
  obtain hw₁ := hw.of_kp C₁.kp
  have U₁ : Unch base (cw Kt.c RR) s.mem s₁.mem := C₁.mem
  obtain rr₁ : sv Kt.c base s₁ RR = x % Kt.c.C.n := by
    show wordsVal _ _ _ _ = _
    rw [v₁]; show (sv Kt.c base s XO + sv Kt.c base s ZERO) % Kt.c.C.n = _; rw [hb.xv, hb.zero, Nat.add_zero]
  rw [Cfg.scalars]
  simp only [progs]
  obtain nlt : ∀ y, y % Kt.c.C.n < Kt.c.C.n := fun y => Nat.mod_lt _ hn0
  -- `k R`.
  obtain r2₁ : sv Kt.c base s₁ R2N = 2 ^ (64 * Kt.c.n) * 2 ^ (64 * Kt.c.n) % Kt.c.C.n :=
    (sv_unch h9 U₁ R2N (kp (by decide) (by decide))).trans hb.r2n
  refine WP.seq (WP.mono (TKit.mulCall_kit hF hk hm hw₁ (o := Kt.c.sl KM) (a := Kt.c.sl K) (b := Kt.c.sl R2N)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv Kt.c base s₁ R2N < Kt.c.C.n; rw [r2₁]; exact nlt _)) fun s₂ ⟨C₂, lt₂, e₂⟩ => ?_)
  obtain hw₂ := hw₁.of_kp C₂.kp
  have U₂ : Unch base (cw Kt.c KM) s₁.mem s₂.mem := C₂.mem
  obtain km : toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₂ KM) = Fin.ofNat Kt.c.C.n k := by
    refine toM_r2 hU ?_
    rw [show sv Kt.c base s₂ KM * 2 ^ (64 * Kt.c.n) % Kt.c.C.n = _ from e₂]
    show sv Kt.c base s₁ K * sv Kt.c base s₁ R2N % Kt.c.C.n = _
    rw [r2₁, show sv Kt.c base s₁ K = sv Kt.c base s K from sv_unch h9 U₁ K (kp (by decide) (by decide)), hb.kv]
  -- `w = (k R)^(n-2)`.
  obtain on₂ : sv Kt.c base s₂ ONEN = 2 ^ (64 * Kt.c.n) % Kt.c.C.n := by
    show wordsVal _ _ _ _ = _
    rw [sv_unch h9 U₂ ONEN (kp (by decide) (by decide)), sv_unch h9 U₁ ONEN (kp (by decide) (by decide))]
    exact hb.onen
  refine WP.seq (WP.mono (TKit.chainPow_kit (P := Cfg.chainN Kt.c) hF hk hm (chainNLay Kt.c Kt.n1 h9) hU hw₂
    (one := Kt.c.sl ONEN) (hl (by decide)) (hs (by decide)) on₂ Kt.chainN_ok)
    fun s₃ ⟨K₃, U₃, lt₃, v₃⟩ => ?_)
  obtain hw₃ := hw₂.of_kc K₃
  obtain acc₃ : toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₃ ACC) = Fin.ofNat Kt.c.C.n k ^ (Kt.c.C.n - 2) := by
    have v : toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₃ ACC) =
        toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₂ KM) ^ (Kt.c.C.n - 2) := v₃
    rw [v, km]
  have acclt₃ : sv Kt.c base s₃ ACC < Kt.c.C.n := lt₃
  -- A slot the steps so far keep.
  obtain k13 : ∀ i ∈ [EE, DD, R2N, ONE, RR], sv Kt.c base s₃ i = sv Kt.c base s₁ i := fun i hi => by
    obtain ⟨h1, h2, h3⟩ := (by decide : ∀ i ∈ [EE, DD, R2N, ONE, RR], i < 45 ∧ i ≠ ACC ∧ i ≠ KM) i hi
    exact (sv_unch h9 U₃ i (chainN_keep h9 h1 h2) (le55 h1)).trans (sv_unch h9 U₂ i (kp h3 h1) (le55 h1))
  obtain r2₃ : sv Kt.c base s₃ R2N = 2 ^ (64 * Kt.c.n) * 2 ^ (64 * Kt.c.n) % Kt.c.C.n :=
    (k13 R2N (by decide)).trans r2₁
  -- `e R`.
  refine WP.seq (WP.mono (TKit.mulCall_kit hF hk hm hw₃ (o := Kt.c.sl EM) (a := Kt.c.sl EE) (b := Kt.c.sl R2N)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv Kt.c base s₃ R2N < Kt.c.C.n; rw [r2₃]; exact nlt _)) fun s₄ ⟨C₄, lt₄, e₄⟩ => ?_)
  obtain hw₄ := hw₃.of_kp C₄.kp
  have U₄ : Unch base (cw Kt.c EM) s₃.mem s₄.mem := C₄.mem
  obtain em : toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₄ EM) = Fin.ofNat Kt.c.C.n e := by
    refine toM_r2 hU ?_
    rw [show sv Kt.c base s₄ EM * 2 ^ (64 * Kt.c.n) % Kt.c.C.n = _ from e₄]
    show sv Kt.c base s₃ EE * sv Kt.c base s₃ R2N % Kt.c.C.n = _
    rw [r2₃, k13 EE (by decide),
      show sv Kt.c base s₁ EE = sv Kt.c base s EE from sv_unch h9 U₁ EE (kp (by decide) (by decide)), hb.ev]
  -- `r R`.
  obtain r2₄ : sv Kt.c base s₄ R2N = 2 ^ (64 * Kt.c.n) * 2 ^ (64 * Kt.c.n) % Kt.c.C.n :=
    (sv_unch h9 U₄ R2N (kp (by decide) (by decide))).trans r2₃
  refine WP.seq (WP.mono (TKit.mulCall_kit hF hk hm hw₄ (o := Kt.c.sl RM) (a := Kt.c.sl RR) (b := Kt.c.sl R2N)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv Kt.c base s₄ R2N < Kt.c.C.n; rw [r2₄]; exact nlt _)) fun s₅ ⟨C₅, lt₅, e₅⟩ => ?_)
  obtain hw₅ := hw₄.of_kp C₅.kp
  have U₅ : Unch base (cw Kt.c RM) s₄.mem s₅.mem := C₅.mem
  obtain rm : toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₅ RM) = Fin.ofNat Kt.c.C.n (x % Kt.c.C.n) := by
    refine toM_r2 hU ?_
    rw [show sv Kt.c base s₅ RM * 2 ^ (64 * Kt.c.n) % Kt.c.C.n = _ from e₅]
    show sv Kt.c base s₄ RR * sv Kt.c base s₄ R2N % Kt.c.C.n = _
    rw [r2₄, show sv Kt.c base s₄ RR = sv Kt.c base s₃ RR from sv_unch h9 U₄ RR (kp (by decide) (by decide)),
      k13 RR (by decide), rr₁]
  -- `d R`.
  obtain r2₅ : sv Kt.c base s₅ R2N = 2 ^ (64 * Kt.c.n) * 2 ^ (64 * Kt.c.n) % Kt.c.C.n :=
    (sv_unch h9 U₅ R2N (kp (by decide) (by decide))).trans r2₄
  refine WP.seq (WP.mono (TKit.mulCall_kit hF hk hm hw₅ (o := Kt.c.sl DM) (a := Kt.c.sl DD) (b := Kt.c.sl R2N)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv Kt.c base s₅ R2N < Kt.c.C.n; rw [r2₅]; exact nlt _)) fun s₆ ⟨C₆, lt₆, e₆⟩ => ?_)
  obtain hw₆ := hw₅.of_kp C₆.kp
  have U₆ : Unch base (cw Kt.c DM) s₅.mem s₆.mem := C₆.mem
  obtain dm : toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₆ DM) = Fin.ofNat Kt.c.C.n d := by
    refine toM_r2 hU ?_
    rw [show sv Kt.c base s₆ DM * 2 ^ (64 * Kt.c.n) % Kt.c.C.n = _ from e₆]
    show sv Kt.c base s₅ DD * sv Kt.c base s₅ R2N % Kt.c.C.n = _
    rw [r2₅, show sv Kt.c base s₅ DD = sv Kt.c base s₃ DD from
        (sv_unch h9 U₅ DD (kp (by decide) (by decide))).trans (sv_unch h9 U₄ DD (kp (by decide) (by decide))),
      k13 DD (by decide),
      show sv Kt.c base s₁ DD = sv Kt.c base s DD from sv_unch h9 U₁ DD (kp (by decide) (by decide)), hb.dv]
  -- `r d R`.
  refine WP.seq (WP.mono (TKit.mulCall_kit hF hk hm hw₆ (o := Kt.c.sl TT) (a := Kt.c.sl RM) (b := Kt.c.sl DM)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    lt₆) fun s₇ ⟨C₇, lt₇, e₇⟩ => ?_)
  obtain hw₇ := hw₆.of_kp C₇.kp
  have U₇ : Unch base (cw Kt.c TT) s₆.mem s₇.mem := C₇.mem
  obtain rm₆ : sv Kt.c base s₆ RM = sv Kt.c base s₅ RM := sv_unch h9 U₆ RM (kp (by decide) (by decide))
  obtain tt : toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₇ TT) =
      Fin.ofNat Kt.c.C.n (x % Kt.c.C.n) * Fin.ofNat Kt.c.C.n d := by
    rw [toM_mul hU e₇]
    show toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₆ RM) *
      toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₆ DM) = _
    rw [rm₆, rm, dm]
  -- `(e + r d) R`.
  obtain em₆ : sv Kt.c base s₆ EM = sv Kt.c base s₄ EM :=
    (sv_unch h9 U₆ EM (kp (by decide) (by decide))).trans (sv_unch h9 U₅ EM (kp (by decide) (by decide)))
  obtain em₇ : sv Kt.c base s₇ EM = sv Kt.c base s₄ EM :=
    (sv_unch h9 U₇ EM (kp (by decide) (by decide))).trans em₆
  refine WP.seq (WP.mono (addCall_kit hF hk hm hw₇ (o := Kt.c.sl SU) (a := Kt.c.sl EM) (b := Kt.c.sl TT)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by
      show sv Kt.c base s₇ EM + sv Kt.c base s₇ TT < 2 * Kt.c.C.n
      have l4 : sv Kt.c base s₄ EM < Kt.c.C.n := lt₄
      have l7 : sv Kt.c base s₇ TT < Kt.c.C.n := lt₇
      rw [em₇]; omega_using [l4, l7])) fun s₈ ⟨C₈, v₈⟩ => ?_)
  obtain hw₈ := hw₇.of_kp C₈.kp
  have U₈ : Unch base (cw Kt.c SU) s₇.mem s₈.mem := C₈.mem
  obtain su : toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₈ SU) =
      Fin.ofNat Kt.c.C.n e + Fin.ofNat Kt.c.C.n (x % Kt.c.C.n) * Fin.ofNat Kt.c.C.n d := by
    rw [show sv Kt.c base s₈ SU = _ from v₈, toM_add]
    show toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₇ EM) +
      toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₇ TT) = _
    rw [em₇, em, tt]
  obtain sult : sv Kt.c base s₈ SU < Kt.c.C.n := by rw [show sv Kt.c base s₈ SU = _ from v₈]; exact nlt _
  -- `w (e + r d) R`.
  refine WP.seq (WP.mono (TKit.mulCall_kit hF hk hm hw₈ (o := Kt.c.sl SMM) (a := Kt.c.sl ACC) (b := Kt.c.sl SU)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    sult) fun s₉ ⟨C₉, lt₉, e₉⟩ => ?_)
  obtain hw₉ := hw₈.of_kp C₉.kp
  have U₉ : Unch base (cw Kt.c SMM) s₈.mem s₉.mem := C₉.mem
  obtain acc₈ : sv Kt.c base s₈ ACC = sv Kt.c base s₃ ACC := by
    show wordsVal _ _ _ _ = wordsVal _ _ _ _
    rw [sv_unch h9 U₈ ACC (kp (by decide) (by decide)), sv_unch h9 U₇ ACC (kp (by decide) (by decide)),
      sv_unch h9 U₆ ACC (kp (by decide) (by decide)), sv_unch h9 U₅ ACC (kp (by decide) (by decide)),
      sv_unch h9 U₄ ACC (kp (by decide) (by decide))]
  obtain smm : toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₉ SMM) = Fin.ofNat Kt.c.C.n k ^ (Kt.c.C.n - 2) *
      (Fin.ofNat Kt.c.C.n e + Fin.ofNat Kt.c.C.n (x % Kt.c.C.n) * Fin.ofNat Kt.c.C.n d) := by
    rw [toM_mul hU e₉]
    show toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₈ ACC) *
      toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₈ SU) = _
    rw [acc₈, acc₃, su]
  -- `s`, out of Montgomery's form.
  obtain one₉ : sv Kt.c base s₉ ONE = 1 := by
    show wordsVal _ _ _ _ = _
    rw [sv_unch h9 U₉ ONE (kp (by decide) (by decide)), sv_unch h9 U₈ ONE (kp (by decide) (by decide)),
      sv_unch h9 U₇ ONE (kp (by decide) (by decide)), sv_unch h9 U₆ ONE (kp (by decide) (by decide)),
      sv_unch h9 U₅ ONE (kp (by decide) (by decide)), sv_unch h9 U₄ ONE (kp (by decide) (by decide))]
    show sv Kt.c base s₃ ONE = 1
    rw [k13 ONE (by decide)]
    show wordsVal _ _ _ _ = _
    rw [sv_unch h9 U₁ ONE (kp (by decide) (by decide))]
    exact hb.one
  refine WP.mono (TKit.mulCall_kit hF hk hm hw₉ (o := Kt.c.sl SS) (a := Kt.c.sl SMM) (b := Kt.c.sl ONE)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv Kt.c base s₉ ONE < Kt.c.C.n; rw [one₉]; have hp1 := Kt.p1; have hpn := Kt.pn; omega_using [hp1, hpn]))
    fun s₁₀ ⟨C₁₀, lt₁₀, e₁₀⟩ => ?_
  have U₁₀ : Unch base (cw Kt.c SS) s₉.mem s₁₀.mem := C₁₀.mem
  obtain ss : Fin.ofNat Kt.c.C.n (sv Kt.c base s₁₀ SS) = toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₉ SMM) := by
    refine toM_one_mul hU ?_
    rw [show sv Kt.c base s₁₀ SS * 2 ^ (64 * Kt.c.n) % Kt.c.C.n = _ from e₁₀]
    show sv Kt.c base s₉ SMM * sv Kt.c base s₉ ONE % Kt.c.C.n = _
    rw [one₉]
  refine ⟨C₁.kp.kc.trans (C₂.kp.kc.trans (K₃.trans (C₄.kp.kc.trans (C₅.kp.kc.trans (C₆.kp.kc.trans
    (C₇.kp.kc.trans (C₈.kp.kc.trans (C₉.kp.kc.trans C₁₀.kp.kc)))))))),
    ((((((((U₁.trans U₂).trans U₃).trans U₄).trans U₅).trans U₆).trans U₇).trans U₈).trans U₉).trans U₁₀, ?_,
    lt₁₀, by rw [ss, smm]⟩
  show wordsVal _ _ _ _ = _
  rw [sv_unch h9 U₁₀ RR (kp (by decide) (by decide)), sv_unch h9 U₉ RR (kp (by decide) (by decide)),
    sv_unch h9 U₈ RR (kp (by decide) (by decide)), sv_unch h9 U₇ RR (kp (by decide) (by decide)),
    sv_unch h9 U₆ RR (kp (by decide) (by decide)), sv_unch h9 U₅ RR (kp (by decide) (by decide)),
    sv_unch h9 U₄ RR (kp (by decide) (by decide))]
  show sv Kt.c base s₃ RR = _
  rw [k13 RR (by decide), rr₁]

/-! ## The end -/

/-- The checks of `r` and `s`, and `r ‖ s` to `out` under the flag's mask, the flag's low bit
returned: `Sign.Cfg.finish`, as the kit writes its numbers. -/
def finish : List Instr :=
  Cfg.nonzeroFlag Kt.c RR ++ Cfg.nonzeroFlag Kt.c SS ++ ldAt .a7 wb (Kt.c.sl FLAG) ++
    Kt.store (Kt.c.sl RR) .s2 0 ++ Kt.store (Kt.c.sl SS) .s2 Kt.L ++ retCode Kt.c

/-- `finish`: the masks of `r ≠ 0` and `s ≠ 0` into the flag, `r ‖ s` (or
zeros) to `out` under it, the flag's low bit to `a0`, and the saved
registers restored. -/
theorem finish_ok {s : State} {base out : Addr} (hw : WsReg s base) (h2 : s.gpr .s2 = out)
    (hfit : out.toNat + 2 * Kt.L ≤ 2 ^ 64)
    (hout : ∀ i < 2 * Kt.L, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hdis : (⟨out, 2 * Kt.L⟩ : Region).Disjoint ⟨base, 8192⟩)
    {b : Bool} (hF : word s.mem base (Kt.c.sl FLAG) = maskOf b) :
    WP isa (.block Kt.finish) s fun s' =>
      s'.gpr .a0 =
        (if (b && !decide (sv Kt.c base s RR = 0)) && !decide (sv Kt.c base s SS = 0) then 1 else 0) ∧
      bytesAt s'.mem out (2 * Kt.L) =
        toBytes Kt.L (if (b && !decide (sv Kt.c base s RR = 0)) && !decide (sv Kt.c base s SS = 0)
          then sv Kt.c base s RR else 0) ++
        toBytes Kt.L (if (b && !decide (sv Kt.c base s RR = 0)) && !decide (sv Kt.c base s SS = 0)
          then sv Kt.c base s SS else 0) ∧
      s'.gpr .s0 = word s.mem base 0 ∧ s'.gpr .s1 = word s.mem base 8 ∧ s'.gpr .s2 = word s.mem base 16 ∧
      s'.gpr .ra = word s.mem base 24 ∧ s'.gpr .s3 = word s.mem base 32 ∧
      (∀ r ∈ preserved, r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp := by
  obtain hL := Kt.Ln
  obtain h9 := Kt.n9
  obtain h1 := Kt.n1
  obtain hfl := sl_lo Kt.c FLAG
  rw [finish, retCode, restoreCode]
  simp only [List.append_assoc]
  -- The checks.
  refine WP.block_append (WP.mono (nzFlag_ok Kt.c h9 (i := RR) (by decide) hw) fun s₁ ⟨r₁, O₁, f₁⟩ => ?_)
  obtain hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono (nzFlag_ok Kt.c h9 (i := SS) (by decide) hw₁) fun s₂ ⟨r₂, O₂, f₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  refine ldAt_ws hw₂ (d := Kt.c.sl FLAG) (sl_lt h1 h9 (by decide)) (sl8 _ _) fun s₃ u₃ => ?_
  obtain hw₃ := hw₂.of_kp (Kp.of_upd u₃)
  obtain ss₁ : sv Kt.c base s₁ SS = sv Kt.c base s SS :=
    O₁.wordsVal (.inl (sl_le _ (by decide))) (sl_64 h9 (by decide))
  generalize hB : ((b && !decide (sv Kt.c base s RR = 0)) && !decide (sv Kt.c base s SS = 0)) = B
  obtain hb : word s₂.mem base (Kt.c.sl FLAG) = maskOf B := by
    rw [f₂, f₁, hF, ss₁, maskOf_and, maskOf_and, hB]
  obtain a₃ : s₃.gpr .a7 = maskOf B := by rw [u₃.gpr]; exact hb
  obtain wv₃ : ∀ i, i < FLAG → wordsVal s₃.mem base (Kt.c.sl i) Kt.c.n = sv Kt.c base s i := fun i hi => by
    rw [u₃.mem, O₂.wordsVal (.inl (sl_le _ hi)) (sl_64 h9 (le55 (Nat.lt_trans hi (by decide)))),
      O₁.wordsVal (.inl (sl_le _ hi)) (sl_64 h9 (le55 (Nat.lt_trans hi (by decide))))]
  obtain q₃ : s₃.gpr .s2 = out := by
    rw [u₃.other _ (by decide), r₂.gpr _ (by decide), r₁.gpr _ (by decide), h2]
  obtain wr₃ : s₃.wr = s.wr := by rw [u₃.wr, r₂.wr, r₁.wr]
  obtain sp' : ∀ {off k : Nat}, off + k ≤ 2 * Kt.L → ∀ i < k,
      ¬ (⟨base, 8192⟩ : Region).Contains (out + BitVec.ofNat 64 off + BitVec.ofNat 64 i) 1 :=
    fun hk => sep_at' hdis hfit hk
  -- `r` and `s` under the mask.
  refine WP.block_append (WP.mono (Kt.store_ok _ (i := RR) (q := .s2) (off := 0) hw₃ a₃ (by decide) (by decide)
    (by omega_using [hL, h9])
    (fun i hi => by rw [q₃, wr₃]; exact hout (0 + i) (by omega_using [hi]))
    (fun i hi => by rw [q₃]; exact out_of_disj hdis hfit (by omega_using [hi]))) fun s₄ ⟨r₄, m₄⟩ => ?_)
  obtain hw₄ := hw₃.of_rest r₄
  obtain q₄ : s₄.gpr .s2 = out := by rw [r₄.gpr _ (by decide), q₃]
  obtain a₄ : s₄.gpr .a7 = maskOf B := by rw [r₄.gpr _ (by decide), a₃]
  rw [q₃, wv₃ RR (by decide)] at m₄
  obtain U₄ : Unch base [(8192, 2 ^ 64)] s₃.mem s₄.mem := by
    rw [m₄]; exact writeBytes_unch _ fun i hi => sp' (off := 0) (k := Kt.L) (by omega_using []) i
      (by simpa [VG.Proof.Weierstrass.length_toBytes] using hi)
  refine WP.block_append (WP.mono (Kt.store_ok _ (i := SS) (q := .s2) (off := Kt.L) hw₄ a₄ (by decide) (by decide)
    (by omega_using [hL, h9])
    (fun i hi => by rw [q₄, r₄.wr, wr₃]; exact hout (Kt.L + i) (by omega_using [hi]))
    (fun i hi => by rw [q₄]; exact out_of_disj hdis hfit (by omega_using [hi]))) fun s₅ ⟨r₅, m₅⟩ => ?_)
  obtain hw₅ := hw₄.of_rest r₅
  obtain ss₄ : wordsVal s₄.mem base (Kt.c.sl SS) Kt.c.n = sv Kt.c base s SS := by
    rw [U₄.wordsVal (all_one (.inl (Nat.le_trans (sl_top h9 (by decide)) (by decide)))) (sl_64 h9 (by decide))]
    exact wv₃ SS (by decide)
  rw [q₄, ss₄] at m₅
  obtain U₅ : Unch base [(8192, 2 ^ 64)] s₄.mem s₅.mem := by
    rw [m₅]; exact writeBytes_unch _ fun i hi => sp' (off := Kt.L) (k := Kt.L) (by omega_using []) i
      (by simpa [VG.Proof.Weierstrass.length_toBytes] using hi)
  obtain wd : ∀ d, d + 8 ≤ 40 → word s₅.mem base d = word s.mem base d := fun d hd => by
    rw [U₅.word (all_one (.inl (show d + 8 ≤ 8192 by omega_using [hd]))) (by omega_using [hd]),
      U₄.word (all_one (.inl (show d + 8 ≤ 8192 by omega_using [hd]))) (by omega_using [hd]), u₃.mem,
      O₂.word (.inl (by omega_using [hd, hfl])) (by omega_using [hd]),
      O₁.word (.inl (by omega_using [hd, hfl])) (by omega_using [hd])]
  obtain fl₅ : word s₅.mem base (Kt.c.sl FLAG) = maskOf B := by
    rw [U₅.word (all_one (.inl (Nat.le_trans (flag_top h1 h9) (by decide)))) (flag_64 h1 h9),
      U₄.word (all_one (.inl (Nat.le_trans (flag_top h1 h9) (by decide)))) (flag_64 h1 h9), u₃.mem, hb]
  -- The bytes.
  obtain hX := VG.Proof.Weierstrass.length_toBytes Kt.L (if B = true then sv Kt.c base s RR else 0)
  obtain hY := VG.Proof.Weierstrass.length_toBytes Kt.L (if B = true then sv Kt.c base s SS else 0)
  obtain bytes₅ : bytesAt s₅.mem out (2 * Kt.L) =
      toBytes Kt.L (if B then sv Kt.c base s RR else 0) ++ toBytes Kt.L (if B then sv Kt.c base s SS else 0) := by
    obtain e1 := VG.WriteBytes.writeBytes_append s₃.mem out (toBytes Kt.L (if B then sv Kt.c base s RR else 0))
      (toBytes Kt.L (if B then sv Kt.c base s SS else 0)) (by rw [hX, hY]; omega_using [hL, h9])
    rw [hX] at e1
    rw [m₅, m₄, BitVec.add_zero, e1]
    have := bytesAt_writeBytes s₃.mem out
      (toBytes Kt.L (if B then sv Kt.c base s RR else 0) ++ toBytes Kt.L (if B then sv Kt.c base s SS else 0))
      (by simp only [List.length_append, hX, hY]; omega_using [hL, h9])
    simp only [List.length_append, hX, hY] at this
    rw [Nat.two_mul]
    exact this
  -- The return value and the restores.
  refine ldAt_ws hw₅ (d := Kt.c.sl FLAG) (sl_lt h1 h9 (by decide)) (sl8 _ _) fun s₉ u₉ => ?_
  refine WP.cons (exec_logicImm (by decide)) ?_
  obtain u₉' := Upd.write s₉ .a0 (s₉.gpr .a0 &&& BitVec.ofInt 64 1)
  obtain hw₉ := (hw₅.of_kp (Kp.of_upd u₉)).of_kp (Kp.of_upd u₉')
  refine ld_ws hw₉ (d := 24) (by decide) (by decide) fun t₁ v₁ => ?_
  obtain hv₁ := hw₉.of_kp (Kp.of_upd v₁)
  refine ld_ws hv₁ (d := 16) (by decide) (by decide) fun t₂ v₂ => ?_
  obtain hv₂ : WsReg t₂ base := ⟨by rw [v₂.other _ (by decide)]; exact hv₁.s0, by rw [v₂.wr]; exact hv₁.wr,
    hv₁.nowrap, hv₁.al⟩
  refine ld_ws hv₂ (d := 8) (by decide) (by decide) fun t₃ v₃ => ?_
  obtain hv₃ : WsReg t₃ base := ⟨by rw [v₃.other _ (by decide)]; exact hv₂.s0, by rw [v₃.wr]; exact hv₂.wr,
    hv₂.nowrap, hv₂.al⟩
  refine ld_ws hv₃ (d := 32) (by decide) (by decide) fun t₄ v₄ => ?_
  obtain hv₄ : WsReg t₄ base := ⟨by rw [v₄.other _ (by decide)]; exact hv₃.s0, by rw [v₄.wr]; exact hv₃.wr,
    hv₃.nowrap, hv₃.al⟩
  refine ld_ws hv₄ (d := 0) (by decide) (by decide) fun t₅ v₅ => WP.block_nil ?_
  obtain M₄ : t₄.mem = s₅.mem := by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem, u₉'.mem, u₉.mem]
  obtain np : ∀ r ∈ preserved, r ∉ [Reg.t0, .t1, .t3, .t4, .a7, .a0, .ra] := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide),
      v₁.other _ (by decide), u₉'.gpr, u₉.gpr, fl₅, and_one]
  · rw [v₅.mem, M₄]; exact bytes₅
  · rw [v₅.gpr, M₄, wd 0 (by decide)]
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, v₂.mem, v₁.mem, u₉'.mem, u₉.mem, wd 8 (by decide)]
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.mem, u₉'.mem, u₉.mem,
      wd 16 (by decide)]
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr,
      u₉'.mem, u₉.mem, wd 24 (by decide)]
  · rw [v₅.other _ (by decide), v₄.gpr, v₃.mem, v₂.mem, v₁.mem, u₉'.mem, u₉.mem, wd 32 (by decide)]
  · intro r hr h0 h1 h2' h3'
    obtain hn := np r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rw [v₅.other _ h0, v₄.other _ h3', v₃.other _ h1, v₂.other _ h2', v₁.other _ hn.2.2.2.2.2.2,
      u₉'.other _ hn.2.2.2.2.2.1, u₉.other _ hn.2.2.2.2.2.1, r₅.gpr _ (by simp [hn.1, hn.2.1]),
      r₄.gpr _ (by simp [hn.1, hn.2.1]), u₃.other _ hn.2.2.2.2.1,
      r₂.gpr _ (by simp [hn.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1]),
      r₁.gpr _ (by simp [hn.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1])]
  · rw [v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, u₉'.sp, u₉.sp, r₅.sp, r₄.sp, u₃.sp, r₂.sp, r₁.sp]

/-! ## The function -/

/-- The signature of `digest` with the private key at `d` and the secret
number at `k`, as the specification computes it. -/
abbrev sg (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith Kt.c.C (ofBytes (bytesAt m d Kt.L)) (hashToInt Kt.c.C (bytesAt m digest Kt.L))
    (ofBytes (bytesAt m k Kt.L))

/-- `vg_ecdsa_<curve>_sign(out = a0, d = a1, digest = a2, k = a3, scratch = a4)`, as the kit reads
and writes its numbers, with `tl` from `k`'s range to `x`. -/
def prog (tl : Prog isa) : Prog isa :=
  .seq (.block Kt.setup) (.seq tl
    (.seq (.seq (addCall Kt.FN (Kt.c.sl RR) (Kt.c.sl XO) (Kt.c.sl ZERO)) (Cfg.scalars Kt.c Kt.FN))
      (.block Kt.finish)))

/-- What `vg_ecdsa_<curve>_sign` returns. -/
def post (s s' : State) : Prop :=
  match Kt.sg s.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3) with
  | some rs => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) (2 * Kt.L) = Spec.Ecdsa.encode Kt.c.C rs
  | none => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) (2 * Kt.L) = List.replicate (2 * Kt.L) 0

/-- `vg_ecdsa_<curve>_sign` by register, with a `tl` that computes what ECDH's `tail` does from what
the setup leaves (which keeps the symbols' addresses, and memory outside the writable regions). -/
theorem sign_ok (hL : Law Kt.c.C) {tl : Prog isa} {s : State} (hs : Kt.Pre s)
    (htl : ∀ s₁, Kt.SetupS (s.gpr .a4) s s₁ → s₁.syms = s.syms → Frame s.wr s.mem s₁.mem →
      WP isa tl s₁ fun s' => TKit.TailPost Kt.c (s.gpr .a4) s₁ s') :
    WP isa (Kt.prog tl) s fun s' => abiPreserved s s' ∧ Kt.post s s' := by
  obtain h9 := Kt.n9
  obtain hLn := Kt.Ln
  obtain hU := Kt.unit
  obtain hwr := hs.wr
  obtain hod := hs.od
  obtain hfo := hs.fo
  rw [prog]
  refine WP.seq (wp_syms_frame (WP.mono (Kt.setup_ok hs) fun s₁ S sy₁ F₁ => ?_))
  obtain T := htl s₁ S sy₁ F₁
  generalize hb : s.gpr .a4 = base at S hwr hod T
  -- `k`'s range, `[k]G` and `x`.
  refine WP.seq (WP.mono T fun s₂ ⟨Kc₂, U₂, f₂, rep₂, xolt, xoeq, acclt, acceq⟩ => ?_)
  obtain hw₂ := S.ws.of_kc Kc₂
  obtain e₂ : ∀ i ∈ [ZERO, ONE, K, DD, EE, R2N, ONEN, EXPN], sv Kt.c base s₂ i = sv Kt.c base s₁ i := fun i hi =>
    sv_unch h9 U₂ i (tailW_keep Kt.c h9 i hi) ((by decide : ∀ i ∈ [ZERO, ONE, K, DD, EE, R2N, ONEN, EXPN], i ≤ 55) i hi)
  obtain hbk : Kt.BackPre base s₂ (ofBytes (bytesAt s.mem (s.gpr .a3) Kt.L))
      (ofBytes (bytesAt s.mem (s.gpr .a1) Kt.L)) (ofBytes (bytesAt s.mem (s.gpr .a2) Kt.L)) (sv Kt.c base s₂ XO) :=
    ⟨hw₂, rfl, xolt, (e₂ ZERO (by decide)).trans S.tc.zero, (e₂ ONE (by decide)).trans S.tc.one,
      (e₂ K (by decide)).trans S.k, (e₂ DD (by decide)).trans S.d, (e₂ EE (by decide)).trans S.e,
      (e₂ R2N (by decide)).trans S.r2n, (e₂ ONEN (by decide)).trans S.onen⟩
  -- `r` and `s`.
  refine WP.seq (WP.mono (Kt.nback_ok hbk) fun s₃ ⟨Kc₃, U₃, rr₃, sslt₃, ss₃⟩ => ?_)
  obtain hw₃ := hw₂.of_kc Kc₃
  obtain fl₃ : word s₃.mem base (Kt.c.sl FLAG) =
      maskOf (((((true && decide (ofBytes (bytesAt s.mem (s.gpr .a1) Kt.L) < Kt.c.C.n)) &&
        !decide (ofBytes (bytesAt s.mem (s.gpr .a1) Kt.L) = 0)) &&
        decide (ofBytes (bytesAt s.mem (s.gpr .a3) Kt.L) < Kt.c.C.n)) &&
        !decide (ofBytes (bytesAt s.mem (s.gpr .a3) Kt.L) = 0))) := by
    rw [U₃.word (backW_flag Kt.c Kt.n1 h9) (flag_64 Kt.n1 h9), f₂, S.flag, S.k, maskOf_and, maskOf_and]
  obtain h2₃ : s₃.gpr .s2 = s.gpr .a0 := by
    rw [Kc₃.gpr _ (by decide) (by decide), Kc₂.gpr _ (by decide) (by decide), S.s2]
  obtain wr₃ : s₃.wr = s.wr := by rw [Kc₃.wr, Kc₂.wr, S.wr]
  refine WP.mono (Kt.finish_ok hw₃ h2₃ hfo (fun i hi => by
      rw [wr₃, hwr]
      exact ⟨_, List.mem_cons_self .., Offset.contains_base (s.gpr .a0) (d := i) (n := 1) (k := 2 * Kt.L)
        (by omega_using [hi]) (by omega_using [hi, hLn, h9])⟩) hod fl₃)
    fun s' ⟨a0', bytes', s0', s1', s2', ra', s3', regs', sp'⟩ => ?_
  -- The registers.
  obtain U₂₃ := U₂.trans U₃
  obtain lo : ∀ w ∈ TKit.tailW Kt.c ++ backW Kt.c, 40 ≤ w.1 := all_app (TKit.tailW_lo Kt.c h9) (backW_lo Kt.c h9)
  refine ⟨⟨fun r hr => ?_, by rw [sp', Kc₃.sp, Kc₂.sp, S.sp], by rw [ra', lo_word U₂₃ lo (d := 24) (by decide), S.sv3]⟩,
    ?_⟩
  · by_cases h0 : r = .s0
    · subst h0; rw [s0', lo_word U₂₃ lo (d := 0) (by decide), S.sv0]
    by_cases h1 : r = .s1
    · subst h1; rw [s1', lo_word U₂₃ lo (d := 8) (by decide), S.sv1]
    by_cases h2' : r = .s2
    · subst h2'; rw [s2', lo_word U₂₃ lo (d := 16) (by decide), S.sv2]
    by_cases h3' : r = .s3
    · subst h3'; rw [s3', lo_word U₂₃ lo (d := 32) (by decide), S.sv4]
    rw [regs' r hr h0 h1 h2' h3', Kc₃.gpr r hr h1, Kc₂.gpr r hr h1, S.regs r h0 h2' h3' hr]
  -- The specification.
  rw [rr₃] at a0' bytes'
  generalize hD : ofBytes (bytesAt s.mem (s.gpr .a1) Kt.L) = D at a0' bytes' fl₃ ss₃ hbk
  generalize hKv : ofBytes (bytesAt s.mem (s.gpr .a3) Kt.L) = Kv at a0' bytes' fl₃ ss₃ hbk
  generalize hE : ofBytes (bytesAt s.mem (s.gpr .a2) Kt.L) = E at ss₃ hbk
  obtain hsg : Kt.sg s.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3) = Spec.Ecdsa.signWith Kt.c.C D E Kv := by
    rw [← hD, ← hE, ← hKv, sg, Kt.hash_eq]
  unfold post
  rw [hsg]
  obtain z64 : toBytes Kt.L 0 ++ toBytes Kt.L 0 = List.replicate (2 * Kt.L) 0 := by
    rw [toBytes_zero, List.replicate_append_replicate, Nat.two_mul]
  by_cases hk : 1 ≤ Kv ∧ Kv < Kt.c.C.n
  · have hk₁ : sv Kt.c base s₁ K = Kv := by rw [S.k, hKv]
    obtain ⟨hR, -, -, -⟩ := rep₂ (by rw [hk₁]; exact hk.1) (by rw [hk₁]; exact hk.2)
    obtain eG : Point.affine (toM Kt.c.C.p (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₁ RX))
        (toM Kt.c.C.p (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₁ RY)) = Spec.Weierstrass.G Kt.c.C := by
      rw [S.rx, S.ry, toM_mont hU, toM_mont hU]; rfl
    rw [eG, hk₁] at hR
    obtain hsig := VG.Proof.Ecdsa.signWith_eq hL (d := D) (e := E) hR xolt xoeq sslt₃ ss₃
    rw [hsig]
    obtain hkn : decide (Kv < Kt.c.C.n) = true := decide_eq_true hk.2
    obtain hk0 : decide (Kv = 0) = false := decide_eq_false (by omega_using [hk])
    rw [hkn, hk0] at a0' bytes'
    by_cases hc : 1 ≤ D ∧ D < Kt.c.C.n ∧ 1 ≤ Kv ∧ Kv < Kt.c.C.n ∧ sv Kt.c base s₂ XO % Kt.c.C.n ≠ 0 ∧
        sv Kt.c base s₃ SS ≠ 0
    · rw [ite_eq_left hc]
      obtain hB : ((((((true && decide (D < Kt.c.C.n)) && !decide (D = 0)) && true) && !false) &&
          !decide (sv Kt.c base s₂ XO % Kt.c.C.n = 0)) && !decide (sv Kt.c base s₃ SS = 0)) = true := by
        simp only [Bool.and_true, Bool.true_and, Bool.not_false, Bool.and_eq_true, Bool.not_eq_true',
          decide_eq_true_eq, decide_eq_false_iff_not]
        exact ⟨⟨⟨hc.2.1, by omega_using [hc]⟩, hc.2.2.2.2.1⟩, hc.2.2.2.2.2⟩
      rw [hB] at a0' bytes'
      exact ⟨by rw [a0']; rfl, by rw [bytes', Spec.Ecdsa.encode, Kt.len]; rfl⟩
    · rw [ite_eq_right hc]
      obtain hB : ((((((true && decide (D < Kt.c.C.n)) && !decide (D = 0)) && true) && !false) &&
          !decide (sv Kt.c base s₂ XO % Kt.c.C.n = 0)) && !decide (sv Kt.c base s₃ SS = 0)) = false := by
        rw [Bool.eq_false_iff]
        intro hB
        simp only [Bool.and_true, Bool.true_and, Bool.not_false, Bool.and_eq_true, Bool.not_eq_true',
          decide_eq_true_eq, decide_eq_false_iff_not] at hB
        exact hc ⟨by omega_using [hB], hB.1.1.1, hk.1, hk.2, hB.1.2, hB.2⟩
      rw [hB] at a0' bytes'
      exact ⟨by rw [a0']; rfl, bytes'.trans z64⟩
  · rw [signWith_none hk]
    obtain hB : ((((((true && decide (D < Kt.c.C.n)) && !decide (D = 0)) && decide (Kv < Kt.c.C.n)) &&
        !decide (Kv = 0)) && !decide (sv Kt.c base s₂ XO % Kt.c.C.n = 0)) &&
        !decide (sv Kt.c base s₃ SS = 0)) = false := by
      by_cases hn : Kv < Kt.c.C.n
      · have : Kv = 0 := by omega_using [hk, hn]
        simp [this]
      · simp [hn]
    rw [hB] at a0' bytes'
    exact ⟨by rw [a0']; rfl, bytes'.trans z64⟩

/-- `vg_ecdsa_<curve>_sign` by register, with `R = [k]G` by the curve's multiplication. -/
theorem signTail_ok (hL : Law Kt.c.C) {s : State} (hs : Kt.Pre s) :
    WP isa (Kt.prog (tail Kt.c Kt.mulN Kt.mulC)) s fun s' => abiPreserved s s' ∧ Kt.post s s' :=
  Kt.sign_ok hL hs fun s₁ S _ _ => by
    obtain hp0 : 0 < Kt.c.C.p := Nat.pos_of_ne_zero (NeZero.ne _)
    refine Kt.toKit.tail_ok hL S.ws S.s3 S.tc.mp S.tc.mn S.tc.zero S.tc.one S.tc.onep S.tc.ap S.tc.b3p S.tc.expp
      (by rw [S.rx]; exact Nat.mod_lt _ hp0) (by rw [S.ry]; exact Nat.mod_lt _ hp0) ?_
    rw [S.rx, S.ry, toM_mont Kt.unit, toM_mont Kt.unit]
    exact Kt.onG

end Kit

end VG.Proof.Ecdsa.RISCV64.SignAll
