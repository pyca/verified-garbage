module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.SignAll
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Verify
public import VerifiedGarbage.Spec.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdh.RISCV64.Masks
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.BytesLen

/-!
# ECDSA verification on RISC-V: correctness, for every curve

`vg_ecdsa_<curve>_verify` meets its contract by register, given the group law
(`Kit.verify_ok`), once for every curve whose numbers are whole bytes of the
order's bits: what the proof needs of a curve is its `Kit`, which is the
signature's (`SignAll.lean`: ECDH's kit and the functions modulo the order
`n`) and that a number of the signature's bytes is below `2 n`.

The proof is the setup (`vsetup_ok`: the saves, the public key's point and
first byte, the constants, `r`, `s` and `e`, and the ranges of `r` and `s`),
the check of the key (ECDH's `check_ok`), `u` and `v` (`uv_ok`),
`[u]G + [v]Q`, which `verify_ok` takes as a hypothesis, since a curve computes
it by its comb and windows or by a joint ladder, `x`, the comparison
(`compare_ok`) and the result (`vfinish_ok`); the specification's answer is
`verify_eq`'s (`Proof/Ecdsa/Verify.lean`). A comb's table is a property `T` of
states that the code before the multiplication keeps (`hTc`, `hTu`). Each
`<Curve>/Verify.lean` is the curve's kit, its contract, and its joint
multiplication as `verify_ok` takes it.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.VerifyAll

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Impl.Ecdsa.RISCV64.Sign VG.Impl.Ecdsa.RISCV64.Verify
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt hashToInt)
open VG.Proof.Ecdh.RISCV64 (TKit)
open VG.Proof.Ecdh.RISCV64.Kit (sv sl8 sl_lo sl_le sl_sep sl_top all_app all_one consts_nodup constCode_eq
  apart_consts flag_consts lo_consts maskOf_and not_mask and_one out_of_disj sep_at' bytesAt_unch
  lo_word own_ge wp_syms_frame cslots mem_cslots mask_eq valid_iff_of valid_on peer_bytes)
open VG.Proof.Ecdsa.RISCV64.SignAll (le55 sl_64 sl_lt flag_top flag_64 below_own flag_own all_cons sv_unch cw cw_keep
  cw_flag cw_lo chainNLay chainN_keep chainN_flag chainN_lo nconsts_nodup nconsts_le apart_nconsts flag_nconsts
  lo_nconsts addCall_kit nzFlag_ok)

/-- `∀ w ∈ W, P w` for ranges `W` given as a list of lists: `t` proves it of each. -/
local macro "ranges" t:tacticSeq : tactic =>
  `(tactic| ((repeat' first | with_reducible apply all_app | with_reducible apply all_one); all_goals ($t)))

/-- What follows code may assume it names the same addresses of statics as before. -/
theorem wp_syms {c : Prog isa} {s : State} {Q R : State → Prop} (h : WP isa c s Q)
    (k : ∀ s', Q s' → s'.syms = s.syms → R s') : WP isa c s R := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, k s' hq (Exec.syms he)⟩

/-- `subCall_ok`, for a field of `k` words modulo `p`. -/
theorem subCall_kit {F : Field} (hF : FieldOk F) {k p : Nat} (hk : F.S.k = k) (hm : F.S.m = p) {s : State}
    {base : Addr} (hw : WsReg s base) {o a b : Nat}
    (ho : o + 8 * k ≤ own k) (ha : a + 8 * k ≤ own k) (hb : b + 8 * k ≤ own k)
    (ho' : o < 4095) (ha' : a < 4095) (hb' : b < 4095)
    (hA : wordsVal s.mem base a k < p) (hB : wordsVal s.mem base b k < p) :
    WP isa (subCall F o a b) s fun s' => CallKeep k base o s s' ∧
      wordsVal s'.mem base o k = (wordsVal s.mem base a k + p - wordsVal s.mem base b k) % p := by
  subst hk hm; exact subCall_ok hF hw ho ha hb ho' ha' hb' hA hB

/-! ## What the steps write -/

theorem top_consts {c : Cfg} (h9 : c.n ≤ 9) : ∀ w ∈ (consts c).map (fun e => (c.sl e.1, 8 * c.n)), w.1 + w.2 ≤ 8192 :=
  fun w hw => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hw
    exact Nat.le_trans (sl_top h9 (TKit.consts_le c e he)) (by decide)

theorem top_nconsts {c : Cfg} (h9 : c.n ≤ 9) :
    ∀ w ∈ (Sign.Cfg.nConsts c).map (fun e => (c.sl e.1, 8 * c.n)), w.1 + w.2 ≤ 8192 := fun w hw => by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hw
  exact Nat.le_trans (sl_top h9 (nconsts_le c e he)) (by decide)

/-- What the peer's point's setup writes is in the working space. -/
theorem peerW_top {c : Cfg} (h1 : 1 ≤ c.n) (h9 : c.n ≤ 9) :
    ∀ w ∈ [(c.sl CX, 8 * c.n)] ++ [(c.sl CY, 8 * c.n)] ++ [(c.sl FLAG, 8)] ++
      (consts c).map (fun e => (c.sl e.1, 8 * c.n)), w.1 + w.2 ≤ 8192 := by
  ranges first
    | exact Nat.le_trans (sl_top h9 (by decide)) (by decide)
    | exact Nat.le_trans (flag_top h1 h9) (by decide)
    | exact top_consts h9

theorem peerW_lo (c : Cfg) :
    ∀ w ∈ [(c.sl CX, 8 * c.n)] ++ [(c.sl CY, 8 * c.n)] ++ [(c.sl FLAG, 8)] ++
      (consts c).map (fun e => (c.sl e.1, 8 * c.n)), 40 ≤ w.1 := by
  ranges first
    | exact Nat.le_trans (by decide) (sl_lo _ _)
    | exact lo_consts _

/-- What the setup writes after the key's point: `r`, `s`, `e` and the flag. -/
abbrev vsW (c : Cfg) : List (Nat × Nat) :=
  [(c.sl VR, 8 * c.n)] ++ [(c.sl VS, 8 * c.n)] ++ [(c.sl VE, 8 * c.n)] ++ [(c.sl FLAG, 8)] ++ [(c.sl FLAG, 8)]

theorem vsW_lo (c : Cfg) : ∀ w ∈ vsW c, 40 ≤ w.1 := by
  ranges exact Nat.le_trans (by decide) (sl_lo _ _)

/-- It keeps the other slots below the flag's. -/
theorem vsW_keep (c : Cfg) {i : Nat} (hi : i < FLAG) (h : i ≠ VR ∧ i ≠ VS ∧ i ≠ VE) :
    ∀ w ∈ vsW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  all_app (all_app (all_app (all_app (all_one (sl_sep _ h.1)) (all_one (sl_sep _ h.2.1))) (all_one (sl_sep _ h.2.2)))
    (all_one (.inl (sl_le _ hi)))) (all_one (.inl (sl_le _ hi)))

/-- The check of the key keeps the slots below the flag's that are not its own. -/
theorem checkKW_apart {c : Cfg} (h9 : c.n ≤ 9) {i : Nat} (hi : i < FLAG)
    (h : ∀ j ∈ [2, 37, 41, 42, 34, 35, 38, 43], i ≠ j) :
    ∀ w ∈ TKit.checkKW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  all_cons (sl_sep c (h 2 (by decide))) (all_cons (sl_sep c (h 37 (by decide)))
    (all_cons (sl_sep c (h 41 (by decide))) (all_cons (sl_sep c (h 42 (by decide)))
    (all_cons (.inl (below_own h9 (Nat.lt_trans hi (by decide)))) (all_cons (sl_sep c (h 34 (by decide)))
    (all_cons (sl_sep c (h 35 (by decide))) (all_cons (sl_sep c (h 38 (by decide)))
    (all_cons (sl_sep c (h 43 (by decide))) (all_cons (.inl (sl_le c hi))
    (all_one (.inl (Nat.le_trans (sl_top h9 (le55 (Nat.lt_trans hi (by decide)))) (by decide)))))))))))))

theorem cw_top {c : Cfg} (h9 : c.n ≤ 9) {o : Nat} (ho : o < 45) : ∀ w ∈ cw c o, w.1 + w.2 ≤ 8192 :=
  all_cons (Nat.le_trans (sl_top h9 (le55 ho)) (by decide))
    (all_one (own_add c.n (Nat.le_trans (Nat.le_add_left _ _) (below_own h9 ho))))

/-- What a power by a chain writes: its result, the table and the functions' own working space. -/
abbrev chW (c : Cfg) : List (Nat × Nat) := [(c.sl ACC, 8 * c.n), (c.sl TB, 9 * (8 * c.n)), (own c.n, 64 * c.n)]

theorem chainN_chW (c : Cfg) : chainWx (Sign.Cfg.chainN c) c.n = chW c := rfl

theorem chW_top {c : Cfg} (h1 : 1 ≤ c.n) (h9 : c.n ≤ 9) : ∀ w ∈ chW c, w.1 + w.2 ≤ 8192 :=
  all_cons (Nat.le_trans (sl_top h9 (by decide)) (by decide))
    (all_cons (Nat.le_trans (chainNLay c h1 h9).short.2.2 (by decide))
    (all_one (own_add c.n (Nat.le_trans (Nat.le_add_left _ _) (below_own h9 (i := ACC) (by decide))))))

/-- What `u` and `v` write. -/
abbrev uvW (c : Cfg) : List (Nat × Nat) :=
  cw c KM ++ chainWx (Sign.Cfg.chainN c) c.n ++ cw c EM ++ cw c UM ++ cw c UU ++ cw c RM ++ cw c VM ++ cw c VV

theorem uvW_keep {c : Cfg} (h9 : c.n ≤ 9) {i : Nat} (hi : i < 45)
    (h : ∀ j ∈ [KM, ACC, EM, UM, UU, RM, VM, VV], i ≠ j) :
    ∀ w ∈ uvW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  repeat' with_reducible apply all_app
  all_goals first | exact cw_keep h9 (h _ (by decide)) hi | exact chainN_keep h9 hi (h _ (by decide))

theorem uvW_flag (c : Cfg) (h1 : 1 ≤ c.n) (h9 : c.n ≤ 9) :
    ∀ w ∈ uvW c, c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := by
  repeat' with_reducible apply all_app
  all_goals first | exact cw_flag h9 (by decide) | exact chainN_flag h1 h9

theorem uvW_lo (c : Cfg) (h9 : c.n ≤ 9) : ∀ w ∈ uvW c, 40 ≤ w.1 := by
  repeat' with_reducible apply all_app
  all_goals first | exact cw_lo h9 _ | exact chainN_lo h9

theorem uvW_top (c : Cfg) (h1 : 1 ≤ c.n) (h9 : c.n ≤ 9) : ∀ w ∈ uvW c, w.1 + w.2 ≤ 8192 := by
  repeat' with_reducible apply all_app
  all_goals first | exact cw_top h9 (by decide) | (rw [chainN_chW]; exact chW_top h1 h9)

/-- What the coordinate `x` out of Montgomery's form writes. -/
abbrev affW (c : Cfg) : List (Nat × Nat) :=
  [(c.sl XM, 8 * c.n), (own c.n, 64 * c.n), (c.sl XO, 8 * c.n), (own c.n, 64 * c.n)]

theorem affW_keep {c : Cfg} (h9 : c.n ≤ 9) {i : Nat} (hi : i < 45) (h : i ≠ XM ∧ i ≠ XO) :
    ∀ w ∈ affW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  all_cons (sl_sep c h.1) (all_cons (.inl (below_own h9 hi)) (all_cons (sl_sep c h.2)
    (all_one (.inl (below_own h9 hi)))))

theorem affW_flag {c : Cfg} (h9 : c.n ≤ 9) : ∀ w ∈ affW c, c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG :=
  all_cons (.inr (sl_le c (by decide))) (all_cons (.inl (flag_own h9)) (all_cons (.inr (sl_le c (by decide)))
    (all_one (.inl (flag_own h9)))))

theorem own_lo {c : Cfg} (h9 : c.n ≤ 9) : 40 ≤ own c.n :=
  Nat.le_trans (Nat.le_trans (by decide) (sl_lo c FLAG)) (Nat.le_trans (Nat.le_add_right _ _) (flag_own h9))

theorem affW_lo {c : Cfg} (h9 : c.n ≤ 9) : ∀ w ∈ affW c, 40 ≤ w.1 :=
  all_cons (Nat.le_trans (by decide) (sl_lo c _)) (all_cons (own_lo h9) (all_cons (Nat.le_trans (by decide) (sl_lo c _))
    (all_one (own_lo h9))))

/-- What the comparison writes. -/
abbrev cmpW (c : Cfg) : List (Nat × Nat) := cw c XN ++ cw c RN ++ cw c WD

/-- What the proof needs of the ranges `W` that a joint multiplication writes: it keeps the saved
registers, the flag, the constants `tail` reads, and `r`. -/
structure JWOk (c : Cfg) (W : List (Nat × Nat)) : Prop where
  lo : ∀ w ∈ W, 40 ≤ w.1
  flag : ∀ w ∈ W, c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG
  consts : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP], ∀ w ∈ W, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i
  vr : ∀ w ∈ W, c.sl VR + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl VR

/-- A signature with `r` or `s` outside `[1, n-1]` does not verify. -/
theorem verify_false {C : Curve} {bs sig : List Byte} {e : Nat}
    (h : ¬ (1 ≤ ofBytes (sig.take C.len) ∧ ofBytes (sig.take C.len) < C.n ∧
      1 ≤ ofBytes (sig.drop C.len) ∧ ofBytes (sig.drop C.len) < C.n)) :
    Spec.Ecdsa.verify C bs e sig = false := by
  unfold Spec.Ecdsa.verify
  split
  · unfold Spec.Ecdsa.verifyWith
    rw [ite_eq_right_iff.mpr]
    intro h'; exact absurd h' h
  · rfl

/-! ## The kit -/

/-- What the proof needs of a curve, beside the signature's kit. -/
structure Kit extends toSKit : VG.Proof.Ecdsa.RISCV64.SignAll.Kit where
  /-- A number of the signature's bytes is below `2 n`: `r mod n` is one subtraction. -/
  n2 : 256 ^ L ≤ 2 * c.C.n

namespace Kit

variable (Kt : Kit)

/-! ## The setup -/

/-- What the contract gives, by register: the public key, the digest and the signature are readable,
the working space writable. -/
structure VPre (s : State) : Prop where
  pk : (⟨s.gpr .a0, 1 + 2 * Kt.L⟩ : Region) ∈ s.rd
  dg : (⟨s.gpr .a1, Kt.L⟩ : Region) ∈ s.rd
  sig : (⟨s.gpr .a2, 2 * Kt.L⟩ : Region) ∈ s.rd
  wr : s.wr = [⟨s.gpr .a3, 8192⟩]
  pd : (⟨s.gpr .a0, 1 + 2 * Kt.L⟩ : Region).Disjoint ⟨s.gpr .a3, 8192⟩
  dd : (⟨s.gpr .a1, Kt.L⟩ : Region).Disjoint ⟨s.gpr .a3, 8192⟩
  sd : (⟨s.gpr .a2, 2 * Kt.L⟩ : Region).Disjoint ⟨s.gpr .a3, 8192⟩
  fp : (s.gpr .a0).toNat + (1 + 2 * Kt.L) ≤ 2 ^ 64
  fd : (s.gpr .a1).toNat + Kt.L ≤ 2 ^ 64
  fg : (s.gpr .a2).toNat + 2 * Kt.L ≤ 2 ^ 64
  fs : (s.gpr .a3).toNat + 8192 ≤ 2 ^ 64
  al : (s.gpr .a3).toNat % 8 = 0

/-- What the setup leaves, from `s`, with `base` the working space. -/
structure VSetup (base : Addr) (s s' : State) : Prop where
  ws : WsReg s' base
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
  x : sv Kt.c base s' CX = ofBytes (bytesAt s.mem (s.gpr .a0 + BitVec.ofNat 64 1) Kt.L)
  y : sv Kt.c base s' CY = ofBytes (bytesAt s.mem (s.gpr .a0 + BitVec.ofNat 64 (1 + Kt.L)) Kt.L)
  rv : sv Kt.c base s' VR = ofBytes (bytesAt s.mem (s.gpr .a2) Kt.L)
  svs : sv Kt.c base s' VS = ofBytes (bytesAt s.mem (s.gpr .a2 + BitVec.ofNat 64 Kt.L) Kt.L)
  ev : sv Kt.c base s' VE = ofBytes (bytesAt s.mem (s.gpr .a1) Kt.L)
  flag : word s'.mem base (Kt.c.sl FLAG) = maskOf ((((decide (s.mem (s.gpr .a0) = 4) &&
    decide (ofBytes (bytesAt s.mem (s.gpr .a2) Kt.L) < Kt.c.C.n)) &&
    !decide (ofBytes (bytesAt s.mem (s.gpr .a2) Kt.L) = 0)) &&
    decide (ofBytes (bytesAt s.mem (s.gpr .a2 + BitVec.ofNat 64 Kt.L) Kt.L) < Kt.c.C.n)) &&
    !decide (ofBytes (bytesAt s.mem (s.gpr .a2 + BitVec.ofNat 64 Kt.L) Kt.L) = 0))
  consts : ∀ e ∈ consts Kt.c, sv Kt.c base s' e.1 = e.2

/-- The setup keeps the constants. -/
theorem consts_apart (c : Cfg) : ∀ e ∈ consts c, ∀ w ∈ vsW c, c.sl e.1 + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl e.1 :=
  fun e he => by
    obtain ⟨h1, h2⟩ := (by decide : ∀ i ∈ cslots, i < FLAG ∧ i ≠ VR ∧ i ≠ VS ∧ i ≠ VE) _ (mem_cslots he)
    exact vsW_keep c h1 h2

/-- The saves, the public key's point and the flag, the constants, `r`, `s` and `e`, and the masks of
`r` and `s` in `[1, n-1]`: `Verify.Cfg.setup`, as the kit reads its numbers. -/
def vsetup : List Instr :=
  saveCode .a3 ++ Kt.load (Kt.c.sl CX) .a0 1 ++ Kt.load (Kt.c.sl CY) .a0 (1 + Kt.L) ++
    leadMask .a0 ++ sdAt .a7 wb (Kt.c.sl FLAG) ++ constCode Kt.c ++
    Kt.load (Kt.c.sl VR) .a2 0 ++ Kt.load (Kt.c.sl VS) .a2 Kt.L ++ Kt.load (Kt.c.sl VE) .a1 0 ++
    rangeOf Kt.c VR ++ rangeOf Kt.c VS

/-- `vsetup`. -/
theorem vsetup_ok {s : State} (hs : Kt.VPre s) : WP isa (.block Kt.vsetup) s (Kt.VSetup (s.gpr .a3) s) := by
  obtain ⟨hrdp, hrdd, hrds, hwr, hpd, hdd, hsd, hfp, hfd, hfg, hfs, hal⟩ := hs
  obtain hL := Kt.Ln
  obtain h9 := Kt.n9
  obtain h1 := Kt.toSKit.n1
  generalize hb : s.gpr .a3 = base at hwr hpd hdd hsd hfs hal
  obtain hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  rw [vsetup]
  obtain e1 : ∀ (A B C D E F G H I J K : List Instr), A ++ B ++ C ++ D ++ E ++ F ++ G ++ H ++ I ++ J ++ K =
      A ++ ((B ++ C ++ D ++ E ++ F) ++ (G ++ (H ++ (I ++ (J ++ K))))) := by intros; simp only [List.append_assoc]
  rw [e1]
  refine WP.block_append (WP.mono (TKit.save_ok hb hwr' hfs hal)
    fun s₁ ⟨hw₁, h3₁, o₁, g₁, rd₁, wr₁, sp₁, U₁, w0, w1, w2, w3, w4⟩ => ?_)
  obtain a0 : s₁.gpr .a0 = s.gpr .a0 := g₁ _ (by decide) (by decide) (by decide)
  obtain a1 : s₁.gpr .a1 = s.gpr .a1 := g₁ _ (by decide) (by decide) (by decide)
  obtain a2 : s₁.gpr .a2 = s.gpr .a2 := g₁ _ (by decide) (by decide) (by decide)
  obtain rdp : (⟨s.gpr .a0, 1 + 2 * Kt.L⟩ : Region) ∈ s.rd ++ s.wr := List.mem_append_left _ hrdp
  obtain rdd : (⟨s.gpr .a1, Kt.L⟩ : Region) ∈ s.rd ++ s.wr := List.mem_append_left _ hrdd
  obtain rds : (⟨s.gpr .a2, 2 * Kt.L⟩ : Region) ∈ s.rd ++ s.wr := List.mem_append_left _ hrds
  -- The key's point, its first byte and the constants.
  refine WP.block_append (WP.mono (Kt.toSKit.toKit.peerLoad_ok hw₁ (q := .a0) (by decide) (by rw [a0, rd₁, wr₁]; exact rdp)
    (by rw [a0]; exact hpd) (by rw [a0]; exact hfp)) fun s₂ ⟨hw₂, r₂, U₂, x₂, y₂, f₂, c₂⟩ => ?_)
  obtain g₂ : ∀ r ∈ [Reg.a1, .a2], s₂.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [r₂.gpr _ (by decide), a1]
    · rw [r₂.gpr _ (by decide), a2]
  -- `r`, `s` and `e`.
  refine WP.block_append (WP.mono (Kt.load_ok (i := VR) (p := .a2) (off := 0) (R := 2 * Kt.L) hw₂ (by decide)
    (by decide) (by omega_using []) (by omega_using [hL, h9])
    (by rw [g₂ .a2 (by simp), r₂.rd, r₂.wr, rd₁, wr₁]; exact rds)
    (fun i hi => by rw [g₂ .a2 (by simp)]; exact out_of_disj hsd hfg (by omega_using [hi])))
    fun s₃ ⟨r₃, O₃, e₃⟩ => ?_)
  obtain hw₃ := hw₂.of_rest r₃
  refine WP.block_append (WP.mono (Kt.load_ok (i := VS) (p := .a2) (off := Kt.L) (R := 2 * Kt.L) hw₃ (by decide)
    (by decide) (by omega_using []) (by omega_using [hL, h9])
    (by rw [r₃.gpr _ (by decide), g₂ .a2 (by simp), r₃.rd, r₃.wr, r₂.rd, r₂.wr, rd₁, wr₁]; exact rds)
    (fun i hi => by rw [r₃.gpr _ (by decide), g₂ .a2 (by simp)]; exact out_of_disj hsd hfg (by omega_using [hi])))
    fun s₄ ⟨r₄, O₄, e₄⟩ => ?_)
  obtain hw₄ := hw₃.of_rest r₄
  obtain r₃₄ := r₃.trans r₄
  refine WP.block_append (WP.mono (Kt.load_ok (i := VE) (p := .a1) (off := 0) (R := Kt.L) hw₄ (by decide)
    (by decide) (by omega_using []) (by omega_using [hL, h9])
    (by rw [r₃₄.gpr _ (by decide), g₂ .a1 (by simp), r₃₄.rd, r₃₄.wr, r₂.rd, r₂.wr, rd₁, wr₁]; exact rdd)
    (fun i hi => by rw [r₃₄.gpr _ (by decide), g₂ .a1 (by simp)]; exact out_of_disj hdd hfd (by omega_using [hi])))
    fun s₅ ⟨r₅, O₅, e₅⟩ => ?_)
  obtain hw₅ := hw₄.of_rest r₅
  -- The ranges.
  refine WP.block_append (WP.mono (TKit.rangeOf_ok Kt.c h9 (i := VR) (by decide) hw₅) fun s₆ ⟨K₆, O₆, f₆⟩ => ?_)
  obtain hw₆ := hw₅.of_kp K₆
  refine WP.mono (TKit.rangeOf_ok Kt.c h9 (i := VS) (by decide) hw₆) fun s₇ ⟨K₇, O₇, f₇⟩ => ?_
  obtain hw₇ := hw₆.of_kp K₇
  -- What each step leaves.
  obtain U₃₇ : Unch base (vsW Kt.c) s₂.mem s₇.mem :=
    (((O₃.unch.trans O₄.unch).trans O₅.unch).trans O₆.unch).trans O₇.unch
  obtain U₂₇ := U₂.trans U₃₇
  obtain lo := all_app (peerW_lo Kt.c) (vsW_lo Kt.c)
  obtain pt := peerW_top (c := Kt.c) h1 h9
  obtain sp' : ∀ {q : Reg} {n : Nat}, (⟨s.gpr q, n⟩ : Region).Disjoint ⟨base, 8192⟩ → (s.gpr q).toNat + n ≤ 2 ^ 64 →
      ∀ {off k : Nat}, off + k ≤ n → ∀ i < k,
        ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr q + BitVec.ofNat 64 off + BitVec.ofNat 64 i) 1 :=
    fun hd hf _ _ hk => sep_at' hd hf hk
  obtain sp0 : ∀ {q : Reg} {n : Nat}, (⟨s.gpr q, n⟩ : Region).Disjoint ⟨base, 8192⟩ → (s.gpr q).toNat + n ≤ 2 ^ 64 →
      ∀ i < n, ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr q + BitVec.ofNat 64 i) 1 := fun hd hf i hi => by
    simpa using sep_at' hd hf (off := 0) (k := _) (by omega_using []) i hi
  obtain K₁₇ : ∀ r ∈ preserved, s₇.gpr r = s₁.gpr r := fun r hr => by
    obtain h1 : r ∉ [Reg.t0, .t1] := fun h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> exact absurd hr (by decide)
    obtain h2 : r ∉ [Reg.t0, .t1, .a7] := fun h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> exact absurd hr (by decide)
    rw [K₇.gpr _ hr, K₆.gpr _ hr, r₅.gpr _ h1, r₄.gpr _ h1, r₃.gpr _ h1, r₂.gpr _ h2]
  obtain sv₅ : ∀ i, i < FLAG → sv Kt.c base s₇ i = sv Kt.c base s₅ i := fun i hi => by
    show wordsVal _ _ _ _ = _
    rw [O₇.wordsVal (.inl (sl_le _ hi)) (sl_64 h9 (le55 (Nat.lt_trans hi (by decide)))),
      O₆.wordsVal (.inl (sl_le _ hi)) (sl_64 h9 (le55 (Nat.lt_trans hi (by decide))))]
  obtain sr : ∀ i < Kt.L, ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr .a2 + BitVec.ofNat 64 i) 1 := fun i hi => by
    simpa using sp' hsd hfg (off := 0) (k := Kt.L) (by omega_using []) i hi
  obtain r₅' : sv Kt.c base s₅ VR = ofBytes (bytesAt s.mem (s.gpr .a2) Kt.L) := by
    show wordsVal _ _ _ _ = _
    rw [O₅.wordsVal (.inl (sl_le _ (by decide))) (sl_64 h9 (by decide)),
      O₄.wordsVal (.inl (sl_le _ (by decide))) (sl_64 h9 (by decide)), e₃,
      r₂.gpr _ (by decide), a2, BitVec.add_zero, bytesAt_unch U₂ pt sr, bytesAt_unch U₁ (by decide) sr]
  obtain s₅' : sv Kt.c base s₅ VS = ofBytes (bytesAt s.mem (s.gpr .a2 + BitVec.ofNat 64 Kt.L) Kt.L) := by
    show wordsVal _ _ _ _ = _
    rw [O₅.wordsVal (.inl (sl_le _ (by decide))) (sl_64 h9 (by decide)), e₄, r₃.gpr _ (by decide),
      r₂.gpr _ (by decide), a2,
      bytesAt_unch (U₂.trans O₃.unch) (all_app pt (all_one (Nat.le_trans (sl_top h9 (by decide)) (by decide))))
        (sp' hsd hfg (off := Kt.L) (k := Kt.L) (by omega_using [])),
      bytesAt_unch U₁ (by decide) (sp' hsd hfg (off := Kt.L) (k := Kt.L) (by omega_using []))]
  obtain mn₅ : sv Kt.c base s₅ MN = Kt.c.C.n := by
    show wordsVal _ _ _ _ = _
    rw [O₅.wordsVal (sl_sep _ (by decide)) (sl_64 h9 (by decide)),
      O₄.wordsVal (sl_sep _ (by decide)) (sl_64 h9 (by decide)),
      O₃.wordsVal (sl_sep _ (by decide)) (sl_64 h9 (by decide))]
    exact Kt.toSKit.toKit.const_at c₂ 1
  refine ⟨hw₇, by rw [K₁₇ _ (by decide), h3₁], fun x h0 h2 h3 hx => by rw [K₁₇ x hx, g₁ x h0 h2 h3], ?_, ?_, ?_,
    by rw [lo_word U₂₇ lo (d := 0) (by decide), w0], by rw [lo_word U₂₇ lo (d := 8) (by decide), w1],
    by rw [lo_word U₂₇ lo (d := 16) (by decide), w2], by rw [lo_word U₂₇ lo (d := 24) (by decide), w3],
    by rw [lo_word U₂₇ lo (d := 32) (by decide), w4], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [K₇.rd, K₆.rd, r₅.rd, r₄.rd, r₃.rd, r₂.rd, rd₁]
  · rw [K₇.wr, K₆.wr, r₅.wr, r₄.wr, r₃.wr, r₂.wr, wr₁]
  · rw [K₇.sp, K₆.sp, r₅.sp, r₄.sp, r₃.sp, r₂.sp, sp₁]
  · show wordsVal _ _ _ _ = _
    rw [sv_unch h9 U₃₇ CX (vsW_keep _ (by decide) (by decide))]
    show sv Kt.c base s₂ CX = _
    rw [x₂, a0, bytesAt_unch U₁ (by decide) (sp' hpd hfp (off := 1) (k := Kt.L) (by omega_using []))]
  · show wordsVal _ _ _ _ = _
    rw [sv_unch h9 U₃₇ CY (vsW_keep _ (by decide) (by decide))]
    show sv Kt.c base s₂ CY = _
    rw [y₂, a0, bytesAt_unch U₁ (by decide) (sp' hpd hfp (off := 1 + Kt.L) (k := Kt.L) (by omega_using []))]
  · rw [sv₅ VR (by decide)]; exact r₅'
  · rw [sv₅ VS (by decide)]; exact s₅'
  · rw [sv₅ VE (by decide)]
    show wordsVal _ _ _ _ = _
    rw [e₅, r₃₄.gpr _ (by decide), g₂ .a1 (by simp), BitVec.add_zero,
      bytesAt_unch ((U₂.trans O₃.unch).trans O₄.unch) (all_app (all_app pt
        (all_one (Nat.le_trans (sl_top h9 (by decide)) (by decide))))
        (all_one (Nat.le_trans (sl_top h9 (by decide)) (by decide)))) (sp0 hdd hfd),
      bytesAt_unch U₁ (by decide) (sp0 hdd hfd)]
  · have h1' := bytesAt_unch U₁ (q := s.gpr .a0) (n := 1) (by decide)
      (by simpa using sp' hpd hfp (off := 0) (k := 1) (by omega_using []))
    simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, List.cons.injEq, and_true,
      BitVec.add_zero] at h1'
    obtain sv₆ : sv Kt.c base s₆ VS = sv Kt.c base s₅ VS := by
      show wordsVal _ _ _ _ = _
      rw [O₆.wordsVal (.inl (sl_le _ (by decide))) (sl_64 h9 (by decide))]
    obtain mn₆ : sv Kt.c base s₆ MN = Kt.c.C.n := by
      show wordsVal _ _ _ _ = _
      rw [O₆.wordsVal (.inl (sl_le _ (by decide))) (sl_64 h9 (by decide))]; exact mn₅
    rw [f₇, f₆, (O₃.unch.trans O₄.unch).trans O₅.unch |>.word (all_app (all_app
        (all_one (.inr (sl_le _ (by decide)))) (all_one (.inr (sl_le _ (by decide)))))
        (all_one (.inr (sl_le _ (by decide))))) (flag_64 h1 h9), f₂, a0, h1', r₅', mn₅,
      sv₆, s₅', mn₆, maskOf_and, maskOf_and, maskOf_and, maskOf_and]
  · intro e he
    show wordsVal _ _ _ _ = _
    rw [sv_unch h9 U₃₇ e.1 (consts_apart Kt.c e he) (TKit.consts_le Kt.c e he)]
    exact c₂ e he

/-! ## `u` and `v` -/

/-- The slots `uv` reads, with what they hold. -/
structure UvPre (base : Addr) (s : State) (r sg e : Nat) : Prop where
  ws : WsReg s base
  one : sv Kt.c base s ONE = 1
  rv : sv Kt.c base s VR = r
  sv' : sv Kt.c base s VS = sg
  ev : sv Kt.c base s VE = e
  r2n : sv Kt.c base s R2N = 2 ^ (64 * Kt.c.n) * 2 ^ (64 * Kt.c.n) % Kt.c.C.n
  onen : sv Kt.c base s ONEN = 2 ^ (64 * Kt.c.n) % Kt.c.C.n

/-- `w = (s R)^(n-2)`, `u = e w` and `v = r w` modulo `n`. -/
theorem uv_ok {base : Addr} {s : State} {r sg e : Nat} (hb : Kt.UvPre base s r sg e) :
    WP isa (Verify.Cfg.uv Kt.c Kt.FN) s fun s' => Kc s s' ∧ Unch base (uvW Kt.c) s.mem s'.mem ∧
      sv Kt.c base s' UU < Kt.c.C.n ∧
      Fin.ofNat Kt.c.C.n (sv Kt.c base s' UU) = Fin.ofNat Kt.c.C.n e * Fin.ofNat Kt.c.C.n sg ^ (Kt.c.C.n - 2) ∧
      sv Kt.c base s' VV < Kt.c.C.n ∧
      Fin.ofNat Kt.c.C.n (sv Kt.c base s' VV) = Fin.ofNat Kt.c.C.n r * Fin.ofNat Kt.c.C.n sg ^ (Kt.c.C.n - 2) := by
  obtain h9 := Kt.n9
  obtain hk := Kt.FNk
  obtain hm := Kt.FNm
  obtain hF := Kt.order_ok
  obtain hU := Kt.toSKit.unitN
  obtain hn0 : 0 < Kt.c.C.n := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain hn1 : 1 < Kt.c.C.n := by have hp1 := Kt.p1; have hpn := Kt.pn; omega_using [hp1, hpn]
  obtain hl : ∀ {i : Nat}, i < 45 → Kt.c.sl i + 8 * Kt.c.n ≤ own Kt.c.n := fun hi => below_own h9 hi
  obtain hs : ∀ {i : Nat}, i ≤ 55 → Kt.c.sl i < 4095 := fun hi => sl_lt Kt.toSKit.n1 h9 hi
  obtain kp : ∀ {i o : Nat}, i ≠ o → i < 45 →
      ∀ w ∈ cw Kt.c o, Kt.c.sl i + 8 * Kt.c.n ≤ w.1 ∨ w.1 + w.2 ≤ Kt.c.sl i := fun hio hi => cw_keep h9 hio hi
  obtain nlt : ∀ y, y % Kt.c.C.n < Kt.c.C.n := fun y => Nat.mod_lt _ hn0
  have hw := hb.ws
  rw [Verify.Cfg.uv]
  simp only [progs]
  -- `s R`.
  refine WP.seq (WP.mono (TKit.mulCall_kit hF hk hm hw (o := Kt.c.sl KM) (a := Kt.c.sl VS) (b := Kt.c.sl R2N)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv Kt.c base s R2N < Kt.c.C.n; rw [hb.r2n]; exact nlt _)) fun s₂ ⟨C₂, lt₂, e₂⟩ => ?_)
  obtain hw₂ := hw.of_kp C₂.kp
  have U₂ : Unch base (cw Kt.c KM) s.mem s₂.mem := C₂.mem
  obtain km : toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₂ KM) = Fin.ofNat Kt.c.C.n sg := by
    refine toM_r2 hU ?_
    rw [show sv Kt.c base s₂ KM * 2 ^ (64 * Kt.c.n) % Kt.c.C.n = _ from e₂]
    show sv Kt.c base s VS * sv Kt.c base s R2N % Kt.c.C.n = _
    rw [hb.r2n, hb.sv']
  -- `w`.
  obtain on₂ : sv Kt.c base s₂ ONEN = 2 ^ (64 * Kt.c.n) % Kt.c.C.n := by
    show wordsVal _ _ _ _ = _; rw [sv_unch h9 U₂ ONEN (kp (by decide) (by decide))]; exact hb.onen
  refine WP.seq (WP.mono (TKit.chainPow_kit (P := Sign.Cfg.chainN Kt.c) hF hk hm (chainNLay Kt.c Kt.toSKit.n1 h9) hU hw₂
    (one := Kt.c.sl ONEN) (hl (by decide)) (hs (by decide)) on₂ Kt.chainN_ok)
    fun s₃ ⟨K₃, U₃, lt₃, v₃⟩ => ?_)
  obtain hw₃ := hw₂.of_kc K₃
  obtain acc₃ : toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₃ ACC) = Fin.ofNat Kt.c.C.n sg ^ (Kt.c.C.n - 2) := by
    have v : toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₃ ACC) =
        toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₂ KM) ^ (Kt.c.C.n - 2) := v₃
    rw [v, km]
  have acclt₃ : sv Kt.c base s₃ ACC < Kt.c.C.n := lt₃
  obtain k13 : ∀ i ∈ [VE, VR, R2N, ONE], sv Kt.c base s₃ i = sv Kt.c base s i := fun i hi => by
    obtain ⟨h1, h2, h3⟩ := (by decide : ∀ i ∈ [VE, VR, R2N, ONE], i < 45 ∧ i ≠ ACC ∧ i ≠ KM) i hi
    exact (sv_unch h9 U₃ i (chainN_keep h9 h1 h2) (le55 h1)).trans (sv_unch h9 U₂ i (kp h3 h1) (le55 h1))
  obtain r2₃ : sv Kt.c base s₃ R2N = 2 ^ (64 * Kt.c.n) * 2 ^ (64 * Kt.c.n) % Kt.c.C.n :=
    (k13 R2N (by decide)).trans hb.r2n
  -- `e R`.
  refine WP.seq (WP.mono (TKit.mulCall_kit hF hk hm hw₃ (o := Kt.c.sl EM) (a := Kt.c.sl VE) (b := Kt.c.sl R2N)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv Kt.c base s₃ R2N < Kt.c.C.n; rw [r2₃]; exact nlt _)) fun s₄ ⟨C₄, lt₄, e₄⟩ => ?_)
  obtain hw₄ := hw₃.of_kp C₄.kp
  have U₄ : Unch base (cw Kt.c EM) s₃.mem s₄.mem := C₄.mem
  obtain em : toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₄ EM) = Fin.ofNat Kt.c.C.n e := by
    refine toM_r2 hU ?_
    rw [show sv Kt.c base s₄ EM * 2 ^ (64 * Kt.c.n) % Kt.c.C.n = _ from e₄]
    show sv Kt.c base s₃ VE * sv Kt.c base s₃ R2N % Kt.c.C.n = _
    rw [r2₃, k13 VE (by decide), hb.ev]
  -- `u R`.
  obtain acc₄ : sv Kt.c base s₄ ACC = sv Kt.c base s₃ ACC := sv_unch h9 U₄ ACC (kp (by decide) (by decide))
  refine WP.seq (WP.mono (TKit.mulCall_kit hF hk hm hw₄ (o := Kt.c.sl UM) (a := Kt.c.sl EM) (b := Kt.c.sl ACC)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv Kt.c base s₄ ACC < Kt.c.C.n; rw [acc₄]; exact acclt₃)) fun s₅ ⟨C₅, lt₅, e₅⟩ => ?_)
  obtain hw₅ := hw₄.of_kp C₅.kp
  have U₅ : Unch base (cw Kt.c UM) s₄.mem s₅.mem := C₅.mem
  obtain um : toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₅ UM) =
      Fin.ofNat Kt.c.C.n e * Fin.ofNat Kt.c.C.n sg ^ (Kt.c.C.n - 2) := by
    rw [toM_mul hU e₅]
    show toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₄ EM) *
      toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₄ ACC) = _
    rw [em, acc₄, acc₃]
  -- `u`.
  obtain one₅ : sv Kt.c base s₅ ONE = 1 := by
    show wordsVal _ _ _ _ = _
    rw [sv_unch h9 U₅ ONE (kp (by decide) (by decide)), sv_unch h9 U₄ ONE (kp (by decide) (by decide))]
    exact (k13 ONE (by decide)).trans hb.one
  refine WP.seq (WP.mono (TKit.mulCall_kit hF hk hm hw₅ (o := Kt.c.sl UU) (a := Kt.c.sl UM) (b := Kt.c.sl ONE)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv Kt.c base s₅ ONE < Kt.c.C.n; rw [one₅]; exact hn1)) fun s₆ ⟨C₆, lt₆, e₆⟩ => ?_)
  obtain hw₆ := hw₅.of_kp C₆.kp
  have U₆ : Unch base (cw Kt.c UU) s₅.mem s₆.mem := C₆.mem
  obtain uu : Fin.ofNat Kt.c.C.n (sv Kt.c base s₆ UU) =
      Fin.ofNat Kt.c.C.n e * Fin.ofNat Kt.c.C.n sg ^ (Kt.c.C.n - 2) := by
    rw [← um]
    refine toM_one_mul hU ?_
    rw [show sv Kt.c base s₆ UU * 2 ^ (64 * Kt.c.n) % Kt.c.C.n = _ from e₆]
    show sv Kt.c base s₅ UM * sv Kt.c base s₅ ONE % Kt.c.C.n = _
    rw [one₅]
  -- `r R`.
  obtain r2₆ : sv Kt.c base s₆ R2N = 2 ^ (64 * Kt.c.n) * 2 ^ (64 * Kt.c.n) % Kt.c.C.n := by
    show wordsVal _ _ _ _ = _
    rw [sv_unch h9 U₆ R2N (kp (by decide) (by decide)), sv_unch h9 U₅ R2N (kp (by decide) (by decide)),
      sv_unch h9 U₄ R2N (kp (by decide) (by decide))]
    exact r2₃
  refine WP.seq (WP.mono (TKit.mulCall_kit hF hk hm hw₆ (o := Kt.c.sl RM) (a := Kt.c.sl VR) (b := Kt.c.sl R2N)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv Kt.c base s₆ R2N < Kt.c.C.n; rw [r2₆]; exact nlt _)) fun s₇ ⟨C₇, lt₇, e₇⟩ => ?_)
  obtain hw₇ := hw₆.of_kp C₇.kp
  have U₇ : Unch base (cw Kt.c RM) s₆.mem s₇.mem := C₇.mem
  obtain rm : toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₇ RM) = Fin.ofNat Kt.c.C.n r := by
    refine toM_r2 hU ?_
    rw [show sv Kt.c base s₇ RM * 2 ^ (64 * Kt.c.n) % Kt.c.C.n = _ from e₇]
    show sv Kt.c base s₆ VR * sv Kt.c base s₆ R2N % Kt.c.C.n = _
    rw [r2₆, show sv Kt.c base s₆ VR = sv Kt.c base s₃ VR from (sv_unch h9 U₆ VR (kp (by decide) (by decide))).trans
      ((sv_unch h9 U₅ VR (kp (by decide) (by decide))).trans (sv_unch h9 U₄ VR (kp (by decide) (by decide)))),
      k13 VR (by decide), hb.rv]
  -- `v R`.
  obtain acc₇ : sv Kt.c base s₇ ACC = sv Kt.c base s₃ ACC := by
    show wordsVal _ _ _ _ = _
    rw [sv_unch h9 U₇ ACC (kp (by decide) (by decide)), sv_unch h9 U₆ ACC (kp (by decide) (by decide)),
      sv_unch h9 U₅ ACC (kp (by decide) (by decide))]
    exact acc₄
  refine WP.seq (WP.mono (TKit.mulCall_kit hF hk hm hw₇ (o := Kt.c.sl VM) (a := Kt.c.sl RM) (b := Kt.c.sl ACC)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv Kt.c base s₇ ACC < Kt.c.C.n; rw [acc₇]; exact acclt₃)) fun s₈ ⟨C₈, lt₈, e₈⟩ => ?_)
  obtain hw₈ := hw₇.of_kp C₈.kp
  have U₈ : Unch base (cw Kt.c VM) s₇.mem s₈.mem := C₈.mem
  obtain vm : toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₈ VM) =
      Fin.ofNat Kt.c.C.n r * Fin.ofNat Kt.c.C.n sg ^ (Kt.c.C.n - 2) := by
    rw [toM_mul hU e₈]
    show toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₇ RM) *
      toM Kt.c.C.n (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₇ ACC) = _
    rw [rm, acc₇, acc₃]
  -- `v`.
  obtain one₈ : sv Kt.c base s₈ ONE = 1 := by
    show wordsVal _ _ _ _ = _
    rw [sv_unch h9 U₈ ONE (kp (by decide) (by decide)), sv_unch h9 U₇ ONE (kp (by decide) (by decide)),
      sv_unch h9 U₆ ONE (kp (by decide) (by decide))]
    exact one₅
  refine WP.mono (TKit.mulCall_kit hF hk hm hw₈ (o := Kt.c.sl VV) (a := Kt.c.sl VM) (b := Kt.c.sl ONE)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv Kt.c base s₈ ONE < Kt.c.C.n; rw [one₈]; exact hn1)) fun s₉ ⟨C₉, lt₉, e₉⟩ => ?_
  have U₉ : Unch base (cw Kt.c VV) s₈.mem s₉.mem := C₉.mem
  obtain vv : Fin.ofNat Kt.c.C.n (sv Kt.c base s₉ VV) =
      Fin.ofNat Kt.c.C.n r * Fin.ofNat Kt.c.C.n sg ^ (Kt.c.C.n - 2) := by
    rw [← vm]
    refine toM_one_mul hU ?_
    rw [show sv Kt.c base s₉ VV * 2 ^ (64 * Kt.c.n) % Kt.c.C.n = _ from e₉]
    show sv Kt.c base s₈ VM * sv Kt.c base s₈ ONE % Kt.c.C.n = _
    rw [one₈]
  obtain uu₉ : sv Kt.c base s₉ UU = sv Kt.c base s₆ UU := by
    show wordsVal _ _ _ _ = _
    rw [sv_unch h9 U₉ UU (kp (by decide) (by decide)), sv_unch h9 U₈ UU (kp (by decide) (by decide)),
      sv_unch h9 U₇ UU (kp (by decide) (by decide))]
  refine ⟨C₂.kp.kc.trans (K₃.trans (C₄.kp.kc.trans (C₅.kp.kc.trans (C₆.kp.kc.trans (C₇.kp.kc.trans
    (C₈.kp.kc.trans C₉.kp.kc)))))),
    ((((((U₂.trans U₃).trans U₄).trans U₅).trans U₆).trans U₇).trans U₈).trans U₉,
    by rw [uu₉]; exact lt₆, by rw [uu₉]; exact uu, lt₉, vv⟩

/-! ## The comparison and the end -/

/-- `x mod n`, `r mod n`, and their difference modulo `n`, zero exactly if `x ≡ r`. -/
theorem compare_ok {base : Addr} {s : State} (hw : WsReg s base) (hx : sv Kt.c base s XO < Kt.c.C.p)
    (hz : sv Kt.c base s ZERO = 0) (hr : sv Kt.c base s VR < 256 ^ Kt.L) :
    WP isa (Verify.Cfg.compare Kt.c Kt.FN) s fun s' => Kc s s' ∧ Unch base (cmpW Kt.c) s.mem s'.mem ∧
      (sv Kt.c base s' WD = 0 ↔
        Fin.ofNat Kt.c.C.n (sv Kt.c base s XO) = Fin.ofNat Kt.c.C.n (sv Kt.c base s VR)) := by
  obtain h9 := Kt.n9
  obtain hk := Kt.FNk
  obtain hm := Kt.FNm
  obtain hF := Kt.order_ok
  obtain hn0 : 0 < Kt.c.C.n := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain hpn := Kt.pn
  obtain hn2 := Kt.n2
  obtain hl : ∀ {i : Nat}, i < 45 → Kt.c.sl i + 8 * Kt.c.n ≤ own Kt.c.n := fun hi => below_own h9 hi
  obtain hs : ∀ {i : Nat}, i ≤ 55 → Kt.c.sl i < 4095 := fun hi => sl_lt Kt.toSKit.n1 h9 hi
  rw [Verify.Cfg.compare]
  simp only [progs]
  refine WP.seq (WP.mono (addCall_kit hF hk hm hw (o := Kt.c.sl XN) (a := Kt.c.sl XO) (b := Kt.c.sl ZERO)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv Kt.c base s XO + sv Kt.c base s ZERO < 2 * Kt.c.C.n; rw [hz]; omega_using [hx, hpn]))
    fun s₁ ⟨C₁, v₁⟩ => ?_)
  obtain hw₁ := hw.of_kp C₁.kp
  have U₁ : Unch base (cw Kt.c XN) s.mem s₁.mem := C₁.mem
  obtain z₁ : sv Kt.c base s₁ ZERO = 0 := by
    show wordsVal _ _ _ _ = _; rw [sv_unch h9 U₁ ZERO (cw_keep h9 (by decide) (by decide))]; exact hz
  obtain r₁ : sv Kt.c base s₁ VR = sv Kt.c base s VR := sv_unch h9 U₁ VR (cw_keep h9 (by decide) (by decide))
  refine WP.seq (WP.mono (addCall_kit hF hk hm hw₁ (o := Kt.c.sl RN) (a := Kt.c.sl VR) (b := Kt.c.sl ZERO)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by
      show sv Kt.c base s₁ VR + sv Kt.c base s₁ ZERO < 2 * Kt.c.C.n
      rw [z₁, r₁]; omega_using [hr, hn2])) fun s₂ ⟨C₂, v₂⟩ => ?_)
  obtain hw₂ := hw₁.of_kp C₂.kp
  have U₂ : Unch base (cw Kt.c RN) s₁.mem s₂.mem := C₂.mem
  obtain xn₂ : sv Kt.c base s₂ XN = sv Kt.c base s XO % Kt.c.C.n := by
    show wordsVal _ _ _ _ = _
    rw [sv_unch h9 U₂ XN (cw_keep h9 (by decide) (by decide)), v₁]
    show (sv Kt.c base s XO + sv Kt.c base s ZERO) % Kt.c.C.n = _; rw [hz, Nat.add_zero]
  obtain rn₂ : sv Kt.c base s₂ RN = sv Kt.c base s VR % Kt.c.C.n := by
    show wordsVal _ _ _ _ = _
    rw [v₂]; show (sv Kt.c base s₁ VR + sv Kt.c base s₁ ZERO) % Kt.c.C.n = _; rw [z₁, Nat.add_zero, r₁]
  refine WP.mono (subCall_kit hF hk hm hw₂ (o := Kt.c.sl WD) (a := Kt.c.sl XN) (b := Kt.c.sl RN)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv Kt.c base s₂ XN < Kt.c.C.n; rw [xn₂]; exact Nat.mod_lt _ hn0)
    (by show sv Kt.c base s₂ RN < Kt.c.C.n; rw [rn₂]; exact Nat.mod_lt _ hn0)) fun s₃ ⟨C₃, v₃⟩ => ?_
  have U₃ : Unch base (cw Kt.c WD) s₂.mem s₃.mem := C₃.mem
  refine ⟨C₁.kp.kc.trans (C₂.kp.kc.trans C₃.kp.kc), (U₁.trans U₂).trans U₃, ?_⟩
  have hw' : sv Kt.c base s₃ WD = (sv Kt.c base s₂ XN + Kt.c.C.n - sv Kt.c base s₂ RN) % Kt.c.C.n := v₃
  rw [hw', xn₂, rn₂, Fin.ext_iff, Fin.val_ofNat, Fin.val_ofNat]
  obtain h1 := Nat.mod_lt (sv Kt.c base s XO) hn0
  obtain h2 := Nat.mod_lt (sv Kt.c base s VR) hn0
  generalize sv Kt.c base s XO % Kt.c.C.n = a at h1 ⊢
  generalize sv Kt.c base s VR % Kt.c.C.n = b at h2 ⊢
  constructor
  · intro h
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hab | hab
    · rw [Nat.mod_eq_of_lt (by omega_using [h1, h2, hab])] at h; omega_using [h1, h2, h, hab]
    · rw [show a + Kt.c.C.n - b = (a - b) + Kt.c.C.n by omega_using [hab], Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega_using [h1])] at h
      omega_using [h1, h2, h, hab]
  · intro h; subst h; rw [show a + Kt.c.C.n - a = Kt.c.C.n by omega_using [], Nat.mod_self]

/-- The end: the masks of `Z ≠ 0` and of the difference being zero into the
flag, its low bit to `a0`, and the saved registers restored. -/
theorem vfinish_ok {s : State} {base : Addr} (hw : WsReg s base) {b : Bool}
    (hF : word s.mem base (Kt.c.sl FLAG) = maskOf b) :
    WP isa (.block (Verify.Cfg.finish Kt.c)) s fun s' =>
      s'.gpr .a0 =
        (if (b && !decide (sv Kt.c base s RZ = 0)) && decide (sv Kt.c base s WD = 0) then 1 else 0) ∧
      s'.gpr .s0 = word s.mem base 0 ∧ s'.gpr .s1 = word s.mem base 8 ∧ s'.gpr .s2 = word s.mem base 16 ∧
      s'.gpr .ra = word s.mem base 24 ∧ s'.gpr .s3 = word s.mem base 32 ∧
      (∀ r ∈ preserved, r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp := by
  obtain h9 := Kt.n9
  obtain h1 := Kt.toSKit.n1
  obtain hfl := sl_lo Kt.c FLAG
  rw [Verify.Cfg.finish, retCode, restoreCode]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (nzFlag_ok Kt.c h9 (i := RZ) (by decide) hw) fun s₁ ⟨r₁, O₁, f₁⟩ => ?_)
  obtain hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono (zeroMask_ok hw₁ (n := Kt.c.n) (a := Kt.c.sl WD) (sl8 _ _)
    (sl_top h9 (by decide))) fun s₂ ⟨r₂, m₂, g₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  refine WP.block_append (WP.mono (TKit.andFlag_ok Kt.c h9 hw₂) fun s₃ ⟨f₃, r₃, O₃⟩ => ?_)
  obtain hw₃ := hw₂.of_rest r₃
  obtain wd₁ : wordsVal s₁.mem base (Kt.c.sl WD) Kt.c.n = sv Kt.c base s WD :=
    O₁.wordsVal (.inl (sl_le _ (by decide))) (sl_64 h9 (by decide))
  generalize hB : ((b && !decide (sv Kt.c base s RZ = 0)) && decide (sv Kt.c base s WD = 0)) = B
  obtain fl₃ : word s₃.mem base (Kt.c.sl FLAG) = maskOf B := by
    rw [f₃, m₂, f₁, hF, g₂, wd₁, maskOf_and, maskOf_and, hB]
  obtain wd : ∀ d, d + 8 ≤ 40 → word s₃.mem base d = word s.mem base d := fun d hd => by
    rw [O₃.word (.inl (by omega_using [hd, hfl])) (by omega_using [hd]), m₂,
      O₁.word (.inl (by omega_using [hd, hfl])) (by omega_using [hd])]
  refine ldAt_ws hw₃ (d := Kt.c.sl FLAG) (sl_lt h1 h9 (by decide)) (sl8 _ _) fun s₉ u₉ => ?_
  refine WP.cons (exec_logicImm (by decide)) ?_
  obtain u₉' := Upd.write s₉ .a0 (s₉.gpr .a0 &&& BitVec.ofInt 64 1)
  obtain hw₉ := (hw₃.of_kp (Kp.of_upd u₉)).of_kp (Kp.of_upd u₉')
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
  obtain np : ∀ r ∈ preserved, r ∉ [Reg.t0, .t1, .t3, .t4, .a7, .a0, .ra] := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide),
      v₁.other _ (by decide), u₉'.gpr, u₉.gpr, fl₃, and_one]
  · rw [v₅.gpr, v₄.mem, v₃.mem, v₂.mem, v₁.mem, u₉'.mem, u₉.mem, wd 0 (by decide)]
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
      u₉'.other _ hn.2.2.2.2.2.1, u₉.other _ hn.2.2.2.2.2.1, r₃.gpr _ (by simp [hn.1]),
      r₂.gpr _ (by simp [hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1]),
      r₁.gpr _ (by simp [hn.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1])]
  · rw [v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, u₉'.sp, u₉.sp, r₃.sp, r₂.sp, r₁.sp]

/-! ## The function -/

/-- Whether the signature at `sig` of `digest` verifies with the key at `pk`,
as the specification answers. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  Spec.Ecdsa.verify Kt.c.C (bytesAt m pk (1 + 2 * Kt.L)) (hashToInt Kt.c.C (bytesAt m digest Kt.L))
    (bytesAt m sig (2 * Kt.L))

/-- `vg_ecdsa_<curve>_verify(public = a0, digest = a1, sig = a2, scratch = a3)`, as the kit reads its
numbers, with `joint` for `[u]G + [v]Q`. -/
def prog (joint : Prog isa) : Prog isa :=
  .seq (.block Kt.vsetup) <|
  .seq (wsCall Kt.checkN Kt.checkC) <|
  .seq (.block ((Sign.Cfg.nConsts Kt.c).flatMap (fun (i, x) => setConst Kt.c.n (Kt.c.sl i) x))) <|
  .seq (Verify.Cfg.uv Kt.c Kt.FN) <|
  .seq joint <|
  .seq (chainPow (chainP Kt.c) (Kt.c.sl ONEP) Kt.c.FP) <|
  .seq (affineCoord Kt.c XM XO RX) <|
  .seq (Verify.Cfg.compare Kt.c Kt.FN) (.block (Verify.Cfg.finish Kt.c))

/-- What `vg_ecdsa_<curve>_verify` returns. -/
def post (s s' : State) : Prop :=
  s'.gpr .a0 = if Kt.vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0

/-- What the joint multiplication reads, with `Q` the point in the check's slots: the constants, `G`,
`u` and `v`, with the working space the only writable region. -/
structure JPre (base : Addr) (s : State) (Q : Point Kt.c.C) : Prop where
  ws : WsReg s base
  s3 : s.gpr .s3 = base
  wr : s.wr = [⟨base, 8192⟩]
  tc : TKit.Consts Kt.c base s
  bp : sv Kt.c base s BP = Kt.c.C.b * 2 ^ (64 * Kt.c.n) % Kt.c.C.p
  gx : sv Kt.c base s GX = Kt.c.C.gx * 2 ^ (64 * Kt.c.n) % Kt.c.C.p
  gy : sv Kt.c base s GY = Kt.c.C.gy * 2 ^ (64 * Kt.c.n) % Kt.c.C.p
  qx : sv Kt.c base s CPX < Kt.c.C.p
  qy : sv Kt.c base s CPY < Kt.c.C.p
  q : Point.affine (toM Kt.c.C.p (2 ^ (64 * Kt.c.n)) (sv Kt.c base s CPX))
    (toM Kt.c.C.p (2 ^ (64 * Kt.c.n)) (sv Kt.c base s CPY)) = Q
  on : Spec.Weierstrass.onCurve Kt.c.C Q = true
  u : sv Kt.c base s UU < Kt.c.C.n
  v : sv Kt.c base s VV < Kt.c.C.n

/-- `vg_ecdsa_<curve>_verify` by register, with a `joint` that computes `R = [u]G + [v]Q` (`hj`),
writing `JW`, given a property `T` of states that holds after the setup (`hT`) and that the check's
call (`hTc`) and changes within the working space (`hTu`) keep: a comb's table, or nothing. -/
theorem verify_ok (hL : Law Kt.c.C) {joint : Prog isa} {JW : List (Nat × Nat)} (hJ : JWOk Kt.c JW)
    {T : State → Prop} {s : State} (hs : Kt.VPre s)
    (hT : ∀ s₁, s₁.syms = s.syms → s₁.rd = s.rd → Frame s.wr s.mem s₁.mem → T s₁)
    (hTc : ∀ {t : State} {Q : State → Prop}, T t → t.wr = [⟨s.gpr .a3, 8192⟩] →
      WP isa (wsCall Kt.checkN Kt.checkC) t Q → WP isa (wsCall Kt.checkN Kt.checkC) t fun t' => Q t' ∧ T t')
    (hTu : ∀ {t t' : State} {W : List (Nat × Nat)}, T t → t'.syms = t.syms → t'.rd = t.rd →
      (∀ w ∈ W, w.1 + w.2 ≤ 8192) → Unch (s.gpr .a3) W t.mem t'.mem → T t')
    (hj : ∀ {t : State} {Q : Point Kt.c.C}, Kt.JPre (s.gpr .a3) t Q → T t →
      WP isa joint t fun t' => Kc t t' ∧ Unch (s.gpr .a3) JW t.mem t'.mem ∧
        Rep Kt.c.C (tmv Kt.c.C Kt.c.n (s.gpr .a3) t' (Kt.c.sl RX)) (tmv Kt.c.C Kt.c.n (s.gpr .a3) t' (Kt.c.sl RY))
          (tmv Kt.c.C Kt.c.n (s.gpr .a3) t' (Kt.c.sl RZ))
          (Spec.Weierstrass.add (Spec.Weierstrass.mul (sv Kt.c (s.gpr .a3) t UU) (Spec.Weierstrass.G Kt.c.C))
            (Spec.Weierstrass.mul (sv Kt.c (s.gpr .a3) t VV) Q)) ∧
        sv Kt.c (s.gpr .a3) t' RX < Kt.c.C.p ∧ sv Kt.c (s.gpr .a3) t' RY < Kt.c.C.p ∧
        sv Kt.c (s.gpr .a3) t' RZ < Kt.c.C.p) :
    WP isa (Kt.prog joint) s fun s' => abiPreserved s s' ∧ Kt.post s s' := by
  obtain h9 := Kt.n9
  obtain h1 := Kt.toSKit.n1
  obtain hLn := Kt.Ln
  obtain hU := Kt.unit
  obtain hp0 : 0 < Kt.c.C.p := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain hwr := hs.wr
  rw [prog]
  refine WP.seq (wp_syms_frame (WP.mono (Kt.vsetup_ok hs) fun s₁ S sy₁ F₁ => ?_))
  obtain hT₁ := hT s₁ sy₁ S.rd F₁
  generalize hb : s.gpr .a3 = base at S hwr hTc hTu hj
  have Sx := S.x
  have Sy := S.y
  have Sflag := S.flag
  have Srv := S.rv
  -- The check.
  obtain hf₁ : word s₁.mem base (Kt.c.sl FLAG) = 0 ∨ word s₁.mem base (Kt.c.sl FLAG) = BitVec.allOnes 64 := by
    rw [S.flag]; unfold maskOf; split <;> simp
  refine WP.seq (WP.mono (hTc hT₁ (by rw [S.wr, hwr]) (Kt.toSKit.toKit.check_ok S.ws S.s3 S.consts hf₁))
    fun s₂ ⟨⟨K₂, U₂, f₂, px₂, py₂⟩, hT₂⟩ => ?_)
  obtain hw₂ := S.ws.of_kp K₂
  -- The constants modulo `n`.
  refine WP.seq (wp_syms (TKit.consts_ok Kt.c h9 _ hw₂ (nconsts_le Kt.c) (nconsts_nodup Kt.c))
    fun s₃ ⟨r₃, U₃, e₃⟩ sy₃ => ?_)
  obtain hw₃ := hw₂.of_rest r₃
  obtain cs₃ : ∀ e ∈ Sign.Cfg.nConsts Kt.c, sv Kt.c base s₃ e.1 = e.2 := fun e he => by
    rw [e₃ e he, Nat.mod_eq_of_lt (Kt.nconsts_lt e he)]
  obtain U₁₃ := U₂.trans U₃
  -- What the check and the constants modulo `n` keep.
  obtain keep13 : ∀ i ∈ [ONE, VR, VS, VE, ZERO, ONEP, AP, B3P, GX, GY, EXPP, MP, MN, BP],
      ∀ w ∈ Kt.toSKit.toKit.checkKW ++ (Sign.Cfg.nConsts Kt.c).map (fun e => (Kt.c.sl e.1, 8 * Kt.c.n)),
        Kt.c.sl i + 8 * Kt.c.n ≤ w.1 ∨ w.1 + w.2 ≤ Kt.c.sl i := fun i hi => by
    obtain ⟨h1, h2, h3⟩ := (by decide : ∀ i ∈ [ONE, VR, VS, VE, ZERO, ONEP, AP, B3P, GX, GY, EXPP, MP, MN, BP],
      i < FLAG ∧ (∀ j ∈ [2, 37, 41, 42, 34, 35, 38, 43], i ≠ j) ∧ (∀ j ∈ [R2N, ONEN, EXPN], i ≠ j)) i hi
    exact all_app (checkKW_apart h9 h1 h2) (apart_nconsts _ h3)
  obtain k₁₃ : ∀ i ∈ [ONE, VR, VS, VE, ZERO, ONEP, AP, B3P, GX, GY, EXPP, MP, MN, BP],
      sv Kt.c base s₃ i = sv Kt.c base s₁ i := fun i hi =>
    sv_unch h9 U₁₃ i (keep13 i hi)
      ((by decide : ∀ i ∈ [ONE, VR, VS, VE, ZERO, ONEP, AP, B3P, GX, GY, EXPP, MP, MN, BP], i ≤ 55) i hi)
  -- What `u` and `v` keep.
  obtain keepU : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP, GX, GY, VR, BP, CPX, CPY],
      ∀ w ∈ uvW Kt.c, Kt.c.sl i + 8 * Kt.c.n ≤ w.1 ∨ w.1 + w.2 ≤ Kt.c.sl i := fun i hi => by
    obtain ⟨h1, h2⟩ := (by decide : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP, GX, GY, VR, BP, CPX, CPY],
      i < 45 ∧ ∀ j ∈ [KM, ACC, EM, UM, UU, RM, VM, VV], i ≠ j) i hi
    exact uvW_keep h9 h1 h2
  obtain tc₁ : TKit.Consts Kt.c base s₁ := ⟨Kt.toSKit.toKit.const_at S.consts 0, Kt.toSKit.toKit.const_at S.consts 1,
    Kt.toSKit.toKit.const_at S.consts 2, Kt.toSKit.toKit.const_at S.consts 3, Kt.toSKit.toKit.const_at S.consts 4,
    Kt.toSKit.toKit.const_at S.consts 5, Kt.toSKit.toKit.const_at S.consts 6, Kt.toSKit.toKit.const_at S.consts 9⟩
  -- `u` and `v`.
  refine WP.seq (wp_syms (Kt.uv_ok (r := ofBytes (bytesAt s.mem (s.gpr .a2) Kt.L))
    (sg := ofBytes (bytesAt s.mem (s.gpr .a2 + BitVec.ofNat 64 Kt.L) Kt.L))
    (e := ofBytes (bytesAt s.mem (s.gpr .a1) Kt.L))
    ⟨hw₃, (k₁₃ ONE (by decide)).trans tc₁.one, (k₁₃ VR (by decide)).trans S.rv, (k₁₃ VS (by decide)).trans S.svs,
      (k₁₃ VE (by decide)).trans S.ev, cs₃ (R2N, _) (List.Mem.head _),
      cs₃ (ONEN, _) (List.Mem.tail _ (List.Mem.head _))⟩)
    fun s₄ ⟨K₄, U₄, ult, uval, vlt, vval⟩ sy₄ => ?_)
  obtain hw₄ := hw₃.of_kc K₄
  -- The key's point, or `G`.
  obtain tc₄ := (tc₁.of_unch h9 U₁₃ fun i hi => keep13 i ((by decide : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP],
      i ∈ [ONE, VR, VS, VE, ZERO, ONEP, AP, B3P, GX, GY, EXPP, MP, MN, BP]) i hi)).of_unch h9 U₄
    fun i hi => keepU i ((by decide : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP],
      i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP, GX, GY, VR, BP, CPX, CPY]) i hi)
  obtain gx₁ : sv Kt.c base s₁ GX = Kt.c.C.gx * 2 ^ (64 * Kt.c.n) % Kt.c.C.p := Kt.toSKit.toKit.const_at S.consts 7
  obtain gy₁ : sv Kt.c base s₁ GY = Kt.c.C.gy * 2 ^ (64 * Kt.c.n) % Kt.c.C.p := Kt.toSKit.toKit.const_at S.consts 8
  obtain bp₁ : sv Kt.c base s₁ BP = Kt.c.C.b * 2 ^ (64 * Kt.c.n) % Kt.c.C.p := Kt.toSKit.toKit.const_at S.consts 11
  obtain e₂₄ : ∀ i ∈ [CPX, CPY], sv Kt.c base s₄ i = sv Kt.c base s₂ i := fun i hi => by
    obtain ⟨h1, h2, h3⟩ := (by decide : ∀ i ∈ [CPX, CPY],
      (∀ j ∈ [R2N, ONEN, EXPN], i ≠ j) ∧ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP, GX, GY, VR, BP, CPX, CPY] ∧
        i ≤ 55) i hi
    exact sv_unch h9 (U₃.trans U₄) i (all_app (apart_nconsts _ h1) (keepU i h2)) h3
  obtain e₁₄ : ∀ i ∈ [GX, GY, VR, BP], sv Kt.c base s₄ i = sv Kt.c base s₁ i := fun i hi => by
    obtain ⟨h1, h2, h3⟩ := (by decide : ∀ i ∈ [GX, GY, VR, BP],
      i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP, GX, GY, VR, BP, CPX, CPY] ∧
      i ∈ [ONE, VR, VS, VE, ZERO, ONEP, AP, B3P, GX, GY, EXPP, MP, MN, BP] ∧ i ≤ 55) i hi
    exact (sv_unch h9 U₄ i (keepU i h1) h3).trans (k₁₃ i h2)
  generalize hF : word s₂.mem base (Kt.c.sl FLAG) = F at px₂ py₂ f₂
  generalize hx : sv Kt.c base s₁ CX = x at px₂ py₂ f₂ Sx
  generalize hy : sv Kt.c base s₁ CY = y at px₂ py₂ f₂ Sy
  obtain hval : F ≠ 0 → Kt.toSKit.toKit.CC.Valid x y := fun h0 => by
    by_contra h
    apply h0
    rw [f₂, mask_eq, decide_eq_false h]
    exact BitVec.and_zero
  obtain lt_qx : sv Kt.c base s₄ CPX < Kt.c.C.p := by
    rw [e₂₄ CPX (by decide), px₂]; split
    · rw [gx₁]; exact Nat.mod_lt _ hp0
    · exact Nat.mod_lt _ hp0
  obtain lt_qy : sv Kt.c base s₄ CPY < Kt.c.C.p := by
    rw [e₂₄ CPY (by decide), py₂]; split
    · rw [gy₁]; exact Nat.mod_lt _ hp0
    · exact Nat.mod_lt _ hp0
  generalize hQ : Point.affine (toM Kt.c.C.p (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₄ CPX))
    (toM Kt.c.C.p (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₄ CPY)) = Q
  obtain hon : Spec.Weierstrass.onCurve Kt.c.C Q = true := by
    rw [← hQ, e₂₄ CPX (by decide), e₂₄ CPY (by decide), px₂, py₂]
    by_cases h0 : F = 0
    · rw [ite_eq_left h0, ite_eq_left h0, gx₁, gy₁, toM_mont hU, toM_mont hU]
      exact Kt.onG
    · rw [ite_eq_right h0, ite_eq_right h0, toM_mont hU, toM_mont hU]
      exact valid_on Kt.toSKit.toKit.CCW (hval h0)
  -- `[u]G + [v]Q`.
  obtain hT₄ : T s₄ := hTu (hTu hT₂ sy₃ r₃.rd (top_nconsts h9) U₃) sy₄ K₄.rd (uvW_top Kt.c h1 h9) U₄
  obtain h3₄ : s₄.gpr .s3 = base := by
    rw [K₄.gpr _ (by decide) (by decide), r₃.gpr _ (by decide), K₂.gpr _ (by decide), S.s3]
  obtain hwr₄ : s₄.wr = [⟨base, 8192⟩] := by rw [K₄.wr, r₃.wr, K₂.wr, S.wr, hwr]
  refine WP.seq (WP.mono (hj ⟨hw₄, h3₄, hwr₄, tc₄, (e₁₄ BP (by decide)).trans bp₁, (e₁₄ GX (by decide)).trans gx₁,
    (e₁₄ GY (by decide)).trans gy₁, lt_qx, lt_qy, hQ, hon, ult, vlt⟩ hT₄)
    fun s₆ ⟨K₆, U₆, rep₆, ltx, lty, rzlt⟩ => ?_)
  obtain hw₆ := hw₄.of_kc K₆
  obtain tc₆ := tc₄.of_unch h9 U₆ hJ.consts
  -- `Z^(p-2)` and `x`.
  obtain kpC : ∀ {i : Nat}, i < 45 → i ≠ ACC →
      ∀ w ∈ chainWx (chainP Kt.c) Kt.c.n, Kt.c.sl i + 8 * Kt.c.n ≤ w.1 ∨ w.1 + w.2 ≤ Kt.c.sl i :=
    fun hi ha => chainN_keep h9 hi ha
  refine WP.seq (WP.mono (TKit.chainPow_kit (P := chainP Kt.c) Kt.field_ok Kt.FPk Kt.FPm
    (TKit.chainLay Kt.c h1 h9) hU hw₆ (one := Kt.c.sl ONEP) (below_own h9 (by decide)) (sl_lt h1 h9 (by decide))
    (by show sv Kt.c base s₆ ONEP = _; rw [tc₆.onep, Nat.one_mul]) Kt.chainP_ok)
    fun s₇ ⟨K₇, U₇, lt₇, v₇⟩ => ?_)
  obtain hw₇ := hw₆.of_kc K₇
  obtain tc₇ := tc₆.of_unch h9 U₇ fun i hi => by
    obtain ⟨h1, h2⟩ := (by decide : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP], i < 45 ∧ i ≠ ACC) i hi
    exact kpC h1 h2
  refine WP.seq (WP.mono (Kt.toTKit.affine_ok hw₇ (t := XM) (o := XO) (a := RX) (by decide) (by decide) (by decide)
    (by decide) lt₇ tc₇.one) fun s₈ ⟨K₈, U₈, lt₈, v₈⟩ => ?_)
  obtain hw₈ := hw₇.of_kp K₈
  have U₈' : Unch base (affW Kt.c) s₇.mem s₈.mem := U₈
  obtain tc₈ := tc₇.of_unch h9 U₈' fun i hi => by
    obtain ⟨h1, h2⟩ := (by decide : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP], i < 45 ∧ i ≠ XM ∧ i ≠ XO) i hi
    exact affW_keep h9 h1 h2
  -- `r` is the number of the signature's bytes.
  obtain vr₈ : sv Kt.c base s₈ VR = ofBytes (bytesAt s.mem (s.gpr .a2) Kt.L) := by
    rw [← Srv]
    show wordsVal _ _ _ _ = _
    rw [sv_unch h9 U₈' VR (affW_keep h9 (by decide) (by decide)), sv_unch h9 U₇ VR (kpC (by decide) (by decide)),
      sv_unch h9 U₆ VR hJ.vr, sv_unch h9 U₄ VR (keepU VR (by decide)), sv_unch h9 U₁₃ VR (keep13 VR (by decide))]
  obtain vr₈' : sv Kt.c base s₈ VR < 256 ^ Kt.L := by
    have := VG.Proof.Weierstrass.ofBytes_lt (bytesAt s.mem (s.gpr .a2) Kt.L)
    rw [VG.Proof.Weierstrass.length_bytesAt] at this
    rw [vr₈]; exact this
  -- The comparison and the end.
  refine WP.seq (WP.mono (Kt.compare_ok hw₈ lt₈ tc₈.zero vr₈') fun s₉ ⟨K₉, U₉, cmp⟩ => ?_)
  obtain hw₉ := hw₈.of_kc K₉
  obtain U₂₉ := (((((U₃.trans U₄).trans U₆).trans U₇).trans U₈').trans U₉)
  refine WP.mono (Kt.vfinish_ok hw₉ (b := (((((decide (s.mem (s.gpr .a0) = 4) &&
      decide (ofBytes (bytesAt s.mem (s.gpr .a2) Kt.L) < Kt.c.C.n)) &&
      !decide (ofBytes (bytesAt s.mem (s.gpr .a2) Kt.L) = 0)) &&
      decide (ofBytes (bytesAt s.mem (s.gpr .a2 + BitVec.ofNat 64 Kt.L) Kt.L) < Kt.c.C.n)) &&
      !decide (ofBytes (bytesAt s.mem (s.gpr .a2 + BitVec.ofNat 64 Kt.L) Kt.L) = 0)) &&
      decide (Kt.toSKit.toKit.CC.Valid x y)))
    (by rw [U₂₉.word (all_app (all_app (all_app (all_app (all_app (flag_nconsts _) (uvW_flag Kt.c h1 h9)) hJ.flag)
          (chainN_flag h1 h9)) (affW_flag h9)) (all_app (all_app (cw_flag h9 (by decide)) (cw_flag h9 (by decide)))
          (cw_flag h9 (by decide)))) (flag_64 h1 h9), hF, f₂, Sflag, mask_eq, maskOf_and]))
    fun s' ⟨a0', s0', s1', s2', ra', s3', regs', sp'⟩ => ?_
  -- The registers.
  obtain U₁₉ := U₂.trans U₂₉
  obtain lo : ∀ w ∈ Kt.toSKit.toKit.checkKW ++ ((((((Sign.Cfg.nConsts Kt.c).map (fun e => (Kt.c.sl e.1, 8 * Kt.c.n)) ++
      uvW Kt.c) ++ JW) ++ chainWx (chainP Kt.c) Kt.c.n) ++ affW Kt.c) ++ cmpW Kt.c), 40 ≤ w.1 :=
    all_app Kt.toSKit.toKit.check_lo (all_app (all_app (all_app (all_app (all_app (lo_nconsts _) (uvW_lo Kt.c h9)) hJ.lo)
      (chainN_lo h9)) (affW_lo h9)) (all_app (all_app (cw_lo h9 _) (cw_lo h9 _)) (cw_lo h9 _)))
  refine ⟨⟨fun r hr => ?_, by rw [sp', K₉.sp, K₈.sp, K₇.sp, K₆.sp, K₄.sp, r₃.sp, K₂.sp, S.sp],
    by rw [ra', lo_word U₁₉ lo (d := 24) (by decide), S.sv3]⟩, ?_⟩
  · by_cases h0 : r = .s0
    · subst h0; rw [s0', lo_word U₁₉ lo (d := 0) (by decide), S.sv0]
    by_cases h1 : r = .s1
    · subst h1; rw [s1', lo_word U₁₉ lo (d := 8) (by decide), S.sv1]
    by_cases h2' : r = .s2
    · subst h2'; rw [s2', lo_word U₁₉ lo (d := 16) (by decide), S.sv2]
    by_cases h3' : r = .s3
    · subst h3'; rw [s3', lo_word U₁₉ lo (d := 32) (by decide), S.sv4]
    obtain ht : r ∉ [Reg.t0, .t1] := by
      rintro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> exact absurd hr (by decide)
    rw [regs' r hr h0 h1 h2' h3', K₉.gpr r hr h1, K₈.gpr r hr, K₇.gpr r hr h1, K₆.gpr r hr h1,
      K₄.gpr r hr h1, r₃.gpr r ht, K₂.gpr r hr, S.regs r h0 h2' h3' hr]
  -- The specification.
  obtain hsplit : bytesAt s.mem (s.gpr .a2) (2 * Kt.L) =
      bytesAt s.mem (s.gpr .a2) Kt.L ++ bytesAt s.mem (s.gpr .a2 + BitVec.ofNat 64 Kt.L) Kt.L := by
    rw [Nat.two_mul]; exact VG.Proof.Weierstrass.bytesAt_add s.mem (s.gpr .a2) Kt.L Kt.L
  obtain hrr : ofBytes ((bytesAt s.mem (s.gpr .a2) (2 * Kt.L)).take Kt.c.C.len) =
      ofBytes (bytesAt s.mem (s.gpr .a2) Kt.L) := by
    rw [Kt.len, hsplit, List.take_left' (VG.Proof.Weierstrass.length_bytesAt _ _ _)]
  obtain hss : ofBytes ((bytesAt s.mem (s.gpr .a2) (2 * Kt.L)).drop Kt.c.C.len) =
      ofBytes (bytesAt s.mem (s.gpr .a2 + BitVec.ofNat 64 Kt.L) Kt.L) := by
    rw [Kt.len, hsplit, List.drop_left' (VG.Proof.Weierstrass.length_bytesAt _ _ _)]
  generalize hR : ofBytes (bytesAt s.mem (s.gpr .a2) Kt.L) = R at a0' hrr vval Sflag Srv vr₈
  generalize hSg : ofBytes (bytesAt s.mem (s.gpr .a2 + BitVec.ofNat 64 Kt.L) Kt.L) = Sg at a0' hss uval vval Sflag
  obtain rz₉ : sv Kt.c base s₉ RZ = sv Kt.c base s₆ RZ := by
    show wordsVal _ _ _ _ = _
    rw [sv_unch h9 U₉ RZ (all_app (all_app (cw_keep h9 (by decide) (by decide)) (cw_keep h9 (by decide) (by decide)))
        (cw_keep h9 (by decide) (by decide))), sv_unch h9 U₈' RZ (affW_keep h9 (by decide) (by decide)),
      sv_unch h9 U₇ RZ (kpC (by decide) (by decide))]
  rw [rz₉] at a0'
  unfold post
  rw [a0', vf, Kt.toSKit.hash_eq]
  by_cases hrs : 1 ≤ R ∧ R < Kt.c.C.n ∧ 1 ≤ Sg ∧ Sg < Kt.c.C.n
  · -- In range: the key's point is the check's.
    obtain hrn : decide (R < Kt.c.C.n) = true := decide_eq_true hrs.2.1
    obtain hr0 : decide (R = 0) = false := decide_eq_false (by omega_using [hrs])
    obtain hsn : decide (Sg < Kt.c.C.n) = true := decide_eq_true hrs.2.2.2
    obtain hs0 : decide (Sg = 0) = false := decide_eq_false (by omega_using [hrs])
    generalize hb0 : s.mem (s.gpr .a0) = b0 at Sflag ⊢
    rw [hrn, hr0, hsn, hs0]
    obtain hlen : (bytesAt s.mem (s.gpr .a0) (1 + 2 * Kt.L)).length = 2 * Kt.c.C.len + 1 := by
      rw [VG.Proof.Weierstrass.length_bytesAt, Kt.len]; omega_using []
    obtain hpb := peer_bytes s.mem (s.gpr .a0) Kt.L
    obtain hhd : (bytesAt s.mem (s.gpr .a0) (1 + 2 * Kt.L)).head? = some b0 := by rw [hpb, ← hb0]; rfl
    obtain hxv : ofBytes (((bytesAt s.mem (s.gpr .a0) (1 + 2 * Kt.L)).drop 1).take Kt.c.C.len) = x := by
      rw [Kt.len, hpb, List.drop_one, List.tail_cons,
        List.take_left' (VG.Proof.Weierstrass.length_bytesAt _ _ _)]; exact Sx.symm
    obtain hyv : ofBytes ((bytesAt s.mem (s.gpr .a0) (1 + 2 * Kt.L)).drop (Kt.c.C.len + 1)) = y := by
      rw [Kt.len, hpb, List.drop_succ_cons, List.drop_left' (VG.Proof.Weierstrass.length_bytesAt _ _ _)]
      exact Sy.symm
    obtain hP : ∀ h : VG.Proof.Ecdh.Valid Kt.c.C b0 x y, Q = .affine ⟨x, h.2.1⟩ ⟨y, h.2.2.1⟩ := fun h => by
      obtain hv : Kt.toSKit.toKit.CC.Valid x y := (valid_iff_of Kt.toSKit.toKit.CCW x y).mpr h.2
      obtain hF0 : F ≠ 0 := by
        rw [f₂, Sflag, mask_eq, hrn, hr0, hsn, hs0, decide_eq_true h.1, decide_eq_true hv]; decide
      rw [← hQ, e₂₄ CPX (by decide), e₂₄ CPY (by decide), px₂, py₂, ite_eq_right hF0, ite_eq_right hF0,
        toM_mont hU, toM_mont hU, VG.Proof.EcKey.fe_eq h.2.1 rfl, VG.Proof.EcKey.fe_eq h.2.2.1 rfl]
    obtain rx₇ : sv Kt.c base s₇ RX = sv Kt.c base s₆ RX := sv_unch h9 U₇ RX (kpC (by decide) (by decide))
    have acc₇ : toM Kt.c.C.p (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₇ ACC) =
        toM Kt.c.C.p (2 ^ (64 * Kt.c.n)) (sv Kt.c base s₆ RZ) ^ (Kt.c.C.p - 2) := v₇
    obtain hxoX : Fin.ofNat Kt.c.C.p (sv Kt.c base s₈ XO) = tmv Kt.c.C Kt.c.n base s₆ (Kt.c.sl RX) *
        tmv Kt.c.C Kt.c.n base s₆ (Kt.c.sl RZ) ^ (Kt.c.C.p - 2) := by
      rw [v₈, acc₇, rx₇]
    rw [VG.Proof.Ecdsa.verify_eq hL hlen hhd hxv hyv hP hrr hss ult vlt uval vval rep₆ lt₈ hxoX]
    obtain key : (((((((decide (b0 = 4) && true) && !false) && true) && !false) &&
        decide (Kt.toSKit.toKit.CC.Valid x y)) && !decide (sv Kt.c base s₆ RZ = 0)) && decide (sv Kt.c base s₉ WD = 0)) =
        decide (VG.Proof.Ecdh.Valid Kt.c.C b0 x y ∧ (1 ≤ R ∧ R < Kt.c.C.n) ∧ (1 ≤ Sg ∧ Sg < Kt.c.C.n) ∧
          tmv Kt.c.C Kt.c.n base s₆ (Kt.c.sl RZ) ≠ 0 ∧
          Fin.ofNat Kt.c.C.n (sv Kt.c base s₈ XO) = Fin.ofNat Kt.c.C.n R) := by
      rw [Bool.eq_iff_iff]
      simp only [Bool.and_true, Bool.not_false, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        decide_eq_false_iff_not]
      obtain hz : tmv Kt.c.C Kt.c.n base s₆ (Kt.c.sl RZ) ≠ 0 ↔ ¬ sv Kt.c base s₆ RZ = 0 := by
        rw [ne_eq]; exact not_congr (toM_eq_zero_iff hU rzlt)
      rw [hz, valid_iff_of Kt.toSKit.toKit.CCW, cmp, vr₈]
      unfold VG.Proof.Ecdh.Valid
      constructor
      · rintro ⟨⟨⟨h4, hv⟩, hz'⟩, hx'⟩; exact ⟨⟨h4, hv⟩, ⟨hrs.1, hrs.2.1⟩, ⟨hrs.2.2.1, hrs.2.2.2⟩, hz', hx'⟩
      · rintro ⟨⟨h4, hv⟩, -, -, hz', hx'⟩; exact ⟨⟨⟨h4, hv⟩, hz'⟩, hx'⟩
    rw [key]
  · -- Out of range: no signature verifies.
    rw [verify_false (by rw [hrr, hss]; exact hrs)]
    obtain hB : (((((((decide (s.mem (s.gpr .a0) = 4) && decide (R < Kt.c.C.n)) && !decide (R = 0)) &&
        decide (Sg < Kt.c.C.n)) && !decide (Sg = 0)) && decide (Kt.toSKit.toKit.CC.Valid x y)) &&
        !decide (sv Kt.c base s₆ RZ = 0)) && decide (sv Kt.c base s₉ WD = 0)) = false := by
      rw [Bool.eq_false_iff]
      intro h
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at h
      exact hrs ⟨by have := h.1.1.1.1.1.2; omega_using [this], h.1.1.1.1.1.1.2,
        by have := h.1.1.1.2; omega_using [this], h.1.1.1.1.2⟩
    rw [hB]

end Kit

end VG.Proof.Ecdsa.RISCV64.VerifyAll
