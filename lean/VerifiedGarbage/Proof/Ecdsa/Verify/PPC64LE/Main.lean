module

public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Main
import VerifiedGarbage.Proof.EcKey.PPC64LE.Finish
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Flags
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Peer
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdh.Exchange
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.Main
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.LadPow
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointFprog
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Mont.PPC64LE.Const
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
import VerifiedGarbage.Proof.Weierstrass.Pow
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Joint
public import VerifiedGarbage.Impl.Ecdsa.Verify.PPC64LE
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Ecdsa.Verify.PPC64LE.Points`, which this module and modules that import it used -/

section

/-! ### `Ecdsa.Verify.PPC64LE.Scalars`, which this module and modules that import it used -/

section

/-! ### `Ecdsa.Verify.PPC64LE.Front`, which this module and modules that import it used -/

section

/-!
# ECDSA verification on PPC64LE: up to the key's checks

As on 32-bit ARM (`Proof/Ecdsa/Verify/Arm/Front.lean`). `front_ok`: the
signature's setup with verification's arguments (`r` into `K`, the hash
into `D` shifted, `public` kept in `r14` and `sig` in `r12`), its tables,
`s` into `PT`, and ECDH's checks of the key (`peer_ok` on `r14`,
`validate_ok`), which leave the key's point, or `G`, in `PX`, `PY` and the
mask of the key's validity in the flag.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Proof.Ecdh.PPC64LE VG.Spec.Weierstrass
open VG.Impl.Ecdh.PPC64LE (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)
open VG.Impl.Ecdsa.Verify.PPC64LE (Args.verify)

variable {c : Cfg}

/-- The arguments: `public` (`1 + 2 len` bytes), `digest` (`len` bytes),
`sig` (`2 len` bytes) and `scratch`, readable and writable as the contract
says and apart from `scratch`. -/
structure VPre (c : Cfg) (s : State) (extra : List Region := []) : Prop where
  rd : s.rd = [⟨s.gpr .r3, 1 + 2 * c.C.len⟩, ⟨s.gpr .r4, c.C.len⟩, ⟨s.gpr .r5, 2 * c.C.len⟩] ++ extra
  wr : s.wr = [⟨s.gpr .r6, size⟩]
  pk_sc : Region.Disjoint ⟨s.gpr .r3, 1 + 2 * c.C.len⟩ ⟨s.gpr .r6, size⟩
  dg_sc : Region.Disjoint ⟨s.gpr .r4, c.C.len⟩ ⟨s.gpr .r6, size⟩
  sig_sc : Region.Disjoint ⟨s.gpr .r5, 2 * c.C.len⟩ ⟨s.gpr .r6, size⟩
  pk_fit : (s.gpr .r3).toNat + (1 + 2 * c.C.len) ≤ 2 ^ 64
  dg_fit : (s.gpr .r4).toNat + c.C.len ≤ 2 ^ 64
  sig_fit : (s.gpr .r5).toNat + 2 * c.C.len ≤ 2 ^ 64
  sc_fit : (s.gpr .r6).toNat + size ≤ 2 ^ 64

/-- The key's `x` and `y`, the hash, and the signature's `r` and `s`. -/
abbrev keyX (c : Cfg) (s₀ : State) : Nat :=
  ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r3 + BitVec.ofNat 64 1) c.C.len)
abbrev keyY (c : Cfg) (s₀ : State) : Nat :=
  ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r3 + BitVec.ofNat 64 (1 + c.C.len)) c.C.len)
abbrev dig (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r4) c.C.len) >>> c.sh
abbrev sigR (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5) c.C.len)
abbrev sigS (c : Cfg) (s₀ : State) : Nat :=
  ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5 + BitVec.ofNat 64 c.C.len) c.C.len)

/-- The key is valid as the code checks it. -/
abbrev KeyOk (c : Cfg) (s₀ : State) : Prop :=
  ((s₀.mem (s₀.gpr .r3) = 4 ∧ keyX c s₀ < c.C.p) ∧ keyY c s₀ < c.C.p) ∧
    OnCurve c (Fin.ofNat c.C.p (keyX c s₀)) (Fin.ofNat c.C.p (keyY c s₀))

/-- After the key's checks, from the state `s₀` at entry, with the working
space at `base`. -/
structure Front (c : Cfg) (s₀ : State) (base : Addr) (s : State) : Prop extends Keep c s₀ base s where
  k : sv c base s K = sigR c s₀
  d : sv c base s D = dig c s₀
  pt : sv c base s PT = sigS c s₀
  rx : sv c base s RX = 0
  ry : sv c base s RY = c.mont 1
  rz : sv c base s RZ = 0
  t₁ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0
  t₂ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 2 + t)) = if (c.C.n - 2).testBit t then 1 else 0
  flag : flagW c base s = mask64 (KeyOk c s₀)
  px_lt : sv c base s PX < c.C.p
  py_lt : sv c base s PY < c.C.p
  px : toM c.C.p (2 ^ (64 * c.n)) (sv c base s PX) =
    if KeyOk c s₀ then Fin.ofNat c.C.p (keyX c s₀) else Fin.ofNat c.C.p c.C.gx
  py : toM c.C.p (2 ^ (64 * c.n)) (sv c base s PY) =
    if KeyOk c s₀ then Fin.ofNat c.C.p (keyY c s₀) else Fin.ofNat c.C.p c.C.gy

theorem VPre.setup {s : State} {extra : List Region} (hp : VPre c s extra) : SetupPre c Args.verify s where
  shift := .inr (.inl rfl)
  k_reg := by decide
  d_reg := by decide
  e_reg := by decide
  sc_reg := by decide
  wr := by show (⟨s.gpr .r6, size⟩ : Region) ∈ s.wr; rw [hp.wr]; simp
  sc_fit := hp.sc_fit
  k_in := fun e he => ⟨⟨s.gpr .r5, 2 * c.C.len⟩, by rw [hp.rd]; simp,
    Offset.contains_base _ (by omega_arith) (by have := hp.sig_fit; omega_arith)⟩
  d_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.dg_fit; omega_arith)
  e_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.dg_fit; omega_arith)
  k_sc := hp.sig_sc.sub_left (Region.sub_prefix (by omega_arith))
  d_sc := hp.dg_sc
  e_sc := hp.dg_sc
  k_fit := show (s.gpr .r5).toNat + c.C.len ≤ 2 ^ 64 by have := hp.sig_fit; omega_arith
  d_fit := hp.dg_fit
  e_fit := hp.dg_fit

theorem slW_le (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i < 45) : ∀ w ∈ slW c l, w.1 + w.2 ≤ size := by
  intro w hw
  have hsz : size = 8192 := rfl
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  have := sl_le c h7 (hl i hi); dsimp only; omega_arith

theorem flag_le (h7 : c.n < 10) : ∀ w ∈ [(c.sl FLAG, 8)], w.1 + w.2 ≤ size := fun w hw => by
  have hsz : size = 8192 := rfl
  rw [List.mem_singleton.mp hw]; have := sl_le c h7 (i := FLAG) (by decide); dsimp only; omega_arith

theorem prefix_eq (c : Cfg) : Impl.Ecdsa.Verify.PPC64LE.Cfg.prefix' c =
    .seq (.block (c.setupWith Args.verify ++ [mov .r12 .r5]))
      (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n))
      (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) (.block [])))) := rfl

theorem loadS_eq (c : Cfg) : Impl.Ecdsa.Verify.PPC64LE.Cfg.loadS c =
    .addi .r6 .r12 c.C.len :: loadBytes c.C.len c.n (c.sl PT) .r6 := rfl

/-- The setup, `sig` to `r12`, and the tables. -/
theorem prefix_ok (hc : CfgOk c) {s₀ : State} {extra : List Region} (hp : VPre c s₀ extra) :
    WP isa (Impl.Ecdsa.Verify.PPC64LE.Cfg.prefix' c) s₀ fun s =>
      St₁ c Args.verify s₀ (s₀.gpr .r6) (BitVec.allOnes 64) s ∧ s.gpr .r12 = s₀.gpr .r5 := by
  have h7 := hc.n10
  rw [prefix_eq]
  refine WP.seq (wp_append (WP.mono (stage₀' hc hp.setup) fun s₁ ⟨S₁, kp₁⟩ =>
    wp_step exec_mov (WP.block_nil ?_)))
  replace S₁ : St₀ c Args.verify s₀ (s₀.gpr .r6) (BitVec.allOnes 64) s₁ := S₁
  obtain kw : Kp [.r12] s₁ (s₁.write .r12 (s₁.gpr .r5)) := Kp.write _ _ (by decide)
  obtain S₁' : St₀ c Args.verify s₀ (s₀.gpr .r6) (BitVec.allOnes 64) (s₁.write .r12 (s₁.gpr .r5)) :=
    ⟨S₁.toKeep.step h7 (kw.rk (rs' := [.r12])) (W := []) (hU := Unch.refl _ _ _)
      (hW := fun _ h => absurd h List.not_mem_nil) (hWs := fun _ h => absurd h List.not_mem_nil),
      S₁.k, S₁.d, S₁.e, S₁.rx, S₁.ry, S₁.rz, S₁.expp, S₁.expn, S₁.flag⟩
  obtain r12₁ : (s₁.write .r12 (s₁.gpr .r5)).gpr .r12 = s₀.gpr .r5 := by
    simp only [write_gpr, ite_true]; exact kp₁.gpr _ (by decide)
  exact tables_ok hc S₁' fun s₂ S₂ kb => WP.block_nil ⟨S₂, by rw [kb.gpr _ (by decide), r12₁]⟩

/-- The setup and tables, `s`, and the checks of the key. -/
theorem front_ok (hc : CfgOk c) {s₀ : State} {extra : List Region} (hp : VPre c s₀ extra) {rest : Prog isa}
    {Q : State → Prop} (h : ∀ s, Front c s₀ (s₀.gpr .r6) s → WP isa rest s Q) :
    WP isa (.seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.prefix' c) (.seq (.block (Impl.Ecdsa.Verify.PPC64LE.Cfg.loadS c))
      (.seq (.block (Impl.Ecdh.PPC64LE.Cfg.peerAt c .r14)) (.seq (Impl.Ecdh.PPC64LE.Cfg.validate c) rest)))) s₀ Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hl8 := hc.len8
  have hlhi := hc.len_hi
  have hsz : size = 8192 := rfl
  obtain hPT := sl_le c h7 (i := PT) (by decide)
  refine WP.seq (WP.mono (prefix_ok hc hp) fun s₂ ⟨S₂, r12₂⟩ => ?_)
  generalize hb : s₀.gpr .r6 = base at S₂ h
  have hn := S₂.ws.nowrap
  obtain hsg : Region.Disjoint ⟨s₀.gpr .r5, 2 * c.C.len⟩ ⟨base, size⟩ := hb ▸ hp.sig_sc
  obtain hpk : Region.Disjoint ⟨s₀.gpr .r3, 1 + 2 * c.C.len⟩ ⟨base, size⟩ := hb ▸ hp.pk_sc
  obtain hrw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [S₂.rk.rd, S₂.rk.wr]
  obtain W₂ : Outside base 0 size s₀.mem s₂.mem :=
    S₂.whole.outside fun w hw => by rw [List.mem_singleton.mp hw]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  rw [loadS_eq]
  refine WP.seq (wp_step (exec_addi (by decide) (show c.C.len < 2 ^ 15 by omega_arith)) ?_)
  obtain kw₂ : Kp [.r6] s₂ (s₂.write .r6 (s₂.gpr .r12 + BitVec.ofNat 64 c.C.len)) := Kp.write _ _ (by decide)
  obtain hfitS : (s₀.gpr .r5 + BitVec.ofNat 64 c.C.len).toNat + c.C.len ≤ 2 ^ 64 := by
    have := hp.sig_fit
    rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (show c.C.len < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  refine WP.mono (setupLoad_ok hc (s := s₂) (i := PT) (src := .r6) (p := s₀.gpr .r5 + BitVec.ofNat 64 c.C.len)
    (S₂.ws.of_kp kw₂) (by decide) (by decide) (by simp only [write_gpr, ite_true, r12₂]) hfitS
    (fun e he => ⟨⟨s₀.gpr .r5, 2 * c.C.len⟩, by rw [kw₂.rd, kw₂.wr, hrw₂, hp.rd]; simp, by
      rw [Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by have := hp.sig_fit; omega_arith)⟩)
    (hsg.sub_left (Offset.sub_base _ (d := c.C.len) (n := c.C.len) (by omega_arith))) (by simp only [write_mem]; exact Outside.refl _ _ _ _))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have U₃ : Unch base (slW c [PT]) s₂.mem s₃.mem := O₃.unch
  rw [bytesAt_keep W₂ (hsg.sub_left (Offset.sub_base _ (d := c.C.len) (n := c.C.len) (by omega_arith))) (by omega_arith) (by omega_arith)] at e₃
  obtain K₃ := S₂.toKeep.step h7 (((kw₂.mono (rs' := [.r6, .r8, .r9]) (by decide)).trans
    (k₃.mono (by decide))).rk (rs' := [.r6, .r8, .r9])) (hU := U₃) (hW := fixedOk_slW (l := [PT]) (by decide))
    (hWs := slW_le h7 (by decide))
  obtain v₃ : ∀ {i}, i < 45 → i ≠ PT → sv c base s₃ i = sv c base s₂ i := fun hi hl =>
    sv_unch U₃ h7 hn hi (apart_slW (by simpa using hl))
  -- The key.
  have hq₃ : s₃.gpr .r14 = s₀.gpr .r3 := K₃.r14
  refine WP.seq (WP.mono (peer_ok hc K₃.ws (q := .r14) (by decide) (by rw [hq₃]; exact hp.pk_fit)
    (by rw [hq₃, K₃.rk.rd, K₃.rk.wr, hp.rd]; simp) (by rw [hq₃]; exact hpk) K₃.fixed.mp)
    fun s₄ ⟨hw₄, k₄, U₄, r2₄, bp₄, x₄, y₄, f₄⟩ => ?_)
  rw [hq₃] at x₄ y₄ f₄
  obtain K₄ := K₃.step h7 (k₄.rk (rs' := peerClob)) (hU := U₄)
    (hW := (fixedOk_slW (by decide)).append fixedOk_flag) (hWs := le_append (slW_le h7 (by decide)) (flag_le h7))
  obtain e₄ : ∀ {i}, i < 45 → i ∉ [R2P, BP, E, QY] → i ≠ FLAG → sv c base s₄ i = sv c base s₃ i :=
    fun hi hl hf => sv_unch U₄ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  obtain W₃ : Outside base 0 size s₀.mem s₃.mem := W₂.trans (O₃.mono (Nat.zero_le _) (by omega_arith))
  obtain x₄' : sv c base s₄ E = keyX c s₀ := by
    rw [x₄, bytesAt_keep W₃ (hpk.sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith) (by omega_arith)]
  obtain y₄' : sv c base s₄ QY = keyY c s₀ := by
    rw [y₄, bytesAt_keep W₃ (hpk.sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith) (by omega_arith)]
  obtain hq0 : s₃.mem (s₀.gpr .r3) = s₀.mem (s₀.gpr .r3) := by
    have := keep_of_disjoint' W₃ hpk (by omega_arith) (i := 0) (by omega_arith) (by omega_arith)
    rwa [BitVec.add_zero] at this
  obtain fl₃ : flagW c base s₃ = BitVec.allOnes 64 := by
    rw [flagW, U₃.word (fun w hw => (apart_slW (c := c) (l := [PT])
      (i := FLAG) (by decide) w hw).imp (fun h => by omega_arith) id) (by have := sl_le c h7 (i := FLAG) (by decide); omega_arith)]
    exact S₂.flag
  obtain hf₄ : flagW c base s₄ = mask64 (((s₀.mem (s₀.gpr .r3) = 4 ∧
      sv c base s₄ E < c.C.p) ∧ sv c base s₄ QY < c.C.p)) := by
    rw [f₄, hq0, fl₃, BitVec.allOnes_and, mask64_and, mask64_and]
  refine WP.seq (WP.mono (validate_ok hc K₄.ws K₄.fixed r2₄ bp₄ hf₄)
    fun s₅ ⟨hw₅, g₅, U₅, f₅, px_lt, py_lt, px, py⟩ => h s₅ ?_)
  obtain K₅ := K₄.step h7 g₅ (hU := U₅) (hW := fixedOk_valW h7) (hWs := valW_le h7)
  obtain e₅ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, W0, W1, W2, W3, PY] → i ≠ FLAG → sv c base s₅ i = sv c base s₄ i :=
    fun hi hl hf => sv_unch U₅ h7 hn hi (apart_append (apart_slW hl)
      (show ∀ w ∈ [(own c.n, 64 * c.n)] ++ [(c.sl FLAG, 8)], _ from
        apart_append (apart_own h7 hi) (apart_flag h0 hf)))
  obtain a₅ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, W0, W1, W2, W3, PY] → i ∉ [R2P, BP, E, QY] → i ≠ FLAG →
      i ≠ PT → sv c base s₅ i = sv c base s₂ i := fun hi h₁ h₂ hf hp =>
    ((e₅ hi h₁ hf).trans (e₄ hi h₂ hf)).trans (v₃ hi hp)
  obtain t₅ : ∀ {j}, j < 3 → ∀ t < 64 * c.n,
      s₅.mem (off base (bitsAt c.n j + t)) = s₂.mem (off base (bitsAt c.n j + t)) :=
    fun hj t ht => by
      rw [tbl_unch U₅ h7 hj ht (tbl_apart_valW h7 h0 _ t),
        tbl_unch U₄ h7 hj ht (apart_append (tbl_apart_slW h7 (by decide) _ t) (tbl_apart_flag h7 h0 _ t)),
        tbl_unch U₃ h7 hj ht (tbl_apart_slW h7 (by decide) _ t)]
  obtain hok : PeerOk c base s₄ ((s₀.mem (s₀.gpr .r3) = 4 ∧ sv c base s₄ E < c.C.p) ∧
      sv c base s₄ QY < c.C.p) = KeyOk c s₀ := by
    rw [PeerOk, x₄', y₄']
  simp only [hok] at f₅ px py
  rw [x₄'] at px
  rw [y₄'] at py
  refine ⟨K₅, ?_, ?_, ?_,
    by rw [a₅ (i := RX) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.rx],
    by rw [a₅ (i := RY) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.ry],
    by rw [a₅ (i := RZ) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.rz],
    fun t ht => by rw [t₅ (j := 1) (by decide) t ht, S₂.t₁ t ht],
    fun t ht => by rw [t₅ (j := 2) (by decide) t ht, S₂.t₂ t ht], f₅, px_lt, py_lt, px, py⟩
  · rw [a₅ (i := K) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.k]
    exact Nat.shiftRight_zero
  · rw [a₅ (i := D) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.d]
    show _ >>> shAt c (some D) D = _; rw [shAt_self]
  · rw [e₅ (i := PT) (by decide) (by decide) (by decide), e₄ (by decide) (by decide) (by decide)]
    exact e₃

end VG.Proof.Ecdsa.Verify.PPC64LE

end

end

/-!
# ECDSA verification on PPC64LE: `u` and `v`

As on 32-bit ARM (`Proof/Ecdsa/Verify/Arm/Final.lean`). `mid_ok`: the
masks of `r` and `s` in `[1, n-1]` into the flag, `w = s^(n-2)` in
Montgomery form modulo `n`, and `u = e w` and `v = r w`, out of it.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Proof.Ecdh.PPC64LE VG.Spec.Weierstrass
open VG.Impl.Ecdh.PPC64LE (PX PY)
open VG.Impl.Ecdsa.Verify.PPC64LE (SM' EM' RM' UM VM U V)

variable {c : Cfg}

/-- The slots `mid_ok` writes. -/
abbrev midW : List Nat := [SM', ACC, DX, DY, DZ, TX, TY, TZ, T0, T1, T2, EM', RM', UM, VM, U, V]

/-- After `u` and `v`. -/
structure Mid (c : Cfg) (s₀ : State) (base : Addr) (s : State) : Prop extends Keep c s₀ base s where
  rx : sv c base s RX = 0
  ry : sv c base s RY = c.mont 1
  rz : sv c base s RZ = 0
  t₁ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0
  flag : flagW c base s =
    mask64 (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n))
  px_lt : sv c base s PX < c.C.p
  py_lt : sv c base s PY < c.C.p
  px : toM c.C.p (2 ^ (64 * c.n)) (sv c base s PX) =
    if KeyOk c s₀ then Fin.ofNat c.C.p (keyX c s₀) else Fin.ofNat c.C.p c.C.gx
  py : toM c.C.p (2 ^ (64 * c.n)) (sv c base s PY) =
    if KeyOk c s₀ then Fin.ofNat c.C.p (keyY c s₀) else Fin.ofNat c.C.p c.C.gy
  rm_lt : sv c base s RM' < c.C.n
  rm : toM c.C.n (2 ^ (64 * c.n)) (sv c base s RM') = Fin.ofNat c.C.n (sigR c s₀)
  u_lt : sv c base s U < c.C.n
  u : Fin.ofNat c.C.n (sv c base s U) =
    Fin.ofNat c.C.n (dig c s₀) * Fin.ofNat c.C.n (sigS c s₀) ^ (c.C.n - 2)
  v_lt : sv c base s V < c.C.n
  v : Fin.ofNat c.C.n (sv c base s V) =
    Fin.ofNat c.C.n (sigR c s₀) * Fin.ofNat c.C.n (sigS c s₀) ^ (c.C.n - 2)

theorem scalars_eq (c : Cfg) : Impl.Ecdsa.Verify.PPC64LE.Cfg.scalars c =
    .seq (.block (c.checkRange (c.sl K) ++ c.checkRange (c.sl PT)))
      (mulCall c.SN (c.sl SM') (c.sl PT) (c.sl R2N)) := rfl

theorem uv_eq (c : Cfg) : Impl.Ecdsa.Verify.PPC64LE.Cfg.uv c =
    .seq (mulCall c.SN (c.sl EM') (c.sl D) (c.sl R2N))
    (.seq (mulCall c.SN (c.sl RM') (c.sl K) (c.sl R2N))
    (.seq (mulCall c.SN (c.sl UM) (c.sl EM') (c.sl ACC))
    (.seq (mulCall c.SN (c.sl VM) (c.sl RM') (c.sl ACC))
    (.seq (mulCall c.SN (c.sl U) (c.sl UM) (c.sl ONE))
      (mulCall c.SN (c.sl V) (c.sl VM) (c.sl ONE)))))) := rfl

/-- One multiplication modulo `n` from what the stages keep. -/
theorem mulN_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State} (K₀ : Keep c s₀ base s)
    {o a b : Nat} (ho : o < 45) (ha : a < 45) (hb : b < 45) (hoF : o = TMP ∨ 12 ≤ o) (hof : FLAG ≠ o)
    (hB : sv c base s b < c.C.n) :
    WP isa (mulCall c.SN (c.sl o) (c.sl a) (c.sl b)) s fun s' =>
      Keep c s₀ base s' ∧ flagW c base s' = flagW c base s ∧
      (∀ {j}, j < 3 → ∀ t < 64 * c.n,
        s'.mem (off base (bitsAt c.n j + t)) = s.mem (off base (bitsAt c.n j + t))) ∧
      (∀ {i}, i < 45 → i ≠ o → sv c base s' i = sv c base s i) ∧
      sv c base s' o < c.C.n ∧
      sv c base s' o * 2 ^ (64 * c.n) % c.C.n = sv c base s a * sv c base s b % c.C.n :=
  WP.mono (slMul_ok hc.fn hc.fnk hc.fnm hc.n10 K₀.ws ho ha hb hB) fun _ ⟨k, U, lt, e⟩ =>
    have := K₀.call hc.n0 hc.n10 ho hoF hof k U
    ⟨this.1, this.2.1, this.2.2.1, this.2.2.2, lt, e⟩

/-- The checks of `r` and `s`, `w = s^(n-2)`, `u` and `v`. -/
theorem mid_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State}
    (hF : Front c s₀ base s) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', Mid c s₀ base s' → WP isa rest s' Q) :
    WP isa (.seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.scalars c) (.seq c.invN
      (.seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.uv c) rest))) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hF.ws.nowrap
  have hsz : size = 8192 := rfl
  obtain hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have hn3 := hc.n_ge
  obtain hfl : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  obtain hl : ∀ {i}, i < 45 → c.sl i + 8 * c.n ≤ size := fun hi => by have := sl_le c h7 hi; omega_arith
  obtain hr2lt : 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n < c.C.n := Nat.mod_lt _ (by omega_arith)
  rw [scalars_eq]
  -- The checks.
  refine WP.seq (WP.seq ?_)
  refine wp_append (WP.mono (checkRange_ok c hF.ws.ws hF.ws.at3 (sl_al c K) h0 (hl (by decide)) (hl (by decide)) hfl)
    fun s₁ ⟨f₁, k₁, O₁⟩ => ?_)
  obtain K₁ := hF.toKeep.step h7 (k₁.rk (rs' := [.r0, .r4, .r5, .r6, .r7, .r8, .r9])) (hU := O₁.unch)
    (hW := fixedOk_flag) (hWs := flag_le h7)
  refine WP.mono (checkRange_ok c K₁.ws.ws K₁.ws.at3 (sl_al c PT) h0 (hl (by decide)) (hl (by decide)) hfl)
    fun s₂ ⟨f₂, k₂, O₂⟩ => ?_
  obtain K₂ := K₁.step h7 (k₂.rk (rs' := [.r0, .r4, .r5, .r6, .r7, .r8, .r9])) (hU := O₂.unch)
    (hW := fixedOk_flag) (hWs := flag_le h7)
  obtain v₂ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₂ i = sv c base s i := fun hi hf =>
    (sv_unch O₂.unch h7 hn hi (apart_flag h0 hf)).trans (sv_unch O₁.unch h7 hn hi (apart_flag h0 hf))
  obtain t₂ : ∀ {j}, j < 3 → ∀ t < 64 * c.n,
      s₂.mem (off base (bitsAt c.n j + t)) = s.mem (off base (bitsAt c.n j + t)) := fun hj t ht => by
    rw [tbl_unch O₂.unch h7 hj ht (tbl_apart_flag h7 h0 _ t), tbl_unch O₁.unch h7 hj ht (tbl_apart_flag h7 h0 _ t)]
  obtain flag₂ : flagW c base s₂ =
      mask64 (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) := by
    have hk : wordsVal s.mem base (c.sl K) c.n = sigR c s₀ := hF.k
    have hmn : wordsVal s.mem base (c.sl MN) c.n = c.C.n := hF.fixed.mn
    obtain hpt₁ : wordsVal s₁.mem base (c.sl PT) c.n = sigS c s₀ :=
      (sv_unch O₁.unch h7 hn (i := PT) (by decide) (apart_flag h0 (by decide))).trans hF.pt
    have hmn₁ : wordsVal s₁.mem base (c.sl MN) c.n = c.C.n := K₁.fixed.mn
    rw [f₂, f₁, hF.flag, mask64_and, mask64_and, hmn₁, hmn, hk, hpt₁]
    simp only [and_assoc]
  -- `s R mod n`.
  refine WP.mono (mulN_ok hc K₂ (o := SM') (a := PT) (b := R2N) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [show sv c base s₂ R2N = _ from K₂.fixed.r2n]; exact hr2lt))
    fun s₃ ⟨K₃, f₃, t₃, v₃, lt₃, e₃⟩ => ?_
  obtain sm₃ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₃ SM') = Fin.ofNat c.C.n (sigS c s₀) := by
    rw [toM_r2 hnR (by rw [e₃, show sv c base s₂ R2N = _ from K₂.fixed.r2n]), v₂ (by decide) (by decide), hF.pt]
  -- `w = s^(n-2)`.
  refine WP.seq (WP.mono (chainPow_ok (P := c.chainN) (S := c.SN) (e := c.C.n - 2) hc.fnk hc.fnm (modN hc)
    (chainLayN hc) hnR K₃.ws (show sv c base s₃ KM < c.C.n from lt₃) hc.chainN) fun s₄ ⟨k₄, U₄, lt₄, w₄⟩ => ?_)
  rw [chainWN_eq] at U₄
  obtain K₄ := K₃.step h7 k₄ (hU := U₄) (hW := fixedOk_chainW h7) (hWs := chainW_le h7)
  obtain e₄ : ∀ {i}, i < 45 → i ≠ ACC → (i < DX ∨ T2 < i) → sv c base s₄ i = sv c base s₃ i := fun hi hr ht =>
    sv_unch U₄ h7 hn hi (apart_chainW h7 hi hr ht)
  obtain f₄ : flagW c base s₄ = flagW c base s₃ := by
    simp only [flagW]
    exact U₄.word (fun w hw => by
      rcases apart_chainW h7 (i := FLAG) (by decide) (by decide) (by decide) w hw with h | h
      · exact Or.inl (by omega_arith)
      · exact Or.inr h) (by have := sl_le c h7 (i := FLAG) (by decide); omega_arith)
  obtain t₄ : ∀ {j}, j < 3 → ∀ t < 64 * c.n,
      s₄.mem (off base (bitsAt c.n j + t)) = s₃.mem (off base (bitsAt c.n j + t)) := fun {j} hj t ht =>
    tbl_unch U₄ h7 hj ht (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact Or.inr (sl_below_bits c h7 (i := ACC) (by decide) j t)
      · have h26 := sl_below_bits c h7 (i := 26) (by decide) j t
        rw [sl_eq] at h26
        refine Or.inr ?_
        show c.sl 17 + 9 * (8 * c.n) ≤ _
        rw [sl_eq]; omega_using [h26]
      · exact tbl_apart_own h7 j t _ (List.mem_singleton_self _))
  obtain w₄' : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₄ ACC) = Fin.ofNat c.C.n (sigS c s₀) ^ (c.C.n - 2) := by
    rw [← sm₃]; exact w₄
  -- `u` and `v`.
  rw [uv_eq]
  refine WP.seq ?_
  refine WP.seq (WP.mono (mulN_ok hc K₄ (o := EM') (a := D) (b := R2N) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [show sv c base s₄ R2N = _ from K₄.fixed.r2n]; exact hr2lt))
    fun s₅ ⟨K₅, f₅, t₅, v₅, lt₅, e₅⟩ => ?_)
  refine WP.seq (WP.mono (mulN_ok hc K₅ (o := RM') (a := K) (b := R2N) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [show sv c base s₅ R2N = _ from K₅.fixed.r2n]; exact hr2lt))
    fun s₆ ⟨K₆, f₆, t₆, v₆, lt₆, e₆⟩ => ?_)
  obtain acc₆ : sv c base s₆ ACC = sv c base s₄ ACC := by
    rw [v₆ (by decide) (by decide), v₅ (by decide) (by decide)]
  refine WP.seq (WP.mono (mulN_ok hc K₆ (o := UM) (a := EM') (b := ACC) (by decide) (by decide) (by decide)
    (by decide) (by decide) (acc₆ ▸ lt₄)) fun s₇ ⟨K₇, f₇, t₇, v₇, lt₇, e₇⟩ => ?_)
  obtain acc₇ : sv c base s₇ ACC = sv c base s₄ ACC := by rw [v₇ (by decide) (by decide), acc₆]
  refine WP.seq (WP.mono (mulN_ok hc K₇ (o := VM) (a := RM') (b := ACC) (by decide) (by decide) (by decide)
    (by decide) (by decide) (acc₇ ▸ lt₄)) fun s₈ ⟨K₈, f₈, t₈, v₈, lt₈, e₈⟩ => ?_)
  refine WP.seq (WP.mono (mulN_ok hc K₈ (o := U) (a := UM) (b := ONE) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [show sv c base s₈ ONE = 1 from K₈.fixed.one]; omega_arith))
    fun s₉ ⟨K₉, f₉, t₉, v₉, lt₉, e₉⟩ => ?_)
  refine WP.mono (mulN_ok hc K₉ (o := V) (a := VM) (b := ONE) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [show sv c base s₉ ONE = 1 from K₉.fixed.one]; omega_arith))
    fun s₁₀ ⟨K₁₀, f₁₀, t₁₀, v₁₀, lt₁₀, e₁₀⟩ => h s₁₀ ?_
  -- What reaches `s₁₀` from `s`.
  obtain a : ∀ {i}, i < 45 → i ∉ midW → i ≠ FLAG → sv c base s₁₀ i = sv c base s i := fun {i} hi hl hf => by
    simp only [midW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hl
    obtain ⟨h1, h2, d1, d2, d3, d4, d5, d6, d7, d8, d9, h4, h5, h6, h7', h8, h9⟩ := hl
    -- one `decide` over the slots: `omega` splits a case for every slot `i` is not
    obtain ht : i < DX ∨ T2 < i :=
      (by decide : ∀ i < 45, i ≠ DX ∧ i ≠ DY ∧ i ≠ DZ ∧ i ≠ TX ∧ i ≠ TY ∧ i ≠ TZ ∧ i ≠ T0 ∧ i ≠ T1 ∧ i ≠ T2 →
        i < DX ∨ T2 < i) i hi ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩
    rw [v₁₀ hi h9, v₉ hi h8, v₈ hi h7', v₇ hi h6, v₆ hi h5, v₅ hi h4, e₄ hi h2 ht, v₃ hi h1,
      v₂ hi hf]
  -- The values.
  obtain d₄ : sv c base s₄ D = dig c s₀ := by
    rw [e₄ (by decide) (by decide) (by decide), v₃ (by decide) (by decide), v₂ (by decide) (by decide), hF.d]
  obtain k₄ : sv c base s₄ K = sigR c s₀ := by
    rw [e₄ (by decide) (by decide) (by decide), v₃ (by decide) (by decide), v₂ (by decide) (by decide), hF.k]
  obtain em₆ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₆ EM') = Fin.ofNat c.C.n (dig c s₀) := by
    rw [v₆ (i := EM') (by decide) (by decide),
      toM_r2 hnR (by rw [e₅, show sv c base s₄ R2N = _ from K₄.fixed.r2n]), d₄]
  obtain rm₆ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₆ RM') = Fin.ofNat c.C.n (sigR c s₀) := by
    rw [toM_r2 hnR (by rw [e₆, show sv c base s₅ R2N = _ from K₅.fixed.r2n]),
      v₅ (i := K) (by decide) (by decide), k₄]
  obtain um₈ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₈ UM) =
      Fin.ofNat c.C.n (dig c s₀) * Fin.ofNat c.C.n (sigS c s₀) ^ (c.C.n - 2) := by
    rw [v₈ (i := UM) (by decide) (by decide), toM_mul hnR e₇, em₆, acc₆, w₄']
  obtain vm₈ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₈ VM) =
      Fin.ofNat c.C.n (sigR c s₀) * Fin.ofNat c.C.n (sigS c s₀) ^ (c.C.n - 2) := by
    rw [toM_mul hnR e₈, v₇ (i := RM') (by decide) (by decide), rm₆, acc₇, w₄']
  refine ⟨K₁₀,
    by rw [a (i := RX) (by decide) (by decide) (by decide), hF.rx],
    by rw [a (i := RY) (by decide) (by decide) (by decide), hF.ry],
    by rw [a (i := RZ) (by decide) (by decide) (by decide), hF.rz], fun t ht => ?_,
    by rw [f₁₀, f₉, f₈, f₇, f₆, f₅, f₄, f₃, flag₂],
    by rw [a (i := PX) (by decide) (by decide) (by decide)]; exact hF.px_lt,
    by rw [a (i := PY) (by decide) (by decide) (by decide)]; exact hF.py_lt,
    by rw [a (i := PX) (by decide) (by decide) (by decide)]; exact hF.px,
    by rw [a (i := PY) (by decide) (by decide) (by decide)]; exact hF.py,
    by rw [v₁₀ (by decide) (by decide), v₉ (by decide) (by decide), v₈ (by decide) (by decide),
      v₇ (by decide) (by decide)]; exact lt₆,
    by rw [v₁₀ (by decide) (by decide), v₉ (by decide) (by decide), v₈ (by decide) (by decide),
      v₇ (by decide) (by decide), rm₆],
    by rw [v₁₀ (by decide) (by decide)]; exact lt₉,
    by rw [v₁₀ (i := U) (by decide) (by decide),
      toM_one_mul hnR (by rw [e₉, show sv c base s₈ ONE = 1 from K₈.fixed.one]), um₈],
    lt₁₀,
    by rw [toM_one_mul hnR (by rw [e₁₀, show sv c base s₉ ONE = 1 from K₉.fixed.one]),
      v₉ (i := VM) (by decide) (by decide), vm₈]⟩
  rw [t₁₀ (j := 1) (by decide) t ht, t₉ (j := 1) (by decide) t ht, t₈ (j := 1) (by decide) t ht,
    t₇ (j := 1) (by decide) t ht, t₆ (j := 1) (by decide) t ht, t₅ (j := 1) (by decide) t ht,
    t₄ (j := 1) (by decide) t ht, t₃ (j := 1) (by decide) t ht, t₂ (j := 1) (by decide) t ht]
  exact hF.t₁ t ht

end VG.Proof.Ecdsa.Verify.PPC64LE

end

end

/-!
# ECDSA verification on PPC64LE: `[u]G + [v]Q`

As on 32-bit ARM (`Proof/Ecdsa/Verify/Arm/Points.lean`): `save_ok` copies
`R` to `U` and resets `R` to `O`; `sum_ok` is `R = U + R` by the complete
addition (`rcbR_ok` on the slots it names); `points_ok` is `[u]G` by the
signature's ladder, `save`, `[v]Q` by ECDH's, and the sum.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Weierstrass.PPC64LE.Point VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Weierstrass.PPC64LE.Point VG.Proof.Ecdsa.PPC64LE
  VG.Proof.Ecdh.PPC64LE VG.Spec.Weierstrass
open VG.Impl.Ecdh.PPC64LE (PX PY)
open VG.Impl.Ecdsa.Verify.PPC64LE (SM' EM' RM' UM VM U V UX UY UZ)

variable {c : Cfg}

/-- `[o] = x`, on numbered slots. -/
theorem setSl_ok (hc : CfgOk c) {s : State} {base : Addr} (hw : WsReg s base) {o x : Nat}
    (ho : o < 45) (hx : x < 2 ^ (64 * c.n)) :
    WP isa (.block (VG.Impl.Mont.PPC64LE.setConst c.n (c.sl o) x)) s fun s' =>
      sv c base s' o = x ∧ Kp [.r11] s s' ∧ Outside base (c.sl o) (8 * c.n) s.mem s'.mem := by
  have := sl_le c hc.n10 ho
  have hsz : size = 8192 := rfl
  refine WP.mono (setConst_ok (size := size) hw.ws hw.at3 (o := c.sl o) (by omega_arith) hx) fun s' ⟨O, e, k⟩ =>
    ⟨?_, k, O⟩
  show wordsVal _ _ _ _ = _
  rw [wordsVal_eq_val32]; exact e

/-- The slots `save` writes. -/
abbrev saveW : List Nat := [UX, UY, UZ, RX, RY, RZ]

theorem save_eq (c : Cfg) : Impl.Ecdsa.Verify.PPC64LE.Cfg.save c =
    copy c.n (c.sl UX) (c.sl RX) ++ (copy c.n (c.sl UY) (c.sl RY) ++
    (copy c.n (c.sl UZ) (c.sl RZ) ++ (VG.Impl.Mont.PPC64LE.setConst c.n (c.sl RX) 0 ++
    (VG.Impl.Mont.PPC64LE.setConst c.n (c.sl RY) (c.mont 1) ++
      VG.Impl.Mont.PPC64LE.setConst c.n (c.sl RZ) 0)))) := by
  simp only [Impl.Ecdsa.Verify.PPC64LE.Cfg.save, List.append_assoc]

/-- `U = R`, and `R = O`. -/
theorem save_ok (hc : CfgOk c) {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block (Impl.Ecdsa.Verify.PPC64LE.Cfg.save c)) s fun s' =>
      Kp [.r4, .r11] s s' ∧ Unch base (slW c saveW) s.mem s'.mem ∧
      sv c base s' UX = sv c base s RX ∧ sv c base s' UY = sv c base s RY ∧
      sv c base s' UZ = sv c base s RZ ∧ sv c base s' RX = 0 ∧ sv c base s' RY = c.mont 1 ∧
      sv c base s' RZ = 0 := by
  have h7 := hc.n10
  have hn := hw.nowrap
  have hp := hc.p_lt
  have hp3 := hc.p_ge
  obtain hm1 : c.mont 1 < 2 ^ (64 * c.n) := by
    have : c.mont 1 < c.C.p := Nat.mod_lt _ (by omega_arith)
    omega_arith
  rw [save_eq]
  refine wp_append (WP.mono (copySl_ok hc hw (o := UX) (a := RX) (by decide) (by decide) (by decide))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
  obtain hw₁ := hw.of_kp k₁
  refine wp_append (WP.mono (copySl_ok hc hw₁ (o := UY) (a := RY) (by decide) (by decide) (by decide))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  obtain hw₂ := hw₁.of_kp k₂
  refine wp_append (WP.mono (copySl_ok hc hw₂ (o := UZ) (a := RZ) (by decide) (by decide) (by decide))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_)
  obtain hw₃ := hw₂.of_kp k₃
  refine wp_append (WP.mono (setSl_ok hc hw₃ (o := RX) (x := 0) (by decide) (Nat.two_pow_pos _))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_)
  obtain hw₄ := hw₃.of_kp k₄
  refine wp_append (WP.mono (setSl_ok hc hw₄ (o := RY) (by decide) hm1) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_)
  obtain hw₅ := hw₄.of_kp k₅
  refine WP.mono (setSl_ok hc hw₅ (o := RZ) (x := 0) (by decide) (Nat.two_pow_pos _))
    fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  obtain o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
      sv c base s' i = sv c base s i := fun {_ _ j _} O hi hij =>
    sv_unch O.unch h7 hn hi (apart_slW (c := c) (l := [j]) (by simpa using hij))
  refine ⟨(((((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans (k₃.mono (by decide))).trans
      (k₄.mono (by decide))).trans (k₅.mono (by decide))).trans (k₆.mono (by decide)), ?_,
    ?_, ?_, ?_, ?_, ?_, e₆⟩
  · have := O₁.unch.trans (O₂.unch.trans (O₃.unch.trans (O₄.unch.trans (O₅.unch.trans O₆.unch))))
    exact this.mono fun w hw => by simpa [saveW, slW] using hw
  · rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), o O₄ (by decide) (by decide),
      o O₃ (by decide) (by decide), o O₂ (by decide) (by decide), e₁]
  · rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), o O₄ (by decide) (by decide),
      o O₃ (by decide) (by decide), e₂, o O₁ (by decide) (by decide)]
  · rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), o O₄ (by decide) (by decide), e₃,
      o O₂ (by decide) (by decide), o O₁ (by decide) (by decide)]
  · rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), e₄]
  · rw [o O₆ (by decide) (by decide), e₅]

/-- The slots of `rcb`'s numbered operands in the sum: `D`, `U`, `R`, `a`,
`3b` and the temporaries. -/
def sumIdx : List Nat := [DX, DY, DZ, UX, UY, UZ, RX, RY, RZ, AP, B3P, T0, T1, T2, T3, T4, T5]

/-- The offsets of `rcb`'s numbered operands in the sum. -/
abbrev sumσ (c : Cfg) (i : Nat) : Nat := c.sl (sumIdx.getD i 0)

theorem sum_fprog (c : Cfg) : fprog c.SP (rcb c.rcbSlots (c.pt UX UY UZ) (c.pt RX RY RZ) (c.pt DX DY DZ)) =
    fprogR (sumσ c) c.SP (rcb sId pId qId oId) := rfl

theorem sumIdx_lt : ∀ i < 17, sumIdx.getD i 0 < 45 := by decide

theorem sumIdx_inj : ∀ i < 17, ∀ j < 17, sumIdx.getD i 0 = sumIdx.getD j 0 → i = j := by decide

theorem sumLay (h7 : c.n < 10) : LayR c.n 17 wIds (sumσ c) where
  le := fun x hx => sl_below_own c h7 (sumIdx_lt x hx)
  apart := fun w hw x hx hxw => sl_apart c fun h => hxw (sumIdx_inj x hx w (by
    simp only [wIds, List.mem_cons, List.not_mem_nil, or_false] at hw; omega_arith) h)

/-- The sum over any modulus `S` of `c.n` words, `m`. -/
theorem sum_core {S : Impl.Weierstrass.Mont.Modulus} {m : Nat} [NeZero m] (hkS : S.k = c.n) (hmS : S.m = m)
    (hM : ModOk c.n m) (h7 : c.n < 10) (hm : UnitMod m (2 ^ (64 * c.n))) {base : Addr} {s : State}
    (hw : WsReg s base) (hlt : ∀ x ∈ rIds, wordsVal s.mem base (sumσ c x) c.n < m) :
    WP isa (fprogR (sumσ c) S (rcb sId pId qId oId)) s fun s' =>
      KeepR c.n (sumσ c) base wIds s s' ∧
      InvR c.n 17 (sumσ c) base m (validAfter (rcb sId pId qId oId) rIds)
        (runOps (rcb sId pId qId oId) fun x => toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (sumσ c x) c.n)) s' ∧
      (runOps (rcb sId pId qId oId) (fun x => toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (sumσ c x) c.n)) 0,
        runOps (rcb sId pId qId oId) (fun x => toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (sumσ c x) c.n)) 1,
        runOps (rcb sId pId qId oId) (fun x => toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (sumσ c x) c.n)) 2) =
        VG.Proof.Weierstrass.rcbAdd
          (toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (sumσ c 9) c.n))
          (toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (sumσ c 10) c.n))
          (toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (sumσ c 3) c.n))
          (toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (sumσ c 4) c.n))
          (toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (sumσ c 5) c.n))
          (toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (sumσ c 6) c.n))
          (toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (sumσ c 7) c.n))
          (toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (sumσ c 8) c.n)) := by
  obtain ⟨cv, w, m', k', d⟩ := S
  dsimp only at hkS hmS
  subst hkS hmS
  exact rcbR_ok (S := ⟨cv, w, m', c.n, d⟩) hM rfl (sumLay h7) hm
    ⟨hw, by decide, hlt, fun _ _ => rfl⟩

/-- The slots `sum` writes. -/
abbrev sumW : List Nat := [DX, DY, DZ, T0, T1, T2, T3, T4, T5, RX, RY, RZ]

theorem sum_eq (c : Cfg) : Impl.Ecdsa.Verify.PPC64LE.Cfg.sum c =
    .seq (fprogR (sumσ c) c.SP (rcb sId pId qId oId))
      (.block (copy c.n (c.sl RX) (c.sl DX) ++ (copy c.n (c.sl RY) (c.sl DY) ++ copy c.n (c.sl RZ) (c.sl DZ)))) := by
  rw [Impl.Ecdsa.Verify.PPC64LE.Cfg.sum, sum_fprog, List.append_assoc]

/-- `R = U + R`, by the complete addition. -/
theorem sum_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State} (K₀ : Keep c s₀ base s)
    (hlt : ∀ i ∈ [AP, B3P, UX, UY, UZ, RX, RY, RZ], sv c base s i < c.C.p) :
    WP isa (Impl.Ecdsa.Verify.PPC64LE.Cfg.sum c) s fun s' =>
      Keep c s₀ base s' ∧ Unch base (slW c sumW ++ [(own c.n, 64 * c.n)]) s.mem s'.mem ∧
      sv c base s' RX < c.C.p ∧ sv c base s' RY < c.C.p ∧ sv c base s' RZ < c.C.p ∧
      (tmv c.C c.n base s' (c.sl RX), tmv c.C c.n base s' (c.sl RY), tmv c.C c.n base s' (c.sl RZ)) =
        rcbAdd (tmv c.C c.n base s (c.sl AP)) (tmv c.C c.n base s (c.sl B3P))
          (tmv c.C c.n base s (c.sl UX)) (tmv c.C c.n base s (c.sl UY)) (tmv c.C c.n base s (c.sl UZ))
          (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY)) (tmv c.C c.n base s (c.sl RZ)) := by
  have h7 := hc.n10
  have hn := K₀.ws.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  obtain hM : ModOk c.n c.C.p := by have := hc.fp; rw [hc.fpk, hc.fpm] at this; exact this
  rw [sum_eq]
  refine WP.seq (WP.mono (sum_core hc.fpk hc.fpm hM h7 hpR K₀.ws (fun x hx => ?_)) fun s₁ ⟨KR, I₁, t₁⟩ => ?_)
  · simp only [rIds, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hlt _ (by decide)
  have UR : Unch base (slW c [DX, DY, DZ, T0, T1, T2, T3, T4, T5] ++ [(own c.n, 64 * c.n)]) s.mem s₁.mem := KR.mem
  obtain K₁ := K₀.step h7 (rs := fnClob) ⟨KR.gpr, KR.rd, KR.wr, KR.sp⟩ (hU := UR)
    (hW := (fixedOk_slW (by decide)).append (fun w hw => by
      rw [List.mem_singleton.mp hw]
      exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_own c h7 (i := 12) (by decide)))))
    (hWs := le_append (slW_le h7 (by decide)) (fun w hw => by
      rw [List.mem_singleton.mp hw]; have := own_below_bits c h7 0; have := bitsAt_le c h7 (j := 0) (by decide)
      dsimp only; omega_arith))
  refine wp_append (WP.mono (copySl_ok hc K₁.ws (o := RX) (a := DX) (by decide) (by decide) (by decide))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  obtain hw₂ := K₁.ws.of_kp k₂
  refine wp_append (WP.mono (copySl_ok hc hw₂ (o := RY) (a := DY) (by decide) (by decide) (by decide))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_)
  obtain hw₃ := hw₂.of_kp k₃
  refine WP.mono (copySl_ok hc hw₃ (o := RZ) (a := DZ) (by decide) (by decide) (by decide))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  obtain o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
      sv c base s' i = sv c base s i := fun {_ _ j _} O hi hij =>
    sv_unch O.unch h7 hn hi (apart_slW (c := c) (l := [j]) (by simpa using hij))
  obtain x₄ : sv c base s₄ RX = sv c base s₁ DX := by
    rw [o O₄ (by decide) (by decide), o O₃ (by decide) (by decide), e₂]
  obtain y₄ : sv c base s₄ RY = sv c base s₁ DY := by
    rw [o O₄ (by decide) (by decide), e₃, o O₂ (by decide) (by decide)]
  obtain z₄ : sv c base s₄ RZ = sv c base s₁ DZ := by
    rw [e₄, o O₃ (by decide) (by decide), o O₂ (by decide) (by decide)]
  obtain U₄ : Unch base (slW c [RX, RY, RZ]) s₁.mem s₄.mem := by
    have := O₂.unch.trans (O₃.unch.trans O₄.unch)
    exact this.mono fun w hw => by simpa [slW] using hw
  obtain K₄ := K₁.step h7 ((k₂.trans (k₃.trans k₄)).rk (rs' := [.r4])) (hU := U₄)
    (hW := fixedOk_slW (by decide)) (hWs := slW_le h7 (by decide))
  obtain hD : ∀ i ∈ [0, 1, 2], i ∈ validAfter (rcb sId pId qId oId) rIds := by decide
  obtain l₀ := I₁.lt 0 (hD 0 (by decide))
  obtain l₁ := I₁.lt 1 (hD 1 (by decide))
  obtain l₂ := I₁.lt 2 (hD 2 (by decide))
  refine ⟨K₄, (UR.trans U₄).mono fun w hw => ?_, by rw [x₄]; exact l₀, by rw [y₄]; exact l₁,
    by rw [z₄]; exact l₂, ?_⟩
  · simp only [slW, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hw ⊢
    grind
  · show (toM _ _ (sv c base s₄ RX), toM _ _ (sv c base s₄ RY), toM _ _ (sv c base s₄ RZ)) = _
    rw [x₄, y₄, z₄]
    exact (congrArg₂ Prod.mk (I₁.val 0 (hD 0 (by decide)))
      (congrArg₂ Prod.mk (I₁.val 1 (hD 1 (by decide))) (I₁.val 2 (hD 2 (by decide))))).trans t₁

/-- After `[u]G + [v]Q`: `R` represents `[u]G + [v]P`. -/
structure Pts (c : Cfg) (s₀ : State) (base : Addr) (u v : Nat) (P : Point c.C) (s : State) : Prop
    extends Keep c s₀ base s where
  t₁ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0
  flag : flagW c base s =
    mask64 (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n))
  rm_lt : sv c base s RM' < c.C.n
  rm : toM c.C.n (2 ^ (64 * c.n)) (sv c base s RM') = Fin.ofNat c.C.n (sigR c s₀)
  rz_lt : sv c base s RZ < c.C.p
  pt : Rep c.C (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY)) (tmv c.C c.n base s (c.sl RZ))
    (add (mul u (G c.C)) (mul v P))

/-- What `scalarAt` writes: `K`'s slot (for `vg_<curve>_mul`) or the table
of bits. -/
abbrev scW (c : Cfg) : List (Nat × Nat) := slW c [K] ++ [(bitsAt c.n 0, 64 * c.n)]

theorem apart_scW (h7 : c.n < 10) {i : Nat} (hi : i < 45) (hK : i ≠ K) :
    ∀ w ∈ scW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_slW (by simpa using hK)) (apart_tbl h7 hi 0)

theorem fixedOk_scW (h7 : c.n < 10) : FixedOk c (scW c) :=
  (fixedOk_slW (by decide)).append (fixedOk_tbl h7 0)

theorem scW_le (h7 : c.n < 10) : ∀ w ∈ scW c, w.1 + w.2 ≤ size :=
  le_append (slW_le h7 (by decide)) fun w hw => by rw [List.mem_singleton.mp hw]; exact bitsAt_le c h7 (by decide)

theorem tbl_apart_scW (h7 : c.n < 10) {j t : Nat} (hj : j ≠ 0) (ht : t < 64 * c.n) :
    ∀ w ∈ scW c, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t :=
  apart_append (tbl_apart_slW h7 (by decide) j t) (tbl_apart_tbl hj ht)

/-- The scalar at slot `i` to where the multiplication reads it: `K`'s slot
for `vg_<curve>_mul`, else the table of its bits. -/
theorem scalarAt_ok (hc : CfgOk c) {s : State} {base : Addr} (hw : WsReg s base) {i : Nat} (hi : i < 45)
    (hK : i ≠ K) :
    WP isa (Impl.Ecdsa.Verify.PPC64LE.Cfg.scalarAt c i) s fun s' => Kp bitsClob s s' ∧
      Unch base (scW c) s.mem s'.mem ∧ (c.mul.isSome → sv c base s' K = sv c base s i) ∧
      (c.mul = none → ∀ t < 64 * c.n, s'.mem (off base (bitsAt c.n 0 + t)) =
        if (sv c base s i).testBit t then 1 else 0) := by
  unfold Impl.Ecdsa.Verify.PPC64LE.Cfg.scalarAt
  split
  · next C hC =>
    refine WP.mono (copySl_ok hc hw (o := K) (a := i) (by decide) hi (Ne.symm hK)) fun s' ⟨x, k, O⟩ =>
      ⟨k.mono, O.unch.mono fun w hw => List.mem_append_left _ (by simpa using hw), fun _ => x, fun h => ?_⟩
    rw [hC] at h; exact absurd h (by simp)
  · next hN =>
    refine WP.mono (tbl_bits_ok hc hw (i := i) (j := 0) hi (by decide)) fun s' ⟨b, k, O⟩ =>
      ⟨k, O.unch.mono fun w hw => List.mem_append_right _ hw, fun h => ?_, fun _ => b⟩
    rw [hN] at h; exact absurd h (by simp)

theorem ladders_eq (c : Cfg) : Impl.Ecdsa.Verify.PPC64LE.Cfg.ladders c =
    .seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.scalarAt c U) (.seq (c.qMul GX GY)
      (.seq (.block (Impl.Ecdsa.Verify.PPC64LE.Cfg.save c)) (.seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.scalarAt c V)
      (.seq (c.qMul PX PY) (Impl.Ecdsa.Verify.PPC64LE.Cfg.sum c))))) := rfl

/-- The slots the multiplications, `save` and the sum write. -/
abbrev ptsW : List Nat := [RX, RY, RZ, UX, UY, UZ, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP, K, ACC, PT]

/-- `[u]G + [v]Q`, into `R`, by the two ladders and the sum. -/
theorem ladders_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) (hC : Law c.C) {s₀ : State} {base : Addr}
    {s : State} (hM : Mid c s₀ base s) {P : Point c.C} (hP : onCurve c.C P = true)
    (hQ : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY)) (tmv c.C c.n base s (c.sl ONEP)) P)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', Pts c s₀ base (sv c base s U) (sv c base s V) P s' → WP isa rest s' Q) :
    WP isa (.seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.ladders c) rest) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hM.ws.nowrap
  have hsz : size = 8192 := rfl
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  obtain hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  have F := hM.fixed
  obtain ha : ∀ {t : State}, Fixed c base s₀.gpr s₀.lr t.mem → tmv c.C c.n base t (c.sl AP) = Fin.ofNat c.C.p c.C.a :=
    fun F => by show toM _ _ (wordsVal _ base (c.sl AP) c.n) = _; rw [F.ap]; exact toM_cmont hc _
  obtain hb : ∀ {t : State}, Fixed c base s₀.gpr s₀.lr t.mem →
      tmv c.C c.n base t (c.sl B3P) = Fin.ofNat c.C.p (3 * c.C.b) :=
    fun F => by show toM _ _ (wordsVal _ base (c.sl B3P) c.n) = _; rw [F.b3p]; exact toM_cmont hc _
  obtain hz : ∀ {t : State}, Fixed c base s₀.gpr s₀.lr t.mem → sv c base t ZERO = 0 := fun F => F.zero
  obtain h1 : ∀ {t : State}, Fixed c base s₀.gpr s₀.lr t.mem → sv c base t ONEP = c.mont 1 := fun F => by
    rw [show sv c base _ ONEP = 2 ^ (64 * c.n) % c.C.p from F.onep, Cfg.mont, Cfg.R, Nat.one_mul]
  -- `O`, as zero and one hold it, stands for `[k]P` for any `k` of `8 len` bits.
  obtain hO : ∀ {t : State} {k : Nat} {P : Point c.C}, Fixed c base s₀.gpr s₀.lr t.mem → k < 2 ^ (8 * c.C.len) →
      Rep c.C (tmv c.C c.n base t (c.sl ZERO)) (tmv c.C c.n base t (c.sl ONEP)) (tmv c.C c.n base t (c.sl ZERO))
        (mul (k >>> (8 * c.C.len)) P) := fun F hk => by
    show Rep c.C (toM _ _ (sv c base _ ZERO)) (toM _ _ (sv c base _ ONEP)) (toM _ _ (sv c base _ ZERO)) _
    rw [hz F, h1 F, toM_cmont hc, toM_zero, shiftRight_eq_zero hk, mul_zero_pt]
    exact rep_infinity' hC
  obtain hW : FixedOk c (ladWp (ladderAt c GX GY) ++ genX c) := (fixedOk_ladWp h3 h7 GX GY).append (fixedOk_genX h7)
  obtain hWs : ∀ w ∈ ladWp (ladderAt c GX GY) ++ genX c, w.1 + w.2 ≤ size :=
    le_append (ladWp_le h3 h7 GX GY) (genX_le h7)
  obtain apL : ∀ {gx gy i : Nat}, i < 45 → i ∉ ACC :: PT :: ladIx → ∀ w ∈ ladWp (ladderAt c gx gy) ++ genX c,
      c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := fun hi hl =>
    apart_append (apart_ladWp h3 h7 hi (nmem_of hl (by decide))) (apart_genX h7 hi (nmem_of hl (by decide)))
  obtain tbL : ∀ {gx gy j t : Nat}, j ≠ 0 → t < 64 * c.n → ∀ w ∈ ladWp (ladderAt c gx gy) ++ genX c,
      bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := fun hj ht =>
    apart_append (tbl_apart_ladWp h3 h7 _ _ _ _) (tbl_apart_genX h7 hj ht)
  rw [ladders_eq]
  refine WP.seq ?_
  -- `u` to where the multiplication reads it.
  refine WP.seq (WP.mono (scalarAt_ok hc hM.ws (i := U) (by decide) (by decide)) fun s₁ ⟨k₁, U₁, sk₁, b₁⟩ => ?_)
  obtain K₁ := hM.toKeep.step h7 (k₁.rk (rs' := bitsClob)) (hU := U₁) (hW := fixedOk_scW h7) (hWs := scW_le h7)
  obtain v₁ : ∀ {i}, i < 45 → i ≠ K → sv c base s₁ i = sv c base s i := fun hi hK =>
    sv_unch U₁ h7 hn hi (apart_scW h7 hi hK)
  -- `[u]G`.
  obtain hu : sv c base s U < 2 ^ (8 * c.C.len) := Nat.lt_trans hM.u_lt hc.n_enc
  obtain hG₁ : Rep c.C (tmv c.C c.n base s₁ (c.sl GX)) (tmv c.C c.n base s₁ (c.sl GY))
      (tmv c.C c.n base s₁ (c.sl ONEP)) (G c.C) := by
    show Rep c.C (toM _ _ (wordsVal s₁.mem _ (c.sl GX) c.n)) (toM _ _ (wordsVal s₁.mem _ (c.sl GY) c.n))
      (toM _ _ (wordsVal s₁.mem _ (c.sl ONEP) c.n)) (G c.C)
    rw [K₁.fixed.gx, K₁.fixed.gy, K₁.fixed.onep, toM_cmont hc, toM_cmont hc, toM_one hpR]
    exact rep_affine' hC _ _
  refine WP.seq (WP.mono (qMul_ok hc h3 hc.mulNf (gx := GX) (gy := GY) (by decide) (by decide) (by decide)
    (by decide) K₁.ws (lt_of_eq_of_lt K₁.fixed.ap (hmont _)) (lt_of_eq_of_lt K₁.fixed.b3p (hmont _))
    (by rw [h1 K₁.fixed]; exact hmont _) (by rw [hz K₁.fixed]; omega_arith)
    (lt_of_eq_of_lt K₁.fixed.gx (hmont _)) (lt_of_eq_of_lt K₁.fixed.gy (hmont _))
    (by rw [v₁ (by decide) (by decide), hM.rx]; omega_arith) (by rw [v₁ (by decide) (by decide), hM.ry]; exact hmont _)
    (by rw [v₁ (by decide) (by decide), hM.rz]; omega_arith) (k := sv c base s U)
    (step_rep' (L := ladderAt c GX GY) (s := s₁) hC hc.onG (ha K₁.fixed) (hb K₁.fixed) hG₁
      (fun h => ⟨by
        simp only [Impl.Ecdsa.PPC64LE.Cfg.qA0, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.2.1]; rfl, by
        show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem base (c.sl ONEP) c.n) = 1
        rw [K₁.fixed.onep]; exact toM_one (unitMod_pow_two hc.p_odd _)⟩))
    (by
      show Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ RX)) (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ RY))
        (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ RZ)) (mul (sv c base s U >>> (8 * c.C.len)) (G c.C))
      rw [v₁ (by decide) (by decide), v₁ (by decide) (by decide), v₁ (by decide) (by decide), hM.rx, hM.ry,
        hM.rz, toM_cmont hc, toM_zero, shiftRight_eq_zero hu, mul_zero_pt]
      exact rep_infinity' hC)
    (hO K₁.fixed hu) sk₁ b₁) fun s₂ ⟨k₂, U₂, L₂, R₂⟩ => ?_)
  obtain K₂ := K₁.step h7 k₂ (hU := U₂) (hW := hW) (hWs := hWs)
  -- `U = [u]G`, `R = O`.
  refine WP.seq (WP.mono (save_ok hc K₂.ws) fun s₃ ⟨k₃, U₃, ux₃, uy₃, uz₃, rx₃, ry₃, rz₃⟩ => ?_)
  obtain K₃ := K₂.step h7 (k₃.rk (rs' := [.r4, .r11])) (hU := U₃) (hW := fixedOk_slW (by decide))
    (hWs := slW_le h7 (by decide))
  obtain W₃ : ∀ {i}, i < 45 → i ∉ ptsW → sv c base s₃ i = sv c base s i := fun hi hl =>
    (sv_unch U₃ h7 hn hi (apart_slW (nmem_of hl (by decide)))).trans
      ((sv_unch U₂ h7 hn hi (apL hi (nmem_of hl (by decide)))).trans (v₁ hi (ne_of_nmem hl (by decide))))
  -- `v` to where the multiplication reads it.
  refine WP.seq (WP.mono (scalarAt_ok hc K₃.ws (i := V) (by decide) (by decide)) fun s₄ ⟨k₄, U₄, sk₄, b₄⟩ => ?_)
  obtain K₄ := K₃.step h7 (k₄.rk (rs' := bitsClob)) (hU := U₄) (hW := fixedOk_scW h7) (hWs := scW_le h7)
  obtain v₄ : ∀ {i}, i < 45 → i ≠ K → sv c base s₄ i = sv c base s₃ i := fun hi hK =>
    sv_unch U₄ h7 hn hi (apart_scW h7 hi hK)
  obtain e₃V : sv c base s₃ V = sv c base s V := W₃ (by decide) (by decide)
  -- `[v]Q`.
  obtain hv : sv c base s V < 2 ^ (8 * c.C.len) := Nat.lt_trans hM.v_lt hc.n_enc
  obtain tv₄ : ∀ {i}, i < 45 → i ∉ ptsW → tmv c.C c.n base s₄ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun hi hl => by
      show toM _ _ (sv c base s₄ _) = toM _ _ (sv c base s _)
      rw [v₄ hi (ne_of_nmem hl (by decide)), W₃ hi hl]
  obtain hQ₄ : Rep c.C (tmv c.C c.n base s₄ (c.sl PX)) (tmv c.C c.n base s₄ (c.sl PY))
      (tmv c.C c.n base s₄ (c.sl ONEP)) P := by
    rw [tv₄ (by decide) (by decide), tv₄ (by decide) (by decide), tv₄ (by decide) (by decide)]; exact hQ
  refine WP.seq (WP.mono (qMul_ok hc h3 hc.mulNf (gx := PX) (gy := PY) (by decide) (by decide) (by decide)
    (by decide) K₄.ws (lt_of_eq_of_lt K₄.fixed.ap (hmont _)) (lt_of_eq_of_lt K₄.fixed.b3p (hmont _))
    (by rw [h1 K₄.fixed]; exact hmont _) (by rw [hz K₄.fixed]; omega_arith)
    (by rw [v₄ (by decide) (by decide), W₃ (by decide) (by decide)]; exact hM.px_lt)
    (by rw [v₄ (by decide) (by decide), W₃ (by decide) (by decide)]; exact hM.py_lt)
    (by rw [v₄ (by decide) (by decide), rx₃]; omega_arith) (by rw [v₄ (by decide) (by decide), ry₃]; exact hmont _)
    (by rw [v₄ (by decide) (by decide), rz₃]; omega_arith) (k := sv c base s V)
    (step_rep' (L := ladderAt c PX PY) (s := s₄) hC hP (ha K₄.fixed) (hb K₄.fixed) hQ₄
      (fun h => ⟨by
        simp only [Impl.Ecdsa.PPC64LE.Cfg.qA0, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.2.1]; rfl, by
        show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₄.mem base (c.sl ONEP) c.n) = 1
        rw [K₄.fixed.onep]; exact toM_one (unitMod_pow_two hc.p_odd _)⟩))
    (by
      show Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₄ RX)) (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₄ RY))
        (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₄ RZ)) (mul (sv c base s V >>> (8 * c.C.len)) P)
      rw [v₄ (by decide) (by decide), v₄ (by decide) (by decide), v₄ (by decide) (by decide), rx₃, ry₃, rz₃,
        toM_cmont hc, toM_zero, shiftRight_eq_zero hv, mul_zero_pt]
      exact rep_infinity' hC)
    (hO K₄.fixed hv) (fun hs => by rw [sk₄ hs, e₃V]) (fun hN t ht => by rw [b₄ hN t ht, e₃V]))
    fun s₅ ⟨k₅, U₅, L₅, R₅⟩ => ?_)
  obtain K₅ := K₄.step h7 k₅ (hU := U₅) (hW := (fixedOk_ladWp h3 h7 PX PY).append (fixedOk_genX h7))
    (hWs := le_append (ladWp_le h3 h7 PX PY) (genX_le h7))
  obtain u₅ : ∀ {i}, i ∈ [UX, UY, UZ] → sv c base s₅ i = sv c base s₃ i := fun {i} hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
      exact (sv_unch U₅ h7 hn (by decide) (apL (by decide) (by decide))).trans (v₄ (by decide) (by decide))
  -- The sum.
  refine WP.mono (sum_ok hc K₅ (fun i hi => ?_)) fun s₆ ⟨K₆, U₆, _, _, rz₆, t₆⟩ => h s₆ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt K₅.fixed.ap (hmont _)
    · exact lt_of_eq_of_lt K₅.fixed.b3p (hmont _)
    · rw [u₅ (by decide), ux₃]; exact L₂ _ (List.mem_cons_self ..)
    · rw [u₅ (by decide), uy₃]; exact L₂ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · rw [u₅ (by decide), uz₃]
      exact L₂ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    · exact L₅ _ (List.mem_cons_self ..)
    · exact L₅ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact L₅ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  -- Facts kept from `s`.
  obtain W₆ : ∀ {i}, i < 45 → i ∉ ptsW → sv c base s₆ i = sv c base s i := fun hi hl =>
    (sv_unch U₆ h7 hn hi (apart_append (apart_slW (nmem_of hl (by decide))) (apart_own h7 hi))).trans
      ((sv_unch U₅ h7 hn hi (apL hi (nmem_of hl (by decide)))).trans
        ((v₄ hi (ne_of_nmem hl (by decide))).trans (W₃ hi hl)))
  obtain hFl := sl_le c h7 (i := FLAG) (by decide)
  obtain flagOk : ∀ {W : List (Nat × Nat)} {m m' : Mem}, Unch base W m m' →
      (∀ w ∈ W, c.sl FLAG + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG) →
      word m' base (c.sl FLAG) = word m base (c.sl FLAG) := fun U ap =>
    U.word (fun w hw => (ap w hw).imp (fun h => by omega_arith) id) (by omega_arith)
  obtain fl₆ : flagW c base s₆ = flagW c base s := by
    simp only [flagW]
    rw [flagOk U₆ (apart_append (apart_slW (by decide)) (apart_own h7 (by decide))),
      flagOk U₅ (apL (by decide) (by decide)), flagOk U₄ (apart_scW h7 (by decide) (by decide)),
      flagOk U₃ (apart_slW (by decide)), flagOk U₂ (apL (by decide) (by decide)),
      flagOk U₁ (apart_scW h7 (by decide) (by decide))]
  obtain rm₆ : sv c base s₆ RM' = sv c base s RM' := W₆ (by decide) (by decide)
  obtain tU : ∀ {i j}, i ∈ [UX, UY, UZ] → sv c base s₃ i = sv c base s₂ j →
      tmv c.C c.n base s₅ (c.sl i) = tmv c.C c.n base s₂ (c.sl j) := fun hi e => by
    show toM _ _ (sv c base s₅ _) = toM _ _ (sv c base s₂ _)
    rw [u₅ hi, e]
  refine ⟨K₆, fun t ht => ?_, by rw [fl₆]; exact hM.flag, by rw [rm₆]; exact hM.rm_lt, by rw [rm₆]; exact hM.rm,
    rz₆, Rep.add hC (hC.onCurve_mul hc.onG _) (hC.onCurve_mul hP _)
      (by rw [Nat.shiftRight_zero] at R₂; exact R₂) (by rw [Nat.shiftRight_zero] at R₅; exact R₅)
      (by refine Eq.symm ?_
          rw [t₆, ha K₅.fixed, hb K₅.fixed, tU (by decide) ux₃, tU (by decide) uy₃, tU (by decide) uz₃])⟩
  rw [tbl_unch U₆ h7 (j := 1) (by decide) ht (apart_append (tbl_apart_slW h7 (by decide) 1 t) (tbl_apart_own h7 1 t)),
    tbl_unch U₅ h7 (j := 1) (by decide) ht (tbL (by decide) ht),
    tbl_unch U₄ h7 (j := 1) (by decide) ht (tbl_apart_scW h7 (by decide) ht),
    tbl_unch U₃ h7 (j := 1) (by decide) ht (tbl_apart_slW h7 (by decide) 1 t),
    tbl_unch U₂ h7 (j := 1) (by decide) ht (tbL (by decide) ht),
    tbl_unch U₁ h7 (j := 1) (by decide) ht (tbl_apart_scW h7 (by decide) ht)]
  exact hM.t₁ t ht

/-! ## `[u]G + [v]Q` by one chain of doublings, for at most six words -/

open VG.Proof.Weierstrass.PPC64LE.Joint (JLay jointW roL wL tL dL)

/-- The joint multiplication's slots, for curves of three to six words. -/
theorem jointLay (hc : CfgOk c) (h3 : 3 ≤ c.n) (h6 : c.n ≤ 6) : JLay (Impl.Ecdsa.Verify.PPC64LE.Cfg.jointCfg c) where
  lad := ladPtLay hc h3 h6 (gx := GX) (gy := GY) (by decide) (by decide)
  low := by
    intro x hx
    simp only [roL, tL, dL, Impl.Ecdsa.Verify.PPC64LE.Cfg.jointCfg, Cfg.ladderCfg, Cfg.pt, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with ((h | h | h | h | h | h | h | h | h | h | h | h) | h | h | h) | h | h | h <;> subst h <;>
      exact ⟨sl_below_pt h3 h6 (by decide), sl_al c _⟩
  ro := by
    intro x hx y hy
    simp only [roL, wL, Impl.Ecdsa.Verify.PPC64LE.Cfg.jointCfg, Cfg.ladderCfg, Cfg.pt, List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact sl_apart c (by decide)
  tne := ⟨sl_apart c (by decide), sl_apart c (by decide), sl_apart c (by decide)⟩
  dne := ⟨sl_apart c (by decide), sl_apart c (by decide), sl_apart c (by decide)⟩
  td := by
    intro x hx y hy
    simp only [tL, dL, Impl.Ecdsa.Verify.PPC64LE.Cfg.jointCfg, Cfg.ladderCfg, Cfg.pt, List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> exact sl_apart c (by decide)
  gq := by
    refine ⟨⟨sl_apart c (by decide), sl_apart c (by decide), sl_apart c (by decide)⟩, ?_⟩
    intro x hx y hy
    simp only [Impl.Ecdsa.Verify.PPC64LE.Cfg.jointCfg, Cfg.ladderCfg, Cfg.pt, List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact sl_apart c (by decide)
  bitsV := by
    show 4096 ≤ bitsAt c.n 3 ∧ bitsAt c.n 3 + 8 * c.C.len ≤ 8192
    rw [bitsAt_eq]; have := hc.len_hi; have := hc.n10; omega_arith

theorem joint_eq (c : Cfg) : Impl.Ecdsa.Verify.PPC64LE.Cfg.joint c =
    .seq (bits (c.sl U) (bitsAt c.n 0) (8 * c.n)) (.seq (bits (c.sl V) (bitsAt c.n 3) (8 * c.n))
      ((Impl.Ecdsa.Verify.PPC64LE.Cfg.jointCfg c).joint c.SP)) := rfl

/-- The slots the joint multiplication writes. -/
abbrev jointIx : List Nat := [RX, RY, RZ, TX, TY, TZ, DX, DY, DZ, K, D, E]

theorem jointW_eq (c : Cfg) : jointW (Impl.Ecdsa.Verify.PPC64LE.Cfg.jointCfg c) =
    slW c [RX, RY, RZ, TX, TY, TZ, DX, DY, DZ] ++ [(Impl.Weierstrass.Point.oAt c.n, 4096 - Impl.Weierstrass.Point.oAt c.n)] ++
      slW c [K, D, E] := rfl

/-- A slot the joint multiplication does not write, apart from what it writes. -/
theorem apart_jointW (h3 : 3 ≤ c.n) (h6 : c.n ≤ 6) {i : Nat} (hi : i < 45) (hl : i ∉ jointIx) :
    ∀ w ∈ jointW (Impl.Ecdsa.Verify.PPC64LE.Cfg.jointCfg c), c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  rw [jointW_eq]
  refine apart_append (apart_append (apart_slW (nmem_of hl (by decide))) fun w hw => ?_)
    (apart_slW (nmem_of hl (by decide)))
  rw [List.mem_singleton.mp hw]
  exact Or.inl (sl_below_pt h3 h6 hi)

/-- The tables of bits are apart from what the joint multiplication writes. -/
theorem tbl_apart_jointW (h3 : 3 ≤ c.n) (h6 : c.n ≤ 6) (j t : Nat) :
    ∀ w ∈ jointW (Impl.Ecdsa.Verify.PPC64LE.Cfg.jointCfg c), bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  obtain hc7 : c.n < 10 := by omega_using [h6]
  rw [jointW_eq]
  refine apart_append (apart_append (tbl_apart_slW hc7 (by decide) j t) fun w hw => ?_)
    (tbl_apart_slW hc7 (by decide) j t)
  · rw [List.mem_singleton.mp hw]
    obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, -, -⟩ := VG.Proof.Weierstrass.PPC64LE.Point.lay_nums h3 h6
    rw [bitsAt_eq]
    exact Or.inr (by dsimp only; omega_arith)

theorem fixedOk_jointW (h3 : 3 ≤ c.n) (h6 : c.n ≤ 6) : FixedOk c (jointW (Impl.Ecdsa.Verify.PPC64LE.Cfg.jointCfg c)) := by
  rw [jointW_eq]
  refine ((fixedOk_slW (by decide)).append fun w hw => ?_).append (fixedOk_slW (by decide))
  rw [List.mem_singleton.mp hw]
  exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_pt h3 h6 (i := 12) (by decide)))

theorem jointW_le (h3 : 3 ≤ c.n) (h6 : c.n ≤ 6) : ∀ w ∈ jointW (Impl.Ecdsa.Verify.PPC64LE.Cfg.jointCfg c), w.1 + w.2 ≤ size := by
  rw [jointW_eq]
  refine le_append (le_append (slW_le (by omega_using [h6]) (by decide)) fun w hw => ?_) (slW_le (by omega_using [h6]) (by decide))
  rw [List.mem_singleton.mp hw]
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, -, -⟩ := VG.Proof.Weierstrass.PPC64LE.Point.lay_nums h3 h6
  show _ ≤ 8192
  dsimp only; omega_using [l1, l2, l4, l5, l6, l7, l8]

/-- `[u]G + [v]Q`, into `R`, by one chain of doublings: the tables of the
bits of `u` and `v`, then `Joint.joint_ok`. -/
theorem jointPts_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) (h6 : c.n ≤ 6) (hC : Law c.C) {s₀ : State} {base : Addr}
    {s : State} (hM : Mid c s₀ base s) {P : Point c.C} (hP : onCurve c.C P = true)
    (hQ : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY)) (tmv c.C c.n base s (c.sl ONEP)) P)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', Pts c s₀ base (sv c base s U) (sv c base s V) P s' → WP isa rest s' Q) :
    WP isa (.seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.joint c) rest) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hM.ws.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  obtain hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  have hlen := hc.len_hi
  rw [joint_eq]
  refine WP.seq ?_
  -- The bits of `u`, then of `v`.
  refine WP.seq (WP.mono (tbl_bits_ok hc hM.ws (i := U) (j := 0) (by decide) (by decide))
    fun s₁ ⟨b₁, k₁, O₁⟩ => ?_)
  obtain K₁ := hM.toKeep.step h7 (k₁.rk (rs' := bitsClob)) (hU := O₁.unch) (hW := fixedOk_tbl h7 0)
    (hWs := fun w hw => by rw [List.mem_singleton.mp hw]; exact bitsAt_le c h7 (by decide))
  obtain hb3 : bitsAt c.n 3 + 64 * c.n ≤ size := by rw [bitsAt_eq]; show _ ≤ 8192; omega_arith
  obtain hsV := sl_le c h7 (i := V) (by decide)
  refine WP.seq (WP.mono (bits_ok K₁.ws.ws K₁.ws.at3 (size := size) (src := c.sl V) (dst := bitsAt c.n 3) h0
    (by show _ ≤ 8192; omega_using [hsV]) hb3 (Or.inl (sl_below_bits c h7 (by decide) 3 0))) fun s₂ ⟨b₂, k₂, O₂⟩ => ?_)
  obtain K₂ := K₁.step h7 (k₂.rk (rs' := bitsClob)) (hU := O₂.unch) (hW := fixedOk_tbl h7 3)
    (hWs := fun w hw => by rw [List.mem_singleton.mp hw]; exact hb3)
  obtain v₁ : ∀ {i}, i < 45 → sv c base s₁ i = sv c base s i := fun hi => sv_unch O₁.unch h7 hn hi (apart_tbl h7 hi 0)
  obtain v₂ : ∀ {i}, i < 45 → sv c base s₂ i = sv c base s i := fun hi =>
    (sv_unch O₂.unch h7 hn hi (apart_tbl h7 hi 3)).trans (v₁ hi)
  have F := K₂.fixed
  obtain one : wordsVal s₂.mem base (c.sl ONEP) c.n = c.mont 1 := by
    rw [F.onep, Cfg.mont, Cfg.R, Nat.one_mul]
  obtain tone : toM c.C.p (2 ^ (64 * c.n)) (c.mont 1) = 1 := by
    rw [Cfg.mont, Cfg.R, Nat.one_mul]; exact toM_one hpR
  -- `[u]G + [v]P`.
  refine WP.mono (Joint.joint_ok (J := Impl.Ecdsa.Verify.PPC64LE.Cfg.jointCfg c) (G := G c.C) (Q := P) (u := sv c base s U)
    (v := sv c base s V) (S := c.SP) hc.fpk hc.fpm (modP hc) hc.p_odd hC hc.onG hP (jointLay hc h3 h6) K₂.ws
    (fun x hx => ?_) ⟨?_, ?_⟩ ?_ ?_ ?_ (fun i hi => ?_) (fun i hi => ?_) (Nat.lt_trans hM.u_lt hc.n_enc)
    (Nat.lt_trans hM.v_lt hc.n_enc) ⟨hmont 1, tone⟩) fun s₃ ⟨k₃, U₃, l₃, r₃⟩ => h s₃ ?_
  · simp only [Impl.Ecdsa.Verify.PPC64LE.Cfg.jointCfg, Cfg.ladderCfg, Cfg.pt, Cfg.rcbSlots, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F.ap (hmont _)
    · exact lt_of_eq_of_lt F.b3p (hmont _)
    · exact lt_of_eq_of_lt F.gx (hmont _)
    · exact lt_of_eq_of_lt F.gy (hmont _)
    · exact lt_of_eq_of_lt one (hmont _)
    · exact lt_of_eq_of_lt (v₂ (by decide)) hM.px_lt
    · exact lt_of_eq_of_lt (v₂ (by decide)) hM.py_lt
    · exact lt_of_eq_of_lt one (hmont _)
    · exact lt_of_eq_of_lt F.zero (by omega_arith)
    · exact lt_of_eq_of_lt one (hmont _)
    · exact lt_of_eq_of_lt F.zero (by omega_arith)
  · show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₂.mem base (c.sl AP) c.n) = _; rw [F.ap]; exact toM_cmont hc _
  · show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₂.mem base (c.sl B3P) c.n) = _; rw [F.b3p]; exact toM_cmont hc _
  · show Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₂.mem base (c.sl GX) c.n)) (toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₂.mem base (c.sl GY) c.n))
      (toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₂.mem base (c.sl ONEP) c.n)) (G c.C)
    rw [F.gx, F.gy, one, toM_cmont hc, toM_cmont hc, tone]
    exact rep_affine' hC _ _
  · show Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ PX)) (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ PY))
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ ONEP)) P
    rw [v₂ (by decide), v₂ (by decide), v₂ (by decide)]
    exact hQ
  · show Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₂.mem base (c.sl ZERO) c.n)) (toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₂.mem base (c.sl ONEP) c.n))
      (toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₂.mem base (c.sl ZERO) c.n)) _
    rw [F.zero, one, tone, toM_zero]
    exact rep_infinity' hC
  · have hi' : i < 64 * c.n := by
      have : i < 8 * c.C.len := hi
      omega_arith
    show s₂.mem (off base (bitsAt c.n 0 + i)) = _
    rw [tbl_unch O₂.unch h7 (j := 0) (by decide) hi' (tbl_apart_tbl (by decide) hi')]
    exact b₁ i hi'
  · have hi' : i < 64 * c.n := by
      have : i < 8 * c.C.len := hi
      omega_arith
    show s₂.mem (off base (bitsAt c.n 3 + i)) = _
    rw [b₂ i hi']
    exact congrArg (fun x => if Nat.testBit x i = true then (1 : BitVec 8) else 0) (v₁ (by decide))
  -- What `Pts` needs.
  obtain K₃ := K₂.step h7 k₃ (hU := U₃) (hW := fixedOk_jointW h3 h6) (hWs := jointW_le h3 h6)
  obtain W₃ : ∀ {i}, i < 45 → i ∉ jointIx → sv c base s₃ i = sv c base s i := fun hi hl =>
    (sv_unch U₃ h7 hn hi (apart_jointW h3 h6 hi hl)).trans (v₂ hi)
  obtain hFl := sl_le c h7 (i := FLAG) (by decide)
  obtain flagOk : ∀ {W : List (Nat × Nat)} {m m' : Mem}, Unch base W m m' →
      (∀ w ∈ W, c.sl FLAG + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG) →
      word m' base (c.sl FLAG) = word m base (c.sl FLAG) := fun U ap =>
    U.word (fun w hw => (ap w hw).imp (fun h => by omega_arith) id) (by omega_arith)
  obtain fl₃ : flagW c base s₃ = flagW c base s := by
    simp only [flagW]
    rw [flagOk U₃ (apart_jointW h3 h6 (by decide) (by decide)), flagOk O₂.unch (apart_tbl h7 (by decide) 3),
      flagOk O₁.unch (apart_tbl h7 (by decide) 0)]
  obtain rm₃ : sv c base s₃ RM' = sv c base s RM' := W₃ (by decide) (by decide)
  refine ⟨K₃, fun t ht => ?_, by rw [fl₃]; exact hM.flag, by rw [rm₃]; exact hM.rm_lt, by rw [rm₃]; exact hM.rm,
    l₃ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))), r₃⟩
  rw [tbl_unch U₃ h7 (j := 1) (by decide) ht (tbl_apart_jointW h3 h6 1 t),
    tbl_unch O₂.unch h7 (j := 1) (by decide) ht (tbl_apart_tbl (by decide) ht),
    tbl_unch O₁.unch h7 (j := 1) (by decide) ht (tbl_apart_tbl (by decide) ht)]
  exact hM.t₁ t ht

/-- `[u]G + [v]Q`, into `R`: by one chain of doublings for at most six
words, else by the two ladders and the sum. -/
theorem points_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) (hC : Law c.C) {s₀ : State} {base : Addr}
    {s : State} (hM : Mid c s₀ base s) {P : Point c.C} (hP : onCurve c.C P = true)
    (hQ : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY)) (tmv c.C c.n base s (c.sl ONEP)) P)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', Pts c s₀ base (sv c base s U) (sv c base s V) P s' → WP isa rest s' Q) :
    WP isa (.seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.points c) rest) s Q := by
  unfold Impl.Ecdsa.Verify.PPC64LE.Cfg.points
  by_cases h6 : c.n ≤ 6
  · simp only [h6, ↓reduceIte]; exact jointPts_ok hc h3 h6 hC hM hP hQ h
  · simp only [h6, ↓reduceIte]; exact ladders_ok hc h3 hC hM hP hQ h

end VG.Proof.Ecdsa.Verify.PPC64LE

end

end

/-! ### `Ecdsa.Verify.PPC64LE.Final`, which only this module used -/

section

/-!
# ECDSA verification on PPC64LE: `x` and the result

As on 32-bit ARM (`Proof/Ecdsa/Verify/Arm/Final.lean`). `vtail_ok`: from
what `points_ok` leaves, the signature's power gives `Z^(p-2)`, and `final`
computes `x = X Z^(p-2)` out of Montgomery's form, `x R mod n` and
`x R - r R mod n`, ands the masks of `Z ≠ 0` and of that difference being
zero (`x ≡ r` modulo `n`) into the flag, returns its low bit and restores
`lr`, `r14` and `r31` (`vfinish_ok`). It writes only the working space.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Proof.Ecdh.PPC64LE VG.Spec.Weierstrass
open VG.Proof.Weierstrass.PPC64LE.Point (tmv)
open VG.Impl.Ecdsa.Verify.PPC64LE (RM' XN W)

variable {c : Cfg}

theorem vfinish_eq (c : Cfg) : Impl.Ecdsa.Verify.PPC64LE.Cfg.finish c =
    .load .d .r10 wb (c.sl FLAG) :: .li .r4 1 :: .logic .and .r4 .r10 .r4 :: (Cfg.restore ++ [mov .r3 .r4]) := rfl

/-- The return value, and `lr`, `r14` and `r31` from the working space. -/
theorem vfinish_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base) (b : Bool)
    (hf : flagW c base s = mask64 (b = true)) :
    WP isa (.block (Impl.Ecdsa.Verify.PPC64LE.Cfg.finish c)) s fun s' =>
      s'.gpr .r3 = (if b then 1 else 0) ∧
      s'.lr = word s.mem base Cfg.lrAt ∧ s'.gpr .r14 = word s.mem base 0 ∧ s'.gpr .r31 = word s.mem base 8 ∧
      Rk [.r0, .r3, .r4, .r10, .r14, .r31] s s' ∧ s'.mem = s.mem := by
  have h7 := hc.n10
  have hsz : size = 8192 := rfl
  obtain hF := sl_le c h7 (i := FLAG) (by decide)
  have hs := hw.ws
  have h3 := hw.at3
  rw [vfinish_eq]
  refine wp_step (ld0_ok hs h3 (by decide) (sl_al c FLAG) (by omega_arith)) ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_logic ?_
  obtain hs₁ := hs.write .r10 (word s.mem base (c.sl FLAG))
  obtain h3₁ := h3.write (d := .r10) (word s.mem base (c.sl FLAG))
  refine restore_ok ((hs₁.write _ _).write _ _) ((h3₁.write _).write _) (by omega_arith) fun t Kt mt lrt r14t r31t => ?_
  refine wp_step exec_mov (WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩)
  · simp only [write_gpr, ite_true]
    rw [Kt.gpr _ (by decide)]
    simp only [write_gpr, ite_true, reduceCtorEq, ite_false]
    rw [show word s.mem base (c.sl FLAG) = mask64 (b = true) from hf]
    exact mask_bit b
  · simp only [write_lr]; rw [lrt]; rfl
  · simp only [write_gpr, reduceCtorEq, ite_false]; rw [r14t]; rfl
  · simp only [write_gpr, reduceCtorEq, ite_false]; rw [r31t]; rfl
  · exact ((((Kp.write s (d := .r10) _ (rs := [.r0, .r3, .r4, .r10, .r14, .r31]) (by decide)).trans
      (Kp.write _ (d := .r4) (BitVec.ofNat 64 1) (by decide))).trans
      (Kp.write _ (d := .r4) _ (by decide))).rk.trans (Kt.mono (by decide))).trans
      (Kp.write t (d := .r3) _ (rs := [.r0, .r3, .r4, .r10, .r14, .r31]) (by decide)).rk
  · simp only [write_mem]; rw [mt]; rfl

theorem final_eq (c : Cfg) : Impl.Ecdsa.Verify.PPC64LE.Cfg.final c =
    .seq (mulCall c.SP (c.sl XM) (c.sl RX) (c.sl ACC))
    (.seq (mulCall c.SP (c.sl X) (c.sl XM) (c.sl ONE))
    (.seq (mulCall c.SN (c.sl XN) (c.sl X) (c.sl R2N))
    (.seq (subCall c.SN (c.sl W) (c.sl XN) (c.sl RM'))
      (.block (c.checkNonzero (c.sl RZ) ++ (Impl.Ecdh.PPC64LE.Cfg.checkZero c (c.sl W) ++
        Impl.Ecdsa.Verify.PPC64LE.Cfg.finish c)))))) := by
  simp only [Impl.Ecdsa.Verify.PPC64LE.Cfg.final, progs, List.append_assoc]

/-- `Z^(p-2)`, `x`, the last checks and the result. -/
theorem vtail_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {u v : Nat} {P : Point c.C} {s : State}
    (hP : Pts c s₀ base u v P s) :
    WP isa (.seq c.invP (Impl.Ecdsa.Verify.PPC64LE.Cfg.final c)) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧ s'.lr = s₀.lr ∧
      Unch base [(0, size)] s₀.mem s'.mem ∧ ∃ xo, xo < c.C.p ∧
        Fin.ofNat c.C.p xo = tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) ∧
        s'.gpr .r3 = if (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
          (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
          Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀) then 1 else 0 := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hP.ws.nowrap
  have hsz : size = 8192 := rfl
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  obtain hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hn3 := hc.n_ge
  obtain hfl : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  -- `Z^(p-2)`.
  refine WP.seq (WP.mono (chainPow_ok (P := c.chainP) (S := c.SP) (e := c.C.p - 2) hc.fpk hc.fpm (modP hc)
    (chainLayP hc) hpR hP.ws hP.rz_lt hc.chainP) fun s₁ ⟨k₁, U₁, lt₁, v₁⟩ => ?_)
  rw [chainWP_eq] at U₁
  obtain K₁ : Keep c s₀ base s₁ := hP.toKeep.step h7 k₁ (hU := U₁) (hW := fixedOk_chainW h7) (hWs := chainW_le h7)
  obtain e₁ : ∀ {i}, i < 45 → i ≠ ACC → (i < DX ∨ T2 < i) → sv c base s₁ i = sv c base s i := fun hi hr ht =>
    sv_unch U₁ h7 hn hi (apart_chainW h7 hi hr ht)
  obtain fl₁ : flagW c base s₁ = flagW c base s := by
    obtain apF : ∀ w ∈ [(c.sl ACC, 8 * c.n), (c.sl DX, 9 * (8 * c.n)), (own c.n, 64 * c.n)],
        c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := fun w hw => by
      have := sl_le c h7 (i := FLAG) (by decide)
      rcases apart_chainW h7 (i := FLAG) (by decide) (by decide) (by decide) w hw with h | h
      · exact Or.inl (by omega_arith)
      · exact Or.inr h
    rw [flagW, U₁.word apF (by omega_arith), ← flagW]
  rw [final_eq]
  -- `XM = X · ACC`.
  refine WP.seq (WP.mono (slMul_ok hc.fp hc.fpk hc.fpm h7 K₁.ws (o := XM) (a := RX) (b := ACC) (by decide)
    (by decide) (by decide) lt₁) fun s₂ ⟨k₂, U₂, _, e₂⟩ => ?_)
  obtain ⟨K₂, f₂, -, v₂⟩ := K₁.call h0 h7 (o := XM) (by decide) (by decide) (by decide) k₂ U₂
  -- `X = XM · 1`.
  obtain one₂ : sv c base s₂ ONE = 1 := (v₂ (by decide) (by decide)).trans K₁.fixed.one
  refine WP.seq (WP.mono (slMul_ok hc.fp hc.fpk hc.fpm h7 K₂.ws (o := X) (a := XM) (b := ONE) (by decide)
    (by decide) (by decide) (by rw [one₂]; omega_arith)) fun s₃ ⟨k₃, U₃, lt₃, e₃⟩ => ?_)
  obtain ⟨K₃, f₃, -, v₃⟩ := K₂.call h0 h7 (o := X) (by decide) (by decide) (by decide) k₃ U₃
  obtain x₃ : Fin.ofNat c.C.p (sv c base s₃ X) =
      tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) := by
    have acc₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ ACC) = tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) := v₁
    rw [toM_one_mul hpR (by rw [e₃, one₂]), toM_mul hpR e₂, acc₁]
    show toM _ _ (sv c base s₁ RX) * _ = toM _ _ (sv c base s RX) * _
    rw [e₁ (by decide) (by decide) (by decide)]
  -- `XN = x R mod n`, `W = XN - r R mod n`.
  have r2₃ : sv c base s₃ R2N = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n := K₃.fixed.r2n
  refine WP.seq (WP.mono (slMul_ok hc.fn hc.fnk hc.fnm h7 K₃.ws (o := XN) (a := X) (b := R2N) (by decide)
    (by decide) (by decide) (by rw [r2₃]; exact Nat.mod_lt _ (by omega_arith))) fun s₄ ⟨k₄, U₄, lt₄, e₄⟩ => ?_)
  obtain ⟨K₄, f₄, -, v₄⟩ := K₃.call h0 h7 (o := XN) (by decide) (by decide) (by decide) k₄ U₄
  obtain rm₄ : sv c base s₄ RM' = sv c base s RM' := by
    rw [v₄ (by decide) (by decide), v₃ (by decide) (by decide), v₂ (by decide) (by decide),
      e₁ (by decide) (by decide) (by decide)]
  refine WP.seq (WP.mono (slSub_ok hc.fn hc.fnk hc.fnm h7 K₄.ws (o := W) (a := XN) (b := RM') (by decide)
    (by decide) (by decide) lt₄ (by rw [rm₄]; exact hP.rm_lt)) fun s₅ ⟨k₅, U₅, e₅⟩ => ?_)
  obtain ⟨K₅, f₅, -, v₅⟩ := K₄.call h0 h7 (o := W) (by decide) (by decide) (by decide) k₅ U₅
  obtain w₅ : sv c base s₅ W = 0 ↔ Fin.ofNat c.C.n (sv c base s₃ X) = Fin.ofNat c.C.n (sigR c s₀) := by
    obtain hlt : sv c base s₅ W < c.C.n := by rw [e₅]; exact Nat.mod_lt _ (by omega_arith)
    rw [← toM_eq_zero_iff hnR hlt, e₅, toM_sub (by rw [rm₄]; have := hP.rm_lt; omega_arith), rm₄, hP.rm,
      toM_r2 hnR (by rw [e₄, r2₃])]
    constructor <;> intro h <;> grind
  -- The checks and the result.
  rw [WP.block_append_iff]
  refine WP.mono (checkNonzero_ok c K₅.ws.ws K₅.ws.at3 (sl_al c RZ) h0
    (by have := sl_le c h7 (i := RZ) (by decide); omega_arith) hfl) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_
  obtain K₆ := K₅.step h7 (k₆.rk (rs' := [.r4, .r5])) (hU := O₆.unch) (hW := fixedOk_flag) (hWs := by
    intro w hw; rw [List.mem_singleton.mp hw]; exact hfl)
  rw [WP.block_append_iff]
  refine WP.mono (checkZero_ok c K₆.ws.ws K₆.ws.at3 (sl_al c W) h0
    (by have := sl_le c h7 (i := W) (by decide); omega_arith) hfl) fun s₇ ⟨f₇, k₇, O₇⟩ => ?_
  obtain K₇ := K₆.step h7 (k₇.rk (rs' := [.r4, .r5])) (hU := O₇.unch) (hW := fixedOk_flag) (hWs := by
    intro w hw; rw [List.mem_singleton.mp hw]; exact hfl)
  obtain z₅ : wordsVal s₅.mem base (c.sl RZ) c.n = sv c base s RZ := by
    show sv c base s₅ RZ = _
    rw [v₅ (by decide) (by decide), v₄ (by decide) (by decide), v₃ (by decide) (by decide),
      v₂ (by decide) (by decide), e₁ (by decide) (by decide) (by decide)]
  obtain hW₆ : wordsVal s₆.mem base (c.sl W) c.n = sv c base s₅ W :=
    sv_unch O₆.unch h7 hn (i := W) (by decide) (apart_flag h0 (by decide))
  obtain hflag : flagW c base s₇ = mask64 (decide ((KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
      (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
      Fin.ofNat c.C.n (sv c base s₃ X) = Fin.ofNat c.C.n (sigR c s₀)) = true) := by
    rw [f₇, f₆, hW₆, f₅, f₄, f₃, f₂, fl₁, hP.flag, z₅, mask64_and, mask64_and]
    simp only [w₅, decide_eq_true_eq, and_assoc]
  refine WP.mono (vfinish_ok hc K₇.ws _ hflag) fun s' ⟨ret, lr, r14, r31, rk, hm⟩ =>
    ⟨?_, by rw [rk.sp, K₇.rk.sp], by rw [lr, K₇.fixed.savedLr], by rw [hm]; exact K₇.whole, _, lt₃, x₃, ?_⟩
  · intro r hr
    obtain hcases : ∀ r ∈ preserved, r = .r14 ∨ r = .r31 ∨
        (r ∉ [Reg.r0, .r3, .r4, .r10, .r14, .r31] ∧ r ∉ work) := by decide
    rcases hcases r hr with rfl | rfl | ⟨h₁, h₂⟩
    · rw [r14]; exact K₇.fixed.saved (.r14, 0) (by decide)
    · rw [r31]; exact K₇.fixed.saved (.r31, 8) (by decide)
    · rw [rk.gpr r h₁, K₇.rk.gpr r h₂]
  · rw [ret]
    simp only [decide_eq_true_eq]

end VG.Proof.Ecdsa.Verify.PPC64LE

end

end


/-!
# ECDSA verification on PPC64LE: the whole function

As on 32-bit ARM (`Proof/Ecdsa/Verify/Arm/Main.lean`). `verify_ok`:
`Cfg.verify` returns 1 exactly if the specification's verification of the
signature holds, for any curve the proof of the code supports (`CfgOk`)
whose group law the proofs support (`Law`), restores the callee-saved
registers and `lr`, keeps `sp` and writes only the working space.
`front_ok`, `mid_ok`, `points_ok` and `vtail_ok` compute what
`Proof.Ecdsa.verify_eq` connects to the specification.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Proof.Ecdh.PPC64LE VG.Spec.Weierstrass
open VG.Proof.Weierstrass.PPC64LE.Point (tmv)
open VG.Impl.Ecdh.PPC64LE (PX PY)
open VG.Impl.Ecdsa.Verify.PPC64LE (U V)

variable {c : Cfg}

/-- The result the contract asks for: 1 exactly if the specification's
verification holds. -/
def VPost (c : Cfg) (s₀ s' : State) : Prop :=
  s'.gpr .r3 =
    if Spec.Ecdsa.verify c.C (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r3) (1 + 2 * c.C.len))
      (Spec.Ecdsa.hashToInt c.C (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r4) c.C.len))
      (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5) (2 * c.C.len)) then 1 else 0

/-- What the function keeps: the callee-saved registers, `sp` and `lr`, and
memory but the working space. -/
structure VKeep (s₀ s' : State) : Prop where
  saved : ∀ r ∈ preserved, s'.gpr r = s₀.gpr r
  sp : s'.sp = s₀.sp
  lr : s'.lr = s₀.lr
  frame : Unch (s₀.gpr .r6) [(0, size)] s₀.mem s'.mem

theorem verifyWith_eq (c : Cfg) (pts : Prog isa) : Impl.Ecdsa.Verify.PPC64LE.Cfg.verifyWith c pts =
    .seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.prefix' c) (.seq (.block (Impl.Ecdsa.Verify.PPC64LE.Cfg.loadS c))
      (.seq (.block (Impl.Ecdh.PPC64LE.Cfg.peerAt c .r14)) (.seq (Impl.Ecdh.PPC64LE.Cfg.validate c)
      (.seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.scalars c) (.seq c.invN
      (.seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.uv c) (.seq pts
      (.seq c.invP (Impl.Ecdsa.Verify.PPC64LE.Cfg.final c))))))))) := rfl

/-- What a computation of `[u]G + [v]Q` into `R` does, as `points_ok` states
it: from the stages before (`Mid`, naming the statics `s₀` names), with the
key's point `P` at `PX`, `PY`, `ONEP`, it leaves `Pts`. -/
def PtsOk (c : Cfg) (s₀ : State) (pts : Prog isa) : Prop :=
  ∀ {s : State}, Mid c s₀ (s₀.gpr .r6) s → s.syms = s₀.syms → ∀ {P : Point c.C}, onCurve c.C P = true →
    Rep c.C (tmv c.C c.n (s₀.gpr .r6) s (c.sl PX)) (tmv c.C c.n (s₀.gpr .r6) s (c.sl PY))
      (tmv c.C c.n (s₀.gpr .r6) s (c.sl ONEP)) P →
    ∀ {rest : Prog isa} {Q : State → Prop},
      (∀ s', Pts c s₀ (s₀.gpr .r6) (sv c (s₀.gpr .r6) s U) (sv c (s₀.gpr .r6) s V) P s' → WP isa rest s' Q) →
      WP isa (.seq pts rest) s Q

/-- `Cfg.verifyWith c pts` returns whether the specification's verification
holds, and restores the callee-saved registers, for `pts` computing
`[u]G + [v]Q` as `PtsOk` states. -/
theorem verifyWith_ok (hc : CfgOk c) (hC : Law c.C) {s₀ : State}
    {extra : List Region} (hp : VPre c s₀ extra) {pts : Prog isa} (hpts : PtsOk c s₀ pts) :
    WP isa (Impl.Ecdsa.Verify.PPC64LE.Cfg.verifyWith c pts) s₀ fun s' => VKeep s₀ s' ∧ VPost c s₀ s' := by
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  obtain setupRun := front_ok hc hp (rest := .seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.scalars c)
    (.seq c.invN (.seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.uv c) (.block []))))
    (Q := fun s => Mid c s₀ (s₀.gpr .r6) s) (fun _ F => mid_ok hc F fun _ M => WP.block_nil M)
  obtain finish : ∀ s₂, Mid c s₀ (s₀.gpr .r6) s₂ → s₂.syms = s₀.syms →
      WP isa (.seq pts (.seq c.invP (Impl.Ecdsa.Verify.PPC64LE.Cfg.final c))) s₂
        (fun t => VKeep s₀ t ∧ VPost c s₀ t) := by
    intro s₂ hM syms₂
    -- The point the second ladder multiplies.
    let P := peerPt c (s₀.mem (s₀.gpr .r3) = 4) (keyX c s₀) (keyY c s₀)
    obtain hPc : onCurve c.C P = true := peerPt_onCurve hc _ _ _
    obtain h1 : tmv c.C c.n (s₀.gpr .r6) s₂ (c.sl ONEP) = 1 := by
      show toM _ _ (wordsVal s₂.mem _ (c.sl ONEP) c.n) = _
      rw [hM.fixed.onep]; exact toM_one hpR
    obtain hQ : Rep c.C (tmv c.C c.n (s₀.gpr .r6) s₂ (c.sl PX)) (tmv c.C c.n (s₀.gpr .r6) s₂ (c.sl PY))
        (tmv c.C c.n (s₀.gpr .r6) s₂ (c.sl ONEP)) P := by
      rw [h1]
      exact peerPt_rep hC _ _ _ hM.px hM.py
    refine hpts hM syms₂ hPc hQ fun s₃ hP => ?_
    refine WP.mono (vtail_ok hc hP) fun s' ⟨saved, sp, lr, frame, xo, hxo, hx, ret⟩ =>
      ⟨⟨saved, sp, lr, frame⟩, ?_⟩
    have hR := hP.pt
    -- The arguments as the specification reads them.
    obtain hlen : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r3) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
      rw [length_bytesAt]; omega_using []
    obtain hb0 : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r3) (1 + 2 * c.C.len)).head? = some (s₀.mem (s₀.gpr .r3)) := by
      rw [peer_bytes]; rfl
    obtain hxv : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r3) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
        keyX c s₀ := by
      rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
    obtain hyv : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r3) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
        keyY c s₀ := by
      rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
    obtain hP' : ∀ h : Ecdh.Valid c.C (s₀.mem (s₀.gpr .r3)) (keyX c s₀) (keyY c s₀),
        P = .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
      show peerPt c _ _ _ = _
      unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
    obtain h16 : 2 * c.C.len = c.C.len + c.C.len := by omega_using []
    obtain hr : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5) (2 * c.C.len)).take c.C.len) = sigR c s₀ := by
      rw [h16, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]
    obtain hs : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5) (2 * c.C.len)).drop c.C.len) = sigS c s₀ := by
      rw [h16, bytesAt_add, List.drop_left' (length_bytesAt _ _ _)]
    obtain hspec := Proof.Ecdsa.verify_eq hC hlen hb0 hxv hyv hP' hr hs hM.u_lt hM.v_lt hM.u hM.v hR hxo hx
    -- The conditions.
    obtain hz := not_congr (toM_eq_zero_iff hpR hP.rz_lt)
    obtain hiff : (Ecdh.Valid c.C (s₀.mem (s₀.gpr .r3)) (keyX c s₀) (keyY c s₀) ∧
        (1 ≤ sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (1 ≤ sigS c s₀ ∧ sigS c s₀ < c.C.n) ∧
        tmv c.C c.n (s₀.gpr .r6) s₃ (c.sl RZ) ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) ↔
        ((KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
          sv c (s₀.gpr .r6) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) := by
      constructor
      · rintro ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hZ, he⟩
        exact ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hz.mp hZ, he⟩
      · rintro ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hZ, he⟩
        exact ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hz.mpr hZ, he⟩
    unfold VPost
    rw [hashToInt_eq c, hspec, ret]
    by_cases h : (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
        sv c (s₀.gpr .r6) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)
    · rw [ite_eq_left (decide_eq_true (hiff.mpr h)), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (hiff.mp (of_decide_eq_true h'))), ite_eq_right h]
  obtain run := VG.PPC64LE.WP.mono_syms setupRun finish
  simpa only [Impl.Ecdsa.Verify.PPC64LE.Cfg.verifyWith, Impl.Ecdsa.Verify.PPC64LE.Cfg.backWith,
    WP.seq_iff (M := isa), WP.block_nil_iff (M := isa)] using run

/-- `vg_ecdsa_<curve>_verify` returns whether the specification's
verification holds, and restores the callee-saved registers. -/
theorem verify_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) (hC : Law c.C) {s₀ : State}
    {extra : List Region} (hp : VPre c s₀ extra) :
    WP isa (Impl.Ecdsa.Verify.PPC64LE.Cfg.verify c) s₀ fun s' => VKeep s₀ s' ∧ VPost c s₀ s' :=
  verifyWith_ok hc hC hp fun hM _ _ hP hQ _ _ h => points_ok hc h3 hC hM hP hQ h

end VG.Proof.Ecdsa.Verify.PPC64LE
