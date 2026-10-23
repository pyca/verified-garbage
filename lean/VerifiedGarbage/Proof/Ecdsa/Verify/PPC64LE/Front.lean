module

public import VerifiedGarbage.Proof.Ecdh.PPC64LE.Validate
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
public import VerifiedGarbage.Impl.Ecdsa.Verify.PPC64LE
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Peer
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Finish
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

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
    Offset.contains_base _ (by omega) (by have := hp.sig_fit; omega)⟩
  d_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.dg_fit; omega)
  e_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.dg_fit; omega)
  k_sc := hp.sig_sc.sub_left (Region.sub_prefix (by omega))
  d_sc := hp.dg_sc
  e_sc := hp.dg_sc
  k_fit := show (s.gpr .r5).toNat + c.C.len ≤ 2 ^ 64 by have := hp.sig_fit; omega
  d_fit := hp.dg_fit
  e_fit := hp.dg_fit

theorem slW_le (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i < 45) : ∀ w ∈ slW c l, w.1 + w.2 ≤ size := by
  intro w hw
  have hsz : size = 8192 := rfl
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  have := sl_le c h7 (hl i hi); dsimp only; omega

theorem flag_le (h7 : c.n < 10) : ∀ w ∈ [(c.sl FLAG, 8)], w.1 + w.2 ≤ size := fun w hw => by
  have hsz : size = 8192 := rfl
  rw [List.mem_singleton.mp hw]; have := sl_le c h7 (i := FLAG) (by decide); dsimp only; omega

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
  have kw : Kp [.r12] s₁ (s₁.write .r12 (s₁.gpr .r5)) := Kp.write _ _ (by decide)
  have S₁' : St₀ c Args.verify s₀ (s₀.gpr .r6) (BitVec.allOnes 64) (s₁.write .r12 (s₁.gpr .r5)) :=
    ⟨S₁.toKeep.step h7 (kw.rk (rs' := [.r12])) (W := []) (hU := Unch.refl _ _ _)
      (hW := fun _ h => absurd h List.not_mem_nil) (hWs := fun _ h => absurd h List.not_mem_nil),
      S₁.k, S₁.d, S₁.e, S₁.rx, S₁.ry, S₁.rz, S₁.expp, S₁.expn, S₁.flag⟩
  have r12₁ : (s₁.write .r12 (s₁.gpr .r5)).gpr .r12 = s₀.gpr .r5 := by
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
  have hPT := sl_le c h7 (i := PT) (by decide)
  refine WP.seq (WP.mono (prefix_ok hc hp) fun s₂ ⟨S₂, r12₂⟩ => ?_)
  generalize hb : s₀.gpr .r6 = base at S₂ h
  have hn := S₂.ws.nowrap
  have hsg : Region.Disjoint ⟨s₀.gpr .r5, 2 * c.C.len⟩ ⟨base, size⟩ := hb ▸ hp.sig_sc
  have hpk : Region.Disjoint ⟨s₀.gpr .r3, 1 + 2 * c.C.len⟩ ⟨base, size⟩ := hb ▸ hp.pk_sc
  have hrw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [S₂.rk.rd, S₂.rk.wr]
  have W₂ : Outside base 0 size s₀.mem s₂.mem :=
    S₂.whole.outside fun w hw => by rw [List.mem_singleton.mp hw]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  rw [loadS_eq]
  refine WP.seq (wp_step (exec_addi (by decide) (show c.C.len < 2 ^ 15 by omega)) ?_)
  have kw₂ : Kp [.r6] s₂ (s₂.write .r6 (s₂.gpr .r12 + BitVec.ofNat 64 c.C.len)) := Kp.write _ _ (by decide)
  have hfitS : (s₀.gpr .r5 + BitVec.ofNat 64 c.C.len).toNat + c.C.len ≤ 2 ^ 64 := by
    have := hp.sig_fit
    rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (show c.C.len < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  refine WP.mono (setupLoad_ok hc (s := s₂) (i := PT) (src := .r6) (p := s₀.gpr .r5 + BitVec.ofNat 64 c.C.len)
    (S₂.ws.of_kp kw₂) (by decide) (by decide) (by simp only [write_gpr, ite_true, r12₂]) hfitS
    (fun e he => ⟨⟨s₀.gpr .r5, 2 * c.C.len⟩, by rw [kw₂.rd, kw₂.wr, hrw₂, hp.rd]; simp, by
      rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by have := hp.sig_fit; omega)⟩)
    (hsg.sub_left (Offset.sub_base _ (d := c.C.len) (n := c.C.len) (by omega))) (by simp only [write_mem]; exact Outside.refl _ _ _ _))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have U₃ : Unch base (slW c [PT]) s₂.mem s₃.mem := O₃.unch
  rw [bytesAt_keep W₂ (hsg.sub_left (Offset.sub_base _ (d := c.C.len) (n := c.C.len) (by omega))) (by omega) (by omega)] at e₃
  have K₃ := S₂.toKeep.step h7 (((kw₂.mono (rs' := [.r6, .r8, .r9]) (by decide)).trans
    (k₃.mono (by decide))).rk (rs' := [.r6, .r8, .r9])) (hU := U₃) (hW := fixedOk_slW (l := [PT]) (by decide))
    (hWs := slW_le h7 (by decide))
  have v₃ : ∀ {i}, i < 45 → i ≠ PT → sv c base s₃ i = sv c base s₂ i := fun hi hl =>
    sv_unch U₃ h7 hn hi (apart_slW (by simpa using hl))
  -- The key.
  have hq₃ : s₃.gpr .r14 = s₀.gpr .r3 := K₃.r14
  refine WP.seq (WP.mono (peer_ok hc K₃.ws (q := .r14) (by decide) (by rw [hq₃]; exact hp.pk_fit)
    (by rw [hq₃, K₃.rk.rd, K₃.rk.wr, hp.rd]; simp) (by rw [hq₃]; exact hpk) K₃.fixed.mp)
    fun s₄ ⟨hw₄, k₄, U₄, r2₄, bp₄, x₄, y₄, f₄⟩ => ?_)
  rw [hq₃] at x₄ y₄ f₄
  have K₄ := K₃.step h7 (k₄.rk (rs' := peerClob)) (hU := U₄)
    (hW := (fixedOk_slW (by decide)).append fixedOk_flag) (hWs := le_append (slW_le h7 (by decide)) (flag_le h7))
  have e₄ : ∀ {i}, i < 45 → i ∉ [R2P, BP, E, QY] → i ≠ FLAG → sv c base s₄ i = sv c base s₃ i :=
    fun hi hl hf => sv_unch U₄ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  have W₃ : Outside base 0 size s₀.mem s₃.mem := W₂.trans (O₃.mono (Nat.zero_le _) (by omega))
  have x₄' : sv c base s₄ E = keyX c s₀ := by
    rw [x₄, bytesAt_keep W₃ (hpk.sub_left (Offset.sub_base _ (by omega))) (by omega) (by omega)]
  have y₄' : sv c base s₄ QY = keyY c s₀ := by
    rw [y₄, bytesAt_keep W₃ (hpk.sub_left (Offset.sub_base _ (by omega))) (by omega) (by omega)]
  have hq0 : s₃.mem (s₀.gpr .r3) = s₀.mem (s₀.gpr .r3) := by
    have := keep_of_disjoint' W₃ hpk (by omega) (i := 0) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  have fl₃ : flagW c base s₃ = BitVec.allOnes 64 := by
    rw [flagW, U₃.word (fun w hw => (apart_slW (c := c) (l := [PT])
      (i := FLAG) (by decide) w hw).imp (fun h => by omega) id) (by have := sl_le c h7 (i := FLAG) (by decide); omega)]
    exact S₂.flag
  have hf₄ : flagW c base s₄ = mask64 (((s₀.mem (s₀.gpr .r3) = 4 ∧
      sv c base s₄ E < c.C.p) ∧ sv c base s₄ QY < c.C.p)) := by
    rw [f₄, hq0, fl₃, BitVec.allOnes_and, mask64_and, mask64_and]
  refine WP.seq (WP.mono (validate_ok hc K₄.ws K₄.fixed r2₄ bp₄ hf₄)
    fun s₅ ⟨hw₅, g₅, U₅, f₅, px_lt, py_lt, px, py⟩ => h s₅ ?_)
  have K₅ := K₄.step h7 g₅ (hU := U₅) (hW := fixedOk_valW h7) (hWs := valW_le h7)
  have e₅ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, W0, W1, W2, W3, PY] → i ≠ FLAG → sv c base s₅ i = sv c base s₄ i :=
    fun hi hl hf => sv_unch U₅ h7 hn hi (apart_append (apart_slW hl)
      (show ∀ w ∈ [(own c.n, 64 * c.n)] ++ [(c.sl FLAG, 8)], _ from
        apart_append (apart_own h7 hi) (apart_flag h0 hf)))
  have a₅ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, W0, W1, W2, W3, PY] → i ∉ [R2P, BP, E, QY] → i ≠ FLAG →
      i ≠ PT → sv c base s₅ i = sv c base s₂ i := fun hi h₁ h₂ hf hp =>
    ((e₅ hi h₁ hf).trans (e₄ hi h₂ hf)).trans (v₃ hi hp)
  have t₅ : ∀ {j}, j < 3 → ∀ t < 64 * c.n,
      s₅.mem (off base (bitsAt c.n j + t)) = s₂.mem (off base (bitsAt c.n j + t)) :=
    fun hj t ht => by
      rw [tbl_unch U₅ h7 hj ht (tbl_apart_valW h7 h0 _ t),
        tbl_unch U₄ h7 hj ht (apart_append (tbl_apart_slW h7 (by decide) _ t) (tbl_apart_flag h7 h0 _ t)),
        tbl_unch U₃ h7 hj ht (tbl_apart_slW h7 (by decide) _ t)]
  have hok : PeerOk c base s₄ ((s₀.mem (s₀.gpr .r3) = 4 ∧ sv c base s₄ E < c.C.p) ∧
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
