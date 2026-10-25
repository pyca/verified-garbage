module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Rep
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Lays
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.Weierstrass.Pow
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.LadderP

/-!
# ECDSA on PPC64LE: the setup, the tables of bits, `[k]G` and `Z^(p-2)`

The stages the signature, the public key and ECDH share, as on 32-bit ARM
(`Proof/Ecdsa/Arm/Stages.lean`, `Main.lean`): the setup (`stage₁`, to
`St₀`), the tables of bits of `k`, `p - 2` and `n - 2` (`tables_ok`, to
`St₁`), and `[k]P` by the ladder over the point functions and `Z^(p-2)`
(`stage₂`, to `St₂`), for the point `P` the ladder's `G` slots hold. What
every stage keeps is `Keep`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Weierstrass.PPC64LE.Point VG.Spec.Weierstrass

variable {c : Cfg} {A : Args}

/-- The arguments' numbers, as the setup reads them (the slot `A.hs`
shifted). -/
abbrev kv (c : Cfg) (A : Args) (s₀ : State) : Nat :=
  ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr A.k) c.C.len) >>> shAt c A.hs K
abbrev dv (c : Cfg) (A : Args) (s₀ : State) : Nat :=
  ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr A.d) c.C.len) >>> shAt c A.hs D
abbrev ev (c : Cfg) (A : Args) (s₀ : State) : Nat :=
  ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr A.e) c.C.len) >>> shAt c A.hs E

/-- The registers the stages may change. -/
abbrev work : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r31]

/-- What the stages keep: the working space at `r3`, the registers but
`work`, the regions and `sp`, `out` in `r14`, the constants and the saved
registers; they write only in the working space. -/
structure Keep (c : Cfg) (s₀ : State) (base : Addr) (s : State) : Prop where
  ws : WsReg s base
  rk : Rk work s₀ s
  r14 : s.gpr .r14 = s₀.gpr .r3
  fixed : Fixed c base s₀.gpr s₀.lr s.mem
  whole : Unch base [(0, size)] s₀.mem s.mem

/-- A stage that changes only registers of `work` and memory in `W`
(missing the constants and in the working space) keeps `Keep`. -/
theorem Keep.step {s₀ : State} {base : Addr} {s s' : State} (K : Keep c s₀ base s) (h7 : c.n < 10)
    {rs : List Reg} (hk : Rk rs s s') (hrs : ∀ r ∈ rs, r ∈ work := by decide) (h3 : Reg.r3 ∉ rs := by decide)
    (h14 : Reg.r14 ∉ rs := by decide)
    {W : List (Nat × Nat)} (hU : Unch base W s.mem s'.mem) (hW : FixedOk c W) (hWs : ∀ w ∈ W, w.1 + w.2 ≤ size) :
    Keep c s₀ base s' :=
  ⟨K.ws.of_rk hk h3, K.rk.trans (hk.mono hrs), by rw [hk.gpr _ h14, K.r14], K.fixed.unch h7 K.ws.nowrap hW hU,
    fun x hx => by
      have h := hx (0, size) (List.mem_singleton_self _)
      have hx' : size ≤ ofs base x := by dsimp only at h; omega_arith
      rw [hU x (fun w hw => Or.inr (by have := hWs w hw; omega_arith)), K.whole x hx]⟩

/-- After the setup. -/
structure St₀ (c : Cfg) (A : Args) (s₀ : State) (base : Addr) (F : BitVec 64) (s : State) : Prop
    extends Keep c s₀ base s where
  k : sv c base s K = kv c A s₀
  d : sv c base s D = dv c A s₀
  e : sv c base s E = ev c A s₀
  rx : sv c base s RX = 0
  ry : sv c base s RY = c.mont 1
  rz : sv c base s RZ = 0
  expp : sv c base s EXPP = c.C.p - 2
  expn : sv c base s EXPN = c.C.n - 2
  flag : flagW c base s = F

/-- After the setup and the tables. -/
structure St₁ (c : Cfg) (A : Args) (s₀ : State) (base : Addr) (F : BitVec 64) (s : State) : Prop
    extends Keep c s₀ base s where
  k : sv c base s K = kv c A s₀
  d : sv c base s D = dv c A s₀
  e : sv c base s E = ev c A s₀
  rx : sv c base s RX = 0
  ry : sv c base s RY = c.mont 1
  rz : sv c base s RZ = 0
  flag : flagW c base s = F
  t₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if (kv c A s₀).testBit t then 1 else 0
  t₁ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0
  t₂ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 2 + t)) = if (c.C.n - 2).testBit t then 1 else 0

/-- The setup. -/
theorem stage₀' (hc : CfgOk c) {s₀ : State} (hp : SetupPre c A s₀) :
    WP isa (.block (c.setupWith A)) s₀ fun s =>
      St₀ c A s₀ (s₀.gpr A.sc) (BitVec.allOnes 64) s ∧ Kp setupClob s₀ s := by
  refine WP.mono (setup_ok hc hp) fun s P => ?_
  have hc' : ∀ ix ∈ c.consts, sv c (s₀.gpr A.sc) s ix.1 = ix.2 := P.consts
  have fx : Fixed c (s₀.gpr A.sc) s₀.gpr s₀.lr s.mem :=
    ⟨hc' (MP, c.C.p) (by simp [Cfg.consts]), hc' (MN, c.C.n) (by simp [Cfg.consts]),
      hc' (ZERO, 0) (by simp [Cfg.consts]), hc' (ONE, 1) (by simp [Cfg.consts]),
      (hc' (ONEP, c.mont 1) (by simp [Cfg.consts])).trans (by simp only [Cfg.mont, Cfg.R, Nat.one_mul]),
      hc' (AP, c.mont c.C.a) (by simp [Cfg.consts]), hc' (B3P, c.mont (3 * c.C.b)) (by simp [Cfg.consts]),
      hc' (GX, c.mont c.C.gx) (by simp [Cfg.consts]), hc' (GY, c.mont c.C.gy) (by simp [Cfg.consts]),
      hc' (R2N, c.R * c.R % c.C.n) (by simp [Cfg.consts]), hc' (ONEN, c.R % c.C.n) (by simp [Cfg.consts]),
      P.saved, P.savedLr⟩
  refine ⟨⟨⟨P.ws, P.keep.rk, P.r14, fx, P.unch.cover fun w hw => ⟨(0, size), List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hw]; decide⟩⟩, P.k, P.d, P.e,
    hc' (RX, 0) (by simp [Cfg.consts]), hc' (RY, c.mont 1) (by simp [Cfg.consts]),
    hc' (RZ, 0) (by simp [Cfg.consts]), hc' (EXPP, c.C.p - 2) (by simp [Cfg.consts]),
    hc' (EXPN, c.C.n - 2) (by simp [Cfg.consts]), P.flag⟩, ?_⟩
  exact P.keep

theorem stage₀ (hc : CfgOk c) {s₀ : State} (hp : SetupPre c A s₀) :
    WP isa (.block (c.setupWith A)) s₀ (St₀ c A s₀ (s₀.gpr A.sc) (BitVec.allOnes 64)) :=
  WP.mono (stage₀' hc hp) fun _ h => h.1

/-- The tables of bits of `k`, `p - 2` and `n - 2`. -/
theorem tables_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {F : BitVec 64} {s : State}
    (S : St₀ c A s₀ base F s) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', St₁ c A s₀ base F s' → Kp bitsClob s s' → WP isa rest s' Q) :
    WP isa (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n))
      (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) rest))) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := S.ws.nowrap
  have hbl : ∀ j < 3, ∀ w ∈ [(bitsAt c.n j, 64 * c.n)], w.1 + w.2 ≤ size := fun j hj w hw => by
    rw [List.mem_singleton.mp hw]; exact bitsAt_le c h7 hj
  -- The table of `k`.
  refine WP.seq (WP.mono (tbl_bits_ok hc S.ws (i := K) (j := 0) (by decide) (by decide))
    fun s₂ ⟨b₂, k₂, O₂⟩ => ?_)
  have u₂ := O₂.unch
  have K₂ := S.toKeep.step h7 (k₂.rk (rs' := bitsClob)) (hU := u₂) (hW := fixedOk_tbl h7 0) (hWs := hbl 0 (by decide))
  have v₂ : ∀ {i}, i < 45 → sv c base s₂ i = sv c base s i := fun hi =>
    sv_unch u₂ h7 hn hi (apart_tbl h7 hi 0)
  -- The table of `p - 2`.
  refine WP.seq (WP.mono (tbl_bits_ok hc K₂.ws (i := EXPP) (j := 1) (by decide) (by decide))
    fun s₃ ⟨b₃, k₃, O₃⟩ => ?_)
  have u₃ := O₃.unch
  have K₃ := K₂.step h7 (k₃.rk (rs' := bitsClob)) (hU := u₃) (hW := fixedOk_tbl h7 1) (hWs := hbl 1 (by decide))
  have v₃ : ∀ {i}, i < 45 → sv c base s₃ i = sv c base s i := fun hi =>
    (sv_unch u₃ h7 hn hi (apart_tbl h7 hi 1)).trans (v₂ hi)
  -- The table of `n - 2`.
  refine WP.seq (WP.mono (tbl_bits_ok hc K₃.ws (i := EXPN) (j := 2) (by decide) (by decide))
    fun s₄ ⟨b₄, k₄, O₄⟩ => h s₄ ?_ ((k₂.trans k₃).trans k₄))
  have u₄ := O₄.unch
  have K₄ := K₃.step h7 (k₄.rk (rs' := bitsClob)) (hU := u₄) (hW := fixedOk_tbl h7 2) (hWs := hbl 2 (by decide))
  have v₄ : ∀ {i}, i < 45 → sv c base s₄ i = sv c base s i := fun hi =>
    (sv_unch u₄ h7 hn hi (apart_tbl h7 hi 2)).trans (v₃ hi)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have apF : ∀ j, ∀ w ∈ [(bitsAt c.n j, 64 * c.n)], c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG :=
    fun j w hw => by
      rw [List.mem_singleton.mp hw]
      have := sl_below_bits c h7 (i := FLAG) (by decide) j 0
      exact Or.inl (by dsimp only; omega_arith)
  refine ⟨K₄, by rw [v₄ (by decide), S.k], by rw [v₄ (by decide), S.d], by rw [v₄ (by decide), S.e],
    by rw [v₄ (by decide), S.rx], by rw [v₄ (by decide), S.ry], by rw [v₄ (by decide), S.rz], ?_, ?_, ?_, ?_⟩
  · rw [flagW, u₄.word (apF 2) (by omega_arith), u₃.word (apF 1) (by omega_arith), u₂.word (apF 0) (by omega_arith), ← flagW,
      S.flag]
  · intro t ht
    rw [tbl_unch u₄ h7 (j := 0) (by decide) ht (tbl_apart_tbl (by decide) ht),
      tbl_unch u₃ h7 (j := 0) (by decide) ht (tbl_apart_tbl (by decide) ht), b₂ t ht,
      show wordsVal s.mem base (c.sl K) c.n = kv c A s₀ from S.k]
  · intro t ht
    rw [tbl_unch u₄ h7 (j := 1) (by decide) ht (tbl_apart_tbl (by decide) ht), b₃ t ht,
      show wordsVal s₂.mem base (c.sl EXPP) c.n = c.C.p - 2 from (v₂ (by decide)).trans S.expp]
  · intro t ht
    rw [b₄ t ht, show wordsVal s₃.mem base (c.sl EXPN) c.n = c.C.n - 2 from (v₃ (by decide)).trans S.expn]

/-- The setup, then the three tables. -/
theorem stage₁ (hc : CfgOk c) {s₀ : State} (hp : SetupPre c A s₀) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s, St₁ c A s₀ (s₀.gpr A.sc) (BitVec.allOnes 64) s → WP isa rest s Q) :
    WP isa (.seq (.block (c.setupWith A)) (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n))
      (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n))
      (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) rest)))) s₀ Q :=
  WP.seq (WP.mono (stage₀ hc hp) fun _ S => tables_ok hc S fun s' S' _ => h s' S')

/-! ## `[k]P` and `Z^(p-2)` -/

theorem toM_cmont (hc : CfgOk c) (x : Nat) : toM c.C.p (2 ^ (64 * c.n)) (c.mont x) = Fin.ofNat c.C.p x :=
  toM_mont (unitMod_pow_two hc.p_odd _)

theorem mul_zero_pt (P : Point c.C) : Spec.Weierstrass.mul 0 P = .infinity := by
  rw [Spec.Weierstrass.mul]; simp

theorem ladPtLay (hc : CfgOk c) (h3 : 3 ≤ c.n) (h6 : c.n ≤ 6) {gx gy : Nat} (hgx : gx < 45) (hgy : gy < 45) :
    LadPtLay (ladderAt c gx gy) where
  k3 := h3
  k6 := h6
  a := sl_below_pt h3 h6 (by decide)
  b3 := sl_below_pt h3 h6 (by decide)
  gx := sl_below_pt h3 h6 hgx
  gy := sl_below_pt h3 h6 hgy
  gz := sl_below_pt h3 h6 (by decide)
  rx := sl_below_pt h3 h6 (by decide)
  ry := sl_below_pt h3 h6 (by decide)
  rz := sl_below_pt h3 h6 (by decide)
  al := ⟨sl_al c _, sl_al c _, sl_al c _, sl_al c _, sl_al c _, sl_al c _, sl_al c _, sl_al c _⟩
  rne := ⟨sl_apart c (by decide), sl_apart c (by decide), sl_apart c (by decide)⟩
  bits := by show 4096 ≤ bitsAt c.n 0; rw [bitsAt_eq]; omega_arith
  bitsE := by
    show bitsAt c.n 0 + 8 * c.C.len ≤ 8192
    rw [bitsAt_eq]; have := hc.len_hi; have := hc.n10; omega_arith
  nbits := by
    show 1 ≤ 8 * c.C.len ∧ 8 * c.C.len < 2 ^ 15
    have := hc.len_hi; have := hc.len8; have := hc.n10; omega_arith

theorem powLayP (hc : CfgOk c) : PowLayP c.powP c.n where
  acc := sl_below_own c hc.n10 (by decide)
  tmp := sl_below_own c hc.n10 (by decide)
  base := sl_below_own c hc.n10 (by decide)
  one := sl_below_own c hc.n10 (by decide)
  own := own_below_bits c hc.n10 1
  bits := bitsAt_le c hc.n10 (j := 1) (by decide)
  nbits := by show 1 ≤ 64 * c.n ∧ 64 * c.n < 2 ^ 15; have := hc.n0; have := hc.n10; omega_arith
  acc_tmp := sl_apart c (by decide)
  acc_one := sl_apart c (by decide)
  base_acc := sl_apart c (by decide)
  base_tmp := sl_apart c (by decide)
  acc4 := sl_al c _
  tmp4 := sl_al c _
  one4 := sl_al c _

theorem powLayN (hc : CfgOk c) : PowLayP c.powN c.n where
  acc := sl_below_own c hc.n10 (by decide)
  tmp := sl_below_own c hc.n10 (by decide)
  base := sl_below_own c hc.n10 (by decide)
  one := sl_below_own c hc.n10 (by decide)
  own := own_below_bits c hc.n10 2
  bits := bitsAt_le c hc.n10 (j := 2) (by decide)
  nbits := by show 1 ≤ 64 * c.n ∧ 64 * c.n < 2 ^ 15; have := hc.n0; have := hc.n10; omega_arith
  acc_tmp := sl_apart c (by decide)
  acc_one := sl_apart c (by decide)
  base_acc := sl_apart c (by decide)
  base_tmp := sl_apart c (by decide)
  acc4 := sl_al c _
  tmp4 := sl_al c _
  one4 := sl_al c _

theorem modP (hc : CfgOk c) : ModOk c.n c.C.p := by
  have h := hc.fp; rw [hc.fpk, hc.fpm] at h; exact h

theorem modN (hc : CfgOk c) : ModOk c.n c.C.n := by
  have h := hc.fn; rw [hc.fnk, hc.fnm] at h; exact h

/-- After `[k]P` and `Z^(p-2)`. -/
structure St₂ (c : Cfg) (A : Args) (s₀ : State) (base : Addr) (F : BitVec 64) (P : Point c.C) (s : State) : Prop
    extends Keep c s₀ base s where
  k : sv c base s K = kv c A s₀
  d : sv c base s D = dv c A s₀
  e : sv c base s E = ev c A s₀
  flag : flagW c base s = F
  t₂ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 2 + t)) = if (c.C.n - 2).testBit t then 1 else 0
  rep : Rep c.C (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
    (tmv c.C c.n base s (c.sl RZ)) (mul (kv c A s₀) P)
  rx_lt : sv c base s RX < c.C.p
  ry_lt : sv c base s RY < c.C.p
  rz_lt : sv c base s RZ < c.C.p
  acc_lt : sv c base s ACC < c.C.p
  acc : toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) = tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2)

theorem powWxP_eq : powWx c.powP c.n = [(c.sl ACC, 8 * c.n), (c.sl PT, 8 * c.n), (own c.n, 64 * c.n)] := rfl
theorem powWxN_eq : powWx c.powN c.n = [(c.sl ACC, 8 * c.n), (c.sl PT, 8 * c.n), (own c.n, 64 * c.n)] := rfl

theorem apart_powWx (h7 : c.n < 10) {i : Nat} (hi : i < 45) (hr : i ∉ [ACC, PT]) :
    ∀ w ∈ [(c.sl ACC, 8 * c.n), (c.sl PT, 8 * c.n), (own c.n, 64 * c.n)],
      c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact sl_apart c hr.1
  · exact sl_apart c hr.2
  · exact Or.inl (sl_below_own c h7 hi)

theorem fixedOk_powWx (h7 : c.n < 10) : FixedOk c [(c.sl ACC, 8 * c.n), (c.sl PT, 8 * c.n), (own c.n, 64 * c.n)] :=
  (fixedOk_slW (l := [ACC, PT]) (by decide)).append (fixedOk_own h7)

theorem powWx_le (h7 : c.n < 10) : ∀ w ∈ [(c.sl ACC, 8 * c.n), (c.sl PT, 8 * c.n), (own c.n, 64 * c.n)],
    w.1 + w.2 ≤ size := by
  have := sl_le c h7 (i := ACC) (by decide)
  have := sl_le c h7 (i := PT) (by decide)
  have := own_eq c.n
  have hsz : size = 8192 := rfl
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> (dsimp only; omega_arith)

theorem tbl_apart_powWx (h7 : c.n < 10) (j t : Nat) :
    ∀ w ∈ [(c.sl ACC, 8 * c.n), (c.sl PT, 8 * c.n), (own c.n, 64 * c.n)],
      bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  have := sl_below_bits c h7 (i := ACC) (by decide) j t
  have := sl_below_bits c h7 (i := PT) (by decide) j t
  have := own_below_bits c h7 j
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> (dsimp only; omega_arith)

/-- What the ladder and the power leave, from `s`: `R` holds `[k]P`, `ACC`
`Z^(p-2)`, and the other slots, the flag and the table of `n - 2` are
unchanged. -/
structure LadPost (c : Cfg) (s₀ : State) (base : Addr) (k : Nat) (P : Point c.C) (s s' : State) : Prop
    extends Keep c s₀ base s' where
  same : ∀ {i}, i < 45 → i ∉ ACC :: PT :: ladIx → sv c base s' i = sv c base s i
  flag : flagW c base s' = flagW c base s
  t₂ : ∀ t < 64 * c.n, s'.mem (off base (bitsAt c.n 2 + t)) = s.mem (off base (bitsAt c.n 2 + t))
  rep : Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
    (tmv c.C c.n base s' (c.sl RZ)) (mul k P)
  rx_lt : sv c base s' RX < c.C.p
  ry_lt : sv c base s' RY < c.C.p
  rz_lt : sv c base s' RZ < c.C.p
  acc_lt : sv c base s' ACC < c.C.p
  acc : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) = tmv c.C c.n base s' (c.sl RZ) ^ (c.C.p - 2)

/-- `[k]P` by the ladder over the point functions, for the point `P` the
slots `gx`, `gy` and `ONEP` represent and the table of bits of any `k` of
`8 len` bits, from `R = O`, then `Z^(p-2)`. -/
theorem ladPow_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) (hC : Law c.C) {gx gy : Nat} (hgx : gx < 45)
    (hgy : gy < 45) (hgw : gx ∉ MP :: ladIx) (hgw' : gy ∉ MP :: ladIx) {s₀ : State} {base : Addr} {s : State} (S : Keep c s₀ base s) {k : Nat}
    (hkl : k < 2 ^ (8 * c.C.len)) (hrx : sv c base s RX = 0) (hry : sv c base s RY = c.mont 1)
    (hrz : sv c base s RZ = 0)
    (ht₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
    (ht₁ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0)
    {P : Point c.C} (hP : onCurve c.C P = true)
    (hG : Rep c.C (tmv c.C c.n base s (c.sl gx)) (tmv c.C c.n base s (c.sl gy)) (tmv c.C c.n base s (c.sl ONEP)) P)
    (hlx : sv c base s gx < c.C.p) (hly : sv c base s gy < c.C.p)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', LadPost c s₀ base k P s s' → WP isa rest s' Q) :
    WP isa (.seq (Point.ladderP (ladderAt c gx gy) c.SP) (.seq (pow c.powP c.SP) rest)) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := S.ws.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have F' := S.fixed
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  have hlt : ∀ x ∈ [(ladderAt c gx gy).S.a, (ladderAt c gx gy).S.b3, (ladderAt c gx gy).G.x,
      (ladderAt c gx gy).G.y, (ladderAt c gx gy).G.z, (ladderAt c gx gy).R.x, (ladderAt c gx gy).R.y,
      (ladderAt c gx gy).R.z], wordsVal s.mem base x (ladderAt c gx gy).M.n < c.C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F'.ap (hmont _)
    · exact lt_of_eq_of_lt F'.b3p (hmont _)
    · exact hlx
    · exact hly
    · exact lt_of_eq_of_lt F'.onep (Nat.mod_lt _ (by omega_arith))
    · exact lt_of_eq_of_lt hrx (by omega_arith)
    · exact lt_of_eq_of_lt hry (hmont _)
    · exact lt_of_eq_of_lt hrz (by omega_arith)
  have hstep := step_rep (L := ladderAt c gx gy) (k := k) hC hP (by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl AP) c.n) = _
      rw [F'.ap]; exact toM_cmont hc _)
    (by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl B3P) c.n) = _
      rw [F'.b3p]; exact toM_cmont hc _) hG
  have hR : Rep c.C (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
      (tmv c.C c.n base s (c.sl RZ)) (mul (k >>> (8 * c.C.len)) P) := by
    show Rep c.C (toM _ _ (sv c base s RX)) (toM _ _ (sv c base s RY)) (toM _ _ (sv c base s RZ)) _
    rw [hrx, hry, hrz, toM_cmont hc, toM_zero, shiftRight_eq_zero hkl, mul_zero_pt]
    exact rep_infinity' hC
  refine WP.seq (WP.mono (ladderP_ok (L := ladderAt c gx gy) (S := c.SP) hc.fpk hc.fpm (modP hc) hc.p_odd hpR
    (fun h6 => ladPtLay hc h3 h6 hgx hgy) (fun _ => ladLayI hc hgx hgy hgw hgw') S.ws hlt hstep hR
    (fun t ht => ht₀ t (by have := hc.len_hi; show t < 64 * c.n; change t < 8 * c.C.len at ht; omega_arith)))
    fun s₅ ⟨K₅, U₅, L₅, R₅⟩ => ?_)
  rw [Nat.shiftRight_zero] at R₅
  have K₅' : Keep c s₀ base s₅ := S.step h7 K₅ (hU := U₅) (hW := fixedOk_ladWp h3 h7 gx gy)
    (hWs := ladWp_le h3 h7 gx gy)
  have e₅ : ∀ {i}, i < 45 → i ∉ ladIx → sv c base s₅ i = sv c base s i := fun hi hr =>
    sv_unch U₅ h7 hn hi (apart_ladWp h3 h7 hi hr)
  have lx₅ : sv c base s₅ RX < c.C.p := L₅ _ (List.mem_cons_self ..)
  have ly₅ : sv c base s₅ RY < c.C.p := L₅ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have lz₅ : sv c base s₅ RZ < c.C.p :=
    L₅ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  refine WP.seq (WP.mono (pow_ok (P := c.powP) (S := c.SP) (e := c.C.p - 2) hc.fpk hc.fpm (modP hc) rfl
    (powLayP hc) hpR K₅'.ws lz₅ K₅'.fixed.onep
    (fun t ht => by
      show s₅.mem (off base (bitsAt c.n 1 + t)) = _
      rw [tbl_unch U₅ h7 (j := 1) (by decide) ht (tbl_apart_ladWp h3 h7 gx gy 1 t)]
      exact ht₁ t ht)
    (show c.C.p - 2 < 2 ^ (64 * c.n) by have := hc.p_lt; omega_arith)) fun s₆ ⟨K₆, U₆, lt₆, v₆⟩ => h s₆ ?_)
  rw [powWxP_eq] at U₆
  have K₆' : Keep c s₀ base s₆ := K₅'.step h7 K₆ (hU := U₆) (hW := fixedOk_powWx h7) (hWs := powWx_le h7)
  have e₆ : ∀ {i}, i < 45 → i ∉ [ACC, PT] → sv c base s₆ i = sv c base s₅ i := fun hi hr =>
    sv_unch U₆ h7 hn hi (apart_powWx h7 hi hr)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have apF₅ : ∀ w ∈ ladWp (ladderAt c gx gy), c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := fun w hw => by
    rcases apart_ladWp h3 h7 (i := FLAG) (gx := gx) (gy := gy) (by decide) (by decide) w hw with h | h
    · exact Or.inl (by omega_arith)
    · exact Or.inr h
  have apF₆ : ∀ w ∈ [(c.sl ACC, 8 * c.n), (c.sl PT, 8 * c.n), (own c.n, 64 * c.n)],
      c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := fun w hw => by
    rcases apart_powWx h7 (i := FLAG) (by decide) (by decide) w hw with h | h
    · exact Or.inl (by omega_arith)
    · exact Or.inr h
  have tR : ∀ i ∈ [RX, RY, RZ], tmv c.C c.n base s₆ (c.sl i) = tmv c.C c.n base s₅ (c.sl i) := by
    intro i hi
    show toM _ _ (sv c base s₆ i) = toM _ _ (sv c base s₅ i)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> rw [e₆ (by decide) (by decide)]
  refine ⟨K₆', fun hi hl => ?_, by rw [flagW, U₆.word apF₆ (by omega_arith), U₅.word apF₅ (by omega_arith), ← flagW], ?_,
    by rw [tR RX (by simp), tR RY (by simp), tR RZ (by simp)]; exact R₅,
    by rw [e₆ (by decide) (by decide)]; exact lx₅,
    by rw [e₆ (by decide) (by decide)]; exact ly₅,
    by rw [e₆ (by decide) (by decide)]; exact lz₅, lt₆, ?_⟩
  · rw [e₆ hi (nmem_of hl (by decide)), e₅ hi (nmem_of hl (by decide))]
  · intro t ht
    rw [tbl_unch U₆ h7 (j := 2) (by decide) ht (tbl_apart_powWx h7 2 t),
      tbl_unch U₅ h7 (j := 2) (by decide) ht (tbl_apart_ladWp h3 h7 gx gy 2 t)]
  · rw [tR RZ (by simp)]; exact v₆

/-- `[k]P` and `Z^(p-2)`, after the setup and the tables. -/
theorem stage₂ (hc : CfgOk c) (h3 : 3 ≤ c.n) (hC : Law c.C) {gx gy : Nat} (hgx : gx < 45)
    (hgy : gy < 45) (hgw : gx ∉ MP :: ladIx) (hgw' : gy ∉ MP :: ladIx) {s₀ : State} {base : Addr} {F : BitVec 64} {s : State} (S : St₁ c A s₀ base F s)
    {P : Point c.C} (hP : onCurve c.C P = true)
    (hG : Rep c.C (tmv c.C c.n base s (c.sl gx)) (tmv c.C c.n base s (c.sl gy)) (tmv c.C c.n base s (c.sl ONEP)) P)
    (hlx : sv c base s gx < c.C.p) (hly : sv c base s gy < c.C.p)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', St₂ c A s₀ base F P s' → WP isa rest s' Q) :
    WP isa (.seq (Point.ladderP (ladderAt c gx gy) c.SP) (.seq (pow c.powP c.SP) rest)) s Q :=
  ladPow_ok hc h3 hC hgx hgy hgw hgw' S.toKeep (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (ofBytes_bytesAt_lt _ _ _))
    S.rx S.ry S.rz S.t₀ S.t₁ hP hG hlx hly fun s' L => h s'
      ⟨L.toKeep, by rw [L.same (by decide) (by decide), S.k], by rw [L.same (by decide) (by decide), S.d],
        by rw [L.same (by decide) (by decide), S.e], by rw [L.flag, S.flag],
        fun t ht => by rw [L.t₂ t ht, S.t₂ t ht], L.rep, L.rx_lt, L.ry_lt, L.rz_lt, L.acc_lt, L.acc⟩

end VG.Proof.Ecdsa.PPC64LE
