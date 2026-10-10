import VerifiedGarbage.Proof.Ecdh.Arm.Validate
import VerifiedGarbage.Impl.Ecdsa.Verify.Arm

/-!
# ECDSA verification on 32-bit ARM: the arguments and the key

As on x86 (`Proof/Ecdsa/Verify/X86/Front.lean`).

`front_ok`: the signature's setup and tables (`stage₁`, with
`Args.verify`, which leave `public` in `r0` and `sig` in `r2`), the load of
`s` and ECDH's checks of the key (`peer_ok` of `r0`, `validate_ok`) leave
`r`, the hash and `s` in their slots, `R = O`, the tables of `p - 2` and
`n - 2`, the flag of the key's validity as the code checks it (`KeyOk`),
and the key's point, or `G` if it is not valid, for ECDH's ladder (`Front`).
-/

namespace VG.Proof.Ecdsa.Verify.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdh.Arm
open VG.Proof.X25519.Arm (Rest wp_dp op2_imm ea toNat_add_lt toNat_imm)
open VG.Impl.Ecdh.Arm (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)
open VG.Impl.Ecdsa.Verify.Arm (Args.verify)

variable {c : Cfg}

/-- The arguments: `public` (`1 + 2 len` bytes), `digest` (`len` bytes),
`sig` (`2 len` bytes) and `scratch`, readable and writable as the contract
says and apart from `scratch`. -/
structure VPre (c : Cfg) (s : State) : Prop where
  rd : s.rd = [⟨ptr s .r0, 1 + 2 * c.C.len⟩, ⟨ptr s .r1, c.C.len⟩, ⟨ptr s .r2, 2 * c.C.len⟩]
  wr : s.wr = [⟨ptr s .r3, 8192⟩]
  pk_sc : Region.Disjoint ⟨ptr s .r0, 1 + 2 * c.C.len⟩ ⟨ptr s .r3, 8192⟩
  dg_sc : Region.Disjoint ⟨ptr s .r1, c.C.len⟩ ⟨ptr s .r3, 8192⟩
  sig_sc : Region.Disjoint ⟨ptr s .r2, 2 * c.C.len⟩ ⟨ptr s .r3, 8192⟩
  pk_fit : (s.gpr .r0).toNat + (1 + 2 * c.C.len) ≤ 2 ^ 32
  dg_fit : (s.gpr .r1).toNat + c.C.len ≤ 2 ^ 32
  sig_fit : (s.gpr .r2).toNat + 2 * c.C.len ≤ 2 ^ 32
  sc_fit : (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32

/-- The key's `x` and `y`, the hash, and the signature's `r` and `s`. -/
abbrev keyX (c : Cfg) (s₀ : State) : Nat :=
  ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r0 + BitVec.ofNat 64 1) c.C.len)
abbrev keyY (c : Cfg) (s₀ : State) : Nat :=
  ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r0 + BitVec.ofNat 64 (1 + c.C.len)) c.C.len)
abbrev dig (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r1) c.C.len) >>> c.sh
abbrev sigR (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r2) c.C.len)
abbrev sigS (c : Cfg) (s₀ : State) : Nat :=
  ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ .r2 + BitVec.ofNat 64 c.C.len) c.C.len)

/-- The key is valid as the code checks it. -/
abbrev KeyOk (c : Cfg) (s₀ : State) : Prop :=
  ((s₀.mem (ptr s₀ .r0) = 4 ∧ keyX c s₀ < c.C.p) ∧ keyY c s₀ < c.C.p) ∧
    OnCurve c (Fin.ofNat c.C.p (keyX c s₀)) (Fin.ofNat c.C.p (keyY c s₀))

/-- After the key's checks, from the state `s₀` at entry, with the working
space at `base`. -/
structure Front (c : Cfg) (s₀ : State) (base : Addr) (s : State) : Prop where
  scr : Scr s base size
  far : Far s base 8192
  rest : Rest (.lr :: work) s₀ s
  fixed : Fixed c base s₀.gpr s.mem
  k : sv c base s K = sigR c s₀
  d : sv c base s D = dig c s₀
  pt : sv c base s PT = sigS c s₀
  rx : sv c base s RX = 0
  ry : sv c base s RY = c.mont 1
  rz : sv c base s RZ = 0
  t₁ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0
  t₂ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 2 + t)) = if (c.C.n - 2).testBit t then 1 else 0
  flag : flagW c base s = mask32 (KeyOk c s₀)
  px_lt : sv c base s PX < c.C.p
  py_lt : sv c base s PY < c.C.p
  px : toM c.C.p (2 ^ (64 * c.n)) (sv c base s PX) =
    if KeyOk c s₀ then Fin.ofNat c.C.p (keyX c s₀) else Fin.ofNat c.C.p c.C.gx
  py : toM c.C.p (2 ^ (64 * c.n)) (sv c base s PY) =
    if KeyOk c s₀ then Fin.ofNat c.C.p (keyY c s₀) else Fin.ofNat c.C.p c.C.gy
  /-- Memory outside `scratch` is unchanged. -/
  unch : Unch base [(0, 8192)] s₀.mem s.mem

theorem VPre.setup {s : State} (hp : VPre c s) : SetupPre c Args.verify s where
  shift := .inr (.inl rfl)
  args := by unfold argsOk; decide
  sc_in := fun h => nomatch h
  wr := by show (⟨ptr s .r3, 8192⟩ : Region) ∈ s.wr; rw [hp.wr]; simp
  k_in := fun e he => ⟨⟨ptr s .r2, 2 * c.C.len⟩, by rw [hp.rd]; simp,
    Offset.contains_base _ (by omega_arith) (by have := hp.sig_fit; omega_arith)⟩
  d_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.dg_fit; omega_arith)
  e_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.dg_fit; omega_arith)
  k_sc := (hp.sig_sc.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Region.sub_prefix (by decide))
  d_sc := hp.dg_sc.sub_right (Region.sub_prefix (by decide))
  e_sc := hp.dg_sc.sub_right (Region.sub_prefix (by decide))
  k_fit := show (s.gpr .r2).toNat + c.C.len ≤ 2 ^ 32 by have := hp.sig_fit; omega_arith
  d_fit := hp.dg_fit
  e_fit := hp.dg_fit
  sc_fit := hp.sc_fit

/-- Ranges of the working space, as one. -/
theorem unch_whole {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (h : Unch base W m m')
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ size) : Unch base [(0, size)] m m' :=
  (h.outside fun w hw => ⟨Nat.zero_le _, by have := hW w hw; omega_arith⟩).unch

theorem slW_le (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i < 45) : ∀ w ∈ slW c l, w.1 + w.2 ≤ size := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  exact sl_le c h7 (hl i hi)

theorem loadS_eq (c : Cfg) : Impl.Ecdsa.Verify.Arm.Cfg.loadS c =
    .dp .add .r6 .r2 (.imm (BitVec.ofNat 32 c.C.len)) :: loadBytes c.C.len c.n (c.sl PT) .r6 := rfl

/-- The setup and tables, `s`, and the checks of the key. -/
theorem front_ok (hc : CfgOk c) {s₀ : State} (hp : VPre c s₀) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s, Front c s₀ (ptr s₀ .r3) s → WP isa rest s Q) :
    WP isa (.seq (Impl.Ecdsa.Verify.Arm.Cfg.prefix' c) (.seq (.block (Impl.Ecdsa.Verify.Arm.Cfg.loadS c))
      (.seq (.block (Impl.Ecdh.Arm.Cfg.peerAt c .r0)) (.seq (Impl.Ecdh.Arm.Cfg.validate c) rest)))) s₀ Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hl8 := hc.len8
  have hlhi := hc.len_hi
  have hsz : size = 4096 := rfl
  have hpk : Region.Disjoint ⟨ptr s₀ .r0, 1 + 2 * c.C.len⟩ ⟨ptr s₀ .r3, size⟩ :=
    hp.pk_sc.sub_right (Region.sub_prefix (by decide))
  have hsg : Region.Disjoint ⟨ptr s₀ .r2, 2 * c.C.len⟩ ⟨ptr s₀ .r3, size⟩ :=
    hp.sig_sc.sub_right (Region.sub_prefix (by decide))
  refine WP.seq (stage₁ hc hp.setup fun s₂ S₂ => WP.block_nil ?_)
  replace S₂ : St₁ c Args.verify s₀ (ptr s₀ .r3) s₂ := S₂
  have hn := S₂.scr.nowrap
  have W₂ : Outside (ptr s₀ .r3) 0 8192 s₀.mem s₂.mem :=
    S₂.whole.outside fun w hw => by rw [List.mem_singleton.mp hw]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  have hrw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [S₂.rest.rd, S₂.rest.wr]
  have hr0 : s₂.gpr .r0 = s₀.gpr .r0 := S₂.args .r0 (by simp)
  have hr2 : s₂.gpr .r2 = s₀.gpr .r2 := S₂.args .r2 (by simp)
  -- `s`.
  have hPT := sl_le c h7 (i := PT) (by decide)
  rw [loadS_eq]
  refine WP.seq (wp_dp (op2_imm (encLen hc)) fun s₂' u₂ => ?_)
  have k₂ : Rest [.r6] s₂ s₂' := u₂.rest (by simp)
  have hs₂ := S₂.scr.of_rest k₂ (by decide)
  have hm₂ : s₂'.mem = s₂.mem := u₂.mem
  have hb : s₂'.gpr .r6 = s₀.gpr .r2 + BitVec.ofNat 32 c.C.len := by rw [u₂.gpr, hr2]; rfl
  have hb' : State.addr (s₂'.gpr .r6) = ptr s₀ .r2 + BitVec.ofNat 64 c.C.len := by
    rw [hb]; exact ea (by have := hp.sig_fit; omega_arith)
  have hbt : (s₂'.gpr .r6).toNat = (s₀.gpr .r2).toNat + c.C.len := by
    rw [hb, toNat_add_lt (by rw [toNat_imm (by omega_arith)]; have := hp.sig_fit; omega_arith), toNat_imm (by omega_arith)]
  have hrw₂' : s₂'.rd ++ s₂'.wr = s₀.rd ++ s₀.wr := by rw [k₂.rd, k₂.wr, hrw₂]
  refine WP.mono (loadBytes_ok hs₂ (src := .r6) (by decide) hPT (by rw [hbt]; have := hp.sig_fit; omega_arith)
    (by omega_arith) hlhi (fun e he => ⟨⟨ptr s₀ .r2, 2 * c.C.len⟩, by rw [hrw₂', hp.rd]; simp, by
      rw [hb', Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (by
      rw [hb']
      exact (hsg.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ hPT)))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [hb', hm₂] at e₃
  rw [hm₂] at O₃
  have hs₃ := hs₂.of_rest k₃ (by decide)
  have K₃ : Rest [.r4, .r6] s₂ s₃ := (k₂.mono (by simp)).trans (k₃.mono (by simp))
  have U₃ : Unch (ptr s₀ .r3) (slW c [PT]) s₂.mem s₃.mem := O₃.unch
  have F₃ := S₂.fixed.unch h7 hn (fixedOk_slW (l := [PT]) (by decide)) U₃
  have v₃ : ∀ {i}, i < 45 → i ≠ PT → sv c (ptr s₀ .r3) s₃ i = sv c (ptr s₀ .r3) s₂ i := fun hi hl =>
    sv_unch U₃ h7 hn hi (apart_slW (by simpa using hl))
  have pt₃ : sv c (ptr s₀ .r3) s₃ PT = sigS c s₀ := by
    rw [sv, e₃, bytesAt_keep W₂ (hp.sig_sc.sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith) (by omega_arith)]
  have W₃ : Outside (ptr s₀ .r3) 0 8192 s₂.mem s₃.mem := O₃.mono (Nat.zero_le _) (by omega_arith)
  have hrw₃ : s₃.rd ++ s₃.wr = s₂.rd ++ s₂.wr := by rw [K₃.rd, K₃.wr]
  have hr0₃ : s₃.gpr .r0 = s₀.gpr .r0 := by rw [K₃.gpr _ (by decide), hr0]
  -- The key.
  refine WP.seq (WP.mono (peer_ok hc hs₃ (q := .r0) (by decide) (by decide) (by rw [hr0₃]; exact hp.pk_fit)
    (by rw [hr0₃, hrw₃, hrw₂, hp.rd]; simp) (by rw [hr0₃]; exact hpk) F₃.mp)
    fun s₄ ⟨hs₄, k₄, U₄, r2₄, bp₄, x₄, y₄, f₄⟩ => ?_)
  rw [hr0₃] at x₄ y₄ f₄
  have F₄ := F₃.unch h7 hn ((fixedOk_slW (l := [R2P, BP, E, QY]) (by decide)).append fixedOk_flag) U₄
  have e₄ : ∀ {i}, i < 45 → i ∉ [R2P, BP, E, QY] → i ≠ FLAG →
      sv c (ptr s₀ .r3) s₄ i = sv c (ptr s₀ .r3) s₃ i := fun hi hl hf =>
    sv_unch U₄ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  have W₃' : Outside (ptr s₀ .r3) 0 8192 s₀.mem s₃.mem := W₂.trans W₃
  have x₄' : sv c (ptr s₀ .r3) s₄ E = keyX c s₀ := by
    rw [x₄, bytesAt_keep W₃' (hp.pk_sc.sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith) (by omega_arith)]
  have y₄' : sv c (ptr s₀ .r3) s₄ QY = keyY c s₀ := by
    rw [y₄, bytesAt_keep W₃' (hp.pk_sc.sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith) (by omega_arith)]
  have hq0 : s₃.mem (ptr s₀ .r0) = s₀.mem (ptr s₀ .r0) := by
    have := keep_of_disjoint' W₃' hp.pk_sc (by omega_arith) (i := 0) (by omega_arith) (by omega_arith)
    rwa [BitVec.add_zero] at this
  have hf₄ : flagW c (ptr s₀ .r3) s₄ = mask32 (((s₀.mem (ptr s₀ .r0) = 4 ∧
      sv c (ptr s₀ .r3) s₄ E < c.C.p) ∧ sv c (ptr s₀ .r3) s₄ QY < c.C.p)) := by
    rw [f₄, flagW, flag_unch (U₃.mono fun w hw => List.mem_append_left _ hw) h7 h0 hn (l := [PT])
      (by decide), ← flagW, S₂.flag, BitVec.allOnes_and, mask32_and, mask32_and]
    simp only [hq0]
  refine WP.seq (WP.mono (validate_ok hc hs₄ ((S₂.far.of_rest K₃).of_rest k₄) F₄ r2₄ bp₄ hf₄)
    fun s₅ ⟨hs₅, g₅, U₅, f₅, px_lt, py_lt, px, py⟩ => h s₅ ?_)
  have F₅ := F₄.unch h7 hn ((fixedOk_slWk h7 (l := [QXM, QYM, TMP, W0, W1, W2, W3, PY]) (by decide)).append
    fixedOk_flag) U₅
  have e₅ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, TMP, W0, W1, W2, W3, PY] → i ≠ FLAG →
      sv c (ptr s₀ .r3) s₅ i = sv c (ptr s₀ .r3) s₄ i := fun hi hl hf =>
    sv_unch U₅ h7 hn hi (apart_append (apart_slWk h7 hi hl) (apart_flag h0 hf))
  have a₅ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, TMP, W0, W1, W2, W3, PY] → i ∉ [R2P, BP, E, QY] → i ≠ FLAG →
      i ≠ PT → sv c (ptr s₀ .r3) s₅ i = sv c (ptr s₀ .r3) s₂ i := fun hi h₁ h₂ hf hp =>
    ((e₅ hi h₁ hf).trans (e₄ hi h₂ hf)).trans (v₃ hi hp)
  have t₅ : ∀ {j}, j < 3 → ∀ t < 64 * c.n,
      s₅.mem (off (ptr s₀ .r3) (bitsAt c.n j + t)) = s₂.mem (off (ptr s₀ .r3) (bitsAt c.n j + t)) :=
    fun hj t ht => by
      rw [tbl_unch U₅ h7 hj ht (apart_append (tbl_apart_slWk h7 (by decide)) (tbl_apart_flag h7 h0 _ t)),
        tbl_unch U₄ h7 hj ht (apart_append (tbl_apart_slW h7 (by decide) _ t) (tbl_apart_flag h7 h0 _ t)),
        tbl_unch U₃ h7 hj ht (tbl_apart_slW h7 (by decide) _ t)]
  have hok : PeerOk c (ptr s₀ .r3) s₄ ((s₀.mem (ptr s₀ .r0) = 4 ∧ sv c (ptr s₀ .r3) s₄ E < c.C.p) ∧
      sv c (ptr s₀ .r3) s₄ QY < c.C.p) = KeyOk c s₀ := by
    rw [PeerOk, x₄', y₄']
  simp only [hok] at f₅ px py
  rw [x₄'] at px
  rw [y₄'] at py
  have hW4 : ∀ w ∈ slW c [R2P, BP, E, QY] ++ [(c.sl FLAG, 4)], w.1 + w.2 ≤ size :=
    le_append (slW_le h7 (by decide)) (flag_le h0 h7)
  have hW5 : ∀ w ∈ slWk c [QXM, QYM, TMP, W0, W1, W2, W3, PY] ++ [(c.sl FLAG, 4)], w.1 + w.2 ≤ size :=
    le_append (slWk_le h7 (by decide)) (flag_le h0 h7)
  refine ⟨hs₅, ((S₂.far.of_rest K₃).of_rest k₄).of_rest g₅, S₂.rest.trans
      (((K₃.mono (by decide)).trans ((k₄.mono (by decide)).trans (g₅.mono powClob_work))).mono (by simp)), F₅,
    by rw [a₅ (i := K) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.k,
      kv_eq (A := Args.verify) rfl],
    by rw [a₅ (i := D) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.d]
       show _ >>> shAt c (some D) D = _; rw [shAt_self],
    by rw [e₅ (i := PT) (by decide) (by decide) (by decide), e₄ (by decide) (by decide) (by decide), pt₃],
    by rw [a₅ (i := RX) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.rx],
    by rw [a₅ (i := RY) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.ry],
    by rw [a₅ (i := RZ) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.rz],
    fun t ht => by rw [t₅ (j := 1) (by decide) t ht, S₂.t₁ t ht],
    fun t ht => by rw [t₅ (j := 2) (by decide) t ht, S₂.t₂ t ht], f₅, px_lt, py_lt, px, py,
    whole_of (whole_of (whole_of S₂.whole U₃ (slW_le h7 (by decide))) U₄ hW4) U₅ hW5⟩

end VG.Proof.Ecdsa.Verify.Arm
