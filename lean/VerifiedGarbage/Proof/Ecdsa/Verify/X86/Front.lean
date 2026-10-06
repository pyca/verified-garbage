import VerifiedGarbage.Proof.Ecdh.X86.Validate
import VerifiedGarbage.Impl.Ecdsa.Verify.X86

/-!
# ECDSA verification on x86 (32-bit): the arguments and the key

As on AArch64 (`Proof/Ecdsa/Verify/AArch64/Front.lean`).

`front_ok`: the signature's setup and tables (`stage₁`, with
`Args.verify`), the load of `s` and ECDH's checks of the key
(`peer_ok` of argument 0, `validate_ok`) leave `r`, the hash and `s` in
their slots, `R = O`, the tables of `p - 2` and `n - 2`, the flag of the
key's validity as the code checks it (`KeyOk`), and the key's point, or `G`
if it is not valid, for ECDH's ladder (`Front`).
-/

namespace VG.Proof.Ecdsa.Verify.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Proof.Ecdh.X86
open VG.Impl.Ecdh.X86 (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)
open VG.Impl.Ecdsa.Verify.X86 (Args.verify)

variable {c : Cfg}

/-- The arguments: `public` (`1 + 2 len` bytes), `digest` (`len` bytes),
`sig` (`2 len` bytes) and `scratch`, readable and writable as the contract
says and apart from `scratch`. -/
structure VPre (c : Cfg) (s : State) (extra : List Region := []) : Prop where
  rd : s.rd = [⟨ptr s 0, 1 + 2 * c.C.len⟩, ⟨ptr s 1, c.C.len⟩, ⟨ptr s 2, 2 * c.C.len⟩, ⟨argAddr s 0, 16⟩] ++ extra
  wr : s.wr = [⟨ptr s 3, size⟩]
  pk_sc : Region.Disjoint ⟨ptr s 0, 1 + 2 * c.C.len⟩ ⟨ptr s 3, size⟩
  dg_sc : Region.Disjoint ⟨ptr s 1, c.C.len⟩ ⟨ptr s 3, size⟩
  sig_sc : Region.Disjoint ⟨ptr s 2, 2 * c.C.len⟩ ⟨ptr s 3, size⟩
  args_sc : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨ptr s 3, size⟩
  ret_sc : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨ptr s 3, size⟩
  pk_fit : (arg s 0).toNat + (1 + 2 * c.C.len) ≤ 2 ^ 32
  dg_fit : (arg s 1).toNat + c.C.len ≤ 2 ^ 32
  sig_fit : (arg s 2).toNat + 2 * c.C.len ≤ 2 ^ 32
  sc_fit : (arg s 3).toNat + size ≤ 2 ^ 32
  sp_fit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32

/-- The key's `x` and `y`, the hash's `e`, and the signature's `r` and `s`. -/
abbrev keyX (c : Cfg) (s₀ : State) : Nat :=
  ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 0 + BitVec.ofNat 64 1) c.C.len)
abbrev keyY (c : Cfg) (s₀ : State) : Nat :=
  ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 0 + BitVec.ofNat 64 (1 + c.C.len)) c.C.len)
abbrev dig (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 1) c.C.len) >>> c.sh
abbrev sigR (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 2) c.C.len)
abbrev sigS (c : Cfg) (s₀ : State) : Nat :=
  ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 2 + BitVec.ofNat 64 c.C.len) c.C.len)

/-- The key is valid as the code checks it. -/
abbrev KeyOk (c : Cfg) (s₀ : State) : Prop :=
  ((s₀.mem (ptr s₀ 0) = 4 ∧ keyX c s₀ < c.C.p) ∧ keyY c s₀ < c.C.p) ∧
    OnCurve c (Fin.ofNat c.C.p (keyX c s₀)) (Fin.ofNat c.C.p (keyY c s₀))

/-- After the key's checks, from the state `s₀` at entry, with the working
space at `base`. -/
structure Front (c : Cfg) (s₀ : State) (base : Addr) (s : State) : Prop where
  scr : Scr s base size
  wr : s.wr = s₀.wr
  rd : s.rd = s₀.rd
  esp : s.gpr .esp = s₀.gpr .esp
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
  /-- Memory outside the working space is unchanged. -/
  unch : Unch base [(0, size)] s₀.mem s.mem

theorem idx_verify {i : Nat} (hi : i ∈ Args.verify.idx) : i < 4 := by
  simp only [Args.idx, List.mem_cons, List.not_mem_nil, or_false] at hi
  omega

theorem VPre.setup {s : State} {extra : List Region} (hp : VPre c s extra) : SetupPre c Args.verify s where
  shift := .inr (.inl rfl)
  wr := by rw [hp.wr]; simp
  arg_in := fun i hi => ⟨_, by rw [hp.rd]; simp, arg_containsN (k := 4) (by have := hp.sp_fit; omega)
    (idx_verify hi)⟩
  arg_sc := fun i hi => hp.args_sc.sub_left (arg_subN (k := 4) (by have := hp.sp_fit; omega) (idx_verify hi))
  sp_fit := fun i hi => by have := idx_verify hi; have := hp.sp_fit; omega
  k_in := fun e he => ⟨⟨ptr s 2, 2 * c.C.len⟩, by rw [hp.rd]; simp,
    Offset.contains_base _ (by omega) (by have := hp.sig_fit; omega)⟩
  d_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.dg_fit; omega)
  e_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.dg_fit; omega)
  k_sc := hp.sig_sc.sub_left (Region.sub_prefix (by omega))
  d_sc := hp.dg_sc
  e_sc := hp.dg_sc
  k_fit := show (arg s 2).toNat + c.C.len ≤ 2 ^ 32 by have := hp.sig_fit; omega
  d_fit := hp.dg_fit
  e_fit := hp.dg_fit
  sc_fit := hp.sc_fit

/-- Ranges of the working space, as one. -/
theorem unch_whole {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (h : Unch base W m m')
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ size) : Unch base [(0, size)] m m' :=
  (h.outside fun w hw => ⟨Nat.zero_le _, by have := hW w hw; omega⟩).unch

theorem slW_le (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i < 45) : ∀ w ∈ slW c l, w.1 + w.2 ≤ size := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  exact sl_le c h7 (hl i hi)

theorem loadS_eq (c : Cfg) : Impl.Ecdsa.Verify.X86.Cfg.loadS c =
    .mov .ebx (.mem (Cfg.argOp 2)) :: .alu .add .ebx (.imm (BitVec.ofNat 32 c.C.len)) ::
      loadBytes c.C.len c.n (c.sl PT) .ebx := by
  simp only [Impl.Ecdsa.Verify.X86.Cfg.loadS, List.cons_append, List.nil_append]

/-- The setup and tables, `s`, and the checks of the key. -/
theorem front_ok (hc : CfgOk c) {s₀ : State} {extra : List Region} (hp : VPre c s₀ extra) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s, Front c s₀ (ptr s₀ 3) s → WP isa rest s Q) :
    WP isa (.seq (Impl.Ecdsa.Verify.X86.Cfg.prefix' c) (.seq (.block (Impl.Ecdsa.Verify.X86.Cfg.loadS c))
      (.seq (.block (Impl.Ecdh.X86.Cfg.peerAt c 0)) (.seq (Impl.Ecdh.X86.Cfg.validate c) rest)))) s₀ Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hsz : size = 8192 := rfl
  have hl8 := hc.len8
  have hlhi := hc.len_hi
  have h4 : (s₀.gpr .esp).toNat + 4 + 4 * 4 ≤ 2 ^ 32 := by have := hp.sp_fit; omega
  refine WP.seq (stage₁ hc hp.setup fun s₂ S₂ => WP.block_nil ?_)
  have hn := S₂.scr.nowrap
  have W₂ : Outside (ptr s₀ 3) 0 size s₀.mem s₂.mem :=
    S₂.whole.outside fun w hw => by rw [List.mem_singleton.mp hw]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  have hrw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [S₂.rd, S₂.wr]
  have hload : ∀ {i}, i < 4 → ∀ t : State, t.gpr .esp = s₂.gpr .esp → t.rd ++ t.wr = s₂.rd ++ s₂.wr →
      Outside (ptr s₀ 3) 0 size s₂.mem t.mem → readSrc t (.mem (Cfg.argOp i)) = some (arg s₀ i) :=
    fun hi t he hrw ho => argLoad_ok ⟨_, by rw [hp.rd]; simp, arg_containsN h4 hi⟩
      (hp.args_sc.sub_left (arg_subN h4 hi)) (he.trans S₂.esp) (hrw.trans hrw₂) (W₂.trans ho)
  -- `s`.
  have hPT := sl_le c h7 (i := PT) (by decide)
  rw [loadS_eq]
  refine WP.seq (wp_movS (hload (i := 2) (by decide) s₂ rfl rfl (VG.Proof.Mont.Outside.refl _ _ _ _))
    fun s₂' u₂ _ => ?_)
  refine wp_addS rfl fun s₂'' u₂' _ => ?_
  have k₂ : Keeps [.ebx] s₂ s₂'' := u₂.keeps.trans u₂'.keeps
  have hs₂ := S₂.scr.of_keeps k₂ (by decide)
  have hm₂ : s₂''.mem = s₂.mem := by rw [u₂'.mem, u₂.mem]
  have hb : s₂''.gpr .ebx = arg s₀ 2 + BitVec.ofNat 32 c.C.len := by rw [u₂'.gpr, u₂.gpr]
  have hb' : (s₂''.gpr .ebx).setWidth 64 = ptr s₀ 2 + BitVec.ofNat 64 c.C.len := by
    rw [hb]; exact addr_eq (by have := hp.sig_fit; omega)
  have hbt : (s₂''.gpr .ebx).toNat = (arg s₀ 2).toNat + c.C.len := by
    rw [hb, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c.C.len) (by omega)]
    exact Nat.mod_eq_of_lt (by have := hp.sig_fit; omega)
  have hrw₂' : s₂''.rd ++ s₂''.wr = s₀.rd ++ s₀.wr := by rw [k₂.2.1, k₂.2.2, hrw₂]
  refine WP.mono (loadBytes_ok hs₂ (src := .ebx) (by decide) hPT (by rw [hbt]; have := hp.sig_fit; omega)
    (by omega) hlhi (fun e he => ⟨⟨ptr s₀ 2, 2 * c.C.len⟩, by rw [hrw₂', hp.rd]; simp, by
      rw [hb', Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)⟩)
    (by
      rw [hb']
      exact (hp.sig_sc.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ hPT)))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [hb', hm₂] at e₃
  rw [hm₂] at O₃
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have K₃ : Keeps [.eax, .ebx] s₂ s₃ := (k₂.mono (by decide)).widen k₃
  have U₃ : Unch (ptr s₀ 3) (slW c [PT]) s₂.mem s₃.mem := O₃.unch
  have F₃ := S₂.fixed.unch h7 hn (fixedOk_slW (l := [PT]) (by decide)) U₃
  have v₃ : ∀ {i}, i < 45 → i ≠ PT → sv c (ptr s₀ 3) s₃ i = sv c (ptr s₀ 3) s₂ i := fun hi hl =>
    sv_unch U₃ h7 hn hi (apart_slW (by simpa using hl))
  have pt₃ : sv c (ptr s₀ 3) s₃ PT = sigS c s₀ := by
    rw [sv, e₃, bytesAt_keep W₂ (hp.sig_sc.sub_left (Offset.sub_base _ (by omega))) (by omega)
      (by omega)]
  have W₃ : Outside (ptr s₀ 3) 0 size s₂.mem s₃.mem := O₃.mono (Nat.zero_le _) (by omega)
  have hrw₃ : s₃.rd ++ s₃.wr = s₂.rd ++ s₂.wr := by rw [K₃.2.1, K₃.2.2]
  -- The key.
  refine WP.seq (WP.mono (peer_ok hc hs₃ (i := 0) (fun t he hrw ho => hload (by decide) t
      (he.trans (K₃.1 _ (by decide))) (hrw.trans hrw₃) (W₃.trans ho))
    hp.pk_fit (by rw [hrw₃, hrw₂, hp.rd]; simp) hp.pk_sc F₃.mp)
    fun s₄ ⟨hs₄, k₄, U₄, r2₄, bp₄, x₄, y₄, f₄⟩ => ?_)
  have F₄ := F₃.unch h7 hn ((fixedOk_slW (l := [R2P, BP, E, QY]) (by decide)).append fixedOk_flag) U₄
  have e₄ : ∀ {i}, i < 45 → i ∉ [R2P, BP, E, QY] → i ≠ FLAG →
      sv c (ptr s₀ 3) s₄ i = sv c (ptr s₀ 3) s₃ i := fun hi hl hf =>
    sv_unch U₄ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  have W₃' : Outside (ptr s₀ 3) 0 size s₀.mem s₃.mem := W₂.trans W₃
  have x₄' : sv c (ptr s₀ 3) s₄ E = keyX c s₀ := by
    rw [x₄, bytesAt_keep W₃' (hp.pk_sc.sub_left (Offset.sub_base _ (by omega))) (by omega) (by omega)]
  have y₄' : sv c (ptr s₀ 3) s₄ QY = keyY c s₀ := by
    rw [y₄, bytesAt_keep W₃' (hp.pk_sc.sub_left (Offset.sub_base _ (by omega))) (by omega) (by omega)]
  have hq0 : s₃.mem (ptr s₀ 0) = s₀.mem (ptr s₀ 0) := by
    have := keep_of_disjoint' W₃' hp.pk_sc (by omega) (i := 0) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  have hf₄ : flagW c (ptr s₀ 3) s₄ = mask32 (((s₀.mem (ptr s₀ 0) = 4 ∧
      sv c (ptr s₀ 3) s₄ E < c.C.p) ∧ sv c (ptr s₀ 3) s₄ QY < c.C.p)) := by
    rw [f₄, flagW, flag_unch (U₃.mono fun w hw => List.mem_append_left _ hw) h7 h0 hn (l := [PT])
      (by decide), ← flagW, S₂.flag, BitVec.allOnes_and, mask32_and, mask32_and]
    simp only [hq0]
  refine WP.seq (WP.mono (validate_ok hc hs₄ F₄ r2₄ bp₄ hf₄)
    fun s₅ ⟨hs₅, g₅, rd₅, wr₅, U₅, f₅, px_lt, py_lt, px, py⟩ => h s₅ ?_)
  have F₅ := F₄.unch h7 hn ((fixedOk_slWk (l := [QXM, QYM, TMP, W0, W1, W2, W3, PY]) (by decide)).append
    fixedOk_flag) U₅
  have e₅ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, TMP, W0, W1, W2, W3, PY] → i ≠ FLAG →
      sv c (ptr s₀ 3) s₅ i = sv c (ptr s₀ 3) s₄ i := fun hi hl hf =>
    sv_unch U₅ h7 hn hi (apart_append (apart_slWk hi hl) (apart_flag h0 hf))
  have a₅ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, TMP, W0, W1, W2, W3, PY] → i ∉ [R2P, BP, E, QY] → i ≠ FLAG →
      i ≠ PT → sv c (ptr s₀ 3) s₅ i = sv c (ptr s₀ 3) s₂ i := fun hi h₁ h₂ hf hp =>
    ((e₅ hi h₁ hf).trans (e₄ hi h₂ hf)).trans (v₃ hi hp)
  have t₅ : ∀ {j}, j < 3 → ∀ t < 64 * c.n,
      s₅.mem (off (ptr s₀ 3) (bitsAt c.n j + t)) = s₂.mem (off (ptr s₀ 3) (bitsAt c.n j + t)) :=
    fun hj t ht => by
      rw [tbl_unch U₅ h7 hj ht (apart_append (tbl_apart_slWk (by decide) hj ht) (tbl_apart_flag h0 _ t)),
        tbl_unch U₄ h7 hj ht (apart_append (tbl_apart_slW (by decide) _ t) (tbl_apart_flag h0 _ t)),
        tbl_unch U₃ h7 hj ht (tbl_apart_slW (by decide) _ t)]
  have hok : PeerOk c (ptr s₀ 3) s₄ ((s₀.mem (ptr s₀ 0) = 4 ∧ sv c (ptr s₀ 3) s₄ E < c.C.p) ∧
      sv c (ptr s₀ 3) s₄ QY < c.C.p) = KeyOk c s₀ := by
    rw [PeerOk, x₄', y₄']
  simp only [hok] at f₅ px py
  rw [x₄'] at px
  rw [y₄'] at py
  have hW4 : ∀ w ∈ slW c [R2P, BP, E, QY] ++ [(c.sl FLAG, 4)], w.1 + w.2 ≤ size :=
    le_append (slW_le h7 (by decide)) (flag_le h0 h7)
  have hW5 : ∀ w ∈ slWk c [QXM, QYM, TMP, W0, W1, W2, W3, PY] ++ [(c.sl FLAG, 4)], w.1 + w.2 ≤ size :=
    le_append (slWk_le h7 (by decide)) (flag_le h0 h7)
  refine ⟨hs₅, by rw [wr₅, k₄.2.2, K₃.2.2, S₂.wr], by rw [rd₅, k₄.2.1, K₃.2.1, S₂.rd],
    by rw [g₅ _ (by decide), k₄.1 _ (by decide), K₃.1 _ (by decide), S₂.esp], F₅,
    by rw [a₅ (i := K) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.k, kv_eq (A := Args.verify) rfl],
    by rw [a₅ (i := D) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.d]
       show _ >>> shAt c (some D) D = _; rw [shAt_self],
    by rw [e₅ (i := PT) (by decide) (by decide) (by decide), e₄ (by decide) (by decide) (by decide), pt₃],
    by rw [a₅ (i := RX) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.rx],
    by rw [a₅ (i := RY) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.ry],
    by rw [a₅ (i := RZ) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.rz],
    fun t ht => by rw [t₅ (j := 1) (by decide) t ht, S₂.t₁ t ht],
    fun t ht => by rw [t₅ (j := 2) (by decide) t ht, S₂.t₂ t ht], f₅, px_lt, py_lt, px, py,
    whole_of (whole_of (whole_of S₂.whole U₃ (slW_le h7 (by decide))) U₄ hW4) U₅ hW5⟩

end VG.Proof.Ecdsa.Verify.X86
