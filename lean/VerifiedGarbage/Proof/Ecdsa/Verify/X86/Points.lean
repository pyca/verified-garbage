module

import VerifiedGarbage.Proof.Ecdh.X86.Peer
import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
import VerifiedGarbage.Proof.Weierstrass.X86.Bits
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Ecdsa.X86.Main
public import VerifiedGarbage.Proof.Ecdsa.X86.Stages
import VerifiedGarbage.Proof.Ecdsa.X86.Inv
import VerifiedGarbage.Proof.Ecdsa.X86.Scalar
import VerifiedGarbage.Proof.Ecdsa.X86.Middle
public import VerifiedGarbage.Proof.Ecdh.X86.Validate
public import VerifiedGarbage.Impl.Ecdsa.Verify.X86
import VerifiedGarbage.Proof.Ecdsa.X86.Finish
import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
import VerifiedGarbage.Proof.Ecdsa.X86.Setup
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Ecdsa.Verify.X86.Front`, which this module and modules that import it used -/

section

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

@[expose] public section

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
  sp_lo : c.stk ≤ (s.gpr .esp).toNat
  stk_sc : (stkR c s).Disjoint ⟨ptr s 3, size⟩

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
  /-- Memory changed only in the working space and the stack the calls use. -/
  whole : Frame (s₀.wr ++ [below (s₀.gpr .esp) c.stk]) s₀.mem s.mem
  sp_lo : c.stk ≤ (s₀.gpr .esp).toNat

theorem Front.keep {s₀ : State} {base : Addr} {s : State} (h : Front c s₀ base s) : Keep c s₀ base s :=
  ⟨h.scr, h.esp, h.rd, h.wr, h.fixed, h.whole, h.sp_lo⟩

theorem idx_verify {i : Nat} (hi : i ∈ Args.verify.idx) : i < 4 := by
  simp only [Args.idx, List.mem_cons, List.not_mem_nil, or_false] at hi
  omega_arith

theorem VPre.setup {s : State} {extra : List Region} (hp : VPre c s extra) : SetupPre c Args.verify s where
  shift := .inr (.inl rfl)
  wr := by rw [hp.wr]; simp
  arg_in := fun i hi => ⟨_, by rw [hp.rd]; simp, arg_containsN (k := 4) (by have := hp.sp_fit; omega_arith)
    (idx_verify hi)⟩
  arg_sc := fun i hi => hp.args_sc.sub_left (arg_subN (k := 4) (by have := hp.sp_fit; omega_arith) (idx_verify hi))
  sp_fit := fun i hi => by have := idx_verify hi; have := hp.sp_fit; omega_arith
  k_in := fun e he => ⟨⟨ptr s 2, 2 * c.C.len⟩, by rw [hp.rd]; simp,
    Offset.contains_base _ (by omega_arith) (by have := hp.sig_fit; omega_arith)⟩
  d_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.dg_fit; omega_arith)
  e_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.dg_fit; omega_arith)
  k_sc := hp.sig_sc.sub_left (Region.sub_prefix (by omega_arith))
  d_sc := hp.dg_sc
  e_sc := hp.dg_sc
  k_fit := show (arg s 2).toNat + c.C.len ≤ 2 ^ 32 by have := hp.sig_fit; omega_arith
  d_fit := hp.dg_fit
  e_fit := hp.dg_fit
  sc_fit := hp.sc_fit
  stk := stkOk_of (Cfg.stk_ge c) hp.sp_lo
    (by rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := hp.sc_fit; omega_arith)]; exact hp.sc_fit)
    (by decide) hp.stk_sc
  sp_lo := hp.sp_lo
  stk_sc := hp.stk_sc

/-- The slot of an argument is apart from what the code writes. -/
theorem vArgs_disjI {s : State} {extra : List Region} (hp : VPre c s extra) {i : Nat} (hi : i < 4) :
    ∀ r ∈ s.wr ++ [below (s.gpr .esp) c.stk], Region.Disjoint ⟨argAddr s i, 4⟩ r := by
  obtain h4 : (s.gpr .esp).toNat + 4 + 4 * 4 ≤ 2 ^ 32 := by have := hp.sp_fit; omega_using [this]
  rw [hp.wr]
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hp.args_sc.sub_left (arg_subN h4 hi)
  · exact (below_disjoint_args hp.sp_lo (k := 16) (by omega_using [h4]) (by decide)).symm.sub_left (arg_subN h4 hi)

theorem loadS_eq (c : Cfg) : Impl.Ecdsa.Verify.X86.Cfg.loadS c =
    .mov .ebx (.mem (Cfg.argOp 2)) :: .alu .add .ebx (.imm (BitVec.ofNat 32 c.C.len)) ::
      loadBytes c.C.len c.n (c.sl PT) .ebx := by
  simp only [Impl.Ecdsa.Verify.X86.Cfg.loadS, List.cons_append, List.nil_append]

/-- The setup and tables, `s`, and the checks of the key. -/
theorem front_ok (hc : CfgOk c) {s₀ : State} {extra : List Region} (hp : VPre c s₀ extra)
    (hsp : SpOk (Impl.Ecdh.X86.Cfg.validate c) c.stk) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s, Front c s₀ (ptr s₀ 3) s → WP isa rest s Q) :
    WP isa (.seq (Impl.Ecdsa.Verify.X86.Cfg.prefix' c) (.seq (.block (Impl.Ecdsa.Verify.X86.Cfg.loadS c))
      (.seq (.block (Impl.Ecdh.X86.Cfg.peerAt c 0)) (.seq (Impl.Ecdh.X86.Cfg.validate c) rest)))) s₀ Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hsz : size = 8192 := rfl
  have hl8 := hc.len8
  have hlhi := hc.len_hi
  obtain h4 : (s₀.gpr .esp).toNat + 4 + 4 * 4 ≤ 2 ^ 32 := by have := hp.sp_fit; omega_arith
  refine WP.seq (stage₁ hc hp.setup fun s₂ S₂ => WP.block_nil ?_)
  have hn := S₂.scr.nowrap
  have W₂ : Outside (ptr s₀ 3) 0 size s₀.mem s₂.mem := S₂.ws
  obtain hrw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [S₂.rd, S₂.wr]
  obtain hload : ∀ {i}, i < 4 → ∀ t : State, t.gpr .esp = s₂.gpr .esp → t.rd ++ t.wr = s₂.rd ++ s₂.wr →
      Outside (ptr s₀ 3) 0 size s₂.mem t.mem → readSrc t (.mem (Cfg.argOp i)) = some (arg s₀ i) :=
    fun hi t he hrw ho => argLoad_ok ⟨_, by rw [hp.rd]; simp, arg_containsN h4 hi⟩
      (hp.args_sc.sub_left (arg_subN h4 hi)) (he.trans S₂.esp) (hrw.trans hrw₂) (W₂.trans ho)
  -- `s`.
  obtain hPT := sl_le c h7 (i := PT) (by decide)
  rw [loadS_eq]
  refine WP.seq (wp_movS (hload (i := 2) (by decide) s₂ rfl rfl (VG.Proof.Mont.Outside.refl _ _ _ _))
    fun s₂' u₂ _ => ?_)
  refine wp_addS rfl fun s₂'' u₂' _ => ?_
  obtain k₂ : Keeps [.ebx] s₂ s₂'' := u₂.keeps.trans u₂'.keeps
  obtain hs₂ := S₂.scr.of_keeps k₂ (by decide)
  obtain hm₂ : s₂''.mem = s₂.mem := by rw [u₂'.mem, u₂.mem]
  obtain hb : s₂''.gpr .ebx = arg s₀ 2 + BitVec.ofNat 32 c.C.len := by rw [u₂'.gpr, u₂.gpr]
  obtain hb' : (s₂''.gpr .ebx).setWidth 64 = ptr s₀ 2 + BitVec.ofNat 64 c.C.len := by
    rw [hb]; exact addr_eq (by have := hp.sig_fit; omega_arith)
  obtain hbt : (s₂''.gpr .ebx).toNat = (arg s₀ 2).toNat + c.C.len := by
    rw [hb, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c.C.len) (by omega_arith)]
    exact Nat.mod_eq_of_lt (by have := hp.sig_fit; omega_arith)
  obtain hrw₂' : s₂''.rd ++ s₂''.wr = s₀.rd ++ s₀.wr := by rw [k₂.2.1, k₂.2.2, hrw₂]
  refine WP.mono (loadBytes_ok hs₂ (src := .ebx) (by decide) hPT (by rw [hbt]; have := hp.sig_fit; omega_arith)
    (by omega_arith) hlhi (fun e he => ⟨⟨ptr s₀ 2, 2 * c.C.len⟩, by rw [hrw₂', hp.rd]; simp, by
      rw [hb', Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (by
      rw [hb']
      exact (hp.sig_sc.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ hPT)))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [hb', hm₂] at e₃
  rw [hm₂] at O₃
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  obtain K₃ : Keeps [.eax, .ebx] s₂ s₃ := (k₂.mono (by decide)).widen k₃
  have U₃ : Unch (ptr s₀ 3) (slW c [PT]) s₂.mem s₃.mem := O₃.unch
  obtain F₃ := S₂.fixed.unch h7 hn (fixedOk_slW (l := [PT]) (by decide)) U₃
  obtain v₃ : ∀ {i}, i < 45 → i ≠ PT → sv c (ptr s₀ 3) s₃ i = sv c (ptr s₀ 3) s₂ i := fun hi hl =>
    sv_unch U₃ h7 hn hi (apart_slW (by simpa using hl))
  obtain pt₃ : sv c (ptr s₀ 3) s₃ PT = sigS c s₀ := by
    rw [sv, e₃, bytesAt_keep W₂ (hp.sig_sc.sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith)
      (by omega_arith)]
  obtain W₃ : Outside (ptr s₀ 3) 0 size s₂.mem s₃.mem := O₃.mono (Nat.zero_le _) (by omega_arith)
  obtain hrw₃ : s₃.rd ++ s₃.wr = s₂.rd ++ s₂.wr := by rw [K₃.2.1, K₃.2.2]
  -- The key.
  refine WP.seq (WP.mono (peer_ok hc hs₃ (i := 0) (fun t he hrw ho => hload (by decide) t
      (he.trans (K₃.1 _ (by decide))) (hrw.trans hrw₃) (W₃.trans ho))
    hp.pk_fit (by rw [hrw₃, hrw₂, hp.rd]; simp) hp.pk_sc F₃.mp)
    fun s₄ ⟨hs₄, k₄, U₄, r2₄, bp₄, x₄, y₄, f₄⟩ => ?_)
  obtain F₄ := F₃.unch h7 hn ((fixedOk_slW (l := [R2P, BP, E, QY]) (by decide)).append fixedOk_flag) U₄
  obtain e₄ : ∀ {i}, i < 45 → i ∉ [R2P, BP, E, QY] → i ≠ FLAG →
      sv c (ptr s₀ 3) s₄ i = sv c (ptr s₀ 3) s₃ i := fun hi hl hf =>
    sv_unch U₄ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  obtain W₃' : Outside (ptr s₀ 3) 0 size s₀.mem s₃.mem := W₂.trans W₃
  obtain x₄' : sv c (ptr s₀ 3) s₄ E = keyX c s₀ := by
    rw [x₄, bytesAt_keep W₃' (hp.pk_sc.sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith) (by omega_arith)]
  obtain y₄' : sv c (ptr s₀ 3) s₄ QY = keyY c s₀ := by
    rw [y₄, bytesAt_keep W₃' (hp.pk_sc.sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith) (by omega_arith)]
  obtain hq0 : s₃.mem (ptr s₀ 0) = s₀.mem (ptr s₀ 0) := by
    have := keep_of_disjoint' W₃' hp.pk_sc (by omega_arith) (i := 0) (by omega_arith) (by omega_arith)
    rwa [BitVec.add_zero] at this
  obtain hf₄ : flagW c (ptr s₀ 3) s₄ = mask32 (((s₀.mem (ptr s₀ 0) = 4 ∧
      sv c (ptr s₀ 3) s₄ E < c.C.p) ∧ sv c (ptr s₀ 3) s₄ QY < c.C.p)) := by
    rw [f₄, flagW, flag_unch (U₃.mono fun w hw => List.mem_append_left _ hw) h7 h0 hn (l := [PT])
      (by decide), ← flagW, S₂.flag, BitVec.allOnes_and, mask32_and, mask32_and]
    simp only [hq0]
  obtain hsc : (⟨ptr s₀ 3, size⟩ : Region) ∈ s₀.wr ++ [below (s₀.gpr .esp) c.stk] :=
    List.mem_append_left _ (by rw [hp.wr]; simp)
  obtain hW4 : ∀ w ∈ slW c [R2P, BP, E, QY] ++ [(c.sl FLAG, 4)], w.1 + w.2 ≤ size :=
    le_append (slW_le h7 (by decide)) (flag_le h0 h7)
  obtain K₄ : Keep c s₀ (ptr s₀ 3) s₄ := ⟨hs₄, by rw [k₄.1 _ (by decide), K₃.1 _ (by decide), S₂.esp],
    by rw [k₄.2.1, K₃.2.1, S₂.rd], by rw [k₄.2.2, K₃.2.2, S₂.wr], F₄,
    (S₂.whole.trans (frame_of_unch U₃ (slW_le h7 (by decide)) hsc)).trans (frame_of_unch U₄ hW4 hsc),
    S₂.sp_lo⟩
  refine WP.seq (K₄.withSp hsp (WP.mono (validate_ok hc hs₄ F₄ r2₄ bp₄ hf₄)
    fun s₅ ⟨hs₅, g₅, rd₅, wr₅, U₅, f₅, px_lt, py_lt, px, py⟩ w₅ => h s₅ ?_))
  obtain F₅ := F₄.unch h7 hn ((fixedOk_slWk (l := [QXM, QYM, TMP, W0, W1, W2, W3, PY]) (by decide)).append
    fixedOk_flag) U₅
  obtain e₅ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, TMP, W0, W1, W2, W3, PY] → i ≠ FLAG →
      sv c (ptr s₀ 3) s₅ i = sv c (ptr s₀ 3) s₄ i := fun hi hl hf =>
    sv_unch U₅ h7 hn hi (apart_append (apart_slWk hi hl) (apart_flag h0 hf))
  obtain a₅ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, TMP, W0, W1, W2, W3, PY] → i ∉ [R2P, BP, E, QY] → i ≠ FLAG →
      i ≠ PT → sv c (ptr s₀ 3) s₅ i = sv c (ptr s₀ 3) s₂ i := fun hi h₁ h₂ hf hp =>
    ((e₅ hi h₁ hf).trans (e₄ hi h₂ hf)).trans (v₃ hi hp)
  obtain t₅ : ∀ {j}, j < 3 → ∀ t < 64 * c.n,
      s₅.mem (off (ptr s₀ 3) (bitsAt c.n j + t)) = s₂.mem (off (ptr s₀ 3) (bitsAt c.n j + t)) :=
    fun hj t ht => by
      rw [tbl_unch U₅ h7 hj ht (apart_append (tbl_apart_slWk (by decide) hj ht) (tbl_apart_flag h0 _ t)),
        tbl_unch U₄ h7 hj ht (apart_append (tbl_apart_slW (by decide) _ t) (tbl_apart_flag h0 _ t)),
        tbl_unch U₃ h7 hj ht (tbl_apart_slW (by decide) _ t)]
  obtain hok : PeerOk c (ptr s₀ 3) s₄ ((s₀.mem (ptr s₀ 0) = 4 ∧ sv c (ptr s₀ 3) s₄ E < c.C.p) ∧
      sv c (ptr s₀ 3) s₄ QY < c.C.p) = KeyOk c s₀ := by
    rw [PeerOk, x₄', y₄']
  simp only [hok] at f₅ px py
  rw [x₄'] at px
  rw [y₄'] at py
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
    fun t ht => by rw [t₅ (j := 2) (by decide) t ht, S₂.t₂ t ht], f₅, px_lt, py_lt, px, py, w₅, S₂.sp_lo⟩

end VG.Proof.Ecdsa.Verify.X86

end

end

/-! ### `Ecdsa.Verify.X86.Scalars`, which this module and modules that import it used -/

section

/-!
# ECDSA verification on x86 (32-bit): `u` and `v`

As on AArch64 (`Proof/Ecdsa/Verify/AArch64/Scalars.lean`).

`mid_ok`: from what `front_ok` leaves, `scalars` ands the masks of `r` and
`s` in `[1, n-1]` into the flag and computes `s R mod n`, the signature's
power modulo `n` gives `w = s^(n-2)` (in Montgomery form), and `uv` computes
`r R mod n` (`RM'`) and `u = e w` and `v = r w` modulo `n`, out of
Montgomery's form (`U`, `V`), with the multiplications of `Proof/Mont`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Proof.Ecdh.X86
open VG.Impl.Ecdh.X86 (PX PY)
open VG.Impl.Ecdsa.Verify.X86 (SM' EM' RM' UM VM U V)

variable {c : Cfg}

/-- The slots `mid_ok` writes. -/
abbrev midW : List Nat := [SM', TMP, ACC, PT, EM', RM', UM, VM, U, V]

/-- After `u` and `v`. -/
structure Mid (c : Cfg) (s₀ : State) (base : Addr) (s : State) : Prop where
  scr : Scr s base size
  wr : s.wr = s₀.wr
  rd : s.rd = s₀.rd
  esp : s.gpr .esp = s₀.gpr .esp
  fixed : Fixed c base s₀.gpr s.mem
  rx : sv c base s RX = 0
  ry : sv c base s RY = c.mont 1
  rz : sv c base s RZ = 0
  t₁ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0
  flag : flagW c base s =
    mask32 (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n))
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
  whole : Frame (s₀.wr ++ [below (s₀.gpr .esp) c.stk]) s₀.mem s.mem
  sp_lo : c.stk ≤ (s₀.gpr .esp).toNat
  k : sv c base s K = sigR c s₀

theorem Mid.keep {s₀ : State} {base : Addr} {s : State} (h : Mid c s₀ base s) : Keep c s₀ base s :=
  ⟨h.scr, h.esp, h.rd, h.wr, h.fixed, h.whole, h.sp_lo⟩

theorem scalars_eq (c : Cfg) : Impl.Ecdsa.Verify.X86.Cfg.scalars c =
    .seq (.block (c.checkRange (c.sl K) ++ c.checkRange (c.sl PT)))
      (Mont.mulCall c.SN (c.sl SM') (c.sl PT) (c.sl R2N)) := rfl

theorem uv_eq (c : Cfg) : Impl.Ecdsa.Verify.X86.Cfg.uv c =
    .seq (Mont.mulCall c.SN (c.sl EM') (c.sl D) (c.sl R2N))
    (.seq (Mont.mulCall c.SN (c.sl RM') (c.sl K) (c.sl R2N))
    (.seq (Mont.mulCall c.SN (c.sl UM) (c.sl EM') (c.sl ACC))
    (.seq (Mont.mulCall c.SN (c.sl VM) (c.sl RM') (c.sl ACC))
    (.seq (Mont.mulCall c.SN (c.sl U) (c.sl UM) (c.sl ONE))
      (Mont.mulCall c.SN (c.sl V) (c.sl VM) (c.sl ONE)))))) := rfl

/-- One multiplication modulo `n`, on numbered slots: it keeps the modulus and
every other slot but the temporary area's. -/
theorem mulN_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hMN : ModOkW c.MN' size c.C.n s.mem base) {o a b : Nat} (ho : o < 45) (ha : a < 45) (hb : b < 45)
    (hB : sv c base s b < c.C.n) (hoN : o ≠ MN) :
    WP isa (Mont.mulCall c.SN (c.sl o) (c.sl a) (c.sl b)) s fun s' =>
      Scr s' base size ∧ ModOkW c.MN' size c.C.n s'.mem base ∧
      (∀ r, r ∉ clob → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Unch base (slWk c [o, TMP]) s.mem s'.mem ∧
      (∀ {i}, i < 45 → i ≠ o → i ≠ TMP → sv c base s' i = sv c base s i) ∧
      sv c base s' o < c.C.n ∧
      sv c base s' o * 2 ^ (64 * c.n) % c.C.n = sv c base s a * sv c base s b % c.C.n := by
  have h7 := hc.n10
  have hn := hs.nowrap
  exact WP.mono (slMul_ok (MN'_n c) hc.fn h7 hs ho ha hb hB) fun s' ⟨k, lt, e⟩ =>
    ⟨k.scr hs, hMN.keepX86 (j := MN) (by decide) rfl rfl rfl rfl h7 hn k (Ne.symm hoN) (by decide),
      k.gpr, k.rd, k.wr, unch_slots (MN'_n c) rfl k.unch (l := [o, TMP]) (by simp) (by simp),
      fun hi h₁ h₂ => sv_keep (MN'_n c) rfl h7 hn k hi h₁ h₂, lt, e⟩

/-- The checks of `r` and `s`, `w = s^(n-2)`, `u` and `v`. -/
theorem mid_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State}
    (hF : Front c s₀ base s) (hsp₁ : SpOk (Impl.Ecdsa.Verify.X86.Cfg.scalars c) c.stk)
    (hsp₂ : SpOk c.nPow c.stk) (hsp₃ : SpOk (Impl.Ecdsa.Verify.X86.Cfg.uv c) c.stk)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', Mid c s₀ base s' → WP isa rest s' Q) :
    WP isa (.seq (Impl.Ecdsa.Verify.X86.Cfg.scalars c) (.seq c.nPow
      (.seq (Impl.Ecdsa.Verify.X86.Cfg.uv c) rest))) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hF.scr.nowrap
  obtain hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have hn3 := hc.n_ge
  have F := hF.fixed
  obtain hf : c.sl FLAG + 4 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  obtain hr2lt : ∀ {m : Mem}, wordsVal m base (c.sl R2N) c.n = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n →
      wordsVal m base (c.sl R2N) c.n < c.C.n := fun h => by rw [h]; exact Nat.mod_lt _ (by omega_arith)
  refine WP.seq (hF.keep.withSp hsp₁ ?_)
  rw [scalars_eq]
  -- The checks.
  refine WP.seq ?_
  refine WP.block_append (WP.mono (checkRange_ok c hF.scr h0 (sl_le c h7 (i := K) (by decide))
    (sl_le c h7 (i := MN) (by decide)) hf) fun s₁ ⟨f₁, k₁, O₁⟩ => ?_)
  obtain hs₁ := hF.scr.of_keeps k₁ (by decide)
  obtain v₁ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₁ i = sv c base s i := fun hi hf =>
    sv_flag O₁ h0 h7 hn hi hf
  refine WP.mono (checkRange_ok c hs₁ h0 (sl_le c h7 (i := PT) (by decide)) (sl_le c h7 (i := MN) (by decide))
    hf) fun s₂ ⟨f₂, k₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  obtain K₂ := k₁.trans k₂
  obtain v₂ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₂ i = sv c base s i := fun hi hf =>
    (sv_flag O₂ h0 h7 hn hi hf).trans (v₁ hi hf)
  obtain U₂ : Unch base [(c.sl FLAG, 4)] s.mem s₂.mem := by
    have := O₁.unch.trans O₂.unch
    exact this.mono fun w hw => by simpa using hw
  obtain F₂ := F.unch h7 hn fixedOk_flag U₂
  obtain flag₂ : flagW c base s₂ =
      mask32 (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) := by
    have hk : wordsVal s.mem base (c.sl K) c.n = sigR c s₀ := hF.k
    have hmn : wordsVal s.mem base (c.sl MN) c.n = c.C.n := F.mn
    obtain hpt₁ : wordsVal s₁.mem base (c.sl PT) c.n = sigS c s₀ := (v₁ (by decide) (by decide)).trans hF.pt
    obtain hmn₁ : wordsVal s₁.mem base (c.sl MN) c.n = c.C.n := (v₁ (by decide) (by decide)).trans F.mn
    rw [f₂, f₁, hF.flag, mask32_and, mask32_and, hmn₁, hmn, hk, hpt₁]
    simp only [and_assoc]
  -- `s R mod n`.
  refine WP.mono (mulN_ok hc hs₂ (modN_of hc F₂.mn) (o := SM') (a := PT) (b := R2N) (by decide) (by decide)
    (by decide) (hr2lt F₂.r2n) (by decide)) fun s₃ ⟨hs₃, M₃, g₃, rd₃, wr₃, U₃, v₃, lt₃, e₃⟩ f₃ => ?_
  obtain F₃ := F₂.unch h7 hn (fixedOk_slWk (by decide)) U₃
  obtain K₃ : Keep c s₀ base s₃ := ⟨hs₃, by rw [g₃ _ (by decide), K₂.1 _ (by decide), hF.esp],
    by rw [rd₃, K₂.2.1, hF.rd], by rw [wr₃, K₂.2.2, hF.wr], F₃, f₃, hF.sp_lo⟩
  obtain sm₃ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₃ SM') = Fin.ofNat c.C.n (sigS c s₀) := by
    rw [toM_r2 hnR (by rw [e₃, show sv c base s₂ R2N = _ from F₂.r2n]), v₂ (by decide) (by decide), hF.pt]
  -- `w = s^(n-2)`.
  refine WP.seq (K₃.withSp hsp₂ (WP.mono (nPow_ok hc hs₃ M₃ lt₃
    F₃.onen (fun t ht => by
      show s₃.mem (off base (bitsAt c.n 2 + t)) = _
      rw [tbl_unch U₃ h7 (j := 2) (by decide) ht (tbl_apart_slWk (by decide) (by decide) ht),
        tbl_unch U₂ h7 (j := 2) (by decide) ht (tbl_apart_flag h0 2 t)]
      exact hF.t₂ t ht)
    (show c.C.n - 2 < 2 ^ (64 * c.n) by have := hc.n_lt; omega_arith)) fun s₄ ⟨K₄, U₄, lt₄, v₄⟩ f₄ => ?_))
  obtain hs₄ := hs₃.of_keeps K₄ (by decide)
  obtain F₄ := F₃.unch h7 hn fixedOk_pwW U₄
  obtain KK₄ : Keep c s₀ base s₄ := ⟨hs₄, by rw [K₄.1 _ (by decide), K₃.esp], by rw [K₄.2.1, K₃.rd],
    by rw [K₄.2.2, K₃.wr], F₄, f₄, hF.sp_lo⟩
  obtain e₄ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₄ i = sv c base s₃ i := fun hi hl =>
    sv_unch U₄ h7 hn hi (apart_pwW hi hl)
  obtain w₄ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₄ ACC) = Fin.ofNat c.C.n (sigS c s₀) ^ (c.C.n - 2) := by
    rw [← sm₃]; exact v₄
  -- `u` and `v`.
  refine WP.seq (KK₄.withSp hsp₃ ?_)
  rw [uv_eq]
  refine WP.seq (WP.mono (mulN_ok hc hs₄ (modN_of hc F₄.mn) (o := EM') (a := D) (b := R2N) (by decide)
    (by decide) (by decide) (hr2lt F₄.r2n) (by decide))
    fun s₅ ⟨hs₅, M₅, g₅, rd₅, wr₅, U₅, v₅, lt₅, e₅⟩ => ?_)
  obtain F₅ := F₄.unch h7 hn (fixedOk_slWk (by decide)) U₅
  refine WP.seq (WP.mono (mulN_ok hc hs₅ M₅ (o := RM') (a := K) (b := R2N) (by decide)
    (by decide) (by decide) (hr2lt F₅.r2n) (by decide))
    fun s₆ ⟨hs₆, M₆, g₆, rd₆, wr₆, U₆, v₆, lt₆, e₆⟩ => ?_)
  obtain F₆ := F₅.unch h7 hn (fixedOk_slWk (by decide)) U₆
  obtain acc₆ : sv c base s₆ ACC = sv c base s₄ ACC := by
    rw [v₆ (by decide) (by decide) (by decide), v₅ (by decide) (by decide) (by decide)]
  refine WP.seq (WP.mono (mulN_ok hc hs₆ M₆ (o := UM) (a := EM') (b := ACC) (by decide)
    (by decide) (by decide) (acc₆ ▸ lt₄) (by decide))
    fun s₇ ⟨hs₇, M₇, g₇, rd₇, wr₇, U₇, v₇, lt₇, e₇⟩ => ?_)
  obtain F₇ := F₆.unch h7 hn (fixedOk_slWk (by decide)) U₇
  obtain acc₇ : sv c base s₇ ACC = sv c base s₄ ACC := by
    rw [v₇ (by decide) (by decide) (by decide), acc₆]
  refine WP.seq (WP.mono (mulN_ok hc hs₇ M₇ (o := VM) (a := RM') (b := ACC) (by decide)
    (by decide) (by decide) (acc₇ ▸ lt₄) (by decide))
    fun s₈ ⟨hs₈, M₈, g₈, rd₈, wr₈, U₈, v₈, lt₈, e₈⟩ => ?_)
  obtain F₈ := F₇.unch h7 hn (fixedOk_slWk (by decide)) U₈
  refine WP.seq (WP.mono (mulN_ok hc hs₈ M₈ (o := U) (a := UM) (b := ONE) (by decide)
    (by decide) (by decide) (by rw [show sv c base s₈ ONE = 1 from F₈.one]; omega_arith) (by decide))
    fun s₉ ⟨hs₉, M₉, g₉, rd₉, wr₉, U₉, v₉, lt₉, e₉⟩ => ?_)
  obtain F₉ := F₈.unch h7 hn (fixedOk_slWk (by decide)) U₉
  refine WP.mono (mulN_ok hc hs₉ M₉ (o := V) (a := VM) (b := ONE) (by decide)
    (by decide) (by decide) (by rw [show sv c base s₉ ONE = 1 from F₉.one]; omega_arith) (by decide))
    fun s₁₀ ⟨hs₁₀, M₁₀, g₁₀, rd₁₀, wr₁₀, U₁₀, v₁₀, lt₁₀, e₁₀⟩ f₁₀ => h s₁₀ ?_
  obtain F₁₀ := F₉.unch h7 hn (fixedOk_slWk (by decide)) U₁₀
  -- What changed: the flag and `midW`, and the accumulator.
  obtain cv : ∀ {l : List Nat}, (∀ i ∈ l, i ∈ midW) →
      ∀ w ∈ slWk c l, ∃ w' ∈ pwW c midW, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := fun hl w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact ⟨(c.sl i, 8 * c.n), List.mem_append_left _ (List.mem_map_of_mem (hl i hi)),
        Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨w, List.mem_append_right _ (List.mem_cons_of_mem _ hw), Nat.le_refl _, Nat.le_refl _⟩
  obtain cv4 : ∀ w ∈ pwW c, ∃ w' ∈ pwW c midW, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      obtain hl : ∀ i ∈ [ACC, PT, TMP], i ∈ midW := by decide
      exact ⟨(c.sl i, 8 * c.n), List.mem_append_left _ (List.mem_map_of_mem (hl i hi)),
        Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨w, List.mem_append_right _ hw, Nat.le_refl _, Nat.le_refl _⟩
  obtain U' : Unch base (pwW c midW) s₂.mem s₁₀.mem :=
    ((U₃.cover (cv (by decide))).trans ((U₄.cover cv4).trans ((U₅.cover (cv (by decide))).trans
      ((U₆.cover (cv (by decide))).trans ((U₇.cover (cv (by decide))).trans ((U₈.cover (cv (by decide))).trans
      ((U₉.cover (cv (by decide))).trans (U₁₀.cover (cv (by decide)))))))))).mono fun w hw => by
        simpa only [List.mem_append, or_self] using hw
  obtain UW : Unch base ([(c.sl FLAG, 4)] ++ pwW c midW) s.mem s₁₀.mem :=
    (U₂.trans U').mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact List.mem_append_left _ hw
      · exact List.mem_append_right _ hw
  obtain a : ∀ {i}, i < 45 → i ∉ midW → i ≠ FLAG → sv c base s₁₀ i = sv c base s i := fun hi hl hf =>
    sv_unch UW h7 hn hi (apart_append (apart_flag h0 hf) (apart_pwW hi hl))
  -- The values.
  obtain d₄ : sv c base s₄ D = dig c s₀ := by
    rw [e₄ (by decide) (by decide), v₃ (by decide) (by decide) (by decide), v₂ (by decide) (by decide), hF.d]
  obtain k₄ : sv c base s₄ K = sigR c s₀ := by
    rw [e₄ (by decide) (by decide), v₃ (by decide) (by decide) (by decide), v₂ (by decide) (by decide), hF.k]
  obtain em₆ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₆ EM') = Fin.ofNat c.C.n (dig c s₀) := by
    rw [v₆ (i := EM') (by decide) (by decide) (by decide),
      toM_r2 hnR (by rw [e₅, show sv c base s₄ R2N = _ from F₄.r2n]), d₄]
  obtain rm₆ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₆ RM') = Fin.ofNat c.C.n (sigR c s₀) := by
    rw [toM_r2 hnR (by rw [e₆, show sv c base s₅ R2N = _ from F₅.r2n]),
      v₅ (i := K) (by decide) (by decide) (by decide), k₄]
  obtain um₈ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₈ UM) =
      Fin.ofNat c.C.n (dig c s₀) * Fin.ofNat c.C.n (sigS c s₀) ^ (c.C.n - 2) := by
    rw [v₈ (i := UM) (by decide) (by decide) (by decide), toM_mul hnR e₇, em₆, acc₆, w₄]
  obtain vm₈ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₈ VM) =
      Fin.ofNat c.C.n (sigR c s₀) * Fin.ofNat c.C.n (sigS c s₀) ^ (c.C.n - 2) := by
    rw [toM_mul hnR e₈, v₇ (i := RM') (by decide) (by decide) (by decide), rm₆, acc₇, w₄]
  refine ⟨hs₁₀, by rw [wr₁₀, wr₉, wr₈, wr₇, wr₆, wr₅, K₄.2.2, wr₃, K₂.2.2, hF.wr],
    by rw [rd₁₀, rd₉, rd₈, rd₇, rd₆, rd₅, K₄.2.1, rd₃, K₂.2.1, hF.rd],
    by rw [g₁₀ _ (by decide), g₉ _ (by decide), g₈ _ (by decide), g₇ _ (by decide), g₆ _ (by decide),
      g₅ _ (by decide), K₄.1 _ (by decide), g₃ _ (by decide), K₂.1 _ (by decide), hF.esp], F₁₀,
    by rw [a (i := RX) (by decide) (by decide) (by decide), hF.rx],
    by rw [a (i := RY) (by decide) (by decide) (by decide), hF.ry],
    by rw [a (i := RZ) (by decide) (by decide) (by decide), hF.rz], fun t ht => ?_, ?_,
    by rw [a (i := PX) (by decide) (by decide) (by decide)]; exact hF.px_lt,
    by rw [a (i := PY) (by decide) (by decide) (by decide)]; exact hF.py_lt,
    by rw [a (i := PX) (by decide) (by decide) (by decide)]; exact hF.px,
    by rw [a (i := PY) (by decide) (by decide) (by decide)]; exact hF.py,
    by rw [v₁₀ (by decide) (by decide) (by decide), v₉ (by decide) (by decide) (by decide),
      v₈ (by decide) (by decide) (by decide), v₇ (by decide) (by decide) (by decide)]; exact lt₆,
    by rw [v₁₀ (by decide) (by decide) (by decide), v₉ (by decide) (by decide) (by decide),
      v₈ (by decide) (by decide) (by decide), v₇ (by decide) (by decide) (by decide), rm₆],
    by rw [v₁₀ (by decide) (by decide) (by decide)]; exact lt₉,
    by rw [v₁₀ (i := U) (by decide) (by decide) (by decide),
      toM_one_mul hnR (by rw [e₉, show sv c base s₈ ONE = 1 from F₈.one]), um₈],
    lt₁₀,
    by rw [toM_one_mul hnR (by rw [e₁₀, show sv c base s₉ ONE = 1 from F₉.one]),
      v₉ (i := VM) (by decide) (by decide) (by decide), vm₈], f₁₀, hF.sp_lo,
    by rw [a (i := K) (by decide) (by decide) (by decide)]; exact hF.k⟩
  · rw [tbl_unch UW h7 (j := 1) (by decide) ht (apart_append (tbl_apart_flag h0 1 t)
      (tbl_apart_pwW (by decide) ht (by decide)))]
    exact hF.t₁ t ht
  · rw [flagW, flag_unch_pwW U' h7 h0 hn (by decide), ← flagW]
    exact flag₂

end VG.Proof.Ecdsa.Verify.X86

end

end

/-!
# ECDSA verification on x86 (32-bit): `[u]G + [v]Q`

As on AArch64 (`Proof/Ecdsa/Verify/AArch64/Points.lean`).

`points_ok`: from what `mid_ok` leaves, the table of `u`'s bits, the
signature's ladder (from `G`), `save` (`[u]G` to `U`, and `R = O`), the
table of `v`'s bits, ECDH's ladder (from the key's point) and `sum` (the
complete addition of `U` and `R`, into `R`), for any invariants of the two
ladders: `R` holds `rcbAdd` of what the two ladders end with. `Main.lean`
gives the invariants of the group law.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Proof.Ecdh.X86
open VG.Impl.Ecdh.X86 (PX PY)
open VG.Impl.Ecdsa.Verify.X86 (SM' EM' RM' UM VM U V UX UY UZ)

variable {c : Cfg}

theorem tbl_le (h7 : c.n < 10) : bitsAt c.n 0 + 64 * c.n ≤ size := bitsAt_le c h7 (j := 0) (by decide)

/-- `[o] = x`, on numbered slots. -/
theorem setSl_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) {o x : Nat}
    (ho : o < 45) (hx : x < 2 ^ (64 * c.n)) :
    WP isa (.block (setConst c.n (c.sl o) x)) s fun s' =>
      sv c base s' o = x ∧ Keeps [.eax] s s' ∧ Outside base (c.sl o) (8 * c.n) s.mem s'.mem :=
  setConst_ok hs (sl_le c hc.n10 ho) hx

/-- The slots `save` writes. -/
abbrev saveW : List Nat := [UX, UY, UZ, RX, RY, RZ]

theorem save_eq (c : Cfg) : Impl.Ecdsa.Verify.X86.Cfg.save c =
    copy (2 * c.n) (c.sl UX) (c.sl RX) ++ (copy (2 * c.n) (c.sl UY) (c.sl RY) ++
    (copy (2 * c.n) (c.sl UZ) (c.sl RZ) ++ (setConst c.n (c.sl RX) 0 ++
    (setConst c.n (c.sl RY) (c.mont 1) ++ setConst c.n (c.sl RZ) 0)))) := by
  simp only [Impl.Ecdsa.Verify.X86.Cfg.save, List.append_assoc]

/-- `U = R`, and `R = O`. -/
theorem save_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) :
    WP isa (.block (Impl.Ecdsa.Verify.X86.Cfg.save c)) s fun s' =>
      Scr s' base size ∧ Keeps [.eax] s s' ∧ Unch base (slW c saveW) s.mem s'.mem ∧
      sv c base s' UX = sv c base s RX ∧ sv c base s' UY = sv c base s RY ∧
      sv c base s' UZ = sv c base s RZ ∧ sv c base s' RX = 0 ∧ sv c base s' RY = c.mont 1 ∧
      sv c base s' RZ = 0 := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp := hc.p_lt
  have hp3 := hc.p_ge
  obtain hm1 : c.mont 1 < 2 ^ (64 * c.n) := by
    have : c.mont 1 < c.C.p := Nat.mod_lt _ (by omega_using [hp3])
    omega_using [hp, this]
  rw [save_eq]
  refine WP.block_append (WP.mono (copySl_ok hc hs (o := UX) (a := RX) (by decide) (by decide) (by decide))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.block_append (WP.mono (copySl_ok hc hs₁ (o := UY) (a := RY) (by decide) (by decide) (by decide))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.block_append (WP.mono (copySl_ok hc hs₂ (o := UZ) (a := RZ) (by decide) (by decide) (by decide))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_)
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.block_append (WP.mono (setSl_ok hc hs₃ (o := RX) (x := 0) (by decide) (Nat.two_pow_pos _))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_)
  obtain hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.block_append (WP.mono (setSl_ok hc hs₄ (o := RY) (by decide) hm1) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_)
  obtain hs₅ := hs₄.of_keeps k₅ (by decide)
  refine WP.mono (setSl_ok hc hs₅ (o := RZ) (x := 0) (by decide) (Nat.two_pow_pos _))
    fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  obtain o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
      sv c base s' i = sv c base s i := fun O hi hij => sv_out O h7 hn hi hij
  refine ⟨hs₅.of_keeps k₆ (by decide), k₁.trans (k₂.trans (k₃.trans (k₄.trans (k₅.trans k₆)))), ?_,
    ?_, ?_, ?_, ?_, ?_, e₆⟩
  · have := O₁.unch.trans (O₂.unch.trans (O₃.unch.trans (O₄.unch.trans (O₅.unch.trans O₆.unch))))
    exact this.mono fun w hw => by simpa [saveW] using hw
  · rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), o O₄ (by decide) (by decide),
      o O₃ (by decide) (by decide), o O₂ (by decide) (by decide), e₁]
  · rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), o O₄ (by decide) (by decide),
      o O₃ (by decide) (by decide), e₂, o O₁ (by decide) (by decide)]
  · rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), o O₄ (by decide) (by decide), e₃,
      o O₂ (by decide) (by decide), o O₁ (by decide) (by decide)]
  · rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), e₄]
  · rw [o O₆ (by decide) (by decide), e₅]

/-- The slots `sum` writes. -/
abbrev sumW : List Nat := [T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, RX, RY, RZ]

/-- The slots of the addition. -/
abbrev sumSl : List Nat := [AP, B3P, T0, T1, T2, T3, T4, T5, DX, DY, DZ, UX, UY, UZ, RX, RY, RZ]

/-- The slots it reads. -/
abbrev sumR : List Nat := [AP, B3P, UX, UY, UZ, RX, RY, RZ]

theorem sum_eq (c : Cfg) : Impl.Ecdsa.Verify.X86.Cfg.sum c =
    .seq (fprog c.SP (rcb c.rcbSlots (c.pt UX UY UZ) (c.pt RX RY RZ) (c.pt DX DY DZ)))
      (.block (copy (2 * c.n) (c.sl RX) (c.sl DX) ++ (copy (2 * c.n) (c.sl RY) (c.sl DY) ++
        copy (2 * c.n) (c.sl RZ) (c.sl DZ)))) := by
  simp only [Impl.Ecdsa.Verify.X86.Cfg.sum, List.append_assoc]

/-- `R = U + R`, by the complete addition. -/
theorem sum_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hlt : ∀ i ∈ sumR, sv c base s i < c.C.p) :
    WP isa (Impl.Ecdsa.Verify.X86.Cfg.sum c) s fun s' =>
      Scr s' base size ∧ (∀ r, r ∉ clob → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Unch base (slWk c sumW) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧ sv c base s' RZ < c.C.p ∧
      (tmv c.C c.n base s' (c.sl RX), tmv c.C c.n base s' (c.sl RY), tmv c.C c.n base s' (c.sl RZ)) =
        rcbAdd (tmv c.C c.n base s (c.sl AP)) (tmv c.C c.n base s (c.sl B3P))
          (tmv c.C c.n base s (c.sl UX)) (tmv c.C c.n base s (c.sl UY)) (tmv c.C c.n base s (c.sl UZ))
          (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY)) (tmv c.C c.n base s (c.sl RZ)) ∧ sv c base s' RX < c.C.p := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  obtain hL : Lay c.MP' size (· ∈ sumSl.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  obtain hW : WkOk c.SP c.MP' c.C.p size c.wk (· ∈ sumSl.map c.sl) :=
    wkOk_map hc hc.fp rfl (jm := MP) (by decide) rfl rfl (by decide)
  obtain hA : RcbApart c.rcbSlots (c.pt UX UY UZ) (c.pt RX RY RZ) (c.pt DX DY DZ) :=
    rcbApart_of h0 (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ]) (lr := sumR) rfl rfl (by decide)
      (by decide)
  obtain hI : Inv c.MP' base size c.C.p (· ∈ sumSl.map c.sl) (sumR.map c.sl)
      (fun x => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base x c.n)) s := by
    refine ⟨hs, hM, fun x hx => ?_, fun x hx => ?_, fun _ _ => rfl⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      obtain sub : ∀ i ∈ sumR, i ∈ sumSl := by decide
      exact List.mem_map_of_mem (sub i hi)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact hlt i hi
  rw [sum_eq]
  refine WP.seq (WP.mono (rcb_ok hL hW hpR hA (fun x hx => ?_) hI (fun x hx => hx))
    fun s₁ ⟨PK, I₁, t₁, _⟩ => ?_)
  · rw [show rcbW c.rcbSlots (c.pt DX DY DZ) ++ rcbR c.rcbSlots (c.pt UX UY UZ) (c.pt RX RY RZ) =
      ([T0, T1, T2, T3, T4, T5, DX, DY, DZ] ++ sumR).map c.sl from rfl] at hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain sub : ∀ i ∈ [T0, T1, T2, T3, T4, T5, DX, DY, DZ] ++ sumR, i ∈ sumSl := by decide
    exact List.mem_map_of_mem (sub i hi)
  have hs₁ := I₁.scr
  obtain hD : ∀ i ∈ [DX, DY, DZ], c.sl i ∈ rcbW c.rcbSlots (c.pt DX DY DZ) ++ sumR.map c.sl := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> simp [rcbW, Cfg.pt]
  refine WP.block_append (WP.mono (copySl_ok hc hs₁ (o := RX) (a := DX) (by decide) (by decide) (by decide))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.block_append (WP.mono (copySl_ok hc hs₂ (o := RY) (a := DY) (by decide) (by decide) (by decide))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_)
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (copySl_ok hc hs₃ (o := RZ) (a := DZ) (by decide) (by decide) (by decide))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  obtain o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
      sv c base s' i = sv c base s i := fun O hi hij => sv_out O h7 hn hi hij
  obtain x₄ : sv c base s₄ RX = sv c base s₁ DX := by
    rw [o O₄ (by decide) (by decide), o O₃ (by decide) (by decide), e₂]
  obtain y₄ : sv c base s₄ RY = sv c base s₁ DY := by
    rw [o O₄ (by decide) (by decide), e₃, o O₂ (by decide) (by decide)]
  obtain z₄ : sv c base s₄ RZ = sv c base s₁ DZ := by
    rw [e₄, o O₃ (by decide) (by decide), o O₂ (by decide) (by decide)]
  obtain K₄ : Keeps [.eax] s₁ s₄ := k₂.trans (k₃.trans k₄)
  obtain U₄ : Unch base (slWk c sumW) s.mem s₄.mem := by
    have := ((Outs.unch PK.mem).trans (O₂.unch.trans (O₃.unch.trans O₄.unch)))
    refine this.mono fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · simp only [progW, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with ⟨y, hy, rfl⟩ | hw | hw | hw
      · simp only [rcbW, Cfg.rcbSlots, Cfg.pt, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [MP'_n]
      · subst hw; simp [MP'_n, MP'_tmp]
      · subst hw; exact List.mem_append_right _ (List.mem_cons_self ..)
      · subst hw; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    · simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | hw | hw <;> (subst hw; simp)
  refine ⟨hs₃.of_keeps k₄ (by decide), fun r hr => ?_, by rw [K₄.2.1, PK.rd], by rw [K₄.2.2, PK.wr],
    U₄, ?_, ?_, ?_, ?_⟩
  · rw [K₄.1 r (fun h => hr (by simp only [List.mem_singleton] at h; subst h; decide)), PK.gpr r hr]
  · have hM₁ := I₁.mod
    refine ⟨hM₁.n0, hM₁.mo, hM₁.tmp, hM₁.sep, ?_, hM₁.inv, hM₁.red⟩
    rw [U₄.wordsVal (fun w hw => ?_) (by have := hM₁.mo; omega_using [hn, this])]
    · exact hM.val
    · exact (apart_slWk (c := c) (i := MP) (by decide) (by decide)) w hw
  · rw [z₄]; exact I₁.lt _ (hD DZ (by simp))
  · have vx := I₁.val _ (hD DX (by simp))
    obtain vy := I₁.val _ (hD DY (by simp))
    obtain vz := I₁.val _ (hD DZ (by simp))
    show (toM _ _ (sv c base s₄ RX), toM _ _ (sv c base s₄ RY), toM _ _ (sv c base s₄ RZ)) = _
    rw [x₄, y₄, z₄]
    exact (congrArg₂ Prod.mk vx (congrArg₂ Prod.mk vy vz)).trans t₁
  · rw [x₄]; exact I₁.lt _ (hD DX (by simp))

/-- `Step` depends only on what the slots of `a`, `3b` and `G` stand for. -/
theorem Step.congr {L : LadderCfg} {C : Curve} {base : Addr} {s s' : State} {k : Nat}
    {Q : Nat → Fe C → Fe C → Fe C → Prop} {a0 : Bool} (h : Step L C base s k Q a0)
    (ha : tmv C L.M.n base s' L.S.a = tmv C L.M.n base s L.S.a)
    (hb : tmv C L.M.n base s' L.S.b3 = tmv C L.M.n base s L.S.b3)
    (hx : tmv C L.M.n base s' L.G.x = tmv C L.M.n base s L.G.x)
    (hy : tmv C L.M.n base s' L.G.y = tmv C L.M.n base s L.G.y)
    (hz : tmv C L.M.n base s' L.G.z = tmv C L.M.n base s L.G.z) : Step L C base s' k Q a0 := by
  intro j hj X Y Z X2 Y2 Z2 X3 Y3 Z3 hq h2 h3
  rw [ha, hb] at h2
  rw [ha, hb, hx, hy, hz] at h3
  exact h j hj X Y Z X2 Y2 Z2 X3 Y3 Z3 hq h2 h3

/-- After `[u]G + [v]Q`, for the invariants `Q₁` of the signature's ladder
and `Q₂` of ECDH's: `R` holds the complete addition of what they end with. -/
structure Pts (c : Cfg) (s₀ : State) (base : Addr)
    (Q₁ Q₂ : Nat → Fe c.C → Fe c.C → Fe c.C → Prop) (s : State) : Prop where
  scr : Scr s base size
  wr : s.wr = s₀.wr
  rd : s.rd = s₀.rd
  esp : s.gpr .esp = s₀.gpr .esp
  fixed : Fixed c base s₀.gpr s.mem
  t₁ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0
  flag : flagW c base s =
    mask32 (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n))
  rm_lt : sv c base s RM' < c.C.n
  rm : toM c.C.n (2 ^ (64 * c.n)) (sv c base s RM') = Fin.ofNat c.C.n (sigR c s₀)
  rz_lt : sv c base s RZ < c.C.p
  pt : ∃ X1 Y1 Z1 X2 Y2 Z2 : Fe c.C, Q₁ 0 X1 Y1 Z1 ∧ Q₂ 0 X2 Y2 Z2 ∧
    (tmv c.C c.n base s (c.sl RX), tmv c.C c.n base s (c.sl RY), tmv c.C c.n base s (c.sl RZ)) =
      rcbAdd (Fin.ofNat c.C.p c.C.a) (Fin.ofNat c.C.p (3 * c.C.b)) X1 Y1 Z1 X2 Y2 Z2
  whole : Frame (s₀.wr ++ [below (s₀.gpr .esp) c.stk]) s₀.mem s.mem
  sp_lo : c.stk ≤ (s₀.gpr .esp).toNat
  rx_lt : sv c base s RX < c.C.p
  /-- `r`, which `vg_<curve>_mul`'s scalar replaces. -/
  k : c.mul = none → sv c base s K = sigR c s₀

theorem Pts.keep {s₀ : State} {base : Addr} {Q₁ Q₂ : Nat → Fe c.C → Fe c.C → Fe c.C → Prop} {s : State}
    (h : Pts c s₀ base Q₁ Q₂ s) : Keep c s₀ base s :=
  ⟨h.scr, h.esp, h.rd, h.wr, h.fixed, h.whole, h.sp_lo⟩

/-- What `scalarAt` writes: `K`'s slot (for `vg_<curve>_mul`) or the table
of bits. -/
abbrev scW (c : Cfg) : List (Nat × Nat) := slW c [K] ++ [(bitsAt c.n 0, 64 * c.n)]

theorem apart_scW (h7 : c.n < 10) {i : Nat} (hi : i < 45) (hK : i ≠ K) :
    ∀ w ∈ scW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_slW (by simpa using hK)) (apart_tbl hi 0)

theorem fixedOk_scW (h7 : c.n < 10) : FixedOk c (scW c) :=
  (fixedOk_slW (by decide)).append (fixedOk_tbl 0)

theorem scW_le (h7 : c.n < 10) : ∀ w ∈ scW c, w.1 + w.2 ≤ size :=
  fun w hw => (List.mem_append.mp hw).elim (slW_le h7 (by decide) w) fun hw => by
    rw [List.mem_singleton.mp hw]; exact tbl_le h7

/-- The scalar at slot `i` to where the multiplication reads it: `K`'s slot
for `vg_<curve>_mul`, else the table of its bits. -/
theorem scalarAt_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) {i : Nat} (hi : i < 45)
    (hK : i ≠ K) :
    WP isa (Impl.Ecdsa.Verify.X86.Cfg.scalarAt c i) s fun s' => Keeps [.eax, .ebx, .edx, .esi] s s' ∧
      Unch base (scW c) s.mem s'.mem ∧ (c.mul = none → Unch base [(bitsAt c.n 0, 64 * c.n)] s.mem s'.mem) ∧
      (c.mul.isSome → sv c base s' K = sv c base s i) ∧
      (c.mul = none → ∀ t < 64 * c.n, s'.mem (off base (bitsAt c.n 0 + t)) =
        if (sv c base s i).testBit t then 1 else 0) := by
  have h7 := hc.n10
  unfold Impl.Ecdsa.Verify.X86.Cfg.scalarAt
  split
  · next C hC =>
    refine WP.mono (copySl_ok hc hs (o := K) (a := i) (by decide) hi (Ne.symm hK)) fun s' ⟨x, k, O⟩ =>
      ⟨k.mono (by decide), O.unch.mono fun w hw => List.mem_append_left _ (by simpa using hw),
        fun h => (by rw [hC] at h; cases h), fun _ => x, fun h => (by rw [hC] at h; cases h)⟩
  · next hN =>
    refine WP.mono (bits_ok hs hc.n0 (sl_le c h7 hi) (tbl_le h7)
      (Or.inl (by have := sl_below_bits c hi 0 0; omega_arith))) fun s' ⟨b, k, O⟩ =>
      ⟨k, O.unch.mono fun w hw => List.mem_append_right _ hw, fun _ => O.unch,
        fun h => (by rw [hN] at h; cases h), fun _ => b⟩

theorem points_eq (c : Cfg) : Impl.Ecdsa.Verify.X86.Cfg.points c =
    .seq (Impl.Ecdsa.Verify.X86.Cfg.scalarAt c U) (.seq (c.gen Impl.Ecdsa.Verify.X86.Args.verify.ao)
      (.seq (.block (Impl.Ecdsa.Verify.X86.Cfg.save c)) (.seq (Impl.Ecdsa.Verify.X86.Cfg.scalarAt c V)
      (.seq (c.qMul PX PY Impl.Ecdsa.Verify.X86.Args.verify.ao) (Impl.Ecdsa.Verify.X86.Cfg.sum c))))) := rfl

/-- The slots the multiplications, `save` and the sum write. -/
abbrev ptsW : List Nat :=
  [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TX, TY, TZ, TMP, UX, UY, UZ, K, ACC, PT]

/-- The ladders' slots. -/
abbrev ladL : List Nat :=
  [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP]

/-- What `points` writes but numbered slots: the table of bits and where
`vg_<curve>_mul` keeps the callee-saved registers. -/
abbrev ptsX (c : Cfg) : List (Nat × Nat) := [(bitsAt c.n 0, 64 * c.n), (c.sl nslots, 16)]

/-- `[u]G + [v]Q`, into `R`. -/
theorem points_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State}
    (hM : Mid c s₀ base s)
    (hA : c.mul.isSome ∨ 3 ≤ c.n ∧ c.n ≤ 6 → Point.LadArg s base Impl.Ecdsa.Verify.X86.Args.verify.ao)
    {Q₁ Q₂ : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hstep₁ : Step c.ladderCfg c.C base s (sv c base s U) Q₁ c.qA0) (hO₁ : Q₁ (64 * c.n) 0 1 0)
    (hstep₂ : Step (Impl.Ecdh.X86.Cfg.ladderQ c) c.C base s (sv c base s V) Q₂ c.qA0)
    (hO₂ : Q₂ (64 * c.n) 0 1 0) (hsp : SpOk (Impl.Ecdsa.Verify.X86.Cfg.points c) c.stk)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', Pts c s₀ base Q₁ Q₂ s' → WP isa rest s' Q) :
    WP isa (.seq (Impl.Ecdsa.Verify.X86.Cfg.points c) rest) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hM.scr.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have F := hM.fixed
  obtain hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  have hsp' := hsp
  rw [points_eq] at hsp'
  obtain hspG : SpOk (c.gen Impl.Ecdsa.Verify.X86.Args.verify.ao) 28 :=
    ⟨hsp'.right.left.1, Nat.le_trans hsp'.right.left.2 (Cfg.stk_le c)⟩
  obtain hspQ : SpOk (c.qMul PX PY Impl.Ecdsa.Verify.X86.Args.verify.ao) 28 :=
    ⟨hsp'.right.right.right.right.left.1, Nat.le_trans hsp'.right.right.right.right.left.2 (Cfg.stk_le c)⟩
  obtain tO : ∀ {t : State}, Fixed c base s₀.gpr t.mem →
      tmv c.C c.n base t (c.sl ZERO) = 0 ∧ tmv c.C c.n base t (c.sl ONEP) = 1 := fun {t} F' => by
    refine ⟨?_, ?_⟩
    · show toM _ _ (wordsVal t.mem base (c.sl ZERO) c.n) = _; rw [F'.zero, toM_zero]
    · show toM _ _ (wordsVal t.mem base (c.sl ONEP) c.n) = _; rw [F'.onep, toM_one hpR]
  refine WP.seq (hM.keep.withSp hsp ?_)
  rw [points_eq]
  -- `u` to where the multiplication reads it.
  refine WP.seq (WP.mono (scalarAt_ok hc hM.scr (i := U) (by decide) (by decide))
    fun s₁ ⟨k₁, U₁, U₁', sk₁, b₁⟩ => ?_)
  obtain hs₁ := hM.scr.of_keeps k₁ (by decide)
  obtain F₁ := F.unch h7 hn (fixedOk_scW h7) U₁
  obtain v₁ : ∀ {i}, i < 45 → i ≠ K → sv c base s₁ i = sv c base s i := fun hi hK =>
    sv_unch U₁ h7 hn hi (apart_scW h7 hi hK)
  obtain A₁ : c.mul.isSome ∨ 3 ≤ c.n ∧ c.n ≤ 6 → Point.LadArg s₁ base Impl.Ecdsa.Verify.X86.Args.verify.ao :=
    fun h => (hA h).keep (k₁.1 _ (by decide)) (k₁.1 _ (by decide)) k₁.2.1 k₁.2.2
      (frame_of_unch U₁ (scW_le h7) List.mem_cons_self)
  -- `[u]G`.
  obtain tv₁ : ∀ {i}, i < 45 → i ≠ K → tmv c.C c.n base s₁ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun hi hK => by
      show toM _ _ (sv c base s₁ _) = toM _ _ (sv c base s _)
      rw [v₁ hi hK]
  obtain hR₁ : Q₁ (64 * c.n) (tmv c.C c.n base s₁ (c.sl RX)) (tmv c.C c.n base s₁ (c.sl RY))
      (tmv c.C c.n base s₁ (c.sl RZ)) := by
    show Q₁ (64 * c.n) (toM _ _ (sv c base s₁ RX)) (toM _ _ (sv c base s₁ RY)) (toM _ _ (sv c base s₁ RZ))
    rw [v₁ (by decide) (by decide), v₁ (by decide) (by decide), v₁ (by decide) (by decide), hM.rx, hM.ry, hM.rz,
      toM_cmont hc, toM_zero]
    exact hO₁
  obtain hO₁' : Q₁ (64 * c.n) (tmv c.C c.n base s₁ (c.sl ZERO)) (tmv c.C c.n base s₁ (c.sl ONEP))
      (tmv c.C c.n base s₁ (c.sl ZERO)) := by rw [(tO F₁).1, (tO F₁).2]; exact hO₁
  refine WP.seq (WP.mono (qMul_ok hc (gx := GX) (gy := GY) (k := sv c base s U) (by decide) (by decide)
    (by decide) (by decide) (by decide) (ladLay hc) (ladWk hc) ladPt hspG hs₁ A₁ F₁.mp
    (lt_of_eq_of_lt F₁.ap (hmont _)) (lt_of_eq_of_lt F₁.b3p (hmont _))
    (lt_of_eq_of_lt F₁.onep (Nat.mod_lt _ (by omega_arith))) (lt_of_eq_of_lt F₁.zero (by omega_arith))
    (lt_of_eq_of_lt F₁.gx (hmont _)) (lt_of_eq_of_lt F₁.gy (hmont _))
    (by rw [v₁ (by decide) (by decide), hM.rx]; omega_arith) (by rw [v₁ (by decide) (by decide), hM.ry]; exact hmont _)
    (by rw [v₁ (by decide) (by decide), hM.rz]; omega_arith)
    (Step.congr hstep₁ (tv₁ (by decide) (by decide)) (tv₁ (by decide) (by decide)) (tv₁ (by decide) (by decide))
      (tv₁ (by decide) (by decide)) (tv₁ (by decide) (by decide))) hR₁ hO₁' sk₁ b₁)
    fun s₂ ⟨K₂, U₂, L₂, q₂, A₂⟩ => ?_)
  rw [Point.ladWp, ladWx_at] at U₂
  obtain hs₂ := hs₁.of_keeps K₂ (by decide)
  obtain F₂ := F₁.unch h7 hn (fixedOk_slWkG (l := ladL) (by decide)) U₂
  -- `U = [u]G`, `R = O`.
  refine WP.seq (WP.mono (save_ok hc hs₂) fun s₃ ⟨hs₃, k₃, U₃, ux₃, uy₃, uz₃, rx₃, ry₃, rz₃⟩ => ?_)
  obtain F₃ := F₂.unch h7 hn (fixedOk_slW (by decide)) U₃
  obtain A₃ : c.mul.isSome ∨ 3 ≤ c.n ∧ c.n ≤ 6 → Point.LadArg s₃ base Impl.Ecdsa.Verify.X86.Args.verify.ao :=
    fun h => (A₂ h).keep (k₃.1 _ (by decide)) (k₃.1 _ (by decide)) k₃.2.1 k₃.2.2
      (frame_of_unch U₃ (slW_le h7 (by decide)) List.mem_cons_self)
  -- `v` to where the multiplication reads it.
  obtain sub₂ : ∀ i ∈ ladL, i ∈ ptsW := by decide
  obtain sub₃ : ∀ i ∈ saveW, i ∈ ptsW := by decide
  obtain nap : ∀ {i}, i ∉ ptsW → i ∉ [ACC, PT] := fun hl h' => hl (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h'; rcases h' with rfl | rfl <;> decide)
  obtain W₃ : ∀ {i}, i < 45 → i ∉ ptsW → sv c base s₃ i = sv c base s i := fun hi hl =>
    ((sv_unch U₃ h7 hn hi (apart_slW (fun h => hl (sub₃ _ h)))).trans
      (sv_unch U₂ h7 hn hi (apart_slWkG hi (fun h => hl (sub₂ _ h)) (nap hl)))).trans
      (v₁ hi (fun h => hl (by rw [h]; decide)))
  refine WP.seq (WP.mono (scalarAt_ok hc hs₃ (i := V) (by decide) (by decide))
    fun s₄ ⟨k₄, U₄, U₄', sk₄, b₄⟩ => ?_)
  obtain hs₄ := hs₃.of_keeps k₄ (by decide)
  obtain F₄ := F₃.unch h7 hn (fixedOk_scW h7) U₄
  obtain v₄ : ∀ {i}, i < 45 → i ≠ K → sv c base s₄ i = sv c base s₃ i := fun hi hK =>
    sv_unch U₄ h7 hn hi (apart_scW h7 hi hK)
  obtain A₄ : c.mul.isSome ∨ 3 ≤ c.n ∧ c.n ≤ 6 → Point.LadArg s₄ base Impl.Ecdsa.Verify.X86.Args.verify.ao :=
    fun h => (A₃ h).keep (k₄.1 _ (by decide)) (k₄.1 _ (by decide)) k₄.2.1 k₄.2.2
      (frame_of_unch U₄ (scW_le h7) List.mem_cons_self)
  -- `[v]Q`.
  obtain tv₄ : ∀ {i}, i < 45 → i ∉ ptsW → tmv c.C c.n base s₄ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun hi hl => by
      show toM _ _ (sv c base s₄ _) = toM _ _ (sv c base s _)
      rw [v₄ hi (fun h => hl (by rw [h]; decide)), W₃ hi hl]
  obtain hR₄ : Q₂ (64 * c.n) (tmv c.C c.n base s₄ (c.sl RX))
      (tmv c.C c.n base s₄ (c.sl RY)) (tmv c.C c.n base s₄ (c.sl RZ)) := by
    show Q₂ (64 * c.n) (toM _ _ (sv c base s₄ RX)) (toM _ _ (sv c base s₄ RY)) (toM _ _ (sv c base s₄ RZ))
    rw [v₄ (by decide) (by decide), v₄ (by decide) (by decide), v₄ (by decide) (by decide), rx₃, ry₃, rz₃,
      toM_cmont hc, toM_zero]
    exact hO₂
  obtain hO₄ : Q₂ (64 * c.n) (tmv c.C c.n base s₄ (c.sl ZERO)) (tmv c.C c.n base s₄ (c.sl ONEP))
      (tmv c.C c.n base s₄ (c.sl ZERO)) := by rw [(tO F₄).1, (tO F₄).2]; exact hO₂
  obtain hV₃ : sv c base s₃ V = sv c base s V := W₃ (by decide) (by decide)
  refine WP.seq (WP.mono (qMul_ok hc (gx := PX) (gy := PY) (k := sv c base s V) (by decide) (by decide)
    (by decide) (by decide) (by decide) (ladLayQ hc) (ladWkQ hc) ladPtQ hspQ hs₄ A₄ F₄.mp
    (lt_of_eq_of_lt F₄.ap (hmont _)) (lt_of_eq_of_lt F₄.b3p (hmont _))
    (lt_of_eq_of_lt F₄.onep (Nat.mod_lt _ (by omega_arith))) (lt_of_eq_of_lt F₄.zero (by omega_arith))
    (by rw [v₄ (by decide) (by decide), W₃ (by decide) (by decide)]; exact hM.px_lt)
    (by rw [v₄ (by decide) (by decide), W₃ (by decide) (by decide)]; exact hM.py_lt)
    (by rw [v₄ (by decide) (by decide), rx₃]; omega_arith) (by rw [v₄ (by decide) (by decide), ry₃]; exact hmont _)
    (by rw [v₄ (by decide) (by decide), rz₃]; omega_arith)
    (Step.congr hstep₂ (tv₄ (by decide) (by decide)) (tv₄ (by decide) (by decide))
      (tv₄ (by decide) (by decide)) (tv₄ (by decide) (by decide)) (tv₄ (by decide) (by decide))) hR₄ hO₄
    (fun h => (sk₄ h).trans hV₃) (fun h t ht => by rw [b₄ h t ht, hV₃]))
    fun s₅ ⟨K₅, U₅, L₅, q₅, _⟩ => ?_)
  rw [Point.ladWp, ladWx_at] at U₅
  obtain hs₅ := hs₄.of_keeps K₅ (by decide)
  obtain F₅ := F₄.unch h7 hn (fixedOk_slWkG (l := ladL) (by decide)) U₅
  obtain M₅ := modP_of hc F₅.mp
  obtain v₅ : ∀ {i}, i < 45 → i ∉ ptsW → sv c base s₅ i = sv c base s₄ i := fun hi hl =>
    sv_unch U₅ h7 hn hi (apart_slWkG hi (fun h => hl (sub₂ _ h)) (nap hl))
  -- The sum.
  obtain u₅ : ∀ {i}, i ∈ [UX, UY, UZ] → sv c base s₅ i = sv c base s₃ i := fun {i} hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
      exact (sv_unch U₅ h7 hn (by decide) (apart_slWkG (by decide) (by decide) (by decide))).trans
        (v₄ (by decide) (by decide))
  refine WP.mono (sum_ok hc hs₅ M₅ (fun i hi => ?_)) fun s₆ ⟨hs₆, g₆, rd₆, wr₆, U₆, M₆, rz₆, t₆, rx₆⟩ f₆ => h s₆ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F₅.ap (hmont _)
    · exact lt_of_eq_of_lt F₅.b3p (hmont _)
    · rw [u₅ (by decide), ux₃]; exact L₂ _ (List.mem_cons_self ..)
    · rw [u₅ (by decide), uy₃]; exact L₂ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · rw [u₅ (by decide), uz₃]
      exact L₂ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    · exact L₅ _ (List.mem_cons_self ..)
    · exact L₅ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact L₅ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  obtain F₆ := F₅.unch h7 hn (fixedOk_slWk (by decide)) U₆
  obtain sub₆ : ∀ i ∈ sumW, i ∈ ptsW := by decide
  obtain UW : Unch base (ptsX c ++ slWkP c ptsW) s.mem s₆.mem := by
    obtain hsl : ∀ {l : List Nat}, (∀ i ∈ l, i ∈ ptsW) → ∀ w ∈ slWk c l, w ∈ ptsX c ++ slWkP c ptsW :=
      fun hl w hw => by
        rcases List.mem_append.mp hw with hw | hw
        · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
          exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _
            (List.mem_map_of_mem (hl i hi))))
        · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hw))
    obtain hslW : ∀ {l : List Nat}, (∀ i ∈ l, i ∈ ptsW) → ∀ w ∈ slW c l, w ∈ ptsX c ++ slWkP c ptsW :=
      fun hl w hw => hsl hl w (List.mem_append_left _ hw)
    obtain hslP : ∀ {l : List Nat}, (∀ i ∈ l, i ∈ ptsW) → ∀ w ∈ slWkP c l, w ∈ ptsX c ++ slWkP c ptsW :=
      fun hl w hw => by
        rcases List.mem_append.mp hw with hw | hw
        · exact hsl hl w hw
        · exact List.mem_append_right _ (List.mem_append_right _ hw)
    obtain hsc : ∀ w ∈ scW c, w ∈ ptsX c ++ slWkP c ptsW := fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hslW (by decide) w hw
      · rw [List.mem_singleton.mp hw]; exact List.mem_append_left _ List.mem_cons_self
    obtain hG : ∀ w ∈ slWkG c ladL, w ∈ ptsX c ++ slWkP c ptsW := fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hslP sub₂ w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact hslW (by decide) w hw
      · exact List.mem_append_left _ hw
    refine (U₁.trans (U₂.trans (U₃.trans (U₄.trans (U₅.trans U₆))))).mono fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · exact hsc w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hG w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hslW sub₃ w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hsc w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hG w hw
    · exact hsl sub₆ w hw
  obtain apX : ∀ {i}, i < 45 → ∀ w ∈ ptsX c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := fun hi w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Or.inl (by have := sl_below_bits c hi 0 0; omega_arith)
    · exact Or.inl (sl_lt c hi)
  obtain tu : ∀ {i j}, i ∈ [UX, UY, UZ] → j ∈ [RX, RY, RZ] → sv c base s₃ i = sv c base s₂ j →
      tmv c.C c.n base s₅ (c.sl i) = tmv c.C c.n base s₂ (c.sl j) := fun hi _ e => by
    show toM _ _ (sv c base s₅ _) = toM _ _ (sv c base s₂ _)
    rw [u₅ hi, e]
  obtain tR₅ : ∀ {i}, i ∈ [AP, B3P] → tmv c.C c.n base s₅ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun {i} hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      show toM _ _ (sv c base s₅ _) = toM _ _ (sv c base s _)
      rcases hi with rfl | rfl <;>
        rw [v₅ (by decide) (by decide), v₄ (by decide) (by decide), W₃ (by decide) (by decide)]
  obtain ha : tmv c.C c.n base s (c.sl AP) = Fin.ofNat c.C.p c.C.a := by
    show toM _ _ (wordsVal s.mem base (c.sl AP) c.n) = _
    rw [F.ap]; exact toM_cmont hc _
  obtain hb : tmv c.C c.n base s (c.sl B3P) = Fin.ofNat c.C.p (3 * c.C.b) := by
    show toM _ _ (wordsVal s.mem base (c.sl B3P) c.n) = _
    rw [F.b3p]; exact toM_cmont hc _
  obtain hFl := sl_le c h7 (i := FLAG) (by decide)
  obtain apF : ∀ w ∈ ptsX c ++ slWkP c ptsW, c.sl FLAG + 4 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := by
    intro w hw
    rcases (apart_append (apX (i := FLAG) (by decide))
      (apart_slWkP (c := c) (i := FLAG) (by decide) (by decide))) w hw with h | h
    · exact Or.inl (by omega_arith)
    · exact Or.inr h
  obtain rm₆ : sv c base s₆ RM' = sv c base s RM' :=
    sv_unch UW h7 hn (by decide) (apart_append (apX (by decide)) (apart_slWkP (by decide) (by decide)))
  refine ⟨hs₆, by rw [wr₆, K₅.2.2, k₄.2.2, k₃.2.2, K₂.2.2, k₁.2.2, hM.wr],
    by rw [rd₆, K₅.2.1, k₄.2.1, k₃.2.1, K₂.2.1, k₁.2.1, hM.rd],
    by rw [g₆ _ (by decide), K₅.1 _ (by decide), k₄.1 _ (by decide), k₃.1 _ (by decide), K₂.1 _ (by decide),
      k₁.1 _ (by decide), hM.esp], F₆, fun t ht => ?_,
    by rw [flagW, Unch.readW32 UW apF (by omega_arith), ← flagW]; exact hM.flag,
    by rw [rm₆]; exact hM.rm_lt, by rw [rm₆]; exact hM.rm, rz₆,
    ⟨_, _, _, _, _, _, q₂, q₅, by
      rw [t₆, tR₅ (by decide), tR₅ (by decide), ha, hb, tu (by decide) (by decide) ux₃,
        tu (by decide) (by decide) uy₃, tu (by decide) (by decide) uz₃]⟩, f₆, hM.sp_lo, rx₆, fun hN => ?_⟩
  · have hX : ∀ w ∈ ptsX c, bitsAt c.n 1 + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n 1 + t := fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact tbl_apart_tbl (j := 1) (j' := 0) (by decide) ht _ List.mem_cons_self
      · have := save_le_wk (c := c) h7
        have := wk_below_bits c 1
        exact Or.inr (by dsimp only; omega_arith)
    rw [tbl_unch UW h7 (j := 1) (by decide) ht (apart_append hX
      (tbl_apart_slWkP (by decide) (by decide) ht))]
    exact hM.t₁ t ht
  · -- `r`, kept where the curve has no `vg_<curve>_mul`.
    obtain tbK : ∀ w ∈ [(bitsAt c.n 0, 64 * c.n)], c.sl K + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl K :=
      apart_tbl (by decide) 0
    show wordsVal s₆.mem base (c.sl K) c.n = _
    rw [sv_unch U₆ h7 hn (i := K) (by decide) (apart_slWk (by decide) (by decide)),
      sv_unch U₅ h7 hn (i := K) (by decide) (apart_slWkG (by decide) (by decide) (by decide)),
      sv_unch (U₄' hN) h7 hn (i := K) (by decide) tbK,
      sv_unch U₃ h7 hn (i := K) (by decide) (apart_slW (by decide)),
      sv_unch U₂ h7 hn (i := K) (by decide) (apart_slWkG (by decide) (by decide) (by decide)),
      sv_unch (U₁' hN) h7 hn (i := K) (by decide) tbK]
    exact hM.k

end VG.Proof.Ecdsa.Verify.X86
