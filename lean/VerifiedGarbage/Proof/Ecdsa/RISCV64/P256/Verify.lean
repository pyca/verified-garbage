module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.Sign
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.Exchange
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Verify
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.Joint
public import VerifiedGarbage.Spec.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.CheckVerified
import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.CheckLit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.P256.Point
import VerifiedGarbage.Proof.EcKey.PublicKey

/-!
# ECDSA verification over P-256 on RISC-V: correctness

`vg_ecdsa_p256_verify` meets its contract by register (`verifyRV`), given
the group law (`verify_rv`): the setup (`vsetup_ok`: the saves, the public
key's point and first byte, the constants, `r`, `s` and `e`, and the
ranges of `r` and `s`), the check of the key (`check_ok`), `u` and `v`
(`uv_ok`), `[u]G + [v]Q` by the joint ladder (`Joint.joint_ok`,
`Proof/Ecdsa/RISCV64/P256/Joint.lean`), `x` and the comparison, and the result; the specification's
answer is `verify_eq`'s (`Proof/Ecdsa/Verify.lean`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P256

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Impl.Ecdsa.RISCV64.Sign VG.Impl.Ecdsa.RISCV64.Verify
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdh.RISCV64.P256
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt hashToInt)

/-- Whether the signature at `sig` of `digest` verifies with the key at `pk`,
as the specification answers. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  Spec.Ecdsa.verify W (bytesAt m pk 65) (hashToInt W (bytesAt m digest 32)) (bytesAt m sig 64)

def verifyRV : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .a0, 65⟩
    let digest : Region := ⟨s.gpr .a1, 32⟩
    let sig : Region := ⟨s.gpr .a2, 64⟩
    let scratch : Region := ⟨s.gpr .a3, 8192⟩
    s.rd = [pk, digest, sig] ∧ s.wr = [scratch] ∧ pk.Disjoint scratch ∧ digest.Disjoint scratch ∧
      sig.Disjoint scratch ∧ (s.gpr .a0).toNat + 65 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 32 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + 8192 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat % 8 = 0
  post s s' := s'.gpr .a0 = if vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3

/-! ## The setup -/

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
  x : sv base s' CX = ofBytes (bytesAt s.mem (s.gpr .a0 + BitVec.ofNat 64 1) 32)
  y : sv base s' CY = ofBytes (bytesAt s.mem (s.gpr .a0 + BitVec.ofNat 64 33) 32)
  rv : sv base s' VR = ofBytes (bytesAt s.mem (s.gpr .a2) 32)
  svs : sv base s' VS = ofBytes (bytesAt s.mem (s.gpr .a2 + BitVec.ofNat 64 32) 32)
  ev : sv base s' VE = ofBytes (bytesAt s.mem (s.gpr .a1) 32)
  flag : word s'.mem base FL = maskOf ((((decide (s.mem (s.gpr .a0) = 4) &&
    decide (ofBytes (bytesAt s.mem (s.gpr .a2) 32) < W.n)) && !decide (ofBytes (bytesAt s.mem (s.gpr .a2) 32) = 0)) &&
    decide (ofBytes (bytesAt s.mem (s.gpr .a2 + BitVec.ofNat 64 32) 32) < W.n)) &&
    !decide (ofBytes (bytesAt s.mem (s.gpr .a2 + BitVec.ofNat 64 32) 32) = 0))
  consts : ∀ e ∈ consts p256, sv base s' e.1 = e.2

theorem consts_apart : ∀ e ∈ consts p256, ∀ w ∈ [(p256.sl VR, 8 * 4)] ++ [(p256.sl VS, 8 * 4)] ++
    [(p256.sl VE, 8 * 4)] ++ [(FL, 8)] ++ [(FL, 8)], p256.sl e.1 + 32 ≤ w.1 ∨ w.1 + w.2 ≤ p256.sl e.1 := by decide

theorem consts_lt100 : ∀ e ∈ consts p256, e.1 < 100 := by decide

/-- `setup`. -/
theorem vsetup_ok {s : State} (hs : verifyRV.pre s) :
    WP isa (.block (Verify.Cfg.setup p256)) s (VSetup (s.gpr .a3) s) := by
  obtain ⟨hrd, hwr, hpd, hdd, hsd, hfp, hfd, hfg, hfs, hal⟩ := hs
  generalize hb : s.gpr .a3 = base at hwr hpd hdd hsd hfs hal
  have hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  rw [Verify.Cfg.setup]
  have e1 : ∀ (A B C D E F G H I J K : List Instr), A ++ B ++ C ++ D ++ E ++ F ++ G ++ H ++ I ++ J ++ K =
      A ++ ((B ++ C ++ D ++ E ++ F) ++ (G ++ (H ++ (I ++ (J ++ K))))) := by intros; simp only [List.append_assoc]
  rw [e1]
  refine WP.block_append (WP.mono (save_ok hb hwr' hfs hal)
    fun s₁ ⟨hw₁, h3₁, o₁, g₁, rd₁, wr₁, sp₁, U₁, w0, w1, w2, w3, w4⟩ => ?_)
  have a0 : s₁.gpr .a0 = s.gpr .a0 := g₁ _ (by decide) (by decide) (by decide)
  have a1 : s₁.gpr .a1 = s.gpr .a1 := g₁ _ (by decide) (by decide) (by decide)
  have a2 : s₁.gpr .a2 = s.gpr .a2 := g₁ _ (by decide) (by decide) (by decide)
  have rdp : (⟨s.gpr .a0, 65⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have rdd : (⟨s.gpr .a1, 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have rds : (⟨s.gpr .a2, 64⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  -- The key's point, its first byte and the constants.
  refine WP.block_append (WP.mono (peerLoad_ok hw₁ (q := .a0) (by decide) (by rw [a0, rd₁, wr₁]; exact rdp)
    (by rw [a0]; exact hpd) (by rw [a0]; exact hfp)) fun s₂ ⟨hw₂, r₂, U₂, x₂, y₂, f₂, c₂⟩ => ?_)
  have g₂ : ∀ r ∈ [Reg.a1, .a2], s₂.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [r₂.gpr _ (by decide), a1]
    · rw [r₂.gpr _ (by decide), a2]
  -- `r`, `s` and `e`.
  rw [show p256.n = 4 from rfl]
  refine WP.block_append (WP.mono (loadNum_ok 4 hw₂ (o := p256.sl VR) (p := .a2) (off := 0) (by decide) (by decide)
    (by decide) (by decide) (fun j hj => by rw [g₂ .a2 (by simp), r₂.rd, r₂.wr, rd₁, wr₁]; exact in_rd8 rds (by omega))
    (fun i hi => by rw [g₂ .a2 (by simp)]; exact out_of_disj hsd hfg (by omega)))
    fun s₃ ⟨r₃, O₃, e₃⟩ => ?_)
  have hw₃ := hw₂.of_rest r₃
  refine WP.block_append (WP.mono (loadNum_ok 4 hw₃ (o := p256.sl VS) (p := .a2) (off := 32) (by decide) (by decide)
    (by decide) (by decide)
    (fun j hj => by rw [r₃.gpr _ (by decide), g₂ .a2 (by simp), r₃.rd, r₃.wr, r₂.rd, r₂.wr, rd₁, wr₁]
                    exact in_rd8 rds (by omega))
    (fun i hi => by rw [r₃.gpr _ (by decide), g₂ .a2 (by simp)]; exact out_of_disj hsd hfg (by omega)))
    fun s₄ ⟨r₄, O₄, e₄⟩ => ?_)
  have hw₄ := hw₃.of_rest r₄
  have r₃₄ := r₃.trans r₄
  refine WP.block_append (WP.mono (loadNum_ok 4 hw₄ (o := p256.sl VE) (p := .a1) (off := 0) (by decide) (by decide)
    (by decide) (by decide)
    (fun j hj => by rw [r₃₄.gpr _ (by decide), g₂ .a1 (by simp), r₃₄.rd, r₃₄.wr, r₂.rd, r₂.wr, rd₁, wr₁]
                    exact in_rd8 rdd (by omega))
    (fun i hi => by rw [r₃₄.gpr _ (by decide), g₂ .a1 (by simp)]; exact out_of_disj hdd hfd (by omega)))
    fun s₅ ⟨r₅, O₅, e₅⟩ => ?_)
  have hw₅ := hw₄.of_rest r₅
  -- The ranges.
  refine WP.block_append (WP.mono (rangeOf_ok (i := VR) (by decide) hw₅) fun s₆ ⟨K₆, O₆, f₆⟩ => ?_)
  have hw₆ := hw₅.of_kp K₆
  refine WP.mono (rangeOf_ok (i := VS) (by decide) hw₆) fun s₇ ⟨K₇, O₇, f₇⟩ => ?_
  have hw₇ := hw₆.of_kp K₇
  -- What each step leaves.
  have U₃₇ := (((O₃.unch.trans O₄.unch).trans O₅.unch).trans O₆.unch).trans O₇.unch
  have U₂₇ := U₂.trans U₃₇
  have sp' : ∀ {q : Reg} {n : Nat}, (⟨s.gpr q, n⟩ : Region).Disjoint ⟨base, 8192⟩ → (s.gpr q).toNat + n ≤ 2 ^ 64 →
      ∀ {off k : Nat}, off + k ≤ n → ∀ i < k,
        ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr q + BitVec.ofNat 64 off + BitVec.ofNat 64 i) 1 :=
    fun hd hf _ _ hk => sep_at' hd hf hk
  have sp0 : ∀ {q : Reg} {n : Nat}, (⟨s.gpr q, n⟩ : Region).Disjoint ⟨base, 8192⟩ → (s.gpr q).toNat + n ≤ 2 ^ 64 →
      ∀ i < n, ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr q + BitVec.ofNat 64 i) 1 := fun hd hf i hi => by
    simpa using sep_at' hd hf (off := 0) (k := _) (by omega) i hi
  have K₁₇ : ∀ r ∈ preserved, s₇.gpr r = s₁.gpr r := fun r hr => by
    have h1 : r ∉ [Reg.t0, .t1] := fun h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> exact absurd hr (by decide)
    have h2 : r ∉ [Reg.t0, .t1, .a7] := fun h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> exact absurd hr (by decide)
    rw [K₇.gpr _ hr, K₆.gpr _ hr, r₅.gpr _ h1, r₄.gpr _ h1, r₃.gpr _ h1, r₂.gpr _ h2]
  have sv₅ : ∀ i, i < 44 → sv base s₇ i = sv base s₅ i := fun i hi => by
    show wordsVal _ _ _ _ = _
    rw [O₇.wordsVal (by rw [sl_eq, FL]; omega) (by rw [sl_eq]; omega),
      O₆.wordsVal (by rw [sl_eq, FL]; omega) (by rw [sl_eq]; omega)]
  have sr : ∀ i < 32, ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr .a2 + BitVec.ofNat 64 i) 1 := fun i hi => by
    simpa using sp' hsd hfg (off := 0) (k := 32) (by omega) i hi
  have r₅' : sv base s₅ VR = ofBytes (bytesAt s.mem (s.gpr .a2) 32) := by
    show wordsVal _ _ _ _ = _
    rw [O₅.wordsVal (by decide) (by decide), O₄.wordsVal (by decide) (by decide), e₃,
      r₂.gpr _ (by decide), a2, BitVec.add_zero, show (8 * 4 : Nat) = 32 from rfl,
      bytesAt_unch U₂ (by decide) sr, bytesAt_unch U₁ (by decide) sr]
  have s₅' : sv base s₅ VS = ofBytes (bytesAt s.mem (s.gpr .a2 + BitVec.ofNat 64 32) 32) := by
    show wordsVal _ _ _ _ = _
    rw [O₅.wordsVal (by decide) (by decide), e₄, r₃.gpr _ (by decide), r₂.gpr _ (by decide), a2,
      show (8 * 4 : Nat) = 32 from rfl,
      bytesAt_unch (U₂.trans O₃.unch) (by decide) (sp' hsd hfg (off := 32) (k := 32) (by omega)),
      bytesAt_unch U₁ (by decide) (sp' hsd hfg (off := 32) (k := 32) (by omega))]
  have mn₅ : sv base s₅ MN = W.n := by
    show wordsVal _ _ _ _ = _
    rw [O₅.wordsVal (by decide) (by decide), O₄.wordsVal (by decide) (by decide),
      O₃.wordsVal (by decide) (by decide)]
    exact const_at c₂ 1
  refine ⟨hw₇, by rw [K₁₇ _ (by decide), h3₁], fun x h0 h2 h3 hx => by rw [K₁₇ x hx, g₁ x h0 h2 h3], ?_, ?_, ?_,
    by rw [U₂₇.word (by decide) (by decide), w0], by rw [U₂₇.word (by decide) (by decide), w1],
    by rw [U₂₇.word (by decide) (by decide), w2], by rw [U₂₇.word (by decide) (by decide), w3],
    by rw [U₂₇.word (by decide) (by decide), w4], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [K₇.rd, K₆.rd, r₅.rd, r₄.rd, r₃.rd, r₂.rd, rd₁]
  · rw [K₇.wr, K₆.wr, r₅.wr, r₄.wr, r₃.wr, r₂.wr, wr₁]
  · rw [K₇.sp, K₆.sp, r₅.sp, r₄.sp, r₃.sp, r₂.sp, sp₁]
  · show wordsVal _ _ _ _ = _
    rw [sv_unch U₃₇ CX (by decide)]
    show sv base s₂ CX = _
    rw [x₂, a0, bytesAt_unch U₁ (by decide) (sp' hpd hfp (off := 1) (k := 32) (by omega))]
  · show wordsVal _ _ _ _ = _
    rw [sv_unch U₃₇ CY (by decide)]
    show sv base s₂ CY = _
    rw [y₂, a0, bytesAt_unch U₁ (by decide) (sp' hpd hfp (off := 33) (k := 32) (by omega))]
  · rw [sv₅ VR (by decide)]; exact r₅'
  · rw [sv₅ VS (by decide)]; exact s₅'
  · rw [sv₅ VE (by decide)]
    show wordsVal _ _ _ _ = _
    rw [e₅, r₃₄.gpr _ (by decide), g₂ .a1 (by simp), BitVec.add_zero, show (8 * 4 : Nat) = 32 from rfl,
      bytesAt_unch ((U₂.trans O₃.unch).trans O₄.unch) (by decide) (sp0 hdd hfd),
      bytesAt_unch U₁ (by decide) (sp0 hdd hfd)]
  · have h1 := bytesAt_unch U₁ (q := s.gpr .a0) (n := 1) (by decide)
      (by simpa using sp' hpd hfp (off := 0) (k := 1) (by omega))
    simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, List.cons.injEq, and_true,
      BitVec.add_zero] at h1
    have sv₆ : sv base s₆ VS = sv base s₅ VS := by
      show wordsVal _ _ _ _ = _
      rw [O₆.wordsVal (by decide) (by decide)]
    have mn₆ : sv base s₆ MN = W.n := by
      show wordsVal _ _ _ _ = _
      rw [O₆.wordsVal (by decide) (by decide)]; exact mn₅
    rw [f₇, f₆, (O₃.unch.trans O₄.unch).trans O₅.unch |>.word (by decide) (by decide), f₂, a0, h1, r₅', mn₅,
      sv₆, s₅', mn₆, maskOf_and, maskOf_and, maskOf_and, maskOf_and]
  · intro e he
    show wordsVal _ _ _ _ = _
    rw [sv_unch U₃₇ e.1 (consts_apart e he) (consts_lt100 e he)]
    exact c₂ e he

/-! ## `u` and `v` -/

/-- The slots `uv` reads, with what they hold. -/
structure UvPre (base : Addr) (s : State) (r sg e : Nat) : Prop where
  ws : WsReg s base
  one : sv base s ONE = 1
  rv : sv base s VR = r
  sv' : sv base s VS = sg
  ev : sv base s VE = e
  r2n : sv base s R2N = 2 ^ 256 * 2 ^ 256 % W.n
  onen : sv base s ONEN = 2 ^ 256 % W.n
  expn : sv base s EXPN = W.n - 2

/-- `w = (s R)^(n-2)`, `u = e w` and `v = r w` modulo `n`. -/
theorem uv_ok {base : Addr} {s : State} {r sg e : Nat} (hb : UvPre base s r sg e) :
    WP isa (Verify.Cfg.uv p256 p256Order) s fun s' => Kc s s' ∧
      Unch base (cw KM ++ chainWx (Cfg.chainN p256) 4 ++ cw EM ++ cw UM ++ cw UU ++ cw RM ++ cw VM ++ cw VV)
        s.mem s'.mem ∧
      sv base s' UU < W.n ∧ Fin.ofNat W.n (sv base s' UU) = Fin.ofNat W.n e * Fin.ofNat W.n sg ^ (W.n - 2) ∧
      sv base s' VV < W.n ∧ Fin.ofNat W.n (sv base s' VV) = Fin.ofNat W.n r * Fin.ofNat W.n sg ^ (W.n - 2) := by
  have hk4 : p256Order.S.k = 4 := rfl
  have hmN : p256Order.S.m = W.n := rfl
  have hn0 : 0 < W.n := by decide
  have hR : (2 : Nat) ^ (64 * p256Order.S.k) = 2 ^ 256 := rfl
  have nlt : ∀ y, y % W.n < W.n := fun y => Nat.mod_lt _ hn0
  have hw := hb.ws
  rw [Verify.Cfg.uv]
  simp only [progs]
  -- `s R`.
  refine WP.seq (WP.mono (mulCall_ok order_ok hw (o := p256.sl KM) (a := p256.sl VS) (b := p256.sl R2N)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv base s R2N < W.n; rw [hb.r2n]; exact nlt _)) fun s₂ ⟨C₂, lt₂, e₂⟩ => ?_)
  rw [hR, hk4, hmN] at e₂
  have hw₂ := hw.of_kp C₂.kp
  have U₂ : Unch base (cw KM) s.mem s₂.mem := C₂.mem
  have km : toM W.n (2 ^ 256) (sv base s₂ KM) = Fin.ofNat W.n sg := by
    refine toM_r2 unitN ?_
    rw [show sv base s₂ KM * 2 ^ 256 % W.n = _ from e₂]
    show sv base s VS * sv base s R2N % W.n = _
    rw [hb.r2n, hb.sv']
  -- `w`.
  have on₂ : sv base s₂ ONEN = 2 ^ 256 % W.n := by
    show wordsVal _ _ _ _ = _; rw [sv_unch U₂ ONEN (by decide)]; exact hb.onen
  refine WP.seq (WP.mono (chainPow_ok (P := Cfg.chainN p256) (F := p256Order) order_ok chainNLay unitN hw₂
    (one := p256.sl ONEN) (by decide) (by decide) (by show sv base s₂ ONEN = _; rw [on₂]; rfl) chainN_ok)
    fun s₃ ⟨K₃, U₃, lt₃, v₃⟩ => ?_)
  have hw₃ := hw₂.of_kc K₃
  have acc₃ : toM W.n (2 ^ 256) (sv base s₃ ACC) = Fin.ofNat W.n sg ^ (W.n - 2) := by
    have v : toM W.n (2 ^ 256) (sv base s₃ ACC) = toM W.n (2 ^ 256) (sv base s₂ KM) ^ (W.n - 2) := v₃
    rw [v, km]
  have acclt₃ : sv base s₃ ACC < W.n := lt₃
  have k13 : ∀ i ∈ [VE, VR, R2N, ONE], sv base s₃ i = sv base s i := fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    show wordsVal _ _ _ _ = _
    rcases hi with rfl | rfl | rfl | rfl <;>
      exact (sv_unch U₃ _ (by decide)).trans (sv_unch U₂ _ (by decide))
  have r2₃ : sv base s₃ R2N = 2 ^ 256 * 2 ^ 256 % W.n := (k13 R2N (by simp)).trans hb.r2n
  -- `e R`.
  refine WP.seq (WP.mono (mulCall_ok order_ok hw₃ (o := p256.sl EM) (a := p256.sl VE) (b := p256.sl R2N)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv base s₃ R2N < W.n; rw [r2₃]; exact nlt _)) fun s₄ ⟨C₄, lt₄, e₄⟩ => ?_)
  rw [hR, hk4, hmN] at e₄
  have hw₄ := hw₃.of_kp C₄.kp
  have U₄ : Unch base (cw EM) s₃.mem s₄.mem := C₄.mem
  have em : toM W.n (2 ^ 256) (sv base s₄ EM) = Fin.ofNat W.n e := by
    refine toM_r2 unitN ?_
    rw [show sv base s₄ EM * 2 ^ 256 % W.n = _ from e₄]
    show sv base s₃ VE * sv base s₃ R2N % W.n = _
    rw [r2₃, k13 VE (by simp), hb.ev]
  -- `u R`.
  have acc₄ : sv base s₄ ACC = sv base s₃ ACC := sv_unch U₄ ACC (by decide)
  refine WP.seq (WP.mono (mulCall_ok order_ok hw₄ (o := p256.sl UM) (a := p256.sl EM) (b := p256.sl ACC)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv base s₄ ACC < W.n; rw [acc₄]; exact acclt₃)) fun s₅ ⟨C₅, lt₅, e₅⟩ => ?_)
  rw [hR, hk4, hmN] at e₅
  have hw₅ := hw₄.of_kp C₅.kp
  have U₅ : Unch base (cw UM) s₄.mem s₅.mem := C₅.mem
  have um : toM W.n (2 ^ 256) (sv base s₅ UM) = Fin.ofNat W.n e * Fin.ofNat W.n sg ^ (W.n - 2) := by
    rw [toM_mul unitN e₅]
    show toM W.n (2 ^ 256) (sv base s₄ EM) * toM W.n (2 ^ 256) (sv base s₄ ACC) = _
    rw [em, acc₄, acc₃]
  -- `u`.
  have one₅ : sv base s₅ ONE = 1 := by
    show wordsVal _ _ _ _ = _
    rw [sv_unch U₅ ONE (by decide), sv_unch U₄ ONE (by decide)]
    exact (k13 ONE (by simp)).trans hb.one
  refine WP.seq (WP.mono (mulCall_ok order_ok hw₅ (o := p256.sl UU) (a := p256.sl UM) (b := p256.sl ONE)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv base s₅ ONE < W.n; rw [one₅]; decide)) fun s₆ ⟨C₆, lt₆, e₆⟩ => ?_)
  rw [hR, hk4, hmN] at e₆
  rw [hk4, hmN] at lt₆
  have hw₆ := hw₅.of_kp C₆.kp
  have U₆ : Unch base (cw UU) s₅.mem s₆.mem := C₆.mem
  have uu : Fin.ofNat W.n (sv base s₆ UU) = Fin.ofNat W.n e * Fin.ofNat W.n sg ^ (W.n - 2) := by
    rw [← um]
    refine toM_one_mul unitN ?_
    rw [show sv base s₆ UU * 2 ^ 256 % W.n = _ from e₆]
    show sv base s₅ UM * sv base s₅ ONE % W.n = _
    rw [one₅]
  -- `r R`.
  have r2₆ : sv base s₆ R2N = 2 ^ 256 * 2 ^ 256 % W.n := by
    show wordsVal _ _ _ _ = _
    rw [sv_unch U₆ R2N (by decide), sv_unch U₅ R2N (by decide), sv_unch U₄ R2N (by decide)]; exact r2₃
  refine WP.seq (WP.mono (mulCall_ok order_ok hw₆ (o := p256.sl RM) (a := p256.sl VR) (b := p256.sl R2N)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv base s₆ R2N < W.n; rw [r2₆]; exact nlt _)) fun s₇ ⟨C₇, lt₇, e₇⟩ => ?_)
  rw [hR, hk4, hmN] at e₇
  have hw₇ := hw₆.of_kp C₇.kp
  have U₇ : Unch base (cw RM) s₆.mem s₇.mem := C₇.mem
  have rm : toM W.n (2 ^ 256) (sv base s₇ RM) = Fin.ofNat W.n r := by
    refine toM_r2 unitN ?_
    rw [show sv base s₇ RM * 2 ^ 256 % W.n = _ from e₇]
    show sv base s₆ VR * sv base s₆ R2N % W.n = _
    rw [r2₆, show sv base s₆ VR = sv base s₃ VR from (sv_unch U₆ VR (by decide)).trans
      ((sv_unch U₅ VR (by decide)).trans (sv_unch U₄ VR (by decide))), k13 VR (by simp), hb.rv]
  -- `v R`.
  have acc₇ : sv base s₇ ACC = sv base s₃ ACC := by
    show wordsVal _ _ _ _ = _
    rw [sv_unch U₇ ACC (by decide), sv_unch U₆ ACC (by decide), sv_unch U₅ ACC (by decide)]; exact acc₄
  refine WP.seq (WP.mono (mulCall_ok order_ok hw₇ (o := p256.sl VM) (a := p256.sl RM) (b := p256.sl ACC)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv base s₇ ACC < W.n; rw [acc₇]; exact acclt₃)) fun s₈ ⟨C₈, lt₈, e₈⟩ => ?_)
  rw [hR, hk4, hmN] at e₈
  have hw₈ := hw₇.of_kp C₈.kp
  have U₈ : Unch base (cw VM) s₇.mem s₈.mem := C₈.mem
  have vm : toM W.n (2 ^ 256) (sv base s₈ VM) = Fin.ofNat W.n r * Fin.ofNat W.n sg ^ (W.n - 2) := by
    rw [toM_mul unitN e₈]
    show toM W.n (2 ^ 256) (sv base s₇ RM) * toM W.n (2 ^ 256) (sv base s₇ ACC) = _
    rw [rm, acc₇, acc₃]
  -- `v`.
  have one₈ : sv base s₈ ONE = 1 := by
    show wordsVal _ _ _ _ = _
    rw [sv_unch U₈ ONE (by decide), sv_unch U₇ ONE (by decide), sv_unch U₆ ONE (by decide)]; exact one₅
  refine WP.mono (mulCall_ok order_ok hw₈ (o := p256.sl VV) (a := p256.sl VM) (b := p256.sl ONE)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv base s₈ ONE < W.n; rw [one₈]; decide)) fun s₉ ⟨C₉, lt₉, e₉⟩ => ?_
  rw [hR, hk4, hmN] at e₉
  rw [hk4, hmN] at lt₉
  have U₉ : Unch base (cw VV) s₈.mem s₉.mem := C₉.mem
  have vv : Fin.ofNat W.n (sv base s₉ VV) = Fin.ofNat W.n r * Fin.ofNat W.n sg ^ (W.n - 2) := by
    rw [← vm]
    refine toM_one_mul unitN ?_
    rw [show sv base s₉ VV * 2 ^ 256 % W.n = _ from e₉]
    show sv base s₈ VM * sv base s₈ ONE % W.n = _
    rw [one₈]
  have uu₉ : sv base s₉ UU = sv base s₆ UU := by
    show wordsVal _ _ _ _ = _
    rw [sv_unch U₉ UU (by decide), sv_unch U₈ UU (by decide), sv_unch U₇ UU (by decide)]
  refine ⟨C₂.kp.kc.trans (K₃.trans (C₄.kp.kc.trans (C₅.kp.kc.trans (C₆.kp.kc.trans (C₇.kp.kc.trans
    (C₈.kp.kc.trans C₉.kp.kc)))))),
    ((((((U₂.trans U₃).trans U₄).trans U₅).trans U₆).trans U₇).trans U₈).trans U₉,
    by rw [uu₉]; exact lt₆, by rw [uu₉]; exact uu, lt₉, vv⟩

/-! ## The comparison and the end -/

/-- `x mod n`, `r mod n`, and their difference modulo `n`, zero exactly if `x ≡ r`. -/
theorem compare_ok {base : Addr} {s : State} (hw : WsReg s base) (hx : sv base s XO < W.p)
    (hz : sv base s ZERO = 0) :
    WP isa (Verify.Cfg.compare p256 p256Order) s fun s' => Kc s s' ∧
      Unch base (cw XN ++ cw RN ++ cw WD) s.mem s'.mem ∧
      (sv base s' WD = 0 ↔ Fin.ofNat W.n (sv base s XO) = Fin.ofNat W.n (sv base s VR)) := by
  have hk4 : p256Order.S.k = 4 := rfl
  have hmN : p256Order.S.m = W.n := rfl
  have hn0 : 0 < W.n := by decide
  have hpn : W.p < 2 * W.n := by decide
  have hn2 : 2 ^ 256 ≤ 2 * W.n := by decide
  rw [Verify.Cfg.compare]
  simp only [progs]
  refine WP.seq (WP.mono (addCall_ok order_ok hw (o := p256.sl XN) (a := p256.sl XO) (b := p256.sl ZERO)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv base s XO + sv base s ZERO < 2 * W.n; rw [hz]; omega)) fun s₁ ⟨C₁, v₁⟩ => ?_)
  rw [hk4, hmN] at v₁
  have hw₁ := hw.of_kp C₁.kp
  have U₁ : Unch base (cw XN) s.mem s₁.mem := C₁.mem
  have z₁ : sv base s₁ ZERO = 0 := by show wordsVal _ _ _ _ = _; rw [sv_unch U₁ ZERO (by decide)]; exact hz
  have r₁ : sv base s₁ VR = sv base s VR := sv_unch U₁ VR (by decide)
  refine WP.seq (WP.mono (addCall_ok order_ok hw₁ (o := p256.sl RN) (a := p256.sl VR) (b := p256.sl ZERO)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by
      show sv base s₁ VR + sv base s₁ ZERO < 2 * W.n
      have := wordsVal_lt s₁.mem base (p256.sl VR) 4
      rw [z₁]; show wordsVal _ _ _ _ + 0 < _; omega)) fun s₂ ⟨C₂, v₂⟩ => ?_)
  rw [hk4, hmN] at v₂
  have hw₂ := hw₁.of_kp C₂.kp
  have U₂ : Unch base (cw RN) s₁.mem s₂.mem := C₂.mem
  have xn₂ : sv base s₂ XN = sv base s XO % W.n := by
    show wordsVal _ _ _ _ = _
    rw [sv_unch U₂ XN (by decide), v₁]; show (sv base s XO + sv base s ZERO) % W.n = _; rw [hz, Nat.add_zero]
  have rn₂ : sv base s₂ RN = sv base s VR % W.n := by
    show wordsVal _ _ _ _ = _
    rw [v₂]; show (sv base s₁ VR + sv base s₁ ZERO) % W.n = _; rw [z₁, Nat.add_zero, r₁]
  refine WP.mono (subCall_ok order_ok hw₂ (o := p256.sl WD) (a := p256.sl XN) (b := p256.sl RN)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv base s₂ XN < W.n; rw [xn₂]; exact Nat.mod_lt _ hn0)
    (by show sv base s₂ RN < W.n; rw [rn₂]; exact Nat.mod_lt _ hn0)) fun s₃ ⟨C₃, v₃⟩ => ?_
  rw [hk4, hmN] at v₃
  have U₃ : Unch base (cw WD) s₂.mem s₃.mem := C₃.mem
  refine ⟨C₁.kp.kc.trans (C₂.kp.kc.trans C₃.kp.kc), (U₁.trans U₂).trans U₃, ?_⟩
  have hw' : sv base s₃ WD = (sv base s₂ XN + W.n - sv base s₂ RN) % W.n := v₃
  rw [hw', xn₂, rn₂, Fin.ext_iff, Fin.val_ofNat, Fin.val_ofNat]
  have h1 := Nat.mod_lt (sv base s XO) hn0
  have h2 := Nat.mod_lt (sv base s VR) hn0
  generalize sv base s XO % W.n = a at *
  generalize sv base s VR % W.n = b at *
  constructor
  · intro h
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hab | hab
    · rw [Nat.mod_eq_of_lt (by omega)] at h; omega
    · rw [show a + W.n - b = (a - b) + W.n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h; omega
  · intro h; subst h; rw [show a + W.n - a = W.n by omega, Nat.mod_self]

/-- The end: the masks of `Z ≠ 0` and of the difference being zero into the
flag, its low bit to `a0`, and the saved registers restored. -/
theorem vfinish_ok {s : State} {base : Addr} (hw : WsReg s base) {c : Bool}
    (hF : word s.mem base FL = maskOf c) :
    WP isa (.block (Verify.Cfg.finish p256)) s fun s' =>
      s'.gpr .a0 = (if (c && !decide (sv base s RZ = 0)) && decide (sv base s WD = 0) then 1 else 0) ∧
      s'.gpr .s0 = word s.mem base 0 ∧ s'.gpr .s1 = word s.mem base 8 ∧ s'.gpr .s2 = word s.mem base 16 ∧
      s'.gpr .ra = word s.mem base 24 ∧ s'.gpr .s3 = word s.mem base 32 ∧
      (∀ r ∈ preserved, r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp := by
  rw [Verify.Cfg.finish, retCode, restoreCode, show p256.n = 4 from rfl]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (nzFlag_ok (i := RZ) (by decide) hw) fun s₁ ⟨r₁, O₁, f₁⟩ => ?_)
  have hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono (zeroMask_ok hw₁ (n := 4) (a := p256.sl WD) (by decide) (by decide))
    fun s₂ ⟨r₂, m₂, g₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  refine WP.block_append (WP.mono (andFlag_ok hw₂) fun s₃ ⟨f₃, r₃, O₃⟩ => ?_)
  have hw₃ := hw₂.of_rest r₃
  have wd₁ : wordsVal s₁.mem base (p256.sl WD) 4 = sv base s WD := O₁.wordsVal (by decide) (by decide)
  generalize hB : ((c && !decide (sv base s RZ = 0)) && decide (sv base s WD = 0)) = B
  have fl₃ : word s₃.mem base FL = maskOf B := by
    rw [f₃, m₂, f₁, hF, g₂, wd₁, maskOf_and, maskOf_and, hB]
  have wd : ∀ d, d + 8 ≤ FL ∨ FL + 8 ≤ d → d + 8 ≤ 2048 → word s₃.mem base d = word s.mem base d := fun d h hd => by
    rw [O₃.word h (by omega), m₂, O₁.word h (by omega)]
  refine ld_ws hw₃ (d := p256.sl FLAG) (by decide) (by decide) fun s₉ u₉ => ?_
  refine WP.cons (exec_logicImm (by decide)) ?_
  have u₉' := Upd.write s₉ .a0 (s₉.gpr .a0 &&& BitVec.ofInt 64 1)
  have hw₉ := (hw₃.of_kp (Kp.of_upd u₉)).of_kp (Kp.of_upd u₉')
  refine ld_ws hw₉ (d := 24) (by decide) (by decide) fun t₁ v₁ => ?_
  have hv₁ := hw₉.of_kp (Kp.of_upd v₁)
  refine ld_ws hv₁ (d := 16) (by decide) (by decide) fun t₂ v₂ => ?_
  have hv₂ : WsReg t₂ base := ⟨by rw [v₂.other _ (by decide)]; exact hv₁.s0, by rw [v₂.wr]; exact hv₁.wr,
    hv₁.nowrap, hv₁.al⟩
  refine ld_ws hv₂ (d := 8) (by decide) (by decide) fun t₃ v₃ => ?_
  have hv₃ : WsReg t₃ base := ⟨by rw [v₃.other _ (by decide)]; exact hv₂.s0, by rw [v₃.wr]; exact hv₂.wr,
    hv₂.nowrap, hv₂.al⟩
  refine ld_ws hv₃ (d := 32) (by decide) (by decide) fun t₄ v₄ => ?_
  have hv₄ : WsReg t₄ base := ⟨by rw [v₄.other _ (by decide)]; exact hv₃.s0, by rw [v₄.wr]; exact hv₃.wr,
    hv₃.nowrap, hv₃.al⟩
  refine ld_ws hv₄ (d := 0) (by decide) (by decide) fun t₅ v₅ => WP.block_nil ?_
  have np : ∀ r ∈ preserved, r ∉ [Reg.t0, .t1, .t3, .t4, .a7, .a0, .ra] := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide),
      v₁.other _ (by decide), u₉'.gpr, u₉.gpr, sl_FLAG, fl₃, and_one]
  · rw [v₅.gpr, v₄.mem, v₃.mem, v₂.mem, v₁.mem, u₉'.mem, u₉.mem, wd 0 (by decide) (by decide)]
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, v₂.mem, v₁.mem, u₉'.mem, u₉.mem,
      wd 8 (by decide) (by decide)]
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.mem, u₉'.mem, u₉.mem,
      wd 16 (by decide) (by decide)]
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr,
      u₉'.mem, u₉.mem, wd 24 (by decide) (by decide)]
  · rw [v₅.other _ (by decide), v₄.gpr, v₃.mem, v₂.mem, v₁.mem, u₉'.mem, u₉.mem, wd 32 (by decide) (by decide)]
  · intro r hr h0 h1 h2' h3'
    have hn := np r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rw [v₅.other _ h0, v₄.other _ h3', v₃.other _ h1, v₂.other _ h2', v₁.other _ hn.2.2.2.2.2.2,
      u₉'.other _ hn.2.2.2.2.2.1, u₉.other _ hn.2.2.2.2.2.1, r₃.gpr _ (by simp [hn.1]),
      r₂.gpr _ (by simp [hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1]),
      r₁.gpr _ (by simp [hn.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1])]
  · rw [v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, u₉'.sp, u₉.sp, r₃.sp, r₂.sp, r₁.sp]

/-! ## The function -/

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

/-- `vg_ecdsa_p256_verify` by register. -/
theorem verify_ok (hL : VG.Proof.Weierstrass.Law W) {s : State} (hs : verifyRV.pre s) :
    WP isa verifyP256 s fun s' => abiPreserved s s' ∧ verifyRV.post s s' := by
  have hs' := hs
  obtain ⟨hrd, hwr, hpd, hdd, hsd, hfp, hfd, hfg, hfs, hal⟩ := hs'
  have hp0 : 0 < W.p := by decide
  rw [verifyP256, Verify.Cfg.verify]
  refine WP.seq (WP.mono (vsetup_ok hs) fun s₁ S => ?_)
  generalize hb : s.gpr .a3 = base at S hwr hpd hdd hsd hfs hal
  have Sx := S.x
  have Sy := S.y
  have Sflag := S.flag
  have Srv := S.rv
  -- The check.
  have hf₁ : word s₁.mem base FL = 0 ∨ word s₁.mem base FL = BitVec.allOnes 64 := by
    rw [S.flag]; unfold maskOf; split <;> simp
  refine WP.seq (WP.mono (check_ok S.ws S.s3 S.consts hf₁) fun s₂ ⟨K₂, U₂, f₂, px₂, py₂⟩ => ?_)
  have hw₂ := S.ws.of_kp K₂
  -- The constants modulo `n`.
  rw [show p256.n = 4 from rfl]
  refine WP.seq (WP.mono (consts_ok _ hw₂ nconsts_slots nconsts_nodup) fun s₃ ⟨r₃, U₃, e₃⟩ => ?_)
  have hw₃ := hw₂.of_rest r₃
  have cs₃ : ∀ e ∈ Cfg.nConsts p256, sv base s₃ e.1 = e.2 := fun e he => by
    rw [e₃ e he, Nat.mod_eq_of_lt (nconsts_lt e he)]
  have U₁₃ := U₂.trans U₃
  have k₁₃ : ∀ i ∈ [ONE, VR, VS, VE, ZERO, ONEP, AP, B3P, GX, GY, EXPP, MP, MN], sv base s₃ i = sv base s₁ i :=
    fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      show wordsVal _ _ _ _ = _
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact sv_unch U₁₃ _ (by decide)
  have tc₁ : TailConsts base s₁ := ⟨const_at S.consts 0, const_at S.consts 1, const_at S.consts 2,
    const_at S.consts 3, const_at S.consts 4, const_at S.consts 5, const_at S.consts 6, const_at S.consts 9⟩
  -- `u` and `v`.
  refine WP.seq (WP.mono (uv_ok (r := ofBytes (bytesAt s.mem (s.gpr .a2) 32))
    (sg := ofBytes (bytesAt s.mem (s.gpr .a2 + BitVec.ofNat 64 32) 32)) (e := ofBytes (bytesAt s.mem (s.gpr .a1) 32))
    ⟨hw₃, (k₁₃ ONE (by simp)).trans tc₁.one, (k₁₃ VR (by simp)).trans S.rv, (k₁₃ VS (by simp)).trans S.svs,
      (k₁₃ VE (by simp)).trans S.ev, cs₃ (R2N, _) (by decide), cs₃ (ONEN, _) (by decide), cs₃ (EXPN, _) (by decide)⟩)
    fun s₄ ⟨K₄, U₄, ult, uval, vlt, vval⟩ => ?_)
  have hw₄ := hw₃.of_kc K₄
  -- The key's point, or `G`.
  have tc₄ := (tc₁.of_unch U₁₃ (by decide)).of_unch U₄ (by decide)
  have gx₁ : sv base s₁ GX = W.gx * 2 ^ 256 % W.p := const_at S.consts 7
  have gy₁ : sv base s₁ GY = W.gy * 2 ^ 256 % W.p := const_at S.consts 8
  have e₂₄ : ∀ i ∈ [CPX, CPY], sv base s₄ i = sv base s₂ i := fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    show wordsVal _ _ _ _ = _
    rcases hi with rfl | rfl <;> exact sv_unch (U₃.trans U₄) _ (by decide)
  have e₁₄ : ∀ i ∈ [GX, GY, VR, AP, B3P, BP], sv base s₄ i = sv base s₁ i := fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    show wordsVal _ _ _ _ = _
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> exact sv_unch (U₁₃.trans U₄) _ (by decide)
  have bp₁ : sv base s₁ BP = W.b * 2 ^ 256 % W.p := const_at S.consts 11
  generalize hF : word s₂.mem base FL = F at px₂ py₂ f₂
  generalize hx : sv base s₁ CX = x at px₂ py₂ f₂ Sx
  generalize hy : sv base s₁ CY = y at px₂ py₂ f₂ Sy
  have hval : F ≠ 0 → CC.Valid x y := fun h0 => by
    by_contra h
    apply h0
    rw [f₂, mask_eq, decide_eq_false h]
    exact BitVec.and_zero
  have lt_qx : sv base s₄ CPX < W.p := by
    rw [e₂₄ CPX (by simp), px₂]; split
    · rw [gx₁]; exact Nat.mod_lt _ hp0
    · exact Nat.mod_lt _ hp0
  have lt_qy : sv base s₄ CPY < W.p := by
    rw [e₂₄ CPY (by simp), py₂]; split
    · rw [gy₁]; exact Nat.mod_lt _ hp0
    · exact Nat.mod_lt _ hp0
  generalize hQ : Point.affine (toM W.p (2 ^ 256) (sv base s₄ CPX)) (toM W.p (2 ^ 256) (sv base s₄ CPY)) = Q
  have hon : Spec.Weierstrass.onCurve W Q = true := by
    rw [← hQ, e₂₄ CPX (by simp), e₂₄ CPY (by simp), px₂, py₂]
    by_cases h0 : F = 0
    · rw [ite_eq_left h0, ite_eq_left h0, gx₁, gy₁, toM_mont unit, toM_mont unit]
      exact VG.Proof.P256.onCurve_G
    · rw [ite_eq_right h0, ite_eq_right h0, toM_mont unit, toM_mont unit]
      exact (hval h0).2.2
  -- `[u]G + [v]Q`, by the joint ladder.
  refine WP.seq (WP.mono (VG.Proof.Ecdsa.RISCV64.Joint.joint_ok hL ⟨hw₄, tc₄.ap, (e₁₄ BP (by simp)).trans bp₁,
    tc₄.zero, tc₄.onep,
    (e₁₄ GX (by simp)).trans gx₁, (e₁₄ GY (by simp)).trans gy₁, lt_qx, lt_qy, hQ, hon⟩)
    fun s₆ ⟨K₆, U₆, pR₆⟩ => ?_)
  have hw₆ := hw₄.of_kc K₆
  have tc₆ := tc₄.of_unch U₆ (by decide)
  have rep₆ : Rep W (tmv W 4 base s₆ (p256.sl RX)) (tmv W 4 base s₆ (p256.sl RY)) (tmv W 4 base s₆ (p256.sl RZ))
      (Spec.Weierstrass.add (Spec.Weierstrass.mul (sv base s₄ UU) (Spec.Weierstrass.G W))
        (Spec.Weierstrass.mul (sv base s₄ VV) Q)) := pR₆.rep
  have lt₆ : ∀ x ∈ [p256.sl RX, p256.sl RY, p256.sl RZ], wordsVal s₆.mem base x 4 < W.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    exacts [pR₆.x, pR₆.y, pR₆.z]
  -- `Z^(p-2)` and `x`.
  refine WP.seq (WP.mono (chainPow_ok (P := chainP p256) (F := p256Field) field_ok chainLay unit hw₆
    (one := p256.sl ONEP) (by decide) (by decide)
    (by show sv base s₆ ONEP = _; rw [tc₆.onep]; rfl) chainP_ok) fun s₇ ⟨K₇, U₇, lt₇, v₇⟩ => ?_)
  have hw₇ := hw₆.of_kc K₇
  have tc₇ := tc₆.of_unch U₇ (by decide)
  refine WP.seq (WP.mono (affine_ok hw₇ (t := XM) (o := XO) (a := RX) (by decide) (by decide) (by decide) (by decide)
    lt₇ tc₇.one) fun s₈ ⟨K₈, U₈, lt₈, v₈⟩ => ?_)
  have hw₈ := hw₇.of_kp K₈
  have tc₈ := tc₇.of_unch U₈ (by decide)
  -- The comparison and the end.
  refine WP.seq (WP.mono (compare_ok hw₈ lt₈ tc₈.zero) fun s₉ ⟨K₉, U₉, cmp⟩ => ?_)
  have hw₉ := hw₈.of_kc K₉
  have U₂₉ := (((((U₃.trans U₄).trans U₆).trans U₇).trans U₈).trans U₉)
  refine WP.mono (vfinish_ok hw₉ (c := (((((decide (s.mem (s.gpr .a0) = 4) &&
      decide (ofBytes (bytesAt s.mem (s.gpr .a2) 32) < W.n)) && !decide (ofBytes (bytesAt s.mem (s.gpr .a2) 32) = 0)) &&
      decide (ofBytes (bytesAt s.mem (s.gpr .a2 + BitVec.ofNat 64 32) 32) < W.n)) &&
      !decide (ofBytes (bytesAt s.mem (s.gpr .a2 + BitVec.ofNat 64 32) 32) = 0)) && decide (CC.Valid x y)))
    (by rw [U₂₉.word (by decide) (by decide), hF, f₂, Sflag, mask_eq, maskOf_and]))
    fun s' ⟨a0', s0', s1', s2', ra', s3', regs', sp'⟩ => ?_
  -- The registers.
  have w19 : ∀ d ∈ [0, 8, 16, 24, 32], word s₉.mem base d = word s₁.mem base d := fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl <;>
      rw [U₉.word (by decide) (by decide), U₈.word (by decide) (by decide), U₇.word (by decide) (by decide),
        U₆.word (by decide) (by decide), U₄.word (by decide) (by decide),
        U₃.word (by decide) (by decide), U₂.word (by decide) (by decide)]
  refine ⟨⟨fun r hr => ?_, by rw [sp', K₉.sp, K₈.sp, K₇.sp, K₆.sp, K₄.sp, r₃.sp, K₂.sp, S.sp],
    by rw [ra', w19 24 (by simp), S.sv3]⟩, ?_⟩
  · by_cases h0 : r = .s0
    · subst h0; rw [s0', w19 0 (by simp), S.sv0]
    by_cases h1 : r = .s1
    · subst h1; rw [s1', w19 8 (by simp), S.sv1]
    by_cases h2' : r = .s2
    · subst h2'; rw [s2', w19 16 (by simp), S.sv2]
    by_cases h3' : r = .s3
    · subst h3'; rw [s3', w19 32 (by simp), S.sv4]
    have ht : r ∉ [Reg.t0, .t1] := by
      rintro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> exact absurd hr (by decide)
    rw [regs' r hr h0 h1 h2' h3', K₉.gpr r hr h1, K₈.gpr r hr, K₇.gpr r hr h1, K₆.gpr r hr h1,
      K₄.gpr r hr h1, r₃.gpr r ht, K₂.gpr r hr, S.regs r h0 h2' h3' hr]
  -- The specification.
  have hsplit : bytesAt s.mem (s.gpr .a2) 64 =
      bytesAt s.mem (s.gpr .a2) 32 ++ bytesAt s.mem (s.gpr .a2 + BitVec.ofNat 64 32) 32 :=
    VG.Proof.Weierstrass.bytesAt_add s.mem (s.gpr .a2) 32 32
  have hrr : ofBytes ((bytesAt s.mem (s.gpr .a2) 64).take W.len) = ofBytes (bytesAt s.mem (s.gpr .a2) 32) := by
    rw [show W.len = 32 from rfl, hsplit, List.take_left' (VG.Proof.Weierstrass.length_bytesAt _ _ _)]
  have hss : ofBytes ((bytesAt s.mem (s.gpr .a2) 64).drop W.len) =
      ofBytes (bytesAt s.mem (s.gpr .a2 + BitVec.ofNat 64 32) 32) := by
    rw [show W.len = 32 from rfl, hsplit, List.drop_left' (VG.Proof.Weierstrass.length_bytesAt _ _ _)]
  generalize hR : ofBytes (bytesAt s.mem (s.gpr .a2) 32) = R at a0' hrr vval Sflag Srv
  generalize hSg : ofBytes (bytesAt s.mem (s.gpr .a2 + BitVec.ofNat 64 32) 32) = Sg at a0' hss uval vval Sflag
  have rz₉ : sv base s₉ RZ = sv base s₆ RZ := by
    show wordsVal _ _ _ _ = _
    rw [sv_unch U₉ RZ (by decide), sv_unch U₈ RZ (by decide), sv_unch U₇ RZ (by decide)]
  have vr₈ : sv base s₈ VR = R := by
    rw [← Srv]
    show wordsVal _ _ _ _ = _
    rw [sv_unch U₈ VR (by decide), sv_unch U₇ VR (by decide), sv_unch U₆ VR (by decide),
      sv_unch U₄ VR (by decide), sv_unch U₁₃ VR (by decide)]
  rw [rz₉] at a0'
  unfold verifyRV
  show s'.gpr .a0 = if vf s.mem (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) then 1 else 0
  rw [a0', vf, hash_eq]
  by_cases hrs : 1 ≤ R ∧ R < W.n ∧ 1 ≤ Sg ∧ Sg < W.n
  · -- In range: the key's point is the check's.
    have hrn : decide (R < W.n) = true := decide_eq_true hrs.2.1
    have hr0 : decide (R = 0) = false := decide_eq_false (by omega)
    have hsn : decide (Sg < W.n) = true := decide_eq_true hrs.2.2.2
    have hs0 : decide (Sg = 0) = false := decide_eq_false (by omega)
    generalize hb0 : s.mem (s.gpr .a0) = b0 at Sflag ⊢
    rw [hrn, hr0, hsn, hs0]
    have hlen : (bytesAt s.mem (s.gpr .a0) 65).length = 2 * W.len + 1 := VG.Proof.Weierstrass.length_bytesAt _ _ _
    have hpb := peer_bytes s.mem (s.gpr .a0) 32
    have hhd : (bytesAt s.mem (s.gpr .a0) 65).head? = some b0 := by rw [hpb, ← hb0]; rfl
    have hxv : ofBytes (((bytesAt s.mem (s.gpr .a0) 65).drop 1).take W.len) = x := by
      rw [show W.len = 32 from rfl, hpb, List.drop_one, List.tail_cons,
        List.take_left' (VG.Proof.Weierstrass.length_bytesAt _ _ _)]; exact Sx.symm
    have hyv : ofBytes ((bytesAt s.mem (s.gpr .a0) 65).drop (W.len + 1)) = y := by
      rw [show W.len = 32 from rfl, hpb, List.drop_succ_cons, List.drop_left' (VG.Proof.Weierstrass.length_bytesAt _ _ _)]
      exact Sy.symm
    have hP : ∀ h : VG.Proof.Ecdh.Valid W b0 x y, Q = .affine ⟨x, h.2.1⟩ ⟨y, h.2.2.1⟩ := fun h => by
      have hv : CC.Valid x y := (valid_iff x y).mpr h.2
      have hF0 : F ≠ 0 := by
        rw [f₂, Sflag, mask_eq, hrn, hr0, hsn, hs0, decide_eq_true h.1, decide_eq_true hv]; decide
      rw [← hQ, e₂₄ CPX (by simp), e₂₄ CPY (by simp), px₂, py₂, ite_eq_right hF0, ite_eq_right hF0,
        toM_mont unit, toM_mont unit, VG.Proof.EcKey.fe_eq h.2.1 rfl, VG.Proof.EcKey.fe_eq h.2.2.1 rfl]
    have rx₇ : sv base s₇ RX = sv base s₆ RX := sv_unch U₇ RX (by decide)
    have acc₇ : toM W.p (2 ^ 256) (sv base s₇ ACC) = toM W.p (2 ^ 256) (sv base s₆ RZ) ^ (W.p - 2) := by
      have v : toM W.p (2 ^ 256) (sv base s₇ ACC) = toM W.p (2 ^ 256) (sv base s₆ RZ) ^ (W.p - 2) := v₇
      rw [v]
    have hxoX : Fin.ofNat W.p (sv base s₈ XO) =
        tmv W 4 base s₆ (p256.sl RX) * tmv W 4 base s₆ (p256.sl RZ) ^ (W.p - 2) := by
      rw [v₈, acc₇, rx₇]
    have rzlt : sv base s₆ RZ < W.p := lt₆ _ (by simp)
    rw [VG.Proof.Ecdsa.verify_eq hL hlen hhd hxv hyv hP hrr hss ult vlt uval vval rep₆ lt₈ hxoX]
    have key : (((((((decide (b0 = 4) && true) && !false) && true) && !false) && decide (CC.Valid x y)) &&
        !decide (sv base s₆ RZ = 0)) && decide (sv base s₉ WD = 0)) =
        decide (VG.Proof.Ecdh.Valid W b0 x y ∧ (1 ≤ R ∧ R < W.n) ∧ (1 ≤ Sg ∧ Sg < W.n) ∧
          tmv W 4 base s₆ (p256.sl RZ) ≠ 0 ∧ Fin.ofNat W.n (sv base s₈ XO) = Fin.ofNat W.n R) := by
      rw [Bool.eq_iff_iff]
      simp only [Bool.and_true, Bool.not_false, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        decide_eq_false_iff_not]
      have hz : tmv W 4 base s₆ (p256.sl RZ) ≠ 0 ↔ ¬ sv base s₆ RZ = 0 := by
        rw [ne_eq]; exact not_congr (toM_eq_zero_iff unit rzlt)
      rw [hz, valid_iff, cmp, vr₈]
      unfold VG.Proof.Ecdh.Valid
      constructor
      · rintro ⟨⟨⟨h4, hv⟩, hz'⟩, hx'⟩; exact ⟨⟨h4, hv⟩, ⟨hrs.1, hrs.2.1⟩, ⟨hrs.2.2.1, hrs.2.2.2⟩, hz', hx'⟩
      · rintro ⟨⟨h4, hv⟩, -, -, hz', hx'⟩; exact ⟨⟨⟨h4, hv⟩, hz'⟩, hx'⟩
    rw [key]
  · -- Out of range: no signature verifies.
    rw [verify_false (by rw [hrr, hss]; exact hrs)]
    have hB : (((((((decide (s.mem (s.gpr .a0) = 4) && decide (R < W.n)) && !decide (R = 0)) &&
        decide (Sg < W.n)) && !decide (Sg = 0)) && decide (CC.Valid x y)) && !decide (sv base s₆ RZ = 0)) &&
        decide (sv base s₉ WD = 0)) = false := by
      rw [Bool.eq_false_iff]
      intro h
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at h
      exact hrs ⟨by have := h.1.1.1.1.1.2; omega, h.1.1.1.1.1.1.2, by have := h.1.1.1.2; omega, h.1.1.1.1.2⟩
    rw [hB]

theorem verify_rv (hL : VG.Proof.Weierstrass.Law W) (s : State) (hs : verifyRV.pre s) :
    ∃ t s', Exec isa verifyP256 s t s' ∧ abiPreserved s s' ∧ verifyRV.post s s' := by
  obtain ⟨t, s', he, h⟩ := verify_ok hL hs
  exact ⟨t, s', he, h⟩

end VG.Proof.Ecdsa.RISCV64.P256
