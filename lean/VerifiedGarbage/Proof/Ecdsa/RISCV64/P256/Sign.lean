module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.Tail
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Tail
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Sign
public import VerifiedGarbage.Spec.Ecdsa
public import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Order.Verified
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Order.Lit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.P256.Point

/-!
# ECDSA signatures over P-256 on RISC-V: correctness

`vg_ecdsa_p256_sign` meets its contract by register (`signRV`), given the
group law (`sign_rv`): the setup (`setupS_ok`: the saves, `k`, `d` and the
digest, the flag, the constants, `d`'s range and `G` to `R`), ECDH's `tail`
(`tail_ok`: `k`'s range, `R = [k]G`, `x`), the values modulo `n`
(`scalars_ok`), and the end (`finish_ok`: the checks of `r` and `s`, and
the signature under the flag); the specification's signature is
`signWith_eq`'s (`Proof/Ecdsa/Sign.lean`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P256

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg VG.Impl.Ecdsa.RISCV64.Sign
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdh.RISCV64.P256
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt hashToInt)
open VG.WriteBytes (writeBytes)

/-- The functions of `n` meet the contracts by register. -/
theorem order_ok : FieldOk p256Order :=
  ⟨P256Order.mul_rv, P256Order.add_rv, P256Order.sub_rv, Impl.Weierstrass.RISCV64.P256Order.mulFn_noFrames,
    Impl.Weierstrass.RISCV64.P256Order.addFn_noFrames, Impl.Weierstrass.RISCV64.P256Order.subFn_noFrames⟩

instance : NeZero p256Order.S.m := ⟨by decide⟩

instance : NeZero W.n := ⟨by decide⟩

theorem n_odd : W.n % 2 = 1 := by decide

theorem unitN : UnitMod W.n (2 ^ (64 * 4)) := unitMod_pow_two n_odd _

theorem powNLay : PowLayR (Cfg.powN p256) 4 where
  acc := by decide
  tmp := by decide
  base := by decide
  one := by decide
  short := by decide
  nbits := by decide
  k1 := by decide
  acc_tmp := by decide
  acc_one := by decide
  base_acc := by decide
  base_tmp := by decide
  bits_w := by decide
  acc8 := by decide
  tmp8 := by decide
  one8 := by decide
  bits8 := by decide

/-- The signature of `digest` with the private key at `d` and the secret
number at `k`, as the specification computes it. -/
abbrev sg (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith W (ofBytes (bytesAt m d 32)) (hashToInt W (bytesAt m digest 32)) (ofBytes (bytesAt m k 32))

def signRV : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 64⟩
    let d : Region := ⟨s.gpr .a1, 32⟩
    let digest : Region := ⟨s.gpr .a2, 32⟩
    let k : Region := ⟨s.gpr .a3, 32⟩
    let scratch : Region := ⟨s.gpr .a4, 8192⟩
    s.rd = [d, digest, k] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      digest.Disjoint scratch ∧ k.Disjoint scratch ∧ (s.gpr .a0).toNat + 64 ≤ 2 ^ 64 ∧
      (s.gpr .a1).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + 32 ≤ 2 ^ 64 ∧
      (s.gpr .a4).toNat + 8192 ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat % 8 = 0
  post s s' :=
    match sg s.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3) with
    | some rs => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) 64 = Spec.Ecdsa.encode W rs
    | none => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) 64 = List.replicate 64 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4

/-- `signRV` with the comb's table (`abi.withConsts`): `signRV` for the state
without it, and what the table adds. -/
def signRVC : Contract isa where
  pre s := signRV.pre (stripConsts Impl.Ecdsa.RISCV64.Comb.p256CombConsts s) ∧
    ConstsOk Impl.Ecdsa.RISCV64.Comb.p256CombConsts 0 s
  post := signRV.post
  pub s₁ s₂ := signRV.pub s₁ s₂ ∧ s₁.syms Impl.Ecdsa.RISCV64.Comb.p256Sym = s₂.syms Impl.Ecdsa.RISCV64.Comb.p256Sym

/-! ## The setup -/

/-- The slots `nConsts` sets. -/
theorem nconsts_slots : ∀ e ∈ Cfg.nConsts p256, e.1 < 44 := by decide

theorem nconsts_nodup : ((Cfg.nConsts p256).map Prod.fst).Nodup := by decide

theorem nconsts_lt : ∀ e ∈ Cfg.nConsts p256, e.2 < 2 ^ 256 := by decide

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
  k : sv base s' K = ofBytes (bytesAt s.mem (s.gpr .a3) 32)
  d : sv base s' DD = ofBytes (bytesAt s.mem (s.gpr .a1) 32)
  e : sv base s' EE = ofBytes (bytesAt s.mem (s.gpr .a2) 32)
  tc : TailConsts base s'
  r2n : sv base s' R2N = 2 ^ 256 * 2 ^ 256 % W.n
  onen : sv base s' ONEN = 2 ^ 256 % W.n
  expn : sv base s' EXPN = W.n - 2
  rx : sv base s' RX = W.gx * 2 ^ 256 % W.p
  ry : sv base s' RY = W.gy * 2 ^ 256 % W.p
  flag : word s'.mem base FL = maskOf ((true && decide (ofBytes (bytesAt s.mem (s.gpr .a1) 32) < W.n)) &&
    !decide (ofBytes (bytesAt s.mem (s.gpr .a1) 32) = 0))

/-- `setup`: the saves, `k`, `d` and the digest, the flag set, the
constants, the mask of `d` in `[1, n-1]`, and `G` to `R`'s first two slots. -/
theorem setupS_ok {s : State} (hs : signRV.pre (stripConsts Impl.Ecdsa.RISCV64.Comb.p256CombConsts s)) :
    WP isa (.block (Cfg.setup p256)) s (SetupS (s.gpr .a4) s) := by
  obtain ⟨hrd, hwr, hod, hdd, hed, hkd, hfo, hfd, hfe, hfk, hfs, hal⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr] at hrd hwr hod hdd hed hkd hfo hfd hfe hfk hfs hal
  rw [Cfg.setup, show p256.n = 4 from rfl]
  simp only [List.append_assoc]
  generalize hb : s.gpr .a4 = base at hwr hod hdd hed hkd hfs hal
  have hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  refine WP.block_append (WP.mono (save_ok hb hwr' hfs hal)
    fun s₁ ⟨hw₁, h3₁, o₁, g₁, rd₁, wr₁, sp₁, U₁, w0, w1, w2, w3, w4⟩ => ?_)
  have a1 : s₁.gpr .a1 = s.gpr .a1 := g₁ _ (by decide) (by decide) (by decide)
  have a2 : s₁.gpr .a2 = s.gpr .a2 := g₁ _ (by decide) (by decide) (by decide)
  have a3 : s₁.gpr .a3 = s.gpr .a3 := g₁ _ (by decide) (by decide) (by decide)
  have rdd : (⟨s.gpr .a1, 32⟩ : Region) ∈ s₁.rd ++ s₁.wr := by
    rw [rd₁]; exact List.mem_append_left _ (stripConsts_rd_mem (by rw [hrd]; simp))
  have rde : (⟨s.gpr .a2, 32⟩ : Region) ∈ s₁.rd ++ s₁.wr := by
    rw [rd₁]; exact List.mem_append_left _ (stripConsts_rd_mem (by rw [hrd]; simp))
  have rdk : (⟨s.gpr .a3, 32⟩ : Region) ∈ s₁.rd ++ s₁.wr := by
    rw [rd₁]; exact List.mem_append_left _ (stripConsts_rd_mem (by rw [hrd]; simp))
  -- `k`, `d` and the digest.
  refine WP.block_append (WP.mono (loadNum_ok 4 hw₁ (o := p256.sl K) (p := .a3) (off := 0) (by decide) (by decide)
    (by decide) (by decide) (fun j hj => by rw [a3]; exact in_rd8 rdk (by omega))
    (fun i hi => by rw [a3]; exact out_of_disj hkd hfk (by omega)))
    fun s₂ ⟨r₂, O₂, e₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  refine WP.block_append (WP.mono (loadNum_ok 4 hw₂ (o := p256.sl DD) (p := .a1) (off := 0) (by decide) (by decide)
    (by decide) (by decide) (fun j hj => by rw [r₂.gpr _ (by decide), a1, r₂.rd, r₂.wr]; exact in_rd8 rdd (by omega))
    (fun i hi => by rw [r₂.gpr _ (by decide), a1]; exact out_of_disj hdd hfd (by omega)))
    fun s₃ ⟨r₃, O₃, e₃⟩ => ?_)
  have hw₃ := hw₂.of_rest r₃
  have r₂₃ := r₂.trans r₃
  refine WP.block_append (WP.mono (loadNum_ok 4 hw₃ (o := p256.sl EE) (p := .a2) (off := 0) (by decide) (by decide)
    (by decide) (by decide) (fun j hj => by rw [r₂₃.gpr _ (by decide), a2, r₂₃.rd, r₂₃.wr]; exact in_rd8 rde (by omega))
    (fun i hi => by rw [r₂₃.gpr _ (by decide), a2]; exact out_of_disj hed hfe (by omega)))
    fun s₄ ⟨r₄, O₄, e₄⟩ => ?_)
  have hw₄ := hw₃.of_rest r₄
  have r₂₄ := r₂₃.trans r₄
  -- The flag.
  rw [List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_li (imm := 0) (by decide) fun s₄a u₄a => ?_
  refine WP.cons (exec_addi (by decide)) ?_
  have u₄b := Upd.write s₄a .t0 (s₄a.gpr .t0 + BitVec.ofInt 64 (-1))
  have hw₄b := (hw₄.of_kp (Kp.of_upd u₄a)).of_kp (Kp.of_upd u₄b)
  refine sd_ws hw₄b (d := p256.sl FLAG) (by decide) (by decide) fun s₅ u₅ => ?_
  have hw₅ := hw₄b.of_kp (Kp.of_mupd u₅)
  have fl₅ : word s₅.mem base FL = maskOf true := by
    rw [u₅.mem, sl_FLAG, word_writeW_self, u₄b.gpr, u₄a.gpr]; decide
  -- The constants.
  rw [constCode_eq]
  refine WP.block_append (WP.mono (consts_ok _ hw₅ consts_slots consts_nodup) fun s₆ ⟨r₆, U₆, e₆⟩ => ?_)
  have hw₆ := hw₅.of_rest r₆
  refine WP.block_append (WP.mono (consts_ok _ hw₆ nconsts_slots nconsts_nodup) fun s₇ ⟨r₇, U₇, e₇⟩ => ?_)
  have hw₇ := hw₆.of_rest r₇
  -- `d`'s range.
  refine WP.block_append (WP.mono (rangeOf_ok (i := DD) (by decide) hw₇) fun s₈ ⟨K₈, O₈, f₈⟩ => ?_)
  have hw₈ := hw₇.of_kp K₈
  -- `G` to `R`.
  refine WP.block_append (WP.mono (copy_ok 4 hw₈ (o := p256.sl RX) (a := p256.sl GX) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₉ ⟨v₉, r₉, O₉⟩ => ?_)
  have hw₉ := hw₈.of_rest r₉
  refine WP.mono (copy_ok 4 hw₉ (o := p256.sl RY) (a := p256.sl GY) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₁₀ ⟨v₁₀, r₁₀, O₁₀⟩ => ?_
  have hw₁₀ := hw₉.of_rest r₁₀
  -- What each step leaves.
  have O₅ : Unch base [(FL, 8)] s₄.mem s₅.mem := by
    rw [u₅.mem, u₄b.mem, u₄a.mem, sl_FLAG]; exact (writeW_outside _ _ _ (by decide)).unch
  have U₂₄ := (O₂.unch.trans O₃.unch).trans O₄.unch
  have U₅₇ := (O₅.trans U₆).trans U₇
  have U₈₁₀ := (O₈.unch.trans O₉.unch).trans O₁₀.unch
  have U₂₁₀ := (U₂₄.trans U₅₇).trans U₈₁₀
  have sp0 : ∀ {q : Reg} {n : Nat}, (⟨s.gpr q, n⟩ : Region).Disjoint ⟨base, 8192⟩ → (s.gpr q).toNat + n ≤ 2 ^ 64 →
      ∀ i < n, ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr q + BitVec.ofNat 64 i) 1 := fun hd hf i hi => by
    simpa using sep_at' hd hf (off := 0) (k := _) (by omega) i hi
  have bk : ∀ {q : Reg} {n : Nat}, (⟨s.gpr q, n⟩ : Region).Disjoint ⟨base, 8192⟩ → (s.gpr q).toNat + n ≤ 2 ^ 64 →
      bytesAt s₁.mem (s.gpr q) n = bytesAt s.mem (s.gpr q) n := fun hd hf =>
    bytesAt_unch U₁ (by decide) (sp0 hd hf)
  have cs₆ : ∀ e ∈ consts p256, sv base s₆ e.1 = e.2 := fun e he => by
    rw [e₆ e he, Nat.mod_eq_of_lt (consts_lt e he)]
  have cs₇ : ∀ e ∈ Cfg.nConsts p256, sv base s₇ e.1 = e.2 := fun e he => by
    rw [e₇ e he, Nat.mod_eq_of_lt (nconsts_lt e he)]
  have tc₆ : TailConsts base s₆ := ⟨const_at cs₆ 0, const_at cs₆ 1, const_at cs₆ 2, const_at cs₆ 3,
    const_at cs₆ 4, const_at cs₆ 5, const_at cs₆ 6, const_at cs₆ 9⟩
  have K₁₀ : ∀ r ∈ preserved, s₁₀.gpr r = s₁.gpr r := fun r hr => by
    have h0 : r ∉ [Reg.t0] := fun h => by simp only [List.mem_singleton] at h; subst h; exact absurd hr (by decide)
    have h1 : r ∉ [Reg.t0, .t1] := fun h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> exact absurd hr (by decide)
    rw [r₁₀.gpr _ h0, r₉.gpr _ h0, K₈.gpr _ hr, r₇.gpr _ h1, r₆.gpr _ h1, u₅.gpr,
      u₄b.other _ (by rintro rfl; exact absurd hr (by decide)),
      u₄a.other _ (by rintro rfl; exact absurd hr (by decide)), r₂₄.gpr _ h1]
  have sv₁₀ : ∀ i, i < 44 → i ≠ RX → i ≠ RY → sv base s₁₀ i = sv base s₈ i := fun i hi h1 h2 => by
    show wordsVal _ _ _ _ = _
    rw [O₁₀.wordsVal (by simp only [sl_eq, RY] at *; omega) (by rw [sl_eq]; omega),
      O₉.wordsVal (by simp only [sl_eq, RX] at *; omega) (by rw [sl_eq]; omega)]
  have sv₈ : ∀ i, i < 44 → sv base s₈ i = sv base s₇ i := fun i hi =>
    sv_unch O₈.unch i (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; rw [sl_eq, FL]; omega)
      (by omega)
  have sv₂₇ : ∀ i ∈ [K, DD, EE], sv base s₇ i = sv base s₄ i := fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> exact sv_unch U₅₇ _ (by decide) (by decide)
  have dv : sv base s₇ DD = ofBytes (bytesAt s.mem (s.gpr .a1) 32) := by
    rw [sv₂₇ DD (by simp)]
    show wordsVal _ _ _ _ = _
    rw [O₄.wordsVal (by decide) (by decide), e₃, r₂.gpr _ (by decide), a1, BitVec.add_zero,
      show (8 * 4 : Nat) = 32 from rfl, bytesAt_unch O₂.unch (by decide) (sp0 hdd hfd), bk hdd hfd]
  refine ⟨hw₁₀, by rw [K₁₀ _ (by decide), o₁], by rw [K₁₀ _ (by decide), h3₁],
    fun x h0 h2 h3 hx => by rw [K₁₀ x hx, g₁ x h0 h2 h3], ?_, ?_, ?_,
    by rw [U₂₁₀.word (by decide) (by decide), w0], by rw [U₂₁₀.word (by decide) (by decide), w1],
    by rw [U₂₁₀.word (by decide) (by decide), w2], by rw [U₂₁₀.word (by decide) (by decide), w3],
    by rw [U₂₁₀.word (by decide) (by decide), w4], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r₁₀.rd, r₉.rd, K₈.rd, r₇.rd, r₆.rd, u₅.rd, u₄b.rd, u₄a.rd, r₂₄.rd, rd₁]
  · rw [r₁₀.wr, r₉.wr, K₈.wr, r₇.wr, r₆.wr, u₅.wr, u₄b.wr, u₄a.wr, r₂₄.wr, wr₁]
  · rw [r₁₀.sp, r₉.sp, K₈.sp, r₇.sp, r₆.sp, u₅.sp, u₄b.sp, u₄a.sp, r₂₄.sp, sp₁]
  · rw [sv₁₀ K (by decide) (by decide) (by decide), sv₈ K (by decide), sv₂₇ K (by simp)]
    show wordsVal _ _ _ _ = _
    rw [O₄.wordsVal (by decide) (by decide), O₃.wordsVal (by decide) (by decide), e₂, a3, BitVec.add_zero,
      show (8 * 4 : Nat) = 32 from rfl, bk hkd hfk]
  · rw [sv₁₀ DD (by decide) (by decide) (by decide), sv₈ DD (by decide), dv]
  · rw [sv₁₀ EE (by decide) (by decide) (by decide), sv₈ EE (by decide), sv₂₇ EE (by simp)]
    show wordsVal _ _ _ _ = _
    rw [e₄, r₂₃.gpr _ (by decide), a2, BitVec.add_zero, show (8 * 4 : Nat) = 32 from rfl,
      bytesAt_unch (O₂.unch.trans O₃.unch) (by decide) (sp0 hed hfe), bk hed hfe]
  · exact (tc₆.of_unch U₇ (by decide)).of_unch U₈₁₀ (by decide)
  · rw [sv₁₀ R2N (by decide) (by decide) (by decide), sv₈ R2N (by decide)]; exact cs₇ (R2N, _) (by decide)
  · rw [sv₁₀ ONEN (by decide) (by decide) (by decide), sv₈ ONEN (by decide)]; exact cs₇ (ONEN, _) (by decide)
  · rw [sv₁₀ EXPN (by decide) (by decide) (by decide), sv₈ EXPN (by decide)]; exact cs₇ (EXPN, _) (by decide)
  · show wordsVal _ _ _ _ = _
    rw [O₁₀.wordsVal (by decide) (by decide), v₉, show wordsVal s₈.mem base (p256.sl GX) 4 = sv base s₈ GX from rfl,
      sv₈ GX (by decide),
      show sv base s₇ GX = sv base s₆ GX from sv_unch U₇ GX (by decide)]
    exact const_at cs₆ 7
  · show wordsVal _ _ _ _ = _
    rw [v₁₀, O₉.wordsVal (by decide) (by decide), show wordsVal s₈.mem base (p256.sl GY) 4 = sv base s₈ GY from rfl,
      sv₈ GY (by decide),
      show sv base s₇ GY = sv base s₆ GY from sv_unch U₇ GY (by decide)]
    exact const_at cs₆ 8
  · have mn₇ : sv base s₇ MN = W.n := (sv_unch U₇ MN (by decide)).trans tc₆.mn
    rw [(O₉.unch.trans O₁₀.unch).word (by decide) (by decide), f₈, (U₆.trans U₇).word (by decide) (by decide),
      fl₅, dv, mn₇, maskOf_and, maskOf_and]

/-! ## The values modulo `n` -/

/-- The slots `back` reads, with what they hold. -/
structure BackPre (base : Addr) (s : State) (k d e x : Nat) : Prop where
  ws : WsReg s base
  xv : sv base s XO = x
  xlt : x < W.p
  zero : sv base s ZERO = 0
  one : sv base s ONE = 1
  kv : sv base s K = k
  dv : sv base s DD = d
  ev : sv base s EE = e
  r2n : sv base s R2N = 2 ^ 256 * 2 ^ 256 % W.n
  onen : sv base s ONEN = 2 ^ 256 % W.n
  expn : sv base s EXPN = W.n - 2

/-- What a call writes: its result and the field's own working space. -/
abbrev cw (o : Nat) : List (Nat × Nat) := [(p256.sl o, 8 * 4), (own 4, 64 * 4)]

theorem hl {i : Nat} (hi : i < 44) : p256.sl i + 8 * p256Order.S.k ≤ own p256Order.S.k := by
  show 64 + 32 * i + 32 ≤ 3840 + 0 - 0 + 0; omega

theorem hs {i : Nat} (hi : i < 44) : p256.sl i < 2048 := by rw [sl_eq]; omega

/-- `r = x mod n`, then `s = k^(n-2) (e + r d) mod n`. -/
theorem nback_ok {base : Addr} {s : State} {k d e x : Nat} (hb : BackPre base s k d e x) :
    WP isa (.seq (addCall p256Order (p256.sl RR) (p256.sl XO) (p256.sl ZERO)) (Cfg.scalars p256 p256Order)) s
      fun s' => Kc s s' ∧
        Unch base (cw RR ++ cw KM ++ powWx (Cfg.powN p256) 4 ++ cw EM ++ cw RM ++ cw DM ++ cw TT ++ cw SU ++
          cw SMM ++ cw SS) s.mem s'.mem ∧
        sv base s' RR = x % W.n ∧ sv base s' SS < W.n ∧
        Fin.ofNat W.n (sv base s' SS) =
          Fin.ofNat W.n k ^ (W.n - 2) * (Fin.ofNat W.n e + Fin.ofNat W.n (x % W.n) * Fin.ofNat W.n d) := by
  have hk4 : p256Order.S.k = 4 := rfl
  have hmN : p256Order.S.m = W.n := rfl
  have hn0 : 0 < W.n := by decide
  have hw := hb.ws
  -- `r`.
  refine WP.seq (WP.mono (addCall_ok order_ok hw (o := p256.sl RR) (a := p256.sl XO) (b := p256.sl ZERO)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv base s XO + sv base s ZERO < 2 * W.n; rw [hb.xv, hb.zero]; have := hb.xlt; have hpn : W.p < 2 * W.n := by decide
        omega))
    fun s₁ ⟨C₁, v₁⟩ => ?_)
  have hw₁ := hw.of_kp C₁.kp
  have U₁ : Unch base (cw RR) s.mem s₁.mem := C₁.mem
  rw [hk4, hmN] at v₁
  have rr₁ : sv base s₁ RR = x % W.n := by
    show wordsVal _ _ _ _ = _
    rw [v₁]; show (sv base s XO + sv base s ZERO) % W.n = _; rw [hb.xv, hb.zero, Nat.add_zero]
  rw [Cfg.scalars]
  simp only [progs]
  have hR : (2 : Nat) ^ (64 * p256Order.S.k) = 2 ^ 256 := rfl
  have nlt : ∀ y, y % W.n < W.n := fun y => Nat.mod_lt _ hn0
  -- `k R`.
  have r2₁ : sv base s₁ R2N = 2 ^ 256 * 2 ^ 256 % W.n := (sv_unch U₁ R2N (by decide)).trans hb.r2n
  refine WP.seq (WP.mono (mulCall_ok order_ok hw₁ (o := p256.sl KM) (a := p256.sl K) (b := p256.sl R2N)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv base s₁ R2N < W.n; rw [r2₁]; exact nlt _)) fun s₂ ⟨C₂, lt₂, e₂⟩ => ?_)
  rw [hR, hk4, hmN] at e₂
  rw [hk4, hmN] at lt₂
  have hw₂ := hw₁.of_kp C₂.kp
  have U₂ : Unch base (cw KM) s₁.mem s₂.mem := C₂.mem
  have km : toM W.n (2 ^ 256) (sv base s₂ KM) = Fin.ofNat W.n k := by
    refine toM_r2 unitN ?_
    rw [show sv base s₂ KM * 2 ^ 256 % W.n = _ from e₂]
    show sv base s₁ K * sv base s₁ R2N % W.n = _
    rw [r2₁, show sv base s₁ K = sv base s K from sv_unch U₁ K (by decide), hb.kv]
  -- `w = (k R)^(n-2)`.
  have on₂ : sv base s₂ ONEN = 2 ^ 256 % W.n := by
    show wordsVal _ _ _ _ = _
    rw [sv_unch U₂ ONEN (by decide), sv_unch U₁ ONEN (by decide)]; exact hb.onen
  have ex₂ : sv base s₂ EXPN = W.n - 2 := by
    show wordsVal _ _ _ _ = _
    rw [sv_unch U₂ EXPN (by decide), sv_unch U₁ EXPN (by decide)]; exact hb.expn
  refine WP.seq (WP.mono (pow_ok (P := Cfg.powN p256) (F := p256Order) order_ok rfl powNLay unitN hw₂ hn0
    (by show sv base s₂ ONEN = _; rw [on₂]; rfl) (by show sv base s₂ EXPN < _; rw [ex₂]; decide))
    fun s₃ ⟨K₃, U₃, lt₃, v₃⟩ => ?_)
  have hw₃ := hw₂.of_kc K₃
  have acc₃ : toM W.n (2 ^ 256) (sv base s₃ ACC) = Fin.ofNat W.n k ^ (W.n - 2) := by
    have v : toM W.n (2 ^ 256) (sv base s₃ ACC) = toM W.n (2 ^ 256) (sv base s₂ KM) ^ sv base s₂ EXPN := v₃
    rw [v, km, ex₂]
  have acclt₃ : sv base s₃ ACC < W.n := lt₃
  -- A slot the steps so far keep.
  have k13 : ∀ i ∈ [EE, DD, R2N, ONE, RR], sv base s₃ i = sv base s₁ i := fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      exact (sv_unch U₃ _ (by decide)).trans (sv_unch U₂ _ (by decide))
  have r2₃ : sv base s₃ R2N = 2 ^ 256 * 2 ^ 256 % W.n := (k13 R2N (by simp)).trans r2₁
  -- `e R`.
  refine WP.seq (WP.mono (mulCall_ok order_ok hw₃ (o := p256.sl EM) (a := p256.sl EE) (b := p256.sl R2N)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv base s₃ R2N < W.n; rw [r2₃]; exact nlt _)) fun s₄ ⟨C₄, lt₄, e₄⟩ => ?_)
  rw [hR, hk4, hmN] at e₄
  rw [hk4, hmN] at lt₄
  have hw₄ := hw₃.of_kp C₄.kp
  have U₄ : Unch base (cw EM) s₃.mem s₄.mem := C₄.mem
  have em : toM W.n (2 ^ 256) (sv base s₄ EM) = Fin.ofNat W.n e := by
    refine toM_r2 unitN ?_
    rw [show sv base s₄ EM * 2 ^ 256 % W.n = _ from e₄]
    show sv base s₃ EE * sv base s₃ R2N % W.n = _
    rw [r2₃, k13 EE (by simp), show sv base s₁ EE = sv base s EE from sv_unch U₁ EE (by decide), hb.ev]
  -- `r R`.
  have r2₄ : sv base s₄ R2N = 2 ^ 256 * 2 ^ 256 % W.n := (sv_unch U₄ R2N (by decide)).trans r2₃
  refine WP.seq (WP.mono (mulCall_ok order_ok hw₄ (o := p256.sl RM) (a := p256.sl RR) (b := p256.sl R2N)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv base s₄ R2N < W.n; rw [r2₄]; exact nlt _)) fun s₅ ⟨C₅, lt₅, e₅⟩ => ?_)
  rw [hR, hk4, hmN] at e₅
  rw [hk4, hmN] at lt₅
  have hw₅ := hw₄.of_kp C₅.kp
  have U₅ : Unch base (cw RM) s₄.mem s₅.mem := C₅.mem
  have rm : toM W.n (2 ^ 256) (sv base s₅ RM) = Fin.ofNat W.n (x % W.n) := by
    refine toM_r2 unitN ?_
    rw [show sv base s₅ RM * 2 ^ 256 % W.n = _ from e₅]
    show sv base s₄ RR * sv base s₄ R2N % W.n = _
    rw [r2₄, show sv base s₄ RR = sv base s₃ RR from sv_unch U₄ RR (by decide), k13 RR (by simp), rr₁]
  -- `d R`.
  have r2₅ : sv base s₅ R2N = 2 ^ 256 * 2 ^ 256 % W.n := (sv_unch U₅ R2N (by decide)).trans r2₄
  refine WP.seq (WP.mono (mulCall_ok order_ok hw₅ (o := p256.sl DM) (a := p256.sl DD) (b := p256.sl R2N)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv base s₅ R2N < W.n; rw [r2₅]; exact nlt _)) fun s₆ ⟨C₆, lt₆, e₆⟩ => ?_)
  rw [hR, hk4, hmN] at e₆
  rw [hk4, hmN] at lt₆
  have hw₆ := hw₅.of_kp C₆.kp
  have U₆ : Unch base (cw DM) s₅.mem s₆.mem := C₆.mem
  have dm : toM W.n (2 ^ 256) (sv base s₆ DM) = Fin.ofNat W.n d := by
    refine toM_r2 unitN ?_
    rw [show sv base s₆ DM * 2 ^ 256 % W.n = _ from e₆]
    show sv base s₅ DD * sv base s₅ R2N % W.n = _
    rw [r2₅, show sv base s₅ DD = sv base s₃ DD from (sv_unch U₅ DD (by decide)).trans (sv_unch U₄ DD (by decide)),
      k13 DD (by simp), show sv base s₁ DD = sv base s DD from sv_unch U₁ DD (by decide), hb.dv]
  -- `r d R`.
  refine WP.seq (WP.mono (mulCall_ok order_ok hw₆ (o := p256.sl TT) (a := p256.sl RM) (b := p256.sl DM)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    lt₆) fun s₇ ⟨C₇, lt₇, e₇⟩ => ?_)
  rw [hR, hk4, hmN] at e₇
  rw [hk4, hmN] at lt₇
  have hw₇ := hw₆.of_kp C₇.kp
  have U₇ : Unch base (cw TT) s₆.mem s₇.mem := C₇.mem
  have rm₆ : sv base s₆ RM = sv base s₅ RM := sv_unch U₆ RM (by decide)
  have tt : toM W.n (2 ^ 256) (sv base s₇ TT) = Fin.ofNat W.n (x % W.n) * Fin.ofNat W.n d := by
    rw [toM_mul unitN e₇]
    show toM W.n (2 ^ 256) (sv base s₆ RM) * toM W.n (2 ^ 256) (sv base s₆ DM) = _
    rw [rm₆, rm, dm]
  -- `(e + r d) R`.
  have em₆ : sv base s₆ EM = sv base s₄ EM :=
    (sv_unch U₆ EM (by decide)).trans (sv_unch U₅ EM (by decide))
  have em₇ : sv base s₇ EM = sv base s₄ EM := (sv_unch U₇ EM (by decide)).trans em₆
  refine WP.seq (WP.mono (addCall_ok order_ok hw₇ (o := p256.sl SU) (a := p256.sl EM) (b := p256.sl TT)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by
      show sv base s₇ EM + sv base s₇ TT < 2 * W.n
      have l4 : sv base s₄ EM < W.n := lt₄
      have l7 : sv base s₇ TT < W.n := lt₇
      rw [em₇]; omega)) fun s₈ ⟨C₈, v₈⟩ => ?_)
  rw [hk4, hmN] at v₈
  have hw₈ := hw₇.of_kp C₈.kp
  have U₈ : Unch base (cw SU) s₇.mem s₈.mem := C₈.mem
  have su : toM W.n (2 ^ 256) (sv base s₈ SU) = Fin.ofNat W.n e + Fin.ofNat W.n (x % W.n) * Fin.ofNat W.n d := by
    rw [show sv base s₈ SU = _ from v₈, toM_add]
    show toM W.n (2 ^ 256) (sv base s₇ EM) + toM W.n (2 ^ 256) (sv base s₇ TT) = _
    rw [em₇, em, tt]
  have sult : sv base s₈ SU < W.n := by rw [show sv base s₈ SU = _ from v₈]; exact nlt _
  -- `w (e + r d) R`.
  refine WP.seq (WP.mono (mulCall_ok order_ok hw₈ (o := p256.sl SMM) (a := p256.sl ACC) (b := p256.sl SU)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    sult) fun s₉ ⟨C₉, lt₉, e₉⟩ => ?_)
  rw [hR, hk4, hmN] at e₉
  rw [hk4, hmN] at lt₉
  have hw₉ := hw₈.of_kp C₉.kp
  have U₉ : Unch base (cw SMM) s₈.mem s₉.mem := C₉.mem
  have acc₈ : sv base s₈ ACC = sv base s₃ ACC := by
    show wordsVal _ _ _ _ = wordsVal _ _ _ _
    rw [sv_unch U₈ ACC (by decide), sv_unch U₇ ACC (by decide), sv_unch U₆ ACC (by decide),
      sv_unch U₅ ACC (by decide), sv_unch U₄ ACC (by decide)]
  have smm : toM W.n (2 ^ 256) (sv base s₉ SMM) =
      Fin.ofNat W.n k ^ (W.n - 2) * (Fin.ofNat W.n e + Fin.ofNat W.n (x % W.n) * Fin.ofNat W.n d) := by
    rw [toM_mul unitN e₉]
    show toM W.n (2 ^ 256) (sv base s₈ ACC) * toM W.n (2 ^ 256) (sv base s₈ SU) = _
    rw [acc₈, acc₃, su]
  -- `s`, out of Montgomery's form.
  have one₉ : sv base s₉ ONE = 1 := by
    show wordsVal _ _ _ _ = _
    rw [sv_unch U₉ ONE (by decide), sv_unch U₈ ONE (by decide), sv_unch U₇ ONE (by decide),
      sv_unch U₆ ONE (by decide), sv_unch U₅ ONE (by decide), sv_unch U₄ ONE (by decide)]
    show sv base s₃ ONE = 1
    rw [k13 ONE (by simp)]
    show wordsVal _ _ _ _ = _
    rw [sv_unch U₁ ONE (by decide)]
    exact hb.one
  refine WP.mono (mulCall_ok order_ok hw₉ (o := p256.sl SS) (a := p256.sl SMM) (b := p256.sl ONE)
    (hl (by decide)) (hl (by decide)) (hl (by decide)) (hs (by decide)) (hs (by decide)) (hs (by decide))
    (by show sv base s₉ ONE < W.n; rw [one₉]; decide)) fun s₁₀ ⟨C₁₀, lt₁₀, e₁₀⟩ => ?_
  rw [hR, hk4, hmN] at e₁₀
  rw [hk4, hmN] at lt₁₀
  have U₁₀ : Unch base (cw SS) s₉.mem s₁₀.mem := C₁₀.mem
  have ss : Fin.ofNat W.n (sv base s₁₀ SS) = toM W.n (2 ^ 256) (sv base s₉ SMM) := by
    refine toM_one_mul unitN ?_
    rw [show sv base s₁₀ SS * 2 ^ 256 % W.n = _ from e₁₀]
    show sv base s₉ SMM * sv base s₉ ONE % W.n = _
    rw [one₉]
  refine ⟨C₁.kp.kc.trans (C₂.kp.kc.trans (K₃.trans (C₄.kp.kc.trans (C₅.kp.kc.trans (C₆.kp.kc.trans
    (C₇.kp.kc.trans (C₈.kp.kc.trans (C₉.kp.kc.trans C₁₀.kp.kc)))))))),
    ((((((((U₁.trans U₂).trans U₃).trans U₄).trans U₅).trans U₆).trans U₇).trans U₈).trans U₉).trans U₁₀, ?_,
    lt₁₀, by rw [ss, smm]⟩
  show wordsVal _ _ _ _ = _
  rw [sv_unch U₁₀ RR (by decide), sv_unch U₉ RR (by decide), sv_unch U₈ RR (by decide),
    sv_unch U₇ RR (by decide), sv_unch U₆ RR (by decide), sv_unch U₅ RR (by decide), sv_unch U₄ RR (by decide)]
  show sv base s₃ RR = _
  rw [k13 RR (by simp), rr₁]

/-! ## The end -/

/-- The flag `&=` the mask of the number at slot `i` being nonzero. -/
theorem nzFlag_ok {i : Nat} (hi : i < 44) {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block (Cfg.nonzeroFlag p256 i)) s fun s' =>
      Rest [.t0, .t3, .t4, .a7] s s' ∧ Outside base FL 8 s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&& maskOf (!decide (sv base s i = 0)) := by
  obtain ⟨a8, a2, -⟩ := sl_lt hi
  rw [Cfg.nonzeroFlag, show p256.n = 4 from rfl]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (zeroMask_ok hw (n := 4) (a := p256.sl i) a8 a2) fun s₁ ⟨r₁, m₁, g₁⟩ => ?_)
  rw [List.singleton_append]
  refine WP.cons (exec_logicImm (by decide)) ?_
  have r₁' := r₁.trans ((Upd.write s₁ .a7 (s₁.gpr .a7 ^^^ BitVec.ofInt 64 (-1))).rest (ws := [.t3, .t4, .a7])
    (by decide))
  refine WP.mono (andFlag_ok (hw.of_rest r₁')) fun s₂ ⟨f₂, r₂, O₂⟩ => ⟨(r₁'.mono (by decide)).trans
    (r₂.mono (by decide)), by
      have : Outside base FL 8 s.mem (s₁.write .a7 (s₁.gpr .a7 ^^^ BitVec.ofInt 64 (-1))).mem := by
        show Outside base FL 8 s.mem s₁.mem; rw [m₁]; exact Outside.refl _ _ _ _
      exact this.trans O₂, ?_⟩
  rw [f₂]
  simp only [State.write, ↓reduceIte]
  rw [m₁, g₁, not_mask]

/-- `finish`: the masks of `r ≠ 0` and `s ≠ 0` into the flag, `r ‖ s` (or
zeros) to `out` under it, the flag's low bit to `a0`, and the saved
registers restored. -/
theorem finish_ok {s : State} {base out : Addr} (hw : WsReg s base) (h2 : s.gpr .s2 = out)
    (hfit : out.toNat + 64 ≤ 2 ^ 64)
    (hout : ∀ i < 64, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hdis : (⟨out, 64⟩ : Region).Disjoint ⟨base, 8192⟩)
    {c : Bool} (hF : word s.mem base FL = maskOf c) :
    WP isa (.block (Cfg.finish p256)) s fun s' =>
      s'.gpr .a0 = (if (c && !decide (sv base s RR = 0)) && !decide (sv base s SS = 0) then 1 else 0) ∧
      bytesAt s'.mem out 64 =
        toBytes 32 (if (c && !decide (sv base s RR = 0)) && !decide (sv base s SS = 0) then sv base s RR else 0) ++
          toBytes 32 (if (c && !decide (sv base s RR = 0)) && !decide (sv base s SS = 0) then sv base s SS else 0) ∧
      s'.gpr .s0 = word s.mem base 0 ∧ s'.gpr .s1 = word s.mem base 8 ∧ s'.gpr .s2 = word s.mem base 16 ∧
      s'.gpr .ra = word s.mem base 24 ∧ s'.gpr .s3 = word s.mem base 32 ∧
      (∀ r ∈ preserved, r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp := by
  rw [Cfg.finish, retCode, restoreCode, show p256.n = 4 from rfl, show 8 * 4 = 32 from rfl]
  simp only [List.append_assoc]
  -- The checks.
  refine WP.block_append (WP.mono (nzFlag_ok (i := RR) (by decide) hw) fun s₁ ⟨r₁, O₁, f₁⟩ => ?_)
  have hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono (nzFlag_ok (i := SS) (by decide) hw₁) fun s₂ ⟨r₂, O₂, f₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  rw [List.singleton_append]
  refine ld_ws hw₂ (d := p256.sl FLAG) (by decide) (by decide) fun s₃ u₃ => ?_
  have hw₃ := hw₂.of_kp (Kp.of_upd u₃)
  have ss₁ : sv base s₁ SS = sv base s SS := by
    show wordsVal _ _ _ _ = _; rw [O₁.wordsVal (by rw [sl_eq, FL]; decide) (by decide)]
  generalize hB : ((c && !decide (sv base s RR = 0)) && !decide (sv base s SS = 0)) = B
  have hb : word s₂.mem base FL = maskOf B := by
    rw [f₂, f₁, hF, ss₁, maskOf_and, maskOf_and, hB]
  have a₃ : s₃.gpr .a7 = maskOf B := by rw [u₃.gpr, sl_FLAG]; exact hb
  have wv₃ : ∀ i, i < 44 → i ≠ FLAG → wordsVal s₃.mem base (p256.sl i) 4 = sv base s i := fun i hi hf => by
    rw [u₃.mem, O₂.wordsVal (by rw [sl_eq, FL]; omega) (by rw [sl_eq]; omega),
      O₁.wordsVal (by rw [sl_eq, FL]; omega) (by rw [sl_eq]; omega)]
  have q₃ : s₃.gpr .s2 = out := by
    rw [u₃.other _ (by decide), r₂.gpr _ (by decide), r₁.gpr _ (by decide), h2]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, r₂.wr, r₁.wr]
  have sp' : ∀ {off k : Nat}, off + k ≤ 64 → ∀ i < k,
      ¬ (⟨base, 8192⟩ : Region).Contains (out + BitVec.ofNat 64 off + BitVec.ofNat 64 i) 1 :=
    fun hk => sep_at' hdis hfit hk
  -- `r` and `s` under the mask.
  refine WP.block_append (WP.mono (storeNum_ok _ 4 hw₃ a₃ (q := .s2) (a := p256.sl RR) (off := 0) (by decide)
    (by decide) (by decide) (by decide)
    (fun i hi => by rw [q₃, wr₃]; exact hout (0 + i) (by omega))
    (fun i hi => by rw [q₃]; exact out_of_disj hdis hfit (by omega))) fun s₄ ⟨r₄, m₄⟩ => ?_)
  have hw₄ := hw₃.of_rest r₄
  have q₄ : s₄.gpr .s2 = out := by rw [r₄.gpr _ (by decide), q₃]
  have a₄ : s₄.gpr .a7 = maskOf B := by rw [r₄.gpr _ (by decide), a₃]
  rw [q₃, wv₃ RR (by decide) (by decide)] at m₄
  have U₄ : Unch base [(8192, 2 ^ 64)] s₃.mem s₄.mem := by
    rw [m₄]; exact writeBytes_unch _ fun i hi => sp' (off := 0) (k := 32) (by decide) i
      (by simpa [VG.Proof.Weierstrass.length_toBytes] using hi)
  refine WP.block_append (WP.mono (storeNum_ok _ 4 hw₄ a₄ (q := .s2) (a := p256.sl SS) (off := 32) (by decide)
    (by decide) (by decide) (by decide)
    (fun i hi => by rw [q₄, r₄.wr, wr₃]; exact hout (32 + i) (by omega))
    (fun i hi => by rw [q₄]; exact out_of_disj hdis hfit (by omega))) fun s₅ ⟨r₅, m₅⟩ => ?_)
  have hw₅ := hw₄.of_rest r₅
  have ss₄ : wordsVal s₄.mem base (p256.sl SS) 4 = sv base s SS := by
    rw [U₄.wordsVal (by intro w hw; simp only [List.mem_singleton] at hw; subst hw; left; decide) (by decide)]
    exact wv₃ SS (by decide) (by decide)
  rw [q₄, ss₄] at m₅
  have U₅ : Unch base [(8192, 2 ^ 64)] s₄.mem s₅.mem := by
    rw [m₅]; exact writeBytes_unch _ fun i hi => sp' (off := 32) (k := 32) (by decide) i
      (by simpa [VG.Proof.Weierstrass.length_toBytes] using hi)
  have wd : ∀ d, d + 8 ≤ FL ∨ FL + 8 ≤ d → d + 8 ≤ 2048 → word s₅.mem base d = word s.mem base d := fun d h hd => by
    rw [U₅.word (by simp; omega) (by omega), U₄.word (by simp; omega) (by omega), u₃.mem, O₂.word h (by omega),
      O₁.word h (by omega)]
  have fl₅ : word s₅.mem base FL = maskOf B := by
    rw [U₅.word (by decide) (by decide), U₄.word (by decide) (by decide), u₃.mem, hb]
  -- The bytes.
  have hX := VG.Proof.Weierstrass.length_toBytes 32 (if B = true then sv base s RR else 0)
  have hY := VG.Proof.Weierstrass.length_toBytes 32 (if B = true then sv base s SS else 0)
  have bytes₅ : bytesAt s₅.mem out 64 =
      toBytes 32 (if B then sv base s RR else 0) ++ toBytes 32 (if B then sv base s SS else 0) := by
    have e1 := VG.WriteBytes.writeBytes_append s₃.mem out (toBytes 32 (if B then sv base s RR else 0))
      (toBytes 32 (if B then sv base s SS else 0)) (by rw [hX, hY]; decide)
    rw [hX] at e1
    rw [m₅, m₄, BitVec.add_zero, e1]
    have := bytesAt_writeBytes s₃.mem out
      (toBytes 32 (if B then sv base s RR else 0) ++ toBytes 32 (if B then sv base s SS else 0))
      (by simp only [List.length_append, hX, hY]; decide)
    simp only [List.length_append, hX, hY] at this
    rw [this]
  -- The return value and the restores.
  refine ld_ws hw₅ (d := p256.sl FLAG) (by decide) (by decide) fun s₉ u₉ => ?_
  refine WP.cons (exec_logicImm (by decide)) ?_
  have u₉' := Upd.write s₉ .a0 (s₉.gpr .a0 &&& BitVec.ofInt 64 1)
  have hw₉ := (hw₅.of_kp (Kp.of_upd u₉)).of_kp (Kp.of_upd u₉')
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
  have M₄ : t₄.mem = s₅.mem := by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem, u₉'.mem, u₉.mem]
  have np : ∀ r ∈ preserved, r ∉ [Reg.t0, .t1, .t3, .t4, .a7, .a0, .ra] := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide),
      v₁.other _ (by decide), u₉'.gpr, u₉.gpr, sl_FLAG, fl₅, and_one]
  · rw [v₅.mem, M₄]; exact bytes₅
  · rw [v₅.gpr, M₄, wd 0 (by decide) (by decide)]
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
      u₉'.other _ hn.2.2.2.2.2.1, u₉.other _ hn.2.2.2.2.2.1, r₅.gpr _ (by simp [hn.1, hn.2.1]),
      r₄.gpr _ (by simp [hn.1, hn.2.1]), u₃.other _ hn.2.2.2.2.1,
      r₂.gpr _ (by simp [hn.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1]),
      r₁.gpr _ (by simp [hn.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1])]
  · rw [v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, u₉'.sp, u₉.sp, r₅.sp, r₄.sp, u₃.sp, r₂.sp, r₁.sp]

/-! ## The function -/

theorem hash_eq (m : Mem) (q : Addr) : hashToInt W (bytesAt m q 32) = ofBytes (bytesAt m q 32) := by
  have hn : Spec.Ecdsa.nBits W = 256 := by decide
  simp only [hashToInt, VG.Proof.Weierstrass.length_bytesAt, hn]
  rfl

theorem signWith_none {C : Curve} {d e k : Nat} (h : ¬ (1 ≤ k ∧ k < C.n)) : Spec.Ecdsa.signWith C d e k = none := by
  unfold Spec.Ecdsa.signWith
  rw [ite_eq_right_iff.mpr]
  intro h'; exact absurd ⟨h'.2.2.1, h'.2.2.2⟩ h

/-- `vg_ecdsa_p256_sign` by register. -/
theorem sign_ok (hL : VG.Proof.Weierstrass.Law W) {s : State} (hs : signRVC.pre s) :
    WP isa signP256 s fun s' => abiPreserved s s' ∧ signRV.post s s' := by
  obtain ⟨hs₀, hk⟩ := hs
  have hs' := hs₀
  obtain ⟨hrd, hwr, hod, hdd, hed, hkd, hfo, hfd, hfe, hfk, hfs, hal⟩ := hs'
  simp only [stripConsts_gpr, stripConsts_wr] at hrd hwr hod hdd hed hkd hfo hfd hfe hfk hfs hal
  have hp0 : 0 < W.p := by decide
  rw [signP256, Cfg.sign, Cfg.signWith, Cfg.back]
  refine WP.seq (Comb.wp_syms_frame (WP.mono (setupS_ok hs₀) fun s₁ S sy₁ F₁ => ?_))
  generalize hb : s.gpr .a4 = base at S hwr hod hdd hed hkd hfs hal
  have hT₁ : Comb.TabAt base s₁ :=
    (Comb.tabAt_of_consts hk (by rw [hwr]; simp)).of_frame sy₁ S.rd F₁ (Comb.tab_wr_of_consts hk)
  -- `k`'s range, `[k]G` and `x`.
  refine WP.seq (WP.mono (Comb.tailG_ok hL S.ws S.s3 S.tc S.rx S.ry hT₁)
    fun s₂ ⟨Kc₂, U₂, f₂, rep₂, xolt, xoeq, acclt, acceq⟩ => ?_)
  have hw₂ := S.ws.of_kc Kc₂
  have e₂ : ∀ i ∈ [ZERO, ONE, K, DD, EE, R2N, ONEN, EXPN], sv base s₂ i = sv base s₁ i := fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact sv_unch U₂ _ (by decide)
  have hbk : BackPre base s₂ (ofBytes (bytesAt s.mem (s.gpr .a3) 32)) (ofBytes (bytesAt s.mem (s.gpr .a1) 32))
      (ofBytes (bytesAt s.mem (s.gpr .a2) 32)) (sv base s₂ XO) :=
    ⟨hw₂, rfl, xolt, (e₂ ZERO (by simp)).trans S.tc.zero, (e₂ ONE (by simp)).trans S.tc.one,
      (e₂ K (by simp)).trans S.k, (e₂ DD (by simp)).trans S.d, (e₂ EE (by simp)).trans S.e,
      (e₂ R2N (by simp)).trans S.r2n, (e₂ ONEN (by simp)).trans S.onen, (e₂ EXPN (by simp)).trans S.expn⟩
  -- `r` and `s`.
  refine WP.seq (WP.mono (nback_ok hbk) fun s₃ ⟨Kc₃, U₃, rr₃, sslt₃, ss₃⟩ => ?_)
  have hw₃ := hw₂.of_kc Kc₃
  have fl₃ : word s₃.mem base FL = maskOf (((((true && decide (ofBytes (bytesAt s.mem (s.gpr .a1) 32) < W.n)) &&
      !decide (ofBytes (bytesAt s.mem (s.gpr .a1) 32) = 0)) &&
      decide (ofBytes (bytesAt s.mem (s.gpr .a3) 32) < W.n)) && !decide (ofBytes (bytesAt s.mem (s.gpr .a3) 32) = 0))) := by
    rw [U₃.word (by decide) (by decide), f₂, S.flag, S.k, maskOf_and, maskOf_and]
  have h2₃ : s₃.gpr .s2 = s.gpr .a0 := by
    rw [Kc₃.gpr _ (by decide) (by decide), Kc₂.gpr _ (by decide) (by decide), S.s2]
  have wr₃ : s₃.wr = s.wr := by rw [Kc₃.wr, Kc₂.wr, S.wr]
  refine WP.mono (finish_ok hw₃ h2₃ hfo (fun i hi => by
      rw [wr₃, hwr]
      exact ⟨_, List.mem_cons_self .., Offset.contains_base (s.gpr .a0) (d := i) (n := 1) (k := 64) (by omega)
        (by omega)⟩) hod fl₃)
    fun s' ⟨a0', bytes', s0', s1', s2', ra', s3', regs', sp'⟩ => ?_
  -- The registers.
  have U₂₃ := U₂.trans U₃
  refine ⟨⟨fun r hr => ?_, by rw [sp', Kc₃.sp, Kc₂.sp, S.sp], by rw [ra', U₂₃.word (by decide) (by decide), S.sv3]⟩,
    ?_⟩
  · by_cases h0 : r = .s0
    · subst h0; rw [s0', U₂₃.word (by decide) (by decide), S.sv0]
    by_cases h1 : r = .s1
    · subst h1; rw [s1', U₂₃.word (by decide) (by decide), S.sv1]
    by_cases h2' : r = .s2
    · subst h2'; rw [s2', U₂₃.word (by decide) (by decide), S.sv2]
    by_cases h3' : r = .s3
    · subst h3'; rw [s3', U₂₃.word (by decide) (by decide), S.sv4]
    rw [regs' r hr h0 h1 h2' h3', Kc₃.gpr r hr h1, Kc₂.gpr r hr h1, S.regs r h0 h2' h3' hr]
  -- The specification.
  rw [rr₃] at a0' bytes'
  generalize hD : ofBytes (bytesAt s.mem (s.gpr .a1) 32) = D at a0' bytes' fl₃ ss₃ hbk
  generalize hKv : ofBytes (bytesAt s.mem (s.gpr .a3) 32) = Kv at a0' bytes' fl₃ ss₃ hbk
  generalize hE : ofBytes (bytesAt s.mem (s.gpr .a2) 32) = E at ss₃ hbk
  have hsg : sg s.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3) = Spec.Ecdsa.signWith W D E Kv := by
    rw [← hD, ← hE, ← hKv, sg, hash_eq]
  unfold signRV
  simp only
  rw [hsg]
  have z64 : toBytes 32 0 ++ toBytes 32 0 = List.replicate 64 0 := by decide
  have hx := sv base s₂ XO
  by_cases hk : 1 ≤ Kv ∧ Kv < W.n
  · have hk₁ : sv base s₁ K = Kv := by rw [S.k, hKv]
    obtain ⟨hR, -, -, -⟩ := rep₂ (by rw [hk₁]; exact hk.1) (by rw [hk₁]; exact hk.2)
    have eG : Point.affine (toM W.p (2 ^ 256) (sv base s₁ RX)) (toM W.p (2 ^ 256) (sv base s₁ RY)) =
        Spec.Weierstrass.G W := by
      rw [S.rx, S.ry, toM_mont unit, toM_mont unit]; rfl
    rw [eG, hk₁] at hR
    have hsig := VG.Proof.Ecdsa.signWith_eq hL (d := D) (e := E) hR xolt xoeq sslt₃ ss₃
    rw [hsig]
    have hkn : decide (Kv < W.n) = true := decide_eq_true hk.2
    have hk0 : decide (Kv = 0) = false := decide_eq_false (by omega)
    rw [hkn, hk0] at a0' bytes'
    by_cases hc : 1 ≤ D ∧ D < W.n ∧ 1 ≤ Kv ∧ Kv < W.n ∧ sv base s₂ XO % W.n ≠ 0 ∧ sv base s₃ SS ≠ 0
    · rw [ite_eq_left hc]
      have hB : ((((((true && decide (D < W.n)) && !decide (D = 0)) && true) && !false) &&
          !decide (sv base s₂ XO % W.n = 0)) && !decide (sv base s₃ SS = 0)) = true := by
        simp only [Bool.and_true, Bool.true_and, Bool.not_false, Bool.and_eq_true, Bool.not_eq_true',
          decide_eq_true_eq, decide_eq_false_iff_not]
        exact ⟨⟨⟨hc.2.1, by omega⟩, hc.2.2.2.2.1⟩, hc.2.2.2.2.2⟩
      rw [hB] at a0' bytes'
      exact ⟨by rw [a0']; rfl, by rw [bytes']; rfl⟩
    · rw [ite_eq_right hc]
      have hB : ((((((true && decide (D < W.n)) && !decide (D = 0)) && true) && !false) &&
          !decide (sv base s₂ XO % W.n = 0)) && !decide (sv base s₃ SS = 0)) = false := by
        rw [Bool.eq_false_iff]
        intro hB
        simp only [Bool.and_true, Bool.true_and, Bool.not_false, Bool.and_eq_true, Bool.not_eq_true',
          decide_eq_true_eq, decide_eq_false_iff_not] at hB
        exact hc ⟨by omega, hB.1.1.1, hk.1, hk.2, hB.1.2, hB.2⟩
      rw [hB] at a0' bytes'
      exact ⟨by rw [a0']; rfl, bytes'.trans z64⟩
  · rw [signWith_none hk]
    have hB : ((((((true && decide (D < W.n)) && !decide (D = 0)) && decide (Kv < W.n)) &&
        !decide (Kv = 0)) && !decide (sv base s₂ XO % W.n = 0)) && !decide (sv base s₃ SS = 0)) = false := by
      by_cases hn : Kv < W.n
      · have : Kv = 0 := by omega
        simp [this]
      · simp [hn]
    rw [hB] at a0' bytes'
    exact ⟨by rw [a0']; rfl, bytes'.trans z64⟩

theorem sign_rv (hL : VG.Proof.Weierstrass.Law W) (s : State) (hs : signRVC.pre s) :
    ∃ t s', Exec isa signP256 s t s' ∧ abiPreserved s s' ∧ signRVC.post s s' := by
  obtain ⟨t, s', he, h⟩ := sign_ok hL hs
  exact ⟨t, s', he, h⟩

end VG.Proof.Ecdsa.RISCV64.P256
