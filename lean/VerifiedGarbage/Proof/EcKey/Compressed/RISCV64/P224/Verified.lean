module

public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Spec.EcKey.P224
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P224.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Weierstrass.Words
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
meta import VerifiedGarbage.Proof.Framework.RISCV64.Consts
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Spec.EcKey.P224
meta import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P224.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Weierstrass.Words
public import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.MainAll
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.Exchange
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.P224.RISCV64
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
import VerifiedGarbage.Proof.EcKey.Compressed.Decode
public import VerifiedGarbage.Impl.EcKey.Compressed.Root
public import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P224.Root
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub
import VerifiedGarbage.Proof.Weierstrass.Sqrt
import VerifiedGarbage.Proof.P224.SqrtTable
import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.CheckLit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.MainAll
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.Exchange
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Impl.EcKey.Compressed.P224.RISCV64
meta import VerifiedGarbage.Spec.EcKey.Compressed.Contract
meta import VerifiedGarbage.Proof.EcKey.Compressed.Decode
meta import VerifiedGarbage.Impl.EcKey.Compressed.Root
meta import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P224.Root
meta import VerifiedGarbage.Proof.Weierstrass.Sqrt
meta import VerifiedGarbage.Proof.P224.SqrtTable
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.CheckLit
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
meta import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub

/-! ### `EcKey.Compressed.RISCV64.P224.Main`, which only this module used -/

section

/-!
# P-224's point compression and decompression on RISC-V: correctness

`vg_ec_p224_compress_public_key` meets its contract by register (`compRV`,
`compress_ok`), by the proof for every curve
(`Proof/EcKey/Compressed/RISCV64/MainAll.lean`) over P-224's kit of ECDH.
`vg_ec_p224_decompress_public_key` (`DPre`, `DPostC`, `decompress_ok`) shares
with the other curves `rhs`, the root's checks and the end (`rhs_ok`,
`root_ok`, `dfin_ok`, that module's too); its setup and its root, by a table
as `p ≡ 1 (mod 4)`, are its own.
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.RISCV64.P224

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg VG.Impl.EcKey.Compressed.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.P224
open VG.Proof.Ecdh.RISCV64.P224
open VG.Proof.Ecdh.RISCV64 (Kit)
open VG.Impl.EcKey.Compressed (q224 root224 tbl224)
open VG.Proof.X25519.RISCV64 (Rest wp_and)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_nil writeBytes_append)

/-- `vg_ec_p224_compress_public_key(out = a0, public = a1, scratch = a2)`, by
register. -/
def compRV : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 29⟩
    let pk : Region := ⟨s.gpr .a1, 57⟩
    let ws : Region := ⟨s.gpr .a2, 8192⟩
    s.rd = [pk] ∧ s.wr = [out, ws] ∧ pk.Disjoint out ∧ pk.Disjoint ws ∧ out.Disjoint ws ∧
      (s.gpr .a0).toNat + 29 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8192 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat % 8 = 0
  post s s' :=
    match Spec.EcKey.compressPublicKey Spec.P224.curve (bytesAt s.mem (s.gpr .a1) 57) with
    | some bs => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) 29 = bs
    | none => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) 29 = List.replicate 29 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2

/-- The contract's postcondition is the kit's. -/
theorem compPost_eq : compRV.post = kit.compPost := by kernel_rfl

/-- `vg_ec_p224_compress_public_key` by register. -/
theorem compress_ok {s : State} (hs : compRV.pre s) :
    WP isa compressP224 s fun s' => abiPreserved s s' ∧ compRV.post s s' :=
  by rw [compPost_eq]; exact kit.compress_ok hs

/-! ## Decompression -/

/-- `tagMask q`: `a7` is the mask of the byte at `[q]` being `02` or `03`. -/
theorem tagMask_ok {s : State} {q : Reg}
    (hin : InRegions (s.rd ++ s.wr) (s.gpr q) 1) :
    WP isa (.block (Cfg.tagMask q)) s fun s' =>
      Rest [.t0, .t1, .a7] s s' ∧ s'.mem = s.mem ∧ s'.gpr .a7 = maskOf (decide (s.mem (s.gpr q) = 2 ∨
        s.mem (s.gpr q) = 3)) :=
  Kit.tagMask_ok hin

/-- `vg_ec_p224_decompress_public_key(out = a0, public = a1, scratch = a2)`'s
precondition, by register. -/
def DPre (s : State) : Prop :=
  let out : Region := ⟨s.gpr .a0, 57⟩
  let pk : Region := ⟨s.gpr .a1, 29⟩
  let ws : Region := ⟨s.gpr .a2, 8192⟩
  s.rd = [pk, ⟨s.syms sqrtSym, 12288⟩] ∧ s.wr = [out, ws] ∧ pk.Disjoint out ∧ pk.Disjoint ws ∧ out.Disjoint ws ∧
    (s.gpr .a0).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 29 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8192 ≤ 2 ^ 64 ∧
    (s.gpr .a2).toNat % 8 = 0 ∧ TabOk (s.gpr .a2) (s.syms sqrtSym) s

/-- What decompression's setup leaves. -/
structure DPost (s s' : State) : Prop where
  ws : WsReg s' (s.gpr .a2)
  s2 : s'.gpr .s2 = s.gpr .a0
  s3 : s'.gpr .s3 = s.gpr .a2
  regs : ∀ x, x ≠ .s0 → x ≠ .s2 → x ≠ .s3 → x ∈ preserved → s'.gpr x = s.gpr x
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  sv0 : word s'.mem (s.gpr .a2) 0 = s.gpr .s0
  sv1 : word s'.mem (s.gpr .a2) 8 = s.gpr .s1
  sv2 : word s'.mem (s.gpr .a2) 16 = s.gpr .s2
  sv3 : word s'.mem (s.gpr .a2) 24 = s.gpr .ra
  sv4 : word s'.mem (s.gpr .a2) 32 = s.gpr .s3
  x : sv (s.gpr .a2) s' CX = ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 28)
  par : word s'.mem (s.gpr .a2) (p224.sl PAR) = (s.mem (s.gpr .a1)).setWidth 64 &&& BitVec.ofInt 64 1
  flag : word s'.mem (s.gpr .a2) FL = maskOf (decide (s.mem (s.gpr .a1) = 2 ∨ s.mem (s.gpr .a1) = 3) &&
    decide (ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 28) < W.p))
  consts : ∀ e ∈ consts p224, sv (s.gpr .a2) s' e.1 = e.2
  far : ∀ x, 8192 ≤ ofs (s.gpr .a2) x → s'.mem x = s.mem x

theorem dsetup_ok {s : State} (hs : DPre s) :
    WP isa (.block (saveCode .a2 ++ loadNum4 3 (p224.sl CX) .a1 1 ++ Cfg.parCode p224 .a1 ++
      Cfg.tagMask .a1 ++ sdAt .a7 wb (p224.sl FLAG) ++ constCode p224 ++ ltMask 4 (p224.sl CX) (p224.sl MP) ++
      andFlag p224)) s fun s' => DPost s s' := by
  obtain ⟨hrd, hwr, hpo, hpw, how, hfo, hfp, hfs, hal, -⟩ := hs
  generalize hb : s.gpr .a2 = base at hwr hpw how hfs hal
  obtain hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (save_ok hb hwr' hfs hal)
    fun s₁ ⟨hw₁, h3₁, o₁, g₁, rd₁, wr₁, sp₁, U₁, w0, w1, w2, w3, w4⟩ => ?_)
  obtain a1 : s₁.gpr .a1 = s.gpr .a1 := g₁ _ (by decide) (by decide) (by decide)
  obtain rdp : (⟨s.gpr .a1, 29⟩ : Region) ∈ s₁.rd ++ s₁.wr := by rw [rd₁, wr₁, hrd]; simp
  -- `x`.
  refine WP.block_append (WP.mono (loadNum4_ok 3 hw₁ (o := p224.sl CX) (p := .a1) (off := 1) (by decide)
    (by decide) (by decide) (by decide) (by rw [a1]; exact in_rd4 rdp (by omega_using []))
    (fun j hj => by rw [a1]; exact in_rd8 rdp (by omega_using [hj]))
    (fun i hi => by rw [a1]; exact out_of_disj hpw hfp (by omega_using [hi]))) fun s₂ ⟨r₂, O₂, e₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  obtain a1₂ : s₂.gpr .a1 = s.gpr .a1 := by rw [r₂.gpr _ (by decide), a1]
  obtain in₂ : InRegions (s₂.rd ++ s₂.wr) (s.gpr .a1) 1 := by
    rw [r₂.rd, r₂.wr]
    have := Offset.contains_base (s.gpr .a1) (d := 0) (n := 1) (k := 29) (by decide) (by decide)
    exact ⟨_, rdp, by simpa using this⟩
  -- The first byte's low bit.
  rw [Cfg.parCode, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_lbu (off := 0) (by decide) (by rw [a1₂, BitVec.add_zero]) in₂ fun s₃ u₃ => ?_
  refine WP.cons (exec_logicImm (by decide)) ?_
  obtain u₃a := Upd.write s₃ .t0 (s₃.gpr .t0 &&& BitVec.ofInt 64 1)
  obtain hw₃ := (hw₂.of_kp (Kp.of_upd u₃)).of_kp (Kp.of_upd u₃a)
  refine sd_ws hw₃ (d := p224.sl PAR) (by decide) (by decide) fun s₄ u₄ => ?_
  obtain hw₄ := hw₃.of_kp (Kp.of_mupd u₄)
  obtain par₄ : word s₄.mem base (p224.sl PAR) = (s₂.mem (s.gpr .a1)).setWidth 64 &&& BitVec.ofInt 64 1 := by
    rw [u₄.mem, word_writeW_self, u₃a.gpr, u₃.gpr]
  obtain O₄ : Outside base (p224.sl PAR) 8 s₂.mem s₄.mem := by
    rw [u₄.mem, u₃a.mem, u₃.mem]; exact writeW_outside _ _ _ (by decide)
  obtain a1₄ : s₄.gpr .a1 = s.gpr .a1 := by
    rw [u₄.gpr, u₃a.other _ (by decide), u₃.other _ (by decide), a1₂]
  -- The tag's mask.
  refine WP.block_append (WP.mono (tagMask_ok (s := s₄) (q := .a1) (by
      rw [a1₄, u₄.rd, u₄.wr, u₃a.rd, u₃a.wr, u₃.rd, u₃.wr]; exact in₂))
    fun s₅ ⟨r₅, m₅, g₅⟩ => ?_)
  obtain hw₅ := hw₄.of_rest r₅
  refine sdAt_ws hw₅ (by decide) (d := p224.sl FLAG) (by decide) (by decide) fun s₆ u₆ => ?_
  obtain hw₆ := hw₅.of_kp (Kp.of_mupd u₆)
  -- The constants and the root's exponent.
  rw [constCode_eq]
  refine WP.block_append (WP.mono (consts_ok _ hw₆ consts_slots consts_nodup) fun s₇ ⟨r₇, U₇, e₇⟩ => ?_)
  obtain hw₈ := hw₆.of_rest r₇
  -- `x < p`.
  refine WP.block_append (WP.mono (ltMask_ok hw₈ (n := 4) (a := p224.sl CX) (m := p224.sl MP) (by decide)
    (by decide) (by decide) (by decide)) fun s₉ ⟨r₉, m₉, g₉⟩ => ?_)
  obtain hw₉ := hw₈.of_rest r₉
  refine WP.mono (andFlag_ok hw₉) fun s₁₀ ⟨f₁₀, r₁₀, O₁₀⟩ => ?_
  -- What changed.
  obtain O₆ : Unch base [(FL, 8)] s₅.mem s₆.mem := by
    rw [u₆.mem]; exact (writeW_outside _ _ _ (by decide)).unch
  obtain U₈₁₀ : Unch base [(FL, 8)] s₇.mem s₁₀.mem := by rw [← m₉]; exact O₁₀.unch
  obtain U₆₁₀ := U₇.trans U₈₁₀
  obtain U₄₁₀ : Unch base _ s₄.mem s₁₀.mem := (by rw [← m₅]; exact O₆ : Unch base [(FL, 8)] s₄.mem s₆.mem).trans U₆₁₀
  obtain U₂₁₀ := O₄.unch.trans U₄₁₀
  obtain U₁₁₀ := O₂.unch.trans U₂₁₀
  obtain hp1 : ∀ x ∈ preserved, x ∉ [Reg.t0, .t1, .a7] := by decide
  obtain hp2 : ∀ x ∈ preserved, x ∉ [Reg.t0, .t1] := by decide
  obtain hp3 : ∀ x ∈ preserved, x ∉ [Reg.t3, .t4, .t5, .t6, .a4, .a7] := by decide
  obtain hp4 : ∀ x ∈ preserved, x ∉ [Reg.t0] := by decide
  obtain hp5 : ∀ x ∈ preserved, x ≠ .t0 := by decide
  obtain gp : ∀ x ∈ preserved, s₁₀.gpr x = s₁.gpr x := fun x hx => by
    rw [r₁₀.gpr _ (hp4 x hx), r₉.gpr _ (hp3 x hx), r₇.gpr _ (hp2 x hx), u₆.gpr,
      r₅.gpr _ (hp1 x hx), u₄.gpr, u₃a.other _ (hp5 x hx), u₃.other _ (hp5 x hx), r₂.gpr _ (hp2 x hx)]
  obtain b₂ : s₂.mem (s.gpr .a1) = s.mem (s.gpr .a1) := by
    obtain h1 := bytesAt_unch (U₁.trans O₂.unch) (q := s.gpr .a1) (n := 1) (by decide)
      (by simpa using sep_at' hpw hfp (off := 0) (k := 1) (by omega_using []))
    simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h1
    simp only [BitVec.add_zero] at h1
    exact h1
  obtain x₂ : sv base s₂ CX = ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 28) := by
    show wordsVal _ _ _ _ = _
    rw [e₂, a1, bytesAt_unch U₁ (by decide) (sep_at' hpw hfp (off := 1) (k := 28) (by omega_using []))]
  obtain cs₇ : ∀ e ∈ consts p224, sv base s₇ e.1 = e.2 := fun e he => by
    rw [e₇ e he, Nat.mod_eq_of_lt (consts_lt e he)]
  obtain hap : ∀ e ∈ consts p224, ∀ w ∈ [(FL, 8)], p224.sl e.1 + 32 ≤ w.1 ∨ w.1 + w.2 ≤ p224.sl e.1 := by decide
  obtain csl : ∀ e ∈ consts p224, e.1 < 100 := fun e he => by have := consts_slots e he; omega_using [this]
  subst hb
  refine ⟨hw₉.of_rest r₁₀, by rw [gp _ (by decide), o₁], by rw [gp _ (by decide), h3₁],
    fun x h0 h2 h3 hx => by rw [gp _ hx, g₁ _ h0 h2 h3], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r₁₀.rd, r₉.rd, r₇.rd, u₆.rd, r₅.rd, u₄.rd, u₃a.rd, u₃.rd, r₂.rd, rd₁]
  · rw [r₁₀.wr, r₉.wr, r₇.wr, u₆.wr, r₅.wr, u₄.wr, u₃a.wr, u₃.wr, r₂.wr, wr₁]
  · rw [r₁₀.sp, r₉.sp, r₇.sp, u₆.sp, r₅.sp, u₄.sp, u₃a.sp, u₃.sp, r₂.sp, sp₁]
  · rw [U₁₁₀.word (by decide) (by decide)]; exact w0
  · rw [U₁₁₀.word (by decide) (by decide)]; exact w1
  · rw [U₁₁₀.word (by decide) (by decide)]; exact w2
  · rw [U₁₁₀.word (by decide) (by decide)]; exact w3
  · rw [U₁₁₀.word (by decide) (by decide)]; exact w4
  · show wordsVal _ _ _ _ = _
    rw [sv_unch U₂₁₀ CX (by decide)]; exact x₂
  · rw [U₄₁₀.word (by decide) (by decide), par₄, b₂]
  · have b₄ : s₄.mem (s.gpr .a1) = s.mem (s.gpr .a1) := by
      obtain h1 := bytesAt_unch ((U₁.trans O₂.unch).trans O₄.unch) (q := s.gpr .a1) (n := 1) (by decide)
        (by simpa using sep_at' hpw hfp (off := 0) (k := 1) (by omega_using []))
      simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h1
      simp only [BitVec.add_zero] at h1
      exact h1
    obtain mp₈ : wordsVal s₇.mem (s.gpr .a2) (p224.sl MP) 4 = W.p := const_at cs₇ 0
    obtain cx₈ : wordsVal s₇.mem (s.gpr .a2) (p224.sl CX) 4 =
        ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 28) := by
      rw [sv_unch (O₄.unch.trans ((by rw [← m₅]; exact O₆ :
        Unch _ [(FL, 8)] s₄.mem s₆.mem).trans U₇)) CX (by decide)]; exact x₂
    rw [f₁₀, m₉, U₇.word (by decide) (by decide), u₆.mem, sl_FLAG,
      word_writeW_self, g₅, g₉, a1₄, b₄, mp₈, cx₈, maskOf_and]
  · intro e he
    show wordsVal _ _ _ _ = _
    rw [U₈₁₀.wordsVal (fun w hw => hap e he w hw) (by have := csl e he; rw [sl_eq]; omega_using [this])]
    exact cs₇ e he
  · intro x hx
    exact (U₁.trans U₁₁₀).far fun w hw => by
      have : w.1 + w.2 ≤ 8192 := (by decide : ∀ w ∈ _, w.1 + w.2 ≤ 8192) w hw
      omega_using [hx, this]

/-! ### `rhs = x³ + a x + b` -/

/-- `x R` to `CXM` and `rhs` (in Montgomery's form) to `RHS`. -/
theorem rhs_ok {s : State} {base : Addr} (hw : WsReg s base) (hr2 : sv base s R2P = 2 ^ 256 * 2 ^ 256 % W.p)
    (hap : sv base s AP = W.a * 2 ^ 256 % W.p) (hbp : sv base s BP = W.b * 2 ^ 256 % W.p) :
    WP isa (fprog p224Field (Cfg.rhsOps p224)) s fun s' =>
      Kp s s' ∧ Unch base ([(p224.sl CXM, 8 * 4), (own 4, 64 * 4)] ++
        (((Cfg.rhsOps p224).tail.map FOp.out).map (fun w => (w, 8 * 4)) ++ [(own 4, 64 * 4)])) s.mem s'.mem ∧
      sv base s' RHS < W.p ∧
      toM W.p (2 ^ 256) (sv base s' RHS) =
        Fin.ofNat W.p (sv base s CX) * Fin.ofNat W.p (sv base s CX) * Fin.ofNat W.p (sv base s CX) +
          Fin.ofNat W.p W.a * Fin.ofNat W.p (sv base s CX) + Fin.ofNat W.p W.b :=
  kit.rhs_ok hw hr2 hap hbp

/-! ### The root's checks -/

/-- `y²` and `y² - rhs` (in Montgomery's form), `y` out of it, and `p - y`. -/
theorem root_ok {s : State} {base : Addr} (hw : WsReg s base) (hacc : sv base s ACC < W.p)
    (hrhs : sv base s RHS < W.p) (hone : sv base s ONE = 1) (hzero : sv base s ZERO = 0) :
    WP isa (fprog p224Field (Cfg.rootOps p224)) s fun s' =>
      Kp s s' ∧ Unch base ([(p224.sl YSQ, 8 * 4), (own 4, 64 * 4)] ++ [(p224.sl DIF, 8 * 4), (own 4, 64 * 4)] ++
        [(p224.sl Y1, 8 * 4), (own 4, 64 * 4)] ++ [(p224.sl Y2, 8 * 4), (own 4, 64 * 4)]) s.mem s'.mem ∧
      sv base s' DIF < W.p ∧
      toM W.p (2 ^ 256) (sv base s' DIF) =
        toM W.p (2 ^ 256) (sv base s ACC) * toM W.p (2 ^ 256) (sv base s ACC) - toM W.p (2 ^ 256) (sv base s RHS) ∧
      sv base s' Y1 < W.p ∧ Fin.ofNat W.p (sv base s' Y1) = toM W.p (2 ^ 256) (sv base s ACC) ∧
      sv base s' Y2 = (W.p - sv base s' Y1) % W.p :=
  kit.root_ok hw hacc hrhs hone hzero

/-! ### The checks into the flag, the root's choice and the output -/

/-- The end: the masks of `y² = rhs` and of the chosen root's parity into the
flag, the root of the first byte's parity chosen, and the point (or zeros)
to `out`, the flag's low bit returned and the saved registers restored. -/
theorem dfin_ok {s : State} {base out : Addr} (hw : WsReg s base) (h2 : s.gpr .s2 = out)
    (hfit : out.toNat + 57 ≤ 2 ^ 64)
    (hout : ∀ i < 57, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hdis : (⟨out, 57⟩ : Region).Disjoint ⟨base, 8192⟩)
    {c : Bool} (hF : word s.mem base FL = maskOf c) {pr : Nat}
    (hpr : (word s.mem base (p224.sl PAR)).toNat % 2 = pr) :
    WP isa (.block (zeroMask p224.n (p224.sl DIF) ++ andFlag p224 ++ Cfg.parMask p224 Y1 ++
      sel p224.n (p224.sl YF) (p224.sl Y1) (p224.sl Y2) ++ Cfg.sameMask p224 YF ++ andFlag p224 ++
      ldAt .a7 wb (p224.sl FLAG) ++ pointOut224 CX YF)) s fun s' =>
      s'.gpr .a0 = (if (c && decide (sv base s DIF = 0)) &&
          decide ((if sv base s Y1 % 2 ≠ pr then sv base s Y2 else sv base s Y1) % 2 = pr) then 1 else 0) ∧
      bytesAt s'.mem out 57 = (if (c && decide (sv base s DIF = 0)) &&
          decide ((if sv base s Y1 % 2 ≠ pr then sv base s Y2 else sv base s Y1) % 2 = pr) then 4 else 0) ::
        (toBytes 28 (if (c && decide (sv base s DIF = 0)) &&
          decide ((if sv base s Y1 % 2 ≠ pr then sv base s Y2 else sv base s Y1) % 2 = pr) then sv base s CX else 0) ++
        toBytes 28 (if (c && decide (sv base s DIF = 0)) &&
          decide ((if sv base s Y1 % 2 ≠ pr then sv base s Y2 else sv base s Y1) % 2 = pr) then
            (if sv base s Y1 % 2 ≠ pr then sv base s Y2 else sv base s Y1) else 0)) ∧
      s'.gpr .s0 = word s.mem base 0 ∧ s'.gpr .s1 = word s.mem base 8 ∧ s'.gpr .s2 = word s.mem base 16 ∧
      s'.gpr .ra = word s.mem base 24 ∧ s'.gpr .s3 = word s.mem base 32 ∧
      (∀ r ∈ preserved, r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp :=
  kit.dfin_ok hw h2 hfit hout hdis hF hpr

/-! ### The square root by the table

`w = rhs^((q-1)/2)` by its chain (`chainPow_ok`), `r` and `t` (`tonOps`),
`t`'s powers (`schain_ok`) and the table's last row (`gload_ok`): the front of
the function (`front_ok`), which leaves the digits' state (`FPost`); then the
digits and the root (`Proof/EcKey/Compressed/RISCV64/P224/Root.lean`), and the
checks and the output (`tail_ok`). -/

theorem wLay : ChainLayR wChain 4 where
  n := rfl
  k1 := by decide
  acc := by decide
  base := by decide
  tbl := by decide
  short := by decide
  acc8 := by decide
  base8 := by decide
  tbl8 := by decide
  acc_base := by decide
  acc_tbl := by decide
  base_tbl := by decide

/-- The chain is `(q-1)/2`'s. -/
theorem wChain_ok : ChainOkR wChain ((q224 - 1) / 2) := ChainOkR.of_check (by lit_decide)

/-- The slots of `r = w rhs` and `t = w r`. -/
abbrev tonSlots : List Nat := [p224.sl TR, p224.sl ACC, p224.sl RHS, p224.sl (SS 0)]

theorem tonLay : Lay p224.MP' (own 4) (· ∈ tonSlots) :=
  ⟨by decide, fun x y hx hy => (by decide : ∀ x ∈ tonSlots, ∀ y ∈ tonSlots,
      x ≠ y → x + 8 * p224.MP'.n ≤ y ∨ y + 8 * p224.MP'.n ≤ x) x hx y hy, by decide, by decide⟩

theorem ton_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps tonOps e (p224.sl TR) = e (p224.sl ACC) * e (p224.sl RHS) ∧
    runOps tonOps e (p224.sl (SS 0)) = e (p224.sl ACC) * (e (p224.sl ACC) * e (p224.sl RHS)) := by
  simp only [tonOps, runOps_cons, runOps_nil, FOp.run, Function.update_apply, sl_eq]
  simp only [TR, SS, ACC, RHS, T0, Nat.reduceMul, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
  exact ⟨trivial, trivial⟩

theorem pow16 (y : Fe W) : y * y * (y * y) * (y * y * (y * y)) * (y * y * (y * y) * (y * y * (y * y))) = y ^ 16 := by
  grind

/-- `s_(m+1) = s_m^16`. -/
theorem sq4_ok {s : State} {base : Addr} (hw : WsReg s base) {m : Nat} (hm : m < 23)
    (hlt : sv base s (SS m) < W.p) :
    WP isa (fprog p224Field (sq4 m)) s fun s' => Kp s s' ∧
      Unch base [(p224.sl (SS (m + 1)), 32), (own 4, 256)] s.mem s'.mem ∧ sv base s' (SS (m + 1)) < W.p ∧
      toM W.p (2 ^ 256) (sv base s' (SS (m + 1))) = toM W.p (2 ^ 256) (sv base s (SS m)) ^ 16 := by
  show WP isa (.seq (mulCall p224Field (p224.sl (SS (m + 1))) (p224.sl (SS m)) (p224.sl (SS m))) <|
    .seq (mulCall p224Field (p224.sl (SS (m + 1))) (p224.sl (SS (m + 1))) (p224.sl (SS (m + 1)))) <|
    .seq (mulCall p224Field (p224.sl (SS (m + 1))) (p224.sl (SS (m + 1))) (p224.sl (SS (m + 1))))
      (mulCall p224Field (p224.sl (SS (m + 1))) (p224.sl (SS (m + 1))) (p224.sl (SS (m + 1))))) s _
  obtain ho : ∀ i, i < 100 → p224.sl i + 8 * 4 ≤ 3840 := fun i hi => by rw [sl_eq]; omega_using [hi]
  obtain hb : ∀ i, i < 100 → p224.sl i < 4095 := fun i hi => by rw [sl_eq]; omega_using [hi]
  obtain hm1 : SS m < 100 := by simp only [SS]; omega_using [hm]
  obtain hm2 : SS (m + 1) < 100 := by simp only [SS]; omega_using [hm]
  refine WP.seq (WP.mono (mulCall_ok field_ok hw (ho _ hm2) (ho _ hm1) (ho _ hm1) (hb _ hm2) (hb _ hm1) (hb _ hm1)
    hlt) fun s₁ ⟨C₁, lt₁, e₁⟩ => ?_)
  obtain hw₁ := hw.of_kp C₁.kp
  refine WP.seq (WP.mono (mulCall_ok field_ok hw₁ (ho _ hm2) (ho _ hm2) (ho _ hm2) (hb _ hm2) (hb _ hm2) (hb _ hm2)
    lt₁) fun s₂ ⟨C₂, lt₂, e₂⟩ => ?_)
  obtain hw₂ := hw₁.of_kp C₂.kp
  refine WP.seq (WP.mono (mulCall_ok field_ok hw₂ (ho _ hm2) (ho _ hm2) (ho _ hm2) (hb _ hm2) (hb _ hm2) (hb _ hm2)
    lt₂) fun s₃ ⟨C₃, lt₃, e₃⟩ => ?_)
  obtain hw₃ := hw₂.of_kp C₃.kp
  refine WP.mono (mulCall_ok field_ok hw₃ (ho _ hm2) (ho _ hm2) (ho _ hm2) (hb _ hm2) (hb _ hm2) (hb _ hm2)
    lt₃) fun s₄ ⟨C₄, lt₄, e₄⟩ => ⟨C₁.kp.trans (C₂.kp.trans (C₃.kp.trans C₄.kp)), ?_, lt₄, ?_⟩
  · have U₁ : Unch base [(p224.sl (SS (m + 1)), 32), (own 4, 256)] s.mem s₁.mem := C₁.mem
    have U₂ : Unch base [(p224.sl (SS (m + 1)), 32), (own 4, 256)] s₁.mem s₂.mem := C₂.mem
    have U₃ : Unch base [(p224.sl (SS (m + 1)), 32), (own 4, 256)] s₂.mem s₃.mem := C₃.mem
    have U₄ : Unch base [(p224.sl (SS (m + 1)), 32), (own 4, 256)] s₃.mem s₄.mem := C₄.mem
    exact ((U₁.trans U₂).trans (U₃.trans U₄)).mono fun w hw => by
      simp only [List.mem_append] at hw; rcases hw with ((h | h) | (h | h)) <;> exact h
  · have v₁ : toM W.p (2 ^ 256) (sv base s₁ (SS (m + 1))) =
        toM W.p (2 ^ 256) (sv base s (SS m)) * toM W.p (2 ^ 256) (sv base s (SS m)) := toM_mul unit e₁
    obtain v₂ : toM W.p (2 ^ 256) (sv base s₂ (SS (m + 1))) =
        toM W.p (2 ^ 256) (sv base s₁ (SS (m + 1))) * toM W.p (2 ^ 256) (sv base s₁ (SS (m + 1))) := toM_mul unit e₂
    obtain v₃ : toM W.p (2 ^ 256) (sv base s₃ (SS (m + 1))) =
        toM W.p (2 ^ 256) (sv base s₂ (SS (m + 1))) * toM W.p (2 ^ 256) (sv base s₂ (SS (m + 1))) := toM_mul unit e₃
    obtain v₄ : toM W.p (2 ^ 256) (sv base s₄ (SS (m + 1))) =
        toM W.p (2 ^ 256) (sv base s₃ (SS (m + 1))) * toM W.p (2 ^ 256) (sv base s₃ (SS (m + 1))) := toM_mul unit e₄
    rw [v₄, v₃, v₂, v₁, pow16]

/-- `s_1 … s_m`, from `s_0 = t`. -/
theorem schain_ok {base : Addr} {t : Fe W} : ∀ m, m ≤ 23 → ∀ {s : State}, WsReg s base →
    sv base s (SS 0) < W.p → toM W.p (2 ^ 256) (sv base s (SS 0)) = t →
    WP isa (schain m) s fun s' => WsReg s' base ∧ Kp s s' ∧
      Unch base [(p224.sl (SS 1), 32 * 23), (own 4, 256)] s.mem s'.mem ∧
      ∀ i ≤ m, sv base s' (SS i) < W.p ∧ toM W.p (2 ^ 256) (sv base s' (SS i)) = Spec.Weierstrass.pow t (16 ^ i)
  | 0, _, s, hw, hlt, hv => WP.block_nil ⟨hw, Kp.refl _, Unch.refl _ _ _, fun i hi => by
      obtain rfl : i = 0 := by omega_using [hi]
      exact ⟨hlt, by rw [hv, VG.Proof.Weierstrass.pow_eq_npow, Nat.pow_zero, Lean.Grind.Semiring.pow_one]⟩⟩
  | m + 1, hm, s, hw, hlt, hv => by
    rw [schain]
    refine WP.seq (WP.mono (schain_ok m (by omega_using [hm]) hw hlt hv) fun s₁ ⟨hw₁, K₁, U₁, v₁⟩ => ?_)
    refine WP.mono (sq4_ok hw₁ (m := m) (by omega_using [hm]) (v₁ m (Nat.le_refl _)).1) fun s₂ ⟨K₂, U₂, lt₂, v₂⟩ =>
      ⟨hw₁.of_kp K₂, K₁.trans K₂, (U₁.trans U₂).cover ?_, fun i hi => ?_⟩
    · intro w hw
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with (rfl | rfl) | (rfl | rfl)
      · exact ⟨_, List.mem_cons_self .., Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
      · refine ⟨_, List.mem_cons_self .., ?_, ?_⟩ <;> simp only [sl_eq, SS] <;> omega_arith
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
    · by_cases he : i = m + 1
      · subst he
        refine ⟨lt₂, ?_⟩
        rw [v₂, (v₁ m (Nat.le_refl _)).2, VG.Proof.Weierstrass.pow_eq_npow, VG.Proof.Weierstrass.pow_eq_npow,
          VG.Proof.Weierstrass.pow_mul_exponents, Nat.pow_succ]
      · have e : sv base s₂ (SS i) = sv base s₁ (SS i) := sv_unch U₂ (SS i) (by
          intro w hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · simp only [sl_eq, SS]; omega_using [he]
          · left; show p224.sl (SS i) + 32 ≤ 3840; simp only [sl_eq, SS]; omega_using [hm, hi]) (by simp only [SS]; omega_using [hm, hi])
        rw [e]; exact v₁ i (by omega_using [hi, he])

/-- The entries `g^e`, `e < n`, from the row at `t0`. -/
theorem gcopies_ok {base T : Addr} : ∀ n, n ≤ 16 → ∀ {s : State}, WsReg s base → TabOk base T s →
    s.gpr .t0 = T + BitVec.ofNat 64 (512 * 23) →
    WP isa (.block (gcopies n)) s fun s' => Rest [.t3] s s' ∧ Unch base [(p224.sl (GS 0), 32 * n)] s.mem s'.mem ∧
      ∀ e < n, sv base s' (GS e) = montT 23 e
  | 0, _, _, _, _, _ => WP.block_nil ⟨Rest.refl _ _, Unch.refl _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn, s, hw, hT, h0 => by
    rw [gcopies]
    refine WP.block_append (WP.mono (gcopies_ok n (by omega_using [hn]) hw hT h0) fun s₁ ⟨r₁, U₁, v₁⟩ => ?_)
    obtain hT₁ := hT.of_unch r₁.rd (fun w hw => by
      rw [List.mem_singleton.mp hw]; show p224.sl (GS 0) + 32 * n ≤ 8192; rw [sl_eq]; simp only [GS]; omega_using [hn]) U₁
    refine WP.mono (entCopy_ok (hw.of_rest r₁) hT₁ (o := GS n) (q := 32 * n) (m := 23) (d := n) (by decide) (by omega_using [hn])
      (by omega_using [hn]) (by simp only [GS]; omega_using [hn]) (by
        rw [r₁.gpr _ (by decide), h0, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_using []))
      fun s₂ ⟨r₂, O₂, v₂⟩ => ⟨r₁.trans r₂, (U₁.trans O₂.unch).cover ?_, fun e he => ?_⟩
    · intro w hw
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      refine ⟨_, List.mem_cons_self .., ?_, ?_⟩ <;> rcases hw with rfl | rfl <;> simp only [sl_eq, GS] <;> omega_using []
    · by_cases h : e = n
      · subst h; exact v₂
      · rw [← v₁ e (by omega_using [he, h])]
        exact O₂.wordsVal (by have := slot_apart (i := GS e) (j := GS n) (by simp only [GS]; omega_using [h]); omega_using [this])
          (by simp only [sl_eq, GS]; omega_using [hn, he])

/-- `s4`–`s6` to the working space's bytes 40–63. -/
theorem sd_s4 {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block [.store .d .s4 .s0 40, .store .d .s5 .s0 48, .store .d .s6 .s0 56]) s fun s' =>
      Rest [] s s' ∧ s'.mem = ((s.mem.writeW (off base 40) (s.gpr .s4)).writeW (off base 48) (s.gpr .s5)).writeW
        (off base 56) (s.gpr .s6) := by
  refine sd_ws hw (by decide) (by decide) fun s₁ u₁ => ?_
  refine sd_ws (hw.of_kp (Kp.of_mupd u₁)) (by decide) (by decide) fun s₂ u₂ => ?_
  refine sd_ws ((hw.of_kp (Kp.of_mupd u₁)).of_kp (Kp.of_mupd u₂)) (by decide) (by decide) fun s₃ u₃ =>
    WP.block_nil ⟨(u₁.rest _).trans ((u₂.rest _).trans (u₃.rest _)), ?_⟩
  rw [u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr]

/-- `s4`–`s6` kept, the last row to `GS`, no digits yet. -/
theorem gload_ok {s : State} {base T : Addr} (hw : WsReg s base) (hT : TabOk base T s)
    (hsym : s.syms sqrtSym = T) :
    WP isa (.block gload) s fun s' => Rest [.t0, .t1, .t3, .s4, .s5] s s' ∧
      Unch base [(40, 24), (p224.sl (GS 0), 512)] s.mem s'.mem ∧
      word s'.mem base 40 = s.gpr .s4 ∧ word s'.mem base 48 = s.gpr .s5 ∧ word s'.mem base 56 = s.gpr .s6 ∧
      (∀ e < 16, sv base s' (GS e) = montT 23 e) ∧ s'.gpr .s4 = 0 ∧ s'.gpr .s5 = 0 := by
  have hn := hw.nowrap
  rw [gload, List.append_assoc, List.append_assoc]
  refine WP.block_append (WP.syms (sd_s4 hw) fun s₁ ⟨r₁, m₁⟩ sy₁ => ?_)
  obtain O₁ : Outside base 40 24 s.mem s₁.mem := by
    rw [m₁]
    exact ((((writeW_outside _ _ _ (by omega_using [])).mono (by omega_using []) (by omega_using [])).trans
      ((writeW_outside _ _ _ (by omega_using [])).mono (by omega_using []) (by omega_using []))).trans
      ((writeW_outside _ _ _ (by omega_using [])).mono (by omega_using []) (by omega_using [])))
  obtain hw₁ := hw.of_kp (Kp.of_rest r₁)
  obtain hT₁ := hT.of_outside r₁.rd (by decide) O₁
  refine rowAddr_ok (T := T) (by decide) (by rw [sy₁]; exact hsym) fun s₂ r₂ h0₂ m₂ => ?_
  obtain hw₂ := hw₁.of_rest r₂
  obtain hT₂ := hT₁.of_mem r₂.rd fun x _ => by rw [m₂]
  refine WP.block_append (WP.mono (gcopies_ok 16 (by decide) hw₂ hT₂ h0₂) fun s₃ ⟨r₃, U₃, v₃⟩ => ?_)
  refine wp_li (imm := 0) (by decide) fun s₄ u₄ => wp_li (imm := 0) (by decide) fun s₅ u₅ => WP.block_nil ?_
  obtain r₅ : Rest [.t0, .t1, .t3, .s4, .s5] s s₅ :=
    (r₁.mono (by decide)).trans ((r₂.mono (by decide)).trans ((r₃.mono (by decide)).trans
      ((u₄.rest (by decide)).trans (u₅.rest (by decide)))))
  obtain m₅ : s₅.mem = s₃.mem := by rw [u₅.mem, u₄.mem]
  obtain U₁₃ : Unch base [(p224.sl (GS 0), 32 * 16)] s₁.mem s₃.mem := by rw [← m₂]; exact U₃
  refine ⟨r₅, by rw [m₅]; exact (O₁.unch.trans U₁₃).cover (by decide), ?_, ?_, ?_, fun e he => ?_,
    by rw [u₅.other _ (by decide), u₄.gpr]; rfl, by rw [u₅.gpr]; rfl⟩
  · rw [m₅, U₁₃.word (by decide) (by omega_using []), m₁, (writeW_outside _ _ _ (by omega_using [])).word (by omega_using []) (by omega_using []),
      (writeW_outside _ _ _ (by omega_using [])).word (by omega_using []) (by omega_using []), word_writeW_self]
  · rw [m₅, U₁₃.word (by decide) (by omega_using []), m₁, (writeW_outside _ _ _ (by omega_using [])).word (by omega_using []) (by omega_using []),
      word_writeW_self]
  · rw [m₅, U₁₃.word (by decide) (by omega_using []), m₁, word_writeW_self]
  · show wordsVal _ _ _ _ = _; rw [m₅]; exact v₃ e he

/-- `rhs = x³ + a x + b` of the public key's `x`. -/
abbrev rhsOf (s : State) : Fe W :=
  Fin.ofNat W.p (ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 28)) *
      Fin.ofNat W.p (ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 28)) *
      Fin.ofNat W.p (ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 28)) +
    Fin.ofNat W.p W.a * Fin.ofNat W.p (ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 28)) +
    Fin.ofNat W.p W.b

/-- What the front leaves, from the state `s` on entry: the digits' state,
and what the checks and the output read. -/
structure FPost (s s' : State) : Prop where
  ws : WsReg s' (s.gpr .a2)
  s2 : s'.gpr .s2 = s.gpr .a0
  regs : ∀ x ∈ preserved, x ≠ .s0 → x ≠ .s1 → x ≠ .s2 → x ≠ .s3 → x ≠ .s4 → x ≠ .s5 → s'.gpr x = s.gpr x
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  sv0 : word s'.mem (s.gpr .a2) 0 = s.gpr .s0
  sv1 : word s'.mem (s.gpr .a2) 8 = s.gpr .s1
  sv2 : word s'.mem (s.gpr .a2) 16 = s.gpr .s2
  sv3 : word s'.mem (s.gpr .a2) 24 = s.gpr .ra
  sv4 : word s'.mem (s.gpr .a2) 32 = s.gpr .s3
  sv5 : word s'.mem (s.gpr .a2) 40 = s.gpr .s4
  sv6 : word s'.mem (s.gpr .a2) 48 = s.gpr .s5
  sv7 : word s'.mem (s.gpr .a2) 56 = s.gpr .s6
  x : sv (s.gpr .a2) s' CX = ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 28)
  par : word s'.mem (s.gpr .a2) (p224.sl PAR) = (s.mem (s.gpr .a1)).setWidth 64 &&& BitVec.ofInt 64 1
  flag : word s'.mem (s.gpr .a2) FL = maskOf (decide (s.mem (s.gpr .a1) = 2 ∨ s.mem (s.gpr .a1) = 3) &&
    decide (ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 28) < W.p))
  one : sv (s.gpr .a2) s' ONE = 1
  zero : sv (s.gpr .a2) s' ZERO = 0
  rhsl : sv (s.gpr .a2) s' RHS < W.p
  rhs : toM W.p (2 ^ 256) (sv (s.gpr .a2) s' RHS) = rhsOf s
  fst : FSt (rhsOf s) (s.gpr .a2) s'
  dst : DSt (rhsOf s) (s.gpr .a2) (s.syms sqrtSym) s' s' 0

/-- The front: up to the digits. -/
theorem front_ok {s : State} (hs : DPre s) : WP isa front224 s (FPost s) := by
  obtain hp0 : 0 < W.p := by decide
  have hT0 : TabOk (s.gpr .a2) (s.syms sqrtSym) s := hs.2.2.2.2.2.2.2.2.2
  rw [front224]
  refine WP.seq (WP.syms (dsetup_ok hs) fun s₁ S sy₁ => ?_)
  obtain ⟨hw₁, S2, S3, Sregs, Srd, Swr, Ssp, Ssv0, Ssv1, Ssv2, Ssv3, Ssv4, Sx, Spar, Sflag, Scs, Sfar⟩ := S
  obtain hT₁ := hT0.of_mem Srd Sfar
  generalize hb : s.gpr .a2 = base at hw₁ S3 Ssv0 Ssv1 Ssv2 Ssv3 Ssv4 Sx Spar Sflag Scs Sfar hT₁ hT0
  generalize hT : s.syms sqrtSym = T at hT₁ hT0
  -- `rhs`.
  refine WP.seq (WP.syms (rhs_ok hw₁ (const_at Scs 10) (const_at Scs 5) (const_at Scs 11))
    fun s₂ ⟨K₂, U₂, lt₂, v₂⟩ sy₂ => ?_)
  obtain hw₂ := hw₁.of_kp K₂
  obtain hT₂ := hT₁.of_unch K₂.rd (by decide) U₂
  obtain one₂ : sv base s₂ ONEP = 2 ^ 256 % W.p := by
    show wordsVal _ _ _ _ = _; rw [sv_unch U₂ ONEP (by decide)]; exact const_at Scs 4
  rw [Sx] at v₂
  -- `w = rhs^((q-1)/2)`.
  refine WP.seq (WP.syms (chainPow_ok (P := wChain) (F := p224Field) field_ok wLay unit hw₂ (one := p224.sl ONEP)
    (by decide) (by decide) one₂ wChain_ok) fun s₃ ⟨Kc₃, U₃, lt₃, v₃⟩ sy₃ => ?_)
  obtain hw₃ := hw₂.of_kc Kc₃
  obtain hT₃ := hT₂.of_unch Kc₃.rd (by decide) U₃
  obtain rhs₃ : sv base s₃ RHS = sv base s₂ RHS := sv_unch U₃ RHS (by decide)
  obtain w₃ : toM W.p (2 ^ 256) (sv base s₃ ACC) = wOf (rhsOf s) := by
    refine v₃.trans ?_
    show toM W.p (2 ^ 256) (sv base s₂ RHS) ^ ((q224 - 1) / 2) = _
    rw [v₂]; exact (VG.Proof.Weierstrass.pow_eq_npow _ _).symm
  -- `r = w rhs` and `t = w r`.
  refine WP.seq (WP.syms (fprog_ok (M := p224.MP') (F := p224Field) field_ok rfl tonLay (by decide) unit tonOps
    (V := [p224.sl ACC, p224.sl RHS]) (E := fun x => toM W.p (2 ^ 256) (wordsVal s₃.mem base x 4))
    ⟨hw₃, by decide, fun x hx => ?_, fun _ _ => rfl⟩ (by decide) (by decide)) fun s₄ ⟨K₄, I₄⟩ sy₄ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact lt₃
    · show sv base s₃ RHS < _; rw [rhs₃]; exact lt₂
  obtain hw₄ := hw₃.of_kp K₄.kp
  have U₄ : Unch base (((tonOps.map FOp.out).map fun w => (w, 8 * 4)) ++ [(own 4, 64 * 4)]) s₃.mem s₄.mem := K₄.mem
  obtain hT₄ := hT₃.of_unch K₄.kp.rd (by decide) U₄
  obtain ⟨tr, tt⟩ := ton_run (fun x => toM W.p (2 ^ 256) (wordsVal s₃.mem base x 4))
  obtain vr₄ : toM W.p (2 ^ 256) (sv base s₄ TR) = rOf (rhsOf s) := by
    refine (I₄.val (p224.sl TR) (by decide)).trans (tr.trans ?_)
    show toM W.p (2 ^ 256) (sv base s₃ ACC) * toM W.p (2 ^ 256) (sv base s₃ RHS) = _
    rw [w₃, rhs₃, v₂]
  obtain vt₄ : toM W.p (2 ^ 256) (sv base s₄ (SS 0)) = tOf (rhsOf s) := by
    refine (I₄.val (p224.sl (SS 0)) (by decide)).trans (tt.trans ?_)
    show toM W.p (2 ^ 256) (sv base s₃ ACC) * (toM W.p (2 ^ 256) (sv base s₃ ACC) *
      toM W.p (2 ^ 256) (sv base s₃ RHS)) = _
    rw [w₃, rhs₃, v₂]
  -- `t`'s powers.
  refine WP.seq (WP.syms (schain_ok 23 (by decide) hw₄ (I₄.lt _ (by decide)) vt₄) fun s₅ ⟨hw₅, K₅, U₅, v₅⟩ sy₅ => ?_)
  obtain hT₅ := hT₄.of_unch K₅.rd (by decide) U₅
  -- The last row.
  refine WP.syms (gload_ok hw₅ hT₅ (by rw [sy₅, sy₄, sy₃, sy₂, sy₁, hT])) fun s₆ ⟨r₆, U₆, w40, w48, w56, g₆, z4, z5⟩ sy₆ => ?_
  obtain hw₆ := wsReg_of_ks hw₅ (Ks.of_rest (rs := [.s4, .s5]) r₆)
  obtain hT₆ := hT₅.of_unch r₆.rd (by decide) U₆
  obtain U₂₆ := ((U₂.trans U₃).trans U₄).trans (U₅.trans U₆)
  obtain U₃₆ := (U₄.trans U₅).trans U₆
  obtain tr₆ : sv base s₆ TR = sv base s₄ TR := sv_unch (U₅.trans U₆) TR (by decide)
  obtain Kc₃' : Ks [.s1] s₂ s₃ :=
    ⟨fun r hr hn => Kc₃.gpr r hr (by intro h; subst h; exact hn (by decide)), Kc₃.rd, Kc₃.wr, Kc₃.sp⟩
  obtain K₁₅ : Ks [.s1] s₁ s₅ := (Ks.of_kp K₂).trans (Kc₃'.trans ((Ks.of_kp K₄.kp).trans (Ks.of_kp K₅)))
  obtain K₁₆ : Ks [.s1, .s4, .s5] s₁ s₆ := K₁₅.mono.trans (Ks.of_rest r₆)
  obtain sym₆ : s₆.syms = s.syms := by rw [sy₆, sy₅, sy₄, sy₃, sy₂, sy₁]
  subst hb hT
  refine ⟨hw₆, by rw [K₁₆.gpr _ (by decide) (by decide), S2], fun x hx h0 h1 h2 h3 h4 h5 => ?_,
    by rw [K₁₆.rd, Srd], by rw [K₁₆.wr, Swr], by rw [K₁₆.sp, Ssp],
    by rw [U₂₆.word (by decide) (by decide)]; exact Ssv0, by rw [U₂₆.word (by decide) (by decide)]; exact Ssv1,
    by rw [U₂₆.word (by decide) (by decide)]; exact Ssv2, by rw [U₂₆.word (by decide) (by decide)]; exact Ssv3,
    by rw [U₂₆.word (by decide) (by decide)]; exact Ssv4,
    by rw [w40, K₁₅.gpr _ (by decide) (by decide), Sregs _ (by decide) (by decide) (by decide) (by decide)],
    by rw [w48, K₁₅.gpr _ (by decide) (by decide), Sregs _ (by decide) (by decide) (by decide) (by decide)],
    by rw [w56, K₁₅.gpr _ (by decide) (by decide), Sregs _ (by decide) (by decide) (by decide) (by decide)],
    by show wordsVal _ _ _ _ = _; rw [sv_unch U₂₆ CX (by decide)]; exact Sx,
    by rw [U₂₆.word (by decide) (by decide)]; exact Spar, by rw [U₂₆.word (by decide) (by decide)]; exact Sflag,
    by show wordsVal _ _ _ _ = _; rw [sv_unch U₂₆ ONE (by decide)]; exact const_at Scs 3,
    by show wordsVal _ _ _ _ = _; rw [sv_unch U₂₆ ZERO (by decide)]; exact const_at Scs 2,
    by show wordsVal _ _ _ _ < _; rw [sv_unch (U₃.trans U₃₆) RHS (by decide)]; exact lt₂,
    by rw [show sv (s.gpr .a2) s₆ RHS = sv (s.gpr .a2) s₂ RHS from sv_unch (U₃.trans U₃₆) RHS (by decide)]; exact v₂,
    ⟨fun m hm => ?_, fun e he => ?_, ?_⟩,
    ⟨hw₆, hT₆, by rw [sym₆], Ks.refl _ _, Unch.refl _ _ _, by rw [z4, kA_zero]; rfl, by rw [z5, kA_zero]; rfl⟩⟩
  · rw [K₁₆.gpr _ hx (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h4, h5⟩)]
    exact Sregs x h0 h2 h3 hx
  · have e : sv (s.gpr .a2) s₆ (SS m) = sv (s.gpr .a2) s₅ (SS m) :=
      sv_unch U₆ (SS m) ((by decide : ∀ m < 24, ∀ w ∈ [((40 : Nat), (24 : Nat)), (p224.sl (GS 0), 512)],
        p224.sl (SS m) + 32 ≤ w.1 ∨ w.1 + w.2 ≤ p224.sl (SS m)) m hm) (by simp only [SS]; omega_using [hm])
    rw [e]; exact v₅ m (by omega_using [hm])
  · rw [g₆ e he]; exact ⟨montT_lt _ _, toM_montT _ _⟩
  · rw [tr₆]; exact ⟨I₄.lt _ (by decide), vr₄⟩


/-! ### The whole decompression -/

theorem par_bit (b : BitVec 8) : (b.setWidth 64 &&& BitVec.ofInt 64 1).toNat % 2 = b.toNat % 2 :=
  Kit.par_bit b

theorem neg_ofNat {v : Nat} (hv : v < W.p) : Fin.ofNat W.p ((W.p - v) % W.p) = -Fin.ofNat W.p v :=
  Kit.neg_ofNat hv

/-- `s4`–`s6` restored from the working space. -/
theorem restore_ok {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block restore456) s fun s' => Rest [.s4, .s5, .s6] s s' ∧ s'.mem = s.mem ∧
      s'.gpr .s4 = word s.mem base 40 ∧ s'.gpr .s5 = word s.mem base 48 ∧ s'.gpr .s6 = word s.mem base 56 := by
  refine ld_ws hw (by decide) (by decide) fun s₁ u₁ => ?_
  obtain hw₁ : WsReg s₁ base := wsReg_of_ks hw (Ks.of_rest (rs := [.s4]) (u₁.rest (ws := [.s4]) (by decide)))
  refine ld_ws hw₁ (by decide) (by decide) fun s₂ u₂ => ?_
  obtain hw₂ : WsReg s₂ base := wsReg_of_ks hw₁ (Ks.of_rest (rs := [.s5]) (u₂.rest (ws := [.s5]) (by decide)))
  refine ld_ws hw₂ (by decide) (by decide) fun s₃ u₃ => WP.block_nil ⟨?_, by rw [u₃.mem, u₂.mem, u₁.mem], ?_, ?_, ?_⟩
  · exact ((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by decide))
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.mem]
  · rw [u₃.gpr, u₂.mem, u₁.mem]

/-- `vg_ec_p224_decompress_public_key`'s postcondition, by register. -/
def DPostC (s s' : State) : Prop :=
  let bs := bytesAt s.mem (s.gpr .a1) 29
  (s'.gpr .a0 = 1 ∧ ∃ Q, Spec.EcKey.matchesCompressedPublicKey Spec.P224.curve bs Q ∧
      bytesAt s'.mem (s.gpr .a0) 57 = Spec.EcKey.encodePoint Q) ∨
    (s'.gpr .a0 = 0 ∧ (¬ ∃ Q, Spec.EcKey.matchesCompressedPublicKey Spec.P224.curve bs Q) ∧
      bytesAt s'.mem (s.gpr .a0) 57 = List.replicate 57 0)

/-- Two facts of the field for `tail_ok`, proven here, without its two hundred hypotheses, which
`grind` reads. -/
private theorem neg_mul_neg_self (r : Fe W) : -r * -r = r * r := by grind
private theorem sub_eq_zero_iff_eq (a b : Fe W) : a - b = 0 ↔ a = b := by
  constructor <;> intro h <;> grind

/-- The root, the checks and the output, after the digits. -/
theorem tail_ok (hL : VG.Proof.Weierstrass.Law W) {s s₆ s₇ : State} (hs : DPre s) (F : FPost s s₆)
    (D : DSt (rhsOf s) (s.gpr .a2) (s.syms sqrtSym) s₆ s₇ 24) :
    WP isa tail224 s₇ fun s' => abiPreserved s s' ∧ DPostC s s' := by
  obtain hp0 : 0 < W.p := by decide
  obtain ⟨hrd, hwr, hpo, hpw, how, hfo, hfp, hfs, hal, -⟩ := hs
  rw [tail224]
  -- The root.
  refine WP.seq (WP.mono (rootMul_ok F.fst D) fun s₈ ⟨hw₈, _, _, K₈, U₈, lt₈, v₈⟩ => ?_)
  refine WP.seq (WP.mono (restore_ok hw₈) fun s₉ ⟨r₉, m₉, g4, g5, g6⟩ => ?_)
  obtain hw₉ := wsReg_of_ks hw₈ (Ks.of_rest (rs := [.s4, .s5, .s6]) r₉)
  obtain U₆₉ : Unch (s.gpr .a2) (dW ++ [(p224.sl ACC, 32), (p224.sl XS, 32), (p224.sl ACC, 32), (own 4, 256)])
      s₆.mem s₉.mem := by rw [m₉]; exact D.unch.trans U₈
  obtain acc₉ : sv (s.gpr .a2) s₉ ACC = sv (s.gpr .a2) s₈ ACC := by show wordsVal _ _ _ _ = _; rw [m₉]
  obtain rhs₉ : sv (s.gpr .a2) s₉ RHS = sv (s.gpr .a2) s₆ RHS := sv_unch U₆₉ RHS (by decide)
  obtain one₉ : sv (s.gpr .a2) s₉ ONE = 1 := by
    rw [show sv (s.gpr .a2) s₉ ONE = sv (s.gpr .a2) s₆ ONE from sv_unch U₆₉ ONE (by decide)]; exact F.one
  obtain zero₉ : sv (s.gpr .a2) s₉ ZERO = 0 := by
    rw [show sv (s.gpr .a2) s₉ ZERO = sv (s.gpr .a2) s₆ ZERO from sv_unch U₆₉ ZERO (by decide)]; exact F.zero
  -- The root's checks.
  refine WP.seq (WP.mono (root_ok hw₉ (by rw [acc₉]; exact lt₈) (by rw [rhs₉]; exact F.rhsl) one₉ zero₉)
    fun s₁₀ ⟨K₁₀, U₁₀, ltd₁₀, vd₁₀, lty₁₀, vy₁₀, y2₁₀⟩ => ?_)
  obtain hw₁₀ := hw₉.of_kp K₁₀
  obtain U₆₁₀ := U₆₉.trans U₁₀
  obtain hF : word s₁₀.mem (s.gpr .a2) FL = maskOf (decide (s.mem (s.gpr .a1) = 2 ∨ s.mem (s.gpr .a1) = 3) &&
      decide (ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 28) < W.p)) := by
    rw [U₆₁₀.word (by decide) (by decide)]; exact F.flag
  obtain hpr : (word s₁₀.mem (s.gpr .a2) (p224.sl PAR)).toNat % 2 = (s.mem (s.gpr .a1)).toNat % 2 := by
    rw [U₆₁₀.word (by decide) (by decide), F.par, par_bit]
  obtain cx₁₀ : sv (s.gpr .a2) s₁₀ CX = ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 28) := by
    show wordsVal _ _ _ _ = _; rw [sv_unch U₆₁₀ CX (by decide)]; exact F.x
  obtain K₆₁₀ : Ks [.s4, .s5, .s6] s₆ s₁₀ :=
    D.ks.trans (K₈.mono.trans ((Ks.of_rest r₉).trans (Ks.of_kp K₁₀)))
  obtain h2₁₀ : s₁₀.gpr .s2 = s.gpr .a0 := by rw [K₆₁₀.gpr _ (by decide) (by decide), F.s2]
  obtain wr₁₀ : s₁₀.wr = s.wr := by rw [K₆₁₀.wr, F.wr]
  refine WP.mono (dfin_ok hw₁₀ h2₁₀ hfo (fun i hi => by
      rw [wr₁₀, hwr]
      exact ⟨_, List.mem_cons_self .., Offset.contains_base (s.gpr .a0) (d := i) (n := 1) (k := 57) (by omega_using [hi])
        (by omega_using [hi])⟩) how hF hpr)
    fun s' ⟨a0', b', s0', s1', s2', ra', s3', regs', sp'⟩ => ?_
  -- The registers.
  obtain w9 : ∀ d, d ∈ [40, 48, 56] → word s₉.mem (s.gpr .a2) d = word s₆.mem (s.gpr .a2) d := fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> exact U₆₉.word (by decide) (by decide)
  refine ⟨⟨fun r hr => ?_, by rw [sp', K₆₁₀.sp, F.sp], by rw [ra', U₆₁₀.word (by decide) (by decide), F.sv3]⟩, ?_⟩
  · by_cases h0 : r = .s0
    · subst h0; rw [s0', U₆₁₀.word (by decide) (by decide), F.sv0]
    by_cases h1 : r = .s1
    · subst h1; rw [s1', U₆₁₀.word (by decide) (by decide), F.sv1]
    by_cases h2' : r = .s2
    · subst h2'; rw [s2', U₆₁₀.word (by decide) (by decide), F.sv2]
    by_cases h3' : r = .s3
    · subst h3'; rw [s3', U₆₁₀.word (by decide) (by decide), F.sv4]
    rw [regs' r hr h0 h1 h2' h3']
    by_cases h4 : r = .s4
    · subst h4; rw [K₁₀.gpr _ (by decide), g4, ← m₉, w9 40 (by decide), F.sv5]
    by_cases h5 : r = .s5
    · subst h5; rw [K₁₀.gpr _ (by decide), g5, ← m₉, w9 48 (by decide), F.sv6]
    by_cases h6 : r = .s6
    · subst h6; rw [K₁₀.gpr _ (by decide), g6, ← m₉, w9 56 (by decide), F.sv7]
    rw [K₆₁₀.gpr r hr (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h4, h5, h6⟩),
      F.regs r hr h0 h1 h2' h3' h4 h5]
  -- The values.
  rw [cx₁₀] at b'
  obtain vd : toM W.p (2 ^ 256) (sv (s.gpr .a2) s₁₀ DIF) = root224 (rhsOf s) * root224 (rhsOf s) - rhsOf s := by
    rw [vd₁₀, acc₉, v₈, rhs₉, F.rhs]
  obtain vy : Fin.ofNat W.p (sv (s.gpr .a2) s₁₀ Y1) = root224 (rhsOf s) := by rw [vy₁₀, acc₉, v₈]
  generalize hx : ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 28) = x at a0' b' hF
  generalize htag : s.mem (s.gpr .a1) = tag at a0' b' hF hpr
  generalize hxf : (Fin.ofNat W.p x : Fe W) = xf
  obtain hrhsF : rhsOf s = xf * xf * xf + Fin.ofNat W.p W.a * xf + Fin.ofNat W.p W.b := by
    rw [← hxf, ← hx]
  generalize hrhs : xf * xf * xf + Fin.ofNat W.p W.a * xf + Fin.ofNat W.p W.b = rhsF at hrhsF
  rw [hrhsF] at vd vy
  generalize hr : root224 rhsF = r at vy vd
  obtain hy1 : r.val = sv (s.gpr .a2) s₁₀ Y1 := by rw [← vy, Fin.val_ofNat, Nat.mod_eq_of_lt lty₁₀]
  generalize hyN : (if sv (s.gpr .a2) s₁₀ Y1 % 2 ≠ tag.toNat % 2 then sv (s.gpr .a2) s₁₀ Y2
    else sv (s.gpr .a2) s₁₀ Y1) = yN at a0' b'
  obtain hyNlt : yN < W.p := by
    rw [← hyN]; split
    · rw [y2₁₀]; exact Nat.mod_lt _ hp0
    · exact lty₁₀
  obtain hch : VG.Impl.EcKey.Compressed.chooseRoot r (tag.toNat % 2) = Fin.ofNat W.p yN := by
    unfold VG.Impl.EcKey.Compressed.chooseRoot
    rw [hy1, ← hyN]
    by_cases h : sv (s.gpr .a2) s₁₀ Y1 % 2 = tag.toNat % 2
    · rw [ite_eq_left h, ite_eq_right (fun h' => h' h), vy]
    · rw [ite_eq_right h, ite_eq_left h, y2₁₀, neg_ofNat lty₁₀, vy]
  obtain hval : (Fin.ofNat W.p yN : Fe W).val = yN := by rw [Fin.val_ofNat, Nat.mod_eq_of_lt hyNlt]
  obtain hsq : VG.Impl.EcKey.Compressed.chooseRoot r (tag.toNat % 2) *
      VG.Impl.EcKey.Compressed.chooseRoot r (tag.toNat % 2) = r * r := by
    unfold VG.Impl.EcKey.Compressed.chooseRoot; split
    · rfl
    · exact neg_mul_neg_self r
  obtain hdif : sv (s.gpr .a2) s₁₀ DIF = 0 ↔ r * r = rhsF := by
    rw [← toM_eq_zero_iff unit ltd₁₀, vd]
    exact sub_eq_zero_iff_eq _ _
  -- The specification's decoding.
  obtain hsplit : bytesAt s.mem (s.gpr .a1) 29 = tag :: bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 28 := by
    obtain h1 : bytesAt s.mem (s.gpr .a1) 1 = [tag] := by
      simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero, htag]
    rw [show (29 : Nat) = 1 + 28 from rfl, VG.Proof.Weierstrass.bytesAt_add, h1]; rfl
  obtain hlen : (bytesAt s.mem (s.gpr .a1) 29).length = W.len + 1 := VG.Proof.Weierstrass.length_bytesAt _ _ _
  obtain hhd : (bytesAt s.mem (s.gpr .a1) 29).head? = some tag := by rw [hsplit]; rfl
  obtain hxv : ofBytes ((bytesAt s.mem (s.gpr .a1) 29).drop 1) = x := by
    rw [hsplit, List.drop_one, List.tail_cons]; exact hx
  obtain hdec := VG.Proof.EcKey.Compressed.decode_checked_eq (C := W) root224 hlen hhd hxv
  simp only [] at hdec
  rw [hxf, hrhs, hr, hch] at hdec
  rw [hch] at hsq
  rw [hval] at hdec
  generalize hB : (((decide (tag = 2 ∨ tag = 3) && decide (x < W.p)) && decide (sv (s.gpr .a2) s₁₀ DIF = 0)) &&
    decide (yN % 2 = tag.toNat % 2)) = B at a0' b'
  obtain key : B = true ↔ ((tag = 2 ∨ tag = 3) ∧ x < W.p) ∧
      (Fin.ofNat W.p yN * Fin.ofNat W.p yN = rhsF ∧ yN % 2 = tag.toNat % 2) := by
    rw [← hB, hsq, ← hdif]
    simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  obtain hroot := VG.Proof.P224.rootFacts224 hL
  unfold DPostC
  simp only []
  cases B
  · have hn : ¬ (((tag = 2 ∨ tag = 3) ∧ x < W.p) ∧
        (Fin.ofNat W.p yN * Fin.ofNat W.p yN = rhsF ∧ yN % 2 = tag.toNat % 2)) := fun h =>
      Bool.false_ne_true (key.mpr h)
    rw [ite_eq_right hn] at hdec
    refine Or.inr ⟨a0', (VG.Proof.EcKey.Compressed.decode_none_iff hroot _).mp hdec, ?_⟩
    rw [b', ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true]
    decide
  · have hc := key.mp rfl
    rw [ite_eq_left hc] at hdec
    refine Or.inl ⟨a0', _, VG.Proof.EcKey.Compressed.decode_sound hdec, ?_⟩
    rw [b']
    show _ = 4 :: (toBytes 28 xf.val ++ toBytes 28 (Fin.ofNat W.p yN : Fe W).val)
    rw [hval, ← hxf, Fin.val_ofNat, Nat.mod_eq_of_lt hc.1.2]
    rfl

/-- `vg_ec_p224_decompress_public_key` by register. -/
theorem decompress_ok (hL : VG.Proof.Weierstrass.Law W) {s : State} (hs : DPre s) :
    WP isa decompressP224 s fun s' => abiPreserved s s' ∧ DPostC s s' := by
  rw [decompressP224]
  refine WP.seq (WP.mono (front_ok hs) fun s₆ F => ?_)
  exact WP.seq (WP.mono (digits_ok F.fst 24 (Nat.le_refl _) F.dst) fun s₇ D => tail_ok hL hs F D)

end VG.Proof.EcKey.Compressed.RISCV64.P224

end

end

/-!
# SEC 1 point conversion over P-224 on RISC-V: `Verified`

`compress_verified`: from `compress_ok`, with the times depending only on the
pointers (by taint tracking).

`decompress_verified`: from `decompress_ok`, under `abi.withConsts` of the
square root's table (`decRVC`). Its time depends on the public key, which
the contract allows (`leak`): the table's entries read are those of the
digits of `rhs`, which the bytes determine. Two runs with the same public
data (the pointers, the table's address, `rhs`) are related (`Two`) by the
correctness proof's states (`front_ok`, `digit_ok`): before the digits, after
each digit (which pins the digits found so far in `s4` and `s5`) and before
the root; each piece is checked by the taint analysis from the registers
those states pin (`RelCT`).
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.RISCV64.P224

open VG VG.RISCV64 VG.Impl.EcKey.Compressed.RISCV64
open VG.Impl.Ecdsa.RISCV64 (Cfg)
open VG.Proof.Weierstrass.RISCV64 (WsReg)
open VG.Proof.Ecdsa.RISCV64.P224 (W)

theorem compress_rv (s : State) (hs : compRV.pre s) :
    ∃ t s', Exec isa compressP224 s t s' ∧ abiPreserved s s' ∧ compRV.post s s' := by
  obtain ⟨t, s', he, h⟩ := compress_ok hs
  exact ⟨t, s', he, h⟩

theorem compress_ct : ConstantTime isa compRV.pre compRV.pub compressP224 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
    (fun _ _ _ _ ⟨hsp, h0, h1, h2⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2⟩) (by taint_decide)

/-- A state satisfying the preconditions, for an output of `n` bytes and an
input of `m`. -/
def convSat (n m : Nat) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, m⟩]
  wr := [⟨0x1000, n⟩, ⟨0x8000, 8192⟩]

theorem compress_verified :
    Verified RISCV64.target compressP224 (Spec.EcKey.P224.inst.compressPublicKeyContract RISCV64.abi) :=
  Verified.of_correct compress_rv compress_ct
    { pre := by
        sig_implies_pre [Spec.EcKey.P224.inst, Spec.EcKey.Instance.compressPublicKeyContract,
          Spec.EcKey.Instance.compressPublicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, compRV,
          RISCV64.abi, RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P224.inst, Spec.EcKey.Instance.compressPublicKeyContract,
          Spec.EcKey.Instance.compressPublicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, compRV,
          RISCV64.abi, RISCV64.argRegs]
        have h' := h
        dsimp only [compRV] at h'
        generalize hq : Spec.EcKey.compressPublicKey _ _ = q
        have hq' : Spec.EcKey.compressPublicKey Spec.P224.curve (Spec.Ecdsa.bytesAt s.mem (s.gpr .a1) 57) = q := hq
        rw [hq'] at h'
        rcases q with _ | z
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
      pub := by
        sig_implies_pub [Spec.EcKey.P224.inst, Spec.EcKey.Instance.compressPublicKeyContract,
          Spec.EcKey.Instance.compressPublicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, compRV,
          RISCV64.abi, RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.P224.inst, Spec.EcKey.Instance.compressPublicKeyContract,
          Spec.EcKey.Instance.compressPublicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, compRV,
          RISCV64.abi, RISCV64.argRegs, convSat] [convSat] using (convSat 29 57) }

/-! ## Decompression's contract -/

/-- The precondition by register, without the table. -/
def DPre0 (s : State) : Prop :=
  let out : Region := ⟨s.gpr .a0, 57⟩
  let pk : Region := ⟨s.gpr .a1, 29⟩
  let ws : Region := ⟨s.gpr .a2, 8192⟩
  s.rd = [pk] ∧ s.wr = [out, ws] ∧ pk.Disjoint out ∧ pk.Disjoint ws ∧ out.Disjoint ws ∧
    (s.gpr .a0).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 29 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8192 ≤ 2 ^ 64 ∧
    (s.gpr .a2).toNat % 8 = 0

/-- `vg_ec_p224_decompress_public_key(out = a0, public = a1, scratch = a2)`, by
register, without the table. -/
def decRV : Contract isa where
  pre := DPre0
  post := DPostC
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    (Spec.EcKey.bytesAt s₁.mem (s₁.gpr .a1) 29).map (·.toNat) = (Spec.EcKey.bytesAt s₂.mem (s₂.gpr .a1) 29).map (·.toNat)

/-- `decRV` with the table (`abi.withConsts`). -/
def decRVC : Contract isa where
  pre s := decRV.pre (stripConsts sqrtConsts s) ∧ ConstsOk sqrtConsts 0 s
  post := decRV.post
  pub s₁ s₂ := decRV.pub s₁ s₂ ∧ s₁.syms sqrtSym = s₂.syms sqrtSym

/-- The precondition the proof of correctness takes. -/
theorem dpre_of {s : State} (h : decRVC.pre s) : DPre s := by
  obtain ⟨⟨hrd, hwr, hpo, hpw, how, hfo, hfp, hfs, hal⟩, hc⟩ := h
  have hc' : ConstsOk [(sqrtSym, sqrtWords)] 0 s := hc
  have hl := sqrtWords_length
  have hr := hc'.rd1
  have hw := hc'.wr1
  have hf := hc'.fit (List.mem_cons_self)
  rw [hl] at hr hw hf
  have hrd' : s.rd = [⟨s.gpr .a1, 29⟩, ⟨s.syms sqrtSym, 12288⟩] := by
    have e1 : s.rd.drop (s.rd.length - 1) = [⟨s.syms sqrtSym, 8 * sqrtWords.length⟩] := hc'.1
    rw [hl] at e1
    have e0 : s.rd.take (s.rd.length - 1) = [⟨s.gpr .a1, 29⟩] := hrd
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, e0, e1]; rfl
  have hwr' : s.wr = [⟨s.gpr .a0, 57⟩, ⟨s.gpr .a2, 8192⟩] := hwr
  have hd : Region.Disjoint ⟨s.syms sqrtSym, 12288⟩ ⟨s.gpr .a2, 8192⟩ := hw _ (by rw [hwr']; simp)
  refine ⟨hrd', hwr, hpo, hpw, how, hfo, hfp, hfs, hal, ?_⟩
  refine ⟨fun i hi => hc'.held1 i (by rw [hl]; exact hi), hc'.aligned List.mem_cons_self,
    by rw [hrd']; simp, hf, fun d hd' => ?_⟩
  have hcn : (⟨s.syms sqrtSym, 12288⟩ : Region).Contains (s.syms sqrtSym + BitVec.ofNat 64 d) 1 :=
    Offset.contains_base _ (by omega_using [hd']) (by omega_using [hd'])
  have := hd _ hcn
  simp only [Region.Contains, Nat.not_le] at this
  simp only [VG.Proof.Mont.ofs]; omega_using [this]

/-! ## Decompression's constant time, relating two runs -/

/-- Both runs satisfy `Φ a`, for the same `a`, with the same stack pointer. -/
def Two {α : Type} (Φ : α → State → Prop) (s₁ s₂ : State) : Prop := ∃ a, Φ a s₁ ∧ Φ a s₂ ∧ s₁.sp = s₂.sp

theorem two_post {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two Φ) c fun _ _ => True) (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) :
    RelCT isa (Two Φ) c (Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨a, h₁, h₂, hsp⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw a s₁ h₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw a s₂ h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, a, y₁, y₂, by rw [(Exec.rdwr e₁).2.2, (Exec.rdwr e₂).2.2, hsp]⟩

/-- `Φ a` fixes the registers `rs` and the table's address. -/
def Pins {α : Type} (Φ : α → State → Prop) (rs : List Reg) : Prop :=
  ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → (∀ r ∈ rs, s₁.gpr r = s₂.gpr r) ∧ s₁.syms sqrtSym = s₂.syms sqrtSym

theorem two_taint {α : Type} {Φ : α → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    {hc : VG.Taint.Hint (taintSym [sqrtSym]).T}
    (h : ((taintSym [sqrtSym]).check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taintSym [sqrtSym]) (Taint.ofRegs rs)
    (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨⟨hsp, fun r hr => (hpin a _ _ h₁ h₂).1 r (Taint.mem_ofRegs.mp hr)⟩,
      fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact (hpin a _ _ h₁ h₂).2⟩) h

/-- The public data of a run: the pointers, the table's address and `rhs`. -/
structure DA where
  out : Addr
  pk : Addr
  base : Addr
  T : Addr
  A : Spec.Weierstrass.Fe W

/-- On entry. -/
def Φ0 (a : DA) (s : State) : Prop :=
  DPre s ∧ s.gpr .a0 = a.out ∧ s.gpr .a1 = a.pk ∧ s.gpr .a2 = a.base ∧ s.syms sqrtSym = a.T ∧ rhsOf s = a.A

/-- After `j` digits. -/
def Φd (j : Nat) (a : DA) (s : State) : Prop :=
  ∃ s₀, s₀.gpr .s2 = a.out ∧ FSt a.A a.base s₀ ∧ DSt a.A a.base a.T s₀ s j

theorem pins_Φ0 : Pins Φ0 [.a0, .a1, .a2] := by
  rintro a s₁ s₂ ⟨-, a0, a1, a2, sy, -⟩ ⟨-, b0, b1, b2, sy', -⟩
  refine ⟨fun r hr => ?_, by rw [sy, sy']⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]

theorem pins_Φd (j : Nat) : Pins (Φd j) [.s0, .s4, .s5] := by
  rintro a s₁ s₂ ⟨_, _, _, D₁⟩ ⟨_, _, _, D₂⟩
  refine ⟨fun r hr => ?_, by rw [D₁.sym, D₂.sym]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [D₁.ws.s0, D₂.ws.s0]
  · rw [D₁.k.1, D₂.k.1]
  · rw [D₁.k.2, D₂.k.2]

theorem pins_tail : Pins (Φd 24) [.s0, .s2, .s4, .s5] := by
  rintro a s₁ s₂ ⟨_, h₁, _, D₁⟩ ⟨_, h₂, _, D₂⟩
  refine ⟨fun r hr => ?_, by rw [D₁.sym, D₂.sym]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [D₁.ws.s0, D₂.ws.s0]
  · rw [D₁.ks.gpr _ (by decide) (by decide), D₂.ks.gpr _ (by decide) (by decide), h₁, h₂]
  · rw [D₁.k.1, D₂.k.1]
  · rw [D₁.k.2, D₂.k.2]

theorem front_rel : RelCT isa (Two Φ0) front224 (Two (Φd 0)) :=
  two_post (two_taint _ pins_Φ0 (by taint_decide)) fun a s ⟨hs, h0, _, h2, hT, hA⟩ =>
    WP.mono (front_ok hs) fun s' F => ⟨s', by rw [F.s2, h0], by rw [← hA, ← h2]; exact F.fst,
      by rw [← hA, ← h2, ← hT]; exact F.dst⟩

/-! The constant-time analyses of the calls of the field's product and difference from their
arguments, each done once for the checks of the 24 digits (`taint_decide_sum`), every one of which
calls the second and all but the first the first; they keep what is public of `s0` and
`s4`–`s6`, which the functions do not write. -/
taint_summary sqrtMulSum : (taintSym [sqrtSym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Ecdsa.RISCV64.p224Field.S.fn "mul") Impl.Ecdsa.RISCV64.p224Field.mulA)
  keeping (Taint.ofRegs [.s0, .s4, .s5, .s6])
taint_summary sqrtSubSum : (taintSym [sqrtSym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Ecdsa.RISCV64.p224Field.S.fn "sub") Impl.Ecdsa.RISCV64.p224Field.subA)
  keeping (Taint.ofRegs [.s0, .s4, .s5, .s6])

/-- Each digit is checked by the taint analysis from the registers of the digits. -/
theorem digit_ct (j : Nat) (hj : j < 24) :
    ∃ hc, ((taintSym [sqrtSym]).check (Taint.ofRegs [.s0, .s4, .s5]) (digit j) hc).isSome = true := by
  match j, hj with
  | 0, _ => show ∃ hc, _; taint_decide_sum [sqrtMulSum, sqrtSubSum]
  | 1, _ => show ∃ hc, _; taint_decide_sum [sqrtMulSum, sqrtSubSum]
  | 2, _ => show ∃ hc, _; taint_decide_sum [sqrtMulSum, sqrtSubSum]
  | 3, _ => show ∃ hc, _; taint_decide_sum [sqrtMulSum, sqrtSubSum]
  | 4, _ => show ∃ hc, _; taint_decide_sum [sqrtMulSum, sqrtSubSum]
  | 5, _ => show ∃ hc, _; taint_decide_sum [sqrtMulSum, sqrtSubSum]
  | 6, _ => show ∃ hc, _; taint_decide_sum [sqrtMulSum, sqrtSubSum]
  | 7, _ => show ∃ hc, _; taint_decide_sum [sqrtMulSum, sqrtSubSum]
  | 8, _ => show ∃ hc, _; taint_decide_sum [sqrtMulSum, sqrtSubSum]
  | 9, _ => show ∃ hc, _; taint_decide_sum [sqrtMulSum, sqrtSubSum]
  | 10, _ => show ∃ hc, _; taint_decide_sum [sqrtMulSum, sqrtSubSum]
  | 11, _ => show ∃ hc, _; taint_decide_sum [sqrtMulSum, sqrtSubSum]
  | 12, _ => show ∃ hc, _; taint_decide_sum [sqrtMulSum, sqrtSubSum]
  | 13, _ => show ∃ hc, _; taint_decide_sum [sqrtMulSum, sqrtSubSum]
  | 14, _ => show ∃ hc, _; taint_decide_sum [sqrtMulSum, sqrtSubSum]
  | 15, _ => show ∃ hc, _; taint_decide_sum [sqrtMulSum, sqrtSubSum]
  | 16, _ => show ∃ hc, _; taint_decide_sum [sqrtMulSum, sqrtSubSum]
  | 17, _ => show ∃ hc, _; taint_decide_sum [sqrtMulSum, sqrtSubSum]
  | 18, _ => show ∃ hc, _; taint_decide_sum [sqrtMulSum, sqrtSubSum]
  | 19, _ => show ∃ hc, _; taint_decide_sum [sqrtMulSum, sqrtSubSum]
  | 20, _ => show ∃ hc, _; taint_decide_sum [sqrtMulSum, sqrtSubSum]
  | 21, _ => show ∃ hc, _; taint_decide_sum [sqrtMulSum, sqrtSubSum]
  | 22, _ => show ∃ hc, _; taint_decide_sum [sqrtMulSum, sqrtSubSum]
  | 23, _ => show ∃ hc, _; taint_decide_sum [sqrtMulSum, sqrtSubSum]
  | _ + 24, h => exact absurd h (by omega_using [])

theorem digits_rel : ∀ j, j ≤ 24 → RelCT isa (Two (Φd 0)) (digits j) (Two (Φd j))
  | 0, _ => by
    rw [digits]
    exact two_post (two_taint [.s0, .s4, .s5] (pins_Φd 0) (hc := .block [] 1024) rfl) fun _ _ h => WP.block_nil h
  | j + 1, hj => by
    rw [digits]
    obtain ⟨hc, h⟩ := digit_ct j (by omega_using [hj])
    exact RelCT.seq (digits_rel j (by omega_using [hj])) (two_post (two_taint _ (pins_Φd j) h)
      fun a s ⟨s₀, h2, F, D⟩ => WP.mono (digit_ok (by omega_using [hj]) F D) fun s' D' => ⟨s₀, h2, F, D'⟩)

theorem tail_ct : RelCT isa (Two (Φd 24)) tail224 fun _ _ => True :=
  two_taint _ pins_tail (by taint_decide)


/-- Equal bytes of the public key give equal `rhs`. -/
theorem rhsOf_eq {s₁ s₂ : State}
    (h : (Spec.EcKey.bytesAt s₁.mem (s₁.gpr .a1) 29).map (·.toNat) =
      (Spec.EcKey.bytesAt s₂.mem (s₂.gpr .a1) 29).map (·.toNat)) : rhsOf s₂ = rhsOf s₁ := by
  have hb' : Spec.EcKey.bytesAt s₁.mem (s₁.gpr .a1) 29 = Spec.EcKey.bytesAt s₂.mem (s₂.gpr .a1) 29 :=
    (List.map_inj_right fun x y h => BitVec.eq_of_toNat_eq h).mp h
  have hb : Spec.Ecdsa.bytesAt s₁.mem (s₁.gpr .a1) 29 = Spec.Ecdsa.bytesAt s₂.mem (s₂.gpr .a1) 29 := hb'
  have hd : ∀ t : State, Spec.Ecdsa.bytesAt t.mem (t.gpr .a1 + BitVec.ofNat 64 1) 28 =
      (Spec.Ecdsa.bytesAt t.mem (t.gpr .a1) 29).drop 1 := fun t => by
    rw [show (29 : Nat) = 1 + 28 from rfl, VG.Proof.Weierstrass.bytesAt_add,
      List.drop_left' (VG.Proof.Weierstrass.length_bytesAt _ _ _)]
  unfold rhsOf
  rw [hd s₂, hd s₁, hb]

theorem decompress_rel : RelCT isa (Two Φ0) decompressP224 fun _ _ => True :=
  RelCT.seq front_rel (RelCT.seq (digits_rel 24 (Nat.le_refl _)) tail_ct)

theorem decompress_ct : ConstantTime isa decRVC.pre decRVC.pub decompressP224 :=
  RelCT.constantTime (decompress_rel.mono (fun s₁ _ ⟨h₁, h₂, ⟨hsp, h0, h1, h2, hb⟩, hsy⟩ =>
    ⟨⟨s₁.gpr .a0, s₁.gpr .a1, s₁.gpr .a2, s₁.syms sqrtSym, rhsOf s₁⟩, ⟨dpre_of h₁, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨dpre_of h₂, h0.symm, h1.symm, h2.symm, hsy.symm, rhsOf_eq hb⟩, hsp⟩) fun _ _ h => h)

theorem decompress_rv (hL : VG.Proof.Weierstrass.Law Spec.P224.curve) (s : State) (hs : decRVC.pre s) :
    ∃ t s', Exec isa decompressP224 s t s' ∧ abiPreserved s s' ∧ decRVC.post s s' := by
  obtain ⟨t, s', he, h⟩ := decompress_ok hL (dpre_of hs)
  exact ⟨t, s', he, h⟩

theorem decRV_implies : decRV.Implies (Spec.EcKey.P224.inst.decompressPublicKeyContract RISCV64.abi) :=
    { pre := by
        sig_implies_pre [Spec.EcKey.P224.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
          Spec.EcKey.Instance.decompressPublicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, decRV, DPre0,
          RISCV64.abi, RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P224.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
          Spec.EcKey.Instance.decompressPublicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, decRV, DPre0,
          RISCV64.abi, RISCV64.argRegs]
        rcases (h : DPostC s s') with ⟨h1, Q, hm, hb⟩ | ⟨h1, hn, hb⟩
        · exact Or.inl ⟨by rw [h1]; rfl, Q, hm, hb⟩
        · exact Or.inr ⟨by rw [h1]; rfl, hn, hb⟩
      pub := by
        sig_implies_pub [Spec.EcKey.P224.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
          Spec.EcKey.Instance.decompressPublicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, decRV, DPre0,
          RISCV64.abi, RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.P224.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
          Spec.EcKey.Instance.decompressPublicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, decRV, DPre0,
          RISCV64.abi, RISCV64.argRegs, convSat] [convSat] using (convSat 57 29) }

/-- A memory holding the table at `0x100000`, for the witness of the contract
with it (irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def sqrtSatMem : Mem := constMem 0x100000 sqrtWords

theorem sqrtSatMem_held : ∀ i < sqrtWords.length,
    sqrtSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = sqrtWords.getD i 0 := by
  have h := constMem_held 0x100000 sqrtWords (by rw [sqrtWords_length]; decide)
  unfold sqrtSatMem
  exact h

/-- A state satisfying the precondition with the table. -/
def decSatC : State :=
  { convSat 57 29 with mem := sqrtSatMem, rd := (convSat 57 29).rd ++ [⟨0x100000, 12288⟩], syms := fun _ => 0x100000 }

theorem dec_sat : (Spec.EcKey.P224.inst.decompressPublicKeyContract (RISCV64.abi.withConsts sqrtConsts)).pre decSatC := by
  have hl := sqrtWords_length
  have held := sqrtSatMem_held
  rw [show sqrtConsts = [(sqrtSym, sqrtWords)] from rfl]
  generalize sqrtWords = W' at hl held ⊢
  generalize e : decSatC = s
  sig_pre [Spec.EcKey.P224.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, RISCV64.abi,
    RISCV64.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  refine ⟨by decide, rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, rfl, rfl,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, by decide⟩
  change r ∈ [⟨0x1000, 57⟩, ⟨0x8000, 8192⟩] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)

theorem decRVC_implies :
    decRVC.Implies (Spec.EcKey.P224.inst.decompressPublicKeyContract (RISCV64.abi.withConsts sqrtConsts)) :=
  { pre := fun _ hs => ⟨decRV_implies.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
    post := fun s s' hs hp => post_consts.mpr (decRV_implies.post (stripConsts _ s) s'
      (pre_consts.mp hs).1 hp)
    pub := fun s₁ s₂ h₁ h₂ hp => ⟨decRV_implies.pub (stripConsts _ s₁) (stripConsts _ s₂)
        (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
      (pub_consts.mp hp).2 _ List.mem_cons_self⟩
    sat := ⟨decSatC, dec_sat⟩ }

theorem decompress_verified (hL : VG.Proof.Weierstrass.Law Spec.P224.curve) :
    Verified RISCV64.target decompressP224
      (Spec.EcKey.P224.inst.decompressPublicKeyContract (RISCV64.abi.withConsts sqrtConsts)) :=
  Verified.of_correct (decompress_rv hL) decompress_ct decRVC_implies

/-- `vg_ec_p224_compress_public_key` as emitted, cleanup included
(`Impl.EcKey.Compressed.RISCV64.Fn.compressP224`), meets its contract in constant
time and returns without secret residue. -/
theorem compress_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.EcKey.Compressed.RISCV64.Fn.compressP224
      (Spec.EcKey.P224.inst.compressPublicKeyContract RISCV64.abi) 32 :=
  RISCV64.Scrub.verifiedScrubbedAll (api := Spec.EcKey.P224.inst.compressPublicKeyApi) (W := 0)
    { code := compressP224, verified := compress_verified }
    (EcKey.RISCV64.Scrub.compressOut _ _ []) (by dsimp only; lit_decide)

/-- `vg_ec_p224_decompress_public_key` as emitted, cleanup included
(`Impl.EcKey.Compressed.RISCV64.Fn.decompressP224`), meets its contract in
constant time and returns without secret residue. -/
theorem decompress_scrubbed (hL : VG.Proof.Weierstrass.Law Spec.P224.curve) :
    VerifiedScrubbed RISCV64.target Impl.EcKey.Compressed.RISCV64.Fn.decompressP224
      (Spec.EcKey.P224.inst.decompressPublicKeyContract (RISCV64.abi.withConsts sqrtConsts)) 32 :=
  RISCV64.Scrub.verifiedScrubbedAll (api := Spec.EcKey.P224.inst.decompressPublicKeyApi) (W := 0)
    { code := decompressP224, verified := decompress_verified hL }
    (EcKey.RISCV64.Scrub.decompressOut _ _ sqrtConsts) (by dsimp only; lit_decide)

end VG.Proof.EcKey.Compressed.RISCV64.P224
