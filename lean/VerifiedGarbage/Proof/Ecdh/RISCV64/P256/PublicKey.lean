module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.Tail
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Tail
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Spec.EcKey
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.P256.Point

/-!
# P-256's public keys on RISC-V: correctness

`vg_ec_p256_public_key` meets its contract by register (`pkRV`), given the
group law (`pk_ok`): the saves, `d` and the constants, `G` to `R`'s first two
slots and the flag set, `tail_ok`, `y`, and the point (`04`, `x` and `y`)
under the flag; the specification's public key is `publicKey_eq`'s
(`Proof/EcKey/PublicKey.lean`).
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64.P256

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.P256
open VG.Proof.X25519.RISCV64 (Rest wp_and)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_nil writeBytes_append)

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point W) :=
  Spec.EcKey.publicKey Spec.P256.curve (ofBytes (bytesAt m d 32))

def pkRV : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 65⟩
    let d : Region := ⟨s.gpr .a1, 32⟩
    let scratch : Region := ⟨s.gpr .a2, 8192⟩
    s.rd = [d] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      (s.gpr .a0).toNat + 65 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8192 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat % 8 = 0
  post s s' :=
    match pk s.mem (s.gpr .a1) with
    | some (.affine x y) => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) 65 = Spec.EcKey.encodePoint (.affine x y)
    | _ => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) 65 = List.replicate 65 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2

/-- `pkRV` with the comb's table (`abi.withConsts`): `pkRV` for the state
without it, and what the table adds. -/
def pkRVC : Contract isa where
  pre s := pkRV.pre (stripConsts Impl.Ecdsa.RISCV64.Comb.p256CombConsts s) ∧
    ConstsOk Impl.Ecdsa.RISCV64.Comb.p256CombConsts 0 s
  post := pkRV.post
  pub s₁ s₂ := pkRV.pub s₁ s₂ ∧ s₁.syms Impl.Ecdsa.RISCV64.Comb.p256Sym = s₂.syms Impl.Ecdsa.RISCV64.Comb.p256Sym

/-- Bytes of a region apart from the working space, from an offset. -/
theorem sep_at {p base : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) (hn : p.toNat + n ≤ 2 ^ 64)
    {off k : Nat} (hk : off + k ≤ n) :
    ∀ i < k, ¬ (⟨base, 8192⟩ : Region).Contains (p + BitVec.ofNat 64 off + BitVec.ofNat 64 i) 1 := fun i hi => by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact out_of_disj hd hn (by omega)

theorem byte_eq (b : Bool) : (BitVec.ofNat 64 4 &&& maskOf b).setWidth 8 = if b then 4 else 0 := by
  cases b <;> decide

/-- `pointOut`: `04 ‖ x ‖ y` from the slots `xo` and `yo` (or zeros, by the
mask `a7`, which the flag holds) to `out`, the flag's low bit to `a0`, and
the saved registers restored. -/
theorem pointOut_ok {s : State} {base out : Addr} (hw : WsReg s base) (h2 : s.gpr .s2 = out)
    (hfit : out.toNat + 65 ≤ 2 ^ 64)
    (hout : ∀ i < 65, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hdis : (⟨out, 65⟩ : Region).Disjoint ⟨base, 8192⟩)
    {B : Bool} (ha7 : s.gpr .a7 = maskOf B) (hfl : word s.mem base FL = maskOf B)
    {xo yo : Nat} (hxo : xo < 44) (hyo : yo < 44) :
    WP isa (.block (pointOut p256 xo yo)) s fun s' =>
      s'.gpr .a0 = (if B then 1 else 0) ∧
      bytesAt s'.mem out 65 = (if B then 4 else 0) ::
        (toBytes 32 (if B then sv base s xo else 0) ++ toBytes 32 (if B then sv base s yo else 0)) ∧
      s'.gpr .s0 = word s.mem base 0 ∧ s'.gpr .s1 = word s.mem base 8 ∧ s'.gpr .s2 = word s.mem base 16 ∧
      s'.gpr .ra = word s.mem base 24 ∧ s'.gpr .s3 = word s.mem base 32 ∧
      (∀ r ∈ preserved, r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp := by
  have sl8 : ∀ i, p256.sl i % 8 = 0 := fun i => by rw [sl_eq]; omega
  have sl32 : ∀ {i}, i < 44 → p256.sl i + 8 * 4 ≤ 2048 := fun hi => by rw [sl_eq]; omega
  have ap : ∀ {i}, i < 44 → ∀ w ∈ [((8192 : Nat), (2 ^ 64 : Nat))], p256.sl i + 8 * 4 ≤ w.1 ∨ w.1 + w.2 ≤ p256.sl i :=
    fun hi w hw => by simp only [List.mem_singleton] at hw; subst hw; left; rw [sl_eq]; omega
  have fit : ∀ {i}, i < 44 → p256.sl i + 8 * 4 ≤ 2 ^ 64 := fun hi => by rw [sl_eq]; omega
  -- `04` under the mask.
  rw [pointOut, retCode, restoreCode, show p256.n = 4 from rfl, show 1 + 8 * 4 = 33 from rfl]
  simp only [List.append_assoc]
  rw [List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_li (imm := 4) (by decide) fun s₄ u₄ => wp_and fun s₅ u₅ => ?_
  refine wp_sb (off := 0) (a := out) (by decide) (by rw [u₅.other _ (by decide), u₄.other _ (by decide), h2,
    BitVec.add_zero]) (by rw [u₅.wr, u₄.wr]; simpa using hout 0 (by decide)) fun s₆ u₆ => ?_
  have hw₆ := ((hw.of_kp (Kp.of_upd u₄)).of_kp (Kp.of_upd u₅)).of_kp (Kp.of_mupd u₆)
  have v₆ : (s₅.gpr .t0).setWidth 8 = if B then 4 else 0 := by
    rw [u₅.gpr, u₄.gpr, u₄.other _ (by decide), ha7, byte_eq]
  have m₆ : s₆.mem = writeBytes s.mem out [if B then 4 else 0] := by
    rw [u₆.mem, v₆, u₅.mem, u₄.mem]
    have := writeBytes_snoc s.mem out [] (if B then 4 else 0) (by decide)
    rw [List.nil_append, writeBytes_nil] at this
    rw [this]; simp
  have q₆ : s₆.gpr .s2 = out := by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), h2]
  have wr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, u₄.wr]
  have a₆ : s₆.gpr .a7 = maskOf B := by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), ha7]
  have sp' : ∀ {off k : Nat}, off + k ≤ 65 → ∀ i < k,
      ¬ (⟨base, 8192⟩ : Region).Contains (out + BitVec.ofNat 64 off + BitVec.ofNat 64 i) 1 :=
    fun hk => sep_at hdis hfit hk
  have U₆ : Unch base [(8192, 2 ^ 64)] s.mem s₆.mem := by
    rw [m₆]; exact writeBytes_unch _ fun i hi => by
      have := sp' (off := 0) (k := 1) (by decide) i (by simpa using hi); simpa using this
  -- `x` and `y` under the mask.
  refine WP.block_append (WP.mono (storeNum_ok _ 4 hw₆ a₆ (q := .s2) (a := p256.sl xo) (off := 1) (by decide) (sl8 xo)
    (sl32 hxo) (by decide)
    (fun i hi => by rw [q₆, wr₆]; exact hout (1 + i) (by omega))
    (fun i hi => by rw [q₆]; exact out_of_disj hdis hfit (by omega))) fun s₇ ⟨r₇, m₇⟩ => ?_)
  have hw₇ := hw₆.of_rest r₇
  have q₇ : s₇.gpr .s2 = out := by rw [r₇.gpr _ (by decide), q₆]
  have a₇ : s₇.gpr .a7 = maskOf B := by rw [r₇.gpr _ (by decide), a₆]
  have xo₆ : wordsVal s₆.mem base (p256.sl xo) 4 = sv base s xo := U₆.wordsVal (ap hxo) (fit hxo)
  rw [q₆, xo₆] at m₇
  have U₇ : Unch base [(8192, 2 ^ 64)] s₆.mem s₇.mem := by
    rw [m₇]; exact writeBytes_unch _ fun i hi => sp' (off := 1) (k := 32) (by decide) i
      (by simpa [VG.Proof.Weierstrass.length_toBytes] using hi)
  refine WP.block_append (WP.mono (storeNum_ok _ 4 hw₇ a₇ (q := .s2) (a := p256.sl yo) (off := 33) (by decide) (sl8 yo)
    (sl32 hyo) (by decide)
    (fun i hi => by rw [q₇, r₇.wr, wr₆]; exact hout (33 + i) (by omega))
    (fun i hi => by rw [q₇]; exact out_of_disj hdis hfit (by omega))) fun s₈ ⟨r₈, m₈⟩ => ?_)
  have hw₈ := hw₇.of_rest r₈
  have yo₇ : wordsVal s₇.mem base (p256.sl yo) 4 = sv base s yo := by
    rw [U₇.wordsVal (ap hyo) (fit hyo)]; exact U₆.wordsVal (ap hyo) (fit hyo)
  rw [q₇, yo₇] at m₈
  have U₈ : Unch base [(8192, 2 ^ 64)] s₇.mem s₈.mem := by
    rw [m₈]; exact writeBytes_unch _ fun i hi => sp' (off := 33) (k := 32) (by decide) i
      (by simpa [VG.Proof.Weierstrass.length_toBytes] using hi)
  have U₃₈ := (U₆.trans U₇).trans U₈
  have wd : ∀ d, d + 8 ≤ 2048 → word s₈.mem base d = word s.mem base d := fun d hd =>
    U₃₈.word (by simp; omega) (by omega)
  have fl₈ : word s₈.mem base FL = maskOf B := by rw [wd FL (by decide), hfl]
  -- The bytes.
  have hX := VG.Proof.Weierstrass.length_toBytes 32 (if B = true then sv base s xo else 0)
  have hY := VG.Proof.Weierstrass.length_toBytes 32 (if B = true then sv base s yo else 0)
  have bytes₈ : bytesAt s₈.mem out 65 = (if B then 4 else 0) ::
      (toBytes 32 (if B then sv base s xo else 0) ++ toBytes 32 (if B then sv base s yo else 0)) := by
    have e1 := writeBytes_append s.mem out [if B then 4 else 0] (toBytes 32 (if B then sv base s xo else 0))
      (by rw [hX, List.length_singleton]; decide)
    have e2 := writeBytes_append s.mem out ([if B then 4 else 0] ++ toBytes 32 (if B then sv base s xo else 0))
      (toBytes 32 (if B then sv base s yo else 0)) (by simp only [List.length_append, List.length_singleton, hX, hY]; decide)
    simp only [List.length_singleton] at e1
    simp only [List.length_append, List.length_singleton, hX] at e2
    rw [m₈, m₇, m₆]
    rw [show (8 * 4 : Nat) = 32 from rfl, e1, e2]
    have := bytesAt_writeBytes s.mem out
      ([if B then 4 else 0] ++ toBytes 32 (if B then sv base s xo else 0) ++ toBytes 32 (if B then sv base s yo else 0))
      (by simp only [List.length_append, List.length_singleton, hX, hY]; decide)
    simp only [List.length_append, List.length_singleton, hX, hY] at this
    rw [this]; rfl
  -- The return value and the restores.
  refine ld_ws hw₈ (d := p256.sl FLAG) (by decide) (by decide) fun s₉ u₉ => ?_
  refine WP.cons (exec_logicImm (by decide)) ?_
  have u₉' := Upd.write s₉ .a0 (s₉.gpr .a0 &&& BitVec.ofInt 64 1)
  have hw₉ := (hw₈.of_kp (Kp.of_upd u₉)).of_kp (Kp.of_upd u₉')
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
  have mt : ∀ {t : State}, t.mem = s₈.mem → word t.mem base = word s₈.mem base := fun h => by rw [h]
  have M₄ : t₄.mem = s₈.mem := by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem, u₉'.mem, u₉.mem]
  have np : ∀ r ∈ preserved, r ∉ [Reg.t0, .t1, .t3, .t4, .a7, .a0, .ra] := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide),
      v₁.other _ (by decide), u₉'.gpr, u₉.gpr, sl_FLAG, fl₈, and_one]
  · rw [v₅.mem, M₄]; exact bytes₈
  · rw [v₅.gpr, M₄, wd 0 (by decide)]
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, v₂.mem, v₁.mem, u₉'.mem, u₉.mem,
      wd 8 (by decide)]
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.mem, u₉'.mem, u₉.mem,
      wd 16 (by decide)]
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr,
      u₉'.mem, u₉.mem, wd 24 (by decide)]
  · rw [v₅.other _ (by decide), v₄.gpr, v₃.mem, v₂.mem, v₁.mem, u₉'.mem, u₉.mem, wd 32 (by decide)]
  · intro r hr h0 h1 h2' h3'
    have hn := np r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rw [v₅.other _ h0, v₄.other _ h3', v₃.other _ h1, v₂.other _ h2', v₁.other _ hn.2.2.2.2.2.2,
      u₉'.other _ hn.2.2.2.2.2.1, u₉.other _ hn.2.2.2.2.2.1, r₈.gpr _ (by simp [hn.1, hn.2.1]),
      r₇.gpr _ (by simp [hn.1, hn.2.1]), u₆.gpr, u₅.other _ hn.1, u₄.other _ hn.1]
  · rw [v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, u₉'.sp, u₉.sp, r₈.sp, r₇.sp, u₆.sp, u₅.sp, u₄.sp]


/-- The end: the flag `&=` the mask of `Z ≠ 0`, the point (or zeros) to
`out`, the flag's low bit to `a0`, and the saved registers restored. -/
theorem finPk_ok {s : State} {base out : Addr} (hw : WsReg s base) (h2 : s.gpr .s2 = out)
    (hfit : out.toNat + 65 ≤ 2 ^ 64)
    (hout : ∀ i < 65, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hdis : (⟨out, 65⟩ : Region).Disjoint ⟨base, 8192⟩)
    {c : Bool} (hF : word s.mem base FL = maskOf c) :
    WP isa (.block (zCode p256 ++ pointOut p256 XO YO)) s fun s' =>
      s'.gpr .a0 = (if c && !decide (sv base s RZ = 0) then 1 else 0) ∧
      bytesAt s'.mem out 65 = (if c && !decide (sv base s RZ = 0) then 4 else 0) ::
        (toBytes 32 (if c && !decide (sv base s RZ = 0) then sv base s XO else 0) ++
          toBytes 32 (if c && !decide (sv base s RZ = 0) then sv base s YO else 0)) ∧
      s'.gpr .s0 = word s.mem base 0 ∧ s'.gpr .s1 = word s.mem base 8 ∧ s'.gpr .s2 = word s.mem base 16 ∧
      s'.gpr .ra = word s.mem base 24 ∧ s'.gpr .s3 = word s.mem base 32 ∧
      (∀ r ∈ preserved, r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp := by
  rw [zCode, show p256.n = 4 from rfl]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (zeroMask_ok hw (n := 4) (a := p256.sl RZ) (by decide) (by decide))
    fun s₁ ⟨r₁, m₁, g₁⟩ => ?_)
  rw [List.singleton_append]
  refine WP.cons (exec_logicImm (by decide)) ?_
  have r₁' := r₁.trans ((Upd.write s₁ .a7 (s₁.gpr .a7 ^^^ BitVec.ofInt 64 (-1))).rest (ws := [.t3, .t4, .a7])
    (by decide))
  have hw₁ := hw.of_rest r₁'
  refine WP.block_append (WP.mono (andFlag_ok hw₁) fun s₂ ⟨f₂, r₂, O₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  rw [List.singleton_append]
  refine ld_ws hw₂ (d := p256.sl FLAG) (by decide) (by decide) fun s₃ u₃ => ?_
  have hw₃ := hw₂.of_kp (Kp.of_upd u₃)
  generalize hB : (c && !decide (sv base s RZ = 0)) = B
  have hb : word s₂.mem base FL = maskOf B := by
    rw [f₂, ← hB]
    simp only [State.write, ↓reduceIte]
    rw [m₁, hF, g₁, not_mask, maskOf_and]
  have a₃ : s₃.gpr .a7 = maskOf B := by rw [u₃.gpr, sl_FLAG]; exact hb
  have wv₃ : ∀ i, i < 44 → i ≠ FLAG → wordsVal s₃.mem base (p256.sl i) 4 = sv base s i := fun i hi hf => by
    rw [u₃.mem, O₂.wordsVal (by rw [sl_eq, FL]; omega) (by rw [sl_eq]; omega)]
    show wordsVal (s₁.write _ _).mem _ _ _ = _
    simp only [State.write]; rw [m₁]
  have q₃ : s₃.gpr .s2 = out := by
    rw [u₃.other _ (by decide), r₂.gpr _ (by decide), r₁'.gpr _ (by decide), h2]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, r₂.wr, r₁'.wr]
  refine WP.mono (pointOut_ok hw₃ q₃ hfit (by rw [wr₃]; exact hout) hdis a₃ (by rw [u₃.mem]; exact hb)
    (xo := XO) (yo := YO) (by decide) (by decide))
    fun s' ⟨a0', b', s0', s1', s2', ra', s3', regs', sp'⟩ => ?_
  have w₃ : ∀ d, d + 8 ≤ FL ∨ FL + 8 ≤ d → d + 8 ≤ 2048 → word s₃.mem base d = word s.mem base d := fun d h hd => by
    rw [u₃.mem, O₂.word h (by omega)]
    show word (s₁.write _ _).mem _ _ = _
    simp only [State.write]; rw [m₁]
  have ex : sv base s₃ XO = sv base s XO := wv₃ XO (by decide) (by decide)
  have ey : sv base s₃ YO = sv base s YO := wv₃ YO (by decide) (by decide)
  refine ⟨a0', by rw [b', ex, ey],
    by rw [s0', w₃ 0 (by decide) (by decide)], by rw [s1', w₃ 8 (by decide) (by decide)],
    by rw [s2', w₃ 16 (by decide) (by decide)], by rw [ra', w₃ 24 (by decide) (by decide)],
    by rw [s3', w₃ 32 (by decide) (by decide)], fun r hr h0 h1 h2' h3' => ?_,
    by rw [sp', u₃.sp, r₂.sp, r₁'.sp]⟩
  have hn : r ∉ [Reg.t0, .t1, .t3, .t4, .a7] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> exact absurd hr (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  rw [regs' r hr h0 h1 h2' h3', u₃.other _ hn.2.2.2.2, r₂.gpr _ (by simp [hn.1]),
    r₁'.gpr _ (by simp [hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2])]

theorem publicKey_none {C : Curve} {d : Nat} (h : ¬ (1 ≤ d ∧ d < C.n)) : Spec.EcKey.publicKey C d = none := by
  unfold Spec.EcKey.publicKey; simp only [h, ↓reduceIte]

/-- `vg_ec_p256_public_key` by register. -/
theorem pk_ok (hL : VG.Proof.Weierstrass.Law W) {s : State} (hs : pkRVC.pre s) :
    WP isa publicKeyP256 s fun s' => abiPreserved s s' ∧ pkRV.post s s' := by
  obtain ⟨⟨hrd, hwr, hod, hdd, hfo, hfd, hfs, hal⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr] at hrd hwr hod hdd hfo hfd hfs hal
  have hp0 : 0 < W.p := by decide
  rw [publicKeyP256, Cfg.publicKeyFn, show p256.n = 4 from rfl]
  simp only [List.append_assoc]
  generalize hb : s.gpr .a2 = base at hwr hod hdd hfs hal
  have hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have hT₀ : VG.Proof.Ecdsa.RISCV64.Comb.TabAt base s := VG.Proof.Ecdsa.RISCV64.Comb.tabAt_of_consts hk hwr'
  refine WP.seq (VG.Proof.Ecdsa.RISCV64.Comb.wp_syms_frame (WP.block_append (WP.mono (save_ok hb hwr' hfs hal)
    fun s₁ ⟨hw₁, h3₁, o₁, g₁, rd₁, wr₁, sp₁, U₁, w0, w1, w2, w3, w4⟩ => ?_)))
  have a1 : s₁.gpr .a1 = s.gpr .a1 := g₁ _ (by decide) (by decide) (by decide)
  have rd1 : (⟨s.gpr .a1, 32⟩ : Region) ∈ s₁.rd ++ s₁.wr := by
    rw [rd₁]; exact List.mem_append_left _ (stripConsts_rd_mem (by rw [hrd]; simp))
  -- `d`.
  refine WP.block_append (WP.mono (loadNum_ok 4 hw₁ (o := p256.sl K) (p := .a1) (off := 0) (by decide) (by decide)
    (by decide) (by decide) (fun j hj => by rw [a1]; exact in_rd8 rd1 (by omega))
    (fun i hi => by rw [a1]; exact out_of_disj hdd hfd (by omega)))
    fun s₂ ⟨r₂, O₂, e₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  -- The flag.
  rw [List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_li (imm := 0) (by decide) fun s₂a u₂a => ?_
  refine WP.cons (exec_addi (by decide)) ?_
  have u₂b := Upd.write s₂a .t0 (s₂a.gpr .t0 + BitVec.ofInt 64 (-1))
  have hw₂b := (hw₂.of_kp (Kp.of_upd u₂a)).of_kp (Kp.of_upd u₂b)
  refine sd_ws hw₂b (d := p256.sl FLAG) (by decide) (by decide) fun s₃ u₃ => ?_
  have hw₃ := hw₂b.of_kp (Kp.of_mupd u₃)
  have fl₃ : word s₃.mem base FL = maskOf true := by
    rw [u₃.mem, sl_FLAG, word_writeW_self, u₂b.gpr, u₂a.gpr]; decide
  -- The constants, and `G` to `R`.
  rw [constCode_eq]
  refine WP.block_append (WP.mono (consts_ok _ hw₃ consts_slots consts_nodup) fun s₄ ⟨r₄, U₄, e₄⟩ => ?_)
  have hw₄ := hw₃.of_rest r₄
  have cs₄ : ∀ e ∈ consts p256, sv base s₄ e.1 = e.2 := fun e he => by
    rw [e₄ e he, Nat.mod_eq_of_lt (consts_lt e he)]
  refine WP.block_append (WP.mono (copy_ok 4 hw₄ (o := p256.sl RX) (a := p256.sl GX) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₅ ⟨v₅, r₅, O₅⟩ => ?_)
  have hw₅ := hw₄.of_rest r₅
  refine WP.mono (copy_ok 4 hw₅ (o := p256.sl RY) (a := p256.sl GY) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₆ ⟨v₆, r₆, O₆⟩ sy₆ F₆ => ?_
  have hw₆ := hw₅.of_rest r₆
  have rd₆ : s₆.rd = s.rd := by rw [r₆.rd, r₅.rd, r₄.rd, u₃.rd, u₂b.rd, u₂a.rd, r₂.rd, rd₁]
  have hT₆ : VG.Proof.Ecdsa.RISCV64.Comb.TabAt base s₆ := hT₀.of_frame sy₆ rd₆ F₆ (VG.Proof.Ecdsa.RISCV64.Comb.tab_wr_of_consts hk)
  have U₄₆ := (U₄.trans O₅.unch).trans O₆.unch
  have tc₄ : TailConsts base s₄ := ⟨const_at cs₄ 0, const_at cs₄ 1, const_at cs₄ 2, const_at cs₄ 3,
    const_at cs₄ 4, const_at cs₄ 5, const_at cs₄ 6, const_at cs₄ 9⟩
  have tc₆ := tc₄.of_unch (O₅.unch.trans O₆.unch) (by decide)
  have rx₆ : sv base s₆ RX = W.gx * 2 ^ 256 % W.p := by
    show wordsVal _ _ _ _ = _
    rw [O₆.wordsVal (by decide) (by decide), v₅]; exact const_at cs₄ 7
  have ry₆ : sv base s₆ RY = W.gy * 2 ^ 256 % W.p := by
    show wordsVal _ _ _ _ = _
    rw [v₆, O₅.wordsVal (by decide) (by decide)]; exact const_at cs₄ 8
  have hon : Spec.Weierstrass.onCurve W (.affine (toM W.p (2 ^ 256) (sv base s₆ RX))
      (toM W.p (2 ^ 256) (sv base s₆ RY))) = true := by
    rw [rx₆, ry₆, toM_mont unit, toM_mont unit]; exact VG.Proof.P256.onCurve_G
  have h3₆ : s₆.gpr .s3 = base := by
    rw [r₆.gpr _ (by decide), r₅.gpr _ (by decide), r₄.gpr _ (by decide), u₃.gpr, u₂b.other _ (by decide),
      u₂a.other _ (by decide), r₂.gpr _ (by decide), h3₁]
  -- `[d]G`, `Z^(p-2)` and `x`.
  refine WP.seq (WP.mono (VG.Proof.Ecdsa.RISCV64.Comb.tailG_ok hL hw₆ h3₆ tc₆ rx₆ ry₆ hT₆)
    fun s₇ ⟨Kc₇, U₇, f₇, rep₇, xolt, xoeq, acclt, acceq⟩ => ?_)
  have hw₇ := hw₆.of_kc Kc₇
  have one₇ : sv base s₇ ONE = 1 := by show wordsVal _ _ _ _ = _; rw [sv_unch U₇ ONE (by decide)]; exact tc₆.one
  -- `y`.
  refine WP.seq (WP.mono (affine_ok hw₇ (t := YM) (o := YO) (a := RY) (by decide) (by decide) (by decide)
    (by decide) acclt one₇) fun s₈ ⟨K₈, U₈, lt₈, v₈⟩ => ?_)
  have hw₈ := hw₇.of_kp K₈
  -- The end.
  have hn0 : ∀ r ∈ [Reg.t0], r ∉ preserved := by decide
  have hn1 : ∀ r ∈ [Reg.t0, .t1], r ∉ preserved := by decide
  have K₁₆ : ∀ r ∈ preserved, s₆.gpr r = s₁.gpr r := fun r hr => by
    have h0 : r ∉ [Reg.t0] := fun h => hn0 r h hr
    have h1 : r ∉ [Reg.t0, .t1] := fun h => hn1 r h hr
    rw [r₆.gpr _ h0, r₅.gpr _ h0, r₄.gpr _ h1, u₃.gpr, u₂b.other _ (by rintro rfl; exact absurd hr (by decide)),
      u₂a.other _ (by rintro rfl; exact absurd hr (by decide)), r₂.gpr _ h1]
  have h2₈ : s₈.gpr .s2 = s.gpr .a0 := by
    rw [K₈.gpr _ (by decide), Kc₇.gpr _ (by decide) (by decide), K₁₆ _ (by decide), o₁]
  have wr₈ : s₈.wr = s.wr := by rw [K₈.wr, Kc₇.wr, r₆.wr, r₅.wr, r₄.wr, u₃.wr, u₂b.wr, u₂a.wr, r₂.wr, wr₁]
  have O₃ : Unch base [(FL, 8)] s₂.mem s₃.mem := by
    rw [u₃.mem, u₂b.mem, u₂a.mem, sl_FLAG]; exact (writeW_outside _ _ _ (by decide)).unch
  have U₁₈ := ((((O₂.unch.trans O₃).trans U₄₆).trans U₇).trans U₈)
  have k₆ : sv base s₆ K = ofBytes (bytesAt s.mem (s.gpr .a1) 32) := by
    show wordsVal _ _ _ _ = _
    rw [sv_unch (O₃.trans U₄₆) K (by decide), e₂, a1, BitVec.add_zero,
      bytesAt_unch U₁ (by decide) (by simpa using sep_at hdd hfd (off := 0) (k := 32) (by omega))]
  have fl₈ : word s₈.mem base FL = maskOf ((true && decide (ofBytes (bytesAt s.mem (s.gpr .a1) 32) < W.n)) &&
      !decide (ofBytes (bytesAt s.mem (s.gpr .a1) 32) = 0)) := by
    rw [U₈.word (by decide) (by decide), f₇, U₄₆.word (by decide) (by decide), fl₃, k₆, maskOf_and, maskOf_and]
  refine WP.mono (finPk_ok hw₈ h2₈ hfo (fun i hi => by
      rw [wr₈, hwr]
      exact ⟨_, List.mem_cons_self .., Offset.contains_base (s.gpr .a0) (d := i) (n := 1) (k := 65) (by omega)
        (by omega)⟩) hod fl₈)
    fun s' ⟨a0', bytes', s0', s1', s2', ra', s3', regs', sp'⟩ => ?_
  -- The registers.
  refine ⟨⟨fun r hr => ?_, by rw [sp', K₈.sp, Kc₇.sp, r₆.sp, r₅.sp, r₄.sp, u₃.sp, u₂b.sp, u₂a.sp, r₂.sp, sp₁],
    by rw [ra', U₁₈.word (by decide) (by decide), w3]⟩, ?_⟩
  · by_cases h0 : r = .s0
    · subst h0; rw [s0', U₁₈.word (by decide) (by decide), w0]
    by_cases h1 : r = .s1
    · subst h1; rw [s1', U₁₈.word (by decide) (by decide), w1]
    by_cases h2' : r = .s2
    · subst h2'; rw [s2', U₁₈.word (by decide) (by decide), w2]
    by_cases h3' : r = .s3
    · subst h3'; rw [s3', U₁₈.word (by decide) (by decide), w4]
    rw [regs' r hr h0 h1 h2' h3', K₈.gpr r hr, Kc₇.gpr r hr h1, K₁₆ r hr, g₁ r h0 h2' h3']
  -- The specification.
  have xo₈ : sv base s₈ XO = sv base s₇ XO := sv_unch U₈ XO (by decide)
  have rz₈ : sv base s₈ RZ = sv base s₇ RZ := sv_unch U₈ RZ (by decide)
  rw [acceq] at v₈
  rw [rz₈] at a0'
  rw [xo₈, rz₈] at bytes'
  generalize hD : ofBytes (bytesAt s.mem (s.gpr .a1) 32) = D at a0' bytes' k₆
  rw [k₆] at rep₇
  have hpk : pk s.mem (s.gpr .a1) = Spec.EcKey.publicKey W D := by rw [← hD]
  unfold pkRV
  simp only
  rw [hpk]
  have z65 : (0 : Byte) :: (toBytes 32 0 ++ toBytes 32 0) = List.replicate 65 0 := by decide
  by_cases hd : 1 ≤ D ∧ D < W.n
  · obtain ⟨hR, -, -, rzlt⟩ := rep₇ hd.1 hd.2
    have eG : Point.affine (toM W.p (2 ^ 256) (sv base s₆ RX)) (toM W.p (2 ^ 256) (sv base s₆ RY)) =
        Spec.Weierstrass.G W := by
      rw [rx₆, ry₆, toM_mont unit, toM_mont unit]; rfl
    rw [eG] at hR
    have hn : decide (D < W.n) = true := decide_eq_true hd.2
    have h0 : decide (D = 0) = false := decide_eq_false (by omega)
    rw [hn, h0] at a0' bytes'
    have hpk' := VG.Proof.EcKey.publicKey_eq hL hR xolt xoeq lt₈ v₈
    rw [ite_eq_left hd] at hpk'
    by_cases hz : sv base s₇ RZ = 0
    · rw [ite_eq_left ((toM_eq_zero_iff unit rzlt).mpr hz)] at hpk'
      rw [hpk']
      rw [decide_eq_true hz] at a0' bytes'
      exact ⟨a0', bytes'.trans z65⟩
    · rw [ite_eq_right fun h => hz ((toM_eq_zero_iff unit rzlt).mp h)] at hpk'
      rw [hpk']
      rw [decide_eq_false hz] at a0' bytes'
      exact ⟨a0', bytes'⟩
  · rw [publicKey_none hd]
    have hb : ((true && decide (D < W.n)) && !decide (D = 0)) = false := by
      by_cases hn : D < W.n
      · have : D = 0 := by omega
        simp [this]
      · simp [hn]
    rw [hb] at a0' bytes'
    exact ⟨a0', bytes'.trans z65⟩

theorem pk_rv (hL : VG.Proof.Weierstrass.Law W) (s : State) (hs : pkRVC.pre s) :
    ∃ t s', Exec isa publicKeyP256 s t s' ∧ abiPreserved s s' ∧ pkRVC.post s s' := by
  obtain ⟨t, s', he, h⟩ := pk_ok hL hs
  exact ⟨t, s', he, h⟩

end VG.Proof.Ecdh.RISCV64.P256
