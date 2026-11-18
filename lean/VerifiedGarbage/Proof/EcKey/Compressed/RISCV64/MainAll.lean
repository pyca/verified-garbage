module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.PublicKeyAll
public import VerifiedGarbage.Impl.EcKey.Compressed.RISCV64
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
import VerifiedGarbage.Proof.EcKey.Compressed.Encode
import VerifiedGarbage.Proof.EcKey.Compressed.Decode
import VerifiedGarbage.Impl.EcKey.Compressed.Root
import VerifiedGarbage.Proof.Weierstrass.Sqrt
import VerifiedGarbage.Proof.EcKey.Compressed.Parity
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Weierstrass.Words

/-!
# SEC 1 point compression and decompression on RISC-V: correctness, for every curve

`vg_ec_<curve>_compress_public_key` meets its contract by register
(`Kit.compress_ok`), once for every curve, over the curve's `Kit` of ECDH
(`Proof/Ecdh/RISCV64/ExchangeAll.lean`): ECDH's saves and its reading of the
point, the flag and the constants (`Kit.peerLoad_ok`), the check of the point
(`Kit.check_ok`), and `02 + (y mod 2)` and `x` (or zeros) under the flag; the
specification's encoding is `compress_eq`'s
(`Proof/EcKey/Compressed/Encode.lean`).

`vg_ec_<curve>_decompress_public_key` meets its contract for a prime
`p ≡ 3 (mod 4)` (`Kit.decompress_ok`): the setup (`Kit.dsetup_ok`),
`rhs = x³ + a x + b` (`Kit.rhs_ok`), its root's candidate by the power,
`y² - rhs` and `y` or `p - y` (`Kit.root_ok`), and the checks into the flag,
the root's choice and the point (`Kit.dfin_ok`). Each `<Curve>/Main.lean` states
them of its curve; P-224, whose `p ≡ 1 (mod 4)`, has its own root and uses the
pieces.
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg VG.Impl.EcKey.Compressed.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.X25519.RISCV64 (Rest wp_and)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_nil writeBytes_append)

/-- Slot arithmetic: the offsets of slots given by number, with the kit's bounds on the words. -/
local macro "kit_slots" E:term : tactic => `(tactic| (
  simp only [Cfg.sl, slot, MP, MN, ZERO, ONE, ONEP, AP, B3P, GX, GY, EXPP, R2P, BP, K, FLAG, RX, RY, RZ, XO, YO, YM,
    CX, CY, CXM, ACC, PT, PAR, EXPS, RHS, TT, YSQ, DIF, Y1, Y2, YF, T0, T1, T2, T3]
  omega_using [TKit.n9 (Kit.toTKit $E), TKit.n4 (Kit.toTKit $E)]))

/-- `∀ w ∈ W, P w` for ranges `W` given as a list of lists: `t` proves it of each. -/
local macro "kit_ranges" t:tacticSeq : tactic =>
  `(tactic| ((repeat' first | with_reducible apply Kit.all_app | with_reducible apply Kit.all_one); all_goals ($t)))

/-- A slot apart from ranges that are other slots, the flag or the constants. -/
local macro "kit_apart" E:term : tactic =>
  `(tactic| kit_ranges (first
    | exact Kit.sl_sep _ (by decide)
    | exact Or.inl (Kit.sl_le _ (by decide))
    | exact Kit.apart_consts _ (by decide)
    | kit_slots $E))

namespace Kit

variable (E : Kit)

/-! ## Compression -/

/-- `vg_ec_<curve>_compress_public_key`, as the kit reads and writes its numbers. -/
def compProg : Prog isa :=
  .seq (.block (saveCode .a2 ++ E.load (E.c.sl CX) .a1 1 ++ E.load (E.c.sl CY) .a1 (1 + E.L) ++
    leadMask .a1 ++ sdAt .a7 wb (E.c.sl FLAG) ++ constCode E.c)) <|
  .seq (wsCall E.checkN E.checkC) <|
  .block (ldAt .a7 wb (E.c.sl FLAG) ++ ldAt .t0 wb (E.c.sl CY) ++ [.logicImm .and .t0 .t0 1, .addi .t0 .t0 2,
      .logic .and .t0 .t0 .a7, .store .b .t0 .s2 0] ++ E.store (E.c.sl CX) .s2 1 ++ retCode E.c)

/-- `vg_ec_<curve>_compress_public_key(out = a0, public = a1, scratch = a2)`'s
precondition, by register. -/
def CompPre (s : State) : Prop :=
  let out : Region := ⟨s.gpr .a0, 1 + E.L⟩
  let pk : Region := ⟨s.gpr .a1, 1 + 2 * E.L⟩
  let ws : Region := ⟨s.gpr .a2, 8192⟩
  s.rd = [pk] ∧ s.wr = [out, ws] ∧ pk.Disjoint out ∧ pk.Disjoint ws ∧ out.Disjoint ws ∧
    (s.gpr .a0).toNat + (1 + E.L) ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + (1 + 2 * E.L) ≤ 2 ^ 64 ∧
    (s.gpr .a2).toNat + 8192 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat % 8 = 0

/-- What it returns. -/
def compPost (s s' : State) : Prop :=
  match Spec.EcKey.compressPublicKey E.c.C (bytesAt s.mem (s.gpr .a1) (1 + 2 * E.L)) with
  | some bs => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) (1 + E.L) = bs
  | none => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) (1 + E.L) = List.replicate (1 + E.L) 0

theorem n1 : 0 < E.c.n := Nat.lt_of_lt_of_le (by decide) E.n4

theorem tag_eq (m : Mem) (base : Addr) (B : Bool) :
    ((((word m base (E.c.sl CY) &&& BitVec.ofInt 64 1) + BitVec.ofInt 64 2) &&& maskOf B).setWidth 8) =
      if B then BitVec.ofNat 8 (2 + wordsVal m base (E.c.sl CY) E.c.n % 2) else 0 :=
  VG.Proof.EcKey.Compressed.tag_byte m base (E.c.sl CY) E.c.n E.n1 B

/-- The check keeps the point it reads. -/
theorem check_xy : ∀ i ∈ [CX, CY], ∀ w ∈ E.checkKW, E.c.sl i + 8 * E.c.n ≤ w.1 ∨ w.1 + w.2 ≤ E.c.sl i := by
  obtain h9 := E.n9
  obtain hown : 64 + 8 * E.c.n * 45 + 8 ≤ own E.c.n := own_ge h9
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;>
    (simp only [checkKW, TKit.checkKW, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Cfg.sl, slot, CX, CY, FLAG]; omega_using [h9, hown])

/-- The peer's point's setup writes above the saves. -/
theorem peer_lo : ∀ w ∈ E.peerW, 40 ≤ w.1 := by
  kit_ranges (first | exact lo_consts _ | exact Nat.le_trans (by decide) (sl_lo _ _))

/-- `vg_ec_<curve>_compress_public_key` by register. -/
theorem compress_ok {s : State} (hs : E.CompPre s) :
    WP isa E.compProg s fun s' => abiPreserved s s' ∧ E.compPost s s' := by
  obtain ⟨hrd, hwr, hpo, hpw, how, hfo, hfp, hfs, hal⟩ := hs
  obtain hL := E.Ln
  obtain h9 := E.n9
  obtain fit : ∀ {i}, i < 45 → E.c.sl i + 8 * E.c.n ≤ 4096 := fun hi => sl_top h9 (by omega_using [hi])
  rw [compProg]
  generalize hb : s.gpr .a2 = base at hwr hpw how hfs hal
  obtain hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (TKit.save_ok hb hwr' hfs hal)
    fun s₁ ⟨hw₁, h3₁, o₁, g₁, rd₁, wr₁, sp₁, U₁, w0, w1, w2, w3, w4⟩ => ?_))
  obtain a1 : s₁.gpr .a1 = s.gpr .a1 := g₁ _ (by decide) (by decide) (by decide)
  simp only [← List.append_assoc]
  refine WP.mono (E.peerLoad_ok hw₁ (q := .a1) (by decide) (by rw [rd₁, wr₁, a1, hrd]; simp)
    (by rw [a1]; exact hpw) (by rw [a1]; exact hfp)) fun s₂ ⟨hw₂, r₂, U₂, x₂, y₂, f₂, c₂⟩ => ?_
  obtain h3₂ : s₂.gpr .s3 = base := by rw [r₂.gpr _ (by decide), h3₁]
  obtain hf₂ : word s₂.mem base (E.c.sl FLAG) = 0 ∨ word s₂.mem base (E.c.sl FLAG) = BitVec.allOnes 64 := by
    rw [f₂]; unfold maskOf; split <;> simp
  -- The check.
  refine WP.seq (WP.mono (E.check_ok hw₂ h3₂ c₂ hf₂) fun s₃ ⟨K₃, U₃, f₃, _, _⟩ => ?_)
  obtain hw₃ := hw₂.of_kp K₃
  obtain q₃ : s₃.gpr .s2 = s.gpr .a0 := by rw [K₃.gpr _ (by decide), r₂.gpr _ (by decide), o₁]
  obtain wr₃ : s₃.wr = s.wr := by rw [K₃.wr, r₂.wr, wr₁]
  generalize hout : s.gpr .a0 = out at q₃ hwr hpo how hfo
  have hdis : (⟨out, 1 + E.L⟩ : Region).Disjoint ⟨base, 8192⟩ := how
  -- The values.
  obtain x₁ : sv E.c base s₂ CX = ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) E.L) := by
    rw [x₂, a1, bytesAt_unch U₁ (by decide) (sep_at' hpw hfp (off := 1) (k := E.L) (by omega_using []))]
  obtain y₁ : sv E.c base s₂ CY = ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 (1 + E.L)) E.L) := by
    rw [y₂, a1, bytesAt_unch U₁ (by decide) (sep_at' hpw hfp (off := 1 + E.L) (k := E.L) (by omega_using []))]
  obtain b₁ : s₁.mem (s₁.gpr .a1) = s.mem (s.gpr .a1) := by
    obtain h1 := bytesAt_unch U₁ (q := s.gpr .a1) (n := 1) (by decide)
      (by simpa using sep_at' hpw hfp (off := 0) (k := 1) (by omega_using []))
    simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h1
    simp only [BitVec.add_zero] at h1
    rw [a1, h1]
  generalize hx : sv E.c base s₂ CX = x at x₁ f₃
  generalize hy : sv E.c base s₂ CY = y at y₁ f₃
  generalize hB : (decide (s.mem (s.gpr .a1) = 4) && decide (E.CC.Valid x y)) = B
  obtain fl₃ : word s₃.mem base (E.c.sl FLAG) = maskOf B := by
    rw [f₃, f₂, b₁, mask_eq, maskOf_and, hB]
  obtain cy₃ : wordsVal s₃.mem base (E.c.sl CY) E.c.n = y := by
    rw [U₃.wordsVal (E.check_xy CY (by decide)) (Nat.le_trans (fit (by decide)) (by decide))]; exact hy
  obtain cx₃ : wordsVal s₃.mem base (E.c.sl CX) E.c.n = x := by
    rw [U₃.wordsVal (E.check_xy CX (by decide)) (Nat.le_trans (fit (by decide)) (by decide))]; exact hx
  -- The first byte.
  rw [retCode, restoreCode]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine ldAt_ws hw₃ (d := E.c.sl FLAG) (by kit_slots E) (sl8 _ _) fun s₄ u₄ => ?_
  obtain hw₄ := hw₃.of_kp (Kp.of_upd u₄)
  refine ldAt_ws hw₄ (d := E.c.sl CY) (by kit_slots E) (sl8 _ _) fun s₅ u₅ => ?_
  refine WP.cons (exec_logicImm (by decide)) ?_
  obtain u₅a := Upd.write s₅ .t0 (s₅.gpr .t0 &&& BitVec.ofInt 64 1)
  refine WP.cons (exec_addi (by decide)) ?_
  obtain u₅b := Upd.write (s₅.write .t0 (s₅.gpr .t0 &&& BitVec.ofInt 64 1)) .t0
    ((s₅.write .t0 (s₅.gpr .t0 &&& BitVec.ofInt 64 1)).gpr .t0 + BitVec.ofInt 64 2)
  refine wp_and fun s₆ u₆ => ?_
  obtain hw₆ := ((((hw₄.of_kp (Kp.of_upd u₅)).of_kp (Kp.of_upd u₅a)).of_kp (Kp.of_upd u₅b))).of_kp (Kp.of_upd u₆)
  obtain q₆ : s₆.gpr .s2 = out := by
    rw [u₆.other _ (by decide), u₅b.other _ (by decide), u₅a.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), q₃]
  obtain wr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅b.wr, u₅a.wr, u₅.wr, u₄.wr, wr₃]
  obtain a₆ : s₆.gpr .a7 = maskOf B := by
    rw [u₆.other _ (by decide), u₅b.other _ (by decide), u₅a.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      fl₃]
  obtain v₆ : (s₆.gpr .t0).setWidth 8 = if B then BitVec.ofNat 8 (2 + y % 2) else 0 := by
    rw [u₆.gpr, u₅b.gpr, u₅b.other _ (by decide), u₅a.gpr, u₅a.other _ (by decide), u₅.gpr, u₄.mem,
      u₅.other _ (by decide), u₄.gpr, fl₃, E.tag_eq, cy₃]
  obtain hout' : ∀ i < 1 + E.L, InRegions s.wr (out + BitVec.ofNat 64 i) 1 := fun i hi => by
    rw [hwr]
    exact ⟨_, List.mem_cons_self .., Offset.contains_base out (d := i) (n := 1) (k := 1 + E.L) (by omega_using [hi])
      (by omega_using [hi, hL, h9])⟩
  refine wp_sb (off := 0) (a := out) (by decide) (by rw [q₆, BitVec.add_zero])
    (by rw [wr₆]; simpa using hout' 0 (by omega_using [])) fun s₇ u₇ => ?_
  obtain hw₇ := hw₆.of_kp (Kp.of_mupd u₇)
  obtain m₇ : s₇.mem = writeBytes s₃.mem out [if B then BitVec.ofNat 8 (2 + y % 2) else 0] := by
    rw [u₇.mem, v₆, u₆.mem, u₅b.mem, u₅a.mem, u₅.mem, u₄.mem]
    have := writeBytes_snoc s₃.mem out [] (if B then BitVec.ofNat 8 (2 + y % 2) else 0) (by decide)
    rw [List.nil_append, writeBytes_nil] at this
    rw [this]; simp
  obtain sp' : ∀ {off k : Nat}, off + k ≤ 1 + E.L → ∀ i < k,
      ¬ (⟨base, 8192⟩ : Region).Contains (out + BitVec.ofNat 64 off + BitVec.ofNat 64 i) 1 :=
    fun hk => sep_at' hdis hfo hk
  obtain U₇ : Unch base [(8192, 2 ^ 64)] s₃.mem s₇.mem := by
    rw [m₇]; exact writeBytes_unch _ fun i hi => by
      have := sp' (off := 0) (k := 1) (by omega_using []) i (by simpa using hi); simpa using this
  obtain q₇ : s₇.gpr .s2 = out := by rw [u₇.gpr, q₆]
  obtain a₇ : s₇.gpr .a7 = maskOf B := by rw [u₇.gpr, a₆]
  obtain ap : ∀ {i}, i < 45 → ∀ w ∈ [((8192 : Nat), (2 ^ 64 : Nat))],
      E.c.sl i + 8 * E.c.n ≤ w.1 ∨ w.1 + w.2 ≤ E.c.sl i :=
    fun hi => all_one (.inl (Nat.le_trans (fit hi) (by decide)))
  -- `x`.
  refine WP.block_append (WP.mono (E.store_ok _ (i := CX) (q := .s2) (off := 1) hw₇ a₇ (by decide) (by decide)
    (by omega_using [hL, h9])
    (fun i hi => by rw [q₇, u₇.wr, wr₆]; exact hout' (1 + i) (by omega_using [hi]))
    (fun i hi => by rw [q₇]; exact out_of_disj hdis hfo (by omega_using [hi]))) fun s₈ ⟨r₈, m₈⟩ => ?_)
  obtain hw₈ := hw₇.of_rest r₈
  obtain xo₇ : wordsVal s₇.mem base (E.c.sl CX) E.c.n = x := by
    rw [U₇.wordsVal (ap (by decide)) (Nat.le_trans (fit (by decide)) (by decide)), cx₃]
  rw [q₇, xo₇] at m₈
  obtain U₈ : Unch base [(8192, 2 ^ 64)] s₇.mem s₈.mem := by
    rw [m₈]; exact writeBytes_unch _ fun i hi => sp' (off := 1) (k := E.L) (by omega_using []) i
      (by simpa [VG.Proof.Weierstrass.length_toBytes] using hi)
  obtain U₃₈ := U₇.trans U₈
  obtain hX := VG.Proof.Weierstrass.length_toBytes E.L (if B = true then x else 0)
  obtain bytes₈ : bytesAt s₈.mem out (1 + E.L) = (if B then BitVec.ofNat 8 (2 + y % 2) else 0) ::
      toBytes E.L (if B then x else 0) := by
    obtain e1 := writeBytes_append s₃.mem out [if B then BitVec.ofNat 8 (2 + y % 2) else 0]
      (toBytes E.L (if B then x else 0)) (by rw [hX, List.length_singleton]; omega_using [hL, h9])
    simp only [List.length_singleton] at e1
    rw [m₈, m₇, e1]
    have := bytesAt_writeBytes s₃.mem out
      ([if B then BitVec.ofNat 8 (2 + y % 2) else 0] ++ toBytes E.L (if B then x else 0))
      (by simp only [List.length_append, List.length_singleton, hX]; omega_using [hL, h9])
    simp only [List.length_append, List.length_singleton, hX] at this
    rw [this]; rfl
  -- The return value and the restores.
  obtain wd : ∀ d, d + 8 ≤ 40 → word s₈.mem base d = word s₁.mem base d := fun d hd => by
    rw [U₃₈.word (by simp; omega_using [hd]) (by omega_using [hd]), lo_word U₃ E.check_lo hd, lo_word U₂ E.peer_lo hd]
  obtain fl₈ : word s₈.mem base (E.c.sl FLAG) = maskOf B := by
    rw [U₃₈.word (by simp; kit_slots E) (by kit_slots E), fl₃]
  refine ldAt_ws hw₈ (d := E.c.sl FLAG) (by kit_slots E) (sl8 _ _) fun s₉ u₉ => ?_
  refine WP.cons (exec_logicImm (by decide)) ?_
  obtain u₉' := Upd.write s₉ .a0 (s₉.gpr .a0 &&& BitVec.ofInt 64 1)
  obtain hw₉ := (hw₈.of_kp (Kp.of_upd u₉)).of_kp (Kp.of_upd u₉')
  refine ld_ws hw₉ (d := 24) (by decide) (by decide) fun t₁ v₁ => ?_
  obtain hv₁ := hw₉.of_kp (Kp.of_upd v₁)
  refine ld_ws hv₁ (d := 16) (by decide) (by decide) fun t₂ v₂ => ?_
  obtain hv₂ : WsReg t₂ base := ⟨by rw [v₂.other _ (by decide)]; exact hv₁.s0, by rw [v₂.wr]; exact hv₁.wr,
    hv₁.nowrap, hv₁.al⟩
  refine ld_ws hv₂ (d := 8) (by decide) (by decide) fun t₃ v₃ => ?_
  obtain hv₃ : WsReg t₃ base := ⟨by rw [v₃.other _ (by decide)]; exact hv₂.s0, by rw [v₃.wr]; exact hv₂.wr,
    hv₂.nowrap, hv₂.al⟩
  refine ld_ws hv₃ (d := 32) (by decide) (by decide) fun t₄ v₄ => ?_
  obtain hv₄ : WsReg t₄ base := ⟨by rw [v₄.other _ (by decide)]; exact hv₃.s0, by rw [v₄.wr]; exact hv₃.wr,
    hv₃.nowrap, hv₃.al⟩
  refine ld_ws hv₄ (d := 0) (by decide) (by decide) fun t₅ v₅ => WP.block_nil ?_
  obtain M₄ : t₄.mem = s₈.mem := by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem, u₉'.mem, u₉.mem]
  obtain np : ∀ r ∈ preserved, r ∉ [Reg.t0, .t1, .a7, .a0, .ra] := by decide
  obtain gp : ∀ r ∈ preserved, r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → t₅.gpr r = s.gpr r := by
    intro r hr h0 h1 h2' h3'
    obtain hn := np r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rw [v₅.other _ h0, v₄.other _ h3', v₃.other _ h1, v₂.other _ h2', v₁.other _ hn.2.2.2.2,
      u₉'.other _ hn.2.2.2.1, u₉.other _ hn.2.2.2.1, r₈.gpr _ (by simp [hn.1, hn.2.1]), u₇.gpr,
      u₆.other _ hn.1, u₅b.other _ hn.1, u₅a.other _ hn.1, u₅.other _ hn.1, u₄.other _ hn.2.2.1,
      K₃.gpr _ hr, r₂.gpr _ (by simp [hn.1, hn.2.1, hn.2.2.1]), g₁ _ h0 h2' h3']
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · by_cases h0 : r = .s0
    · subst h0; rw [v₅.gpr, M₄, wd 0 (by decide), w0]
    by_cases h1 : r = .s1
    · subst h1
      rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, v₂.mem, v₁.mem, u₉'.mem, u₉.mem,
        wd 8 (by decide), w1]
    by_cases h2' : r = .s2
    · subst h2'
      rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.mem, u₉'.mem,
        u₉.mem, wd 16 (by decide), w2]
    by_cases h3' : r = .s3
    · subst h3'; rw [v₅.other _ (by decide), v₄.gpr, v₃.mem, v₂.mem, v₁.mem, u₉'.mem, u₉.mem, wd 32 (by decide), w4]
    exact gp r hr h0 h1 h2' h3'
  · rw [v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, u₉'.sp, u₉.sp, r₈.sp, u₇.sp, u₆.sp, u₅b.sp, u₅a.sp, u₅.sp, u₄.sp,
      K₃.sp, r₂.sp, sp₁]
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr,
      u₉'.mem, u₉.mem, wd 24 (by decide), w3]
  -- The specification.
  obtain a0' : t₅.gpr .a0 = if B then 1 else 0 := by
    rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide),
      v₁.other _ (by decide), u₉'.gpr, u₉.gpr, fl₈, and_one]
  obtain bytes' : bytesAt t₅.mem out (1 + E.L) = (if B then BitVec.ofNat 8 (2 + y % 2) else 0) ::
      toBytes E.L (if B then x else 0) := by rw [v₅.mem, M₄]; exact bytes₈
  obtain hlen : (bytesAt s.mem (s.gpr .a1) (1 + 2 * E.L)).length = 2 * E.c.C.len + 1 := by
    rw [VG.Proof.Weierstrass.length_bytesAt, E.len, Nat.add_comm]
  obtain hpb := peer_bytes s.mem (s.gpr .a1) E.L
  obtain hhd : (bytesAt s.mem (s.gpr .a1) (1 + 2 * E.L)).head? = some (s.mem (s.gpr .a1)) := by rw [hpb]; rfl
  obtain hxv : ofBytes (((bytesAt s.mem (s.gpr .a1) (1 + 2 * E.L)).drop 1).take E.c.C.len) = x := by
    rw [E.len, hpb, List.drop_one, List.tail_cons,
      List.take_left' (VG.Proof.Weierstrass.length_bytesAt _ _ _)]; exact x₁.symm
  obtain hyv : ofBytes ((bytesAt s.mem (s.gpr .a1) (1 + 2 * E.L)).drop (E.c.C.len + 1)) = y := by
    rw [E.len, hpb, List.drop_succ_cons, List.drop_left' (VG.Proof.Weierstrass.length_bytesAt _ _ _)]
    exact y₁.symm
  obtain hce := VG.Proof.EcKey.Compressed.compress_eq hlen hhd hxv hyv
  rw [E.len] at hce
  unfold compPost
  rw [hout, hce]
  obtain key : B = true ↔ VG.Proof.Ecdh.Valid E.c.C (s.mem (s.gpr .a1)) x y := by
    rw [← hB]
    unfold VG.Proof.Ecdh.Valid
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, valid_iff_of E.CCW]
  by_cases hv : VG.Proof.Ecdh.Valid E.c.C (s.mem (s.gpr .a1)) x y
  · rw [ite_eq_left hv]
    rw [key.mpr hv] at a0' bytes'
    exact ⟨a0', bytes'⟩
  · rw [ite_eq_right hv]
    obtain hb' : B = false := by
      cases h : B
      · rfl
      · exact absurd (key.mp h) hv
    rw [hb'] at a0' bytes'
    exact ⟨a0', bytes'.trans (by
      rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true, toBytes_zero, Nat.add_comm 1,
        List.replicate_succ])⟩

/-! ## Decompression -/

/-- `subCall_ok`, for a field of `k` words modulo `p`. -/
theorem subCall_kit {F : Field} (hF : FieldOk F) {k p : Nat} (hk : F.S.k = k) (hm : F.S.m = p) {s : State}
    {base : Addr} (hw : WsReg s base) {o a b : Nat}
    (ho : o + 8 * k ≤ own k) (ha : a + 8 * k ≤ own k) (hb : b + 8 * k ≤ own k)
    (ho' : o < 4095) (ha' : a < 4095) (hb' : b < 4095)
    (hA : wordsVal s.mem base a k < p) (hB : wordsVal s.mem base b k < p) :
    WP isa (subCall F o a b) s fun s' => CallKeep k base o s s' ∧
      wordsVal s'.mem base o k = (wordsVal s.mem base a k + p - wordsVal s.mem base b k) % p := by
  subst hk hm; exact subCall_ok hF hw ho ha hb ho' ha' hb' hA hB

/-- `pow_ok`, for a field of `k` words modulo `p`. -/
theorem pow_kit {P : PowCfg} {F : Field} {k p : Nat} [NeZero p] (hF : FieldOk F) (hk : F.S.k = k) (hm : F.S.m = p)
    (hn : P.M.n = k) (hL : PowLayR P k) (hU : UnitMod p (2 ^ (64 * k))) {base : Addr} {s : State}
    (hs : WsReg s base) (hO : wordsVal s.mem base P.one k = 2 ^ (64 * k) % p)
    (he : wordsVal s.mem base P.bits k < 2 ^ P.nbits) :
    WP isa (pow P F) s fun s' => Kc s s' ∧ Unch base (powWx P k) s.mem s'.mem ∧
      wordsVal s'.mem base P.acc k < p ∧
      toM p (2 ^ (64 * k)) (wordsVal s'.mem base P.acc k) =
        toM p (2 ^ (64 * k)) (wordsVal s.mem base P.base k) ^ wordsVal s.mem base P.bits k := by
  subst hk hm; exact pow_ok hF hn hL hU hs (Nat.pos_of_ne_zero (NeZero.ne _)) hO he

/-- A slot apart from what a call of a field function writes to another. -/
theorem call_apart {c : Cfg} (h9 : c.n ≤ 9) {i o : Nat} (hi : i < 45) (hne : i ≠ o) :
    ∀ w ∈ [(c.sl o, 8 * c.n), (own c.n, 64 * c.n)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  obtain hle := sl_le c hi
  obtain hown := own_ge h9
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact sl_sep c hne
  · exact .inl (by omega_using [hle, hown])

/-- A word of a slot that is not a constant's is apart from the constants. -/
theorem word_consts (c : Cfg) (h1 : 0 < c.n) {i : Nat} (hi : ∀ j ∈ cslots, i ≠ j) :
    ∀ w ∈ (consts c).map (fun e => (c.sl e.1, 8 * c.n)), c.sl i + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  fun w hw => by have := apart_consts c hi w hw; omega_using [this, h1]

/-- The mask of a byte being `02` or `03`. -/
theorem tag_mask (b : BitVec 8) :
    (0 : BitVec 64) - ((((b.setWidth 64 ^^^ BitVec.ofInt 64 2) >>> 1) + BitVec.ofInt 64 (-1)) >>> 63) =
      maskOf (decide (b = 2 ∨ b = 3)) := by
  revert b; decide

/-- `tagMask q`: `a7` is the mask of the byte at `[q]` being `02` or `03`. -/
theorem tagMask_ok {s : State} {q : Reg}
    (hin : InRegions (s.rd ++ s.wr) (s.gpr q) 1) :
    WP isa (.block (Cfg.tagMask q)) s fun s' =>
      Rest [.t0, .t1, .a7] s s' ∧ s'.mem = s.mem ∧ s'.gpr .a7 = maskOf (decide (s.mem (s.gpr q) = 2 ∨
        s.mem (s.gpr q) = 3)) := by
  rw [Cfg.tagMask]
  refine wp_lbu (off := 0) (by decide) (by simp) hin fun s₁ u₁ => ?_
  refine WP.cons (exec_logicImm (by decide)) ?_
  refine wp_srl (by decide) fun s₂ u₂ => ?_
  refine WP.cons (exec_addi (by decide)) ?_
  refine wp_srl (by decide) fun s₃ u₃ => wp_li (imm := 0) (by decide) fun s₄ u₄ => wp_sub fun s₅ u₅ =>
    WP.block_nil ⟨?_, ?_, ?_⟩
  · have R := fun {a b : State} {d : Reg} {v : BitVec 64} (u : Upd a b d v) (h : d ∈ [Reg.t0, .t1, .a7]) =>
      u.rest (ws := [Reg.t0, .t1, .a7]) h
    exact ((((R u₁ (by decide)).trans (R (Upd.write _ _ _) (by decide))).trans (R u₂ (by decide))).trans
      (R (Upd.write _ _ _) (by decide))).trans
      (((R u₃ (by decide)).trans (R u₄ (by decide))).trans (R u₅ (by decide)))
  · rw [u₅.mem, u₄.mem, u₃.mem]; simp only [State.write]; rw [u₂.mem]; simp only [State.write]; exact u₁.mem
  · rw [u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.gpr]
    simp only [State.write, ↓reduceIte]
    rw [u₂.gpr]
    simp only [State.write, ↓reduceIte]
    rw [u₁.gpr, show BitVec.ofNat 64 0 = 0 from rfl, tag_mask]

/-- `vg_ec_<curve>_decompress_public_key(out = a0, public = a1, scratch = a2)`'s
precondition, by register. -/
def DPre (s : State) : Prop :=
  let out : Region := ⟨s.gpr .a0, 1 + 2 * E.L⟩
  let pk : Region := ⟨s.gpr .a1, 1 + E.L⟩
  let ws : Region := ⟨s.gpr .a2, 8192⟩
  s.rd = [pk] ∧ s.wr = [out, ws] ∧ pk.Disjoint out ∧ pk.Disjoint ws ∧ out.Disjoint ws ∧
    (s.gpr .a0).toNat + (1 + 2 * E.L) ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + (1 + E.L) ≤ 2 ^ 64 ∧
    (s.gpr .a2).toNat + 8192 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat % 8 = 0

/-- What decompression's setup leaves. -/
structure DPost (E : Kit) (s s' : State) : Prop where
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
  x : sv E.c (s.gpr .a2) s' CX = ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) E.L)
  par : word s'.mem (s.gpr .a2) (E.c.sl PAR) = (s.mem (s.gpr .a1)).setWidth 64 &&& BitVec.ofInt 64 1
  flag : word s'.mem (s.gpr .a2) (E.c.sl FLAG) =
    maskOf (decide (s.mem (s.gpr .a1) = 2 ∨ s.mem (s.gpr .a1) = 3) &&
      decide (ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) E.L) < E.c.C.p))
  consts : ∀ e ∈ consts E.c, sv E.c (s.gpr .a2) s' e.1 = e.2
  exps : sv E.c (s.gpr .a2) s' EXPS = (E.c.C.p + 1) / 4

/-- `p`, the first constant, is below `2^(64 n)`. -/
theorem p_lt : E.c.C.p < 2 ^ (64 * E.c.n) :=
  E.consts_lt ((consts E.c)[0]'(by rw [consts_len]; decide)) (List.getElem_mem _)

/-- The setup: the saves, `x`, the first byte's low bit, the flag set to the
mask of that byte being `02` or `03` and of `x < p`, the constants and the
root's exponent. -/
theorem dsetup_ok {s : State} (hs : E.DPre s) :
    WP isa (.block (saveCode .a2 ++ E.load (E.c.sl CX) .a1 1 ++ Cfg.parCode E.c .a1 ++
      Cfg.tagMask .a1 ++ sdAt .a7 wb (E.c.sl FLAG) ++ constCode E.c ++
      setConst E.c.n (E.c.sl EXPS) ((E.c.C.p + 1) / 4) ++ ltMask E.c.n (E.c.sl CX) (E.c.sl MP) ++
      andFlag E.c)) s fun s' => E.DPost s s' := by
  obtain ⟨hrd, hwr, hpo, hpw, how, hfo, hfp, hfs, hal⟩ := hs
  obtain hL := E.Ln
  obtain h9 := E.n9
  obtain h1 := E.n1
  obtain fit : ∀ i, i < 45 → E.c.sl i + 8 * E.c.n ≤ 4096 := fun _ hi => sl_top h9 (by omega_using [hi])
  obtain top : ∀ i, i < 45 → E.c.sl i + 8 * E.c.n ≤ 2 ^ 64 := fun i hi => Nat.le_trans (fit i hi) (by decide)
  generalize hb : s.gpr .a2 = base at hwr hpw how hfs hal
  obtain hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (TKit.save_ok hb hwr' hfs hal)
    fun s₁ ⟨hw₁, h3₁, o₁, g₁, rd₁, wr₁, sp₁, U₁, w0, w1, w2, w3, w4⟩ => ?_)
  obtain a1 : s₁.gpr .a1 = s.gpr .a1 := g₁ _ (by decide) (by decide) (by decide)
  obtain rdp : (⟨s.gpr .a1, 1 + E.L⟩ : Region) ∈ s₁.rd ++ s₁.wr := by rw [rd₁, wr₁, hrd]; simp
  -- `x`.
  refine WP.block_append (WP.mono (E.load_ok (i := CX) (p := .a1) (off := 1) (R := 1 + E.L) hw₁ (by decide)
    (by decide) (by omega_using []) (by omega_using [hL, h9]) (by rw [a1]; exact rdp)
    (fun j hj => by rw [a1]; exact out_of_disj hpw hfp (by omega_using [hj]))) fun s₂ ⟨r₂, O₂, e₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  obtain a1₂ : s₂.gpr .a1 = s.gpr .a1 := by rw [r₂.gpr _ (by decide), a1]
  obtain in₂ : InRegions (s₂.rd ++ s₂.wr) (s.gpr .a1) 1 := by
    rw [r₂.rd, r₂.wr]
    have := Offset.contains_base (s.gpr .a1) (d := 0) (n := 1) (k := 1 + E.L) (by omega_using []) (by decide)
    exact ⟨_, rdp, by simpa using this⟩
  -- The first byte's low bit.
  rw [Cfg.parCode, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_lbu (off := 0) (by decide) (by rw [a1₂, BitVec.add_zero]) in₂ fun s₃ u₃ => ?_
  refine WP.cons (exec_logicImm (by decide)) ?_
  obtain u₃a := Upd.write s₃ .t0 (s₃.gpr .t0 &&& BitVec.ofInt 64 1)
  obtain hw₃ := (hw₂.of_kp (Kp.of_upd u₃)).of_kp (Kp.of_upd u₃a)
  refine sd_ws hw₃ (d := E.c.sl PAR) (by kit_slots E) (sl8 _ _) fun s₄ u₄ => ?_
  obtain hw₄ := hw₃.of_kp (Kp.of_mupd u₄)
  obtain par₄ : word s₄.mem base (E.c.sl PAR) = (s₂.mem (s.gpr .a1)).setWidth 64 &&& BitVec.ofInt 64 1 := by
    rw [u₄.mem, word_writeW_self, u₃a.gpr, u₃.gpr]
  obtain O₄ : Outside base (E.c.sl PAR) 8 s₂.mem s₄.mem := by
    rw [u₄.mem, u₃a.mem, u₃.mem]; exact writeW_outside _ _ _ (by kit_slots E)
  obtain a1₄ : s₄.gpr .a1 = s.gpr .a1 := by
    rw [u₄.gpr, u₃a.other _ (by decide), u₃.other _ (by decide), a1₂]
  -- The tag's mask.
  refine WP.block_append (WP.mono (tagMask_ok (s := s₄) (q := .a1) (by
      rw [a1₄, u₄.rd, u₄.wr, u₃a.rd, u₃a.wr, u₃.rd, u₃.wr]; exact in₂))
    fun s₅ ⟨r₅, m₅, g₅⟩ => ?_)
  obtain hw₅ := hw₄.of_rest r₅
  refine sdAt_ws hw₅ (by decide) (d := E.c.sl FLAG) (by kit_slots E) (sl8 _ _) fun s₆ u₆ => ?_
  obtain hw₆ := hw₅.of_kp (Kp.of_mupd u₆)
  -- The constants and the root's exponent.
  rw [constCode_eq]
  refine WP.block_append (WP.mono (TKit.consts_ok E.c E.n9 _ hw₆ (TKit.consts_le E.c) (consts_nodup E.c))
    fun s₇ ⟨r₇, U₇, e₇⟩ => ?_)
  obtain hw₇ := hw₆.of_rest r₇
  refine WP.block_append (WP.mono (setConst_ok E.c.n hw₇ (o := E.c.sl EXPS) (x := (E.c.C.p + 1) / 4) (sl8 _ _)
    (fit _ (by decide))) fun s₈ ⟨r₈, O₈, e₈⟩ => ?_)
  obtain hw₈ := hw₇.of_rest r₈
  -- `x < p`.
  refine WP.block_append (WP.mono (ltMask_ok hw₈ (n := E.c.n) (a := E.c.sl CX) (m := E.c.sl MP) (sl8 _ _)
    (sl8 _ _) (fit _ (by decide)) (fit _ (by decide))) fun s₉ ⟨r₉, m₉, g₉⟩ => ?_)
  obtain hw₉ := hw₈.of_rest r₉
  refine WP.mono (E.andFlag_ok hw₉) fun s₁₀ ⟨f₁₀, r₁₀, O₁₀⟩ => ?_
  -- What changed.
  obtain O₆ : Unch base [(E.c.sl FLAG, 8)] s₅.mem s₆.mem := by
    rw [u₆.mem]; exact (writeW_outside _ _ _ (by kit_slots E)).unch
  obtain U₈₁₀ : Unch base [(E.c.sl FLAG, 8)] s₈.mem s₁₀.mem := by rw [← m₉]; exact O₁₀.unch
  obtain U₆₁₀ := (U₇.trans O₈.unch).trans U₈₁₀
  obtain U₄₆ : Unch base [(E.c.sl FLAG, 8)] s₄.mem s₆.mem := by rw [← m₅]; exact O₆
  obtain U₄₁₀ := U₄₆.trans U₆₁₀
  obtain U₂₁₀ := O₄.unch.trans U₄₁₀
  obtain U₁₁₀ := O₂.unch.trans U₂₁₀
  obtain hp1 : ∀ x ∈ preserved, x ∉ [Reg.t0, .t1, .a7] := by decide
  obtain hp2 : ∀ x ∈ preserved, x ∉ [Reg.t0, .t1] := by decide
  obtain hp3 : ∀ x ∈ preserved, x ∉ [Reg.t3, .t4, .t5, .t6, .a4, .a7] := by decide
  obtain hp4 : ∀ x ∈ preserved, x ∉ [Reg.t0] := by decide
  obtain hp5 : ∀ x ∈ preserved, x ≠ .t0 := by decide
  obtain gp : ∀ x ∈ preserved, s₁₀.gpr x = s₁.gpr x := fun x hx => by
    rw [r₁₀.gpr _ (hp4 x hx), r₉.gpr _ (hp3 x hx), r₈.gpr _ (hp2 x hx), r₇.gpr _ (hp2 x hx), u₆.gpr,
      r₅.gpr _ (hp1 x hx), u₄.gpr, u₃a.other _ (hp5 x hx), u₃.other _ (hp5 x hx), r₂.gpr _ (hp2 x hx)]
  obtain b₂ : s₂.mem (s.gpr .a1) = s.mem (s.gpr .a1) := by
    obtain h1 := bytesAt_unch (U₁.trans O₂.unch) (q := s.gpr .a1) (n := 1) (by kit_ranges (first | decide | kit_slots E))
      (by simpa using sep_at' hpw hfp (off := 0) (k := 1) (by omega_using []))
    simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h1
    simp only [BitVec.add_zero] at h1
    exact h1
  obtain x₂ : sv E.c base s₂ CX = ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) E.L) := by
    show wordsVal _ _ _ _ = _
    rw [e₂, a1, bytesAt_unch U₁ (by decide) (sep_at' hpw hfp (off := 1) (k := E.L) (by omega_using []))]
  obtain cs₇ : ∀ e ∈ consts E.c, sv E.c base s₇ e.1 = e.2 := fun e he => by
    rw [e₇ e he, Nat.mod_eq_of_lt (E.consts_lt e he)]
  obtain lo : ∀ d, d + 8 ≤ 40 → word s₁₀.mem base d = word s₁.mem base d := fun d hd =>
    lo_word U₁₁₀ (by kit_ranges (first | exact lo_consts _ | exact Nat.le_trans (by decide) (sl_lo _ _))) hd
  obtain cx₄ : sv E.c base s₄ CX = ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) E.L) := by
    show wordsVal _ _ _ _ = _
    rw [O₄.wordsVal (by kit_slots E) (top CX (by decide))]; exact x₂
  subst hb
  refine ⟨hw₉.of_rest r₁₀, by rw [gp _ (by decide), o₁], by rw [gp _ (by decide), h3₁],
    fun x h0 h2 h3 hx => by rw [gp _ hx, g₁ _ h0 h2 h3], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r₁₀.rd, r₉.rd, r₈.rd, r₇.rd, u₆.rd, r₅.rd, u₄.rd, u₃a.rd, u₃.rd, r₂.rd, rd₁]
  · rw [r₁₀.wr, r₉.wr, r₈.wr, r₇.wr, u₆.wr, r₅.wr, u₄.wr, u₃a.wr, u₃.wr, r₂.wr, wr₁]
  · rw [r₁₀.sp, r₉.sp, r₈.sp, r₇.sp, u₆.sp, r₅.sp, u₄.sp, u₃a.sp, u₃.sp, r₂.sp, sp₁]
  · rw [lo 0 (by decide)]; exact w0
  · rw [lo 8 (by decide)]; exact w1
  · rw [lo 16 (by decide)]; exact w2
  · rw [lo 24 (by decide)]; exact w3
  · rw [lo 32 (by decide)]; exact w4
  · show wordsVal _ _ _ _ = _
    rw [U₄₁₀.wordsVal (by kit_apart E) (top CX (by decide))]; exact cx₄
  · rw [U₄₁₀.word (by kit_ranges (first | exact word_consts _ h1 (by decide) | kit_slots E)) (by kit_slots E),
      par₄, b₂]
  · have b₄ : s₄.mem (s.gpr .a1) = s.mem (s.gpr .a1) := by
      obtain h1 := bytesAt_unch ((U₁.trans O₂.unch).trans O₄.unch) (q := s.gpr .a1) (n := 1)
        (by kit_ranges (first | decide | kit_slots E))
        (by simpa using sep_at' hpw hfp (off := 0) (k := 1) (by omega_using []))
      simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h1
      simp only [BitVec.add_zero] at h1
      exact h1
    obtain mp₈ : wordsVal s₈.mem (s.gpr .a2) (E.c.sl MP) E.c.n = E.c.C.p := by
      rw [O₈.wordsVal (sl_sep _ (i := MP) (j := EXPS) (by decide)) (top MP (by decide))]; exact E.const_at cs₇ 0
    obtain cx₈ : wordsVal s₈.mem (s.gpr .a2) (E.c.sl CX) E.c.n =
        ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) E.L) := by
      rw [O₈.wordsVal (sl_sep _ (i := CX) (j := EXPS) (by decide)) (top CX (by decide)),
        (U₄₆.trans U₇).wordsVal (by kit_apart E) (top CX (by decide))]; exact cx₄
    rw [f₁₀, m₉, O₈.word (.inr (sl_le _ (by decide))) (by kit_slots E), U₇.word (flag_consts _) (by kit_slots E),
      u₆.mem, word_writeW_self, g₅, g₉, a1₄, b₄, mp₈, cx₈, maskOf_and]
  · intro e he
    obtain hj := (by decide : ∀ j ∈ cslots, j < FLAG ∧ j ≠ EXPS ∧ j < 45) _ (mem_cslots he)
    show wordsVal _ _ _ _ = _
    rw [U₈₁₀.wordsVal (all_one (.inl (sl_le _ hj.1))) (top _ hj.2.2),
      O₈.wordsVal (sl_sep _ hj.2.1) (top _ hj.2.2)]
    exact cs₇ e he
  · show wordsVal _ _ _ _ = _
    rw [U₈₁₀.wordsVal (all_one (.inl (sl_le _ (i := EXPS) (j := FLAG) (by decide)))) (top EXPS (by decide)), e₈]
    obtain hp := E.p_lt
    exact Nat.mod_eq_of_lt (by omega_using [hp])

/-! ### `rhs = x³ + a x + b` -/

/-- The slots of `rhs`'s operations after the first, by number, and the operations on them. -/
abbrev rhsIdx : List Nat := [CXM, RHS, TT, AP, BP]

abbrev rhsOpsI : List FOp :=
  [.mul RHS CXM CXM, .mul RHS RHS CXM, .mul TT AP CXM, .add RHS RHS TT, .add RHS RHS BP]

theorem rhsOps_tail (c : Cfg) : (Cfg.rhsOps c).tail = rhsOpsI.map (FOp.rename c.sl) := rfl

/-- The slots of `rhs`'s operations after the first. -/
abbrev rhsSlots (c : Cfg) : List Nat := rhsIdx.map c.sl

theorem rhsLay (c : Cfg) (h9 : c.n ≤ 9) : Lay c.MP' (own c.n) (· ∈ rhsSlots c) := by
  obtain hown := own_ge h9
  refine ⟨fun x hx => ?_, fun x y hx hy hne => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have : c.sl i + 8 * c.n ≤ c.sl 45 := sl_le c ((by decide : ∀ i ∈ rhsIdx, i < 45) i hi)
    show c.sl i + 8 * c.n ≤ own c.n
    omega_using [this, hown]
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
    exact sl_sep c fun h => hne (congrArg c.sl h)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact sl_sep c ((by decide : ∀ i ∈ rhsIdx, i ≠ MP) i hi)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact sl_sep c ((by decide : ∀ i ∈ rhsIdx, i ≠ TMP) i hi)

theorem rhsShort (c : Cfg) (h1 : 1 ≤ c.n) (h9 : c.n ≤ 9) : Short (· ∈ rhsSlots c) := fun x hx => by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  have := sl_top h9 (i := i) ((by decide : ∀ i ∈ rhsIdx, i ≤ 55) i hi)
  omega_using [this, h1]

theorem rhs_run (c : Cfg) (h1 : 1 ≤ c.n) {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps (Cfg.rhsOps c).tail e (c.sl RHS) =
      e (c.sl CXM) * e (c.sl CXM) * e (c.sl CXM) + e (c.sl AP) * e (c.sl CXM) + e (c.sl BP) := by
  have h := congrFun (runOps_rename c.sl rhsOpsI e fun _ _ _ hy => TKit.sl_inj c h1 hy) RHS
  rw [rhsOps_tail]
  refine h.trans ?_
  simp only [rhsOpsI, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [RHS, TT, CXM, AP, BP, T0, T1, Nat.reduceEqDiff, ↓reduceIte]

/-- `x R` to `CXM` and `rhs` (in Montgomery's form) to `RHS`. -/
theorem rhs_ok {s : State} {base : Addr} (hw : WsReg s base)
    (hr2 : sv E.c base s R2P = 2 ^ (64 * E.c.n) * 2 ^ (64 * E.c.n) % E.c.C.p)
    (hap : sv E.c base s AP = E.c.C.a * 2 ^ (64 * E.c.n) % E.c.C.p)
    (hbp : sv E.c base s BP = E.c.C.b * 2 ^ (64 * E.c.n) % E.c.C.p) :
    WP isa (fprog E.c.FP (Cfg.rhsOps E.c)) s fun s' =>
      Kp s s' ∧ Unch base ([(E.c.sl CXM, 8 * E.c.n), (own E.c.n, 64 * E.c.n)] ++
        (((Cfg.rhsOps E.c).tail.map FOp.out).map (fun w => (w, 8 * E.c.n)) ++ [(own E.c.n, 64 * E.c.n)]))
          s.mem s'.mem ∧
      sv E.c base s' RHS < E.c.C.p ∧
      toM E.c.C.p (2 ^ (64 * E.c.n)) (sv E.c base s' RHS) =
        Fin.ofNat E.c.C.p (sv E.c base s CX) * Fin.ofNat E.c.C.p (sv E.c base s CX) *
            Fin.ofNat E.c.C.p (sv E.c base s CX) +
          Fin.ofNat E.c.C.p E.c.C.a * Fin.ofNat E.c.C.p (sv E.c base s CX) + Fin.ofNat E.c.C.p E.c.C.b := by
  obtain hp0 : 0 < E.c.C.p := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain h9 := E.n9
  obtain h1 : 1 ≤ E.c.n := E.n1
  obtain hown := own_ge h9
  obtain fit : ∀ i, i < 45 → E.c.sl i + 8 * E.c.n ≤ own E.c.n := fun i hi => by
    have := sl_le E.c hi; omega_using [this, hown]
  obtain lt4 : ∀ i, i < 45 → E.c.sl i < 4095 := fun i hi => by
    have := sl_top h9 (i := i) (by omega_using [hi]); omega_using [this, h1]
  obtain top : ∀ i, i < 45 → E.c.sl i + 8 * E.c.n ≤ 2 ^ 64 := fun i hi =>
    Nat.le_trans (sl_top h9 (by omega_using [hi])) (by decide)
  show WP isa (.seq (mulCall E.c.FP (E.c.sl CXM) (E.c.sl CX) (E.c.sl R2P))
    (fprog E.c.FP (Cfg.rhsOps E.c).tail)) s _
  refine WP.seq (WP.mono (TKit.mulCall_kit E.field_ok E.FPk E.FPm hw (o := E.c.sl CXM) (a := E.c.sl CX)
    (b := E.c.sl R2P) (fit CXM (by decide)) (fit CX (by decide)) (fit R2P (by decide)) (lt4 CXM (by decide))
    (lt4 CX (by decide)) (lt4 R2P (by decide))
    (by show sv E.c base s R2P < _; rw [hr2]; exact Nat.mod_lt _ hp0)) fun s₁ ⟨C₁, lt₁, e₁⟩ => ?_)
  obtain hw₁ := hw.of_kp C₁.kp
  have U₁ : Unch base [(E.c.sl CXM, 8 * E.c.n), (own E.c.n, 64 * E.c.n)] s.mem s₁.mem := C₁.mem
  obtain xm₁ : sv E.c base s₁ CXM = sv E.c base s CX * 2 ^ (64 * E.c.n) % E.c.C.p :=
    mont_eq E.unit lt₁ (e₁.trans (by show sv E.c base s CX * sv E.c base s R2P % E.c.C.p = _; rw [hr2]))
  obtain ap₁ : sv E.c base s₁ AP = E.c.C.a * 2 ^ (64 * E.c.n) % E.c.C.p := by
    show wordsVal _ _ _ _ = _
    rw [U₁.wordsVal (call_apart h9 (i := AP) (o := CXM) (by decide) (by decide)) (top AP (by decide))]; exact hap
  obtain bp₁ : sv E.c base s₁ BP = E.c.C.b * 2 ^ (64 * E.c.n) % E.c.C.p := by
    show wordsVal _ _ _ _ = _
    rw [U₁.wordsVal (call_apart h9 (i := BP) (o := CXM) (by decide) (by decide)) (top BP (by decide))]; exact hbp
  obtain hR : E.c.sl RHS ∈ validAfter (Cfg.rhsOps E.c).tail [E.c.sl CXM, E.c.sl AP, E.c.sl BP] :=
    (mem_validAfter _ _).mpr (.inr (by
      rw [rhsOps_tail, List.map_map]
      exact List.mem_map.mpr ⟨.mul RHS CXM CXM, List.getElem_mem (show 0 < rhsOpsI.length by decide), rfl⟩))
  refine WP.mono (TKit.fprog_kit (M := E.c.MP') (F := E.c.FP) E.field_ok E.FPm E.FPk (rhsLay E.c h9)
    (rhsShort E.c h1 h9) E.unit (Cfg.rhsOps E.c).tail (V := [E.c.sl CXM, E.c.sl AP, E.c.sl BP])
    (E := fun x => toM E.c.C.p (2 ^ (64 * E.c.n)) (wordsVal s₁.mem base x E.c.n))
    ⟨hw₁, fun x hx => ?_, fun x hx => ?_, fun _ _ => rfl⟩ (fun op hop x hx => ?_) ?_)
    fun s' ⟨K, I⟩ => ⟨C₁.kp.trans K.kp, U₁.trans K.mem, I.lt _ hR, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (show x ∈ ([CXM, AP, BP] : List Nat).map E.c.sl from hx)
    exact List.mem_map_of_mem ((by decide : ∀ i ∈ ([CXM, AP, BP] : List Nat), i ∈ rhsIdx) i hi)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact lt₁
    · show sv E.c base s₁ AP < _; rw [ap₁]; exact Nat.mod_lt _ hp0
    · show sv E.c base s₁ BP < _; rw [bp₁]; exact Nat.mod_lt _ hp0
  · rw [rhsOps_tail] at hop
    obtain ⟨op', hop', rfl⟩ := List.mem_map.mp hop
    rw [TKit.rename_slots] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact List.mem_map_of_mem ((by decide : ∀ op ∈ rhsOpsI, ∀ y ∈ op.out :: op.ins, y ∈ rhsIdx) op' hop' y hy)
  · rw [rhsOps_tail]
    exact readsOk_rename E.c.sl (V := [CXM, AP, BP]) (by decide)
  · have v := I.val (E.c.sl RHS) hR
    refine v.trans ((rhs_run E.c h1 (F := Fe E.c.C) _).trans ?_)
    show toM E.c.C.p (2 ^ (64 * E.c.n)) (sv E.c base s₁ CXM) * toM E.c.C.p (2 ^ (64 * E.c.n)) (sv E.c base s₁ CXM) *
        toM E.c.C.p (2 ^ (64 * E.c.n)) (sv E.c base s₁ CXM) +
        toM E.c.C.p (2 ^ (64 * E.c.n)) (sv E.c base s₁ AP) * toM E.c.C.p (2 ^ (64 * E.c.n)) (sv E.c base s₁ CXM) +
        toM E.c.C.p (2 ^ (64 * E.c.n)) (sv E.c base s₁ BP) = _
    rw [xm₁, ap₁, bp₁, toM_mont E.unit, toM_mont E.unit, toM_mont E.unit]

/-! ### The root's checks -/

/-- `y²` and `y² - rhs` (in Montgomery's form), `y` out of it, and `p - y`. -/
theorem root_ok {s : State} {base : Addr} (hw : WsReg s base) (hacc : sv E.c base s ACC < E.c.C.p)
    (hrhs : sv E.c base s RHS < E.c.C.p) (hone : sv E.c base s ONE = 1) (hzero : sv E.c base s ZERO = 0) :
    WP isa (fprog E.c.FP (Cfg.rootOps E.c)) s fun s' =>
      Kp s s' ∧ Unch base ([(E.c.sl YSQ, 8 * E.c.n), (own E.c.n, 64 * E.c.n)] ++
        [(E.c.sl DIF, 8 * E.c.n), (own E.c.n, 64 * E.c.n)] ++ [(E.c.sl Y1, 8 * E.c.n), (own E.c.n, 64 * E.c.n)] ++
        [(E.c.sl Y2, 8 * E.c.n), (own E.c.n, 64 * E.c.n)]) s.mem s'.mem ∧
      sv E.c base s' DIF < E.c.C.p ∧
      toM E.c.C.p (2 ^ (64 * E.c.n)) (sv E.c base s' DIF) =
        toM E.c.C.p (2 ^ (64 * E.c.n)) (sv E.c base s ACC) * toM E.c.C.p (2 ^ (64 * E.c.n)) (sv E.c base s ACC) -
          toM E.c.C.p (2 ^ (64 * E.c.n)) (sv E.c base s RHS) ∧
      sv E.c base s' Y1 < E.c.C.p ∧
      Fin.ofNat E.c.C.p (sv E.c base s' Y1) = toM E.c.C.p (2 ^ (64 * E.c.n)) (sv E.c base s ACC) ∧
      sv E.c base s' Y2 = (E.c.C.p - sv E.c base s' Y1) % E.c.C.p := by
  obtain hp0 : 0 < E.c.C.p := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain hp1 := E.p1
  obtain h9 := E.n9
  obtain h1 : 1 ≤ E.c.n := E.n1
  obtain hown := own_ge h9
  obtain fit : ∀ i, i < 45 → E.c.sl i + 8 * E.c.n ≤ own E.c.n := fun i hi => by
    have := sl_le E.c hi; omega_using [this, hown]
  obtain lt4 : ∀ i, i < 45 → E.c.sl i < 4095 := fun i hi => by
    have := sl_top h9 (i := i) (by omega_using [hi]); omega_using [this, h1]
  obtain top : ∀ i, i < 45 → E.c.sl i + 8 * E.c.n ≤ 2 ^ 64 := fun i hi =>
    Nat.le_trans (sl_top h9 (by omega_using [hi])) (by decide)
  obtain keep : ∀ {o i : Nat} {m m' : Mem}, Unch base [(E.c.sl o, 8 * E.c.n), (own E.c.n, 64 * E.c.n)] m m' →
      i < 45 → i ≠ o → wordsVal m' base (E.c.sl i) E.c.n = wordsVal m base (E.c.sl i) E.c.n :=
    fun U hi hne => U.wordsVal (call_apart h9 hi hne) (top _ hi)
  show WP isa (.seq (mulCall E.c.FP (E.c.sl YSQ) (E.c.sl ACC) (E.c.sl ACC)) <|
    .seq (subCall E.c.FP (E.c.sl DIF) (E.c.sl YSQ) (E.c.sl RHS)) <|
    .seq (mulCall E.c.FP (E.c.sl Y1) (E.c.sl ACC) (E.c.sl ONE))
      (subCall E.c.FP (E.c.sl Y2) (E.c.sl ZERO) (E.c.sl Y1))) s _
  refine WP.seq (WP.mono (TKit.mulCall_kit E.field_ok E.FPk E.FPm hw (o := E.c.sl YSQ) (a := E.c.sl ACC)
    (b := E.c.sl ACC) (fit YSQ (by decide)) (fit ACC (by decide)) (fit ACC (by decide)) (lt4 YSQ (by decide))
    (lt4 ACC (by decide)) (lt4 ACC (by decide)) hacc) fun s₁ ⟨C₁, lt₁, e₁⟩ => ?_)
  obtain hw₁ := hw.of_kp C₁.kp
  have U₁ : Unch base [(E.c.sl YSQ, 8 * E.c.n), (own E.c.n, 64 * E.c.n)] s.mem s₁.mem := C₁.mem
  obtain e₁' : ∀ i, i ∈ [ACC, RHS, ONE, ZERO] → sv E.c base s₁ i = sv E.c base s i := fun i hi =>
    keep U₁ ((by decide : ∀ i ∈ [ACC, RHS, ONE, ZERO], i < 45) i hi)
      ((by decide : ∀ i ∈ [ACC, RHS, ONE, ZERO], i ≠ YSQ) i hi)
  refine WP.seq (WP.mono (subCall_kit E.field_ok E.FPk E.FPm hw₁ (o := E.c.sl DIF) (a := E.c.sl YSQ)
    (b := E.c.sl RHS) (fit DIF (by decide)) (fit YSQ (by decide)) (fit RHS (by decide)) (lt4 DIF (by decide))
    (lt4 YSQ (by decide)) (lt4 RHS (by decide)) lt₁
    (by show sv E.c base s₁ RHS < _; rw [e₁' RHS (by simp)]; exact hrhs)) fun s₂ ⟨C₂, e₂⟩ => ?_)
  obtain hw₂ := hw₁.of_kp C₂.kp
  have U₂ : Unch base [(E.c.sl DIF, 8 * E.c.n), (own E.c.n, 64 * E.c.n)] s₁.mem s₂.mem := C₂.mem
  obtain e₂' : ∀ i, i ∈ [ACC, ONE, ZERO] → sv E.c base s₂ i = sv E.c base s i := fun i hi =>
    (keep U₂ ((by decide : ∀ i ∈ [ACC, ONE, ZERO], i < 45) i hi)
      ((by decide : ∀ i ∈ [ACC, ONE, ZERO], i ≠ DIF) i hi)).trans
      (e₁' i ((by decide : ∀ i ∈ [ACC, ONE, ZERO], i ∈ [ACC, RHS, ONE, ZERO]) i hi))
  refine WP.seq (WP.mono (TKit.mulCall_kit E.field_ok E.FPk E.FPm hw₂ (o := E.c.sl Y1) (a := E.c.sl ACC)
    (b := E.c.sl ONE) (fit Y1 (by decide)) (fit ACC (by decide)) (fit ONE (by decide)) (lt4 Y1 (by decide))
    (lt4 ACC (by decide)) (lt4 ONE (by decide))
    (by show sv E.c base s₂ ONE < _; rw [e₂' ONE (by simp), hone]; exact hp1)) fun s₃ ⟨C₃, lt₃, e₃⟩ => ?_)
  obtain hw₃ := hw₂.of_kp C₃.kp
  have U₃ : Unch base [(E.c.sl Y1, 8 * E.c.n), (own E.c.n, 64 * E.c.n)] s₂.mem s₃.mem := C₃.mem
  obtain z₃ : sv E.c base s₃ ZERO = 0 := by
    show wordsVal _ _ _ _ = _
    rw [keep U₃ (i := ZERO) (by decide) (by decide)]; rw [← hzero]; exact e₂' ZERO (by simp)
  refine WP.mono (subCall_kit E.field_ok E.FPk E.FPm hw₃ (o := E.c.sl Y2) (a := E.c.sl ZERO) (b := E.c.sl Y1)
    (fit Y2 (by decide)) (fit ZERO (by decide)) (fit Y1 (by decide)) (lt4 Y2 (by decide)) (lt4 ZERO (by decide))
    (lt4 Y1 (by decide)) (by show sv E.c base s₃ ZERO < _; rw [z₃]; exact hp0) lt₃) fun s₄ ⟨C₄, e₄⟩ => ?_
  have U₄ : Unch base [(E.c.sl Y2, 8 * E.c.n), (own E.c.n, 64 * E.c.n)] s₃.mem s₄.mem := C₄.mem
  obtain dif₄ : sv E.c base s₄ DIF = sv E.c base s₂ DIF := by
    show wordsVal _ _ _ _ = _
    rw [keep U₄ (i := DIF) (by decide) (by decide)]; exact keep U₃ (i := DIF) (by decide) (by decide)
  obtain y1₄ : sv E.c base s₄ Y1 = sv E.c base s₃ Y1 := keep U₄ (i := Y1) (by decide) (by decide)
  have h2 : sv E.c base s₂ DIF = (sv E.c base s₁ YSQ + E.c.C.p - sv E.c base s₁ RHS) % E.c.C.p := e₂
  obtain lt₂ : sv E.c base s₂ DIF < E.c.C.p := by rw [h2]; exact Nat.mod_lt _ hp0
  refine ⟨C₁.kp.trans (C₂.kp.trans (C₃.kp.trans C₄.kp)), ((U₁.trans U₂).trans U₃).trans U₄, by rw [dif₄]; exact lt₂,
    ?_, by rw [y1₄]; exact lt₃, ?_, ?_⟩
  · rw [dif₄]
    obtain hr1 : sv E.c base s₁ RHS < E.c.C.p := by rw [e₁' RHS (by simp)]; exact hrhs
    obtain hm : toM E.c.C.p (2 ^ (64 * E.c.n)) (sv E.c base s₁ YSQ) = toM E.c.C.p (2 ^ (64 * E.c.n)) (sv E.c base s ACC) *
        toM E.c.C.p (2 ^ (64 * E.c.n)) (sv E.c base s ACC) := toM_mul E.unit e₁
    rw [h2, toM_sub (by omega_using [hr1]), hm, e₁' RHS (by simp)]
  · rw [y1₄]
    refine toM_one_mul E.unit ?_
    have h := e₃
    rw [show wordsVal s₂.mem base (E.c.sl ONE) E.c.n = 1 from (e₂' ONE (by simp)).trans hone,
      show wordsVal s₂.mem base (E.c.sl ACC) E.c.n = sv E.c base s ACC from e₂' ACC (by simp)] at h
    exact h
  · have h4 : sv E.c base s₄ Y2 = (sv E.c base s₃ ZERO + E.c.C.p - sv E.c base s₃ Y1) % E.c.C.p := e₄
    rw [h4, z₃, Nat.zero_add, y1₄]

/-! ### The checks into the flag, the root's choice and the output -/

theorem mask_maskOf (P : Prop) [Decidable P] : VG.Proof.Weierstrass.mask P = maskOf (decide P) := by
  unfold VG.Proof.Weierstrass.mask maskOf; by_cases h : P <;> simp [h]

theorem same_mask (x y : BitVec 64) :
    ((x ^^^ y) &&& BitVec.ofInt 64 1) + BitVec.ofInt 64 (-1) = maskOf (decide (x.toNat % 2 = y.toNat % 2)) := by
  obtain hlow : (x ^^^ y) &&& 1 = if x.toNat % 2 = y.toNat % 2 then 0 else 1 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_xor, show (1 : BitVec 64).toNat = 1 from rfl,
      Nat.and_one_is_mod, show 2 = 2 ^ 1 from rfl, Nat.xor_mod_two_pow]
    rcases Nat.mod_two_eq_zero_or_one x.toNat with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one y.toNat with hy | hy <;> simp [hx, hy]
  rw [show BitVec.ofInt 64 1 = 1 from rfl, hlow]
  by_cases h : x.toNat % 2 = y.toNat % 2 <;> simp [h, maskOf] <;> decide

/-- `parMask a`: `a7` is the mask of the low bits of `[a]` and `PAR` differing. -/
theorem parMask_ok {s : State} {base : Addr} (hw : WsReg s base) {a : Nat} (ha : E.c.sl a < 2048) :
    WP isa (.block (Cfg.parMask E.c a)) s fun s' =>
      Rest [.t0, .t1, .a7] s s' ∧ s'.mem = s.mem ∧
      s'.gpr .a7 = maskOf (decide ((word s.mem base (E.c.sl a)).toNat % 2 ≠
        (word s.mem base (E.c.sl PAR)).toNat % 2)) := by
  rw [Cfg.parMask]
  refine ld_ws hw ha (sl8 _ _) fun s₁ u₁ => ?_
  refine ld_ws (hw.of_kp (Kp.of_upd u₁)) (d := E.c.sl PAR) (by kit_slots E) (sl8 _ _) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine WP.cons (exec_logicImm (by decide)) ?_
  obtain u₃a := Upd.write s₃ .t0 (s₃.gpr .t0 &&& BitVec.ofInt 64 1)
  refine wp_li (imm := 0) (by decide) fun s₄ u₄ => wp_sub fun s₅ u₅ => WP.block_nil ⟨?_, ?_, ?_⟩
  · have R := fun {a b : State} {d : Reg} {v : BitVec 64} (u : Upd a b d v) (h : d ∈ [Reg.t0, .t1, .a7]) =>
      u.rest (ws := [Reg.t0, .t1, .a7]) h
    exact ((((R u₁ (by decide)).trans (R u₂ (by decide))).trans (R u₃ (by decide))).trans
      (R u₃a (by decide))).trans ((R u₄ (by decide)).trans (R u₅ (by decide)))
  · rw [u₅.mem, u₄.mem, u₃a.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃a.gpr, u₃.gpr, u₂.other _ (by decide), u₂.gpr, u₁.gpr, u₁.mem,
      show BitVec.ofNat 64 0 = 0 from rfl, show BitVec.ofInt 64 1 = 1 from rfl,
      VG.Proof.EcKey.Compressed.xor_low_mask, mask_maskOf]

/-- `sameMask a`: `a7` is the mask of the low bits of `[a]` and `PAR` being equal. -/
theorem sameMask_ok {s : State} {base : Addr} (hw : WsReg s base) {a : Nat} (ha : E.c.sl a < 2048) :
    WP isa (.block (Cfg.sameMask E.c a)) s fun s' =>
      Rest [.t0, .t1, .a7] s s' ∧ s'.mem = s.mem ∧
      s'.gpr .a7 = maskOf (decide ((word s.mem base (E.c.sl a)).toNat % 2 =
        (word s.mem base (E.c.sl PAR)).toNat % 2)) := by
  rw [Cfg.sameMask]
  refine ld_ws hw ha (sl8 _ _) fun s₁ u₁ => ?_
  refine ld_ws (hw.of_kp (Kp.of_upd u₁)) (d := E.c.sl PAR) (by kit_slots E) (sl8 _ _) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine WP.cons (exec_logicImm (by decide)) ?_
  obtain u₃a := Upd.write s₃ .t0 (s₃.gpr .t0 &&& BitVec.ofInt 64 1)
  refine WP.cons (exec_addi (by decide)) ?_
  obtain u₄ := Upd.write (s₃.write .t0 (s₃.gpr .t0 &&& BitVec.ofInt 64 1)) .a7
    ((s₃.write .t0 (s₃.gpr .t0 &&& BitVec.ofInt 64 1)).gpr .t0 + BitVec.ofInt 64 (-1))
  refine WP.block_nil ⟨?_, ?_, ?_⟩
  · have R := fun {a b : State} {d : Reg} {v : BitVec 64} (u : Upd a b d v) (h : d ∈ [Reg.t0, .t1, .a7]) =>
      u.rest (ws := [Reg.t0, .t1, .a7]) h
    exact ((((R u₁ (by decide)).trans (R u₂ (by decide))).trans (R u₃ (by decide))).trans
      (R u₃a (by decide))).trans (R u₄ (by decide))
  · rw [u₄.mem, u₃a.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₄.gpr, u₃a.gpr, u₃.gpr, u₂.other _ (by decide), u₂.gpr, u₁.gpr, u₁.mem, same_mask]

/-- The end: the masks of `y² = rhs` and of the chosen root's parity into the
flag, the root of the first byte's parity chosen, and the point (or zeros)
to `out`, the flag's low bit returned and the saved registers restored. -/
theorem dfin_ok {s : State} {base out : Addr} (hw : WsReg s base) (h2 : s.gpr .s2 = out)
    (hfit : out.toNat + (1 + 2 * E.L) ≤ 2 ^ 64)
    (hout : ∀ i < 1 + 2 * E.L, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hdis : (⟨out, 1 + 2 * E.L⟩ : Region).Disjoint ⟨base, 8192⟩)
    {c : Bool} (hF : word s.mem base (E.c.sl FLAG) = maskOf c) {pr : Nat}
    (hpr : (word s.mem base (E.c.sl PAR)).toNat % 2 = pr) :
    WP isa (.block (zeroMask E.c.n (E.c.sl DIF) ++ andFlag E.c ++ Cfg.parMask E.c Y1 ++
      sel E.c.n (E.c.sl YF) (E.c.sl Y1) (E.c.sl Y2) ++ Cfg.sameMask E.c YF ++ andFlag E.c ++
      ldAt .a7 wb (E.c.sl FLAG) ++ E.pointOutC CX YF)) s fun s' =>
      s'.gpr .a0 = (if (c && decide (sv E.c base s DIF = 0)) &&
          decide ((if sv E.c base s Y1 % 2 ≠ pr then sv E.c base s Y2 else sv E.c base s Y1) % 2 = pr) then 1 else 0) ∧
      bytesAt s'.mem out (1 + 2 * E.L) = (if (c && decide (sv E.c base s DIF = 0)) &&
          decide ((if sv E.c base s Y1 % 2 ≠ pr then sv E.c base s Y2 else sv E.c base s Y1) % 2 = pr) then 4 else 0) ::
        (toBytes E.L (if (c && decide (sv E.c base s DIF = 0)) &&
          decide ((if sv E.c base s Y1 % 2 ≠ pr then sv E.c base s Y2 else sv E.c base s Y1) % 2 = pr) then
            sv E.c base s CX else 0) ++
        toBytes E.L (if (c && decide (sv E.c base s DIF = 0)) &&
          decide ((if sv E.c base s Y1 % 2 ≠ pr then sv E.c base s Y2 else sv E.c base s Y1) % 2 = pr) then
            (if sv E.c base s Y1 % 2 ≠ pr then sv E.c base s Y2 else sv E.c base s Y1) else 0)) ∧
      s'.gpr .s0 = word s.mem base 0 ∧ s'.gpr .s1 = word s.mem base 8 ∧ s'.gpr .s2 = word s.mem base 16 ∧
      s'.gpr .ra = word s.mem base 24 ∧ s'.gpr .s3 = word s.mem base 32 ∧
      (∀ r ∈ preserved, r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp := by
  obtain h9 := E.n9
  obtain h1 := E.n1
  obtain hfl := sl_lo E.c FLAG
  obtain hyf := sl_lo E.c YF
  obtain fit : ∀ i, i < 45 → E.c.sl i + 8 * E.c.n ≤ 4096 := fun _ hi => sl_top h9 (by omega_using [hi])
  obtain top : ∀ i, i < 45 → E.c.sl i + 8 * E.c.n ≤ 2 ^ 64 := fun i hi => Nat.le_trans (fit i hi) (by decide)
  simp only [List.append_assoc]
  -- `y² = rhs`.
  refine WP.block_append (WP.mono (zeroMask_ok hw (n := E.c.n) (a := E.c.sl DIF) (sl8 _ _) (fit DIF (by decide)))
    fun s₁ ⟨r₁, m₁, g₁⟩ => ?_)
  obtain hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono (E.andFlag_ok hw₁) fun s₂ ⟨f₂, r₂, O₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  obtain w₂ : ∀ i, i < 44 → wordsVal s₂.mem base (E.c.sl i) E.c.n = sv E.c base s i := fun i hi => by
    rw [O₂.wordsVal (.inl (sl_le _ hi)) (top i (by omega_using [hi])), m₁]
  obtain wd₂ : ∀ i, i < 44 → word s₂.mem base (E.c.sl i) = word s.mem base (E.c.sl i) := fun i hi => by
    obtain hle := sl_le E.c (i := i) (j := FLAG) hi
    obtain ht := top i (by omega_using [hi])
    rw [O₂.word (.inl (by omega_using [hle, h1])) (by omega_using [ht, h1]), m₁]
  -- The root of the first byte's parity.
  refine WP.block_append (WP.mono (E.parMask_ok hw₂ (a := Y1) (by kit_slots E)) fun s₃ ⟨r₃, m₃, g₃⟩ => ?_)
  obtain hw₃ := hw₂.of_rest r₃
  obtain par₂ : (word s₂.mem base (E.c.sl PAR)).toNat % 2 = pr := by rw [wd₂ PAR (by decide), hpr]
  obtain y1₂ : (word s₂.mem base (E.c.sl Y1)).toNat % 2 = sv E.c base s Y1 % 2 := by
    rw [VG.Proof.EcKey.Compressed.slot_parity s₂.mem base (E.c.sl Y1) E.c.n h1]
    exact congrArg (· % 2) (w₂ Y1 (by decide))
  rw [par₂, y1₂] at g₃
  refine WP.block_append (WP.mono (sel_ok (decide (sv E.c base s Y1 % 2 ≠ pr)) E.c.n hw₃ g₃ (o := E.c.sl YF)
    (a := E.c.sl Y1) (b := E.c.sl Y2) (sl8 _ _) (sl8 _ _) (sl8 _ _) (fit YF (by decide)) (fit Y1 (by decide))
    (fit Y2 (by decide)) (.inr (sl_le _ (by decide))) (.inr (sl_le _ (by decide)))) fun s₄ ⟨v₄, r₄, O₄⟩ => ?_)
  obtain hw₄ := hw₃.of_rest r₄
  obtain yf₄ : wordsVal s₄.mem base (E.c.sl YF) E.c.n =
      if sv E.c base s Y1 % 2 ≠ pr then sv E.c base s Y2 else sv E.c base s Y1 := by
    rw [v₄, m₃, w₂ Y1 (by decide), w₂ Y2 (by decide)]
    by_cases h : sv E.c base s Y1 % 2 ≠ pr <;> simp [h]
  generalize hy : (if sv E.c base s Y1 % 2 ≠ pr then sv E.c base s Y2 else sv E.c base s Y1) = y at yf₄
  refine WP.block_append (WP.mono (E.sameMask_ok hw₄ (a := YF) (by kit_slots E)) fun s₅ ⟨r₅, m₅, g₅⟩ => ?_)
  obtain hw₅ := hw₄.of_rest r₅
  obtain par₄ : (word s₄.mem base (E.c.sl PAR)).toNat % 2 = pr := by
    rw [O₄.word (by kit_slots E) (by kit_slots E), m₃, par₂]
  obtain yf₄' : (word s₄.mem base (E.c.sl YF)).toNat % 2 = y % 2 := by
    rw [VG.Proof.EcKey.Compressed.slot_parity s₄.mem base (E.c.sl YF) E.c.n h1, yf₄]
  rw [par₄, yf₄'] at g₅
  refine WP.block_append (WP.mono (E.andFlag_ok hw₅) fun s₆ ⟨f₆, r₆, O₆⟩ => ?_)
  obtain hw₆ := hw₅.of_rest r₆
  refine ldAt_ws hw₆ (d := E.c.sl FLAG) (by kit_slots E) (sl8 _ _) fun s₇ u₇ => ?_
  obtain hw₇ := hw₆.of_kp (Kp.of_upd u₇)
  generalize hB : ((c && decide (sv E.c base s DIF = 0)) && decide (y % 2 = pr)) = B
  obtain fl₆ : word s₆.mem base (E.c.sl FLAG) = maskOf B := by
    rw [f₆, m₅, O₄.word (by kit_slots E) (by kit_slots E), m₃, f₂, g₁, g₅, m₁, hF, maskOf_and, maskOf_and, ← hB]
  obtain a₇ : s₇.gpr .a7 = maskOf B := by rw [u₇.gpr, fl₆]
  obtain q₇ : s₇.gpr .s2 = out := by
    rw [u₇.other _ (by decide), r₆.gpr _ (by decide), r₅.gpr _ (by decide), r₄.gpr _ (by decide),
      r₃.gpr _ (by decide), r₂.gpr _ (by decide), r₁.gpr _ (by decide), h2]
  obtain wr₇ : s₇.wr = s.wr := by rw [u₇.wr, r₆.wr, r₅.wr, r₄.wr, r₃.wr, r₂.wr, r₁.wr]
  refine WP.mono (E.pointOut_ok hw₇ q₇ hfit (by rw [wr₇]; exact hout) hdis a₇ (by rw [u₇.mem]; exact fl₆)
    (xo := CX) (yo := YF) (by decide) (by decide))
    fun s' ⟨a0', b', s0', s1', s2', ra', s3', regs', sp'⟩ => ?_
  have m₇₄ : s₇.mem = s₆.mem := u₇.mem
  obtain w₇ : ∀ d, d + 8 ≤ 40 → word s₇.mem base d = word s.mem base d := fun d hd => by
    rw [m₇₄, O₆.word (.inl (by omega_using [hd, hfl])) (by omega_using [hd]), m₅,
      O₄.word (.inl (by omega_using [hd, hyf])) (by omega_using [hd]), m₃,
      O₂.word (.inl (by omega_using [hd, hfl])) (by omega_using [hd]), m₁]
  obtain cx₇ : sv E.c base s₇ CX = sv E.c base s CX := by
    show wordsVal _ _ _ _ = _
    rw [m₇₄, O₆.wordsVal (.inl (sl_le _ (i := CX) (j := FLAG) (by decide))) (top CX (by decide)), m₅,
      O₄.wordsVal (sl_sep _ (i := CX) (j := YF) (by decide)) (top CX (by decide)), m₃, w₂ CX (by decide)]
  obtain yf₇ : sv E.c base s₇ YF = y := by
    show wordsVal _ _ _ _ = _
    rw [m₇₄, O₆.wordsVal (.inl (sl_le _ (i := YF) (j := FLAG) (by decide))) (top YF (by decide)), m₅, yf₄]
  refine ⟨a0', by rw [b', cx₇, yf₇], by rw [s0', w₇ 0 (by decide)], by rw [s1', w₇ 8 (by decide)],
    by rw [s2', w₇ 16 (by decide)], by rw [ra', w₇ 24 (by decide)], by rw [s3', w₇ 32 (by decide)],
    fun r hr h0 h1 h2' h3' => ?_, by rw [sp', u₇.sp, r₆.sp, r₅.sp, r₄.sp, r₃.sp, r₂.sp, r₁.sp]⟩
  obtain hn : r ∉ [Reg.t0, .t1, .t3, .t4, .a7] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> exact absurd hr (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  rw [regs' r hr h0 h1 h2' h3', u₇.other _ hn.2.2.2.2, r₆.gpr _ (by simp [hn.1]),
    r₅.gpr _ (by simp [hn.1, hn.2.1, hn.2.2.2.2]), r₄.gpr _ (by simp [hn.1, hn.2.1]),
    r₃.gpr _ (by simp [hn.1, hn.2.1, hn.2.2.2.2]), r₂.gpr _ (by simp [hn.1]),
    r₁.gpr _ (by simp [hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2])]

/-! ### The whole decompression, for `p ≡ 3 (mod 4)` -/

/-- The root's power's slots. -/
theorem sqrtLay (c : Cfg) (h1 : 1 ≤ c.n) (h9 : c.n ≤ 9) : PowLayR (Cfg.sqrtP c) c.n := by
  obtain h := rvOwn_cases c.n
  constructor
  all_goals first
    | exact sl8 _ _
    | exact h1
    | (simp only [Cfg.sqrtP, powWx, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        Cfg.sl, slot, ACC, PT, RHS, ONEP, EXPS, T0, own]; omega_using [h1, h9, h])

theorem par_bit (b : BitVec 8) : (b.setWidth 64 &&& BitVec.ofInt 64 1).toNat % 2 = b.toNat % 2 := by
  revert b; decide

theorem neg_ofNat {p : Nat} [NeZero p] {v : Nat} (hv : v < p) : Fin.ofNat p ((p - v) % p) = -Fin.ofNat p v := by
  apply Fin.ext
  rw [Fin.val_ofNat, Fin.neg_def, Fin.val_ofNat, Nat.mod_eq_of_lt hv, Nat.mod_mod]

/-- `vg_ec_<curve>_decompress_public_key`, as the kit reads and writes its numbers. -/
def decompProg : Prog isa :=
  .seq (.block (saveCode .a2 ++ E.load (E.c.sl CX) .a1 1 ++ Cfg.parCode E.c .a1 ++ Cfg.tagMask .a1 ++
    sdAt .a7 wb (E.c.sl FLAG) ++ constCode E.c ++ setConst E.c.n (E.c.sl EXPS) ((E.c.C.p + 1) / 4) ++
    ltMask E.c.n (E.c.sl CX) (E.c.sl MP) ++ andFlag E.c)) <|
  .seq (fprog E.c.FP (Cfg.rhsOps E.c)) <|
  .seq (pow (Cfg.sqrtP E.c) E.c.FP) <|
  .seq (fprog E.c.FP (Cfg.rootOps E.c)) <|
  .block (zeroMask E.c.n (E.c.sl DIF) ++ andFlag E.c ++ Cfg.parMask E.c Y1 ++
    sel E.c.n (E.c.sl YF) (E.c.sl Y1) (E.c.sl Y2) ++ Cfg.sameMask E.c YF ++ andFlag E.c ++
    ldAt .a7 wb (E.c.sl FLAG) ++ E.pointOutC CX YF)

/-- `vg_ec_<curve>_decompress_public_key`'s postcondition, by register. -/
def DPostC (s s' : State) : Prop :=
  let bs := bytesAt s.mem (s.gpr .a1) (1 + E.L)
  (s'.gpr .a0 = 1 ∧ ∃ Q, Spec.EcKey.matchesCompressedPublicKey E.c.C bs Q ∧
      bytesAt s'.mem (s.gpr .a0) (1 + 2 * E.L) = Spec.EcKey.encodePoint Q) ∨
    (s'.gpr .a0 = 0 ∧ (¬ ∃ Q, Spec.EcKey.matchesCompressedPublicKey E.c.C bs Q) ∧
      bytesAt s'.mem (s.gpr .a0) (1 + 2 * E.L) = List.replicate (1 + 2 * E.L) 0)

/-- Layout facts: slots given by number against the ranges that `rhs`, the power and the root's checks
write, unfolded to arithmetic in the words' count, with its bounds and the place of the field's own working
space. -/
local macro "kit_lay" "[" hs:term,* "]" : tactic => `(tactic| (
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq,
    Cfg.rhsOps, List.tail, List.map_cons, List.map_nil, FOp.out, powWx, Cfg.sqrtP, Cfg.sl, slot, MP, ZERO, ONE,
    ONEP, AP, BP, R2P, FLAG, CX, CXM, ACC, PT, PAR, EXPS, RHS, TT, YSQ, DIF, Y1, Y2, YF, T0, T1, T2, T3]
  omega_using [$hs,*]))

/-- `vg_ec_<curve>_decompress_public_key` by register, for `p ≡ 3 (mod 4)`. -/
theorem decompress_ok (h34 : E.c.C.p % 4 = 3) (hL : Law E.c.C) {s : State} (hs : E.DPre s) :
    WP isa E.decompProg s fun s' => abiPreserved s s' ∧ E.DPostC s s' := by
  obtain hp0 : 0 < E.c.C.p := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain hLn := E.Ln
  obtain h9 := E.n9
  obtain h1 : 1 ≤ E.c.n := E.n1
  obtain hplt := E.p_lt
  obtain hown : 64 + 8 * E.c.n * 45 + 8 ≤ own E.c.n := own_ge h9
  obtain top : ∀ i, i < 45 → E.c.sl i + 8 * E.c.n ≤ 2 ^ 64 := fun i hi =>
    Nat.le_trans (sl_top h9 (by omega_using [hi])) (by decide)
  have hs' := hs
  obtain ⟨hrd, hwr, hpo, hpw, how, hfo, hfp, hfs, hal⟩ := hs'
  rw [decompProg]
  refine WP.seq (WP.mono (E.dsetup_ok hs) fun s₁ S => ?_)
  obtain ⟨hw₁, S2, S3, Sregs, Srd, Swr, Ssp, Ssv0, Ssv1, Ssv2, Ssv3, Ssv4, Sx, Spar, Sflag, Scs, Sexps⟩ := S
  generalize hb : s.gpr .a2 = base at hw₁ S3 Ssv0 Ssv1 Ssv2 Ssv3 Ssv4 Sx Spar Sflag Scs Sexps hwr hpw how
  -- `rhs`.
  refine WP.seq (WP.mono (E.rhs_ok hw₁ (E.const_at Scs 10) (E.const_at Scs 5) (E.const_at Scs 11))
    fun s₂ ⟨K₂, U₂, lt₂, v₂⟩ => ?_)
  obtain hw₂ := hw₁.of_kp K₂
  obtain one₂ : sv E.c base s₂ ONEP = 2 ^ (64 * E.c.n) % E.c.C.p := by
    show wordsVal _ _ _ _ = _
    rw [U₂.wordsVal (by kit_lay [h9, h1, hown]) (top ONEP (by decide))]
    exact (E.const_at Scs 4).trans (by
      show 1 * 2 ^ (64 * E.c.n) % E.c.C.p = 2 ^ (64 * E.c.n) % E.c.C.p; rw [Nat.one_mul])
  obtain exps₂ : sv E.c base s₂ EXPS = (E.c.C.p + 1) / 4 := by
    show wordsVal _ _ _ _ = _
    rw [U₂.wordsVal (by kit_lay [h9, h1, hown]) (top EXPS (by decide))]; exact Sexps
  -- The root.
  refine WP.seq (WP.mono (pow_kit (P := Cfg.sqrtP E.c) (F := E.c.FP) E.field_ok E.FPk E.FPm rfl
    (sqrtLay E.c h1 h9) E.unit hw₂ one₂
    (by show sv E.c base s₂ EXPS < 2 ^ (64 * E.c.n); rw [exps₂]; omega_using [hplt]))
    fun s₃ ⟨Kc₃, U₃, lt₃, v₃⟩ => ?_)
  obtain hw₃ := hw₂.of_kc Kc₃
  obtain rhs₃ : sv E.c base s₃ RHS = sv E.c base s₂ RHS :=
    U₃.wordsVal (by kit_lay [h9, h1, hown]) (top RHS (by decide))
  obtain one₃ : sv E.c base s₃ ONE = 1 := by
    show wordsVal _ _ _ _ = _
    rw [U₃.wordsVal (by kit_lay [h9, h1, hown]) (top ONE (by decide)),
      U₂.wordsVal (by kit_lay [h9, h1, hown]) (top ONE (by decide))]; exact E.const_at Scs 3
  obtain zero₃ : sv E.c base s₃ ZERO = 0 := by
    show wordsVal _ _ _ _ = _
    rw [U₃.wordsVal (by kit_lay [h9, h1, hown]) (top ZERO (by decide)),
      U₂.wordsVal (by kit_lay [h9, h1, hown]) (top ZERO (by decide))]; exact E.const_at Scs 2
  -- The root's checks.
  refine WP.seq (WP.mono (E.root_ok hw₃ lt₃ (by rw [rhs₃]; exact lt₂) one₃ zero₃)
    fun s₄ ⟨K₄, U₄, ltd₄, vd₄, lty₄, vy₄, y2₄⟩ => ?_)
  obtain hw₄ := hw₃.of_kp K₄
  obtain U₁₄ := (U₂.trans U₃).trans U₄
  obtain lo : ∀ d, d + 8 ≤ 40 → word s₄.mem base d = word s₁.mem base d := fun d hd =>
    lo_word U₁₄ (by kit_lay [h9, h1, hown]) hd
  obtain hF : word s₄.mem base (E.c.sl FLAG) = maskOf (decide (s.mem (s.gpr .a1) = 2 ∨ s.mem (s.gpr .a1) = 3) &&
      decide (ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) E.L) < E.c.C.p)) := by
    rw [U₁₄.word (by kit_lay [h9, h1, hown]) (by kit_slots E)]; exact Sflag
  obtain hpr : (word s₄.mem base (E.c.sl PAR)).toNat % 2 = (s.mem (s.gpr .a1)).toNat % 2 := by
    rw [U₁₄.word (by kit_lay [h9, h1, hown]) (by kit_slots E), Spar, par_bit]
  obtain cx₄ : sv E.c base s₄ CX = ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) E.L) := by
    show wordsVal _ _ _ _ = _
    rw [U₁₄.wordsVal (by kit_lay [h9, h1, hown]) (top CX (by decide))]; exact Sx
  obtain h2₄ : s₄.gpr .s2 = s.gpr .a0 := by
    rw [K₄.gpr _ (by decide), Kc₃.gpr _ (by decide) (by decide), K₂.gpr _ (by decide), S2]
  obtain wr₄ : s₄.wr = s.wr := by rw [K₄.wr, Kc₃.wr, K₂.wr, Swr]
  refine WP.mono (E.dfin_ok hw₄ h2₄ hfo (fun i hi => by
      rw [wr₄, hwr]
      exact ⟨_, List.mem_cons_self .., Offset.contains_base (s.gpr .a0) (d := i) (n := 1) (k := 1 + 2 * E.L)
        (by omega_using [hi]) (by omega_using [hi, hLn, h9])⟩) how hF hpr)
    fun s' ⟨a0', b', s0', s1', s2', ra', s3', regs', sp'⟩ => ?_
  -- The registers.
  refine ⟨⟨fun r hr => ?_, by rw [sp', K₄.sp, Kc₃.sp, K₂.sp, Ssp],
    by rw [ra', lo 24 (by decide), Ssv3]⟩, ?_⟩
  · by_cases h0 : r = .s0
    · subst h0; rw [s0', lo 0 (by decide), Ssv0]
    by_cases h1 : r = .s1
    · subst h1; rw [s1', lo 8 (by decide), Ssv1]
    by_cases h2' : r = .s2
    · subst h2'; rw [s2', lo 16 (by decide), Ssv2]
    by_cases h3' : r = .s3
    · subst h3'; rw [s3', lo 32 (by decide), Ssv4]
    rw [regs' r hr h0 h1 h2' h3', K₄.gpr r hr, Kc₃.gpr r hr h1, K₂.gpr r hr, Sregs r h0 h2' h3' hr]
  -- The values.
  have x₁ : sv E.c base s₁ CX = ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) E.L) := Sx
  rw [cx₄] at b'
  generalize hx : ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) E.L) = x at x₁ a0' b' hF
  generalize htag : s.mem (s.gpr .a1) = tag at a0' b' hF hpr
  rw [x₁] at v₂
  obtain v₃' : toM E.c.C.p (2 ^ (64 * E.c.n)) (sv E.c base s₃ ACC) =
      toM E.c.C.p (2 ^ (64 * E.c.n)) (sv E.c base s₂ RHS) ^ ((E.c.C.p + 1) / 4) := by
    have := v₃
    rw [show wordsVal s₂.mem base (Cfg.sqrtP E.c).bits E.c.n = (E.c.C.p + 1) / 4 from exps₂] at this
    exact this
  rw [rhs₃] at vd₄
  generalize hxf : (Fin.ofNat E.c.C.p x : Fe E.c.C) = xf at v₂
  generalize hrhs : xf * xf * xf + Fin.ofNat E.c.C.p E.c.C.a * xf + Fin.ofNat E.c.C.p E.c.C.b = rhsF at v₂
  rw [v₂] at v₃' vd₄
  rw [v₃'] at vy₄ vd₄
  generalize hr : rhsF ^ ((E.c.C.p + 1) / 4) = r at vy₄ vd₄
  obtain hy1 : r.val = sv E.c base s₄ Y1 := by rw [← vy₄, Fin.val_ofNat, Nat.mod_eq_of_lt lty₄]
  generalize hyN : (if sv E.c base s₄ Y1 % 2 ≠ tag.toNat % 2 then sv E.c base s₄ Y2 else sv E.c base s₄ Y1) = yN
    at a0' b'
  obtain hyNlt : yN < E.c.C.p := by
    rw [← hyN]; split
    · rw [y2₄]; exact Nat.mod_lt _ hp0
    · exact lty₄
  obtain hch : VG.Impl.EcKey.Compressed.chooseRoot r (tag.toNat % 2) = Fin.ofNat E.c.C.p yN := by
    unfold VG.Impl.EcKey.Compressed.chooseRoot
    rw [hy1, ← hyN]
    by_cases h : sv E.c base s₄ Y1 % 2 = tag.toNat % 2
    · rw [ite_eq_left h, ite_eq_right (fun h' => h' h), vy₄]
    · rw [ite_eq_right h, ite_eq_left h, y2₄, neg_ofNat lty₄, vy₄]
  obtain hval : (Fin.ofNat E.c.C.p yN : Fe E.c.C).val = yN := by rw [Fin.val_ofNat, Nat.mod_eq_of_lt hyNlt]
  obtain hsq : VG.Impl.EcKey.Compressed.chooseRoot r (tag.toNat % 2) *
      VG.Impl.EcKey.Compressed.chooseRoot r (tag.toNat % 2) = r * r := by
    unfold VG.Impl.EcKey.Compressed.chooseRoot; split
    · rfl
    · rw [Lean.Grind.Ring.neg_mul, Lean.Grind.Ring.mul_neg, Lean.Grind.AddCommGroup.neg_neg]
  obtain hdif : sv E.c base s₄ DIF = 0 ↔ r * r = rhsF := by
    rw [← toM_eq_zero_iff E.unit ltd₄, vd₄]
    exact Lean.Grind.AddCommGroup.sub_eq_zero_iff
  -- The specification's decoding.
  obtain hsplit : bytesAt s.mem (s.gpr .a1) (1 + E.L) =
      tag :: bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) E.L := by
    obtain h1 : bytesAt s.mem (s.gpr .a1) 1 = [tag] := by
      simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero, htag]
    rw [VG.Proof.Weierstrass.bytesAt_add, h1]; rfl
  obtain hlen : (bytesAt s.mem (s.gpr .a1) (1 + E.L)).length = E.c.C.len + 1 := by
    rw [VG.Proof.Weierstrass.length_bytesAt, E.len, Nat.add_comm]
  obtain hhd : (bytesAt s.mem (s.gpr .a1) (1 + E.L)).head? = some tag := by rw [hsplit]; rfl
  obtain hxv : ofBytes ((bytesAt s.mem (s.gpr .a1) (1 + E.L)).drop 1) = x := by
    rw [hsplit, List.drop_one, List.tail_cons]; exact hx
  obtain hdec := VG.Proof.EcKey.Compressed.decode_checked_eq (C := E.c.C)
    VG.Impl.EcKey.Compressed.rootThreeModFour hlen hhd hxv
  simp only [] at hdec
  rw [hxf, hrhs, VG.Impl.EcKey.Compressed.rootThreeModFour, VG.Proof.Weierstrass.pow_eq_npow, hr, hch] at hdec
  rw [hch] at hsq
  rw [hval] at hdec
  generalize hB : (((decide (tag = 2 ∨ tag = 3) && decide (x < E.c.C.p)) && decide (sv E.c base s₄ DIF = 0)) &&
    decide (yN % 2 = tag.toNat % 2)) = B at a0' b'
  obtain key : B = true ↔ ((tag = 2 ∨ tag = 3) ∧ x < E.c.C.p) ∧
      (Fin.ofNat E.c.C.p yN * Fin.ofNat E.c.C.p yN = rhsF ∧ yN % 2 = tag.toNat % 2) := by
    rw [← hB, hsq, ← hdif]
    simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  obtain hroot := VG.Proof.Weierstrass.rootFacts_three_mod_four hL h34
  unfold DPostC
  simp only []
  cases B
  · have hn : ¬ (((tag = 2 ∨ tag = 3) ∧ x < E.c.C.p) ∧
        (Fin.ofNat E.c.C.p yN * Fin.ofNat E.c.C.p yN = rhsF ∧ yN % 2 = tag.toNat % 2)) := fun h =>
      Bool.false_ne_true (key.mpr h)
    rw [ite_eq_right hn] at hdec
    refine Or.inr ⟨a0', (VG.Proof.EcKey.Compressed.decode_none_iff hroot _).mp hdec, ?_⟩
    rw [b', ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true]
    exact zeros_eq E.L
  · have hc := key.mp rfl
    rw [ite_eq_left hc] at hdec
    refine Or.inl ⟨a0', _, VG.Proof.EcKey.Compressed.decode_sound hdec, ?_⟩
    rw [b']
    show _ = 4 :: (toBytes E.c.C.len xf.val ++ toBytes E.c.C.len (Fin.ofNat E.c.C.p yN : Fe E.c.C).val)
    rw [E.len, hval, ← hxf, Fin.val_ofNat, Nat.mod_eq_of_lt hc.1.2]
    rfl

end Kit

end VG.Proof.Ecdh.RISCV64
