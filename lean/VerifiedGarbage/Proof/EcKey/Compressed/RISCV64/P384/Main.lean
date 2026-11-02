module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.Exchange
public import VerifiedGarbage.Impl.EcKey.Compressed.P384.RISCV64
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
import VerifiedGarbage.Proof.EcKey.Compressed.Encode
import VerifiedGarbage.Proof.EcKey.Compressed.Decode
import VerifiedGarbage.Impl.EcKey.Compressed.Root
import VerifiedGarbage.Proof.Weierstrass.Sqrt
import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.PublicKey
import VerifiedGarbage.Proof.EcKey.Compressed.Parity
import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.CheckVerified
import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.CheckLit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Weierstrass.Words

/-!
# P-384's point compression and decompression on RISC-V: correctness

`vg_ec_p384_compress_public_key` meets its contract by register (`compRV`,
`compress_ok`): ECDH's saves and its reading of the point, the flag and the
constants (`peerLoad_ok`), the check of the point (`check_ok`), and
`02 + (y mod 2)` and `x` (or zeros) under the flag; the specification's
encoding is `compress_eq`'s (`Proof/EcKey/Compressed/Encode.lean`).
-/

@[expose] public section

-- `p`, below `2^384`, is evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.EcKey.Compressed.RISCV64.P384

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg VG.Impl.EcKey.Compressed.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.P384
open VG.Proof.Ecdh.RISCV64.P384
open VG.Proof.X25519.RISCV64 (Rest wp_and)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_nil writeBytes_append)

/-- `vg_ec_p384_compress_public_key(out = a0, public = a1, scratch = a2)`, by
register. -/
def compRV : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 49⟩
    let pk : Region := ⟨s.gpr .a1, 97⟩
    let ws : Region := ⟨s.gpr .a2, 8192⟩
    s.rd = [pk] ∧ s.wr = [out, ws] ∧ pk.Disjoint out ∧ pk.Disjoint ws ∧ out.Disjoint ws ∧
      (s.gpr .a0).toNat + 49 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 97 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8192 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat % 8 = 0
  post s s' :=
    match Spec.EcKey.compressPublicKey Spec.P384.curve (bytesAt s.mem (s.gpr .a1) 97) with
    | some bs => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) 49 = bs
    | none => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) 49 = List.replicate 49 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2

theorem tag_eq (m : Mem) (base : Addr) (B : Bool) :
    ((((word m base (p384.sl CY) &&& BitVec.ofInt 64 1) + BitVec.ofInt 64 2) &&& maskOf B).setWidth 8) =
      if B then BitVec.ofNat 8 (2 + wordsVal m base (p384.sl CY) 6 % 2) else 0 :=
  VG.Proof.EcKey.Compressed.tag_byte m base (p384.sl CY) 6 (by decide) B

/-- `vg_ec_p384_compress_public_key` by register. -/
theorem compress_ok {s : State} (hs : compRV.pre s) :
    WP isa compressP384 s fun s' => abiPreserved s s' ∧ compRV.post s s' := by
  obtain ⟨hrd, hwr, hpo, hpw, how, hfo, hfp, hfs, hal⟩ := hs
  rw [compressP384, Cfg.compressFn]
  generalize hb : s.gpr .a2 = base at hwr hpw how hfs hal
  have hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (save_ok hb hwr' hfs hal)
    fun s₁ ⟨hw₁, h3₁, o₁, g₁, rd₁, wr₁, sp₁, U₁, w0, w1, w2, w3, w4⟩ => ?_))
  have a1 : s₁.gpr .a1 = s.gpr .a1 := g₁ _ (by decide) (by decide) (by decide)
  simp only [← List.append_assoc]
  refine WP.mono (peerLoad_ok hw₁ (q := .a1) (by decide) (by rw [rd₁, wr₁, a1, hrd]; simp)
    (by rw [a1]; exact hpw) (by rw [a1]; exact hfp)) fun s₂ ⟨hw₂, r₂, U₂, x₂, y₂, f₂, c₂⟩ => ?_
  have h3₂ : s₂.gpr .s3 = base := by rw [r₂.gpr _ (by decide), h3₁]
  have hf₂ : word s₂.mem base FL = 0 ∨ word s₂.mem base FL = BitVec.allOnes 64 := by
    rw [f₂]; unfold maskOf; split <;> simp
  -- The check.
  refine WP.seq (WP.mono (check_ok hw₂ h3₂ c₂ hf₂) fun s₃ ⟨K₃, U₃, f₃, _, _⟩ => ?_)
  have hw₃ := hw₂.of_kp K₃
  have q₃ : s₃.gpr .s2 = s.gpr .a0 := by rw [K₃.gpr _ (by decide), r₂.gpr _ (by decide), o₁]
  have wr₃ : s₃.wr = s.wr := by rw [K₃.wr, r₂.wr, wr₁]
  generalize hout : s.gpr .a0 = out at q₃ hwr hpo how hfo
  have hdis : (⟨out, 49⟩ : Region).Disjoint ⟨base, 8192⟩ := how
  -- The values.
  have x₁ : sv base s₂ CX = ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 48) := by
    rw [x₂, a1, bytesAt_unch U₁ (by decide) (sep_at' hpw hfp (off := 1) (k := 48) (by omega))]
  have y₁ : sv base s₂ CY = ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 49) 48) := by
    rw [y₂, a1, bytesAt_unch U₁ (by decide) (sep_at' hpw hfp (off := 49) (k := 48) (by omega))]
  have b₁ : s₁.mem (s₁.gpr .a1) = s.mem (s.gpr .a1) := by
    have h1 := bytesAt_unch U₁ (q := s.gpr .a1) (n := 1) (by decide)
      (by simpa using sep_at' hpw hfp (off := 0) (k := 1) (by omega))
    simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h1
    simp only [BitVec.add_zero] at h1
    rw [a1, h1]
  generalize hx : sv base s₂ CX = x at x₁ f₃
  generalize hy : sv base s₂ CY = y at y₁ f₃
  generalize hB : (decide (s.mem (s.gpr .a1) = 4) && decide (CC.Valid x y)) = B
  have fl₃ : word s₃.mem base FL = maskOf B := by
    rw [f₃, f₂, b₁, mask_eq, maskOf_and, hB]
  have cy₃ : wordsVal s₃.mem base (p384.sl CY) 6 = y := by
    rw [U₃.wordsVal (by decide) (by decide)]; exact hy
  have cx₃ : wordsVal s₃.mem base (p384.sl CX) 6 = x := by
    rw [U₃.wordsVal (by decide) (by decide)]; exact hx
  -- The first byte.
  rw [show p384.n = 6 from rfl, retCode, restoreCode]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine ldAt_ws hw₃ (d := p384.sl FLAG) (by decide) (by decide) fun s₄ u₄ => ?_
  have hw₄ := hw₃.of_kp (Kp.of_upd u₄)
  refine ldAt_ws hw₄ (d := p384.sl CY) (by decide) (by decide) fun s₅ u₅ => ?_
  refine WP.cons (exec_logicImm (by decide)) ?_
  have u₅a := Upd.write s₅ .t0 (s₅.gpr .t0 &&& BitVec.ofInt 64 1)
  refine WP.cons (exec_addi (by decide)) ?_
  have u₅b := Upd.write (s₅.write .t0 (s₅.gpr .t0 &&& BitVec.ofInt 64 1)) .t0
    ((s₅.write .t0 (s₅.gpr .t0 &&& BitVec.ofInt 64 1)).gpr .t0 + BitVec.ofInt 64 2)
  refine wp_and fun s₆ u₆ => ?_
  have hw₆ := ((((hw₄.of_kp (Kp.of_upd u₅)).of_kp (Kp.of_upd u₅a)).of_kp (Kp.of_upd u₅b))).of_kp (Kp.of_upd u₆)
  have q₆ : s₆.gpr .s2 = out := by
    rw [u₆.other _ (by decide), u₅b.other _ (by decide), u₅a.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), q₃]
  have wr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅b.wr, u₅a.wr, u₅.wr, u₄.wr, wr₃]
  have a₆ : s₆.gpr .a7 = maskOf B := by
    rw [u₆.other _ (by decide), u₅b.other _ (by decide), u₅a.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      sl_FLAG, fl₃]
  have v₆ : (s₆.gpr .t0).setWidth 8 = if B then BitVec.ofNat 8 (2 + y % 2) else 0 := by
    rw [u₆.gpr, u₅b.gpr, u₅b.other _ (by decide), u₅a.gpr, u₅a.other _ (by decide), u₅.gpr, u₄.mem,
      u₅.other _ (by decide), u₄.gpr, sl_FLAG, fl₃, tag_eq, cy₃]
  have hout' : ∀ i < 49, InRegions s.wr (out + BitVec.ofNat 64 i) 1 := fun i hi => by
    rw [hwr]
    exact ⟨_, List.mem_cons_self .., Offset.contains_base out (d := i) (n := 1) (k := 49) (by omega) (by omega)⟩
  refine wp_sb (off := 0) (a := out) (by decide) (by rw [q₆, BitVec.add_zero])
    (by rw [wr₆]; simpa using hout' 0 (by decide)) fun s₇ u₇ => ?_
  have hw₇ := hw₆.of_kp (Kp.of_mupd u₇)
  have m₇ : s₇.mem = writeBytes s₃.mem out [if B then BitVec.ofNat 8 (2 + y % 2) else 0] := by
    rw [u₇.mem, v₆, u₆.mem, u₅b.mem, u₅a.mem, u₅.mem, u₄.mem]
    have := writeBytes_snoc s₃.mem out [] (if B then BitVec.ofNat 8 (2 + y % 2) else 0) (by decide)
    rw [List.nil_append, writeBytes_nil] at this
    rw [this]; simp
  have sp' : ∀ {off k : Nat}, off + k ≤ 49 → ∀ i < k,
      ¬ (⟨base, 8192⟩ : Region).Contains (out + BitVec.ofNat 64 off + BitVec.ofNat 64 i) 1 :=
    fun hk => sep_at' hdis hfo hk
  have U₇ : Unch base [(8192, 2 ^ 64)] s₃.mem s₇.mem := by
    rw [m₇]; exact writeBytes_unch _ fun i hi => by
      have := sp' (off := 0) (k := 1) (by decide) i (by simpa using hi); simpa using this
  have q₇ : s₇.gpr .s2 = out := by rw [u₇.gpr, q₆]
  have a₇ : s₇.gpr .a7 = maskOf B := by rw [u₇.gpr, a₆]
  -- `x`.
  refine WP.block_append (WP.mono (storeNum_ok _ 6 hw₇ a₇ (q := .s2) (a := p384.sl CX) (off := 1) (by decide)
    (by decide) (by decide) (by decide)
    (fun i hi => by rw [q₇, u₇.wr, wr₆]; exact hout' (1 + i) (by omega))
    (fun i hi => by rw [q₇]; exact out_of_disj hdis hfo (by omega))) fun s₈ ⟨r₈, m₈⟩ => ?_)
  have hw₈ := hw₇.of_rest r₈
  have xo₇ : wordsVal s₇.mem base (p384.sl CX) 6 = x := by rw [U₇.wordsVal (by decide) (by decide), cx₃]
  rw [q₇, xo₇] at m₈
  have U₈ : Unch base [(8192, 2 ^ 64)] s₇.mem s₈.mem := by
    rw [m₈]; exact writeBytes_unch _ fun i hi => sp' (off := 1) (k := 48) (by decide) i
      (by simpa [VG.Proof.Weierstrass.length_toBytes] using hi)
  have U₃₈ := U₇.trans U₈
  have hX := VG.Proof.Weierstrass.length_toBytes 48 (if B = true then x else 0)
  have bytes₈ : bytesAt s₈.mem out 49 = (if B then BitVec.ofNat 8 (2 + y % 2) else 0) ::
      toBytes 48 (if B then x else 0) := by
    have e1 := writeBytes_append s₃.mem out [if B then BitVec.ofNat 8 (2 + y % 2) else 0]
      (toBytes 48 (if B then x else 0)) (by rw [hX, List.length_singleton]; decide)
    simp only [List.length_singleton] at e1
    rw [m₈, m₇, show (8 * 6 : Nat) = 48 from rfl, e1]
    have := bytesAt_writeBytes s₃.mem out
      ([if B then BitVec.ofNat 8 (2 + y % 2) else 0] ++ toBytes 48 (if B then x else 0))
      (by simp only [List.length_append, List.length_singleton, hX]; decide)
    simp only [List.length_append, List.length_singleton, hX] at this
    rw [this]; rfl
  -- The return value and the restores.
  have wd : ∀ d ∈ [0, 8, 16, 24, 32], word s₈.mem base d = word s₁.mem base d := fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl <;>
      rw [U₃₈.word (by decide) (by decide), U₃.word (by decide) (by decide), U₂.word (by decide) (by decide)]
  have fl₈ : word s₈.mem base FL = maskOf B := by
    rw [U₃₈.word (by decide) (by decide), fl₃]
  refine ldAt_ws hw₈ (d := p384.sl FLAG) (by decide) (by decide) fun s₉ u₉ => ?_
  refine WP.cons (exec_logicImm (by decide)) ?_
  have u₉' := Upd.write s₉ .a0 (s₉.gpr .a0 &&& BitVec.ofInt 64 1)
  have hw₉ := (hw₈.of_kp (Kp.of_upd u₉)).of_kp (Kp.of_upd u₉')
  refine ldAt_ws hw₉ (d := 24) (by decide) (by decide) fun t₁ v₁ => ?_
  have hv₁ := hw₉.of_kp (Kp.of_upd v₁)
  refine ldAt_ws hv₁ (d := 16) (by decide) (by decide) fun t₂ v₂ => ?_
  have hv₂ : WsReg t₂ base := ⟨by rw [v₂.other _ (by decide)]; exact hv₁.s0, by rw [v₂.wr]; exact hv₁.wr,
    hv₁.nowrap, hv₁.al⟩
  refine ldAt_ws hv₂ (d := 8) (by decide) (by decide) fun t₃ v₃ => ?_
  have hv₃ : WsReg t₃ base := ⟨by rw [v₃.other _ (by decide)]; exact hv₂.s0, by rw [v₃.wr]; exact hv₂.wr,
    hv₂.nowrap, hv₂.al⟩
  refine ldAt_ws hv₃ (d := 32) (by decide) (by decide) fun t₄ v₄ => ?_
  have hv₄ : WsReg t₄ base := ⟨by rw [v₄.other _ (by decide)]; exact hv₃.s0, by rw [v₄.wr]; exact hv₃.wr,
    hv₃.nowrap, hv₃.al⟩
  refine ldAt_ws hv₄ (d := 0) (by decide) (by decide) fun t₅ v₅ => WP.block_nil ?_
  have M₄ : t₄.mem = s₈.mem := by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem, u₉'.mem, u₉.mem]
  have np : ∀ r ∈ preserved, r ∉ [Reg.t0, .t1, .a7, .a0, .ra] := by decide
  have gp : ∀ r ∈ preserved, r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → t₅.gpr r = s.gpr r := by
    intro r hr h0 h1 h2' h3'
    have hn := np r hr
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
  have a0' : t₅.gpr .a0 = if B then 1 else 0 := by
    rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide),
      v₁.other _ (by decide), u₉'.gpr, u₉.gpr, sl_FLAG, fl₈, and_one]
  have bytes' : bytesAt t₅.mem out 49 = (if B then BitVec.ofNat 8 (2 + y % 2) else 0) ::
      toBytes 48 (if B then x else 0) := by rw [v₅.mem, M₄]; exact bytes₈
  have hlen : (bytesAt s.mem (s.gpr .a1) 97).length = 2 * W.len + 1 := VG.Proof.Weierstrass.length_bytesAt _ _ _
  have hpb := peer_bytes s.mem (s.gpr .a1) 48
  have hhd : (bytesAt s.mem (s.gpr .a1) 97).head? = some (s.mem (s.gpr .a1)) := by rw [hpb]; rfl
  have hxv : ofBytes (((bytesAt s.mem (s.gpr .a1) 97).drop 1).take W.len) = x := by
    rw [show W.len = 48 from rfl, hpb, List.drop_one, List.tail_cons,
      List.take_left' (VG.Proof.Weierstrass.length_bytesAt _ _ _)]; exact x₁.symm
  have hyv : ofBytes ((bytesAt s.mem (s.gpr .a1) 97).drop (W.len + 1)) = y := by
    rw [show W.len = 48 from rfl, hpb, List.drop_succ_cons, List.drop_left' (VG.Proof.Weierstrass.length_bytesAt _ _ _)]
    exact y₁.symm
  unfold compRV
  simp only
  rw [hout, VG.Proof.EcKey.Compressed.compress_eq hlen hhd hxv hyv]
  have key : B = true ↔ VG.Proof.Ecdh.Valid W (s.mem (s.gpr .a1)) x y := by
    rw [← hB]
    unfold VG.Proof.Ecdh.Valid
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, valid_iff]
  by_cases hv : VG.Proof.Ecdh.Valid W (s.mem (s.gpr .a1)) x y
  · rw [ite_eq_left hv]
    rw [key.mpr hv] at a0' bytes'
    exact ⟨a0', bytes'⟩
  · rw [ite_eq_right hv]
    have hb' : B = false := by
      cases h : B
      · rfl
      · exact absurd (key.mp h) hv
    rw [hb'] at a0' bytes'
    exact ⟨a0', bytes'.trans (by rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true]; decide)⟩

/-! ## Decompression -/

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

/-- `vg_ec_p384_decompress_public_key(out = a0, public = a1, scratch = a2)`'s
precondition, by register. -/
def DPre (s : State) : Prop :=
  let out : Region := ⟨s.gpr .a0, 97⟩
  let pk : Region := ⟨s.gpr .a1, 49⟩
  let ws : Region := ⟨s.gpr .a2, 8192⟩
  s.rd = [pk] ∧ s.wr = [out, ws] ∧ pk.Disjoint out ∧ pk.Disjoint ws ∧ out.Disjoint ws ∧
    (s.gpr .a0).toNat + 97 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 49 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8192 ≤ 2 ^ 64 ∧
    (s.gpr .a2).toNat % 8 = 0

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
  x : sv (s.gpr .a2) s' CX = ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 48)
  par : word s'.mem (s.gpr .a2) (p384.sl PAR) = (s.mem (s.gpr .a1)).setWidth 64 &&& BitVec.ofInt 64 1
  flag : word s'.mem (s.gpr .a2) FL = maskOf (decide (s.mem (s.gpr .a1) = 2 ∨ s.mem (s.gpr .a1) = 3) &&
    decide (ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 48) < W.p))
  consts : ∀ e ∈ consts p384, sv (s.gpr .a2) s' e.1 = e.2
  exps : sv (s.gpr .a2) s' EXPS = (W.p + 1) / 4

theorem dsetup_ok {s : State} (hs : DPre s) :
    WP isa (.block (saveCode .a2 ++ loadNum p384.n (p384.sl CX) .a1 1 ++ Cfg.parCode p384 .a1 ++
      Cfg.tagMask .a1 ++ sdAt .a7 wb (p384.sl FLAG) ++ constCode p384 ++
      setConst p384.n (p384.sl EXPS) ((p384.C.p + 1) / 4) ++ ltMask p384.n (p384.sl CX) (p384.sl MP) ++
      andFlag p384)) s fun s' => DPost s s' := by
  obtain ⟨hrd, hwr, hpo, hpw, how, hfo, hfp, hfs, hal⟩ := hs
  generalize hb : s.gpr .a2 = base at hwr hpw how hfs hal
  have hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  rw [show p384.n = 6 from rfl]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (save_ok hb hwr' hfs hal)
    fun s₁ ⟨hw₁, h3₁, o₁, g₁, rd₁, wr₁, sp₁, U₁, w0, w1, w2, w3, w4⟩ => ?_)
  have a1 : s₁.gpr .a1 = s.gpr .a1 := g₁ _ (by decide) (by decide) (by decide)
  have rdp : (⟨s.gpr .a1, 49⟩ : Region) ∈ s₁.rd ++ s₁.wr := by rw [rd₁, wr₁, hrd]; simp
  -- `x`.
  refine WP.block_append (WP.mono (loadNum_ok 6 hw₁ (o := p384.sl CX) (p := .a1) (off := 1) (by decide)
    (by decide) (by decide) (by decide) (fun j hj => by rw [a1]; exact in_rd8 rdp (by omega))
    (fun i hi => by rw [a1]; exact out_of_disj hpw hfp (by omega))) fun s₂ ⟨r₂, O₂, e₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  have a1₂ : s₂.gpr .a1 = s.gpr .a1 := by rw [r₂.gpr _ (by decide), a1]
  have in₂ : InRegions (s₂.rd ++ s₂.wr) (s.gpr .a1) 1 := by
    rw [r₂.rd, r₂.wr]
    have := Offset.contains_base (s.gpr .a1) (d := 0) (n := 1) (k := 49) (by decide) (by decide)
    exact ⟨_, rdp, by simpa using this⟩
  -- The first byte's low bit.
  rw [Cfg.parCode, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_lbu (off := 0) (by decide) (by rw [a1₂, BitVec.add_zero]) in₂ fun s₃ u₃ => ?_
  refine WP.cons (exec_logicImm (by decide)) ?_
  have u₃a := Upd.write s₃ .t0 (s₃.gpr .t0 &&& BitVec.ofInt 64 1)
  have hw₃ := (hw₂.of_kp (Kp.of_upd u₃)).of_kp (Kp.of_upd u₃a)
  refine sdAt_ws hw₃ (by decide) (d := p384.sl PAR) (by decide) (by decide) fun s₄ u₄ => ?_
  have hw₄ := hw₃.of_kp (Kp.of_mupd u₄)
  have par₄ : word s₄.mem base (p384.sl PAR) = (s₂.mem (s.gpr .a1)).setWidth 64 &&& BitVec.ofInt 64 1 := by
    rw [u₄.mem, word_writeW_self, u₃a.gpr, u₃.gpr]
  have O₄ : Outside base (p384.sl PAR) 8 s₂.mem s₄.mem := by
    rw [u₄.mem, u₃a.mem, u₃.mem]; exact writeW_outside _ _ _ (by decide)
  have a1₄ : s₄.gpr .a1 = s.gpr .a1 := by
    rw [u₄.gpr, u₃a.other _ (by decide), u₃.other _ (by decide), a1₂]
  -- The tag's mask.
  refine WP.block_append (WP.mono (tagMask_ok (s := s₄) (q := .a1) (by
      rw [a1₄, u₄.rd, u₄.wr, u₃a.rd, u₃a.wr, u₃.rd, u₃.wr]; exact in₂))
    fun s₅ ⟨r₅, m₅, g₅⟩ => ?_)
  have hw₅ := hw₄.of_rest r₅
  refine sdAt_ws hw₅ (by decide) (d := p384.sl FLAG) (by decide) (by decide) fun s₆ u₆ => ?_
  have hw₆ := hw₅.of_kp (Kp.of_mupd u₆)
  -- The constants and the root's exponent.
  rw [constCode_eq]
  refine WP.block_append (WP.mono (consts_ok _ hw₆ consts_slots consts_nodup) fun s₇ ⟨r₇, U₇, e₇⟩ => ?_)
  have hw₇ := hw₆.of_rest r₇
  refine WP.block_append (WP.mono (setConst_ok 6 hw₇ (o := p384.sl EXPS) (x := (p384.C.p + 1) / 4) (by decide)
    (by decide)) fun s₈ ⟨r₈, O₈, e₈⟩ => ?_)
  have hw₈ := hw₇.of_rest r₈
  -- `x < p`.
  refine WP.block_append (WP.mono (ltMask_ok hw₈ (n := 6) (a := p384.sl CX) (m := p384.sl MP) (by decide)
    (by decide) (by decide) (by decide)) fun s₉ ⟨r₉, m₉, g₉⟩ => ?_)
  have hw₉ := hw₈.of_rest r₉
  refine WP.mono (andFlag_ok hw₉) fun s₁₀ ⟨f₁₀, r₁₀, O₁₀⟩ => ?_
  -- What changed.
  have O₆ : Unch base [(FL, 8)] s₅.mem s₆.mem := by
    rw [u₆.mem]; exact (writeW_outside _ _ _ (by decide)).unch
  have U₈₁₀ : Unch base [(FL, 8)] s₈.mem s₁₀.mem := by rw [← m₉]; exact O₁₀.unch
  have U₆₁₀ := (U₇.trans O₈.unch).trans U₈₁₀
  have U₄₁₀ : Unch base _ s₄.mem s₁₀.mem := (by rw [← m₅]; exact O₆ : Unch base [(FL, 8)] s₄.mem s₆.mem).trans U₆₁₀
  have U₂₁₀ := O₄.unch.trans U₄₁₀
  have U₁₁₀ := O₂.unch.trans U₂₁₀
  have hp1 : ∀ x ∈ preserved, x ∉ [Reg.t0, .t1, .a7] := by decide
  have hp2 : ∀ x ∈ preserved, x ∉ [Reg.t0, .t1] := by decide
  have hp3 : ∀ x ∈ preserved, x ∉ [Reg.t3, .t4, .t5, .t6, .a4, .a7] := by decide
  have hp4 : ∀ x ∈ preserved, x ∉ [Reg.t0] := by decide
  have hp5 : ∀ x ∈ preserved, x ≠ .t0 := by decide
  have gp : ∀ x ∈ preserved, s₁₀.gpr x = s₁.gpr x := fun x hx => by
    rw [r₁₀.gpr _ (hp4 x hx), r₉.gpr _ (hp3 x hx), r₈.gpr _ (hp2 x hx), r₇.gpr _ (hp2 x hx), u₆.gpr,
      r₅.gpr _ (hp1 x hx), u₄.gpr, u₃a.other _ (hp5 x hx), u₃.other _ (hp5 x hx), r₂.gpr _ (hp2 x hx)]
  have b₂ : s₂.mem (s.gpr .a1) = s.mem (s.gpr .a1) := by
    have h1 := bytesAt_unch (U₁.trans O₂.unch) (q := s.gpr .a1) (n := 1) (by decide)
      (by simpa using sep_at' hpw hfp (off := 0) (k := 1) (by omega))
    simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h1
    simp only [BitVec.add_zero] at h1
    exact h1
  have x₂ : sv base s₂ CX = ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 48) := by
    show wordsVal _ _ _ _ = _
    rw [e₂, a1, bytesAt_unch U₁ (by decide) (sep_at' hpw hfp (off := 1) (k := 48) (by omega))]
  have cs₇ : ∀ e ∈ consts p384, sv base s₇ e.1 = e.2 := fun e he => by
    rw [e₇ e he, Nat.mod_eq_of_lt (consts_lt e he)]
  have hap : ∀ e ∈ consts p384, ∀ w ∈ [(p384.sl EXPS, 8 * 6)] ++ [(FL, 8)],
      p384.sl e.1 + 48 ≤ w.1 ∨ w.1 + w.2 ≤ p384.sl e.1 := by decide
  have csl : ∀ e ∈ consts p384, e.1 < 100 := fun e he => by have := consts_slots e he; omega
  subst hb
  refine ⟨hw₉.of_rest r₁₀, by rw [gp _ (by decide), o₁], by rw [gp _ (by decide), h3₁],
    fun x h0 h2 h3 hx => by rw [gp _ hx, g₁ _ h0 h2 h3], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r₁₀.rd, r₉.rd, r₈.rd, r₇.rd, u₆.rd, r₅.rd, u₄.rd, u₃a.rd, u₃.rd, r₂.rd, rd₁]
  · rw [r₁₀.wr, r₉.wr, r₈.wr, r₇.wr, u₆.wr, r₅.wr, u₄.wr, u₃a.wr, u₃.wr, r₂.wr, wr₁]
  · rw [r₁₀.sp, r₉.sp, r₈.sp, r₇.sp, u₆.sp, r₅.sp, u₄.sp, u₃a.sp, u₃.sp, r₂.sp, sp₁]
  · rw [U₁₁₀.word (by decide) (by decide)]; exact w0
  · rw [U₁₁₀.word (by decide) (by decide)]; exact w1
  · rw [U₁₁₀.word (by decide) (by decide)]; exact w2
  · rw [U₁₁₀.word (by decide) (by decide)]; exact w3
  · rw [U₁₁₀.word (by decide) (by decide)]; exact w4
  · show wordsVal _ _ _ _ = _
    rw [sv_unch U₂₁₀ CX (by decide)]; exact x₂
  · rw [U₄₁₀.word (by decide) (by decide), par₄, b₂]
  · have b₄ : s₄.mem (s.gpr .a1) = s.mem (s.gpr .a1) := by
      have h1 := bytesAt_unch ((U₁.trans O₂.unch).trans O₄.unch) (q := s.gpr .a1) (n := 1) (by decide)
        (by simpa using sep_at' hpw hfp (off := 0) (k := 1) (by omega))
      simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h1
      simp only [BitVec.add_zero] at h1
      exact h1
    have mp₈ : wordsVal s₈.mem (s.gpr .a2) (p384.sl MP) 6 = W.p := by
      rw [O₈.wordsVal (by decide) (by decide)]; exact const_at cs₇ 0
    have cx₈ : wordsVal s₈.mem (s.gpr .a2) (p384.sl CX) 6 =
        ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 48) := by
      rw [O₈.wordsVal (by decide) (by decide), sv_unch (O₄.unch.trans ((by rw [← m₅]; exact O₆ :
        Unch _ [(FL, 8)] s₄.mem s₆.mem).trans U₇)) CX (by decide)]; exact x₂
    rw [f₁₀, m₉, O₈.word (by decide) (by decide), U₇.word (by decide) (by decide), u₆.mem, sl_FLAG,
      word_writeW_self, g₅, g₉, a1₄, b₄, mp₈, cx₈, maskOf_and]
  · intro e he
    show wordsVal _ _ _ _ = _
    rw [U₈₁₀.wordsVal (fun w hw => hap e he w (List.mem_append_right _ hw)) (by have := csl e he; rw [sl_eq]; omega),
      O₈.wordsVal (by have := hap e he _ (List.mem_append_left _ (List.mem_singleton_self _)); simpa using this)
        (by have := csl e he; rw [sl_eq]; omega)]
    exact cs₇ e he
  · show wordsVal _ _ _ _ = _
    rw [U₈₁₀.wordsVal (by decide) (by decide), e₈]
    decide

/-! ### `rhs = x³ + a x + b` -/

/-- The slots of `rhs`'s operations after the first. -/
abbrev rhsSlots : List Nat := [p384.sl CXM, p384.sl RHS, p384.sl TT, p384.sl AP, p384.sl BP]

theorem rhsLay : Lay p384.MP' (own 6) (· ∈ rhsSlots) :=
  ⟨by decide, fun x y hx hy => (by decide : ∀ x ∈ rhsSlots, ∀ y ∈ rhsSlots,
      x ≠ y → x + 8 * p384.MP'.n ≤ y ∨ y + 8 * p384.MP'.n ≤ x) x hx y hy, by decide, by decide⟩

theorem rhsShort : Short (· ∈ rhsSlots) := by decide

theorem rhs_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps (Cfg.rhsOps p384).tail e (p384.sl RHS) =
      e (p384.sl CXM) * e (p384.sl CXM) * e (p384.sl CXM) + e (p384.sl AP) * e (p384.sl CXM) + e (p384.sl BP) := by
  simp only [Cfg.rhsOps, List.tail, runOps_cons, runOps_nil, FOp.run, Function.update_apply, sl_eq]
  simp only [RHS, TT, CXM, AP, BP, T0, T1, Nat.reduceMul, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]

/-- `x R` to `CXM` and `rhs` (in Montgomery's form) to `RHS`. -/
theorem rhs_ok {s : State} {base : Addr} (hw : WsReg s base) (hr2 : sv base s R2P = 2 ^ 384 * 2 ^ 384 % W.p)
    (hap : sv base s AP = W.a * 2 ^ 384 % W.p) (hbp : sv base s BP = W.b * 2 ^ 384 % W.p) :
    WP isa (fprog p384Field (Cfg.rhsOps p384)) s fun s' =>
      Kp s s' ∧ Unch base ([(p384.sl CXM, 8 * 6), (own 6, 64 * 6)] ++
        (((Cfg.rhsOps p384).tail.map FOp.out).map (fun w => (w, 8 * 6)) ++ [(own 6, 64 * 6)])) s.mem s'.mem ∧
      sv base s' RHS < W.p ∧
      toM W.p (2 ^ 384) (sv base s' RHS) =
        Fin.ofNat W.p (sv base s CX) * Fin.ofNat W.p (sv base s CX) * Fin.ofNat W.p (sv base s CX) +
          Fin.ofNat W.p W.a * Fin.ofNat W.p (sv base s CX) + Fin.ofNat W.p W.b := by
  have hp0 : 0 < W.p := by decide
  show WP isa (.seq (mulCall p384Field (p384.sl CXM) (p384.sl CX) (p384.sl R2P))
    (fprog p384Field (Cfg.rhsOps p384).tail)) s _
  refine WP.seq (WP.mono (mulCall_ok field_ok hw (o := p384.sl CXM) (a := p384.sl CX) (b := p384.sl R2P)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by show sv base s R2P < _; rw [hr2]; exact Nat.mod_lt _ hp0)) fun s₁ ⟨C₁, lt₁, e₁⟩ => ?_)
  have hw₁ := hw.of_kp C₁.kp
  have U₁ : Unch base [(p384.sl CXM, 8 * 6), (own 6, 64 * 6)] s.mem s₁.mem := C₁.mem
  have xm₁ : sv base s₁ CXM = sv base s CX * 2 ^ 384 % W.p :=
    mont_eq lt₁ (e₁.trans (by show sv base s CX * sv base s R2P % W.p = _; rw [hr2]))
  have ap₁ : sv base s₁ AP = W.a * 2 ^ 384 % W.p := by
    show wordsVal _ _ _ _ = _; rw [sv_unch U₁ AP (by decide)]; exact hap
  have bp₁ : sv base s₁ BP = W.b * 2 ^ 384 % W.p := by
    show wordsVal _ _ _ _ = _; rw [sv_unch U₁ BP (by decide)]; exact hbp
  refine WP.mono (fprog_ok (M := p384.MP') (F := p384Field) field_ok rfl rhsLay rhsShort unit
    (Cfg.rhsOps p384).tail (V := [p384.sl CXM, p384.sl AP, p384.sl BP])
    (E := fun x => toM W.p (2 ^ 384) (wordsVal s₁.mem base x 6)) ⟨hw₁, by decide, fun x hx => ?_, fun _ _ => rfl⟩
    (by decide) (by decide)) fun s' ⟨K, I⟩ => ⟨C₁.kp.trans K.kp, U₁.trans K.mem, I.lt _ (by decide), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact lt₁
    · show sv base s₁ AP < _; rw [ap₁]; exact Nat.mod_lt _ hp0
    · show sv base s₁ BP < _; rw [bp₁]; exact Nat.mod_lt _ hp0
  · have v := I.val (p384.sl RHS) (by decide)
    refine v.trans ((rhs_run (F := Fe W) _).trans ?_)
    show toM W.p (2 ^ 384) (sv base s₁ CXM) * toM W.p (2 ^ 384) (sv base s₁ CXM) *
        toM W.p (2 ^ 384) (sv base s₁ CXM) + toM W.p (2 ^ 384) (sv base s₁ AP) * toM W.p (2 ^ 384) (sv base s₁ CXM) +
        toM W.p (2 ^ 384) (sv base s₁ BP) = _
    rw [xm₁, ap₁, bp₁, toM_mont unit, toM_mont unit, toM_mont unit]

/-! ### The root's checks -/

/-- `y²` and `y² - rhs` (in Montgomery's form), `y` out of it, and `p - y`. -/
theorem root_ok {s : State} {base : Addr} (hw : WsReg s base) (hacc : sv base s ACC < W.p)
    (hrhs : sv base s RHS < W.p) (hone : sv base s ONE = 1) (hzero : sv base s ZERO = 0) :
    WP isa (fprog p384Field (Cfg.rootOps p384)) s fun s' =>
      Kp s s' ∧ Unch base ([(p384.sl YSQ, 8 * 6), (own 6, 64 * 6)] ++ [(p384.sl DIF, 8 * 6), (own 6, 64 * 6)] ++
        [(p384.sl Y1, 8 * 6), (own 6, 64 * 6)] ++ [(p384.sl Y2, 8 * 6), (own 6, 64 * 6)]) s.mem s'.mem ∧
      sv base s' DIF < W.p ∧
      toM W.p (2 ^ 384) (sv base s' DIF) =
        toM W.p (2 ^ 384) (sv base s ACC) * toM W.p (2 ^ 384) (sv base s ACC) - toM W.p (2 ^ 384) (sv base s RHS) ∧
      sv base s' Y1 < W.p ∧ Fin.ofNat W.p (sv base s' Y1) = toM W.p (2 ^ 384) (sv base s ACC) ∧
      sv base s' Y2 = (W.p - sv base s' Y1) % W.p := by
  have hp0 : 0 < W.p := by decide
  show WP isa (.seq (mulCall p384Field (p384.sl YSQ) (p384.sl ACC) (p384.sl ACC)) <|
    .seq (subCall p384Field (p384.sl DIF) (p384.sl YSQ) (p384.sl RHS)) <|
    .seq (mulCall p384Field (p384.sl Y1) (p384.sl ACC) (p384.sl ONE))
      (subCall p384Field (p384.sl Y2) (p384.sl ZERO) (p384.sl Y1))) s _
  refine WP.seq (WP.mono (mulCall_ok field_ok hw (o := p384.sl YSQ) (a := p384.sl ACC) (b := p384.sl ACC)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hacc) fun s₁ ⟨C₁, lt₁, e₁⟩ => ?_)
  have hw₁ := hw.of_kp C₁.kp
  have U₁ : Unch base [(p384.sl YSQ, 8 * 6), (own 6, 64 * 6)] s.mem s₁.mem := C₁.mem
  have e₁' : ∀ i, i ∈ [ACC, RHS, ONE, ZERO] → sv base s₁ i = sv base s i := fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> exact sv_unch U₁ _ (by decide)
  refine WP.seq (WP.mono (subCall_ok field_ok hw₁ (o := p384.sl DIF) (a := p384.sl YSQ) (b := p384.sl RHS)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) lt₁
    (by show sv base s₁ RHS < _; rw [e₁' RHS (by simp)]; exact hrhs)) fun s₂ ⟨C₂, e₂⟩ => ?_)
  have hw₂ := hw₁.of_kp C₂.kp
  have U₂ : Unch base [(p384.sl DIF, 8 * 6), (own 6, 64 * 6)] s₁.mem s₂.mem := C₂.mem
  have e₂' : ∀ i, i ∈ [ACC, ONE, ZERO] → sv base s₂ i = sv base s i := fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> (rw [← e₁' _ (by simp)]; exact sv_unch U₂ _ (by decide))
  refine WP.seq (WP.mono (mulCall_ok field_ok hw₂ (o := p384.sl Y1) (a := p384.sl ACC) (b := p384.sl ONE)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by show sv base s₂ ONE < _; rw [e₂' ONE (by simp), hone]; decide)) fun s₃ ⟨C₃, lt₃, e₃⟩ => ?_)
  have hw₃ := hw₂.of_kp C₃.kp
  have U₃ : Unch base [(p384.sl Y1, 8 * 6), (own 6, 64 * 6)] s₂.mem s₃.mem := C₃.mem
  have z₃ : sv base s₃ ZERO = 0 := by
    show wordsVal _ _ _ _ = _; rw [sv_unch U₃ ZERO (by decide)]; rw [← hzero]; exact e₂' ZERO (by simp)
  refine WP.mono (subCall_ok field_ok hw₃ (o := p384.sl Y2) (a := p384.sl ZERO) (b := p384.sl Y1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by show sv base s₃ ZERO < _; rw [z₃]; exact hp0) lt₃) fun s₄ ⟨C₄, e₄⟩ => ?_
  have U₄ : Unch base [(p384.sl Y2, 8 * 6), (own 6, 64 * 6)] s₃.mem s₄.mem := C₄.mem
  have dif₄ : sv base s₄ DIF = sv base s₂ DIF := by
    show wordsVal _ _ _ _ = _; rw [sv_unch U₄ DIF (by decide)]; exact sv_unch U₃ DIF (by decide)
  have y1₄ : sv base s₄ Y1 = sv base s₃ Y1 := sv_unch U₄ Y1 (by decide)
  have ysq₂ : sv base s₂ YSQ = sv base s₁ YSQ := sv_unch U₂ YSQ (by decide)
  have h2 : sv base s₂ DIF = (sv base s₁ YSQ + W.p - sv base s₁ RHS) % W.p := e₂
  have lt₂ : sv base s₂ DIF < W.p := by rw [h2]; exact Nat.mod_lt _ hp0
  refine ⟨C₁.kp.trans (C₂.kp.trans (C₃.kp.trans C₄.kp)), ((U₁.trans U₂).trans U₃).trans U₄, by rw [dif₄]; exact lt₂,
    ?_, by rw [y1₄]; exact lt₃, ?_, ?_⟩
  · rw [dif₄]
    have hr1 : sv base s₁ RHS < W.p := by rw [e₁' RHS (by simp)]; exact hrhs
    have hm : toM W.p (2 ^ 384) (sv base s₁ YSQ) = toM W.p (2 ^ 384) (sv base s ACC) *
        toM W.p (2 ^ 384) (sv base s ACC) := toM_mul unit e₁
    rw [h2, toM_sub (by omega), hm, e₁' RHS (by simp)]
  · rw [y1₄]
    refine toM_one_mul unit ?_
    have h := e₃
    rw [show wordsVal s₂.mem base (p384.sl ONE) p384Field.S.k = 1 from (e₂' ONE (by simp)).trans hone,
      show wordsVal s₂.mem base (p384.sl ACC) p384Field.S.k = sv base s ACC from e₂' ACC (by simp)] at h
    exact h
  · have h4 : sv base s₄ Y2 = (sv base s₃ ZERO + W.p - sv base s₃ Y1) % W.p := e₄
    rw [h4, z₃, Nat.zero_add, y1₄]

/-! ### The checks into the flag, the root's choice and the output -/

theorem mask_maskOf (P : Prop) [Decidable P] : VG.Proof.Weierstrass.mask P = maskOf (decide P) := by
  unfold VG.Proof.Weierstrass.mask maskOf; by_cases h : P <;> simp [h]

theorem same_mask (x y : BitVec 64) :
    ((x ^^^ y) &&& BitVec.ofInt 64 1) + BitVec.ofInt 64 (-1) = maskOf (decide (x.toNat % 2 = y.toNat % 2)) := by
  have hlow : (x ^^^ y) &&& 1 = if x.toNat % 2 = y.toNat % 2 then 0 else 1 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_xor, show (1 : BitVec 64).toNat = 1 from rfl,
      Nat.and_one_is_mod, show 2 = 2 ^ 1 from rfl, Nat.xor_mod_two_pow]
    rcases Nat.mod_two_eq_zero_or_one x.toNat with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one y.toNat with hy | hy <;> simp [hx, hy]
  rw [show BitVec.ofInt 64 1 = 1 from rfl, hlow]
  by_cases h : x.toNat % 2 = y.toNat % 2 <;> simp [h, maskOf] <;> decide

/-- `parMask a`: `a7` is the mask of the low bits of `[a]` and `PAR` differing. -/
theorem parMask_ok {s : State} {base : Addr} (hw : WsReg s base) {a : Nat} (ha : a < 41) :
    WP isa (.block (Cfg.parMask p384 a)) s fun s' =>
      Rest [.t0, .t1, .a7] s s' ∧ s'.mem = s.mem ∧
      s'.gpr .a7 = maskOf (decide ((word s.mem base (p384.sl a)).toNat % 2 ≠
        (word s.mem base (p384.sl PAR)).toNat % 2)) := by
  have sl8 : p384.sl a % 8 = 0 := by rw [sl_eq]; omega
  have sl2 : p384.sl a < 2048 := by rw [sl_eq]; omega
  rw [Cfg.parMask]
  refine ld_ws hw sl2 sl8 fun s₁ u₁ => ?_
  refine ld_ws (hw.of_kp (Kp.of_upd u₁)) (d := p384.sl PAR) (by decide) (by decide) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine WP.cons (exec_logicImm (by decide)) ?_
  have u₃a := Upd.write s₃ .t0 (s₃.gpr .t0 &&& BitVec.ofInt 64 1)
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
theorem sameMask_ok {s : State} {base : Addr} (hw : WsReg s base) {a : Nat} (ha : a < 41) :
    WP isa (.block (Cfg.sameMask p384 a)) s fun s' =>
      Rest [.t0, .t1, .a7] s s' ∧ s'.mem = s.mem ∧
      s'.gpr .a7 = maskOf (decide ((word s.mem base (p384.sl a)).toNat % 2 =
        (word s.mem base (p384.sl PAR)).toNat % 2)) := by
  have sl8 : p384.sl a % 8 = 0 := by rw [sl_eq]; omega
  have sl2 : p384.sl a < 2048 := by rw [sl_eq]; omega
  rw [Cfg.sameMask]
  refine ld_ws hw sl2 sl8 fun s₁ u₁ => ?_
  refine ld_ws (hw.of_kp (Kp.of_upd u₁)) (d := p384.sl PAR) (by decide) (by decide) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine WP.cons (exec_logicImm (by decide)) ?_
  have u₃a := Upd.write s₃ .t0 (s₃.gpr .t0 &&& BitVec.ofInt 64 1)
  refine WP.cons (exec_addi (by decide)) ?_
  have u₄ := Upd.write (s₃.write .t0 (s₃.gpr .t0 &&& BitVec.ofInt 64 1)) .a7
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
    (hfit : out.toNat + 97 ≤ 2 ^ 64)
    (hout : ∀ i < 97, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hdis : (⟨out, 97⟩ : Region).Disjoint ⟨base, 8192⟩)
    {c : Bool} (hF : word s.mem base FL = maskOf c) {pr : Nat}
    (hpr : (word s.mem base (p384.sl PAR)).toNat % 2 = pr) :
    WP isa (.block (zeroMask p384.n (p384.sl DIF) ++ andFlag p384 ++ Cfg.parMask p384 Y1 ++
      sel p384.n (p384.sl YF) (p384.sl Y1) (p384.sl Y2) ++ Cfg.sameMask p384 YF ++ andFlag p384 ++
      ldAt .a7 wb (p384.sl FLAG) ++ pointOut p384 CX YF)) s fun s' =>
      s'.gpr .a0 = (if (c && decide (sv base s DIF = 0)) &&
          decide ((if sv base s Y1 % 2 ≠ pr then sv base s Y2 else sv base s Y1) % 2 = pr) then 1 else 0) ∧
      bytesAt s'.mem out 97 = (if (c && decide (sv base s DIF = 0)) &&
          decide ((if sv base s Y1 % 2 ≠ pr then sv base s Y2 else sv base s Y1) % 2 = pr) then 4 else 0) ::
        (toBytes 48 (if (c && decide (sv base s DIF = 0)) &&
          decide ((if sv base s Y1 % 2 ≠ pr then sv base s Y2 else sv base s Y1) % 2 = pr) then sv base s CX else 0) ++
        toBytes 48 (if (c && decide (sv base s DIF = 0)) &&
          decide ((if sv base s Y1 % 2 ≠ pr then sv base s Y2 else sv base s Y1) % 2 = pr) then
            (if sv base s Y1 % 2 ≠ pr then sv base s Y2 else sv base s Y1) else 0)) ∧
      s'.gpr .s0 = word s.mem base 0 ∧ s'.gpr .s1 = word s.mem base 8 ∧ s'.gpr .s2 = word s.mem base 16 ∧
      s'.gpr .ra = word s.mem base 24 ∧ s'.gpr .s3 = word s.mem base 32 ∧
      (∀ r ∈ preserved, r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp := by
  rw [show p384.n = 6 from rfl]
  simp only [List.append_assoc]
  -- `y² = rhs`.
  refine WP.block_append (WP.mono (zeroMask_ok hw (n := 6) (a := p384.sl DIF) (by decide) (by decide))
    fun s₁ ⟨r₁, m₁, g₁⟩ => ?_)
  have hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono (andFlag_ok hw₁) fun s₂ ⟨f₂, r₂, O₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  have w₂ : ∀ i, i < 44 → i ≠ FLAG → wordsVal s₂.mem base (p384.sl i) 6 = sv base s i := fun i hi hf => by
    rw [O₂.wordsVal (by rw [sl_eq, FL]; omega) (by rw [sl_eq]; omega), m₁]
  have wd₂ : ∀ i, i < 44 → i ≠ FLAG → word s₂.mem base (p384.sl i) = word s.mem base (p384.sl i) := fun i hi hf => by
    rw [O₂.word (by rw [sl_eq, FL]; omega) (by rw [sl_eq]; omega), m₁]
  -- The root of the first byte's parity.
  refine WP.block_append (WP.mono (parMask_ok hw₂ (a := Y1) (by decide)) fun s₃ ⟨r₃, m₃, g₃⟩ => ?_)
  have hw₃ := hw₂.of_rest r₃
  have par₂ : (word s₂.mem base (p384.sl PAR)).toNat % 2 = pr := by rw [wd₂ PAR (by decide) (by decide), hpr]
  have y1₂ : (word s₂.mem base (p384.sl Y1)).toNat % 2 = sv base s Y1 % 2 := by
    rw [VG.Proof.EcKey.Compressed.slot_parity s₂.mem base (p384.sl Y1) 6 (by decide)]
    exact congrArg (· % 2) (w₂ Y1 (by decide) (by decide))
  rw [par₂, y1₂] at g₃
  refine WP.block_append (WP.mono (sel_ok (decide (sv base s Y1 % 2 ≠ pr)) 6 hw₃ g₃ (o := p384.sl YF)
    (a := p384.sl Y1) (b := p384.sl Y2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₄ ⟨v₄, r₄, O₄⟩ => ?_)
  have hw₄ := hw₃.of_rest r₄
  have yf₄ : wordsVal s₄.mem base (p384.sl YF) 6 =
      if sv base s Y1 % 2 ≠ pr then sv base s Y2 else sv base s Y1 := by
    rw [v₄, m₃, w₂ Y1 (by decide) (by decide), w₂ Y2 (by decide) (by decide)]
    by_cases h : sv base s Y1 % 2 ≠ pr <;> simp [h]
  generalize hy : (if sv base s Y1 % 2 ≠ pr then sv base s Y2 else sv base s Y1) = y at yf₄
  refine WP.block_append (WP.mono (sameMask_ok hw₄ (a := YF) (by decide)) fun s₅ ⟨r₅, m₅, g₅⟩ => ?_)
  have hw₅ := hw₄.of_rest r₅
  have par₄ : (word s₄.mem base (p384.sl PAR)).toNat % 2 = pr := by
    rw [O₄.word (by decide) (by decide), m₃, par₂]
  have yf₄' : (word s₄.mem base (p384.sl YF)).toNat % 2 = y % 2 := by
    rw [VG.Proof.EcKey.Compressed.slot_parity s₄.mem base (p384.sl YF) 6 (by decide), yf₄]
  rw [par₄, yf₄'] at g₅
  refine WP.block_append (WP.mono (andFlag_ok hw₅) fun s₆ ⟨f₆, r₆, O₆⟩ => ?_)
  have hw₆ := hw₅.of_rest r₆
  refine ldAt_ws hw₆ (d := p384.sl FLAG) (by decide) (by decide) fun s₇ u₇ => ?_
  have hw₇ := hw₆.of_kp (Kp.of_upd u₇)
  generalize hB : ((c && decide (sv base s DIF = 0)) && decide (y % 2 = pr)) = B
  have fl₆ : word s₆.mem base FL = maskOf B := by
    rw [f₆, m₅, O₄.word (by decide) (by decide), m₃, f₂, g₁, g₅, m₁, hF, maskOf_and, maskOf_and, ← hB]
  have a₇ : s₇.gpr .a7 = maskOf B := by rw [u₇.gpr, sl_FLAG, fl₆]
  have q₇ : s₇.gpr .s2 = out := by
    rw [u₇.other _ (by decide), r₆.gpr _ (by decide), r₅.gpr _ (by decide), r₄.gpr _ (by decide),
      r₃.gpr _ (by decide), r₂.gpr _ (by decide), r₁.gpr _ (by decide), h2]
  have wr₇ : s₇.wr = s.wr := by rw [u₇.wr, r₆.wr, r₅.wr, r₄.wr, r₃.wr, r₂.wr, r₁.wr]
  refine WP.mono (pointOut_ok hw₇ q₇ hfit (by rw [wr₇]; exact hout) hdis a₇ (by rw [u₇.mem]; exact fl₆)
    (xo := CX) (yo := YF) (by decide) (by decide) (by decide) (by decide))
    fun s' ⟨a0', b', s0', s1', s2', ra', s3', regs', sp'⟩ => ?_
  have m₇₄ : s₇.mem = s₆.mem := u₇.mem
  have w₇ : ∀ d, d + 8 ≤ 40 → word s₇.mem base d = word s.mem base d := fun d hd => by
    rw [m₇₄, O₆.word (by rw [FL]; omega) (by omega), m₅, O₄.word (by rw [sl_eq]; omega) (by omega), m₃,
      O₂.word (by rw [FL]; omega) (by omega), m₁]
  have cx₇ : sv base s₇ CX = sv base s CX := by
    show wordsVal _ _ _ _ = _
    rw [m₇₄, O₆.wordsVal (by decide) (by decide), m₅, O₄.wordsVal (by decide) (by decide), m₃,
      w₂ CX (by decide) (by decide)]
  have yf₇ : sv base s₇ YF = y := by
    show wordsVal _ _ _ _ = _
    rw [m₇₄, O₆.wordsVal (by decide) (by decide), m₅, yf₄]
  refine ⟨a0', by rw [b', cx₇, yf₇], by rw [s0', w₇ 0 (by decide)], by rw [s1', w₇ 8 (by decide)],
    by rw [s2', w₇ 16 (by decide)], by rw [ra', w₇ 24 (by decide)], by rw [s3', w₇ 32 (by decide)],
    fun r hr h0 h1 h2' h3' => ?_, by rw [sp', u₇.sp, r₆.sp, r₅.sp, r₄.sp, r₃.sp, r₂.sp, r₁.sp]⟩
  have hn : r ∉ [Reg.t0, .t1, .t3, .t4, .a7] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> exact absurd hr (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  rw [regs' r hr h0 h1 h2' h3', u₇.other _ hn.2.2.2.2, r₆.gpr _ (by simp [hn.1]),
    r₅.gpr _ (by simp [hn.1, hn.2.1, hn.2.2.2.2]), r₄.gpr _ (by simp [hn.1, hn.2.1]),
    r₃.gpr _ (by simp [hn.1, hn.2.1, hn.2.2.2.2]), r₂.gpr _ (by simp [hn.1]),
    r₁.gpr _ (by simp [hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2])]

/-! ### The whole decompression -/

theorem sqrtLay : PowLayR (Cfg.sqrtP p384) 6 where
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

theorem par_bit (b : BitVec 8) : (b.setWidth 64 &&& BitVec.ofInt 64 1).toNat % 2 = b.toNat % 2 := by
  revert b; decide

theorem neg_ofNat {v : Nat} (hv : v < W.p) : Fin.ofNat W.p ((W.p - v) % W.p) = -Fin.ofNat W.p v := by
  apply Fin.ext
  rw [Fin.val_ofNat, Fin.neg_def, Fin.val_ofNat, Nat.mod_eq_of_lt hv, Nat.mod_mod]

/-- `vg_ec_p384_decompress_public_key`'s postcondition, by register. -/
def DPostC (s s' : State) : Prop :=
  let bs := bytesAt s.mem (s.gpr .a1) 49
  (s'.gpr .a0 = 1 ∧ ∃ Q, Spec.EcKey.matchesCompressedPublicKey Spec.P384.curve bs Q ∧
      bytesAt s'.mem (s.gpr .a0) 97 = Spec.EcKey.encodePoint Q) ∨
    (s'.gpr .a0 = 0 ∧ (¬ ∃ Q, Spec.EcKey.matchesCompressedPublicKey Spec.P384.curve bs Q) ∧
      bytesAt s'.mem (s.gpr .a0) 97 = List.replicate 97 0)

/-- `vg_ec_p384_decompress_public_key` by register. -/
theorem decompress_ok (hL : VG.Proof.Weierstrass.Law W) {s : State} (hs : DPre s) :
    WP isa decompressP384 s fun s' => abiPreserved s s' ∧ DPostC s s' := by
  have hp0 : 0 < W.p := by decide
  have hs' := hs
  obtain ⟨hrd, hwr, hpo, hpw, how, hfo, hfp, hfs, hal⟩ := hs'
  rw [decompressP384, Cfg.decompressFn]
  refine WP.seq (WP.mono (dsetup_ok hs) fun s₁ S => ?_)
  obtain ⟨hw₁, S2, S3, Sregs, Srd, Swr, Ssp, Ssv0, Ssv1, Ssv2, Ssv3, Ssv4, Sx, Spar, Sflag, Scs, Sexps⟩ := S
  generalize hb : s.gpr .a2 = base at hw₁ S3 Ssv0 Ssv1 Ssv2 Ssv3 Ssv4 Sx Spar Sflag Scs Sexps hwr hpw how
  -- `rhs`.
  refine WP.seq (WP.mono (rhs_ok hw₁ (const_at Scs 10) (const_at Scs 5) (const_at Scs 11))
    fun s₂ ⟨K₂, U₂, lt₂, v₂⟩ => ?_)
  have hw₂ := hw₁.of_kp K₂
  have one₂ : sv base s₂ ONEP = 2 ^ 384 % W.p := by
    show wordsVal _ _ _ _ = _; rw [sv_unch U₂ ONEP (by decide)]
    exact const_at Scs 4
  have exps₂ : sv base s₂ EXPS = (W.p + 1) / 4 := by
    show wordsVal _ _ _ _ = _; rw [sv_unch U₂ EXPS (by decide)]; exact Sexps
  -- The root.
  refine WP.seq (WP.mono (pow_ok (P := Cfg.sqrtP p384) (F := p384Field) field_ok rfl sqrtLay unit hw₂ hp0
    one₂ (by show sv base s₂ EXPS < _; rw [exps₂]; decide)) fun s₃ ⟨Kc₃, U₃, lt₃, v₃⟩ => ?_)
  have hw₃ := hw₂.of_kc Kc₃
  have rhs₃ : sv base s₃ RHS = sv base s₂ RHS := sv_unch U₃ RHS (by decide)
  have one₃ : sv base s₃ ONE = 1 := by
    show wordsVal _ _ _ _ = _
    rw [sv_unch U₃ ONE (by decide), sv_unch U₂ ONE (by decide)]; exact const_at Scs 3
  have zero₃ : sv base s₃ ZERO = 0 := by
    show wordsVal _ _ _ _ = _
    rw [sv_unch U₃ ZERO (by decide), sv_unch U₂ ZERO (by decide)]; exact const_at Scs 2
  -- The root's checks.
  refine WP.seq (WP.mono (root_ok hw₃ lt₃ (by rw [rhs₃]; exact lt₂) one₃ zero₃)
    fun s₄ ⟨K₄, U₄, ltd₄, vd₄, lty₄, vy₄, y2₄⟩ => ?_)
  have hw₄ := hw₃.of_kp K₄
  have U₁₄ := (U₂.trans U₃).trans U₄
  have hF : word s₄.mem base FL = maskOf (decide (s.mem (s.gpr .a1) = 2 ∨ s.mem (s.gpr .a1) = 3) &&
      decide (ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 48) < W.p)) := by
    rw [U₁₄.word (by decide) (by decide)]; exact Sflag
  have hpr : (word s₄.mem base (p384.sl PAR)).toNat % 2 = (s.mem (s.gpr .a1)).toNat % 2 := by
    rw [U₁₄.word (by decide) (by decide), Spar, par_bit]
  have cx₄ : sv base s₄ CX = ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 48) := by
    show wordsVal _ _ _ _ = _; rw [sv_unch U₁₄ CX (by decide)]; exact Sx
  have h2₄ : s₄.gpr .s2 = s.gpr .a0 := by
    rw [K₄.gpr _ (by decide), Kc₃.gpr _ (by decide) (by decide), K₂.gpr _ (by decide), S2]
  have wr₄ : s₄.wr = s.wr := by rw [K₄.wr, Kc₃.wr, K₂.wr, Swr]
  refine WP.mono (dfin_ok hw₄ h2₄ hfo (fun i hi => by
      rw [wr₄, hwr]
      exact ⟨_, List.mem_cons_self .., Offset.contains_base (s.gpr .a0) (d := i) (n := 1) (k := 97) (by omega)
        (by omega)⟩) how hF hpr)
    fun s' ⟨a0', b', s0', s1', s2', ra', s3', regs', sp'⟩ => ?_
  -- The registers.
  refine ⟨⟨fun r hr => ?_, by rw [sp', K₄.sp, Kc₃.sp, K₂.sp, Ssp],
    by rw [ra', U₁₄.word (by decide) (by decide), Ssv3]⟩, ?_⟩
  · by_cases h0 : r = .s0
    · subst h0; rw [s0', U₁₄.word (by decide) (by decide), Ssv0]
    by_cases h1 : r = .s1
    · subst h1; rw [s1', U₁₄.word (by decide) (by decide), Ssv1]
    by_cases h2' : r = .s2
    · subst h2'; rw [s2', U₁₄.word (by decide) (by decide), Ssv2]
    by_cases h3' : r = .s3
    · subst h3'; rw [s3', U₁₄.word (by decide) (by decide), Ssv4]
    rw [regs' r hr h0 h1 h2' h3', K₄.gpr r hr, Kc₃.gpr r hr h1, K₂.gpr r hr, Sregs r h0 h2' h3' hr]
  -- The values.
  have x₁ : sv base s₁ CX = ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 48) := Sx
  rw [cx₄] at b'
  generalize hx : ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 48) = x at x₁ a0' b' hF
  generalize htag : s.mem (s.gpr .a1) = tag at a0' b' hF hpr
  rw [x₁] at v₂
  have v₃' : toM W.p (2 ^ 384) (sv base s₃ ACC) = toM W.p (2 ^ 384) (sv base s₂ RHS) ^ ((W.p + 1) / 4) := by
    have := v₃; rw [show wordsVal s₂.mem base (Cfg.sqrtP p384).bits p384Field.S.k = (W.p + 1) / 4 from exps₂] at this
    exact this
  rw [rhs₃] at vd₄
  generalize hxf : (Fin.ofNat W.p x : Fe W) = xf at v₂
  generalize hrhs : xf * xf * xf + Fin.ofNat W.p W.a * xf + Fin.ofNat W.p W.b = rhsF at v₂
  rw [v₂] at v₃' vd₄
  rw [v₃'] at vy₄ vd₄
  generalize hr : rhsF ^ ((W.p + 1) / 4) = r at vy₄ vd₄
  have hy1 : r.val = sv base s₄ Y1 := by rw [← vy₄, Fin.val_ofNat, Nat.mod_eq_of_lt lty₄]
  generalize hyN : (if sv base s₄ Y1 % 2 ≠ tag.toNat % 2 then sv base s₄ Y2 else sv base s₄ Y1) = yN at a0' b'
  have hyNlt : yN < W.p := by
    rw [← hyN]; split
    · rw [y2₄]; exact Nat.mod_lt _ hp0
    · exact lty₄
  have hch : VG.Impl.EcKey.Compressed.chooseRoot r (tag.toNat % 2) = Fin.ofNat W.p yN := by
    unfold VG.Impl.EcKey.Compressed.chooseRoot
    rw [hy1, ← hyN]
    by_cases h : sv base s₄ Y1 % 2 = tag.toNat % 2
    · rw [ite_eq_left h, ite_eq_right (fun h' => h' h), vy₄]
    · rw [ite_eq_right h, ite_eq_left h, y2₄, neg_ofNat lty₄, vy₄]
  have hval : (Fin.ofNat W.p yN : Fe W).val = yN := by rw [Fin.val_ofNat, Nat.mod_eq_of_lt hyNlt]
  have hsq : VG.Impl.EcKey.Compressed.chooseRoot r (tag.toNat % 2) * VG.Impl.EcKey.Compressed.chooseRoot r (tag.toNat % 2) =
      r * r := by
    unfold VG.Impl.EcKey.Compressed.chooseRoot; split
    · rfl
    · grind
  have hdif : sv base s₄ DIF = 0 ↔ r * r = rhsF := by
    rw [← toM_eq_zero_iff unit ltd₄, vd₄]
    constructor <;> intro h <;> grind
  -- The specification's decoding.
  have hsplit : bytesAt s.mem (s.gpr .a1) 49 = tag :: bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 48 := by
    have h1 : bytesAt s.mem (s.gpr .a1) 1 = [tag] := by
      simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero, htag]
    rw [show (49 : Nat) = 1 + 48 from rfl, VG.Proof.Weierstrass.bytesAt_add, h1]; rfl
  have hlen : (bytesAt s.mem (s.gpr .a1) 49).length = W.len + 1 := VG.Proof.Weierstrass.length_bytesAt _ _ _
  have hhd : (bytesAt s.mem (s.gpr .a1) 49).head? = some tag := by rw [hsplit]; rfl
  have hxv : ofBytes ((bytesAt s.mem (s.gpr .a1) 49).drop 1) = x := by
    rw [hsplit, List.drop_one, List.tail_cons]; exact hx
  have hdec := VG.Proof.EcKey.Compressed.decode_checked_eq (C := W) VG.Impl.EcKey.Compressed.rootThreeModFour hlen
    hhd hxv
  simp only [] at hdec
  rw [hxf, hrhs, VG.Impl.EcKey.Compressed.rootThreeModFour, VG.Proof.Weierstrass.pow_eq_npow, hr, hch] at hdec
  rw [hch] at hsq
  rw [hval] at hdec
  generalize hB : (((decide (tag = 2 ∨ tag = 3) && decide (x < W.p)) && decide (sv base s₄ DIF = 0)) &&
    decide (yN % 2 = tag.toNat % 2)) = B at a0' b'
  have key : B = true ↔ ((tag = 2 ∨ tag = 3) ∧ x < W.p) ∧
      (Fin.ofNat W.p yN * Fin.ofNat W.p yN = rhsF ∧ yN % 2 = tag.toNat % 2) := by
    rw [← hB, hsq, ← hdif]
    simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  have hroot := VG.Proof.Weierstrass.rootFacts_three_mod_four hL (by decide)
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
    show _ = 4 :: (toBytes 48 xf.val ++ toBytes 48 (Fin.ofNat W.p yN : Fe W).val)
    rw [hval, ← hxf, Fin.val_ofNat, Nat.mod_eq_of_lt hc.1.2]
    rfl

end VG.Proof.EcKey.Compressed.RISCV64.P384
