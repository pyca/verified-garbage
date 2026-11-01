module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.Exchange
public import VerifiedGarbage.Impl.EcKey.Compressed.P256.RISCV64
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
import VerifiedGarbage.Proof.EcKey.Compressed.Encode
import VerifiedGarbage.Proof.EcKey.Compressed.Parity
import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.CheckVerified
import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.CheckLit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Weierstrass.Words

/-!
# P-256's point compression and decompression on RISC-V: correctness

`vg_ec_p256_compress_public_key` meets its contract by register (`compRV`,
`compress_ok`): ECDH's saves and its reading of the point, the flag and the
constants (`peerLoad_ok`), the check of the point (`check_ok`), and
`02 + (y mod 2)` and `x` (or zeros) under the flag; the specification's
encoding is `compress_eq`'s (`Proof/EcKey/Compressed/Encode.lean`).
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.RISCV64.P256

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg VG.Impl.EcKey.Compressed.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.P256
open VG.Proof.Ecdh.RISCV64.P256
open VG.Proof.X25519.RISCV64 (Rest wp_and)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_nil writeBytes_append)

/-- `vg_ec_p256_compress_public_key(out = a0, public = a1, scratch = a2)`, by
register. -/
def compRV : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 33⟩
    let pk : Region := ⟨s.gpr .a1, 65⟩
    let ws : Region := ⟨s.gpr .a2, 8192⟩
    s.rd = [pk] ∧ s.wr = [out, ws] ∧ pk.Disjoint out ∧ pk.Disjoint ws ∧ out.Disjoint ws ∧
      (s.gpr .a0).toNat + 33 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 65 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8192 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat % 8 = 0
  post s s' :=
    match Spec.EcKey.compressPublicKey Spec.P256.curve (bytesAt s.mem (s.gpr .a1) 65) with
    | some bs => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) 33 = bs
    | none => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) 33 = List.replicate 33 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2

theorem tag_eq (m : Mem) (base : Addr) (B : Bool) :
    ((((word m base (p256.sl CY) &&& BitVec.ofInt 64 1) + BitVec.ofInt 64 2) &&& maskOf B).setWidth 8) =
      if B then BitVec.ofNat 8 (2 + wordsVal m base (p256.sl CY) 4 % 2) else 0 :=
  VG.Proof.EcKey.Compressed.tag_byte m base (p256.sl CY) 4 (by decide) B

/-- `vg_ec_p256_compress_public_key` by register. -/
theorem compress_ok {s : State} (hs : compRV.pre s) :
    WP isa compressP256 s fun s' => abiPreserved s s' ∧ compRV.post s s' := by
  obtain ⟨hrd, hwr, hpo, hpw, how, hfo, hfp, hfs, hal⟩ := hs
  rw [compressP256, Cfg.compressFn]
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
  have hdis : (⟨out, 33⟩ : Region).Disjoint ⟨base, 8192⟩ := how
  -- The values.
  have x₁ : sv base s₂ CX = ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 1) 32) := by
    rw [x₂, a1, bytesAt_unch U₁ (by decide) (sep_at' hpw hfp (off := 1) (k := 32) (by omega))]
  have y₁ : sv base s₂ CY = ofBytes (bytesAt s.mem (s.gpr .a1 + BitVec.ofNat 64 33) 32) := by
    rw [y₂, a1, bytesAt_unch U₁ (by decide) (sep_at' hpw hfp (off := 33) (k := 32) (by omega))]
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
  have cy₃ : wordsVal s₃.mem base (p256.sl CY) 4 = y := by
    rw [U₃.wordsVal (by decide) (by decide)]; exact hy
  have cx₃ : wordsVal s₃.mem base (p256.sl CX) 4 = x := by
    rw [U₃.wordsVal (by decide) (by decide)]; exact hx
  -- The first byte.
  rw [show p256.n = 4 from rfl, retCode, restoreCode]
  simp only [List.cons_append, List.nil_append]
  refine ld_ws hw₃ (d := p256.sl FLAG) (by decide) (by decide) fun s₄ u₄ => ?_
  have hw₄ := hw₃.of_kp (Kp.of_upd u₄)
  refine ld_ws hw₄ (d := p256.sl CY) (by decide) (by decide) fun s₅ u₅ => ?_
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
  have hout' : ∀ i < 33, InRegions s.wr (out + BitVec.ofNat 64 i) 1 := fun i hi => by
    rw [hwr]
    exact ⟨_, List.mem_cons_self .., Offset.contains_base out (d := i) (n := 1) (k := 33) (by omega) (by omega)⟩
  refine wp_sb (off := 0) (a := out) (by decide) (by rw [q₆, BitVec.add_zero])
    (by rw [wr₆]; simpa using hout' 0 (by decide)) fun s₇ u₇ => ?_
  have hw₇ := hw₆.of_kp (Kp.of_mupd u₇)
  have m₇ : s₇.mem = writeBytes s₃.mem out [if B then BitVec.ofNat 8 (2 + y % 2) else 0] := by
    rw [u₇.mem, v₆, u₆.mem, u₅b.mem, u₅a.mem, u₅.mem, u₄.mem]
    have := writeBytes_snoc s₃.mem out [] (if B then BitVec.ofNat 8 (2 + y % 2) else 0) (by decide)
    rw [List.nil_append, writeBytes_nil] at this
    rw [this]; simp
  have sp' : ∀ {off k : Nat}, off + k ≤ 33 → ∀ i < k,
      ¬ (⟨base, 8192⟩ : Region).Contains (out + BitVec.ofNat 64 off + BitVec.ofNat 64 i) 1 :=
    fun hk => sep_at' hdis hfo hk
  have U₇ : Unch base [(8192, 2 ^ 64)] s₃.mem s₇.mem := by
    rw [m₇]; exact writeBytes_unch _ fun i hi => by
      have := sp' (off := 0) (k := 1) (by decide) i (by simpa using hi); simpa using this
  have q₇ : s₇.gpr .s2 = out := by rw [u₇.gpr, q₆]
  have a₇ : s₇.gpr .a7 = maskOf B := by rw [u₇.gpr, a₆]
  -- `x`.
  refine WP.block_append (WP.mono (storeNum_ok _ 4 hw₇ a₇ (q := .s2) (a := p256.sl CX) (off := 1) (by decide)
    (by decide) (by decide) (by decide)
    (fun i hi => by rw [q₇, u₇.wr, wr₆]; exact hout' (1 + i) (by omega))
    (fun i hi => by rw [q₇]; exact out_of_disj hdis hfo (by omega))) fun s₈ ⟨r₈, m₈⟩ => ?_)
  have hw₈ := hw₇.of_rest r₈
  have xo₇ : wordsVal s₇.mem base (p256.sl CX) 4 = x := by rw [U₇.wordsVal (by decide) (by decide), cx₃]
  rw [q₇, xo₇] at m₈
  have U₈ : Unch base [(8192, 2 ^ 64)] s₇.mem s₈.mem := by
    rw [m₈]; exact writeBytes_unch _ fun i hi => sp' (off := 1) (k := 32) (by decide) i
      (by simpa [VG.Proof.Weierstrass.length_toBytes] using hi)
  have U₃₈ := U₇.trans U₈
  have hX := VG.Proof.Weierstrass.length_toBytes 32 (if B = true then x else 0)
  have bytes₈ : bytesAt s₈.mem out 33 = (if B then BitVec.ofNat 8 (2 + y % 2) else 0) ::
      toBytes 32 (if B then x else 0) := by
    have e1 := writeBytes_append s₃.mem out [if B then BitVec.ofNat 8 (2 + y % 2) else 0]
      (toBytes 32 (if B then x else 0)) (by rw [hX, List.length_singleton]; decide)
    simp only [List.length_singleton] at e1
    rw [m₈, m₇, show (8 * 4 : Nat) = 32 from rfl, e1]
    have := bytesAt_writeBytes s₃.mem out
      ([if B then BitVec.ofNat 8 (2 + y % 2) else 0] ++ toBytes 32 (if B then x else 0))
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
  have bytes' : bytesAt t₅.mem out 33 = (if B then BitVec.ofNat 8 (2 + y % 2) else 0) ::
      toBytes 32 (if B then x else 0) := by rw [v₅.mem, M₄]; exact bytes₈
  have hlen : (bytesAt s.mem (s.gpr .a1) 65).length = 2 * W.len + 1 := VG.Proof.Weierstrass.length_bytesAt _ _ _
  have hpb := peer_bytes s.mem (s.gpr .a1) 32
  have hhd : (bytesAt s.mem (s.gpr .a1) 65).head? = some (s.mem (s.gpr .a1)) := by rw [hpb]; rfl
  have hxv : ofBytes (((bytesAt s.mem (s.gpr .a1) 65).drop 1).take W.len) = x := by
    rw [show W.len = 32 from rfl, hpb, List.drop_one, List.tail_cons,
      List.take_left' (VG.Proof.Weierstrass.length_bytesAt _ _ _)]; exact x₁.symm
  have hyv : ofBytes ((bytesAt s.mem (s.gpr .a1) 65).drop (W.len + 1)) = y := by
    rw [show W.len = 32 from rfl, hpb, List.drop_succ_cons, List.drop_left' (VG.Proof.Weierstrass.length_bytesAt _ _ _)]
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

end VG.Proof.EcKey.Compressed.RISCV64.P256
