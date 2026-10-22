module

import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Aad
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Body
public import VerifiedGarbage.Impl.AesGcm.X86_64.Fast
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Loop
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith

/-!
# AES-GCM `seal_split`'s path for TLS records: at most 16 bytes left

Untrusted: everything here is checked by Lean. `Fast.tail` ends `seal_split`
for the at most 16 bytes left after `prefix` without `oneBlocks`: the total
length put back (`fixTlen_ok`), `H'` and `H'²` loaded from the prepared key
context (`finPowP_ok`, which `ShortFacts.pp1` and `pp2` make multiply as `H`
and `H²`), and `finish`'s end for no whole blocks (`Short.finRest_ok` with
`q = 0`). It leaves what `SealSplit.body` does (`Split.body_ok`): `tail_ok`;
and so does `Fast.run`'s choice between them on the bytes left (`fbody_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Fast

variable {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24}

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64.Split (fixTlen_ok splitFrame BodyOk FinOk body_ok)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts KsOk IsH1 IsH2 finRest_ok)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Proof.Gcm.X86_64.Pclmul (Only const_ok)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks inc32 zeros padLen toBytes ofBytes ctxH)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (Absorbed xorKs lensBlock padded)

/-- `finPowP`: the constants, and the 16 bytes at `ctx + 272` and at
`ctx + 256` in `xmm3` and `xmm6`. -/
theorem finPowP_run {Ctx : Addr} (s : State) (h13 : s.gpr .r13 = Ctx)
    (in1 : InRegions (s.rd ++ s.wr) (Ctx + BitVec.ofNat 64 272) 16)
    (in2 : InRegions (s.rd ++ s.wr) (Ctx + BitVec.ofNat 64 256) 16) :
    WP isa (.block Impl.AesGcm.X86_64.Short.finPowP) s fun t =>
      t.xmm .xmm0 = revMask ∧ t.xmm .xmm1 = poly ∧ t.xmm .xmm3 = s.mem.readW (Ctx + BitVec.ofNat 64 272) 128 ∧
      t.xmm .xmm6 = s.mem.readW (Ctx + BitVec.ofNat 64 256) 128 ∧
      Only [.xmm0, .xmm12, .xmm1, .xmm12, .xmm3, .xmm6] s t := by
  have e : ∀ d : Nat, s.gpr .r13 + BitVec.ofInt 64 (d : Int) = Ctx + BitVec.ofNat 64 d := fun d => by
    rw [h13, BitVec.ofInt_natCast]
  simp only [Impl.AesGcm.X86_64.Short.finPowP, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  have O₂ := o₁.trans o₂
  rw [show ([.movdquLoad .xmm3 (at_ .r13 272), .movdquLoad .xmm6 (at_ .r13 256)] : List Instr) =
      [.movdquLoad .xmm3 (at_ .r13 272)] ++ [.movdquLoad .xmm6 (at_ .r13 256)] from rfl, WP.block_append_iff]
  refine WP.mono (ld_ok .xmm3 .r13 272 s₂ (by rw [O₂.rd, O₂.wr, O₂.gpr _ (by decide), e]; exact in1))
    fun s₃ ⟨l₃, o₃⟩ => ?_
  refine WP.mono (ld_ok .xmm6 .r13 256 s₃ (by
      rw [o₃.rd, o₃.wr, O₂.rd, O₂.wr, o₃.gpr _ (by decide), O₂.gpr _ (by decide), e]; exact in2))
    fun s₄ ⟨l₄, o₄⟩ => ?_
  rw [O₂.gpr _ (by decide), e, O₂.mem] at l₃
  rw [o₃.gpr _ (by decide), O₂.gpr _ (by decide), e, o₃.mem, O₂.mem] at l₄
  exact ⟨by rw [o₄.xmm _ (by decide), o₃.xmm _ (by decide), o₂.xmm _ (by decide), c₁,
      VG.Proof.Gcm.X86_64.Pclmul.rev_eq],
    by rw [o₄.xmm _ (by decide), o₃.xmm _ (by decide), c₂], by rw [o₄.xmm _ (by decide), l₃], l₄,
    O₂.trans (o₃.trans o₄)⟩

/-- `finPowP` from a prepared key context: the constants, and `H'` and `H'²`,
which multiply as `H` and `H²`. -/
theorem finPowP_ok (hF : ShortFacts) {Ctx : Addr} {H : Block} (s : State) (h13 : s.gpr .r13 = Ctx)
    (in1 : InRegions (s.rd ++ s.wr) (Ctx + BitVec.ofNat 64 272) 16)
    (in2 : InRegions (s.rd ++ s.wr) (Ctx + BitVec.ofNat 64 256) 16)
    (p1 : s.mem.readW (Ctx + BitVec.ofNat 64 272) 128 = Spec.Gcm.preparedPower (Spec.Gcm.hpow H 1))
    (p2 : s.mem.readW (Ctx + BitVec.ofNat 64 256) 128 = Spec.Gcm.preparedPower (Spec.Gcm.hpow H 2)) :
    WP isa (.block Impl.AesGcm.X86_64.Short.finPowP) s fun t =>
      t.xmm .xmm0 = revMask ∧ t.xmm .xmm1 = poly ∧ IsH1 H (t.xmm .xmm3) ∧ IsH2 H (t.xmm .xmm3) (t.xmm .xmm6) ∧
      Only [.xmm0, .xmm12, .xmm1, .xmm12, .xmm3, .xmm6] s t :=
  WP.mono (finPowP_run s h13 in1 in2) fun _ ⟨x0, x1, x3, x6, o⟩ =>
    ⟨x0, x1, by rw [x3, p1]; exact hF.pp1 H, by rw [x3, x6, p1, p2]; exact hF.pp2 H, o⟩

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- `tail` for the `n ≤ 16` bytes left: what `SealSplit.body` leaves
(`Split.body_ok`). -/
theorem tail_ok (hF : ShortFacts) {ks : Prog isa} (hks : KsOk ks) {R : Nat} {D : Addr} {n al N : Nat}
    {H icb : Block} {a : List Byte} {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hR : RoundsAt s.mem W R)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n) (h16 : n ≤ 16)
    (hd : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n)
    (kw : (below SP 56).Disjoint ⟨W, 2560⟩) (kd : (below SP 56).Disjoint ⟨D, n⟩)
    (kM : (below SP 56).Disjoint ⟨Ctx, (CtxMode.preparedN np hpn).len⟩) (sp : 56 ≤ SP.toNat)
    (X : CtxExt (CtxMode.preparedN np hpn) Ctx (W + BitVec.ofNat 64 16) W SP D n s)
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) (hcb : blockAt s.mem (cbA W) = icb)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al)
    (habs : Absorbed s.mem (yA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H (a ++ zeros (padLen a.length)))
    (haux : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 N) :
    WP isa (Impl.AesGcm.X86_64.Fast.tail ks) s fun s' =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (splitFrame W D SP n) s.mem s'.mem ∧
      bytesAt s'.mem D n = xorKs (ciphOf s.mem Ctx R) icb 0 (bytesAt s.mem D n) ∧
      bytesAt s'.mem W 16 = toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt s'.mem D n))))
        [ofBytes (lensBlock al N)] ^^^ ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16))) := by
  have hD := hd.ok.w
  have b24 : Region.Sub (below SP 24) (below SP 56) := below_sub (by decide) (by decide)
  have kc : (below SP 56).Disjoint ⟨Ctx, 256⟩ := kM.sub_right (Region.sub_prefix (CtxMode.preparedN np hpn).ge)
  have h : ObPre (CtxMode.preparedN np hpn) Ctx W SP R D n s :=
    ⟨he, hR, hdat, hlen, hd, kc.sub_left b24, kw.sub_left b24, kd.sub_left b24, by omega, X⟩
  -- The total length put back.
  unfold Impl.AesGcm.X86_64.Fast.tail
  refine WP.seq (WP.mono (fixTlen_ok he haux) fun s₁ ⟨m₁, g₁, rd₁, wr₁⟩ => ?_)
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) rd₁ wr₁
  have fW : Frame [⟨W + BitVec.ofNat 64 192, 8⟩] s.mem s₁.mem := by
    rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (Nat.le_refl _) (by decide) (by have := L.ww; omega))
  have one : ∀ {p : Addr} {k : Nat}, (⟨p, k⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 192, 8⟩ →
      ∀ r ∈ [(⟨W + BitVec.ofNat 64 192, 8⟩ : Region)], (⟨p, k⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  have wW : ∀ {d k : Nat}, d + k ≤ 192 ∨ 200 ≤ d → d + k ≤ 2560 →
      (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 192, 8⟩ :=
    fun h₁ h₂ => Offset.disjoint W h₁ (by have := L.ww; omega) (by have := L.ww; omega)
  have rW : ∀ d, d + 8 ≤ 192 ∨ 200 ≤ d → d + 8 ≤ 2560 →
      s₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => fW.readW (Region.contains_self _ _) (one (wW h₁ h₂)) (by decide)
  have f₁ : Frame (oneFrameB W D SP n) s.mem s₁.mem := fW.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨W + BitVec.ofNat 64 192, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  have dC := ctx_oneFrameB L hd.ctx (kc.sub_left b24)
  have hc₁ : ciphOf s₁.mem Ctx R = ciphOf s.mem Ctx R := ciph_frame f₁ dC hR.2
  have stD : (⟨W + BitVec.ofNat 64 16, 80⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 192, 8⟩ :=
    wW (.inl (by decide)) (by decide)
  have bW : ∀ {p : Addr}, Region.Sub ⟨p, 16⟩ ⟨W + BitVec.ofNat 64 16, 80⟩ → blockAt s₁.mem p = blockAt s.mem p :=
    fun hs => blockAt_frame fW (one (stD.sub_left hs))
  have hJ₁ : blockAt s₁.mem (W + BitVec.ofNat 64 16) = blockAt s.mem (W + BitVec.ofNat 64 16) :=
    bW (Region.sub_prefix (by decide))
  have hcb₁ : blockAt s₁.mem (cbA W) = Nat.repeat inc32 0 icb := by
    rw [bW Split.cb_sub]; exact hcb
  have ab₁ : Absorbed s₁.mem (yA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H
      (a ++ zeros (padLen a.length) ++ bytesAt s₁.mem D (16 * 0)) := by
    rw [show bytesAt s₁.mem D (16 * 0) = [] from rfl, List.append_nil]
    have hm := Nat.mod_lt (a ++ zeros (padLen a.length)).length (show 16 > 0 by decide)
    refine ⟨by rw [bW Split.y_sub]; exact habs.1, ?_⟩
    rw [bytesAt_frame fW (one (stD.sub_left
      (Offset.sub_base (W + BitVec.ofNat 64 16) (d := 32) (k := 80) (by omega)))) (by omega)]
    exact habs.2
  have dDW : (⟨D, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 192, 8⟩ := hD.sub_right (Lay.wSub (by decide))
  have ht₁ : bytesAt s₁.mem (D + BitVec.ofNat 64 (16 * 0)) n = bytesAt s.mem (D + BitVec.ofNat 64 (16 * 0)) n := by
    rw [show D + BitVec.ofNat 64 (16 * 0) = D by simp]
    exact bytesAt_frame fW (one dDW) (by have := hd.ok.wrap; omega)
  have hR₁ : RoundsAt s₁.mem W R := ⟨by rw [rW 176 (.inl (by decide)) (by decide)]; exact hR.1, hR.2⟩
  -- `H'` and `H'²`.
  have cov₁ := X.cov
  rw [← rd₁, ← wr₁] at cov₁
  have hX : VG.Proof.Gcm.X86_64.Stitch.PowersN np s₁.mem Ctx :=
    (CtxMode.preparedN np hpn).frame fW (one (X.cw.sub_right (Lay.wSub (by decide)))) X.w X.ok
  have p0 := hX 0 (by have := hpn.1; omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at p0
  have hH₁ : ctxH s₁.mem Ctx = H := by
    rw [ctxH_eq, blockAt_frame fW (one ((X.cw.sub_left (Offset.sub_base Ctx (show 240 + 16 ≤ 1024 by decide))).sub_right
      (Lay.wSub (by decide)))), hH]
  rw [hH₁] at p0
  unfold Impl.AesGcm.X86_64.Short.finishP
  refine WP.seq (WP.mono (finPowP_ok hF s₁ he₁.r13 (in_off cov₁ (show 272 + 16 ≤ 1024 by decide) (by exact (by decide : (1024 : Nat) < 2 ^ 64)))
    (in_off cov₁ (show 256 + 16 ≤ 1024 by decide) (by exact (by decide : (1024 : Nat) < 2 ^ 64))) p0.2 p0.1) fun s₂ ⟨x0, x1, h1, h2, o₂⟩ => ?_)
  have he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep (fun g hg => o₂.gpr _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> decide)) o₂.rd o₂.wr
  refine WP.mono (finRest_ok (q := 0) hks h (by omega) h16 f₁ hR₁ hc₁ hJ₁ (by rfl) hcb₁ ab₁ ht₁
    (by rw [m₁, Mem.readW_writeW_self64])
    (by rw [rW 200 (.inr (by decide)) (by decide), hdat]; simp)
    (by rw [rW 208 (.inr (by decide)) (by decide)]; exact hlen)
    (by rw [rW 184 (.inl (by decide)) (by decide)]; exact hal) he₂ o₂.mem
    (o₂.rd.trans rd₁) (o₂.wr.trans wr₁) x0 x1 h1 h2) fun t ⟨et, rdt, wrt, ft, hCt, hTt⟩ =>
      ⟨et, rdt, wrt, ft.sub fun r hr => ?_, hCt, hTt⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨below SP 56, by simp, b24⟩

end

/-- The bytes left compared with 17. -/
theorem lenTest_ok {Ctx St W SP : Addr} {n : Nat} (hn : n < 2 ^ 64) (s : State) (he : Env Ctx St W SP s)
    (hl : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 lenO)), .alu .cmp .rax (imm 17)]) s fun t =>
      t.cf = some (decide (n < 17)) ∧ (∀ g, g ≠ .rax → t.gpr g = s.gpr g) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  have q₁ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  obtain ⟨s₃, run₃, ax₃, g₃, m₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa [.mov .rax (.mem (at_ .r15 lenO))] s = some s₃ ∧
      s₃.gpr .rax = BitVec.ofNat 64 n ∧ (∀ g, g ≠ .rax → s₃.gpr g = s.gpr g) ∧ s₃.mem = s.mem ∧ s₃.rd = s.rd ∧
      s₃.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, q₁, hl], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · intro g hg; simp [gpr_setReg, hg]
    all_goals rfl
  obtain ⟨s₄, run₄, -, cf₄, g₄, m₄, rd₄, wr₄⟩ := cmpImm_ok s₃ .rax ax₃ hn (show 17 < 2 ^ 31 by decide)
  exact WP.block_append_iff.mpr (WP.of_runBlock ⟨s₃, run₃, WP.of_runBlock ⟨s₄, run₄, cf₄,
    fun g hg => by rw [g₄, g₃ g hg], m₄.trans m₃, rd₄.trans rd₃, wr₄.trans wr₃⟩⟩)

/-- `Fast.run`'s code after `prefix`: `tail` for at most 16 bytes left, and
`SealSplit.body` otherwise. -/
theorem fbody_ok (hF : ShortFacts) {ks : Prog isa} (hks : KsOk ks) (B : BlkFn (CtxMode.preparedN np hpn)) {fin : Prog isa}
    (hfin : FinOk (CtxMode.preparedN np hpn) fin) :
    BodyOk (CtxMode.preparedN np hpn) (.seq (.block [.mov .rax (.mem (at_ .r15 lenO)), .alu .cmp .rax (imm 17)])
      (.ite .b (Impl.AesGcm.X86_64.Fast.tail ks)
        (.frame (.push [.rax]) (.seq (oneBlocks B.enc) (.seq (.block SealSplit.fixTlen) fin)) (.pop .rax 1)))) := by
  intro Ctx W SP L R D n al N H icb a s he hR hdat hlen hd kw kd kM sp X hH hcb hal habs haux hN
  refine WP.seq (WP.mono (lenTest_ok hd.ok.lt s he hlen) fun t ⟨cf, g, m, rd, wr⟩ => ?_)
  have het : Env Ctx (W + BitVec.ofNat 64 16) W SP t := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g _ (by decide)) rd wr
  have hRt : RoundsAt t.mem W R := by rw [m]; exact hR
  have hdt := hd.of_eq rd wr
  have Xt := X.of_eq rd wr m
  have post : ∀ s' : State, (Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ s'.rd = t.rd ∧ s'.wr = t.wr ∧
      Frame (splitFrame W D SP n) t.mem s'.mem ∧
      bytesAt s'.mem D n = xorKs (ciphOf t.mem Ctx R) icb 0 (bytesAt t.mem D n) ∧
      bytesAt s'.mem W 16 = toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt s'.mem D n))))
        [ofBytes (lensBlock al N)] ^^^ ciphOf t.mem Ctx R (blockAt t.mem (W + BitVec.ofNat 64 16)))) →
      (Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (splitFrame W D SP n) s.mem s'.mem ∧
      bytesAt s'.mem D n = xorKs (ciphOf s.mem Ctx R) icb 0 (bytesAt s.mem D n) ∧
      bytesAt s'.mem W 16 = toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt s'.mem D n))))
        [ofBytes (lensBlock al N)] ^^^ ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16)))) :=
    fun s' ⟨e', rd', wr', f', hC, hT⟩ => ⟨e', rd'.trans rd, wr'.trans wr, m ▸ f', m ▸ hC, m ▸ hT⟩
  refine WP.ite (decide (n < 17)) (eval_b cf) (fun h => ?_) (fun h => ?_)
  · exact WP.mono (tail_ok L hF hks het hRt (by rw [m]; exact hdat) (by rw [m]; exact hlen)
      (by have := of_decide_eq_true h; omega) hdt kw kd kM sp Xt (by rw [m]; exact hH) (by rw [m]; exact hcb)
      (by rw [m]; exact hal) (by rw [m]; exact habs) (by rw [m]; exact haux)) post
  · exact WP.mono (body_ok L B hfin het hRt (by rw [m]; exact hdat) (by rw [m]; exact hlen) hdt kw kd kM sp Xt
      (by rw [m]; exact hH) (by rw [m]; exact hcb) (by rw [m]; exact hal) (by rw [m]; exact habs)
      (by rw [m]; exact haux) hN) post

end VG.Proof.AesGcm.X86_64.Fast
