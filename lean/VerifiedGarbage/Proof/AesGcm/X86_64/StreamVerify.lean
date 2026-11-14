module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Ghash1
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTag
import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_verify`

Untrusted: everything here is checked by Lean. A tag length `tagLenOk` does
not allow gives 0; any other pads the received tag, read from `tag`
(`recv`), computes the tag (`finTag 0`) and compares (`cmp 0`), without a
branch.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput ghashFrom ghash blocks zeros padLen ofBytes
  toBytes)
open VG.Proof.Gcm (Absorbed Ctr lensBlock)

/-- The regions the check of a received tag writes, with `N` bytes at `W`. -/
abbrev verFrame (St W SP : Addr) (N : Nat := 2560) : List Region :=
  [⟨St, 32⟩, ⟨W, 16⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 240, 32⟩, ⟨W + BitVec.ofNat 64 512, N - 512⟩,
    below SP 8]

/-- The tag `finTag` computes, for buffered input `x`. -/
abbrev tagOf (m : Mem) (Ctx St : Addr) (R : Nat) (aL tL : BitVec 64) (x : List Byte) : List Byte :=
  toBytes (ghashFrom (blockAt m (Ctx + BitVec.ofNat 64 240))
    (ghash (blockAt m (Ctx + BitVec.ofNat 64 240)) (blocks (x ++ zeros (padLen x.length))))
    [ofBytes (lensBlock aL.toNat tL.toNat)] ^^^ ciphOf m Ctx R (blockAt m St))

theorem bytesAt_take (m : Mem) (p : Addr) {t n : Nat} (h : t ≤ n) : bytesAt m p t = (bytesAt m p n).take t := by
  rw [show n = t + (n - t) by omega_arith, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]

section
variable (v : GcmImpl) {Ctx St W SP : Addr} {N gs : Nat} [G : GhFits v N gs] (L : Lay Ctx St W SP N)
include G L

/-- A received tag of an allowed length `t`, at `Tp` (in `rsi`), checked, with the call of `vg_aes_ctr32`
`T`. -/
theorem verifyCheck_ok (hN : 272 ≤ N) (T : TagCall v N) {R t : Nat} {s : State} (he : Env Ctx St W SP s N) (hR : RoundsAt s.mem W R)
    {aL tL : BitVec 64} (hA : s.mem.readW (W + BitVec.ofNat 64 184) 64 = aL)
    (hT : s.mem.readW (W + BitVec.ofNat 64 192) 64 = tL)
    (htl : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 t) (h1 : 1 ≤ t) (h16 : t ≤ 16) {Tp : Addr} (hsi : s.gpr .rsi = Tp)
    (hTr : Covers [⟨Tp, t⟩] (s.rd ++ s.wr)) (dTW : (⟨Tp, t⟩ : Region).Disjoint ⟨W, N⟩) {x : List Byte}
    (hx : x.length % 16 = (if tL = 0 then aL.toNat else tL.toNat) % 16) :
    WP isa (.seq recv (.seq (finTag v.callees 0) (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))]) (cmp 0)))) s
      fun s' => Env Ctx St W SP s' N ∧ Frame (verFrame St W SP N) s.mem s'.mem ∧
        (Absorbed s.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) x →
          s'.gpr .rax = (if (tagOf s.mem Ctx St R aL tL x).take t = bytesAt s.mem Tp t then 1 else 0)) := by
  refine WP.seq (WP.mono (recv_ok he hbx h1 h16 hsi hTr (dTW.sub_right (Lay.wSub (Lay.leN hN))) (Lay.leN hN) L.nlt)
    fun s₁ ⟨he₁, hrc, f₁, _⟩ => ?_)
  have dW : ∀ d k, (d + k ≤ 256 ∨ 272 ≤ d) → d + k ≤ N → ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)],
      (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k h h' r hr; simp only [List.mem_singleton] at hr; subst hr
    exact L.w_w (by omega_arith) h' (Lay.leN hN)
  have dS : ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)], ∀ d k, d + k ≤ 80 →
      (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro r hr d k hk; simp only [List.mem_singleton] at hr; subst hr
    exact L.st_w hk (.inr ⟨by decide, (Lay.leN hN)⟩)
  have rd₁ : ∀ d, d + 8 ≤ 256 → s₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => f₁.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (dW d 8 (.inl hd) (by omega_using [hN, hd]))
      (by decide)
  have hR₁ : RoundsAt s₁.mem W R := ⟨by rw [rd₁ 176 (by decide)]; exact hR.1, hR.2⟩
  refine WP.seq (WP.mono (finTag_ok v L (by omega_using [hN]) T (o := 0) (.inl rfl) he₁ hR₁ (by rw [rd₁ 184 (by decide), hA])
    (by rw [rd₁ 192 (by decide), hT]) hx) fun s₂ ⟨he₂, _, f₂, ht⟩ => ?_)
  have dT : ∀ d k, 112 ≤ d → d + k ≤ 272 → ∀ r ∈ tagFrame St W SP 0 N, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · simpa using (L.st_w (a := 0) (n := 32) (d := d) (k := k) (by decide) (.inr ⟨by omega_arith, by omega_arith⟩)).symm
    · exact L.w_w (.inr (by omega_arith)) (by omega_arith) (Lay.leN hN)
    · simpa using L.w_w (a := d) (n := k) (d := 0) (k := 16) (.inr (by omega_arith)) (by omega_arith) (Lay.leN hN)
    · exact L.w_hi (by omega_arith) (by omega_arith)
    · exact (L.stk_w (by omega_arith)).symm
  have rd₂ : ∀ d, 112 ≤ d → d + 8 ≤ 272 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (dT d 8 h₁ h₂) (by decide)
  have r₂ := he₂.perm.wR (show 224 + 8 ≤ N by omega_using [hN]) L.nlt
  obtain ⟨s₃, run₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO))] s₂ = some s₃ ∧
      s₃.gpr .rbx = BitVec.ofNat 64 t ∧ (∀ r, r ≠ .rbx → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧
      s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by xrun [he₂.r15, r₂], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, rd₂ 224 (by decide) (by decide), rd₁ 224 (by decide), htl]
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ : Env Ctx St W SP s₃ N := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
  have hrc₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 256) 16 = bytesAt s.mem Tp t ++ zeros (16 - t) := by
    rw [hm₃, bytesAt_frame f₂ (dT 256 16 (by decide) (by decide)) (by decide), hrc]
  refine WP.mono (cmp_ok L hN (o := 0) (.inl rfl) he₃ hbx₃ h1 h16 (length_bytesAt _ _ _) hrc₃)
    fun s₄ ⟨he₄, hax₄, f₄⟩ => ⟨he₄, ?_, fun ha => ?_⟩
  · rw [hm₃] at f₄
    refine ((f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)).trans (f₄.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨W + BitVec.ofNat 64 240, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 32⟩, by simp, fun _ h => h⟩
      · exact ⟨⟨W + BitVec.ofNat 64 96, 16⟩, by simp, fun _ h => h⟩
      · exact ⟨⟨W, 16⟩, by simp, by simpa using Region.sub_prefix (base := W) (show 16 ≤ 16 by decide)⟩
      · exact ⟨⟨W + BitVec.ofNat 64 512, N - 512⟩, by simp, fun _ h => h⟩
      · exact ⟨below SP 8, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨W + BitVec.ofNat 64 240, 32⟩, by simp, Region.sub_prefix (by decide)⟩
  · have dC : ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)], (⟨Ctx, 256⟩ : Region).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right (Lay.wSub (Lay.leN hN))
    have hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = blockAt s.mem (Ctx + BitVec.ofNat 64 240) :=
      blockAt_frame f₁ fun r hr => (dC r hr).sub_left (Lay.ctxSub (by decide))
    have hJ₁ : blockAt s₁.mem St = blockAt s.mem St := by simpa using blockAt_frame f₁ fun r hr => dS r hr 0 16 (by decide)
    have hc₁ : ciphOf s₁.mem Ctx R = ciphOf s.mem Ctx R := ciph_frame f₁ dC hR.2
    have ha₁ : Absorbed s₁.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32)
        (blockAt s₁.mem (Ctx + BitVec.ofNat 64 240)) x := by
      rw [hH₁]
      exact ha.congr (blockAt_frame f₁ fun r hr => dS r hr 16 16 (by decide))
        (bytesAt_frame f₁ (fun r hr => dS r hr 32 (x.length % 16) (by omega_arith)) (by omega_arith))
    have hT₂ : bytesAt s₂.mem (W + BitVec.ofNat 64 0) 16 = tagOf s.mem Ctx St R aL tL x := by
      rw [ht ha₁, hH₁, hc₁, hJ₁]
    have hT₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 0) t = (tagOf s.mem Ctx St R aL tL x).take t := by
      rw [hm₃, bytesAt_take _ _ h16, hT₂]
    rw [hax₄, hT₃]

end

/-- After the entry of `verify`: `FinEntry`, the tag length at `W + 224` and
in `rbx`, and the address of `tag` in `rsi`. -/
structure VerEntry (s₀ : State) (Ctx St W SP : Addr) (N : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s N
  rounds : RoundsAt s.mem W (s₀.gpr .rsi).toNat
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = s₀.gpr .rcx
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = s₀.gpr .r8
  tl : s.mem.readW (W + BitVec.ofNat 64 224) 64 = stackArg s₀ 0
  rbx : s.gpr .rbx = stackArg s₀ 0
  rsi : s.gpr .rsi = s₀.gpr .r9
  saved : SavedAt s.mem W s₀
  frame : Frame [savedR W, slotsR W, ⟨W + BitVec.ofNat 64 224, 8⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The entry of `verify`, with `W` at `[rsp + 16]` and the tag length at `[rsp + 8]`. -/
theorem verifyEntry_ok {s : State} {Ctx St W SP : Addr} {N : Nat} (L : Lay Ctx St W SP N) (hN : 272 ≤ N) (hCtx : s.gpr .rdi = Ctx)
    (hSt : s.gpr .rdx = St) (hSP : s.gpr .rsp = SP) (hW : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = W)
    (ha : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8) (ht : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 8) 8)
    (dA : (⟨SP + BitVec.ofNat 64 8, 8⟩ : Region).Disjoint ⟨W, N⟩) (hperm : Perm Ctx St W s N)
    (hR : (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14) :
    WP isa (.block (finEntry 16 ++ ([.mov .rbx (.mem (at_ .rsp 8)), .store (at_ .r15 tlO) .rbx,
      .mov .rsi (.reg .r9)] : List Instr))) s (VerEntry s Ctx St W SP N) := by
  refine WP.block_append (WP.mono (finEntry_ok hCtx hSt hSP hW ha hperm L.ww hR (Lay.leN hN) L.nlt) fun s₁ he => ?_)
  have dA' : ∀ r ∈ [savedR W, slotsR W], (⟨SP + BitVec.ofNat 64 8, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact dA.sub_right (Lay.wSub (Lay.leN hN))
  have htl₁ : s₁.mem.readW (SP + BitVec.ofNat 64 8) 64 = stackArg s 0 := by
    rw [he.frame.readW (r := ⟨SP + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _) dA' (by decide), ← hSP]; rfl
  have r₁ : InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 8) 8 := by rw [he.rd, he.wr]; exact ht
  have w₁ := he.env.perm.wW (show 224 + 8 ≤ N from (Lay.leN hN)) L.nlt
  obtain ⟨s₂, run₂, hbx₂, hsi₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rbx (.mem (at_ .rsp 8)),
      .store (at_ .r15 tlO) .rbx, .mov .rsi (.reg .r9)] s₁ = some s₂ ∧ s₂.gpr .rbx = stackArg s 0 ∧
      s₂.gpr .rsi = s.gpr .r9 ∧ (∀ r, r ≠ .rbx → r ≠ .rsi → s₂.gpr r = s₁.gpr r) ∧
      s₂.mem = s₁.mem.writeW (W + BitVec.ofNat 64 224) (stackArg s 0) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [he.env.rsp, he.env.r15, r₁, w₁], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, htl₁]
    · simp [gpr_setReg, he.r9]
    · intro r a b; simp [gpr_setReg, a, b]
    · simp [mem_setReg, gpr_setReg, htl₁]
    all_goals rfl
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have f₂ : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s₁.mem s₂.mem := by
    rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have rd₂ : ∀ d, (d + 8 ≤ 224 ∨ 232 ≤ d) → d + 8 ≤ N →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h h' =>
    f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega_arith) h' (Lay.leN hN)) (by decide)
  exact ⟨he.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂,
    ⟨by rw [rd₂ 176 (.inl (by decide)) (Lay.leN hN)]; exact he.rounds.1, he.rounds.2⟩,
    by rw [rd₂ 184 (.inl (by decide)) (Lay.leN hN)]; exact he.alen,
    by rw [rd₂ 192 (.inl (by decide)) (Lay.leN hN)]; exact he.tlen,
    by rw [hm₂, Mem.readW_writeW_self64], hbx₂, hsi₂,
    he.saved.frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (.inl (by decide)) (Lay.leN hN) (Lay.leN hN)),
    (he.frame.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp).trans
      (f₂.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp),
    hrd₂.trans he.rd, hwr₂.trans he.wr⟩

/-- What the precondition of `verify` gives. -/
theorem ver_lay {N : Nat} {s : State} (hp : Proof.AesGcm.verifyPre N s) (hN : 272 ≤ N := by decide)
    (hN' : N < 2 ^ 64 := by decide) :
    Lay (s.gpr .rdi) (s.gpr .rdx) (stackArg s 1) (s.gpr .rsp) N ∧
      Perm (s.gpr .rdi) (s.gpr .rdx) (stackArg s 1) s N ∧
      InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 16) 8 ∧
      InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8 ∧
      (⟨s.gpr .rsp + BitVec.ofNat 64 8, 8⟩ : Region).Disjoint ⟨stackArg s 1, N⟩ ∧
      Covers [⟨s.gpr .r9, (stackArg s 0).toNat⟩] (s.rd ++ s.wr) ∧
      (⟨s.gpr .r9, (stackArg s 0).toNat⟩ : Region).Disjoint ⟨stackArg s 1, N⟩ ∧
      (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, 80⟩ ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 1, N⟩ ∧
      (⟨s.gpr .rdx, 80⟩ : Region).Disjoint ⟨stackArg s 1, N⟩ ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14) := by
  simp only [Proof.AesGcm.verifyPre, Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, Proof.AesGcm.args,
    Proof.AesGcm.arg] at hp
  obtain ⟨hrd, hwr, d_cs, d_cw, d_sw, d_tw, d_wa, r_s, r_w, k_c, k_s, k_w, wc, ws, -, ww, -, hR⟩ := hp
  have hA : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := rfl
  rw [hA] at hrd d_wa
  have pa : Covers [⟨s.gpr .rsp + BitVec.ofNat 64 8, 16⟩] (s.rd ++ s.wr) := by
    rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_singleton_self _))))
  refine ⟨Lay.of wc ws ww d_cs d_cw d_sw k_c k_s k_w (by omega_using [hN]) hN',
    ⟨by rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..)),
      by rw [hwr]; exact covers_of_mem (List.mem_cons_self ..),
      by rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩, ?_,
    by simpa using in_off pa (d := 0) (n := 8) (by decide) (by decide),
    d_wa.symm.sub_left (Region.sub_prefix (by decide)),
    by rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
    by simpa using d_tw, r_s, r_w, d_sw, hR⟩
  have := in_off pa (d := 8) (n := 8) (by decide) (by decide)
  rwa [add_ofNat_assoc] at this

/-- One run of `vg_aes_gcm_stream_verify`, for the input `x` GHASH has. -/
theorem streamVerify_run (v : GcmImpl) {N gs : Nat} [G : GhFits v N gs] (TC : TagCall v N) (hN : 272 ≤ N) (hN' : N < 2 ^ 64) {s : State}
    (hp : (Proof.AesGcm.streamVerifyX86_64 N).pre s) {x : List Byte}
    (hx : x.length % 16 = (if s.gpr .r8 = 0 then (s.gpr .rcx).toNat else (s.gpr .r8).toNat) % 16) :
    WP isa (streamVerify v.callees) s fun s' => gprPreserved s s' ∧
      (Absorbed s.mem (s.gpr .rdx + BitVec.ofNat 64 16) (s.gpr .rdx + BitVec.ofNat 64 32) (ctxH s.mem (s.gpr .rdi)) x →
        let T := tagOf s.mem (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rsi).toNat (s.gpr .rcx) (s.gpr .r8) x
        let t := (stackArg s 0).toNat
        if Spec.Gcm.tagLenOk t ∧ T.take t = bytesAt s.mem (s.gpr .r9) t then s'.gpr .rax = 1
        else s'.gpr .rax = 0) := by
  obtain ⟨L, hperm, ha, hta, dA, hTr, dTW, r_s, r_w, d_sw, hR⟩ := ver_lay hp hN hN'
  have hW : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 16) 64 = stackArg s 1 := rfl
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSt : s.gpr .rdx = St at *
  generalize hTp : s.gpr .r9 = Tp at *
  generalize hWd : stackArg s 1 = W at *
  generalize hSP : s.gpr .rsp = SP at *
  -- The entry, and the tag length kept at `W + 224`.
  refine WP.seq (WP.mono (verifyEntry_ok L hN hCtx hSt hSP hW ha hta dA hperm hR) fun s₂ he => ?_)
  generalize htl : stackArg s 0 = tl at *
  refine WP.seq (WP.mono (tagLenOk_ok s₂ (t := tl.toNat) (by rw [he.rbx, htl]; simp) tl.isLt) fun s₃ ⟨hz₃, k₃⟩ => ?_)
  have he₃ : Env Ctx St W SP s₃ N := he.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact k₃.gpr _ (by decide)) k₃.rd k₃.wr
  have F₃ : Frame [savedR W, slotsR W, ⟨W + BitVec.ofNat 64 224, 8⟩] s.mem s₃.mem := by rw [k₃.mem]; exact he.frame
  have dF : ∀ p k, (⟨p, k⟩ : Region).Disjoint ⟨W, N⟩ → ∀ r ∈ [savedR W, slotsR W, ⟨W + BitVec.ofNat 64 224, 8⟩],
      (⟨p, k⟩ : Region).Disjoint r := by
    intro p k h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact h.sub_right (Lay.wSub (Lay.leN hN))
  generalize ht : tl.toNat = t at *
  have htl₃ : s₃.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
    rw [k₃.mem, he.tl, htl, ← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hbx₃ : s₃.gpr .rbx = BitVec.ofNat 64 t := by
    rw [k₃.gpr _ (by decide), he.rbx, htl, ← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hsi₃ : s₃.gpr .rsi = Tp := by rw [k₃.gpr _ (by decide), he.rsi, hTp]
  have hR₃ : RoundsAt s₃.mem W (s.gpr .rsi).toNat := by rw [k₃.mem]; exact he.rounds
  have hA₃ : s₃.mem.readW (W + BitVec.ofNat 64 184) 64 = s.gpr .rcx := by rw [k₃.mem]; exact he.alen
  have hT₃ : s₃.mem.readW (W + BitVec.ofNat 64 192) 64 = s.gpr .r8 := by rw [k₃.mem]; exact he.tlen
  have hTr₃ : Covers [⟨Tp, t⟩] (s₃.rd ++ s₃.wr) := by rw [k₃.rd, k₃.wr, he.rd, he.wr]; exact hTr
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => Env Ctx St W SP s₄ N ∧ Frame (verFrame St W SP N) s₃.mem s₄.mem ∧
      (Absorbed s₃.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32)
          (blockAt s₃.mem (Ctx + BitVec.ofNat 64 240)) x →
        let T := tagOf s₃.mem Ctx St (s.gpr .rsi).toNat (s.gpr .rcx) (s.gpr .r8) x
        if Spec.Gcm.tagLenOk t ∧ T.take t = bytesAt s₃.mem Tp t then s₄.gpr .rax = 1 else s₄.gpr .rax = 0))
    (WP.ite (!Spec.Gcm.tagLenOk t) (eval_e hz₃) (fun hbad => ?_) (fun hok => ?_)) fun s₄ h₄ => ?_)
  · -- A length `tagLenOk` does not allow.
    have hbad' : Spec.Gcm.tagLenOk t = false := by simpa using hbad
    refine WP.run (Q := fun s₄ => s₄.gpr .rax = 0 ∧ (∀ r, r ≠ .rax → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧
        s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr)
      ⟨_, by xrun [], by simp [gpr_setReg], fun r hr => by simp [gpr_setReg, hr], by rfl, by rfl, by rfl⟩
      fun s₄ ⟨hax, hg₄, hm₄, hrd₄, hwr₄⟩ => ?_
    refine ⟨he₃.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide)) hrd₄ hwr₄, by rw [hm₄]; exact Frame.refl _ _,
      fun _ => ?_⟩
    simp only [hbad', Bool.false_eq_true, false_and, ↓reduceIte]
    exact hax
  · -- An allowed length.
    have hok' : Spec.Gcm.tagLenOk t = true := by simpa using hok
    have hb : 1 ≤ t ∧ t ≤ 16 := by
      simp only [Spec.Gcm.tagLenOk, Bool.and_eq_true, decide_eq_true_eq] at hok'
      omega_arith
    refine WP.mono (verifyCheck_ok v L hN TC he₃ hR₃ hA₃ hT₃ htl₃ hbx₃ hb.1 hb.2 hsi₃
      hTr₃ dTW hx)
      fun s₄ ⟨he₄, f₄, hq⟩ => ⟨he₄, f₄, fun ha => ?_⟩
    simp only [hok', true_and]
    have hax := hq ha
    split
    · next e => simp only [e, ↓reduceIte] at hax; exact hax
    · next e => simp only [e, ↓reduceIte] at hax; exact hax
  obtain ⟨he₄, f₄, hq⟩ := h₄
  have dV : ∀ r ∈ verFrame St W SP N, (savedR W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa using (L.st_w (a := 0) (n := 32) (d := 128) (k := 48) (by decide) (.inr ⟨by decide, (Lay.leN hN)⟩)).symm
    · simpa using L.w_w (a := 128) (n := 48) (d := 0) (k := 16) (.inr (by decide)) (Lay.leN hN) (Lay.leN hN)
    · exact L.w_w (.inr (by decide)) (Lay.leN hN) (Lay.leN hN)
    · exact L.w_w (.inl (by decide)) (Lay.leN hN) (Lay.leN hN)
    · exact L.w_hi (by decide) (Lay.leN hN)
    · exact (L.stk_w (Lay.leN hN)).symm
  have hsv₃ : SavedAt s₃.mem W s := by rw [k₃.mem]; exact he.saved
  have hsv₄ : SavedAt s₄.mem W s := hsv₃.frame f₄ dV
  have hret : s₄.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [ret_kept f₄ (fun r hr => ?_), ret_kept F₃ (fun r hr => ?_)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact r_w.sub_right (Lay.wSub (Lay.leN hN))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact r_s.sub_right (Region.sub_prefix (by decide))
      · exact r_w.sub_right (Region.sub_prefix (by omega_using [hN]))
      · exact r_w.sub_right (Lay.wSub (Lay.leN hN))
      · exact r_w.sub_right (Lay.wSub (Lay.leN hN))
      · exact r_w.sub_right Lay.hiSub
      · exact ret_below SP
  refine WP.mono (exit_ok he₄.r15 (by rw [he₄.rsp, hSP]) (covers_left he₄.perm.w) hsv₄ (by rw [hSP, hret]) (by omega_using [hN]))
    fun s' ⟨hg, _, hax⟩ => ⟨hg, fun ha => ?_⟩
  have dS : ∀ d k, d + k ≤ 80 → ∀ r ∈ [savedR W, slotsR W, ⟨W + BitVec.ofNat 64 224, 8⟩],
      (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun d k hk => dF _ _ (d_sw.sub_left (Lay.stSub hk))
  have hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [ctxH_eq]; exact blockAt_frame F₃ (dF _ _ (L.cw'.sub_left (Lay.ctxSub (by decide))))
  have ha₃ : Absorbed s₃.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32)
      (blockAt s₃.mem (Ctx + BitVec.ofNat 64 240)) x := by
    rw [hH₃]
    exact ha.congr (blockAt_frame F₃ (dS 16 16 (by decide))) (bytesAt_frame F₃ (dS 32 _ (by omega_arith)) (by omega_arith))
  have hT : tagOf s₃.mem Ctx St (s.gpr .rsi).toNat (s.gpr .rcx) (s.gpr .r8) x =
      tagOf s.mem Ctx St (s.gpr .rsi).toNat (s.gpr .rcx) (s.gpr .r8) x := by
    simp only [tagOf]
    rw [hH₃, ← ctxH_eq, ciph_frame F₃ (dF _ _ L.cw') hR, show blockAt s₃.mem St = blockAt s.mem St by
      simpa using blockAt_frame F₃ (dS 0 16 (by decide))]
  have hrc : bytesAt s₃.mem Tp t = bytesAt s.mem Tp t :=
    bytesAt_frame F₃ (dF _ _ dTW) (by rw [← ht]; exact Nat.le_of_lt tl.isLt)
  have hq' := hq ha₃
  rw [hT, hrc] at hq'
  dsimp only
  rw [hax]
  exact hq'

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr ctxH ctxCiph ghashInput zeros blockAt)

theorem tagOf_eq {m : Mem} {Ctx St : Addr} {R : Nat} {aL tL : BitVec 64} {ciph : Spec.Gcm.Block → Spec.Gcm.Block}
    {iv a c : List Byte} (hj : blockAt m St = Spec.Gcm.j0 (ctxH m Ctx) iv) (hc : ciph = ctxCiph m Ctx R)
    (hA : aL = BitVec.ofNat 64 a.length) (hT : tL.toNat = c.length) :
    tagOf m Ctx St R aL tL (ghashInput a c) = Spec.Gcm.fullTag ciph (ctxH m Ctx) iv a c := by
  rw [Proof.Gcm.fullTag_eq, tagOf, ← ctxH_eq, hj, hA, hT, BitVec.toNat_ofNat, lensBlock_mod_left, hc]
  rfl

/-- `vg_aes_gcm_stream_verify`. -/
theorem streamVerify_wp (v : GcmImpl) {N gs : Nat} [G : GhFits v N gs] (T : TagCall v N) (hN : 272 ≤ N) (hN' : N < 2 ^ 64) {s : State}
    (hp : (Proof.AesGcm.streamVerifyX86_64 N).pre s) :
    WP isa (streamVerify v.callees) s fun s' => gprPreserved s s' ∧ (Proof.AesGcm.streamVerifyX86_64 N).post s s' := by
  have h := WP.forall_det
    (P := fun i : List Byte × List Byte × List Byte =>
      s.gpr .rcx = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .r8).toNat = i.2.2.length)
    (R := gprPreserved s)
    (WP.mono (streamVerify_run v T hN hN' hp (x := List.replicate
      ((if s.gpr .r8 = 0 then (s.gpr .rcx).toNat else (s.gpr .r8).toNat) % 16) 0) (by simp)) fun _ h => h.1)
    fun i hi => WP.mono (streamVerify_run v T hN hN' hp (ghashInput_lens hi.1 hi.2)) fun _ h => h.2
  refine WP.mono h fun s' ⟨hg, hq⟩ => ⟨hg, fun iv a c hr hA hT => ?_⟩
  rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit] at hr
  obtain ⟨hj, ha, -⟩ := hr
  have e := hq (iv, a, c) ⟨hA, hT⟩ ha
  simp only [Proof.AesGcm.arg] at e ⊢
  rw [tagOf_eq hj rfl hA hT] at e
  split
  · next hc => simp only [hc, and_self, ↓reduceIte] at e; rw [e]; rfl
  · next hc => simp only [hc, ↓reduceIte] at e; rw [e]; rfl

end VG.Proof.AesGcm.X86_64
