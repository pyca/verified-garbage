module

-- separate module: the digest's constant-time proof, whose sponge calls take most of the build of verify's body CT

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopCTBlocks
public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopHash
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCT

/-!
# SLH-DSA (SHAKE) on x86-64, `verify`: the digest in constant time

Untrusted: everything here is checked by Lean. Two runs, each in a `Ctx`
state of the same layout, whose calls of the sponge functions take the same
arguments, leak the same (`kabs_ct`, `kpad_ct`, `ksqz_ct`), and so do two
runs of `hashM'` (`hash_ct`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.VerifyTop

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Impl.SlhDsa.X86_64.Shake (Arg kabs kpad ksqz callA hashM')
open VG.Proof.MlKem.X86_64 (AbsorbArgs PadArgs SqueezeArgs absorb_pre pad_pre squeeze_pre)

variable {L : VL}

theorem ce_rsp (t : State) (rd wr : List Region) : (t.callEntry.withRegions rd wr).gpr .rsp = t.gpr .rsp - 8 := by
  rw [State.withRegions_gpr, State.callEntry_rsp]

theorem ce_reg (t : State) (rd wr : List Region) {r : Reg} (h : r ≠ .rsp) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

theorem kabs_ct {p : Params} (hS : S6 p) (hL : L.Ok) {src len pos : Arg} (h1 : argOk src) (h2 : argOk len)
    (h3 : argOk pos) (has : [.scr Layout.oStream, .imm 136, pos, src, len, .scr (Layout.oStream + 200)] ∈ verifyArgLists p)
    {dp : Addr} {N q : Nat} (hql : q < 136) (hNl : N < 2 ^ 64)
    (hin : InRegions (L.rd ++ [L.FR, L.SCR]) dp N) (dS : Region.Disjoint ⟨dp, N⟩ ⟨L.ST, 840⟩)
    (kD : (below L.SP 16).Disjoint ⟨dp, N⟩) {A₁ A₂ : State → Prop}
    (hA : ∀ t, A₁ t ∨ A₂ t → ∃ g m₀, Ctx L g m₀ t ∧ argVal t src = dp ∧ argVal t len = BitVec.ofNat 64 N ∧
      argVal t pos = BitVec.ofNat 64 q) :
    RelCT isa (fun a b => A₁ a ∧ A₂ b) (kabs src len pos) fun _ _ => True := by
  unfold kabs callA
  let B : State → Prop := fun t1 => (∃ g m₀, Ctx L g m₀ t1) ∧ AbsorbArgs t1 L.ST dp L.KS 136 q N ∧
    Covers ([⟨dp, N⟩] ++ [⟨L.ST, 200⟩, ⟨L.KS, 640⟩]) (t1.rd ++ t1.wr) ∧ Covers [⟨L.ST, 200⟩, ⟨L.KS, 640⟩] t1.wr
  have hw : ∀ t, A₁ t ∨ A₂ t → WP isa (.block (([Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9].zip [Arg.scr Layout.oStream,
      .imm 136, pos, src, len, .scr (Layout.oStream + 200)]).flatMap fun (d, a) => a.mov d)) t B := fun t ht => by
    obtain ⟨g, m₀, hc, e1, e2, e3⟩ := hA t ht
    exact WP.mono (kabs_mv hL hc h1 h2 h3 e1 e2 e3 hql hNl hin dS kD) fun t1 ⟨hc1, _, ha, c1, c2⟩ =>
      ⟨⟨g, m₀, hc1⟩, ha, c1, c2⟩
  refine Levels.relSeq (B₁ := B) (B₂ := B) (ct_args hS _ has fun x y ⟨hx, hy⟩ r hr => ?_)
    (fun a h => hw a (.inl h)) (fun b h => hw b (.inr h)) ?_
  · obtain ⟨_, _, cx, -⟩ := hA x (.inl hx)
    obtain ⟨_, _, cy, -⟩ := hA y (.inr hy)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [cx.rsp, cy.rsp]
    · rw [cx.rbx, cy.rbx]
  refine RelCT.call Proof.Sha3.X86_64.Stream.Absorb.absorb_correct Proof.Sha3.X86_64.Stream.Absorb.absorb_ct
    [⟨dp, N⟩] [⟨L.ST, 200⟩, ⟨L.KS, 640⟩] fun a b ⟨⟨⟨_, _, ca⟩, aa, a1, a2⟩, ⟨⟨_, _, cb⟩, ab, b1, b2⟩⟩ =>
      ⟨absorb_pre aa, absorb_pre ab, ?_, a1, a2, b1, b2, by rw [ca.rsp, cb.rsp]⟩
  simp only [Proof.Sha3.absorbX86_64, ce_reg _ _ _ (show Reg.rdi ≠ .rsp by decide),
    ce_reg _ _ _ (show Reg.rsi ≠ .rsp by decide), ce_reg _ _ _ (show Reg.rdx ≠ .rsp by decide),
    ce_reg _ _ _ (show Reg.rcx ≠ .rsp by decide), ce_reg _ _ _ (show Reg.r8 ≠ .rsp by decide),
    ce_reg _ _ _ (show Reg.r9 ≠ .rsp by decide), ce_rsp, aa.rdi, ab.rdi, aa.rsi, ab.rsi, aa.rdx, ab.rdx, aa.rcx, ab.rcx,
    aa.r8, ab.r8, aa.r9, ab.r9, ca.rsp, cb.rsp, and_self]

theorem kpad_ct {p : Params} (hS : S6 p) (hL : L.Ok) {pos : Arg} (h3 : argOk pos)
    (has : [.scr Layout.oStream, .imm 136, pos, .imm 0x1f, .scr (Layout.oStream + 200)] ∈ verifyArgLists p)
    {q : Nat} (hql : q < 136) {A₁ A₂ : State → Prop}
    (hA : ∀ t, A₁ t ∨ A₂ t → ∃ g m₀, Ctx L g m₀ t ∧ argVal t pos = BitVec.ofNat 64 q) :
    RelCT isa (fun a b => A₁ a ∧ A₂ b) (kpad pos) fun _ _ => True := by
  unfold kpad callA
  let B : State → Prop := fun t1 => (∃ g m₀, Ctx L g m₀ t1) ∧ PadArgs t1 L.ST L.KS 136 q ∧
    Covers ([] ++ [⟨L.ST, 200⟩, ⟨L.KS, 640⟩]) (t1.rd ++ t1.wr) ∧ Covers [⟨L.ST, 200⟩, ⟨L.KS, 640⟩] t1.wr
  have hw : ∀ t, A₁ t ∨ A₂ t → WP isa (.block (([Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9].zip [Arg.scr Layout.oStream,
      .imm 136, pos, .imm 0x1f, .scr (Layout.oStream + 200)]).flatMap fun (d, a) => a.mov d)) t B := fun t ht => by
    obtain ⟨g, m₀, hc, e3⟩ := hA t ht
    exact WP.mono (kpad_mv hL hc h3 e3 hql) fun t1 ⟨hc1, ha, c1, c2⟩ => ⟨⟨g, m₀, hc1⟩, ha, c1, c2⟩
  refine Levels.relSeq (B₁ := B) (B₂ := B) (ct_args hS _ has fun x y ⟨hx, hy⟩ r hr => ?_)
    (fun a h => hw a (.inl h)) (fun b h => hw b (.inr h)) ?_
  · obtain ⟨_, _, cx, -⟩ := hA x (.inl hx)
    obtain ⟨_, _, cy, -⟩ := hA y (.inr hy)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [cx.rsp, cy.rsp]
    · rw [cx.rbx, cy.rbx]
  refine RelCT.call Proof.Sha3.X86_64.Stream.Pad.pad_correct Proof.Sha3.X86_64.Stream.Pad.pad_ct
    [] [⟨L.ST, 200⟩, ⟨L.KS, 640⟩] fun a b ⟨⟨⟨_, _, ca⟩, aa, a1, a2⟩, ⟨⟨_, _, cb⟩, ab, b1, b2⟩⟩ =>
      ⟨pad_pre aa, pad_pre ab, ?_, a1, a2, b1, b2, by rw [ca.rsp, cb.rsp]⟩
  simp only [Proof.Sha3.padX86_64, ce_reg _ _ _ (show Reg.rdi ≠ .rsp by decide),
    ce_reg _ _ _ (show Reg.rsi ≠ .rsp by decide), ce_reg _ _ _ (show Reg.rdx ≠ .rsp by decide),
    ce_reg _ _ _ (show Reg.r8 ≠ .rsp by decide), ce_rsp, aa.rdi, ab.rdi, aa.rsi, ab.rsi, aa.rdx, ab.rdx,
    aa.r8, ab.r8, ca.rsp, cb.rsp, and_self]

theorem ksqz_ct {p : Params} (hS : S6 p) (hL : L.Ok) {A₁ A₂ : State → Prop}
    (hA : ∀ t, A₁ t ∨ A₂ t → ∃ g m₀, Ctx L g m₀ t) :
    RelCT isa (fun a b => A₁ a ∧ A₂ b) (ksqz (.scr Layout.oDigest) p.m) fun _ _ => True := by
  have hm := (S6.par hS).m64
  have eD : Layout.oDigest = 30304 := rfl
  unfold ksqz callA
  let B : State → Prop := fun t1 => (∃ g m₀, Ctx L g m₀ t1) ∧
    SqueezeArgs t1 L.ST (at' L.S Layout.oDigest) L.KS 136 0 p.m ∧
    Covers ([] ++ [⟨L.ST, 200⟩, ⟨at' L.S Layout.oDigest, p.m⟩, ⟨L.KS, 640⟩]) (t1.rd ++ t1.wr) ∧
    Covers [⟨L.ST, 200⟩, ⟨at' L.S Layout.oDigest, p.m⟩, ⟨L.KS, 640⟩] t1.wr
  have hw : ∀ t, A₁ t ∨ A₂ t → WP isa (.block (([Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9].zip [Arg.scr Layout.oStream,
      .imm 136, .imm 0, .scr Layout.oDigest, .imm p.m, .scr (Layout.oStream + 200)]).flatMap fun (d, a) => a.mov d))
      t B := fun t ht => by
    obtain ⟨g, m₀, hc⟩ := hA t ht
    exact WP.mono (ksqz_mv hL hc (o := Layout.oDigest) (m := p.m) (by rw [eD]; omega) (by rw [eD, oStream_eq]; omega)
      (by omega)) fun t1 ⟨hc1, ha, c1, c2⟩ => ⟨⟨g, m₀, hc1⟩, ha, c1, c2⟩
  refine Levels.relSeq (B₁ := B) (B₂ := B) (ct_args hS _ (by simp [verifyArgLists]) fun x y ⟨hx, hy⟩ r hr => ?_)
    (fun a h => hw a (.inl h)) (fun b h => hw b (.inr h)) ?_
  · obtain ⟨_, _, cx⟩ := hA x (.inl hx)
    obtain ⟨_, _, cy⟩ := hA y (.inr hy)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [cx.rsp, cy.rsp]
    · rw [cx.rbx, cy.rbx]
  refine RelCT.call Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct Proof.Sha3.X86_64.Stream.Squeeze.squeeze_ct
    [] [⟨L.ST, 200⟩, ⟨at' L.S Layout.oDigest, p.m⟩, ⟨L.KS, 640⟩]
    fun a b ⟨⟨⟨_, _, ca⟩, aa, a1, a2⟩, ⟨⟨_, _, cb⟩, ab, b1, b2⟩⟩ =>
      ⟨squeeze_pre aa, squeeze_pre ab, ?_, a1, a2, b1, b2, by rw [ca.rsp, cb.rsp]⟩
  simp only [Proof.Sha3.squeezeX86_64, ce_reg _ _ _ (show Reg.rdi ≠ .rsp by decide),
    ce_reg _ _ _ (show Reg.rsi ≠ .rsp by decide), ce_reg _ _ _ (show Reg.rdx ≠ .rsp by decide),
    ce_reg _ _ _ (show Reg.rcx ≠ .rsp by decide), ce_reg _ _ _ (show Reg.r8 ≠ .rsp by decide),
    ce_reg _ _ _ (show Reg.r9 ≠ .rsp by decide), ce_rsp, aa.rdi, ab.rdi, aa.rsi, ab.rsi, aa.rdx, ab.rdx, aa.rcx, ab.rcx,
    aa.r8, ab.r8, aa.r9, ab.r9, ca.rsp, cb.rsp, and_self]

/-- A run in a `Ctx` state, and one whose `rax` is `q`. -/
abbrev CC (L : VL) (t : State) : Prop := ∃ g m₀, Ctx L g m₀ t
abbrev CR (L : VL) (q : Nat) (t : State) : Prop := CC L t ∧ (t.gpr .rax).toNat = q

theorem kstep {p : Params} (hS : S6 p) (hL : L.Ok) {src len pos : Arg} (h1 : argOk src) (h2 : argOk len)
    (h3 : argOk pos) (has : [.scr Layout.oStream, .imm 136, pos, src, len, .scr (Layout.oStream + 200)] ∈ verifyArgLists p)
    {dp : Addr} {N q : Nat} (hql : q < 136) (hNl : N < 2 ^ 64)
    (hin : InRegions (L.rd ++ [L.FR, L.SCR]) dp N) (dS : Region.Disjoint ⟨dp, N⟩ ⟨L.ST, 840⟩)
    (kD : (below L.SP 16).Disjoint ⟨dp, N⟩) {A₁ A₂ : State → Prop}
    (hA : ∀ t, A₁ t ∨ A₂ t → ∃ g m₀, Ctx L g m₀ t ∧ argVal t src = dp ∧ argVal t len = BitVec.ofNat 64 N ∧
      argVal t pos = BitVec.ofNat 64 q) {c : Prog isa} {Q : State → State → Prop}
    (hr : RelCT isa (fun a b => CR L ((q + N) % 136) a ∧ CR L ((q + N) % 136) b) c Q) :
    RelCT isa (fun a b => A₁ a ∧ A₂ b) (.seq (kabs src len pos) c) Q := by
  have hw : ∀ t, A₁ t ∨ A₂ t → WP isa (kabs src len pos) t (CR L ((q + N) % 136)) := fun t ht => by
    obtain ⟨g, m₀, hc, e1, e2, e3⟩ := hA t ht
    exact WP.mono (kabs_ok hL hc h1 h2 h3 e1 e2 e3 hql hNl hin dS kD) fun t' ⟨hc', _, hx⟩ => ⟨⟨g, m₀, hc'⟩, hx⟩
  exact Levels.relSeq (kabs_ct hS hL h1 h2 h3 has hql hNl hin dS kD hA) (fun a h => hw a (.inl h))
    (fun b h => hw b (.inr h)) hr

theorem hash_ct {p : Params} (hS : S6 p) (hL : L.Ok) (hn : L.n = p.n) (hsl : L.n ≤ L.sigL) {A₁ A₂ : State → Prop}
    (hA : ∀ t, A₁ t ∨ A₂ t → CC L t) :
    RelCT isa (fun a b => A₁ a ∧ A₂ b) (hashM' p [.slot Impl.SlhDsa.X86_64.Verify.fVSig, .scr Layout.oPkSeed,
      .scr Layout.oPkRoot] (.scr Layout.oDigest) p.m) fun _ _ => True := by
  have hn32 := hL.n32
  have hp32 : p.n ≤ 32 := by omega
  have ctxLt := hL.ctxLt
  have eP : Layout.oPkSeed = 3232 := rfl
  have eR : Layout.oPkRoot = 3264 := rfl
  unfold hashM'
  simp only [List.zipIdx_cons, List.zipIdx_nil, List.foldr_cons, List.foldr_nil, List.length_cons, List.length_nil]
  rw [← hn]
  have hz : ∀ t, A₁ t ∨ A₂ t → WP isa (.block Impl.SlhDsa.X86_64.Shake.zeroState) t (CC L) := fun t ht => by
    obtain ⟨g, m₀, hc⟩ := hA t ht
    exact WP.mono (zero_ok hL hc) fun t' ⟨hc', _⟩ => ⟨g, m₀, hc'⟩
  refine Levels.relSeq (B₁ := CC L) (B₂ := CC L) (ct_zero fun x y ⟨hx, hy⟩ r hr => ?_) (fun a h => hz a (.inl h))
    (fun b h => hz b (.inr h)) ?_
  · obtain ⟨_, _, cx⟩ := hA x (.inl hx)
    obtain ⟨_, _, cy⟩ := hA y (.inr hy)
    simp only [List.mem_singleton] at hr; subst hr; rw [cx.rbx, cy.rbx]
  have hcc : ∀ {q : Nat} {t : State}, CC L t ∨ CR L q t → CC L t := fun h => by rcases h with h | h; exacts [h, h.1]
  -- `R`
  obtain ⟨i1, d1, k1⟩ := input_src hL (R := L.SIG) (by simp) hL.sSig hL.kSig (N := L.n) hsl
  refine kstep hS hL (src := .slot Impl.SlhDsa.X86_64.Verify.fVSig) (len := .imm L.n) (pos := .imm (L.n * 0)) (N := L.n) (q := L.n * 0)
    (by show 16 + 8 ≤ 72; omega) (by show L.n < 2 ^ 32; omega) (by show _ < 2 ^ 32; omega)
    (by rw [hn]; simp [verifyArgLists]) (by omega) (by omega) i1 d1 k1 (fun t ht => by
      obtain ⟨g, m₀, hc⟩ : CC L t := by rcases ht with h | h <;> exact h
      exact ⟨g, m₀, hc, by simp only [argVal, Impl.SlhDsa.X86_64.Verify.fVSig, hc.rsp]; exact hc.pSig, rfl, rfl⟩) ?_
  -- `PK.seed`
  obtain ⟨i2, d2, k2⟩ := scr_src hL (o := Layout.oPkSeed) (N := L.n) (by rw [eP, oStream_eq]; omega)
  refine kstep hS hL (src := .scr Layout.oPkSeed) (len := .imm L.n) (pos := .imm (L.n * (0 + 1))) (N := L.n) (q := L.n * (0 + 1))
    (by show _ < 2 ^ 31; rw [eP]; omega) (by show L.n < 2 ^ 32; omega) (by show _ < 2 ^ 32; omega)
    (by rw [hn]; simp [verifyArgLists]) (by omega) (by omega) i2 d2 k2 (fun t ht => by
      obtain ⟨g, m₀, hc⟩ := ht.elim (·.1) (·.1)
      exact ⟨g, m₀, hc, by simp only [argVal, hc.rbx], rfl, rfl⟩) ?_
  -- `PK.root`
  obtain ⟨i3, d3, k3⟩ := scr_src hL (o := Layout.oPkRoot) (N := L.n) (by rw [eR, oStream_eq]; omega)
  refine kstep hS hL (src := .scr Layout.oPkRoot) (len := .imm L.n) (pos := .imm (L.n * (0 + 1 + 1))) (N := L.n) (q := L.n * (0 + 1 + 1))
    (by show _ < 2 ^ 31; rw [eR]; omega) (by show L.n < 2 ^ 32; omega) (by show _ < 2 ^ 32; omega)
    (by rw [hn]; simp [verifyArgLists]) (by omega) (by omega) i3 d3 k3 (fun t ht => by
      obtain ⟨g, m₀, hc⟩ := ht.elim (·.1) (·.1)
      exact ⟨g, m₀, hc, by simp only [argVal, hc.rbx], rfl, rfl⟩) ?_
  -- `0 ‖ ctx_len`
  obtain ⟨i4, d4, k4⟩ := sp_src hL
  refine kstep hS hL (src := .sp) (len := .imm 2) (pos := .imm (L.n * (0 + 1 + 1 + 1))) (N := 2)
    (q := L.n * (0 + 1 + 1 + 1)) trivial
    (by show 2 < 2 ^ 32; omega) (by show _ < 2 ^ 32; omega) (by rw [hn]; simp [verifyArgLists]) (by omega) (by omega)
    i4 d4 k4 (fun t ht => by
      obtain ⟨g, m₀, hc⟩ := ht.elim (·.1) (·.1)
      exact ⟨g, m₀, hc, by simp only [argVal, hc.rsp], rfl, rfl⟩) ?_
  -- `ctx`
  obtain ⟨i5, d5, k5⟩ := input_src hL (R := L.CTX) (by simp) hL.sCtx hL.kCtx (N := L.ctxLen.toNat) (Nat.le_refl _)
  refine kstep hS hL (src := .slot Impl.SlhDsa.X86_64.Shake.fCtx) (len := .slot Impl.SlhDsa.X86_64.Shake.fCtxLen)
    (pos := .ret) (N := L.ctxLen.toNat) (q := (L.n * (0 + 1 + 1 + 1) + 2) % 136) (by show 40 + 8 ≤ 72; omega) (by show 32 + 8 ≤ 72; omega) trivial (by simp [verifyArgLists])
    (Nat.mod_lt _ (by decide)) (by have := L.ctxLen.isLt; omega) i5 d5 k5 (fun t ht => by
      obtain ⟨⟨g, m₀, hc⟩, hx⟩ := ht.elim id id
      exact ⟨g, m₀, hc, by simp only [argVal, Impl.SlhDsa.X86_64.Shake.fCtx, hc.rsp]; exact hc.pCtx,
        by simp only [argVal, Impl.SlhDsa.X86_64.Shake.fCtxLen, hc.rsp]; rw [hc.pCtxLen, BitVec.ofNat_toNat,
          BitVec.setWidth_eq],
        by simp only [argVal]; rw [← hx, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩) ?_
  -- the message
  obtain ⟨i6, d6, k6⟩ := input_src hL (R := L.MSG) (by simp) hL.sMsg hL.kMsg (N := L.len.toNat) (Nat.le_refl _)
  refine kstep hS hL (src := .slot Impl.SlhDsa.X86_64.Shake.fMsg) (len := .slot Impl.SlhDsa.X86_64.Shake.fLen)
    (pos := .ret) (N := L.len.toNat) (q := ((L.n * (0 + 1 + 1 + 1) + 2) % 136 + L.ctxLen.toNat) % 136)
    (by show 56 + 8 ≤ 72; omega) (by show 48 + 8 ≤ 72; omega) trivial (by simp [verifyArgLists])
    (Nat.mod_lt _ (by decide)) (by have := L.len.isLt; omega) i6 d6 k6 (fun t ht => by
      obtain ⟨⟨g, m₀, hc⟩, hx⟩ := ht.elim id id
      exact ⟨g, m₀, hc, by simp only [argVal, Impl.SlhDsa.X86_64.Shake.fMsg, hc.rsp]; exact hc.pMsg,
        by simp only [argVal, Impl.SlhDsa.X86_64.Shake.fLen, hc.rsp]; rw [hc.pLen, BitVec.ofNat_toNat,
          BitVec.setWidth_eq],
        by simp only [argVal]; rw [← hx, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩) ?_
  -- pad and squeeze
  have hp' : ∀ t, CR L ((((L.n * (0 + 1 + 1 + 1) + 2) % 136 + L.ctxLen.toNat) % 136 + L.len.toNat) % 136) t →
      WP isa (kpad .ret) t (CC L) := fun t ⟨⟨g, m₀, hc⟩, hx⟩ =>
    WP.mono (kpad_ok hL hc (pos := .ret)
      (q := (((L.n * (0 + 1 + 1 + 1) + 2) % 136 + L.ctxLen.toNat) % 136 + L.len.toNat) % 136) trivial
      (by simp only [argVal]; rw [← hx, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]) (Nat.mod_lt _ (by decide))) fun t' ⟨hc', _⟩ => ⟨g, m₀, hc'⟩
  refine Levels.relSeq (B₁ := CC L) (B₂ := CC L) (kpad_ct hS hL (pos := .ret)
    (q := (((L.n * (0 + 1 + 1 + 1) + 2) % 136 + L.ctxLen.toNat) % 136 + L.len.toNat) % 136) trivial
    (by simp [verifyArgLists])
    (Nat.mod_lt _ (by decide)) fun t ht => by
      obtain ⟨⟨g, m₀, hc⟩, hx⟩ := ht.elim id id
      exact ⟨g, m₀, hc, by simp only [argVal]; rw [← hx, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩) hp' hp' ?_
  exact ksqz_ct hS hL fun t ht => ht.elim id id

end VG.Proof.SlhDsa.X86_64.VerifyTop
