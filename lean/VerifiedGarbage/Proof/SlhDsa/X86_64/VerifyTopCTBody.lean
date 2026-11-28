module

-- separate module: the body's constant-time proof, kept apart from the top level's parsing of the contract

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopCT
public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopMain
public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkForsCT
public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkXmssCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCT
import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopIdx
import VerifiedGarbage.Proof.SlhDsa.X86_64.KeyGen

/-!
# SLH-DSA (SHAKE) on x86-64, `verify`: the frame's body in constant time

Untrusted: everything here is checked by Lean. Two runs of `verifyBody` from
the frame's push (`Pushed`), with the same layout and the same inputs (`Inp`),
leak the same (`body_ct`): each part leaks only the layout and values the
inputs determine, which the runs' correctness (`VerifyTopMain`) gives.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.VerifyTop

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Impl.SlhDsa.X86_64.Shake (treeLanes stk)
open VG.Impl.SlhDsa.X86_64.Verify (vvar vParseIdx fVSig forsPk xmssPk layerBody)
open VG.Proof.Sha3.X86_64 (wp_mov32i)

variable {L : VL}

/-- Two runs' inputs agree. -/
structure Inp (L : VL) (m₁ m₂ : Mem) : Prop where
  seed : bytesAt m₁ L.pk L.n = bytesAt m₂ L.pk L.n
  root : bytesAt m₁ (L.pk + BitVec.ofNat 64 L.n) L.n = bytesAt m₂ (L.pk + BitVec.ofNat 64 L.n) L.n
  msg : bytesAt m₁ L.msg L.len.toNat = bytesAt m₂ L.msg L.len.toNat
  ctx : bytesAt m₁ L.ctx L.ctxLen.toNat = bytesAt m₂ L.ctx L.ctxLen.toNat
  sig : bytesAt m₁ L.sig L.sigL = bytesAt m₂ L.sig L.sigL

/-- The indices and FORS's public key of a run. -/
abbrev vT (p : Params) (L : VL) (m : Mem) : Nat := (splitDigest p (vDigest p L m)).2.1
abbrev vLf (p : Params) (L : VL) (m : Mem) : Nat := (splitDigest p (vDigest p L m)).2.2
abbrev vF (p : Params) (L : VL) (m : Mem) : List Byte :=
  forsPkFromSig p (bytesAt m (L.sig + BitVec.ofNat 64 p.n) p.forsSigLen) (splitDigest p (vDigest p L m)).1
    (bytesAt m L.pk L.n) (forsAdrs (Proof.SlhDsa.layerTree 0 (vT p L m)) (vLf p L m))

section
variable {m₁ m₂ : Mem} (hI : Inp L m₁ m₂)
include hI

theorem Inp.sub {o k : Nat} (hk : o + k ≤ L.sigL) :
    bytesAt m₁ (L.sig + BitVec.ofNat 64 o) k = bytesAt m₂ (L.sig + BitVec.ofNat 64 o) k := by
  rw [← bytesAt_drop_take _ _ hk, ← bytesAt_drop_take _ _ hk, hI.sig]

theorem Inp.hIn (hsl : L.n ≤ L.sigL) : hIn L m₁ = hIn L m₂ := by
  have e := hI.sub (o := 0) (k := L.n) (by omega)
  have z : L.sig + BitVec.ofNat 64 0 = L.sig := BitVec.add_zero _
  rw [z] at e
  simp only [VerifyTop.hIn, e, hI.seed, hI.root, hI.ctx, hI.msg]

theorem Inp.vDigest {p : Params} (hsl : L.n ≤ L.sigL) : vDigest p L m₁ = vDigest p L m₂ := by
  simp only [VerifyTop.vDigest, hI.hIn hsl]

theorem Inp.vT {p : Params} (hsl : L.n ≤ L.sigL) : vT p L m₁ = vT p L m₂ := by
  simp only [VerifyTop.vT, hI.vDigest hsl]

theorem Inp.vLf {p : Params} (hsl : L.n ≤ L.sigL) : vLf p L m₁ = vLf p L m₂ := by
  simp only [VerifyTop.vLf, hI.vDigest hsl]

theorem Inp.vF {p : Params} (hsl : L.n ≤ L.sigL) (hsl2 : p.n + p.forsSigLen ≤ L.sigL) : vF p L m₁ = vF p L m₂ := by
  simp only [VerifyTop.vF, hI.vT hsl, hI.vLf hsl, hI.vDigest hsl, hI.sub hsl2, hI.seed]

theorem Inp.sigHt {p : Params} (hp : VPar p) (hsl : L.sigL = p.sigLen) : sigHt p L m₁ = sigHt p L m₂ :=
  hI.sub (by rw [hsl, hp.sigLen])

theorem Inp.vOk {p : Params} (hp : VPar p) (hn : L.n = p.n) (hsl : L.sigL = p.sigLen) : vOk p L m₁ = vOk p L m₂ := by
  have hsl1 : L.n ≤ L.sigL := by rw [hsl, hp.sigLen, hn]; omega
  have hsl2 : p.n + p.forsSigLen ≤ L.sigL := by rw [hsl, hp.sigLen]; omega
  simp only [VerifyTop.vOk, hI.vDigest hsl1, hI.sub hsl2, hI.seed, hI.root, hI.sigHt hp hsl]

end

theorem split_tree_lt {p : Params} (hp : VPar p) (D : List Byte) : (splitDigest p D).2.1 < 2 ^ 64 := by
  have h := Nat.mod_lt (toInt ((D.drop p.mdLen).take p.treeIdxLen) p.treeIdxLen)
    (Nat.pow_pos (n := p.h - p.h / p.d) (show 0 < 2 by decide))
  have := hp.tb; have := hp.tb'
  exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega))

theorem split_leaf_lt {p : Params} (hp : VPar p) (D : List Byte) : (splitDigest p D).2.2 < 2 ^ p.hp := by
  unfold splitDigest
  rw [← hp.hd]
  exact Nat.mod_lt _ (Nat.pow_pos (by decide))

/-! ## `forsPk` -/

/-- After the indices: the state `b2_ok` gives, from a digest of the run's. -/
abbrev B2' (p : Params) (L : VL) (g : Reg → BitVec 64) (m : Mem) (t : State) : Prop :=
  ∃ t₀, bytesAt t₀.mem (at' L.S Layout.oDigest) p.m = vDigest p L m ∧ B2Post p L g m t₀ t

/-- After `forsPk`. -/
abbrev F3 (p : Params) (L : VL) (g : Reg → BitVec 64) (m : Mem) (t : State) : Prop :=
  Ctx L g m t ∧ t.mem.readW (L.var 0) 64 = BitVec.ofNat 64 (vT p L m) ∧
    t.mem.readW (L.var 1) 64 = BitVec.ofNat 64 (vLf p L m) ∧ bytesAt t.mem (at' L.S Layout.oMsg) p.n = vF p L m

theorem leaf32 {p : Params} (hp : VPar p) (m : Mem) (S : Addr) : dLeaf p m S < 2 ^ 32 :=
  Nat.lt_of_lt_of_le (dLeaf_lt hp m S) (Nat.pow_le_pow_right (by decide) (by have := hp.hp9; omega))

theorem fors3_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hp : VPar p) (hmx : (forsPk p f).allInstrs (fun i => !loadsMxcsr i) = true) (hsp : NoSp (forsPk p f))
    (hst : T.stack + 16 ≤ L.st) (hL : L.Ok) (hn : L.n = p.n) (hsl : p.n + p.forsSigLen ≤ L.sigL) (name : String)
    {g : Reg → BitVec 64} {m : Mem} {t : State} (hb : B2' p L g m t) :
    WP isa (.call name (forsPk p f)) t (F3 p L g m) := by
  obtain ⟨t₀, hd, hb⟩ := hb
  refine WP.mono (forsCall_ok T ht hp hmx hsp hst hL hn hsl hb.ctx hb.adr (leaf32 hp _ _) hb.rdi hb.rsi hb.rdx name)
    fun t' ⟨hc', hv', hmsg⟩ => ⟨hc', ?_, ?_, ?_⟩
  · rw [hv' 0 (by omega), hb.v0]; simp only [dTree]; rw [hd]
  · rw [hv' 1 (by omega), hb.v1]; simp only [dLeaf]; rw [hd]
  · rw [hmsg, mdAt_eq hp, hb.dg]; simp only [dTree, dLeaf]; rw [hd]

theorem fors_ct {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hp : VPar p) (hmx : (forsPk p f).allInstrs (fun i => !loadsMxcsr i) = true)
    (hst : T.stack + 16 ≤ L.st) (hL : L.Ok) (hn : L.n = p.n) (hsl : L.sigL = p.sigLen) (name : String)
    {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem} (hI : Inp L m₁ m₂) :
    RelCT isa (fun a b => B2' p L g₁ m₁ a ∧ B2' p L g₂ m₂ b) (.call name (forsPk p f)) fun _ _ => True := by
  have hsl1 : L.n ≤ L.sigL := by rw [hsl, hp.sigLen, hn]; omega
  have hsl2 : p.n + p.forsSigLen ≤ L.sigL := by rw [hsl, hp.sigLen]; omega
  have hv := ForsCT.forsPk_verified hp.p6 hp.fam T ht (stack := L.st) hst (by have := hL.st62; omega) hmx
  refine RelCT.call hv.1 hv.2.1 [⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩] [⟨L.S, scratchLen⟩, ⟨L.S, 0⟩]
    fun s₁ s₂ ⟨⟨t₁, hd₁, hb₁⟩, ⟨t₂, hd₂, hb₂⟩⟩ => ?_
  obtain ⟨p₁, c₁, w₁⟩ := fors_pre hp hL hn hsl2 hb₁.ctx hb₁.adr (leaf32 hp _ _) hb₁.rdi hb₁.rsi hb₁.rdx
  obtain ⟨p₂, c₂, w₂⟩ := fors_pre hp hL hn hsl2 hb₂.ctx hb₂.adr (leaf32 hp _ _) hb₂.rdi hb₂.rsi hb₂.rdx
  have eL : dLeaf p t₁.mem L.S = dLeaf p t₂.mem L.S := by
    simp only [dLeaf]; rw [hd₁, hd₂, hI.vDigest hsl1]
  have hmd : p.mdLen + 2 ≤ p.m := by have := hp.m; have := hp.ti7; omega
  have hmd' : Layout.oDigest + (p.mdLen + 2) ≤ 65536 := by
    have := hp.m64; rw [show Layout.oDigest = 30304 from rfl]; omega
  refine ⟨p₁, p₂, ?_, c₁, w₁, c₂, w₂, by rw [hb₁.ctx.rsp, hb₂.ctx.rsp]⟩
  simp only [forsPkContract, ce_reg _ _ _ (show Reg.rdi ≠ .rsp by decide),
    ce_reg _ _ _ (show Reg.rsi ≠ .rsp by decide), ce_reg _ _ _ (show Reg.rdx ≠ .rsp by decide), ce_rsp,
    hb₁.rdi, hb₂.rdi, hb₁.rsi, hb₂.rsi, hb₁.rdx, hb₂.rdx, eL, hb₁.ctx.rsp, hb₂.ctx.rsp, true_and]
  refine ⟨?_, ?_⟩
  · rw [ce_sig hL hb₁.ctx _ _ hsl2, ce_sig hL hb₂.ctx _ _ hsl2, hI.sub hsl2]
  · rw [ce_scr hL hb₁.ctx _ _ hmd', ce_scr hL hb₂.ctx _ _ hmd', ← bytesAt_take' _ _ hmd, ← bytesAt_take' _ _ hmd,
      hb₁.dg, hb₂.dg, hd₁, hd₂, hI.vDigest hsl1]

/-! ## The layers -/

/-- Before layer `j` of a run. -/
abbrev LIv (p : Params) (L : VL) (g : Reg → BitVec 64) (m : Mem) (j : Nat) (t : State) : Prop :=
  LI p L g m (vF p L m) (vT p L m) (vLf p L m) j t

/-- Layer `j`'s first block's state, from its start `t₀`. -/
abbrev LB' (p : Params) (L : VL) (g : Reg → BitVec 64) (m : Mem) (j : Nat) (t : State) : Prop :=
  ∃ t₀, LIv p L g m j t₀ ∧ LB1Post p L g m (vF p L m) (vT p L m) (vLf p L m) j t₀ t

theorem xmss_ct {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hp : VPar p) (hst : T.stack + 16 ≤ L.st) (hL : L.Ok) (hn : L.n = p.n) (hsl : L.sigL = p.sigLen) (name : String)
    {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem} (hI : Inp L m₁ m₂) {j : Nat} (hj : j < p.d) :
    RelCT isa (fun a b => LB' p L g₁ m₁ j a ∧ LB' p L g₂ m₂ j b) (.call name (xmssPk p f)) fun _ _ => True := by
  have hsl1 : L.n ≤ L.sigL := by rw [hsl, hp.sigLen, hn]; omega
  have hsl2 : p.n + p.forsSigLen ≤ L.sigL := by rw [hsl, hp.sigLen]; omega
  have hsl' : p.n + p.forsSigLen + j * p.xmssSigLen + p.xmssSigLen ≤ L.sigL := by
    rw [hsl, hp.sigLen]
    have := Nat.mul_le_mul_right p.xmssSigLen (show j + 1 ≤ p.d by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  have hv := XmssCT.xmssPk_verified T ht hp.n hp.fam hp.w4 hp.hp1 (by have := hp.hp9; omega) (stack := L.st) hst
    (by have := hL.st62; omega) T.nomx
  have hF : htFold p (vF p L m₁) (sigHt p L m₁) (bytesAt m₁ L.pk L.n) (vT p L m₁) (vLf p L m₁) j =
      htFold p (vF p L m₂) (sigHt p L m₂) (bytesAt m₂ L.pk L.n) (vT p L m₂) (vLf p L m₂) j := by
    rw [hI.vF hsl1 hsl2, hI.sigHt hp hsl, hI.seed, hI.vT hsl1, hI.vLf hsl1]
  have hlf : ∀ m : Mem, (htFold p (vF p L m) (sigHt p L m) (bytesAt m L.pk L.n) (vT p L m) (vLf p L m) j).2.2 <
      2 ^ p.hp := fun m => htFold_leaf p _ _ _ _ _ (split_leaf_lt hp _) j
  refine RelCT.call hv.1 hv.2.1 [⟨L.sig + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen), p.xmssSigLen⟩]
    [⟨L.S, scratchLen⟩, ⟨L.S, 0⟩] fun s₁ s₂ ⟨⟨t₁, hI₁, hb₁⟩, ⟨t₂, hI₂, hb₂⟩⟩ => ?_
  obtain ⟨p₁, c₁, w₁⟩ := xmss_pre hp hL hn hsl' hb₁.ctx hb₁.adr (hlf m₁) hb₁.rdi hb₁.rsi hb₁.rdx
  obtain ⟨p₂, c₂, w₂⟩ := xmss_pre hp hL hn hsl' hb₂.ctx hb₂.adr (hlf m₂) hb₂.rdi hb₂.rsi hb₂.rdx
  have hmo : Layout.oMsg + p.n ≤ 65536 := by have := hp.n; rw [show Layout.oMsg = 30496 from rfl]; omega
  refine ⟨p₁, p₂, ?_, c₁, w₁, c₂, w₂, by rw [hb₁.ctx.rsp, hb₂.ctx.rsp]⟩
  simp only [xmssPkContract, ce_reg _ _ _ (show Reg.rdi ≠ .rsp by decide),
    ce_reg _ _ _ (show Reg.rsi ≠ .rsp by decide), ce_reg _ _ _ (show Reg.rdx ≠ .rsp by decide), ce_rsp,
    hb₁.rdi, hb₂.rdi, hb₁.rsi, hb₂.rsi, hb₁.rdx, hb₂.rdx, hF, hb₁.ctx.rsp, hb₂.ctx.rsp, true_and]
  refine ⟨?_, ?_⟩
  · rw [ce_sig hL hb₁.ctx _ _ hsl', ce_sig hL hb₂.ctx _ _ hsl', hI.sub hsl']
  · rw [ce_scr hL hb₁.ctx _ _ hmo, ce_scr hL hb₂.ctx _ _ hmo, hb₁.msg, hb₂.msg, hI₁.msg, hI₂.msg, hF]

theorem rbx_of {P₁ P₂ : State → Prop} (h₁ : ∀ x, P₁ x → x.gpr .rbx = L.S) (h₂ : ∀ x, P₂ x → x.gpr .rbx = L.S) :
    ∀ x y, P₁ x ∧ P₂ y → ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r := fun x y ⟨hx, hy⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁ x hx, h₂ y hy]

theorem rsp_rbx_of {P₁ P₂ : State → Prop} (h₁ : ∀ x, P₁ x → CC L x) (h₂ : ∀ x, P₂ x → CC L x) :
    ∀ x y, P₁ x ∧ P₂ y → ∀ r ∈ [Reg.rsp, .rbx], x.gpr r = y.gpr r := fun x y ⟨hx, hy⟩ r hr => by
  obtain ⟨_, _, cx⟩ := h₁ x hx
  obtain ⟨_, _, cy⟩ := h₂ y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [cx.rsp, cy.rsp]
  · rw [cx.rbx, cy.rbx]

theorem layer_ct {p : Params} (hS : S6 p) {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n)
    (ht : f.t4 = T.code) (hst : T.stack + 16 ≤ L.st) (hL : L.Ok) (hn : L.n = p.n) (hsl : L.sigL = p.sigLen)
    (gv : Impl.SlhDsa.X86_64.Verify.VFns) {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem} (hI : Inp L m₁ m₂) {j : Nat}
    (hj : j < p.d) :
    RelCT isa (fun a b => LIv p L g₁ m₁ j a ∧ LIv p L g₂ m₂ j b) (layerBody p f gv) fun _ _ => True := by
  have hp := hS.par
  have hsl' : p.n + p.forsSigLen + j * p.xmssSigLen + p.xmssSigLen ≤ L.sigL := by
    rw [hsl, hp.sigLen]
    have := Nat.mul_le_mul_right p.xmssSigLen (show j + 1 ≤ p.d by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  unfold layerBody
  refine Levels.relSeq (B₁ := LB' p L g₁ m₁ j) (B₂ := LB' p L g₂ m₂ j)
    (ct_lb1 hS (rbx_of (fun x h => h.ctx.rbx) fun x h => h.ctx.rbx))
    (fun a h => WP.mono (lb1_ok hp hL hn (split_tree_lt hp _) hj h) fun t ht => ⟨a, h, ht⟩)
    (fun a h => WP.mono (lb1_ok hp hL hn (split_tree_lt hp _) hj h) fun t ht => ⟨a, h, ht⟩) ?_
  have hw : ∀ {g m} (a : State), LB' p L g m j a → WP isa (.call gv.xmssPkName (xmssPk p f)) a (CC L) :=
    fun a ⟨_, _, hb⟩ => WP.mono (xmssCall_ok T ht hp hst hL hn hsl' hb.ctx hb.adr
      (htFold_leaf p _ _ _ _ _ (split_leaf_lt hp _) j) hb.rdi hb.rsi hb.rdx gv.xmssPkName) fun t' h => ⟨_, _, h.1⟩
  exact Levels.relSeq (B₁ := CC L) (B₂ := CC L) (xmss_ct T ht hp hst hL hn hsl gv.xmssPkName hI hj) hw hw
    (ct_lb2 hS (rbx_of (fun x ⟨_, _, h⟩ => h.rbx) fun x ⟨_, _, h⟩ => h.rbx))

theorem loop_ct {p : Params} (hS : S6 p) {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n)
    (ht : f.t4 = T.code) (hst : T.stack + 16 ≤ L.st) (hL : L.Ok) (hn : L.n = p.n) (hsl : L.sigL = p.sigLen)
    (gv : Impl.SlhDsa.X86_64.Verify.VFns) {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem} (hI : Inp L m₁ m₂) :
    RelCT isa (fun a b => LIv p L g₁ m₁ 0 a ∧ LIv p L g₂ m₂ 0 b) (.loop (layerBody p f gv) .ne)
      fun a b => LIv p L g₁ m₁ p.d a ∧ LIv p L g₂ m₂ p.d b := by
  have hp := hS.par
  have hd := hp.d1
  have hstep : ∀ {g m} (n : Nat) (s : State), n ≤ p.d ∧ 0 < n ∧ LIv p L g m (p.d - n) s →
      WP isa (layerBody p f gv) s fun s' => isa.eval .ne s' = some (decide (p.d - n + 1 ≠ p.d)) ∧
        (decide (p.d - n + 1 ≠ p.d) = false → LIv p L g m p.d s') ∧
        (decide (p.d - n + 1 ≠ p.d) = true → n - 1 < n ∧
          (n - 1 ≤ p.d ∧ 0 < n - 1 ∧ LIv p L g m (p.d - (n - 1)) s')) := fun n s ⟨h1, h2, hI'⟩ =>
    WP.mono (layer_ok T ht hp hst hL hn hsl gv (split_tree_lt hp _) (split_leaf_lt hp _) (j := p.d - n) (by omega) hI')
      fun s' ⟨hne, hI''⟩ => ⟨hne, fun hf => by
        simp only [decide_eq_false_iff_not, Decidable.not_not] at hf; rw [hf] at hI''; exact hI'',
        fun ht' => by
          simp only [decide_eq_true_eq] at ht'
          refine ⟨by omega, by omega, by omega, ?_⟩
          rw [show p.d - (n - 1) = p.d - n + 1 by omega]; exact hI''⟩
  refine RelCT.mono (Levels.relLoop (I₁ := fun n s => n ≤ p.d ∧ 0 < n ∧ LIv p L g₁ m₁ (p.d - n) s)
    (I₂ := fun n s => n ≤ p.d ∧ 0 < n ∧ LIv p L g₂ m₂ (p.d - n) s) (Q₁ := LIv p L g₁ m₁ p.d)
    (Q₂ := LIv p L g₂ m₂ p.d) (fun n => decide (p.d - n + 1 ≠ p.d)) (fun n => n - 1)
    (fun n s₁ s₂ t₁ t₂ s₁' s₂' h e₁ e₂ => layer_ct hS T ht hst hL hn hsl gv hI (j := p.d - n)
      (by have := h.1.2.1; omega) s₁ s₂ t₁ t₂ s₁' s₂' ⟨h.1.2.2, h.2.2.2⟩ e₁ e₂) hstep hstep p.d)
    (fun a b ⟨ha, hb⟩ => ⟨⟨Nat.le_refl _, hd, by rw [Nat.sub_self]; exact ha⟩,
      ⟨Nat.le_refl _, hd, by rw [Nat.sub_self]; exact hb⟩⟩) fun _ _ h => h

/-! ## The comparison and the result -/

theorem cmp_eq {p : Params} (hn : L.n = p.n) {g : Reg → BitVec 64} {m : Mem} {t : State} (h : LIv p L g m p.d t) :
    decide (bytesAt t.mem (at' L.S Layout.oMsg) p.n = bytesAt t.mem (at' L.S Layout.oPkRoot) p.n) = vOk p L m := by
  rw [h.msg, show p.n = L.n from hn.symm, h.ctx.kRoot]
  simp only [vOk, vF, vT, vLf, vDigest, hn]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq]

theorem ite_rbx {t : State} (b : Bool) (hz : t.zf = some b) (hb : t.gpr .rbx = L.S) :
    WP isa (.ite .e (.block [.mov32 .rax (.imm 1)]) (.block [.mov32 .rax (.imm 0)])) t
      fun u => u.gpr .rbx = L.S :=
  WP.ite b hz (fun _ => wp_mov32i fun u e => WP.block_nil (by rw [e.other _ (by decide), hb]))
    fun _ => wp_mov32i fun u e => WP.block_nil (by rw [e.other _ (by decide), hb])

theorem tail_ct {p : Params} (hS : S6 p) (hn : L.n = p.n) (hsl : L.sigL = p.sigLen)
    {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem} (hI : Inp L m₁ m₂) :
    RelCT isa (fun a b => LIv p L g₁ m₁ p.d a ∧ LIv p L g₂ m₂ p.d b)
      (.seq (.block (.mov32 .rax (.imm 0) :: (List.range (p.n / 8)).flatMap (fun w =>
          [.mov .rcx (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oMsg + 8 * w))),
            .alu .xor .rcx (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oPkRoot + 8 * w))),
            .alu .or .rax (.reg .rcx)]) ++ ([.alu .test .rax (.reg .rax)] : List Instr)))
        (.seq (.ite .e (.block [.mov32 .rax (.imm 1)]) (.block [.mov32 .rax (.imm 0)]))
          (.block (.mov .r10 (.reg .rax) :: Impl.SlhDsa.X86_64.Shake.kgRestore ++ ([.mov .rax (.reg .r10)] : List Instr)))))
      fun _ _ => True := by
  have hp := hS.par
  refine Levels.relSeq (B₁ := fun t => t.gpr .rbx = L.S ∧ t.zf = some (vOk p L m₁))
    (B₂ := fun t => t.gpr .rbx = L.S ∧ t.zf = some (vOk p L m₂))
    (ct_cmp hS (rbx_of (fun x h => h.ctx.rbx) fun x h => h.ctx.rbx))
    (fun a h => WP.mono (cmp_ok hp h.ctx) fun t' ⟨hc, hz⟩ => ⟨hc.rbx, by rw [hz, cmp_eq hn h]⟩)
    (fun a h => WP.mono (cmp_ok hp h.ctx) fun t' ⟨hc, hz⟩ => ⟨hc.rbx, by rw [hz, cmp_eq hn h]⟩) ?_
  refine Levels.relSeq (B₁ := fun u => u.gpr .rbx = L.S) (B₂ := fun u => u.gpr .rbx = L.S)
    (RelCT.ite (fun s₁ s₂ ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩ => by
      show s₁.zf = s₂.zf; rw [h₁, h₂, hI.vOk hp hn hsl]) ct_res1 ct_res0)
    (fun a h => ite_rbx _ h.2 h.1) (fun a h => ite_rbx _ h.2 h.1) (ct_epi (rbx_of (fun _ h => h) fun _ h => h))

/-! ## The body -/

/-- Two runs of the frame's body, from the push, with the same layout and the
same inputs, leak the same. -/
theorem body_ct {p : Params} (hS : S6 p) {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n)
    (ht : f.t4 = T.code) (hmx : (forsPk p f).allInstrs (fun i => !loadsMxcsr i) = true) (hsp : NoSp (forsPk p f))
    (hst : T.stack + 16 ≤ L.st) (hL : L.Ok) (hn : L.n = p.n) (hsl : L.sigL = p.sigLen)
    (gv : Impl.SlhDsa.X86_64.Verify.VFns) {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem} (hI : Inp L m₁ m₂) :
    RelCT isa (fun a b => Pushed L g₁ m₁ a ∧ Pushed L g₂ m₂ b) (Impl.SlhDsa.X86_64.Verify.verifyBody p f gv)
      fun _ _ => True := by
  have hp := hS.par
  have hsl1 : L.n ≤ L.sigL := by rw [hsl, hp.sigLen, hn]; omega
  have hsl2 : p.n + p.forsSigLen ≤ L.sigL := by rw [hsl, hp.sigLen]; omega
  unfold Impl.SlhDsa.X86_64.Verify.verifyBody
  refine Levels.relSeq (ct_pro hS fun x y ⟨hx, hy⟩ => pushed_agree hL hx hy) (fun a h => pro_ok hL hn h)
    (fun a h => pro_ok hL hn h) ?_
  refine Levels.relSeq (hash_ct hS hL hn hsl1 fun t ht => ht.elim (fun h => ⟨_, _, h⟩) fun h => ⟨_, _, h⟩)
    (fun a h => hash_ok hL hn hsl1 hp.m64 h) (fun a h => hash_ok hL hn hsl1 hp.m64 h) ?_
  refine Levels.relSeq (B₁ := B2' p L g₁ m₁) (B₂ := B2' p L g₂ m₂)
    (ct_b2 hS (rsp_rbx_of (fun x h => ⟨_, _, h.1⟩) fun x h => ⟨_, _, h.1⟩))
    (fun a h => WP.mono (b2_ok hp hL hn h.1) fun t ht => ⟨a, h.2, ht⟩)
    (fun a h => WP.mono (b2_ok hp hL hn h.1) fun t ht => ⟨a, h.2, ht⟩) ?_
  refine Levels.relSeq (B₁ := F3 p L g₁ m₁) (B₂ := F3 p L g₂ m₂) (fors_ct T ht hp hmx hst hL hn hsl _ hI)
    (fun a h => fors3_ok T ht hp hmx hsp hst hL hn hsl2 _ h) (fun a h => fors3_ok T ht hp hmx hsp hst hL hn hsl2 _ h) ?_
  refine Levels.relSeq (B₁ := LIv p L g₁ m₁ 0) (B₂ := LIv p L g₂ m₂ 0)
    (ct_b3 hS (rsp_rbx_of (fun x h => ⟨_, _, h.1⟩) fun x h => ⟨_, _, h.1⟩))
    (fun a h => start_ok hp hL h.1 h.2.1 h.2.2.1 h.2.2.2) (fun a h => start_ok hp hL h.1 h.2.1 h.2.2.1 h.2.2.2) ?_
  exact RelCT.seq (loop_ct hS T ht hst hL hn hsl gv hI) (tail_ct hS hn hsl hI)

end VG.Proof.SlhDsa.X86_64.VerifyTop
