module

public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCtBase
public import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedContract
import VerifiedGarbage.Proof.RsaPss.X86_64.PcCVerified
public import VerifiedGarbage.Proof.RsaPss.X86_64.PcChk
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCParams
public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
import VerifiedGarbage.Proof.RsaPss.X86_64.PcCCorrect
import VerifiedGarbage.Proof.RsaPss.X86_64.PcChk
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCCorrect
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCFixed
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyFixed
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyBody
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCall
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCCall
public import VerifiedGarbage.Impl.RsaPss.X86_64.Encoding
public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCtx
public import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedCall

/-!
# RSASSA-PSS verification with cached public-key values on x86-64, around
the check of the encoding: constant time, and `Verified`

The prologue and the check of the modulus' first byte, `emBits` and the
public-key operation's arguments (public: the modulus' length and first
byte, and places), its call (constant time by its contract), `sAcc` and
`checkEncoding`'s arguments (only `sAcc` is secret), its call (constant time
by its contract), the result, and the epilogue, in two runs whose entry
states agree on the public data (`codeC_ct`). With `codeC_correct`,
`verifyC` meets `Spec.RsaPss.verifyPrecomputedContract` (`codeC_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (PublicImpl pdChkContract)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable {G : Spec.Mgf1.Hash} {H : Hash}

/-- The cache's place and words agree too. -/
def extraC (G : Spec.Mgf1.Hash) (a s : State) : Prop :=
  Pre G a ∧ Pre G s ∧ stackArg s 5 = stackArg a 5 ∧ stackArg s 6 = stackArg a 6 ∧
    Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat =
      Spec.Rsa.wordsAt a.mem (stackArg a 5) (stackArg a 6).toNat

abbrev CSib := VSib (extra := extraC G) G
abbrev CAt := VAt (extra := extraC G) G

/-! ## The public values -/

/-- `emBits`. -/
def veb (s : State) : Nat := ebV (s.gpr .rsi).toNat (n0v s)

/-- `emLen`. -/
def vel (s : State) : Nat := Spec.RsaPss.emLength (veb s)

/-- `lo`. -/
def vclo (s : State) : Nat := (s.gpr .rsi).toNat - vel s

/-- The words `emBitsB` stores. -/
def vex (s : State) : List (Nat × BitVec 64) :=
  [(26, BitVec.ofNat 64 (vclo s)), (27, BitVec.ofNat 64 (veb s)), (28, BitVec.ofNat 64 (vel s))]

theorem CSib.veb {a s : State} (S : CSib (G := G) a s) : veb s = veb a := by
  simp only [VG.Proof.RsaPss.X86_64.Pc.veb, S.n0v, S.gpr (r := .rsi) (by decide)]

theorem CSib.vel {a s : State} (S : CSib (G := G) a s) : vel s = vel a := by
  simp only [VG.Proof.RsaPss.X86_64.Pc.vel, S.veb]

theorem CSib.vclo {a s : State} (S : CSib (G := G) a s) : vclo s = vclo a := by
  simp only [VG.Proof.RsaPss.X86_64.Pc.vclo, S.vel, S.gpr (r := .rsi) (by decide)]

theorem CSib.vex {a s : State} (S : CSib (G := G) a s) : vex s = vex a := by
  simp only [VG.Proof.RsaPss.X86_64.Pc.vex, S.veb, S.vel, S.vclo]

theorem CSib.pre {a s : State} (S : CSib (G := G) a s) : Pre G s := S.2.2.2.2.1

theorem veb_ok {s : State} (hp : VPre G s) :
    vclo s ≤ 1 ∧ 1 ≤ veb s ∧ veb s ≤ Proof.RsaPss.maxEmBits ∧ vclo s + vel s = (s.gpr .rsi).toNat := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hl8 : Nat.log2 (n0v s) < 8 := RsaPss.log2_lt8 (s.mem (s.gpr .rdi))
  refine ⟨lo_le hl8 (by omega), ?_, ?_, ?_⟩
  · unfold veb ebV; omega
  · unfold veb ebV Proof.RsaPss.maxEmBits; omega
  · unfold vclo vel veb ebV Spec.RsaPss.emLength; omega

/-! ## The pieces -/

/-- After the frame's push. -/
def J0 (s t : State) : Prop := t = allocState frameBytes s

/-- The words the prologue stores. -/
def K1 : List Nat := [17, 18, 19, 20, 21, 22, 37, 38]

variable (H) in
/-- After the prologue: the modulus' first byte, and ZF set if it is zero. -/
def J1 (s t : State) : Prop :=
  VS H s t K1 [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (vwrR s) s.mem t.mem ∧
    t.gpr .rax = BitVec.ofNat 64 (n0v s) ∧ t.zf = some (decide (n0v s = 0))

variable (H) in
/-- At the end. -/
def JR (s t : State) : Prop := VS H s t [] [] fun _ _ => True

theorem pro_ct : RelCT isa (Two (CAt (G := G) J0)) (.block (verifyPrologue ++ n0)) (Two (CAt (G := G) (J1 H))) := by
  obtain ⟨_, hc⟩ := vFixed.pro
  have ar : ∀ (s : State) {r : Reg}, r ≠ .rsp → (allocState frameBytes s).gpr r = s.gpr r := fun s r hr => by
    rw [allocState_gpr']; exact ifn hr _ _
  refine two_post (two_pub0 1 [.rdi, .rsi, .rdx, .rcx, .r8, .r9] fb State.wr
    (fun a => [(.rdi, a.gpr .rdi), (.rsi, a.gpr .rsi), (.rdx, a.gpr .rdx), (.rcx, a.gpr .rcx), (.r8, a.gpr .r8),
      (.r9, a.gpr .r9)])
    (fun a t ⟨s, S, ht⟩ => ⟨by rw [ht, allocState_gpr', ifp rfl, ← S.fb], by rw [ht, ← S.wr, ← S.fb]; rfl,
      fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> rw [ht, ar s (by decide)] <;>
          exact S.gpr (by decide)⟩)
    (fun a t ⟨s, S, _⟩ => S.rest) (fun _ => rfl) hc) fun a t ⟨s, S, ht⟩ => ?_
  subst ht
  have hp := S.ps
  rw [WP.block_append_iff]
  refine WP.mono (verifyPro_ok hp) fun t1 ⟨k1, L1, R1, f1⟩ => ?_
  have hM1 : Frame (vwrR s) s.mem t1.mem := f1.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vframe_sub s⟩
  refine WP.mono (vn0_ok hp L1 R1 (by simp [vproW, upd]) k1.2.1 hM1) fun t2 ⟨k2, hm2, hax2, hz2⟩ =>
    ⟨s, S, ⟨L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2]), k2.2.2.trans k1.2.2,
      ⟨_, _, hm2 ▸ R1, fun k hk => ?_, trivial⟩, fun _ hp => by cases hp⟩, k2.2.1.trans k1.2.1, hm2 ▸ hM1, hax2, hz2⟩
  simp only [K1, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [vproW, upd, vw]

/-- A refusal. -/
theorem fail_ct {Φ : State → State → Prop}
    (hΦ : ∀ a t, Φ a t → ∃ s ks X, CSib (G := G) a s ∧ VS H s t ks [] X) :
    RelCT isa (Two Φ) verifyFail (Two (CAt (G := G) (JR H))) := by
  obtain ⟨_, hc⟩ := vFixed.fail
  have hv : ∀ a t, Φ a t → ∃ s, CSib (G := G) a s ∧ VS H s t [] [] fun _ _ => True := fun a t h => by
    obtain ⟨s, ks, X, S, v⟩ := hΦ a t h
    exact ⟨s, S, v.sub (fun _ h => by cases h) [] (fun _ hp => by cases hp) fun _ _ _ => trivial⟩
  refine two_post (vtwo (G := G) (H := H) [] [] (fun _ => []) (fun a t h => let ⟨s, S, v⟩ := hv a t h; ⟨s, _, S, v⟩)
    (fun _ => rfl) (by decide) hc) fun a t h => ?_
  obtain ⟨s, S, v⟩ := hv a t h
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem) ?_ rfl) fun t' ⟨hm, k⟩ =>
    ⟨s, S, v.keep k hm (by decide) fun _ hp => by cases hp⟩
  xrun [verifyFail]

theorem restore_ct : RelCT isa (Two (CAt (G := G) (JR H))) (.block restoreRegs) fun _ _ => True := by
  obtain ⟨_, hc⟩ := vFixed.restore
  exact vtwo (G := G) (H := H) [] [] (fun _ => []) (fun a t ⟨s, S, v⟩ => ⟨s, _, S, v⟩) (fun _ => rfl) (by decide) hc

/-- The words `emBitsB` stores, in a run. -/
def EX (s : State) : (Nat → Byte) → (Nat → BitVec 64) → Prop := fun _ W => ∀ p ∈ vex s, W p.1 = p.2

variable (H) in
/-- Before the public-key operation. -/
def JP (s t : State) : Prop :=
  VS H s t K1 [] (EX s) ∧ t.rd = s.rd ∧ Frame (vwrR s) s.mem t.mem ∧
    (∀ i < 4, word t.mem (fb s) (8 * i) = vArg s i) ∧ t.gpr .rdi = stackArg s 3 ∧
    t.gpr .rsi = s.gpr .rsi ∧ t.gpr .rdx = stackArg s 5 ∧ t.gpr .rcx = stackArg s 6 ∧ t.gpr .r8 = s.gpr .rdx ∧
    t.gpr .r9 = s.gpr .rcx

variable (H) in
/-- After it. -/
def JQ (s t : State) : Prop := VS H s t K1 [] (EX s) ∧ t.rd = s.rd ∧ Frame (vwrR s) s.mem t.mem

theorem prep_ct : RelCT isa (Two fun a t => CAt (G := G) (J1 H) a t ∧ isa.eval .e t = some false)
    (.block (emBitsB ++ pubArgsC)) (Two (CAt (G := G) (JP H))) := by
  obtain ⟨_, hc⟩ := vcFixed.prep
  refine two_post (vtwo (G := G) (H := H) [17, 19, 20, 21, 22, 38] [.rax] (fun a => [(.rax, BitVec.ofNat 64 (n0v a))])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.n0v]; exact h.2.2.2.1) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨⟨s, S, h⟩, he⟩ => ?_
  obtain ⟨v, hrd, hM, hax, hz⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := CSib.pre S
  have h0 : n0v s ≠ 0 := fun h0 => by
    have : isa.eval .e t = some true := by rw [show isa.eval .e t = t.zf from rfl, hz, h0]; rfl
    rw [this] at he; cases he
  refine WP.mono (vprep_ok hp v.L R v.wr hrd hM (hw 17 (by decide)) (hw 19 (by decide)) (hw 20 (by decide))
    (hw 22 (by decide)) (hw 38 (by decide)) (x := n0v s) (BitVec.isLt _) h0 hax)
    fun u ⟨L', k', ⟨W', R', ha, hb⟩, di, si, dx, cx, r8, r9, hM'⟩ =>
      ⟨s, S, v.next L' k'.2.2 R' (fun k hk => ?_) (fun p hp => ?_), k'.2.1.trans hrd, hM',
        fun i hi => (R'.fr i (by unfold nW frameBytes; omega)).trans (ha i hi), di, si, dx, cx, r8, r9⟩
  · have hk' := hk
    simp only [K1, List.mem_cons, List.not_mem_nil, or_false] at hk'
    rw [hb k (by unfold nW frameBytes; omega) (by omega), ← hw k hk]
    simp only [vW, upd]
    rw [ifn (by omega), ifn (by omega), ifn (by omega)]
  · simp only [vex, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> dsimp only <;> rw [hb _ (by decide) (by decide)] <;> simp [vW, upd] <;> rfl

/-- An input, at a call, as on entry. -/
theorem centry_bytes {s t : State} (hst : t.gpr .rsp = fb s) (hM : Frame (vwrR s) s.mem t.mem)
    {R : Region} (hK : (vstkR s).Disjoint R) (hS : R.Disjoint (vscrR s)) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.callEntry.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, hst]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have fSE : Frame (vwrR s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vret_sub s⟩)
  exact bytesAt_frame fSE (vin_apart hK hS) hl

theorem centry_pre {a s t : State} (S : CSib (G := G) a s) (hst : t.gpr .rsp = fb s)
    (hM : Frame (vwrR s) s.mem t.mem) :
    Spec.Rsa.wordsAt t.callEntry.mem (stackArg s 5) (stackArg s 6).toNat =
      Spec.Rsa.wordsAt a.mem (stackArg a 5) (stackArg a 6).toNat := by
  have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, hst]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have fSE : Frame (vwrR s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vret_sub s⟩)
  exact (pre_words S.2.2.2.2.1 fSE).trans S.2.2.2.2.2.2.2

theorem centry_e {a s t : State} (S : CSib (G := G) a s) (hst : t.gpr .rsp = fb s)
    (hM : Frame (vwrR s) s.mem t.mem) :
    Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat := by
  have hp := S.ps
  rw [← S.eB]
  exact centry_bytes (R := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩) hst hM hp.dKe hp.des
    (by have := hp.wE; dsimp only; omega)

theorem cvArg_sib {a s : State} (S : CSib (G := G) a s) {i : Nat} : vArg s i = vArg a i := by
  unfold vArg
  split <;> simp only [S.gpr (r := .r9) (by decide), S.gpr (r := .rsi) (by decide), S.arg3, S.arg4]

/-- The public-key operation's public data agree. -/
theorem cpub {a s₁ s₂ t₁ t₂ : State} (S₁ : CSib (G := G) a s₁) (h₁ : JP H s₁ t₁) (S₂ : CSib (G := G) a s₂)
    (h₂ : JP H s₂ t₂) :
    pdChkContract.pub (t₁.callEntry.withRegions (callRd s₁) (cWr s₁))
      (t₂.callEntry.withRegions (callRd s₂) (cWr s₂)) := by
  obtain ⟨v₁, -, hM₁, ha₁, di₁, si₁, dx₁, cx₁, r8₁, r9₁⟩ := h₁
  obtain ⟨v₂, -, hM₂, ha₂, di₂, si₂, dx₂, cx₂, r8₂, r9₂⟩ := h₂
  have p₁ := S₁.ps
  have p₂ := S₂.ps
  have hE₁ : ∀ i < 4, stackArg (t₁.callEntry.withRegions (callRd s₁) (cWr s₁)) i = vArg a i :=
    fun i hi => ((vstackArg_call p₁ v₁.L.rsp _ _ hi).trans (ha₁ i hi)).trans (cvArg_sib S₁)
  have hE₂ : ∀ i < 4, stackArg (t₂.callEntry.withRegions (callRd s₂) (cWr s₂)) i = vArg a i :=
    fun i hi => ((vstackArg_call p₂ v₂.L.rsp _ _ hi).trans (ha₂ i hi)).trans (cvArg_sib S₂)
  have bn₁ := centry_pre S₁ v₁.L.rsp hM₁
  have bn₂ := centry_pre S₂ v₂.L.rsp hM₂
  have be₁ := centry_e S₁ v₁.L.rsp hM₁
  have be₂ := centry_e S₂ v₂.L.rsp hM₂
  have g : ∀ (t : State) (rd wr : List Region) {r : Reg}, r ≠ .rsp → (t.callEntry.withRegions rd wr).gpr r = t.gpr r :=
    fun t rd wr r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  refine ⟨fun r hr => ?_, by rw [hE₁ 0 (by decide), hE₂ 0 (by decide)], by rw [hE₁ 1 (by decide), hE₂ 1 (by decide)],
    by rw [hE₁ 2 (by decide), hE₂ 2 (by decide)], by rw [hE₁ 3 (by decide), hE₂ 3 (by decide)], ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), di₁, di₂, S₁.arg3, S₂.arg3]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), si₁, si₂, S₁.gpr (r := .rsi) (by decide),
        S₂.gpr (r := .rsi) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), dx₁, dx₂, S₁.2.2.2.2.2.1, S₂.2.2.2.2.2.1]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), cx₁, cx₂, S₁.2.2.2.2.2.2.1, S₂.2.2.2.2.2.2.1]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), r8₁, r8₂, S₁.gpr (r := .rdx) (by decide),
        S₂.gpr (r := .rdx) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), r9₁, r9₂, S₁.gpr (r := .rcx) (by decide),
        S₂.gpr (r := .rcx) (by decide)]
    · rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, v₁.L.rsp,
        v₂.L.rsp, S₁.fb, S₂.fb]
  · rw [State.withRegions_mem, State.withRegions_mem, g _ _ _ (by decide), g _ _ _ (by decide),
      g _ _ _ (by decide), g _ _ _ (by decide), dx₁, dx₂, cx₁, cx₂, bn₁, bn₂]
  · rw [State.withRegions_mem, State.withRegions_mem, g _ _ _ (by decide), g _ _ _ (by decide),
      g _ _ _ (by decide), g _ _ _ (by decide), r8₁, r8₂, r9₁, r9₂, be₁, be₂]

theorem pcall_ct (impl : PublicImpl) :
    RelCT isa (Two (CAt (G := G) (JP H))) (.call impl.name impl.code) (Two (CAt (G := G) (JQ H))) := by
  refine two_post (RelCT.callEx (k := pdChkContract) impl.ok impl.ct fun t₁ t₂ ⟨a, ⟨s₁, S₁, h₁⟩, ⟨s₂, S₂, h₂⟩⟩ => ?_)
    fun a t ⟨s, S, h⟩ => ?_
  · have hpub := cpub S₁ h₁ S₂ h₂
    obtain ⟨c₁, w₁⟩ := call_covers (CSib.pre S₁) h₁.2.1 h₁.1.wr
    obtain ⟨c₂, w₂⟩ := call_covers (CSib.pre S₂) h₂.2.1 h₂.1.wr
    obtain ⟨v₁, -, -, a₁, di₁, si₁, dx₁, cx₁, r8₁, r9₁⟩ := h₁
    obtain ⟨v₂, -, -, a₂, di₂, si₂, dx₂, cx₂, r8₂, r9₂⟩ := h₂
    exact ⟨_, _, _, _, call_pre (CSib.pre S₁) v₁.L.rsp a₁ di₁ si₁ dx₁ cx₁ r8₁ r9₁,
      call_pre (CSib.pre S₂) v₂.L.rsp a₂ di₂ si₂ dx₂ cx₂ r8₂ r9₂, hpub, c₁, w₁, c₂, w₂,
      by rw [v₁.L.rsp, v₂.L.rsp, S₁.fb, S₂.fb]⟩
  · obtain ⟨v, hrd, hM, ha, di, si, dx, cx, r8, r9⟩ := h
    obtain ⟨V, W, R, hw, hx⟩ := v.W
    have hp := CSib.pre S
    have hk2 := hp.k2
    refine WP.mono (call_ok impl hp v.L.rsp hrd v.wr hM ha di si dx cx r8 r9)
      fun u ⟨rd', wr', cs', _, hM', hk', _⟩ => ?_
    have R' := R.of_call v.L.geo (m' := u.mem) (rgs := [(0, (s.gpr .rsi).toNat)]) (fun x hx hin => hk' x (by
        rcases hin with hin | hin
        · refine .inr ⟨hin, ?_⟩
          have := hx _ (List.mem_singleton_self _)
          rwa [off_zero] at this
        · exact .inl hin)) (by
        intro p hp'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
        subst hp'; dsimp only; unfold oRsa; omega)
    exact ⟨s, S, v.next (v.L.of_rep' R R' rfl (cs' .rsp (by decide)) wr') wr' R' hw hx, rd'.trans hrd, hM'⟩

variable (H) in
/-- Before `checkEncoding`. -/
def JK (s t : State) : Prop :=
  VS H s t [] [] (fun _ W => W 0 = off (stackArg s 3) (8 * kw (s.gpr .rsi).toNat) ∧
    W 1 = stackArg s 4 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)) ∧ t.rd = s.rd ∧ Frame (vwrR s) s.mem t.mem ∧
    t.gpr .rdi = s.gpr .r8 ∧ t.gpr .rsi = off (stackArg s 3) (vclo s) ∧ t.gpr .rdx = BitVec.ofNat 64 (vel s) ∧
    t.gpr .rcx = BitVec.ofNat 64 (veb s) ∧ t.gpr .r8 = stackArg s 1 ∧ t.gpr .r9 = stackArg s 2

theorem cargs_ct : RelCT isa (Two (CAt (G := G) (JQ H))) (.block chkArgs) (Two (CAt (G := G) (JK H))) := by
  obtain ⟨_, hc⟩ := vcFixed.chkArgs
  refine two_post (vtwoX (G := G) (H := H) (extra := extraC G) id [17, 21, 22, 37] vex [26, 27, 28] [] (fun _ => [])
    (fun a t ⟨s, S, h⟩ => ⟨s, S, h.1.sub (by decide) [] (fun _ hp => by cases hp)
      fun _ _ x => by rw [← CSib.vex S]; exact x⟩)
    (fun _ => rfl) (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM⟩ := h
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hp := CSib.pre S
  obtain ⟨hlo, -, -, -⟩ := veb_ok hp.toVPre
  refine WP.mono (chkArgs_ok hp v.L R v.wr hrd hM (lo := vclo s) (el := vel s) (eb := veb s) (hw 17 (by decide))
    (hw 22 (by decide)) (hx (26, BitVec.ofNat 64 (vclo s)) (by simp [vex]))
    (hx (27, BitVec.ofNat 64 (veb s)) (by simp [vex])) (hx (28, BitVec.ofNat 64 (vel s)) (by simp [vex]))
    (hw 37 (by decide)) hlo)
    fun u ⟨L', k', R', hM', di, si, dx, cx, r8, r9⟩ =>
      ⟨s, S, v.next L' k'.2.2 R' (fun _ h => by cases h) ⟨by simp [chkW, upd], by simp [chkW, upd]⟩,
        k'.2.1.trans hrd, hM', di, si, dx, cx, r8, r9⟩

variable {chkN : String} {chkC : Prog isa}
  (hvK : ∀ s, (chkK G).pre s → ∃ t s', Exec isa chkC s t s' ∧ abiPreserved s s' ∧ (chkK G).post s s')
  (hctK : ConstantTime isa (chkK G).pre (chkK G).pub chkC) (hspK : SpSafe chkC)
  (hdK : chkC.x86_64Depth ≤ chkStack)

include hvK hctK hspK hdK in
theorem kcall_ct : RelCT isa (Two (CAt (G := G) (JK H))) (.call chkN chkC) (Two (CAt (G := G) (JR H))) := by
  have g : ∀ (t : State) (rd wr : List Region) {r : Reg}, r ≠ .rsp →
      (t.callEntry.withRegions rd wr).gpr r = t.gpr r :=
    fun t rd wr r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  refine two_post (RelCT.callEx (k := chkK G) hvK hctK fun t₁ t₂ ⟨a, ⟨s₁, S₁, h₁⟩, ⟨s₂, S₂, h₂⟩⟩ => ?_)
    fun a t ⟨s, S, h⟩ => ?_
  · obtain ⟨v₁, rd₁, -, di₁, si₁, dx₁, cx₁, r8₁, r9₁⟩ := h₁
    obtain ⟨v₂, rd₂, -, di₂, si₂, dx₂, cx₂, r8₂, r9₂⟩ := h₂
    obtain ⟨V₁, W₁, R₁, -, x₁, y₁⟩ := v₁.W
    obtain ⟨V₂, W₂, R₂, -, x₂, y₂⟩ := v₂.W
    have p₁ := CSib.pre S₁; have p₂ := CSib.pre S₂
    obtain ⟨lo₁, e₁, f₁, l₁⟩ := veb_ok p₁.toVPre
    obtain ⟨lo₂, e₂, f₂, l₂⟩ := veb_ok p₂.toVPre
    obtain ⟨c₁, w₁⟩ := ck_covers p₁ rd₁ v₁.wr (lo := vclo s₁) (el := vel s₁) (by omega)
    obtain ⟨c₂, w₂⟩ := ck_covers p₂ rd₂ v₂.wr (lo := vclo s₂) (el := vel s₂) (by omega)
    have a₀₁ := (R₁.fr 0 (by decide)).trans x₁
    have a₁₁ := (R₁.fr 1 (by decide)).trans y₁
    have a₀₂ := (R₂.fr 0 (by decide)).trans x₂
    have a₁₂ := (R₂.fr 1 (by decide)).trans y₂
    refine ⟨_, _, _, _, ck_pre p₁ v₁.L.rsp a₀₁ a₁₁ di₁ si₁ dx₁ cx₁ (by omega) e₁ f₁ rfl,
      ck_pre p₂ v₂.L.rsp a₀₂ a₁₂ di₂ si₂ dx₂ cx₂ (by omega) e₂ f₂ rfl, ⟨fun r hr => ?_, ?_, ?_, ?_⟩, c₁, w₁, c₂, w₂,
      by rw [v₁.L.rsp, v₂.L.rsp, S₁.fb, S₂.fb]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [g _ _ _ (by decide), g _ _ _ (by decide), di₁, di₂, S₁.gpr (r := .r8) (by decide),
          S₂.gpr (r := .r8) (by decide)]
      · rw [g _ _ _ (by decide), g _ _ _ (by decide), si₁, si₂, S₁.arg3, S₂.arg3, CSib.vclo S₁, CSib.vclo S₂]
      · rw [g _ _ _ (by decide), g _ _ _ (by decide), dx₁, dx₂, CSib.vel S₁, CSib.vel S₂]
      · rw [g _ _ _ (by decide), g _ _ _ (by decide), cx₁, cx₂, CSib.veb S₁, CSib.veb S₂]
      · rw [g _ _ _ (by decide), g _ _ _ (by decide), r8₁, r8₂, S₁.arg1, S₂.arg1]
      · rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, v₁.L.rsp,
          v₂.L.rsp, S₁.fb, S₂.fb]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), r9₁, r9₂, S₁.arg2, S₂.arg2]
    · rw [vstackArg_call p₁.toVPre v₁.L.rsp _ _ (i := 0) (by decide),
        vstackArg_call p₂.toVPre v₂.L.rsp _ _ (i := 0) (by decide), a₀₁, a₀₂, S₁.arg3, S₂.arg3,
        S₁.gpr (r := .rsi) (by decide), S₂.gpr (r := .rsi) (by decide)]
    · rw [vstackArg_call p₁.toVPre v₁.L.rsp _ _ (i := 1) (by decide),
        vstackArg_call p₂.toVPre v₂.L.rsp _ _ (i := 1) (by decide), a₁₁, a₁₂, S₁.arg4, S₂.arg4,
        S₁.gpr (r := .rsi) (by decide), S₂.gpr (r := .rsi) (by decide)]
  · obtain ⟨v, hrd, hM, di, si, dx, cx, r8, r9⟩ := h
    obtain ⟨V, W, R, hw, x0, x1⟩ := v.W
    have hp := CSib.pre S
    obtain ⟨-, e1, e2, l⟩ := veb_ok hp.toVPre
    refine WP.mono (ck_call hvK hspK hdK hp v.L.rsp hrd v.wr hM R ((R.fr 0 (by decide)).trans x0)
      ((R.fr 1 (by decide)).trans x1) di si dx cx r8 r9 (by omega) e1 e2 rfl)
      fun u ⟨rd', wr', cs', _, _, R', _⟩ =>
        ⟨s, S, v.next (v.L.of_rep' R R' rfl (cs' .rsp (by decide)) wr') wr' R' hw trivial⟩

theorem acc_ct : RelCT isa (Two (CAt (G := G) (JR H))) (.block [.alu .and .rax (.mem (sp sAcc))])
    (Two (CAt (G := G) (JR H))) := by
  obtain ⟨_, hc⟩ := vcFixed.acc
  refine two_post (vtwo (G := G) (H := H) [] [] (fun _ => []) (fun a t ⟨s, S, v⟩ => ⟨s, _, S, v⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, v⟩ => ?_
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem) ?_ rfl) fun t' ⟨hm, k⟩ =>
    ⟨s, S, v.keep k hm (by decide) fun _ hp => by cases hp⟩
  xrun [ea_sp, v.L.rsp, v.L.ld (d := sAcc) (by decide)]

include hvK hctK hspK hdK in
theorem cbody_ct (H : Hash) (impl : PublicImpl) :
    RelCT isa (Two (CAt (G := G) J0)) (verifyCBody chkN chkC impl.name impl.code) fun _ _ => True := by
  unfold verifyCBody
  simp only [seqs]
  refine (pro_ct (H := H)).seq ((two_ite (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
      rw [show isa.eval .e t₁ = t₁.zf from rfl, show isa.eval .e t₂ = t₂.zf from rfl, h₁.2.2.2.2, h₂.2.2.2.2,
        S₁.n0v, S₂.n0v])
    (fail_ct (Φ := fun a t => CAt (G := G) (J1 H) a t ∧ isa.eval .e t = some true)
      fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, _, S, h.1⟩)
    (prep_ct.seq ((pcall_ct impl).seq (cargs_ct.seq ((kcall_ct hvK hctK hspK hdK).seq acc_ct))))).seq
    restore_ct)

include hvK hctK hspK hdK in
theorem codeC_ct (H : Hash) (impl : PublicImpl) : ConstantTime isa (contract G).pre (contract G).pub
    (verifyC chkN chkC impl.name impl.code) := by
  apply RelCT.constantTime
  apply valloc
  apply (cbody_ct hvK hctK hspK hdK H impl).mono
  · rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, e₁, e₂⟩
    have p₁ := pre_of G h₁
    have p₂ := pre_of G h₂
    exact ⟨s₁, ⟨s₁, ⟨p₁.toVPre, vpub_refl G s₁, p₁.toVPre, p₁, p₁, rfl, rfl, rfl⟩, e₁⟩,
      ⟨s₂, ⟨p₁.toVPre, hpub.1, p₂.toVPre, p₁, p₂, hpub.2.1.symm, hpub.2.2.1.symm, hpub.2.2.2.symm⟩, e₂⟩⟩
  · exact fun _ _ h => h

include hvK hctK hdK in
theorem codeC_verified (H : Hash) (hG : G ∈ Pbkdf2.Md.X86_64.mdHashes) (hspK : SpSafe chkC) (impl : PublicImpl) :
    Verified X86_64.target (verifyC chkN chkC impl.name impl.code)
      (Spec.RsaPss.verifyPrecomputedContract G G abi verifyStack) :=
  Verified.of_correct (k := contract G) (codeC_correct hvK hspK hdK impl)
    (codeC_ct hvK hctK hspK hdK H impl) (implies G hG)

end VG.Proof.RsaPss.X86_64.Pc
