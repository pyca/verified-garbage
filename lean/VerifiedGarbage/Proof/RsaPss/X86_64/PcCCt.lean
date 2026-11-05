module

public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCtBase
public import VerifiedGarbage.Proof.RsaPss.X86_64.PcCVerified
public import VerifiedGarbage.Proof.RsaPss.X86_64.PcChk
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCParams
public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
public import VerifiedGarbage.Proof.RsaPss.X86_64.PcCCorrect
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

public import VerifiedGarbage.Proof.RsaPss.X86_64.ByIdx
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.RsaPss.X86_64.TabCall
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCtx
import VerifiedGarbage.Proof.RsaPss.X86_64.EncCtx
/-!
# RSASSA-PSS verification with cached public-key values on x86-64, around
the check of the encoding: constant time, and `Verified`

The prologue and the check of the modulus' first byte, the index of the
table `hash`'s hash function (public: the tables are), `emBits` and the
public-key operation's arguments (public: the modulus' length and first
byte, and places), its call (constant time by its contract), `sAcc` and
`checkEncoding`'s arguments (only `sAcc` is secret), the choice of
`checkEncoding` by that index and its call (constant time by its contract:
its public data, the places and lengths and the tables' words, agree), the
result, and the epilogue, in two runs whose entry states agree on the public
data (`codeC_ct`). With `codeC_correct`, `verifyC` meets the contract
(`codeC_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (PublicImpl pdChkContract)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable {tsH tsG : List FnTable} {H : Hash}

abbrev CSib (a s : State) : Prop := VSib tsH tsG a s
abbrev CAt (J : State → State → Prop) (a t : State) : Prop := VAt tsH tsG J a t

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

/-- The index of the table `hash`'s hash function. -/
def vidx (a : State) : Nat := (vidxWord a).toNat

theorem CSib.veb {a s : State} (S : CSib (tsH := tsH) (tsG := tsG) a s) : veb s = veb a := by
  simp only [VG.Proof.RsaPss.X86_64.Pc.veb, S.n0v, S.gpr (r := .rsi) (by decide)]

theorem CSib.vel {a s : State} (S : CSib (tsH := tsH) (tsG := tsG) a s) : vel s = vel a := by
  simp only [VG.Proof.RsaPss.X86_64.Pc.vel, S.veb]

theorem CSib.vclo {a s : State} (S : CSib (tsH := tsH) (tsG := tsG) a s) : vclo s = vclo a := by
  simp only [VG.Proof.RsaPss.X86_64.Pc.vclo, S.vel, S.gpr (r := .rsi) (by decide)]

theorem CSib.vex {a s : State} (S : CSib (tsH := tsH) (tsG := tsG) a s) : vex s = vex a := by
  simp only [VG.Proof.RsaPss.X86_64.Pc.vex, S.veb, S.vel, S.vclo]

theorem CSib.pre {a s : State} (S : CSib (tsH := tsH) (tsG := tsG) a s) : Pre tsH tsG s := S.ps

theorem veb_ok {s : State} (hp : VPre tsH tsG s) :
    vclo s ≤ 1 ∧ 1 ≤ veb s ∧ veb s ≤ Proof.RsaPss.maxEmBits ∧ vclo s + vel s = (s.gpr .rsi).toNat := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hl8 : Nat.log2 (n0v s) < 8 := RsaPss.log2_lt8 (s.mem (s.gpr .rdi))
  refine ⟨lo_le hl8 (by omega), ?_, ?_, ?_⟩
  · unfold veb ebV; omega
  · unfold veb ebV Proof.RsaPss.maxEmBits; omega
  · unfold vclo vel veb ebV Spec.RsaPss.emLength; omega

variable (f : MdFns) (g : Impl.Mgf1.X86_64.Table.Fns) in
/-- What the tables give the runs whose entry states agree with `a`: the
functions `T` and hash functions `Hs`, `Gs`, the same for every run, that
`checkEncoding` for the index of `a`'s table checks with, in constant time. -/
structure KGood (a : State) (T : Tabs) (Hs Gs : Spec.Mgf1.Hash) : Prop where
  sel : ∀ s, (verifyK tsH tsG).pub a s → Pre tsH tsG s → KSel f g s (vidx a) T Hs Gs
  words : ∀ s, (verifyK tsH tsG).pub a s → Pre tsH tsG s →
    tabWords s.mem (stackArg s 8) (stackArg s 9) = tabWords a.mem (stackArg a 8) (stackArg a 9)
  ct : ConstantTime isa (chkK T Hs Gs).pre (chkK T Hs Gs).pub (checkEncoding f (ofIdx (vidx a)) g)

/-! ## The pieces -/

/-- After the frame's push. -/
def J0 (s t : State) : Prop := t = allocState frameBytes s

/-- The words the prologue stores. -/
def K1 : List Nat := [17, 18, 19, 20, 21, 22, 37, 38]

variable (H) in
/-- After the prologue: the modulus' first byte, ZF set if it is zero, and
the table `hash` in `r11`. -/
def J1 (s t : State) : Prop :=
  VS H s t K1 [(.r11, stackArg s 8)] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (vwrR s) s.mem t.mem ∧
    t.gpr .rax = BitVec.ofNat 64 (n0v s) ∧ t.zf = some (decide (n0v s = 0))

variable (H) in
/-- And the index in its slot. -/
def J2 (s t : State) : Prop :=
  VS H s t (K1 ++ [47]) [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (vwrR s) s.mem t.mem ∧
    t.gpr .rax = BitVec.ofNat 64 (n0v s) ∧ t.zf = some (decide (n0v s = 0))

variable (H) in
/-- At the end. -/
def JR (s t : State) : Prop := VS H s t [] [] fun _ _ => True

theorem pro_ct : RelCT isa (Two (CAt (tsH := tsH) (tsG := tsG) J0))
    (.block (verifyPrologue ++ n0 ++ [.mov .r11 (.mem (arg 8))])) (Two (CAt (tsH := tsH) (tsG := tsG) (J1 H))) := by
  obtain ⟨_, hc⟩ := vcFixed.pro
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
  rw [WP.block_append_iff, WP.block_append_iff]
  refine X86_64.WP.mono_syms (verifyPro_ok hp) fun t1 ⟨k1, L1, R1, f1⟩ sy1 => ?_
  have hM1 : Frame (vwrR s) s.mem t1.mem := f1.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vframe_sub s⟩
  refine X86_64.WP.mono_syms (vn0_ok hp L1 R1 (by simp [vproW, upd]) k1.2.1 hM1)
    fun t2 ⟨k2, hm2, hax2, hz2⟩ sy2 => ?_
  have hM2 : Frame (vwrR s) s.mem t2.mem := hm2 ▸ hM1
  have L2 : Lay t2 (fb s) (stackArg s 4) := L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2])
  refine X86_64.WP.mono_syms (vr11Arg_ok hp L2.rsp (k2.2.1.trans k1.2.1) hM2)
    fun t3 ⟨k3, hm3, h11, hz3⟩ sy3 =>
    ⟨s, S, ⟨⟨L2.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3]), k3.2.2.trans (k2.2.2.trans k1.2.2),
      ⟨_, _, hm3 ▸ hm2 ▸ R1, fun k hk => ?_, trivial⟩, fun p hp => by rw [List.mem_singleton.mp hp]; exact h11,
      sy3.trans (sy2.trans sy1)⟩, k3.2.1.trans (k2.2.1.trans k1.2.1), hm3 ▸ hM2,
      (k3.gpr (by decide)).trans hax2, hz3.trans hz2⟩⟩
  simp only [K1, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [vproW, upd, vw]

theorem vidx_ct : RelCT isa (Two (CAt (tsH := tsH) (tsG := tsG) (J1 H))) (.block idxSlot)
    (Two (CAt (tsH := tsH) (tsG := tsG) (J2 H))) := by
  obtain ⟨_, hc⟩ := vcFixed.idx
  refine two_post (vtwo (H := H) [] [.r11] (fun a => [(.r11, stackArg a 8)])
    (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (fun _ hk => by cases hk) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.arg8]; exact h.1.regs _ (List.mem_singleton_self _))
      fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hax, hz⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  refine X86_64.WP.mono_syms (vidxSlot_ok S.ps v.L R hrd hM (v.regs _ (List.mem_singleton_self _)))
    fun u ⟨L', k', R', hz', hM'⟩ sy => ⟨s, S, ⟨v.next L' k'.2.2 R' (fun k hk => ?_) trivial sy, k'.2.1.trans hrd, hM',
      (k'.gpr (by decide)).trans hax, hz'.trans hz⟩⟩
  rcases List.mem_append.mp hk with hk | hk
  · have : k ≠ 47 := by simp only [K1, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
    simp only [upd]; rw [ifn this]; exact hw k hk
  · rw [List.mem_singleton.mp hk]; simp [upd, vw, vidxWord]

/-- A refusal. -/
theorem fail_ct {Φ : State → State → Prop}
    (hΦ : ∀ a t, Φ a t → ∃ s ks X, CSib (tsH := tsH) (tsG := tsG) a s ∧ VS H s t ks [] X) :
    RelCT isa (Two Φ) verifyFail (Two (CAt (tsH := tsH) (tsG := tsG) (JR H))) := by
  obtain ⟨_, hc⟩ := vFixed.fail
  have hv : ∀ a t, Φ a t → ∃ s, CSib (tsH := tsH) (tsG := tsG) a s ∧ VS H s t [] [] fun _ _ => True :=
    fun a t h => by
      obtain ⟨s, ks, X, S, v⟩ := hΦ a t h
      exact ⟨s, S, v.sub (fun _ h => by cases h) [] (fun _ hp => by cases hp) fun _ _ _ => trivial⟩
  refine two_post (vtwo (H := H) [] [] (fun _ => []) (fun a t h => let ⟨s, S, v⟩ := hv a t h; ⟨s, _, S, v⟩)
    (fun _ => rfl) (by decide) hc) fun a t h => ?_
  obtain ⟨s, S, v⟩ := hv a t h
  refine X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem) ?_ rfl) fun t' ⟨hm, k⟩ sy =>
    ⟨s, S, v.keep k hm (by decide) (fun _ hp => by cases hp) sy⟩
  xrun [verifyFail]

theorem restore_ct : RelCT isa (Two (CAt (tsH := tsH) (tsG := tsG) (JR H))) (.block restoreRegs)
    fun _ _ => True := by
  obtain ⟨_, hc⟩ := vFixed.restore
  exact vtwo (H := H) [] [] (fun _ => []) (fun a t ⟨s, S, v⟩ => ⟨s, _, S, v⟩) (fun _ => rfl) (by decide) hc

/-- The words `emBitsB` stores, in a run. -/
def EX (s : State) : (Nat → Byte) → (Nat → BitVec 64) → Prop := fun _ W => ∀ p ∈ vex s, W p.1 = p.2

/-- The words kept from the prologue to `checkEncoding`'s arguments. -/
def KP : List Nat := K1 ++ [47]

variable (H) in
/-- Before the public-key operation. -/
def JP (s t : State) : Prop :=
  VS H s t KP [] (EX s) ∧ t.rd = s.rd ∧ Frame (vwrR s) s.mem t.mem ∧
    (∀ i < 4, word t.mem (fb s) (8 * i) = vArg s i) ∧ t.gpr .rdi = stackArg s 4 ∧
    t.gpr .rsi = s.gpr .rsi ∧ t.gpr .rdx = stackArg s 6 ∧ t.gpr .rcx = stackArg s 7 ∧ t.gpr .r8 = s.gpr .rdx ∧
    t.gpr .r9 = s.gpr .rcx

variable (H) in
/-- After it. -/
def JQ (s t : State) : Prop := VS H s t KP [] (EX s) ∧ t.rd = s.rd ∧ Frame (vwrR s) s.mem t.mem

theorem prep_ct : RelCT isa (Two fun a t => CAt (tsH := tsH) (tsG := tsG) (J2 H) a t ∧ isa.eval .e t = some false)
    (.block (emBitsB ++ pubArgsC)) (Two (CAt (tsH := tsH) (tsG := tsG) (JP H))) := by
  obtain ⟨_, hc⟩ := vcFixed.prep
  refine two_post (vtwo (H := H) [17, 19, 20, 21, 22, 38] [.rax] (fun a => [(.rax, BitVec.ofNat 64 (n0v a))])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.n0v]; exact h.2.2.2.1) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨⟨s, S, h⟩, he⟩ => ?_
  obtain ⟨v, hrd, hM, hax, hz⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := CSib.pre S
  have h0 : n0v s ≠ 0 := fun h0 => by
    have : isa.eval .e t = some true := by rw [show isa.eval .e t = t.zf from rfl, hz, h0]; rfl
    rw [this] at he; cases he
  refine X86_64.WP.mono_syms (vprep_ok hp v.L R v.wr hrd hM (hw 17 (by decide)) (hw 19 (by decide))
    (hw 20 (by decide)) (hw 22 (by decide)) (hw 38 (by decide)) (x := n0v s) (BitVec.isLt _) h0 hax)
    fun u ⟨L', k', ⟨W', R', ha, hb⟩, di, si, dx, cx, r8, r9, hM'⟩ sy =>
      ⟨s, S, v.next L' k'.2.2 R' (fun k hk => ?_) (fun p hp => ?_) sy, k'.2.1.trans hrd, hM',
        fun i hi => (R'.fr i (by unfold nW frameBytes; omega)).trans (ha i hi), di, si, dx, cx, r8, r9⟩
  · have hk' := hk
    simp only [KP, K1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hk'
    rw [hb k (by unfold nW frameBytes; omega) (by omega), ← hw k hk]
    simp only [vW, upd]
    rw [ifn (by omega), ifn (by omega), ifn (by omega)]
  · simp only [vex, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> dsimp only <;> rw [hb _ (by decide) (by decide)] <;> simp [vW, upd] <;> rfl

theorem centry_pre {a s t : State} (S : CSib (tsH := tsH) (tsG := tsG) a s) (hst : t.gpr .rsp = fb s)
    (hM : Frame (vwrR s) s.mem t.mem) :
    Spec.Rsa.wordsAt t.callEntry.mem (stackArg s 6) (stackArg s 7).toNat =
      Spec.Rsa.wordsAt a.mem (stackArg a 6) (stackArg a 7).toNat := by
  have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, hst]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have fSE : Frame (vwrR s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vret8_sub s⟩)
  exact (pre_words S.ps fSE).trans S.preW

/-- An input, at a call, as on entry. -/
theorem centry_bytes {s t : State} (hst : t.gpr .rsp = fb s) (hM : Frame (vwrR s) s.mem t.mem)
    {R : Region} (hK : (vstkR s).Disjoint R) (hS : R.Disjoint (vscrR s)) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.callEntry.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, hst]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have fSE : Frame (vwrR s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vret8_sub s⟩)
  exact bytesAt_frame fSE (vin_apart hK hS) hl

theorem centry_e {a s t : State} (S : CSib (tsH := tsH) (tsG := tsG) a s) (hst : t.gpr .rsp = fb s)
    (hM : Frame (vwrR s) s.mem t.mem) :
    Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat := by
  have hp := S.ps
  rw [← S.eB]
  exact centry_bytes (R := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩) hst hM hp.dKe hp.des
    (by have := hp.wE; dsimp only; omega)

theorem cvArg_sib {a s : State} (S : CSib (tsH := tsH) (tsG := tsG) a s) {i : Nat} : vArg s i = vArg a i := by
  unfold vArg
  split <;> simp only [S.gpr (r := .rsi) (by decide), S.arg3, S.arg4, S.sig]

/-- The public-key operation's public data agree. -/
theorem cpub {a s₁ s₂ t₁ t₂ : State} (S₁ : CSib (tsH := tsH) (tsG := tsG) a s₁) (h₁ : JP H s₁ t₁)
    (S₂ : CSib (tsH := tsH) (tsG := tsG) a s₂) (h₂ : JP H s₂ t₂) :
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
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), dx₁, dx₂, S₁.arg6, S₂.arg6]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), cx₁, cx₂, S₁.arg7, S₂.arg7]
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
    RelCT isa (Two (CAt (tsH := tsH) (tsG := tsG) (JP H))) (.call impl.name impl.code)
      (Two (CAt (tsH := tsH) (tsG := tsG) (JQ H))) := by
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
    refine X86_64.WP.mono_syms (call_ok impl hp v.L.rsp hrd v.wr hM ha di si dx cx r8 r9)
      fun u ⟨rd', wr', cs', _, hM', hk', _⟩ sy => ?_
    have R' := R.of_call v.L.geo (m' := u.mem) (rgs := [(0, (s.gpr .rsi).toNat)]) (fun x hx hin => hk' x (by
        rcases hin with hin | hin
        · refine .inr ⟨hin, ?_⟩
          have := hx _ (List.mem_singleton_self _)
          rwa [off_zero] at this
        · exact .inl hin)) (by
        intro p hp'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
        subst hp'; dsimp only; unfold oRsa; omega)
    exact ⟨s, S, v.next (v.L.of_rep' R R' rfl (cs' .rsp (by decide)) wr') wr' R' hw hx sy, rd'.trans hrd, hM'⟩

variable (H) in
/-- Before `checkEncoding`. -/
def JK (s t : State) : Prop :=
  VS H s t [] [] (fun _ W => W 0 = off (stackArg s 4) (8 * kw (s.gpr .rsi).toNat) ∧
    W 1 = stackArg s 5 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat) ∧ W 2 = stackArg s 8 ∧ W 3 = stackArg s 9) ∧
    t.rd = s.rd ∧ Frame (vwrR s) s.mem t.mem ∧
    t.gpr .rdi = s.gpr .r8 ∧ t.gpr .rsi = off (stackArg s 4) (vclo s) ∧ t.gpr .rdx = BitVec.ofNat 64 (vel s) ∧
    t.gpr .rcx = BitVec.ofNat 64 (veb s) ∧ t.gpr .r8 = stackArg s 2 ∧ t.gpr .r9 = stackArg s 3 ∧
    t.gpr .r11 = vidxWord s

theorem cargs_ct : RelCT isa (Two (CAt (tsH := tsH) (tsG := tsG) (JQ H))) (.block (chkArgs ++ idxLoad))
    (Two (CAt (tsH := tsH) (tsG := tsG) (JK H))) := by
  obtain ⟨_, hc⟩ := vcFixed.chkArgs
  refine two_post (vtwoX (H := H) id [17, 21, 22, 37, 47] vex [26, 27, 28] [] (fun _ => [])
    (fun a t ⟨s, S, h⟩ => ⟨s, S, h.1.sub (by decide) [] (fun _ hp => by cases hp)
      fun _ _ x => by rw [← CSib.vex S]; exact x⟩)
    (fun _ => rfl) (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM⟩ := h
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hp := CSib.pre S
  obtain ⟨hlo, -, -, -⟩ := veb_ok hp.toVPre
  rw [WP.block_append_iff]
  refine X86_64.WP.mono_syms (chkArgs_ok hp v.L R v.wr hrd hM (lo := vclo s) (el := vel s) (eb := veb s)
    (hw 17 (by decide)) (hw 22 (by decide)) (hx (26, BitVec.ofNat 64 (vclo s)) (by simp [vex]))
    (hx (27, BitVec.ofNat 64 (veb s)) (by simp [vex])) (hx (28, BitVec.ofNat 64 (vel s)) (by simp [vex]))
    (hw 37 (by decide)) hlo)
    fun u ⟨L', k', R', hM', di, si, dx, cx, r8, r9⟩ sy => ?_
  refine X86_64.WP.mono_syms (vidxLoad_ok L' R') fun u2 ⟨k2, hm2, h11⟩ sy2 => ?_
  have L2 : Lay u2 (fb s) (stackArg s 4) := L'.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2])
  refine ⟨s, S, v.next L2 (k2.2.2.trans k'.2.2) (hm2 ▸ R') (fun _ h => by cases h)
      ⟨by simp [chkW, upd], by simp [chkW, upd], by simp [chkW, upd], by simp [chkW, upd]⟩ (sy2.trans sy),
    k2.2.1.trans (k'.2.1.trans hrd), hm2 ▸ hM', (k2.gpr (by decide)).trans di, (k2.gpr (by decide)).trans si,
    (k2.gpr (by decide)).trans dx, (k2.gpr (by decide)).trans cx, (k2.gpr (by decide)).trans r8,
    (k2.gpr (by decide)).trans r9, ?_⟩
  rw [h11]; simp only [chkW, upd]
  rw [ifn (by decide), ifn (by decide), ifn (by decide), ifn (by decide), ifn (by decide)]
  exact hw 47 (by decide)

/-- `checkEncoding`'s arguments, from the state before the call. -/
theorem kAt_of {f : MdFns} {g : Impl.Mgf1.X86_64.Table.Fns} {s t : State} (hp : Pre tsH tsG s) (h : JK H s t)
    {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash} (E : KSel f g s i T Hs Gs) :
    KAt T s t (vclo s) (veb s) (vel s) := by
  obtain ⟨v, hrd, hM, di, si, dx, cx, r8, r9, -⟩ := h
  obtain ⟨V, W, R, -, x0, x1, x2, x3⟩ := v.W
  obtain ⟨-, e1, e2, l⟩ := veb_ok hp.toVPre
  exact ⟨v.L.rsp, hrd, v.wr, hM, v.sy, (R.fr 0 (by decide)).trans x0, (R.fr 1 (by decide)).trans x1,
    (R.fr 2 (by decide)).trans x2, (R.fr 3 (by decide)).trans x3, di, si, dx, cx, r8, r9, by omega, e1, e2, rfl,
    E.hD, E.tabs⟩

/-- The tables' words, at the call, as on entry. -/
theorem vtabWords_call {s t : State} (hp : Pre tsH tsG s) (hM : Frame (vwrR s) s.mem t.mem)
    (hsp : t.gpr .rsp = fb s) :
    tabWords t.callEntry.mem (stackArg s 8) (stackArg s 9) = tabWords s.mem (stackArg s 8) (stackArg s 9) := by
  have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, hsp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have fSE : Frame (vwrR s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vret8_sub s⟩)
  simp only [tabWords, vtab_read hp fSE (.inl rfl) (by decide : 0 + 8 ≤ 40),
    vtab_read hp fSE (.inl rfl) (by decide : 24 + 8 ≤ 40), vtab_read hp fSE (.inl rfl) (by decide : 32 + 8 ≤ 40),
    vtab_read hp fSE (.inr rfl) (by decide : 0 + 8 ≤ 40), vtab_read hp fSE (.inr rfl) (by decide : 8 + 8 ≤ 40),
    vtab_read hp fSE (.inr rfl) (by decide : 16 + 8 ≤ 40), vtab_read hp fSE (.inr rfl) (by decide : 32 + 8 ≤ 40)]

variable {f : MdFns} {g : Impl.Mgf1.X86_64.Table.Fns}
  (hsel : ∀ a, Pre tsH tsG a → ∃ T Hs Gs, KGood (tsH := tsH) (tsG := tsG) f g a T Hs Gs)
  (hspK : ∀ i ∈ idxs, SpSafe (checkEncoding f (ofIdx i) g))
  (hdK : ∀ i ∈ idxs, (checkEncoding f (ofIdx i) g).x86_64Depth ≤ chkStack)

include hsel hspK hdK in
/-- The call of `checkEncoding` for the index `j`. -/
theorem kcall_ct {j : Nat} (hj : j ∈ idxs) :
    RelCT isa (Two fun a t => CAt (tsH := tsH) (tsG := tsG) (JK H) a t ∧ vidx a = j)
      (.call (chkName j) (checkEncoding f (ofIdx j) g)) (Two (CAt (tsH := tsH) (tsG := tsG) (JR H))) := by
  have g' : ∀ (t : State) (rd wr : List Region) {r : Reg}, r ≠ .rsp →
      (t.callEntry.withRegions rd wr).gpr r = t.gpr r :=
    fun t rd wr r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  refine two_post ?_ fun a t ⟨⟨s, S, h⟩, hja⟩ => ?_
  · refine (RelCT.exists_ (P := fun (x : Tabs × Spec.Mgf1.Hash × Spec.Mgf1.Hash) t₁ t₂ => ∃ a,
        (CAt (tsH := tsH) (tsG := tsG) (JK H) a t₁ ∧ vidx a = j) ∧
        (CAt (tsH := tsH) (tsG := tsG) (JK H) a t₂ ∧ vidx a = j) ∧
        KGood (tsH := tsH) (tsG := tsG) f g a x.1 x.2.1 x.2.2 ∧ Pre tsH tsG a) fun x => ?_).mono
      (fun t₁ t₂ ⟨a, h₁, h₂⟩ => by
        have hpa : Pre tsH tsG a := h₁.1.choose_spec.1.1
        obtain ⟨T, Hs, Gs, G⟩ := hsel a hpa
        exact ⟨(T, Hs, Gs), a, h₁, h₂, G, hpa⟩) fun _ _ h => h
    by_cases hx : ∃ a, vidx a = j ∧ KGood (tsH := tsH) (tsG := tsG) f g a x.1 x.2.1 x.2.2 ∧ Pre tsH tsG a
    · obtain ⟨a₀, hj₀, G₀, hpa₀⟩ := hx
      have E₀ := G₀.sel a₀ (vpub_refl tsH tsG a₀) hpa₀
      rw [hj₀] at E₀
      have hct := G₀.ct
      rw [hj₀] at hct
      refine RelCT.callEx (k := chkK x.1 x.2.1 x.2.2) E₀.ok hct
        fun t₁ t₂ ⟨a, ⟨⟨s₁, S₁, h₁⟩, hj₁⟩, ⟨⟨s₂, S₂, h₂⟩, _⟩, G, hpa⟩ => ?_
      have p₁ := S₁.ps; have p₂ := S₂.ps
      have E₁ := G.sel s₁ S₁.2.1 p₁
      have E₂ := G.sel s₂ S₂.2.1 p₂
      have A₁ := kAt_of p₁ h₁ E₁
      have A₂ := kAt_of p₂ h₂ E₂
      obtain ⟨c₁, w₁⟩ := ck_covers (T := x.1) p₁ A₁.rd A₁.wr A₁.hlo A₁.hD
      obtain ⟨c₂, w₂⟩ := ck_covers (T := x.1) p₂ A₂.rd A₂.wr A₂.hlo A₂.hD
      refine ⟨_, _, _, _, ck_pre (Hs := x.2.1) (Gs := x.2.2) p₁ A₁, ck_pre (Hs := x.2.1) (Gs := x.2.2) p₂ A₂,
        ⟨fun r hr => ?_, ?_, ?_, ?_⟩, c₁, w₁, c₂, w₂, by rw [A₁.sp, A₂.sp, S₁.fb, S₂.fb]⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [g' _ _ _ (by decide), g' _ _ _ (by decide), A₁.di, A₂.di, S₁.gpr (r := .r8) (by decide),
            S₂.gpr (r := .r8) (by decide)]
        · rw [g' _ _ _ (by decide), g' _ _ _ (by decide), A₁.si, A₂.si, S₁.arg3, S₂.arg3, CSib.vclo S₁,
            CSib.vclo S₂]
        · rw [g' _ _ _ (by decide), g' _ _ _ (by decide), A₁.dx, A₂.dx, CSib.vel S₁, CSib.vel S₂]
        · rw [g' _ _ _ (by decide), g' _ _ _ (by decide), A₁.cx, A₂.cx, CSib.veb S₁, CSib.veb S₂]
        · rw [g' _ _ _ (by decide), g' _ _ _ (by decide), A₁.r8, A₂.r8, S₁.arg1, S₂.arg1]
        · rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, A₁.sp,
            A₂.sp, S₁.fb, S₂.fb]
      · rw [g' _ _ _ (by decide), g' _ _ _ (by decide), A₁.r9, A₂.r9, S₁.arg2, S₂.arg2]
      · rw [stackArgs_four, stackArgs_four, vstackArg_call p₁ A₁.sp _ _ (i := 0) (by decide),
          vstackArg_call p₂ A₂.sp _ _ (i := 0) (by decide), vstackArg_call p₁ A₁.sp _ _ (i := 1) (by decide),
          vstackArg_call p₂ A₂.sp _ _ (i := 1) (by decide), vstackArg_call p₁ A₁.sp _ _ (i := 2) (by decide),
          vstackArg_call p₂ A₂.sp _ _ (i := 2) (by decide), vstackArg_call p₁ A₁.sp _ _ (i := 3) (by decide),
          vstackArg_call p₂ A₂.sp _ _ (i := 3) (by decide), A₁.w0, A₂.w0, A₁.w1, A₂.w1, A₁.w2, A₂.w2, A₁.w3, A₂.w3,
          S₁.arg3, S₂.arg3, S₁.arg4, S₂.arg4, S₁.gpr (r := .rsi) (by decide), S₂.gpr (r := .rsi) (by decide),
          S₁.arg8, S₂.arg8, S₁.arg9, S₂.arg9]
      · rw [vstackArg_call p₁ A₁.sp _ _ (i := 2) (by decide), vstackArg_call p₂ A₂.sp _ _ (i := 2) (by decide),
          vstackArg_call p₁ A₁.sp _ _ (i := 3) (by decide), vstackArg_call p₂ A₂.sp _ _ (i := 3) (by decide),
          A₁.w2, A₂.w2, A₁.w3, A₂.w3, State.withRegions_mem, State.withRegions_mem, vtabWords_call p₁ A₁.M A₁.sp,
          vtabWords_call p₂ A₂.M A₂.sp, G.words s₁ S₁.2.1 p₁, G.words s₂ S₂.2.1 p₂]
    · exact RelCT.of_false fun _ _ ⟨a, ⟨_, hj₁⟩, _, G, hpa⟩ => hx ⟨a, hj₁, G, hpa⟩
  · have hp := S.ps
    obtain ⟨T, Hs, Gs, G⟩ := hsel a S.1
    have E := G.sel s S.2.1 hp
    rw [hja] at E
    have A := kAt_of hp h E
    obtain ⟨v, -⟩ := h
    obtain ⟨V, W, R, hw, -⟩ := v.W
    exact WP.mono (ck_call E.ok (hspK j hj) (hdK j hj) hp A R)
      fun u ⟨rd', wr', cs', _, hM', sy', R', _⟩ => ⟨s, S, v.next (v.L.of_rep' R R' rfl (cs' .rsp (by decide)) wr') wr'
        R' hw trivial (sy'.trans v.sy.symm)⟩

include hsel hspK hdK in
/-- The choice of `checkEncoding` by the table's index, and its call. -/
theorem kchoose_ct : RelCT isa (Two (CAt (tsH := tsH) (tsG := tsG) (JK H)))
    (byIdx (fun i => .call (chkName i) (checkEncoding f (ofIdx i) g)) idxs)
    (Two (CAt (tsH := tsH) (tsG := tsG) (JR H))) := by
  refine byIdx_ct vidx (fun a t t' ⟨s, S, h⟩ k hm sy => ?_) (fun a t ⟨s, S, h⟩ => ?_) cmpOk_idxs
    (fun j hj => ?_) (fun j hj => kcall_ct hsel hspK hdK hj)
  · obtain ⟨v, hrd, hM, di, si, dx, cx, r8, r9, r11⟩ := h
    have gk : ∀ r, t'.gpr r = t.gpr r := fun r => k.gpr (List.not_mem_nil)
    exact ⟨s, S, v.keep k hm (by simp) (fun _ hp => by cases hp) sy, k.2.1.trans hrd, hm ▸ hM,
      (gk _).trans di, (gk _).trans si, (gk _).trans dx, (gk _).trans cx, (gk _).trans r8, (gk _).trans r9,
      (gk _).trans r11⟩
  · obtain ⟨T, Hs, Gs, G⟩ := hsel a S.1
    refine ⟨(G.sel a (vpub_refl tsH tsG a) S.1).mem, ?_⟩
    rw [h.2.2.2.2.2.2.2.2.2, S.idxw, vidx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · obtain ⟨_, hc⟩ := vcFixed.cmp j hj
    exact vtwo (H := H) [] [.r11] (fun a => [(.r11, vidxWord a)])
      (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (fun _ hk => by cases hk) _ (fun p hp => by
        rw [List.mem_singleton.mp hp, ← S.idxw]; exact h.2.2.2.2.2.2.2.2.2) fun _ _ x => x⟩)
      (fun _ => rfl) (by decide) hc

theorem acc_ct : RelCT isa (Two (CAt (tsH := tsH) (tsG := tsG) (JR H))) (.block [.alu .and .rax (.mem (sp sAcc))])
    (Two (CAt (tsH := tsH) (tsG := tsG) (JR H))) := by
  obtain ⟨_, hc⟩ := vcFixed.acc
  refine two_post (vtwo (H := H) [] [] (fun _ => []) (fun a t ⟨s, S, v⟩ => ⟨s, _, S, v⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, v⟩ => ?_
  refine X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem) ?_ rfl) fun t' ⟨hm, k⟩ sy =>
    ⟨s, S, v.keep k hm (by decide) (fun _ hp => by cases hp) sy⟩
  xrun [ea_sp, v.L.rsp, v.L.ld (d := sAcc) (by decide)]

include hsel hspK hdK in
theorem cbody_ct (H : Hash) (impl : PublicImpl) :
    RelCT isa (Two (CAt (tsH := tsH) (tsG := tsG) J0)) (verifyCBody f g impl.name impl.code) fun _ _ => True := by
  unfold verifyCBody
  simp only [seqs]
  refine (pro_ct (H := H)).seq (vidx_ct.seq ((two_ite (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
      rw [show isa.eval .e t₁ = t₁.zf from rfl, show isa.eval .e t₂ = t₂.zf from rfl, h₁.2.2.2.2, h₂.2.2.2.2,
        S₁.n0v, S₂.n0v])
    (fail_ct (Φ := fun a t => CAt (tsH := tsH) (tsG := tsG) (J2 H) a t ∧ isa.eval .e t = some true)
      fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, _, S, h.1⟩)
    (prep_ct.seq ((pcall_ct impl).seq (cargs_ct.seq ((kchoose_ct hsel hspK hdK).seq acc_ct))))).seq
    restore_ct))

include hsel hspK hdK in
theorem codeC_ct (H : Hash) (impl : PublicImpl) : ConstantTime isa (verifyK tsH tsG).pre (verifyK tsH tsG).pub
    (Impl.RsaPss.X86_64.verifyC f g impl.name impl.code) :=
  RelCT.constantTime (valloc ((cbody_ct hsel hspK hdK H impl).mono
    (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, e₁, e₂⟩ => by
      have p₁ := pre_of h₁
      have p₂ := pre_of h₂
      obtain ⟨T, Hs, Gs, G⟩ := hsel s₁ p₁
      have hi : vidxWord s₂ = vidxWord s₁ :=
        (G.sel s₂ hpub p₂).idx.trans (G.sel s₁ (vpub_refl tsH tsG s₁) p₁).idx.symm
      exact ⟨s₁, ⟨s₁, ⟨p₁, vpub_refl tsH tsG s₁, p₁, rfl⟩, e₁⟩, ⟨s₂, ⟨p₁, hpub, p₂, hi⟩, e₂⟩⟩) fun _ _ h => h))

include hsel hspK hdK in
/-- `verifyC` meets the contract with the tables `tsH` and `tsG`. -/
theorem codeC_verified (H : Hash) (hsat : ∃ s, (VG.Proof.RsaPss.X86_64.verifyC tsH tsG).pre s)
    (impl : PublicImpl) :
    Verified X86_64.target (Impl.RsaPss.X86_64.verifyC f g impl.name impl.code)
      (VG.Proof.RsaPss.X86_64.verifyC tsH tsG) :=
  Verified.of_correct (k := verifyK tsH tsG)
    (codeC_correct (fun s h => let ⟨T, Hs, Gs, G⟩ := hsel s (pre_of h)
      ⟨_, T, Hs, Gs, G.sel s (vpub_refl tsH tsG s) (pre_of h)⟩) hspK hdK impl)
    (codeC_ct hsel hspK hdK H impl) (verify_implies tsH tsG hsat)

end VG.Proof.RsaPss.X86_64.Pc
