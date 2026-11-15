module

public import VerifiedGarbage.Proof.MdHashTable.X86_64.Tables
public import VerifiedGarbage.Proof.HashTable.X86_64
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCCt
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCtBase
public import VerifiedGarbage.Impl.RsaPss.X86_64.Encoding
public import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedCall
public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCtx
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.RsaPss.X86_64.PcCCorrect
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCVerified
public import VerifiedGarbage.Proof.RsaPss.X86_64.ByIdx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
public import VerifiedGarbage.Proof.RsaPss.X86_64.PcChk
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCParams
public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCCorrect
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCFixed
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyFixed
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyBody
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCall
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCCall
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.RsaPss.X86_64.TabCall
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCtx
import VerifiedGarbage.Proof.RsaPss.X86_64.EncCtx
public import VerifiedGarbage.Proof.RsaPss.X86_64.EncCorrect
public import VerifiedGarbage.Proof.RsaPss.X86_64.EncFrame
public import VerifiedGarbage.Proof.RsaPss.X86_64.CtBase
public import VerifiedGarbage.Proof.RsaPss.X86_64.CtHashCT
public import VerifiedGarbage.Proof.RsaPss.X86_64.MgfCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.RsaPss.X86_64.SignFixed
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
import VerifiedGarbage.Proof.RsaPss.X86_64.SignEnc
import VerifiedGarbage.Proof.RsaPss.X86_64.Params
import VerifiedGarbage.Proof.RsaPss.X86_64.EncFixed
public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCorrect
public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkSaltBackCT
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyFrame
public import VerifiedGarbage.Proof.RsaPss.X86_64.Shapes
public import VerifiedGarbage.Proof.Mgf1.Basic
import VerifiedGarbage.Proof.RsaOaep.X86_64.Stack

/-! ### `RsaPss.X86_64.PcCCt`, which only this module used -/

section

/-! ### `RsaPss.X86_64.PcCVerified`, which only this module used -/

section

/-!
# RSASSA-PSS verification with cached public-key values on x86-64, around
the check of the encoding: the calling convention

`codeC_correct`: `verifyC` meets `verifyK` when the cache matches, and keeps
the callee-saved registers, its return address (which only its frame and
calls are below) and MXCSR's control bits.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.Rsa.X86_64 (PublicImpl)

variable {tsH tsG : List FnTable} {f : MdFns} {g : Impl.Mgf1.X86_64.Table.Fns}

theorem chk_calls (hK : ∀ i ∈ idxs, SpSafe (checkEncoding f (ofIdx i) g))
    (hdK : ∀ i ∈ idxs, (checkEncoding f (ofIdx i) g).x86_64Depth ≤ chkStack) :
    (byIdx (fun i => .call (chkName i) (checkEncoding f (ofIdx i) g)) idxs).allInstrs
        (fun i => !isa.writesSp i) = true ∧
      (byIdx (fun i => .call (chkName i) (checkEncoding f (ofIdx i) g)) idxs).x86_64Depth ≤ chkStack + 8 :=
  byIdx_calls fun i hi => ⟨by simp only [Code.allInstrs]; exact spAll_of (hK i hi),
    by simp only [Code.x86_64Depth]; exact Nat.add_le_add_right (hdK i hi) 8⟩

theorem codeC_spAll (hK : ∀ i ∈ idxs, SpSafe (checkEncoding f (ofIdx i) g))
    (hdK : ∀ i ∈ idxs, (checkEncoding f (ofIdx i) g).x86_64Depth ≤ chkStack) (v : PublicImpl) :
    (Impl.RsaPss.X86_64.verifyC f g v.name v.code).allInstrs (fun i => !isa.writesSp i) = true := by
  simp only [Impl.RsaPss.X86_64.verifyC, verifyCBody, seqs, Code.allInstrs, (chk_calls hK hdK).1,
    spAll_of (SpSafe.of_all v.spSafe), verifyFail, Bool.and_true, Bool.true_and]
  rfl

theorem codeC_sp (hK : ∀ i ∈ idxs, SpSafe (checkEncoding f (ofIdx i) g))
    (hdK : ∀ i ∈ idxs, (checkEncoding f (ofIdx i) g).x86_64Depth ≤ chkStack) (v : PublicImpl) :
    SpSafe (Impl.RsaPss.X86_64.verifyC f g v.name v.code) := by
  have h := codeC_spAll hK hdK v
  rw [Code.allInstrs_eq] at h
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem codeC_xd (hK : ∀ i ∈ idxs, SpSafe (checkEncoding f (ofIdx i) g))
    (hdK : ∀ i ∈ idxs, (checkEncoding f (ofIdx i) g).x86_64Depth ≤ chkStack) (v : PublicImpl) :
    (Impl.RsaPss.X86_64.verifyC f g v.name v.code).x86_64Depth ≤ verifyStack := by
  have := (chk_calls hK hdK).2
  simp only [Impl.RsaPss.X86_64.verifyC, verifyCBody, seqs, Code.x86_64Depth, x86_64Depth_zero v.nosp v.depth,
    verifyFail, X86_64.Instr.frameBytes, Nat.zero_max, Nat.max_zero]
  exact Nat.le_trans (Nat.add_le_add_right (Nat.max_le.mpr ⟨(by decide : 0 + 8 ≤ chkStack + 8), this⟩) frameBytes)
    (by decide)

theorem codeC_correct (hsel : ∀ s, (verifyK tsH tsG).pre s → ∃ i T Hs Gs, KSel f g s i T Hs Gs)
    (hK : ∀ i ∈ idxs, SpSafe (checkEncoding f (ofIdx i) g))
    (hdK : ∀ i ∈ idxs, (checkEncoding f (ofIdx i) g).x86_64Depth ≤ chkStack) (v : PublicImpl)
    (s : State) (h : (verifyK tsH tsG).pre s) :
    ∃ t s', Exec isa (Impl.RsaPss.X86_64.verifyC f g v.name v.code) s t s' ∧ abiPreserved s s' ∧
      (verifyK tsH tsG).post s s' := by
  have hp := pre_of h
  have hd := codeC_xd hK hdK v
  obtain ⟨i, T, Hs, Gs, E⟩ := hsel s h
  have hW := X86_64.WP.stackFrame (codeC_sp hK hdK v) (by unfold verifyStack chkStack at hd; omega_using [hd])
    (codeC_ok hK hdK v h E)
  obtain ⟨t, s', he, ⟨hcs, hpost, hmx⟩, hf⟩ := hW
  refine ⟨t, s', he, ⟨hcs, ?_, hmx⟩, hpost⟩
  -- The return address.
  refine Mem.readW_congr fun i hi => hf _ fun r hr hc => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [hp.hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact hp.dRs _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) hc
  · simp only [List.mem_singleton] at hr; subst hr
    have := hp.sp1; have := hp.sp2
    exact Offset.base_disjoint_below (s.gpr .rsp) (n := (Impl.RsaPss.X86_64.verifyC f g v.name v.code).x86_64Depth)
      (k := 8) (by unfold verifyStack chkStack at *; omega_using [hd]) _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) hc

end VG.Proof.RsaPss.X86_64.Pc

end

end

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
  refine ⟨lo_le hl8 (by omega_using [hk1]), ?_, ?_, ?_⟩
  · unfold veb ebV; omega_using [hk1]
  · unfold veb ebV Proof.RsaPss.maxEmBits; omega_using [hk2, hl8]
  · unfold vclo vel veb ebV Spec.RsaPss.emLength; omega_using [hk1, hl8]

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
  · have : k ≠ 47 := by simp only [K1, List.mem_cons, List.not_mem_nil, or_false] at hk; omega_using [hk]
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
        fun i hi => (R'.fr i (by unfold nW frameBytes; omega_using [hi])).trans (ha i hi), di, si, dx, cx, r8, r9⟩
  · have hk' := hk
    simp only [KP, K1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hk'
    rw [hb k (by unfold nW frameBytes; omega_using [hk']) (by omega_using [hk']), ← hw k hk]
    simp only [vW, upd]
    rw [ifn (by omega_using [hk']), ifn (by omega_using [hk']), ifn (by omega_using [hk'])]
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
    (by have := hp.wE; dsimp only; omega_using [])

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
        subst hp'; dsimp only; unfold oRsa; omega_using [hk2])
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
    (R.fr 2 (by decide)).trans x2, (R.fr 3 (by decide)).trans x3, di, si, dx, cx, r8, r9, by omega_using [l], e1, e2, rfl,
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
  simp only [tabWords, vtab_read hp fSE (.inl rfl) (by decide : 0 + 8 ≤ 56),
    vtab_read hp fSE (.inl rfl) (by decide : 24 + 8 ≤ 56), vtab_read hp fSE (.inl rfl) (by decide : 32 + 8 ≤ 56),
    vtab_read hp fSE (.inr rfl) (by decide : 0 + 8 ≤ 56), vtab_read hp fSE (.inr rfl) (by decide : 8 + 8 ≤ 56),
    vtab_read hp fSE (.inr rfl) (by decide : 16 + 8 ≤ 56), vtab_read hp fSE (.inr rfl) (by decide : 48 + 8 ≤ 56)]

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

end

end

/-! ### `RsaPss.X86_64.EncCt`, which only this module used -/

section

/-! ### `RsaPss.X86_64.EncCtEnc`, which only this module used -/

section

/-! ### `RsaPss.X86_64.EncCtBase`, which only this module used -/

section

/-!
# EMSA-PSS's encoding on x86-64: two runs

As for signing (`SignCtBase`): each run's entry state `s` agrees with the
first's, `a`, on the public data (`Sib`): the pointers, the lengths and
`emBits`, from which both compute the same public values (`sw`): `DB`'s
place and length, the mask of the top bits, the salt's length and the
hash's blocks. The digest and the salt are secret. A run's state between
two pieces is described by `SS`; both runs then start the next piece's
taint analysis from the same public values (`stwo`). The writable regions
after the frame are `em` and the working space.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Enc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable (T : Tabs)

/-- `encK.pub`, which does not depend on the hash functions. -/
def EPub (s₁ s₂ : State) : Prop :=
  (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
    (List.range 4).map (stackArg s₁) = (List.range 4).map (stackArg s₂) ∧
    tabWords s₁.mem (stackArg s₁ 2) (stackArg s₁ 3) = tabWords s₂.mem (stackArg s₂ 2) (stackArg s₂ 3)

/-- The entry state `s` of a run, and the first's, `a`. -/
def Sib (a s : State) : Prop := Pre T a ∧ EPub a s ∧ Pre T s

/-- A predicate of the state of a run, given its entry state, for every run
whose entry state agrees with `a`. -/
def At (J : State → State → Prop) (a t : State) : Prop := ∃ s, Sib T a s ∧ J s t

theorem pub_refl (s : State) : EPub s s := ⟨fun _ _ => rfl, rfl, rfl⟩

variable {T}

namespace Sib

variable {a s : State} (h : Sib T a s)
include h

theorem gpr {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) : s.gpr r = a.gpr r :=
  (h.2.1.1 r hr).symm

theorem arg {i : Nat} (hi : i < 4) : stackArg s i = stackArg a i := by
  have := congrArg (fun l => l.getD i 0) h.2.1.2.1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some] at this
  exact this.symm

theorem arg0 : stackArg s 0 = stackArg a 0 := h.arg (by decide)
theorem arg1 : stackArg s 1 = stackArg a 1 := h.arg (by decide)

theorem pa : Pre T a := h.1
theorem ps : Pre T s := h.2.2

/-- The words of the tables. -/
theorem tws : s.mem.readW (off (stackArg s 2) 0) 64 = a.mem.readW (off (stackArg a 2) 0) 64 ∧
    s.mem.readW (off (stackArg s 2) 24) 64 = a.mem.readW (off (stackArg a 2) 24) 64 ∧
    s.mem.readW (off (stackArg s 2) 32) 64 = a.mem.readW (off (stackArg a 2) 32) 64 ∧
    s.mem.readW (off (stackArg s 3) 0) 64 = a.mem.readW (off (stackArg a 3) 0) 64 ∧
    s.mem.readW (off (stackArg s 3) 8) 64 = a.mem.readW (off (stackArg a 3) 8) 64 ∧
    s.mem.readW (off (stackArg s 3) 16) 64 = a.mem.readW (off (stackArg a 3) 16) 64 ∧
    s.mem.readW (off (stackArg s 3) 48) 64 = a.mem.readW (off (stackArg a 3) 48) 64 := by
  have := h.2.1.2.2.symm
  simp only [tabWords, List.cons.injEq, and_true] at this
  exact this

/-- The runs' symbols agree on the tables' functions. -/
theorem syH : SyH T.H T.dn T.f a.syms s.syms :=
  ⟨h.ps.tabs.hf, h.ps.tabs.h0.symm.trans (h.tws.1.trans h.pa.tabs.h0),
    h.ps.tabs.h3.symm.trans (h.tws.2.1.trans h.pa.tabs.h3), h.ps.tabs.h4.symm.trans (h.tws.2.2.1.trans h.pa.tabs.h4)⟩

theorem syG : SyG T.G T.g a.syms s.syms :=
  ⟨h.ps.tabs.gf, h.ps.tabs.g0.symm.trans (h.tws.2.2.2.1.trans h.pa.tabs.g0),
    h.ps.tabs.g1.symm.trans (h.tws.2.2.2.2.1.trans h.pa.tabs.g1),
    h.ps.tabs.g2.symm.trans (h.tws.2.2.2.2.2.1.trans h.pa.tabs.g2)⟩

theorem fb : fb s = fb a := by
  simp only [VG.Proof.RsaPss.X86_64.fb, h.gpr (r := .rsp) (by decide)]

theorem wr : s.wr = a.wr := by
  rw [h.ps.hwr, h.pa.hwr, h.arg0, h.arg1, h.gpr (r := .rdi) (by decide), h.gpr (r := .rsi) (by decide)]

theorem frR : frR s = ⟨VG.Proof.RsaPss.X86_64.fb a, frameBytes⟩ := by
  simp only [VG.Proof.RsaPss.X86_64.frR, h.fb]

end Sib

/-! ## The public values -/

/-- `lo`, always 0. -/
def slo (_s : State) : Nat := 0

/-- `emLen`. -/
def seml (s : State) : Nat := (s.gpr .rsi).toNat

/-- `dbLen`. -/
def sdb (D : Nat) (s : State) : Nat := seml s - D - 1

/-- The salt's length. -/
def ssl (s : State) : Nat := (s.gpr .r8).toNat

/-- The blocks of the hash of `M'`. -/
def snb (H : Hash) (s : State) : Nat := (8 + H.D + ssl s + H.P.L) / H.P.B + 1

/-- The mask of `maskedDB`'s first byte. -/
def smask (s : State) : Byte := (0xFF : Byte) >>> (8 * seml s - (s.gpr .r9).toNat)

/-- The public words of the frame, by index. -/
def sw (H : Hash) (s : State) (k : Nat) : BitVec 64 :=
  match k with
  | 8 => s.mem.readW (off (stackArg s 2) 0) 64
  | 9 => s.mem.readW (off (stackArg s 2) 24) 64
  | 10 => s.mem.readW (off (stackArg s 2) 32) 64
  | 11 => s.mem.readW (off (stackArg s 3) 0) 64
  | 12 => s.mem.readW (off (stackArg s 3) 8) 64
  | 13 => s.mem.readW (off (stackArg s 3) 16) 64
  | 14 => s.mem.readW (off (stackArg s 3) 48) 64
  | 16 => s.gpr .rdi
  | 17 => s.gpr .rsi
  | 21 => stackArg s 0
  | 23 => off (stackArg s 0) (oEm + slo s)
  | 24 => BitVec.ofNat 64 (sdb H.D s)
  | 25 => BitVec.setWidth 64 (smask s)
  | 26 => BitVec.ofNat 64 (slo s)
  | 27 => BitVec.ofNat 64 (8 + H.D + ssl s)
  | 28 => BitVec.ofNat 64 (snb H s)
  | 37 => s.gpr .rdx
  | 39 => s.gpr .rcx
  | 40 => s.gpr .r8
  | _ => 0

/-- The public words `ks`. -/
def spw (H : Hash) (s : State) (ks : List Nat) : List (Nat × BitVec 64) := ks.map fun k => (k, sw H s k)

namespace Sib

variable {a s : State} (h : Sib T a s)
include h

theorem seml : seml s = seml a := by simp only [VG.Proof.RsaPss.X86_64.Enc.seml, h.gpr (r := .rsi) (by decide)]
theorem sdb {D : Nat} : sdb D s = sdb D a := by simp only [VG.Proof.RsaPss.X86_64.Enc.sdb, h.seml]
theorem ssl : ssl s = ssl a := by simp only [VG.Proof.RsaPss.X86_64.Enc.ssl, h.gpr (r := .r8) (by decide)]
theorem snb {H : Hash} : snb H s = snb H a := by simp only [VG.Proof.RsaPss.X86_64.Enc.snb, h.ssl]
theorem smask : smask s = smask a := by
  simp only [VG.Proof.RsaPss.X86_64.Enc.smask, h.seml, h.gpr (r := .r9) (by decide)]

theorem sw {H : Hash} (k : Nat) : sw H s k = sw H a k := by
  unfold VG.Proof.RsaPss.X86_64.Enc.sw
  split <;> simp only [h.gpr (r := .rdi) (by decide), h.gpr (r := .rsi) (by decide), h.gpr (r := .rdx) (by decide),
    h.gpr (r := .rcx) (by decide), h.gpr (r := .r8) (by decide), h.arg0, h.sdb, h.snb, h.ssl, h.smask, slo,
    h.tws.1, h.tws.2.1, h.tws.2.2.1, h.tws.2.2.2.1, h.tws.2.2.2.2.1, h.tws.2.2.2.2.2.1, h.tws.2.2.2.2.2.2]

/-- The frame, `em` and the working space are apart. -/
theorem rest : RestOk 2 (VG.Proof.RsaPss.X86_64.fb a) a.wr := by
  have hp := h.pa
  refine ⟨by rw [hp.hwr]; rfl, ?_, ?_⟩
  · rw [hp.hwr]
    refine List.Pairwise.cons ?_ (List.pairwise_pair.mpr hp.dOs)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dKo.sub_left (frame_sub a)
    · exact hp.dKs.sub_left (frame_sub a)
  · rw [hp.hwr]; intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have := hp.wO; have := hp.wS
    rcases hr with rfl | rfl <;> dsimp only <;> omega_arith

end Sib

/-! ## A run's state between pieces -/

/-- A run, with entry state `s`, between two pieces. -/
structure SS (H : Hash) (s t : State) (ks : List Nat) (rs : List (Reg × BitVec 64))
    (X : (Nat → Byte) → (Nat → BitVec 64) → Prop) : Prop where
  L : Lay t (fb s) (stackArg s 0)
  wr : t.wr = frR s :: s.wr
  W : ∃ V W, Rep t.mem (fb s) (stackArg s 0) V W ∧ (∀ k ∈ ks, W k = sw H s k) ∧ X V W
  regs : ∀ p ∈ rs, t.gpr p.1 = p.2
  sy : t.syms = s.syms

variable {H : Hash}

theorem ss_pub {a s t : State} (S : Sib T a s) {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : SS H s t ks rs X) :
    Pub (fb a) (stackArg a 0) a.wr (spw H a ks) rs X t := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  refine ⟨?_, ?_, ⟨V, W, ?_, fun p hp => ?_, hx⟩, h.regs⟩
  · rw [← S.fb, ← S.arg0]; exact h.L
  · rw [h.wr, S.frR, S.wr]
  · rw [← S.fb, ← S.arg0]; exact R
  · simp only [spw, List.mem_map] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    rw [hw k hk, S.sw]

/-- A piece the analysis checks from `pT 2 ks rgs`. -/
theorem stwo {Φ : State → State → Prop} {c : Prog isa} (ks : List Nat) (rgs : List Reg)
    (rs : State → List (Reg × BitVec 64))
    (hΦ : ∀ a t, Φ a t → ∃ s X, Sib T a s ∧ SS H s t ks (rs a) X) (hr : ∀ a, (rs a).map Prod.fst = rgs)
    (hks : ∀ k ∈ ks, k < nW) {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check (pT 2 ks rgs) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True :=
  two_pub 2 ks rgs fb (fun a => stackArg a 0) State.wr (fun a => spw H a ks) rs
    (fun a t h => let ⟨_, X, S, v⟩ := hΦ a t h; ⟨X, ss_pub S v⟩) (fun a t h => let ⟨_, _, S, _⟩ := hΦ a t h; S.rest)
    (fun a => by simp [spw, Function.comp_def]) hr hks h

theorem SS.keep {s t t' : State} {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : SS H s t ks rs X) {rs' : List Reg} (k : Keep rs' t t')
    (hm : t'.mem = t.mem) (hsp : Reg.rsp ∉ rs') (hrs : ∀ p ∈ rs, p.1 ∉ rs') (hs : t'.syms = t.syms) :
    SS H s t' ks rs X :=
  ⟨h.L.congr (k.gpr hsp) k.2.2 (by rw [hm]), k.2.2.trans h.wr, by rw [hm]; exact h.W,
    fun p hp => (k.gpr (hrs p hp)).trans (h.regs p hp), hs.trans h.sy⟩

theorem SS.next {s t t' : State} {ks ks' : List Nat} {rs : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : SS H s t ks rs X) (L' : Lay t' (fb s) (stackArg s 0))
    (hwr : t'.wr = t.wr) {V' : Nat → Byte} {W' : Nat → BitVec 64} (R' : Rep t'.mem (fb s) (stackArg s 0) V' W')
    (hw : ∀ k ∈ ks', W' k = sw H s k) (hx : X' V' W') (hs : t'.syms = t.syms) : SS H s t' ks' [] X' :=
  ⟨L', hwr.trans h.wr, ⟨V', W', R', hw, hx⟩, (fun _ hp => by cases hp), hs.trans h.sy⟩

theorem SS.sub {s t : State} {ks ks' : List Nat} {rs : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : SS H s t ks rs X) (hks : ∀ k ∈ ks', k ∈ ks)
    (rs' : List (Reg × BitVec 64)) (hrs : ∀ p ∈ rs', t.gpr p.1 = p.2) (hX : ∀ V W, X V W → X' V W) :
    SS H s t ks' rs' X' := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  exact ⟨h.L, h.wr, ⟨V, W, R, fun k hk => hw k (hks k hk), hX V W hx⟩, hrs, h.sy⟩

end VG.Proof.RsaPss.X86_64.Enc

end

end


/-!
# EMSA-PSS's encoding on x86-64: `signEnc` in two runs

`signEnc`'s pieces (`SignCtEnc`), each constant time from the public words of
both runs of `encode`: `DB`'s place and length, the salt's length and so the
length and blocks of `M'`, are public; the digest, the salt and everything
derived from them are not (`enc_signEnc_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Enc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {T : Tabs}

/-- The public words after the checks. -/
def KS6 : List Nat := [8, 9, 10, 11, 12, 13, 14, 16, 17, 21, 25, 26, 37, 39, 40]

/-- And `DB`'s. -/
def KSM : List Nat := [8, 9, 10, 11, 12, 13, 14, 16, 17, 21, 23, 24, 25, 26, 37, 39, 40]

/-- And the length and blocks of `M'`. -/
def KSL : List Nat := [8, 9, 10, 11, 12, 13, 14, 16, 17, 21, 23, 24, 25, 26, 27, 28, 37, 39, 40]

theorem ksm_ne {k j : Nat} (h : k ∈ KSM) (hj : j ∉ KSM) : k ≠ j := fun e => hj (e ▸ h)

theorem ksm_lt {k : Nat} (h : k ∈ KSM) : k < nW := by
  simp only [KSM, List.mem_cons, List.not_mem_nil, or_false] at h; unfold nW frameBytes; omega_arith

/-- After the checks: the salt fits, `rax = emLen - hLen - 2`. -/
def SJ6 (H : Hash) (s t : State) : Prop :=
  SS H s t KS6 [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧
    t.gpr .rax = BitVec.ofNat 64 (seml s - (H.D + 2)) ∧ t.cf = some (decide (seml s - (H.D + 2) < ssl s)) ∧
    H.D + 2 ≤ seml s

/-- In the encoding: the public words `ks`. -/
def SE (H : Hash) (ks : List Nat) (X : State → (Nat → Byte) → (Nat → BitVec 64) → Prop) (s t : State) : Prop :=
  SS H s t ks [] (X s) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧ H.D + ssl s + 2 ≤ seml s

/-- `SE` as a public piece's start. -/
theorem se_ss {ks : List Nat} {X : State → (Nat → Byte) → (Nat → BitVec 64) → Prop} {a t : State}
    (h : At T (SE T.H ks X) a t) (ks' : List Nat) (hks : ∀ k ∈ ks', k ∈ ks := by decide) :
    ∃ s X', Sib T a s ∧ SS T.H s t ks' [] X' :=
  let ⟨s, S, h⟩ := h; ⟨s, _, S, h.1.sub hks [] (fun _ hp => by cases hp) fun _ _ x => x⟩

theorem sdb_ct : RelCT isa (Two fun a t => At T (SJ6 T.H) a t ∧ isa.eval .b t = some false) (.block dbSlots)
    (Two (At T (SE T.H KSM fun _ _ _ => True))) := by
  obtain ⟨_, hc⟩ := sFixed.dbSlots
  refine two_post (stwo (T := T) (H := T.H) [26] [.rax] (fun a => [(.rax, BitVec.ofNat 64 (seml a - (T.H.D + 2)))])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.seml]; exact h.2.2.2.1) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨⟨s, S, h⟩, hb⟩ => ?_
  obtain ⟨v, hrd, hM, hax, hcf, hok⟩ := h
  have hfit : T.H.D + ssl s + 2 ≤ seml s := by
    rw [show isa.eval .b t = t.cf from rfl, hcf] at hb
    simp only [Option.some.injEq, decide_eq_false_iff_not] at hb; omega_arith
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have L := v.L
  refine X86_64.WP.mono_syms (WP.keepIn (by safe_by [dbSlots]) (by exact Nat.zero_le 16)
    (dbSlots_ok L R (hw 26 (by decide)) hax)) fun u1 ⟨⟨L1, k1, R1⟩, f1⟩ sy =>
    ⟨s, S, ⟨v.next L1 k1.2.2 R1 (fun k hk => ?_) trivial sy, k1.2.1.trans hrd, frame_keep hp v.wr L.rsp hM f1, hfit⟩⟩
  by_cases h23 : k = 23
  · subst h23; simp [upd, sw]
  by_cases h24 : k = 24
  · subst h24
    simp only [upd, Nat.reduceEqDiff, ite_false, ite_true, sw, sdb]
    congr 1; omega_arith
  simp only [upd]; rw [ifn h23, ifn h24]
  exact hw k ((by decide : ∀ k ∈ KSM, k ≠ 23 → k ≠ 24 → k ∈ KS6) k hk h23 h24)

/-- After `mHash`: `rcx` is `Y`. -/
def SC2 (H : Hash) (s t : State) : Prop := SE H KSM (fun _ _ _ => True) s t ∧ t.gpr .rcx = off (stackArg s 0) oY

variable (hH : HashOK T.H) (K : Callees T.H)

include hH in
theorem scyd_ct (hc : SignChecks T.H.P T.H.D) :
    RelCT isa (Two (At T (SE T.H KSM fun _ _ _ => True))) (.seq clearY (copyDigest T.H)) (Two (At T (SC2 T.H))) := by
  obtain ⟨_, hc⟩ := hc.copyDigest
  refine two_post (stwo (T := T) (H := T.H) [21, 37] [] (fun _ => []) (fun a t h => se_ss h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hp := S.ps
  have wDg := hp.wDg
  have hDN := hH.hDN
  have hN := hH.N_le
  refine WP.seq (X86_64.WP.mono_syms (WP.keepIn (by safe_by [clearY]) (by exact Nat.zero_le 16)
    (clearY_ok v.L R)) fun u1 ⟨⟨L1, k1, hcx1, R1⟩, f1⟩ sy1 => ?_)
  have hM1 := frame_keep hp v.wr v.L.rsp hM f1
  refine X86_64.WP.mono_syms (WP.keepIn (by safe_by [copyDigest]) (by exact Nat.zero_le 16)
    (copyDigest_ok hH L1 R1 (p := s.gpr .rdx) (hw 37 (by decide)) hcx1
    (fun i hi => ⟨⟨s.gpr .rdx, T.H.D⟩, List.mem_append_left _ (by rw [k1.2.1, hrd, hp.hrd]; simp),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (fun i hi j hj => Outside.ne L1 (by
      have := hp.outside hp.dOdg hp.ddgs hp.dKdg (a := s.gpr .rdx + BitVec.ofNat 64 i)
        (Offset.contains_base _ (by omega_arith) (by omega_arith))
      rwa [k1.2.2, v.wr]) (by unfold oY oRsa; omega_arith)))) fun u2 ⟨⟨L2, k2, R2⟩, f2⟩ sy2 =>
    ⟨s, S, ⟨v.next L2 (k2.2.2.trans k1.2.2) R2 hw hx (sy2.trans sy1), k2.2.1.trans (k1.2.1.trans hrd),
      frame_keep hp (k1.2.2.trans v.wr) L1.rsp hM1 f2, hok⟩, (k2.gpr (by decide)).trans hcx1⟩

theorem w40 {s : State} {W : Nat → BitVec 64} (h : W 40 = sw T.H s 40) : W 40 = BitVec.ofNat 64 (ssl s) := by
  rw [h]; show s.gpr .r8 = _; rw [ssl, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem ssl_le {s : State} (h : T.H.D + ssl s + 2 ≤ seml s) (hk : (s.gpr .rsi).toNat ≤ 1024) : ssl s ≤ 1024 := by
  unfold seml at h; omega_arith

include hH in
theorem copySaltY_ct (hc : SignChecks T.H.P T.H.D) :
    RelCT isa (Two (At T (SC2 T.H))) (copySaltY T.H) (Two (At T (SE T.H KSM fun _ _ _ => True))) := by
  obtain ⟨_, hc⟩ := hc.copySaltY
  refine two_post (stwo (T := T) (H := T.H) [39, 40] [.rcx] (fun a => [(.rcx, off (stackArg a 0) oY)])
    (fun a t ⟨s, S, ⟨v, _⟩, hcx⟩ => ⟨s, _, S, v.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.arg0]; exact hcx) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, ⟨v, hrd, hM, hok⟩, hcx⟩ => ?_
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hp := S.ps
  have wSa := hp.wSa
  have hk2 := hp.k2
  have hsl := ssl_le hok hk2
  have hss : ssl s = (s.gpr .r8).toNat := rfl
  have hDN := hH.hDN
  have hN := hH.N_le
  exact X86_64.WP.mono_syms (WP.keepIn (by safe_by [copySaltY]) (by exact Nat.zero_le 16)
    (copySaltY_ok hH v.L R (q := s.gpr .rcx) (sl := ssl s) (hw 39 (by decide)) (w40 (hw 40 (by decide)))
      (by omega_arith) hcx
      (fun i hi => ⟨⟨s.gpr .rcx, (s.gpr .r8).toNat⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
        Offset.contains_base _ (by unfold ssl at hi; omega_arith) (by omega_arith)⟩)
      (fun i hi j hj => Outside.ne v.L (by
        have := hp.outside hp.dOsa hp.dsas hp.dKsa (a := s.gpr .rcx + BitVec.ofNat 64 i)
          (Offset.contains_base _ (by unfold ssl at hi; omega_arith) (by omega_arith))
        rwa [v.wr]) (by unfold oY oRsa; omega_arith)))) fun u ⟨⟨L', k', R'⟩, f⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' hw hx sy, k'.2.1.trans hrd, frame_keep hp v.wr v.L.rsp hM f, hok⟩

include hH in
theorem signLen_ct (hc : SignChecks T.H.P T.H.D) :
    RelCT isa (Two (At T (SE T.H KSM fun _ _ _ => True))) (.block (signLen T.H))
      (Two (At T (SE T.H KSL fun _ _ _ => True))) := by
  obtain ⟨_, hc⟩ := hc.signLen
  refine two_post (stwo (T := T) (H := T.H) [40] [] (fun _ => []) (fun a t h => se_ss h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hsl := ssl_le hok hp.k2
  exact X86_64.WP.mono_syms (WP.keepIn (by safe_by [signLen]) (by exact Nat.zero_le 16)
    (signLen_ok hH v.L R (sl := ssl s) (w40 (hw 40 (by decide))) (by omega_arith))) fun u ⟨⟨L', k', R'⟩, f⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' (fun k hk => by
      by_cases h27 : k = 27
      · subst h27; simp [upd, sw]
      by_cases h28 : k = 28
      · subst h28; simp [upd, sw, snb]
      simp only [upd]; rw [ifn h28, ifn h27]
      exact hw k ((by decide : ∀ k ∈ KSL, k ≠ 27 → k ≠ 28 → k ∈ KSM) k hk h27 h28)) trivial sy,
      k'.2.1.trans hrd, frame_keep hp v.wr v.L.rsp hM f, hok⟩

/-- A public word of the entry state `a`. -/
theorem spw_w {H : Hash} {a : State} {ks : List Nat} {W : Nat → BitVec 64} (hw : ∀ p ∈ spw H a ks, W p.1 = p.2)
    {k : Nat} (hk : k ∈ ks) : W k = sw H a k :=
  hw (k, sw H a k) (List.mem_map.mpr ⟨k, hk, rfl⟩)

/-- The slots of the table of `MdHash`, in a run. -/
theorem ss_ht {s t : State} {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (hp : Pre T s) (v : SS T.H s t ks rs X) {W : Nat → BitVec 64}
    (hw : ∀ k ∈ ks, W k = sw T.H s k) (h8 : 8 ∈ ks := by decide) (h9 : 9 ∈ ks := by decide)
    (h10 : 10 ∈ ks := by decide) : HT T.H T.dn T.f W t.syms := by
  rw [v.sy]; exact hp.tabs.hf.ht ((hw 8 h8).trans hp.tabs.h0) ((hw 9 h9).trans hp.tabs.h3) ((hw 10 h10).trans hp.tabs.h4)

/-- The slots of the table of `MdHash`, in a run. -/
theorem ss_gt {s t : State} {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (hp : Pre T s) (v : SS T.H s t ks rs X) {W : Nat → BitVec 64}
    (hw : ∀ k ∈ ks, W k = sw T.H s k) (h11 : 11 ∈ ks := by decide) (h12 : 12 ∈ ks := by decide)
    (h13 : 13 ∈ ks := by decide) (h14 : 14 ∈ ks := by decide) : GT T.G T.g W t.syms := by
  rw [v.sy]
  exact hp.tabs.gf.gt ((hw 11 h11).trans hp.tabs.g0) ((hw 12 h12).trans hp.tabs.g1) ((hw 13 h13).trans hp.tabs.g2)
    ((hw 14 h14).trans hp.tabs.g4)

/-- The hash's anchor: the blocks of `M'`. -/
def shashA (H : Hash) (a : State) : HA := ⟨fb a, stackArg a 0, a.wr, snb H a, a.syms⟩

include hH in
theorem sl_he {a t : State} (h : At T (SE T.H KSL fun _ _ _ => True) a t) :
    HE T.H T.dn T.f 2 (shashA T.H a) t := by
  obtain ⟨s, S, v, -, -, hok⟩ := h
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have hk2 := S.pa.k2
  have tb := S.pa.tabs
  rw [S.ssl, S.seml] at hok
  have hsl := ssl_le hok hk2
  have h1 := Nat.lt_div_mul_add (a := 8 + T.H.D + ssl a + T.H.P.L) (b := T.H.P.B) hB0
  have h2 := Nat.div_mul_le_self (8 + T.H.D + ssl a + T.H.P.L) T.H.P.B
  obtain ⟨L, w, ⟨V, W, R, hw, -⟩, rg⟩ := ss_pub S v
  refine ⟨⟨S.rest, Nat.succ_pos _, by simp only [shashA, snb]; rw [Nat.succ_mul]; omega_arith⟩,
    ⟨L, w, ⟨V, W, R, fun p hp => ?_, 8 + T.H.D + ssl a, spw_w hw (k := 27) (by decide), ?_⟩, rg⟩, S.syH.tr v.sy⟩
  · simp only [hws, shashA, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact spw_w hw (k := 21) (by decide)
    · exact spw_w hw (k := 28) (by decide)
    · exact (spw_w hw (k := 8) (by decide)).trans tb.h0
    · exact (spw_w hw (k := 9) (by decide)).trans tb.h3
    · exact (spw_w hw (k := 10) (by decide)).trans tb.h4
  · simp only [shashA, snb]; rw [Nat.succ_mul]; omega_arith

variable (hdk : DigOK T.H) (hf : MdFnsSafe T.f) (hg : FnsSafe T.g)

include hH K hdk hf in
theorem shash_ct (hc : HashChecks T.H.P T.H.D 2) :
    RelCT isa (Two (At T (SE T.H KSL fun _ _ _ => True))) (ctHash T.f T.H)
      (Two (At T (SE T.H KSM fun _ _ _ => True))) := by
  refine two_post (two_map (shashA T.H) (fun a t h => sl_he hH h)
    (ctHash_ct hH K hdk 2 hc (fixedChecks (.inr rfl)))) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have hsl := ssl_le hok hp.k2
  have h1 := Nat.lt_div_mul_add (a := 8 + T.H.D + ssl s + T.H.P.L) (b := T.H.P.B) hB0
  have h2 := Nat.div_mul_le_self (8 + T.H.D + ssl s + T.H.P.L) T.H.P.B
  have hks : ∀ k ∈ KSM, k ∈ KSL := by decide
  exact X86_64.WP.mono_syms (WP.keepIn (ctHash_safe hH hf) (by have := ctHash_xd (H := T.H) hf; omega_using [this])
    (ctHash_gen hH K v.L R (hw 27 (by decide)) (hw 28 (by decide)) (by unfold snb; rw [Nat.succ_mul]; omega_arith)
      (by unfold snb; rw [Nat.succ_mul]; omega_arith) (ss_ht hp v hw) hdk))
    fun u ⟨⟨L', rd', wr', _, V', W', R', _, hW', _⟩, f⟩ sy =>
    ⟨s, S, ⟨L', wr'.trans v.wr, ⟨V', W', R', fun k hk => (hW' k (ksm_lt hk) (ksm_ne hk (by decide))
      (ksm_ne hk (by decide))).trans (hw k (hks k hk)), trivial⟩, (fun _ hp => by cases hp), sy.trans v.sy⟩,
      rd'.trans hrd, frame_keep hp v.wr v.L.rsp hM f, hok⟩

theorem sclearEm_ct : RelCT isa (Two (At T (SE T.H KSM fun _ _ _ => True))) clearEm
    (Two (At T (SE T.H KSM fun _ _ _ => True))) := by
  obtain ⟨_, hc⟩ := sFixed.clearEm
  refine two_post (stwo (T := T) (H := T.H) [17, 21] [] (fun _ => []) (fun a t h => se_ss h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have hk1 : 1 ≤ (s.gpr .rsi).toNat := by unfold seml at hok; omega_arith
  exact X86_64.WP.mono_syms (WP.keepIn (by decide) (by exact Nat.zero_le 16)
    (clearEm_ok v.L R (k := (s.gpr .rsi).toNat)
      (by rw [hw 17 (by decide)]; show s.gpr .rsi = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by omega_arith) hk2)) fun u ⟨⟨L', k', R'⟩, f⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' hw trivial sy, k'.2.1.trans hrd, frame_keep hp v.wr v.L.rsp hM f, hok⟩

theorem sputSalt_ct :
    RelCT isa (Two (At T (SE T.H KSM fun _ _ _ => True))) putSalt (Two (At T (SE T.H KSM fun _ _ _ => True))) := by
  obtain ⟨_, hc⟩ := sFixed.putSalt
  refine two_post (stwo (T := T) (H := T.H) [23, 24, 39, 40] [] (fun _ => []) (fun a t h => se_ss h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have wSa := hp.wSa
  have hk2 := hp.k2
  have : slo s = 0 := rfl
  have hss : ssl s = (s.gpr .r8).toNat := rfl
  exact X86_64.WP.mono_syms (WP.keepIn (by safe_by [putSalt]) (by exact Nat.zero_le 16)
    (putSalt_ok v.L R (e := oEm + slo s) (db := sdb T.H.D s) (q := s.gpr .rcx) (sl := ssl s) (hw 23 (by decide))
      (hw 24 (by decide)) (hw 39 (by decide)) (w40 (hw 40 (by decide))) (by unfold sdb; omega_arith)
      (by unfold sdb seml oEm oRsa at *; omega_arith)
      (fun i hi => ⟨⟨s.gpr .rcx, (s.gpr .r8).toNat⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
        Offset.contains_base _ (by unfold ssl at hi; omega_arith) (by omega_arith)⟩)
      (fun i hi j hj => Outside.ne v.L (by
        have := hp.outside hp.dOsa hp.dsas hp.dKsa (a := s.gpr .rcx + BitVec.ofNat 64 i)
          (Offset.contains_base _ (by unfold ssl at hi; omega_arith) (by omega_arith))
        rwa [v.wr]) (by unfold sdb seml oEm oRsa at *; omega_arith)))) fun u ⟨⟨L', k', R'⟩, f⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' hw trivial sy, k'.2.1.trans hrd, frame_keep hp v.wr v.L.rsp hM f, hok⟩

include hH in
/-- `putH`'s copy of the digest. -/
theorem putH1_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e db : Nat} (he : W 23 = off S e) (hdb : W 24 = BitVec.ofNat 64 db)
    (hend : e + db + T.H.D ≤ oRsa) (he1 : oEm ≤ e) :
    WP isa (.seq (.block (([.mov .rdi (.mem (sp sEb)), .mov .rax (.mem (sp sDb)), .alu .add .rdi (.reg .rax)] : List Instr) ++
      scr .rsi oDig ++ ([.mov32 .r8 (.imm 0)] : List Instr)))
      (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rdi .r8) .rax] (.imm (BitVec.ofNat 32 T.H.D)))) u fun w =>
      Lay w F S ∧ Keep [.rdi, .rsi, .rax, .r8] u w ∧ Rep w.mem F S (cpV V (fun i => V (oDig + i)) (e + db) T.H.D) W := by
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have c1 : oEm = 2560 := rfl
  have c3 : oDig = 2304 := rfl
  have c5 : oRsa = 8192 := rfl
  have hs := L.slot
  simp only [Bignum.word] at hs
  refine WP.seq (WP.mono (WP.keep [.rdi, .rsi, .r8, .rax] (Q := fun v => v.gpr .rdi = off S (e + db) ∧
      v.gpr .rsi = off S oDig ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨h₁, h₂, h₃, hm⟩, hkv⟩ => ?_)
  · xrun [scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sScr) (by decide), hs,
      L.ld (d := sEb) (by decide), L.ld (d := sDb) (by decide), R.rd (d := sEb) 23 rfl (by decide),
      R.rd (d := sDb) 24 rfl (by decide), he, hdb, off_plus,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oDig < 2 ^ 31 by decide)]
  have Lv : Lay v F S := L.congr (hkv.gpr (by decide)) hkv.2.2 (by rw [hm])
  have Rv : Rep v.mem F S V W := hm ▸ R
  refine WP.mono (copy_ok Lv Rv (d := .rdi) (by decide) (p := off S oDig) (o := e + db) (disp := 0)
    (n := T.H.D) (stepI_ok (show T.H.D < 2 ^ 31 by omega_arith) v [.rax, .r8]) hD (by unfold oRsa at *; omega_arith) h₂ h₁ h₃
    (fun i hi => by rw [off_plus]; exact Lv.sld8 (by unfold oRsa; omega_arith))
    (fun i hi j hj => by rw [off_plus]; exact Offset.add_ofNat_ne S (by omega_arith) (by omega_arith) (by omega_arith)))
    fun w ⟨Lw, kw, Rw⟩ => ⟨Lw, (hkv.trans kw).mono (by decide), ?_⟩
  refine (congrArg (fun V' => Rep w.mem F S V' W) (funext fun x => ?_)).mp Rw
  simp only [cpV, Nat.add_zero]
  split
  · rw [off_plus, Rv.scr _ (by unfold oRsa at *; omega_arith)]
  · rfl

include hH in
theorem sputH_ct (hc : SignChecks T.H.P T.H.D) :
    RelCT isa (Two (At T (SE T.H KSM fun _ _ _ => True))) (putH T.H) (Two (At T (SE T.H KSM fun _ _ _ => True))) := by
  obtain ⟨_, h1⟩ := hc.putH
  obtain ⟨_, h2⟩ := sFixed.putHTail
  have hDN := hH.hDN
  have hN := hH.N_le
  refine two_post ?_ fun a t ⟨s, S, h⟩ => ?_
  · rw [putH_eq]
    refine RelCT.assoc (RelCT.seq (two_post (Ψ := At T (SE T.H KSM fun _ _ _ => True))
      (stwo (T := T) (H := T.H) [21, 23, 24] [] (fun _ => [])
      (fun a t h => se_ss h _) (fun _ => rfl) (by decide) h1) fun a t ⟨s, S, h⟩ => ?_)
      (stwo (T := T) (H := T.H) [17, 21] [] (fun _ => [])
        (fun a t (h : At T (SE T.H KSM fun _ _ _ => True) a t) => se_ss h _) (fun _ => rfl) (by decide) h2))
    obtain ⟨v, hrd, hM, hok⟩ := h
    obtain ⟨V, W, R, hw, -⟩ := v.W
    have hk2 := S.ps.k2
    have : slo s = 0 := rfl
    exact X86_64.WP.mono_syms (WP.keepIn (by safe_by [putH]) (by exact Nat.zero_le 16)
      (putH1_ok hH v.L R (e := oEm + slo s) (db := sdb T.H.D s) (hw 23 (by decide)) (hw 24 (by decide))
        (by unfold sdb seml oEm oRsa at *; omega_arith) (by omega_arith))) fun u ⟨⟨L', k', R'⟩, f⟩ sy =>
      ⟨s, S, v.next L' k'.2.2 R' hw trivial sy, k'.2.1.trans hrd, frame_keep S.ps v.wr v.L.rsp hM f, hok⟩
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have : slo s = 0 := rfl
  exact X86_64.WP.mono_syms (WP.keepIn (by safe_by [putH]) (by exact Nat.zero_le 16)
    (putH_ok hH v.L R (e := oEm + slo s) (db := sdb T.H.D s) (k := (s.gpr .rsi).toNat) (hw 23 (by decide))
      (hw 24 (by decide)) (by rw [hw 17 (by decide)]; show s.gpr .rsi = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by omega_arith) (by unfold sdb seml at *; omega_arith) hk2)) fun u ⟨⟨L', k', R'⟩, f⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' hw trivial sy, k'.2.1.trans hrd, frame_keep hp v.wr v.L.rsp hM f, hok⟩

/-- `MGF1`'s anchor: `DB`'s place and length. -/
def smgfA (H : Hash) (a : State) : MA := ⟨fb a, stackArg a 0, a.wr, oEm + slo a, sdb H.D a, a.syms⟩

theorem se_me {a t : State} (h : At T (SE T.H KSM fun _ _ _ => True) a t) :
    ME T.G T.g 2 T.H (smgfA T.H a) t := by
  obtain ⟨s, S, v, -, -, hok⟩ := h
  have hp := S.pa
  have hk2 := hp.k2
  have tb := hp.tabs
  have : slo a = 0 := rfl
  rw [S.seml, S.ssl] at hok
  obtain ⟨L, w, ⟨V, W, R, hw, -⟩, rg⟩ := ss_pub S v
  refine ⟨⟨S.rest, ⟨by simp only [smgfA]; omega_arith, by simp only [smgfA, sdb]; omega_arith, ?_⟩⟩,
    ⟨L, w, ⟨V, W, R, fun p hp => ?_, trivial⟩, rg⟩, S.syG.tr v.sy⟩
  · simp only [smgfA, sdb, seml] at hok ⊢; omega_arith
  · simp only [smgfA, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact spw_w hw (k := 21) (by decide)
    · exact spw_w hw (k := 23) (by decide)
    · exact spw_w hw (k := 24) (by decide)
    · exact (spw_w hw (k := 14) (by decide)).trans tb.g4
    · exact (spw_w hw (k := 11) (by decide)).trans tb.g0
    · exact (spw_w hw (k := 12) (by decide)).trans tb.g1
    · exact (spw_w hw (k := 13) (by decide)).trans tb.g2

variable (hG : Pbkdf2.Md.X86_64.Calls.StreamOK T.G) {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = T.G.D)
  (hGv : Proof.Mgf1.Valid Gs)

include hG hGh hGl hGv hg in
theorem smgf_ct (hc : HashChecks T.H.P T.H.D 2) :
    RelCT isa (Two (At T (SE T.H KSM fun _ _ _ => True))) (mgfXor T.H T.g)
      (Two (At T (SE T.H KSM fun _ _ _ => True))) := by
  refine two_post (two_map (smgfA T.H) (fun a t h => se_me h)
    (mgfXor_ct hG hGh hGl hGv hc (fixedChecks (.inr rfl)))) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have : slo s = 0 := rfl
  exact X86_64.WP.mono_syms (WP.keepIn (mgfXor_safe hg) (mgfXor_xd hg)
    (mgfXor_ok hG hGh hGl hGv T.H v.L R (ss_gt hp v hw) (e := oEm + slo s) (db := sdb T.H.D s)
      ⟨by omega_arith, by unfold sdb; omega_arith, by unfold sdb seml at *; unfold oEm; omega_arith⟩ (hw 23 (by decide))
      (hw 24 (by decide)))) fun u ⟨⟨L', rd', wr', _, V', W', R', hW', _⟩, f⟩ sy =>
    ⟨s, S, ⟨L', wr'.trans v.wr, ⟨V', W', R', fun k hk => (hW' k (ksm_lt hk) (by
      simp only [KSM, List.mem_cons, List.not_mem_nil, or_false] at hk; omega_arith)).trans (hw k hk), trivial⟩,
      (fun _ hp => by cases hp), sy.trans v.sy⟩, rd'.trans hrd, frame_keep hp v.wr v.L.rsp hM f, hok⟩

theorem sclearTop_ct : RelCT isa (Two (At T (SE T.H KSM fun _ _ _ => True))) (.block clearTop)
    (Two (At T (SE T.H KSM fun _ _ _ => True))) := by
  obtain ⟨_, hc⟩ := sFixed.clearTop
  refine two_post (stwo (T := T) (H := T.H) [23] [] (fun _ => []) (fun a t h => se_ss h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have : slo s = 0 := rfl
  exact X86_64.WP.mono_syms (WP.keepIn (by safe_by [clearTop]) (by exact Nat.zero_le 16)
    (clearTop_ok v.L R (e := oEm + slo s) (c := smask s) (hw 23 (by decide))
      (by rw [hw 25 (by decide)]; rfl) (by unfold oEm oRsa; omega_arith)))
    fun u ⟨⟨L', k', R'⟩, f⟩ sy => ⟨s, S, v.next L' k'.2.2 R' hw trivial sy, k'.2.1.trans hrd,
      frame_keep S.ps v.wr v.L.rsp hM f, hok⟩

include hH K hdk hf hG hGh hGl hGv hg in
theorem enc_signEnc_ct (hc : PssChecks T.H.P T.H.D) :
    RelCT isa (Two fun a t => At T (SJ6 T.H) a t ∧ isa.eval .b t = some false) (signEnc T.f T.H T.g)
      (Two (At T (SE T.H KSM fun _ _ _ => True))) := by
  unfold signEnc
  simp only [seqs]
  exact sdb_ct.seq (RelCT.assoc ((scyd_ct hH hc.sign).seq ((copySaltY_ct hH hc.sign).seq
    ((signLen_ct hH hc.sign).seq ((shash_ct hH K hdk hf hc.hash2).seq (sclearEm_ct.seq (sputSalt_ct.seq
      ((sputH_ct hH hc.sign).seq ((smgf_ct hg hG hGh hGl hGv hc.hash2).seq sclearTop_ct)))))))))

end VG.Proof.RsaPss.X86_64.Enc

end

end


/-!
# EMSA-PSS's encoding on x86-64: constant time, and `Verified`

The prologue, the checks of `emLen` and the salt's length (their branches
are on public values), the encoding (`enc_signEnc_ct`), its copy to `em` and
the epilogue, in two runs whose entry states agree on the public data
(`enc_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Enc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {T : Tabs}

/-- The entry of the frame. -/
def J0 (s t : State) : Prop := t = allocState frameBytes s

/-- The public words the prologue stores. -/
def KS0 : List Nat := [16, 17, 21, 25, 26, 37, 39, 40]

/-- And the slots of the table of `MdHash`. -/
def KS1 : List Nat := [8, 9, 10, 16, 17, 21, 25, 26, 37, 39, 40]

/-- After the prologue: `r11` is the table `hash`. -/
def EJa (H : Hash) (s t : State) : Prop :=
  SS H s t KS0 [(.r11, stackArg s 2)] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame [frR s] s.mem t.mem

/-- After its slots: `r11` is the table `mgf1`. -/
def EJb (H : Hash) (s t : State) : Prop :=
  SS H s t KS1 [(.r11, stackArg s 3)] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame [frR s] s.mem t.mem

/-- After the tables' slots. -/
def EJ1 (H : Hash) (s t : State) : Prop :=
  SS H s t KS6 [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem

/-- After `fitH`: CF set if `emLen` is too short. -/
def EJ2 (H : Hash) (s t : State) : Prop :=
  EJ1 H s t ∧ t.gpr .rax = BitVec.ofNat 64 (seml s) ∧ t.cf = some (decide (seml s < H.D + 2))

/-- At the end. -/
def EJR (H : Hash) (s t : State) : Prop := SS H s t [] [] fun _ _ => True

theorem pro_ct : RelCT isa (Two (At T J0)) (.block (encPrologue ++ ([.mov .r11 (.mem (arg 2))] : List Instr)))
    (Two (At T (EJa T.H))) := by
  obtain ⟨_, hc⟩ := eFixed.pro
  have ar : ∀ (s : State) {r : Reg}, r ≠ .rsp → (allocState frameBytes s).gpr r = s.gpr r := fun s r hr => by
    rw [allocState_gpr']; exact ifn hr _ _
  refine two_post (two_pub0 2 [.rdi, .rsi, .rdx, .rcx, .r8, .r9] fb State.wr
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
  refine X86_64.WP.mono_syms (encPro_ok hp) fun t1 ⟨k1, L1, R1, f1⟩ s1 => ?_
  refine X86_64.WP.mono_syms (argR11_ok hp L1.rsp k1.2.1 f1 (j := 2) (by decide)) fun t2 ⟨k2, hm2, h11⟩ s2 =>
    ⟨s, S, ⟨L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2]), k2.2.2.trans k1.2.2,
      ⟨_, _, hm2 ▸ R1, fun k hk => ?_, trivial⟩, fun p hp => by rw [List.mem_singleton.mp hp]; exact h11,
      s2.trans s1⟩, k2.2.1.trans k1.2.1, hm2 ▸ f1⟩
  have hel := hp.hel
  simp only [KS0, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [proW', proW, upd, sw, smask, seml, slo, hel]

theorem hsl_ct : RelCT isa (Two (At T (EJa T.H))) (.block (hSlots ++ ([.mov .r11 (.mem (arg 3))] : List Instr)))
    (Two (At T (EJb T.H))) := by
  obtain ⟨_, hc⟩ := eFixed.hSl
  refine two_post (stwo (T := T) (H := T.H) [] [.r11] (fun a => [(.r11, stackArg a 2)])
    (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (fun _ hk => by cases hk) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.arg (by decide)]; exact h.1.regs _ (List.mem_singleton_self _))
      fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hf⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  refine X86_64.WP.mono_syms (hSl_ok S.ps v.L R hrd hf (v.regs _ (List.mem_singleton_self _)))
    fun u ⟨k, L', h11, f', R'⟩ sy =>
    ⟨s, S, ⟨L', k.2.2.trans v.wr, ⟨_, _, R', fun j hj => ?_, trivial⟩,
      fun p hp => by rw [List.mem_singleton.mp hp]; exact h11, sy.trans v.sy⟩, k.2.1.trans hrd, f'⟩
  simp only [KS1, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | h | h | h | h | h | h | h | h
  · simp [upd, sw]
  · simp [upd, sw]
  · simp [upd, sw]
  all_goals
    simp only [upd]
    rw [ifn (by omega_using [h]), ifn (by omega_using [h]), ifn (by omega_using [h])]
    exact hw _ (by simp only [KS0, List.mem_cons, List.not_mem_nil, or_false]; omega_using [h])

theorem gsl_ct : RelCT isa (Two (At T (EJb T.H))) (.block gSlots) (Two (At T (EJ1 T.H))) := by
  obtain ⟨_, hc⟩ := eFixed.gSl
  refine two_post (stwo (T := T) (H := T.H) [] [.r11] (fun a => [(.r11, stackArg a 3)])
    (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (fun _ hk => by cases hk) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.arg (by decide)]; exact h.1.regs _ (List.mem_singleton_self _))
      fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hf⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  refine X86_64.WP.mono_syms (gSl_ok S.ps v.L R hrd hf (v.regs _ (List.mem_singleton_self _)))
    fun u ⟨k, L', f', R'⟩ sy =>
    ⟨s, S, ⟨L', k.2.2.trans v.wr, ⟨_, _, R', fun j hj => ?_, trivial⟩, (fun _ hp => by cases hp), sy.trans v.sy⟩,
      k.2.1.trans hrd, frame_wrR f'⟩
  simp only [KS6, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with h | h | h | rfl | rfl | rfl | rfl | h | h | h | h | h | h | h | h
  rotate_left 3
  · simp [upd, sw]
  · simp [upd, sw]
  · simp [upd, sw]
  · simp [upd, sw]
  all_goals
    simp only [upd]
    rw [ifn (by omega_using [h]), ifn (by omega_using [h]), ifn (by omega_using [h]), ifn (by omega_using [h])]
    exact hw _ (by simp only [KS1, List.mem_cons, List.not_mem_nil, or_false]; omega_using [h])

theorem fit_ct (hc : HashChecks T.H.P T.H.D 2) (hH : HashOK T.H) :
    RelCT isa (Two (At T (EJ1 T.H))) (.block (fitH T.H)) (Two (At T (EJ2 T.H))) := by
  obtain ⟨_, hc⟩ := hc.fit
  refine two_post (stwo (T := T) (H := T.H) [17] [] (fun _ => [])
    (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hk2 := S.ps.k2
  have hDN := hH.hDN; have hN := hH.N_le
  refine X86_64.WP.mono_syms (fitH_ok (H := T.H) (by omega_using [hDN, hN]) v.L R (k := seml s)
    (by rw [hw 17 (by decide)]; show s.gpr .rsi = _; rw [seml, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by unfold seml; omega_using [hk2])) fun t' ⟨k', hm, hax, hcf⟩ sy =>
    ⟨s, S, ⟨v.keep k' hm (by decide) (fun _ hp => by cases hp) sy, k'.2.1.trans hrd, hm ▸ hM⟩, hax, hcf⟩

/-- A refusal: 0. -/
theorem ret0_ct {Φ : State → State → Prop}
    (hΦ : ∀ a t, Φ a t → ∃ s X, Sib T a s ∧ SS T.H s t [] [] X) :
    RelCT isa (Two Φ) ret0 (Two (At T (EJR T.H))) := by
  obtain ⟨_, hc⟩ := eFixed.ret0
  refine two_post (stwo (T := T) (H := T.H) [] [] (fun _ => []) hΦ (fun _ => rfl) (by decide) hc)
    fun a t h => ?_
  obtain ⟨s, X, S, v⟩ := hΦ a t h
  refine X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem) (by xrun [ret0]) rfl)
    fun t' ⟨hm, k⟩ sy => ⟨s, S, (v.keep k hm (by decide) (fun _ hp => by cases hp) sy).sub (by decide) []
      (fun _ hp => by cases hp) fun _ _ _ => trivial⟩

theorem salt_ct (hc : SignChecks T.H.P T.H.D) (hH : HashOK T.H) :
    RelCT isa (Two fun a t => At T (EJ2 T.H) a t ∧ isa.eval .b t = some false)
      (.block (([.mov .rdx (.mem (sp sSaltLen))] : List Instr) ++ saltFits T.H)) (Two (At T (SJ6 T.H))) := by
  obtain ⟨_, hc⟩ := hc.salt
  refine two_post (stwo (T := T) (H := T.H) [40] [.rax] (fun a => [(.rax, BitVec.ofNat 64 (seml a))])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.1.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.seml]; exact h.2.1) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨⟨s, S, h⟩, hb⟩ => ?_
  obtain ⟨⟨v, hrd, hM⟩, hax, hcf⟩ := h
  have hok : T.H.D + 2 ≤ seml s := by
    rw [show isa.eval .b t = t.cf from rfl, hcf] at hb
    simp only [Option.some.injEq, decide_eq_false_iff_not] at hb; omega_using [hb]
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have hDN := hH.hDN; have hN := hH.N_le
  have L := v.L
  rw [WP.block_append_iff]
  refine X86_64.WP.mono_syms (WP.keep [.rdx] (Q := fun u => u.gpr .rdx = s.gpr .r8 ∧ u.mem = t.mem) ?_ rfl)
    fun t5 ⟨⟨hdx5, hm5⟩, k5⟩ sy5 => ?_
  · xrun [ea_sp, L.rsp, L.ld (d := sSaltLen) (by decide), R.rd (d := sSaltLen) 40 rfl (by decide),
      hw 40 (by decide)]
    rfl
  refine X86_64.WP.mono_syms (saltFits_ok (H := T.H) (by omega_using [hDN, hN]) t5 (a := seml s) (b := s.gpr .r8) hok
    (by unfold seml; omega_using [hk2]) (by rw [k5.gpr (by decide)]; exact hax) hdx5) fun t6 ⟨k6, hm6, hax6, hc6⟩ sy6 => ?_
  have hm : t6.mem = t.mem := by rw [hm6, hm5]
  exact ⟨s, S, (v.keep (k5.trans k6) hm (by decide) (fun _ hp => by cases hp) (sy6.trans sy5)).sub (by decide) []
    (fun _ hp => by cases hp) fun _ _ x => x, k6.2.1.trans (k5.2.1.trans hrd), hm ▸ hM, hax6, hc6, hok⟩

theorem copyOut_ct :
    RelCT isa (Two (At T (SE T.H KSM fun _ _ _ => True))) copyOut (Two (At T (EJR T.H))) := by
  obtain ⟨_, hc⟩ := eFixed.copyOut
  refine two_post (stwo (T := T) (H := T.H) [16, 17, 21] [] (fun _ => []) (fun a t h => se_ss h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  exact X86_64.WP.mono_syms (copyOut_ok hp v.L R v.wr (hw 16 (by decide)) (hw 17 (by decide))
    (by unfold seml at hok; omega_using [hok]))
    fun u ⟨L', k', R', _⟩ sy => ⟨s, S, v.next L' k'.2.2 R' (fun _ hk => by cases hk) trivial sy⟩

theorem ret1_ct : RelCT isa (Two (At T (EJR T.H))) (.block [.mov32 .rax (.imm 1)]) (Two (At T (EJR T.H))) := by
  obtain ⟨_, hc⟩ := eFixed.ret1
  refine two_post (stwo (T := T) (H := T.H) [] [] (fun _ => []) (fun a t ⟨s, S, v⟩ => ⟨s, _, S, v⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, v⟩ => ?_
  exact X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem) (by xrun) rfl) fun t' ⟨hm, k⟩ sy =>
    ⟨s, S, v.keep k hm (by decide) (fun _ hp => by cases hp) sy⟩

theorem restore_ct : RelCT isa (Two (At T (EJR T.H))) (.block restoreRegs) fun _ _ => True := by
  obtain ⟨_, hc⟩ := sFixed.restore
  exact stwo (T := T) (H := T.H) [] [] (fun _ => []) (fun a t ⟨s, S, v⟩ => ⟨s, _, S, v⟩) (fun _ => rfl)
    (by decide) hc

variable (hH : HashOK T.H) (K : Callees T.H) (hG : Pbkdf2.Md.X86_64.Calls.StreamOK T.G) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = T.G.D) (hGv : Proof.Mgf1.Valid Gs)
  (hf : MdFnsSafe T.f) (hg : FnsSafe T.g) (hdk : DigOK T.H) (hc : PssChecks T.H.P T.H.D)

include hH K hG hGh hGl hGv hf hg hdk hc in
theorem body_ct : RelCT isa (Two (At T J0)) (encBody T.f T.H T.g) fun _ _ => True := by
  unfold encBody encMain
  simp only [seqs]
  exact pro_ct.seq (hsl_ct.seq (gsl_ct.seq ((fit_ct hc.hash2 hH).seq ((two_ite
      (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
        rw [show isa.eval .b t₁ = t₁.cf from rfl, show isa.eval .b t₂ = t₂.cf from rfl, h₁.2.2, h₂.2.2,
          S₁.seml, S₂.seml])
      (ret0_ct (Φ := fun a t => At T (EJ2 T.H) a t ∧ isa.eval .b t = some true)
        fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
      ((salt_ct hc.sign hH).seq (two_ite
        (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
          rw [show isa.eval .b t₁ = t₁.cf from rfl, show isa.eval .b t₂ = t₂.cf from rfl, h₁.2.2.2.2.1,
            h₂.2.2.2.2.1, S₁.seml, S₂.seml, S₁.ssl, S₂.ssl])
        (ret0_ct (Φ := fun a t => At T (SJ6 T.H) a t ∧ isa.eval .b t = some true)
          fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
        ((enc_signEnc_ct hH K hdk hf hg hG hGh hGl hGv hc).seq (copyOut_ct.seq ret1_ct))))).seq restore_ct))))

include hH K hG hGh hGl hGv hf hg hdk hc in
/-- `encode` is constant time. -/
theorem enc_ct (Hs : Spec.Mgf1.Hash) :
    ConstantTime isa (encK T Hs Gs).pre (encK T Hs Gs).pub (encode T.f T.H T.g) :=
  RelCT.constantTime (valloc ((body_ct hH K hG hGh hGl hGv hf hg hdk hc).mono
    (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, e₁, e₂⟩ => ⟨s₁, ⟨s₁, ⟨Pre.of T h₁, pub_refl s₁, Pre.of T h₁⟩, e₁⟩,
      ⟨s₂, ⟨Pre.of T h₁, hpub, Pre.of T h₂⟩, e₂⟩⟩) fun _ _ h => h))

end VG.Proof.RsaPss.X86_64.Enc

end

end

/-! ### `RsaPss.X86_64.ChkCt`, which only this module used -/

section

/-!
# EMSA-PSS's check of an encoding on x86-64: constant time, and `Verified`

The prologue, the copy of the encoding, the salt length's arguments (the
branch on `any_salt_len`, which the runs' entry states agree on), the checks
of the lengths (on public values), verification's checks
(`ChkCtMid`, `ChkCtBack`, `ChkSaltBackCT`) and the epilogue, in two runs
whose entry states agree on the public data (`chk_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Chk

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {T : Tabs}

/-- The entry of the frame. -/
def J0 (s t : State) : Prop := t = allocState frameBytes s

/-- The words the prologue stores. -/
def KP0 : List Nat := [17, 21, 25, 26, 36, 37, 38]

/-- And the slots of the table of `MdHash`. -/
def KP1 : List Nat := [8, 9, 10, 17, 21, 25, 26, 36, 37, 38]

/-- And those of the table of `MdHash`. -/
def KP : List Nat := [8, 9, 10, 11, 12, 13, 14, 17, 21, 25, 26, 36, 37, 38]

/-- After the prologue: `r11` is the table `hash`. -/
def CJa (H : Hash) (s t : State) : Prop :=
  VS H s t KP0 [(.r11, stackArg s 2)] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame [frR s] s.mem t.mem ∧
    t.gpr .r9 = s.gpr .r9

/-- After its slots: `r11` is the table `mgf1`. -/
def CJb (H : Hash) (s t : State) : Prop :=
  VS H s t KP1 [(.r11, stackArg s 3)] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame [frR s] s.mem t.mem ∧
    t.gpr .r9 = s.gpr .r9

/-- After the tables' slots, and the copy. -/
def CJ1 (H : Hash) (s t : State) : Prop :=
  VS H s t KP [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧ t.gpr .r9 = s.gpr .r9

/-- After the salt length's arguments. -/
def CJ2 (H : Hash) (s t : State) : Prop :=
  VS H s t K5 [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧ t.gpr .rdx = vrdx s

/-- After `fitH`: CF set if `emLen` is too short. -/
def CJ3 (H : Hash) (s t : State) : Prop :=
  CJ2 H s t ∧ t.gpr .rax = BitVec.ofNat 64 (veml s) ∧ t.cf = some (decide (veml s < H.D + 2))

theorem pro_ct : RelCT isa (Two (VAt T J0)) (.block (chkPrologue ++ ([.mov .r11 (.mem (arg 2))] : List Instr)))
    (Two (VAt T (CJa T.H))) := by
  obtain ⟨_, hc⟩ := cFixed.pro
  have ar : ∀ (s : State) {r : Reg}, r ≠ .rsp → (allocState frameBytes s).gpr r = s.gpr r := fun s r hr => by
    rw [allocState_gpr']; exact ifn hr _ _
  refine two_post (two_pub0 1 [.rdi, .rsi, .rdx, .rcx, .r8] fb State.wr
    (fun a => [(.rdi, a.gpr .rdi), (.rsi, a.gpr .rsi), (.rdx, a.gpr .rdx), (.rcx, a.gpr .rcx), (.r8, a.gpr .r8)])
    (fun a t ⟨s, S, ht⟩ => ⟨by rw [ht, allocState_gpr', ifp rfl, ← S.fb], by rw [ht, ← S.wr, ← S.fb]; rfl,
      fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> rw [ht, ar s (by decide)] <;>
          exact S.gpr (by decide)⟩)
    (fun a t ⟨s, S, _⟩ => S.rest) (fun _ => rfl) hc) fun a t ⟨s, S, ht⟩ => ?_
  subst ht
  have hp := S.ps
  rw [WP.block_append_iff]
  refine X86_64.WP.mono_syms (chkPro_ok hp) fun t1 ⟨k1, L1, R1, f1⟩ s1 => ?_
  refine X86_64.WP.mono_syms (argR11_ok hp L1.rsp k1.2.1 f1 (j := 2) (by decide)) fun t2 ⟨k2, hm2, h11⟩ s2 =>
    ⟨s, S, ⟨L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2]), k2.2.2.trans k1.2.2,
      ⟨_, _, hm2 ▸ R1, fun k hk => ?_, trivial⟩, fun p hp => by rw [List.mem_singleton.mp hp]; exact h11,
      s2.trans s1⟩, k2.2.1.trans k1.2.1, hm2 ▸ f1, by rw [k2.gpr (by decide), k1.gpr (by decide)]; rfl⟩
  have hel := hp.hel
  simp only [KP0, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [proW', proW, upd, vw, cmask, vlo, hel]

theorem hsl_ct : RelCT isa (Two (VAt T (CJa T.H))) (.block (hSlots ++ ([.mov .r11 (.mem (arg 3))] : List Instr)))
    (Two (VAt T (CJb T.H))) := by
  obtain ⟨_, hc⟩ := cFixed.hSl
  refine two_post (vtwo (T := T) (H := T.H) [] [.r11] (fun a => [(.r11, stackArg a 2)])
    (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (fun _ hk => by cases hk) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.arg (by decide)]; exact h.1.regs _ (List.mem_singleton_self _))
      fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hf, h9⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  refine X86_64.WP.mono_syms (hSl_ok S.ps v.L R hrd hf (v.regs _ (List.mem_singleton_self _)))
    fun u ⟨k, L', h11, f', R'⟩ sy =>
    ⟨s, S, ⟨L', k.2.2.trans v.wr, ⟨_, _, R', fun j hj => ?_, trivial⟩,
      fun p hp => by rw [List.mem_singleton.mp hp]; exact h11, sy.trans v.sy⟩, k.2.1.trans hrd, f',
      (k.gpr (by decide)).trans h9⟩
  simp only [KP1, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | h | h | h | h | h | h | h
  · simp [upd, vw]
  · simp [upd, vw]
  · simp [upd, vw]
  all_goals
    simp only [upd]
    rw [ifn (by omega_using [h]), ifn (by omega_using [h]), ifn (by omega_using [h])]
    exact hw _ (by simp only [KP0, List.mem_cons, List.not_mem_nil, or_false]; omega_using [h])

theorem gsl_ct : RelCT isa (Two (VAt T (CJb T.H))) (.block gSlots) (Two (VAt T (CJ1 T.H))) := by
  obtain ⟨_, hc⟩ := cFixed.gSl
  refine two_post (vtwo (T := T) (H := T.H) [] [.r11] (fun a => [(.r11, stackArg a 3)])
    (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (fun _ hk => by cases hk) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.arg (by decide)]; exact h.1.regs _ (List.mem_singleton_self _))
      fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hf, h9⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  refine X86_64.WP.mono_syms (gSl_ok S.ps v.L R hrd hf (v.regs _ (List.mem_singleton_self _)))
    fun u ⟨k, L', f', R'⟩ sy =>
    ⟨s, S, ⟨L', k.2.2.trans v.wr, ⟨_, _, R', fun j hj => ?_, trivial⟩, (fun _ hp => by cases hp), sy.trans v.sy⟩,
      k.2.1.trans hrd, frame_wrR f', (k.gpr (by decide)).trans h9⟩
  simp only [KP, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with h | h | h | rfl | rfl | rfl | rfl | h | h | h | h | h | h | h
  rotate_left 3
  · simp [upd, vw]
  · simp [upd, vw]
  · simp [upd, vw]
  · simp [upd, vw]
  all_goals
    simp only [upd]
    rw [ifn (by omega_using [h]), ifn (by omega_using [h]), ifn (by omega_using [h]), ifn (by omega_using [h])]
    exact hw _ (by simp only [KP1, List.mem_cons, List.not_mem_nil, or_false]; omega_using [h])

theorem copyIn_ct : RelCT isa (Two (VAt T (CJ1 T.H))) copyIn (Two (VAt T (CJ1 T.H))) := by
  obtain ⟨_, hc⟩ := cFixed.copyIn
  refine two_post (vtwo (T := T) (H := T.H) [17, 21, 38] [] (fun _ => [])
    (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, h9⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  exact X86_64.WP.mono_syms (WP.keepIn (by safe_by [copyIn]) (by exact Nat.zero_le 16)
    (copyIn_ok hp v.L R v.wr hrd (hw 17 (by decide)) (hw 38 (by decide)))) fun u ⟨⟨L', k', R'⟩, f⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' hw trivial sy, k'.2.1.trans hrd, frame_keep hp v.wr v.L.rsp hM f,
      (k'.gpr (by decide)).trans h9⟩

/-- After `any_salt_len`'s test. -/
def CJZ (H : Hash) (s t : State) : Prop :=
  VS H s t [] [] (fun _ _ => True) ∧ t.zf = some (decide ((s.gpr .r9).setWidth 32 = 0))

theorem anyReg_ct : RelCT isa (Two (VAt T (CJ1 T.H))) anyReg (Two (VAt T (CJ2 T.H))) := by
  refine two_post ?_ fun a t ⟨s, S, v, hrd, hM, h9⟩ => ?_
  · obtain ⟨_, h1⟩ := cFixed.any1
    obtain ⟨_, hT⟩ := cFixed.anyT
    obtain ⟨_, hE⟩ := cFixed.anyE
    unfold anyReg
    refine (two_post (Ψ := VAt T (CJZ T.H)) (vtwo (T := T) (H := T.H) [] [] (fun _ => [])
      (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
      (fun _ => rfl) (by decide) h1) fun a t ⟨s, S, v, _, _, h9⟩ => ?_).seq (two_ite
        (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
          rw [show isa.eval .e t₁ = t₁.zf from rfl, show isa.eval .e t₂ = t₂.zf from rfl, h₁.2, h₂.2, S₁.r9, S₂.r9])
        (vtwo (T := T) (H := T.H) [] [] (fun _ => []) (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1⟩)
          (fun _ => rfl) (by decide) hT)
        (vtwo (T := T) (H := T.H) [] [] (fun _ => []) (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1⟩)
          (fun _ => rfl) (by decide) hE))
    refine X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem ∧
        t'.zf = some (decide ((s.gpr .r9).setWidth 32 = 0))) (by
      xrun [h9]
      rw [BitVec.and_self, zext32_beq_zero]) rfl) fun t' ⟨⟨hm, hz⟩, k⟩ sy =>
      ⟨s, S, (v.keep k hm (by decide) (fun _ hp => by cases hp) sy).sub (by decide) [] (fun _ hp => by cases hp)
        fun _ _ _ => trivial, hz⟩
  · obtain ⟨V, W, R, hw, -⟩ := v.W
    have hp := S.ps
    refine X86_64.WP.mono_syms (WP.keepIn (by safe_by [anyReg]) (by exact Nat.zero_le 16)
      (anyReg_ok v.L R (hw 36 (by decide)) h9)) fun u ⟨⟨L', k', R', hdx⟩, f⟩ sy =>
      ⟨s, S, v.next L' k'.2.2 R' (fun k hk => ?_) trivial sy, k'.2.1.trans hrd, frame_keep hp v.wr v.L.rsp hM f,
        by rw [hdx]; rfl⟩
    by_cases h35 : k = 35
    · subst h35; simp [upd, vw]
    simp only [upd]; rw [ifn h35]
    exact hw k ((by decide : ∀ k ∈ K5, k ≠ 35 → k ∈ KP) k hk h35)

theorem fit_ct (hc : HashChecks T.H.P T.H.D 1) (hH : HashOK T.H) :
    RelCT isa (Two (VAt T (CJ2 T.H))) (.block (fitH T.H)) (Two (VAt T (CJ3 T.H))) := by
  obtain ⟨_, hc⟩ := hc.fit
  refine two_post (vtwo (T := T) (H := T.H) [17] [] (fun _ => [])
    (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hdx⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hk2 := S.ps.k2
  have hDN := hH.hDN; have hN := hH.N_le
  refine X86_64.WP.mono_syms (fitH_ok (H := T.H) (by omega_using [hDN, hN]) v.L R (k := veml s)
    (by rw [hw 17 (by decide)]; show s.gpr .rdx = _; rw [veml, vlo, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by unfold veml; omega_using [hk2])) fun t' ⟨k', hm, hax, hcf⟩ sy =>
    ⟨s, S, ⟨v.keep k' hm (by decide) (fun _ hp => by cases hp) sy, k'.2.1.trans hrd, hm ▸ hM,
      (k'.gpr (by decide)).trans hdx⟩, hax, hcf⟩

/-- A refusal: 0. -/
theorem ret0_ct {Φ : State → State → Prop}
    (hΦ : ∀ a t, Φ a t → ∃ s X, VSib T a s ∧ VS T.H s t [] [] X) :
    RelCT isa (Two Φ) ret0 (Two (VAt T (JR T.H))) := by
  obtain ⟨_, hc⟩ := cFixed.ret0
  refine two_post (vtwo (T := T) (H := T.H) [] [] (fun _ => []) hΦ (fun _ => rfl) (by decide) hc)
    fun a t h => ?_
  obtain ⟨s, X, S, v⟩ := hΦ a t h
  refine X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem) (by xrun [ret0]) rfl)
    fun t' ⟨hm, k⟩ sy => ⟨s, S, (v.keep k hm (by decide) (fun _ hp => by cases hp) sy).sub (by decide) []
      (fun _ hp => by cases hp) fun _ _ _ => trivial⟩

theorem salt_ct (hc : VerifyChecks T.H.P T.H.D) (hH : HashOK T.H) :
    RelCT isa (Two fun a t => VAt T (CJ3 T.H) a t ∧ isa.eval .b t = some false)
      (.block (([.mov .rax (.mem (sp sK)), .mov .r8 (.mem (sp sLo)), .alu .sub .rax (.reg .r8)] : List Instr) ++
        saltFits T.H)) (Two (VAt T (J7 T.H))) := by
  obtain ⟨_, hc⟩ := hc.salt
  refine two_post (vtwo (T := T) (H := T.H) [17, 26] [.rdx] (fun a => [(.rdx, vrdx a)])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.1.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.vrdx]; exact h.1.2.2.2) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨⟨s, S, h⟩, hb⟩ => ?_
  obtain ⟨⟨v, hrd, hM, hdx⟩, hax, hcf⟩ := h
  have hok : T.H.D + 2 ≤ veml s := by
    rw [show isa.eval .b t = t.cf from rfl, hcf] at hb
    simp only [Option.some.injEq, decide_eq_false_iff_not] at hb; omega_using [hb]
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have hDN := hH.hDN; have hN := hH.N_le
  have L := v.L
  rw [WP.block_append_iff]
  refine X86_64.WP.mono_syms (WP.keep [.rax, .r8] (Q := fun u => u.gpr .rax = BitVec.ofNat 64 (veml s) ∧
    u.mem = t.mem) ?_ rfl) fun t6 ⟨⟨hax6, hm6⟩, k6⟩ sy6 => ?_
  · xrun [ea_sp, L.rsp, L.ld (d := sK) (by decide), L.ld (d := sLo) (by decide), R.rd (d := sK) 17 rfl (by decide),
      R.rd (d := sLo) 26 rfl (by decide), hw 17 (by decide), hw 26 (by decide)]
    show s.gpr .rdx - BitVec.ofNat 64 (vlo s) = BitVec.ofNat 64 ((s.gpr .rdx).toNat - vlo s)
    rw [vlo, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact BitVec.sub_zero _
  refine X86_64.WP.mono_syms (saltFits_ok (H := T.H) (by omega_using [hDN, hN]) t6 (a := veml s) (b := vrdx s) hok
    (by unfold veml; omega_using [hk2]) hax6 (by rw [k6.gpr (by decide)]; exact hdx)) fun t7 ⟨k7, hm7, hax7, hc7⟩ sy7 => ?_
  have hm : t7.mem = t.mem := by rw [hm7, hm6]
  exact ⟨s, S, v.keep (k6.trans k7) hm (by decide) (fun _ hp => by cases hp) (sy7.trans sy6),
    k7.2.1.trans (k6.2.1.trans hrd), hm ▸ hM, hax7, hc7, hok⟩

theorem dbSlots_ct : RelCT isa (Two fun a t => VAt T (J7 T.H) a t ∧ isa.eval .b t = some false) (.block dbSlots)
    (Two (VAt T (JT T.H))) := by
  obtain ⟨_, hc⟩ := cFixed.dbSlots
  refine two_post (vtwo (T := T) (H := T.H) [26] [.rax]
    (fun a => [(.rax, BitVec.ofNat 64 (veml a - (T.H.D + 2)))])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.veml]; exact h.2.2.2.1) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨⟨s, S, h⟩, _⟩ => ?_
  obtain ⟨v, hrd, hM, hax, -, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have w : ∀ k ∈ K5, W k = vw T.H s k := hw
  refine X86_64.WP.mono_syms (dbSlots_ok v.L R (w 26 (by decide)) hax) fun u1 ⟨L1, k1, R1⟩ sy =>
    ⟨s, S, ⟨v.next L1 k1.2.2 R1 (fun k hk => ?_) trivial sy, k1.2.1.trans hrd, hok⟩⟩
  by_cases h23 : k = 23
  · subst h23; simp [upd, vw]
  by_cases h24 : k = 24
  · subst h24
    simp only [upd, Nat.reduceEqDiff, ite_false, ite_true, vw, vdb]
    congr 1; omega_using [hok]
  simp only [upd]; rw [ifn h24, ifn h23]; exact w k (km_k5 hk h23 h24)

theorem restore_ct : RelCT isa (Two (VAt T (JR T.H))) (.block restoreRegs) fun _ _ => True := by
  obtain ⟨_, hc⟩ := cFixed.restore
  exact vtwo (T := T) (H := T.H) [] [] (fun _ => []) (fun a t ⟨s, S, v⟩ => ⟨s, _, S, v⟩) (fun _ => rfl)
    (by decide) hc

variable (hH : HashOK T.H) (K : Callees T.H) (hG : Pbkdf2.Md.X86_64.Calls.StreamOK T.G) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = T.G.D) (hGv : Proof.Mgf1.Valid Gs)
  (hdk : DigOK T.H) (hc : PssChecks T.H.P T.H.D)

include hH K hG hGh hGl hGv hdk hc in
theorem main_ct :
    RelCT isa (Two fun a t => VAt T (J7 T.H) a t ∧ isa.eval .b t = some false) (chkMain T.f T.H T.g)
      (Two (VAt T (JR T.H))) := by
  unfold chkMain
  simp only [seqs]
  exact dbSlots_ct.seq (acc0_ct.seq ((mgf_ct hG hGh hGl hGv hc.hash1).seq (clearTop_ct.seq
    ((scanCheck_ct hH hc.verify).seq (saltBack_ct hH K hdk hc)))))

include hH K hG hGh hGl hGv hdk hc in
theorem body_ct : RelCT isa (Two (VAt T J0)) (chkBody T.f T.H T.g) fun _ _ => True := by
  unfold chkBody
  simp only [seqs]
  exact pro_ct.seq (hsl_ct.seq (gsl_ct.seq (copyIn_ct.seq (anyReg_ct.seq ((fit_ct hc.hash1 hH).seq ((two_ite
      (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
        rw [show isa.eval .b t₁ = t₁.cf from rfl, show isa.eval .b t₂ = t₂.cf from rfl, h₁.2.2, h₂.2.2,
          S₁.veml, S₂.veml])
      (ret0_ct (Φ := fun a t => VAt T (CJ3 T.H) a t ∧ isa.eval .b t = some true)
        fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
      ((salt_ct hc.verify hH).seq (two_ite
        (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
          rw [show isa.eval .b t₁ = t₁.cf from rfl, show isa.eval .b t₂ = t₂.cf from rfl, h₁.2.2.2.2.1,
            h₂.2.2.2.2.1, S₁.veml, S₂.veml, S₁.vrdx, S₂.vrdx])
        (ret0_ct (Φ := fun a t => VAt T (J7 T.H) a t ∧ isa.eval .b t = some true)
          fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
        (main_ct hH K hG hGh hGl hGv hdk hc)))).seq restore_ct))))))

include hH K hG hGh hGl hGv hdk hc in
/-- `checkEncoding` is constant time. -/
theorem chk_ct (Hs : Spec.Mgf1.Hash) :
    ConstantTime isa (chkK T Hs Gs).pre (chkK T Hs Gs).pub (checkEncoding T.f T.H T.g) :=
  RelCT.constantTime (valloc ((body_ct hH K hG hGh hGl hGv hdk hc).mono
    (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, e₁, e₂⟩ => ⟨s₁, ⟨s₁, ⟨Pre.of T h₁, vpub_refl s₁, Pre.of T h₁⟩, e₁⟩,
      ⟨s₂, ⟨Pre.of T h₁, hpub, Pre.of T h₂⟩, e₂⟩⟩) fun _ _ h => h))

end VG.Proof.RsaPss.X86_64.Chk

end

end


/-!
# RSASSA-PSS on x86-64 with the tables of `vs`: the instances

For variants `vs` of `MdHash` that pass the checks the registrations make
(`OK`), what signing and verification need of the tables a state holds: a
table of `MdHash` of a variant `w` of `vs` and a table of `MdHash` of a
variant `w'` give the functions `tabsOf vs w w'` and the hash functions
`w.mgf.G` and `w'.mgf.G`, which every state whose public data agree also
holds, and with which `encode` and `checkEncoding` for the index of `w`'s hash
function (whose code is that of `w`, `encode_shape`) are correct and
constant time (`esel_of`, `sgood_of`, `ksel_of`, `kgood_of`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash HashOK MgfLink)
open VG.Proof.MdHashTable.X86_64 (digName idx Shape held_tableOf hashAt_tableOf htf_of mem_names)
open VG.Proof.Bignum (off)

/-- The tables' functions for the variants `w` (of the table `hash`) and `w'`
(of the table `mgf1`). -/
def tabsOf (vs : List MdHash) (w w' : MdHash) : Tabs :=
  ⟨w.U, digName w, MdHashTable.X86_64.fnsOf vs, w'.H.stream, HashTable.X86_64.fnsOf vs⟩

/-- What the registrations check of the variants whose tables the functions
take: their functions of the same name have the same code, each has the
shape of its index and each index has one, and not too many names. -/
def OK (vs : List MdHash) : Prop :=
  MdHashTable.X86_64.Coh vs ∧ HashTable.X86_64.Coh vs ∧ (∀ w ∈ vs, Shape w) ∧
    (∀ i ∈ idxs, ∃ w ∈ vs, idx w = i) ∧
    (MdHashTable.X86_64.names vs ++ HashTable.X86_64.names vs).length < 2 ^ 32

instance (vs : List MdHash) : Decidable (OK vs) := by unfold OK; infer_instance

/-! ## The code of an index -/

theorem encode_shape (f : MdFns) (g : Impl.Mgf1.X86_64.Table.Fns) {H : Impl.Pbkdf2.Md.X86_64.Hash} {i : Nat}
    (hP : H.P = (shapeOf i).1) (hD : H.D = (shapeOf i).2) : encode f (ofIdx i) g = encode f H g := by
  show encode f (ckH (shapeOf i).1 (shapeOf i).2) g = _
  rw [← hP, ← hD]
  rfl

theorem check_shape (f : MdFns) (g : Impl.Mgf1.X86_64.Table.Fns) {H : Impl.Pbkdf2.Md.X86_64.Hash} {i : Nat}
    (hP : H.P = (shapeOf i).1) (hD : H.D = (shapeOf i).2) : checkEncoding f (ofIdx i) g = checkEncoding f H g := by
  show checkEncoding f (ckH (shapeOf i).1 (shapeOf i).2) g = _
  rw [← hP, ← hD]
  rfl

/-! ## The functions the tables' calls reach -/

theorem allSafe {c : Prog isa} (h1 : c.allInstrs (fun i => !isa.writesSp i) = true)
    (h2 : c.allInstrs (fun i => !loadsMxcsr i) = true) : c.allInstrs safeI = true := by
  rw [safeI_eq, allInstrs_and, h1, h2]; rfl

theorem mdFns_safe {vs : List MdHash} (hs : ∀ w ∈ vs, Shape w) : MdFnsSafe (MdHashTable.X86_64.fnsOf vs) where
  init q hq := by
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq
    exact ⟨allSafe w.K.iSp w.K.iMx, by dsimp only; rw [w.K.iXD]⟩
  comp q hq := by
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq
    exact ⟨allSafe w.K.cSp w.K.cMx, by dsimp only; rw [w.K.cXD]⟩
  dig q hq := by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
    obtain ⟨hi, hP, -⟩ := hs w hw
    show (Impl.MdHashTable.X86_64.digest w.U.P).allInstrs safeI = true ∧
      (Impl.MdHashTable.X86_64.digest w.U.P).x86_64Depth ≤ 0
    rw [hP]
    exact dig_safe _ hi

theorem hFns_safe (vs : List MdHash) : FnsSafe (HashTable.X86_64.fnsOf vs) where
  init q hq := by
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq
    exact ⟨allSafe w.K.iSp w.K.iMx, by dsimp only; rw [w.K.iXD]; omega_using []⟩
  upd q hq := by
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq
    refine ⟨allSafe (spAll_of (RsaOaep.X86_64.SpSafe.of_noSp w.ok.updSp)) w.ok.updMx, ?_⟩
    dsimp only
    rw [x86_64Depth_noSp w.ok.updSp]
    have := w.ok.updDepth
    omega_using [this]
  fin q hq := by
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq
    refine ⟨allSafe (spAll_of (RsaOaep.X86_64.SpSafe.of_noSp w.ok.finSp)) w.ok.finMx, ?_⟩
    dsimp only
    rw [x86_64Depth_noSp w.ok.finSp]
    have := w.ok.finDepth
    omega_using [this]

theorem link_valid {H : Impl.Pbkdf2.Md.X86_64.Hash} (hH : HashOK H) (l : MgfLink H hH) : Proof.Mgf1.Valid l.G :=
  ⟨by rw [l.len]; exact hH.hD0, fun x => by
    rw [l.hash, hH.hash, List.length_take, MdStream.Md.hash, hH.md.digest_length, l.len]
    exact Nat.min_eq_left hH.hDN⟩

theorem dig_of_shape {w : MdHash} (h : Shape w) : DigOK w.U := DigOK.of_P h.2.1 (dig_shape _ h.1)

theorem pss_of_shape {w : MdHash} (h : Shape w) : PssChecks w.U.P w.U.D := by
  rw [h.2.1, h.2.2]; exact pss_shape _ h.1

variable {vs : List MdHash} (hok : OK vs)

theorem idx_lt (w : MdHash) : idx w < 2 ^ 64 := by
  have hm := w.mgf.mem
  simp only [idx]
  simp only [Proof.Pbkdf2.Md.X86_64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e | e | e <;> rw [e] <;> decide

theorem sp_of_all {c : Prog isa} (h : c.allInstrs (fun i => !isa.writesSp i) = true) : SpSafe c := by
  rw [Code.allInstrs_eq] at h
  intro i hi
  simpa using List.all_eq_true.mp h i hi

include hok in
/-- The code for each index never writes `rsp`, and uses at most `encStack`
or `chkStack` bytes of stack. -/
theorem enc_safe : ∀ i ∈ idxs, SpSafe (encode (MdHashTable.X86_64.fnsOf vs) (ofIdx i) (HashTable.X86_64.fnsOf vs)) ∧
    (encode (MdHashTable.X86_64.fnsOf vs) (ofIdx i) (HashTable.X86_64.fnsOf vs)).x86_64Depth ≤ encStack := by
  intro i hi
  obtain ⟨w, hw, rfl⟩ := hok.2.2.2.1 i hi
  have hs := hok.2.2.1 w hw
  rw [encode_shape _ _ hs.2.1 hs.2.2]
  refine ⟨sp_of_all ?_, Enc.enc_xd (T := tabsOf vs w w) (mdFns_safe hok.2.2.1) (hFns_safe vs)⟩
  exact Enc.enc_spAll (T := tabsOf vs w w) w.okU (mdFns_safe hok.2.2.1) (hFns_safe vs)

include hok in
theorem chk_safe : ∀ i ∈ idxs, SpSafe (checkEncoding (MdHashTable.X86_64.fnsOf vs) (ofIdx i) (HashTable.X86_64.fnsOf vs)) ∧
    (checkEncoding (MdHashTable.X86_64.fnsOf vs) (ofIdx i) (HashTable.X86_64.fnsOf vs)).x86_64Depth ≤ chkStack := by
  intro i hi
  obtain ⟨w, hw, rfl⟩ := hok.2.2.2.1 i hi
  have hs := hok.2.2.1 w hw
  rw [check_shape _ _ hs.2.1 hs.2.2]
  refine ⟨sp_of_all ?_, Chk.chk_xd (T := tabsOf vs w w) (mdFns_safe hok.2.2.1) (hFns_safe vs)⟩
  exact Chk.chk_spAll (T := tabsOf vs w w) w.okU (mdFns_safe hok.2.2.1) (hFns_safe vs)

/-! ## The tables a state holds -/

/-- The functions of the tables of `vs` at distinct addresses: those of the
tables of `MdHash`, and of `MdHash`. -/
theorem distinct_split {sy : String → Addr}
    (h : (tabFns (MdHashTable.X86_64.tables vs) ++ tabFns (HashTable.X86_64.tables vs)).Pairwise
      fun f g => f ≠ g → sy f ≠ sy g) :
    (MdHashTable.X86_64.names vs).Pairwise (fun f g => f ≠ g → sy f ≠ sy g) ∧
      (HashTable.X86_64.names vs).Pairwise (fun f g => f ≠ g → sy f ≠ sy g) :=
  ⟨(List.pairwise_append.mp h).1, (List.pairwise_append.mp h).2.1⟩

/-- Two states whose names of the tables' functions agree, holding the tables
of `w` and `w'`, have the same words of them. -/
theorem tabWords_eq {s a : State} {pH pG : Addr} {pH' pG' : Addr} {w w' : MdHash} (hw : w ∈ vs) (hw' : w' ∈ vs)
    (hsy : ∀ f ∈ tabFns (MdHashTable.X86_64.tables vs) ++ tabFns (HashTable.X86_64.tables vs), a.syms f = s.syms f)
    (hs : Abi.tableHeld 64 s.mem pH (FnTable.words isa s (MdHashTable.X86_64.tableOf w)))
    (hs' : Abi.tableHeld 64 s.mem pG (FnTable.words isa s (HashTable.X86_64.tableOf w')))
    (ha : Abi.tableHeld 64 a.mem pH' (FnTable.words isa a (MdHashTable.X86_64.tableOf w)))
    (ha' : Abi.tableHeld 64 a.mem pG' (FnTable.words isa a (HashTable.X86_64.tableOf w'))) :
    tabWords s.mem pH pG = tabWords a.mem pH' pG' := by
  obtain ⟨s0, s3, s4, -⟩ := held_tableOf hs
  obtain ⟨a0, a3, a4, -⟩ := held_tableOf ha
  obtain ⟨⟨t0, t1, t2⟩, -, t4⟩ := HashTable.X86_64.held_tableOf hs'
  obtain ⟨⟨b0, b1, b2⟩, -, b4⟩ := HashTable.X86_64.held_tableOf ha'
  have n := mem_names hw
  have n' := HashTable.X86_64.mem_names hw'
  have e : ∀ f, f ∈ MdHashTable.X86_64.names vs → a.syms f = s.syms f := fun f hf =>
    hsy f (List.mem_append_left _ hf)
  have e' : ∀ f, f ∈ HashTable.X86_64.names vs → a.syms f = s.syms f := fun f hf =>
    hsy f (List.mem_append_right _ hf)
  have t0' : s.mem.readW (off pG 0) 64 = _ := t0
  have t1' : s.mem.readW (off pG 8) 64 = _ := t1
  have t2' : s.mem.readW (off pG 16) 64 = _ := t2
  have b0' : a.mem.readW (off pG' 0) 64 = _ := b0
  have b1' : a.mem.readW (off pG' 8) 64 = _ := b1
  have b2' : a.mem.readW (off pG' 16) 64 = _ := b2
  simp only [tabWords, s0, s3, s4, a0, a3, a4, t0', t1', t2', b0', b1', b2', t4, b4, e _ n.1, e _ n.2.2.2.1,
    e _ n.2.2.2.2, e' w'.H.stream.initN n'.1, e' w'.H.stream.updN n'.2.1, e' w'.H.stream.finN n'.2.2]

include hok in
/-- What encoding needs of the tables of `w` and `w'`, in a state that holds
them at the stack arguments 16 and 17. -/
theorem esel_of {s : State} {w w' : MdHash} (hw : w ∈ vs) (hw' : w' ∈ vs)
    (hsy : (tabFns (MdHashTable.X86_64.tables vs) ++ tabFns (HashTable.X86_64.tables vs)).Pairwise
      fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hdl : Spec.RsaPss.digestLenOk 64 s.mem (stackArg s 16) (stackArg s 11))
    (hH : Abi.tableHeld 64 s.mem (stackArg s 16) (FnTable.words isa s (MdHashTable.X86_64.tableOf w)))
    (hG : Abi.tableHeld 64 s.mem (stackArg s 17) (FnTable.words isa s (HashTable.X86_64.tableOf w'))) :
    ESel (MdHashTable.X86_64.fnsOf vs) (HashTable.X86_64.fnsOf vs) s (idx w) (tabsOf vs w w') w.mgf.G w'.mgf.G := by
  obtain ⟨h0, h3, h4, h5, -⟩ := held_tableOf hH
  obtain ⟨⟨g0, g1, g2⟩, g3, g4⟩ := HashTable.X86_64.held_tableOf hG
  have hs := hok.2.2.1 w hw
  obtain ⟨d, d'⟩ := distinct_split hsy
  have hA := hashAt_tableOf h5
  have t := HashTable.X86_64.tabOK_of hok.2.1 d' hw'
  refine ⟨hs.1, h5, ⟨h0, h3, h4, g0, g1, g2, g4, htf_of hok.1 d hw, ⟨t.i, t.u, t.f⟩⟩, hA,
    HashTable.X86_64.hashAt_tableOf g3, ((hdl _ hA).trans w.mgf.len).symm, fun s' h => ?_⟩
  rw [encode_shape _ _ hs.2.1 hs.2.2]
  exact Enc.enc_correct (T := tabsOf vs w w') w.okU w.KU w'.ok.stream w'.mgf.hash w'.mgf.len (link_valid w'.ok w'.mgf)
    (mdFns_safe hok.2.2.1) (hFns_safe vs) (dig_of_shape hs) w.mgfU s' h

include hok in
/-- What verification needs of the tables of `w` and `w'`, in a state that
holds them at the stack arguments 8 and 9. -/
theorem ksel_of {s : State} {w w' : MdHash} (hw : w ∈ vs) (hw' : w' ∈ vs)
    (hsy : (tabFns (MdHashTable.X86_64.tables vs) ++ tabFns (HashTable.X86_64.tables vs)).Pairwise
      fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hdl : Spec.RsaPss.digestLenOk 64 s.mem (stackArg s 8) (s.gpr .r9))
    (hH : Abi.tableHeld 64 s.mem (stackArg s 8) (FnTable.words isa s (MdHashTable.X86_64.tableOf w)))
    (hG : Abi.tableHeld 64 s.mem (stackArg s 9) (FnTable.words isa s (HashTable.X86_64.tableOf w'))) :
    Pc.KSel (MdHashTable.X86_64.fnsOf vs) (HashTable.X86_64.fnsOf vs) s (idx w) (tabsOf vs w w') w.mgf.G
      w'.mgf.G := by
  obtain ⟨h0, h3, h4, h5, -⟩ := held_tableOf hH
  obtain ⟨⟨g0, g1, g2⟩, g3, g4⟩ := HashTable.X86_64.held_tableOf hG
  have hs := hok.2.2.1 w hw
  obtain ⟨d, d'⟩ := distinct_split hsy
  have hA := hashAt_tableOf h5
  have t := HashTable.X86_64.tabOK_of hok.2.1 d' hw'
  refine ⟨hs.1, h5, ⟨h0, h3, h4, g0, g1, g2, g4, htf_of hok.1 d hw, ⟨t.i, t.u, t.f⟩⟩, hA,
    HashTable.X86_64.hashAt_tableOf g3, ((hdl _ hA).trans w.mgf.len).symm, fun s' h => ?_⟩
  rw [check_shape _ _ hs.2.1 hs.2.2]
  exact Chk.chk_correct (T := tabsOf vs w w') w.okU w.KU w'.ok.stream w'.mgf.hash w'.mgf.len (link_valid w'.ok w'.mgf)
    (mdFns_safe hok.2.2.1) (hFns_safe vs) (dig_of_shape hs) w.mgfU s' h

theorem tidx_read {m : Mem} {p : Addr} {s : State} {w : MdHash}
    (h : Abi.tableHeld 64 m p (FnTable.words isa s (MdHashTable.X86_64.tableOf w))) :
    (m.readW (off p 40) 64).toNat = idx w := by
  rw [(held_tableOf h).2.2.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (idx_lt w)]

include hok in
/-- Signing's: the tables of the first run's entry state `a`, which every
state whose public data agree with it holds. -/
theorem sgood_of {a : State}
    (hp : SPre (MdHashTable.X86_64.tables vs) (HashTable.X86_64.tables vs) a) :
    ∃ T Hs Gs, SGood (tsH := MdHashTable.X86_64.tables vs) (tsG := HashTable.X86_64.tables vs)
      (MdHashTable.X86_64.fnsOf vs) (HashTable.X86_64.fnsOf vs) a T Hs Gs := by
  obtain ⟨_, hT, hwa⟩ := hp.tabH
  obtain ⟨w, wm, rfl⟩ := List.mem_map.mp hT
  obtain ⟨_, hT', hwa'⟩ := hp.tabG
  obtain ⟨w', wm', rfl⟩ := List.mem_map.mp hT'
  have hs := hok.2.2.1 w wm
  have hidx : sidx a = idx w := tidx_read hwa
  refine ⟨tabsOf vs w w', w.mgf.G, w'.mgf.G, ⟨fun s hpub hps => ?_, fun s hpub hps => ?_, ?_⟩⟩
  · rw [hidx]
    exact esel_of hok wm wm' hps.hsy hps.hdl ((hpub.2.2.2.2.2.1 _ hT).mp hwa) ((hpub.2.2.2.2.2.2 _ hT').mp hwa')
  · exact tabWords_eq wm wm' hpub.2.2.2.2.1 ((hpub.2.2.2.2.2.1 _ hT).mp hwa) ((hpub.2.2.2.2.2.2 _ hT').mp hwa')
      hwa hwa'
  · rw [hidx, encode_shape _ _ hs.2.1 hs.2.2]
    exact Enc.enc_ct (T := tabsOf vs w w') w.okU w.KU w'.ok.stream w'.mgf.hash w'.mgf.len (link_valid w'.ok w'.mgf)
      (mdFns_safe hok.2.2.1) (hFns_safe vs) (dig_of_shape hs) (pss_of_shape hs) w.mgf.G

include hok in
/-- Verification's. -/
theorem kgood_of {a : State} (ha : Pc.Pre (MdHashTable.X86_64.tables vs) (HashTable.X86_64.tables vs) a) :
    ∃ T Hs Gs, Pc.KGood (tsH := MdHashTable.X86_64.tables vs) (tsG := HashTable.X86_64.tables vs)
      (MdHashTable.X86_64.fnsOf vs) (HashTable.X86_64.fnsOf vs) a T Hs Gs := by
  obtain ⟨_, hT, hwa⟩ := ha.tabH
  obtain ⟨w, wm, rfl⟩ := List.mem_map.mp hT
  obtain ⟨_, hT', hwa'⟩ := ha.tabG
  obtain ⟨w', wm', rfl⟩ := List.mem_map.mp hT'
  have hs := hok.2.2.1 w wm
  have hidx : Pc.vidx a = idx w := tidx_read hwa
  have hH : ∀ s, (verifyK (MdHashTable.X86_64.tables vs) (HashTable.X86_64.tables vs)).pub a s →
      Abi.tableHeld 64 s.mem (stackArg s 8) (FnTable.words isa s (MdHashTable.X86_64.tableOf w)) := fun s hpub =>
    (hpub.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ hT).mp hwa
  have hG : ∀ s, (verifyK (MdHashTable.X86_64.tables vs) (HashTable.X86_64.tables vs)).pub a s →
      Abi.tableHeld 64 s.mem (stackArg s 9) (FnTable.words isa s (HashTable.X86_64.tableOf w')) := fun s hpub =>
    (hpub.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ hT').mp hwa'
  refine ⟨tabsOf vs w w', w.mgf.G, w'.mgf.G, ⟨fun s hpub hps => ?_, fun s hpub hps => ?_, ?_⟩⟩
  · rw [hidx]
    exact ksel_of hok wm wm' hps.hsy hps.hdl (hH s hpub) (hG s hpub)
  · exact tabWords_eq wm wm' hpub.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (hH s hpub) (hG s hpub) hwa hwa'
  · rw [hidx, check_shape _ _ hs.2.1 hs.2.2]
    exact Chk.chk_ct (T := tabsOf vs w w') w.okU w.KU w'.ok.stream w'.mgf.hash w'.mgf.len (link_valid w'.ok w'.mgf)
      (dig_of_shape hs) (pss_of_shape hs) w.mgf.G

end VG.Proof.RsaPss.X86_64
