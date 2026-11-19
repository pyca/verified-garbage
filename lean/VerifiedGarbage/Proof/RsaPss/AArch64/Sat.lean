module

public import VerifiedGarbage.Proof.RsaPss.AArch64.SignPVerified
public import VerifiedGarbage.Proof.RsaPss.AArch64.Instances
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.RsaPss.AArch64.MgfCT
import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignPVerified
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.RelSplit
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.RsaPss.AArch64.MgfCT
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame
meta import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Proof.RsaPss.AArch64.Shapes
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.PrecomputedCorrect
meta import VerifiedGarbage.Proof.RsaPss.AArch64.Shapes
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.PrecomputedCorrect
import VerifiedGarbage.Proof.RsaPss.AArch64.SignSpec
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignSpec
import VerifiedGarbage.Proof.RsaPss.AArch64.EncCT
meta import VerifiedGarbage.Proof.RsaPss.AArch64.EncCT

/-! ### `RsaPss.AArch64.VerifyCCt`, which only this module used -/

section

/-! ### `RsaPss.AArch64.VerifyCTBase`, which this module and modules that import it used -/

section

/-! ### `RsaPss.AArch64.VerifyCTop`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS verification on AArch64, calling `checkEncoding`: correctness

`code_ok`: from the precondition, `verifyC` keeps the calling convention,
and, if `pre` holds the modulus' values, returns 1 exactly when
`RsaPss.verify` says (`Post`): the prologue (`prologue_ok`), the check of
the modulus' first byte, `emBits` and the public operation's arguments
(`emBitsB_ok`, `pubArgs_ok`), its call (`call_ok`), `checkEncoding`'s
arguments and its call for the index of the table of `MdHash` (`chkArgs_ok`,
`byIdx_wp`, `chkCall_ok`), and the result's AND with the leading byte's
check (`verifyOut_enc`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (wp_nil wp_and wp_movz eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.RsaPss.AArch64 (off emBitsB_ok restore_frame_ok byIdx_wp Tabs)
open VG.Proof.RsaPss.AArch64.Sgn (stk kR fb frame_sub frame_sub0 setWidth_byte)

/-- Verifying's result, if `pre` holds the modulus' values, and the calling
convention. -/
def Post (Hs Gs : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ (Cons s → (s'.gpr .x0).setWidth 32 = if verifyOut Hs Gs s then 1 else 0)

/-- Before the checks. -/
theorem fail_ok {s t : State} (hm : Mid s t) :
    WP isa verifyFail t fun t' => Mid s t' ∧ (t'.gpr .x0).setWidth 32 = 0 := by
  unfold verifyFail movi
  exact wp_movz fun w o e => wp_nil ⟨⟨by rw [o.sp, hm.sp], by rw [o.rd, hm.rd], by rw [o.wr, hm.wr],
    fun r hr => by rw [o.vcs r hr, hm.v r hr], by rw [o.mem]; exact hm.fr⟩, by rw [e]; rfl⟩

theorem and_flags (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then (1 : BitVec 32) else 0) &&& (if q then (1 : BitVec 64) else 0).setWidth 32) =
      if q ∧ p then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- `emBits`, `emLen` and `lo`, and the public operation's arguments. -/
theorem pubArgsC_ok {tsH tsG : List FnTable} {K : Nat} {s u : State} (hp : PreV tsH tsG K s) (hu : AtChk s u) (h0 : s.mem (s.gpr .x0) ≠ 0) :
    WP isa (.block (emBitsB ++ pubArgsC)) u (AtCall s (ebS s) (elS s) (loS s)) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hx := (s.mem (s.gpr .x0)).isLt
  have h0' : (s.mem (s.gpr .x0)).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  have hx10 : u.gpr .x10 = BitVec.ofNat 64 (s.mem (s.gpr .x0)).toNat := by rw [hu.x10, setWidth_byte]
  rw [WP.block_append_iff]
  refine WP.mono (emBitsB_ok (by omega_using [hk1]) hk2 hx h0' hx10 (by rw [hu.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]))
    fun u₁ ⟨O₁, x24, x25, x26⟩ => ?_
  have hpc : PreCall s (ebS s) (elS s) (loS s) u₁ := {
    sp := O₁.sp.trans hu.sp
    rd := O₁.rd.trans hu.rd
    wr := O₁.wr.trans hu.wr
    x20 := (O₁.get .x20).trans hu.x20
    x23 := (O₁.get .x23).trans hu.x23
    x24 := x24
    x25 := x25
    x26 := x26
    x27 := (O₁.get .x27).trans hu.x27
    v := fun r hr => (O₁.vcs r hr).trans (hu.v r hr)
    mem := by rw [O₁.mem]; exact hu.mem
    fr := by rw [O₁.mem]; exact hu.fr }
  exact pubArgs_ok hpc

section
variable {f : MdFns} {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {tsH tsG : List FnTable} (c : PdChecked) {K : Nat}
  (h624 : 624 ≤ K) (hcK : c.stack ≤ K)

include h624 hcK in
/-- After the check of the modulus' first byte: the public operation, the
check of the encoding, and the AND. -/
theorem main_ok {s u : State} (hp : PreV tsH tsG K s) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
    (E : CSel f g tsH tsG s i T Hs Gs) (hu : AtChk s u) (hsy : u.syms = s.syms) (h0 : s.mem (s.gpr .x0) ≠ 0) :
    WP isa (seqs [.block (emBitsB ++ pubArgsC), .call c.name c.code, .block chkArgs,
      byIdx (fun i => .call (chkName i) (checkEncoding f (ofIdx i) g)) idxs,
      .block [.logic .and .x .x0 .x0 .x26]]) u fun t => Mid s t ∧
      (Cons s → (t.gpr .x0).setWidth 32 = if verifyOut Hs Gs s then 1 else 0) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  obtain ⟨-, -, -, hlo⟩ := eb_bounds hk1 hk2 h0
  unfold seqs seqs seqs seqs
  refine WP.seq (WP.mono_syms (pubArgsC_ok hp hu h0) fun t ht sy => ?_)
  refine WP.seq (WP.mono_syms (call_ok c hp hcK ht) fun t₂ ht₂ sy₂ => ?_)
  refine WP.seq (WP.mono_syms (chkArgs_ok hp h0 ht₂) fun t₃ ht₃ sy₃ => ?_)
  refine WP.seq (byIdx_wp E.mem (fun j hj => by unfold idxs at hj; simp at hj; omega_using [hj]) (ht₃.x27.trans E.idx)
    fun t' o sy' => WP.mono (chkCall_ok hp h624 E h0 (ht₃.only9 o) (by rw [sy', sy₃, sy₂, sy, hsy]))
      fun t₄ ht₄ => ?_)
  refine wp_and fun t₅ o₅ e₅ => wp_nil ⟨⟨by rw [o₅.sp, ht₄.sp], by rw [o₅.rd, ht₄.rd], by rw [o₅.wr, ht₄.wr],
    fun r hr => by rw [o₅.vcs r hr, ht₄.v r hr], by rw [o₅.mem]; exact ht₄.fr⟩, fun hc => ?_⟩
  rw [e₅, BitVec.setWidth_and, ht₄.x0 hc, ht₄.x26 hc, and_flags, verifyOut_enc Hs Gs hk1 hk2 h0,
    take_zeros hlo (by rw [pubX_length]; omega_using [hk1])]
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]

include h624 hcK in
/-- After the prologue: the check of the modulus' first byte, then 0 or
`main_ok`. -/
theorem body_ok {s u : State} (hp : PreV tsH tsG K s) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
    (E : CSel f g tsH tsG s i T Hs Gs) (hu : AtChk s u) (hsy : u.syms = s.syms) :
    WP isa (.ite (.zero .x .x10) verifyFail (seqs [.block (emBitsB ++ pubArgsC), .call c.name c.code,
      .block chkArgs, byIdx (fun i => .call (chkName i) (checkEncoding f (ofIdx i) g)) idxs,
      .block [.logic .and .x .x0 .x0 .x26]])) u fun t => Mid s t ∧
      (Cons s → (t.gpr .x0).setWidth 32 = if verifyOut Hs Gs s then 1 else 0) := by
  have hk1 := hp.k1
  have hx10 : u.gpr .x10 = BitVec.ofNat 64 (s.mem (s.gpr .x0)).toNat := by rw [hu.x10, setWidth_byte]
  refine WP.ite _ (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · have h0 : s.mem (s.gpr .x0) = 0 := by
      rw [hx10, beq_iff_eq] at hb
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat hb
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (s.mem (s.gpr .x0)).isLt; omega_using [])] at this
      exact this
    exact WP.mono (fail_ok ⟨hu.sp, hu.rd, hu.wr, hu.v, hu.fr⟩) fun t ⟨m, r⟩ =>
      ⟨m, fun _ => by rw [verifyOut_zero Hs Gs (by omega_using [hk1]) h0, r]; rfl⟩
  have h0 : s.mem (s.gpr .x0) ≠ 0 := fun h => by rw [hx10, h] at hb; exact absurd hb (by decide)
  exact main_ok c h624 hcK hp E hu hsy h0

include h624 hcK in
theorem code_ok {s : State} (hp : PreV tsH tsG K s) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
    (E : CSel f g tsH tsG s i T Hs Gs) :
    WP isa (verifyC f g c.name c.code) s (Post Hs Gs s) := by
  unfold verifyC
  refine WP.alloc (by decide) (by have := hp.sp1; unfold stk at this; omega_using [this]) ?_
  unfold verifyCBody seqs seqs seqs
  refine WP.seq (WP.mono_syms (prologue_ok hp (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
    (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])) fun u hu sy => ?_)
  refine WP.seq (WP.mono (body_ok c h624 hcK hp E hu (by rw [sy]; simp [allocated])) fun t ⟨m, r⟩ => ?_)
  exact WP.mono (restore_frame_ok m.sp m.wr m.v m.fr.sv) fun w ⟨habi, hx0, _⟩ _ _ _ =>
    ⟨⟨habi.1, habi.2.1, habi.2.2⟩, fun hc => by dsimp only; rw [hx0]; exact r hc⟩

end

end VG.Proof.RsaPss.AArch64.Vfy

end

end

/-!
# RSASSA-PSS verification on AArch64: constant time, the public data

The pointers, the lengths, the bytes of `n` and `e` and the precomputed
values are public (`PubV`, from `verifyPrecomputedMdTableContract.pub`); the
digest and the signature are secret. Two runs with the same public data as an
anchor `a` (`E`) are related at each point of the code by what correctness
says there; a failed check of the modulus' first byte returns 0
(`vfail_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPkcs1Sig.AArch64 (Two two_taint two_post)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.RsaPss.AArch64 (pins_nil)
open VG.Proof.RsaPss.AArch64.Sgn (fb bytesAt_cons)

/-! ## The public data -/

/-- The public data of an entry state `s` is the anchor `a`'s: the
pointers and lengths, the bytes of `n` and `e`, and the precomputed values. -/
structure PubV (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ argRegs, s.gpr r = a.gpr r
  a1 : (stackArg s 1).setWidth 32 = (stackArg a 1).setWidth 32
  args : ∀ i < 8, i ≠ 1 → stackArg s i = stackArg a i
  bn : Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x0) (a.gpr .x1).toNat
  be : Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x2) (a.gpr .x3).toNat
  w : Spec.Rsa.wordsAt s.mem (stackArg s 4) (stackArg s 5).toNat =
    Spec.Rsa.wordsAt a.mem (stackArg a 4) (stackArg a 5).toNat

theorem PubV.refl (s : State) : PubV s s :=
  ⟨rfl, fun _ _ => rfl, rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩

theorem leak_eq2 {a b a' b' : List Byte} (ha : a.length = a'.length)
    (h : (a ++ b).map (·.toNat) = (a' ++ b').map (·.toNat)) : a = a' ∧ b = b' :=
  List.append_inj ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h) ha

/-- An entry state with the anchor's public data. -/
def E (tsH tsG : List FnTable) (K : Nat) (a s : State) : Prop := PreV tsH tsG K s ∧ PubV a s

namespace E
variable {tsH tsG : List FnTable} {K : Nat} {a s : State} (h : E tsH tsG K a s)
include h

theorem gpr {r : Reg} (hr : r ∈ argRegs) : s.gpr r = a.gpr r := h.2.g r hr

theorem fb : fb s = fb a := by show s.sp - _ = a.sp - _; rw [h.2.sp]

theorem scr : scr s = scr a := h.2.args 2 (by decide) (by decide)

theorem n0 : s.mem (s.gpr .x0) = a.mem (a.gpr .x0) := by
  have hk := h.1.k1
  have e1 := h.gpr (r := .x1) (by decide)
  have := h.2.bn
  rw [bytesAt_cons s.mem (s.gpr .x0) (k := (s.gpr .x1).toNat) (by omega_using [hk]),
    bytesAt_cons a.mem (a.gpr .x0) (k := (a.gpr .x1).toNat) (by rw [← e1]; omega_using [hk])] at this
  exact (List.cons.inj this).1

theorem any : anyV s = anyV a := by rw [anyV, anyV, h.2.a1]

end E

/-! ## A failed check -/

/-- 0 returned. -/
theorem vfail_ct {tsH tsG : List FnTable} {K : Nat} {Φ : State → State → Prop}
    (hΦ : ∀ a u, Φ a u → ∃ s, E tsH tsG K a s ∧ Mid s u) :
    RelCT isa (Two Φ) verifyFail (Two fun a t => t.sp = fb a) :=
  two_post (two_taint [] (pins_nil fun a s₁ s₂ h₁ h₂ => by
      obtain ⟨_, e₁, m₁⟩ := hΦ a s₁ h₁
      obtain ⟨_, e₂, m₂⟩ := hΦ a s₂ h₂
      rw [m₁.sp, m₂.sp, e₁.fb, e₂.fb]) (by taint_decide))
    fun a u h => by
      obtain ⟨s, e, m⟩ := hΦ a u h
      exact WP.mono (fail_ok m) fun t ⟨m', _⟩ => by rw [m'.sp, e.fb]

end VG.Proof.RsaPss.AArch64.Vfy

end

end

/-!
# RSASSA-PSS verification on AArch64, calling `checkEncoding`: constant time

`code_ct`: two runs of `verifyC` from entry states with the same public data
leak the same trace. The check of the modulus' first byte, `emBits` and the
arguments are on public values (the taint analysis); the calls of the
precomputed public operation and of `checkEncoding` are related by their
callees' contracts (`call_ct`, `chk_ct`), the latter chosen by the table's
index, the same in both runs (`byIdx_ct`), whose tables name the same
functions (`CSel`); the leading byte is only ANDed into the result.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero wp_and wp_nil)
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked Two two_taint two_post two_ite two_alloc two_mono pdCallCT wp_ldrSp)
open VG.Proof.RsaPss.AArch64 (byIdx_ct Tabs)
open VG.Proof.RsaPss.AArch64.Sgn (kR fb frame_sub0 stackArgAddr_fb wp_and callEntry_gpr eval_zero_w)

namespace E
variable {tsH tsG : List FnTable} {K : Nat} {a s : State} (h : E tsH tsG K a s)
include h

theorem eb : ebS s = ebS a := by unfold ebS; rw [h.n0, h.gpr (r := .x1) (by decide)]

theorem el : elS s = elS a := by unfold elS; rw [h.eb]

theorem lo : loS s = loS a := by unfold loS; rw [h.el, h.gpr (r := .x1) (by decide)]

theorem cw : cwV s = cwV a := by unfold cwV; rw [h.gpr (r := .x1) (by decide)]

end E

/-- A buffer of the caller, apart from the stack. -/
theorem bytes_f {K : Nat} {s : State} {m : Mem} (hf : Frame [⟨fb s, frameBytes⟩] s.mem m) {p : Addr} {len : Nat}
    (hk : (kR K s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact (hk.sub_left (frame_sub0 K s)).symm) hl (List.mem_range.mp hi)

/-- Words of the caller, apart from the stack. -/
theorem words_f {K : Nat} {s : State} {m : Mem} (hf : Frame [⟨fb s, frameBytes⟩] s.mem m) {p : Addr} {n : Nat}
    (hk : (kR K s).Disjoint ⟨p, n * 8⟩) (hl : p.toNat + n * 8 ≤ 2 ^ 64) :
    Spec.Rsa.wordsAt m p n = Spec.Rsa.wordsAt s.mem p n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => hf.readW (r := ⟨p, n * 8⟩) ?_ (fun r hr => ?_) (by decide)
  · have := List.mem_range.mp hi
    exact Offset.contains_base _ (by omega_using [this]) (by omega_using [hl, this])
  · rw [List.mem_singleton.mp hr]; exact (hk.sub_left (frame_sub0 K s)).symm

/-! ## The precomputed public operation -/

theorem call_ct (c : PdChecked) {tsH tsG : List FnTable} {K : Nat} (hcK : c.stack ≤ K) :
    RelCT isa (Two fun a t => ∃ s, E tsH tsG K a s ∧ s.mem (s.gpr .x0) ≠ 0 ∧ AtCall s (ebS s) (elS s) (loS s) t)
      (.call c.name c.code) fun _ _ => True := by
  refine pdCallCT c fun t₁ t₂ ⟨a, ⟨s₁, h₁, _, c₁⟩, ⟨s₂, h₂, _, c₂⟩⟩ => ?_
  have e : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r := fun r hr => (h₁.gpr hr).trans (h₂.gpr hr).symm
  have g : ∀ i < 8, i ≠ 1 → stackArg s₁ i = stackArg s₂ i := fun i h h' =>
    (h₁.2.args i h h').trans (h₂.2.args i h h').symm
  refine ⟨pdOk_of c h₁.1 hcK c₁, pdOk_of c h₂.1 hcK c₂, ⟨?_, fun r hr => ?_, fun i hi => ?_⟩, ?_, ?_⟩
  · rw [c₁.sp, c₂.sp, h₁.fb, h₂.fb]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.x0, c₂.x0, h₁.scr, h₂.scr]
    · rw [c₁.x1, c₂.x1, e .x1 (by decide)]
    · rw [c₁.x2, c₂.x2, g 4 (by decide) (by decide)]
    · rw [c₁.x3, c₂.x3, g 5 (by decide) (by decide)]
    · rw [c₁.x4, c₂.x4, e .x2 (by decide)]
    · rw [c₁.x5, c₂.x5, e .x3 (by decide)]
    · rw [c₁.x6, c₂.x6, e .x6 (by decide)]
    · rw [c₁.x7, c₂.x7, e .x1 (by decide)]
  · rcases (by omega_using [hi] : i = 0 ∨ i = 1) with rfl | rfl
    · rw [c₁.a0, c₂.a0, h₁.scr, h₂.scr]
    · rw [c₁.a1, c₂.a1, g 3 (by decide) (by decide)]
  · rw [c₁.x2, c₁.x3, c₂.x2, c₂.x3, words_f c₁.mem h₁.1.kP h₁.1.wP, words_f c₂.mem h₂.1.kP h₂.1.wP, h₁.2.w, h₂.2.w]
  · rw [c₁.x4, c₁.x5, c₂.x4, c₂.x5, bytes_f c₁.mem h₁.1.ke (by have := h₁.1.we; omega_using []),
      bytes_f c₂.mem h₂.1.ke (by have := h₂.1.we; omega_using []), h₁.2.be, h₂.2.be]

/-- An entry state with the anchor's public data, whose tables name the
functions `T` (and hash functions `Hs`, `Gs`) at the anchor's addresses,
for the index `i`. -/
abbrev ES (f : MdFns) (g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns) (tsH tsG : List FnTable) (K i : Nat) (T : Tabs)
    (Hs Gs : Spec.Mgf1.Hash) (a s : State) : Prop :=
  E tsH tsG K a s ∧ CSel f g tsH tsG s i T Hs Gs ∧ ∀ n ∈ T.names, s.syms n = a.syms n

section
variable {f : MdFns} {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {tsH tsG : List FnTable} (c : PdChecked) {K : Nat}
  (h624 : 624 ≤ K) (hcK : c.stack ≤ K) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
  (hv : ∀ s', (Chk.chkK T Hs Gs).pre s' → ∃ t s'', Exec isa (checkEncoding f (ofIdx i) g) s' t s'' ∧
    abiPreserved s' s'' ∧ (Chk.chkK T Hs Gs).post s' s'')
  (hct : ConstantTime isa (Chk.chkK T Hs Gs).pre (Chk.chkK T Hs Gs).pub (checkEncoding f (ofIdx i) g))

/-! ## `checkEncoding` -/

include h624 hv hct in
/-- Two calls of `checkEncoding` from runs with the same public data. -/
theorem chk_ct :
    RelCT isa (Two fun a t => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ s.mem (s.gpr .x0) ≠ 0 ∧ AtChkC K s t ∧
        t.syms = s.syms)
      (.call (chkName i) (checkEncoding f (ofIdx i) g))
      (Two fun a t => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ AfterChkC Hs Gs K s t) := by
  refine two_post (RelCT.callEx (k := Chk.chkK T Hs Gs) hv hct
    fun t₁ t₂ ⟨a, ⟨s₁, h₁, z₁, j₁, y₁⟩, ⟨s₂, h₂, z₂, j₂, y₂⟩⟩ => ?_) fun a t ⟨s, h, z, j, y⟩ => ?_
  · obtain ⟨r₁, w₁⟩ := chkCovers h₁.1.1 h₁.2.1 z₁ j₁
    obtain ⟨r₂, w₂⟩ := chkCovers h₂.1.1 h₂.2.1 z₂ j₂
    refine ⟨_, _, _, _, chkPre_of h₁.1.1 h624 h₁.2.1 z₁ j₁ y₁, chkPre_of h₂.1.1 h624 h₂.2.1 z₂ j₂ y₂,
      ⟨⟨?_, fun r hr => ?_, ?_, fun j hj => ?_⟩, fun n hn => ?_⟩,
      Covers.append_left r₁ (Covers.right w₁), w₁, Covers.append_left r₂ (Covers.right w₂), w₂⟩
    · show t₂.sp = t₁.sp
      rw [j₁.sp, j₂.sp, h₁.1.fb, h₂.1.fb]
    · simp only [State.withRegions_gpr]
      have hr' : r ∈ argRegs := by
        simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with h | h | h | h | h | h | h <;> simp [h]
      rw [callEntry_gpr hr', callEntry_gpr hr']
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [j₁.x0, j₂.x0, h₁.1.gpr (by decide), h₂.1.gpr (by decide)]
      · rw [j₁.x1, j₂.x1, h₁.1.scr, h₂.1.scr, h₁.1.lo, h₂.1.lo]
      · rw [j₁.x2, j₂.x2, h₁.1.el, h₂.1.el]
      · rw [j₁.x3, j₂.x3, h₁.1.eb, h₂.1.eb]
      · rw [j₁.x4, j₂.x4, h₁.1.2.args 0 (by decide) (by decide), h₂.1.2.args 0 (by decide) (by decide)]
      · rw [j₁.x6, j₂.x6, h₁.1.scr, h₂.1.scr, h₁.1.cw, h₂.1.cw]
      · rw [j₁.x7, j₂.x7, h₁.1.2.args 3 (by decide) (by decide), h₂.1.2.args 3 (by decide) (by decide),
          h₁.1.cw, h₂.1.cw]
    · simp only [State.withRegions_gpr]
      rw [callEntry_gpr (by decide), callEntry_gpr (by decide), j₁.x5, j₂.x5, h₁.1.any, h₂.1.any]
    · show stackArg t₂ j = stackArg t₁ j
      rcases (by omega_using [hj] : j = 0 ∨ j = 1) with rfl | rfl
      · rw [j₁.a0, j₂.a0, h₁.1.2.args 6 (by decide) (by decide), h₂.1.2.args 6 (by decide) (by decide)]
      · rw [j₁.a1, j₂.a1, h₁.1.2.args 7 (by decide) (by decide), h₂.1.2.args 7 (by decide) (by decide)]
    · show t₂.syms n = t₁.syms n
      rw [y₁, y₂, h₁.2.2 n hn, h₂.2.2 n hn]
  · exact WP.mono (chkCall_ok h.1.1 h624 h.2.1 z j y) fun t' h' => ⟨s, h, h'⟩

/-- The stack's address `x10` holds the table's address. -/
theorem argT_ok {s : State} (hp : PreV tsH tsG K s) :
    WP isa (.block [arg .x10 6]) (allocated frameBytes s) fun u => u.gpr .x10 = stackArg s 6 ∧
      u.syms = s.syms ∧ u.sp = fb s ∧ u.gpr .x0 = s.gpr .x0 := by
  refine WP.of_syms ?_
  unfold arg
  refine wp_ldrSp (by decide) (by
    simp only [allocated]
    rw [show s.sp - BitVec.ofNat 64 frameBytes = fb s from rfl, ← stackArgAddr_fb]
    exact arg_in hp (Covers.left (Covers.refl _)) (j := 6) (by decide)) fun u o e => wp_nil fun sy =>
      ⟨?_, sy, by rw [o.sp]; rfl, by rw [o.get .x0]; rfl⟩
  rw [e]
  simp only [allocated]
  rw [show s.sp - BitVec.ofNat 64 frameBytes = fb s from rfl, ← stackArgAddr_fb]
  rfl

include h624 hcK hv hct in
theorem code_ct : RelCT isa (Two (ES f g tsH tsG K i T Hs Gs)) (verifyC f g c.name c.code) fun _ _ => True := by
  unfold verifyC
  refine two_alloc (R := fun _ _ => True) ?_
  unfold verifyCBody seqs seqs seqs
  rw [show verifyPrologue ++ n0 .x0 = [arg .x10 6] ++ (verifyPrologue.tail ++ n0 .x0) from rfl]
  refine RelCT.seq_block_append ?_
  -- The table's address.
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧
      WP isa (.block (verifyPrologue.tail ++ n0 .x0)) u (AtChk s) ∧ u.gpr .x10 = stackArg s 6 ∧ u.syms = s.syms ∧
      u.sp = fb s ∧ u.gpr .x0 = s.gpr .x0)
    (two_taint [] (fun _ _ _ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂]; simp only [allocated, h₁.1.2.sp, h₂.1.2.sp],
      fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
    fun a u ⟨s, h, hu⟩ => ?_) ?_
  · subst hu
    have hw := prologue_ok (u := allocated frameBytes s) h.1.1 (by simp [allocated]) (by simp [allocated])
      (by simp [allocated]) (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])
    rw [show verifyPrologue ++ n0 .x0 = [arg .x10 6] ++ (verifyPrologue.tail ++ n0 .x0) from rfl,
      WP.block_append_iff] at hw
    exact WP.mono (wp_and hw (argT_ok h.1.1)) fun u ⟨w, x, y, p, q⟩ => ⟨s, h, w, x, y, p, q⟩
  -- The prologue.
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ AtChk s u ∧ u.syms = s.syms)
    (two_taint [.x0, .x10] (fun _ u₁ u₂ ⟨s₁, h₁, _, x₁, _, p₁, q₁⟩ ⟨s₂, h₂, _, x₂, _, p₂, q₂⟩ =>
      ⟨by rw [p₁, p₂, h₁.1.fb, h₂.1.fb], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [q₁, q₂, h₁.1.gpr (by decide), h₂.1.gpr (by decide)]
        · rw [x₁, x₂, h₁.1.2.args 6 (by decide) (by decide), h₂.1.2.args 6 (by decide) (by decide)]⟩)
      (by taint_decide))
    fun a u ⟨s, h, w, x, y, _⟩ => WP.mono_syms w fun t ht sy => ⟨s, h, ht, sy.trans y⟩) ?_
  refine RelCT.seq ?_ (two_taint (Φ := fun a t => t.sp = fb a) [] (fun a t₁ t₂ h₁ h₂ =>
    ⟨by rw [h₁, h₂], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
  refine two_ite (fun a u₁ u₂ ⟨s₁, h₁, j₁, _⟩ ⟨s₂, h₂, j₂, _⟩ => by
      rw [eval_zero, eval_zero, j₁.x10, j₂.x10, h₁.1.n0, h₂.1.n0])
    (vfail_ct fun a u ⟨⟨s, h, j, _⟩, _⟩ => ⟨s, h.1, ⟨j.sp, j.rd, j.wr, j.v, j.fr⟩⟩) ?_
  unfold seqs seqs seqs seqs
  refine RelCT.seq (two_post
    (Ψ := fun a t => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ s.mem (s.gpr .x0) ≠ 0 ∧
      AtCall s (ebS s) (elS s) (loS s) t ∧ t.syms = s.syms)
    (two_taint [.x10, .x20, .x23] (fun a u₁ u₂ ⟨⟨s₁, h₁, j₁, _⟩, _⟩ ⟨⟨s₂, h₂, j₂, _⟩, _⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.1.fb, h₂.1.fb], fun r hr => ?_⟩) (by taint_decide))
    fun a u ⟨⟨s, h, j, y⟩, hb⟩ => ?_) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [j₁.x10, j₂.x10, h₁.1.n0, h₂.1.n0]
    · exact (j₁.x20.trans h₁.1.scr).trans (j₂.x20.trans h₂.1.scr).symm
    · rw [j₁.x23, j₂.x23, h₁.1.gpr (by decide), h₂.1.gpr (by decide)]
  · have h0 : s.mem (s.gpr .x0) ≠ 0 := fun h0 => by
      rw [eval_zero, j.x10, h0] at hb
      exact absurd hb (by decide)
    exact WP.mono_syms (pubArgsC_ok h.1.1 j h0) fun t ht sy => ⟨s, h, h0, ht, sy.trans y⟩
  -- The public operation.
  refine RelCT.seq (two_post
    (Ψ := fun a t => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ s.mem (s.gpr .x0) ≠ 0 ∧
      AfterCall K s (ebS s) (elS s) (loS s) t ∧ t.syms = s.syms)
    ((call_ct c hcK).mono (fun _ _ => two_mono fun _ _ ⟨s, h, z, j, _⟩ => ⟨s, h.1, z, j⟩) fun _ _ h => h)
    fun a t ⟨s, h, z, j, y⟩ => WP.mono_syms (call_ok c h.1.1 hcK j) fun t' h' sy => ⟨s, h, z, h', sy.trans y⟩) ?_
  -- `checkEncoding`'s arguments.
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ s.mem (s.gpr .x0) ≠ 0 ∧
      AtChkC K s t ∧ t.syms = s.syms)
    (two_taint [.x20, .x23, .x24, .x25, .x26] (fun a u₁ u₂ ⟨s₁, h₁, _, j₁, _⟩ ⟨s₂, h₂, _, j₂, _⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.1.fb, h₂.1.fb], fun r hr => ?_⟩) (by taint_decide))
    fun a u ⟨s, h, z, j, y⟩ => WP.mono_syms (chkArgs_ok h.1.1 z j) fun t ht sy => ⟨s, h, z, ht, sy.trans y⟩) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (j₁.x20.trans h₁.1.scr).trans (j₂.x20.trans h₂.1.scr).symm
    · rw [j₁.x23, j₂.x23, h₁.1.gpr (by decide), h₂.1.gpr (by decide)]
    · rw [j₁.x24, j₂.x24, h₁.1.eb, h₂.1.eb]
    · rw [j₁.x25, j₂.x25, h₁.1.el, h₂.1.el]
    · rw [j₁.x26, j₂.x26, h₁.1.lo, h₂.1.lo]
  -- `checkEncoding`, for the index of the table.
  refine RelCT.seq (byIdx_ct (Q := Two fun a t => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ AfterChkC Hs Gs K s t)
    (fun _ => i) (fun a t t' ⟨s, h, z, j, y⟩ o sy => ⟨s, h, z, j.only9 o, sy.trans y⟩)
    (fun a t ⟨s, h, z, j, y⟩ => ⟨h.2.1.mem, j.x27.trans h.2.1.idx, rfl⟩)
    (fun j hj => by unfold idxs at hj; simp at hj; omega_using [hj]) (fun j hj => ?_) (fun j hj => ?_)) ?_
  · unfold idxs at hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact two_taint [.x27] (fun a t₁ t₂ ⟨s₁, h₁, _, j₁, _⟩ ⟨s₂, h₂, _, j₂, _⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.1.fb, h₂.1.fb], fun r hr => by
        rw [List.mem_singleton.mp hr, j₁.x27, j₂.x27, h₁.2.1.idx, h₂.2.1.idx]⟩) (by taint_decide)
  · by_cases hij : i = j
    · subst hij
      exact (chk_ct h624 hv hct).mono (fun _ _ => two_mono fun _ _ h => h.1) fun _ _ h => h
    · exact RelCT.of_false fun _ _ ⟨a, h₁, _⟩ => hij h₁.2
  exact two_post (two_taint (Φ := fun a t => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ AfterChkC Hs Gs K s t) []
    (fun a t₁ t₂ ⟨s₁, h₁, j₁⟩ ⟨s₂, h₂, j₂⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.1.fb, h₂.1.fb], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
    fun a t ⟨s, h, j⟩ => wp_and fun t' o _ => wp_nil (by rw [o.sp, j.sp, h.1.fb])

end

end VG.Proof.RsaPss.AArch64.Vfy

end

end

/-! ### `RsaPss.AArch64.VerifyCVerified`, which only this module used -/

section

/-!
# RSASSA-PSS verification on AArch64, calling `checkEncoding`: correctness and constant time

`verifyK vs K`: `verifyPrecomputedMdTableContract` with the tables of `vs`,
stated on the registers and the stack (its precondition `PreV`, its public
data `PubV` and the tables'), which `verifyC` meets: correctness
(`code_ok`, with the selection `CSel` the tables a state holds give,
`csel_of`) and constant time (`code_ct`, for the index, the functions and
the hash functions of the first run's tables, which every run with the same
public data holds): `verify_correct`, `verify_constantTime`.

The contract implies `verifyK` (`verify_implies`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked Two)
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.MdHashTable.AArch64 (idx)
open VG.Proof.RsaPss.AArch64 (OK tabsOf csel_of chk_of chkCT_of names_sub Tabs)
open VG.Proof.RsaPss.AArch64.Sgn (stk)

/-- `verifyPrecomputedMdTableContract` with the tables `tsH` and `tsG` and the
stack `stk K`, on the registers and the stack. -/
def verifyK (tsH tsG : List FnTable) (K : Nat) : Contract isa where
  pre s := PreV tsH tsG K s
  post s s' := ∀ H G, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 6) = some H →
    Spec.MdHashTable.hashAt 64 s.mem (stackArg s 7) = some G → Cons s →
      (s'.gpr .x0).setWidth 32 = if Spec.RsaPss.verify H G (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .x4) H.len)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x1).toNat)
        (Spec.RsaPss.expectedSaltLen (stackArg s 0) ((stackArg s 1).setWidth 32)) then 1 else 0
  pub s₁ s₂ := PubV s₁ s₂ ∧
    (∀ f ∈ (tsH.map (·.fns)).flatten ++ (tsG.map (·.fns)).flatten, s₁.syms f = s₂.syms f) ∧
    (∀ T ∈ tsH, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 6) (FnTable.words isa s₁ T) ↔
      Abi.tableHeld 64 s₂.mem (stackArg s₂ 6) (FnTable.words isa s₂ T))) ∧
    ∀ T ∈ tsG, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 7) (FnTable.words isa s₁ T) ↔
      Abi.tableHeld 64 s₂.mem (stackArg s₂ 7) (FnTable.words isa s₂ T))

/-- `verifyK` with the tables of `vs`. -/
abbrev verifyKV (vs : List MdHash) (K : Nat) : Contract isa :=
  verifyK (MdHashTable.AArch64.tables vs) (HashTable.AArch64.tables vs) K

/-- The tables of a state meeting the precondition: those of variants `w`
and `w'` of `vs`. -/
theorem tabs_of {vs : List MdHash} {K : Nat} {s : State}
    (hp : PreV (MdHashTable.AArch64.tables vs) (HashTable.AArch64.tables vs) K s) :
    ∃ w ∈ vs, ∃ w' ∈ vs,
      Abi.tableHeld 64 s.mem (stackArg s 6) (FnTable.words isa s (MdHashTable.AArch64.tableOf w)) ∧
      Abi.tableHeld 64 s.mem (stackArg s 7) (FnTable.words isa s (HashTable.AArch64.tableOf w')) := by
  obtain ⟨_, hT, hH⟩ := hp.tabH
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨_, hT', hG⟩ := hp.tabG
  obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hT'
  exact ⟨w, hw, w', hw', hH, hG⟩

variable {vs : List MdHash} (hok : OK vs) (c : PdChecked) {K : Nat} (h624 : 624 ≤ K) (hcK : c.stack ≤ K)

include hok h624 hcK in
theorem verify_correct (s : State) (h : (verifyKV vs K).pre s) :
    ∃ t s', Exec isa (verifyC (MdHashTable.AArch64.fnsOf vs) (HashTable.AArch64.fnsOf vs) c.name c.code) s t s' ∧
      abiPreserved s s' ∧ (verifyKV vs K).post s s' := by
  obtain ⟨w, hw, w', hw', hH, hG⟩ := tabs_of h
  have E := csel_of hok hw hw' h.hsy h.hdl hH hG
  obtain ⟨t, s', he, habi, hr⟩ := code_ok c h624 hcK h E
  refine ⟨t, s', he, habi, fun H G hH' hG' hc => ?_⟩
  cases hH'.symm.trans E.hH
  cases hG'.symm.trans E.hG
  exact hr hc

/-- The index, the functions and the hash functions `x` whose
`checkEncoding` is correct and constant time. -/
def ChkGood (x : Nat × Tabs × Spec.Mgf1.Hash × Spec.Mgf1.Hash) : Prop :=
  (∀ s', (Chk.chkK x.2.1 x.2.2.1 x.2.2.2).pre s' → ∃ t s'',
    Exec isa (checkEncoding (MdHashTable.AArch64.fnsOf vs) (ofIdx x.1) (HashTable.AArch64.fnsOf vs)) s' t s'' ∧
      abiPreserved s' s'' ∧ (Chk.chkK x.2.1 x.2.2.1 x.2.2.2).post s' s'') ∧
    ConstantTime isa (Chk.chkK x.2.1 x.2.2.1 x.2.2.2).pre (Chk.chkK x.2.1 x.2.2.1 x.2.2.2).pub
      (checkEncoding (MdHashTable.AArch64.fnsOf vs) (ofIdx x.1) (HashTable.AArch64.fnsOf vs))

include hok h624 hcK in
theorem verify_constantTime :
    ConstantTime isa (verifyKV vs K).pre (verifyKV vs K).pub
      (verifyC (MdHashTable.AArch64.fnsOf vs) (HashTable.AArch64.fnsOf vs) c.name c.code) := by
  refine RelCT.constantTime ((RelCT.exists_ (Q := fun _ _ => True)
      (P := fun (x : Nat × Tabs × Spec.Mgf1.Hash × Spec.Mgf1.Hash) s₁ s₂ =>
        ChkGood (vs := vs) x ∧ Two (ES (MdHashTable.AArch64.fnsOf vs) (HashTable.AArch64.fnsOf vs)
          (MdHashTable.AArch64.tables vs) (HashTable.AArch64.tables vs) K x.1 x.2.1 x.2.2.1 x.2.2.2) s₁ s₂)
      fun x => ?_).mono (fun s₁ s₂ ⟨h₁, h₂, hpub⟩ => ?_) fun _ _ h => h)
  · by_cases hx : ChkGood (vs := vs) x
    · exact (code_ct c h624 hcK hx.1 hx.2).mono (fun _ _ h => h.2) fun _ _ h => h
    · exact RelCT.of_false fun _ _ h => hx h.1
  obtain ⟨w, hw, w', hw', hH, hG⟩ := tabs_of h₁
  obtain ⟨pV, hsy, htH, htG⟩ := hpub
  have hH₂ := (htH _ (List.mem_map_of_mem hw)).mp hH
  have hG₂ := (htG _ (List.mem_map_of_mem hw')).mp hG
  refine ⟨(idx w, tabsOf vs w w', w.mgf.G, w'.mgf.G), ⟨chk_of hok hw, chkCT_of hok hw⟩, s₁,
    ⟨⟨h₁, PubV.refl s₁⟩, csel_of hok hw hw' h₁.hsy h₁.hdl hH hG, fun _ _ => rfl⟩,
    ⟨⟨h₂, pV⟩, csel_of hok hw hw' h₂.hsy h₂.hdl hH₂ hG₂, fun n hn => (hsy n (names_sub hw hw' n hn)).symm⟩⟩

/-- The contract, with the tables of `vs`. -/
abbrev verifyCK (vs : List MdHash) (K : Nat) : Contract isa :=
  Spec.RsaPss.verifyPrecomputedMdTableContract (verifyAbi (MdHashTable.AArch64.tables vs) (HashTable.AArch64.tables vs))
    (stk K)

omit hok c h624 hcK in
/-- The contract implies `verifyK`, if it is satisfiable. -/
theorem verify_implies (hsat : ∃ s, (verifyCK vs K).pre s) : (verifyKV vs K).Implies (verifyCK vs K) where
  pre _ h := preV_of h
  post s s' _ h := by
    sig_post [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs,
    List.append_eq, _root_.List.range, _root_.List.range.loop]
    intro H G hH hG hc
    exact h H G hH hG hc
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs,
    List.append_eq, _root_.List.range, _root_.List.range.loop] at h
    simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq] at h
    obtain ⟨hsp, hsy, htH, htG, hl, g0, g1, g2, g3, g4, g5, g6, g7, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
    obtain ⟨hne, hw⟩ := List.append_inj hl (by simp [VG.Proof.RsaPkcs1Sig.bytesAt_length, g1, g3])
    obtain ⟨hn, he⟩ := leak_eq2 (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length, VG.Proof.RsaPkcs1Sig.bytesAt_length, g1]) hne
    refine ⟨⟨hsp.symm, fun r hr => ?_, a1.symm, fun i hi hi1 => ?_, hn.symm, he.symm,
      ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hw).symm⟩, hsy,
      fun T hT => htH _ _ rfl rfl T hT, fun T hT => htG _ _ rfl rfl T hT⟩
    · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [g0.symm, g1.symm, g2.symm, g3.symm, g4.symm, g5.symm, g6.symm, g7.symm]
    · match i, hi, hi1 with
      | 0, _, _ => exact a0.symm | 1, _, h => exact absurd rfl h | 2, _, _ => exact a2.symm
      | 3, _, _ => exact a3.symm | 4, _, _ => exact a4.symm | 5, _, _ => exact a5.symm
      | 6, _, _ => exact a6.symm | 7, _, _ => exact a7.symm | n + 8, h, _ => exact absurd h (by omega_using [])
  sat := hsat

end VG.Proof.RsaPss.AArch64.Vfy

end

end


/-!
# RSASSA-PSS on AArch64 with the tables of `vs`: the contracts are satisfiable

By the states of the contracts with the hash functions fixed, with the table
of `MdHash` of a variant `w` of `vs` at `0x300000`, the table of `MdHash` of
`w` at `0x300100` (the stack arguments' values), and the tables' functions at
distinct addresses (`symsOf`): `sign_sat`, `verify_sat`, as on x86-64
(`Proof/RsaPss/X86_64/Sat.lean`); and the instances, `sign_ok`, `verify_ok`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.HashTable (symsOf symsOf_distinct readW_sep64)

/-- The words `ws` written from `p`. -/
def putWs (m : Mem) (p : Addr) : List (BitVec 64) → Mem
  | [] => m
  | w :: ws => putWs (m.writeW p w) (p + 8) ws

theorem add8_toNat {p : Addr} (h : p.toNat + 8 < 2 ^ 64) : (p + 8).toNat = p.toNat + 8 := by
  rw [BitVec.toNat_add, show (8 : Addr).toNat = 8 from rfl, Nat.mod_eq_of_lt h]

/-- A word apart from the words `putWs` writes. -/
theorem putWs_out {m : Mem} {a : Addr} : ∀ {p : Addr} {ws : List (BitVec 64)},
    (a.toNat + 8 ≤ p.toNat ∨ p.toNat + 8 * ws.length ≤ a.toNat) → p.toNat + 8 * ws.length < 2 ^ 64 →
    a.toNat + 8 ≤ 2 ^ 64 → (putWs m p ws).readW a 64 = m.readW a 64
  | _, [], _, _, _ => rfl
  | p, w :: ws, h, hp, ha => by
    simp only [List.length_cons] at h hp
    have h8 := add8_toNat (p := p) (by omega_using [hp])
    simp only [putWs]
    rw [putWs_out (by rw [h8]; omega_using [h]) (by rw [h8]; omega_using [hp]) ha, readW_sep64 (by omega_using [h]) ha (by omega_using [hp])]

/-- The words `putWs` writes. -/
theorem putWs_held {m : Mem} : ∀ {p : Addr} {ws : List (BitVec 64)}, p.toNat + 8 * ws.length < 2 ^ 64 →
    Abi.tableHeld 64 (putWs m p ws) p ws
  | _, [], _ => fun i hi => absurd hi (Nat.not_lt_zero _)
  | p, w :: ws, hp => by
    simp only [List.length_cons] at hp
    have h8 := add8_toNat (p := p) (by omega_using [hp])
    intro i hi
    simp only [putWs]
    cases i with
    | zero =>
      rw [show p + BitVec.ofNat 64 (64 / 8 * 0) = p from BitVec.add_zero p,
        putWs_out (.inl (by rw [h8])) (by rw [h8]; omega_using [hp]) (by omega_using [hp]), Mem.readW_writeW_self64]
      simp
    | succ i =>
      have := putWs_held (m := m.writeW p w) (p := p + 8) (ws := ws) (by rw [h8]; omega_using [hp]) i
        (by simp at hi; omega_using [hi])
      rw [show p + BitVec.ofNat 64 (64 / 8 * (i + 1)) = p + 8 + BitVec.ofNat 64 (64 / 8 * i) by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega_using []]
      simpa using this

/-- The words of a table, its functions at the addresses `symsOf ns`. -/
def tw (ns : List String) (T : FnTable) : List (BitVec 64) := T.fns.map (symsOf ns) ++ T.data

/-- The names of the tables' functions. -/
def allNames (vs : List MdHash) : List String := MdHashTable.AArch64.names vs ++ HashTable.AArch64.names vs

/-- The memory `m` with the tables of `w` at `0x300000` and `0x300100`, and
`m` itself below `0x300000`. -/
def tabMem (m : Mem) (vs : List MdHash) (w : MdHash) : Mem := fun a =>
  bif Nat.blt a.toNat 0x300000 then m a
  else putWs (putWs m 0x300000 (tw (allNames vs) (MdHashTable.AArch64.tableOf w))) 0x300100
    (tw (allNames vs) (MdHashTable.AArch64.tableOf w)) a

/-- A state with `s`'s registers and regions, the tables of `w` at `0x300000`
and `0x300100`, and `vs`' functions at distinct addresses. -/
def withTabs (s : State) (vs : List MdHash) (w : MdHash) : State :=
  { s with mem := tabMem s.mem vs w, syms := symsOf (allNames vs) }

theorem withTabs_arg (s : State) (vs : List MdHash) (w : MdHash) {j : Nat}
    (hj : (stackArgAddr s j).toNat + 8 ≤ 0x300000) : stackArg (withTabs s vs w) j = stackArg s j := by
  show (tabMem s.mem vs w).readW (stackArgAddr s j) 64 = s.mem.readW (stackArgAddr s j) 64
  refine Mem.readW_congr fun i hi => ?_
  have : (stackArgAddr s j + BitVec.ofNat 64 i).toNat < 0x300000 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hj, hi]
  simp only [tabMem, Nat.blt_eq.mpr this, Bool.cond_true]

/-- Above `0x300000`, the tables' memory. -/
theorem tabMem_above {m : Mem} {vs : List MdHash} {w : MdHash} {p : Addr} {ws : List (BitVec 64)}
    (hp : 0x300000 ≤ p.toNat) (hl : p.toNat + 8 * ws.length < 2 ^ 64)
    (h : Abi.tableHeld 64 (putWs (putWs m 0x300000 (tw (allNames vs) (MdHashTable.AArch64.tableOf w))) 0x300100
      (tw (allNames vs) (MdHashTable.AArch64.tableOf w))) p ws) :
    Abi.tableHeld 64 (tabMem m vs w) p ws := by
  intro i hi
  rw [← h i hi]
  refine Mem.readW_congr fun k hk => ?_
  have : ¬ (p + BitVec.ofNat 64 (64 / 8 * i) + BitVec.ofNat 64 k).toNat < 0x300000 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hp, hl, hi, hk]
  have hb : Nat.blt (p + BitVec.ofNat 64 (64 / 8 * i) + BitVec.ofNat 64 k).toNat 0x300000 = false := by
    rw [Bool.eq_false_iff]; intro hc; exact this (Nat.blt_eq.mp hc)
  simp only [tabMem, hb, Bool.cond_false]

theorem withTabs_heldH (s : State) (vs : List MdHash) (w : MdHash) :
    Abi.tableHeld 64 (withTabs s vs w).mem 0x300000
      (FnTable.words isa (withTabs s vs w) (MdHashTable.AArch64.tableOf w)) := by
  have hl : (tw (allNames vs) (MdHashTable.AArch64.tableOf w)).length = 11 := by
    simp [tw, MdHashTable.AArch64.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf]
  have c1 : (0x300000 : Addr).toNat = 0x300000 := rfl
  have c2 : (0x300100 : Addr).toNat = 0x300100 := rfl
  refine tabMem_above (by rw [c1]) (by simp [FnTable.words, MdHashTable.AArch64.tableOf, Spec.MdHashTable.dataOf,
    Spec.HashTable.dataOf]) fun i hi => ?_
  have hi' : i < 11 := by
    simp [FnTable.words, MdHashTable.AArch64.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf] at hi; omega_using [hi]
  rw [putWs_out (.inl (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))
    (by simp [tw, MdHashTable.AArch64.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf])
    (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]
  exact putWs_held (by rw [hl]; decide) i (by rw [hl]; exact hi')

theorem withTabs_heldG (s : State) (vs : List MdHash) (w : MdHash) :
    Abi.tableHeld 64 (withTabs s vs w).mem 0x300100
      (FnTable.words isa (withTabs s vs w) (MdHashTable.AArch64.tableOf w)) :=
  tabMem_above (by decide) (by simp [FnTable.words, MdHashTable.AArch64.tableOf, Spec.MdHashTable.dataOf,
      Spec.HashTable.dataOf])
    (putWs_held (by simp [tw, MdHashTable.AArch64.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf]))

/-! ## Signing -/

/-- A state meeting signing's precondition but for the tables: a 512-bit
modulus, one-byte `e`, primes, exponents and `qInv`, a digest of `dl` bytes,
an empty salt, a working space of 2080 words, the stack arguments at
`0x10000`, and the tables' addresses `0x300000` and `0x300100`. -/
def signSatBase (dl : Nat) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 64 | .x4 => 0x3000 | .x5 => 1 | .x6 => 0x4100
    | .x7 => 1 | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10001 then 0x42 else bif Nat.beq a.toNat 0x10008 then 1
    else bif Nat.beq a.toNat 0x10011 then 0x43 else bif Nat.beq a.toNat 0x10018 then 1
    else bif Nat.beq a.toNat 0x10021 then 0x44 else bif Nat.beq a.toNat 0x10028 then 1
    else bif Nat.beq a.toNat 0x10031 then 0x45 else bif Nat.beq a.toNat 0x10038 then 1
    else bif Nat.beq a.toNat 0x10041 then 0x46 else bif Nat.beq a.toNat 0x10048 then BitVec.ofNat 8 dl
    else bif Nat.beq a.toNat 0x10051 then 0x47 else bif Nat.beq a.toNat 0x10062 then 0x02
    else bif Nat.beq a.toNat 0x10068 then 0x20 else bif Nat.beq a.toNat 0x10069 then 0x08
    else bif Nat.beq a.toNat 0x10072 then 0x30 else bif Nat.beq a.toNat 0x10079 then 0x01
    else bif Nat.beq a.toNat 0x1007A then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩,
    ⟨0x4600, dl⟩, ⟨0x4700, 0⟩, ⟨0x300000, 88⟩, ⟨0x300100, 88⟩, ⟨0x10000, 128⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 2080 * 8⟩]

variable {vs : List MdHash}

theorem signSat_args (dl : Nat) : ∀ j < 16, (stackArgAddr (signSatBase dl) j).toNat + 8 ≤ 0x300000 := fun j hj => by
  have c0 : (65536 : Addr).toNat = 65536 := rfl
  simp only [stackArgAddr, signSatBase, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The stack arguments of `signSatBase dl`. -/
def signArgs (dl : Nat) : Nat → BitVec 64
  | 0 => 0x4200 | 1 => 1 | 2 => 0x4300 | 3 => 1 | 4 => 0x4400 | 5 => 1 | 6 => 0x4500 | 7 => 1
  | 8 => 0x4600 | 9 => BitVec.ofNat 64 dl | 10 => 0x4700 | 11 => 0 | 12 => 0x20000 | 13 => 2080
  | 14 => 0x300000 | _ => 0x300100

/-- Signing's precondition, from the facts of a state. -/
theorem sign_pre_of {tsH tsG : List FnTable} {dl : Nat} (hdl : dl ≤ 64) {s : State}
    (hg : s.gpr = (signSatBase dl).gpr) (hsp : s.sp = 0x10000) (ha : ∀ j < 16, stackArg s j = signArgs dl j)
    (hrd : s.rd = (signSatBase dl).rd) (hwr : s.wr = (signSatBase dl).wr)
    (hH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem 0x300000 (FnTable.words isa s T))
    (hG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem 0x300100 (FnTable.words isa s T))
    (hsy : ((tsH.map (·.fns)).flatten ++ (tsG.map (·.fns)).flatten).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hd : Spec.RsaPss.digestLenOk 64 s.mem 0x300000 (BitVec.ofNat 64 dl)) :
    (Spec.RsaPss.signMdTableContract (Sgn.signAbi tsH tsG) (Sgn.stk 3248)).pre s := by
  rw [show Sgn.stk 3248 = 3583 + 1 from rfl]
  sig_pre [Spec.RsaPss.signMdTableContract, Spec.RsaPss.signMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argRegs, List.append_eq, _root_.List.range, _root_.List.range.loop]
  have hdl' : (BitVec.ofNat 64 dl).toNat = dl := by rw [BitVec.toNat_ofNat]; omega_using [hdl]
  have hA : ∀ j, stackArgAddr s j = 0x10000 + BitVec.ofNat 64 (8 * j) := fun j => by
    simp only [stackArgAddr, hsp]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide),
    ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide), hg, hsp, hrd,
    hwr, hA, signArgs]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaPss.signMdTableContract, Spec.RsaPss.signMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argRegs, List.append_eq, _root_.List.range, _root_.List.range.loop]
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | exact Region.disjoint_of_sep (by decide)
    | decide
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (rw [hdl']; apply Region.disjoint_of_sep; simp [Region.sep]; omega_using [hdl])
    | (rw [hdl']; rfl)
    | (rw [hdl']; simp; omega_using [hdl])
    | (simp; omega)

theorem sign_sat_of {w : MdHash} (hw : w ∈ vs) (hl : (allNames vs).length < 2 ^ 32) {dl : Nat} (hdl : dl ≤ 64)
    (hlen : w.mgf.G.len = dl) (hb : ∀ j < 16, stackArg (signSatBase dl) j = signArgs dl j) :
    (Sgn.signCK vs 3248).pre (withTabs (signSatBase dl) vs w) :=
  sign_pre_of hdl rfl rfl (fun j hj => (withTabs_arg _ vs w (signSat_args dl j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hw, withTabs_heldH _ vs w⟩ ⟨_, List.mem_map_of_mem hw, withTabs_heldG _ vs w⟩
    (symsOf_distinct hl) fun H hH => by
      have hA := MdHashTable.AArch64.hashAt_tableOf
        (MdHashTable.AArch64.held_tableOf (withTabs_heldH (signSatBase dl) vs w)).2.2.2.1
      cases hH.symm.trans hA
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hdl]), hlen]

theorem signSat_b16 : ∀ j < 16, stackArg (signSatBase 16) j = signArgs 16 j := by decide
theorem signSat_b20 : ∀ j < 16, stackArg (signSatBase 20) j = signArgs 20 j := by decide
theorem signSat_b28 : ∀ j < 16, stackArg (signSatBase 28) j = signArgs 28 j := by decide
theorem signSat_b32 : ∀ j < 16, stackArg (signSatBase 32) j = signArgs 32 j := by decide
theorem signSat_b48 : ∀ j < 16, stackArg (signSatBase 48) j = signArgs 48 j := by decide
theorem signSat_b64 : ∀ j < 16, stackArg (signSatBase 64) j = signArgs 64 j := by decide

theorem sign_sat (hok : OK vs) : ∃ s, (Sgn.signCK vs 3248).pre s := by
  obtain ⟨w, hw, -⟩ := hok.2.2.2.1 0 (by decide)
  have hl := hok.2.2.2.2.1
  have hm := w.mgf.mem
  simp only [Pbkdf2.Md.AArch64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e | e | e
  · exact ⟨_, sign_sat_of hw hl (by decide) (by rw [e]; rfl) signSat_b16⟩
  · exact ⟨_, sign_sat_of hw hl (by decide) (by rw [e]; rfl) signSat_b20⟩
  · exact ⟨_, sign_sat_of hw hl (by decide) (by rw [e]; rfl) signSat_b28⟩
  · exact ⟨_, sign_sat_of hw hl (by decide) (by rw [e]; rfl) signSat_b32⟩
  · exact ⟨_, sign_sat_of hw hl (by decide) (by rw [e]; rfl) signSat_b48⟩
  · exact ⟨_, sign_sat_of hw hl (by decide) (by rw [e]; rfl) signSat_b64⟩
  · exact ⟨_, sign_sat_of hw hl (by decide) (by rw [e]; rfl) signSat_b28⟩
  · exact ⟨_, sign_sat_of hw hl (by decide) (by rw [e]; rfl) signSat_b32⟩

/-! ## Verification with a precomputed key -/

/-- A state meeting verification's precondition but for the tables: a
512-bit modulus, one-byte `e`, a digest of `dl` bytes, a 64-byte signature,
16 words of `pre` at `0x5000`, a working space of 2080 words, the stack
arguments at `0x10000`, and the tables' addresses `0x300000` and
`0x300100`. -/
def verifySatBase (dl : Nat) : State where
  gpr r := match r with
    | .x0 => 0x2000 | .x1 => 64 | .x2 => 0x3000 | .x3 => 1 | .x4 => 0x4600 | .x5 => BitVec.ofNat 64 dl
    | .x6 => 0x4000 | .x7 => 64 | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10012 then 0x02 else bif Nat.beq a.toNat 0x10018 then 0x20
    else bif Nat.beq a.toNat 0x10019 then 0x08 else bif Nat.beq a.toNat 0x10021 then 0x50
    else bif Nat.beq a.toNat 0x10028 then 16 else bif Nat.beq a.toNat 0x10032 then 0x30
    else bif Nat.beq a.toNat 0x10039 then 0x01 else bif Nat.beq a.toNat 0x1003A then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4600, dl⟩, ⟨0x4000, 64⟩, ⟨0x5000, 128⟩, ⟨0x300000, 88⟩, ⟨0x300100, 88⟩,
    ⟨0x10000, 64⟩]
  wr := [⟨0x20000, 2080 * 8⟩]

theorem verifySat_args (dl : Nat) : ∀ j < 8, (stackArgAddr (verifySatBase dl) j).toNat + 8 ≤ 0x300000 :=
  fun j hj => by
    have c0 : (65536 : Addr).toNat = 65536 := rfl
    simp only [stackArgAddr, verifySatBase, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-- The stack arguments of `verifySatBase dl`. -/
def verifyArgs : Nat → BitVec 64
  | 0 => 0 | 1 => 0 | 2 => 0x20000 | 3 => 2080 | 4 => 0x5000 | 5 => 16 | 6 => 0x300000 | _ => 0x300100

/-- Verification's precondition, from the facts of a state. -/
theorem verify_pre_of {tsH tsG : List FnTable} {dl : Nat} (hdl : dl ≤ 64) {s : State}
    (hg : s.gpr = (verifySatBase dl).gpr) (hsp : s.sp = 0x10000) (ha : ∀ j < 8, stackArg s j = verifyArgs j)
    (hrd : s.rd = (verifySatBase dl).rd) (hwr : s.wr = (verifySatBase dl).wr)
    (hH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem 0x300000 (FnTable.words isa s T))
    (hG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem 0x300100 (FnTable.words isa s T))
    (hsy : ((tsH.map (·.fns)).flatten ++ (tsG.map (·.fns)).flatten).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hd : Spec.RsaPss.digestLenOk 64 s.mem 0x300000 (BitVec.ofNat 64 dl)) :
    (Spec.RsaPss.verifyPrecomputedMdTableContract (Vfy.verifyAbi tsH tsG) (Sgn.stk 624)).pre s := by
  rw [show Sgn.stk 624 = 959 + 1 from rfl]
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argRegs, List.append_eq, _root_.List.range,
    _root_.List.range.loop]
  have hdl' : (BitVec.ofNat 64 dl).toNat = dl := by rw [BitVec.toNat_ofNat]; omega_using [hdl]
  have hA : ∀ j, stackArgAddr s j = 0x10000 + BitVec.ofNat 64 (8 * j) := fun j => by
    simp only [stackArgAddr, hsp]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), hg, hsp, hrd, hwr, hA, verifyArgs]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argRegs, List.append_eq, _root_.List.range,
    _root_.List.range.loop]
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | exact Region.disjoint_of_sep (by decide)
    | decide
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (rw [hdl']; apply Region.disjoint_of_sep; simp [Region.sep]; omega_using [hdl])
    | (rw [hdl']; rfl)
    | (rw [hdl']; simp; omega_using [hdl])
    | (simp; omega)

theorem verify_sat_of {w : MdHash} (hw : w ∈ vs) (hl : (allNames vs).length < 2 ^ 32) {dl : Nat} (hdl : dl ≤ 64)
    (hlen : w.mgf.G.len = dl) (hb : ∀ j < 8, stackArg (verifySatBase dl) j = verifyArgs j) :
    (Vfy.verifyCK vs 624).pre (withTabs (verifySatBase dl) vs w) :=
  verify_pre_of hdl rfl rfl (fun j hj => (withTabs_arg _ vs w (verifySat_args dl j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hw, withTabs_heldH _ vs w⟩ ⟨_, List.mem_map_of_mem hw, withTabs_heldG _ vs w⟩
    (symsOf_distinct hl) fun H hH => by
      have hA := MdHashTable.AArch64.hashAt_tableOf
        (MdHashTable.AArch64.held_tableOf (withTabs_heldH (verifySatBase dl) vs w)).2.2.2.1
      cases hH.symm.trans hA
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hdl]), hlen]

theorem verifySat_b16 : ∀ j < 8, stackArg (verifySatBase 16) j = verifyArgs j := by decide
theorem verifySat_b20 : ∀ j < 8, stackArg (verifySatBase 20) j = verifyArgs j := by decide
theorem verifySat_b28 : ∀ j < 8, stackArg (verifySatBase 28) j = verifyArgs j := by decide
theorem verifySat_b32 : ∀ j < 8, stackArg (verifySatBase 32) j = verifyArgs j := by decide
theorem verifySat_b48 : ∀ j < 8, stackArg (verifySatBase 48) j = verifyArgs j := by decide
theorem verifySat_b64 : ∀ j < 8, stackArg (verifySatBase 64) j = verifyArgs j := by decide

theorem verify_sat (hok : OK vs) : ∃ s, (Vfy.verifyCK vs 624).pre s := by
  obtain ⟨w, hw, -⟩ := hok.2.2.2.1 0 (by decide)
  have hl := hok.2.2.2.2.1
  have hm := w.mgf.mem
  simp only [Pbkdf2.Md.AArch64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e | e | e
  · exact ⟨_, verify_sat_of hw hl (by decide) (by rw [e]; rfl) verifySat_b16⟩
  · exact ⟨_, verify_sat_of hw hl (by decide) (by rw [e]; rfl) verifySat_b20⟩
  · exact ⟨_, verify_sat_of hw hl (by decide) (by rw [e]; rfl) verifySat_b28⟩
  · exact ⟨_, verify_sat_of hw hl (by decide) (by rw [e]; rfl) verifySat_b32⟩
  · exact ⟨_, verify_sat_of hw hl (by decide) (by rw [e]; rfl) verifySat_b48⟩
  · exact ⟨_, verify_sat_of hw hl (by decide) (by rw [e]; rfl) verifySat_b64⟩
  · exact ⟨_, verify_sat_of hw hl (by decide) (by rw [e]; rfl) verifySat_b28⟩
  · exact ⟨_, verify_sat_of hw hl (by decide) (by rw [e]; rfl) verifySat_b32⟩

/-! ## Signing with the key's precomputed values -/

open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

/-- The stack arguments of `signPSatBase dl`: the key (`keyMem`'s), a
digest of `dl` bytes, an empty salt, a working space of 2080 words, the
tables at `0x300000` and `0x300100`, and `pre` at `0x4800`. -/
def signPArgs (dl : Nat) : List Nat :=
  [0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x4700, dl, 0x4780, 0, 0x20000, 2080, 0x300000, 0x300100,
    0x4800, 24]

/-- The memory of `signPSatBase dl`: the stack arguments from `0x10000`, and
the key. -/
def signPMem (dl : Nat) (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x10000 i && Nat.blt i 0x10090 then
    BitVec.ofNat 8 ((signPArgs dl).getD ((i - 0x10000) / 8) 0 / 256 ^ ((i - 0x10000) % 8))
  else bif keyIn i then keyMem a else 0

/-- A state meeting the precomputed signing's precondition but for the
tables: the key `keyMem` holds (a 512-bit modulus at `0x2000`, 256-bit
primes at `0x4200` and `0x4300` and `pre` at `0x4800`), one-byte `e`. -/
def signPSatBase (dl : Nat) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 64 | .x4 => 0x3000 | .x5 => 1 | .x6 => 0x4200
    | .x7 => 32 | _ => 0
  sp := 0x10000
  mem := signPMem dl
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩, ⟨0x4600, 32⟩,
    ⟨0x4700, dl⟩, ⟨0x4780, 0⟩, ⟨0x4800, 192⟩, ⟨0x300000, 88⟩, ⟨0x300100, 88⟩, ⟨0x10000, 144⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 2080 * 8⟩]

theorem signPSat_args (dl : Nat) : ∀ j < 18, (stackArgAddr (signPSatBase dl) j).toNat + 8 ≤ 0x300000 := fun j hj => by
  have c0 : (65536 : Addr).toNat = 65536 := rfl
  simp only [stackArgAddr, signPSatBase, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The precomputed signing's precondition, from the facts of a state. -/
theorem signP_pre_of {tsH tsG : List FnTable} {dl : Nat} (hdl : dl ≤ 64) {s : State}
    (hg : s.gpr = (signPSatBase dl).gpr) (hsp : s.sp = 0x10000)
    (ha : ∀ j < 18, stackArg s j = BitVec.ofNat 64 ((signPArgs dl).getD j 0))
    (hrd : s.rd = (signPSatBase dl).rd) (hwr : s.wr = (signPSatBase dl).wr)
    (hH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem 0x300000 (FnTable.words isa s T))
    (hG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem 0x300100 (FnTable.words isa s T))
    (hsy : ((tsH.map (·.fns)).flatten ++ (tsG.map (·.fns)).flatten).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hd : Spec.RsaPss.digestLenOk 64 s.mem 0x300000 (BitVec.ofNat 64 dl))
    (hkey : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem 0x2000 64) (Spec.Rsa.bytesAt s.mem 0x4200 32)
      (Spec.Rsa.bytesAt s.mem 0x4300 32) = some (Spec.Rsa.wordsAt s.mem 0x4800 24)) :
    (Spec.RsaPss.signPrecomputedMdTableContract (Sgn.signPAbi tsH tsG) (Sgn.stk 3248)).pre s := by
  rw [show Sgn.stk 3248 = 3583 + 1 from rfl]
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argRegs, List.append_eq, _root_.List.range, _root_.List.range.loop]
  have hdl' : (BitVec.ofNat 64 dl).toNat = dl := by rw [BitVec.toNat_ofNat]; omega_using [hdl]
  have hA : ∀ j, stackArgAddr s j = 0x10000 + BitVec.ofNat 64 (8 * j) := fun j => by
    simp only [stackArgAddr, hsp]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide),
    ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide),
    ha 16 (by decide), ha 17 (by decide), hg, hsp, hrd, hwr, hA, signPArgs]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argRegs, List.append_eq, _root_.List.range, _root_.List.range.loop]
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | exact Region.disjoint_of_sep (by decide)
    | decide
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (rw [hdl']; apply Region.disjoint_of_sep; simp [Region.sep]; omega_using [hdl])
    | (rw [hdl']; rfl)
    | (rw [hdl']; simp; omega_using [hdl])
    | (simp; omega)
    | exact hkey
    | exact hH
    | exact hG
    | exact hd

/-- The key, in a state with the tables. -/
theorem signPSat_key (dl : Nat) (vs : List MdHash) (w : MdHash) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt (withTabs (signPSatBase dl) vs w).mem 0x2000 64)
      (Spec.Rsa.bytesAt (withTabs (signPSatBase dl) vs w).mem 0x4200 32)
      (Spec.Rsa.bytesAt (withTabs (signPSatBase dl) vs w).mem 0x4300 32) =
    some (Spec.Rsa.wordsAt (withTabs (signPSatBase dl) vs w).mem 0x4800 24) :=
  key_pre_of fun a ha => by
    have hk : a.toNat < 0x48C0 := by
      simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha; omega
    have h1 : Nat.blt a.toNat 0x300000 = true := Nat.blt_eq.mpr (by omega_using [hk])
    have h2 : (Nat.ble 0x10000 a.toNat && Nat.blt a.toNat 0x10090) = false := by
      rw [Bool.eq_false_iff]; intro h; simp only [Bool.and_eq_true, Nat.ble_eq] at h; omega
    have e1 : (withTabs (signPSatBase dl) vs w).mem a = signPMem dl a := by
      show (bif _ then _ else _) = _
      rw [h1, Bool.cond_true]
      rfl
    rw [e1]
    show (bif _ then _ else _) = _
    rw [h2, Bool.cond_false, ha, Bool.cond_true]

theorem signP_sat_of {w : MdHash} (hw : w ∈ vs) (hl : (allNames vs).length < 2 ^ 32) {dl : Nat} (hdl : dl ≤ 64)
    (hlen : w.mgf.G.len = dl)
    (hb : ∀ j < 18, stackArg (signPSatBase dl) j = BitVec.ofNat 64 ((signPArgs dl).getD j 0)) :
    (Sgn.signPCK vs 3248).pre (withTabs (signPSatBase dl) vs w) :=
  signP_pre_of hdl rfl rfl (fun j hj => (withTabs_arg _ vs w (signPSat_args dl j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hw, withTabs_heldH _ vs w⟩ ⟨_, List.mem_map_of_mem hw, withTabs_heldG _ vs w⟩
    (symsOf_distinct hl) (fun H hH => by
      have hA := MdHashTable.AArch64.hashAt_tableOf
        (MdHashTable.AArch64.held_tableOf (withTabs_heldH (signPSatBase dl) vs w)).2.2.2.1
      cases hH.symm.trans hA
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hdl]), hlen]) (signPSat_key dl vs w)

theorem signPSat_b16 : ∀ j < 18, stackArg (signPSatBase 16) j = BitVec.ofNat 64 ((signPArgs 16).getD j 0) := by
  decide
theorem signPSat_b20 : ∀ j < 18, stackArg (signPSatBase 20) j = BitVec.ofNat 64 ((signPArgs 20).getD j 0) := by
  decide
theorem signPSat_b28 : ∀ j < 18, stackArg (signPSatBase 28) j = BitVec.ofNat 64 ((signPArgs 28).getD j 0) := by
  decide
theorem signPSat_b32 : ∀ j < 18, stackArg (signPSatBase 32) j = BitVec.ofNat 64 ((signPArgs 32).getD j 0) := by
  decide
theorem signPSat_b48 : ∀ j < 18, stackArg (signPSatBase 48) j = BitVec.ofNat 64 ((signPArgs 48).getD j 0) := by
  decide
theorem signPSat_b64 : ∀ j < 18, stackArg (signPSatBase 64) j = BitVec.ofNat 64 ((signPArgs 64).getD j 0) := by
  decide

theorem signP_sat (hok : OK vs) : ∃ s, (Sgn.signPCK vs 3248).pre s := by
  obtain ⟨w, hw, -⟩ := hok.2.2.2.1 0 (by decide)
  have hl := hok.2.2.2.2.1
  have hm := w.mgf.mem
  simp only [Pbkdf2.Md.AArch64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e | e | e
  · exact ⟨_, signP_sat_of hw hl (by decide) (by rw [e]; rfl) signPSat_b16⟩
  · exact ⟨_, signP_sat_of hw hl (by decide) (by rw [e]; rfl) signPSat_b20⟩
  · exact ⟨_, signP_sat_of hw hl (by decide) (by rw [e]; rfl) signPSat_b28⟩
  · exact ⟨_, signP_sat_of hw hl (by decide) (by rw [e]; rfl) signPSat_b32⟩
  · exact ⟨_, signP_sat_of hw hl (by decide) (by rw [e]; rfl) signPSat_b48⟩
  · exact ⟨_, signP_sat_of hw hl (by decide) (by rw [e]; rfl) signPSat_b64⟩
  · exact ⟨_, signP_sat_of hw hl (by decide) (by rw [e]; rfl) signPSat_b28⟩
  · exact ⟨_, signP_sat_of hw hl (by decide) (by rw [e]; rfl) signPSat_b32⟩

/-! ## The instance -/

/-- `vg_rsa_pss_sign`, with the tables of `vs`, calling the private-key
operation checked against the public exponent of the implementation `c`. -/
theorem sign_ok (hok : OK vs) (c : Proof.Rsa.AArch64.CrtImpl) :
    Verified AArch64.target
      (signC (MdHashTable.AArch64.fnsOf vs) (HashTable.AArch64.fnsOf vs) (RsaPkcs1Sig.AArch64.privOf c).name
        (RsaPkcs1Sig.AArch64.privOf c).code)
      (Sgn.signCK vs (RsaPkcs1Sig.AArch64.privOf c).stack) :=
  have h : 624 ≤ (RsaPkcs1Sig.AArch64.privOf c).stack := by
    show 624 ≤ Proof.Rsa.AArch64.stackBytes; decide
  ⟨Sgn.sign_correct hok _ h (Nat.le_refl _), Sgn.sign_constantTime hok _ h (Nat.le_refl _), sign_sat hok⟩

/-- `vg_rsa_pss_sign_precomputed`, with the tables of `vs`, calling
`vg_rsa_private_checked_precomputed` of the implementation `c`. -/
theorem signP_ok (hok : OK vs) (c : Proof.Rsa.AArch64.CrtImpl) :
    Verified AArch64.target
      (signCP (MdHashTable.AArch64.fnsOf vs) (HashTable.AArch64.fnsOf vs) (RsaPkcs1Sig.AArch64.privPOf c).name
        (RsaPkcs1Sig.AArch64.privPOf c).code)
      (Sgn.signPCK vs (RsaPkcs1Sig.AArch64.privPOf c).stack) :=
  have h : 624 ≤ (RsaPkcs1Sig.AArch64.privPOf c).stack := by
    show 624 ≤ Proof.Rsa.AArch64.stackBytes; decide
  ⟨Sgn.signP_correct hok _ h (Nat.le_refl _), Sgn.signP_constantTime hok _ h (Nat.le_refl _), signP_sat hok⟩

/-- `vg_rsa_pss_verify_precomputed`, with the tables of `vs`, calling the
precomputed public-key operation of the implementation `v`. -/
theorem verify_ok (hok : OK vs) (v : Proof.Rsa.AArch64.PublicImpl) :
    Verified AArch64.target
      (verifyC (MdHashTable.AArch64.fnsOf vs) (HashTable.AArch64.fnsOf vs) (RsaPkcs1Sig.AArch64.pdOf v).name
        (RsaPkcs1Sig.AArch64.pdOf v).code)
      (Vfy.verifyCK vs 624) :=
  have h : (RsaPkcs1Sig.AArch64.pdOf v).stack ≤ 624 := by show 16 ≤ 624; decide
  Verified.of_correct (Vfy.verify_correct hok _ (Nat.le_refl _) h)
    (Vfy.verify_constantTime hok _ (Nat.le_refl _) h) (Vfy.verify_implies (verify_sat hok))

end VG.Proof.RsaPss.AArch64
