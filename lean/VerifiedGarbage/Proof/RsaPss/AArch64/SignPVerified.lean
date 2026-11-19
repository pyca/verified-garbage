module

-- separate module: its proofs cost more than its imports, and the satisfiability witness's
-- changes (`Sat`) need not re-check them
public import VerifiedGarbage.Spec.RsaPss.MdTable
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignSpec
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaPss.AArch64.Instances
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignPre
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame
import VerifiedGarbage.Proof.RsaPss.AArch64.MgfCT
import VerifiedGarbage.Proof.RsaPss.SignEncode
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelSplit
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame
meta import VerifiedGarbage.Proof.RsaPss.AArch64.MgfCT
meta import VerifiedGarbage.Proof.RsaPss.SignEncode
meta import VerifiedGarbage.Proof.RsaPss.Params
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
meta import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.Rsa.BytesFrame
meta import VerifiedGarbage.Proof.Rsa.BytesFrame
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignCArgs
import VerifiedGarbage.Proof.RsaPss.AArch64.EncCT
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignCArgs
meta import VerifiedGarbage.Proof.RsaPss.AArch64.EncCT
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignPre
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignSpec
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignPre
public import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
meta import VerifiedGarbage.Proof.MlKem.AArch64.Wp
meta import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Encode
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Calls
import VerifiedGarbage.Proof.RsaPss.AArch64.MaskBits
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Encode
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Calls
meta import VerifiedGarbage.Proof.RsaPss.AArch64.MaskBits
meta import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash

/-! ### `RsaPss.AArch64.SignCCt`, which this module and modules that import it used -/

section

/-! ### `RsaPss.AArch64.SignCTop`, which this module and modules that import it used -/

section

/-! ### `RsaPss.AArch64.SignCorrect`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS signing on AArch64: correctness

Zeros to `out` (`fail_ok`); the checks and the encoding with the private
operation, or `fail` (`body_ok`), which is `RsaPss.sign` (`signOut_eq`);
the restores (`restore_ok`); the whole function (`code_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Impl.RsaPkcs1Sig.AArch64 (psLoop)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz eval_zero eval_nonzero)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp wp_mov fill_ok PrivChecked)
open VG.Proof.RsaPkcs1Sig (bytesAt_writeBytes frame_writeBytes)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64 (off loV maskV saltFits_ok)

theorem oR_eq {tsH tsG : List FnTable} {K : Nat} {s : State} (hp : PreS tsH tsG K s) :
    (⟨s.gpr .x0, (s.gpr .x3).toNat⟩ : Region) = oR s := by
  show (⟨s.gpr .x0, (s.gpr .x3).toNat⟩ : Region) = ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
  rw [hp.ol]

/-- Zeros to `out`, and 0 returned. -/
theorem fail_ok {tsH tsG : List FnTable} {K : Nat} {s t : State} (hp : PreS tsH tsG K s) (hm : Mid s t) (h23 : t.gpr .x23 = s.gpr .x3) :
    WP isa signFail t fun t' => Mid s t' ∧
      Spec.Rsa.writtenOutcome t'.mem (s.gpr .x0) (s.gpr .x3).toNat ((t'.gpr .x0).setWidth 32) .invalid := by
  have hk1 := hp.k1; have hk2 := hp.k2
  unfold signFail ld
  refine WP.seq (WP.mono (Q := fun (u : State) => Only [.x14, .x13, .x15] t u ∧ u.gpr .x14 = s.gpr .x0 ∧
      u.gpr .x13 = BitVec.ofNat 64 (s.gpr .x3).toNat ∧ (u.gpr .x15).setWidth 8 = 0) ?_
    fun u ⟨O, h14, h13, h15⟩ => ?_)
  · have hr : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 sOut) 8 := by
      rw [hm.sp, hm.rd, hm.wr]
      exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ (by decide) (by decide)))
    refine wp_ldrSp (by decide) hr fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ => wp_movz fun u₃ o₃ e₃ => wp_nil
      ⟨(o₁.trans (o₂.trans o₃)).mono, ?_, ?_, ?_⟩
    · rw [o₃.get .x14, o₂.get .x14, e₁, hm.sp]; exact hm.fr.rs (.x0, sOut) (by simp [regSlots])
    · rw [o₃.get .x13, e₂, o₁.get .x23, h23, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [e₃]; rfl
  have hO := oR_eq hp
  refine WP.seq (WP.mono (fill_ok (p := s.gpr .x0) (n := (s.gpr .x3).toNat) (b := 0) (by omega_using [hk1]) (by omega_using []) h14 h13
    h15 fun i hi => ?_) fun v ⟨kv, mv⟩ => ?_)
  · rw [O.wr, hm.wr]
    exact ⟨_, List.mem_cons_of_mem _ hp.hwo, by
      rw [← hO]; exact Offset.contains_base _ (by omega_using [hi]) (by have := hp.wo; rw [hp.ol] at this; omega_using [hi])⟩
  refine wp_movz fun w o e => wp_nil ⟨⟨?_, ?_, ?_, fun r hr => ?_, ?_⟩, by rw [e]; rfl, ?_⟩
  · rw [o.sp, kv.sp, O.sp, hm.sp]
  · rw [o.rd, kv.rd, O.rd, hm.rd]
  · rw [o.wr, kv.wr, O.wr, hm.wr]
  · rw [o.vcs r hr, kv.vcs r hr, O.vcs r hr, hm.v r hr]
  · have fw : Frame [⟨s.gpr .x0, (s.gpr .x3).toNat⟩] u.mem w.mem := by
      rw [o.mem, mv]; have := frame_writeBytes u.mem (s.gpr .x0) (List.replicate (s.gpr .x3).toNat 0)
      rwa [List.length_replicate] at this
    rw [hO] at fw
    exact (O.mem ▸ hm.fr).frame fw
      (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact (hp.ko.sub_left (frame_sub K s (d := 96) (n := 152) (by decide))))
      (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact (hp.ko.sub_left (frame_sub K s (d := 288) (n := 16) (by decide))))
  · rw [o.mem, mv]
    have := bytesAt_writeBytes u.mem (s.gpr .x0) (List.replicate (s.gpr .x3).toNat 0) (by simp; omega_using [])
    rwa [List.length_replicate] at this

end VG.Proof.RsaPss.AArch64.Sgn

end

end

/-! ### `RsaPss.AArch64.ByIdx`, which this module and modules that import it used -/

section

/-!
# The choice of the code for the hash function of a table, on AArch64

`byIdx b is` runs `b i` for the index `i` in `x27`, by comparisons with each
of `is` (`x9 := x27 - j`): `byIdx_wp` from the state before the comparisons,
`byIdx_ct` in two runs whose `x27` is the same, each comparison writing only
`x9`, as on x86-64 (`Proof/RsaPss/X86_64/SignCCorrect.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (Only wp_nil wp_subImm eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two two_post two_ite two_mono two_taint)

/-- The comparison of `x27` with `j`. -/
abbrev cmpIdx (j : Nat) : Prog isa := .block [.subImm .x .x9 .x27 j]

theorem sub_eq_zero {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    (BitVec.ofNat 64 i - BitVec.ofNat 64 j == 0) = decide (i = j) := by
  by_cases h : i = j
  · subst h; simp
  · have : BitVec.ofNat 64 i - BitVec.ofNat 64 j ≠ 0 := fun e => h (by
      have e' : BitVec.ofNat 64 i = BitVec.ofNat 64 j := by
        rw [← BitVec.sub_add_cancel (BitVec.ofNat 64 i) (BitVec.ofNat 64 j), e]; exact BitVec.zero_add _
      have := congrArg BitVec.toNat e'
      simpa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using this)
    rw [decide_eq_false h]
    exact beq_false_of_ne this

/-- A comparison of `x27` with `j`: `x9` is zero exactly when `i = j`. -/
theorem cmpIdx_ok {t : State} {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 4096) (h27 : t.gpr .x27 = BitVec.ofNat 64 i) :
    WP isa (cmpIdx j) t fun t' => Only [.x9] t t' ∧ (t'.gpr .x9 == 0) = decide (i = j) ∧ t'.syms = t.syms :=
  WP.of_syms (wp_subImm hj fun t' o e => wp_nil fun sy => ⟨o, by rw [e, h27, sub_eq_zero hi (by omega_using [hj])], sy⟩)

/-- `byIdx b is` runs `b i`. -/
theorem byIdx_wp {b : Nat → Prog isa} {Q : State → Prop} : ∀ {is : List Nat} {i : Nat} {t : State},
    i ∈ is → (∀ j ∈ is, j < 4096) → t.gpr .x27 = BitVec.ofNat 64 i →
    (∀ t', Only [.x9] t t' → t'.syms = t.syms → WP isa (b i) t' Q) → WP isa (byIdx b is) t Q
  | [], _, _, hi, _, _, _ => absurd hi List.not_mem_nil
  | [j], i, t, hi, _, _, h => by
    obtain rfl := List.mem_singleton.mp hi
    exact h t (Only.refl _ _) rfl
  | j :: k :: is, i, t, hi, hlt, h27, h => by
    have hil : i < 2 ^ 64 := by have := hlt i hi; omega_using [this]
    simp only [byIdx]
    refine WP.seq (WP.mono (cmpIdx_ok hil (hlt j List.mem_cons_self) h27) fun t' ⟨o, hz, sy⟩ => ?_)
    refine WP.ite (M := isa) _ (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
    · rw [hz, decide_eq_true_eq] at hb
      subst hb
      exact h t' o sy
    · rw [hz, decide_eq_false_iff_not] at hb
      have hi' : i ∈ k :: is := (List.mem_cons.mp hi).resolve_left hb
      exact byIdx_wp hi' (fun x hx => hlt x (List.mem_cons_of_mem _ hx)) ((o.get .x27).trans h27)
        fun t'' o' sy' => h t'' ((o.trans o').mono) (sy'.trans sy)

/-- `byIdx b is` in two runs whose `x27` is the index `idx a` of the anchor:
the comparisons from the same public `x27`, then `b (idx a)`. -/
theorem byIdx_ct {α : Type} {b : Nat → Prog isa} {Q : State → State → Prop} (idx : α → Nat) :
    ∀ {is : List Nat} {Φ : α → State → Prop},
    (∀ a t t', Φ a t → Only [.x9] t t' → t'.syms = t.syms → Φ a t') →
    (∀ a t, Φ a t → idx a ∈ is ∧ t.gpr .x27 = BitVec.ofNat 64 (idx a) ∧ t.sp = t.sp) →
    (∀ j ∈ is, j < 4096) →
    (∀ j ∈ is, RelCT isa (Two Φ) (cmpIdx j) fun _ _ => True) →
    (∀ j ∈ is, RelCT isa (Two fun a t => Φ a t ∧ idx a = j) (b j) Q) →
    RelCT isa (Two Φ) (byIdx b is) Q
  | [], _, _, hΦ, _, _, _ => RelCT.of_false fun _ _ ⟨a, h₁, _⟩ => by simpa using (hΦ a _ h₁).1
  | [j], _, _, hΦ, _, _, hb => (hb j (List.mem_singleton_self _)).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, ⟨h₁, List.mem_singleton.mp (hΦ a _ h₁).1⟩, ⟨h₂, List.mem_singleton.mp (hΦ a _ h₁).1⟩⟩)
    fun _ _ h => h
  | j :: k :: is, Φ, hkeep, hΦ, hlt, hc, hb => by
    simp only [byIdx]
    have ih := byIdx_ct idx (is := k :: is) (Φ := fun a t => Φ a t ∧ idx a ≠ j)
      (fun a t t' ⟨h, hn⟩ o sy => ⟨hkeep a t t' h o sy, hn⟩)
      (fun a t ⟨h, hn⟩ => ⟨(List.mem_cons.mp (hΦ a t h).1).resolve_left hn, (hΦ a t h).2⟩)
      (fun x hx => hlt x (List.mem_cons_of_mem _ hx))
      (fun x hx => (hc x (List.mem_cons_of_mem _ hx)).mono (fun _ _ => two_mono fun _ _ h => h.1) fun _ _ h => h)
      (fun x hx => (hb x (List.mem_cons_of_mem _ hx)).mono (fun _ _ => two_mono fun _ _ h => ⟨h.1.1, h.2⟩)
        fun _ _ h => h)
    refine RelCT.seq (two_post (Ψ := fun a t => Φ a t ∧ (t.gpr .x9 == 0) = decide (idx a = j))
      (hc j List.mem_cons_self) fun a t h => ?_) (two_ite (fun a t₁ t₂ h₁ h₂ => ?_)
        ((hb j List.mem_cons_self).mono (fun _ _ => two_mono fun a t ⟨⟨h, hz⟩, he⟩ => ⟨h, ?_⟩) fun _ _ h => h)
        (ih.mono (fun _ _ => two_mono fun a t ⟨⟨h, hz⟩, he⟩ => ⟨h, ?_⟩) fun _ _ h => h))
    · obtain ⟨hm, h27, _⟩ := hΦ a t h
      exact WP.mono (cmpIdx_ok (by have := hlt _ hm; omega_using [this]) (hlt j List.mem_cons_self) h27)
        fun t' ⟨o, hz, sy⟩ => ⟨hkeep a t t' h o sy, hz⟩
    · rw [eval_zero, eval_zero, h₁.2, h₂.2]
    · rw [eval_zero, hz] at he
      simpa using he
    · rw [eval_zero, hz] at he
      simpa using he

end VG.Proof.RsaPss.AArch64

end

end

/-!
# RSASSA-PSS signing on AArch64, calling `encode`: correctness

`code_ok`: from the precondition, `signC` keeps the calling convention, and
`out` and the result are as `RsaPss.sign` says (`Post`): the prologue
(`prologue_ok`), the check of the modulus' first byte, `emBits` and
`encode`'s arguments (`emBitsB_ok`, `encArgs_ok`), the call of `encode` for
the index of the table of `MdHash` (`byIdx_wp`, `encCall_ok`), then either zeros to `out` (`fail_ok`) or the private-key
operation on `EM` (`privArgs_ok`, `call_ok`), and the restores
(`restore_frame_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (PrivChecked)
open VG.Proof.RsaPss.AArch64 (off ebV emBitsB_ok restore_frame_ok byIdx_wp Tabs)

/-- Signing's result, and the calling convention. -/
def Post (Hs Gs : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧
    Spec.Rsa.writtenOutcome s'.mem (s.gpr .x0) (s.gpr .x3).toNat ((s'.gpr .x0).setWidth 32) (signOut Hs Gs s)

theorem setWidth_byte (b : Byte) : b.setWidth 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem eval_zero_w (s : State) (r : Reg) : isa.eval (.zero .w r) s = some ((s.gpr r).setWidth 32 == 0) := by
  simp [eval, State.read]

/-- `emBits`, `emLen` and `lo` of a call from `s`. -/
abbrev ebS (s : State) : Nat := ebV (s.gpr .x3).toNat (s.mem (s.gpr .x2)).toNat
abbrev elS (s : State) : Nat := Spec.RsaPss.emLength (ebS s)
abbrev loS (s : State) : Nat := (s.gpr .x3).toNat - elS s

section
variable {tsH tsG : List FnTable} {K : Nat} {s : State} (hp : PreS tsH tsG K s) (h0 : s.mem (s.gpr .x2) ≠ 0)
include hp h0

theorem eb_bounds : 1 ≤ ebS s ∧ ebS s ≤ Proof.RsaPss.maxEmBits ∧ loS s + elS s = (s.gpr .x3).toNat ∧ loS s ≤ 1 := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have h0' : (s.mem (s.gpr .x2)).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  have hl8 := RsaPss.log2_lt8 (s.mem (s.gpr .x2))
  unfold loS elS ebS Spec.RsaPss.emLength ebV Proof.RsaPss.maxEmBits
  omega_using [hk1, hk2, hl8]

/-- `emBits`, `emLen` and `lo`, and `encode`'s arguments. -/
theorem args_ok {u : State} (hu : AtChk s u) :
    WP isa (.block (emBitsB ++ encArgs)) u (AtEnc K s (ebS s) (elS s) (loS s)) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hx := (s.mem (s.gpr .x2)).isLt
  have h0' : (s.mem (s.gpr .x2)).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  have hx10 : u.gpr .x10 = BitVec.ofNat 64 (s.mem (s.gpr .x2)).toNat := by rw [hu.x10, setWidth_byte]
  rw [WP.block_append_iff]
  refine WP.mono (emBitsB_ok (by omega_using [hk1]) hk2 hx h0' hx10 (by rw [hu.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]))
    fun u₁ ⟨O₁, x24, x25, x26⟩ => ?_
  have hpar : AtPar K s (ebS s) (elS s) (loS s) u₁ := {
    sp := O₁.sp.trans hu.sp
    rd := O₁.rd.trans hu.rd
    wr := O₁.wr.trans hu.wr
    v := fun r hr => (O₁.vcs r hr).trans (hu.v r hr)
    mem := by rw [O₁.mem]; exact hu.mem.mono (by simp)
    fr := by rw [O₁.mem]; exact hu.fr
    x20 := (O₁.get .x20).trans hu.x20
    x23 := (O₁.get .x23).trans hu.x23
    x24 := x24
    x25 := x25
    x26 := x26
    x27 := (O₁.get .x27).trans hu.x27 }
  exact encArgs_ok hp hpar

end

/-- After `encode` returned nonzero: its encoding, after `lo` zero bytes, is
`EM`. -/
theorem main_of {Hs Gs : Spec.Mgf1.Hash} {tsH tsG : List FnTable} {K : Nat} {s t : State} (hp : PreS tsH tsG K s)
    (h0 : s.mem (s.gpr .x2) ≠ 0)
    (ht : AfterEnc Hs Gs K s (ebS s) (elS s) (loS s) t) (hb : isa.eval (.zero .w .x0) t = some false) :
    ∃ e', Spec.RsaPss.encode Hs Gs (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 9).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 10) (stackArg s 11).toNat) (ebS s) = some e' ∧
      Main K s (Spec.RsaPss.zeros (loS s) ++ e') t := by
  obtain ⟨-, -, hlok, hlo⟩ := eb_bounds hp h0
  rw [eval_zero_w] at hb
  have hres := ht.res
  revert hres
  cases Spec.RsaPss.encode Hs Gs (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 9).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 10) (stackArg s 11).toNat) (ebS s) with
  | none => intro hres; rw [hres] at hb; exact absurd hb (by decide)
  | some e' =>
    intro hres
    exact ⟨e', rfl, ht.sp, ht.rd, ht.wr, ht.x20, ht.x23, ht.v, ht.mem, ht.fr,
      em_input hlok hlo ht.z hres.2⟩

section
variable {f : MdFns} {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {tsH tsG : List FnTable} (c : PrivChecked) {K : Nat}
  (h624 : 624 ≤ K) (hcK : c.stack ≤ K)

include h624 hcK in
/-- After the check of the modulus' first byte: the encoding, then the
private-key operation or zeros. -/
theorem main_ok {s u : State} (hp : PreS tsH tsG K s) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
    (E : ESel f g tsH tsG s i T Hs Gs) (hu : AtChk s u) (hsy : u.syms = s.syms) (h0 : s.mem (s.gpr .x2) ≠ 0) :
    WP isa (seqs [.block (emBitsB ++ encArgs), byIdx (fun i => .call (encName i) (encode f (ofIdx i) g)) idxs,
      .ite (.zero .w .x0) signFail (.seq (.block privArgs) (.call c.name c.code))]) u fun t => Mid s t ∧
      Spec.Rsa.writtenOutcome t.mem (s.gpr .x0) (s.gpr .x3).toNat ((t.gpr .x0).setWidth 32) (signOut Hs Gs s) := by
  have hk1 := hp.k1
  obtain ⟨heb1, heb2, hlok, -⟩ := eb_bounds hp h0
  have hsign := signOut_enc Hs Gs (s := s) (by omega_using [hk1]) h0
  unfold seqs seqs
  refine WP.seq (WP.mono_syms (args_ok hp h0 hu) fun t ht sy => ?_)
  refine WP.seq (byIdx_wp E.mem (fun j hj => by unfold idxs at hj; simp at hj; omega_using [hj]) (ht.x27.trans E.idx)
    fun t' o sy' => WP.mono (encCall_ok hp h624 E (ht.only9 o) (by rw [sy', sy, hsy]) (by omega_using [hlok]) rfl heb1 heb2)
      fun t₂ ht₂ => ?_)
  unfold seqs
  have M₂ : Mid s t₂ := ⟨ht₂.sp, ht₂.rd, ht₂.wr, ht₂.v, ht₂.fr⟩
  refine WP.ite _ (eval_zero_w _ _) (fun hb => ?_) (fun hb => ?_)
  · -- No encoding: zeros.
    refine WP.mono (fail_ok hp M₂ ht₂.x23) fun t' ⟨m, r⟩ => ⟨m, ?_⟩
    rw [hsign]
    have hres := ht₂.res
    revert hres
    cases Spec.RsaPss.encode Hs Gs (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 9).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 10) (stackArg s 11).toNat) (ebS s) with
    | none => intro _; exact r
    | some e' =>
      intro hres
      rw [hres.1] at hb
      exact absurd hb (by decide)
  -- The encoding, and the private-key operation.
  obtain ⟨e', he', hm⟩ := main_of hp h0 ht₂ (by rw [eval_zero_w, ← hb])
  refine WP.seq (WP.mono (privArgs_ok hp hm) fun u₃ h₃ => ?_)
  refine WP.mono (call_ok c hp hcK h₃) fun t' ht' => ⟨ht'.toMid, ?_⟩
  rw [hsign]
  erw [he']
  exact ht'.res

include h624 hcK in
/-- After the prologue: the check of the modulus' first byte, then zeros or
`main_ok`. -/
theorem body_ok {s u : State} (hp : PreS tsH tsG K s) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
    (E : ESel f g tsH tsG s i T Hs Gs) (hu : AtChk s u) (hsy : u.syms = s.syms) :
    WP isa (.ite (.zero .x .x10) signFail (seqs [.block (emBitsB ++ encArgs),
      byIdx (fun i => .call (encName i) (encode f (ofIdx i) g)) idxs,
      .ite (.zero .w .x0) signFail (.seq (.block privArgs) (.call c.name c.code))])) u fun t => Mid s t ∧
      Spec.Rsa.writtenOutcome t.mem (s.gpr .x0) (s.gpr .x3).toNat ((t.gpr .x0).setWidth 32) (signOut Hs Gs s) := by
  have hk1 := hp.k1
  have hx10 : u.gpr .x10 = BitVec.ofNat 64 (s.mem (s.gpr .x2)).toNat := by rw [hu.x10, setWidth_byte]
  refine WP.ite _ (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · -- `n₀ = 0`.
    have h0 : s.mem (s.gpr .x2) = 0 := by
      rw [hx10, beq_iff_eq] at hb
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat hb
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (s.mem (s.gpr .x2)).isLt; omega_using [])] at this
      exact this
    exact WP.mono (fail_ok hp ⟨hu.sp, hu.rd, hu.wr, hu.v, hu.fr⟩ hu.x23) fun t ⟨m, r⟩ =>
      ⟨m, by rw [signOut_zero Hs Gs (by omega_using [hk1]) h0]; exact r⟩
  have h0 : s.mem (s.gpr .x2) ≠ 0 := fun h => by rw [hx10, h] at hb; exact absurd hb (by decide)
  exact main_ok c h624 hcK hp E hu hsy h0

include h624 hcK in
theorem code_ok {s : State} (hp : PreS tsH tsG K s) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
    (E : ESel f g tsH tsG s i T Hs Gs) :
    WP isa (signC f g c.name c.code) s (Post Hs Gs s) := by
  unfold signC
  refine WP.alloc (by decide) (by have := fb_toNat hp; omega_using [this]) ?_
  unfold signCBody seqs seqs seqs
  refine WP.seq (WP.mono_syms (prologue_ok hp (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
    (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])) fun u hu sy => ?_)
  refine WP.seq (WP.mono (body_ok c h624 hcK hp E hu (by rw [sy]; simp [allocated])) fun t ⟨m, r⟩ => ?_)
  refine WP.mono (restore_frame_ok m.sp m.wr m.v m.fr.sv) fun w ⟨habi, hx0, hmem⟩ mm uu fl =>
    ⟨⟨habi.1, habi.2.1, habi.2.2⟩, ?_⟩
  -- The output lies apart from the frame, whose bytes the `free` loses.
  have hb : Spec.Rsa.bytesAt mm (s.gpr .x0) (s.gpr .x3).toNat =
      Spec.Rsa.bytesAt (freed frameBytes w).mem (s.gpr .x0) (s.gpr .x3).toNat :=
    List.map_congr_left fun i hi => lost_byte (R := oR s) fl
      (hp.ko.symm.sub_right (Offset.sub_below s.sp (by unfold stk; omega_arith) (by unfold stk; omega_arith)))
      (show i < (s.gpr .x1).toNat by rw [hp.ol]; exact List.mem_range.mp hi)
  refine Proof.Rsa.writtenOutcome_of_bytesAt hb ?_
  show Spec.Rsa.writtenOutcome (freed frameBytes w).mem _ _ (((freed frameBytes w).gpr .x0).setWidth 32) _
  rw [hx0, hmem]; exact r

end

end VG.Proof.RsaPss.AArch64.Sgn

end

end

/-! ### `RsaPss.AArch64.SignCTBase`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS signing on AArch64: constant time, the public data

The pointers, the lengths, the tables' addresses and the bytes of `n` and
`e` are public (`PubS`); the digest, the salt and the private key are
secret. Two runs with the same public data as an anchor `a` (`E`) are
related at each point of the code by what correctness says there.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-! ## The public data -/

/-- The public data of an entry state `s` is the anchor `a`'s: the
pointers and lengths, and the bytes of `n` and `e`. -/
structure PubS (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ argRegs, s.gpr r = a.gpr r
  args : ∀ i < 16, stackArg s i = stackArg a i
  bn : Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x2) (a.gpr .x3).toNat
  be : Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x4) (a.gpr .x5).toNat

theorem PubS.refl (s : State) : PubS s s :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

/-- An entry state with the anchor's public data. -/
def E (tsH tsG : List FnTable) (K : Nat) (a s : State) : Prop := PreS tsH tsG K s ∧ PubS a s

namespace E
variable {tsH tsG : List FnTable} {K : Nat} {a s : State} (h : E tsH tsG K a s)
include h

theorem gpr {r : Reg} (hr : r ∈ argRegs) : s.gpr r = a.gpr r := h.2.g r hr

theorem fb : fb s = fb a := by show s.sp - _ = a.sp - _; rw [h.2.sp]

theorem n0 : s.mem (s.gpr .x2) = a.mem (a.gpr .x2) := by
  have hk := h.1.k1
  have e3 := h.gpr (r := .x3) (by decide)
  have := h.2.bn
  rw [bytesAt_cons s.mem (s.gpr .x2) (k := (s.gpr .x3).toNat) (by omega_using [hk]),
    bytesAt_cons a.mem (a.gpr .x2) (k := (a.gpr .x3).toNat) (by rw [← e3]; omega_using [hk])] at this
  exact (List.cons.inj this).1

theorem scr : scr s = scr a := h.2.args 12 (by decide)

end E

end VG.Proof.RsaPss.AArch64.Sgn

end

end

/-!
# RSASSA-PSS signing on AArch64, calling `encode`: constant time

`code_ct`: two runs of `signC` from entry states with the same public data
leak the same trace. The check of the modulus' first byte and `emBits` are
on public values (the taint analysis); the choice of `encode` by the table's
index is the same in both runs (`byIdx_ct`), whose tables name the same
functions (`ESel`); the calls of `encode` and of the private-key operation
are related by their callees' contracts (`enc_ct`, `call_ct`), and
`encode`'s result, branched on, is public: whether the salt fits
(`AfterEnc.x0`). A failure loads `out` from its slot, public by
correctness (`fail_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (PrivChecked Two Pins two_taint two_post two_map two_ite two_alloc two_mono privCallCT
  wp_ldrSp ArgsEq)
open VG.Proof.RsaPss.AArch64 (off ebV two_step pins_nil emBitsB_ok byIdx_ct cmpIdx Tabs)

namespace E
variable {tsH tsG : List FnTable} {K : Nat} {a s : State} (h : E tsH tsG K a s)
include h

theorem eb : ebS s = ebS a := by unfold ebS; rw [h.n0, h.gpr (r := .x3) (by decide)]

theorem el : elS s = elS a := by unfold elS; rw [h.eb]

theorem lo : loS s = loS a := by unfold loS; rw [h.el, h.gpr (r := .x3) (by decide)]

theorem argv : argv s = argv a := by
  unfold Sgn.argv
  rw [h.gpr (r := .x6) (by decide), h.gpr (r := .x7) (by decide), h.2.args 0 (by decide), h.2.args 1 (by decide),
    h.2.args 2 (by decide), h.2.args 3 (by decide), h.2.args 4 (by decide), h.2.args 5 (by decide),
    h.2.args 6 (by decide), h.2.args 7 (by decide), h.2.args 13 (by decide), h.scr]

end E

/-- `encode`'s result: 1 exactly when the salt fits. -/
theorem AfterEnc.x0 {Hs Gs : Spec.Mgf1.Hash} {K : Nat} {s : State} {eb el lo : Nat} {t : State}
    (h : AfterEnc Hs Gs K s eb el lo t) (hl : Hs.len = (stackArg s 9).toNat) :
    (t.gpr .x0).setWidth 32 =
      if Hs.len + (stackArg s 11).toNat + 2 ≤ Spec.RsaPss.emLength eb then (1 : BitVec 32) else 0 := by
  have hi := RsaPss.encode_isSome₂ Hs Gs (mHash := Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 9).toNat)
    (salt := Spec.Rsa.bytesAt s.mem (stackArg s 10) (stackArg s 11).toNat) (eb := eb)
    (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length, hl])
  rw [VG.Proof.RsaPkcs1Sig.bytesAt_length] at hi
  have hr := h.res
  revert hr hi
  cases Spec.RsaPss.encode Hs Gs (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 9).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 10) (stackArg s 11).toNat) eb with
  | none =>
    intro hi hr
    have hc : ¬ Hs.len + (stackArg s 11).toNat + 2 ≤ Spec.RsaPss.emLength eb := fun hc => by simp [hc] at hi
    rw [hr, ite_eq_right hc]
  | some e =>
    intro hi hr
    have hc : Hs.len + (stackArg s 11).toNat + 2 ≤ Spec.RsaPss.emLength eb := by simpa using hi.symm
    rw [hr.1, ite_eq_left hc]

/-! ## A failed check -/

/-- Zeros to `out`: its address is loaded from its slot, the caller's. -/
theorem fail_ct {tsH tsG : List FnTable} {K : Nat} {Φ : State → State → Prop}
    (hΦ : ∀ a u, Φ a u → ∃ s, E tsH tsG K a s ∧ Mid s u ∧ u.gpr .x23 = s.gpr .x3) :
    RelCT isa (Two Φ) signFail (Two fun a t => t.sp = fb a) := by
  refine two_post ?_ fun a u h => ?_
  rotate_left
  · obtain ⟨s, e, m, h23⟩ := hΦ a u h
    exact WP.mono (fail_ok e.1 m h23) fun t ⟨m', _⟩ => by rw [m'.sp, e.fb]
  unfold signFail
  refine RelCT.seq_block_append (M := isa) (l₁ := [ld .x14 sOut]) ?_
  refine two_step (Ψ := fun a t => t.sp = fb a ∧ t.gpr .x14 = a.gpr .x0 ∧ t.gpr .x23 = a.gpr .x3)
    (two_taint [] (fun a s₁ s₂ h₁ h₂ => ?_) (by taint_decide)) (fun a u h => ?_)
    (two_taint [.x14, .x23] (fun a s₁ s₂ h₁ h₂ => ⟨by rw [h₁.1, h₂.1], fun r hr => ?_⟩) (by taint_decide))
  · obtain ⟨_, e₁, m₁, _⟩ := hΦ a s₁ h₁
    obtain ⟨_, e₂, m₂, _⟩ := hΦ a s₂ h₂
    exact ⟨by rw [m₁.sp, m₂.sp, e₁.fb, e₂.fb], fun _ h => absurd h List.not_mem_nil⟩
  · obtain ⟨s, e, m, h23⟩ := hΦ a u h
    unfold ld
    refine wp_ldrSp (by decide) (by
      rw [m.sp, m.rd, m.wr]
      exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ (by decide) (by decide)))) fun u' o x =>
      wp_nil ⟨by rw [o.sp, m.sp, e.fb], ?_, by rw [o.get .x23, h23, e.gpr (by decide)]⟩
    rw [x, m.sp]
    exact (m.fr.rs (.x0, sOut) (by simp [regSlots])).trans (e.gpr (by decide))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]

/-! ## The private-key operation -/

theorem call_ct (c : PrivChecked) {tsH tsG : List FnTable} {K : Nat} (hcK : c.stack ≤ K) :
    RelCT isa (Two fun a t => ∃ s em, E tsH tsG K a s ∧ AtCall K s em t) (.call c.name c.code)
      fun _ _ => True := by
  refine privCallCT c fun t₁ t₂ ⟨a, ⟨s₁, em₁, h₁, c₁⟩, ⟨s₂, em₂, h₂, c₂⟩⟩ => ?_
  have e : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r := fun r hr => (h₁.gpr hr).trans (h₂.gpr hr).symm
  refine ⟨privOk_of c h₁.1 hcK c₁.toArgs, privOk_of c h₂.1 hcK c₂.toArgs, ⟨?_, fun r hr => ?_, fun i hi => ?_⟩, ?_, ?_⟩
  · rw [c₁.sp, c₂.sp, h₁.fb, h₂.fb]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.x0, c₂.x0, e .x0 (by decide)]
    · rw [c₁.x1, c₂.x1, e .x3 (by decide)]
    · rw [c₁.x2, c₂.x2, e .x2 (by decide)]
    · rw [c₁.x3, c₂.x3, e .x3 (by decide)]
    · rw [c₁.x4, c₂.x4, e .x4 (by decide)]
    · rw [c₁.x5, c₂.x5, e .x5 (by decide)]
    · rw [c₁.x6, c₂.x6, h₁.scr, h₂.scr]
    · rw [c₁.x7, c₂.x7, e .x3 (by decide)]
  · rw [c₁.args i hi, c₂.args i hi, h₁.argv, h₂.argv]
  · rw [c₁.x2, c₁.x3, c₂.x2, c₂.x3, bytes_wrS c₁.mem h₁.1.kn h₁.1.ns (by have := h₁.1.wn; omega_using []),
      bytes_wrS c₂.mem h₂.1.kn h₂.1.ns (by have := h₂.1.wn; omega_using []), h₁.2.bn, h₂.2.bn]
  · rw [c₁.x4, c₁.x5, c₂.x4, c₂.x5, bytes_wrS c₁.mem h₁.1.ke h₁.1.es (by have := h₁.1.we; omega_using []),
      bytes_wrS c₂.mem h₂.1.ke h₂.1.es (by have := h₂.1.we; omega_using []), h₁.2.be, h₂.2.be]

/-- An entry state with the anchor's public data, whose tables name the
functions `T` (and hash functions `Hs`, `Gs`) at the anchor's addresses,
for the index `i`. -/
abbrev ES (f : MdFns) (g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns) (tsH tsG : List FnTable) (K i : Nat) (T : Tabs)
    (Hs Gs : Spec.Mgf1.Hash) (a s : State) : Prop :=
  E tsH tsG K a s ∧ ESel f g tsH tsG s i T Hs Gs ∧ ∀ n ∈ T.names, s.syms n = a.syms n

theorem wp_and {c : Prog isa} {s : State} {P Q : State → Prop} (h₁ : WP isa c s P) (h₂ : WP isa c s Q) :
    WP isa c s fun t => P t ∧ Q t := by
  obtain ⟨t₁, s₁, e₁, p⟩ := h₁
  obtain ⟨t₂, s₂, e₂, q⟩ := h₂
  obtain ⟨rfl, rfl⟩ := Exec.det e₁ e₂
  exact ⟨t₁, s₁, e₁, p, q⟩

theorem callEntry_gpr {t : State} {r : Reg} (hr : r ∈ argRegs) : t.callEntry.gpr r = t.gpr r := by
  simp only [State.callEntry]
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

section
variable {f : MdFns} {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {tsH tsG : List FnTable} (c : PrivChecked) {K : Nat}
  (h624 : 624 ≤ K) (hcK : c.stack ≤ K) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
  (hv : ∀ s', (Enc.encK T Hs Gs).pre s' → ∃ t s'', Exec isa (encode f (ofIdx i) g) s' t s'' ∧
    abiPreserved s' s'' ∧ (Enc.encK T Hs Gs).post s' s'')
  (hct : ConstantTime isa (Enc.encK T Hs Gs).pre (Enc.encK T Hs Gs).pub (encode f (ofIdx i) g))

include h624 hv hct in
/-- Two calls of `encode` from runs with the same public data. -/
theorem enc_ct :
    RelCT isa (Two fun a t => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ s.mem (s.gpr .x2) ≠ 0 ∧
        AtEnc K s (ebS s) (elS s) (loS s) t ∧ t.syms = s.syms)
      (.call (encName i) (encode f (ofIdx i) g))
      (Two fun a t => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ s.mem (s.gpr .x2) ≠ 0 ∧
        AfterEnc Hs Gs K s (ebS s) (elS s) (loS s) t) := by
  refine two_post (RelCT.callEx (k := Enc.encK T Hs Gs) hv hct
    fun t₁ t₂ ⟨a, ⟨s₁, h₁, z₁, j₁, y₁⟩, ⟨s₂, h₂, z₂, j₂, y₂⟩⟩ => ?_) fun a t ⟨s, h, z, j, y⟩ => ?_
  · obtain ⟨b₁, b₂, l₁, -⟩ := eb_bounds h₁.1.1 z₁
    obtain ⟨c₁, c₂, l₂, -⟩ := eb_bounds h₂.1.1 z₂
    obtain ⟨r₁, w₁⟩ := enc_covers h₁.1.1 h₁.2.1 j₁ (by omega_using [l₁])
    obtain ⟨r₂, w₂⟩ := enc_covers h₂.1.1 h₂.2.1 j₂ (by omega_using [l₂])
    refine ⟨_, _, _, _, encPre_of h₁.1.1 h624 h₁.2.1 j₁ y₁ (by omega_using [l₁]) rfl b₁ b₂,
      encPre_of h₂.1.1 h624 h₂.2.1 j₂ y₂ (by omega_using [l₂]) rfl c₁ c₂, ⟨⟨?_, fun r hr => ?_, fun j hj => ?_⟩, fun n hn => ?_⟩,
      Covers.append_left r₁ (Covers.right w₁), w₁, Covers.append_left r₂ (Covers.right w₂), w₂⟩
    · show t₂.sp = t₁.sp
      rw [j₁.sp, j₂.sp, h₁.1.fb, h₂.1.fb]
    · simp only [State.withRegions_gpr]
      rw [callEntry_gpr hr, callEntry_gpr hr]
      simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [j₁.x0, j₂.x0, h₁.1.scr, h₂.1.scr, h₁.1.lo, h₂.1.lo]
      · rw [j₁.x1, j₂.x1, h₁.1.el, h₂.1.el]
      · rw [j₁.x2, j₂.x2, h₁.1.2.args 8 (by decide), h₂.1.2.args 8 (by decide)]
      · rw [j₁.x3, j₂.x3, h₁.1.2.args 10 (by decide), h₂.1.2.args 10 (by decide)]
      · rw [j₁.x4, j₂.x4, h₁.1.2.args 11 (by decide), h₂.1.2.args 11 (by decide)]
      · rw [j₁.x5, j₂.x5, h₁.1.eb, h₂.1.eb]
      · rw [j₁.x6, j₂.x6, h₁.1.scr, h₂.1.scr]
      · rw [j₁.x7, j₂.x7, h₁.1.2.args 13 (by decide), h₂.1.2.args 13 (by decide)]
    · show stackArg t₂ j = stackArg t₁ j
      rcases (by omega_using [hj] : j = 0 ∨ j = 1) with rfl | rfl
      · rw [j₁.a0, j₂.a0, h₁.1.2.args 14 (by decide), h₂.1.2.args 14 (by decide)]
      · rw [j₁.a1, j₂.a1, h₁.1.2.args 15 (by decide), h₂.1.2.args 15 (by decide)]
    · show t₂.syms n = t₁.syms n
      rw [y₁, y₂, h₁.2.2 n hn, h₂.2.2 n hn]
  · obtain ⟨b₁, b₂, l, -⟩ := eb_bounds h.1.1 z
    exact WP.mono (encCall_ok h.1.1 h624 h.2.1 j y (by omega_using [l]) rfl b₁ b₂) fun t' h' => ⟨s, h, z, h'⟩

/-- The stack's address `x10` holds the table's address. -/
theorem argT_ok {s : State} (hp : PreS tsH tsG K s) :
    WP isa (.block [arg .x10 14]) (allocated frameBytes s) fun u => u.gpr .x10 = stackArg s 14 ∧
      u.syms = s.syms ∧ u.sp = fb s ∧ u.gpr .x2 = s.gpr .x2 := by
  refine WP.of_syms ?_
  unfold arg
  refine wp_ldrSp (by decide) (by
    simp only [allocated]
    rw [show s.sp - BitVec.ofNat 64 frameBytes = fb s from rfl, ← stackArgAddr_fb]
    exact arg_in hp (Covers.left (Covers.refl _)) (j := 14) (by decide)) fun u o e => wp_nil fun sy =>
      ⟨?_, sy, by rw [o.sp]; rfl, by rw [o.get .x2]; rfl⟩
  rw [e]
  simp only [allocated]
  rw [show s.sp - BitVec.ofNat 64 frameBytes = fb s from rfl, ← stackArgAddr_fb]
  rfl

include h624 hcK hv hct in
theorem code_ct : RelCT isa (Two (ES f g tsH tsG K i T Hs Gs)) (signC f g c.name c.code) fun _ _ => True := by
  unfold signC
  refine two_alloc (R := fun _ _ => True) ?_
  unfold signCBody seqs seqs seqs
  rw [show signPrologue ++ n0 .x2 = [arg .x10 14] ++ (signPrologue.tail ++ n0 .x2) from rfl]
  refine RelCT.seq_block_append ?_
  -- The table's address.
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧
      WP isa (.block (signPrologue.tail ++ n0 .x2)) u (AtChk s) ∧ u.gpr .x10 = stackArg s 14 ∧ u.syms = s.syms ∧
      u.sp = fb s ∧ u.gpr .x2 = s.gpr .x2)
    (two_taint [] (fun _ _ _ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂]; simp only [allocated, h₁.1.2.sp, h₂.1.2.sp],
      fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
    fun a u ⟨s, h, hu⟩ => ?_) ?_
  · subst hu
    have hw := prologue_ok (u := allocated frameBytes s) h.1.1 (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
      (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])
    rw [show signPrologue ++ n0 .x2 = [arg .x10 14] ++ (signPrologue.tail ++ n0 .x2) from rfl,
      WP.block_append_iff] at hw
    exact WP.mono (wp_and hw (argT_ok h.1.1)) fun u ⟨w, x, y, p, q⟩ => ⟨s, h, w, x, y, p, q⟩
  -- The prologue.
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ AtChk s u ∧ u.syms = s.syms)
    (two_taint [.x2, .x10] (fun _ u₁ u₂ ⟨s₁, h₁, _, x₁, _, p₁, q₁⟩ ⟨s₂, h₂, _, x₂, _, p₂, q₂⟩ =>
      ⟨by rw [p₁, p₂, h₁.1.fb, h₂.1.fb], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [q₁, q₂, h₁.1.gpr (by decide), h₂.1.gpr (by decide)]
        · rw [x₁, x₂, h₁.1.2.args 14 (by decide), h₂.1.2.args 14 (by decide)]⟩)
      (by taint_decide))
    fun a u ⟨s, h, w, x, y, _⟩ => WP.mono_syms w fun t ht sy => ⟨s, h, ht, sy.trans y⟩) ?_
  refine RelCT.seq ?_ (two_taint (Φ := fun a t => t.sp = fb a) [] (fun a t₁ t₂ h₁ h₂ =>
    ⟨by rw [h₁, h₂], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
  refine two_ite (fun a u₁ u₂ ⟨s₁, h₁, j₁, _⟩ ⟨s₂, h₂, j₂, _⟩ => by
      rw [eval_zero, eval_zero, j₁.x10, j₂.x10, h₁.1.n0, h₂.1.n0])
    (fail_ct fun a u ⟨⟨s, h, j, _⟩, _⟩ => ⟨s, h.1, ⟨j.sp, j.rd, j.wr, j.v, j.fr⟩, j.x23⟩) ?_
  unfold seqs seqs
  refine RelCT.seq (two_post
    (Ψ := fun a t => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ s.mem (s.gpr .x2) ≠ 0 ∧
      AtEnc K s (ebS s) (elS s) (loS s) t ∧ t.syms = s.syms)
    (two_taint [.x10, .x20, .x23] (fun a u₁ u₂ ⟨⟨s₁, h₁, j₁, _⟩, _⟩ ⟨⟨s₂, h₂, j₂, _⟩, _⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.1.fb, h₂.1.fb], fun r hr => ?_⟩) (by taint_decide))
    fun a u ⟨⟨s, h, j, y⟩, hb⟩ => ?_) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [j₁.x10, j₂.x10, h₁.1.n0, h₂.1.n0]
    · exact (j₁.x20.trans h₁.1.scr).trans (j₂.x20.trans h₂.1.scr).symm
    · rw [j₁.x23, j₂.x23, h₁.1.gpr (by decide), h₂.1.gpr (by decide)]
  · have h0 : s.mem (s.gpr .x2) ≠ 0 := fun h0 => by
      rw [eval_zero, j.x10, h0] at hb
      exact absurd hb (by decide)
    exact WP.mono_syms (args_ok h.1.1 h0 j) fun t ht sy => ⟨s, h, h0, ht, sy.trans y⟩
  -- `encode`, for the index of the table.
  refine RelCT.seq (byIdx_ct (Q := Two fun a t => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ s.mem (s.gpr .x2) ≠ 0 ∧
      AfterEnc Hs Gs K s (ebS s) (elS s) (loS s) t) (fun _ => i) (fun a t t' ⟨s, h, z, j, y⟩ o sy => ⟨s, h, z, j.only9 o, sy.trans y⟩)
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
      exact (enc_ct h624 hv hct).mono (fun _ _ => two_mono fun _ _ h => h.1) fun _ _ h => h
    · exact RelCT.of_false fun _ _ ⟨a, h₁, _⟩ => hij h₁.2
  -- `encode`'s result.
  refine two_ite (fun a t₁ t₂ ⟨s₁, h₁, _, j₁⟩ ⟨s₂, h₂, _, j₂⟩ => by
      rw [eval_zero_w, eval_zero_w, j₁.x0 (h₁.2.1.hl.trans h₁.2.1.hD), j₂.x0 (h₂.2.1.hl.trans h₂.2.1.hD),
        h₁.1.eb, h₂.1.eb, h₁.1.2.args 11 (by decide), h₂.1.2.args 11 (by decide)])
    (fail_ct fun a u ⟨⟨s, h, _, j⟩, _⟩ => ⟨s, h.1, ⟨j.sp, j.rd, j.wr, j.v, j.fr⟩, j.x23⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s em, E tsH tsG K a s ∧ AtCall K s em t)
    (two_taint [] (fun a t₁ t₂ ⟨⟨s₁, h₁, _, j₁⟩, _⟩ ⟨⟨s₂, h₂, _, j₂⟩, _⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.1.fb, h₂.1.fb], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
    fun a t ⟨⟨s, h, z, j⟩, hb⟩ => ?_) ?_
  · obtain ⟨_, _, hm⟩ := main_of h.1.1 z j hb
    exact WP.mono (privArgs_ok h.1.1 hm) fun t' h' => ⟨s, _, h.1, h'⟩
  exact two_post (call_ct c hcK) fun a t ⟨s, em, h, hA⟩ =>
    WP.mono (call_ok c h.1 hcK hA) fun t' h' => by rw [h'.sp, h.fb]

end

end VG.Proof.RsaPss.AArch64.Sgn

end

end

/-! ### `RsaPss.AArch64.SignPCt`, which only this module used -/

section

/-! ### `RsaPss.AArch64.SignPCall`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS signing on AArch64 with the key's precomputed values: the call

`vg_rsa_pss_sign_precomputed` (`signCP`) is `vg_rsa_pss_sign`'s code but for
the call of `vg_rsa_private_checked_precomputed`, whose stack arguments 12 and
13, `pre` and `pre_len` (ours 16 and 17, `PreXS`), are the slots of the
caller's `x19` and `x20`: those registers are restored from them first, and
the restores at the end leave them out (`MidP`). The failures restore them
too (`failP_ok`); `preArgs_ok` and `callP_ok` the call.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_strx wp_nil)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_ldrSp PrivPChecked PrivPOk PrivOk privPCall privRdP privWr preR)
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytes_apart)
open VG.Proof.RsaPss.AArch64 (off)

/-- `pre`, our stack arguments 16 and 17. -/
abbrev prR (s : State) : Region := ⟨stackArg s 16, (stackArg s 17).toNat * 8⟩

/-- Our stack arguments, `pre` and `pre_len` included. -/
abbrev aR2 (s : State) : Region := ⟨stackArgAddr s 0, 144⟩

/-- What the code needs of `pre`, by name. -/
structure PreXS (K : Nat) (s : State) : Prop where
  rd : Covers [prR s, aR2 s] s.rd
  sp3 : s.sp.toNat + 144 ≤ 2 ^ 64
  oa : (oR s).Disjoint (aR2 s)
  sa : (sR s).Disjoint (aR2 s)
  ka : (kR K s).Disjoint (aR2 s)
  opr : (oR s).Disjoint (prR s)
  spr : (sR s).Disjoint (prR s)
  kpr : (kR K s).Disjoint (prR s)
  wpr : (stackArg s 16).toNat + (stackArg s 17).toNat * 8 ≤ 2 ^ 64
  prl : (stackArg s 17).toNat =
    Spec.Rsa.privatePrecomputedWords (s.gpr .x3).toNat (s.gpr .x7).toNat (stackArg s 1).toNat
  key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 16) (stackArg s 17).toNat)

/-- In the frame, after `x19` and `x20` are restored: the slots of the other
saved registers. -/
structure MidP (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  sv : Spill.Saved (fb s) s.gpr (saved.drop 2) t.mem
  x19 : t.gpr .x19 = s.gpr .x19
  x20 : t.gpr .x20 = s.gpr .x20

theorem saved_drop {s : State} {m : Mem} (h : Spill.Saved (fb s) s.gpr saved m) :
    Spill.Saved (fb s) s.gpr (saved.drop 2) m := fun p hp => h p (List.mem_of_mem_drop hp)

/-- `x19` and `x20` restored from their slots. -/
theorem reload_ok {s t : State} (hm : Mid s t) :
    WP isa (.block reload) t fun t' => MidP s t' ∧ t'.gpr .x0 = t.gpr .x0 ∧ t'.mem = t.mem := by
  unfold reload ld
  obtain rsl : ∀ {u : State} {d : Nat}, u.sp = fb s → u.rd = s.rd → u.wr = ⟨fb s, frameBytes⟩ :: s.wr →
      d + 8 ≤ frameBytes → InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 d) 8 := fun hsp hrd hwr hd => by
    rw [hsp, hrd, hwr]; exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ hd (by unfold frameBytes at hd; omega_using [hd])))
  refine wp_ldrSp (by decide) (rsl hm.sp hm.rd hm.wr (by decide)) fun u₁ o₁ e₁ => ?_
  refine wp_ldrSp (by decide) (rsl (o₁.sp.trans hm.sp) (o₁.rd.trans hm.rd) (o₁.wr.trans hm.wr) (by decide))
    fun u₂ o₂ e₂ => wp_nil ?_
  rw [hm.sp, hm.fr.sv (.x19, 96) (by decide)] at e₁
  rw [o₁.sp, hm.sp, o₁.mem, hm.fr.sv (.x20, 104) (by decide)] at e₂
  exact ⟨⟨o₂.sp.trans (o₁.sp.trans hm.sp), o₂.rd.trans (o₁.rd.trans hm.rd), o₂.wr.trans (o₁.wr.trans hm.wr),
      fun r hr => (o₂.vcs r hr).trans ((o₁.vcs r hr).trans (hm.v r hr)),
      by rw [o₂.mem, o₁.mem]; exact saved_drop hm.fr.sv,
      by rw [o₂.gpr .x19 (by decide), e₁], e₂⟩,
    by rw [o₂.gpr .x0 (by decide), o₁.gpr .x0 (by decide)], by rw [o₂.mem, o₁.mem]⟩

/-- Zeros to `out`, 0 returned, and `x19` and `x20` restored. -/
theorem failP_ok {tsH tsG : List FnTable} {K : Nat} {s t : State} (hp : PreS tsH tsG K s) (hm : Mid s t)
    (h23 : t.gpr .x23 = s.gpr .x3) :
    WP isa signFailP t fun t' => MidP s t' ∧
      Spec.Rsa.writtenOutcome t'.mem (s.gpr .x0) (s.gpr .x3).toNat ((t'.gpr .x0).setWidth 32) .invalid :=
  WP.seq (WP.mono (fail_ok hp hm h23) fun _ ⟨m, r⟩ =>
    WP.mono (reload_ok m) fun _ ⟨m', h0, hmem⟩ => ⟨m', by rw [h0, hmem]; exact r⟩)

/-- At the call of `vg_rsa_private_checked_precomputed`. -/
structure AtCallP (K : Nat) (s : State) (em : List Byte) (t : State) : Prop extends CallArgs s t where
  pre : stackArg t 12 = stackArg s 16
  prl : stackArg t 13 = stackArg s 17
  x19 : t.gpr .x19 = s.gpr .x19
  x20 : t.gpr .x20 = s.gpr .x20
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame (wrS K s) s.mem t.mem
  sv : Spill.Saved (fb s) s.gpr (saved.drop 2) t.mem
  em : Spec.Rsa.bytesAt t.mem (off (scr s) oEm) (s.gpr .x3).toNat = em

/-- Our stack argument `j < 18`, in memory changed only where the code
writes. -/
theorem argP_frameW {K : Nat} {s : State} (hx : PreXS K s) {m : Mem}
    (h : Frame (wrS K s) s.mem m) {j : Nat} (hj : j < 18) : m.readW (stackArgAddr s j) 64 = stackArg s j :=
  h.readW (r := aR2 s) (by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_using [hj]) (by have := hx.sp3; omega_using [hj]))
    (wrS_disj hx.ka hx.sa.symm) (by decide)

theorem argP_in {K : Nat} {s : State} (hx : PreXS K s) {rs : List Region} (hrd : Covers s.rd rs) {j : Nat}
    (hj : j < 18) : InRegions rs (stackArgAddr s j) 8 :=
  hrd _ _ <| hx.rd _ _ ⟨aR2 s, by simp, by
    rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_using [hj]) (by have := hx.sp3; omega_using [hj])⟩

/-- `x19` and `x20` restored, and `pre` and `pre_len` in their slots. -/
theorem preArgs_ok {tsH tsG : List FnTable} {K : Nat} {s t : State} (hp : PreS tsH tsG K s) (hx : PreXS K s)
    {em : List Byte} (ha : AtCall K s em t) : WP isa (.block preArgs) t (AtCallP K s em) := by
  unfold preArgs reload st ld arg
  simp only [List.cons_append, List.nil_append]
  obtain rsl : ∀ {u : State} {d : Nat}, u.sp = fb s → u.rd = s.rd → u.wr = ⟨fb s, frameBytes⟩ :: s.wr →
      d + 8 ≤ frameBytes → InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 d) 8 := fun hsp hrd hwr hd => by
    rw [hsp, hrd, hwr]; exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ hd (by unfold frameBytes at hd; omega_using [hd])))
  obtain hA : ∀ {u : State} (j : Nat), j < 18 → u.sp = fb s → u.rd = s.rd → u.wr = ⟨fb s, frameBytes⟩ :: s.wr →
      InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (frameBytes + 8 * j)) 8 := fun j hj hsp hrd hwr => by
    rw [hsp, hrd, ← stackArgAddr_fb]
    exact argP_in hx (Covers.left (Covers.refl _)) hj
  -- `x19`, `x20`.
  refine wp_ldrSp (by decide) (rsl ha.sp ha.rd ha.wr (by decide)) fun u₁ o₁ e₁ => ?_
  rw [ha.sp, ha.fr.sv (.x19, 96) (by decide)] at e₁
  refine wp_ldrSp (by decide) (rsl (o₁.sp.trans ha.sp) (o₁.rd.trans ha.rd) (o₁.wr.trans ha.wr) (by decide))
    fun u₂ o₂ e₂ => ?_
  rw [o₁.sp, ha.sp, o₁.mem, ha.fr.sv (.x20, 104) (by decide)] at e₂
  obtain sp₂ : u₂.sp = fb s := o₂.sp.trans (o₁.sp.trans ha.sp)
  obtain rd₂ : u₂.rd = s.rd := o₂.rd.trans (o₁.rd.trans ha.rd)
  obtain wr₂ : u₂.wr = ⟨fb s, frameBytes⟩ :: s.wr := o₂.wr.trans (o₁.wr.trans ha.wr)
  obtain mem₂ : u₂.mem = t.mem := o₂.mem.trans o₁.mem
  -- `pre`.
  refine wp_ldrSp (by decide) (hA 16 (by decide) sp₂ rd₂ wr₂) fun u₃ o₃ e₃ => ?_
  rw [sp₂, ← stackArgAddr_fb, mem₂, argP_frameW hx ha.mem (by decide)] at e₃
  refine wp_addSp (by decide) fun u₄ o₄ e₄ => ?_
  rw [o₃.sp, sp₂, BitVec.add_zero] at e₄
  refine wp_strx (a := fb s + BitVec.ofNat 64 96) (by decide) (by rw [e₄])
    (by rw [o₄.wr, o₃.wr, wr₂]; exact in_frame _ _ (by decide)) fun u₅ m₅ => ?_
  obtain sp₅ : u₅.sp = fb s := by rw [m₅.sp, o₄.sp, o₃.sp, sp₂]
  obtain rd₅ : u₅.rd = s.rd := by rw [m₅.rd, o₄.rd, o₃.rd, rd₂]
  obtain wr₅ : u₅.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [m₅.wr, o₄.wr, o₃.wr, wr₂]
  obtain mem₅ : u₅.mem = t.mem.writeW (fb s + BitVec.ofNat 64 96) (stackArg s 16) := by
    rw [m₅.mem, o₄.get .x9, e₃, o₄.mem, o₃.mem, mem₂]
  -- `pre_len`.
  refine wp_ldrSp (by decide) (hA 17 (by decide) sp₅ rd₅ wr₅) fun u₆ o₆ e₆ => ?_
  obtain c96 : (⟨fb s + BitVec.ofNat 64 96, 16⟩ : Region).Contains (fb s + BitVec.ofNat 64 96) 8 :=
    Offset.contains _ (by decide) (by decide) (by decide)
  obtain c104 : (⟨fb s + BitVec.ofNat 64 96, 16⟩ : Region).Contains (fb s + BitVec.ofNat 64 104) 8 :=
    Offset.contains _ (by decide) (by decide) (by decide)
  obtain dA : (aR2 s).Disjoint ⟨fb s + BitVec.ofNat 64 96, 16⟩ :=
    (hx.ka.sub_left (frame_sub K s (d := 96) (n := 16) (by decide))).symm
  obtain f5 : Frame [(⟨fb s + BitVec.ofNat 64 96, 16⟩ : Region)] t.mem u₅.mem := by
    rw [mem₅]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c96
  obtain c17 : (aR2 s).Contains (stackArgAddr s 17) 8 := by
    rw [stackArgAddr_eq s 17]
    exact Offset.contains_base _ (by decide) (by have := hx.sp3; omega_using [])
  obtain m17 : u₅.mem.readW (stackArgAddr s 17) 64 = stackArg s 17 := by
    rw [f5.readW c17 (fun r hr => by rw [List.mem_singleton.mp hr]; exact dA) (by decide)]
    exact argP_frameW hx ha.mem (by decide)
  rw [sp₅, ← stackArgAddr_fb, m17] at e₆
  refine wp_addSp (by decide) fun u₇ o₇ e₇ => ?_
  rw [o₆.sp, sp₅, BitVec.add_zero] at e₇
  refine wp_strx (a := fb s + BitVec.ofNat 64 104) (by decide) (by rw [e₇])
    (by rw [o₇.wr, o₆.wr, wr₅]; exact in_frame _ _ (by decide)) fun u₈ m₈ => wp_nil ?_
  obtain mem₈ : u₈.mem = (t.mem.writeW (fb s + BitVec.ofNat 64 96) (stackArg s 16)).writeW
      (fb s + BitVec.ofNat 64 104) (stackArg s 17) := by
    rw [m₈.mem, o₇.get .x9, e₆, o₇.mem, o₆.mem, mem₅]
  obtain fW : Frame [(⟨fb s + BitVec.ofNat 64 96, 16⟩ : Region)] t.mem u₈.mem := by
    rw [mem₈]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c96).writeW (List.mem_singleton_self _) _ c104
  obtain r96 : ∀ {d : Nat}, d + 8 ≤ 96 ∨ 112 ≤ d → d + 8 ≤ frameBytes →
      u₈.mem.readW (fb s + BitVec.ofNat 64 d) 64 = t.mem.readW (fb s + BitVec.ofNat 64 d) 64 := fun hd hd' =>
    fW.readW (r := ⟨fb s + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by omega_using [hd]) (by unfold frameBytes at hd'; omega_using [hd']) (by decide)) (by decide)
  obtain gO : ∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x9 → r ≠ .x16 → u₈.gpr r = t.gpr r := fun r h1 h2 h3 h4 => by
    rw [m₈.gpr, o₇.gpr r (by simpa using h4), o₆.gpr r (by simpa using h3), m₅.gpr, o₄.gpr r (by simpa using h4),
      o₃.gpr r (by simpa using h3), o₂.gpr r (by simpa using h2), o₁.gpr r (by simpa using h1)]
  obtain sp₈ : u₈.sp = fb s := by rw [m₈.sp, o₇.sp, o₆.sp, sp₅]
  obtain hst : ∀ i, u₈.mem.readW (u₈.sp + BitVec.ofNat 64 (8 * i)) 64 = stackArg u₈ i := fun _ => rfl
  refine {
    sp := sp₈
    rd := (by rw [m₈.rd, o₇.rd, o₆.rd, rd₅])
    wr := (by rw [m₈.wr, o₇.wr, o₆.wr, wr₅])
    x0 := (by rw [gO .x0 (by decide) (by decide) (by decide) (by decide), ha.x0])
    x1 := (by rw [gO .x1 (by decide) (by decide) (by decide) (by decide), ha.x1])
    x2 := (by rw [gO .x2 (by decide) (by decide) (by decide) (by decide), ha.x2])
    x3 := (by rw [gO .x3 (by decide) (by decide) (by decide) (by decide), ha.x3])
    x4 := (by rw [gO .x4 (by decide) (by decide) (by decide) (by decide), ha.x4])
    x5 := (by rw [gO .x5 (by decide) (by decide) (by decide) (by decide), ha.x5])
    x6 := (by rw [gO .x6 (by decide) (by decide) (by decide) (by decide), ha.x6])
    x7 := (by rw [gO .x7 (by decide) (by decide) (by decide) (by decide), ha.x7])
    args := fun i hi => ?_
    pre := ?_
    prl := ?_
    x19 := (by rw [m₈.gpr, o₇.gpr .x19 (by decide), o₆.gpr .x19 (by decide), m₅.gpr, o₄.gpr .x19 (by decide),
      o₃.gpr .x19 (by decide), o₂.gpr .x19 (by decide), e₁])
    x20 := (by rw [m₈.gpr, o₇.gpr .x20 (by decide), o₆.gpr .x20 (by decide), m₅.gpr, o₄.gpr .x20 (by decide),
      o₃.gpr .x20 (by decide), e₂])
    v := fun r hr => (by
      rw [m₈.vcs r hr, o₇.vcs r hr, o₆.vcs r hr, m₅.vcs r hr, o₄.vcs r hr, o₃.vcs r hr, o₂.vcs r hr,
        o₁.vcs r hr, ha.v r hr])
    mem := ha.mem.trans (fW.sub fun r hr => (by
      rw [List.mem_singleton.mp hr]
      exact ⟨⟨fb s, frameBytes⟩, List.mem_cons_self, Offset.sub_base _ (by decide)⟩))
    sv := fun p hp' => (by
      have := saved_offs p (List.mem_of_mem_drop hp')
      obtain h112 : 112 ≤ p.2 := (show ∀ q ∈ saved.drop 2, 112 ≤ q.2 by decide) p hp'
      rw [r96 (.inr h112) (by unfold frameBytes; omega_using [this])]
      exact ha.fr.sv p (List.mem_of_mem_drop hp'))
    em := ?_ }
  · show u₈.mem.readW (u₈.sp + BitVec.ofNat 64 (8 * i)) 64 = _
    rw [sp₈, r96 (.inl (by omega_using [hi])) (by unfold frameBytes; omega_using [hi])]
    have := ha.args i hi
    simp only [stackArg, stackArgAddr, ha.sp] at this
    exact this
  · show u₈.mem.readW (u₈.sp + BitVec.ofNat 64 (8 * 12)) 64 = _
    rw [sp₈, mem₈, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64]
  · show u₈.mem.readW (u₈.sp + BitVec.ofNat 64 (8 * 13)) 64 = _
    rw [sp₈, mem₈, Mem.readW_writeW_self64]
  · rw [← ha.em]
    obtain hemR : (kR K s).Disjoint ⟨off (scr s) oEm, (s.gpr .x3).toNat⟩ := hp.ks.sub_right (em_sub hp)
    exact bytes_apart (R := ⟨off (scr s) oEm, (s.gpr .x3).toNat⟩) fW
      (hemR.symm.sub_right (frame_sub K s (d := 96) (n := 16) (by decide))) (by dsimp only; omega_using [])


/-! ## The call -/

theorem privArgsP_ok {tsH tsG : List FnTable} {K : Nat} {s t : State} (hp : PreS tsH tsG K s) (hx : PreXS K s)
    {em : List Byte} (hm : Main K s em t) : WP isa (.block privArgsP) t (AtCallP K s em) := by
  unfold privArgsP
  rw [WP.block_append_iff]
  exact WP.mono (privArgs_ok hp hm) fun _ h => preArgs_ok hp hx h

/-- `pre`'s words are few. -/
theorem prl_le {tsH tsG : List FnTable} {K : Nat} {s : State} (hp : PreS tsH tsG K s) (hx : PreXS K s) : (stackArg s 17).toNat ≤ 1024 := by
  have := hp.k2; have := hp.p2; have := hp.q2
  rw [hx.prl]
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.primeWords,
    Spec.Rsa.modulusWords]
  omega_arith

theorem privPOk_ofP (c : PrivPChecked) {tsH tsG : List FnTable} {K : Nat} {s t : State} (hp : PreS tsH tsG K s)
    (hx : PreXS K s) (hcK : c.stack ≤ K) {em : List Byte} (ha : AtCallP K s em t) : PrivPOk c.stack t := by
  obtain hfb := fb_toNat hp
  obtain hkb := kb_toNat hp
  have hcl := c.le
  obtain hK : Region.Sub ⟨fb s - BitVec.ofNat 64 c.stack, c.stack⟩ (kR K s) := fun a h =>
    (Offset.sub_below (fb s) (a := c.stack) (b := K) (n := c.stack) (m := K) hcK (by omega_using [hcK]) a h) |>
      fun h' => by
        obtain e : fb s - BitVec.ofNat 64 K = kb K s := by rw [fb_eq K, BitVec.add_sub_cancel]
        rw [e] at h'
        exact Region.sub_prefix (by unfold stk; omega_using []) a h'
  obtain a1 : stackArg t 1 = s.gpr .x7 := ha.args 1 (by decide)
  obtain a3 : stackArg t 3 = stackArg s 1 := ha.args 3 (by decide)
  obtain a0 : stackArg t 0 = s.gpr .x6 := ha.args 0 (by decide)
  obtain a2 : stackArg t 2 = stackArg s 0 := ha.args 2 (by decide)
  obtain a10 : stackArg t 10 = off (scr s) oRsa := ha.args 10 (by decide)
  obtain a11 : stackArg t 11 = stackArg s 13 - BitVec.ofNat 64 1024 := ha.args 11 (by decide)
  obtain hO : (⟨s.gpr .x0, (s.gpr .x3).toNat⟩ : Region) = oR s := by
    show (⟨s.gpr .x0, (s.gpr .x3).toNat⟩ : Region) = ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    rw [hp.ol]
  obtain f112 : Region.Sub ⟨fb s, 112⟩ (kR K s) := by
    have := frame_sub K s (d := 0) (n := 112) (by decide); rwa [BitVec.add_zero] at this
  obtain hP : preR t = prR s := by simp only [preR, ha.pre, ha.prl]
  obtain hw : 8 * (stackArg s 17).toNat < 2 ^ 64 := by have := prl_le hp hx; omega_using [this]
  obtain hpre : Spec.Rsa.wordsAt t.mem (stackArg s 16) (stackArg s 17).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 16) (stackArg s 17).toNat :=
    VG.Proof.Rsa.wordsAt_frame ha.mem hw (wrS_disj (by rw [Nat.mul_comm]; exact hx.kpr)
      (by rw [Nat.mul_comm]; exact hx.spr.symm))
  obtain hl : ∀ {p : Addr} {len : Nat}, p.toNat + len ≤ 2 ^ 64 → len ≤ 2 ^ 64 := fun h => by omega_using [h]
  refine ⟨privOk_of c hp hcK ha.toCallArgs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ha.sp]; have := hfb; unfold frameBytes at this; omega_using [this]
  · rw [ha.x0, ha.x1, ha.sp, hO]; exact (hp.ko.sub_left f112).symm
  · rw [a10, a11, ha.sp]; exact (hp.ks.sub_left f112).symm.sub_left (sc_sub hp)
  · rw [ha.sp]; exact (Offset.base_disjoint_below (fb s) (n := c.stack) (k := 112) (by omega_using [hcl])).symm
  · rw [hP, ha.x0, ha.x1, hO]; exact hx.opr
  · rw [hP, a10, a11]; exact hx.spr.sub_left (sc_sub hp)
  · rw [hP, ha.sp]; exact hx.kpr.sub_left hK
  · rw [ha.pre, ha.prl]; exact hx.wpr
  · rw [hP, ha.sp, ha.rd]
    refine Covers.cons (Covers.left (Covers.trans (Covers.one ⟨prR s, by simp, Region.contains_self _ _⟩) hx.rd))
      (Covers.right (Covers.one ?_))
    rw [ha.wr]
    exact in_frame s s.wr (d := 0) (n := 112) (by decide) |> fun h => by simpa using h
  · rw [ha.prl, ha.x3, a1, a3]; exact hx.prl
  · rw [ha.x2, ha.x3, a0, a1, a2, a3, ha.pre, ha.prl, hpre,
      bytes_wrS ha.mem hp.kn hp.ns (hl hp.wn), bytes_wrS ha.mem hp.kp hp.ps (hl hp.wp),
      bytes_wrS ha.mem hp.kq hp.qs (hl hp.wq)]
    exact hx.key

/-- After the call: `MidP`, and `out` written with the result. -/
structure AfterCallP (s : State) (em : List Byte) (t : State) : Prop extends MidP s t where
  res : Spec.Rsa.writtenOutcome t.mem (s.gpr .x0) (s.gpr .x3).toNat ((t.gpr .x0).setWidth 32) (privOut s em)

theorem callP_ok (c : PrivPChecked) {tsH tsG : List FnTable} {K : Nat} {s t : State} (hp : PreS tsH tsG K s)
    (hx : PreXS K s) (hcK : c.stack ≤ K) {em : List Byte} (ha : AtCallP K s em t) :
    WP isa (.call c.name c.code) t (AfterCallP s em) := by
  obtain hfb := fb_toNat hp
  obtain hkb := kb_toNat hp
  have hcl := c.le
  have hd := c.depth
  obtain a1 : stackArg t 1 = s.gpr .x7 := ha.args 1 (by decide)
  obtain a0 : stackArg t 0 = s.gpr .x6 := ha.args 0 (by decide)
  obtain a2 : stackArg t 2 = stackArg s 0 := ha.args 2 (by decide)
  obtain a3 : stackArg t 3 = stackArg s 1 := ha.args 3 (by decide)
  obtain a4 : stackArg t 4 = stackArg s 2 := ha.args 4 (by decide)
  obtain a6 : stackArg t 6 = stackArg s 4 := ha.args 6 (by decide)
  obtain a8 : stackArg t 8 = stackArg s 6 := ha.args 8 (by decide)
  obtain a10 : stackArg t 10 = off (scr s) oRsa := ha.args 10 (by decide)
  obtain a11 : stackArg t 11 = stackArg s 13 - BitVec.ofNat 64 1024 := ha.args 11 (by decide)
  refine privPCall c (privPOk_ofP c hp hx hcK ha) fun s' hrd' hwr' hsp' hf hpres hvs hpost => ?_
  simp only [privWr] at hf
  rw [ha.x0, ha.x1, a10, a11, ha.sp] at hf
  obtain hl : ∀ {p : Addr} {len : Nat}, p.toNat + len ≤ 2 ^ 64 → len ≤ 2 ^ 64 := fun h => by omega_using [h]
  rw [ha.x0, ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, a0, a1, a2, a3, a4, a6, a8, ha.em,
    bytes_wrS ha.mem hp.kn hp.ns (hl hp.wn), bytes_wrS ha.mem hp.ke hp.es (hl hp.we),
    bytes_wrS ha.mem hp.kp hp.ps (hl hp.wp), bytes_wrS ha.mem hp.kq hp.qs (hl hp.wq),
    bytes_wrS ha.mem (len := (s.gpr .x7).toNat) (by rw [← hp.hdp]; exact hp.kdp) (by rw [← hp.hdp]; exact hp.dps)
      (by have := hp.wdp; rw [hp.hdp] at this; omega_using []),
    bytes_wrS ha.mem (len := (stackArg s 1).toNat) (by rw [← hp.hdq]; exact hp.kdq)
      (by rw [← hp.hdq]; exact hp.dqs) (by have := hp.wdq; rw [hp.hdq] at this; omega_using []),
    bytes_wrS ha.mem (len := (s.gpr .x7).toNat) (by rw [← hp.hqi]; exact hp.kqi) (by rw [← hp.hqi]; exact hp.qis)
      (by have := hp.wqi; rw [hp.hqi] at this; omega_using [])] at hpost
  obtain hO : (⟨s.gpr .x0, (s.gpr .x3).toNat⟩ : Region) = oR s := by
    show (⟨s.gpr .x0, (s.gpr .x3).toNat⟩ : Region) = ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    rw [hp.ol]
  obtain f72 : Region.Sub ⟨fb s + BitVec.ofNat 64 112, 72⟩ (kR K s) := frame_sub K s (by decide)
  exact {
    sp := hsp'.trans ha.sp
    rd := hrd'.trans ha.rd
    wr := hwr'.trans ha.wr
    v := fun r hr => (hvs r hr).trans (ha.v r hr)
    sv := ha.sv.frame_in (lo := 112) (n := 72) (by decide) hf (fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl) | rfl
      · rw [hO]; exact hp.ko.sub_left f72
      · exact (hp.ks.sub_left f72).sub_right (sc_sub hp)
      · exact Offset.disjoint_below _ (by omega_using [hcl, hd]))
    x19 := (hpres .x19 (by decide) (by decide)).trans ha.x19
    x20 := (hpres .x20 (by decide) (by decide)).trans ha.x20
    res := hpost }


/-! ## The function -/

section
variable {f : MdFns} {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {tsH tsG : List FnTable} (c : PrivPChecked) {K : Nat}
  (h624 : 624 ≤ K) (hcK : c.stack ≤ K)

open VG.Proof.MlKem.AArch64 (eval_zero)
open VG.Proof.RsaPss.AArch64 (ebV byIdx_wp Tabs restoreP_frame_ok)

include h624 hcK in
theorem mainP_ok {s u : State} (hp : PreS tsH tsG K s) (hx : PreXS K s) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
    (E : ESel f g tsH tsG s i T Hs Gs) (hu : AtChk s u) (hsy : u.syms = s.syms) (h0 : s.mem (s.gpr .x2) ≠ 0) :
    WP isa (seqs [.block (emBitsB ++ encArgs), byIdx (fun i => .call (encName i) (encode f (ofIdx i) g)) idxs,
      .ite (.zero .w .x0) signFailP (.seq (.block privArgsP) (.call c.name c.code))]) u fun t => MidP s t ∧
      Spec.Rsa.writtenOutcome t.mem (s.gpr .x0) (s.gpr .x3).toNat ((t.gpr .x0).setWidth 32) (signOut Hs Gs s) := by
  have hk1 := hp.k1
  obtain ⟨heb1, heb2, hlok, -⟩ := eb_bounds hp h0
  obtain hsign := signOut_enc Hs Gs (s := s) (by omega_using [hk1]) h0
  unfold seqs seqs
  refine WP.seq (WP.mono_syms (args_ok hp h0 hu) fun t ht sy => ?_)
  refine WP.seq (byIdx_wp E.mem (fun j hj => by unfold idxs at hj; simp at hj; omega_using [hj]) (ht.x27.trans E.idx)
    fun t' o sy' => WP.mono (encCall_ok hp h624 E (ht.only9 o) (by rw [sy', sy, hsy]) (by omega_using [hlok]) rfl heb1 heb2)
      fun t₂ ht₂ => ?_)
  unfold seqs
  obtain M₂ : Mid s t₂ := ⟨ht₂.sp, ht₂.rd, ht₂.wr, ht₂.v, ht₂.fr⟩
  refine WP.ite _ (eval_zero_w _ _) (fun hb => ?_) (fun hb => ?_)
  · refine WP.mono (failP_ok hp M₂ ht₂.x23) fun t' ⟨m, r⟩ => ⟨m, ?_⟩
    rw [hsign]
    have hres := ht₂.res
    revert hres
    cases Spec.RsaPss.encode Hs Gs (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 9).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 10) (stackArg s 11).toNat) (ebS s) with
    | none => intro _; exact r
    | some e' =>
      intro hres
      rw [hres.1] at hb
      exact absurd hb (by decide)
  obtain ⟨e', he', hm⟩ := main_of hp h0 ht₂ (by rw [eval_zero_w, ← hb])
  refine WP.seq (WP.mono (privArgsP_ok hp hx hm) fun u₃ h₃ => ?_)
  refine WP.mono (callP_ok c hp hx hcK h₃) fun t' ht' => ⟨ht'.toMidP, ?_⟩
  rw [hsign]
  erw [he']
  exact ht'.res

include h624 hcK in
theorem bodyP_ok {s u : State} (hp : PreS tsH tsG K s) (hx : PreXS K s) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
    (E : ESel f g tsH tsG s i T Hs Gs) (hu : AtChk s u) (hsy : u.syms = s.syms) :
    WP isa (.ite (.zero .x .x10) signFailP (seqs [.block (emBitsB ++ encArgs),
      byIdx (fun i => .call (encName i) (encode f (ofIdx i) g)) idxs,
      .ite (.zero .w .x0) signFailP (.seq (.block privArgsP) (.call c.name c.code))])) u fun t => MidP s t ∧
      Spec.Rsa.writtenOutcome t.mem (s.gpr .x0) (s.gpr .x3).toNat ((t.gpr .x0).setWidth 32) (signOut Hs Gs s) := by
  have hk1 := hp.k1
  obtain hx10 : u.gpr .x10 = BitVec.ofNat 64 (s.mem (s.gpr .x2)).toNat := by rw [hu.x10, setWidth_byte]
  refine WP.ite _ (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · have h0 : s.mem (s.gpr .x2) = 0 := by
      rw [hx10, beq_iff_eq] at hb
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat hb
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (s.mem (s.gpr .x2)).isLt; omega_using [])] at this
      exact this
    exact WP.mono (failP_ok hp ⟨hu.sp, hu.rd, hu.wr, hu.v, hu.fr⟩ hu.x23) fun t ⟨m, r⟩ =>
      ⟨m, by rw [signOut_zero Hs Gs (by omega_using [hk1]) h0]; exact r⟩
  obtain h0 : s.mem (s.gpr .x2) ≠ 0 := fun h => by rw [hx10, h] at hb; exact absurd hb (by decide)
  exact mainP_ok c h624 hcK hp hx E hu hsy h0

include h624 hcK in
theorem codeP_ok {s : State} (hp : PreS tsH tsG K s) (hx : PreXS K s) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
    (E : ESel f g tsH tsG s i T Hs Gs) :
    WP isa (signCP f g c.name c.code) s (Post Hs Gs s) := by
  unfold signCP
  refine WP.alloc (by decide) (by have := fb_toNat hp; omega_using [this]) ?_
  unfold signCBodyP seqs seqs seqs
  refine WP.seq (WP.mono_syms (prologue_ok hp (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
    (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])) fun u hu sy => ?_)
  refine WP.seq (WP.mono (bodyP_ok c h624 hcK hp hx E hu (by rw [sy]; simp [allocated])) fun t ⟨m, r⟩ => ?_)
  refine WP.mono (restoreP_frame_ok m.sp m.wr m.v m.sv m.x19 m.x20) fun w ⟨habi, hx0, hmem⟩ mm uu fl =>
    ⟨⟨habi.1, habi.2.1, habi.2.2⟩, ?_⟩
  -- The output lies apart from the frame, whose bytes the `free` loses.
  have hb : Spec.Rsa.bytesAt mm (s.gpr .x0) (s.gpr .x3).toNat =
      Spec.Rsa.bytesAt (freed frameBytes w).mem (s.gpr .x0) (s.gpr .x3).toNat :=
    List.map_congr_left fun i hi => lost_byte (R := oR s) fl
      (hp.ko.symm.sub_right (Offset.sub_below s.sp (by unfold stk; omega_arith) (by unfold stk; omega_arith)))
      (show i < (s.gpr .x1).toNat by rw [hp.ol]; exact List.mem_range.mp hi)
  refine Proof.Rsa.writtenOutcome_of_bytesAt hb ?_
  show Spec.Rsa.writtenOutcome (freed frameBytes w).mem _ _ (((freed frameBytes w).gpr .x0).setWidth 32) _
  rw [hx0, hmem]; exact r

end

end VG.Proof.RsaPss.AArch64.Sgn

end

end

/-!
# RSASSA-PSS signing on AArch64 with the key's precomputed values: constant time

`codeP_ct`: `code_ct`'s runs, from entry states that also agree on `pre`'s
address and length and on the modulus' values in it (`PubX`): a failure
restores `x19` and `x20` from their slots (`failP_ct`), and the call of
`vg_rsa_private_checked_precomputed` is related by its contract
(`callP_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (PrivPChecked Two Pins two_taint two_post two_map two_ite two_alloc two_mono
  privPCallCT wp_ldrSp ArgsEq)
open VG.Proof.RsaPss.AArch64 (off ebV two_step pins_nil emBitsB_ok byIdx_ct cmpIdx Tabs)

/-- The public data of `pre`: its address and length, and the modulus'
values in it. -/
def PubX (a s : State) : Prop :=
  stackArg s 16 = stackArg a 16 ∧ stackArg s 17 = stackArg a 17 ∧
    Spec.Rsa.wordsAt s.mem (stackArg s 16) (Spec.Rsa.precomputedWords (s.gpr .x3).toNat) =
      Spec.Rsa.wordsAt a.mem (stackArg a 16) (Spec.Rsa.precomputedWords (a.gpr .x3).toNat)

/-- An entry state with the anchor's public data, `pre`'s included. -/
def EP (tsH tsG : List FnTable) (K : Nat) (a s : State) : Prop := E tsH tsG K a s ∧ (PreXS K s ∧ PubX a s)

/-- `ES`, with `pre`. -/
abbrev ESP (f : MdFns) (g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns) (tsH tsG : List FnTable) (K i : Nat) (T : Tabs)
    (Hs Gs : Spec.Mgf1.Hash) (a s : State) : Prop :=
  ES f g tsH tsG K i T Hs Gs a s ∧ (PreXS K s ∧ PubX a s)

/-- Zeros to `out`, and `x19` and `x20` restored. -/
theorem failP_ct {tsH tsG : List FnTable} {K : Nat} {Φ : State → State → Prop}
    (hΦ : ∀ a u, Φ a u → ∃ s, E tsH tsG K a s ∧ Mid s u ∧ u.gpr .x23 = s.gpr .x3) :
    RelCT isa (Two Φ) signFailP (Two fun a t => t.sp = fb a) := by
  refine two_post ?_ fun a u h => ?_
  · unfold signFailP
    exact RelCT.seq (fail_ct hΦ) (two_taint (Φ := fun a t => t.sp = fb a) [] (fun a t₁ t₂ h₁ h₂ =>
      ⟨by rw [h₁, h₂], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
  · obtain ⟨s, e, m, h23⟩ := hΦ a u h
    exact WP.mono (failP_ok e.1 m h23) fun t ⟨m', _⟩ => by rw [m'.sp, e.fb]

/-- The modulus' values in `pre`, at the call. -/
theorem preWords_eq {tsH tsG : List FnTable} {K : Nat} {s t : State} (hp : PreS tsH tsG K s) (hx : PreXS K s)
    {em : List Byte} (ha : AtCallP K s em t) :
    Spec.Rsa.wordsAt t.mem (stackArg t 12) (Spec.Rsa.precomputedWords (t.gpr .x3).toNat) =
      Spec.Rsa.wordsAt s.mem (stackArg s 16) (Spec.Rsa.precomputedWords (s.gpr .x3).toNat) := by
  rw [ha.pre, ha.x3]
  have hle : Spec.Rsa.precomputedWords (s.gpr .x3).toNat ≤ (stackArg s 17).toNat := by
    rw [hx.prl]; simp only [Spec.Rsa.privatePrecomputedWords]; omega_using []
  have hw := prl_le hp hx
  have sub : Region.Sub ⟨stackArg s 16, 8 * Spec.Rsa.precomputedWords (s.gpr .x3).toNat⟩ (prR s) :=
    Region.sub_prefix (by omega_using [hle])
  exact VG.Proof.Rsa.wordsAt_frame ha.mem (by omega_using [hle, hw])
    (wrS_disj (hx.kpr.sub_right sub) (hx.spr.sub_right sub).symm)

theorem callP_ct (c : PrivPChecked) {tsH tsG : List FnTable} {K : Nat} (hcK : c.stack ≤ K) :
    RelCT isa (Two fun a t => ∃ s em, EP tsH tsG K a s ∧ AtCallP K s em t) (.call c.name c.code)
      fun _ _ => True := by
  refine privPCallCT c fun t₁ t₂ ⟨a, ⟨s₁, em₁, h₁, c₁⟩, ⟨s₂, em₂, h₂, c₂⟩⟩ => ?_
  have e : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r := fun r hr => (h₁.1.gpr hr).trans (h₂.1.gpr hr).symm
  refine ⟨privPOk_ofP c h₁.1.1 h₁.2.1 hcK c₁, privPOk_ofP c h₂.1.1 h₂.2.1 hcK c₂,
    ⟨?_, fun r hr => ?_, fun i hi => ?_⟩, ?_, ?_, ?_⟩
  · rw [c₁.sp, c₂.sp, h₁.1.fb, h₂.1.fb]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.x0, c₂.x0, e .x0 (by decide)]
    · rw [c₁.x1, c₂.x1, e .x3 (by decide)]
    · rw [c₁.x2, c₂.x2, e .x2 (by decide)]
    · rw [c₁.x3, c₂.x3, e .x3 (by decide)]
    · rw [c₁.x4, c₂.x4, e .x4 (by decide)]
    · rw [c₁.x5, c₂.x5, e .x5 (by decide)]
    · rw [c₁.x6, c₂.x6, h₁.1.scr, h₂.1.scr]
    · rw [c₁.x7, c₂.x7, e .x3 (by decide)]
  · rcases (by omega_using [hi] : i < 12 ∨ i = 12 ∨ i = 13) with h | rfl | rfl
    · rw [c₁.args i h, c₂.args i h, h₁.1.argv, h₂.1.argv]
    · rw [c₁.pre, c₂.pre, h₁.2.2.1, h₂.2.2.1]
    · rw [c₁.prl, c₂.prl, h₁.2.2.2.1, h₂.2.2.2.1]
  · rw [c₁.x2, c₁.x3, c₂.x2, c₂.x3, bytes_wrS c₁.mem h₁.1.1.kn h₁.1.1.ns (by have := h₁.1.1.wn; omega_using []),
      bytes_wrS c₂.mem h₂.1.1.kn h₂.1.1.ns (by have := h₂.1.1.wn; omega_using []), h₁.1.2.bn, h₂.1.2.bn]
  · rw [c₁.x4, c₁.x5, c₂.x4, c₂.x5, bytes_wrS c₁.mem h₁.1.1.ke h₁.1.1.es (by have := h₁.1.1.we; omega_using []),
      bytes_wrS c₂.mem h₂.1.1.ke h₂.1.1.es (by have := h₂.1.1.we; omega_using []), h₁.1.2.be, h₂.1.2.be]
  · rw [preWords_eq h₁.1.1 h₁.2.1 c₁, preWords_eq h₂.1.1 h₂.2.1 c₂, h₁.2.2.2.2, h₂.2.2.2.2]

section
variable {f : MdFns} {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {tsH tsG : List FnTable} (c : PrivPChecked) {K : Nat}
  (h624 : 624 ≤ K) (hcK : c.stack ≤ K) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
  (hv : ∀ s', (Enc.encK T Hs Gs).pre s' → ∃ t s'', Exec isa (encode f (ofIdx i) g) s' t s'' ∧
    abiPreserved s' s'' ∧ (Enc.encK T Hs Gs).post s' s'')
  (hct : ConstantTime isa (Enc.encK T Hs Gs).pre (Enc.encK T Hs Gs).pub (encode f (ofIdx i) g))

include h624 hcK hv hct in
theorem codeP_ct : RelCT isa (Two (ESP f g tsH tsG K i T Hs Gs)) (signCP f g c.name c.code) fun _ _ => True := by
  unfold signCP
  refine two_alloc (R := fun _ _ => True) ?_
  unfold signCBodyP seqs seqs seqs
  rw [show signPrologue ++ n0 .x2 = [arg .x10 14] ++ (signPrologue.tail ++ n0 .x2) from rfl]
  refine RelCT.seq_block_append ?_
  -- The table's address.
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s, ESP f g tsH tsG K i T Hs Gs a s ∧
      WP isa (.block (signPrologue.tail ++ n0 .x2)) u (AtChk s) ∧ u.gpr .x10 = stackArg s 14 ∧ u.syms = s.syms ∧
      u.sp = fb s ∧ u.gpr .x2 = s.gpr .x2)
    (two_taint [] (fun _ _ _ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂]; simp only [allocated, h₁.1.1.2.sp, h₂.1.1.2.sp],
      fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
    fun a u ⟨s, h, hu⟩ => ?_) ?_
  · subst hu
    have hw := prologue_ok (u := allocated frameBytes s) h.1.1.1 (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
      (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])
    rw [show signPrologue ++ n0 .x2 = [arg .x10 14] ++ (signPrologue.tail ++ n0 .x2) from rfl,
      WP.block_append_iff] at hw
    exact WP.mono (wp_and hw (argT_ok h.1.1.1)) fun u ⟨w, x, y, p, q⟩ => ⟨s, h, w, x, y, p, q⟩
  -- The prologue.
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s, ESP f g tsH tsG K i T Hs Gs a s ∧ AtChk s u ∧ u.syms = s.syms)
    (two_taint [.x2, .x10] (fun _ u₁ u₂ ⟨s₁, h₁, _, x₁, _, p₁, q₁⟩ ⟨s₂, h₂, _, x₂, _, p₂, q₂⟩ =>
      ⟨by rw [p₁, p₂, h₁.1.1.fb, h₂.1.1.fb], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [q₁, q₂, h₁.1.1.gpr (by decide), h₂.1.1.gpr (by decide)]
        · rw [x₁, x₂, h₁.1.1.2.args 14 (by decide), h₂.1.1.2.args 14 (by decide)]⟩)
      (by taint_decide))
    fun a u ⟨s, h, w, x, y, _⟩ => WP.mono_syms w fun t ht sy => ⟨s, h, ht, sy.trans y⟩) ?_
  refine RelCT.seq ?_ (two_taint (Φ := fun a t => t.sp = fb a) [] (fun a t₁ t₂ h₁ h₂ =>
    ⟨by rw [h₁, h₂], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
  refine two_ite (fun a u₁ u₂ ⟨s₁, h₁, j₁, _⟩ ⟨s₂, h₂, j₂, _⟩ => by
      rw [eval_zero, eval_zero, j₁.x10, j₂.x10, h₁.1.1.n0, h₂.1.1.n0])
    (failP_ct fun a u ⟨⟨s, h, j, _⟩, _⟩ => ⟨s, h.1.1, ⟨j.sp, j.rd, j.wr, j.v, j.fr⟩, j.x23⟩) ?_
  unfold seqs seqs
  refine RelCT.seq (two_post
    (Ψ := fun a t => ∃ s, ESP f g tsH tsG K i T Hs Gs a s ∧ s.mem (s.gpr .x2) ≠ 0 ∧
      AtEnc K s (ebS s) (elS s) (loS s) t ∧ t.syms = s.syms)
    (two_taint [.x10, .x20, .x23] (fun a u₁ u₂ ⟨⟨s₁, h₁, j₁, _⟩, _⟩ ⟨⟨s₂, h₂, j₂, _⟩, _⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.1.1.fb, h₂.1.1.fb], fun r hr => ?_⟩) (by taint_decide))
    fun a u ⟨⟨s, h, j, y⟩, hb⟩ => ?_) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [j₁.x10, j₂.x10, h₁.1.1.n0, h₂.1.1.n0]
    · exact (j₁.x20.trans h₁.1.1.scr).trans (j₂.x20.trans h₂.1.1.scr).symm
    · rw [j₁.x23, j₂.x23, h₁.1.1.gpr (by decide), h₂.1.1.gpr (by decide)]
  · have h0 : s.mem (s.gpr .x2) ≠ 0 := fun h0 => by
      rw [eval_zero, j.x10, h0] at hb
      exact absurd hb (by decide)
    exact WP.mono_syms (args_ok h.1.1.1 h0 j) fun t ht sy => ⟨s, h, h0, ht, sy.trans y⟩
  -- `encode`, for the index of the table.
  refine RelCT.seq (byIdx_ct (Q := Two fun a t => ∃ s, ESP f g tsH tsG K i T Hs Gs a s ∧ s.mem (s.gpr .x2) ≠ 0 ∧
      AfterEnc Hs Gs K s (ebS s) (elS s) (loS s) t) (fun _ => i) (fun a t t' ⟨s, h, z, j, y⟩ o sy => ⟨s, h, z, j.only9 o, sy.trans y⟩)
    (fun a t ⟨s, h, z, j, y⟩ => ⟨h.1.2.1.mem, j.x27.trans h.1.2.1.idx, rfl⟩)
    (fun j hj => by unfold idxs at hj; simp at hj; omega_using [hj]) (fun j hj => ?_) (fun j hj => ?_)) ?_
  · unfold idxs at hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact two_taint [.x27] (fun a t₁ t₂ ⟨s₁, h₁, _, j₁, _⟩ ⟨s₂, h₂, _, j₂, _⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.1.1.fb, h₂.1.1.fb], fun r hr => by
        rw [List.mem_singleton.mp hr, j₁.x27, j₂.x27, h₁.1.2.1.idx, h₂.1.2.1.idx]⟩) (by taint_decide)
  · by_cases hij : i = j
    · subst hij
      refine two_post ((enc_ct h624 hv hct).mono (fun _ _ => two_mono fun _ _ ⟨⟨s, h, z, j, y⟩, _⟩ =>
        ⟨s, h.1, z, j, y⟩) fun _ _ _ => trivial) fun a t ⟨⟨s, h, z, j, y⟩, _⟩ => ?_
      obtain ⟨b₁, b₂, l, -⟩ := eb_bounds h.1.1.1 z
      exact WP.mono (encCall_ok h.1.1.1 h624 h.1.2.1 j y (by omega_using [l]) rfl b₁ b₂) fun t' h' => ⟨s, h, z, h'⟩
    · exact RelCT.of_false fun _ _ ⟨a, h₁, _⟩ => hij h₁.2
  -- `encode`'s result.
  refine two_ite (fun a t₁ t₂ ⟨s₁, h₁, _, j₁⟩ ⟨s₂, h₂, _, j₂⟩ => by
      rw [eval_zero_w, eval_zero_w, j₁.x0 (h₁.1.2.1.hl.trans h₁.1.2.1.hD), j₂.x0 (h₂.1.2.1.hl.trans h₂.1.2.1.hD),
        h₁.1.1.eb, h₂.1.1.eb, h₁.1.1.2.args 11 (by decide), h₂.1.1.2.args 11 (by decide)])
    (failP_ct fun a u ⟨⟨s, h, _, j⟩, _⟩ => ⟨s, h.1.1, ⟨j.sp, j.rd, j.wr, j.v, j.fr⟩, j.x23⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s em, EP tsH tsG K a s ∧ AtCallP K s em t)
    (two_taint [] (fun a t₁ t₂ ⟨⟨s₁, h₁, _, j₁⟩, _⟩ ⟨⟨s₂, h₂, _, j₂⟩, _⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.1.1.fb, h₂.1.1.fb], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
    fun a t ⟨⟨s, h, z, j⟩, hb⟩ => ?_) ?_
  · obtain ⟨_, _, hm⟩ := main_of h.1.1.1 z j hb
    exact WP.mono (privArgsP_ok h.1.1.1 h.2.1 hm) fun t' h' => ⟨s, _, ⟨h.1.1, h.2⟩, h'⟩
  exact two_post (callP_ct c hcK) fun a t ⟨s, em, h, hA⟩ =>
    WP.mono (callP_ok c h.1.1 h.2.1 hcK hA) fun t' h' => by rw [h'.sp, h.1.fb]


end

end VG.Proof.RsaPss.AArch64.Sgn

end

end

/-! ### `RsaPss.AArch64.SignCVerified`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS signing on AArch64, calling `encode`: correctness and constant time

`signMdTableContract` with the tables of `vs` (and the stack of the frame and
of the deeper callee, `stk K`), from correctness (`code_ok`, with the
selection `ESel` the tables a state holds give, `esel_of`) and constant time
(`code_ct`, for the index, the functions and the hash functions of the
first run's tables, which every run with the same public data holds:
`pubS_of`): `sign_correct`, `sign_constantTime`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPkcs1Sig.AArch64 (PrivChecked Two)
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.MdHashTable.AArch64 (idx)
open VG.Proof.RsaPss.AArch64 (OK tabsOf esel_of enc_of encCT_of names_sub Tabs)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-- The contract, with the tables of `vs`. -/
abbrev signCK (vs : List MdHash) (K : Nat) : Contract isa :=
  Spec.RsaPss.signMdTableContract (signAbi (MdHashTable.AArch64.tables vs) (HashTable.AArch64.tables vs)) (stk K)

theorem leak_eq {a b a' b' : List Byte} (ha : a.length = a'.length)
    (h : (a ++ b).map (·.toNat) = (a' ++ b').map (·.toNat)) : a = a' ∧ b = b' :=
  List.append_inj ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h) ha

/-- The public data of the contract, by name: the anchor `s₁`'s. -/
theorem pubS_of {tsH tsG : List FnTable} {K : Nat} {s₁ s₂ : State}
    (h : (Spec.RsaPss.signMdTableContract (signAbi tsH tsG) (stk K)).pub s₁ s₂) :
    PubS s₁ s₂ ∧ (∀ f ∈ (tsH.map (·.fns)).flatten ++ (tsG.map (·.fns)).flatten, s₁.syms f = s₂.syms f) ∧
      (∀ T ∈ tsH, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 14) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 14) (FnTable.words isa s₂ T))) ∧
      ∀ T ∈ tsG, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 15) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 15) (FnTable.words isa s₂ T)) := by
  sig_pub [Spec.RsaPss.signMdTableContract, Spec.RsaPss.signMdTableSig, Spec.MdHashTable.param, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs,
    List.append_eq, _root_.List.range, _root_.List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at h
  obtain ⟨hsp, hsy, htH, htG, hl, g0, g1, g2, g3, g4, g5, g6, g7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15⟩ := h
  obtain ⟨hn, he⟩ := leak_eq (by rw [bytesAt_length, bytesAt_length, g3]) hl
  refine ⟨⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, hn.symm, he.symm⟩, hsy, fun T hT => htH _ _ rfl rfl T hT,
    fun T hT => htG _ _ rfl rfl T hT⟩
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [g0.symm, g1.symm, g2.symm, g3.symm, g4.symm, g5.symm, g6.symm, g7.symm]
  · match i, hi with
    | 0, _ => exact a0.symm | 1, _ => exact a1.symm | 2, _ => exact a2.symm | 3, _ => exact a3.symm
    | 4, _ => exact a4.symm | 5, _ => exact a5.symm | 6, _ => exact a6.symm | 7, _ => exact a7.symm
    | 8, _ => exact a8.symm | 9, _ => exact a9.symm | 10, _ => exact a10.symm | 11, _ => exact a11.symm
    | 12, _ => exact a12.symm | 13, _ => exact a13.symm | 14, _ => exact a14.symm | 15, _ => exact a15.symm
    | n + 16, h => exact absurd h (by omega_using [])

variable {vs : List MdHash} (hok : OK vs) (c : PrivChecked) {K : Nat} (h624 : 624 ≤ K) (hcK : c.stack ≤ K)

/-- The tables of a state meeting the precondition: those of variants `w`
and `w'` of `vs`. -/
theorem tabs_of {s : State} (hp : PreS (MdHashTable.AArch64.tables vs) (HashTable.AArch64.tables vs) K s) :
    ∃ w ∈ vs, ∃ w' ∈ vs,
      Abi.tableHeld 64 s.mem (stackArg s 14) (FnTable.words isa s (MdHashTable.AArch64.tableOf w)) ∧
      Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s (HashTable.AArch64.tableOf w')) := by
  obtain ⟨_, hT, hH⟩ := hp.tabH
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨_, hT', hG⟩ := hp.tabG
  obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hT'
  exact ⟨w, hw, w', hw', hH, hG⟩

include hok h624 hcK in
theorem sign_correct (s : State) (h : (signCK vs K).pre s) :
    ∃ t s', Exec isa (signC (MdHashTable.AArch64.fnsOf vs) (HashTable.AArch64.fnsOf vs) c.name c.code) s t s' ∧
      abiPreserved s s' ∧ (signCK vs K).post s s' := by
  have hp := preS_of h
  obtain ⟨w, hw, w', hw', hH, hG⟩ := tabs_of hp
  have E := esel_of hok hw hw' hp.hsy hp.hdl hH hG
  obtain ⟨t, s', he, habi, hr⟩ := code_ok c h624 hcK hp E
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Spec.RsaPss.signMdTableContract, Spec.RsaPss.signMdTableSig, Spec.MdHashTable.param, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs,
    List.append_eq, _root_.List.range, _root_.List.range.loop]
  intro H G hH' hG'
  cases hH'.symm.trans E.hH
  cases hG'.symm.trans E.hG
  rw [E.hl, E.hD]
  exact hr

/-- The index, the functions and the hash functions `x` whose `encode` is
correct and constant time. -/
def EncGood (x : Nat × Tabs × Spec.Mgf1.Hash × Spec.Mgf1.Hash) : Prop :=
  (∀ s', (Enc.encK x.2.1 x.2.2.1 x.2.2.2).pre s' → ∃ t s'',
    Exec isa (encode (MdHashTable.AArch64.fnsOf vs) (ofIdx x.1) (HashTable.AArch64.fnsOf vs)) s' t s'' ∧
      abiPreserved s' s'' ∧ (Enc.encK x.2.1 x.2.2.1 x.2.2.2).post s' s'') ∧
    ConstantTime isa (Enc.encK x.2.1 x.2.2.1 x.2.2.2).pre (Enc.encK x.2.1 x.2.2.1 x.2.2.2).pub
      (encode (MdHashTable.AArch64.fnsOf vs) (ofIdx x.1) (HashTable.AArch64.fnsOf vs))

include hok h624 hcK in
theorem sign_constantTime :
    ConstantTime isa (signCK vs K).pre (signCK vs K).pub
      (signC (MdHashTable.AArch64.fnsOf vs) (HashTable.AArch64.fnsOf vs) c.name c.code) := by
  refine RelCT.constantTime ((RelCT.exists_ (Q := fun _ _ => True) (P := fun (x : Nat × Tabs × Spec.Mgf1.Hash × Spec.Mgf1.Hash) s₁ s₂ =>
      EncGood (vs := vs) x ∧ Two (ES (MdHashTable.AArch64.fnsOf vs) (HashTable.AArch64.fnsOf vs)
        (MdHashTable.AArch64.tables vs) (HashTable.AArch64.tables vs) K x.1 x.2.1 x.2.2.1 x.2.2.2) s₁ s₂)
      fun x => ?_).mono (fun s₁ s₂ ⟨h₁, h₂, hpub⟩ => ?_) fun _ _ h => h)
  · by_cases hx : EncGood (vs := vs) x
    · exact (code_ct c h624 hcK hx.1 hx.2).mono (fun _ _ h => h.2) fun _ _ h => h
    · exact RelCT.of_false fun _ _ h => hx h.1
  have p₁ := preS_of h₁
  have p₂ := preS_of h₂
  obtain ⟨w, hw, w', hw', hH, hG⟩ := tabs_of p₁
  obtain ⟨pS, hsy, htH, htG⟩ := pubS_of hpub
  have hH₂ := (htH _ (List.mem_map_of_mem hw)).mp hH
  have hG₂ := (htG _ (List.mem_map_of_mem hw')).mp hG
  refine ⟨(idx w, tabsOf vs w w', w.mgf.G, w'.mgf.G), ⟨enc_of hok hw, encCT_of hok hw⟩, s₁,
    ⟨⟨p₁, PubS.refl s₁⟩, esel_of hok hw hw' p₁.hsy p₁.hdl hH hG, fun _ _ => rfl⟩,
    ⟨⟨p₂, pS⟩, esel_of hok hw hw' p₂.hsy p₂.hdl hH₂ hG₂, fun n hn => (hsy n (names_sub hw hw' n hn)).symm⟩⟩

end VG.Proof.RsaPss.AArch64.Sgn

end

end

/-!
# RSASSA-PSS signing on AArch64 with the key's precomputed values: correctness and constant time

`signPrecomputedMdTableContract` with the tables of `vs`, for `signCP`: its
precondition gives `PreS` and `pre`'s facts `PreXS` (`preSP_of`), its public
data `PubS` and `PubX` (`pubSP_of`); then `codeP_ok` and `codeP_ct`:
`signP_correct`, `signP_constantTime`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPkcs1Sig.AArch64 (PrivPChecked Two)
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.MdHashTable.AArch64 (idx)
open VG.Proof.RsaPss.AArch64 (OK tabsOf esel_of enc_of encCT_of names_sub Tabs)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-- The ABI the contract states, with the tables. -/
abbrev signPAbi (tsH tsG : List FnTable) : Abi isa :=
  abi.withTables Spec.RsaPss.signPrecomputedMdTableSig [("hash", tsH), ("mgf1", tsG)]

/-- The contract, with the tables of `vs`. -/
abbrev signPCK (vs : List MdHash) (K : Nat) : Contract isa :=
  Spec.RsaPss.signPrecomputedMdTableContract
    (signPAbi (MdHashTable.AArch64.tables vs) (HashTable.AArch64.tables vs)) (stk K)

theorem preSP_of {tsH tsG : List FnTable} {K : Nat} {s : State}
    (h : (Spec.RsaPss.signPrecomputedMdTableContract (signPAbi tsH tsG) (stk K)).pre s) :
    PreS tsH tsG K s ∧ PreXS K s := by
  have e : stk K = (frameBytes + K - 1) + 1 := by unfold stk frameBytes; omega_using []
  rw [e] at h
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argRegs, List.append_eq, _root_.List.range, _root_.List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero,
    Option.some.injEq, exists_eq_left'] at h
  sig_split h
  rename_i sp1 sp2 tabH tabG hsy hrd hwr on oe op oq odp odq oqi odg osl os opr otH otG oa ns es ps qs dps dqs qis
    dgs sls spr stH stG sa ko kn ke kp kq kdp kdq kqi kdg ksl ks kpr ktH ktG ka wo wn we wp wq wdp wdq wqi wdg wsl
    ws wpr wtH wtG _ob1 ol e1 e2 p1 p2 q1 q2 hdp hqi hdq hs prl key
  obtain ⟨k1, k2⟩ := _ob1
  rw [← e] at sp1 ko kn ke kp kq kdp kdq kqi kdg ksl ks kpr ktH ktG ka
  have a128 : Region.Sub (aR s) (aR2 s) := Region.sub_prefix (by decide)
  refine ⟨⟨sp1, by omega_using [sp2], tabH, tabG, hsy, ?_, by rw [hwr]; simp, by rw [hwr]; simp, on, oe,
    op, oq, odp, odq, oqi, odg, osl, os, otH, otG, oa.sub_right a128, ns, es, ps, qs, dps, dqs, qis, dgs, sls, stH,
    stG, sa.sub_right a128, ko, kn, ke, kp, kq, kdp, kdq, kqi, kdg, ksl, ks, ktH, ktG, ka.sub_right a128, wo, wn, we,
    wp, wq, wdp, wdq, wqi, wdg, wsl, ws, wtH, wtG, k1, k2, ol, e1, e2, p1, p2, q1, q2, hdp, hqi, hdq,
    by unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hs; omega_using [hs], h⟩,
    ⟨Covers.of_mem fun r hr => by
      rw [hrd]; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp [prR, aR2],
      sp2, oa, sa, ka, opr, spr, kpr, wpr, prl, key⟩⟩
  rw [hrd]
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨nR s, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨eR s, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨pR s, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨qR s, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨dpR s, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨dqR s, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨qiR s, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨dgR s, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨slR s, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨tHR s, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨tGR s, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨aR2 s, by simp, 0, (BitVec.add_zero _).symm, by simp⟩

/-- The public data of the contract, by name: the anchor `s₁`'s. -/
theorem pubSP_of {tsH tsG : List FnTable} {K : Nat} {s₁ s₂ : State}
    (h : (Spec.RsaPss.signPrecomputedMdTableContract (signPAbi tsH tsG) (stk K)).pub s₁ s₂) :
    PubS s₁ s₂ ∧ PubX s₁ s₂ ∧ (∀ f ∈ (tsH.map (·.fns)).flatten ++ (tsG.map (·.fns)).flatten, s₁.syms f = s₂.syms f) ∧
      (∀ T ∈ tsH, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 14) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 14) (FnTable.words isa s₂ T))) ∧
      ∀ T ∈ tsG, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 15) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 15) (FnTable.words isa s₂ T)) := by
  sig_pub [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.wordCount,
    Spec.MdHashTable.fns, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, List.append_eq, _root_.List.range, _root_.List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at h
  obtain ⟨hsp, hsy, htH, htG, hl, g0, g1, g2, g3, g4, g5, g6, g7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15, a16, a17⟩ := h
  obtain ⟨hl₁, hl₂⟩ := List.append_inj hl (by simp [bytesAt_length, g3, g5])
  obtain ⟨hn, he⟩ := leak_eq (by rw [bytesAt_length, bytesAt_length, g3]) hl₁
  have hw := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl₂
  refine ⟨⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, hn.symm, he.symm⟩, ⟨a16.symm, a17.symm, ?_⟩, hsy,
    fun T hT => htH _ _ rfl rfl T hT, fun T hT => htG _ _ rfl rfl T hT⟩
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [g0.symm, g1.symm, g2.symm, g3.symm, g4.symm, g5.symm, g6.symm, g7.symm]
  · match i, hi with
    | 0, _ => exact a0.symm | 1, _ => exact a1.symm | 2, _ => exact a2.symm | 3, _ => exact a3.symm
    | 4, _ => exact a4.symm | 5, _ => exact a5.symm | 6, _ => exact a6.symm | 7, _ => exact a7.symm
    | 8, _ => exact a8.symm | 9, _ => exact a9.symm | 10, _ => exact a10.symm | 11, _ => exact a11.symm
    | 12, _ => exact a12.symm | 13, _ => exact a13.symm | 14, _ => exact a14.symm | 15, _ => exact a15.symm
    | n + 16, h => exact absurd h (by omega_using [])
  · exact hw.symm

theorem PubX.refl (s : State) : PubX s s := ⟨rfl, rfl, rfl⟩

variable {vs : List MdHash} (hok : OK vs) (c : PrivPChecked) {K : Nat} (h624 : 624 ≤ K) (hcK : c.stack ≤ K)

include hok h624 hcK in
theorem signP_correct (s : State) (h : (signPCK vs K).pre s) :
    ∃ t s', Exec isa (signCP (MdHashTable.AArch64.fnsOf vs) (HashTable.AArch64.fnsOf vs) c.name c.code) s t s' ∧
      abiPreserved s s' ∧ (signPCK vs K).post s s' := by
  obtain ⟨hp, hx⟩ := preSP_of h
  obtain ⟨w, hw, w', hw', hH, hG⟩ := tabs_of hp
  have E := esel_of hok hw hw' hp.hsy hp.hdl hH hG
  obtain ⟨t, s', he, habi, hr⟩ := codeP_ok c h624 hcK hp hx E
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.wordCount,
    Spec.MdHashTable.fns, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, List.append_eq, _root_.List.range, _root_.List.range.loop]
  intro H G hH' hG'
  cases hH'.symm.trans E.hH
  cases hG'.symm.trans E.hG
  rw [E.hl, E.hD]
  exact hr

include hok h624 hcK in
theorem signP_constantTime :
    ConstantTime isa (signPCK vs K).pre (signPCK vs K).pub
      (signCP (MdHashTable.AArch64.fnsOf vs) (HashTable.AArch64.fnsOf vs) c.name c.code) := by
  refine RelCT.constantTime ((RelCT.exists_ (Q := fun _ _ => True) (P := fun (x : Nat × Tabs × Spec.Mgf1.Hash × Spec.Mgf1.Hash) s₁ s₂ =>
      EncGood (vs := vs) x ∧ Two (ESP (MdHashTable.AArch64.fnsOf vs) (HashTable.AArch64.fnsOf vs)
        (MdHashTable.AArch64.tables vs) (HashTable.AArch64.tables vs) K x.1 x.2.1 x.2.2.1 x.2.2.2) s₁ s₂)
      fun x => ?_).mono (fun s₁ s₂ ⟨h₁, h₂, hpub⟩ => ?_) fun _ _ h => h)
  · by_cases hx : EncGood (vs := vs) x
    · exact (codeP_ct c h624 hcK hx.1 hx.2).mono (fun _ _ h => h.2) fun _ _ h => h
    · exact RelCT.of_false fun _ _ h => hx h.1
  obtain ⟨p₁, x₁⟩ := preSP_of h₁
  obtain ⟨p₂, x₂⟩ := preSP_of h₂
  obtain ⟨w, hw, w', hw', hH, hG⟩ := tabs_of p₁
  obtain ⟨pS, pX, hsy, htH, htG⟩ := pubSP_of hpub
  have hH₂ := (htH _ (List.mem_map_of_mem hw)).mp hH
  have hG₂ := (htG _ (List.mem_map_of_mem hw')).mp hG
  refine ⟨(idx w, tabsOf vs w w', w.mgf.G, w'.mgf.G), ⟨enc_of hok hw, encCT_of hok hw⟩, s₁,
    ⟨⟨⟨p₁, PubS.refl s₁⟩, esel_of hok hw hw' p₁.hsy p₁.hdl hH hG, fun _ _ => rfl⟩, x₁, PubX.refl s₁⟩,
    ⟨⟨⟨p₂, pS⟩, esel_of hok hw hw' p₂.hsy p₂.hdl hH₂ hG₂, fun n hn => (hsy n (names_sub hw hw' n hn)).symm⟩, x₂, pX⟩⟩

end VG.Proof.RsaPss.AArch64.Sgn
