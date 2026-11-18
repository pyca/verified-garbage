module

public import VerifiedGarbage.Proof.RsaPss.AArch64.SignSpec
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignCEnc
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame
import VerifiedGarbage.Proof.RsaPss.AArch64.Restore
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.MlKem.AArch64.Wp
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
meta import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Calls
import VerifiedGarbage.Proof.RsaPss.AArch64.SignChecks
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash

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
