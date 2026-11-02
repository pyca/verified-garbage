module

public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Main
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.X86.Cand.Spec
public import VerifiedGarbage.Proof.Ffdh.Contract

/-!
# The FFDH candidate on i686: its body

`bits`, the generator and `used` into the header, then a shortage if the
tape has fewer than `L` octets, else `main` (`body_ok`): the status, `out`
and `used` of `sievedParameterCandidate`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86 VG.Proof.Ffdh.X86.KeyGen
open VG.Impl.Ffdh.X86.Candidate
open VG.Impl.Bignum.X86.PublicRt (argAt)

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- A word read through `esp`, apart from the working space and the 96 bytes below `esp`, after a
stage. -/
theorem readArg_step {m : MemOp} (hm : m.base = .esp) {v : BitVec 32} (hr : readSrc s (.mem m) = some v)
    {t : State} (S : Step Ex base bytes len args s t) (dws : Region.Disjoint ⟨s.ea m, 4⟩ ⟨base, bytes⟩)
    (d40 : Region.Disjoint ⟨s.ea m, 4⟩ (below (s.gpr .esp) 96)) : readSrc t (.mem m) = some v := by
  have h := S.inp
  have fit := fR_fit h
  have bl := h.bytes_lt
  have e : t.ea m = s.ea m := by simp only [State.ea, hm, S.esp]
  simp only [readSrc, State.load32] at hr ⊢
  rw [e, S.keeps.2.1, S.keeps.2.2]
  split at hr
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ‹_›)]
    rw [← hr]
    refine congrArg some (S.frame.readW (r := ⟨s.ea m, 4⟩) (Region.contains_self _ _) (fun r hr' => ?_) (by decide))
    rw [frameR, List.mem_cons, List.mem_map] at hr'
    rcases hr' with rfl | ⟨q, hq, rfl⟩
    · exact d40
    · have := fit q hq
      exact dws.sub_right (Offset.sub_base _ (by omega))
  · cases hr

/-- `bits`, the generator and `used` into the header, and the tape's length compared with `L`. -/
theorem bodyHead_ok (h : In Ex base bytes len args s) {n : Nat} (Gl : args 12 = BitVec.ofNat 32 n)
    (small : n < 2 ^ 32) (h3 : args 3 = BitVec.ofNat 32 len) {up : BitVec 32} {bits g : Nat}
    (rb : readSrc s (.mem (argAt 19 3)) = some (BitVec.ofNat 32 bits))
    (rg : readSrc s (.mem (argAt 19 4)) = some (BitVec.ofNat 32 g))
    (ru : readSrc s (.mem (argAt 19 2)) = some up)
    (dws : ∀ j ∈ [2, 3, 4], Region.Disjoint ⟨s.ea (argAt 19 j), 4⟩ ⟨base, bytes⟩)
    (d40 : ∀ j ∈ [2, 3, 4], Region.Disjoint ⟨s.ea (argAt 19 j), 4⟩ (below (s.gpr .esp) 96))
    (hb2 : bits ≤ 8192) (hg25 : g = 2 ∨ g = 5) :
    WP isa (.block (entryWords ++ ([.mov .eax (.mem (argAt 0 12)), .alu .cmp .eax (.mem (argAt 0 3))] : List Instr))) s fun t =>
      Step Ex base bytes len args s t ∧ w32 t.mem base bitsOff = bits ∧ w32 t.mem base genOff = g ∧
      w32 t.mem base usedOff = up.toNat ∧ Kept base len [] [bitsOff, genOff, usedOff] s.mem t.mem ∧
      t.cf = some (decide (n < len)) := by
  have hu := h.upper
  have ul : up.toNat < 2 ^ 32 := up.isLt
  have ra : ∀ {t : State} {j : Nat} {v : BitVec 32}, j ∈ [2, 3, 4] → readSrc s (.mem (argAt 19 j)) = some v →
      Step Ex base bytes len args s t → readSrc t (.mem (argAt 19 j)) = some v :=
    fun hj hr S => readArg_step rfl hr S (dws _ hj) (d40 _ hj)
  unfold entryWords
  simp only [List.cons_append, List.nil_append]
  refine wp_movS rb fun t₁ U₁ _ => ?_
  have S₁ : Step Ex base bytes len args s t₁ := Step.regs h U₁.mem U₁.keeps
  refine hdr_store S₁.inp hdr_bits fun t₂ S₂ W₂ k₂ _ _ _ _ => ?_
  have S₂' := S₁.trans S₂
  refine wp_movS (ra (by simp) rg S₂') fun t₃ U₃ _ => ?_
  have S₃ : Step Ex base bytes len args s t₃ := S₂'.trans (Step.regs S₂.inp U₃.mem U₃.keeps)
  refine hdr_store S₃.inp hdr_gen fun t₄ S₄ W₄ k₄ _ _ _ _ => ?_
  have S₄' := S₃.trans S₄
  refine wp_movS (ra (by simp) ru S₄') fun t₅ U₅ _ => ?_
  have S₅ : Step Ex base bytes len args s t₅ := S₄'.trans (Step.regs S₄.inp U₅.mem U₅.keeps)
  refine hdr_store S₅.inp hdr_used fun t₆ S₆ W₆ k₆ _ _ _ _ => ?_
  have S₆' := S₅.trans S₆
  refine wp_movS (S₆'.inp.arg (i := 12) (by decide)) fun t₇ U₇ _ => ?_
  have h₇ := S₆'.inp.regs U₇.keeps U₇.mem
  refine wp_cmpC (h₇.arg (i := 3) (by decide)) fun t₈ F₈ c₈ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact S₆'.trans (Step.regs S₆.inp (by rw [F₈.mem, U₇.mem]) (U₇.keeps.trans (F₈.keeps _)))
  · rw [F₈.mem, U₇.mem, k₆.word_eq, U₅.mem, k₄.word_eq, U₃.mem, W₂, U₁.gpr, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  · rw [F₈.mem, U₇.mem, k₆.word_eq, U₅.mem, W₄, U₃.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [F₈.mem, U₇.mem, W₆, U₅.gpr]
  · exact (by rw [U₁.mem]; exact (Kept.refl _).mono : Kept base len [] [bitsOff, genOff, usedOff] s.mem t₁.mem).trans
      (k₂.mono.trans ((by rw [U₃.mem]; exact (Kept.refl _).mono :
        Kept base len [] [bitsOff, genOff, usedOff] t₂.mem t₃.mem).trans (k₄.mono.trans
          ((by rw [U₅.mem]; exact (Kept.refl _).mono : Kept base len [] [bitsOff, genOff, usedOff] t₄.mem t₅.mem).trans
            (k₆.mono.trans (by rw [F₈.mem, U₇.mem]; exact (Kept.refl _).mono))))))
  · rw [c₈, U₇.gpr, Gl, h3, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
      Nat.mod_eq_of_lt (by omega)]

/-- The body, from the frame's state `s`, with the function's `bits`, generator and `used` read
above the frame. -/
theorem body_ok (h : In Ex base bytes len args s) {T : List Byte}
    (G : TapeGeo Ex args base bytes (s.gpr .esp) T.length)
    (hT : Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) T.length = T)
    (Ox : OutAt args base bytes len 0 (s.gpr .esp) s.wr) {up : BitVec 32}
    (U : UsedAt base bytes up (s.gpr .esp) ⟨byteAddr (args 0), len⟩ s.wr)
    (h3 : args 3 = BitVec.ofNat 32 len) {bits g : Nat}
    (rb : readSrc s (.mem (argAt 19 3)) = some (BitVec.ofNat 32 bits))
    (rg : readSrc s (.mem (argAt 19 4)) = some (BitVec.ofNat 32 g))
    (ru : readSrc s (.mem (argAt 19 2)) = some up)
    (dws : ∀ j ∈ [2, 3, 4], Region.Disjoint ⟨s.ea (argAt 19 j), 4⟩ ⟨base, bytes⟩)
    (d40 : ∀ j ∈ [2, 3, 4], Region.Disjoint ⟨s.ea (argAt 19 j), 4⟩ (below (s.gpr .esp) 96))
    (hbl : len = (bits + 7) / 8) (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192) (hg25 : g = 2 ∨ g = 5)
    {Tb : BitVec 32} (TT : Table Tb (s.gpr .esp) s)
    (TA : Region.Disjoint ⟨Tb.setWidth 64, 8192⟩ ⟨base, bytes⟩) :
    WP isa Impl.Ffdh.X86.Candidate.body s (Fin base len args up s
      (Proof.Ffdh.candidateStatus (Spec.Ffdh.sievedParameterCandidate bits g T))
      (candUsed T (Spec.Ffdh.sievedParameterCandidate bits g T))
      (candOut len (Spec.Ffdh.sievedParameterCandidate bits g T))) := by
  unfold Impl.Ffdh.X86.Candidate.body
  refine WP.seq (WP.mono_syms (bodyHead_ok h G.len G.small h3 rb rg ru dws d40 hb2 hg25)
    fun u ⟨S, B, Gn, Us, k, c⟩ sy => ?_)
  have Ox' : OutAt args base bytes len 0 (u.gpr .esp) u.wr := by rw [S.esp]; exact Ox.keep rfl S.keeps
  have U' : UsedAt base bytes up (u.gpr .esp) ⟨byteAddr (args 0), len⟩ u.wr := by
    rw [S.esp]; exact U.keep rfl S.keeps
  refine WP.ite _ c (fun e => ?_) fun e => ?_
  · have sh : T.length < (bits + 7) / 8 := by simp at e; omega
    rw [sieved_short sh]
    exact WP.mono (short_ok S.inp Ox' U' Us) fun t R => R.after S
  · have hL : len ≤ T.length := by simp at e; omega
    exact WP.mono (main_ok S.inp (by rw [S.esp]; exact G) (by rw [tape_keep G S, hT]) Ox' U' Us h3 hL B hbl hb1 hb2
      Gn hg25 (TT.step S sy TA) TA) fun t R => R.after S

end VG.Proof.Ffdh.X86.Cand
