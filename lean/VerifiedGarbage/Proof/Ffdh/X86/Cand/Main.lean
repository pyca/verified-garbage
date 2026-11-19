module

import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Import
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Phase
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Sieve
public import VerifiedGarbage.Spec.Ffdh.SievedCandidate
public import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ScreenedStream
public import VerifiedGarbage.Proof.RsaKeyGen.TrialFilter
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Base
public import VerifiedGarbage.Proof.Ffdh.X86.KeyGen
import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion

/-! ### `Ffdh.X86.Cand.Tests`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86.Cand.Result`, which this module and modules that import it used -/

section

/-!
# The FFDH candidate on i686: its results

`storeUsed` writes the octets used, a 64-bit word, at `used` (whose address
the header keeps); a shortage (`short_ok`), a rejection (`reject_ok`) and an
acceptance (`accept_ok`) write `out`, `used` and the status (`Fin`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86 VG.Proof.Ffdh.X86.KeyCut VG.Proof.Ffdh.X86.KeyGen
open VG.Impl.Ffdh.X86.Candidate
open VG.Impl.Ffdh.X86 (exportTo)

/-- Where `used` lies: eight writable bytes apart from the working space, the frame, the 40 bytes
below it and `out`. -/
structure UsedAt (base : Addr) (bytes : Nat) (up sp : BitVec 32) (out : Region) (wr : List Region) : Prop where
  fit : up.toNat + 8 ≤ 2 ^ 32
  wr : InRegions wr (byteAddr up) 8
  apart : Region.Disjoint ⟨base, bytes⟩ ⟨byteAddr up, 8⟩
  frame : Region.Disjoint ⟨sp.setWidth 64, 76⟩ ⟨byteAddr up, 8⟩
  below : Region.Disjoint ⟨byteAddr up, 8⟩ (below sp 96)
  out : Region.Disjoint out ⟨byteAddr up, 8⟩

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

theorem UsedAt.keep {up sp : BitVec 32} {out : Region} {wr : List Region} (U : UsedAt base bytes up sp out wr)
    {t : State} {rs : List Reg} (e : s.wr = wr) (K : Keeps rs s t) : UsedAt base bytes up sp out t.wr := by
  rw [K.2.2, e]; exact U

theorem hdr_used : Hdr usedOff := ⟨.inl ⟨by decide, by decide⟩, by decide⟩

/-- `eax` (`k`) written at `used`, a 64-bit word. -/
theorem storeUsed_ok (h : In Ex base bytes len args s) {up : BitVec 32} {out : Region}
    (U : UsedAt base bytes up (s.gpr .esp) out s.wr) (hu : w32 s.mem base usedOff = up.toNat) {k : Nat}
    (hk : k < 2 ^ 32) (he : s.gpr .eax = BitVec.ofNat 32 k) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, t.mem.readW (byteAddr up) 64 = BitVec.ofNat 64 k → Frame [⟨byteAddr up, 8⟩] s.mem t.mem →
      Keeps [.eax, .ecx] s t → In Ex base bytes len args t → WP isa (.block is) t Q) :
    WP isa (.block (storeUsed ++ is)) s Q := by
  have fit := U.fit
  unfold storeUsed
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (hdr_read h hdr_used) fun t₁ U₁ _ => ?_
  have ec : t₁.gpr .ecx = up := by rw [U₁.gpr, hu, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have wIn : ∀ t : State, t.wr = s.wr → ∀ d, d + 4 ≤ 8 → InRegions t.wr (byteAddr up + BitVec.ofNat 64 d) 4 :=
    fun t ht d hd => by rw [ht]; exact VG.CallLay.inRegions_sub U.wr hd (by decide)
  refine wp_storeS (show t₁.ea (at_ .ecx 0) = byteAddr up + BitVec.ofNat 64 0 from by
      show byteAddr (t₁.gpr .ecx + BitVec.ofNat 32 0) = _; rw [ec]; exact byteAddr_add (by omega_using []))
    (wIn t₁ U₁.wr 0 (by decide)) fun t₂ M₂ => ?_
  refine wp_movi fun t₃ U₃ => ?_
  refine wp_storeS (show t₃.ea (at_ .ecx 4) = byteAddr up + BitVec.ofNat 64 4 from by
      show byteAddr (t₃.gpr .ecx + BitVec.ofNat 32 4) = _
      rw [U₃.other _ (by decide), M₂.gpr, ec]; exact byteAddr_add (by omega_using [fit]))
    (by rw [U₃.wr, M₂.wr]; exact wIn t₁ U₁.wr 4 (by decide)) fun t₄ M₄ => ?_
  have mem₄ : t₄.mem = (s.mem.writeW (byteAddr up + BitVec.ofNat 64 0) (BitVec.ofNat 32 k)).writeW
      (byteAddr up + BitVec.ofNat 64 4) (0 : BitVec 32) := by
    rw [M₄.mem, U₃.gpr, U₃.mem, M₂.mem, U₁.other _ (by decide), U₁.mem, he]
  have F : Frame [⟨byteAddr up, 8⟩] s.mem t₄.mem := by
    rw [mem₄]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by omega_using []))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by omega_using []))
  have K : Keeps [.eax, .ecx] s t₄ :=
    ((U₁.keeps.mono (by decide)).trans ((M₂.keeps [.eax, .ecx]).trans (U₃.keeps.mono (by decide)))).trans
      (M₄.keeps [.eax, .ecx])
  have sep : Mem.Sep (byteAddr up + BitVec.ofNat 64 0) 4 (byteAddr up + BitVec.ofNat 64 4) 4 :=
    Offset.sep _ (.inl (by decide)) (by decide) (by decide)
  have z0 : byteAddr up + BitVec.ofNat 64 0 = byteAddr up := by simp
  refine kk t₄ ?_ F K (in_keepOut h K (by decide) (by decide) F U.frame)
  have hi : t₄.mem.readW (byteAddr up + BitVec.ofNat 64 4) 32 = 0 := by rw [mem₄, Mem.readW_writeW_self32]
  have lo : t₄.mem.readW (byteAddr up + BitVec.ofNat 64 0) 32 = BitVec.ofNat 32 k := by
    rw [mem₄, Mem.readW_writeW_sep sep (by decide), Mem.readW_writeW_self32]
  rw [z0] at lo
  rw [Proof.Rc2.Word32.read64_pair, hi, lo]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  rw [Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by omega_using [hk])]

/-- A result: the status `r`, `out` and `used`, the changes within them and `fR`, and the
registers. -/
structure Fin (base : Addr) (len : Nat) (args : Nat → BitVec 32) (up : BitVec 32) (s : State) (r used : Nat)
    (out : List Byte) (t : State) : Prop where
  eax : t.gpr .eax = BitVec.ofNat 32 r
  bytes : Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len = out
  used : t.mem.readW (byteAddr up) 64 = BitVec.ofNat 64 used
  frame : Frame (⟨byteAddr (args 0), len⟩ :: ⟨byteAddr up, 8⟩ :: frameR base (s.gpr .esp) (fR len)) s.mem t.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t

/-- A result after a stage. -/
theorem Fin.after {u t : State} {up : BitVec 32} {r used : Nat} {out : List Byte}
    (S : Step Ex base bytes len args s u) (R : Fin base len args up u r used out t) :
    Fin base len args up s r used out t := by
  obtain ⟨E, B, Us, F, K⟩ := R
  rw [S.esp] at F
  refine ⟨E, B, Us, (S.frame.mono fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)).trans F,
    S.keeps.trans K⟩

/-- `out`, its octets written and its status `eax`, then `used` and the status: the end of a result. -/
theorem finish_ok (h : In Ex base bytes len args s) {up : BitVec 32}
    (U : UsedAt base bytes up (s.gpr .esp) ⟨byteAddr (args 0), len⟩ s.wr) (hu : w32 s.mem base usedOff = up.toNat)
    {k r : Nat} (hk : k < 2 ^ 32) (he : s.gpr .eax = BitVec.ofNat 32 k) :
    WP isa (.block (storeUsed ++ ([.mov .eax (.imm (BitVec.ofNat 32 r))] : List Instr))) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 r ∧
      Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len = Spec.Rsa.bytesAt s.mem (byteAddr (args 0)) len ∧
      t.mem.readW (byteAddr up) 64 = BitVec.ofNat 64 k ∧ Frame [⟨byteAddr up, 8⟩] s.mem t.mem ∧
      Keeps [.eax, .ecx] s t := by
  refine storeUsed_ok h U hu hk he fun t₁ W F K _ => wp_movi fun t U' => WP.block_nil ⟨U'.gpr, ?_, ?_, ?_, ?_⟩
  · rw [U'.mem]
    have := h.upper
    exact frame_bytes F (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact U.out) (by omega_using [this])
  · rw [U'.mem, W]
  · rw [U'.mem]; exact F
  · exact K.trans (U'.keeps.mono (by decide))

/-- Zeros to `out`, through the mask word. -/
theorem zeroOut_ok (h : In Ex base bytes len args s) (Ox : OutAt args base bytes len 0 (s.gpr .esp) s.wr) :
    WP isa zeroOut s fun t =>
      Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len = List.replicate len 0 ∧
      Frame (⟨byteAddr (args 0), len⟩ :: frameR base (s.gpr .esp) (fR len)) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧ In Ex base bytes len args t ∧
      Kept base len [19] [accOff] s.mem t.mem := by
  have ao : accOff = 8 := rfl
  have nb : numBase = 3336 := rfl
  unfold zeroOut
  refine WP.seq (show WP isa (.block ([.mov .ecx (.imm 0)] ++ [.store (sc accOff) .ecx])) s _ from
    WP.block_append (wp_movS rfl fun u a _ => WP.block_nil ?_))
  have hu : In Ex base bytes len args u := h.regs a.keeps a.mem
  refine WP.mono (storeMask_ok hu (d := accOff) (c := false) (by omega_using [ao, nb]) a.gpr) fun v ⟨I, O, W, _, K⟩ => ?_
  have S : Step Ex base bytes len args s v := (Step.regs h a.mem a.keeps).trans (Step.word hu (by omega_using [ao]) O K)
  have kv : Kept base len [] [accOff] s.mem v.mem := by
    rw [← a.mem]; exact kept_word hu (by omega_using [ao, nb]) (by decide) O
  refine WP.mono (export_ok I (p := 0) (l := 1) (c := false) (by decide) (by decide) I.outLen
    (by rw [S.esp]; exact Ox.keep rfl S.keeps) (BitVec.eq_of_toNat_eq W) rfl (fun e => nomatch e))
    fun t ⟨B, _, F, Kt, It, kt⟩ => ⟨?_, ?_, S.keeps.trans Kt, It, kv.mono.trans kt.mono⟩
  · rw [B]; exact VG.Proof.Bignum.i2osp_zero' _
  · rw [S.esp] at F
    exact (S.frame.mono fun r hr => List.mem_cons_of_mem _ hr).trans F

/-- A shortage: zeros, nothing used, 0. -/
theorem short_ok (h : In Ex base bytes len args s) (Ox : OutAt args base bytes len 0 (s.gpr .esp) s.wr)
    {up : BitVec 32} (U : UsedAt base bytes up (s.gpr .esp) ⟨byteAddr (args 0), len⟩ s.wr)
    (hu : w32 s.mem base usedOff = up.toNat) :
    WP isa short s (Fin base len args up s 0 0 (List.replicate len 0)) := by
  have nb : numBase = 3336 := rfl
  unfold short
  refine WP.seq (WP.mono (zeroOut_ok h Ox) fun u ⟨B, F, K, I, k⟩ => ?_)
  have sp : u.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  have hu' : w32 u.mem base usedOff = up.toNat := by rw [k.word_eq, hu]
  simp only [List.cons_append]
  refine wp_movi fun u₁ U₁ => ?_
  have I₁ := I.regs U₁.keeps U₁.mem
  refine WP.mono (finish_ok I₁ (up := up) (by rw [U₁.keeps.1 _ (by decide), sp]; exact U.keep rfl (K.trans (U₁.keeps.mono (by decide))))
    (by rw [U₁.mem]; exact hu') (k := 0) (r := 0) (by decide) U₁.gpr) fun t ⟨E, Bt, W, Ft, Kt⟩ => ?_
  refine ⟨E, by rw [Bt, U₁.mem, B], W, ?_, (K.trans (U₁.keeps.mono (by decide))).trans (Kt.mono (by decide))⟩
  rw [U₁.mem] at Ft
  exact (F.mono fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)).trans
    (Ft.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- The cursor `c` as the octets used, and the status `r`. -/
theorem curTail_ok (h : In Ex base bytes len args s) {up : BitVec 32}
    (U : UsedAt base bytes up (s.gpr .esp) ⟨byteAddr (args 0), len⟩ s.wr) (hu : w32 s.mem base usedOff = up.toNat)
    {c r : Nat} (hc : w32 s.mem base curOff = c) :
    WP isa (.block (([.mov .eax (.mem (sc curOff))] : List Instr) ++ storeUsed ++
      ([.mov .eax (.imm (BitVec.ofNat 32 r))] : List Instr))) s
      fun t => t.gpr .eax = BitVec.ofNat 32 r ∧
        Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len = Spec.Rsa.bytesAt s.mem (byteAddr (args 0)) len ∧
        t.mem.readW (byteAddr up) 64 = BitVec.ofNat 64 c ∧ Frame [⟨byteAddr up, 8⟩] s.mem t.mem ∧
        Keeps [.eax, .ecx] s t := by
  have cl : c < 2 ^ 32 := by rw [← hc]; exact BitVec.isLt _
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (hdr_read h hdr_cur) fun u₁ U₁ _ => ?_
  have I₁ := h.regs U₁.keeps U₁.mem
  refine WP.mono (finish_ok I₁ (up := up) (by rw [U₁.keeps.1 _ (by decide)]; exact U.keep rfl U₁.keeps)
    (by rw [U₁.mem]; exact hu) (k := c) (r := r) cl (by rw [U₁.gpr, hc])) fun t ⟨E, B, W, F, K⟩ =>
    ⟨E, by rw [B, U₁.mem], W, by rw [U₁.mem] at F; exact F, (U₁.keeps.mono (by decide)).trans K⟩

/-- A rejection: zeros, the cursor `c` used, 2. -/
theorem reject_ok (h : In Ex base bytes len args s) (Ox : OutAt args base bytes len 0 (s.gpr .esp) s.wr)
    {up : BitVec 32} (U : UsedAt base bytes up (s.gpr .esp) ⟨byteAddr (args 0), len⟩ s.wr)
    (hu : w32 s.mem base usedOff = up.toNat) {c : Nat} (hc : w32 s.mem base curOff = c) :
    WP isa reject s (Fin base len args up s 2 c (List.replicate len 0)) := by
  unfold reject
  refine WP.seq (WP.mono (zeroOut_ok h Ox) fun u ⟨B, F, K, I, k⟩ => ?_)
  have sp : u.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  refine WP.mono (curTail_ok I (up := up) (r := 2) (by rw [sp]; exact U.keep rfl K) (by rw [k.word_eq, hu])
    (by rw [k.word_eq, hc])) fun t ⟨E, Bt, W, Ft, Kt⟩ => ⟨E, by rw [Bt, B], W, ?_, K.trans (Kt.mono (by decide))⟩
  exact (F.mono fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)).trans
    (Ft.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- p written to `out`. -/
theorem acceptOut_ok (h : In Ex base bytes len args s) (Ox : OutAt args base bytes len 0 (s.gpr .esp) s.wr)
    {p : Nat} (hp : sv s.mem base len .wide 9 = p) (hpl : p < 2 ^ (8 * len)) :
    WP isa acceptOut s fun u => Spec.Rsa.bytesAt u.mem (byteAddr (args 0)) len = Spec.Rsa.i2osp p len ∧
      Frame (⟨byteAddr (args 0), len⟩ :: frameR base (s.gpr .esp) (fR len)) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u ∧ In Ex base bytes len args u ∧
      Kept base len [19] [accOff] s.mem u.mem := by
  have ao : accOff = 8 := rfl
  have nb : numBase = 3336 := rfl
  unfold acceptOut
  refine WP.seq (WP.mono (copy19_ok h (a := 9) (by decide)) fun u₁ ⟨S₁, V₁, k₁⟩ => ?_)
  have h₁ := S₁.inp
  refine WP.seq (show WP isa (.block ([.mov .ecx (.imm (BitVec.allOnes 32))] ++ [.store (sc accOff) .ecx])) u₁ _ from
    WP.block_append (wp_movS rfl fun u a _ => WP.block_nil ?_))
  have hu' : In Ex base bytes len args u := h₁.regs a.keeps a.mem
  refine WP.mono (storeMask_ok hu' (d := accOff) (c := true) (by omega_using [ao, nb]) a.gpr) fun v ⟨I, O, W, _, K⟩ => ?_
  have S : Step Ex base bytes len args s v := S₁.trans ((Step.regs h₁ a.mem a.keeps).trans (Step.word hu' (by omega_using [ao]) O K))
  have kv : Kept base len [19] [accOff] s.mem v.mem :=
    k₁.mono.trans (by rw [← a.mem]; exact (kept_word hu' (by omega_using [ao, nb]) (by decide) O).mono)
  have V : val32 v.mem base (lo len (.slot .wide 19)) (cwc len .wide) = p := by
    have := lo_wide len 19
    have f := slot_fit1 h (j := 19) (by decide)
    rw [cb1] at f
    have bw := bc_eq_cwc len .wide
    have bl := h.bytes_lt
    rw [O.val32 (.inr (by omega_using [ao, nb, this])) (by omega_using [f, bw, bl]), a.mem, V₁, hp]
  refine WP.mono (export_ok I (p := 0) (l := 1) (c := true) (by decide) (by decide) I.outLen
    (by rw [S.esp]; exact Ox.keep rfl S.keeps) (BitVec.eq_of_toNat_eq W) V (fun _ => hpl))
    fun u₂ ⟨B, _, F₂, K₂, I₂, k₂⟩ => ⟨by rw [B]; rfl, ?_, S.keeps.trans K₂, I₂, kv.trans k₂.mono⟩
  rw [S.esp] at F₂
  exact (S.frame.mono fun r hr => List.mem_cons_of_mem _ hr).trans F₂

/-- An acceptance: p, the octets read so far used, 1. -/
theorem accept_ok (h : In Ex base bytes len args s) (Ox : OutAt args base bytes len 0 (s.gpr .esp) s.wr)
    {up : BitVec 32} (U : UsedAt base bytes up (s.gpr .esp) ⟨byteAddr (args 0), len⟩ s.wr)
    (hu : w32 s.mem base usedOff = up.toNat) {c p : Nat} (hc : w32 s.mem base curOff = c)
    (hp : sv s.mem base len .wide 9 = p) (hpl : p < 2 ^ (8 * len)) :
    WP isa accept s (Fin base len args up s 1 c (Spec.Rsa.i2osp p len)) := by
  unfold Impl.Ffdh.X86.Candidate.accept
  refine WP.seq (WP.mono (acceptOut_ok h Ox hp hpl) fun u ⟨B, F, K, I, k⟩ => ?_)
  have sp : u.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  refine WP.mono (curTail_ok I (up := up) (r := 1) (by rw [sp]; exact U.keep rfl K) (by rw [k.word_eq, hu])
    (by rw [k.word_eq, hc])) fun t ⟨E, Bt, W, Ft, Kt⟩ => ⟨E, by rw [Bt, B], W, ?_, K.trans (Kt.mono (by decide))⟩
  exact (F.mono fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)).trans
    (Ft.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))

end VG.Proof.Ffdh.X86.Cand

end

end

/-!
# The FFDH candidate on i686: the screened tests

`phaseWords δ ε` sets a phase's words for a modulus of `bits − δ` bits
(`phaseWords_ok`); `onPass` goes on after a phase that passed, and ends with
a rejection or a shortage otherwise (`onPass_ok`); `tests` runs one witness
for p, all of q's and the rest of p's: the result of `screenedChecks`
(`tests_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86 VG.Proof.Ffdh.X86.KeyGen
open VG.Impl.Ffdh.X86.Candidate

/-- A result's status, octets used and output, for p. -/
def resStatus : Option (Bool × Spec.RsaKeyGen.Rand) → Nat
  | none => 0
  | some (true, _) => 1
  | some (false, _) => 2

def resUsed (T : List Byte) : Option (Bool × Spec.RsaKeyGen.Rand) → Nat
  | none => 0
  | some (_, r) => T.length - r.length

def resOut (p len : Nat) : Option (Bool × Spec.RsaKeyGen.Rand) → List Byte
  | some (true, _) => Spec.Rsa.i2osp p len
  | _ => List.replicate len 0

theorem hdr_bits : Hdr bitsOff := ⟨.inl ⟨by decide, by decide⟩, by decide⟩
theorem hdr_k : Hdr kOff := ⟨.inr ⟨by decide, by decide⟩, by decide⟩

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- A phase's words for a modulus of `bits − δ` bits: those bits, their octets, and
`primeChecks (bits − δ) − ε` witnesses. -/
theorem phaseWords_ok (h : In Ex base bytes len args s) {bits δ ε : Nat} (hb : w32 s.mem base bitsOff = bits)
    (hδ : δ ≤ 1) (hε : ε ≤ 1) (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Step Ex base bytes len args s t → w32 t.mem base kOff = bits - δ →
      w32 t.mem base octOff = (bits - δ + 7) / 8 → w32 t.mem base cntOff = Spec.Ffdh.primeChecks (bits - δ) - ε →
      Kept base len [] [kOff, octOff, cntOff] s.mem t.mem → WP isa (.block is) t Q) :
    WP isa (.block (phaseWords δ ε ++ is)) s Q := by
  unfold phaseWords
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (hdr_read h hdr_bits) fun t₁ U₁ _ => wp_subi fun t₂ U₂ _ _ => ?_
  have e₂ : t₂.gpr .eax = BitVec.ofNat 32 (bits - δ) := by
    rw [U₂.gpr, U₁.gpr, hb, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_arith) (by omega_arith)]
  have K₂ : Keeps [.eax] s t₂ := U₁.keeps.trans (U₂.keeps.mono (by decide))
  have m₂ : t₂.mem = s.mem := by rw [U₂.mem, U₁.mem]
  refine hdr_store (h.regs K₂ m₂) hdr_k fun t₃ S₃ W₃ k₃ O₃ g₃ _ _ => ?_
  refine wp_addi fun t₄ U₄ => wp_shr (n := 3) (by decide) fun t₅ U₅ _ => ?_
  have e₅ : t₅.gpr .eax = BitVec.ofNat 32 ((bits - δ + 7) / 8) := by
    rw [U₅.gpr, U₄.gpr, g₃, e₂]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    show ((bits - δ) % 2 ^ 32 + 7) % 2 ^ 32 / 2 ^ 3 = _
    omega_arith
  have K₅ : Keeps [.eax] t₃ t₅ := U₄.keeps.trans U₅.keeps
  have m₅ : t₅.mem = t₃.mem := by rw [U₅.mem, U₄.mem]
  refine hdr_store (S₃.inp.regs K₅ m₅) hdr_oct fun t₆ S₆ W₆ k₆ O₆ g₆ _ _ => ?_
  refine wp_movS (hdr_read S₆.inp hdr_k) fun t₇ U₇ _ => wp_cmpi fun t₈ F₈ c₈ _ => wp_sbb_self c₈ fun t₉ U₉ =>
    wp_andi fun t₁₀ U₁₀ => wp_addi fun t₁₁ U₁₁ => ?_
  have kk₆ : w32 t₆.mem base kOff = bits - δ := by
    rw [k₆.word_eq, m₅, W₃, e₂, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have e₇ : (t₇.gpr .eax).toNat = bits - δ := by
    rw [U₇.gpr, kk₆, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have K₁₁ : Keeps [.eax, .ecx] t₆ t₁₁ :=
    ((((U₇.keeps.mono (by decide)).trans (F₈.keeps _)).trans (U₉.keeps.mono (by decide))).trans
      (U₁₀.keeps.mono (by decide))).trans (U₁₁.keeps.mono (by decide))
  have m₁₁ : t₁₁.mem = t₆.mem := by rw [U₁₁.mem, U₁₀.mem, U₉.mem, F₈.mem, U₇.mem]
  have e₁₁ : (t₁₁.gpr .ecx).toNat = Spec.Ffdh.primeChecks (bits - δ) - ε := by
    rw [U₁₁.gpr, U₁₀.gpr, U₉.gpr, e₇]
    unfold Spec.Ffdh.primeChecks
    by_cases small : bits - δ < 2049
    · simp only [show decide (bits - δ < (2049 : BitVec 32).toNat) = true from decide_eq_true small,
        ↓reduceIte, show bits - δ ≤ 2048 by omega_arith]
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      show (4294967232 + (128 - ε) % 2 ^ 32) % 2 ^ 32 = 64 - ε
      omega_arith
    · simp only [show decide (bits - δ < (2049 : BitVec 32).toNat) = false from decide_eq_false small,
        Bool.false_eq_true, ↓reduceIte, show ¬ bits - δ ≤ 2048 by omega_arith]
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      show (0 + (128 - ε) % 2 ^ 32) % 2 ^ 32 = 128 - ε
      omega_arith
  refine hdr_store (S₆.inp.regs K₁₁ m₁₁) hdr_cnt fun t S W kt O _ _ _ => ?_
  have S₁₁ : Step Ex base bytes len args t₆ t₁₁ := Step.regs S₆.inp m₁₁ K₁₁
  refine k t ((Step.regs h m₂ K₂).trans (S₃.trans ((Step.regs S₃.inp m₅ K₅).trans (S₆.trans (S₁₁.trans S)))))
    ?_ ?_ ?_ ?_
  · rw [kt.word_eq, m₁₁, kk₆]
  · rw [kt.word_eq, m₁₁, W₆, e₅, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  · rw [W, e₁₁]
  · exact (by rw [m₂]; exact (Kept.refl _).mono : Kept base len [] [kOff, octOff, cntOff] s.mem t₂.mem).trans
      (k₃.mono.trans ((by rw [m₅]; exact (Kept.refl _).mono : Kept base len [] [kOff, octOff, cntOff] t₃.mem t₅.mem).trans
        (k₆.mono.trans ((by rw [m₁₁]; exact (Kept.refl _).mono : Kept base len [] [kOff, octOff, cntOff] t₆.mem t₁₁.mem).trans
          kt.mono))))

/-- After a phase with the result `D`: on to `rest` if it passed, else a rejection or a shortage. -/
theorem onPass_ok (h : In Ex base bytes len args s) (Ox : OutAt args base bytes len 0 (s.gpr .esp) s.wr)
    {up : BitVec 32} (U : UsedAt base bytes up (s.gpr .esp) ⟨byteAddr (args 0), len⟩ s.wr)
    (hu : w32 s.mem base usedOff = up.toNat) {T : List Byte} {p : Nat} {D A : Option (Bool × Spec.RsaKeyGen.Rand)}
    (he : s.gpr .eax = BitVec.ofNat 32 (drawStatus D))
    (hcur : ∀ b r, D = some (b, r) → ∃ c, w32 s.mem base curOff = c ∧ c ≤ T.length ∧ T.drop c = r)
    (hF : ∀ r, D = some (false, r) → A = some (false, r)) (hN : D = none → A = none) {rest : Prog isa}
    (hrest : ∀ r, D = some (true, r) → ∀ u, In Ex base bytes len args u → u.mem = s.mem → Keeps [] s u →
      WP isa rest u (Fin base len args up u (resStatus A) (resUsed T A) (resOut p len A))) :
    WP isa (onPass rest) s (Fin base len args up s (resStatus A) (resUsed T A) (resOut p len A)) := by
  unfold onPass
  refine WP.seq (wp_cmpi fun u₁ F₁ _ z₁ => WP.block_nil ?_)
  have h₁ : In Ex base bytes len args u₁ := h.regs (F₁.keeps []) F₁.mem
  have S₁ : Step Ex base bytes len args s u₁ := Step.regs h F₁.mem (F₁.keeps [])
  have st : drawStatus D < 4 := by unfold drawStatus; split <;> decide
  have z : ∀ k, k < 4 → (BitVec.ofNat 32 (drawStatus D) - BitVec.ofNat 32 k == 0) = decide (drawStatus D = k) :=
    fun k hk => sub_beq (by omega_arith) (by omega_arith)
  refine WP.ite (decide (drawStatus D = 1)) (by show u₁.zf = _; rw [z₁, he]; exact congrArg some (z 1 (by decide)))
    (fun e => ?_) fun e => ?_
  · rcases D with _ | ⟨⟨⟩ | ⟨⟩, r⟩
    · simp [drawStatus] at e
    · simp [drawStatus] at e
    · exact WP.mono (hrest r rfl u₁ h₁ F₁.mem (F₁.keeps [])) fun t R => R.after S₁
  refine WP.seq (wp_cmpi fun u₂ F₂ _ z₂ => WP.block_nil ?_)
  have h₂ : In Ex base bytes len args u₂ := h₁.regs (F₂.keeps []) F₂.mem
  have S₂ : Step Ex base bytes len args s u₂ := S₁.trans (Step.regs h₁ F₂.mem (F₂.keeps []))
  have m₂ : u₂.mem = s.mem := by rw [F₂.mem, F₁.mem]
  have Ox₂ : OutAt args base bytes len 0 (u₂.gpr .esp) u₂.wr := by rw [S₂.esp]; exact Ox.keep rfl S₂.keeps
  have U₂ : UsedAt base bytes up (u₂.gpr .esp) ⟨byteAddr (args 0), len⟩ u₂.wr := by
    rw [S₂.esp]; exact U.keep rfl S₂.keeps
  refine WP.ite (decide (drawStatus D = 2))
    (by show u₂.zf = _; rw [z₂, F₁.gpr, he]; exact congrArg some (z 2 (by decide))) (fun e₂ => ?_) fun e₂ => ?_
  · rcases D with _ | ⟨⟨⟩ | ⟨⟩, r⟩
    · simp [drawStatus] at e₂
    · obtain ⟨c, hc, hcl, hr⟩ := hcur false r rfl
      rw [hF r rfl]
      refine WP.mono (reject_ok h₂ Ox₂ U₂ (by rw [m₂, hu]) (by rw [m₂, hc])) fun t R => ?_
      have : T.length - r.length = c := by rw [← hr, List.length_drop]; omega_arith
      exact R.after S₂ |> fun R' => by simp only [resStatus, resUsed, resOut, this]; exact R'
    · simp [drawStatus] at e
  · rcases D with _ | ⟨⟨⟩ | ⟨⟩, r⟩
    · rw [hN rfl]
      exact WP.mono (short_ok h₂ Ox₂ U₂ (by rw [m₂, hu])) fun t R => R.after S₂
    · simp [drawStatus] at e₂
    · simp [drawStatus] at e

/-- A phase and what follows it: `rest` from where a pass leaves the tape. -/
theorem phasePass_ok (h : In Ex base bytes len args s) {T : List Byte}
    (G : TapeGeo Ex args base bytes (s.gpr .esp) T.length)
    (hT : Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) T.length = T)
    (Ox : OutAt args base bytes len 0 (s.gpr .esp) s.wr) {up : BitVec 32}
    (U : UsedAt base bytes up (s.gpr .esp) ⟨byteAddr (args 0), len⟩ s.wr) (hu : w32 s.mem base usedOff = up.toNat)
    {j w n c p : Nat} (hj9 : 9 ≤ j) (hj : j ≤ 10) (hw : sv s.mem base len .wide j = w) (hw3 : 3 ≤ w)
    (hodd : w % 2 = 1) (ho : w32 s.mem base octOff = Spec.Ffdh.witnessOctets w)
    (hk : w32 s.mem base kOff = Spec.RsaKeyGen.bitLength (w - 1)) (hn : w32 s.mem base cntOff = n) (hn1 : 1 ≤ n)
    (hc : w32 s.mem base curOff = c) (hcT : c ≤ T.length) {A : Option (Bool × Spec.RsaKeyGen.Rand)}
    (hF : ∀ r, ParameterCandidate.checkWitnesses w n (T.drop c) = some (false, r) → A = some (false, r))
    (hN : ParameterCandidate.checkWitnesses w n (T.drop c) = none → A = none) {rest : Prog isa}
    (hrest : ∀ r, ParameterCandidate.checkWitnesses w n (T.drop c) = some (true, r) → ∀ u c',
      Step Ex base bytes len args s u → Kept base len [11, 13, 14, 15] (twoOff :: drawDs) s.mem u.mem →
      w32 u.mem base curOff = c' → c' ≤ T.length → T.drop c' = r →
      WP isa rest u (Fin base len args up u (resStatus A) (resUsed T A) (resOut p len A))) :
    WP isa (.seq (phase j) (onPass rest)) s (Fin base len args up s (resStatus A) (resUsed T A) (resOut p len A)) := by
  refine WP.seq (WP.mono (phase_ok h G hT hj9 hj hw hw3 hodd ho hk hn hn1 hc hcT) fun u ⟨Su, Eu, Cu, ku⟩ => ?_)
  refine WP.mono (onPass_ok Su.inp (by rw [Su.esp]; exact Ox.keep rfl Su.keeps)
    (by rw [Su.esp]; exact U.keep rfl Su.keeps) (by rw [ku.word_eq, hu]) Eu Cu hF hN
    fun r hD u' hu' m K => ?_) fun t R => R.after Su
  obtain ⟨c', hc', hcl, hr⟩ := Cu true r hD
  exact hrest r hD u' c' (Su.trans (Step.regs Su.inp m K)) (by rw [m]; exact ku) (by rw [m, hc']) hcl hr

/-- The screened tests of p (slot 9) and q (slot 10), with the tape read from `c₀`: the result of
`screenedChecks`. -/
theorem tests_ok (h : In Ex base bytes len args s) {T : List Byte}
    (G : TapeGeo Ex args base bytes (s.gpr .esp) T.length)
    (hT : Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) T.length = T)
    (Ox : OutAt args base bytes len 0 (s.gpr .esp) s.wr) {up : BitVec 32}
    (U : UsedAt base bytes up (s.gpr .esp) ⟨byteAddr (args 0), len⟩ s.wr) (hu : w32 s.mem base usedOff = up.toNat)
    {bits p q c₀ : Nat} (hb : w32 s.mem base bitsOff = bits) (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192)
    (hp : sv s.mem base len .wide 9 = p) (hq : sv s.mem base len .wide 10 = q) (hp3 : 3 ≤ p) (hpo : p % 2 = 1)
    (hq3 : 3 ≤ q) (hqo : q % 2 = 1) (hbp : Spec.RsaKeyGen.bitLength (p - 1) = bits)
    (hbp' : Spec.RsaKeyGen.bitLength p = bits) (hbq : Spec.RsaKeyGen.bitLength (q - 1) = bits - 1)
    (hbq' : Spec.RsaKeyGen.bitLength q = bits - 1) (hpl : p < 2 ^ (8 * len))
    (hc : w32 s.mem base curOff = c₀) (hcT : c₀ ≤ T.length) :
    WP isa tests s (Fin base len args up s
      (resStatus (ParameterCandidate.screenedChecks p q (T.drop c₀)))
      (resUsed T (ParameterCandidate.screenedChecks p q (T.drop c₀)))
      (resOut p len (ParameterCandidate.screenedChecks p q (T.drop c₀)))) := by
  unfold tests
  -- One witness for p.
  refine WP.seq (phaseWords_ok h hb (δ := 0) (ε := 0) (by decide) (by decide) hb1 hb2 fun t₁ S₁ K₁ O₁ _ k₁ =>
    wp_movi fun t₂ U₂ => hdr_store (S₁.inp.regs U₂.keeps U₂.mem) hdr_cnt fun t₃ S₃ W₃ k₃ _ _ _ _ => WP.block_nil ?_)
  have S₀ : Step Ex base bytes len args s t₃ := S₁.trans ((Step.regs S₁.inp U₂.mem U₂.keeps).trans S₃)
  have k₀ : Kept base len [] [kOff, octOff, cntOff] s.mem t₃.mem :=
    k₁.trans ((by rw [U₂.mem]; exact (Kept.refl _).mono : Kept base len [] [kOff, octOff, cntOff] t₁.mem t₂.mem).trans
      k₃.mono)
  refine WP.mono (phasePass_ok S₀.inp (by rw [S₀.esp]; exact G) (by rw [tape_keep G S₀, hT])
    (by rw [S₀.esp]; exact Ox.keep rfl S₀.keeps) (by rw [S₀.esp]; exact U.keep rfl S₀.keeps)
    (by rw [k₀.word_eq, hu]) (j := 9) (w := p) (n := 1) (c := c₀) (p := p) (by decide) (by decide)
    (by rw [k₀.slot_eq, hp]) hp3 hpo (by rw [k₃.word_eq, U₂.mem, O₁, Spec.Ffdh.witnessOctets, hbp, Nat.sub_zero])
    (by rw [k₃.word_eq, U₂.mem, K₁, hbp, Nat.sub_zero])
    (by rw [W₃, U₂.gpr]; rfl) (by decide) (by rw [k₀.word_eq, hc]) hcT
    (fun r hD => by unfold ParameterCandidate.screenedChecks; rw [hD]; rfl)
    (fun hD => by unfold ParameterCandidate.screenedChecks; rw [hD]; rfl) ?_) fun t R => R.after S₀
  intro r₁ hD₁ u₁ c₁ Su₁ ku₁ hc₁ hcl₁ hr₁
  have S₁' : Step Ex base bytes len args s u₁ := S₀.trans Su₁
  have kk₁ : Kept base len [11, 13, 14, 15] (kOff :: octOff :: twoOff :: drawDs) s.mem u₁.mem :=
    k₀.mono.trans ku₁.mono
  -- All of q's witnesses.
  refine WP.seq ?_
  rw [← List.append_nil (phaseWords 1 0)]
  refine phaseWords_ok Su₁.inp (by rw [kk₁.word_eq, hb]) (δ := 1) (ε := 0) (by decide) (by decide) hb1 hb2
    fun t₄ S₄ K₄ O₄ C₄ k₄ => WP.block_nil ?_
  have S₂ : Step Ex base bytes len args s t₄ := S₁'.trans S₄
  have kk₂ : Kept base len [11, 13, 14, 15] (kOff :: octOff :: twoOff :: drawDs) s.mem t₄.mem :=
    kk₁.trans k₄.mono
  refine WP.mono (phasePass_ok S₂.inp (by rw [S₂.esp]; exact G) (by rw [tape_keep G S₂, hT])
    (by rw [S₂.esp]; exact Ox.keep rfl S₂.keeps) (by rw [S₂.esp]; exact U.keep rfl S₂.keeps)
    (by rw [kk₂.word_eq, hu]) (j := 10) (w := q) (n := Spec.Ffdh.primeChecks (bits - 1)) (c := c₁) (p := p)
    (by decide) (by decide) (by rw [kk₂.slot_eq, hq]) hq3 hqo (by rw [O₄, Spec.Ffdh.witnessOctets, hbq])
    (by rw [K₄, hbq]) (by rw [C₄, Nat.sub_zero]) (by unfold Spec.Ffdh.primeChecks; split <;> decide)
    (by rw [k₄.word_eq, hc₁]) hcl₁
    (fun r hD => by
      rw [hr₁] at hD
      simp only [ParameterCandidate.screenedChecks, hD₁, hD, hbq', bind, Option.bind, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, Bool.not_false, pure])
    (fun hD => by
      rw [hr₁] at hD
      simp only [ParameterCandidate.screenedChecks, hD₁, hD, hbq', bind, Option.bind, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte])
    ?_) fun t R => R.after S₄
  intro r₂ hD₂ u₂ c₂ Su₂ ku₂ hc₂ hcl₂ hr₂
  rw [hr₁] at hD₂
  have S₃ : Step Ex base bytes len args s u₂ := S₂.trans Su₂
  have kk₃ : Kept base len [11, 13, 14, 15] (kOff :: octOff :: twoOff :: drawDs) s.mem u₂.mem :=
    kk₂.trans ku₂.mono
  have eA : ParameterCandidate.screenedChecks p q (T.drop c₀) =
      ParameterCandidate.checkWitnesses p (Spec.Ffdh.primeChecks bits - 1) (T.drop c₂) := by
    rw [hr₂]
    simp only [ParameterCandidate.screenedChecks, hD₁, hD₂, hbq', hbp', bind, Option.bind, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]
  rw [eA]
  -- The rest of p's.
  refine WP.seq ?_
  rw [← List.append_nil (phaseWords 0 1)]
  refine phaseWords_ok Su₂.inp (by rw [kk₃.word_eq, hb]) (δ := 0) (ε := 1) (by decide) (by decide) hb1 hb2
    fun t₅ S₅ K₅ O₅ C₅ k₅ => WP.block_nil ?_
  have S₆ : Step Ex base bytes len args s t₅ := S₃.trans S₅
  have kk₄ : Kept base len [11, 13, 14, 15] (kOff :: octOff :: twoOff :: drawDs) s.mem t₅.mem :=
    kk₃.trans k₅.mono
  refine WP.mono (phasePass_ok S₆.inp (by rw [S₆.esp]; exact G) (by rw [tape_keep G S₆, hT])
    (by rw [S₆.esp]; exact Ox.keep rfl S₆.keeps) (by rw [S₆.esp]; exact U.keep rfl S₆.keeps)
    (by rw [kk₄.word_eq, hu]) (j := 9) (w := p) (n := Spec.Ffdh.primeChecks bits - 1) (c := c₂) (p := p)
    (by decide) (by decide) (by rw [kk₄.slot_eq, hp]) hp3 hpo
    (by rw [O₅, Spec.Ffdh.witnessOctets, hbp, Nat.sub_zero]) (by rw [K₅, hbp, Nat.sub_zero])
    (by rw [C₅, Nat.sub_zero]) (by unfold Spec.Ffdh.primeChecks; split <;> decide)
    (by rw [k₅.word_eq, hc₂]) hcl₂ (fun r hD => hD) (fun hD => hD) ?_) fun t R => R.after S₅
  intro r₃ hD₃ u₃ c₃ Su₃ ku₃ hc₃ hcl₃ hr₃
  have kk₅ : Kept base len [11, 13, 14, 15] (kOff :: octOff :: twoOff :: drawDs) s.mem u₃.mem :=
    kk₄.trans ku₃.mono
  have S₇ : Step Ex base bytes len args s u₃ := S₆.trans Su₃
  rw [hD₃]
  have used : T.length - r₃.length = c₃ := by rw [← hr₃, List.length_drop]; omega_arith
  simp only [resStatus, resUsed, resOut, used]
  exact accept_ok Su₃.inp (by rw [S₇.esp]; exact Ox.keep rfl S₇.keeps) (by rw [S₇.esp]; exact U.keep rfl S₇.keeps)
    (by rw [kk₅.word_eq, hu]) hc₃ (by rw [kk₅.slot_eq, hp]) hpl

end VG.Proof.Ffdh.X86.Cand

end

end

/-! ### `Ffdh.X86.Cand.Spec`, which this module and modules that import it used -/

section

/-!
# The FFDH candidate on i686: its checks against the specification

The congruences of each generator (`gen2_eq`, `gen5_eq`), RSA's sieve on an
odd number past its primes (`sieve_shape`), and `sievedParameterCandidate`
for too short a tape, a rejected candidate and one that goes on to its
tests (`sieved_short`, `sieved_reject`, `sieved_tests`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.Spec.Ffdh VG.Proof.Ffdh.ParameterCandidate

/-- The table's sieve on an odd number past its primes: `primeShape` and RSA's sieve. -/
theorem sieve_shape {c bits : Nat} (hc : 8161 < c) (ho : c % 2 = 1) :
    (!VG.Proof.RsaKeyGen.trialPrefix c (sieveCount bits)) =
      (primeShape c && !Spec.RsaKeyGen.obviouslyComposite bits c) := by
  rw [← trialPrefix_sieveCount (bits := bits) hc, primeShape_sieve hc ho]
  by_cases hit : VG.Proof.RsaKeyGen.trialPrefix c (sieveCount bits) = true
  · simp only [hit, Bool.not_true, Bool.and_false]
  · have small : ((List.range 53).any fun i => c % VG.Impl.RsaKeyGen.tabEntry i == 0) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      apply hit
      simp only [List.any_eq_true, List.mem_range, beq_iff_eq] at h
      obtain ⟨i, hi, hd⟩ := h
      simp only [VG.Proof.RsaKeyGen.trialPrefix, List.any_eq_true, List.mem_range,
        VG.Proof.RsaKeyGen.entryDivides, decide_eq_true_eq]
      exact ⟨i, by unfold sieveCount; split <;> omega_using [hi], hd⟩
    simp only [Bool.eq_false_iff.mpr hit, small, Bool.not_false, Bool.and_self]

/-- The shape for the generator 2: `p mod 8 = 3` and `3 | p − 2`. -/
theorem gen2_eq {bits p : Nat} (hb : 512 ≤ bits ∧ bits ≤ 8192) (hl : Spec.RsaKeyGen.bitLength p = bits)
    (hp : 2 ≤ p) : generationShape bits 2 p = (decide (p % 8 = 3) && decide ((p - 2) % 3 = 0)) := by
  unfold generationShape
  simp only [hl, show (512 ≤ bits) = True from propext ⟨fun _ => trivial, fun _ => hb.1⟩,
    show (bits ≤ 8192) = True from propext ⟨fun _ => trivial, fun _ => hb.2⟩, decide_true, beq_self_eq_true,
    Bool.true_and, ↓reduceIte]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- The shape for the generator 5, of an odd p: `5 | p − 2` or `5 | p − 3`. -/
theorem gen5_eq {bits p : Nat} (hb : 512 ≤ bits ∧ bits ≤ 8192) (hl : Spec.RsaKeyGen.bitLength p = bits)
    (hp : 3 ≤ p) (ho : p % 2 = 1) :
    generationShape bits 5 p = (decide ((p - 2) % 5 = 0) || decide ((p - 3) % 5 = 0)) := by
  unfold generationShape
  simp only [hl, show (512 ≤ bits) = True from propext ⟨fun _ => trivial, fun _ => hb.1⟩,
    show (bits ≤ 8192) = True from propext ⟨fun _ => trivial, fun _ => hb.2⟩, decide_true, beq_self_eq_true,
    Bool.true_and, show ((5 : Nat) == 2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq]
  omega_using [hp, ho]

/-- Too short a tape for the candidate. -/
theorem sieved_short {bits g : Nat} {r : Spec.RsaKeyGen.Rand} (h : r.length < (bits + 7) / 8) :
    sievedParameterCandidate bits g r = none := by
  unfold sievedParameterCandidate
  rw [draw_of_short h]
  rfl

/-- A candidate its shape or sieve rejects. -/
theorem sieved_reject {bits g : Nat} {r : Spec.RsaKeyGen.Rand} (h : (bits + 7) / 8 ≤ r.length)
    (hr : (generationShape bits g (candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) &&
      primeShape (candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) &&
      primeShape ((candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8))) - 1) / 2) &&
      !Spec.RsaKeyGen.obviouslyComposite bits (candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) &&
      !Spec.RsaKeyGen.obviouslyComposite bits
        ((candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8))) - 1) / 2)) = false) :
    sievedParameterCandidate bits g r = some (none, r.drop ((bits + 7) / 8)) := by
  unfold sievedParameterCandidate
  rw [draw_of_le h]
  simp only [bind, Option.bind_some, hr, Bool.not_false, ↓reduceIte]
  rfl

/-- A candidate past its shape and sieve: the result of its tests. -/
theorem sieved_tests {bits g : Nat} {r : Spec.RsaKeyGen.Rand} (h : (bits + 7) / 8 ≤ r.length)
    (hr : (generationShape bits g (candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) &&
      primeShape (candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) &&
      primeShape ((candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8))) - 1) / 2) &&
      !Spec.RsaKeyGen.obviouslyComposite bits (candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) &&
      !Spec.RsaKeyGen.obviouslyComposite bits
        ((candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8))) - 1) / 2)) = true) :
    sievedParameterCandidate bits g r =
      (screenedChecks (candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8))))
        ((candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8))) - 1) / 2) (r.drop ((bits + 7) / 8))).map
        fun x => (if x.1 then some (candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) else none, x.2) := by
  have hs : primeShape (candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8)))) = true ∧
      primeShape ((candidateOf bits (Spec.Rsa.os2ip (r.take ((bits + 7) / 8))) - 1) / 2) = true := by
    simp only [Bool.and_eq_true] at hr
    exact ⟨hr.1.1.1.2, hr.1.1.2⟩
  rw [screenedChecks_eq hs.1 hs.2]
  unfold sievedParameterCandidate
  rw [draw_of_le h]
  simp only [bind, Option.bind_some, hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases screenedParameterWitnesses _ _ _ with
  | none => rfl
  | some x => rfl

end VG.Proof.Ffdh.X86.Cand

end

end

/-!
# The FFDH candidate on i686: p's checks and tests

`shape`: p from the tape's first `L` octets, cut to `bits` bits with its
top and lowest bits set (`shape_ok`); its generator's congruences
(`congruences_ok`); q (`half_ok`); and `main`: a rejection unless they hold,
q is odd and RSA's sieve passes p and q, else the tests (`main_ok`): the
result of `sievedParameterCandidate`.
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

/-- The tape's first `L` octets. -/
theorem bytesAt_take (m : Mem) (p : Addr) {L n : Nat} (h : L ≤ n) :
    Spec.Rsa.bytesAt m p L = (Spec.Rsa.bytesAt m p n).take L := by
  have := bytesAt_offset m p (a := 0) (b := L) (n := n) (by omega_arith)
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, List.drop_zero] using this

/-- p from the tape: `candidateOf bits x` for the integer `x` of its first `L` octets; the cursor
past them, and `bits` as the cut's width. -/
theorem shape_ok (h : In Ex base bytes len args s) {T : List Byte}
    (G : TapeGeo Ex args base bytes (s.gpr .esp) T.length)
    (hT : Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) T.length = T) (h3 : args 3 = BitVec.ofNat 32 len)
    (hL : len ≤ T.length) {bits : Nat} (hb : w32 s.mem base bitsOff = bits) (hbl : len = (bits + 7) / 8)
    (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192) :
    WP isa shape s fun t => Step Ex base bytes len args s t ∧
      sv t.mem base len .wide 9 = Spec.Ffdh.candidateOf bits (Spec.Rsa.os2ip (T.take len)) ∧
      w32 t.mem base curOff = len ∧ Kept base len [9] [curOff, kOff] s.mem t.mem := by
  have bl := h.bytes_lt
  obtain f9 := slot_fit1 h (j := 9) (by decide)
  obtain c1 := cb1 len
  obtain w1 := cw1 len
  obtain lb := len_le_bc len
  have lo' := h.lower'
  obtain bw := bc_eq_cwc len .wide
  have fit := G.fit
  have small := G.small
  unfold shape
  refine WP.seq (WP.mono (load_ok h (one_ok .wide) f9 (p := 2) (l := 3) (L := len) (by decide) (by decide) h3
    (by omega_arith) (by omega_arith) (by omega_arith)
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      VG.CallLay.inRegions_sub (off := 0) (G.rd _ _ h.extra) (by omega_arith : 0 + len ≤ T.length) (by omega_arith))
    (G.apart.sub_left (Region.sub_prefix hL))) fun u₁ ⟨V₁, O₁, K₁⟩ => ?_)
  rw [c1] at O₁
  rw [w1, bytesAt_take _ _ hL, hT] at V₁
  obtain S₁ : Step Ex base bytes len args s u₁ := Step.slot h (by decide) O₁ K₁
  obtain k₁ := kept_slot h O₁
  have h₁ := S₁.inp
  refine WP.seq (wp_movS (h₁.arg (i := 3) (by decide)) fun u₂ U₂ _ => ?_)
  refine hdr_store (h₁.regs U₂.keeps U₂.mem) hdr_cur fun u₃ S₃ W₃ k₃ O₃ g₃ _ _ => ?_
  refine wp_movS (hdr_read S₃.inp hdr_bits) fun u₄ U₄ _ => ?_
  refine hdr_store (S₃.inp.regs U₄.keeps U₄.mem) hdr_k fun u₅ S₅ W₅ k₅ O₅ _ _ _ => WP.block_nil ?_
  obtain S₂₅ : Step Ex base bytes len args u₁ u₅ :=
    (Step.regs h₁ U₂.mem U₂.keeps).trans (S₃.trans ((Step.regs S₃.inp U₄.mem U₄.keeps).trans S₅))
  obtain k₂₅ : Kept base len [] [curOff, kOff] u₁.mem u₅.mem :=
    (by rw [U₂.mem]; exact (Kept.refl _).mono : Kept base len [] [curOff, kOff] u₁.mem u₂.mem).trans
      (k₃.mono.trans ((by rw [U₄.mem]; exact (Kept.refl _).mono : Kept base len [] [curOff, kOff] u₃.mem u₄.mem).trans
        k₅.mono))
  obtain kw₅ : w32 u₅.mem base kOff = bits := by
    rw [W₅, U₄.gpr, k₃.word_eq, U₂.mem, k₁.word_eq, hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  obtain cw₅ : w32 u₅.mem base curOff = len := by
    rw [k₅.word_eq, U₄.mem, W₃, U₂.gpr, h3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  generalize hx : Spec.Rsa.os2ip (T.take len) = x at V₁
  obtain xl : x < 2 ^ (8 * len) := by
    have := VG.Proof.Bignum.os2ip_lt (T.take len)
    rw [List.length_take, Nat.min_eq_left hL, VG.Proof.Bignum.pow256_eq, hx] at this
    exact this
  obtain sv₅ : sv u₅.mem base len .wide 9 = x := by rw [k₂₅.slot_eq, ← V₁]
  refine WP.seq (WP.mono (cut_ok S₂₅.inp (j := 9) (by decide) true (k := bits) kw₅ (by omega_arith) (by omega_arith)
    (by rw [sv₅]; exact Nat.lt_of_lt_of_le xl (Nat.pow_le_pow_right (by decide) (by omega_arith))))
    fun u₆ ⟨h₆, O₆, V₆, K₆⟩ => ?_)
  simp only [↓reduceIte] at V₆
  rw [sv₅] at V₆
  obtain S₆ : Step Ex base bytes len args u₅ u₆ := Step.slot S₂₅.inp (by decide) O₆ K₆
  rw [← List.append_nil (setLow _)]
  refine setLow_ok h₆ (j := 9) (by decide) fun u₇ h₇ O₇ V₇ K₇ => WP.block_nil ?_
  obtain O₇' : Outside base (lo len (.slot .wide 9)) (bc len .wide) u₆.mem u₇.mem := O₇.mono (Nat.le_refl _) (by omega_arith)
  obtain S₇ : Step Ex base bytes len args u₆ u₇ := Step.slot h₆ (by decide) O₇' K₇
  refine ⟨S₁.trans (S₂₅.trans (S₆.trans S₇)), ?_, ?_, ?_⟩
  · rw [V₇, V₆]; rfl
  · rw [(kept_slot h₆ O₇').word_eq, (kept_slot S₂₅.inp O₆).word_eq, cw₅]
  · exact k₁.mono.trans (k₂₅.mono.trans ((kept_slot S₂₅.inp O₆).mono.trans (kept_slot h₆ O₇').mono))

theorem hdr_gen : Hdr genOff := ⟨.inl ⟨by decide, by decide⟩, by decide⟩
theorem hdr_ok : Hdr okOff := ⟨.inr ⟨by decide, by decide⟩, by decide⟩

/-- `p − t` into slot 12, through `t` in slot 16. -/
theorem minus_ok (h : In Ex base bytes len args s) {p t : Nat} (hp : sv s.mem base len .wide 9 = p) (ht : t ≤ p)
    (htl : t < 2 ^ 32) :
    WP isa (minus t) s fun u => Step Ex base bytes len args s u ∧ sv u.mem base len .wide 12 = p - t ∧
      Kept base len [12, 16] [] s.mem u.mem := by
  unfold minus
  refine WP.seq (WP.mono (setW_ok h (a := 16) (v := t) (by decide) htl) fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  obtain S₁ : Step Ex base bytes len args s u₁ := Step.slot h (by decide) O₁ K₁
  obtain p₁ : sv u₁.mem base len .wide 9 = p := by rw [slotKeep h (by decide) (by decide) O₁, hp]
  refine WP.mono (subW_ok S₁.inp (o := 12) (a := 9) (b := 16) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [V₁, p₁]; exact ht)) fun u ⟨S, V, k, _, _⟩ => ⟨S₁.trans S, by rw [V, V₁, p₁], ?_⟩
  exact (kept_slot h O₁).mono.trans k.mono

/-- A divisibility test, as a stage. -/
theorem dividesS_ok (h : In Ex base bytes len args s) {j : Nat} (hj : j ≤ 27) {prime inv : Nat}
    (p3 : 3 ≤ prime) (p65 : prime ≤ 65537) (podd : prime % 2 = 1) (pinv : (prime * inv + 1) % 2 ^ 32 = 0)
    (invl : inv < 2 ^ 32) :
    WP isa (divides (.slot .wide j) prime inv) s fun t => Step Ex base bytes len args s t ∧
      t.gpr .eax = BitVec.ofNat 32 (decide (sv s.mem base len .wide j % prime = 0)).toNat ∧
      Kept base len [] [] s.mem t.mem :=
  WP.mono (divides_ok h hj p3 p65 podd pinv invl) fun _ ⟨I, F, E, K⟩ =>
    ⟨⟨I, frameR_mono F (fun _ hp => nomatch hp), K⟩, E, kept_out h (r := below (s.gpr .esp) 96) F h.room.apart.symm⟩

/-- p's congruences for its generator `g` (2 or 5): `eax` its `generationShape`. -/
theorem congruences_ok (h : In Ex base bytes len args s) {p g bits : Nat} (hp : sv s.mem base len .wide 9 = p)
    (hp3 : 3 ≤ p) (hpo : p % 2 = 1) (hbl : Spec.RsaKeyGen.bitLength p = bits) (hb : 512 ≤ bits ∧ bits ≤ 8192)
    (hg : w32 s.mem base genOff = g) (hg25 : g = 2 ∨ g = 5) :
    WP isa congruences s fun t => Step Ex base bytes len args s t ∧
      t.gpr .eax = BitVec.ofNat 32 (Spec.Ffdh.generationShape bits g p).toNat ∧
      Kept base len [12, 16] [okOff] s.mem t.mem := by
  unfold congruences
  refine WP.seq (wp_movS (hdr_read h hdr_gen) fun u₁ U₁ _ => wp_cmpi fun u₂ F₂ _ z₂ => WP.block_nil ?_)
  obtain m₂ : u₂.mem = s.mem := by rw [F₂.mem, U₁.mem]
  obtain S₂ : Step Ex base bytes len args s u₂ := Step.regs h m₂ (U₁.keeps.trans (F₂.keeps _))
  have h₂ := S₂.inp
  obtain p₂ : sv u₂.mem base len .wide 9 = p := by rw [m₂, hp]
  obtain k₂ : Kept base len [12, 16] [okOff] s.mem u₂.mem := by rw [m₂]; exact (Kept.refl _).mono
  obtain gl : g < 2 ^ 32 := by omega_arith
  refine WP.ite (decide (g = 2)) (by
      show u₂.zf = _
      rw [z₂, U₁.gpr, hg, show (2 : BitVec 32) = BitVec.ofNat 32 2 from rfl, sub_beq gl (by decide)])
    (fun e => ?_) fun e => ?_
  · obtain rfl : g = 2 := by simpa using e
    rw [gen2_eq hb hbl (by omega_arith)]
    unfold gen2
    refine WP.seq (lowWord_ok h₂ (j := 9) (by decide) fun u₃ m₃ K₃ e₃ => wp_andi fun u₄ U₄ =>
      wp_cmpi fun u₅ F₅ _ z₅ => WP.block_nil ?_)
    obtain m₅ : u₅.mem = s.mem := by rw [F₅.mem, U₄.mem, m₃, m₂]
    obtain S₅ : Step Ex base bytes len args s u₅ :=
      S₂.trans (Step.regs h₂ (by rw [m₅, m₂]) ((K₃.trans (U₄.keeps.mono (by decide))).trans (F₅.keeps _)))
    obtain e₄ : u₄.gpr .eax = BitVec.ofNat 32 (p % 8) := by
      rw [U₄.gpr, e₃, p₂]
      apply BitVec.eq_of_toNat_eq
      obtain e8 : p % 2 ^ 32 % 8 = p % 8 := Nat.mod_mod_of_dvd p (by decide)
      rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide)),
        show (7 : BitVec 32).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, e8,
        Nat.mod_eq_of_lt (by omega_arith : p % 8 < 2 ^ 32)]
    refine WP.ite (decide (p % 8 = 3)) (by
        show u₅.zf = _
        rw [z₅, e₄, show (3 : BitVec 32) = BitVec.ofNat 32 3 from rfl, sub_beq (by omega_arith) (by decide)])
      (fun e₈ => ?_) fun e₈ => ?_
    · have p8 : p % 8 = 3 := by simpa using e₈
      refine WP.seq (WP.mono (minus_ok S₅.inp (p := p) (t := 2) (by rw [m₅, hp]) (by omega_arith) (by decide))
        fun u₆ ⟨S₆, V₆, k₆⟩ => ?_)
      refine WP.mono (dividesS_ok S₆.inp (j := 12) (prime := 3) (inv := inv3) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) fun t ⟨S, E, k⟩ => ⟨S₅.trans (S₆.trans S), ?_, ?_⟩
      · rw [E, V₆]; simp [p8]
      · exact (by rw [m₅]; exact (Kept.refl _).mono : Kept base len [12, 16] [okOff] s.mem u₅.mem).trans
          (k₆.mono.trans k.mono)
    · have p8 : ¬ p % 8 = 3 := by simpa using e₈
      refine wp_movi fun t U => WP.block_nil ⟨S₅.trans (Step.regs S₅.inp U.mem U.keeps), ?_, ?_⟩
      · rw [U.gpr]; simp [p8]
      · rw [U.mem, m₅]; exact (Kept.refl _).mono
  · have g5 : g = 5 := by
      have : ¬ g = 2 := by simpa using e
      omega_arith
    subst g5
    rw [gen5_eq hb hbl hp3 hpo]
    unfold gen5
    refine WP.seq (WP.mono (minus_ok h₂ (p := p) (t := 2) p₂ (by omega_arith) (by decide)) fun u₃ ⟨S₃, V₃, k₃⟩ => ?_)
    refine WP.seq (WP.mono (dividesS_ok S₃.inp (j := 12) (prime := 5) (inv := inv5) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)) fun u₄ ⟨S₄, E₄, k₄⟩ => ?_)
    rw [V₃] at E₄
    refine WP.seq (hdr_store S₄.inp hdr_ok fun u₅ S₅ W₅ k₅ _ g₅ _ _ => WP.block_nil ?_)
    obtain p₅ : sv u₅.mem base len .wide 9 = p := by rw [k₅.slot_eq, k₄.slot_eq, k₃.slot_eq, p₂]
    refine WP.seq (WP.mono (minus_ok S₅.inp (p := p) (t := 3) p₅ (by omega_arith) (by decide)) fun u₆ ⟨S₆, V₆, k₆⟩ => ?_)
    refine WP.seq (WP.mono (dividesS_ok S₆.inp (j := 12) (prime := 5) (inv := inv5) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)) fun u₇ ⟨S₇, E₇, k₇⟩ => ?_)
    rw [V₆] at E₇
    refine wp_orS (hdr_read S₇.inp hdr_ok) fun t U => WP.block_nil ⟨?_, ?_, ?_⟩
    · exact S₂.trans (S₃.trans (S₄.trans (S₅.trans (S₆.trans (S₇.trans (Step.regs S₇.inp U.mem U.keeps))))))
    · rw [U.gpr, E₇, k₇.word_eq, k₆.word_eq, W₅, E₄]
      cases decide ((p - 2) % 5 = 0) <;> cases decide ((p - 3) % 5 = 0) <;> rfl
    · exact k₂.trans (k₃.mono.trans (k₄.mono.trans (k₅.mono.trans (k₆.mono.trans (k₇.mono.trans
        (by rw [U.mem]; exact (Kept.refl _).mono))))))

/-- The specification's screen of p and q, in the machine's checks. -/
theorem screen_eq {bits g p : Nat} (hp : 8161 < p) (hpo : p % 2 = 1) (hq : 8161 < (p - 1) / 2) :
    (Spec.Ffdh.generationShape bits g p && Spec.Ffdh.primeShape p && Spec.Ffdh.primeShape ((p - 1) / 2) &&
      !Spec.RsaKeyGen.obviouslyComposite bits p && !Spec.RsaKeyGen.obviouslyComposite bits ((p - 1) / 2)) =
    (Spec.Ffdh.generationShape bits g p && decide ((p - 1) / 2 % 2 = 1) &&
      !VG.Proof.RsaKeyGen.trialPrefix p (sieveCount bits) &&
      !VG.Proof.RsaKeyGen.trialPrefix ((p - 1) / 2) (sieveCount bits)) := by
  rw [sieve_shape hp hpo]
  by_cases qo : (p - 1) / 2 % 2 = 1
  · rw [sieve_shape hq qo]
    simp only [qo, decide_true, Bool.and_true]
    cases Spec.Ffdh.generationShape bits g p <;> cases Spec.Ffdh.primeShape p <;>
      cases Spec.Ffdh.primeShape ((p - 1) / 2) <;> cases Spec.RsaKeyGen.obviouslyComposite bits p <;>
      cases Spec.RsaKeyGen.obviouslyComposite bits ((p - 1) / 2) <;> rfl
  · have : Spec.Ffdh.primeShape ((p - 1) / 2) = false := by
      unfold Spec.Ffdh.primeShape
      simp [show ¬ (p - 1) / 2 % 2 = 1 from qo]
    simp [this, qo]

/-- The octets used and the output of a candidate's result. -/
def candUsed (T : List Byte) : Option (Option Nat × Spec.RsaKeyGen.Rand) → Nat
  | some (_, rest) => T.length - rest.length
  | none => 0

def candOut (len : Nat) : Option (Option Nat × Spec.RsaKeyGen.Rand) → List Byte
  | some (some p, _) => Spec.Rsa.i2osp p len
  | _ => List.replicate len 0

theorem res_map (T : List Byte) (p len : Nat) (A : Option (Bool × Spec.RsaKeyGen.Rand)) :
    resStatus A = Proof.Ffdh.candidateStatus (A.map fun x => (if x.1 then some p else none, x.2)) ∧
      resUsed T A = candUsed T (A.map fun x => (if x.1 then some p else none, x.2)) ∧
      resOut p len A = candOut len (A.map fun x => (if x.1 then some p else none, x.2)) := by
  rcases A with _ | ⟨⟨⟩ | ⟨⟩, r⟩ <;> exact ⟨rfl, rfl, rfl⟩

/-- RSA's table after a stage. -/
theorem Table.step {Tb : BitVec 32} (TT : Table Tb (s.gpr .esp) s) {t : State}
    (S : Step Ex base bytes len args s t) (sy : t.syms = s.syms)
    (TA : Region.Disjoint ⟨Tb.setWidth 64, 8192⟩ ⟨base, bytes⟩) : Table Tb (t.gpr .esp) t := by
  have h := S.inp
  obtain fit := fR_fit h
  have bl := h.bytes_lt
  have tf := TT.fit
  refine ⟨by rw [sy]; exact TT.sym, fun i hi d hd => by rw [S.keeps.2.1, S.keeps.2.2]; exact TT.read i hi d hd,
    fun i hi => ?_, TT.fit, by rw [S.esp]; exact TT.far⟩
  rw [← TT.words i hi]
  refine S.frame.readW (r := ⟨Tb.setWidth 64, 8192⟩) (w := 64)
    (Offset.contains_base _ (by omega_arith : 8 * i + 8 ≤ 8192) (by omega_arith)) (fun r hr => ?_) (by decide)
  rw [frameR, List.mem_cons, List.mem_map] at hr
  rcases hr with rfl | ⟨q, hq, rfl⟩
  · exact TT.far
  · have := fit q hq
    exact TA.sub_right (Offset.sub_base _ (by omega_arith))

/-- `q = p >> 1` into slot 10. -/
theorem half_ok (h : In Ex base bytes len args s) {p : Nat} (hp : sv s.mem base len .wide 9 = p) :
    WP isa half s fun t => Step Ex base bytes len args s t ∧ sv t.mem base len .wide 10 = p / 2 ∧
      Kept base len [10] [] s.mem t.mem := by
  unfold half
  refine WP.seq (WP.mono (copyO_ok h (a := 9) (b := 10) (by decide) (by decide) (by decide))
    fun u ⟨S₁, V₁, k₁, _, _⟩ => ?_)
  refine WP.mono (halve_ok S₁.inp (j := 10) (by decide)) fun t ⟨_, O, V, K⟩ =>
    ⟨S₁.trans (Step.slot S₁.inp (by decide) O K), by rw [V, V₁, hp], k₁.trans (kept_slot S₁.inp O)⟩

/-- `test eax, eax` of a flag: ZF its negation. -/
theorem testEax_ok {b : Bool} (he : s.gpr .eax = BitVec.ofNat 32 b.toNat) :
    WP isa testEax s fun t => t.mem = s.mem ∧ Keeps [] s t ∧ isa.eval .e t = some (!b) :=
  wp_testS rfl fun t F z => WP.block_nil ⟨F.mem, F.keeps [], by
    show t.zf = _; rw [z, he]; cases b <;> rfl⟩

/-- q's lowest bit: ZF if q is even. -/
theorem oddQ_ok (h : In Ex base bytes len args s) {q : Nat} (hq : sv s.mem base len .wide 10 = q) :
    WP isa (.block (lowWord (.slot .wide 10) ++ ([.alu .and .eax (.imm 1)] : List Instr))) s fun t =>
      Step Ex base bytes len args s t ∧ t.mem = s.mem ∧ isa.eval .e t = some (decide (q % 2 = 0)) :=
  lowWord_ok h (j := 10) (by decide) fun u m K e => wp_andZ fun t U z => WP.block_nil
    ⟨Step.regs h (by rw [U.mem, m]) (K.trans (U.keeps.mono (by decide))), by rw [U.mem, m], by
      show t.zf = _
      rw [z, e, and_one_zero _ (Nat.mod_lt _ (by decide)), hq, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2 ^ 32)]⟩

/-- RSA's sieve, as a stage. -/
theorem sieveS_ok (h : In Ex base bytes len args s) {j : Nat} (hj : j ≤ 27) {Tb : BitVec 32}
    (TT : Table Tb (s.gpr .esp) s) {bits : Nat} (hb : w32 s.mem base bitsOff = bits) :
    WP isa (sieve (.slot .wide j)) s fun t => Step Ex base bytes len args s t ∧
      t.gpr .eax = BitVec.ofNat 32 (VG.Proof.RsaKeyGen.trialPrefix (sv s.mem base len .wide j) (sieveCount bits)).toNat ∧
      Kept base len [] [] s.mem t.mem :=
  WP.mono (sieve_ok h hj TT hb) fun _ ⟨I, F, E, K⟩ =>
    ⟨⟨I, frameR_mono F (fun _ hp => nomatch hp), K⟩, E, kept_out h (r := below (s.gpr .esp) 96) F h.room.apart.symm⟩

/-- p's checks and tests: the result of `sievedParameterCandidate` for a tape of at least `L`
octets. -/
theorem main_ok (h : In Ex base bytes len args s) {T : List Byte}
    (G : TapeGeo Ex args base bytes (s.gpr .esp) T.length)
    (hT : Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) T.length = T)
    (Ox : OutAt args base bytes len 0 (s.gpr .esp) s.wr) {up : BitVec 32}
    (U : UsedAt base bytes up (s.gpr .esp) ⟨byteAddr (args 0), len⟩ s.wr) (hu : w32 s.mem base usedOff = up.toNat)
    (h3 : args 3 = BitVec.ofNat 32 len) (hL : len ≤ T.length) {bits g : Nat} (hb : w32 s.mem base bitsOff = bits)
    (hbl : len = (bits + 7) / 8) (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192) (hg : w32 s.mem base genOff = g)
    (hg25 : g = 2 ∨ g = 5) {Tb : BitVec 32} (TT : Table Tb (s.gpr .esp) s)
    (TA : Region.Disjoint ⟨Tb.setWidth 64, 8192⟩ ⟨base, bytes⟩) :
    WP isa main s (Fin base len args up s
      (Proof.Ffdh.candidateStatus (Spec.Ffdh.sievedParameterCandidate bits g T))
      (candUsed T (Spec.Ffdh.sievedParameterCandidate bits g T))
      (candOut len (Spec.Ffdh.sievedParameterCandidate bits g T))) := by
  obtain hL' : (bits + 7) / 8 ≤ T.length := by omega_arith
  -- The candidate and q.
  generalize hx : Spec.Rsa.os2ip (T.take len) = x
  obtain ⟨hpo, hpl, hpu⟩ := ParameterCandidate.candidate_shape (bits := bits) (by omega_arith) x
  obtain ⟨hbp', hbp⟩ := ParameterCandidate.candidate_bitLength (bits := bits) (by omega_arith) x
  obtain hbq' := ParameterCandidate.half_bitLength (bits := bits) (by omega_arith) x
  generalize hp : Spec.Ffdh.candidateOf bits x = p at hpo hpl hpu hbp' hbp hbq'
  obtain big : 2 ^ 20 ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) (by omega_arith)
  obtain p8 : p < 2 ^ (8 * len) := Nat.lt_of_lt_of_le hpu (Nat.pow_le_pow_right (by decide) (by omega_arith))
  obtain screen := screen_eq (bits := bits) (g := g) (p := p) (by omega_arith) hpo (by omega_arith)
  -- A rejection, from a stage of `s` that keeps the cursor and `used`.
  obtain rej : ∀ u, Step Ex base bytes len args s u → w32 u.mem base curOff = len →
      w32 u.mem base usedOff = up.toNat →
      (Spec.Ffdh.generationShape bits g p && decide ((p - 1) / 2 % 2 = 1) &&
        !VG.Proof.RsaKeyGen.trialPrefix p (sieveCount bits) &&
        !VG.Proof.RsaKeyGen.trialPrefix ((p - 1) / 2) (sieveCount bits)) = false →
      WP isa reject u (Fin base len args up s
        (Proof.Ffdh.candidateStatus (Spec.Ffdh.sievedParameterCandidate bits g T))
        (candUsed T (Spec.Ffdh.sievedParameterCandidate bits g T))
        (candOut len (Spec.Ffdh.sievedParameterCandidate bits g T))) := by
    intro u Su hc hu' e
    rw [sieved_reject hL' (by rw [← hbl, hx, hp, screen, e])]
    refine WP.mono (reject_ok Su.inp (by rw [Su.esp]; exact Ox.keep rfl Su.keeps)
      (by rw [Su.esp]; exact U.keep rfl Su.keeps) hu' hc) fun t R => ?_
    have := R.after Su
    simp only [Proof.Ffdh.candidateStatus, candUsed, candOut, List.length_drop,
      show T.length - (T.length - (bits + 7) / 8) = len by omega_arith]
    exact this
  unfold main
  -- p.
  refine WP.seq (WP.mono_syms (shape_ok h G hT h3 hL hb hbl hb1 hb2) fun u₁ ⟨S₁, P₁, C₁, k₁⟩ sy₁ => ?_)
  rw [hx, hp] at P₁
  -- Its congruences.
  refine WP.seq (WP.mono_syms (congruences_ok S₁.inp P₁ (by omega_arith) hpo hbp' ⟨hb1, hb2⟩ (by rw [k₁.word_eq, hg])
    hg25) fun u₂ ⟨S₂, E₂, k₂⟩ sy₂ => ?_)
  refine WP.seq (WP.mono_syms (testEax_ok E₂) fun u₃ ⟨m₃, K₃, z₃⟩ sy₃ => ?_)
  obtain S₃ : Step Ex base bytes len args s u₃ := S₁.trans (S₂.trans (Step.regs S₂.inp m₃ K₃))
  obtain cur₃ : w32 u₃.mem base curOff = len := by rw [m₃, k₂.word_eq, C₁]
  obtain used₃ : w32 u₃.mem base usedOff = up.toNat := by rw [m₃, k₂.word_eq, k₁.word_eq, hu]
  obtain p₃ : sv u₃.mem base len .wide 9 = p := by rw [m₃, k₂.slot_eq, P₁]
  obtain bits₃ : w32 u₃.mem base bitsOff = bits := by rw [m₃, k₂.word_eq, k₁.word_eq, hb]
  refine WP.ite _ z₃ (fun e => rej u₃ S₃ cur₃ used₃ (by
    have : Spec.Ffdh.generationShape bits g p = false := by simpa using e
    simp [this])) fun e => ?_
  obtain gt : Spec.Ffdh.generationShape bits g p = true := by simpa using e
  -- q, odd.
  refine WP.seq (WP.mono_syms (half_ok S₃.inp p₃) fun u₄ ⟨S₄, Q₄, k₄⟩ sy₄ => ?_)
  rw [show p / 2 = (p - 1) / 2 by omega_arith] at Q₄
  refine WP.seq (WP.mono_syms (oddQ_ok S₄.inp Q₄) fun u₅ ⟨S₅, m₅, z₅⟩ sy₅ => ?_)
  obtain S₀₅ : Step Ex base bytes len args s u₅ := S₃.trans (S₄.trans S₅)
  obtain cur₅ : w32 u₅.mem base curOff = len := by rw [m₅, k₄.word_eq, cur₃]
  obtain used₅ : w32 u₅.mem base usedOff = up.toNat := by rw [m₅, k₄.word_eq, used₃]
  refine WP.ite _ z₅ (fun e => rej u₅ S₀₅ cur₅ used₅ (by
    have : ¬ (p - 1) / 2 % 2 = 1 := by simp at e; omega_arith
    simp [this])) fun e => ?_
  obtain qo : (p - 1) / 2 % 2 = 1 := by simp at e; omega_arith
  obtain hbq := ParameterCandidate.half_pred_bitLength (bits := bits) (by omega_arith) x (by rw [hp]; exact qo)
  rw [hp] at hbq
  -- RSA's sieve on p.
  obtain sy₀₅ : u₅.syms = s.syms := sy₅.trans (sy₄.trans (sy₃.trans (sy₂.trans sy₁)))
  refine WP.seq (WP.mono_syms (sieveS_ok S₀₅.inp (j := 9) (bits := bits) (by decide) (TT.step S₀₅ sy₀₅ TA)
    (by rw [m₅, k₄.word_eq, bits₃])) fun u₆ ⟨S₆, E₆, k₆⟩ sy₆ => ?_)
  rw [m₅, k₄.slot_eq, p₃] at E₆
  refine WP.seq (WP.mono_syms (testEax_ok E₆) fun u₇ ⟨m₇, K₇, z₇⟩ sy₇ => ?_)
  obtain S₀₇ : Step Ex base bytes len args s u₇ := S₀₅.trans (S₆.trans (Step.regs S₆.inp m₇ K₇))
  obtain cur₇ : w32 u₇.mem base curOff = len := by rw [m₇, k₆.word_eq, cur₅]
  obtain used₇ : w32 u₇.mem base usedOff = up.toNat := by rw [m₇, k₆.word_eq, used₅]
  obtain ne₇ : isa.eval .ne u₇ = some (VG.Proof.RsaKeyGen.trialPrefix p (sieveCount bits)) := by
    show u₇.zf.map (!·) = _
    rw [show u₇.zf = _ from z₇]; simp
  refine WP.ite _ ne₇ (fun e => rej u₇ S₀₇ cur₇ used₇ (by simp [e])) fun e => ?_
  -- RSA's sieve on q.
  obtain sy₀₇ : u₇.syms = s.syms := sy₇.trans (sy₆.trans sy₀₅)
  refine WP.seq (WP.mono_syms (sieveS_ok S₀₇.inp (j := 10) (bits := bits) (by decide) (TT.step S₀₇ sy₀₇ TA)
    (by rw [m₇, k₆.word_eq, m₅, k₄.word_eq, bits₃])) fun u₈ ⟨S₈, E₈, k₈⟩ sy₈ => ?_)
  rw [m₇, k₆.slot_eq, m₅, Q₄] at E₈
  refine WP.seq (WP.mono_syms (testEax_ok E₈) fun u₉ ⟨m₉, K₉, z₉⟩ sy₉ => ?_)
  obtain S₀₉ : Step Ex base bytes len args s u₉ := S₀₇.trans (S₈.trans (Step.regs S₈.inp m₉ K₉))
  obtain cur₉ : w32 u₉.mem base curOff = len := by rw [m₉, k₈.word_eq, cur₇]
  obtain used₉ : w32 u₉.mem base usedOff = up.toNat := by rw [m₉, k₈.word_eq, used₇]
  obtain ne₉ : isa.eval .ne u₉ = some (VG.Proof.RsaKeyGen.trialPrefix ((p - 1) / 2) (sieveCount bits)) := by
    show u₉.zf.map (!·) = _
    rw [show u₉.zf = _ from z₉]; simp
  refine WP.ite _ ne₉ (fun e' => rej u₉ S₀₉ cur₉ used₉ (by simp [e'])) fun e' => ?_
  -- The tests.
  obtain pass : (Spec.Ffdh.generationShape bits g p && decide ((p - 1) / 2 % 2 = 1) &&
      !VG.Proof.RsaKeyGen.trialPrefix p (sieveCount bits) &&
      !VG.Proof.RsaKeyGen.trialPrefix ((p - 1) / 2) (sieveCount bits)) = true := by simp [gt, qo, e, e']
  rw [sieved_tests hL' (by rw [← hbl, hx, hp, screen, pass])]
  rw [← hbl, hx, hp]
  obtain ⟨e₁, e₂, e₃⟩ := res_map T p len (ParameterCandidate.screenedChecks p ((p - 1) / 2) (T.drop len))
  rw [← e₁, ← e₂, ← e₃]
  obtain k₀₉ : Kept base len [9, 10, 12, 16] [curOff, kOff, okOff] s.mem u₉.mem :=
    k₁.mono.trans (k₂.mono.trans ((by rw [m₃]; exact (Kept.refl _).mono : Kept base len [9, 10, 12, 16]
      [curOff, kOff, okOff] u₂.mem u₃.mem).trans (k₄.mono.trans ((by rw [m₅]; exact (Kept.refl _).mono :
        Kept base len [9, 10, 12, 16] [curOff, kOff, okOff] u₄.mem u₅.mem).trans (k₆.mono.trans
          ((by rw [m₇]; exact (Kept.refl _).mono : Kept base len [9, 10, 12, 16] [curOff, kOff, okOff] u₆.mem
            u₇.mem).trans (k₈.mono.trans (by rw [m₉]; exact (Kept.refl _).mono))))))))
  refine WP.mono (tests_ok S₀₉.inp (by rw [S₀₉.esp]; exact G) (by rw [tape_keep G S₀₉, hT])
    (by rw [S₀₉.esp]; exact Ox.keep rfl S₀₉.keeps) (by rw [S₀₉.esp]; exact U.keep rfl S₀₉.keeps) used₉
    (by rw [k₀₉.word_eq, hb]) hb1 hb2 (by rw [m₉, k₈.slot_eq, m₇, k₆.slot_eq, m₅, k₄.slot_eq, p₃])
    (by rw [m₉, k₈.slot_eq, m₇, k₆.slot_eq, m₅, Q₄]) (by omega_arith) hpo (by omega_arith) qo hbp hbp' hbq hbq' p8 cur₉ hL)
    fun t R => R.after S₀₉

end VG.Proof.Ffdh.X86.Cand
