module

import VerifiedGarbage.Proof.Ffdh.X86.Cand.Phase
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ScreenedStream
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Draw
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Base
public import VerifiedGarbage.Proof.Ffdh.X86.KeyGen
import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset

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
