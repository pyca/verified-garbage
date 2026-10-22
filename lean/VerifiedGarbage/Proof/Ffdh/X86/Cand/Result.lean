module

public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Base
public import VerifiedGarbage.Proof.Ffdh.X86.KeyGen
import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

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
  below : Region.Disjoint ⟨byteAddr up, 8⟩ (below sp 40)
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
      show byteAddr (t₁.gpr .ecx + BitVec.ofNat 32 0) = _; rw [ec]; exact byteAddr_add (by omega))
    (wIn t₁ U₁.wr 0 (by decide)) fun t₂ M₂ => ?_
  refine wp_movi fun t₃ U₃ => ?_
  refine wp_storeS (show t₃.ea (at_ .ecx 4) = byteAddr up + BitVec.ofNat 64 4 from by
      show byteAddr (t₃.gpr .ecx + BitVec.ofNat 32 4) = _
      rw [U₃.other _ (by decide), M₂.gpr, ec]; exact byteAddr_add (by omega))
    (by rw [U₃.wr, M₂.wr]; exact wIn t₁ U₁.wr 4 (by decide)) fun t₄ M₄ => ?_
  have mem₄ : t₄.mem = (s.mem.writeW (byteAddr up + BitVec.ofNat 64 0) (BitVec.ofNat 32 k)).writeW
      (byteAddr up + BitVec.ofNat 64 4) (0 : BitVec 32) := by
    rw [M₄.mem, U₃.gpr, U₃.mem, M₂.mem, U₁.other _ (by decide), U₁.mem, he]
  have F : Frame [⟨byteAddr up, 8⟩] s.mem t₄.mem := by
    rw [mem₄]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by omega))
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
  rw [Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by omega)]

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
    WP isa (.block (storeUsed ++ [.mov .eax (.imm (BitVec.ofNat 32 r))])) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 r ∧
      Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len = Spec.Rsa.bytesAt s.mem (byteAddr (args 0)) len ∧
      t.mem.readW (byteAddr up) 64 = BitVec.ofNat 64 k ∧ Frame [⟨byteAddr up, 8⟩] s.mem t.mem ∧
      Keeps [.eax, .ecx] s t := by
  refine storeUsed_ok h U hu hk he fun t₁ W F K _ => wp_movi fun t U' => WP.block_nil ⟨U'.gpr, ?_, ?_, ?_, ?_⟩
  · rw [U'.mem]
    have := h.upper
    exact frame_bytes F (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact U.out) (by omega)
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
  refine WP.mono (storeMask_ok hu (d := accOff) (c := false) (by omega) a.gpr) fun v ⟨I, O, W, _, K⟩ => ?_
  have S : Step Ex base bytes len args s v := (Step.regs h a.mem a.keeps).trans (Step.word hu (by omega) O K)
  have kv : Kept base len [] [accOff] s.mem v.mem := by
    rw [← a.mem]; exact kept_word hu (by omega) (by decide) O
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
    WP isa (.block ([.mov .eax (.mem (sc curOff))] ++ storeUsed ++ [.mov .eax (.imm (BitVec.ofNat 32 r))])) s
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

/-- An acceptance: p (slot 9), the cursor `c` used, 1. -/
theorem accept_ok (h : In Ex base bytes len args s) (Ox : OutAt args base bytes len 0 (s.gpr .esp) s.wr)
    {up : BitVec 32} (U : UsedAt base bytes up (s.gpr .esp) ⟨byteAddr (args 0), len⟩ s.wr)
    (hu : w32 s.mem base usedOff = up.toNat) {c p : Nat} (hc : w32 s.mem base curOff = c)
    (hp : sv s.mem base len .wide 9 = p) (hpl : p < 2 ^ (8 * len)) :
    WP isa accept s (Fin base len args up s 1 c (Spec.Rsa.i2osp p len)) := by
  have ao : accOff = 8 := rfl
  have nb : numBase = 3336 := rfl
  unfold Impl.Ffdh.X86.Candidate.accept
  refine WP.seq (WP.mono (copy19_ok h (a := 9) (by decide)) fun u₁ ⟨S₁, V₁, k₁⟩ => ?_)
  have h₁ := S₁.inp
  refine WP.seq (show WP isa (.block ([.mov .ecx (.imm (BitVec.allOnes 32))] ++ [.store (sc accOff) .ecx])) u₁ _ from
    WP.block_append (wp_movS rfl fun u a _ => WP.block_nil ?_))
  have hu' : In Ex base bytes len args u := h₁.regs a.keeps a.mem
  refine WP.mono (storeMask_ok hu' (d := accOff) (c := true) (by omega) a.gpr) fun v ⟨I, O, W, _, K⟩ => ?_
  have S : Step Ex base bytes len args s v := S₁.trans ((Step.regs h₁ a.mem a.keeps).trans (Step.word hu' (by omega) O K))
  have kv : Kept base len [19] [accOff] s.mem v.mem :=
    k₁.mono.trans (by rw [← a.mem]; exact (kept_word hu' (by omega) (by decide) O).mono)
  have V : val32 v.mem base (lo len (.slot .wide 19)) (cwc len .wide) = p := by
    have := lo_wide len 19
    have f := slot_fit1 h (j := 19) (by decide)
    rw [cb1] at f
    have bw := bc_eq_cwc len .wide
    have bl := h.bytes_lt
    rw [O.val32 (.inr (by omega)) (by omega), a.mem, V₁, hp]
  refine WP.seq (WP.mono (export_ok I (p := 0) (l := 1) (c := true) (by decide) (by decide) I.outLen
    (by rw [S.esp]; exact Ox.keep rfl S.keeps) (BitVec.eq_of_toNat_eq W) V (fun _ => hpl))
    fun u₂ ⟨B, _, F₂, K₂, I₂, k₂⟩ => ?_)
  have sp : u₂.gpr .esp = s.gpr .esp := by rw [K₂.1 _ (by decide), S.esp]
  refine WP.mono (curTail_ok I₂ (up := up) (r := 1) (by rw [sp]; exact U.keep rfl (S.keeps.trans K₂))
    (by rw [k₂.word_eq, kv.word_eq, hu]) (by rw [k₂.word_eq, kv.word_eq, hc]))
    fun t ⟨E, Bt, Wt, Ft, Kt⟩ => ⟨E, by rw [Bt, B]; rfl, Wt, ?_, (S.keeps.trans K₂).trans (Kt.mono (by decide))⟩
  rw [S.esp] at F₂
  exact ((S.frame.mono fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)).trans (F₂.mono fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))).trans
    (Ft.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))

end VG.Proof.Ffdh.X86.Cand
