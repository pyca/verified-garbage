module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Steps
public import VerifiedGarbage.Proof.Weierstrass.X86_64.BytesLen
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce

/-!
# Deterministic ECDSA on x86-64: scalars longer than the hash

For P-521's scalars (`wide`, 66 bytes in 9 words): the `Q` bytes at an
offset above the frame's pointers, shifted right in place through the words
at `scratch + 2816` (`conv_ok`, by `loadBytes_ok`, `shrWords_ok` and
`storeBytes_ok`), which makes `core`'s digest and the candidate; and copies
to and zero words in the frame above its pointers (`copyF_ok`, `zeroF_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Mont (wordsVal Outside off)
open VG.Proof.Mont.X86_64 (Scr KeepRegs)
open VG.Proof.Weierstrass.X86_64 (loadBytes_ok shrWords_ok storeBytes_ok)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

theorem scr_of (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .rdi = L.scr) : Scr t L.scr 8192 :=
  ⟨hdi, by rw [hc.wr]; simp, hL.nc⟩

theorem scr_keep {s s' : State} {base : Addr} {size : Nat} (h : Scr s base size) (hdi : s'.gpr .rdi = s.gpr .rdi)
    (hwr : s'.wr = s.wr) : Scr s' base size :=
  ⟨hdi.trans h.rdi, hwr ▸ h.wr, h.nowrap⟩

/-- `rcx ← -1`. -/
theorem ones_ok (u : State) : WP isa (.block [.movImm64 .rcx (BitVec.allOnes 64)]) u fun u' =>
    u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.gpr .rcx = BitVec.allOnes 64 ∧
      ∀ r, r ≠ .rcx → u'.gpr r = u.gpr r := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr⟩

/-- `conv o s`: the `Q` bytes at `rsp + o`, above the frame's pointers,
shifted right by `s` bits in place, through the words at `scratch + 2816`. -/
theorem conv_ok (hL : L.Ok) (hW : P.R.wide = true) {t : State} (hc : Ctx L g m₀ t)
    (hdi : t.gpr .rdi = L.scr) {o s : Nat} (ho₁ : 216 ≤ o) (ho₂ : o + 72 ≤ 496) (hs₁ : 1 ≤ s) (hs₂ : s < 32) :
    WP isa (.block ((cfgOf P).conv o s)) t fun t' => Ctx L g m₀ t' ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → t'.gpr r = t.gpr r) ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2816, 72⟩, ⟨L.B + BitVec.ofNat 64 (24 + o), P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (24 + o)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (24 + o)) P.Q) >>> s) := by
  obtain ⟨hw9, hQ66⟩ := P.sizesW hW
  have he := L.he
  have hnb := hL.nb
  refine WP.of_syms ?_
  rw [Cfg.conv, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .rsi) (by decide) (o := o) (by omega_arith)) fun u₁ h₁ => ?_
  have hS₁ : Scr u₁ L.scr 8192 := scr_keep (scr_of hL hc hdi) (h₁.keep _ (by decide)) (by rw [h₁.ctx.wr, hc.wr])
  have hsi₁ : u₁.gpr .rsi = L.B + BitVec.ofNat 64 (24 + o) := h₁.val
  refine WP.mono (loadBytes_ok hS₁ (len := P.Q) (n := P.w) (o := 2816) (src := .rsi) (by decide) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (fun d hd => by rw [hsi₁, Offset.add_add]; exact h₁.ctx.inFr (by omega_arith) (by omega_arith))
    (by rw [hsi₁]; exact hL.stk_scr (by omega_arith) (by omega_arith))) fun u₂ ⟨hv₂, k₂, O₂⟩ => ?_
  refine WP.mono (shrWords_ok (scr_keep hS₁ (k₂.gpr _ (by decide)) k₂.wr) (n := P.w) (o := 2816) (sh := s) (by omega_arith)
    hs₁ hs₂) fun u₃ ⟨hv₃, k₃, O₃⟩ => ?_
  refine WP.mono (ones_ok u₃) fun u₄ ⟨hm₄, hrd₄, hwr₄, hcx₄, hg₄⟩ => ?_
  have hsp₄ : u₄.gpr .rsp = L.B + BitVec.ofNat 64 24 := by
    rw [hg₄ _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), h₁.keep _ (by decide), hc.rsp]
  have hwr₄' : u₄.wr = t.wr := by rw [hwr₄, k₃.wr, k₂.wr, h₁.ctx.wr, hc.wr]
  have hdst : u₄.gpr .rsp + BitVec.ofNat 64 o = L.B + BitVec.ofNat 64 (24 + o) := by rw [hsp₄, Offset.add_add]
  refine WP.mono (storeBytes_ok (scr_keep (scr_keep hS₁ (k₂.gpr _ (by decide)) k₂.wr)
      ((hg₄ _ (by decide)).trans (k₃.gpr _ (by decide))) (hwr₄.trans k₃.wr))
    (len := P.Q) (n := P.w) (d := o) (a := 2816) (dst := .rsp) (by decide) (by decide) true
    (by rw [hcx₄]; rfl) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by rw [hdst, toNat_add_of (by omega_arith)]; omega_arith)
    (fun e m hem => by rw [hdst, Offset.add_add, hwr₄']; exact hc.inFrW (by omega_arith) (by omega_arith))
    (by rw [hdst]; exact (hL.stk_scr (by omega_arith) (by omega_arith)).symm)) fun u₅ ⟨hb₅, k₅, O₅⟩ hsy => ?_
  rw [hdst] at hb₅ O₅
  -- What changed: the words at `scratch + 2560`, and the bytes converted.
  have hf : Frame [⟨L.scr + BitVec.ofNat 64 2816, 72⟩, ⟨L.B + BitVec.ofNat 64 (24 + o), P.Q⟩] t.mem u₅.mem := by
    have f₂ := frame_of_outside (O₂.trans O₃) (by omega_arith)
    have f₅ := frame_of_outside O₅ (by omega_arith)
    rw [add_ofNat_zero, hm₄] at f₅
    rw [h₁.mem, show 8 * P.w = 72 by omega_arith] at f₂
    exact (f₂.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩).trans (f₅.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩)
  have hg : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → u₅.gpr r = t.gpr r := fun r h₁' h₂ h₃ h₄ => by
    rw [k₅.gpr _ (by simp [h₁', h₃]), hg₄ _ h₂, k₃.gpr _ (by simp [h₁', h₃]), k₂.gpr _ (by simp [h₁']),
      h₁.keep _ h₄]
  refine ⟨hc.keep hL (by rw [k₅.rd, hrd₄, k₃.rd, k₂.rd, h₁.ctx.rd, hc.rd]) (by rw [k₅.wr, hwr₄']) (hg _ (by decide)
      (by decide) (by decide) (by decide)) (fun r hr hr' => hg r (ne_cs hr (by decide)) (ne_cs hr (by decide))
      (ne_cs hr (by decide)) (ne_cs hr (by decide))) hf (hsy := hsy) fun r hr => ?_, hg, hf, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact safe_scr L (by omega_arith)
    · exact safe_high L (by omega_arith) (by omega_arith)
  · rw [ecdsa_bytesAt] at hb₅
    simp only [ite_true] at hb₅
    rw [hb₅, hm₄, hv₃, hv₂, hsi₁, ecdsa_bytesAt, h₁.mem]

/-! ## Copies into the frame above its pointers -/

/-- `8 K` bytes copied to `rsp + d`, above the frame's pointers, by `copyN`, with `Ctx` kept. -/
theorem copyF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : Addr} (hs : u.gpr src = S)
    (hsr : src ≠ .rax) {so d K : Nat} (hd₁ : 216 ≤ d) (hd₂ : 24 + d + 8 * K ≤ 520)
    (hr : ∀ j < K, InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (so + 8 * j)) 8)
    (hsep : Region.Disjoint ⟨S + BitVec.ofNat 64 so, 8 * K⟩ ⟨L.B + BitVec.ofNat 64 (24 + d), 8 * K⟩) :
    WP isa (.block (Cfg.copyN K src so .rsp d)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.B + BitVec.ofNat 64 (24 + d), 8 * K⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (24 + d)) (8 * K) =
        Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 so) (8 * K) := by
  have he := L.he
  rw [← fr_add] at hsep ⊢
  refine WP.mono_syms (copyN_ok (K := K) (by decide) hsr hsep (by omega_arith) K (Nat.le_refl _) u hs hc.rsp hr
    fun j hj => by rw [fr_add]; exact hc.inFrW (by omega_arith) (by omega_arith)) fun u' ⟨hrd, hwr, hg, hf, hb⟩ hsy => ?_
  refine ⟨hc.keep hL hrd hwr (hg _ (by decide)) (fun r hr _ => hg r (ne_cs hr (by decide))) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [fr_add]; exact safe_high L (by omega_arith) (by omega_arith))
      hsy,
    hg, hf, hb⟩

/-- A zero word at `rsp + o`, above the frame's pointers. -/
theorem zeroF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {o : Nat} (ho₁ : 216 ≤ o)
    (ho₂ : 24 + o + 8 ≤ 520) :
    WP isa (.block [.alu32 .xor .rax (.reg .rax), .store (stk o) .rax]) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.B + BitVec.ofNat 64 (24 + o), 8⟩] u.mem u'.mem ∧
      ∀ k ≤ 8, Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (24 + o)) k = List.replicate k 0 := by
  have w := hc.inFrW (d := 24 + o) (n := 8) (by omega_arith) (by have := L.he; omega_arith)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32, State.setReg32,
    State.store64, ea_stk, hc.rsp, Offset.add_add, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq,
    ite_false, ite_true, RegUpd.wr_setReg, RegUpd.wr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags, w,
    Option.bind_some, Option.some.injEq, exists_eq_left', xor_self_zx]
  have hf : Frame [⟨L.B + BitVec.ofNat 64 (24 + o), 8⟩] u.mem
      (u.mem.writeW (L.B + BitVec.ofNat 64 (24 + o)) (0 : BitVec 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.keep hL rfl rfl (by triv) (fun r hr _ => ?_) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega_arith) ho₂) rfl,
    fun r hr => ?_, hf, fun k hk => ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ne_cs hr (by decide : Reg.rax ∉ calleeSaved), ite_false]
  · simp only [hr, ite_false]
  · rw [bytesAt_take _ _ (k := 8 * 1) (by omega_arith), bytesAt_of_readW (k := 1) _ _ 0 fun j hj => by
      rw [show j = 0 by omega_arith, Nat.mul_zero, add_ofNat_zero, Mem.readW_writeW_self64],
      show (List.range (8 * 1)).map (fun i => (0 : BitVec 64).extractLsb' (8 * (i % 8)) 8) =
        List.replicate 8 0 by decide, List.take_replicate, Nat.min_eq_left hk]

/-- `sh` is 7 for P-521's sizes. -/
theorem sh7 (hW : P.R.wide = true) : P.R.sh = 7 := by
  have h₁ := P.R.nBits_len; have h₂ := P.R.sizesW hW; omega_arith

/-- `scratch` in `rdi`. -/
theorem scrPtr_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.scrPtr) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .rdi = L.scr := by
  have h208 := hc.inFr (d := 208) (by omega_arith) (by omega_arith)
  apply WP.of_runBlock
  simp only [Cfg.scrPtr, fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_stk,
    hc.rsp, Offset.add_add, Nat.reduceAdd, h208, ite_true, Option.map_some, hc.pScr, RegUpd.gpr_setReg_self,
    RegUpd.mem_setReg, Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL (d := .rdi) (by decide) rfl rfl rfl rfl fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, trivial, trivial⟩

end VG.Proof.Ecdsa.Rfc6979.X86_64
