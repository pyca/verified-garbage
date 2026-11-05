module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Steps
public import VerifiedGarbage.Proof.Mont.X86_64.Words
import VerifiedGarbage.Proof.Weierstrass.X86_64.BytesLen
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Blocks
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-!
# Deterministic ECDSA on x86-64: P-521's shifts, and the candidate's `V`s

For P-521 (`big`), whose scalars are longer than any digest and whose `n`
has fewer bits than them: the `Q` bytes at an offset above the frame's
pointers, shifted right in place through the words at `scratch + 2560`
(`conv_ok`, by `loadBytes_ok`, `shrWords_ok` and `storeBytes_ok`), as for
the candidate `T`'s first `Q` bytes (`candTop_ok`); zero words above the
pointers (`zero9_ok`); and `genT` with one more `V` (`genT_succ`).
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
shifted right by `s` bits in place, through the words at `scratch + 2560`. -/
theorem conv_ok (hL : L.Ok) (hW : P.R.big = true) {t : State} (hc : Ctx L g m₀ t)
    (hdi : t.gpr .rdi = L.scr) {o s : Nat} (ho₁ : 232 ≤ o) (ho₂ : o + 72 ≤ 600) (hs₁ : 1 ≤ s) (hs₂ : s < 32) :
    WP isa (.block ((cfgOf P).conv o s)) t fun t' => Ctx L g m₀ t' ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → t'.gpr r = t.gpr r) ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (24 + o), P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (24 + o)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (24 + o)) P.Q) >>> s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h4, hw9, hQ8, hQ66, hQw, hwQ⟩ := P.sizes
  have hW' := P.sizesW hW
  have he := L.he
  have hnb := hL.nb
  refine WP.of_syms ?_
  rw [Cfg.conv, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .rsi) (by decide) (o := o) (by omega_arith)) fun u₁ h₁ => ?_
  have hS₁ : Scr u₁ L.scr 8192 := scr_keep (scr_of hL hc hdi) (h₁.keep _ (by decide)) (by rw [h₁.ctx.wr, hc.wr])
  have hsi₁ : u₁.gpr .rsi = L.B + BitVec.ofNat 64 (24 + o) := h₁.val
  refine WP.mono (loadBytes_ok hS₁ (len := P.Q) (n := P.w) (o := 2560) (src := .rsi) (by decide) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (fun d hd => by rw [hsi₁, Offset.add_add]; exact h₁.ctx.inFr (by omega_arith) (by omega_arith))
    (by rw [hsi₁]; exact hL.stk_scr (by omega_arith) (by omega_arith))) fun u₂ ⟨hv₂, k₂, O₂⟩ => ?_
  refine WP.mono (shrWords_ok (scr_keep hS₁ (k₂.gpr _ (by decide)) k₂.wr) (n := P.w) (o := 2560) (sh := s) (by omega_arith)
    hs₁ hs₂) fun u₃ ⟨hv₃, k₃, O₃⟩ => ?_
  refine WP.mono (ones_ok u₃) fun u₄ ⟨hm₄, hrd₄, hwr₄, hcx₄, hg₄⟩ => ?_
  have hsp₄ : u₄.gpr .rsp = L.B + BitVec.ofNat 64 24 := by
    rw [hg₄ _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), h₁.keep _ (by decide), hc.rsp]
  have hwr₄' : u₄.wr = t.wr := by rw [hwr₄, k₃.wr, k₂.wr, h₁.ctx.wr, hc.wr]
  have hdst : u₄.gpr .rsp + BitVec.ofNat 64 o = L.B + BitVec.ofNat 64 (24 + o) := by rw [hsp₄, Offset.add_add]
  refine WP.mono (storeBytes_ok (scr_keep (scr_keep hS₁ (k₂.gpr _ (by decide)) k₂.wr)
      ((hg₄ _ (by decide)).trans (k₃.gpr _ (by decide))) (hwr₄.trans k₃.wr))
    (len := P.Q) (n := P.w) (d := o) (a := 2560) (dst := .rsp) (by decide) (by decide) true
    (by rw [hcx₄]; rfl) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by rw [hdst, toNat_add_of (by omega_arith)]; omega_arith)
    (fun e m hem => by rw [hdst, Offset.add_add, hwr₄']; exact hc.inFrW (by omega_arith) (by omega_arith))
    (by rw [hdst]; exact (hL.stk_scr (by omega_arith) (by omega_arith)).symm)) fun u₅ ⟨hb₅, k₅, O₅⟩ hsy => ?_
  rw [hdst] at hb₅ O₅
  -- What changed: the words at `scratch + 2560`, and the bytes converted.
  have hf : Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (24 + o), P.Q⟩] t.mem u₅.mem := by
    have f₂ := frame_of_outside (O₂.trans O₃) (by omega_arith)
    have f₅ := frame_of_outside O₅ (by omega_arith)
    rw [add_ofNat_zero, hm₄] at f₅
    rw [h₁.mem] at f₂
    exact (f₂.sub fun r hr => ⟨⟨L.scr + BitVec.ofNat 64 2560, 72⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)⟩).trans
      (f₅.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩)
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

/-- A zero word at `rsp + o`, above the frame's pointers. -/
theorem zeroF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {o : Nat} (ho₁ : 232 ≤ o)
    (ho₂ : 24 + o + 8 ≤ 240 + 8 * L.e) :
    WP isa (.block [.alu32 .xor .rax (.reg .rax), .store (stk o) .rax]) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.B + BitVec.ofNat 64 (24 + o), 8⟩] u.mem u'.mem ∧
      ∀ k ≤ 8, Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (24 + o)) k = List.replicate k 0 := by
  have w := hc.inFrW (d := 24 + o) (n := 8) (by omega_arith) (by omega_arith)
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

/-! ## Zero words, and copies into the frame -/

/-- Nine zero words at `rsp + o`, above the frame's pointers. -/
theorem zero9_ok (hL : L.Ok) {o : Nat} (ho₁ : 232 ≤ o) (ho₂ : 24 + o + 72 ≤ 240 + 8 * L.e) :
    ∀ k ≤ 9, ∀ {u : State}, Ctx L g m₀ u →
    WP isa (.block ((List.range k).flatMap fun j => [.alu32 .xor .rax (.reg .rax), .store (stk (o + 8 * j)) .rax])) u
      fun u' => Ctx L g m₀ u' ∧ (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧
        Frame [⟨L.B + BitVec.ofNat 64 (24 + o), 72⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (24 + o)) (8 * k) = List.replicate (8 * k) 0
  | 0, _, u, hc => WP.of_runBlock ⟨u, rfl, hc, fun _ _ => rfl, Frame.refl _ _, rfl⟩
  | k + 1, hk, u, hc => by
    have := hL.nb
    have := L.he
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (zero9_ok hL ho₁ ho₂ k (by omega) hc) fun u₁ ⟨hc₁, hg₁, hf₁, hb₁⟩ => ?_
    refine WP.mono (zeroF_ok hL hc₁ (o := o + 8 * k) (by omega) (by omega)) fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
    refine ⟨hc₂, fun r hr => (hg₂ r hr).trans (hg₁ r hr), hf₁.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _,
      by simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)⟩), ?_⟩
    rw [show 8 * (k + 1) = 8 * k + 8 by omega, Proof.Hmac.Common.bytesAt_add, Offset.add_add,
      show 24 + o + 8 * k = 24 + (o + 8 * k) by omega, hb₂ 8 (Nat.le_refl _),
      bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), hb₁, List.replicate_append_replicate]

/-! ## The candidate -/

/-- `genT` with one more `V`: the last after the others. -/
theorem genT_succ (H : Spec.Hmac.HashFunction) (K : List Byte) : ∀ (k : Nat) (V : List Byte),
    Spec.Ecdsa.Rfc6979.genT H K (k + 1) V =
      ((Spec.Ecdsa.Rfc6979.genT H K k V).1 ++ Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K k V).2,
        Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K k V).2)
  | 0, V => by simp [Spec.Ecdsa.Rfc6979.genT]
  | k + 1, V => by
    show (Spec.Hmac.hmac H K V ++ (Spec.Ecdsa.Rfc6979.genT H K (k + 1) (Spec.Hmac.hmac H K V)).1,
        (Spec.Ecdsa.Rfc6979.genT H K (k + 1) (Spec.Hmac.hmac H K V)).2) =
      ((Spec.Hmac.hmac H K V ++ (Spec.Ecdsa.Rfc6979.genT H K k (Spec.Hmac.hmac H K V)).1) ++
          Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K k (Spec.Hmac.hmac H K V)).2,
        Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K k (Spec.Hmac.hmac H K V)).2)
    rw [genT_succ H K k (Spec.Hmac.hmac H K V)]
    simp

theorem genT_length (P : RfcHash) (K : List Byte) : ∀ (k : Nat) (V : List Byte),
    (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H K k V).1.length = k * P.H.D
  | 0, V => by simp [Spec.Ecdsa.Rfc6979.genT]
  | k + 1, V => by
    rw [genT_succ, List.length_append, genT_length P K k V, mac_length]
    rw [Nat.succ_mul]

/-- If `sh ≠ 0`: `T`'s first `Q` bytes shifted right by `sh` bits. -/
theorem candTop_ok (hL : L.Ok) (hW : P.R.big = true) (hsh : P.R.sh ≠ 0) (hsh8 : P.R.sh < 8) {t : State}
    (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).candTop) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (24 + fT), P.Q⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (24 + fT)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (24 + fT)) P.Q) >>> P.R.sh) := by
  have hsc : (cfgOf P).sh = P.R.sh := rfl
  have hbc : (cfgOf P).big = true := hW
  rw [Cfg.candTop, hbc, ite_eq_left_of_eq_true _ _ (eq_self true), hsc, WP.block_append_iff]
  refine WP.mono (scrPtr_ok hL hc) fun u₁ ⟨hc₁, hm₁, hdi₁, _⟩ => ?_
  refine WP.mono (conv_ok hL hW hc₁ hdi₁ (o := fT) (s := P.R.sh) (by decide) (by decide) (by omega) (by omega))
    fun u₂ ⟨hc₂, _, hf₂, hb₂⟩ => ?_
  rw [hm₁] at hf₂ hb₂
  exact ⟨hc₂, hf₂, hb₂⟩

end VG.Proof.Ecdsa.Rfc6979.X86_64
