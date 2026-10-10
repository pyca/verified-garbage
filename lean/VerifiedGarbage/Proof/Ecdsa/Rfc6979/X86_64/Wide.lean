import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Steps
import VerifiedGarbage.Proof.Weierstrass.X86_64.BytesLen

/-!
# Deterministic ECDSA on x86-64: scalars longer than the hash

For a curve whose scalars are longer than the hash function's output
(`wide`: P-521's 66 bytes with SHA-512's 64): the `Q` bytes at an offset
above the frame's pointers, shifted right in place through the words at
`scratch + 2560` (`conv_ok`, by `loadBytes_ok`, `shrWords_ok` and
`storeBytes_ok`); the digest for `core`, the digest then `Q - D` zero bytes
shifted right, which is the digest's number shifted left by `sh` bits
(`coreDigest_ok`); and the candidate, `V` kept above the pointers (`keepV_ok`)
and, after the next `V`, its first word after it, shifted right by `sh` bits
(`candTop_ok`).
-/

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

/-- In the wide case, the frame has 18 words above its pointers. -/
theorem e18 (hLe : L.e = P.e) (hW : P.R.wide = true) : L.e = 18 := by
  rw [hLe]; simp only [RfcHash.e, hW, ite_true]

/-- `conv o s`: the `Q` bytes at `rsp + o`, above the frame's pointers,
shifted right by `s` bits in place, through the words at `scratch + 2560`. -/
theorem conv_ok (hL : L.Ok) (hLe : L.e = P.e) (hW : P.R.wide = true) {t : State} (hc : Ctx L g m₀ t)
    (hdi : t.gpr .rdi = L.scr) {o s : Nat} (ho₁ : 216 ≤ o) (ho₂ : o + 72 ≤ 360) (hs₁ : 1 ≤ s) (hs₂ : s < 32) :
    WP isa (.block ((cfgOf P).conv o s)) t fun t' => Ctx L g m₀ t' ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → t'.gpr r = t.gpr r) ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (24 + o), P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (24 + o)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (24 + o)) P.Q) >>> s) := by
  obtain ⟨hw9, hQ66, -, -⟩ := P.sizesW hW
  have he := e18 hLe hW
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
    (hsr : src ≠ .rax) {so d K : Nat} (hd₁ : 216 ≤ d) (hd₂ : 24 + d + 8 * K ≤ 240 + 8 * L.e)
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
    (ho₂ : 24 + o + 8 ≤ 240 + 8 * L.e) :
    WP isa (.block [.alu32 .xor .rax (.reg .rax), .store (stk o) .rax]) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.B + BitVec.ofNat 64 (24 + o), 8⟩] u.mem u'.mem ∧
      ∀ k ≤ 8, Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (24 + o)) k = List.replicate k 0 := by
  have w := hc.inFrW (d := 24 + o) (n := 8) (by omega_arith) ho₂
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

theorem shift_mul (e : Nat) : (e * 2 ^ (8 * 2)) >>> (8 * (66 - 64) - 7) = e * 2 ^ 7 := by
  rw [show 8 * (66 - 64) - 7 = 9 from rfl, Nat.shiftRight_eq_div_pow,
    show e * 2 ^ (8 * 2) = e * 2 ^ 7 * 2 ^ 9 by rw [Nat.mul_assoc, ← Nat.pow_add],
    Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-! ## The digest for `core` -/

/-- The digest for `core`: the digest's number shifted left by `sh` bits, in
`Q` bytes above the pointers. -/
theorem coreDigest_ok (hL : L.Ok) (hLe : L.e = P.e) (hW : P.R.wide = true) (hdn : P.H.D ≤ dn) {t : State}
    (hc : Ctx L g m₀ t) (hsi : t.gpr .rsi = L.dg) (hdi : t.gpr .rdi = L.scr) :
    WP isa (.block (cfgOf P).coreDigest) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 240, P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 240) P.Q =
        Spec.Weierstrass.toBytes P.Q (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.dg P.H.D) * 2 ^ P.R.sh) := by
  obtain ⟨hw9, hQ66, hD64, -⟩ := P.sizesW hW
  have he := e18 hLe hW
  have hsh := sh7 hW
  show WP isa (.block ([.alu32 .xor .rax (.reg .rax), .store (stk (216 + P.Q - 8)) .rax] ++
    Cfg.copyN (P.H.D / 8) .rsi 0 .rsp 216 ++ (cfgOf P).conv 216 (8 * (P.Q - P.H.D) - P.R.sh))) t _
  rw [hQ66, hD64, hsh, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zeroF_ok hL hc (o := 216 + 66 - 8) (by omega_arith) (by omega_arith)) fun u₁ ⟨hc₁, hg₁, hf₁, hz₁⟩ => ?_
  have hdg₁ : Spec.Sha256.bytesAt u₁.mem L.dg 64 = Spec.Sha256.bytesAt t.mem L.dg 64 :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_DG (by omega_arith)).symm.sub_left (Region.sub_prefix (by omega_arith))) (by omega_arith)
  refine WP.mono (copyF_ok hL hc₁ (src := .rsi) (S := L.dg) ((hg₁ _ (by decide)).trans hsi) (by decide) (so := 0)
    (d := 216) (K := 64 / 8) (by omega_arith) (by omega_arith) (fun j hj => by rw [Nat.zero_add]; exact hc₁.inDg (by omega_arith) (by omega_arith))
    (by rw [add_ofNat_zero]
        exact (hL.stk_DG (by omega_arith)).symm.sub_left (Region.sub_prefix (by omega_arith)))) fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  refine WP.mono (conv_ok hL hLe hW hc₂ (by rw [hg₂ _ (by decide), hg₁ _ (by decide), hdi]) (o := 216) (s := 8 * (66 - 64) - 7)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun u₃ ⟨hc₃, _, hf₃, hb₃⟩ => ?_
  simp only [Nat.reduceAdd] at hf₃ hb₃
  rw [hQ66] at hf₃ hb₃
  refine ⟨hc₃, ?_, ?_⟩
  · refine ((hf₁.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩).trans
      (hf₂.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩)).trans hf₃
    · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)
  · -- The digest then two zero bytes, shifted right by 9 bits.
    have hY : Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 240) 66 =
        Spec.Sha256.bytesAt t.mem L.dg 64 ++ List.replicate 2 0 := by
      rw [show (66 : Nat) = 8 * (64 / 8) + 2 from rfl, Proof.Hmac.Common.bytesAt_add, hb₂, add_ofNat_zero,
        show 8 * (64 / 8) = 64 from rfl, hdg₁, Offset.add_add]
      refine congrArg (Spec.Sha256.bytesAt t.mem L.dg 64 ++ ·) ?_
      rw [bytesAt_frame hf₂ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
          (by omega_arith)]
      have h8 := hz₁ (6 + 2) (by omega_arith)
      rw [Proof.Hmac.Common.bytesAt_add, Offset.add_add, ← List.replicate_append_replicate] at h8
      simp only [Nat.reduceAdd, Nat.reduceSub] at h8 ⊢
      exact (List.append_inj h8 (by simp [Spec.Sha256.bytesAt])).2
    rw [hb₃, hY, ofBytes_append_zeros, shift_mul]

/-! ## The candidate -/

/-- What a candidate changes: `scratch`, the stack below the frame, `K` and
`V`, and the candidate above the pointers. -/
abbrev CWW {dn : Nat} (L : Lay dn) : List Region := [L.SCR, ⟨L.B, 152⟩, ⟨L.B + BitVec.ofNat 64 312, 72⟩]

theorem kvw_cww : ∀ r ∈ KVW L, ∃ r' ∈ CWW L, Region.Sub r r' := fun r hr => ⟨r, by
  simp only [CWW, KVW, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with h | h <;> simp [h], sub_refl _⟩

/-- `scratch` in `rdi`. -/
theorem scrPtr_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.scrPtr) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .rdi = L.scr := by
  have h208 := hc.inFr (d := 208) (by omega_arith) (by omega_arith)
  apply WP.of_runBlock
  simp only [Cfg.scrPtr, fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_stk,
    hc.rsp, Offset.add_add, Nat.reduceAdd, h208, ite_true, Option.map_some, hc.pScr, RegUpd.gpr_setReg_self,
    RegUpd.mem_setReg, Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL (d := .rdi) (by decide) rfl rfl rfl rfl fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, trivial, trivial⟩

/-- Two `V`s to a candidate: `V = HMAC_K(V)`, kept above the pointers, then
`V = HMAC_K(V)` again, its first word after it, and the candidate's `Q`
bytes shifted right by `sh` bits. -/
theorem candW_ok (hL : L.Ok) (hLe : L.e = P.e) (hW : P.R.wide = true) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).cand t fun u => Ctx L g m₀ u ∧ Frame (CWW L) t.mem u.mem ∧ kOf P L u.mem = kOf P L t.mem ∧
      vOf P L u.mem = P.mac (kOf P L t.mem) (P.mac (kOf P L t.mem) (vOf P L t.mem)) ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 312) P.Q =
        Spec.Weierstrass.toBytes P.Q (Spec.Weierstrass.ofBytes ((P.mac (kOf P L t.mem) (vOf P L t.mem) ++
          P.mac (kOf P L t.mem) (P.mac (kOf P L t.mem) (vOf P L t.mem))).take P.Q) >>> P.R.sh) := by
  obtain ⟨hw9, hQ66, hD64, -⟩ := P.sizesW hW
  have he := e18 hLe hW
  have hsh := sh7 hW
  have hwd : (cfgOf P).wide = true := hW
  have hD' : (cfgOf P).H.D = 64 := hD64
  simp only [Cfg.cand, Cfg.keepV, Cfg.candTop, hwd, ite_true, fV, fKb, hD', Nat.reduceDiv, Nat.reduceAdd]
  refine WP.seq (WP.mono (hmacV_ok hL hc) fun u₁ ⟨hc₁, hf₁, hk₁, hv₁⟩ => ?_)
  -- `V` above the pointers.
  refine WP.seq (WP.mono (copyF_ok hL hc₁ (src := .rsp) (S := L.B + BitVec.ofNat 64 24) hc₁.rsp (by decide)
    (so := 64) (d := 288) (K := 8) (by omega_arith) (by omega_arith)
    (fun j hj => by rw [fr_add]; exact hc₁.inFr (by omega_arith) (by omega_arith))
    (by rw [fr_add]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))) fun u₂ ⟨hc₂, _, hf₂, hb₂⟩ => ?_)
  rw [fr_add] at hb₂
  have hk₂ : kOf P L u₂.mem = kOf P L u₁.mem := bytesAt_frame hf₂ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums)) (by nums)
  have hv₂ : vOf P L u₂.mem = vOf P L u₁.mem := bytesAt_frame hf₂ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums)) (by nums)
  refine WP.seq (WP.mono (hmacV_ok hL hc₂) fun u₃ ⟨hc₃, hf₃, hk₃, hv₃⟩ => ?_)
  have hb₃ : Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 312) 64 = vOf P L u₁.mem := by
    rw [bytesAt_frame hf₃ (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by omega_arith)
      · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)) (by omega_arith)]
    simp only [Nat.reduceAdd] at hb₂
    rw [hb₂]
    show Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 88) 64 = Spec.Sha256.bytesAt u₁.mem _ P.H.D
    rw [hD64]
  refine WP.seq (WP.mono (scrPtr_ok hL hc₃) fun u₄ ⟨hc₄, hm₄, hdi₄⟩ => ?_)
  rw [WP.block_append_iff]
  -- The next eight bytes, from `V`.
  have hr₄ : InRegions (u₄.rd ++ u₄.wr) (L.B + BitVec.ofNat 64 24 + BitVec.ofNat 64 64) 8 := by
    rw [fr_add]; exact hc₄.inFr (by omega_arith) (by omega_arith)
  have hw₄ : InRegions u₄.wr (L.B + BitVec.ofNat 64 24 + BitVec.ofNat 64 352) 8 := by
    rw [fr_add]; exact hc₄.inFrW (by omega_arith) (by omega_arith)
  refine WP.mono_syms (copyW_ok (u := u₄) (src := .rsp) (dst := .rsp) (so := 64) (d := 352) hc₄.rsp hc₄.rsp hr₄
    hw₄ (by decide)) fun u₅ ⟨hrd₅, hwr₅, hg₅, hm₅⟩ hsy₅ => ?_
  rw [fr_add, fr_add] at hm₅
  have hf₅ : Frame [⟨L.B + BitVec.ofNat 64 (24 + 352), 8⟩] u₄.mem u₅.mem := by
    rw [hm₅]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hc₅ : Ctx L g m₀ u₅ := hc₄.keep hL hrd₅ hwr₅ (hg₅ _ (by decide)) (fun r hr _ => hg₅ r (ne_cs hr (by decide)))
    hf₅ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega_arith) (by omega_arith))
    hsy₅
  refine WP.mono (conv_ok hL hLe hW hc₅ (by rw [hg₅ _ (by decide), hdi₄]) (o := 288) (s := P.R.sh)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun u₆ ⟨hc₆, _, hf₆, hb₆⟩ => ?_
  simp only [Nat.reduceAdd] at hf₂ hb₂ hm₅ hf₅ hf₆ hb₆
  -- `K` and `V`, apart from the candidate and `scratch`.
  have dK : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 2560, 72⟩ : Region), ⟨L.B + BitVec.ofNat 64 312, P.Q⟩],
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 24, 128⟩ r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hL.stk_scr (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  have dK₅ : ∀ r ∈ [(⟨L.B + BitVec.ofNat 64 376, 8⟩ : Region)], Region.Disjoint ⟨L.B + BitVec.ofNat 64 24, 128⟩ r := by
    simp only [List.mem_singleton]; rintro r rfl; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  have kv : ∀ {m m' : Mem} {ws : List Region}, Frame ws m m' →
      (∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 24, 128⟩ r) →
      kOf P L m' = kOf P L m ∧ vOf P L m' = vOf P L m := fun hf hd =>
    ⟨bytesAt_frame (p := L.B + BitVec.ofNat 64 24) (n := P.H.D) hf
        (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega_arith) (by nums))) (by nums),
      bytesAt_frame (p := L.B + BitVec.ofNat 64 88) (n := P.H.D) hf
        (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega_arith) (by nums))) (by nums)⟩
  have e₆ := kv hf₆ dK
  have e₅ := kv hf₅ dK₅
  rw [hm₄] at e₅
  refine ⟨hc₆, ?_, ?_, ?_, ?_⟩
  · have c₃ : (⟨L.B + BitVec.ofNat 64 312, 72⟩ : Region) ∈ CWW L := by simp [CWW]
    have c₁ : L.SCR ∈ CWW L := by simp [CWW]
    refine ((((hf₁.sub kvw_cww).trans (hf₂.sub fun r hr => ⟨_, c₃, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)⟩)).trans
      (hf₃.sub kvw_cww)).trans (hm₄ ▸ hf₅.sub fun r hr => ⟨_, c₃, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)⟩)).trans
      (hf₆.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, c₁, Offset.sub_base _ (by omega_arith)⟩
    · exact ⟨_, c₃, Region.sub_prefix (by omega_arith)⟩
  · rw [e₆.1, e₅.1, hk₃, hk₂, hk₁]
  · rw [e₆.2, e₅.2, hv₃, hk₂, hv₂, hv₁, hk₁]
  · -- The candidate's bytes: the first `V`, then the next two of the second.
    have hkv : P.mac (kOf P L t.mem) (vOf P L t.mem) = vOf P L u₁.mem := hv₁.symm
    have hv₃' : P.mac (kOf P L t.mem) (P.mac (kOf P L t.mem) (vOf P L t.mem)) = vOf P L u₃.mem := by
      rw [hv₃, hk₂, hv₂, hv₁, hk₁]
    rw [hQ66] at hb₆ ⊢
    rw [hb₆, hv₃', hkv, List.take_append, List.take_of_length_le (by simp [Spec.Sha256.bytesAt]; omega_arith),
      show 66 - (vOf P L u₁.mem).length = 2 by simp [Spec.Sha256.bytesAt]; omega_arith]
    refine congrArg (fun x => Spec.Weierstrass.toBytes 66 (Spec.Weierstrass.ofBytes x >>> P.R.sh)) ?_
    rw [show (66 : Nat) = 64 + 2 from rfl, Proof.Hmac.Common.bytesAt_add, Offset.add_add]
    simp only [Nat.reduceAdd]
    congr 1
    · rw [bytesAt_frame hf₅ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
          (by omega_arith), hm₄, hb₃]
    · rw [bytesAt_take _ _ (k := 8) (by omega_arith), hm₅, bytesAt_copied, hm₄]
      show _ = (Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 88) P.H.D).take 2
      rw [hD64, ← bytesAt_take _ _ (by omega_arith), ← bytesAt_take _ _ (by omega_arith)]

end VG.Proof.Ecdsa.Rfc6979.X86_64
