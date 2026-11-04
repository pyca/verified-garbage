module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Steps
public import VerifiedGarbage.Proof.Mont.X86_64.Words
import VerifiedGarbage.Proof.Weierstrass.X86_64.BytesLen
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Blocks
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-!
# Deterministic ECDSA on x86-64: scalars longer than the hash

For a hash function whose output is shorter than the curve's scalars
(`wide`): the `Q` bytes at an offset above the frame's pointers, shifted
right in place through the words at `scratch + 2560` (`conv_ok`, by
`loadBytes_ok`, `shrWords_ok` and `storeBytes_ok`); `h`, `Q - D` zero bytes
then the digest (`hPrep_ok`); the digest for `core` if `sh ≠ 0`, the digest
between `Q - D - 1` zero bytes and one, shifted right by `8 - sh` bits, which
is the digest's number shifted left by `sh` bits (`xPrep_ok`); and the
candidate `T`, `m` successive `V = HMAC_K(V)` each copied after the last
(`candW_ok`), its first `Q` bytes then shifted right by `sh` bits
(`candTop_ok`).
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

/-- In the wide case, the frame has 34 words above its pointers. -/
theorem e34 (hLe : L.e = P.e) (hW : P.wide = true) : L.e = 34 := by
  rw [hLe]; simp only [RfcHash.e, hW, ite_true]

/-- `conv o s`: the `Q` bytes at `rsp + o`, above the frame's pointers,
shifted right by `s` bits in place, through the words at `scratch + 2560`. -/
theorem conv_ok (hL : L.Ok) (hLe : L.e = P.e) (hW : P.wide = true) {t : State} (hc : Ctx L g m₀ t)
    (hdi : t.gpr .rdi = L.scr) {o s : Nat} (ho₁ : 216 ≤ o) (ho₂ : o + 72 ≤ 488) (hs₁ : 1 ≤ s) (hs₂ : s < 32) :
    WP isa (.block ((cfgOf P).conv o s)) t fun t' => Ctx L g m₀ t' ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → t'.gpr r = t.gpr r) ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (24 + o), P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (24 + o)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (24 + o)) P.Q) >>> s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h4, hw9, hQ8, hQ66, hQw, hwQ, -, -⟩ := P.sizes
  have he := e34 hLe hW
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
theorem zero9_ok (hL : L.Ok) {o : Nat} (ho₁ : 216 ≤ o) (ho₂ : 24 + o + 72 ≤ 240 + 8 * L.e) :
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

/-- `Q` bytes copied to `rsp + d`, above the frame's pointers, by `copyBytes`, with `Ctx` kept. -/
theorem copyBF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : Addr} (hs : u.gpr src = S)
    (hsr : src ≠ .rax) {so d Q : Nat} (h8 : 8 ≤ Q) (hso : so + Q < 2 ^ 64) (hd₁ : 216 ≤ d)
    (hd₂ : 24 + d + Q ≤ 240 + 8 * L.e)
    (hr : ∀ j, j + 8 ≤ Q → InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (so + j)) 8)
    (hsep : Region.Disjoint ⟨S + BitVec.ofNat 64 so, Q⟩ ⟨L.B + BitVec.ofNat 64 (24 + d), Q⟩) :
    WP isa (.block (Cfg.copyBytes Q src so .rsp d)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.B + BitVec.ofNat 64 (24 + d), Q⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (24 + d)) Q =
        Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 so) Q := by
  have he := L.he
  rw [← fr_add] at hsep ⊢
  refine WP.mono_syms (copyBytes_ok (by decide) hsr hsep h8 hso (by omega) hs hc.rsp hr
    fun j hj => by rw [fr_add]; exact hc.inFrW (by omega) (by omega)) fun u' ⟨hrd, hwr, hg, hf, hb⟩ hsy => ?_
  refine ⟨hc.keep hL hrd hwr (hg _ (by decide)) (fun r hr _ => hg r (ne_cs hr (by decide))) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [fr_add]; exact safe_high L (by omega) (by omega))
      hsy,
    hg, hf, hb⟩

/-! ## `h` and the digest for `core` -/

/-- `h`: `Q - D` zero bytes, then the digest (at `rsi`), at `fX`. -/
theorem hPrep_ok (hL : L.Ok) (hLe : L.e = P.e) (hW : P.wide = true) (hdn : P.H.D ≤ dn) {t : State}
    (hc : Ctx L g m₀ t) (hsi : t.gpr .rsi = L.dg) :
    WP isa (.block (cfgOf P).hPrep) t fun t' => Ctx L g m₀ t' ∧ (∀ r, r ≠ .rax → t'.gpr r = t.gpr r) ∧
      Frame [⟨L.B + BitVec.ofNat 64 240, 72⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 240) P.Q =
        List.replicate (P.Q - P.H.D) 0 ++ Spec.Sha256.bytesAt t.mem L.dg P.H.D := by
  have he := e34 hLe hW
  have hQD : P.H.D < P.Q := by simpa [RfcHash.wide] using hW
  have := P.sizes
  rw [show (cfgOf P).hPrep = Cfg.zero9 fX ++ Cfg.copyBytes P.H.D .rsi 0 .rsp (216 + P.Q - P.H.D) from rfl,
    WP.block_append_iff]
  refine WP.mono (zero9_ok hL (o := fX) (by decide) (by rw [he]; decide) 9 (Nat.le_refl _) hc)
    fun u₁ ⟨hc₁, hg₁, hf₁, hb₁⟩ => ?_
  simp only [show 24 + fX = 240 from rfl] at hf₁ hb₁
  have hdg₁ : Spec.Sha256.bytesAt u₁.mem L.dg P.H.D = Spec.Sha256.bytesAt t.mem L.dg P.H.D :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_DG (by omega)).symm.sub_left (Region.sub_prefix hdn)) (by nums)
  have hsep : Region.Disjoint ⟨L.dg + BitVec.ofNat 64 0, P.H.D⟩
      ⟨L.B + BitVec.ofNat 64 (24 + (216 + P.Q - P.H.D)), P.H.D⟩ := by
    rw [add_ofNat_zero]
    exact (hL.stk_DG (by rw [he]; nums)).symm.sub_left (Region.sub_prefix hdn)
  refine WP.mono (copyBF_ok hL hc₁ (src := .rsi) (S := L.dg) ((hg₁ _ (by decide)).trans hsi) (by decide) (so := 0)
    (d := 216 + P.Q - P.H.D) (Q := P.H.D) (by nums) (by nums) (by omega) (by rw [he]; nums)
    (fun j hj => by rw [Nat.zero_add]; exact hc₁.inDg (by omega) (by nums)) hsep)
    fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  have e₁ : 24 + (216 + P.Q - P.H.D) = 240 + (P.Q - P.H.D) := by omega
  rw [e₁, add_ofNat_zero, hdg₁] at hb₂
  rw [e₁] at hf₂
  refine ⟨hc₂, fun r hr => (hg₂ r hr).trans (hg₁ r hr), hf₁.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _,
    by simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by nums)⟩), ?_⟩
  rw [show P.Q = (P.Q - P.H.D) + P.H.D by omega, Proof.Hmac.Common.bytesAt_add, Offset.add_add,
    show P.Q - P.H.D + P.H.D - P.H.D = P.Q - P.H.D by omega, hb₂,
    bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by nums)) (by omega)]
  have := bytesAt_take u₁.mem (L.B + BitVec.ofNat 64 240) (n := P.Q - P.H.D) (k := 8 * 9) (by nums)
  rw [this, hb₁, List.take_replicate, Nat.min_eq_left (by nums)]

theorem shift_back (e sh : Nat) (hs : sh < 8) : (e * 2 ^ 8) >>> (8 - sh) = e * 2 ^ sh := by
  rw [Nat.shiftRight_eq_div_pow, show e * 2 ^ 8 = e * 2 ^ sh * 2 ^ (8 - sh) by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- If `sh ≠ 0`: the digest for `core`, the digest's number shifted left by
`sh` bits, in `Q` bytes at `fXc`. -/
theorem xPrep_ok (hL : L.Ok) (hLe : L.e = P.e) (hW : P.wide = true) (hdn : P.H.D ≤ dn) (hsh : P.R.sh ≠ 0)
    {t : State} (hc : Ctx L g m₀ t) (hsi : t.gpr .rsi = L.dg) (hdi : t.gpr .rdi = L.scr) :
    WP isa (.block (cfgOf P).xPrep) t fun t' => Ctx L g m₀ t' ∧ t'.gpr .rdi = t.gpr .rdi ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 312, 72⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 312) P.Q =
        Spec.Weierstrass.toBytes P.Q (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.dg P.H.D) * 2 ^ P.R.sh) := by
  have he := e34 hLe hW
  have hQD : P.H.D < P.Q := by simpa [RfcHash.wide] using hW
  have hsl := P.R.nBits_len
  have hsh8 : P.R.sh < 8 := by omega
  have hsc : (cfgOf P).sh = P.R.sh := rfl
  have := P.sizes
  rw [Cfg.xPrep, hsc, ite_eq_right_of_eq_false _ _ (eq_false hsh),
    show Cfg.copyBytes (cfgOf P).D .rsi 0 .rsp (fXc + (cfgOf P).len - (cfgOf P).D - 1) =
      Cfg.copyBytes P.H.D .rsi 0 .rsp (288 + P.Q - P.H.D - 1) from rfl, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zero9_ok hL (o := fXc) (by decide) (by rw [he]; decide) 9 (Nat.le_refl _) hc)
    fun u₁ ⟨hc₁, hg₁, hf₁, hb₁⟩ => ?_
  simp only [show 24 + fXc = 312 from rfl] at hf₁ hb₁
  have hdg₁ : Spec.Sha256.bytesAt u₁.mem L.dg P.H.D = Spec.Sha256.bytesAt t.mem L.dg P.H.D :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_DG (by omega)).symm.sub_left (Region.sub_prefix hdn)) (by nums)
  have hsep : Region.Disjoint ⟨L.dg + BitVec.ofNat 64 0, P.H.D⟩
      ⟨L.B + BitVec.ofNat 64 (24 + (288 + P.Q - P.H.D - 1)), P.H.D⟩ := by
    rw [add_ofNat_zero]
    exact (hL.stk_DG (by rw [he]; nums)).symm.sub_left (Region.sub_prefix hdn)
  refine WP.mono (copyBF_ok hL hc₁ (src := .rsi) (S := L.dg) ((hg₁ _ (by decide)).trans hsi) (by decide) (so := 0)
    (d := 288 + P.Q - P.H.D - 1) (Q := P.H.D) (by nums) (by nums) (by omega) (by rw [he]; nums)
    (fun j hj => by rw [Nat.zero_add]; exact hc₁.inDg (by omega) (by nums)) hsep)
    fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  have e₁ : 24 + (288 + P.Q - P.H.D - 1) = 312 + (P.Q - P.H.D - 1) := by omega
  rw [e₁, add_ofNat_zero, hdg₁] at hb₂
  rw [e₁] at hf₂
  have hdi₂ : u₂.gpr .rdi = L.scr := by rw [hg₂ _ (by decide), hg₁ _ (by decide), hdi]
  refine WP.mono (conv_ok hL hLe hW hc₂ hdi₂ (o := fXc) (s := 8 - P.R.sh) (by decide) (by decide) (by omega)
    (by omega)) fun u₃ ⟨hc₃, hg₃, hf₃, hb₃⟩ => ?_
  simp only [show 24 + fXc = 312 from rfl] at hf₃ hb₃
  refine ⟨hc₃, by rw [hg₃ _ (by decide) (by decide) (by decide) (by decide), hg₂ _ (by decide), hg₁ _ (by decide)],
    ?_, ?_⟩
  · refine ((hf₁.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩).trans
      (hf₂.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩)).trans
      (hf₃.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact sub_refl _
    · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by nums)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., sub_refl _⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by nums)⟩
  · -- `Q - D - 1` zero bytes, the digest, and a zero byte, shifted right by `8 - sh` bits.
    have hY : Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 312) P.Q =
        List.replicate (P.Q - P.H.D - 1) 0 ++ (Spec.Sha256.bytesAt t.mem L.dg P.H.D ++ List.replicate 1 0) := by
      have hz : ∀ a n, a + n ≤ 72 → Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (312 + a)) n =
          List.replicate n 0 := fun a n han => by
        have h1 := bytesAt_take u₁.mem (L.B + BitVec.ofNat 64 312) (n := a + n) (k := 8 * 9) (by omega)
        rw [hb₁, List.take_replicate, Nat.min_eq_left (by omega), Proof.Hmac.Common.bytesAt_add, Offset.add_add,
          ← List.replicate_append_replicate] at h1
        exact (List.append_inj h1 (by simp [Spec.Sha256.bytesAt])).2
      have e := Proof.Hmac.Common.bytesAt_add u₂.mem (L.B + BitVec.ofNat 64 312) (P.Q - P.H.D - 1) (P.H.D + 1)
      have e' := Proof.Hmac.Common.bytesAt_add u₂.mem (L.B + BitVec.ofNat 64 312 + BitVec.ofNat 64 (P.Q - P.H.D - 1))
        P.H.D 1
      rw [show P.Q - P.H.D - 1 + (P.H.D + 1) = P.Q by omega] at e
      rw [Offset.add_add, Offset.add_add] at e'
      rw [Offset.add_add] at e
      have p₁ : Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 312) (P.Q - P.H.D - 1) =
          List.replicate (P.Q - P.H.D - 1) 0 := by
        rw [bytesAt_frame hf₂ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (by omega) (by omega) (by nums)) (by omega)]
        have := hz 0 (P.Q - P.H.D - 1) (by nums)
        rwa [Nat.add_zero] at this
      have p₃ : Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (312 + (P.Q - P.H.D - 1) + P.H.D)) 1 =
          List.replicate 1 0 := by
        rw [bytesAt_frame hf₂ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (by omega) (by omega) (by nums)) (by omega),
          show 312 + (P.Q - P.H.D - 1) + P.H.D = 312 + (P.Q - P.H.D - 1 + P.H.D) by omega]
        exact hz (P.Q - P.H.D - 1 + P.H.D) 1 (by nums)
      rw [e, e', hb₂, p₁, p₃]
    rw [hb₃, hY, ofBytes_zeros, ofBytes_append_zeros, show 8 * 1 = 8 from rfl, shift_back _ _ hsh8]

-- @@WIDE@@
end VG.Proof.Ecdsa.Rfc6979.X86_64
