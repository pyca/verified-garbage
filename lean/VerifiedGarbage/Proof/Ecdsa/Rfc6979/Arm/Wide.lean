module

import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Steps
public import VerifiedGarbage.Proof.Mont.Arm.Words
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Reduce
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Weierstrass.Arm.BytesLen
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Regs
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import Batteries.Logic
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Deterministic ECDSA on 32-bit ARM: scalars longer than the hash

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Wide.lean`), for a hash function
whose output is shorter than the curve's scalars (`wide`): the `Q` bytes at
an offset in the frame's top words, shifted right in place through the words
at `scratch + 2560` (`conv_ok`, by `loadBytes_ok`, `shrWords_ok` and
`storeBytes_ok`, with the table and `d` kept in `r2` and `r3` meanwhile, as
those use `r4` and `r5`; only P-521's sizes shift, `sh ≠ 0`); `h`, `Q - D`
zero bytes then the digest (`hPrep_ok`); the digest for `core` if `sh ≠ 0`,
the digest between `Q - D - 1` zero bytes and one, shifted right by `8 - sh`
bits, which is the digest's number shifted left by `sh` bits (`xPrep_ok`);
and the candidate `T`, `m` successive `V = HMAC_K(V)` each copied after the
last (`candW_ok`), its first `Q` bytes then shifted right by `sh` bits
(`candTop_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.Mont (wordsVal Outside off ofs)
open VG.Proof.Mont.Arm (Scr)
open VG.Proof.X25519.Arm (Rest Upd wp_ldr wp_str wp_dp wp_mov wp_movw op2_reg op2_imm dpVal)
open VG.Proof.Weierstrass.Arm (loadBytes_ok shrWords_ok storeBytes_ok)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

theorem frame_of_outside {base : Addr} {d n : Nat} {m m' : Mem} (h : Outside base d n m m')
    (hn : d + n ≤ 2 ^ 64) : Frame [⟨base + BitVec.ofNat 64 d, n⟩] m m' := fun x hx => h x (by
  have h₁ := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at h₁
  have h₂ := Offset.lt_iff x base hn
  simp only [ofs]
  omega_arith)

/-- `scratch`'s first 4096 bytes, as the conversions address them from `r12`. -/
theorem scr_of (hL : L.Ok) {t : State} (hwr : t.wr = [L.FR, L.OUT, L.SCR]) (h12 : t.gpr .r12 = L.scr) :
    Scr t (State.addr L.scr) 4096 :=
  ⟨by rw [h12], ⟨8192, by omega_arith, by omega_arith, by rw [hwr]; simp⟩, by have := hL.nc; rw [toNat_addr]; omega_arith,
    Nat.le_refl _⟩

theorem scr_keep {s s' : State} {base : Addr} {size : Nat} (h : Scr s base size) (h12 : s'.gpr .r12 = s.gpr .r12)
    (hwr : s'.wr = s.wr) : Scr s' base size :=
  ⟨h12 ▸ h.wb, hwr ▸ h.wr, h.nowrap, h.small⟩

/-- If the hash is shorter than the scalars, the frame has 68 words at its top. -/
theorem e68 (hLe : L.e = P.e) (hW : P.wide = true) : L.e = 68 := by
  rw [hLe]; simp only [RfcHash.e, Impl.Ecdsa.Rfc6979.Arm.extra, hW, ↓reduceIte]

/-- Only P-521's scalars are shifted. -/
theorem curveW (hsh : P.R.sh ≠ 0) : P.R.wide = true := by
  cases h : P.R.wide
  · have := P.R.sizesA h; have := P.R.nBits_len; omega_arith
  · rfl

/-- If the hash is shorter than the scalars, `h` is at the frame's top. -/
theorem hB_wide (hW : P.wide = true) : P.hB = 240 := by
  simp only [RfcHash.hB, hW, Bool.true_or, ↓reduceIte]

theorem allOnes_movt : ((0xffff : BitVec 16) ++ ((0xffff : BitVec 16).setWidth 32).extractLsb' 0 16 : BitVec 32) =
    BitVec.allOnes 32 := by decide

/-- `conv o s`: the `Q` bytes at `r8 + o`, in the frame's top words, shifted
right by `s` bits in place, through the words at `scratch + 2560`. -/
theorem conv_ok (hL : L.Ok) (hLe : L.e = P.e) (hS : P.R.wide = true) (hW : P.wide = true) {t : State}
    (hc : Ctx L g m₀ t) {o s : Nat} (ho₁ : 216 ≤ o) (ho₂ : o + 72 ≤ 488) (hoe : encodable (BitVec.ofNat 32 o) = true) (hs₁ : 1 ≤ s)
    (hs₂ : s < 32) :
    WP isa (.block ((cfgOf P).conv o s)) t fun t' => Ctx L g m₀ t' ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r10 → r ≠ .r12 → t'.gpr r = t.gpr r) ∧
      Frame [⟨State.addr L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (24 + o), P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (24 + o)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (24 + o)) P.Q) >>> s) := by
  apply WP.of_syms
  have hw9 : P.w = 9 := (P.R.sizesW hS).1
  have hQ66 : P.Q = 66 := (P.R.sizesW hS).2.1
  have he := e68 hLe hW
  have nB := hL.nB
  have nc := hL.nc
  have hfp := fp_toNat' hL
  have := L.sp.isLt
  have hw2 : (cfgOf P).w / 2 = P.w := by simp only [cfgOf, show P.R.E.C.len = 66 from hQ66, show P.R.E.n = 9 from hw9]; decide
  have hlen : (cfgOf P).len = P.Q := rfl
  simp only [Cfg.conv, hw2, hlen, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movS (op2_reg _ _) fun u₁ v₁ => wp_movS (op2_reg _ _) fun u₂ v₂ => ?_
  refine wp_dpS (op2_imm hoe) fun u₃ v₃ => wp_movS (op2_reg _ _) fun u₄ v₄ => ?_
  have K₄ : Rest [.r1, .r2, .r3, .r12] t u₄ :=
    (v₁.rest (by simp)).trans <| (v₂.rest (by simp)).trans <| (v₃.rest (by simp)).trans (v₄.rest (by simp))
  have h12 : u₄.gpr .r12 = L.scr := by
    rw [v₄.gpr, v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), hc.r11]
  have hS₄ : Scr u₄ (State.addr L.scr) 4096 := scr_of hL (by rw [K₄.wr, hc.wr]) h12
  have hr1 : u₄.gpr .r1 = L.fp + BitVec.ofNat 32 o := by
    rw [v₄.other _ (by decide), v₃.gpr, dpVal, v₂.other _ (by decide), v₁.other _ (by decide), hc.r8]
  have ha₁ : State.addr (L.fp + BitVec.ofNat 32 o) = L.B + BitVec.ofNat 64 (24 + o) := hL.fpA (by omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (loadBytes_ok hS₄ (len := P.Q) (n := P.w) (o := 2560) (src := .r1) (by decide) (by omega_arith)
    (by rw [hr1, fp_toNat hL (by omega_arith)]; omega_arith) (by omega_arith) (by omega_arith)
    (fun d hd => by rw [hr1, ha₁, Offset.add_add, K₄.rd, K₄.wr]; exact hc.inFr (by omega_arith) (by omega_arith))
    (by rw [hr1, ha₁]; exact (hL.stk_scr (by omega_arith) (by omega_arith)))) fun u₅ ⟨hv₅, k₅, O₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (shrWords_ok (scr_keep hS₄ (k₅.gpr _ (by decide)) k₅.wr) (n := P.w) (o := 2560) (sh := s)
    (by omega_arith) hs₁ hs₂) fun u₆ ⟨hv₆, k₆, O₆⟩ => ?_
  refine wp_movwS fun u₇ v₇ => wp_movt fun u₈ v₈ => ?_
  have h10 : u₈.gpr .r10 = BitVec.allOnes 32 := by rw [v₈.gpr, v₇.gpr]; exact allOnes_movt
  have K₈ : Rest [.r4, .r5, .r10] u₅ u₈ :=
    (k₆.mono (by simp)).trans <| (v₇.rest (by simp)).trans (v₈.rest (by simp))
  have hS₈ : Scr u₈ (State.addr L.scr) 4096 := scr_keep hS₄
    (by rw [K₈.gpr _ (by decide), k₅.gpr _ (by decide)]) (by rw [K₈.wr, k₅.wr])
  have h8 : u₈.gpr .r8 = L.fp := by rw [K₈.gpr _ (by decide), k₅.gpr _ (by decide), K₄.gpr _ (by decide), hc.r8]
  have hdst : State.addr (u₈.gpr .r8) + BitVec.ofNat 64 o = L.B + BitVec.ofNat 64 (24 + o) := by
    rw [h8, hL.fpA0, Offset.add_add]
  rw [WP.block_append_iff]
  refine WP.mono (storeBytes_ok hS₈ (len := P.Q) (n := P.w) (d := o) (a := 2560) (dst := .r8) (by decide)
    (by decide) true (by rw [h10]; rfl) (by omega_arith) (by omega_arith) (by omega_arith) (by rw [h8]; omega_arith) (by omega_arith)
    (fun e m hem => by
      rw [hdst, Offset.add_add, K₈.wr, k₅.wr, K₄.wr]; exact hc.inFrW (by omega_arith) (by omega_arith))
    (by rw [hdst]; exact (hL.stk_scr (by omega_arith) (by omega_arith)).symm)) fun u₉ ⟨hb₉, k₉, O₉⟩ => ?_
  rw [hdst] at hb₉ O₉
  refine wp_movS (op2_reg _ _) fun u₁₀ v₁₀ => wp_movS (op2_reg _ _) fun u₁₁ v₁₁ => WP.block_nil (fun sy => ?_)
  -- Through the conversion, every register but those it writes.
  have K : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r10 → r ≠ .r12 →
      u₉.gpr r = t.gpr r := fun r h1 h2 h3 h4 h5 h10' h12' => by
    rw [k₉.gpr _ (by simp [h4, h5]), K₈.gpr _ (by simp [h4, h5, h10']), k₅.gpr _ (by simp [h4]),
      K₄.gpr _ (by simp [h1, h2, h3, h12'])]
  have hr2 : u₉.gpr .r2 = t.gpr .r4 := by
    rw [k₉.gpr _ (by decide), K₈.gpr _ (by decide), k₅.gpr _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr]
  have hr3 : u₉.gpr .r3 = t.gpr .r5 := by
    rw [k₉.gpr _ (by decide), K₈.gpr _ (by decide), k₅.gpr _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide)]
  have hg : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r10 → r ≠ .r12 → u₁₁.gpr r = t.gpr r :=
    fun r h1 h2 h3 h10' h12' => by
      by_cases h4 : r = .r4
      · subst h4; rw [v₁₁.other _ (by decide), v₁₀.gpr, hr2]
      by_cases h5 : r = .r5
      · subst h5; rw [v₁₁.gpr, v₁₀.other _ (by decide), hr3]
      rw [v₁₁.other _ h5, v₁₀.other _ h4, K r h1 h2 h3 h4 h5 h10' h12']
  have m₄ : u₄.mem = t.mem := by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  have m₈ : u₈.mem = u₆.mem := by rw [v₈.mem, v₇.mem]
  have hm : u₁₁.mem = u₉.mem := by rw [v₁₁.mem, v₁₀.mem]
  -- What changed: the words at `scratch + 2560`, and the bytes converted.
  have hf : Frame [⟨State.addr L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (24 + o), P.Q⟩]
      t.mem u₁₁.mem := by
    have f₅ := frame_of_outside (O₅.trans O₆) (by omega_arith)
    have f₉ := frame_of_outside O₉ (by omega_arith)
    rw [BitVec.add_zero, m₈] at f₉
    rw [show 8 * P.w = 72 by omega_arith, m₄] at f₅
    rw [hm]
    exact (f₅.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩).trans (f₉.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩)
  have hp : ∀ r ∈ ptrRegs, r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r10 ∧ r ≠ .r12 := by decide
  refine ⟨hc.keep hL (by rw [v₁₁.rd, v₁₀.rd, k₉.rd, K₈.rd, k₅.rd, K₄.rd])
      (by rw [v₁₁.wr, v₁₀.wr, k₉.wr, K₈.wr, k₅.wr, K₄.wr]) (by rw [v₁₁.sp, v₁₀.sp, k₉.sp, K₈.sp, k₅.sp, K₄.sp])
      (fun r hr => hg r (hp r hr).1 (hp r hr).2.1 (hp r hr).2.2.1 (hp r hr).2.2.2.1 (hp r hr).2.2.2.2) hf
      (fun r hr => ?_) sy, hg, hf, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact safe_scr L (by omega_arith)
    · exact safe_high L (by omega_arith) (by omega_arith)
  · rw [ecdsa_bytesAt] at hb₉
    simp only [ite_true] at hb₉
    rw [hm, hb₉, m₈, hv₆, hv₅, hr1, ha₁, ecdsa_bytesAt, m₄]

/-! ## Copies into the frame's top words -/

theorem fpd (hL : L.Ok) (d : Nat) : State.addr L.fp + BitVec.ofNat 64 d = L.B + BitVec.ofNat 64 (24 + d) := by
  rw [hL.fpA0, Offset.add_add]

/-- `4 K` bytes copied to `r8 + d`, in the frame's top words, by `copyN`, with `Ctx` kept. -/
theorem copyF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : BitVec 32} (hs : u.gpr src = S)
    (hsr : src ≠ .r0) {so d K : Nat} (hd₁ : 216 ≤ d) (hd₂ : d + 4 * K ≤ 216 + 4 * L.e) (hso : so + 4 * K ≤ 4096)
    (hsn : S.toNat + so + 4 * K ≤ 2 ^ 32)
    (hr : ∀ j < K, InRegions (u.rd ++ u.wr) (State.addr S + BitVec.ofNat 64 (so + 4 * j)) 4)
    (hsep : Region.Disjoint ⟨State.addr S + BitVec.ofNat 64 so, 4 * K⟩ ⟨L.B + BitVec.ofNat 64 (24 + d), 4 * K⟩) :
    WP isa (.block (Cfg.copyN K src so .r8 d)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧ Frame [⟨L.B + BitVec.ofNat 64 (24 + d), 4 * K⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (24 + d)) (4 * K) =
        Spec.Sha256.bytesAt u.mem (State.addr S + BitVec.ofNat 64 so) (4 * K) := by
  have nB := hL.nB
  have he := L.he
  have hfp := fp_toNat' hL
  have := L.sp.isLt
  refine WP.mono_syms (copyN_ok (K := K) (by decide) hsr (by rw [fpd hL]; exact hsep) hsn (by omega_arith) hso (by omega_arith) K
    (Nat.le_refl _) u hs hc.r8 hr fun j hj => by rw [fpd hL]; exact hc.inFrW (by omega_arith) (by omega_arith))
    fun u' ⟨hrd, hwr, hsp, hg, hf, hb⟩ sy => ?_
  rw [fpd hL] at hf hb
  exact ⟨hc.keep hL hrd hwr hsp (fun r hr => hg r (ptr_r0 r hr)) hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega_arith) (by omega_arith)) sy, hg, hf, hb⟩

/-- A zero word at `r8 + o`, in the frame's top words. -/
theorem zeroF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {o : Nat} (ho₁ : 216 ≤ o)
    (ho₂ : o + 4 ≤ 216 + 4 * L.e) :
    WP isa (.block [.mov .r0 (.imm 0), .str .r0 .r8 o]) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧ Frame [⟨L.B + BitVec.ofNat 64 (24 + o), 4⟩] u.mem u'.mem ∧
      ∀ k ≤ 4, Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (24 + o)) k = List.replicate k 0 := by
  have he := L.he
  refine wp_movS (op2_imm (v := 0) (by decide)) fun s₁ u₁ =>
    wp_strS (a := L.B + BitVec.ofNat 64 (24 + o)) (by omega_arith)
      (by rw [u₁.other _ (by decide), hc.r8]; exact hL.fpA (by omega_arith))
      (by rw [u₁.wr]; exact hc.inFrW (by omega_arith) (by omega_arith)) fun s₂ m₂ => WP.block_nil ?_
  have hm : s₂.mem = u.mem.writeW (L.B + BitVec.ofNat 64 (24 + o)) (0 : BitVec 32) := by
    rw [m₂.mem, u₁.mem, u₁.gpr]
  have hf : Frame [⟨L.B + BitVec.ofNat 64 (24 + o), 4⟩] u.mem s₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨(hc.upd u₁ (by decide)).keep hL m₂.rd m₂.wr m₂.sp (fun r _ => by rw [m₂.gpr]) (by rw [u₁.mem]; exact hf)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega_arith) (by omega_arith)) m₂.syms,
    fun r hr => by rw [m₂.gpr, u₁.other _ hr], hf, fun k hk => by rw [hm]; exact bytesAt_writeW_zero _ _ hk⟩

/-- `k` zero words at `r8 + o`, in the frame's top words, from `r0 = 0`. -/
theorem zeros_ok (hL : L.Ok) {o : Nat} (ho₁ : 216 ≤ o) (ho₂ : o + 72 ≤ 216 + 4 * L.e) :
    ∀ k ≤ 18, ∀ (u : State), Ctx L g m₀ u → u.gpr .r0 = 0 →
    WP isa (.block ((List.range k).map fun j => Instr.str .r0 .r8 (o + 4 * j))) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, u'.gpr r = u.gpr r) ∧ Frame [⟨L.B + BitVec.ofNat 64 (24 + o), 72⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (24 + o)) (4 * k) = List.replicate (4 * k) 0
  | 0, _, u, hc, _ => WP.block_nil ⟨hc, fun _ => rfl, Frame.refl _ _, rfl⟩
  | k + 1, hk, u, hc, h0 => by
    have he := L.he
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zeros_ok hL ho₁ ho₂ k (by omega_arith) u hc h0) fun u₁ ⟨hc₁, hg₁, hf₁, hb₁⟩ => ?_
    refine wp_strS (a := L.B + BitVec.ofNat 64 (24 + (o + 4 * k))) (by omega_arith)
      (by rw [hc₁.r8]; exact hL.fpA (by omega_arith))
      (hc₁.inFrW (by omega_arith) (by omega_arith)) fun u₂ m₂ => WP.block_nil ?_
    have hm : u₂.mem = u₁.mem.writeW (L.B + BitVec.ofNat 64 (24 + (o + 4 * k))) (0 : BitVec 32) := by
      rw [m₂.mem, hg₁, h0]
    have hf : Frame [⟨L.B + BitVec.ofNat 64 (24 + (o + 4 * k)), 4⟩] u₁.mem u₂.mem := by
      rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    refine ⟨hc₁.keep hL m₂.rd m₂.wr m₂.sp (fun r _ => by rw [m₂.gpr]) hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega_arith) (by omega_arith)) m₂.syms,
      fun r => by rw [m₂.gpr, hg₁], hf₁.trans (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)⟩), ?_⟩
    rw [show 4 * (k + 1) = 4 * k + 4 by omega_arith, Proof.Hmac.Common.bytesAt_add, Offset.add_add,
      show 24 + o + 4 * k = 24 + (o + 4 * k) by omega_arith, hm, bytesAt_writeW_zero _ _ (Nat.le_refl _), ← hm,
      bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith), hb₁,
      List.replicate_append_replicate]

/-- Eighteen zero words at `r8 + o`. -/
theorem zero18_ok (hL : L.Ok) {o : Nat} (ho₁ : 216 ≤ o) (ho₂ : o + 72 ≤ 216 + 4 * L.e) {u : State}
    (hc : Ctx L g m₀ u) :
    WP isa (.block (Cfg.zero18 o)) u fun u' => Ctx L g m₀ u' ∧ (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧
      Frame [⟨L.B + BitVec.ofNat 64 (24 + o), 72⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (24 + o)) 72 = List.replicate 72 0 := by
  refine wp_movS (op2_imm (v := 0) (by decide)) fun u₁ v₁ => ?_
  refine WP.mono (zeros_ok hL ho₁ ho₂ 18 (Nat.le_refl _) u₁ (hc.upd v₁ (by decide)) v₁.gpr)
    fun u' ⟨hc', hg', hf', hb'⟩ => ⟨hc', fun r hr => by rw [hg', v₁.other _ hr], by rw [← v₁.mem]; exact hf', hb'⟩

/-! ## `h` and the digest for `core` -/

/-- `h`: `Q - D` zero bytes, then the digest (at `r6`), at `fX`. -/
theorem hPrep_ok (hL : L.Ok) (hLe : L.e = P.e) (hW : P.wide = true) (hdn : P.H.D ≤ dn) {t : State}
    (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).hPrep) t fun t' => Ctx L g m₀ t' ∧ (∀ r, r ≠ .r0 → t'.gpr r = t.gpr r) ∧
      Frame [⟨L.B + BitVec.ofNat 64 240, 72⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 240) P.Q =
        List.replicate (P.Q - P.H.D) 0 ++ Spec.Sha256.bytesAt t.mem (State.addr L.dg) P.H.D := by
  have he := e68 hLe hW
  have hQD : P.H.D < P.Q := by simpa [RfcHash.wide] using hW
  have := P.sizes; have := P.wsizes; have ng := hL.ng
  have e4 : 4 * (P.H.D / 4) = P.H.D := by anums
  rw [show (cfgOf P).hPrep = Cfg.zero18 fX ++ Cfg.copyN (P.H.D / 4) .r6 0 .r8 (216 + P.Q - P.H.D) from rfl,
    WP.block_append_iff]
  refine WP.mono (zero18_ok hL (o := fX) (by decide) (by rw [he]; decide) hc) fun u₁ ⟨hc₁, hg₁, hf₁, hb₁⟩ => ?_
  simp only [show 24 + fX = 240 from rfl] at hf₁ hb₁
  have hdg₁ : Spec.Sha256.bytesAt u₁.mem (State.addr L.dg) P.H.D = Spec.Sha256.bytesAt t.mem (State.addr L.dg) P.H.D :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_DG (by omega_arith)).symm.sub_left (Region.sub_prefix hdn)) (by anums)
  refine WP.mono (copyF_ok hL hc₁ (src := .r6) (S := L.dg) hc₁.r6 (by decide) (so := 0) (d := 216 + P.Q - P.H.D)
    (K := P.H.D / 4) (by omega_arith) (by rw [he]; anums) (by anums) (by omega_arith)
    (fun j hj => hc₁.inDg (by omega_arith) (by omega_arith))
    (by rw [BitVec.add_zero, e4]; exact (hL.stk_DG (by rw [he]; anums)).symm.sub_left (Region.sub_prefix hdn)))
    fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  have e₁ : 24 + (216 + P.Q - P.H.D) = 240 + (P.Q - P.H.D) := by omega_arith
  rw [e₁, BitVec.add_zero, e4, hdg₁] at hb₂
  rw [e₁, e4] at hf₂
  refine ⟨hc₂, fun r hr => (hg₂ r hr).trans (hg₁ r hr), hf₁.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _,
    by simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by anums)⟩), ?_⟩
  rw [show P.Q = (P.Q - P.H.D) + P.H.D by omega_arith, Proof.Hmac.Common.bytesAt_add, Offset.add_add,
    show P.Q - P.H.D + P.H.D - P.H.D = P.Q - P.H.D by omega_arith, hb₂,
    bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by anums)) (by omega_arith)]
  have := bytesAt_take u₁.mem (L.B + BitVec.ofNat 64 240) (n := P.Q - P.H.D) (k := 72) (by anums)
  rw [this, hb₁, List.take_replicate, Nat.min_eq_left (by anums)]

theorem shift_back (e sh : Nat) (hs : sh < 8) : (e * 2 ^ 8) >>> (8 - sh) = e * 2 ^ sh := by
  rw [Nat.shiftRight_eq_div_pow, show e * 2 ^ 8 = e * 2 ^ sh * 2 ^ (8 - sh) by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega_arith, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- If `sh ≠ 0`: the digest for `core`, the digest's number shifted left by
`sh` bits, in `Q` bytes at `fXc`. -/
theorem xPrep_ok (hL : L.Ok) (hLe : L.e = P.e) (hW : P.wide = true) (hdn : P.H.D ≤ dn) (hsh : P.R.sh ≠ 0)
    {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).xPrep) t fun t' => Ctx L g m₀ t' ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r10 → r ≠ .r12 → t'.gpr r = t.gpr r) ∧
      Frame [⟨State.addr L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 312, 72⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 312) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (State.addr L.dg) P.H.D) * 2 ^ P.R.sh) := by
  have he := e68 hLe hW
  have hS := curveW hsh
  have hQD : P.H.D < P.Q := by simpa [RfcHash.wide] using hW
  have hsl := P.R.nBits_len
  have hsh8 : P.R.sh < 8 := by omega_arith
  have hsc : (cfgOf P).sh = P.R.sh := rfl
  have := P.sizes; have := P.wsizes; have ng := hL.ng
  have e4 : 4 * (P.H.D / 4) = P.H.D := by anums
  rw [Cfg.xPrep, hsc, ite_eq_right_of_eq_false _ _ (eq_false hsh),
    show Cfg.copyN ((cfgOf P).D / 4) .r6 0 .r8 (fXc + (cfgOf P).len - (cfgOf P).D - 1) =
      Cfg.copyN (P.H.D / 4) .r6 0 .r8 (288 + P.Q - P.H.D - 1) from rfl, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zero18_ok hL (o := fXc) (by decide) (by rw [he]; decide) hc) fun u₁ ⟨hc₁, hg₁, hf₁, hb₁⟩ => ?_
  simp only [show 24 + fXc = 312 from rfl] at hf₁ hb₁
  have hdg₁ : Spec.Sha256.bytesAt u₁.mem (State.addr L.dg) P.H.D = Spec.Sha256.bytesAt t.mem (State.addr L.dg) P.H.D :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_DG (by omega_arith)).symm.sub_left (Region.sub_prefix hdn)) (by anums)
  refine WP.mono (copyF_ok hL hc₁ (src := .r6) (S := L.dg) hc₁.r6 (by decide) (so := 0)
    (d := 288 + P.Q - P.H.D - 1) (K := P.H.D / 4) (by omega_arith) (by rw [he]; anums) (by anums) (by omega_arith)
    (fun j hj => hc₁.inDg (by omega_arith) (by omega_arith))
    (by rw [BitVec.add_zero, e4]; exact (hL.stk_DG (by rw [he]; anums)).symm.sub_left (Region.sub_prefix hdn)))
    fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  have e₁ : 24 + (288 + P.Q - P.H.D - 1) = 312 + (P.Q - P.H.D - 1) := by omega_arith
  rw [e₁, BitVec.add_zero, e4, hdg₁] at hb₂
  rw [e₁, e4] at hf₂
  refine WP.mono (conv_ok hL hLe hS hW hc₂ (o := fXc) (s := 8 - P.R.sh) (by decide) (by decide) (by decide)
    (by omega_arith) (by omega_arith)) fun u₃ ⟨hc₃, hg₃, hf₃, hb₃⟩ => ?_
  simp only [show 24 + fXc = 312 from rfl] at hf₃ hb₃
  refine ⟨hc₃, fun r h0 h1 h2 h3 h10 h12 => by rw [hg₃ _ h1 h2 h3 h10 h12, hg₂ _ h0, hg₁ _ h0], ?_, ?_⟩
  · refine ((hf₁.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩).trans
      (hf₂.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩)).trans
      (hf₃.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact sub_refl _
    · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by anums)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., sub_refl _⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by anums)⟩
  · -- `Q - D - 1` zero bytes, the digest, and a zero byte, shifted right by `8 - sh` bits.
    have hY : Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 312) P.Q =
        List.replicate (P.Q - P.H.D - 1) 0 ++
          (Spec.Sha256.bytesAt t.mem (State.addr L.dg) P.H.D ++ List.replicate 1 0) := by
      have hz : ∀ a n, a + n ≤ 72 → Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (312 + a)) n =
          List.replicate n 0 := fun a n han => by
        have h1 := bytesAt_take u₁.mem (L.B + BitVec.ofNat 64 312) (n := a + n) (k := 72) (by omega_arith)
        rw [hb₁, List.take_replicate, Nat.min_eq_left (by omega_arith), Proof.Hmac.Common.bytesAt_add, Offset.add_add,
          ← List.replicate_append_replicate] at h1
        exact (List.append_inj h1 (by simp [Spec.Sha256.bytesAt])).2
      have e := Proof.Hmac.Common.bytesAt_add u₂.mem (L.B + BitVec.ofNat 64 312) (P.Q - P.H.D - 1) (P.H.D + 1)
      have e' := Proof.Hmac.Common.bytesAt_add u₂.mem (L.B + BitVec.ofNat 64 312 + BitVec.ofNat 64 (P.Q - P.H.D - 1))
        P.H.D 1
      rw [show P.Q - P.H.D - 1 + (P.H.D + 1) = P.Q by omega_arith] at e
      rw [Offset.add_add, Offset.add_add] at e'
      rw [Offset.add_add] at e
      have p₁ : Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 312) (P.Q - P.H.D - 1) =
          List.replicate (P.Q - P.H.D - 1) 0 := by
        rw [bytesAt_frame hf₂ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by anums)) (by omega_arith)]
        have := hz 0 (P.Q - P.H.D - 1) (by anums)
        rwa [Nat.add_zero] at this
      have p₃ : Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (312 + (P.Q - P.H.D - 1) + P.H.D)) 1 =
          List.replicate 1 0 := by
        rw [bytesAt_frame hf₂ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by anums)) (by omega_arith),
          show 312 + (P.Q - P.H.D - 1) + P.H.D = 312 + (P.Q - P.H.D - 1 + P.H.D) by omega_arith]
        exact hz (P.Q - P.H.D - 1 + P.H.D) 1 (by anums)
      rw [e, e', hb₂, p₁, p₃]
    rw [hb₃, hY, ofBytes_zeros, ofBytes_append_zeros, show 8 * 1 = 8 from rfl, shift_back _ _ hsh8]

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
    rw [genT_succ, List.length_append, genT_length P K k V]
    have := P.mac_length K (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H K k V).2
    simp only [RfcHash.mac] at this
    rw [this, Nat.succ_mul]

/-- What a candidate changes: `scratch`, the stack below the frame, `K` and
`V`, and `T` at the frame's top. -/
abbrev CWW {dn : Nat} (L : Lay dn) : List Region := [L.SCR, ⟨L.B, 152⟩, ⟨L.B + BitVec.ofNat 64 384, 128⟩]

theorem kvw_cww : ∀ r ∈ KVW L, ∃ r' ∈ CWW L, Region.Sub r r' := fun r hr => ⟨r, by
  simp only [CWW, KVW, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with h | h <;> simp [h], sub_refl _⟩

/-- The first `k` `V`s of the candidate: each `V = HMAC_K(V)`, copied to `T`
after the ones before. -/
theorem candW_ok (hL : L.Ok) (hLe : L.e = P.e) (hW : P.wide = true) (hT : TabL P L) :
    ∀ k, k * P.H.D ≤ 128 → ∀ {t : State}, Ctx L g m₀ t →
    WP isa ((cfgOf P).candW k) t fun u => Ctx L g m₀ u ∧ u.gpr .r9 = t.gpr .r9 ∧ Frame (CWW L) t.mem u.mem ∧
      kOf P L u.mem = kOf P L t.mem ∧
      vOfP P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kOf P L t.mem) k (vOfP P L t.mem)).2 ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 384) (k * P.H.D) =
        (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kOf P L t.mem) k (vOfP P L t.mem)).1
  | 0, _, t, hc => WP.block_nil ⟨hc, rfl, Frame.refl _ _, rfl, rfl, by simp [Spec.Ecdsa.Rfc6979.genT,
      Spec.Sha256.bytesAt]⟩
  | k + 1, hk, t, hc => by
    have he := e68 hLe hW
    have hk' : k * P.H.D + P.H.D ≤ 128 := by rw [Nat.succ_mul] at hk; exact hk
    have := P.sizes
    have e4 : 4 * (P.H.D / 4) = P.H.D := by anums
    rw [Cfg.candW]
    refine WP.seq (WP.mono (candW_ok hL hLe hW hT k (by omega_arith) hc) fun u₁ ⟨hc₁, h9₁, hf₁, hk₁, hv₁, hb₁⟩ => ?_)
    refine WP.seq (WP.mono (hmacV_ok hL hT hc₁) fun u₂ ⟨hc₂, h9₂, hf₂, hk₂, hv₂⟩ => ?_)
    have hfp := fp_toNat' hL; have := L.sp.isLt; have nB := hL.nB
    have hD64 : P.H.D ≤ 64 := by anums
    have hsep : Region.Disjoint ⟨State.addr L.fp + BitVec.ofNat 64 fV, 4 * (P.H.D / 4)⟩
        ⟨L.B + BitVec.ofNat 64 (24 + (360 + k * P.H.D)), 4 * (P.H.D / 4)⟩ := by
      rw [fpd hL, e4]
      exact Offset.disjoint _ (by unfold fV; omega_arith) (by unfold fV; omega_arith) (by omega_arith)
    refine WP.mono (copyF_ok hL hc₂ (src := .r8) (S := L.fp) hc₂.r8 (by decide) (so := fV)
      (d := 360 + k * P.H.D) (K := P.H.D / 4) (by omega_arith) (by rw [he]; omega_arith) (by simp only [fV]; omega_arith) (by simp only [fV]; omega_arith)
      (fun j hj => by
        rw [fpd hL]
        have : j < P.H.D / 4 := hj
        exact hc₂.inFr (by unfold fV; omega_arith) (by unfold fV; omega_arith))
      hsep)
      fun u₃ ⟨hc₃, hg₃, hf₃, hb₃⟩ => ?_
    have e₁ : 24 + (360 + k * P.H.D) = 384 + k * P.H.D := by omega_arith
    rw [e₁, e4] at hf₃ hb₃
    rw [fpd hL, show 24 + fV = 88 from rfl] at hb₃
    -- What the copy keeps: `K`, `V` and `scratch`.
    have dKV : ∀ {o : Nat}, 24 ≤ o → o + P.H.D ≤ 152 →
        Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 o) P.H.D =
          Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 o) P.H.D :=
      fun h₁ h₂ => bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)
    have hk₃ : kOf P L u₃.mem = kOf P L u₂.mem := dKV (by decide) (by anums)
    have hv₃ : vOfP P L u₃.mem = vOfP P L u₂.mem := dKV (by decide) (by anums)
    refine ⟨hc₃, by rw [hg₃ _ (by decide), h9₂, h9₁], ?_, ?_, ?_, ?_⟩
    · refine ((hf₁.trans (hf₂.sub kvw_cww)).trans (hf₃.sub fun r hr => ?_))
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B + BitVec.ofNat 64 384, 128⟩, by simp [CWW], Offset.sub _ (by omega_arith) (by omega_arith)⟩
    · rw [hk₃, hk₂, hk₁]
    · rw [hv₃, hv₂, genT_succ, hk₁, hv₁]
    · rw [genT_succ, Nat.succ_mul, Proof.Hmac.Common.bytesAt_add, Offset.add_add, hb₃, ← hb₁,
        show Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 88) P.H.D = vOfP P L u₂.mem from rfl, hv₂, hk₁, hv₁]
      congr 1
      · -- `T`'s first `k` `V`s, kept by the HMAC and the copy.
        rw [bytesAt_frame hf₃ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)]
        exact bytesAt_frame hf₂ (fun r hr => by
          simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hL.stk_SCR (by rw [he]; omega_arith)
          · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)) (by omega_arith)

/-- If `sh ≠ 0`: `T`'s first `Q` bytes shifted right by `sh` bits. -/
theorem candTop_ok (hL : L.Ok) (hLe : L.e = P.e) (hW : P.wide = true) (hsh : P.R.sh ≠ 0) {t : State}
    (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).candTop) t fun u => Ctx L g m₀ u ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r10 → r ≠ .r12 → u.gpr r = t.gpr r) ∧
      Frame [⟨State.addr L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 384, P.Q⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 384) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 384) P.Q) >>> P.R.sh) := by
  have hsl := P.R.nBits_len
  have hsc : (cfgOf P).sh = P.R.sh := rfl
  rw [Cfg.candTop, hsc, ite_eq_right_of_eq_false _ _ (eq_false hsh)]
  refine WP.mono (conv_ok hL hLe (curveW hsh) hW hc (o := fT) (s := P.R.sh) (by decide) (by decide) (by decide)
    (by omega_arith) (by omega_arith)) fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  simp only [show 24 + fT = 384 from rfl] at hf₂ hb₂
  exact ⟨hc₂, hg₂, hf₂, hb₂⟩


end VG.Proof.Ecdsa.Rfc6979.Arm
