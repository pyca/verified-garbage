module
-- separate module: its proofs (the buffers X and h) build in parallel with `Steps`, which `Cand` also imports

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Steps
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Copy
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Ecdsa.Rfc6979.X86.Wide`, which only this module used -/

section

/-!
# Deterministic ECDSA on x86 (32-bit): scalars longer than the hash

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Wide.lean`), for P-521 (`big`),
whose scalars are longer than any digest and whose `n` has fewer bits than
them: the `Q` bytes at an offset above `B` in the frame, shifted right in
place through the words at `scratch + 2560` (`conv_ok`, by `loadBytes_ok`,
`shrWords_ok` and `storeBytes_ok`), as for the candidate `T`'s first `Q`
bytes (`candTop_ok`); zero words above `B` (`zero18_ok`); and `genT` with
one more `V` (`genT_succ`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.Mont (wordsVal Outside off ofs)
open VG.Proof.Mont.X86 (Scr Keeps)
open VG.Proof.Weierstrass.X86 (loadBytes_ok shrWords_ok storeBytes_ok)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

theorem frame_of_outside {base : Addr} {d n : Nat} {m m' : Mem} (h : Outside base d n m m')
    (hn : d + n ≤ 2 ^ 64) : Frame [⟨base + BitVec.ofNat 64 d, n⟩] m m' := fun x hx => h x (by
  have h₁ := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at h₁
  have h₂ := Offset.lt_iff x base hn
  simp only [ofs]
  omega_arith)

theorem scr_of (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .edi = L.sc) : Scr t L.scr 8192 := by
  have hn : L.scr.toNat + 8192 ≤ 2 ^ 32 := by
    have := hL.nc; have := L.sc.isLt
    simp only [Lay.scr, BitVec.toNat_setWidth]; omega_arith
  have hF : 20 ≤ L.F.toNat := by have := hL.FN; have := hL.e588; omega_arith
  -- The calls' 20 bytes below `F` are in the stack the contract gives.
  have hd : Region.Disjoint ⟨L.F.setWidth 64 - BitVec.ofNat 64 20, 20⟩ ⟨L.scr, 8192⟩ := by
    rw [hL.F64, Offset.add_ofNat_sub _ (by decide)]
    exact hL.stk_scr0 (by omega_arith) (Nat.le_refl _)
  refine ⟨by rw [hdi], by rw [hc.wr]; simp, hn, ?_⟩
  rw [hc.esp]
  exact VG.Proof.Weierstrass.X86.stkOk_of (Nat.le_refl _) hF hn (by decide) hd

theorem scr_keep {s s' : State} {base : Addr} {size : Nat} (h : Scr s base size) (hdi : s'.gpr .edi = s.gpr .edi)
    (hsp : s'.gpr .esp = s.gpr .esp) (hwr : s'.wr = s.wr) : Scr s' base size :=
  h.of_eq hdi hsp hwr

/-- `conv o s`: the `Q` bytes at `esp + o`, in the frame's top words,
shifted right by `s` bits in place, through the words at `scratch + 2560`. -/
theorem conv_ok (hL : L.Ok) (hW : P.R.big = true) {t : State} (hc : Ctx L g m₀ t)
    (hdi : t.gpr .edi = L.sc) {o s : Nat} (ho₁ : 152 ≤ o) (ho₂ : o + 72 ≤ 512) (hs₁ : 1 ≤ s) (hs₂ : s < 32) :
    WP isa (.block ((cfgOf P).conv o s)) t fun t' => Ctx L g m₀ t' ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → t'.gpr r = t.gpr r) ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (76 + o), P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (76 + o)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (76 + o)) P.Q) >>> s) := by
  obtain ⟨hw9, -, hQ66, -⟩ := P.sizesW hW
  have nB := hL.nB
  have hFN := hL.FN
  have e588 := hL.e588
  have e28 := hL.e28
  have hw2 : (cfgOf P).w / 2 = P.w := by simp only [cfgOf, show P.R.E.C.len = 66 from hQ66, show P.w = 9 from hw9]; decide
  refine WP.of_syms ?_
  rw [Cfg.conv, hw2, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .esi) (by decide) o) fun u₁ h₁ => ?_
  have hS₁ : Scr u₁ L.scr 8192 := scr_keep (scr_of hL hc hdi) (h₁.keep _ (by decide))
    (h₁.keep _ (by decide)) (by rw [h₁.ctx.wr, hc.wr])
  have hsi₁ : u₁.gpr .esi = L.F + BitVec.ofNat 32 o := h₁.val
  have ha₁ : (L.F + BitVec.ofNat 32 o).setWidth 64 = L.B + BitVec.ofNat 64 (76 + o) := hL.addrF (by omega_arith)
  refine WP.mono (loadBytes_ok hS₁ (len := P.Q) (n := P.w) (o := 2560) (src := .esi) (by decide) (by omega_arith)
    (by rw [hsi₁, hL.frN (by omega_arith)]; omega_arith) (by omega_arith) (by omega_arith)
    (fun d hd => by rw [hsi₁, ha₁, Offset.add_add]; exact h₁.ctx.inFr (by omega_arith) (by omega_arith) hL)
    (by rw [hsi₁, ha₁]; exact hL.stk_scr (by omega_arith) (by omega_arith))) fun u₂ ⟨hv₂, k₂, O₂⟩ => ?_
  refine WP.mono (shrWords_ok (scr_keep hS₁ (k₂.1 _ (by decide)) (k₂.1 _ (by decide)) k₂.2.2) (n := P.w) (o := 2560) (sh := s)
    (by omega_arith) hs₁ hs₂) fun u₃ ⟨hv₃, k₃, O₃⟩ => ?_
  refine wp_movi fun u₄ v₄ => WP.block_nil ?_
  have hsp₄ : u₄.gpr .esp = L.F := by
    rw [v₄.other _ (by decide), k₃.1 _ (by decide), k₂.1 _ (by decide), h₁.keep _ (by decide), hc.esp]
  have hwr₄ : u₄.wr = t.wr := by rw [v₄.wr, k₃.2.2, k₂.2.2, h₁.ctx.wr, hc.wr]
  have hS₄ : Scr u₄ L.scr 8192 := scr_keep hS₁ (by rw [v₄.other _ (by decide), k₃.1 _ (by decide),
    k₂.1 _ (by decide)]) (by rw [v₄.other _ (by decide), k₃.1 _ (by decide), k₂.1 _ (by decide)])
    (by rw [v₄.wr, k₃.2.2, k₂.2.2])
  have hdst : (u₄.gpr .esp).setWidth 64 + BitVec.ofNat 64 o = L.B + BitVec.ofNat 64 (76 + o) := by
    rw [hsp₄, hL.F64, Offset.add_add]
  refine WP.mono (storeBytes_ok hS₄ (len := P.Q) (n := P.w) (d := o) (a := 2560) (dst := .esp) (by decide)
    (by decide) true (by rw [v₄.gpr]; rfl) (by omega_arith) (by omega_arith) (by omega_arith) (by rw [hsp₄, hFN]; omega_arith)
    (fun e m hem => by rw [hdst, Offset.add_add, hwr₄]; exact hc.inFrW (by omega_arith) (by omega_arith) hL)
    (by rw [hdst]; exact (hL.stk_scr (by omega_arith) (by omega_arith)).symm)) fun u₅ ⟨hb₅, k₅, O₅⟩ => ?_
  intro hsy
  rw [hdst] at hb₅ O₅
  -- What changed: the words at `scratch + 2560`, and the bytes converted.
  have hf : Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (76 + o), P.Q⟩] t.mem u₅.mem := by
    have f₂ := frame_of_outside (O₂.trans O₃) (by omega_arith)
    have f₅ := frame_of_outside O₅ (by omega_arith)
    rw [BitVec.add_zero, v₄.mem] at f₅
    rw [h₁.mem, show 8 * P.w = 72 by omega_arith] at f₂
    exact (f₂.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩).trans (f₅.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩)
  have hg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → u₅.gpr r = t.gpr r := fun r h₁' h₂ h₃ h₄ => by
    rw [k₅.1 _ (by simp [h₁', h₃]), v₄.other _ h₂, k₃.1 _ (by simp [h₁', h₃]), k₂.1 _ (by simp [h₁']),
      h₁.keep _ h₄]
  refine ⟨hc.keep (hsy := hsy) hL (by rw [k₅.2.1, v₄.rd, k₃.2.1, k₂.2.1, h₁.ctx.rd, hc.rd]) (by rw [k₅.2.2, hwr₄])
      (hg _ (by decide) (by decide) (by decide) (by decide)) hf fun r hr => ?_, hg, hf, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact safe_scr L (by omega_arith)
    · exact safe_high L (by omega_arith) (by omega_arith)
  · rw [ecdsa_bytesAt] at hb₅
    simp only [ite_true] at hb₅
    rw [hb₅, v₄.mem, hv₃, hv₂, hsi₁, ha₁, ecdsa_bytesAt, h₁.mem]

/-- The bytes of a zero word. -/
theorem bytesAt_writeW_zero (m : Mem) (p : Addr) {k : Nat} (hk : k ≤ 4) :
    Spec.Sha256.bytesAt (m.writeW p (0 : BitVec 32)) p k = List.replicate k 0 := by
  rw [List.eq_replicate_iff]
  refine ⟨by simp [Spec.Sha256.bytesAt], fun b hb => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  have hi := List.mem_range.mp hi
  have e : (p + BitVec.ofNat 64 i - p).toNat = i := by
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  simp only [Mem.writeW, Mem.write, e, show i < 32 / 8 by omega_arith, ite_true]
  apply BitVec.eq_of_toNat_eq; simp


/-- A zero word at `esp + o`, in the frame's top words. -/
theorem zeroF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hax : u.gpr .eax = 0) {o : Nat} (ho₁ : 152 ≤ o)
    (ho₂ : o + 4 ≤ 512) :
    WP isa (.block [.store (stk o) .eax]) u fun u' => Ctx L g m₀ u' ∧ u'.gpr = u.gpr ∧
      Frame [⟨L.B + BitVec.ofNat 64 (76 + o), 4⟩] u.mem u'.mem ∧
      ∀ k ≤ 4, Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (76 + o)) k = List.replicate k 0 := by
  have nB := hL.nB
  have ea : addr L.F o = L.B + BitVec.ofNat 64 (76 + o) := hL.addrF (by omega_arith)
  refine wp_stm (B := L.F) hc.esp (by rw [ea]; exact hc.inFrW (by omega_arith) (by omega_arith) hL)
    fun u₂ v₂ => WP.block_nil ?_
  have hm : u₂.mem = u.mem.writeW (L.B + BitVec.ofNat 64 (76 + o)) (0 : BitVec 32) := by
    rw [v₂.mem, hax, ea]
  have hf : Frame [⟨L.B + BitVec.ofNat 64 (76 + o), 4⟩] u.mem u₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.keep (hsy := v₂.syms) hL v₂.rd v₂.wr (by rw [v₂.gpr]) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega_arith) (by omega_arith)),
    v₂.gpr, hf, fun k hk => by rw [hm]; exact bytesAt_writeW_zero _ _ hk⟩

/-- `k` zero words at `esp + o`, above `B`, with `eax = 0`. -/
theorem zeroK_ok (hL : L.Ok) {o : Nat} (ho₁ : 152 ≤ o) (ho₂ : o + 72 ≤ 512) :
    ∀ k ≤ 18, ∀ {u : State}, Ctx L g m₀ u → u.gpr .eax = 0 →
    WP isa (.block ((List.range k).map fun j => .store (stk (o + 4 * j)) .eax)) u
      fun u' => Ctx L g m₀ u' ∧ u'.gpr = u.gpr ∧
        Frame [⟨L.B + BitVec.ofNat 64 (76 + o), 72⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (76 + o)) (4 * k) = List.replicate (4 * k) 0
  | 0, _, u, hc, _ => WP.of_runBlock ⟨u, rfl, hc, rfl, Frame.refl _ _, rfl⟩
  | k + 1, hk, u, hc, hax => by
    have := hL.nB
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zeroK_ok hL ho₁ ho₂ k (by omega_using [hk]) hc hax) fun u₁ ⟨hc₁, hg₁, hf₁, hb₁⟩ => ?_
    refine WP.mono (zeroF_ok hL hc₁ (by rw [hg₁, hax]) (o := o + 4 * k) (by omega_using [ho₁]) (by omega_using [ho₂, hk]))
      fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
    refine ⟨hc₂, hg₂.trans hg₁, hf₁.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _,
      by simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_using []) (by omega_using [hk])⟩), ?_⟩
    rw [show 4 * (k + 1) = 4 * k + 4 by omega_using [], Proof.Hmac.Common.bytesAt_add, Offset.add_add,
      show 76 + o + 4 * k = 76 + (o + 4 * k) by omega_using [], hb₂ 4 (Nat.le_refl _),
      bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_using []) (by omega_using [ho₂, hk]) (by omega_using [ho₂, hk])) (by omega_using [hk]), hb₁, List.replicate_append_replicate]

/-- Eighteen zero words at `esp + o`, above `B`. -/
theorem zero18_ok (hL : L.Ok) {o : Nat} (ho₁ : 152 ≤ o) (ho₂ : o + 72 ≤ 512) {u : State} (hc : Ctx L g m₀ u) :
    WP isa (.block (Cfg.zero18 o)) u fun u' => Ctx L g m₀ u' ∧ (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧
      Frame [⟨L.B + BitVec.ofNat 64 (76 + o), 72⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (76 + o)) 72 = List.replicate 72 0 := by
  rw [Cfg.zero18, WP.block_append_iff]
  refine WP.mono (movi_ok hL hc (d := .eax) (by decide) 0) fun u₁ h₁ => ?_
  refine WP.mono (zeroK_ok hL ho₁ ho₂ 18 (Nat.le_refl _) h₁.ctx h₁.val) fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ =>
    ⟨hc₂, fun r hr => by rw [hg₂, h₁.keep r hr], h₁.mem ▸ hf₂, hb₂⟩

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
    (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H K k V).1.length = k * P.F.H.D
  | 0, V => by simp [Spec.Ecdsa.Rfc6979.genT]
  | k + 1, V => by
    rw [genT_succ, List.length_append, genT_length P K k V, mac_length]
    rw [Nat.succ_mul]

/-- `scratch` in `edi`. -/
theorem scrPtr_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.scrPtr) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .edi = L.sc ∧
      ∀ r, r ≠ .edi → u.gpr r = t.gpr r :=
  WP.mono (arg_ok hL hc (d := .edi) (by decide) (i := 4) (by decide)) fun u h => ⟨h.ctx, h.mem, h.val, h.keep⟩

/-- If `big`: `T`'s first `Q` bytes shifted right by `sh` bits. -/
theorem candTop_ok (hL : L.Ok) (hW : P.R.big = true) (hsh : P.R.sh ≠ 0) (hsh8 : P.R.sh < 8) {t : State}
    (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).candTop t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (76 + fT), P.Q⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (76 + fT)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (76 + fT)) P.Q) >>> P.R.sh) := by
  have hsc : (cfgOf P).sh = P.R.sh := rfl
  have hbc : (cfgOf P).big = true := hW
  rw [Cfg.candTop, hbc, ite_eq_left_of_eq_true _ _ (eq_self true), hsc]
  refine WP.seq (WP.mono (scrPtr_ok hL hc) fun u₁ ⟨hc₁, hm₁, hdi₁, _⟩ => ?_)
  refine WP.mono (conv_ok hL hW hc₁ hdi₁ (o := fT) (s := P.R.sh) (by decide) (by decide) (by omega_using [hsh]) (by omega_using [hsh8]))
    fun u₂ ⟨hc₂, _, hf₂, hb₂⟩ => ?_
  rw [hm₁] at hf₂ hb₂
  exact ⟨hc₂, hf₂, hb₂⟩

end VG.Proof.Ecdsa.Rfc6979.X86

end

end


/-!
# Deterministic ECDSA on x86 (32-bit): the digest into `X`

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Prep.lean`): `X` (`prepX_ok`):
`Q - m` zero bytes, then the digest's first `m = min(D, Q)`, its length the
smaller of the frame's `D` and `Q` (`min_ok`, by the borrow of `D - Q`, a
mask), copied by the byte loop (`cpLoop_ok`); and, if `big`, the digest for
`core`, the digest's number shifted left by `sh` bits (`prepC_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.Rfc6979.X86

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## `X` -/

theorem min_mask {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b &&&
        (if decide ((BitVec.ofNat 32 a).toNat < (BitVec.ofNat 32 b).toNat) then BitVec.allOnes 32 else 0)) +
      BitVec.ofNat 32 b = BitVec.ofNat 32 (min a b) := by
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases h : a < b
  · simp only [h, decide_true, ite_true, BitVec.and_allOnes, BitVec.sub_add_cancel, Nat.min_eq_left (Nat.le_of_lt h)]
  · rw [ite_eq_right_iff.mpr (fun h' => absurd (of_decide_eq_true h') h), Nat.min_eq_right (Nat.le_of_not_lt h)]
    simp

/-- `sub ecx, Q; sbb edx, edx; and ecx, edx; add ecx, Q`: the smaller of
`ecx` and `Q` in `ecx`. -/
theorem min_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (hcx : u.gpr .ecx = BitVec.ofNat 32 a) :
    WP isa (.block [.alu .sub .ecx (.imm (BitVec.ofNat 32 b)), .alu .sbb .edx (.reg .edx),
      .alu .and .ecx (.reg .edx), .alu .add .ecx (.imm (BitVec.ofNat 32 b))]) u fun u' => Ctx L g m₀ u' ∧
      u'.mem = u.mem ∧ u'.gpr .ecx = BitVec.ofNat 32 (min a b) ∧
      ∀ r, r ≠ .ecx → r ≠ .edx → u'.gpr r = u.gpr r := by
  refine wp_subi fun u₁ v₁ hc₁ _ => wp_sbb_self hc₁ fun u₂ v₂ => wp_and fun u₃ v₃ => wp_addi fun u₄ v₄ =>
    WP.block_nil ⟨?_, by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem], ?_, fun r h₁ h₂ => ?_⟩
  · exact hc.regs hL (by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd]) (by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr])
      (by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem])
      (by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide)])
      (by rw [v₄.syms, v₃.syms, v₂.syms, v₁.syms])
  · rw [v₄.gpr, v₃.gpr, v₂.gpr, v₂.other .ecx (by decide), v₁.gpr, hcx]
    exact min_mask ha hb
  · rw [v₄.other _ h₁, v₃.other _ h₁, v₂.other _ h₂, v₁.other _ h₁]

/-- `ebx = esp + o - ecx`, and the digest in `esi`. -/
theorem xTail_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (o : Nat) :
    WP isa (.block [.mov .ebx (.reg .esp), .alu .add .ebx (.imm (BitVec.ofNat 32 o)), .alu .sub .ebx (.reg .ecx),
      .mov .esi (argM 2)]) u fun u' => Ctx L g m₀ u' ∧ u'.mem = u.mem ∧
      u'.gpr .ebx = L.F + BitVec.ofNat 32 o - u.gpr .ecx ∧ u'.gpr .esi = L.a2 ∧
      ∀ r, r ≠ .ebx → r ≠ .esi → u'.gpr r = u.gpr r := by
  refine wp_mov fun u₁ v₁ => wp_addi fun u₂ v₂ => wp_sub fun u₃ v₃ _ => ?_
  have c₃ : Ctx L g m₀ u₃ := hc.regs hL (by rw [v₃.rd, v₂.rd, v₁.rd]) (by rw [v₃.wr, v₂.wr, v₁.wr])
    (by rw [v₃.mem, v₂.mem, v₁.mem]) (by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide)])
    (by rw [v₃.syms, v₂.syms, v₁.syms])
  refine WP.mono (arg_ok hL c₃ (d := .esi) (by decide) (i := 2) (by decide)) fun u₄ h₄ =>
    ⟨h₄.ctx, by rw [h₄.mem, v₃.mem, v₂.mem, v₁.mem], ?_, h₄.val, fun r h₁ h₂ => ?_⟩
  · rw [h₄.keep _ (by decide), v₃.gpr, v₂.gpr, v₂.other .ecx (by decide), v₁.gpr, v₁.other .ecx (by decide),
      hc.esp]
  · rw [h₄.keep _ h₂, v₃.other _ h₁, v₂.other _ h₁, v₁.other _ h₁]

theorem sub_min32 (F : BitVec 32) {a b c : Nat} (h : c ≤ b) :
    F + BitVec.ofNat 32 (a + b) - BitVec.ofNat 32 c = F + BitVec.ofNat 32 (a + (b - c)) := by
  rw [show a + b = a + (b - c) + c by omega_using [h], ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- The arguments of `X`'s copy: `X` cleared, `ecx = m = min(D, Q)`, the
digest in `esi`, `X + Q - m` in `ebx`. -/
theorem xArgs_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).xArgs) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 (76 + fX), 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (76 + fX)) 72 = List.replicate 72 0 ∧
      u.gpr .ecx = BitVec.ofNat 32 (min P.F.H.D P.Q) ∧
      u.gpr .ebx = L.F + BitVec.ofNat 32 (fX + (P.Q - min P.F.H.D P.Q)) ∧ u.gpr .esi = L.a2 := by
  obtain ⟨-, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  have hlen : (cfgOf P).len = P.Q := rfl
  rw [Cfg.xArgs, WP.block_append_iff]
  refine WP.mono (zero18_ok hL (o := fX) (by decide) (by decide) hc) fun u₁ ⟨hc₁, _, hf₁, hb₁⟩ => ?_
  rw [hlen, show ([.mov .ecx (.mem (stk fDl)), .alu .sub .ecx (.imm (BitVec.ofNat 32 P.Q)),
      .alu .sbb .edx (.reg .edx), .alu .and .ecx (.reg .edx), .alu .add .ecx (.imm (BitVec.ofNat 32 P.Q)),
      .mov .ebx (.reg .esp), .alu .add .ebx (.imm (BitVec.ofNat 32 (fX + P.Q))), .alu .sub .ebx (.reg .ecx),
      .mov .esi (argM 2)] : List Instr) =
    [.mov .ecx (.mem (stk fDl))] ++ [.alu .sub .ecx (.imm (BitVec.ofNat 32 P.Q)),
      .alu .sbb .edx (.reg .edx), .alu .and .ecx (.reg .edx), .alu .add .ecx (.imm (BitVec.ofNat 32 P.Q))] ++
      [.mov .ebx (.reg .esp), .alu .add .ebx (.imm (BitVec.ofNat 32 (fX + P.Q))), .alu .sub .ebx (.reg .ecx),
        .mov .esi (argM 2)] from rfl, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ldF_ok hL hc₁ (d := .ecx) (by decide) (o := fDl) (by decide)) fun u₂ h₂ => ?_
  have hcx₂ : u₂.gpr .ecx = BitVec.ofNat 32 P.F.H.D := by rw [h₂.val, hc₁.dl hT]
  refine WP.mono (min_ok hL h₂.ctx (a := P.F.H.D) (b := P.Q) (by omega_using [hD64]) (by omega_using [hQ66]) hcx₂)
    fun u₃ ⟨hc₃, hm₃, hcx₃, _⟩ => ?_
  refine WP.mono (xTail_ok hL hc₃ (fX + P.Q)) fun u₄ ⟨hc₄, hm₄, hbx₄, hsi₄, hg₄⟩ => ?_
  have hm : min P.F.H.D P.Q ≤ P.Q := Nat.min_le_right _ _
  rw [hcx₃, sub_min32 _ hm] at hbx₄
  have hmm : u₄.mem = u₁.mem := by rw [hm₄, hm₃, h₂.mem]
  exact ⟨hc₄, hmm ▸ hf₁, hmm ▸ hb₁, by rw [hg₄ _ (by decide) (by decide), hcx₃], hbx₄, hsi₄⟩

/-- `X`, the `Q` bytes at `fX`: `Q - m` zero bytes, then the digest's first
`m = min(D, Q)`. -/
theorem prepX_ok (hL : L.Ok) (hT : TabL P L) (hdn : P.F.H.D ≤ dn) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).prepX t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 (76 + fX), 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (76 + fX)) P.Q =
        List.replicate (P.Q - min P.F.H.D P.Q) 0 ++ Spec.Sha256.bytesAt t.mem L.dg (min P.F.H.D P.Q) := by
  have hnb := hL.nB
  have ng := hL.ng
  obtain ⟨-, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  rw [Cfg.prepX]
  refine WP.seq (WP.mono (xArgs_ok hL hT hc) fun u₅ ⟨hc₅, hf₁, hb₁, hcx₅, hbx₅, hsi₅⟩ => ?_)
  have hm : min P.F.H.D P.Q ≤ P.Q := Nat.min_le_right _ _
  have hm8 : 8 ≤ min P.F.H.D P.Q := by omega_using [hD16, hQ8]
  have hdn' : min P.F.H.D P.Q ≤ dn := by omega_using [hdn]
  have ea : (L.F + BitVec.ofNat 32 (fX + (P.Q - min P.F.H.D P.Q))).setWidth 64 =
      L.B + BitVec.ofNat 64 (76 + fX + (P.Q - min P.F.H.D P.Q)) := by
    rw [hL.frv (by simp only [fX]; omega_using [hQ66]), Nat.add_assoc]
  have sepD : Region.Disjoint ⟨L.a2.setWidth 64, min P.F.H.D P.Q⟩
      ⟨L.B + BitVec.ofNat 64 (76 + fX + (P.Q - min P.F.H.D P.Q)), min P.F.H.D P.Q⟩ :=
    ((hL.kg.sub_left (Offset.sub_base _ (by simp only [fX]; omega_using [hQ66]))).symm.sub_left (Region.sub_prefix hdn'))
  refine WP.mono (cpLoop_ok hL hc₅ (S := L.a2) (D := L.F + BitVec.ofNat 32 (fX + (P.Q - min P.F.H.D P.Q)))
      (n := min P.F.H.D P.Q) (by omega_using [hD16, hQ8]) (by omega_using [hD64]) (by omega_using [hdn, ng])
      (by rw [hL.frN (by simp only [fX]; omega_using [hQ66])]; have := hL.e28; have := hL.e588; simp only [fX]; omega_using [hQ66])
      (by have := hc₅.inDg (o := 0) (n := min P.F.H.D P.Q) (by omega_using [hdn]) (by omega_using []); rwa [BitVec.add_zero] at this)
      (by rw [ea]; exact hc₅.inFrW (by omega_using []) (by simp only [fX]; omega_using [hQ66]) hL)
      (by rw [ea]; exact sepD)
      (by rw [ea]; exact safe_high L (by simp only [fX]; omega_using []) (by simp only [fX]; omega_using [hQ66]))
      hsi₅ hbx₅ hcx₅) fun u ⟨hc', hf, hb, _⟩ => ?_
  rw [ea] at hf hb
  have hdg : Spec.Sha256.bytesAt u₅.mem L.dg (min P.F.H.D P.Q) = Spec.Sha256.bytesAt t.mem L.dg (min P.F.H.D P.Q) :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact fun a h₁ h₂ => hL.kg a (Offset.sub_base L.B (d := 76 + fX) (n := 72) (k := 588)
        (by simp only [fX]; omega_using []) a h₂) (Region.sub_prefix hdn' a h₁)) (by omega_using [hD64])
  refine ⟨hc', hf₁.trans ?_, ?_⟩
  · exact hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_using []) (by simp only [fX]; omega_using [hQ66])⟩
  · rw [show P.Q = (P.Q - min P.F.H.D P.Q) + min P.F.H.D P.Q by omega_using [], Proof.Hmac.Common.bytesAt_add,
      Offset.add_add, hb, ← show P.Q = (P.Q - min P.F.H.D P.Q) + min P.F.H.D P.Q by omega_using [],
      bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by omega_using [])) (by simp only [fX]; omega_using [hQ66]) (by simp only [fX]; omega_using [hQ66])) (by omega_using [hQ66]),
      hdg]
    rw [bytesAt_take _ _ (k := 72) (by omega_using [hQ66]), hb₁, List.take_replicate, Nat.min_eq_left (by omega_using [hQ66])]

/-! ## P-521's digest for `core` -/

theorem shift_back (e sh : Nat) (hs : sh < 8) : (e * 2 ^ 8) >>> (8 - sh) = e * 2 ^ sh := by
  rw [Nat.shiftRight_eq_div_pow, show e * 2 ^ 8 = e * 2 ^ sh * 2 ^ (8 - sh) by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega_using [hs], Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- The arguments of the copy of `core`'s digest, if `big`: it cleared,
`ecx = D`, the digest in `esi`, `Xc + Q - 1 - D` in `ebx`. -/
theorem xcArgs_ok (hL : L.Ok) (hT : TabL P L) (hW : P.R.big = true) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).xcArgs) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 (76 + fXc), 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (76 + fXc)) 72 = List.replicate 72 0 ∧
      u.gpr .ecx = BitVec.ofNat 32 P.F.H.D ∧
      u.gpr .ebx = L.F + BitVec.ofNat 32 (fXc + (P.Q - 1 - P.F.H.D)) ∧ u.gpr .esi = L.a2 := by
  obtain ⟨-, -, hQ66, hQD⟩ := P.sizesW hW
  obtain ⟨-, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  have hlen : (cfgOf P).len = P.Q := rfl
  rw [Cfg.xcArgs, WP.block_append_iff]
  refine WP.mono (zero18_ok hL (o := fXc) (by decide) (by decide) hc) fun u₁ ⟨hc₁, _, hf₁, hb₁⟩ => ?_
  rw [hlen, show ([.mov .ecx (.mem (stk fDl)), .mov .ebx (.reg .esp),
      .alu .add .ebx (.imm (BitVec.ofNat 32 (fXc + P.Q - 1))), .alu .sub .ebx (.reg .ecx),
      .mov .esi (argM 2)] : List Instr) =
    [.mov .ecx (.mem (stk fDl))] ++ [.mov .ebx (.reg .esp), .alu .add .ebx (.imm (BitVec.ofNat 32 (fXc + P.Q - 1))),
        .alu .sub .ebx (.reg .ecx), .mov .esi (argM 2)] from rfl, WP.block_append_iff]
  refine WP.mono (ldF_ok hL hc₁ (d := .ecx) (by decide) (o := fDl) (by decide)) fun u₂ h₂ => ?_
  have hcx₂ : u₂.gpr .ecx = BitVec.ofNat 32 P.F.H.D := by rw [h₂.val, hc₁.dl hT]
  refine WP.mono (xTail_ok hL h₂.ctx (fXc + P.Q - 1)) fun u₃ ⟨hc₃, hm₃, hbx₃, hsi₃, hg₃⟩ => ?_
  rw [hcx₂, show fXc + P.Q - 1 = fXc + (P.Q - 1) by simp only [fXc]; omega_using [hQ66], sub_min32 _ (by omega_using [hQD]),
    show fXc + (P.Q - 1 - P.F.H.D) = fXc + (P.Q - 1 - P.F.H.D) from rfl] at hbx₃
  have hmm : u₃.mem = u₁.mem := by rw [hm₃, h₂.mem]
  exact ⟨hc₃, hmm ▸ hf₁, hmm ▸ hb₁, by rw [hg₃ _ (by decide) (by decide), hcx₂], hbx₃, hsi₃⟩

/-- If `big`: the digest for `core`, the digest's number shifted left by
`sh` bits, in `Q` bytes at `fXc`. -/
theorem prepC_ok (hL : L.Ok) (hT : TabL P L) (hW : P.R.big = true) (hdn : P.F.H.D ≤ dn) {t : State}
    (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).prepC t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (76 + fXc), 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (76 + fXc)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.dg P.F.H.D) * 2 ^ P.R.sh) := by
  have hnb := hL.nB
  have ng := hL.ng
  obtain ⟨-, -, hQ66, hQD⟩ := P.sizesW hW
  obtain ⟨-, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  have hsl := P.R.nBits_len
  have hnb5 := (P.R.sizesW hW).2.2
  have hsh8 : P.R.sh < 8 := by simp only [RfcHash.Q] at hQ66; omega_using [hsl]
  have hsh1 : 1 ≤ P.R.sh := by simp only [RfcHash.Q] at hQ66; omega_using [hsl, hnb5]
  have hsc : (cfgOf P).sh = P.R.sh := rfl
  rw [Cfg.prepC]
  refine WP.seq (WP.mono (xcArgs_ok hL hT hW hc) fun u₁ ⟨hc₁, hf₁, hb₁, hcx₁, hbx₁, hsi₁⟩ => ?_)
  have ea : (L.F + BitVec.ofNat 32 (fXc + (P.Q - 1 - P.F.H.D))).setWidth 64 =
      L.B + BitVec.ofNat 64 (76 + fXc + (P.Q - 1 - P.F.H.D)) := by
    rw [hL.frv (by simp only [fXc]; omega_using [hQ66]), Nat.add_assoc]
  have sepD : Region.Disjoint ⟨L.a2.setWidth 64, P.F.H.D⟩
      ⟨L.B + BitVec.ofNat 64 (76 + fXc + (P.Q - 1 - P.F.H.D)), P.F.H.D⟩ :=
    ((hL.kg.sub_left (Offset.sub_base _ (by simp only [fXc]; omega_using [hQ66, hQD]))).symm.sub_left (Region.sub_prefix hdn))
  have hdg : Spec.Sha256.bytesAt u₁.mem L.dg P.F.H.D = Spec.Sha256.bytesAt t.mem L.dg P.F.H.D :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact fun a h₁ h₂ => hL.kg a (Offset.sub_base L.B (d := 76 + fXc) (n := 72) (k := 588)
        (by simp only [fXc]; omega_using []) a h₂) (Region.sub_prefix hdn a h₁)) (by omega_using [hD64])
  refine WP.seq (WP.mono (cpLoop_ok hL hc₁ (S := L.a2) (D := L.F + BitVec.ofNat 32 (fXc + (P.Q - 1 - P.F.H.D)))
      (n := P.F.H.D) (by omega_using [hD16]) (by omega_using [hD64]) (by omega_using [hdn, ng])
      (by rw [hL.frN (by simp only [fXc]; omega_using [hQ66])]; have := hL.e28; have := hL.e588; simp only [fXc]; omega_using [hQ66, hQD])
      (by have := hc₁.inDg (o := 0) (n := P.F.H.D) (by omega_using [hdn]) (by omega_using []); rwa [BitVec.add_zero] at this)
      (by rw [ea]; exact hc₁.inFrW (by omega_using []) (by simp only [fXc]; omega_using [hQ66, hQD]) hL)
      (by rw [ea]; exact sepD)
      (by rw [ea]; exact safe_high L (by simp only [fXc]; omega_using []) (by simp only [fXc]; omega_using [hQ66, hQD]))
      hsi₁ hbx₁ hcx₁) fun u₄ ⟨hc₄, hf₄, hb₄, _⟩ => ?_)
  rw [ea] at hf₄ hb₄
  refine WP.seq (WP.mono (scrPtr_ok hL hc₄) fun u₅ ⟨hc₅, hm₅, hdi₅, _⟩ => ?_)
  rw [hsc]
  refine WP.mono (conv_ok hL hW hc₅ hdi₅ (o := fXc) (s := 8 - P.R.sh) (by decide) (by decide) (by omega_using [hsl])
    (by omega_using [])) fun u₆ ⟨hc₆, _, hf₆, hb₆⟩ => ?_
  refine ⟨hc₆, ?_, ?_⟩
  · refine ((hf₁.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩).trans
      (hf₄.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩)).trans
      (hm₅ ▸ hf₆.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h
    · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_using []) (by simp only [fXc]; omega_using [hQ66, hQD])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega_using [hQ66])⟩
  · -- `Q - D - 1` zero bytes, the digest, and a zero byte, shifted right by `8 - sh` bits.
    have hz : ∀ a n, a + n ≤ 72 → Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (76 + fXc + a)) n =
        List.replicate n 0 := fun a n han => by
      have h1 := bytesAt_take u₁.mem (L.B + BitVec.ofNat 64 (76 + fXc)) (n := a + n) (k := 72) (by omega_using [han])
      rw [hb₁, List.take_replicate, Nat.min_eq_left (by omega_using [han]), Proof.Hmac.Common.bytesAt_add, Offset.add_add,
        ← List.replicate_append_replicate] at h1
      exact (List.append_inj h1 (by simp [Spec.Sha256.bytesAt])).2
    have hY : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (76 + fXc)) P.Q =
        List.replicate (P.Q - 1 - P.F.H.D) 0 ++ (Spec.Sha256.bytesAt t.mem L.dg P.F.H.D ++ List.replicate 1 0) := by
      have e := Proof.Hmac.Common.bytesAt_add u₄.mem (L.B + BitVec.ofNat 64 (76 + fXc)) (P.Q - 1 - P.F.H.D)
        (P.F.H.D + 1)
      have e' := Proof.Hmac.Common.bytesAt_add u₄.mem
        (L.B + BitVec.ofNat 64 (76 + fXc) + BitVec.ofNat 64 (P.Q - 1 - P.F.H.D)) P.F.H.D 1
      rw [show P.Q - 1 - P.F.H.D + (P.F.H.D + 1) = P.Q by omega_using [hQD]] at e
      rw [Offset.add_add, Offset.add_add] at e'
      rw [Offset.add_add] at e
      have p₁ : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (76 + fXc)) (P.Q - 1 - P.F.H.D) =
          List.replicate (P.Q - 1 - P.F.H.D) 0 := by
        rw [bytesAt_frame hf₄ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (.inl (by omega_using [])) (by simp only [fXc]; omega_using [hQ66]) (by simp only [fXc]; omega_using [hQ66, hQD]))
          (by omega_using [hQ66])]
        have := hz 0 (P.Q - 1 - P.F.H.D) (by omega_using [hQ66])
        rwa [Nat.add_zero] at this
      have p₃ : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (76 + fXc + (P.Q - 1 - P.F.H.D) + P.F.H.D)) 1 =
          List.replicate 1 0 := by
        rw [bytesAt_frame hf₄ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (.inr (by omega_using [])) (by simp only [fXc]; omega_using [hQ66, hQD]) (by simp only [fXc]; omega_using [hQ66, hQD]))
          (by omega_using []), show 76 + fXc + (P.Q - 1 - P.F.H.D) + P.F.H.D = 76 + fXc + (P.Q - 1 - P.F.H.D + P.F.H.D) by omega_using []]
        exact hz (P.Q - 1 - P.F.H.D + P.F.H.D) 1 (by omega_using [hQ66, hQD])
      rw [e, e', hb₄, hdg, p₁, p₃]
    rw [hb₆, hm₅, hY, ofBytes_zeros, ofBytes_append_zeros, show 8 * 1 = 8 from rfl, shift_back _ _ hsh8]

end VG.Proof.Ecdsa.Rfc6979.X86
