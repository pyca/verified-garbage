module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Steps
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Copy
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Deterministic ECDSA on x86 (32-bit): scalars longer than the hash

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Wide.lean`), for a hash function
whose output is shorter than the curve's scalars (`wide`): the `Q` bytes at
an offset in the frame's top words, shifted right in place through the words
at `scratch + 2560` (`conv_ok`, by `loadBytes_ok`, `shrWords_ok` and
`storeBytes_ok`); `h`, `Q - D` zero bytes then the digest (`hPrep_ok`); the
digest for `core` if `sh ≠ 0`, the digest between `Q - D - 1` zero bytes and
one, shifted right by `8 - sh` bits, which is the digest's number shifted
left by `sh` bits (`xPrep_ok`); and the candidate `T`, `m` successive
`V = HMAC_K(V)` each copied after the last (`candW_ok`), its first `Q` bytes
then shifted right by `sh` bits (`candTop_ok`).
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

theorem scr_of (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .edi = L.a4) : Scr t L.scr 8192 := by
  have hn : L.scr.toNat + 8192 ≤ 2 ^ 32 := by
    have := hL.nc; have := L.a4.isLt
    simp only [Lay.scr, BitVec.toNat_setWidth]; omega_arith
  have hF : 20 ≤ L.F.toNat := by have := hL.FN; have := hL.e272; omega_arith
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

/-- In the wide case, the frame has 68 words at its top. -/
theorem e68 (hLe : L.e = P.e) (hW : P.wide = true) : L.e = 68 := by
  rw [hLe]; simp only [RfcHash.e, Impl.Ecdsa.Rfc6979.X86.extra, hW, ite_true]

/-- `conv o s`: the `Q` bytes at `esp + o`, in the frame's top words,
shifted right by `s` bits in place, through the words at `scratch + 2560`. -/
theorem conv_ok (hL : L.Ok) (hLe : L.e = P.e) (hW : P.wide = true) {t : State} (hc : Ctx L g m₀ t)
    (hdi : t.gpr .edi = L.a4) {o s : Nat} (ho₁ : 196 ≤ o) (ho₂ : o + 72 ≤ 468) (hs₁ : 1 ≤ s) (hs₂ : s < 32) :
    WP isa (.block ((cfgOf P).conv o s)) t fun t' => Ctx L g m₀ t' ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → t'.gpr r = t.gpr r) ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (76 + o), P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (76 + o)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (76 + o)) P.Q) >>> s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h3, hw9, hQ8, hQ66, hQw, hwQ, -⟩ := P.sizes
  have he := e68 hLe hW
  have nB := hL.nB
  have hFN := hL.FN
  have e272 := hL.e272
  have e20 := hL.e28
  have hw2 : (cfgOf P).w = P.w := rfl
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
    rw [h₁.mem] at f₂
    exact (f₂.sub fun r hr => ⟨⟨L.scr + BitVec.ofNat 64 2560, 72⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)⟩).trans
      (f₅.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩)
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

/-! ## Copies into the frame's top words -/

/-- `4 K` bytes copied to `esp + d`, in the frame's top words, by `copyN`, with `Ctx` kept. -/
theorem copyF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : BitVec 32} {SA : Addr}
    (hs : u.gpr src = S) (hsr : src ≠ .eax) {so d K : Nat} (hd₁ : 196 ≤ d) (hd₂ : d + 4 * K ≤ 196 + 4 * L.e)
    (hSA : ∀ j < K, addr S (so + 4 * j) = SA + BitVec.ofNat 64 (4 * j))
    (hr : ∀ j < K, InRegions (u.rd ++ u.wr) (SA + BitVec.ofNat 64 (4 * j)) 4)
    (hsep : Region.Disjoint ⟨SA, 4 * K⟩ ⟨L.B + BitVec.ofNat 64 (76 + d), 4 * K⟩) :
    WP isa (.block (Cfg.copyN K src so .esp d)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.B + BitVec.ofNat 64 (76 + d), 4 * K⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (76 + d)) (4 * K) = Spec.Sha256.bytesAt u.mem SA (4 * K) :=
  have nB := hL.nB
  have he := L.he
  WP.mono_syms (copyN_ok (K := K) (by decide) hsr hSA (fun j hj => fr_addr hL (by omega_arith)) hsep (by omega_arith) K
    (Nat.le_refl _) u hs hc.esp hr fun j hj => by rw [Offset.add_add]; exact hc.inFrW (by omega_arith) (by omega_arith) hL)
    fun u' ⟨hrd, hwr, hg, hf, hb⟩ hsy =>
    ⟨hc.keep (hsy := hsy) hL hrd hwr (hg _ (by decide)) hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega_arith) (by omega_arith)), hg, hf, hb⟩

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
theorem zeroF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {o : Nat} (ho₁ : 196 ≤ o)
    (ho₂ : o + 4 ≤ 196 + 4 * L.e) :
    WP isa (.block [.mov .eax (.imm 0), .store (stk o) .eax]) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.B + BitVec.ofNat 64 (76 + o), 4⟩] u.mem u'.mem ∧
      ∀ k ≤ 4, Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (76 + o)) k = List.replicate k 0 := by
  have nB := hL.nB
  have ea : addr L.F o = L.B + BitVec.ofNat 64 (76 + o) := hL.addrF (by omega_arith)
  refine wp_movi fun u₁ v₁ => wp_stm (B := L.F) (by rw [v₁.other .esp (by decide), hc.esp])
    (by rw [v₁.wr, ea]; exact hc.inFrW (by omega_arith) (by omega_arith) hL) fun u₂ v₂ => WP.block_nil ?_
  have hm : u₂.mem = u.mem.writeW (L.B + BitVec.ofNat 64 (76 + o)) (0 : BitVec 32) := by
    rw [v₂.mem, v₁.gpr, v₁.mem, ea]
  have hf : Frame [⟨L.B + BitVec.ofNat 64 (76 + o), 4⟩] u.mem u₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.keep (hsy := by rw [v₂.syms, v₁.syms]) hL (by rw [v₂.rd, v₁.rd]) (by rw [v₂.wr, v₁.wr]) (by rw [v₂.gpr, v₁.other _ (by decide)]) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega_arith) (by omega_arith)),
    fun r hr => by rw [v₂.gpr, v₁.other _ hr], hf, fun k hk => by rw [hm]; exact bytesAt_writeW_zero _ _ hk⟩

/-- `Q` bytes copied to `esp + d`, in the frame's top words, by `copyBytes`, with `Ctx` kept. -/
theorem copyBF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : BitVec 32} {SA : Addr}
    (hs : u.gpr src = S) (hsr : src ≠ .eax) {so d Q : Nat} (h4 : 4 ≤ Q) (hd₁ : 196 ≤ d) (hd₂ : d + Q ≤ 196 + 4 * L.e)
    (hSA : ∀ j, j + 4 ≤ Q → addr S (so + j) = SA + BitVec.ofNat 64 j)
    (hr : ∀ j, j + 4 ≤ Q → InRegions (u.rd ++ u.wr) (SA + BitVec.ofNat 64 j) 4)
    (hsep : Region.Disjoint ⟨SA, Q⟩ ⟨L.B + BitVec.ofNat 64 (76 + d), Q⟩) :
    WP isa (.block (Cfg.copyBytes Q src so .esp d)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.B + BitVec.ofNat 64 (76 + d), Q⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (76 + d)) Q = Spec.Sha256.bytesAt u.mem SA Q :=
  have nB := hL.nB
  have he := L.he
  WP.mono_syms (copyBytes_ok (by decide) hsr hSA
    (fun j hj => by rw [hL.addrF (by omega_arith), Offset.add_add, Nat.add_assoc]) hsep h4 (by omega_arith) hs hc.esp hr
    fun j hj => by rw [Offset.add_add]; exact hc.inFrW (by omega_arith) (by omega_arith) hL)
    fun u' ⟨hrd, hwr, hg, hf, hb⟩ hsy =>
    ⟨hc.keep (hsy := hsy) hL hrd hwr (hg _ (by decide)) hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega_arith) (by omega_arith)), hg, hf, hb⟩

/-- The stores of `zero18`, the first `k` of them, with `eax` zero. -/
theorem zeroStores_ok (hL : L.Ok) {o : Nat} (ho₁ : 196 ≤ o) (ho₂ : o + 72 ≤ 196 + 4 * L.e) :
    ∀ k ≤ 18, ∀ {u : State}, Ctx L g m₀ u → u.gpr .eax = 0 →
    WP isa (.block ((List.range k).map fun j => .store (stk (o + 4 * j)) .eax)) u
      fun u' => Ctx L g m₀ u' ∧ (∀ r, u'.gpr r = u.gpr r) ∧
        Frame [⟨L.B + BitVec.ofNat 64 (76 + o), 72⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (76 + o)) (4 * k) = List.replicate (4 * k) 0
  | 0, _, u, hc, _ => WP.of_runBlock ⟨u, rfl, hc, fun _ => rfl, Frame.refl _ _, rfl⟩
  | k + 1, hk, u, hc, hax => by
    have nB := hL.nB
    have := L.he
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zeroStores_ok hL ho₁ ho₂ k (by omega) hc hax) fun u₁ ⟨hc₁, hg₁, hf₁, hb₁⟩ => ?_
    have ea : addr L.F (o + 4 * k) = L.B + BitVec.ofNat 64 (76 + (o + 4 * k)) := hL.addrF (by omega_arith)
    refine wp_stm (B := L.F) (by rw [hc₁.esp]) (by rw [ea]; exact hc₁.inFrW (by omega_arith) (by omega_arith) hL)
      fun u₂ v₂ => WP.block_nil ?_
    have hm : u₂.mem = u₁.mem.writeW (L.B + BitVec.ofNat 64 (76 + (o + 4 * k))) (0 : BitVec 32) := by
      rw [v₂.mem, ea, hg₁, hax]
    have hf : Frame [⟨L.B + BitVec.ofNat 64 (76 + (o + 4 * k)), 4⟩] u₁.mem u₂.mem := by
      rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    refine ⟨hc₁.keep (hsy := v₂.syms) hL v₂.rd v₂.wr (by rw [v₂.gpr]) hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega_arith) (by omega_arith)),
      fun r => by rw [v₂.gpr, hg₁], hf₁.trans (hf.sub fun r hr => ⟨_, List.mem_singleton_self _,
        by simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)⟩), ?_⟩
    have h2 : Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (76 + (o + 4 * k))) 4 = List.replicate 4 0 := by
      rw [hm]; exact bytesAt_writeW_zero _ _ (Nat.le_refl _)
    have h1 : Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (76 + o)) (4 * k) =
        Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (76 + o)) (4 * k) :=
      bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
    rw [show 4 * (k + 1) = 4 * k + 4 by omega, Proof.Hmac.Common.bytesAt_add, Offset.add_add,
      show 76 + o + 4 * k = 76 + (o + 4 * k) by omega, h2, h1, hb₁, List.replicate_append_replicate]

/-- Eighteen zero words at `esp + o`, in the frame's top words. -/
theorem zero18_ok (hL : L.Ok) {o : Nat} (ho₁ : 196 ≤ o) (ho₂ : o + 72 ≤ 196 + 4 * L.e) {u : State}
    (hc : Ctx L g m₀ u) :
    WP isa (.block (Cfg.zero18 o)) u fun u' => Ctx L g m₀ u' ∧ (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧
      Frame [⟨L.B + BitVec.ofNat 64 (76 + o), 72⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (76 + o)) 72 = List.replicate 72 0 := by
  rw [Cfg.zero18, WP.block_append_iff]
  refine wp_movi fun u₁ v₁ => WP.block_nil ?_
  have hc₁ := (Upd.of_wp hL hc (by decide) v₁).ctx
  refine WP.mono (zeroStores_ok hL ho₁ ho₂ 18 (Nat.le_refl _) hc₁ v₁.gpr) fun u' ⟨hc', hg', hf', hb'⟩ =>
    ⟨hc', fun r hr => by rw [hg', v₁.other _ hr], by rw [← v₁.mem]; exact hf', hb'⟩

/-! ## `h` and the digest for `core` -/

/-- `h`: `Q - D` zero bytes, then the digest (at `esi`), at `fX`. -/
theorem hPrep_ok (hL : L.Ok) (hLe : L.e = P.e) (hW : P.wide = true) (hdn : P.H.D ≤ dn) {t : State}
    (hc : Ctx L g m₀ t) (hsi : t.gpr .esi = L.a2) :
    WP isa (.block (cfgOf P).hPrep) t fun t' => Ctx L g m₀ t' ∧ (∀ r, r ≠ .eax → t'.gpr r = t.gpr r) ∧
      Frame [⟨L.B + BitVec.ofNat 64 272, 72⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 272) P.Q =
        List.replicate (P.Q - P.H.D) 0 ++ Spec.Sha256.bytesAt t.mem L.dg P.H.D := by
  have he := e68 hLe hW
  have hQD : P.H.D < P.Q := by simpa [RfcHash.wide] using hW
  have := P.sizes
  have nB := hL.nB
  have ng := hL.ng
  rw [show (cfgOf P).hPrep = Cfg.zero18 fX ++ Cfg.copyBytes P.H.D .esi 0 .esp (196 + P.Q - P.H.D) from rfl,
    WP.block_append_iff]
  refine WP.mono (zero18_ok hL (o := fX) (by decide) (by rw [he]; decide) hc)
    fun u₁ ⟨hc₁, hg₁, hf₁, hb₁⟩ => ?_
  simp only [show 76 + fX = 272 from rfl] at hf₁ hb₁
  have hdg₁ : Spec.Sha256.bytesAt u₁.mem L.dg P.H.D = Spec.Sha256.bytesAt t.mem L.dg P.H.D :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_DG (by omega_arith)).symm.sub_left (Region.sub_prefix hdn)) (by nums)
  have hsep : Region.Disjoint ⟨L.dg, P.H.D⟩ ⟨L.B + BitVec.ofNat 64 (76 + (196 + P.Q - P.H.D)), P.H.D⟩ :=
    (hL.stk_DG (by rw [he]; nums)).symm.sub_left (Region.sub_prefix hdn)
  refine WP.mono (copyBF_ok hL hc₁ (src := .esi) (S := L.a2) (SA := L.dg) ((hg₁ _ (by decide)).trans hsi) (by decide)
    (so := 0) (d := 196 + P.Q - P.H.D) (Q := P.H.D) (by nums) (by omega) (by rw [he]; nums)
    (fun j hj => by rw [Nat.zero_add]; exact addr_eq (by omega_arith))
    (fun j hj => hc₁.inDg (by omega) (by nums)) hsep)
    fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  have e₁ : 76 + (196 + P.Q - P.H.D) = 272 + (P.Q - P.H.D) := by omega
  rw [e₁, hdg₁] at hb₂
  rw [e₁] at hf₂
  refine ⟨hc₂, fun r hr => (hg₂ r hr).trans (hg₁ r hr), hf₁.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _,
    by simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by nums)⟩), ?_⟩
  rw [show P.Q = (P.Q - P.H.D) + P.H.D by omega, Proof.Hmac.Common.bytesAt_add, Offset.add_add,
    show P.Q - P.H.D + P.H.D - P.H.D = P.Q - P.H.D by omega, hb₂,
    bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by nums)) (by omega)]
  have := bytesAt_take u₁.mem (L.B + BitVec.ofNat 64 272) (n := P.Q - P.H.D) (k := 72) (by nums)
  rw [this, hb₁, List.take_replicate, Nat.min_eq_left (by nums)]

theorem shift_back (e sh : Nat) (hs : sh < 8) : (e * 2 ^ 8) >>> (8 - sh) = e * 2 ^ sh := by
  rw [Nat.shiftRight_eq_div_pow, show e * 2 ^ 8 = e * 2 ^ sh * 2 ^ (8 - sh) by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- If `sh ≠ 0`: the digest for `core`, the digest's number shifted left by
`sh` bits, in `Q` bytes at `fXc`. -/
theorem xPrep_ok (hL : L.Ok) (hLe : L.e = P.e) (hW : P.wide = true) (hdn : P.H.D ≤ dn) (hsh : P.R.sh ≠ 0)
    {t : State} (hc : Ctx L g m₀ t) (hsi : t.gpr .esi = L.a2) (hdi : t.gpr .edi = L.a4) :
    WP isa (.block (cfgOf P).xPrep) t fun t' => Ctx L g m₀ t' ∧ t'.gpr .edi = t.gpr .edi ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 344, 72⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 344) P.Q =
        Spec.Weierstrass.toBytes P.Q (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.dg P.H.D) * 2 ^ P.R.sh) := by
  have he := e68 hLe hW
  have hQD : P.H.D < P.Q := by simpa [RfcHash.wide] using hW
  have hsl := P.R.nBits_len
  have hsh8 : P.R.sh < 8 := by omega
  have hsc : (cfgOf P).sh = P.R.sh := rfl
  have := P.sizes
  have nB := hL.nB
  have ng := hL.ng
  rw [Cfg.xPrep, hsc, ite_eq_right_of_eq_false _ _ (eq_false hsh),
    show Cfg.copyBytes (cfgOf P).D .esi 0 .esp (fXc + (cfgOf P).len - (cfgOf P).D - 1) =
      Cfg.copyBytes P.H.D .esi 0 .esp (268 + P.Q - P.H.D - 1) from rfl, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zero18_ok hL (o := fXc) (by decide) (by rw [he]; decide) hc)
    fun u₁ ⟨hc₁, hg₁, hf₁, hb₁⟩ => ?_
  simp only [show 76 + fXc = 344 from rfl] at hf₁ hb₁
  have hdg₁ : Spec.Sha256.bytesAt u₁.mem L.dg P.H.D = Spec.Sha256.bytesAt t.mem L.dg P.H.D :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_DG (by omega_arith)).symm.sub_left (Region.sub_prefix hdn)) (by nums)
  have hsep : Region.Disjoint ⟨L.dg, P.H.D⟩ ⟨L.B + BitVec.ofNat 64 (76 + (268 + P.Q - P.H.D - 1)), P.H.D⟩ :=
    (hL.stk_DG (by rw [he]; nums)).symm.sub_left (Region.sub_prefix hdn)
  refine WP.mono (copyBF_ok hL hc₁ (src := .esi) (S := L.a2) (SA := L.dg) ((hg₁ _ (by decide)).trans hsi) (by decide)
    (so := 0) (d := 268 + P.Q - P.H.D - 1) (Q := P.H.D) (by nums) (by omega) (by rw [he]; nums)
    (fun j hj => by rw [Nat.zero_add]; exact addr_eq (by omega_arith))
    (fun j hj => hc₁.inDg (by omega) (by nums)) hsep)
    fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  have e₁ : 76 + (268 + P.Q - P.H.D - 1) = 344 + (P.Q - P.H.D - 1) := by omega
  rw [e₁, hdg₁] at hb₂
  rw [e₁] at hf₂
  have hdi₂ : u₂.gpr .edi = L.a4 := by rw [hg₂ _ (by decide), hg₁ _ (by decide), hdi]
  refine WP.mono (conv_ok hL hLe hW hc₂ hdi₂ (o := fXc) (s := 8 - P.R.sh) (by decide) (by decide) (by omega)
    (by omega)) fun u₃ ⟨hc₃, hg₃, hf₃, hb₃⟩ => ?_
  simp only [show 76 + fXc = 344 from rfl] at hf₃ hb₃
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
    have hY : Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 344) P.Q =
        List.replicate (P.Q - P.H.D - 1) 0 ++ (Spec.Sha256.bytesAt t.mem L.dg P.H.D ++ List.replicate 1 0) := by
      have hz : ∀ a n, a + n ≤ 72 → Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (344 + a)) n =
          List.replicate n 0 := fun a n han => by
        have h1 := bytesAt_take u₁.mem (L.B + BitVec.ofNat 64 344) (n := a + n) (k := 72) (by omega)
        rw [hb₁, List.take_replicate, Nat.min_eq_left (by omega), Proof.Hmac.Common.bytesAt_add, Offset.add_add,
          ← List.replicate_append_replicate] at h1
        exact (List.append_inj h1 (by simp [Spec.Sha256.bytesAt])).2
      have e := Proof.Hmac.Common.bytesAt_add u₂.mem (L.B + BitVec.ofNat 64 344) (P.Q - P.H.D - 1) (P.H.D + 1)
      have e' := Proof.Hmac.Common.bytesAt_add u₂.mem (L.B + BitVec.ofNat 64 344 + BitVec.ofNat 64 (P.Q - P.H.D - 1))
        P.H.D 1
      rw [show P.Q - P.H.D - 1 + (P.H.D + 1) = P.Q by omega] at e
      rw [Offset.add_add, Offset.add_add] at e'
      rw [Offset.add_add] at e
      have p₁ : Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 344) (P.Q - P.H.D - 1) =
          List.replicate (P.Q - P.H.D - 1) 0 := by
        rw [bytesAt_frame hf₂ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (by omega) (by omega) (by nums)) (by omega)]
        have := hz 0 (P.Q - P.H.D - 1) (by nums)
        rwa [Nat.add_zero] at this
      have p₃ : Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (344 + (P.Q - P.H.D - 1) + P.H.D)) 1 =
          List.replicate 1 0 := by
        rw [bytesAt_frame hf₂ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (by omega) (by omega) (by nums)) (by omega),
          show 344 + (P.Q - P.H.D - 1) + P.H.D = 344 + (P.Q - P.H.D - 1 + P.H.D) by omega]
        exact hz (P.Q - P.H.D - 1 + P.H.D) 1 (by nums)
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
    rw [genT_succ, List.length_append, genT_length P K k V, mac_length]
    rw [Nat.succ_mul]

/-- What a candidate changes: `scratch`, the stack below the frame, `K` and
`V`, and `T` at the frame's top. -/
abbrev CWW {dn : Nat} (L : Lay dn) : List Region := [L.SCR, ⟨L.B, 204⟩, ⟨L.B + BitVec.ofNat 64 416, 128⟩]

theorem kvw_cww : ∀ r ∈ KVW L, ∃ r' ∈ CWW L, Region.Sub r r' := fun r hr => ⟨r, by
  simp only [CWW, KVW, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with h | h <;> simp [h], sub_refl _⟩

/-- The first `k` `V`s of the candidate: each `V = HMAC_K(V)`, copied to `T`
after the ones before. -/
theorem candW_ok (hL : L.Ok) (hLe : L.e = P.e) (hW : P.wide = true) (hT : TabL P L) :
    ∀ k, k * P.H.D ≤ 128 → ∀ {t : State}, Ctx L g m₀ t → SavedK P L t.mem (kOf P L t.mem) →
    WP isa ((cfgOf P).candW k) t fun u => Ctx L g m₀ u ∧ Frame (CWW L) t.mem u.mem ∧
      kOf P L u.mem = kOf P L t.mem ∧
      vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kOf P L t.mem) k (vOf P L t.mem)).2 ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 416) (k * P.H.D) =
        (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kOf P L t.mem) k (vOf P L t.mem)).1 ∧
      SavedK P L u.mem (kOf P L u.mem)
  | 0, _, t, hc, hS => WP.of_runBlock ⟨t, rfl, hc, Frame.refl _ _, rfl, rfl, by simp [Spec.Ecdsa.Rfc6979.genT,
      Spec.Sha256.bytesAt], hS⟩
  | k + 1, hk, t, hc, hS => by
    have he := e68 hLe hW
    have nB := hL.nB
    have hk' : k * P.H.D + P.H.D ≤ 128 := by rw [Nat.succ_mul] at hk; exact hk
    rw [Cfg.candW]
    refine WP.seq (WP.mono (candW_ok hL hLe hW hT k (by nums) hc hS) fun u₁ ⟨hc₁, hf₁, hk₁, hv₁, hb₁, hS₁⟩ => ?_)
    refine WP.seq (WP.mono (hmacVR_ok hL hT hc₁ hS₁) fun u₂ ⟨hc₂, hf₂, hk₂, hv₂, hS₂⟩ => ?_)
    have hsep : Region.Disjoint ⟨L.B + BitVec.ofNat 64 140, P.H.D⟩
        ⟨L.B + BitVec.ofNat 64 (76 + (fT + k * (cfgOf P).D)), P.H.D⟩ :=
      Offset.disjoint _ (by simp only [fT, cfgOf]; nums) (by nums) (by simp only [fT, cfgOf]; nums)
    refine WP.mono (copyBF_ok hL hc₂ (src := .esp) (S := L.F) (SA := L.B + BitVec.ofNat 64 140) hc₂.esp (by decide)
      (so := fV) (d := fT + k * (cfgOf P).D) (Q := P.H.D) (by nums) (by simp only [fT]; omega)
      (by simp only [fT, cfgOf]; rw [he]; nums)
      (fun j hj => by rw [hL.addrF (by simp only [fV]; nums), Offset.add_add, show 76 + (fV + j) = 140 + j by
        simp only [fV]; omega])
      (fun j hj => by rw [Offset.add_add]; exact hc₂.inFr (by omega) (by nums) hL) hsep)
      fun u₃ ⟨hc₃, _, hf₃, hb₃⟩ => ?_
    have e₁ : 76 + (fT + k * (cfgOf P).D) = 416 + k * P.H.D := by simp only [fT, cfgOf]; omega
    rw [e₁] at hf₃ hb₃
    -- What the copy keeps: `K`, `V` and `scratch`.
    have dKV : ∀ {o : Nat}, 76 ≤ o → o + P.H.D ≤ 204 →
        Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 o) P.H.D = Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 o) P.H.D :=
      fun h₁ h₂ => bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by nums) (by nums)) (by nums)
    have hk₃ : kOf P L u₃.mem = kOf P L u₂.mem := dKV (by decide) (by nums)
    have hv₃ : vOf P L u₃.mem = vOf P L u₂.mem := dKV (by decide) (by nums)
    refine ⟨hc₃, ?_, ?_, ?_, ?_, ?_⟩
    · refine ((hf₁.trans (hf₂.sub kvw_cww)).trans (hf₃.sub fun r hr => ?_))
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B + BitVec.ofNat 64 416, 128⟩, by simp [CWW], Offset.sub _ (by omega) (by nums)⟩
    · rw [hk₃, hk₂, hk₁]
    · rw [hv₃, hv₂, genT_succ, hk₁, hv₁]
    · rw [genT_succ, Nat.succ_mul, Proof.Hmac.Common.bytesAt_add, Offset.add_add, hb₃, ← hb₁,
        show Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 140) P.H.D = vOf P L u₂.mem from rfl, hv₂, hk₁, hv₁]
      congr 1
      · -- `T`'s first `k` `V`s, kept by the HMAC and the copy.
        rw [bytesAt_frame hf₃ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (by omega) (by omega) (by nums)) (by nums)]
        exact bytesAt_frame hf₂ (fun r hr => by
          simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hL.stk_SCR (by rw [he]; nums)
          · exact Offset.disjoint_base _ (by omega) (by nums)) (by nums)
    · rw [hk₃]
      exact hS₂.frame hf₃ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hL.stk_scr (by rw [he]; nums) (by decide)).symm

/-- If `sh ≠ 0`: `T`'s first `Q` bytes shifted right by `sh` bits. -/
theorem candTop_ok (hL : L.Ok) (hLe : L.e = P.e) (hW : P.wide = true) (hT : TabL P L) (hsh : P.R.sh ≠ 0)
    {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).candTop) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 416, P.Q⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 416) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 416) P.Q) >>> P.R.sh) := by
  have hsl := P.R.nBits_len
  have hsc : (cfgOf P).sh = P.R.sh := rfl
  rw [Cfg.candTop, hsc, ite_eq_right_of_eq_false _ _ (eq_false hsh), WP.block_append_iff]
  refine WP.mono (scrPtr_ok hL hT hc) fun u₁ h₁ => ?_
  refine WP.mono (conv_ok hL hLe hW h₁.ctx h₁.val (o := fT) (s := P.R.sh) (by decide) (by decide) (by omega)
    (by omega)) fun u₂ ⟨hc₂, _, hf₂, hb₂⟩ => ?_
  simp only [show 76 + fT = 416 from rfl] at hf₂ hb₂
  rw [h₁.mem] at hf₂ hb₂
  exact ⟨hc₂, hf₂, hb₂⟩

end VG.Proof.Ecdsa.Rfc6979.X86
