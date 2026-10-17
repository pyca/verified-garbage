module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Steps
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.X25519.X86.Column

/-!
# Deterministic ECDSA on x86 (32-bit): scalars longer than the hash

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Wide.lean`), for a curve whose
scalars are longer than the hash function's output (`wide`: P-521's 66 bytes
with SHA-512's 64): the `Q` bytes at an offset in the frame's top words,
shifted right in place through the words at `scratch + 2560` (`conv_ok`, by
`loadBytes_ok`, `shrWords_ok` and `storeBytes_ok`); the digest for `core`,
the digest then `Q - D` zero bytes shifted right, which is the digest's
number shifted left by `sh` bits (`coreDigest_ok`); and the candidate, `V`
kept in the frame's top words and, after the next `V`, its first word after
it, shifted right by `sh` bits (`candW_ok`).
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

theorem scr_of (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .edi = L.a3) : Scr t L.scr 8192 := by
  have hn : L.scr.toNat + 8192 ≤ 2 ^ 32 := by
    have := hL.nc; have := L.a3.isLt
    simp only [Lay.scr, BitVec.toNat_setWidth]; omega_arith
  have hF : 20 ≤ L.F.toNat := by have := hL.FN; have := hL.e536; omega_arith
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
theorem conv_ok (hL : L.Ok) (hW : P.R.wide = true) {t : State} (hc : Ctx L g m₀ t)
    (hdi : t.gpr .edi = L.a3) {o s : Nat} (ho₁ : 196 ≤ o) (ho₂ : o + 72 ≤ 460) (hs₁ : 1 ≤ s) (hs₂ : s < 32) :
    WP isa (.block ((cfgOf P).conv o s)) t fun t' => Ctx L g m₀ t' ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → t'.gpr r = t.gpr r) ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (76 + o), P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (76 + o)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (76 + o)) P.Q) >>> s) := by
  obtain ⟨hw9, hQ66, -⟩ := P.sizesW hW
  have nB := hL.nB
  have hFN := hL.FN
  have e536 := hL.e536
  have e28 := hL.e28
  have hw2 : ((cfgOf P).len + 7) / 8 = P.w := by simp only [cfgAny, show P.R.E.C.len = 66 from hQ66, show P.w = 9 from hw9]
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

/-! ## Copies into the frame's top words -/

/-- `4 K` bytes copied to `esp + d`, in the frame's top words, by `copyN`, with `Ctx` kept. -/
theorem copyF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : BitVec 32} {SA : Addr}
    (hs : u.gpr src = S) (hsr : src ≠ .eax) {so d K : Nat} (hd₁ : 196 ≤ d) (hd₂ : d + 4 * K ≤ 460)
    (hSA : ∀ j < K, addr S (so + 4 * j) = SA + BitVec.ofNat 64 (4 * j))
    (hr : ∀ j < K, InRegions (u.rd ++ u.wr) (SA + BitVec.ofNat 64 (4 * j)) 4)
    (hsep : Region.Disjoint ⟨SA, 4 * K⟩ ⟨L.B + BitVec.ofNat 64 (76 + d), 4 * K⟩) :
    WP isa (.block (copyN K src so .esp d)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.B + BitVec.ofNat 64 (76 + d), 4 * K⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (76 + d)) (4 * K) = Spec.Sha256.bytesAt u.mem SA (4 * K) :=
  have nB := hL.nB
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
    (ho₂ : o + 4 ≤ 460) :
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

end VG.Proof.Ecdsa.Rfc6979.X86
