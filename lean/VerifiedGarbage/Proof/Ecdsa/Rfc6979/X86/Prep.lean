module

-- separate module: its proofs (the buffers X and h) build in parallel with `Steps`, which `Cand` also imports
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Hmac
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Regs
public import VerifiedGarbage.Proof.Framework.X86.Wp
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import Aesop.BuiltinRules
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.X86.Lit
import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Bignum.X86.CopyRegion
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86
public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Spec.Sha256

/-! ### `Ecdsa.Rfc6979.X86.Copy`, which this module and modules that import it used -/

section

/-!
# Deterministic ECDSA on x86 (32-bit): copying words

`copyN k src so dst d` copies the `4 k` bytes at `src + so` to `dst + d`, a
word at a time through `eax`, when the two ranges are apart: each word
written is the word read (`copyW_ok`), so the bytes written are the bytes
read (`copyN_ok`, by induction on the words). The addresses the code
computes from `src` and `dst` are those of ranges at `SA` and `DA`.
`copyBytes Q` copies `Q ≥ 4` bytes: the whole words, then the last four bytes
again (`copyBytes_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.Rfc6979.X86
open VG.Impl.Pbkdf2.Stream.X86 (at_)

/-- One word copied through `eax`. -/
theorem copyW_ok {u : State} {src dst : Reg} {S D : BitVec 32} (hs : u.gpr src = S) (hd : u.gpr dst = D)
    {so d : Nat} (hr : InRegions (u.rd ++ u.wr) (addr S so) 4) (hw : InRegions u.wr (addr D d) 4)
    (hdr : dst ≠ .eax) :
    WP isa (.block [.mov .eax (.mem (at_ src so)), .store (at_ dst d) .eax]) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧
      u'.mem = u.mem.writeW (addr D d) (u.mem.readW (addr S so) 32) :=
  wp_ldm hs hr fun u₁ v₁ => wp_stm (B := D) (by rw [v₁.other _ hdr, hd]) (by rw [v₁.wr]; exact hw)
    fun u₂ v₂ => WP.block_nil ⟨by rw [v₂.rd, v₁.rd], by rw [v₂.wr, v₁.wr],
      fun r hr => by rw [v₂.gpr, v₁.other _ hr], by rw [v₂.mem, v₁.gpr, v₁.mem]⟩

theorem bytesAt_copied (m : Mem) (D S : Addr) :
    Spec.Sha256.bytesAt (m.writeW D (m.readW S 32)) D 4 = Spec.Sha256.bytesAt m S 4 := by
  rw [show (32 : Nat) = 8 * 4 from rfl, Proof.Hmac.Common.writeW_readW]
  have := Proof.Hmac.Common.bytesAt_writeBytes_self m D (Spec.Sha256.bytesAt m S 4) (by simp [Spec.Sha256.bytesAt])
  rwa [Proof.Hmac.Common.bytesAt_length] at this

theorem copyN_ok {src dst : Reg} {S D : BitVec 32} {SA DA : Addr} {so d K : Nat} (hdr : dst ≠ .eax)
    (hsr : src ≠ .eax) (hSA : ∀ j < K, addr S (so + 4 * j) = SA + BitVec.ofNat 64 (4 * j))
    (hDA : ∀ j < K, addr D (d + 4 * j) = DA + BitVec.ofNat 64 (4 * j))
    (hsep : Region.Disjoint ⟨SA, 4 * K⟩ ⟨DA, 4 * K⟩) (hK : 4 * K < 2 ^ 32) :
    ∀ k ≤ K, ∀ u : State, u.gpr src = S → u.gpr dst = D →
      (∀ j < K, InRegions (u.rd ++ u.wr) (SA + BitVec.ofNat 64 (4 * j)) 4) →
      (∀ j < K, InRegions u.wr (DA + BitVec.ofNat 64 (4 * j)) 4) →
      WP isa (.block (Cfg.copyN k src so dst d)) u fun u' =>
        u'.rd = u.rd ∧ u'.wr = u.wr ∧ (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧
        Frame [⟨DA, 4 * K⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem DA (4 * k) = Spec.Sha256.bytesAt u.mem SA (4 * k)
  | 0, _, u, _, _, _, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _, rfl⟩
  | k + 1, hk, u, hs, hd, hr, hw => by
    rw [Cfg.copyN, List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copyN_ok hdr hsr hSA hDA hsep hK k (by omega_using [hk]) u hs hd hr hw)
      fun u₁ ⟨hrd₁, hwr₁, hg₁, hf₁, hb₁⟩ => ?_
    refine WP.mono (copyW_ok (u := u₁) (so := so + 4 * k) (d := d + 4 * k) (hg₁ _ hsr ▸ hs) (hg₁ _ hdr ▸ hd)
      (by rw [hSA k (by omega_using [hk]), hrd₁, hwr₁]; exact hr k (by omega_using [hk]))
      (by rw [hDA k (by omega_using [hk]), hwr₁]; exact hw k (by omega_using [hk])) hdr) fun u₂ ⟨hrd₂, hwr₂, hg₂, hm₂⟩ => ?_
    rw [hSA k (by omega_using [hk]), hDA k (by omega_using [hk])] at hm₂
    -- The word written, within the destination.
    have hsub : Region.Sub ⟨DA + BitVec.ofNat 64 (4 * k), 4⟩ ⟨DA, 4 * K⟩ := Offset.sub_base _ (by omega_using [hk])
    have hf₂ : Frame [⟨DA + BitVec.ofNat 64 (4 * k), 4⟩] u₁.mem u₂.mem := by
      rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    -- The word read, unchanged by the earlier words.
    have hsrc : Spec.Sha256.bytesAt u₁.mem (SA + BitVec.ofNat 64 (4 * k)) 4 =
        Spec.Sha256.bytesAt u.mem (SA + BitVec.ofNat 64 (4 * k)) 4 :=
      bytesAt_frame hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hsep.sub_left (Offset.sub_base _ (by omega_using [hk]))) (by omega_using [])
    refine ⟨hrd₂.trans hrd₁, hwr₂.trans hwr₁, fun r hr => (hg₂ r hr).trans (hg₁ r hr),
      hf₁.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact hsub⟩), ?_⟩
    rw [show 4 * (k + 1) = 4 * k + 4 by omega_using [], Proof.Hmac.Common.bytesAt_add, Proof.Hmac.Common.bytesAt_add,
      ← hsrc]
    congr 1
    · rw [← hb₁]
      exact bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by omega_using []) (by omega_using [hK, hk])) (by omega_using [hK, hk])
    · rw [hm₂]; exact bytesAt_copied _ _ _

/-- The first `n` of `k` bytes. -/
theorem bytesAt_take (m : Mem) (p : Addr) {n k : Nat} (h : n ≤ k) :
    Spec.Sha256.bytesAt m p n = (Spec.Sha256.bytesAt m p k).take n := by
  rw [show k = n + (k - n) by omega_using [h], Proof.Hmac.Common.bytesAt_add, List.take_left']
  simp [Spec.Sha256.bytesAt]

theorem copyBytes_ok {src dst : Reg} {S D : BitVec 32} {SA DA : Addr} {so d Q : Nat} (hdr : dst ≠ .eax)
    (hsr : src ≠ .eax) (hSA : ∀ j, j + 4 ≤ Q → addr S (so + j) = SA + BitVec.ofNat 64 j)
    (hDA : ∀ j, j + 4 ≤ Q → addr D (d + j) = DA + BitVec.ofNat 64 j)
    (hsep : Region.Disjoint ⟨SA, Q⟩ ⟨DA, Q⟩) (h4 : 4 ≤ Q) (hQ : Q < 2 ^ 32) {u : State}
    (hs : u.gpr src = S) (hd : u.gpr dst = D)
    (hr : ∀ j, j + 4 ≤ Q → InRegions (u.rd ++ u.wr) (SA + BitVec.ofNat 64 j) 4)
    (hw : ∀ j, j + 4 ≤ Q → InRegions u.wr (DA + BitVec.ofNat 64 j) 4) :
    WP isa (.block (Cfg.copyBytes Q src so dst d)) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧
      Frame [⟨DA, Q⟩] u.mem u'.mem ∧ Spec.Sha256.bytesAt u'.mem DA Q = Spec.Sha256.bytesAt u.mem SA Q := by
  rw [Cfg.copyBytes, WP.block_append_iff]
  have hK : 4 * (Q / 4) ≤ Q := Nat.mul_div_le Q 4
  refine WP.mono (copyN_ok (S := S) (D := D) (SA := SA) (DA := DA) (so := so) (d := d) (K := Q / 4) hdr hsr
      (fun j hj => hSA (4 * j) (by omega_using [hj])) (fun j hj => hDA (4 * j) (by omega_using [hj]))
      ((hsep.sub_left (Region.sub_prefix (by omega_using []))).sub_right (Region.sub_prefix (by omega_using []))) (by omega_using [hQ])
      (Q / 4) (Nat.le_refl _) u hs hd
      (fun j hj => hr (4 * j) (by omega_using [hj])) fun j hj => hw (4 * j) (by omega_using [hj]))
    fun u₁ ⟨hrd₁, hwr₁, hg₁, hf₁, hb₁⟩ => ?_
  have hf₁' : Frame [⟨DA, Q⟩] u.mem u₁.mem :=
    hf₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_using [])⟩
  by_cases hm : Q % 4 = 0
  · simp only [hm, ite_true]
    have e : 4 * (Q / 4) = Q := by omega_using [hm]
    rw [e] at hb₁
    exact WP.block_nil ⟨hrd₁, hwr₁, hg₁, hf₁', hb₁⟩
  · simp only [hm, ite_false]
    have eS : addr S (so + Q - 4) = SA + BitVec.ofNat 64 (Q - 4) := by
      rw [show so + Q - 4 = so + (Q - 4) by omega_using [h4]]; exact hSA (Q - 4) (by omega_using [h4])
    have eD : addr D (d + Q - 4) = DA + BitVec.ofNat 64 (Q - 4) := by
      rw [show d + Q - 4 = d + (Q - 4) by omega_using [h4]]; exact hDA (Q - 4) (by omega_using [h4])
    refine WP.mono (copyW_ok (u := u₁) (so := so + Q - 4) (d := d + Q - 4) (hg₁ _ hsr ▸ hs) (hg₁ _ hdr ▸ hd)
      (by rw [eS, hrd₁, hwr₁]; exact hr (Q - 4) (by omega_using [h4])) (by rw [eD, hwr₁]; exact hw (Q - 4) (by omega_using [h4])) hdr)
      fun u₂ ⟨hrd₂, hwr₂, hg₂, hm₂⟩ => ?_
    rw [eS, eD] at hm₂
    have hf₂ : Frame [⟨DA + BitVec.ofNat 64 (Q - 4), 4⟩] u₁.mem u₂.mem := by
      rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    refine ⟨hrd₂.trans hrd₁, hwr₂.trans hwr₁, fun r hr => (hg₂ r hr).trans (hg₁ r hr),
      hf₁'.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by omega_using [h4])⟩), ?_⟩
    rw [show Q = (Q - 4) + 4 by omega_using [h4], Proof.Hmac.Common.bytesAt_add, Proof.Hmac.Common.bytesAt_add]
    congr 1
    · rw [bytesAt_frame hf₂ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint _ (by omega_using []) (by omega_using [hQ])) (by omega_using [hQ]),
        bytesAt_take _ _ (k := 4 * (Q / 4)) (by omega_using []), hb₁, ← bytesAt_take _ _ (by omega_using [])]
    · rw [hm₂, bytesAt_copied]
      exact bytesAt_frame hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hsep.sub_left (Offset.sub_base _ (by omega_using [h4]))).sub_right (Region.sub_prefix (by omega_using [])))
        (by omega_using [])

end VG.Proof.Ecdsa.Rfc6979.X86

end

end

/-! ### `Ecdsa.Rfc6979.X86.Steps`, which this module and modules that import it used -/

section

/-! ### `Ecdsa.Rfc6979.X86.Msg`, which only this module used -/

section

/-!
# Deterministic ECDSA on x86 (32-bit): the messages of steps d, f and h.3

`b`, and `‖ d ‖ h` if `full`, at `scratch + 2256` (`msg_ok`), as on x86-64
(`Proof/Ecdsa/Rfc6979/X86_64/Msg.lean`): the byte `b` (`byte_ok`), then the
private key and `h` copied (`tail_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.Rfc6979.X86
open VG.Impl.Pbkdf2.Stream.X86 (at_)

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `mov byte [m], r`. -/
theorem wp_store8 {r : Reg8} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hw : InRegions s.wr a 1)
    (k : ∀ t, Mupd s t (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) t Q) :
    WP isa (.block (.store8 m r :: is)) s Q :=
  cons (s' := { s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8) })
    (by simp only [exec, ha, State.store8, hw, ite_true]) (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

end

/-- `Q` bytes copied to `scratch + d` by `copyBytes`, with `Ctx` kept. -/
theorem copyB_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : BitVec 32} {SA : Addr}
    (hs : u.gpr src = S) (hsr : src ≠ .eax) (hdi : u.gpr .edi = L.sc) {so d Q : Nat} (h4 : 4 ≤ Q)
    (hd : d + Q ≤ 8192) (hSA : ∀ j, j + 4 ≤ Q → addr S (so + j) = SA + BitVec.ofNat 64 j)
    (hr : ∀ j, j + 4 ≤ Q → InRegions (u.rd ++ u.wr) (SA + BitVec.ofNat 64 j) 4)
    (hsep : Region.Disjoint ⟨SA, Q⟩ ⟨L.scr + BitVec.ofNat 64 d, Q⟩) :
    WP isa (.block (Cfg.copyBytes Q src so .edi d)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.scr + BitVec.ofNat 64 d, Q⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 d) Q = Spec.Sha256.bytesAt u.mem SA Q :=
  have nc := hL.nc
  WP.mono_syms (copyBytes_ok (by decide) hsr hSA (fun j hj => by rw [addr_eq (by omega_arith), Offset.add_add]) hsep h4
      (by omega_arith) hs hdi hr fun j hj => by rw [Offset.add_add]; exact hc.inScrW (by omega_arith))
    fun u' ⟨hrd, hwr, hg, hf, hb⟩ hsy =>
    ⟨hc.keep (hsy := hsy) hL hrd hwr (hg _ (by decide)) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L hd), hg, hf, hb⟩

/-- The pointers: `scratch` in `edi`, `d` in `esi`. -/
theorem ptrs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.msgPtrs) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .edi = L.sc ∧
      u.gpr .esi = L.a1 := by
  rw [Cfg.msgPtrs, show ([.mov .edi (argM 4), .mov .esi (argM 1)] : List Instr) =
    [.mov .edi (argM 4)] ++ [.mov .esi (argM 1)] from rfl, WP.block_append_iff]
  refine WP.mono (arg_ok hL hc (d := .edi) (by decide) (i := 4) (by omega_arith)) fun u₁ h₁ => ?_
  refine WP.mono (arg_ok hL h₁.ctx (d := .esi) (by decide) (i := 1) (by omega_arith)) fun u₂ h₂ =>
    ⟨h₂.ctx, by rw [h₂.mem, h₁.mem], by rw [h₂.keep _ (by decide), h₁.val]; rfl, h₂.val⟩

/-- The byte `b` at `scratch + 2256`, with `scratch` in `edi`. -/
theorem byte_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .edi = L.sc) (b : Nat) :
    WP isa (.block ([.mov .eax (.imm (BitVec.ofNat 32 b)), .store8 (at_ .edi sMsg) .al] : List Instr)) t
      fun u => Ctx L g m₀ u ∧ (∀ r, r ≠ .eax → u.gpr r = t.gpr r) ∧
        Frame [⟨L.scr + BitVec.ofNat 64 2256, 1⟩] t.mem u.mem ∧
        Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) 1 = [BitVec.ofNat 8 b] := by
  have nc := hL.nc
  have ea : addr L.sc 2256 = L.scr + BitVec.ofNat 64 2256 := addr_eq (by omega_arith)
  refine wp_movi fun u₃ v₃ => wp_store8 (a := L.scr + BitVec.ofNat 64 2256)
    (by show addr (u₃.gpr .edi) 2256 = _; rw [v₃.other .edi (by decide), hdi, ea])
    (by rw [v₃.wr]; exact hc.inScrW (o := 2256) (n := 1) (by omega_arith)) fun u₄ v₄ => WP.block_nil ?_
  have hb8 : (u₃.gpr Reg8.al.reg).setWidth 8 = BitVec.ofNat 8 b := by
    rw [show Reg8.al.reg = .eax from rfl, v₃.gpr]
    apply BitVec.eq_of_toNat_eq; simp
  rw [hb8] at v₄
  have hm₄ : u₄.mem = t.mem.writeW (L.scr + BitVec.ofNat 64 2256) (BitVec.ofNat 8 b) := by
    rw [v₄.mem, v₃.mem]
  have hf₃ : Frame [⟨L.scr + BitVec.ofNat 64 2256, 1⟩] t.mem u₄.mem := by
    rw [hm₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.keep (hsy := by rw [v₄.syms, v₃.syms]) hL (by rw [v₄.rd, v₃.rd]) (by rw [v₄.wr, v₃.wr])
      (by rw [v₄.gpr, v₃.other _ (by decide)]) hf₃
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by omega_arith)),
    fun r hr => by rw [v₄.gpr, v₃.other _ hr], hf₃, ?_⟩
  show [u₄.mem (L.scr + BitVec.ofNat 64 2256 + BitVec.ofNat 64 0)] = _
  rw [BitVec.add_zero, hm₄, WriteBytes.writeW8_apply]; simp

/-- `d ‖ h`, `Q` bytes each, at `scratch + a`, with `scratch` in `edi` and
`d` in `esi`, `h` at `ho` in the frame. -/
theorem tail_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hdi : u.gpr .edi = L.sc) (hsi : u.gpr .esi = L.a1)
    {a Q ho : Nat} (ha : a + 2 * Q ≤ 8192) (h4 : 4 ≤ Q) (hQ : Q ≤ 66) (hho : 76 + ho + Q ≤ 588)
    (hq : Q ≤ L.q) :
    WP isa (.block (Cfg.copyBytes Q .esi 0 .edi a ++ Cfg.copyBytes Q .esp ho .edi (a + Q))) u
      fun u' => Ctx L g m₀ u' ∧ Frame [⟨L.scr + BitVec.ofNat 64 a, 2 * Q⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 a) (2 * Q) =
          Spec.Sha256.bytesAt u.mem L.d Q ++
            Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (76 + ho)) Q := by
  have nc := hL.nc
  have nd := hL.nd
  rw [WP.block_append_iff]
  refine WP.mono (copyB_ok hL hc (S := L.a1) (SA := L.d) (src := .esi) hsi (by decide) hdi (so := 0) (d := a) h4
    (by omega_arith) (fun j hj => by rw [addr_eq (by omega_arith), Nat.zero_add])
    (fun j hj => hc.inD (by omega_arith) (by omega_arith))
    ((hL.dc.sub_left (Region.sub_prefix hq)).sub_right (Offset.sub_base _ (by omega_arith))))
    fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  have hdi₂ : u₂.gpr .edi = L.sc := (hg₂ _ (by decide)).trans hdi
  refine WP.mono (copyB_ok hL hc₂ (S := L.F) (SA := L.B + BitVec.ofNat 64 (76 + ho)) (src := .esp) hc₂.esp
    (by decide) hdi₂ (so := ho) (d := a + Q) h4 (by omega_arith)
    (fun j hj => by rw [hL.addrF (by omega_arith), Offset.add_add, Nat.add_assoc])
    (fun j hj => by rw [Offset.add_add]; exact hc₂.inFr (by omega_arith) (by omega_arith) hL)
    (hL.stk_scr (by omega_arith) (by omega_arith))) fun u₃ ⟨hc₃, _, hf₃, hb₃⟩ => ?_
  refine ⟨hc₃, ?_, ?_⟩
  · refine (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_arith) (by omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_arith) (by omega_arith)
  · rw [show 2 * Q = Q + Q by omega_arith, Proof.Hmac.Common.bytesAt_add _ _ Q Q, Offset.add_add, hb₃,
      bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith), hb₂]
    refine congrArg (fun y => Spec.Sha256.bytesAt u.mem L.d Q ++ y) ?_
    exact bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by omega_arith) (by omega_arith)) (by omega_arith)

variable {P : RfcHash}

/-- `h` in the frame. -/
abbrev hOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 (76 + (cfgOf P).fHo)) P.Q

/-- The length of the message. -/
abbrev mlen (P : RfcHash) (full : Bool) : Nat := if full then 1 + 2 * P.Q else 1

/-- The message `b` (`‖ d ‖ h` if `full`, `Q` bytes each) at `scratch + 2256`. -/
theorem msg_ok (hL : L.Ok) (hq : L.q = P.Q) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .edi = L.sc)
    (hsi : t.gpr .esi = L.a1) (b : Nat) (full : Bool) :
    WP isa (.block ((cfgOf P).msg b full)) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2256, 1 + 2 * P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.scr + BitVec.ofNat 64 2256) (mlen P full) =
        [BitVec.ofNat 8 b] ++ (if full then Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem else []) := by
  have hQ := P.sizes
  have hlen : (cfgOf P).len = P.Q := rfl
  have hho : 76 + (cfgOf P).fHo + P.Q ≤ 588 := by
    simp only [Cfg.fHo, cfgOf]
    rcases Bool.eq_false_or_eq_true P.R.big with h | h <;>
      simp only [h, fX, fH, ite_true, ite_false, Bool.false_eq_true] <;> nums
  cases full
  · simp only [Cfg.msg, Bool.false_eq_true, ite_false, List.append_nil, mlen]
    refine WP.mono (byte_ok hL hc hdi b) fun u ⟨hcu, _, hf, hb⟩ =>
      ⟨hcu, hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩, hb⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub _ (by omega_arith) (by omega_arith)
  · simp only [Cfg.msg, ite_true, sMsg, mlen]
    rw [WP.block_append_iff]
    refine WP.mono (byte_ok hL hc hdi b) fun u ⟨hcu, hg, hf, hb⟩ => ?_
    have hdi' : u.gpr .edi = L.sc := (hg _ (by decide)).trans hdi
    have hsi' : u.gpr .esi = L.a1 := (hg _ (by decide)).trans hsi
    refine WP.mono (tail_ok hL hcu hdi' hsi' (a := 2256 + 1) (Q := (cfgOf P).len) (ho := (cfgOf P).fHo)
      (by show _ + 2 * P.Q ≤ _; nums) (by show 4 ≤ P.Q; nums) (by show P.Q ≤ 66; nums) hho (by rw [hq]; rfl))
      fun u' ⟨hcu', hf', hb'⟩ => ⟨hcu', ?_, ?_⟩
    · refine (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (hf'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.sub _ (by omega_arith) (by omega_arith)
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.sub _ (by omega_arith) (by rw [hlen]; nums)
    · rw [Proof.Hmac.Common.bytesAt_add _ _ 1 (2 * P.Q), Offset.add_add]
      have hb'' : Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 (2256 + 1)) (2 * P.Q) =
          Spec.Sha256.bytesAt u.mem L.d P.Q ++ hOf P L u.mem := hb'
      rw [hb'', bytesAt_frame hf' (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by nums)) (by omega_arith), hb]
      refine congrArg ([BitVec.ofNat 8 b] ++ ·) ?_
      have hdq : Spec.Sha256.bytesAt u.mem L.d P.Q = Spec.Sha256.bytesAt t.mem L.d P.Q :=
        bytesAt_frame hf (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hL.dc.sub_left (Region.sub_prefix (by rw [hq]))).sub_right (Offset.sub_base _ (by omega_arith)))
          (by nums)
      rw [hdq]
      refine congrArg (Spec.Sha256.bytesAt t.mem L.d P.Q ++ ·) ?_
      exact bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hL.stk_scr (by omega_arith) (by omega_arith)) (by nums)

end VG.Proof.Ecdsa.Rfc6979.X86

end

end


/-!
# Deterministic ECDSA on x86 (32-bit): the steps on `K` and `V`

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Prep.lean`): each HMAC with the
key `K` and `V` (both of the digest length `D`, at the start of the frame)
is HMAC's states for `K` (by `init`, then saved, or restored from the copy),
the table's `update` with `V` and, for a new `K`, with the message at
`scratch + 2256`, then `finalize` into `V` (`vfin_ok`) or `K` (`vmfin_ok`):
`V = HMAC_K(V)` from a new `K`, saving the states (`hmacVS_ok`), or from the
saved ones (`hmacVR_ok`); `K = HMAC_K(V ‖ m)` (`hmacKB_ok`). With the message
`b ‖ d ‖ h` or `b` (`msg_ok`): steps d–e and f–g (`rekeyFull_ok`) and h.3
(`rekey_ok`). They change only `scratch`, the stack below the frame, `K` and
`V` (`KVW`).

The copies of HMAC's two states are the byte loop (`cpLoop_ok`,
`Proof.Bignum.X86.copyBytes_ok`) over their 384 bytes, from `scratch` to
`scratch + 3072` (`save_ok`) and back (`restore_ok`). A state moves with its
bytes (`RfcHash.reprOK`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.Rfc6979.X86

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## The byte loop -/

/-- The loop's `n > 0` bytes from `S` (in `esi`) to `D` (in `ebx`), apart,
the count in `ecx`, into a safe region: `Ctx` kept, and the bytes copied. -/
theorem cpLoop_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {S D : BitVec 32} {n : Nat} (hn : 0 < n)
    (hn32 : n < 2 ^ 32) (hS : S.toNat + n ≤ 2 ^ 32) (hD : D.toNat + n ≤ 2 ^ 32)
    (hr : InRegions (u.rd ++ u.wr) (S.setWidth 64) n) (hw : InRegions u.wr (D.setWidth 64) n)
    (hsep : Region.Disjoint ⟨S.setWidth 64, n⟩ ⟨D.setWidth 64, n⟩) (hsafe : Safe L ⟨D.setWidth 64, n⟩)
    (hsi : u.gpr .esi = S) (hbx : u.gpr .ebx = D) (hcx : u.gpr .ecx = BitVec.ofNat 32 n) :
    WP isa Cfg.cpLoop u fun u' => Ctx L g m₀ u' ∧ Frame [⟨D.setWidth 64, n⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (D.setWidth 64) n = Spec.Sha256.bytesAt u.mem (S.setWidth 64) n ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .esi → r ≠ .ecx → u'.gpr r = u.gpr r) := by
  refine WP.mono_syms (Proof.Bignum.X86.copyBytes_ok u
    (Proof.Bignum.X86.copyCtx_of_regions u S D hn32 hS hD hr hw hsep) hn hsi hbx hcx) fun u' I hsy => ?_
  have hf : Frame [⟨D.setWidth 64, n⟩] u.mem u'.mem := I.frame hD
  have hk := I.rest
  have hrest : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .esi → r ≠ .ecx → u'.gpr r = u.gpr r := by
    intro r h₁ h₂ h₃ h₄
    refine hk.1 r ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h | h) <;> contradiction
  refine ⟨hc.keep (hsy := hsy) hL hk.2.1 hk.2.2 (hk.1 .esp (by decide)) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsafe), hf, ?_, hrest⟩
  simp only [Spec.Sha256.bytesAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  have e := I.copied j hj
  rw [Proof.Bignum.X86.byteAddr_add (by omega_using [hD, hj]), Proof.Bignum.X86.byteAddr_add (by omega_using [hS, hj])] at e
  exact e

/-! ## The copies of HMAC's states -/

/-- A copy at `scratch + 3072` of HMAC's inner and outer states for the block key `k0`. -/
def SavedB (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) (k0 : List Byte) : Prop :=
  P.ok.hH.SH.Repr m (L.scr + BitVec.ofNat 64 3072) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad) ∧
    P.ok.hH.SH.Repr m (L.scr + BitVec.ofNat 64 3264) (Spec.Hmac.xorPad k0 Spec.Hmac.opad)

/-- The copy's region. -/
abbrev SaveR {dn : Nat} (L : Lay dn) : Region := ⟨L.scr + BitVec.ofNat 64 3072, 384⟩

theorem state_le (P : RfcHash) : P.ok.hH.SH.stateBytes ≤ 192 := by rw [P.ok.hH.hS]; nums

/-- The bytes of `n` at `p` in `m'` are those at `q` in `m`, one by one. -/
theorem byte_of_bytesAt {m m' : Mem} {p q : Addr} {n : Nat}
    (h : Spec.Sha256.bytesAt m' p n = Spec.Sha256.bytesAt m q n) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (q + BitVec.ofNat 64 i) := by
  have := congrArg (·[i]?) h
  simpa [Spec.Sha256.bytesAt, hi] using this

/-- The copy survives memory that changed apart from it. -/
theorem SavedB.frame {m m' : Mem} {k0 : List Byte} (hS : SavedB P L m k0) {ws : List Region}
    (hf : Frame ws m m') (hd : ∀ r ∈ ws, Region.Disjoint (SaveR L) r) : SavedB P L m' k0 := by
  have hle := state_le P
  refine ⟨P.reprOK _ _ _ _ _ (fun i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 3072, 192⟩) hf
      (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega_using []) (by omega_using []))) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega_using [hle, hi])) hS.1,
    P.reprOK _ _ _ _ _ (fun i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 3264, 192⟩) hf
      (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega_using []) (by omega_using []))) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega_using [hle, hi])) hS.2⟩

/-- What HMAC's functions write is apart from the copy. -/
theorem W_save (hL : L.Ok) : ∀ r ∈ W L, Region.Disjoint (SaveR L) r := by
  intro r hr
  simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (Offset.disjoint_base _ (by decide) (by decide))
  · exact ((hL.kc.sub_left (Region.sub_prefix (by omega_using []))).sub_right (Offset.sub_base _ (by decide))).symm

/-- The arguments of a copy of the states: `esi`, `ebx` and `ecx = 384`. -/
theorem copyArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (toSave : Bool) :
    WP isa (.block (Cfg.copyArgs toSave)) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧
      u.gpr .esi = L.sc + BitVec.ofNat 32 (if toSave then sInner else sSave) ∧
      u.gpr .ebx = L.sc + BitVec.ofNat 32 (if toSave then sSave else sInner) ∧ u.gpr .ecx = 384 := by
  have k : ∀ a b : Nat, WP isa (.block (Cfg.scr .esi a ++ Cfg.scr .ebx b ++ ([.mov .ecx (.imm 384)] : List Instr))) t
      fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .esi = L.sc + BitVec.ofNat 32 a ∧
        u.gpr .ebx = L.sc + BitVec.ofNat 32 b ∧ u.gpr .ecx = 384 := fun a b => by
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (scr_ok hL hc (d := .esi) (by decide) a) fun u₁ h₁ => ?_
    refine WP.mono (scr_ok hL h₁.ctx (d := .ebx) (by decide) b) fun u₂ h₂ => ?_
    refine WP.mono (movi_ok hL h₂.ctx (d := .ecx) (by decide) 384) fun u₃ h₃ => ?_
    exact ⟨h₃.ctx, by rw [h₃.mem, h₂.mem, h₁.mem], by rw [h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val],
      by rw [h₃.keep _ (by decide), h₂.val], h₃.val⟩
  cases toSave
  · exact k sSave sInner
  · exact k sInner sSave

/-- The copy of 384 bytes of `scratch` from `a` to `b`. -/
theorem copyS_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (toSave : Bool) {a b : Nat}
    (ha : a = if toSave then sInner else sSave) (hb : b = if toSave then sSave else sInner) :
    WP isa (.seq (.block (Cfg.copyArgs toSave)) Cfg.cpLoop) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 b, 384⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 b) 384 =
        Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 a) 384 := by
  have nc := hL.nc
  have hab : (a = 0 ∧ b = 3072) ∨ (a = 3072 ∧ b = 0) := by
    cases toSave <;> subst ha hb <;> decide
  refine WP.seq (WP.mono (copyArgs_ok hL hc toSave) fun u ⟨hcu, hmu, hsi, hbx, hcx⟩ => ?_)
  rw [← ha] at hsi
  rw [← hb] at hbx
  have ea : (L.sc + BitVec.ofNat 32 a).setWidth 64 = L.scr + BitVec.ofNat 64 a := hL.scrv (by omega_using [hab])
  have eb : (L.sc + BitVec.ofNat 32 b).setWidth 64 = L.scr + BitVec.ofNat 64 b := hL.scrv (by omega_using [hab])
  refine WP.mono (cpLoop_ok hL hcu (n := 384) (by decide) (by decide) (by rw [hL.scrN (by omega_using [hab])]; omega_using [nc, hab])
    (by rw [hL.scrN (by omega_using [hab])]; omega_using [nc, hab]) (by rw [ea]; exact hcu.inScr (by omega_using [hab]))
    (by rw [eb]; exact hcu.inScrW (by omega_using [hab]))
    (by rw [ea, eb]; exact Offset.disjoint _ (by omega_using [hab]) (by omega_using [hab]) (by omega_using [hab]))
    (by rw [eb]; exact safe_scr L (by omega_using [hab])) hsi hbx hcx) fun u' ⟨hc', hf', hb', _⟩ => ?_
  rw [ea, eb, hmu] at *
  exact ⟨hc', hf', hb'⟩

/-- After `init`: the states copied to `scratch + 3072`, and `St` kept. -/
theorem save_ok (hL : L.Ok) {k0 : List Byte} {u : State} (hu : St P L g m₀ k0 [] u) :
    WP isa Cfg.save u fun u' => St P L g m₀ k0 [] u' ∧ SavedB P L u'.mem k0 ∧
      Frame [SaveR L] u.mem u'.mem := by
  have hle := state_le P
  refine WP.mono (copyS_ok hL hu.ctx true (a := 0) (b := 3072) rfl rfl) fun u' ⟨hc', hf', hb'⟩ => ?_
  have hst : ∀ o, o + 192 ≤ 384 → ∀ i < P.ok.hH.SH.stateBytes,
      u'.mem (L.scr + BitVec.ofNat 64 o + BitVec.ofNat 64 i) = u.mem (L.scr + BitVec.ofNat 64 o + BitVec.ofNat 64 i) :=
    fun o ho i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 o, 192⟩) hf'
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_using [ho]) (by omega_using [ho]) (by omega_using [])) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega_using [hle, hi])
  have hin := hu.inner
  rw [List.append_nil] at hin
  refine ⟨⟨hc', hu.klen, hu.tlen, ?_, ?_⟩, ⟨?_, ?_⟩, hf'⟩
  · rw [List.append_nil]; exact P.reprOK _ _ _ _ _ (fun i hi => hst 0 (by decide) i hi) hin
  · exact P.reprOK _ _ _ _ _ (fun i hi => hst 192 (by decide) i hi) hu.outer
  · exact P.reprOK _ _ _ _ _ (fun i hi => byte_of_bytesAt hb' (by omega_using [hle, hi])) hin
  · exact P.reprOK _ _ _ _ _ (fun i hi => by
      have h := byte_of_bytesAt hb' (i := 192 + i) (by omega_using [hle, hi])
      have e1 : L.scr + BitVec.ofNat 64 3264 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 3072 + BitVec.ofNat 64 (192 + i) := by
        rw [Offset.add_add, Offset.add_add]; congr 2; omega_using []
      have e2 : L.scr + BitVec.ofNat 64 192 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 0 + BitVec.ofNat 64 (192 + i) := by
        rw [Offset.add_add, Offset.add_add, Nat.zero_add]
      rw [e1, e2]; exact h) hu.outer

/-- The copy back: HMAC's states for the block key `k0`, and the copy kept. -/
theorem restore_ok (hL : L.Ok) {k0 : List Byte} {t : State} (hc : Ctx L g m₀ t) (hS : SavedB P L t.mem k0)
    (hk : k0.length = P.F.H.B) :
    WP isa Cfg.restore t fun u => St P L g m₀ k0 [] u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 0, 384⟩] t.mem u.mem ∧ SavedB P L u.mem k0 := by
  have hle := state_le P
  refine WP.mono (copyS_ok hL hc false (a := 3072) (b := 0) rfl rfl) fun u ⟨hcu, hf, hb⟩ => ?_
  refine ⟨⟨hcu, hk, by simp, ?_, ?_⟩, hf, hS.frame hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (by decide) (by decide) (by decide)⟩
  · rw [List.append_nil]; exact P.reprOK _ _ _ _ _ (fun i hi => byte_of_bytesAt hb (by omega_using [hle, hi])) hS.1
  · exact P.reprOK _ _ _ _ _ (fun i hi => by
      have h := byte_of_bytesAt hb (i := 192 + i) (by omega_using [hle, hi])
      have e1 : L.scr + BitVec.ofNat 64 192 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 0 + BitVec.ofNat 64 (192 + i) := by
        rw [Offset.add_add, Offset.add_add, Nat.zero_add]
      have e2 : L.scr + BitVec.ofNat 64 3264 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 3072 + BitVec.ofNat 64 (192 + i) := by
        rw [Offset.add_add, Offset.add_add]; congr 2; omega_using []
      rw [e1, e2]; exact h) hS.2

/-! ## `K` and `V` -/

/-- `K` and `V` (of the hash function's output length), in the frame. -/
abbrev kOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte := keyOf P L m
abbrev vOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 140) P.F.H.D

/-- A copy of HMAC's states for the key `K`. -/
abbrev SavedK (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) (K : List Byte) : Prop :=
  SavedB P L m (Spec.Hmac.blockKey P.ok.hH.SH.H K)

/-- HMAC with a key is HMAC with its block key. -/
theorem mac_eq (P : RfcHash) (K t : List Byte) :
    P.mac K t = Spec.Hmac.hmacBlockKey P.ok.hH.SH.H (Spec.Hmac.blockKey P.ok.hH.SH.H K) t := rfl

/-- HMAC's output is the hash function's. -/
theorem mac_length (P : RfcHash) (K t : List Byte) : (P.mac K t).length = P.F.H.D := by
  simp only [RfcHash.mac, Spec.Hmac.hmac, Spec.Hmac.hmacBlockKey, P.macLen]

/-- What the steps change: `scratch`, the stack below the frame, `K` and `V`. -/
abbrev KVW {dn : Nat} (L : Lay dn) : List Region := [L.SCR, ⟨L.B, 204⟩]

theorem kvw_of {rs : List Region} (h : ∀ r ∈ rs, Region.Sub r L.SCR ∨ Region.Sub r ⟨L.B, 204⟩) :
    ∀ r ∈ rs, ∃ r' ∈ KVW L, Region.Sub r r' := fun r hr => by
  rcases h r hr with h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨⟨L.B, 204⟩, by simp, h⟩

/-- HMAC's writes, and the MAC's place `dst` (`K` or `V`), within `KVW`. -/
theorem wd_kvw {dst : Nat} (h : dst + P.F.H.D ≤ 128) :
    ∀ r ∈ W L ++ [⟨L.B + BitVec.ofNat 64 (76 + dst), P.F.H.D⟩], ∃ r' ∈ KVW L, Region.Sub r r' :=
  kvw_of fun r hr => by
    simp only [W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (Region.sub_prefix (by omega_using []))
    · exact .inr (Region.sub_prefix (by omega_using []))
    · exact .inr (Offset.sub_base _ (by omega_using [h]))

/-- The `D` bytes at `o` in the frame survive HMAC's writes and the MAC's at `dst`. -/
theorem kv_frame {dst : Nat} (hL : L.Ok) {m m' : Mem}
    (hf : Frame (W L ++ [⟨L.B + BitVec.ofNat 64 (76 + dst), P.F.H.D⟩]) m m')
    {o : Nat} (ho : 76 ≤ o) (hod : o + P.F.H.D ≤ 76 + dst ∨ 76 + dst + P.F.H.D ≤ o) (hoe : o + P.F.H.D ≤ 588)
    (hdst : dst + P.F.H.D ≤ 128) :
    Spec.Sha256.bytesAt m' (L.B + BitVec.ofNat 64 o) P.F.H.D = Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 o) P.F.H.D :=
  bytesAt_frame hf (fun r hr => by
    simp only [W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.stk_scr0 (by omega_using [hoe]) (by decide)
    · exact Offset.disjoint_base _ ho (by nums)
    · exact Offset.disjoint _ hod (by omega_using [hoe]) (by omega_using [hdst])) (by nums)

/-- What HMAC's functions write, with the MAC at `dst` in the frame, is apart from the copy. -/
theorem wd_save (hL : L.Ok) {dst : Nat} (hdst : dst + P.F.H.D ≤ 128) :
    ∀ r ∈ W L ++ [⟨L.B + BitVec.ofNat 64 (76 + dst), P.F.H.D⟩], Region.Disjoint (SaveR L) r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact W_save hL r hr
  · simp only [List.mem_singleton] at hr; subst hr
    exact (hL.stk_scr (by nums) (by decide)).symm

/-- The message's bytes survive HMAC's writes. -/
theorem msg_W (hL : L.Ok) {m m' : Mem} (hf : Frame (W L) m m') {len : Nat} (hlen : 2256 + len ≤ 8192) :
    Spec.Sha256.bytesAt m' (L.scr + BitVec.ofNat 64 2256) len = Spec.Sha256.bytesAt m (L.scr + BitVec.ofNat 64 2256) len :=
  bytesAt_frame hf (fun r hr => by
    simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [hlen])
    · exact (hL.low_scr (by omega_using [hlen])).symm) (by omega_using [hlen])

/-- `update` with `V`, then `finalize` into the frame at `dst`: `HMAC(K₀, V)`. -/
theorem vfin_ok (hL : L.Ok) (hT : TabL P L) {k0 : List Byte} {u : State} (hu : St P L g m₀ k0 [] u) {dst : Nat}
    (hdst : dst + P.F.H.D ≤ 128) :
    WP isa (.seq (cfgOf P).updV ((cfgOf P).fin 0 dst)) u fun u' => Ctx L g m₀ u' ∧
      Frame (W L ++ [⟨L.B + BitVec.ofNat 64 (76 + dst), P.F.H.D⟩]) u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (76 + dst)) P.F.H.D =
        Spec.Hmac.hmacBlockKey P.ok.hH.SH.H k0 (vOf P L u.mem) := by
  refine WP.seq (WP.mono (updV_step hL hT hu) fun w ⟨hw, hfw⟩ => ?_)
  refine WP.mono (fin_step hL hT hw (len := 0) (dst := dst) (by simp [Spec.Sha256.bytesAt]) (by decide) hdst)
    fun u' ⟨hc', hf', hm'⟩ => ⟨hc', ?_, hm'⟩
  exact (hfw.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩).trans hf'

/-- `update` with `V`, then with the message's `len` bytes, then `finalize`
into `K`: `HMAC(K₀, V ‖ m)`. -/
theorem vmfin_ok (hL : L.Ok) (hT : TabL P L) {k0 : List Byte} {u : State} (hu : St P L g m₀ k0 [] u) {len : Nat}
    (hlen : len ≤ 256) :
    WP isa (.seq (cfgOf P).updV (.seq ((cfgOf P).updM len) ((cfgOf P).fin len fK))) u fun u' => Ctx L g m₀ u' ∧
      Frame (W L ++ [⟨L.B + BitVec.ofNat 64 (76 + fK), P.F.H.D⟩]) u.mem u'.mem ∧
      kOf P L u'.mem = Spec.Hmac.hmacBlockKey P.ok.hH.SH.H k0
        (vOf P L u.mem ++ Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) len) := by
  refine WP.seq (WP.mono (updV_step hL hT hu) fun w ⟨hw, hfw⟩ => ?_)
  refine WP.seq (WP.mono (updM_step hL hT hw (by simp [Spec.Sha256.bytesAt]) hlen) fun w' ⟨hw', hfw'⟩ => ?_)
  refine WP.mono (fin_step hL hT hw' (len := len) (dst := fK)
    (by simp [Spec.Sha256.bytesAt]) hlen (by simp only [fK]; nums)) fun u' ⟨hc', hf', hm'⟩ => ⟨hc', ?_, ?_⟩
  · exact ((hfw.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩).trans
      (hfw'.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩)).trans hf'
  · show Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 76) P.F.H.D = _
    rw [show L.B + BitVec.ofNat 64 76 = L.B + BitVec.ofNat 64 (76 + fK) from rfl, hm',
      show sMsg = 2256 from rfl, msg_W hL hfw (len := len) (by omega_using [hlen])]

/-- `V`'s and `K`'s bytes survive HMAC's writes and the copy's. -/
theorem kv_WS (hL : L.Ok) {m m' : Mem} (hW : Frame (W L ++ [SaveR L]) m m') {o : Nat} (ho : 76 ≤ o)
    (hoe : o + P.F.H.D ≤ 204) :
    Spec.Sha256.bytesAt m' (L.B + BitVec.ofNat 64 o) P.F.H.D = Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 o) P.F.H.D :=
  bytesAt_frame hW (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_scr0 (by omega_using [hoe]) (by decide)
      · exact Offset.disjoint_base _ ho (by nums)
    · simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by omega_using [hoe]) (by decide)) (by nums)

/-- `V = HMAC_K(V)`, HMAC's states for `K` saved. -/
theorem hmacVS_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).hmacVS t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = kOf P L t.mem ∧ vOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem) ∧
      SavedK P L t'.mem (kOf P L t'.mem) := by
  refine WP.seq (WP.mono (init_step hL hT hc) fun u ⟨hu, hfu⟩ => ?_)
  refine WP.seq (WP.mono (save_ok hL hu) fun u' ⟨hu', hS, hf'⟩ => ?_)
  refine WP.mono (vfin_ok hL hT hu' (dst := fV) (by simp only [fV]; nums)) fun t' ⟨hc', hf'', hm⟩ => ?_
  have hW : Frame (W L ++ [SaveR L]) t.mem u'.mem :=
    (hfu.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩).trans
      (hf'.sub fun r hr => ⟨r, List.mem_append_right _ hr, sub_refl _⟩)
  have hk : kOf P L t'.mem = kOf P L t.mem := by
    show Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 76) P.F.H.D = _
    rw [kv_frame hL hf'' (o := 76) (by decide) (.inl (by simp only [fV]; nums)) (by nums) (by simp only [fV]; nums)]
    exact kv_WS hL hW (by decide) (by nums)
  have hv : vOf P L u'.mem = vOf P L t.mem := kv_WS hL hW (by decide) (by nums)
  refine ⟨hc', ?_, hk, ?_, ?_⟩
  · refine (hW.sub fun r hr => ?_).trans (hf''.sub (wd_kvw (P := P) (dst := fV) (by simp only [fV]; nums)))
    rcases List.mem_append.mp hr with hr | hr
    · exact wd_kvw (P := P) (dst := fV) (by simp only [fV]; nums) r (List.mem_append_left _ hr)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
  · rw [show vOf P L t'.mem = Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (76 + fV)) P.F.H.D from rfl, hm, hv,
      mac_eq]
  · rw [hk]; exact hS.frame hf'' (wd_save hL (by simp only [fV]; nums))

/-- `V = HMAC_K(V)`, from the saved states for `K`, which it keeps. -/
theorem hmacVR_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t)
    (hS : SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (cfgOf P).hmacVR t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = kOf P L t.mem ∧ vOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem) ∧
      SavedK P L t'.mem (kOf P L t'.mem) := by
  refine WP.seq (WP.mono (restore_ok hL hc hS (blockKey_length (keyOf_length _))) fun u ⟨hu, hfu, hSu⟩ => ?_)
  refine WP.mono (vfin_ok hL hT hu (dst := fV) (by simp only [fV]; nums)) fun t' ⟨hc', hf', hm⟩ => ?_
  have hR : Region.Disjoint ⟨L.B + BitVec.ofNat 64 76, 128⟩ ⟨L.scr + BitVec.ofNat 64 0, 384⟩ :=
    hL.stk_scr (by omega_using []) (by decide)
  have hk : kOf P L t'.mem = kOf P L t.mem := by
    show Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 76) P.F.H.D = _
    rw [kv_frame hL hf' (o := 76) (by decide) (.inl (by simp only [fV]; nums)) (by nums) (by simp only [fV]; nums)]
    exact bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hR.sub_left (Offset.sub _ (by omega_using []) (by nums))) (by nums)
  have hv : vOf P L u.mem = vOf P L t.mem :=
    bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hR.sub_left (Offset.sub _ (by omega_using []) (by nums))) (by nums)
  refine ⟨hc', ?_, hk, ?_, ?_⟩
  · refine (hfu.sub fun r hr => ?_).trans (hf'.sub (wd_kvw (P := P) (dst := fV) (by simp only [fV]; nums)))
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
  · rw [show vOf P L t'.mem = Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (76 + fV)) P.F.H.D from rfl, hm, hv,
      mac_eq]
  · rw [hk]; exact hSu.frame hf' (wd_save hL (by simp only [fV]; nums))

/-- `K = HMAC_K(V ‖ m)`, for the message `m` of `len` bytes at
`scratch + 2256`, from HMAC's states for `K` by `init` or, if `fresh` is
false, from the saved ones. -/
theorem hmacKB_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {len : Nat} (hlen : len ≤ 256)
    (fresh : Bool) (hS : fresh = false → SavedK P L t.mem (kOf P L t.mem)) :
    WP isa ((cfgOf P).hmacK fresh len) t fun t' =>
      Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧ vOf P L t'.mem = vOf P L t.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem)
        (vOf P L t.mem ++ Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len) := by
  have post : ∀ {u : State}, St P L g m₀ (Spec.Hmac.blockKey P.ok.hH.SH.H (kOf P L t.mem)) [] u →
      ∀ {ws : List Region}, Frame ws t.mem u.mem → (∀ r ∈ ws, ∃ r' ∈ KVW L, Region.Sub r r') →
      (∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 140, P.F.H.D⟩ r) →
      (∀ r ∈ ws, Region.Disjoint ⟨L.scr + BitVec.ofNat 64 2256, len⟩ r) →
      WP isa (.seq (cfgOf P).updV (.seq ((cfgOf P).updM len) ((cfgOf P).fin len fK))) u fun t' =>
        Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧ vOf P L t'.mem = vOf P L t.mem ∧
        kOf P L t'.mem = P.mac (kOf P L t.mem)
          (vOf P L t.mem ++ Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len) := by
    intro u hu ws hf hk hdv hdm
    refine WP.mono (vmfin_ok hL hT hu hlen) fun t' ⟨hc', hf', hm⟩ => ⟨hc', ?_, ?_, ?_⟩
    · exact (hf.sub hk).trans (hf'.sub (wd_kvw (P := P) (dst := fK) (by simp only [fK]; nums)))
    · show Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 140) P.F.H.D = _
      rw [kv_frame hL hf' (o := 140) (by decide) (.inr (by simp only [fK]; nums)) (by nums) (by simp only [fK]; nums)]
      exact bytesAt_frame hf hdv (by nums)
    · rw [hm]
      have hv : vOf P L u.mem = vOf P L t.mem := bytesAt_frame hf hdv (by nums)
      have hmsg : Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) len =
          Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len := bytesAt_frame hf hdm (by omega_using [hlen])
      rw [hv, hmsg, mac_eq]
  cases fresh
  · refine WP.seq (WP.mono (restore_ok hL hc (hS rfl) (blockKey_length (keyOf_length _))) fun u ⟨hu, hfu, _⟩ => ?_)
    have hu' : St P L g m₀ (Spec.Hmac.blockKey P.ok.hH.SH.H (kOf P L t.mem)) [] u := hu
    refine post hu' hfu (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
    · exact hL.stk_scr (by nums) (by decide)
    · exact Offset.disjoint _ (by omega_using []) (by omega_using [hlen]) (by decide)
  · refine WP.seq (WP.mono (init_step hL hT hc) fun u ⟨hu, hfu⟩ => ?_)
    refine post hu hfu (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_) <;>
      simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr <;> rcases hr with rfl | rfl
    · exact ⟨L.SCR, by simp, Region.sub_prefix (by omega_using [])⟩
    · exact ⟨⟨L.B, 204⟩, by simp, Region.sub_prefix (by omega_using [])⟩
    · exact hL.stk_scr0 (by nums) (by decide)
    · exact Offset.disjoint_base _ (by omega_using []) (by nums)
    · exact Offset.disjoint_base _ (by decide) (by omega_using [hlen])
    · exact hL.low_scr (by omega_using [hlen]) |>.symm

/-- What the steps need of the layout: the scalars' bytes, and the table of `P`. -/
def HOk (P : RfcHash) {dn : Nat} (L : Lay dn) : Prop := L.q = P.Q ∧ TabL P L

/-- `K = HMAC_K(V ‖ m)`, then `V = HMAC_K(V)`, for the message `m = b (‖ d ‖ h)`. -/
theorem rekey_gen (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) {b : Nat} {full : Bool}
    (fresh : Bool) (hS : fresh = false → SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (.seq (.block Cfg.msgPtrs) (.seq (.block ((cfgOf P).msg b full))
      (.seq ((cfgOf P).hmacK fresh (mlen P full)) (cfgOf P).hmacVS))) t
      fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
        kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem else [])) ∧
        vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) ∧ SavedK P L t'.mem (kOf P L t'.mem) := by
  have hT := hq.2
  refine WP.seq (WP.mono (ptrs_ok hL hc) fun p ⟨hcp, hmp, hdip, hsip⟩ => ?_)
  rw [← hmp] at hS ⊢
  refine WP.seq (WP.mono (msg_ok (P := P) hL hq.1 hcp hdip hsip b full) fun u ⟨hcu, hfu, hbu⟩ => ?_)
  have hsafe : Region.Disjoint ⟨L.B + BitVec.ofNat 64 76, 128⟩ ⟨L.scr + BitVec.ofNat 64 2256, 1 + 2 * P.Q⟩ :=
    hL.stk_scr (by nums) (by nums)
  have hku : kOf P L u.mem = kOf P L p.mem := bytesAt_frame hfu (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hsafe.sub_left (Offset.sub _ (by omega_using []) (by nums))) (by nums)
  have hvu : vOf P L u.mem = vOf P L p.mem := bytesAt_frame hfu (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hsafe.sub_left (Offset.sub _ (by omega_using []) (by nums))) (by nums)
  have hSu : fresh = false → SavedK P L u.mem (kOf P L u.mem) := fun h => hku ▸ (hS h).frame hfu fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (by nums) (by nums) (by nums)
  refine WP.seq (WP.mono (hmacKB_ok (P := P) hL hT hcu (len := mlen P full)
    (by cases full <;> simp only [mlen, Bool.false_eq_true, ite_true, ite_false] <;> nums) fresh hSu)
    fun w ⟨hcw, hfw, hvw, hkw⟩ => ?_)
  refine WP.mono (hmacVS_ok hL hT hcw) fun t' ⟨hc', hf', hk', hv', hs'⟩ => ⟨hc', ?_, ?_, ?_, hs'⟩
  · exact ((hfu.sub (kvw_of fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inl (Offset.sub_base _ (by nums)))).trans hfw).trans hf'
  · rw [hk', hkw, hku, hvu, hbu, List.append_assoc]
  · rw [hv', hk', hvw, hvu]

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
theorem rekeyFull_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) (b : Nat)
    (hS : b ≠ 0 → SavedK P L t.mem (kOf P L t.mem)) :
    WP isa ((cfgOf P).rekeyFull b) t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [BitVec.ofNat 8 b] ++
        (Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem)) ∧
      vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) ∧ SavedK P L t'.mem (kOf P L t'.mem) := by
  unfold Cfg.rekeyFull
  refine WP.mono (rekey_gen (full := true) hL hq hc (decide (b = 0)) fun h => hS (by simpa using h))
    fun t' h => ?_
  simpa using h

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
theorem rekey_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).rekey t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [0]) ∧
      vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) ∧ SavedK P L t'.mem (kOf P L t'.mem) :=
  WP.mono (rekey_gen (b := 0) (full := false) hL hq hc true (fun h => absurd h (by decide)))
    fun _ h => ⟨h.1, h.2.1, by rw [h.2.2.1]; simp, h.2.2.2⟩

end VG.Proof.Ecdsa.Rfc6979.X86

end

end

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
  obtain h₁ := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at h₁
  obtain h₂ := Offset.lt_iff x base hn
  simp only [ofs]
  omega_arith)

theorem scr_of (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .edi = L.sc) : Scr t L.scr 8192 := by
  obtain hn : L.scr.toNat + 8192 ≤ 2 ^ 32 := by
    have := hL.nc; have := L.sc.isLt
    simp only [Lay.scr, BitVec.toNat_setWidth]; omega_arith
  obtain hF : 20 ≤ L.F.toNat := by have := hL.FN; have := hL.e588; omega_arith
  -- The calls' 20 bytes below `F` are in the stack the contract gives.
  obtain hd : Region.Disjoint ⟨L.F.setWidth 64 - BitVec.ofNat 64 20, 20⟩ ⟨L.scr, 8192⟩ := by
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
  obtain hw2 : (cfgOf P).w / 2 = P.w := by simp only [cfgOf, show P.R.E.C.len = 66 from hQ66, show P.w = 9 from hw9]; decide
  refine WP.of_syms ?_
  rw [Cfg.conv, hw2, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .esi) (by decide) o) fun u₁ h₁ => ?_
  obtain hS₁ : Scr u₁ L.scr 8192 := scr_keep (scr_of hL hc hdi) (h₁.keep _ (by decide))
    (h₁.keep _ (by decide)) (by rw [h₁.ctx.wr, hc.wr])
  have hsi₁ : u₁.gpr .esi = L.F + BitVec.ofNat 32 o := h₁.val
  obtain ha₁ : (L.F + BitVec.ofNat 32 o).setWidth 64 = L.B + BitVec.ofNat 64 (76 + o) := hL.addrF (by omega_arith)
  refine WP.mono (loadBytes_ok hS₁ (len := P.Q) (n := P.w) (o := 2560) (src := .esi) (by decide) (by omega_arith)
    (by rw [hsi₁, hL.frN (by omega_arith)]; omega_arith) (by omega_arith) (by omega_arith)
    (fun d hd => by rw [hsi₁, ha₁, Offset.add_add]; exact h₁.ctx.inFr (by omega_arith) (by omega_arith) hL)
    (by rw [hsi₁, ha₁]; exact hL.stk_scr (by omega_arith) (by omega_arith))) fun u₂ ⟨hv₂, k₂, O₂⟩ => ?_
  refine WP.mono (shrWords_ok (scr_keep hS₁ (k₂.1 _ (by decide)) (k₂.1 _ (by decide)) k₂.2.2) (n := P.w) (o := 2560) (sh := s)
    (by omega_arith) hs₁ hs₂) fun u₃ ⟨hv₃, k₃, O₃⟩ => ?_
  refine wp_movi fun u₄ v₄ => WP.block_nil ?_
  obtain hsp₄ : u₄.gpr .esp = L.F := by
    rw [v₄.other _ (by decide), k₃.1 _ (by decide), k₂.1 _ (by decide), h₁.keep _ (by decide), hc.esp]
  obtain hwr₄ : u₄.wr = t.wr := by rw [v₄.wr, k₃.2.2, k₂.2.2, h₁.ctx.wr, hc.wr]
  obtain hS₄ : Scr u₄ L.scr 8192 := scr_keep hS₁ (by rw [v₄.other _ (by decide), k₃.1 _ (by decide),
    k₂.1 _ (by decide)]) (by rw [v₄.other _ (by decide), k₃.1 _ (by decide), k₂.1 _ (by decide)])
    (by rw [v₄.wr, k₃.2.2, k₂.2.2])
  obtain hdst : (u₄.gpr .esp).setWidth 64 + BitVec.ofNat 64 o = L.B + BitVec.ofNat 64 (76 + o) := by
    rw [hsp₄, hL.F64, Offset.add_add]
  refine WP.mono (storeBytes_ok hS₄ (len := P.Q) (n := P.w) (d := o) (a := 2560) (dst := .esp) (by decide)
    (by decide) true (by rw [v₄.gpr]; rfl) (by omega_arith) (by omega_arith) (by omega_arith) (by rw [hsp₄, hFN]; omega_arith)
    (fun e m hem => by rw [hdst, Offset.add_add, hwr₄]; exact hc.inFrW (by omega_arith) (by omega_arith) hL)
    (by rw [hdst]; exact (hL.stk_scr (by omega_arith) (by omega_arith)).symm)) fun u₅ ⟨hb₅, k₅, O₅⟩ => ?_
  intro hsy
  rw [hdst] at hb₅ O₅
  -- What changed: the words at `scratch + 2560`, and the bytes converted.
  obtain hf : Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (76 + o), P.Q⟩] t.mem u₅.mem := by
    obtain f₂ := frame_of_outside (O₂.trans O₃) (by omega_arith)
    obtain f₅ := frame_of_outside O₅ (by omega_arith)
    rw [BitVec.add_zero, v₄.mem] at f₅
    rw [h₁.mem, show 8 * P.w = 72 by omega_arith] at f₂
    exact (f₂.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩).trans (f₅.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩)
  obtain hg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → u₅.gpr r = t.gpr r := fun r h₁' h₂ h₃ h₄ => by
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
  obtain hi := List.mem_range.mp hi
  obtain e : (p + BitVec.ofNat 64 i - p).toNat = i := by
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
  obtain ea : addr L.F o = L.B + BitVec.ofNat 64 (76 + o) := hL.addrF (by omega_arith)
  refine wp_stm (B := L.F) hc.esp (by rw [ea]; exact hc.inFrW (by omega_arith) (by omega_arith) hL)
    fun u₂ v₂ => WP.block_nil ?_
  obtain hm : u₂.mem = u.mem.writeW (L.B + BitVec.ofNat 64 (76 + o)) (0 : BitVec 32) := by
    rw [v₂.mem, hax, ea]
  obtain hf : Frame [⟨L.B + BitVec.ofNat 64 (76 + o), 4⟩] u.mem u₂.mem := by
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
  obtain c₃ : Ctx L g m₀ u₃ := hc.regs hL (by rw [v₃.rd, v₂.rd, v₁.rd]) (by rw [v₃.wr, v₂.wr, v₁.wr])
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
  obtain hcx₂ : u₂.gpr .ecx = BitVec.ofNat 32 P.F.H.D := by rw [h₂.val, hc₁.dl hT]
  refine WP.mono (min_ok hL h₂.ctx (a := P.F.H.D) (b := P.Q) (by omega_using [hD64]) (by omega_using [hQ66]) hcx₂)
    fun u₃ ⟨hc₃, hm₃, hcx₃, _⟩ => ?_
  refine WP.mono (xTail_ok hL hc₃ (fX + P.Q)) fun u₄ ⟨hc₄, hm₄, hbx₄, hsi₄, hg₄⟩ => ?_
  obtain hm : min P.F.H.D P.Q ≤ P.Q := Nat.min_le_right _ _
  rw [hcx₃, sub_min32 _ hm] at hbx₄
  obtain hmm : u₄.mem = u₁.mem := by rw [hm₄, hm₃, h₂.mem]
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
  obtain hm : min P.F.H.D P.Q ≤ P.Q := Nat.min_le_right _ _
  obtain hm8 : 8 ≤ min P.F.H.D P.Q := by omega_using [hD16, hQ8]
  obtain hdn' : min P.F.H.D P.Q ≤ dn := by omega_using [hdn]
  obtain ea : (L.F + BitVec.ofNat 32 (fX + (P.Q - min P.F.H.D P.Q))).setWidth 64 =
      L.B + BitVec.ofNat 64 (76 + fX + (P.Q - min P.F.H.D P.Q)) := by
    rw [hL.frv (by simp only [fX]; omega_using [hQ66]), Nat.add_assoc]
  obtain sepD : Region.Disjoint ⟨L.a2.setWidth 64, min P.F.H.D P.Q⟩
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
  obtain hdg : Spec.Sha256.bytesAt u₅.mem L.dg (min P.F.H.D P.Q) = Spec.Sha256.bytesAt t.mem L.dg (min P.F.H.D P.Q) :=
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
  obtain hcx₂ : u₂.gpr .ecx = BitVec.ofNat 32 P.F.H.D := by rw [h₂.val, hc₁.dl hT]
  refine WP.mono (xTail_ok hL h₂.ctx (fXc + P.Q - 1)) fun u₃ ⟨hc₃, hm₃, hbx₃, hsi₃, hg₃⟩ => ?_
  rw [hcx₂, show fXc + P.Q - 1 = fXc + (P.Q - 1) by simp only [fXc]; omega_using [hQ66], sub_min32 _ (by omega_using [hQD]),
    show fXc + (P.Q - 1 - P.F.H.D) = fXc + (P.Q - 1 - P.F.H.D) from rfl] at hbx₃
  obtain hmm : u₃.mem = u₁.mem := by rw [hm₃, h₂.mem]
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
  obtain hnb5 := (P.R.sizesW hW).2.2
  obtain hsh8 : P.R.sh < 8 := by simp only [RfcHash.Q] at hQ66; omega_using [hsl]
  obtain hsh1 : 1 ≤ P.R.sh := by simp only [RfcHash.Q] at hQ66; omega_using [hsl, hnb5]
  have hsc : (cfgOf P).sh = P.R.sh := rfl
  rw [Cfg.prepC]
  refine WP.seq (WP.mono (xcArgs_ok hL hT hW hc) fun u₁ ⟨hc₁, hf₁, hb₁, hcx₁, hbx₁, hsi₁⟩ => ?_)
  obtain ea : (L.F + BitVec.ofNat 32 (fXc + (P.Q - 1 - P.F.H.D))).setWidth 64 =
      L.B + BitVec.ofNat 64 (76 + fXc + (P.Q - 1 - P.F.H.D)) := by
    rw [hL.frv (by simp only [fXc]; omega_using [hQ66]), Nat.add_assoc]
  obtain sepD : Region.Disjoint ⟨L.a2.setWidth 64, P.F.H.D⟩
      ⟨L.B + BitVec.ofNat 64 (76 + fXc + (P.Q - 1 - P.F.H.D)), P.F.H.D⟩ :=
    ((hL.kg.sub_left (Offset.sub_base _ (by simp only [fXc]; omega_using [hQ66, hQD]))).symm.sub_left (Region.sub_prefix hdn))
  obtain hdg : Spec.Sha256.bytesAt u₁.mem L.dg P.F.H.D = Spec.Sha256.bytesAt t.mem L.dg P.F.H.D :=
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
    obtain hz : ∀ a n, a + n ≤ 72 → Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (76 + fXc + a)) n =
        List.replicate n 0 := fun a n han => by
      obtain h1 := bytesAt_take u₁.mem (L.B + BitVec.ofNat 64 (76 + fXc)) (n := a + n) (k := 72) (by omega_using [han])
      rw [hb₁, List.take_replicate, Nat.min_eq_left (by omega_using [han]), Proof.Hmac.Common.bytesAt_add, Offset.add_add,
        ← List.replicate_append_replicate] at h1
      exact (List.append_inj h1 (by simp [Spec.Sha256.bytesAt])).2
    obtain hY : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (76 + fXc)) P.Q =
        List.replicate (P.Q - 1 - P.F.H.D) 0 ++ (Spec.Sha256.bytesAt t.mem L.dg P.F.H.D ++ List.replicate 1 0) := by
      obtain e := Proof.Hmac.Common.bytesAt_add u₄.mem (L.B + BitVec.ofNat 64 (76 + fXc)) (P.Q - 1 - P.F.H.D)
        (P.F.H.D + 1)
      obtain e' := Proof.Hmac.Common.bytesAt_add u₄.mem
        (L.B + BitVec.ofNat 64 (76 + fXc) + BitVec.ofNat 64 (P.Q - 1 - P.F.H.D)) P.F.H.D 1
      rw [show P.Q - 1 - P.F.H.D + (P.F.H.D + 1) = P.Q by omega_using [hQD]] at e
      rw [Offset.add_add, Offset.add_add] at e'
      rw [Offset.add_add] at e
      obtain p₁ : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (76 + fXc)) (P.Q - 1 - P.F.H.D) =
          List.replicate (P.Q - 1 - P.F.H.D) 0 := by
        rw [bytesAt_frame hf₄ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (.inl (by omega_using [])) (by simp only [fXc]; omega_using [hQ66]) (by simp only [fXc]; omega_using [hQ66, hQD]))
          (by omega_using [hQ66])]
        have := hz 0 (P.Q - 1 - P.F.H.D) (by omega_using [hQ66])
        rwa [Nat.add_zero] at this
      obtain p₃ : Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (76 + fXc + (P.Q - 1 - P.F.H.D) + P.F.H.D)) 1 =
          List.replicate 1 0 := by
        rw [bytesAt_frame hf₄ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (.inr (by omega_using [])) (by simp only [fXc]; omega_using [hQ66, hQD]) (by simp only [fXc]; omega_using [hQ66, hQD]))
          (by omega_using []), show 76 + fXc + (P.Q - 1 - P.F.H.D) + P.F.H.D = 76 + fXc + (P.Q - 1 - P.F.H.D + P.F.H.D) by omega_using []]
        exact hz (P.Q - 1 - P.F.H.D + P.F.H.D) 1 (by omega_using [hQ66, hQD])
      rw [e, e', hb₄, hdg, p₁, p₃]
    rw [hb₆, hm₅, hY, ofBytes_zeros, ofBytes_append_zeros, show 8 * 1 = 8 from rfl, shift_back _ _ hsh8]

end VG.Proof.Ecdsa.Rfc6979.X86
