module
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Layout
public import VerifiedGarbage.Proof.Framework.X86.Wp

import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Copy
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Regs
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import Aesop.BuiltinRules
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.X86.Lit
import VerifiedGarbage.Proof.Weierstrass.PointContract

/-!
# Deterministic ECDSA on x86 (32-bit): the messages of steps d, f and h.3

`V ‖ b`, and `‖ d ‖ h` if `full`, at `scratch + 2256`, for `V` of `D` bytes
(`msg_ok`), as on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Msg.lean`): `V`
copied from the frame (`head_ok`), the byte `b`, then the private key and
`h` copied (`tail_ok`).
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

/-- A range of `scratch`, as the code addresses it from `scratch` in a register. -/
theorem scr_addr (hL : L.Ok) {d j : Nat} (h : d + 4 * j < 8192) :
    addr L.a4 (d + 4 * j) = L.scr + BitVec.ofNat 64 d + BitVec.ofNat 64 (4 * j) := by
  rw [addr_eq (by have := hL.nc; omega_arith), Offset.add_add]

/-- A range of the frame, as the code addresses it from `esp`. -/
theorem fr_addr (hL : L.Ok) {o j : Nat} (h : o + 4 * j < 224 + 4 * L.e) :
    addr L.F (o + 4 * j) = L.B + BitVec.ofNat 64 (76 + o) + BitVec.ofNat 64 (4 * j) := by
  rw [hL.addrF h, Offset.add_add, Nat.add_assoc]

/-- `4 K` bytes copied to `scratch + d` by `copyN`, with `Ctx` kept. -/
theorem copy_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : BitVec 32} {SA : Addr}
    (hs : u.gpr src = S) (hsr : src ≠ .eax) (hdi : u.gpr .edi = L.a4) {so d K : Nat} (hd : d + 4 * K ≤ 8192)
    (hSA : ∀ j < K, addr S (so + 4 * j) = SA + BitVec.ofNat 64 (4 * j))
    (hr : ∀ j < K, InRegions (u.rd ++ u.wr) (SA + BitVec.ofNat 64 (4 * j)) 4)
    (hsep : Region.Disjoint ⟨SA, 4 * K⟩ ⟨L.scr + BitVec.ofNat 64 d, 4 * K⟩) :
    WP isa (.block (Cfg.copyN K src so .edi d)) u fun u' => Ctx L g m₀ u' ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.scr + BitVec.ofNat 64 d, 4 * K⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 d) (4 * K) = Spec.Sha256.bytesAt u.mem SA (4 * K) :=
  WP.mono_syms (copyN_ok (K := K) (by decide) hsr hSA (fun j hj => scr_addr hL (by omega_arith)) hsep (by omega_arith) K
    (Nat.le_refl _) u hs hdi hr fun j hj => by
      rw [Offset.add_add]; exact hc.inScrW (by omega_arith)) fun u' ⟨hrd, hwr, hg, hf, hb⟩ hsy =>
    ⟨hc.keep (hsy := hsy) hL hrd hwr (hg _ (by decide)) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L hd),
      hrd, hwr, hg, hf, hb⟩

/-- The pointers: `scratch` in `edi` and `d` in `esi`. -/
theorem ptrs_ok (hL : L.Ok) {c : Cfg} (hw : c.wide = L.wide) (hh : c.hHigh = L.hHigh) {t : State}
    (hc : Ctx L g m₀ t) :
    WP isa (.block c.msgPtrs) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .edi = L.a4 ∧ u.gpr .esi = L.a1 := by
  rw [Cfg.msgPtrs, show ([.mov .edi (c.arg 4), .mov .esi (c.arg 1)] : List Instr) =
    [.mov .edi (c.arg 4)] ++ [.mov .esi (c.arg 1)] from rfl, WP.block_append_iff]
  refine WP.mono (argC_ok hL hw hh hc (d := .edi) (by decide) (i := 4) (by omega_arith)) fun u₁ h₁ => ?_
  refine WP.mono (argC_ok hL hw hh h₁.ctx (d := .esi) (by decide) (i := 1) (by omega_arith)) fun u₂ h₂ => ?_
  exact ⟨h₂.ctx, by rw [h₂.mem, h₁.mem], by rw [h₂.keep _ (by decide), h₁.val]; rfl, h₂.val⟩

/-- `copyBytes` of a multiple of 4 bytes is `copyN`. -/
theorem copyBytes_four {len : Nat} (h : len % 4 = 0) (src : Reg) (so : Nat) (dst : Reg) (d : Nat) :
    Cfg.copyBytes len src so dst d = Cfg.copyN (len / 4) src so dst d := by
  simp [Cfg.copyBytes, h]

/-- `V ‖ b`, for `V` of `D` bytes, with `scratch` in `edi`. -/
theorem head_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .edi = L.a4) (b : Nat) {D : Nat}
    (hD : D ≤ 64) (hD4 : D % 4 = 0) :
    WP isa (.block (Cfg.copyBytes D .esp fV .edi sMsg ++
      ([.mov .eax (.imm (BitVec.ofNat 32 b)), .store8 (at_ .edi (sMsg + D)) .al] : List Instr))) t fun u =>
      Ctx L g m₀ u ∧ (∀ r, r ≠ .eax → u.gpr r = t.gpr r) ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2256, D + 1⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) (D + 1) =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 140) D ++ [BitVec.ofNat 8 b] := by
  have e4 : 4 * (D / 4) = D := by omega_arith
  have nc := hL.nc
  rw [copyBytes_four hD4]
  simp only [fV, sMsg]
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok hL hc (S := L.F) (SA := L.B + BitVec.ofNat 64 140) (src := .esp) hc.esp (by decide) hdi
    (so := 64) (d := 2256) (K := D / 4) (by omega_arith) (fun j hj => fr_addr hL (by omega_arith))
    (fun j hj => by rw [Offset.add_add]; exact hc.inFr (by omega_arith) (by omega_arith) hL)
    (hL.stk_scr (by omega_arith) (by omega_arith))) fun u₂ ⟨hc₂, hrd₂, hwr₂, hg₂, hf₂, hb₂⟩ => ?_
  rw [e4] at hf₂ hb₂
  have hdi₂ : u₂.gpr .edi = L.a4 := (hg₂ _ (by decide)).trans hdi
  have ea : addr L.a4 (2256 + D) = L.scr + BitVec.ofNat 64 (2256 + D) := addr_eq (by omega_arith)
  refine wp_movi fun u₃ v₃ => wp_store8 (a := L.scr + BitVec.ofNat 64 (2256 + D))
    (by show addr (u₃.gpr .edi) (2256 + D) = _; rw [v₃.other .edi (by decide), hdi₂, ea])
    (by rw [v₃.wr]; exact hc₂.inScrW (o := 2256 + D) (n := 1) (by omega_arith)) fun u₄ v₄ => WP.block_nil ?_
  have hb8 : (u₃.gpr Reg8.al.reg).setWidth 8 = BitVec.ofNat 8 b := by
    rw [show Reg8.al.reg = .eax from rfl, v₃.gpr]
    apply BitVec.eq_of_toNat_eq; simp
  rw [hb8] at v₄
  have hm₄ : u₄.mem = u₂.mem.writeW (L.scr + BitVec.ofNat 64 (2256 + D)) (BitVec.ofNat 8 b) := by
    rw [v₄.mem, v₃.mem]
  have hf₃ : Frame [⟨L.scr + BitVec.ofNat 64 (2256 + D), 1⟩] u₂.mem u₄.mem := by
    rw [hm₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc₂.keep (hsy := by rw [v₄.syms, v₃.syms]) hL (by rw [v₄.rd, v₃.rd]) (by rw [v₄.wr, v₃.wr])
      (by rw [v₄.gpr, v₃.other _ (by decide)]) hf₃
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by omega_arith)),
    fun r hr => by rw [v₄.gpr, v₃.other _ hr, hg₂ r hr], ?_, ?_⟩
  · refine (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_arith) (by omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_arith) (by omega_arith)
  · rw [Proof.Hmac.Common.bytesAt_add, Offset.add_add]
    have e₁ : Spec.Sha256.bytesAt u₄.mem (L.scr + BitVec.ofNat 64 2256) D =
        Spec.Sha256.bytesAt u₂.mem (L.scr + BitVec.ofNat 64 2256) D :=
      bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)
    rw [e₁, hb₂]
    refine congrArg (fun y => Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 140) D ++ y) ?_
    show [u₄.mem (L.scr + BitVec.ofNat 64 (2256 + D) + BitVec.ofNat 64 0)] = _
    rw [BitVec.add_zero, hm₄, WriteBytes.writeW8_apply]; simp

/-- `Q` bytes copied to `scratch + d` by `copyBytes`, with `Ctx` kept. -/
theorem copyB_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : BitVec 32} {SA : Addr}
    (hs : u.gpr src = S) (hsr : src ≠ .eax) (hdi : u.gpr .edi = L.a4) {so d Q : Nat} (h4 : 4 ≤ Q)
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

/-- `‖ d ‖ h`, `Q` bytes each, after `D + 1` bytes, with `scratch` in `edi`
and `d` in `esi`, `h` at `ho` in the frame. -/
theorem tail_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hdi : u.gpr .edi = L.a4) (hsi : u.gpr .esi = L.a1)
    {D Q ho : Nat} (hD : D ≤ 64) (h4 : 4 ≤ Q) (hQ : Q ≤ 66) (hq : Q ≤ L.q) (hho : 76 + ho + Q ≤ 272 + 4 * L.e) :
    WP isa (.block (Cfg.copyBytes Q .esi 0 .edi (2256 + D + 1) ++ Cfg.copyBytes Q .esp ho .edi (2256 + D + 1 + Q))) u
      fun u' => Ctx L g m₀ u' ∧ Frame [⟨L.scr + BitVec.ofNat 64 (2256 + D + 1), 2 * Q⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 (2256 + D + 1)) (2 * Q) =
          Spec.Sha256.bytesAt u.mem L.d Q ++ Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (76 + ho)) Q := by
  have nc := hL.nc
  have nd := hL.nd
  have he := L.he
  have nB := hL.nB
  rw [WP.block_append_iff]
  refine WP.mono (copyB_ok hL hc (src := .esi) (SA := L.d) hsi (by decide) hdi (so := 0) (d := 2256 + D + 1) h4
    (by omega_arith) (fun j hj => by rw [Nat.zero_add]; exact addr_eq (by omega_arith))
    (fun j hj => hc.inD (by omega_arith) (by omega_arith))
    ((hL.dc.sub_left (Region.sub_prefix hq)).sub_right (Offset.sub_base _ (by omega_arith))))
    fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  have hdi₂ : u₂.gpr .edi = L.a4 := (hg₂ _ (by decide)).trans hdi
  refine WP.mono (copyB_ok hL hc₂ (S := L.F) (SA := L.B + BitVec.ofNat 64 (76 + ho)) (src := .esp) hc₂.esp (by decide)
    hdi₂ (so := ho) (d := 2256 + D + 1 + Q) h4 (by omega_arith)
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

/-- `h` in the message: from the stack at `hb` (`Q` bytes). -/
abbrev hPart (Q hb : Nat) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 hb) Q

/-- The message `V ‖ b` (`‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + 2256`, for `V` of `D` bytes, `h` at `ho` in the frame. -/
theorem msg_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .edi = L.a4) (hsi : t.gpr .esi = L.a1)
    (b : Nat) (full : Bool) (ho : Nat) {D Q : Nat}
    (hD : D ≤ 64) (hD4 : D % 4 = 0) (h4 : 4 ≤ Q) (hQ : Q ≤ 66) (hq : Q ≤ L.q)
    (hA : full = true → 76 + ho + Q ≤ 272 + 4 * L.e) :
    WP isa (.block (Cfg.msg Q D b full ho)) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2256, D + 2 * Q + 1⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.scr + BitVec.ofNat 64 2256) (if full then D + 2 * Q + 1 else D + 1) =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 140) D ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem L.d Q ++ hPart Q (76 + ho) L t.mem else []) := by
  have nc := hL.nc
  have := L.he
  cases full
  · simp only [Cfg.msg, Bool.false_eq_true, ite_false, List.append_nil]
    refine WP.mono (head_ok hL hc hdi b hD hD4) fun u ⟨hcu, _, hf, hb⟩ =>
      ⟨hcu, hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩, hb⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub _ (by omega_arith) (by omega_arith)
  · simp only [Cfg.msg, ite_true, sMsg]
    rw [WP.block_append_iff]
    refine WP.mono (head_ok hL hc hdi b hD hD4) fun u ⟨hcu, hg, hf, hb⟩ => ?_
    have hdi' : u.gpr .edi = L.a4 := (hg _ (by decide)).trans hdi
    have hsi' : u.gpr .esi = L.a1 := (hg _ (by decide)).trans hsi
    have hho := hA rfl
    refine WP.mono (tail_ok hL hcu hdi' hsi' hD h4 hQ hq hho) fun u' ⟨hcu', hf', hb'⟩ => ⟨hcu', ?_, ?_⟩
    · refine (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (hf'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.sub _ (by omega_arith) (by omega_arith)
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.sub _ (by omega_arith) (by omega_arith)
    · rw [show D + 2 * Q + 1 = (D + 1) + 2 * Q by omega_arith, Proof.Hmac.Common.bytesAt_add _ _ (D + 1) (2 * Q),
        Offset.add_add, show 2256 + (D + 1) = 2256 + D + 1 by omega_arith, hb',
        bytesAt_frame hf' (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith), hb]
      refine congrArg (fun y => Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 140) D ++ [BitVec.ofNat 8 b] ++ y) ?_
      have hdq : Spec.Sha256.bytesAt u.mem L.d Q = Spec.Sha256.bytesAt t.mem L.d Q :=
        bytesAt_frame hf (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hL.dc.sub_left (Region.sub_prefix hq)).sub_right (Offset.sub_base _ (by omega_arith))) (by omega_arith)
      rw [hdq]
      refine congrArg (Spec.Sha256.bytesAt t.mem L.d Q ++ ·) ?_
      exact bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hL.stk_scr (by omega_arith) (by omega_arith)) (by omega_arith)

end VG.Proof.Ecdsa.Rfc6979.X86
