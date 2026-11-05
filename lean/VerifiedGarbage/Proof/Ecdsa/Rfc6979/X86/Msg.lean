module
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Hash
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

/-- A range of `scratch`, as the code addresses it from `scratch` in a register. -/
theorem scr_addr (hL : L.Ok) {d j : Nat} (h : d + 4 * j < 8192) :
    addr L.sc (d + 4 * j) = L.scr + BitVec.ofNat 64 d + BitVec.ofNat 64 (4 * j) := by
  rw [addr_eq (by have := hL.nc; omega_arith), Offset.add_add]

/-- A range of the frame, as the code addresses it from `esp`. -/
theorem fr_addr (hL : L.Ok) {o j : Nat} (h : o + 4 * j < 540) :
    addr L.F (o + 4 * j) = L.B + BitVec.ofNat 64 (76 + o) + BitVec.ofNat 64 (4 * j) := by
  rw [hL.addrF h, Offset.add_add, Nat.add_assoc]

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
