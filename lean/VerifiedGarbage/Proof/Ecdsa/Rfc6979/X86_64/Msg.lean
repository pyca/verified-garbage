module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Blocks
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Mont.X86_64.Row
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Copy

/-!
# Deterministic ECDSA on x86-64: the messages of steps d, f and h.3

`V ‖ b`, and `‖ d ‖ h` if `full`, at `scratch + 2560`, for `V` of `D` bytes
(`msg_ok`): `V`'s 64 bytes copied from the frame and the byte `b` after its
first `D` (`head_ok`), then the private key and `h` copied (`tail_ok`), at
addresses from `scratch + D`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

/-- `8 K` bytes copied to `scratch + d` by `copyN`, with `Ctx` kept. -/
theorem copy_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : Addr} (hs : u.gpr src = S)
    (hsr : src ≠ .rax) (hdi : u.gpr .rdi = L.scr) {so d K : Nat} (hd : d + 8 * K ≤ 8192)
    (hr : ∀ j < K, InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (so + 8 * j)) 8)
    (hsep : Region.Disjoint ⟨S + BitVec.ofNat 64 so, 8 * K⟩ ⟨L.scr + BitVec.ofNat 64 d, 8 * K⟩) :
    WP isa (.block (Cfg.copyN K src so .rdi d)) u fun u' => Ctx L g m₀ u' ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.scr + BitVec.ofNat 64 d, 8 * K⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 d) (8 * K) =
        Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 so) (8 * K) :=
  WP.mono_syms (copyN_ok (K := K) (by decide) hsr hsep (by have := hL.nc; omega_using [hd]) K (Nat.le_refl _) u hs hdi hr
    fun j hj => hc.inScrW (by omega_using [hd, hj])) fun u' ⟨hrd, hwr, hg, hf, hb⟩ hsy =>
    ⟨hc.keep hL hrd hwr (hg _ (by decide)) (fun r hr _ => hg r (ne_cs hr (by decide))) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L hd) hsy,
      hrd, hwr, hg, hf, hb⟩

theorem fr_add (B : Addr) (o : Nat) : B + BitVec.ofNat 64 24 + BitVec.ofNat 64 o = B + BitVec.ofNat 64 (24 + o) :=
  Offset.add_add _ _ _

/-- The pointers: `scratch` in `rdi`, `d` in `rsi`, `D` in `rdx`. -/
theorem ptrs_ok (hL : L.Ok) {P : RfcHash} (hq : HashLay P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.msgPtrs) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .rdi = L.scr ∧
      u.gpr .rsi = L.d ∧ u.gpr .rdx = BitVec.ofNat 64 P.H.D := by
  rw [show Cfg.msgPtrs = [.mov .rdi (.mem (stk fScratch))] ++ [.mov .rsi (.mem (stk fD))] ++
    [.mov .rdx (.mem (stk fHL))] from rfl, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ld_ok hL hc (d := .rdi) (by decide) (o := fScratch) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (ld_ok hL h₁.ctx (d := .rsi) (by decide) (o := fD) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (ldHL_ok hL hq h₂.ctx (d := .rdx) (by decide)) fun u₃ h₃ => ?_
  refine ⟨h₃.ctx, by rw [h₃.mem, h₂.mem, h₁.mem], ?_, ?_, h₃.val⟩
  · rw [h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]; exact hc.pScr
  · rw [h₃.keep _ (by decide), h₂.val, h₁.mem]; exact hc.pD

/-- `Q` bytes copied to `scratch + a + d` by `copyBytes`, through a register
`dst` holding `scratch + a`, with `Ctx` kept. -/
theorem copyB_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src dst : Reg} {S : Addr} (hs : u.gpr src = S)
    (hsr : src ≠ .rax) (hdr : dst ≠ .rax) {a : Nat} (hdi : u.gpr dst = L.scr + BitVec.ofNat 64 a) {so d Q : Nat}
    (h8 : 8 ≤ Q) (hd : a + d + Q ≤ 8192) (hso : so + Q < 2 ^ 64)
    (hr : ∀ j, j + 8 ≤ Q → InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (so + j)) 8)
    (hsep : Region.Disjoint ⟨S + BitVec.ofNat 64 so, Q⟩ ⟨L.scr + BitVec.ofNat 64 (a + d), Q⟩) :
    WP isa (.block (Cfg.copyBytes Q src so dst d)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.scr + BitVec.ofNat 64 (a + d), Q⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 (a + d)) Q =
        Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 so) Q := by
  have e : ∀ x, L.scr + BitVec.ofNat 64 a + BitVec.ofNat 64 x = L.scr + BitVec.ofNat 64 (a + x) :=
    fun x => Offset.add_add _ _ _
  refine WP.mono_syms (copyBytes_ok (D := L.scr + BitVec.ofNat 64 a) (d := d) hdr hsr (by rw [e]; exact hsep) h8 hso
    (by omega_using [hd]) hs hdi hr fun j hj => by
      rw [e, show a + (d + j) = (a + d) + j by omega_using []]; exact hc.inScrW (by omega_using [hd, hj]))
    fun u' ⟨hrd, hwr, hg, hf, hb⟩ hsy => ?_
  rw [e] at hf hb
  exact ⟨hc.keep hL hrd hwr (hg _ (by decide)) (fun r hr _ => hg r (ne_cs hr (by decide))) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L hd) hsy, hg, hf, hb⟩

/-- `V`'s 64 bytes, then `b` after the first `D` of them, with `scratch` in
`rdi` and `D` in `rdx`, which then holds `scratch + D`. -/
theorem head_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .rdi = L.scr) (b : Nat) {D : Nat}
    (hD : D ≤ 64) (hdx : t.gpr .rdx = BitVec.ofNat 64 D) :
    WP isa (.block (Cfg.copyN 8 .rsp fV .rdi sMsg ++
      ([.alu .add .rdx (.reg .rdi), .mov32 .rax (.imm (BitVec.ofNat 32 b)), .store8 (at_ .rdx sMsg) .rax] :
        List Instr))) t fun u =>
      Ctx L g m₀ u ∧ (∀ r, r ≠ .rax → r ≠ .rdx → u.gpr r = t.gpr r) ∧ u.gpr .rdx = L.scr + BitVec.ofNat 64 D ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 65⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2560) (D + 1) =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 88) D ++ [BitVec.ofNat 8 b] := by
  simp only [fV, sMsg]
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok hL hc (S := L.B + BitVec.ofNat 64 24) (src := .rsp) hc.rsp (by decide) hdi
    (so := 64) (d := 2560) (K := 8) (by omega_using [])
    (fun j hj => by rw [fr_add]; exact hc.inFr (by omega_using []) (by have := L.he; omega_using [hj, this]))
    (by rw [fr_add]; exact hL.stk_scr (by have := L.he; omega_using [this]) (by omega_using [])))
    fun u₂ ⟨hc₂, _, _, hg₂, hf₂, hb₂⟩ => ?_
  have hdi₂ : u₂.gpr .rdi = L.scr := (hg₂ _ (by decide)).trans hdi
  have hdx₂ : u₂.gpr .rdx = BitVec.ofNat 64 D := (hg₂ _ (by decide)).trans hdx
  have hX : BitVec.ofNat 64 D + L.scr + BitVec.ofNat 64 2560 = L.scr + BitVec.ofNat 64 (2560 + D) := by
    rw [BitVec.add_comm (BitVec.ofNat 64 D), Offset.add_add, Nat.add_comm]
  have w := hc₂.inScrW (o := 2560 + D) (n := 1) (by omega_using [hD])
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, State.setReg32,
    State.store8, ea_at, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_false, ite_true,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, hdi₂, hdx₂, hX, RegUpd.wr_setReg, RegUpd.wr_arithFlags, w,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  have hb8 : ((BitVec.ofNat 32 b).setWidth 64).setWidth 8 = BitVec.ofNat 8 b := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [hb8]
  have hf₃ : Frame [⟨L.scr + BitVec.ofNat 64 (2560 + D), 1⟩] u₂.mem
      (u₂.mem.writeW (L.scr + BitVec.ofNat 64 (2560 + D)) (BitVec.ofNat 8 b)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc₂.keep hL rfl rfl (by triv) (fun r hr hr' => ?_) hf₃
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by omega_using [hD])) rfl,
    fun r hr hr' => ?_, ?_, ?_, ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ne_cs hr (by decide : Reg.rax ∉ calleeSaved),
      ne_cs hr (by decide : Reg.rdx ∉ calleeSaved), ite_false]
  · simp only [hr, hr', ite_false]; exact hg₂ r hr
  · rw [BitVec.add_comm]
  · refine (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_using []) (by omega_using [])
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_using []) (by omega_using [hD])
  · rw [Proof.Hmac.Common.bytesAt_add, Offset.add_add]
    have e₁ : Spec.Sha256.bytesAt (u₂.mem.writeW (L.scr + BitVec.ofNat 64 (2560 + D)) (BitVec.ofNat 8 b))
        (L.scr + BitVec.ofNat 64 2560) D = Spec.Sha256.bytesAt u₂.mem (L.scr + BitVec.ofNat 64 2560) D :=
      bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_using []) (by omega_using [hD]) (by omega_using [hD])) (by omega_using [hD])
    rw [e₁, bytesAt_take _ _ (k := 8 * 8) (by omega_using [hD]), hb₂, fr_add, ← bytesAt_take _ _ (by omega_using [hD])]
    refine congrArg (fun y => Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (24 + 64)) D ++ y) ?_
    show [(u₂.mem.writeW (L.scr + BitVec.ofNat 64 (2560 + D)) (BitVec.ofNat 8 b))
      (L.scr + BitVec.ofNat 64 (2560 + D) + BitVec.ofNat 64 0)] = _
    rw [add_ofNat_zero, WriteBytes.writeW8_apply]; simp

/-- `‖ d ‖ h`, `Q` bytes each, after `D + 1` bytes, with `scratch + D` in
`rdx` and `d` in `rsi`, `h` at `fH` in the frame. -/
theorem tail_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {D : Nat} (hdx : u.gpr .rdx = L.scr + BitVec.ofNat 64 D)
    (hsi : u.gpr .rsi = L.d) {Q : Nat} (hD : D ≤ 64) (h8 : 8 ≤ Q) (hQ : Q ≤ 66) (hq : Q ≤ L.q) :
    WP isa (.block (Cfg.copyBytes Q .rsi 0 .rdx (sMsg + 1) ++ Cfg.copyBytes Q .rsp fH .rdx (sMsg + 1 + Q))) u
      fun u' => Ctx L g m₀ u' ∧ Frame [⟨L.scr + BitVec.ofNat 64 (D + (2560 + 1)), 2 * Q⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 (D + (2560 + 1))) (2 * Q) =
          Spec.Sha256.bytesAt u.mem L.d Q ++ Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 312) Q := by
  simp only [sMsg, fH]
  rw [WP.block_append_iff]
  refine WP.mono (copyB_ok hL hc (src := .rsi) hsi (by decide) (by decide) hdx (so := 0) (d := 2560 + 1) h8
    (by omega_using [hD, hQ]) (by omega_using [hQ])
    (fun j hj => by rw [Nat.zero_add]; exact hc.inD (by omega_using [hq, hj]) (by omega_using [hQ, hj]))
    (by rw [add_ofNat_zero]
        exact (hL.dc.sub_left (Region.sub_prefix hq)).sub_right (Offset.sub_base _ (by omega_using [hD, hQ]))))
    fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  have hdx₂ : u₂.gpr .rdx = L.scr + BitVec.ofNat 64 D := (hg₂ _ (by decide)).trans hdx
  refine WP.mono (copyB_ok hL hc₂ (S := L.B + BitVec.ofNat 64 24) (src := .rsp) hc₂.rsp (by decide) (by decide)
    hdx₂ (so := 288) (d := 2560 + 1 + Q) h8 (by omega_using [hD, hQ]) (by omega_using [hQ])
    (fun j hj => by rw [fr_add]; exact hc₂.inFr (by omega_using []) (by have := L.he; omega_using [hQ, hj, this]))
    (by rw [fr_add]; exact hL.stk_scr (by have := L.he; omega_using [hQ, this]) (by omega_using [hD, hQ])))
    fun u₃ ⟨hc₃, _, hf₃, hb₃⟩ => ?_
  refine ⟨hc₃, ?_, ?_⟩
  · refine (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_using []) (by omega_using [])
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_using []) (by omega_using [])
  · rw [show 2 * Q = Q + Q by omega_using [], Proof.Hmac.Common.bytesAt_add _ _ Q Q, Offset.add_add,
      show D + (2560 + 1) + Q = D + (2560 + 1 + Q) by omega_using [], hb₃, fr_add,
      bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_using []) (by omega_using [hD, hQ]) (by omega_using [hD, hQ])) (by omega_using [hQ]),
      hb₂, add_ofNat_zero]
    refine congrArg (fun y => Spec.Sha256.bytesAt u.mem L.d Q ++ y) ?_
    exact bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by have := L.he; omega_using [hQ, this]) (by omega_using [hD, hQ])) (by omega_using [hQ])

/-- `h`, in the frame. -/
abbrev hPart (Q : Nat) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 312) Q

/-- The message `V ‖ b` (`‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + 2560`, for `V` of `D` bytes. -/
theorem msg_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .rdi = L.scr) (hsi : t.gpr .rsi = L.d)
    {D : Nat} (hdx : t.gpr .rdx = BitVec.ofNat 64 D) (b : Nat) (full : Bool) {Q : Nat} (hD : D ≤ 64)
    (h8 : 8 ≤ Q) (hQ : Q ≤ 66) (hq : Q ≤ L.q) :
    WP isa (.block (Cfg.msg Q b full)) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 200⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.scr + BitVec.ofNat 64 2560) (if full then D + 2 * Q + 1 else D + 1) =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 88) D ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem L.d Q ++ hPart Q L t.mem else []) := by
  cases full
  · simp only [Cfg.msg, Bool.false_eq_true, ite_false, List.append_nil]
    refine WP.mono (head_ok hL hc hdi b hD hdx) fun u ⟨hcu, _, _, hf, hb⟩ =>
      ⟨hcu, hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩, hb⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub _ (by omega_using []) (by omega_using [])
  · simp only [Cfg.msg, ite_true]
    rw [WP.block_append_iff]
    refine WP.mono (head_ok hL hc hdi b hD hdx) fun u ⟨hcu, hg, hdxu, hf, hb⟩ => ?_
    have hsi' : u.gpr .rsi = L.d := (hg _ (by decide) (by decide)).trans hsi
    refine WP.mono (tail_ok hL hcu hdxu hsi' hD h8 hQ hq) fun u' ⟨hcu', hf', hb'⟩ => ⟨hcu', ?_, ?_⟩
    · refine (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (hf'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.sub _ (by omega_using []) (by omega_using [])
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.sub _ (by omega_using []) (by omega_using [hD, hQ])
    · rw [show D + 2 * Q + 1 = (D + 1) + 2 * Q by omega_using [], Proof.Hmac.Common.bytesAt_add _ _ (D + 1) (2 * Q),
        Offset.add_add, show 2560 + (D + 1) = D + (2560 + 1) by omega_using [], hb',
        bytesAt_frame hf' (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega_using []) (by omega_using [hD]) (by omega_using [hD, hQ])) (by omega_using [hD]), hb]
      refine congrArg (fun y => Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 88) D ++ [BitVec.ofNat 8 b] ++ y) ?_
      have hdq : Spec.Sha256.bytesAt u.mem L.d Q = Spec.Sha256.bytesAt t.mem L.d Q :=
        bytesAt_frame hf (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hL.dc.sub_left (Region.sub_prefix hq)).sub_right (Offset.sub_base _ (by omega_using []))) (by omega_using [hQ])
      rw [hdq]
      refine congrArg (Spec.Sha256.bytesAt t.mem L.d Q ++ ·) ?_
      exact bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hL.stk_scr (by have := L.he; omega_using [hQ, this]) (by omega_using [])) (by omega_using [hQ])

end VG.Proof.Ecdsa.Rfc6979.X86_64
